#include <sys/select.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>

#include <ctype.h>
#include <curses.h>
#include <errno.h>
#include <fcntl.h>
#include <locale.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <term.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>
#include <wchar.h>

/* Allow to lazyload items when a file is specified? This saves memory but
   increases some latency when seeking items. It also causes issues if the
   feed is changed while having the UI open (and offsets are changed). */
/*#define LAZYLOAD 1*/

#define LEN(a) sizeof((a))/sizeof((a)[0])

#define PAD_TRUNCATE_SYMBOL    "\xe2\x80\xa6" /* symbol: "ellipsis" */
#define SCROLLBAR_SYMBOL_BAR   "\xe2\x94\x82" /* symbol: "light vertical" */
#define SCROLLBAR_SYMBOL_TICK  " "

/* See the README for some color theme examples. */
#define THEME_ITEM_NORMAL()           do {                            } while(0)
#define THEME_ITEM_FOCUS()            do {                            } while(0)
#define THEME_ITEM_BOLD()             do { attrmode(ATTR_BOLD_ON);    } while(0)
#define THEME_ITEM_SELECTED()         do { attrmode(ATTR_REVERSE_ON); } while(0)
#define THEME_SCROLLBAR_FOCUS()       do {                            } while(0)
#define THEME_SCROLLBAR_NORMAL()      do { attrmode(ATTR_FAINT_ON);   } while(0)
#define THEME_SCROLLBAR_TICK_FOCUS()  do { attrmode(ATTR_REVERSE_ON); } while(0)
#define THEME_SCROLLBAR_TICK_NORMAL() do { attrmode(ATTR_REVERSE_ON); } while(0)
#define THEME_STATUSBAR()             do { attrmode(ATTR_REVERSE_ON); } while(0)
#define THEME_INPUT_LABEL()           do { attrmode(ATTR_REVERSE_ON); } while(0)
#define THEME_INPUT_NORMAL()          do {                            } while(0)

static char *plumber = "xdg-open"; /* environment variable: $SFEED_PLUMBER */
static char *piper = "sfeed_content"; /* environment variable: $SFEED_PIPER */
static char *yanker = "xclip -r"; /* environment variable: $SFEED_YANKER */

enum {
	ATTR_RESET = 0,	ATTR_BOLD_ON = 1, ATTR_FAINT_ON = 2, ATTR_REVERSE_ON = 7
};

enum Pane { PaneFeeds, PaneItems, PaneLast };

enum {
	FieldUnixTimestamp = 0, FieldTitle, FieldLink, FieldContent,
	FieldContentType, FieldId, FieldAuthor, FieldEnclosure, FieldLast
};

struct win {
	int width; /* absolute width of the window */
	int height; /* absolute height of the window */
	int dirty; /* needs draw update: clears screen */
};

struct row {
	char *text; /* text string, optional if using row_format() callback */
	int bold;
	void *data; /* data binding */
};

struct pane {
	int x; /* absolute x position on the screen */
	int y; /* absolute y position on the screen */
	int width; /* absolute width of the pane */
	int height; /* absolute height of the pane */
	off_t pos; /* focused row position */
	struct row *rows;
	size_t nrows; /* total amount of rows */
	int focused; /* has focus or not */
	int hidden; /* is visible or not */
	int dirty; /* needs draw update */
	/* (optional) callback functions */
	struct row *(*row_get)(struct pane *, off_t pos);
	char *(*row_format)(struct pane *, struct row *);
	int (*row_match)(struct pane *, struct row *, const char *);
};

struct scrollbar {
	int tickpos;
	int ticksize;
	int x; /* absolute x position on the screen */
	int y; /* absolute y position on the screen */
	int size; /* absolute size of the bar */
	int focused; /* has focus or not */
	int hidden; /* is visible or not */
	int dirty; /* needs draw update */
};

struct statusbar {
	int x; /* absolute x position on the screen */
	int y; /* absolute y position on the screen */
	int width; /* absolute width of the bar */
	char *text; /* data */
	int hidden; /* is visible or not */
	int dirty; /* needs draw update */
};

/* /UI */

struct item {
	char *link; /* separate link field (always loaded in case of urlfile) */
	char *fields[FieldLast];
	char *line; /* allocated split line */
	time_t timestamp;
	int timeok;
	int isnew;
	off_t offset; /* line offset in file for lazyload */
};

struct items {
	struct item *items;     /* array of items */
	size_t len;             /* amount of items */
	size_t cap;             /* available capacity */
};

struct feed {
	char         *name;     /* feed name */
	char         *path;     /* path to feed or NULL for stdin */
	unsigned long totalnew; /* amount of new items per feed */
	unsigned long total;    /* total items */
	FILE *fp;               /* file pointer */
};

#undef err
void err(int, const char *, ...);

void alldirty(void);
void cleanup(void);
void draw(void);
int isurlnew(const char *);
void markread(struct pane *, off_t, off_t, int);
void pane_draw(struct pane *);
void readurls(void);
void sighandler(int);
void updategeom(void);
void updatesidebar(int);

static struct statusbar statusbar;
static struct pane panes[PaneLast];
static struct scrollbar scrollbars[PaneLast]; /* each pane has a scrollbar */
static struct win win;
static size_t selpane;
static int usemouse = 1; /* use xterm mouse tracking */
static int onlynew = 0; /* show only new in sidebar */

static struct termios tsave; /* terminal state at startup */
static struct termios tcur;
static int devnullfd;
static int needcleanup;

static struct feed *feeds;
static struct feed *curfeed;
static size_t nfeeds; /* amount of feeds */
static time_t comparetime;
static char *urlfile, **urls;
static size_t nurls;

volatile sig_atomic_t sigstate = 0;

int
ttywritef(const char *fmt, ...)
{
	va_list ap;
	int n;

	va_start(ap, fmt);
	n = vdprintf(1, fmt, ap);
	va_end(ap);

	return n;
}

int
ttywrite(const char *s)
{
	if (!s)
		return 0; /* for tparm() returning NULL */
	return write(1, s, strlen(s));
}

/* like BSD err(), but calls cleanup() and _exit(). */
void
err(int code, const char *fmt, ...)
{
	va_list ap;
	int saved_errno;

	saved_errno = errno;
	cleanup();

	va_start(ap, fmt);
	vdprintf(2, fmt, ap);
	va_end(ap);

	if (saved_errno)
		dprintf(2, ": %s", strerror(saved_errno));
	write(2, "\n", 1);

	_exit(code);
}

void *
erealloc(void *ptr, size_t size)
{
	void *p;

	if (!(p = realloc(ptr, size)))
		err(1, "realloc");
	return p;
}

void *
ecalloc(size_t nmemb, size_t size)
{
	void *p;

	if (!(p = calloc(nmemb, size)))
		err(1, "calloc");
	return p;
}

char *
estrdup(const char *s)
{
	char *p;

	if (!(p = strdup(s)))
		err(1, "strdup");
	return p;
}

#undef strcasestr
char *
strcasestr(const char *h, const char *n)
{
	size_t i;

	if (!n[0])
		return (char *)h;

	for (; *h; ++h) {
		for (i = 0; n[i] && tolower((unsigned char)n[i]) ==
		            tolower((unsigned char)h[i]); ++i)
			;
		if (n[i] == '\0')
			return (char *)h;
	}

	return NULL;
}

/* Splits fields in the line buffer by replacing TAB separators with NUL ('\0')
 * terminators and assign these fields as pointers. If there are less fields
 * than expected then the field is an empty string constant. */
void
parseline(char *line, char *fields[FieldLast])
{
	char *prev, *s;
	size_t i;

	for (prev = line, i = 0;
	    (s = strchr(prev, '\t')) && i < FieldLast - 1;
	    i++) {
		*s = '\0';
		fields[i] = prev;
		prev = s + 1;
	}
	fields[i++] = prev;
	/* make non-parsed fields empty. */
	for (; i < FieldLast; i++)
		fields[i] = "";
}

/* Parse time to time_t, assumes time_t is signed, ignores fractions. */
int
strtotime(const char *s, time_t *t)
{
	long long l;
	char *e;

	errno = 0;
	l = strtoll(s, &e, 10);
	if (errno || *s == '\0' || *e)
		return -1;
	/* NOTE: assumes time_t is 64-bit on 64-bit platforms:
	         long long (atleast 32-bit) to time_t. */
	if (t)
		*t = (time_t)l;

	return 0;
}

size_t
colw(const char *s)
{
	wchar_t wc;
	size_t col = 0, i, slen;
	int rl, w;

	slen = strlen(s);
	for (i = 0; i < slen; i += rl) {
		if ((rl = mbtowc(&wc, &s[i], slen - i < 4 ? slen - i : 4)) <= 0)
			break;
		if ((w = wcwidth(wc)) == -1)
			continue;
		col += w;
	}
	return col;
}

/* Format `len' columns of characters. If string is shorter pad the rest
 * with characters `pad`. */
int
utf8pad(char *buf, size_t bufsiz, const char *s, size_t len, int pad)
{
	wchar_t wc;
	size_t col = 0, i, slen, siz = 0;
	int rl, w;

	if (!len)
		return -1;

	slen = strlen(s);
	for (i = 0; i < slen; i += rl) {
		if ((rl = mbtowc(&wc, &s[i], slen - i < 4 ? slen - i : 4)) <= 0)
			break;
		if ((w = wcwidth(wc)) == -1)
			continue;
		if (col + w > len || (col + w == len && s[i + rl])) {
			if (siz + 4 >= bufsiz)
				return -1;
			memcpy(&buf[siz], PAD_TRUNCATE_SYMBOL, sizeof(PAD_TRUNCATE_SYMBOL) - 1);
			siz += sizeof(PAD_TRUNCATE_SYMBOL) - 1;
			if (col + w == len && w > 1)
				buf[siz++] = pad;
			buf[siz] = '\0';
			return 0;
		}
		if (siz + rl + 1 >= bufsiz)
			return -1;
		memcpy(&buf[siz], &s[i], rl);
		col += w;
		siz += rl;
		buf[siz] = '\0';
	}

	len -= col;
	if (siz + len + 1 >= bufsiz)
		return -1;
	memset(&buf[siz], pad, len);
	siz += len;
	buf[siz] = '\0';

	return 0;
}

void
printpad(const char *s, int width)
{
	char buf[1024];
	if (utf8pad(buf, sizeof(buf), s, width, ' ') != -1)
		ttywrite(buf);
}

void
resettitle(void)
{
	ttywrite("\x1b""c"); /* rs1: reset title and state */
}

void
updatetitle(void)
{
	unsigned long totalnew = 0, total = 0;
	size_t i;

	for (i = 0; i < nfeeds; i++) {
		totalnew += feeds[i].totalnew;
		total += feeds[i].total;
	}
	ttywritef("\x1b]2;(%lu/%lu) - sfeed_curses\x1b\\", totalnew, total);
}

void
appmode(int on)
{
	/*ttywrite(on ? "\x1b[?1049h" : "\x1b[?1049l");*/ /* smcup, rmcup */
	ttywrite(tparm(on ? enter_ca_mode : exit_ca_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
mousemode(int on)
{
	ttywrite(on ? "\x1b[?1000h" : "\x1b[?1000l"); /* xterm mouse mode */
}

void
cursormode(int on)
{
	/*ttywrite(on ? "\x1b[?25h" : "\x1b[?25l");*/ /* DECTCEM (in)Visible cursor */
	ttywrite(tparm(on ? cursor_normal : cursor_invisible, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
cursorsave(void)
{
	/*ttywrite("\x1b""7");*/
	ttywrite(tparm(save_cursor, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
cursorrestore(void)
{
	/*ttywrite("\x1b""8");*/
	ttywrite(tparm(restore_cursor, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
cursormove(int x, int y)
{
	/*ttywritef("\x1b[%d;%dH", y + 1, x + 1);*/
	ttywrite(tparm(cursor_address, y, x, 0, 0, 0, 0, 0, 0, 0));
}

void
attrmode(int mode)
{
	char *p;

	/*ttywritef("\x1b[%dm", mode);*/
	switch (mode) {
	case ATTR_RESET: p = exit_attribute_mode; break;
	case ATTR_BOLD_ON: p = enter_bold_mode; break;
	case ATTR_FAINT_ON: p = enter_dim_mode; break;
	case ATTR_REVERSE_ON: p = enter_standout_mode; break;
	default: return;
	}
	ttywrite(tparm(p, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
cleareol(void)
{
	/*ttywrite("\x1b[K");*/
	ttywrite(tparm(clr_eol, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
clearscreen(void)
{
	/*ttywrite("\x1b[H\x1b[2J");*/
	ttywrite(tparm(clear_screen, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
cleanup(void)
{
	struct sigaction sa;

	if (!needcleanup)
		return;

	/* restore terminal settings */
	tcsetattr(0, TCSANOW, &tsave);

	cursormode(1);
	appmode(0);
	clearscreen();

	/* xterm mouse-mode */
	if (usemouse)
		mousemode(0);

	resettitle();

	sigemptyset(&sa.sa_mask);
	sa.sa_flags = SA_RESTART; /* require BSD signal semantics */
	sa.sa_handler = SIG_DFL;
	sigaction(SIGWINCH, &sa, NULL);

	needcleanup = 0;
}

void
win_update(struct win *w, int width, int height)
{
	if (width != w->width || height != w->height)
		w->dirty = 1;
	w->width = width;
	w->height = height;
}

void
resizewin(void)
{
	/*struct winsize winsz;
	if (ioctl(0, TIOCGWINSZ, &winsz) == -1)
		err(1, "ioctl");
	win_update(&win, winsz.ws_col, winsz.ws_row);*/

	setupterm(NULL, 1, NULL);
	/* termios globals are changed: `lines` and `columns` */
	win_update(&win, columns, lines);
	if (win.dirty)
		alldirty();
}

void
init(void)
{
	struct sigaction sa;

	tcgetattr(0, &tsave);
	memcpy(&tcur, &tsave, sizeof(tcur));
	tcur.c_lflag &= ~(ECHO|ICANON);
	tcsetattr(0, TCSANOW, &tcur);

	resizewin();

	appmode(1);
	cursormode(0);

	/* xterm mouse-mode */
	if (usemouse)
		mousemode(usemouse);

	updategeom();

	sigemptyset(&sa.sa_mask);
	sa.sa_flags = SA_RESTART; /* require BSD signal semantics */
	sa.sa_handler = sighandler;
	sigaction(SIGHUP, &sa, NULL);
	sigaction(SIGINT, &sa, NULL);
	sigaction(SIGTERM, &sa, NULL);
	sigaction(SIGWINCH, &sa, NULL);

	needcleanup = 1;
}

/* Pipe item line or item field to a program.
   If `field` is -1 then pipe the TSV line, else a specified field.
   if `wantoutput` is 1 then cleanup and restore the tty,
   if 0 then don't do that and also write stdout and stderr to /dev/null. */
void
pipeitem(const char *cmd, struct item *item, int field, int wantoutput)
{
	FILE *fp;
	int i, pid, wpid, status;

	if (wantoutput)
		cleanup();

	switch ((pid = fork())) {
	case -1:
		err(1, "fork");
	case 0:
		if (!wantoutput) {
			dup2(devnullfd, 1);
			dup2(devnullfd, 2);
		}

		errno = 0;
		if (!(fp = popen(cmd, "w")))
			err(1, "popen");
		if (field == -1) {
			for (i = 0; i < FieldLast; i++) {
				if (i)
					fputc('\t', fp);
				fputs(item->fields[i], fp);
			}
		} else {
			fputs(item->fields[field], fp);
		}
		fputc('\n', fp);
		status = pclose(fp);
		status = WIFEXITED(status) ? WEXITSTATUS(status) : 127;
		_exit(status);
	default:
		while ((wpid = wait(NULL)) >= 0 && wpid != pid)
			;

		if (wantoutput) {
			updatesidebar(onlynew);
			updatetitle();
			init();
		}
	}
}

void
forkexec(char *argv[])
{
	switch (fork()) {
	case -1:
		err(1, "fork");
	case 0:
		dup2(devnullfd, 1);
		dup2(devnullfd, 2);
		if (execvp(argv[0], argv) == -1)
			_exit(1);
	}
}

struct row *
pane_row_get(struct pane *p, off_t pos)
{
	if (pos < 0 || pos >= p->nrows)
		return NULL;

	if (p->row_get)
		return p->row_get(p, pos);
	else
		return p->rows + pos;
}

char *
pane_row_text(struct pane *p, struct row *row)
{
	/* custom formatter */
	if (p->row_format)
		return p->row_format(p, row);
	else
		return row->text;
}

int
pane_row_match(struct pane *p, struct row *row, const char *s)
{
	if (p->row_match)
		return p->row_match(p, row, s);
	return (strcasestr(pane_row_text(p, row), s) != NULL);
}

void
pane_row_draw(struct pane *p, off_t pos, int selected)
{
	struct row *row;

	row = pane_row_get(p, pos);

	cursorsave();
	cursormove(p->x, p->y + (pos % p->height));

	if (p->focused)
		THEME_ITEM_FOCUS();
	else
		THEME_ITEM_NORMAL();
	if (row && row->bold)
		THEME_ITEM_BOLD();
	if (selected)
		THEME_ITEM_SELECTED();
	if (row)
		printpad(pane_row_text(p, row), p->width);
	else
		ttywritef("%-*.*s", p->width, p->width, "");

	attrmode(ATTR_RESET);
	cursorrestore();
}

void
pane_setpos(struct pane *p, off_t pos)
{
	if (pos < 0)
		pos = 0; /* clamp */
	if (!p->nrows)
		return; /* invalid */
	if (pos >= p->nrows)
		pos = p->nrows - 1; /* clamp */
	if (pos == p->pos)
		return; /* no change */

	/* is on different scroll region? mark whole pane dirty */
	if (((p->pos - (p->pos % p->height)) / p->height) !=
	    ((pos - (pos % p->height)) / p->height)) {
		p->dirty = 1;
	} else {
		/* only redraw the 2 dirty rows */
		pane_row_draw(p, p->pos, 0);
		pane_row_draw(p, pos, 1);
	}
	p->pos = pos;
}

void
pane_scrollpage(struct pane *p, int pages)
{
	off_t pos;

	if (pages < 0) {
		pos = p->pos - (-pages * p->height);
		pos -= (p->pos % p->height);
		pos += p->height - 1;
		pane_setpos(p, pos);
	} else if (pages > 0) {
		pos = p->pos + (pages * p->height);
		if ((p->pos % p->height))
			pos -= (p->pos % p->height);
		pane_setpos(p, pos);
	}
}

void
pane_scrolln(struct pane *p, int n)
{
	pane_setpos(p, p->pos + n);
}

void
pane_setfocus(struct pane *p, int on)
{
	if (p->focused != on) {
		p->focused = on;
		p->dirty = 1;
	}
}

void
pane_draw(struct pane *p)
{
	off_t pos, y;

	if (p->hidden || !p->dirty)
		return;

	/* draw visible rows */
	pos = p->pos - (p->pos % p->height);
	for (y = 0; y < p->height; y++)
		pane_row_draw(p, y + pos, (y + pos) == p->pos);

	p->dirty = 0;
}

/* Cycle visible pane in a direction, but don't cycle back. */
void
cyclepanen(int n)
{
	int i;

	if (n < 0) {
		n = -n; /* absolute */
		for (i = selpane; n && i - 1 >= 0; i--) {
			if (panes[i - 1].hidden)
				continue;
			n--;
			selpane = i - 1;
		}
	} else if (n > 0) {
		for (i = selpane; n && i + 1 < LEN(panes); i++) {
			if (panes[i + 1].hidden)
				continue;
			n--;
			selpane = i + 1;
		}
	}
}

/* Cycle visible panes. */
void
cyclepane(void)
{
	int i;

	i = selpane;
	cyclepanen(+1);
	/* reached end, cycle back to first most-visible */
	if (i == selpane)
		cyclepanen(-PaneLast);
}

void
updategeom(void)
{
	int w, x;

	panes[PaneFeeds].x = 0;
	panes[PaneFeeds].y = 0;
	/* reserve space for statusbar */
	panes[PaneFeeds].height = win.height > 1 ? win.height - 1 : 1;

	/* NOTE: updatesidebar() must happen before this function for the
	   remaining width */
	if (!panes[PaneFeeds].hidden) {
		w = win.width - panes[PaneFeeds].width;
		x = panes[PaneFeeds].x + panes[PaneFeeds].width;
		/* space for scrollbar if sidebar is visible */
		w--;
		x++;
	} else {
		w = win.width;
		x = 0;
	}

	panes[PaneItems].x = x;
	panes[PaneItems].width = w > 0 ? w - 1 : 0; /* rest and space for scrollbar */
	panes[PaneItems].height = panes[PaneFeeds].height;
	panes[PaneItems].y = panes[PaneFeeds].y;

	scrollbars[PaneFeeds].x = panes[PaneFeeds].x + panes[PaneFeeds].width;
	scrollbars[PaneFeeds].y = panes[PaneFeeds].y;
	scrollbars[PaneFeeds].size = panes[PaneFeeds].height;
	scrollbars[PaneFeeds].hidden = panes[PaneFeeds].hidden;

	scrollbars[PaneItems].x = panes[PaneItems].x + panes[PaneItems].width;
	scrollbars[PaneItems].y = panes[PaneItems].y;
	scrollbars[PaneItems].size = panes[PaneItems].height;

	/* statusbar below */
	statusbar.width = win.width;
	statusbar.x = 0;
	statusbar.y = panes[PaneFeeds].height;

	alldirty();
}

void
scrollbar_setfocus(struct scrollbar *s, int on)
{
	if (s->focused != on) {
		s->focused = on;
		s->dirty = 1;
	}
}

void
scrollbar_update(struct scrollbar *s, off_t pos, off_t nrows, int pageheight)
{
	int tickpos = 0, ticksize = 0;

	/* do not show a scrollbar if all items fit on the page */
	if (nrows > pageheight) {
		ticksize = s->size / ((double)nrows / (double)pageheight);
		if (ticksize == 0)
			ticksize = 1;

		tickpos = (pos / (double)nrows) * (double)s->size;

		/* fixup due to cell precision */
		if (pos + pageheight >= nrows ||
		    tickpos + ticksize >= s->size)
			tickpos = s->size - ticksize;
	}

	if (s->tickpos != tickpos || s->ticksize != ticksize)
		s->dirty = 1;
	s->tickpos = tickpos;
	s->ticksize = ticksize;
}

void
scrollbar_draw(struct scrollbar *s)
{
	off_t y;

	if (s->hidden || !s->dirty)
		return;

	cursorsave();

	/* draw bar (not tick) */
	if (s->focused)
		THEME_SCROLLBAR_FOCUS();
	else
		THEME_SCROLLBAR_NORMAL();
	for (y = 0; y < s->size; y++) {
		if (y >= s->tickpos && y < s->tickpos + s->ticksize)
			continue; /* skip tick */
		cursormove(s->x, s->y + y);
		ttywrite(SCROLLBAR_SYMBOL_BAR);
	}

	/* draw tick */
	if (s->focused)
		THEME_SCROLLBAR_TICK_FOCUS();
	else
		THEME_SCROLLBAR_TICK_NORMAL();
	for (y = s->tickpos; y < s->size && y < s->tickpos + s->ticksize; y++) {
		cursormove(s->x, s->y + y);
		ttywrite(SCROLLBAR_SYMBOL_TICK);
	}

	attrmode(ATTR_RESET);
	cursorrestore();
	s->dirty = 0;
}

int
readch(void)
{
	unsigned char b;
	fd_set readfds;
	struct timeval tv;

	for (;;) {
		FD_ZERO(&readfds);
		FD_SET(0, &readfds);
		tv.tv_sec = 0;
		tv.tv_usec = 250000; /* 250ms */
		switch (select(1, &readfds, NULL, NULL, &tv)) {
		case -1:
			if (errno != EINTR)
				err(1, "select");
			return -2; /* EINTR: like a signal */
		case 0:
			return -3; /* time-out */
		}

		switch (read(0, &b, 1)) {
		case -1: err(1, "read");
		case 0: return EOF;
		default: return (int)b;
		}
	}
}

char *
lineeditor(void)
{
	char *input = NULL;
	size_t cap = 0, nchars = 0;
	int ch;

	for (;;) {
		if (nchars + 1 >= cap) {
			cap = cap ? cap * 2 : 32;
			input = erealloc(input, cap);
		}

		ch = readch();
		if (ch == EOF || ch == '\r' || ch == '\n') {
			input[nchars] = '\0';
			break;
		} else if (ch == '\b' || ch == 0x7f) {
			if (!nchars)
				continue;
			input[--nchars] = '\0';
			ch = '\b'; /* back */
			write(1, &ch, 1);
			ch = ' '; /* blank */
			write(1, &ch, 1);
			ch = '\b'; /* back */
			write(1, &ch, 1);
			continue;
		} else if (ch >= ' ') {
			write(1, &ch, 1);
		} else if (ch < 0) {
			continue; /* process signals later */
		}
		input[nchars++] = ch;
	}
	return input;
}

char *
uiprompt(int x, int y, char *fmt, ...)
{
	va_list ap;
	char *input;
	char buf[32];

	va_start(ap, fmt);
	if (vsnprintf(buf, sizeof(buf), fmt, ap) >= sizeof(buf))
		buf[sizeof(buf) - 1] = '\0';
	va_end(ap);

	cursorsave();
	cursormove(x, y);
	THEME_INPUT_LABEL();
	ttywrite(buf);
	attrmode(ATTR_RESET);

	THEME_INPUT_NORMAL();
	cleareol();
	cursormode(1);
	cursormove(x + colw(buf) + 1, y);

	input = lineeditor();
	attrmode(ATTR_RESET);

	cursormode(0);
	cursorrestore();

	return input;
}

void
statusbar_draw(struct statusbar *s)
{
	if (s->hidden || !s->dirty)
		return;

	cursorsave();
	cursormove(s->x, s->y);
	THEME_STATUSBAR();
	printpad(s->text, s->width);
	attrmode(ATTR_RESET);
	cursorrestore();
	s->dirty = 0;
}

void
statusbar_update(struct statusbar *s, const char *text)
{
	if (s->text && !strcmp(s->text, text))
		return;

	free(s->text);
	s->text = estrdup(text);
	s->dirty = 1;
}

/* Line to item, modifies and splits line in-place. */
int
linetoitem(char *line, struct item *item)
{
	char *fields[FieldLast];
	time_t parsedtime;

	item->line = line;
	parseline(line, fields);
	memcpy(item->fields, fields, sizeof(fields));
	if (urlfile)
		item->link = estrdup(fields[FieldLink]);
	else
		item->link = NULL;

	parsedtime = 0;
	if (!strtotime(fields[FieldUnixTimestamp], &parsedtime)) {
		item->timestamp = parsedtime;
		item->timeok = 1;
	} else {
		item->timestamp = 0;
		item->timeok = 0;
	}

	return 0;
}

void
feed_items_free(struct items *items)
{
	size_t i;

	for (i = 0; i < items->len; i++) {
		free(items->items[i].line);
		free(items->items[i].link);
	}
	free(items->items);
	items->items = NULL;
	items->len = 0;
	items->cap = 0;
}

int
feed_items_get(struct feed *f, FILE *fp, struct items *itemsret)
{
	struct item *item, *items = NULL;
	char *line = NULL;
	size_t cap, i, linesize = 0, nitems;
	ssize_t linelen;
	off_t offset;
	int ret = -1;

	cap = nitems = 0;
	offset = 0;
	for (i = 0; ; i++) {
		if (i + 1 >= cap) {
			cap = cap ? cap * 2 : 16;
			items = erealloc(items, cap * sizeof(struct item));
		}
		if ((linelen = getline(&line, &linesize, fp)) > 0) {
			item = &items[i];

			item->offset = offset;
			offset += linelen;

			if (line[linelen - 1] == '\n')
				line[--linelen] = '\0';

#ifdef LAZYLOAD
			if (f->path) {
				linetoitem(line, item);

				/* data is ignored here, will be lazy-loaded later. */
				item->line = NULL;
				memset(item->fields, 0, sizeof(item->fields));
			} else {
				linetoitem(estrdup(line), item);
			}
#else
			linetoitem(estrdup(line), item);
#endif

			nitems++;
		}
		if (ferror(fp))
			goto err;
		if (linelen <= 0 || feof(fp))
			break;
	}
	itemsret->cap = cap;
	itemsret->items = items;
	itemsret->len = nitems;
	ret = 0;

err:
	if (ret)
		feed_items_free(itemsret);
	free(line);
	return ret;
}

void
updatenewitems(struct feed *f)
{
	struct pane *p;
	struct row *row;
	struct item *item;
	size_t i;

	p = &panes[PaneItems];
	f->totalnew = 0;
	for (i = 0; i < p->nrows; i++) {
		row = &(p->rows[i]); /* do not use pane_row_get */
		item = (struct item *)row->data;
		if (urlfile)
			item->isnew = isurlnew(item->link);
		else
			item->isnew = (item->timeok && item->timestamp >= comparetime);
		row->bold = item->isnew;
		f->totalnew += item->isnew;
	}
	f->total = p->nrows;
}

void
feed_load(struct feed *f, FILE *fp)
{
	static struct items items;
	struct pane *p;
	size_t i;

	feed_items_free(&items);
	if (feed_items_get(f, fp, &items) == -1)
		err(1, "%s: %s", __func__, f->name);

	p = &panes[PaneItems];
	p->pos = 0;
	p->nrows = items.len;
	free(p->rows);
	p->rows = ecalloc(sizeof(p->rows[0]), items.len + 1);
	for (i = 0; i < items.len; i++)
		p->rows[i].data = &(items.items[i]); /* do not use pane_row_get */

	updatenewitems(f);

	p->dirty = 1;
}

void
feed_count(struct feed *f, FILE *fp)
{
	char *fields[FieldLast];
	char *line = NULL;
	size_t linesize = 0;
	ssize_t linelen;
	time_t parsedtime;

	f->totalnew = f->total = 0;
	while ((linelen = getline(&line, &linesize, fp)) > 0) {
		if (line[linelen - 1] == '\n')
			line[--linelen] = '\0';
		parseline(line, fields);

		if (urlfile) {
			f->totalnew += isurlnew(fields[FieldLink]);
		} else {
			parsedtime = 0;
			if (!strtotime(fields[FieldUnixTimestamp], &parsedtime))
				f->totalnew += (parsedtime >= comparetime);
		}
		f->total++;
	}
	free(line);
}

void
feed_setenv(struct feed *f)
{
	if (f && f->path)
		setenv("SFEED_FEED_PATH", f->path, 1);
	else
		unsetenv("SFEED_FEED_PATH");
}

/* Change feed, have one file open, reopen file if needed. */
void
feeds_set(struct feed *f)
{
	if (curfeed) {
		if (curfeed->path && curfeed->fp) {
			fclose(curfeed->fp);
			curfeed->fp = NULL;
		}
	}

	if (f && f->path) {
		if (!f->fp && !(f->fp = fopen(f->path, "rb")))
			err(1, "fopen: %s", f->path);
	}

	feed_setenv(f);

	curfeed = f;
}

void
feeds_load(struct feed *feeds, size_t nfeeds)
{
	struct feed *f;
	size_t i;

	if ((comparetime = time(NULL)) == -1)
		err(1, "time");
	/* 1 day is old news */
	comparetime -= 86400;

	for (i = 0; i < nfeeds; i++) {
		f = &feeds[i];

		if (f->path) {
			if (f->fp) {
				if (fseek(f->fp, 0, SEEK_SET))
					err(1, "fseek: %s", f->path);
			} else {
				if (!(f->fp = fopen(f->path, "rb")))
					err(1, "fopen: %s", f->path);
			}
		}
		if (!f->fp) {
			/* reading from stdin, just recount new */
			if (f == curfeed)
				updatenewitems(f);
			continue;
		}

		/* load first items, because of first selection or stdin. */
		if (f == curfeed) {
			feed_load(f, f->fp);
		} else {
			feed_count(f, f->fp);
			if (f->path && f->fp) {
				fclose(f->fp);
				f->fp = NULL;
			}
		}
	}
}

void
feeds_reloadall(void)
{
	off_t pos;

	pos = panes[PaneItems].pos; /* store numeric position */
	readurls();
	feeds_set(curfeed); /* close and reopen feed if possible */
	feeds_load(feeds, nfeeds);
	/* restore numeric position */
	pane_setpos(&panes[PaneItems], pos);
	updatesidebar(onlynew);
	updatetitle();
}

int
getsidebarwidth(void)
{
	struct feed *feed;
	static char text[1024];
	int i, len, width = 0;

	for (i = 0; i < nfeeds; i++) {
		feed = &feeds[i];

		snprintf(text, sizeof(text), "%s (%lu/%lu)",
		         feed->name, feed->totalnew, feed->total);
		len = colw(text);
		if (len > width)
			width = len;

		if (onlynew && feed->totalnew == 0)
			continue;
	}

	return width;
}

void
updatesidebar(int onlynew)
{
	struct pane *p;
	struct row *row;
	struct feed *feed;
	size_t i, nrows;
	int oldwidth;

	p = &panes[PaneFeeds];

	if (!p->rows)
		p->rows = ecalloc(sizeof(p->rows[0]), nfeeds + 1);

	oldwidth = p->width;
	p->width = getsidebarwidth();

	nrows = 0;
	for (i = 0; i < nfeeds; i++) {
		feed = &feeds[i];

		row = &(p->rows[nrows]);
		row->bold = (feed->totalnew > 0);
		row->data = feed;

		if (onlynew && feed->totalnew == 0)
			continue;

		nrows++;
	}
	p->nrows = nrows;

	if (p->width != oldwidth)
		updategeom();
	else
		p->dirty = 1;

	if (!p->nrows)
		p->pos = 0;
	else if (p->pos >= p->nrows)
		p->pos = p->nrows - 1;
}

void
sighandler(int signo)
{
	switch (signo) {
	case SIGHUP:
	case SIGINT:
	case SIGTERM:
	case SIGWINCH:
		sigstate = signo;
		break;
	}
}

void
alldirty(void)
{
	win.dirty = 1;
	panes[PaneFeeds].dirty = 1;
	panes[PaneItems].dirty = 1;
	scrollbars[PaneFeeds].dirty = 1;
	scrollbars[PaneItems].dirty = 1;
	statusbar.dirty = 1;
}

void
draw(void)
{
	struct row *row;
	struct item *item;
	size_t i;

	if (win.dirty) {
		clearscreen();
		win.dirty = 0;
	}

	/* There is the same amount and indices of panes and scrollbars. */
	for (i = 0; i < LEN(panes); i++) {
		pane_setfocus(&panes[i], i == selpane);
		pane_draw(&panes[i]);

		scrollbar_setfocus(&scrollbars[i], i == selpane);
		scrollbar_update(&scrollbars[i],
		                 panes[i].pos - (panes[i].pos % panes[i].height),
		                 panes[i].nrows, panes[i].height);
		scrollbar_draw(&scrollbars[i]);
	}

	/* If item selection text changed then update the status text. */
	if ((row = pane_row_get(&panes[PaneItems], panes[PaneItems].pos))) {
		item = (struct item *)row->data;
		statusbar_update(&statusbar, item->fields[FieldLink]);
	} else {
		statusbar_update(&statusbar, "");
	}
	statusbar_draw(&statusbar);
}

void
mousereport(int button, int release, int x, int y)
{
	struct pane *p;
	struct feed *f;
	struct row *row;
	struct item *item;
	size_t i;
	int changedpane, dblclick, pos;

	if (!usemouse || release || button == -1)
		return;

	for (i = 0; i < LEN(panes); i++) {
		p = &panes[i];
		if (p->hidden)
			continue;

		if (!(x >= p->x && x < p->x + p->width &&
		      y >= p->y && y < p->y + p->height))
			continue;

		changedpane = (selpane != i);
		selpane = i;
		/* relative position on screen */
		pos = y - p->y + p->pos - (p->pos % p->height);
		dblclick = (pos == p->pos); /* clicking the same row */

		switch (button) {
		case 0: /* left-click */
			if (!p->nrows || pos >= p->nrows)
				break;
			pane_setpos(p, pos);
			if (selpane == PaneFeeds) {
				readurls();
				row = pane_row_get(p, p->pos);
				f = (struct feed *)row->data;
				feeds_set(f);
				if (f->fp)
					feed_load(f, f->fp);
				/* redraw row: counts could be changed */
				updatesidebar(onlynew);
				updatetitle();
			} else if (selpane == PaneItems) {
				if (dblclick && !changedpane) {
					row = pane_row_get(p, p->pos);
					item = (struct item *)row->data;
					markread(p, p->pos, p->pos, 1);
					forkexec((char *[]) { plumber, item->fields[FieldLink], NULL });
				}
			}
			break;
		case 2: /* right-click */
			if (!p->nrows || pos >= p->nrows)
				break;
			pane_setpos(p, pos);
			if (selpane == PaneItems) {
				row = pane_row_get(p, p->pos);
				item = (struct item *)row->data;
				markread(p, p->pos, p->pos, 1);
				pipeitem(piper, item, -1, 1);
			}
			break;
		case 3: /* scroll up */
		case 4: /* scroll down */
			pane_scrollpage(p, button == 3 ? -1 : +1);
			break;
		}
	}
}

/* Custom formatter for feed row. */
char *
feed_row_format(struct pane *p, struct row *row)
{
	struct feed *feed;
	static char text[1024];
	char bufw[256], counts[128];
	int len;

	feed = (struct feed *)row->data;

	len = snprintf(counts, sizeof(counts), "(%lu/%lu)",
	               feed->totalnew, feed->total);
	if (utf8pad(bufw, sizeof(bufw), feed->name, p->width - len, ' ') != -1)
		snprintf(text, sizeof(text), "%s%s", bufw, counts);
	else
		text[0] = '\0';

	return text;
}

int
feed_row_match(struct pane *p, struct row *row, const char *s)
{
	struct feed *feed;

	feed = (struct feed *)row->data;

	return (strcasestr(feed->name, s) != NULL);
}

#ifdef LAZYLOAD
struct row *
item_row_get(struct pane *p, off_t pos)
{
	struct row *itemrow;
	struct item *item;
	struct feed *f;
	char *line = NULL;
	size_t linesize = 0;
	ssize_t linelen;

	itemrow = p->rows + pos;
	item = (struct item *)itemrow->data;

	f = curfeed;
	if (f && f->path && f->fp && !item->line) {
		if (fseek(f->fp, item->offset, SEEK_SET))
			err(1, "fseek: %s", f->path);
		linelen = getline(&line, &linesize, f->fp);

		if (linelen <= 0)
			return NULL;

		if (line[linelen - 1] == '\n')
			line[--linelen] = '\0';

		linetoitem(estrdup(line), item);
		free(line);

		itemrow->data = item;
	}
	return itemrow;
}
#endif

/* Custom formatter for item row. */
char *
item_row_format(struct pane *p, struct row *row)
{
	static char text[1024];
	struct item *item;
	struct tm tm;

	item = (struct item *)row->data;

	if (item->timeok && localtime_r(&(item->timestamp), &tm)) {
		snprintf(text, sizeof(text), "%c %04d-%02d-%02d %02d:%02d %s",
		         item->fields[FieldEnclosure][0] ? '@' : ' ',
		         tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday,
		         tm.tm_hour, tm.tm_min, item->fields[FieldTitle]);
	} else {
		snprintf(text, sizeof(text), "%c                  %s",
		         item->fields[FieldEnclosure][0] ? '@' : ' ',
		         item->fields[FieldTitle]);
	}

	return text;
}

void
markread(struct pane *p, off_t from, off_t to, int isread)
{
	struct row *row;
	struct item *item;
	FILE *fp;
	off_t i;
	const char *cmd;
	int isnew = !isread, pid, wpid, status, visstart;

	if (!urlfile || !p->nrows)
		return;

	if (isread) {
		if (!(cmd = getenv("SFEED_MARK_READ")))
			cmd = "sfeed_markread read";
	} else {
		if (!(cmd = getenv("SFEED_MARK_UNREAD")))
			cmd = "sfeed_markread unread";
	}

	switch ((pid = fork())) {
	case -1:
		err(1, "fork");
	case 0:
		dup2(devnullfd, 1);
		dup2(devnullfd, 2);

		errno = 0;
		if (!(fp = popen(cmd, "w")))
			err(1, "popen");

		for (i = from; i <= to; i++) {
			row = &(p->rows[i]); /* use pane_row_get: no need for lazyload */
			item = (struct item *)row->data;
			if (item->isnew != isnew) {
				fputs(item->link, fp);
				fputc('\n', fp);
			}
		}
		status = pclose(fp);
		status = WIFEXITED(status) ? WEXITSTATUS(status) : 127;
		_exit(status);
	default:
		while ((wpid = wait(&status)) >= 0 && wpid != pid)
			;

		/* fail: exit statuscode was non-zero */
		if (status)
			break;

		visstart = p->pos - (p->pos % p->height); /* visible start */
		for (i = from; i <= to && i < p->nrows; i++) {
			row = &(p->rows[i]);
			item = (struct item *)row->data;
			if (item->isnew == isnew)
				continue;

			row->bold = item->isnew = isnew;
			curfeed->totalnew += isnew ? 1 : -1;

			/* draw if visible on screen */
			if (i >= visstart && i < visstart + p->height)
				pane_row_draw(p, i, i == p->pos);
		}
		updatesidebar(onlynew);
		updatetitle();
	}
}

int
urlcmp(const void *v1, const void *v2)
{
	return strcmp(*((char **)v1), *((char **)v2));
}

void
readurls(void)
{
	FILE *fp;
	char *line = NULL;
	size_t linesiz = 0, cap = 0;
	ssize_t n;

	while (nurls > 0)
		free(urls[--nurls]);
	free(urls);
	urls = NULL;
	nurls = 0;

	if (!urlfile || !(fp = fopen(urlfile, "rb")))
		return;

	while ((n = getline(&line, &linesiz, fp)) > 0) {
		if (line[n - 1] == '\n')
			line[--n] = '\0';
		if (nurls + 1 >= cap) {
			cap = cap ? cap * 2 : 16;
			urls = erealloc(urls, cap * sizeof(char *));
		}
		urls[nurls++] = estrdup(line);
	}
	fclose(fp);
	free(line);

	qsort(urls, nurls, sizeof(char *), urlcmp);
}

int
isurlnew(const char *url)
{
	return bsearch(&url, urls, nurls, sizeof(char *), urlcmp) == NULL;
}

int
main(int argc, char *argv[])
{
	struct pane *p;
	struct feed *f;
	struct row *row;
	struct item *item;
	size_t i;
	char *name, *tmp;
	char *search = NULL; /* search text */
	int ch, button, fd, x, y, release;
	off_t off;

#ifdef __OpenBSD__
	if (pledge("stdio rpath tty proc exec", NULL) == -1)
		err(1, "pledge");
#endif

	setlocale(LC_CTYPE, "");

	if ((tmp = getenv("SFEED_PLUMBER")))
		plumber = tmp;
	if ((tmp = getenv("SFEED_PIPER")))
		piper = tmp;
	if ((tmp = getenv("SFEED_YANKER")))
		yanker = tmp;
	urlfile = getenv("SFEED_URL_FILE");

	panes[PaneFeeds].row_format = feed_row_format;
	panes[PaneFeeds].row_match = feed_row_match;
	panes[PaneItems].row_format = item_row_format;
#ifdef LAZYLOAD
	panes[PaneItems].row_get = item_row_get;
#endif

	feeds = ecalloc(argc, sizeof(struct feed));
	if (argc == 1) {
		nfeeds = 1;
		f = &feeds[0];
		f->name = "stdin";
		if (!(f->fp = fdopen(0, "rb")))
			err(1, "fdopen");
	} else {
		for (i = 1; i < argc; i++) {
			f = &feeds[i - 1];
			f->path = argv[i];
			name = ((name = strrchr(argv[i], '/'))) ? name + 1 : argv[i];
			f->name = name;
		}
		nfeeds = argc - 1;
	}
	readurls();
	feeds_set(&feeds[0]);
	feeds_load(feeds, nfeeds);

	if (!isatty(0)) {
		if ((fd = open("/dev/tty", O_RDONLY)) == -1)
			err(1, "open: /dev/tty");
		if (dup2(fd, 0) == -1)
			err(1, "dup2: /dev/tty");
	}
	if (argc == 1)
		feeds[0].fp = NULL;

	if (argc > 1) {
		panes[PaneFeeds].hidden = 0;
		selpane = PaneFeeds;
	} else {
		panes[PaneFeeds].hidden = 1;
		selpane = PaneItems;
	}

	if ((devnullfd = open("/dev/null", O_WRONLY)) == -1)
		err(1, "open: /dev/null");

	updatesidebar(onlynew);
	updatetitle();
	init();
	draw();

	while (1) {
		if ((ch = readch()) < 0)
			goto event;
		switch (ch) {
		case '\x1b':
			if ((ch = readch()) < 0)
				goto event;
			if (ch != '[' && ch != 'O')
				continue; /* unhandled */
			if ((ch = readch()) < 0)
				goto event;
			switch (ch) {
			case 'M': /* reported mouse event */
				if ((ch = readch()) < 0)
					goto event;
				/* button numbers (0 - 2) encoded in lowest 2 bits
				   release does not indicate which button (so set to 0).
				   Handle extended buttons like scrollwheels
				   and side-buttons by substracting 64 in each range. */
				for (i = 0, ch -= 32; ch >= 64; i += 3)
					ch -= 64;

				release = 0;
				button = (ch & 3) + i;
				if (!i && button == 3) {
					release = 1;
					button = -1;
				}

				/* X10 mouse-encoding */
				if ((ch = readch()) < 0)
					goto event;
				x = ch;
				if ((ch = readch()) < 0)
					goto event;
				y = ch;
				mousereport(button, release, x - 33, y - 33);
				break;
			case 'A': goto keyup;    /* arrow up */
			case 'B': goto keydown;  /* arrow down */
			case 'C': goto keyright; /* arrow left */
			case 'D': goto keyleft;  /* arrow right */
			case 'F': goto endpos;   /* end */
			case 'H': goto startpos; /* home */
			case '4': /* end */
				if ((ch = readch()) < 0)
					goto event;
				if (ch == '~')
					goto endpos;
				continue;
			case '5': /* page up */
				if ((ch = readch()) < 0)
					goto event;
				if (ch == '~')
					goto prevpage;
				continue;
			case '6': /* page down */
				if ((ch = readch()) < 0)
					goto event;
				if (ch == '~')
					goto nextpage;
				continue;
			}
			break;
keyup:
		case 'k':
			pane_scrolln(&panes[selpane], -1);
			break;
keydown:
		case 'j':
			pane_scrolln(&panes[selpane], +1);
			break;
keyleft:
		case 'h':
			cyclepanen(-1);
			break;
keyright:
		case 'l':
			cyclepanen(+1);
			break;
		case '\t':
			cyclepane();
			break;
startpos:
		case 'g':
			pane_setpos(&panes[selpane], 0);
			break;
endpos:
		case 'G':
			p = &panes[selpane];
			if (p->nrows)
				pane_setpos(p, p->nrows - 1);
			break;
prevpage:
		case 2: /* ^B */
			pane_scrollpage(&panes[selpane], -1);
			break;
nextpage:
		case ' ':
		case 6: /* ^F */
			pane_scrollpage(&panes[selpane], +1);
			break;
		case '/': /* new search (forward) */
		case '?': /* new search (backward) */
		case 'n': /* search again (forward) */
		case 'N': /* search again (backward) */
			p = &panes[selpane];
			if (!p->nrows)
				break;

			/* prompt for new input */
			if (ch == '?' || ch == '/') {
				tmp = ch == '?' ? "backward" : "forward";
				free(search);
				search = uiprompt(statusbar.x, statusbar.y,
				                  "Search (%s):", tmp);
				statusbar.dirty = 1;
			}
			if (!search)
				break;

			if (ch == '/' || ch == 'n') {
				/* forward */
				for (off = p->pos + 1; off < p->nrows; off++) {
					if (pane_row_match(p, pane_row_get(p, off), search)) {
						pane_setpos(p, off);
						break;
					}
				}
			} else {
				/* backward */
				for (off = p->pos - 1; off >= 0; off--) {
					if (pane_row_match(p, pane_row_get(p, off), search)) {
						pane_setpos(p, off);
						break;
					}
				}
			}
			break;
		case 12: /* ^L, redraw */
			alldirty();
			break;
		case 'R': /* reload all files */
			feeds_reloadall();
			break;
		case 'a': /* attachment */
		case 'e': /* enclosure */
		case '@':
			if (selpane == PaneItems && panes[selpane].nrows) {
				p = &panes[selpane];
				row = pane_row_get(p, p->pos);
				item = (struct item *)row->data;
				forkexec((char *[]) { plumber, item->fields[FieldEnclosure], NULL });
			}
			break;
		case 'm': /* toggle mouse mode */
			usemouse = !usemouse;
			mousemode(usemouse);
			break;
		case 's': /* toggle sidebar */
			panes[PaneFeeds].hidden = !panes[PaneFeeds].hidden;
			if (selpane == PaneFeeds && panes[selpane].hidden)
				selpane = PaneItems;
			updategeom();
			break;
		case 't': /* toggle showing only new in sidebar */
			onlynew = !onlynew;
			pane_setpos(&panes[PaneFeeds], 0);
			updatesidebar(onlynew);
			break;
		case 'o': /* feeds: load, items: plumb url */
		case '\n':
			p = &panes[selpane];
			if (selpane == PaneFeeds && panes[selpane].nrows) {
				readurls();
				row = pane_row_get(p, p->pos);
				f = (struct feed *)row->data;
				feeds_set(f);
				if (f->fp)
					feed_load(f, f->fp);
				/* redraw row: counts could be changed */
				updatesidebar(onlynew);
				updatetitle();
			} else if (selpane == PaneItems && panes[selpane].nrows) {
				row = pane_row_get(p, p->pos);
				item = (struct item *)row->data;
				markread(p, p->pos, p->pos, 1);
				forkexec((char *[]) { plumber, item->fields[FieldLink], NULL });
			}
			break;
		case 'c': /* items: pipe TSV line to program */
		case 'p':
		case '|':
		case 'y': /* yank: pipe TSV field to yank url to clipboard */
		case 'E': /* yank: pipe TSV field to yank enclosure to clipboard */
			if (selpane == PaneItems && panes[selpane].nrows) {
				p = &panes[selpane];
				row = pane_row_get(p, p->pos);
				item = (struct item *)row->data;
				switch (ch) {
				case 'y': pipeitem(yanker, item, FieldLink, 0); break;
				case 'E': pipeitem(yanker, item, FieldEnclosure, 0); break;
				default:
					markread(p, p->pos, p->pos, 1);
					pipeitem(piper, item, -1, 1);
					break;
				}
			}
			break;
		case 'f': /* mark all read */
		case 'F': /* mark all unread */
			if (panes[PaneItems].nrows) {
				p = &panes[PaneItems];
				markread(p, 0, p->nrows - 1, ch == 'f');
			}
			break;
		case 'r': /* mark item as read */
		case 'u': /* mark item as unread */
			if (selpane == PaneItems && panes[selpane].nrows) {
				p = &panes[selpane];
				markread(p, p->pos, p->pos, ch == 'r');
			}
			break;
		case 4: /* EOT */
		case 'q': goto end;
		}
event:
		if (ch == EOF)
			goto end;
		else if (ch == -3 && sigstate == 0)
			continue; /* just a time-out, nothing to do */

		/* handle last signal */
		switch (sigstate) {
		case SIGHUP:
			feeds_reloadall();
			sigstate = 0;
			break;
		case SIGINT:
		case SIGTERM:
			cleanup();
			_exit(128 + sigstate);
		case SIGWINCH:
			resizewin();
			updategeom();
			sigstate = 0;
			break;
		}

		draw();
	}
end:
	cleanup();

	return 0;
}
