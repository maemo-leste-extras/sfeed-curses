#include <sys/select.h>
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

#define LEN(a)              sizeof((a))/sizeof((a)[0])
#define PAD_TRUNCATE_SYMBOL "\xe2\x80\xa6" /* symbol: "ellipsis" */
#define SCROLLBAR_SYMBOL    "\xe2\x94\x82" /* symbol: "light vertical" */

enum {
	ATTR_RESET = 0,
	ATTR_BOLD_ON = 1, ATTR_FAINT_ON = 2,
	ATTR_REVERSE_ON = 7, ATTR_REVERSE_OFF = 27,
};

enum Pane { PaneFeeds, PaneItems, PaneLast };

enum {
	FieldUnixTimestamp = 0, FieldTitle, FieldLink, FieldContent,
	FieldContentType, FieldId, FieldAuthor, FieldEnclosure, FieldLast
};

struct win {
	int width;
	int height;
	int dirty;
};

struct row {
	char *text;
	int bold;
	void *data;
};

struct pane {
	int x; /* absolute x position on the screen */
	int y; /* absolute y position on the screen */
	int width; /* absolute width of the window */
	int height; /* absolute height of the window */
	off_t pos; /* focused row position */
	struct row *rows;
	size_t nrows; /* total amount of rows */
	int focused; /* has focus or not */
	int hidden; /* is visible or not */
	int dirty; /* needs draw update */

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

/* feed info */
struct feed {
	char         *name;     /* feed name */
	char         *path;     /* path to feed or NULL for stdin */
	unsigned long totalnew; /* amount of new items per feed */
	unsigned long total;    /* total items */
	FILE *fp;               /* file pointer */
};

struct item {
	char *link; /* separate link field (always loaded) */
	char *fields[FieldLast];
	char *line; /* allocated split line */
	time_t timestamp;
	int timeok;
	int isnew;
	off_t offset; /* line offset in file for lazyload */
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

/* config */

/* Allow to lazyload items when a file is specified? This saves memory but
   increases some latency when seeking items. It also causes issues if the
   feed is changed while having the UI open (and offsets are changed). */
/*#define LAZYLOAD 1 */

static char *plumber = "xdg-open"; /* environment variable: $SFEED_PLUMBER */
static char *piper = "less"; /* environment variable: $SFEED_PIPER */

/* like BSD err(), but calls cleanup() and _exit(). */
void
err(int code, const char *fmt, ...)
{
	va_list ap;
	int saved_errno;

	saved_errno = errno;
	cleanup();

	va_start(ap, fmt);
	vfprintf(stderr, fmt, ap);
	va_end(ap);

	fputs(": ", stderr);
	errno = saved_errno;
	perror(NULL);

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

/* format `len' columns of characters. If string is shorter pad the rest
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
	utf8pad(buf, sizeof(buf), s, width, ' ');
	fputs(buf, stdout);
}

void
resettitle(void)
{
	fputs("\x1b""c", stdout); /* rs1: reset title and state */
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
	printf("\x1b]2;(%lu/%lu) - sfeed_curses\x1b\\", totalnew, total);
}

void
appmode(int on)
{
	/*fputs(on ? "\x1b[?1049h" : "\x1b[?1049l", stdout);*/ /* smcup, rmcup */
	putp(tparm(on ? enter_ca_mode : exit_ca_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
mousemode(int on)
{
	fputs(on ? "\x1b[?1000h" : "\x1b[?1000l", stdout); /* xterm mouse mode */
}

void
cursormode(int on)
{
	/*fputs(on ? "\x1b[?25h" : "\x1b[?25l", stdout);*/ /* DECTCEM (in)Visible cursor */
	putp(tparm(on ? cursor_visible : cursor_invisible, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
cursorsave(void)
{
	/*fputs("\x1b""7", stdout);*/
	putp(tparm(save_cursor, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
cursorrestore(void)
{
	/*fputs("\x1b""8", stdout);*/
	putp(tparm(restore_cursor, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
cursormove(int x, int y)
{
	/*printf("\x1b[%d;%dH", y + 1, x + 1);*/
	putp(tparm(cursor_address, y, x, 0, 0, 0, 0, 0, 0, 0));
}

void
attrmode(int mode)
{
	char *p;

	/*printf("\x1b[%dm", mode);*/
	switch (mode) {
	case ATTR_RESET: p = exit_attribute_mode; break;
	case ATTR_BOLD_ON: p = enter_bold_mode; break;
	case ATTR_FAINT_ON: p = enter_dim_mode; break;
	case ATTR_REVERSE_ON: p = enter_standout_mode; break;
	case ATTR_REVERSE_OFF: p = exit_standout_mode; break;
	default: return;
	}
	putp(tparm(p, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
cleareol(void)
{
	/*fputs("\x1b[K", stdout);*/
	putp(tparm(clr_eol, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
clearscreen(void)
{
	/*fputs("\x1b[H\x1b[2J", stdout);*/
	putp(tparm(clear_screen, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

void
cleanup(void)
{
	struct sigaction sa;

	if (!needcleanup)
		return;

	/* restore terminal settings */
	tcsetattr(0, TCSANOW, &tsave);

	appmode(0);
	cursormode(1);
	clearscreen();

	/* xterm mouse-mode */
	if (usemouse)
		mousemode(0);

	resettitle();
	fflush(stdout);

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

	cursormode(0);
	appmode(1);

	/* xterm mouse-mode */
	if (usemouse)
		mousemode(usemouse);

	updategeom();
	fflush(stdout);

	sigemptyset(&sa.sa_mask);
	sa.sa_flags = SA_RESTART; /* require BSD signal semantics */
	sa.sa_handler = sighandler;
	sigaction(SIGHUP, &sa, NULL);
	sigaction(SIGINT, &sa, NULL);
	sigaction(SIGTERM, &sa, NULL);
	sigaction(SIGWINCH, &sa, NULL);

	needcleanup = 1;
}

/* pipe item to a program, if `wantoutput` is set then cleanup and restore the
   terminal attribute settings, if not set then don't do that and also ignore
   stdout and stderr. */
void
pipeitem(const char *cmd, struct item *item, int wantoutput)
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
		for (i = 0; i < FieldLast; i++) {
			if (i)
				fputc('\t', fp);
			fputs(item->fields[i], fp);
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
plumb(const char *cmd, char *url)
{
	switch (fork()) {
	case -1:
		err(1, "fork");
	case 0:
		dup2(devnullfd, 1);
		dup2(devnullfd, 2);
		if (execlp(cmd, cmd, url, NULL) < 0)
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
pane_row_draw(struct pane *p, off_t pos)
{
	struct row *row;
	int r, y;

	row = pane_row_get(p, pos);

	y = p->y + (pos % p->height); /* relative position on screen */
	cursorsave();
	cursormove(p->x, y);

	r = 0;
	if (pos == p->pos) {
		attrmode(ATTR_REVERSE_ON);
		if (!p->focused)
			attrmode(ATTR_FAINT_ON);
		r = 1;
	} else if (p->nrows && pos < p->nrows && row && row->bold) {
		attrmode(ATTR_BOLD_ON);
		r = 1;
	}
	if (row)
		printpad(pane_row_text(p, row), p->width);
	else
		printf("%-*.*s", p->width, p->width, "");
	if (r)
		attrmode(ATTR_RESET);
	cursorrestore();
}

void
pane_setpos(struct pane *p, off_t pos)
{
	off_t prev;

	if (pos < 0)
		pos = 0; /* clamp */
	if (!p->nrows)
		return; /* invalid */
	if (pos >= p->nrows)
		pos = p->nrows - 1; /* clamp */
	if (pos == p->pos)
		return; /* no change */

	/* is on different scroll region? mark dirty */
	if (((p->pos - (p->pos % p->height)) / p->height) !=
	    ((pos - (pos % p->height)) / p->height)) {
		p->pos = pos;
		p->dirty = 1;
		pane_draw(p);
	} else {
		/* only redraw the 1 or 2 dirty rows */
		prev = p->pos;
		p->pos = pos;
		pane_row_draw(p, prev); /* draw previous row again */
		pane_row_draw(p, p->pos); /* draw new highlighted row */
		fflush(stdout); /* flush and update directly */
	}
}

void
pane_setstartpos(struct pane *p)
{
	pane_setpos(p, 0);
}

void
pane_setendpos(struct pane *p)
{
	pane_setpos(p, p->nrows - 1);
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

	pos = p->pos - (p->pos % p->height);
	for (y = 0; y < p->height; y++)
		pane_row_draw(p, y + pos);

	p->dirty = 0;
}

/* cycle visible pane in a direction, but don't cycle back */
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

/* cycle visible panes */
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
	panes[PaneFeeds].height = win.height - 1; /* space for statusbar */

	/* NOTE: updatesidebar() must happen before updategeometry for the
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

	panes[PaneItems].width = w - 1; /* rest and space for scrollbar */
	panes[PaneItems].height = win.height - 1; /* space for statusbar */
	panes[PaneItems].x = x;
	panes[PaneItems].y = 0;

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
	statusbar.y = win.height - 1;

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
	if (!s->focused)
		attrmode(ATTR_FAINT_ON);
	for (y = 0; y < s->size; y++) {
		cursormove(s->x, s->y + y);
		if (y >= s->tickpos && y < s->tickpos + s->ticksize) {
			attrmode(ATTR_REVERSE_ON);
			fputs(" ", stdout);
			attrmode(ATTR_REVERSE_OFF);
		} else {
			fputs(SCROLLBAR_SYMBOL, stdout);
		}
	}
	if (!s->focused)
		attrmode(ATTR_RESET);
	cursorrestore();
	s->dirty = 0;
}

int
readch(void)
{
	unsigned char b;
	fd_set readfds;

	for (;;) {
		FD_ZERO(&readfds);
		FD_SET(0, &readfds);
		if (select(1, &readfds, NULL, NULL, NULL) == -1) {
			if (errno != EINTR)
				err(1, "select");
			return -2; /* EINTR: like a signal */
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
	attrmode(ATTR_REVERSE_ON);
	fputs(buf, stdout);
	attrmode(ATTR_REVERSE_OFF);
	cleareol();
	cursormode(1);
	cursormove(x + colw(buf) + 1, y);
	fflush(stdout);

	input = lineeditor();

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
	attrmode(ATTR_REVERSE_ON);
	printpad(s->text, s->width);
	attrmode(ATTR_REVERSE_OFF);
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

/* line to item, modifies and splits line in-place */
int
linetoitem(char *line, struct item *item)
{
	char *fields[FieldLast];
	time_t parsedtime;

	item->line = line;
	parseline(line, fields);
	memcpy(item->fields, fields, sizeof(fields));
	item->link = estrdup(fields[FieldLink]);

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

int
feed_getitems(struct feed *f, FILE *fp, struct item **items, size_t *nitems)
{
	struct item *item;
	char *line = NULL;
	size_t cap, i, linesize = 0;
	ssize_t linelen;
	off_t offset;
	int ret = -1;

	*items = NULL;
	*nitems = 0;

	cap = 0;
	offset = 0;
	for (i = 0; ; i++) {
		if (i + 1 >= cap) {
			cap = cap ? cap * 2 : 16;
			*items = erealloc(*items, cap * sizeof(struct item));
		}
		if ((linelen = getline(&line, &linesize, fp)) > 0) {
			item = (*items) + i;

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

			(*nitems)++;
		}
		if (ferror(fp))
			goto err;
		if (linelen <= 0 || feof(fp))
			break;
	}
	ret = 0;

err:
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
	static struct item *items = NULL;
	static size_t nitems = 0;
	struct pane *p;
	struct row *row;
	size_t i;

	for (i = 0; i < nitems; i++) {
		free(items[i].line);
		free(items[i].link);
	}
	free(items);
	items = NULL;
	nitems = 0;

	p = &panes[PaneItems];
	free(p->rows);
	p->rows = NULL;
	p->nrows = 0;

	if (feed_getitems(f, fp, &items, &nitems) == -1)
		err(1, "%s: %s", __func__, f->name);

	p->pos = 0;
	p->nrows = nitems;
	p->rows = ecalloc(sizeof(p->rows[0]), nitems + 1);
	for (i = 0; i < nitems; i++) {
		row = &(p->rows[i]); /* do not use pane_row_get */
		row->text = ""; /* custom formatter */
		row->data = &items[i];
	}

	updatenewitems(f);

	p->dirty = 1;
	scrollbars[PaneItems].dirty = 1;
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

/* change feed, have one file open, reopen file if needed */
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
		if (i == 0 || f == curfeed) {
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
	feeds_load(feeds, nfeeds);
	/* restore numeric position */
	pane_setpos(&panes[PaneItems], pos);
	updatesidebar(onlynew);
	updategeom();
	updatetitle();
}

void
updatesidebar(int onlynew)
{
	struct pane *p;
	struct row *row;
	struct feed *feed;
	size_t i, nrows;
	int len, width;

	p = &panes[PaneFeeds];

	if (!p->rows)
		p->rows = ecalloc(sizeof(p->rows[0]), nfeeds + 1);

	nrows = 0;
	width = 0;
	for (i = 0; i < nfeeds; i++) {
		feed = &feeds[i];

		row = &(p->rows[nrows]);
		row->text = ""; /* custom formatter is used */
		row->bold = (feed->totalnew > 0);
		row->data = feed;

		len = colw(pane_row_text(p, row));
		if (len > width)
			width = len;

		if (onlynew && feed->totalnew == 0)
			continue;

		nrows++;
	}
	p->nrows = nrows;
	p->width = width;
	if (!p->nrows)
		p->pos = 0;
	else if (p->pos >= p->nrows)
		p->pos = p->nrows - 1;
	p->dirty = 1;
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

	if (win.width <= 1 || win.height <= 3 ||
	    (!panes[PaneFeeds].hidden && win.width <= panes[PaneFeeds].width + 2))
		return;

	if (win.dirty) {
		clearscreen();
		win.dirty = 0;
	}

	/* if item selection text changed, update the status text */
	if (panes[PaneItems].nrows &&
	    (row = pane_row_get(&panes[PaneItems], panes[PaneItems].pos))) {
		item = (struct item *)row->data;
		statusbar_update(&statusbar, item->link);
	} else {
		statusbar_update(&statusbar, "");
	}

	/* NOTE: theres the same amount and indices of panes and scrollbars. */
	for (i = 0; i < LEN(panes); i++) {
		pane_setfocus(&panes[i], i == selpane);
		pane_draw(&panes[i]);

		scrollbar_setfocus(&scrollbars[i], i == selpane);
		scrollbar_update(&scrollbars[i],
		                 panes[i].pos - (panes[i].pos % panes[i].height),
		                 panes[i].nrows, panes[i].height);
		scrollbar_draw(&scrollbars[i]);
	}
	statusbar_draw(&statusbar);
	fflush(stdout);
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
			if (i == PaneFeeds) {
				row = pane_row_get(p, pos);
				f = (struct feed *)row->data;
				feeds_set(f);
				if (f->fp)
					feed_load(f, f->fp);
				/* redraw row: counts could be changed */
				updatesidebar(onlynew);
				updategeom();
				updatetitle();
			} else if (i == PaneItems) {
				if (dblclick && !changedpane) {
					row = pane_row_get(&panes[PaneItems], pos);
					item = (struct item *)row->data;
					markread(p, p->pos, p->pos, 1);
					plumb(plumber, item->fields[FieldLink]);
				}
			}
			break;
		case 2: /* right-click */
			if (!p->nrows || pos >= p->nrows)
				break;
			pane_setpos(p, pos);
			if (i == PaneItems) {
				p = &panes[PaneItems];
				row = pane_row_get(p, p->pos);
				item = (struct item *)row->data;
				markread(p, p->pos, p->pos, 1);
				pipeitem(piper, item, 1);
			}
			break;
		case 3: /* scroll up */
		case 4: /* scroll down */
			pane_scrollpage(p, button == 3 ? -1 : +1);
			break;
		}
	}
}

/* custom formatter for feed row */
char *
feed_row_format(struct pane *p, struct row *row)
{
	struct feed *feed;
	static char text[1024];
	char bufw[256], counts[128];
	int len;

	feed = (struct feed *)row->data;

	if (p->width) {
		len = snprintf(counts, sizeof(counts), "(%lu/%lu)",
		               feed->totalnew, feed->total);
		utf8pad(bufw, sizeof(bufw), feed->name, p->width - len, ' ');
		snprintf(text, sizeof(text), "%s%s", bufw, counts);
	} else {
		snprintf(text, sizeof(text), "%s (%lu/%lu)",
		         feed->name, feed->totalnew, feed->total);
	}

	return text;
}

int
feed_row_match(struct pane *p, struct row *row, const char *s)
{
	struct feed *feed;

	feed = (struct feed *)row->data;

	return (strcasestr(feed->name, s) != NULL);
}

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

/* custom formatter for item row */
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
		localtime_r(&(item->timestamp), &tm);
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
	int isnew = !isread, pid, wpid, status;

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
			row = &(p->rows[i]);
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
		for (i = from; i <= to && i < p->nrows; i++) {
			row = &(p->rows[i]);
			item = (struct item *)row->data;
			if (item->isnew != isnew) {
				row->bold = item->isnew = isnew;
				curfeed->totalnew += isnew ? 1 : -1;
			}
		}
		updatesidebar(onlynew);
		updategeom();
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

	setlocale(LC_CTYPE, "");

	if ((tmp = getenv("SFEED_PLUMBER")))
		plumber = tmp;
	if ((tmp = getenv("SFEED_PIPER")))
		piper = tmp;
	urlfile = getenv("SFEED_URL_FILE");

	panes[PaneFeeds].row_format = feed_row_format;
	panes[PaneFeeds].row_match = feed_row_match;
	panes[PaneItems].row_format = item_row_format;
	panes[PaneItems].row_get = item_row_get;

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
	feeds_load(feeds, nfeeds);
	feeds_set(&feeds[0]);

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

	if ((devnullfd = open("/dev/null", O_WRONLY)) < 0)
		err(1, "open: /dev/null");

	updatetitle();
	updatesidebar(onlynew);
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
			pane_setstartpos(&panes[selpane]);
			break;
endpos:
		case 'G':
			pane_setendpos(&panes[selpane]);
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
			if (selpane == PaneItems && panes[PaneItems].nrows) {
				p = &panes[PaneItems];
				row = pane_row_get(p, p->pos);
				item = (struct item *)row->data;
				plumb(plumber, item->fields[FieldEnclosure]);
			}
			break;
		case 'm': /* toggle mouse mode */
			usemouse = !usemouse;
			mousemode(usemouse);
			break;
		case 's': /* toggle sidebar */
			panes[PaneFeeds].hidden = !panes[PaneFeeds].hidden;
			if (selpane == PaneFeeds && panes[PaneFeeds].hidden)
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
			if (selpane == PaneFeeds && panes[PaneFeeds].nrows) {
				p = &panes[selpane];
				row = pane_row_get(p, p->pos);
				f = (struct feed *)row->data;
				feeds_set(f);
				if (f->fp)
					feed_load(f, f->fp);
				/* redraw row: counts could be changed */
				updatesidebar(onlynew);
				updategeom();
				updatetitle();
			} else if (selpane == PaneItems && panes[PaneItems].nrows) {
				p = &panes[PaneItems];
				row = pane_row_get(p, p->pos);
				item = (struct item *)row->data;
				markread(p, p->pos, p->pos, 1);
				plumb(plumber, item->link);
			}
			break;
		case 'c': /* items: pipe TSV line to program */
		case 'p':
		case '|':
		case 'y': /* yank: pipe TSV line to yank url to clipboard */
		case 'E': /* yank: pipe TSV line to yank enclosure to clipboard */
			if (selpane == PaneItems && panes[PaneItems].nrows) {
				p = &panes[PaneItems];
				row = pane_row_get(p, p->pos);
				item = (struct item *)row->data;
				switch (ch) {
				case 'y': pipeitem("cut -f 3 | xclip -r", item, 0); break;
				case 'E': pipeitem("cut -f 8 | xclip -r", item, 0); break;
				default:
					markread(p, p->pos, p->pos, 1);
					pipeitem(piper, item, 1);
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
			if (selpane == PaneItems && panes[PaneItems].nrows) {
				p = &panes[PaneItems];
				markread(p, p->pos, p->pos, ch == 'r');
			}
			break;
		case 4: /* EOT */
		case 'q': goto end;
		}
event:
		if (ch == EOF)
			goto end;

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
