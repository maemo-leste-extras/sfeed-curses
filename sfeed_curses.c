#include <sys/ioctl.h>
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

#define LEN(a) sizeof((a))/sizeof((a)[0])

enum {
	FieldUnixTimestamp = 0, FieldTitle, FieldLink, FieldContent,
	FieldContentType, FieldId, FieldAuthor, FieldEnclosure, FieldLast
};

enum Pane { PaneFeeds, PaneItems, PaneLast };

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

struct scrollbar {
	int tickpos;
	int ticksize;
	int x; /* absolute x position of the window on the screen */
	int y; /* absolute y position of the window on the screen */
	int size; /* absolute size of the bar */
	int focused; /* has focus or not */
	int hidden; /* is visible or not */
	int dirty; /* needs draw update */
};

struct pane {
	int x; /* absolute x position of the window on the screen */
	int y; /* absolute y position of the window on the screen */
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

struct statusbar {
	int x; /* absolute x position of the window on the screen */
	int y; /* absolute y position of the window on the screen */
	int width; /* absolute width of the bar */
	char *text; /* data */
	int hidden; /* is visible or not */
	int dirty; /* needs draw update */
};

#undef err
void err(int, const char *, ...);

void alldirty(void);
void cleanup(void);
void draw(void);
void pane_draw(struct pane *);
void pane_setpos(struct pane *p, off_t pos);
void statusbar_draw(struct statusbar *);
void sighandler(int);
void updategeom(void);
void updatesidebar(int);

static struct statusbar statusbar;
static struct pane panes[PaneLast];
static struct scrollbar scrollbars[PaneLast]; /* each pane has a scrollbar */
static struct win win;
static size_t selpane;

static struct termios tsave; /* terminal state at startup */
static struct termios tcur;

static struct winsize winsz; /* window size information */
static int ttyfd = 0; /* fd of tty */
static int devnullfd;

static int needcleanup;

/* feed info */
struct feed {
	char         *name;     /* feed name */
	char         *path;     /* path to feed or NULL from stdin */
	unsigned long totalnew; /* amount of new items per feed */
	unsigned long total;    /* total items */
	FILE *fp;               /* file pointer */
};

static struct feed *feeds;
static struct feed *curfeed;
static size_t nfeeds; /* amount of feeds */

static time_t comparetime;

struct item {
	char *fields[FieldLast];
	char *line; /* allocated split line */
	time_t timestamp;
	struct tm tm;
	int isnew;
	off_t offset; /* line offset in file */
};

/* config */

/* use xterm mouse tracking */
static int usemouse = 1;
/* show only new in sidebar (default = 0 = all) */
static int onlynew = 0;
/* Allow to lazyload items when a file is specified? This saves memory but
   increases some latency when seeking items. It also causes issues if the
   feed is changed while having the UI open (and offsets are changed). */
static int lazyload = 0;

static char *plumber = "xdg-open";
static char *piper = "less";

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
			memcpy(&buf[siz], "\xe2\x80\xa6", 3); /* ellipsis */
			siz += 3;
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
	printf("\x1b%c", 'c'); /* reset title and state */
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
mousemode(int on)
{
	putp(on ? "\x1b[?1000h" : "\x1b[?1000l");
}

void
cleanup(void)
{
	struct sigaction sa;

	if (!needcleanup)
		return;

	/* restore terminal settings */
	tcsetattr(ttyfd, TCSANOW, &tsave);

	putp(tparm(cursor_visible, 0, 0, 0, 0, 0, 0, 0, 0, 0));
	putp(tparm(clear_screen, 0, 0, 0, 0, 0, 0, 0, 0, 0));

	/* xterm mouse-mode */
	if (usemouse)
		mousemode(0);

	resettitle();
	fflush(stdout);

	sigemptyset(&sa.sa_mask);
	sa.sa_flags = SA_RESTART;
	sa.sa_handler = SIG_DFL;
	if (sigaction(SIGWINCH, &sa, NULL) == -1)
		err(1, "sigaction: SIGWINCH");

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
getwinsize(void)
{
	if (ioctl(ttyfd, TIOCGWINSZ, &winsz) == -1)
		err(1, "ioctl");
	win_update(&win, winsz.ws_col, winsz.ws_row);
	if (win.dirty)
		alldirty();
}

void
init(void)
{
	struct sigaction sa;

	tcgetattr(ttyfd, &tsave);
	memcpy(&tcur, &tsave, sizeof(tcur));
	tcur.c_lflag &= ~(ECHO|ICANON);
	tcsetattr(ttyfd, TCSANOW, &tcur);

	getwinsize();

	setupterm(NULL, 1, NULL);
	putp(tparm(save_cursor, 0, 0, 0, 0, 0, 0, 0, 0, 0));
	putp(tparm(cursor_invisible, 0, 0, 0, 0, 0, 0, 0, 0, 0));

	/* xterm mouse-mode */
	if (usemouse)
		mousemode(usemouse);

	updategeom();

	fflush(stdout);

	sigemptyset(&sa.sa_mask);
	sa.sa_flags = SA_RESTART; /* require BSD signal semantics */
	sa.sa_handler = sighandler;
	if (sigaction(SIGWINCH, &sa, NULL) == -1)
		err(1, "sigaction: SIGWINCH");

	needcleanup = 1;
}

/* pipe item to a program, if `wantoutput` is set then cleanup and restore the
   terminal attribute settings, if not set then don't do that and also ignore
   stdout and stderr. */
void
pipeitem(const char *cmd, struct item *item, int wantoutput)
{
	FILE *fp;
	int i, pid, wpid;

	if (wantoutput)
		cleanup();
	switch ((pid = fork())) {
	case -1:
		err(1, "fork");
		return;
	case 0:
		if (!wantoutput) {
			dup2(devnullfd, 1);
			dup2(devnullfd, 2);
		}

		errno = 0;
		if (!(fp = popen(cmd, "w"))) {
			fputs("popen: ", stderr);
			perror(NULL);
			_exit(1);
		}
		for (i = 0; i < FieldLast; i++) {
			if (i)
				fputc('\t', fp);
			fputs(item->fields[i], fp);
		}
		fputc('\n', fp);
		_exit(pclose(fp));
		break;
	default:
		while ((wpid = wait(NULL)) >= 0 && wpid != pid)
			;
	}

	if (wantoutput) {
		updatesidebar(onlynew);
		updatetitle();
		init();
	}
}

void
plumb(const char *cmd, char *url)
{
	switch (fork()) {
	case -1:
		err(1, "fork");
		return;
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
	if (pos >= p->nrows)
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
	putp(tparm(cursor_address, y, p->x, 0, 0, 0, 0, 0, 0, 0));

	r = 0;
	if (pos == p->pos) {
		putp(tparm(enter_standout_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));
		if (!p->focused)
			putp(tparm(enter_dim_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));
		r = 1;
	} else if (p->nrows && pos < p->nrows && row && row->bold) {
		putp(tparm(enter_bold_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));
		r = 1;
	}
	if (row)
		printpad(pane_row_text(p, row), p->width);
	else
		printf("%-*.*s", p->width, p->width, "");
	if (r)
		putp("\x1b[0m");
}

void
pane_setpos(struct pane *p, off_t pos)
{
	off_t prev;

	if (pos == p->pos)
		return; /* no change */
	if (!p->nrows)
		return; /* invalid */
	if (pos < 0)
		pos = 0; /* clamp */
	if (pos >= p->nrows)
		pos = p->nrows - 1; /* clamp */

	/* is on different screen ? */
	if (((p->pos - (p->pos % p->height)) / p->height) !=
	    ((pos - (pos % p->height)) / p->height)) {
		p->pos = pos;
		// TODO: dirty region handling? or setting dirty per row?
		p->dirty = 1;
		pane_draw(p);
	} else {
		prev = p->pos;
		p->pos = pos;
		// TODO: dirty region handling? or setting dirty per row?
		pane_row_draw(p, prev); /* draw previous row again */
		pane_row_draw(p, p->pos); /* draw new highlighted row */
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
	pane_setpos(p, p->nrows);
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
	if (n < 0)
		pane_setpos(p, p->pos + n);
	else if (n > 0)
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

	if (!s->focused)
		putp(tparm(enter_dim_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));
	for (y = 0; y < s->size; y++) {
		putp(tparm(cursor_address, s->y + y, s->x, 0, 0, 0, 0, 0, 0, 0));
		if (y >= s->tickpos && y < s->tickpos + s->ticksize) {
			putp(tparm(enter_standout_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));
			fputs(" ", stdout);
			putp(tparm(exit_standout_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));
		} else {
			fputs("\xe2\x94\x82", stdout); /* symbol: "light vertical" */
		}
	}
	if (!s->focused)
		putp("\x1b[0m");
	s->dirty = 0;
}

char *
uiprompt(int x, int y, char *fmt, ...)
{
	va_list ap;
	char *input = NULL;
	size_t n;
	ssize_t r;
	char buf[32];
	struct termios tset;

	va_start(ap, fmt);
	if (vsnprintf(buf, sizeof(buf), fmt, ap) >= sizeof(buf))
		buf[sizeof(buf) - 1] = '\0';
	va_end(ap);

	tcgetattr(ttyfd, &tset);
	tset.c_lflag |= (ECHO|ICANON);
	tcsetattr(ttyfd, TCSANOW, &tset);

	putp(tparm(save_cursor, 0, 0, 0, 0, 0, 0, 0, 0, 0));
	putp(tparm(cursor_address, y, x, 0, 0, 0, 0, 0, 0, 0));
	putp(tparm(enter_standout_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));
	fputs(buf, stdout);
	putp(tparm(exit_standout_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));

	putp(tparm(clr_eol, 0, 0, 0, 0, 0, 0, 0, 0, 0));
	putp(tparm(cursor_visible, 0, 0, 0, 0, 0, 0, 0, 0, 0));
	putp(tparm(cursor_address, y, x + colw(buf), 0, 0, 0, 0, 0, 0, 0));
	fflush(stdout);

	n = 0;
	r = getline(&input, &n, stdin);

	putp(tparm(cursor_invisible, 0, 0, 0, 0, 0, 0, 0, 0, 0));
	tcsetattr(ttyfd, TCSANOW, &tcur); /* restore */
	putp(tparm(restore_cursor, 0, 0, 0, 0, 0, 0, 0, 0, 0));

	fflush(stdout);

	if (r < 0) {
		clearerr(stdin);
		free(input);
		input = NULL;
	} else if (input[r - 1] == '\n') {
		input[--r] = '\0';
	}

	return input;
}

void
statusbar_draw(struct statusbar *s)
{
	if (s->hidden || !s->dirty)
		return;
	putp(tparm(cursor_address, s->y, s->x, 0, 0, 0, 0, 0, 0, 0));
	putp(tparm(enter_standout_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));
	printpad(s->text, s->width);
	putp(tparm(exit_standout_mode, 0, 0, 0, 0, 0, 0, 0, 0, 0));
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
	struct tm tm;
	time_t parsedtime;

	parseline(line, fields);

	parsedtime = 0;
	if (strtotime(fields[FieldUnixTimestamp], &parsedtime))
		return -1;
	if (!localtime_r(&parsedtime, &tm))
		return -1;

	item->line = line;
	item->isnew = (parsedtime >= comparetime);
	item->timestamp = parsedtime;
	memcpy(&(item->tm), &tm, sizeof(tm));
	memcpy(item->fields, fields, sizeof(fields));

	return 0;
}

int
feed_getitems(struct feed *f, FILE *fp, struct item **items, size_t *nitems)
{
	struct item *item;
	char *dupline, *line = NULL;
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
			if (cap == 0)
				cap = 16;
			else
				cap *= 2;
			*items = erealloc(*items, cap * sizeof(struct item));
		}
		if ((linelen = getline(&line, &linesize, fp)) > 0) {
			item = (*items) + i;

			item->offset = offset;
			offset += linelen;

			if (line[linelen - 1] == '\n')
				line[--linelen] = '\0';

			if (lazyload && f->path) {
				if (linetoitem(line, item) == -1) {
					i--;
					continue;
				}
				/* data is ignored here, will be lazy-loaded later. */
				item->line = NULL;
				memset(item->fields, 0, sizeof(item->fields));
			} else {
				dupline = estrdup(line);
				if (linetoitem(dupline, item) == -1) {
					i--;
					free(dupline);
					continue;
				}
			}

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
feed_load(struct feed *f, FILE *fp)
{
	static struct item *items = NULL;
	static size_t nitems = 0;
	struct pane *p;
	struct row *row;
	size_t i;

	for (i = 0; i < nitems; i++)
		free(items[i].line);
	free(items);
	items = NULL;
	nitems = 0;

	p = &panes[PaneItems];
	free(p->rows);
	p->rows = NULL;
	p->nrows = 0;

	if (feed_getitems(f, fp, &items, &nitems) == -1)
		err(1, "%s: %s", __func__, f->path);

	f->totalnew = 0;
	f->total = nitems;
	for (i = 0; i < nitems; i++)
		f->totalnew += items[i].isnew;

	p->pos = 0;
	p->nrows = nitems;
	p->rows = ecalloc(sizeof(p->rows[0]), nitems + 1);
	for (i = 0; i < nitems; i++) {
		row = &(p->rows[i]);
		row->text = ""; /* custom formatter */
		row->bold = items[i].isnew;
		row->data = &items[i];
	}
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
	struct tm *tm;
	time_t parsedtime;

	while ((linelen = getline(&line, &linesize, fp)) > 0) {
		if (line[linelen - 1] == '\n')
			line[--linelen] = '\0';
		parseline(line, fields);

		parsedtime = 0;
		if (strtotime(fields[FieldUnixTimestamp], &parsedtime))
			continue;
		if (!(tm = localtime(&parsedtime)))
			continue; /* ignore item */

		f->totalnew += (parsedtime >= comparetime);
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
		f->totalnew = f->total = 0;

		if (f->path) {
			if (f->fp) {
				if (fseek(f->fp, 0, SEEK_SET))
					err(1, "fseek: %s", f->path);
			} else {
				if (!(f->fp = fopen(f->path, "rb")))
					err(1, "fopen: %s", f->path);
			}
		}

		/* load first items, because of first selection or stdin. */
		if (i == 0)
			feed_load(f, f->fp);
		else
			feed_count(f, f->fp);

		if (f->path && f->fp) {
			fclose(f->fp);
			f->fp = NULL;
		}
	}
}

void
updatesidebar(int onlynew)
{
	struct pane *p;
	struct row *row;
	struct feed *feed;
	size_t i;
	int len, width;

	p = &panes[PaneFeeds];

	if (!p->rows)
		p->rows = ecalloc(sizeof(p->rows[0]), nfeeds + 1);

	p->nrows = 0;
	p->width = 0;
	width = 0;
	for (i = 0; i < nfeeds; i++) {
		feed = &feeds[i];

		row = &(p->rows[p->nrows]);
		row->text = ""; /* custom formatter is used */
		row->bold = (feed->totalnew > 0);
		row->data = feed;

		len = colw(pane_row_text(p, row));
		if (len > width)
			width = len;

		if (onlynew && feed->totalnew == 0)
			continue;

		p->nrows++;
	}
	p->width = width;
	p->dirty = 1;
}

void
sighandler(int signo)
{
	if (signo == SIGWINCH) {
		getwinsize();
		updategeom();
		draw();
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
		putp(tparm(clear_screen, 0, 0, 0, 0, 0, 0, 0, 0, 0));
		win.dirty = 0;
	}

	/* if item selection text changed, update the status text */
	if (panes[PaneItems].nrows &&
	    (row = pane_row_get(&panes[PaneItems], panes[PaneItems].pos))) {
		item = (struct item *)row->data;
		statusbar_update(&statusbar, item->fields[FieldLink]);
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
	int changedpane, pos;

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

		switch (button) {
		case 0: /* left-click */
			if (!p->nrows || pos >= p->nrows)
				break;
			if (i == PaneFeeds) {
				pane_setpos(p, pos);
				row = pane_row_get(p, pos);
				f = (struct feed *)row->data;
				feeds_set(f);
				feed_load(f, f->fp);
				/* redraw row: counts could be changed */
				pane_row_draw(p, pos);
				updatetitle();
			} else if (i == PaneItems) {
				/* clicking the same highlighted row */
				if (p->pos == pos && !changedpane) {
					row = pane_row_get(&panes[PaneItems], pos);
					item = (struct item *)row->data;
					plumb(plumber, item->fields[FieldLink]);
				} else {
					pane_setpos(p, pos);
				}
			}
			break;
		case 2: /* right-click */
			if (!p->nrows || pos >= p->nrows)
				break;
			if (i == PaneItems) {
				pane_setpos(p, pos);
				p = &panes[PaneItems];
				row = pane_row_get(p, p->pos);
				item = (struct item *)row->data;
				pipeitem(piper, item, 1);
			}
			break;
		case 3: /* scroll up */
		case 4: /* scroll down */
			pane_scrollpage(p, button == 3 ? -1 : +1);
			break;
		}
		draw();
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
	char *dupline, *line = NULL;
	size_t linesize = 0;
	ssize_t linelen;

	itemrow = p->rows + pos;
	item = (struct item *)itemrow->data;

	f = curfeed;
	if (f && f->path && !item->line) {
		if (fseek(f->fp, item->offset, SEEK_SET))
			err(1, "fseek: %s", f->path);
		linelen = getline(&line, &linesize, f->fp);

		if (linelen <= 0)
			return NULL;

		if (line[linelen - 1] == '\n')
			line[--linelen] = '\0';

		dupline = estrdup(line);
		if (linetoitem(dupline, item) == -1) {
			free(dupline);
			return NULL;
		}
		free(line);

		itemrow->data = item;
	}
	return itemrow;
}

/* custom formatter for item row */
char *
item_row_format(struct pane *p, struct row *row)
{
	struct item *item;
	static char text[1024];

	item = (struct item *)row->data;

	snprintf(text, sizeof(text), "%c %04d-%02d-%02d %02d:%02d %s",
	         item->fields[FieldEnclosure][0] ? '@' : ' ',
	         item->tm.tm_year + 1900, item->tm.tm_mon + 1, item->tm.tm_mday,
	         item->tm.tm_hour, item->tm.tm_min, item->fields[FieldTitle]);

	return text;
}

int
readch(void)
{
	unsigned char b;
	ssize_t n;

	n = read(ttyfd, &b, 1);
	if (n < 0)
		return EOF;
	else if (n == -1)
		err(1, "read");

	return (int)b;
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
	int ch, button, x, y, release; /* mouse button event */
	off_t off;

	setlocale(LC_CTYPE, "");

	if ((tmp = getenv("SFEED_PLUMBER")))
		plumber = tmp;
	if ((tmp = getenv("SFEED_PIPER")))
		piper = tmp;

	feeds = ecalloc(argc, sizeof(struct feed));
	if (argc == 1) {
		nfeeds = 1;
		f = &feeds[0];
		f->name = "stdin";
		if (!(f->fp = fdopen(ttyfd, "rb")))
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
	feeds_set(NULL);
	feeds_load(feeds, nfeeds);
	feeds_set(&feeds[0]);

	if (!isatty(ttyfd)) {
		close(ttyfd);
		if ((ttyfd = open("/dev/tty", O_RDONLY)) == -1)
			err(1, "open: /dev/tty");
		if (dup2(ttyfd, 0) == -1)
			err(1, "dup2: /dev/tty");
	}
	if (argc == 1)
		feeds[0].fp = NULL;

	panes[PaneFeeds].row_format = feed_row_format;
	panes[PaneFeeds].row_match = feed_row_match;
	panes[PaneItems].row_format = item_row_format;
	panes[PaneItems].row_get = item_row_get;

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

	atexit(cleanup);

	draw();

	while ((ch = readch()) != EOF) {
		switch (ch) {
		case '\x1b':
			ch = readch();
			if (ch != '[' && ch != 'O')
				continue; /* unhandled */
			switch ((ch = readch())) {
			case EOF: goto end;
			case 'M': /* reported mouse event */
				if ((ch = readch()) == EOF)
					goto end;
				/* button numbers (0 - 2) encoded in lowest 2 bits
				   release does not indicate which button (so set to 0). */
				ch -= 32;

				/* extended buttons like scrollwheels */
				release = 0;
				if (ch >= 64) {
					button = ((ch - 64) & 3) + 3;
				} else {
					button = ch & 3;
					if (button == 3) {
						button = -1;
						release = 1;
					}
				}
				/* X10 mouse-encoding */
				if ((x = readch()) == EOF)
					goto end;
				if ((y = readch()) == EOF)
					goto end;
				mousereport(button, release, x - 33, y - 33);
				break;
			case 'A': goto keyup;    /* arrow up */
			case 'B': goto keydown;  /* arrow down */
			case 'C': goto keyright; /* arrow left */
			case 'D': goto keyleft;  /* arrow right */
			case 'F': goto endpos;   /* end */
			case 'H': goto startpos; /* home */
			case '4': /* end */
				if ((ch = readch()) == '~')
					goto endpos;
				continue;
			case '5': /* page up */
				if ((ch = readch()) == '~')
					goto prevpage;
				continue;
			case '6': /* page down */
				if ((ch = readch()) == '~')
					goto nextpage;
				continue;
			}
			continue;
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
				                  "Search (%s): ", tmp);
				alldirty();
				draw();
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
		case 12: /* ^L */
		case 'r': /* update window dimensions and redraw */
			alldirty();
			break;
		case 'R': /* reload all files */
			if (nfeeds == 1 && !feeds[0].path)
				break;
			feeds_set(NULL);
			feeds_load(feeds, nfeeds);
			feeds_set(&feeds[0]);
			panes[PaneFeeds].pos = 0;
			updatesidebar(onlynew);
			updategeom();
			updatetitle();
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
			fflush(stdout);
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
				feed_load(f, f->fp);
				/* redraw row: counts could be changed */
				pane_row_draw(p, p->pos);
				updatetitle();
			} else if (selpane == PaneItems && panes[PaneItems].nrows) {
				p = &panes[PaneItems];
				row = pane_row_get(p, p->pos);
				item = (struct item *)row->data;
				plumb(plumber, item->fields[FieldLink]);
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
				default:  pipeitem(piper, item, 1); break;
				}
			}
			break;
		case 4: /* EOT */
		case 'q': goto end;
		}
		draw();
	}
end:
	return 0;
}
