// Stripped-down primitive printf-style formatting routines,
// used in common by printf, sprintf, fprintf, etc.
// This code is also used by both the kernel and user programs.

#include <inc/types.h>
#include <inc/stdio.h>
#include <inc/string.h>
#include <inc/stdarg.h>
#include <inc/error.h>

#define CLR(ch) ((ch) | color)
#define FGCLR(c) (color = ((color & (~0x0F00)) | (c << 8)))
#define BGCLR(c) (color = ((color & (~0xF000)) | (c << 12)))
static int color = 0x0700;

/*
 * Space or zero padding and a field width are supported for the numeric
 * formats only.
 *
 * The special format %e takes an integer error code
 * and prints a string describing the error.
 * The integer may be positive or negative,
 * so that -E_NO_MEM and E_NO_MEM are equivalent.
 */

static const char * const error_string[MAXERROR + 1] =
{
	NULL,
	"unspecified error",
	"bad environment",
	"invalid parameter",
	"out of memory",
	"out of environments",
	"segmentation fault",
	"env is not recving",
	"unexpected end of file",
	"not a valid executable",
	"no free space on disk",
	"too many files are open",
	"file or block not found",
	"invalid path",
	"file already exists",
	"operation not supported",
	"try again",
	"block was not locked",
	"file too big",
	"is directory",
	"I/O error",
};

/*
 * Print a number (base <= 16) in reverse order,
 * using specified putch function and associated pointer putdat.
 */
static void
printnum(void (*putch)(int, void*), void *putdat,
	 unsigned long long num, unsigned base, int width, int padc)
{
	// first recursively print all preceding (more significant) digits
	if (num >= base) {
		printnum(putch, putdat, num / base, base, width - 1, padc);
	} else {
		// print any needed pad characters before first digit
		while (--width > 0)
			putch(CLR(padc), putdat);
	}

	// then print this (the least significant) digit
	putch(CLR("0123456789abcdef"[num % base]), putdat);
}

// Get an unsigned int of various possible sizes from a varargs list,
// depending on the lflag parameter.
static unsigned long long
getuint(va_list *ap, int lflag)
{
	if (lflag >= 2)
		return va_arg(*ap, unsigned long long);
	else if (lflag)
		return va_arg(*ap, unsigned long);
	else
		return va_arg(*ap, unsigned int);
}

// Same as getuint but signed - can't use getuint
// because of sign extension
static long long
getint(va_list *ap, int lflag)
{
	if (lflag >= 2)
		return va_arg(*ap, long long);
	else if (lflag)
		return va_arg(*ap, long);
	else
		return va_arg(*ap, int);
}


// Main function to format and print a string.
void printfmt(void (*putch)(int, void*), void *putdat, const char *fmt, ...);

void set_sgr(unsigned int *args, unsigned int argc) {
	for (unsigned int i=0; i<argc; i++) {
		switch (args[i]) {
			case 30: FGCLR(0); continue; // Black
			case 31: FGCLR(4); continue; // Red
			case 32: FGCLR(2); continue; // Green
			case 33: FGCLR(6); continue; // Yellow/brown
			case 34: FGCLR(1); continue; // Blue
			case 35: FGCLR(5); continue; // Magenta
			case 36: FGCLR(3); continue; // Cyan
			case 37: FGCLR(7); continue; // White
			case 40: BGCLR(0); continue; // Black
			case 41: BGCLR(4); continue; // Red
			case 42: BGCLR(2); continue; // Green
			case 43: BGCLR(6); continue; // Yellow/brown
			case 44: BGCLR(1); continue; // Blue
			case 45: BGCLR(5); continue; // Magenta
			case 46: BGCLR(3); continue; // Cyan
			case 47: BGCLR(8); continue; // White
			case 0:
				color=0x0700;
			default: continue;
		}
	}
}

int ansi_sequence(const char *seq) {
	int taken = 0;
	unsigned int aindex = 0;
	unsigned int args[] = { 0, 0 }; 
	unsigned char ch;
	while ((ch = *(unsigned char *) seq++) != 0) {
		taken++;
		switch (ch) {
			case '0':
				args[aindex] *= 10;
				continue;
			case '1':
				args[aindex] *= 10;
				args[aindex] += 1;
				continue;
			case '2':
				args[aindex] *= 10;
				args[aindex] += 2;
				continue;
			case '3':
				args[aindex] *= 10;
                                args[aindex] += 3;
                                continue;
			case '4':
				args[aindex] *= 10;
                                args[aindex] += 4;
                                continue;
			case '5':
				args[aindex] *= 10;
                                args[aindex] += 5;
                                continue;
			case '6':
				args[aindex] *= 10;
                                args[aindex] += 6;
                                continue;
			case '7':
				args[aindex] *= 10;
                                args[aindex] += 7;
                                continue;
			case '8':
				args[aindex] *= 10;
                                args[aindex] += 8;
                                continue;
			case '9':
				args[aindex] *= 10;
                                args[aindex] += 9;
                                continue;
			case 'm':
				set_sgr(args,aindex+1);
				return taken;
			case ';':
				aindex++;
				if (aindex==2) return -1;
				continue;
			default:
				return -1;
		}		
	}
	return -1;
}

void
vprintfmt(void (*putch)(int, void*), void *putdat, const char *fmt, va_list ap)
{
	register const char *p;
	register int ch, err;
	unsigned long long num;
	int base, lflag, width, precision, altflag;
	char padc;

	while (1) {
		while ((ch = *(unsigned char *) fmt++) != '%') {
			if (ch == '\0')
				return;
			if (ch == '\033') {
				ch = *(unsigned char *) fmt++;
				if (ch == '[') {
					int taken = ansi_sequence(fmt);
					if (taken < 0) {
						putch('\033',putdat);
						fmt--;
					} else {
						fmt += taken;
					}
				} else {
					putch(CLR('\033'),putdat);
					fmt--;
				}
			} else {
				putch(CLR(ch), putdat);
			}
		}

		// Process a %-escape sequence
		padc = ' ';
		width = -1;
		precision = -1;
		lflag = 0;
		altflag = 0;
	reswitch:
		switch (ch = *(unsigned char *) fmt++) {

		// flag to pad on the right
		case '-':
			padc = '-';
			goto reswitch;

		// flag to pad with 0's instead of spaces
		case '0':
			padc = '0';
			goto reswitch;

		// width field
		case '1':
		case '2':
		case '3':
		case '4':
		case '5':
		case '6':
		case '7':
		case '8':
		case '9':
			for (precision = 0; ; ++fmt) {
				precision = precision * 10 + ch - '0';
				ch = *fmt;
				if (ch < '0' || ch > '9')
					break;
			}
			goto process_precision;

		case '*':
			precision = va_arg(ap, int);
			goto process_precision;

		case '.':
			if (width < 0)
				width = 0;
			goto reswitch;

		case '#':
			altflag = 1;
			goto reswitch;

		process_precision:
			if (width < 0)
				width = precision, precision = -1;
			goto reswitch;

		// long flag (doubled for long long)
		case 'l':
			lflag++;
			goto reswitch;

		// character
		case 'c':
			putch(CLR(va_arg(ap, int)), putdat);
			break;

		// error message
		case 'e':
			err = va_arg(ap, int);
			if (err < 0)
				err = -err;
			if (err > MAXERROR || (p = error_string[err]) == NULL)
				printfmt(putch, putdat, "error %d", err);
			else
				printfmt(putch, putdat, "%s", p);
			break;

		// string
		case 's':
			if ((p = va_arg(ap, char *)) == NULL)
				p = "(null)";
			if (width > 0 && padc != '-')
				for (width -= strnlen(p, precision); width > 0; width--)
					putch(CLR(padc), putdat);
			for (; (ch = *p++) != '\0' && (precision < 0 || --precision >= 0); width--)
				if (altflag && (ch < ' ' || ch > '~'))
					putch(CLR('?'), putdat);
				else
					putch(CLR(ch), putdat);
			for (; width > 0; width--)
				putch(CLR(' '), putdat);
			break;

		// (signed) decimal
		case 'd':
			num = getint(&ap, lflag);
			if ((long long) num < 0) {
				putch(CLR('-'), putdat);
				num = -(long long) num;
			}
			base = 10;
			goto number;

		// unsigned decimal
		case 'u':
			num = getuint(&ap, lflag);
			base = 10;
			goto number;

		// (unsigned) octal
		case 'o':
			// Replace this with your code.
			num = getuint(&ap, lflag);
			base = 8;
			goto number;

		// pointer
		case 'p':
			putch(CLR('0'), putdat);
			putch(CLR('x'), putdat);
			num = (unsigned long long)
				(uintptr_t) va_arg(ap, void *);
			base = 16;
			goto number;

		// (unsigned) hexadecimal
		case 'x':
			num = getuint(&ap, lflag);
			base = 16;
		number:
			printnum(putch, putdat, num, base, width, padc);
			break;

		// escaped '%' character
		case '%':
			putch(CLR(ch), putdat);
			break;

		// unrecognized escape sequence - just print it literally
		default:
			putch(CLR('%'), putdat);
			for (fmt--; fmt[-1] != '%'; fmt--)
				/* do nothing */;
			break;
		}
	}
}

void
printfmt(void (*putch)(int, void*), void *putdat, const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	vprintfmt(putch, putdat, fmt, ap);
	va_end(ap);
}

struct sprintbuf {
	char *buf;
	char *ebuf;
	int cnt;
};

static void
sprintputch(int ch, void *ptr)
{
	struct sprintbuf *b = (struct sprintbuf *) ptr;
	b->cnt++;
	if (b->buf < b->ebuf)
		*b->buf++ = ch;
}

int
vsnprintf(char *buf, int n, const char *fmt, va_list ap)
{
	struct sprintbuf b = {buf, buf+n-1, 0};

	if (buf == NULL || n < 1)
		return -E_INVAL;

	// print the string to the buffer
	vprintfmt(sprintputch, &b, fmt, ap);

	// null terminate the buffer
	*b.buf = '\0';

	return b.cnt;
}

int
snprintf(char *buf, int n, const char *fmt, ...)
{
	va_list ap;
	int rc;

	va_start(ap, fmt);
	rc = vsnprintf(buf, n, fmt, ap);
	va_end(ap);

	return rc;
}


