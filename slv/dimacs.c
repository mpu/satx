#include <ctype.h>

#include "all.h"

static int
skipc(FILE *f)
{
	int c;

	do
		c = fgetc(f);
	while (c == '\n' || isspace(c));
	if (c != 'c') {
		ungetc(c, f);
		return 0;
	}
	do
		c = fgetc(f);
	while (c != '\n' && c != EOF);
	return 1;
}

int
indimacs(FILE *f, Cls **pcls, uint *pncls, uint *pnvar)
{
	Cls *cls, *cur, *end;
	uint nvar, ncls, nlit;
	int l;

	while (skipc(f))
		;
	if (fscanf(f, "p cnf %u %u ", &nvar, &ncls) != 2)
		return 0;
	cls = vnew(ncls, sizeof *cls);
	cur = cls;
	end = &cls[ncls];
	while (cur<end) {
		cur->lit = vnew(5, sizeof (uint));
		nlit = 0;
		for (;;) {
			if (fscanf(f, "%d ", &l) != 1)
				goto clean;
			vgrow(&cur->lit, nlit+1);
			if (l == 0)
				break;
			if (l < 0)
				cur->lit[nlit] = Neg(-l);
			else
				cur->lit[nlit] = Pos(l);
			nlit++;
		}
		cur->nlit = nlit;
		cur++;
	}
	*pcls = cls;
	*pncls = ncls;
	*pnvar = nvar;
	return 1;

clean:
	/* we don't free, since we're likely
	 * going to crash after that anyway */
	*pcls = 0;
	*pncls = 0;
	*pnvar = 0;
	return 0;
}
