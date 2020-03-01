#include "all.h"

#define DBG(l) l&1 ? "" : "~", l/2

typedef struct Var Var;
typedef struct Lit Lit;

struct Var {
	uchr trl : 1; /* 1 iff in the trail */
	uchr set : 1; /* 1 iff the variable is currently assigned */
	uchr val : 1; /* assigned truth value */
	Var *nxt, *prv; /* unassigned list */
};

struct Lit {
	uint *cls; /* the clauses in which this literal appears */
	uint ncls;
};

/* invariants:
 * - the first literal of a clause is unassigned or true
 * - when the clause is not sat, its first literal is unassigned
 * - if the first literal is assigned, it's assigned to 1 and
 *   the clause is sat
 */

Cls *cls;
uint ncls;

Lit *lit;
uint nlit; /* 2*nvar */

Var una; /* doubly linked unassigned list head */

Var *var;
uint nvar;

uint *trail;
uint level;  /* if level>0; trail[level-1] is the last set literal */

/* trail structure:
 *
 *  | ... var | val | choice |
 * 31         2     1        0
 *
 * - var: the variable number
 * - val: the truth value assigned to var
 * - choice: 1 if choosen, 0 if deduced by unit propagation
 */

#define Choose(lit) (2*(lit) + 1)
#define Deduce(lit) (2*(lit))

#define IsChoice(t) ((t) & 1)
#define GetLit(t)   ((t) >> 1)

#define O ++*mems

int
idpll(uint *mems)
{
	uint *l, *lend;
	uint v, n, x, y;
	uint *c, *cend;
	Lit *pl;
	Cls *pc;

	level = 0;
	for (n=0; n<nvar; n++) {
		var[n].trl = 0;
		var[n].set = 0;
	}
idpll:
	O;
	/* pick a variable to assign */
	if (level == nvar) {
		assert(una.nxt == &una && una.prv == &una);
		return 0;
	}
	v = una.nxt - var;
	n = level++;
	var[v].trl = 1;
	if (lit[Pos(v)].ncls == 0)
		/* no clause contains the positive,
		 * assign the variable to false */
		trail[n] = Deduce(Neg(v));
	else if (lit[Neg(v)].ncls == 0)
		trail[n] = Deduce(Pos(v));
	else
		/* assign to true by default */
		trail[n] = Choose(Pos(v));

	/* unit propagate the choice */
unit:
	for (; O,n<level; n++) {
		x = GetLit(trail[n]);
		assert(var[Var(x)].trl);
#ifndef NDEBUG
		printf("unit prop (lit: %s%u (%s))\n",
			DBG(x), IsChoice(trail[n]) ? "chosen" : "deduced");
#endif
		/* update the watch literal of
		 * all the clauses containing
		 * the negation of the chosen
		 * literal */
		x = Flip(x);
		pl = &lit[x];
		c = pl->cls;
		cend = &c[pl->ncls];
		for (; O,c<cend; c++) {
			if (0) printf("looking at clause %u\n", *c);
			pc = &cls[*c];
			l = pc->lit;
			lend = &l[pc->nlit];
			if (*l != x) {
				/* the watch is good; go find
				 * if it's the only literal
				 * left */
				y = *l;
				goto search;
			}
			/* find another watch */
			for (; O,1;) {
				if (++l == lend)
					/* conflict! */
					goto conflict;
				y = *l;
				v = Var(y);
				if (!var[v].set)
					break;
				assert(var[v].val == !(y&1));
			}
			pc->lit[0] = y;
			*l = x;
			/* find out if we found the only
			 * unassigned literal of the clause;
			 * if so, deduce its truth */
		search:
			if (var[Var(y)].trl)
				/* the variable is already in the
				 * trail, so we should not add it
				 * anyway */
				continue;
			for (; O,1;) {
				if (++l == lend) {
					var[Var(y)].trl = 1;
					trail[level++] = Deduce(y);
					break;
				}
				v = Var(*l);
				if (!var[v].set && *l != x)
					break;
				assert(*l == x || var[v].val == !(*l&1));
			}
		}
		/* mark all clauses containing x
		 * as sat by setting their watch
		 * literal to x */
		x = Flip(x);
		pl = &lit[x];
		c = pl->cls;
		cend = &c[pl->ncls];
		for (; O,c<cend; c++) {
			pc = &cls[*c];
			l = pc->lit;
			lend = &l[pc->nlit];
			if (*l == x)
				/* already good */
				continue;
			if (var[Var(*l)].set) {
				/* already good */
				assert(var[Var(*l)].val == (*l&1));
				continue;
			}
			for (; O,*l!=x; l++)
				;
			*l = pc->lit[0];
			pc->lit[0] = x;
		}
		/* finally, mark the variable as set! */
		v = Var(x);
		var[v].set = 1;
		var[v].prv->nxt = var[v].nxt;
		var[v].nxt->prv = var[v].prv;
		var[v].val = (x&1);
	}
	goto idpll;

conflict:
	for (; O,1;) {
		if (level == 0) {
			return 1;
		}
		n = trail[--level];
		v = Var(GetLit(n));
		var[v].trl = 0;
		var[v].set = 0;
		var[v].prv->nxt = &var[v]; /* dance! */
		var[v].nxt->prv = &var[v];
		if (IsChoice(n)) {
			/* revert the choice */
			n = level++;
			var[v].trl = 1;
			trail[n] = Deduce(Neg(v));
			goto unit;
		}
	}
}

int
uintcmp(const void *a, const void *b)
{
	return (*(uint *)a > *(uint *)b) - (*(uint *)a < *(uint *)b);
}

void
initialize(uint *prm)
{
	Var *cur, *prv;
	uint n;

	/* initialize and link variables */
	prv = &una;
	prv->nxt = prv;
	prv->prv = prv;
	for (n=0; n<nvar; n++) {
		cur = &var[prm[n]];
		cur->trl = 0;
		cur->set = 0;
		cur->nxt = prv->nxt;
		cur->prv = prv;
		cur->prv->nxt = cur;
		cur->nxt->prv = cur;
	}

	/* sort clauses */
	for (n=0; n<ncls; n++)
		qsort(cls[n].lit, cls[n].nlit, sizeof cls[n].lit[0], uintcmp);

	level = 0;
}

int
main(int ac, char *av[])
{
	uint *prm;
	uint mems;
	uint *l, *lend;
	uint r, n, t;
	Lit *pl;
	int uns;

	/* 1. read in dimacs */
	/* todo: make sure literals appear once per clause */
	if (!indimacs(stdin, &cls, &ncls, &nvar))
		die("could not parse dimacs");
	printf("input %u clauses and %u variables\n", ncls, nvar);

	/* 2. preprocess clauses */
	/* todo: filter clauses already known to be true
	 * and return unsat if a clause is empty */

	/* 3. populate data structures */
	nlit = 2*nvar;
	lit = calloc(nlit, sizeof *lit);
	if (!lit)
		die("out of mem");
	for (n=0; n<nlit; n++)
		lit[n].cls = vnew(4, sizeof *lit[n].cls);
	for (n=0; n<ncls; n++) {
		l = cls[n].lit;
		lend = &l[cls[n].nlit];
		for (; l<lend; l++) {
			pl = &lit[*l];
			vgrow(&pl->cls, pl->ncls+1);
			pl->cls[pl->ncls++] = n;
		}
	}
	trail = calloc(nvar, sizeof *trail);
	var = calloc(nvar, sizeof *var);
	
	prm = calloc(nvar, sizeof *prm);
	for (n=0; n<nvar; n++)
		prm[n] = n;

	/* if 'x' is passed, exhaust all variable orderings
	 * and report the mems for each */
	if (ac>1 && strcmp(av[1], "x")==0) {
		do {
			initialize(prm);
			mems = 0;
			uns = idpll(&mems);
			printf("%u, %d\n", mems, !uns);
		} while (nextperm(prm, nvar));

		return 0;
	}

	/* else generate a random-ish permutation of the vars */
	srand(42);
#ifndef NDEBUG
	if (0) {
#else
	for (n=0; n<nvar; n++) {
#endif
		r = rand() % (nvar - n);
		t = prm[r];
		prm[r] = prm[n];
		prm[n] = t;
	}


	/* 4. dpll backtracking procedure */
	initialize(prm);
	mems = 0;
	uns = idpll(&mems);
	puts(uns ? "unsat" : "sat");
	return uns;
}
