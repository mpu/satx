#include "all.h"

#define DBG(l) l&1 ? "" : "~", l/2

typedef struct Var Var;
typedef struct Lit Lit;

struct Var {
	uchr set : 1; /* 1 iff the variable is currently assigned */
	uchr val : 1; /* assigned truth value */
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

uint *prm; /* a permutation of variables */
uint next;

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

int main()
{
	uint *l, *lend;
	uint v, n, r, x, y, t;
	uint *c, *cend;
	Lit *pl;
	Cls *pc;

	/* 1. read in dimacs */
	if (!indimacs(stdin, &cls, &ncls, &nvar))
		die("could not parse dimacs");
	printf("input %u clauses and %u variables\n", ncls, nvar);

	/* FIX THIS SHIT */
	nvar++;

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

	/* generate a random-ish permutation of the vars */
	prm = calloc(nvar, sizeof *prm);
	for (n=0; n<nvar; n++)
		prm[n] = n;
	srand(42);
/* rnd: */
	for (n=0; 0 && n<nvar; n++) {
		r = rand() % (nvar - n);
		t = prm[r];
		prm[r] = prm[n];
		prm[n] = t;
	}

	/* 4. dpll backtracking procedure */
idpll:
	/* pick a variable to assign */
	if (level == nvar) {
		puts("sat");
		return 0;
	}
	do {
		v = prm[next];
		next = (next+1) % nvar;
	} while (var[v].set);
	var[v].set = 1;
	if (lit[Pos(v)].ncls == 0) {
		/* no clause contains the positive,
		 * assign the variable to false */
		var[v].val = 0;
		n = level++;
		trail[n] = Deduce(Neg(v));
	} else {
		/* assign to true by default */
		var[v].set = 1;
		var[v].val = 1;
		n = level++;
		trail[n] = Choose(Pos(v));
	}
	/* unit propagate the choice */

unit:
	for (; n<level; n++) {
		/* update the watch literal of
		 * all the clauses containing
		 * the negation of the chosen
		 * literal */
		x = GetLit(trail[n]);
		printf("unit prop (lit: %s%u (%s))\n",
			DBG(x), IsChoice(trail[n]) ? "chosen" : "deduced");
		x = Flip(x);
		pl = &lit[x];
		c = pl->cls;
		cend = &c[pl->ncls];
		for (; c<cend; c++) {
			pc = &cls[*c];
			l = pc->lit;
			lend = &l[pc->nlit];
			if (*l != x)
				/* the watch is good; go find
				 * if it's the only literal
				 * left if it is unassigned */
				goto search;
			/* find another watch */
			for (;;) {
				if (++l == lend)
					/* conflict! */
					goto conflict;
				y = *l;
				v = Var(y);
				if (y == Flip(x) || !var[v].set)
					break;
				assert(var[v].val == !(y&1));
			}
			pc->lit[0] = y;
			*l = x;
			/* find out if we found the only
			 * unassigned literal of the clause;
			 * if so, deduce its truth */
		search:
			if (var[Var(*l)].set) {
				/* if the literal is set, it must
				 * be true; and the clause is sat */
				assert(var[Var(*l)].val == (*l&1));
				continue;
			}
			for (;;) {
				if (++l == lend) {
					/* FIXME: invariant broken */
					trail[level++] = Choose(y);
					var[v].set = 1;
					var[v].val = (y&1);
					break;
				}
				if (!var[Var(*l)].set)
					break;
				assert(var[Var(*l)].val == !(*l&1));
			}
		}
		/* mark all clauses containing x
		 * as sat by setting their watch
		 * literal to x */
		x = Flip(x);
		pl = &lit[x];
		c = pl->cls;
		cend = &c[pl->ncls];
		for (; c<cend; c++) {
			pc = &cls[*c];
			l = pc->lit;
			lend = &l[pc->nlit];
			if (var[Var(*l)].set) {
				/* already marked sat */
				printf(" %s%u (%d)\n", DBG(*l), var[Var(*l)].val);
				assert(var[Var(*l)].val == (*l&1));
				continue;
			}
			for (; *l!=x; l++)
				;
			*l = pc->lit[0];
			pc->lit[0] = x;
		}
	}
	goto idpll;

conflict:
	for (;;) {
		if (level == 0) {
			puts("unsat");
			return 1;
		}
		n = trail[--level];
		v = Var(GetLit(n));
		assert(var[v].set);
		if (IsChoice(n)) {
			/* revert the choice */
			assert(var[v].val == 1);
			var[v].val = 0;
			n = level++;
			trail[n] = Deduce(Neg(v));
			goto unit;
		}
		var[v].set = 0;
	}

	return 0;
}
