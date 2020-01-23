#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

#define Pos(v) (2*(v) + 1)
#define Neg(v) (2*(v))
#define Flip(l) ((l) ^ 1)
#define Var(l) ((l) >> 1)

typedef unsigned char uchr;
typedef unsigned int uint;
typedef unsigned long long ulng;

typedef struct Cls Cls;

struct Cls {
	uint *lit;
	uint nlit;
};

/* utils.c */
void die(char *) __attribute__((noreturn));
void *vnew(ulng, size_t);
void vgrow(void *, ulng);
void vfree(void *);

/* dimacs.c */
int indimacs(FILE *, Cls **, uint *, uint *);
