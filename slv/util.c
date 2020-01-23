#include "all.h"

void
die(char *msg)
{
	fputs("dying: ", stderr);
	fputs(msg, stderr);
	fputc('\n', stderr);
	exit(66);
}

#define MAGIC 0x4943554c

typedef struct Hdr Hdr;

struct Hdr {
	uint magic;
	uint esz;
	ulng cap;
} __attribute__((aligned(8)));

void *
vnew(ulng cap, size_t esz)
{
	Hdr *h;

	if (esz > 0xffffffff)
		die("vec too big");
	h = malloc(sizeof *h + (cap*esz));
	if (!h)
		die("out of mem");
	h->magic = MAGIC;
	h->esz = esz;
	h->cap = cap;
	return (void *)(h+1);
}

void
vgrow(void *pvec, ulng cap)
{
	Hdr *h;
	ulng cap0;

	h = (*(Hdr **)pvec) - 1;
	assert(h->magic == MAGIC);
	if (cap <= h->cap)
		return;
	cap0 = 2*h->cap + 1;
	if (cap < cap0)
		cap = cap0;
	h = realloc(h, sizeof *h + (cap*h->esz));
	if (!h)
		die("out of mem");
	h->cap = cap;
	*(void **)pvec = (void *)(h+1);
}

void
vfree(void *vec)
{
	Hdr *h;

	h = (Hdr *)vec - 1;
	assert(h->magic == MAGIC);
	h->magic = 0;
	free(h);
}
