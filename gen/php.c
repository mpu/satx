/* efficient code to generate
 * pigeon-hole-principle sat
 * instances
 */
#include <stdio.h>

#define Var(p,h) (1 + h + nh*(p))

int
main(int ac, char *av[])
{
	unsigned h, p1, p2, nh, np;

	if (ac < 3
	|| sscanf(av[1], "%u", &nh) != 1
	|| sscanf(av[2], "%u", &np) != 1) {
		puts("usage: ./php HOLES PIGEONS");
		return 1;
	}

	printf("p cnf %u %u\n", Var(np-1, nh-1), np + nh * np*(np-1)/2);
	/* each pigeon is in a hole */
	for (p1=0; p1<np; p1++) {
		for (h=0; h<nh; h++)
			printf("%u ", Var(p1, h));
		puts("0");
	}
	/* a hole has at most one pigeon */
	for (h=0; h<nh; h++) {
		for (p1=0; p1<np; p1++) {
			for (p2=p1+1; p2<np; p2++) {
				printf("-%u -%u 0\n", Var(p1, h), Var(p2, h));
			}
		}
	}
}
