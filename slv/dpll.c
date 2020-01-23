#include "all.h"

int main()
{
	Cls *cls;
	uint ncls, nvar;

	if (!indimacs(stdin, &cls, &ncls, &nvar))
		die("could not parse dimacs");
	printf("input %u clauses and %u variables\n", ncls, nvar);
	return 0;
}
