#include "size_t.h"

extern void klee_make_symbolic(void *, size_t, const char *);

int __VERIFIER_nondet_int(void)
{
	int x;
	klee_make_symbolic(&x, sizeof(x), "nondet-int");
	return x;
}
