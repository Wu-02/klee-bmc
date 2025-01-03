#include "size_t.h"

extern void klee_make_symbolic(void *, size_t, const char *);

int __VERIFIER_nondet_size_t(void)
{
	size_t x;
	klee_make_symbolic(&x, sizeof(x), "nondet-size_t");
	return x;
}
