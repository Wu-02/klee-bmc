#include "size_t.h"

extern void klee_make_symbolic(void *, size_t, const char *);

unsigned short __VERIFIER_nondet_u16(void)
{
	unsigned short x;
	klee_make_symbolic(&x, sizeof(x), "nondet-ushort");
	return x;
}
