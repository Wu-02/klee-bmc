#include "size_t.h"

extern void klee_make_symbolic(void *, size_t, const char *);

unsigned char __VERIFIER_nondet_u8(void)
{
	unsigned char x;
	klee_make_symbolic(&x, sizeof(x), "nondet-uchar");
	return x;
}
