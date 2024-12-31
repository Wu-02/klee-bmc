#include "size_t.h"

extern void klee_make_symbolic(void *, size_t, const char *);

#ifdef __x86_64__
unsigned __int128 __VERIFIER_nondet_uint128(void) {
  unsigned __int128 x;
  klee_make_symbolic(&x, sizeof(x), "unsigned __int128");
  return x;
}
#endif