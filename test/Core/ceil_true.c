// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result true

#include <math.h>

extern void abort(void);
void __VERIFIER_assert(int cond);
void reach_error() { __VERIFIER_assert(0); }

int main(void)
{
  __VERIFIER_assert(ceil(2.4) == 3.0);
  __VERIFIER_assert(ceil(-2.4) == -2.0);

  double c = ceil(-0.0);
  __VERIFIER_assert((c == -0.0) && signbit(c));

  c = ceil(-INFINITY);
  __VERIFIER_assert(isinf(INFINITY) && signbit(c));
}
