// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result true

void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "fabs.c", 5, __extension__ __PRETTY_FUNCTION__); })); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error();abort();} } return; }

int main(void)
{
  __VERIFIER_assert(fabs(+3.0) == +3.0);
  __VERIFIER_assert(fabs(-3.0) == +3.0);
  __VERIFIER_assert(fabs(-0.0) == -0.0);
  __VERIFIER_assert(fabs(-0.0) == +0.0);
  __VERIFIER_assert(fabs(-(__builtin_inff())) == (__builtin_inff()));
  __VERIFIER_assert((sizeof (fabs(-(__builtin_nanf ("")))) == sizeof (float) ? __isnanf (fabs(-(__builtin_nanf ("")))) : sizeof (fabs(-(__builtin_nanf ("")))) == sizeof (double) ? __isnan (fabs(-(__builtin_nanf ("")))) : __isnanl (fabs(-(__builtin_nanf (""))))));
}
