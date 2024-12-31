// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
int __VERIFIER_nondet_int();
_Bool __VERIFIER_nondet_bool();

main()
{
  int x, y, d;

  while (x>0 && y>0 && d>0)
  {
    _Bool c = __VERIFIER_nondet_bool();
    if(c) {
      x=x-1;
      d=__VERIFIER_nondet_int();
    } else {
      x = __VERIFIER_nondet_int();
      y = y- 1;
      d=d-1;
    }
  }
  __VERIFIER_assert(0);
}


