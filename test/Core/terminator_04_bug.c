// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
int __VERIFIER_nondet_int();
_Bool __VERIFIER_nondet_bool();

main()
{
  int x=__VERIFIER_nondet_int();
  int y=__VERIFIER_nondet_int();

  while (x>0 && y>0)
  {
    _Bool c = __VERIFIER_nondet_bool();
    if(c)
      x=x-1;
    else {
      x = __VERIFIER_nondet_int();
      y = y- 1;
    }
  }
  __VERIFIER_assert(0);
}


