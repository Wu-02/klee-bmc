// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
int __VERIFIER_nondet_int();
_Bool __VERIFIER_nondet_bool();

main()
{
  int x=__VERIFIER_nondet_int();
  int y=__VERIFIER_nondet_int();

  if (y>0)
  {
    while(x<100)
    {
      x=x+y;
     }
  }
  __VERIFIER_assert(0);
}

