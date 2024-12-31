// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
int __VERIFIER_nondet_int();

main()
{
  int x=__VERIFIER_nondet_int();
  int *p = &x;

  while(x<100) {
   (*p)++;
  }
  __VERIFIER_assert(0);
  //  __VERIFIER_assert(array[0]>=menor);
}

