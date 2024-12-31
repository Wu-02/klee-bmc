// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
unsigned int __VERIFIER_nondet_uint();

int main()
{
  unsigned int n = __VERIFIER_nondet_uint();
//  __VERIFIER_assume(n>0 && n<10000);
  unsigned int x=n, y=0;
//  __VERIFIER_assume(x==n);
  while(x>0)
  {
    x--;
    y++;
  }
  __VERIFIER_assert(y!=n);
//  __VERIFIER_assert(x==0);
}
