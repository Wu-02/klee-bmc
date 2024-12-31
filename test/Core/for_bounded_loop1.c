// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);

int __VERIFIER_nondet_int();
void __VERIFIER_assume(int cond);

int main() {
  int i=0, x=0, y=0;
  int n=__VERIFIER_nondet_int();
  __VERIFIER_assume(n>0);
  for(i=0; i<n; i++)
  {
    x = x-y;
    __VERIFIER_assert(x==0);
    y = __VERIFIER_nondet_int();
    __VERIFIER_assume(y!=0);
    x = x+y;
    __VERIFIER_assert(x!=0);
  }
  //__VERIFIER_assume(i>=n);
  __VERIFIER_assert(x==0);
}

