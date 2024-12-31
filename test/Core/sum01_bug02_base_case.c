// RUN: %kleebmc --k-induction   -Wno-error=implicit-function-declaration %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
#define a (2)
unsigned int __VERIFIER_nondet_uint();
int main() {
  int i, n=__VERIFIER_nondet_uint(), sn=0;
  for(i=1; i<=n; i++) {
    //if (i<10) //first case
    sn = sn + a; //second case OK
    if (i==4) sn=-10; //third case OK
  }
  //__VERIFIER_assume(i>n);
  __VERIFIER_assert(sn==n*a || sn == 0);
}
