// RUN: %kleebmc --k-induction %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
int __VERIFIER_nondet_int();

int main() {
  int i, n=__VERIFIER_nondet_int(), sn=0;
  for(i=1; i<=n; i++)
    if (i<10)
      sn = sn + 2;
  __VERIFIER_assert(sn==n*2 || sn == 0);
}
