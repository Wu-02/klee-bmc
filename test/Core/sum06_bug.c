// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
#define a 2
int __VERIFIER_nondet_int();
void __VERIFIER_assume(int cond);

int main()
{
  unsigned long long int i=1, sn=0;
  int n = __VERIFIER_nondet_int();

  __VERIFIER_assume(n < 1000 && n >= -1000);

  while ( i <= n ) {
    sn = sn + ((i%10==9)? 4 : a);
    i++;
  }

  __VERIFIER_assert(sn == n * a || sn == 0);
}
