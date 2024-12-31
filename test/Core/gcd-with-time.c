// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
//#include <stdio.h>

int gcd(int a, int b)
{
  int __time = 1;
  while(b>0)
  {
     __time += 7;
    if (a>b)
    {
      __time += 13;
      a=a-b;
    }
    else
    {
      __time += 17;
      b=b-a;
    }
  }
  __time += 21;
  __VERIFIER_assert(__time<=70);
  return a;
}

int __VERIFIER_nondet_int();

int main()
{
  gcd(__VERIFIER_nondet_int(),__VERIFIER_nondet_int());
//  int a=15, b=4;
//  gcd(a,b);
//  printf("mdc: %d\n", gcd(a,b));
  return 0;
}
