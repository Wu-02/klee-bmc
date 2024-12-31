// RUN: %kleebmc --k-induction %s | %FileCheck %s
// CHECK: Verification finished with result true

#include "assert.h"
int __VERIFIER_nondet_int();

int main()
{
  int x=__VERIFIER_nondet_int();
  int *p = &x;

  while(x<100) {
   (*p)++;
  }

  return 0;
}

