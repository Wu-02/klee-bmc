// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result true

#include "assert.h"

int __VERIFIER_nondet_int();
void __VERIFIER_assume(int cond);

int main() {
  int i=0, x=0, y=0;
  int n=__VERIFIER_nondet_int();
  __VERIFIER_assume(n>0);
  for(i=0; 1; i++)
  {
    assert(x==0);
  }
  assert(x==0);
}

