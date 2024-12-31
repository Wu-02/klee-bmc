// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result true

#include "assert.h"

int __VERIFIER_nondet_int();

int main() {
  int x=0;

  while(1)
  {
    assert(x==0);
  }

  assert(x==0);
}
