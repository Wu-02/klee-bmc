// RUN: %kleebmc --k-induction %s | %FileCheck %s
// CHECK: Verification finished with result true

#include "assert.h"
extern void __VERIFIER_assert(int cond);
int main()
{
  int status = 0;
  // status = *
  while(__VERIFIER_nondet_int()) // __verifier_nondet_int$1 = *
  {
    if(!status) // status = *
    {
      status = 1;
    }
    else if(status == 1)
    {
      status = 2;
    }
  } // status = 1 U 2

  while(__VERIFIER_nondet_int())
    __VERIFIER_assert(status != 3);

  return 0;
}