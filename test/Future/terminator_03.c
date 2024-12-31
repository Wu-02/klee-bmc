// RUN: %kleebmc --k-induction -Wno-error=implicit-int %s | %FileCheck %s
// CHECK: Verification finished with result true

#include "assert.h"
int __VERIFIER_nondet_int();
_Bool __VERIFIER_nondet_bool();

main()
{
  int x=__VERIFIER_nondet_int();
  int y=__VERIFIER_nondet_int();

  if (y>0)
  {
    while(x<100)
    {
      x=x+y;
     }
  }
  //  assert(array[0]>=menor);
}


