// RUN: %kleebmc --k-induction %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
extern void __VERIFIER_assert(int cond);

#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void reach_error()
{
  __VERIFIER_assert(0);
}

int main()
{
  int status = 0;

  while(__VERIFIER_nondet_int())
  {
    if(!status)
    {
      status = 1;
    }
    else if(status == 1)
    {
      status = 2;
    }
    else if(status >= 2)
    {
      status = 3;
    }
  }
  __VERIFIER_assert(status != 3);
  return 0;
}