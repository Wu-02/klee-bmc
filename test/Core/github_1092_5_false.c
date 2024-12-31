// RUN: %kleebmc --k-induction %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
extern void __VERIFIER_assert(int cond);
int status = 0;
int foo()
{
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
}

int bar()
{
  do
  {
    __VERIFIER_assert(status != 2);
  } while(0);
}
int main()
{
  foo();
  bar();
  return 0;
}