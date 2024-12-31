// RUN: %kleebmc --k-induction %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);

int main()
{
  int status = 0;

  int cnt = 4;
  while(cnt--)
  {
  }
  do

  {
    __VERIFIER_assert(0);

  } while(0);
}