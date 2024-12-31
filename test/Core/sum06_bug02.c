// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
#define a 2
int main()
{
  unsigned long long int i=1, sn=0;
  while ( 1 ) {
    sn = sn + ((i%10==9)? 4 : a);
    __VERIFIER_assert ( sn==i*a ) ;
    i++;
  }
}
