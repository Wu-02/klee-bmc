// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
#define a 2
int main()
{
  unsigned long long int i=1, sn=0;
  unsigned int n=20;
  while ( i<=n ) {
    sn = sn + ((i%15==14)? 4 : a);
    i++;
  }
  __VERIFIER_assert ( sn==n*a ) ;
}
