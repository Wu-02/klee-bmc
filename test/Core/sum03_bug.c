// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
#define a (2)
int __VERIFIER_nondet_int();
unsigned int __VERIFIER_nondet_uint();
_Bool __VERIFIER_nondet_bool();

int main() {
  int sn=0;
  unsigned int x=0;

  while(1){
    if (x<10)
      sn = sn + a;
    x++;
    __VERIFIER_assert(sn==x*a || sn == 0);
  }
}
