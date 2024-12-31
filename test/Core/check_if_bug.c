// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
int __VERIFIER_nondet_int();
void __VERIFIER_assume(int cond);

int main() {

  int x=__VERIFIER_nondet_int();
  __VERIFIER_assume(x>0);
  int y=__VERIFIER_nondet_int();
  __VERIFIER_assume(y>=0);
  __VERIFIER_assume(y<1);
  int z=0;

  while(x>0) {
      x--;
      if(x==y) z=1; // __VERIFIER_assert(0);
  }
  __VERIFIER_assert(z==0);
}

