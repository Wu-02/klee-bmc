// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

unsigned int __VERIFIER_nondet_uint();
int __VERIFIER_nondet_int();

#define SIZE 1

main()
{
  unsigned int j,k;
  int array[SIZE], menor;

  menor = __VERIFIER_nondet_int();

  for(j=0;j<SIZE;j++) {
       array[j] = __VERIFIER_nondet_int();

       if(array[j]<=menor)
          menor = array[j];
    }

    //@ assert array[0] > menor;
}

