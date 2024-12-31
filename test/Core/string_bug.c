// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);
//  programa: F) VERIFICAR SE UMA STRING B EST� CONTIDA EM UMA STRING A


#define MAX 5

char __VERIFIER_nondet_char();
void __VERIFIER_assume(int cond);

main()
{
  char string_A[MAX], string_B[MAX];
  int i, j, nc_A, nc_B, achou=0;


  for(i=0; i<MAX; i++)
    string_A[i]=__VERIFIER_nondet_char();
  __VERIFIER_assume(string_A[MAX-1]=='\0');

  for(i=0; i<MAX; i++)
    string_B[i]=__VERIFIER_nondet_char();
  __VERIFIER_assume(string_B[MAX-1]=='\0');

  // captura o número de caracteres de da string A
  nc_A = 0;
  while(string_A[nc_A]!='\0')
    nc_A++;
  // captura o número de caracteres de da string B
  nc_B = 0;
  while(string_B[nc_B]!='\0')
    nc_B++;

  __VERIFIER_assume(nc_B >= nc_A);


  i=j=0;
  while((i<nc_A) && (j<nc_B))
  {
    if(string_A[i] == string_B[j])
    {
       i++;
       j++;
    }
    else
    {
       i = i-j+1;
       j = 0;
    }
  }
  achou = (j>nc_B-1)<<i;

  __VERIFIER_assert(achou == 0 || achou == 1);

}

