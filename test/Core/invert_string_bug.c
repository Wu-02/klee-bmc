// RUN: %kleebmc %s | %FileCheck %s
// CHECK: Verification finished with result false

void __VERIFIER_assert(int cond);

extern char __VERIFIER_nondet_char();

int main() {
    int MAX=10000;
    char str1[MAX], str2[MAX];
    int cont, i, j;
    cont = 0;

    for (i=0; i<MAX; i++) {
        str1[i]=__VERIFIER_nondet_char();
    }
	str1[MAX-1]= '\0';

    j = 0;

    // Copia str1 inversa para str2
    for (i = MAX - 1; i >= 0; i--) {
        str2[j] = str1[0];
        j++;
    }
	//__VERIFIER_assume(i<0);
	j = MAX-1;
    for (i=0; i<MAX; i++) {
      __VERIFIER_assert(str1[i] == str2[j]);
	  j--;
    }

}
