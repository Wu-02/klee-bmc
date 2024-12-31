extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) {
    if(!cond) {__assert_fail("0", "__VERIFIER_assert.c", 4, "__VERIFIER_assert");abort();}
}