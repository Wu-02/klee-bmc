extern void __assert_fail(const char *, const char *, unsigned int,
                          const char *) __attribute__((__nothrow__, __leaf__))
__attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "deep-nested.c", 2, "reach_error"); }

void __VERIFIER_assert(_Bool cond) {
  if (!(cond)) {
  ERROR: {
    reach_error();
    abort();
  }
  }
  return;
}

int main() {
  unsigned a, b, c, d, e;

  unsigned uint32_max=0xffffffff;

  for (d = 0; d < uint32_max - 1; ++d) {
    for (e = 0; e < uint32_max - 1; ++e) {
      if ((d == e) && (e == (uint32_max - 2))) {
        __VERIFIER_assert(0);
      }
    }
  }

  return 0;
}
