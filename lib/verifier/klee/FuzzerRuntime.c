#include <stdlib.h>
#include <stdint.h>
#include <signal.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#define SIZE 4096

extern int __map2check_main__();

uint8_t fuzzer_data[SIZE];
size_t fuzzer_size;

uint8_t next_byte() {
  static size_t i = 0;
  if (i < fuzzer_size) {
    return fuzzer_data[i++];
  }
  exit(0);
}

static void signal_handler(int sig, siginfo_t *si, void *unused) {
    const char *error_msg;

    switch(sig) {
        case SIGSEGV:
            error_msg = "Segmentation fault\n";
            break;
        case SIGBUS:
            error_msg = "Bus error\n";
            break;
        case SIGABRT:
            error_msg = "abort() called\n";
            break;
        default:
            error_msg = "Unknown signal\n";
    }

    write(STDERR_FILENO, error_msg, strlen(error_msg));

    _exit(0);
}

// Register handlers for different signals that may crash the program
// Since we are only interested in assertion failures, we don't crash the program in this case.
void setup_signal_handler(void) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(struct sigaction));

    sa.sa_sigaction = signal_handler;
    sa.sa_flags = SA_SIGINFO;

    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);
    sigaction(SIGABRT, &sa, NULL);
}

void __assert_fail(const char *failedexpr, const char *file, unsigned int line,
                   const char *fn) {
  // This message will be used to identify assertion fails from other crashes.
  char *msg = "__assert_fail() called\n";
  write(STDOUT_FILENO, msg, strlen(msg));
  exit(100); // use a special retuan value to crash the program, but don't send SIGABRT
}

void abort() {
  // don't crash the program because this can be called when assume fails.
  exit(0);
}

int main(int argc, char **argv) {
    setup_signal_handler();
    FILE *fp = fopen(argv[1], "rb");
    if (fp == NULL) {
      printf("Can't open file or file does\'t exist.\n");
      exit(0);
    }
    fuzzer_size = fread(fuzzer_data, sizeof fuzzer_data[0], SIZE, fp);
    fclose(fp);

    __map2check_main__();

    return 0;
}

#define VERIFIER_NON_DET(type, alias)\
type __VERIFIER_nondet_##alias() {\
  uint64_t result = 0;\
  for (int i = 0; i < sizeof(type); i++)\
    result |= next_byte() << (8 * i);\
  return (type)result;\
}
VERIFIER_NON_DET(char, char)
VERIFIER_NON_DET(int, int)
VERIFIER_NON_DET(long, long)
VERIFIER_NON_DET(float, float)
VERIFIER_NON_DET(double, double)
VERIFIER_NON_DET(_Bool, bool)
VERIFIER_NON_DET(_Bool, _Bool)
VERIFIER_NON_DET(char *, pchar)
VERIFIER_NON_DET(void *, pointer)
VERIFIER_NON_DET(short, short)
VERIFIER_NON_DET(size_t, size_t)
VERIFIER_NON_DET(unsigned char, uchar)
VERIFIER_NON_DET(unsigned, unsigned)
VERIFIER_NON_DET(unsigned int, uint)
VERIFIER_NON_DET(unsigned int, u32)
VERIFIER_NON_DET(unsigned short, ushort)
VERIFIER_NON_DET(unsigned long, ulong)
VERIFIER_NON_DET(unsigned long, sector_t)
VERIFIER_NON_DET(long long, loff_t)
#ifdef __x86_64__
VERIFIER_NON_DET(__int128, int128)
VERIFIER_NON_DET(unsigned __int128, uint128)
#endif

void __VERIFIER_make_nondet(void *mem, size_t size, const char *name) {
    uint8_t *ptr = (uint8_t *)mem;
    for (size_t i = 0; i < size; i++) {
        ptr[i] = next_byte();
    }
}
