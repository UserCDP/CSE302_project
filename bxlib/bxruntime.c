#include <sys/types.h>
#include <stdio.h>

void print_int(int64_t value) {
  (void) printf("%lld\n", value);
}

void print_bool(int64_t value) {
  (void) printf("%s\n", value ? "true" : "false");
}
