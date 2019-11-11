#include <stdint.h>
#include <stddef.h>

void fibonacci(uint64_t *x, const size_t n) {
  x[0] = 1;
  x[1] = 1;

  for (size_t i = 2; i < n; i++) {
    x[i] = x[i-1] + x[i-2];
  }
}
