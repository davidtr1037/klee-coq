#include <assert.h>
#include <stdint.h>

#include "klee/klee.h"

void klee_sdiv_check_32(int32_t x, int32_t y) {
  assert(!(x == INT32_MIN && y == -1) && y != 0);
}

void klee_sdiv_check_64(int64_t x, int64_t y) {
  assert(!(x == INT64_MIN && y == -1) && y != 0);
}
