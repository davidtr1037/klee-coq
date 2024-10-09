#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

#include <klee/klee.h>

void f1(int x) {
    int y = x << 2;
}

void f2() {
    int x = klee_make_symbolic_int32();
    int y = x << 7;
}

int main() {
    f1(100);
    f2();
    return 0;
}
