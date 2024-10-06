#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

void test_urem_1() {
    unsigned x = 3;
    unsigned y = 2;
    unsigned a = x % y;
    unsigned n = klee_make_symbolic_int32();
    unsigned b = n % a;
}

void test_srem_1() {
    int x = 3;
    int y = 2;
    int a = x % y;
    int n = klee_make_symbolic_int32();
    int b = n % a;
}

int main() {
    test_urem_1();
    test_srem_1();
    return 0;
}
