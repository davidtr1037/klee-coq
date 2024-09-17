#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

int custom_div(int a, int b) {
    int r = a;
    while (r >= b) {
        r = r - b;
    }
    return r;
}

int factorial(int n) {
    int r = 1;
    int i = 1;
    while (i <= n) {
        r = r * i;
        i = i + 1;
    }
    return r;
}

void factorial_spec(int n) {
    int r = factorial(n);
    int i = 2;
    while (i <= n) {
        assert(custom_div(r, i) == 0);
        i = i + 1;
    }
}

int main() {
    int n = klee_make_symbolic_int32();
    klee_assume_bool(n < 5);
    factorial_spec(n);
    return 0;
}
