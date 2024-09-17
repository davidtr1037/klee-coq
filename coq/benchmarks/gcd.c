#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

int gcd(a, b) {
    int old_a = a;
    int old_b = b;

    while (a != b) {
        if (a <= b) {
            b = b - a;
        } else {
            a = a - b;
        }
        assert(a >= 0 && b >= 0 && (a < old_a || b < old_b));
    }

    return a;
}

int main() {
    int a = klee_make_symbolic_int32();
    int b = klee_make_symbolic_int32();
    klee_assume_bool(a > 0);
    klee_assume_bool(a < 5);
    klee_assume_bool(b > 0);
    klee_assume_bool(b < 5);
    gcd(a, b);
}
