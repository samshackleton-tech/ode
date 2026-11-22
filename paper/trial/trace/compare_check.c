// The three functions of compare.ode against C, and a loop that calls one of them many times so that the
// instructions of one call can be counted.
//   compare_check                      every count from 0 to 40, the arrays the same and differing at each place
//   compare_check early|ct|differ same|first|last CALLS     CALLS calls on two arrays of 32 bytes
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern uint64_t ode_equal_early(const uint8_t *a, const uint8_t *b, uint64_t n);
extern uint64_t ode_equal_ct(const uint8_t *a, const uint8_t *b, uint64_t n);
extern uint64_t ode_differ_ct(const uint8_t *a, const uint8_t *b, uint64_t n);

int main(int argc, char **argv) {
    uint8_t a[40], b[40];
    for (int i = 0; i < 40; i++) a[i] = (uint8_t)(i * 37 + 11);
    memcpy(b, a, 40);
    if (argc == 1) {
        int cases = 0;
        for (uint64_t n = 0; n <= 40; n++) {
            if (ode_equal_early(a, b, n) != 1 || ode_equal_ct(a, b, n) != 1 || ode_differ_ct(a, b, n) != 0) return 10;
            cases++;
            for (uint64_t p = 0; p < n; p++) {
                for (int bit = 0; bit < 8; bit += 7) {
                    b[p] ^= (uint8_t)(1 << bit);
                    if (ode_equal_early(a, b, n) != 0 || ode_equal_ct(a, b, n) != 0 || ode_differ_ct(a, b, n) == 0) return 20;
                    b[p] ^= (uint8_t)(1 << bit);
                    cases++;
                }
            }
        }
        printf("the three functions agree with C in %d cases\n", cases);
        return 0;
    }
    uint64_t (*f)(const uint8_t *, const uint8_t *, uint64_t) =
        strcmp(argv[1], "ct") == 0 ? ode_equal_ct : strcmp(argv[1], "differ") == 0 ? ode_differ_ct : ode_equal_early;
    if (strcmp(argv[2], "first") == 0) b[0] ^= 1;
    if (strcmp(argv[2], "last") == 0) b[31] ^= 1;
    uint64_t calls = strtoull(argv[3], 0, 10);
    volatile uint64_t sum = 0;
    for (uint64_t i = 0; i < calls; i++) sum += f(a, b, 32);
    printf("%llu\n", (unsigned long long)sum);
    return 0;
}
