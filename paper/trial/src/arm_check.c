// What src/arm.ode2's three functions must compute, in C, for a few inputs. Prints one line and returns 0
// where they agree; a number that says which comparison failed where they do not.
#include <stdint.h>
#include <stdio.h>

extern void arm_mix16_3(uint32_t *out, const uint32_t *d, const uint32_t *a);
extern void arm_mix12(uint32_t *out, const uint32_t *d, const uint32_t *a);
extern uint64_t arm_all_zero_words(const uint32_t *xs, uint64_t n);

static uint32_t ror32(uint32_t x, int r) { return (x >> r) | (x << (32 - r)); }

int main(void) {
    uint32_t d[4] = {0x12345678u, 1u, 0xffffffffu, 0x80000000u};
    uint32_t a[4] = {0xdeadbeefu, 2u, 0u, 1u};
    uint32_t o16[4], o12[4];
    arm_mix16_3(o16, d, a);
    arm_mix12(o12, d, a);
    for (int i = 0; i < 4; i++) {
        uint32_t d1 = ror32(d[i] ^ a[i], 16);
        uint32_t a2 = ror32(a[i] ^ d1, 16);
        uint32_t d3 = ror32(d1 ^ a2, 16);
        if (o16[i] != d3) return 10 + i;
        if (o12[i] != ror32(d[i] ^ a[i], 12)) return 20 + i;
    }
    uint32_t zeros[4] = {0, 0, 0, 0};
    uint32_t last[4] = {0, 0, 0, 0xffffffffu};
    uint32_t first[4] = {1, 0, 0, 0};
    if (arm_all_zero_words(zeros, 0) != 1) return 30;
    if (arm_all_zero_words(zeros, 4) != 1) return 31;
    if (arm_all_zero_words(last, 4) != 0) return 32;
    if (arm_all_zero_words(first, 4) != 0) return 33;
    if (arm_all_zero_words(last, 3) != 1) return 34;
    printf("the three functions agree with the C\n");
    return 0;
}
