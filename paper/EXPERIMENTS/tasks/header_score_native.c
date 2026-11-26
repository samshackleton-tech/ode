/* Native hardware test harness for verified 16-field fixed-header policy risk scorer. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef uint64_t (*hs_fn_t)(const uint8_t *h, uint64_t n);

#ifdef NATIVE_JIT_BIN
#include <pthread.h>
#include <sys/mman.h>
#include <libkern/OSCacheControl.h>

static hs_fn_t load_jit_fn(const char *path, size_t entry_off, void **out_buf, size_t *out_sz) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror("fopen"); exit(2); }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    size_t map_sz = ((size_t)sz + 4095) & ~(size_t)4095;
    if (map_sz == 0) map_sz = 4096;
    void *mem = mmap(NULL, map_sz, PROT_READ | PROT_WRITE | PROT_EXEC,
                     MAP_PRIVATE | MAP_ANON | MAP_JIT, -1, 0);
    if (mem == MAP_FAILED) { perror("mmap"); exit(2); }
    pthread_jit_write_protect_np(0);
    if (fread(mem, 1, (size_t)sz, f) != (size_t)sz) { perror("fread"); exit(2); }
    fclose(f);
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(mem, (size_t)sz);
    *out_buf = mem;
    *out_sz = map_sz;
    return (hs_fn_t)((uint8_t *)mem + entry_off);
}
#else
extern uint64_t ode_hrslejxv4lnql6e53janwkl7tjtgn7oydsuja33hgvgktnbwwehq(const uint8_t *h, uint64_t n);
#endif

static uint64_t ref_score(const uint8_t h[16]) {
    uint64_t s = 0;
    if (h[0]  >= 128) s += 17;
    if (h[1]  >= 64)  s += 23;
    if (h[2]  >= 200) s += 31;
    if (h[3]  == 0)   s += 41;
    if (h[4]  >= 100) s += 13;
    if (h[5]  <  16)  s += 29;
    if (h[6]  >= 180) s += 37;
    if (h[7]  == 255) s += 53;
    if (h[8]  >= 90)  s += 19;
    if (h[9]  <  40)  s += 43;
    if (h[10] >= 150) s += 11;
    if (h[11] == 42)  s += 59;
    if (h[12] >= 220) s += 47;
    if (h[13] <  32)  s += 61;
    if (h[14] >= 75)  s += 29;
    if (h[15] == 1)   s += 71;
    return s;
}

static void check(hs_fn_t fn, const char *label, const uint8_t h[16]) {
    uint64_t want = ref_score(h);
    uint64_t got = fn(h, 16);
    if (got != want) {
        fprintf(stderr, "FAIL %s: got=%llu want=%llu\n",
                label, (unsigned long long)got, (unsigned long long)want);
        exit(1);
    }
}

int main(int argc, char **argv) {
    hs_fn_t fn = NULL;
#ifdef NATIVE_JIT_BIN
    void *buf = NULL;
    size_t map_sz = 0;
    if (argc != 3) { fprintf(stderr, "usage: %s text.bin entry_off\n", argv[0]); return 2; }
    fn = load_jit_fn(argv[1], (size_t)strtoull(argv[2], NULL, 0), &buf, &map_sz);
#else
    (void)argc; (void)argv;
    fn = ode_hrslejxv4lnql6e53janwkl7tjtgn7oydsuja33hgvgktnbwwehq;
#endif
    uint8_t all0[16] = {0};
    uint8_t all255[16];
    uint8_t all_fire[16] = {128, 64, 200, 0, 100, 15, 180, 255, 90, 39, 150, 42, 220, 31, 75, 1};
    uint8_t none_fire[16] = {127, 63, 199, 1, 99, 16, 179, 254, 89, 40, 149, 41, 219, 32, 74, 2};
    uint8_t hi_miss[16] = {127, 63, 199, 255, 99, 255, 179, 0, 89, 255, 149, 43, 219, 255, 74, 0};
    for (int i = 0; i < 16; i++) all255[i] = 255;

    check(fn, "all0", all0);
    check(fn, "all255", all255);
    check(fn, "all_fire", all_fire);
    check(fn, "none_fire", none_fire);
    check(fn, "hi_miss", hi_miss);

    for (int i = 0; i < 16; i++) {
        uint8_t tmp[16];
        for (int j = 0; j < 16; j++) tmp[j] = none_fire[j];
        tmp[i] = all_fire[i];
        check(fn, "single_rule", tmp);
    }

    uint64_t rng = 0x9e3779b97f4a7c15ULL;
    for (int t = 0; t < 1000; t++) {
        uint8_t h[16];
        for (int i = 0; i < 16; i++) {
            rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
            h[i] = (uint8_t)(rng & 0xff);
        }
        check(fn, "fuzz", h);
    }
    printf("NATIVE_PASS 1021/1021\n");
#ifdef NATIVE_JIT_BIN
    munmap(buf, map_sz);
#endif
    return 0;
}
