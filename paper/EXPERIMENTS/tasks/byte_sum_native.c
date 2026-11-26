/* Native real-silicon test harness (+ optional NATIVE_BENCH timing) for `byte_sum`.
 * Contract ID: 4lzcji2jrhepmln3ah4chochys4klbj2cvugbw665estynenutja
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint64_t (*byte_sum_fn)(const uint8_t *a, uint64_t n);

#ifdef NATIVE_JIT_BIN
#include <sys/mman.h>
#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#endif
static byte_sum_fn load_jit(const char *path, size_t entry_off) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror("fopen"); exit(2); }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    size_t map_sz = (size_t)sz < 4096 ? 4096 : (((size_t)sz + 4095) & ~(size_t)4095);
#ifdef __APPLE__
    void *mem = mmap(NULL, map_sz, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANON | MAP_JIT, -1, 0);
    if (mem == MAP_FAILED) { perror("mmap"); exit(2); }
    pthread_jit_write_protect_np(0);
    if (fread(mem, 1, (size_t)sz, f) != (size_t)sz) { perror("fread"); exit(2); }
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(mem, (size_t)sz);
#else
    void *mem = mmap(NULL, map_sz, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (mem == MAP_FAILED) { perror("mmap"); exit(2); }
    if (fread(mem, 1, (size_t)sz, f) != (size_t)sz) { perror("fread"); exit(2); }
    if (mprotect(mem, map_sz, PROT_READ | PROT_EXEC) != 0) { perror("mprotect"); exit(2); }
#endif
    fclose(f);
    return (byte_sum_fn)((uint8_t *)mem + entry_off);
}
#else
extern uint64_t ode_4lzcji2jrhepmln3ah4chochys4klbj2cvugbw665estynenutja(const uint8_t *a, uint64_t n);
#endif

static uint64_t ref_byte_sum(const uint8_t *a, uint64_t n) {
    uint64_t s = 0;
    for (uint64_t i = 0; i < n; i++) s += a[i];
    return s;
}

static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

int main(int argc, char **argv) {
#ifdef NATIVE_JIT_BIN
    if (argc < 3) { fprintf(stderr, "usage: %s TEXT.bin ENTRY_OFF\n", argv[0]); return 2; }
    byte_sum_fn fn = load_jit(argv[1], (size_t)strtoull(argv[2], NULL, 0));
#else
    (void)argc; (void)argv;
    byte_sum_fn fn = ode_4lzcji2jrhepmln3ah4chochys4klbj2cvugbw665estynenutja;
#endif
    static uint8_t buf[8192];
    const uint64_t lens[] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 23, 24, 31, 32, 33, 63, 64, 65, 127, 128, 255, 257, 1024, 4096};
    int passed = 0, total = 0;
    uint64_t rng = 0x9e3779b97f4a7c15ULL;
    for (size_t li = 0; li < sizeof(lens) / sizeof(lens[0]); li++) {
        uint64_t n = lens[li];
        /* Pattern 0: zeros */
        memset(buf, 0, n);
        total++;
        uint64_t got = fn(buf, n), exp = ref_byte_sum(buf, n);
        if (got != exp) { fprintf(stderr, "FAIL zeros n=%llu got=%llu exp=%llu\n", (unsigned long long)n, (unsigned long long)got, (unsigned long long)exp); return 1; }
        passed++;
        /* Pattern 1: all 0xFF */
        memset(buf, 0xFF, n);
        total++;
        got = fn(buf, n); exp = ref_byte_sum(buf, n);
        if (got != exp) { fprintf(stderr, "FAIL 0xff n=%llu got=%llu exp=%llu\n", (unsigned long long)n, (unsigned long long)got, (unsigned long long)exp); return 1; }
        passed++;
        /* Pattern 2: ascending ramp */
        for (uint64_t i = 0; i < n; i++) buf[i] = (uint8_t)((i * 37 + 13) & 0xFF);
        total++;
        got = fn(buf, n); exp = ref_byte_sum(buf, n);
        if (got != exp) { fprintf(stderr, "FAIL ramp n=%llu got=%llu exp=%llu\n", (unsigned long long)n, (unsigned long long)got, (unsigned long long)exp); return 1; }
        passed++;
        /* Pattern 3: xorshift random */
        for (uint64_t i = 0; i < n; i++) {
            rng ^= rng >> 12; rng ^= rng << 25; rng ^= rng >> 27;
            buf[i] = (uint8_t)((rng * 2685821657736338717ULL) >> 56);
        }
        total++;
        got = fn(buf, n); exp = ref_byte_sum(buf, n);
        if (got != exp) { fprintf(stderr, "FAIL rand n=%llu got=%llu exp=%llu\n", (unsigned long long)n, (unsigned long long)got, (unsigned long long)exp); return 1; }
        passed++;
    }
    if (getenv("NATIVE_BENCH")) {
        for (uint64_t i = 0; i < 4096; i++) buf[i] = (uint8_t)(i & 0xFF);
        volatile uint64_t sink = 0;
        for (int w = 0; w < 2000; w++) sink += fn(buf, 4096);
        const int rounds = 9, iters = 20000;
        double samples[9];
        for (int r = 0; r < rounds; r++) {
            uint64_t t0 = now_ns();
            uint64_t acc = 0;
            for (int k = 0; k < iters; k++) acc += fn(buf, 4096);
            uint64_t dt = now_ns() - t0;
            sink ^= acc;
            samples[r] = (double)dt / (double)iters;
        }
        for (int i = 0; i < rounds; i++)
            for (int j = i + 1; j < rounds; j++)
                if (samples[j] < samples[i]) { double t = samples[i]; samples[i] = samples[j]; samples[j] = t; }
        printf("BENCH_4096_NS=%.2f\n", samples[rounds / 2]);
        (void)sink;
    }
    printf("NATIVE_PASS %d/%d\n", passed, total);
    return 0;
}
