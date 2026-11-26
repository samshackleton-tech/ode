/* Real-silicon correctness + optional throughput harness for `utf8_valid`.
 * Contract ID: ykps3cug73fjveiyq2i3t55756kxodpe5l6x4gexcdnvjmyhcrna
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t (*utf8_fn)(const uint8_t *src, uint64_t n);
static utf8_fn g_fn = NULL;

#ifdef NATIVE_JIT_BIN
#include <sys/mman.h>
#include <unistd.h>
#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#endif
static utf8_fn load_jit(const char *path, size_t entry_off) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror("fopen"); exit(2); }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *tmp = (uint8_t *)malloc((size_t)sz);
    if (!tmp) { perror("malloc"); exit(2); }
    if (fread(tmp, 1, (size_t)sz, f) != (size_t)sz) { perror("fread"); exit(2); }
    fclose(f);
    size_t ps = (size_t)sysconf(_SC_PAGESIZE);
    size_t map_sz = (((size_t)sz + ps - 1) / ps) * ps;
    if (map_sz < ps) map_sz = ps;
#ifdef __APPLE__
    void *mem = mmap(NULL, map_sz, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANON | MAP_JIT, -1, 0);
    if (mem == MAP_FAILED) { perror("mmap"); exit(2); }
    pthread_jit_write_protect_np(0);
    memcpy(mem, tmp, (size_t)sz);
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(mem, (size_t)sz);
#else
    void *mem = mmap(NULL, map_sz, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (mem == MAP_FAILED) { perror("mmap"); exit(2); }
    memcpy(mem, tmp, (size_t)sz);
    if (mprotect(mem, map_sz, PROT_READ | PROT_EXEC) != 0) { perror("mprotect"); exit(2); }
#endif
    free(tmp);
    return (utf8_fn)((uint8_t *)mem + entry_off);
}
#else
extern uint64_t ode_ykps3cug73fjveiyq2i3t55756kxodpe5l6x4gexcdnvjmyhcrna(const uint8_t *src, uint64_t n);
#define NATIVE_SYM ode_ykps3cug73fjveiyq2i3t55756kxodpe5l6x4gexcdnvjmyhcrna
#endif

static inline int is_cont(uint8_t b) { return b >= 0x80 && b <= 0xBF; }

static uint64_t ref_utf8(const uint8_t *s, size_t n) {
    size_t i = 0;
    while (i < n) {
        uint8_t b0 = s[i];
        if (b0 < 0x80) { i += 1; continue; }
        if (b0 < 0xC2) return 0;
        if (b0 <= 0xDF) {
            if (i + 2 > n || !is_cont(s[i + 1])) return 0;
            i += 2;
        } else if (b0 <= 0xEF) {
            if (i + 3 > n || !is_cont(s[i + 2])) return 0;
            uint8_t b1 = s[i + 1];
            if (b0 == 0xE0) { if (b1 < 0xA0 || b1 > 0xBF) return 0; }
            else if (b0 == 0xED) { if (b1 < 0x80 || b1 > 0x9F) return 0; }
            else { if (!is_cont(b1)) return 0; }
            i += 3;
        } else if (b0 <= 0xF4) {
            if (i + 4 > n || !is_cont(s[i + 2]) || !is_cont(s[i + 3])) return 0;
            uint8_t b1 = s[i + 1];
            if (b0 == 0xF0) { if (b1 < 0x90 || b1 > 0xBF) return 0; }
            else if (b0 == 0xF4) { if (b1 < 0x80 || b1 > 0x8F) return 0; }
            else { if (!is_cont(b1)) return 0; }
            i += 4;
        } else return 0;
    }
    return 1;
}

static uint64_t rng = 0x123456789abcdef0ULL;
static uint32_t next_u32(void) {
    uint64_t x = rng; x ^= x << 13; x ^= x >> 7; x ^= x << 17; rng = x;
    return (uint32_t)x;
}

static int check_case(const uint8_t *buf, size_t n, const char *tag, int *passed, int *total) {
    (*total)++;
    uint64_t exp = ref_utf8(buf, n);
    uint64_t got = g_fn(buf, (uint64_t)n);
    if (got != exp) {
        fprintf(stderr, "FAIL %s (n=%zu): got=%llu exp=%llu\n",
                tag, n, (unsigned long long)got, (unsigned long long)exp);
        return 0;
    }
    (*passed)++;
    return 1;
}

#ifdef NATIVE_BENCH
#include <time.h>
static uint64_t now_ns(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}
#if defined(__x86_64__)
static inline uint64_t rdtsc_now(void) {
    uint32_t lo, hi;
    __asm__ volatile("lfence; rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}
#endif
#endif

int main(int argc, char **argv) {
#ifdef NATIVE_JIT_BIN
    if (argc < 3) { fprintf(stderr, "usage: %s text.bin entry_off\n", argv[0]); return 2; }
    g_fn = load_jit(argv[1], (size_t)strtoull(argv[2], NULL, 10));
#else
    (void)argc; (void)argv;
    g_fn = NATIVE_SYM;
#endif
    int passed = 0, total = 0;

    // 1. Empty & all 256 single bytes
    uint8_t empty[1] = {0};
    if (!check_case(empty, 0, "empty", &passed, &total)) return 1;
    for (int b = 0; b < 256; b++) {
        uint8_t one[1] = {(uint8_t)b};
        if (!check_case(one, 1, "single_byte", &passed, &total)) return 1;
    }

    // 2. Canonical RFC 3629 Table 3-7 edge vectors
    struct { const uint8_t b[8]; size_t n; } vecs[] = {
        {{0xC0, 0x80}, 2}, {{0xC1, 0xBF}, 2}, {{0xC2, 0x80}, 2}, {{0xDF, 0xBF}, 2},
        {{0xC2, 0x7F}, 2}, {{0xC2, 0xC0}, 2}, {{0xDF, 0xC0}, 2},
        {{0xE0, 0x9F, 0xBF}, 3}, {{0xE0, 0xA0, 0x80}, 3}, {{0xE0, 0xBF, 0xBF}, 3}, {{0xE0, 0xA0, 0x7F}, 3},
        {{0xE1, 0x80, 0x80}, 3}, {{0xEC, 0xBF, 0xBF}, 3},
        {{0xED, 0x80, 0x80}, 3}, {{0xED, 0x9F, 0xBF}, 3}, {{0xED, 0xA0, 0x80}, 3}, {{0xED, 0xBF, 0xBF}, 3},
        {{0xEE, 0x80, 0x80}, 3}, {{0xEF, 0xBF, 0xBF}, 3},
        {{0xF0, 0x8F, 0xBF, 0xBF}, 4}, {{0xF0, 0x90, 0x80, 0x80}, 4}, {{0xF0, 0xBF, 0xBF, 0xBF}, 4},
        {{0xF1, 0x80, 0x80, 0x80}, 4}, {{0xF3, 0xBF, 0xBF, 0xBF}, 4},
        {{0xF4, 0x80, 0x80, 0x80}, 4}, {{0xF4, 0x8F, 0xBF, 0xBF}, 4}, {{0xF4, 0x90, 0x80, 0x80}, 4},
        {{0xF5, 0x80, 0x80, 0x80}, 4}, {{0xF0, 0x90, 0x80}, 3}, {{0xE0, 0xA0}, 2},
        {{'a','b','c',0xC2,0xA9,0xE2,0x82,0xAC}, 8},
        {{'x',0xF0,0x9F,0x98,0x80,'y'}, 6},
    };
    for (size_t i = 0; i < sizeof(vecs)/sizeof(vecs[0]); i++) {
        if (!check_case(vecs[i].b, vecs[i].n, "edge", &passed, &total)) return 1;
    }

    // 3. Lengths 1..64 pure ASCII + single bad byte placed at every offset (catches unroll/tail bugs!)
    uint8_t buf[1024];
    for (size_t n = 1; n <= 64; n++) {
        for (size_t i = 0; i < n; i++) buf[i] = (uint8_t)(' ' + (i % 95));
        if (!check_case(buf, n, "ascii_valid", &passed, &total)) return 1;
        buf[n - 1] = 0x80;
        if (!check_case(buf, n, "ascii_tail_bad", &passed, &total)) return 1;
        buf[n - 1] = 'A';
        if (n >= 2) {
            buf[n / 2] = 0xFF;
            if (!check_case(buf, n, "ascii_mid_bad", &passed, &total)) return 1;
        }
    }

    // 4. 200 randomized valid & mutated multilingual UTF-8 buffers up to 512 B
    for (int t = 0; t < 200; t++) {
        size_t pos = 0;
        size_t target = 16 + (next_u32() % 480);
        while (pos + 4 <= target) {
            uint32_t kind = next_u32() % 10;
            if (kind < 6) {
                buf[pos++] = (uint8_t)(next_u32() & 0x7F);
            } else if (kind < 8) {
                buf[pos++] = (uint8_t)(0xC2 + (next_u32() % 30));
                buf[pos++] = (uint8_t)(0x80 + (next_u32() & 0x3F));
            } else if (kind == 8) {
                uint8_t b0 = (uint8_t)(0xE0 + (next_u32() % 16));
                uint8_t b1 = (b0 == 0xE0) ? (uint8_t)(0xA0 + (next_u32() % 32))
                           : (b0 == 0xED) ? (uint8_t)(0x80 + (next_u32() % 32))
                           : (uint8_t)(0x80 + (next_u32() & 0x3F));
                buf[pos++] = b0; buf[pos++] = b1; buf[pos++] = (uint8_t)(0x80 + (next_u32() & 0x3F));
            } else {
                uint8_t b0 = (uint8_t)(0xF0 + (next_u32() % 5));
                uint8_t b1 = (b0 == 0xF0) ? (uint8_t)(0x90 + (next_u32() % 48))
                           : (b0 == 0xF4) ? (uint8_t)(0x80 + (next_u32() % 16))
                           : (uint8_t)(0x80 + (next_u32() & 0x3F));
                buf[pos++] = b0; buf[pos++] = b1;
                buf[pos++] = (uint8_t)(0x80 + (next_u32() & 0x3F));
                buf[pos++] = (uint8_t)(0x80 + (next_u32() & 0x3F));
            }
        }
        if (t % 2 == 1 && pos > 0) {
            // Inject a subtle RFC 3629 defect (surrogate, overlong, or lone continuation)
            size_t p = next_u32() % pos;
            buf[p] ^= (uint8_t)(1u << (next_u32() % 8));
        }
        if (!check_case(buf, pos, "rand_utf8", &passed, &total)) return 1;
    }

    printf("NATIVE_PASS %d/%d\n", passed, total);

#ifdef NATIVE_BENCH
    uint8_t ascii[1024], mixed[1024];
    for (int i = 0; i < 1024; i++) ascii[i] = (uint8_t)('a' + (i % 26));
    const uint8_t pat[] = "Hello, \xE4\xB8\x96\xE7\x95\x8C! \xF0\x9F\x8C\x8D Caf\xC3\xA9 ";
    size_t plen = sizeof(pat) - 1;
    size_t mlen = 0;
    while (mlen + plen <= 1024) { memcpy(mixed + mlen, pat, plen); mlen += plen; }
    const int ITERS = 300000;
    uint64_t sink = 0;
    for (int i = 0; i < 20000; i++) sink += g_fn(ascii, 1024) + g_fn(mixed, mlen);
    uint64_t best_a = ~0ULL, best_m = ~0ULL;
    for (int r = 0; r < 5; r++) {
        uint64_t t0 = now_ns();
        for (int i = 0; i < ITERS; i++) sink += g_fn(ascii, 1024);
        uint64_t dt = now_ns() - t0; if (dt < best_a) best_a = dt;
        t0 = now_ns();
        for (int i = 0; i < ITERS; i++) sink += g_fn(mixed, mlen);
        dt = now_ns() - t0; if (dt < best_m) best_m = dt;
    }
    double ns_a = (double)best_a / ITERS, ns_m = (double)best_m / ITERS;
#if defined(__x86_64__)
    uint64_t cyc_a = ~0ULL, cyc_m = ~0ULL;
    for (int r = 0; r < 5; r++) {
        uint64_t t0 = rdtsc_now();
        for (int i = 0; i < ITERS; i++) sink += g_fn(ascii, 1024);
        uint64_t dt = rdtsc_now() - t0; if (dt < cyc_a) cyc_a = dt;
        t0 = rdtsc_now();
        for (int i = 0; i < ITERS; i++) sink += g_fn(mixed, mlen);
        dt = rdtsc_now() - t0; if (dt < cyc_m) cyc_m = dt;
    }
    printf("BENCH_UTF8 ascii1024=%.2f ns (%.1f ref_cyc, %.3f GiB/s) mixed%zu=%.2f ns (%.1f ref_cyc, %.3f GiB/s) sink=%llu\n",
           ns_a, (double)cyc_a / ITERS, (1024.0 / ns_a) * (1e9 / (1024.0*1024.0*1024.0)),
           mlen, ns_m, (double)cyc_m / ITERS, ((double)mlen / ns_m) * (1e9 / (1024.0*1024.0*1024.0)),
           (unsigned long long)sink);
#else
    printf("BENCH_UTF8 ascii1024=%.2f ns (%.3f GiB/s) mixed%zu=%.2f ns (%.3f GiB/s) sink=%llu\n",
           ns_a, (1024.0 / ns_a) * (1e9 / (1024.0*1024.0*1024.0)),
           mlen, ns_m, ((double)mlen / ns_m) * (1e9 / (1024.0*1024.0*1024.0)),
           (unsigned long long)sink);
#endif
#endif
    return 0;
}
