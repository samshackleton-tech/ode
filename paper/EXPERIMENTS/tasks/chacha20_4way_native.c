/* Real-silicon correctness + optional throughput harness for `chacha20_4way`.
 * Contract IDs:
 *   x86_64 (`needs avx needs avx512`): i4ms6vhpzvftnenj5opj7thi6ltpvqquxwsasrtyfda67m3l7k2a
 *   arm64:                             53a2xllgc33xg5rjaplh2yk5rojhwijvtmd55idtb2jx5mzvwqda
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef void (*chacha_fn)(uint8_t out[256], const uint8_t st[256]);
static chacha_fn g_fn = NULL;

#ifdef NATIVE_JIT_BIN
#include <sys/mman.h>
#include <unistd.h>
#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#endif
static chacha_fn load_jit(const char *path, size_t entry_off) {
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
    return (chacha_fn)((uint8_t *)mem + entry_off);
}
#else
#if defined(__aarch64__)
extern void ode_53a2xllgc33xg5rjaplh2yk5rojhwijvtmd55idtb2jx5mzvwqda(uint8_t out[256], const uint8_t st[256]);
#define NATIVE_SYM ode_53a2xllgc33xg5rjaplh2yk5rojhwijvtmd55idtb2jx5mzvwqda
#else
extern void ode_i4ms6vhpzvftnenj5opj7thi6ltpvqquxwsasrtyfda67m3l7k2a(uint8_t out[256], const uint8_t st[256]);
#define NATIVE_SYM ode_i4ms6vhpzvftnenj5opj7thi6ltpvqquxwsasrtyfda67m3l7k2a
#endif
#endif

static inline uint32_t rotl32(uint32_t x, int n) {
    return (x << n) | (x >> (32 - n));
}

static void ref_qr(uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d) {
    *a += *b; *d ^= *a; *d = rotl32(*d, 16);
    *c += *d; *b ^= *c; *b = rotl32(*b, 12);
    *a += *b; *d ^= *a; *d = rotl32(*d, 8);
    *c += *d; *b ^= *c; *b = rotl32(*b, 7);
}

static void ref_chacha20_block(uint32_t out[16], const uint32_t in[16]) {
    uint32_t x[16];
    memcpy(x, in, 64);
    for (int i = 0; i < 10; i++) {
        ref_qr(&x[0], &x[4], &x[8],  &x[12]);
        ref_qr(&x[1], &x[5], &x[9],  &x[13]);
        ref_qr(&x[2], &x[6], &x[10], &x[14]);
        ref_qr(&x[3], &x[7], &x[11], &x[15]);
        ref_qr(&x[0], &x[5], &x[10], &x[15]);
        ref_qr(&x[1], &x[6], &x[11], &x[12]);
        ref_qr(&x[2], &x[7], &x[8],  &x[13]);
        ref_qr(&x[3], &x[4], &x[9],  &x[14]);
    }
    for (int i = 0; i < 16; i++) out[i] = x[i] + in[i];
}

static uint64_t rng = 0xdeadbeefcafebabeULL;
static uint32_t next_u32(void) {
    uint64_t x = rng;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rng = x;
    return (uint32_t)x;
}

#ifdef NATIVE_BENCH
#include <time.h>
static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
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

    // 1. Official RFC 8439 Section 2.3.2 test vector across all 4 lanes (with distinct counters 1..4)
    const uint32_t rfc_in[16] = {
        0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
        0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c,
        0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c,
        0x00000001, 0x09000000, 0x4a000000, 0x00000000
    };
    const uint32_t rfc_exp0[16] = {
        0xe4e7f110, 0x15593bd1, 0x1fdd0f50, 0xc47120a3,
        0xc7f4d1c7, 0x0368c033, 0x9aaa2204, 0x4e6cd4c3,
        0x466482d2, 0x09aa9f07, 0x05d7c214, 0xa2028bd9,
        0xd19c12b5, 0xb94e16de, 0xe883d0cb, 0x4e3c50a2
    };
    uint32_t st[64], got[64], exp[64];
    for (int lane = 0; lane < 4; lane++) {
        memcpy(&st[lane * 16], rfc_in, 64);
        st[lane * 16 + 12] = (uint32_t)(1 + lane);
        ref_chacha20_block(&exp[lane * 16], &st[lane * 16]);
    }
    if (memcmp(exp, rfc_exp0, 64) != 0) {
        fprintf(stderr, "internal ref mismatch vs RFC 8439\n");
        return 2;
    }
    memset(got, 0xcc, sizeof(got));
    g_fn((uint8_t *)got, (const uint8_t *)st);
    for (int w = 0; w < 64; w++) {
        total++;
        if (got[w] != exp[w]) {
            fprintf(stderr, "FAIL RFC8439 word %d: got=%08x exp=%08x\n", w, got[w], exp[w]);
            return 1;
        }
        passed++;
    }

    // 2. All-zero, all-ones, and 32 randomized 4-way batches (4*34 = 136 blocks, 256 B each)
    for (int trial = 0; trial < 34; trial++) {
        for (int i = 0; i < 64; i++) {
            if (trial == 0) st[i] = 0;
            else if (trial == 1) st[i] = 0xffffffffu;
            else st[i] = next_u32();
        }
        for (int lane = 0; lane < 4; lane++)
            ref_chacha20_block(&exp[lane * 16], &st[lane * 16]);
        memset(got, 0x55, sizeof(got));
        g_fn((uint8_t *)got, (const uint8_t *)st);
        total++;
        if (memcmp(got, exp, sizeof(exp)) != 0) {
            fprintf(stderr, "FAIL trial %d\n", trial);
            return 1;
        }
        passed++;
    }

    printf("NATIVE_PASS %d/%d\n", passed, total);

#ifdef NATIVE_BENCH
    for (int lane = 0; lane < 4; lane++) {
        memcpy(&st[lane * 16], rfc_in, 64);
        st[lane * 16 + 12] = (uint32_t)(1 + lane);
    }
    const int ITERS = 500000;
    uint64_t sink = 0;
    for (int i = 0; i < 20000; i++) {
        g_fn((uint8_t *)got, (const uint8_t *)st);
        sink += got[0];
    }
    uint64_t best_ns = ~0ULL;
    for (int r = 0; r < 5; r++) {
        uint64_t t0 = now_ns();
        for (int i = 0; i < ITERS; i++) {
            g_fn((uint8_t *)got, (const uint8_t *)st);
            sink += got[i & 63];
        }
        uint64_t dt = now_ns() - t0;
        if (dt < best_ns) best_ns = dt;
    }
    double ns = (double)best_ns / (double)ITERS;
    double gib = (256.0 / ns) * (1e9 / (1024.0 * 1024.0 * 1024.0));
#if defined(__x86_64__)
    uint64_t best_cyc = ~0ULL;
    for (int r = 0; r < 5; r++) {
        uint64_t t0 = rdtsc_now();
        for (int i = 0; i < ITERS; i++) {
            g_fn((uint8_t *)got, (const uint8_t *)st);
            sink += got[i & 63];
        }
        uint64_t dt = rdtsc_now() - t0;
        if (dt < best_cyc) best_cyc = dt;
    }
    printf("BENCH_CHACHA4 %.2f ns/256B (%.3f GiB/s, %.1f ref_cyc) sink=%llu\n",
           ns, gib, (double)best_cyc / (double)ITERS, (unsigned long long)sink);
#else
    printf("BENCH_CHACHA4 %.2f ns/256B (%.3f GiB/s) sink=%llu\n",
           ns, gib, (unsigned long long)sink);
#endif
#endif
    return 0;
}
