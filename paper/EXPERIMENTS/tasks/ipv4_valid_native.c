/* Real-silicon correctness + optional throughput harness for `ipv4_valid`.
 * Contract ID (identical on x86_64 and arm64):
 *   hh2id4zrh6vshq5hjpeuu53hlzy3x4uqhnnvuctrsk6hlfzseysa
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t (*ipv4_fn)(const uint8_t *pkt, uint64_t n);
static ipv4_fn g_fn = NULL;

#ifdef NATIVE_JIT_BIN
#include <sys/mman.h>
#include <unistd.h>
#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#endif
static ipv4_fn load_jit(const char *path, size_t entry_off) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror("fopen"); exit(2); }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *tmp = (uint8_t *)malloc((size_t)(sz > 0 ? sz : 1));
    if (!tmp) { perror("malloc"); exit(2); }
    if (sz > 0 && fread(tmp, 1, (size_t)sz, f) != (size_t)sz) { perror("fread"); exit(2); }
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
    return (ipv4_fn)((uint8_t *)mem + entry_off);
}
#else
extern uint64_t ode_hh2id4zrh6vshq5hjpeuu53hlzy3x4uqhnnvuctrsk6hlfzseysa(
    const uint8_t *pkt, uint64_t n);
#endif

static uint64_t ref_ipv4_valid(const uint8_t *pkt, uint64_t n) {
    if (n < 20) return 0;
    uint8_t ver = pkt[0] >> 4;
    uint8_t ihl = pkt[0] & 0x0f;
    if (ver != 4 || ihl < 5) return 0;
    uint64_t hlen = (uint64_t)ihl * 4;
    if (hlen > n) return 0;
    uint64_t tot = ((uint64_t)pkt[2] << 8) | pkt[3];
    if (tot < hlen || tot > n) return 0;
    uint64_t s = 0;
    for (uint64_t k = 0; k < (uint64_t)ihl * 2; k++) {
        s += ((uint64_t)pkt[2 * k] << 8) | pkt[2 * k + 1];
    }
    s = (s & 0xffff) + (s >> 16);
    s = (s & 0xffff) + (s >> 16);
    return (s == 0xffff) ? 1 : 0;
}

static uint64_t rng = 0x9e3779b97f4a7c15ULL;
static uint64_t xorshift(void) {
    uint64_t x = rng;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rng = x;
    return x;
}

static void fill_valid(uint8_t *buf, uint8_t ihl, uint16_t tot_len) {
    uint64_t hlen = (uint64_t)ihl * 4;
    buf[0] = (uint8_t)((4 << 4) | (ihl & 0x0f));
    buf[1] = (uint8_t)(xorshift() & 0xff);
    buf[2] = (uint8_t)(tot_len >> 8);
    buf[3] = (uint8_t)(tot_len & 0xff);
    for (uint64_t i = 4; i < hlen; i++) buf[i] = (uint8_t)(xorshift() & 0xff);
    buf[10] = 0;
    buf[11] = 0;
    uint64_t s = 0;
    for (uint64_t i = 0; i < hlen; i += 2) s += ((uint64_t)buf[i] << 8) | buf[i + 1];
    s = (s & 0xffff) + (s >> 16);
    s = (s & 0xffff) + (s >> 16);
    uint16_t ck = (uint16_t)(~s & 0xffff);
    buf[10] = (uint8_t)(ck >> 8);
    buf[11] = (uint8_t)(ck & 0xff);
}

static int total = 0;
static void check(const char *label, const uint8_t *buf, uint64_t n) {
    uint64_t exp = ref_ipv4_valid(buf, n);
    uint64_t got = g_fn(buf, n);
    total++;
    if (got != exp) {
        fprintf(stderr, "FAIL %s (n=%llu): got=%llu exp=%llu\n",
                label, (unsigned long long)n, (unsigned long long)got, (unsigned long long)exp);
        exit(1);
    }
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
    g_fn = ode_hh2id4zrh6vshq5hjpeuu53hlzy3x4uqhnnvuctrsk6hlfzseysa;
#endif
    static uint8_t buf[65536];

    // 1. Famous RFC 791 / Wikipedia 20-byte IPv4 header (total_len = 0x0073 = 115, checksum = 0xb861)
    const uint8_t wiki[20] = {
        0x45, 0x00, 0x00, 0x73, 0x00, 0x00, 0x40, 0x00,
        0x40, 0x11, 0xb8, 0x61, 0xc0, 0xa8, 0x00, 0x01,
        0xc0, 0xa8, 0x00, 0xc7
    };
    memset(buf, 0xaa, 128);
    memcpy(buf, wiki, 20);
    check("wiki_ok_115", buf, 115);
    check("wiki_ok_128", buf, 128);
    check("wiki_trunc_114", buf, 114);
    for (int len = 0; len < 20; len++) {
        char lbl[32];
        snprintf(lbl, sizeof(lbl), "short_%d", len);
        check(lbl, buf, (uint64_t)len);
    }

    // 2. All version values 0..15 and all IHL values 0..15
    for (int ver = 0; ver < 16; ver++) {
        for (int ihl = 0; ihl < 16; ihl++) {
            uint8_t h[64];
            memset(h, 0, sizeof(h));
            if (ihl >= 5) fill_valid(h, (uint8_t)ihl, (uint16_t)(ihl * 4));
            h[0] = (uint8_t)((ver << 4) | ihl);
            // Recompute checksum if ver != 4 so ONLY version fails
            if (ihl >= 5 && ver != 4) {
                h[10] = h[11] = 0;
                uint64_t s = 0;
                for (int i = 0; i < ihl * 4; i += 2) s += ((uint64_t)h[i] << 8) | h[i + 1];
                s = (s & 0xffff) + (s >> 16);
                s = (s & 0xffff) + (s >> 16);
                uint16_t ck = (uint16_t)(~s & 0xffff);
                h[10] = (uint8_t)(ck >> 8);
                h[11] = (uint8_t)(ck & 0xff);
            }
            char lbl[32];
            snprintf(lbl, sizeof(lbl), "v%d_ihl%d", ver, ihl);
            check(lbl, h, 64);
        }
    }

    // 3. Single-bit flip in EVERY byte of a 20-byte (ihl=5) and 60-byte (ihl=15) header
    for (int ihl_idx = 0; ihl_idx < 2; ihl_idx++) {
        uint8_t ihl = ihl_idx == 0 ? 5 : 15;
        uint64_t hlen = (uint64_t)ihl * 4;
        fill_valid(buf, ihl, (uint16_t)hlen);
        check("base_valid", buf, hlen);
        for (uint64_t b = 0; b < hlen; b++) {
            buf[b] ^= 0x01;
            check("bitflip_lo", buf, hlen);
            buf[b] ^= 0x01;
            buf[b] ^= 0x80;
            check("bitflip_hi", buf, hlen);
            buf[b] ^= 0x80;
        }
        // Header length exceeds buffer
        check("hlen_gt_n", buf, hlen - 1);
    }

    // 4. Carry-fold boundary: all-0xFF header words (max sum = 30 * 65535 = 1,966,050)
    //    and tot_len < hlen, tot_len == 65535
    fill_valid(buf, 15, 65535);
    check("max_65535_ok", buf, 65535);
    check("max_65535_short", buf, 65534);
    fill_valid(buf, 5, 19);
    check("tot_lt_hlen", buf, 64);
    // Max-carry header: set words to 0xffff except hdr[0..3] and checksum
    memset(buf, 0xff, 60);
    buf[0] = 0x4f;
    buf[2] = 0x00;
    buf[3] = 0x3c;
    buf[10] = buf[11] = 0;
    {
        uint64_t s = 0;
        for (int i = 0; i < 60; i += 2) s += ((uint64_t)buf[i] << 8) | buf[i + 1];
        s = (s & 0xffff) + (s >> 16);
        s = (s & 0xffff) + (s >> 16);
        uint16_t ck = (uint16_t)(~s & 0xffff);
        buf[10] = (uint8_t)(ck >> 8);
        buf[11] = (uint8_t)(ck & 0xff);
    }
    check("max_carry_60", buf, 60);

    // 5. 80 randomized valid & corrupted headers across ihl 5..15
    for (int t = 0; t < 80; t++) {
        uint8_t ihl = (uint8_t)(5 + (xorshift() % 11));
        uint16_t hlen = (uint16_t)(ihl * 4);
        uint16_t extra = (uint16_t)(xorshift() % 1400);
        uint16_t tot = (uint16_t)(hlen + extra);
        fill_valid(buf, ihl, tot);
        check("rand_ok", buf, tot);
        buf[10] ^= 0x04;
        check("rand_bad_ck", buf, tot);
        buf[10] ^= 0x04;
    }

    printf("NATIVE_PASS %d/%d\n", total, total);

#ifdef NATIVE_BENCH
    static uint8_t pkt20[64], pkt60[64];
    fill_valid(pkt20, 5, 20);
    fill_valid(pkt60, 15, 60);
    if (g_fn(pkt20, 20) != 1 || g_fn(pkt60, 60) != 1) {
        fprintf(stderr, "bench packet invalid\n");
        return 1;
    }
    const int ITERS = 2000000;
    volatile uint64_t sink = 0;
    for (int i = 0; i < 50000; i++) sink += g_fn(pkt20, 20) + g_fn(pkt60, 60);

    uint64_t b20 = ~0ULL, b60 = ~0ULL;
    for (int r = 0; r < 5; r++) {
        uint64_t t0 = now_ns();
        for (int i = 0; i < ITERS; i++) sink += g_fn(pkt20, 20);
        uint64_t d0 = now_ns() - t0;
        if (d0 < b20) b20 = d0;
        uint64_t t1 = now_ns();
        for (int i = 0; i < ITERS; i++) sink += g_fn(pkt60, 60);
        uint64_t d1 = now_ns() - t1;
        if (d1 < b60) b60 = d1;
    }
    double ns20 = (double)b20 / (double)ITERS;
    double ns60 = (double)b60 / (double)ITERS;
#if defined(__x86_64__)
    uint64_t c20 = ~0ULL, c60 = ~0ULL;
    for (int r = 0; r < 5; r++) {
        uint64_t t0 = rdtsc_now();
        for (int i = 0; i < ITERS; i++) sink += g_fn(pkt20, 20);
        uint64_t d0 = rdtsc_now() - t0;
        if (d0 < c20) c20 = d0;
        uint64_t t1 = rdtsc_now();
        for (int i = 0; i < ITERS; i++) sink += g_fn(pkt60, 60);
        uint64_t d1 = rdtsc_now() - t1;
        if (d1 < c60) c60 = d1;
    }
    printf("BENCH_IPV4 ihl5=%.2f ns (%.2f ref_cyc) ihl15=%.2f ns (%.2f ref_cyc) sink=%llu\n",
           ns20, (double)c20 / ITERS, ns60, (double)c60 / ITERS, (unsigned long long)sink);
#else
    printf("BENCH_IPV4 ihl5=%.2f ns ihl15=%.2f ns sink=%llu\n",
           ns20, ns60, (unsigned long long)sink);
#endif
#endif
    return 0;
}
