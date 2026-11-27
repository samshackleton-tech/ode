/* Real-silicon correctness harness for `blake3_compress1`.
 * Contract IDs:
 *   x86_64 (`needs avx needs avx512`): 3mwrna2mvj7xwwguz2quumvjbhrxve5aq6r576ucii67s6l3yh2q
 *   arm64:                             hkxqh23yct3ndyut6iehnh6p7jtyy4qprhin7lqtbwgxqzt65u4q
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef void (*b3_c1_fn)(uint32_t *h, const uint32_t *m, uint32_t length, uint64_t t, uint32_t flags);
static b3_c1_fn g_fn = NULL;

#ifdef NATIVE_JIT_BIN
#include <sys/mman.h>
#include <unistd.h>
#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#endif
static b3_c1_fn load_jit(const char *path, size_t entry_off) {
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
    return (b3_c1_fn)((uint8_t *)mem + entry_off);
}
#else
#if defined(__aarch64__)
extern void ode_hkxqh23yct3ndyut6iehnh6p7jtyy4qprhin7lqtbwgxqzt65u4q(uint32_t *h, const uint32_t *m, uint32_t length, uint64_t t, uint32_t flags);
#define NATIVE_SYM ode_hkxqh23yct3ndyut6iehnh6p7jtyy4qprhin7lqtbwgxqzt65u4q
#else
extern void ode_3mwrna2mvj7xwwguz2quumvjbhrxve5aq6r576ucii67s6l3yh2q(uint32_t *h, const uint32_t *m, uint32_t length, uint64_t t, uint32_t flags);
#define NATIVE_SYM ode_3mwrna2mvj7xwwguz2quumvjbhrxve5aq6r576ucii67s6l3yh2q
#endif
#endif

static const uint32_t IV[8] = {
    0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au,
    0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u,
};
static const uint8_t PERM[16] = {
    2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8
};

static inline uint32_t rotr32(uint32_t x, unsigned n) {
    return (x >> n) | (x << (32u - n));
}

static void g_ref(uint32_t v[16], int a, int b, int c, int d, uint32_t mx, uint32_t my) {
    v[a] = v[a] + v[b] + mx;
    v[d] = rotr32(v[d] ^ v[a], 16);
    v[c] = v[c] + v[d];
    v[b] = rotr32(v[b] ^ v[c], 12);
    v[a] = v[a] + v[b] + my;
    v[d] = rotr32(v[d] ^ v[a], 8);
    v[c] = v[c] + v[d];
    v[b] = rotr32(v[b] ^ v[c], 7);
}

static void compress_ref(uint32_t h[8], const uint32_t m_in[16], uint32_t length, uint64_t t, uint32_t flags) {
    uint32_t v[16], m[16], next_m[16];
    memcpy(v, h, 32);
    v[8] = IV[0]; v[9] = IV[1]; v[10] = IV[2]; v[11] = IV[3];
    v[12] = (uint32_t)t;
    v[13] = (uint32_t)(t >> 32);
    v[14] = length;
    v[15] = flags;
    memcpy(m, m_in, 64);
    for (int r = 0; r < 7; r++) {
        g_ref(v, 0, 4, 8, 12, m[0], m[1]);
        g_ref(v, 1, 5, 9, 13, m[2], m[3]);
        g_ref(v, 2, 6, 10, 14, m[4], m[5]);
        g_ref(v, 3, 7, 11, 15, m[6], m[7]);
        g_ref(v, 0, 5, 10, 15, m[8], m[9]);
        g_ref(v, 1, 6, 11, 12, m[10], m[11]);
        g_ref(v, 2, 7, 8, 13, m[12], m[13]);
        g_ref(v, 3, 4, 9, 14, m[14], m[15]);
        if (r < 6) {
            for (int i = 0; i < 16; i++) next_m[i] = m[PERM[i]];
            memcpy(m, next_m, 64);
        }
    }
    for (int i = 0; i < 8; i++) h[i] = v[i] ^ v[i + 8];
}

static uint64_t xorshift64(uint64_t *s) {
    uint64_t x = *s;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *s = x;
    return x;
}

int main(int argc, char **argv) {
#ifdef NATIVE_JIT_BIN
    if (argc < 3) { fprintf(stderr, "usage: %s text.bin entry_off\n", argv[0]); return 2; }
    g_fn = load_jit(argv[1], (size_t)strtoull(argv[2], NULL, 10));
#else
    (void)argc; (void)argv;
    g_fn = NATIVE_SYM;
#endif
    static const uint8_t empty_expect[32] = {
        0xaf, 0x13, 0x49, 0xb9, 0xf5, 0xf9, 0xa1, 0xa6,
        0xa0, 0x40, 0x4d, 0xea, 0x36, 0xdc, 0xc9, 0x49,
        0x9b, 0xcb, 0x25, 0xc9, 0xad, 0xc1, 0x12, 0xb7,
        0xcc, 0x9a, 0x93, 0xca, 0xe4, 0x1f, 0x32, 0x62,
    };
    uint32_t h[8], h_ref[8], m[16];
    memcpy(h, IV, 32);
    memset(m, 0, 64);
    g_fn(h, m, 0u, 0ull, 1u | 2u | 8u);
    if (memcmp(h, empty_expect, 32) != 0) {
        fprintf(stderr, "FAIL: official BLAKE3 empty-message vector mismatch\n");
        return 1;
    }

    int passed = 1, total = 201;
    uint64_t seed = 0xB30120261127ULL;
    for (int tc = 0; tc < 200; tc++) {
        for (int i = 0; i < 8; i++) h[i] = (uint32_t)xorshift64(&seed);
        for (int i = 0; i < 16; i++) m[i] = (uint32_t)xorshift64(&seed);
        uint32_t length = (uint32_t)(xorshift64(&seed) % 65u);
        uint64_t t = xorshift64(&seed);
        uint32_t flags = (uint32_t)(xorshift64(&seed) & 0x7Fu);
        memcpy(h_ref, h, 32);
        compress_ref(h_ref, m, length, t, flags);
        g_fn(h, m, length, t, flags);
        if (memcmp(h, h_ref, 32) != 0) {
            fprintf(stderr, "FAIL: mismatch on random test %d\n", tc);
            return 1;
        }
        passed++;
    }
    printf("NATIVE_PASS %d/%d\n", passed, total);
    return 0;
}
