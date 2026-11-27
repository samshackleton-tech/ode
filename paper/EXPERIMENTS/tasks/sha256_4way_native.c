/* Native real-silicon test harness (+ optional NATIVE_BENCH timing) for `sha256_4way`.
 * Contract IDs:
 *   arm64:  o3hgxtczokkzp7r2eaybjvdgc4cyrny6vawtweqxrzmxu32hrswa
 *   x86_64: 2wohv4skh4liyco6pegmuwcvelhqew4xgp7gbki4hrg44azweuda
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef void (*sha256_4way_fn)(uint32_t out[32], const uint32_t state[32], const uint32_t blocks[64], const uint32_t k[64]);

#ifdef NATIVE_JIT_BIN
#include <sys/mman.h>
#include <unistd.h>
#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#endif
static sha256_4way_fn load_jit(const char *path, size_t entry_off) {
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
    return (sha256_4way_fn)((uint8_t *)mem + entry_off);
}
#else
#if defined(__aarch64__)
extern void ode_o3hgxtczokkzp7r2eaybjvdgc4cyrny6vawtweqxrzmxu32hrswa(uint32_t out[32], const uint32_t state[32], const uint32_t blocks[64], const uint32_t k[64]);
#define ODE_ENTRY ode_o3hgxtczokkzp7r2eaybjvdgc4cyrny6vawtweqxrzmxu32hrswa
#else
extern void ode_2wohv4skh4liyco6pegmuwcvelhqew4xgp7gbki4hrg44azweuda(uint32_t out[32], const uint32_t state[32], const uint32_t blocks[64], const uint32_t k[64]);
#define ODE_ENTRY ode_2wohv4skh4liyco6pegmuwcvelhqew4xgp7gbki4hrg44azweuda
#endif
#endif

static const uint32_t SHA256_IV[8] = {
    0x6a09e667u, 0xbb67ae85u, 0x3c6ef372u, 0xa54ff53au,
    0x510e527fu, 0x9b05688cu, 0x1f83d9abu, 0x5be0cd19u
};

static const uint32_t SHA256_K[64] = {
    0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u,
    0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
    0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u,
    0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
    0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu,
    0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
    0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u,
    0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
    0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u,
    0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
    0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u,
    0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
    0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u,
    0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
    0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
    0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u
};

static inline uint32_t rotr32(uint32_t x, unsigned n) {
    return (x >> n) | (x << (32 - n));
}

static void ref_sha256_compress(uint32_t out[8], const uint32_t h[8], const uint32_t m[16], const uint32_t k[64]) {
    uint32_t w[64];
    for (int i = 0; i < 16; i++) w[i] = m[i];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = rotr32(w[i - 15], 7) ^ rotr32(w[i - 15], 18) ^ (w[i - 15] >> 3);
        uint32_t s1 = rotr32(w[i - 2], 17) ^ rotr32(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }
    uint32_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
    for (int t = 0; t < 64; t++) {
        uint32_t S1 = rotr32(e, 6) ^ rotr32(e, 11) ^ rotr32(e, 25);
        uint32_t ch = g ^ (e & (f ^ g));
        uint32_t t1 = hh + S1 + ch + k[t] + w[t];
        uint32_t S0 = rotr32(a, 2) ^ rotr32(a, 13) ^ rotr32(a, 22);
        uint32_t maj = (a & b) ^ ((a ^ b) & c);
        uint32_t t2 = S0 + maj;
        hh = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    out[0] = h[0] + a; out[1] = h[1] + b; out[2] = h[2] + c; out[3] = h[3] + d;
    out[4] = h[4] + e; out[5] = h[5] + f; out[6] = h[6] + g; out[7] = h[7] + hh;
}

static void fill_msg_block(uint32_t w[16], const char *s) {
    uint8_t b[64];
    memset(b, 0, 64);
    size_t n = strlen(s);
    memcpy(b, s, n);
    b[n] = 0x80;
    uint64_t bits = (uint64_t)n * 8;
    for (int i = 0; i < 8; i++) b[63 - i] = (uint8_t)(bits >> (8 * i));
    for (int i = 0; i < 16; i++)
        w[i] = ((uint32_t)b[4*i] << 24) | ((uint32_t)b[4*i+1] << 16) | ((uint32_t)b[4*i+2] << 8) | b[4*i+3];
}

int main(int argc, char **argv) {
#ifdef NATIVE_JIT_BIN
    if (argc < 3) { fprintf(stderr, "usage: %s text.bin entry_off\n", argv[0]); return 2; }
    sha256_4way_fn target = load_jit(argv[1], (size_t)strtoull(argv[2], NULL, 0));
#else
    (void)argc; (void)argv;
    sha256_4way_fn target = ODE_ENTRY;
#endif
    int total = 0, passed = 0;

    /* 1. Official NIST FIPS 180-4 single-block vectors in parallel across the 4 lanes */
    uint32_t st[32], blk[64], got[32], want[32];
    for (int lane = 0; lane < 4; lane++) memcpy(&st[lane * 8], SHA256_IV, 32);
    fill_msg_block(&blk[0], "");
    fill_msg_block(&blk[16], "abc");
    fill_msg_block(&blk[32], "The quick brown fox jumps over the lazy dog");
    fill_msg_block(&blk[48], "The quick brown fox jumps over the lazy dog.");

    target(got, st, blk, SHA256_K);
    const uint32_t nist_empty[8] = {0xe3b0c442u,0x98fc1c14u,0x9afbf4c8u,0x996fb924u,0x27ae41e4u,0x649b934cu,0xa495991bu,0x7852b855u};
    const uint32_t nist_abc[8]   = {0xba7816bfu,0x8f01cfeau,0x414140deu,0x5dae2223u,0xb00361a3u,0x96177a9cu,0xb410ff61u,0xf20015adu};
    const uint32_t nist_fox[8]   = {0xd7a8fbb3u,0x07d78094u,0x69ca9abcu,0xb0082e4fu,0x8d5651e4u,0x6d3cdb76u,0x2d02d0bfu,0x37c9e592u};
    const uint32_t nist_fox2[8]  = {0xef537f25u,0xc895bfa7u,0x82526529u,0xa9b63d97u,0xaa631564u,0xd5d789c2u,0xb765448cu,0x8635fb6cu};
    const uint32_t *nists[4] = {nist_empty, nist_abc, nist_fox, nist_fox2};
    for (int lane = 0; lane < 4; lane++) {
        total++;
        if (memcmp(&got[lane * 8], nists[lane], 32) == 0) passed++;
        else { printf("FAIL nist lane %d\n", lane); return 1; }
    }

    /* 2. Multi-block NIST vector ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") */
    uint8_t mb[128];
    memset(mb, 0, sizeof(mb));
    const char *s2 = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    memcpy(mb, s2, 56);
    mb[56] = 0x80;
    mb[126] = (uint8_t)((56 * 8) >> 8);
    mb[127] = (uint8_t)((56 * 8) & 0xff);
    for (int lane = 0; lane < 4; lane++) {
        memcpy(&st[lane * 8], SHA256_IV, 32);
        for (int i = 0; i < 16; i++)
            blk[lane * 16 + i] = ((uint32_t)mb[4*i]<<24)|((uint32_t)mb[4*i+1]<<16)|((uint32_t)mb[4*i+2]<<8)|mb[4*i+3];
    }
    target(got, st, blk, SHA256_K);
    memcpy(st, got, sizeof(st));
    for (int lane = 0; lane < 4; lane++) {
        for (int i = 0; i < 16; i++)
            blk[lane * 16 + i] = ((uint32_t)mb[64+4*i]<<24)|((uint32_t)mb[64+4*i+1]<<16)|((uint32_t)mb[64+4*i+2]<<8)|mb[64+4*i+3];
    }
    target(got, st, blk, SHA256_K);
    const uint32_t nist_2blk[8] = {0x248d6a61u,0xd20638b8u,0xe5c02693u,0x0c3e6039u,0xa33ce459u,0x64ff2167u,0xf6ecedd4u,0x19db06c1u};
    for (int lane = 0; lane < 4; lane++) {
        total++;
        if (memcmp(&got[lane * 8], nist_2blk, 32) == 0) passed++;
        else { printf("FAIL nist 2-block lane %d\n", lane); return 1; }
    }

    /* 3. 64 pseudorandom 4-way batches (256 independent blocks, including custom K on odd trials) */
    uint64_t rng = 0x9e3779b97f4a7c15ULL;
    uint32_t custom_k[64];
    for (int trial = 0; trial < 64; trial++) {
        for (int i = 0; i < 32; i++) { rng = rng * 6364136223846793005ULL + 1442695040888963407ULL; st[i] = (uint32_t)(rng >> 32); }
        for (int i = 0; i < 64; i++) { rng = rng * 6364136223846793005ULL + 1442695040888963407ULL; blk[i] = (uint32_t)(rng >> 32); }
        const uint32_t *kp = SHA256_K;
        if (trial & 1) {
            for (int i = 0; i < 64; i++) { rng = rng * 6364136223846793005ULL + 1442695040888963407ULL; custom_k[i] = (uint32_t)(rng >> 32); }
            kp = custom_k;
        }
        target(got, st, blk, kp);
        for (int lane = 0; lane < 4; lane++) {
            ref_sha256_compress(&want[lane * 8], &st[lane * 8], &blk[lane * 16], kp);
            total++;
            if (memcmp(&got[lane * 8], &want[lane * 8], 32) == 0) passed++;
            else { printf("FAIL random trial %d lane %d\n", trial, lane); return 1; }
        }
    }

    printf("NATIVE_PASS %d/%d\n", passed, total);

#ifdef NATIVE_BENCH
    for (int lane = 0; lane < 4; lane++) memcpy(&st[lane * 8], SHA256_IV, 32);
    for (int i = 0; i < 64; i++) blk[i] = (uint32_t)(i * 0x01010101u + 0x12345678u);
    for (int w = 0; w < 20000; w++) target(got, st, blk, SHA256_K);
    const int iters = 1000000;
    double best_ns = 1e9;
    volatile uint32_t sink = 0;
    for (int r = 0; r < 7; r++) {
        struct timespec t0, t1;
        clock_gettime(CLOCK_MONOTONIC, &t0);
        for (int i = 0; i < iters; i++) {
            target(got, st, blk, SHA256_K);
            blk[0] ^= got[0];
        }
        clock_gettime(CLOCK_MONOTONIC, &t1);
        sink ^= got[0];
        double ns = ((t1.tv_sec - t0.tv_sec) * 1e9 + (t1.tv_nsec - t0.tv_nsec)) / (double)iters;
        if (ns < best_ns) best_ns = ns;
    }
    double gib_s = (256.0 / best_ns) * 1e9 / (1024.0 * 1024.0 * 1024.0);
    printf("NATIVE_BENCH 4x64B=%.2fns %.3fGiB/s sink=%u\n", best_ns, gib_s, (unsigned)sink);
#endif
    return 0;
}
