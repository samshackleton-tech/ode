/* Real-silicon correctness + optional throughput harness for `ct_base64_decode`.
 * Contract ID (identical on x86_64 and arm64):
 *   5ibuszg65c23xbxdcscfcsjfpw3w3xju3hi672yvtmecj7y7e2dq
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint64_t (*ct_b64_fn)(uint8_t out[192], const uint8_t src[256], uint64_t n);

#ifdef NATIVE_JIT_BIN
#include <sys/mman.h>
#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#endif
static ct_b64_fn load_jit(const char *path, size_t entry_off) {
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
    return (ct_b64_fn)((uint8_t *)mem + entry_off);
}
#else
extern uint64_t ode_5ibuszg65c23xbxdcscfcsjfpw3w3xju3hi672yvtmecj7y7e2dq(
    uint8_t out[192], const uint8_t src[256], uint64_t n);
#define ODE_ENTRY ode_5ibuszg65c23xbxdcscfcsjfpw3w3xju3hi672yvtmecj7y7e2dq
#endif

static const char B64_ALPHABET[65] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

static uint8_t ref_b64_dec(uint8_t c) {
    if (c >= 65 && c <= 90)  return (uint8_t)(c - 1);   /* 64..89 */
    if (c >= 97 && c <= 122) return (uint8_t)(c - 7);   /* 90..115 */
    if (c >= 48 && c <= 57)  return (uint8_t)(c + 68);  /* 116..125 */
    if (c == 43)             return 126;                /* '+' */
    if (c == 47)             return 127;                /* '/' */
    return 0;
}

static uint64_t ref_b64_decode(uint8_t out[192], const uint8_t src[256]) {
    uint64_t ok = 1;
    for (int q = 0; q < 64; q++) {
        uint8_t d0 = ref_b64_dec(src[4 * q + 0]);
        uint8_t d1 = ref_b64_dec(src[4 * q + 1]);
        uint8_t d2 = ref_b64_dec(src[4 * q + 2]);
        uint8_t d3 = ref_b64_dec(src[4 * q + 3]);
        if (d0 < 64 || d1 < 64 || d2 < 64 || d3 < 64) ok = 0;
        uint8_t v0 = d0 & 63, v1 = d1 & 63, v2 = d2 & 63, v3 = d3 & 63;
        out[3 * q + 0] = (uint8_t)((v0 << 2) | (v1 >> 4));
        out[3 * q + 1] = (uint8_t)(((v1 & 15) << 4) | (v2 >> 2));
        out[3 * q + 2] = (uint8_t)(((v2 & 3) << 6) | v3);
    }
    return ok;
}

static void encode_192(uint8_t src[256], const uint8_t raw[192]) {
    for (int q = 0; q < 64; q++) {
        uint8_t b0 = raw[3 * q + 0], b1 = raw[3 * q + 1], b2 = raw[3 * q + 2];
        src[4 * q + 0] = (uint8_t)B64_ALPHABET[b0 >> 2];
        src[4 * q + 1] = (uint8_t)B64_ALPHABET[((b0 & 3) << 4) | (b1 >> 4)];
        src[4 * q + 2] = (uint8_t)B64_ALPHABET[((b1 & 15) << 2) | (b2 >> 6)];
        src[4 * q + 3] = (uint8_t)B64_ALPHABET[b2 & 63];
    }
}

static int run_case(ct_b64_fn fn, const char *label, const uint8_t src[256]) {
    uint8_t got[192], exp[192];
    memset(got, 0xA5, sizeof(got));
    uint64_t got_ok = fn(got, src, 256);
    uint64_t exp_ok = ref_b64_decode(exp, src);
    if (got_ok != exp_ok) {
        fprintf(stderr, "FAIL %s: ok got=%llu exp=%llu\n", label,
                (unsigned long long)got_ok, (unsigned long long)exp_ok);
        return 1;
    }
    if (memcmp(got, exp, 192) != 0) {
        for (int i = 0; i < 192; i++) {
            if (got[i] != exp[i]) {
                fprintf(stderr, "FAIL %s: byte %d got=0x%02x exp=0x%02x\n",
                        label, i, got[i], exp[i]);
                break;
            }
        }
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
#ifdef NATIVE_JIT_BIN
    if (argc < 3) { fprintf(stderr, "usage: %s text.bin entry_off\n", argv[0]); return 2; }
    ct_b64_fn fn = load_jit(argv[1], (size_t)strtoull(argv[2], NULL, 0));
#else
    (void)argc; (void)argv;
    ct_b64_fn fn = ODE_ENTRY;
#endif

    uint8_t src[256], raw[192];
    int total = 0, failed = 0;

    /* 1. All-zero ('AAAA...') and all-ones ('////...') */
    memset(src, 'A', 256);
    failed += run_case(fn, "all-A", src); total++;
    memset(src, '/', 256);
    failed += run_case(fn, "all-slash", src); total++;

    /* 2. All 64 alphabet characters repeated x4 (exercises every valid char at every slot mod 4) */
    for (int shift = 0; shift < 4; shift++) {
        for (int i = 0; i < 256; i++) src[i] = (uint8_t)B64_ALPHABET[(i + shift) & 63];
        failed += run_case(fn, "alphabet-rot", src); total++;
    }

    /* 3. RFC 4648 known plaintext ("foobar" repeated 32 times = 192 bytes -> "Zm9vYmFy" x32) */
    for (int i = 0; i < 192; i += 6) memcpy(raw + i, "foobar", 6);
    encode_192(src, raw);
    if (memcmp(src, "Zm9vYmFy", 8) != 0) { fprintf(stderr, "internal encode error\n"); return 2; }
    failed += run_case(fn, "rfc4648-foobar", src); total++;

    /* 4. 64 deterministic pseudo-random valid 192-byte round-trips */
    uint64_t rng = 0x9E3779B97F4A7C15ULL;
    for (int t = 0; t < 64; t++) {
        for (int i = 0; i < 192; i++) {
            rng ^= rng >> 12; rng ^= rng << 25; rng ^= rng >> 27;
            raw[i] = (uint8_t)((rng * 0x2545F4914F6CDD1DULL) >> 56);
        }
        encode_192(src, raw);
        failed += run_case(fn, "random-valid", src); total++;
    }

    /* 5. Boundary & invalid-character negative controls: EVERY byte value 0..255 placed
     *    in a valid block (tests '+', ',', '-', '.', '/', '0', '9', ':', '@', 'A', 'Z',
     *    '[', '`', 'a', 'z', '{', '=', 0, 127, 128, 255 at varied positions mod 4). */
    for (int b = 0; b < 256; b++) {
        for (int i = 0; i < 256; i++) src[i] = (uint8_t)B64_ALPHABET[(i * 7 + b) & 63];
        src[b] = (uint8_t)b;
        failed += run_case(fn, "byte-sweep", src); total++;
    }

    /* 6. Single invalid byte '=' at first, middle, and last positions (0, 1, 2, 3, 127, 255) */
    const int bad_pos[6] = {0, 1, 2, 3, 127, 255};
    for (int k = 0; k < 6; k++) {
        memset(src, 'Q', 256);
        src[bad_pos[k]] = '=';
        failed += run_case(fn, "bad-pos", src); total++;
    }

    if (failed != 0) {
        fprintf(stderr, "NATIVE_FAIL %d/%d\n", failed, total);
        return 1;
    }

#ifdef NATIVE_BENCH
    for (int i = 0; i < 256; i++) src[i] = (uint8_t)B64_ALPHABET[(i * 13 + 5) & 63];
    uint8_t out[192];
    volatile uint64_t sink = 0;
    for (int w = 0; w < 50000; w++) sink ^= fn(out, src, 256);
    double best_ns = 1e18;
    const int ITERS = 1000000;
    for (int trial = 0; trial < 9; trial++) {
        struct timespec t0, t1;
        clock_gettime(CLOCK_MONOTONIC, &t0);
        uint64_t acc = 0;
        for (int it = 0; it < ITERS; it++) {
            acc ^= fn(out, src, 256);
            src[0] = (uint8_t)B64_ALPHABET[(it + (int)acc) & 63];
        }
        clock_gettime(CLOCK_MONOTONIC, &t1);
        sink ^= acc ^ out[0];
        double ns = ((double)(t1.tv_sec - t0.tv_sec) * 1e9 + (double)(t1.tv_nsec - t0.tv_nsec)) / (double)ITERS;
        if (ns < best_ns) best_ns = ns;
    }
    double gib_s = (256.0 / best_ns) * 1e9 / (1024.0 * 1024.0 * 1024.0);
    printf("NATIVE_BENCH %.2f ns/256B (%.3f GiB/s) sink=%llu\n",
           best_ns, gib_s, (unsigned long long)sink);
#endif
    printf("NATIVE_PASS %d/%d\n", total, total);
    return 0;
}
