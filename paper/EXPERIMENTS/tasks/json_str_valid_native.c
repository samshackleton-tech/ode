#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t (*json_fn)(const uint8_t *src, uint64_t n);
static json_fn g_fn = NULL;

#ifdef NATIVE_JIT_BIN
#include <sys/mman.h>
#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#endif
static json_fn load_jit(const char *path, size_t entry_off) {
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
    return (json_fn)((uint8_t *)mem + entry_off);
}
#else
extern uint64_t ode_4totxwdumkxnrfw5zgsfvw54fmy24uvfzvgtjkvn2u77hkoetyma(
    const uint8_t *src, uint64_t n);
#endif

#define FN g_fn

static int ref_is_hex(uint8_t c) {
    return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'F') || (c >= 'a' && c <= 'f');
}

static int ref_is_simple_esc(uint8_t c) {
    return c == '"' || c == '\\' || c == '/' || c == 'b' ||
           c == 'f' || c == 'n' || c == 'r' || c == 't';
}

static uint64_t ref_json_str_valid(const uint8_t *src, uint64_t n) {
    if (n < 2) return 0;
    if (src[0] != '"' || src[n - 1] != '"') return 0;
    uint64_t i = 1, end = n - 1;
    while (i < end) {
        uint8_t c = src[i];
        if (c == '\\') {
            if (i + 1 >= end) return 0;
            uint8_t e = src[i + 1];
            if (ref_is_simple_esc(e)) {
                i += 2;
            } else if (e == 'u') {
                if (i + 5 >= end) return 0;
                if (!ref_is_hex(src[i + 2]) || !ref_is_hex(src[i + 3]) ||
                    !ref_is_hex(src[i + 4]) || !ref_is_hex(src[i + 5]))
                    return 0;
                i += 6;
            } else {
                return 0;
            }
        } else if (c < 32 || c == '"' || c > 126) {
            return 0;
        } else {
            i += 1;
        }
    }
    return 1;
}

static uint64_t rng = 0x123456789abcdef0ULL;
static uint64_t xorshift(void) {
    uint64_t x = rng;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rng = x;
    return x;
}

static int total = 0;

static void check(const char *label, const uint8_t *buf, uint64_t n) {
    uint64_t exp = ref_json_str_valid(buf, n);
    uint64_t got = FN(buf, n);
    total++;
    if (got != exp) {
        fprintf(stderr, "FAIL %s (n=%llu): got=%llu exp=%llu\n",
                label, (unsigned long long)n, (unsigned long long)got, (unsigned long long)exp);
        exit(1);
    }
}

static void check_str(const char *label, const char *s) {
    check(label, (const uint8_t *)s, (uint64_t)strlen(s));
}

#ifdef NATIVE_BENCH
#include <time.h>
static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}
#endif

int main(int argc, char **argv) {
#ifdef NATIVE_JIT_BIN
    if (argc < 3) { fprintf(stderr, "usage: %s text.bin entry_off\n", argv[0]); return 2; }
    g_fn = load_jit(argv[1], (size_t)strtoull(argv[2], NULL, 10));
#else
    (void)argc; (void)argv;
    g_fn = ode_4totxwdumkxnrfw5zgsfvw54fmy24uvfzvgtjkvn2u77hkoetyma;
#endif
    // 1. Boundary & structural edge cases
    check("empty", (const uint8_t *)"", 0);
    check_str("one_quote", "\"");
    check_str("empty_json", "\"\"");
    check_str("plain_ascii", "\"hello, world! 0123456789 ~!@#$%^&*()_+-=[]{}|;:',.<>?/\"");
    check_str("no_open", "hello\"");
    check_str("no_close", "\"hello");
    check_str("unescaped_mid_quote", "\"ab\"cd\"");
    check_str("trailing_backslash", "\"abc\\\"");
    check_str("escaped_backslash_end", "\"abc\\\\\"");
    check_str("all_simple_escapes", "\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"");
    check_str("all_hex_digits", "\"\\u0123\\u4567\\u89AB\\uCDEF\\uabcd\\uef09\"");

    // 2. Every single byte value as solo interior char (0..255)
    for (int b = 0; b < 256; b++) {
        uint8_t buf[3] = {'"', (uint8_t)b, '"'};
        char lbl[32];
        snprintf(lbl, sizeof(lbl), "solo_%02x", b);
        check(lbl, buf, 3);
    }

    // 3. Every single byte value after backslash `\<c>` (0..255)
    for (int b = 0; b < 256; b++) {
        uint8_t buf[4] = {'"', '\\', (uint8_t)b, '"'};
        char lbl[32];
        snprintf(lbl, sizeof(lbl), "esc_%02x", b);
        check(lbl, buf, 4);
    }

    // 4. Every byte value in each of the 4 hex positions of `\uXXXX`
    const int boundary_chars[] = {
        0, 31, 32, '/', '0', '9', ':', '@', 'A', 'F', 'G', '`', 'a', 'f', 'g', 126, 127, 255
    };
    size_t nbc = sizeof(boundary_chars) / sizeof(boundary_chars[0]);
    for (int pos = 0; pos < 4; pos++) {
        for (size_t k = 0; k < nbc; k++) {
            uint8_t buf[8] = {'"', '\\', 'u', '0', 'a', 'F', '9', '"'};
            buf[3 + pos] = (uint8_t)boundary_chars[k];
            char lbl[32];
            snprintf(lbl, sizeof(lbl), "u_pos%d_%02x", pos, boundary_chars[k]);
            check(lbl, buf, 8);
        }
    }

    // 5. Truncated `\u` escapes of lengths 0..3 hex digits
    check_str("u_trunc0", "\"\\u\"");
    check_str("u_trunc1", "\"\\u1\"");
    check_str("u_trunc2", "\"\\u12\"");
    check_str("u_trunc3", "\"\\u123\"");
    check_str("u_ok4", "\"\\u1234\"");

    // 6. Randomized realistic valid & single-byte-mutated JSON strings up to 4096 B
    static uint8_t buf[4096];
    const char *simple_escs = "\"\\/bfnrt";
    const char *hex_chars = "0123456789ABCDEFabcdef";
    for (int trial = 0; trial < 40; trial++) {
        uint64_t target = 16 + (xorshift() % 3800);
        buf[0] = '"';
        uint64_t pos = 1;
        while (pos + 8 < target) {
            uint64_t r = xorshift() % 20;
            if (r == 0) {
                buf[pos++] = '\\';
                buf[pos++] = (uint8_t)simple_escs[xorshift() % 8];
            } else if (r == 1) {
                buf[pos++] = '\\';
                buf[pos++] = 'u';
                for (int h = 0; h < 4; h++)
                    buf[pos++] = (uint8_t)hex_chars[xorshift() % 22];
            } else {
                uint8_t c;
                do { c = (uint8_t)(32 + (xorshift() % 95)); } while (c == '"' || c == '\\');
                buf[pos++] = c;
            }
        }
        buf[pos++] = '"';
        check("rand_valid", buf, pos);
        // Single-byte corruption at a random interior index
        uint64_t m = 1 + (xorshift() % (pos - 2));
        uint8_t orig = buf[m];
        buf[m] = (trial & 1) ? 0x07 : '"';
        check("rand_mut", buf, pos);
        buf[m] = orig;
    }

    // 7. Max length 4096 bytes all-plain valid string
    buf[0] = '"';
    for (int i = 1; i < 4095; i++) buf[i] = 'a' + (i % 26);
    buf[4095] = '"';
    check("max_4096", buf, 4096);

    printf("NATIVE_PASS %d/%d\n", total, total);

#ifdef NATIVE_BENCH
    // Benchmark two realistic workloads (all valid so the full string is scanned):
    //   - plain 512 B JSON string (typical API string / URL / identifier)
    //   - mixed 512 B JSON string (~4% escapes: \", \n, \\, \u0041)
    static uint8_t plain[512];
    static uint8_t mixed[512];
    plain[0] = '"';
    for (int i = 1; i < 511; i++) {
        uint8_t c = (uint8_t)(32 + ((i * 37 + 11) % 95));
        if (c == '"' || c == '\\') c = 'x';
        plain[i] = c;
    }
    plain[511] = '"';

    mixed[0] = '"';
    int p = 1;
    while (p < 511) {
        if (p % 64 == 10 && p + 6 < 511) {
            memcpy(mixed + p, "\\u0041", 6);
            p += 6;
        } else if (p % 29 == 5 && p + 2 < 511) {
            uint8_t esc = (p & 1) ? 'n' : '"';
            mixed[p++] = '\\';
            mixed[p++] = esc;
        } else {
            uint8_t c = (uint8_t)(32 + ((p * 29 + 7) % 95));
            if (c == '"' || c == '\\') c = 'y';
            mixed[p++] = c;
        }
    }
    mixed[511] = '"';
    if (FN(plain, 512) != 1 || FN(mixed, 512) != 1) {
        fprintf(stderr, "bench vector invalid\n");
        return 1;
    }

    const int ITERS = 400000;
    volatile uint64_t sink = 0;
    // Warmup
    for (int i = 0; i < 10000; i++) sink += FN(plain, 512) + FN(mixed, 512);

    uint64_t best_plain = ~0ULL, best_mixed = ~0ULL;
    for (int r = 0; r < 5; r++) {
        uint64_t t0 = now_ns();
        for (int i = 0; i < ITERS; i++) sink += FN(plain, 512);
        uint64_t dt = now_ns() - t0;
        if (dt < best_plain) best_plain = dt;

        uint64_t t1 = now_ns();
        for (int i = 0; i < ITERS; i++) sink += FN(mixed, 512);
        uint64_t dt1 = now_ns() - t1;
        if (dt1 < best_mixed) best_mixed = dt1;
    }
    double ns_plain = (double)best_plain / (double)ITERS;
    double ns_mixed = (double)best_mixed / (double)ITERS;
    double gib_plain = (512.0 / ns_plain) * (1e9 / (1024.0 * 1024.0 * 1024.0));
    double gib_mixed = (512.0 / ns_mixed) * (1e9 / (1024.0 * 1024.0 * 1024.0));
    printf("BENCH_512B plain=%.2f ns (%.3f GiB/s) mixed=%.2f ns (%.3f GiB/s) sink=%llu\n",
           ns_plain, gib_plain, ns_mixed, gib_mixed, (unsigned long long)sink);
#endif
    return 0;
}
