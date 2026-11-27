/* Native hardware test harness for verified constant-time big-endian byte-slice `<`. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t (*ct_lt_fn_t)(const uint8_t *a, const uint8_t *b, uint64_t n);

#ifdef NATIVE_JIT_BIN
#include <pthread.h>
#include <sys/mman.h>
#include <unistd.h>
#include <libkern/OSCacheControl.h>

static ct_lt_fn_t load_jit_fn(const char *path, size_t entry_off, void **out_buf, size_t *out_sz) {
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
    void *mem = mmap(NULL, map_sz, PROT_READ | PROT_WRITE | PROT_EXEC,
                     MAP_PRIVATE | MAP_ANON | MAP_JIT, -1, 0);
    if (mem == MAP_FAILED) { perror("mmap"); exit(2); }
    pthread_jit_write_protect_np(0);
    memcpy(mem, tmp, (size_t)sz);
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(mem, (size_t)sz);
    free(tmp);
    *out_buf = mem;
    *out_sz = map_sz;
    return (ct_lt_fn_t)((uint8_t *)mem + entry_off);
}
#else
extern uint64_t ode_z5mi7h56f2qwr2uqti72jtovd26jpjh3e2ue7vw2l5v5vwxudzna(
    const uint8_t *a, const uint8_t *b, uint64_t n);
#endif

static int check_case(ct_lt_fn_t fn, const char *name, const uint8_t *a, const uint8_t *b, size_t n, uint64_t want) {
    uint64_t got = fn(a, b, (uint64_t)n);
    if (got != want) {
        fprintf(stderr, "FAIL %s: got=%llu want=%llu\n", name, (unsigned long long)got, (unsigned long long)want);
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    ct_lt_fn_t fn = NULL;
#ifdef NATIVE_JIT_BIN
    void *buf = NULL;
    size_t map_sz = 0;
    if (argc != 3) { fprintf(stderr, "usage: %s text.bin entry_off\n", argv[0]); return 2; }
    fn = load_jit_fn(argv[1], (size_t)strtoull(argv[2], NULL, 0), &buf, &map_sz);
#else
    (void)argc; (void)argv;
    fn = ode_z5mi7h56f2qwr2uqti72jtovd26jpjh3e2ue7vw2l5v5vwxudzna;
#endif
    int fails = 0;
    uint8_t z[4] = {0, 0, 0, 0};
    uint8_t u1[2] = {1, 255};
    uint8_t u2[2] = {2, 0};
    uint8_t u3[3] = {1, 5, 9};
    uint8_t u4[3] = {1, 5, 10};
    /* Curve25519 field prime p = 2^255 - 19 in big-endian */
    uint8_t p[32], p_minus1[32], p_plus1[32];
    memset(p, 0xff, 32);
    p[0] = 0x7f;
    p[31] = 0xed;
    memcpy(p_minus1, p, 32); p_minus1[31] = 0xec;
    memcpy(p_plus1, p, 32);  p_plus1[31] = 0xee;

    fails += check_case(fn, "empty", z, z, 0, 0);
    fails += check_case(fn, "eq_zero", z, z, 4, 0);
    fails += check_case(fn, "msb_lt_lsb_gt", u1, u2, 2, 1);
    fails += check_case(fn, "msb_gt_lsb_lt", u2, u1, 2, 0);
    fails += check_case(fn, "last_byte_lt", u3, u4, 3, 1);
    fails += check_case(fn, "last_byte_gt", u4, u3, 3, 0);
    fails += check_case(fn, "p25519_lt", p_minus1, p, 32, 1);
    fails += check_case(fn, "p25519_eq", p, p, 32, 0);
    fails += check_case(fn, "p25519_gt", p_plus1, p, 32, 0);

#ifdef NATIVE_JIT_BIN
    munmap(buf, map_sz);
#endif
    if (fails == 0) {
        printf("NATIVE_PASS 9/9\n");
        return 0;
    }
    return 1;
}
