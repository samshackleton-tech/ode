/* Native real-silicon test harness for `der_valid`.
 * Contract ID: pyqksm2d6u3quuwvpwjwr4j4kgmgy7zlqjixoqobp2gr24sggfma
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t (*der_valid_fn)(const uint8_t *buf, uint64_t n);

#ifdef NATIVE_JIT_BIN
#include <sys/mman.h>
#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#endif
static der_valid_fn load_jit(const char *path, size_t entry_off) {
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
    return (der_valid_fn)((uint8_t *)mem + entry_off);
}
#else
extern uint64_t ode_pyqksm2d6u3quuwvpwjwr4j4kgmgy7zlqjixoqobp2gr24sggfma(const uint8_t *buf, uint64_t n);
#endif

static uint64_t ref_oid_ok(const uint8_t *buf, uint64_t i, uint64_t end) {
    uint64_t at_start = 1;
    while (i < end) {
        uint8_t b = buf[i];
        if (at_start && b == 0x80) return 0;
        at_start = (b >= 128) ? 0 : 1;
        i++;
    }
    return at_start;
}

static uint64_t ref_der_seq(const uint8_t *buf, uint64_t pos, uint64_t end, int depth) {
    while (pos < end) {
        if (pos + 2 > end) return 0;
        uint8_t tag = buf[pos];
        uint8_t l0 = buf[pos + 1];
        uint64_t hlen = 0, vlen = 0;
        if (l0 < 128) {
            hlen = 2;
            vlen = l0;
        } else if (l0 == 0x81) {
            if (pos + 3 > end || buf[pos + 2] < 128) return 0;
            hlen = 3;
            vlen = buf[pos + 2];
        } else if (l0 == 0x82) {
            if (pos + 4 > end || buf[pos + 2] < 1) return 0;
            hlen = 4;
            vlen = ((uint64_t)buf[pos + 2] << 8) | buf[pos + 3];
        } else {
            return 0;
        }
        if (pos + hlen + vlen > end) return 0;
        uint64_t vpos = pos + hlen;
        if (tag == 0x30) {
            if (depth == 0) return 0;
            if (!ref_der_seq(buf, vpos, vpos + vlen, depth - 1)) return 0;
        } else if (tag == 0x01) {
            if (vlen != 1 || (buf[vpos] != 0x00 && buf[vpos] != 0xFF)) return 0;
        } else if (tag == 0x02) {
            if (vlen == 0) return 0;
            if (vlen >= 2) {
                if (buf[vpos] == 0x00 && buf[vpos + 1] < 128) return 0;
                if (buf[vpos] == 0xFF && buf[vpos + 1] >= 128) return 0;
            }
        } else if (tag == 0x03) {
            if (vlen == 0) return 0;
            uint8_t u = buf[vpos];
            if (u > 7) return 0;
            if (vlen == 1) {
                if (u != 0) return 0;
            } else {
                uint8_t last = buf[vpos + vlen - 1];
                if ((last & ((1u << u) - 1u)) != 0) return 0;
            }
        } else if (tag == 0x04) {
            /* any bytes */
        } else if (tag == 0x05) {
            if (vlen != 0) return 0;
        } else if (tag == 0x06) {
            if (vlen == 0 || !ref_oid_ok(buf, vpos, vpos + vlen)) return 0;
        } else {
            return 0;
        }
        pos = vpos + vlen;
    }
    return pos == end ? 1 : 0;
}

static uint64_t ref_der_valid(const uint8_t *buf, uint64_t n) {
    if (n == 0) return 0;
    return ref_der_seq(buf, 0, n, 3);
}

static int g_passed = 0, g_total = 0;

static void check(der_valid_fn fn, const char *label, const uint8_t *buf, uint64_t n, uint64_t want) {
    uint64_t ref = ref_der_valid(buf, n);
    if (ref != want) {
        fprintf(stderr, "INTERNAL HARNESS MISMATCH %s: ref=%llu want=%llu\n",
                label, (unsigned long long)ref, (unsigned long long)want);
        exit(2);
    }
    g_total++;
    uint64_t got = fn(buf, n);
    if (got != want) {
        fprintf(stderr, "FAIL %s (n=%llu): got=%llu exp=%llu\n",
                label, (unsigned long long)n, (unsigned long long)got, (unsigned long long)want);
        exit(1);
    }
    g_passed++;
}

int main(int argc, char **argv) {
#ifdef NATIVE_JIT_BIN
    if (argc < 3) { fprintf(stderr, "usage: %s TEXT.bin ENTRY_OFF\n", argv[0]); return 2; }
    der_valid_fn fn = load_jit(argv[1], (size_t)strtoull(argv[2], NULL, 0));
#else
    (void)argc; (void)argv;
    der_valid_fn fn = ode_pyqksm2d6u3quuwvpwjwr4j4kgmgy7zlqjixoqobp2gr24sggfma;
#endif
    static uint8_t big[1024];
    const uint8_t empty[1] = {0};
    check(fn, "empty", empty, 0, 0);

    /* NULL */
    const uint8_t v_null[] = {0x05, 0x00};
    const uint8_t v_null_bad[] = {0x05, 0x01, 0x00};
    const uint8_t v_trunc1[] = {0x05};
    check(fn, "null_ok", v_null, sizeof(v_null), 1);
    check(fn, "null_bad_len", v_null_bad, sizeof(v_null_bad), 0);
    check(fn, "trunc1", v_trunc1, sizeof(v_trunc1), 0);

    /* BOOLEAN */
    const uint8_t v_bool0[] = {0x01, 0x01, 0x00};
    const uint8_t v_boolff[] = {0x01, 0x01, 0xFF};
    const uint8_t v_bool01[] = {0x01, 0x01, 0x01};
    const uint8_t v_bool7f[] = {0x01, 0x01, 0x7F};
    const uint8_t v_bool_len0[] = {0x01, 0x00};
    const uint8_t v_bool_len2[] = {0x01, 0x02, 0x00, 0x00};
    check(fn, "bool_false", v_bool0, sizeof(v_bool0), 1);
    check(fn, "bool_true", v_boolff, sizeof(v_boolff), 1);
    check(fn, "bool_noncanon_01", v_bool01, sizeof(v_bool01), 0);
    check(fn, "bool_noncanon_7f", v_bool7f, sizeof(v_bool7f), 0);
    check(fn, "bool_len0", v_bool_len0, sizeof(v_bool_len0), 0);
    check(fn, "bool_len2", v_bool_len2, sizeof(v_bool_len2), 0);

    /* INTEGER */
    const uint8_t v_int0[] = {0x02, 0x01, 0x00};
    const uint8_t v_intm1[] = {0x02, 0x01, 0xFF};
    const uint8_t v_int128[] = {0x02, 0x02, 0x00, 0x80};
    const uint8_t v_int_badpos[] = {0x02, 0x02, 0x00, 0x7F};
    const uint8_t v_int_neg129[] = {0x02, 0x02, 0xFF, 0x7F};
    const uint8_t v_int_badneg[] = {0x02, 0x02, 0xFF, 0x80};
    const uint8_t v_int_len0[] = {0x02, 0x00};
    check(fn, "int_0", v_int0, sizeof(v_int0), 1);
    check(fn, "int_m1", v_intm1, sizeof(v_intm1), 1);
    check(fn, "int_128", v_int128, sizeof(v_int128), 1);
    check(fn, "int_bad_pos", v_int_badpos, sizeof(v_int_badpos), 0);
    check(fn, "int_neg129", v_int_neg129, sizeof(v_int_neg129), 1);
    check(fn, "int_bad_neg", v_int_badneg, sizeof(v_int_badneg), 0);
    check(fn, "int_len0", v_int_len0, sizeof(v_int_len0), 0);

    /* BIT STRING across all u = 0..8 */
    const uint8_t v_bs_empty_ok[] = {0x03, 0x01, 0x00};
    const uint8_t v_bs_empty_bad[] = {0x03, 0x01, 0x01};
    const uint8_t v_bs_len0[] = {0x03, 0x00};
    check(fn, "bs_empty_ok", v_bs_empty_ok, sizeof(v_bs_empty_ok), 1);
    check(fn, "bs_empty_bad", v_bs_empty_bad, sizeof(v_bs_empty_bad), 0);
    check(fn, "bs_len0", v_bs_len0, sizeof(v_bs_len0), 0);
    for (unsigned u = 0; u <= 7; u++) {
        uint8_t ok_b[4] = {0x03, 0x02, (uint8_t)u, (uint8_t)(0xFFu << u)};
        check(fn, "bs_u_ok", ok_b, 4, 1);
        if (u > 0) {
            uint8_t bad_b[4] = {0x03, 0x02, (uint8_t)u, (uint8_t)((0xFFu << u) | (1u << (u - 1)))};
            check(fn, "bs_u_bad", bad_b, 4, 0);
        }
    }
    const uint8_t v_bs_u8[] = {0x03, 0x02, 0x08, 0x00};
    check(fn, "bs_u8", v_bs_u8, sizeof(v_bs_u8), 0);

    /* OID */
    const uint8_t v_oid_sha256[] = {0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01};
    const uint8_t v_oid_lead80[] = {0x06, 0x02, 0x80, 0x01};
    const uint8_t v_oid_mid80[] = {0x06, 0x03, 0x2A, 0x80, 0x01};
    const uint8_t v_oid_trunc[] = {0x06, 0x02, 0x60, 0x86};
    const uint8_t v_oid_empty[] = {0x06, 0x00};
    check(fn, "oid_sha256", v_oid_sha256, sizeof(v_oid_sha256), 1);
    check(fn, "oid_lead80", v_oid_lead80, sizeof(v_oid_lead80), 0);
    check(fn, "oid_mid80", v_oid_mid80, sizeof(v_oid_mid80), 0);
    check(fn, "oid_trunc", v_oid_trunc, sizeof(v_oid_trunc), 0);
    check(fn, "oid_empty", v_oid_empty, sizeof(v_oid_empty), 0);

    /* Long lengths: 0x80 indefinite, 0x81 canonical & non-canonical, 0x82 canonical & non-canonical, 0x83 reject */
    const uint8_t v_indef[] = {0x04, 0x80, 0x00, 0x00};
    const uint8_t v_len83[] = {0x04, 0x83, 0x01, 0x00, 0x00};
    check(fn, "len_indef", v_indef, sizeof(v_indef), 0);
    check(fn, "len_83", v_len83, sizeof(v_len83), 0);

    memset(big, 0xAA, sizeof(big));
    big[0] = 0x04; big[1] = 0x81; big[2] = 0x7F;
    check(fn, "len81_noncanon", big, 3 + 0x7F, 0);
    big[2] = 0x80;
    check(fn, "len81_ok", big, 3 + 0x80, 1);
    check(fn, "len81_trunc", big, 3 + 0x7F, 0);
    big[1] = 0x82; big[2] = 0x00; big[3] = 0xFF;
    check(fn, "len82_noncanon", big, 4 + 0xFF, 0);
    big[2] = 0x01; big[3] = 0x00;
    check(fn, "len82_ok", big, 4 + 0x100, 1);
    check(fn, "len82_trunc", big, 4 + 0xFF, 0);

    /* Nested SEQUENCEs: depth 1, 2, 3 valid; depth 4 rejected; X.509-like nested structure */
    const uint8_t v_seq_empty[] = {0x30, 0x00};
    const uint8_t v_seq_d1[] = {0x30, 0x02, 0x05, 0x00};
    const uint8_t v_seq_d2[] = {0x30, 0x04, 0x30, 0x02, 0x05, 0x00};
    const uint8_t v_seq_d3[] = {0x30, 0x06, 0x30, 0x04, 0x30, 0x02, 0x05, 0x00};
    const uint8_t v_seq_d4[] = {0x30, 0x08, 0x30, 0x06, 0x30, 0x04, 0x30, 0x02, 0x05, 0x00};
    const uint8_t v_x509[] = {
        0x30, 0x21,
          0x30, 0x15,
            0x02, 0x01, 0x02,
            0x30, 0x0D,
              0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01,
              0x05, 0x00,
            0x01, 0x01, 0xFF,
          0x03, 0x04, 0x02, 0xAB, 0xCD, 0xFC,
          0x04, 0x02, 0xDE, 0xAD
    };
    const uint8_t v_x509_bad_inner[] = {
        0x30, 0x21,
          0x30, 0x15,
            0x02, 0x01, 0x02,
            0x30, 0x0D,
              0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01,
              0x05, 0x00,
            0x01, 0x01, 0x01, /* non-canonical BOOLEAN inside nested SEQUENCE */
          0x03, 0x04, 0x02, 0xAB, 0xCD, 0xFC,
          0x04, 0x02, 0xDE, 0xAD
    };
    const uint8_t v_unknown_tag[] = {0x31, 0x00};
    check(fn, "seq_empty", v_seq_empty, sizeof(v_seq_empty), 1);
    check(fn, "seq_d1", v_seq_d1, sizeof(v_seq_d1), 1);
    check(fn, "seq_d2", v_seq_d2, sizeof(v_seq_d2), 1);
    check(fn, "seq_d3", v_seq_d3, sizeof(v_seq_d3), 1);
    check(fn, "seq_d4_reject", v_seq_d4, sizeof(v_seq_d4), 0);
    check(fn, "x509_nested", v_x509, sizeof(v_x509), 1);
    check(fn, "x509_bad_inner", v_x509_bad_inner, sizeof(v_x509_bad_inner), 0);
    check(fn, "unknown_tag", v_unknown_tag, sizeof(v_unknown_tag), 0);

    /* Differential fuzz: 200 mutated variants of v_x509 */
    uint8_t mut[sizeof(v_x509)];
    uint64_t rng = 0x517cc1b727220a95ULL;
    for (int t = 0; t < 200; t++) {
        memcpy(mut, v_x509, sizeof(v_x509));
        rng ^= rng >> 12; rng ^= rng << 25; rng ^= rng >> 27;
        uint64_t h = rng * 2685821657736338717ULL;
        size_t idx = (size_t)(h % sizeof(v_x509));
        mut[idx] ^= (uint8_t)(1u << ((h >> 16) & 7u));
        size_t n = sizeof(v_x509) - (size_t)((h >> 24) % 4u);
        check(fn, "fuzz_x509", mut, n, ref_der_valid(mut, n));
    }

    printf("NATIVE_PASS %d/%d\n", g_passed, g_total);
    return 0;
}
