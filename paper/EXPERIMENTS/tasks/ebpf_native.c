/* Native hardware test harness for verified RFC 9669 eBPF bundles.
 *
 * Mode 1 (ELF64 x86-64 Linux, link directly against candidate .o):
 *   cc -O2 ebpf_native.c candidate.o -o run_test && ./run_test
 *
 * Mode 2 (Apple Silicon macOS AArch64, raw .text bytes + entry offset):
 *   cc -O2 -DNATIVE_JIT_BIN ebpf_native.c -o run_test && ./run_test text.bin ENTRY_OFF
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t (*ebpf_fn_t)(const uint8_t *prog, uint64_t n, uint64_t fuel, uint64_t arg1);

#ifdef NATIVE_JIT_BIN
#include <pthread.h>
#include <sys/mman.h>
#include <unistd.h>
#include <libkern/OSCacheControl.h>

static ebpf_fn_t load_jit_fn(const char *path, size_t entry_off, void **out_buf, size_t *out_sz) {
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
    return (ebpf_fn_t)((uint8_t *)mem + entry_off);
}
#else
extern uint64_t ode_d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa(
    const uint8_t *prog, uint64_t n, uint64_t fuel, uint64_t arg1);
#endif

static void insn(uint8_t *p, uint8_t op, uint8_t regs, int16_t off, uint32_t imm) {
    uint16_t uoff = (uint16_t)off;
    p[0] = op;
    p[1] = regs;
    p[2] = (uint8_t)(uoff & 0xff);
    p[3] = (uint8_t)(uoff >> 8);
    p[4] = (uint8_t)(imm & 0xff);
    p[5] = (uint8_t)((imm >> 8) & 0xff);
    p[6] = (uint8_t)((imm >> 16) & 0xff);
    p[7] = (uint8_t)((imm >> 24) & 0xff);
}

int main(int argc, char **argv) {
    ebpf_fn_t fn = NULL;
#ifdef NATIVE_JIT_BIN
    void *buf = NULL;
    size_t map_sz = 0;
    if (argc != 3) { fprintf(stderr, "usage: %s text.bin entry_off\n", argv[0]); return 2; }
    fn = load_jit_fn(argv[1], (size_t)strtoull(argv[2], NULL, 0), &buf, &map_sz);
#else
    (void)argc; (void)argv;
    fn = ode_d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa;
#endif
    const uint64_t ERR = 4294967296ULL;
    int fails = 0;

    /* 1. MOV32 r0, 10; ADD32 r0, r1; EXIT with arg1=32 -> 42 */
    uint8_t p1[24];
    insn(p1 + 0,  0xb7, 0x00, 0, 10);
    insn(p1 + 8,  0x0f, 0x10, 0, 0);
    insn(p1 + 16, 0x95, 0x00, 0, 0);
    uint64_t g1 = fn(p1, sizeof(p1), 16, 32);
    if (g1 != 42) { fprintf(stderr, "FAIL t1: got %llu want 42\n", (unsigned long long)g1); fails++; }

    /* 2. Countdown sum: sum(1..10) = 55 */
    uint8_t p2[48];
    insn(p2 + 0,  0xb7, 0x00, 0, 0);      /* r0 = 0 */
    insn(p2 + 8,  0x15, 0x01, 3, 0);      /* if r1 == 0 goto EXIT (+3 -> pc=5) */
    insn(p2 + 16, 0x0f, 0x10, 0, 0);      /* r0 += r1 */
    insn(p2 + 24, 0x17, 0x01, 0, 1);      /* r1 -= 1 */
    insn(p2 + 32, 0x05, 0x00, -4, 0);     /* goto pc=1 */
    insn(p2 + 40, 0x95, 0x00, 0, 0);      /* EXIT */
    uint64_t g2 = fn(p2, sizeof(p2), 100, 10);
    if (g2 != 55) { fprintf(stderr, "FAIL t2: got %llu want 55\n", (unsigned long long)g2); fails++; }

    /* 3. Invalid opcode -> ERR */
    uint8_t p3[8];
    insn(p3, 0xfe, 0x00, 0, 0);
    uint64_t g3 = fn(p3, sizeof(p3), 10, 0);
    if (g3 != ERR) { fprintf(stderr, "FAIL t3: got %llu want ERR\n", (unsigned long long)g3); fails++; }

    /* 4. Backward jump underflow -> ERR */
    uint8_t p4[8];
    insn(p4, 0x05, 0x00, -5, 0);
    uint64_t g4 = fn(p4, sizeof(p4), 10, 0);
    if (g4 != ERR) { fprintf(stderr, "FAIL t4: got %llu want ERR\n", (unsigned long long)g4); fails++; }

    /* 5. Fuel exhausted -> ERR */
    uint64_t g5 = fn(p1, sizeof(p1), 0, 32);
    if (g5 != ERR) { fprintf(stderr, "FAIL t5: got %llu want ERR\n", (unsigned long long)g5); fails++; }

    /* 6. 32-bit wrap on SUB32 (0 - 1 mod 2^32 = 0xffffffff) */
    uint8_t p6[24];
    insn(p6 + 0,  0xb7, 0x00, 0, 0);
    insn(p6 + 8,  0x17, 0x00, 0, 1);
    insn(p6 + 16, 0x95, 0x00, 0, 0);
    uint64_t g6 = fn(p6, sizeof(p6), 10, 0);
    if (g6 != 4294967295ULL) { fprintf(stderr, "FAIL t6: got %llu want 4294967295\n", (unsigned long long)g6); fails++; }

    /* 7. JGT_K taken vs not taken */
    uint8_t p7[32];
    insn(p7 + 0,  0x25, 0x01, 1, 5);      /* if r1 > 5 goto pc=2 */
    insn(p7 + 8,  0x95, 0x00, 0, 0);      /* EXIT (r0=0) */
    insn(p7 + 16, 0xb7, 0x00, 0, 77);     /* r0 = 77 */
    insn(p7 + 24, 0x95, 0x00, 0, 0);      /* EXIT */
    uint64_t g7a = fn(p7, sizeof(p7), 10, 6);
    uint64_t g7b = fn(p7, sizeof(p7), 10, 5);
    if (g7a != 77 || g7b != 0) {
        fprintf(stderr, "FAIL t7: got (%llu, %llu) want (77, 0)\n",
                (unsigned long long)g7a, (unsigned long long)g7b);
        fails++;
    }

#ifdef NATIVE_JIT_BIN
    munmap(buf, map_sz);
#endif
    if (fails == 0) {
        printf("NATIVE_PASS 7/7\n");
        return 0;
    }
    return 1;
}
