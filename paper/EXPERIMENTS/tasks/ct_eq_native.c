/* Native hardware test harness for verified byte-slice equality (trace depends on the length alone). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t (*ct_eq_fn_t)(const uint8_t *a, const uint8_t *b, uint64_t n);

#ifdef NATIVE_JIT_BIN
#include <pthread.h>
#include <sys/mman.h>
#include <unistd.h>
#include <libkern/OSCacheControl.h>

static ct_eq_fn_t load_jit_fn(const char *path, size_t entry_off, void **out_buf, size_t *out_sz) {
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
    return (ct_eq_fn_t)((uint8_t *)mem + entry_off);
}
#else
extern uint64_t ode_rpxfmeixumkaoep4wemhcysirkt7uciujxzihzc4m6obijc7bvmq(
    const uint8_t *a, const uint8_t *b, uint64_t n);
#endif

int main(int argc, char **argv) {
    ct_eq_fn_t fn = NULL;
#ifdef NATIVE_JIT_BIN
    void *buf = NULL;
    size_t map_sz = 0;
    if (argc != 3) { fprintf(stderr, "usage: %s text.bin entry_off\n", argv[0]); return 2; }
    fn = load_jit_fn(argv[1], (size_t)strtoull(argv[2], NULL, 0), &buf, &map_sz);
#else
    (void)argc; (void)argv;
    fn = ode_rpxfmeixumkaoep4wemhcysirkt7uciujxzihzc4m6obijc7bvmq;
#endif
    uint8_t a[32], b[32];
    for (int i = 0; i < 32; i++) { a[i] = (uint8_t)(i * 7 + 3); b[i] = a[i]; }
    int fails = 0;
    if (fn(a, b, 0) != 1) { fprintf(stderr, "FAIL empty\n"); fails++; }
    if (fn(a, b, 32) != 1) { fprintf(stderr, "FAIL eq32\n"); fails++; }
    b[0] ^= 1;
    if (fn(a, b, 32) != 0) { fprintf(stderr, "FAIL diff_first\n"); fails++; }
    b[0] = a[0]; b[31] ^= 0x80;
    if (fn(a, b, 32) != 0) { fprintf(stderr, "FAIL diff_last\n"); fails++; }
    b[31] = a[31]; b[17] ^= 0x40;
    if (fn(a, b, 32) != 0) { fprintf(stderr, "FAIL diff_mid\n"); fails++; }
#ifdef NATIVE_JIT_BIN
    munmap(buf, map_sz);
#endif
    if (fails == 0) {
        printf("NATIVE_PASS 5/5\n");
        return 0;
    }
    return 1;
}
