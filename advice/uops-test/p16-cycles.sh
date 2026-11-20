#!/bin/bash
# How many cycles and instructions the 16-way AVX-512 kernel of the shipped file takes for a block
# (blake3_servil_avx512_p16 of kcheck/b3hashr.o in the Ode repository): one thread, under the bench lock.
# For comparison with a prediction made from uops.info's tables (the study's predict.py).
set -uo pipefail
R="$1"; O="$R/out"; mkdir -p "$O"
cd "$R/ode" || exit 1
{ echo "ode $(git rev-parse HEAD)"; grep -m1 'model name' /proc/cpuinfo || true; uname -r; cc --version | head -n 1;
  echo "b3hashr.o $(sha256sum kcheck/b3hashr.o | cut -c1-64)"; } > "$O/identity.txt"
cat "$O/identity.txt"
W="$R/w"; mkdir -p "$W"
cat > "$W/p16_cycles.c" <<'EOF'
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <linux/perf_event.h>

void blake3_servil_avx512_p16(const uint8_t *const *inputs, uint64_t n, const uint8_t *key, uint64_t t, uint64_t packed, uint8_t *out);

static int counter(uint64_t config) {
    struct perf_event_attr a;
    memset(&a, 0, sizeof a);
    a.type = PERF_TYPE_HARDWARE; a.size = sizeof a; a.config = config;
    a.exclude_kernel = 1; a.exclude_hv = 1; a.disabled = 0;
    return (int)syscall(SYS_perf_event_open, &a, 0, -1, -1, 0);
}
static uint64_t count(int fd) { uint64_t v = 0; if (fd < 0 || read(fd, &v, 8) != 8) return 0; return v; }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec * 1e9 + ts.tv_nsec; }

int main(int argc, char **argv) {
    uint64_t n = argc > 1 ? strtoull(argv[1], 0, 10) : 16, reps = argc > 2 ? strtoull(argv[2], 0, 10) : 200000;
    const uint8_t *table[16];
    uint8_t *key = aligned_alloc(64, 64), *out = aligned_alloc(64, 512);
    for (int i = 0; i < 16; i++) {
        uint8_t *p = aligned_alloc(64, n * 64);
        for (uint64_t k = 0; k < n * 64; k++) p[k] = (uint8_t)(k * 31 + i * 7 + 1);
        table[i] = p;
    }
    for (int k = 0; k < 32; k++) key[k] = (uint8_t)(k + 1);
    uint64_t packed = 0 | (1u << 8) | (2u << 16) | (64u << 24);     /* flags 0, start 1, end 2, length 64 */
    for (uint64_t r = 0; r < reps / 10 + 1000; r++) blake3_servil_avx512_p16(table, n, key, r, packed, out);
    int cyc = counter(PERF_COUNT_HW_CPU_CYCLES), ins = counter(PERF_COUNT_HW_INSTRUCTIONS);
    uint64_t c0 = count(cyc), i0 = count(ins); double t0 = now();
    for (uint64_t r = 0; r < reps; r++) blake3_servil_avx512_p16(table, n, key, r, packed, out);
    uint64_t c1 = count(cyc), i1 = count(ins); double t1 = now();
    unsigned sum = 0; for (int k = 0; k < 512; k++) sum = sum * 131 + out[k];
    double blocks = (double)reps * (double)n;
    printf("n %llu  reps %llu  cycles a block %.2f  instructions a block %.2f  ns a block %.3f  counters %s  out %08x\n",
           (unsigned long long)n, (unsigned long long)reps, (c1 - c0) / blocks, (i1 - i0) / blocks, (t1 - t0) / blocks,
           cyc >= 0 && ins >= 0 ? "perf" : "NONE", sum);
    return 0;
}
EOF
cc -O2 -o "$W/p16_cycles" "$W/p16_cycles.c" kcheck/b3hashr.o || { echo "the harness does not build: FAILED" > "$O/status.txt"; exit 1; }
for round in 1 2 3 4 5; do
  for n in 16 64 1; do
    reps=$((3200000 / n))
    taskset -c 2 "$W/p16_cycles" "$n" "$reps" >> "$O/cycles.txt" 2>&1 || echo "n $n FAILED" >> "$O/cycles.txt"
  done
done
cat "$O/cycles.txt"
echo done > "$O/status.txt"
