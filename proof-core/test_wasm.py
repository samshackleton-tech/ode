#!/usr/bin/env pypy3
"""Dual-verification (`--verifier both`) and native execution tests for the WebAssembly 2.0
binary module validator and 17-opcode bounded stack-machine interpreter (`examples/wasm/wasm_core.ode`)
on x86-64 and AArch64."""
import os, platform, re, shutil, struct, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ODE_TOOL = os.path.join(ROOT, "lang", "ode_tool.py")
SRC = os.path.join(HERE, "examples", "wasm", "wasm_core.ode")

IS_LINUX_X86 = (platform.system() == "Linux" and platform.machine() in ("x86_64", "AMD64"))
IS_MAC_ARM64 = (platform.system() == "Darwin" and platform.machine() == "arm64")


def reloc_arm64_text(elf_path, sym_name):
    with open(elf_path, "rb") as f:
        b = f.read()
    e_shoff = struct.unpack_from("<Q", b, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", b, 58)
    secs = [struct.unpack_from("<IIQQQQI", b, e_shoff + i * e_shentsize) for i in range(e_shnum)]
    shstr_off = secs[e_shstrndx][4]
    sname = lambda idx: b[shstr_off + idx:b.index(0, shstr_off + idx)].decode("ascii", "replace")
    tb, eoff, sv = b"", 0, {}
    for sn, st, _, _, so, sz, sl in secs:
        if sname(sn) == ".text":
            tb = b[so:so + sz]
        elif st == 2:
            stro = secs[sl][4]
            for idx, pos in enumerate(range(so, so + sz, 24)):
                nm, _, _, _, val, _ = struct.unpack_from("<IBBHQQ", b, pos)
                sv[idx] = val
                if b[stro + nm:b.index(0, stro + nm)].decode("ascii", "replace") == sym_name:
                    eoff = val
    buf = bytearray(tb)
    for sn, st, _, _, so, sz, _ in secs:
        if st == 4 and sname(sn) == ".rela.text":
            for pos in range(so, so + sz, 24):
                ro, ri, ra = struct.unpack_from("<QQq", b, pos)
                if (ri & 0xFFFFFFFF) in (282, 283):
                    imm26 = (((sv[ri >> 32] + ra) - ro) >> 2) & 0x03FFFFFF
                    ins = struct.unpack_from("<I", buf, ro)[0]
                    struct.pack_into("<I", buf, ro, (ins & 0xFC000000) | imm26)
    return bytes(buf), eoff


@unittest.skipUnless(shutil.which("lake"), "Lean's `lake` is not installed here")
class TestWasmCore(unittest.TestCase):
    def test_wasm_core_dual_verify_and_native(self):
        fns = [
            "wasm_module_hdr_ok",
            "wasm_uleb32_len",
            "wasm_uleb32_val",
            "wasm_section_next",
            "wasm_validate_module",
            "wasm_eval_stack",
        ]
        root_fns = ["wasm_validate_module", "wasm_eval_stack"]

        with tempfile.TemporaryDirectory() as d:
            cids, syms, objs = {}, {}, {}
            for fn in fns:
                for tgt in ("x86_64", "arm64"):
                    obj_p = os.path.join(d, f"{fn}_{tgt}.o")
                    prf_p = os.path.join(d, f"{fn}_{tgt}.proof")
                    res = subprocess.run(
                        [sys.executable, ODE_TOOL, "pack", SRC, "--fn", fn, "--target", tgt,
                         "--c-abi", "--verifier", "both", "--out", obj_p, "--proof", prf_p],
                        capture_output=True, text=True,
                    )
                    self.assertEqual(res.returncode, 0, f"Wasm pack failed ({fn}, {tgt}):\n{res.stdout}\n{res.stderr}")
                    self.assertIn("VERDICT:           shown", res.stdout)
                    self.assertIn("odeverify (shown), verify2 (shown)", res.stdout)
                    m = re.search(r"SYMBOL:\s+(ode_[a-z2-7]{52})", res.stdout)
                    self.assertIsNotNone(m, res.stdout)
                    syms[(fn, tgt)] = m.group(1)
                    cids[(fn, tgt)] = m.group(1)[4:]
                    objs[(fn, tgt)] = obj_p
                self.assertEqual(cids[(fn, "x86_64")], cids[(fn, "arm64")], f"cross-arch hash mismatch: {fn}")

            def c_body(p):
                return f"""
    const uint64_t MOD_ERR = 4294967295ULL;
    const uint64_t TRAP = 4294967296ULL;
    /* 1. Valid minimal Wasm 2.0 module (0 sections) */
    const uint8_t mod_empty[8] = {{ 0x00, 'a', 's', 'm', 0x01, 0x00, 0x00, 0x00 }};
    CHK({p}wasm_validate_module(mod_empty, sizeof(mod_empty)) == 0);
    /* 2. Valid 4-section Wasm module: Custom(0), Type(1), Function(3), Custom(0), Code(10) */
    const uint8_t mod_ok[] = {{
        0x00, 'a', 's', 'm', 0x01, 0x00, 0x00, 0x00,
        0x00, 0x02, 'h', 'i',           /* Custom section (id=0, size=2) */
        0x01, 0x04, 0x01, 0x60, 0x00, 0x00, /* Type section (id=1, size=4) */
        0x03, 0x02, 0x01, 0x00,         /* Function section (id=3, size=2) */
        0x00, 0x00,                     /* Second Custom section (id=0, size=0) */
        0x0A, 0x04, 0x01, 0x02, 0x00, 0x0B /* Code section (id=10, size=4) */
    }};
    CHK({p}wasm_validate_module(mod_ok, sizeof(mod_ok)) == 5);
    /* 3. Out-of-order sections (Function=3 then Type=1) must be refused */
    const uint8_t mod_ooo[] = {{
        0x00, 'a', 's', 'm', 0x01, 0x00, 0x00, 0x00,
        0x03, 0x01, 0x00,
        0x01, 0x01, 0x00
    }};
    CHK({p}wasm_validate_module(mod_ooo, sizeof(mod_ooo)) == MOD_ERR);
    /* 4. Truncated section payload must be refused */
    CHK({p}wasm_validate_module(mod_ok, sizeof(mod_ok) - 1) == MOD_ERR);
    /* 5. Bad version 2 must be refused */
    const uint8_t mod_badv[8] = {{ 0x00, 'a', 's', 'm', 0x02, 0x00, 0x00, 0x00 }};
    CHK({p}wasm_validate_module(mod_badv, sizeof(mod_badv)) == MOD_ERR);
    /* 6. Wasm stack VM: (i32.const 40) (i32.const 2) (i32.add) (end) -> 42 */
    const uint8_t prog_add[] = {{ 0x41, 40, 0x41, 2, 0x6A, 0x0B }};
    CHK({p}wasm_eval_stack(prog_add, sizeof(prog_add), 16) == 42);
    /* 7. Wrapping i32.sub: (i32.const 0) (i32.const 1) (i32.sub) (end) -> 0xFFFFFFFF */
    const uint8_t prog_sub[] = {{ 0x41, 0, 0x41, 1, 0x6B, 0x0B }};
    CHK({p}wasm_eval_stack(prog_sub, sizeof(prog_sub), 16) == 0xFFFFFFFFULL);
    /* 8. local.tee, local.get, local.set, nop, drop, select, comparisons, eqz:
          local0 := 10 (tee), push 3, add -> 13, local.set 0;
          push 100, push 99, (local.get 0 == 13 ? 1 : 0) -> select -> 100! */
    const uint8_t prog_rich[] = {{
        0x01,                   /* nop */
        0x41, 10,               /* i32.const 10 */
        0x22, 0,                /* local.tee 0 -> stk=[10], loc0=10 */
        0x41, 3,                /* i32.const 3  -> stk=[10, 3] */
        0x6A,                   /* i32.add      -> stk=[13] */
        0x21, 0,                /* local.set 0  -> stk=[], loc0=13 */
        0x41, 100,              /* i32.const 100 */
        0x41, 99,               /* i32.const 99 */
        0x20, 0,                /* local.get 0 -> 13 (sp=3) */
        0x1B,                   /* select (c=13 != 0 -> picks 100!) -> stk=[100] */
        0x41, 7,                /* i32.const 7 */
        0x1A,                   /* drop -> stk=[100] */
        0x41, 100,              /* i32.const 100 */
        0x46,                   /* i32.eq -> 1 */
        0x45,                   /* i32.eqz -> 0 */
        0x45,                   /* i32.eqz -> 1 */
        0x0B                    /* end -> 1 */
    }};
    CHK({p}wasm_eval_stack(prog_rich, sizeof(prog_rich), 64) == 1);
    /* 9. select with c == 0 picks second value (99) */
    const uint8_t prog_sel0[] = {{ 0x41, 100, 0x41, 99, 0x41, 0, 0x1B, 0x0B }};
    CHK({p}wasm_eval_stack(prog_sel0, sizeof(prog_sel0), 16) == 99);
    /* 10. Unsigned comparison: (0 - 1) >_u 100 == 1 */
    const uint8_t prog_gtu[] = {{ 0x41, 0, 0x41, 1, 0x6B, 0x41, 100, 0x4B, 0x0B }};
    CHK({p}wasm_eval_stack(prog_gtu, sizeof(prog_gtu), 16) == 1);
    /* 11. Traps: stack underflow, stack overflow (>3), fuel exhaustion, bad opcode */
    const uint8_t trap_under[] = {{ 0x1A, 0x0B }};
    CHK({p}wasm_eval_stack(trap_under, sizeof(trap_under), 16) == TRAP);
    const uint8_t trap_over[] = {{ 0x41, 1, 0x41, 2, 0x41, 3, 0x41, 4, 0x0B }};
    CHK({p}wasm_eval_stack(trap_over, sizeof(trap_over), 16) == TRAP);
    CHK({p}wasm_eval_stack(prog_add, sizeof(prog_add), 2) == TRAP);
    const uint8_t trap_badop[] = {{ 0xFF, 0x0B }};
    CHK({p}wasm_eval_stack(trap_badop, sizeof(trap_badop), 16) == TRAP);
"""

            cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
            if IS_LINUX_X86 and cc:
                decls = "\n".join([
                    f'uint64_t {syms[("wasm_validate_module", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("wasm_eval_stack", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                ])
                aliases = "\n".join(f'#define fn_{fn} {syms[(fn, "x86_64")]}' for fn in root_fns)
                c_src = f"""
#include <stdint.h>
#include <stdio.h>
{decls}
{aliases}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
{c_body("fn_")}
    puts("wasm_x86: OK");
    return 0;
}}
"""
                c_p, exe_p = os.path.join(d, "run_wasm.c"), os.path.join(d, "run_wasm")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run([cc, "-O1", "-o", exe_p, c_p] + [objs[(fn, "x86_64")] for fn in root_fns],
                               check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "wasm_x86: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                types = {
                    "wasm_validate_module": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "wasm_eval_stack": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                }
                load_lines = []
                for fn in root_fns:
                    code, entry = reloc_arm64_text(objs[(fn, "arm64")], syms[(fn, "arm64")])
                    bp = os.path.join(d, f"{fn}.bin")
                    with open(bp, "wb") as bf:
                        bf.write(code)
                    ty = types[fn]
                    load_lines.append(
                        f'    {ty.replace("(*)", "(*fn_" + fn + ")")} = ({ty})load_jit("{bp}", {len(code)}, {entry});'
                    )
                loads = "\n".join(load_lines)
                c_src = f"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <pthread.h>
#include <libkern/OSCacheControl.h>
static void *load_jit(const char *path, size_t n, size_t entry_off) {{
    uint8_t *tmp = (uint8_t *)malloc(n);
    FILE *fp = fopen(path, "rb");
    if (!tmp || !fp || fread(tmp, 1, n, fp) != n) {{ fprintf(stderr, "read %s\\n", path); exit(2); }}
    fclose(fp);
    void *p = mmap(NULL, (n + 4095) & ~4095ULL, PROT_READ|PROT_WRITE|PROT_EXEC, MAP_PRIVATE|MAP_ANON|MAP_JIT, -1, 0);
    if (p == MAP_FAILED) {{ perror("mmap"); exit(2); }}
    pthread_jit_write_protect_np(0);
    memcpy(p, tmp, n);
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(p, n);
    free(tmp);
    return (uint8_t *)p + entry_off;
}}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
{loads}
{c_body("fn_")}
    puts("wasm_arm64: OK");
    return 0;
}}
"""
                c_p, exe_p = os.path.join(d, "run_wasm_arm64.c"), os.path.join(d, "run_wasm_arm64")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", exe_p, c_p], check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "wasm_arm64: OK")


if __name__ == "__main__":
    unittest.main()
