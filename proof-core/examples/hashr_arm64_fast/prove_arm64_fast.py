#!/usr/bin/env python3
"""Prove, bundle, audit, and emit `.S` for the fast AArch64 BLAKE3 hash (Step 1).

Proves all 7 new/upgraded AArch64 functions in topological order (reusing the kept proof
of `blake3_servil_compress_in_place_arm64`):
  1. blake3_servil_compress_in_place_arm64   (kept proof, 116 insns)
  2. b3l_pad_fast_arm64                      (custom calling, stack 0, 8-byte-step n==64)
  3. b3l_node_out_fast_arm64                 (10 insns, stack 0, tail jump `b`)
  4. b3l_chunk_node_fast_arm64               (stack 0 + tail jump `b` for len <= 64)
  5. b3l_wide4_fast_arm64                    (4-way NEON `children`, shared by 4 KiB & subtrees)
  6. b3l_subtree_fast_arm64                  (uses `b3l_wide4_fast_arm64` at 4 KiB)
  7. b3l_hashr_long_arm64                    (direct 4-KiB `b3l_wide4_fast_arm64` dispatch!)
  8. b3l_hashr_arm64                         (14-insn zero-copy 64B tail jump `b`, 1-insn >1024 tail jump `b`, 0-spill <=1024)

Verifies all 8 functions in ONE `odeverify` run, packs and audits one single AArch64 ELF64
bundle via `ode_audit.pack_bundle` + `ode_audit.audit_bundle`, and optionally emits a settled
cross-platform `.S` file (with both `bl` and `b` relocations) via `--emit-s PATH`.
"""

import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
PC = os.path.dirname(os.path.dirname(HERE))
ROOT = os.path.dirname(PC)
ARM = os.path.join(PC, "examples", "arm64")
KCHECK = os.path.join(ROOT, "kcheck")
for d in (PC, os.path.join(ROOT, "lang"), os.path.join(ROOT, "arm64"),
          os.path.join(ROOT, "core"), KCHECK):
    if d not in sys.path:
        sys.path.insert(0, d)

import obj as aobj
import ode
import ode_audit
import odec
import prove
import statement

FUNCTIONS = [
    (os.path.join(ARM, "compress_arm64.ode"),  "compress1_arm64",       "blake3_servil_compress_in_place_arm64"),
    (os.path.join(HERE, "hash_fast_arm64.ode"), "pad_fast_arm64",       "b3l_pad_fast_arm64"),
    (os.path.join(HERE, "hash_fast_arm64.ode"), "node_out_fast_arm64",  "b3l_node_out_fast_arm64"),
    (os.path.join(HERE, "hash_fast_arm64.ode"), "chunk_node_fast_arm64","b3l_chunk_node_fast_arm64"),
    (os.path.join(HERE, "wide4_fast_arm64.ode"),"wide4_fast_arm64",     "b3l_wide4_fast_arm64"),
    (os.path.join(HERE, "hash_fast_arm64.ode"), "subtree_fast_arm64",   "b3l_subtree_fast_arm64"),
    (os.path.join(HERE, "hash_fast_arm64.ode"), "hashr_long_arm64",     "b3l_hashr_long_arm64"),
    (os.path.join(HERE, "hash_fast_arm64.ode"), "hashr_fast_arm64",     "b3l_hashr_arm64"),
]


def load_full_spec():
    with open(os.path.join(KCHECK, "blake3.spec"), "r", encoding="utf-8") as f:
        spec = f.read()
    with open(os.path.join(ARM, "compress_arm64.spec"), "r", encoding="utf-8") as f:
        spec += "\n" + f.read()
    with open(os.path.join(HERE, "hash_fast_arm64.spec"), "r", encoding="utf-8") as f:
        spec += "\n" + f.read()
    return spec


def kept_compress_proof():
    with open(os.path.join(PC, "proofs", "b3hashr_arm64.proof"), "r", encoding="utf-8") as f:
        txt = f.read()
    start = txt.index("for blake3_servil_compress_in_place_arm64\n")
    end = txt.index("\nfor ", start + 1)
    return txt[start:end + 1]


def prove_one(spec_text, kept_pairs, kept_proofs_map, target_obj, target_sym, target_places, tmp_dir):
    all_fns = kept_pairs + [(target_obj, target_sym)]
    st_path = os.path.join(tmp_dir, target_sym + ".st")
    pf_path = os.path.join(tmp_dir, target_sym + ".prf")
    st_lines = statement.statement(spec_text, all_fns)
    with open(st_path, "w", encoding="utf-8") as f:
        f.write("\n".join(st_lines) + "\n")
    done = []
    for _, sym in kept_pairs:
        done.extend(kept_proofs_map[sym].splitlines())
    sp = ode.Spec(spec_text)
    seqs = statement.sequences(sp)
    counted = {name: m["state"] for name, m in ode.Parser(spec_text).file()[2].items()}
    reg_list = prove.REGISTERS_ARM
    trace_exprs, instrs = prove.fn_statement_info(st_path, target_sym, reg_list)
    keep, marked, marked_result = {}, {}, {}
    t0 = time.time()
    while True:
        kinds = statement.kinds_of(sp.contracts[target_sym], target_sym, sp.layouts)
        pl_lines = prove.places(
            target_places, keep, seqs, kinds, counted, target_sym, marked,
            regs=reg_list, marked_result=marked_result,
        )
        p = prove.Prover(
            st_path, done + [f"for {target_sym}"] + pl_lines, pf_path, [],
            trace_exprs=trace_exprs, instrs=instrs, reg_list=reg_list,
        )
        p.last = ""
        p.last_proof = []
        try:
            proof = p.solve([])
        except prove.Unkept as e:
            keep[e.args[0]] = [r for r in keep.get(e.args[0], reg_list) if r != reg_list[e.args[1]]]
            p.close()
            continue
        except prove.Marked as e:
            marked[e.args[0]] = marked.get(e.args[0], []) + [reg_list[e.args[1]]]
            p.close()
            continue
        except prove.MarkedResult as e:
            marked_result[e.args[0]] = marked_result.get(e.args[0], []) + [reg_list[e.args[1]]]
            p.close()
            continue
        except BaseException as exc:
            last = p.last
            p.close()
            raise RuntimeError(f"prove failed for {target_sym} after {time.time()-t0:.2f}s: {exc}\nLAST:\n{last[:2000]}")
        if proof is None:
            last = p.last
            p.close()
            raise RuntimeError(f"no proof found for {target_sym} after {time.time()-t0:.2f}s:\n{last[:2000]}")
        fn_lines = [f"for {target_sym}"] + pl_lines + proof
        p.close()
        dt = time.time() - t0
        print(f"  PROVED {target_sym}: {len(fn_lines)} lines in {dt:.2f}s", flush=True)
        return "\n".join(fn_lines) + "\n"


def emit_asm(fns, contract_b32, binary_b32, export_as=None):
    """Emit one cross-platform `.S` file preserving every verified instruction word and
    both `bl` (`R_AARCH64_CALL26 = 283`) and tail-jump `b` (`R_AARCH64_JUMP26 = 282`) relocations.
    When `export_as` is given (e.g. `blake3_servil_ode_hashr_arm64`), helpers use private local
    labels and only the entry point is exported globally."""
    lines = [
        "// Lean-4-verified single-threaded BLAKE3 for AArch64 (8/8 functions, 100% Ode source,",
        "// custom calling + verified tail calls `b` + zero-copy 64 B + direct 4-KiB 4-way NEON).",
        f"// Audited bundle BLAKE3(contract) = {contract_b32}",
        f"// Audited bundle BLAKE3(binary)   = {binary_b32}",
        "#ifdef __APPLE__",
        "#define SYM(x) _##x",
        "#define LSYM(x) L_ode_##x",
        "#else",
        "#define SYM(x) x",
        "#define LSYM(x) .L_ode_##x",
        "#endif",
        ".text",
    ]
    entry_sym = fns[-1][1]
    for obj_p, sym in fns:
        e = aobj.Elf(obj_p)
        symbols, symtab = e.symbols()
        shndx, value, size, at = aobj.place(e, sym)
        relocs = e.relocations(shndx, symtab)
        code = e.b[at:at + size]
        lines.append(".p2align 4")
        if export_as is not None and sym == entry_sym:
            lines += [f".globl SYM({export_as})", f"SYM({export_as}):", f"LSYM({sym}):"]
        elif export_as is not None:
            lines.append(f"LSYM({sym}):")
        else:
            lines += [f".globl SYM({sym})", f"SYM({sym}):"]
        for off in range(0, size, 4):
            rel = relocs.get(value + off)
            if rel is not None:
                rtype, sym_idx = rel[0], rel[1]
                target_sym = symbols[sym_idx][0]
                tlabel = f"LSYM({target_sym})" if export_as is not None else f"SYM({target_sym})"
                if rtype == 282:
                    lines.append(f"  b {tlabel}")
                elif rtype == 283:
                    lines.append(f"  bl {tlabel}")
                else:
                    raise ValueError(f"unsupported relocation type {rtype} in {sym}+{off}")
            else:
                w = int.from_bytes(code[off:off + 4], "little")
                lines.append(f"  .word 0x{w:08x}")
    return "\n".join(lines) + "\n"


def main():
    emit_s = None
    only_syms = None
    reuse_existing = "--reuse" in sys.argv
    if "--emit-s" in sys.argv:
        emit_s = sys.argv[sys.argv.index("--emit-s") + 1]
    if "--only" in sys.argv:
        only_syms = set(sys.argv[sys.argv.index("--only") + 1].split(","))

    spec_text = load_full_spec()
    kept_proof_file = os.path.join(HERE, "b3hashr_arm64_fast.proof")

    with tempfile.TemporaryDirectory() as d:
        built_pairs = []
        places_map = {}
        unit_elfs = {}
        for src, ode_fn, sym in FUNCTIONS:
            obj_p = os.path.join(d, sym + ".o")
            odec.build(src, ode_fn, obj_p)
            pl = odec.places(src, ode_fn) or ""
            built_pairs.append((obj_p, sym))
            places_map[sym] = pl
            with open(obj_p, "rb") as f:
                unit_elfs[sym] = f.read()

        proofs_map = {"blake3_servil_compress_in_place_arm64": kept_compress_proof()}
        if reuse_existing and os.path.exists(kept_proof_file):
            with open(kept_proof_file, "r", encoding="utf-8") as f:
                raw = f.read()
            parts = raw.split("\nfor ")
            for i, p in enumerate(parts):
                sec = p if i == 0 else "for " + p
                sec = sec.strip()
                if not sec:
                    continue
                first = sec.splitlines()[0]
                assert first.startswith("for ")
                nm = first[4:].strip()
                proofs_map[nm] = sec + "\n"

        kept_pairs = [built_pairs[0]]
        for obj_p, sym in built_pairs[1:]:
            if sym in proofs_map and (only_syms is None or sym not in only_syms):
                print(f"  REUSE {sym} ({len(proofs_map[sym].splitlines())} lines)", flush=True)
            else:
                proofs_map[sym] = prove_one(
                    spec_text, kept_pairs, proofs_map, obj_p, sym, places_map[sym], d
                )
            kept_pairs.append((obj_p, sym))

        combined = "".join(proofs_map[sym] for _, sym in built_pairs)
        with open(kept_proof_file, "w", encoding="utf-8") as f:
            f.write(combined)
        print(f"\nWrote {kept_proof_file} ({len(combined)} bytes, {len(combined.splitlines())} lines)", flush=True)

        # Full 8-function odeverify run
        st_p = os.path.join(d, "all8.st")
        st_lines = statement.statement(spec_text, built_pairs)
        with open(st_p, "w", encoding="utf-8") as f:
            f.write("\n".join(st_lines) + "\n")
        t0 = time.time()
        r = subprocess.run(
            [os.path.join(PC, ".lake", "build", "bin", "odeverify"),
             statement.TABLES["arm64"], st_p, kept_proof_file],
            capture_output=True, text=True,
        )
        dt = time.time() - t0
        print(f"Full 8-fn odeverify ({dt:.2f}s): rc={r.returncode} out={r.stdout.strip()} err={r.stderr.strip()}", flush=True)
        if r.returncode != 0:
            raise SystemExit(1)

        # Pack & audit single AArch64 bundle
        out_o = os.path.join(d, "b3hashr_arm64_fast.o")
        out_p = os.path.join(d, "b3hashr_arm64_fast.bundle.proof")
        order = [sym for _, sym in built_pairs]
        res = ode_audit.pack_bundle(
            [unit_elfs[sym] for sym in order], order, "b3l_hashr_arm64", spec_text, out_o, out_p,
            existing_proof_path=kept_proof_file,
        )
        print("AUDITED BUNDLE:", res["verdict"], "fns=", res["coverage"]["functions"],
              "insns=", res["coverage"]["instructions"],
              "contract=", res["contract_b32"], "binary=", res["binary_b32"], flush=True)
        assert res["verdict"] == "shown"
        assert res["coverage"]["functions"] == 8

        if emit_s is not None:
            asm_txt = emit_asm(
                built_pairs, res["contract_b32"], res["binary_b32"],
                export_as="blake3_servil_ode_hashr_arm64",
            )
            with open(emit_s, "w", encoding="utf-8") as f:
                f.write(asm_txt)
            print(f"Wrote {emit_s} ({len(asm_txt)} bytes)", flush=True)


if __name__ == "__main__":
    main()
