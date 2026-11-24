#!/usr/bin/env python3
"""Prove and audit the fast short-input x86-64 BLAKE3 bundle (Step C).

Proves `b3l_pad_fast` (custom calling, stack 0), `b3l_chunk_node_fast`, and `b3l_hashr`
(zero-spill fast paths for `len == 64`, `len < 64`, `65..1024`, delegating `> 1024` to
`b3l_hashr_long`), verifies all 16 functions in ONE `odeverify` call, and packs a single
hash-bound ELF64 `.o` audited by `ode audit`.
"""

import os
import re
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
PC = os.path.dirname(os.path.dirname(HERE))
ROOT = os.path.dirname(PC)
KCHECK = os.path.join(ROOT, "kcheck")
for d in (PC, os.path.join(ROOT, "lang"), KCHECK, os.path.join(ROOT, "core")):
    if d not in sys.path:
        sys.path.insert(0, d)

import lean_verify
import ode
import ode_audit
import odec
import prove
import statement

KEPT_INNER = [
    "blake3_servil_compress_in_place_sse41",
    "blake3_servil_compress_in_place_avx512",
    "blake3_servil_avx512_k32",
    "blake3_servil_avx512_p16",
    "blake3_servil_avx512_p32",
    "b3l_pad",
    "b3l_node_out",
    "b3l_chunk_node",
    "b3l_wide32",
    "b3l_wide128",
    "b3l_take",
    "b3l_part32",
    "b3l_subtree",
]


def load_full_spec():
    with open(os.path.join(KCHECK, "blake3.spec"), "r", encoding="utf-8") as f:
        spec = f.read()
    with open(os.path.join(KCHECK, "proofs", "inner.spec"), "r", encoding="utf-8") as f:
        inner = f.read()
    with open(os.path.join(HERE, "hash_fast.spec"), "r", encoding="utf-8") as f:
        fspec = f.read()
    layouts = "\n".join(re.findall(r"^layout .*$", inner, re.M))
    def c_of(t, n):
        (x,) = re.findall(rf"^contract {n}\(.*?^\}}\n", t, re.S | re.M)
        return x
    return spec + "\n" + layouts + "\n" + "\n".join(c_of(inner, n) for n in KEPT_INNER) + "\n" + fspec


def prove_one_with_kept(spec_text, kept_pairs, kept_proofs_map, target_obj, target_sym, target_places, tmp_dir):
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
    reg_list = prove.REGISTERS
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


def emit_settled_s(bundle_obj_bytes, export_sym, out_s_path, contract_b32, binary_b32):
    """Settle intra-object relocations of an audited x86-64 bundle `.o` into a standalone `.S` file."""
    elf = ode_audit.parse_elf64(bundle_obj_bytes)
    assert elf["target"] == "x86-64"
    tsec = elf["by_name"][".text"][0]
    t_idx = tsec["idx"]
    ro_secs = elf["by_name"].get(".rodata", [])
    ro_idx = ro_secs[0]["idx"] if ro_secs else -1
    ro_body = ro_secs[0]["body"] if ro_secs else b""

    text = bytearray(tsec["body"])
    ro_off = len(text)
    if ro_body:
        pad = (-len(text)) % 64
        text += b"\xcc" * pad
        ro_off = len(text)
        text += ro_body
        # Pad final blob to 16-byte boundary.
        tail_pad = (-len(text)) % 16
        if tail_pad:
            text += bytes(tail_pad)

    syms = elf["symbols"]
    import struct
    for s in elf["sections"]:
        if s["type"] == ode_audit.SHT_RELA and s["info"] == t_idx:
            for pos in range(0, len(s["body"]), 24):
                r_off, r_info, r_add = struct.unpack_from("<QQq", s["body"], pos)
                r_type = r_info & 0xFFFFFFFF
                rsym = syms[r_info >> 32]
                if r_type == ode_audit.R_X86_64_PC32 and ro_idx >= 0 and rsym["shndx"] == ro_idx:
                    disp = (ro_off + rsym["value"] + r_add) - r_off
                elif r_type == ode_audit.R_X86_64_PLT32 and rsym["shndx"] == t_idx:
                    disp = (rsym["value"] + r_add) - r_off
                else:
                    raise ValueError(f"cannot settle relocation type={r_type} sym={rsym['name']!r}")
                struct.pack_into("<i", text, r_off, disp)

    exp = next(s for s in syms if s["name"] == export_sym)
    lines = [
        "// Lean-4-verified single-threaded BLAKE3 for x86-64 (17/17 functions, custom calling",
        "// `b3l_pad_fast` + zero-spill short-input path <= 1024 B + AVX-512 32-way wide tree).",
        f"// Audited bundle BLAKE3(contract) = {contract_b32}",
        f"// Audited bundle BLAKE3(binary)   = {binary_b32}",
        "// Only the entry point `blake3_servil_ode_hashr` is global.",
        ".text",
        ".p2align 6",
        ".Lode_b3hashr_text:",
    ]
    for i in range(0, len(text), 16):
        chunk = text[i:i + 16]
        lines.append("  .byte " + ", ".join(f"0x{b:02x}" for b in chunk))
    lines.extend([
        ".globl blake3_servil_ode_hashr",
        ".type blake3_servil_ode_hashr, @function",
        f".set blake3_servil_ode_hashr, .Lode_b3hashr_text + 0x{exp['value']:x}",
        f".size blake3_servil_ode_hashr, {exp['size']}",
        '.section .note.GNU-stack,"",@progbits',
        "",
    ])
    with open(out_s_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))


def main():
    emit_s = None
    if "--emit-s" in sys.argv:
        emit_s = sys.argv[sys.argv.index("--emit-s") + 1]
    full_spec = load_full_spec()
    src = os.path.join(HERE, "hash_fast.ode")
    with tempfile.TemporaryDirectory(prefix="b3_fast_") as d:
        # Build all 13 legacy objects cleanly from source.
        bdir = os.path.join(d, "orig")
        os.makedirs(bdir)
        subprocess.run([sys.executable, os.path.join(ROOT, "lang", "odec.py"),
                        os.path.join(KCHECK, "hash.ode"), "--all", bdir], check=True, capture_output=True)
        subprocess.run([sys.executable, os.path.join(KCHECK, "kernels.py"), bdir],
                       check=True, capture_output=True)
        # Rename `b3l_hashr` -> `b3l_hashr_long` inside `orig/hashr.o`!
        with open(os.path.join(bdir, "hashr.o"), "rb") as f:
            long_elf = ode_audit.rename_elf_symbol(f.read(), "b3l_hashr", "b3l_hashr_long")
        long_o = os.path.join(bdir, "hashr_long.o")
        with open(long_o, "wb") as f:
            f.write(long_elf)

        # Build the 3 new fast objects.
        pad_o = os.path.join(d, "pad_fast.o"); odec.build(src, "pad_fast", pad_o)
        chk_o = os.path.join(d, "chunk_node_fast.o"); odec.build(src, "chunk_node_fast", chk_o)
        hsh_o = os.path.join(d, "hashr_fast.o"); odec.build(src, "hashr_fast", hsh_o)

        # Load kept proofs.
        kept_prf = {}
        for nm in KEPT_INNER:
            with open(os.path.join(PC, "proofs", nm + ".proof"), "r", encoding="utf-8") as f:
                kept_prf[nm] = f.read()
        with open(os.path.join(PC, "proofs", "b3l_hashr.proof"), "r", encoding="utf-8") as f:
            kept_prf["b3l_hashr_long"] = f.read().replace("for b3l_hashr\n", "for b3l_hashr_long\n", 1)

        # Check if `b3l_hashr_long` with `stack 18672` passes with the kept proof directly!
        obj_for = {
            "blake3_servil_compress_in_place_sse41": os.path.join(bdir, "one_sse41.o"),
            "blake3_servil_compress_in_place_avx512": os.path.join(bdir, "one.o"),
            "blake3_servil_avx512_k32": os.path.join(bdir, "k32.o"),
            "blake3_servil_avx512_p16": os.path.join(bdir, "p16.o"),
            "blake3_servil_avx512_p32": os.path.join(bdir, "k32.o"),
            "b3l_pad": os.path.join(bdir, "pad.o"),
            "b3l_node_out": os.path.join(bdir, "node_out.o"),
            "b3l_chunk_node": os.path.join(bdir, "chunk_node.o"),
            "b3l_wide32": os.path.join(bdir, "wide32.o"),
            "b3l_wide128": os.path.join(bdir, "wide128.o"),
            "b3l_take": os.path.join(bdir, "take.o"),
            "b3l_part32": os.path.join(bdir, "part32.o"),
            "b3l_subtree": os.path.join(bdir, "subtree.o"),
            "b3l_hashr_long": long_o,
        }
        kept_pairs_14 = [(obj_for[n], n) for n in KEPT_INNER + ["b3l_hashr_long"]]
        long_prf_path = os.path.join(d, "long14.prf")
        with open(long_prf_path, "w", encoding="utf-8") as f:
            for _, n in kept_pairs_14:
                f.write(kept_prf[n])
        ok_long, msg_long = lean_verify.verify(full_spec, kept_pairs_14, long_prf_path)
        print(f"CHECK b3l_hashr_long (stack 18672) with kept proof: ok={ok_long} msg={msg_long!r}", flush=True)
        if not ok_long:
            return 1

        # Prove `b3l_pad_fast` and `b3l_chunk_node_fast` cleanly with minimal callees.
        kept_2 = [(obj_for["blake3_servil_compress_in_place_sse41"], "blake3_servil_compress_in_place_sse41"),
                  (obj_for["blake3_servil_compress_in_place_avx512"], "blake3_servil_compress_in_place_avx512")]
        pad_prf = prove_one_with_kept(full_spec, [], kept_prf, pad_o, "b3l_pad_fast", odec.places(src, "pad_fast"), d)
        kept_prf["b3l_pad_fast"] = pad_prf
        chk_prf = prove_one_with_kept(
            full_spec, kept_2 + [(pad_o, "b3l_pad_fast")], kept_prf,
            chk_o, "b3l_chunk_node_fast", "", d,
        )
        kept_prf["b3l_chunk_node_fast"] = chk_prf

        # Prove `b3l_hashr` (fast wrapper!) — only needs direct callees + closure!
        hsh_prf = prove_one_with_kept(
            full_spec,
            kept_pairs_14 + [(pad_o, "b3l_pad_fast"), (chk_o, "b3l_chunk_node_fast")],
            kept_prf,
            hsh_o, "b3l_hashr", "", d,
        )
        kept_prf["b3l_hashr"] = hsh_prf

        # Save the 3 new proof files!
        for nm, txt in [
            ("b3l_pad_fast.proof", pad_prf),
            ("b3l_chunk_node_fast.proof", chk_prf),
            ("b3l_hashr_fast.proof", hsh_prf),
        ]:
            with open(os.path.join(HERE, nm), "w", encoding="utf-8") as f:
                f.write(txt)

        # Pack ALL 16 functions into ONE self-contained ELF64 `.o` + `.proof` and audit!
        order16 = KEPT_INNER + ["b3l_hashr_long", "b3l_pad_fast", "b3l_chunk_node_fast", "b3l_hashr"]
        unit_files = [
            os.path.join(bdir, "one_sse41.o"),
            os.path.join(bdir, "one.o"),
            os.path.join(bdir, "k32.o"),
            os.path.join(bdir, "p16.o"),
            os.path.join(bdir, "pad.o"),
            os.path.join(bdir, "node_out.o"),
            os.path.join(bdir, "chunk_node.o"),
            os.path.join(bdir, "wide32.o"),
            os.path.join(bdir, "wide128.o"),
            os.path.join(bdir, "take.o"),
            os.path.join(bdir, "part32.o"),
            os.path.join(bdir, "subtree.o"),
            long_o,
            pad_o,
            chk_o,
            hsh_o,
        ]
        unit_elfs = []
        for uf in unit_files:
            with open(uf, "rb") as f:
                unit_elfs.append(f.read())
        comb_prf = os.path.join(d, "all16.prf")
        with open(comb_prf, "w", encoding="utf-8") as f:
            for nm in order16:
                f.write(kept_prf[nm])
        out_o = os.path.join(d, "b3hashr_fast_bundle.o")
        out_p = os.path.join(d, "b3hashr_fast_bundle.proof")
        res = ode_audit.pack_bundle(
            unit_elfs, order16, "b3l_hashr", full_spec, out_o, out_p,
            existing_proof_path=comb_prf,
        )
        print(ode_audit.format_audit_report(res))
        if res["verdict"] != "shown":
            return 1
        if emit_s:
            with open(out_o, "rb") as f:
                ob = f.read()
            emit_settled_s(ob, res["symbol"], emit_s, res["contract_b32"], res["binary_b32"])
            print(f"WROTE settled assembly: {emit_s} ({os.path.getsize(emit_s)} B)")
        return 0


if __name__ == "__main__":
    sys.exit(main())
