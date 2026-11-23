#!/usr/bin/env python3
"""Tests for advice/estimate.py: static bounds, concrete memory traces, all five Layer-1
hazard classes (positive and negative controls), L1D LRU simulation, variant comparison,
and budget enforcement. Runs offline under CPython and PyPy without Lean."""
import os, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (HERE, os.path.join(ROOT, "lang"), os.path.join(ROOT, "arm64"), os.path.join(ROOT, "core")):
    if d not in sys.path:
        sys.path.insert(0, d)
import estimate, odec


def _compile_and_decode(src_text, fn_names):
    with tempfile.TemporaryDirectory() as d:
        src_path = os.path.join(d, "prog.ode")
        with open(src_path, "w") as f:
            f.write(src_text)
        target, _, _, _ = odec.source(src_text, src_path)
        progs, lmaps, frames = {}, {}, {}
        for name in fn_names:
            info = odec.compile_info(src_path, name)
            sym = info["symbol"]
            obj_path = os.path.join(d, f"{sym}.o")
            with open(obj_path, "wb") as f:
                f.write(info["elf"])
            _, dec = estimate.decode_object(obj_path, sym, target)
            progs[sym] = dec
            lmaps[sym] = info["line_map"]
            frames[sym] = info["frame"]
        return target, progs, lmaps, frames


class StaticTests(unittest.TestCase):
    def test_arm_mix_apple_vs_ampere_icache_lines(self):
        src = os.path.join(ROOT, "proof-core", "examples", "arm64", "mix.ode")
        info = odec.compile_info(src, "mix16_6")
        with tempfile.TemporaryDirectory() as d:
            op = os.path.join(d, "mix.o")
            with open(op, "wb") as f:
                f.write(info["elf"])
            _, dec = estimate.decode_object(op, "arm_mix16_6", "arm64")
        rep_apple = estimate.static_analyze(dec, "arm64", "apple_m", info["line_map"], info["frame"])
        rep_amp = estimate.static_analyze(dec, "arm64", "ampere1", info["line_map"], info["frame"])
        self.assertEqual(rep_apple["whole"]["instructions"], 26)
        self.assertEqual(rep_apple["code_bytes"], 104)
        self.assertEqual(rep_apple["frame_bytes"], 96)
        # 104 bytes fits in 1 Apple M 128 B cache line, but needs 2 AmpereOne 64 B cache lines
        self.assertEqual(rep_apple["icache_lines"], 1)
        self.assertEqual(rep_amp["icache_lines"], 2)
        self.assertGreater(rep_apple["whole"]["compute_lower_bound"], 0)
        self.assertGreater(rep_amp["whole"]["compute_lower_bound"], 0)

    def test_zen4_double_pumps_512bit_over_zen5(self):
        src = os.path.join(ROOT, "wide", "p16.ode")
        info = odec.compile_info(src, "p16")
        with tempfile.TemporaryDirectory() as d:
            op = os.path.join(d, "p16.o")
            with open(op, "wb") as f:
                f.write(info["elf"])
            _, dec = estimate.decode_object(op, info["symbol"], "x86_64")
        rep_z5 = estimate.static_analyze(dec, "x86_64", "zen5", info["line_map"], info["frame"])
        rep_z4 = estimate.static_analyze(dec, "x86_64", "zen4", info["line_map"], info["frame"])
        rep_ice = estimate.static_analyze(dec, "x86_64", "icelake", info["line_map"], info["frame"])
        # Zen 4 double-pumps 512-bit AVX-512 execution, so its vector throughput and compute bound exceed Zen 5's
        self.assertGreater(rep_z4["whole"]["unit_throughput"]["vec"], rep_z5["whole"]["unit_throughput"]["vec"])
        self.assertGreater(rep_z4["whole"]["compute_lower_bound"], rep_z5["whole"]["compute_lower_bound"])
        self.assertGreater(rep_ice["whole"]["compute_lower_bound"], 0)
        self.assertGreaterEqual(len(rep_z5["loops"]), 1)

    def test_adler32_loop_alignment_advice(self):
        src = os.path.join(ROOT, "kcheck", "programs", "adler32", "adler32.ode")
        info = odec.compile_info(src, "adler32")
        with tempfile.TemporaryDirectory() as d:
            op = os.path.join(d, "adler.o")
            with open(op, "wb") as f:
                f.write(info["elf"])
            _, dec = estimate.decode_object(op, info["symbol"], "x86_64")
        rep = estimate.static_analyze(dec, "x86_64", "zen5", info["line_map"], info["frame"])
        self.assertEqual(len(rep["loops"]), 1)
        lp = rep["loops"][0]
        # 108 bytes crossing 3 lines when misaligned -> aligning saves 1 i-cache line
        self.assertEqual(lp["icache_lines"], 3)
        self.assertEqual(lp["min_icache_lines"], 2)
        self.assertTrue(lp["align_saves_line"])


class HazardTests(unittest.TestCase):
    def test_line_split_and_page_crossing_arm64_sizes(self):
        # One 16-byte NEON load from [x1] and store to [x0]
        src = """target arm64
fn copy16 as "t_copy16" {
  ld1 {v0.4s}, [x1]
  st1 {v0.4s}, [x0]
  ret
}
"""
        target, progs, lmaps, frames = _compile_and_decode(src, ["copy16"])
        # 1. Aligned: 0 splits, 0 page crossings on both AmpereOne (64 B / 4 KiB) and Apple M (128 B / 16 KiB)
        tr0 = estimate.trace_memory(progs, "t_copy16", target,
                                    init_regs={"x0": 0x100000, "x1": 0x200400}, line_maps=lmaps)
        self.assertTrue(tr0["returned"])
        m_amp0 = estimate.analyze_memory(tr0, target, "ampere1")
        m_app0 = estimate.analyze_memory(tr0, target, "apple_m")
        self.assertEqual(m_amp0["line_splits"], 0)
        self.assertEqual(m_app0["line_splits"], 0)
        self.assertEqual(m_amp0["page_crossings"], 0)
        self.assertEqual(m_app0["page_crossings"], 0)

        # 2. Offset +60: crosses 64 B cache line (AmpereOne split!) but stays inside 128 B Apple M cache line!
        tr60 = estimate.trace_memory(progs, "t_copy16", target,
                                     init_regs={"x0": 0x100000, "x1": 0x200400 + 60}, line_maps=lmaps)
        m_amp60 = estimate.analyze_memory(tr60, target, "ampere1")
        m_app60 = estimate.analyze_memory(tr60, target, "apple_m")
        self.assertEqual(m_amp60["line_splits"], 1)
        self.assertEqual(m_app60["line_splits"], 0)

        # 3. Offset +4092: crosses 4 KiB page (AmpereOne page crossing!) but NOT 16 KiB Apple M page!
        tr4k = estimate.trace_memory(progs, "t_copy16", target,
                                     init_regs={"x0": 0x100000, "x1": 0x200000 + 4092}, line_maps=lmaps)
        m_amp4k = estimate.analyze_memory(tr4k, target, "ampere1")
        m_app4k = estimate.analyze_memory(tr4k, target, "apple_m")
        self.assertEqual(m_amp4k["page_crossings"], 1)
        self.assertEqual(m_amp4k["line_splits"], 1)
        self.assertEqual(m_app4k["page_crossings"], 0)
        self.assertEqual(m_app4k["line_splits"], 1)

        # 4. Offset +16380: crosses 16 KiB page on Apple M too!
        tr16k = estimate.trace_memory(progs, "t_copy16", target,
                                      init_regs={"x0": 0x100000, "x1": 0x200000 + 16380}, line_maps=lmaps)
        m_app16k = estimate.analyze_memory(tr16k, target, "apple_m")
        self.assertEqual(m_app16k["page_crossings"], 1)

    def test_stlf_clean_vs_partial_arm64(self):
        # Clean STLF: store 8 B to [sp], load 8 B from [sp]
        src_clean = """target arm64
fn clean as "t_clean" {
  sub sp, sp, 16
  str x0, [sp, 0]
  ldr x1, [sp, 0]
  add sp, sp, 16
  ret
}
"""
        # Partial STLF: two 8 B stores to [sp, 0] and [sp, 8], then one 16 B vector load from [sp]
        src_partial = """target arm64
fn partial as "t_partial" {
  sub sp, sp, 16
  str x0, [sp, 0]
  str x1, [sp, 8]
  add x2, sp, 0
  ld1 {v0.4s}, [x2]
  add sp, sp, 16
  ret
}
"""
        t1, p1, lm1, _ = _compile_and_decode(src_clean, ["clean"])
        mc = estimate.analyze_memory(estimate.trace_memory(p1, "t_clean", t1, line_maps=lm1), t1, "apple_m")
        self.assertEqual(mc["stlf_clean"], 1)
        self.assertEqual(mc["stlf_partial"], 0)

        t2, p2, lm2, _ = _compile_and_decode(src_partial, ["partial"])
        mp = estimate.analyze_memory(estimate.trace_memory(p2, "t_partial", t2, line_maps=lm2), t2, "apple_m")
        self.assertEqual(mp["stlf_partial"], 1)
        self.assertEqual(mp["details"]["stlf_partial"][0]["load_line"], 7)
        self.assertGreater(mp["hazard_cycles"], 0)

    def test_4k_aliasing_positive_and_negative_x86(self):
        # Store 8 B to [rdi], then immediately load 8 B from [rsi]
        src = """target x86_64
fn st_ld as "t_st_ld" {
  mov qword ptr [rdi], rdx
  mov rax, qword ptr [rsi]
  ret
}
"""
        target, progs, lmaps, _ = _compile_and_decode(src, ["st_ld"])
        # Positive: rdi and rsi share low 12 bits (0x100000 and 0x200000) -> 4K alias on Zen 5 and Ice Lake!
        tr_hit = estimate.trace_memory(progs, "t_st_ld", target,
                                       init_regs={"rdi": 0x100000, "rsi": 0x200000, "rdx": 7}, line_maps=lmaps)
        mz_hit = estimate.analyze_memory(tr_hit, target, "zen5")
        mi_hit = estimate.analyze_memory(tr_hit, target, "icelake")
        self.assertEqual(mz_hit["alias_4k"], 1)
        self.assertEqual(mi_hit["alias_4k"], 1)
        self.assertGreater(mz_hit["hazard_cycles"], 0)

        # Negative: rdi=0x100000, rsi=0x200400 -> different low 12 bits -> 0 aliases!
        tr_ok = estimate.trace_memory(progs, "t_st_ld", target,
                                      init_regs={"rdi": 0x100000, "rsi": 0x200400, "rdx": 7}, line_maps=lmaps)
        mz_ok = estimate.analyze_memory(tr_ok, target, "zen5")
        self.assertEqual(mz_ok["alias_4k"], 0)
        self.assertEqual(mz_ok["hazard_cycles"], 0)

    def test_l1d_set_conflict_detection(self):
        # Zen 5 L1D: 48 KiB, 12 ways, 64 B lines -> 64 sets -> stride 4096 B maps every access to set 0!
        def make_trace(n_lines):
            # Access n_lines twice so warm-cache simulation measures conflict evictions
            accs = []
            for pass_i in range(2):
                for j in range(n_lines):
                    accs.append({
                        "step": pass_i * n_lines + j, "fn": "f", "pc": 0, "kind": "R",
                        "addr": 0x100000 + j * 4096, "size": 8, "file": "f.ode", "line": 1, "typed": "mov",
                    })
            return {"steps": len(accs), "returned": True, "fault": None, "accesses": accs,
                    "dyn_ops": [], "final_regs": {}, "sp_entry": 0x70000000}

        # 8 lines in set 0 fits inside 12 ways -> no conflict, 0 warm misses
        m_fit = estimate.analyze_memory(make_trace(8), "x86_64", "zen5")
        self.assertFalse(m_fit["l1d_set_conflict"])
        self.assertEqual(m_fit["l1d_max_set_depth"], 8)
        self.assertEqual(m_fit["l1d_warm_misses"], 0)
        self.assertEqual(m_fit["l1d_cold_misses"], 8)

        # 14 lines in set 0 exceeds 12 ways -> set conflict + warm misses!
        m_ov = estimate.analyze_memory(make_trace(14), "x86_64", "zen5")
        self.assertTrue(m_ov["l1d_set_conflict"])
        self.assertEqual(m_ov["l1d_max_set_depth"], 14)
        self.assertGreater(m_ov["l1d_warm_misses"], 0)

    def test_trace_across_arm64_calls_and_compare_and_budgets(self):
        src = os.path.join(ROOT, "proof-core", "examples", "arm64", "mix.ode")
        progs, lmaps, frames = {}, {}, {}
        with tempfile.TemporaryDirectory() as d:
            for name in ("mix16_3", "mix16_again", "mix16_6"):
                info = odec.compile_info(src, name)
                sym = info["symbol"]
                op = os.path.join(d, f"{sym}.o")
                with open(op, "wb") as f:
                    f.write(info["elf"])
                _, dec = estimate.decode_object(op, sym, "arm64")
                progs[sym] = dec
                lmaps[sym] = info["line_map"]
                frames[sym] = info["frame"]
        st = estimate.static_analyze(progs["arm_mix16_6"], "arm64", "ampere1", lmaps["arm_mix16_6"], frames["arm_mix16_6"])
        tr_good = estimate.trace_memory(progs, "arm_mix16_6", "arm64",
                                        init_regs={"x0": 0x100000, "x1": 0x110400, "x2": 0x120800}, line_maps=lmaps)
        tr_bad = estimate.trace_memory(progs, "arm_mix16_6", "arm64",
                                       init_regs={"x0": 0x100007, "x1": 0x110407, "x2": 0x120807}, line_maps=lmaps)
        mg = estimate.analyze_memory(tr_good, "arm64", "ampere1", frames["arm_mix16_6"])
        mb = estimate.analyze_memory(tr_bad, "arm64", "ampere1", frames["arm_mix16_6"])
        self.assertTrue(mg["returned"])
        self.assertEqual(mg["steps"], 118)
        self.assertEqual(mg["line_splits"], 0)
        self.assertEqual(mb["line_splits"], 4)
        self.assertGreater(mb["est_warm_cycles"], mg["est_warm_cycles"])

        cmp_text = estimate.compare_reports("aligned", st, mg, "unaligned", st, mb)
        self.assertIn("cache-line splits", cmp_text)
        self.assertIn("est warm-L1 total (cyc)", cmp_text)

        self.assertEqual(estimate.check_budgets(st, mg, {"max_bytes": 128, "max_line_splits": 0}), [])
        errs = estimate.check_budgets(st, mb, {"max_bytes": 64, "max_line_splits": 0})
        self.assertEqual(len(errs), 2)
        self.assertTrue(any("max_bytes" in e for e in errs))
        self.assertTrue(any("max_line_splits" in e for e in errs))

    def test_calibrate_predictions_offline(self):
        import calibrate
        with tempfile.TemporaryDirectory() as d:
            _, pairs_x86 = calibrate.predict_x86("zen5", d)
            _, pairs_arm = calibrate.predict_arm64("ampere1", d)
        by_x = {p["name"]: p for p in pairs_x86}
        self.assertGreater(by_x["p16_align"]["pred_b_warm"], by_x["p16_align"]["pred_a_warm"])
        self.assertGreater(by_x["alias_4k"]["pred_b_warm"], by_x["alias_4k"]["pred_a_warm"])
        self.assertGreater(by_x["stlf_width"]["pred_b_warm"], by_x["stlf_width"]["pred_a_warm"])
        self.assertGreater(by_x["l1d_set_conflict"]["pred_b_warm"], by_x["l1d_set_conflict"]["pred_a_warm"])
        by_a = {p["name"]: p for p in pairs_arm}
        self.assertGreater(by_a["arm_mix_align"]["pred_b_warm"], by_a["arm_mix_align"]["pred_a_warm"])
        self.assertGreater(by_a["arm_stlf_width"]["pred_b_warm"], by_a["arm_stlf_width"]["pred_a_warm"])
        self.assertGreater(by_a["arm_l1d_conflict"]["pred_b_warm"], by_a["arm_l1d_conflict"]["pred_a_warm"])


if __name__ == "__main__":
    unittest.main()
