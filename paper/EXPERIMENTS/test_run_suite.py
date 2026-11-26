#!/usr/bin/env pypy3
"""Unit tests for the automated pre-registered experiment harness (`run_suite.py`)."""
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import run_suite


class TestRunSuite(unittest.TestCase):
    def test_01_quickstart_leakage_guard_refuses_ct_eq_and_allows_unseen(self):
        with (HERE / "tasks" / "ct_eq.json").open("r", encoding="utf-8") as f:
            ct_eq = json.load(f)
        with self.assertRaises(SystemExit) as ctx:
            run_suite.check_quickstart_leakage([ct_eq])
        self.assertIn("overlaps docs/QUICKSTART.md", str(ctx.exception))

        for tid in ("ebpf", "ct_count"):
            with (HERE / "tasks" / f"{tid}.json").open("r", encoding="utf-8") as f:
                task = json.load(f)
            run_suite.check_quickstart_leakage([task])

    def test_02_progressive_results_writes_in_progress_then_complete(self):
        orig_exp = run_suite.EXP_DIR
        try:
            with tempfile.TemporaryDirectory() as td:
                run_suite.EXP_DIR = Path(td)
                tasks = [{"id": "t1"}]
                models = ["m1"]
                targets = ["x86_64", "arm64"]
                c1 = {
                    "task": "t1", "model": "m1", "target": "x86_64", "strict_pass": True,
                    "rounds_to_pass": 1, "stopped_reason": None, "total_cost_usd": 0.1,
                    "verify2_pass": True, "native_status": "pass", "native_detail": "NATIVE_PASS 5/5",
                    "final_metrics": {"functions": 1, "instructions": 10, "code_bytes": 40},
                    "rounds": [{"category": "passed"}],
                }
                c2 = {
                    "task": "t1", "model": "m1", "target": "arm64", "strict_pass": False,
                    "rounds_to_pass": None, "stopped_reason": "consecutive_truncations_2",
                    "total_cost_usd": 0.2, "verify2_pass": None, "native_status": "not_run",
                    "native_detail": None, "final_metrics": {},
                    "rounds": [{"category": "output_token_limit"}, {"category": "output_token_limit"}],
                }
                jp, mp = run_suite.write_results("utest", "0" * 40, tasks, models, targets, [c1], None, expected_total=2)
                d1 = json.loads(jp.read_text(encoding="utf-8"))
                self.assertEqual(d1["status"], "in_progress")
                self.assertEqual(d1["completed_cells"], 1)
                self.assertEqual(d1["total_cells"], 2)
                self.assertIn("in progress: 1/2 cells finished", mp.read_text(encoding="utf-8"))

                jp, mp = run_suite.write_results("utest", "0" * 40, tasks, models, targets, [c1, c2], None, expected_total=2)
                d2 = json.loads(jp.read_text(encoding="utf-8"))
                self.assertEqual(d2["status"], "complete")
                self.assertEqual(d2["completed_cells"], 2)
                self.assertEqual(d2["cells"][0]["stopped_reason"], "consecutive_truncations_2")
                self.assertNotIn("in progress:", mp.read_text(encoding="utf-8"))
        finally:
            run_suite.EXP_DIR = orig_exp

    def test_03_parse_advise_excludes_callees_and_arm_baseline(self):
        adv = (
            "  loop 0: +0x10..+0x50 lines 10..20 — 12 ins, 48 B, 1 i-cache line(s), >= 3.0 cyc/iter (ports) | "
            "pipeline sim ~4.50 cyc/iter (ports:ALU0, 2 fused, 1.12 cyc/B across 4 load(s)/4 B, excludes 4 callee(s))\n"
            "      zen5    : ~ 4.50 cyc/iter, 1.12 cyc/B [ports:ALU0]\n"
        )
        m = run_suite.parse_advise_metrics(adv, "x86_64")
        self.assertEqual(m["hot_loop"], 0)
        self.assertAlmostEqual(m["cyc_per_b"], 1.12)
        self.assertEqual(m["excludes_callees"], 4)

        adv_multi = (
            "  loop 0: +0x34..+0x74 lines 68..84 — 16 ins, 64 B, 1 i-cache line(s), >= 6.0 cyc/iter (critical_path) | "
            "pipeline sim ~3.50 cyc/iter (ports:I4, 6 fused, 3.50 cyc/B across 1 load(s)/1 B)\n"
            "  loop 1: +0x34..+0x188 lines 68..157 — 85 ins, 340 B, 4 i-cache line(s), >= 22.0 cyc/iter (branch_throughput) | "
            "pipeline sim ~22.00 cyc/iter (ports:I4, 22 fused, 1.00 cyc/B across 8 load(s)/22 B, excludes 4 callee(s)) "
            "[secondary back-edge to +0x34; slice spans multiple paths]\n"
        )
        m2 = run_suite.parse_advise_metrics(adv_multi, "arm64")
        self.assertEqual(m2["hot_loop"], 0)
        self.assertEqual(m2["load_bytes"], 1)
        self.assertAlmostEqual(m2["cyc_per_b"], 3.50)

        orig_exp = run_suite.EXP_DIR
        try:
            with tempfile.TemporaryDirectory() as td:
                run_suite.EXP_DIR = Path(td)
                base_cells = [
                    {"task": "t1", "model": "m1", "target": "x86_64", "arm": "blind", "strict_pass": True,
                     "rounds_to_pass": 1, "total_cost_usd": 0.5, "rounds_used": 2, "round_categories": ["passed", "passed"]},
                    {"task": "t1", "model": "m1", "target": "x86_64", "arm": "advised", "strict_pass": False,
                     "rounds_to_pass": None, "total_cost_usd": 0.8, "rounds_used": 4, "round_categories": ["other"] * 4},
                ]
                bp = Path(td) / "base.json"
                bp.write_text(json.dumps({"run_id": "v1", "cells": base_cells}), encoding="utf-8")
                cur_cells = [
                    {"task": "t1", "model": "m1", "target": "x86_64", "arm": "blind", "strict_pass": True,
                     "rounds_to_pass": 1, "total_cost_usd": 0.4, "verify2_pass": True, "native_status": "pass",
                     "native_detail": "NATIVE_PASS 1/1", "final_metrics": {}, "rounds": [{"category": "passed"}]},
                    {"task": "t1", "model": "m1", "target": "x86_64", "arm": "advised", "strict_pass": True,
                     "rounds_to_pass": 2, "total_cost_usd": 0.6, "verify2_pass": True, "native_status": "pass",
                     "native_detail": "NATIVE_PASS 1/1", "final_metrics": {}, "rounds": [{"category": "other"}, {"category": "passed"}]},
                ]
                _, mp = run_suite.write_results("v2", "0" * 40, [{"id": "t1"}], ["m1"], ["x86_64"], cur_cells, bp, expected_total=2)
                md = mp.read_text(encoding="utf-8")
                self.assertIn("| Strict passes | 1/2 | 2/2 | +1 |", md)
                self.assertIn("| `t1` | `m1` | `x86_64` | `advised` | FAIL ($0.80) | PASS (R2, $0.60) |", md)
        finally:
            run_suite.EXP_DIR = orig_exp

    def test_04_regression_presets_valid_and_no_quickstart_overlap(self):
        for preset_name, want_tasks, want_models in [
            ("regression-v1", 4, 9),
            ("regression-v1-efficient", 4, 6),
        ]:
            path, data = run_suite.load_preset(preset_name)
            self.assertTrue(path.exists())
            self.assertEqual(len(data["tasks"]), want_tasks)
            self.assertEqual(len(data["models"]), want_models)
            tasks = []
            for tid in data["tasks"]:
                tp = run_suite.TASKS_DIR / f"{tid}.json"
                self.assertTrue(tp.exists(), f"missing task {tid}")
                with tp.open("r", encoding="utf-8") as f:
                    t = json.load(f)
                self.assertTrue((run_suite.ROOT / t["spec_file"]).exists())
                self.assertTrue((run_suite.ROOT / t["reference_solution"]).exists())
                self.assertTrue((run_suite.ROOT / t["native_harness"]).exists())
                tasks.append(t)
            run_suite.check_quickstart_leakage(tasks)

        with self.assertRaises(SystemExit):
            run_suite.load_preset("does-not-exist-preset")

    def test_05_lpt_schedule_provider_sort_and_ref_cache(self):
        jobs = [
            ({"id": "ipv4_valid"}, "anthropic/claude-haiku-5.5", "x86_64", "advised"),
            ({"id": "chacha20_4way"}, "anthropic/claude-fable-5.2", "arm64", "advised"),
            ({"id": "der_valid"}, "openai/gpt-6.2-astra-pro", "x86_64", "advised"),
        ]
        ordered = run_suite.schedule_jobs_lpt(jobs)
        self.assertEqual(ordered[0][0]["id"], "chacha20_4way")
        self.assertEqual(ordered[0][1], "anthropic/claude-fable-5.2")
        self.assertEqual(ordered[-1][0]["id"], "ipv4_valid")
        # Cache key changes when task/target changes and stays deterministic across repeated calls
        with (run_suite.TASKS_DIR / "ipv4_valid.json").open("r", encoding="utf-8") as f:
            t_ip = json.load(f)
        k1 = run_suite._ref_cache_key(t_ip, "x86_64")
        k2 = run_suite._ref_cache_key(t_ip, "x86_64")
        k3 = run_suite._ref_cache_key(t_ip, "arm64")
        self.assertEqual(k1, k2)
        self.assertNotEqual(k1, k3)

    def test_06_opt_rounds_cap_and_non_loop_skip(self):
        """Post-pass opt rounds stop immediately when `cyc/B` is None, and failed opt rounds consume `opt_rounds`."""
        import threading, types
        with (run_suite.TASKS_DIR / "der_valid.json").open("r", encoding="utf-8") as f:
            task = json.load(f)

        orig_api = run_suite.call_openrouter
        orig_tool = run_suite.run_tool
        orig_adv = run_suite.run_static_advise
        orig_v2 = run_suite.run_verify2_on_bundle
        orig_nat = run_suite.run_native_test
        orig_exp = run_suite.expected_contract_id_for
        try:
            run_suite.expected_contract_id_for = lambda t, tgt: "a" * 52
            run_suite.run_verify2_on_bundle = lambda o, p, tgt: (True, "shown", 0.01)
            run_suite.run_native_test = lambda o, t, tgt, x, a=None: ("pass", "NATIVE_PASS")
            args = types.SimpleNamespace(
                run_id="t6", max_rounds=8, opt_rounds=2, max_usd=10.0, cell_timeout=0,
                temperature=0.2, max_tokens=2048, effort="medium", api_timeout=30,
                x86_exec_script=None, arm64_exec_script=None, provider_sort="throughput",
            )
            # Case A: non-loop task (`cpb is None`) stops immediately on R1 (0 wasted opt rounds!)
            calls = [0]
            def fake_api_a(*a, **kw):
                calls[0] += 1
                return "```ode\nfn der_valid() { return 0 }\n```", {"cost": 0.01}, 0.1
            def fake_tool_a(cmd, work):
                if "pack" in cmd:
                    (work / "out.o").write_bytes(b"o")
                    (work / "out.proof").write_bytes(b"p")
                return 0, "VERDICT:           shown\nFUNCTIONS: 1\nINSTRUCTIONS: 10\nCODE_BYTES: 40\n", 0.01
            run_suite.call_openrouter = fake_api_a
            run_suite.run_tool = fake_tool_a
            run_suite.run_static_advise = lambda *a, **kw: ("fn der_valid: no loops\n", {"cyc_per_b": None})
            with tempfile.TemporaryDirectory() as td:
                c = run_suite.run_cell(
                    task, "m1", "x86_64", args, "k",
                    run_suite.BudgetGuard(10.0), Path(td), threading.BoundedSemaphore(2), arm="advised",
                )
            self.assertTrue(c["strict_pass"])
            self.assertEqual(len(c["rounds"]), 1)
            self.assertEqual(calls[0], 1)

            # Case B: loop task (`cpb = 1.50`) where R2 & R3 opt attempts FAIL stops after exactly 2 opt rounds (3 total!)
            calls[0] = 0
            def fake_tool_b(cmd, work):
                if "pack" in cmd:
                    if calls[0] == 1:
                        (work / "out.o").write_bytes(b"o")
                        (work / "out.proof").write_bytes(b"p")
                        return 0, "VERDICT:           shown\nFUNCTIONS: 1\nINSTRUCTIONS: 10\nCODE_BYTES: 40\n", 0.01
                    return 1, "refused in opt attempt", 0.01
                return 0, "VERDICT:           shown\nFUNCTIONS: 1\nINSTRUCTIONS: 10\nCODE_BYTES: 40\n", 0.01
            run_suite.run_tool = fake_tool_b
            run_suite.run_static_advise = lambda *a, **kw: ("loop 0: 1.50 cyc/B\n", {"cyc_per_b": 1.5, "load_bytes": 1})
            with tempfile.TemporaryDirectory() as td:
                c = run_suite.run_cell(
                    task, "m1", "x86_64", args, "k",
                    run_suite.BudgetGuard(10.0), Path(td), threading.BoundedSemaphore(2), arm="advised",
                )
            self.assertTrue(c["strict_pass"])
            self.assertEqual(len(c["rounds"]), 3)
            self.assertEqual(calls[0], 3)
        finally:
            run_suite.call_openrouter = orig_api
            run_suite.run_tool = orig_tool
            run_suite.run_static_advise = orig_adv
            run_suite.run_verify2_on_bundle = orig_v2
            run_suite.run_native_test = orig_nat
            run_suite.expected_contract_id_for = orig_exp


if __name__ == "__main__":
    unittest.main()
