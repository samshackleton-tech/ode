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


if __name__ == "__main__":
    unittest.main()
