#!/usr/bin/env python3
"""Self-test for the pre-registered AI coder experiment (paper/coder-exp/):
1. Every one of the 8 locked tasks has a reference Ode solution that passes Lean `odeverify` (`shown`).
2. Every one of the 8 locked tasks has a planted negative control that is refused (`verdict != "shown"`).
3. The evaluation harness (`run_experiment.py --mode mock`) runs end to end through `ode_tool.py serve`,
   produces valid JSONL records, enforces Arm A vs Arm C behavior, and computes summary statistics."""
import json, os, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
EXP = os.path.join(ROOT, "paper", "coder-exp")
sys.path.insert(0, HERE)
sys.path.insert(0, EXP)
import built, run_experiment, tasks


@unittest.skipUnless(built.LAKE is not None, "Lean toolchain not installed")
class CoderExperimentSelfTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")

    def test_all_8_tasks_reference_shown_and_negative_refused(self):
        self.assertEqual(len(tasks.TASKS), 8)
        targets = [t["target"] for t in tasks.TASKS]
        self.assertEqual(targets.count("x86_64"), 4)
        self.assertEqual(targets.count("arm64"), 4)
        worker = run_experiment.ToolWorker()
        try:
            with tempfile.TemporaryDirectory() as td:
                for task in tasks.TASKS:
                    sp = os.path.join(td, f"{task['id']}.spec")
                    gp = os.path.join(td, f"{task['id']}_good.ode")
                    bp = os.path.join(td, f"{task['id']}_bad.ode")
                    with open(sp, "w") as f: f.write(task["spec"])
                    with open(gp, "w") as f: f.write(task["reference"])
                    with open(bp, "w") as f: f.write(task["negative"])
                    with self.subTest(task=task["id"], kind="reference"):
                        resp, _ = worker.check(gp, sp)
                        self.assertTrue(resp["ok"], f"{task['id']} reference failed: {resp}")
                        self.assertEqual(resp["result"]["verdict"], "shown")
                    with self.subTest(task=task["id"], kind="negative"):
                        resp, _ = worker.check(bp, sp)
                        self.assertFalse(resp["ok"], f"{task['id']} negative unexpectedly passed!")
        finally:
            worker.close()

    def test_mock_harness_end_to_end(self):
        with tempfile.TemporaryDirectory() as td:
            out_path = os.path.join(td, "mock.jsonl")
            rc = run_experiment.main([
                "--mode", "mock",
                "--models", "mock/tiny-coder",
                "--arms", "arm_a", "arm_c",
                "--tasks", "T1_x86_mix_step", "T4_arm_lead_zeros",
                "--max-turns", "2",
                "--out", out_path,
            ])
            self.assertEqual(rc, 0)
            with open(out_path) as f:
                recs = [json.loads(l) for l in f if l.strip()]
            self.assertEqual(len(recs), 4)
            by_key = {(r["arm"], r["task_id"]): r for r in recs}
            # In mock mode: Arm A stays on negative (fails); Arm C repairs on turn 2 (passes!)
            self.assertFalse(by_key[("arm_a", "T1_x86_mix_step")]["passed"])
            self.assertFalse(by_key[("arm_a", "T4_arm_lead_zeros")]["passed"])
            self.assertTrue(by_key[("arm_c", "T1_x86_mix_step")]["passed"])
            self.assertEqual(by_key[("arm_c", "T1_x86_mix_step")]["passed_turn"], 2)
            self.assertTrue(by_key[("arm_c", "T4_arm_lead_zeros")]["passed"])
            self.assertEqual(by_key[("arm_c", "T4_arm_lead_zeros")]["passed_turn"], 2)


if __name__ == "__main__":
    unittest.main()
