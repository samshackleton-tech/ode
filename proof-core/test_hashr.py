#!/usr/bin/env pypy3
"""Verify the entire single-threaded BLAKE3 binary (`../kcheck/b3hashr.o` — all 14 functions,
3,761 machine instructions = 100% of the object file) in ONE `odeverify` call under the Lean 4
soundness theorem, together with negative controls for every new rule (recursion, value arrays,
stack bounds, processor features, trace independence, and code mutations).

    pypy3 test_hashr.py        (skipped where Lean's `lake` is not installed)

The 14 functions verified together in topological order:
  1. blake3_servil_compress_in_place_sse41   ( 94 insns)
  2. blake3_servil_compress_in_place_avx512  ( 76 insns)
  3. blake3_servil_avx512_k32                (702 insns)
  4. blake3_servil_avx512_p16                (460 insns)
  5. blake3_servil_avx512_p32                (699 insns)
  6. b3l_pad                                 ( 39 insns)
  7. b3l_node_out                            ( 18 insns)
  8. b3l_chunk_node                          ( 81 insns)
  9. b3l_wide32                              (259 insns)
 10. b3l_wide128                             (670 insns)
 11. b3l_take                                (133 insns, recursive, value array `cvs`)
 12. b3l_part32                              ( 76 insns, passes frame value array to `b3l_take`)
 13. b3l_subtree                             (189 insns, recursive)
 14. b3l_hashr                               (265 insns, top-level entry point in `blake3.spec`)
Total: 14 of 14 functions, 3,761 of 3,761 instructions (100%).
"""
import os, re, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE)
sys.path.insert(0, KCHECK)
sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, session, statement

OBJ = os.path.join(KCHECK, "b3hashr.o")
ORDER = [
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
    "b3l_hashr",
]
EXPECTED_INSNS = {
    "blake3_servil_compress_in_place_sse41": 94,
    "blake3_servil_compress_in_place_avx512": 76,
    "blake3_servil_avx512_k32": 702,
    "blake3_servil_avx512_p16": 460,
    "blake3_servil_avx512_p32": 699,
    "b3l_pad": 39,
    "b3l_node_out": 18,
    "b3l_chunk_node": 81,
    "b3l_wide32": 259,
    "b3l_wide128": 670,
    "b3l_take": 133,
    "b3l_part32": 76,
    "b3l_subtree": 189,
    "b3l_hashr": 265,
}
FUNCTIONS = [(OBJ, name) for name in ORDER]


def contract_of(text, name):
    (found,) = re.findall(rf"^contract {name}\(.*?^\}}\n", text, re.S | re.M)
    return found


def full_spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f:
        spec = f.read()
    with open(os.path.join(KCHECK, "proofs", "inner.spec")) as f:
        inner = f.read()
    layouts = "\n".join(re.findall(r"^layout .*$", inner, re.M))
    contracts = "\n".join(contract_of(inner, n) for n in ORDER if n != "b3l_hashr")
    return change(spec + "\n" + layouts + "\n" + contracts)


def combined_proof(names=ORDER):
    parts = []
    for name in names:
        with open(os.path.join(HERE, "proofs", name + ".proof")) as f:
            parts.append(f.read())
    return "".join(parts)


def once(old, new):
    def edit(t):
        assert t.count(old) == 1, f"expected 1 occurrence of {old!r}, got {t.count(old)}"
        return t.replace(old, new, 1)
    return edit


def verify_subset(spec, names, obj_override=None, proof_text=None):
    fns = [(obj_override.get(n, OBJ) if obj_override else OBJ, n) for n in names]
    with tempfile.TemporaryDirectory() as d:
        st = os.path.join(d, "s")
        pf = os.path.join(d, "p")
        lines = statement.statement(spec, fns)
        with open(st, "w") as f:
            f.write("\n".join(lines) + "\n")
        with open(pf, "w") as f:
            f.write(combined_proof(names) if proof_text is None else proof_text)
        r = subprocess.run([os.path.join(HERE, ".lake", "build", "bin", "odeverify"),
                            os.path.join(HERE, "..", "core", "x86.tab"), st, pf],
                           capture_output=True, text=True)
        return r.returncode == 0, (r.stdout + r.stderr).strip()


def verify_only(spec, target, names, obj_override=None):
    """Run `odeprove --only TARGET` (via `session.Session`) on a single function (with its
    callees' contracts present) using the kept proof for TARGET: fast, exact negative-control check."""
    fns = [(obj_override.get(n, OBJ) if obj_override else OBJ, n) for n in names]
    with tempfile.TemporaryDirectory() as d:
        st = os.path.join(d, "s")
        lines = statement.statement(spec, fns)
        with open(st, "w") as f:
            f.write("\n".join(lines) + "\n")
        with open(os.path.join(HERE, "proofs", target + ".proof")) as f:
            pftext = f.read().splitlines()
        assert pftext and pftext[0] == f"for {target}"
        sess = session.Session(st, [pftext[0]], target, only=True)
        try:
            out = sess.ask(pftext[1:]).strip()
        finally:
            sess.close()
        return out == "shown", out


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class FullHashr(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        built.built("odeprove")
        cls.dir = tempfile.mkdtemp(prefix="odehashr-")
        with open(os.path.join(KCHECK, "hash.ode")) as f:
            cls.source = f.read()

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def test_statement_covers_all_14_functions_and_3761_instructions(self):
        lines = statement.statement(full_spec_text(), FUNCTIONS)
        counts = {}
        cur = None
        for l in lines:
            if l.startswith("fn "):
                cur = l.split()[1]
                counts[cur] = 0
            elif cur and l.startswith("i "):
                counts[cur] += 1
        self.assertEqual(counts, EXPECTED_INSNS)
        self.assertEqual(sum(counts.values()), 3761)

    def test_all_14_functions_verified_in_one_odeverify_call(self):
        ok, out = verify_subset(full_spec_text(), ORDER)
        self.assertTrue(ok, out)
        self.assertEqual(out, "shown")

    def test_stronger_trace_contract_without_flags_on_b3l_hashr(self):
        # b3l_hashr's trace depends only on len and plat (not even on flags or key or input).
        spec = full_spec_text(once("trace depends on len, flags, plat", "trace depends on len, plat"))
        ok, out = verify_only(spec, "b3l_hashr", ORDER)
        self.assertTrue(ok, out)
        self.assertEqual(out, "shown")

    def test_false_contracts_are_refused(self):
        take_deps = ORDER[:ORDER.index("b3l_take") + 1]
        part_deps = ORDER[:ORDER.index("b3l_part32") + 1]
        sub_deps = ORDER[:ORDER.index("b3l_subtree") + 1]
        cases = [
            # Value-array entry expression and bounds
            ("b3l_take wrong chunk counter t + i + 1 in cvs",
             "b3l_take", take_deps,
             once("chunk_node(kf.key, t + i, kf.flags, input[1024 * i .. 1024 * i + 1024])",
                  "chunk_node(kf.key, t + i + 1, kf.flags, input[1024 * i .. 1024 * i + 1024])")),
            ("b3l_take wrong root flag 1 in cvs",
             "b3l_take", take_deps,
             once("node_value(chunk_node(kf.key, t + i, kf.flags, input[1024 * i .. 1024 * i + 1024]), 0)",
                  "node_value(chunk_node(kf.key, t + i, kf.flags, input[1024 * i .. 1024 * i + 1024]), 1)")),
            # Recursion termination measure
            ("b3l_take missing decreases len",
             "b3l_take", take_deps,
             once("    trace depends on len, t\n    decreases len\n",
                  "    trace depends on len, t\n")),
            ("b3l_subtree missing decreases len",
             "b3l_subtree", sub_deps,
             once("    trace depends on len, t, plat\n    decreases len\n",
                  "    trace depends on len, t, plat\n")),
            # Stack budgets
            ("b3l_take stack budget too small",
             "b3l_take", take_deps,
             once("stack 640 + 384 * bits((len - 1) / 1024)",
                  "stack 32 + 384 * bits((len - 1) / 1024)")),
            ("b3l_part32 stack budget too small",
             "b3l_part32", part_deps,
             once("    trace depends on len, t\n    stack 8192\n",
                  "    trace depends on len, t\n    stack 128\n")),
            ("b3l_subtree stack budget too small",
             "b3l_subtree", sub_deps,
             once("stack 16896 + 384 * bits((len - 1) / 1024)",
                  "stack 128 + 384 * bits((len - 1) / 1024)")),
            ("b3l_hashr stack budget too small",
             "b3l_hashr", ORDER,
             once("stack 18688 + 384 * bits(len / 1024)",
                  "stack 128 + 384 * bits(len / 1024)")),
            # Processor feature requirements
            ("b3l_hashr missing needs avx512 if plat == 5",
             "b3l_hashr", ORDER,
             once("    stack 18688 + 384 * bits(len / 1024)\n    needs sse41\n    needs avx512 if plat == 5\n}\n",
                  "    stack 18688 + 384 * bits(len / 1024)\n    needs sse41\n}\n")),
            ("b3l_hashr missing needs sse41",
             "b3l_hashr", ORDER,
             once("    stack 18688 + 384 * bits(len / 1024)\n    needs sse41\n    needs avx512 if plat == 5\n}\n",
                  "    stack 18688 + 384 * bits(len / 1024)\n    needs avx512 if plat == 5\n}\n")),
            # Trace independence: len and plat truly affect control flow
            ("b3l_hashr omits len from trace depends on",
             "b3l_hashr", ORDER,
             once("trace depends on len, flags, plat", "trace depends on flags, plat")),
            ("b3l_hashr omits plat from trace depends on",
             "b3l_hashr", ORDER,
             once("trace depends on len, flags, plat", "trace depends on len, flags")),
            # Functional postcondition
            ("b3l_hashr wrong ensures (flags + 1)",
             "b3l_hashr", ORDER,
             once("ensures out = bytes_of(hash_words(words(key), flags, input))",
                  "ensures out = bytes_of(hash_words(words(key), flags + 1, input))")),
        ]
        for label, target, deps, edit in cases:
            with self.subTest(label):
                ok, out = verify_only(full_spec_text(edit), target, deps)
                self.assertFalse(ok, f"expected refusal for {label}, got: {out}")

    def test_mutated_code_is_refused(self):
        # 1. Mutate b3l_hashr's root flag (root=8 -> root=0) and reassemble.
        bad_hashr = once("  // b3l_node_out(out, nd, 8, plat)\n  mov rdi, rbx\n  lea rsi, [rsp + 48]\n  mov rdx, 8\n",
                         "  // b3l_node_out(out, nd, 8, plat)\n  mov rdi, rbx\n  lea rsi, [rsp + 48]\n  mov rdx, 0\n")(self.source)
        src1 = os.path.join(self.dir, "bad_hashr.ode")
        obj1 = os.path.join(self.dir, "bad_hashr.o")
        with open(src1, "w") as f:
            f.write(bad_hashr)
        odec.build(src1, "hashr", obj1)
        ok, out = verify_only(full_spec_text(), "b3l_hashr", ORDER, obj_override={"b3l_hashr": obj1})
        self.assertFalse(ok, f"expected refusal for mutated b3l_hashr code, got: {out}")

        # 2. Mutate b3l_take's right recursive call to pass base `cvs` instead of `rcvs`.
        bad_take = once("  mov r8, qword ptr [rsp + 256]\n  mov r9, qword ptr [rsp + 264]\n  call b3l_take\n",
                        "  mov r8, qword ptr [rsp + 256]\n  mov r9, r15\n  call b3l_take\n")(self.source)
        src2 = os.path.join(self.dir, "bad_take.ode")
        obj2 = os.path.join(self.dir, "bad_take.o")
        with open(src2, "w") as f:
            f.write(bad_take)
        odec.build(src2, "take", obj2)
        take_deps = ORDER[:ORDER.index("b3l_take") + 1]
        ok, out = verify_only(full_spec_text(), "b3l_take", take_deps, obj_override={"b3l_take": obj2})
        self.assertFalse(ok, f"expected refusal for mutated b3l_take code, got: {out}")


if __name__ == "__main__":
    unittest.main()
