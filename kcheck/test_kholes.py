#!/usr/bin/env python3
"""Eight holes found by reading (four on November 17, 2026 in kfn.py and the kernels' verifiers, to merge them, and
then again with the question the first two had taught; two more that day in the afternoon, in the proof's part
and the specification's sequences; two more on November 18 while writing the memory and call rules down); each
was "shown, of something false". The copies that were shown then are refused now; these are the copies.

1. The stack pointer (kfn.py's machine, which is kbyte.py's too). `mov rsp, rdi`, `lea rsp, [rdi]` and
   `pop rsp` put an argument's address in the stack pointer, and the machine then took a push to go to the
   function's own frame. A copy of the shipped ode_common with four instructions added wrote eight bytes
   below `a` on a processor and was shown to meet its public contract.
2. The address of the file's data (kdecode.py; kcheck.py, kloop.py). The decoder wrote `lea reg, [rip + data]`
   as a move of the number RODATA + where, the same row as a true `mov reg, NUMBER`, and the kernels'
   verifiers took any such number within the data for its address. A copy of b3hashr.o with seven bytes
   changed in the 32-lane kernel (`mov rdi, 0x50004500` for `lea rdi, [rip + the schedule]`) was shown to
   meet the public contract; on a processor it stopped on a fault, and with a page mapped at that address it
   returned a digest that is not BLAKE3's.
3. The stack below the stack pointer (kfn.py's machine). What the machine remembered of it outlived a call,
   which writes there (the return address, the callee's frame). A copy of the shipped ode_unframe that pushes
   r15 and pops it before a call, then moves the stack pointer down and pops r15 again, was shown to meet its
   public contract; on a processor r15 then holds the return address, and the function reads its input far
   outside it.
4. What a call leaves in the registers (kfn.py's machine). Every register a callee may change was the one
   unknown "left by a call"; two of them compared with a number were taken to answer alike, so a path on
   which they differ was never run. A copy of ode_unframe that writes a byte below `out` where rcx is zero
   and rdx is not (after a call, whose callee is free in what it leaves there) was shown to meet its public
   contract.
5. The proof's `layout`s, and the paths a proof could delete (ode.py, kfn.py, kbyte.py). A layout comes with
   the proof, which Bob does not read; nothing checked where its fields lay, that they did not overlap, or
   that `below` was at least 1. `layout tiny 8 { a: 32 bytes at 0 }` let a verified function write past what
   its caller had room for (saved registers, the return address); `layout alias 32 { a: number at 0, b: cv at 0 }`
   gave two fields of one place two entries of the model's memory; and `layout impossible 8 { v: number at 0
   below 0 }` - no value of it is - put facts that cannot all hold into a caller, whose path was then dropped
   as no path and its code after the call never checked. `backdoor.o` here is the whole of it: the real
   b3hashr.o code with one branch added, which for every message of a byte or more calls a one-instruction
   callee whose `writes p` is that layout and then writes 32 zero bytes to `out` - it was shown to meet the
   public contract of the reader's own blake3.spec (exit 0), and on a processor it fails the first official
   vector (blake3-reports/p16-20261113/hole-layout).
6. A `sequence` whose value changes shape each turn (kspec.py). What cannot be run was named by the shape of
   its first value: `sequence grow(n) { h[0] = [0]  h[b + 1] = h[b] ++ [0]  for b in 0..n }` made
   `len(grow(n))` 1, and a function returning the constant 1 was shown.
7. What a call assumes and leaves at an address (kfn.py). Three ways the caller and callee disagreed on
   memory: (a) an address argument the callee only reads, of a kind other than bytes (`cv`, `block`, a
   `layout`), was read lazily, so where `ensures` did not mention it the caller never checked that it lay in
   the caller's memory or apart from the callee's stack frame - `b3l_hashr` calling `b3l_twice(rsp - 24, out)`
   let `b3l_twice`'s stack write overwrite its own input between two reads, verified against the unmodified
   blake3.spec in default by-proof mode, and failed the first official vector on a processor; (b) a `layout`
   argument in `writes` (`ensures p = make(p.a)`) gave the callee every field's `below` and `byte` invariant
   on entry while the caller checked only `p.a`; (c) `writes p` without `ensures` put a fresh `of_kind(p)`
   record (with `below` facts) into the caller after a `ret` callee.
8. Stack places in a byte program's proof (kbyte.py). `any stack[N]` put an eight-byte entry at `rsp + N`
   without checking that it lay below the return address in the function's own frame, letting a function
   that reads `[rsp + 0x10000000]` (a segmentation fault on a processor) be shown to return 0.

And one of that day's own changes, caught the same way before it was shipped: counting down (`dec`) and
`test` were taken to set the flags as a compare does; a jump on the order after them is refused now.
And two things the decoder read that a processor refuses as illegal instructions (class Decoder): of a milder
kind, since a function with them stops on a fault and computes nothing wrong; but it was shown to return.
And two more of the file's reading, milder still: a table the file points at outside itself was read as
whatever the slices gave, and (found with 5) a public contract the proof left out was not printed by the
first page of verify.py, and the check said "NOT verified" of it while exiting 0."""
import os, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "programs")); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import check_programs, kbyte, kcheck, kdecode, kfn, kspec, ode, odec
from test_kcheck import assemble

KERNEL = "blake3_servil_compress_in_place_avx512"
FIRST = "  vmovdqu xmm0, xmmword ptr [rdi]\n"            # the kernel's first instruction (wide/one.ode)
WAYS = [("an argument's address moved into it, a push, and back", "  mov rax, rsp\n  mov rsp, rdi\n  push rbx\n  mov rsp, rax\n", "leaves the function's own frame"),
        ("the same by lea", "  mov rax, rsp\n  lea rsp, [rdi+0]\n  push rbx\n  mov rsp, rax\n", "leaves the function's own frame"),
        ("the same by a pop", "  mov rax, rsp\n  push rdi\n  pop rsp\n  push rbx\n  mov rsp, rax\n", "an instruction this verifier does not know: 5c"),          # (the table has no row for it, so no bytes are read as it)
        ("a push of it", "  push rsp\n  pop rax\n", "an instruction this verifier does not know: 54"),
        ("above where it was at entry", "  add rsp, 8\n  sub rsp, 8\n", "leaves the function's own frame"),
        # (November 17, on taking the instructions out of the verifier: only the stack pointer's own value is rounded down to a boundary)
        ("rounded down to a 64-byte boundary from above where it was, sixty-four bytes written there, and back",
         "  mov r11, rsp\n  lea rax, [rsp+64]\n  and rax, -64\n  mov rsp, rax\n  sub rsp, 64\n  vpxord zmm16, zmm16, zmm16\n  vmovdqa32 zmmword ptr [rsp], zmm16\n  mov rsp, r11\n", "and of ('a', 'frame', 64)"),
        ("moved 8192 bytes down by lea, a write there, and back", "  lea rsp, [rsp-0x2000]\n  mov qword ptr [rsp], rbx\n  lea rsp, [rsp+0x2000]\n", "8192 bytes of stack used")]


class Stack(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.mkdtemp()
        with open(os.path.join(HERE, "blake3.spec")) as f: spec = f.read()
        with open(os.path.join(HERE, "proofs", "inner.spec")) as f: inner = f.read()
        head = "ensures h = compress(h, m, t, length, flags)\n    stack 0\n    needs avx512"
        assert inner.count(head) == 1
        # the kernel's contract with room on the stack: a maker's to write (an inner contract)
        cls.spec = ode.with_proof(spec, inner.replace(head, head.replace("stack 0", "stack 4096")))
        with open(os.path.join(HERE, "..", "wide", "one.ode")) as f: cls.source = f.read()
        assert cls.source.count(FIRST) == 1

    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.work)

    def kernel(self, source):
        p = os.path.join(self.work, "k.ode")
        with open(p, "w") as f: f.write(source)
        with open(os.path.join(self.work, "k.S"), "w") as f: f.write(odec.assembly(p, "compress1"))
        assemble(os.path.join(self.work, "k.S"), os.path.join(self.work, "k.o"))
        kspec.SPEC = self.spec; kfn.CONTRACTS.clear()
        kfn.check(kfn.load(os.path.join(self.work, "k.o"), None, KERNEL), None, symbol=KERNEL)

    def test_the_kernel_as_it_is_meets_the_contract_with_room_on_the_stack(self):
        self.kernel(self.source)

    def test_counting_down_says_only_whether_the_number_is_zero(self):
        at = "  dec al\n  jz @done\n"
        self.assertEqual(self.source.count(at), 2)             # (the source has two kernels: the first is the one tried here)
        with self.assertRaises(kcheck.Fail) as refused: self.kernel(self.source.replace(at, "  dec al\n  jb @done\n  jz @done\n", 1))
        self.assertIn("say only whether a number is zero", str(refused.exception))

    def test_no_way_out_of_the_frame(self):
        for what, added, why in WAYS:
            with self.subTest(what):
                with self.assertRaises((kcheck.Fail, kdecode.Stop)) as refused: self.kernel(self.source.replace(FIRST, added + FIRST))
                self.assertIn(why, str(refused.exception))

    def common(self, text, place):
        read = lambda *p: open(os.path.join(HERE, "programs", *p)).read()
        with open(os.path.join(self.work, "c.S"), "w") as f: f.write(text)
        assemble(os.path.join(self.work, "c.S"), os.path.join(self.work, "c.o"))
        spec = ode.with_proof(read("common", "common.spec"), check_programs.lemmas("common"))
        kbyte.check(kbyte.load(os.path.join(self.work, "c.o"), "ode_common"), spec, "ode_common", read("common", "common.proof").replace("place +0x34", "place " + place))

    def test_a_program_of_bytes_that_writes_below_its_argument(self):
        text = odec.assembly(os.path.join(HERE, "programs", "common", "common.ode"), "common")
        at = "_ode_common:\n    push rbx\n"
        self.assertEqual(text.count(at), 1)
        self.common(text, "+0x34")                                          # as shipped
        with self.assertRaises(kcheck.Fail) as refused:
            self.common(text.replace(at, "_ode_common:\n    mov rax, rsp\n    mov rsp, rdi\n    push rbx\n    mov rsp, rax\n    push rbx\n"), "+0x3e")
        self.assertIn("leaves the function's own frame", str(refused.exception))


class Calls(unittest.TestCase):
    """ode_unframe (programs/frame: it calls two functions by their contracts) with instructions added around a call."""
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.mkdtemp()
        read = lambda *p: open(os.path.join(HERE, "programs", *p)).read()
        cls.spec = ode.with_proof(read("frame", "frame.spec"), read("frame", "unframe.inner") + check_programs.lemmas("frame"))
        cls.source, cls.proof = odec.assembly(os.path.join(HERE, "programs", "frame", "frame.ode"), "unframe"), read("frame", "unframe.proof")

    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.work)

    def unframe(self, text):
        with open(os.path.join(self.work, "u.S"), "w") as f: f.write(text)
        assemble(os.path.join(self.work, "u.S"), os.path.join(self.work, "u.o"))
        kbyte.check(kbyte.load(os.path.join(self.work, "u.o"), "ode_unframe"), self.spec, "ode_unframe", self.proof)

    def changed(self, old, new):
        self.assertEqual(self.source.count(old), 1, old)
        return self.source.replace(old, new)

    def test_as_shipped(self): self.unframe(self.source)

    def test_nothing_is_remembered_of_the_stack_below_the_stack_pointer(self):
        call = "    mov rcx, r15\n    call CALL(ode_lz4_decode)\n"
        with self.assertRaises(kcheck.Fail) as refused:
            self.unframe(self.changed(call, "    mov rcx, r15\n    push r15\n    pop r11\n    call CALL(ode_lz4_decode)\n    sub rsp, 8\n    pop r15\n"))
        self.assertIn("nothing was written there", str(refused.exception))

    def test_what_a_call_leaves_in_two_registers_is_two_unknowns(self):
        after = "    call CALL(ode_lz4_decode)\n    mov qword ptr [rsp + 0], rax\n"
        evil = "    mov byte ptr [rbx - 1], 65\n.Lskip:\n    mov qword ptr [rsp + 0], rax\n"         # a byte written below `out`
        for asked in ("    cmp rcx, 0\n    jne .Lskip\n    cmp rdx, 0\n    je .Lskip\n",            # where rcx is zero and rdx is not
                      "    cmp rcx, 0\n    jne .Lskip\n"):                                         # (where rcx is zero: this one was always refused)
            with self.assertRaises(kcheck.Fail) as refused: self.unframe(self.changed(after, "    call CALL(ode_lz4_decode)\n" + asked + evil))
            self.assertIn("a write at out + -1", str(refused.exception))


class Data(unittest.TestCase):
    def test_a_number_moved_is_not_the_address_of_the_data(self):
        obj = os.path.join(HERE, "b3hashr.o")
        e = kdecode.Elf(obj); s = kdecode.Settled(e)
        start = s.at["blake3_servil_avx512_k32"]
        rows, data = kdecode.read(obj, "blake3_servil_avx512_k32", 0, 0)
        at, row = next((a, i) for a, _, i in rows if i.startswith(".lea_data "))
        self.assertTrue(row.startswith(".lea_data .rdi "))
        where = e.sections[e.index[".text"]]["off"] + (start - s.lo) + at
        b = bytearray(e.b)
        self.assertEqual(bytes(b[where:where + 3]), bytes.fromhex("488d3d"))                    # lea rdi, [rip + ...]
        b[where:where + 7] = bytes.fromhex("48c7c7") + (0x50000000 + int(row.split()[2], 16)).to_bytes(4, "little")    # mov rdi, that number
        work = tempfile.mkdtemp()
        try:
            changed = os.path.join(work, "changed.o")
            with open(changed, "wb") as f: f.write(bytes(b))
            self.assertIn(".mov 64 (.reg .rdi) (.imm 0x5000", "\n".join(i for _, _, i in kdecode.read(changed, "blake3_servil_avx512_k32", 0, 0)[0]))
            r = subprocess.run([sys.executable, os.path.join(HERE, "check_binary.py"), changed, "--maintain"], capture_output=True, text=True)
            self.assertEqual(r.returncode, 1, r.stdout[-400:])
            self.assertIn("blake3_servil_avx512_k32: NOT shown", r.stdout)
            self.assertIn("b3l_hashr: NOT shown", r.stdout)
        finally: shutil.rmtree(work)


class Decoder(unittest.TestCase):
    """Bytes are read as an instruction only where the table of instructions writes those very bytes for an
    instance of a row (../core/encode.py). Until November 17, 2026 a reader written by hand took more: an
    instruction of more than fifteen bytes (a processor faults on it) and VEX forms that are no instruction (a
    processor stops on them), and a function with them was shown to return. And it took an instruction
    written with bits and bytes it had no need of (a prefix that says nothing, a displacement of zero written
    out): what a processor does with each such form was a question apart for each."""
    def decode(self, code): return kdecode.decode(bytes.fromhex(code), 0, None, b"", 0, 0, 0)

    def refused(self, code):
        with self.assertRaisesRegex(kdecode.Stop, "an instruction this verifier does not know"): self.decode(code)

    def test_an_instruction_is_at_most_fifteen_bytes(self):
        self.assertEqual(self.decode("6690"), (2, ".nop"))
        self.assertEqual(self.decode("6666666666662e0f1f840000000000"), (15, ".nop"))        # the longest the table writes
        for code in ("66" * 14 + "90", "66" * 20 + "90", "66" * 12 + "0f1f840000000000"): self.refused(code)

    def test_vex_has_no_instruction_at_the_older_encodings_escapes(self):
        self.assertEqual(self.decode("660f3800c1"), (5, ".xpshufb 0 0 1"))             # PSHUFB as SSSE3 writes it
        for code in ("c5f93800c1", "c5f93a0ec105", "c4e1793800c1"): self.refused(code)

    def test_only_the_bytes_the_table_writes_are_read(self):
        for code, row in (("4801c8", ".add 64 (.reg .rax) (.reg .rcx)"), ("89c8", ".mov 32 (.reg .rax) (.reg .rcx)"), ("488b00", ".mov 64 (.reg .rax) (.mem .rax 0x0)"),
                          ("488b4008", ".mov 64 (.reg .rax) (.mem .rax 0x8)"), ("488b0424", ".mov 64 (.reg .rax) (.mem .rsp 0x0)"), ("c5f1fec2", ".xpaddd 0 1 2"),
                          ("c5f96fc1", ".xmov 0 1"), ("62f17548fec2", ".zpaddd 0 1 2"), ("440fb6c7", ".movzx8 .r8 (.reg .rdi)"), ("400fb6c7", ".movzx8 .rax (.reg .rdi)")):
            self.assertEqual(self.decode(code), (len(code) // 2, row))
        for code, what in (("4089c8", "a REX prefix that says nothing"), ("4a01c8", "a REX bit that names no register here"), ("488b0420", "a SIB byte with no need of one"),
                           ("488b4000", "a displacement of zero, written out"), ("488b8008000000", "four bytes of displacement where one holds it"),
                           ("488b0460", "a scale"), ("4803c1", "an add of registers the other way about"), ("c4e171fec2", "three bytes of VEX prefix where two say it"),
                           ("c5f16fc1", "a second source named where there is none"), ("c5f5fec2", "256 bits"), ("62f175c8fec2", "EVEX zeroing"),
                           ("62f17558fec2", "an EVEX broadcast"), ("62f17548fe4208", "an EVEX add from memory with no index"), ("0fb6c7", "the low byte of rdi with no REX prefix (that is bh)"),
                           ("54", "a push of the stack pointer"), ("66" + "4801c8", "a prefix before an instruction that has none")):
            with self.subTest(what): self.refused(code)


class Proof(unittest.TestCase):
    """What an untrusted proof's `layout` can be made to say (hole 5), and the file that was shown by it."""

    def read(self, inner):
        with open(os.path.join(HERE, "blake3.spec")) as f: text = f.read()
        return ode.with_proof(text, inner)

    def test_where_a_layouts_fields_lie_is_checked(self):
        for layout, why in (("layout tiny 8 { a: 32 bytes at 0 }", "does not lie within its 8 bytes"),
                            ("layout alias 32 { a: number at 0, b: cv at 0 }", "have a byte in common")):
            with self.subTest(layout):
                with self.assertRaisesRegex(ode.Err, why): self.read(layout)

    def test_a_layout_below_zero_has_no_value(self):
        with self.assertRaisesRegex(ode.Err, "no number is"): self.read("layout impossible 8 { v: number at 0 below 0 }")

    def test_the_file_that_was_shown_by_it_is_refused(self):
        """backdoor.o: the real b3hashr.o code with one branch added (hole 5's whole demonstration: it was
        shown to meet the public contract of the reader's own blake3.spec, and on a processor it fails the
        first official vector). The layout it carries is now refused when the proof is read."""
        import subprocess
        r = subprocess.run([sys.executable, os.path.join(HERE, "check_binary.py"), os.path.join(HERE, "backdoor.o"), "--spec", os.path.join(HERE, "blake3.spec")], capture_output=True, text=True)
        self.assertEqual(r.returncode, 1, r.stdout[-400:])
        self.assertIn("NOT shown: the proof's part cannot be read", r.stdout)
        self.assertIn("below 0", r.stdout)

    def test_a_public_contract_the_proof_leaves_out_is_printed_and_said(self):
        """(Found with hole 5.) A specification the reader brings with a contract for a function this file
        does not have: the first page of verify.py prints it and the check says NOT verified of it, while
        the functions the file does have stand. (Until November 17, 2026 that page printed only the
        contracts the proof spoke of.) Where the file has such a function, programs/test_files.py holds
        that the file is NOT shown."""
        import subprocess, tempfile
        with open(os.path.join(HERE, "programs", "frame", "odeframe.o"), "rb") as f: pass
        frame = os.path.join(HERE, "programs", "frame", "odeframe.o")
        with open(os.path.join(HERE, "programs", "frame", "frame.spec")) as f: spec = f.read()
        extra = spec + "\ncontract ode_absent(out: 32 bytes, n: number) {\n    requires no_overlap(out)\n    returns n\n    stack 0\n}\n"
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "two.spec")
            with open(path, "w") as f: f.write(extra)
            r = subprocess.run([sys.executable, os.path.join(HERE, "verify.py"), frame, path], capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout[-400:])
            self.assertIn("ode_absent: NOT verified", r.stdout)
            self.assertIn("contract ode_absent", r.stdout)
            self.assertIn("(this file has none of that name)", r.stdout)

    def test_a_ring_of_calls_is_refused(self):
        """(Found with hole 5's reading.) Two functions that call one another: until November 17, 2026 nothing
        in check_binary.py asked that the calls come to an end (only programs/check_file.py did). Each
        function's own check passes (each call is taken by the other's contract, its stack covered: a ring of
        constant stacks cannot pass, but one whose stack grows with an argument can, and nothing bound it);
        the ring is refused by the driver. (On a processor two functions calling one another stop on a stack
        fault once the stack runs out.)"""
        import check_binary
        self.assertEqual(check_binary.ring_of({"a": ["b"], "b": ["a"]}), {"a", "b"})
        self.assertEqual(check_binary.ring_of({"a": ["b"], "b": ["c"], "c": ["a"]}), {"a", "b", "c"})
        self.assertEqual(check_binary.ring_of({"a": ["a"], "b": ["c"], "c": ["b"]}), {"b", "c"})   # a self-call is lessens' to show
        self.assertEqual(check_binary.ring_of({"a": ["b", "c"], "b": [], "c": []}), set())

    def test_a_sequence_whose_value_changes_shape_is_not_named_by_its_first(self):
        """Hole 6: a sequence that grows a place each turn was named by the shape of its first value, so
        `len(grow(n))` was taken for 1 and a function returning the constant 1 was shown."""
        import kfn, kspec, kterms
        spec = ode.Spec("""sequence grow(n) {
 h[0] = [0]
 h[b + 1] = h[b] ++ [0]
 for b in 0..n
}
contract demo(n: number) {
 returns len(grow(n))
 stack 0
}
""")
        self.assertEqual(spec.call(ode.Numbers(), "grow", 2), [0, 0, 0])
        kspec.SPEC = spec
        kfn.CONTRACTS.clear()
        rows = [(kfn.BASE, kfn.BASE + 5, ".mov 32 (.reg .rax) (.imm 0x1)"), (kfn.BASE + 5, kfn.BASE + 6, ".ret")]
        try:
            kfn.check(rows, "demo", symbol="demo")
            self.fail("the shape-changing sequence was named by its first value")
        except kcheck.Fail as refused:
            self.assertIn("stay of one shape", str(refused))
        finally:
            import kspec as k, kfn as f
            k.SPEC = ode.load(); f.CONTRACTS.clear()

    def test_a_table_the_file_points_at_outside_itself_is_not_read(self):
        """(Found with hole 5's reading.) A section header naming bytes past the file's end was read as
        whatever the slices gave."""
        with open(os.path.join(HERE, "b3hashr.o"), "rb") as f: b = bytearray(f.read())
        import struct
        shoff, = struct.unpack_from("<Q", b, 40)
        struct.pack_into("<Q", b, shoff + 24, 1 << 40)          # the first section's offset, past the file
        with self.assertRaises(kdecode.Stop): kdecode.Elf(bytes(b))


class CallMemory(unittest.TestCase):
    """Hole 7 (memory at a call in kfn.py) and hole 8 (`stack[N]` in a proof of kbyte.py)."""

    def tearDown(self):
        kspec.SPEC = ode.load(); kfn.CONTRACTS.clear()

    def with_inner(self, inner):
        with open(os.path.join(HERE, "blake3.spec")) as f: text = f.read()
        kspec.SPEC = ode.with_proof(text, inner); kfn.CONTRACTS.clear()

    def test_an_unread_address_argument_at_a_call_must_lie_in_the_callers_memory(self):
        """Hole 7(a): `b3l_twice(p: cv, h: cv)` has `ensures h = h` and XORs two reads of `[p]` around a stack
        write into `h`. When a caller passes `rsp - 24` (inside `b3l_twice`'s stack frame) or an out-of-bounds
        address, the call is refused."""
        self.with_inner("""
contract b3l_twice(p: cv, h: cv) {
    requires no_overlap(p, h)
    ensures h = h
    stack 16
    needs sse41
}
contract b3l_caller(h: cv) {
    ensures h = h
    stack 64
    needs sse41
}
""")
        B = kfn.BASE
        twice = [
            (B,      B + 4,  ".sub 64 (.reg .rsp) (.imm 0x10)"),
            (B + 4,  B + 6,  ".xor 32 (.reg .rax) (.reg .rax)"),
            (B + 6,  B + 10, ".mov 64 (.mem .rsp 0x0) (.reg .rax)"),
            (B + 10, B + 14, ".xloadu 0 .rdi 0x0"),
            (B + 14, B + 19, ".mov 32 (.reg .rax) (.imm 0xDEADBEEF)"),
            (B + 19, B + 23, ".mov 64 (.mem .rsp 0x0) (.reg .rax)"),
            (B + 23, B + 27, ".xloadu 1 .rdi 0x0"),
            (B + 27, B + 31, ".xpxor 0 0 1"),
            (B + 31, B + 35, ".xloadu 2 .rsi 0x0"),
            (B + 35, B + 39, ".xpxor 2 2 0"),
            (B + 39, B + 43, ".xstoreu .rsi 0x0 2"),
            (B + 43, B + 47, ".add 64 (.reg .rsp) (.imm 0x10)"),
            (B + 47, B + 48, ".ret"),
        ]
        kfn.check(twice, None, symbol="b3l_twice")
        for bad_lea, why in ((".lea .rdi .rsp -24", "do not lie in the caller's live frame"),
                             (".lea .rdi .rsp 0x10", "do not lie in the caller's live frame"),
                             (".lea .rdi .rsi 0x20", "not shown to lie within h")):
            caller = [
                (B,      B + 4,  ".sub 64 (.reg .rsp) (.imm 0x8)"),
                (B + 4,  B + 7,  ".mov 64 (.reg .rsi) (.reg .rdi)"),
                (B + 7,  B + 12, bad_lea),
                (B + 12, B + 17, ".call b3l_twice"),
                (B + 17, B + 21, ".add 64 (.reg .rsp) (.imm 0x8)"),
                (B + 21, B + 22, ".ret"),
            ]
            with self.subTest(bad_lea):
                with self.assertRaisesRegex(kcheck.Fail, why):
                    kfn.check(caller, None, symbol="b3l_caller")

    def test_a_written_layouts_unmentioned_fields_are_not_assumed_on_entry(self):
        """Hole 7(b): `ensures p = make_rec(p.a)` mentions only `p.a`, so `b3l_edit` may not assume `p.b < 65`
        (or read `p.b` at all) before writing `p.b`."""
        self.with_inner("""
layout partial_rec 16 { a: number at 0, b: number at 8 below 65 }
def make_rec(x) { { a: x, b: 0 } }
contract b3l_edit(p: partial_rec) {
    ensures p = make_rec(p.a)
    stack 0
}
""")
        B = kfn.BASE
        edit = [
            (B,      B + 4,  ".mov 64 (.reg .rax) (.mem .rdi 0x8)"),
            (B + 4,  B + 8,  ".cmp 64 (.reg .rax) (.imm 0x41)"),
            (B + 8,  B + 10, f".jae 0x{B + 18:X}"),
            (B + 10, B + 17, ".mov 64 (.reg .rax) (.imm 0x0)"),
            (B + 17, B + 18, ".nop"),
            (B + 18, B + 22, ".mov 64 (.mem .rdi 0x8) (.reg .rax)"),
            (B + 22, B + 23, ".ret"),
        ]
        with self.assertRaisesRegex(kcheck.Fail, "nothing has been written there"):
            kfn.check(edit, None, symbol="b3l_edit")

    def test_writes_without_ensures_leaves_no_invariant_for_the_caller(self):
        """Hole 7(c): `writes p` means `p` may hold anything afterwards; calling a `ret` function with
        `writes p` on a constrained layout leaves nothing readable in the caller's frame, not `p.v < 65`."""
        self.with_inner("""
layout constrained 8 { v: number at 0 below 65 }
contract b3l_spoil(p: constrained) {
    writes p
    stack 0
}
contract b3l_caller(out: 1 bytes) {
    ensures out = [0]
    stack 32
}
""")
        B = kfn.BASE
        kfn.check([(B, B + 1, ".ret")], None, symbol="b3l_spoil")
        caller = [
            (B,      B + 1,  ".push .rbx"),
            (B + 1,  B + 5,  ".sub 64 (.reg .rsp) (.imm 0x10)"),
            (B + 5,  B + 8,  ".mov 64 (.reg .rbx) (.reg .rdi)"),
            (B + 8,  B + 15, ".mov 64 (.reg .rax) (.imm 0x3E7)"),
            (B + 15, B + 19, ".mov 64 (.mem .rsp 0x0) (.reg .rax)"),
            (B + 19, B + 22, ".mov 64 (.reg .rdi) (.reg .rsp)"),
            (B + 22, B + 27, ".call b3l_spoil"),
            (B + 27, B + 31, ".mov 64 (.reg .rax) (.mem .rsp 0x0)"),
            (B + 31, B + 35, ".cmp 64 (.reg .rax) (.imm 0x64)"),
            (B + 35, B + 37, f".jae 0x{B + 40:X}"),
            (B + 37, B + 40, ".mov 8 (.mem .rbx 0x0) (.imm 0x0)"),
            (B + 40, B + 44, ".add 64 (.reg .rsp) (.imm 0x10)"),
            (B + 44, B + 45, ".pop .rbx"),
            (B + 45, B + 46, ".ret"),
        ]
        with self.assertRaisesRegex(kcheck.Fail, "nothing was written there"):
            kfn.check(caller, None, symbol="b3l_caller")

    def test_a_proof_in_kbyte_cannot_name_stack_cells_outside_the_frame(self):
        """Hole 8: `any stack[268435456]` in a `.proof` file placed a readable cell 256 MiB above `rsp`."""
        spec = ode.Spec("contract f(n: number) {\n returns 0\n stack 0\n}\n")
        B = kbyte.BASE
        rows = [(B, B + 2, f".jmp 0x{B + 2:X}"),
                (B + 2, B + 9, ".mov 64 (.reg .rcx) (.mem .rsp 0x10000000)"),
                (B + 9, B + 11, ".xor 32 (.reg .rax) (.reg .rax)"),
                (B + 11, B + 12, ".ret")]
        with self.assertRaisesRegex(kcheck.Fail, "outside the function's own frame"):
            kbyte.check(rows, spec, "f", "place +0x2 {\n any stack[268435456], rcx\n}\n")
        with self.assertRaisesRegex(kcheck.Fail, "outside the function's own frame"):
            kbyte.check(rows, spec, "f", "place +0x2 {\n any stack[0], rcx\n}\n")


if __name__ == "__main__":
    unittest.main()
