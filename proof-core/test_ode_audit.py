"""Positive and adversarial negative-control tests for lang/ode_audit.py and `ode_tool.py pack/audit/spec-test`."""

import os
import struct
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (HERE, os.path.join(ROOT, "lang"), os.path.join(ROOT, "kcheck")):
    if d not in sys.path:
        sys.path.insert(0, d)

import built
import ode_audit
import ode_canon

ODE_TOOL = os.path.join(ROOT, "lang", "ode_tool.py")


def _inject_extra_global_symbol(elf_bytes, sym_name):
    """Test helper: inject an extra STB_GLOBAL STT_FUNC symbol into an ELF64 `.o`."""
    parsed = ode_audit.parse_elf64(elf_bytes)
    secs = [dict(s) for s in parsed["sections"]]
    st = [s for s in secs if s["type"] == ode_audit.SHT_SYMTAB][0]
    strtab_sec = secs[st["link"]]
    strtab = bytearray(strtab_sec["body"])
    if not strtab.endswith(b"\x00"):
        strtab.append(0)
    off = len(strtab)
    strtab.extend(sym_name.encode("utf-8") + b"\x00")
    sym_buf = bytearray(st["body"])
    text_idx = parsed["by_name"][".text"][0]["idx"]
    sym_buf += struct.pack("<IBBHQQ", off, (ode_audit.STB_GLOBAL << 4) | ode_audit.STT_FUNC, 0, text_idx, 0, 4)
    st["body"] = bytes(sym_buf)
    st["size"] = len(sym_buf)
    strtab_sec["body"] = bytes(strtab)
    strtab_sec["size"] = len(strtab)
    return ode_audit._rebuild_elf64(parsed["machine"], parsed["shstrndx"], secs)


def _replace_section_body(elf_bytes, sec_name, new_body, new_flags=None):
    parsed = ode_audit.parse_elf64(elf_bytes)
    secs = [dict(s) for s in parsed["sections"]]
    for s in secs:
        if s["name"] == sec_name:
            s["body"] = bytes(new_body)
            s["size"] = len(new_body)
            if new_flags is not None:
                s["flags"] = new_flags
            break
    else:
        raise ValueError(f"section {sec_name} not found")
    return ode_audit._rebuild_elf64(parsed["machine"], parsed["shstrndx"], secs)


class TestOdeAudit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.tmp = tempfile.TemporaryDirectory(prefix="test_ode_audit_")
        cls.d = cls.tmp.name

        # Pack x86-64 and AArch64 UTF-8 2-byte decoder once for positive & adversarial controls.
        cls.x86_obj = os.path.join(cls.d, "utf8_x86.o")
        cls.x86_prf = os.path.join(cls.d, "utf8_x86.proof")
        cls.x86_glo = os.path.join(cls.d, "utf8_x86.glossary.json")
        cls.x86_res = ode_audit.pack_verified(
            os.path.join(ROOT, "factory", "verified", "utf8_decode_2byte_x86_64.ode"),
            os.path.join(ROOT, "factory", "verified", "utf8_decode_2byte_x86_64.spec"),
            cls.x86_obj,
            cls.x86_prf,
            glossary_out=cls.x86_glo,
        )

        cls.arm_obj = os.path.join(cls.d, "utf8_arm.o")
        cls.arm_prf = os.path.join(cls.d, "utf8_arm.proof")
        cls.arm_res = ode_audit.pack_verified(
            os.path.join(ROOT, "factory", "verified", "utf8_decode_2byte_arm64.ode"),
            os.path.join(ROOT, "factory", "verified", "utf8_decode_2byte_arm64.spec"),
            cls.arm_obj,
            cls.arm_prf,
        )

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls, "tmp"):
            cls.tmp.cleanup()

    def test_01_positive_x86_and_arm64_share_exact_contract_id_with_distinct_binary_ids(self):
        self.assertEqual(self.x86_res["verdict"], "shown", self.x86_res.get("errors"))
        self.assertEqual(self.arm_res["verdict"], "shown", self.arm_res.get("errors"))
        # Same semantic contract -> IDENTICAL 52-char base-32 BLAKE3 contract ID and symbol!
        self.assertEqual(self.x86_res["contract_b32"], self.arm_res["contract_b32"])
        self.assertEqual(self.x86_res["symbol"], self.arm_res["symbol"])
        self.assertEqual(len(self.x86_res["contract_b32"]), 52)
        self.assertEqual(len(self.x86_res["binary_b32"]), 52)
        self.assertEqual(len(self.arm_res["binary_b32"]), 52)
        # Different architectures -> DISTINCT 52-char base-32 binary IDs!
        self.assertNotEqual(self.x86_res["binary_b32"], self.arm_res["binary_b32"])
        self.assertEqual(self.x86_res["coverage"]["exported_symbols"], 1)
        self.assertEqual(self.x86_res["coverage"]["hooks"], 0)
        self.assertEqual(self.arm_res["coverage"]["exported_symbols"], 1)
        self.assertEqual(self.arm_res["coverage"]["hooks"], 0)

    def test_02_positive_chacha20_block_both_isas(self):
        for tag, ode_rel, spec_rel in (
            ("x86", "factory/verified/chacha20_block_x86_64.ode", "factory/verified/chacha20_block_x86_64.spec"),
            ("arm", "factory/verified/chacha20_block_arm64.ode", "factory/verified/chacha20_block_arm64.spec"),
        ):
            obj = os.path.join(self.d, f"c20_{tag}.o")
            prf = os.path.join(self.d, f"c20_{tag}.proof")
            res = ode_audit.pack_verified(os.path.join(ROOT, ode_rel), os.path.join(ROOT, spec_rel), obj, prf)
            self.assertEqual(res["verdict"], "shown", f"chacha20 {tag} failed: {res.get('errors')}")
            self.assertGreater(res["coverage"]["instructions"], 400)

    def test_03_cli_audit_show_contract_glossary_and_spec_test(self):
        cid = self.x86_res["contract_b32"]
        p = subprocess.run(
            [sys.executable, ODE_TOOL, "audit", self.x86_obj, "--proof", self.x86_prf,
             "--expect-contract", cid, "--show-contract", "--glossary", self.x86_glo],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("VERDICT:           shown", p.stdout)
        self.assertIn(f"BLAKE3(contract):  {cid}", p.stdout)
        self.assertIn("utf8_cp2", p.stdout)

        canon_path = os.path.join(self.d, "utf8.ocl")
        with open(canon_path, "w", encoding="utf-8") as f:
            f.write(self.x86_res["canonical_ocl"])
        p1 = subprocess.run(
            [sys.executable, ODE_TOOL, "spec-test", canon_path, "--call", "f0", "--arg", "[65]"],
            capture_output=True, text=True, check=True,
        )
        self.assertEqual(p1.stdout.strip(), "65")
        p2 = subprocess.run(
            [sys.executable, ODE_TOOL, "spec-test", canon_path, "--call", "utf8_cp2",
             "--glossary", self.x86_glo, "--arg", "[192, 175]"],
            capture_output=True, text=True, check=True,
        )
        self.assertEqual(p2.stdout.strip(), "4294967295")

    def test_04_attack_1a_contract_bait_and_switch_refused(self):
        wrong_b32 = "a" * 52
        res = ode_audit.audit_binary(self.x86_obj, self.x86_prf, expect_contract=wrong_b32)
        self.assertEqual(res["verdict"], "refused")
        self.assertTrue(any("contract hash mismatch" in e for e in res["errors"]), res["errors"])

        other_spec = os.path.join(ROOT, "factory", "verified", "chacha20_block_arm64.spec")
        res2 = ode_audit.audit_binary(self.x86_obj, self.x86_prf, contract_path=other_spec)
        self.assertEqual(res2["verdict"], "refused")
        self.assertTrue(any("contract mismatch" in e for e in res2["errors"]), res2["errors"])

    def test_05_attack_1b_extra_exported_symbol_refused(self):
        with open(self.x86_obj, "rb") as f:
            raw = f.read()
        bad = _inject_extra_global_symbol(raw, "hidden_backdoor")
        bad_path = os.path.join(self.d, "attack_extra_sym.o")
        with open(bad_path, "wb") as f:
            f.write(bad)
        res = ode_audit.audit_binary(bad_path, self.x86_prf)
        self.assertEqual(res["verdict"], "refused")
        self.assertTrue(any("expected exactly 1 exported symbol" in e for e in res["errors"]), res["errors"])

    def test_06_attack_1c_init_array_and_extra_exec_section_refused(self):
        with open(self.x86_obj, "rb") as f:
            raw = f.read()
        bad_init = ode_audit.append_elf_section(
            raw, ".init_array", b"\x00" * 8,
            sh_type=ode_audit.SHT_INIT_ARRAY,
            sh_flags=ode_audit.SHF_ALLOC | ode_audit.SHF_WRITE,
            sh_align=8,
        )
        p_init = os.path.join(self.d, "attack_init_array.o")
        with open(p_init, "wb") as f:
            f.write(bad_init)
        res1 = ode_audit.audit_binary(p_init, self.x86_prf)
        self.assertEqual(res1["verdict"], "refused")
        self.assertTrue(any("forbidden startup/teardown hook" in e for e in res1["errors"]), res1["errors"])

        bad_exec = ode_audit.append_elf_section(
            raw, ".text.evil", b"\xc3",
            sh_type=ode_audit.SHT_PROGBITS,
            sh_flags=ode_audit.SHF_ALLOC | ode_audit.SHF_EXECINSTR,
            sh_align=1,
        )
        p_exec = os.path.join(self.d, "attack_extra_exec.o")
        with open(p_exec, "wb") as f:
            f.write(bad_exec)
        res2 = ode_audit.audit_binary(p_exec, self.x86_prf)
        self.assertEqual(res2["verdict"], "refused")
        self.assertTrue(any("unexpected executable section" in e for e in res2["errors"]), res2["errors"])

    def test_07_attack_1d_trailing_executable_bytes_in_text_refused(self):
        for tag, obj_p, prf_p, bad_tail in (
            ("x86", self.x86_obj, self.x86_prf, b"\xcc\xc3"),
            ("arm", self.arm_obj, self.arm_prf, b"\x00\x00\x20\xd4"),
        ):
            with open(obj_p, "rb") as f:
                raw = f.read()
            parsed = ode_audit.parse_elf64(raw)
            cur_text = parsed["by_name"][".text"][0]["body"]
            bad = _replace_section_body(raw, ".text", cur_text + bad_tail)
            p_bad = os.path.join(self.d, f"attack_tail_{tag}.o")
            with open(p_bad, "wb") as f:
                f.write(bad)
            res = ode_audit.audit_binary(p_bad, prf_p)
            self.assertEqual(res["verdict"], "refused", f"trailing bytes not caught on {tag}")
            self.assertTrue(
                any("trailing executable bytes" in e or "odeverify refused" in e or "decode failed" in e for e in res["errors"]),
                res["errors"],
            )

    def test_08_attack_1e_non_canonical_or_alloc_ode_ocl_refused(self):
        with open(self.x86_obj, "rb") as f:
            raw = f.read()
        with open(os.path.join(ROOT, "factory", "verified", "utf8_decode_2byte_x86_64.spec"), "rb") as f:
            raw_spec = f.read()
        bad_noncanon = _replace_section_body(raw, ".ode.ocl", raw_spec)
        p1 = os.path.join(self.d, "attack_noncanon.o")
        with open(p1, "wb") as f:
            f.write(bad_noncanon)
        r1 = ode_audit.audit_binary(p1, self.x86_prf)
        self.assertEqual(r1["verdict"], "refused")
        self.assertTrue(any("not in canonical form" in e for e in r1["errors"]), r1["errors"])

        bad_alloc = _replace_section_body(raw, ".ode.ocl", self.x86_res["canonical_ocl"].encode(), new_flags=ode_audit.SHF_ALLOC)
        p2 = os.path.join(self.d, "attack_alloc_ocl.o")
        with open(p2, "wb") as f:
            f.write(bad_alloc)
        r2 = ode_audit.audit_binary(p2, self.x86_prf)
        self.assertEqual(r2["verdict"], "refused")
        self.assertTrue(any("non-allocated" in e for e in r2["errors"]), r2["errors"])

    def test_09_attack_1f_truncated_expect_contract_refused(self):
        prefix16 = self.x86_res["contract_b32"][:16]
        res = ode_audit.audit_binary(self.x86_obj, self.x86_prf, expect_contract=prefix16)
        self.assertEqual(res["verdict"], "refused")
        self.assertTrue(any("full 52-character" in e for e in res["errors"]), res["errors"])

    def test_10_attack_1g_symbol_not_bound_to_contract_hash_refused(self):
        with open(self.x86_obj, "rb") as f:
            raw = f.read()
        bad = ode_audit.rename_elf_symbol(raw, self.x86_res["symbol"], "ode_utf8_decode_2byte")
        p_bad = os.path.join(self.d, "attack_bad_sym.o")
        with open(p_bad, "wb") as f:
            f.write(bad)
        res = ode_audit.audit_binary(p_bad, self.x86_prf)
        self.assertEqual(res["verdict"], "refused")
        self.assertTrue(any("does not match canonical contract hash symbol" in e for e in res["errors"]), res["errors"])

    def test_11_attack_2_binary_byte_flip_changes_hash_and_fails_odeverify(self):
        with open(self.x86_obj, "rb") as f:
            raw = f.read()
        parsed = ode_audit.parse_elf64(raw)
        text = bytearray(parsed["by_name"][".text"][0]["body"])
        idx = text.find(b"\xc2")
        if idx < 0:
            idx = 0
        text[idx] ^= 0x01
        bad = _replace_section_body(raw, ".text", bytes(text))
        p_bad = os.path.join(self.d, "attack_flip.o")
        with open(p_bad, "wb") as f:
            f.write(bad)
        res = ode_audit.audit_binary(p_bad, self.x86_prf)
        self.assertNotEqual(res["binary_b32"], self.x86_res["binary_b32"])
        self.assertEqual(res["verdict"], "refused")


if __name__ == "__main__":
    unittest.main()
