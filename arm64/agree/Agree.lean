import Table
import Machine
import Arm64.Trusted.ISA.Decode
import Arm64.Trusted.ISA.Eval

/-!
# Agreement between `arm64.tab` and Google DeepMind's `arm64-semantics`

Standalone proof package. Depends only on the instruction-table definitions (`Table.lean`,
`Machine.lean`) and Google DeepMind's `Arm64.Trusted.ISA` (`Decode`, `Eval`).

Four rows of `arm64/arm64.tab`, one from each major class, are proved to agree with Google's
decoder (`Arm64.decode`) and evaluator (`Arm64.execInstWithSvc Arm64.noSyscalls`):
1. `add_rrr`  — 64-bit general-purpose register arithmetic (`D = add64(S, P)`)
2. `ldr64_sp` — 64-bit load through `sp`, including the 16-byte SP-alignment fault (`D = mem64(on16(sp), N)`)
3. `eor_v`    — 128-bit NEON three-register bitwise XOR (`X = each32(xor32, Y, Z)`)
4. `rev32_8h` — 128-bit NEON halfword reverse = 16-bit rotate per 32-bit lane (`X = each32(ror32, Y, 16)`)
-/

namespace ArmAgree

/-! ## Generic bit-field helpers for 32-bit AArch64 encodings -/

theorem testBit_eq_false_of_lt {v k i : Nat} (hv : v < 2 ^ k) (hi : k ≤ i) :
    v.testBit i = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hpow : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
  have hdiv : v / 2 ^ i = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hv hpow)
  simp [hdiv]

/-- A field of `w` bits placed at bit offset `lo` has zero outside `[lo, lo + w)`. -/
theorem field_and_eq_zero {v w lo : Nat} {mask : BitVec 32}
    (hv : v < 2 ^ w)
    (hdisj : ∀ i : Fin 32, lo ≤ i.val → i.val < lo + w → mask.getLsbD i.val = false) :
    (BitVec.ofNat 32 v <<< lo) &&& mask = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  by_cases hlo : lo ≤ i
  · by_cases hhi : i < lo + w
    · simp [hdisj ⟨i, hi⟩ hlo hhi]
    · have : v.testBit (i - lo) = false := testBit_eq_false_of_lt hv (by omega)
      simp [this]
  · simp [hlo]

/-- Extracting `len` bits at `pos` from a field at `[lo, lo + w)` that does not overlap `[pos, pos + len)` gives 0. -/
theorem extract_field_miss {v w lo pos len : Nat}
    (hv : v < 2 ^ w) (hmiss : lo + w ≤ pos ∨ pos + len ≤ lo) :
    (BitVec.ofNat 32 v <<< lo).extractLsb' pos len = 0#len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  by_cases hlt : pos + i < 32
  · by_cases hlo : lo ≤ pos + i
    · have : v.testBit (pos + i - lo) = false := testBit_eq_false_of_lt hv (by omega)
      simp [hlt, this]
    · simp [hlt, hlo]
  · simp [hlt]

/-- Extracting `w` bits at `lo` from a field of `w` bits placed at `lo` recovers the field. -/
theorem extract_field_hit {v w lo : Nat} (hfit : lo + w ≤ 32) :
    (BitVec.ofNat 32 v <<< lo).extractLsb' lo w = BitVec.ofNat w v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hlt : lo + i < 32 := by omega
  have hnot : ¬ (lo + i < lo) := by omega
  have hi32 : i < 32 := by omega
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
             hi, hlt, hnot, hi32, decide_true, decide_false, Bool.not_false, Bool.true_and, Nat.add_sub_cancel_left]

theorem extract_or {a b : BitVec 32} {pos len : Nat} :
    (a ||| b).extractLsb' pos len = a.extractLsb' pos len ||| b.extractLsb' pos len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_or, hi]

theorem bv_and_assoc (a b c : BitVec 32) : (a &&& b) &&& c = a &&& (b &&& c) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp [BitVec.getLsbD_and, Bool.and_assoc]

theorem bv_and_comm (a b : BitVec 32) : a &&& b = b &&& a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp [BitVec.getLsbD_and, Bool.and_comm]

theorem bv_and_self (a : BitVec 32) : a &&& a = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp

theorem mask_of_fixed {w base fixed m : BitVec 32}
    (hw : w &&& fixed = base &&& fixed) (hm : m &&& fixed = m) :
    w &&& m = base &&& m := by
  calc w &&& m = w &&& (m &&& fixed) := by rw [hm]
    _ = (w &&& fixed) &&& m := by rw [bv_and_comm m fixed, ← bv_and_assoc]
    _ = (base &&& fixed) &&& m := by rw [hw]
    _ = base &&& (m &&& fixed) := by rw [bv_and_assoc, bv_and_comm fixed m]
    _ = base &&& m := by rw [hm]

/-- If `w` agrees with `base` on `fixed`, and `base` disagrees with `c` on `m &&& fixed`,
then `(w &&& m == c) = false`. -/
theorem mask_ne_of_fixed {w base fixed m c : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hneq : ((base &&& (m &&& fixed)) == (c &&& fixed)) = false) :
    ((w &&& m) == c) = false := by
  cases h : ((w &&& m) == c)
  · rfl
  · exfalso
    have heq : w &&& m = c := beq_iff_eq.mp h
    have hsub := congrArg (fun x => x &&& fixed) heq
    rw [bv_and_assoc] at hsub
    have hm' : (m &&& fixed) &&& fixed = m &&& fixed := by rw [bv_and_assoc, bv_and_self]
    rw [mask_of_fixed hw hm'] at hsub
    rw [hsub, beq_self_eq_true] at hneq
    cases hneq

theorem word_ne_of_fixed {w base fixed c : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hneq : ((base &&& fixed) == (c &&& fixed)) = false) :
    (w == c) = false := by
  cases h : (w == c)
  · rfl
  · exfalso
    have heq : w = c := beq_iff_eq.mp h
    rw [heq] at hw
    rw [← hw, beq_self_eq_true] at hneq
    cases hneq

theorem getLsbD_of_fixed {w base fixed : BitVec 32} {i : Nat}
    (hw : w &&& fixed = base &&& fixed) (hi : fixed.getLsbD i = true) :
    w.getLsbD i = base.getLsbD i := by
  have := congrArg (fun x => x.getLsbD i) hw
  simpa [BitVec.getLsbD_and, hi] using this

theorem extract_of_fixed {w base fixed : BitVec 32} {pos len : Nat}
    (hw : w &&& fixed = base &&& fixed)
    (hfix : ∀ i : Fin len, fixed.getLsbD (pos + i.val) = true) :
    w.extractLsb' pos len = base.extractLsb' pos len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact getLsbD_of_fixed hw (hfix ⟨i, hi⟩)

/-- Reusable check that a word's fixed bits skip a whole list of `(mask, value)` guards in `Arm64.decode`. -/
def skipsAll (base fixed : BitVec 32) (guards : List (BitVec 32 × BitVec 32)) : Bool :=
  guards.all fun (m, c) => ((base &&& (m &&& fixed)) == (c &&& fixed)) == false

theorem skipsAll_mem {w base fixed : BitVec 32} {guards : List (BitVec 32 × BitVec 32)}
    (hw : w &&& fixed = base &&& fixed) (hs : skipsAll base fixed guards = true)
    {m c : BitVec 32} (hmem : (m, c) ∈ guards) :
    ((w &&& m) == c) = false := by
  have h1 := List.all_eq_true.mp hs (m, c) hmem
  exact mask_ne_of_fixed hw (by simpa using h1)

/-! ## State correspondence between `Ode.State` and `Arm64.State` -/

/-- General register `x0..x30` in `Ode.Machine`: `sp` occupies slot 4 (`Ode.RSP`), so `x4` occupies slot 31. -/
def armSlot (k : Nat) : Nat := if k = 4 then 31 else k

/-- Assembly name of general register `k` (`"x0"` .. `"x30"`). -/
def armRegName (k : Nat) : String := "x" ++ toString k

/-- Correspondence between an `Ode.State` and an `Arm64.State`. -/
structure AgreeState (st : Ode.State) (gs : Arm64.State) : Prop where
  running : gs.status = .Running
  gpr     : ∀ k : Fin 31, (gs.readReg64 (.gpr (BitVec.ofNat 5 k.val))).toNat = st.reg (armSlot k.val)
  sp      : gs.sp.toNat = st.reg Ode.RSP
  vec     : ∀ (v : Fin 32) (j : Fin 4), ((gs.readVReg128 (BitVec.ofNat 5 v.val)).extractLsb' (32 * j.val) 32).toNat = st.vec v.val j.val
  mem     : ∀ a : Nat, a < Ode.M64 → (gs.mem.read8 (BitVec.ofNat 64 a)).toNat = (st.mem a).val
  pc      : gs.pc.toNat = st.rip

theorem regIndex_armRegName : ∀ k : Fin 31, Ode.regIndex (armRegName k.val) = some (armSlot k.val) := by decide
theorem armSlot_ne_rsp : ∀ k : Fin 31, armSlot k.val ≠ Ode.RSP := by decide
theorem armSlot_inj : ∀ k j : Fin 31, armSlot k.val = armSlot j.val → k = j := by decide
theorem regIndex_sp : Ode.regIndex "sp" = some Ode.RSP := by decide
theorem toNat_ofNat5_ne31 : ∀ k : Fin 31, (BitVec.ofNat 5 k.val == 31#5) = false := by decide
theorem fromZRBits_fin31 : ∀ k : Fin 31, Arm64.Reg.fromZRBits (BitVec.ofNat 5 k.val) = .gpr (BitVec.ofNat 5 k.val) := by decide
theorem ofNat5_inj {a b : Fin 31} (h : BitVec.ofNat 5 a.val = BitVec.ofNat 5 b.val) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  have ha : a.val < 32 := by omega
  have hb : b.val < 32 := by omega
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact Fin.ext this

theorem ofNat5_inj32 {a b : Fin 32} (h : BitVec.ofNat 5 a.val = BitVec.ofNat 5 b.val) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this
  exact Fin.ext this

theorem toNat_append_eq {w m : Nat} (x : BitVec w) (y : BitVec m) :
    (x ++ y).toNat = x.toNat * 2 ^ m + y.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  let x' : BitVec (w + m) := BitVec.ofNat (w + m) x.toNat <<< m
  let y' : BitVec (w + m) := BitVec.ofNat (w + m) y.toNat
  have hxy : x ++ y = x' ||| y' := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_append, BitVec.getLsbD_or]
    simp only [x', y', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    by_cases him : i < m
    · simp [him, BitVec.getLsbD]
    · have hge : m ≤ i := by omega
      have hy0 : y.toNat.testBit i = false := testBit_eq_false_of_lt hy hge
      have himwm : i - m < w + m := by omega
      simp [him, hy0, himwm, BitVec.getLsbD]
  have hdisj : x' &&& y' = 0#(w + m) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [x', y', BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
               hi, decide_true, Bool.true_and]
    by_cases him : i < m
    · simp [him]
    · have hy0 : y.toNat.testBit i = false := testBit_eq_false_of_lt hy (by omega)
      simp [hy0]
  rw [hxy, ← BitVec.add_eq_or_of_and_eq_zero x' y' hdisj, BitVec.toNat_add]
  have hpow : 2 ^ w * 2 ^ m = 2 ^ (w + m) := (Nat.pow_add 2 w m).symm
  have hx_lt : x.toNat < 2 ^ (w + m) := by
    have : 2 ^ w ≤ 2 ^ (w + m) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right w m)
    omega
  have hy_lt : y.toNat < 2 ^ (w + m) := by
    have : 2 ^ m ≤ 2 ^ (w + m) := Nat.pow_le_pow_right (by decide) (Nat.le_add_left m w)
    omega
  have hx' : x'.toNat = x.toNat * 2 ^ m := by
    simp only [x', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt hx_lt]
    have hmul : x.toNat * 2 ^ m < 2 ^ (w + m) := by
      rw [← hpow]; exact Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos m)
    exact Nat.mod_eq_of_lt hmul
  have hy' : y'.toNat = y.toNat := by
    simp only [y', BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hy_lt
  rw [hx', hy']
  have hsum : x.toNat * 2 ^ m + y.toNat < 2 ^ (w + m) := by
    rw [← hpow]
    have hle : (x.toNat + 1) * 2 ^ m ≤ 2 ^ w * 2 ^ m := Nat.mul_le_mul_right (2 ^ m) hx
    rw [Nat.add_mul, Nat.one_mul] at hle
    omega
  exact Nat.mod_eq_of_lt hsum

/-- Eight-byte little-endian load agrees between `Arm64.Memory.read64` and `Ode.load` when the
8-byte access does not wrap past `2^64`. -/
theorem read64_eq_load {st : Ode.State} {gs : Arm64.State} (hA : AgreeState st gs)
    {a : Nat} (hfit : a + 8 ≤ Ode.M64) :
    (gs.mem.read64 (BitVec.ofNat 64 a)).toNat = Ode.load st.mem a 8 := by
  unfold Arm64.Memory.read64 Ode.load Ode.load Ode.load Ode.load Ode.load Ode.load Ode.load Ode.load Ode.load
  have hb : ∀ k : Nat, k < 8 →
      (gs.mem.read8 (BitVec.ofNat 64 a + BitVec.ofNat 64 k)).toNat = (st.mem (a + k)).val := by
    intro k hk
    have hadd : BitVec.ofNat 64 a + BitVec.ofNat 64 k = BitVec.ofNat 64 (a + k) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      unfold Ode.M64 at hfit
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hadd]
    exact hA.mem (a + k) (by omega)
  have h0 := hb 0 (by decide); have h1 := hb 1 (by decide); have h2 := hb 2 (by decide); have h3 := hb 3 (by decide)
  have h4 := hb 4 (by decide); have h5 := hb 5 (by decide); have h6 := hb 6 (by decide); have h7 := hb 7 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [toNat_append_eq, Nat.add_assoc]
  have e2 : (st.mem (a + (1 + 1))).val = (st.mem (a + 2)).val := rfl
  have e3 : (st.mem (a + (1 + (1 + 1)))).val = (st.mem (a + 3)).val := rfl
  have e4 : (st.mem (a + (1 + (1 + (1 + 1))))).val = (st.mem (a + 4)).val := rfl
  have e5 : (st.mem (a + (1 + (1 + (1 + (1 + 1)))))).val = (st.mem (a + 5)).val := rfl
  have e6 : (st.mem (a + (1 + (1 + (1 + (1 + (1 + 1))))))).val = (st.mem (a + 6)).val := rfl
  have e7 : (st.mem (a + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))).val = (st.mem (a + 7)).val := rfl
  rw [e2, e3, e4, e5, e6, e7, h0, h1, h2, h3, h4, h5, h6, h7]
  omega

/-- Stack-pointer 16-byte alignment agrees between `Arm64.State.spAligned` and `st.reg Ode.RSP % 16 = 0`. -/
theorem spAligned_iff {st : Ode.State} {gs : Arm64.State} (hA : AgreeState st gs) :
    gs.spAligned = decide (st.reg Ode.RSP % 16 = 0) := by
  unfold Arm64.State.spAligned
  have hmod : (gs.sp &&& 15#64).toNat = st.reg Ode.RSP % 16 := by
    rw [BitVec.toNat_and, hA.sp]
    change st.reg Ode.RSP &&& (2 ^ 4 - 1) = st.reg Ode.RSP % 16
    rw [Nat.and_two_pow_sub_one_eq_mod]
  cases h : ((gs.sp &&& 15#64) == 0#64)
  · have hne : (gs.sp &&& 15#64).toNat ≠ 0 := by
      intro hz
      have heq : gs.sp &&& 15#64 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hz)
      rw [heq, beq_self_eq_true] at h; cases h
    rw [hmod] at hne
    simp [hne]
  · have heq : gs.sp &&& 15#64 = 0#64 := beq_iff_eq.mp h
    have hz : (gs.sp &&& 15#64).toNat = 0 := by rw [heq]; rfl
    rw [hmod] at hz
    simp [hz]

/-! ## Row 1: `add_rrr` (`add D64, S64, P64 | .add .D .S .P | D = add64(S, P)`) -/

/-- Exact 32-bit encoding from `arm64/arm64.tab`:
`1 0 0 01011 00 0 PPPPP 000000 SSSSS DDDDD`. -/
def encodeAddRrr (d s p : Fin 31) : BitVec 32 :=
  0x8b000000#32 ||| (BitVec.ofNat 32 p.val <<< 16) ||| (BitVec.ofNat 32 s.val <<< 5) ||| BitVec.ofNat 32 d.val

def effectAddRrr : List Ode.Stmt :=
  [.set (.name "D") (.call "add64" [.name "S", .name "P"])]

def bindAddRrr (d s p : Fin 31) : Ode.Bind :=
  [("P", armRegName p.val), ("S", armRegName s.val), ("D", armRegName d.val)]

theorem encodeAddRrr_fixed (d s p : Fin 31) :
    encodeAddRrr d s p &&& 0xffe0fc00#32 = 0x8b000000#32 &&& 0xffe0fc00#32 := by
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have hp : p.val < 2 ^ 5 := by omega
  have h1 : (BitVec.ofNat 32 p.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hp (by decide)
  have h2 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hs (by decide)
  have h3 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hd (by decide)
  simp only [BitVec.shiftLeft_zero] at h3
  unfold encodeAddRrr
  simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]

theorem decode_add_rrr (d s p : Fin 31) :
    Arm64.decode (encodeAddRrr d s p) =
      some (.addSubShift .W64 .ADD (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0) := by
  have hf := encodeAddRrr_fixed d s p
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have hp : p.val < 2 ^ 5 := by omega
  have ex_d : (encodeAddRrr d s p).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeAddRrr; simp only [extract_or]
    have h0 : (0x8b000000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_s : (encodeAddRrr d s p).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeAddRrr; simp only [extract_or]
    have h0 : (0x8b000000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_p : (encodeAddRrr d s p).extractLsb' 16 5 = BitVec.ofNat 5 p.val := by
    unfold encodeAddRrr; simp only [extract_or]
    have h0 : (0x8b000000#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 p.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_imm6 : (encodeAddRrr d s p).extractLsb' 10 6 = 0#6 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_sh : (encodeAddRrr d s p).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have b31 : (encodeAddRrr d s p).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have b30 : (encodeAddRrr d s p).getLsbD 30 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have b29 : (encodeAddRrr d s p).getLsbD 29 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             b31, b30, b29, ex_d, ex_s, ex_p, ex_imm6, ex_sh, fromZRBits_fin31,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x10000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f800000#32) (c := 0x11000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f800000#32) (c := 0x12000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f800000#32) (c := 0x12800000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f800000#32) (c := 0x13000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7f800000#32) (c := 0x13800000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7c000000#32) (c := 0x14000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xff000010#32) (c := 0x54000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7e000000#32) (c := 0x34000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7e000000#32) (c := 0x36000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xff9ffc1f#32) (c := 0xd61f0000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x0a000000#32) (by decide),
             mask_of_fixed hf (m := 0x1f200000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  simp [Arm64.RegWidth.ofBool, Arm64.AddSubOp.ofBits, Arm64.ShiftType.ofBits]

theorem agree_add_rrr (d s p : Fin 31) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeAddRrr d s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectAddRrr, bindAddRrr d s p, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) ((st.reg (armSlot s.val) + st.reg (armSlot p.val)) % Ode.M64)
  let st' : Ode.State := Ode.noted (bindAddRrr d s p) st0 (.set (.name "D") (.call "add64" [.name "S", .name "P"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectAddRrr, bindAddRrr d s p, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectAddRrr, Ode.execStmt, Ode.isUnknown,
          Ode.value, Ode.values, Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf,
          bindAddRrr, List.lookup, regIndex_armRegName, Ode.prim, st', st1, st0]
  refine ⟨.addSubShift .W64 .ADD (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0,
          st', decode_add_rrr d s p, hexec, ?_, ?_⟩
  · have hadd : (Arm64.AddWithCarry64
                  (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)))
                  (gs.readReg64 (.gpr (BitVec.ofNat 5 p.val))) false).1 =
                gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) +
                  gs.readReg64 (.gpr (BitVec.ofNat 5 p.val)) := by
      simp only [Arm64.AddWithCarry64, Bool.false_eq_true, ↓reduceIte, BitVec.zero_add]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_add]
      have hs64 := (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))).isLt
      have hp64 := (gs.readReg64 (.gpr (BitVec.ofNat 5 p.val))).isLt
      omega
    have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
        (.addSubShift .W64 .ADD (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0) gs =
        (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val))
          (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) + gs.readReg64 (.gpr (BitVec.ofNat 5 p.val)))).advancePC := by
      simp [Arm64.execInstWithSvc, Arm64.execAddSubShift, Arm64.evalAddSub,
            Arm64.State.readReg, Arm64.State.writeReg, Arm64.shiftVal, Arm64.shift64, hadd]
    rw [hgs]
    refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.readReg64, Arm64.State.writeReg64,
                 Arm64.RegFile.read, Arm64.RegFile.write, toNat_ofNat5_ne31, Bool.false_eq_true, ↓reduceIte,
                 Ode.setReg, Ode.noted]
      by_cases hkd : k = d
      · subst hkd
        simp only [↓reduceIte]
        have hs := hA.gpr s; have hp := hA.gpr p
        simp only [Arm64.State.readReg64, Arm64.RegFile.read, toNat_ofNat5_ne31, Bool.false_eq_true, ↓reduceIte] at hs hp
        rw [BitVec.toNat_add, hs, hp]
        change (st.reg (armSlot s.val) + st.reg (armSlot p.val)) % Ode.M64 = _
        rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
      · have hne5 : BitVec.ofNat 5 k.val ≠ BitVec.ofNat 5 d.val := fun e => hkd (ofNat5_inj e)
        have hnes : armSlot k.val ≠ armSlot d.val := fun e => hkd (armSlot_inj k d e)
        simp only [hne5, hnes, ↓reduceIte]
        have hk := hA.gpr k
        simpa [Arm64.State.readReg64, Arm64.RegFile.read, toNat_ofNat5_ne31] using hk
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted,
             (armSlot_ne_rsp d).symm] using hA.sp
    · intro v j
      simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Arm64.State.readVReg128,
             Ode.setReg, Ode.noted] using hA.vec v j
    · intro a ha
      simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.mem a ha
    · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted,
                 BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
      have : 4 % 2 ^ 64 = 4 := by decide
      unfold Ode.M64 at hpc
      rw [this, Nat.mod_eq_of_lt hpc]
  · simp [Arm64.execInstWithSvc, Arm64.execAddSubShift, Arm64.evalAddSub,
          Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC]

/-! ## Row 2: `ldr64_sp` (`ldr D64, [sp, N] | .ldr64_sp .D N | D = mem64(on16(sp), N)`) -/

/-- Exact 32-bit encoding from `arm64/arm64.tab`:
`11 111 0 01 01 nnnnnnnnnnnn 11111 DDDDD ; N=n*8`. -/
def encodeLdr64Sp (d : Fin 31) (n : Fin 4096) : BitVec 32 :=
  0xf94003e0#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| BitVec.ofNat 32 d.val

def effectLdr64Sp : List Ode.Stmt :=
  [.set (.name "D") (.call "mem64" [.call "on16" [.name "sp"], .name "N"])]

def bindLdr64Sp (d : Fin 31) (numStr : String) : Ode.Bind :=
  [("N", numStr), ("D", armRegName d.val)]

theorem encodeLdr64Sp_fixed (d : Fin 31) (n : Fin 4096) :
    encodeLdr64Sp d n &&& 0xffc003e0#32 = 0xf94003e0#32 &&& 0xffc003e0#32 := by
  have hd : d.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := by omega
  have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc003e0#32 = 0#32 := field_and_eq_zero hn (by decide)
  have h2 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffc003e0#32 = 0#32 := field_and_eq_zero hd (by decide)
  simp only [BitVec.shiftLeft_zero] at h2
  unfold encodeLdr64Sp
  simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]

theorem decode_ldr64_sp (d : Fin 31) (n : Fin 4096) :
    Arm64.decode (encodeLdr64Sp d n) =
      some (.ldr .W64 .X64 false (.gpr (BitVec.ofNat 5 d.val)) (.Offset .sp (BitVec.ofNat 64 (n.val * 8)))) := by
  have hf := encodeLdr64Sp_fixed d n
  have hd : d.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := by omega
  have ex_d : (encodeLdr64Sp d n).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeLdr64Sp; simp only [extract_or]
    have h0 : (0xf94003e0#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_n : (encodeLdr64Sp d n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeLdr64Sp; simp only [extract_or]
    have h0 : (0xf94003e0#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_rn : (encodeLdr64Sp d n).extractLsb' 5 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_sz : (encodeLdr64Sp d n).extractLsb' 30 2 = 3#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeLdr64Sp d n).extractLsb' 22 2 = 1#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hshift : (BitVec.ofNat 12 n.val).zeroExtend 64 <<< 3 = BitVec.ofNat 64 (n.val * 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have : n.val < 4096 := n.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             ex_d, ex_n, ex_rn, ex_sz, ex_opc, fromZRBits_fin31,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x10000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f800000#32) (c := 0x11000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f800000#32) (c := 0x12000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f800000#32) (c := 0x12800000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f800000#32) (c := 0x13000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7f800000#32) (c := 0x13800000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7c000000#32) (c := 0x14000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7e000000#32) (c := 0x34000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7e000000#32) (c := 0x36000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xff000010#32) (c := 0x54000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xff9ffc1f#32) (c := 0xd61f0000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x0a000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f200000#32) (c := 0x0b000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1fe00000#32) (c := 0x0b200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1fe0fc00#32) (c := 0x1a000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x3fe00410#32) (c := 0x3a400000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x3fe00800#32) (c := 0x1a800000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7fff0000#32) (c := 0x5ac00000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7fe0e000#32) (c := 0x1ac04000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7fe00000#32) (c := 0x1ac00000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7f000000#32) (c := 0x1b000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x7f800000#32) (c := 0x28000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x3e000000#32) (c := 0x28000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffc00000#32) (c := 0xf9800000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe00c00#32) (c := 0xf8800000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe00c00#32) (c := 0xf8a00800#32) (by decide),
             mask_ne_of_fixed hf (m := 0x3f200c00#32) (c := 0x38200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0x3f200c00#32) (c := 0x19000000#32) (by decide),
             mask_of_fixed hf (m := 0x3f000000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  simp only [Arm64.Reg.fromSPBits, Arm64.mkLoadStoreInst, BitVec.toNat_ofNat]
  rw [hshift]
  rfl

/-- `ldr64_sp`, misaligned stack pointer: BOTH models fault (`none` in `Ode.Machine`,
`SP alignment fault` in Google's `Arm64`). -/
theorem agree_ldr64_sp_fault (d : Fin 31) (n : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (_hnum : Ode.readInt numStr = some ((n.val * 8 : Nat) : Int))
    (hmis : st.reg Ode.RSP % 16 ≠ 0) :
    ∃ ginst,
      Arm64.decode (encodeLdr64Sp d n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectLdr64Sp, bindLdr64Sp d numStr, next⟩ u st = none ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).status = .Exception "SP alignment fault" := by
  refine ⟨.ldr .W64 .X64 false (.gpr (BitVec.ofNat 5 d.val)) (.Offset .sp (BitVec.ofNat 64 (n.val * 8))),
          decode_ldr64_sp d n, ?_, ?_⟩
  · simp [Ode.exec, Ode.execAll, effectLdr64Sp, Ode.execStmt, Ode.isUnknown,
          Ode.value, Ode.values, Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf,
          bindLdr64Sp, List.lookup, regIndex_sp, Ode.prim, hmis]
  · have hsp : gs.spAligned = false := by rw [spAligned_iff hA]; simp [hmis]
    simp [Arm64.execInstWithSvc, Arm64.execLdr, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.State.setStatus, hsp]

/-- `ldr64_sp`, aligned stack pointer and readable memory without 64-bit address wrap:
BOTH models load the same 8 bytes into `d`, advance `pc` by 4, and leave everything else unchanged. -/
theorem agree_ldr64_sp (d : Fin 31) (n : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some ((n.val * 8 : Nat) : Int))
    (hal : st.reg Ode.RSP % 16 = 0)
    (hfit : st.reg Ode.RSP + n.val * 8 + 8 ≤ Ode.M64)
    (hread : gs.mem.canRead (gs.sp + BitVec.ofNat 64 (n.val * 8)) 8 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeLdr64Sp d n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectLdr64Sp, bindLdr64Sp d numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hnlt : n.val * 8 < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  have hmodN : (((n.val : Int) * 8) % (Ode.M64 : Int)).toNat = n.val * 8 := by
    have hcast : ((n.val : Int) * 8) = ((n.val * 8 : Nat) : Int) := by simp
    rw [hcast, Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hnlt)]; rfl
  have hea_nat : (st.reg Ode.RSP + n.val * 8) % Ode.M64 = st.reg Ode.RSP + n.val * 8 :=
    Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.sp + BitVec.ofNat 64 (n.val * 8) = BitVec.ofNat 64 (st.reg Ode.RSP + n.val * 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.sp]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt (by omega)]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) (Ode.load st.mem (st.reg Ode.RSP + n.val * 8) 8)
  let st' : Ode.State := Ode.noted (bindLdr64Sp d numStr) st0 (.set (.name "D") (.call "mem64" [.call "on16" [.name "sp"], .name "N"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectLdr64Sp, bindLdr64Sp d numStr, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.read (st.reg Ode.RSP + n.val * 8) 8 = true := by
      simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectLdr64Sp, Ode.execStmt, Ode.isUnknown,
          Ode.value, Ode.values, Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf,
          bindLdr64Sp, List.lookup, regIndex_sp, regIndex_armRegName, Ode.prim, Ode.sumList,
          hnum, hal, hmodN, hea_nat, hall, st', st1, st0]
  have hsp : gs.spAligned = true := by rw [spAligned_iff hA]; simp [hal]
  have hread' : gs.mem.canRead (BitVec.ofNat 64 (st.reg Ode.RSP + n.val * 8)) 8 = true := by
    rwa [← hea_bv]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.ldr .W64 .X64 false (.gpr (BitVec.ofNat 5 d.val)) (.Offset .sp (BitVec.ofNat 64 (n.val * 8)))) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) (gs.mem.read64 (BitVec.ofNat 64 (st.reg Ode.RSP + n.val * 8)))).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execLdr, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.State.readReg64, Arm64.MemWidth.bytes,
          Arm64.Memory.readSized, Arm64.State.writeReg, hsp, hea_bv, hread']
  refine ⟨.ldr .W64 .X64 false (.gpr (BitVec.ofNat 5 d.val)) (.Offset .sp (BitVec.ofNat 64 (n.val * 8))),
          st', decode_ldr64_sp d n, hexec, ?_, ?_⟩
  · rw [hgs]
    refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.readReg64, Arm64.State.writeReg64,
                 Arm64.RegFile.read, Arm64.RegFile.write, toNat_ofNat5_ne31, Bool.false_eq_true, ↓reduceIte,
                 Ode.setReg, Ode.noted]
      by_cases hkd : k = d
      · subst hkd
        simp only [↓reduceIte]
        have hld := read64_eq_load hA hfit
        have hlt : Ode.load st.mem (st.reg Ode.RSP + n.val * 8) 8 < Ode.M64 := by
          rw [← hld]; exact (gs.mem.read64 _).isLt
        rw [hld, Nat.mod_eq_of_lt hlt]
      · have hne5 : BitVec.ofNat 5 k.val ≠ BitVec.ofNat 5 d.val := fun e => hkd (ofNat5_inj e)
        have hnes : armSlot k.val ≠ armSlot d.val := fun e => hkd (armSlot_inj k d e)
        simp only [hne5, hnes, ↓reduceIte]
        have hk := hA.gpr k
        simpa [Arm64.State.readReg64, Arm64.RegFile.read, toNat_ofNat5_ne31] using hk
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted,
             (armSlot_ne_rsp d).symm] using hA.sp
    · intro v j
      simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Arm64.State.readVReg128,
             Ode.setReg, Ode.noted] using hA.vec v j
    · intro a ha
      simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.mem a ha
    · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted,
                 BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
      have : 4 % 2 ^ 64 = 4 := by decide
      unfold Ode.M64 at hpc
      rw [this, Nat.mod_eq_of_lt hpc]
  · rw [hgs]; rfl

/-! ## Shared list of `Arm64.decode` guards before the SIMD sections (37 & 38) -/

/-- All `(mask, expected)` branch guards in `Arm64.decode` before section 37 (`simdThreeSame`). -/
def guardsBeforeSimdThreeSame : List (BitVec 32 × BitVec 32) := [
  (0xffe0001f#32, 0xd4000001#32), (0xffe0001f#32, 0xd4200000#32), (0xfffff01f#32, 0xd503201f#32),
  (0xffff0000#32, 0x00000000#32), (0xffffffe0#32, 0xd50b7420#32), (0x1f000000#32, 0x10000000#32),
  (0x1f800000#32, 0x11000000#32), (0x1f800000#32, 0x12000000#32), (0x1f800000#32, 0x12800000#32),
  (0x1f800000#32, 0x13000000#32), (0x7f800000#32, 0x13800000#32), (0x7c000000#32, 0x14000000#32),
  (0x7e000000#32, 0x34000000#32), (0x7e000000#32, 0x36000000#32), (0xff000010#32, 0x54000000#32),
  (0xff9ffc1f#32, 0xd61f0000#32), (0x1f000000#32, 0x0a000000#32), (0x1f200000#32, 0x0b000000#32),
  (0x1fe00000#32, 0x0b200000#32), (0x1fe0fc00#32, 0x1a000000#32), (0x3fe00410#32, 0x3a400000#32),
  (0x3fe00800#32, 0x1a800000#32), (0x7fff0000#32, 0x5ac00000#32), (0x7fe0e000#32, 0x1ac04000#32),
  (0x7fe00000#32, 0x1ac00000#32), (0x7f000000#32, 0x1b000000#32), (0x7f800000#32, 0x28000000#32),
  (0x3e000000#32, 0x28000000#32), (0xffc00000#32, 0xf9800000#32), (0xffe00c00#32, 0xf8800000#32),
  (0xffe00c00#32, 0xf8a00800#32), (0x3f200c00#32, 0x38200000#32), (0x3f200c00#32, 0x19000000#32),
  (0x3f000000#32, 0x39000000#32), (0x3f000000#32, 0x38000000#32), (0x3f000000#32, 0x18000000#32),
  (0x3f000000#32, 0x1c000000#32), (0x3fbffc00#32, 0x089ffc00#32), (0x3fff7c00#32, 0x085f7c00#32),
  (0x3fe07c00#32, 0x08007c00#32), (0xbfff0000#32, 0x887f0000#32), (0xbfe00000#32, 0x88200000#32),
  (0x3fa07c00#32, 0x08a07c00#32), (0xbfa07c00#32, 0x08207c00#32), (0xffd00000#32, 0xd5100000#32),
  (0xfffff01f#32, 0xd503301f#32), (0x3f800000#32, 0x2c000000#32), (0x3e000000#32, 0x2c000000#32),
  (0x3f000000#32, 0x3d000000#32), (0x3f000000#32, 0x3c000000#32), (0xbfbf0000#32, 0x0c000000#32),
  (0xbfa00000#32, 0x0c800000#32), (0xbffff000#32, 0x0d40c000#32), (0xbfe0f000#32, 0x0dc0c000#32),
  (0xbfe00000#32, 0x0d800000#32), (0xbfbf0000#32, 0x0d000000#32), (0xbfe00000#32, 0x0dc00000#32),
  (0xffffcc00#32, 0x4e284800#32),
  (0x7f20fc00#32, 0x1e200000#32), (0x9f800400#32, 0x0f000400#32), (0xbfe08c00#32, 0x0e000000#32),
  (0xfffffc00#32, 0x5ef1b800#32), (0xffe0fc00#32, 0x5e000400#32), (0x9fe08400#32, 0x0e000400#32)
]

/-- Any word whose fixed bits skip all earlier guards and match `0x9f200400 == 0x0e200400`
decodes as `Arm64.Instr.simdThreeSame`. -/
theorem decode_at_simdThreeSame {w base fixed : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hnop : ((base &&& fixed) == (0xd503201f#32 &&& fixed)) = false)
    (hskip : skipsAll base fixed guardsBeforeSimdThreeSame = true)
    (hmatch : (0x9f200400#32 &&& fixed = 0x9f200400#32) ∧ (base &&& 0x9f200400#32 = 0x0e200400#32)) :
    Arm64.decode w =
      some (.simdThreeSame (w.getLsbD 30) (w.getLsbD 29) (w.extractLsb' 22 2)
        (w.extractLsb' 16 5) (w.extractLsb' 11 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5)) := by
  have sk : ∀ m c, (m, c) ∈ guardsBeforeSimdThreeSame → ((w &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hw hskip hm
  have hhit : w &&& 0x9f200400#32 = 0x0e200400#32 := by rw [mask_of_fixed hw hmatch.1, hmatch.2]
  unfold Arm64.decode
  simp only [word_ne_of_fixed hw hnop,
             sk 0xffe0001f#32 0xd4000001#32 (by decide), sk 0xffe0001f#32 0xd4200000#32 (by decide),
             sk 0xfffff01f#32 0xd503201f#32 (by decide), sk 0xffff0000#32 0x00000000#32 (by decide),
             sk 0xffffffe0#32 0xd50b7420#32 (by decide), sk 0x1f000000#32 0x10000000#32 (by decide),
             sk 0x1f800000#32 0x11000000#32 (by decide), sk 0x1f800000#32 0x12000000#32 (by decide),
             sk 0x1f800000#32 0x12800000#32 (by decide), sk 0x1f800000#32 0x13000000#32 (by decide),
             sk 0x7f800000#32 0x13800000#32 (by decide), sk 0x7c000000#32 0x14000000#32 (by decide),
             sk 0x7e000000#32 0x34000000#32 (by decide), sk 0x7e000000#32 0x36000000#32 (by decide),
             sk 0xff000010#32 0x54000000#32 (by decide), sk 0xff9ffc1f#32 0xd61f0000#32 (by decide),
             sk 0x1f000000#32 0x0a000000#32 (by decide), sk 0x1f200000#32 0x0b000000#32 (by decide),
             sk 0x1fe00000#32 0x0b200000#32 (by decide), sk 0x1fe0fc00#32 0x1a000000#32 (by decide),
             sk 0x3fe00410#32 0x3a400000#32 (by decide), sk 0x3fe00800#32 0x1a800000#32 (by decide),
             sk 0x7fff0000#32 0x5ac00000#32 (by decide), sk 0x7fe0e000#32 0x1ac04000#32 (by decide),
             sk 0x7fe00000#32 0x1ac00000#32 (by decide), sk 0x7f000000#32 0x1b000000#32 (by decide),
             sk 0x7f800000#32 0x28000000#32 (by decide), sk 0x3e000000#32 0x28000000#32 (by decide),
             sk 0xffc00000#32 0xf9800000#32 (by decide), sk 0xffe00c00#32 0xf8800000#32 (by decide),
             sk 0xffe00c00#32 0xf8a00800#32 (by decide), sk 0x3f200c00#32 0x38200000#32 (by decide),
             sk 0x3f200c00#32 0x19000000#32 (by decide), sk 0x3f000000#32 0x39000000#32 (by decide),
             sk 0x3f000000#32 0x38000000#32 (by decide), sk 0x3f000000#32 0x18000000#32 (by decide),
             sk 0x3f000000#32 0x1c000000#32 (by decide), sk 0x3fbffc00#32 0x089ffc00#32 (by decide),
             sk 0x3fff7c00#32 0x085f7c00#32 (by decide), sk 0x3fe07c00#32 0x08007c00#32 (by decide),
             sk 0xbfff0000#32 0x887f0000#32 (by decide), sk 0xbfe00000#32 0x88200000#32 (by decide),
             sk 0x3fa07c00#32 0x08a07c00#32 (by decide), sk 0xbfa07c00#32 0x08207c00#32 (by decide),
             sk 0xffd00000#32 0xd5100000#32 (by decide), sk 0xfffff01f#32 0xd503301f#32 (by decide),
             sk 0x3f800000#32 0x2c000000#32 (by decide), sk 0x3e000000#32 0x2c000000#32 (by decide),
             sk 0x3f000000#32 0x3d000000#32 (by decide), sk 0x3f000000#32 0x3c000000#32 (by decide),
             sk 0xbfbf0000#32 0x0c000000#32 (by decide), sk 0xbfa00000#32 0x0c800000#32 (by decide),
             sk 0xbffff000#32 0x0d40c000#32 (by decide), sk 0xbfe0f000#32 0x0dc0c000#32 (by decide),
             sk 0xbfe00000#32 0x0d800000#32 (by decide), sk 0xbfbf0000#32 0x0d000000#32 (by decide),
             sk 0xbfe00000#32 0x0dc00000#32 (by decide),
             sk 0xffffcc00#32 0x4e284800#32 (by decide), sk 0x7f20fc00#32 0x1e200000#32 (by decide),
             sk 0x9f800400#32 0x0f000400#32 (by decide), sk 0xbfe08c00#32 0x0e000000#32 (by decide),
             sk 0xfffffc00#32 0x5ef1b800#32 (by decide), sk 0xffe0fc00#32 0x5e000400#32 (by decide),
             sk 0x9fe08400#32 0x0e000400#32 (by decide),
             hhit, beq_self_eq_true, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Any word whose fixed bits skip all earlier guards and `simdThreeSame`, and match
`0x9f3e0c00 == 0x0e200800`, decodes as `Arm64.Instr.simdTwoRegMisc`. -/
theorem decode_at_simdTwoRegMisc {w base fixed : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hnop : ((base &&& fixed) == (0xd503201f#32 &&& fixed)) = false)
    (hskip : skipsAll base fixed ((0x9f200400#32, 0x0e200400#32) :: guardsBeforeSimdThreeSame) = true)
    (hmatch : (0x9f3e0c00#32 &&& fixed = 0x9f3e0c00#32) ∧ (base &&& 0x9f3e0c00#32 = 0x0e200800#32)) :
    Arm64.decode w =
      some (.simdTwoRegMisc (w.getLsbD 30) (w.getLsbD 29) (w.extractLsb' 22 2)
        (w.extractLsb' 12 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5)) := by
  have sk : ∀ m c, (m, c) ∈ (0x9f200400#32, 0x0e200400#32) :: guardsBeforeSimdThreeSame → ((w &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hw hskip hm
  have hhit : w &&& 0x9f3e0c00#32 = 0x0e200800#32 := by rw [mask_of_fixed hw hmatch.1, hmatch.2]
  unfold Arm64.decode
  simp only [word_ne_of_fixed hw hnop,
             sk 0xffe0001f#32 0xd4000001#32 (by decide), sk 0xffe0001f#32 0xd4200000#32 (by decide),
             sk 0xfffff01f#32 0xd503201f#32 (by decide), sk 0xffff0000#32 0x00000000#32 (by decide),
             sk 0xffffffe0#32 0xd50b7420#32 (by decide), sk 0x1f000000#32 0x10000000#32 (by decide),
             sk 0x1f800000#32 0x11000000#32 (by decide), sk 0x1f800000#32 0x12000000#32 (by decide),
             sk 0x1f800000#32 0x12800000#32 (by decide), sk 0x1f800000#32 0x13000000#32 (by decide),
             sk 0x7f800000#32 0x13800000#32 (by decide), sk 0x7c000000#32 0x14000000#32 (by decide),
             sk 0x7e000000#32 0x34000000#32 (by decide), sk 0x7e000000#32 0x36000000#32 (by decide),
             sk 0xff000010#32 0x54000000#32 (by decide), sk 0xff9ffc1f#32 0xd61f0000#32 (by decide),
             sk 0x1f000000#32 0x0a000000#32 (by decide), sk 0x1f200000#32 0x0b000000#32 (by decide),
             sk 0x1fe00000#32 0x0b200000#32 (by decide), sk 0x1fe0fc00#32 0x1a000000#32 (by decide),
             sk 0x3fe00410#32 0x3a400000#32 (by decide), sk 0x3fe00800#32 0x1a800000#32 (by decide),
             sk 0x7fff0000#32 0x5ac00000#32 (by decide), sk 0x7fe0e000#32 0x1ac04000#32 (by decide),
             sk 0x7fe00000#32 0x1ac00000#32 (by decide), sk 0x7f000000#32 0x1b000000#32 (by decide),
             sk 0x7f800000#32 0x28000000#32 (by decide), sk 0x3e000000#32 0x28000000#32 (by decide),
             sk 0xffc00000#32 0xf9800000#32 (by decide), sk 0xffe00c00#32 0xf8800000#32 (by decide),
             sk 0xffe00c00#32 0xf8a00800#32 (by decide), sk 0x3f200c00#32 0x38200000#32 (by decide),
             sk 0x3f200c00#32 0x19000000#32 (by decide), sk 0x3f000000#32 0x39000000#32 (by decide),
             sk 0x3f000000#32 0x38000000#32 (by decide), sk 0x3f000000#32 0x18000000#32 (by decide),
             sk 0x3f000000#32 0x1c000000#32 (by decide), sk 0x3fbffc00#32 0x089ffc00#32 (by decide),
             sk 0x3fff7c00#32 0x085f7c00#32 (by decide), sk 0x3fe07c00#32 0x08007c00#32 (by decide),
             sk 0xbfff0000#32 0x887f0000#32 (by decide), sk 0xbfe00000#32 0x88200000#32 (by decide),
             sk 0x3fa07c00#32 0x08a07c00#32 (by decide), sk 0xbfa07c00#32 0x08207c00#32 (by decide),
             sk 0xffd00000#32 0xd5100000#32 (by decide), sk 0xfffff01f#32 0xd503301f#32 (by decide),
             sk 0x3f800000#32 0x2c000000#32 (by decide), sk 0x3e000000#32 0x2c000000#32 (by decide),
             sk 0x3f000000#32 0x3d000000#32 (by decide), sk 0x3f000000#32 0x3c000000#32 (by decide),
             sk 0xbfbf0000#32 0x0c000000#32 (by decide), sk 0xbfa00000#32 0x0c800000#32 (by decide),
             sk 0xbffff000#32 0x0d40c000#32 (by decide), sk 0xbfe0f000#32 0x0dc0c000#32 (by decide),
             sk 0xbfe00000#32 0x0d800000#32 (by decide), sk 0xbfbf0000#32 0x0d000000#32 (by decide),
             sk 0xbfe00000#32 0x0dc00000#32 (by decide),
             sk 0xffffcc00#32 0x4e284800#32 (by decide), sk 0x7f20fc00#32 0x1e200000#32 (by decide),
             sk 0x9f800400#32 0x0f000400#32 (by decide), sk 0xbfe08c00#32 0x0e000000#32 (by decide),
             sk 0xfffffc00#32 0x5ef1b800#32 (by decide), sk 0xffe0fc00#32 0x5e000400#32 (by decide),
             sk 0x9fe08400#32 0x0e000400#32 (by decide), sk 0x9f200400#32 0x0e200400#32 (by decide),
             hhit, beq_self_eq_true, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-! ## Row 3: `eor_v` (`eor vX.16b, vY.16b, vZ.16b | .eor X Y Z | X = each32(xor32, Y, Z)`) -/

/-- Exact 32-bit encoding from `arm64/arm64.tab`:
`0 1 1 01110 00 1 ZZZZZ 00011 1 YYYYY XXXXX`. -/
def encodeEorV (x y z : Fin 32) : BitVec 32 :=
  0x6e201c00#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

def effectEorV : List Ode.Stmt :=
  [.vset (.name "X") (.call "each32" [.name "xor32", .name "Y", .name "Z"])]

def bindEorV (sx sy sz : String) : Ode.Bind :=
  [("Z", sz), ("Y", sy), ("X", sx)]

theorem encodeEorV_fixed (x y z : Fin 32) :
    encodeEorV x y z &&& 0xffe0fc00#32 = 0x6e201c00#32 &&& 0xffe0fc00#32 := by
  have hx : x.val < 2 ^ 5 := x.isLt
  have hy : y.val < 2 ^ 5 := y.isLt
  have hz : z.val < 2 ^ 5 := z.isLt
  have h1 : (BitVec.ofNat 32 z.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hz (by decide)
  have h2 : (BitVec.ofNat 32 y.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hy (by decide)
  have h3 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hx (by decide)
  simp only [BitVec.shiftLeft_zero] at h3
  unfold encodeEorV
  simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]

theorem decode_eor_v (x y z : Fin 32) :
    Arm64.decode (encodeEorV x y z) =
      some (.simdThreeSame true true 0#2 (BitVec.ofNat 5 z.val) 0b00011#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) := by
  have hf := encodeEorV_fixed x y z
  have hx : x.val < 2 ^ 5 := x.isLt
  have hy : y.val < 2 ^ 5 := y.isLt
  have hz : z.val < 2 ^ 5 := z.isLt
  rw [decode_at_simdThreeSame hf (by decide) (by decide) (by decide)]
  have ex_x : (encodeEorV x y z).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeEorV; simp only [extract_or]
    have h0 : (0x6e201c00#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_y : (encodeEorV x y z).extractLsb' 5 5 = BitVec.ofNat 5 y.val := by
    unfold encodeEorV; simp only [extract_or]
    have h0 : (0x6e201c00#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 y.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_z : (encodeEorV x y z).extractLsb' 16 5 = BitVec.ofNat 5 z.val := by
    unfold encodeEorV; simp only [extract_or]
    have h0 : (0x6e201c00#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 z.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have b30 : (encodeEorV x y z).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have b29 : (encodeEorV x y z).getLsbD 29 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have ex_sz : (encodeEorV x y z).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_op : (encodeEorV x y z).extractLsb' 11 5 = 0b00011#5 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [b30, b29, ex_sz, ex_z, ex_op, ex_y, ex_x]

theorem agree_eor_v (x y z : Fin 32) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeEorV x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectEorV, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let lanes : List Nat := [st.vec y.val 0 ^^^ st.vec z.val 0, st.vec y.val 1 ^^^ st.vec z.val 1,
                           st.vec y.val 2 ^^^ st.vec z.val 2, st.vec y.val 3 ^^^ st.vec z.val 3]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "each32" [.name "xor32", .name "Y", .name "Z"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectEorV, bind, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectEorV, Ode.execStmt, Ode.lanesOf, Ode.vecArg,
          hbx, hby, hbz, Ode.prim32, List.range, List.range.loop, List.zip, List.mapM, List.mapM.loop, lanes, st', st1, st0]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdThreeSame true true 0#2 (BitVec.ofNat 5 z.val) 0b00011#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) (gs.readVReg128 (BitVec.ofNat 5 y.val) ^^^ gs.readVReg128 (BitVec.ofNat 5 z.val))).advancePC := by
    simp [Arm64.execInstWithSvc]
  refine ⟨.simdThreeSame true true 0#2 (BitVec.ofNat 5 z.val) 0b00011#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val),
          st', decode_eor_v x y z, hexec, ?_, ?_⟩
  · rw [hgs]
    refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_⟩
    · intro k; simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Arm64.State.readReg64,
                      Ode.setVec, Ode.noted] using hA.gpr k
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.sp
    · intro v j
      simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.readVReg128, Arm64.State.writeVReg128,
                 Arm64.VRegFile.read, Arm64.VRegFile.write, Ode.setVec, Ode.noted]
      by_cases hvx : v = x
      · subst hvx
        simp only [↓reduceIte, j.isLt]
        have hx : ((gs.vregs.regs (BitVec.ofNat 5 y.val) ^^^ gs.vregs.regs (BitVec.ofNat 5 z.val)).extractLsb' (32 * j.val) 32) =
            (gs.vregs.regs (BitVec.ofNat 5 y.val)).extractLsb' (32 * j.val) 32 ^^^
            (gs.vregs.regs (BitVec.ofNat 5 z.val)).extractLsb' (32 * j.val) 32 := by
          apply BitVec.eq_of_getLsbD_eq; intro i hi
          simp [BitVec.getLsbD_xor, hi]
        rw [hx, BitVec.toNat_xor]
        have hy := hA.vec y j; have hz := hA.vec z j
        simp only [Arm64.State.readVReg128, Arm64.VRegFile.read] at hy hz
        rw [hy, hz]
        rcases j with ⟨j, hj⟩
        match j, hj with
        | 0, _ => rfl
        | 1, _ => rfl
        | 2, _ => rfl
        | 3, _ => rfl
      · have hne5 : BitVec.ofNat 5 v.val ≠ BitVec.ofNat 5 x.val := fun e => hvx (ofNat5_inj32 e)
        have hnev : v.val ≠ x.val := fun e => hvx (Fin.ext e)
        simp only [hne5, hnev, ↓reduceIte]
        have hv := hA.vec v j
        simpa [Arm64.State.readVReg128, Arm64.VRegFile.read] using hv
    · intro a ha
      simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.mem a ha
    · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted,
                 BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
      have : 4 % 2 ^ 64 = 4 := by decide
      unfold Ode.M64 at hpc
      rw [this, Nat.mod_eq_of_lt hpc]
  · rw [hgs]; rfl

/-! ## Row 4: `rev32_8h` (`rev32 vX.8h, vY.8h | .rev32 X Y | X = each32(ror32, Y, 16)`) -/

/-- Exact 32-bit encoding from `arm64/arm64.tab`:
`0 1 1 01110 01 10000 00000 10 YYYYY XXXXX`. -/
def encodeRev32 (x y : Fin 32) : BitVec 32 :=
  0x6e600800#32 ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

def effectRev32 : List Ode.Stmt :=
  [.vset (.name "X") (.call "each32" [.name "ror32", .name "Y", .number 16])]

def bindRev32 (sx sy : String) : Ode.Bind :=
  [("Y", sy), ("X", sx)]

theorem encodeRev32_fixed (x y : Fin 32) :
    encodeRev32 x y &&& 0xfffffc00#32 = 0x6e600800#32 &&& 0xfffffc00#32 := by
  have hx : x.val < 2 ^ 5 := x.isLt
  have hy : y.val < 2 ^ 5 := y.isLt
  have h1 : (BitVec.ofNat 32 y.val <<< 5) &&& 0xfffffc00#32 = 0#32 := field_and_eq_zero hy (by decide)
  have h2 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xfffffc00#32 = 0#32 := field_and_eq_zero hx (by decide)
  simp only [BitVec.shiftLeft_zero] at h2
  unfold encodeRev32
  simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]

theorem decode_rev32 (x y : Fin 32) :
    Arm64.decode (encodeRev32 x y) =
      some (.simdTwoRegMisc true true 1#2 0#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) := by
  have hf := encodeRev32_fixed x y
  have hx : x.val < 2 ^ 5 := x.isLt
  have hy : y.val < 2 ^ 5 := y.isLt
  rw [decode_at_simdTwoRegMisc hf (by decide) (by decide) (by decide)]
  have ex_x : (encodeRev32 x y).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeRev32; simp only [extract_or]
    have h0 : (0x6e600800#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hy (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_y : (encodeRev32 x y).extractLsb' 5 5 = BitVec.ofNat 5 y.val := by
    unfold encodeRev32; simp only [extract_or]
    have h0 : (0x6e600800#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 y.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have b30 : (encodeRev32 x y).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have b29 : (encodeRev32 x y).getLsbD 29 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have ex_sz : (encodeRev32 x y).extractLsb' 22 2 = 1#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_op : (encodeRev32 x y).extractLsb' 12 5 = 0#5 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [b30, b29, ex_sz, ex_op, ex_y, ex_x]

/-- Reversing the two 16-bit halfwords of a 32-bit word is identical to rotating right by 16 bits. -/
theorem rev16_eq_rotr16 (w : BitVec 32) :
    ((w &&& 0xffff#32) <<< 16 ||| (w >>> 16 &&& 0xffff#32)).toNat = Ode.rotr w.toNat 16 := by
  have h1 : ((w &&& 0xffff#32) <<< 16).toNat = (w.toNat % 65536) * 65536 := by
    have ha : (w &&& 0xffff#32).toNat = w.toNat % 65536 := by
      rw [BitVec.toNat_and]; change w.toNat &&& (2 ^ 16 - 1) = _; rw [Nat.and_two_pow_sub_one_eq_mod]
    rw [BitVec.toNat_shiftLeft, ha, Nat.shiftLeft_eq]
    have : w.toNat % 65536 < 65536 := Nat.mod_lt _ (by decide)
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : ((w >>> 16) &&& 0xffff#32).toNat = w.toNat / 65536 := by
    have hs : (w >>> 16).toNat = w.toNat / 65536 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hlt : w.toNat / 65536 < 65536 := by have := w.isLt; omega
    rw [BitVec.toNat_and, hs]; change (w.toNat / 65536) &&& (2 ^ 16 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  have hdisj : ((w &&& 0xffff#32) <<< 16) &&& ((w >>> 16) &&& 0xffff#32) = 0#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases h16 : i < 16
    · simp [h16]
    · have : (0xffff#32).getLsbD i = false := by revert i hi h16; decide
      simp [this]
  have hor : (((w &&& 0xffff#32) <<< 16) ||| ((w >>> 16) &&& 0xffff#32)).toNat =
      ((w &&& 0xffff#32) <<< 16).toNat + ((w >>> 16) &&& 0xffff#32).toNat := by
    have := BitVec.add_eq_or_of_and_eq_zero _ _ hdisj
    rw [← this, BitVec.toNat_add, h1, h2]
    have hlt1 : w.toNat % 65536 < 65536 := Nat.mod_lt _ (by decide)
    have hlt2 : w.toNat / 65536 < 65536 := by have := w.isLt; omega
    exact Nat.mod_eq_of_lt (by omega)
  rw [hor, h1, h2]; unfold Ode.rotr; omega

/-- Extracting each 32-bit lane of `w3 ++ w2 ++ w1 ++ w0` recovers `w0`, `w1`, `w2`, `w3`. -/
theorem extract_concat4 (w3 w2 w1 w0 : BitVec 32) :
    (w3 ++ w2 ++ w1 ++ w0).extractLsb' 0 32 = w0 ∧
    (w3 ++ w2 ++ w1 ++ w0).extractLsb' 32 32 = w1 ∧
    (w3 ++ w2 ++ w1 ++ w0).extractLsb' 64 32 = w2 ∧
    (w3 ++ w2 ++ w1 ++ w0).extractLsb' 96 32 = w3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb']; simp only [hi, decide_true, Bool.true_and, Nat.zero_add]
    rw [BitVec.getLsbD_append]; simp [hi]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb']; simp only [hi, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_append, ite_eq_right_iff.mpr (by omega), BitVec.getLsbD_append, ite_eq_left_iff.mpr (by omega)]
    congr 1; omega
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb']; simp only [hi, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_append, ite_eq_right_iff.mpr (by omega), BitVec.getLsbD_append, ite_eq_right_iff.mpr (by omega),
        BitVec.getLsbD_append, ite_eq_left_iff.mpr (by omega)]
    congr 1; omega
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb']; simp only [hi, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_append, ite_eq_right_iff.mpr (by omega), BitVec.getLsbD_append, ite_eq_right_iff.mpr (by omega),
        BitVec.getLsbD_append, ite_eq_right_iff.mpr (by omega)]
    congr 1; omega

theorem agree_rev32 (x y : Fin 32) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeRev32 x y) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectRev32, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let lanes : List Nat := [Ode.rotr (st.vec y.val 0) 16, Ode.rotr (st.vec y.val 1) 16,
                           Ode.rotr (st.vec y.val 2) 16, Ode.rotr (st.vec y.val 3) 16]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "each32" [.name "ror32", .name "Y", .number 16])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectRev32, bind, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectRev32, Ode.execStmt, Ode.lanesOf, Ode.vecArg,
          hbx, hby, Ode.value, Ode.prim32, List.range, List.range.loop, List.mapM, List.mapM.loop, lanes, st', st1, st0]
  let vn := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let rev16 (w : BitVec 32) : BitVec 32 := (w &&& 0xffff#32) <<< 16 ||| (w >>> 16 &&& 0xffff#32)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdTwoRegMisc true true 1#2 0#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val)
        (rev16 (vn.extractLsb' 96 32) ++ rev16 (vn.extractLsb' 64 32) ++
         rev16 (vn.extractLsb' 32 32) ++ rev16 (vn.extractLsb' 0 32))).advancePC := by
    simp [Arm64.execInstWithSvc, rev16, vn, List.range', List.foldl]
  refine ⟨.simdTwoRegMisc true true 1#2 0#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val),
          st', decode_rev32 x y, hexec, ?_, ?_⟩
  · rw [hgs]
    refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_⟩
    · intro k; simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Arm64.State.readReg64,
                      Ode.setVec, Ode.noted] using hA.gpr k
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.sp
    · intro v j
      simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.readVReg128, Arm64.State.writeVReg128,
                 Arm64.VRegFile.read, Arm64.VRegFile.write, Ode.setVec, Ode.noted]
      by_cases hvx : v = x
      · subst hvx
        simp only [↓reduceIte, j.isLt]
        have ⟨he0, he1, he2, he3⟩ := extract_concat4
          (rev16 (vn.extractLsb' 96 32)) (rev16 (vn.extractLsb' 64 32))
          (rev16 (vn.extractLsb' 32 32)) (rev16 (vn.extractLsb' 0 32))
        have hv0 := hA.vec y ⟨0, by decide⟩
        have hv1 := hA.vec y ⟨1, by decide⟩
        have hv2 := hA.vec y ⟨2, by decide⟩
        have hv3 := hA.vec y ⟨3, by decide⟩
        rcases j with ⟨j, hj⟩
        match j, hj with
        | 0, _ => rw [show 32 * (⟨0, by decide⟩ : Fin 4).val = 0 by rfl, he0, rev16_eq_rotr16]; exact congrArg (Ode.rotr · 16) hv0
        | 1, _ => rw [show 32 * (⟨1, by decide⟩ : Fin 4).val = 32 by rfl, he1, rev16_eq_rotr16]; exact congrArg (Ode.rotr · 16) hv1
        | 2, _ => rw [show 32 * (⟨2, by decide⟩ : Fin 4).val = 64 by rfl, he2, rev16_eq_rotr16]; exact congrArg (Ode.rotr · 16) hv2
        | 3, _ => rw [show 32 * (⟨3, by decide⟩ : Fin 4).val = 96 by rfl, he3, rev16_eq_rotr16]; exact congrArg (Ode.rotr · 16) hv3
      · have hne5 : BitVec.ofNat 5 v.val ≠ BitVec.ofNat 5 x.val := fun e => hvx (ofNat5_inj32 e)
        have hnev : v.val ≠ x.val := fun e => hvx (Fin.ext e)
        simp only [hne5, hnev, ↓reduceIte]
        have hv := hA.vec v j
        simpa [Arm64.State.readVReg128, Arm64.VRegFile.read] using hv
    · intro a ha
      simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.mem a ha
    · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted,
                 BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
      have : 4 % 2 ^ 64 = 4 := by decide
      unfold Ode.M64 at hpc
      rw [this, Nat.mod_eq_of_lt hpc]
  · rw [hgs]; rfl

end ArmAgree
