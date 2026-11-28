import Table
import Machine
import Arm64.Trusted.ISA.Decode
import Arm64.Trusted.ISA.Eval

/-!
# Agreement between `arm64.tab` and Google DeepMind's `arm64-semantics`

Standalone proof package. Depends only on the instruction-table definitions (`Table.lean`,
`Machine.lean`) and Google DeepMind's `Arm64.Trusted.ISA` (`Decode`, `Eval`).

All 54 rows of `arm64/arm64.tab` are proved in this file (58 `agree_` theorems) to agree with
Google's decoder (`Arm64.decode`) and evaluator (`Arm64.execInstWithSvc Arm64.noSyscalls`),
spanning integer arithmetic, memory loads and stores (including the 16-byte SP-alignment fault),
comparisons, conditional and unconditional branches, calls, returns, and 128-bit NEON operations.
-/

namespace ArmAgree

-- Register placeholders are never condition-flag names in `Ode.flagVal`.
@[simp] private theorem flagVal_B (s : Ode.State) : Ode.flagVal s "B" = none := rfl
@[simp] private theorem flagVal_D (s : Ode.State) : Ode.flagVal s "D" = none := rfl
@[simp] private theorem flagVal_P (s : Ode.State) : Ode.flagVal s "P" = none := rfl
@[simp] private theorem flagVal_S (s : Ode.State) : Ode.flagVal s "S" = none := rfl
@[simp] private theorem flagVal_X (s : Ode.State) : Ode.flagVal s "X" = none := rfl
@[simp] private theorem flagVal_Y (s : Ode.State) : Ode.flagVal s "Y" = none := rfl
@[simp] private theorem flagVal_Z (s : Ode.State) : Ode.flagVal s "Z" = none := rfl
@[simp] private theorem flagVal_sp (s : Ode.State) : Ode.flagVal s "sp" = none := rfl

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

/-- Correspondence between an `Ode.State` and an `Arm64.State`.
Note `cf`: AArch64's `PSTATE.C` is the no-borrow carry bit (`x >= y`), whereas Ode's `cf` is
unsigned borrow (`below(x, y)`), so `gs.pstate.c = !st.cf`. -/
structure AgreeState (st : Ode.State) (gs : Arm64.State) : Prop where
  running : gs.status = .Running
  gpr     : ∀ k : Fin 31, (gs.readReg64 (.gpr (BitVec.ofNat 5 k.val))).toNat = st.reg (armSlot k.val)
  sp      : gs.sp.toNat = st.reg Ode.RSP
  vec     : ∀ (v : Fin 32) (j : Fin 4), ((gs.readVReg128 (BitVec.ofNat 5 v.val)).extractLsb' (32 * j.val) 32).toNat = st.vec v.val j.val
  mem     : ∀ a : Nat, a < Ode.M64 → (gs.mem.read8 (BitVec.ofNat 64 a)).toNat = (st.mem a).val
  pc      : gs.pc.toNat = st.rip
  zf      : gs.pstate.z = st.zf
  cf      : gs.pstate.c = !st.cf

theorem regIndex_armRegName : ∀ k : Fin 31, Ode.regIndex (armRegName k.val) = some (armSlot k.val) := by decide
theorem armSlot_ne_rsp : ∀ k : Fin 31, armSlot k.val ≠ Ode.RSP := by decide
theorem armSlot_inj : ∀ k j : Fin 31, armSlot k.val = armSlot j.val → k = j := by decide
theorem regIndex_sp : Ode.regIndex "sp" = some Ode.RSP := by decide
theorem toNat_ofNat5_ne31 : ∀ k : Fin 31, (BitVec.ofNat 5 k.val == 31#5) = false := by decide
theorem fromZRBits_fin31 : ∀ k : Fin 31, Arm64.Reg.fromZRBits (BitVec.ofNat 5 k.val) = .gpr (BitVec.ofNat 5 k.val) := by decide
theorem fromSPBits_fin31 : ∀ k : Fin 31, Arm64.Reg.fromSPBits (BitVec.ofNat 5 k.val) = .gpr (BitVec.ofNat 5 k.val) := by decide
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
    refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.zf
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.cf
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
    refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.zf
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.cf
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
    refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.zf
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.cf
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
    refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.zf
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.cf
  · rw [hgs]; rfl

/-! ## Row 5: `ldrb` (`ldrb D32, [B64, N] | .ldrb .D .B N | D = mem8(B, N)`) -/

/-- Exact 32-bit encoding from `arm64/arm64.tab`:
`00 111 0 01 01 nnnnnnnnnnnn BBBBB DDDDD ; N=n*1`. -/
def encodeLdrb (d b : Fin 31) (n : Fin 4096) : BitVec 32 :=
  0x39400000#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| (BitVec.ofNat 32 b.val <<< 5) ||| BitVec.ofNat 32 d.val

def effectLdrb : List Ode.Stmt :=
  [.set (.name "D") (.call "mem8" [.name "B", .name "N"])]

def bindLdrb (d b : Fin 31) (numStr : String) : Ode.Bind :=
  [("N", numStr), ("B", armRegName b.val), ("D", armRegName d.val)]

theorem encodeLdrb_fixed (d b : Fin 31) (n : Fin 4096) :
    encodeLdrb d b n &&& 0xffc00000#32 = 0x39400000#32 &&& 0xffc00000#32 := by
  have hd : d.val < 2 ^ 5 := by omega
  have hb : b.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := by omega
  have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hn (by decide)
  have h2 : (BitVec.ofNat 32 b.val <<< 5) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hb (by decide)
  have h3 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hd (by decide)
  simp only [BitVec.shiftLeft_zero] at h3
  unfold encodeLdrb
  simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]

theorem decode_ldrb (d b : Fin 31) (n : Fin 4096) :
    Arm64.decode (encodeLdrb d b n) =
      some (.ldr .W32 .B8 false (.gpr (BitVec.ofNat 5 d.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 n.val))) := by
  have hf := encodeLdrb_fixed d b n
  have hd : d.val < 2 ^ 5 := by omega
  have hb : b.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := by omega
  have ex_d : (encodeLdrb d b n).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeLdrb; simp only [extract_or]
    have h0 : (0x39400000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_b : (encodeLdrb d b n).extractLsb' 5 5 = BitVec.ofNat 5 b.val := by
    unfold encodeLdrb; simp only [extract_or]
    have h0 : (0x39400000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 b.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_n : (encodeLdrb d b n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeLdrb; simp only [extract_or]
    have h0 : (0x39400000#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 10 12 = 0#12 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_sz : (encodeLdrb d b n).extractLsb' 30 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeLdrb d b n).extractLsb' 22 2 = 1#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hshift : (BitVec.ofNat 12 n.val).zeroExtend 64 <<< 0 = BitVec.ofNat 64 n.val := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have : n.val < 4096 := n.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             ex_d, ex_b, ex_n, ex_sz, ex_opc, fromZRBits_fin31, fromSPBits_fin31,
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
  simp only [Arm64.mkLoadStoreInst, BitVec.toNat_ofNat]
  rw [hshift]
  rfl

theorem agree_ldrb (d b : Fin 31) (n : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (n.val : Int))
    (hfit : st.reg (armSlot b.val) + n.val < Ode.M64)
    (hread : gs.mem.canRead (gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 n.val) 1 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeLdrb d b n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectLdrb, bindLdrb d b numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hnlt : n.val < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  have hmodN : ((n.val : Int) % (Ode.M64 : Int)).toNat = n.val := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hnlt)]; rfl
  have hea_nat : (st.reg (armSlot b.val) + n.val) % Ode.M64 = st.reg (armSlot b.val) + n.val :=
    Nat.mod_eq_of_lt hfit
  have hea_bv : gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 n.val =
      BitVec.ofNat 64 (st.reg (armSlot b.val) + n.val) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.gpr b]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hfit]
  let a := st.reg (armSlot b.val) + n.val
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) (Ode.load st.mem a 1)
  let st' : Ode.State := Ode.noted (bindLdrb d b numStr) st0 (.set (.name "D") (.call "mem8" [.name "B", .name "N"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectLdrb, bindLdrb d b numStr, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.read a 1 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectLdrb, Ode.execStmt, Ode.isUnknown,
          Ode.value, Ode.values, Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf,
          bindLdrb, List.lookup, regIndex_armRegName, Ode.sumList,
          hnum, hmodN, hea_nat, hall, a, st', st1, st0]
  have hread' : gs.mem.canRead (BitVec.ofNat 64 a) 1 = true := by rwa [← hea_bv]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.ldr .W32 .B8 false (.gpr (BitVec.ofNat 5 d.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 n.val))) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) ((gs.mem.read8 (BitVec.ofNat 64 a)).zeroExtend 64)).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execLdr, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.MemWidth.bytes,
          Arm64.Memory.readSized, Arm64.State.writeReg, hea_bv, a, hread']
  refine ⟨.ldr .W32 .B8 false (.gpr (BitVec.ofNat 5 d.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 n.val)),
          st', decode_ldrb d b n, hexec, ?_, ?_⟩
  · rw [hgs]
    refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.readReg64, Arm64.State.writeReg64,
                 Arm64.RegFile.read, Arm64.RegFile.write, toNat_ofNat5_ne31, Bool.false_eq_true, ↓reduceIte,
                 Ode.setReg, Ode.noted]
      by_cases hkd : k = d
      · subst hkd
        simp only [↓reduceIte, BitVec.toNat_setWidth]
        have hm := hA.mem a hfit
        have hlt8 : (gs.mem.read8 (BitVec.ofNat 64 a)).toNat < 256 := (gs.mem.read8 _).isLt
        have hld : Ode.load st.mem a 1 = (st.mem a).val := by simp [Ode.load]
        rw [hld, ← hm]
        unfold Ode.M64
        rw [Nat.mod_eq_of_lt (by omega)]
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
    · intro addr haddr
      simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.mem addr haddr
    · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted,
                 BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
      have : 4 % 2 ^ 64 = 4 := by decide
      unfold Ode.M64 at hpc
      rw [this, Nat.mod_eq_of_lt hpc]
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.zf
    · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.cf
  · rw [hgs]; rfl

/-! ## Row 6: `cmp_rr` (`cmp S64, P64 | .cmp .S .P | zf = equal(S, P); cf = below(S, P)`) -/

/-- Exact 32-bit encoding from `arm64/arm64.tab`:
`1 1 1 01011 00 0 PPPPP 000000 SSSSS 11111` (`SUBS XZR, Xn, Xm`). -/
def encodeCmpRr (s p : Fin 31) : BitVec 32 :=
  0xeb00001f#32 ||| (BitVec.ofNat 32 p.val <<< 16) ||| (BitVec.ofNat 32 s.val <<< 5)

def effectCmpRr : List Ode.Stmt :=
  [.set (.name "zf") (.call "equal" [.name "S", .name "P"]),
   .set (.name "cf") (.call "below" [.name "S", .name "P"])]

def bindCmpRr (s p : Fin 31) : Ode.Bind :=
  [("P", armRegName p.val), ("S", armRegName s.val)]

theorem encodeCmpRr_fixed (s p : Fin 31) :
    encodeCmpRr s p &&& 0xffe0fc1f#32 = 0xeb00001f#32 &&& 0xffe0fc1f#32 := by
  have hs : s.val < 2 ^ 5 := by omega
  have hp : p.val < 2 ^ 5 := by omega
  have h1 : (BitVec.ofNat 32 p.val <<< 16) &&& 0xffe0fc1f#32 = 0#32 := field_and_eq_zero hp (by decide)
  have h2 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xffe0fc1f#32 = 0#32 := field_and_eq_zero hs (by decide)
  unfold encodeCmpRr
  simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]

theorem decode_cmp_rr (s p : Fin 31) :
    Arm64.decode (encodeCmpRr s p) =
      some (.addSubShift .W64 .SUBS .xzr (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0) := by
  have hf := encodeCmpRr_fixed s p
  have hs : s.val < 2 ^ 5 := by omega
  have hp : p.val < 2 ^ 5 := by omega
  have ex_d : (encodeCmpRr s p).extractLsb' 0 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_s : (encodeCmpRr s p).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeCmpRr; simp only [extract_or]
    have h0 : (0xeb00001f#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    rw [h0, h1, h2]; simp
  have ex_p : (encodeCmpRr s p).extractLsb' 16 5 = BitVec.ofNat 5 p.val := by
    unfold encodeCmpRr; simp only [extract_or]
    have h0 : (0xeb00001f#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 p.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hs (by omega)
    rw [h0, h1, h2]; simp
  have ex_imm6 : (encodeCmpRr s p).extractLsb' 10 6 = 0#6 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_sh : (encodeCmpRr s p).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have b31 : (encodeCmpRr s p).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have b30 : (encodeCmpRr s p).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have b29 : (encodeCmpRr s p).getLsbD 29 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
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
  simp [Arm64.RegWidth.ofBool, Arm64.AddSubOp.ofBits, Arm64.ShiftType.ofBits, Arm64.Reg.fromZRBits]

/-- Exact arithmetic identity for 64-bit `AddWithCarry64 x (~~~y) true`:
`z = decide (x.toNat = y.toNat)` and `c = !decide (x.toNat < y.toNat)`. -/
theorem addWithCarry64_sub_flags (x y : BitVec 64) :
    (Arm64.AddWithCarry64 x (~~~y) true).2.z = decide (x.toNat = y.toNat) ∧
    (Arm64.AddWithCarry64 x (~~~y) true).2.c = !decide (x.toNat < y.toNat) := by
  have hx := x.isLt
  have hy := y.isLt
  have hnot : (~~~y).toNat = 2 ^ 64 - 1 - y.toNat := BitVec.toNat_not
  let usum : BitVec 65 := 1#65 + ((~~~y).zeroExtend 65 + x.zeroExtend 65)
  have husum : usum.toNat = 2 ^ 64 + x.toNat - y.toNat := by
    simp only [usum, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hnot]
    have hpow : 2 ^ 65 = 2 * 2 ^ 64 := by decide
    have h1 : 1 % 2 ^ 65 = 1 := by decide
    rw [h1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨?_, ?_⟩
  · change (usum.truncate 64 == 0#64) = decide (x.toNat = y.toNat)
    have htr : (usum.truncate 64).toNat = usum.toNat % 2 ^ 64 := by
      simp [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
    by_cases hxy : x.toNat = y.toNat
    · have hz : (usum.truncate 64).toNat = 0 := by rw [htr, husum, hxy]; omega
      have hbv : usum.truncate 64 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hz)
      simp [hbv, hxy]
    · have hnz : (usum.truncate 64).toNat ≠ 0 := by rw [htr, husum]; omega
      have hne : usum.truncate 64 ≠ 0#64 := fun h => hnz (by rw [h]; rfl)
      simp [beq_false_of_ne hne, hxy]
  · change usum.msb = !decide (x.toNat < y.toNat)
    rw [BitVec.msb_eq_decide, husum]
    by_cases hlt : x.toNat < y.toNat <;> simp [hlt] <;> omega

theorem agree_cmp_rr (s p : Fin 31) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeCmpRr s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectCmpRr, bindCmpRr s p, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) := by
  have hs_mod : st.reg (armSlot s.val) % Ode.M64 = st.reg (armSlot s.val) := by
    rw [← hA.gpr s]; exact Nat.mod_eq_of_lt (gs.readReg64 _).isLt
  have hp_mod : st.reg (armSlot p.val) % Ode.M64 = st.reg (armSlot p.val) := by
    rw [← hA.gpr p]; exact Nat.mod_eq_of_lt (gs.readReg64 _).isLt
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let zVal : Bool := (if st.reg (armSlot s.val) == st.reg (armSlot p.val) then 1 else 0) != 0
  let cVal : Bool := (if st.reg (armSlot s.val) < st.reg (armSlot p.val) then 1 else 0) != 0
  let st1 : Ode.State := Ode.noted (bindCmpRr s p) st0 (.set (.name "zf") (.call "equal" [.name "S", .name "P"])) { st0 with zf := zVal }
  let st' : Ode.State := Ode.noted (bindCmpRr s p) st1 (.set (.name "cf") (.call "below" [.name "S", .name "P"])) { st1 with cf := cVal }
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectCmpRr, bindCmpRr s p, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectCmpRr, Ode.execStmt, Ode.isUnknown,
          Ode.value, Ode.values, Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf,
          bindCmpRr, List.lookup, regIndex_armRegName, Ode.prim, Ode.noted, hs_mod, hp_mod, zVal, cVal, st', st1, st0]
  let x := gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))
  let y := gs.readReg64 (.gpr (BitVec.ofNat 5 p.val))
  let ps := (Arm64.AddWithCarry64 x (~~~y) true).2
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.addSubShift .W64 .SUBS .xzr (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0) gs =
      ((gs.writeReg64 .xzr (Arm64.AddWithCarry64 x (~~~y) true).1).setPState ps).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execAddSubShift, Arm64.evalAddSub,
          Arm64.State.readReg, Arm64.State.writeReg, Arm64.shiftVal, Arm64.shift64, x, y, ps]
  have ⟨hz, hc⟩ := addWithCarry64_sub_flags x y
  refine ⟨.addSubShift .W64 .SUBS .xzr (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0,
          st', decode_cmp_rr s p, hexec, ?_⟩
  rw [hgs]
  refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setPState, Arm64.State.writeReg64,
           Arm64.State.readReg64, Ode.noted] using hA.gpr k
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setPState, Arm64.State.writeReg64,
           Ode.noted] using hA.sp
  · intro v j
    simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setPState, Arm64.State.writeReg64,
           Arm64.State.readVReg128, Ode.noted] using hA.vec v j
  · intro a ha
    simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setPState, Arm64.State.writeReg64,
           Ode.noted] using hA.mem a ha
  · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.setPState, Arm64.State.writeReg64,
               Ode.noted, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
    have : 4 % 2 ^ 64 = 4 := by decide
    unfold Ode.M64 at hpc
    rw [this, Nat.mod_eq_of_lt hpc]
  · change ps.z = zVal
    rw [show ps.z = decide (x.toNat = y.toNat) from hz, hA.gpr s, hA.gpr p]
    by_cases h : st.reg (armSlot s.val) = st.reg (armSlot p.val) <;> simp [zVal, h]
  · change ps.c = !cVal
    rw [show ps.c = !decide (x.toNat < y.toNat) from hc, hA.gpr s, hA.gpr p]
    by_cases h : st.reg (armSlot s.val) < st.reg (armSlot p.val) <;> simp [cVal, h]

/-! ## Rows 7 & 8: `b_hs` (`jump I if not cf`) and `b_lo` (`jump I if cf`) -/

/-- Exact 32-bit encoding of `b.cond`: `01010100 iiiiiiiiiiiiiiiiiii 0 cccc ; pc=I`. -/
def encodeBCond (cond4 : BitVec 4) (imm19 : BitVec 19) : BitVec 32 :=
  0x54000000#32 ||| (BitVec.ofNat 32 imm19.toNat <<< 5) ||| BitVec.ofNat 32 cond4.toNat

def encodeBHs (imm19 : BitVec 19) : BitVec 32 := encodeBCond 2#4 imm19
def encodeBLo (imm19 : BitVec 19) : BitVec 32 := encodeBCond 3#4 imm19
def encodeBHi (imm19 : BitVec 19) : BitVec 32 := encodeBCond 8#4 imm19
def encodeBLs (imm19 : BitVec 19) : BitVec 32 := encodeBCond 9#4 imm19

def effectBHs : List Ode.Stmt := [.jump (.name "I") (some ("cf", false))]
def effectBLo : List Ode.Stmt := [.jump (.name "I") (some ("cf", true))]
def effectBHi : List Ode.Stmt := [.jump (.name "I") (some ("hi", true))]
def effectBLs : List Ode.Stmt := [.jump (.name "I") (some ("hi", false))]

def bindJump (numStr : String) : Ode.Bind := [("I", numStr)]

theorem encodeBCond_fixed (cond4 : BitVec 4) (imm19 : BitVec 19) :
    encodeBCond cond4 imm19 &&& 0xff00001f#32 = (0x54000000#32 ||| BitVec.ofNat 32 cond4.toNat) &&& 0xff00001f#32 := by
  have hi : imm19.toNat < 2 ^ 19 := imm19.isLt
  have h1 : (BitVec.ofNat 32 imm19.toNat <<< 5) &&& 0xff00001f#32 = 0#32 := field_and_eq_zero hi (by decide)
  unfold encodeBCond
  simp only [BitVec.and_or_distrib_right, h1, BitVec.or_zero]

theorem decode_b_cond (cond4 : BitVec 4) (imm19 : BitVec 19) :
    Arm64.decode (encodeBCond cond4 imm19) =
      some (.bCond (Arm64.CondCode.ofBits cond4) ((imm19.signExtend 64) <<< 2)) := by
  have hf := encodeBCond_fixed cond4 imm19
  have hi : imm19.toNat < 2 ^ 19 := imm19.isLt
  have hc : cond4.toNat < 2 ^ 4 := cond4.isLt
  have hf' : encodeBCond cond4 imm19 &&& 0xff000010#32 = 0x54000000#32 &&& 0xff000010#32 := by
    have h1 : (BitVec.ofNat 32 imm19.toNat <<< 5) &&& 0xff000010#32 = 0#32 := field_and_eq_zero hi (by decide)
    have h2 : (BitVec.ofNat 32 cond4.toNat <<< 0) &&& 0xff000010#32 = 0#32 := field_and_eq_zero hc (by decide)
    simp only [BitVec.shiftLeft_zero] at h2
    unfold encodeBCond
    simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]
  have ex_imm : (encodeBCond cond4 imm19).extractLsb' 5 19 = imm19 := by
    unfold encodeBCond; simp only [extract_or]
    have h0 : (0x54000000#32).extractLsb' 5 19 = 0#19 := by decide
    have h1 : (BitVec.ofNat 32 imm19.toNat <<< 5).extractLsb' 5 19 = BitVec.ofNat 19 imm19.toNat := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 cond4.toNat <<< 0).extractLsb' 5 19 = 0#19 := extract_field_miss hc (by omega)
    simp only [BitVec.shiftLeft_zero] at h2
    rw [h0, h1, h2]
    simp
  have ex_cond : (encodeBCond cond4 imm19).extractLsb' 0 4 = cond4 := by
    unfold encodeBCond; simp only [extract_or]
    have h0 : (0x54000000#32).extractLsb' 0 4 = 0#4 := by decide
    have h1 : (BitVec.ofNat 32 imm19.toNat <<< 5).extractLsb' 0 4 = 0#4 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 cond4.toNat <<< 0).extractLsb' 0 4 = BitVec.ofNat 4 cond4.toNat := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2
    rw [h0, h1, h2]
    simp
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf' (c := 0xd503201f#32) (by decide),
             ex_imm, ex_cond,
             mask_ne_of_fixed hf' (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf' (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf' (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf' (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf' (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
             mask_ne_of_fixed hf' (m := 0x1f000000#32) (c := 0x10000000#32) (by decide),
             mask_ne_of_fixed hf' (m := 0x1f800000#32) (c := 0x11000000#32) (by decide),
             mask_ne_of_fixed hf' (m := 0x1f800000#32) (c := 0x12000000#32) (by decide),
             mask_ne_of_fixed hf' (m := 0x1f800000#32) (c := 0x12800000#32) (by decide),
             mask_ne_of_fixed hf' (m := 0x1f800000#32) (c := 0x13000000#32) (by decide),
             mask_ne_of_fixed hf' (m := 0x7f800000#32) (c := 0x13800000#32) (by decide),
             mask_ne_of_fixed hf' (m := 0x7c000000#32) (c := 0x14000000#32) (by decide),
             mask_ne_of_fixed hf' (m := 0x7e000000#32) (c := 0x34000000#32) (by decide),
             mask_ne_of_fixed hf' (m := 0x7e000000#32) (c := 0x36000000#32) (by decide),
             mask_of_fixed hf' (m := 0xff000010#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

/-- `b_hs` (`b.hs I | jump I if not cf`) agrees with Google's `B.CS` (`ConditionHolds .CS = pstate.c = !cf`)
on both the taken and fall-through paths. -/
theorem agree_b_hs (imm19 : BitVec 19) (target : Nat) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hnum : Ode.readInt numStr = some (target : Int))
    (htlt : target < Ode.M64)
    (htarget : prog.base + target = (gs.pc + ((imm19.signExtend 64) <<< 2)).toNat)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeBHs imm19) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectBHs, bindJump numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hmodT : ((target : Int) % (Ode.M64 : Int)).toNat = target := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr htlt)]; rfl
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let stBody : Ode.State := if st.cf == false then { st0 with rip := prog.base + target } else st0
  let st' : Ode.State := Ode.noted (bindJump numStr) st0 (.jump (.name "I") (some ("cf", false))) stBody
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectBHs, bindJump numStr, next⟩ u st = some (.next st') := by
    cases hcf : st.cf
    · simp [Ode.exec, Ode.execAll, effectBHs, Ode.execStmt, Ode.condFlag, Ode.value, Ode.isNumberLetter,
            bindJump, List.lookup, hnum, hmodT, st', stBody, st0, hcf]
    · simp [Ode.exec, Ode.execAll, effectBHs, Ode.execStmt, Ode.condFlag, st', stBody, st0, hcf]
  have hdec : Arm64.decode (encodeBHs imm19) = some (.bCond .CS ((imm19.signExtend 64) <<< 2)) := by
    simpa [encodeBHs, Arm64.CondCode.ofBits] using decode_b_cond 2#4 imm19
  refine ⟨.bCond .CS ((imm19.signExtend 64) <<< 2), st', hdec, hexec, ?_, ?_⟩
  · cases hcf : st.cf
    · have hc : gs.pstate.c = true := by rw [hA.cf, hcf]; rfl
      have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .CS ((imm19.signExtend 64) <<< 2)) gs =
          gs.setPC (gs.pc + ((imm19.signExtend 64) <<< 2)) := by
        simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc]
      rw [hgs]
      refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; simpa [st', stBody, st0, hcf, Arm64.State.setPC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
      · simpa [st', stBody, st0, hcf, Arm64.State.setPC, Ode.noted] using hA.sp
      · intro v j; simpa [st', stBody, st0, hcf, Arm64.State.setPC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
      · intro a ha; simpa [st', stBody, st0, hcf, Arm64.State.setPC, Ode.noted] using hA.mem a ha
      · simp [st', stBody, st0, hcf, Arm64.State.setPC, Ode.noted, htarget]
      · simpa [st', stBody, st0, hcf, Arm64.State.setPC, Ode.noted] using hA.zf
      · simpa [st', stBody, st0, hcf, Arm64.State.setPC, Ode.noted] using hA.cf
    · have hc : gs.pstate.c = false := by rw [hA.cf, hcf]; rfl
      have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .CS ((imm19.signExtend 64) <<< 2)) gs = gs.advancePC := by
        simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc]
      rw [hgs]
      refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
      · simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Ode.noted] using hA.sp
      · intro v j; simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
      · intro a ha; simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Ode.noted] using hA.mem a ha
      · simp only [st', stBody, st0, hcf, Arm64.State.advancePC, Ode.noted, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext, beq_iff_eq, Bool.true_eq_false, ↓reduceIte]
        have : 4 % 2 ^ 64 = 4 := by decide
        unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
      · simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Ode.noted] using hA.zf
      · simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Ode.noted] using hA.cf
  · cases hcf : st.cf
    · have hc : gs.pstate.c = true := by rw [hA.cf, hcf]; rfl
      simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc, Arm64.State.setPC]
    · have hc : gs.pstate.c = false := by rw [hA.cf, hcf]; rfl
      simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc, Arm64.State.advancePC]

/-- `b_lo` (`b.lo I | jump I if cf`) agrees with Google's `B.CC` (`ConditionHolds .CC = !pstate.c = cf`)
on both the taken and fall-through paths. -/
theorem agree_b_lo (imm19 : BitVec 19) (target : Nat) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hnum : Ode.readInt numStr = some (target : Int))
    (htlt : target < Ode.M64)
    (htarget : prog.base + target = (gs.pc + ((imm19.signExtend 64) <<< 2)).toNat)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeBLo imm19) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectBLo, bindJump numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hmodT : ((target : Int) % (Ode.M64 : Int)).toNat = target := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr htlt)]; rfl
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let stBody : Ode.State := if st.cf == true then { st0 with rip := prog.base + target } else st0
  let st' : Ode.State := Ode.noted (bindJump numStr) st0 (.jump (.name "I") (some ("cf", true))) stBody
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectBLo, bindJump numStr, next⟩ u st = some (.next st') := by
    cases hcf : st.cf
    · simp [Ode.exec, Ode.execAll, effectBLo, Ode.execStmt, Ode.condFlag, st', stBody, st0, hcf]
    · simp [Ode.exec, Ode.execAll, effectBLo, Ode.execStmt, Ode.condFlag, Ode.value, Ode.isNumberLetter,
            bindJump, List.lookup, hnum, hmodT, st', stBody, st0, hcf]
  have hdec : Arm64.decode (encodeBLo imm19) = some (.bCond .CC ((imm19.signExtend 64) <<< 2)) := by
    simpa [encodeBLo, Arm64.CondCode.ofBits] using decode_b_cond 3#4 imm19
  refine ⟨.bCond .CC ((imm19.signExtend 64) <<< 2), st', hdec, hexec, ?_, ?_⟩
  · cases hcf : st.cf
    · have hc : gs.pstate.c = true := by rw [hA.cf, hcf]; rfl
      have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .CC ((imm19.signExtend 64) <<< 2)) gs = gs.advancePC := by
        simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc]
      rw [hgs]
      refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
      · simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Ode.noted] using hA.sp
      · intro v j; simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
      · intro a ha; simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Ode.noted] using hA.mem a ha
      · simp only [st', stBody, st0, hcf, Arm64.State.advancePC, Ode.noted, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext, beq_iff_eq, Bool.false_eq_true, ↓reduceIte]
        have : 4 % 2 ^ 64 = 4 := by decide
        unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
      · simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Ode.noted] using hA.zf
      · simpa [st', stBody, st0, hcf, Arm64.State.advancePC, Ode.noted] using hA.cf
    · have hc : gs.pstate.c = false := by rw [hA.cf, hcf]; rfl
      have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .CC ((imm19.signExtend 64) <<< 2)) gs =
          gs.setPC (gs.pc + ((imm19.signExtend 64) <<< 2)) := by
        simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc]
      rw [hgs]
      refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; simpa [st', stBody, st0, hcf, Arm64.State.setPC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
      · simpa [st', stBody, st0, hcf, Arm64.State.setPC, Ode.noted] using hA.sp
      · intro v j; simpa [st', stBody, st0, hcf, Arm64.State.setPC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
      · intro a ha; simpa [st', stBody, st0, hcf, Arm64.State.setPC, Ode.noted] using hA.mem a ha
      · simp [st', stBody, st0, hcf, Arm64.State.setPC, Ode.noted, htarget]
      · simpa [st', stBody, st0, hcf, Arm64.State.setPC, Ode.noted] using hA.zf
      · simpa [st', stBody, st0, hcf, Arm64.State.setPC, Ode.noted] using hA.cf
  · cases hcf : st.cf
    · have hc : gs.pstate.c = true := by rw [hA.cf, hcf]; rfl
      simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc, Arm64.State.advancePC]
    · have hc : gs.pstate.c = false := by rw [hA.cf, hcf]; rfl
      simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc, Arm64.State.setPC]

/-- `b_hi` (`b.hi I | jump I if hi`) agrees with Google's `B.HI` (`ConditionHolds .HI = pstate.c && !pstate.z = !cf && !zf`)
on both the taken and fall-through paths. -/
theorem agree_b_hi (imm19 : BitVec 19) (target : Nat) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hnum : Ode.readInt numStr = some (target : Int))
    (htlt : target < Ode.M64)
    (htarget : prog.base + target = (gs.pc + ((imm19.signExtend 64) <<< 2)).toNat)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeBHi imm19) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectBHi, bindJump numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hmodT : ((target : Int) % (Ode.M64 : Int)).toNat = target := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr htlt)]; rfl
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let stBody : Ode.State := if (!st.cf && !st.zf) == true then { st0 with rip := prog.base + target } else st0
  let st' : Ode.State := Ode.noted (bindJump numStr) st0 (.jump (.name "I") (some ("hi", true))) stBody
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectBHi, bindJump numStr, next⟩ u st = some (.next st') := by
    cases hcf : st.cf <;> cases hzf : st.zf <;>
      simp [Ode.exec, Ode.execAll, effectBHi, Ode.execStmt, Ode.condFlag, Ode.value, Ode.isNumberLetter,
            bindJump, List.lookup, hnum, hmodT, st', stBody, st0, hcf, hzf]
  have hdec : Arm64.decode (encodeBHi imm19) = some (.bCond .HI ((imm19.signExtend 64) <<< 2)) := by
    simpa [encodeBHi, Arm64.CondCode.ofBits] using decode_b_cond 8#4 imm19
  refine ⟨.bCond .HI ((imm19.signExtend 64) <<< 2), st', hdec, hexec, ?_, ?_⟩
  · cases hcf : st.cf <;> cases hzf : st.zf
    · have hc : gs.pstate.c = true := by rw [hA.cf, hcf]; rfl
      have hz : gs.pstate.z = false := by rw [hA.zf, hzf]
      have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .HI ((imm19.signExtend 64) <<< 2)) gs =
          gs.setPC (gs.pc + ((imm19.signExtend 64) <<< 2)) := by
        simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc, hz]
      rw [hgs]
      refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
      · simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Ode.noted] using hA.sp
      · intro v j; simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
      · intro a ha; simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Ode.noted] using hA.mem a ha
      · simp [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Ode.noted, htarget]
      · simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Ode.noted] using hA.zf
      · simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Ode.noted] using hA.cf
    all_goals
      (have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .HI ((imm19.signExtend 64) <<< 2)) gs = gs.advancePC := by
         have hc := hA.cf; have hz := hA.zf; rw [hcf] at hc; rw [hzf] at hz
         simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc, hz]
       rw [hgs]
       refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       · intro k; simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
       · simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Ode.noted] using hA.sp
       · intro v j; simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
       · intro a ha; simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Ode.noted] using hA.mem a ha
       · simp only [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Ode.noted, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, beq_iff_eq, Bool.false_eq_true, ↓reduceIte]
         have : 4 % 2 ^ 64 = 4 := by decide
         unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
       · simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Ode.noted] using hA.zf
       · simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Ode.noted] using hA.cf)
  · cases hcf : st.cf <;> cases hzf : st.zf <;>
      (have hc := hA.cf; have hz := hA.zf; rw [hcf] at hc; rw [hzf] at hz
       simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc, hz, Arm64.State.setPC, Arm64.State.advancePC])

/-- `b_ls` (`b.ls I | jump I if not hi`) agrees with Google's `B.LS` (`ConditionHolds .LS = !(pstate.c && !pstate.z) = cf || zf`)
on both the taken and fall-through paths. -/
theorem agree_b_ls (imm19 : BitVec 19) (target : Nat) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hnum : Ode.readInt numStr = some (target : Int))
    (htlt : target < Ode.M64)
    (htarget : prog.base + target = (gs.pc + ((imm19.signExtend 64) <<< 2)).toNat)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeBLs imm19) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectBLs, bindJump numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hmodT : ((target : Int) % (Ode.M64 : Int)).toNat = target := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr htlt)]; rfl
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let stBody : Ode.State := if (!st.cf && !st.zf) == false then { st0 with rip := prog.base + target } else st0
  let st' : Ode.State := Ode.noted (bindJump numStr) st0 (.jump (.name "I") (some ("hi", false))) stBody
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectBLs, bindJump numStr, next⟩ u st = some (.next st') := by
    cases hcf : st.cf <;> cases hzf : st.zf <;>
      simp [Ode.exec, Ode.execAll, effectBLs, Ode.execStmt, Ode.condFlag, Ode.value, Ode.isNumberLetter,
            bindJump, List.lookup, hnum, hmodT, st', stBody, st0, hcf, hzf]
  have hdec : Arm64.decode (encodeBLs imm19) = some (.bCond .LS ((imm19.signExtend 64) <<< 2)) := by
    simpa [encodeBLs, Arm64.CondCode.ofBits] using decode_b_cond 9#4 imm19
  refine ⟨.bCond .LS ((imm19.signExtend 64) <<< 2), st', hdec, hexec, ?_, ?_⟩
  · cases hcf : st.cf <;> cases hzf : st.zf
    · have hc : gs.pstate.c = true := by rw [hA.cf, hcf]; rfl
      have hz : gs.pstate.z = false := by rw [hA.zf, hzf]
      have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .LS ((imm19.signExtend 64) <<< 2)) gs = gs.advancePC := by
        simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc, hz]
      rw [hgs]
      refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
      · simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Ode.noted] using hA.sp
      · intro v j; simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
      · intro a ha; simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Ode.noted] using hA.mem a ha
      · simp only [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Ode.noted, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext, Bool.not_false, Bool.and_true, beq_iff_eq, Bool.true_eq_false, ↓reduceIte]
        have : 4 % 2 ^ 64 = 4 := by decide
        unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
      · simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Ode.noted] using hA.zf
      · simpa [st', stBody, st0, hcf, hzf, Arm64.State.advancePC, Ode.noted] using hA.cf
    all_goals
      (have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .LS ((imm19.signExtend 64) <<< 2)) gs =
           gs.setPC (gs.pc + ((imm19.signExtend 64) <<< 2)) := by
         have hc := hA.cf; have hz := hA.zf; rw [hcf] at hc; rw [hzf] at hz
         simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc, hz]
       rw [hgs]
       refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       · intro k; simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
       · simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Ode.noted] using hA.sp
       · intro v j; simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
       · intro a ha; simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Ode.noted] using hA.mem a ha
       · simp [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Ode.noted, htarget]
       · simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Ode.noted] using hA.zf
       · simpa [st', stBody, st0, hcf, hzf, Arm64.State.setPC, Ode.noted] using hA.cf)
  · cases hcf : st.cf <;> cases hzf : st.zf <;>
      (have hc := hA.cf; have hz := hA.zf; rw [hcf] at hc; rw [hzf] at hz
       simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hc, hz, Arm64.State.setPC, Arm64.State.advancePC])

/-! ## Shared helpers for rows 9–20 -/

/-- Updating a single general register `d` in both models preserves `AgreeState` and `pstate`. -/
theorem agreeState_writeGpr {prog : Ode.Program} {st : Ode.State} {gs : Arm64.State} {next : Nat}
    (hA : AgreeState st gs) (d : Fin 31) (v : BitVec 64) (val : Nat) (hv : v.toNat = val)
    (bind : Ode.Bind) (stmt : Ode.Stmt)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
    let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) val
    let st' : Ode.State := Ode.noted bind st0 stmt st1
    AgreeState st' ((gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) v).advancePC) := by
  intro st0 st1 st'
  refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.readReg64, Arm64.State.writeReg64,
               Arm64.RegFile.read, Arm64.RegFile.write, toNat_ofNat5_ne31, Bool.false_eq_true, ↓reduceIte,
               Ode.setReg, Ode.noted]
    by_cases hkd : k = d
    · subst hkd
      simp only [↓reduceIte, hv]
      exact (Nat.mod_eq_of_lt (by rw [← hv]; exact v.isLt)).symm
    · have hne5 : BitVec.ofNat 5 k.val ≠ BitVec.ofNat 5 d.val := fun e => hkd (ofNat5_inj e)
      have hnes : armSlot k.val ≠ armSlot d.val := fun e => hkd (armSlot_inj k d e)
      simp only [hne5, hnes, ↓reduceIte]
      have hk := hA.gpr k
      simpa [Arm64.State.readReg64, Arm64.RegFile.read, toNat_ofNat5_ne31] using hk
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted,
           (armSlot_ne_rsp d).symm] using hA.sp
  · intro vec j
    simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Arm64.State.readVReg128,
           Ode.setReg, Ode.noted] using hA.vec vec j
  · intro a ha
    simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.mem a ha
  · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted,
               BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
    have : 4 % 2 ^ 64 = 4 := by decide
    unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.zf
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.cf

theorem addWithCarry64_add_val (x y : BitVec 64) :
    (Arm64.AddWithCarry64 x y false).1.toNat = (x.toNat + y.toNat) % Ode.M64 := by
  have hx := x.isLt; have hy := y.isLt
  simp only [Arm64.AddWithCarry64, Bool.false_eq_true, ↓reduceIte,
             BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  unfold Ode.M64
  rw [Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 65),
      Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 65),
      Nat.mod_eq_of_lt (by omega : y.toNat + x.toNat < 2 ^ 65),
      show (0 : Nat) % 2 ^ 65 = 0 from rfl,
      Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : y.toNat + x.toNat < 2 ^ 65),
      Nat.add_comm]

theorem addWithCarry64_sub_val (x y : BitVec 64) :
    (Arm64.AddWithCarry64 x (~~~y) true).1.toNat = (x.toNat + (Ode.M64 - y.toNat % Ode.M64)) % Ode.M64 := by
  have hx := x.isLt; have hy := y.isLt
  have hnot : (~~~y).toNat = 2 ^ 64 - 1 - y.toNat := by rw [BitVec.toNat_not]
  simp only [Arm64.AddWithCarry64, ↓reduceIte,
             BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, hnot]
  unfold Ode.M64
  rw [Nat.mod_eq_of_lt hy,
      Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 1 - y.toNat < 2 ^ 65),
      Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 65),
      Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 1 - y.toNat + x.toNat < 2 ^ 65),
      show (1 : Nat) % 2 ^ 65 = 1 from by decide,
      Nat.mod_eq_of_lt (by omega : 1 + (2 ^ 64 - 1 - y.toNat + x.toNat) < 2 ^ 65)]
  congr 1; omega

/-! ## Row 9: `nop` (`nop | .nop | nothing`) -/

def encodeNop : BitVec 32 := 0xd503201f#32
def effectNop : List Ode.Stmt := [.nothing]

theorem decode_nop : Arm64.decode encodeNop = some .nop := by decide

theorem agree_nop (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode encodeNop = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectNop, [], next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st' : Ode.State := Ode.noted [] st0 .nothing st0
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectNop, [], next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectNop, Ode.execStmt, st', st0]
  refine ⟨.nop, st', decode_nop, hexec, ?_, rfl⟩
  refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.advancePC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
  · simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.advancePC, Ode.noted] using hA.sp
  · intro v j; simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.advancePC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
  · intro a ha; simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.advancePC, Ode.noted] using hA.mem a ha
  · simp only [st', st0, Arm64.execInstWithSvc, Arm64.State.advancePC, Ode.noted, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
    have : 4 % 2 ^ 64 = 4 := by decide
    unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
  · simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.advancePC, Ode.noted] using hA.zf
  · simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.advancePC, Ode.noted] using hA.cf

/-! ## Rows 10 & 11: `mov_ri` (`mov D64, I`) and `mov32_ri` (`mov D32, I`) -/

def encodeMovRi (d : Fin 31) (imm : Fin 65536) : BitVec 32 :=
  0xd2800000#32 ||| (BitVec.ofNat 32 imm.val <<< 5) ||| BitVec.ofNat 32 d.val

def encodeMov32Ri (d : Fin 31) (imm : Fin 65536) : BitVec 32 :=
  0x52800000#32 ||| (BitVec.ofNat 32 imm.val <<< 5) ||| BitVec.ofNat 32 d.val

def effectMovRi : List Ode.Stmt := [.set (.name "D") (.name "I")]
def bindMovRi (d : Fin 31) (numStr : String) : Ode.Bind := [("D", armRegName d.val), ("I", numStr)]

theorem encodeMovRi_fixed (d : Fin 31) (imm : Fin 65536) :
    encodeMovRi d imm &&& 0xffe00000#32 = 0xd2800000#32 &&& 0xffe00000#32 := by
  have hd : d.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 16 := imm.isLt
  have h1 : (BitVec.ofNat 32 imm.val <<< 5) &&& 0xffe00000#32 = 0#32 := field_and_eq_zero hi (by decide)
  have h2 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffe00000#32 = 0#32 := field_and_eq_zero hd (by decide)
  simp only [BitVec.shiftLeft_zero] at h2
  unfold encodeMovRi; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]

theorem decode_mov_ri (d : Fin 31) (imm : Fin 65536) :
    Arm64.decode (encodeMovRi d imm) = some (.moveWide .W64 .MOVZ (.gpr (BitVec.ofNat 5 d.val)) (BitVec.ofNat 16 imm.val) 0) := by
  have hf := encodeMovRi_fixed d imm
  have hd : d.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 16 := imm.isLt
  have ex_d : (encodeMovRi d imm).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeMovRi; simp only [extract_or]
    have h0 : (0xd2800000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_i : (encodeMovRi d imm).extractLsb' 5 16 = BitVec.ofNat 16 imm.val := by
    unfold encodeMovRi; simp only [extract_or]
    have h0 : (0xd2800000#32).extractLsb' 5 16 = 0#16 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 5).extractLsb' 5 16 = BitVec.ofNat 16 imm.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 16 = 0#16 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have hsf : (encodeMovRi d imm).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hopc : (encodeMovRi d imm).extractLsb' 29 2 = 2#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hhw : (encodeMovRi d imm).extractLsb' 21 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide), hsf, hopc, hhw, ex_d, ex_i, fromZRBits_fin31,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x10000000#32) (by decide),
             mask_of_fixed hf (m := 0x1f800000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_mov_ri (d : Fin 31) (imm : Fin 65536) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (imm.val : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeMovRi d imm) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectMovRi, bindMovRi d numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hilt : imm.val < Ode.M64 := by unfold Ode.M64; have := imm.isLt; omega
  have hmod : ((imm.val : Int) % (Ode.M64 : Int)).toNat = imm.val := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hilt)]; rfl
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) imm.val
  let st' : Ode.State := Ode.noted (bindMovRi d numStr) st0 (.set (.name "D") (.name "I")) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectMovRi, bindMovRi d numStr, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectMovRi, Ode.execStmt, Ode.isUnknown, Ode.value,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindMovRi, List.lookup,
          regIndex_armRegName, hnum, hmod, st', st1, st0]
  have hv : ((BitVec.ofNat 16 imm.val).zeroExtend 64 <<< 0).toNat = imm.val := by
    simp only [BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := imm.isLt; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.moveWide .W64 .MOVZ (.gpr (BitVec.ofNat 5 d.val)) (BitVec.ofNat 16 imm.val) 0) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) ((BitVec.ofNat 16 imm.val).zeroExtend 64 <<< 0)).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execMoveWide, Arm64.State.writeReg]
  refine ⟨_, st', decode_mov_ri d imm, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]; exact agreeState_writeGpr hA d _ imm.val hv _ _ hnext hpc

theorem encodeMov32Ri_fixed (d : Fin 31) (imm : Fin 65536) :
    encodeMov32Ri d imm &&& 0xffe00000#32 = 0x52800000#32 &&& 0xffe00000#32 := by
  have hd : d.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 16 := imm.isLt
  have h1 : (BitVec.ofNat 32 imm.val <<< 5) &&& 0xffe00000#32 = 0#32 := field_and_eq_zero hi (by decide)
  have h2 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffe00000#32 = 0#32 := field_and_eq_zero hd (by decide)
  simp only [BitVec.shiftLeft_zero] at h2
  unfold encodeMov32Ri; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]

theorem decode_mov32_ri (d : Fin 31) (imm : Fin 65536) :
    Arm64.decode (encodeMov32Ri d imm) = some (.moveWide .W32 .MOVZ (.gpr (BitVec.ofNat 5 d.val)) (BitVec.ofNat 16 imm.val) 0) := by
  have hf := encodeMov32Ri_fixed d imm
  have hd : d.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 16 := imm.isLt
  have ex_d : (encodeMov32Ri d imm).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeMov32Ri; simp only [extract_or]
    have h0 : (0x52800000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_i : (encodeMov32Ri d imm).extractLsb' 5 16 = BitVec.ofNat 16 imm.val := by
    unfold encodeMov32Ri; simp only [extract_or]
    have h0 : (0x52800000#32).extractLsb' 5 16 = 0#16 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 5).extractLsb' 5 16 = BitVec.ofNat 16 imm.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 16 = 0#16 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have hsf : (encodeMov32Ri d imm).getLsbD 31 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hopc : (encodeMov32Ri d imm).extractLsb' 29 2 = 2#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hhw : (encodeMov32Ri d imm).extractLsb' 21 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide), hsf, hopc, hhw, ex_d, ex_i, fromZRBits_fin31,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x10000000#32) (by decide),
             mask_of_fixed hf (m := 0x1f800000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_mov32_ri (d : Fin 31) (imm : Fin 65536) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (imm.val : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeMov32Ri d imm) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectMovRi, bindMovRi d numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hilt : imm.val < Ode.M64 := by unfold Ode.M64; have := imm.isLt; omega
  have hmod : ((imm.val : Int) % (Ode.M64 : Int)).toNat = imm.val := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hilt)]; rfl
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) imm.val
  let st' : Ode.State := Ode.noted (bindMovRi d numStr) st0 (.set (.name "D") (.name "I")) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectMovRi, bindMovRi d numStr, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectMovRi, Ode.execStmt, Ode.isUnknown, Ode.value,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindMovRi, List.lookup,
          regIndex_armRegName, hnum, hmod, st', st1, st0]
  have hv : ((((BitVec.ofNat 16 imm.val).zeroExtend 64 <<< 0).truncate 32).zeroExtend 64).toNat = imm.val := by
    simp only [BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := imm.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.moveWide .W32 .MOVZ (.gpr (BitVec.ofNat 5 d.val)) (BitVec.ofNat 16 imm.val) 0) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) ((((BitVec.ofNat 16 imm.val).zeroExtend 64 <<< 0).truncate 32).zeroExtend 64)).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execMoveWide, Arm64.State.writeReg]
  refine ⟨_, st', decode_mov32_ri d imm, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]; exact agreeState_writeGpr hA d _ imm.val hv _ _ hnext hpc

/-! ## Row 12: `mov_rr` (`mov D64, S64 | .mov .D .S | D = S`) -/

def encodeMovRr (d s : Fin 31) : BitVec 32 :=
  0xaa0003e0#32 ||| (BitVec.ofNat 32 s.val <<< 16) ||| BitVec.ofNat 32 d.val

def effectMovRr : List Ode.Stmt := [.set (.name "D") (.name "S")]
def bindMovRr (d s : Fin 31) : Ode.Bind := [("D", armRegName d.val), ("S", armRegName s.val)]

theorem encodeMovRr_fixed (d s : Fin 31) :
    encodeMovRr d s &&& 0xffe0ffe0#32 = 0xaa0003e0#32 &&& 0xffe0ffe0#32 := by
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have h1 : (BitVec.ofNat 32 s.val <<< 16) &&& 0xffe0ffe0#32 = 0#32 := field_and_eq_zero hs (by decide)
  have h2 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffe0ffe0#32 = 0#32 := field_and_eq_zero hd (by decide)
  simp only [BitVec.shiftLeft_zero] at h2
  unfold encodeMovRr; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]

theorem decode_mov_rr (d s : Fin 31) :
    Arm64.decode (encodeMovRr d s) =
      some (.logicalShift .W64 .ORR (.gpr (BitVec.ofNat 5 d.val)) .xzr (.gpr (BitVec.ofNat 5 s.val)) .LSL 0) := by
  have hf := encodeMovRr_fixed d s
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have ex_d : (encodeMovRr d s).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeMovRr; simp only [extract_or]
    have h0 : (0xaa0003e0#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 s.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hs (by omega)
    have h2 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_s : (encodeMovRr d s).extractLsb' 16 5 = BitVec.ofNat 5 s.val := by
    unfold encodeMovRr; simp only [extract_or]
    have h0 : (0xaa0003e0#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 s.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have hsf : (encodeMovRr d s).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hopc : (encodeMovRr d s).extractLsb' 29 2 = 1#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hsh : (encodeMovRr d s).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hnbit : (encodeMovRr d s).getLsbD 21 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have himm6 : (encodeMovRr d s).extractLsb' 10 6 = 0#6 := by rw [extract_of_fixed hf (by decide)]; decide
  have hrn : (encodeMovRr d s).extractLsb' 5 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             hsf, hopc, hsh, hnbit, himm6, hrn, ex_d, ex_s, fromZRBits_fin31,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
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
             mask_of_fixed hf (m := 0x1f000000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_mov_rr (d s : Fin 31)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeMovRr d s) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectMovRr, bindMovRr d s, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) (st.reg (armSlot s.val))
  let st' : Ode.State := Ode.noted (bindMovRr d s) st0 (.set (.name "D") (.name "S")) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectMovRr, bindMovRr d s, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectMovRr, Ode.execStmt, Ode.isUnknown, Ode.value,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindMovRr, List.lookup,
          regIndex_armRegName, st', st1, st0]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.logicalShift .W64 .ORR (.gpr (BitVec.ofNat 5 d.val)) .xzr (.gpr (BitVec.ofNat 5 s.val)) .LSL 0) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)))).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execLogicalShift, Arm64.evalLogical, Arm64.shiftVal, Arm64.shift64,
          Arm64.State.readReg, Arm64.State.readReg64, Arm64.State.writeReg]
  refine ⟨_, st', decode_mov_rr d s, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]; exact agreeState_writeGpr hA d _ _ (hA.gpr s) _ _ hnext hpc

/-! ## Rows 13 & 14: `add_rri` (`add D64, S64, I`) and `sub_rri` (`sub D64, S64, I`) -/

def encodeAddRri (d s : Fin 31) (imm : Fin 4096) : BitVec 32 :=
  0x91000000#32 ||| (BitVec.ofNat 32 imm.val <<< 10) ||| (BitVec.ofNat 32 s.val <<< 5) ||| BitVec.ofNat 32 d.val

def encodeSubRri (d s : Fin 31) (imm : Fin 4096) : BitVec 32 :=
  0xd1000000#32 ||| (BitVec.ofNat 32 imm.val <<< 10) ||| (BitVec.ofNat 32 s.val <<< 5) ||| BitVec.ofNat 32 d.val

def effectAddRri : List Ode.Stmt := [.set (.name "D") (.call "add64" [.name "S", .name "I"])]
def effectSubRri : List Ode.Stmt := [.set (.name "D") (.call "sub64" [.name "S", .name "I"])]
def bindRri (d s : Fin 31) (numStr : String) : Ode.Bind :=
  [("D", armRegName d.val), ("I", numStr), ("S", armRegName s.val)]

theorem encodeAddRri_fixed (d s : Fin 31) (imm : Fin 4096) :
    encodeAddRri d s imm &&& 0xffc00000#32 = 0x91000000#32 &&& 0xffc00000#32 := by
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 12 := imm.isLt
  have h1 : (BitVec.ofNat 32 imm.val <<< 10) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hi (by decide)
  have h2 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hs (by decide)
  have h3 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hd (by decide)
  simp only [BitVec.shiftLeft_zero] at h3
  unfold encodeAddRri; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]

theorem decode_add_rri (d s : Fin 31) (imm : Fin 4096) :
    Arm64.decode (encodeAddRri d s imm) =
      some (.addSubImm .W64 .ADD (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (BitVec.ofNat 12 imm.val) false) := by
  have hf := encodeAddRri_fixed d s imm
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 12 := imm.isLt
  have ex_d : (encodeAddRri d s imm).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeAddRri; simp only [extract_or]
    have h0 : (0x91000000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_s : (encodeAddRri d s imm).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeAddRri; simp only [extract_or]
    have h0 : (0x91000000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_i : (encodeAddRri d s imm).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := by
    unfold encodeAddRri; simp only [extract_or]
    have h0 : (0x91000000#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 10 12 = 0#12 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have hsf : (encodeAddRri d s imm).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h30 : (encodeAddRri d s imm).getLsbD 30 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h29 : (encodeAddRri d s imm).getLsbD 29 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h22 : (encodeAddRri d s imm).getLsbD 22 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             hsf, h30, h29, h22, ex_d, ex_s, ex_i, fromSPBits_fin31,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x10000000#32) (by decide),
             mask_of_fixed hf (m := 0x1f800000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_add_rri (d s : Fin 31) (imm : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (imm.val : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeAddRri d s imm) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectAddRri, bindRri d s numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hilt : imm.val < Ode.M64 := by unfold Ode.M64; have := imm.isLt; omega
  have hmod : ((imm.val : Int) % (Ode.M64 : Int)).toNat = imm.val := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hilt)]; rfl
  let val := (st.reg (armSlot s.val) + imm.val) % Ode.M64
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) val
  let st' : Ode.State := Ode.noted (bindRri d s numStr) st0 (.set (.name "D") (.call "add64" [.name "S", .name "I"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectAddRri, bindRri d s numStr, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectAddRri, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize, Ode.prim,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindRri, List.lookup,
          regIndex_armRegName, hnum, hmod, val, st', st1, st0]
  have himm : ((BitVec.ofNat 12 imm.val).zeroExtend 64).toNat = imm.val := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := imm.isLt; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hv : (Arm64.AddWithCarry64 (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))) ((BitVec.ofNat 12 imm.val).zeroExtend 64) false).1.toNat = val := by
    rw [addWithCarry64_add_val, hA.gpr s, himm]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.addSubImm .W64 .ADD (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (BitVec.ofNat 12 imm.val) false) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val))
        (Arm64.AddWithCarry64 (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))) ((BitVec.ofNat 12 imm.val).zeroExtend 64) false).1).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.writeReg]
  refine ⟨_, st', decode_add_rri d s imm, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]; exact agreeState_writeGpr hA d _ val hv _ _ hnext hpc

theorem encodeSubRri_fixed (d s : Fin 31) (imm : Fin 4096) :
    encodeSubRri d s imm &&& 0xffc00000#32 = 0xd1000000#32 &&& 0xffc00000#32 := by
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 12 := imm.isLt
  have h1 : (BitVec.ofNat 32 imm.val <<< 10) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hi (by decide)
  have h2 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hs (by decide)
  have h3 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hd (by decide)
  simp only [BitVec.shiftLeft_zero] at h3
  unfold encodeSubRri; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]

theorem decode_sub_rri (d s : Fin 31) (imm : Fin 4096) :
    Arm64.decode (encodeSubRri d s imm) =
      some (.addSubImm .W64 .SUB (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (BitVec.ofNat 12 imm.val) false) := by
  have hf := encodeSubRri_fixed d s imm
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 12 := imm.isLt
  have ex_d : (encodeSubRri d s imm).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeSubRri; simp only [extract_or]
    have h0 : (0xd1000000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_s : (encodeSubRri d s imm).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeSubRri; simp only [extract_or]
    have h0 : (0xd1000000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_i : (encodeSubRri d s imm).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := by
    unfold encodeSubRri; simp only [extract_or]
    have h0 : (0xd1000000#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 10 12 = 0#12 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have hsf : (encodeSubRri d s imm).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h30 : (encodeSubRri d s imm).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h29 : (encodeSubRri d s imm).getLsbD 29 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h22 : (encodeSubRri d s imm).getLsbD 22 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             hsf, h30, h29, h22, ex_d, ex_s, ex_i, fromSPBits_fin31,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x10000000#32) (by decide),
             mask_of_fixed hf (m := 0x1f800000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_sub_rri (d s : Fin 31) (imm : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (imm.val : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeSubRri d s imm) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectSubRri, bindRri d s numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hilt : imm.val < Ode.M64 := by unfold Ode.M64; have := imm.isLt; omega
  have hmod : ((imm.val : Int) % (Ode.M64 : Int)).toNat = imm.val := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hilt)]; rfl
  let val := (st.reg (armSlot s.val) + (Ode.M64 - imm.val % Ode.M64)) % Ode.M64
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) val
  let st' : Ode.State := Ode.noted (bindRri d s numStr) st0 (.set (.name "D") (.call "sub64" [.name "S", .name "I"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectSubRri, bindRri d s numStr, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectSubRri, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize, Ode.prim,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindRri, List.lookup,
          regIndex_armRegName, hnum, hmod, val, st', st1, st0]
  have himm : ((BitVec.ofNat 12 imm.val).zeroExtend 64).toNat = imm.val := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := imm.isLt; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hv : (Arm64.AddWithCarry64 (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))) (~~~((BitVec.ofNat 12 imm.val).zeroExtend 64)) true).1.toNat = val := by
    rw [addWithCarry64_sub_val, hA.gpr s, himm]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.addSubImm .W64 .SUB (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (BitVec.ofNat 12 imm.val) false) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val))
        (Arm64.AddWithCarry64 (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))) (~~~((BitVec.ofNat 12 imm.val).zeroExtend 64)) true).1).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.writeReg]
  refine ⟨_, st', decode_sub_rri d s imm, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]; exact agreeState_writeGpr hA d _ val hv _ _ hnext hpc

/-! ## Row 15: `sub_rrr` (`sub D64, S64, P64 | .sub .D .S .P | D = sub64(S, P)`) -/

def encodeSubRrr (d s p : Fin 31) : BitVec 32 :=
  0xcb000000#32 ||| (BitVec.ofNat 32 p.val <<< 16) ||| (BitVec.ofNat 32 s.val <<< 5) ||| BitVec.ofNat 32 d.val

def effectSubRrr : List Ode.Stmt := [.set (.name "D") (.call "sub64" [.name "S", .name "P"])]

theorem encodeSubRrr_fixed (d s p : Fin 31) :
    encodeSubRrr d s p &&& 0xffe0fc00#32 = 0xcb000000#32 &&& 0xffe0fc00#32 := by
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have hp : p.val < 2 ^ 5 := by omega
  have h1 : (BitVec.ofNat 32 p.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hp (by decide)
  have h2 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hs (by decide)
  have h3 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hd (by decide)
  simp only [BitVec.shiftLeft_zero] at h3
  unfold encodeSubRrr; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]

theorem decode_sub_rrr (d s p : Fin 31) :
    Arm64.decode (encodeSubRrr d s p) =
      some (.addSubShift .W64 .SUB (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0) := by
  have hf := encodeSubRrr_fixed d s p
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have hp : p.val < 2 ^ 5 := by omega
  have ex_d : (encodeSubRrr d s p).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeSubRrr; simp only [extract_or]
    have h0 : (0xcb000000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_s : (encodeSubRrr d s p).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeSubRrr; simp only [extract_or]
    have h0 : (0xcb000000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_p : (encodeSubRrr d s p).extractLsb' 16 5 = BitVec.ofNat 5 p.val := by
    unfold encodeSubRrr; simp only [extract_or]
    have h0 : (0xcb000000#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 p.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have hsf : (encodeSubRrr d s p).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h30 : (encodeSubRrr d s p).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h29 : (encodeSubRrr d s p).getLsbD 29 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hsh : (encodeSubRrr d s p).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have himm : (encodeSubRrr d s p).extractLsb' 10 6 = 0#6 := by rw [extract_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             hsf, h30, h29, hsh, himm, ex_d, ex_s, ex_p, fromZRBits_fin31,
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
             mask_of_fixed hf (m := 0x1f200000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_sub_rrr (d s p : Fin 31)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeSubRrr d s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectSubRrr, bindAddRrr d s p, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let val := (st.reg (armSlot s.val) + (Ode.M64 - st.reg (armSlot p.val) % Ode.M64)) % Ode.M64
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) val
  let st' : Ode.State := Ode.noted (bindAddRrr d s p) st0 (.set (.name "D") (.call "sub64" [.name "S", .name "P"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectSubRrr, bindAddRrr d s p, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectSubRrr, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize, Ode.prim,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindAddRrr, List.lookup,
          regIndex_armRegName, val, st', st1, st0]
  have hv : (Arm64.AddWithCarry64 (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))) (~~~(gs.readReg64 (.gpr (BitVec.ofNat 5 p.val)))) true).1.toNat = val := by
    rw [addWithCarry64_sub_val, hA.gpr s, hA.gpr p]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.addSubShift .W64 .SUB (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val))
        (Arm64.AddWithCarry64 (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))) (~~~(gs.readReg64 (.gpr (BitVec.ofNat 5 p.val)))) true).1).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execAddSubShift, Arm64.evalAddSub, Arm64.shiftVal, Arm64.shift64,
          Arm64.State.readReg, Arm64.State.writeReg]
  refine ⟨_, st', decode_sub_rrr d s p, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]; exact agreeState_writeGpr hA d _ val hv _ _ hnext hpc

/-! ## Row 16: `cmp_ri` (`cmp S64, I | .cmpi .S I | zf = equal(S, I); cf = below(S, I)`) -/

def encodeCmpRi (s : Fin 31) (imm : Fin 4096) : BitVec 32 :=
  0xf100001f#32 ||| (BitVec.ofNat 32 imm.val <<< 10) ||| (BitVec.ofNat 32 s.val <<< 5)

def effectCmpRi : List Ode.Stmt :=
  [.set (.name "zf") (.call "equal" [.name "S", .name "I"]),
   .set (.name "cf") (.call "below" [.name "S", .name "I"])]

def bindCmpRi (s : Fin 31) (numStr : String) : Ode.Bind :=
  [("I", numStr), ("S", armRegName s.val)]

theorem encodeCmpRi_fixed (s : Fin 31) (imm : Fin 4096) :
    encodeCmpRi s imm &&& 0xffc0001f#32 = 0xf100001f#32 &&& 0xffc0001f#32 := by
  have hs : s.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 12 := imm.isLt
  have h1 : (BitVec.ofNat 32 imm.val <<< 10) &&& 0xffc0001f#32 = 0#32 := field_and_eq_zero hi (by decide)
  have h2 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xffc0001f#32 = 0#32 := field_and_eq_zero hs (by decide)
  unfold encodeCmpRi; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]

theorem decode_cmp_ri (s : Fin 31) (imm : Fin 4096) :
    Arm64.decode (encodeCmpRi s imm) =
      some (.addSubImm .W64 .SUBS .xzr (.gpr (BitVec.ofNat 5 s.val)) (BitVec.ofNat 12 imm.val) false) := by
  have hf := encodeCmpRi_fixed s imm
  have hs : s.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 12 := imm.isLt
  have ex_s : (encodeCmpRi s imm).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeCmpRi; simp only [extract_or]
    have h0 : (0xf100001f#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    rw [h0, h1, h2]; simp
  have ex_i : (encodeCmpRi s imm).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := by
    unfold encodeCmpRi; simp only [extract_or]
    have h0 : (0xf100001f#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 10 12 = 0#12 := extract_field_miss hs (by omega)
    rw [h0, h1, h2]; simp
  have hsf : (encodeCmpRi s imm).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h30 : (encodeCmpRi s imm).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h29 : (encodeCmpRi s imm).getLsbD 29 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h22 : (encodeCmpRi s imm).getLsbD 22 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hrd : (encodeCmpRi s imm).extractLsb' 0 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             hsf, h30, h29, h22, hrd, ex_s, ex_i, fromSPBits_fin31,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x10000000#32) (by decide),
             mask_of_fixed hf (m := 0x1f800000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_cmp_ri (s : Fin 31) (imm : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (imm.val : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeCmpRi s imm) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectCmpRi, bindCmpRi s numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) := by
  have hilt : imm.val < Ode.M64 := by unfold Ode.M64; have := imm.isLt; omega
  have hmod : ((imm.val : Int) % (Ode.M64 : Int)).toNat = imm.val := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hilt)]; rfl
  have hsLt : st.reg (armSlot s.val) < Ode.M64 := by
    rw [← hA.gpr s]; exact (gs.readReg64 _).isLt
  have hsMod : st.reg (armSlot s.val) % Ode.M64 = st.reg (armSlot s.val) := Nat.mod_eq_of_lt hsLt
  have hiMod : imm.val % Ode.M64 = imm.val := Nat.mod_eq_of_lt hilt
  let zVal : Bool := (if st.reg (armSlot s.val) = imm.val then 1 else 0) != 0
  let cVal : Bool := (if st.reg (armSlot s.val) < imm.val then 1 else 0) != 0
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.noted (bindCmpRi s numStr) st0 (.set (.name "zf") (.call "equal" [.name "S", .name "I"])) { st0 with zf := zVal }
  let st' : Ode.State := Ode.noted (bindCmpRi s numStr) st1 (.set (.name "cf") (.call "below" [.name "S", .name "I"])) { st1 with cf := cVal }
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectCmpRi, bindCmpRi s numStr, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectCmpRi, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize, Ode.prim,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindCmpRi, List.lookup,
          regIndex_armRegName, hnum, hmod, hsMod, hiMod, zVal, cVal, st', st1, st0, Ode.noted]
  let x := gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))
  let y := (BitVec.ofNat 12 imm.val).zeroExtend 64
  have hy : y.toNat = imm.val := by
    simp only [y, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := imm.isLt; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  let ps := (Arm64.AddWithCarry64 x (~~~y) true).2
  have ⟨hz, hc⟩ := addWithCarry64_sub_flags x y
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.addSubImm .W64 .SUBS .xzr (.gpr (BitVec.ofNat 5 s.val)) (BitVec.ofNat 12 imm.val) false) gs =
      ((gs.writeReg64 .xzr (Arm64.AddWithCarry64 x (~~~y) true).1).setPState ps).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.State.readReg,
          Arm64.State.writeReg, x, y, ps]
  refine ⟨_, st', decode_cmp_ri s imm, hexec, ?_⟩
  rw [hgs]
  refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setPState, Arm64.State.writeReg64,
                    Arm64.State.readReg64, Ode.noted] using hA.gpr k
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setPState, Arm64.State.writeReg64, Ode.noted] using hA.sp
  · intro v j; simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setPState, Arm64.State.writeReg64,
                      Arm64.State.readVReg128, Ode.noted] using hA.vec v j
  · intro a ha; simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setPState, Arm64.State.writeReg64, Ode.noted] using hA.mem a ha
  · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.setPState, Arm64.State.writeReg64,
               Ode.noted, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
    have : 4 % 2 ^ 64 = 4 := by decide
    unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
  · change ps.z = zVal
    rw [show ps.z = decide (x.toNat = y.toNat) from hz, hA.gpr s, hy]
    by_cases h : st.reg (armSlot s.val) = imm.val <;> simp [zVal, h]
  · change ps.c = !cVal
    rw [show ps.c = !decide (x.toNat < y.toNat) from hc, hA.gpr s, hy]
    by_cases h : st.reg (armSlot s.val) < imm.val <;> simp [cVal, h]

/-! ## Rows 17, 18 & 19: `b` (`jump I`), `b_eq` (`jump I if zf`), `b_ne` (`jump I if not zf`) -/

def encodeB (imm26 : BitVec 26) : BitVec 32 :=
  0x14000000#32 ||| BitVec.ofNat 32 imm26.toNat

def encodeBEq (imm19 : BitVec 19) : BitVec 32 := encodeBCond 0#4 imm19
def encodeBNe (imm19 : BitVec 19) : BitVec 32 := encodeBCond 1#4 imm19

def effectB : List Ode.Stmt := [.jump (.name "I") none]
def effectBEq : List Ode.Stmt := [.jump (.name "I") (some ("zf", true))]
def effectBNe : List Ode.Stmt := [.jump (.name "I") (some ("zf", false))]

theorem encodeB_fixed (imm26 : BitVec 26) :
    encodeB imm26 &&& 0xfc000000#32 = 0x14000000#32 &&& 0xfc000000#32 := by
  have hi : imm26.toNat < 2 ^ 26 := imm26.isLt
  have h1 : (BitVec.ofNat 32 imm26.toNat <<< 0) &&& 0xfc000000#32 = 0#32 := field_and_eq_zero hi (by decide)
  simp only [BitVec.shiftLeft_zero] at h1
  unfold encodeB; simp only [BitVec.and_or_distrib_right, h1, BitVec.or_zero]

theorem decode_b (imm26 : BitVec 26) :
    Arm64.decode (encodeB imm26) = some (.b ((imm26.signExtend 64) <<< 2)) := by
  have hf := encodeB_fixed imm26
  have ex_i : (encodeB imm26).extractLsb' 0 26 = imm26 := by
    unfold encodeB; simp only [extract_or]
    have h0 : (0x14000000#32).extractLsb' 0 26 = 0#26 := by decide
    have h1 : (BitVec.ofNat 32 imm26.toNat <<< 0).extractLsb' 0 26 = BitVec.ofNat 26 imm26.toNat := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h1; rw [h0, h1]; simp
  have h31 : (encodeB imm26).getLsbD 31 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide), h31, ex_i,
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
             mask_of_fixed hf (m := 0x7c000000#32) (by decide),
             Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_b (imm26 : BitVec 26) (target : Nat) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (target : Int))
    (htlt : target < Ode.M64)
    (htarget : prog.base + target = (gs.pc + ((imm26.signExtend 64) <<< 2)).toNat) :
    ∃ ginst st',
      Arm64.decode (encodeB imm26) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectB, bindJump numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hmodT : ((target : Int) % (Ode.M64 : Int)).toNat = target := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr htlt)]; rfl
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st' : Ode.State := Ode.noted (bindJump numStr) st0 (.jump (.name "I") none) { st0 with rip := prog.base + target }
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectB, bindJump numStr, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectB, Ode.execStmt, Ode.value, Ode.isNumberLetter,
          bindJump, List.lookup, hnum, hmodT, st', st0]
  refine ⟨.b ((imm26.signExtend 64) <<< 2), st', decode_b imm26, hexec, ?_, rfl⟩
  refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
  · simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC, Ode.noted] using hA.sp
  · intro v j; simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
  · intro a ha; simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC, Ode.noted] using hA.mem a ha
  · simp [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC, Ode.noted, htarget]
  · simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC, Ode.noted] using hA.zf
  · simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC, Ode.noted] using hA.cf

theorem agree_b_eq (imm19 : BitVec 19) (target : Nat) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (target : Int))
    (htlt : target < Ode.M64)
    (htarget : prog.base + target = (gs.pc + ((imm19.signExtend 64) <<< 2)).toNat)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeBEq imm19) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectBEq, bindJump numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hmodT : ((target : Int) % (Ode.M64 : Int)).toNat = target := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr htlt)]; rfl
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let stBody : Ode.State := if st.zf == true then { st0 with rip := prog.base + target } else st0
  let st' : Ode.State := Ode.noted (bindJump numStr) st0 (.jump (.name "I") (some ("zf", true))) stBody
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectBEq, bindJump numStr, next⟩ u st = some (.next st') := by
    cases hzf : st.zf
    · simp [Ode.exec, Ode.execAll, effectBEq, Ode.execStmt, Ode.condFlag, st', stBody, st0, hzf]
    · simp [Ode.exec, Ode.execAll, effectBEq, Ode.execStmt, Ode.condFlag, Ode.value, Ode.isNumberLetter,
            bindJump, List.lookup, hnum, hmodT, st', stBody, st0, hzf]
  have hdec : Arm64.decode (encodeBEq imm19) = some (.bCond .EQ ((imm19.signExtend 64) <<< 2)) := by
    simpa [encodeBEq, Arm64.CondCode.ofBits] using decode_b_cond 0#4 imm19
  refine ⟨.bCond .EQ ((imm19.signExtend 64) <<< 2), st', hdec, hexec, ?_, ?_⟩
  · cases hzf : st.zf
    · have hz : gs.pstate.z = false := by rw [hA.zf, hzf]
      have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .EQ ((imm19.signExtend 64) <<< 2)) gs = gs.advancePC := by
        simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hz]
      rw [hgs]; refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
      · simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Ode.noted] using hA.sp
      · intro v j; simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
      · intro a ha; simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Ode.noted] using hA.mem a ha
      · simp only [st', stBody, st0, hzf, Arm64.State.advancePC, Ode.noted, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext, beq_iff_eq, Bool.false_eq_true, ↓reduceIte]
        have : 4 % 2 ^ 64 = 4 := by decide
        unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
      · simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Ode.noted] using hA.zf
      · simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Ode.noted] using hA.cf
    · have hz : gs.pstate.z = true := by rw [hA.zf, hzf]
      have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .EQ ((imm19.signExtend 64) <<< 2)) gs =
          gs.setPC (gs.pc + ((imm19.signExtend 64) <<< 2)) := by
        simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hz]
      rw [hgs]; refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; simpa [st', stBody, st0, hzf, Arm64.State.setPC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
      · simpa [st', stBody, st0, hzf, Arm64.State.setPC, Ode.noted] using hA.sp
      · intro v j; simpa [st', stBody, st0, hzf, Arm64.State.setPC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
      · intro a ha; simpa [st', stBody, st0, hzf, Arm64.State.setPC, Ode.noted] using hA.mem a ha
      · simp [st', stBody, st0, hzf, Arm64.State.setPC, Ode.noted, htarget]
      · simpa [st', stBody, st0, hzf, Arm64.State.setPC, Ode.noted] using hA.zf
      · simpa [st', stBody, st0, hzf, Arm64.State.setPC, Ode.noted] using hA.cf
  · cases hzf : st.zf
    · have hz : gs.pstate.z = false := by rw [hA.zf, hzf]
      simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hz, Arm64.State.advancePC]
    · have hz : gs.pstate.z = true := by rw [hA.zf, hzf]
      simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hz, Arm64.State.setPC]

theorem agree_b_ne (imm19 : BitVec 19) (target : Nat) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (target : Int))
    (htlt : target < Ode.M64)
    (htarget : prog.base + target = (gs.pc + ((imm19.signExtend 64) <<< 2)).toNat)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeBNe imm19) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectBNe, bindJump numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hmodT : ((target : Int) % (Ode.M64 : Int)).toNat = target := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr htlt)]; rfl
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let stBody : Ode.State := if st.zf == false then { st0 with rip := prog.base + target } else st0
  let st' : Ode.State := Ode.noted (bindJump numStr) st0 (.jump (.name "I") (some ("zf", false))) stBody
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectBNe, bindJump numStr, next⟩ u st = some (.next st') := by
    cases hzf : st.zf
    · simp [Ode.exec, Ode.execAll, effectBNe, Ode.execStmt, Ode.condFlag, Ode.value, Ode.isNumberLetter,
            bindJump, List.lookup, hnum, hmodT, st', stBody, st0, hzf]
    · simp [Ode.exec, Ode.execAll, effectBNe, Ode.execStmt, Ode.condFlag, st', stBody, st0, hzf]
  have hdec : Arm64.decode (encodeBNe imm19) = some (.bCond .NE ((imm19.signExtend 64) <<< 2)) := by
    simpa [encodeBNe, Arm64.CondCode.ofBits] using decode_b_cond 1#4 imm19
  refine ⟨.bCond .NE ((imm19.signExtend 64) <<< 2), st', hdec, hexec, ?_, ?_⟩
  · cases hzf : st.zf
    · have hz : gs.pstate.z = false := by rw [hA.zf, hzf]
      have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .NE ((imm19.signExtend 64) <<< 2)) gs =
          gs.setPC (gs.pc + ((imm19.signExtend 64) <<< 2)) := by
        simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hz]
      rw [hgs]; refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; simpa [st', stBody, st0, hzf, Arm64.State.setPC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
      · simpa [st', stBody, st0, hzf, Arm64.State.setPC, Ode.noted] using hA.sp
      · intro v j; simpa [st', stBody, st0, hzf, Arm64.State.setPC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
      · intro a ha; simpa [st', stBody, st0, hzf, Arm64.State.setPC, Ode.noted] using hA.mem a ha
      · simp [st', stBody, st0, hzf, Arm64.State.setPC, Ode.noted, htarget]
      · simpa [st', stBody, st0, hzf, Arm64.State.setPC, Ode.noted] using hA.zf
      · simpa [st', stBody, st0, hzf, Arm64.State.setPC, Ode.noted] using hA.cf
    · have hz : gs.pstate.z = true := by rw [hA.zf, hzf]
      have hgs : Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .NE ((imm19.signExtend 64) <<< 2)) gs = gs.advancePC := by
        simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hz]
      rw [hgs]; refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Arm64.State.readReg64, Ode.noted] using hA.gpr k
      · simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Ode.noted] using hA.sp
      · intro v j; simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
      · intro a ha; simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Ode.noted] using hA.mem a ha
      · simp only [st', stBody, st0, hzf, Arm64.State.advancePC, Ode.noted, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext, beq_iff_eq, Bool.true_eq_false, ↓reduceIte]
        have : 4 % 2 ^ 64 = 4 := by decide
        unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
      · simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Ode.noted] using hA.zf
      · simpa [st', stBody, st0, hzf, Arm64.State.advancePC, Ode.noted] using hA.cf
  · cases hzf : st.zf
    · have hz : gs.pstate.z = false := by rw [hA.zf, hzf]
      simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hz, Arm64.State.setPC]
    · have hz : gs.pstate.z = true := by rw [hA.zf, hzf]
      simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, hz, Arm64.State.advancePC]

/-! ## Row 20: `strb` (`strb S32, [B64, N] | .strb .S .B N | mem8(B, N) = low8(S)`) -/

def encodeStrb (s b : Fin 31) (n : Fin 4096) : BitVec 32 :=
  0x39000000#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| (BitVec.ofNat 32 b.val <<< 5) ||| BitVec.ofNat 32 s.val

def effectStrb : List Ode.Stmt :=
  [.set (.call "mem8" [.name "B", .name "N"]) (.call "low8" [.name "S"])]

def bindStrb (s b : Fin 31) (numStr : String) : Ode.Bind :=
  [("B", armRegName b.val), ("N", numStr), ("S", armRegName s.val)]

theorem encodeStrb_fixed (s b : Fin 31) (n : Fin 4096) :
    encodeStrb s b n &&& 0xffc00000#32 = 0x39000000#32 &&& 0xffc00000#32 := by
  have hs : s.val < 2 ^ 5 := by omega
  have hb : b.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := n.isLt
  have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hn (by decide)
  have h2 : (BitVec.ofNat 32 b.val <<< 5) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hb (by decide)
  have h3 : (BitVec.ofNat 32 s.val <<< 0) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hs (by decide)
  simp only [BitVec.shiftLeft_zero] at h3
  unfold encodeStrb; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]

theorem decode_strb (s b : Fin 31) (n : Fin 4096) :
    Arm64.decode (encodeStrb s b n) =
      some (.str .B8 (.gpr (BitVec.ofNat 5 s.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 n.val))) := by
  have hf := encodeStrb_fixed s b n
  have hs : s.val < 2 ^ 5 := by omega
  have hb : b.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := n.isLt
  have ex_s : (encodeStrb s b n).extractLsb' 0 5 = BitVec.ofNat 5 s.val := by
    unfold encodeStrb; simp only [extract_or]
    have h0 : (0x39000000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_b : (encodeStrb s b n).extractLsb' 5 5 = BitVec.ofNat 5 b.val := by
    unfold encodeStrb; simp only [extract_or]
    have h0 : (0x39000000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 b.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hs (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_n : (encodeStrb s b n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeStrb; simp only [extract_or]
    have h0 : (0x39000000#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 10 12 = 0#12 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hs (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_sz : (encodeStrb s b n).extractLsb' 30 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeStrb s b n).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hshift : (BitVec.ofNat 12 n.val).zeroExtend 64 <<< 0 = BitVec.ofNat 64 n.val := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have : n.val < 4096 := n.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             ex_s, ex_b, ex_n, ex_sz, ex_opc, fromZRBits_fin31, fromSPBits_fin31,
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
  simp only [Arm64.mkLoadStoreInst, BitVec.toNat_ofNat]
  rw [hshift]; rfl

theorem agree_strb (s b : Fin 31) (n : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (n.val : Int))
    (hfit : st.reg (armSlot b.val) + n.val < Ode.M64)
    (hwrite : gs.mem.canWrite (gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 n.val) 1 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeStrb s b n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectStrb, bindStrb s b numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hnlt : n.val < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  have hmodN : ((n.val : Int) % (Ode.M64 : Int)).toNat = n.val := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hnlt)]; rfl
  have hea_nat : (st.reg (armSlot b.val) + n.val) % Ode.M64 = st.reg (armSlot b.val) + n.val :=
    Nat.mod_eq_of_lt hfit
  have hea_bv : gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 n.val =
      BitVec.ofNat 64 (st.reg (armSlot b.val) + n.val) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.gpr b]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hfit]
  let a := st.reg (armSlot b.val) + n.val
  let byteVal := st.reg (armSlot s.val) % 256
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := { st0 with mem := Ode.store st.mem a byteVal 1 }
  let st' : Ode.State := Ode.noted (bindStrb s b numStr) st0 (.set (.call "mem8" [.name "B", .name "N"]) (.call "low8" [.name "S"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectStrb, bindStrb s b numStr, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.write a 1 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectStrb, Ode.execStmt, Ode.isUnknown,
          Ode.value, Ode.values, Ode.memSize, Ode.prim, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf,
          bindStrb, List.lookup, regIndex_armRegName, Ode.sumList,
          hnum, hmodN, hea_nat, hall, a, byteVal, st', st1, st0]
  have hwrite' : gs.mem.canWrite (BitVec.ofNat 64 a) 1 = true := by rwa [← hea_bv]
  let val64 := gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.str .B8 (.gpr (BitVec.ofNat 5 s.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 n.val))) gs =
      (gs.setMem (gs.mem.write8 (BitVec.ofNat 64 a) (val64.truncate 8))).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execStr, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.MemWidth.bytes,
          Arm64.Memory.writeSized, hea_bv, a, hwrite', val64]
  refine ⟨_, st', decode_strb s b n, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Arm64.State.readReg64, Ode.noted] using hA.gpr k
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Ode.noted] using hA.sp
  · intro v j; simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
  · intro addr haddr
    simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Arm64.Memory.read8, Arm64.Memory.write8, Ode.noted]
    by_cases heq : addr = a
    · subst heq
      simp only [↓reduceIte, Ode.store, BitVec.toNat_setWidth, val64, hA.gpr s, byteVal]
      have : (2 ^ 8 : Nat) = 256 := by decide
      rw [this, Nat.mod_mod]
    · have hne_bv : BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a := by
        intro hbv
        have ht := congrArg BitVec.toNat hbv
        simp only [BitVec.toNat_ofNat] at ht
        unfold Ode.M64 at haddr hfit
        rw [Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt hfit] at ht
        exact heq ht
      simp only [hne_bv, ↓reduceIte, Ode.store, heq]
      simpa [Arm64.Memory.read8] using hA.mem addr haddr
  · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Ode.noted, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
    have : 4 % 2 ^ 64 = 4 := by decide
    unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Ode.noted] using hA.zf
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Ode.noted] using hA.cf

/-! ## Shared helpers for rows 21–30 (stack pointer, loads/stores, call/return) -/

theorem agreeState_writeSp {prog : Ode.Program} {st : Ode.State} {gs : Arm64.State} {next : Nat}
    (hA : AgreeState st gs) (v : BitVec 64) (val : Nat) (hv : v.toNat = val)
    (bind : Ode.Bind) (stmt : Ode.Stmt)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
    let st1 : Ode.State := Ode.setReg st0 Ode.RSP val
    let st' : Ode.State := Ode.noted bind st0 stmt st1
    AgreeState st' ((gs.writeReg64 .sp v).advancePC) := by
  intro st0 st1 st'
  refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.readReg64, Arm64.State.writeReg64,
           Ode.setReg, Ode.noted, armSlot_ne_rsp k] using hA.gpr k
  · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted,
               ↓reduceIte, hv]
    exact (Nat.mod_eq_of_lt (by rw [← hv]; exact v.isLt)).symm
  · intro vec j
    simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Arm64.State.readVReg128,
           Ode.setReg, Ode.noted] using hA.vec vec j
  · intro a ha
    simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.mem a ha
  · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted,
               BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
    have : 4 % 2 ^ 64 = 4 := by decide
    unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.zf
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeReg64, Ode.setReg, Ode.noted] using hA.cf

theorem read32_eq_load {st : Ode.State} {gs : Arm64.State} (hA : AgreeState st gs)
    {a : Nat} (hfit : a + 4 ≤ Ode.M64) :
    (gs.mem.read32 (BitVec.ofNat 64 a)).toNat = Ode.load st.mem a 4 := by
  unfold Arm64.Memory.read32 Ode.load Ode.load Ode.load Ode.load Ode.load
  have hb : ∀ k : Nat, k < 4 →
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
  simp only [Nat.add_zero] at h0
  simp only [toNat_append_eq, Nat.add_assoc]
  have e2 : (st.mem (a + (1 + 1))).val = (st.mem (a + 2)).val := rfl
  have e3 : (st.mem (a + (1 + (1 + 1)))).val = (st.mem (a + 3)).val := rfl
  rw [e2, e3, h0, h1, h2, h3]
  omega

theorem store_at (mem : Nat → Ode.Byte) : ∀ n a v addr,
    (Ode.store mem a v n addr).val =
      if a ≤ addr ∧ addr < a + n then (v / 256 ^ (addr - a)) % 256 else (mem addr).val
  | 0, a, v, addr => by simp [Ode.store]; omega
  | n + 1, a, v, addr => by
    unfold Ode.store
    rw [store_at _ n (a + 1) (v / 256) addr]
    by_cases hhi : a + 1 ≤ addr ∧ addr < a + 1 + n
    · have h1 : a ≤ addr ∧ addr < a + (n + 1) := by omega
      simp only [hhi, h1, and_self, ↓reduceIte]
      rw [Nat.div_div_eq_div_mul]
      have hexp : 256 * 256 ^ (addr - (a + 1)) = 256 ^ (addr - a) := by
        have hk : addr - a = (addr - (a + 1)) + 1 := by omega
        rw [hk, Nat.pow_succ, Nat.mul_comm]
      rw [hexp]
    · simp only [hhi, ↓reduceIte]
      by_cases heq : addr = a
      · subst heq
        have h1 : addr ≤ addr ∧ addr < addr + (n + 1) := by omega
        simp [h1]
      · have h1 : ¬ (a ≤ addr ∧ addr < a + (n + 1)) := by omega
        simp [heq, h1]

theorem bv64_add_ofNat_eq {a k addr : Nat} (hfit : a + k < Ode.M64) (haddr : addr < Ode.M64) :
    (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + BitVec.ofNat 64 k) ↔ addr = a + k := by
  unfold Ode.M64 at hfit haddr
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
    rw [Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at ht
    exact ht
  · intro h; subst h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem read8_write8_eq (m : Arm64.Memory) (p q : BitVec 64) (b : BitVec 8) :
    (m.write8 p b).read8 q = if q = p then b else m.read8 q := by
  by_cases h : q = p <;> simp [Arm64.Memory.read8, Arm64.Memory.write8, h]

theorem extract_byte_toNat {w : Nat} (v : BitVec w) (k : Nat) :
    (v.extractLsb' (8 * k) 8).toNat = (v.toNat / 256 ^ k) % 256 := by
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have h1 : 2 ^ (8 * k) = 256 ^ k := by rw [Nat.pow_mul]
  rw [h1]

theorem write32_eq_store {st : Ode.State} {gs : Arm64.State} (hA : AgreeState st gs)
    {a : Nat} (hfit : a + 4 ≤ Ode.M64) (v : BitVec 32) (val : Nat) (hv : v.toNat = val)
    {addr : Nat} (haddr : addr < Ode.M64) :
    ((gs.mem.write32 (BitVec.ofNat 64 a) v).read8 (BitVec.ofNat 64 addr)).toNat =
      (Ode.store st.mem a val 4 addr).val := by
  rw [store_at]
  unfold Arm64.Memory.write32
  simp only [read8_write8_eq]
  have h3 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 3#64) ↔ addr = a + 3 := bv64_add_ofNat_eq (by omega) haddr
  have h2 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 2#64) ↔ addr = a + 2 := bv64_add_ofNat_eq (by omega) haddr
  have h1 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 1#64) ↔ addr = a + 1 := bv64_add_ofNat_eq (by omega) haddr
  have h0 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 0#64) ↔ addr = a + 0 := bv64_add_ofNat_eq (by omega) haddr
  by_cases c3 : addr = a + 3
  · simp only [h3.mpr c3, show a ≤ addr ∧ addr < a + 4 by omega, and_self, ↓reduceIte]
    subst c3; simpa [hv] using extract_byte_toNat v 3
  · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 3#64 from fun h => c3 (h3.mp h), ↓reduceIte]
    by_cases c2 : addr = a + 2
    · simp only [h2.mpr c2, show a ≤ addr ∧ addr < a + 4 by omega, and_self, ↓reduceIte]
      subst c2; simpa [hv] using extract_byte_toNat v 2
    · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 2#64 from fun h => c2 (h2.mp h), ↓reduceIte]
      by_cases c1 : addr = a + 1
      · simp only [h1.mpr c1, show a ≤ addr ∧ addr < a + 4 by omega, and_self, ↓reduceIte]
        subst c1; simpa [hv] using extract_byte_toNat v 1
      · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 1#64 from fun h => c1 (h1.mp h), ↓reduceIte]
        by_cases c0 : addr = a
        · simp only [h0.mpr (by omega), show a ≤ addr ∧ addr < a + 4 by omega, and_self, ↓reduceIte]
          subst c0; simp [hv, extract_byte_toNat v 0]
        · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 0#64 from fun h => c0 (by have := h0.mp h; omega),
                     show ¬(a ≤ addr ∧ addr < a + 4) by omega, ↓reduceIte]
          exact hA.mem addr haddr

theorem write64_eq_store {st : Ode.State} {gs : Arm64.State} (hA : AgreeState st gs)
    {a : Nat} (hfit : a + 8 ≤ Ode.M64) (v : BitVec 64) (val : Nat) (hv : v.toNat = val)
    {addr : Nat} (haddr : addr < Ode.M64) :
    ((gs.mem.write64 (BitVec.ofNat 64 a) v).read8 (BitVec.ofNat 64 addr)).toNat =
      (Ode.store st.mem a val 8 addr).val := by
  rw [store_at]
  unfold Arm64.Memory.write64
  simp only [read8_write8_eq]
  have h7 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 7#64) ↔ addr = a + 7 := bv64_add_ofNat_eq (by omega) haddr
  have h6 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 6#64) ↔ addr = a + 6 := bv64_add_ofNat_eq (by omega) haddr
  have h5 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 5#64) ↔ addr = a + 5 := bv64_add_ofNat_eq (by omega) haddr
  have h4 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 4#64) ↔ addr = a + 4 := bv64_add_ofNat_eq (by omega) haddr
  have h3 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 3#64) ↔ addr = a + 3 := bv64_add_ofNat_eq (by omega) haddr
  have h2 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 2#64) ↔ addr = a + 2 := bv64_add_ofNat_eq (by omega) haddr
  have h1 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 1#64) ↔ addr = a + 1 := bv64_add_ofNat_eq (by omega) haddr
  have h0 : (BitVec.ofNat 64 addr = BitVec.ofNat 64 a + 0#64) ↔ addr = a + 0 := bv64_add_ofNat_eq (by omega) haddr
  by_cases c7 : addr = a + 7
  · simp only [h7.mpr c7, show a ≤ addr ∧ addr < a + 8 by omega, and_self, ↓reduceIte]
    subst c7; simpa [hv] using extract_byte_toNat v 7
  · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 7#64 from fun h => c7 (h7.mp h), ↓reduceIte]
    by_cases c6 : addr = a + 6
    · simp only [h6.mpr c6, show a ≤ addr ∧ addr < a + 8 by omega, and_self, ↓reduceIte]
      subst c6; simpa [hv] using extract_byte_toNat v 6
    · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 6#64 from fun h => c6 (h6.mp h), ↓reduceIte]
      by_cases c5 : addr = a + 5
      · simp only [h5.mpr c5, show a ≤ addr ∧ addr < a + 8 by omega, and_self, ↓reduceIte]
        subst c5; simpa [hv] using extract_byte_toNat v 5
      · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 5#64 from fun h => c5 (h5.mp h), ↓reduceIte]
        by_cases c4 : addr = a + 4
        · simp only [h4.mpr c4, show a ≤ addr ∧ addr < a + 8 by omega, and_self, ↓reduceIte]
          subst c4; simpa [hv] using extract_byte_toNat v 4
        · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 4#64 from fun h => c4 (h4.mp h), ↓reduceIte]
          by_cases c3 : addr = a + 3
          · simp only [h3.mpr c3, show a ≤ addr ∧ addr < a + 8 by omega, and_self, ↓reduceIte]
            subst c3; simpa [hv] using extract_byte_toNat v 3
          · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 3#64 from fun h => c3 (h3.mp h), ↓reduceIte]
            by_cases c2 : addr = a + 2
            · simp only [h2.mpr c2, show a ≤ addr ∧ addr < a + 8 by omega, and_self, ↓reduceIte]
              subst c2; simpa [hv] using extract_byte_toNat v 2
            · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 2#64 from fun h => c2 (h2.mp h), ↓reduceIte]
              by_cases c1 : addr = a + 1
              · simp only [h1.mpr c1, show a ≤ addr ∧ addr < a + 8 by omega, and_self, ↓reduceIte]
                subst c1; simpa [hv] using extract_byte_toNat v 1
              · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 1#64 from fun h => c1 (h1.mp h), ↓reduceIte]
                by_cases c0 : addr = a
                · simp only [h0.mpr (by omega), show a ≤ addr ∧ addr < a + 8 by omega, and_self, ↓reduceIte]
                  subst c0; simp [hv, extract_byte_toNat v 0]
                · simp only [show BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 a + 0#64 from fun h => c0 (by have := h0.mp h; omega),
                             show ¬(a ≤ addr ∧ addr < a + 8) by omega, ↓reduceIte]
                  exact hA.mem addr haddr

theorem agreeState_setMem {prog : Ode.Program} {st : Ode.State} {gs : Arm64.State} {next : Nat}
    (hA : AgreeState st gs) (mem' : Nat → Ode.Byte) (gmem' : Arm64.Memory)
    (hmem : ∀ addr, addr < Ode.M64 → (gmem'.read8 (BitVec.ofNat 64 addr)).toNat = (mem' addr).val)
    (bind : Ode.Bind) (stmt : Ode.Stmt)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
    let st1 : Ode.State := { st0 with mem := mem' }
    let st' : Ode.State := Ode.noted bind st0 stmt st1
    AgreeState st' ((gs.setMem gmem').advancePC) := by
  intro st0 st1 st'
  refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Arm64.State.readReg64, Ode.noted] using hA.gpr k
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Ode.noted] using hA.sp
  · intro v j; simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Arm64.State.readVReg128, Ode.noted] using hA.vec v j
  · intro addr haddr
    simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Ode.noted] using hmem addr haddr
  · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Ode.noted, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
    have : 4 % 2 ^ 64 = 4 := by decide
    unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Ode.noted] using hA.zf
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.setMem, Ode.noted] using hA.cf

/-! ## Rows 21, 22 & 23: `add_sp`, `sub_sp`, `add_of_sp` -/

def encodeAddSp (imm : Fin 4096) : BitVec 32 := 0x910003ff#32 ||| (BitVec.ofNat 32 imm.val <<< 10)
def encodeSubSp (imm : Fin 4096) : BitVec 32 := 0xd10003ff#32 ||| (BitVec.ofNat 32 imm.val <<< 10)
def encodeAddOfSp (d : Fin 31) (imm : Fin 4096) : BitVec 32 :=
  0x910003e0#32 ||| (BitVec.ofNat 32 imm.val <<< 10) ||| BitVec.ofNat 32 d.val

def effectAddSp : List Ode.Stmt := [.set (.name "sp") (.call "add64" [.name "sp", .name "I"])]
def effectSubSp : List Ode.Stmt := [.set (.name "sp") (.call "sub64" [.name "sp", .name "I"])]
def effectAddOfSp : List Ode.Stmt := [.set (.name "D") (.call "add64" [.name "sp", .name "I"])]

def bindSpImm (numStr : String) : Ode.Bind := [("I", numStr)]
def bindAddOfSp (d : Fin 31) (numStr : String) : Ode.Bind := [("D", armRegName d.val), ("I", numStr)]

theorem encodeAddSp_fixed (imm : Fin 4096) :
    encodeAddSp imm &&& 0xffc003ff#32 = 0x910003ff#32 &&& 0xffc003ff#32 := by
  have hi : imm.val < 2 ^ 12 := imm.isLt
  have h1 : (BitVec.ofNat 32 imm.val <<< 10) &&& 0xffc003ff#32 = 0#32 := field_and_eq_zero hi (by decide)
  unfold encodeAddSp; simp only [BitVec.and_or_distrib_right, h1, BitVec.or_zero]

theorem decode_add_sp (imm : Fin 4096) :
    Arm64.decode (encodeAddSp imm) = some (.addSubImm .W64 .ADD .sp .sp (BitVec.ofNat 12 imm.val) false) := by
  have hf := encodeAddSp_fixed imm
  have ex_i : (encodeAddSp imm).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := by
    unfold encodeAddSp; simp only [extract_or]
    have h0 : (0x910003ff#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := extract_field_hit (by omega)
    rw [h0, h1]; simp
  have hsf : (encodeAddSp imm).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h30 : (encodeAddSp imm).getLsbD 30 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h29 : (encodeAddSp imm).getLsbD 29 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h22 : (encodeAddSp imm).getLsbD 22 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hrn : (encodeAddSp imm).extractLsb' 5 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  have hrd : (encodeAddSp imm).extractLsb' 0 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             hsf, h30, h29, h22, hrn, hrd, ex_i,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x10000000#32) (by decide),
             mask_of_fixed hf (m := 0x1f800000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_add_sp (imm : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (imm.val : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeAddSp imm) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectAddSp, bindSpImm numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hilt : imm.val < Ode.M64 := by unfold Ode.M64; have := imm.isLt; omega
  have hmod : ((imm.val : Int) % (Ode.M64 : Int)).toNat = imm.val := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hilt)]; rfl
  let val := (st.reg Ode.RSP + imm.val) % Ode.M64
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 Ode.RSP val
  let st' : Ode.State := Ode.noted (bindSpImm numStr) st0 (.set (.name "sp") (.call "add64" [.name "sp", .name "I"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectAddSp, bindSpImm numStr, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectAddSp, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize, Ode.prim,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindSpImm, List.lookup,
          regIndex_sp, hnum, hmod, val, st', st1, st0]
  have himm : ((BitVec.ofNat 12 imm.val).zeroExtend 64).toNat = imm.val := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := imm.isLt; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hv : (Arm64.AddWithCarry64 gs.sp ((BitVec.ofNat 12 imm.val).zeroExtend 64) false).1.toNat = val := by
    rw [addWithCarry64_add_val, hA.sp, himm]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.addSubImm .W64 .ADD .sp .sp (BitVec.ofNat 12 imm.val) false) gs =
      (gs.writeReg64 .sp (Arm64.AddWithCarry64 gs.sp ((BitVec.ofNat 12 imm.val).zeroExtend 64) false).1).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.readReg64, Arm64.State.writeReg]
  refine ⟨_, st', decode_add_sp imm, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]; exact agreeState_writeSp hA _ val hv _ _ hnext hpc

theorem encodeSubSp_fixed (imm : Fin 4096) :
    encodeSubSp imm &&& 0xffc003ff#32 = 0xd10003ff#32 &&& 0xffc003ff#32 := by
  have hi : imm.val < 2 ^ 12 := imm.isLt
  have h1 : (BitVec.ofNat 32 imm.val <<< 10) &&& 0xffc003ff#32 = 0#32 := field_and_eq_zero hi (by decide)
  unfold encodeSubSp; simp only [BitVec.and_or_distrib_right, h1, BitVec.or_zero]

theorem decode_sub_sp (imm : Fin 4096) :
    Arm64.decode (encodeSubSp imm) = some (.addSubImm .W64 .SUB .sp .sp (BitVec.ofNat 12 imm.val) false) := by
  have hf := encodeSubSp_fixed imm
  have ex_i : (encodeSubSp imm).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := by
    unfold encodeSubSp; simp only [extract_or]
    have h0 : (0xd10003ff#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := extract_field_hit (by omega)
    rw [h0, h1]; simp
  have hsf : (encodeSubSp imm).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h30 : (encodeSubSp imm).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h29 : (encodeSubSp imm).getLsbD 29 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h22 : (encodeSubSp imm).getLsbD 22 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hrn : (encodeSubSp imm).extractLsb' 5 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  have hrd : (encodeSubSp imm).extractLsb' 0 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             hsf, h30, h29, h22, hrn, hrd, ex_i,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x10000000#32) (by decide),
             mask_of_fixed hf (m := 0x1f800000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_sub_sp (imm : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (imm.val : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeSubSp imm) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectSubSp, bindSpImm numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hilt : imm.val < Ode.M64 := by unfold Ode.M64; have := imm.isLt; omega
  have hmod : ((imm.val : Int) % (Ode.M64 : Int)).toNat = imm.val := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hilt)]; rfl
  let val := (st.reg Ode.RSP + (Ode.M64 - imm.val % Ode.M64)) % Ode.M64
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 Ode.RSP val
  let st' : Ode.State := Ode.noted (bindSpImm numStr) st0 (.set (.name "sp") (.call "sub64" [.name "sp", .name "I"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectSubSp, bindSpImm numStr, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectSubSp, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize, Ode.prim,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindSpImm, List.lookup,
          regIndex_sp, hnum, hmod, val, st', st1, st0]
  have himm : ((BitVec.ofNat 12 imm.val).zeroExtend 64).toNat = imm.val := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := imm.isLt; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hv : (Arm64.AddWithCarry64 gs.sp (~~~((BitVec.ofNat 12 imm.val).zeroExtend 64)) true).1.toNat = val := by
    rw [addWithCarry64_sub_val, hA.sp, himm]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.addSubImm .W64 .SUB .sp .sp (BitVec.ofNat 12 imm.val) false) gs =
      (gs.writeReg64 .sp (Arm64.AddWithCarry64 gs.sp (~~~((BitVec.ofNat 12 imm.val).zeroExtend 64)) true).1).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.readReg64, Arm64.State.writeReg]
  refine ⟨_, st', decode_sub_sp imm, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]; exact agreeState_writeSp hA _ val hv _ _ hnext hpc

theorem encodeAddOfSp_fixed (d : Fin 31) (imm : Fin 4096) :
    encodeAddOfSp d imm &&& 0xffc003e0#32 = 0x910003e0#32 &&& 0xffc003e0#32 := by
  have hd : d.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 12 := imm.isLt
  have h1 : (BitVec.ofNat 32 imm.val <<< 10) &&& 0xffc003e0#32 = 0#32 := field_and_eq_zero hi (by decide)
  have h2 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffc003e0#32 = 0#32 := field_and_eq_zero hd (by decide)
  simp only [BitVec.shiftLeft_zero] at h2
  unfold encodeAddOfSp; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]

theorem decode_add_of_sp (d : Fin 31) (imm : Fin 4096) :
    Arm64.decode (encodeAddOfSp d imm) =
      some (.addSubImm .W64 .ADD (.gpr (BitVec.ofNat 5 d.val)) .sp (BitVec.ofNat 12 imm.val) false) := by
  have hf := encodeAddOfSp_fixed d imm
  have hd : d.val < 2 ^ 5 := by omega
  have hi : imm.val < 2 ^ 12 := imm.isLt
  have ex_d : (encodeAddOfSp d imm).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeAddOfSp; simp only [extract_or]
    have h0 : (0x910003e0#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_i : (encodeAddOfSp d imm).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := by
    unfold encodeAddOfSp; simp only [extract_or]
    have h0 : (0x910003e0#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 imm.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 imm.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have hsf : (encodeAddOfSp d imm).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h30 : (encodeAddOfSp d imm).getLsbD 30 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h29 : (encodeAddOfSp d imm).getLsbD 29 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have h22 : (encodeAddOfSp d imm).getLsbD 22 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hrn : (encodeAddOfSp d imm).extractLsb' 5 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             hsf, h30, h29, h22, hrn, ex_d, ex_i, fromSPBits_fin31,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
             mask_ne_of_fixed hf (m := 0x1f000000#32) (c := 0x10000000#32) (by decide),
             mask_of_fixed hf (m := 0x1f800000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_add_of_sp (d : Fin 31) (imm : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (imm.val : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeAddOfSp d imm) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectAddOfSp, bindAddOfSp d numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hilt : imm.val < Ode.M64 := by unfold Ode.M64; have := imm.isLt; omega
  have hmod : ((imm.val : Int) % (Ode.M64 : Int)).toNat = imm.val := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hilt)]; rfl
  let val := (st.reg Ode.RSP + imm.val) % Ode.M64
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) val
  let st' : Ode.State := Ode.noted (bindAddOfSp d numStr) st0 (.set (.name "D") (.call "add64" [.name "sp", .name "I"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectAddOfSp, bindAddOfSp d numStr, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectAddOfSp, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize, Ode.prim,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindAddOfSp, List.lookup,
          regIndex_armRegName, regIndex_sp, hnum, hmod, val, st', st1, st0]
  have himm : ((BitVec.ofNat 12 imm.val).zeroExtend 64).toNat = imm.val := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := imm.isLt; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hv : (Arm64.AddWithCarry64 gs.sp ((BitVec.ofNat 12 imm.val).zeroExtend 64) false).1.toNat = val := by
    rw [addWithCarry64_add_val, hA.sp, himm]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.addSubImm .W64 .ADD (.gpr (BitVec.ofNat 5 d.val)) .sp (BitVec.ofNat 12 imm.val) false) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) (Arm64.AddWithCarry64 gs.sp ((BitVec.ofNat 12 imm.val).zeroExtend 64) false).1).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.readReg64, Arm64.State.writeReg]
  refine ⟨_, st', decode_add_of_sp d imm, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]; exact agreeState_writeGpr hA d _ val hv _ _ hnext hpc

/-! ## Rows 24, 25, 26, 27 & 28: `ldr64`, `str64`, `ldr32`, `str32`, `str64_sp` -/

def encodeLdr64 (d b : Fin 31) (n : Fin 4096) : BitVec 32 :=
  0xf9400000#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| (BitVec.ofNat 32 b.val <<< 5) ||| BitVec.ofNat 32 d.val

def encodeStr64 (s b : Fin 31) (n : Fin 4096) : BitVec 32 :=
  0xf9000000#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| (BitVec.ofNat 32 b.val <<< 5) ||| BitVec.ofNat 32 s.val

def encodeLdr32 (d b : Fin 31) (n : Fin 4096) : BitVec 32 :=
  0xb9400000#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| (BitVec.ofNat 32 b.val <<< 5) ||| BitVec.ofNat 32 d.val

def encodeStr32 (s b : Fin 31) (n : Fin 4096) : BitVec 32 :=
  0xb9000000#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| (BitVec.ofNat 32 b.val <<< 5) ||| BitVec.ofNat 32 s.val

def encodeStr64Sp (s : Fin 31) (n : Fin 4096) : BitVec 32 :=
  0xf90003e0#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| BitVec.ofNat 32 s.val

def effectLdr64 : List Ode.Stmt := [.set (.name "D") (.call "mem64" [.name "B", .name "N"])]
def effectStr64 : List Ode.Stmt := [.set (.call "mem64" [.name "B", .name "N"]) (.name "S")]
def effectLdr32 : List Ode.Stmt := [.set (.name "D") (.call "low32" [.call "mem32" [.name "B", .name "N"]])]
def effectStr32 : List Ode.Stmt := [.set (.call "mem32" [.name "B", .name "N"]) (.call "low32" [.name "S"])]
def effectStr64Sp : List Ode.Stmt := [.set (.call "mem64" [.call "on16" [.name "sp"], .name "N"]) (.name "S")]

def bindStr64Sp (s : Fin 31) (numStr : String) : Ode.Bind := [("N", numStr), ("S", armRegName s.val)]

def guardsBeforeLdstImm : List (BitVec 32 × BitVec 32) :=
  [(0xffe0001f#32, 0xd4000001#32), (0xffe0001f#32, 0xd4200000#32),
   (0xfffff01f#32, 0xd503201f#32), (0xffff0000#32, 0x00000000#32),
   (0xffffffe0#32, 0xd50b7420#32), (0x1f000000#32, 0x10000000#32),
   (0x1f800000#32, 0x11000000#32), (0x1f800000#32, 0x12000000#32),
   (0x1f800000#32, 0x12800000#32), (0x1f800000#32, 0x13000000#32),
   (0x7f800000#32, 0x13800000#32), (0x7c000000#32, 0x14000000#32),
   (0x7e000000#32, 0x34000000#32), (0x7e000000#32, 0x36000000#32),
   (0xff000010#32, 0x54000000#32), (0xff9ffc1f#32, 0xd61f0000#32),
   (0x1f000000#32, 0x0a000000#32), (0x1f200000#32, 0x0b000000#32),
   (0x1fe00000#32, 0x0b200000#32), (0x1fe0fc00#32, 0x1a000000#32),
   (0x3fe00410#32, 0x3a400000#32), (0x3fe00800#32, 0x1a800000#32),
   (0x7fff0000#32, 0x5ac00000#32), (0x7fe0e000#32, 0x1ac04000#32),
   (0x7fe00000#32, 0x1ac00000#32), (0x7f000000#32, 0x1b000000#32),
   (0x7f800000#32, 0x28000000#32), (0x3e000000#32, 0x28000000#32),
   (0xffc00000#32, 0xf9800000#32), (0xffe00c00#32, 0xf8800000#32),
   (0xffe00c00#32, 0xf8a00800#32), (0x3f200c00#32, 0x38200000#32),
   (0x3f200c00#32, 0x19000000#32)]

/-- Shared decoder helper for unsigned-immediate loads and stores (`bits[29:24] = 111001`). -/
theorem decode_at_ldstImm {w base fixed : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hnop : ((base &&& fixed) == (0xd503201f#32 &&& fixed)) = false)
    (hmatch : (0x3f000000#32 &&& fixed = 0x3f000000#32) ∧ (base &&& 0x3f000000#32 = 0x39000000#32))
    (hskip : skipsAll base fixed guardsBeforeLdstImm = true) :
    Arm64.decode w =
      let sizeBits := (w.extractLsb' 30 2).toNat
      let opc := (w.extractLsb' 22 2).toNat
      let imm12 := w.extractLsb' 10 12
      let rn := Arm64.Reg.fromSPBits (w.extractLsb' 5 5)
      let rt := Arm64.Reg.fromZRBits (w.extractLsb' 0 5)
      Arm64.mkLoadStoreInst sizeBits opc rt (.Offset rn ((imm12.zeroExtend 64) <<< sizeBits)) := by
  have sk : ∀ m c, (m, c) ∈ guardsBeforeLdstImm → ((w &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hw hskip hm
  have hhit : w &&& 0x3f000000#32 = 0x39000000#32 := by rw [mask_of_fixed hw hmatch.1, hmatch.2]
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
             sk 0x3f200c00#32 0x19000000#32 (by decide),
             hhit, beq_self_eq_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem decode_ldr64 (d b : Fin 31) (n : Fin 4096) :
    Arm64.decode (encodeLdr64 d b n) =
      some (.ldr .W64 .X64 false (.gpr (BitVec.ofNat 5 d.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 8)))) := by
  have hd : d.val < 2 ^ 5 := by omega
  have hb : b.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := n.isLt
  have hf : encodeLdr64 d b n &&& 0xffc00000#32 = 0xf9400000#32 &&& 0xffc00000#32 := by
    have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hn (by decide)
    have h2 : (BitVec.ofNat 32 b.val <<< 5) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hb (by decide)
    have h3 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hd (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeLdr64; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_ldstImm hf (by decide) ⟨by decide, by decide⟩ (by decide)]
  have ex_d : (encodeLdr64 d b n).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeLdr64; simp only [extract_or]
    have h0 : (0xf9400000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_b : (encodeLdr64 d b n).extractLsb' 5 5 = BitVec.ofNat 5 b.val := by
    unfold encodeLdr64; simp only [extract_or]
    have h0 : (0xf9400000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 b.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_n : (encodeLdr64 d b n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeLdr64; simp only [extract_or]
    have h0 : (0xf9400000#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 10 12 = 0#12 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_sz : (encodeLdr64 d b n).extractLsb' 30 2 = 3#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeLdr64 d b n).extractLsb' 22 2 = 1#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hshift : (BitVec.ofNat 12 n.val).zeroExtend 64 <<< 3 = BitVec.ofNat 64 (n.val * 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have := n.isLt; omega
  simp only [ex_d, ex_b, ex_n, ex_sz, ex_opc, fromZRBits_fin31, fromSPBits_fin31, Arm64.mkLoadStoreInst, BitVec.toNat_ofNat]
  rw [hshift]

theorem agree_ldr64 (d b : Fin 31) (n : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (n.val * 8 : Int))
    (hfit : st.reg (armSlot b.val) + n.val * 8 + 8 ≤ Ode.M64)
    (hread : gs.mem.canRead (gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 8)) 8 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeLdr64 d b n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectLdr64, bindLdrb d b numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hnlt : n.val * 8 < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  have hmodN : ((n.val * 8 : Int) % (Ode.M64 : Int)).toNat = n.val * 8 := by unfold Ode.M64; have := n.isLt; omega
  have hea_nat : (st.reg (armSlot b.val) + n.val * 8) % Ode.M64 = st.reg (armSlot b.val) + n.val * 8 :=
    Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 8) =
      BitVec.ofNat 64 (st.reg (armSlot b.val) + n.val * 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.gpr b]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt (by omega)]
  let a := st.reg (armSlot b.val) + n.val * 8
  let val := Ode.load st.mem a 8
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) val
  let st' : Ode.State := Ode.noted (bindLdrb d b numStr) st0 (.set (.name "D") (.call "mem64" [.name "B", .name "N"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectLdr64, bindLdrb d b numStr, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.read a 8 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectLdr64, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindLdrb, List.lookup, regIndex_armRegName,
          Ode.sumList, hnum, hmodN, hea_nat, hall, a, val, st', st1, st0]
  have hread' : gs.mem.canRead (BitVec.ofNat 64 a) 8 = true := by rwa [← hea_bv]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.ldr .W64 .X64 false (.gpr (BitVec.ofNat 5 d.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 8)))) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) (gs.mem.read64 (BitVec.ofNat 64 a))).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execLdr, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized,
          Arm64.State.writeReg, hea_bv, a, hread']
  refine ⟨_, st', decode_ldr64 d b n, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]; exact agreeState_writeGpr hA d _ val (read64_eq_load hA hfit) _ _ hnext hpc

theorem decode_str64 (s b : Fin 31) (n : Fin 4096) :
    Arm64.decode (encodeStr64 s b n) =
      some (.str .X64 (.gpr (BitVec.ofNat 5 s.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 8)))) := by
  have hs : s.val < 2 ^ 5 := by omega
  have hb : b.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := n.isLt
  have hf : encodeStr64 s b n &&& 0xffc00000#32 = 0xf9000000#32 &&& 0xffc00000#32 := by
    have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hn (by decide)
    have h2 : (BitVec.ofNat 32 b.val <<< 5) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hb (by decide)
    have h3 : (BitVec.ofNat 32 s.val <<< 0) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hs (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeStr64; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_ldstImm hf (by decide) ⟨by decide, by decide⟩ (by decide)]
  have ex_s : (encodeStr64 s b n).extractLsb' 0 5 = BitVec.ofNat 5 s.val := by
    unfold encodeStr64; simp only [extract_or]
    have h0 : (0xf9000000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_b : (encodeStr64 s b n).extractLsb' 5 5 = BitVec.ofNat 5 b.val := by
    unfold encodeStr64; simp only [extract_or]
    have h0 : (0xf9000000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 b.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hs (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_n : (encodeStr64 s b n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeStr64; simp only [extract_or]
    have h0 : (0xf9000000#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 10 12 = 0#12 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hs (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_sz : (encodeStr64 s b n).extractLsb' 30 2 = 3#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeStr64 s b n).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hshift : (BitVec.ofNat 12 n.val).zeroExtend 64 <<< 3 = BitVec.ofNat 64 (n.val * 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have := n.isLt; omega
  simp only [ex_s, ex_b, ex_n, ex_sz, ex_opc, fromZRBits_fin31, fromSPBits_fin31, Arm64.mkLoadStoreInst, BitVec.toNat_ofNat]
  rw [hshift]

theorem agree_str64 (s b : Fin 31) (n : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (n.val * 8 : Int))
    (hfit : st.reg (armSlot b.val) + n.val * 8 + 8 ≤ Ode.M64)
    (hwrite : gs.mem.canWrite (gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 8)) 8 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeStr64 s b n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectStr64, bindStrb s b numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hnlt : n.val * 8 < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  have hmodN : ((n.val * 8 : Int) % (Ode.M64 : Int)).toNat = n.val * 8 := by unfold Ode.M64; have := n.isLt; omega
  have hea_nat : (st.reg (armSlot b.val) + n.val * 8) % Ode.M64 = st.reg (armSlot b.val) + n.val * 8 :=
    Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 8) =
      BitVec.ofNat 64 (st.reg (armSlot b.val) + n.val * 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.gpr b]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt (by omega)]
  let a := st.reg (armSlot b.val) + n.val * 8
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := { st0 with mem := Ode.store st.mem a (st.reg (armSlot s.val)) 8 }
  let st' : Ode.State := Ode.noted (bindStrb s b numStr) st0 (.set (.call "mem64" [.name "B", .name "N"]) (.name "S")) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectStr64, bindStrb s b numStr, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.write a 8 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectStr64, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindStrb, List.lookup, regIndex_armRegName,
          Ode.sumList, hnum, hmodN, hea_nat, hall, a, st', st1, st0]
  have hwrite' : gs.mem.canWrite (BitVec.ofNat 64 a) 8 = true := by rwa [← hea_bv]
  let val64 := gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.str .X64 (.gpr (BitVec.ofNat 5 s.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 8)))) gs =
      (gs.setMem (gs.mem.write64 (BitVec.ofNat 64 a) val64)).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execStr, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.writeSized,
          hea_bv, a, hwrite', val64]
  refine ⟨_, st', decode_str64 s b n, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  exact agreeState_setMem hA _ _ (fun addr haddr => write64_eq_store hA hfit val64 _ (hA.gpr s) haddr) _ _ hnext hpc

theorem decode_ldr32 (d b : Fin 31) (n : Fin 4096) :
    Arm64.decode (encodeLdr32 d b n) =
      some (.ldr .W32 .W32 false (.gpr (BitVec.ofNat 5 d.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 4)))) := by
  have hd : d.val < 2 ^ 5 := by omega
  have hb : b.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := n.isLt
  have hf : encodeLdr32 d b n &&& 0xffc00000#32 = 0xb9400000#32 &&& 0xffc00000#32 := by
    have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hn (by decide)
    have h2 : (BitVec.ofNat 32 b.val <<< 5) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hb (by decide)
    have h3 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hd (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeLdr32; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_ldstImm hf (by decide) ⟨by decide, by decide⟩ (by decide)]
  have ex_d : (encodeLdr32 d b n).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeLdr32; simp only [extract_or]
    have h0 : (0xb9400000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_b : (encodeLdr32 d b n).extractLsb' 5 5 = BitVec.ofNat 5 b.val := by
    unfold encodeLdr32; simp only [extract_or]
    have h0 : (0xb9400000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 b.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_n : (encodeLdr32 d b n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeLdr32; simp only [extract_or]
    have h0 : (0xb9400000#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 10 12 = 0#12 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_sz : (encodeLdr32 d b n).extractLsb' 30 2 = 2#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeLdr32 d b n).extractLsb' 22 2 = 1#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hshift : (BitVec.ofNat 12 n.val).zeroExtend 64 <<< 2 = BitVec.ofNat 64 (n.val * 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have := n.isLt; omega
  simp only [ex_d, ex_b, ex_n, ex_sz, ex_opc, fromZRBits_fin31, fromSPBits_fin31, Arm64.mkLoadStoreInst, BitVec.toNat_ofNat]
  rw [hshift]

theorem agree_ldr32 (d b : Fin 31) (n : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (n.val * 4 : Int))
    (hfit : st.reg (armSlot b.val) + n.val * 4 + 4 ≤ Ode.M64)
    (hread : gs.mem.canRead (gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 4)) 4 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeLdr32 d b n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectLdr32, bindLdrb d b numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hnlt : n.val * 4 < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  have hmodN : ((n.val * 4 : Int) % (Ode.M64 : Int)).toNat = n.val * 4 := by unfold Ode.M64; have := n.isLt; omega
  have hea_nat : (st.reg (armSlot b.val) + n.val * 4) % Ode.M64 = st.reg (armSlot b.val) + n.val * 4 :=
    Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 4) =
      BitVec.ofNat 64 (st.reg (armSlot b.val) + n.val * 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.gpr b]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt (by omega)]
  let a := st.reg (armSlot b.val) + n.val * 4
  let val := Ode.load st.mem a 4 % 2 ^ 32
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) val
  let st' : Ode.State := Ode.noted (bindLdrb d b numStr) st0 (.set (.name "D") (.call "low32" [.call "mem32" [.name "B", .name "N"]])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectLdr32, bindLdrb d b numStr, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.read a 4 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectLdr32, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize, Ode.prim,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindLdrb, List.lookup, regIndex_armRegName,
          Ode.sumList, hnum, hmodN, hea_nat, hall, a, val, st', st1, st0]
  have hread' : gs.mem.canRead (BitVec.ofNat 64 a) 4 = true := by rwa [← hea_bv]
  have hv : ((((gs.mem.read32 (BitVec.ofNat 64 a)).zeroExtend 64).truncate 32).zeroExtend 64).toNat = val := by
    have hr := read32_eq_load hA hfit
    have hlt := (gs.mem.read32 (BitVec.ofNat 64 a)).isLt
    simp only [BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (show (gs.mem.read32 (BitVec.ofNat 64 a)).toNat < 2 ^ 64 by omega), hr,
        Nat.mod_eq_of_lt (show Ode.load st.mem a 4 % 2 ^ 32 < 2 ^ 64 by omega)]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.ldr .W32 .W32 false (.gpr (BitVec.ofNat 5 d.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 4)))) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) ((((gs.mem.read32 (BitVec.ofNat 64 a)).zeroExtend 64).truncate 32).zeroExtend 64)).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execLdr, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized,
          Arm64.State.writeReg, hea_bv, a, hread']
  refine ⟨_, st', decode_ldr32 d b n, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]; exact agreeState_writeGpr hA d _ val hv _ _ hnext hpc

theorem decode_str32 (s b : Fin 31) (n : Fin 4096) :
    Arm64.decode (encodeStr32 s b n) =
      some (.str .W32 (.gpr (BitVec.ofNat 5 s.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 4)))) := by
  have hs : s.val < 2 ^ 5 := by omega
  have hb : b.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := n.isLt
  have hf : encodeStr32 s b n &&& 0xffc00000#32 = 0xb9000000#32 &&& 0xffc00000#32 := by
    have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hn (by decide)
    have h2 : (BitVec.ofNat 32 b.val <<< 5) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hb (by decide)
    have h3 : (BitVec.ofNat 32 s.val <<< 0) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hs (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeStr32; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_ldstImm hf (by decide) ⟨by decide, by decide⟩ (by decide)]
  have ex_s : (encodeStr32 s b n).extractLsb' 0 5 = BitVec.ofNat 5 s.val := by
    unfold encodeStr32; simp only [extract_or]
    have h0 : (0xb9000000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_b : (encodeStr32 s b n).extractLsb' 5 5 = BitVec.ofNat 5 b.val := by
    unfold encodeStr32; simp only [extract_or]
    have h0 : (0xb9000000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 b.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hs (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_n : (encodeStr32 s b n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeStr32; simp only [extract_or]
    have h0 : (0xb9000000#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 10 12 = 0#12 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hs (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_sz : (encodeStr32 s b n).extractLsb' 30 2 = 2#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeStr32 s b n).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hshift : (BitVec.ofNat 12 n.val).zeroExtend 64 <<< 2 = BitVec.ofNat 64 (n.val * 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have := n.isLt; omega
  simp only [ex_s, ex_b, ex_n, ex_sz, ex_opc, fromZRBits_fin31, fromSPBits_fin31, Arm64.mkLoadStoreInst, BitVec.toNat_ofNat]
  rw [hshift]

theorem agree_str32 (s b : Fin 31) (n : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (n.val * 4 : Int))
    (hfit : st.reg (armSlot b.val) + n.val * 4 + 4 ≤ Ode.M64)
    (hwrite : gs.mem.canWrite (gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 4)) 4 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeStr32 s b n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectStr32, bindStrb s b numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hnlt : n.val * 4 < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  have hmodN : ((n.val * 4 : Int) % (Ode.M64 : Int)).toNat = n.val * 4 := by unfold Ode.M64; have := n.isLt; omega
  have hea_nat : (st.reg (armSlot b.val) + n.val * 4) % Ode.M64 = st.reg (armSlot b.val) + n.val * 4 :=
    Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 4) =
      BitVec.ofNat 64 (st.reg (armSlot b.val) + n.val * 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.gpr b]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt (by omega)]
  let a := st.reg (armSlot b.val) + n.val * 4
  let val32Nat := st.reg (armSlot s.val) % 2 ^ 32
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := { st0 with mem := Ode.store st.mem a val32Nat 4 }
  let st' : Ode.State := Ode.noted (bindStrb s b numStr) st0 (.set (.call "mem32" [.name "B", .name "N"]) (.call "low32" [.name "S"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectStr32, bindStrb s b numStr, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.write a 4 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectStr32, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize, Ode.prim,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindStrb, List.lookup, regIndex_armRegName,
          Ode.sumList, hnum, hmodN, hea_nat, hall, a, val32Nat, st', st1, st0]
  have hwrite' : gs.mem.canWrite (BitVec.ofNat 64 a) 4 = true := by rwa [← hea_bv]
  let val32 := (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))).truncate 32
  have hv32 : val32.toNat = val32Nat := by simp [val32, val32Nat, BitVec.toNat_setWidth, hA.gpr s]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.str .W32 (.gpr (BitVec.ofNat 5 s.val)) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 4)))) gs =
      (gs.setMem (gs.mem.write32 (BitVec.ofNat 64 a) val32)).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execStr, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.writeSized,
          hea_bv, a, hwrite', val32]
  refine ⟨_, st', decode_str32 s b n, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  exact agreeState_setMem hA _ _ (fun addr haddr => write32_eq_store hA hfit val32 val32Nat hv32 haddr) _ _ hnext hpc

theorem decode_str64_sp (s : Fin 31) (n : Fin 4096) :
    Arm64.decode (encodeStr64Sp s n) =
      some (.str .X64 (.gpr (BitVec.ofNat 5 s.val)) (.Offset .sp (BitVec.ofNat 64 (n.val * 8)))) := by
  have hs : s.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := n.isLt
  have hf : encodeStr64Sp s n &&& 0xffc003e0#32 = 0xf90003e0#32 &&& 0xffc003e0#32 := by
    have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc003e0#32 = 0#32 := field_and_eq_zero hn (by decide)
    have h2 : (BitVec.ofNat 32 s.val <<< 0) &&& 0xffc003e0#32 = 0#32 := field_and_eq_zero hs (by decide)
    simp only [BitVec.shiftLeft_zero] at h2
    unfold encodeStr64Sp; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]
  rw [decode_at_ldstImm hf (by decide) ⟨by decide, by decide⟩ (by decide)]
  have ex_s : (encodeStr64Sp s n).extractLsb' 0 5 = BitVec.ofNat 5 s.val := by
    unfold encodeStr64Sp; simp only [extract_or]
    have h0 : (0xf90003e0#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_n : (encodeStr64Sp s n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeStr64Sp; simp only [extract_or]
    have h0 : (0xf90003e0#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hs (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_b : (encodeStr64Sp s n).extractLsb' 5 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_sz : (encodeStr64Sp s n).extractLsb' 30 2 = 3#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeStr64Sp s n).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hshift : (BitVec.ofNat 12 n.val).zeroExtend 64 <<< 3 = BitVec.ofNat 64 (n.val * 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have := n.isLt; omega
  simp only [ex_s, ex_b, ex_n, ex_sz, ex_opc, fromZRBits_fin31, Arm64.mkLoadStoreInst, BitVec.toNat_ofNat]
  rw [hshift]; rfl

theorem agree_str64_sp_fault (s : Fin 31) (n : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (n.val * 8 : Int))
    (hmis : st.reg Ode.RSP % 16 ≠ 0) :
    ∃ ginst,
      Arm64.decode (encodeStr64Sp s n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectStr64Sp, bindStr64Sp s numStr, next⟩ u st = none ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).status = .Exception "SP alignment fault" := by
  have hsp : gs.spAligned = false := by rw [spAligned_iff hA]; exact decide_eq_false hmis
  refine ⟨_, decode_str64_sp s n, ?_, ?_⟩
  · simp [Ode.exec, Ode.execAll, effectStr64Sp, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize,
          Ode.prim, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindStr64Sp, List.lookup,
          regIndex_armRegName, regIndex_sp, hnum, hmis]
  · simp [Arm64.execInstWithSvc, Arm64.execStr, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.State.setStatus, hsp]

theorem agree_str64_sp (s : Fin 31) (n : Fin 4096) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (n.val * 8 : Int))
    (hal : st.reg Ode.RSP % 16 = 0)
    (hfit : st.reg Ode.RSP + n.val * 8 + 8 ≤ Ode.M64)
    (hwrite : gs.mem.canWrite (gs.sp + BitVec.ofNat 64 (n.val * 8)) 8 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeStr64Sp s n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectStr64Sp, bindStr64Sp s numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hsp : gs.spAligned = true := by rw [spAligned_iff hA]; exact decide_eq_true hal
  have hnlt : n.val * 8 < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  have hmodN : ((n.val * 8 : Int) % (Ode.M64 : Int)).toNat = n.val * 8 := by unfold Ode.M64; have := n.isLt; omega
  have hea_nat : (st.reg Ode.RSP + n.val * 8) % Ode.M64 = st.reg Ode.RSP + n.val * 8 :=
    Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.sp + BitVec.ofNat 64 (n.val * 8) = BitVec.ofNat 64 (st.reg Ode.RSP + n.val * 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.sp]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt (by omega)]
  let a := st.reg Ode.RSP + n.val * 8
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := { st0 with mem := Ode.store st.mem a (st.reg (armSlot s.val)) 8 }
  let st' : Ode.State := Ode.noted (bindStr64Sp s numStr) st0 (.set (.call "mem64" [.call "on16" [.name "sp"], .name "N"]) (.name "S")) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectStr64Sp, bindStr64Sp s numStr, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.write a 8 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectStr64Sp, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.memSize, Ode.prim,
          Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindStr64Sp, List.lookup, regIndex_armRegName, regIndex_sp,
          Ode.sumList, hnum, hmodN, hal, hea_nat, hall, a, st', st1, st0]
  have hwrite' : gs.mem.canWrite (BitVec.ofNat 64 a) 8 = true := by rwa [← hea_bv]
  let val64 := gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.str .X64 (.gpr (BitVec.ofNat 5 s.val)) (.Offset .sp (BitVec.ofNat 64 (n.val * 8)))) gs =
      (gs.setMem (gs.mem.write64 (BitVec.ofNat 64 a) val64)).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execStr, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.State.readReg64, Arm64.MemWidth.bytes,
          Arm64.Memory.writeSized, hsp, hea_bv, a, hwrite', val64]
  refine ⟨_, st', decode_str64_sp s n, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  exact agreeState_setMem hA _ _ (fun addr haddr => write64_eq_store hA hfit val64 _ (hA.gpr s) haddr) _ _ hnext hpc

/-! ## Rows 29 & 30: `bl` (`call I link x30`) and `ret` (`return x30`) -/

def encodeBl (imm26 : BitVec 26) : BitVec 32 := 0x94000000#32 ||| BitVec.ofNat 32 imm26.toNat
def encodeRet : BitVec 32 := 0xd65f03c0#32

def effectBl : List Ode.Stmt := [.callLink (.name "I") "x30"]
def effectRet : List Ode.Stmt := [.retLink "x30"]

theorem encodeBl_fixed (imm26 : BitVec 26) :
    encodeBl imm26 &&& 0xfc000000#32 = 0x94000000#32 &&& 0xfc000000#32 := by
  have hi : imm26.toNat < 2 ^ 26 := imm26.isLt
  have h1 : (BitVec.ofNat 32 imm26.toNat <<< 0) &&& 0xfc000000#32 = 0#32 := field_and_eq_zero hi (by decide)
  simp only [BitVec.shiftLeft_zero] at h1
  unfold encodeBl; simp only [BitVec.and_or_distrib_right, h1, BitVec.or_zero]

theorem decode_bl (imm26 : BitVec 26) :
    Arm64.decode (encodeBl imm26) = some (.bl ((imm26.signExtend 64) <<< 2)) := by
  have hf := encodeBl_fixed imm26
  have ex_i : (encodeBl imm26).extractLsb' 0 26 = imm26 := by
    unfold encodeBl; simp only [extract_or]
    have h0 : (0x94000000#32).extractLsb' 0 26 = 0#26 := by decide
    have h1 : (BitVec.ofNat 32 imm26.toNat <<< 0).extractLsb' 0 26 = BitVec.ofNat 26 imm26.toNat := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h1; rw [h0, h1]; simp
  have h31 : (encodeBl imm26).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide), h31, ex_i,
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
             mask_of_fixed hf (m := 0x7c000000#32) (by decide),
             Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_bl (imm26 : BitVec 26) (prog callee : Ode.Program) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64)
    (htarget : callee.base = (gs.pc + ((imm26.signExtend 64) <<< 2)).toNat) :
    let instr : Ode.Instr := ⟨effectBl, [("I", callee.name)], next⟩
    ∃ ginst,
      Arm64.decode (encodeBl imm26) = some ginst ∧
      Ode.callTarget instr = some callee.name ∧
      AgreeState (Ode.afterCall prog callee instr st) (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  intro instr
  have hidx30 : Ode.regIndex "x30" = some (armSlot 30) := by decide
  have hlink : Ode.callLink instr = some (armSlot 30) := by simp [instr, Ode.callLink, effectBl, hidx30]
  have htgt : Ode.callTarget instr = some callee.name := by simp [instr, Ode.callTarget, effectBl, List.lookup, hidx30]
  refine ⟨.bl ((imm26.signExtend 64) <<< 2), decode_bl imm26, htgt, ?_, rfl⟩
  rw [Ode.afterCall_link hlink]
  refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    simp only [Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.writeReg64, Arm64.State.readReg64,
               Arm64.RegFile.read, Arm64.RegFile.write, toNat_ofNat5_ne31, Bool.false_eq_true, ↓reduceIte]
    by_cases hk : k = ⟨30, by decide⟩
    · subst hk
      change (if (30#5 : BitVec 5) = 30#5 then gs.pc + 4#64 else gs.regs.regs 30#5).toNat = (prog.base + next) % Ode.M64
      simp only [↓reduceIte, BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
      have : 4 % 2 ^ 64 = 4 := by decide
      unfold Ode.M64 at hpc ⊢; rw [this, Nat.mod_eq_of_lt hpc]
    · have hne5 : BitVec.ofNat 5 k.val ≠ 30#5 := fun e => hk (ofNat5_inj (a := k) (b := ⟨30, by decide⟩) e)
      have hnes : armSlot k.val ≠ armSlot 30 := fun e => hk (armSlot_inj k ⟨30, by decide⟩ e)
      simp only [hnes, ↓reduceIte]
      change (if BitVec.ofNat 5 k.val = 30#5 then gs.pc + 4#64 else gs.regs.regs (BitVec.ofNat 5 k.val)).toNat = st.reg (armSlot k.val)
      simp only [hne5, ↓reduceIte]
      have hgk := hA.gpr k
      simpa [Arm64.State.readReg64, Arm64.RegFile.read, toNat_ofNat5_ne31] using hgk
  · simpa [Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.writeReg64, Arm64.Reg.lr,
           (armSlot_ne_rsp ⟨30, by decide⟩).symm] using hA.sp
  · intro v j; simpa [Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.writeReg64, Arm64.Reg.lr, Arm64.State.readVReg128] using hA.vec v j
  · intro a ha; simpa [Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.writeReg64, Arm64.Reg.lr] using hA.mem a ha
  · simp [Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.writeReg64, htarget]
  · simpa [Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.writeReg64, Arm64.Reg.lr] using hA.zf
  · simpa [Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.writeReg64, Arm64.Reg.lr] using hA.cf

theorem decode_ret : Arm64.decode encodeRet = some (.ret (.gpr 30#5)) := by decide

theorem agree_ret (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) :
    ∃ ginst st',
      Arm64.decode encodeRet = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectRet, [], next⟩ u st = some (.returned st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st' : Ode.State := { st0 with rip := st.reg (armSlot 30) }
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectRet, [], next⟩ u st = some (.returned st') := by
    have hidx : Ode.regIndex "x30" = some (armSlot 30) := by decide
    simp [Ode.exec, Ode.execAll, effectRet, hidx, st', st0]
  refine ⟨.ret (.gpr 30#5), st', decode_ret, hexec, ?_, rfl⟩
  refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.readReg64] using hA.gpr k
  · simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC] using hA.sp
  · intro v j; simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.readVReg128] using hA.vec v j
  · intro a ha; simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC] using hA.mem a ha
  · simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC] using hA.gpr ⟨30, by decide⟩
  · simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC] using hA.zf
  · simpa [st', st0, Arm64.execInstWithSvc, Arm64.State.setPC] using hA.cf

/-! ## Shared helpers for rows 31–36 (remaining NEON vector operations) -/

theorem agreeState_writeVec {prog : Ode.Program} {st : Ode.State} {gs : Arm64.State} {next : Nat}
    (hA : AgreeState st gs) (x : Fin 32) (v : BitVec 128) (lanes : List Nat) (u0 : Nat)
    (hlanes : ∀ j : Fin 4, (v.extractLsb' (32 * j.val) 32).toNat = lanes.getD j.val 0)
    (bind : Ode.Bind) (stmt : Ode.Stmt)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
    let st1 : Ode.State := Ode.setVec st0 x.val lanes u0
    let st' : Ode.State := Ode.noted bind st0 stmt st1
    AgreeState st' ((gs.writeVReg128 (BitVec.ofNat 5 x.val) v).advancePC) := by
  intro st0 st1 st'
  refine ⟨hA.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Arm64.State.readReg64,
                    Ode.setVec, Ode.noted] using hA.gpr k
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.sp
  · intro vec j
    simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.readVReg128, Arm64.State.writeVReg128,
               Arm64.VRegFile.read, Arm64.VRegFile.write, Ode.setVec, Ode.noted]
    by_cases hvx : vec = x
    · subst hvx
      simp only [↓reduceIte, j.isLt]
      exact hlanes j
    · have hne5 : BitVec.ofNat 5 vec.val ≠ BitVec.ofNat 5 x.val := fun e => hvx (ofNat5_inj32 e)
      have hnev : vec.val ≠ x.val := fun e => hvx (Fin.ext e)
      simp only [hne5, hnev, ↓reduceIte]
      exact hA.vec vec j
  · intro a ha; simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.mem a ha
  · simp only [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted,
               BitVec.toNat_add, BitVec.toNat_ofNat, hA.pc, hnext]
    have : 4 % 2 ^ 64 = 4 := by decide
    unfold Ode.M64 at hpc; rw [this, Nat.mod_eq_of_lt hpc]
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.zf
  · simpa [st', st1, st0, Arm64.State.advancePC, Arm64.State.writeVReg128, Ode.setVec, Ode.noted] using hA.cf

theorem mask32_getLsbD (i : Nat) :
    (((1#128 <<< 32) - 1#128 : BitVec 128)).getLsbD i = decide (i < 32) := by
  have hm : ((1#128 <<< 32) - 1#128 : BitVec 128) = BitVec.ofNat 128 (2 ^ 32 - 1) := by decide
  rw [hm, BitVec.getLsbD_ofNat]
  by_cases hi : i < 128
  · simp only [hi, decide_true, Bool.true_and, Nat.testBit_two_pow_sub_one]
  · simp [hi, show ¬(i < 32) by omega]

theorem lane_pack4_extract (a0 a1 a2 a3 : BitVec 128) :
    let m : BitVec 128 := (1#128 <<< 32) - 1#128
    let v : BitVec 128 := (((0#128 ||| (a0 &&& m) <<< 0) ||| (a1 &&& m) <<< 32) ||| (a2 &&& m) <<< 64) ||| (a3 &&& m) <<< 96
    v.extractLsb' 0 32 = a0.truncate 32 ∧
    v.extractLsb' 32 32 = a1.truncate 32 ∧
    v.extractLsb' 64 32 = a2.truncate 32 ∧
    v.extractLsb' 96 32 = a3.truncate 32 := by
  intro m v
  have hm : ∀ k, m.getLsbD k = decide (k < 32) := mask32_getLsbD
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [v, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
               BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero, hm, hi,
               Nat.zero_add, Nat.sub_zero, decide_true, Bool.true_and, Bool.and_true, Bool.false_or,
               show i < 128 by omega, show ¬(i < 0) by omega, show i < 64 by omega, show i < 96 by omega,
               decide_false, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [v, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
               BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero, hm, hi,
               Nat.sub_zero, decide_true, Bool.true_and, Bool.and_true, Bool.false_or,
               show 32 + i < 128 by omega, show ¬(32 + i < 32) by omega, show 32 + i < 64 by omega,
               show 32 + i < 96 by omega, show 32 + i - 32 = i by omega,
               decide_false, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [v, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
               BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero, hm, hi,
               Nat.sub_zero, decide_true, Bool.true_and, Bool.and_true, Bool.false_or,
               show 64 + i < 128 by omega, show ¬(64 + i < 32) by omega, show ¬(64 + i < 64) by omega,
               show 64 + i < 96 by omega, show ¬(64 + i - 32 < 32) by omega, show 64 + i - 64 = i by omega,
               decide_false, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [v, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
               BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero, hm, hi,
               Nat.sub_zero, decide_true, Bool.true_and, Bool.and_true, Bool.false_or,
               show 96 + i < 128 by omega, show ¬(96 + i < 32) by omega, show ¬(96 + i < 64) by omega,
               show ¬(96 + i < 96) by omega, show ¬(96 + i - 32 < 32) by omega, show ¬(96 + i - 64 < 32) by omega,
               show 96 + i - 96 = i by omega,
               decide_false, Bool.not_false, Bool.and_false, Bool.or_false]

theorem lane_slice_toNat (v : BitVec 128) (j : Fin 4) :
    (((v >>> (j.val * 32)) &&& ((1#128 <<< 32) - 1#128)).toNat) = (v.extractLsb' (32 * j.val) 32).toNat := by
  have heq : (v >>> (j.val * 32)) &&& ((1#128 <<< 32) - 1#128) = (v.extractLsb' (32 * j.val) 32).zeroExtend 128 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, mask32_getLsbD, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
    by_cases h32 : i < 32
    · simp [h32, hi, Nat.mul_comm, Nat.add_comm]
    · simp [h32]
  rw [heq, BitVec.toNat_setWidth]
  have := (v.extractLsb' (32 * j.val) 32).isLt
  exact Nat.mod_eq_of_lt (by omega)

theorem zipSimdLanes_4s_unfold (vn vm : BitVec 128) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    let m : BitVec 128 := (1#128 <<< 32) - 1#128
    let out (k : Nat) := f ((vn >>> (k * 32)) &&& m) ((vm >>> (k * 32)) &&& m) &&& m
    Arm64.zipSimdLanes true 32 vn vm f =
      (((0#128 ||| out 0 <<< 0) ||| out 1 <<< 32) ||| out 2 <<< 64) ||| out 3 <<< 96 := by
  simp [Arm64.zipSimdLanes, List.range', List.foldl]

theorem mapSimdLanes_4s_unfold (vn : BitVec 128) (f : BitVec 128 → BitVec 128) :
    let m : BitVec 128 := (1#128 <<< 32) - 1#128
    let out (k : Nat) := f ((vn >>> (k * 32)) &&& m) &&& m
    Arm64.mapSimdLanes true 32 vn f =
      (((0#128 ||| out 0 <<< 0) ||| out 1 <<< 32) ||| out 2 <<< 64) ||| out 3 <<< 96 := by
  simp [Arm64.mapSimdLanes, List.range', List.foldl]

/-! ## Row 31: `orr_v` (`orr vX.16b, vY.16b, vZ.16b | .orr X Y Z | X = each32(or32, Y, Z)`) -/

def encodeOrrV (x y z : Fin 32) : BitVec 32 :=
  0x4ea01c00#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

def effectOrrV : List Ode.Stmt :=
  [.vset (.name "X") (.call "each32" [.name "or32", .name "Y", .name "Z"])]

theorem decode_orr_v (x y z : Fin 32) :
    Arm64.decode (encodeOrrV x y z) =
      some (.simdThreeSame true false 2#2 (BitVec.ofNat 5 z.val) 3#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) := by
  have hx : x.val < 2 ^ 5 := x.isLt; have hy : y.val < 2 ^ 5 := y.isLt; have hz : z.val < 2 ^ 5 := z.isLt
  have hf : encodeOrrV x y z &&& 0xffe0fc00#32 = 0x4ea01c00#32 &&& 0xffe0fc00#32 := by
    have h1 : (BitVec.ofNat 32 z.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hz (by decide)
    have h2 : (BitVec.ofNat 32 y.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hy (by decide)
    have h3 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeOrrV; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_simdThreeSame hf (by decide) (by decide) ⟨by decide, by decide⟩]
  have ex_x : (encodeOrrV x y z).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeOrrV; simp only [extract_or]
    have h0 : (0x4ea01c00#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_y : (encodeOrrV x y z).extractLsb' 5 5 = BitVec.ofNat 5 y.val := by
    unfold encodeOrrV; simp only [extract_or]
    have h0 : (0x4ea01c00#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 y.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_z : (encodeOrrV x y z).extractLsb' 16 5 = BitVec.ofNat 5 z.val := by
    unfold encodeOrrV; simp only [extract_or]
    have h0 : (0x4ea01c00#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 z.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have hq : (encodeOrrV x y z).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hu : (encodeOrrV x y z).getLsbD 29 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hsz : (encodeOrrV x y z).extractLsb' 22 2 = 2#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hopc : (encodeOrrV x y z).extractLsb' 11 5 = 3#5 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [hq, hu, hsz, hopc, ex_x, ex_y, ex_z]

theorem agree_orr_v (x y z : Fin 32) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeOrrV x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectOrrV, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let lanes : List Nat := [st.vec y.val 0 ||| st.vec z.val 0, st.vec y.val 1 ||| st.vec z.val 1,
                           st.vec y.val 2 ||| st.vec z.val 2, st.vec y.val 3 ||| st.vec z.val 3]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "each32" [.name "or32", .name "Y", .name "Z"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectOrrV, bind, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectOrrV, Ode.execStmt, Ode.lanesOf, Ode.vecArg,
          hbx, hby, hbz, Ode.prim32, List.range, List.range.loop, List.mapM, List.mapM.loop, lanes, st', st1, st0]
  let vn := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vm := gs.readVReg128 (BitVec.ofNat 5 z.val)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdThreeSame true false 2#2 (BitVec.ofNat 5 z.val) 3#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) (vn ||| vm)).advancePC := by
    simp [Arm64.execInstWithSvc, vn, vm]
  refine ⟨_, st', decode_orr_v x y z, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  apply agreeState_writeVec hA x (vn ||| vm) lanes (u 0) ?_ _ _ hnext hpc
  intro j
  have hex : (vn ||| vm).extractLsb' (32 * j.val) 32 = vn.extractLsb' (32 * j.val) 32 ||| vm.extractLsb' (32 * j.val) 32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_or, hi]
  rw [hex, BitVec.toNat_or, hA.vec y j, hA.vec z j]
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

/-! ## Row 32: `add_4s` (`add vX.4s, vY.4s, vZ.4s | .add4s X Y Z | X = each32(add32, Y, Z)`) -/

def encodeAdd4s (x y z : Fin 32) : BitVec 32 :=
  0x4ea08400#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

def effectAdd4s : List Ode.Stmt :=
  [.vset (.name "X") (.call "each32" [.name "add32", .name "Y", .name "Z"])]

theorem decode_add_4s (x y z : Fin 32) :
    Arm64.decode (encodeAdd4s x y z) =
      some (.simdThreeSame true false 2#2 (BitVec.ofNat 5 z.val) 16#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) := by
  have hx : x.val < 2 ^ 5 := x.isLt; have hy : y.val < 2 ^ 5 := y.isLt; have hz : z.val < 2 ^ 5 := z.isLt
  have hf : encodeAdd4s x y z &&& 0xffe0fc00#32 = 0x4ea08400#32 &&& 0xffe0fc00#32 := by
    have h1 : (BitVec.ofNat 32 z.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hz (by decide)
    have h2 : (BitVec.ofNat 32 y.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hy (by decide)
    have h3 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeAdd4s; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_simdThreeSame hf (by decide) (by decide) ⟨by decide, by decide⟩]
  have ex_x : (encodeAdd4s x y z).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeAdd4s; simp only [extract_or]
    have h0 : (0x4ea08400#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_y : (encodeAdd4s x y z).extractLsb' 5 5 = BitVec.ofNat 5 y.val := by
    unfold encodeAdd4s; simp only [extract_or]
    have h0 : (0x4ea08400#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 y.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_z : (encodeAdd4s x y z).extractLsb' 16 5 = BitVec.ofNat 5 z.val := by
    unfold encodeAdd4s; simp only [extract_or]
    have h0 : (0x4ea08400#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 z.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have hq : (encodeAdd4s x y z).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hu : (encodeAdd4s x y z).getLsbD 29 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hsz : (encodeAdd4s x y z).extractLsb' 22 2 = 2#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hopc : (encodeAdd4s x y z).extractLsb' 11 5 = 16#5 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [hq, hu, hsz, hopc, ex_x, ex_y, ex_z]

theorem agree_add_4s (x y z : Fin 32) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeAdd4s x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectAdd4s, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let lanes : List Nat := [(st.vec y.val 0 + st.vec z.val 0) % Ode.W32, (st.vec y.val 1 + st.vec z.val 1) % Ode.W32,
                           (st.vec y.val 2 + st.vec z.val 2) % Ode.W32, (st.vec y.val 3 + st.vec z.val 3) % Ode.W32]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "each32" [.name "add32", .name "Y", .name "Z"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectAdd4s, bind, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectAdd4s, Ode.execStmt, Ode.lanesOf, Ode.vecArg,
          hbx, hby, hbz, Ode.prim32, List.range, List.range.loop, List.mapM, List.mapM.loop, lanes, st', st1, st0]
  let vn := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vm := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let res := Arm64.zipSimdLanes true 32 vn vm (fun a b => a + b)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdThreeSame true false 2#2 (BitVec.ofNat 5 z.val) 16#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp [Arm64.execInstWithSvc, vn, vm, res]
  refine ⟨_, st', decode_add_4s x y z, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  apply agreeState_writeVec hA x res lanes (u 0) ?_ _ _ hnext hpc
  have hunf := zipSimdLanes_4s_unfold vn vm (fun a b => a + b)
  have hpack := lane_pack4_extract
    (((vn >>> (0 * 32)) &&& ((1#128 <<< 32) - 1#128)) + ((vm >>> (0 * 32)) &&& ((1#128 <<< 32) - 1#128)))
    (((vn >>> (1 * 32)) &&& ((1#128 <<< 32) - 1#128)) + ((vm >>> (1 * 32)) &&& ((1#128 <<< 32) - 1#128)))
    (((vn >>> (2 * 32)) &&& ((1#128 <<< 32) - 1#128)) + ((vm >>> (2 * 32)) &&& ((1#128 <<< 32) - 1#128)))
    (((vn >>> (3 * 32)) &&& ((1#128 <<< 32) - 1#128)) + ((vm >>> (3 * 32)) &&& ((1#128 <<< 32) - 1#128)))
  have hlane : ∀ j : Fin 4,
      ((((vn >>> (j.val * 32)) &&& ((1#128 <<< 32) - 1#128)) +
        ((vm >>> (j.val * 32)) &&& ((1#128 <<< 32) - 1#128))).truncate 32).toNat =
      (st.vec y.val j.val + st.vec z.val j.val) % Ode.W32 := by
    intro j
    have hyj : ((vn >>> (j.val * 32)) &&& ((1#128 <<< 32) - 1#128)).toNat = st.vec y.val j.val := by
      rw [lane_slice_toNat vn j]; exact hA.vec y j
    have hzj : ((vm >>> (j.val * 32)) &&& ((1#128 <<< 32) - 1#128)).toNat = st.vec z.val j.val := by
      rw [lane_slice_toNat vm j]; exact hA.vec z j
    have hyLt : st.vec y.val j.val < 2 ^ 32 := by rw [← hA.vec y j]; exact (vn.extractLsb' (32 * j.val) 32).isLt
    have hzLt : st.vec z.val j.val < 2 ^ 32 := by rw [← hA.vec z j]; exact (vm.extractLsb' (32 * j.val) 32).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, hyj, hzj]
    rw [Nat.mod_eq_of_lt (show st.vec y.val j.val + st.vec z.val j.val < 2 ^ 128 by omega)]
    rfl
  intro j
  change (res.extractLsb' (32 * j.val) 32).toNat = _
  rw [show res = _ from hunf]
  match j with
  | ⟨0, _⟩ => change ((_ : BitVec 128).extractLsb' 0 32).toNat = _; rw [hpack.1]; exact hlane ⟨0, by decide⟩
  | ⟨1, _⟩ => change ((_ : BitVec 128).extractLsb' 32 32).toNat = _; rw [hpack.2.1]; exact hlane ⟨1, by decide⟩
  | ⟨2, _⟩ => change ((_ : BitVec 128).extractLsb' 64 32).toNat = _; rw [hpack.2.2.1]; exact hlane ⟨2, by decide⟩
  | ⟨3, _⟩ => change ((_ : BitVec 128).extractLsb' 96 32).toNat = _; rw [hpack.2.2.2]; exact hlane ⟨3, by decide⟩

/-! ## Rows 33 & 34: `ushr_4s` (`each32(shr32, Y, I)`) and `shl_4s` (`each32(shl32, Y, I)`) -/

def guardsBeforeSimdImmShift : List (BitVec 32 × BitVec 32) :=
  guardsBeforeSimdThreeSame.take 59

theorem decode_at_simdImmShift {w base fixed : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hnop : ((base &&& fixed) == (0xd503201f#32 &&& fixed)) = false)
    (hskip : skipsAll base fixed guardsBeforeSimdImmShift = true)
    (hmatch : (0x9f800400#32 &&& fixed = 0x9f800400#32) ∧ (base &&& 0x9f800400#32 = 0x0f000400#32)) :
    Arm64.decode w =
      some (.simdImmShift (w.getLsbD 30) (w.getLsbD 29) (w.extractLsb' 19 4) (w.extractLsb' 16 3)
        (w.extractLsb' 11 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5)) := by
  have sk : ∀ m c, (m, c) ∈ guardsBeforeSimdImmShift → ((w &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hw hskip hm
  have hhit : w &&& 0x9f800400#32 = 0x0f000400#32 := by rw [mask_of_fixed hw hmatch.1, hmatch.2]
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
             hhit, beq_self_eq_true, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

def encodeUshr4s (x y : Fin 32) (i : Fin 32) : BitVec 32 :=
  0x6f200400#32 ||| (BitVec.ofNat 32 i.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

def encodeShl4s (x y : Fin 32) (i : Fin 32) : BitVec 32 :=
  0x4f205400#32 ||| (BitVec.ofNat 32 i.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

def effectUshr4s : List Ode.Stmt :=
  [.vset (.name "X") (.call "each32" [.name "shr32", .name "Y", .name "I"])]

def effectShl4s : List Ode.Stmt :=
  [.vset (.name "X") (.call "each32" [.name "shl32", .name "Y", .name "I"])]

theorem immhb_of_fin32 (i : Fin 32) :
    ((BitVec.ofNat 4 (4 + i.val / 8) ++ BitVec.ofNat 3 (i.val % 8)) : BitVec 7).toNat = 32 + i.val ∧
    (BitVec.ofNat 4 (4 + i.val / 8) == 0#4) = false ∧
    (BitVec.ofNat 4 (4 + i.val / 8)).getLsbD 3 = false := by
  have hi := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · rw [toNat_append_eq]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · apply beq_false_of_ne; intro h
    have ht := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at ht
    rw [Nat.mod_eq_of_lt (by omega)] at ht; omega
  · rw [BitVec.getLsbD_ofNat]; simp only [show (3 : Nat) < 4 by decide, decide_true, Bool.true_and]
    rw [Nat.testBit_eq_decide_div_mod_eq]; simp [show (4 + i.val / 8) / 2 ^ 3 = 0 by omega]

theorem extract_immh_immb_ushr : ∀ i : Fin 32,
    (0x6f200400#32 ||| (BitVec.ofNat 32 i.val <<< 16)).extractLsb' 19 4 = BitVec.ofNat 4 (4 + i.val / 8) ∧
    (0x6f200400#32 ||| (BitVec.ofNat 32 i.val <<< 16)).extractLsb' 16 3 = BitVec.ofNat 3 (i.val % 8) := by decide

theorem extract_immh_immb_shl : ∀ i : Fin 32,
    (0x4f205400#32 ||| (BitVec.ofNat 32 i.val <<< 16)).extractLsb' 19 4 = BitVec.ofNat 4 (4 + i.val / 8) ∧
    (0x4f205400#32 ||| (BitVec.ofNat 32 i.val <<< 16)).extractLsb' 16 3 = BitVec.ofNat 3 (i.val % 8) := by decide

theorem decode_ushr_4s (x y i : Fin 32) :
    Arm64.decode (encodeUshr4s x y i) =
      some (.simdImmShift true true (BitVec.ofNat 4 (4 + i.val / 8)) (BitVec.ofNat 3 (i.val % 8))
        0#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) := by
  have hx : x.val < 2 ^ 5 := x.isLt; have hy : y.val < 2 ^ 5 := y.isLt; have hi : i.val < 2 ^ 5 := i.isLt
  have hf : encodeUshr4s x y i &&& 0xffe0fc00#32 = 0x6f200400#32 &&& 0xffe0fc00#32 := by
    have h1 : (BitVec.ofNat 32 i.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hi (by decide)
    have h2 : (BitVec.ofNat 32 y.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hy (by decide)
    have h3 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeUshr4s; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_simdImmShift hf (by decide) (by decide) ⟨by decide, by decide⟩]
  have ex_x : (encodeUshr4s x y i).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeUshr4s; simp only [extract_or]
    have h0 : (0x6f200400#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 i.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_y : (encodeUshr4s x y i).extractLsb' 5 5 = BitVec.ofNat 5 y.val := by
    unfold encodeUshr4s; simp only [extract_or]
    have h0 : (0x6f200400#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 i.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 y.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_immh : (encodeUshr4s x y i).extractLsb' 19 4 = BitVec.ofNat 4 (4 + i.val / 8) := by
    unfold encodeUshr4s; rw [extract_or, extract_or]
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 19 4 = 0#4 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 19 4 = 0#4 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [(extract_immh_immb_ushr i).1, h2, h3]; simp
  have ex_immb : (encodeUshr4s x y i).extractLsb' 16 3 = BitVec.ofNat 3 (i.val % 8) := by
    unfold encodeUshr4s; rw [extract_or, extract_or]
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 16 3 = 0#3 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 16 3 = 0#3 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [(extract_immh_immb_ushr i).2, h2, h3]; simp
  have hq : (encodeUshr4s x y i).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hop : (encodeUshr4s x y i).getLsbD 29 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hopc : (encodeUshr4s x y i).extractLsb' 11 5 = 0#5 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [hq, hop, hopc, ex_x, ex_y, ex_immh, ex_immb]

theorem agree_ushr_4s (x y i : Fin 32) (numStr : String) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val)
    (hbi : bind.lookup "I" = some numStr) (hnum : Ode.readInt numStr = some ((32 - i.val : Nat) : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeUshr4s x y i) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectUshr4s, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hi := i.isLt
  have hmodI : (((32 - i.val : Nat) : Int) % (Ode.M64 : Int)).toNat = 32 - i.val := by unfold Ode.M64; omega
  let sh := 32 - i.val
  let lanes : List Nat := [st.vec y.val 0 >>> sh, st.vec y.val 1 >>> sh,
                           st.vec y.val 2 >>> sh, st.vec y.val 3 >>> sh]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "each32" [.name "shr32", .name "Y", .name "I"])) st1
  have hvecI : Ode.vecOf bind "I" = none := by simp [Ode.vecOf, Ode.isVectorLetter]
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectUshr4s, bind, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectUshr4s, Ode.execStmt, Ode.lanesOf, Ode.vecArg,
          hbx, hby, hvecI, hbi, Ode.value, Ode.isNumberLetter, hnum, hmodI, Ode.prim32,
          List.range, List.range.loop, List.mapM, List.mapM.loop, lanes, sh, st', st1, st0]
  have ⟨himmhb, hnz, _⟩ := immhb_of_fin32 i
  let vn := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let res := Arm64.mapSimdLanes true 32 vn (fun lane => lane >>> sh)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdImmShift true true (BitVec.ofNat 4 (4 + i.val / 8)) (BitVec.ofNat 3 (i.val % 8))
        0#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp [Arm64.execInstWithSvc, hnz, himmhb, show ¬(32 + i.val ≥ 64) by omega,
          show 32 + i.val ≥ 32 by omega, show 2 * 32 - (32 + i.val) = sh by omega, vn, res]
  refine ⟨_, st', decode_ushr_4s x y i, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  apply agreeState_writeVec hA x res lanes (u 0) ?_ _ _ hnext hpc
  have hunf := mapSimdLanes_4s_unfold vn (fun lane => lane >>> sh)
  have hpack := lane_pack4_extract
    (((vn >>> (0 * 32)) &&& ((1#128 <<< 32) - 1#128)) >>> sh)
    (((vn >>> (1 * 32)) &&& ((1#128 <<< 32) - 1#128)) >>> sh)
    (((vn >>> (2 * 32)) &&& ((1#128 <<< 32) - 1#128)) >>> sh)
    (((vn >>> (3 * 32)) &&& ((1#128 <<< 32) - 1#128)) >>> sh)
  have hlane : ∀ j : Fin 4,
      ((((vn >>> (j.val * 32)) &&& ((1#128 <<< 32) - 1#128)) >>> sh).truncate 32).toNat =
      st.vec y.val j.val >>> sh := by
    intro j
    have hyj : ((vn >>> (j.val * 32)) &&& ((1#128 <<< 32) - 1#128)).toNat = st.vec y.val j.val := by
      rw [lane_slice_toNat vn j]; exact hA.vec y j
    have hyLt : st.vec y.val j.val < 2 ^ 32 := by rw [← hA.vec y j]; exact (vn.extractLsb' (32 * j.val) 32).isLt
    have hlt : st.vec y.val j.val >>> sh < 2 ^ 32 := by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hyLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, hyj]
    exact Nat.mod_eq_of_lt hlt
  intro j
  change (res.extractLsb' (32 * j.val) 32).toNat = _
  rw [show res = _ from hunf]
  match j with
  | ⟨0, _⟩ => change ((_ : BitVec 128).extractLsb' 0 32).toNat = _; rw [hpack.1]; exact hlane ⟨0, by decide⟩
  | ⟨1, _⟩ => change ((_ : BitVec 128).extractLsb' 32 32).toNat = _; rw [hpack.2.1]; exact hlane ⟨1, by decide⟩
  | ⟨2, _⟩ => change ((_ : BitVec 128).extractLsb' 64 32).toNat = _; rw [hpack.2.2.1]; exact hlane ⟨2, by decide⟩
  | ⟨3, _⟩ => change ((_ : BitVec 128).extractLsb' 96 32).toNat = _; rw [hpack.2.2.2]; exact hlane ⟨3, by decide⟩

theorem decode_shl_4s (x y i : Fin 32) :
    Arm64.decode (encodeShl4s x y i) =
      some (.simdImmShift true false (BitVec.ofNat 4 (4 + i.val / 8)) (BitVec.ofNat 3 (i.val % 8))
        10#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) := by
  have hx : x.val < 2 ^ 5 := x.isLt; have hy : y.val < 2 ^ 5 := y.isLt; have hi : i.val < 2 ^ 5 := i.isLt
  have hf : encodeShl4s x y i &&& 0xffe0fc00#32 = 0x4f205400#32 &&& 0xffe0fc00#32 := by
    have h1 : (BitVec.ofNat 32 i.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hi (by decide)
    have h2 : (BitVec.ofNat 32 y.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hy (by decide)
    have h3 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeShl4s; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_simdImmShift hf (by decide) (by decide) ⟨by decide, by decide⟩]
  have ex_x : (encodeShl4s x y i).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeShl4s; simp only [extract_or]
    have h0 : (0x4f205400#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 i.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_y : (encodeShl4s x y i).extractLsb' 5 5 = BitVec.ofNat 5 y.val := by
    unfold encodeShl4s; simp only [extract_or]
    have h0 : (0x4f205400#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 i.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hi (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 y.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_immh : (encodeShl4s x y i).extractLsb' 19 4 = BitVec.ofNat 4 (4 + i.val / 8) := by
    unfold encodeShl4s; rw [extract_or, extract_or]
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 19 4 = 0#4 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 19 4 = 0#4 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [(extract_immh_immb_shl i).1, h2, h3]; simp
  have ex_immb : (encodeShl4s x y i).extractLsb' 16 3 = BitVec.ofNat 3 (i.val % 8) := by
    unfold encodeShl4s; rw [extract_or, extract_or]
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 16 3 = 0#3 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 16 3 = 0#3 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [(extract_immh_immb_shl i).2, h2, h3]; simp
  have hq : (encodeShl4s x y i).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hop : (encodeShl4s x y i).getLsbD 29 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hopc : (encodeShl4s x y i).extractLsb' 11 5 = 10#5 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [hq, hop, hopc, ex_x, ex_y, ex_immh, ex_immb]

theorem agree_shl_4s (x y i : Fin 32) (numStr : String) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val)
    (hbi : bind.lookup "I" = some numStr) (hnum : Ode.readInt numStr = some (i.val : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeShl4s x y i) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectShl4s, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hi := i.isLt
  have hmodI : ((i.val : Int) % (Ode.M64 : Int)).toNat = i.val := by unfold Ode.M64; omega
  let lanes : List Nat := [(st.vec y.val 0 <<< i.val) % Ode.W32, (st.vec y.val 1 <<< i.val) % Ode.W32,
                           (st.vec y.val 2 <<< i.val) % Ode.W32, (st.vec y.val 3 <<< i.val) % Ode.W32]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "each32" [.name "shl32", .name "Y", .name "I"])) st1
  have hvecI : Ode.vecOf bind "I" = none := by simp [Ode.vecOf, Ode.isVectorLetter]
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectShl4s, bind, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectShl4s, Ode.execStmt, Ode.lanesOf, Ode.vecArg,
          hbx, hby, hvecI, hbi, Ode.value, Ode.isNumberLetter, hnum, hmodI, Ode.prim32,
          List.range, List.range.loop, List.mapM, List.mapM.loop, lanes, st', st1, st0]
  have ⟨himmhb, hnz, _⟩ := immhb_of_fin32 i
  let vn := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let res := Arm64.mapSimdLanes true 32 vn (fun lane => lane <<< i.val)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdImmShift true false (BitVec.ofNat 4 (4 + i.val / 8)) (BitVec.ofNat 3 (i.val % 8))
        10#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp [Arm64.execInstWithSvc, hnz, himmhb, show ¬(32 + i.val ≥ 64) by omega,
          show 32 + i.val ≥ 32 by omega, show 32 + i.val - 32 = i.val by omega, vn, res]
  refine ⟨_, st', decode_shl_4s x y i, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  apply agreeState_writeVec hA x res lanes (u 0) ?_ _ _ hnext hpc
  have hunf := mapSimdLanes_4s_unfold vn (fun lane => lane <<< i.val)
  have hpack := lane_pack4_extract
    (((vn >>> (0 * 32)) &&& ((1#128 <<< 32) - 1#128)) <<< i.val)
    (((vn >>> (1 * 32)) &&& ((1#128 <<< 32) - 1#128)) <<< i.val)
    (((vn >>> (2 * 32)) &&& ((1#128 <<< 32) - 1#128)) <<< i.val)
    (((vn >>> (3 * 32)) &&& ((1#128 <<< 32) - 1#128)) <<< i.val)
  have hlane : ∀ j : Fin 4,
      ((((vn >>> (j.val * 32)) &&& ((1#128 <<< 32) - 1#128)) <<< i.val).truncate 32).toNat =
      (st.vec y.val j.val <<< i.val) % Ode.W32 := by
    intro j
    have hyj : ((vn >>> (j.val * 32)) &&& ((1#128 <<< 32) - 1#128)).toNat = st.vec y.val j.val := by
      rw [lane_slice_toNat vn j]; exact hA.vec y j
    have hyLt : st.vec y.val j.val < 2 ^ 32 := by rw [← hA.vec y j]; exact (vn.extractLsb' (32 * j.val) 32).isLt
    have hpow : 2 ^ i.val < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hi
    have hlt128 : st.vec y.val j.val <<< i.val < 2 ^ 128 := by
      rw [Nat.shiftLeft_eq]
      have : st.vec y.val j.val * 2 ^ i.val < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hyLt hpow
      omega
    simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, hyj]
    rw [Nat.mod_eq_of_lt hlt128]; rfl
  intro j
  change (res.extractLsb' (32 * j.val) 32).toNat = _
  rw [show res = _ from hunf]
  match j with
  | ⟨0, _⟩ => change ((_ : BitVec 128).extractLsb' 0 32).toNat = _; rw [hpack.1]; exact hlane ⟨0, by decide⟩
  | ⟨1, _⟩ => change ((_ : BitVec 128).extractLsb' 32 32).toNat = _; rw [hpack.2.1]; exact hlane ⟨1, by decide⟩
  | ⟨2, _⟩ => change ((_ : BitVec 128).extractLsb' 64 32).toNat = _; rw [hpack.2.2.1]; exact hlane ⟨2, by decide⟩
  | ⟨3, _⟩ => change ((_ : BitVec 128).extractLsb' 96 32).toNat = _; rw [hpack.2.2.2]; exact hlane ⟨3, by decide⟩

/-! ## Rows 35 & 36: `ld1_4s` (`X = mem128(B, 0)`) and `st1_4s` (`mem128(B, 0) = X`) -/

def guardsBeforeSimdLdSt1Multi : List (BitVec 32 × BitVec 32) :=
  guardsBeforeSimdThreeSame.take 50

theorem decode_at_simdLdSt1Multi {w base fixed : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hnop : ((base &&& fixed) == (0xd503201f#32 &&& fixed)) = false)
    (hskip : skipsAll base fixed guardsBeforeSimdLdSt1Multi = true)
    (hmatch : (0xbfbf0000#32 &&& fixed = 0xbfbf0000#32) ∧ (base &&& 0xbfbf0000#32 = 0x0c000000#32))
    (hopc : w.extractLsb' 12 4 = 7#4) :
    Arm64.decode w =
      some (.simdLdSt1Multi (w.getLsbD 22) (w.getLsbD 30) (w.extractLsb' 10 2) 1
        (Arm64.Reg.fromSPBits (w.extractLsb' 5 5)) (w.getLsbD 23) (w.extractLsb' 16 5) (w.extractLsb' 0 5)) := by
  have sk : ∀ m c, (m, c) ∈ guardsBeforeSimdLdSt1Multi → ((w &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hw hskip hm
  have hhit : w &&& 0xbfbf0000#32 = 0x0c000000#32 := by rw [mask_of_fixed hw hmatch.1, hmatch.2]
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
             hhit, hopc, beq_self_eq_true, Bool.true_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

def encodeLd1_4s (x : Fin 32) (b : Fin 31) : BitVec 32 :=
  0x4c407800#32 ||| (BitVec.ofNat 32 b.val <<< 5) ||| BitVec.ofNat 32 x.val

def encodeSt1_4s (x : Fin 32) (b : Fin 31) : BitVec 32 :=
  0x4c007800#32 ||| (BitVec.ofNat 32 b.val <<< 5) ||| BitVec.ofNat 32 x.val

def effectLd1_4s : List Ode.Stmt := [.vset (.name "X") (.call "mem128" [.name "B", .number 0])]
def effectSt1_4s : List Ode.Stmt := [.vset (.call "mem128" [.name "B", .number 0]) (.name "X")]

theorem read128_lane_eq_load {st : Ode.State} {gs : Arm64.State} (hA : AgreeState st gs)
    {a : Nat} (hfit : a + 16 ≤ Ode.M64) (j : Fin 4) :
    ((gs.mem.read128 (BitVec.ofNat 64 a)).extractLsb' (32 * j.val) 32).toNat =
      Ode.load st.mem (a + j.val * 4) 4 := by
  have hlo := read64_eq_load hA (a := a) (by omega)
  have hadd8 : BitVec.ofNat 64 a + 8#64 = BitVec.ofNat 64 (a + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    unfold Ode.M64 at hfit
    rw [Nat.mod_eq_of_lt (by omega), show 8 % 2 ^ 64 = 8 by decide, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hhi : (gs.mem.read64 (BitVec.ofNat 64 a + 8#64)).toNat = Ode.load st.mem (a + 8) 8 := by
    rw [hadd8]; exact read64_eq_load hA (a := a + 8) (by omega)
  have hload8 : ∀ b, Ode.load st.mem b 8 = Ode.load st.mem b 4 + 2 ^ 32 * Ode.load st.mem (b + 4) 4 := by
    intro b
    unfold Ode.load Ode.load Ode.load Ode.load Ode.load Ode.load Ode.load Ode.load Ode.load
    have e4 : b + 1 + 1 + 1 + 1 = b + 4 := by omega
    have e5 : b + 1 + 1 + 1 + 1 + 1 = b + 4 + 1 := by omega
    have e6 : b + 1 + 1 + 1 + 1 + 1 + 1 = b + 4 + 1 + 1 := by omega
    have e7 : b + 1 + 1 + 1 + 1 + 1 + 1 + 1 = b + 4 + 1 + 1 + 1 := by omega
    rw [e4, e5, e6, e7]; omega
  have hload4lt : ∀ b, Ode.load st.mem b 4 < 2 ^ 32 := by
    intro b
    unfold Ode.load Ode.load Ode.load Ode.load Ode.load
    have b0 := (st.mem b).isLt; have b1 := (st.mem (b + 1)).isLt
    have b2 := (st.mem (b + 1 + 1)).isLt; have b3 := (st.mem (b + 1 + 1 + 1)).isLt
    omega
  unfold Arm64.Memory.read128
  rw [BitVec.extractLsb'_toNat, toNat_append_eq, hhi, hlo, hload8 a, hload8 (a + 8)]
  have l0 := hload4lt a; have l1 := hload4lt (a + 4); have l2 := hload4lt (a + 8); have l3 := hload4lt (a + 12)
  have h12 : a + 8 + 4 = a + 12 := by omega
  rw [h12]
  match j with
  | ⟨0, _⟩ => simp only [Nat.mul_zero, Nat.zero_mul, Nat.shiftRight_zero, Nat.add_zero]; omega
  | ⟨1, _⟩ => simp only [Nat.mul_one, Nat.one_mul, Nat.shiftRight_eq_div_pow]; omega
  | ⟨2, _⟩ =>
    simp only [Nat.shiftRight_eq_div_pow, show 32 * 2 = 64 by decide, show 2 * 4 = 8 by decide]
    omega
  | ⟨3, _⟩ =>
    simp only [Nat.shiftRight_eq_div_pow, show 32 * 3 = 96 by decide, show 3 * 4 = 12 by decide,
               show (2 : Nat) ^ 96 = 2 ^ 64 * 2 ^ 32 by decide]
    omega

theorem decode_ld1_4s (x : Fin 32) (b : Fin 31) :
    Arm64.decode (encodeLd1_4s x b) =
      some (.simdLdSt1Multi true true 2#2 1 (.gpr (BitVec.ofNat 5 b.val)) false 0#5 (BitVec.ofNat 5 x.val)) := by
  have hx : x.val < 2 ^ 5 := x.isLt; have hb : b.val < 2 ^ 5 := by omega
  have hf : encodeLd1_4s x b &&& 0xfffffc00#32 = 0x4c407800#32 &&& 0xfffffc00#32 := by
    have h1 : (BitVec.ofNat 32 b.val <<< 5) &&& 0xfffffc00#32 = 0#32 := field_and_eq_zero hb (by decide)
    have h2 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xfffffc00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h2
    unfold encodeLd1_4s; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]
  have hopc : (encodeLd1_4s x b).extractLsb' 12 4 = 7#4 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [decode_at_simdLdSt1Multi hf (by decide) (by decide) ⟨by decide, by decide⟩ hopc]
  have ex_x : (encodeLd1_4s x b).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeLd1_4s; simp only [extract_or]
    have h0 : (0x4c407800#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hb (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_b : (encodeLd1_4s x b).extractLsb' 5 5 = BitVec.ofNat 5 b.val := by
    unfold encodeLd1_4s; simp only [extract_or]
    have h0 : (0x4c407800#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 b.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have hl : (encodeLd1_4s x b).getLsbD 22 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hq : (encodeLd1_4s x b).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hsz : (encodeLd1_4s x b).extractLsb' 10 2 = 2#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hpi : (encodeLd1_4s x b).getLsbD 23 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hrm : (encodeLd1_4s x b).extractLsb' 16 5 = 0#5 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [hl, hq, hsz, hpi, hrm, ex_x, ex_b, fromSPBits_fin31]

theorem agree_ld1_4s (x : Fin 32) (b : Fin 31) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hbb : Ode.regOf bind "B" = some (armSlot b.val))
    (hfit : st.reg (armSlot b.val) + 16 ≤ Ode.M64)
    (hread : gs.mem.canRead (gs.readReg64 (.gpr (BitVec.ofNat 5 b.val))) 16 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeLd1_4s x b) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectLd1_4s, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let a := st.reg (armSlot b.val)
  have ha_mod : a % Ode.M64 = a := Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) = BitVec.ofNat 64 a := by
    apply BitVec.eq_of_toNat_eq; rw [hA.gpr b, BitVec.toNat_ofNat]
    unfold Ode.M64 at hfit; exact (Nat.mod_eq_of_lt (by omega)).symm
  let lanes : List Nat := [Ode.load st.mem a 4, Ode.load st.mem (a + 4) 4,
                           Ode.load st.mem (a + 8) 4, Ode.load st.mem (a + 12) 4]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "mem128" [.name "B", .number 0])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectLd1_4s, bind, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.read a 16 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectLd1_4s, Ode.execStmt, Ode.lanesOf, Ode.values, Ode.sumList,
          hbx, Ode.value, Ode.isNumberLetter, hbb, ha_mod, hall,
          List.range, List.range.loop, lanes, a, st', st1, st0]
  have hread' : gs.mem.canRead (BitVec.ofNat 64 a) 16 = true := by rwa [← hea_bv]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdLdSt1Multi true true 2#2 1 (.gpr (BitVec.ofNat 5 b.val)) false 0#5 (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) (gs.mem.read128 (BitVec.ofNat 64 a))).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.checkRegSPAligned, Arm64.SimdMemSize.ofQ, Arm64.SimdMemSize.bytes,
          Arm64.simdLoadRegs, Arm64.Memory.readSimdSized, hea_bv, hread']
  refine ⟨_, st', decode_ld1_4s x b, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  apply agreeState_writeVec hA x (gs.mem.read128 (BitVec.ofNat 64 a)) lanes (u 0) ?_ _ _ hnext hpc
  intro j
  rw [read128_lane_eq_load hA hfit j]
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

theorem decode_st1_4s (x : Fin 32) (b : Fin 31) :
    Arm64.decode (encodeSt1_4s x b) =
      some (.simdLdSt1Multi false true 2#2 1 (.gpr (BitVec.ofNat 5 b.val)) false 0#5 (BitVec.ofNat 5 x.val)) := by
  have hx : x.val < 2 ^ 5 := x.isLt; have hb : b.val < 2 ^ 5 := by omega
  have hf : encodeSt1_4s x b &&& 0xfffffc00#32 = 0x4c007800#32 &&& 0xfffffc00#32 := by
    have h1 : (BitVec.ofNat 32 b.val <<< 5) &&& 0xfffffc00#32 = 0#32 := field_and_eq_zero hb (by decide)
    have h2 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xfffffc00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h2
    unfold encodeSt1_4s; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]
  have hopc : (encodeSt1_4s x b).extractLsb' 12 4 = 7#4 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [decode_at_simdLdSt1Multi hf (by decide) (by decide) ⟨by decide, by decide⟩ hopc]
  have ex_x : (encodeSt1_4s x b).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeSt1_4s; simp only [extract_or]
    have h0 : (0x4c007800#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hb (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_b : (encodeSt1_4s x b).extractLsb' 5 5 = BitVec.ofNat 5 b.val := by
    unfold encodeSt1_4s; simp only [extract_or]
    have h0 : (0x4c007800#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 b.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have hl : (encodeSt1_4s x b).getLsbD 22 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hq : (encodeSt1_4s x b).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hsz : (encodeSt1_4s x b).extractLsb' 10 2 = 2#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hpi : (encodeSt1_4s x b).getLsbD 23 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hrm : (encodeSt1_4s x b).extractLsb' 16 5 = 0#5 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [hl, hq, hsz, hpi, hrm, ex_x, ex_b, fromSPBits_fin31]

theorem agree_st1_4s (x : Fin 32) (b : Fin 31) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hbb : Ode.regOf bind "B" = some (armSlot b.val))
    (hfit : st.reg (armSlot b.val) + 16 ≤ Ode.M64)
    (hwrite : gs.mem.canWrite (gs.readReg64 (.gpr (BitVec.ofNat 5 b.val))) 16 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeSt1_4s x b) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectSt1_4s, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let a := st.reg (armSlot b.val)
  have ha_mod : a % Ode.M64 = a := Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) = BitVec.ofNat 64 a := by
    apply BitVec.eq_of_toNat_eq; rw [hA.gpr b, BitVec.toNat_ofNat]
    unfold Ode.M64 at hfit; exact (Nat.mod_eq_of_lt (by omega)).symm
  let mem' := Ode.store (Ode.store (Ode.store (Ode.store st.mem a (st.vec x.val 0) 4) (a + 4) (st.vec x.val 1) 4)
                (a + 8) (st.vec x.val 2) 4) (a + 12) (st.vec x.val 3) 4
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := { st0 with mem := mem' }
  let st' : Ode.State := Ode.noted bind st0 (.vset (.call "mem128" [.name "B", .number 0]) (.name "X")) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectSt1_4s, bind, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.write a 16 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectSt1_4s, Ode.execStmt, Ode.vecArg, Ode.values, Ode.sumList,
          hbx, Ode.value, Ode.isNumberLetter, hbb, ha_mod, hall,
          List.range, List.range.loop, mem', a, st', st1, st0]
  have hwrite' : gs.mem.canWrite (BitVec.ofNat 64 a) 16 = true := by rwa [← hea_bv]
  let vx := gs.readVReg128 (BitVec.ofNat 5 x.val)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdLdSt1Multi false true 2#2 1 (.gpr (BitVec.ofNat 5 b.val)) false 0#5 (BitVec.ofNat 5 x.val)) gs =
      (gs.setMem (gs.mem.write128 (BitVec.ofNat 64 a) vx)).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.checkRegSPAligned, Arm64.SimdMemSize.ofQ, Arm64.SimdMemSize.bytes,
          Arm64.simdStoreRegs, Arm64.Memory.writeSimdSized, hea_bv, hwrite', vx]
  refine ⟨_, st', decode_st1_4s x b, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  apply agreeState_setMem hA mem' (gs.mem.write128 (BitVec.ofNat 64 a) vx) ?_ _ _ hnext hpc
  intro addr haddr
  have hadd8 : BitVec.ofNat 64 a + 8#64 = BitVec.ofNat 64 (a + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    unfold Ode.M64 at hfit
    rw [Nat.mod_eq_of_lt (by omega), show 8 % 2 ^ 64 = 8 by decide, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hlo64 : (vx.extractLsb' 0 64).toNat = st.vec x.val 0 + 2 ^ 32 * st.vec x.val 1 := by
    have h0 := hA.vec x ⟨0, by decide⟩; have h1 := hA.vec x ⟨1, by decide⟩
    have hv0 : (vx.extractLsb' 0 64).extractLsb' 0 32 = vx.extractLsb' 0 32 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]
    have hv1 : (vx.extractLsb' 0 64).extractLsb' 32 32 = vx.extractLsb' 32 32 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]
    have hloLt : (vx.extractLsb' 0 64).toNat < 2 ^ 64 := (vx.extractLsb' 0 64).isLt
    have e0 := congrArg BitVec.toNat hv0; have e1 := congrArg BitVec.toNat hv1
    rw [BitVec.extractLsb'_toNat] at e0 e1; simp only [Nat.shiftRight_eq_div_pow] at e0 e1
    change (vx.extractLsb' 0 32).toNat = st.vec x.val 0 at h0
    change (vx.extractLsb' 32 32).toNat = st.vec x.val 1 at h1
    omega
  have hhi64 : (vx.extractLsb' 64 64).toNat = st.vec x.val 2 + 2 ^ 32 * st.vec x.val 3 := by
    have h2 := hA.vec x ⟨2, by decide⟩; have h3 := hA.vec x ⟨3, by decide⟩
    have hv2 : (vx.extractLsb' 64 64).extractLsb' 0 32 = vx.extractLsb' 64 32 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk, show k < 64 by omega]
    have hv3 : (vx.extractLsb' 64 64).extractLsb' 32 32 = vx.extractLsb' 96 32 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk, show 32 + k < 64 by omega, show 64 + (32 + k) = 96 + k by omega]
    have hhiLt : (vx.extractLsb' 64 64).toNat < 2 ^ 64 := (vx.extractLsb' 64 64).isLt
    have e2 := congrArg BitVec.toNat hv2; have e3 := congrArg BitVec.toNat hv3
    rw [BitVec.extractLsb'_toNat] at e2 e3; simp only [Nat.shiftRight_eq_div_pow] at e2 e3
    change (vx.extractLsb' 64 32).toNat = st.vec x.val 2 at h2
    change (vx.extractLsb' 96 32).toNat = st.vec x.val 3 at h3
    omega
  have hstore8 : ∀ m p w0 w1 (hw0 : w0 < 2 ^ 32) addr,
      (Ode.store (Ode.store m p w0 4) (p + 4) w1 4 addr).val =
      (Ode.store m p (w0 + 2 ^ 32 * w1) 8 addr).val := by
    intro m p w0 w1 hw0 addr
    rw [store_at, store_at, store_at]
    by_cases hhi : p + 4 ≤ addr ∧ addr < p + 4 + 4
    · simp only [hhi, show p ≤ addr ∧ addr < p + 8 by omega, and_self, ↓reduceIte]
      have hk : addr - p = 4 + (addr - (p + 4)) := by omega
      rw [hk, Nat.pow_add, show (256 : Nat) ^ 4 = 2 ^ 32 by decide, ← Nat.div_div_eq_div_mul]
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 32), Nat.div_eq_of_lt hw0, Nat.zero_add]
    · simp only [hhi, ↓reduceIte]
      by_cases hlo : p ≤ addr ∧ addr < p + 4
      · simp only [hlo, show p ≤ addr ∧ addr < p + 8 by omega, and_self, ↓reduceIte]
        have hd : 256 ^ (addr - p) * 256 ∣ 2 ^ 32 := by
          have : addr - p + 1 ≤ 4 := by omega
          have := Nat.pow_dvd_pow 256 this
          simpa [Nat.pow_succ] using this
        obtain ⟨q, hq⟩ := hd
        have hq2 : 2 ^ 32 * w1 = 256 ^ (addr - p) * (256 * (q * w1)) := by
          rw [hq, Nat.mul_assoc, Nat.mul_assoc]
        have hpos : 0 < 256 ^ (addr - p) := Nat.pow_pos (by decide)
        rw [hq2, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
      · simp only [hlo, show ¬(p ≤ addr ∧ addr < p + 8) by omega, ↓reduceIte]
  have hw0 : st.vec x.val 0 < 2 ^ 32 := by rw [← hA.vec x ⟨0, by decide⟩]; exact (vx.extractLsb' 0 32).isLt
  have hw2 : st.vec x.val 2 < 2 ^ 32 := by rw [← hA.vec x ⟨2, by decide⟩]; exact (vx.extractLsb' 64 32).isLt
  let stMid : Ode.State := { st with mem := Ode.store st.mem a (st.vec x.val 0 + 2 ^ 32 * st.vec x.val 1) 8 }
  let gsMid : Arm64.State := gs.setMem (gs.mem.write64 (BitVec.ofNat 64 a) (vx.extractLsb' 0 64))
  have hMid : AgreeState stMid gsMid :=
    ⟨hA.running, hA.gpr, hA.sp, hA.vec,
     fun p hp => write64_eq_store hA (by omega) (vx.extractLsb' 0 64) _ hlo64 hp,
     hA.pc, hA.zf, hA.cf⟩
  have hstep2 := write64_eq_store hMid (a := a + 8) (by omega) (vx.extractLsb' 64 64) _ hhi64 haddr
  unfold Arm64.Memory.write128
  rw [hadd8]
  change ((gsMid.mem.write64 (BitVec.ofNat 64 (a + 8)) (vx.extractLsb' 64 64)).read8 (BitVec.ofNat 64 addr)).toNat = _
  rw [hstep2]
  change (Ode.store (Ode.store st.mem a (st.vec x.val 0 + 2 ^ 32 * st.vec x.val 1) 8) (a + 8) (st.vec x.val 2 + 2 ^ 32 * st.vec x.val 3) 8 addr).val = (mem' addr).val
  have h1 := hstore8 st.mem a (st.vec x.val 0) (st.vec x.val 1) hw0
  have heqm : Ode.store (Ode.store st.mem a (st.vec x.val 0) 4) (a + 4) (st.vec x.val 1) 4 =
              Ode.store st.mem a (st.vec x.val 0 + 2 ^ 32 * st.vec x.val 1) 8 := by
    funext p; exact Fin.ext (h1 p)
  have h2 := hstore8 (Ode.store st.mem a (st.vec x.val 0 + 2 ^ 32 * st.vec x.val 1) 8) (a + 8) (st.vec x.val 2) (st.vec x.val 3) hw2 addr
  simpa [mem', heqm, show a + 8 + 4 = a + 12 by omega] using h2.symm

-- ============================================================================
-- Row 37: `lsl_ri` (`lsl D64, S64, I` -> `D = shl64(S, I)`, 1 <= I <= 63)
-- ============================================================================

def effectLslRi : List Ode.Stmt :=
  [.set (.name "D") (.call "shl64" [.name "S", .name "I"])]

def encodeLslRi (d s : Fin 31) (sh : Fin 63) : BitVec 32 :=
  0xd3400000#32 ||| (BitVec.ofNat 32 (63 - sh.val) <<< 16) ||| (BitVec.ofNat 32 (62 - sh.val) <<< 10) |||
    (BitVec.ofNat 32 s.val <<< 5) ||| BitVec.ofNat 32 d.val

def guardsBeforeBitfield : List (BitVec 32 × BitVec 32) :=
  guardsBeforeSimdThreeSame.take 9

theorem decode_lsl_ri (d s : Fin 31) (sh : Fin 63) :
    Arm64.decode (encodeLslRi d s sh) =
      some (.bitfield .W64 .UBFM (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val))
        (63 - sh.val) (62 - sh.val)) := by
  have hr : 63 - sh.val < 2 ^ 6 := by omega
  have hs' : 62 - sh.val < 2 ^ 6 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have hd : d.val < 2 ^ 5 := by omega
  have hf : encodeLslRi d s sh &&& 0xffc00000#32 = 0xd3400000#32 &&& 0xffc00000#32 := by
    have h1 : (BitVec.ofNat 32 (63 - sh.val) <<< 16) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hr (by decide)
    have h2 : (BitVec.ofNat 32 (62 - sh.val) <<< 10) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hs' (by decide)
    have h3 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hs (by decide)
    have h4 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hd (by decide)
    simp only [BitVec.shiftLeft_zero] at h4
    unfold encodeLslRi; simp only [BitVec.and_or_distrib_right, h1, h2, h3, h4, BitVec.or_zero]
  have sk : ∀ m c, (m, c) ∈ guardsBeforeBitfield → ((encodeLslRi d s sh &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hf (by decide) hm
  have hnop : (encodeLslRi d s sh == 0xd503201f#32) = false := word_ne_of_fixed hf (by decide)
  have hhit : encodeLslRi d s sh &&& 0x1f800000#32 = 0x13000000#32 := by
    rw [mask_of_fixed hf (by decide)]; decide
  have hsf : (encodeLslRi d s sh).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hopc : ((encodeLslRi d s sh).extractLsb' 29 2).toNat = 2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hn : (encodeLslRi d s sh).getLsbD 22 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have ex_r : (encodeLslRi d s sh).extractLsb' 16 6 = BitVec.ofNat 6 (63 - sh.val) := by
    unfold encodeLslRi; simp only [extract_or]
    have h0 : (0xd3400000#32).extractLsb' 16 6 = 0#6 := by decide
    have h1 : (BitVec.ofNat 32 (63 - sh.val) <<< 16).extractLsb' 16 6 = BitVec.ofNat 6 (63 - sh.val) := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 (62 - sh.val) <<< 10).extractLsb' 16 6 = 0#6 := extract_field_miss hs' (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 16 6 = 0#6 := extract_field_miss hs (by omega)
    have h4 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 16 6 = 0#6 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  have ex_s' : (encodeLslRi d s sh).extractLsb' 10 6 = BitVec.ofNat 6 (62 - sh.val) := by
    unfold encodeLslRi; simp only [extract_or]
    have h0 : (0xd3400000#32).extractLsb' 10 6 = 0#6 := by decide
    have h1 : (BitVec.ofNat 32 (63 - sh.val) <<< 16).extractLsb' 10 6 = 0#6 := extract_field_miss hr (by omega)
    have h2 : (BitVec.ofNat 32 (62 - sh.val) <<< 10).extractLsb' 10 6 = BitVec.ofNat 6 (62 - sh.val) := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 10 6 = 0#6 := extract_field_miss hs (by omega)
    have h4 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 10 6 = 0#6 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  have ex_s : (encodeLslRi d s sh).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeLslRi; simp only [extract_or]
    have h0 : (0xd3400000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 (63 - sh.val) <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hr (by omega)
    have h2 : (BitVec.ofNat 32 (62 - sh.val) <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hs' (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    have h4 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  have ex_d : (encodeLslRi d s sh).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeLslRi; simp only [extract_or]
    have h0 : (0xd3400000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 (63 - sh.val) <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hr (by omega)
    have h2 : (BitVec.ofNat 32 (62 - sh.val) <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hs' (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hs (by omega)
    have h4 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  unfold Arm64.decode
  simp only [hnop,
             sk 0xffe0001f#32 0xd4000001#32 (by decide), sk 0xffe0001f#32 0xd4200000#32 (by decide),
             sk 0xfffff01f#32 0xd503201f#32 (by decide), sk 0xffff0000#32 0x00000000#32 (by decide),
             sk 0xffffffe0#32 0xd50b7420#32 (by decide), sk 0x1f000000#32 0x10000000#32 (by decide),
             hhit,
             show (0x13000000#32 == 0x11000000#32) = false by decide,
             show (0x13000000#32 == 0x12000000#32) = false by decide,
             show (0x13000000#32 == 0x12800000#32) = false by decide,
             beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
             Arm64.RegWidth.ofBool, hsf, hopc, hn, ex_r, ex_s', ex_s, ex_d,
             fromZRBits_fin31, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs']

theorem agree_lsl_ri (d s : Fin 31) (sh : Fin 63) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some ((sh.val + 1 : Nat) : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeLslRi d s sh) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectLslRi, bindRri d s numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let shift := sh.val + 1
  have hshlt : shift < Ode.M64 := by unfold Ode.M64; have := sh.isLt; omega
  have hmod : (((sh.val : Int) + 1) % (Ode.M64 : Int)).toNat = shift := by
    have h1 : (sh.val : Int) + 1 = ((shift : Nat) : Int) := by push_cast [shift]; rfl
    rw [h1, Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hshlt)]; rfl
  let val := (st.reg (armSlot s.val) <<< shift) % Ode.M64
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) val
  let st' : Ode.State := Ode.noted (bindRri d s numStr) st0 (.set (.name "D") (.call "shl64" [.name "S", .name "I"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectLslRi, bindRri d s numStr, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectLslRi, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.prim,
          Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindRri, List.lookup,
          regIndex_armRegName, hnum, hmod, val, shift, st', st1, st0]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.bitfield .W64 .UBFM (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val))
        (63 - sh.val) (62 - sh.val)) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) <<< shift)).advancePC := by
    have hrm : (63 - sh.val) % 64 = 63 - sh.val := Nat.mod_eq_of_lt (by omega)
    have hsm : (62 - sh.val) % 64 = 62 - sh.val := Nat.mod_eq_of_lt (by omega)
    have hc0 : ¬(63 - sh.val = 64) := by omega
    have hc2 : 63 - sh.val > 62 - sh.val := by omega
    have hc3 : (62 - sh.val) + 1 = 63 - sh.val := by omega
    have hc4 : 64 - (63 - sh.val) = shift := by omega
    simp [Arm64.execInstWithSvc, Arm64.execBitfield, Arm64.evalBitfield,
          Arm64.State.writeReg, Arm64.State.readReg,
          show (Arm64.BitfieldOp.UBFM == Arm64.BitfieldOp.UBFM) = true by decide,
          hrm, hsm, hc0, hc2, hc3, hc4]
  refine ⟨_, st', decode_lsl_ri d s sh, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  have hgv : (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) <<< shift).toNat = val := by
    rw [BitVec.toNat_shiftLeft, hA.gpr s]; rfl
  exact agreeState_writeGpr hA d (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) <<< shift) val hgv _ _ hnext hpc

-- ============================================================================
-- Row 38: `fmov_d` (`fmov dX, S64` -> `X = lanes_of64(S)`)
-- ============================================================================

def effectFmovD : List Ode.Stmt :=
  [.vset (.name "X") (.call "lanes_of64" [.name "S"])]

def encodeFmovD (x : Fin 32) (s : Fin 31) : BitVec 32 :=
  0x9e670000#32 ||| (BitVec.ofNat 32 s.val <<< 5) ||| BitVec.ofNat 32 x.val

def guardsBeforeFmov : List (BitVec 32 × BitVec 32) :=
  guardsBeforeSimdThreeSame.take 58

theorem decode_fmov_d (x : Fin 32) (s : Fin 31) :
    Arm64.decode (encodeFmovD x s) =
      some (.fmovGprVec true 1#2 0#2 7#3 (BitVec.ofNat 5 s.val) (BitVec.ofNat 5 x.val)) := by
  have hs : s.val < 2 ^ 5 := by omega
  have hx : x.val < 2 ^ 5 := x.isLt
  have hf : encodeFmovD x s &&& 0xfffffc00#32 = 0x9e670000#32 &&& 0xfffffc00#32 := by
    have h1 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xfffffc00#32 = 0#32 := field_and_eq_zero hs (by decide)
    have h2 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xfffffc00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h2
    unfold encodeFmovD; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]
  have sk : ∀ m c, (m, c) ∈ guardsBeforeFmov → ((encodeFmovD x s &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hf (by decide) hm
  have hnop : (encodeFmovD x s == 0xd503201f#32) = false := word_ne_of_fixed hf (by decide)
  have hhit : encodeFmovD x s &&& 0x7f20fc00#32 = 0x1e200000#32 := by rw [mask_of_fixed hf (by decide)]; decide
  have hsf : (encodeFmovD x s).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hft : (encodeFmovD x s).extractLsb' 22 2 = 1#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hrm : (encodeFmovD x s).extractLsb' 19 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hop : (encodeFmovD x s).extractLsb' 16 3 = 7#3 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_s : (encodeFmovD x s).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeFmovD; simp only [extract_or]
    have h0 : (0x9e670000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_x : (encodeFmovD x s).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeFmovD; simp only [extract_or]
    have h0 : (0x9e670000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hs (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  unfold Arm64.decode
  simp only [hnop,
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
             sk 0xbfe00000#32 0x0dc00000#32 (by decide), sk 0xffffcc00#32 0x4e284800#32 (by decide),
             hhit, beq_self_eq_true, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
             hsf, hft, hrm, hop, ex_s, ex_x]

theorem agree_fmov_d (x : Fin 32) (s : Fin 31) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hbs : Ode.regOf bind "S" = some (armSlot s.val))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeFmovD x s) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectFmovD, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let sv := st.reg (armSlot s.val)
  let lanes : List Nat := [sv % Ode.W32, sv / Ode.W32 % Ode.W32, 0, 0]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "lanes_of64" [.name "S"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectFmovD, bind, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectFmovD, Ode.execStmt, Ode.lanesOf, Ode.values,
          Ode.value, Ode.isNumberLetter, hbx, hbs, lanes, sv, st', st1, st0]
  let gval := gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.fmovGprVec true 1#2 0#2 7#3 (BitVec.ofNat 5 s.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) (gval.zeroExtend 128)).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.State.writeVReg64, fromZRBits_fin31, gval]
  refine ⟨_, st', decode_fmov_d x s, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  apply agreeState_writeVec hA x (gval.zeroExtend 128) lanes (u 0) ?_ bind _ hnext hpc
  intro k
  have hval : gval.toNat = sv := hA.gpr s
  have hzero : (gval.zeroExtend 128).toNat = sv := by
    simp only [BitVec.zeroExtend, BitVec.toNat_setWidth, hval]
    exact Nat.mod_eq_of_lt (by have := gval.isLt; omega)
  match k with
  | ⟨0, _⟩ => simp [lanes, Ode.W32, BitVec.extractLsb'_toNat, hzero]
  | ⟨1, _⟩ => simp [lanes, Ode.W32, BitVec.extractLsb'_toNat, hzero, Nat.shiftRight_eq_div_pow]
  | ⟨2, _⟩ =>
    simp only [lanes, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
               BitVec.extractLsb'_toNat, hzero, Nat.shiftRight_eq_div_pow]
    have hlt : sv < 2 ^ 64 := by rw [← hval]; exact gval.isLt
    rw [Nat.div_eq_of_lt hlt]
  | ⟨3, _⟩ =>
    simp only [lanes, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
               BitVec.extractLsb'_toNat, hzero, Nat.shiftRight_eq_div_pow]
    have hlt : sv < 2 ^ 96 := by have := gval.isLt; omega
    rw [Nat.div_eq_of_lt hlt]

-- ============================================================================
-- Rows 39-44: SIMD Permute (`uzp1_4s`, `uzp2_4s`, `zip1_4s`, `zip2_4s`, `zip1_2d`, `zip2_2d`)
-- ============================================================================

def guardsBeforeSimdPermute : List (BitVec 32 × BitVec 32) :=
  guardsBeforeSimdThreeSame ++
  [ (0x9f200400#32, 0x0e200400#32), (0x9f3e0c00#32, 0x0e200800#32),
    (0x9f3e0c00#32, 0x0e300800#32) ]

theorem decode_at_simdPermute {w base fixed : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hnop : ((base &&& fixed) == (0xd503201f#32 &&& fixed)) = false)
    (hskip : skipsAll base fixed guardsBeforeSimdPermute = true)
    (hmatch : (0xbf208c00#32 &&& fixed = 0xbf208c00#32) ∧ (base &&& 0xbf208c00#32 = 0x0e000800#32)) :
    Arm64.decode w =
      some (.simdPermute (w.getLsbD 30) (w.extractLsb' 22 2) (w.extractLsb' 16 5)
        (w.extractLsb' 12 3) (w.extractLsb' 5 5) (w.extractLsb' 0 5)) := by
  have sk : ∀ m c, (m, c) ∈ guardsBeforeSimdPermute → ((w &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hw hskip hm
  have hhit : w &&& 0xbf208c00#32 = 0x0e000800#32 := by rw [mask_of_fixed hw hmatch.1, hmatch.2]
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
             sk 0xbfe00000#32 0x0dc00000#32 (by decide), sk 0xffffcc00#32 0x4e284800#32 (by decide),
             sk 0x7f20fc00#32 0x1e200000#32 (by decide), sk 0x9f800400#32 0x0f000400#32 (by decide),
             sk 0xbfe08c00#32 0x0e000000#32 (by decide), sk 0xfffffc00#32 0x5ef1b800#32 (by decide),
             sk 0xffe0fc00#32 0x5e000400#32 (by decide), sk 0x9fe08400#32 0x0e000400#32 (by decide),
             sk 0x9f200400#32 0x0e200400#32 (by decide), sk 0x9f3e0c00#32 0x0e200800#32 (by decide),
             sk 0x9f3e0c00#32 0x0e300800#32 (by decide),
             hhit, beq_self_eq_true, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

private theorem mask64_getLsbD (i : Nat) :
    (((1#128 <<< 64) - 1#128 : BitVec 128)).getLsbD i = decide (i < 64) := by
  have hm : ((1#128 <<< 64) - 1#128 : BitVec 128) = BitVec.ofNat 128 (2 ^ 64 - 1) := by decide
  rw [hm, BitVec.getLsbD_ofNat]
  by_cases hi : i < 128
  · simp only [hi, decide_true, Bool.true_and, Nat.testBit_two_pow_sub_one]
  · simp [hi, show ¬(i < 64) by omega]

private theorem getSimdLane32_getLsbD (v : BitVec 128) (idx j : Nat) :
    (Arm64.getSimdLane v 32 idx).getLsbD j = (decide (j < 32) && v.getLsbD (idx * 32 + j)) := by
  unfold Arm64.getSimdLane
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, mask32_getLsbD j, Bool.and_comm]

private theorem getSimdLane64_getLsbD (v : BitVec 128) (idx j : Nat) :
    (Arm64.getSimdLane v 64 idx).getLsbD j = (decide (j < 64) && v.getLsbD (idx * 64 + j)) := by
  unfold Arm64.getSimdLane
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, mask64_getLsbD j, Bool.and_comm]

private theorem bv_or4_swap (a b c d : BitVec 128) :
    a ||| c ||| b ||| d = a ||| b ||| c ||| d := by
  apply BitVec.eq_of_getLsbD_eq; intro k _
  simp only [BitVec.getLsbD_or]
  cases a.getLsbD k <;> cases b.getLsbD k <;> cases c.getLsbD k <;> cases d.getLsbD k <;> rfl

private theorem pack4_32_extract (a0 a1 a2 a3 : BitVec 128)
    (ha0 : ∀ j, 32 ≤ j → j < 128 → a0.getLsbD j = false)
    (ha1 : ∀ j, 32 ≤ j → j < 128 → a1.getLsbD j = false)
    (ha2 : ∀ j, 32 ≤ j → j < 128 → a2.getLsbD j = false) :
    let acc : BitVec 128 := a0 ||| (a1 <<< 32) ||| (a2 <<< 64) ||| (a3 <<< 96)
    acc.extractLsb' 0 32 = a0.extractLsb' 0 32 ∧
    acc.extractLsb' 32 32 = a1.extractLsb' 0 32 ∧
    acc.extractLsb' 64 32 = a2.extractLsb' 0 32 ∧
    acc.extractLsb' 96 32 = a3.extractLsb' 0 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, Nat.zero_add,
               BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
               show k < 64 by omega, show k < 96 by omega, show k < 128 by omega,
               Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, Nat.zero_add,
               BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
               ha0 (32 + k) (by omega) (by omega),
               show ¬(32 + k < 32) by omega, show 32 + k < 64 by omega, show 32 + k < 96 by omega,
               show 32 + k < 128 by omega, show 32 + k - 32 = k by omega,
               decide_false, Bool.not_false, Bool.not_true, Bool.true_and, Bool.and_true,
               Bool.and_false, Bool.false_and, Bool.false_or, Bool.or_false]
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, Nat.zero_add,
               BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
               ha0 (64 + k) (by omega) (by omega), ha1 (64 + k - 32) (by omega) (by omega),
               show ¬(64 + k < 32) by omega, show ¬(64 + k < 64) by omega, show 64 + k < 96 by omega,
               show 64 + k < 128 by omega, show 64 + k - 64 = k by omega,
               decide_false, Bool.not_false, Bool.not_true, Bool.true_and, Bool.and_true,
               Bool.and_false, Bool.false_and, Bool.false_or, Bool.or_false]
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, Nat.zero_add,
               BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
               ha0 (96 + k) (by omega) (by omega), ha1 (96 + k - 32) (by omega) (by omega),
               ha2 (96 + k - 64) (by omega) (by omega),
               show ¬(96 + k < 32) by omega, show ¬(96 + k < 64) by omega, show ¬(96 + k < 96) by omega,
               show 96 + k < 128 by omega, show 96 + k - 96 = k by omega,
               decide_false, Bool.not_false, Bool.true_and, Bool.and_true, Bool.and_false, Bool.false_or]

private theorem pack2_64_extract (a0 a1 : BitVec 128)
    (ha0 : ∀ j, 64 ≤ j → j < 128 → a0.getLsbD j = false) :
    let acc : BitVec 128 := a0 ||| (a1 <<< 64)
    acc.extractLsb' 0 32 = a0.extractLsb' 0 32 ∧
    acc.extractLsb' 32 32 = a0.extractLsb' 32 32 ∧
    acc.extractLsb' 64 32 = a1.extractLsb' 0 32 ∧
    acc.extractLsb' 96 32 = a1.extractLsb' 32 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, Nat.zero_add,
               BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, show k < 64 by omega, show k < 128 by omega,
               Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
               BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, show 32 + k < 64 by omega, show 32 + k < 128 by omega,
               Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, Nat.zero_add,
               BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
               ha0 (64 + k) (by omega) (by omega), show ¬(64 + k < 64) by omega,
               show 64 + k - 64 = k by omega, show 64 + k < 128 by omega,
               decide_false, Bool.not_false, Bool.true_and, Bool.and_true, Bool.false_or]
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
               BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
               ha0 (96 + k) (by omega) (by omega), show ¬(96 + k < 64) by omega,
               show 96 + k - 64 = 32 + k by omega, show 96 + k < 128 by omega,
               decide_false, Bool.not_false, Bool.true_and, Bool.and_true, Bool.false_or]

private theorem getSimdLane32_extract (v : BitVec 128) (idx : Nat) :
    (Arm64.getSimdLane v 32 idx).extractLsb' 0 32 = v.extractLsb' (idx * 32) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, Nat.zero_add]
  rw [getSimdLane32_getLsbD v idx k]; simp [hk]

private theorem getSimdLane32_hi (v : BitVec 128) (idx j : Nat) (h1 : 32 ≤ j) (_ : j < 128) :
    (Arm64.getSimdLane v 32 idx).getLsbD j = false := by
  rw [getSimdLane32_getLsbD v idx j]; simp [show ¬(j < 32) by omega]

private theorem getSimdLane64_extract0 (v : BitVec 128) (idx : Nat) :
    (Arm64.getSimdLane v 64 idx).extractLsb' 0 32 = v.extractLsb' (idx * 64) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, Nat.zero_add]
  rw [getSimdLane64_getLsbD v idx k]; simp [show k < 64 by omega]

private theorem getSimdLane64_extract1 (v : BitVec 128) (idx : Nat) :
    (Arm64.getSimdLane v 64 idx).extractLsb' 32 32 = v.extractLsb' (idx * 64 + 32) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  rw [getSimdLane64_getLsbD v idx (32 + k)]; simp [show 32 + k < 64 by omega, Nat.add_assoc]

private theorem getSimdLane64_hi (v : BitVec 128) (idx j : Nat) (h1 : 64 ≤ j) (_ : j < 128) :
    (Arm64.getSimdLane v 64 idx).getLsbD j = false := by
  rw [getSimdLane64_getLsbD v idx j]; simp [show ¬(j < 64) by omega]

private theorem encode_simdPermute_decode (base : BitVec 32) (sz : BitVec 2) (opc : BitVec 3)
    (x y z : Fin 32)
    (hbz : base.extractLsb' 16 5 = 0#5) (hby : base.extractLsb' 5 5 = 0#5) (hbx : base.extractLsb' 0 5 = 0#5)
    (hskip : skipsAll base 0xffe0fc00#32 guardsBeforeSimdPermute = true)
    (hnop : ((base &&& 0xffe0fc00#32) == (0xd503201f#32 &&& 0xffe0fc00#32)) = false)
    (hmatch : base &&& 0xbf208c00#32 = 0x0e000800#32)
    (hq : base.getLsbD 30 = true)
    (hsz : base.extractLsb' 22 2 = sz)
    (hopc : base.extractLsb' 12 3 = opc) :
    Arm64.decode (base ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val) =
      some (.simdPermute true sz (BitVec.ofNat 5 z.val) opc (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) := by
  have hz : z.val < 2 ^ 5 := z.isLt; have hy : y.val < 2 ^ 5 := y.isLt; have hx : x.val < 2 ^ 5 := x.isLt
  let w := base ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val
  have hf : w &&& 0xffe0fc00#32 = base &&& 0xffe0fc00#32 := by
    have h1 : (BitVec.ofNat 32 z.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hz (by decide)
    have h2 : (BitVec.ofNat 32 y.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hy (by decide)
    have h3 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold w; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_simdPermute hf hnop hskip ⟨by decide, hmatch⟩]
  have ex_z : w.extractLsb' 16 5 = BitVec.ofNat 5 z.val := by
    unfold w; simp only [extract_or, hbz]
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 z.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h1, h2, h3]; simp
  have ex_y : w.extractLsb' 5 5 = BitVec.ofNat 5 y.val := by
    unfold w; simp only [extract_or, hby]
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 y.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h1, h2, h3]; simp
  have ex_x : w.extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold w; simp only [extract_or, hbx]
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h1, h2, h3]; simp
  have hq' : w.getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide), hq]
  have hsz' : w.extractLsb' 22 2 = sz := by rw [extract_of_fixed hf (by decide), hsz]
  have hopc' : w.extractLsb' 12 3 = opc := by rw [extract_of_fixed hf (by decide), hopc]
  rw [hq', hsz', hopc', ex_z, ex_y, ex_x]

private theorem agree_lanes_helper (x : Fin 32) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (stmt : Ode.Stmt) (l0 l1 l2 l3 : Nat) (ginst : Arm64.Instr) (word : BitVec 32) (res : BitVec 128)
    (hdec : Arm64.decode word = some ginst)
    (heff : Ode.exec Ode.Perm.all prog ⟨[stmt], bind, next⟩ u st =
      some (.next (Ode.noted bind { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
        stmt (Ode.setVec { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] } x.val [l0, l1, l2, l3] (u 0)))))
    (hgs : Arm64.execInstWithSvc Arm64.noSyscalls ginst gs = (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC)
    (h0 : (res.extractLsb' 0 32).toNat = l0)
    (h1 : (res.extractLsb' 32 32).toNat = l1)
    (h2 : (res.extractLsb' 64 32).toNat = l2)
    (h3 : (res.extractLsb' 96 32).toNat = l3)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst' st',
      Arm64.decode word = some ginst' ∧
      Ode.exec Ode.Perm.all prog ⟨[stmt], bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst' gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst' gs).pstate = gs.pstate := by
  refine ⟨ginst, _, hdec, heff, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  apply agreeState_writeVec hA x res [l0, l1, l2, l3] (u 0) ?_ bind stmt hnext hpc
  intro k
  match k with
  | ⟨0, _⟩ => simpa [List.getD] using h0
  | ⟨1, _⟩ => simpa [List.getD] using h1
  | ⟨2, _⟩ => simpa [List.getD] using h2
  | ⟨3, _⟩ => simpa [List.getD] using h3

-- Row 39: `uzp1_4s` (`X = lanes(Y.0, Y.2, Z.0, Z.2)`)
def effectUzp1_4s : List Ode.Stmt :=
  [.vset (.name "X") (.call "lanes" [.lane "Y" 0, .lane "Y" 2, .lane "Z" 0, .lane "Z" 2])]

def encodeUzp1_4s (x y z : Fin 32) : BitVec 32 :=
  0x4e801800#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

theorem agree_uzp1_4s (x y z : Fin 32) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeUzp1_4s x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectUzp1_4s, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let e0 := Arm64.getSimdLane vy 32 0; let e1 := Arm64.getSimdLane vy 32 2
  let e2 := Arm64.getSimdLane vz 32 0; let e3 := Arm64.getSimdLane vz 32 2
  let res : BitVec 128 := e0 ||| (e1 <<< 32) ||| (e2 <<< 64) ||| (e3 <<< 96)
  have hdec := encode_simdPermute_decode 0x4e801800#32 2#2 1#3 x y z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdPermute true 2#2 (BitVec.ofNat 5 z.val) 1#3 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp only [Arm64.execInstWithSvc, res, e0, e1, e2, e3, vy, vz]
    simp [List.range', List.foldl]
    exact congrArg (fun v => (gs.writeVReg128 _ v).advancePC) (bv_or4_swap _ _ _ _)
  have hex := pack4_32_extract e0 e1 e2 e3 (getSimdLane32_hi vy 0) (getSimdLane32_hi vy 2) (getSimdLane32_hi vz 0)
  apply agree_lanes_helper x bind prog u st gs next hA _
    (st.vec y.val 0) (st.vec y.val 2) (st.vec z.val 0) (st.vec z.val 2) _ _ res hdec
    (by simp [Ode.exec, Ode.execAll, Ode.execStmt, Ode.lanesOf, Ode.laneArg, hbx, hby, hbz]) hgs
    (by rw [hex.1, getSimdLane32_extract]; exact hA.vec y ⟨0, by decide⟩)
    (by rw [hex.2.1, getSimdLane32_extract]; exact hA.vec y ⟨2, by decide⟩)
    (by rw [hex.2.2.1, getSimdLane32_extract]; exact hA.vec z ⟨0, by decide⟩)
    (by rw [hex.2.2.2, getSimdLane32_extract]; exact hA.vec z ⟨2, by decide⟩)
    hnext hpc

-- Row 40: `uzp2_4s` (`X = lanes(Y.1, Y.3, Z.1, Z.3)`)
def effectUzp2_4s : List Ode.Stmt :=
  [.vset (.name "X") (.call "lanes" [.lane "Y" 1, .lane "Y" 3, .lane "Z" 1, .lane "Z" 3])]

def encodeUzp2_4s (x y z : Fin 32) : BitVec 32 :=
  0x4e805800#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

theorem agree_uzp2_4s (x y z : Fin 32) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeUzp2_4s x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectUzp2_4s, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let e0 := Arm64.getSimdLane vy 32 1; let e1 := Arm64.getSimdLane vy 32 3
  let e2 := Arm64.getSimdLane vz 32 1; let e3 := Arm64.getSimdLane vz 32 3
  let res : BitVec 128 := e0 ||| (e1 <<< 32) ||| (e2 <<< 64) ||| (e3 <<< 96)
  have hdec := encode_simdPermute_decode 0x4e805800#32 2#2 5#3 x y z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdPermute true 2#2 (BitVec.ofNat 5 z.val) 5#3 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp only [Arm64.execInstWithSvc, res, e0, e1, e2, e3, vy, vz]
    simp [List.range', List.foldl]
    exact congrArg (fun v => (gs.writeVReg128 _ v).advancePC) (bv_or4_swap _ _ _ _)
  have hex := pack4_32_extract e0 e1 e2 e3 (getSimdLane32_hi vy 1) (getSimdLane32_hi vy 3) (getSimdLane32_hi vz 1)
  apply agree_lanes_helper x bind prog u st gs next hA _
    (st.vec y.val 1) (st.vec y.val 3) (st.vec z.val 1) (st.vec z.val 3) _ _ res hdec
    (by simp [Ode.exec, Ode.execAll, Ode.execStmt, Ode.lanesOf, Ode.laneArg, hbx, hby, hbz]) hgs
    (by rw [hex.1, getSimdLane32_extract]; exact hA.vec y ⟨1, by decide⟩)
    (by rw [hex.2.1, getSimdLane32_extract]; exact hA.vec y ⟨3, by decide⟩)
    (by rw [hex.2.2.1, getSimdLane32_extract]; exact hA.vec z ⟨1, by decide⟩)
    (by rw [hex.2.2.2, getSimdLane32_extract]; exact hA.vec z ⟨3, by decide⟩)
    hnext hpc

-- Row 41: `zip1_4s` (`X = lanes(Y.0, Z.0, Y.1, Z.1)`)
def effectZip1_4s : List Ode.Stmt :=
  [.vset (.name "X") (.call "lanes" [.lane "Y" 0, .lane "Z" 0, .lane "Y" 1, .lane "Z" 1])]

def encodeZip1_4s (x y z : Fin 32) : BitVec 32 :=
  0x4e803800#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

theorem agree_zip1_4s (x y z : Fin 32) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeZip1_4s x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectZip1_4s, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let e0 := Arm64.getSimdLane vy 32 0; let e1 := Arm64.getSimdLane vz 32 0
  let e2 := Arm64.getSimdLane vy 32 1; let e3 := Arm64.getSimdLane vz 32 1
  let res : BitVec 128 := e0 ||| (e1 <<< 32) ||| (e2 <<< 64) ||| (e3 <<< 96)
  have hdec := encode_simdPermute_decode 0x4e803800#32 2#2 3#3 x y z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdPermute true 2#2 (BitVec.ofNat 5 z.val) 3#3 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp [Arm64.execInstWithSvc, List.range', List.foldl, res, e0, e1, e2, e3, vy, vz]
  have hex := pack4_32_extract e0 e1 e2 e3 (getSimdLane32_hi vy 0) (getSimdLane32_hi vz 0) (getSimdLane32_hi vy 1)
  apply agree_lanes_helper x bind prog u st gs next hA _
    (st.vec y.val 0) (st.vec z.val 0) (st.vec y.val 1) (st.vec z.val 1) _ _ res hdec
    (by simp [Ode.exec, Ode.execAll, Ode.execStmt, Ode.lanesOf, Ode.laneArg, hbx, hby, hbz]) hgs
    (by rw [hex.1, getSimdLane32_extract]; exact hA.vec y ⟨0, by decide⟩)
    (by rw [hex.2.1, getSimdLane32_extract]; exact hA.vec z ⟨0, by decide⟩)
    (by rw [hex.2.2.1, getSimdLane32_extract]; exact hA.vec y ⟨1, by decide⟩)
    (by rw [hex.2.2.2, getSimdLane32_extract]; exact hA.vec z ⟨1, by decide⟩)
    hnext hpc

-- Row 42: `zip2_4s` (`X = lanes(Y.2, Z.2, Y.3, Z.3)`)
def effectZip2_4s : List Ode.Stmt :=
  [.vset (.name "X") (.call "lanes" [.lane "Y" 2, .lane "Z" 2, .lane "Y" 3, .lane "Z" 3])]

def encodeZip2_4s (x y z : Fin 32) : BitVec 32 :=
  0x4e807800#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

theorem agree_zip2_4s (x y z : Fin 32) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeZip2_4s x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectZip2_4s, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let e0 := Arm64.getSimdLane vy 32 2; let e1 := Arm64.getSimdLane vz 32 2
  let e2 := Arm64.getSimdLane vy 32 3; let e3 := Arm64.getSimdLane vz 32 3
  let res : BitVec 128 := e0 ||| (e1 <<< 32) ||| (e2 <<< 64) ||| (e3 <<< 96)
  have hdec := encode_simdPermute_decode 0x4e807800#32 2#2 7#3 x y z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdPermute true 2#2 (BitVec.ofNat 5 z.val) 7#3 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp [Arm64.execInstWithSvc, List.range', List.foldl, res, e0, e1, e2, e3, vy, vz]
  have hex := pack4_32_extract e0 e1 e2 e3 (getSimdLane32_hi vy 2) (getSimdLane32_hi vz 2) (getSimdLane32_hi vy 3)
  apply agree_lanes_helper x bind prog u st gs next hA _
    (st.vec y.val 2) (st.vec z.val 2) (st.vec y.val 3) (st.vec z.val 3) _ _ res hdec
    (by simp [Ode.exec, Ode.execAll, Ode.execStmt, Ode.lanesOf, Ode.laneArg, hbx, hby, hbz]) hgs
    (by rw [hex.1, getSimdLane32_extract]; exact hA.vec y ⟨2, by decide⟩)
    (by rw [hex.2.1, getSimdLane32_extract]; exact hA.vec z ⟨2, by decide⟩)
    (by rw [hex.2.2.1, getSimdLane32_extract]; exact hA.vec y ⟨3, by decide⟩)
    (by rw [hex.2.2.2, getSimdLane32_extract]; exact hA.vec z ⟨3, by decide⟩)
    hnext hpc

-- Row 43: `zip1_2d` (`X = lanes(Y.0, Y.1, Z.0, Z.1)`)
def effectZip1_2d : List Ode.Stmt :=
  [.vset (.name "X") (.call "lanes" [.lane "Y" 0, .lane "Y" 1, .lane "Z" 0, .lane "Z" 1])]

def encodeZip1_2d (x y z : Fin 32) : BitVec 32 :=
  0x4ec03800#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

theorem agree_zip1_2d (x y z : Fin 32) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeZip1_2d x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectZip1_2d, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let e0 := Arm64.getSimdLane vy 64 0; let e1 := Arm64.getSimdLane vz 64 0
  let res : BitVec 128 := e0 ||| (e1 <<< 64)
  have hdec := encode_simdPermute_decode 0x4ec03800#32 3#2 3#3 x y z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdPermute true 3#2 (BitVec.ofNat 5 z.val) 3#3 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp [Arm64.execInstWithSvc, List.foldl, res, e0, e1, vy, vz]
  have hex := pack2_64_extract e0 e1 (getSimdLane64_hi vy 0)
  apply agree_lanes_helper x bind prog u st gs next hA _
    (st.vec y.val 0) (st.vec y.val 1) (st.vec z.val 0) (st.vec z.val 1) _ _ res hdec
    (by simp [Ode.exec, Ode.execAll, Ode.execStmt, Ode.lanesOf, Ode.laneArg, hbx, hby, hbz]) hgs
    (by rw [hex.1, getSimdLane64_extract0]; exact hA.vec y ⟨0, by decide⟩)
    (by rw [hex.2.1, getSimdLane64_extract1]; exact hA.vec y ⟨1, by decide⟩)
    (by rw [hex.2.2.1, getSimdLane64_extract0]; exact hA.vec z ⟨0, by decide⟩)
    (by rw [hex.2.2.2, getSimdLane64_extract1]; exact hA.vec z ⟨1, by decide⟩)
    hnext hpc

-- Row 44: `zip2_2d` (`X = lanes(Y.2, Y.3, Z.2, Z.3)`)
def effectZip2_2d : List Ode.Stmt :=
  [.vset (.name "X") (.call "lanes" [.lane "Y" 2, .lane "Y" 3, .lane "Z" 2, .lane "Z" 3])]

def encodeZip2_2d (x y z : Fin 32) : BitVec 32 :=
  0x4ec07800#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

theorem agree_zip2_2d (x y z : Fin 32) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeZip2_2d x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectZip2_2d, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let e0 := Arm64.getSimdLane vy 64 1; let e1 := Arm64.getSimdLane vz 64 1
  let res : BitVec 128 := e0 ||| (e1 <<< 64)
  have hdec := encode_simdPermute_decode 0x4ec07800#32 3#2 7#3 x y z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdPermute true 3#2 (BitVec.ofNat 5 z.val) 7#3 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp [Arm64.execInstWithSvc, List.foldl, res, e0, e1, vy, vz]
  have hex := pack2_64_extract e0 e1 (getSimdLane64_hi vy 1)
  apply agree_lanes_helper x bind prog u st gs next hA _
    (st.vec y.val 2) (st.vec y.val 3) (st.vec z.val 2) (st.vec z.val 3) _ _ res hdec
    (by simp [Ode.exec, Ode.execAll, Ode.execStmt, Ode.lanesOf, Ode.laneArg, hbx, hby, hbz]) hgs
    (by rw [hex.1, getSimdLane64_extract0]; exact hA.vec y ⟨2, by decide⟩)
    (by rw [hex.2.1, getSimdLane64_extract1]; exact hA.vec y ⟨3, by decide⟩)
    (by rw [hex.2.2.1, getSimdLane64_extract0]; exact hA.vec z ⟨2, by decide⟩)
    (by rw [hex.2.2.2, getSimdLane64_extract1]; exact hA.vec z ⟨3, by decide⟩)
    hnext hpc

-- ============================================================================
-- Rows 45-47: SIMD Extract (`ext_4`, `ext_8`, `ext_12`)
-- ============================================================================

def guardsBeforeSimdExt : List (BitVec 32 × BitVec 32) :=
  guardsBeforeSimdPermute ++ [ (0xbf208c00#32, 0x0e000800#32) ]

private theorem decode_at_simdExt {w base fixed : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hnop : ((base &&& fixed) == (0xd503201f#32 &&& fixed)) = false)
    (hskip : skipsAll base fixed guardsBeforeSimdExt = true)
    (hmatch : (0xbfe08400#32 &&& fixed = 0xbfe08400#32) ∧ (base &&& 0xbfe08400#32 = 0x2e000000#32)) :
    Arm64.decode w =
      some (.simdExt (w.getLsbD 30) (w.extractLsb' 16 5) (w.extractLsb' 11 4)
        (w.extractLsb' 5 5) (w.extractLsb' 0 5)) := by
  have sk : ∀ m c, (m, c) ∈ guardsBeforeSimdExt → ((w &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hw hskip hm
  have hhit : w &&& 0xbfe08400#32 = 0x2e000000#32 := by rw [mask_of_fixed hw hmatch.1, hmatch.2]
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
             sk 0xbfe00000#32 0x0dc00000#32 (by decide), sk 0xffffcc00#32 0x4e284800#32 (by decide),
             sk 0x7f20fc00#32 0x1e200000#32 (by decide), sk 0x9f800400#32 0x0f000400#32 (by decide),
             sk 0xbfe08c00#32 0x0e000000#32 (by decide), sk 0xfffffc00#32 0x5ef1b800#32 (by decide),
             sk 0xffe0fc00#32 0x5e000400#32 (by decide), sk 0x9fe08400#32 0x0e000400#32 (by decide),
             sk 0x9f200400#32 0x0e200400#32 (by decide), sk 0x9f3e0c00#32 0x0e200800#32 (by decide),
             sk 0x9f3e0c00#32 0x0e300800#32 (by decide), sk 0xbf208c00#32 0x0e000800#32 (by decide),
             hhit, beq_self_eq_true, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

private theorem decode_simdExt_word (base : BitVec 32) (imm4 : BitVec 4) (x y z : Fin 32)
    (hbz : base.extractLsb' 16 5 = 0#5) (hby : base.extractLsb' 5 5 = 0#5) (hbx : base.extractLsb' 0 5 = 0#5)
    (hskip : skipsAll base 0xffe0fc00#32 guardsBeforeSimdExt = true)
    (hnop : ((base &&& 0xffe0fc00#32) == (0xd503201f#32 &&& 0xffe0fc00#32)) = false)
    (hmatch : base &&& 0xbfe08400#32 = 0x2e000000#32)
    (hq : base.getLsbD 30 = true)
    (himm : base.extractLsb' 11 4 = imm4) :
    Arm64.decode (base ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val) =
      some (.simdExt true (BitVec.ofNat 5 z.val) imm4 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) := by
  have hz : z.val < 2 ^ 5 := z.isLt; have hy : y.val < 2 ^ 5 := y.isLt; have hx : x.val < 2 ^ 5 := x.isLt
  let w := base ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val
  have hf : w &&& 0xffe0fc00#32 = base &&& 0xffe0fc00#32 := by
    have h1 : (BitVec.ofNat 32 z.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hz (by decide)
    have h2 : (BitVec.ofNat 32 y.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hy (by decide)
    have h3 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold w; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_simdExt hf hnop hskip ⟨by decide, hmatch⟩]
  have ex_z : w.extractLsb' 16 5 = BitVec.ofNat 5 z.val := by
    unfold w; simp only [extract_or, hbz]
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 z.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h1, h2, h3]; simp
  have ex_y : w.extractLsb' 5 5 = BitVec.ofNat 5 y.val := by
    unfold w; simp only [extract_or, hby]
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 y.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h1, h2, h3]; simp
  have ex_x : w.extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold w; simp only [extract_or, hbx]
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h1, h2, h3]; simp
  have hq' : w.getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide), hq]
  have himm' : w.extractLsb' 11 4 = imm4 := by rw [extract_of_fixed hf (by decide), himm]
  rw [hq', himm', ex_z, ex_y, ex_x]

private theorem ext_lane_low (vy vz : BitVec 128) (sh k : Nat) (h : sh + k < 4) :
    (((vz ++ vy) >>> (32 * sh)).truncate 128).extractLsb' (32 * k) 32 =
      vy.extractLsb' (32 * (sh + k)) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.truncate, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
             BitVec.getLsbD_append, hj, decide_true, Bool.true_and,
             show 32 * k + j < 128 by omega, show 32 * sh + (32 * k + j) < 128 by omega, ↓reduceIte]
  exact congrArg vy.getLsbD (by omega)

private theorem ext_lane_high (vy vz : BitVec 128) (sh k : Nat) (hlo : 4 ≤ sh + k) (hhi : sh + k < 8) (hk : k < 4) :
    (((vz ++ vy) >>> (32 * sh)).truncate 128).extractLsb' (32 * k) 32 =
      vz.extractLsb' (32 * (sh + k - 4)) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.truncate, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
             BitVec.getLsbD_append, hj, decide_true, Bool.true_and,
             show 32 * k + j < 128 by omega, show ¬(32 * sh + (32 * k + j) < 128) by omega, ↓reduceIte]
  exact congrArg vz.getLsbD (by omega)

-- Row 45: `ext_4` (`X = lanes(Y.1, Y.2, Y.3, Z.0)`)
def effectExt4 : List Ode.Stmt :=
  [.vset (.name "X") (.call "lanes" [.lane "Y" 1, .lane "Y" 2, .lane "Y" 3, .lane "Z" 0])]

def encodeExt4 (x y z : Fin 32) : BitVec 32 :=
  0x6e002000#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

theorem agree_ext_4 (x y z : Fin 32) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeExt4 x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectExt4, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let res : BitVec 128 := ((vz ++ vy) >>> 32).truncate 128
  have hdec := decode_simdExt_word 0x6e002000#32 4#4 x y z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdExt true (BitVec.ofNat 5 z.val) 4#4 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp [Arm64.execInstWithSvc, res, vy, vz]
  apply agree_lanes_helper x bind prog u st gs next hA _
    (st.vec y.val 1) (st.vec y.val 2) (st.vec y.val 3) (st.vec z.val 0) _ _ res hdec
    (by simp [Ode.exec, Ode.execAll, Ode.execStmt, Ode.lanesOf, Ode.laneArg, hbx, hby, hbz]) hgs
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_low vy vz 1 0 (by omega))).trans (hA.vec y ⟨1, by decide⟩))
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_low vy vz 1 1 (by omega))).trans (hA.vec y ⟨2, by decide⟩))
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_low vy vz 1 2 (by omega))).trans (hA.vec y ⟨3, by decide⟩))
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_high vy vz 1 3 (by omega) (by omega) (by omega))).trans (hA.vec z ⟨0, by decide⟩))
    hnext hpc

-- Row 46: `ext_8` (`X = lanes(Y.2, Y.3, Z.0, Z.1)`)
def effectExt8 : List Ode.Stmt :=
  [.vset (.name "X") (.call "lanes" [.lane "Y" 2, .lane "Y" 3, .lane "Z" 0, .lane "Z" 1])]

def encodeExt8 (x y z : Fin 32) : BitVec 32 :=
  0x6e004000#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

theorem agree_ext_8 (x y z : Fin 32) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeExt8 x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectExt8, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let res : BitVec 128 := ((vz ++ vy) >>> 64).truncate 128
  have hdec := decode_simdExt_word 0x6e004000#32 8#4 x y z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdExt true (BitVec.ofNat 5 z.val) 8#4 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp [Arm64.execInstWithSvc, res, vy, vz]
  apply agree_lanes_helper x bind prog u st gs next hA _
    (st.vec y.val 2) (st.vec y.val 3) (st.vec z.val 0) (st.vec z.val 1) _ _ res hdec
    (by simp [Ode.exec, Ode.execAll, Ode.execStmt, Ode.lanesOf, Ode.laneArg, hbx, hby, hbz]) hgs
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_low vy vz 2 0 (by omega))).trans (hA.vec y ⟨2, by decide⟩))
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_low vy vz 2 1 (by omega))).trans (hA.vec y ⟨3, by decide⟩))
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_high vy vz 2 2 (by omega) (by omega) (by omega))).trans (hA.vec z ⟨0, by decide⟩))
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_high vy vz 2 3 (by omega) (by omega) (by omega))).trans (hA.vec z ⟨1, by decide⟩))
    hnext hpc

-- Row 47: `ext_12` (`X = lanes(Y.3, Z.0, Z.1, Z.2)`)
def effectExt12 : List Ode.Stmt :=
  [.vset (.name "X") (.call "lanes" [.lane "Y" 3, .lane "Z" 0, .lane "Z" 1, .lane "Z" 2])]

def encodeExt12 (x y z : Fin 32) : BitVec 32 :=
  0x6e006000#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

theorem agree_ext_12 (x y z : Fin 32) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeExt12 x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectExt12, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let res : BitVec 128 := ((vz ++ vy) >>> 96).truncate 128
  have hdec := decode_simdExt_word 0x6e006000#32 12#4 x y z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdExt true (BitVec.ofNat 5 z.val) 12#4 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp [Arm64.execInstWithSvc, res, vy, vz]
  apply agree_lanes_helper x bind prog u st gs next hA _
    (st.vec y.val 3) (st.vec z.val 0) (st.vec z.val 1) (st.vec z.val 2) _ _ res hdec
    (by simp [Ode.exec, Ode.execAll, Ode.execStmt, Ode.lanesOf, Ode.laneArg, hbx, hby, hbz]) hgs
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_low vy vz 3 0 (by omega))).trans (hA.vec y ⟨3, by decide⟩))
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_high vy vz 3 1 (by omega) (by omega) (by omega))).trans (hA.vec z ⟨0, by decide⟩))
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_high vy vz 3 2 (by omega) (by omega) (by omega))).trans (hA.vec z ⟨1, by decide⟩))
    (by simpa [res] using (congrArg BitVec.toNat (ext_lane_high vy vz 3 3 (by omega) (by omega) (by omega))).trans (hA.vec z ⟨2, by decide⟩))
    hnext hpc

-- ============================================================================
-- Row 48: `lsr_ri` (`lsr D64, S64, I` -> `D = shr64(S, I)`, 0 <= I <= 63)
-- ============================================================================

def effectLsrRi : List Ode.Stmt :=
  [.set (.name "D") (.call "shr64" [.name "S", .name "I"])]

def encodeLsrRi (d s : Fin 31) (sh : Fin 64) : BitVec 32 :=
  0xd340fc00#32 ||| (BitVec.ofNat 32 sh.val <<< 16) ||| (BitVec.ofNat 32 s.val <<< 5) ||| BitVec.ofNat 32 d.val

theorem decode_lsr_ri (d s : Fin 31) (sh : Fin 64) :
    Arm64.decode (encodeLsrRi d s sh) =
      some (.bitfield .W64 .UBFM (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val))
        sh.val 63) := by
  have hr : sh.val < 2 ^ 6 := sh.isLt
  have hs : s.val < 2 ^ 5 := by omega
  have hd : d.val < 2 ^ 5 := by omega
  have hf : encodeLsrRi d s sh &&& 0xffc0fc00#32 = 0xd340fc00#32 &&& 0xffc0fc00#32 := by
    have h1 : (BitVec.ofNat 32 sh.val <<< 16) &&& 0xffc0fc00#32 = 0#32 := field_and_eq_zero hr (by decide)
    have h2 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xffc0fc00#32 = 0#32 := field_and_eq_zero hs (by decide)
    have h3 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffc0fc00#32 = 0#32 := field_and_eq_zero hd (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeLsrRi; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  have sk : ∀ m c, (m, c) ∈ guardsBeforeBitfield → ((encodeLsrRi d s sh &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hf (by decide) hm
  have hnop : (encodeLsrRi d s sh == 0xd503201f#32) = false := word_ne_of_fixed hf (by decide)
  have hhit : encodeLsrRi d s sh &&& 0x1f800000#32 = 0x13000000#32 := by
    rw [mask_of_fixed hf (by decide)]; decide
  have hsf : (encodeLsrRi d s sh).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hopc : ((encodeLsrRi d s sh).extractLsb' 29 2).toNat = 2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hn : (encodeLsrRi d s sh).getLsbD 22 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have ex_s' : (encodeLsrRi d s sh).extractLsb' 10 6 = 63#6 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_r : (encodeLsrRi d s sh).extractLsb' 16 6 = BitVec.ofNat 6 sh.val := by
    unfold encodeLsrRi; simp only [extract_or]
    have h0 : (0xd340fc00#32).extractLsb' 16 6 = 0#6 := by decide
    have h1 : (BitVec.ofNat 32 sh.val <<< 16).extractLsb' 16 6 = BitVec.ofNat 6 sh.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 16 6 = 0#6 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 16 6 = 0#6 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_s : (encodeLsrRi d s sh).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeLsrRi; simp only [extract_or]
    have h0 : (0xd340fc00#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 sh.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hr (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_d : (encodeLsrRi d s sh).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeLsrRi; simp only [extract_or]
    have h0 : (0xd340fc00#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 sh.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hr (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  unfold Arm64.decode
  simp only [hnop,
             sk 0xffe0001f#32 0xd4000001#32 (by decide), sk 0xffe0001f#32 0xd4200000#32 (by decide),
             sk 0xfffff01f#32 0xd503201f#32 (by decide), sk 0xffff0000#32 0x00000000#32 (by decide),
             sk 0xffffffe0#32 0xd50b7420#32 (by decide), sk 0x1f000000#32 0x10000000#32 (by decide),
             hhit,
             show (0x13000000#32 == 0x11000000#32) = false by decide,
             show (0x13000000#32 == 0x12000000#32) = false by decide,
             show (0x13000000#32 == 0x12800000#32) = false by decide,
             beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
             Arm64.RegWidth.ofBool, hsf, hopc, hn, ex_r, ex_s', ex_s, ex_d,
             fromZRBits_fin31, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hr]

theorem agree_lsr_ri (d s : Fin 31) (sh : Fin 64) (numStr : String)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnum : Ode.readInt numStr = some (sh.val : Int))
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeLsrRi d s sh) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectLsrRi, bindRri d s numStr, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hshlt : sh.val < Ode.M64 := by unfold Ode.M64; have := sh.isLt; omega
  have hmod : ((sh.val : Int) % (Ode.M64 : Int)).toNat = sh.val := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hshlt)]; rfl
  have hsmod : st.reg (armSlot s.val) % Ode.M64 = st.reg (armSlot s.val) := by
    have hs' : st.reg (armSlot s.val) < Ode.M64 := by
      rw [← hA.gpr s]; exact (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val))).isLt
    exact Nat.mod_eq_of_lt hs'
  let val := st.reg (armSlot s.val) >>> sh.val
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) val
  let st' : Ode.State := Ode.noted (bindRri d s numStr) st0 (.set (.name "D") (.call "shr64" [.name "S", .name "I"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectLsrRi, bindRri d s numStr, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectLsrRi, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.prim,
          Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindRri, List.lookup,
          regIndex_armRegName, hnum, hmod, hsmod, val, st', st1, st0]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.bitfield .W64 .UBFM (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) sh.val 63) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) >>> sh.val)).advancePC := by
    have hrm : sh.val % 64 = sh.val := Nat.mod_eq_of_lt sh.isLt
    simp [Arm64.execInstWithSvc, Arm64.execBitfield, Arm64.evalBitfield,
          Arm64.State.writeReg, Arm64.State.readReg, hrm,
          show (Arm64.BitfieldOp.UBFM == Arm64.BitfieldOp.UBFM) = true by decide]
  refine ⟨_, st', decode_lsr_ri d s sh, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  have hgv : (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) >>> sh.val).toNat = val := by
    rw [BitVec.toNat_ushiftRight, hA.gpr s]
  exact agreeState_writeGpr hA d (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) >>> sh.val) val hgv _ _ hnext hpc

-- ============================================================================
-- Row 49: `orr_rrr` (`orr D64, S64, P64` -> `D = or64(S, P)`)
-- ============================================================================

def effectOrrRrr : List Ode.Stmt :=
  [.set (.name "D") (.call "or64" [.name "S", .name "P"])]

def encodeOrrRrr (d s p : Fin 31) : BitVec 32 :=
  0xaa000000#32 ||| (BitVec.ofNat 32 p.val <<< 16) ||| (BitVec.ofNat 32 s.val <<< 5) ||| BitVec.ofNat 32 d.val

theorem decode_orr_rrr (d s p : Fin 31) :
    Arm64.decode (encodeOrrRrr d s p) =
      some (.logicalShift .W64 .ORR (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0) := by
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have hp : p.val < 2 ^ 5 := by omega
  have hf : encodeOrrRrr d s p &&& 0xffe0fc00#32 = 0xaa000000#32 &&& 0xffe0fc00#32 := by
    have h1 : (BitVec.ofNat 32 p.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hp (by decide)
    have h2 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hs (by decide)
    have h3 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hd (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeOrrRrr; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  have ex_d : (encodeOrrRrr d s p).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeOrrRrr; simp only [extract_or]
    have h0 : (0xaa000000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_s : (encodeOrrRrr d s p).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeOrrRrr; simp only [extract_or]
    have h0 : (0xaa000000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_p : (encodeOrrRrr d s p).extractLsb' 16 5 = BitVec.ofNat 5 p.val := by
    unfold encodeOrrRrr; simp only [extract_or]
    have h0 : (0xaa000000#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 p.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have hsf : (encodeOrrRrr d s p).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hopc : (encodeOrrRrr d s p).extractLsb' 29 2 = 1#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hsh : (encodeOrrRrr d s p).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hnbit : (encodeOrrRrr d s p).getLsbD 21 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have himm6 : (encodeOrrRrr d s p).extractLsb' 10 6 = 0#6 := by rw [extract_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             hsf, hopc, hsh, hnbit, himm6, ex_d, ex_s, ex_p, fromZRBits_fin31,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
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
             mask_of_fixed hf (m := 0x1f000000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_orr_rrr (d s p : Fin 31)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeOrrRrr d s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectOrrRrr, bindAddRrr d s p, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let val := (st.reg (armSlot s.val) ||| st.reg (armSlot p.val)) % Ode.M64
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) val
  let st' : Ode.State := Ode.noted (bindAddRrr d s p) st0 (.set (.name "D") (.call "or64" [.name "S", .name "P"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectOrrRrr, bindAddRrr d s p, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectOrrRrr, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.prim,
          Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindAddRrr, List.lookup,
          regIndex_armRegName, val, st', st1, st0]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.logicalShift .W64 .ORR (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val))
        (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) ||| gs.readReg64 (.gpr (BitVec.ofNat 5 p.val)))).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execLogicalShift, Arm64.evalLogical, Arm64.shiftVal, Arm64.shift64,
          Arm64.State.readReg, Arm64.State.readReg64, Arm64.State.writeReg]
  refine ⟨_, st', decode_orr_rrr d s p, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  have hgv : (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) ||| gs.readReg64 (.gpr (BitVec.ofNat 5 p.val))).toNat = val := by
    rw [BitVec.toNat_or, hA.gpr s, hA.gpr p]
    have hlt : (st.reg (armSlot s.val) ||| st.reg (armSlot p.val)) < Ode.M64 := by
      have hs' : st.reg (armSlot s.val) < 2 ^ 64 := by rw [← hA.gpr s]; exact (gs.readReg64 _).isLt
      have hp' : st.reg (armSlot p.val) < 2 ^ 64 := by rw [← hA.gpr p]; exact (gs.readReg64 _).isLt
      exact Nat.or_lt_two_pow hs' hp'
    exact (Nat.mod_eq_of_lt hlt).symm
  exact agreeState_writeGpr hA d _ val hgv _ _ hnext hpc

-- ============================================================================
-- Row 50: `and_rrr` (`and D64, S64, P64` -> `D = and64(S, P)`)
-- ============================================================================

def effectAndRrr : List Ode.Stmt :=
  [.set (.name "D") (.call "and64" [.name "S", .name "P"])]

def encodeAndRrr (d s p : Fin 31) : BitVec 32 :=
  0x8a000000#32 ||| (BitVec.ofNat 32 p.val <<< 16) ||| (BitVec.ofNat 32 s.val <<< 5) ||| BitVec.ofNat 32 d.val

theorem decode_and_rrr (d s p : Fin 31) :
    Arm64.decode (encodeAndRrr d s p) =
      some (.logicalShift .W64 .AND (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0) := by
  have hd : d.val < 2 ^ 5 := by omega
  have hs : s.val < 2 ^ 5 := by omega
  have hp : p.val < 2 ^ 5 := by omega
  have hf : encodeAndRrr d s p &&& 0xffe0fc00#32 = 0x8a000000#32 &&& 0xffe0fc00#32 := by
    have h1 : (BitVec.ofNat 32 p.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hp (by decide)
    have h2 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hs (by decide)
    have h3 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hd (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeAndRrr; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  have ex_d : (encodeAndRrr d s p).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeAndRrr; simp only [extract_or]
    have h0 : (0x8a000000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_s : (encodeAndRrr d s p).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeAndRrr; simp only [extract_or]
    have h0 : (0x8a000000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_p : (encodeAndRrr d s p).extractLsb' 16 5 = BitVec.ofNat 5 p.val := by
    unfold encodeAndRrr; simp only [extract_or]
    have h0 : (0x8a000000#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 p.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hs (by omega)
    have h3 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have hsf : (encodeAndRrr d s p).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hopc : (encodeAndRrr d s p).extractLsb' 29 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hsh : (encodeAndRrr d s p).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hnbit : (encodeAndRrr d s p).getLsbD 21 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have himm6 : (encodeAndRrr d s p).extractLsb' 10 6 = 0#6 := by rw [extract_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
             hsf, hopc, hsh, hnbit, himm6, ex_d, ex_s, ex_p, fromZRBits_fin31,
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4000001#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffe0001f#32) (c := 0xd4200000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xfffff01f#32) (c := 0xd503201f#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffff0000#32) (c := 0x00000000#32) (by decide),
             mask_ne_of_fixed hf (m := 0xffffffe0#32) (c := 0xd50b7420#32) (by decide),
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
             mask_of_fixed hf (m := 0x1f000000#32) (by decide),
             Bool.false_eq_true, ↓reduceIte]
  rfl

theorem agree_and_rrr (d s p : Fin 31)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeAndRrr d s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectAndRrr, bindAddRrr d s p, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let val := (st.reg (armSlot s.val) &&& st.reg (armSlot p.val)) % Ode.M64
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) val
  let st' : Ode.State := Ode.noted (bindAddRrr d s p) st0 (.set (.name "D") (.call "and64" [.name "S", .name "P"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectAndRrr, bindAddRrr d s p, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectAndRrr, Ode.execStmt, Ode.isUnknown, Ode.value, Ode.values, Ode.prim,
          Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, bindAddRrr, List.lookup,
          regIndex_armRegName, val, st', st1, st0]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.logicalShift .W64 .AND (.gpr (BitVec.ofNat 5 d.val)) (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) .LSL 0) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val))
        (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) &&& gs.readReg64 (.gpr (BitVec.ofNat 5 p.val)))).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execLogicalShift, Arm64.evalLogical, Arm64.shiftVal, Arm64.shift64,
          Arm64.State.readReg, Arm64.State.readReg64, Arm64.State.writeReg]
  refine ⟨_, st', decode_and_rrr d s p, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  have hgv : (gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) &&& gs.readReg64 (.gpr (BitVec.ofNat 5 p.val))).toNat = val := by
    rw [BitVec.toNat_and, hA.gpr s, hA.gpr p]
    have hlt : (st.reg (armSlot s.val) &&& st.reg (armSlot p.val)) < Ode.M64 := by
      have hs' : st.reg (armSlot s.val) < 2 ^ 64 := by rw [← hA.gpr s]; exact (gs.readReg64 _).isLt
      have hp' : st.reg (armSlot p.val) < 2 ^ 64 := by rw [← hA.gpr p]; exact (gs.readReg64 _).isLt
      exact Nat.and_lt_two_pow _ hp'
    exact (Nat.mod_eq_of_lt hlt).symm
  exact agreeState_writeGpr hA d _ val hgv _ _ hnext hpc

/-! ## Rows 51–54: `ldr128`, `str128`, `ldr128_sp`, `str128_sp` (128-bit vector load/store with scaled immediate offset) -/

def guardsBeforeSimdLdStImm : List (BitVec 32 × BitVec 32) :=
  guardsBeforeSimdThreeSame.take 48

private theorem decode_at_simdLdStImm {w base fixed : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hnop : ((base &&& fixed) == (0xd503201f#32 &&& fixed)) = false)
    (hskip : skipsAll base fixed guardsBeforeSimdLdStImm = true)
    (hmatch : (0x3f000000#32 &&& fixed = 0x3f000000#32) ∧ (base &&& 0x3f000000#32 = 0x3d000000#32)) :
    Arm64.decode w =
      match Arm64.decodeSimdLoadStoreType (w.extractLsb' 30 2).toNat (w.extractLsb' 22 2).toNat with
      | some (isLoad, sz, scale) =>
        let offset : BitVec 64 := ((w.extractLsb' 10 12).zeroExtend 64) <<< scale
        let addr := Arm64.AddrMode.Offset (Arm64.Reg.fromSPBits (w.extractLsb' 5 5)) offset
        if isLoad then some (.ldrSimd sz (w.extractLsb' 0 5) addr)
        else some (.strSimd sz (w.extractLsb' 0 5) addr)
      | none => none := by
  have sk : ∀ m c, (m, c) ∈ guardsBeforeSimdLdStImm → ((w &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hw hskip hm
  have hhit : w &&& 0x3f000000#32 = 0x3d000000#32 := by rw [mask_of_fixed hw hmatch.1, hmatch.2]
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
             Bool.false_eq_true, ↓reduceIte]
  rw [hhit]
  simp only [beq_self_eq_true, ↓reduceIte]
  rfl

private theorem write128_eq_store16 {st : Ode.State} {gs : Arm64.State} {a : Nat}
    (hA : AgreeState st gs) (x : Fin 32) (hfit : a + 16 ≤ Ode.M64) {addr : Nat} (haddr : addr < Ode.M64) :
    let vx := gs.readVReg128 (BitVec.ofNat 5 x.val)
    let mem' := Ode.store (Ode.store (Ode.store (Ode.store st.mem a (st.vec x.val 0) 4)
                  (a + 4) (st.vec x.val 1) 4) (a + 8) (st.vec x.val 2) 4) (a + 12) (st.vec x.val 3) 4
    ((gs.mem.write128 (BitVec.ofNat 64 a) vx).read8 (BitVec.ofNat 64 addr)).toNat = (mem' addr).val := by
  intro vx mem'
  have hadd8 : BitVec.ofNat 64 a + 8#64 = BitVec.ofNat 64 (a + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    unfold Ode.M64 at hfit
    rw [Nat.mod_eq_of_lt (by omega), show 8 % 2 ^ 64 = 8 by decide, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hlo64 : (vx.extractLsb' 0 64).toNat = st.vec x.val 0 + 2 ^ 32 * st.vec x.val 1 := by
    have h0 := hA.vec x ⟨0, by decide⟩; have h1 := hA.vec x ⟨1, by decide⟩
    have hv0 : (vx.extractLsb' 0 64).extractLsb' 0 32 = vx.extractLsb' 0 32 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]
    have hv1 : (vx.extractLsb' 0 64).extractLsb' 32 32 = vx.extractLsb' 32 32 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]
    have hloLt : (vx.extractLsb' 0 64).toNat < 2 ^ 64 := (vx.extractLsb' 0 64).isLt
    have e0 := congrArg BitVec.toNat hv0; have e1 := congrArg BitVec.toNat hv1
    rw [BitVec.extractLsb'_toNat] at e0 e1; simp only [Nat.shiftRight_eq_div_pow] at e0 e1
    change (vx.extractLsb' 0 32).toNat = st.vec x.val 0 at h0
    change (vx.extractLsb' 32 32).toNat = st.vec x.val 1 at h1
    omega
  have hhi64 : (vx.extractLsb' 64 64).toNat = st.vec x.val 2 + 2 ^ 32 * st.vec x.val 3 := by
    have h2 := hA.vec x ⟨2, by decide⟩; have h3 := hA.vec x ⟨3, by decide⟩
    have hv2 : (vx.extractLsb' 64 64).extractLsb' 0 32 = vx.extractLsb' 64 32 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk, show k < 64 by omega]
    have hv3 : (vx.extractLsb' 64 64).extractLsb' 32 32 = vx.extractLsb' 96 32 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk, show 32 + k < 64 by omega, show 64 + (32 + k) = 96 + k by omega]
    have hhiLt : (vx.extractLsb' 64 64).toNat < 2 ^ 64 := (vx.extractLsb' 64 64).isLt
    have e2 := congrArg BitVec.toNat hv2; have e3 := congrArg BitVec.toNat hv3
    rw [BitVec.extractLsb'_toNat] at e2 e3; simp only [Nat.shiftRight_eq_div_pow] at e2 e3
    change (vx.extractLsb' 64 32).toNat = st.vec x.val 2 at h2
    change (vx.extractLsb' 96 32).toNat = st.vec x.val 3 at h3
    omega
  have hstore8 : ∀ m p w0 w1 (hw0 : w0 < 2 ^ 32) addr,
      (Ode.store (Ode.store m p w0 4) (p + 4) w1 4 addr).val =
      (Ode.store m p (w0 + 2 ^ 32 * w1) 8 addr).val := by
    intro m p w0 w1 hw0 addr
    rw [store_at, store_at, store_at]
    by_cases hhi : p + 4 ≤ addr ∧ addr < p + 4 + 4
    · simp only [hhi, show p ≤ addr ∧ addr < p + 8 by omega, and_self, ↓reduceIte]
      have hk : addr - p = 4 + (addr - (p + 4)) := by omega
      rw [hk, Nat.pow_add, show (256 : Nat) ^ 4 = 2 ^ 32 by decide, ← Nat.div_div_eq_div_mul]
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 32), Nat.div_eq_of_lt hw0, Nat.zero_add]
    · simp only [hhi, ↓reduceIte]
      by_cases hlo : p ≤ addr ∧ addr < p + 4
      · simp only [hlo, show p ≤ addr ∧ addr < p + 8 by omega, and_self, ↓reduceIte]
        have hd : 256 ^ (addr - p) * 256 ∣ 2 ^ 32 := by
          have : addr - p + 1 ≤ 4 := by omega
          have := Nat.pow_dvd_pow 256 this
          simpa [Nat.pow_succ] using this
        obtain ⟨q, hq⟩ := hd
        have hq2 : 2 ^ 32 * w1 = 256 ^ (addr - p) * (256 * (q * w1)) := by
          rw [hq, Nat.mul_assoc, Nat.mul_assoc]
        have hpos : 0 < 256 ^ (addr - p) := Nat.pow_pos (by decide)
        rw [hq2, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
      · simp only [hlo, show ¬(p ≤ addr ∧ addr < p + 8) by omega, ↓reduceIte]
  have hw0 : st.vec x.val 0 < 2 ^ 32 := by rw [← hA.vec x ⟨0, by decide⟩]; exact (vx.extractLsb' 0 32).isLt
  have hw2 : st.vec x.val 2 < 2 ^ 32 := by rw [← hA.vec x ⟨2, by decide⟩]; exact (vx.extractLsb' 64 32).isLt
  let stMid : Ode.State := { st with mem := Ode.store st.mem a (st.vec x.val 0 + 2 ^ 32 * st.vec x.val 1) 8 }
  let gsMid : Arm64.State := gs.setMem (gs.mem.write64 (BitVec.ofNat 64 a) (vx.extractLsb' 0 64))
  have hMid : AgreeState stMid gsMid :=
    ⟨hA.running, hA.gpr, hA.sp, hA.vec,
     fun p hp => write64_eq_store hA (by omega) (vx.extractLsb' 0 64) _ hlo64 hp,
     hA.pc, hA.zf, hA.cf⟩
  have hstep2 := write64_eq_store hMid (a := a + 8) (by omega) (vx.extractLsb' 64 64) _ hhi64 haddr
  unfold Arm64.Memory.write128
  rw [hadd8]
  change ((gsMid.mem.write64 (BitVec.ofNat 64 (a + 8)) (vx.extractLsb' 64 64)).read8 (BitVec.ofNat 64 addr)).toNat = _
  rw [hstep2]
  change (Ode.store (Ode.store st.mem a (st.vec x.val 0 + 2 ^ 32 * st.vec x.val 1) 8) (a + 8) (st.vec x.val 2 + 2 ^ 32 * st.vec x.val 3) 8 addr).val = (mem' addr).val
  have h1 := hstore8 st.mem a (st.vec x.val 0) (st.vec x.val 1) hw0
  have heqm : Ode.store (Ode.store st.mem a (st.vec x.val 0) 4) (a + 4) (st.vec x.val 1) 4 =
              Ode.store st.mem a (st.vec x.val 0 + 2 ^ 32 * st.vec x.val 1) 8 := by
    funext p; exact Fin.ext (h1 p)
  have h2 := hstore8 (Ode.store st.mem a (st.vec x.val 0 + 2 ^ 32 * st.vec x.val 1) 8) (a + 8) (st.vec x.val 2) (st.vec x.val 3) hw2 addr
  simpa [mem', heqm, show a + 8 + 4 = a + 12 by omega] using h2.symm

def encodeLdr128 (x : Fin 32) (b : Fin 31) (n : Fin 4096) : BitVec 32 :=
  0x3dc00000#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| (BitVec.ofNat 32 b.val <<< 5) ||| BitVec.ofNat 32 x.val

def encodeStr128 (x : Fin 32) (b : Fin 31) (n : Fin 4096) : BitVec 32 :=
  0x3d800000#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| (BitVec.ofNat 32 b.val <<< 5) ||| BitVec.ofNat 32 x.val

def encodeLdr128Sp (x : Fin 32) (n : Fin 4096) : BitVec 32 :=
  0x3dc003e0#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| BitVec.ofNat 32 x.val

def encodeStr128Sp (x : Fin 32) (n : Fin 4096) : BitVec 32 :=
  0x3d8003e0#32 ||| (BitVec.ofNat 32 n.val <<< 10) ||| BitVec.ofNat 32 x.val

def effectLdr128 : List Ode.Stmt :=
  [.vset (.name "X") (.call "mem128" [.name "B", .name "N"])]

def effectStr128 : List Ode.Stmt :=
  [.vset (.call "mem128" [.name "B", .name "N"]) (.name "X")]

def effectLdr128Sp : List Ode.Stmt :=
  [.vset (.name "X") (.call "mem128" [.call "on16" [.name "sp"], .name "N"])]

def effectStr128Sp : List Ode.Stmt :=
  [.vset (.call "mem128" [.call "on16" [.name "sp"], .name "N"]) (.name "X")]

private theorem shift4_imm12 (n : Fin 4096) :
    (BitVec.ofNat 12 n.val).zeroExtend 64 <<< 4 = BitVec.ofNat 64 (n.val * 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have := n.isLt; omega

theorem decode_ldr128 (x : Fin 32) (b : Fin 31) (n : Fin 4096) :
    Arm64.decode (encodeLdr128 x b n) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 x.val) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 16)))) := by
  have hx : x.val < 2 ^ 5 := x.isLt
  have hb : b.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := n.isLt
  have hf : encodeLdr128 x b n &&& 0xffc00000#32 = 0x3dc00000#32 &&& 0xffc00000#32 := by
    have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hn (by decide)
    have h2 : (BitVec.ofNat 32 b.val <<< 5) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hb (by decide)
    have h3 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeLdr128; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_simdLdStImm hf (by decide) (by decide) ⟨by decide, by decide⟩]
  have ex_x : (encodeLdr128 x b n).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeLdr128; simp only [extract_or]
    have h0 : (0x3dc00000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_b : (encodeLdr128 x b n).extractLsb' 5 5 = BitVec.ofNat 5 b.val := by
    unfold encodeLdr128; simp only [extract_or]
    have h0 : (0x3dc00000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 b.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_n : (encodeLdr128 x b n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeLdr128; simp only [extract_or]
    have h0 : (0x3dc00000#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 10 12 = 0#12 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_sz : (encodeLdr128 x b n).extractLsb' 30 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeLdr128 x b n).extractLsb' 22 2 = 3#2 := by rw [extract_of_fixed hf (by decide)]; decide
  simp only [ex_sz, ex_opc, ex_n, ex_b, ex_x, fromSPBits_fin31, BitVec.toNat_ofNat, Arm64.decodeSimdLoadStoreType]
  rw [shift4_imm12 n]; rfl

theorem decode_str128 (x : Fin 32) (b : Fin 31) (n : Fin 4096) :
    Arm64.decode (encodeStr128 x b n) =
      some (.strSimd .Q128 (BitVec.ofNat 5 x.val) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 16)))) := by
  have hx : x.val < 2 ^ 5 := x.isLt
  have hb : b.val < 2 ^ 5 := by omega
  have hn : n.val < 2 ^ 12 := n.isLt
  have hf : encodeStr128 x b n &&& 0xffc00000#32 = 0x3d800000#32 &&& 0xffc00000#32 := by
    have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hn (by decide)
    have h2 : (BitVec.ofNat 32 b.val <<< 5) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hb (by decide)
    have h3 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffc00000#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeStr128; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_simdLdStImm hf (by decide) (by decide) ⟨by decide, by decide⟩]
  have ex_x : (encodeStr128 x b n).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeStr128; simp only [extract_or]
    have h0 : (0x3d800000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_b : (encodeStr128 x b n).extractLsb' 5 5 = BitVec.ofNat 5 b.val := by
    unfold encodeStr128; simp only [extract_or]
    have h0 : (0x3d800000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 5 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 b.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_n : (encodeStr128 x b n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeStr128; simp only [extract_or]
    have h0 : (0x3d800000#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 b.val <<< 5).extractLsb' 10 12 = 0#12 := extract_field_miss hb (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_sz : (encodeStr128 x b n).extractLsb' 30 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeStr128 x b n).extractLsb' 22 2 = 2#2 := by rw [extract_of_fixed hf (by decide)]; decide
  simp only [ex_sz, ex_opc, ex_n, ex_b, ex_x, fromSPBits_fin31, BitVec.toNat_ofNat, Arm64.decodeSimdLoadStoreType]
  rw [shift4_imm12 n]; rfl

theorem decode_ldr128_sp (x : Fin 32) (n : Fin 4096) :
    Arm64.decode (encodeLdr128Sp x n) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 x.val) (.Offset .sp (BitVec.ofNat 64 (n.val * 16)))) := by
  have hx : x.val < 2 ^ 5 := x.isLt; have hn : n.val < 2 ^ 12 := n.isLt
  have hf : encodeLdr128Sp x n &&& 0xffc003e0#32 = 0x3dc003e0#32 &&& 0xffc003e0#32 := by
    have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc003e0#32 = 0#32 := field_and_eq_zero hn (by decide)
    have h2 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffc003e0#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h2
    unfold encodeLdr128Sp; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]
  rw [decode_at_simdLdStImm hf (by decide) (by decide) ⟨by decide, by decide⟩]
  have ex_x : (encodeLdr128Sp x n).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeLdr128Sp; simp only [extract_or]
    have h0 : (0x3dc003e0#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_n : (encodeLdr128Sp x n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeLdr128Sp; simp only [extract_or]
    have h0 : (0x3dc003e0#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_b : (encodeLdr128Sp x n).extractLsb' 5 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_sz : (encodeLdr128Sp x n).extractLsb' 30 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeLdr128Sp x n).extractLsb' 22 2 = 3#2 := by rw [extract_of_fixed hf (by decide)]; decide
  simp only [ex_sz, ex_opc, ex_n, ex_b, ex_x, BitVec.toNat_ofNat, Arm64.decodeSimdLoadStoreType]
  rw [shift4_imm12 n]; rfl

theorem decode_str128_sp (x : Fin 32) (n : Fin 4096) :
    Arm64.decode (encodeStr128Sp x n) =
      some (.strSimd .Q128 (BitVec.ofNat 5 x.val) (.Offset .sp (BitVec.ofNat 64 (n.val * 16)))) := by
  have hx : x.val < 2 ^ 5 := x.isLt; have hn : n.val < 2 ^ 12 := n.isLt
  have hf : encodeStr128Sp x n &&& 0xffc003e0#32 = 0x3d8003e0#32 &&& 0xffc003e0#32 := by
    have h1 : (BitVec.ofNat 32 n.val <<< 10) &&& 0xffc003e0#32 = 0#32 := field_and_eq_zero hn (by decide)
    have h2 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffc003e0#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h2
    unfold encodeStr128Sp; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]
  rw [decode_at_simdLdStImm hf (by decide) (by decide) ⟨by decide, by decide⟩]
  have ex_x : (encodeStr128Sp x n).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeStr128Sp; simp only [extract_or]
    have h0 : (0x3d8003e0#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 0 5 = 0#5 := extract_field_miss hn (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_n : (encodeStr128Sp x n).extractLsb' 10 12 = BitVec.ofNat 12 n.val := by
    unfold encodeStr128Sp; simp only [extract_or]
    have h0 : (0x3d8003e0#32).extractLsb' 10 12 = 0#12 := by decide
    have h1 : (BitVec.ofNat 32 n.val <<< 10).extractLsb' 10 12 = BitVec.ofNat 12 n.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 10 12 = 0#12 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_b : (encodeStr128Sp x n).extractLsb' 5 5 = 31#5 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_sz : (encodeStr128Sp x n).extractLsb' 30 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have ex_opc : (encodeStr128Sp x n).extractLsb' 22 2 = 2#2 := by rw [extract_of_fixed hf (by decide)]; decide
  simp only [ex_sz, ex_opc, ex_n, ex_b, ex_x, BitVec.toNat_ofNat, Arm64.decodeSimdLoadStoreType]
  rw [shift4_imm12 n]; rfl

private theorem bind_lookup_N {bind : Ode.Bind} {n : Fin 4096}
    (hbn : (bind.lookup "N").bind Ode.readInt = some (n.val * 16 : Int)) :
    (bind.lookup "N").bind ((Option.map fun i => (i % (Ode.M64 : Int)).toNat) ∘ Ode.readInt) = some (n.val * 16) := by
  have hmodN : ((n.val * 16 : Int) % (Ode.M64 : Int)).toNat = n.val * 16 := by unfold Ode.M64; have := n.isLt; omega
  cases hlu : bind.lookup "N" with
  | none => simp [hlu] at hbn
  | some s =>
    simp only [hlu, Option.bind_some] at hbn ⊢
    simp [Function.comp, hbn, hmodN]

theorem agree_ldr128 (x : Fin 32) (b : Fin 31) (n : Fin 4096) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hbb : Ode.regOf bind "B" = some (armSlot b.val))
    (hbn : (bind.lookup "N").bind Ode.readInt = some (n.val * 16 : Int))
    (hfit : st.reg (armSlot b.val) + n.val * 16 + 16 ≤ Ode.M64)
    (hread : gs.mem.canRead (gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 16)) 16 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeLdr128 x b n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectLdr128, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hnlt : n.val * 16 < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  let a := st.reg (armSlot b.val) + n.val * 16
  have ha_mod : a % Ode.M64 = a := Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 16) = BitVec.ofNat 64 a := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.gpr b]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt (by omega)]
  let lanes : List Nat := [Ode.load st.mem a 4, Ode.load st.mem (a + 4) 4,
                           Ode.load st.mem (a + 8) 4, Ode.load st.mem (a + 12) 4]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "mem128" [.name "B", .name "N"])) st1
  have hvalN := bind_lookup_N hbn
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectLdr128, bind, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.read a 16 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectLdr128, Ode.execStmt, Ode.lanesOf, Ode.values, Ode.sumList,
          hbx, hvalN, Ode.value, Ode.isNumberLetter, hbb, ha_mod, hall,
          List.range, List.range.loop, lanes, a, st', st1, st0]
  have hread' : gs.mem.canRead (BitVec.ofNat 64 a) 16 = true := by rwa [← hea_bv]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.ldrSimd .Q128 (BitVec.ofNat 5 x.val) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 16)))) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) (gs.mem.read128 (BitVec.ofNat 64 a))).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.SimdMemSize.bytes,
          Arm64.Memory.readSimdSized, hea_bv, hread']
  refine ⟨_, st', decode_ldr128 x b n, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  apply agreeState_writeVec hA x (gs.mem.read128 (BitVec.ofNat 64 a)) lanes (u 0) ?_ _ _ hnext hpc
  intro j
  rw [read128_lane_eq_load hA hfit j]
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

theorem agree_str128 (x : Fin 32) (b : Fin 31) (n : Fin 4096) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hbb : Ode.regOf bind "B" = some (armSlot b.val))
    (hbn : (bind.lookup "N").bind Ode.readInt = some (n.val * 16 : Int))
    (hfit : st.reg (armSlot b.val) + n.val * 16 + 16 ≤ Ode.M64)
    (hwrite : gs.mem.canWrite (gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 16)) 16 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeStr128 x b n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectStr128, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hnlt : n.val * 16 < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  let a := st.reg (armSlot b.val) + n.val * 16
  have ha_mod : a % Ode.M64 = a := Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.readReg64 (.gpr (BitVec.ofNat 5 b.val)) + BitVec.ofNat 64 (n.val * 16) = BitVec.ofNat 64 a := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.gpr b]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt (by omega)]
  let mem' := Ode.store (Ode.store (Ode.store (Ode.store st.mem a (st.vec x.val 0) 4)
                (a + 4) (st.vec x.val 1) 4) (a + 8) (st.vec x.val 2) 4) (a + 12) (st.vec x.val 3) 4
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := { st0 with mem := mem' }
  let st' : Ode.State := Ode.noted bind st0 (.vset (.call "mem128" [.name "B", .name "N"]) (.name "X")) st1
  have hvalN := bind_lookup_N hbn
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectStr128, bind, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.write a 16 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectStr128, Ode.execStmt, Ode.vecArg, Ode.values, Ode.sumList,
          hbx, hvalN, Ode.value, Ode.isNumberLetter, hbb, ha_mod, hall,
          List.range, List.range.loop, mem', a, st', st1, st0]
  have hwrite' : gs.mem.canWrite (BitVec.ofNat 64 a) 16 = true := by rwa [← hea_bv]
  let vx := gs.readVReg128 (BitVec.ofNat 5 x.val)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.strSimd .Q128 (BitVec.ofNat 5 x.val) (.Offset (.gpr (BitVec.ofNat 5 b.val)) (BitVec.ofNat 64 (n.val * 16)))) gs =
      (gs.setMem (gs.mem.write128 (BitVec.ofNat 64 a) vx)).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.SimdMemSize.bytes,
          Arm64.Memory.writeSimdSized, hea_bv, hwrite', vx]
  refine ⟨_, st', decode_str128 x b n, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  exact agreeState_setMem hA mem' (gs.mem.write128 (BitVec.ofNat 64 a) vx)
    (fun addr haddr => write128_eq_store16 hA x hfit haddr) _ _ hnext hpc

theorem agree_ldr128_sp_fault (x : Fin 32) (n : Fin 4096) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hbx : Ode.vecOf bind "X" = some x.val)
    (_hbn : (bind.lookup "N").bind Ode.readInt = some (n.val * 16 : Int))
    (hmis : st.reg Ode.RSP % 16 ≠ 0) :
    ∃ ginst,
      Arm64.decode (encodeLdr128Sp x n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectLdr128Sp, bind, next⟩ u st = none ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).status = .Exception "SP alignment fault" := by
  have hsp : gs.spAligned = false := by rw [spAligned_iff hA]; exact decide_eq_false hmis
  refine ⟨_, decode_ldr128_sp x n, ?_, ?_⟩
  · simp [Ode.exec, Ode.execAll, effectLdr128Sp, Ode.execStmt, Ode.lanesOf, Ode.values,
          Ode.value, Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, Ode.prim, regIndex_sp, hbx, hmis]
  · simp [Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.State.setStatus, hsp]

theorem agree_ldr128_sp (x : Fin 32) (n : Fin 4096) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hbx : Ode.vecOf bind "X" = some x.val)
    (hbn : (bind.lookup "N").bind Ode.readInt = some (n.val * 16 : Int))
    (hal : st.reg Ode.RSP % 16 = 0)
    (hfit : st.reg Ode.RSP + n.val * 16 + 16 ≤ Ode.M64)
    (hread : gs.mem.canRead (gs.sp + BitVec.ofNat 64 (n.val * 16)) 16 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeLdr128Sp x n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectLdr128Sp, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hsp : gs.spAligned = true := by rw [spAligned_iff hA]; exact decide_eq_true hal
  have hnlt : n.val * 16 < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  let a := st.reg Ode.RSP + n.val * 16
  have ha_mod : a % Ode.M64 = a := Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.sp + BitVec.ofNat 64 (n.val * 16) = BitVec.ofNat 64 a := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.sp]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt (by omega)]
  let lanes : List Nat := [Ode.load st.mem a 4, Ode.load st.mem (a + 4) 4,
                           Ode.load st.mem (a + 8) 4, Ode.load st.mem (a + 12) 4]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "mem128" [.call "on16" [.name "sp"], .name "N"])) st1
  have hvalN := bind_lookup_N hbn
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectLdr128Sp, bind, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.read a 16 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectLdr128Sp, Ode.execStmt, Ode.lanesOf, Ode.values, Ode.sumList,
          hbx, hvalN, Ode.value, Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, Ode.prim, regIndex_sp,
          hal, ha_mod, hall, List.range, List.range.loop, lanes, a, st', st1, st0]
  have hread' : gs.mem.canRead (BitVec.ofNat 64 a) 16 = true := by rwa [← hea_bv]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.ldrSimd .Q128 (BitVec.ofNat 5 x.val) (.Offset .sp (BitVec.ofNat 64 (n.val * 16)))) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) (gs.mem.read128 (BitVec.ofNat 64 a))).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.State.readReg64, Arm64.SimdMemSize.bytes,
          Arm64.Memory.readSimdSized, hsp, hea_bv, hread']
  refine ⟨_, st', decode_ldr128_sp x n, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  apply agreeState_writeVec hA x (gs.mem.read128 (BitVec.ofNat 64 a)) lanes (u 0) ?_ _ _ hnext hpc
  intro j
  rw [read128_lane_eq_load hA hfit j]
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

theorem agree_str128_sp_fault (x : Fin 32) (n : Fin 4096) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hbx : Ode.vecOf bind "X" = some x.val)
    (_hbn : (bind.lookup "N").bind Ode.readInt = some (n.val * 16 : Int))
    (hmis : st.reg Ode.RSP % 16 ≠ 0) :
    ∃ ginst,
      Arm64.decode (encodeStr128Sp x n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectStr128Sp, bind, next⟩ u st = none ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).status = .Exception "SP alignment fault" := by
  have hsp : gs.spAligned = false := by rw [spAligned_iff hA]; exact decide_eq_false hmis
  refine ⟨_, decode_str128_sp x n, ?_, ?_⟩
  · simp [Ode.exec, Ode.execAll, effectStr128Sp, Ode.execStmt, Ode.vecArg, Ode.values,
          Ode.value, Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, Ode.prim, regIndex_sp, hbx, hmis]
  · simp [Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.State.setStatus, hsp]

theorem agree_str128_sp (x : Fin 32) (n : Fin 4096) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs) (hbx : Ode.vecOf bind "X" = some x.val)
    (hbn : (bind.lookup "N").bind Ode.readInt = some (n.val * 16 : Int))
    (hal : st.reg Ode.RSP % 16 = 0)
    (hfit : st.reg Ode.RSP + n.val * 16 + 16 ≤ Ode.M64)
    (hwrite : gs.mem.canWrite (gs.sp + BitVec.ofNat 64 (n.val * 16)) 16 = true)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeStr128Sp x n) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectStr128Sp, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  have hsp : gs.spAligned = true := by rw [spAligned_iff hA]; exact decide_eq_true hal
  have hnlt : n.val * 16 < Ode.M64 := by unfold Ode.M64; have := n.isLt; omega
  let a := st.reg Ode.RSP + n.val * 16
  have ha_mod : a % Ode.M64 = a := Nat.mod_eq_of_lt (by omega)
  have hea_bv : gs.sp + BitVec.ofNat 64 (n.val * 16) = BitVec.ofNat 64 a := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hA.sp]
    unfold Ode.M64 at hfit hnlt
    rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt (by omega)]
  let mem' := Ode.store (Ode.store (Ode.store (Ode.store st.mem a (st.vec x.val 0) 4)
                (a + 4) (st.vec x.val 1) 4) (a + 8) (st.vec x.val 2) 4) (a + 12) (st.vec x.val 3) 4
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := { st0 with mem := mem' }
  let st' : Ode.State := Ode.noted bind st0 (.vset (.call "mem128" [.call "on16" [.name "sp"], .name "N"]) (.name "X")) st1
  have hvalN := bind_lookup_N hbn
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectStr128Sp, bind, next⟩ u st = some (.next st') := by
    have hall : Ode.allowed Ode.Perm.all.write a 16 = true := by simp [Ode.allowed, Ode.Perm.all]
    simp [Ode.exec, Ode.execAll, effectStr128Sp, Ode.execStmt, Ode.vecArg, Ode.values, Ode.sumList,
          hbx, hvalN, Ode.value, Ode.memSize, Ode.isNumberLetter, Ode.isRegisterLetter, Ode.regOf, Ode.prim, regIndex_sp,
          hal, ha_mod, hall, List.range, List.range.loop, mem', a, st', st1, st0]
  have hwrite' : gs.mem.canWrite (BitVec.ofNat 64 a) 16 = true := by rwa [← hea_bv]
  let vx := gs.readVReg128 (BitVec.ofNat 5 x.val)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.strSimd .Q128 (BitVec.ofNat 5 x.val) (.Offset .sp (BitVec.ofNat 64 (n.val * 16)))) gs =
      (gs.setMem (gs.mem.write128 (BitVec.ofNat 64 a) vx)).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.AddrMode.baseReg,
          Arm64.checkRegSPAligned, Arm64.evalAddrMode, Arm64.State.readReg64, Arm64.SimdMemSize.bytes,
          Arm64.Memory.writeSimdSized, hsp, hea_bv, hwrite', vx]
  refine ⟨_, st', decode_str128_sp x n, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  exact agreeState_setMem hA mem' (gs.mem.write128 (BitVec.ofNat 64 a) vx)
    (fun addr haddr => write128_eq_store16 hA x hfit haddr) _ _ hnext hpc

/-! ## Row 57: `and_v` (`and vX.16b, vY.16b, vZ.16b`) -/

def encodeAndV (x y z : Fin 32) : BitVec 32 :=
  0x4e201c00#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

def effectAndV : List Ode.Stmt :=
  [.vset (.name "X") (.call "each32" [.name "and32", .name "Y", .name "Z"])]

theorem decode_and_v (x y z : Fin 32) :
    Arm64.decode (encodeAndV x y z) =
      some (.simdThreeSame true false 0#2 (BitVec.ofNat 5 z.val) 3#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) := by
  have hx : x.val < 2 ^ 5 := x.isLt; have hy : y.val < 2 ^ 5 := y.isLt; have hz : z.val < 2 ^ 5 := z.isLt
  have hf : encodeAndV x y z &&& 0xffe0fc00#32 = 0x4e201c00#32 &&& 0xffe0fc00#32 := by
    have h1 : (BitVec.ofNat 32 z.val <<< 16) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hz (by decide)
    have h2 : (BitVec.ofNat 32 y.val <<< 5) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hy (by decide)
    have h3 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffe0fc00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h3
    unfold encodeAndV; simp only [BitVec.and_or_distrib_right, h1, h2, h3, BitVec.or_zero]
  rw [decode_at_simdThreeSame hf (by decide) (by decide) ⟨by decide, by decide⟩]
  have ex_x : (encodeAndV x y z).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeAndV; simp only [extract_or]
    have h0 : (0x4e201c00#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_y : (encodeAndV x y z).extractLsb' 5 5 = BitVec.ofNat 5 y.val := by
    unfold encodeAndV; simp only [extract_or]
    have h0 : (0x4e201c00#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 y.val := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have ex_z : (encodeAndV x y z).extractLsb' 16 5 = BitVec.ofNat 5 z.val := by
    unfold encodeAndV; simp only [extract_or]
    have h0 : (0x4e201c00#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 z.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hy (by omega)
    have h3 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h3; rw [h0, h1, h2, h3]; simp
  have hq : (encodeAndV x y z).getLsbD 30 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hu : (encodeAndV x y z).getLsbD 29 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hsz : (encodeAndV x y z).extractLsb' 22 2 = 0#2 := by rw [extract_of_fixed hf (by decide)]; decide
  have hopc : (encodeAndV x y z).extractLsb' 11 5 = 3#5 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [hq, hu, hsz, hopc, ex_x, ex_y, ex_z]

theorem agree_and_v (x y z : Fin 32) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeAndV x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectAndV, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let lanes : List Nat := [st.vec y.val 0 &&& st.vec z.val 0, st.vec y.val 1 &&& st.vec z.val 1,
                           st.vec y.val 2 &&& st.vec z.val 2, st.vec y.val 3 &&& st.vec z.val 3]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "each32" [.name "and32", .name "Y", .name "Z"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectAndV, bind, next⟩ u st = some (.next st') := by
    simp [Ode.exec, Ode.execAll, effectAndV, Ode.execStmt, Ode.lanesOf, Ode.vecArg,
          hbx, hby, hbz, Ode.prim32, List.range, List.range.loop, List.mapM, List.mapM.loop, lanes, st', st1, st0]
  let vn := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vm := gs.readVReg128 (BitVec.ofNat 5 z.val)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.simdThreeSame true false 0#2 (BitVec.ofNat 5 z.val) 3#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) (vn &&& vm)).advancePC := by
    simp [Arm64.execInstWithSvc, vn, vm]
  refine ⟨_, st', decode_and_v x y z, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  apply agreeState_writeVec hA x (vn &&& vm) lanes (u 0) ?_ _ _ hnext hpc
  intro j
  have hex : (vn &&& vm).extractLsb' (32 * j.val) 32 = vn.extractLsb' (32 * j.val) 32 &&& vm.extractLsb' (32 * j.val) 32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_and, hi]
  rw [hex, BitVec.toNat_and, hA.vec y j, hA.vec z j]
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

/-! ## Rows 58–63: `csel_eq`, `csel_ne`, `csel_hs`, `csel_lo`, `csel_hi`, `csel_ls` -/

def encodeCsel (c : BitVec 4) (d s p : Fin 31) : BitVec 32 :=
  0x9a800000#32 ||| (BitVec.ofNat 32 p.val <<< 16) ||| (c.zeroExtend 32 <<< 12)
                ||| (BitVec.ofNat 32 s.val <<< 5) ||| BitVec.ofNat 32 d.val

def encodeCselEq (d s p : Fin 31) : BitVec 32 := encodeCsel 0#4 d s p
def encodeCselNe (d s p : Fin 31) : BitVec 32 := encodeCsel 1#4 d s p
def encodeCselHs (d s p : Fin 31) : BitVec 32 := encodeCsel 2#4 d s p
def encodeCselLo (d s p : Fin 31) : BitVec 32 := encodeCsel 3#4 d s p
def encodeCselHi (d s p : Fin 31) : BitVec 32 := encodeCsel 8#4 d s p
def encodeCselLs (d s p : Fin 31) : BitVec 32 := encodeCsel 9#4 d s p

def effectCsel (flag : String) : List Ode.Stmt :=
  [.set (.name "D") (.call "select" [.name flag, .name "S", .name "P"])]

def effectCselEq : List Ode.Stmt := effectCsel "zf"
def effectCselNe : List Ode.Stmt := effectCsel "nzf"
def effectCselHs : List Ode.Stmt := effectCsel "ncf"
def effectCselLo : List Ode.Stmt := effectCsel "cf"
def effectCselHi : List Ode.Stmt := effectCsel "hi"
def effectCselLs : List Ode.Stmt := effectCsel "nhi"

theorem decode_csel (c : BitVec 4) (d s p : Fin 31) :
    Arm64.decode (encodeCsel c d s p) =
      some (.condSelect .W64 .CSEL (.gpr (BitVec.ofNat 5 d.val))
        (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) (Arm64.CondCode.ofBits c)) := by
  have hd : d.val < 2 ^ 5 := by have := d.isLt; omega
  have hs : s.val < 2 ^ 5 := by have := s.isLt; omega
  have hp : p.val < 2 ^ 5 := by have := p.isLt; omega
  have hc : c.toNat < 2 ^ 4 := c.isLt
  have hcz : c.zeroExtend 32 = BitVec.ofNat 32 c.toNat := by
    apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (by omega : c.toNat < 2 ^ 32)]
  have hf : encodeCsel c d s p &&& 0xffe00c00#32 = 0x9a800000#32 &&& 0xffe00c00#32 := by
    have h1 : (BitVec.ofNat 32 p.val <<< 16) &&& 0xffe00c00#32 = 0#32 := field_and_eq_zero hp (by decide)
    have h2 : (BitVec.ofNat 32 c.toNat <<< 12) &&& 0xffe00c00#32 = 0#32 := field_and_eq_zero hc (by decide)
    have h3 : (BitVec.ofNat 32 s.val <<< 5) &&& 0xffe00c00#32 = 0#32 := field_and_eq_zero hs (by decide)
    have h4 : (BitVec.ofNat 32 d.val <<< 0) &&& 0xffe00c00#32 = 0#32 := field_and_eq_zero hd (by decide)
    simp only [BitVec.shiftLeft_zero] at h4
    unfold encodeCsel; rw [hcz]; simp only [BitVec.and_or_distrib_right, h1, h2, h3, h4, BitVec.or_zero]
  have ex_d : (encodeCsel c d s p).extractLsb' 0 5 = BitVec.ofNat 5 d.val := by
    unfold encodeCsel; rw [hcz]; simp only [extract_or]
    have h0 : (0x9a800000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 c.toNat <<< 12).extractLsb' 0 5 = 0#5 := extract_field_miss hc (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hs (by omega)
    have h4 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 d.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  have ex_s : (encodeCsel c d s p).extractLsb' 5 5 = BitVec.ofNat 5 s.val := by
    unfold encodeCsel; rw [hcz]; simp only [extract_or]
    have h0 : (0x9a800000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 c.toNat <<< 12).extractLsb' 5 5 = 0#5 := extract_field_miss hc (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 s.val := extract_field_hit (by omega)
    have h4 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  have ex_p : (encodeCsel c d s p).extractLsb' 16 5 = BitVec.ofNat 5 p.val := by
    unfold encodeCsel; rw [hcz]; simp only [extract_or]
    have h0 : (0x9a800000#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 p.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 c.toNat <<< 12).extractLsb' 16 5 = 0#5 := extract_field_miss hc (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hs (by omega)
    have h4 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  have ex_c : (encodeCsel c d s p).extractLsb' 12 4 = c := by
    unfold encodeCsel; rw [hcz]; simp only [extract_or]
    have h0 : (0x9a800000#32).extractLsb' 12 4 = 0#4 := by decide
    have h1 : (BitVec.ofNat 32 p.val <<< 16).extractLsb' 12 4 = 0#4 := extract_field_miss hp (by omega)
    have h2 : (BitVec.ofNat 32 c.toNat <<< 12).extractLsb' 12 4 = BitVec.ofNat 4 c.toNat := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 s.val <<< 5).extractLsb' 12 4 = 0#4 := extract_field_miss hs (by omega)
    have h4 : (BitVec.ofNat 32 d.val <<< 0).extractLsb' 12 4 = 0#4 := extract_field_miss hd (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  have hb31 : (encodeCsel c d s p).getLsbD 31 = true := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hb30 : (encodeCsel c d s p).getLsbD 30 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  have hb10 : (encodeCsel c d s p).getLsbD 10 = false := by rw [getLsbD_of_fixed hf (by decide)]; decide
  unfold Arm64.decode
  simp only [word_ne_of_fixed hf (c := 0xd503201f#32) (by decide),
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
             mask_of_fixed hf (m := 0x3fe00800#32) (by decide),
             hb31, hb30, hb10, ex_d, ex_s, ex_p, ex_c, fromZRBits_fin31,
             Arm64.CondSelectOp.ofBits, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem agree_csel_core (c : BitVec 4) (flag : String) (d s p : Fin 31) (bind : Ode.Bind)
    (prog : Ode.Program) (u : Nat → Nat) (st : Ode.State) (gs : Arm64.State) (next : Nat)
    (hA : AgreeState st gs)
    (hbd : Ode.regOf bind "D" = some (armSlot d.val))
    (hbs : Ode.regOf bind "S" = some (armSlot s.val))
    (hbp : Ode.regOf bind "P" = some (armSlot p.val))
    (hflag : Ode.flagVal st flag = some (if Arm64.ConditionHolds (Arm64.CondCode.ofBits c) gs.pstate then 1 else 0))
    (hnotnum : Ode.isNumberLetter flag = false)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeCsel c d s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectCsel flag, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let holds := Arm64.ConditionHolds (Arm64.CondCode.ofBits c) gs.pstate
  let resBV : BitVec 64 := if holds then gs.readReg64 (.gpr (BitVec.ofNat 5 s.val)) else gs.readReg64 (.gpr (BitVec.ofNat 5 p.val))
  let resNat : Nat := if holds then st.reg (armSlot s.val) else st.reg (armSlot p.val)
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setReg st0 (armSlot d.val) resNat
  let st' : Ode.State := Ode.noted bind st0 (.set (.name "D") (.call "select" [.name flag, .name "S", .name "P"])) st1
  have hflag0 : Ode.flagVal st0 flag = Ode.flagVal st flag := by simp [Ode.flagVal, st0]
  have hns : Ode.isNumberLetter "S" = false := rfl
  have hnp : Ode.isNumberLetter "P" = false := rfl
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectCsel flag, bind, next⟩ u st = some (.next st') := by
    cases hh : holds <;>
      simp [Ode.exec, Ode.execAll, effectCsel, Ode.execStmt, Ode.isUnknown,
            Ode.value, Ode.values, Ode.memSize, Ode.prim,
            hnotnum, hns, hnp, hflag0, hflag, hbd, hbs, hbp, holds, hh, resNat, st', st1, st0]
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.condSelect .W64 .CSEL (.gpr (BitVec.ofNat 5 d.val))
        (.gpr (BitVec.ofNat 5 s.val)) (.gpr (BitVec.ofNat 5 p.val)) (Arm64.CondCode.ofBits c)) gs =
      (gs.writeReg64 (.gpr (BitVec.ofNat 5 d.val)) resBV).advancePC := by
    simp [Arm64.execInstWithSvc, Arm64.execCondSelect, Arm64.State.readReg, Arm64.State.writeReg, holds, resBV]
  have hval : resBV.toNat = resNat := by
    cases hh : holds
    · simp only [resBV, resNat, hh, Bool.false_eq_true, ↓reduceIte]; exact hA.gpr p
    · simp only [resBV, resNat, hh, ↓reduceIte]; exact hA.gpr s
  refine ⟨_, st', decode_csel c d s p, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  exact agreeState_writeGpr hA d resBV resNat hval bind _ hnext hpc

theorem agree_csel_eq (d s p : Fin 31) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat) (hA : AgreeState st gs)
    (hbd : Ode.regOf bind "D" = some (armSlot d.val)) (hbs : Ode.regOf bind "S" = some (armSlot s.val))
    (hbp : Ode.regOf bind "P" = some (armSlot p.val)) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st', Arm64.decode (encodeCselEq d s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectCselEq, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate :=
  agree_csel_core 0#4 "zf" d s p bind prog u st gs next hA hbd hbs hbp
    (by simp [Ode.flagVal, Arm64.CondCode.ofBits, Arm64.ConditionHolds, hA.zf]) (by decide) hnext hpc

theorem agree_csel_ne (d s p : Fin 31) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat) (hA : AgreeState st gs)
    (hbd : Ode.regOf bind "D" = some (armSlot d.val)) (hbs : Ode.regOf bind "S" = some (armSlot s.val))
    (hbp : Ode.regOf bind "P" = some (armSlot p.val)) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st', Arm64.decode (encodeCselNe d s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectCselNe, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate :=
  agree_csel_core 1#4 "nzf" d s p bind prog u st gs next hA hbd hbs hbp
    (by simp [Ode.flagVal, Arm64.CondCode.ofBits, Arm64.ConditionHolds, hA.zf]) (by decide) hnext hpc

theorem agree_csel_hs (d s p : Fin 31) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat) (hA : AgreeState st gs)
    (hbd : Ode.regOf bind "D" = some (armSlot d.val)) (hbs : Ode.regOf bind "S" = some (armSlot s.val))
    (hbp : Ode.regOf bind "P" = some (armSlot p.val)) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st', Arm64.decode (encodeCselHs d s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectCselHs, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate :=
  agree_csel_core 2#4 "ncf" d s p bind prog u st gs next hA hbd hbs hbp
    (by simp [Ode.flagVal, Arm64.CondCode.ofBits, Arm64.ConditionHolds, hA.cf]) (by decide) hnext hpc

theorem agree_csel_lo (d s p : Fin 31) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat) (hA : AgreeState st gs)
    (hbd : Ode.regOf bind "D" = some (armSlot d.val)) (hbs : Ode.regOf bind "S" = some (armSlot s.val))
    (hbp : Ode.regOf bind "P" = some (armSlot p.val)) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st', Arm64.decode (encodeCselLo d s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectCselLo, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate :=
  agree_csel_core 3#4 "cf" d s p bind prog u st gs next hA hbd hbs hbp
    (by simp [Ode.flagVal, Arm64.CondCode.ofBits, Arm64.ConditionHolds, hA.cf]) (by decide) hnext hpc

theorem agree_csel_hi (d s p : Fin 31) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat) (hA : AgreeState st gs)
    (hbd : Ode.regOf bind "D" = some (armSlot d.val)) (hbs : Ode.regOf bind "S" = some (armSlot s.val))
    (hbp : Ode.regOf bind "P" = some (armSlot p.val)) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st', Arm64.decode (encodeCselHi d s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectCselHi, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate :=
  agree_csel_core 8#4 "hi" d s p bind prog u st gs next hA hbd hbs hbp
    (by cases hcf : st.cf <;> cases hzf : st.zf <;>
        simp [Ode.flagVal, Arm64.CondCode.ofBits, Arm64.ConditionHolds, hA.cf, hA.zf, hcf, hzf])
    (by decide) hnext hpc

theorem agree_csel_ls (d s p : Fin 31) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat) (hA : AgreeState st gs)
    (hbd : Ode.regOf bind "D" = some (armSlot d.val)) (hbs : Ode.regOf bind "S" = some (armSlot s.val))
    (hbp : Ode.regOf bind "P" = some (armSlot p.val)) (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st', Arm64.decode (encodeCselLs d s p) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectCselLs, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate :=
  agree_csel_core 9#4 "nhi" d s p bind prog u st gs next hA hbd hbs hbp
    (by cases hcf : st.cf <;> cases hzf : st.zf <;>
        simp [Ode.flagVal, Arm64.CondCode.ofBits, Arm64.ConditionHolds, hA.cf, hA.zf, hcf, hzf])
    (by decide) hnext hpc

/-! ## Rows 64–67: `sha256su0`, `sha256su1`, `sha256h`, `sha256h2` -/

def guardsBeforeCryptoSha2Reg : List (BitVec 32 × BitVec 32) :=
  (0x9f200400#32, 0x0e200400#32) ::
  (0x9f3e0c00#32, 0x0e200800#32) ::
  (0x9f3e0c00#32, 0x0e300800#32) ::
  (0xbf208c00#32, 0x0e000800#32) ::
  (0xbfe08400#32, 0x2e000000#32) ::
  (0xbf20fc00#32, 0x0e20e000#32) ::
  (0x9f200c00#32, 0x0e200000#32) ::
  guardsBeforeSimdThreeSame

private theorem decode_at_cryptoSha2Reg {w base fixed : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hnop : ((base &&& fixed) == (0xd503201f#32 &&& fixed)) = false)
    (hskip : skipsAll base fixed guardsBeforeCryptoSha2Reg = true)
    (hmatch : (0xfffe0c00#32 &&& fixed = 0xfffe0c00#32) ∧ (base &&& 0xfffe0c00#32 = 0x5e280800#32))
    (hop : (w.extractLsb' 12 5 == 0#5 || w.extractLsb' 12 5 == 1#5 || w.extractLsb' 12 5 == 2#5) = true) :
    Arm64.decode w = some (.cryptoSha2Reg (w.extractLsb' 12 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5)) := by
  have sk : ∀ m c, (m, c) ∈ guardsBeforeCryptoSha2Reg → ((w &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hw hskip hm
  have hhit : w &&& 0xfffe0c00#32 = 0x5e280800#32 := by rw [mask_of_fixed hw hmatch.1, hmatch.2]
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
             sk 0x9f200400#32 0x0e200400#32 (by decide), sk 0x9f3e0c00#32 0x0e200800#32 (by decide),
             sk 0x9f3e0c00#32 0x0e300800#32 (by decide), sk 0xbf208c00#32 0x0e000800#32 (by decide),
             sk 0xbfe08400#32 0x2e000000#32 (by decide), sk 0xbf20fc00#32 0x0e20e000#32 (by decide),
             sk 0x9f200c00#32 0x0e200000#32 (by decide),
             hhit, hop, beq_self_eq_true, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

private theorem decode_at_cryptoSha3Reg {w base fixed : BitVec 32}
    (hw : w &&& fixed = base &&& fixed)
    (hnop : ((base &&& fixed) == (0xd503201f#32 &&& fixed)) = false)
    (hskip : skipsAll base fixed ((0xfffe0c00#32, 0x5e280800#32) :: guardsBeforeCryptoSha2Reg) = true)
    (hmatch : (0xffe08c00#32 &&& fixed = 0xffe08c00#32) ∧ (base &&& 0xffe08c00#32 = 0x5e000000#32))
    (hop : (w.extractLsb' 12 3 != 7#3) = true) :
    Arm64.decode w = some (.cryptoSha3Reg (w.extractLsb' 12 3) (w.extractLsb' 16 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5)) := by
  have sk : ∀ m c, (m, c) ∈ ((0xfffe0c00#32, 0x5e280800#32) :: guardsBeforeCryptoSha2Reg) → ((w &&& m) == c) = false :=
    fun m c hm => skipsAll_mem hw hskip hm
  have hhit : w &&& 0xffe08c00#32 = 0x5e000000#32 := by rw [mask_of_fixed hw hmatch.1, hmatch.2]
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
             sk 0x9f200400#32 0x0e200400#32 (by decide), sk 0x9f3e0c00#32 0x0e200800#32 (by decide),
             sk 0x9f3e0c00#32 0x0e300800#32 (by decide), sk 0xbf208c00#32 0x0e000800#32 (by decide),
             sk 0xbfe08400#32 0x2e000000#32 (by decide), sk 0xbf20fc00#32 0x0e20e000#32 (by decide),
             sk 0x9f200c00#32 0x0e200000#32 (by decide), sk 0xfffe0c00#32 0x5e280800#32 (by decide),
             hhit, hop, beq_self_eq_true, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-! ### BitVec 32 ↔ Nat bridge lemmas for SHA-256 primitives -/

private theorem bv_getLsbD_ge {w : Nat} (x : BitVec w) (i : Nat) (h : w ≤ i) :
    x.getLsbD i = false := by
  unfold BitVec.getLsbD Nat.testBit
  rw [Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))]
  rfl

private theorem bv32_rotateRight_toNat (a : BitVec 32) (n : Nat) (hn : n < 32) :
    (a.rotateRight n).toNat = Ode.rotr a.toNat n := by
  have hmod : n % 32 = n := Nat.mod_eq_of_lt hn
  have hdisj : ((a >>> n) ||| (a <<< (32 - n))) = a.rotateRight n := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
               BitVec.getLsbD_rotateRight, hi, decide_true, Bool.true_and, hmod]
    by_cases h : i < 32 - n
    · simp [h]
    · have h1 : 32 ≤ n + i := by omega
      rw [bv_getLsbD_ge a (n + i) h1]
      simp [h]
  have hsum : ((a >>> n) ||| (a <<< (32 - n))).toNat = (a >>> n).toNat + (a <<< (32 - n)).toNat := by
    have ha : ((a >>> n) &&& (a <<< (32 - n))) = 0#32 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
                 BitVec.getLsbD_zero, hi, decide_true, Bool.true_and]
      by_cases h : i < 32 - n
      · simp [h]
      · have h1 : 32 ≤ n + i := by omega
        rw [bv_getLsbD_ge a (n + i) h1]; simp
    have hadd : (a >>> n) + (a <<< (32 - n)) = (a >>> n) ||| (a <<< (32 - n)) :=
      BitVec.add_eq_or_of_and_eq_zero _ _ ha
    have hlt : (a >>> n).toNat + (a <<< (32 - n)).toNat < 2 ^ 32 := by
      have hhi : (a >>> n).toNat < 2 ^ (32 - n) := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have := a.isLt
        have hp : 2 ^ 32 = 2 ^ (32 - n) * 2 ^ n := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).mpr (by omega)
      have hlo : (a <<< (32 - n)).toNat = a.toNat % 2 ^ n * 2 ^ (32 - n) := by
        rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        have hp : 2 ^ 32 = 2 ^ n * 2 ^ (32 - n) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
        rw [hp, Nat.mul_mod_mul_right]
      have hm : a.toNat % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
      have hp : 2 ^ 32 = 2 ^ n * 2 ^ (32 - n) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      have hmul : (a.toNat % 2 ^ n + 1) * 2 ^ (32 - n) ≤ 2 ^ n * 2 ^ (32 - n) :=
        Nat.mul_le_mul_right _ hm
      rw [Nat.add_mul, Nat.one_mul] at hmul
      omega
    rw [← hadd, BitVec.toNat_add, Nat.mod_eq_of_lt hlt]
  rw [← hdisj, hsum, Ode.rotr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hp : 2 ^ 32 = 2 ^ n * 2 ^ (32 - n) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
  rw [hp, Nat.mul_mod_mul_right]

private theorem bv32_shaChoose_toNat (e f g : BitVec 32) :
    (Arm64.shaChoose32 e f g).toNat = Ode.sha256Ch e.toNat f.toNat g.toNat := by
  have h : Arm64.shaChoose32 e f g = g ^^^ (e &&& (f ^^^ g)) := by
    unfold Arm64.shaChoose32
    rw [BitVec.xor_comm, BitVec.and_comm]
  rw [h, Ode.sha256Ch, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_xor]

private theorem bv32_shaMajority_toNat (a b c : BitVec 32) :
    (Arm64.shaMajority32 a b c).toNat = Ode.sha256Maj a.toNat b.toNat c.toNat := by
  have h : Arm64.shaMajority32 a b c = (a &&& b) ^^^ ((a ^^^ b) &&& c) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    unfold Arm64.shaMajority32
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl
  rw [h, Ode.sha256Maj, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_xor]

private theorem bv32_sha256Sigma0_toNat (a : BitVec 32) :
    (Arm64.sha256Sigma0 a).toNat = Ode.sha256S0 a.toNat := by
  unfold Arm64.sha256Sigma0 Ode.sha256S0
  rw [BitVec.toNat_xor, BitVec.toNat_xor,
      bv32_rotateRight_toNat a 2 (by decide), bv32_rotateRight_toNat a 13 (by decide),
      bv32_rotateRight_toNat a 22 (by decide)]

private theorem bv32_sha256Sigma1_toNat (e : BitVec 32) :
    (Arm64.sha256Sigma1 e).toNat = Ode.sha256S1 e.toNat := by
  unfold Arm64.sha256Sigma1 Ode.sha256S1
  rw [BitVec.toNat_xor, BitVec.toNat_xor,
      bv32_rotateRight_toNat e 6 (by decide), bv32_rotateRight_toNat e 11 (by decide),
      bv32_rotateRight_toNat e 25 (by decide)]

private theorem bv32_sha256s0_toNat (x : BitVec 32) :
    (x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)).toNat = Ode.sha256s0 x.toNat := by
  unfold Ode.sha256s0
  rw [BitVec.toNat_xor, BitVec.toNat_xor, BitVec.toNat_ushiftRight,
      bv32_rotateRight_toNat x 7 (by decide), bv32_rotateRight_toNat x 18 (by decide)]

private theorem bv32_sha256s1_toNat (x : BitVec 32) :
    (x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)).toNat = Ode.sha256s1 x.toNat := by
  unfold Ode.sha256s1
  rw [BitVec.toNat_xor, BitVec.toNat_xor, BitVec.toNat_ushiftRight,
      bv32_rotateRight_toNat x 17 (by decide), bv32_rotateRight_toNat x 19 (by decide)]

private theorem append4_32_extract (d c b a : BitVec 32) :
    (d ++ c ++ b ++ a).extractLsb' 0 32 = a ∧
    (d ++ c ++ b ++ a).extractLsb' 32 32 = b ∧
    (d ++ c ++ b ++ a).extractLsb' 64 32 = c ∧
    (d ++ c ++ b ++ a).extractLsb' 96 32 = d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and, Nat.zero_add]
    simp [hi]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    have h1 : ¬ (32 + i < 32) := by omega
    simp only [h1, ↓reduceIte, Nat.add_sub_cancel_left, hi]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    have h1 : ¬ (64 + i < 32) := by omega
    have h2 : ¬ (64 + i - 32 < 32) := by omega
    have h3 : 64 + i - 32 - 32 < 32 := by omega
    simp only [h1, h2, h3, ↓reduceIte]; congr 1; omega
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    have h1 : ¬ (96 + i < 32) := by omega
    have h2 : ¬ (96 + i - 32 < 32) := by omega
    have h3 : ¬ (96 + i - 32 - 32 < 32) := by omega
    simp only [h1, h2, h3, ↓reduceIte]; congr 1; omega

private theorem pack4_or_extract (e0 e1 e2 e3 : BitVec 32) :
    let v : BitVec 128 := 0#128 ||| (e0.zeroExtend 128 <<< 0) ||| (e1.zeroExtend 128 <<< 32)
                          ||| (e2.zeroExtend 128 <<< 64) ||| (e3.zeroExtend 128 <<< 96)
    v.extractLsb' 0 32 = e0 ∧ v.extractLsb' 32 32 = e1 ∧
    v.extractLsb' 64 32 = e2 ∧ v.extractLsb' 96 32 = e3 := by
  intro v
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [v, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_zero,
               BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, Nat.zero_add]
    have h1 : i < 32 := hi
    have h2 : i < 64 := by omega
    have h3 : i < 96 := by omega
    have h4 : i < 128 := by omega
    simp [h1, h2, h3, h4]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [v, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_zero,
               BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, Nat.sub_zero]
    have h0 : 32 ≤ 32 + i := by omega
    have h1 : ¬ (32 + i < 32) := by omega
    have h2 : 32 + i < 64 := by omega
    have h3 : 32 + i < 96 := by omega
    have h4 : 32 + i < 128 := by omega
    have hi128 : i < 128 := by omega
    rw [bv_getLsbD_ge e0 (32 + i) h0]
    simp [h1, h2, h3, h4, hi128]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [v, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_zero,
               BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, Nat.sub_zero]
    have h0 : 32 ≤ 64 + i := by omega
    have h1 : 32 ≤ 64 + i - 32 := by omega
    have h2 : ¬ (64 + i < 64) := by omega
    have h3 : 64 + i < 96 := by omega
    have h4 : 64 + i < 128 := by omega
    have hi128 : i < 128 := by omega
    rw [bv_getLsbD_ge e0 (64 + i) h0, bv_getLsbD_ge e1 (64 + i - 32) h1]
    simp [h2, h3, h4, hi128]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [v, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_zero,
               BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, Nat.sub_zero]
    have h0 : 32 ≤ 96 + i := by omega
    have h1 : 32 ≤ 96 + i - 32 := by omega
    have h2 : 32 ≤ 96 + i - 64 := by omega
    have h3 : ¬ (96 + i < 96) := by omega
    have h4 : 96 + i < 128 := by omega
    have hi128 : i < 128 := by omega
    rw [bv_getLsbD_ge e0 (96 + i) h0, bv_getLsbD_ge e1 (96 + i - 32) h1,
        bv_getLsbD_ge e2 (96 + i - 64) h2]
    simp [h3, h4, hi128]

private theorem extract_append_32_96 (a : BitVec 32) (b : BitVec 96) :
    (a ++ b).extractLsb' 0 32 = b.extractLsb' 0 32 ∧
    (a ++ b).extractLsb' 32 32 = b.extractLsb' 32 32 ∧
    (a ++ b).extractLsb' 64 32 = b.extractLsb' 64 32 ∧
    (a ++ b).extractLsb' 96 32 = a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and, Nat.zero_add]
    have : i < 96 := by omega
    simp [this]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    have : 32 + i < 96 := by omega
    simp [this]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    have : 64 + i < 96 := by omega
    simp [this]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    have : ¬ (96 + i < 96) := by omega
    simp [this]

private theorem extract_sub96 (v : BitVec 128) :
    (v.extractLsb' 32 96).extractLsb' 0 32 = v.extractLsb' 32 32 ∧
    (v.extractLsb' 32 96).extractLsb' 32 32 = v.extractLsb' 64 32 ∧
    (v.extractLsb' 32 96).extractLsb' 64 32 = v.extractLsb' 96 32 := by
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add]
    have : i < 96 := by omega
    simp [this]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    have : 32 + i < 96 := by omega
    simp only [this, decide_true, Bool.true_and]; congr 1; omega
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    have : 64 + i < 96 := by omega
    simp only [this, decide_true, Bool.true_and]; congr 1; omega

private theorem bv32_add_toNat (a b : BitVec 32) :
    (a + b).toNat = (a.toNat + b.toNat) % Ode.W32 := by
  rw [BitVec.toNat_add]; rfl

-- Row 64: `sha256su0` (`X = sha256msg1(X, Y)`)
def encodeSha256su0 (x y : Fin 32) : BitVec 32 :=
  0x5e282800#32 ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

def effectSha256su0 : List Ode.Stmt :=
  [.vset (.name "X") (.call "sha256msg1" [.name "X", .name "Y"])]

theorem decode_sha256su0 (x y : Fin 32) :
    Arm64.decode (encodeSha256su0 x y) =
      some (.cryptoSha2Reg 2#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) := by
  have hx : x.val < 2 ^ 5 := x.isLt; have hy : y.val < 2 ^ 5 := y.isLt
  have hf : encodeSha256su0 x y &&& 0xfffffc00#32 = 0x5e282800#32 &&& 0xfffffc00#32 := by
    have h1 : (BitVec.ofNat 32 y.val <<< 5) &&& 0xfffffc00#32 = 0#32 := field_and_eq_zero hy (by decide)
    have h2 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xfffffc00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h2
    unfold encodeSha256su0; simp only [BitVec.and_or_distrib_right, h1, h2, BitVec.or_zero]
  have hopc : (encodeSha256su0 x y).extractLsb' 12 5 = 2#5 := by rw [extract_of_fixed hf (by decide)]; decide
  rw [decode_at_cryptoSha2Reg hf (by decide) (by decide) ⟨by decide, by decide⟩ (by rw [hopc]; decide), hopc]
  have ex_x : (encodeSha256su0 x y).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeSha256su0; simp only [extract_or]
    have h0 : (0x5e282800#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hy (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  have ex_y : (encodeSha256su0 x y).extractLsb' 5 5 = BitVec.ofNat 5 y.val := by
    unfold encodeSha256su0; simp only [extract_or]
    have h0 : (0x5e282800#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 y.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h2; rw [h0, h1, h2]; simp
  rw [ex_x, ex_y]

private def sha256su0Res (vx vy : BitVec 128) : BitVec 128 :=
  let x0 := vx.extractLsb' 0 32; let x1 := vx.extractLsb' 32 32
  let x2 := vx.extractLsb' 64 32; let x3 := vx.extractLsb' 96 32
  let y0 := vy.extractLsb' 0 32
  let s0 (v : BitVec 32) : BitVec 32 := v.rotateRight 7 ^^^ v.rotateRight 18 ^^^ (v >>> 3)
  0#128 ||| ((s0 x1 + x0).zeroExtend 128 <<< 0) ||| ((s0 x2 + x1).zeroExtend 128 <<< 32)
        ||| ((s0 x3 + x2).zeroExtend 128 <<< 64) ||| ((s0 y0 + x3).zeroExtend 128 <<< 96)

private theorem evalCryptoSha2Reg_su0 (vx vy : BitVec 128) :
    Arm64.evalCryptoSha2Reg 2#5 vx vy = Except.ok (sha256su0Res vx vy) := by
  have ht := extract_append_32_96 (vy.extractLsb' 0 32) (vx.extractLsb' 32 96)
  have hsub := extract_sub96 vx
  unfold Arm64.evalCryptoSha2Reg sha256su0Res
  dsimp only [List.range, List.range.loop, List.foldl]
  have hm0 : 0 * 32 = 0 := rfl
  have hm1 : 1 * 32 = 32 := rfl
  have hm2 : 2 * 32 = 64 := rfl
  have hm3 : 3 * 32 = 96 := rfl
  simp only [hm0, hm1, hm2, hm3, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2, hsub.1, hsub.2.1, hsub.2.2]
  rfl

private theorem sha256su0Res_lanes (vx vy : BitVec 128) :
    let x0 := vx.extractLsb' 0 32; let x1 := vx.extractLsb' 32 32
    let x2 := vx.extractLsb' 64 32; let x3 := vx.extractLsb' 96 32
    let y0 := vy.extractLsb' 0 32
    let s0 (v : BitVec 32) : BitVec 32 := v.rotateRight 7 ^^^ v.rotateRight 18 ^^^ (v >>> 3)
    (sha256su0Res vx vy).extractLsb' 0 32 = s0 x1 + x0 ∧
    (sha256su0Res vx vy).extractLsb' 32 32 = s0 x2 + x1 ∧
    (sha256su0Res vx vy).extractLsb' 64 32 = s0 x3 + x2 ∧
    (sha256su0Res vx vy).extractLsb' 96 32 = s0 y0 + x3 :=
  pack4_or_extract _ _ _ _

private theorem lanesOf_sha256msg1 (perm : Ode.Perm) (bind : Ode.Bind) (s : Ode.State)
    {x y : Nat} (hbx : Ode.vecOf bind "X" = some x) (hby : Ode.vecOf bind "Y" = some y) :
    Ode.lanesOf perm bind s (.call "sha256msg1" [.name "X", .name "Y"]) =
      some (Ode.sha256Msg1 [s.vec x 0, s.vec x 1, s.vec x 2, s.vec x 3]
                           [s.vec y 0, s.vec y 1, s.vec y 2, s.vec y 3]) := by
  have h0 : ("sha256msg1" == "mem128") = false := by decide
  have h0w : ("sha256msg1" == "words") = false := by decide
  have h1 : ("sha256msg1" == "lanes_of64") = false := by decide
  have h2 : ("sha256msg1" == "lanes") = false := by decide
  have h3 : ("sha256msg1" == "each32") = false := by decide
  have h4 : ("sha256msg1" == "shuffle_bytes") = false := by decide
  have h5 : ("sha256msg1" == "sha256msg1") = true := by decide
  simp only [Ode.lanesOf, h0, h0w, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte,
             Ode.vecArg, hbx, hby, List.range, List.range.loop, List.map, Option.bind, Option.map]

theorem agree_sha256su0 (x y : Fin 32) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat) (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeSha256su0 x y) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectSha256su0, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vx := gs.readVReg128 (BitVec.ofNat 5 x.val)
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let res := sha256su0Res vx vy
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.cryptoSha2Reg 2#5 (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp only [Arm64.execInstWithSvc]
    change Arm64.applySimdResult gs (BitVec.ofNat 5 x.val) (Arm64.evalCryptoSha2Reg 2#5 vx vy) = _
    rw [evalCryptoSha2Reg_su0]; rfl
  let lanes := Ode.sha256Msg1 [st.vec x.val 0, st.vec x.val 1, st.vec x.val 2, st.vec x.val 3]
                              [st.vec y.val 0, st.vec y.val 1, st.vec y.val 2, st.vec y.val 3]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "sha256msg1" [.name "X", .name "Y"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectSha256su0, bind, next⟩ u st = some (.next st') := by
    have hxa : ("X" == "above128") = false := by decide
    simp only [Ode.exec, Ode.execAll, effectSha256su0, Ode.execStmt,
               lanesOf_sha256msg1 Ode.Perm.all bind st0 hbx hby, hxa, hbx, Bool.false_eq_true, ↓reduceIte,
               st', st1, st0, lanes]
  refine ⟨_, st', decode_sha256su0 x y, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  have hpk := sha256su0Res_lanes vx vy
  let x0 := vx.extractLsb' 0 32; let x1 := vx.extractLsb' 32 32
  let x2 := vx.extractLsb' 64 32; let x3 := vx.extractLsb' 96 32
  let y0 := vy.extractLsb' 0 32
  let s0 (v : BitVec 32) : BitVec 32 := v.rotateRight 7 ^^^ v.rotateRight 18 ^^^ (v >>> 3)
  let o0 := s0 x1 + x0; let o1 := s0 x2 + x1; let o2 := s0 x3 + x2; let o3 := s0 y0 + x3
  have hx0 : x0.toNat = st.vec x.val 0 := hA.vec x ⟨0, by decide⟩
  have hx1 : x1.toNat = st.vec x.val 1 := hA.vec x ⟨1, by decide⟩
  have hx2 : x2.toNat = st.vec x.val 2 := hA.vec x ⟨2, by decide⟩
  have hx3 : x3.toNat = st.vec x.val 3 := hA.vec x ⟨3, by decide⟩
  have hy0 : y0.toNat = st.vec y.val 0 := hA.vec y ⟨0, by decide⟩
  have ho0 : o0.toNat = (st.vec x.val 0 + Ode.sha256s0 (st.vec x.val 1)) % Ode.W32 := by
    simp only [o0, s0, bv32_add_toNat, bv32_sha256s0_toNat, hx0, hx1]; rw [Nat.add_comm]
  have ho1 : o1.toNat = (st.vec x.val 1 + Ode.sha256s0 (st.vec x.val 2)) % Ode.W32 := by
    simp only [o1, s0, bv32_add_toNat, bv32_sha256s0_toNat, hx1, hx2]; rw [Nat.add_comm]
  have ho2 : o2.toNat = (st.vec x.val 2 + Ode.sha256s0 (st.vec x.val 3)) % Ode.W32 := by
    simp only [o2, s0, bv32_add_toNat, bv32_sha256s0_toNat, hx2, hx3]; rw [Nat.add_comm]
  have ho3 : o3.toNat = (st.vec x.val 3 + Ode.sha256s0 (st.vec y.val 0)) % Ode.W32 := by
    simp only [o3, s0, bv32_add_toNat, bv32_sha256s0_toNat, hx3, hy0]; rw [Nat.add_comm]
  apply agreeState_writeVec hA x res lanes (u 0) ?_ _ _ hnext hpc
  intro j
  have hsu0 : lanes = [o0.toNat, o1.toNat, o2.toNat, o3.toNat] := by
    dsimp only [lanes, Ode.sha256Msg1, List.getD, List.getElem?_cons_zero,
                List.getElem?_cons_succ, Option.getD_some]
    rw [← ho0, ← ho1, ← ho2, ← ho3]
  rw [hsu0]
  match j with
  | ⟨0, _⟩ => simp only [Nat.mul_zero]; rw [show res.extractLsb' 0 32 = o0 from hpk.1]; rfl
  | ⟨1, _⟩ => simp only [Nat.mul_one]; rw [show res.extractLsb' 32 32 = o1 from hpk.2.1]; rfl
  | ⟨2, _⟩ => have h64 : 32 * 2 = 64 := rfl; simp only [h64]; rw [show res.extractLsb' 64 32 = o2 from hpk.2.2.1]; rfl
  | ⟨3, _⟩ => have h96 : 32 * 3 = 96 := rfl; simp only [h96]; rw [show res.extractLsb' 96 32 = o3 from hpk.2.2.2]; rfl

-- Shared 3-register SHA-256 encoder/decoder (`sha256h`, `sha256h2`, `sha256su1`)
private def encodeSha3 (opc : BitVec 3) (x y z : Fin 32) : BitVec 32 :=
  0x5e000000#32 ||| (BitVec.ofNat 32 z.val <<< 16) ||| (opc.zeroExtend 32 <<< 12)
                ||| (BitVec.ofNat 32 y.val <<< 5) ||| BitVec.ofNat 32 x.val

def encodeSha256h (x y z : Fin 32) : BitVec 32 := encodeSha3 4#3 x y z
def encodeSha256h2 (x y z : Fin 32) : BitVec 32 := encodeSha3 5#3 x y z
def encodeSha256su1 (x y z : Fin 32) : BitVec 32 := encodeSha3 6#3 x y z

def effectSha256h : List Ode.Stmt := [.vset (.name "X") (.call "sha256h" [.name "X", .name "Y", .name "Z"])]
def effectSha256h2 : List Ode.Stmt := [.vset (.name "X") (.call "sha256h2" [.name "X", .name "Y", .name "Z"])]
def effectSha256su1 : List Ode.Stmt := [.vset (.name "X") (.call "sha256su1" [.name "X", .name "Y", .name "Z"])]

private theorem decode_sha3 (opc : BitVec 3) (hop : (opc != 7#3) = true) (x y z : Fin 32) :
    Arm64.decode (encodeSha3 opc x y z) =
      some (.cryptoSha3Reg opc (BitVec.ofNat 5 z.val) (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) := by
  have hx : x.val < 2 ^ 5 := x.isLt; have hy : y.val < 2 ^ 5 := y.isLt; have hz : z.val < 2 ^ 5 := z.isLt
  have ho : opc.toNat < 2 ^ 3 := opc.isLt
  have hoz : opc.zeroExtend 32 = BitVec.ofNat 32 opc.toNat := by
    apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (by omega : opc.toNat < 2 ^ 32)]
  have hf : encodeSha3 opc x y z &&& 0xffe08c00#32 = 0x5e000000#32 &&& 0xffe08c00#32 := by
    have h1 : (BitVec.ofNat 32 z.val <<< 16) &&& 0xffe08c00#32 = 0#32 := field_and_eq_zero hz (by decide)
    have h2 : (BitVec.ofNat 32 opc.toNat <<< 12) &&& 0xffe08c00#32 = 0#32 := field_and_eq_zero ho (by decide)
    have h3 : (BitVec.ofNat 32 y.val <<< 5) &&& 0xffe08c00#32 = 0#32 := field_and_eq_zero hy (by decide)
    have h4 : (BitVec.ofNat 32 x.val <<< 0) &&& 0xffe08c00#32 = 0#32 := field_and_eq_zero hx (by decide)
    simp only [BitVec.shiftLeft_zero] at h4
    unfold encodeSha3; rw [hoz]; simp only [BitVec.and_or_distrib_right, h1, h2, h3, h4, BitVec.or_zero]
  have ex_opc : (encodeSha3 opc x y z).extractLsb' 12 3 = opc := by
    unfold encodeSha3; rw [hoz]; simp only [extract_or]
    have h0 : (0x5e000000#32).extractLsb' 12 3 = 0#3 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 12 3 = 0#3 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 opc.toNat <<< 12).extractLsb' 12 3 = BitVec.ofNat 3 opc.toNat := extract_field_hit (by omega)
    have h3 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 12 3 = 0#3 := extract_field_miss hy (by omega)
    have h4 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 12 3 = 0#3 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  rw [decode_at_cryptoSha3Reg hf (by decide) (by decide) ⟨by decide, by decide⟩ (by rw [ex_opc]; exact hop), ex_opc]
  have ex_x : (encodeSha3 opc x y z).extractLsb' 0 5 = BitVec.ofNat 5 x.val := by
    unfold encodeSha3; rw [hoz]; simp only [extract_or]
    have h0 : (0x5e000000#32).extractLsb' 0 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 0 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 opc.toNat <<< 12).extractLsb' 0 5 = 0#5 := extract_field_miss ho (by omega)
    have h3 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 0 5 = 0#5 := extract_field_miss hy (by omega)
    have h4 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 0 5 = BitVec.ofNat 5 x.val := extract_field_hit (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  have ex_y : (encodeSha3 opc x y z).extractLsb' 5 5 = BitVec.ofNat 5 y.val := by
    unfold encodeSha3; rw [hoz]; simp only [extract_or]
    have h0 : (0x5e000000#32).extractLsb' 5 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 5 5 = 0#5 := extract_field_miss hz (by omega)
    have h2 : (BitVec.ofNat 32 opc.toNat <<< 12).extractLsb' 5 5 = 0#5 := extract_field_miss ho (by omega)
    have h3 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 5 5 = BitVec.ofNat 5 y.val := extract_field_hit (by omega)
    have h4 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 5 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  have ex_z : (encodeSha3 opc x y z).extractLsb' 16 5 = BitVec.ofNat 5 z.val := by
    unfold encodeSha3; rw [hoz]; simp only [extract_or]
    have h0 : (0x5e000000#32).extractLsb' 16 5 = 0#5 := by decide
    have h1 : (BitVec.ofNat 32 z.val <<< 16).extractLsb' 16 5 = BitVec.ofNat 5 z.val := extract_field_hit (by omega)
    have h2 : (BitVec.ofNat 32 opc.toNat <<< 12).extractLsb' 16 5 = 0#5 := extract_field_miss ho (by omega)
    have h3 : (BitVec.ofNat 32 y.val <<< 5).extractLsb' 16 5 = 0#5 := extract_field_miss hy (by omega)
    have h4 : (BitVec.ofNat 32 x.val <<< 0).extractLsb' 16 5 = 0#5 := extract_field_miss hx (by omega)
    simp only [BitVec.shiftLeft_zero] at h4; rw [h0, h1, h2, h3, h4]; simp
  rw [ex_x, ex_y, ex_z]

-- Row 65: `sha256su1` (`X = sha256su1(X, Y, Z)`)
theorem agree_sha256su1 (x y z : Fin 32) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat) (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeSha256su1 x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectSha256su1, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vx := gs.readVReg128 (BitVec.ofNat 5 x.val)
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let x0 := vx.extractLsb' 0 32; let x1 := vx.extractLsb' 32 32
  let x2 := vx.extractLsb' 64 32; let x3 := vx.extractLsb' 96 32
  let y1 := vy.extractLsb' 32 32; let y2 := vy.extractLsb' 64 32; let y3 := vy.extractLsb' 96 32
  let z0 := vz.extractLsb' 0 32; let z2 := vz.extractLsb' 64 32; let z3 := vz.extractLsb' 96 32
  let s1 (v : BitVec 32) : BitVec 32 := v.rotateRight 17 ^^^ v.rotateRight 19 ^^^ (v >>> 10)
  let r0 := s1 z2 + x0 + y1
  let r1 := s1 z3 + x1 + y2
  let r2 := s1 r0 + x2 + y3
  let r3 := s1 r1 + x3 + z0
  let res : BitVec 128 := r3 ++ r2 ++ r1 ++ r0
  have ht := extract_append_32_96 z0 (vy.extractLsb' 32 96)
  have hsub := extract_sub96 vy
  have heval : Arm64.evalCryptoSha3Reg 6#3 vx vy vz = Except.ok res := by
    unfold Arm64.evalCryptoSha3Reg
    dsimp only
    rw [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2, hsub.1, hsub.2.1, hsub.2.2]
    rfl
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.cryptoSha3Reg 6#3 (BitVec.ofNat 5 z.val) (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) res).advancePC := by
    simp only [Arm64.execInstWithSvc]
    change Arm64.applySimdResult gs (BitVec.ofNat 5 x.val) (Arm64.evalCryptoSha3Reg 6#3 vx vy vz) = _
    rw [heval]; rfl
  let lanes := Ode.sha256Su1
    [st.vec x.val 0, st.vec x.val 1, st.vec x.val 2, st.vec x.val 3]
    [st.vec y.val 0, st.vec y.val 1, st.vec y.val 2, st.vec y.val 3]
    [st.vec z.val 0, st.vec z.val 1, st.vec z.val 2, st.vec z.val 3]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "sha256su1" [.name "X", .name "Y", .name "Z"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectSha256su1, bind, next⟩ u st = some (.next st') := by
    simp only [Ode.exec, Ode.execAll, effectSha256su1, Ode.execStmt, Ode.lanesOf, Ode.vecArg,
               hbx, hby, hbz, List.range, List.range.loop, List.map, st', st1, st0]
    rfl
  refine ⟨_, st', decode_sha3 6#3 (by decide) x y z, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  have hex := append4_32_extract r3 r2 r1 r0
  have hx0 : x0.toNat = st.vec x.val 0 := hA.vec x ⟨0, by decide⟩
  have hx1 : x1.toNat = st.vec x.val 1 := hA.vec x ⟨1, by decide⟩
  have hx2 : x2.toNat = st.vec x.val 2 := hA.vec x ⟨2, by decide⟩
  have hx3 : x3.toNat = st.vec x.val 3 := hA.vec x ⟨3, by decide⟩
  have hy1 : y1.toNat = st.vec y.val 1 := hA.vec y ⟨1, by decide⟩
  have hy2 : y2.toNat = st.vec y.val 2 := hA.vec y ⟨2, by decide⟩
  have hy3 : y3.toNat = st.vec y.val 3 := hA.vec y ⟨3, by decide⟩
  have hz0 : z0.toNat = st.vec z.val 0 := hA.vec z ⟨0, by decide⟩
  have hz2 : z2.toNat = st.vec z.val 2 := hA.vec z ⟨2, by decide⟩
  have hz3 : z3.toNat = st.vec z.val 3 := hA.vec z ⟨3, by decide⟩
  have hr0 : r0.toNat = ((st.vec x.val 0 + st.vec y.val 1) % Ode.W32 + Ode.sha256s1 (st.vec z.val 2)) % Ode.W32 := by
    simp only [r0, s1, bv32_add_toNat, bv32_sha256s1_toNat, hx0, hy1, hz2]
    rw [Nat.mod_add_mod, Nat.mod_add_mod]; congr 1; omega
  have hr1 : r1.toNat = ((st.vec x.val 1 + st.vec y.val 2) % Ode.W32 + Ode.sha256s1 (st.vec z.val 3)) % Ode.W32 := by
    simp only [r1, s1, bv32_add_toNat, bv32_sha256s1_toNat, hx1, hy2, hz3]
    rw [Nat.mod_add_mod, Nat.mod_add_mod]; congr 1; omega
  have hr2 : r2.toNat = ((st.vec x.val 2 + st.vec y.val 3) % Ode.W32 + Ode.sha256s1 r0.toNat) % Ode.W32 := by
    simp only [r2, s1, bv32_add_toNat, bv32_sha256s1_toNat, hx2, hy3]
    rw [Nat.mod_add_mod, Nat.mod_add_mod]; congr 1; omega
  have hr3 : r3.toNat = ((st.vec x.val 3 + st.vec z.val 0) % Ode.W32 + Ode.sha256s1 r1.toNat) % Ode.W32 := by
    simp only [r3, s1, bv32_add_toNat, bv32_sha256s1_toNat, hx3, hz0]
    rw [Nat.mod_add_mod, Nat.mod_add_mod]; congr 1; omega
  apply agreeState_writeVec hA x res lanes (u 0) ?_ _ _ hnext hpc
  intro j
  have hsu1 : lanes = [r0.toNat, r1.toNat, r2.toNat, r3.toNat] := by
    dsimp only [lanes, Ode.sha256Su1, Ode.sha256Msg2, List.getD, List.getElem?_cons_zero,
                List.getElem?_cons_succ, Option.getD_some]
    rw [← hr0, ← hr1, ← hr2, ← hr3]
  rw [hsu1]
  match j with
  | ⟨0, _⟩ => change (res.extractLsb' 0 32).toNat = r0.toNat; rw [hex.1]
  | ⟨1, _⟩ => change (res.extractLsb' 32 32).toNat = r1.toNat; rw [hex.2.1]
  | ⟨2, _⟩ => change (res.extractLsb' 64 32).toNat = r2.toNat; rw [hex.2.2.1]
  | ⟨3, _⟩ => change (res.extractLsb' 96 32).toNat = r3.toNat; rw [hex.2.2.2]

-- Shared 1-round & 4-round SHA-256 hash agreement lemma for `sha256h` and `sha256h2`
private def sha256HashStepBV (x y : BitVec 128) (wk : BitVec 32) : BitVec 128 × BitVec 128 :=
  let x0 := x.extractLsb' 0 32; let x1 := x.extractLsb' 32 32
  let x2 := x.extractLsb' 64 32; let x3 := x.extractLsb' 96 32
  let y0 := y.extractLsb' 0 32; let y1 := y.extractLsb' 32 32
  let y2 := y.extractLsb' 64 32; let y3 := y.extractLsb' 96 32
  let chs := Arm64.shaChoose32 y0 y1 y2
  let maj := Arm64.shaMajority32 x0 x1 x2
  let t := y3 + Arm64.sha256Sigma1 y0 + chs + wk
  let x3' := t + x3
  let y3' := t + Arm64.sha256Sigma0 x0 + maj
  (x2 ++ x1 ++ x0 ++ y3', y2 ++ y1 ++ y0 ++ x3')

private theorem sha256HashStepBV_lanes (x y : BitVec 128) (wk : BitVec 32)
    (a b c d e f g h w : Nat)
    (ha : (x.extractLsb' 0 32).toNat = a) (hb : (x.extractLsb' 32 32).toNat = b)
    (hc : (x.extractLsb' 64 32).toNat = c) (hd : (x.extractLsb' 96 32).toNat = d)
    (he : (y.extractLsb' 0 32).toNat = e) (hf : (y.extractLsb' 32 32).toNat = f)
    (hg : (y.extractLsb' 64 32).toNat = g) (hh : (y.extractLsb' 96 32).toNat = h)
    (hw : wk.toNat = w) :
    let (x', y') := sha256HashStepBV x y wk
    let (a', b', c', d', e', f', g', h') := Ode.sha256Round a b c d e f g h w
    (x'.extractLsb' 0 32).toNat = a' ∧ (x'.extractLsb' 32 32).toNat = b' ∧
    (x'.extractLsb' 64 32).toNat = c' ∧ (x'.extractLsb' 96 32).toNat = d' ∧
    (y'.extractLsb' 0 32).toNat = e' ∧ (y'.extractLsb' 32 32).toNat = f' ∧
    (y'.extractLsb' 64 32).toNat = g' ∧ (y'.extractLsb' 96 32).toNat = h' := by
  dsimp only [sha256HashStepBV, Ode.sha256Round]
  have hex := append4_32_extract (x.extractLsb' 64 32) (x.extractLsb' 32 32) (x.extractLsb' 0 32)
    ((y.extractLsb' 96 32 + Arm64.sha256Sigma1 (y.extractLsb' 0 32) +
      Arm64.shaChoose32 (y.extractLsb' 0 32) (y.extractLsb' 32 32) (y.extractLsb' 64 32) + wk) +
      Arm64.sha256Sigma0 (x.extractLsb' 0 32) +
      Arm64.shaMajority32 (x.extractLsb' 0 32) (x.extractLsb' 32 32) (x.extractLsb' 64 32))
  have hey := append4_32_extract (y.extractLsb' 64 32) (y.extractLsb' 32 32) (y.extractLsb' 0 32)
    ((y.extractLsb' 96 32 + Arm64.sha256Sigma1 (y.extractLsb' 0 32) +
      Arm64.shaChoose32 (y.extractLsb' 0 32) (y.extractLsb' 32 32) (y.extractLsb' 64 32) + wk) +
      x.extractLsb' 96 32)
  rw [hex.1, hex.2.1, hex.2.2.1, hex.2.2.2, hey.1, hey.2.1, hey.2.2.1, hey.2.2.2]
  refine ⟨?_, ha, hb, hc, ?_, he, hf, hg⟩
  · simp only [bv32_add_toNat, bv32_sha256Sigma1_toNat, bv32_shaChoose_toNat,
               bv32_sha256Sigma0_toNat, bv32_shaMajority_toNat, ha, hb, hc, he, hf, hg, hh, hw]
    rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]
  · simp only [bv32_add_toNat, bv32_sha256Sigma1_toNat, bv32_shaChoose_toNat, hd, he, hf, hg, hh, hw]
    rw [Nat.add_comm]

-- Row 66: `sha256h` (`X = sha256h(X, Y, Z)`)
theorem agree_sha256h (x y z : Fin 32) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat) (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeSha256h x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectSha256h, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vx := gs.readVReg128 (BitVec.ofNat 5 x.val)
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let s1 := sha256HashStepBV vx vy (vz.extractLsb' 0 32)
  let s2 := sha256HashStepBV s1.1 s1.2 (vz.extractLsb' 32 32)
  let s3 := sha256HashStepBV s2.1 s2.2 (vz.extractLsb' 64 32)
  let s4 := sha256HashStepBV s3.1 s3.2 (vz.extractLsb' 96 32)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.cryptoSha3Reg 4#3 (BitVec.ofNat 5 z.val) (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) s4.1).advancePC := by
    simp only [Arm64.execInstWithSvc, Arm64.evalCryptoSha3Reg, Arm64.applySimdResult,
               Arm64.sha256Hash, List.range, List.range.loop, List.foldl]
    rfl
  let lanes := Ode.sha256H
    [st.vec x.val 0, st.vec x.val 1, st.vec x.val 2, st.vec x.val 3]
    [st.vec y.val 0, st.vec y.val 1, st.vec y.val 2, st.vec y.val 3]
    [st.vec z.val 0, st.vec z.val 1, st.vec z.val 2, st.vec z.val 3]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "sha256h" [.name "X", .name "Y", .name "Z"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectSha256h, bind, next⟩ u st = some (.next st') := by
    simp only [Ode.exec, Ode.execAll, effectSha256h, Ode.execStmt, Ode.lanesOf, Ode.vecArg,
               hbx, hby, hbz, List.range, List.range.loop, List.map, st', st1, st0]
    rfl
  refine ⟨_, st', decode_sha3 4#3 (by decide) x y z, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  have h1 := sha256HashStepBV_lanes vx vy (vz.extractLsb' 0 32)
    (st.vec x.val 0) (st.vec x.val 1) (st.vec x.val 2) (st.vec x.val 3)
    (st.vec y.val 0) (st.vec y.val 1) (st.vec y.val 2) (st.vec y.val 3) (st.vec z.val 0)
    (hA.vec x ⟨0, by decide⟩) (hA.vec x ⟨1, by decide⟩) (hA.vec x ⟨2, by decide⟩) (hA.vec x ⟨3, by decide⟩)
    (hA.vec y ⟨0, by decide⟩) (hA.vec y ⟨1, by decide⟩) (hA.vec y ⟨2, by decide⟩) (hA.vec y ⟨3, by decide⟩)
    (hA.vec z ⟨0, by decide⟩)
  rcases h1 with ⟨h1a, h1b, h1c, h1d, h1e, h1f, h1g, h1h⟩
  have h2 := sha256HashStepBV_lanes s1.1 s1.2 (vz.extractLsb' 32 32) _ _ _ _ _ _ _ _ (st.vec z.val 1)
    h1a h1b h1c h1d h1e h1f h1g h1h (hA.vec z ⟨1, by decide⟩)
  rcases h2 with ⟨h2a, h2b, h2c, h2d, h2e, h2f, h2g, h2h⟩
  have h3 := sha256HashStepBV_lanes s2.1 s2.2 (vz.extractLsb' 64 32) _ _ _ _ _ _ _ _ (st.vec z.val 2)
    h2a h2b h2c h2d h2e h2f h2g h2h (hA.vec z ⟨2, by decide⟩)
  rcases h3 with ⟨h3a, h3b, h3c, h3d, h3e, h3f, h3g, h3h⟩
  have h4 := sha256HashStepBV_lanes s3.1 s3.2 (vz.extractLsb' 96 32) _ _ _ _ _ _ _ _ (st.vec z.val 3)
    h3a h3b h3c h3d h3e h3f h3g h3h (hA.vec z ⟨3, by decide⟩)
  rcases h4 with ⟨h4a, h4b, h4c, h4d, _, _, _, _⟩
  apply agreeState_writeVec hA x s4.1 lanes (u 0) ?_ _ _ hnext hpc
  intro j
  have hL : lanes = [(s4.1.extractLsb' 0 32).toNat, (s4.1.extractLsb' 32 32).toNat,
                     (s4.1.extractLsb' 64 32).toNat, (s4.1.extractLsb' 96 32).toNat] := by
    dsimp only [s4, sha256HashStepBV]
    rw [h4a, h4b, h4c, h4d]; rfl
  rw [hL]
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

-- Row 67: `sha256h2` (`X = sha256h2(X, Y, Z)`)
theorem agree_sha256h2 (x y z : Fin 32) (bind : Ode.Bind) (prog : Ode.Program) (u : Nat → Nat)
    (st : Ode.State) (gs : Arm64.State) (next : Nat) (hA : AgreeState st gs)
    (hbx : Ode.vecOf bind "X" = some x.val) (hby : Ode.vecOf bind "Y" = some y.val) (hbz : Ode.vecOf bind "Z" = some z.val)
    (hnext : prog.base + next = st.rip + 4) (hpc : st.rip + 4 < Ode.M64) :
    ∃ ginst st',
      Arm64.decode (encodeSha256h2 x y z) = some ginst ∧
      Ode.exec Ode.Perm.all prog ⟨effectSha256h2, bind, next⟩ u st = some (.next st') ∧
      AgreeState st' (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs) ∧
      (Arm64.execInstWithSvc Arm64.noSyscalls ginst gs).pstate = gs.pstate := by
  let vx := gs.readVReg128 (BitVec.ofNat 5 x.val)
  let vy := gs.readVReg128 (BitVec.ofNat 5 y.val)
  let vz := gs.readVReg128 (BitVec.ofNat 5 z.val)
  let s1 := sha256HashStepBV vy vx (vz.extractLsb' 0 32)
  let s2 := sha256HashStepBV s1.1 s1.2 (vz.extractLsb' 32 32)
  let s3 := sha256HashStepBV s2.1 s2.2 (vz.extractLsb' 64 32)
  let s4 := sha256HashStepBV s3.1 s3.2 (vz.extractLsb' 96 32)
  have hgs : Arm64.execInstWithSvc Arm64.noSyscalls
      (.cryptoSha3Reg 5#3 (BitVec.ofNat 5 z.val) (BitVec.ofNat 5 y.val) (BitVec.ofNat 5 x.val)) gs =
      (gs.writeVReg128 (BitVec.ofNat 5 x.val) s4.2).advancePC := by
    simp only [Arm64.execInstWithSvc, Arm64.evalCryptoSha3Reg, Arm64.applySimdResult,
               Arm64.sha256Hash, List.range, List.range.loop, List.foldl]
    rfl
  let lanes := Ode.sha256H2
    [st.vec x.val 0, st.vec x.val 1, st.vec x.val 2, st.vec x.val 3]
    [st.vec y.val 0, st.vec y.val 1, st.vec y.val 2, st.vec y.val 3]
    [st.vec z.val 0, st.vec z.val 1, st.vec z.val 2, st.vec z.val 3]
  let st0 : Ode.State := { st with rip := prog.base + next, trace := st.trace ++ [(st.rip, 0)] }
  let st1 : Ode.State := Ode.setVec st0 x.val lanes (u 0)
  let st' : Ode.State := Ode.noted bind st0 (.vset (.name "X") (.call "sha256h2" [.name "X", .name "Y", .name "Z"])) st1
  have hexec : Ode.exec Ode.Perm.all prog ⟨effectSha256h2, bind, next⟩ u st = some (.next st') := by
    simp only [Ode.exec, Ode.execAll, effectSha256h2, Ode.execStmt, Ode.lanesOf, Ode.vecArg,
               hbx, hby, hbz, List.range, List.range.loop, List.map, st', st1, st0]
    rfl
  refine ⟨_, st', decode_sha3 5#3 (by decide) x y z, hexec, ?_, by rw [hgs]; rfl⟩
  rw [hgs]
  have h1 := sha256HashStepBV_lanes vy vx (vz.extractLsb' 0 32)
    (st.vec y.val 0) (st.vec y.val 1) (st.vec y.val 2) (st.vec y.val 3)
    (st.vec x.val 0) (st.vec x.val 1) (st.vec x.val 2) (st.vec x.val 3) (st.vec z.val 0)
    (hA.vec y ⟨0, by decide⟩) (hA.vec y ⟨1, by decide⟩) (hA.vec y ⟨2, by decide⟩) (hA.vec y ⟨3, by decide⟩)
    (hA.vec x ⟨0, by decide⟩) (hA.vec x ⟨1, by decide⟩) (hA.vec x ⟨2, by decide⟩) (hA.vec x ⟨3, by decide⟩)
    (hA.vec z ⟨0, by decide⟩)
  rcases h1 with ⟨h1a, h1b, h1c, h1d, h1e, h1f, h1g, h1h⟩
  have h2 := sha256HashStepBV_lanes s1.1 s1.2 (vz.extractLsb' 32 32) _ _ _ _ _ _ _ _ (st.vec z.val 1)
    h1a h1b h1c h1d h1e h1f h1g h1h (hA.vec z ⟨1, by decide⟩)
  rcases h2 with ⟨h2a, h2b, h2c, h2d, h2e, h2f, h2g, h2h⟩
  have h3 := sha256HashStepBV_lanes s2.1 s2.2 (vz.extractLsb' 64 32) _ _ _ _ _ _ _ _ (st.vec z.val 2)
    h2a h2b h2c h2d h2e h2f h2g h2h (hA.vec z ⟨2, by decide⟩)
  rcases h3 with ⟨h3a, h3b, h3c, h3d, h3e, h3f, h3g, h3h⟩
  have h4 := sha256HashStepBV_lanes s3.1 s3.2 (vz.extractLsb' 96 32) _ _ _ _ _ _ _ _ (st.vec z.val 3)
    h3a h3b h3c h3d h3e h3f h3g h3h (hA.vec z ⟨3, by decide⟩)
  rcases h4 with ⟨_, _, _, _, h4e, h4f, h4g, h4h⟩
  apply agreeState_writeVec hA x s4.2 lanes (u 0) ?_ _ _ hnext hpc
  intro j
  have hL : lanes = [(s4.2.extractLsb' 0 32).toNat, (s4.2.extractLsb' 32 32).toNat,
                     (s4.2.extractLsb' 64 32).toNat, (s4.2.extractLsb' 96 32).toNat] := by
    dsimp only [s4, sha256HashStepBV]
    rw [h4e, h4f, h4g, h4h]; rfl
  rw [hL]
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

end ArmAgree
