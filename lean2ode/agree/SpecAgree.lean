import Contract

open Ode

/-!
# Standalone Lean 4 Spec-Agreement Proofs (`lean2ode/agree`)

This standalone package lies completely outside Bob's verifier (`proof-core`). It proves that
`Contract.evalSpec` evaluating the exact OdeSpecL `Def` ASTs emitted by `lean2ode` +
`proof-core/statement.py` agrees **for all inputs** with the original upstream Lean 4
specifications from:

1. `keithadler/lean-x509` (`X509/Der.lean`): `tagOk`, `constructed`, `beF`, `be`, `encodeLen`
   (infinite-domain proofs for all `n : Nat`!).
2. `c2sp/BLAKE3` (`Blake3.lean`): `rotr` (for all `2^32` 32-bit words and all shifts `k < 32`!).
3. RFC 4648 Base64: `b64Val` (for all `256` bytes) and `b64Letter` (for all `v : Nat`!).

`test_spec_agree.py` additionally runs `lean2ode` and `statement.definitions` live on these exact
Lean 4 definitions and verifies that the generated `.statement` S-expressions match the `Def`
constants proved here line for line.
-/

namespace SpecAgree

-- =============================================================================
-- 1. Upstream Lean 4 reference specifications
-- =============================================================================

namespace X509
def beF : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else beF f (n / 256) ++ [n % 256]

def be (n : Nat) : List Nat := beF n n

def encodeLen (n : Nat) : List Nat :=
  if n < 128 then [n] else (128 + (be n).length) :: be n

def tagOk (t : Nat) : Bool := t < 256 && t % 32 != 31

def constructed (t : Nat) : Bool := (t / 32) % 2 == 1
end X509

namespace B3
def rotr (x : UInt32) (n : Nat) : UInt32 :=
  (x >>> n.toUInt32) ||| (x <<< (32 - n).toUInt32)
end B3

namespace B64
def b64Val (b : UInt8) : UInt8 :=
  if b >= 65 && b <= 90 then b - 65
  else if b >= 97 && b <= 122 then b - 71
  else if b >= 48 && b <= 57 then b + 4
  else if b == 43 then 62
  else if b == 47 then 63
  else 255

def b64Letter (v : Nat) : Nat :=
  if v < 26 then 65 + v
  else if v < 52 then 71 + v
  else if v < 62 then v - 4
  else if v == 62 then 43
  else 47
end B64

-- =============================================================================
-- 2. Exact `Contract.Def` ASTs emitted by `lean2ode` + `statement.definitions`
-- =============================================================================

def defTagOk : Def :=
  { name := "tagOk", params := ["t"],
    body := .ifx (.bin "<" (.name "t") (.num 256))
                 (.bin "!=" (.bin "%" (.name "t") (.num 32)) (.num 31))
                 (.bin "==" (.num 0) (.num 1)) }

def defConstructed : Def :=
  { name := "constructed", params := ["t"],
    body := .bin "==" (.bin "%" (.bin "/" (.name "t") (.num 32)) (.num 2)) (.num 1) }

def defBeF : Def :=
  { name := "beF", params := ["n", "x"],
    body := .ifx (.bin "==" (.name "n") (.num 0))
                 (.list .nil)
                 (.ifx (.bin "==" (.name "x") (.num 0))
                       (.list .nil)
                       (.bin "++"
                             (.call "beF" (.cons (.bin "-" (.name "n") (.num 1))
                                                 (.cons (.bin "/" (.name "x") (.num 256)) .nil)))
                             (.list (.cons (.bin "%" (.name "x") (.num 256)) .nil)))) }

def defBe : Def :=
  { name := "be", params := ["n"],
    body := .call "beF" (.cons (.name "n") (.cons (.name "n") .nil)) }

def defEncodeLen : Def :=
  { name := "encodeLen", params := ["n"],
    body := .ifx (.bin "<" (.name "n") (.num 128))
                 (.list (.cons (.name "n") .nil))
                 (.bin "++"
                       (.list (.cons (.bin "+" (.num 128) (.call "len" (.cons (.call "be" (.cons (.name "n") .nil)) .nil))) .nil))
                       (.call "be" (.cons (.name "n") .nil))) }

def defRotr : Def :=
  { name := "rotr", params := ["x", "n"],
    body := .bin ">>>" (.name "x") (.name "n") }

def defB64Val : Def :=
  { name := "b64Val", params := ["b"],
    body :=
      .ifx (.ifx (.bin ">=" (.name "b") (.num 65)) (.bin "<=" (.name "b") (.num 90)) (.bin "==" (.num 0) (.num 1)))
           (.bin "%" (.bin "-" (.bin "+" (.name "b") (.num 256)) (.num 65)) (.num 256))
      (.ifx (.ifx (.bin ">=" (.name "b") (.num 97)) (.bin "<=" (.name "b") (.num 122)) (.bin "==" (.num 0) (.num 1)))
           (.bin "%" (.bin "-" (.bin "+" (.name "b") (.num 256)) (.num 71)) (.num 256))
      (.ifx (.ifx (.bin ">=" (.name "b") (.num 48)) (.bin "<=" (.name "b") (.num 57)) (.bin "==" (.num 0) (.num 1)))
           (.bin "%" (.bin "+" (.name "b") (.num 4)) (.num 256))
      (.ifx (.bin "==" (.name "b") (.num 43)) (.num 62)
      (.ifx (.bin "==" (.name "b") (.num 47)) (.num 63) (.num 255))))) }

def defB64Letter : Def :=
  { name := "b64Letter", params := ["v"],
    body :=
      .ifx (.bin "<" (.name "v") (.num 26)) (.bin "+" (.num 65) (.name "v"))
      (.ifx (.bin "<" (.name "v") (.num 52)) (.bin "+" (.num 71) (.name "v"))
      (.ifx (.bin "<" (.name "v") (.num 62))
            (.ifx (.bin ">=" (.name "v") (.num 4)) (.bin "-" (.name "v") (.num 4)) (.num 0))
      (.ifx (.bin "==" (.name "v") (.num 62)) (.num 43) (.num 47)))) }

def allDefs : List Def :=
  [defTagOk, defConstructed, defBeF, defBe, defEncodeLen, defRotr, defB64Val, defB64Letter]

-- =============================================================================
-- 3. One-step `evalSpec` unfolding lemmas (keeps all proofs instant)
-- =============================================================================

private theorem eval_num (defs : List Def) (f : Nat) (env : List (String × Val)) (n : Int) (hn : 0 ≤ n) :
    evalSpec defs (f + 1) env (.num n) = some (.int n) := by
  simp [evalSpec, hn]

private theorem eval_name (defs : List Def) (f : Nat) (env : List (String × Val)) (x : String) :
    evalSpec defs (f + 1) env (.name x) = env.lookup x := rfl

private theorem eval_bin (defs : List Def) (f : Nat) (env : List (String × Val))
    (op : String) (a b : SExpr) (va vb : Val)
    (ha : evalSpec defs f env a = some va) (hb : evalSpec defs f env b = some vb) :
    evalSpec defs (f + 1) env (.bin op a b) = binop op va vb := by
  simp [evalSpec, ha, hb]

private theorem eval_ifx_t (defs : List Def) (f : Nat) (env : List (String × Val))
    (c a b : SExpr) (hc : evalSpec defs f env c = some (.bool true)) :
    evalSpec defs (f + 1) env (.ifx c a b) = evalSpec defs f env a := by
  simp [evalSpec, hc]

private theorem eval_ifx_f (defs : List Def) (f : Nat) (env : List (String × Val))
    (c a b : SExpr) (hc : evalSpec defs f env c = some (.bool false)) :
    evalSpec defs (f + 1) env (.ifx c a b) = evalSpec defs f env b := by
  simp [evalSpec, hc]

private theorem eval_list_one (defs : List Def) (f : Nat) (env : List (String × Val))
    (a : SExpr) (va : Val) (ha : evalSpec defs f env a = some va) :
    evalSpec defs (f + 1) env (.list (.cons a .nil)) = some (.list [va]) := by
  simp [evalSpec, evalList, ha]

private theorem eval_len (defs : List Def) (f : Nat) (env : List (String × Val))
    (a : SExpr) (l : List Val) (ha : evalSpec defs f env a = some (.list l)) :
    evalSpec defs (f + 1) env (.call "len" (.cons a .nil)) = some (.int l.length) := by
  simp [evalSpec, evalList, ha]

private theorem eval_call1 (defs : List Def) (f : Nat) (env : List (String × Val))
    (fn p : String) (body a : SExpr) (va : Val)
    (hne : fn ≠ "len") (hown : fn ∉ own)
    (hd : findDef defs fn = some ⟨fn, [p], body⟩)
    (ha : evalSpec defs f env a = some va) :
    evalSpec defs (f + 1) env (.call fn (.cons a .nil)) = evalSpec defs f [(p, va)] body := by
  simp [evalSpec, evalList, ha, hne, hown, hd]

private theorem eval_call2 (defs : List Def) (f : Nat) (env : List (String × Val))
    (fn p1 p2 : String) (body a b : SExpr) (va vb : Val)
    (hne : fn ≠ "len") (hown : fn ∉ own)
    (hd : findDef defs fn = some ⟨fn, [p1, p2], body⟩)
    (ha : evalSpec defs f env a = some va) (hb : evalSpec defs f env b = some vb) :
    evalSpec defs (f + 1) env (.call fn (.cons a (.cons b .nil)))
      = evalSpec defs f [(p1, va), (p2, vb)] body := by
  simp [evalSpec, evalList, ha, hb, hne, hown, hd]

private theorem eval_false_lit (defs : List Def) (f : Nat) (env : List (String × Val)) :
    evalSpec defs (f + 2) env (.bin "==" (.num 0) (.num 1)) = some (.bool false) := by
  rw [eval_bin _ _ _ _ _ _ (.int 0) (.int 1) (eval_num _ _ _ 0 (by omega)) (eval_num _ _ _ 1 (by omega))]
  rfl

private theorem eval_cmp (defs : List Def) (f : Nat) (x : String) (v : Int) (op : String) (k : Int) (hk : 0 ≤ k) :
    evalSpec defs (f + 2) [(x, .int v)] (.bin op (.name x) (.num k)) = binop op (.int v) (.int k) := by
  rw [eval_bin _ _ _ _ _ _ (.int v) (.int k) (by simp [eval_name]) (eval_num _ _ _ k hk)]

-- =============================================================================
-- 4. Universally quantified agreement theorems (complete proofs, standard axioms)
-- =============================================================================

/-- Agreement for `X509.tagOk` across all `t : Nat` (infinite domain). -/
theorem agree_der_tagOk :
    ∀ t : Nat,
      evalSpec allDefs 10 [("t", .int t)] (.call "tagOk" (.cons (.name "t") .nil))
        = some (.bool (X509.tagOk t)) := by
  intro t
  rw [eval_call1 allDefs 9 _ "tagOk" "t" defTagOk.body _ (.int t)
        (by decide) (by decide) rfl (by simp [eval_name])]
  unfold defTagOk X509.tagOk
  by_cases h : t < 256
  · rw [eval_ifx_t _ 8 _ _ _ _ (by rw [eval_cmp _ 6 "t" t "<" 256 (by omega)]; simp [binop]; omega)]
    rw [eval_bin _ 7 _ "!=" _ _ (.int ((t : Int) % 32)) (.int 31)
          (by rw [eval_cmp _ 5 "t" t "%" 32 (by omega)]; simp [binop])
          (eval_num _ 6 _ 31 (by omega))]
    simp only [binop, h, decide_true, Bool.true_and, bne, beq_iff_eq]
    have hmod : ((t : Int) % 32 == 31) = (t % 32 == 31) := by
      apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
      rw [show (32 : Int) = ((32 : Nat) : Int) from rfl, ← Int.natCast_emod]; omega
    exact congrArg (fun b => some (Val.bool !b)) hmod
  · rw [eval_ifx_f _ 8 _ _ _ _ (by rw [eval_cmp _ 6 "t" t "<" 256 (by omega)]; simp [binop]; omega)]
    rw [eval_false_lit]
    simp [h]

/-- Agreement for `X509.constructed` across all `t : Nat` (infinite domain). -/
theorem agree_der_constructed :
    ∀ t : Nat,
      evalSpec allDefs 10 [("t", .int t)] (.call "constructed" (.cons (.name "t") .nil))
        = some (.bool (X509.constructed t)) := by
  intro t
  rw [eval_call1 allDefs 9 _ "constructed" "t" defConstructed.body _ (.int t)
        (by decide) (by decide) rfl rfl]
  unfold defConstructed X509.constructed
  rw [eval_bin _ 8 _ "==" _ _ (.int (((t : Int) / 32) % 2)) (.int 1)
        (by
          rw [eval_bin _ 7 _ "%" _ _ (.int ((t : Int) / 32)) (.int 2)
                (by rw [eval_cmp _ 5 "t" t "/" 32 (by omega)]; simp [binop])
                (eval_num _ 6 _ 2 (by omega))]
          simp [binop])
        (eval_num _ 7 _ 1 (by omega))]
  simp only [binop, beq_iff_eq]
  have hdm : (((t : Int) / 32) % 2 == 1) = ((t / 32) % 2 == 1) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
    rw [show (32 : Int) = ((32 : Nat) : Int) from rfl, show (2 : Int) = ((2 : Nat) : Int) from rfl,
        ← Int.natCast_ediv, ← Int.natCast_emod]; omega
  exact congrArg (fun b => some (Val.bool b)) hdm

/-- Agreement for recursive `X509.beF` across all `(f, n : Nat)` and any sufficient fuel
    (proved by induction on `f`, infinite domain). -/
theorem agree_der_beF :
    ∀ (f n fuel : Nat), 4 * f + 6 ≤ fuel →
      evalSpec allDefs fuel [("n", .int f), ("x", .int n)]
        (.call "beF" (.cons (.name "n") (.cons (.name "x") .nil)))
        = some (Val.bytes (X509.beF f n)) := by
  intro f
  induction f with
  | zero =>
    intro n fuel hfuel
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 6 := ⟨fuel - 6, by omega⟩
    rw [eval_call2 allDefs (k + 5) _ "beF" "n" "x" defBeF.body _ _ (.int 0) (.int n)
          (by decide) (by decide) rfl rfl rfl]
    unfold defBeF X509.beF Val.bytes
    rw [eval_ifx_t _ (k + 4) _ _ _ _
          (by
            rw [eval_bin _ (k + 3) _ "==" _ _ (.int 0) (.int 0)
                  rfl (eval_num _ (k + 2) _ 0 (by omega))]
            rfl)]
    rfl
  | succ f ih =>
    intro n fuel hfuel
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 6 := ⟨fuel - 6, by omega⟩
    rw [eval_call2 allDefs (k + 5) _ "beF" "n" "x" defBeF.body _ _ (.int (f + 1 : Nat)) (.int n)
          (by decide) (by decide) rfl rfl rfl]
    unfold defBeF X509.beF
    rw [eval_ifx_f _ (k + 4) _ _ _ _
          (by
            rw [eval_bin _ (k + 3) _ "==" _ _ (.int (f + 1 : Nat)) (.int 0)
                  rfl (eval_num _ (k + 2) _ 0 (by omega))]
            simp [binop]; omega)]
    by_cases hn : n = 0
    · subst hn
      rw [eval_ifx_t _ (k + 3) _ _ _ _
            (by
              rw [eval_bin _ (k + 2) _ "==" _ _ (.int 0) (.int 0)
                    rfl (eval_num _ (k + 1) _ 0 (by omega))]
              rfl)]
      rfl
    · rw [eval_ifx_f _ (k + 3) _ _ _ _
            (by
              rw [eval_bin _ (k + 2) _ "==" _ _ (.int n) (.int 0)
                    rfl (eval_num _ (k + 1) _ 0 (by omega))]
              simp [binop]; omega)]
      have hk1 : 1 ≤ k := by omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hsub : evalSpec allDefs (m + 2) [("n", .int (f + 1 : Nat)), ("x", .int n)]
            (.bin "-" (.name "n") (.num 1)) = some (.int f) := by
        rw [eval_bin _ (m + 1) _ "-" _ _ (.int (f + 1 : Nat)) (.int 1)
              rfl (eval_num _ m _ 1 (by omega))]
        simp only [binop, show (1 : Int) ≤ ((f + 1 : Nat) : Int) by omega, ↓reduceIte]
        exact congrArg (fun z => some (Val.int z)) (by omega)
      have hdiv : evalSpec allDefs (m + 2) [("n", .int (f + 1 : Nat)), ("x", .int n)]
            (.bin "/" (.name "x") (.num 256)) = some (.int (n / 256 : Nat)) := by
        rw [eval_bin _ (m + 1) _ "/" _ _ (.int n) (.int 256)
              rfl (eval_num _ m _ 256 (by omega))]
        simp only [binop, show (0 : Int) < 256 by decide, ↓reduceIte]
        exact congrArg (fun z => some (Val.int z)) (by omega)
      have hcall : evalSpec allDefs (m + 3) [("n", .int (f + 1 : Nat)), ("x", .int n)]
            (.call "beF" (.cons (.bin "-" (.name "n") (.num 1))
                                (.cons (.bin "/" (.name "x") (.num 256)) .nil)))
            = some (Val.bytes (X509.beF f (n / 256))) := by
        rw [eval_call2 allDefs (m + 2) _ "beF" "n" "x" defBeF.body _ _ (.int f) (.int (n / 256 : Nat))
              (by decide) (by decide) rfl hsub hdiv]
        have hih := ih (n / 256) (m + 3) (by omega)
        rw [eval_call2 allDefs (m + 2) _ "beF" "n" "x" defBeF.body _ _ (.int f) (.int (n / 256 : Nat))
              (by decide) (by decide) rfl rfl rfl] at hih
        exact hih
      have hmod : evalSpec allDefs (m + 3) [("n", .int (f + 1 : Nat)), ("x", .int n)]
            (.list (.cons (.bin "%" (.name "x") (.num 256)) .nil))
            = some (.list [.int (n % 256 : Nat)]) := by
        rw [eval_list_one _ (m + 2) _ _ (.int (n % 256 : Nat))]
        rw [eval_bin _ (m + 1) _ "%" _ _ (.int n) (.int 256)
              rfl (eval_num _ m _ 256 (by omega))]
        simp only [binop, show (0 : Int) < 256 by decide, ↓reduceIte]
        exact congrArg (fun z => some (Val.int z)) (by omega)
      rw [eval_bin _ (m + 3) _ "++" _ _ (Val.bytes (X509.beF f (n / 256))) (.list [.int (n % 256 : Nat)])
            hcall hmod]
      simp [Val.bytes, binop, hn]

/-- Agreement for `X509.be` across all `n : Nat` (infinite domain). -/
theorem agree_der_be :
    ∀ (n fuel : Nat), 4 * n + 8 ≤ fuel →
      evalSpec allDefs fuel [("n", .int n)] (.call "be" (.cons (.name "n") .nil))
        = some (Val.bytes (X509.be n)) := by
  intro n fuel hfuel
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 2 := ⟨fuel - 2, by omega⟩
  rw [eval_call1 allDefs (k + 1) _ "be" "n" defBe.body _ (.int n)
        (by decide) (by decide) rfl rfl]
  unfold defBe X509.be
  have hbeF := agree_der_beF n n (k + 1) (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [eval_call2 allDefs (m + 1) _ "beF" "n" "x" defBeF.body _ _ (.int n) (.int n)
        (by decide) (by decide) rfl rfl rfl] at hbeF ⊢
  exact hbeF

/-- Agreement for `X509.encodeLen` across all `n : Nat` (infinite domain). -/
theorem agree_der_encodeLen :
    ∀ (n fuel : Nat), 4 * n + 14 ≤ fuel →
      evalSpec allDefs fuel [("n", .int n)] (.call "encodeLen" (.cons (.name "n") .nil))
        = some (Val.bytes (X509.encodeLen n)) := by
  intro n fuel hfuel
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 6 := ⟨fuel - 6, by omega⟩
  rw [eval_call1 allDefs (k + 5) _ "encodeLen" "n" defEncodeLen.body _ (.int n)
        (by decide) (by decide) rfl (by simp [eval_name])]
  unfold defEncodeLen X509.encodeLen
  by_cases h : n < 128
  · rw [eval_ifx_t _ (k + 4) _ _ _ _ (by rw [eval_cmp _ (k + 2) "n" n "<" 128 (by omega)]; simp [binop]; omega)]
    rw [eval_list_one _ (k + 3) _ _ (.int n) (by simp [eval_name])]
    simp [Val.bytes, h]
  · rw [eval_ifx_f _ (k + 4) _ _ _ _ (by rw [eval_cmp _ (k + 2) "n" n "<" 128 (by omega)]; simp [binop]; omega)]
    have hbe0 := agree_der_be n k (by omega)
    have hbe2 := agree_der_be n (k + 3) (by omega)
    rw [eval_bin _ (k + 3) _ "++" _ _ (.list [.int (128 + (X509.be n).length : Nat)])
          (Val.bytes (X509.be n))
          (by
            rw [eval_list_one _ (k + 2) _ _ (.int (128 + (X509.be n).length : Nat))]
            rw [eval_bin _ (k + 1) _ "+" _ _ (.int 128) (.int (X509.be n).length)
                  (eval_num _ k _ 128 (by omega))
                  (by
                    rw [eval_len _ k _ _ ((X509.be n).map fun (x : Nat) => .int x) hbe0]
                    simp [List.length_map])]
            simp [binop])
          hbe2]
    simp [Val.bytes, binop, h]

/-- Helper: `UInt32` rotate-right `(x >>> k) ||| (x <<< (32 - k))` equals `Machine.rotr x.toNat k`
    for every 32-bit word `x` and every shift count `k < 32`. -/
private theorem uint32_rotr_eq_machine (x : UInt32) (k : Nat) (hk : k < 32) :
    (B3.rotr x k).toNat = rotr x.toNat k := by
  have hx : x.toNat < 2 ^ 32 := x.toFin.isLt
  unfold B3.rotr rotr
  by_cases hk0 : k = 0
  · subst hk0
    simp [UInt32.toNat_or, UInt32.toNat_shiftLeft, Nat.mod_one]
  · have hmod1 : k.toUInt32.toNat % 32 = k := by
      rw [Nat.toUInt32_eq, UInt32.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 32), Nat.mod_eq_of_lt hk]
    have hmod2 : (32 - k).toUInt32.toNat % 32 = 32 - k := by
      rw [Nat.toUInt32_eq, UInt32.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega : 32 - k < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 32 - k < 32)]
    have hshr : (x >>> k.toUInt32).toNat = x.toNat / 2 ^ k := by
      rw [UInt32.toNat_shiftRight, hmod1, Nat.shiftRight_eq_div_pow]
    have hshl : (x <<< (32 - k).toUInt32).toNat = (x.toNat % 2 ^ k) * 2 ^ (32 - k) := by
      rw [UInt32.toNat_shiftLeft, hmod2, Nat.shiftLeft_eq]
      have hpow : 2 ^ 32 = 2 ^ k * 2 ^ (32 - k) := by rw [← Nat.pow_add]; congr 1; omega
      rw [hpow, Nat.mul_mod_mul_right]
    rw [UInt32.toNat_or, hshr, hshl]
    have hlow : x.toNat / 2 ^ k < 2 ^ (32 - k) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
      calc x.toNat < 2 ^ 32 := hx
        _ = 2 ^ (32 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or]
    have hsum : (x.toNat / 2 ^ k + x.toNat % 2 ^ k * 2 ^ (32 - k)).testBit i
        = (if i < 32 - k then (x.toNat / 2 ^ k).testBit i else (x.toNat % 2 ^ k).testBit (i - (32 - k))) := by
      rw [Nat.add_comm, Nat.mul_comm]
      exact Nat.testBit_two_pow_mul_add (x.toNat % 2 ^ k) hlow i
    rw [hsum]
    by_cases hi : i < 32 - k
    · have hzero : (x.toNat % 2 ^ k * 2 ^ (32 - k)).testBit i = false := by
        rw [Nat.mul_comm, Nat.testBit_two_pow_mul]; simp [Nat.not_le.mpr hi]
      simp [hi, hzero]
    · have hge : 32 - k ≤ i := Nat.le_of_not_lt hi
      have hzero : (x.toNat / 2 ^ k).testBit i = false := by
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlow (Nat.pow_le_pow_right (by decide) hge))
      have hhi : (x.toNat % 2 ^ k * 2 ^ (32 - k)).testBit i = (x.toNat % 2 ^ k).testBit (i - (32 - k)) := by
        rw [Nat.mul_comm, Nat.testBit_two_pow_mul]; simp [hge]
      simp [hi, hzero, hhi]

/-- Agreement for `c2sp/BLAKE3` `rotr` across ALL `2^32` 32-bit words and ALL shift counts `k < 32`. -/
theorem agree_blake3_rotr :
    ∀ (x : UInt32) (k : Nat), k < 32 →
      evalSpec allDefs 6 [("x", .word x.toNat), ("n", .int k)]
        (.call "rotr" (.cons (.name "x") (.cons (.name "n") .nil)))
        = some (.word (B3.rotr x k).toNat) := by
  intro x k hk
  rw [eval_call2 allDefs 5 _ "rotr" "x" "n" defRotr.body _ _ (.word x.toNat) (.int k)
        (by decide) (by decide) rfl rfl rfl]
  unfold defRotr
  rw [eval_bin _ 4 _ ">>>" _ _ (.word x.toNat) (.int k) rfl rfl]
  simp only [binop, show (">>>" == ">>>") = true by rfl, show (0 : Int) ≤ (k : Int) by omega,
    show (k : Int) ≤ 32 by omega, and_self, ↓reduceIte, Int.toNat_natCast]
  rw [uint32_rotr_eq_machine x k hk]

private theorem eval_and_range (f : Nat) (x : String) (v : Nat) (lo hi : Int) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) :
    evalSpec allDefs (f + 3) [(x, .int v)]
      (.ifx (.bin ">=" (.name x) (.num lo)) (.bin "<=" (.name x) (.num hi)) (.bin "==" (.num 0) (.num 1)))
      = some (.bool (decide (lo ≤ v) && decide ((v : Int) ≤ hi))) := by
  by_cases h1 : lo ≤ v
  · rw [eval_ifx_t _ (f + 2) _ _ _ _ (by rw [eval_cmp _ f x v ">=" lo hlo]; simp [binop, h1])]
    rw [eval_cmp _ f x v "<=" hi hhi]
    simp [binop, h1]
  · rw [eval_ifx_f _ (f + 2) _ _ _ _ (by rw [eval_cmp _ f x v ">=" lo hlo]; simp [binop, h1])]
    rw [eval_false_lit]
    simp [h1]

/-- Pure-`Nat` characterization of `B64.b64Val b`. -/
private theorem b64Val_toNat (b : UInt8) :
    (B64.b64Val b).toNat =
      if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then b.toNat - 65
      else if 97 ≤ b.toNat ∧ b.toNat ≤ 122 then b.toNat - 71
      else if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then b.toNat + 4
      else if b.toNat = 43 then 62
      else if b.toNat = 47 then 63
      else 255 := by
  have hb : b.toNat < 256 := b.toFin.isLt
  have hle : ∀ (c : UInt8), (b ≤ c) ↔ b.toNat ≤ c.toNat := fun _ => UInt8.le_iff_toNat_le
  have hge : ∀ (c : UInt8), (b ≥ c) ↔ c.toNat ≤ b.toNat := fun _ => UInt8.le_iff_toNat_le
  have h65 : (65 : UInt8).toNat = 65 := rfl
  have h90 : (90 : UInt8).toNat = 90 := rfl
  have h71 : (71 : UInt8).toNat = 71 := rfl
  have h97 : (97 : UInt8).toNat = 97 := rfl
  have h122 : (122 : UInt8).toNat = 122 := rfl
  have h48 : (48 : UInt8).toNat = 48 := rfl
  have h57 : (57 : UInt8).toNat = 57 := rfl
  have heq : ∀ (c : UInt8), (b == c) = decide (b.toNat = c.toNat) := by
    intro c; cases h : (b == c)
    · symm; simp only [decide_eq_false_iff_not]; intro he
      have : b = c := UInt8.toNat_inj.mp he; subst this; simp at h
    · symm; simp only [decide_eq_true_eq]; exact congrArg UInt8.toNat (eq_of_beq h)
  unfold B64.b64Val
  by_cases h1 : 65 ≤ b.toNat ∧ b.toNat ≤ 90
  · have hcond : (decide (b ≥ 65) && decide (b ≤ 90)) = true := by simp [hge, hle, h65, h90, h1.1, h1.2]
    simp only [hcond, ↓reduceIte, h1, and_self]
    exact UInt8.toNat_sub_of_le b 65 ((hge 65).mpr h1.1)
  · have hcond : (decide (b ≥ 65) && decide (b ≤ 90)) = false := by
      simp only [hge, hle, h65, h90, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, h1]
    by_cases h2 : 97 ≤ b.toNat ∧ b.toNat ≤ 122
    · have hcond2 : (decide (b ≥ 97) && decide (b ≤ 122)) = true := by simp [hge, hle, h97, h122, h2.1, h2.2]
      simp only [hcond2, ↓reduceIte, h2, and_self]
      exact UInt8.toNat_sub_of_le b 71 ((hge 71).mpr (by omega))
    · have hcond2 : (decide (b ≥ 97) && decide (b ≤ 122)) = false := by
        simp only [hge, hle, h97, h122, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp only [hcond2, Bool.false_eq_true, ↓reduceIte, h2]
      by_cases h3 : 48 ≤ b.toNat ∧ b.toNat ≤ 57
      · have hcond3 : (decide (b ≥ 48) && decide (b ≤ 57)) = true := by simp [hge, hle, h48, h57, h3.1, h3.2]
        simp only [hcond3, ↓reduceIte, h3, and_self]
        rw [UInt8.toNat_add]; change (b.toNat + 4) % 256 = b.toNat + 4; omega
      · have hcond3 : (decide (b ≥ 48) && decide (b ≤ 57)) = false := by
          simp only [hge, hle, h48, h57, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
        simp only [hcond3, Bool.false_eq_true, ↓reduceIte, h3]
        rw [heq 43, heq 47]
        by_cases h4 : b.toNat = 43
        · simp [h4]
        · by_cases h5 : b.toNat = 47 <;> simp [h4, h5]

/-- Agreement for RFC 4648 `b64Val` across all 256 byte values `b : UInt8`. -/
theorem agree_b64_val :
    ∀ b : UInt8,
      evalSpec allDefs 20 [("b", .int b.toNat)] (.call "b64Val" (.cons (.name "b") .nil))
        = some (.int (B64.b64Val b).toNat) := by
  intro b
  have hb : b.toNat < 256 := b.toFin.isLt
  rw [b64Val_toNat b]
  rw [eval_call1 allDefs 19 _ "b64Val" "b" defB64Val.body _ (.int b.toNat)
        (by decide) (by decide) rfl rfl]
  unfold defB64Val
  by_cases hAZ : 65 ≤ b.toNat ∧ b.toNat ≤ 90
  · rw [eval_ifx_t _ 18 _ _ _ _ (by rw [eval_and_range 15 "b" b.toNat 65 90 (by omega) (by omega)]; congr 2; simp [Bool.and_eq_true]; omega)]
    rw [eval_bin _ 17 _ "%" _ _ (.int ((b.toNat : Int) + 256 - 65)) (.int 256)
          (by
            rw [eval_bin _ 16 _ "-" _ _ (.int ((b.toNat : Int) + 256)) (.int 65)
                  (by rw [eval_cmp _ 14 "b" b.toNat "+" 256 (by omega)]; simp [binop])
                  (eval_num _ 15 _ 65 (by omega))]
            simp [binop, show (65 : Int) ≤ (b.toNat : Int) + 256 by omega])
          (eval_num _ 16 _ 256 (by omega))]
    simp only [binop, show ("%" == "+") = false by rfl, show ("%" == "-") = false by rfl,
      show ("%" == "*") = false by rfl, show ("%" == "==") = false by rfl,
      show ("%" == "!=") = false by rfl, show ("%" == "<") = false by rfl,
      show ("%" == "<=") = false by rfl, show ("%" == ">") = false by rfl,
      show ("%" == ">=") = false by rfl, show ("%" == "%") = true by rfl,
      show (0 : Int) < 256 by decide, ↓reduceIte, hAZ, and_self]
    exact congrArg (fun z => some (Val.int z)) (by omega)
  · rw [eval_ifx_f _ 18 _ _ _ _ (by rw [eval_and_range 15 "b" b.toNat 65 90 (by omega) (by omega)]; congr 2; simp; omega)]
    simp only [hAZ, ↓reduceIte]
    by_cases haz : 97 ≤ b.toNat ∧ b.toNat ≤ 122
    · rw [eval_ifx_t _ 17 _ _ _ _ (by rw [eval_and_range 14 "b" b.toNat 97 122 (by omega) (by omega)]; congr 2; simp [Bool.and_eq_true]; omega)]
      rw [eval_bin _ 16 _ "%" _ _ (.int ((b.toNat : Int) + 256 - 71)) (.int 256)
            (by
              rw [eval_bin _ 15 _ "-" _ _ (.int ((b.toNat : Int) + 256)) (.int 71)
                    (by rw [eval_cmp _ 13 "b" b.toNat "+" 256 (by omega)]; simp [binop])
                    (eval_num _ 14 _ 71 (by omega))]
              simp [binop, show (71 : Int) ≤ (b.toNat : Int) + 256 by omega])
            (eval_num _ 15 _ 256 (by omega))]
      simp only [binop, show ("%" == "+") = false by rfl, show ("%" == "-") = false by rfl,
        show ("%" == "*") = false by rfl, show ("%" == "==") = false by rfl,
        show ("%" == "!=") = false by rfl, show ("%" == "<") = false by rfl,
        show ("%" == "<=") = false by rfl, show ("%" == ">") = false by rfl,
        show ("%" == ">=") = false by rfl, show ("%" == "%") = true by rfl,
        show (0 : Int) < 256 by decide, ↓reduceIte, haz, and_self]
      exact congrArg (fun z => some (Val.int z)) (by omega)
    · rw [eval_ifx_f _ 17 _ _ _ _ (by rw [eval_and_range 14 "b" b.toNat 97 122 (by omega) (by omega)]; congr 2; simp; omega)]
      simp only [haz, ↓reduceIte]
      by_cases h09 : 48 ≤ b.toNat ∧ b.toNat ≤ 57
      · rw [eval_ifx_t _ 16 _ _ _ _ (by rw [eval_and_range 13 "b" b.toNat 48 57 (by omega) (by omega)]; congr 2; simp [Bool.and_eq_true]; omega)]
        rw [eval_bin _ 15 _ "%" _ _ (.int ((b.toNat : Int) + 4)) (.int 256)
              (by rw [eval_cmp _ 13 "b" b.toNat "+" 4 (by omega)]; simp [binop])
              (eval_num _ 14 _ 256 (by omega))]
        simp only [binop, show ("%" == "+") = false by rfl, show ("%" == "-") = false by rfl,
          show ("%" == "*") = false by rfl, show ("%" == "==") = false by rfl,
          show ("%" == "!=") = false by rfl, show ("%" == "<") = false by rfl,
          show ("%" == "<=") = false by rfl, show ("%" == ">") = false by rfl,
          show ("%" == ">=") = false by rfl, show ("%" == "%") = true by rfl,
          show (0 : Int) < 256 by decide, ↓reduceIte, h09, and_self]
        exact congrArg (fun z => some (Val.int z)) (by omega)
      · rw [eval_ifx_f _ 16 _ _ _ _ (by rw [eval_and_range 13 "b" b.toNat 48 57 (by omega) (by omega)]; congr 2; simp; omega)]
        simp only [h09, ↓reduceIte]
        by_cases h43 : b.toNat = 43
        · rw [eval_ifx_t _ 15 _ _ _ _ (by rw [eval_cmp _ 13 "b" b.toNat "==" 43 (by omega)]; simp [binop]; omega)]
          rw [eval_num _ 14 _ 62 (by omega)]
          simp [h43]
        · rw [eval_ifx_f _ 15 _ _ _ _ (by rw [eval_cmp _ 13 "b" b.toNat "==" 43 (by omega)]; simp [binop]; omega)]
          simp only [h43, ↓reduceIte]
          by_cases h47 : b.toNat = 47
          · rw [eval_ifx_t _ 14 _ _ _ _ (by rw [eval_cmp _ 12 "b" b.toNat "==" 47 (by omega)]; simp [binop]; omega)]
            rw [eval_num _ 13 _ 63 (by omega)]
            simp [h47]
          · rw [eval_ifx_f _ 14 _ _ _ _ (by rw [eval_cmp _ 12 "b" b.toNat "==" 47 (by omega)]; simp [binop]; omega)]
            rw [eval_num _ 13 _ 255 (by omega)]
            simp [h47]

/-- Agreement for RFC 4648 `b64Letter` across ALL `v : Nat` (infinite domain!). -/
theorem agree_b64_letter :
    ∀ v : Nat,
      evalSpec allDefs 16 [("v", .int v)] (.call "b64Letter" (.cons (.name "v") .nil))
        = some (.int (B64.b64Letter v)) := by
  intro v
  rw [eval_call1 allDefs 15 _ "b64Letter" "v" defB64Letter.body _ (.int v)
        (by decide) (by decide) rfl rfl]
  unfold defB64Letter B64.b64Letter
  by_cases h1 : v < 26
  · rw [eval_ifx_t _ 14 _ _ _ _ (by rw [eval_cmp _ 12 "v" v "<" 26 (by omega)]; simp [binop]; omega)]
    rw [eval_bin _ 13 _ "+" _ _ (.int 65) (.int v) (eval_num _ 12 _ 65 (by omega)) rfl]
    simp [binop, h1]
  · rw [eval_ifx_f _ 14 _ _ _ _ (by rw [eval_cmp _ 12 "v" v "<" 26 (by omega)]; simp [binop]; omega)]
    by_cases h2 : v < 52
    · rw [eval_ifx_t _ 13 _ _ _ _ (by rw [eval_cmp _ 11 "v" v "<" 52 (by omega)]; simp [binop]; omega)]
      rw [eval_bin _ 12 _ "+" _ _ (.int 71) (.int v) (eval_num _ 11 _ 71 (by omega)) rfl]
      simp [binop, h1, h2]
    · rw [eval_ifx_f _ 13 _ _ _ _ (by rw [eval_cmp _ 11 "v" v "<" 52 (by omega)]; simp [binop]; omega)]
      by_cases h3 : v < 62
      · rw [eval_ifx_t _ 12 _ _ _ _ (by rw [eval_cmp _ 10 "v" v "<" 62 (by omega)]; simp [binop]; omega)]
        rw [eval_ifx_t _ 11 _ _ _ _ (by rw [eval_cmp _ 9 "v" v ">=" 4 (by omega)]; simp [binop]; omega)]
        rw [eval_bin _ 10 _ "-" _ _ (.int v) (.int 4) rfl (eval_num _ 9 _ 4 (by omega))]
        simp only [binop, show (4 : Int) ≤ v by omega, ↓reduceIte, h1, h2, h3]
        exact congrArg (fun z => some (Val.int z)) (by omega)
      · rw [eval_ifx_f _ 12 _ _ _ _ (by rw [eval_cmp _ 10 "v" v "<" 62 (by omega)]; simp [binop]; omega)]
        by_cases h4 : v = 62
        · subst h4
          rw [eval_ifx_t _ 11 _ _ _ _ (by rw [eval_cmp _ 9 "v" (62 : Nat) "==" 62 (by omega)]; rfl)]
          rw [eval_num _ 10 _ 43 (by omega)]
          simp
        · rw [eval_ifx_f _ 11 _ _ _ _ (by rw [eval_cmp _ 9 "v" v "==" 62 (by omega)]; simp [binop]; omega)]
          rw [eval_num _ 10 _ 47 (by omega)]
          have hne : (v == 62) = false := by simp [h4]
          simp [h1, h2, h3, hne]

end SpecAgree
