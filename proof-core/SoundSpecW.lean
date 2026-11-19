import SoundCall
import SoundList
import SoundVec

/-!
# The specification on words: what `weval` gives is what the account's `evalSpec` gives

`weval` (Core.lean) works an expression of the specification out on the terms of the table. Here: the value
it gives stands for the value `evalSpec` gives with the same fuel, the names being the contract's at entry.
So an `ensures` of a whole run of words that the verifier has passed holds of the machine's state.
-/

namespace Ode

open Arithmetic

/-- What a value on words stands for, the unknowns being `ρ` and the table `T`: a value of the account. -/
inductive WDen (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (T : List Node) : WVal → Val → Prop
  | int (n : Int) : WDen ctx s0 ρ T (.int n) (.int n)
  | bool (b : Bool) : WDen ctx s0 ρ T (.bool b) (.bool b)
  | num (r : Row) : WDen ctx s0 ρ T (.num r) (.int (ev ρ r))
  | word (xs : List Nat) : WDen ctx s0 ρ T (.word xs) (.word (sumList (xs.map (den (inpOf ctx s0) ρ T)) % W32))
  | counter (r : Row) (h : 0 ≤ ev ρ r) : WDen ctx s0 ρ T (.counter r) (.counter ((ev ρ r).toNat % 2 ^ 64))
  | nil : WDen ctx s0 ρ T (.list []) (.list [])
  | cons {v : WVal} {a : Val} {vs : List WVal} {as : List Val} :
      WDen ctx s0 ρ T v a → WDen ctx s0 ρ T (.list vs) (.list as) → WDen ctx s0 ρ T (.list (v :: vs)) (.list (a :: as))
  | run (r n : Nat) (hb : ∀ k, k < n → s0.mem (s0.reg r + k) < 256) :
      WDen ctx s0 ρ T (.run r n) (.list ((List.range n).map fun k => Val.int (s0.mem (s0.reg r + k))))
  | other (a : Val) : WDen ctx s0 ρ T .other a

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {T : List Node}

theorem WDen.int_inv {n : Int} {a : Val} (h : WDen ctx s0 ρ T (.int n) a) : a = .int n := by cases h; rfl
theorem WDen.bool_inv {b : Bool} {a : Val} (h : WDen ctx s0 ρ T (.bool b) a) : a = .bool b := by cases h; rfl
theorem WDen.list_inv {l : List WVal} {a : Val} (h : WDen ctx s0 ρ T (.list l) a) : ∃ l', a = .list l' := by
  cases h with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

theorem WDen.length : ∀ {l : List WVal} {l' : List Val}, WDen ctx s0 ρ T (.list l) (.list l') → l.length = l'.length
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by
    cases h with
    | cons h1 h2 => simp [WDen.length h2]

theorem WDen.getElem? : ∀ {l : List WVal} {l' : List Val} {k : Nat} {v : WVal}, WDen ctx s0 ρ T (.list l) (.list l') → l[k]? = some v →
    ∃ a, l'[k]? = some a ∧ WDen ctx s0 ρ T v a
  | [], _, _, _, _, hk => by simp at hk
  | x :: xs, _, k, v, h, hk => by
    cases h with
    | cons h1 h2 =>
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero] at hk
        injection hk with hk; subst hk
        exact ⟨_, by simp, h1⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        obtain ⟨a, ha, hd⟩ := WDen.getElem? h2 hk
        exact ⟨a, by simpa using ha, hd⟩

theorem WDen.append : ∀ {l1 : List WVal} {l1' : List Val} {l2 : List WVal} {l2' : List Val}, WDen ctx s0 ρ T (.list l1) (.list l1') →
    WDen ctx s0 ρ T (.list l2) (.list l2') → WDen ctx s0 ρ T (.list (l1 ++ l2)) (.list (l1' ++ l2'))
  | [], _, _, _, h1, h2 => by cases h1; exact h2
  | _ :: _, _, _, _, h1, h2 => by
    cases h1 with
    | cons ha hr => exact WDen.cons ha (WDen.append hr h2)

theorem WDen.set : ∀ {l : List WVal} {l' : List Val} {k : Nat} {x : WVal} {a : Val}, WDen ctx s0 ρ T (.list l) (.list l') →
    WDen ctx s0 ρ T x a → WDen ctx s0 ρ T (.list (l.set k x)) (.list (l'.set k a))
  | [], _, _, _, _, h, _ => by cases h; exact WDen.nil
  | _ :: _, _, k, _, _, h, hx => by
    cases h with
    | cons h1 h2 =>
      cases k with
      | zero => exact WDen.cons hx h2
      | succ k => exact WDen.cons h1 (WDen.set h2 hx)

/-- The names on words stand for the names of the account, one for one. -/
def EnvDen (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (T : List Node) : List (String × WVal) → List (String × Val) → Prop
  | [], [] => True
  | (x, v) :: e, (y, a) :: e' => x = y ∧ WDen ctx s0 ρ T v a ∧ EnvDen ctx s0 ρ T e e'
  | _, _ => False

theorem EnvDen.lookup {x : String} : ∀ {env : List (String × WVal)} {env' : List (String × Val)} {v : WVal},
    EnvDen ctx s0 ρ T env env' → env.lookup x = some v → ∃ a, env'.lookup x = some a ∧ WDen ctx s0 ρ T v a
  | [], [], _, _, h => by simp at h
  | [], _ :: _, _, hE, _ => by simp [EnvDen] at hE
  | _ :: _, [], _, hE, _ => by simp [EnvDen] at hE
  | (y, w) :: e, (y', a) :: e', v, hE, h => by
    obtain ⟨rfl, hw, hE'⟩ := hE
    simp only [List.lookup] at h ⊢
    cases hxy : x == y with
    | true =>
      simp only [hxy] at h ⊢
      injection h with h; subst h
      exact ⟨a, rfl, hw⟩
    | false =>
      simp only [hxy] at h ⊢
      exact EnvDen.lookup hE' h

theorem EnvDen.zip : ∀ {ps : List String} {vs : List WVal} {as : List Val}, WDen ctx s0 ρ T (.list vs) (.list as) →
    EnvDen ctx s0 ρ T (ps.zip vs) (ps.zip as)
  | [], _, _, _ => by simp [EnvDen]
  | _ :: _, [], _, h => by cases h; simp [EnvDen]
  | p :: ps, _ :: _, _, h => by
    cases h with
    | cons h1 h2 => exact ⟨rfl, h1, EnvDen.zip h2⟩

end

/-! ## What is looked up -/

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

/-- A division the facts held already say: the unknowns are the quotient and the remainder. -/
theorem divided_spec (H : Holds ctx s0 ρ s st) {x : Row} {m : Int} (pos : 0 < m) {q : Nat} (hd : divided s x m = some q) :
    ρ q = ev ρ x / m ∧ ρ (q + 1) = ev ρ x % m := by
  have hq := List.find?_some hd
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hq
  obtain ⟨_, ⟨⟨m1, m2⟩, m3⟩, m4⟩ := hq
  have f1 := H.facts _ m1
  have f2 := H.facts _ m2
  have f3 := H.facts _ m3
  have f4 := H.facts _ m4
  rw [holds_iff] at f1 f2 f3 f4
  simp only [ev_sub, ev_add, ev_scale, ev_var, ev_const] at f1 f2 f3 f4
  have u := (Int.ediv_emod_unique (a := ev ρ x) (r := ρ (q + 1)) (q := ρ q) pos).mpr ⟨by omega, f3, by omega⟩
  exact ⟨u.1.symm, u.2.symm⟩

theorem lowOf_sound (H : Holds ctx s0 ρ s st) {x r : Row} {m : Int} (pos : 0 < m) (h : lowOf s x m = some r) : ev ρ r = ev ρ x % m := by
  unfold lowOf at h
  split at h
  next hk =>
    injection h with h; subst h
    rw [ev_const, ev_low_exact hk]
  next =>
    cases hd : divided s x m with
    | none => simp [hd] at h
    | some q =>
      simp only [hd, Option.map_some] at h
      injection h with h; subst h
      rw [ev_var]; exact (divided_spec H pos hd).2

theorem highOf_sound (H : Holds ctx s0 ρ s st) {x q : Row} (h : highOf s x = some q) : ev ρ q = ev ρ x / W32i := by
  unfold highOf at h
  split at h
  next =>
    cases hd : divided s x W32i with
    | none => simp [hd] at h
    | some k =>
      simp only [hd, Option.map_some] at h
      injection h with h; subst h
      rw [ev_var]; exact (divided_spec H (by decide) hd).1
  next =>
    split at h
    next hc =>
      injection h with h; subst h
      cases hk : Lin.isConst (Lin.word x) with
      | none => simp [hk] at hc
      | some cst =>
        have e1 := ev_isConst (ρ := ρ) hk
        have e2 : cst = x.constant % W32i := isConst_constant hk
        have eh := ev_high ρ x
        have c0 := Int.emod_nonneg x.constant (show W32i ≠ 0 by decide)
        have c1 := Int.emod_lt_of_pos x.constant (show (0 : Int) < W32i by decide)
        rw [e1, e2] at eh
        unfold W32i at eh c0 c1 ⊢
        omega
    next => cases h

theorem knownNonneg_sound (H : Holds ctx s0 ρ s st) {r : Row} (h : knownNonneg s r = true) : 0 ≤ ev ρ r := by
  unfold knownNonneg at h
  split at h
  next k hk => rw [ev_isConst hk]; simpa using h
  next =>
    have := H.facts r (List.contains_iff_mem.mp h)
    rw [holds_iff] at this; exact this

/-- Every term of the state's table is a word. -/
theorem Holds.den_lt (wf : WF s) (i : Nat) : den (inpOf ctx s0) ρ s.terms i < W32 :=
  Ode.den_lt wf.words.table (inpOf_lt ctx s0) wf.words.rotrs i

/-- The term a word is, where it is one: the sum of the word's terms, wrapping. -/
theorem idOf_den (wf : WF s) {xs : List Nat} {a : Nat} (h : idOf (fun n => findNode n s.terms 0) xs = some a) :
    den (inpOf ctx s0) ρ s.terms a = sumList (xs.map (den (inpOf ctx s0) ρ s.terms)) % W32 := by
  have key : ∀ ys, findNode (.add ys) s.terms 0 = some a →
      den (inpOf ctx s0) ρ s.terms a = sumList (ys.map (den (inpOf ctx s0) ρ s.terms)) % W32 := by
    intro ys hf
    have hn := (findNode_spec _ _ _ _ hf).2
    rw [den_node wf.words.table (by simpa using hn)]
    rfl
  match xs, h with
  | [], h => exact key [] h
  | [b], h =>
    simp only [idOf] at h
    injection h with h; subst h
    simp only [List.map, sumList, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (Holds.den_lt wf b)).symm
  | b :: c :: more, h => exact key _ h

/-- A term found in the table: it is what its node says. -/
theorem found_den (wf : WF s) {n : Node} {i : Nat} (h : findNode n s.terms 0 = some i) :
    den (inpOf ctx s0) ρ s.terms i = n.value (inpOf ctx s0) ρ (den (inpOf ctx s0) ρ s.terms) := by
  have hn := (findNode_spec _ _ _ _ h).2
  exact den_node wf.words.table (by simpa using hn)

/-- One term as a word. -/
theorem WDen.one (wf : WF s) (i : Nat) :
    WDen ctx s0 ρ s.terms (.word [i]) (.word (den (inpOf ctx s0) ρ s.terms i)) := by
  have h := WDen.word (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) [i]
  simp only [List.map, sumList, Nat.add_zero, Nat.mod_eq_of_lt (Holds.den_lt (ctx := ctx) (s0 := s0) (ρ := ρ) wf i)] at h
  exact h

end

/-! ## Operators -/

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

local notation "𝔻" => den (inpOf ctx s0) ρ s.terms

theorem wbin_sound (H : Holds ctx s0 ρ s st) (wf : WF s) {op : String} {x y v : WVal} {xa ya : Val}
    (h : wbin (fun n => findNode n s.terms 0) s op x y = some v) (hx : WDen ctx s0 ρ s.terms x xa) (hy : WDen ctx s0 ρ s.terms y ya) :
    ∃ a, binop op xa ya = some a ∧ WDen ctx s0 ρ s.terms v a := by
  cases x with
  | int a =>
    cases y with
    | int b =>
      cases hx; cases hy
      simp only [wbin] at h
      cases hb : binop op (.int a) (.int b) with
      | none => simp [hb] at h
      | some r =>
        cases r with
        | int n => simp only [hb, Option.some.injEq] at h; subst h; exact ⟨_, rfl, WDen.int n⟩
        | bool c => simp only [hb, Option.some.injEq] at h; subst h; exact ⟨_, rfl, WDen.bool c⟩
        | _ => simp [hb] at h
    | _ => simp [wbin] at h
  | word xs =>
    cases y with
    | word ys =>
      cases hx; cases hy
      simp only [wbin] at h
      split at h
      next hop =>
        have oe : op = "+" := by simpa using hop
        subst oe
        simp only [Option.some.injEq] at h; subst h
        refine ⟨.word ((sumList (xs.map 𝔻) % W32 + sumList (ys.map 𝔻) % W32) % W32), by simp [binop, wordop], ?_⟩
        have e : (sumList (xs.map 𝔻) % W32 + sumList (ys.map 𝔻) % W32) % W32 =
            sumList (((xs ++ ys).foldr insertSorted []).map 𝔻) % W32 := by
          rw [sumList_sorted, sumList_append]; exact (Nat.add_mod _ _ _).symm
        rw [e]; exact WDen.word _
      next hop =>
        split at h
        next hop2 =>
          have oe : op = "^" := by simpa using hop2
          subst oe
          cases ha : idOf (fun n => findNode n s.terms 0) xs <;> cases hb : idOf (fun n => findNode n s.terms 0) ys <;> simp only [ha, hb, reduceCtorEq] at h
          rename_i a b
          cases hf : findNode (.xor (min a b) (max a b)) s.terms 0 with
          | none => simp [hf] at h
          | some i =>
            simp only [hf, Option.map_some, Option.some.injEq] at h; subst h
            have di := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hf
            have da := idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf ha
            have db := idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hb
            refine ⟨.word (sumList (xs.map 𝔻) % W32 ^^^ sumList (ys.map 𝔻) % W32), by simp [binop, wordop], ?_⟩
            have e : sumList (xs.map 𝔻) % W32 ^^^ sumList (ys.map 𝔻) % W32 = 𝔻 i := by
              rw [di, ← da, ← db]
              simp only [Node.value]
              cases Nat.le_total a b with
              | inl le => rw [Nat.min_eq_left le, Nat.max_eq_right le]
              | inr le => rw [Nat.min_eq_right le, Nat.max_eq_left le, Nat.xor_comm]
            rw [e]; exact WDen.one wf i
        next => simp at h
    | int n =>
      cases hx; cases hy
      simp only [wbin] at h
      split at h
      next hc =>
        obtain ⟨hop, n0, n32⟩ := hc
        have oe : op = ">>>" := by simpa using hop
        subst oe
        cases ha : idOf (fun n => findNode n s.terms 0) xs with
        | none => simp [ha] at h
        | some a =>
          simp only [ha] at h
          cases hf : findNode (.rotr a n.toNat) s.terms 0 with
          | none => simp [hf] at h
          | some i =>
            simp only [hf, Option.map_some, Option.some.injEq] at h; subst h
            have di := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hf
            have da := idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf ha
            refine ⟨.word (rotr (sumList (xs.map 𝔻) % W32) n.toNat), by simp [binop, n0, n32], ?_⟩
            have e : rotr (sumList (xs.map 𝔻) % W32) n.toNat = 𝔻 i := by rw [di, ← da]; rfl
            rw [e]; exact WDen.one wf i
      next => simp at h
    | _ => simp [wbin] at h
  | num r =>
    cases y with
    | int m =>
      cases hx; cases hy
      simp only [wbin] at h
      split at h
      next hc =>
        obtain ⟨hop, mpos⟩ := hc
        have oe : op = "%" := by simpa using hop
        subst oe
        cases hl : lowOf s r m with
        | none => simp [hl] at h
        | some r' =>
          simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
          refine ⟨.int (ev ρ r % m), by simp [binop, mpos], ?_⟩
          rw [← lowOf_sound H mpos hl]; exact WDen.num r'
      next => simp at h
    | _ => simp [wbin] at h
  | list a =>
    cases y with
    | list b =>
      obtain ⟨a', rfl⟩ := WDen.list_inv hx
      obtain ⟨b', rfl⟩ := WDen.list_inv hy
      simp only [wbin] at h
      split at h
      next hop =>
        have oe : op = "++" := by simpa using hop
        subst oe
        simp only [Option.some.injEq] at h; subst h
        exact ⟨.list (a' ++ b'), by simp [binop], WDen.append hx hy⟩
      next => simp at h
    | _ => simp [wbin] at h
  | _ => cases y <;> simp [wbin] at h

end

/-! ## The words of a run of bytes -/

theorem map_range_succ {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl

theorem map_range_add4 {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 4)).map f = f 0 :: f 1 :: f 2 :: f 3 :: (List.range n).map (fun i => f (i + 4)) := by
  rw [show n + 4 = n + 1 + 1 + 1 + 1 from rfl, map_range_succ, map_range_succ, map_range_succ, map_range_succ]

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

/-- The words of the table that are a run's words: they are what the account's `words` makes of the run's
bytes, four bytes a word, the lowest first. -/
theorem toWords_fn (wf : WF s) {j : Nat} : ∀ (count k : Nat) (g : Nat → Nat) (wvs : List WVal),
    inputWords (fun n => findNode n s.terms 0) j count k = some wvs → (∀ i, i < 4 * count → g i < 256) →
    (∀ q a, a = 4 * q → q < count →
      inpOf ctx s0 j (k + q) = g a + 256 * g (a + 1) + 65536 * g (a + 2) + 16777216 * g (a + 3)) →
    ∃ ws, toWords ((List.range (4 * count)).map fun i => Val.int (g i)) = some ws ∧ WDen ctx s0 ρ s.terms (.list wvs) (.list ws)
  | 0, k, g, wvs, h, _, _ => by
    simp only [inputWords, Option.some.injEq] at h; subst h
    exact ⟨[], by simp [toWords], WDen.nil⟩
  | count + 1, k, g, wvs, h, hb, hwd => by
    simp only [inputWords] at h
    cases hf : findNode (.input j k) s.terms 0 <;> cases hr : inputWords (fun n => findNode n s.terms 0) j count (k + 1) <;>
      simp only [hf, hr, reduceCtorEq, Option.some.injEq] at h
    rename_i i rest
    subst h
    obtain ⟨ws, hw, hd⟩ := toWords_fn wf count (k + 1) (fun i => g (i + 4)) rest hr (fun i hi => hb (i + 4) (by omega))
      (fun q a ha hq => by
        have := hwd (q + 1) (a + 4) (by omega) (by omega)
        have e : k + 1 + q = k + (q + 1) := by omega
        rw [e, this, Nat.add_right_comm a 1 4, Nat.add_right_comm a 2 4, Nat.add_right_comm a 3 4])
    have b0 := hb 0 (by omega)
    have b1 := hb 1 (by omega)
    have b2 := hb 2 (by omega)
    have b3 := hb 3 (by omega)
    have h0 := hwd 0 0 rfl (by omega)
    simp only [Nat.zero_add, Nat.add_zero] at h0
    have di : den (inpOf ctx s0) ρ s.terms i = inpOf ctx s0 j k := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hf
    refine ⟨.word (inpOf ctx s0 j k) :: ws, ?_, WDen.cons (by rw [← di]; exact WDen.one wf i) hd⟩
    rw [show 4 * (count + 1) = 4 * count + 4 from rfl, map_range_add4]
    simp only [toWords]
    rw [if_pos ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩, hw]
    simp only [Option.map_some, Option.some.injEq, List.cons.injEq, Val.word.injEq, and_true]
    omega

end

/-! ## The language's own names -/

theorem load4 (mem : Nat → Nat) (a : Nat) :
    load mem a 4 = mem a % 256 + 256 * (mem (a + 1) % 256 + 256 * (mem (a + 1 + 1) % 256 + 256 * (mem (a + 1 + 1 + 1) % 256 + 256 * 0))) := rfl

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

local notation "𝔻" => den (inpOf ctx s0) ρ s.terms

theorem wown_sound (H : Holds ctx s0 ρ s st) (wf : WF s) {f : String} {vs : List WVal} {as : List Val} {v : WVal}
    (h : wown ctx (fun n => findNode n s.terms 0) s f vs = some v) (hv : WDen ctx s0 ρ s.terms (.list vs) (.list as)) :
    ∃ a, builtin f as = some a ∧ WDen ctx s0 ρ s.terms v a := by
  rcases vs with _ | ⟨x, _ | ⟨y, more⟩⟩
  · simp [wown] at h
  · cases hv with
    | cons hx hnil =>
      cases hnil
      cases x with
      | int n =>
        cases hx
        simp only [wown] at h
        split at h
        next hf =>
          have fe : f = "word" := by simpa using hf
          subst fe
          split at h
          next n0 =>
            cases hfn : findNode (.atom (Lin.word (Lin.const n))) s.terms 0 with
            | none => simp [hfn] at h
            | some i =>
              simp only [hfn, Option.map_some, Option.some.injEq] at h; subst h
              have di : 𝔻 i = (ev ρ (Lin.word (Lin.const n)) % W32i).toNat := found_den wf hfn
              refine ⟨.word (n.toNat % W32), by simp [builtin, n0], ?_⟩
              have e : n.toNat % W32 = 𝔻 i := by rw [di, ev_word, ev_const]; unfold W32 W32i; omega
              rw [e]; exact WDen.one wf i
          next => simp at h
        next hf =>
          split at h
          next hf2 =>
            have fe : f = "counter" := by simpa using hf2
            subst fe
            split at h
            next n0 =>
              simp only [Option.some.injEq] at h; subst h
              refine ⟨.counter (n.toNat % 2 ^ 64), by simp [builtin, n0], ?_⟩
              have := WDen.counter (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.const n) (by rw [ev_const]; exact n0)
              rw [ev_const] at this; exact this
            next => simp at h
          next => simp at h
      | num r =>
        cases hx
        simp only [wown] at h
        split at h
        next => simp at h
        next hk =>
          have r0 : 0 ≤ ev ρ r := knownNonneg_sound H (by simpa using hk)
          split at h
          next hf =>
            have fe : f = "word" := by simpa using hf
            subst fe
            cases hfn : findNode (.atom (Lin.word r)) s.terms 0 with
            | none => simp [hfn] at h
            | some i =>
              simp only [hfn, Option.map_some, Option.some.injEq] at h; subst h
              have di : 𝔻 i = (ev ρ (Lin.word r) % W32i).toNat := found_den wf hfn
              refine ⟨.word ((ev ρ r).toNat % W32), by simp [builtin, r0], ?_⟩
              have e : (ev ρ r).toNat % W32 = 𝔻 i := by rw [di, ev_word]; unfold W32 W32i; omega
              rw [e]; exact WDen.one wf i
          next hf =>
            split at h
            next hf2 =>
              have fe : f = "counter" := by simpa using hf2
              subst fe
              simp only [Option.some.injEq] at h; subst h
              exact ⟨.counter ((ev ρ r).toNat % 2 ^ 64), by simp [builtin, r0], WDen.counter r r0⟩
            next => simp at h
      | word xs =>
        cases hx
        simp only [wown] at h
        split at h
        next hf =>
          have fe : f = "word" := by simpa using hf
          subst fe
          simp only [Option.some.injEq] at h; subst h
          exact ⟨_, by simp [builtin], WDen.word xs⟩
        next => simp at h
      | counter r =>
        cases hx with
        | counter _ r0 =>
          simp only [wown] at h
          split at h
          next hf =>
            have fe : f = "counter" := by simpa using hf
            subst fe
            simp only [Option.some.injEq] at h; subst h
            exact ⟨_, by simp [builtin], WDen.counter r r0⟩
          next hf =>
            split at h
            next hf2 =>
              have fe : f = "lo" := by simpa using hf2
              subst fe
              cases hfn : findNode (.atom (Lin.word r)) s.terms 0 with
              | none => simp [hfn] at h
              | some i =>
                simp only [hfn, Option.map_some, Option.some.injEq] at h; subst h
                have di : 𝔻 i = (ev ρ (Lin.word r) % W32i).toNat := found_den wf hfn
                refine ⟨.word ((ev ρ r).toNat % 2 ^ 64 % W32), by simp [builtin], ?_⟩
                have e : (ev ρ r).toNat % 2 ^ 64 % W32 = 𝔻 i := by rw [di, ev_word]; unfold W32 W32i; omega
                rw [e]; exact WDen.one wf i
            next hf2 =>
              split at h
              next hf3 =>
                have fe : f = "hi" := by simpa using hf3
                subst fe
                cases hq : highOf s r with
                | none => simp [hq] at h
                | some q =>
                  simp only [hq, Option.bind_some] at h
                  cases hfn : findNode (.atom (Lin.word q)) s.terms 0 with
                  | none => simp [hfn] at h
                  | some i =>
                    simp only [hfn, Option.map_some, Option.some.injEq] at h; subst h
                    have di : 𝔻 i = (ev ρ (Lin.word q) % W32i).toNat := found_den wf hfn
                    have eq := highOf_sound H hq
                    refine ⟨.word ((ev ρ r).toNat % 2 ^ 64 / W32), by simp [builtin], ?_⟩
                    have e : (ev ρ r).toNat % 2 ^ 64 / W32 = 𝔻 i := by rw [di, ev_word, eq]; unfold W32 W32i; omega
                    rw [e]; exact WDen.one wf i
              next => simp at h
      | run r n =>
        cases hx with
        | run _ _ hb =>
          simp only [wown] at h
          split at h
          next hc =>
            obtain ⟨hf, n4⟩ := hc
            have fe : f = "words" := by simpa using hf
            subst fe
            cases hra : runAt r (ctx.contract.fixeds ++ ctx.contract.inouts) 0 with
            | none => simp [hra] at h
            | some j =>
              simp only [hra, Option.bind_some] at h
              cases hin : inputWords (fun n => findNode n s.terms 0) j (n / 4) 0 with
              | none => simp [hin] at h
              | some wvs =>
                simp only [hin, Option.map_some, Option.some.injEq] at h; subst h
                obtain ⟨_, x', n', hj⟩ := runAt_spec hra
                have hj' : (ctx.contract.fixeds ++ ctx.contract.inouts)[j]? = some (x', r, n') := by simpa using hj
                obtain ⟨ws, hw, hd⟩ := toWords_fn (ctx := ctx) (s0 := s0) (ρ := ρ) wf (n / 4) 0 (fun i => s0.mem (s0.reg r + i)) wvs hin
                  (fun i hi => hb i (by omega))
                  (fun q a ha hq => by
                    subst ha
                    have b0 := hb (4 * q) (by omega)
                    have b1 := hb (4 * q + 1) (by omega)
                    have b2 := hb (4 * q + 2) (by omega)
                    have b3 := hb (4 * q + 3) (by omega)
                    have e0 : inpOf ctx s0 j (0 + q) = load s0.mem (s0.reg r + 4 * q) 4 := by simp only [inpOf, hj', Nat.zero_add]
                    have e1 : s0.reg r + 4 * q + 1 = s0.reg r + (4 * q + 1) := by omega
                    have e2 : s0.reg r + 4 * q + 1 + 1 = s0.reg r + (4 * q + 2) := by omega
                    have e3 : s0.reg r + 4 * q + 1 + 1 + 1 = s0.reg r + (4 * q + 3) := by omega
                    rw [e0, load4, e3, e2, e1]
                    omega)
                have en : 4 * (n / 4) = n := by omega
                rw [en] at hw
                exact ⟨.list ws, by simp [builtin, hw], hd⟩
          next => simp at h
      | _ => simp [wown] at h
  · cases x <;> simp [wown] at h

/-! ## Lists of expressions -/

theorem wevalList_sound {ev : SExpr → Option WVal} {ev' : SExpr → Option Val}
    (hev : ∀ e v, ev e = some v → ∃ a, ev' e = some a ∧ WDen ctx s0 ρ s.terms v a) :
    ∀ (args : SExpr) (vs : List WVal), wevalList ev args = some vs →
      ∃ as, evalList ev' args = some as ∧ WDen ctx s0 ρ s.terms (.list vs) (.list as) := by
  intro args
  induction args with
  | nil => intro vs h; simp only [wevalList, Option.some.injEq] at h; subst h; exact ⟨[], rfl, WDen.nil⟩
  | cons a rest _ ih =>
    intro vs h
    simp only [wevalList] at h
    cases ha : ev a <;> cases hr : wevalList ev rest <;> simp only [ha, hr, reduceCtorEq, Option.some.injEq] at h
    rename_i v vs'
    subst h
    obtain ⟨a', ea, da⟩ := hev a v ha
    obtain ⟨as, eas, das⟩ := ih vs' hr
    exact ⟨a' :: as, by simp only [evalList, ea, eas], WDen.cons da das⟩
  | _ => intro vs h; simp [wevalList] at h

theorem wevalEach_sound {ev : Int → Option WVal} {ev' : Int → Option Val}
    (hev : ∀ i v, ev i = some v → ∃ a, ev' i = some a ∧ WDen ctx s0 ρ s.terms v a) :
    ∀ (count : Nat) (i : Int) (vs : List WVal), wevalEach ev count i = some vs →
      ∃ as, evalEach ev' count i = some as ∧ WDen ctx s0 ρ s.terms (.list vs) (.list as)
  | 0, i, vs, h => by simp only [wevalEach, Option.some.injEq] at h; subst h; exact ⟨[], rfl, WDen.nil⟩
  | count + 1, i, vs, h => by
    simp only [wevalEach] at h
    cases ha : ev i <;> cases hr : wevalEach ev count (i + 1) <;> simp only [ha, hr, reduceCtorEq, Option.some.injEq] at h
    rename_i v vs'
    subst h
    obtain ⟨a', ea, da⟩ := hev i v ha
    obtain ⟨as, eas, das⟩ := wevalEach_sound hev count (i + 1) vs' hr
    exact ⟨a' :: as, by simp only [evalEach, ea, eas], WDen.cons da das⟩

theorem wputAll_sound : ∀ (ps : List WVal) (ps' : List Val) (l : List WVal) (l' : List Val) (l2 : List WVal),
    WDen ctx s0 ρ s.terms (.list l) (.list l') → WDen ctx s0 ρ s.terms (.list ps) (.list ps') → wputAll l ps = some l2 →
    ∃ l2', putAll l' ps' = some l2' ∧ WDen ctx s0 ρ s.terms (.list l2) (.list l2')
  | [], ps', l, l', l2, hl, hp, h => by
    cases hp
    simp only [wputAll, Option.some.injEq] at h; subst h
    exact ⟨l', by simp [putAll], hl⟩
  | [p], ps', l, l', l2, hl, hp, h => by cases p <;> simp [wputAll] at h
  | p :: x :: rest, ps', l, l', l2, hl, hp, h => by
    cases hp with
    | cons hp1 hp2 =>
      cases hp2 with
      | cons hx hrest =>
        cases p with
        | int i =>
          cases hp1
          simp only [wputAll] at h
          split at h
          next hc =>
            obtain ⟨l2', e, d⟩ := wputAll_sound rest _ (l.set i.toNat x) _ l2 (WDen.set hl hx) hrest h
            refine ⟨l2', ?_, d⟩
            simp only [putAll]
            rw [if_pos ⟨hc.1, by rw [← WDen.length hl]; exact hc.2⟩]
            exact e
          next => simp at h
        | _ => simp [wputAll] at h

end

/-! ## An expression -/

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

/-- What `weval` gives of an expression stands for what `evalSpec` gives of it with the same fuel, the names
on words standing for the names of the account. -/
theorem weval_sound (H : Holds ctx s0 ρ s st) (wf : WF s) :
    ∀ (fuel : Nat) (env : List (String × WVal)) (env' : List (String × Val)) (e : SExpr) (v : WVal),
      weval ctx (fun n => findNode n s.terms 0) s fuel env e = some v → EnvDen ctx s0 ρ s.terms env env' →
      ∃ a, evalSpec ctx.defs fuel env' e = some a ∧ WDen ctx s0 ρ s.terms v a
  | 0, _, _, _, _, h, _ => by simp [weval] at h
  | fuel + 1, env, env', e, v, h, hE => by
    have ih := weval_sound H wf fuel
    cases e with
    | num n =>
      simp only [weval] at h
      split at h
      next n0 =>
        simp only [Option.some.injEq] at h; subst h
        refine ⟨.int n, ?_, WDen.int n⟩
        simp only [evalSpec]; rw [if_pos n0]
      next => simp at h
    | name x =>
      simp only [weval] at h
      obtain ⟨a, ha, hd⟩ := EnvDen.lookup hE h
      refine ⟨a, ?_, hd⟩
      simp only [evalSpec]; exact ha
    | bin op a b =>
      simp only [weval] at h
      cases ha : weval ctx (fun n => findNode n s.terms 0) s fuel env a <;> cases hb : weval ctx (fun n => findNode n s.terms 0) s fuel env b <;>
        simp only [ha, hb, reduceCtorEq] at h
      rename_i x y
      obtain ⟨xa, ea, da⟩ := ih env env' a x ha hE
      obtain ⟨ya, eb, db⟩ := ih env env' b y hb hE
      obtain ⟨r, er, dr⟩ := wbin_sound H wf h da db
      refine ⟨r, ?_, dr⟩
      simp only [evalSpec, ea, eb]; exact er
    | ifx c a b =>
      simp only [weval] at h
      cases hc : weval ctx (fun n => findNode n s.terms 0) s fuel env c with
      | none => simp [hc] at h
      | some cv =>
        obtain ⟨ca, ec, dc⟩ := ih env env' c cv hc hE
        cases cv with
        | bool t =>
          cases dc
          cases t with
          | true =>
            simp only [hc] at h
            obtain ⟨r, er, dr⟩ := ih env env' a v h hE
            refine ⟨r, ?_, dr⟩
            simp only [evalSpec, ec]; exact er
          | false =>
            simp only [hc] at h
            obtain ⟨r, er, dr⟩ := ih env env' b v h hE
            refine ⟨r, ?_, dr⟩
            simp only [evalSpec, ec]; exact er
        | _ => simp [hc] at h
    | index a i =>
      simp only [weval] at h
      cases ha : weval ctx (fun n => findNode n s.terms 0) s fuel env a <;> cases hi : weval ctx (fun n => findNode n s.terms 0) s fuel env i <;>
        simp only [ha, hi, reduceCtorEq] at h
      rename_i av iv
      obtain ⟨aa, ea, da⟩ := ih env env' a av ha hE
      obtain ⟨ia, ei, di⟩ := ih env env' i iv hi hE
      cases av with
      | list l =>
        cases iv with
        | int k =>
          cases di
          obtain ⟨l', rfl⟩ := WDen.list_inv da
          simp only at h
          split at h
          next k0 =>
            obtain ⟨r, er, dr⟩ := WDen.getElem? da h
            refine ⟨r, ?_, dr⟩
            simp only [evalSpec, ea, ei]; rw [if_pos k0]; exact er
          next => simp at h
        | _ => simp at h
      | _ => cases iv <;> simp at h
    | call f args =>
      simp only [weval] at h
      cases hl : wevalList (weval ctx (fun n => findNode n s.terms 0) s fuel env) args with
      | none => simp [hl] at h
      | some vs =>
        simp only [hl] at h
        obtain ⟨as, el, dl⟩ := wevalList_sound (ev' := evalSpec ctx.defs fuel env') (fun e v hv => ih env env' e v hv hE) args vs hl
        split at h
        next => simp at h
        next hlen =>
          split at h
          next hown =>
            obtain ⟨r, er, dr⟩ := wown_sound H wf h dl
            refine ⟨r, ?_, dr⟩
            simp only [evalSpec, el]; rw [if_neg hlen, if_pos hown]; exact er
          next hown =>
            cases hd : findDef ctx.defs f with
            | none => simp [hd] at h
            | some d =>
              simp only [hd] at h
              split at h
              next hp =>
                obtain ⟨r, er, dr⟩ := ih (d.params.zip vs) (d.params.zip as) d.body v h (EnvDen.zip dl)
                have hp' : (d.params.length == as.length) = true := by rw [← WDen.length dl]; exact hp
                refine ⟨r, ?_, dr⟩
                simp only [evalSpec, el]; rw [if_neg hlen, if_neg hown]; simp only [hd]; rw [if_pos hp']; exact er
              next => simp at h
    | list items =>
      simp only [weval] at h
      cases hl : wevalList (weval ctx (fun n => findNode n s.terms 0) s fuel env) items with
      | none => simp [hl] at h
      | some vs =>
        simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
        obtain ⟨as, el, dl⟩ := wevalList_sound (ev' := evalSpec ctx.defs fuel env') (fun e v hv => ih env env' e v hv hE) items vs hl
        refine ⟨.list as, ?_, dl⟩
        simp only [evalSpec, el, Option.map_some]
    | letx x e rest =>
      simp only [weval] at h
      cases he : weval ctx (fun n => findNode n s.terms 0) s fuel env e with
      | none => simp [he] at h
      | some xv =>
        simp only [he] at h
        obtain ⟨xa, ex, dx⟩ := ih env env' e xv he hE
        obtain ⟨r, er, dr⟩ := ih ((x, xv) :: env) ((x, xa) :: env') rest v h ⟨rfl, dx, hE⟩
        refine ⟨r, ?_, dr⟩
        simp only [evalSpec, ex]; exact er
    | each e x a b =>
      simp only [weval] at h
      cases ha : weval ctx (fun n => findNode n s.terms 0) s fuel env a <;> cases hb : weval ctx (fun n => findNode n s.terms 0) s fuel env b <;>
        simp only [ha, hb, reduceCtorEq] at h
      rename_i av bv
      obtain ⟨aa, ea, da⟩ := ih env env' a av ha hE
      obtain ⟨ba, eb, db⟩ := ih env env' b bv hb hE
      cases av with
      | int lo =>
        cases bv with
        | int hi =>
          cases da; cases db
          simp only at h
          cases hl : wevalEach (fun i => weval ctx (fun n => findNode n s.terms 0) s fuel ((x, .int i) :: env) e) (hi - lo).toNat lo with
          | none => simp [hl] at h
          | some vs =>
            simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
            obtain ⟨as, el, dl⟩ := wevalEach_sound (ev' := fun i => evalSpec ctx.defs fuel ((x, .int i) :: env') e)
              (fun i v hv => ih ((x, .int i) :: env) ((x, .int i) :: env') e v hv ⟨rfl, WDen.int i, hE⟩) (hi - lo).toNat lo vs hl
            refine ⟨.list as, ?_, dl⟩
            simp only [evalSpec, ea, eb, el, Option.map_some]
        | _ => simp at h
      | _ => cases bv <;> simp at h
    | withx a puts =>
      simp only [weval] at h
      cases ha : weval ctx (fun n => findNode n s.terms 0) s fuel env a <;> cases hp : wevalList (weval ctx (fun n => findNode n s.terms 0) s fuel env) puts <;>
        simp only [ha, hp, reduceCtorEq] at h
      rename_i av ps
      obtain ⟨aa, ea, da⟩ := ih env env' a av ha hE
      obtain ⟨ps', ep, dp⟩ := wevalList_sound (ev' := evalSpec ctx.defs fuel env') (fun e v hv => ih env env' e v hv hE) puts ps hp
      cases av with
      | list l =>
        obtain ⟨l', rfl⟩ := WDen.list_inv da
        simp only at h
        cases hw : wputAll l ps with
        | none => simp [hw] at h
        | some l2 =>
          simp only [hw, Option.map_some, Option.some.injEq] at h; subst h
          obtain ⟨l2', e2, d2⟩ := wputAll_sound ps ps' l l' l2 da dp hw
          refine ⟨.list l2', ?_, d2⟩
          simp only [evalSpec, ea, ep, e2, Option.map_some]
      | _ => simp at h
    | _ => simp [weval] at h

end

/-! ## The names of the contract, and the `ensures` -/

theorem fixedsIn_tail {y : String × Nat × Nat} (a : String × Kind) (r : Nat) {args : List (String × Kind)} {regs : List Nat}
    (m : y ∈ fixedsIn args regs) : y ∈ fixedsIn (a :: args) (r :: regs) := by
  obtain ⟨n, k⟩ := a
  cases k <;> simp [fixedsIn, m]

theorem inoutsIn_tail {y : String × Nat × Nat} (a : String × Kind) (r : Nat) {args : List (String × Kind)} {regs : List Nat}
    (m : y ∈ inoutsIn args regs) : y ∈ inoutsIn (a :: args) (r :: regs) := by
  obtain ⟨n, k⟩ := a
  cases k <;> simp [inoutsIn, m]

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

local notation "𝔻" => den (inpOf ctx s0) ρ s.terms

/-- The names on words stand for the contract's names as the account has them at entry. -/
theorem wenvIn_sound (H : Holds ctx s0 ρ s st) {T : List Node} (c : Contract) :
    ∀ (args : List (String × Kind)) (regs : List Nat), (∀ r ∈ regs, r < 16) →
      (∀ x r n, (x, r, n) ∈ fixedsIn args regs → ∀ k, k < n → s0.mem (s0.reg r + k) < 256) →
      (∀ x r n, (x, r, n) ∈ inoutsIn args regs → ∀ k, k < n → s0.mem (s0.reg r + k) < 256) →
      EnvDen ctx s0 ρ T (wenvIn c args regs) (envWIn c s0 args regs)
  | [], _, _, _, _ => by simp [wenvIn, envWIn, EnvDen]
  | _ :: _, [], _, _, _ => by simp [wenvIn, envWIn, EnvDen]
  | (n, kind) :: args, r :: regs, hreg, hf, hi => by
    have ih := wenvIn_sound H (T := T) c args regs (fun r' m => hreg r' (List.mem_cons_of_mem _ m))
      (fun x r' n' m => hf x r' n' (fixedsIn_tail (n, kind) r m)) (fun x r' n' m => hi x r' n' (inoutsIn_tail (n, kind) r m))
    cases kind with
    | number =>
      simp only [wenvIn, envWIn]
      refine ⟨rfl, ?_, ih⟩
      have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := T) (Lin.var r)
      rw [ev_var, H.entry r (hreg r (List.mem_cons_self ..))] at this
      exact this
    | bytes len =>
      simp only [wenvIn, envWIn]
      cases c.regOf len with
      | none => exact ih
      | some l => exact ⟨rfl, WDen.other _, ih⟩
    | out k =>
      simp only [wenvIn, envWIn]
      exact ih
    | fixed count =>
      simp only [wenvIn, envWIn]
      refine ⟨rfl, ?_, ih⟩
      simp only [Val.bytes, List.map_map]
      exact WDen.run r count (hf n r count (by simp [fixedsIn]))
    | inout count =>
      simp only [wenvIn, envWIn]
      refine ⟨rfl, ?_, ih⟩
      simp only [Val.bytes, List.map_map]
      exact WDen.run r count (hi n r count (by simp [inoutsIn]))

theorem wenv_sound {p : Program} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) {T : List Node} :
    EnvDen ctx s0 ρ T (wenvIn ctx.contract ctx.contract.args argRegs) (ctx.contract.envW s0) :=
  wenvIn_sound H ctx.contract ctx.contract.args argRegs (fun _ m => argRegs_lt m)
    (fun _ _ _ m k hk => (E.fixed m).2.2.1 k hk) (fun _ _ _ m _ hk => E.inoutByte m hk)

/-- The words the specification gives are the words known written: the bytes of the run are the bytes of
those words, four a word, the lowest first. -/
theorem written_words (H : Holds ctx s0 ρ s st) (wf : WF s) {w : Nat} {x : String} {r n : Nat}
    (hw : ctx.contract.outs[w]? = some (x, r, n)) :
    ∀ (l : List WVal) (ws : List Val) (j : Nat), wordsWritten (fun n => findNode n s.terms 0) s.wroteW w j l = true →
      WDen ctx s0 ρ s.terms (.list l) (.list ws) →
      ∃ bs : List Nat, ofWords ws = some (bs.map fun (b : Nat) => Val.int b) ∧ bs.length = 4 * l.length ∧
        ∀ k, k < bs.length → bs[k]? = some (st.mem (s0.reg r + 4 * j + k))
  | [], ws, j, _, hd => by
    cases hd
    exact ⟨[], by simp [ofWords], rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | v :: rest, ws, j, hww, hd => by
    cases hd with
    | cons hv hrest =>
      cases v with
      | word xs =>
        cases hv
        simp only [wordsWritten, Bool.and_eq_true] at hww
        obtain ⟨h1, h2⟩ := hww
        cases hi : idOf (fun n => findNode n s.terms 0) xs with
        | none => simp [hi] at h1
        | some i =>
          simp only [hi] at h1
          have m : (w, j, i) ∈ s.wroteW := List.contains_iff_mem.mp h1
          obtain ⟨g1, g2⟩ := H.words.2.2 w j i m x r n hw
          obtain ⟨bs, eo, len, hm⟩ := written_words H wf hw rest _ (j + 1) h2 hrest
          have dw := idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hi
          refine ⟨[𝔻 i % 256, 𝔻 i / 256 % 256, 𝔻 i / 65536 % 256, 𝔻 i / 16777216 % 256] ++ bs, ?_, ?_, ?_⟩
          · have lt := Holds.den_lt (ctx := ctx) (s0 := s0) (ρ := ρ) wf i
            rw [← dw]; simp [ofWords, eo, lt]
          · simp only [List.length_append, List.length_cons, List.length_nil, len]; omega
          · intro k hk
            match k, hk with
            | 0, _ => rw [g2 0 (by omega)]; simp
            | 1, _ => rw [g2 1 (by omega)]; simp
            | 2, _ => rw [g2 2 (by omega)]; simp
            | 3, _ => rw [g2 3 (by omega)]; simp
            | k + 4, hk =>
              have := hm k (by simp at hk; omega)
              simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
              rw [this]; congr 2; omega
      | _ => simp [wordsWritten] at hww

/-- An `ensures` of a whole run of words that the verifier has passed holds: the run's bytes at the return
are the bytes of the words the specification gives of the names at entry. -/
theorem symEnsureW_sound {p : Program} (E : Setting ctx p s0) {e : EnsureW} {items : Items}
    {r : Unit × Items} {st' : State}
    (h : symEnsureW ctx s e items = .ok r) (H : Holds ctx s0 ρ s st) (wf : WF s) (hmem : st'.mem = st.mem) :
    e.holds ctx.contract ctx.defs s0 st' := by
  unfold symEnsureW at h
  cases hv : e.value with
  | call f args =>
    simp only [hv] at h
    cases args with
    | cons x tl =>
      cases tl with
      | nil =>
        dsimp only at h
        split at h
        next hf =>
          have fe : f = "bytes_of" := by simpa using hf
          subst fe
          cases hfo : findOutNamed e.run ctx.contract.outs 0 with
          | none => simp only [hfo] at h; exact (refuse_ok h).elim
          | some wn =>
            obtain ⟨w, n⟩ := wn
            simp only [hfo] at h
            have hl : (fun n => (termIndex s.terms)[n]?) = fun n => findNode n s.terms 0 :=
              funext fun n => termIndex_spec s.terms n
            rw [hl] at h
            obtain ⟨rr, _, hw⟩ := findOutNamed_spec hfo
            have hw' : ctx.contract.outs[w]? = some (e.run, rr, n) := by simpa using hw
            cases hwv : weval ctx (fun n => findNode n s.terms 0) s WFUEL (wenvIn ctx.contract ctx.contract.args argRegs) x with
            | none => simp only [hwv] at h; exact (refuse_ok h).elim
            | some v =>
              cases v with
              | list l =>
                simp only [hwv] at h
                split at h
                next hc =>
                  obtain ⟨hlen, hww⟩ := hc
                  obtain ⟨a, ea, da⟩ := weval_sound H wf WFUEL _ _ x _ hwv (wenv_sound E H)
                  obtain ⟨ws, rfl⟩ := WDen.list_inv da
                  obtain ⟨bs, eo, blen, hm⟩ := written_words H wf hw' l ws 0 hww da
                  refine ⟨rr, n, bs, List.mem_of_getElem? hw', ⟨WFUEL + 1, ?_⟩, by omega, ?_⟩
                  · rw [hv]
                    simp only [evalSpec, evalList, ea]
                    simp [own, builtin, eo, Val.bytes]
                  · intro k hk
                    have hk' := hm k hk
                    simp only [Nat.mul_zero, Nat.add_zero] at hk'
                    obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.mp hk'
                    rw [hmem]; exact e.symm
                next => exact (refuse_ok h).elim
              | _ => simp only [hwv] at h; exact (refuse_ok h).elim
        next => exact (refuse_ok h).elim
      | _ => exact (refuse_ok h).elim
    | _ => exact (refuse_ok h).elim
  | _ => simp only [hv] at h; exact (refuse_ok h).elim

end

end Ode
