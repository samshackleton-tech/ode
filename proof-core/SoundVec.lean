import SoundStep

/-!
# Why the verifier's yes is right, 2b: rows over vector registers

The words of a vector register are terms of a table (Core.lean, "Words"). Here: each term the verifier makes
is the word the machine computes; a load of sixteen bytes gives the words the run held at entry; a store
puts the register's words into the run.
-/

namespace Ode

open Arithmetic

/-- A table the verifier may hold, the unknowns in use being `nv`: every term is made of terms before it,
its rows speak of unknowns in use, and a word is turned by 32 bits at most. -/
structure TableOk (nv : Nat) (T : List Node) : Prop where
  wf : WFT T
  atoms : ∀ (j : Nat) (r : Row), T[j]? = some (Node.atom r) → bounded nv r
  rotrs : ∀ (j a n : Nat), T[j]? = some (Node.rotr a n) → n ≤ 32

theorem WordsWF.ok {s : Sym} (W : WordsWF s) : TableOk s.nvars s.terms := ⟨W.table, W.atoms, W.rotrs⟩

theorem TableOk.mono {nv nv' : Nat} {T : List Node} (ok : TableOk nv T) (le : nv ≤ nv') : TableOk nv' T :=
  ⟨ok.wf, fun j r h => bounded_mono le (ok.atoms j r h), ok.rotrs⟩

/-- A term made: the table has grown by it at most and is still one the verifier may hold, and the term is `v`. -/
structure Step (inp : Nat → Nat → Nat) (ρ : Nat → Int) (nv : Nat) (T T' : List Node) (i v : Nat) : Prop where
  ext : Ext T T'
  ok : TableOk nv T'
  lt : i < T'.length
  den : den inp ρ T' i = v

theorem intern_keeps {P : Node → Prop} {n : Node} {T : List Node} (hT : ∀ (j : Nat) (m : Node), T[j]? = some m → P m) (hn : P n) :
    ∀ (j : Nat) (m : Node), (intern n T).2[j]? = some m → P m := by
  intro j m h
  unfold intern at h
  split at h
  · exact hT j m h
  · simp only at h
    by_cases hj : j < T.length
    · rw [List.getElem?_append_left hj] at h; exact hT j m h
    · rw [List.getElem?_append_right (by omega)] at h
      cases hk : j - T.length with
      | zero => rw [hk] at h; simp at h; rw [← h]; exact hn
      | succ k => rw [hk] at h; simp at h

theorem step_of_made {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {n : Node} {T : List Node} {v : Nat} (ok : TableOk nv T)
    (m : Made inp ρ T (intern n T).2 (intern n T).1 v) (ha : ∀ r, n = .atom r → bounded nv r) (hr : ∀ a k, n = .rotr a k → k ≤ 32) :
    Step inp ρ nv T (intern n T).2 (intern n T).1 v :=
  ⟨m.ext,
   ⟨m.wf,
    fun j r h => intern_keeps (P := fun m => ∀ r, m = .atom r → bounded nv r) (fun j m hj r e => ok.atoms j r (e ▸ hj)) ha j _ h r rfl,
    fun j a k h => intern_keeps (P := fun m => ∀ a k, m = .rotr a k → k ≤ 32) (fun j m hj a k e => ok.rotrs j a k (e ▸ hj)) hr j _ h a k rfl⟩,
   m.lt, m.den⟩

theorem bounded_word {nv : Nat} {r : Row} (hb : bounded nv r) : bounded nv (Lin.word r) :=
  Nat.le_trans (strip_length _) (by rw [List.length_map]; exact hb)

theorem bounded_high {nv : Nat} {r : Row} (hb : bounded nv r) : bounded nv (Lin.high r) :=
  Nat.le_trans (strip_length _) (by rw [List.length_map]; exact hb)

theorem wAtom_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {T : List Node} {r : Row} (ok : TableOk nv T) (hb : bounded nv r) :
    Step inp ρ nv T (wAtom r T).2 (wAtom r T).1 (ev ρ r % W32i).toNat :=
  step_of_made ok (wAtom_made (T' := (wAtom r T).2) (i := (wAtom r T).1) rfl ok.wf)
    (fun r' e => by injection e with e; rw [← e]; exact bounded_word hb) (fun a k e => by cases e)

theorem wAdd_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {T : List Node} {a b : Nat} (ok : TableOk nv T)
    (ha : a < T.length) (hb : b < T.length) :
    Step inp ρ nv T (wAdd a b T).2 (wAdd a b T).1 ((den inp ρ T a + den inp ρ T b) % W32) :=
  step_of_made ok (wAdd_made (T' := (wAdd a b T).2) (i := (wAdd a b T).1) rfl ok.wf ha hb) (fun r e => by cases e) (fun a k e => by cases e)

theorem wXor_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {T : List Node} {a b : Nat} (ok : TableOk nv T)
    (ha : a < T.length) (hb : b < T.length) :
    Step inp ρ nv T (wXor a b T).2 (wXor a b T).1 (den inp ρ T a ^^^ den inp ρ T b) :=
  step_of_made ok (wXor_made (T' := (wXor a b T).2) (i := (wXor a b T).1) rfl ok.wf ha hb) (fun r e => by cases e) (fun a k e => by cases e)

theorem wRotr_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {T : List Node} {a n : Nat} (ok : TableOk nv T)
    (ha : a < T.length) (hn : n ≤ 32) :
    Step inp ρ nv T (wRotr a n T).2 (wRotr a n T).1 (rotr (den inp ρ T a) n) :=
  step_of_made ok (wRotr_made (T' := (wRotr a n T).2) (i := (wRotr a n T).1) rfl ok.wf ha) (fun r e => by cases e)
    (fun a k e => by injection e with _ e; rw [← e]; exact hn)

theorem input_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {T : List Node} {j k : Nat} (ok : TableOk nv T) :
    Step inp ρ nv T (intern (.input j k) T).2 (intern (.input j k) T).1 (inp j k) :=
  step_of_made ok (made (T' := (intern (.input j k) T).2) (i := (intern (.input j k) T).1) rfl ok.wf (by intro x mx; simp [Node.parts] at mx))
    (fun r e => by cases e) (fun a k e => by cases e)

/-- The terms made for a list, one after another: each is what it is to be (`val`), in the table at the end. -/
theorem termsOf_step {α : Type} {mk : α → List Node → Nat × List Node} {val : α → Nat} {inp : Nat → Nat → Nat} {ρ : Nat → Int}
    {nv : Nat} {T0 : List Node} :
    ∀ (xs : List α) (T : List Node), (∀ a ∈ xs, ∀ T, Ext T0 T → TableOk nv T → Step inp ρ nv T (mk a T).2 (mk a T).1 (val a)) →
      Ext T0 T → TableOk nv T →
      Ext T (termsOf mk xs T).2 ∧ TableOk nv (termsOf mk xs T).2 ∧ (termsOf mk xs T).1.length = xs.length ∧
      (∀ i ∈ (termsOf mk xs T).1, i < (termsOf mk xs T).2.length) ∧
      ∀ k (hk : k < xs.length), den inp ρ (termsOf mk xs T).2 ((termsOf mk xs T).1.getD k 0) = val xs[k]
  | [], T, _, _, ok => ⟨Ext.refl T, ok, rfl, (fun i m => nomatch m), (fun k hk => absurd hk (Nat.not_lt_zero k))⟩
  | a :: as, T, hmk, e, ok => by
    have S := hmk a (List.mem_cons_self ..) T e ok
    obtain ⟨e2, ok2, len, lt, dn⟩ := termsOf_step as (mk a T).2 (fun b mb => hmk b (List.mem_cons_of_mem _ mb)) (e.trans S.ext) S.ok
    refine ⟨S.ext.trans e2, ok2, by simp [termsOf, len], ?_, ?_⟩
    · intro i mi
      simp only [termsOf, List.mem_cons] at mi
      rcases mi with rfl | mi
      · exact Nat.lt_of_lt_of_le S.lt e2.le
      · exact lt i mi
    · intro k hk
      cases k with
      | zero =>
        show den inp ρ (termsOf mk as (mk a T).2).2 (mk a T).1 = val a
        rw [den_ext S.ok.wf e2 S.lt]; exact S.den
      | succ k => exact dn k (by simpa using hk)

/-! ## The state, with more terms -/

theorem Holds.terms {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF s)
    {T' : List Node} (e : Ext s.terms T') : Holds ctx s0 ρ { s with terms := T' } st :=
  ⟨H.entry, H.reg, H.small, H.zf, H.cf, H.frame, H.facts, H.bytes, H.spec, H.mem, H.wrote,
   ⟨fun x ids hx k hk => by
      obtain ⟨len, lt⟩ := wf.words.vec x ids hx
      have hk' : k < ids.length := by omega
      have eq : ids.getD k 0 = ids[k] := by simp [List.getD, List.getElem?_eq_getElem hk']
      show st.vec x k = den (inpOf ctx s0) ρ T' (ids.getD k 0)
      rw [den_ext wf.words.table e (by rw [eq]; exact lt _ (List.getElem_mem hk'))]
      exact H.words.1 x ids hx k hk,
    H.words.2.1,
    fun w j i m x r n ho => by
      obtain ⟨h1, h2⟩ := H.words.2.2 w j i m x r n ho
      refine ⟨h1, fun b hb => ?_⟩
      show st.mem _ = den (inpOf ctx s0) ρ T' i / 256 ^ b % 256
      rw [den_ext wf.words.table e (wf.words.wrote w j i m)]
      exact h2 b hb⟩,
   fun k m => Known.holds_mono (wf.known k m) (Agree.refl _ _) wf.words.table wf.words.atoms e (H.known k m)⟩

theorem WF.terms {s : Sym} (wf : WF s) {T' : List Node} (e : Ext s.terms T') (ok : TableOk s.nvars T') : WF { s with terms := T' } :=
  ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.facts, wf.bytes, wf.spec, wf.wrote,
   ⟨ok.wf, ok.atoms, fun x ids h => ⟨(wf.words.vec x ids h).1, fun i mi => Nat.lt_of_lt_of_le ((wf.words.vec x ids h).2 i mi) e.le⟩,
    ok.rotrs, fun w j i h => Nat.lt_of_lt_of_le (wf.words.wrote w j i h) e.le⟩,
   fun k m => Known.wf_mono (Nat.le_refl _) e.le (wf.known k m)⟩

theorem Carried.terms {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF s)
    {T' : List Node} (e : Ext s.terms T') (ok : TableOk s.nvars T') : Carried ctx s0 ρ s ρ { s with terms := T' } st :=
  ⟨Agree.refl _ _, Nat.le_refl _, H.terms wf e, wf.terms e ok⟩

/-! ## What an EFFECT names -/

theorem lt4 {k : Nat} (h : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

theorem list4 {α : Type} : ∀ {l : List α}, l.length = 4 → ∃ a b c d, l = [a, b, c, d]
  | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩
  | [], h => by simp at h
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | [_, _, _], h => by simp at h
  | _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

/-- A vector register the verifier knows the words of: the machine's four low lanes of it are those terms. -/
theorem symVec_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} {bind : Bind} {e : Expr} {l : List Nat}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (h : symVec bind s e = some l) :
    ∃ r, l.length = 4 ∧ (∀ i ∈ l, i < s.terms.length) ∧ vecArg bind st e = some [st.vec r 0, st.vec r 1, st.vec r 2, st.vec r 3] ∧
      ∀ k, k < 4 → st.vec r k = den (inpOf ctx s0) ρ s.terms (l.getD k 0) := by
  cases e with
  | name n =>
    simp only [symVec] at h
    cases hv : vecOf bind n with
    | none => simp [hv] at h
    | some r =>
      simp only [hv, Option.bind_some] at h
      obtain ⟨len, lt⟩ := wf.words.vec r l h
      exact ⟨r, len, lt, by simp only [vecArg, hv]; rfl, H.words.1 r l h⟩
  | number _ => simp [symVec] at h
  | lane _ _ => simp [symVec] at h
  | call _ _ => simp [symVec] at h

theorem symLane_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} {bind : Bind} {e : Expr} {i : Nat}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (h : symLane bind s e = some i) :
    i < s.terms.length ∧ ∃ v, laneArg bind st e = some v ∧ v = den (inpOf ctx s0) ρ s.terms i := by
  cases e with
  | lane n k =>
    simp only [symLane] at h
    split at h
    next hk =>
      cases hv : vecOf bind n with
      | none => simp [hv] at h
      | some r =>
        simp only [hv, Option.bind_some] at h
        cases hl : s.vec.lookup r with
        | none => simp [hl] at h
        | some l =>
          simp only [hl, Option.bind_some] at h
          have e : l.getD k 0 = i := by simp [List.getD, h]
          refine ⟨(wf.words.vec r l hl).2 i (List.mem_of_getElem? h), st.vec r k, by simp [laneArg, hv], ?_⟩
          rw [← e]; exact H.words.1 r l hl k hk
    next => cases h
  | number _ => simp [symLane] at h
  | name _ => simp [symLane] at h
  | call _ _ => simp [symLane] at h

theorem number_not_vector {n : String} (h : isNumberLetter n = true) : isVectorLetter n = false := by
  simp only [isNumberLetter, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((rfl | rfl) | rfl) | rfl) | rfl <;> decide

/-- A number of the table in an EFFECT: the machine has the same number; it is no vector register. -/
theorem symNumber_sound {perm : Perm} {bind : Bind} {st : State} {e : Expr} {k : Int} (h : symNumber bind e = some k) :
    0 ≤ k ∧ k < 2 ^ 64 ∧ value perm bind st e = some k.toNat ∧ vecArg bind st e = none := by
  cases e with
  | number n =>
    simp only [symNumber] at h
    split at h
    next lt =>
      injection h with h; subst h
      exact ⟨Int.natCast_nonneg n, by exact_mod_cast lt, by simp [value], rfl⟩
    next => cases h
  | name n =>
    simp only [symNumber] at h
    split at h
    next hl =>
      cases hb : (bind.lookup n).bind readInt with
      | none => simp [hb] at h
      | some i =>
        simp only [hb, Option.map_some] at h
        injection h with h; subst h
        have h1 := Int.emod_nonneg i (show (M64 : Int) ≠ 0 by decide)
        have h2 := Int.emod_lt_of_pos i (show (0 : Int) < (M64 : Int) by decide)
        refine ⟨h1, by rw [M64_cast] at h2; exact h2, by simp [value, hl, hb], ?_⟩
        simp [vecArg, vecOf, number_not_vector hl]
    next => cases h
  | lane _ _ => simp [symNumber] at h
  | call _ _ => simp [symNumber] at h

/-- A general register in an EFFECT: the machine's number in it is the row's. -/
theorem symReg_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} {bind : Bind} {e : Expr} {x : Row}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (h : symReg bind s e = some x) :
    ∃ xa, value (ctx.contract.perm s0) bind st e = some xa ∧ xa < M64 ∧ (xa : Int) = ev ρ x ∧ bounded s.nvars x := by
  cases e with
  | name n =>
    simp only [symReg] at h
    split at h
    next => cases h
    next hl =>
      cases hr : regOf bind n with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.map_some] at h
        injection h with h; subst h
        have lt := regOf_lt hr
        exact ⟨st.reg r, by simp [value, hl, hr], H.small r, H.reg r lt, wf.reg r lt⟩
  | number _ => simp [symReg] at h
  | lane _ _ => simp [symReg] at h
  | call _ _ => simp [symReg] at h

/-! ## Sixteen bytes read -/

theorem runAt_spec {r : Nat} : ∀ {l : List (String × Nat × Nat)} {k j : Nat}, runAt r l k = some j →
    k ≤ j ∧ ∃ x n, l[j - k]? = some (x, r, n)
  | [], _, _, h => by simp [runAt] at h
  | (x, r', n) :: more, k, j, h => by
    simp only [runAt] at h
    split at h
    next e =>
      injection h with h; subst h; subst e
      exact ⟨Nat.le_refl _, x, n, by simp⟩
    next =>
      obtain ⟨le, x', n', hj⟩ := runAt_spec h
      refine ⟨by omega, x', n', ?_⟩
      have : j - k = (j - (k + 1)) + 1 := by omega
      rw [this]; simpa using hj

/-- The four words of a run at a place divisible by four, where memory there is as it was at entry: the
terms made for them are the words the machine reads. -/
theorem load128_terms {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF s)
    {j : Nat} {x : String} {r n c : Nat} (hj : (ctx.contract.fixeds ++ ctx.contract.inouts)[j]? = some (x, r, n))
    (hmem : ∀ k, k < 16 → st.mem (s0.reg r + c + k) = s0.mem (s0.reg r + c + k)) (hc : c % 4 = 0) :
    Carried ctx s0 ρ s ρ { s with terms := (termsOf intern ((List.range 4).map fun i => Node.input j (c / 4 + i)) s.terms).2 } st ∧
    (∀ i ∈ (termsOf intern ((List.range 4).map fun i => Node.input j (c / 4 + i)) s.terms).1,
      i < (termsOf intern ((List.range 4).map fun i => Node.input j (c / 4 + i)) s.terms).2.length) ∧
    ∀ k, k < 4 → load st.mem (s0.reg r + c + 4 * k) 4 =
      den (inpOf ctx s0) ρ (termsOf intern ((List.range 4).map fun i => Node.input j (c / 4 + i)) s.terms).2
        ((termsOf intern ((List.range 4).map fun i => Node.input j (c / 4 + i)) s.terms).1.getD k 0) := by
  obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := intern)
    (val := fun nd => match nd with | .input j k => inpOf ctx s0 j k | _ => 0)
    (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) ((List.range 4).map fun i => Node.input j (c / 4 + i)) s.terms
    (by
      intro a ma T eT okT
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ma
      exact input_step okT)
    (Ext.refl _) wf.words.ok
  refine ⟨Carried.terms H wf e ok, lt, ?_⟩
  intro k hk
  rw [dn k (by simpa using hk)]
  simp only [List.getElem_map, List.getElem_range]
  unfold inpOf
  rw [hj]
  have e4 : 4 * (c / 4 + k) = c + 4 * k := by omega
  simp only [e4]
  rw [← Nat.add_assoc]
  apply load_congr
  intro y hy1 hy2
  have := hmem (y - (s0.reg r + c)) (by omega)
  have ey : s0.reg r + c + (y - (s0.reg r + c)) = y := by omega
  rw [ey] at this; exact this

theorem symLoad128_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s1 : Sym} {addr : Row} {l : List Nat}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symLoad128 ctx s addr items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (a : Nat)
    (ha : ∀ A : Nat, (A : Int) = ev ρ addr → A < M64 → a = A) :
    allowed (ctx.contract.perm s0).read a 16 = true ∧ Carried ctx s0 ρ s ρ s1 st ∧ (∀ i ∈ l, i < s1.terms.length) ∧
    ∀ k, k < 4 → load st.mem (a + 4 * k) 4 = den (inpOf ctx s0) ρ s1.terms (l.getD k 0) := by
  unfold symLoad128 at h
  cases hf : findOut addr ctx.contract.fixeds 0 with
  | some w0 =>
    obtain ⟨j, off, x, r, n, rfl, _, hj, ho⟩ := findOut_spec hf
    simp only [hf] at h
    have hj' : ctx.contract.fixeds[j]? = some (x, r, n) := by simpa using hj
    simp only [hj'] at h
    cases hc : Lin.isConst off with
    | none => simp only [hc] at h; exact (refuse_ok h).elim
    | some c =>
      simp only [hc] at h
      split at h
      next hcond =>
        have := V.pure_ok h
        injection this with h1 _
        injection h1 with h1 h2
        subst h1 h2
        obtain ⟨c0, cm, cn⟩ := hcond
        have hm := List.mem_of_getElem? hj'
        obtain ⟨f1, f2, f3, f4⟩ := E.fixed hm
        have hr : ρ r = s0.reg r := H.entry r (fixeds_lt hm)
        have eoff := ev_isConst (ρ := ρ) hc
        rw [ho, ev_sub, ev_var, hr] at eoff
        have hA : a = s0.reg r + c.toNat := ha (s0.reg r + c.toNat) (by omega) (by unfold M64 at f1 ⊢; omega)
        have hjj : (ctx.contract.fixeds ++ ctx.contract.inouts)[j]? = some (x, r, n) := by
          rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj').1]; exact hj'
        have hstack := E.stack
        have hmem : ∀ k, k < 16 → st.mem (s0.reg r + c.toNat + k) = s0.mem (s0.reg r + c.toNat + k) := by
          intro k hk
          apply H.mem
          · simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
          · unfold Contract.inOut
            rw [List.any_eq_false]
            intro ⟨x', r', n'⟩ hm'
            have := f4 x' r' n' hm'
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            omega
        obtain ⟨cr, lt, dn⟩ := load128_terms (ρ := ρ) H wf hjj hmem (by omega)
        refine ⟨allowed_of _ _ _ ?_, cr, lt, ?_⟩
        · intro y hy1 hy2
          simp only [Contract.perm, Bool.or_eq_true]
          right
          unfold Contract.inFixed
          simp only [Bool.or_eq_true]
          left
          exact List.any_eq_true.mpr ⟨(x, r, n), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        · intro k hk
          rw [hA]; exact dn k hk
      next => exact (refuse_ok h).elim
  | none =>
    simp only [hf] at h
    cases hf2 : findOut addr ctx.contract.outs 0 with
    | none => simp only [hf2] at h; exact (refuse_ok h).elim
    | some w0 =>
      obtain ⟨w, off, x, r, n, rfl, _, hw, ho⟩ := findOut_spec hf2
      simp only [hf2] at h
      have hw' : ctx.contract.outs[w]? = some (x, r, n) := by simpa using hw
      simp only [hw'] at h
      cases hc : Lin.isConst off with
      | none => simp only [hc] at h; exact (refuse_ok h).elim
      | some c =>
        simp only [hc] at h
        cases hra : runAt r (ctx.contract.fixeds ++ ctx.contract.inouts) 0 with
        | none => simp only [hra] at h; exact (refuse_ok h).elim
        | some j =>
          simp only [hra] at h
          obtain ⟨_, x', n', hj⟩ := runAt_spec hra
          have hj' : (ctx.contract.fixeds ++ ctx.contract.inouts)[j]? = some (x', r, n') := by simpa using hj
          simp only [hj'] at h
          split at h
          next => exact (refuse_ok h).elim
          next hin =>
            split at h
            next hcond =>
              have := V.pure_ok h
              injection this with h1 _
              injection h1 with h1 h2
              subst h1 h2
              obtain ⟨c0, cm, cn, cn'⟩ := hcond
              have hin' : w ∈ s.intact := by simpa using hin
              have hm := List.mem_of_getElem? hw'
              have hfit := (E.out hm).1
              have hr : ρ r = s0.reg r := H.entry r (outs_lt hm)
              have eoff := ev_isConst (ρ := ρ) hc
              rw [ho, ev_sub, ev_var, hr] at eoff
              have hA : a = s0.reg r + c.toNat := ha (s0.reg r + c.toNat) (by omega) (by unfold M64 at hfit ⊢; omega)
              have hmem : ∀ k, k < 16 → st.mem (s0.reg r + c.toNat + k) = s0.mem (s0.reg r + c.toNat + k) := by
                intro k hk
                have := H.words.2.1 w hin' x r n hw' (c.toNat + k) (by omega)
                rw [← Nat.add_assoc] at this; exact this
              obtain ⟨cr, lt, dn⟩ := load128_terms (ρ := ρ) H wf hj' hmem (by omega)
              refine ⟨allowed_of _ _ _ ?_, cr, lt, ?_⟩
              · intro y hy1 hy2
                simp only [Contract.perm, Bool.or_eq_true]
                right
                unfold Contract.inFixed
                simp only [Bool.or_eq_true]
                rcases List.mem_append.mp (List.mem_of_getElem? hj') with m | m
                · left
                  exact List.any_eq_true.mpr ⟨(x', r, n'), m, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
                · right
                  exact List.any_eq_true.mpr ⟨(x', r, n'), m, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
              · intro k hk
                rw [hA]; exact dn k hk
            next => exact (refuse_ok h).elim

/-! ## The four words a row sets a vector register to -/

theorem isConst_constant {a : Row} {k : Int} (h : Lin.isConst a = some k) : k = a.constant := by
  unfold Lin.isConst at h
  split at h
  next => injection h with h; exact h.symm
  next => contradiction

theorem vec4_getD {f : Nat → Nat} {k : Nat} (hk : k < 4) : [f 0, f 1, f 2, f 3].getD k 0 = f k := by
  rcases lt4 hk with rfl | rfl | rfl | rfl <;> rfl

theorem getD4_mem {l : List Nat} (h : l.length = 4) {k : Nat} (hk : k < 4) : l.getD k 0 ∈ l := by
  obtain ⟨a, b, c, d, rfl⟩ := list4 h
  rcases lt4 hk with rfl | rfl | rfl | rfl <;> simp

theorem word_of_const (ρ : Nat → Int) {k : Int} (h : 0 ≤ k) : k.toNat % W32 = (ev ρ (Lin.const k) % W32i).toNat := by
  rw [ev_const]; unfold W32 W32i; omega

/-- The two halves of what a general register holds: the terms made are the machine's two low lanes, and
two zeros. -/
theorem symHalves_sound {ctx : Ctx} {s0 : State} {s s1 : Sym} {x : Row} {l : List Nat} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symHalves s x items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (xa : Nat) (hxa : xa < M64)
    (hx : (xa : Int) = ev ρ x) (hb : bounded s.nvars x) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s1 st ∧ (∀ i ∈ l, i < s1.terms.length) ∧
      ∀ k, k < 4 → [xa % W32, xa / W32 % W32, 0, 0].getD k 0 = den (inpOf ctx s0) ρ' s1.terms (l.getD k 0) := by
  unfold symHalves at h
  split at h
  next =>
    have := V.pure_ok h
    injection this with h1 _
    injection h1 with h1 h2
    subst h1 h2
    obtain ⟨ρ', c, hq, _, bq, _⟩ := symDivide_sound (ctx := ctx) (s0 := s0) (m := W32i) H wf hb (by decide) (by rw [← hx]; omega)
    have ex : ev ρ' x = ev ρ x := (ev_agree hb c.agree).symm
    obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := wAtom) (val := fun r => (ev ρ' r % W32i).toNat) (inp := inpOf ctx s0) (ρ := ρ')
      (nv := (symDivide s x W32i).2.2.nvars) (T0 := (symDivide s x W32i).2.2.terms)
      [x, (symDivide s x W32i).1, Lin.const 0, Lin.const 0] (symDivide s x W32i).2.2.terms
      (by
        intro r mr T eT okT
        apply wAtom_step okT
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at mr
        rcases mr with rfl | rfl | rfl | rfl
        · exact bounded_mono c.mono hb
        · exact bq
        · exact bounded_const _ _
        · exact bounded_const _ _)
      (Ext.refl _) c.wf.words.ok
    refine ⟨ρ', c.then (Carried.terms c.holds c.wf e ok), lt, ?_⟩
    intro k hk
    rcases lt4 hk with rfl | rfl | rfl | rfl
    · rw [dn 0 (by show _ < 4; omega)]
      show xa % W32 = (ev ρ' x % W32i).toNat
      rw [ex, ← hx]; unfold W32 W32i; omega
    · rw [dn 1 (by show _ < 4; omega)]
      show xa / W32 % W32 = (ev ρ' (symDivide s x W32i).1 % W32i).toNat
      rw [hq, ← hx]; unfold W32 W32i; omega
    · rw [dn 2 (by show _ < 4; omega)]
      show 0 = (ev ρ' (Lin.const 0) % W32i).toNat
      rw [ev_const]; rfl
    · rw [dn 3 (by show _ < 4; omega)]
      show 0 = (ev ρ' (Lin.const 0) % W32i).toNat
      rw [ev_const]; rfl
  next =>
    have hw : (0 ≤ ev ρ (Lin.word x) ∧ ev ρ (Lin.word x) < W32i) ∧
        (l, s1) = ((termsOf wAtom [x, Lin.high x, Lin.const 0, Lin.const 0] s.terms).1,
                   { s with terms := (termsOf wAtom [x, Lin.high x, Lin.const 0, Lin.const 0] s.terms).2 }) := by
      split at h
      next =>
        obtain ⟨_, r1, g1, h⟩ := V.bind_ok h
        obtain ⟨_, r2, g2, h⟩ := V.bind_ok h
        have g1 := entail_sound g1 ρ H.facts
        have g2 := entail_sound g2 ρ H.facts
        simp only [ev_sub, ev_const] at g2
        have := V.pure_ok h
        injection this with h1 _
        exact ⟨⟨g1, by omega⟩, h1⟩
      next hc =>
        have := V.pure_ok h
        injection this with h1 _
        refine ⟨?_, h1⟩
        cases hk : Lin.isConst (Lin.word x) with
        | none => simp [hk] at hc
        | some cst =>
          have e1 := ev_isConst (ρ := ρ) hk
          have e2 : cst = x.constant % W32i := isConst_constant hk
          rw [e1, e2]
          exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
    obtain ⟨hw, h1⟩ := hw
    injection h1 with h1 h2
    subst h1 h2
    have eh := ev_high ρ x
    obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := wAtom) (val := fun r => (ev ρ r % W32i).toNat) (inp := inpOf ctx s0) (ρ := ρ)
      (nv := s.nvars) (T0 := s.terms) [x, Lin.high x, Lin.const 0, Lin.const 0] s.terms
      (by
        intro r mr T eT okT
        apply wAtom_step okT
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at mr
        rcases mr with rfl | rfl | rfl | rfl
        · exact hb
        · exact bounded_high hb
        · exact bounded_const _ _
        · exact bounded_const _ _)
      (Ext.refl _) wf.words.ok
    refine ⟨ρ, Carried.terms H wf e ok, lt, ?_⟩
    intro k hk
    rcases lt4 hk with rfl | rfl | rfl | rfl
    · rw [dn 0 (by show _ < 4; omega)]
      show xa % W32 = (ev ρ x % W32i).toNat
      rw [← hx]; unfold W32 W32i; omega
    · rw [dn 1 (by show _ < 4; omega)]
      show xa / W32 % W32 = (ev ρ (Lin.high x) % W32i).toNat
      obtain ⟨w0, w1⟩ := hw
      unfold W32i at eh w1 ⊢
      unfold W32
      omega
    · rw [dn 2 (by show _ < 4; omega)]
      show 0 = (ev ρ (Lin.const 0) % W32i).toNat
      rw [ev_const]; rfl
    · rw [dn 3 (by show _ < 4; omega)]
      show 0 = (ev ρ (Lin.const 0) % W32i).toNat
      rw [ev_const]; rfl

theorem pure_pair {α β : Type} {a x : α} {b y : β} {items rest : Items}
    (h : (Pure.pure (a, b) : V (α × β)) items = .ok ((x, y), rest)) : x = a ∧ y = b := by
  have := V.pure_ok h
  injection this with h1 _
  injection h1 with h1 h2
  exact ⟨h1, h2⟩

/-! ## Shifts, shuffles of bytes and blends of halves -/

theorem wShl_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {T : List Node} {a n : Nat} (ok : TableOk nv T)
    (ha : a < T.length) : Step inp ρ nv T (wShl a n T).2 (wShl a n T).1 ((den inp ρ T a <<< n) % W32) :=
  step_of_made ok (wShl_made (T' := (wShl a n T).2) (i := (wShl a n T).1) rfl ok.wf ha) (fun r e => by cases e) (fun a k e => by cases e)

theorem wShr_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {T : List Node} {a n : Nat} (ok : TableOk nv T)
    (ha : a < T.length) : Step inp ρ nv T (wShr a n T).2 (wShr a n T).1 (den inp ρ T a >>> n) :=
  step_of_made ok (wShr_made (T' := (wShr a n T).2) (i := (wShr a n T).1) rfl ok.wf ha) (fun r e => by cases e) (fun a k e => by cases e)

theorem orTurns4 {T : List Node} {x0 x1 x2 x3 y0 y1 y2 y3 : Nat} {turns : List (Nat × Nat)}
    (h : orTurns T ([x0, x1, x2, x3].zip [y0, y1, y2, y3]) = some turns) :
    ∃ t0 t1 t2 t3, turns = [t0, t1, t2, t3] ∧ orTurn T x0 y0 = some t0 ∧ orTurn T x1 y1 = some t1 ∧
      orTurn T x2 y2 = some t2 ∧ orTurn T x3 y3 = some t3 := by
  simp only [List.zip_cons_cons, List.zip_nil_right, orTurns] at h
  cases h0 : orTurn T x0 y0 <;> cases h1 : orTurn T x1 y1 <;> cases h2 : orTurn T x2 y2 <;> cases h3 : orTurn T x3 y3 <;>
    simp only [h0, h1, h2, h3, reduceCtorEq] at h
  rename_i t0 t1 t2 t3
  injection h with h
  exact ⟨t0, t1, t2, t3, h.symm, rfl, rfl, rfl, rfl⟩

theorem constWords_cons {T : List Node} {a : Nat} {more : List Nat} {ks : List Int} (h : constWords T (a :: more) = some ks) :
    ∃ r k ks', T[a]? = some (.atom r) ∧ Lin.isConst r = some k ∧ constWords T more = some ks' ∧ ks = k :: ks' := by
  simp only [constWords] at h
  cases ha : T[a]? with
  | none => simp [ha] at h
  | some n =>
    cases hm : constWords T more with
    | none => cases n <;> simp [ha, hm] at h
    | some ks' =>
      cases n with
      | atom r =>
        simp only [ha, hm] at h
        cases hk : Lin.isConst r with
        | none => simp [hk] at h
        | some k =>
          simp only [hk, Option.map_some, Option.some.injEq] at h
          exact ⟨r, k, ks', rfl, hk, rfl, h.symm⟩
      | _ => simp [ha, hm] at h

/-- A term that is a number of the table is that number as a word. -/
theorem constWord_den {inp : Nat → Nat → Nat} {ρ : Nat → Int} {T : List Node} {y : Nat} {r : Row} {k : Int} (hw : WFT T)
    (hy : T[y]? = some (.atom r)) (hk : Lin.isConst r = some k) : den inp ρ T y = (k % W32i).toNat := by
  rw [den_node hw hy]
  simp only [Node.value, ev_isConst hk]

/-- The shuffle of bytes a turn by 8 bits is written as: each word turned right by 8 bits. -/
theorem shuffle_rot8 {a0 a1 a2 a3 : Nat} (h0 : a0 < W32) (h1 : a1 < W32) (h2 : a2 < W32) (h3 : a3 < W32) :
    shuffleBytes [a0, a1, a2, a3] [0x00030201, 0x04070605, 0x080B0A09, 0x0C0F0E0D] =
      [rotr a0 8, rotr a1 8, rotr a2 8, rotr a3 8] := by
  unfold W32 at h0 h1 h2 h3
  simp [shuffleBytes, byteOf, rotr, List.range, List.range.loop]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem shuffle_rot16 {a0 a1 a2 a3 : Nat} (h0 : a0 < W32) (h1 : a1 < W32) (h2 : a2 < W32) (h3 : a3 < W32) :
    shuffleBytes [a0, a1, a2, a3] [0x01000302, 0x05040706, 0x09080B0A, 0x0D0C0F0E] =
      [rotr a0 16, rotr a1 16, rotr a2 16, rotr a3 16] := by
  unfold W32 at h0 h1 h2 h3
  simp [shuffleBytes, byteOf, rotr, List.range, List.range.loop]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- A blend of halves in which the two halves of each word come from one register: each word whole. -/
theorem blend_words {a0 a1 a2 a3 b0 b1 b2 b3 i : Nat} (ha0 : a0 < W32) (ha1 : a1 < W32) (ha2 : a2 < W32) (ha3 : a3 < W32)
    (hb0 : b0 < W32) (hb1 : b1 < W32) (hb2 : b2 < W32) (hb3 : b3 < W32)
    (hi : (List.range 4).all (fun k => i / 4 ^ k % 4 == 0 || i / 4 ^ k % 4 == 3) = true) :
    blendHalves [a0, a1, a2, a3] [b0, b1, b2, b3] i =
      (List.range 4).map (fun k => if i / 4 ^ k % 4 = 3 then [b0, b1, b2, b3].getD k 0 else [a0, a1, a2, a3].getD k 0) := by
  unfold W32 at *
  simp [List.range, List.range.loop] at hi
  obtain ⟨c0, c1, c2, c3⟩ := hi
  simp [blendHalves, halfOf, List.range, List.range.loop]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals (repeat' split)
  all_goals (try simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some])
  all_goals omega

/-- `each32`: what the verifier takes the four words to be, the machine sets. -/
theorem symEach32_sound {ctx : Ctx} {s0 : State} (bind : Bind) {s s1 : Sym}  {args : List Expr} {l : List Nat}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symEach32 bind s args items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s1 st ∧ ∃ lanes, lanesOf (ctx.contract.perm s0) bind st (.call "each32" args) = some lanes ∧
      (∀ i ∈ l, i < s1.terms.length) ∧ ∀ k, k < 4 → lanes.getD k 0 = den (inpOf ctx s0) ρ' s1.terms (l.getD k 0) := by
  unfold symEach32 at h
  rcases args with _ | ⟨e1, _ | ⟨a, _ | ⟨b, _ | ⟨e4, more⟩⟩⟩⟩
  · exact (refuse_ok h).elim
  · exact (refuse_ok h).elim
  · exact (refuse_ok h).elim
  · cases e1 with
    | number _ => exact (refuse_ok h).elim
    | lane _ _ => exact (refuse_ok h).elim
    | call _ _ => exact (refuse_ok h).elim
    | name op =>
      cases hx : symVec bind s a with
      | none => simp only [hx] at h; exact (refuse_ok h).elim
      | some x =>
        simp only [hx] at h
        obtain ⟨rx, lenx, ltx, hvx, hdx⟩ := symVec_sound H wf hx
        obtain ⟨x0, x1, x2, x3, rfl⟩ := list4 lenx
        cases hy : symVec bind s b with
        | some y =>
          simp only [hy] at h
          obtain ⟨ry, leny, lty, hvy, hdy⟩ := symVec_sound H wf hy
          obtain ⟨y0, y1, y2, y3, rfl⟩ := list4 leny
          split at h
          next hop =>
            have oe : op = "add32" := by simpa using hop
            subst oe
            obtain ⟨rfl, rfl⟩ := pure_pair h
            obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := fun (q : Nat × Nat) => wAdd q.1 q.2)
              (val := fun q => (den (inpOf ctx s0) ρ s.terms q.1 + den (inpOf ctx s0) ρ s.terms q.2) % W32)
              (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) ([x0, x1, x2, x3].zip [y0, y1, y2, y3]) s.terms
              (by
                intro q mq T eT okT
                have m1 := ltx q.1 (List.of_mem_zip (a := q.1) (b := q.2) mq).1
                have m2 := lty q.2 (List.of_mem_zip (a := q.1) (b := q.2) mq).2
                have S := wAdd_step (inp := inpOf ctx s0) (ρ := ρ) okT (Nat.lt_of_lt_of_le m1 eT.le) (Nat.lt_of_lt_of_le m2 eT.le)
                rw [den_ext wf.words.table eT m1, den_ext wf.words.table eT m2] at S
                exact S)
              (Ext.refl _) wf.words.ok
            refine ⟨ρ, Carried.terms H wf e ok,
              [(st.vec rx 0 + st.vec ry 0) % W32, (st.vec rx 1 + st.vec ry 1) % W32, (st.vec rx 2 + st.vec ry 2) % W32,
               (st.vec rx 3 + st.vec ry 3) % W32], ?_, lt, ?_⟩
            · simp [lanesOf, hvx, hvy, prim32]
            · intro k hk
              rcases lt4 hk with rfl | rfl | rfl | rfl
              · rw [dn 0 (by show _ < 4; omega), hdx 0 (by omega), hdy 0 (by omega)]; rfl
              · rw [dn 1 (by show _ < 4; omega), hdx 1 (by omega), hdy 1 (by omega)]; rfl
              · rw [dn 2 (by show _ < 4; omega), hdx 2 (by omega), hdy 2 (by omega)]; rfl
              · rw [dn 3 (by show _ < 4; omega), hdx 3 (by omega), hdy 3 (by omega)]; rfl
          next hop =>
            split at h
            next hop2 =>
              have oe : op = "xor32" := by simpa using hop2
              subst oe
              obtain ⟨rfl, rfl⟩ := pure_pair h
              obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := fun (q : Nat × Nat) => wXor q.1 q.2)
                (val := fun q => den (inpOf ctx s0) ρ s.terms q.1 ^^^ den (inpOf ctx s0) ρ s.terms q.2)
                (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) ([x0, x1, x2, x3].zip [y0, y1, y2, y3]) s.terms
                (by
                  intro q mq T eT okT
                  have m1 := ltx q.1 (List.of_mem_zip (a := q.1) (b := q.2) mq).1
                  have m2 := lty q.2 (List.of_mem_zip (a := q.1) (b := q.2) mq).2
                  have S := wXor_step (inp := inpOf ctx s0) (ρ := ρ) okT (Nat.lt_of_lt_of_le m1 eT.le) (Nat.lt_of_lt_of_le m2 eT.le)
                  rw [den_ext wf.words.table eT m1, den_ext wf.words.table eT m2] at S
                  exact S)
                (Ext.refl _) wf.words.ok
              refine ⟨ρ, Carried.terms H wf e ok,
                [st.vec rx 0 ^^^ st.vec ry 0, st.vec rx 1 ^^^ st.vec ry 1, st.vec rx 2 ^^^ st.vec ry 2, st.vec rx 3 ^^^ st.vec ry 3],
                ?_, lt, ?_⟩
              · simp [lanesOf, hvx, hvy, prim32]
              · intro k hk
                rcases lt4 hk with rfl | rfl | rfl | rfl
                · rw [dn 0 (by show _ < 4; omega), hdx 0 (by omega), hdy 0 (by omega)]; rfl
                · rw [dn 1 (by show _ < 4; omega), hdx 1 (by omega), hdy 1 (by omega)]; rfl
                · rw [dn 2 (by show _ < 4; omega), hdx 2 (by omega), hdy 2 (by omega)]; rfl
                · rw [dn 3 (by show _ < 4; omega), hdx 3 (by omega), hdy 3 (by omega)]; rfl
            next hop2 =>
              split at h
              next hop3 =>
                -- the or of a word shifted left and the same word shifted right: the word turned
                have oe : op = "or32" := by simpa using hop3
                subst oe
                cases ht : orTurns s.terms ([x0, x1, x2, x3].zip [y0, y1, y2, y3]) with
                | none => simp only [ht] at h; exact (refuse_ok h).elim
                | some turns =>
                  simp only [ht] at h
                  obtain ⟨rfl, rfl⟩ := pure_pair h
                  obtain ⟨t0, t1, t2, t3, rfl, g0, g1, g2, g3⟩ := orTurns4 ht
                  have dl : ∀ i, den (inpOf ctx s0) ρ s.terms i < W32 := fun i => den_lt wf.words.table (inpOf_lt ctx s0) wf.words.rotrs i
                  have o0 := orTurn_sound (inp := inpOf ctx s0) (ρ := ρ) wf.words.table dl g0
                  have o1 := orTurn_sound (inp := inpOf ctx s0) (ρ := ρ) wf.words.table dl g1
                  have o2 := orTurn_sound (inp := inpOf ctx s0) (ρ := ρ) wf.words.table dl g2
                  have o3 := orTurn_sound (inp := inpOf ctx s0) (ρ := ρ) wf.words.table dl g3
                  obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := fun (q : Nat × Nat) => wRotr q.1 q.2)
                    (val := fun q => rotr (den (inpOf ctx s0) ρ s.terms q.1) q.2)
                    (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) [t0, t1, t2, t3] s.terms
                    (by
                      intro q mq T eT okT
                      have hq : q.1 < s.terms.length ∧ q.2 ≤ 32 := by
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at mq
                        rcases mq with rfl | rfl | rfl | rfl
                        · exact ⟨o0.1, o0.2.1⟩
                        · exact ⟨o1.1, o1.2.1⟩
                        · exact ⟨o2.1, o2.2.1⟩
                        · exact ⟨o3.1, o3.2.1⟩
                      have S := wRotr_step (inp := inpOf ctx s0) (ρ := ρ) okT (Nat.lt_of_lt_of_le hq.1 eT.le) hq.2
                      rw [den_ext wf.words.table eT hq.1] at S
                      exact S)
                    (Ext.refl _) wf.words.ok
                  refine ⟨ρ, Carried.terms H wf e ok,
                    [st.vec rx 0 ||| st.vec ry 0, st.vec rx 1 ||| st.vec ry 1, st.vec rx 2 ||| st.vec ry 2, st.vec rx 3 ||| st.vec ry 3],
                    ?_, lt, ?_⟩
                  · simp [lanesOf, hvx, hvy, prim32]
                  · intro k hk
                    rcases lt4 hk with rfl | rfl | rfl | rfl
                    · rw [dn 0 (by show _ < 4; omega), hdx 0 (by omega), hdy 0 (by omega)]; exact o0.2.2
                    · rw [dn 1 (by show _ < 4; omega), hdx 1 (by omega), hdy 1 (by omega)]; exact o1.2.2
                    · rw [dn 2 (by show _ < 4; omega), hdx 2 (by omega), hdy 2 (by omega)]; exact o2.2.2
                    · rw [dn 3 (by show _ < 4; omega), hdx 3 (by omega), hdy 3 (by omega)]; exact o3.2.2
              next => exact (refuse_ok h).elim
        | none =>
          simp only [hy] at h
          cases hn : symNumber bind b with
          | none => simp only [hn] at h; exact (refuse_ok h).elim
          | some n =>
            simp only [hn] at h
            split at h
            next hop =>
              have oe : op = "ror32" := by simpa using hop
              subst oe
              obtain ⟨rfl, rfl⟩ := pure_pair h
              obtain ⟨n0, n_lt, vn, vecn⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) hn
              obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := fun q => wRotr q (n.toNat % 32))
                (val := fun q => rotr (den (inpOf ctx s0) ρ s.terms q) (n.toNat % 32))
                (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) [x0, x1, x2, x3] s.terms
                (by
                  intro q mq T eT okT
                  have m1 := ltx q mq
                  have S := wRotr_step (inp := inpOf ctx s0) (ρ := ρ) (n := n.toNat % 32) okT (Nat.lt_of_lt_of_le m1 eT.le) (by omega)
                  rw [den_ext wf.words.table eT m1] at S
                  exact S)
                (Ext.refl _) wf.words.ok
              refine ⟨ρ, Carried.terms H wf e ok,
                [rotr (st.vec rx 0) (n.toNat % 32), rotr (st.vec rx 1) (n.toNat % 32), rotr (st.vec rx 2) (n.toNat % 32),
                 rotr (st.vec rx 3) (n.toNat % 32)], ?_, lt, ?_⟩
              · simp [lanesOf, hvx, vecn, vn, prim32]
              · intro k hk
                rcases lt4 hk with rfl | rfl | rfl | rfl
                · rw [dn 0 (by show _ < 4; omega), hdx 0 (by omega)]; rfl
                · rw [dn 1 (by show _ < 4; omega), hdx 1 (by omega)]; rfl
                · rw [dn 2 (by show _ < 4; omega), hdx 2 (by omega)]; rfl
                · rw [dn 3 (by show _ < 4; omega), hdx 3 (by omega)]; rfl
            next hop =>
              split at h
              next hop2 =>
                have oe : op = "shl32" := by simpa using hop2
                subst oe
                obtain ⟨rfl, rfl⟩ := pure_pair h
                obtain ⟨n0, n_lt, vn, vecn⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) hn
                obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := fun q => wShl q n.toNat)
                  (val := fun q => (den (inpOf ctx s0) ρ s.terms q <<< n.toNat) % W32)
                  (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) [x0, x1, x2, x3] s.terms
                  (by
                    intro q mq T eT okT
                    have m1 := ltx q mq
                    have S := wShl_step (inp := inpOf ctx s0) (ρ := ρ) (n := n.toNat) okT (Nat.lt_of_lt_of_le m1 eT.le)
                    rw [den_ext wf.words.table eT m1] at S
                    exact S)
                  (Ext.refl _) wf.words.ok
                refine ⟨ρ, Carried.terms H wf e ok,
                  [(st.vec rx 0 <<< n.toNat) % W32, (st.vec rx 1 <<< n.toNat) % W32, (st.vec rx 2 <<< n.toNat) % W32,
                   (st.vec rx 3 <<< n.toNat) % W32], ?_, lt, ?_⟩
                · simp [lanesOf, hvx, vecn, vn, prim32]
                · intro k hk
                  rcases lt4 hk with rfl | rfl | rfl | rfl
                  · rw [dn 0 (by show _ < 4; omega), hdx 0 (by omega)]; rfl
                  · rw [dn 1 (by show _ < 4; omega), hdx 1 (by omega)]; rfl
                  · rw [dn 2 (by show _ < 4; omega), hdx 2 (by omega)]; rfl
                  · rw [dn 3 (by show _ < 4; omega), hdx 3 (by omega)]; rfl
              next hop2 =>
                split at h
                next hop3 =>
                  have oe : op = "shr32" := by simpa using hop3
                  subst oe
                  obtain ⟨rfl, rfl⟩ := pure_pair h
                  obtain ⟨n0, n_lt, vn, vecn⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) hn
                  obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := fun q => wShr q n.toNat)
                    (val := fun q => den (inpOf ctx s0) ρ s.terms q >>> n.toNat)
                    (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) [x0, x1, x2, x3] s.terms
                    (by
                      intro q mq T eT okT
                      have m1 := ltx q mq
                      have S := wShr_step (inp := inpOf ctx s0) (ρ := ρ) (n := n.toNat) okT (Nat.lt_of_lt_of_le m1 eT.le)
                      rw [den_ext wf.words.table eT m1] at S
                      exact S)
                    (Ext.refl _) wf.words.ok
                  refine ⟨ρ, Carried.terms H wf e ok,
                    [st.vec rx 0 >>> n.toNat, st.vec rx 1 >>> n.toNat, st.vec rx 2 >>> n.toNat, st.vec rx 3 >>> n.toNat], ?_, lt, ?_⟩
                  · simp [lanesOf, hvx, vecn, vn, prim32]
                  · intro k hk
                    rcases lt4 hk with rfl | rfl | rfl | rfl
                    · rw [dn 0 (by show _ < 4; omega), hdx 0 (by omega)]; rfl
                    · rw [dn 1 (by show _ < 4; omega), hdx 1 (by omega)]; rfl
                    · rw [dn 2 (by show _ < 4; omega), hdx 2 (by omega)]; rfl
                    · rw [dn 3 (by show _ < 4; omega), hdx 3 (by omega)]; rfl
                next => exact (refuse_ok h).elim
  · exact (refuse_ok h).elim

/-- `shuffle_bytes`: what the verifier takes the four words to be, the machine sets. -/
theorem symShuffle_sound {ctx : Ctx} {s0 : State} (bind : Bind) {s s1 : Sym} {args : List Expr} {l : List Nat}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symShuffle bind s args items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s1 st ∧ ∃ lanes, lanesOf (ctx.contract.perm s0) bind st (.call "shuffle_bytes" args) = some lanes ∧
      (∀ i ∈ l, i < s1.terms.length) ∧ ∀ k, k < 4 → lanes.getD k 0 = den (inpOf ctx s0) ρ' s1.terms (l.getD k 0) := by
  unfold symShuffle at h
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, more⟩⟩⟩
  · exact (refuse_ok h).elim
  · exact (refuse_ok h).elim
  · cases hx : symVec bind s a <;> cases hy : symVec bind s b <;> simp only [hx, hy] at h
    all_goals try exact (refuse_ok h).elim
    rename_i x y
    obtain ⟨rx, lenx, ltx, hvx, hdx⟩ := symVec_sound H wf hx
    obtain ⟨ry, leny, lty, hvy, hdy⟩ := symVec_sound H wf hy
    obtain ⟨x0, x1, x2, x3, rfl⟩ := list4 lenx
    obtain ⟨y0, y1, y2, y3, rfl⟩ := list4 leny
    cases hn : (constWords s.terms [y0, y1, y2, y3]).bind shuffleTurn with
    | none => simp only [hn] at h; exact (refuse_ok h).elim
    | some n =>
      simp only [hn] at h
      obtain ⟨rfl, rfl⟩ := pure_pair h
      obtain ⟨ks, hks, htn⟩ := Option.bind_eq_some_iff.mp hn
      obtain ⟨r0, k0, ks0, a0, c0, m0, rfl⟩ := constWords_cons hks
      obtain ⟨r1, k1, ks1, a1, c1, m1, rfl⟩ := constWords_cons m0
      obtain ⟨r2, k2, ks2, a2, c2, m2, rfl⟩ := constWords_cons m1
      obtain ⟨r3, k3, ks3, a3, c3, m3, rfl⟩ := constWords_cons m2
      have e3 : ks3 = [] := by simp only [constWords, Option.some.injEq] at m3; exact m3.symm
      subst e3
      have dl : ∀ i, den (inpOf ctx s0) ρ s.terms i < W32 := fun i => den_lt wf.words.table (inpOf_lt ctx s0) wf.words.rotrs i
      have vx : ∀ k, k < 4 → st.vec rx k < W32 := fun k hk => by rw [hdx k hk]; exact dl _
      have d0 : st.vec ry 0 = (k0 % W32i).toNat := by rw [hdy 0 (by omega)]; exact constWord_den wf.words.table a0 c0
      have d1 : st.vec ry 1 = (k1 % W32i).toNat := by rw [hdy 1 (by omega)]; exact constWord_den wf.words.table a1 c1
      have d2 : st.vec ry 2 = (k2 % W32i).toNat := by rw [hdy 2 (by omega)]; exact constWord_den wf.words.table a2 c2
      have d3 : st.vec ry 3 = (k3 % W32i).toNat := by rw [hdy 3 (by omega)]; exact constWord_den wf.words.table a3 c3
      have turn : n ≤ 32 ∧ shuffleBytes [st.vec rx 0, st.vec rx 1, st.vec rx 2, st.vec rx 3] [st.vec ry 0, st.vec ry 1, st.vec ry 2, st.vec ry 3] =
          [rotr (st.vec rx 0) n, rotr (st.vec rx 1) n, rotr (st.vec rx 2) n, rotr (st.vec rx 3) n] := by
        rw [d0, d1, d2, d3]
        unfold shuffleTurn at htn
        split at htn
        next e8 =>
          injection htn with htn; subst htn
          injection e8 with e0 e8; injection e8 with e1 e8; injection e8 with e2 e8; injection e8 with e3 _
          subst e0 e1 e2 e3
          exact ⟨by decide, shuffle_rot8 (vx 0 (by omega)) (vx 1 (by omega)) (vx 2 (by omega)) (vx 3 (by omega))⟩
        next =>
          split at htn
          next e16 =>
            injection htn with htn; subst htn
            injection e16 with e0 e16; injection e16 with e1 e16; injection e16 with e2 e16; injection e16 with e3 _
            subst e0 e1 e2 e3
            exact ⟨by decide, shuffle_rot16 (vx 0 (by omega)) (vx 1 (by omega)) (vx 2 (by omega)) (vx 3 (by omega))⟩
          next => cases htn
      obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := fun q => wRotr q n)
        (val := fun q => rotr (den (inpOf ctx s0) ρ s.terms q) n)
        (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) [x0, x1, x2, x3] s.terms
        (by
          intro q mq T eT okT
          have m1 := ltx q mq
          have S := wRotr_step (inp := inpOf ctx s0) (ρ := ρ) (n := n) okT (Nat.lt_of_lt_of_le m1 eT.le) turn.1
          rw [den_ext wf.words.table eT m1] at S
          exact S)
        (Ext.refl _) wf.words.ok
      refine ⟨ρ, Carried.terms H wf e ok,
        [rotr (st.vec rx 0) n, rotr (st.vec rx 1) n, rotr (st.vec rx 2) n, rotr (st.vec rx 3) n], ?_, lt, ?_⟩
      · simp [lanesOf, hvx, hvy, turn.2]
      · intro k hk
        rcases lt4 hk with rfl | rfl | rfl | rfl
        · rw [dn 0 (by show _ < 4; omega), hdx 0 (by omega)]; rfl
        · rw [dn 1 (by show _ < 4; omega), hdx 1 (by omega)]; rfl
        · rw [dn 2 (by show _ < 4; omega), hdx 2 (by omega)]; rfl
        · rw [dn 3 (by show _ < 4; omega), hdx 3 (by omega)]; rfl
  · exact (refuse_ok h).elim

/-- `pick4`, `blend4`, `blend_halves`: what the verifier takes the four words to be, the machine sets. -/
theorem symMoved_sound {ctx : Ctx} {s0 : State} (bind : Bind) {s s1 : Sym} {f : String} {args : List Expr} {l : List Nat}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symMoved bind s f args items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s1 st ∧ ∃ lanes, lanesOf (ctx.contract.perm s0) bind st (.call f args) = some lanes ∧
      (∀ i ∈ l, i < s1.terms.length) ∧ ∀ k, k < 4 → lanes.getD k 0 = den (inpOf ctx s0) ρ' s1.terms (l.getD k 0) := by
  unfold symMoved at h
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨i, _ | ⟨e4, more⟩⟩⟩⟩
  · exact (refuse_ok h).elim
  · exact (refuse_ok h).elim
  · exact (refuse_ok h).elim
  · cases hx : symVec bind s a <;> cases hy : symVec bind s b <;> cases hi : symNumber bind i <;>
      simp only [hx, hy, hi] at h
    all_goals try exact (refuse_ok h).elim
    rename_i x y iv
    obtain ⟨rx, lenx, ltx, hvx, hdx⟩ := symVec_sound H wf hx
    obtain ⟨ry, leny, lty, hvy, hdy⟩ := symVec_sound H wf hy
    obtain ⟨i0, i_lt, vi, _⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) hi
    have m4 : ∀ j, j % 4 < 4 := fun j => Nat.mod_lt _ (by decide)
    split at h
    next hp =>
      have fe : f = "pick4" := by simpa using hp
      subst fe
      obtain ⟨rfl, rfl⟩ := pure_pair h
      refine ⟨ρ, Carried.here H wf,
        [[st.vec rx 0, st.vec rx 1, st.vec rx 2, st.vec rx 3].getD (iv.toNat % 4) 0,
         [st.vec rx 0, st.vec rx 1, st.vec rx 2, st.vec rx 3].getD (iv.toNat / 4 % 4) 0,
         [st.vec ry 0, st.vec ry 1, st.vec ry 2, st.vec ry 3].getD (iv.toNat / 16 % 4) 0,
         [st.vec ry 0, st.vec ry 1, st.vec ry 2, st.vec ry 3].getD (iv.toNat / 64 % 4) 0], ?_, ?_, ?_⟩
      · simp [lanesOf, hvx, hvy, vi]
      · intro j mj
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at mj
        rcases mj with rfl | rfl | rfl | rfl
        · exact ltx _ (getD4_mem lenx (m4 _))
        · exact ltx _ (getD4_mem lenx (m4 _))
        · exact lty _ (getD4_mem leny (m4 _))
        · exact lty _ (getD4_mem leny (m4 _))
      · intro k hk
        rcases lt4 hk with rfl | rfl | rfl | rfl
        · show [st.vec rx 0, st.vec rx 1, st.vec rx 2, st.vec rx 3].getD (iv.toNat % 4) 0 = _
          rw [vec4_getD (f := st.vec rx) (m4 _)]; exact hdx _ (m4 _)
        · show [st.vec rx 0, st.vec rx 1, st.vec rx 2, st.vec rx 3].getD (iv.toNat / 4 % 4) 0 = _
          rw [vec4_getD (f := st.vec rx) (m4 _)]; exact hdx _ (m4 _)
        · show [st.vec ry 0, st.vec ry 1, st.vec ry 2, st.vec ry 3].getD (iv.toNat / 16 % 4) 0 = _
          rw [vec4_getD (f := st.vec ry) (m4 _)]; exact hdy _ (m4 _)
        · show [st.vec ry 0, st.vec ry 1, st.vec ry 2, st.vec ry 3].getD (iv.toNat / 64 % 4) 0 = _
          rw [vec4_getD (f := st.vec ry) (m4 _)]; exact hdy _ (m4 _)
    next hp =>
      split at h
      next hb =>
        have fe : f = "blend4" := by simpa using hb
        subst fe
        obtain ⟨rfl, rfl⟩ := pure_pair h
        refine ⟨ρ, Carried.here H wf,
          (List.range 4).map (fun k => if iv.toNat / 2 ^ k % 2 = 1 then [st.vec ry 0, st.vec ry 1, st.vec ry 2, st.vec ry 3].getD k 0
            else [st.vec rx 0, st.vec rx 1, st.vec rx 2, st.vec rx 3].getD k 0), ?_, ?_, ?_⟩
        · simp [lanesOf, hvx, hvy, vi]
        · intro j mj
          obtain ⟨k, mk, rfl⟩ := List.mem_map.mp mj
          have hk : k < 4 := List.mem_range.mp mk
          split
          · exact lty _ (getD4_mem leny hk)
          · exact ltx _ (getD4_mem lenx hk)
        · intro k hk
          rcases lt4 hk with rfl | rfl | rfl | rfl
          · show (if _ then _ else _) = den _ _ _ (if _ then _ else _)
            split
            · exact hdy 0 (by omega)
            · exact hdx 0 (by omega)
          · show (if _ then _ else _) = den _ _ _ (if _ then _ else _)
            split
            · exact hdy 1 (by omega)
            · exact hdx 1 (by omega)
          · show (if _ then _ else _) = den _ _ _ (if _ then _ else _)
            split
            · exact hdy 2 (by omega)
            · exact hdx 2 (by omega)
          · show (if _ then _ else _) = den _ _ _ (if _ then _ else _)
            split
            · exact hdy 3 (by omega)
            · exact hdx 3 (by omega)
      next hb =>
        split at h
        next hh =>
          -- each word wholly from the one register or the other
          have fe : f = "blend_halves" := by simpa using hh
          subst fe
          split at h
          next hall =>
            have dl : ∀ i, den (inpOf ctx s0) ρ s.terms i < W32 := fun i => den_lt wf.words.table (inpOf_lt ctx s0) wf.words.rotrs i
            have vx : ∀ k, k < 4 → st.vec rx k < W32 := fun k hk => by rw [hdx k hk]; exact dl _
            have vy : ∀ k, k < 4 → st.vec ry k < W32 := fun k hk => by rw [hdy k hk]; exact dl _
            obtain ⟨rfl, rfl⟩ := pure_pair h
            refine ⟨ρ, Carried.here H wf,
              (List.range 4).map (fun k => if iv.toNat / 4 ^ k % 4 = 3 then [st.vec ry 0, st.vec ry 1, st.vec ry 2, st.vec ry 3].getD k 0
                else [st.vec rx 0, st.vec rx 1, st.vec rx 2, st.vec rx 3].getD k 0), ?_, ?_, ?_⟩
            · rw [← blend_words (vx 0 (by omega)) (vx 1 (by omega)) (vx 2 (by omega)) (vx 3 (by omega))
                (vy 0 (by omega)) (vy 1 (by omega)) (vy 2 (by omega)) (vy 3 (by omega)) hall]
              simp [lanesOf, hvx, hvy, vi]
            · intro j mj
              obtain ⟨k, mk, rfl⟩ := List.mem_map.mp mj
              have hk : k < 4 := List.mem_range.mp mk
              split
              · exact lty _ (getD4_mem leny hk)
              · exact ltx _ (getD4_mem lenx hk)
            · intro k hk
              rcases lt4 hk with rfl | rfl | rfl | rfl
              · show (if _ then _ else _) = den _ _ _ (if _ then _ else _)
                split
                · exact hdy 0 (by omega)
                · exact hdx 0 (by omega)
              · show (if _ then _ else _) = den _ _ _ (if _ then _ else _)
                split
                · exact hdy 1 (by omega)
                · exact hdx 1 (by omega)
              · show (if _ then _ else _) = den _ _ _ (if _ then _ else _)
                split
                · exact hdy 2 (by omega)
                · exact hdx 2 (by omega)
              · show (if _ then _ else _) = den _ _ _ (if _ then _ else _)
                split
                · exact hdy 3 (by omega)
                · exact hdx 3 (by omega)
          next => exact (refuse_ok h).elim
        next => exact (refuse_ok h).elim
  · exact (refuse_ok h).elim

/-- What the verifier takes the four words to be that a row sets a vector register to: the machine sets
those lanes. -/
theorem symLanes_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) {s s1 : Sym} {v : Expr} {l : List Nat}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symLanes ctx bind s v items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s1 st ∧ ∃ lanes, lanesOf (ctx.contract.perm s0) bind st v = some lanes ∧
      (∀ i ∈ l, i < s1.terms.length) ∧ ∀ k, k < 4 → lanes.getD k 0 = den (inpOf ctx s0) ρ' s1.terms (l.getD k 0) := by
  cases v with
  | number _ => simp only [symLanes] at h; exact (refuse_ok h).elim
  | lane _ _ => simp only [symLanes] at h; exact (refuse_ok h).elim
  | name n =>
    simp only [symLanes] at h
    cases hv : symVec bind s (.name n) with
    | none => simp only [hv] at h; exact (refuse_ok h).elim
    | some l' =>
      simp only [hv] at h
      obtain ⟨rfl, rfl⟩ := pure_pair h
      obtain ⟨r, len, lt, hva, hd⟩ := symVec_sound H wf hv
      refine ⟨ρ, Carried.here H wf, _, by simp only [lanesOf]; exact hva, lt, ?_⟩
      intro k hk
      rw [vec4_getD hk]; exact hd k hk
  | call f args =>
    simp only [symLanes] at h
    split at h
    next hf =>
      -- sixteen bytes of memory
      have fe : f = "mem128" := by simpa using hf
      subst fe
      rcases args with _ | ⟨b, _ | ⟨n, _ | ⟨c, more⟩⟩⟩
      · exact (refuse_ok h).elim
      · exact (refuse_ok h).elim
      · cases hx : symReg bind s b with
        | none => cases hk : symNumber bind n <;> simp only [hx, hk] at h <;> exact (refuse_ok h).elim
        | some x =>
          cases hk : symNumber bind n with
          | none => simp only [hx, hk] at h; exact (refuse_ok h).elim
          | some k =>
            simp only [hx, hk] at h
            obtain ⟨xb, vb, xb_lt, xb_ev, xb_b⟩ := symReg_sound H wf hx
            obtain ⟨k0, k_lt, vn, _⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) hk
            have sgx := signed_ev ρ x
            have sgk := signed_ev ρ (Lin.const k)
            rw [ev_const] at sgk
            obtain ⟨hal, cr, lt, dn⟩ := symLoad128_sound E h H wf ((xb + k.toNat) % M64) (by
              intro A hA hlt
              rw [ev_add] at hA
              unfold M64 at xb_lt hlt ⊢
              omega)
            refine ⟨ρ, cr, (List.range 4).map (fun i => load st.mem ((xb + k.toNat) % M64 + 4 * i) 4), ?_, lt, ?_⟩
            · simp [lanesOf, values_two vb vn, sumList, hal]
            · intro k' hk'
              rw [← dn k' hk']
              rcases lt4 hk' with rfl | rfl | rfl | rfl <;> rfl
      · exact (refuse_ok h).elim
    next hf =>
      split at h
      next hf2 =>
        -- four numbers of the table
        have fe : f = "words" := by simpa using hf2
        subst fe
        rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e5, more⟩⟩⟩⟩⟩
        · exact (refuse_ok h).elim
        · exact (refuse_ok h).elim
        · exact (refuse_ok h).elim
        · exact (refuse_ok h).elim
        · cases ha : symNumber bind a <;> cases hb : symNumber bind b <;> cases hc : symNumber bind c <;>
            cases hd : symNumber bind d <;> simp only [ha, hb, hc, hd] at h
          all_goals try exact (refuse_ok h).elim
          rename_i ka kb kc kd
          obtain ⟨rfl, rfl⟩ := pure_pair h
          obtain ⟨a0, _, va, _⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) ha
          obtain ⟨b0, _, vb, _⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) hb
          obtain ⟨c0, _, vc, _⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) hc
          obtain ⟨d0, _, vd, _⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) hd
          obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := wAtom) (val := fun r => (ev ρ r % W32i).toNat) (inp := inpOf ctx s0) (ρ := ρ)
            (nv := s.nvars) (T0 := s.terms) [Lin.const ka, Lin.const kb, Lin.const kc, Lin.const kd] s.terms
            (by
              intro r mr T eT okT
              apply wAtom_step okT
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at mr
              rcases mr with rfl | rfl | rfl | rfl <;> exact bounded_const _ _)
            (Ext.refl _) wf.words.ok
          refine ⟨ρ, Carried.terms H wf e ok, [ka.toNat % W32, kb.toNat % W32, kc.toNat % W32, kd.toNat % W32], ?_, lt, ?_⟩
          · simp [lanesOf, values, va, vb, vc, vd]
          · intro k hk
            rcases lt4 hk with rfl | rfl | rfl | rfl
            · rw [dn 0 (by show _ < 4; omega)]; exact word_of_const ρ a0
            · rw [dn 1 (by show _ < 4; omega)]; exact word_of_const ρ b0
            · rw [dn 2 (by show _ < 4; omega)]; exact word_of_const ρ c0
            · rw [dn 3 (by show _ < 4; omega)]; exact word_of_const ρ d0
        · exact (refuse_ok h).elim
      next hf2 =>
        split at h
        next hf3 =>
          -- the halves of a general register
          have fe : f = "lanes_of64" := by simpa using hf3
          subst fe
          rcases args with _ | ⟨a, _ | ⟨b, more⟩⟩
          · exact (refuse_ok h).elim
          · cases hx : symReg bind s a with
            | none => simp only [hx] at h; exact (refuse_ok h).elim
            | some x =>
              simp only [hx] at h
              obtain ⟨xa, va, xa_lt, xa_ev, xa_b⟩ := symReg_sound H wf hx
              obtain ⟨ρ', c, lt, dn⟩ := symHalves_sound h H wf xa xa_lt xa_ev xa_b
              exact ⟨ρ', c, [xa % W32, xa / W32 % W32, 0, 0], by simp [lanesOf, values, va], lt, dn⟩
          · exact (refuse_ok h).elim
        next hf3 =>
          split at h
          next hf4 =>
            -- four lanes picked
            have fe : f = "lanes" := by simpa using hf4
            subst fe
            rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e5, more⟩⟩⟩⟩⟩
            · exact (refuse_ok h).elim
            · exact (refuse_ok h).elim
            · exact (refuse_ok h).elim
            · exact (refuse_ok h).elim
            · cases ha : symLane bind s a <;> cases hb : symLane bind s b <;> cases hc : symLane bind s c <;>
                cases hd : symLane bind s d <;> simp only [ha, hb, hc, hd] at h
              all_goals try exact (refuse_ok h).elim
              rename_i ia ib ic id
              obtain ⟨rfl, rfl⟩ := pure_pair h
              obtain ⟨la, va, hla, ea⟩ := symLane_sound H wf ha
              obtain ⟨lb, vb, hlb, eb⟩ := symLane_sound H wf hb
              obtain ⟨lc, vc, hlc, ec⟩ := symLane_sound H wf hc
              obtain ⟨ld, vd, hld, ed⟩ := symLane_sound H wf hd
              refine ⟨ρ, Carried.here H wf, [va, vb, vc, vd], ?_, ?_, ?_⟩
              · simp [lanesOf, hla, hlb, hlc, hld]
              · intro i mi
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at mi
                rcases mi with rfl | rfl | rfl | rfl <;> assumption
              · intro k hk
                rcases lt4 hk with rfl | rfl | rfl | rfl <;> assumption
            · exact (refuse_ok h).elim
          next hf4 =>
            split at h
            next hf5 =>
              -- lane by lane
              have fe : f = "each32" := by simpa using hf5
              subst fe
              exact symEach32_sound bind h H wf
            next hf5 =>
              split at h
              next hf6 =>
                have fe : f = "shuffle_bytes" := by simpa using hf6
                subst fe
                exact symShuffle_sound bind h H wf
              next hf6 => exact symMoved_sound bind h H wf

/-! ## Sixteen bytes written -/

theorem store_at : ∀ (n : Nat) (mem : Nat → Nat) (a v b : Nat), b < n → store mem a v n (a + b) = v / 256 ^ b % 256
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, mem, a, v, b, h => by
    simp only [store]
    cases b with
    | zero =>
      rw [store_other _ _ _ _ _ (by omega)]
      simp
    | succ b =>
      have e : a + (b + 1) = (a + 1) + b := by omega
      rw [e, store_at n _ (a + 1) (v / 256) b (by omega), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem store4_other (mem : Nat → Nat) (a v0 v1 v2 v3 y : Nat) (h : y < a ∨ a + 16 ≤ y) :
    store (store (store (store mem a v0 4) (a + 4) v1 4) (a + 8) v2 4) (a + 12) v3 4 y = mem y := by
  rw [store_other _ _ _ _ _ (by omega), store_other _ _ _ _ _ (by omega), store_other _ _ _ _ _ (by omega),
      store_other _ _ _ _ _ (by omega)]

theorem store4_at (mem : Nat → Nat) (a v0 v1 v2 v3 : Nat) {i b : Nat} (hi : i < 4) (hb : b < 4) :
    store (store (store (store mem a v0 4) (a + 4) v1 4) (a + 8) v2 4) (a + 12) v3 4 (a + 4 * i + b) =
      [v0, v1, v2, v3].getD i 0 / 256 ^ b % 256 := by
  rcases lt4 hi with rfl | rfl | rfl | rfl
  · rw [store_other _ _ _ _ _ (by omega), store_other _ _ _ _ _ (by omega), store_other _ _ _ _ _ (by omega)]
    exact store_at 4 mem a v0 b hb
  · rw [store_other _ _ _ _ _ (by omega), store_other _ _ _ _ _ (by omega)]
    exact store_at 4 _ (a + 4) v1 b hb
  · rw [store_other _ _ _ _ _ (by omega)]
    exact store_at 4 _ (a + 8) v2 b hb
  · exact store_at 4 _ (a + 12) v3 b hb

theorem lookup_cons_cases {x r : Nat} {l ids : List Nat} {more : List (Nat × List Nat)} (h : ((r, l) :: more).lookup x = some ids) :
    (x = r ∧ ids = l) ∨ (x ≠ r ∧ more.lookup x = some ids) := by
  by_cases e : x = r
  · subst e
    left
    simp [List.lookup] at h
    exact ⟨rfl, h.symm⟩
  · right
    refine ⟨e, ?_⟩
    have ne : (x == r) = false := by simpa using e
    simp only [List.lookup, ne] at h
    exact h

/-- Four words of a vector register stored into a run given to write, at a place divisible by four: the
run's words there are now the register's terms; what was known of other words and other runs is still so. -/
theorem Holds.store128 {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) {w : Nat} {name : String} {r n : Nat} (hw : ctx.contract.outs[w]? = some (name, r, n))
    {c : Nat} (hc4 : c % 4 = 0) (hcn : c + 16 ≤ n) (hnw : (s.wrote.any fun e => e.1 == w) = false)
    {rv : Nat} {l : List Nat} (hd : ∀ k, k < 4 → st.vec rv k = den (inpOf ctx s0) ρ s.terms (l.getD k 0))
    (a : Nat) (ha : a = s0.reg r + c) :
    Holds ctx s0 ρ { s with intact := s.intact.filter (· != w),
                            wroteW := ((List.range 4).map fun i => (w, c / 4 + i, l.getD i 0)) ++
                                      s.wroteW.filter fun e => !(e.1 == w && decide (c / 4 ≤ e.2.1) && decide (e.2.1 < c / 4 + 4)) }
      { st with mem := store (store (store (store st.mem a (st.vec rv 0) 4) (a + 4) (st.vec rv 1) 4) (a + 8) (st.vec rv 2) 4)
                         (a + 12) (st.vec rv 3) 4 } where
  entry := H.entry
  reg := H.reg
  small := H.small
  zf := H.zf
  cf := H.cf
  facts := H.facts
  spec := H.spec
  bytes := H.bytes
  frame o' v m := by
    obtain ⟨g1, g2, g3⟩ := H.frame o' v m
    refine ⟨g1, g2, ?_⟩
    have hs := E.stack
    have ho := (E.out (List.mem_of_getElem? hw)).2
    have e : load (store (store (store (store st.mem a (st.vec rv 0) 4) (a + 4) (st.vec rv 1) 4) (a + 8) (st.vec rv 2) 4)
          (a + 12) (st.vec rv 3) 4) ((s0.reg RSP : Int) + o').toNat 8 = load st.mem ((s0.reg RSP : Int) + o').toNat 8 :=
      load_congr _ _ _ _ (fun y h1 h2 => store4_other _ _ _ _ _ _ _ (by omega))
    show ((load (store (store (store (store st.mem a (st.vec rv 0) 4) (a + 4) (st.vec rv 1) 4) (a + 8) (st.vec rv 2) 4)
          (a + 12) (st.vec rv 3) 4) ((s0.reg RSP : Int) + o').toNat 8 : Nat) : Int) = ev ρ v
    rw [e]; exact g3
  mem y hy ho' := by
    show store (store (store (store st.mem a (st.vec rv 0) 4) (a + 4) (st.vec rv 1) 4) (a + 8) (st.vec rv 2) 4) (a + 12) (st.vec rv 3) 4 y = s0.mem y
    have hne : y < a ∨ a + 16 ≤ y := by
      refine Decidable.by_contra fun hin => ?_
      have : ctx.contract.inOut s0 y = true := by
        unfold Contract.inOut
        exact List.any_eq_true.mpr ⟨(name, r, n), List.mem_of_getElem? hw, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
      rw [this] at ho'; cases ho'
    rw [store4_other _ _ _ _ _ _ _ hne]
    exact H.mem y hy ho'
  wrote w' o' v m := by
    obtain ⟨name', r', n', g1, g2, g3, g4⟩ := H.wrote w' o' v m
    refine ⟨name', r', n', g1, g2, g3, ?_⟩
    have ne' : w' ≠ w := by
      intro e
      rw [e] at m
      exact (List.any_eq_false.mp hnw) _ m (by simp)
    have := E.outOut hw g1 (Ne.symm ne')
    show (store (store (store (store st.mem a (st.vec rv 0) 4) (a + 4) (st.vec rv 1) 4) (a + 8) (st.vec rv 2) 4) (a + 12) (st.vec rv 3) 4
      (s0.reg r' + (ev ρ o').toNat) : Int) = ev ρ v
    rw [store4_other _ _ _ _ _ _ _ (by omega)]
    exact g4
  words := by
    refine ⟨H.words.1, ?_, ?_⟩
    · intro w' m x' r' n' g1 k hk'
      obtain ⟨m', ne⟩ := List.mem_filter.mp m
      have ne' : w' ≠ w := by simpa using ne
      have := E.outOut hw g1 (Ne.symm ne')
      show store (store (store (store st.mem a (st.vec rv 0) 4) (a + 4) (st.vec rv 1) 4) (a + 8) (st.vec rv 2) 4) (a + 12) (st.vec rv 3) 4
        (s0.reg r' + k) = s0.mem (s0.reg r' + k)
      rw [store4_other _ _ _ _ _ _ _ (by omega)]
      exact H.words.2.1 w' m' x' r' n' g1 k hk'
    · intro w' j i m x' r' n' g1
      rcases List.mem_append.mp m with m | m
      · obtain ⟨q, mq, eq⟩ := List.mem_map.mp m
        have hq : q < 4 := List.mem_range.mp mq
        injection eq with e1 e2
        injection e2 with e2 e3
        subst e1 e2 e3
        rw [hw] at g1
        injection g1 with g1; injection g1 with _ g1; injection g1 with g1 gn
        subst g1 gn
        refine ⟨by omega, fun b hb => ?_⟩
        show store (store (store (store st.mem a (st.vec rv 0) 4) (a + 4) (st.vec rv 1) 4) (a + 8) (st.vec rv 2) 4) (a + 12) (st.vec rv 3) 4
          (s0.reg r + 4 * (c / 4 + q) + b) = _
        have e : s0.reg r + 4 * (c / 4 + q) + b = a + 4 * q + b := by omega
        rw [e, store4_at _ _ _ _ _ _ hq hb, vec4_getD (f := st.vec rv) hq, hd q hq]
      · obtain ⟨m', keep⟩ := List.mem_filter.mp m
        obtain ⟨g2, g3⟩ := H.words.2.2 w' j i m' x' r' n' g1
        refine ⟨g2, fun b hb => ?_⟩
        show store (store (store (store st.mem a (st.vec rv 0) 4) (a + 4) (st.vec rv 1) 4) (a + 8) (st.vec rv 2) 4) (a + 12) (st.vec rv 3) 4
          (s0.reg r' + 4 * j + b) = _
        have hne : s0.reg r' + 4 * j + b < a ∨ a + 16 ≤ s0.reg r' + 4 * j + b := by
          by_cases e : w' = w
          · subst e
            rw [hw] at g1
            injection g1 with g1; injection g1 with _ g1; injection g1 with g1 gn
            subst g1 gn
            simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at keep
            omega
          · have := E.outOut hw g1 (Ne.symm e)
            omega
        rw [store4_other _ _ _ _ _ _ _ hne]
        exact g3 b hb
  known := H.known

/-! ## A row that sets a vector register, or stores one -/

theorem symVset_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) {s s' : Sym} {place v : Expr}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symStmt ctx bind s (.vset place v) items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (base u : Nat) :
    ∃ ρ' st', Carried ctx s0 ρ s ρ' s' st' ∧ execStmt (ctx.contract.perm s0) bind base u st (.vset place v) = some st' ∧
      st'.rip = st.rip := by
  simp only [symStmt] at h
  cases place with
  | number _ => exact (refuse_ok h).elim
  | lane _ _ => exact (refuse_ok h).elim
  | name n =>
    dsimp only at h
    split at h
    next hn =>
      -- the lanes above the low four: nothing is held of them
      split at h
      next hu =>
        have := V.pure_ok h
        injection this with h1 _
        subst h1
        refine ⟨ρ, { st with vec := fun x k => if k < 4 ∨ 16 ≤ x then st.vec x k else u / W32 ^ (16 * x + k) % W32 },
          ⟨Agree.refl _ _, Nat.le_refl _, ?_, wf⟩, ?_, rfl⟩
        · exact ⟨H.entry, H.reg, H.small, H.zf, H.cf, H.frame, H.facts, H.bytes, H.spec, H.mem, H.wrote,
            ⟨fun x ids hx k hk => by
               show (if k < 4 ∨ 16 ≤ x then st.vec x k else _) = _
               rw [if_pos (Or.inl hk)]; exact H.words.1 x ids hx k hk,
             H.words.2.1, H.words.2.2⟩, H.known⟩
        · simp [execStmt, hn, hu]
      next => exact (refuse_ok h).elim
    next hn =>
      cases hr : vecOf bind n with
      | none => simp only [hr] at h; exact (refuse_ok h).elim
      | some r =>
        simp only [hr] at h
        obtain ⟨⟨l, s1⟩, r1, e1, h⟩ := V.bind_ok h
        obtain ⟨ρ', c, lanes, hl, lt, dn⟩ := symLanes_sound E bind e1 H wf
        dsimp only at h
        split at h
        next hlen =>
          have := V.pure_ok h
          injection this with h1 _
          subst h1
          have len : l.length = 4 := by simpa using hlen
          refine ⟨ρ', setVec st r lanes u, ⟨c.agree, c.mono, ?_, ?_⟩, ?_, rfl⟩
          · exact ⟨c.holds.entry, c.holds.reg, c.holds.small, c.holds.zf, c.holds.cf, c.holds.frame, c.holds.facts, c.holds.bytes,
              c.holds.spec, c.holds.mem, c.holds.wrote,
              ⟨fun x ids hx k hk => by
                 show (if x = r then (if k < 4 then lanes.getD k 0 else _) else st.vec x k) = _
                 rcases lookup_cons_cases hx with ⟨e, e2⟩ | ⟨ne, hx'⟩
                 · rw [if_pos e, if_pos hk, e2]; exact dn k hk
                 · rw [if_neg ne]; exact c.holds.words.1 x ids hx' k hk,
               c.holds.words.2.1, c.holds.words.2.2⟩, c.holds.known⟩
          · exact ⟨c.wf.base, c.wf.reg, c.wf.zf, c.wf.cf, c.wf.frame, c.wf.facts, c.wf.bytes, c.wf.spec, c.wf.wrote,
              ⟨c.wf.words.table, c.wf.words.atoms,
               fun x ids hx => by
                 rcases lookup_cons_cases hx with ⟨e, e2⟩ | ⟨ne, hx'⟩
                 · rw [e2]; exact ⟨len, lt⟩
                 · exact c.wf.words.vec x ids hx',
               c.wf.words.rotrs, c.wf.words.wrote⟩, c.wf.known⟩
          · simp [execStmt, hn, hr, hl]
        next => exact (refuse_ok h).elim
  | call f args =>
    rcases args with _ | ⟨b, _ | ⟨n, _ | ⟨c', more⟩⟩⟩
    · exact (refuse_ok h).elim
    · exact (refuse_ok h).elim
    · dsimp only at h
      split at h
      next hf =>
        cases hl : symVec bind s v <;> cases hx : symReg bind s b <;> cases hk : symNumber bind n <;> simp only [hl, hx, hk] at h
        all_goals try exact (refuse_ok h).elim
        rename_i l x k
        cases hfo : findOut (Lin.add (signed x) (signed (Lin.const k))) ctx.contract.outs 0 with
        | none => simp only [hfo] at h; exact (refuse_ok h).elim
        | some w0 =>
          obtain ⟨w, off, name, r, n', rfl, _, hw, ho⟩ := findOut_spec hfo
          simp only [hfo] at h
          have hw' : ctx.contract.outs[w]? = some (name, r, n') := by simpa using hw
          simp only [hw'] at h
          cases hc : Lin.isConst off with
          | none => simp only [hc] at h; exact (refuse_ok h).elim
          | some c =>
            simp only [hc] at h
            split at h
            next => exact (refuse_ok h).elim
            next hcond =>
              split at h
              next => exact (refuse_ok h).elim
              next hnw =>
                split at h
                next => exact (refuse_ok h).elim
                next hlen =>
                  have := V.pure_ok h
                  injection this with h1 _
                  subst h1
                  have hc3 : 0 ≤ c ∧ c % 4 = 0 ∧ c + 16 ≤ n' := by simpa using hcond
                  have hnw' : (s.wrote.any fun e => e.1 == w) = false := by
                    cases hb : (s.wrote.any fun e => e.1 == w) with
                    | false => rfl
                    | true => exact (hnw hb).elim
                  have len : l.length = 4 := by simpa using hlen
                  obtain ⟨rv, _, lt, hva, hd⟩ := symVec_sound H wf hl
                  obtain ⟨xb, vb, xb_lt, xb_ev, xb_b⟩ := symReg_sound H wf hx
                  obtain ⟨k0, k_lt, vn, _⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) hk
                  have sgx := signed_ev ρ x
                  have sgk := signed_ev ρ (Lin.const k)
                  rw [ev_const] at sgk
                  have hm := List.mem_of_getElem? hw'
                  have hfit := (E.out hm).1
                  have hr : ρ r = s0.reg r := H.entry r (outs_lt hm)
                  have eoff := ev_isConst (ρ := ρ) hc
                  rw [ho, ev_sub, ev_add, ev_var, hr] at eoff
                  have hA : (xb + k.toNat) % M64 = s0.reg r + c.toNat := by
                    unfold M64 at xb_lt hfit ⊢
                    omega
                  have hw1 : allowed (ctx.contract.perm s0).write ((xb + k.toNat) % M64) 16 = true := by
                    apply allowed_of
                    intro y hy1 hy2
                    simp only [Contract.perm, Bool.or_eq_true]
                    right
                    unfold Contract.inOut
                    exact List.any_eq_true.mpr ⟨(name, r, n'), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
                  refine ⟨ρ, _, ⟨Agree.refl _ _, Nat.le_refl _,
                    H.store128 E hw' (c := c.toNat) (by omega) (by omega) hnw' hd ((xb + k.toNat) % M64) hA, ?_⟩, ?_, rfl⟩
                  · exact ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.facts, wf.bytes, wf.spec, wf.wrote,
                      ⟨wf.words.table, wf.words.atoms, wf.words.vec, wf.words.rotrs,
                       fun w' j i m => by
                         rcases List.mem_append.mp m with m | m
                         · obtain ⟨q, mq, eq⟩ := List.mem_map.mp m
                           injection eq with _ e2
                           injection e2 with _ e3
                           rw [← e3]
                           exact lt _ (getD4_mem len (List.mem_range.mp mq))
                         · exact wf.words.wrote w' j i (List.mem_filter.mp m).1⟩, wf.known⟩
                  · simp [execStmt, values_two vb vn, hva, sumList, hw1]
      next => exact (refuse_ok h).elim
    · exact (refuse_ok h).elim

/-- One statement of an effect that the verifier has passed: the machine carries it out, and what the
verifier then holds is so of the machine's state. -/
theorem symStmt_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) {s s' : Sym} {stmt : Stmt}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symStmt ctx bind s stmt items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (base u : Nat) :
    ∃ ρ' st', Carried ctx s0 ρ s ρ' s' st' ∧ execStmt (ctx.contract.perm s0) bind base u st stmt = some st' ∧ st'.rip = st.rip := by
  cases stmt with
  | vset place v => exact symVset_sound E bind h H wf base u
  | vset512 _ _ => simp only [symStmt] at h; exact (refuse_ok h).elim
  | nothing => exact symStmt_scalar E bind h H wf base u (fun _ _ e => by cases e)
  | ret => exact symStmt_scalar E bind h H wf base u (fun _ _ e => by cases e)
  | call t => exact symStmt_scalar E bind h H wf base u (fun _ _ e => by cases e)
  | jump t c => exact symStmt_scalar E bind h H wf base u (fun _ _ e => by cases e)
  | set place v => exact symStmt_scalar E bind h H wf base u (fun _ _ e => by cases e)

end Ode
