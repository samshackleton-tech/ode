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

theorem intern_keeps {P : Node → Prop} {n : Node} {t : Tab} (hT : ∀ (j : Nat) (m : Node), t.list[j]? = some m → P m) (hn : P n) :
    ∀ (j : Nat) (m : Node), (intern n t).2.list[j]? = some m → P m := by
  intro j m h
  rcases intern_list (n := n) (t := t) (t' := (intern n t).2) (i := (intern n t).1) rfl with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e] at h; exact hT j m h
  · rw [e] at h
    by_cases hj : j < t.list.length
    · rw [List.getElem?_append_left hj] at h; exact hT j m h
    · rw [List.getElem?_append_right (by omega)] at h
      cases hk : j - t.list.length with
      | zero => rw [hk] at h; simp at h; rw [← h]; exact hn
      | succ k => rw [hk] at h; simp at h

theorem step_of_made {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {n : Node} {t : Tab} {v : Nat} (ok : TableOk nv t.list)
    (m : Made inp ρ t.list (intern n t).2.list (intern n t).1 v) (ha : ∀ r, n = .atom r → bounded nv r) (hr : ∀ a k, n = .rotr a k → k ≤ 32) :
    Step inp ρ nv t.list (intern n t).2.list (intern n t).1 v :=
  ⟨m.ext,
   ⟨m.wf,
    fun j r h => intern_keeps (P := fun m => ∀ r, m = .atom r → bounded nv r) (fun j m hj r e => ok.atoms j r (e ▸ hj)) ha j _ h r rfl,
    fun j a k h => intern_keeps (P := fun m => ∀ a k, m = .rotr a k → k ≤ 32) (fun j m hj a k e => ok.rotrs j a k (e ▸ hj)) hr j _ h a k rfl⟩,
   m.lt, m.den⟩

theorem bounded_word {nv : Nat} {r : Row} (hb : bounded nv r) : bounded nv (Lin.word r) :=
  Nat.le_trans (strip_length _) (by rw [List.length_map]; exact hb)

theorem bounded_high {nv : Nat} {r : Row} (hb : bounded nv r) : bounded nv (Lin.high r) :=
  Nat.le_trans (strip_length _) (by rw [List.length_map]; exact hb)

theorem wAtom_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {r : Row} (ok : TableOk nv t.list) (hb : bounded nv r) :
    Step inp ρ nv t.list (wAtom r t).2.list (wAtom r t).1 (ev ρ r % W32i).toNat :=
  step_of_made ok (wAtom_made (t' := (wAtom r t).2) (i := (wAtom r t).1) rfl ok.wf)
    (fun r' e => by injection e with e; rw [← e]; exact bounded_word hb) (fun a k e => by cases e)

theorem wAdd_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {a b : Nat} (ok : TableOk nv t.list)
    (ha : a < t.list.length) (hb : b < t.list.length) :
    Step inp ρ nv t.list (wAdd a b t).2.list (wAdd a b t).1 ((den inp ρ t.list a + den inp ρ t.list b) % W32) :=
  step_of_made ok (wAdd_made (t' := (wAdd a b t).2) (i := (wAdd a b t).1) rfl ok.wf ha hb) (fun r e => by cases e) (fun a k e => by cases e)

theorem wXor_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {a b : Nat} (ok : TableOk nv t.list)
    (ha : a < t.list.length) (hb : b < t.list.length) :
    Step inp ρ nv t.list (wXor a b t).2.list (wXor a b t).1 (den inp ρ t.list a ^^^ den inp ρ t.list b) :=
  step_of_made ok (wXor_made (t' := (wXor a b t).2) (i := (wXor a b t).1) rfl ok.wf ha hb) (fun r e => by cases e) (fun a k e => by cases e)

theorem wAnd_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {a b : Nat} (ok : TableOk nv t.list)
    (ha : a < t.list.length) (hb : b < t.list.length) :
    Step inp ρ nv t.list (wAnd a b t).2.list (wAnd a b t).1 (den inp ρ t.list a &&& den inp ρ t.list b) :=
  step_of_made ok (wAnd_made (t' := (wAnd a b t).2) (i := (wAnd a b t).1) rfl ok.wf ha hb) (fun r e => by cases e) (fun a k e => by cases e)

theorem wUlt_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {a b : Nat} (ok : TableOk nv t.list)
    (ha : a < t.list.length) (hb : b < t.list.length) :
    Step inp ρ nv t.list (wUlt a b t).2.list (wUlt a b t).1 (if den inp ρ t.list a < den inp ρ t.list b then 1 else 0) := by
  unfold wUlt
  split
  next e =>
    subst e
    have z := wAtom_step (inp := inp) (ρ := ρ) (t := t) ok (bounded_const nv 0)
    simpa [ev_const] using z
  next ne =>
    exact step_of_made ok
      (made (inp := inp) (ρ := ρ) (n := .ult a b) (t := t) (t' := (intern (.ult a b) t).2) (i := (intern (.ult a b) t).1) rfl ok.wf (by
        intro j mj
        simp only [Node.parts, List.mem_cons, List.mem_nil_iff, or_false] at mj
        rcases mj with mj | mj <;> (rw [mj]; assumption)))
      (fun r e => by cases e) (fun a k e => by cases e)

theorem wSel_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {m a b : Nat} (ok : TableOk nv t.list)
    (hm : m < t.list.length) (ha : a < t.list.length) (hb : b < t.list.length) :
    Step inp ρ nv t.list (wSel m a b t).2.list (wSel m a b t).1
      (if den inp ρ t.list m = 0 then den inp ρ t.list b else den inp ρ t.list a) := by
  unfold wSel
  split
  next e =>
    have el : t.list[m]? = some (.atom (Lin.word (Lin.const 0))) := by simpa [Tab.list] using e
    have dm : den inp ρ t.list m = 0 := by
      rw [den_node ok.wf el]
      simp [Node.value, ev_word, ev_const]
    rw [if_pos dm]
    exact ⟨Ext.refl _, ok, hb, rfl⟩
  next ne =>
    exact step_of_made ok
      (made (inp := inp) (ρ := ρ) (n := .sel m a b) (t := t) (t' := (intern (.sel m a b) t).2) (i := (intern (.sel m a b) t).1) rfl ok.wf (by
        intro j mj
        simp only [Node.parts, List.mem_cons, List.mem_nil_iff, or_false] at mj
        rcases mj with mj | mj | mj <;> (rw [mj]; assumption)))
      (fun r e => by cases e) (fun a k e => by cases e)

theorem wAddConst_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {a k : Nat} (ok : TableOk nv t.list)
    (ha : a < t.list.length) (hinp : ∀ j k, inp j k < W32) :
    Step inp ρ nv t.list (wAddConst a k t).2.list (wAddConst a k t).1 ((den inp ρ t.list a + k) % W32) := by
  unfold wAddConst
  split
  next k0 =>
    subst k0
    rw [Nat.add_zero, Nat.mod_eq_of_lt (den_lt ok.wf hinp ok.rotrs a)]
    exact ⟨Ext.refl _, ok, ha, rfl⟩
  next kn =>
    split
    next r e =>
      have el : t.list[a]? = some (.atom r) := by simpa [Tab.list] using e
      have z := wAtom_step (inp := inp) (ρ := ρ) (t := t) (r := Lin.add r (Lin.const k)) ok
        (bounded_add (ok.atoms a r el) (bounded_const nv k))
      have da : den inp ρ t.list a = (ev ρ r % W32i).toNat := by rw [den_node ok.wf el]; rfl
      have e2 : (ev ρ (Lin.add r (Lin.const k)) % W32i).toNat = ((ev ρ r % W32i).toNat + k) % W32 := by
        rw [ev_add, ev_const]
        unfold W32i W32
        omega
      rw [da, ← e2]; exact z
    next =>
      have s1 := wAtom_step (inp := inp) (ρ := ρ) (t := t) (r := Lin.const k) ok (bounded_const nv k)
      have s2 := wAdd_step (inp := inp) (ρ := ρ) (t := (wAtom (Lin.const k) t).2) (a := a) (b := (wAtom (Lin.const k) t).1) s1.ok
        (Nat.lt_of_lt_of_le ha s1.ext.le) s1.lt
      refine ⟨s1.ext.trans s2.ext, s2.ok, s2.lt, ?_⟩
      rw [s2.den, den_ext ok.wf s1.ext ha, s1.den, ev_const]
      unfold W32i W32
      omega

theorem wRotr_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {a n : Nat} (ok : TableOk nv t.list)
    (ha : a < t.list.length) (hn : n ≤ 32) :
    Step inp ρ nv t.list (wRotr a n t).2.list (wRotr a n t).1 (rotr (den inp ρ t.list a) n) :=
  step_of_made ok (wRotr_made (t' := (wRotr a n t).2) (i := (wRotr a n t).1) rfl ok.wf ha) (fun r e => by cases e)
    (fun a k e => by injection e with _ e; rw [← e]; exact hn)

theorem input_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {j k : Nat} (ok : TableOk nv t.list) :
    Step inp ρ nv t.list (intern (.input j k) t).2.list (intern (.input j k) t).1 (inp j k) :=
  step_of_made ok (made (t' := (intern (.input j k) t).2) (i := (intern (.input j k) t).1) rfl ok.wf (by intro x mx; simp [Node.parts] at mx))
    (fun r e => by cases e) (fun a k e => by cases e)

/-- The terms made for a list, one after another: each is what it is to be (`val`), in the table at the end. -/
theorem termsOf_step {α : Type} {mk : α → Tab → Nat × Tab} {val : α → Nat} {inp : Nat → Nat → Nat} {ρ : Nat → Int}
    {nv : Nat} {T0 : List Node} :
    ∀ (xs : List α) (T : Tab), (∀ a ∈ xs, ∀ T : Tab, Ext T0 T.list → TableOk nv T.list → Step inp ρ nv T.list (mk a T).2.list (mk a T).1 (val a)) →
      Ext T0 T.list → TableOk nv T.list →
      Ext T.list (termsOf mk xs T).2.list ∧ TableOk nv (termsOf mk xs T).2.list ∧ (termsOf mk xs T).1.length = xs.length ∧
      (∀ i ∈ (termsOf mk xs T).1, i < (termsOf mk xs T).2.list.length) ∧
      ∀ k (hk : k < xs.length), den inp ρ (termsOf mk xs T).2.list ((termsOf mk xs T).1.getD k 0) = val xs[k]
  | [], T, _, _, ok => ⟨Ext.refl T.list, ok, rfl, (fun i m => nomatch m), (fun k hk => absurd hk (Nat.not_lt_zero k))⟩
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
        show den inp ρ (termsOf mk as (mk a T).2).2.list (mk a T).1 = val a
        rw [den_ext S.ok.wf e2 S.lt]; exact S.den
      | succ k => exact dn k (by simpa using hk)

/-! ## The state, with more terms -/

theorem Holds.terms {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    {t' : Tab} (e : Ext s.terms t'.list) : Holds ctx s0 ρ { s with tab := t' } st :=
  ⟨H.entry, H.data, H.reg, H.small, H.zf, H.cf, H.frame,
   fun o i m => by
     obtain ⟨h1, h2, h3⟩ := H.frameW o i m
     exact ⟨h1, h2, h3.trans (den_ext wf.words.table e (wf.frameW o i m)).symm⟩,
   H.facts, H.bytes, H.spec, H.mem, H.wrote,
   ⟨fun x ids hx k hk => by
      have lt := (wf.words.vec x ids hx).2
      have eq : ids.getD k 0 = ids[k] := by simp [List.getD, List.getElem?_eq_getElem hk]
      show st.vec x k = den (inpOf ctx s0) ρ t'.list (ids.getD k 0)
      rw [den_ext wf.words.table e (by rw [eq]; exact lt _ (List.getElem_mem hk))]
      exact H.words.vec x ids hx k hk,
    H.words.intact,
    fun w j i m x r n ho => by
      obtain ⟨h1, h2⟩ := H.words.wrote w j i m x r n ho
      refine ⟨h1, fun b hb => ?_⟩
      show st.mem _ = den (inpOf ctx s0) ρ t'.list i / 256 ^ b % 256
      rw [den_ext wf.words.table e (wf.words.wrote w j i m)]
      exact h2 b hb,
    fun o ids hs => ⟨(H.words.spill o ids hs).1, fun k hk => by
      have lt := (wf.words.spill o ids hs).2.2
      have hc : ids.getD k 0 = ids[k] := by simp [List.getD, List.getElem?_eq_getElem hk]
      show Ode.load st.mem _ 4 = den (inpOf ctx s0) ρ t'.list (ids.getD k 0)
      rw [den_ext wf.words.table e (by rw [hc]; exact lt _ (List.getElem_mem hk))]
      exact (H.words.spill o ids hs).2 k hk⟩⟩,
   fun k m => Known.holds_mono (wf.known k m) (Agree.refl _ _) wf.words.table wf.words.atoms e (H.known k m), H.range, H.vecIntact⟩

theorem WF.terms {s : Sym} (wf : WF ctx s) {t' : Tab} (e : Ext s.terms t'.list) (ok : TableOk s.nvars t'.list) : WF ctx { s with tab := t' } :=
  ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame,
   fun o i m => Nat.lt_of_lt_of_le (wf.frameW o i m) e.le,
   wf.facts, wf.bytes, wf.spec, wf.wrote,
   ⟨ok.wf, ok.atoms, fun x ids h => ⟨(wf.words.vec x ids h).1, fun i mi => Nat.lt_of_lt_of_le ((wf.words.vec x ids h).2 i mi) e.le⟩,
    ok.rotrs, fun w j i h => Nat.lt_of_lt_of_le (wf.words.wrote w j i h) e.le,
    fun o ids hs => by
      obtain ⟨bo, len, lt⟩ := wf.words.spill o ids hs
      exact ⟨bo, len, fun i mi => Nat.lt_of_lt_of_le (lt i mi) e.le⟩⟩,
   fun k m => Known.wf_mono (Nat.le_refl _) e.le (wf.known k m), wf.range⟩

theorem Carried.terms {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    {t' : Tab} (e : Ext s.terms t'.list) (ok : TableOk s.nvars t'.list) : Carried ctx s0 ρ s ρ { s with tab := t' } st :=
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
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (h : symVec bind s e = some l) :
    ∃ r, l.length = 4 ∧ (∀ i ∈ l, i < s.terms.length) ∧ vecArg bind st e = some [st.vec r 0, st.vec r 1, st.vec r 2, st.vec r 3] ∧
      ∀ k, k < 4 → st.vec r k = den (inpOf ctx s0) ρ s.terms (l.getD k 0) := by
  cases e with
  | name n =>
    simp only [symVec] at h
    cases hv : vecOf bind n with
    | none => simp [hv] at h
    | some r =>
      simp only [hv, Option.bind_some] at h
      cases hi : s.vec.lookup r with
      | none => simp [hi] at h
      | some ids =>
        simp only [hi, Option.map_some, Option.some.injEq] at h
        subst l
        obtain ⟨len, lt⟩ := wf.words.vec r ids hi
        refine ⟨r, by rw [List.length_take]; omega, fun i m => lt i (List.mem_of_mem_take m), by simp only [vecArg, hv]; rfl, ?_⟩
        intro k hk
        have dn := H.words.vec r ids hi k (by omega)
        simpa only [List.getD, List.getElem?_take_of_lt hk] using dn
  | number _ => simp [symVec] at h
  | lane _ _ => simp [symVec] at h
  | call _ _ => simp [symVec] at h

theorem symLane_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} {bind : Bind} {e : Expr} {i : Nat}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (h : symLane bind s e = some i) :
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
          have len := (wf.words.vec r l hl).1
          rw [← e]; exact H.words.vec r l hl k (by omega)
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
        have hne : (n == "xmm0") = false := by
          unfold isNumberLetter at hl
          cases h0 : (n == "xmm0")
          · rfl
          · have : n = "xmm0" := by simpa using h0
            subst this; simp at hl
        simp [vecArg, vecOf, hne, number_not_vector hl]
    next => cases h
  | lane _ _ => simp [symNumber] at h
  | call _ _ => simp [symNumber] at h

/-- A general register in an EFFECT: the machine's number in it is the row's. -/
theorem symReg_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} {bind : Bind} {e : Expr} {x : Row}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (h : symReg ctx bind s e = some x) :
    ∃ xa, value (ctx.contract.perm ctx.pieces s0) bind st e = some xa ∧ xa < M64 ∧ (xa : Int) = ev ρ x ∧ bounded s.nvars x := by
  cases e with
  | name n =>
    simp only [symReg] at h
    split at h
    next => cases h
    next hl =>
      cases hr : ctx.regOf bind n with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.map_some] at h
        injection h with h; subst h
        obtain ⟨hr', lt⟩ := Ctx.regOf_some hr
        exact ⟨st.reg r, by simp [value, hl, hr'], H.small r, H.reg r lt, wf.reg r lt⟩
  | number _ => simp [symReg] at h
  | lane _ _ => simp [symReg] at h
  | call _ _ => simp [symReg] at h

theorem wordAddress_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {bind : Bind} {b n : Expr} {x : Row} {k : Int}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hx : symReg ctx bind s b = some x) (hk : symNumber bind n = some k) :
    ∃ xb, values (ctx.contract.perm ctx.pieces s0) bind st [b, n] = some [xb, k.toNat] ∧
      ∀ A : Nat, (A : Int) = ev ρ (Lin.add (signed x) (signed (Lin.const k))) → A < M64 → (xb + k.toNat) % M64 = A := by
  obtain ⟨xb, vb, xb_lt, xb_ev, _⟩ := symReg_sound H wf hx
  obtain ⟨k0, k_lt, vn, _⟩ := symNumber_sound (perm := ctx.contract.perm ctx.pieces s0) (st := st) hk
  refine ⟨xb, values_two vb vn, ?_⟩
  have sgx := signed_ev ρ x
  have sgk := signed_ev ρ (Lin.const k)
  rw [ev_const] at sgk
  intro A hA hlt
  rw [ev_add] at hA
  unfold M64 at xb_lt hlt ⊢
  omega

theorem symWordAddr_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {bind : Bind} {args : List Expr} {addr : Row}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (h : symWordAddr ctx bind s args = some addr) :
    ∃ vs, values (ctx.contract.perm ctx.pieces s0) bind st args = some vs ∧ bounded s.nvars addr ∧
      ∀ A : Nat, (A : Int) = ev ρ addr → A < M64 → sumList vs % M64 = A := by
  rcases args with _ | ⟨b, _ | ⟨n, _ | ⟨i, _ | ⟨_, _⟩⟩⟩⟩
  · simp [symWordAddr] at h
  · simp [symWordAddr] at h
  · cases hx : symReg ctx bind s b <;> cases hk : symNumber bind n <;> simp [symWordAddr, hx, hk] at h
    subst addr
    obtain ⟨xb, vs, ha⟩ := wordAddress_sound H wf hx hk
    obtain ⟨_, _, _, _, bx⟩ := symReg_sound H wf hx
    exact ⟨_, vs, bounded_add (bounded_signed bx) (bounded_signed (bounded_const _ _)),
      by simpa only [sumList, Nat.add_zero] using ha⟩
  · cases hx : symReg ctx bind s b <;> cases hk : symNumber bind n <;> cases hy : symReg ctx bind s i <;> simp [symWordAddr, hx, hk, hy] at h
    subst addr
    rename_i x k y
    obtain ⟨xb, vb, xb_lt, xb_ev, bx⟩ := symReg_sound H wf hx
    obtain ⟨yb, vi, yb_lt, yb_ev, by'⟩ := symReg_sound H wf hy
    obtain ⟨k0, k_lt, vn, _⟩ := symNumber_sound (perm := ctx.contract.perm ctx.pieces s0) (st := st) hk
    refine ⟨[xb, k.toNat, yb], by simp [values, vb, vn, vi],
      bounded_add (bounded_add (bounded_signed bx) (bounded_signed (bounded_const _ _))) (bounded_signed by'), ?_⟩
    have sgx := signed_ev ρ x
    have sgy := signed_ev ρ y
    have sgk := signed_ev ρ (Lin.const k)
    rw [ev_const] at sgk
    intro A hA hlt
    simp only [ev_add] at hA
    simp only [sumList, Nat.add_zero]
    unfold M64 at xb_lt yb_lt hlt ⊢
    omega
  · simp [symWordAddr] at h

/-! ## Read a run of words -/

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

/-- The terms for a load stand for the words in memory when those bytes still have their entry values. -/
theorem loadWords_terms {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    {j : Nat} {x : String} {r n c width : Nat} (hj : ctx.contract.wordRuns[j]? = some (x, r, n))
    (hmem : ∀ k, k < 4 * width → st.mem (s0.reg r + c + k) = s0.mem (s0.reg r + c + k)) (hc : c % 4 = 0) :
    let made := termsOf intern ((List.range width).map fun i => Node.input j (c / 4 + i)) s.tab
    Carried ctx s0 ρ s ρ { s with tab := made.2 } st ∧ made.1.length = width ∧
    (∀ i ∈ made.1, i < made.2.list.length) ∧
    ∀ k, k < width → load st.mem (s0.reg r + c + 4 * k) 4 = den (inpOf ctx s0) ρ made.2.list (made.1.getD k 0) := by
  dsimp only
  obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := intern)
    (val := fun nd => match nd with | .input j k => inpOf ctx s0 j k | _ => 0)
    (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) ((List.range width).map fun i => Node.input j (c / 4 + i)) s.tab
    (by
      intro a ma T eT okT
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ma
      exact input_step okT)
    (Ext.refl _) wf.words.ok
  refine ⟨Carried.terms H wf e ok, by simpa using len, lt, ?_⟩
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

/-- Eight bytes are two words: the low one and 2^32 times the high one. -/
theorem load_halves_vec (mem : Nat → Byte) (a : Nat) : load mem a 8 = load mem a 4 + 4294967296 * load mem (a + 4) 4 := by
  simp only [load, Nat.add_assoc, Nat.reduceAdd]
  omega

theorem frameCellWords_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (wf : WF ctx s) {o : Int} {lo hi : Row} (h : frameCellWords s o = some (lo, hi)) :
    -(ctx.contract.stackAt s0 : Int) ≤ o ∧ o + 8 ≤ 0 ∧
    bounded s.nvars lo ∧ bounded s.nvars hi ∧
    (load st.mem ((s0.reg RSP : Int) + o).toNat 4 : Int) = ev ρ lo % W32i ∧
    (load st.mem (((s0.reg RSP : Int) + o).toNat + 4) 4 : Int) = ev ρ hi % W32i := by
  have h4 : (256 : Nat) ^ 4 = 4294967296 := by decide
  unfold frameCellWords at h
  cases hf : s.frame.find? (fun cell => cell.1 == o) with
  | none => simp [hf] at h
  | some p =>
    obtain ⟨o', x⟩ := p
    simp only [hf] at h
    split at h
    next hk =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hm := List.mem_of_find?_eq_some hf
      have ho : o' = o := by have := List.find?_some hf; simpa using this
      subst ho
      obtain ⟨g1, g2, g3⟩ := H.frame _ _ hm
      have bx : bounded s.nvars x := wf.frame _ _ hm
      have bh : bounded s.nvars (Lin.high x) := bounded_high bx
      have hk' : knownNonneg s (Lin.word x) = true ∧ plain s.facts (Lin.sub (Lin.const (W32i - 1)) (Lin.word x)) = true := by
        simpa using hk
      have h0 := knownNonneg_sound H hk'.1
      have h1 := plain_sound hk'.2 ρ H.facts
      simp only [ev_sub, ev_const] at h1
      have eh := ev_high ρ x
      have e := load_halves_vec st.mem ((s0.reg RSP : Int) + o').toNat
      have lt1 := load_lt st.mem ((s0.reg RSP : Int) + o').toNat 4
      have lt2 := load_lt st.mem (((s0.reg RSP : Int) + o').toNat + 4) 4
      rw [h4] at lt1 lt2
      refine ⟨g1, g2, bx, bh, ?_, ?_⟩
      · rw [e] at g3; rw [← g3]; unfold W32i; omega
      · rw [e] at g3; unfold W32i at h1 eh ⊢; omega
    next => simp at h

theorem framePairRows_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (wf : WF ctx s) (hst : ctx.contract.stackAt s0 ≤ s0.reg RSP) :
    ∀ (pairs : Nat) (o : Int) {rows : List Row}, framePairRows s o pairs = some rows →
      rows.length = 2 * pairs ∧
      (∀ r ∈ rows, bounded s.nvars r) ∧
      ∀ k, k < 2 * pairs →
        -(ctx.contract.stackAt s0 : Int) ≤ o + 4 * (k : Int) ∧ o + 4 * (k : Int) + 4 ≤ 0 ∧
        (load st.mem (((s0.reg RSP : Int) + o).toNat + 4 * k) 4 : Int) = ev ρ (rows.getD k (Lin.const 0)) % W32i
  | 0, o, rows, h => by
    simp only [framePairRows, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun _ m => absurd m (by simp), fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | pairs + 1, o, rows, h => by
    simp only [framePairRows] at h
    cases hc : frameCellWords s o with
    | none => simp [hc] at h
    | some lh =>
      obtain ⟨lo, hi⟩ := lh
      cases hr : framePairRows s (o + 8) pairs with
      | none => simp [hc, hr] at h
      | some rest =>
        simp only [hc, hr, Option.some.injEq] at h; subst h
        obtain ⟨g1, g2, blo, bhi, hlo, hhi⟩ := frameCellWords_sound H wf hc
        obtain ⟨rlen, rbd, rmem⟩ := framePairRows_sound H wf hst pairs (o + 8) hr
        refine ⟨by simp [rlen]; omega, ?_, ?_⟩
        · intro r mr
          rcases List.mem_cons.mp mr with rfl | mr
          · exact blo
          · rcases List.mem_cons.mp mr with rfl | mr
            · exact bhi
            · exact rbd r mr
        · intro k hk
          match k with
          | 0 => refine ⟨by omega, by omega, by simpa using hlo⟩
          | 1 => refine ⟨by omega, by omega, by simpa using hhi⟩
          | k + 2 =>
            obtain ⟨m1, m2, m3⟩ := rmem k (by omega)
            have e1 : ((s0.reg RSP : Int) + (o + 8)).toNat + 4 * k = ((s0.reg RSP : Int) + o).toNat + 4 * (k + 2) := by omega
            rw [e1] at m3
            refine ⟨by omega, by omega, ?_⟩
            simpa [List.getD] using m3

theorem frameWIds_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hstack : ctx.contract.stackAt s0 ≤ s0.reg RSP) :
    ∀ (count k : Nat) (o : Int) {ids : List Nat}, frameWIds s.frameW o count k = some ids →
      ids.length = count ∧ (∀ i ∈ ids, i < s.terms.length) ∧
      ∀ j, j < count → -(ctx.contract.stackAt s0 : Int) ≤ o + 4 * ((k + j : Nat) : Int) ∧
        o + 4 * ((k + j : Nat) : Int) + 4 ≤ 0 ∧
        load st.mem (((s0.reg RSP : Int) + o + 4 * (k : Int)).toNat + 4 * j) 4 =
          den (inpOf ctx s0) ρ s.terms (ids.getD j 0)
  | 0, _, _, ids, h => by
    simp only [frameWIds, Option.some.injEq] at h; subst h
    exact ⟨rfl, (fun _ m => by cases m), fun _ hj => by omega⟩
  | count + 1, k, o, ids, h => by
    simp only [frameWIds] at h
    cases hf : s.frameW.find? (fun e => e.1 == o + 4 * (k : Int)) with
    | none => simp only [hf] at h; cases h
    | some p =>
      cases hr : frameWIds s.frameW o count (k + 1) with
      | none => simp only [hf, hr] at h; cases h
      | some rest =>
        simp only [hf, hr, Option.some.injEq] at h; subst h
        have hmem := List.mem_of_find?_eq_some hf
        have heq : p.1 = o + 4 * (k : Int) := by simpa using List.find?_some hf
        obtain ⟨h1, h2, h3⟩ := H.frameW p.1 p.2 hmem
        have hlt := wf.frameW p.1 p.2 hmem
        obtain ⟨rlen, rlt, rmem⟩ := frameWIds_sound H wf hstack count (k + 1) o hr
        refine ⟨by simp [rlen], fun i mi => ?_, fun j hj => ?_⟩
        · rcases List.mem_cons.mp mi with rfl | mi
          · exact hlt
          · exact rlt i mi
        · cases j with
          | zero =>
            simp only [Nat.add_zero, Nat.mul_zero, List.getD, List.getElem?_cons_zero, Option.getD_some]
            rw [heq] at h1 h2 h3
            refine ⟨by omega, by omega, ?_⟩
            have e : ((s0.reg RSP : Int) + o + 4 * (k : Int)).toNat = ((s0.reg RSP : Int) + (o + 4 * (k : Int))).toNat := by omega
            rw [e]; exact h3
          | succ j =>
            obtain ⟨b1, b2, b3⟩ := rmem j (by omega)
            have ek : k + (j + 1) = k + 1 + j := by omega
            rw [ek]
            refine ⟨b1, b2, ?_⟩
            have e : ((s0.reg RSP : Int) + o + 4 * (k : Int)).toNat + 4 * (j + 1) =
                     ((s0.reg RSP : Int) + o + 4 * ((k + 1 : Nat) : Int)).toNat + 4 * j := by omega
            rw [e]
            simpa only [List.getD, List.getElem?_cons_succ] using b3

theorem findValArray_spec {addr : Row} : ∀ (vas : List (String × Nat × Nat × Nat × Nat)) (start k : Nat)
    {x : String} {r l ch el : Nat} {c : Int},
    findValArray addr vas start = some (k, x, r, l, ch, el, c) →
    start ≤ k ∧ vas[k - start]? = some (x, r, l, ch, el) ∧ Lin.isConst (Lin.sub addr (Lin.var r)) = some c ∧ 0 ≤ c ∧ c % 4 = 0
  | [], _, _, _, _, _, _, _, _, h => by simp [findValArray] at h
  | (x0, r0, l0, ch0, el0) :: more, start, k, x, r, l, ch, el, c, h => by
    simp only [findValArray] at h
    cases hc : Lin.isConst (Lin.sub addr (Lin.var r0)) with
    | none =>
      simp only [hc] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := findValArray_spec more (start + 1) k h
      refine ⟨by omega, ?_, h3, h4, h5⟩
      have hs : k - start = (k - (start + 1)) + 1 := by omega
      rw [hs]; exact h2
    | some c0 =>
      simp only [hc] at h
      split at h
      next hok =>
        injection h with h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨Nat.le_refl _, by simp, hc, hok.1, hok.2⟩
      next =>
        obtain ⟨h1, h2, h3, h4, h5⟩ := findValArray_spec more (start + 1) k h
        refine ⟨by omega, ?_, h3, h4, h5⟩
        have hs : k - start = (k - (start + 1)) + 1 := by omega
        rw [hs]; exact h2

private theorem symLoadValArray_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s1 : Sym}
    {addr : Row} {l : List Nat} {width : Nat} {items rest : Items} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (a : Nat)
    (ha : ∀ A : Nat, (A : Int) = ev ρ addr → A < M64 → a = A)
    (h : (match findValArray addr ctx.contract.valArrays 0 with
      | some (k, _, _, lenR, ch, el, c) =>
        let i := c.toNat / el
        if 0 < ch ∧ 0 < el ∧ el % 4 = 0 ∧ c.toNat + 4 * width ≤ el * (i + 1) then do
          entail s.facts (Lin.sub (Lin.var lenR) (Lin.const ((i + 1) * ch)))
          let j := ctx.contract.fixeds.length + ctx.contract.inouts.length + ctx.contract.regions.length + k
          let made := termsOf intern ((List.range width).map fun m => Node.input j (c.toNat / 4 + m)) s.tab
          pure (made.1, { s with tab := made.2 })
        else refuse (if width = 4 then "sixteen bytes that are not four words of the run"
                     else if width = 1 then "four bytes that are not a word of the run"
                     else "sixty-four bytes that are not sixteen words of the run")
      | none => refuse s!"{if width = 4 then "sixteen" else if width = 1 then "four" else "sixty-four"} bytes that are of no run of words given to read") items = .ok ((l, s1), rest)) :
    allowed (ctx.contract.perm ctx.pieces s0).read a (4 * width) = true ∧ Carried ctx s0 ρ s ρ s1 st ∧ l.length = width ∧
    (∀ i ∈ l, i < s1.terms.length) ∧
    ∀ k, k < width → load st.mem (a + 4 * k) 4 = den (inpOf ctx s0) ρ s1.terms (l.getD k 0) := by
  cases hva : findValArray addr ctx.contract.valArrays 0 with
  | none => simp only [hva] at h; exact (refuse_ok h).elim
  | some va =>
    obtain ⟨k, x, r, lenR, ch, el, c⟩ := va
    simp only [hva] at h
    split at h
    next hcond =>
      obtain ⟨hch, hel, hel4, hwi⟩ := hcond
      obtain ⟨_, hk, hc, hc0, hc4⟩ := findValArray_spec ctx.contract.valArrays 0 k hva
      have hk' : ctx.contract.valArrays[k]? = some (x, r, lenR, ch, el) := by simpa using hk
      have hm := List.mem_of_getElem? hk'
      obtain ⟨hr_lt, hl_lt, _, _, _⟩ := valArrays_lt hm
      obtain ⟨va1, va2, va3⟩ := E.valArray hm
      obtain ⟨_, _, he, hp⟩ := V.bind_ok h
      have hlen_ge := entail_sound he ρ H.facts
      rw [ev_sub, ev_var, ev_const, H.entry lenR hl_lt] at hlen_ge
      have hi_lt : c.toNat / el + 1 ≤ s0.reg lenR / ch := by
        have h1 : (c.toNat / el + 1) * ch ≤ s0.reg lenR := by
          have h0 : (((c.toNat / el + 1) * ch : Nat) : Int) = (↑(c.toNat / el) + 1) * ↑ch := by
            rw [Int.natCast_mul, Int.natCast_add]; rfl
          omega
        exact (Nat.le_div_iff_mul_le hch).mpr h1
      have hbytes : c.toNat + 4 * width ≤ el * (s0.reg lenR / ch) := by
        have := Nat.mul_le_mul_left el hi_lt
        omega
      have := V.pure_ok hp
      injection this with h1 _
      injection h1 with h1 h2
      subst h1 h2
      have hr : ρ r = s0.reg r := H.entry r hr_lt
      have eoff := ev_isConst (ρ := ρ) hc
      rw [ev_sub, ev_var, hr] at eoff
      have hA : a = s0.reg r + c.toNat := ha (s0.reg r + c.toNat) (by omega) (by unfold M64 at va1 ⊢; omega)
      have hmem : ∀ m, m < 4 * width → st.mem (s0.reg r + c.toNat + m) = s0.mem (s0.reg r + c.toNat + m) := by
        intro m hm'
        apply H.mem
        · simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
        · unfold Contract.inOut
          rw [List.any_eq_false]
          intro ⟨x', r', n'⟩ hm2
          have := va3 x' r' n' hm2
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
      obtain ⟨cr, len, lt, dn⟩ := loadWords_terms (ρ := ρ) H wf (wordRuns_of_valArray hk') hmem (by omega)
      refine ⟨allowed_of _ _ _ ?_, cr, len, lt, ?_⟩
      · intro y hy1 hy2
        simp only [Contract.perm, Bool.or_eq_true]
        left; right
        unfold Contract.inValArray
        exact List.any_eq_true.mpr ⟨(x, r, lenR, ch, el), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
      · intro m hm'
        rw [hA]; exact dn m hm'
    next => exact (refuse_ok h).elim

theorem symLoadWords_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s1 : Sym} {addr : Row} {l : List Nat}
    {items rest : Items} {ρ : Nat → Int} {st : State} {width : Nat}
    (h : symLoadWords ctx s addr width items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (nonempty : 0 < width) (a : Nat)
    (ha : ∀ A : Nat, (A : Int) = ev ρ addr → A < M64 → a = A) :
    allowed (ctx.contract.perm ctx.pieces s0).read a (4 * width) = true ∧ Carried ctx s0 ρ s ρ s1 st ∧ l.length = width ∧
    (∀ i ∈ l, i < s1.terms.length) ∧
    ∀ k, k < width → load st.mem (a + 4 * k) 4 = den (inpOf ctx s0) ρ s1.terms (l.getD k 0) := by
  simp only [symLoadWords] at h
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
        obtain ⟨f1, f2, f3, f4⟩ := E.fixedAt hm
        have hr : ρ r = s0.reg r := H.entry r (fixeds_lt hm)
        have eoff := ev_isConst (ρ := ρ) hc
        rw [ho, ev_sub, ev_var, hr] at eoff
        have hA : a = s0.reg r + c.toNat := ha (s0.reg r + c.toNat) (by omega) (by unfold M64 at f1 ⊢; omega)
        have hjj : (ctx.contract.fixeds ++ ctx.contract.inouts)[j]? = some (x, r, n) := by
          rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj').1]; exact hj'
        have hstack := E.stack
        have hmem : ∀ k, k < 4 * width → st.mem (s0.reg r + c.toNat + k) = s0.mem (s0.reg r + c.toNat + k) := by
          intro k hk
          apply H.mem
          · simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
          · unfold Contract.inOut
            rw [List.any_eq_false]
            intro ⟨x', r', n'⟩ hm'
            have := f4 x' r' n' hm'
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            omega
        obtain ⟨cr, len, lt, dn⟩ := loadWords_terms (ρ := ρ) H wf (wordRuns_of hjj) hmem (by omega)
        refine ⟨allowed_of _ _ _ ?_, cr, len, lt, ?_⟩
        · intro y hy1 hy2
          simp only [Contract.perm, Bool.or_eq_true]
          left; left; left; right
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
    | none =>
      simp only [hf2] at h
      cases hc : Lin.isConst (Lin.sub addr (Lin.var RSP)) with
      | none => simp only [hc] at h; exact symLoadValArray_sound E H wf a ha h
      | some o =>
        cases hsp : s.sp with
        | none => simp only [hc, hsp] at h; exact symLoadValArray_sound E H wf a ha h
        | some sp =>
          simp only [hc, hsp] at h
          split at h
          next hcond =>
            obtain ⟨hso, ho0⟩ := hcond
            cases hpr : (if width % 2 = 0 then framePairRows s o (width / 2) else none) with
            | none =>
              simp only [hpr] at h
              cases hfw : frameWIds s.frameW o width 0 with
              | none => simp only [hfw] at h; exact (refuse_ok h).elim
              | some fids =>
                simp only [hfw] at h
                have := V.pure_ok h
                injection this with h1 _
                injection h1 with h1 h2
                subst h1 h2
                obtain ⟨flen, flt, fmem⟩ := frameWIds_sound H wf E.stackAt width 0 o hfw
                have hbound0 : -(ctx.contract.stackAt s0 : Int) ≤ o := by
                  have := (fmem 0 nonempty).1; omega
                have hrsp : ρ RSP = s0.reg RSP := H.entry RSP (by unfold Ctx.nreg Contract.regs RSP; split <;> omega)
                have eoff := ev_isConst (ρ := ρ) hc
                rw [ev_sub, ev_var, hrsp] at eoff
                have hsmall := E.small RSP
                have hstack := E.stackAt
                have hA : a = ((s0.reg RSP : Int) + o).toNat := ha ((s0.reg RSP : Int) + o).toNat (by omega) (by unfold M64 at hsmall ⊢; omega)
                refine ⟨allowed_of _ _ _ ?_, ⟨Agree.refl _ _, Nat.le_refl _, H, wf⟩, flen, flt, ?_⟩
                · intro y hy1 hy2
                  simp only [Contract.perm, Bool.or_eq_true]
                  left; left; left; left; left; left
                  simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]
                  omega
                · intro k hk
                  rw [hA]
                  have hm := (fmem k hk).2.2
                  simpa only [Int.ofNat_zero, Int.mul_zero, Int.add_zero] using hm
            | some rows =>
              simp only [hpr] at h
              have hw2 : width % 2 = 0 := by
                by_cases hw : width % 2 = 0
                · exact hw
                · simp [hw] at hpr
              simp only [hw2, ↓reduceIte] at hpr
              have := V.pure_ok h
              injection this with h1 _
              injection h1 with h1 h2
              subst h1 h2
              obtain ⟨rlen, rbd, rmem⟩ := framePairRows_sound H wf E.stackAt (width / 2) o hpr
              have hlen : rows.length = width := by omega
              have h2w : 2 * (width / 2) = width := by omega
              have hbound0 : -(ctx.contract.stackAt s0 : Int) ≤ o := by
                have := (rmem 0 (by omega)).1; omega
              have hrsp : ρ RSP = s0.reg RSP := H.entry RSP (by unfold Ctx.nreg Contract.regs RSP; split <;> omega)
              have eoff := ev_isConst (ρ := ρ) hc
              rw [ev_sub, ev_var, hrsp] at eoff
              have hsmall := E.small RSP
              have hstack := E.stackAt
              have hA : a = ((s0.reg RSP : Int) + o).toNat := ha ((s0.reg RSP : Int) + o).toNat (by omega) (by unfold M64 at hsmall ⊢; omega)
              obtain ⟨e, ok, tlen, tlt, tdn⟩ := termsOf_step (mk := wAtom)
                (val := fun r => (ev ρ r % W32i).toNat)
                (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) rows s.tab
                (fun r mr T _ okT => wAtom_step okT (rbd r mr))
                (Ext.refl _) wf.words.ok
              refine ⟨allowed_of _ _ _ ?_, Carried.terms H wf e ok, by omega, tlt, ?_⟩
              · intro y hy1 hy2
                have hle := Contract.stack_le_stackAt ctx.contract s0
                simp only [Contract.perm, Bool.or_eq_true]
                left; left; left; left; left; left
                simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]
                omega
              · intro k hk
                rw [hA]
                have hm := (rmem k (by omega)).2.2
                have hd := tdn k (by omega)
                have hget : rows[k]'(by omega) = rows.getD k (Lin.const 0) := by
                  have hlt : k < rows.length := by omega
                  simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]
                rw [hget] at hd
                rw [hd]
                omega
          next => exact (refuse_ok h).elim
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
              have hmem : ∀ k, k < 4 * width → st.mem (s0.reg r + c.toNat + k) = s0.mem (s0.reg r + c.toNat + k) := by
                intro k hk
                have := H.words.intact w hin' x r n hw' (c.toNat + k) (by omega)
                rw [← Nat.add_assoc] at this; exact this
              obtain ⟨cr, len, lt, dn⟩ := loadWords_terms (ρ := ρ) H wf (wordRuns_of hj') hmem (by omega)
              refine ⟨allowed_of _ _ _ ?_, cr, len, lt, ?_⟩
              · intro y hy1 hy2
                simp only [Contract.perm, Bool.or_eq_true]
                left; left; left; right
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

theorem symMemWords_sound {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s s' : Sym} {l : List Nat}
    {bind : Bind} {args : List Expr} {width : Nat} {items rest : Items} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (nonempty : 0 < width) (h : symMemWords ctx bind s args width items = .ok ((l, s'), rest)) :
    ∃ vs, values (ctx.contract.perm ctx.pieces s0) bind st args = some vs ∧
      let a := sumList vs % M64
      allowed (ctx.contract.perm ctx.pieces s0).read a (4 * width) = true ∧ Carried ctx s0 ρ s ρ s' st ∧ l.length = width ∧
      (∀ i ∈ l, i < s'.terms.length) ∧ ∀ k, k < width → load st.mem (a + 4 * k) 4 = den (inpOf ctx s0) ρ s'.terms (l.getD k 0) := by
  unfold symMemWords at h
  cases ha : symWordAddr ctx bind s args <;> simp only [ha] at h
  · exact (refuse_ok h).elim
  · obtain ⟨vs, vv, _, loc⟩ := symWordAddr_sound H wf ha
    exact ⟨vs, vv, symLoadWords_sound E h H wf nonempty _ loc⟩

/-! ## The four words a row sets a vector register to -/

theorem isConst_constant {a : Row} {k : Int} (h : Lin.isConst a = some k) : k = a.constant := by
  unfold Lin.isConst at h
  split at h
  next => injection h with h; exact h.symm
  next => contradiction

theorem vec4_getD {f : Nat → Nat} {k : Nat} (hk : k < 4) : [f 0, f 1, f 2, f 3].getD k 0 = f k := by
  rcases lt4 hk with rfl | rfl | rfl | rfl <;> rfl

theorem getD_index {α : Type} {xs : List α} {k : Nat} (h : k < xs.length) (d : α) : xs.getD k d = xs[k] := by
  simp only [List.getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD4_mem {l : List Nat} (h : l.length = 4) {k : Nat} (hk : k < 4) : l.getD k 0 ∈ l := by
  have h' : k < l.length := by simpa only [h] using hk
  rw [getD_index h']
  exact List.getElem_mem h'

theorem word_of_const (ρ : Nat → Int) {k : Int} (h : 0 ≤ k) : k.toNat % W32 = (ev ρ (Lin.const k) % W32i).toNat := by
  rw [ev_const]; unfold W32 W32i; omega

/-- The two halves of what a general register holds: the terms made are the machine's two low lanes, and
two zeros. -/
theorem symHalves_sound {ctx : Ctx} {s0 : State} {s s1 : Sym} {x : Row} {l : List Nat} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symHalves s x items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (xa : Nat) (hxa : xa < M64)
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
      [x, (symDivide s x W32i).1, Lin.const 0, Lin.const 0] (symDivide s x W32i).2.2.tab
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
        (l, s1) = ((termsOf wAtom [x, Lin.high x, Lin.const 0, Lin.const 0] s.tab).1,
                   { s with tab := (termsOf wAtom [x, Lin.high x, Lin.const 0, Lin.const 0] s.tab).2 }) := by
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
      (nv := s.nvars) (T0 := s.terms) [x, Lin.high x, Lin.const 0, Lin.const 0] s.tab
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

theorem wShl_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {a n : Nat} (ok : TableOk nv t.list)
    (ha : a < t.list.length) : Step inp ρ nv t.list (wShl a n t).2.list (wShl a n t).1 ((den inp ρ t.list a <<< n) % W32) :=
  step_of_made ok (wShl_made (t' := (wShl a n t).2) (i := (wShl a n t).1) rfl ok.wf ha) (fun r e => by cases e) (fun a k e => by cases e)

theorem wShr_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {a n : Nat} (ok : TableOk nv t.list)
    (ha : a < t.list.length) : Step inp ρ nv t.list (wShr a n t).2.list (wShr a n t).1 (den inp ρ t.list a >>> n) :=
  step_of_made ok (wShr_made (t' := (wShr a n t).2) (i := (wShr a n t).1) rfl ok.wf ha) (fun r e => by cases e) (fun a k e => by cases e)

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
    (h : symEach32 bind s args items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s1 st ∧ ∃ lanes, lanesOf (ctx.contract.perm ctx.pieces s0) bind st (.call "each32" args) = some lanes ∧
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
              (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) ([x0, x1, x2, x3].zip [y0, y1, y2, y3]) s.tab
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
                (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) ([x0, x1, x2, x3].zip [y0, y1, y2, y3]) s.tab
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
              next hop2a =>
                have oe : op = "and32" := by simpa using hop2a
                subst oe
                obtain ⟨rfl, rfl⟩ := pure_pair h
                obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := fun (q : Nat × Nat) => wAnd q.1 q.2)
                  (val := fun q => den (inpOf ctx s0) ρ s.terms q.1 &&& den (inpOf ctx s0) ρ s.terms q.2)
                  (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) ([x0, x1, x2, x3].zip [y0, y1, y2, y3]) s.tab
                  (by
                    intro q mq T eT okT
                    have m1 := ltx q.1 (List.of_mem_zip (a := q.1) (b := q.2) mq).1
                    have m2 := lty q.2 (List.of_mem_zip (a := q.1) (b := q.2) mq).2
                    have S := wAnd_step (inp := inpOf ctx s0) (ρ := ρ) okT (Nat.lt_of_lt_of_le m1 eT.le) (Nat.lt_of_lt_of_le m2 eT.le)
                    rw [den_ext wf.words.table eT m1, den_ext wf.words.table eT m2] at S
                    exact S)
                  (Ext.refl _) wf.words.ok
                refine ⟨ρ, Carried.terms H wf e ok,
                  [st.vec rx 0 &&& st.vec ry 0, st.vec rx 1 &&& st.vec ry 1, st.vec rx 2 &&& st.vec ry 2, st.vec rx 3 &&& st.vec ry 3],
                  ?_, lt, ?_⟩
                · simp [lanesOf, hvx, hvy, prim32]
                · intro k hk
                  rcases lt4 hk with rfl | rfl | rfl | rfl
                  · rw [dn 0 (by show _ < 4; omega), hdx 0 (by omega), hdy 0 (by omega)]; rfl
                  · rw [dn 1 (by show _ < 4; omega), hdx 1 (by omega), hdy 1 (by omega)]; rfl
                  · rw [dn 2 (by show _ < 4; omega), hdx 2 (by omega), hdy 2 (by omega)]; rfl
                  · rw [dn 3 (by show _ < 4; omega), hdx 3 (by omega), hdy 3 (by omega)]; rfl
              next hop2a =>
                split at h
                next hop3 =>
                  -- the or of a vector with itself (`mov vD.16b, vS.16b` = `orr vD.16b, vS.16b, vS.16b`)
                  -- or of a word shifted left and the same word shifted right: the word turned
                  have oe : op = "or32" := by simpa using hop3
                  subst oe
                  split at h
                  next hxy =>
                    have heq : [x0, x1, x2, x3] = [y0, y1, y2, y3] := by simpa using hxy
                    obtain ⟨rfl, rfl⟩ := pure_pair h
                    have hsame : ∀ k, k < 4 → st.vec rx k = st.vec ry k := fun k hk => by
                      rw [hdx k hk, hdy k hk, heq]
                    refine ⟨ρ, Carried.terms H wf (Ext.refl _) wf.words.ok,
                      [st.vec rx 0 ||| st.vec ry 0, st.vec rx 1 ||| st.vec ry 1,
                       st.vec rx 2 ||| st.vec ry 2, st.vec rx 3 ||| st.vec ry 3], ?_, ltx, ?_⟩
                    · simp [lanesOf, hvx, hvy, prim32]
                    · intro k hk
                      rcases lt4 hk with rfl | rfl | rfl | rfl
                      · rw [← hsame 0 (by omega), Nat.or_self, hdx 0 (by omega)]; rfl
                      · rw [← hsame 1 (by omega), Nat.or_self, hdx 1 (by omega)]; rfl
                      · rw [← hsame 2 (by omega), Nat.or_self, hdx 2 (by omega)]; rfl
                      · rw [← hsame 3 (by omega), Nat.or_self, hdx 3 (by omega)]; rfl
                  next hxy =>
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
                      (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) [t0, t1, t2, t3] s.tab
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
              obtain ⟨n0, n_lt, vn, vecn⟩ := symNumber_sound (perm := ctx.contract.perm ctx.pieces s0) (st := st) hn
              obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := fun q => wRotr q (n.toNat % 32))
                (val := fun q => rotr (den (inpOf ctx s0) ρ s.terms q) (n.toNat % 32))
                (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) [x0, x1, x2, x3] s.tab
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
                obtain ⟨n0, n_lt, vn, vecn⟩ := symNumber_sound (perm := ctx.contract.perm ctx.pieces s0) (st := st) hn
                obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := fun q => wShl q n.toNat)
                  (val := fun q => (den (inpOf ctx s0) ρ s.terms q <<< n.toNat) % W32)
                  (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) [x0, x1, x2, x3] s.tab
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
                  obtain ⟨n0, n_lt, vn, vecn⟩ := symNumber_sound (perm := ctx.contract.perm ctx.pieces s0) (st := st) hn
                  obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := fun q => wShr q n.toNat)
                    (val := fun q => den (inpOf ctx s0) ρ s.terms q >>> n.toNat)
                    (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) [x0, x1, x2, x3] s.tab
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
    (h : symShuffle bind s args items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s1 st ∧ ∃ lanes, lanesOf (ctx.contract.perm ctx.pieces s0) bind st (.call "shuffle_bytes" args) = some lanes ∧
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
        (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) [x0, x1, x2, x3] s.tab
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
    (h : symMoved bind s f args items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s1 st ∧ ∃ lanes, lanesOf (ctx.contract.perm ctx.pieces s0) bind st (.call f args) = some lanes ∧
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
    obtain ⟨i0, i_lt, vi, _⟩ := symNumber_sound (perm := ctx.contract.perm ctx.pieces s0) (st := st) hi
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

/-- Soundness of symbolic SHA-256 combinators (`sha256msg1/2`, `sha256su1`, `sha256rnds2`, `sha256h/h2`). -/
theorem wAdd2_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {a b : Nat} (ok : TableOk nv t.list)
    (ha : a < t.list.length) (hb : b < t.list.length) :
    Step inp ρ nv t.list (wAdd2 a b t).2.list (wAdd2 a b t).1 ((den inp ρ t.list a + den inp ρ t.list b) % W32) :=
  wAdd_step ok ha hb

theorem wSha256Ch_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {e f g : Nat}
    (ok : TableOk nv t.list) (he : e < t.list.length) (hf : f < t.list.length) (hg : g < t.list.length) :
    Step inp ρ nv t.list (wSha256Ch e f g t).2.list (wSha256Ch e f g t).1
      (sha256Ch (den inp ρ t.list e) (den inp ρ t.list f) (den inp ρ t.list g)) := by
  unfold wSha256Ch sha256Ch
  have s1 := wXor_step (inp := inp) (ρ := ρ) ok hf hg
  have s2 := wAnd_step (inp := inp) (ρ := ρ) s1.ok (Nat.lt_of_lt_of_le he s1.ext.le) s1.lt
  have e12 := s1.ext.trans s2.ext
  have s3 := wXor_step (inp := inp) (ρ := ρ) s2.ok (Nat.lt_of_lt_of_le hg e12.le) s2.lt
  refine ⟨e12.trans s3.ext, s3.ok, s3.lt, ?_⟩
  rw [s3.den, den_ext ok.wf e12 hg, s2.den, den_ext ok.wf s1.ext he, s1.den]

theorem wSha256Maj_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {a b c : Nat}
    (ok : TableOk nv t.list) (ha : a < t.list.length) (hb : b < t.list.length) (hc : c < t.list.length) :
    Step inp ρ nv t.list (wSha256Maj a b c t).2.list (wSha256Maj a b c t).1
      (sha256Maj (den inp ρ t.list a) (den inp ρ t.list b) (den inp ρ t.list c)) := by
  unfold wSha256Maj sha256Maj
  have s1 := wAnd_step (inp := inp) (ρ := ρ) ok ha hb
  have s2 := wXor_step (inp := inp) (ρ := ρ) s1.ok (Nat.lt_of_lt_of_le ha s1.ext.le) (Nat.lt_of_lt_of_le hb s1.ext.le)
  have e12 := s1.ext.trans s2.ext
  have s3 := wAnd_step (inp := inp) (ρ := ρ) s2.ok s2.lt (Nat.lt_of_lt_of_le hc e12.le)
  have e23 := s2.ext.trans s3.ext
  have e13 := s1.ext.trans e23
  have s4 := wXor_step (inp := inp) (ρ := ρ) s3.ok (Nat.lt_of_lt_of_le s1.lt e23.le) s3.lt
  refine ⟨e13.trans s4.ext, s4.ok, s4.lt, ?_⟩
  rw [s4.den, den_ext s1.ok.wf e23 s1.lt, s1.den, s3.den, s2.den,
      den_ext ok.wf s1.ext ha, den_ext ok.wf s1.ext hb, den_ext ok.wf e12 hc]

theorem wSha256S0_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {a : Nat}
    (ok : TableOk nv t.list) (ha : a < t.list.length) :
    Step inp ρ nv t.list (wSha256S0 a t).2.list (wSha256S0 a t).1 (sha256S0 (den inp ρ t.list a)) := by
  unfold wSha256S0 sha256S0
  have s1 := wRotr_step (inp := inp) (ρ := ρ) (n := 2) ok ha (by decide)
  have s2 := wRotr_step (inp := inp) (ρ := ρ) (n := 13) s1.ok (Nat.lt_of_lt_of_le ha s1.ext.le) (by decide)
  have e12 := s1.ext.trans s2.ext
  have s3 := wRotr_step (inp := inp) (ρ := ρ) (n := 22) s2.ok (Nat.lt_of_lt_of_le ha e12.le) (by decide)
  have e23 := s2.ext.trans s3.ext
  have e13 := s1.ext.trans e23
  have s4 := wXor_step (inp := inp) (ρ := ρ) s3.ok (Nat.lt_of_lt_of_le s1.lt e23.le) (Nat.lt_of_lt_of_le s2.lt s3.ext.le)
  have s5 := wXor_step (inp := inp) (ρ := ρ) s4.ok s4.lt (Nat.lt_of_lt_of_le s3.lt s4.ext.le)
  refine ⟨(e13.trans s4.ext).trans s5.ext, s5.ok, s5.lt, ?_⟩
  rw [s5.den, s4.den, den_ext s1.ok.wf e23 s1.lt, s1.den, den_ext s2.ok.wf s3.ext s2.lt, s2.den,
      den_ext ok.wf s1.ext ha, den_ext s3.ok.wf s4.ext s3.lt, s3.den, den_ext ok.wf e12 ha]

theorem wSha256S1_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {e : Nat}
    (ok : TableOk nv t.list) (he : e < t.list.length) :
    Step inp ρ nv t.list (wSha256S1 e t).2.list (wSha256S1 e t).1 (sha256S1 (den inp ρ t.list e)) := by
  unfold wSha256S1 sha256S1
  have s1 := wRotr_step (inp := inp) (ρ := ρ) (n := 6) ok he (by decide)
  have s2 := wRotr_step (inp := inp) (ρ := ρ) (n := 11) s1.ok (Nat.lt_of_lt_of_le he s1.ext.le) (by decide)
  have e12 := s1.ext.trans s2.ext
  have s3 := wRotr_step (inp := inp) (ρ := ρ) (n := 25) s2.ok (Nat.lt_of_lt_of_le he e12.le) (by decide)
  have e23 := s2.ext.trans s3.ext
  have e13 := s1.ext.trans e23
  have s4 := wXor_step (inp := inp) (ρ := ρ) s3.ok (Nat.lt_of_lt_of_le s1.lt e23.le) (Nat.lt_of_lt_of_le s2.lt s3.ext.le)
  have s5 := wXor_step (inp := inp) (ρ := ρ) s4.ok s4.lt (Nat.lt_of_lt_of_le s3.lt s4.ext.le)
  refine ⟨(e13.trans s4.ext).trans s5.ext, s5.ok, s5.lt, ?_⟩
  rw [s5.den, s4.den, den_ext s1.ok.wf e23 s1.lt, s1.den, den_ext s2.ok.wf s3.ext s2.lt, s2.den,
      den_ext ok.wf s1.ext he, den_ext s3.ok.wf s4.ext s3.lt, s3.den, den_ext ok.wf e12 he]

theorem wSha256s0_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {x : Nat}
    (ok : TableOk nv t.list) (hx : x < t.list.length) :
    Step inp ρ nv t.list (wSha256s0 x t).2.list (wSha256s0 x t).1 (sha256s0 (den inp ρ t.list x)) := by
  unfold wSha256s0 sha256s0
  have s1 := wRotr_step (inp := inp) (ρ := ρ) (n := 7) ok hx (by decide)
  have s2 := wRotr_step (inp := inp) (ρ := ρ) (n := 18) s1.ok (Nat.lt_of_lt_of_le hx s1.ext.le) (by decide)
  have e12 := s1.ext.trans s2.ext
  have s3 := wShr_step (inp := inp) (ρ := ρ) (n := 3) s2.ok (Nat.lt_of_lt_of_le hx e12.le)
  have e23 := s2.ext.trans s3.ext
  have e13 := s1.ext.trans e23
  have s4 := wXor_step (inp := inp) (ρ := ρ) s3.ok (Nat.lt_of_lt_of_le s1.lt e23.le) (Nat.lt_of_lt_of_le s2.lt s3.ext.le)
  have s5 := wXor_step (inp := inp) (ρ := ρ) s4.ok s4.lt (Nat.lt_of_lt_of_le s3.lt s4.ext.le)
  refine ⟨(e13.trans s4.ext).trans s5.ext, s5.ok, s5.lt, ?_⟩
  rw [s5.den, s4.den, den_ext s1.ok.wf e23 s1.lt, s1.den, den_ext s2.ok.wf s3.ext s2.lt, s2.den,
      den_ext ok.wf s1.ext hx, den_ext s3.ok.wf s4.ext s3.lt, s3.den, den_ext ok.wf e12 hx]

theorem wSha256s1_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {x : Nat}
    (ok : TableOk nv t.list) (hx : x < t.list.length) :
    Step inp ρ nv t.list (wSha256s1 x t).2.list (wSha256s1 x t).1 (sha256s1 (den inp ρ t.list x)) := by
  unfold wSha256s1 sha256s1
  have s1 := wRotr_step (inp := inp) (ρ := ρ) (n := 17) ok hx (by decide)
  have s2 := wRotr_step (inp := inp) (ρ := ρ) (n := 19) s1.ok (Nat.lt_of_lt_of_le hx s1.ext.le) (by decide)
  have e12 := s1.ext.trans s2.ext
  have s3 := wShr_step (inp := inp) (ρ := ρ) (n := 10) s2.ok (Nat.lt_of_lt_of_le hx e12.le)
  have e23 := s2.ext.trans s3.ext
  have e13 := s1.ext.trans e23
  have s4 := wXor_step (inp := inp) (ρ := ρ) s3.ok (Nat.lt_of_lt_of_le s1.lt e23.le) (Nat.lt_of_lt_of_le s2.lt s3.ext.le)
  have s5 := wXor_step (inp := inp) (ρ := ρ) s4.ok s4.lt (Nat.lt_of_lt_of_le s3.lt s4.ext.le)
  refine ⟨(e13.trans s4.ext).trans s5.ext, s5.ok, s5.lt, ?_⟩
  rw [s5.den, s4.den, den_ext s1.ok.wf e23 s1.lt, s1.den, den_ext s2.ok.wf s3.ext s2.lt, s2.den,
      den_ext ok.wf s1.ext hx, den_ext s3.ok.wf s4.ext s3.lt, s3.den, den_ext ok.wf e12 hx]

structure RoundStep (inp : Nat → Nat → Nat) (ρ : Nat → Int) (nv : Nat) (T T' : List Node)
    (ids : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat)
    (vals : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Prop where
  ext : Ext T T'
  ok : TableOk nv T'
  la : ids.1 < T'.length
  lb : ids.2.1 < T'.length
  lc : ids.2.2.1 < T'.length
  ld : ids.2.2.2.1 < T'.length
  le_ : ids.2.2.2.2.1 < T'.length
  lf : ids.2.2.2.2.2.1 < T'.length
  lg : ids.2.2.2.2.2.2.1 < T'.length
  lh : ids.2.2.2.2.2.2.2 < T'.length
  da : den inp ρ T' ids.1 = vals.1
  db : den inp ρ T' ids.2.1 = vals.2.1
  dc : den inp ρ T' ids.2.2.1 = vals.2.2.1
  dd : den inp ρ T' ids.2.2.2.1 = vals.2.2.2.1
  de : den inp ρ T' ids.2.2.2.2.1 = vals.2.2.2.2.1
  df : den inp ρ T' ids.2.2.2.2.2.1 = vals.2.2.2.2.2.1
  dg : den inp ρ T' ids.2.2.2.2.2.2.1 = vals.2.2.2.2.2.2.1
  dh : den inp ρ T' ids.2.2.2.2.2.2.2 = vals.2.2.2.2.2.2.2

theorem wSha256Round_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab}
    {a b c d e f g h wk : Nat} (ok : TableOk nv t.list)
    (ha : a < t.list.length) (hb : b < t.list.length) (hc : c < t.list.length) (hd : d < t.list.length)
    (he : e < t.list.length) (hf : f < t.list.length) (hg : g < t.list.length) (hh : h < t.list.length)
    (hwk : wk < t.list.length) :
    RoundStep inp ρ nv t.list (wSha256Round a b c d e f g h wk t).2.list
      (wSha256Round a b c d e f g h wk t).1
      (sha256Round (den inp ρ t.list a) (den inp ρ t.list b) (den inp ρ t.list c) (den inp ρ t.list d)
                   (den inp ρ t.list e) (den inp ρ t.list f) (den inp ρ t.list g) (den inp ρ t.list h)
                   (den inp ρ t.list wk)) := by
  unfold wSha256Round sha256Round
  have st1 := wSha256S1_step (inp := inp) (ρ := ρ) ok he
  have st2 := wSha256Ch_step (inp := inp) (ρ := ρ) st1.ok
    (Nat.lt_of_lt_of_le he st1.ext.le) (Nat.lt_of_lt_of_le hf st1.ext.le) (Nat.lt_of_lt_of_le hg st1.ext.le)
  have e12 := st1.ext.trans st2.ext
  have st3 := wAdd2_step (inp := inp) (ρ := ρ) st2.ok
    (Nat.lt_of_lt_of_le hh e12.le) (Nat.lt_of_lt_of_le st1.lt st2.ext.le)
  have e13 := e12.trans st3.ext
  have st4 := wAdd2_step (inp := inp) (ρ := ρ) st3.ok st3.lt (Nat.lt_of_lt_of_le st2.lt st3.ext.le)
  have e14 := e13.trans st4.ext
  have st5 := wAdd2_step (inp := inp) (ρ := ρ) st4.ok st4.lt (Nat.lt_of_lt_of_le hwk e14.le)
  have e15 := e14.trans st5.ext
  have st6 := wSha256S0_step (inp := inp) (ρ := ρ) st5.ok (Nat.lt_of_lt_of_le ha e15.le)
  have e16 := e15.trans st6.ext
  have st7 := wSha256Maj_step (inp := inp) (ρ := ρ) st6.ok
    (Nat.lt_of_lt_of_le ha e16.le) (Nat.lt_of_lt_of_le hb e16.le) (Nat.lt_of_lt_of_le hc e16.le)
  have e17 := e16.trans st7.ext
  have st8 := wAdd2_step (inp := inp) (ρ := ρ) st7.ok (Nat.lt_of_lt_of_le st6.lt st7.ext.le) st7.lt
  have e58 := (st6.ext.trans st7.ext).trans st8.ext
  have e18 := e17.trans st8.ext
  have st9 := wAdd2_step (inp := inp) (ρ := ρ) st8.ok (Nat.lt_of_lt_of_le st5.lt e58.le) st8.lt
  have e59 := e58.trans st9.ext
  have e19 := e18.trans st9.ext
  have st10 := wAdd2_step (inp := inp) (ρ := ρ) st9.ok (Nat.lt_of_lt_of_le hd e19.le) (Nat.lt_of_lt_of_le st5.lt e59.le)
  have e110 := e19.trans st10.ext
  exact ⟨e110, st10.ok,
    Nat.lt_of_lt_of_le st9.lt st10.ext.le,
    Nat.lt_of_lt_of_le ha e110.le, Nat.lt_of_lt_of_le hb e110.le, Nat.lt_of_lt_of_le hc e110.le,
    st10.lt,
    Nat.lt_of_lt_of_le he e110.le, Nat.lt_of_lt_of_le hf e110.le, Nat.lt_of_lt_of_le hg e110.le,
    by
      dsimp only
      rw [den_ext st9.ok.wf st10.ext st9.lt, st9.den, den_ext st5.ok.wf e58 st5.lt,
          st5.den, st4.den, st3.den, den_ext ok.wf e12 hh, den_ext st1.ok.wf st2.ext st1.lt, st1.den,
          den_ext st2.ok.wf st3.ext st2.lt, st2.den,
          den_ext ok.wf st1.ext he, den_ext ok.wf st1.ext hf, den_ext ok.wf st1.ext hg,
          den_ext ok.wf e14 hwk,
          st8.den, den_ext st6.ok.wf st7.ext st6.lt, st6.den, den_ext ok.wf e15 ha,
          st7.den, den_ext ok.wf e16 ha, den_ext ok.wf e16 hb, den_ext ok.wf e16 hc],
    den_ext ok.wf e110 ha, den_ext ok.wf e110 hb, den_ext ok.wf e110 hc,
    by
      dsimp only
      rw [st10.den, den_ext ok.wf e19 hd, den_ext st5.ok.wf e59 st5.lt,
          st5.den, st4.den, st3.den, den_ext ok.wf e12 hh, den_ext st1.ok.wf st2.ext st1.lt, st1.den,
          den_ext st2.ok.wf st3.ext st2.lt, st2.den,
          den_ext ok.wf st1.ext he, den_ext ok.wf st1.ext hf, den_ext ok.wf st1.ext hg,
          den_ext ok.wf e14 hwk],
    den_ext ok.wf e110 he, den_ext ok.wf e110 hf, den_ext ok.wf e110 hg⟩

theorem list4_lt {l : List Nat} {T : List Node} {a b c d : Nat}
    (hl : l = [a, b, c, d]) (ha : a < T.length) (hb : b < T.length) (hc : c < T.length) (hd : d < T.length) :
    ∀ i ∈ l, i < T.length := by
  subst hl; intro i mi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at mi
  rcases mi with rfl | rfl | rfl | rfl <;> assumption

theorem vec_lt_getD {l : List Nat} {n : Nat} (hlt : ∀ i ∈ l, i < n) (hlen : l.length = 4) {k : Nat} (hk : k < 4) :
    l.getD k 0 < n := by
  have hk' : k < l.length := by omega
  have heq : l.getD k 0 = l[k] := by simp [List.getD, List.getElem?_eq_getElem hk']
  rw [heq]; exact hlt _ (List.getElem_mem hk')

theorem getD4_0 {α : Type} (a b c d z : α) : [a, b, c, d].getD 0 z = a := rfl
theorem getD4_1 {α : Type} (a b c d z : α) : [a, b, c, d].getD 1 z = b := rfl
theorem getD4_2 {α : Type} (a b c d z : α) : [a, b, c, d].getD 2 z = c := rfl
theorem getD4_3 {α : Type} (a b c d z : α) : [a, b, c, d].getD 3 z = d := rfl
theorem range4_map {α : Type} (f : Nat → α) : (List.range 4).map f = [f 0, f 1, f 2, f 3] := rfl

theorem wSha256s0_step_eq {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t t' : Tab} {a r : Nat}
    (h : wSha256s0 a t = (r, t')) (ok : TableOk nv t.list) (ha : a < t.list.length) :
    Step inp ρ nv t.list t'.list r (sha256s0 (den inp ρ t.list a)) := by
  have s := wSha256s0_step (inp := inp) (ρ := ρ) ok ha; rw [h] at s; exact s

theorem wSha256s1_step_eq {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t t' : Tab} {a r : Nat}
    (h : wSha256s1 a t = (r, t')) (ok : TableOk nv t.list) (ha : a < t.list.length) :
    Step inp ρ nv t.list t'.list r (sha256s1 (den inp ρ t.list a)) := by
  have s := wSha256s1_step (inp := inp) (ρ := ρ) ok ha; rw [h] at s; exact s

theorem wAdd2_step_eq {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t t' : Tab} {a b r : Nat}
    (h : wAdd2 a b t = (r, t')) (ok : TableOk nv t.list) (ha : a < t.list.length) (hb : b < t.list.length) :
    Step inp ρ nv t.list t'.list r ((den inp ρ t.list a + den inp ρ t.list b) % W32) := by
  have s := wAdd2_step (inp := inp) (ρ := ρ) ok ha hb; rw [h] at s; exact s

theorem wSha256Round_step_eq {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t t' : Tab}
    {a b c d e f g h wk a' b' c' d' e' f' g' h' : Nat}
    (hr : wSha256Round a b c d e f g h wk t = ((a', b', c', d', e', f', g', h'), t'))
    (ok : TableOk nv t.list)
    (ha : a < t.list.length) (hb : b < t.list.length) (hc : c < t.list.length) (hd : d < t.list.length)
    (he : e < t.list.length) (hf : f < t.list.length) (hg : g < t.list.length) (hh : h < t.list.length)
    (hwk : wk < t.list.length) :
    RoundStep inp ρ nv t.list t'.list (a', b', c', d', e', f', g', h')
      (sha256Round (den inp ρ t.list a) (den inp ρ t.list b) (den inp ρ t.list c) (den inp ρ t.list d)
                   (den inp ρ t.list e) (den inp ρ t.list f) (den inp ρ t.list g) (den inp ρ t.list h)
                   (den inp ρ t.list wk)) := by
  have st := wSha256Round_step (inp := inp) (ρ := ρ) ok ha hb hc hd he hf hg hh hwk
  rw [hr] at st; exact st

private theorem wSha256Msg1_gen {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat}
    (fs : Nat → Tab → Nat × Tab) (cs : Nat → Nat)
    (hfs : ∀ {t : Tab} {a : Nat}, TableOk nv t.list → a < t.list.length →
      Step inp ρ nv t.list (fs a t).2.list (fs a t).1 (cs (den inp ρ t.list a)))
    (fa : Nat → Nat → Tab → Nat × Tab)
    (hfa : ∀ {t : Tab} {a b : Nat}, TableOk nv t.list → a < t.list.length → b < t.list.length →
      Step inp ρ nv t.list (fa a b t).2.list (fa a b t).1 ((den inp ρ t.list a + den inp ρ t.list b) % W32))
    {t : Tab} {x y : List Nat}
    (ok : TableOk nv t.list) (hx : ∀ i ∈ x, i < t.list.length) (hy : ∀ i ∈ y, i < t.list.length)
    (lx : x.length = 4) (ly : y.length = 4) :
    let res :=
      let (s0, t) := fs (x.getD 1 0) t
      let (r0, t) := fa (x.getD 0 0) s0 t
      let (s1, t) := fs (x.getD 2 0) t
      let (r1, t) := fa (x.getD 1 0) s1 t
      let (s2, t) := fs (x.getD 3 0) t
      let (r2, t) := fa (x.getD 2 0) s2 t
      let (s3, t) := fs (y.getD 0 0) t
      let (r3, t) := fa (x.getD 3 0) s3 t
      ([r0, r1, r2, r3], t)
    Ext t.list res.2.list ∧ TableOk nv res.2.list ∧
    (∀ i ∈ res.1, i < res.2.list.length) ∧
    ∀ k, k < 4 → ([(den inp ρ t.list (x.getD 0 0) + cs (den inp ρ t.list (x.getD 1 0))) % W32,
                   (den inp ρ t.list (x.getD 1 0) + cs (den inp ρ t.list (x.getD 2 0))) % W32,
                   (den inp ρ t.list (x.getD 2 0) + cs (den inp ρ t.list (x.getD 3 0))) % W32,
                   (den inp ρ t.list (x.getD 3 0) + cs (den inp ρ t.list (y.getD 0 0))) % W32]).getD k 0 =
                 den inp ρ res.2.list (res.1.getD k 0) := by
  dsimp only
  have x0 := vec_lt_getD hx lx (k := 0) (by decide)
  have x1 := vec_lt_getD hx lx (k := 1) (by decide)
  have x2 := vec_lt_getD hx lx (k := 2) (by decide)
  have x3 := vec_lt_getD hx lx (k := 3) (by decide)
  have y0 := vec_lt_getD hy ly (k := 0) (by decide)
  have s0 := hfs ok x1
  have r0 := hfa s0.ok (Nat.lt_of_lt_of_le x0 s0.ext.le) s0.lt
  have e0 := s0.ext.trans r0.ext
  have s1 := hfs r0.ok (Nat.lt_of_lt_of_le x2 e0.le)
  have r1 := hfa s1.ok (Nat.lt_of_lt_of_le x1 (e0.trans s1.ext).le) s1.lt
  have e1 := s1.ext.trans r1.ext; have e01 := e0.trans e1
  have s2 := hfs r1.ok (Nat.lt_of_lt_of_le x3 e01.le)
  have r2 := hfa s2.ok (Nat.lt_of_lt_of_le x2 (e01.trans s2.ext).le) s2.lt
  have e2 := s2.ext.trans r2.ext; have e02 := e01.trans e2
  have s3 := hfs r2.ok (Nat.lt_of_lt_of_le y0 e02.le)
  have r3 := hfa s3.ok (Nat.lt_of_lt_of_le x3 (e02.trans s3.ext).le) s3.lt
  have e3 := s3.ext.trans r3.ext; have e03 := e02.trans e3
  refine ⟨e03, r3.ok, list4_lt rfl (Nat.lt_of_lt_of_le r0.lt (e1.trans (e2.trans e3)).le)
    (Nat.lt_of_lt_of_le r1.lt (e2.trans e3).le) (Nat.lt_of_lt_of_le r2.lt e3.le) r3.lt, ?_⟩
  intro k hk
  rcases lt4 hk with rfl | rfl | rfl | rfl
  · simp only [getD4_0]
    rw [den_ext r0.ok.wf (e1.trans (e2.trans e3)) r0.lt, r0.den, den_ext ok.wf s0.ext x0, s0.den]
  · simp only [getD4_1]
    rw [den_ext r1.ok.wf (e2.trans e3) r1.lt, r1.den, den_ext ok.wf (e0.trans s1.ext) x1, s1.den, den_ext ok.wf e0 x2]
  · simp only [getD4_2]
    rw [den_ext r2.ok.wf e3 r2.lt, r2.den, den_ext ok.wf (e01.trans s2.ext) x2, s2.den, den_ext ok.wf e01 x3]
  · simp only [getD4_3]
    rw [r3.den, den_ext ok.wf (e02.trans s3.ext) x3, s3.den, den_ext ok.wf e02 y0]

theorem wSha256Msg1_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {x y : List Nat}
    (ok : TableOk nv t.list) (hx : ∀ i ∈ x, i < t.list.length) (hy : ∀ i ∈ y, i < t.list.length)
    (lx : x.length = 4) (ly : y.length = 4) :
    Ext t.list (wSha256Msg1 x y t).2.list ∧ TableOk nv (wSha256Msg1 x y t).2.list ∧
    (∀ i ∈ (wSha256Msg1 x y t).1, i < (wSha256Msg1 x y t).2.list.length) ∧
    ∀ k, k < 4 → (sha256Msg1 ((List.range 4).map fun j => den inp ρ t.list (x.getD j 0))
                             ((List.range 4).map fun j => den inp ρ t.list (y.getD j 0))).getD k 0 =
                 den inp ρ (wSha256Msg1 x y t).2.list ((wSha256Msg1 x y t).1.getD k 0) := by
  unfold wSha256Msg1 sha256Msg1
  simp only [range4_map, getD4_0, getD4_1, getD4_2, getD4_3]
  exact wSha256Msg1_gen wSha256s0 sha256s0
    (fun ok' ha => wSha256s0_step (inp := inp) (ρ := ρ) ok' ha)
    wAdd2 (fun ok' ha hb => wAdd2_step (inp := inp) (ρ := ρ) ok' ha hb)
    ok hx hy lx ly

theorem wSha256Msg2_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {x z : List Nat}
    (ok : TableOk nv t.list) (hx : ∀ i ∈ x, i < t.list.length) (hz : ∀ i ∈ z, i < t.list.length)
    (lx : x.length = 4) (lz : z.length = 4) :
    Ext t.list (wSha256Msg2 x z t).2.list ∧ TableOk nv (wSha256Msg2 x z t).2.list ∧
    (∀ i ∈ (wSha256Msg2 x z t).1, i < (wSha256Msg2 x z t).2.list.length) ∧
    ∀ k, k < 4 → (sha256Msg2 ((List.range 4).map fun j => den inp ρ t.list (x.getD j 0))
                             ((List.range 4).map fun j => den inp ρ t.list (z.getD j 0))).getD k 0 =
                 den inp ρ (wSha256Msg2 x z t).2.list ((wSha256Msg2 x z t).1.getD k 0) := by
  unfold wSha256Msg2 sha256Msg2
  simp only [range4_map, getD4_0, getD4_1, getD4_2, getD4_3]
  have x0 := vec_lt_getD hx lx (k := 0) (by decide)
  have x1 := vec_lt_getD hx lx (k := 1) (by decide)
  have x2 := vec_lt_getD hx lx (k := 2) (by decide)
  have x3 := vec_lt_getD hx lx (k := 3) (by decide)
  have z2 := vec_lt_getD hz lz (k := 2) (by decide)
  have z3 := vec_lt_getD hz lz (k := 3) (by decide)
  rcases hs0 : wSha256s1 (z.getD 2 0) t with ⟨v0, ts0⟩
  have s0 := wSha256s1_step_eq (inp := inp) (ρ := ρ) hs0 ok z2
  rcases hr0 : wAdd2 (x.getD 0 0) v0 ts0 with ⟨u0, t0⟩
  have r0 := wAdd2_step_eq (inp := inp) (ρ := ρ) hr0 s0.ok (Nat.lt_of_lt_of_le x0 s0.ext.le) s0.lt
  have e0 := s0.ext.trans r0.ext
  rcases hs1 : wSha256s1 (z.getD 3 0) t0 with ⟨v1, ts1⟩
  have s1 := wSha256s1_step_eq (inp := inp) (ρ := ρ) hs1 r0.ok (Nat.lt_of_lt_of_le z3 e0.le)
  rcases hr1 : wAdd2 (x.getD 1 0) v1 ts1 with ⟨u1, t1⟩
  have r1 := wAdd2_step_eq (inp := inp) (ρ := ρ) hr1 s1.ok (Nat.lt_of_lt_of_le x1 (e0.trans s1.ext).le) s1.lt
  have e1 := s1.ext.trans r1.ext; have e01 := e0.trans e1
  rcases hs2 : wSha256s1 u0 t1 with ⟨v2, ts2⟩
  have s2 := wSha256s1_step_eq (inp := inp) (ρ := ρ) hs2 r1.ok (Nat.lt_of_lt_of_le r0.lt e1.le)
  rcases hr2 : wAdd2 (x.getD 2 0) v2 ts2 with ⟨u2, t2⟩
  have r2 := wAdd2_step_eq (inp := inp) (ρ := ρ) hr2 s2.ok (Nat.lt_of_lt_of_le x2 (e01.trans s2.ext).le) s2.lt
  have e2 := s2.ext.trans r2.ext; have e02 := e01.trans e2
  rcases hs3 : wSha256s1 u1 t2 with ⟨v3, ts3⟩
  have s3 := wSha256s1_step_eq (inp := inp) (ρ := ρ) hs3 r2.ok (Nat.lt_of_lt_of_le r1.lt e2.le)
  rcases hr3 : wAdd2 (x.getD 3 0) v3 ts3 with ⟨u3, t3⟩
  have r3 := wAdd2_step_eq (inp := inp) (ρ := ρ) hr3 s3.ok (Nat.lt_of_lt_of_le x3 (e02.trans s3.ext).le) s3.lt
  have e3 := s3.ext.trans r3.ext; have e03 := e02.trans e3
  refine ⟨e03, r3.ok, list4_lt rfl (Nat.lt_of_lt_of_le r0.lt (e1.trans (e2.trans e3)).le)
    (Nat.lt_of_lt_of_le r1.lt (e2.trans e3).le) (Nat.lt_of_lt_of_le r2.lt e3.le) r3.lt, ?_⟩
  intro k hk
  rcases lt4 hk with rfl | rfl | rfl | rfl
  · simp only [getD4_0]
    rw [den_ext r0.ok.wf (e1.trans (e2.trans e3)) r0.lt, r0.den, den_ext ok.wf s0.ext x0, s0.den]
  · simp only [getD4_1]
    rw [den_ext r1.ok.wf (e2.trans e3) r1.lt, r1.den, den_ext ok.wf (e0.trans s1.ext) x1, s1.den, den_ext ok.wf e0 z3]
  · simp only [getD4_2]
    rw [den_ext r2.ok.wf e3 r2.lt, r2.den, den_ext ok.wf (e01.trans s2.ext) x2, s2.den, den_ext r0.ok.wf e1 r0.lt, r0.den, den_ext ok.wf s0.ext x0, s0.den]
  · simp only [getD4_3]
    rw [r3.den, den_ext ok.wf (e02.trans s3.ext) x3, s3.den, den_ext r1.ok.wf e2 r1.lt, r1.den, den_ext ok.wf (e0.trans s1.ext) x1, s1.den, den_ext ok.wf e0 z3]

theorem wSha256Su1_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {x y z : List Nat}
    (ok : TableOk nv t.list)
    (hx : ∀ i ∈ x, i < t.list.length) (hy : ∀ i ∈ y, i < t.list.length) (hz : ∀ i ∈ z, i < t.list.length)
    (lx : x.length = 4) (ly : y.length = 4) (lz : z.length = 4) :
    Ext t.list (wSha256Su1 x y z t).2.list ∧ TableOk nv (wSha256Su1 x y z t).2.list ∧
    (∀ i ∈ (wSha256Su1 x y z t).1, i < (wSha256Su1 x y z t).2.list.length) ∧
    ∀ k, k < 4 → (sha256Su1 ((List.range 4).map fun j => den inp ρ t.list (x.getD j 0))
                            ((List.range 4).map fun j => den inp ρ t.list (y.getD j 0))
                            ((List.range 4).map fun j => den inp ρ t.list (z.getD j 0))).getD k 0 =
                 den inp ρ (wSha256Su1 x y z t).2.list ((wSha256Su1 x y z t).1.getD k 0) := by
  unfold wSha256Su1 sha256Su1
  have x0 := vec_lt_getD hx lx (k := 0) (by decide)
  have x1 := vec_lt_getD hx lx (k := 1) (by decide)
  have x2 := vec_lt_getD hx lx (k := 2) (by decide)
  have x3 := vec_lt_getD hx lx (k := 3) (by decide)
  have y1 := vec_lt_getD hy ly (k := 1) (by decide)
  have y2 := vec_lt_getD hy ly (k := 2) (by decide)
  have y3 := vec_lt_getD hy ly (k := 3) (by decide)
  have z0 := vec_lt_getD hz lz (k := 0) (by decide)
  rcases hp0 : wAdd2 (x.getD 0 0) (y.getD 1 0) t with ⟨u0, t0⟩; dsimp
  have st0 := wAdd2_step_eq (inp := inp) (ρ := ρ) hp0 ok x0 y1
  rcases hp1 : wAdd2 (x.getD 1 0) (y.getD 2 0) t0 with ⟨u1, t1⟩; dsimp
  have st1 := wAdd2_step_eq (inp := inp) (ρ := ρ) hp1 st0.ok (Nat.lt_of_lt_of_le x1 st0.ext.le) (Nat.lt_of_lt_of_le y2 st0.ext.le)
  have e01 := st0.ext.trans st1.ext
  rcases hp2 : wAdd2 (x.getD 2 0) (y.getD 3 0) t1 with ⟨u2, t2⟩; dsimp
  have st2 := wAdd2_step_eq (inp := inp) (ρ := ρ) hp2 st1.ok (Nat.lt_of_lt_of_le x2 e01.le) (Nat.lt_of_lt_of_le y3 e01.le)
  have e02 := e01.trans st2.ext
  rcases hp3 : wAdd2 (x.getD 3 0) (z.getD 0 0) t2 with ⟨u3, t3⟩; dsimp
  have st3 := wAdd2_step_eq (inp := inp) (ρ := ρ) hp3 st2.ok (Nat.lt_of_lt_of_le x3 e02.le) (Nat.lt_of_lt_of_le z0 e02.le)
  have e03 := e02.trans st3.ext
  have hts : ∀ i ∈ [u0, u1, u2, u3], i < t3.list.length :=
    list4_lt rfl (Nat.lt_of_lt_of_le st0.lt (st1.ext.trans (st2.ext.trans st3.ext)).le)
      (Nat.lt_of_lt_of_le st1.lt (st2.ext.trans st3.ext).le) (Nat.lt_of_lt_of_le st2.lt st3.ext.le) st3.lt
  have hz' : ∀ i ∈ z, i < t3.list.length := fun i mi => Nat.lt_of_lt_of_le (hz i mi) e03.le
  obtain ⟨em, okm, ltm, dnm⟩ := wSha256Msg2_step (inp := inp) (ρ := ρ) st3.ok hts hz' rfl lz
  refine ⟨e03.trans em, okm, ltm, ?_⟩
  intro k hk
  have eqL : ((List.range 4).map fun j => den inp ρ t3.list ([u0, u1, u2, u3].getD j 0)) =
      [(den inp ρ t.list (x.getD 0 0) + den inp ρ t.list (y.getD 1 0)) % W32,
       (den inp ρ t.list (x.getD 1 0) + den inp ρ t.list (y.getD 2 0)) % W32,
       (den inp ρ t.list (x.getD 2 0) + den inp ρ t.list (y.getD 3 0)) % W32,
       (den inp ρ t.list (x.getD 3 0) + den inp ρ t.list (z.getD 0 0)) % W32] := by
    simp only [range4_map, getD4_0, getD4_1, getD4_2, getD4_3]
    rw [den_ext st0.ok.wf (st1.ext.trans (st2.ext.trans st3.ext)) st0.lt, st0.den,
        den_ext st1.ok.wf (st2.ext.trans st3.ext) st1.lt, st1.den, den_ext ok.wf st0.ext x1, den_ext ok.wf st0.ext y2,
        den_ext st2.ok.wf st3.ext st2.lt, st2.den, den_ext ok.wf e01 x2, den_ext ok.wf e01 y3,
        st3.den, den_ext ok.wf e02 x3, den_ext ok.wf e02 z0]
  have eqZ : ((List.range 4).map fun j => den inp ρ t3.list (z.getD j 0)) =
      ((List.range 4).map fun j => den inp ρ t.list (z.getD j 0)) := by
    apply List.map_congr_left; intro j hj
    exact den_ext ok.wf e03 (vec_lt_getD hz lz (List.mem_range.mp hj))
  have d := dnm k hk
  rw [eqL, eqZ] at d
  simpa only [range4_map, getD4_0, getD4_1, getD4_2, getD4_3] using d

theorem wSha256Rnds2_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {x z wk : List Nat}
    (ok : TableOk nv t.list)
    (hx : ∀ i ∈ x, i < t.list.length) (hz : ∀ i ∈ z, i < t.list.length) (hwk : ∀ i ∈ wk, i < t.list.length)
    (lx : x.length = 4) (lz : z.length = 4) (lwk : wk.length = 4) :
    Ext t.list (wSha256Rnds2 x z wk t).2.list ∧ TableOk nv (wSha256Rnds2 x z wk t).2.list ∧
    (∀ i ∈ (wSha256Rnds2 x z wk t).1, i < (wSha256Rnds2 x z wk t).2.list.length) ∧
    ∀ k, k < 4 → (sha256Rnds2 ((List.range 4).map fun j => den inp ρ t.list (x.getD j 0))
                              ((List.range 4).map fun j => den inp ρ t.list (z.getD j 0))
                              ((List.range 4).map fun j => den inp ρ t.list (wk.getD j 0))).getD k 0 =
                 den inp ρ (wSha256Rnds2 x z wk t).2.list ((wSha256Rnds2 x z wk t).1.getD k 0) := by
  unfold wSha256Rnds2 sha256Rnds2
  simp only [range4_map, getD4_0, getD4_1, getD4_2, getD4_3]
  rcases hr1 : wSha256Round (z.getD 3 0) (z.getD 2 0) (x.getD 3 0) (x.getD 2 0)
      (z.getD 1 0) (z.getD 0 0) (x.getD 1 0) (x.getD 0 0) (wk.getD 0 0) t with ⟨⟨a1, b1, c1, d1, e1, f1, g1, h1⟩, t1⟩
  have r1 := wSha256Round_step_eq (inp := inp) (ρ := ρ) hr1 ok
    (vec_lt_getD hz lz (k := 3) (by decide)) (vec_lt_getD hz lz (k := 2) (by decide))
    (vec_lt_getD hx lx (k := 3) (by decide)) (vec_lt_getD hx lx (k := 2) (by decide))
    (vec_lt_getD hz lz (k := 1) (by decide)) (vec_lt_getD hz lz (k := 0) (by decide))
    (vec_lt_getD hx lx (k := 1) (by decide)) (vec_lt_getD hx lx (k := 0) (by decide))
    (vec_lt_getD hwk lwk (k := 0) (by decide))
  rcases hc1 : sha256Round (den inp ρ t.list (z.getD 3 0)) (den inp ρ t.list (z.getD 2 0))
      (den inp ρ t.list (x.getD 3 0)) (den inp ρ t.list (x.getD 2 0))
      (den inp ρ t.list (z.getD 1 0)) (den inp ρ t.list (z.getD 0 0))
      (den inp ρ t.list (x.getD 1 0)) (den inp ρ t.list (x.getD 0 0))
      (den inp ρ t.list (wk.getD 0 0)) with ⟨A1, B1, C1, D1, E1, F1, G1, H1⟩
  rw [hc1] at r1
  rcases hr2 : wSha256Round a1 b1 c1 d1 e1 f1 g1 h1 (wk.getD 1 0) t1 with ⟨⟨a2, b2, c2, d2, e2, f2, g2, h2⟩, t2⟩
  have r2 := wSha256Round_step_eq (inp := inp) (ρ := ρ) hr2 r1.ok
    r1.la r1.lb r1.lc r1.ld r1.le_ r1.lf r1.lg r1.lh
    (Nat.lt_of_lt_of_le (vec_lt_getD hwk lwk (k := 1) (by decide)) r1.ext.le)
  have w1 := den_ext (inp := inp) (ρ := ρ) ok.wf r1.ext (vec_lt_getD hwk lwk (k := 1) (by decide))
  rw [r1.da, r1.db, r1.dc, r1.dd, r1.de, r1.df, r1.dg, r1.dh, w1] at r2
  rcases hc2 : sha256Round A1 B1 C1 D1 E1 F1 G1 H1 (den inp ρ t.list (wk.getD 1 0)) with ⟨A2, B2, C2, D2, E2, F2, G2, H2⟩
  rw [hc2] at r2
  refine ⟨r1.ext.trans r2.ext, r2.ok, list4_lt rfl r2.lf r2.le_ r2.lb r2.la, ?_⟩
  intro k hk
  rcases lt4 hk with rfl | rfl | rfl | rfl
  · simp only [getD4_0]; exact r2.df.symm
  · simp only [getD4_1]; exact r2.de.symm
  · simp only [getD4_2]; exact r2.db.symm
  · simp only [getD4_3]; exact r2.da.symm

theorem wSha256H_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {x y wk : List Nat}
    (ok : TableOk nv t.list)
    (hx : ∀ i ∈ x, i < t.list.length) (hy : ∀ i ∈ y, i < t.list.length) (hwk : ∀ i ∈ wk, i < t.list.length)
    (lx : x.length = 4) (ly : y.length = 4) (lwk : wk.length = 4) :
    Ext t.list (wSha256H x y wk t).2.list ∧ TableOk nv (wSha256H x y wk t).2.list ∧
    (∀ i ∈ (wSha256H x y wk t).1, i < (wSha256H x y wk t).2.list.length) ∧
    ∀ k, k < 4 → (sha256H ((List.range 4).map fun j => den inp ρ t.list (x.getD j 0))
                          ((List.range 4).map fun j => den inp ρ t.list (y.getD j 0))
                          ((List.range 4).map fun j => den inp ρ t.list (wk.getD j 0))).getD k 0 =
                 den inp ρ (wSha256H x y wk t).2.list ((wSha256H x y wk t).1.getD k 0) := by
  unfold wSha256H sha256H
  simp only [range4_map, getD4_0, getD4_1, getD4_2, getD4_3]
  rcases hr1 : wSha256Round (x.getD 0 0) (x.getD 1 0) (x.getD 2 0) (x.getD 3 0)
      (y.getD 0 0) (y.getD 1 0) (y.getD 2 0) (y.getD 3 0) (wk.getD 0 0) t with ⟨⟨a1, b1, c1, d1, e1, f1, g1, h1⟩, t1⟩
  have r1 := wSha256Round_step_eq (inp := inp) (ρ := ρ) hr1 ok
    (vec_lt_getD hx lx (k := 0) (by decide)) (vec_lt_getD hx lx (k := 1) (by decide))
    (vec_lt_getD hx lx (k := 2) (by decide)) (vec_lt_getD hx lx (k := 3) (by decide))
    (vec_lt_getD hy ly (k := 0) (by decide)) (vec_lt_getD hy ly (k := 1) (by decide))
    (vec_lt_getD hy ly (k := 2) (by decide)) (vec_lt_getD hy ly (k := 3) (by decide))
    (vec_lt_getD hwk lwk (k := 0) (by decide))
  rcases hc1 : sha256Round (den inp ρ t.list (x.getD 0 0)) (den inp ρ t.list (x.getD 1 0))
      (den inp ρ t.list (x.getD 2 0)) (den inp ρ t.list (x.getD 3 0))
      (den inp ρ t.list (y.getD 0 0)) (den inp ρ t.list (y.getD 1 0))
      (den inp ρ t.list (y.getD 2 0)) (den inp ρ t.list (y.getD 3 0))
      (den inp ρ t.list (wk.getD 0 0)) with ⟨A1, B1, C1, D1, E1, F1, G1, H1⟩
  rw [hc1] at r1
  rcases hr2 : wSha256Round a1 b1 c1 d1 e1 f1 g1 h1 (wk.getD 1 0) t1 with ⟨⟨a2, b2, c2, d2, e2, f2, g2, h2⟩, t2⟩
  have r2 := wSha256Round_step_eq (inp := inp) (ρ := ρ) hr2 r1.ok
    r1.la r1.lb r1.lc r1.ld r1.le_ r1.lf r1.lg r1.lh
    (Nat.lt_of_lt_of_le (vec_lt_getD hwk lwk (k := 1) (by decide)) r1.ext.le)
  have w1 := den_ext (inp := inp) (ρ := ρ) ok.wf r1.ext (vec_lt_getD hwk lwk (k := 1) (by decide))
  rw [r1.da, r1.db, r1.dc, r1.dd, r1.de, r1.df, r1.dg, r1.dh, w1] at r2
  rcases hc2 : sha256Round A1 B1 C1 D1 E1 F1 G1 H1 (den inp ρ t.list (wk.getD 1 0)) with ⟨A2, B2, C2, D2, E2, F2, G2, H2⟩
  rw [hc2] at r2
  have e12 := r1.ext.trans r2.ext
  rcases hr3 : wSha256Round a2 b2 c2 d2 e2 f2 g2 h2 (wk.getD 2 0) t2 with ⟨⟨a3, b3, c3, d3, e3, f3, g3, h3⟩, t3⟩
  have r3 := wSha256Round_step_eq (inp := inp) (ρ := ρ) hr3 r2.ok
    r2.la r2.lb r2.lc r2.ld r2.le_ r2.lf r2.lg r2.lh
    (Nat.lt_of_lt_of_le (vec_lt_getD hwk lwk (k := 2) (by decide)) e12.le)
  have w2 := den_ext (inp := inp) (ρ := ρ) ok.wf e12 (vec_lt_getD hwk lwk (k := 2) (by decide))
  rw [r2.da, r2.db, r2.dc, r2.dd, r2.de, r2.df, r2.dg, r2.dh, w2] at r3
  rcases hc3 : sha256Round A2 B2 C2 D2 E2 F2 G2 H2 (den inp ρ t.list (wk.getD 2 0)) with ⟨A3, B3, C3, D3, E3, F3, G3, H3⟩
  rw [hc3] at r3
  have e13 := e12.trans r3.ext
  rcases hr4 : wSha256Round a3 b3 c3 d3 e3 f3 g3 h3 (wk.getD 3 0) t3 with ⟨⟨a4, b4, c4, d4, e4, f4, g4, h4⟩, t4⟩
  have r4 := wSha256Round_step_eq (inp := inp) (ρ := ρ) hr4 r3.ok
    r3.la r3.lb r3.lc r3.ld r3.le_ r3.lf r3.lg r3.lh
    (Nat.lt_of_lt_of_le (vec_lt_getD hwk lwk (k := 3) (by decide)) e13.le)
  have w3 := den_ext (inp := inp) (ρ := ρ) ok.wf e13 (vec_lt_getD hwk lwk (k := 3) (by decide))
  rw [r3.da, r3.db, r3.dc, r3.dd, r3.de, r3.df, r3.dg, r3.dh, w3] at r4
  rcases hc4 : sha256Round A3 B3 C3 D3 E3 F3 G3 H3 (den inp ρ t.list (wk.getD 3 0)) with ⟨A4, B4, C4, D4, E4, F4, G4, H4⟩
  rw [hc4] at r4
  refine ⟨e13.trans r4.ext, r4.ok, list4_lt rfl r4.la r4.lb r4.lc r4.ld, ?_⟩
  intro k hk
  rcases lt4 hk with rfl | rfl | rfl | rfl
  · simp only [getD4_0]; exact r4.da.symm
  · simp only [getD4_1]; exact r4.db.symm
  · simp only [getD4_2]; exact r4.dc.symm
  · simp only [getD4_3]; exact r4.dd.symm

theorem wSha256H2_step {inp : Nat → Nat → Nat} {ρ : Nat → Int} {nv : Nat} {t : Tab} {x y wk : List Nat}
    (ok : TableOk nv t.list)
    (hx : ∀ i ∈ x, i < t.list.length) (hy : ∀ i ∈ y, i < t.list.length) (hwk : ∀ i ∈ wk, i < t.list.length)
    (lx : x.length = 4) (ly : y.length = 4) (lwk : wk.length = 4) :
    Ext t.list (wSha256H2 x y wk t).2.list ∧ TableOk nv (wSha256H2 x y wk t).2.list ∧
    (∀ i ∈ (wSha256H2 x y wk t).1, i < (wSha256H2 x y wk t).2.list.length) ∧
    ∀ k, k < 4 → (sha256H2 ((List.range 4).map fun j => den inp ρ t.list (x.getD j 0))
                           ((List.range 4).map fun j => den inp ρ t.list (y.getD j 0))
                           ((List.range 4).map fun j => den inp ρ t.list (wk.getD j 0))).getD k 0 =
                 den inp ρ (wSha256H2 x y wk t).2.list ((wSha256H2 x y wk t).1.getD k 0) := by
  unfold wSha256H2 sha256H2
  simp only [range4_map, getD4_0, getD4_1, getD4_2, getD4_3]
  rcases hr1 : wSha256Round (y.getD 0 0) (y.getD 1 0) (y.getD 2 0) (y.getD 3 0)
      (x.getD 0 0) (x.getD 1 0) (x.getD 2 0) (x.getD 3 0) (wk.getD 0 0) t with ⟨⟨a1, b1, c1, d1, e1, f1, g1, h1⟩, t1⟩
  have r1 := wSha256Round_step_eq (inp := inp) (ρ := ρ) hr1 ok
    (vec_lt_getD hy ly (k := 0) (by decide)) (vec_lt_getD hy ly (k := 1) (by decide))
    (vec_lt_getD hy ly (k := 2) (by decide)) (vec_lt_getD hy ly (k := 3) (by decide))
    (vec_lt_getD hx lx (k := 0) (by decide)) (vec_lt_getD hx lx (k := 1) (by decide))
    (vec_lt_getD hx lx (k := 2) (by decide)) (vec_lt_getD hx lx (k := 3) (by decide))
    (vec_lt_getD hwk lwk (k := 0) (by decide))
  rcases hc1 : sha256Round (den inp ρ t.list (y.getD 0 0)) (den inp ρ t.list (y.getD 1 0))
      (den inp ρ t.list (y.getD 2 0)) (den inp ρ t.list (y.getD 3 0))
      (den inp ρ t.list (x.getD 0 0)) (den inp ρ t.list (x.getD 1 0))
      (den inp ρ t.list (x.getD 2 0)) (den inp ρ t.list (x.getD 3 0))
      (den inp ρ t.list (wk.getD 0 0)) with ⟨A1, B1, C1, D1, E1, F1, G1, H1⟩
  rw [hc1] at r1
  rcases hr2 : wSha256Round a1 b1 c1 d1 e1 f1 g1 h1 (wk.getD 1 0) t1 with ⟨⟨a2, b2, c2, d2, e2, f2, g2, h2⟩, t2⟩
  have r2 := wSha256Round_step_eq (inp := inp) (ρ := ρ) hr2 r1.ok
    r1.la r1.lb r1.lc r1.ld r1.le_ r1.lf r1.lg r1.lh
    (Nat.lt_of_lt_of_le (vec_lt_getD hwk lwk (k := 1) (by decide)) r1.ext.le)
  have w1 := den_ext (inp := inp) (ρ := ρ) ok.wf r1.ext (vec_lt_getD hwk lwk (k := 1) (by decide))
  rw [r1.da, r1.db, r1.dc, r1.dd, r1.de, r1.df, r1.dg, r1.dh, w1] at r2
  rcases hc2 : sha256Round A1 B1 C1 D1 E1 F1 G1 H1 (den inp ρ t.list (wk.getD 1 0)) with ⟨A2, B2, C2, D2, E2, F2, G2, H2⟩
  rw [hc2] at r2
  have e12 := r1.ext.trans r2.ext
  rcases hr3 : wSha256Round a2 b2 c2 d2 e2 f2 g2 h2 (wk.getD 2 0) t2 with ⟨⟨a3, b3, c3, d3, e3, f3, g3, h3⟩, t3⟩
  have r3 := wSha256Round_step_eq (inp := inp) (ρ := ρ) hr3 r2.ok
    r2.la r2.lb r2.lc r2.ld r2.le_ r2.lf r2.lg r2.lh
    (Nat.lt_of_lt_of_le (vec_lt_getD hwk lwk (k := 2) (by decide)) e12.le)
  have w2 := den_ext (inp := inp) (ρ := ρ) ok.wf e12 (vec_lt_getD hwk lwk (k := 2) (by decide))
  rw [r2.da, r2.db, r2.dc, r2.dd, r2.de, r2.df, r2.dg, r2.dh, w2] at r3
  rcases hc3 : sha256Round A2 B2 C2 D2 E2 F2 G2 H2 (den inp ρ t.list (wk.getD 2 0)) with ⟨A3, B3, C3, D3, E3, F3, G3, H3⟩
  rw [hc3] at r3
  have e13 := e12.trans r3.ext
  rcases hr4 : wSha256Round a3 b3 c3 d3 e3 f3 g3 h3 (wk.getD 3 0) t3 with ⟨⟨a4, b4, c4, d4, e4, f4, g4, h4⟩, t4⟩
  have r4 := wSha256Round_step_eq (inp := inp) (ρ := ρ) hr4 r3.ok
    r3.la r3.lb r3.lc r3.ld r3.le_ r3.lf r3.lg r3.lh
    (Nat.lt_of_lt_of_le (vec_lt_getD hwk lwk (k := 3) (by decide)) e13.le)
  have w3 := den_ext (inp := inp) (ρ := ρ) ok.wf e13 (vec_lt_getD hwk lwk (k := 3) (by decide))
  rw [r3.da, r3.db, r3.dc, r3.dd, r3.de, r3.df, r3.dg, r3.dh, w3] at r4
  rcases hc4 : sha256Round A3 B3 C3 D3 E3 F3 G3 H3 (den inp ρ t.list (wk.getD 3 0)) with ⟨A4, B4, C4, D4, E4, F4, G4, H4⟩
  rw [hc4] at r4
  refine ⟨e13.trans r4.ext, r4.ok, list4_lt rfl r4.le_ r4.lf r4.lg r4.lh, ?_⟩
  intro k hk
  rcases lt4 hk with rfl | rfl | rfl | rfl
  · simp only [getD4_0]; exact r4.de.symm
  · simp only [getD4_1]; exact r4.df.symm
  · simp only [getD4_2]; exact r4.dg.symm
  · simp only [getD4_3]; exact r4.dh.symm

theorem vec4_eq_den {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {r : Nat} {x : List Nat}
    (hd : ∀ k, k < 4 → st.vec r k = den (inpOf ctx s0) ρ s.terms (x.getD k 0)) :
    (List.range 4).map (st.vec r) = (List.range 4).map fun j => den (inpOf ctx s0) ρ s.terms (x.getD j 0) :=
  List.map_congr_left fun j hj => hd j (List.mem_range.mp hj)

/-- Hardware SHA-256 vector instructions (`sha256msg1/2`, `sha256su1`, `sha256rnds2`, `sha256h/h2`). -/
theorem symSha256_sound {ctx : Ctx} {s0 : State} (bind : Bind) {s s1 : Sym} {f : String} {args : List Expr} {l : List Nat}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symSha256 bind s f args items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s1 st ∧ ∃ lanes, lanesOf (ctx.contract.perm ctx.pieces s0) bind st (.call f args) = some lanes ∧
      (∀ i ∈ l, i < s1.terms.length) ∧ ∀ k, k < 4 → lanes.getD k 0 = den (inpOf ctx s0) ρ' s1.terms (l.getD k 0) := by
  unfold symSha256 at h
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, more⟩⟩⟩⟩
  · exact (refuse_ok h).elim
  · exact (refuse_ok h).elim
  · cases hx : symVec bind s a <;> cases hy : symVec bind s b <;> simp only [hx, hy] at h
    all_goals try exact (refuse_ok h).elim
    rename_i x y
    obtain ⟨rx, lx, ltx, vax, hdx⟩ := symVec_sound H wf hx
    obtain ⟨ry, ly, lty, vay, hdy⟩ := symVec_sound H wf hy
    split at h
    next hf1 =>
      have fe : f = "sha256msg1" := by simpa using hf1
      subst fe
      obtain ⟨rfl, rfl⟩ := pure_pair h
      obtain ⟨e, ok, lt, dn⟩ := wSha256Msg1_step (inp := inpOf ctx s0) (ρ := ρ) wf.words.ok ltx lty lx ly
      refine ⟨ρ, Carried.terms H wf e ok, sha256Msg1 ((List.range 4).map (st.vec rx)) ((List.range 4).map (st.vec ry)), ?_, lt, ?_⟩
      · simp only [lanesOf, vax, vay, Option.bind_some, Option.map_some]; rfl
      · rw [vec4_eq_den hdx, vec4_eq_den hdy]; exact dn
    next hf1 =>
      split at h
      next hf2 =>
        have fe : f = "sha256msg2" := by simpa using hf2
        subst fe
        obtain ⟨rfl, rfl⟩ := pure_pair h
        obtain ⟨e, ok, lt, dn⟩ := wSha256Msg2_step (inp := inpOf ctx s0) (ρ := ρ) wf.words.ok ltx lty lx ly
        refine ⟨ρ, Carried.terms H wf e ok, sha256Msg2 ((List.range 4).map (st.vec rx)) ((List.range 4).map (st.vec ry)), ?_, lt, ?_⟩
        · simp only [lanesOf, vax, vay, Option.bind_some, Option.map_some]; rfl
        · rw [vec4_eq_den hdx, vec4_eq_den hdy]; exact dn
      next => exact (refuse_ok h).elim
  · cases hx : symVec bind s a <;> cases hy : symVec bind s b <;> cases hz : symVec bind s c <;> simp only [hx, hy, hz] at h
    all_goals try exact (refuse_ok h).elim
    rename_i x y z
    obtain ⟨rx, lx, ltx, vax, hdx⟩ := symVec_sound H wf hx
    obtain ⟨ry, ly, lty, vay, hdy⟩ := symVec_sound H wf hy
    obtain ⟨rz, lz, ltz, vaz, hdz⟩ := symVec_sound H wf hz
    split at h
    next hf1 =>
      have fe : f = "sha256su1" := by simpa using hf1
      subst fe
      obtain ⟨rfl, rfl⟩ := pure_pair h
      obtain ⟨e, ok, lt, dn⟩ := wSha256Su1_step (inp := inpOf ctx s0) (ρ := ρ) wf.words.ok ltx lty ltz lx ly lz
      refine ⟨ρ, Carried.terms H wf e ok, sha256Su1 ((List.range 4).map (st.vec rx)) ((List.range 4).map (st.vec ry)) ((List.range 4).map (st.vec rz)), ?_, lt, ?_⟩
      · simp only [lanesOf, vax, vay, vaz]; rfl
      · rw [vec4_eq_den hdx, vec4_eq_den hdy, vec4_eq_den hdz]; exact dn
    next hf1 =>
      split at h
      next hf2 =>
        have fe : f = "sha256rnds2" := by simpa using hf2
        subst fe
        obtain ⟨rfl, rfl⟩ := pure_pair h
        obtain ⟨e, ok, lt, dn⟩ := wSha256Rnds2_step (inp := inpOf ctx s0) (ρ := ρ) wf.words.ok ltx lty ltz lx ly lz
        refine ⟨ρ, Carried.terms H wf e ok, sha256Rnds2 ((List.range 4).map (st.vec rx)) ((List.range 4).map (st.vec ry)) ((List.range 4).map (st.vec rz)), ?_, lt, ?_⟩
        · simp only [lanesOf, vax, vay, vaz]; rfl
        · rw [vec4_eq_den hdx, vec4_eq_den hdy, vec4_eq_den hdz]; exact dn
      next hf2 =>
        split at h
        next hf3 =>
          have fe : f = "sha256h" := by simpa using hf3
          subst fe
          obtain ⟨rfl, rfl⟩ := pure_pair h
          obtain ⟨e, ok, lt, dn⟩ := wSha256H_step (inp := inpOf ctx s0) (ρ := ρ) wf.words.ok ltx lty ltz lx ly lz
          refine ⟨ρ, Carried.terms H wf e ok, sha256H ((List.range 4).map (st.vec rx)) ((List.range 4).map (st.vec ry)) ((List.range 4).map (st.vec rz)), ?_, lt, ?_⟩
          · simp only [lanesOf, vax, vay, vaz]; rfl
          · rw [vec4_eq_den hdx, vec4_eq_den hdy, vec4_eq_den hdz]; exact dn
        next hf3 =>
          split at h
          next hf4 =>
            have fe : f = "sha256h2" := by simpa using hf4
            subst fe
            obtain ⟨rfl, rfl⟩ := pure_pair h
            obtain ⟨e, ok, lt, dn⟩ := wSha256H2_step (inp := inpOf ctx s0) (ρ := ρ) wf.words.ok ltx lty ltz lx ly lz
            refine ⟨ρ, Carried.terms H wf e ok, sha256H2 ((List.range 4).map (st.vec rx)) ((List.range 4).map (st.vec ry)) ((List.range 4).map (st.vec rz)), ?_, lt, ?_⟩
            · simp only [lanesOf, vax, vay, vaz]; rfl
            · rw [vec4_eq_den hdx, vec4_eq_den hdy, vec4_eq_den hdz]; exact dn
          next => exact (refuse_ok h).elim
  · exact (refuse_ok h).elim

/-- What the verifier takes the four words to be that a row sets a vector register to: the machine sets
those lanes. -/
theorem symLanes_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) {s s1 : Sym} {v : Expr} {l : List Nat}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symLanes ctx bind s v items = .ok ((l, s1), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s1 st ∧ ∃ lanes, lanesOf (ctx.contract.perm ctx.pieces s0) bind st v = some lanes ∧
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
      have fe : f = "mem128" := by simpa using hf
      subst f
      obtain ⟨vs, vv, al, c, _, lt, dn⟩ := symMemWords_sound E H wf (by decide) h
      let a := sumList vs % M64
      refine ⟨ρ, c, (List.range 4).map (fun i => Ode.load st.mem (a + 4 * i) 4), ?_, lt, ?_⟩
      · simp [lanesOf, vv, al, a]
      · intro k hk
        rw [← dn k hk]
        rcases lt4 hk with rfl | rfl | rfl | rfl <;> rfl
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
          obtain ⟨a0, _, va, _⟩ := symNumber_sound (perm := ctx.contract.perm ctx.pieces s0) (st := st) ha
          obtain ⟨b0, _, vb, _⟩ := symNumber_sound (perm := ctx.contract.perm ctx.pieces s0) (st := st) hb
          obtain ⟨c0, _, vc, _⟩ := symNumber_sound (perm := ctx.contract.perm ctx.pieces s0) (st := st) hc
          obtain ⟨d0, _, vd, _⟩ := symNumber_sound (perm := ctx.contract.perm ctx.pieces s0) (st := st) hd
          obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := wAtom) (val := fun r => (ev ρ r % W32i).toNat) (inp := inpOf ctx s0) (ρ := ρ)
            (nv := s.nvars) (T0 := s.terms) [Lin.const ka, Lin.const kb, Lin.const kc, Lin.const kd] s.tab
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
          · cases hx : symReg ctx bind s a with
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
              next hf6 =>
                split at h
                next hf7 => exact symSha256_sound bind h H wf
                next hf7 => exact symMoved_sound bind h H wf

/-! ## Store a run of words -/

theorem store_at : ∀ (n : Nat) (mem : Nat → Byte) (a v b : Nat), b < n → store mem a v n (a + b) = v / 256 ^ b % 256
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

theorem storeWords_other (mem : Nat → Byte) (a : Nat) (ls : List Nat) (y : Nat) (h : y < a ∨ a + 4 * ls.length ≤ y) :
    storeWords mem a ls y = mem y := by
  induction ls generalizing a mem with
  | nil => rfl
  | cons v ls ih =>
    simp only [List.length_cons] at h
    rw [storeWords, ih _ _ (by omega), store_other _ _ _ _ _ (by omega)]

theorem storeWords_at (mem : Nat → Byte) (a : Nat) (ls : List Nat) (i b : Nat) (hi : i < ls.length) (hb : b < 4) :
    storeWords mem a ls (a + 4 * i + b) = ls.getD i 0 / 256 ^ b % 256 := by
  induction ls generalizing mem a i with
  | nil => simp at hi
  | cons v ls ih =>
    simp only [List.length_cons] at hi
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, storeWords, List.getD, List.getElem?_cons_zero, Option.getD_some]
      rw [storeWords_other _ _ _ _ (by omega)]
      exact store_at 4 mem a v b hb
    | succ i =>
      have e : a + 4 * (i + 1) + b = a + 4 + 4 * i + b := by omega
      rw [e, storeWords, ih _ _ _ (by omega)]
      rfl

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

/-- A store replaces the words at its destination and preserves facts about other words and runs. -/
theorem Holds.storeRunWords {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) {w : Nat} {name : String} {r n : Nat} (hw : ctx.contract.outs[w]? = some (name, r, n))
    {c : Nat} {l lanes : List Nat} (hl : lanes.length = l.length)
    (hc4 : c % 4 = 0) (hcn : c + 4 * l.length ≤ n) (hnw : (s.wrote.any fun e => e.1 == w) = false)
    (hd : ∀ k, k < l.length → lanes.getD k 0 = den (inpOf ctx s0) ρ s.terms (l.getD k 0))
    (a : Nat) (ha : a = s0.reg r + c) :
    Holds ctx s0 ρ (rememberStore s w (c / 4) l) { st with mem := storeWords st.mem a lanes } where
  range := fun _ h => nomatch h
  vecIntact := H.vecIntact
  entry := H.entry
  data := H.data
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
    have hs := E.stackAt
    have ho := (E.outAt (List.mem_of_getElem? hw)).2
    have e : load (storeWords st.mem a lanes) ((s0.reg RSP : Int) + o').toNat 8 = load st.mem ((s0.reg RSP : Int) + o').toNat 8 :=
      load_congr _ _ _ _ (fun y h1 h2 => storeWords_other _ _ _ _ (by omega))
    show ((load (storeWords st.mem a lanes) ((s0.reg RSP : Int) + o').toNat 8 : Nat) : Int) = ev ρ v
    rw [e]; exact g3
  frameW o' i m := by
    obtain ⟨g1, g2, g3⟩ := H.frameW o' i m
    refine ⟨g1, g2, ?_⟩
    have hs := E.stackAt
    have ho := (E.outAt (List.mem_of_getElem? hw)).2
    have e : load (storeWords st.mem a lanes) ((s0.reg RSP : Int) + o').toNat 4 = load st.mem ((s0.reg RSP : Int) + o').toNat 4 :=
      load_congr _ _ _ _ (fun y h1 h2 => storeWords_other _ _ _ _ (by omega))
    rw [e]; exact g3
  mem y hy ho' := by
    show storeWords st.mem a lanes y = s0.mem y
    have hne : y < a ∨ a + 4 * lanes.length ≤ y := by
      refine Decidable.by_contra fun hin => ?_
      have : ctx.contract.inOut s0 y = true := by
        unfold Contract.inOut
        exact List.any_eq_true.mpr ⟨(name, r, n), List.mem_of_getElem? hw, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
      rw [this] at ho'; cases ho'
    rw [storeWords_other _ _ _ _ hne]
    exact H.mem y hy ho'
  wrote w' o' v m := by
    obtain ⟨name', r', n', g1, g2, g3, g4⟩ := H.wrote w' o' v m
    refine ⟨name', r', n', g1, g2, g3, ?_⟩
    have ne' : w' ≠ w := by
      intro e
      rw [e] at m
      exact (List.any_eq_false.mp hnw) _ m (by simp)
    have := E.outOut hw g1 (Ne.symm ne')
    show (storeWords st.mem a lanes (s0.reg r' + (ev ρ o').toNat) : Int) = ev ρ v
    rw [storeWords_other _ _ _ _ (by omega)]
    exact g4
  words := by
    refine ⟨H.words.vec, ?_, ?_, (fun _ _ h => nomatch h)⟩
    · intro w' m x' r' n' g1 k hk'
      obtain ⟨m', ne⟩ := List.mem_filter.mp m
      have ne' : w' ≠ w := by simpa using ne
      have := E.outOut hw g1 (Ne.symm ne')
      show storeWords st.mem a lanes (s0.reg r' + k) = s0.mem (s0.reg r' + k)
      rw [storeWords_other _ _ _ _ (by omega)]
      exact H.words.intact w' m' x' r' n' g1 k hk'
    · intro w' j i m x' r' n' g1
      rcases List.mem_append.mp m with m | m
      · obtain ⟨q, mq, eq⟩ := List.mem_map.mp m
        have hq : q < l.length := List.mem_range.mp mq
        injection eq with e1 e2
        injection e2 with e2 e3
        subst e1 e2 e3
        rw [hw] at g1
        injection g1 with g1; injection g1 with _ g1; injection g1 with g1 gn
        subst g1 gn
        refine ⟨by omega, fun b hb => ?_⟩
        show (storeWords st.mem a lanes (s0.reg r + 4 * (c / 4 + q) + b)).val = _
        have e : s0.reg r + 4 * (c / 4 + q) + b = a + 4 * q + b := by omega
        rw [e, storeWords_at _ _ _ _ _ (by omega) hb, hd q hq]
        rfl
      · obtain ⟨m', keep⟩ := List.mem_filter.mp m
        obtain ⟨g2, g3⟩ := H.words.wrote w' j i m' x' r' n' g1
        refine ⟨g2, fun b hb => ?_⟩
        show (storeWords st.mem a lanes (s0.reg r' + 4 * j + b)).val = _
        have hne : s0.reg r' + 4 * j + b < a ∨ a + 4 * lanes.length ≤ s0.reg r' + 4 * j + b := by
          by_cases e : w' = w
          · subst e
            rw [hw] at g1
            injection g1 with g1; injection g1 with _ g1; injection g1 with g1 gn
            subst g1 gn
            simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at keep
            omega
          · have := E.outOut hw g1 (Ne.symm e)
            omega
        rw [storeWords_other _ _ _ _ hne]
        exact g3 b hb
  known := H.known

theorem load_storeWords_at (mem : Nat → Byte) (a : Nat) (ls : List Nat) (i : Nat)
    (hi : i < ls.length) (hlt : ls.getD i 0 < W32) :
    load (storeWords mem a ls) (a + 4 * i) 4 = ls.getD i 0 := by
  have b0 := storeWords_at mem a ls i 0 hi (by decide)
  have b1 := storeWords_at mem a ls i 1 hi (by decide)
  have b2 := storeWords_at mem a ls i 2 hi (by decide)
  have b3 := storeWords_at mem a ls i 3 hi (by decide)
  simp only [load]
  rw [show a + 4 * i = a + 4 * i + 0 by omega, b0]
  rw [show a + 4 * i + 0 + 1 = a + 4 * i + 1 by omega, b1]
  rw [show a + 4 * i + 1 + 1 = a + 4 * i + 2 by omega, b2]
  rw [show a + 4 * i + 2 + 1 = a + 4 * i + 3 by omega, b3]
  unfold W32 at hlt; omega

/-- A vector store into the stack frame updates `frameW` and keeps disjoint `frame`, `frameW`, and output runs. -/
theorem Holds.storeFrameWords {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) {o : Int} {width a : Nat} {l lanes : List Nat}
    (hst : -(ctx.contract.stack : Int) ≤ o) (ho0 : o + 4 * (width : Int) ≤ 0)
    (ha : (a : Int) = (s0.reg RSP : Int) + o)
    (hl : lanes.length = width) (hd : ∀ k, k < width → lanes.getD k 0 = den (inpOf ctx s0) ρ s.terms (l.getD k 0)) :
    Holds ctx s0 ρ { s with
      spill := [], range := none,
      frame := s.frame.filter fun (c, _) => decide (c + 8 ≤ o) || decide (o + 4 * (width : Int) ≤ c),
      frameW := ((List.range width).map fun (k : Nat) => (o + 4 * (k : Int), l.getD k 0)) ++
                s.frameW.filter fun (c, _) => decide (c + 4 ≤ o) || decide (o + 4 * (width : Int) ≤ c) }
      { st with mem := storeWords st.mem a lanes } where
  range := fun _ h => nomatch h
  vecIntact := H.vecIntact
  entry := H.entry
  data := H.data
  reg := H.reg
  small := H.small
  zf := H.zf
  cf := H.cf
  facts := H.facts
  spec := H.spec
  bytes := H.bytes
  frame c v m := by
    obtain ⟨m, hk⟩ := List.mem_filter.mp m
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
    obtain ⟨g1, g2, g3⟩ := H.frame c v m
    have hs := E.stackAt
    refine ⟨g1, g2, ?_⟩
    have e : load (storeWords st.mem a lanes) ((s0.reg RSP : Int) + c).toNat 8 = load st.mem ((s0.reg RSP : Int) + c).toNat 8 :=
      load_congr _ _ _ _ (fun y h1 h2 => storeWords_other _ _ _ _ (by omega))
    show ((load (storeWords st.mem a lanes) ((s0.reg RSP : Int) + c).toNat 8 : Nat) : Int) = ev ρ v
    rw [e]; exact g3
  frameW c i m := by
    have hs := E.stackAt
    have hle := Contract.stack_le_stackAt ctx.contract s0
    rcases List.mem_append.mp m with m | m
    · obtain ⟨k, mk, eq⟩ := List.mem_map.mp m
      have hk : k < width := List.mem_range.mp mk
      injection eq with e1 e2; subst e1 e2
      refine ⟨by omega, by omega, ?_⟩
      have ea : ((s0.reg RSP : Int) + (o + 4 * (k : Int))).toNat = a + 4 * k := by omega
      rw [ea, load_storeWords_at st.mem a lanes k (by omega) (by rw [hd k hk]; exact den_lt wf.words.table (inpOf_lt ctx s0) wf.words.rotrs _)]
      exact hd k hk
    · obtain ⟨m, hk⟩ := List.mem_filter.mp m
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
      obtain ⟨g1, g2, g3⟩ := H.frameW c i m
      refine ⟨g1, g2, ?_⟩
      have e : load (storeWords st.mem a lanes) ((s0.reg RSP : Int) + c).toNat 4 = load st.mem ((s0.reg RSP : Int) + c).toNat 4 :=
        load_congr _ _ _ _ (fun y h1 h2 => storeWords_other _ _ _ _ (by omega))
      rw [e]; exact g3
  mem y hy ho' := by
    have hs := E.stackAt
    have hle := Contract.stack_le_stackAt ctx.contract s0
    simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hy
    show storeWords st.mem a lanes y = s0.mem y
    rw [storeWords_other _ _ _ _ (by omega)]
    exact H.mem y (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; exact hy) ho'
  wrote w' o' v m := by
    obtain ⟨name', r', n', g1, g2, g3, g4⟩ := H.wrote w' o' v m
    have hs := E.stack
    have ho := (E.out (List.mem_of_getElem? g1)).2
    refine ⟨name', r', n', g1, g2, g3, ?_⟩
    show (storeWords st.mem a lanes (s0.reg r' + (ev ρ o').toNat) : Int) = ev ρ v
    rw [storeWords_other _ _ _ _ (by omega)]
    exact g4
  words := by
    have hs := E.stack
    refine ⟨H.words.vec, ?_, ?_, (fun _ _ h => nomatch h)⟩
    · intro w' m x' r' n' g1 k hk'
      have ho := (E.out (List.mem_of_getElem? g1)).2
      show storeWords st.mem a lanes (s0.reg r' + k) = s0.mem (s0.reg r' + k)
      rw [storeWords_other _ _ _ _ (by omega)]
      exact H.words.intact w' m x' r' n' g1 k hk'
    · intro w' j i m x' r' n' g1
      obtain ⟨g2, g3⟩ := H.words.wrote w' j i m x' r' n' g1
      have ho := (E.out (List.mem_of_getElem? g1)).2
      refine ⟨g2, fun b hb => ?_⟩
      show (storeWords st.mem a lanes (s0.reg r' + 4 * j + b)).val = _
      rw [storeWords_other _ _ _ _ (by omega)]
      exact g3 b hb
  known := H.known

theorem symStoreWords_sound {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s s' : Sym}
    {addr : Row} {l lanes : List Nat} {width a : Nat} {items rest : Items} (E : Setting ctx p s0)
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (nonempty : 0 < width)
    (h : symStoreWords ctx s addr l width items = .ok (s', rest))
    (ha : ∀ A : Nat, (A : Int) = ev ρ addr → A < M64 → a = A)
    (hl : lanes.length = width) (hlt : ∀ i ∈ l, i < s.terms.length)
    (hd : ∀ k, k < width → lanes.getD k 0 = den (inpOf ctx s0) ρ s.terms (l.getD k 0)) :
    allowed (ctx.contract.perm ctx.pieces s0).write a (4 * width) = true ∧
      Carried ctx s0 ρ s ρ s' { st with mem := storeWords st.mem a lanes } := by
  simp only [symStoreWords] at h
  cases hfo : findOut addr ctx.contract.outs 0 with
  | none =>
    simp only [hfo] at h
    cases hc : Lin.isConst (Lin.sub addr (Lin.var RSP)) with
    | none => simp only [hc] at h; exact (refuse_ok h).elim
    | some o =>
      cases hsp : s.sp with
      | none => simp only [hc, hsp] at h; exact (refuse_ok h).elim
      | some sp =>
        simp only [hc, hsp] at h
        split at h
        next hcond =>
          obtain ⟨hst, hso, ho0, hlen⟩ := hcond
          have len : l.length = width := by simpa using hlen
          have hs := V.pure_ok h
          injection hs with h1 _; subst s'
          have hrsp : ρ RSP = s0.reg RSP := H.entry RSP ctx.rsp_lt
          have eoff := ev_isConst (ρ := ρ) hc
          rw [ev_sub, ev_var, hrsp] at eoff
          have hsmall := E.small RSP
          have hstack := E.stack
          have hle := Contract.stack_le_stackAt ctx.contract s0
          have hA : a = ((s0.reg RSP : Int) + o).toNat := ha ((s0.reg RSP : Int) + o).toNat (by omega) (by unfold M64 at hsmall ⊢; omega)
          have hAi : (a : Int) = (s0.reg RSP : Int) + o := by omega
          refine ⟨allowed_of _ _ _ ?_, ⟨Agree.refl _ _, Nat.le_refl _,
            H.storeFrameWords E wf hst ho0 hAi hl hd, ?_⟩⟩
          · intro y hy1 hy2
            simp only [Contract.perm, Bool.or_eq_true]
            left; simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]; omega
          · exact ⟨wf.base, wf.reg, wf.zf, wf.cf,
              fun c v m => wf.frame c v (List.mem_filter.mp m).1,
              fun c i m => by
                rcases List.mem_append.mp m with m | m
                · obtain ⟨k, mk, eq⟩ := List.mem_map.mp m
                  have hk : k < width := List.mem_range.mp mk
                  injection eq with _ e2; subst e2
                  rw [getD_index (by omega)]
                  exact hlt _ (List.getElem_mem (by omega))
                · exact wf.frameW c i (List.mem_filter.mp m).1,
              wf.facts, wf.bytes, wf.spec, wf.wrote,
              wf.words.mono rfl rfl rfl (Nat.le_refl _) (Or.inr rfl), wf.known, fun _ h => nomatch h⟩
        next => exact (refuse_ok h).elim
  | some w0 =>
    obtain ⟨w, off, name, r, n, rfl, _, hw, ho⟩ := findOut_spec hfo
    have hw' : ctx.contract.outs[w]? = some (name, r, n) := by simpa using hw
    simp only [hfo, hw'] at h
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
            have hs := V.pure_ok h
            injection hs with h1 _; subst s'
            have hc3 : 0 ≤ c ∧ c % 4 = 0 ∧ c + 4 * width ≤ n := by simpa using hcond
            have hnw' : (s.wrote.any fun e => e.1 == w) = false := by
              cases hb : (s.wrote.any fun e => e.1 == w) with
              | false => rfl
              | true => exact (hnw hb).elim
            have len : l.length = width := by simpa using hlen
            have hm := List.mem_of_getElem? hw'
            have fit := (E.out hm).1
            have hr : ρ r = s0.reg r := H.entry r (outs_lt hm)
            have eoff := ev_isConst (ρ := ρ) hc
            rw [ho, ev_sub, ev_var, hr] at eoff
            have hA : a = s0.reg r + c.toNat := ha _ (by omega) (by unfold M64 at fit ⊢; omega)
            refine ⟨allowed_of _ _ _ ?_, ⟨Agree.refl _ _, Nat.le_refl _,
              H.storeRunWords E hw' (c := c.toNat) (hl.trans len.symm) (by omega) (by omega) hnw' (fun k hk => hd k (by omega)) a hA, ?_⟩⟩
            · intro y hy1 hy2
              simp only [Contract.perm, Bool.or_eq_true]
              right
              unfold Contract.inOut
              exact List.any_eq_true.mpr ⟨(name, r, n), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
            · exact ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.frameW, wf.facts, wf.bytes, wf.spec, wf.wrote,
                ⟨wf.words.table, wf.words.atoms, wf.words.vec, wf.words.rotrs,
                 fun w' j i m => by
                   rcases List.mem_append.mp m with m | m
                   · obtain ⟨q, mq, eq⟩ := List.mem_map.mp m
                     injection eq with _ e2
                     injection e2 with _ e3
                     rw [← e3, getD_index (List.mem_range.mp mq)]
                     exact hlt _ (List.getElem_mem (List.mem_range.mp mq))
                   · exact wf.words.wrote w' j i (List.mem_filter.mp m).1,
                 fun _ _ hs => nomatch hs⟩, wf.known, fun _ h => nomatch h⟩

/-! ## A row that sets a vector register, or stores one -/

theorem forgetHigh_lookup {vec : List (Nat × List Nat)} {x : Nat} {ids : List Nat}
    (h : (forgetHigh vec).lookup x = some ids) :
    ∃ old, vec.lookup x = some old ∧ ids = (if x < 16 then old.take 4 else old) := by
  induction vec with
  | nil => simp [forgetHigh] at h
  | cons p ps ih =>
    obtain ⟨r, lanes⟩ := p
    change ((r, if r < 16 then lanes.take 4 else lanes) :: forgetHigh ps).lookup x = _ at h
    rcases lookup_cons_cases h with ⟨rfl, eq⟩ | ⟨ne, tail⟩
    · exact ⟨lanes, List.lookup_cons_self, eq⟩
    · obtain ⟨old, ho, eq⟩ := ih tail
      have bn : (x == r) = false := by simpa using ne
      exact ⟨old, by simpa only [List.lookup, bn] using ho, eq⟩

theorem symVset_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) {s s' : Sym} {place v : Expr}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symStmt ctx bind s (.vset place v) items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (base u : Nat) :
    ∃ ρ' st', Carried ctx s0 ρ s ρ' s' st' ∧ execStmt (ctx.contract.perm ctx.pieces s0) bind base u st (.vset place v) = some st' ∧
      st'.rip = st.rip := by
  simp only [symStmt] at h
  cases place with
  | number _ => exact (refuse_ok h).elim
  | lane _ _ => exact (refuse_ok h).elim
  | name n =>
    dsimp only at h
    split at h
    next hn =>
      split at h
      next hu =>
        have := V.pure_ok h
        injection this with h1 _
        subst h1
        refine ⟨ρ, { st with vec := fun x k => if k < 4 ∨ 16 ≤ x then st.vec x k else u / W32 ^ (16 * x + k) % W32 },
          ⟨Agree.refl _ _, Nat.le_refl _, ?_, ?_⟩, ?_, rfl⟩
        · exact ⟨H.entry, H.data, H.reg, H.small, H.zf, H.cf, H.frame, H.frameW, H.facts, H.bytes, H.spec, H.mem, H.wrote,
            ⟨fun x ids hx k hk => by
               obtain ⟨old, ho, rfl⟩ := forgetHigh_lookup hx
               show (if k < 4 ∨ 16 ≤ x then st.vec x k else _) = _
               by_cases low : x < 16
               · rw [ite_eq_left low, List.length_take] at hk
                 have h4 : k < 4 := by omega
                 rw [ite_eq_left (Or.inl h4), ite_eq_left low]
                 simpa only [List.getD, List.getElem?_take_of_lt h4] using H.words.vec x old ho k (by omega)
               · rw [ite_eq_left (Or.inr (by omega)), ite_eq_right low]
                 rw [ite_eq_right low] at hk
                 exact H.words.vec x old ho k hk,
             H.words.intact, H.words.wrote, H.words.spill⟩, H.known, H.range,
            fun x hx => by
              have h16 : 16 ≤ x := by have := (List.mem_filter.mp hx).2; simpa using this
              funext k; simp only [ite_eq_left (Or.inr h16)]
              exact congrFun (H.vecIntact x (List.mem_filter.mp hx).1) k⟩
        · exact ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.frameW, wf.facts, wf.bytes, wf.spec, wf.wrote,
            ⟨wf.words.table, wf.words.atoms,
             fun x ids hx => by
               obtain ⟨old, ho, rfl⟩ := forgetHigh_lookup hx
               obtain ⟨len, lt⟩ := wf.words.vec x old ho
               split
               · exact ⟨Or.inl (by rw [List.length_take]; omega), fun i m => lt i (List.mem_of_mem_take m)⟩
               · exact ⟨len, lt⟩,
             wf.words.rotrs, wf.words.wrote, wf.words.spill⟩, wf.known, wf.range⟩
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
          · exact ⟨c.holds.entry, c.holds.data, c.holds.reg, c.holds.small, c.holds.zf, c.holds.cf, c.holds.frame, c.holds.frameW, c.holds.facts, c.holds.bytes,
              c.holds.spec, c.holds.mem, c.holds.wrote,
              ⟨fun x ids hx k hk => by
                 show (if x = r then (if k < 4 then lanes.getD k 0 else _) else st.vec x k) = _
                 rcases lookup_cons_cases hx with ⟨e, e2⟩ | ⟨ne, hx'⟩
                 · have h4 : k < 4 := by simpa only [e2, len] using hk
                   rw [if_pos e, if_pos h4, e2]; exact dn k h4
                 · rw [if_neg ne]; exact c.holds.words.vec x ids hx' k hk,
               c.holds.words.intact, c.holds.words.wrote, c.holds.words.spill⟩, c.holds.known, c.holds.range,
              fun x hx => by
                have hne : x ≠ r := by have := (List.mem_filter.mp hx).2; simpa using this
                funext k; simp only [setVec, ite_eq_right hne]
                exact congrFun (c.holds.vecIntact x (List.mem_filter.mp hx).1) k⟩
          · exact ⟨c.wf.base, c.wf.reg, c.wf.zf, c.wf.cf, c.wf.frame, c.wf.frameW, c.wf.facts, c.wf.bytes, c.wf.spec, c.wf.wrote,
              ⟨c.wf.words.table, c.wf.words.atoms,
               fun x ids hx => by
                 rcases lookup_cons_cases hx with ⟨e, e2⟩ | ⟨ne, hx'⟩
                 · rw [e2]; exact ⟨Or.inl len, lt⟩
                 · exact c.wf.words.vec x ids hx',
               c.wf.words.rotrs, c.wf.words.wrote, c.wf.words.spill⟩, c.wf.known, c.wf.range⟩
          · simp [execStmt, hn, hr, hl]
        next => exact (refuse_ok h).elim
  | call f args =>
    rcases args with _ | ⟨b, _ | ⟨n, _ | ⟨c', more⟩⟩⟩
    · exact (refuse_ok h).elim
    · exact (refuse_ok h).elim
    · dsimp only at h
      split at h
      next hf =>
        cases hl : symVec bind s v <;> cases hx : symReg ctx bind s b <;> cases hk : symNumber bind n <;> simp only [hl, hx, hk] at h
        all_goals try exact (refuse_ok h).elim
        rename_i l x k
        obtain ⟨rv, _, lt, hv, hd⟩ := symVec_sound H wf hl
        obtain ⟨xb, vs, ha⟩ := wordAddress_sound H wf hx hk
        let lanes := [st.vec rv 0, st.vec rv 1, st.vec rv 2, st.vec rv 3]
        obtain ⟨al, c⟩ := symStoreWords_sound (lanes := lanes) E H wf (by decide) h ha rfl lt (fun j hj => by
          simp only [lanes, vec4_getD hj, hd j hj])
        refine ⟨ρ, _, c, ?_, rfl⟩
        simp [execStmt, vs, hv, sumList, al, storeWords, lanes, Nat.add_assoc]
      next => exact (refuse_ok h).elim
    · exact (refuse_ok h).elim

end Ode
