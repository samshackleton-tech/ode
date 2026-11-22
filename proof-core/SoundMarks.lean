/-
The marks, of the verifier: what `Sym.q` says is not marked is not marked in the machine.

The rules of the verifier (what a statement does to values) are shown of `execStmt`, which changes no
mark: the machine brings the marks up to date after a statement (`noted`). So what is shown here stands
beside what is shown of the rules, and does not go through them.
-/
import SoundLoop
import Trace

namespace Ode
open Arithmetic

/-- The cells of the frame the verifier has as not marked are in the frame, and none of their bytes is
marked. -/
def CellsOk (ctx : Ctx) (s0 : State) (fq : List Int) (m : Nat → Bool) : Prop :=
  ∀ c ∈ fq, -(ctx.contract.stack : Int) ≤ c ∧ c + 8 ≤ 0 ∧ ∀ k, k < 8 → m (((s0.reg RSP : Int) + c).toNat + k) = false

theorem CellsOk.nil {ctx : Ctx} {s0 : State} {m : Nat → Bool} : CellsOk ctx s0 [] m := fun _ h => by cases h

/-- What the verifier knows of the marks is so of the machine's state: each register it has as not marked
is not marked; a flag it has as not marked is not marked; each cell of the frame it has as not marked is
not marked; and every byte of memory outside the frame and the runs given to write is marked as it was at
entry. -/
structure MarksOk (ctx : Ctx) (s0 : State) (q : SMarks) (st : State) : Prop where
  reg : ∀ r ∈ q.regq, st.marks.reg r = false
  zf : q.zq = true → st.marks.zf = false
  cf : q.cq = true → st.marks.cf = false
  stable : ∀ a, ctx.contract.inFrame s0 a = false → ctx.contract.inOut s0 a = false → st.marks.mem a = s0.marks.mem a
  frame : CellsOk ctx s0 q.fq st.marks.mem

theorem MarksOk.fields {ctx : Ctx} {s0 : State} {q : SMarks} {st st' : State} (M : MarksOk ctx s0 q st)
    (h : st'.marks = st.marks) : MarksOk ctx s0 q st' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [h]
  · exact M.reg
  · exact M.zf
  · exact M.cf
  · exact M.stable
  · exact M.frame

theorem anyMarked_none {m : Nat → Bool} : ∀ (n a : Nat), (∀ x, a ≤ x → x < a + n → m x = false) → anyMarked m a n = false
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [anyMarked, h a (Nat.le_refl _) (by omega), Bool.false_or]
    exact anyMarked_none n (a + 1) fun x h1 h2 => h x (by omega) (by omega)

/-! ## Expressions made of nothing marked -/

mutual
  theorem clean_sound {bind : Bind} {q : List Nat} {st : State} (hq : ∀ r ∈ q, st.marks.reg r = false) :
      ∀ (e : Expr), cleanExpr bind q e = true → exprMark bind st e = false ∧ addrsQuiet bind st e = true
    | .number _, _ => ⟨rfl, rfl⟩
    | .lane _ _, h => by simp [cleanExpr] at h
    | .name n, h => by
      refine ⟨?_, rfl⟩
      simp only [cleanExpr, Bool.or_eq_true] at h
      simp only [exprMark]
      split
      · rfl
      next hn =>
        rcases h with h | h
        · exact absurd h hn
        · cases hr : regOf bind n with
          | none => simp [hr] at h
          | some r =>
            simp only [hr] at h ⊢
            exact hq r (List.contains_iff_mem.mp h)
    | .call f args, h => by
      simp only [cleanExpr, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      obtain ⟨e1, e2⟩ := cleanAll_sound hq args h.2
      exact ⟨by simp only [exprMark, e1, h.1, Bool.false_or], by simp only [addrsQuiet, e2, h.1, Option.isNone_none, Bool.true_or, Bool.and_true]⟩
  theorem cleanAll_sound {bind : Bind} {q : List Nat} {st : State} (hq : ∀ r ∈ q, st.marks.reg r = false) :
      ∀ (es : List Expr), cleanAll bind q es = true → exprMarks bind st es = false ∧ addrsQuietAll bind st es = true
    | [], _ => ⟨rfl, rfl⟩
    | e :: es, h => by
      simp only [cleanAll, Bool.and_eq_true] at h
      obtain ⟨a1, a2⟩ := clean_sound hq e h.1
      obtain ⟨b1, b2⟩ := cleanAll_sound hq es h.2
      exact ⟨by simp only [exprMarks, a1, b1, Bool.or_false], by simp only [addrsQuietAll, a2, b2, Bool.and_true]⟩
end

mutual
  theorem quietS_sound {bind : Bind} {q : List Nat} {st : State} (hq : ∀ r ∈ q, st.marks.reg r = false) :
      ∀ (e : Expr), quietExprS bind q e = true → addrsQuiet bind st e = true
    | .number _, _ => rfl
    | .lane _ _, _ => rfl
    | .name _, _ => rfl
    | .call f args, h => by
      simp only [quietExprS, Bool.and_eq_true, Bool.or_eq_true] at h
      have e1 := quietAllS_sound hq args h.1
      rcases h.2 with hw | hc
      · simp only [addrsQuiet, e1, hw, Bool.true_or, Bool.and_true]
      · simp only [addrsQuiet, e1, (cleanAll_sound hq args hc).1, Bool.not_false, Bool.or_true, Bool.and_true]
  theorem quietAllS_sound {bind : Bind} {q : List Nat} {st : State} (hq : ∀ r ∈ q, st.marks.reg r = false) :
      ∀ (es : List Expr), quietAllS bind q es = true → addrsQuietAll bind st es = true
    | [], _ => rfl
    | e :: es, h => by
      simp only [quietAllS, Bool.and_eq_true] at h
      simp only [addrsQuietAll, quietS_sound hq e h.1, quietAllS_sound hq es h.2, Bool.and_true]
end

/-! ## A load of memory given to read only -/

theorem notFrame {ctx : Ctx} {s0 : State} {a : Nat} (h : a < s0.reg RSP - ctx.contract.stack ∨ s0.reg RSP ≤ a) :
    ctx.contract.inFrame s0 a = false := by
  simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- A part of an address that is a register or a number: what it is worth in the machine is what its row
is worth. -/
theorem plainRow_value {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF s)
    {bind : Bind} {e : Expr} {x : Row} (h : plainRow bind s e = some x) :
    ∃ v, value Perm.all bind st e = some v ∧ (v : Int) = ev ρ x ∧ v < M64 ∧ bounded s.nvars x := by
  cases e with
  | number n =>
    simp only [plainRow] at h
    split at h
    next hn => injection h with h; subst h; exact ⟨n, rfl, by simp, by unfold M64; omega, bounded_const _ _⟩
    next => cases h
  | name n =>
    simp only [plainRow] at h
    split at h
    next hn =>
      cases hb : (bind.lookup n).bind readInt with
      | none => simp [hb] at h
      | some i =>
        simp only [hb, Option.map] at h
        injection h with h; subst h
        have h0 : 0 ≤ i % (M64 : Int) := Int.emod_nonneg _ (by rw [M64_cast]; decide)
        have h1 : i % (M64 : Int) < M64 := Int.emod_lt_of_pos _ (by rw [M64_cast]; decide)
        refine ⟨(i % (M64 : Int)).toNat, by simp only [value, hn, if_true, hb, Option.map], by simp only [ev_const]; omega, by omega, bounded_const _ _⟩
    next hn =>
      cases hr : regOf bind n with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.map] at h
        injection h with h; subst h
        exact ⟨st.reg r, by simp only [value, hn, hr, Option.map]; rfl, H.reg r (regOf_lt hr), H.small r, wf.reg r (regOf_lt hr)⟩
  | lane _ _ => simp [plainRow] at h
  | call _ _ => simp [plainRow] at h

/-- An address the verifier places in the frame, so many bytes from where the stack pointer was at entry:
the machine works out that address. -/
theorem frameAddr {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF s) {bind : Bind} {a b : Expr} {x y : Row} {c : Int}
    (hx : plainRow bind s a = some x) (hy : plainRow bind s b = some y)
    (hl : locate ctx (Lin.add (signed x) (signed y)) = some (.frame c)) :
    ∃ ad, addrOf bind st [a, b] = some ad ∧
      (-(ctx.contract.stack : Int) ≤ c → c ≤ 0 → ad = ((s0.reg RSP : Int) + c).toNat) := by
  obtain ⟨va, ea, xa, la, ba⟩ := plainRow_value H wf hx
  obtain ⟨vb, eb, xb, lb, bb⟩ := plainRow_value H wf hy
  have hA : ev ρ (Lin.add (signed x) (signed y)) = ev ρ (signed x) + ev ρ (signed y) := ev_add _ _ _
  have sx := signed_ev ρ x
  have sy := signed_ev ρ y
  have hc := ev_isConst (ρ := ρ) (locate_frame hl)
  rw [ev_sub, ev_var, H.entry RSP (by decide)] at hc
  have hs := E.stack
  have ha := E.above
  refine ⟨(va + (vb + 0)) % M64, by simp only [addrOf, values, ea, eb, Option.map, sumList], fun h1 h2 => ?_⟩
  unfold M64 at *
  omega

/-- A load the verifier takes as one of memory given to read only: its bytes are not marked. -/
theorem publicLoad_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ ρ1 : Nat → Int}
    {s s1 : Sym} {st st1 : State} (M : MarksOk ctx s0 s.q st) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (C : Carried ctx s0 ρ s ρ1 s1 st1) {bind : Bind} {size : Nat} {a b : Expr}
    (h : publicLoad ctx bind s s1 size a b = true) :
    ∃ ad, addrOf bind st [a, b] = some ad ∧ anyMarked st.marks.mem ad size = false := by
  unfold publicLoad at h
  cases hx : plainRow bind s a with
  | none => simp [hx] at h
  | some x =>
    cases hy : plainRow bind s b with
    | none => simp [hx, hy] at h
    | some y =>
      simp only [hx, hy] at h
      obtain ⟨va, ea, xa, la, ba⟩ := plainRow_value H wf hx
      obtain ⟨vb, eb, xb, lb, bb⟩ := plainRow_value H wf hy
      have hb : bounded s.nvars (Lin.add (signed x) (signed y)) := bounded_add (bounded_signed ba) (bounded_signed bb)
      have hA : ev ρ (Lin.add (signed x) (signed y)) = ev ρ (signed x) + ev ρ (signed y) := ev_add _ _ _
      have sx := signed_ev ρ x
      have sy := signed_ev ρ y
      refine ⟨(va + (vb + 0)) % M64, by simp only [addrOf, values, ea, eb, Option.map, sumList], ?_⟩
      cases hl : locate ctx (Lin.add (signed x) (signed y)) with
      | some w =>
        cases w with
        | frame c =>
          simp only [hl, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨hsize, hin⟩ := h
          subst hsize
          obtain ⟨c1, c2, c3⟩ := M.frame c (List.contains_iff_mem.mp hin)
          obtain ⟨ad, e1, e2⟩ := frameAddr E H wf hx hy hl
          have e0 : addrOf bind st [a, b] = some ((va + (vb + 0)) % M64) := by simp only [addrOf, values, ea, eb, Option.map, sumList]
          rw [e0] at e1
          injection e1 with e1
          rw [e1, e2 c1 (by omega)]
          exact anyMarked_none _ _ fun x x1 x2 => by
            have := c3 (x - ((s0.reg RSP : Int) + c).toNat) (by omega)
            rw [show ((s0.reg RSP : Int) + c).toNat + (x - ((s0.reg RSP : Int) + c).toNat) = x by omega] at this
            exact this
        | out w o => simp [hl] at h
        | data c =>
          -- the file's data: its marks are as at entry, and at entry none of its bytes is marked
          simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨h0, h1⟩ := h
          have hmod : (((va + (vb + 0)) % M64 : Nat) : Int) % 2 ^ 64 = ev ρ (Lin.add (signed x) (signed y)) % 2 ^ 64 := by
            rw [hA]; unfold M64 at la lb ⊢; omega
          obtain ⟨hd, hadr⟩ := dataAddr E H hl h0 h1 (Nat.mod_lt _ (by decide)) hmod
          rw [hadr]
          exact anyMarked_none _ _ fun a a1 a2 => by
            rw [M.stable a (E.data_notFrame hd (by omega) (by omega)) (E.data_notOut hd (by omega) (by omega))]
            have := E.quiet.2.2.2.2 (a - s0.data) (by omega)
            rw [show s0.data + (a - s0.data) = a by omega] at this
            exact this
        | region r o =>
          obtain ⟨base, len, hreg, ho⟩ := locate_region hl
          simp only [hl, hreg, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
          obtain ⟨⟨hsize, hlook⟩, hnh⟩ := h
          subst hsize
          cases hv : lookupByte r o s1.bytes with
          | none => simp [hv] at hlook
          | some v =>
            obtain ⟨base', len', hr', g1, g2, _⟩ := C.holds.bytes v r o (lookupByte_mem hv)
            rw [hreg] at hr'
            injection hr' with hr'
            injection hr' with hb1 hb2
            subst hb1 hb2
            have hmem : (base, len) ∈ ctx.contract.regions := List.mem_of_getElem? hreg
            have hbase := (regions_lt hmem).1
            have eo : ev ρ1 o = ev ρ (Lin.add (signed x) (signed y)) - s0.reg base := by
              rw [ho, ev_sub, ev_var, C.holds.entry base hbase, ← ev_agree hb C.agree]
            obtain ⟨r1, r2⟩ := E.region hmem
            have had : (va + (vb + 0)) % M64 = s0.reg base + (ev ρ1 o).toNat := by
              unfold M64 at *
              omega
            rw [had]
            have hk : (ev ρ1 o).toNat < s0.reg len := by omega
            simp only [anyMarked, Bool.or_false]
            rw [M.stable _ (notFrame (by omega)) (E.region_notOut hmem (by omega) (by omega))]
            exact E.quiet.2.2.1 base len hmem hnh _ hk
      | none =>
        simp only [hl] at h
        cases hf : findOut (Lin.add (signed x) (signed y)) ctx.contract.fixeds 0 with
        | none => simp [hf] at h
        | some w =>
          obtain ⟨j, off, name, base, n, hw, _, hget, hoff⟩ := findOut_spec hf
          subst hw
          simp only [hf] at h
          have hget : ctx.contract.fixeds[j]? = some (name, base, n) := by simpa using hget
          cases hc : Lin.isConst off with
          | none => simp [hc] at h
          | some c =>
            simp only [hc, hget, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
            obtain ⟨⟨c0, c1⟩, hid⟩ := h
            have hmem : (name, base, n) ∈ ctx.contract.fixeds := List.mem_of_getElem? hget
            have hbase := fixeds_lt hmem
            have eo : (c : Int) = ev ρ (Lin.add (signed x) (signed y)) - s0.reg base := by
              rw [← ev_isConst (ρ := ρ) hc, hoff, ev_sub, ev_var, H.entry base hbase]
            obtain ⟨f1, f2, _, f4⟩ := E.fixed hmem
            by_cases hz : size = 0
            · subst hz; rfl
            have had : (va + (vb + 0)) % M64 = s0.reg base + c.toNat := by
              unfold M64 at *
              omega
            rw [had]
            refine anyMarked_none _ _ fun x x1 x2 => ?_
            have hnot : name ∉ ctx.contract.hidden := by
              intro hm
              rw [List.contains_iff_mem.mpr hm] at hid
              cases hid
            have hk : x - s0.reg base < n := by omega
            have hx : x = s0.reg base + (x - s0.reg base) := by omega
            rw [M.stable x (notFrame (by omega)) (fixed_notOut E hmem (by omega) (by omega))]
            rw [hx]
            exact E.quiet.2.2.2.1 name base n hmem hnot _ hk

/-! ## What an expression's value may be marked with -/

mutual
  theorem markOf_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ ρ1 : Nat → Int}
      {s s1 : Sym} {st st1 : State} (M : MarksOk ctx s0 s.q st) (H : Holds ctx s0 ρ s st) (wf : WF s)
      (C : Carried ctx s0 ρ s ρ1 s1 st1) {bind : Bind} :
      ∀ (e : Expr) {m : Bool}, markOf ctx bind s s1 e = some m →
        addrsQuiet bind st e = true ∧ (m = false → exprMark bind st e = false)
    | .number _, _, _ => ⟨rfl, fun _ => rfl⟩
    | .lane _ _, m, h => by
      simp only [markOf] at h
      injection h with h; subst h
      exact ⟨rfl, fun x => by cases x⟩
    | .name n, m, h => by
      simp only [markOf] at h
      injection h with h; subst h
      refine ⟨rfl, fun x => ?_⟩
      exact (clean_sound M.reg (.name n) (by simpa using x)).1
    | .call f args, m, h => by
      simp only [markOf] at h
      split at h
      next hw =>
        split at h
        next hc =>
          obtain ⟨c1, c2⟩ := cleanAll_sound M.reg args hc
          refine ⟨by simp only [addrsQuiet, c1, c2, Bool.not_false, Bool.or_true, Bool.and_true], fun hm => ?_⟩
          split at h
          next size a b hs =>
            injection h with h
            subst h
            have hp : publicLoad ctx bind s s1 size a b = true := by simpa using hm
            obtain ⟨ad, ha, hmk⟩ := publicLoad_sound E M H wf C hp
            simp only [exprMark, c1, memSize_width hs, ha, hmk, Bool.or_false]
          next => injection h with h; subst h; cases hm
        next => cases h
      next hw =>
        have hw : memWidth f = none := by simpa using hw
        obtain ⟨c2, c1⟩ := marksOf_sound E M H wf C args h
        exact ⟨by simp only [addrsQuiet, c2, hw, Option.isNone_none, Bool.true_or, Bool.and_true],
          fun hm => by simp only [exprMark, c1 hm, hw, Bool.or_false]⟩
  theorem marksOf_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ ρ1 : Nat → Int}
      {s s1 : Sym} {st st1 : State} (M : MarksOk ctx s0 s.q st) (H : Holds ctx s0 ρ s st) (wf : WF s)
      (C : Carried ctx s0 ρ s ρ1 s1 st1) {bind : Bind} :
      ∀ (es : List Expr) {m : Bool}, marksOf ctx bind s s1 es = some m →
        addrsQuietAll bind st es = true ∧ (m = false → exprMarks bind st es = false)
    | [], _, _ => ⟨rfl, fun _ => rfl⟩
    | e :: es, m, h => by
      simp only [marksOf] at h
      split at h
      next x y hx hy =>
        injection h with h
        subst h
        obtain ⟨a1, a2⟩ := markOf_sound E M H wf C e hx
        obtain ⟨b1, b2⟩ := marksOf_sound E M H wf C es hy
        refine ⟨by simp only [addrsQuietAll, a1, b1, Bool.and_true], fun hm => ?_⟩
        simp only [Bool.or_eq_false_iff] at hm
        simp only [exprMarks, a2 hm.1, b2 hm.2, Bool.or_false]
      next => cases h
end

/-! ## A statement -/

theorem allowed_at {p : Nat → Bool} : ∀ {n a : Nat}, allowed p a n = true → ∀ x, a ≤ x → x < a + n → p x = true
  | 0, a, _, x, h1, h2 => by omega
  | n + 1, a, h, x, h1, h2 => by
    simp only [allowed, Bool.and_eq_true] at h
    by_cases hx : x = a
    · subst hx; exact h.1
    · exact allowed_at h.2 x (by omega) (by omega)

/-- A statement that ran and whose place is memory: the machine was let write the place's bytes. -/
theorem store_allowed {perm : Perm} {bind : Bind} {base u : Nat} {st st1 : State} {stmt : Stmt}
    (h : execStmt perm bind base u st stmt = some st1) {f : String} {args : List Expr} {v : Expr}
    (hp : stmtParts stmt = some (.call f args, v)) :
    ∃ w ad, placeWidth stmt = some w ∧ addrOf bind st args = some ad ∧ allowed perm.write ad w = true := by
  cases stmt with
  | nothing => cases hp
  | ret => cases hp
  | call _ => cases hp
  | jump _ _ => cases hp
  | set place v' =>
    simp only [stmtParts] at hp
    injection hp with hp
    injection hp with h1 h2
    subst h1 h2
    simp only [execStmt] at h
    cases hx : (if isUnknown v' = true then some u else value perm bind st v') with
    | none => simp [hx] at h
    | some x =>
      simp only [hx] at h
      cases hs : memSize f with
      | none => simp [hs] at h
      | some size =>
        cases hv : values perm bind st args with
        | none => simp [hs, hv] at h
        | some vs =>
          simp only [hs, hv] at h
          split at h
          next ha => exact ⟨size, sumList vs % M64, by simp only [placeWidth, hs], by simp only [addrOf, values_all args hv, Option.map], ha⟩
          next => cases h
  | vset place v' =>
    simp only [stmtParts] at hp
    injection hp with hp
    injection hp with h1 h2
    subst h1 h2
    simp only [execStmt] at h
    split at h
    next vs l hvs _ =>
      split at h
      next ha => exact ⟨16, sumList vs % M64, rfl, by simp only [addrOf, values_all args hvs, Option.map], ha⟩
      next => cases h
    next => cases h
  | vset512 place v' =>
    simp only [stmtParts] at hp
    injection hp with hp
    injection hp with h1 h2
    subst h1 h2
    simp only [execStmt, execVec512] at h
    cases hl : lanesOf512 perm bind st v' with
    | none => simp [hl] at h
    | some lanes =>
      simp only [hl, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · cases h
      · simp only [addr512] at h
        cases hvs : values perm bind st args with
        | none => simp [hvs] at h
        | some vs =>
          simp only [hvs, Option.bind_eq_bind, Option.bind_some] at h
          split at h
          · simp only [Option.bind_some] at h
            split at h
            next ha => exact ⟨64, sumList vs % M64, rfl, by simp only [addrOf, values_all args hvs, Option.map], ha⟩
            next => cases h
          · simp at h

/-- A statement that ran, touching only what the contract lets the function touch: outside the frame and
the runs given to write every byte of memory is marked as it was. -/
theorem marksAfter_stable {ctx : Ctx} {s0 : State} {bind : Bind} {base u : Nat} {st st1 : State} {stmt : Stmt}
    (h : execStmt (ctx.contract.perm s0) bind base u st stmt = some st1) (a : Nat)
    (hf : ctx.contract.inFrame s0 a = false) (ho : ctx.contract.inOut s0 a = false) :
    (marksAfter bind st stmt).mem a = st.marks.mem a := by
  unfold marksAfter
  cases hp : stmtParts stmt with
  | none => rfl
  | some pv =>
    obtain ⟨place, v⟩ := pv
    cases place with
    | call f args =>
      obtain ⟨w, ad, hw, ha, hal⟩ := store_allowed h hp
      simp only [hw, ha]
      show markBytes st.marks.mem ad w _ a = st.marks.mem a
      unfold markBytes
      split
      next hin =>
        have := allowed_at hal a hin.1 hin.2
        simp [Contract.perm, hf, ho] at this
      next => rfl
    | number _ => rfl
    | lane _ _ => rfl
    | name n =>
      cases stmt with
      | set _ _ =>
        simp only
        split
        · rfl
        · split
          · rfl
          · split <;> rfl
      | vset _ _ => rfl
      | vset512 _ _ => rfl
      | nothing => cases hp
      | ret => cases hp
      | call _ => cases hp
      | jump _ _ => cases hp

/-- The statement sets no general register and no flag. -/
def NoRegSet : Stmt → Expr → Prop
  | .set _ _, .name _ => False
  | _, _ => True

theorem marksAfter_same {bind : Bind} {st : State} {stmt : Stmt} {place v : Expr} (hp : stmtParts stmt = some (place, v))
    (hk : NoRegSet stmt place) :
    (marksAfter bind st stmt).reg = st.marks.reg ∧ (marksAfter bind st stmt).zf = st.marks.zf ∧
    (marksAfter bind st stmt).cf = st.marks.cf := by
  cases stmt with
  | nothing => cases hp
  | ret => cases hp
  | call _ => cases hp
  | jump _ _ => cases hp
  | set pl v' =>
    simp only [stmtParts] at hp
    injection hp with hp
    injection hp with h1 h2
    subst h1 h2
    cases pl with
    | name _ => exact hk.elim
    | number _ => exact ⟨rfl, rfl, rfl⟩
    | lane _ _ => exact ⟨rfl, rfl, rfl⟩
    | call f args => simp only [marksAfter, stmtParts]; split <;> exact ⟨rfl, rfl, rfl⟩
  | vset pl v' =>
    simp only [stmtParts] at hp
    injection hp with hp
    injection hp with h1 h2
    subst h1 h2
    cases pl with
    | name _ => exact ⟨rfl, rfl, rfl⟩
    | number _ => exact ⟨rfl, rfl, rfl⟩
    | lane _ _ => exact ⟨rfl, rfl, rfl⟩
    | call f args => simp only [marksAfter, stmtParts]; split <;> exact ⟨rfl, rfl, rfl⟩
  | vset512 pl v' =>
    simp only [stmtParts] at hp
    injection hp with hp
    injection hp with h1 h2
    subst h1 h2
    cases pl with
    | name _ => exact ⟨rfl, rfl, rfl⟩
    | number _ => exact ⟨rfl, rfl, rfl⟩
    | lane _ _ => exact ⟨rfl, rfl, rfl⟩
    | call f args => simp only [marksAfter, stmtParts]; split <;> exact ⟨rfl, rfl, rfl⟩

/-- A store to memory: the cells of the frame the verifier has as not marked after it are not marked. -/
theorem cellsAfter_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (M : MarksOk ctx s0 s.q st) (H : Holds ctx s0 ρ s st) (wf : WF s) {bind : Bind} {f : String} {args : List Expr} {v : Expr}
    {m : Bool} (mv : m = false → exprMark bind st v = false) :
    CellsOk ctx s0 (cellsAfter ctx bind s f args m) (marksAfter bind st (.set (.call f args) v)).mem := by
  unfold cellsAfter
  cases hsz : memSize f with
  | none => exact CellsOk.nil
  | some size =>
    match args with
    | [] => exact CellsOk.nil
    | [_] => exact CellsOk.nil
    | _ :: _ :: _ :: _ => exact CellsOk.nil
    | [a, b] =>
      simp only
      cases hx : plainRow bind s a with
      | none => exact CellsOk.nil
      | some x =>
        cases hy : plainRow bind s b with
        | none => exact CellsOk.nil
        | some y =>
          simp only
          cases hl : locate ctx (Lin.add (signed x) (signed y)) with
          | none => exact CellsOk.nil
          | some w =>
            cases w with
            | region _ _ => exact CellsOk.nil
            | out w o =>
              -- a store within a run given to write: the run is no part of the frame, so each cell stays as it was
              simp only
              obtain ⟨name, base, n, hw, ho⟩ := locate_out hl
              simp only [hw]
              cases hc : Lin.isConst o with
              | none => exact CellsOk.nil
              | some c =>
                simp only
                split
                next hb =>
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
                  obtain ⟨va, ea, xa, la, ba⟩ := plainRow_value H wf hx
                  obtain ⟨vb, eb, xb, lb, bb⟩ := plainRow_value H wf hy
                  have sx := signed_ev ρ x
                  have sy := signed_ev ρ y
                  have hm := List.mem_of_getElem? hw
                  have hbase : ρ base = s0.reg base := H.entry base (outs_lt hm)
                  have hfit := (E.out hm).1
                  have hfr := (E.out hm).2
                  have hcv := ev_isConst (ρ := ρ) hc
                  rw [ho, ev_sub, ev_add, ev_var, hbase] at hcv
                  have hs := E.stack
                  have hpos : 0 < size := by
                    unfold memSize at hsz
                    split at hsz
                    · injection hsz with hsz; omega
                    · split at hsz
                      · injection hsz with hsz; omega
                      · split at hsz
                        · injection hsz with hsz; omega
                        · cases hsz
                  have had : (va + (vb + 0)) % M64 = s0.reg base + c.toNat := by unfold M64 at *; omega
                  have e1 : addrOf bind st [a, b] = some ((va + (vb + 0)) % M64) := by
                    simp only [addrOf, values, ea, eb, Option.map, sumList]
                  have hmem : (marksAfter bind st (.set (.call f [a, b]) v)).mem =
                      markBytes st.marks.mem ((va + (vb + 0)) % M64) size (exprMark bind st v) := by
                    simp only [marksAfter, stmtParts, placeWidth, hsz, e1]
                  rw [hmem, had]
                  intro o' ho'
                  obtain ⟨o1, o2, o3⟩ := M.frame o' ho'
                  refine ⟨o1, o2, fun k hk => ?_⟩
                  unfold markBytes
                  rw [if_neg (by omega)]
                  exact o3 k hk
                next => exact CellsOk.nil
            | data _ => exact CellsOk.nil
            | frame c =>
              simp only
              split
              next hb =>
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
                obtain ⟨ad, e1, e2⟩ := frameAddr E H wf hx hy hl
                have e2 := e2 hb.1 (by omega)
                have hs := E.stack
                have hmem : (marksAfter bind st (.set (.call f [a, b]) v)).mem = markBytes st.marks.mem ad size (exprMark bind st v) := by
                  simp only [marksAfter, stmtParts, placeWidth, hsz, e1]
                rw [hmem]
                intro o ho
                rcases List.mem_append.mp ho with h1 | h2
                · split at h1
                  next h8 =>
                    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h8
                    have : o = c := by simpa using h1
                    subst this
                    refine ⟨hb.1, by omega, fun k hk => ?_⟩
                    unfold markBytes
                    rw [if_pos ⟨by omega, by omega⟩]
                    exact mv h8.2
                  next => cases h1
                · obtain ⟨hin, hap⟩ := List.mem_filter.mp h2
                  simp only [Bool.or_eq_true, decide_eq_true_eq] at hap
                  obtain ⟨o1, o2, o3⟩ := M.frame o hin
                  refine ⟨o1, o2, fun k hk => ?_⟩
                  unfold markBytes
                  rw [if_neg (by omega)]
                  exact o3 k hk
              next => exact CellsOk.nil

/-! The marks of a statement are worked out from the registers of the state before and from what is known
not to be marked there, and from nothing else of it. -/

theorem plainRow_light (bind : Bind) (s : Sym) (e : Expr) : plainRow bind s.light e = plainRow bind s e := by
  cases e <;> rfl

theorem publicLoad_light (ctx : Ctx) (bind : Bind) (s s1 : Sym) (size : Nat) (a b : Expr) :
    publicLoad ctx bind s.light s1 size a b = publicLoad ctx bind s s1 size a b := by
  unfold publicLoad
  rw [plainRow_light, plainRow_light]
  rfl

mutual
  theorem markOf_light (ctx : Ctx) (bind : Bind) (s s1 : Sym) : ∀ (e : Expr), markOf ctx bind s.light s1 e = markOf ctx bind s s1 e
    | .number _ => rfl
    | .lane _ _ => rfl
    | .name _ => rfl
    | .call f args => by
      simp only [markOf, marksOf_light ctx bind s s1 args, publicLoad_light]
      rfl
  theorem marksOf_light (ctx : Ctx) (bind : Bind) (s s1 : Sym) : ∀ (es : List Expr), marksOf ctx bind s.light s1 es = marksOf ctx bind s s1 es
    | [] => rfl
    | e :: es => by simp only [marksOf, markOf_light ctx bind s s1 e, marksOf_light ctx bind s s1 es]
end

theorem stmtMarks_light (ctx : Ctx) (bind : Bind) (s s1 : Sym) (st : Stmt) :
    stmtMarks ctx bind s.light s1 st = stmtMarks ctx bind s s1 st := by
  cases st with
  | set place v => simp only [stmtMarks, markOf_light]; rfl
  | _ => rfl

/-- A STATEMENT. Where the verifier has followed the marks over a statement (`stmtMarks`), the statement
uses nothing marked in a way that shows, and what the verifier then has as not marked is not marked in
the state the machine goes on in. -/
theorem stmtMarks_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ ρ1 : Nat → Int}
    {s s1 : Sym} {st st1 : State} (M : MarksOk ctx s0 s.q st) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (C : Carried ctx s0 ρ s ρ1 s1 st1) {bind : Bind} {base u : Nat} {stmt : Stmt}
    (hx : execStmt (ctx.contract.perm s0) bind base u st stmt = some st1) {q' : SMarks}
    (hm : stmtMarks ctx bind s s1 stmt = some q') :
    quietStmt bind st stmt = true ∧ MarksOk ctx s0 q' (noted bind st stmt st1) := by
  have stable : ∀ a, ctx.contract.inFrame s0 a = false → ctx.contract.inOut s0 a = false →
      (marksAfter bind st stmt).mem a = s0.marks.mem a := fun a hf ho => by
    rw [marksAfter_stable hx a hf ho]; exact M.stable a hf ho
  have keep : ∀ {place v : Expr} {fq : List Int}, stmtParts stmt = some (place, v) → NoRegSet stmt place →
      CellsOk ctx s0 fq (marksAfter bind st stmt).mem →
      MarksOk ctx s0 { s.q with fq := fq } (noted bind st stmt st1) := fun hp hk hcells => by
    obtain ⟨e1, e2, e3⟩ := marksAfter_same (bind := bind) (st := st) hp hk
    refine ⟨fun r hr => ?_, fun hz => ?_, fun hc => ?_, stable, hcells⟩
    · show (marksAfter bind st stmt).reg r = false
      rw [e1]; exact M.reg r hr
    · show (marksAfter bind st stmt).zf = false
      rw [e2]; exact M.zf hz
    · show (marksAfter bind st stmt).cf = false
      rw [e3]; exact M.cf hc
  cases stmt with
  | nothing =>
    simp only [stmtMarks] at hm
    injection hm with hm; subst hm
    exact ⟨rfl, M.reg, M.zf, M.cf, stable, M.frame⟩
  | ret => simp [stmtMarks] at hm
  | call _ => simp [stmtMarks] at hm
  | jump _ _ => simp [stmtMarks] at hm
  | vset place v =>
    simp only [stmtMarks] at hm
    split at hm
    next hqv =>
      have qv := quietS_sound M.reg v hqv
      cases place with
      | call f args =>
        simp only at hm
        split at hm
        next hc =>
          injection hm with hm; subst hm
          obtain ⟨c1, c2⟩ := cleanAll_sound M.reg args hc
          exact ⟨by simp only [quietStmt, stmtParts, qv, c1, c2, Bool.not_false, Bool.and_true], keep rfl trivial CellsOk.nil⟩
        next => cases hm
      | name _ => simp only at hm; injection hm with hm; subst hm; exact ⟨by simp only [quietStmt, stmtParts, qv, Bool.and_true], keep rfl trivial M.frame⟩
      | number _ => simp only at hm; injection hm with hm; subst hm; exact ⟨by simp only [quietStmt, stmtParts, qv, Bool.and_true], keep rfl trivial M.frame⟩
      | lane _ _ => simp only at hm; injection hm with hm; subst hm; exact ⟨by simp only [quietStmt, stmtParts, qv, Bool.and_true], keep rfl trivial M.frame⟩
    next => cases hm
  | vset512 place v =>
    simp only [stmtMarks] at hm
    split at hm
    next hqv =>
      have qv := quietS_sound M.reg v hqv
      cases place with
      | call f args =>
        simp only at hm
        split at hm
        next hc =>
          injection hm with hm; subst hm
          obtain ⟨c1, c2⟩ := cleanAll_sound M.reg args hc
          exact ⟨by simp only [quietStmt, stmtParts, qv, c1, c2, Bool.not_false, Bool.and_true], keep rfl trivial CellsOk.nil⟩
        next => cases hm
      | name _ => simp only at hm; injection hm with hm; subst hm; exact ⟨by simp only [quietStmt, stmtParts, qv, Bool.and_true], keep rfl trivial M.frame⟩
      | number _ => simp only at hm; injection hm with hm; subst hm; exact ⟨by simp only [quietStmt, stmtParts, qv, Bool.and_true], keep rfl trivial M.frame⟩
      | lane _ _ => simp only at hm; injection hm with hm; subst hm; exact ⟨by simp only [quietStmt, stmtParts, qv, Bool.and_true], keep rfl trivial M.frame⟩
    next => cases hm
  | set place v =>
    simp only [stmtMarks] at hm
    cases hmv : markOf ctx bind s s1 v with
    | none => simp [hmv] at hm
    | some m =>
      simp only [hmv] at hm
      obtain ⟨qv, mv⟩ := markOf_sound E M H wf C v hmv
      cases place with
      | number _ => simp at hm
      | lane _ _ => simp at hm
      | call f args =>
        simp only at hm
        split at hm
        next hc =>
          injection hm with hm; subst hm
          obtain ⟨c1, c2⟩ := cleanAll_sound M.reg args hc
          exact ⟨by simp only [quietStmt, stmtParts, qv, c1, c2, Bool.not_false, Bool.and_true], keep rfl trivial (cellsAfter_sound E M H wf mv)⟩
        next => cases hm
      | name n =>
        simp only at hm
        have memsame : (marksAfter bind st (.set (.name n) v)).mem = st.marks.mem := by
          simp only [marksAfter, stmtParts]
          split
          · rfl
          · split
            · rfl
            · split <;> rfl
        have cells : CellsOk ctx s0 s.q.fq (marksAfter bind st (.set (.name n) v)).mem := by rw [memsame]; exact M.frame
        refine ⟨by simp only [quietStmt, stmtParts, qv, Bool.and_true], ?_⟩
        by_cases hz : (n == "zf") = true
        · simp only [hz, if_true] at hm
          injection hm with hm; subst hm
          refine ⟨fun r hr => ?_, fun hq => ?_, fun hq => ?_, stable, cells⟩
          · show (marksAfter bind st (.set (.name n) v)).reg r = false
            simp only [marksAfter, stmtParts, hz, if_true]; exact M.reg r hr
          · show (marksAfter bind st (.set (.name n) v)).zf = false
            simp only [marksAfter, stmtParts, hz, if_true]
            exact mv (by simpa using hq)
          · show (marksAfter bind st (.set (.name n) v)).cf = false
            simp only [marksAfter, stmtParts, hz, if_true]; exact M.cf hq
        · simp only [hz, if_false, Bool.false_eq_true] at hm
          by_cases hcf : (n == "cf") = true
          · simp only [hcf, if_true] at hm
            injection hm with hm; subst hm
            refine ⟨fun r hr => ?_, fun hq => ?_, fun hq => ?_, stable, cells⟩
            · show (marksAfter bind st (.set (.name n) v)).reg r = false
              simp only [marksAfter, stmtParts, hz, hcf, if_true, if_false, Bool.false_eq_true]; exact M.reg r hr
            · show (marksAfter bind st (.set (.name n) v)).zf = false
              simp only [marksAfter, stmtParts, hz, hcf, if_true, if_false, Bool.false_eq_true]; exact M.zf hq
            · show (marksAfter bind st (.set (.name n) v)).cf = false
              simp only [marksAfter, stmtParts, hz, hcf, if_true, if_false, Bool.false_eq_true]
              exact mv (by simpa using hq)
          · simp only [hcf, if_false, Bool.false_eq_true] at hm
            cases hr : regOf bind n with
            | none => simp [hr] at hm
            | some r =>
              simp only [hr] at hm
              injection hm with hm; subst hm
              refine ⟨fun k hk => ?_, fun hq => ?_, fun hq => ?_, stable, cells⟩
              · show (marksAfter bind st (.set (.name n) v)).reg k = false
                simp only [marksAfter, stmtParts, hz, hcf, hr, if_false, Bool.false_eq_true]
                show (if k = r then exprMark bind st v else st.marks.reg k) = false
                simp only at hk
                by_cases hkr : k = r
                · rw [if_pos hkr]
                  cases m with
                  | false => exact mv rfl
                  | true =>
                    simp only [if_true] at hk
                    have := (List.mem_filter.mp hk).2
                    simp [hkr] at this
                · rw [if_neg hkr]
                  cases m with
                  | false =>
                    simp only [Bool.false_eq_true, if_false, List.mem_cons] at hk
                    rcases hk with hk | hk
                    · exact absurd hk hkr
                    · exact M.reg k (List.mem_filter.mp hk).1
                  | true =>
                    simp only [if_true] at hk
                    exact M.reg k (List.mem_filter.mp hk).1
              · show (marksAfter bind st (.set (.name n) v)).zf = false
                simp only [marksAfter, stmtParts, hz, hcf, hr, if_false, Bool.false_eq_true]; exact M.zf hq
              · show (marksAfter bind st (.set (.name n) v)).cf = false
                simp only [marksAfter, stmtParts, hz, hcf, hr, if_false, Bool.false_eq_true]; exact M.cf hq

/-! ## What does not mention the marks -/

theorem Holds.q {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (x : SMarks) :
    Holds ctx s0 ρ { s with q := x } st :=
  ⟨H.entry, H.data, H.reg, H.small, H.zf, H.cf, H.frame, H.facts, H.bytes, H.spec, H.mem, H.wrote, H.words, H.known, H.range⟩

theorem WF.q {s : Sym} (wf : WF s) (x : SMarks) : WF { s with q := x } :=
  ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.facts, wf.bytes, wf.spec, wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, wf.range⟩

theorem Carried.q {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {s s' : Sym} {st : State} (c : Carried ctx s0 ρ s ρ' s' st) (x : SMarks) :
    Carried ctx s0 ρ s ρ' { s' with q := x } st := ⟨c.agree, c.mono, c.holds.q x, c.wf.q x⟩

/-! ## A jump, a return -/

theorem jumpTarget_quiet {bind : Bind} {target : Expr} {t : Nat} (h : jumpTarget bind target = some t) (st : State) :
    addrsQuiet bind st target = true ∧ exprMark bind st target = false := by
  cases target with
  | name n =>
    simp only [jumpTarget] at h
    split at h
    next hn => exact ⟨rfl, by simp only [exprMark, hn, if_true]⟩
    next => cases h
  | number _ => simp [jumpTarget] at h
  | lane _ _ => simp [jumpTarget] at h
  | call _ _ => simp [jumpTarget] at h

/-- At a return the verifier has let through, the address returned to is not marked. -/
theorem return_quiet {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (M : MarksOk ctx s0 s.q st) (H : Holds ctx s0 ρ s st) (hsp : s.sp = some 0)
    (hq : quietRegs.all s.q.regq.contains = true) : quietRet st = true := by
  have hreg : ∀ r ∈ quietRegs, st.marks.reg r = false := fun r hr =>
    M.reg r (List.contains_iff_mem.mp (List.all_eq_true.mp hq r hr))
  have e : st.reg RSP = s0.reg RSP := by
    have h1 := H.reg RSP (by decide)
    have h2 := ev_isConst (ρ := ρ) hsp
    rw [ev_sub, ev_var, H.entry RSP (by decide)] at h2
    omega
  have hs := E.stack
  simp only [quietRet, hreg RSP (by decide), Bool.not_false, Bool.true_and, Bool.not_eq_true']
  rw [e]
  refine anyMarked_none _ _ fun x x1 x2 => ?_
  rw [M.stable x (notFrame (Or.inr x1)) (E.frame_notOut (by omega) x2)]
  have := E.quiet.2.1 (x - s0.reg RSP) (by omega)
  rw [show s0.reg RSP + (x - s0.reg RSP) = x by omega] at this
  exact this

/-! ## A place -/

theorem arrive_q {ctx : Ctx} {pl : Place} {first s : Sym} {d : Row} {items : Items} {r : Unit × Items}
    (h : arrive ctx pl first d s items = .ok r) : first.q.regq.all s.q.regq.contains = true := by
  cases hfind : pl.keep.find? (fun r => s.reg r != first.reg r) with
  | some _ => simp only [arrive, hfind] at h; exact (refuse_ok h).elim
  | none =>
    simp only [arrive, hfind] at h
    split at h
    next => exact (refuse_ok h).elim
    next hq => simpa using hq

/-- The registers a place's general state takes as not marked are among those not marked on first coming. -/
theorem placeQuiet_all (pl : Place) (regq : List Nat) : (placeQuiet pl regq).all regq.contains = true :=
  List.all_eq_true.mpr fun r m => List.contains_iff_mem.mpr (List.mem_filter.mp m).1

/-- What is so of the marks where more registers are known not to be marked is so where fewer are. -/
theorem MarksOk.fewer {ctx : Ctx} {s0 : State} {q : SMarks} {st : State} (M : MarksOk ctx s0 q st) {regs : List Nat}
    (h : regs.all q.regq.contains = true) : MarksOk ctx s0 { regq := regs } st :=
  ⟨fun r hr => M.reg r (List.contains_iff_mem.mp (List.all_eq_true.mp h r hr)), (fun x => by cases x), (fun x => by cases x), M.stable, CellsOk.nil⟩

/-! ## A call -/

theorem quiet_not_kept : ∀ r ∈ quietRegs, calleeSaved.contains r = false := by decide

/-- A call the verifier has let through, of the marks: the stack pointer is not marked; what the called
function's contract asks about marks is so in the state it starts in; and in the state the caller goes on
in, what the verifier has as not marked after the call is not marked. -/
theorem callQuiet_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (M : MarksOk ctx s0 s.q st) (H : Holds ctx s0 ρ s st) {c : Contract} (hq : callQuiet ctx s c = true)
    (q : Program) (i : Instr) (hw : allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true)
    (hwrite : ∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) :
    st.marks.reg RSP = false ∧ c.quietAt (afterCall p q i st) ∧
    ∀ s2, c.quietAfter (afterCall p q i st) s2 → MarksOk ctx s0 (afterCallQ s) (backFrom st s2) := by
  simp only [callQuiet, Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨hregs, hdata⟩, hfix⟩, houts⟩, hrun⟩ := hq
  have hdata : c.data = [] := by simpa using hdata
  have regs : ∀ r ∈ quietRegs, st.marks.reg r = false := fun r hr =>
    M.reg r (List.contains_iff_mem.mp (List.all_eq_true.mp hregs r hr))
  have notw : ∀ a, ctx.contract.inFrame s0 a = false → ctx.contract.inOut s0 a = false →
      ¬ (st.reg RSP - 8 ≤ a ∧ a < st.reg RSP - 8 + 8) := fun a hf ho hin => by
    have := allowed_at hw a hin.1 hin.2
    simp [Contract.perm, hf, ho] at this
  refine ⟨regs RSP (by decide), ⟨fun r hr => regs r hr, fun k hk => ?_, fun r l hm hnh k hk => ?_, fun x r n hm hnot => ?_,
    fun k hk => by rw [hdata] at hk; cases hk⟩, ?_⟩
  · show markBytes st.marks.mem (st.reg RSP - 8) 8 false ((if RSP = RSP then st.reg RSP - 8 else st.reg RSP) + k) = false
    rw [if_pos rfl]
    unfold markBytes
    rw [if_pos ⟨by omega, by omega⟩]
  · have hfound := List.all_eq_true.mp hrun (r, l) hm
    simp only [hnh, Bool.false_or] at hfound
    cases hf : findRun s r l ctx.contract.regions 0 with
    | none => simp [hf] at hfound
    | some j =>
      obtain ⟨b0, l0, _, hget, er, el⟩ := findRun_spec hf
      have hnh0 : ctx.contract.hiddenAt b0 = false := by
        rw [hf] at hfound
        simp only at hfound
        have hget' : ctx.contract.regions[j]? = some (b0, l0) := by simpa using hget
        rw [hget'] at hfound
        simpa using hfound
      have hmem : (b0, l0) ∈ ctx.contract.regions := List.mem_of_getElem? hget
      obtain ⟨hb0, hl0⟩ := regions_lt hmem
      obtain ⟨ra, la⟩ := regions_args hm
      obtain ⟨r16, rne⟩ := argRegs_not_rsp ra
      obtain ⟨l16, lne⟩ := argRegs_not_rsp la
      have vr : st.reg r = s0.reg b0 := by
        have := H.reg r r16
        rw [er, ev_var, H.entry b0 hb0] at this
        omega
      have vl : st.reg l = s0.reg l0 := by
        have := H.reg l l16
        rw [el, ev_var, H.entry l0 hl0] at this
        omega
      have hk : k < s0.reg l0 := by
        have hk : k < (if l = RSP then st.reg RSP - 8 else st.reg l) := hk
        rw [if_neg lne, vl] at hk
        exact hk
      show markBytes st.marks.mem (st.reg RSP - 8) 8 false ((if r = RSP then st.reg RSP - 8 else st.reg r) + k) = false
      rw [if_neg rne, vr]
      unfold markBytes
      split
      · rfl
      · obtain ⟨_, r2⟩ := E.region hmem
        rw [M.stable _ (notFrame (by omega)) (E.region_notOut hmem (by omega) (by omega))]
        exact E.quiet.2.2.1 b0 l0 hmem hnh0 k hk
  · have hx := List.all_eq_true.mp hfix (x, r, n) hm
    rcases Bool.or_eq_true_iff.mp hx with hh | hframe
    · exact absurd (List.contains_iff_mem.mp hh) hnot
    · -- a part of the frame, in whole cells, each of them known not to be marked
      intro k hk
      have r16 : r < 16 := fixeds_lt hm
      have rne : r ≠ RSP := by
        have hr := fixedsIn_mem c.args argRegs x r n hm
        intro e
        rw [e] at hr
        simp [argRegs, RSP] at hr
      cases hfr : frameAt s r with
      | none => simp [hfr] at hframe
      | some o =>
        simp only [hfr, Bool.and_eq_true, decide_eq_true_eq] at hframe
        obtain ⟨n8, hcells⟩ := hframe
        have vr : (st.reg r : Int) = s0.reg RSP + o := by
          have h1 := H.reg r r16
          unfold frameAt at hfr
          have h2 := ev_isConst (ρ := ρ) hfr
          rw [ev_sub, ev_var, H.entry RSP (by decide)] at h2
          omega
        have hin : k / 8 < n / 8 := by omega
        have hc := List.all_eq_true.mp hcells (k / 8) (List.mem_range.mpr hin)
        obtain ⟨c1, c2, c3⟩ := M.frame _ (List.contains_iff_mem.mp hc)
        show markBytes st.marks.mem (st.reg RSP - 8) 8 false ((if r = RSP then st.reg RSP - 8 else st.reg r) + k) = false
        rw [if_neg rne]
        unfold markBytes
        split
        · rfl
        · have e : st.reg r + k = ((s0.reg RSP : Int) + (o + 8 * ((k / 8 : Nat) : Int))).toNat + k % 8 := by omega
          rw [e]; exact c3 (k % 8) (by omega)
  · intro s2 ⟨qr, qs⟩
    refine ⟨fun r hr => ?_, (fun x => by cases x), (fun x => by cases x), fun a hf ho => ?_, fun cc hcc => ?_⟩
    · show (if calleeSaved.contains r then st.marks.reg r else s2.marks.reg r) = false
      rcases List.mem_append.mp hr with h1 | h2
      · rw [if_neg (by rw [quiet_not_kept r h1]; decide)]; exact qr r h1
      · rw [if_pos (List.mem_filter.mp h2).2]; exact M.reg r (List.mem_filter.mp h2).1
    · show s2.marks.mem a = s0.marks.mem a
      have hn : (c.perm (afterCall p q i st)).write a = false := by
        cases hx : (c.perm (afterCall p q i st)).write a with
        | false => rfl
        | true =>
          have := hwrite a hx
          simp [Contract.perm, hf, ho] at this
      simp only [Contract.perm, Bool.or_eq_false_iff] at hn
      rw [qs a hn.1 hn.2]
      show markBytes st.marks.mem (st.reg RSP - 8) 8 false a = s0.marks.mem a
      unfold markBytes
      rw [if_neg (notw a hf ho)]
      exact M.stable a hf ho
    · -- a cell of the frame not below the stack pointer: the called function's frame is below it, and the
      -- runs it may write are within runs this function was given to write, which are no part of the frame
      have hcc : cc ∈ (match s.sp with | some sp => s.q.fq.filter (fun c => decide (sp ≤ c)) | none => []) := hcc
      cases hsp : s.sp with
      | none => rw [hsp] at hcc; cases hcc
      | some sp =>
        rw [hsp] at hcc
        obtain ⟨hin, hle⟩ := List.mem_filter.mp hcc
        have hle : sp ≤ cc := by simpa using hle
        obtain ⟨c1, c2, c3⟩ := M.frame cc hin
        refine ⟨c1, c2, fun k hk => ?_⟩
        have hs := E.stack
        have ersp : (st.reg RSP : Int) = s0.reg RSP + sp := by
          have h1 := H.reg RSP (by decide)
          have h2 := ev_isConst (ρ := ρ) hsp
          rw [ev_sub, ev_var, H.entry RSP (by decide)] at h2
          omega
        have houts : (c.outs.all fun (_, r, n) => decide (r ≠ RSP) && decide (r < 16) &&
            ((ctx.contract.outs.any fun (_, b, n0) =>
              match Lin.isConst (Lin.sub (s.reg r) (Lin.var b)) with
              | some k => decide (0 ≤ k) && decide (b < 16) && decide (k + n ≤ n0)
              | none => false) ||
             (match frameAt s r with
              | some o => s.q.fq.all fun cell => decide (cell + 8 ≤ o) || decide (o + (n : Int) ≤ cell)
              | none => false))) = true := by
          cases he : s.q.fq.isEmpty with
          | true => rw [List.isEmpty_iff.mp he] at hin; cases hin
          | false => rw [he, Bool.false_or] at houts; exact houts
        generalize ha : ((s0.reg RSP : Int) + cc).toNat + k = a
        have hf : c.inFrame (afterCall p q i st) a = false := by
          simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          right
          show ¬ a < (if RSP = RSP then st.reg RSP - 8 else st.reg RSP)
          rw [if_pos rfl]
          omega
        have ho : c.inOut (afterCall p q i st) a = false := by
          unfold Contract.inOut
          rw [List.any_eq_false]
          intro ⟨x, r, n⟩ hm
          have := List.all_eq_true.mp houts (x, r, n) hm
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at this
          obtain ⟨⟨rne, r16⟩, hgiven | hframe⟩ := this
          · -- within a run this function was given to write, which is no part of the frame
            obtain ⟨⟨x0, b, n0⟩, hm0, hpart⟩ := List.any_eq_true.mp hgiven
            cases hk : Lin.isConst (Lin.sub (s.reg r) (Lin.var b)) with
            | none => simp [hk] at hpart
            | some k =>
              simp only [hk, Bool.and_eq_true, decide_eq_true_eq] at hpart
              obtain ⟨⟨k0, b16⟩, hn⟩ := hpart
              have vr : (st.reg r : Int) = s0.reg b + k := by
                have h1 := H.reg r r16
                have h2 := ev_isConst (ρ := ρ) hk
                rw [ev_sub, ev_var, H.entry b b16] at h2
                omega
              obtain ⟨_, o2⟩ := E.out hm0
              show ¬ ((decide ((if r = RSP then st.reg RSP - 8 else st.reg r) ≤ a) && decide (a < (if r = RSP then st.reg RSP - 8 else st.reg r) + n)) = true)
              rw [if_neg rne]
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              omega
          · -- a part of the frame: the cell lies apart from it
            cases hfr : frameAt s r with
            | none => simp [hfr] at hframe
            | some o =>
              rw [hfr] at hframe
              have hapart := List.all_eq_true.mp hframe cc hin
              simp only [Bool.or_eq_true, decide_eq_true_eq] at hapart
              have vr : (st.reg r : Int) = s0.reg RSP + o := by
                have h1 := H.reg r r16
                unfold frameAt at hfr
                have h2 := ev_isConst (ρ := ρ) hfr
                rw [ev_sub, ev_var, H.entry RSP (by decide)] at h2
                omega
              show ¬ ((decide ((if r = RSP then st.reg RSP - 8 else st.reg r) ≤ a) && decide (a < (if r = RSP then st.reg RSP - 8 else st.reg r) + n)) = true)
              rw [if_neg rne]
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              omega
        show s2.marks.mem a = false
        rw [qs a hf ho]
        show markBytes st.marks.mem (st.reg RSP - 8) 8 false a = false
        unfold markBytes
        split
        · rfl
        · rw [← ha]; exact c3 k hk

/-- Forgetting of some cells of the frame that they are known not to be marked keeps what is held of the marks. -/
theorem quietAtCall_marks {ctx : Ctx} {s0 : State} {s : Sym} {st : State} (M : MarksOk ctx s0 s.q st) (c : Contract) :
    MarksOk ctx s0 (quietAtCall s c).q st := by
  unfold quietAtCall
  exact ⟨M.reg, M.zf, M.cf, M.stable, fun x hx => M.frame x (List.mem_filter.mp hx).1⟩

theorem quietAtCall_holds {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (c : Contract) :
    Holds ctx s0 ρ (quietAtCall s c) st := by
  unfold quietAtCall
  exact H.q _

end Ode
