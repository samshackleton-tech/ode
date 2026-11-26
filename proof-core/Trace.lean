/-
What can be observed of a run does not depend on what is marked.

The machine of Machine.lean carries a mark on each general register, flag and byte of memory, moves the
marks as it moves values, and (`execQ`) stops where something marked is used in an address, decides a
jump or is the address a return goes to. This file shows what that is for: of two runs of that machine
from states that are alike in everything not marked, the states at the end are again alike in everything
not marked, and the two runs let the same things be observed: the same instructions at the same
addresses, touching the same memory.

Nothing here is about a verifier or a contract. It is about the machine alone.
-/
import Machine

namespace Ode

/-- Two states are alike in everything not marked: they have the same marks, are at the same place in
the code, have each file's read-only data at the same address, have let the same things be observed, and every
register, flag and byte of memory that is not marked is the same in both; and so is the lowest byte of a
register whose lowest byte is not marked. (Of the vector registers nothing is asked: they are always taken as marked.) -/
structure Alike (a b : State) : Prop where
  marks : a.marks = b.marks
  rip : a.rip = b.rip
  data : a.data = b.data
  trace : a.trace = b.trace
  reg : ∀ r, a.marks.reg r = false → a.reg r = b.reg r
  zf : a.marks.zf = false → a.zf = b.zf
  cf : a.marks.cf = false → a.cf = b.cf
  mem : ∀ x, a.marks.mem x = false → a.mem x = b.mem x
  low : ∀ r, a.marks.low r = false → a.reg r % 256 = b.reg r % 256

/-! ## Memory -/

theorem allowed_all (a : Nat) : ∀ n, allowed Perm.all.read a n = true ∧ allowed Perm.all.write a n = true := by
  intro n
  induction n generalizing a with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih => simp only [allowed, (ih (a + 1)).1, (ih (a + 1)).2]; exact ⟨rfl, rfl⟩

theorem anyMarked_false {m : Nat → Bool} : ∀ {n a : Nat}, anyMarked m a n = false → ∀ x, a ≤ x → x < a + n → m x = false
  | 0, a, _, x, h1, h2 => by omega
  | n + 1, a, h, x, h1, h2 => by
    simp only [anyMarked, Bool.or_eq_false_iff] at h
    by_cases hx : x = a
    · subst hx; exact h.1
    · exact anyMarked_false h.2 x (by omega) (by omega)

theorem load_same (m1 m2 : Nat → Byte) : ∀ (n a : Nat), (∀ x, a ≤ x → x < a + n → m1 x = m2 x) → load m1 a n = load m2 a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [load]
    rw [h a (Nat.le_refl _) (by omega), load_same m1 m2 n (a + 1) fun x h1 h2 => h x (by omega) (by omega)]

theorem store_outside : ∀ (n : Nat) (m : Nat → Byte) (a v x : Nat), x < a ∨ a + n ≤ x → store m a v n x = m x
  | 0, _, _, _, _, _ => rfl
  | n + 1, m, a, v, x, h => by
    simp only [store]
    rw [store_outside n _ (a + 1) (v / 256) x (by omega), if_neg (by omega)]

theorem store_inside : ∀ (n : Nat) (m1 m2 : Nat → Byte) (a v x : Nat), a ≤ x → x < a + n → store m1 a v n x = store m2 a v n x
  | 0, _, _, _, _, _, h1, h2 => by omega
  | n + 1, m1, m2, a, v, x, h1, h2 => by
    simp only [store]
    by_cases hx : x = a
    · rw [store_outside n _ (a + 1) _ x (by omega), store_outside n _ (a + 1) _ x (by omega), if_pos hx, if_pos hx]
    · exact store_inside n _ _ (a + 1) _ x (by omega) (by omega)

theorem storeWords_outside : ∀ (ws : List Nat) (m : Nat → Byte) (a x : Nat), x < a ∨ a + 4 * ws.length ≤ x → storeWords m a ws x = m x
  | [], _, _, _, _ => rfl
  | w :: ws, m, a, x, h => by
    simp only [storeWords]
    simp only [List.length_cons] at h
    rw [storeWords_outside ws _ (a + 4) x (by omega), store_outside 4 m a w x (by omega)]

theorem memSize_width {f : String} {n : Nat} (h : memSize f = some n) : memWidth f = some n := by
  unfold memSize at h
  unfold memWidth
  split at h
  next h8 => rw [if_pos h8]; exact h
  next h8 =>
    rw [if_neg h8]
    split at h
    next h32 => rw [if_pos h32]; exact h
    next h32 =>
      rw [if_neg h32]
      split at h
      next h64 => rw [if_pos h64]; exact h
      next => cases h

/-! ## Expressions -/

mutual
  /-- What an expression is worth where only some memory may be read, it is worth where all may. -/
  theorem value_all {perm : Perm} {bind : Bind} {s : State} : ∀ (e : Expr) {v : Nat},
      value perm bind s e = some v → value Perm.all bind s e = some v
    | .number _, _, h => h
    | .lane _ _, _, h => h
    | .name _, _, h => h
    | .call f args, v, h => by
      simp only [value] at h ⊢
      cases hv : values perm bind s args with
      | none => simp only [hv] at h; cases h
      | some vs =>
        simp only [hv] at h
        simp only [values_all args hv]
        cases hm : memSize f with
        | none => simp only [hm] at h ⊢; exact h
        | some size =>
          simp only [hm] at h ⊢
          split at h
          · rw [if_pos (allowed_all _ _).1]; exact h
          · cases h
  theorem values_all {perm : Perm} {bind : Bind} {s : State} : ∀ (es : List Expr) {vs : List Nat},
      values perm bind s es = some vs → values Perm.all bind s es = some vs
    | [], _, h => h
    | e :: es, vs, h => by
      simp only [values] at h ⊢
      cases h1 : value perm bind s e with
      | none => simp only [h1] at h; cases h
      | some v =>
        cases h2 : values perm bind s es with
        | none => simp only [h1, h2] at h; cases h
        | some ws =>
          simp only [h1, h2] at h
          simp only [value_all e h1, values_all es h2]
          exact h
end

/-- What `lowOnly` finds: `low8` of a general register. -/
theorem lowOnly_some {bind : Bind} {f : String} {args : List Expr} {r : Nat} (h : lowOnly bind f args = some r) :
    f = "low8" ∧ ∃ n, args = [.name n] ∧ isNumberLetter n = false ∧ regOf bind n = some r := by
  unfold lowOnly at h
  split at h
  next hf =>
    refine ⟨by simpa using hf, ?_⟩
    split at h
    next n =>
      split at h
      · cases h
      next hn => exact ⟨n, rfl, by simpa using hn, h⟩
    next => cases h
  next => cases h

theorem flagVal_alike {a b : State} (A : Alike a b) {n : String} {m : Bool}
    (hf : flagMark a.marks n = some m) (hm : m = false) :
    flagVal a n = flagVal b n := by
  subst hm
  unfold flagMark at hf
  by_cases h1 : n = "zf"
  · subst h1; simp at hf; simp [flagVal, A.zf hf]
  · by_cases h2 : n = "nzf"
    · subst h2; simp at hf; simp [flagVal, A.zf hf]
    · by_cases h3 : n = "cf"
      · subst h3; simp at hf; simp [flagVal, A.cf hf]
      · by_cases h4 : n = "ncf"
        · subst h4; simp at hf; simp [flagVal, A.cf hf]
        · by_cases h5 : n = "hi"
          · subst h5; simp at hf; simp [flagVal, A.zf hf.1, A.cf hf.2]
          · by_cases h6 : n = "nhi"
            · subst h6; simp at hf; simp [flagVal, A.zf hf.1, A.cf hf.2]
            · simp [h1, h2, h3, h4, h5, h6] at hf

theorem regOf_none_of_flagMark {bind : Bind} {m : Marks} {n : String} {b : Bool} (hf : flagMark m n = some b) :
    regOf bind n = none := by
  simp only [flagMark] at hf
  by_cases h1 : n = "zf"
  · subst h1; rfl
  · by_cases h2 : n = "nzf"
    · subst h2; rfl
    · by_cases h3 : n = "cf"
      · subst h3; rfl
      · by_cases h4 : n = "ncf"
        · subst h4; rfl
        · by_cases h5 : n = "hi"
          · subst h5; rfl
          · by_cases h6 : n = "nhi"
            · subst h6; rfl
            · simp [beq_iff_eq, h1, h2, h3, h4, h5, h6] at hf

theorem flagVal_none_of_flagMark_none {s : State} {n : String} (hf : flagMark s.marks n = none) :
    flagVal s n = none := by
  unfold flagMark at hf
  by_cases h1 : n = "zf"
  · subst h1; simp at hf
  · by_cases h2 : n = "nzf"
    · subst h2; simp at hf
    · by_cases h3 : n = "cf"
      · subst h3; simp at hf
      · by_cases h4 : n = "ncf"
        · subst h4; simp at hf
        · by_cases h5 : n = "hi"
          · subst h5; simp at hf
          · by_cases h6 : n = "nhi"
            · subst h6; simp at hf
            · simp [flagVal, h1, h2, h3, h4, h5, h6]

theorem flagMark_none_of_regOf {bind : Bind} {m : Marks} {n : String} {r : Nat} (hr : regOf bind n = some r) :
    flagMark m n = none := by
  cases hf : flagMark m n with
  | none => rfl
  | some b => rw [regOf_none_of_flagMark hf] at hr; cases hr

theorem flagVal_none_of_regOf {bind : Bind} {s : State} {n : String} {r : Nat} (hr : regOf bind n = some r) :
    flagVal s n = none :=
  flagVal_none_of_flagMark_none (flagMark_none_of_regOf (m := s.marks) hr)

mutual
  /-- Of an expression whose addresses are made of nothing marked, in two states alike: it is marked in
  both or in neither; it reads the same memory; and where it is not marked it is worth the same. -/
  theorem expr_alike {bind : Bind} {a b : State} (A : Alike a b) : ∀ (e : Expr), addrsQuiet bind a e = true →
      exprMark bind a e = exprMark bind b e ∧ touched bind a e = touched bind b e ∧ addrsQuiet bind b e = true ∧
      (exprMark bind a e = false → value Perm.all bind a e = value Perm.all bind b e)
    | .number _, _ => ⟨rfl, rfl, rfl, fun _ => rfl⟩
    | .lane _ _, _ => ⟨rfl, rfl, rfl, fun _ => rfl⟩
    | .name n, _ => by
      refine ⟨by simp only [exprMark, A.marks], rfl, rfl, ?_⟩
      intro hm
      simp only [exprMark] at hm
      simp only [value]
      split
      · rfl
      next hn =>
        rw [if_neg hn] at hm
        cases hf : flagMark a.marks n with
        | some m =>
          simp only [hf] at hm
          have hfv := flagVal_alike A hf hm
          have hrg := regOf_none_of_flagMark (bind := bind) hf
          rw [hfv, hrg]; rfl
        | none =>
          simp only [hf] at hm
          have hfa := flagVal_none_of_flagMark_none hf
          have hfb : flagVal b n = none := flagVal_none_of_flagMark_none (A.marks ▸ hf)
          rw [hfa, hfb]
          cases hr : regOf bind n with
          | none => simp only [hr] at hm; cases hm
          | some r => simp only [hr] at hm; simp only [Option.map, A.reg r hm]
    | .call f args, h => by
      cases hl : lowOnly bind f args with
      | some r =>
        -- the lowest byte of a general register: the same in both where the register or that byte is not marked
        obtain ⟨hf, n, ha, hn, hr⟩ := lowOnly_some hl
        subst hf ha
        refine ⟨by simp only [exprMark, hl, A.marks], rfl, rfl, ?_⟩
        intro hm
        simp only [exprMark, hl, Bool.and_eq_false_iff] at hm
        have e : a.reg r % 256 = b.reg r % 256 := by
          cases hm with
          | inl h1 => rw [A.reg r h1]
          | inr h2 => exact A.low r h2
        simp only [value, values, hn, hr, flagVal_none_of_regOf hr, Option.map, memSize, prim]
        simp [e]
      | none =>
      simp only [addrsQuiet, Bool.and_eq_true] at h
      obtain ⟨hq, hw⟩ := h
      obtain ⟨em, tm, qb, vm⟩ := exprs_alike A args hq
      cases hmw : memWidth f with
      | none =>
        have ms : memSize f = none := by
          cases hs : memSize f with
          | none => rfl
          | some n => rw [memSize_width hs] at hmw; cases hmw
        refine ⟨by simp only [exprMark, hl, hmw, em], by simp only [touched, hmw, tm], by simp only [addrsQuiet, hmw, qb]; rfl, ?_⟩
        intro hm
        simp only [exprMark, hl, hmw, Bool.or_false] at hm
        simp only [value, vm hm, ms, A.data]
      | some w =>
        simp only [hmw, Option.isNone_some, Bool.false_or, Bool.not_eq_true'] at hw
        have ve := vm hw
        have ae : addrOf bind a args = addrOf bind b args := by simp only [addrOf, ve]
        refine ⟨by simp only [exprMark, hl, hmw, em, ae, A.marks], by simp only [touched, hmw, tm, ae],
          by simp only [addrsQuiet, hmw, qb, ← em, hw]; rfl, ?_⟩
        intro hm
        simp only [exprMark, hl, hmw, hw, Bool.false_or] at hm
        simp only [value, ← ve]
        cases hvs : values Perm.all bind a args with
        | none => rfl
        | some vs =>
          simp only
          cases hs : memSize f with
          | none => simp only [A.data]
          | some size =>
            simp only
            have hsz : size = w := by rw [memSize_width hs] at hmw; injection hmw
            subst hsz
            simp only [addrOf, hvs, Option.map] at hm
            rw [load_same a.mem b.mem size _ fun x h1 h2 => A.mem x (anyMarked_false hm x h1 h2)]
  theorem exprs_alike {bind : Bind} {a b : State} (A : Alike a b) : ∀ (es : List Expr), addrsQuietAll bind a es = true →
      exprMarks bind a es = exprMarks bind b es ∧ touchedAll bind a es = touchedAll bind b es ∧ addrsQuietAll bind b es = true ∧
      (exprMarks bind a es = false → values Perm.all bind a es = values Perm.all bind b es)
    | [], _ => ⟨rfl, rfl, rfl, fun _ => rfl⟩
    | e :: es, h => by
      simp only [addrsQuietAll, Bool.and_eq_true] at h
      obtain ⟨e1, t1, q1, v1⟩ := expr_alike A e h.1
      obtain ⟨e2, t2, q2, v2⟩ := exprs_alike A es h.2
      refine ⟨by simp only [exprMarks, e1, e2], by simp only [touchedAll, t1, t2], by simp only [addrsQuietAll, q1, q2]; rfl, ?_⟩
      intro hm
      simp only [exprMarks, Bool.or_eq_false_iff] at hm
      simp only [values, v1 hm.1, v2 hm.2]
end

/-! ## One statement -/

/-- The mark of a lowest byte, in two states alike. -/
theorem lowMark_alike {bind : Bind} {a b : State} (A : Alike a b) : ∀ (v : Expr), addrsQuiet bind a v = true →
    lowMark bind a v = lowMark bind b v
  | .call f [x, w], hq => by
    simp only [lowMark]
    split
    · have hw : addrsQuiet bind a w = true := by
        simp only [addrsQuiet, addrsQuietAll, Bool.and_eq_true] at hq; exact hq.1.2.1
      exact (expr_alike A w hw).1
    · exact (expr_alike A _ hq).1
  | .number _, hq => (expr_alike A _ hq).1
  | .lane _ _, hq => (expr_alike A _ hq).1
  | .name _, hq => (expr_alike A _ hq).1
  | .call _ [], hq => (expr_alike A _ hq).1
  | .call _ [_], hq => (expr_alike A _ hq).1
  | .call _ (_ :: _ :: _ :: _), hq => (expr_alike A _ hq).1

/-- What `setlow8(x, w)` is worth: `x` with `w` as its lowest byte. -/
theorem value_setlow8 {perm : Perm} {bind : Bind} {s : State} {x w : Expr} {v : Nat}
    (h : value perm bind s (.call "setlow8" [x, w]) = some v) :
    ∃ xv wv, value perm bind s w = some wv ∧ v = xv % M64 / 256 * 256 + wv % 256 := by
  simp only [value, values] at h
  cases hx : value perm bind s x with
  | none => simp [hx] at h
  | some xv =>
    cases hw : value perm bind s w with
    | none => simp [hx, hw] at h
    | some wv =>
      simp [hx, hw, memSize, prim] at h
      exact ⟨xv, wv, rfl, h.symm⟩

theorem unknown_marked {bind : Bind} {s : State} {v : Expr} (h : isUnknown v = true) : exprMark bind s v = true := by
  cases v with
  | name n =>
    simp only [isUnknown, beq_iff_eq] at h
    subst h
    rfl
  | _ => simp [isUnknown] at h

/-- What a statement's marks and observations are, in two states alike. -/
theorem notes_alike {bind : Bind} {a b : State} (A : Alike a b) {st : Stmt} (hq : quietStmt bind a st = true) :
    marksAfter bind a st = marksAfter bind b st ∧ observed bind a st = observed bind b st := by
  have parts : ∀ place v, stmtParts st = some (place, v) →
      (addrsQuiet bind a v = true ∧ match place with
        | .call _ args => addrsQuietAll bind a args = true ∧ exprMarks bind a args = false
        | _ => True) →
      exprMark bind a v = exprMark bind b v ∧ touched bind a v = touched bind b v ∧
      match place with
        | .call _ args => addrOf bind a args = addrOf bind b args ∧ touchedAll bind a args = touchedAll bind b args
        | _ => True := by
    intro place v _ h
    obtain ⟨e1, t1, _, _⟩ := expr_alike A v h.1
    refine ⟨e1, t1, ?_⟩
    cases place with
    | call f args =>
      obtain ⟨_, t2, _, v2⟩ := exprs_alike A args h.2.1
      exact ⟨by simp only [addrOf, v2 h.2.2], t2⟩
    | _ => trivial
  cases st with
  | nothing => exact ⟨by simp only [marksAfter, stmtParts, A.marks], rfl⟩
  | ret => exact ⟨by simp only [marksAfter, stmtParts, A.marks], rfl⟩
  | call _ => exact ⟨by simp only [marksAfter, stmtParts, A.marks], rfl⟩
  | retLink _ => exact ⟨by simp only [marksAfter, stmtParts, A.marks], rfl⟩
  | callLink _ _ => exact ⟨by simp only [marksAfter, stmtParts, A.marks], rfl⟩
  | jump _ _ => exact ⟨by simp only [marksAfter, stmtParts, A.marks], rfl⟩
  | set place v =>
    cases place with
    | call f args =>
      simp only [quietStmt, stmtParts, Bool.and_eq_true, Bool.not_eq_true'] at hq
      obtain ⟨e1, t1, ae, t2⟩ := parts _ v rfl ⟨hq.1, hq.2.1, hq.2.2⟩
      exact ⟨by simp only [marksAfter, stmtParts, placeWidth, ae, e1, A.marks], by simp only [observed, stmtParts, placeWidth, ae, t1, t2]⟩
    | name n =>
      simp only [quietStmt, stmtParts, Bool.and_true] at hq
      obtain ⟨e1, t1, _⟩ := parts _ v rfl ⟨hq, trivial⟩
      exact ⟨by simp only [marksAfter, stmtParts, e1, A.marks, lowMark_alike A v hq], by simp only [observed, stmtParts, t1]⟩
    | number _ =>
      simp only [quietStmt, stmtParts, Bool.and_true] at hq
      obtain ⟨e1, t1, _⟩ := parts _ v rfl ⟨hq, trivial⟩
      exact ⟨by simp only [marksAfter, stmtParts, A.marks], by simp only [observed, stmtParts, t1]⟩
    | lane _ _ =>
      simp only [quietStmt, stmtParts, Bool.and_true] at hq
      obtain ⟨e1, t1, _⟩ := parts _ v rfl ⟨hq, trivial⟩
      exact ⟨by simp only [marksAfter, stmtParts, A.marks], by simp only [observed, stmtParts, t1]⟩
  | vset place v =>
    cases place with
    | call f args =>
      simp only [quietStmt, stmtParts, Bool.and_eq_true, Bool.not_eq_true'] at hq
      obtain ⟨e1, t1, ae, t2⟩ := parts _ v rfl ⟨hq.1, hq.2.1, hq.2.2⟩
      exact ⟨by simp only [marksAfter, stmtParts, placeWidth, ae, A.marks], by simp only [observed, stmtParts, placeWidth, ae, t1, t2]⟩
    | name n =>
      simp only [quietStmt, stmtParts, Bool.and_true] at hq
      obtain ⟨e1, t1, _⟩ := parts _ v rfl ⟨hq, trivial⟩
      exact ⟨by simp only [marksAfter, stmtParts, A.marks], by simp only [observed, stmtParts, t1]⟩
    | number _ =>
      simp only [quietStmt, stmtParts, Bool.and_true] at hq
      obtain ⟨e1, t1, _⟩ := parts _ v rfl ⟨hq, trivial⟩
      exact ⟨by simp only [marksAfter, stmtParts, A.marks], by simp only [observed, stmtParts, t1]⟩
    | lane _ _ =>
      simp only [quietStmt, stmtParts, Bool.and_true] at hq
      obtain ⟨e1, t1, _⟩ := parts _ v rfl ⟨hq, trivial⟩
      exact ⟨by simp only [marksAfter, stmtParts, A.marks], by simp only [observed, stmtParts, t1]⟩
  | vset512 place v =>
    cases place with
    | call f args =>
      simp only [quietStmt, stmtParts, Bool.and_eq_true, Bool.not_eq_true'] at hq
      obtain ⟨e1, t1, ae, t2⟩ := parts _ v rfl ⟨hq.1, hq.2.1, hq.2.2⟩
      exact ⟨by simp only [marksAfter, stmtParts, placeWidth, ae, A.marks], by simp only [observed, stmtParts, placeWidth, ae, t1, t2]⟩
    | name n =>
      simp only [quietStmt, stmtParts, Bool.and_true] at hq
      obtain ⟨e1, t1, _⟩ := parts _ v rfl ⟨hq, trivial⟩
      exact ⟨by simp only [marksAfter, stmtParts, A.marks], by simp only [observed, stmtParts, t1]⟩
    | number _ =>
      simp only [quietStmt, stmtParts, Bool.and_true] at hq
      obtain ⟨e1, t1, _⟩ := parts _ v rfl ⟨hq, trivial⟩
      exact ⟨by simp only [marksAfter, stmtParts, A.marks], by simp only [observed, stmtParts, t1]⟩
    | lane _ _ =>
      simp only [quietStmt, stmtParts, Bool.and_true] at hq
      obtain ⟨e1, t1, _⟩ := parts _ v rfl ⟨hq, trivial⟩
      exact ⟨by simp only [marksAfter, stmtParts, A.marks], by simp only [observed, stmtParts, t1]⟩

/-- A statement that sets a vector register or stores one changes no general register and no flag, does
not move the place in the code, and changes memory only where it stores: `w` bytes at the place's address. -/
def VecKept (bind : Bind) (w : Nat) (place : Expr) (s s' : State) : Prop :=
  s'.reg = s.reg ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧ s'.rip = s.rip ∧ s'.data = s.data ∧
  match place with
  | .call _ args => ∃ ad, addrOf bind s args = some ad ∧ ∀ x, x < ad ∨ ad + w ≤ x → s'.mem x = s.mem x
  | _ => s'.mem = s.mem

theorem vset_kept {perm : Perm} {bind : Bind} {base u : Nat} {s s' : State} {place v : Expr}
    (h : execStmt perm bind base u s (.vset place v) = some s') : VecKept bind 16 place s s' := by
  cases place with
  | name n =>
    simp only [execStmt] at h
    split at h
    · split at h
      · injection h with h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases h
    · split at h
      · injection h with h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases h
  | call f args =>
    simp only [execStmt] at h
    split at h
    next vs l hvs _ =>
      split at h
      · injection h with h; subst h
        refine ⟨rfl, rfl, rfl, rfl, rfl, sumList vs % M64, by simp only [addrOf, values_all args hvs, Option.map], fun x hx => ?_⟩
        show store _ _ _ 4 x = s.mem x
        rw [store_outside 4 _ _ _ x (by omega), store_outside 4 _ _ _ x (by omega), store_outside 4 _ _ _ x (by omega),
          store_outside 4 _ _ _ x (by omega)]
      · cases h
    next => cases h
  | number _ => simp only [execStmt] at h; cases h
  | lane _ _ => simp only [execStmt] at h; cases h

theorem vset512_kept {perm : Perm} {bind : Bind} {base u : Nat} {s s' : State} {place v : Expr}
    (h : execStmt perm bind base u s (.vset512 place v) = some s') : VecKept bind 64 place s s' := by
  simp only [execStmt, execVec512] at h
  cases hl : lanesOf512 perm bind s v with
  | none => simp [hl] at h
  | some lanes =>
    simp only [hl, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h
    next hlen =>
      have hlen : lanes.length = 16 := by simpa using hlen
      cases place with
      | name n =>
        simp only at h
        cases hr : vecOf512 bind n with
        | none => simp [hr] at h
        | some r => simp only [hr, Option.map] at h; injection h with h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      | call f args =>
        simp only [addr512] at h
        cases hvs : values perm bind s args with
        | none => simp [hvs] at h
        | some vs =>
          simp only [hvs, Option.bind_eq_bind, Option.bind_some] at h
          split at h
          · simp only [Option.bind_some] at h
            split at h
            · injection h with h; subst h
              refine ⟨rfl, rfl, rfl, rfl, rfl, sumList vs % M64, by simp only [addrOf, values_all args hvs, Option.map], fun x hx => ?_⟩
              exact storeWords_outside lanes _ _ x (by rw [hlen]; omega)
            · cases h
          · simp at h
      | number _ => simp at h
      | lane _ _ => simp at h

/-- A statement that stores a vector, or sets a vector register, in two states alike. -/
theorem vec_alike {bind : Bind} {w : Nat} {place : Expr} {a b a' b' : State} {mk : Marks} (A : Alike a b)
    (ka : VecKept bind w place a a') (kb : VecKept bind w place b b')
    (hm : mk = match place with
      | .call _ args => (match addrOf bind a args with
        | some ad => { a.marks with mem := markBytes a.marks.mem ad w true }
        | none => a.marks)
      | _ => a.marks)
    (hq : match place with
      | .call _ args => addrOf bind a args = addrOf bind b args
      | _ => True) :
    a'.rip = b'.rip ∧ (∀ r, mk.reg r = false → a'.reg r = b'.reg r) ∧ (mk.zf = false → a'.zf = b'.zf) ∧
    (mk.cf = false → a'.cf = b'.cf) ∧ ∀ x, mk.mem x = false → a'.mem x = b'.mem x := by
  obtain ⟨r1, z1, c1, i1, _, m1⟩ := ka
  obtain ⟨r2, z2, c2, i2, _, m2⟩ := kb
  rw [r1, r2, z1, z2, c1, c2, i1, i2]
  cases place with
  | call f args =>
    simp only at m1 m2 hq hm
    obtain ⟨ad, ha, m1⟩ := m1
    obtain ⟨ad', hb, m2⟩ := m2
    rw [ha] at hq hm
    rw [hb] at hq
    injection hq with hq
    subst hq
    simp only at hm
    subst hm
    refine ⟨A.rip, A.reg, A.zf, A.cf, fun x hx => ?_⟩
    simp only [markBytes] at hx
    by_cases hin : ad ≤ x ∧ x < ad + w
    · rw [if_pos hin] at hx; cases hx
    · rw [if_neg hin] at hx
      rw [m1 x (by omega), m2 x (by omega)]
      exact A.mem x hx
  | name _ => simp only at m1 m2 hm; subst hm; rw [m1, m2]; exact ⟨A.rip, A.reg, A.zf, A.cf, A.mem⟩
  | number _ => simp only at m1 m2 hm; subst hm; rw [m1, m2]; exact ⟨A.rip, A.reg, A.zf, A.cf, A.mem⟩
  | lane _ _ => simp only at m1 m2 hm; subst hm; rw [m1, m2]; exact ⟨A.rip, A.reg, A.zf, A.cf, A.mem⟩

/-- Is a jump taken? -/
def jumps (s : State) : Option (String × Bool) → Bool
  | none => true
  | some (flag, want) => condFlag s flag == want

theorem execStmt_jump (perm : Perm) (bind : Bind) (base u : Nat) (s : State) (target : Expr) (cond : Option (String × Bool)) :
    execStmt perm bind base u s (.jump target cond) =
      if jumps s cond then (value perm bind s target).map fun t => { s with rip := base + t } else some s := by
  cases cond with
  | none => rfl
  | some fw => rfl

/-- No statement changes where the files' data lies. -/
theorem execStmt_data {perm : Perm} {bind : Bind} {base u : Nat} {s s' : State} :
    ∀ (st : Stmt), execStmt perm bind base u s st = some s' → s'.data = s.data
  | .nothing, h => by simp only [execStmt] at h; injection h with h; subst h; rfl
  | .ret, h => by simp only [execStmt] at h; cases h
  | .call _, h => by simp only [execStmt] at h; cases h
  | .vset512 _ _, h => (vset512_kept h).2.2.2.2.1
  | .vset _ _, h => (vset_kept h).2.2.2.2.1
  | .jump target cond, h => by
    rw [execStmt_jump] at h
    split at h
    · cases hv : value perm bind s target with
      | none => rw [hv] at h; cases h
      | some t => rw [hv] at h; injection h with h; subst h; rfl
    · injection h with h; subst h; rfl
  | .set place v, h => by
    simp only [execStmt] at h
    split at h
    next x n _ =>
      split at h
      · injection h with h; subst h; rfl
      · split at h
        · injection h with h; subst h; rfl
        · cases hr : regOf bind n with
          | none => simp [hr] at h
          | some r => simp only [hr, Option.map] at h; injection h with h; subst h; rfl
    next x f args _ =>
      split at h
      · split at h
        · injection h with h; subst h; rfl
        · cases h
      · cases h
    next => cases h

theorem jumps_alike {a b : State} (A : Alike a b) {cond : Option (String × Bool)}
    (h : (match cond with
      | none => true
      | some (flag, _) => !condMark a.marks flag) = true) : jumps a cond = jumps b cond := by
  cases cond with
  | none => rfl
  | some fw =>
    obtain ⟨flag, want⟩ := fw
    simp only [jumps, condFlag, condMark] at h ⊢
    by_cases hz : (flag == "zf") = true
    · simp only [hz, if_true, Bool.not_eq_true'] at h ⊢; rw [A.zf h]
    · simp only [hz, if_false, Bool.false_eq_true] at h ⊢
      by_cases hh : (flag == "hi") = true
      · simp only [hh, if_true, Bool.not_eq_true', Bool.or_eq_false_iff] at h ⊢
        rw [A.cf h.1, A.zf h.2]
      · simp only [hh, if_false, Bool.false_eq_true, Bool.not_eq_true'] at h ⊢; rw [A.cf h]

/-- The lowest byte of what a register is set to is the same in both, where `lowMark` has it as not marked. -/
theorem low_same {bind : Bind} {a b : State} (A : Alike a b) {v : Expr} (hqv : addrsQuiet bind a v = true)
    {p1 p2 : Perm} {u1 u2 x1 x2 : Nat}
    (e1 : (if isUnknown v = true then some u1 else value p1 bind a v) = some x1)
    (e2 : (if isUnknown v = true then some u2 else value p2 bind b v) = some x2)
    (hm : lowMark bind a v = false) : x1 % M64 % 256 = x2 % M64 % 256 := by
  have whole : exprMark bind a v = false → x1 = x2 := by
    intro hm
    by_cases hu : isUnknown v = true
    · rw [unknown_marked hu] at hm; cases hm
    · rw [if_neg hu] at e1 e2
      have := (expr_alike A v hqv).2.2.2 hm
      rw [value_all v e1, value_all v e2] at this
      injection this
  unfold lowMark at hm
  split at hm
  next f x w =>
    split at hm
    next hf =>
      -- `setlow8(x, w)`: the lowest byte is `w`'s, and `w` is worth the same in both
      have hf : f = "setlow8" := by simpa using hf
      subst hf
      simp only [isUnknown, Bool.false_eq_true, if_false] at e1 e2
      have hqw : addrsQuiet bind a w = true := by
        simp only [addrsQuiet, addrsQuietAll, Bool.and_eq_true] at hqv; exact hqv.1.2.1
      have ew := (expr_alike A w hqw).2.2.2 hm
      obtain ⟨xa, wa, hwa, rfl⟩ := value_setlow8 e1
      obtain ⟨xb, wb, hwb, rfl⟩ := value_setlow8 e2
      rw [value_all w hwa, value_all w hwb] at ew
      injection ew with ew
      subst ew
      unfold M64
      omega
    next => rw [whole hm]
  next => rw [whole hm]

/-- ONE STATEMENT, the lowest bytes: after it a register whose lowest byte is not marked has the same lowest
byte in both. -/
theorem stmt_low {bind : Bind} {base : Nat} {a b a' b' : State} (A : Alike a b) {st : Stmt}
    (hq : quietStmt bind a st = true) {p1 p2 : Perm} {u1 u2 : Nat}
    (h1 : execStmt p1 bind base u1 a st = some a') (h2 : execStmt p2 bind base u2 b st = some b') :
    ∀ r, (marksAfter bind a st).low r = false → a'.reg r % 256 = b'.reg r % 256 := by
  cases st with
  | nothing =>
    simp only [execStmt] at h1 h2
    injection h1 with h1; injection h2 with h2; subst h1; subst h2
    exact A.low
  | ret => simp only [execStmt] at h1; cases h1
  | call _ => simp only [execStmt] at h1; cases h1
  | retLink _ => simp only [execStmt] at h1; cases h1
  | callLink _ _ => simp only [execStmt] at h1; cases h1
  | vset place v =>
    intro r hr
    rw [(vset_kept h1).1, (vset_kept h2).1]
    refine A.low r ?_
    rw [← hr]
    cases place with
    | call f args => cases h : addrOf bind a args <;> simp only [marksAfter, stmtParts, placeWidth, h]
    | _ => simp only [marksAfter, stmtParts]
  | vset512 place v =>
    intro r hr
    rw [(vset512_kept h1).1, (vset512_kept h2).1]
    refine A.low r ?_
    rw [← hr]
    cases place with
    | call f args => cases h : addrOf bind a args <;> simp only [marksAfter, stmtParts, placeWidth, h]
    | _ => simp only [marksAfter, stmtParts]
  | jump target cond =>
    intro r hr
    have e1 : a'.reg = a.reg := by
      rw [execStmt_jump] at h1
      split at h1
      · cases hv : value p1 bind a target with
        | none => rw [hv] at h1; cases h1
        | some t => rw [hv] at h1; injection h1 with h1; subst h1; rfl
      · injection h1 with h1; subst h1; rfl
    have e2 : b'.reg = b.reg := by
      rw [execStmt_jump] at h2
      split at h2
      · cases hv : value p2 bind b target with
        | none => rw [hv] at h2; cases h2
        | some t => rw [hv] at h2; injection h2 with h2; subst h2; rfl
      · injection h2 with h2; subst h2; rfl
    rw [e1, e2]
    exact A.low r (by simpa only [marksAfter, stmtParts] using hr)
  | set place v =>
    have hqv : addrsQuiet bind a v = true := by
      simp only [quietStmt, stmtParts, Bool.and_eq_true] at hq; exact hq.1
    intro r hr
    simp only [execStmt] at h1 h2
    cases e1 : (if isUnknown v = true then some u1 else value p1 bind a v) with
    | none => simp [e1] at h1
    | some x1 =>
      cases e2 : (if isUnknown v = true then some u2 else value p2 bind b v) with
      | none => simp [e2] at h2
      | some x2 =>
        simp only [e1, e2] at h1 h2
        cases place with
        | number _ => simp at h1
        | lane _ _ => simp at h1
        | name n =>
          simp only at h1 h2
          by_cases hz : (n == "zf") = true
          · simp only [hz, if_true] at h1 h2
            injection h1 with h1; injection h2 with h2; subst h1; subst h2
            simp only [marksAfter, stmtParts, hz, if_true] at hr
            exact A.low r hr
          · simp only [hz, if_false, Bool.false_eq_true] at h1 h2
            by_cases hc : (n == "cf") = true
            · simp only [hc, if_true] at h1 h2
              injection h1 with h1; injection h2 with h2; subst h1; subst h2
              simp only [marksAfter, stmtParts, hz, hc, if_true, if_false, Bool.false_eq_true] at hr
              exact A.low r hr
            · simp only [hc, if_false, Bool.false_eq_true] at h1 h2
              cases hreg : regOf bind n with
              | none => simp [hreg] at h1
              | some r0 =>
                simp only [hreg, Option.map] at h1 h2
                injection h1 with h1; injection h2 with h2; subst h1; subst h2
                simp only [marksAfter, stmtParts, hz, hc, hreg, if_false, Bool.false_eq_true] at hr
                show (if r = r0 then x1 % M64 else a.reg r) % 256 = (if r = r0 then x2 % M64 else b.reg r) % 256
                by_cases hk : r = r0
                · rw [if_pos hk] at hr
                  rw [if_pos hk, if_pos hk]
                  exact low_same A hqv e1 e2 hr
                · rw [if_neg hk] at hr; rw [if_neg hk, if_neg hk]; exact A.low r hr
        | call f args =>
          -- a store: no register changes, and no register's mark
          simp only at h1 h2
          have r1 : a'.reg = a.reg := by
            split at h1
            · split at h1
              · injection h1 with h1; subst h1; rfl
              · cases h1
            · cases h1
          have r2 : b'.reg = b.reg := by
            split at h2
            · split at h2
              · injection h2 with h2; subst h2; rfl
              · cases h2
            · cases h2
          rw [r1, r2]
          refine A.low r ?_
          rw [← hr]
          simp only [marksAfter, stmtParts]
          split <;> rfl

/-- ONE STATEMENT. In two states alike in everything not marked, a statement that uses nothing marked
in a way that shows leaves two states alike again, whatever the unknowns turned out to be in each and
whatever each was let touch. -/
theorem stmt_alike {bind : Bind} {base : Nat} {a b a' b' : State} (A : Alike a b) {st : Stmt}
    (hq : quietStmt bind a st = true) {p1 p2 : Perm} {u1 u2 : Nat}
    (h1 : execStmt p1 bind base u1 a st = some a') (h2 : execStmt p2 bind base u2 b st = some b') :
    Alike (noted bind a st a') (noted bind b st b') := by
  obtain ⟨mk, ob⟩ := notes_alike A hq
  have hd : a'.data = b'.data := by rw [execStmt_data _ h1, execStmt_data _ h2]; exact A.data
  suffices h : a'.rip = b'.rip ∧ (∀ r, (marksAfter bind a st).reg r = false → a'.reg r = b'.reg r) ∧
      ((marksAfter bind a st).zf = false → a'.zf = b'.zf) ∧ ((marksAfter bind a st).cf = false → a'.cf = b'.cf) ∧
      ∀ x, (marksAfter bind a st).mem x = false → a'.mem x = b'.mem x from
    ⟨mk, h.1, hd, by simp only [noted, A.trace, ob], h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
      fun r hr => stmt_low (a' := a') (b' := b') A hq h1 h2 r hr⟩
  cases st with
  | nothing =>
    simp only [execStmt] at h1 h2
    injection h1 with h1; injection h2 with h2; subst h1; subst h2
    exact ⟨A.rip, A.reg, A.zf, A.cf, A.mem⟩
  | ret => simp only [execStmt] at h1; cases h1
  | call _ => simp only [execStmt] at h1; cases h1
  | retLink _ => simp only [execStmt] at h1; cases h1
  | callLink _ _ => simp only [execStmt] at h1; cases h1
  | vset place v =>
    refine vec_alike A (vset_kept h1) (vset_kept h2) ?_ ?_
    · cases place with
      | call f args => cases h : addrOf bind a args <;> simp only [marksAfter, stmtParts, placeWidth, h]
      | _ => simp only [marksAfter, stmtParts]
    · cases place with
      | call f args =>
        simp only [quietStmt, stmtParts, Bool.and_eq_true, Bool.not_eq_true'] at hq
        simp only [addrOf, (exprs_alike A args hq.2.1).2.2.2 hq.2.2]
      | _ => trivial
  | vset512 place v =>
    refine vec_alike A (vset512_kept h1) (vset512_kept h2) ?_ ?_
    · cases place with
      | call f args => cases h : addrOf bind a args <;> simp only [marksAfter, stmtParts, placeWidth, h]
      | _ => simp only [marksAfter, stmtParts]
    · cases place with
      | call f args =>
        simp only [quietStmt, stmtParts, Bool.and_eq_true, Bool.not_eq_true'] at hq
        simp only [addrOf, (exprs_alike A args hq.2.1).2.2.2 hq.2.2]
      | _ => trivial
  | jump target cond =>
    simp only [quietStmt, Bool.and_eq_true, Bool.not_eq_true'] at hq
    obtain ⟨⟨hqt, hmt⟩, hflag⟩ := hq
    have tv : ∀ {t1 t2 : Nat}, value p1 bind a target = some t1 → value p2 bind b target = some t2 → t1 = t2 := by
      intro t1 t2 e1 e2
      have := (expr_alike A target hqt).2.2.2 hmt
      rw [value_all target e1, value_all target e2] at this
      injection this
    have taken := jumps_alike A hflag
    rw [execStmt_jump] at h1 h2
    rw [← taken] at h2
    split at h1
    next ht =>
      rw [if_pos ht] at h2
      cases e1 : value p1 bind a target with
      | none => simp [e1] at h1
      | some t1 =>
        cases e2 : value p2 bind b target with
        | none => simp [e2] at h2
        | some t2 =>
          simp only [e1, e2, Option.map] at h1 h2
          injection h1 with h1; injection h2 with h2; subst h1; subst h2
          exact ⟨by show base + t1 = base + t2; rw [tv e1 e2], A.reg, A.zf, A.cf, A.mem⟩
    next ht =>
      rw [if_neg ht] at h2
      injection h1 with h1; injection h2 with h2; subst h1; subst h2
      exact ⟨A.rip, A.reg, A.zf, A.cf, A.mem⟩
  | set place v =>
    have hqv : addrsQuiet bind a v = true := by
      simp only [quietStmt, stmtParts, Bool.and_eq_true] at hq; exact hq.1
    have xe : ∀ {x1 x2 : Nat}, (if isUnknown v = true then some u1 else value p1 bind a v) = some x1 →
        (if isUnknown v = true then some u2 else value p2 bind b v) = some x2 → exprMark bind a v = false → x1 = x2 := by
      intro x1 x2 e1 e2 hm
      by_cases hu : isUnknown v = true
      · rw [unknown_marked hu] at hm; cases hm
      · rw [if_neg hu] at e1 e2
        have := (expr_alike A v hqv).2.2.2 hm
        rw [value_all v e1, value_all v e2] at this
        injection this
    simp only [execStmt] at h1 h2
    cases e1 : (if isUnknown v = true then some u1 else value p1 bind a v) with
    | none => simp [e1] at h1
    | some x1 =>
      cases e2 : (if isUnknown v = true then some u2 else value p2 bind b v) with
      | none => simp [e2] at h2
      | some x2 =>
        simp only [e1, e2] at h1 h2
        cases place with
        | number _ => simp at h1
        | lane _ _ => simp at h1
        | name n =>
          simp only at h1 h2
          by_cases hz : (n == "zf") = true
          · simp only [hz, if_true] at h1 h2
            injection h1 with h1; injection h2 with h2; subst h1; subst h2
            simp only [marksAfter, stmtParts, hz, if_true]
            exact ⟨A.rip, A.reg, fun hm => by show (x1 != 0) = (x2 != 0); rw [xe e1 e2 hm], A.cf, A.mem⟩
          · simp only [hz, if_false, Bool.false_eq_true] at h1 h2
            by_cases hc : (n == "cf") = true
            · simp only [hc, if_true] at h1 h2
              injection h1 with h1; injection h2 with h2; subst h1; subst h2
              simp only [marksAfter, stmtParts, hz, hc, if_true, if_false, Bool.false_eq_true]
              exact ⟨A.rip, A.reg, A.zf, fun hm => by show (x1 != 0) = (x2 != 0); rw [xe e1 e2 hm], A.mem⟩
            · simp only [hc, if_false, Bool.false_eq_true] at h1 h2
              cases hr : regOf bind n with
              | none => simp [hr] at h1
              | some r =>
                simp only [hr, Option.map] at h1 h2
                injection h1 with h1; injection h2 with h2; subst h1; subst h2
                simp only [marksAfter, stmtParts, hz, hc, hr, if_false, Bool.false_eq_true]
                refine ⟨A.rip, fun k hk => ?_, A.zf, A.cf, A.mem⟩
                show (if k = r then x1 % M64 else a.reg k) = (if k = r then x2 % M64 else b.reg k)
                by_cases hkr : k = r
                · rw [if_pos hkr] at hk; rw [if_pos hkr, if_pos hkr, xe e1 e2 hk]
                · rw [if_neg hkr] at hk; rw [if_neg hkr, if_neg hkr]; exact A.reg k hk
        | call f args =>
          simp only [quietStmt, stmtParts, Bool.and_eq_true, Bool.not_eq_true'] at hq
          have ae : addrOf bind a args = addrOf bind b args := by
            simp only [addrOf, (exprs_alike A args hq.2.1).2.2.2 hq.2.2]
          simp only at h1 h2
          cases hs : memSize f with
          | none => simp [hs] at h1
          | some size =>
            cases v1 : values p1 bind a args with
            | none => simp [hs, v1] at h1
            | some vs1 =>
              cases v2 : values p2 bind b args with
              | none => simp [hs, v2] at h2
              | some vs2 =>
                simp only [hs, v1, v2] at h1 h2
                have a1 : addrOf bind a args = some (sumList vs1 % M64) := by simp only [addrOf, values_all args v1, Option.map]
                have a2 : addrOf bind b args = some (sumList vs2 % M64) := by simp only [addrOf, values_all args v2, Option.map]
                rw [a1, a2] at ae
                injection ae with ae
                rw [← ae] at h2
                split at h1
                · split at h2
                  · injection h1 with h1; injection h2 with h2; subst h1; subst h2
                    simp only [marksAfter, stmtParts, placeWidth, hs, a1]
                    refine ⟨A.rip, A.reg, A.zf, A.cf, fun x hx => ?_⟩
                    show store a.mem _ x1 size x = store b.mem _ x2 size x
                    simp only [markBytes] at hx
                    by_cases hin : sumList vs1 % M64 ≤ x ∧ x < sumList vs1 % M64 + size
                    · rw [if_pos hin] at hx
                      rw [xe e1 e2 hx]
                      exact store_inside size _ _ _ _ x hin.1 hin.2
                    · rw [if_neg hin] at hx
                      rw [store_outside size _ _ _ x (by omega), store_outside size _ _ _ x (by omega)]
                      exact A.mem x hx
                  · cases h2
                · cases h1

/-! ## An instruction -/

/-- Two outcomes of an instruction are alike: both go on, or both have returned, in states alike. -/
def OutAlike : Outcome → Outcome → Prop
  | .next a, .next b => Alike a b
  | .returned a, .returned b => Alike a b
  | _, _ => False

theorem all_alike {bind : Bind} {base : Nat} {p1 p2 : Perm} {u1 u2 : Nat → Nat} :
    ∀ (stmts : List Stmt) (k1 k2 : Nat) {a b : State} {o1 o2 : Outcome}, Alike a b →
    execAllQ p1 bind base u1 k1 a stmts = some o1 → execAllQ p2 bind base u2 k2 b stmts = some o2 → OutAlike o1 o2
  | [], _, _, a, b, o1, o2, A, h1, h2 => by
    simp only [execAllQ] at h1 h2
    injection h1 with h1; injection h2 with h2; subst h1; subst h2
    exact A
  | st :: rest, k1, k2, a, b, o1, o2, A, h1, h2 => by
    have go : ∀ {a' b' : State}, quietStmt bind a st = true → execStmt p1 bind base (u1 k1) a st = some a' →
        execStmt p2 bind base (u2 k2) b st = some b' →
        execAllQ p1 bind base u1 (k1 + 1) (noted bind a st a') rest = some o1 →
        execAllQ p2 bind base u2 (k2 + 1) (noted bind b st b') rest = some o2 → OutAlike o1 o2 :=
      fun hq e1 e2 r1 r2 => all_alike rest (k1 + 1) (k2 + 1) (stmt_alike A hq e1 e2) r1 r2
    cases st with
    | ret =>
      simp only [execAllQ] at h1 h2
      split at h1
      next hq =>
        split at h2
        next =>
          injection h1 with h1; injection h2 with h2; subst h1; subst h2
          simp only [Bool.and_eq_true, quietRet, Bool.not_eq_true'] at hq
          have sp := A.reg RSP hq.1.1
          show Alike _ _
          refine ⟨A.marks, ?_, A.data, ?_, fun k hk => ?_, A.zf, A.cf, A.mem, fun k hk => ?_⟩
          · show load a.mem (a.reg RSP) 8 = load b.mem (b.reg RSP) 8
            rw [← sp]
            exact load_same _ _ 8 _ fun x x1 x2 => A.mem x (anyMarked_false hq.1.2 x x1 x2)
          · show a.trace ++ [(a.reg RSP, 8)] = b.trace ++ [(b.reg RSP, 8)]
            rw [A.trace, sp]
          · show (if k = RSP then (a.reg RSP + 8) % M64 else a.reg k) = (if k = RSP then (b.reg RSP + 8) % M64 else b.reg k)
            by_cases hkr : k = RSP
            · rw [if_pos hkr, if_pos hkr, sp]
            · rw [if_neg hkr, if_neg hkr]; exact A.reg k hk
          · show (if k = RSP then (a.reg RSP + 8) % M64 else a.reg k) % 256 = (if k = RSP then (b.reg RSP + 8) % M64 else b.reg k) % 256
            by_cases hkr : k = RSP
            · rw [if_pos hkr, if_pos hkr, sp]
            · rw [if_neg hkr, if_neg hkr]; exact A.low k hk
        next => cases h2
      next => cases h1
    | retLink r =>
      -- a return by a register: the register is not marked, so both go back to the same address
      simp only [execAllQ] at h1 h2
      cases hr : regIndex r with
      | none => simp [hr] at h1
      | some k =>
        simp only [hr, Option.bind] at h1 h2
        split at h1
        next => cases h1
        next hm =>
          split at h2
          next => cases h2
          next =>
            injection h1 with h1; injection h2 with h2; subst h1; subst h2
            have hk : a.marks.reg k = false := by simpa using hm
            show Alike _ _
            exact ⟨A.marks, A.reg k hk, A.data, A.trace, A.reg, A.zf, A.cf, A.mem, A.low⟩
    | callLink _ _ =>
      simp only [execAllQ] at h1 h2
      split at h1
      next hq =>
        split at h2
        next => split at h1 <;> split at h2 <;> first | cases h1 | cases h2 | exact go hq ‹_› ‹_› h1 h2
        next => cases h2
      next => cases h1
    | nothing =>
      simp only [execAllQ] at h1 h2
      split at h1
      next hq =>
        split at h2
        next => split at h1 <;> split at h2 <;> first | cases h1 | cases h2 | exact go hq ‹_› ‹_› h1 h2
        next => cases h2
      next => cases h1
    | call _ =>
      simp only [execAllQ] at h1 h2
      split at h1
      next hq =>
        split at h2
        next => split at h1 <;> split at h2 <;> first | cases h1 | cases h2 | exact go hq ‹_› ‹_› h1 h2
        next => cases h2
      next => cases h1
    | jump _ _ =>
      simp only [execAllQ] at h1 h2
      split at h1
      next hq =>
        split at h2
        next => split at h1 <;> split at h2 <;> first | cases h1 | cases h2 | exact go hq ‹_› ‹_› h1 h2
        next => cases h2
      next => cases h1
    | set _ _ =>
      simp only [execAllQ] at h1 h2
      split at h1
      next hq =>
        split at h2
        next => split at h1 <;> split at h2 <;> first | cases h1 | cases h2 | exact go hq ‹_› ‹_› h1 h2
        next => cases h2
      next => cases h1
    | vset _ _ =>
      simp only [execAllQ] at h1 h2
      split at h1
      next hq =>
        split at h2
        next => split at h1 <;> split at h2 <;> first | cases h1 | cases h2 | exact go hq ‹_› ‹_› h1 h2
        next => cases h2
      next => cases h1
    | vset512 _ _ =>
      simp only [execAllQ] at h1 h2
      split at h1
      next hq =>
        split at h2
        next => split at h1 <;> split at h2 <;> first | cases h1 | cases h2 | exact go hq ‹_› ‹_› h1 h2
        next => cases h2
      next => cases h1

/-- ONE INSTRUCTION, in two states alike. -/
theorem execQ_alike {p : Program} {i : Instr} {p1 p2 : Perm} {u1 u2 : Nat → Nat} {a b : State} {o1 o2 : Outcome}
    (A : Alike a b) (h1 : execQ p1 p i u1 a = some o1) (h2 : execQ p2 p i u2 b = some o2) : OutAlike o1 o2 :=
  all_alike i.effect 0 0
    (a := { a with rip := p.base + i.next, trace := a.trace ++ [(a.rip, 0)] })
    (b := { b with rip := p.base + i.next, trace := b.trace ++ [(b.rip, 0)] })
    ⟨A.marks, rfl, A.data, by show a.trace ++ [(a.rip, 0)] = b.trace ++ [(b.rip, 0)]; rw [A.trace, A.rip], A.reg, A.zf, A.cf, A.mem, A.low⟩
    h1 h2

/-- A call is not run as an instruction of the function it is in. -/
theorem execQ_call {p : Program} {i : Instr} {name : String} (h : callTarget i = some name) (perm : Perm) (u : Nat → Nat)
    (s : State) : execQ perm p i u s = none := by
  unfold callTarget at h
  split at h
  next n heff => simp [execQ, heff, execAllQ, execStmt]
  next n r heff => simp [execQ, heff, execAllQ, execStmt]
  next => cases h

/-- The state a called function starts in, of two states alike. (Where the call writes the address to come
back to below the stack pointer, the stack pointer is not marked.) -/
theorem afterCall_alike {p q : Program} {i : Instr} {a b : State} (A : Alike a b) (h : callLink i = none → a.marks.reg RSP = false) :
    Alike (afterCall p q i a) (afterCall p q i b) := by
  cases hl : callLink i with
  | none =>
    have sp := A.reg RSP (h hl)
    rw [afterCall_stack hl, afterCall_stack hl]
    refine ⟨?_, rfl, A.data, ?_, fun k hk => ?_, A.zf, A.cf, fun x hx => ?_, fun k hk => ?_⟩
    rotate_right
    · show (if k = RSP then a.reg RSP - 8 else a.reg k) % 256 = (if k = RSP then b.reg RSP - 8 else b.reg k) % 256
      by_cases hkr : k = RSP
      · rw [if_pos hkr, if_pos hkr, sp]
      · rw [if_neg hkr, if_neg hkr]; exact A.low k hk
    · show ({ a.marks with mem := markBytes a.marks.mem (a.reg RSP - 8) 8 false } : Marks) =
        { b.marks with mem := markBytes b.marks.mem (b.reg RSP - 8) 8 false }
      rw [A.marks, sp]
    · show a.trace ++ [(a.rip, 0), (a.reg RSP - 8, 8)] = b.trace ++ [(b.rip, 0), (b.reg RSP - 8, 8)]
      rw [A.trace, A.rip, sp]
    · show (if k = RSP then a.reg RSP - 8 else a.reg k) = (if k = RSP then b.reg RSP - 8 else b.reg k)
      by_cases hkr : k = RSP
      · rw [if_pos hkr, if_pos hkr, sp]
      · rw [if_neg hkr, if_neg hkr]; exact A.reg k hk
    · show store a.mem (a.reg RSP - 8) (p.base + i.next) 8 x = store b.mem (b.reg RSP - 8) (p.base + i.next) 8 x
      have hx : markBytes a.marks.mem (a.reg RSP - 8) 8 false x = false := hx
      rw [← sp]
      simp only [markBytes] at hx
      by_cases hin : a.reg RSP - 8 ≤ x ∧ x < a.reg RSP - 8 + 8
      · exact store_inside 8 _ _ _ _ x hin.1 hin.2
      · rw [if_neg hin] at hx
        rw [store_outside 8 _ _ _ x (by omega), store_outside 8 _ _ _ x (by omega)]
        exact A.mem x hx
  | some l =>
    -- the address to come back to is put in a register: that register holds the same in both, and is not marked
    rw [afterCall_link hl, afterCall_link hl]
    refine ⟨?_, rfl, A.data, ?_, fun k hk => ?_, A.zf, A.cf, A.mem, fun k hk => ?_⟩
    · show ({ a.marks with reg := fun k => if k = l then false else a.marks.reg k } : Marks) =
        { b.marks with reg := fun k => if k = l then false else b.marks.reg k }
      rw [A.marks]
    · show a.trace ++ [(a.rip, 0)] = b.trace ++ [(b.rip, 0)]
      rw [A.trace, A.rip]
    · have hk : (if k = l then false else a.marks.reg k) = false := hk
      show (if k = l then (p.base + i.next) % M64 else a.reg k) = (if k = l then (p.base + i.next) % M64 else b.reg k)
      by_cases hkl : k = l
      · rw [if_pos hkl, if_pos hkl]
      · rw [if_neg hkl] at hk; rw [if_neg hkl, if_neg hkl]; exact A.reg k hk
    · show (if k = l then (p.base + i.next) % M64 else a.reg k) % 256 = (if k = l then (p.base + i.next) % M64 else b.reg k) % 256
      by_cases hkl : k = l
      · rw [if_pos hkl, if_pos hkl]
      · rw [if_neg hkl, if_neg hkl]; exact A.low k hk

/-- The states two callers go on in after a call, of two states alike at the call and two alike at the
return, the registers a callee keeps (`kept`) holding in each what they held at the call. -/
theorem backFrom_alike {kept : List Nat} {a b a1 b1 : State} (A : Alike a b) (A1 : Alike a1 b1)
    (ka : ∀ r ∈ kept, a1.reg r = a.reg r) (kb : ∀ r ∈ kept, b1.reg r = b.reg r) :
    Alike (backFrom kept a a1) (backFrom kept b b1) := by
  refine ⟨?_, A1.rip, A1.data, A1.trace, fun r hr => ?_, A1.zf, A1.cf, A1.mem, A1.low⟩
  · show ({ a1.marks with reg := fun r => if kept.contains r then a.marks.reg r else a1.marks.reg r } : Marks) =
      { b1.marks with reg := fun r => if kept.contains r then b.marks.reg r else b1.marks.reg r }
    rw [A.marks, A1.marks]
  · have hr : (if kept.contains r then a.marks.reg r else a1.marks.reg r) = false := hr
    show a1.reg r = b1.reg r
    by_cases hc : kept.contains r = true
    · rw [if_pos hc] at hr
      have hm : r ∈ kept := by simpa using hc
      rw [ka r hm, kb r hm]; exact A.reg r hr
    · rw [if_neg hc] at hr; exact A1.reg r hr

/-! ## A run -/

/-- The function `p`, started in the state `s`, has returned in the state `s'`: by instructions of the
machine that stops where something marked shows, whatever the unknowns turned out to be at each and
whatever each was let touch; a called function running to its return in its turn, and giving back the
registers a callee keeps as it found them (`keptAt`: which they are goes by the call instruction). -/
theorem afterTail_alike {q : Program} {a b : State} (A : Alike a b) : Alike (afterTail q a) (afterTail q b) :=
  ⟨A.marks, rfl, A.data, by show a.trace ++ [(a.rip, 0)] = b.trace ++ [(b.rip, 0)]; rw [A.trace, A.rip], A.reg, A.zf, A.cf, A.mem, A.low⟩

inductive Ends (world : List Program) : Program → State → State → Prop where
  | ret (p : Program) (s : State) (i : Instr) (perm : Perm) (u : Nat → Nat) (s' : State) :
      p.fetch s.rip = some i → execQ perm p i u s = some (.returned s') → Ends world p s s'
  | step (p : Program) (s : State) (i : Instr) (perm : Perm) (u : Nat → Nat) (s1 s' : State) :
      p.fetch s.rip = some i → execQ perm p i u s = some (.next s1) → Ends world p s1 s' → Ends world p s s'
  | call (p : Program) (s : State) (i : Instr) (name : String) (q : Program) (s1 s' : State) :
      p.fetch s.rip = some i → callTarget i = some name → findProgram world name = some q →
      (callLink i = none → s.marks.reg RSP = false) →
      Ends world q (afterCall p q i s) s1 → (∀ r ∈ keptAt i, s1.reg r = s.reg r) →
      Ends world p (backFrom (keptAt i) s s1) s' → Ends world p s s'
  | tail (p : Program) (s : State) (i : Instr) (name : String) (q : Program) (s' : State) :
      p.fetch s.rip = some i → tailTarget i = some name → findProgram world name = some q →
      Ends world q (afterTail q s) s' → Ends world p s s'

/-- TWO RUNS. Of two runs of a function from states alike in everything not marked, the states at the
return are alike in everything not marked. -/
theorem ends_alike {world : List Program} {p : Program} {a a' : State} (E1 : Ends world p a a') :
    ∀ {b b' : State}, Alike a b → Ends world p b b' → Alike a' b' := by
  induction E1 with
  | ret p s i perm u s' hf hx =>
    intro b b' A E2
    cases E2 with
    | ret _ _ i2 perm2 u2 _ hf2 hx2 =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      exact execQ_alike A hx hx2
    | step _ _ i2 perm2 u2 s1 _ hf2 hx2 _ =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      exact (execQ_alike A hx hx2).elim
    | call _ _ i2 name q s1 _ hf2 hc _ _ _ _ _ =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [execQ_call hc] at hx; cases hx
    | tail _ _ i2 name q _ hf2 ht _ _ =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [execQ_tail ht] at hx; cases hx
  | step p s i perm u s1 s' hf hx _ ih =>
    intro b b' A E2
    cases E2 with
    | ret _ _ i2 perm2 u2 _ hf2 hx2 =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      exact (execQ_alike A hx hx2).elim
    | step _ _ i2 perm2 u2 t1 _ hf2 hx2 E2 =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      exact ih (execQ_alike A hx hx2) E2
    | call _ _ i2 name q t1 _ hf2 hc _ _ _ _ _ =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [execQ_call hc] at hx; cases hx
    | tail _ _ i2 name q _ hf2 ht _ _ =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [execQ_tail ht] at hx; cases hx
  | call p s i name q s1 s' hf hc hw hsp _ hk _ ih1 ih2 =>
    intro b b' A E2
    cases E2 with
    | ret _ _ i2 perm2 u2 _ hf2 hx2 =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [execQ_call hc] at hx2; cases hx2
    | step _ _ i2 perm2 u2 t1 _ hf2 hx2 _ =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [execQ_call hc] at hx2; cases hx2
    | call _ _ i2 name2 q2 t1 _ hf2 hc2 hw2 _ Ein hk2 Eout =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [hc] at hc2; injection hc2 with e; subst e
      rw [hw] at hw2; injection hw2 with e; subst e
      exact ih2 (backFrom_alike A (ih1 (afterCall_alike A hsp) Ein) hk hk2) Eout
    | tail _ _ i2 name2 q2 _ hf2 ht2 _ _ =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [tailTarget_not_call ht2] at hc; cases hc
  | tail p s i name q s' hf ht hw _ ih =>
    intro b b' A E2
    cases E2 with
    | ret _ _ i2 perm2 u2 _ hf2 hx2 =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [execQ_tail ht] at hx2; cases hx2
    | step _ _ i2 perm2 u2 t1 _ hf2 hx2 _ =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [execQ_tail ht] at hx2; cases hx2
    | call _ _ i2 name2 q2 t1 _ hf2 hc2 _ _ _ _ _ =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [tailTarget_not_call ht] at hc2; cases hc2
    | tail _ _ i2 name2 q2 _ hf2 ht2 hw2 Ein =>
      rw [← A.rip, hf] at hf2; injection hf2 with e; subst e
      rw [ht] at ht2; injection ht2 with e; subst e
      rw [hw] at hw2; injection hw2 with e; subst e
      exact ih (afterTail_alike A) Ein

/-- THE TRACE. Two runs of a function from states alike in everything not marked let the same things be
observed: the same instructions at the same addresses, touching the same memory. -/
theorem ends_trace {world : List Program} {p : Program} {a a' b b' : State} (A : Alike a b)
    (E1 : Ends world p a a') (E2 : Ends world p b b') : a'.trace = b'.trace :=
  (ends_alike E1 A E2).trace

/-! ## The machine that stops, and the machine that does not

`execQ` is `exec` with the stop added: where it takes a step, `exec` takes the same step, to the same
state. (So a run of a function that never stops the one is a run of the other.) -/

theorem execAllQ_execAll {perm : Perm} {bind : Bind} {base : Nat} {u : Nat → Nat} :
    ∀ (stmts : List Stmt) (k : Nat) {s : State} {o : Outcome},
    execAllQ perm bind base u k s stmts = some o → execAll perm bind base u k s stmts = some o
  | [], _, _, _, h => h
  | st :: rest, k, s, o, h => by
    have go : ∀ {s' : State}, execStmt perm bind base (u k) s st = some s' →
        execAllQ perm bind base u (k + 1) (noted bind s st s') rest = some o →
        execAll perm bind base u (k + 1) (noted bind s st s') rest = some o :=
      fun _ r => execAllQ_execAll rest (k + 1) r
    cases st with
    | ret =>
      simp only [execAllQ] at h
      split at h
      next hq =>
        simp only [Bool.and_eq_true] at hq
        simp only [execAll, hq.2, if_true]
        exact h
      next => cases h
    | retLink r =>
      simp only [execAllQ] at h
      cases hr : regIndex r with
      | none => simp [hr] at h
      | some k =>
        simp only [hr, Option.bind] at h
        split at h
        next => cases h
        next => simp only [execAll, hr, Option.map]; exact h
    | callLink _ _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => simp only [execAll, e]; exact go e h)
      next => cases h
    | nothing =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => simp only [execAll, e]; exact go e h)
      next => cases h
    | call _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => simp only [execAll, e]; exact go e h)
      next => cases h
    | jump _ _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => simp only [execAll, e]; exact go e h)
      next => cases h
    | set _ _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => simp only [execAll, e]; exact go e h)
      next => cases h
    | vset _ _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => simp only [execAll, e]; exact go e h)
      next => cases h
    | vset512 _ _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => simp only [execAll, e]; exact go e h)
      next => cases h

/-- Where the machine that stops takes a step, the machine that does not stop takes the same step. -/
theorem execQ_exec {perm : Perm} {p : Program} {i : Instr} {u : Nat → Nat} {s : State} {o : Outcome}
    (h : execQ perm p i u s = some o) : exec perm p i u s = some o :=
  execAllQ_execAll i.effect 0 h

/-! ## Where the files' data lies never changes

No statement changes `State.data`, so no instruction does, no call does, and a function returns with it
as it was. (A contract need not promise it: it is so of every run.) -/

/-- Where the files' data lies in the state an instruction gives. -/
def Outcome.data : Outcome → Nat → Nat
  | .next s => s.data
  | .returned s => s.data

theorem execAllQ_data {perm : Perm} {bind : Bind} {base : Nat} {u : Nat → Nat} :
    ∀ (stmts : List Stmt) (k : Nat) {s : State} {o : Outcome},
    execAllQ perm bind base u k s stmts = some o → o.data = s.data
  | [], _, _, _, h => by injection h with h; subst h; rfl
  | st :: rest, k, s, o, h => by
    have go : ∀ {s' : State}, execStmt perm bind base (u k) s st = some s' →
        execAllQ perm bind base u (k + 1) (noted bind s st s') rest = some o → o.data = s.data :=
      fun {s'} e r => by
        have h1 : o.data = (noted bind s st s').data := execAllQ_data rest (k + 1) r
        have h2 : s'.data = s.data := execStmt_data st e
        exact h1.trans h2
    cases st with
    | ret =>
      simp only [execAllQ] at h
      split at h
      next => injection h with h; subst h; rfl
      next => cases h
    | retLink r =>
      simp only [execAllQ] at h
      cases hr : regIndex r with
      | none => simp [hr] at h
      | some k =>
        simp only [hr, Option.bind] at h
        split at h
        next => cases h
        next => injection h with h; subst h; rfl
    | callLink _ _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => exact go e h)
      next => cases h
    | nothing =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => exact go e h)
      next => cases h
    | call _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => exact go e h)
      next => cases h
    | jump _ _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => exact go e h)
      next => cases h
    | set _ _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => exact go e h)
      next => cases h
    | vset _ _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => exact go e h)
      next => cases h
    | vset512 _ _ =>
      simp only [execAllQ] at h
      split at h
      next => split at h <;> first | cases h | (next s' e => exact go e h)
      next => cases h

theorem execQ_data {perm : Perm} {p : Program} {i : Instr} {u : Nat → Nat} {s : State} {o : Outcome}
    (h : execQ perm p i u s = some o) : o.data = s.data :=
  execAllQ_data i.effect 0 (s := { s with rip := p.base + i.next, trace := s.trace ++ [(s.rip, 0)] }) h

/-- **The data stays where it is.** A function that runs from `s` to states of which `Q` holds runs to
states of which `Q` holds and that have the files' data where `s` has it. -/
theorem runs_data {world : List Program} {perm : Perm} {p : Program} {Q : State → Prop} {s : State}
    (h : Runs world perm p Q s) : Runs world perm p (fun s' => Q s' ∧ s'.data = s.data) s := by
  induction h with
  | step perm p Q s i hf hn _ hr ih =>
    refine Runs.step perm p _ s i hf hn (fun u s' e => ?_) (fun u s' e => ⟨hr u s' e, execQ_data e⟩)
    have hd : s'.data = s.data := execQ_data e
    have := ih u s' e
    rw [hd] at this
    exact this
  | call perm p Q s i name q inner R hf hc hw hstack hir hiw _ hk _ ihq ihp =>
    rw [afterCall_data] at ihq
    refine Runs.call perm p _ s i name q inner (fun s' => R s' ∧ s'.data = s.data) hf hc hw hstack hir hiw ihq
      (fun s' hs' => hk s' hs'.1) (fun s' hs' => ?_)
    have := ihp s' hs'.1
    have hd : (backFrom (keptAt i) s s').data = s.data := hs'.2
    rw [hd] at this
    exact this
  | tail perm p Q s i name q inner hf ht hw hir hiw _ ihq =>
    exact Runs.tail perm p _ s i name q inner hf ht hw hir hiw ihq

end Ode
