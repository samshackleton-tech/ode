import Core
/-!
# Why the verifier's yes is right, 1: sums, the proof's items, and what follows from facts
-/
namespace Ode
open Arithmetic

/-- What a sum of unknowns is, the unknowns being the whole numbers `ρ`. -/
def ev (ρ : Nat → Int) (r : Row) : Int := dot r.coeff ρ + r.constant

theorem holds_iff {ρ : Nat → Int} {r : Row} : r.holds ρ ↔ 0 ≤ ev ρ r := Iff.rfl

theorem dot_strip (cs : List Int) (ρ : Nat → Int) : dot (Lin.strip cs) ρ = dot cs ρ := by
  induction cs generalizing ρ with
  | nil => rfl
  | cons c cs ih =>
    unfold Lin.strip
    split
    next h =>
      have := ih (fun n => ρ (n + 1))
      rw [h] at this
      split
      next hc => simp only [beq_iff_eq] at hc; simp [dot, hc, ← this]
      next => simp [dot, ← this]
    next d ds h =>
      have := ih (fun n => ρ (n + 1))
      rw [h] at this
      simp only [dot] at this ⊢
      omega

theorem dot_var (x : Nat) (ρ : Nat → Int) : dot (List.replicate x 0 ++ [1]) ρ = ρ x := by
  induction x generalizing ρ with
  | zero => simp [dot]
  | succ x ih => simp [List.replicate_succ, dot, ih]

@[simp] theorem ev_const (ρ : Nat → Int) (k : Int) : ev ρ (Lin.const k) = k := by simp [ev, Lin.const, dot]
@[simp] theorem ev_var (ρ : Nat → Int) (x : Nat) : ev ρ (Lin.var x) = ρ x := by simp [ev, Lin.var, dot_var]
@[simp] theorem ev_add (ρ : Nat → Int) (a b : Row) : ev ρ (Lin.add a b) = ev ρ a + ev ρ b := by
  simp only [ev, Lin.add, dot_strip, dot_sum]; omega
@[simp] theorem ev_scale (ρ : Nat → Int) (n : Int) (a : Row) : ev ρ (Lin.scale n a) = n * ev ρ a := by
  simp only [ev, Lin.scale, dot_strip, dot_scale, Int.mul_add]
@[simp] theorem ev_sub (ρ : Nat → Int) (a b : Row) : ev ρ (Lin.sub a b) = ev ρ a - ev ρ b := by
  simp only [Lin.sub, ev_add, ev_scale]; omega

theorem ev_isConst {ρ : Nat → Int} {a : Row} {k : Int} (h : Lin.isConst a = some k) : ev ρ a = k := by
  unfold Lin.isConst at h
  split at h
  next e =>
    injection h with h
    have : a.coeff = [] := by simpa using e
    simp [ev, this, dot, h]
  next => contradiction

/-! ## The monad -/

theorem V.bind_ok {x : V α} {f : α → V β} {items : Items} {r : β × Items}
    (h : (x >>= f) items = .ok r) : ∃ a rest, x items = .ok (a, rest) ∧ f a rest = .ok r := by
  change V.bind x f items = .ok r at h
  unfold V.bind at h
  split at h
  next a rest hx => exact ⟨a, rest, hx, h⟩
  next => contradiction

theorem V.pure_ok {a : α} {items : Items} {r : α × Items}
    (h : (Pure.pure a : V α) items = .ok r) : r = (a, items) := by
  change V.pure a items = .ok r at h
  unfold V.pure at h
  injection h with h; exact h.symm

theorem refuse_ok {why : String} {items : Items} {r : α × Items} (h : (refuse why : V α) items = .ok r) : False := by
  unfold refuse at h; contradiction

theorem need_ok {what : String} {facts goals : List Row} {items : Items} {r : α × Items}
    (h : (need what facts goals : V α) items = .ok r) : False := by
  unfold need at h; contradiction

/-! ## What follows from facts -/

theorem plain_sound {facts : List Row} {g : Row} (h : plain facts g = true) (ρ : Nat → Int)
    (hf : ∀ f ∈ facts, f.holds ρ) : 0 ≤ ev ρ g := by
  unfold plain at h
  split at h
  next k hk => rw [ev_isConst hk]; simpa using h
  next =>
    obtain ⟨f, fin, hfk⟩ := List.any_eq_true.mp h
    split at hfk
    next k hk =>
      have e := ev_isConst (ρ := ρ) hk
      have := hf f fin
      rw [holds_iff] at this
      simp only [ev_sub] at e
      have : 0 ≤ k := by simpa using hfk
      omega
    next => contradiction

theorem entailAs_sound {what : String} {facts : List Row} {g : Row} {items : Items} {r : Unit × Items}
    (h : entailAs what facts g items = .ok r) (ρ : Nat → Int) (hf : ∀ f ∈ facts, f.holds ρ) : 0 ≤ ev ρ g := by
  unfold entailAs at h
  split at h
  next hp => exact plain_sound hp ρ hf
  next =>
    obtain ⟨a, rest, _, h2⟩ := V.bind_ok h
    split at h2
    next starts steps =>
      split at h2
      next hr =>
        apply Classical.byContradiction
        intro hn
        apply refutes_sound _ _ _ hr ρ
        intro row hrow
        cases hrow with
        | head => rw [holds_iff]; simp only [negation, ev_sub, ev_const]; omega
        | tail _ hm => exact hf row hm
      next => exact (refuse_ok h2).elim
    next => exact (refuse_ok h2).elim
    next => exact (need_ok h2).elim

theorem entail_sound {facts : List Row} {g : Row} {items : Items} {r : Unit × Items}
    (h : entail facts g items = .ok r) (ρ : Nat → Int) (hf : ∀ f ∈ facts, f.holds ρ) : 0 ≤ ev ρ g :=
  entailAs_sound (what := "entail") h ρ hf

theorem entails_sound {facts : List Row} {ρ : Nat → Int} (hf : ∀ f ∈ facts, f.holds ρ) :
    ∀ {goals : List Row} {items rest : Items}, each (entail facts) goals items = .ok ((), rest) →
      ∀ g ∈ goals, g.holds ρ
  | [], _, _, _, _, m => by simp at m
  | k :: more, _, _, h, g, m => by
    simp only [each] at h
    obtain ⟨_, _, hk, hm⟩ := V.bind_ok h
    rcases List.mem_cons.mp m with rfl | m
    · exact entail_sound hk ρ hf
    · exact entails_sound hf hm g m

theorem staysBelow_sound {facts : List Row} {x : Row} {m : Int} {items rest : Items}
    (h : staysBelow facts x m items = .ok (true, rest)) (ρ : Nat → Int) (hf : ∀ f ∈ facts, f.holds ρ) :
    ev ρ x ≤ m - 1 := by
  have goal : ∀ {items : Items} {r : Unit × Items}, entail facts (Lin.sub (Lin.const (m - 1)) x) items = .ok r → ev ρ x ≤ m - 1 := by
    intro items r e
    have g := entail_sound e ρ hf
    simp only [ev_sub, ev_const] at g
    omega
  unfold staysBelow at h
  split at h
  next hp =>
    have g := plain_sound hp ρ hf
    simp only [ev_sub, ev_const] at g
    omega
  next =>
    obtain ⟨item, rest1, _, h2⟩ := V.bind_ok h
    split at h2
    next name n =>
      split at h2
      next =>
        obtain ⟨_, r1, e1, _⟩ := V.bind_ok h2
        exact goal e1
      next =>
        split at h2
        next =>
          have := V.pure_ok h2
          injection this with hc _
          cases hc
        next => exact (refuse_ok h2).elim
    next => exact (refuse_ok h2).elim
    next => exact (need_ok h2).elim

theorem isBelow_sound {facts : List Row} {a b : Row} {items : Items} {t : Bool} {rest : Items}
    (h : isBelow facts a b items = .ok (t, rest)) (ρ : Nat → Int) (hf : ∀ f ∈ facts, f.holds ρ) :
    t = decide (ev ρ a < ev ρ b) := by
  cases hk : Lin.isConst (Lin.sub a b) with
  | some k =>
    simp only [isBelow, hk] at h
    have e := ev_isConst (ρ := ρ) hk
    simp only [ev_sub] at e
    have := V.pure_ok h
    injection this with hc _
    subst hc
    by_cases h1 : k < 0 <;> simp [h1] <;> omega
  | none =>
    simp only [isBelow, hk] at h
    obtain ⟨item, rest1, _, h2⟩ := V.bind_ok h
    split at h2
    next name n =>
      split at h2
      next =>
        obtain ⟨_, r1, e1, h3⟩ := V.bind_ok h2
        have := V.pure_ok h3
        injection this with hc _
        subst hc
        have g1 := entail_sound e1 ρ hf
        simp only [ev_sub, ev_const] at g1
        simp; omega
      next =>
        split at h2
        next =>
          obtain ⟨_, r1, e1, h3⟩ := V.bind_ok h2
          have := V.pure_ok h3
          injection this with hc _
          subst hc
          have g1 := entail_sound e1 ρ hf
          simp only [ev_sub] at g1
          simp; omega
        next => exact (refuse_ok h2).elim
    next => exact (refuse_ok h2).elim
    next => exact (need_ok h2).elim

theorem compare_sound {facts : List Row} {a b : Row} {items : Items} {c : Cmp} {rest : Items}
    (h : compare facts a b items = .ok (c, rest)) (ρ : Nat → Int) (hf : ∀ f ∈ facts, f.holds ρ) :
    (c = .lt → ev ρ a < ev ρ b) ∧ (c = .eq → ev ρ a = ev ρ b) ∧ (c = .gt → ev ρ b < ev ρ a) := by
  cases hk : Lin.isConst (Lin.sub a b) with
  | some k =>
    simp only [compare, hk] at h
    have e := ev_isConst (ρ := ρ) hk
    simp only [ev_sub] at e
    have := V.pure_ok h
    injection this with hc _
    subst hc
    by_cases h1 : k < 0 <;> by_cases h2 : k = 0 <;> simp [h1, h2] <;> omega
  | none =>
    simp only [compare, hk] at h
    obtain ⟨item, rest1, _, h2⟩ := V.bind_ok h
    split at h2
    next name n =>
      split at h2
      next =>
        obtain ⟨_, r1, e1, h3⟩ := V.bind_ok h2
        obtain ⟨_, r2, e2, h4⟩ := V.bind_ok h3
        have := V.pure_ok h4
        injection this with hc _
        subst hc
        have g1 := entail_sound e1 ρ hf
        have g2 := entail_sound e2 ρ hf
        simp only [ev_sub] at g1 g2
        refine ⟨?_, ?_, ?_⟩ <;> intro hc <;> first | contradiction | omega
      next =>
        split at h2
        next =>
          obtain ⟨_, r1, e1, h3⟩ := V.bind_ok h2
          have := V.pure_ok h3
          injection this with hc _
          subst hc
          have g1 := entail_sound e1 ρ hf
          simp only [ev_sub, ev_const] at g1
          refine ⟨?_, ?_, ?_⟩ <;> intro hc <;> first | contradiction | omega
        next =>
          split at h2
          next =>
            obtain ⟨_, r1, e1, h3⟩ := V.bind_ok h2
            have := V.pure_ok h3
            injection this with hc _
            subst hc
            have g1 := entail_sound e1 ρ hf
            simp only [ev_sub, ev_const] at g1
            refine ⟨?_, ?_, ?_⟩ <;> intro hc <;> first | contradiction | omega
          next => exact (refuse_ok h2).elim
    next => exact (refuse_ok h2).elim
    next => exact (need_ok h2).elim

theorem constBelowZero_fails {r : Row} (h : constBelowZero r = true) (ρ : Nat → Int) : ¬ r.holds ρ := by
  unfold constBelowZero at h
  split at h
  next k hk =>
    rw [holds_iff, ev_isConst hk]
    have : k < 0 := by simpa using h
    omega
  next => contradiction

/-- A way assumed: either no input goes it, or the rows are added to the facts (or were plain numbers). -/
theorem assume_sound {s : Sym} {rows : List Row} {items : Items} {res : Option Sym} {rest : Items}
    (h : assume s rows items = .ok (res, rest)) (ρ : Nat → Int) (hf : ∀ f ∈ s.facts, f.holds ρ) :
    match res with
    | none => ¬ ∀ r ∈ rows, r.holds ρ
    | some s' => s' = s ∨ s' = { s with facts := rows ++ s.facts } := by
  unfold assume at h
  split at h
  next hany =>
    have := V.pure_ok h
    injection this with hc _
    subst hc
    obtain ⟨r, rin, hr⟩ := List.any_eq_true.mp hany
    exact fun all => constBelowZero_fails hr ρ (all r rin)
  next =>
    split at h
    next =>
      have := V.pure_ok h
      injection this with hc _
      subst hc
      exact Or.inl rfl
    next =>
      obtain ⟨item, rest1, _, h2⟩ := V.bind_ok h
      split at h2
      next name n =>
        split at h2
        next =>
          have := V.pure_ok h2
          injection this with hc _
          subst hc
          exact Or.inr rfl
        next =>
          split at h2
          next =>
            obtain ⟨item2, rest2, _, h3⟩ := V.bind_ok h2
            split at h3
            next starts steps =>
              split at h3
              next hr =>
                have := V.pure_ok h3
                injection this with hc _
                subst hc
                intro all
                apply refutes_sound _ _ _ hr ρ
                intro row hrow
                cases List.mem_append.mp hrow with
                | inl m => exact all row m
                | inr m => exact hf row m
              next => exact (refuse_ok h3).elim
            next => exact (refuse_ok h3).elim
          next => exact (refuse_ok h2).elim
      next => exact (refuse_ok h2).elim
      next => exact (need_ok h2).elim

end Ode
