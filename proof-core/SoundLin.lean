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

theorem Lin.sameList_iff : ∀ {xs ys : List Int}, Lin.sameList xs ys = true ↔ xs = ys
  | [], [] => by simp [Lin.sameList]
  | [], _ :: _ => by simp [Lin.sameList]
  | _ :: _, [] => by simp [Lin.sameList]
  | x :: xs, y :: ys => by
    simp only [Lin.sameList, Bool.and_eq_true, beq_iff_eq, List.cons.injEq]
    rw [Lin.sameList_iff]

theorem Lin.same_iff {a b : Row} : Lin.same a b = true ↔ a = b := by
  cases a; cases b
  simp only [Lin.same, Bool.and_eq_true, beq_iff_eq, Lin.sameList_iff, Row.mk.injEq]
  exact And.comm

/-- The second list is `c` times the first: so is what they add up to. -/
theorem dot_timesCoeff (c : Int) : ∀ (xs ys : List Int) (ρ : Nat → Int), Lin.timesCoeff c xs ys = true → dot ys ρ = c * dot xs ρ
  | [], ys, ρ, h => by
    simp only [Lin.timesCoeff] at h
    simp [dot, dot_allZero ys ρ h]
  | x :: xs, [], ρ, h => by
    simp only [Lin.timesCoeff, Bool.and_eq_true, beq_iff_eq] at h
    have e := dot_timesCoeff c xs [] (fun n => ρ (n + 1)) h.2
    simp only [dot] at e ⊢
    rw [Int.mul_add, ← Int.mul_assoc, h.1, ← e]
    simp
  | x :: xs, y :: ys, ρ, h => by
    simp only [Lin.timesCoeff, Bool.and_eq_true, beq_iff_eq] at h
    simp only [dot, h.1, dot_timesCoeff c xs ys _ h.2]
    rw [Int.mul_add, Int.mul_assoc]

theorem lessTimes_sound {g f : Row} {c k : Int} (h : Lin.lessTimes g c f = some k) (ρ : Nat → Int) :
    ev ρ g - c * ev ρ f = k := by
  unfold Lin.lessTimes at h
  split at h
  next ht =>
    injection h with h
    have e := dot_timesCoeff c f.coeff g.coeff ρ ht
    simp only [ev, e, Int.mul_add]
    omega
  next => contradiction

/-- The least of some numbers is one of them. -/
theorem leastNat_mem : ∀ {l : List Nat} {c : Nat}, leastNat l = some c → c ∈ l
  | [], _, h => by simp [leastNat] at h
  | a :: l, c, h => by
    simp only [leastNat] at h
    cases hl : leastNat l with
    | none => simp only [hl, Option.some.injEq] at h; subst h; exact List.mem_cons_self ..
    | some b =>
      simp only [hl, Option.some.injEq] at h
      split at h
      next => subst h; exact List.mem_cons_self ..
      next => subst h; exact List.mem_cons_of_mem _ (leastNat_mem hl)

/-- `among` is membership. -/
theorem among_iff {facts : List Row} {g : Row} : among facts g = true ↔ g ∈ facts := by
  simp only [among, List.any_eq_true, Lin.same_iff]
  exact ⟨fun ⟨f, m, e⟩ => e ▸ m, fun m => ⟨g, m, rfl⟩⟩

/-- Two lists of multiples that are the same but for zeros at their ends are the same sum. -/
theorem dot_sameCoeff : ∀ (xs ys : List Int) (ρ : Nat → Int), Lin.sameCoeff xs ys = true → dot xs ρ = dot ys ρ
  | [], ys, ρ, h => by
    simp only [Lin.sameCoeff] at h
    simp [dot, dot_allZero ys ρ h]
  | x :: xs, [], ρ, h => by
    simp only [Lin.sameCoeff] at h
    rw [dot_allZero (x :: xs) ρ h]; rfl
  | x :: xs, y :: ys, ρ, h => by
    simp only [Lin.sameCoeff, Bool.and_eq_true, beq_iff_eq] at h
    simp only [dot, h.1, dot_sameCoeff xs ys _ h.2]

theorem plain_sound {facts : List Row} {g : Row} (h : plain facts g = true) (ρ : Nat → Int)
    (hf : ∀ f ∈ facts, f.holds ρ) : 0 ≤ ev ρ g := by
  unfold plain at h
  split at h
  next k hk => rw [ev_isConst hk]; simpa using h
  next =>
    obtain ⟨f, fin, hfk⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfk
    have f0 := hf f fin
    rw [holds_iff] at f0
    have e := dot_sameCoeff g.coeff f.coeff ρ hfk.1
    simp only [ev] at f0 ⊢
    omega

theorem plainTimes_sound {facts : List Row} {g : Row} (h : plainTimes facts g = true) (ρ : Nat → Int)
    (hf : ∀ f ∈ facts, f.holds ρ) : 0 ≤ ev ρ g := by
  unfold plainTimes at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact plain_sound h ρ hf
  · obtain ⟨f, fin, hfk⟩ := List.any_eq_true.mp h
    split at hfk
    next a b _ _ =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hfk
      obtain ⟨⟨_, k0⟩, hc⟩ := hfk
      split at hc
      next k hk =>
        have e := lessTimes_sound hk ρ
        have f0 := hf f fin
        rw [holds_iff] at f0
        have c0 : 0 ≤ k := by simpa using hc
        have := Int.mul_nonneg k0 f0
        omega
      next => contradiction
    next => contradiction

/-- The least of some numbers is one of them. -/
theorem least_mem : ∀ {l : List Int} {c : Int}, least l = some c → c ∈ l
  | [], _, h => by simp [least] at h
  | a :: l, c, h => by
    simp only [least] at h
    cases hl : least l with
    | none => simp only [hl, Option.some.injEq] at h; subst h; exact List.mem_cons_self ..
    | some b =>
      simp only [hl, Option.some.injEq] at h
      split at h
      next => subst h; exact List.mem_cons_self ..
      next => subst h; exact List.mem_cons_of_mem _ (least_mem hl)

/-- A number the facts say at once that a row is no more than: it is no more than that. -/
theorem boundOf_sound {facts : List Row} {x : Row} {c : Int} (h : boundOf facts x = some c) (ρ : Nat → Int)
    (hf : ∀ f ∈ facts, f.holds ρ) : ev ρ x ≤ c := by
  obtain ⟨f, fin, hk⟩ := List.mem_filterMap.mp (least_mem h)
  have e := ev_isConst (ρ := ρ) hk
  have f0 := hf f fin
  rw [holds_iff] at f0
  rw [ev_add] at e
  omega

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
