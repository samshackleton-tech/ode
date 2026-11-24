import SoundSpec
/-!
# Why the verifier's yes is right, 6: a place, and what holds there
-/
namespace Ode
open Arithmetic

theorem all_nil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := fun _ m => nomatch m

theorem all_one {α : Type} {P : α → Prop} {a : α} (h : P a) : ∀ x ∈ [a], P x := fun x m => by
  simp only [List.mem_singleton] at m
  subst m
  exact h

theorem all_two {α : Type} {P : α → Prop} {a b : α} (ha : P a) (hb : P b) : ∀ x ∈ [a, b], P x := fun x m => by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
  rcases m with rfl | rfl
  · exact ha
  · exact hb

/-- What a line `fact …` of a place says, the names having these values: an equality says that the two sides
have the same values (or neither has one); another comparison, that both sides are numbers so related. -/
def Asserts (defs : List Def) (env : List (String × Val)) : SExpr → Prop
  | .bin op a b =>
    if op == "==" then ∀ v, Value defs env a v ↔ Value defs env b v
    else ∃ x y : Int, Value defs env a (.int x) ∧ Value defs env b (.int y) ∧ binop op (.int x) (.int y) = some (.bool true)
  | _ => False

theorem asserts_rel {defs : List Def} {env : List (String × Val)} {op : String} {a b : SExpr} {X Y : Int} {P : Prop}
    (hne : (op == "==") = false) (sa : Value defs env a (.int X)) (sb : Value defs env b (.int Y))
    (hP : binop op (.int X) (.int Y) = some (.bool true) ↔ P) : Asserts defs env (.bin op a b) ↔ P := by
  simp only [Asserts, hne, Bool.false_eq_true, if_false]
  constructor
  · rintro ⟨x, y, h1, h2, h3⟩
    have ex := Value.unique h1 sa
    have ey := Value.unique h2 sb
    injection ex with ex
    injection ey with ey
    subst ex ey
    exact hP.mp h3
  · exact fun h => ⟨X, Y, sa, sb, hP.mpr h⟩

theorem asserts_eq {defs : List Def} {env : List (String × Val)} {a b : SExpr} {X Y : Int}
    (sa : Value defs env a (.int X)) (sb : Value defs env b (.int Y)) : Asserts defs env (.bin "==" a b) ↔ X = Y := by
  simp only [Asserts, beq_self_eq_true, if_true]
  constructor
  · intro h
    have := Value.unique ((h _).mp sa) sb
    injection this
  · intro h v
    subst h
    constructor
    · intro hv; rw [Value.unique hv sa]; exact sb
    · intro hv; rw [Value.unique hv sb]; exact sa

theorem asserts_call {defs : List Def} {env : List (String × Val)} {a b : SExpr} {V : Int} {Q : Val → Prop}
    (sa : ∀ x, Value defs env a x ↔ Q x) (sb : Value defs env b (.int V)) : Asserts defs env (.bin "==" a b) ↔ Q (.int V) := by
  simp only [Asserts, beq_self_eq_true, if_true]
  constructor
  · intro h; exact (sa _).mp ((h _).mpr sb)
  · intro h v
    have ha := (sa _).mpr h
    constructor
    · intro hv; rw [Value.unique hv ha]; exact sb
    · intro hv; rw [Value.unique hv sb]; exact ha

theorem asserts_symm {defs : List Def} {env : List (String × Val)} {a b : SExpr} :
    Asserts defs env (.bin "==" a b) ↔ Asserts defs env (.bin "==" b a) := by
  simp only [Asserts, beq_self_eq_true, if_true]
  exact ⟨fun h v => (h v).symm, fun h v => (h v).symm⟩

/-- A line of a place worked out on symbols: the rows and facts that come out hold exactly when what the
line says is so. -/
theorem assertion_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (env : List (String × SVal)) {e : SExpr}
    {s s' : Sym} {rows : List Row} {sfacts : List SFact} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : assertion ctx env s e items = .ok ((rows, sfacts, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hb : EnvB s.nvars env) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ (∀ r ∈ rows, bounded s'.nvars r) ∧ (∀ f ∈ sfacts, f.bounded s'.nvars) ∧
      (((∀ r ∈ rows, r.holds ρ') ∧ (∀ f ∈ sfacts, f.holds ctx s0 ρ')) ↔ Asserts ctx.defs (semEnv ctx s0 ρ' env) e) := by
  cases e with
  | num _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | list _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | letx _ _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | each _ _ _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | slice _ _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | withx _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | record _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | field _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | theNumber _ _ _ _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | thePower _ _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | name _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | ifx _ _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | index _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | call _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | nil => simp only [assertion] at h; exact (refuse_ok h).elim
  | cons _ _ => simp only [assertion] at h; exact (refuse_ok h).elim
  | bin op a b =>
    simp only [assertion] at h
    obtain ⟨⟨x, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨⟨y, s2⟩, r2, e2, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1, sa, ba⟩ := seval_sound E env a e1 H wf hb
    have hb1 := hb.mono c1.mono
    obtain ⟨ρ2, c2, sb, bb⟩ := seval_sound E env b e2 c1.holds c1.wf hb1
    have sa2 := SRes.sem_agree sa ba hb1 c2.agree
    have ba2 := SRes.bounded_mono c2.mono ba
    have nomem : ∀ (f : SFact), f ∈ ([] : List SFact) → f.holds ctx s0 ρ2 := all_nil
    have norow : ∀ (r : Row), r ∈ ([] : List Row) → r.holds ρ2 := all_nil
    cases x with
    | list _ => cases y <;> exact (refuse_ok h).elim
    | val vx =>
      cases vx with
      | region _ => cases y <;> exact (refuse_ok h).elim
      | bool _ => cases y <;> exact (refuse_ok h).elim
      | lin x =>
        cases y with
        | list _ => exact (refuse_ok h).elim
        | tail c =>
          simp only at h
          split at h
          next hop =>
            have := V.pure_ok h
            injection this with hp _
            injection hp with e1 e2
            injection e2 with e2 e3
            subst e1 e2 e3
            have fe : op = "==" := by simpa using hop
            subst fe
            refine ⟨ρ2, c1.then c2, all_nil, all_one ⟨bb, ba2⟩, ?_⟩
            rw [asserts_symm, asserts_call sb sa2]
            exact ⟨fun hh => hh.2 _ (List.mem_singleton.mpr rfl), fun hh => ⟨norow, all_one hh⟩⟩
          next => exact (refuse_ok h).elim
        | val vy =>
          cases vy with
          | region _ => exact (refuse_ok h).elim
          | bool _ => exact (refuse_ok h).elim
          | lin y =>
            simp only at h
            simp only [SRes.sem, semv] at sa2 sb
            have bx : bounded s2.nvars x := ba2
            have by' : bounded s2.nvars y := bb
            split at h
            next hop =>
              have := V.pure_ok h
              injection this with hp _
              injection hp with e1 e2
              injection e2 with e2 e3
              subst e1 e2 e3
              have fe : op = "==" := by simpa using hop
              subst fe
              refine ⟨ρ2, c1.then c2, all_two (bounded_sub bx by') (bounded_sub by' bx), all_nil, ?_⟩
              rw [asserts_eq sa2 sb]
              constructor
              · intro hh
                have h1 := hh.1 _ (List.mem_cons_self ..)
                have h2 := hh.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
                rw [holds_iff, ev_sub] at h1 h2
                omega
              · intro hh
                refine ⟨fun r m => ?_, nomem⟩
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
                rcases m with rfl | rfl <;> rw [holds_iff, ev_sub] <;> omega
            next hop =>
              have hne : (op == "==") = false := by simpa using hop
              split at h
              next hop2 =>
                have := V.pure_ok h
                injection this with hp _
                injection hp with e1 e2
                injection e2 with e2 e3
                subst e1 e2 e3
                have fe : op = "<=" := by simpa using hop2
                subst fe
                refine ⟨ρ2, c1.then c2, all_one (bounded_sub by' bx), all_nil, ?_⟩
                rw [asserts_rel hne sa2 sb (P := ev ρ2 x ≤ ev ρ2 y) (by simp [binop])]
                constructor
                · intro hh
                  have h1 := hh.1 _ (List.mem_singleton.mpr rfl)
                  rw [holds_iff, ev_sub] at h1
                  omega
                · intro hh
                  refine ⟨fun r m => ?_, nomem⟩
                  simp only [List.mem_singleton] at m; subst m
                  rw [holds_iff, ev_sub]; omega
              next hop2 =>
                split at h
                next hop3 =>
                  have := V.pure_ok h
                  injection this with hp _
                  injection hp with e1 e2
                  injection e2 with e2 e3
                  subst e1 e2 e3
                  have fe : op = "<" := by simpa using hop3
                  subst fe
                  refine ⟨ρ2, c1.then c2, all_one (bounded_sub (bounded_sub by' bx) (bounded_const _ _)), all_nil, ?_⟩
                  rw [asserts_rel hne sa2 sb (P := ev ρ2 x < ev ρ2 y) (by simp [binop])]
                  constructor
                  · intro hh
                    have h1 := hh.1 _ (List.mem_singleton.mpr rfl)
                    rw [holds_iff] at h1; simp only [ev_sub, ev_const] at h1
                    omega
                  · intro hh
                    refine ⟨fun r m => ?_, nomem⟩
                    simp only [List.mem_singleton] at m; subst m
                    rw [holds_iff]; simp only [ev_sub, ev_const]; omega
                next hop3 =>
                  split at h
                  next hop4 =>
                    have := V.pure_ok h
                    injection this with hp _
                    injection hp with e1 e2
                    injection e2 with e2 e3
                    subst e1 e2 e3
                    have fe : op = ">=" := by simpa using hop4
                    subst fe
                    refine ⟨ρ2, c1.then c2, all_one (bounded_sub bx by'), all_nil, ?_⟩
                    rw [asserts_rel hne sa2 sb (P := ev ρ2 y ≤ ev ρ2 x) (by simp [binop])]
                    constructor
                    · intro hh
                      have h1 := hh.1 _ (List.mem_singleton.mpr rfl)
                      rw [holds_iff, ev_sub] at h1
                      omega
                    · intro hh
                      refine ⟨fun r m => ?_, nomem⟩
                      simp only [List.mem_singleton] at m; subst m
                      rw [holds_iff, ev_sub]; omega
                  next hop4 =>
                    split at h
                    next hop5 =>
                      have := V.pure_ok h
                      injection this with hp _
                      injection hp with e1 e2
                      injection e2 with e2 e3
                      subst e1 e2 e3
                      have fe : op = ">" := by simpa using hop5
                      subst fe
                      refine ⟨ρ2, c1.then c2, all_one (bounded_sub (bounded_sub bx by') (bounded_const _ _)), all_nil, ?_⟩
                      rw [asserts_rel hne sa2 sb (P := ev ρ2 y < ev ρ2 x) (by simp [binop])]
                      constructor
                      · intro hh
                        have h1 := hh.1 _ (List.mem_singleton.mpr rfl)
                        rw [holds_iff] at h1; simp only [ev_sub, ev_const] at h1
                        omega
                      · intro hh
                        refine ⟨fun r m => ?_, nomem⟩
                        simp only [List.mem_singleton] at m; subst m
                        rw [holds_iff]; simp only [ev_sub, ev_const]; omega
                    next => exact (refuse_ok h).elim
    | tail c =>
      cases y with
      | list _ => exact (refuse_ok h).elim
      | tail c' =>
        simp only at h
        split at h
        next hop =>
          have := V.pure_ok h
          injection this with hp _
          injection hp with e1 e2
          injection e2 with e2 e3
          subst e1 e2 e3
          have fe : op = "==" := by simpa using hop
          subst fe
          refine ⟨ρ2, c1.then c2, all_nil, all_one ⟨ba2, bb⟩, ?_⟩
          simp only [Asserts, beq_self_eq_true, if_true]
          constructor
          · intro hh v
            have := hh.2 _ (List.mem_singleton.mpr rfl) v
            exact (sa2 v).trans (this.trans (sb v).symm)
          · intro hh
            refine ⟨norow, fun f m => ?_⟩
            simp only [List.mem_singleton] at m; subst m
            exact fun v => (sa2 v).symm.trans ((hh v).trans (sb v))
        next => exact (refuse_ok h).elim
      | val vy =>
        cases vy with
        | region _ => exact (refuse_ok h).elim
        | bool _ => exact (refuse_ok h).elim
        | lin y =>
          simp only at h
          split at h
          next hop =>
            have := V.pure_ok h
            injection this with hp _
            injection hp with e1 e2
            injection e2 with e2 e3
            subst e1 e2 e3
            have fe : op = "==" := by simpa using hop
            subst fe
            refine ⟨ρ2, c1.then c2, all_nil, all_one ⟨ba2, bb⟩, ?_⟩
            rw [asserts_call sa2 sb]
            exact ⟨fun hh => hh.2 _ (List.mem_singleton.mpr rfl), fun hh => ⟨norow, all_one hh⟩⟩
          next => exact (refuse_ok h).elim

theorem Agree.symm {n : Nat} {ρ ρ' : Nat → Int} (a : Agree n ρ ρ') : Agree n ρ' ρ := fun k hk => (a k hk).symm

theorem each_mem {α : Type} {f : α → V Unit} : ∀ {l : List α} {items : Items} {r : Unit × Items},
    each f l items = .ok r → ∀ a ∈ l, ∃ items' r', f a items' = .ok r'
  | [], _, _, _, _, m => nomatch m
  | x :: more, items, r, h, a, m => by
    simp only [each] at h
    obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
    cases m with
    | head => exact ⟨items, _, e1⟩
    | tail _ m => exact each_mem h a m

/-- Facts of the specification the verifier has come to, one after another: all are so. -/
theorem specGoals_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) :
    ∀ (goals : List SFact) {s s' : Sym} {items rest : Items} {ρ : Nat → Int} {st : State},
    fold (specGoal ctx 16) s goals items = .ok (s', rest) → Holds ctx s0 ρ s st → WF ctx s → (∀ f ∈ goals, f.bounded s.nvars) →
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ ∀ f ∈ goals, f.holds ctx s0 ρ'
  | [], s, s', items, rest, ρ, st, h, H, wf, hb => by
    simp only [fold] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨ρ, Carried.here H wf, all_nil⟩
  | g :: more, s, s', items, rest, ρ, st, h, H, wf, hb => by
    simp only [fold] at h
    obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1, g1⟩ := specGoal_sound E 16 e1 H wf (hb g (List.mem_cons_self ..))
    obtain ⟨ρ2, c2, g2⟩ := specGoals_sound E more h c1.holds c1.wf
      (fun f m => SFact.bounded_mono c1.mono (hb f (List.mem_cons_of_mem _ m)))
    refine ⟨ρ2, c1.then c2, fun f m => ?_⟩
    cases m with
    | head => exact SFact.holds_agree (SFact.bounded_mono c1.mono (hb g (List.mem_cons_self ..))) c2.agree g1
    | tail _ m => exact g2 f m

/-- A line of a place the verifier has shown of a state: what the line says is so. -/
theorem establish_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (env : List (String × SVal)) {e : SExpr}
    {s s' : Sym} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : establish ctx env s e items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hb : EnvB s.nvars env) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ Asserts ctx.defs (semEnv ctx s0 ρ' env) e := by
  unfold establish at h
  obtain ⟨⟨rows, sfacts, s1⟩, r1, e1, h⟩ := V.bind_ok h
  obtain ⟨_, r2, e2, h⟩ := V.bind_ok h
  obtain ⟨ρ1, c1, br, bf, iff1⟩ := assertion_sound E env e1 H wf hb
  have hrows : ∀ r ∈ rows, r.holds ρ1 := fun r m => by
    obtain ⟨items', r', hr⟩ := each_mem e2 r m
    exact entail_sound hr ρ1 c1.holds.facts
  obtain ⟨ρ2, c2, hf⟩ := specGoals_sound E sfacts h c1.holds c1.wf bf
  have hf1 : ∀ f ∈ sfacts, f.holds ctx s0 ρ1 := fun f m => SFact.holds_agree (bf f m) c2.agree.symm (hf f m)
  have A := iff1.mp ⟨hrows, hf1⟩
  rw [semEnv_agree (hb.mono c1.mono) c2.agree] at A
  exact ⟨ρ2, c1.then c2, A⟩

theorem establish_all {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (env : List (String × SVal)) :
    ∀ (facts : List SExpr) {s s' : Sym} {items rest : Items} {ρ : Nat → Int} {st : State},
    fold (establish ctx env) s facts items = .ok (s', rest) → Holds ctx s0 ρ s st → WF ctx s → EnvB s.nvars env →
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ ∀ e ∈ facts, Asserts ctx.defs (semEnv ctx s0 ρ' env) e
  | [], s, s', items, rest, ρ, st, h, H, wf, hb => by
    simp only [fold] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨ρ, Carried.here H wf, all_nil⟩
  | e :: more, s, s', items, rest, ρ, st, h, H, wf, hb => by
    simp only [fold] at h
    obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1, a1⟩ := establish_sound E env e1 H wf hb
    obtain ⟨ρ2, c2, a2⟩ := establish_all E env more h c1.holds c1.wf (hb.mono c1.mono)
    refine ⟨ρ2, c1.then c2, fun x m => ?_⟩
    cases m with
    | head => rw [← semEnv_agree (hb.mono c1.mono) c2.agree]; exact a1
    | tail _ m => exact a2 x m

/-- A line of a place taken as known of a state of which it is so: what the verifier then holds is so. -/
theorem suppose_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (env : List (String × SVal)) {e : SExpr}
    {s s' : Sym} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : suppose ctx env s e items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hb : EnvB s.nvars env)
    (A : Asserts ctx.defs (semEnv ctx s0 ρ env) e) : ∃ ρ', Carried ctx s0 ρ s ρ' s' st := by
  unfold suppose at h
  obtain ⟨⟨rows, sfacts, s1⟩, r1, e1, h⟩ := V.bind_ok h
  have := V.pure_ok h
  injection this with h1 _
  subst h1
  obtain ⟨ρ1, c1, br, bf, iff1⟩ := assertion_sound E env e1 H wf hb
  rw [semEnv_agree hb c1.agree] at A
  obtain ⟨hr, hf⟩ := iff1.mpr A
  have H1 := c1.holds
  have w1 := c1.wf
  exact ⟨ρ1, c1.agree, c1.mono,
    ⟨H1.entry, H1.data, H1.reg, H1.small, H1.zf, H1.cf, H1.frame, H1.frameW,
     fun f m => (List.mem_append.mp m).elim (hr f) (H1.facts f), H1.bytes,
     fun f m => (List.mem_append.mp m).elim (hf f) (H1.spec f), H1.mem, H1.wrote, H1.words, H1.known, H1.range⟩,
    ⟨w1.base, w1.reg, w1.zf, w1.cf, w1.frame, w1.frameW,
     fun f m => (List.mem_append.mp m).elim (br f) (w1.facts f), w1.bytes,
     fun f m => (List.mem_append.mp m).elim (bf f) (w1.spec f), w1.wrote, w1.words.mono rfl rfl rfl (Nat.le_refl _), w1.known, w1.range⟩⟩

theorem suppose_all {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (env : List (String × SVal)) :
    ∀ (facts : List SExpr) {s s' : Sym} {items rest : Items} {ρ : Nat → Int} {st : State},
    fold (suppose ctx env) s facts items = .ok (s', rest) → Holds ctx s0 ρ s st → WF ctx s → EnvB s.nvars env →
    (∀ e ∈ facts, Asserts ctx.defs (semEnv ctx s0 ρ env) e) → ∃ ρ', Carried ctx s0 ρ s ρ' s' st
  | [], s, s', items, rest, ρ, st, h, H, wf, hb, A => by
    simp only [fold] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨ρ, Carried.here H wf⟩
  | e :: more, s, s', items, rest, ρ, st, h, H, wf, hb, A => by
    simp only [fold] at h
    obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1⟩ := suppose_sound E env e1 H wf hb (A e (List.mem_cons_self ..))
    obtain ⟨ρ2, c2⟩ := suppose_all E env more h c1.holds c1.wf (hb.mono c1.mono)
      (fun x m => by rw [← semEnv_agree hb c1.agree]; exact A x (List.mem_cons_of_mem _ m))
    exact ⟨ρ2, c1.then c2⟩

end Ode
