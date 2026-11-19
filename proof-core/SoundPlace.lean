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
    (h : assertion ctx env s e items = .ok ((rows, sfacts, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (hb : EnvB s.nvars env) :
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
    fold (specGoal ctx 16) s goals items = .ok (s', rest) → Holds ctx s0 ρ s st → WF s → (∀ f ∈ goals, f.bounded s.nvars) →
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
    (h : establish ctx env s e items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (hb : EnvB s.nvars env) :
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
    fold (establish ctx env) s facts items = .ok (s', rest) → Holds ctx s0 ρ s st → WF s → EnvB s.nvars env →
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
    (h : suppose ctx env s e items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (hb : EnvB s.nvars env)
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
    ⟨H1.entry, H1.reg, H1.small, H1.zf, H1.cf, H1.frame,
     fun f m => (List.mem_append.mp m).elim (hr f) (H1.facts f), H1.bytes,
     fun f m => (List.mem_append.mp m).elim (hf f) (H1.spec f), H1.mem, H1.wrote, H1.words⟩,
    ⟨w1.base, w1.reg, w1.zf, w1.cf, w1.frame,
     fun f m => (List.mem_append.mp m).elim (br f) (w1.facts f), w1.bytes,
     fun f m => (List.mem_append.mp m).elim (bf f) (w1.spec f), w1.wrote, w1.words.mono rfl rfl rfl (Nat.le_refl _)⟩⟩

theorem suppose_all {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (env : List (String × SVal)) :
    ∀ (facts : List SExpr) {s s' : Sym} {items rest : Items} {ρ : Nat → Int} {st : State},
    fold (suppose ctx env) s facts items = .ok (s', rest) → Holds ctx s0 ρ s st → WF s → EnvB s.nvars env →
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

/-! ## What a place says of the machine -/

/-- The names of a place as values, in a state of the machine there: a name the place gives is what its
register holds; the contract's names are what they were at entry. -/
def placeVals (ctx : Ctx) (pl : Place) (s0 st : State) : List (String × Val) :=
  pl.names.map (fun nr => (nr.1, Val.int (st.reg nr.2))) ++ ctx.contract.env s0

theorem semEnv_placeEnv {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (pl : Place)
    (hentry : ∀ r, r < 16 → ρ r = s0.reg r) (hreg : ∀ r, r < 16 → (st.reg r : Int) = ev ρ (s.reg r))
    (hn : ∀ nr ∈ pl.names, nr.2 < 16) :
    semEnv ctx s0 ρ (placeEnv ctx pl s.reg) = placeVals ctx pl s0 st := by
  have h2 := semEnv_symEnv ctx s0 ρ hentry
  unfold semEnv at h2 ⊢
  unfold placeEnv placeVals
  rw [List.map_append, List.map_map, h2]
  congr 1
  apply List.map_congr_left
  intro ⟨n, r⟩ m
  simp only [Function.comp, semv]
  rw [hreg r (hn (n, r) m)]

theorem placeEnv_bounded {ctx : Ctx} (pl : Place) {s : Sym} (wf : WF s) (hn : ∀ nr ∈ pl.names, nr.2 < 16) :
    EnvB s.nvars (placeEnv ctx pl s.reg) := by
  intro nv m
  unfold placeEnv at m
  rcases List.mem_append.mp m with m | m
  · obtain ⟨⟨n, r⟩, hm, rfl⟩ := List.mem_map.mp m
    exact wf.reg r (hn (n, r) hm)
  · exact (symEnv_bounded ctx.contract).mono wf.base nv m

/-- What a place says of a state of the machine there, `first` being what the verifier held when a path
first came there and `ρs` what its unknowns then were: those unknowns are still what they were, the
registers kept and the frame are as `first` has them, memory outside the frame is as at entry, and the
place's facts are so of what the named registers hold. -/
structure AtPlace (ctx : Ctx) (pl : Place) (s0 : State) (first : Sym) (ρs ρ : Nat → Int) (st : State) : Prop where
  outer : Agree first.nvars ρs ρ
  entry : ∀ r, r < 16 → ρ r = s0.reg r
  kept : ∀ r, r < 16 → pl.keep.contains r = true → (st.reg r : Int) = ev ρ (first.reg r)
  small : ∀ r, st.reg r < M64
  frame : ∀ o v, (o, v) ∈ first.frame →
    -(ctx.contract.stack : Int) ≤ o ∧ o + 8 ≤ 0 ∧ (load st.mem ((s0.reg RSP : Int) + o).toNat 8 : Int) = ev ρ v
  mem : ∀ a, ctx.contract.inFrame s0 a = false → ctx.contract.inOut s0 a = false → st.mem a = s0.mem a
  facts : ∀ e ∈ pl.facts, Asserts ctx.defs (placeVals ctx pl s0 st) e

theorem general_wf (pl : Place) {first : Sym} (wf : WF first) : WF (first.general pl) := by
  have le : first.nvars ≤ first.nvars + 16 := Nat.le_add_right _ _
  refine ⟨Nat.le_add_left _ _, ?_, trivial, trivial, ?_, ?_,
          (fun v r o m => ⟨Nat.lt_of_lt_of_le (wf.bytes v r o m).1 le, bounded_mono le (wf.bytes v r o m).2⟩),
          (fun f m => SFact.bounded_mono le (wf.spec f m)), (fun _ _ _ m => nomatch m),
          ⟨wf.words.table, fun j r h => bounded_mono le (wf.words.atoms j r h), fun x ids h => by simp [Sym.general] at h,
           wf.words.rotrs, fun w j i h => by simp [Sym.general] at h⟩⟩
  · intro r hr
    show bounded (first.nvars + 16) (if pl.keep.contains r = true then first.reg r else Lin.var (first.nvars + r))
    split
    · exact bounded_mono (Nat.le_add_right _ _) (wf.reg r hr)
    · exact bounded_var (by omega)
  · intro o v m
    exact bounded_mono (Nat.le_add_right _ _) (wf.frame o v m)
  · intro f m
    simp only [Sym.general, List.mem_append] at m
    rcases m with m | m
    · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp m
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
      have hr := List.mem_range.mp (List.mem_filter.mp hr).1
      simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · exact bounded_var (show first.nvars + r < first.nvars + 16 by omega)
      · exact bounded_sub (bounded_const _ _) (bounded_var (show first.nvars + r < first.nvars + 16 by omega))
    · exact bounded_mono le (wf.facts f m)

/-- Of every state of the machine of which the place says what it says, what the general state holds is
so: the registers not kept are the unknowns the general state made for them, and what was so of the
unknowns of before, when the path first came there, is so still. -/
theorem general_holds {ctx : Ctx} {s0 : State} (pl : Place) {first : Sym} (wf : WF first)
    {ρs ρ : Nat → Int} {stf st : State} (Hf : Holds ctx s0 ρs first stf) (A : AtPlace ctx pl s0 first ρs ρ st) :
    Holds ctx s0 (fun k => if first.nvars ≤ k ∧ k < first.nvars + 16 then (st.reg (k - first.nvars) : Int) else ρ k)
      (first.general pl) st := by
  have ag : Agree first.nvars ρ (fun k => if first.nvars ≤ k ∧ k < first.nvars + 16 then (st.reg (k - first.nvars) : Int) else ρ k) := by
    intro k hk
    show ρ k = if first.nvars ≤ k ∧ k < first.nvars + 16 then (st.reg (k - first.nvars) : Int) else ρ k
    rw [if_neg (by omega)]
  have base := wf.base
  have hentry : ∀ r, r < 16 → (fun k => if first.nvars ≤ k ∧ k < first.nvars + 16 then (st.reg (k - first.nvars) : Int) else ρ k) r = s0.reg r := by
    intro r hr
    show (if first.nvars ≤ r ∧ r < first.nvars + 16 then (st.reg (r - first.nvars) : Int) else ρ r) = s0.reg r
    rw [if_neg (by omega)]
    exact A.entry r hr
  have Hg := Hf.agree wf (Agree.trans (Nat.le_refl _) A.outer ag)
  refine ⟨hentry, ?_, A.small, trivial, trivial, ?_, ?_, Hg.bytes, Hg.spec, A.mem, (fun _ _ _ m => nomatch m),
    ⟨fun x ids h => by simp [Sym.general] at h, fun w m => by simp [Sym.general] at m, fun w j i m => by simp [Sym.general] at m⟩⟩
  · intro r hr
    show (st.reg r : Int) = ev _ (if pl.keep.contains r = true then first.reg r else Lin.var (first.nvars + r))
    by_cases hk : pl.keep.contains r = true
    · rw [if_pos hk, ← ev_agree (wf.reg r hr) ag]
      exact A.kept r hr hk
    · rw [if_neg hk, ev_var]
      show (st.reg r : Int) = if first.nvars ≤ first.nvars + r ∧ first.nvars + r < first.nvars + 16 then (st.reg (first.nvars + r - first.nvars) : Int) else ρ (first.nvars + r)
      rw [if_pos (by omega), Nat.add_sub_cancel_left]
  · intro o v m
    obtain ⟨h1, h2, h3⟩ := A.frame o v m
    exact ⟨h1, h2, by rw [← ev_agree (wf.frame o v m) ag]; exact h3⟩
  · intro f m
    simp only [Sym.general, List.mem_append] at m
    rcases m with m | m
    · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp m
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
      have hr := List.mem_range.mp (List.mem_filter.mp hr).1
      have sm := A.small r
      unfold M64 at sm
      have val : (if first.nvars ≤ first.nvars + r ∧ first.nvars + r < first.nvars + 16 then (st.reg (first.nvars + r - first.nvars) : Int) else ρ (first.nvars + r)) = st.reg r := by
        rw [if_pos (by omega), Nat.add_sub_cancel_left]
      simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · rw [holds_iff, ev_var, val]; omega
      · rw [holds_iff, ev_sub, ev_const, ev_var, val]; simp only [top]; omega
    · exact Hg.facts f m

/-- The verifier's work when a path first comes to a place: of the state it came in, the place says what
it says; and of every state of which the place says so (the unknowns of before being what they were), what
the general state holds is so, and the place's number there is the general state's number, no less than
zero. -/
theorem generalize_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (pl : Place) {s g first : Sym} {d : Row}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : generalize ctx pl s items = .ok ((g, d, first), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) :
    (∀ nr ∈ pl.names, nr.2 < 16) ∧ ∃ ρ1, Agree s.nvars ρ ρ1 ∧ s.nvars ≤ first.nvars ∧ AtPlace ctx pl s0 first ρ1 ρ1 st ∧
      WF g ∧ first.nvars ≤ g.nvars ∧ bounded g.nvars d ∧
      ∀ ρ' st', AtPlace ctx pl s0 first ρ1 ρ' st' →
        ∃ ρ'', Holds ctx s0 ρ'' g st' ∧ Agree first.nvars ρ' ρ'' ∧ 0 ≤ ev ρ'' d ∧
          Value ctx.defs (placeVals ctx pl s0 st') pl.decreases (.int (ev ρ'' d)) := by
  unfold generalize at h
  split at h
  next => exact (refuse_ok h).elim
  next hguard =>
    have hnames : ∀ nr ∈ pl.names, nr.2 < 16 := by
      intro ⟨n, r⟩ m
      show r < 16
      by_cases c : r < 16
      · exact c
      · exfalso
        apply hguard
        simp only [Bool.or_eq_true]
        right
        exact List.any_eq_true.mpr ⟨(n, r), m, by simp only [decide_eq_true_eq]; omega⟩
    obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨g1, r2, e2, h⟩ := V.bind_ok h
    obtain ⟨⟨dres, g2⟩, r3, e3, h⟩ := V.bind_ok h
    have envb : EnvB s.nvars (placeEnv ctx pl s.reg) := placeEnv_bounded pl wf hnames
    obtain ⟨ρ1, c1, a1⟩ := establish_all E _ pl.facts e1 H wf envb
    have env1 : semEnv ctx s0 ρ1 (placeEnv ctx pl s.reg) = placeVals ctx pl s0 st := by
      rw [← semEnv_agree envb c1.agree]
      exact semEnv_placeEnv pl H.entry H.reg hnames
    have first_at : AtPlace ctx pl s0 s1 ρ1 ρ1 st :=
      ⟨Agree.refl _ _, c1.holds.entry, fun r hr _ => c1.holds.reg r hr, c1.holds.small, c1.holds.frame, c1.holds.mem,
       fun e m => by rw [← env1]; exact a1 e m⟩
    cases dres with
    | list _ => exact (refuse_ok h).elim
    | tail _ => exact (refuse_ok h).elim
    | val v =>
      cases v with
      | region _ => exact (refuse_ok h).elim
      | bool _ => exact (refuse_ok h).elim
      | lin d' =>
        simp only at h
        obtain ⟨_, r4, e4, h⟩ := V.bind_ok h
        have := V.pure_ok h
        injection this with h1 _
        injection h1 with hg h2
        injection h2 with hd hf
        rw [hg, hd, hf]
        have G : ∀ ρ' st', AtPlace ctx pl s0 s1 ρ1 ρ' st' →
            ∃ ρ'', Holds ctx s0 ρ'' g2 st' ∧ WF g2 ∧ s1.nvars ≤ g2.nvars ∧ Agree s1.nvars ρ' ρ'' ∧ bounded g2.nvars d' ∧ 0 ≤ ev ρ'' d' ∧
              Value ctx.defs (placeVals ctx pl s0 st') pl.decreases (.int (ev ρ'' d')) := by
          intro ρ' st' A
          have H0 := general_holds pl c1.wf c1.holds A
          have ag0 : Agree s1.nvars ρ' (fun k => if s1.nvars ≤ k ∧ k < s1.nvars + 16 then (st'.reg (k - s1.nvars) : Int) else ρ' k) := by
            intro k hk
            show ρ' k = if s1.nvars ≤ k ∧ k < s1.nvars + 16 then (st'.reg (k - s1.nvars) : Int) else ρ' k
            rw [if_neg (by omega)]
          have w0 := general_wf pl c1.wf
          have envb0 : EnvB (s1.general pl).nvars (placeEnv ctx pl (s1.general pl).reg) := placeEnv_bounded pl w0 hnames
          have env0 := semEnv_placeEnv (ctx := ctx) pl H0.entry H0.reg hnames
          obtain ⟨ρa, ca⟩ := suppose_all E _ pl.facts e2 H0 w0 envb0 (fun e m => by rw [env0]; exact A.facts e m)
          obtain ⟨ρb, cb, sem, bd⟩ := seval_sound E _ pl.decreases e3 ca.holds ca.wf (envb0.mono ca.mono)
          have env2 : semEnv ctx s0 ρb (placeEnv ctx pl (s1.general pl).reg) = placeVals ctx pl s0 st' := by
            rw [← semEnv_agree envb0 (ca.then cb).agree]; exact env0
          rw [env2] at sem
          exact ⟨ρb, cb.holds, cb.wf, Nat.le_trans (Nat.le_add_right _ 16) (ca.then cb).mono,
                 Agree.trans (Nat.le_add_right _ 16) ag0 (ca.then cb).agree, bd, entail_sound e4 ρb cb.holds.facts, sem⟩
        obtain ⟨ρx, Hx, wg, leg, _, bdd, _, _⟩ := G ρ1 st first_at
        refine ⟨hnames, ρ1, c1.agree, c1.mono, first_at, wg, leg, bdd, ?_⟩
        intro ρ' st' A
        obtain ⟨ρ'', Hh, _, _, agx, _, pos, val⟩ := G ρ' st' A
        exact ⟨ρ'', Hh, agx, pos, val⟩

/-- The verifier's work when a path comes again to a place: of the state of the machine there the place
says what it says, and the place's number there is less than `d` was. -/
theorem arrive_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (pl : Place) (hn : ∀ nr ∈ pl.names, nr.2 < 16)
    {first s : Sym} {d : Row} {items : Items} {r : Unit × Items} {ρ : Nat → Int} {st : State}
    (h : arrive ctx pl first d s items = .ok r) (H : Holds ctx s0 ρ s st) (wf : WF s) (hd : bounded s.nvars d) :
    AtPlace ctx pl s0 first ρ ρ st ∧
    ∃ n : Int, Value ctx.defs (placeVals ctx pl s0 st) pl.decreases (.int n) ∧ n + 1 ≤ ev ρ d := by
  cases hfind : pl.keep.find? (fun r => s.reg r != first.reg r) with
  | some _ => simp only [arrive, hfind] at h; exact (refuse_ok h).elim
  | none =>
    simp only [arrive, hfind] at h
    split at h
    next => exact (refuse_ok h).elim
    next hframe =>
      have hkeep : ∀ r, pl.keep.contains r = true → s.reg r = first.reg r := by
        intro r hr
        have hm : r ∈ pl.keep := List.contains_iff_mem.mp hr
        have := List.find?_eq_none.mp hfind r hm
        by_cases c : s.reg r = first.reg r
        · exact c
        · exact absurd (bne_iff_ne.mpr c) this
      have hall : (first.frame.all fun cell => s.frame.contains cell) = true := by
        cases hx : (first.frame.all fun cell => s.frame.contains cell) with
        | true => rfl
        | false => rw [hx] at hframe; exact (hframe rfl).elim
      have hfr : ∀ o v, (o, v) ∈ first.frame → (o, v) ∈ s.frame := fun o v m =>
        List.contains_iff_mem.mp (List.all_eq_true.mp hall (o, v) m)
      obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
      obtain ⟨⟨dres, s2⟩, r2, e2, h⟩ := V.bind_ok h
      have envb : EnvB s.nvars (placeEnv ctx pl s.reg) := placeEnv_bounded pl wf hn
      have env0 := semEnv_placeEnv (ctx := ctx) pl H.entry H.reg hn
      obtain ⟨ρ1, c1, a1⟩ := establish_all E _ pl.facts e1 H wf envb
      obtain ⟨ρ2, c2, sem, bd⟩ := seval_sound E _ pl.decreases e2 c1.holds c1.wf (envb.mono c1.mono)
      have env1 : semEnv ctx s0 ρ1 (placeEnv ctx pl s.reg) = placeVals ctx pl s0 st := by
        rw [← semEnv_agree envb c1.agree]; exact env0
      have env2 : semEnv ctx s0 ρ2 (placeEnv ctx pl s.reg) = placeVals ctx pl s0 st := by
        rw [← semEnv_agree envb (c1.then c2).agree]; exact env0
      refine ⟨⟨Agree.refl _ _, H.entry, (fun r hr hk => by rw [← hkeep r hk]; exact H.reg r hr), H.small,
               (fun o v m => H.frame o v (hfr o v m)), H.mem, (fun e m => by rw [← env1]; exact a1 e m)⟩, ?_⟩
      cases dres with
      | list _ => exact (refuse_ok h).elim
      | tail _ => exact (refuse_ok h).elim
      | val v =>
        cases v with
        | region _ => exact (refuse_ok h).elim
        | bool _ => exact (refuse_ok h).elim
        | lin d' =>
          simp only at h
          have g := entail_sound h ρ2 c2.holds.facts
          simp only [ev_sub, ev_const] at g
          rw [env2] at sem
          refine ⟨ev ρ2 d', sem, ?_⟩
          rw [ev_agree hd (c1.then c2).agree]
          omega

end Ode
