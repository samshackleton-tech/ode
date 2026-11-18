import SoundSpec
/-!
# Why the verifier's yes is right, 5b: a list of the specification, and what an `ensures` says
-/
namespace Ode
open Arithmetic

/-- A list of numbers, none below zero, as the numbers they are. -/
def asList : List Val → Option (List Nat)
  | [] => some []
  | .int k :: rest => if 0 ≤ k then (asList rest).map (k.toNat :: ·) else none
  | _ => none

theorem asList_bytes : ∀ {vals : List Val} {l : List Nat}, asList vals = some l → vals = l.map fun (b : Nat) => Val.int b
  | [], l, h => by simp only [asList] at h; injection h with h; subst h; rfl
  | .int k :: rest, l, h => by
    simp only [asList] at h
    split at h
    next hk =>
      cases hr : asList rest with
      | none => simp [hr] at h
      | some l' =>
        simp only [hr, Option.map_some] at h
        injection h with h
        subst h
        rw [asList_bytes hr]
        simp [Int.toNat_of_nonneg hk]
    next => contradiction
  | .bool _ :: _, _, h => by simp [asList] at h
  | .word _ :: _, _, h => by simp [asList] at h
  | .counter _ :: _, _, h => by simp [asList] at h
  | .list _ :: _, _, h => by simp [asList] at h
  | .record _ :: _, _, h => by simp [asList] at h

theorem Value.list {defs : List Def} {env : List (String × Val)} {items : SExpr} {vals : List Val} {l : List Nat}
    (h : Values defs env items vals) (ha : asList vals = some l) : Value defs env (.list items) (.bytes l) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f + 1, by simp [evalSpec, hf, Val.bytes, asList_bytes ha]⟩

/-- The numbers rows stand for, as the things of a list. -/
def listOf (ρ : Nat → Int) (rows : List Row) : List Nat := rows.map fun r => (ev ρ r).toNat

theorem listOf_agree {n : Nat} {ρ ρ' : Nat → Int} {rows : List Row} (hb : ∀ r ∈ rows, bounded n r) (a : Agree n ρ ρ') :
    listOf ρ rows = listOf ρ' rows := by
  unfold listOf
  exact List.map_congr_left fun r m => by rw [ev_agree (hb r m) a]

/-- The things of a list written out are numbers no less than zero. -/
theorem numbers_sound {ctx : Ctx} {s0 : State} {facts : List Row} {ρ : Nat → Int} (hf : ∀ f ∈ facts, f.holds ρ) {n : Nat} :
    ∀ {vs : List SVal} {rows : List Row} {items rest : List Item}, numbers facts vs items = .ok (rows, rest) → (∀ v ∈ vs, v.bounded n) →
      asList (vs.map (semv ctx s0 ρ)) = some (listOf ρ rows) ∧ (∀ r ∈ rows, 0 ≤ ev ρ r) ∧ (∀ r ∈ rows, bounded n r)
  | [], rows, items, rest, h, _ => by
    simp only [numbers] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨rfl, (fun _ m => nomatch m), (fun _ m => nomatch m)⟩
  | .lin v :: more, rows, items, rest, h, hb => by
    simp only [numbers] at h
    obtain ⟨_, r1, g1, h⟩ := V.bind_ok h
    obtain ⟨rest', r2, g2, h⟩ := V.bind_ok h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    have g1 := entail_sound g1 ρ hf
    obtain ⟨a1, a2, a3⟩ := numbers_sound (ctx := ctx) (s0 := s0) hf g2 (fun v m => hb v (List.mem_cons_of_mem _ m))
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.map_cons, semv, asList, a1, listOf, if_pos g1, Option.map_some]
    · intro r m
      rcases List.mem_cons.mp m with rfl | m
      · exact g1
      · exact a2 r m
    · intro r m
      rcases List.mem_cons.mp m with rfl | m
      · exact hb (.lin r) (List.mem_cons_self ..)
      · exact a3 r m
  | .region _ :: _, _, _, _, h, _ => by simp only [numbers] at h; exact (refuse_ok h).elim
  | .bool _ :: _, _, _, _, h, _ => by simp only [numbers] at h; exact (refuse_ok h).elim

/-- **A list of the specification, on symbols.** The rows that come out are the things of the list the
expression is, each no less than zero. -/
theorem slist_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) :
    ∀ (fuel : Nat) (env : List (String × SVal)) (e : SExpr) {s s' : Sym} {rows : List Row} {items rest : List Item} {ρ : Nat → Int} {st : State},
    slist ctx fuel env s e items = .ok ((rows, s'), rest) → Holds ctx s0 ρ s st → WF s → EnvB s.nvars env →
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ (∀ r ∈ rows, bounded s'.nvars r) ∧ (∀ r ∈ rows, 0 ≤ ev ρ' r) ∧
      Value ctx.defs (semEnv ctx s0 ρ' env) e (.bytes (listOf ρ' rows))
  | 0, _, _, _, _, _, _, _, _, _, h, _, _, _ => by simp only [slist] at h; exact (refuse_ok h).elim
  | fuel + 1, env, e, s, s', rows, items, rest, ρ, st, h, H, wf, hb => by
    cases e with
    | num _ => simp only [slist] at h; exact (refuse_ok h).elim
    | name _ => simp only [slist] at h; exact (refuse_ok h).elim
    | index _ _ => simp only [slist] at h; exact (refuse_ok h).elim
    | nil => simp only [slist] at h; exact (refuse_ok h).elim
    | cons _ _ => simp only [slist] at h; exact (refuse_ok h).elim
    | letx _ _ _ => simp only [slist] at h; exact (refuse_ok h).elim
    | each _ _ _ _ => simp only [slist] at h; exact (refuse_ok h).elim
    | slice _ _ _ => simp only [slist] at h; exact (refuse_ok h).elim
    | withx _ _ => simp only [slist] at h; exact (refuse_ok h).elim
    | record _ _ => simp only [slist] at h; exact (refuse_ok h).elim
    | field _ _ => simp only [slist] at h; exact (refuse_ok h).elim
    | theNumber _ _ _ _ _ => simp only [slist] at h; exact (refuse_ok h).elim
    | thePower _ _ _ => simp only [slist] at h; exact (refuse_ok h).elim
    | list l =>
      simp only [slist] at h
      obtain ⟨⟨vs, s1⟩, r1, e1, h⟩ := V.bind_ok h
      obtain ⟨ρ1, c1, sem, bd⟩ := seval_sound E env l e1 H wf hb
      cases vs with
      | val _ => exact (refuse_ok h).elim
      | tail _ => exact (refuse_ok h).elim
      | list vs =>
        simp only at h
        obtain ⟨rows', r2, e2, h⟩ := V.bind_ok h
        have := V.pure_ok h
        injection this with h1 _
        injection h1 with h1 h2
        subst h1 h2
        obtain ⟨a1, a2, a3⟩ := numbers_sound (ctx := ctx) (s0 := s0) c1.holds.facts e2 bd
        exact ⟨ρ1, c1, a3, a2, Value.list sem a1⟩
    | bin op a b =>
      simp only [slist] at h
      split at h
      next hop =>
        have : op = "++" := by simpa using hop
        subst this
        obtain ⟨⟨x, s1⟩, r1, e1, h⟩ := V.bind_ok h
        obtain ⟨⟨y, s2⟩, r2, e2, h⟩ := V.bind_ok h
        have := V.pure_ok h
        injection this with h1 _
        injection h1 with h1 h2
        subst h1 h2
        obtain ⟨ρ1, c1, b1, z1, v1⟩ := slist_sound E fuel env a e1 H wf hb
        have hb1 : EnvB s1.nvars env := hb.mono c1.mono
        obtain ⟨ρ2, c2, b2, z2, v2⟩ := slist_sound E fuel env b e2 c1.holds c1.wf hb1
        refine ⟨ρ2, c1.then c2, ?_, ?_, ?_⟩
        · intro r m
          rcases List.mem_append.mp m with m | m
          · exact bounded_mono c2.mono (b1 r m)
          · exact b2 r m
        · intro r m
          rcases List.mem_append.mp m with m | m
          · rw [← ev_agree (b1 r m) c2.agree]; exact z1 r m
          · exact z2 r m
        · rw [semEnv_agree hb1 c2.agree, listOf_agree b1 c2.agree] at v1
          have : listOf ρ2 (x ++ y) = listOf ρ2 x ++ listOf ρ2 y := by simp [listOf]
          rw [this]
          exact Value.bin v1 v2 (by simp [binop, Val.bytes])
      next => exact (refuse_ok h).elim
    | ifx c a b =>
      simp only [slist] at h
      obtain ⟨⟨cv, s1⟩, r1, e1, h⟩ := V.bind_ok h
      obtain ⟨ρ1, c1, sem, bd⟩ := seval_sound E env c e1 H wf hb
      have hb1 : EnvB s1.nvars env := hb.mono c1.mono
      cases cv with
      | tail _ => exact (refuse_ok h).elim
      | list _ => exact (refuse_ok h).elim
      | val v =>
        cases v with
        | lin _ => exact (refuse_ok h).elim
        | region _ => exact (refuse_ok h).elim
        | bool t =>
          simp only [SRes.sem, semv] at sem
          cases t with
          | true =>
            simp only [if_true] at h
            obtain ⟨ρ2, c2, b2, z2, v2⟩ := slist_sound E fuel env a h c1.holds c1.wf hb1
            rw [semEnv_agree hb1 c2.agree] at sem
            exact ⟨ρ2, c1.then c2, b2, z2, (Value.ifx sem _).mpr (by simpa using v2)⟩
          | false =>
            simp only [Bool.false_eq_true, if_false] at h
            obtain ⟨ρ2, c2, b2, z2, v2⟩ := slist_sound E fuel env b h c1.holds c1.wf hb1
            rw [semEnv_agree hb1 c2.agree] at sem
            exact ⟨ρ2, c1.then c2, b2, z2, (Value.ifx sem _).mpr (by simpa using v2)⟩
    | call f args =>
      simp only [slist] at h
      obtain ⟨⟨vs, s1⟩, r1, e1, h⟩ := V.bind_ok h
      obtain ⟨ρ1, c1, sem, bd⟩ := seval_sound E env args e1 H wf hb
      have hb1 : EnvB s1.nvars env := hb.mono c1.mono
      cases vs with
      | val _ => exact (refuse_ok h).elim
      | tail _ => exact (refuse_ok h).elim
      | list vs =>
        simp only at h
        split at h
        next => exact (refuse_ok h).elim
        next hlen =>
          split at h
          next => exact (refuse_ok h).elim
          next ho =>
            cases hd : findDef ctx.defs f with
            | none => simp only [hd] at h; exact (refuse_ok h).elim
            | some d =>
              simp only [hd] at h
              split at h
              next hp =>
                have henv : EnvB s1.nvars (d.params.zip vs) := fun nv m => bd nv.2 (mem_zip_right m)
                obtain ⟨ρ2, c2, b2, z2, v2⟩ := slist_sound E fuel (d.params.zip vs) d.body h c1.holds c1.wf henv
                rw [semEnv_zip] at v2
                simp only [SRes.sem] at sem
                rw [semEnv_agree hb1 c2.agree] at sem
                have hvs : vs.map (semv ctx s0 ρ1) = vs.map (semv ctx s0 ρ2) :=
                  List.map_congr_left fun v m => semv_agree (bd v m) c2.agree
                rw [hvs] at sem
                exact ⟨ρ2, c1.then c2, b2, z2, (Value.call (by simpa using hlen) (by simpa using ho) hd (by simpa using hp) sem _).mpr v2⟩
              next => exact (refuse_ok h).elim

/-! ## An `ensures`, at the return -/

theorem findOutNamed_spec {name : String} : ∀ {l : List (String × Nat × Nat)} {k w n : Nat}, findOutNamed name l k = some (w, n) →
    ∃ r, k ≤ w ∧ l[w - k]? = some (name, r, n)
  | [], _, _, _, h => by simp [findOutNamed] at h
  | (x, r, n') :: more, k, w, n, h => by
    simp only [findOutNamed] at h
    split at h
    next hx =>
      injection h with h
      injection h with h1 h2
      subst h1 h2
      have : x = name := by simpa using hx
      subst this
      exact ⟨r, Nat.le_refl _, by simp⟩
    next =>
      obtain ⟨r', hk, hr⟩ := findOutNamed_spec h
      refine ⟨r', by omega, ?_⟩
      have : w - k = (w - (k + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]; exact hr

theorem wroteAt_spec {w : Nat} {place : Row} : ∀ {l : List (Nat × Row × Row)} {x : Row}, wroteAt w place l = some x →
    ∃ o, (w, o, x) ∈ l ∧ Lin.isConst (Lin.sub o place) = some 0
  | [], _, h => by simp [wroteAt] at h
  | (w', o, x') :: more, x, h => by
    simp only [wroteAt] at h
    split at h
    next hc =>
      injection h with h
      subst h
      obtain ⟨e1, e2⟩ := hc
      subst e1
      exact ⟨o, List.mem_cons_self .., e2⟩
    next =>
      obtain ⟨o', m, e⟩ := wroteAt_spec h
      exact ⟨o', List.mem_cons_of_mem _ m, e⟩

/-- The things of a list, each shown to be what is known written at its place. -/
theorem written_sound {facts : List Row} {wrote : List (Nat × Row × Row)} {w : Nat} {lo : Row} {ρ : Nat → Int} (hf : ∀ f ∈ facts, f.holds ρ) :
    ∀ {k : Nat} {rows : List Row} {items : List Item} {r : Unit × List Item}, written facts wrote w lo k rows items = .ok r →
      ∀ j (hj : j < rows.length), ∃ o x, (w, o, x) ∈ wrote ∧ ev ρ o = ev ρ lo + ((k + j : Nat) : Int) ∧ ev ρ x = ev ρ rows[j]
  | _, [], _, _, _ => fun j hj => absurd hj (by simp)
  | k, v :: more, items, r, h => by
    simp only [written] at h
    cases hw : wroteAt w (Lin.add lo (Lin.const (k : Int))) wrote with
    | none => simp only [hw] at h; exact (refuse_ok h).elim
    | some x =>
      simp only [hw] at h
      obtain ⟨_, r1, g1, h⟩ := V.bind_ok h
      obtain ⟨_, r2, g2, h⟩ := V.bind_ok h
      have g1 := entail_sound g1 ρ hf
      have g2 := entail_sound g2 ρ hf
      simp only [ev_sub] at g1 g2
      obtain ⟨o, m, e⟩ := wroteAt_spec hw
      have e := ev_isConst (ρ := ρ) e
      simp only [ev_sub, ev_add, ev_const] at e
      intro j hj
      cases j with
      | zero => exact ⟨o, x, m, by simp only [Nat.add_zero]; omega, by simp only [List.getElem_cons_zero]; omega⟩
      | succ j =>
        obtain ⟨o', x', m', e1, e2⟩ := written_sound hf h j (by simpa using hj)
        exact ⟨o', x', m', by omega, by simpa using e2⟩

/-- **One `ensures`.** Where the verifier has passed it, it holds of the state at the return (`st'`, whose
memory is that of the state `st` the verifier is at). -/
theorem symEnsure_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {env : List (String × SVal)} {s s' : Sym}
    {e : Ensure} {items rest : List Item} {ρ : Nat → Int} {st st' : State}
    (h : symEnsure ctx env s e items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (hb : EnvB s.nvars env)
    (henv : ∀ ρ', Agree s.nvars ρ ρ' → semEnv ctx s0 ρ' env = ctx.contract.envAfter s0 st') (hmem : st'.mem = st.mem) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ e.holds ctx.contract ctx.defs s0 st' := by
  unfold symEnsure at h
  cases hfo : findOutNamed e.run ctx.contract.outs 0 with
  | none => simp only [hfo] at h; exact (refuse_ok h).elim
  | some wn =>
    obtain ⟨w, n⟩ := wn
    simp only [hfo] at h
    obtain ⟨r, _, hw⟩ := findOutNamed_spec hfo
    simp only [Nat.sub_zero] at hw
    obtain ⟨⟨rows, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨⟨rlo, s2⟩, r2, e2, h⟩ := V.bind_ok h
    obtain ⟨⟨lo, s3⟩, r3, e3, h⟩ := V.bind_ok h
    obtain ⟨⟨rhi, s4⟩, r4, e4, h⟩ := V.bind_ok h
    obtain ⟨⟨hi, s5⟩, r5, e5, h⟩ := V.bind_ok h
    obtain ⟨_, r6, g1, h⟩ := V.bind_ok h
    obtain ⟨_, r7, g2, h⟩ := V.bind_ok h
    obtain ⟨_, r8, g3, h⟩ := V.bind_ok h
    obtain ⟨_, r9, g4, h⟩ := V.bind_ok h
    obtain ⟨_, r10, g5, h⟩ := V.bind_ok h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    obtain ⟨ρ1, c1, b1, z1, v1⟩ := slist_sound E LIST env e.value e1 H wf hb
    have hb1 : EnvB s1.nvars env := hb.mono c1.mono
    obtain ⟨ρ2, c2, sem2, bd2⟩ := seval_sound E env e.lo e2 c1.holds c1.wf hb1
    obtain ⟨ρ3, c3, vlo, blo⟩ := numberV_sound (opener_sound E DEEP) c2.holds c2.wf e3 sem2 bd2
    have hb3 : EnvB s3.nvars env := hb1.mono (Nat.le_trans c2.mono c3.mono)
    obtain ⟨ρ4, c4, sem4, bd4⟩ := seval_sound E env e.hi e4 c3.holds c3.wf hb3
    obtain ⟨ρ5, c5, vhi, bhi⟩ := numberV_sound (opener_sound E DEEP) c4.holds c4.wf e5 sem4 bd4
    have a1 : Agree s.nvars ρ ρ1 := c1.agree
    have a2 : Agree s.nvars ρ ρ2 := Agree.trans c1.mono a1 c2.agree
    have a3 : Agree s.nvars ρ ρ3 := Agree.trans (Nat.le_trans c1.mono c2.mono) a2 c3.agree
    have a4 : Agree s.nvars ρ ρ4 := Agree.trans (Nat.le_trans (Nat.le_trans c1.mono c2.mono) c3.mono) a3 c4.agree
    rw [henv ρ1 a1] at v1
    rw [henv ρ2 a2] at vlo
    rw [henv ρ4 a4] at vhi
    have ag35 : Agree s3.nvars ρ3 ρ5 := Agree.trans c4.mono c4.agree c5.agree
    have ag15 : Agree s1.nvars ρ1 ρ5 := Agree.trans c2.mono c2.agree (Agree.trans c3.mono c3.agree ag35)
    rw [listOf_agree b1 ag15] at v1
    rw [ev_agree blo ag35] at vlo
    have g1 := entail_sound g1 ρ5 c5.holds.facts
    have g2 := entail_sound g2 ρ5 c5.holds.facts
    have g3 := entail_sound g3 ρ5 c5.holds.facts
    have g4 := entail_sound g4 ρ5 c5.holds.facts
    simp only [ev_sub, ev_add, ev_const] at g2 g3 g4
    have wr := written_sound (ρ := ρ5) c5.holds.facts g5
    refine ⟨ρ5, c1.then (c2.then (c3.then (c4.then c5))), ?_⟩
    unfold Ensure.holds
    refine ⟨r, n, ev ρ5 lo, ev ρ5 hi, listOf ρ5 rows, List.mem_of_getElem? hw, vlo, vhi, v1, g1, ?_, by omega, ?_⟩
    · simp only [listOf, List.length_map]; omega
    · intro k hk
      have hk' : k < rows.length := by simpa [listOf] using hk
      obtain ⟨o, x, m, eo, ex⟩ := wr k hk'
      obtain ⟨name', r', n', q1, q2, q3, q4⟩ := c5.holds.wrote w o x m
      rw [hw] at q1
      injection q1 with q1
      injection q1 with _ q1
      injection q1 with q1 qn
      subst q1 qn
      have z := z1 rows[k] (List.getElem_mem hk')
      rw [ev_agree (b1 _ (List.getElem_mem hk')) ag15] at z
      rw [hmem]
      simp only [listOf, List.getElem_map]
      have eo' : ev ρ5 o = ev ρ5 lo + (k : Int) := by rw [eo]; simp
      have : s0.reg r + (ev ρ5 lo).toNat + k = s0.reg r + (ev ρ5 o).toNat := by
        rw [eo']
        omega
      rw [this]
      have ex' : ev ρ5 x = ev ρ5 rows[k] := ex
      omega

/-- Every `ensures` of a list. -/
theorem symEnsures_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {env : List (String × SVal)} :
    ∀ {es : List Ensure} {s s' : Sym} {items rest : List Item} {ρ : Nat → Int} {st st' : State},
    fold (symEnsure ctx env) s es items = .ok (s', rest) → Holds ctx s0 ρ s st → WF s → EnvB s.nvars env →
    (∀ ρ', Agree s.nvars ρ ρ' → semEnv ctx s0 ρ' env = ctx.contract.envAfter s0 st') → st'.mem = st.mem →
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ ∀ e ∈ es, e.holds ctx.contract ctx.defs s0 st'
  | [], s, s', items, rest, ρ, st, st', h, H, wf, _, _, _ => by
    simp only [fold] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨ρ, Carried.here H wf, (fun _ m => nomatch m)⟩
  | e :: more, s, s', items, rest, ρ, st, st', h, H, wf, hb, henv, hmem => by
    simp only [fold] at h
    obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1, he⟩ := symEnsure_sound E e1 H wf hb henv hmem
    obtain ⟨ρ2, c2, hrest⟩ := symEnsures_sound E h c1.holds c1.wf (hb.mono c1.mono)
      (fun ρ' a => henv ρ' (Agree.trans c1.mono c1.agree a)) hmem
    refine ⟨ρ2, c1.then c2, ?_⟩
    intro e' m
    rcases List.mem_cons.mp m with rfl | m
    · exact he
    · exact hrest e' m

end Ode
