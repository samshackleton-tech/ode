import SoundCallW
/-!
# Why the verifier's yes is right, 7c: a call of a function that is given a table of addresses

The called function (a wide kernel) reads a table of addresses, each the address of so many blocks, and
writes one run; the table and the run are parts of this function's frame (`symCallL` of Core.lean). Here:
what its contract asks is so of the state it starts in; what it may touch, this function may touch; and of
every state the contract lets it return in, what the verifier holds after the call is so. A use of a
definition that the verifier has given a number of its own has a value, because the called function's
contract says the whole it is a part of has one; the unknown of that number stands for it (SoundCode.lean).
-/
namespace Ode
open Arithmetic

/-! ## What `nameval` lets through keeps its meaning when more unknowns and terms are made -/

mutual
theorem WVal.ok_mono {n n' t t' : Nat} (hn : n ≤ n') (ht : t ≤ t') : ∀ (v : WVal), v.ok n t = true → v.ok n' t' = true
  | .int _, _ => by simp [WVal.ok]
  | .bool _, _ => by simp [WVal.ok]
  | .num r, h => by simp only [WVal.ok, decide_eq_true_eq] at h ⊢; omega
  | .counter r, h => by simp only [WVal.ok, decide_eq_true_eq] at h ⊢; omega
  | .word xs, h => by
    simp only [WVal.ok, List.all_eq_true, decide_eq_true_eq] at h ⊢
    intro x hx
    have := h x hx
    omega
  | .list l, h => by
    simp only [WVal.ok] at h ⊢
    exact WVal.okAll_mono hn ht l h
  | .use u, h => by simp only [WVal.ok, decide_eq_true_eq] at h ⊢; omega
  | .run _ _, _ => by simp [WVal.ok]
  | .part _ _ _, _ => by simp [WVal.ok]
  | .pbyte _ _, _ => by simp [WVal.ok]
  | .other, _ => by simp [WVal.ok]
  | .region _ _, h => by simp [WVal.ok] at h
  | .span _ _ _, h => by simp [WVal.ok] at h
  | .wbytes xs, h => by
    simp only [WVal.ok, List.all_eq_true, decide_eq_true_eq] at h ⊢
    intro x hx
    have := h x hx
    omega
  | .record _, h => by simp [WVal.ok] at h
  | .lanes _ _ _, h => by simp [WVal.ok] at h
  | .lane _ _ _, h => by simp [WVal.ok] at h
theorem WVal.okAll_mono {n n' t t' : Nat} (hn : n ≤ n') (ht : t ≤ t') : ∀ (l : List WVal), WVal.okAll n t l = true → WVal.okAll n' t' l = true
  | [], _ => by simp [WVal.okAll]
  | v :: rest, h => by
    simp only [WVal.okAll, Bool.and_eq_true] at h ⊢
    exact ⟨WVal.ok_mono hn ht v h.1, WVal.okAll_mono hn ht rest h.2⟩
end

/-- A thing that speaks only of unknowns in use and of terms of the table stands for the same value under
other unknowns that agree on those in use, and in a table with more terms after it. -/
theorem WDen.mono {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {T T' : List Node} {n : Nat} (a : Agree n ρ ρ') (hw : WFT T)
    (ha : ∀ (j : Nat) (r : Row), T[j]? = some (Node.atom r) → bounded n r) (e : Ext T T') {v : WVal} {x : Val}
    (h : WDen ctx s0 ρ T v x) : v.ok n T.length = true → WDen ctx s0 ρ' T' v x := by
  induction h with
  | int k => intro _; exact WDen.int k
  | bool b => intro _; exact WDen.bool b
  | num r =>
    intro ok
    have hb : bounded n r := by show r.coeff.length ≤ n; simpa [WVal.ok] using ok
    rw [ev_agree hb a]; exact WDen.num r
  | word xs =>
    intro ok
    have hx : ∀ i ∈ xs, i < T.length := by simpa [WVal.ok] using ok
    have em : xs.map (den (inpOf ctx s0) ρ T) = xs.map (den (inpOf ctx s0) ρ' T') :=
      List.map_congr_left fun i hi => (den_mono hw ha a e (hx i hi)).symm
    rw [em]; exact WDen.word xs
  | counter r h0 =>
    intro ok
    have hb : bounded n r := by show r.coeff.length ≤ n; simpa [WVal.ok] using ok
    rw [ev_agree hb a] at h0 ⊢
    exact WDen.counter r h0
  | nil => intro _; exact WDen.nil
  | cons _ _ ih1 ih2 =>
    intro ok
    simp only [WVal.ok, WVal.okAll, Bool.and_eq_true] at ok
    exact WDen.cons (ih1 ok.1) (ih2 (by simp only [WVal.ok]; exact ok.2))
  | run r k hb => intro _; exact WDen.run r k hb
  | part r off k hb => intro _; exact WDen.part r off k hb
  | pbyte r off hb => intro _; exact WDen.pbyte r off hb
  | use u =>
    intro ok
    have hu : u < n := by simpa [WVal.ok] using ok
    rw [a u hu]; exact WDen.use u
  | other x => intro _; exact WDen.other x
  | region _ _ _ _ => intro ok; simp [WVal.ok] at ok
  | span _ _ _ _ _ => intro ok; simp [WVal.ok] at ok
  | wbytes xs =>
    intro ok
    have hx : ∀ i ∈ xs, i < T.length := by simpa [WVal.ok] using ok
    have em : xs.map (den (inpOf ctx s0) ρ T) = xs.map (den (inpOf ctx s0) ρ' T') :=
      List.map_congr_left fun i hi => (den_mono hw ha a e (hx i hi)).symm
    rw [em]; exact WDen.wbytes xs
  | rnil => intro ok; simp [WVal.ok] at ok
  | rcons _ _ _ _ => intro ok; simp [WVal.ok] at ok
  | lanes _ _ _ _ _ _ => intro ok; simp [WVal.ok] at ok
  | lane _ _ _ _ _ _ _ _ _ => intro ok; simp [WVal.ok] at ok

/-- A number held as a row that is a number of the table stands for that number. -/
theorem wnorm_den {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {T : List Node} {v : WVal} {x : Val}
    (h : WDen ctx s0 ρ T v x) : WDen ctx s0 ρ T (wnorm v) x := by
  cases v with
  | num r =>
    cases h
    cases hc : Lin.isConst r with
    | some k => simp only [wnorm, hc]; rw [ev_isConst hc]; exact WDen.int k
    | none => simp only [wnorm, hc]; exact WDen.num r
  | _ => exact h

/-- Every name's thing speaks only of unknowns in use and of terms of the table. -/
def EnvOk (n t : Nat) (env : List (String × WVal)) : Prop := ∀ p ∈ env, p.2.ok n t = true

theorem EnvOk.mono {n n' t t' : Nat} {env : List (String × WVal)} (hn : n ≤ n') (ht : t ≤ t') (h : EnvOk n t env) : EnvOk n' t' env :=
  fun p m => WVal.ok_mono hn ht _ (h p m)

theorem EnvOk.cons {n t : Nat} {env : List (String × WVal)} {x : String} {v : WVal} (hv : v.ok n t = true) (h : EnvOk n t env) :
    EnvOk n t ((x, v) :: env) := fun p m => by
  rcases List.mem_cons.mp m with rfl | m
  · exact hv
  · exact h p m

theorem EnvOk.zip {n t : Nat} : ∀ {ps : List String} {vs : List WVal}, WVal.okAll n t vs = true → EnvOk n t (ps.zip vs)
  | [], _, _ => fun p m => by simp at m
  | _ :: _, [], _ => fun p m => by simp at m
  | p0 :: ps, v :: vs, h => by
    simp only [WVal.okAll, Bool.and_eq_true] at h
    rw [List.zip_cons_cons]
    exact EnvOk.cons h.1 (EnvOk.zip h.2)

theorem EnvDen.mono {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {T T' : List Node} {n : Nat} (a : Agree n ρ ρ') (hw : WFT T)
    (ha : ∀ (j : Nat) (r : Row), T[j]? = some (Node.atom r) → bounded n r) (e : Ext T T') :
    ∀ {env : List (String × WVal)} {env' : List (String × Val)}, EnvDen ctx s0 ρ T env env' → EnvOk n T.length env →
      EnvDen ctx s0 ρ' T' env env'
  | [], [], _, _ => by simp [EnvDen]
  | [], _ :: _, h, _ => by simp [EnvDen] at h
  | _ :: _, [], h, _ => by simp [EnvDen] at h
  | (x, v) :: env, (y, b) :: env', h, ok =>
    ⟨h.1, WDen.mono a hw ha e h.2.1 (ok _ (List.mem_cons_self ..)),
      EnvDen.mono a hw ha e h.2.2 (fun p m => ok p (List.mem_cons_of_mem _ m))⟩

section
variable {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {s s' : Sym} {st : State}

/-- Along what `nameval` adds to the state (unknowns, facts, what is known; the table stays): a thing let
through keeps its meaning. -/
theorem Carried.wden (C : Carried ctx s0 ρ s ρ' s' st) (wf : WF ctx s) (ht : s'.tab = s.tab) {v : WVal} {x : Val}
    (d : WDen ctx s0 ρ s.terms v x) (ok : v.ok s.nvars s.terms.length = true) : WDen ctx s0 ρ' s'.terms v x := by
  have et : s'.terms = s.terms := by show s'.tab.list = s.tab.list; rw [ht]
  rw [et]
  exact WDen.mono C.agree wf.words.table wf.words.atoms (Ext.refl _) d ok

theorem Carried.envDen (C : Carried ctx s0 ρ s ρ' s' st) (wf : WF ctx s) (ht : s'.tab = s.tab) {env : List (String × WVal)}
    {env' : List (String × Val)} (hE : EnvDen ctx s0 ρ s.terms env env') (hO : EnvOk s.nvars s.terms.length env) :
    EnvDen ctx s0 ρ' s'.terms env env' := by
  have et : s'.terms = s.terms := by show s'.tab.list = s.tab.list; rw [ht]
  rw [et]
  exact EnvDen.mono C.agree wf.words.table wf.words.atoms (Ext.refl _) hE hO

theorem Carried.envOk (C : Carried ctx s0 ρ s ρ' s' st) (ht : s'.tab = s.tab) {env : List (String × WVal)}
    (hO : EnvOk s.nvars s.terms.length env) : EnvOk s'.nvars s'.terms.length env := by
  have et : s'.terms = s.terms := by show s'.tab.list = s.tab.list; rw [ht]
  rw [et]
  exact hO.mono C.mono (Nat.le_refl _)

theorem Carried.wok (C : Carried ctx s0 ρ s ρ' s' st) (ht : s'.tab = s.tab) {v : WVal}
    (ok : v.ok s.nvars s.terms.length = true) : v.ok s'.nvars s'.terms.length = true := by
  have et : s'.terms = s.terms := by show s'.tab.list = s.tab.list; rw [ht]
  rw [et]
  exact WVal.ok_mono C.mono (Nat.le_refl _) _ ok

end

/-- Two numbers' bits put together: the table of words stays as it was. -/
theorem symOrKnown_tab {s s' : Sym} {x y : Row} {v : EV} {items rest : Items}
    (h : symOrKnown s x y items = .ok ((v, s'), rest)) : s'.tab = s.tab := by
  unfold symOrKnown at h
  cases hk : knownOr x y s.known with
  | some v0 =>
    simp only [hk] at h
    have := V.pure_ok h
    injection this with hp _
    injection hp with _ h2
    subst h2; rfl
  | none =>
    simp only [hk] at h
    have := V.pure_ok h
    injection this with hp _
    injection hp with _ h2
    subst h2; rfl

/-! ## `nameval`: an expression of the called function's `ensures`, worked out on this function's terms

The called function's contract says the expression has a value. What `nameval` gives stands for that value,
under unknowns that agree with those before on the ones in use: a use that was given a number of its own has
the value, and the unknown of that number stands for it. -/

/-- What `nameval` is shown to give, from the state `s` under `ρ` to the state `s'`: the state it comes back
with holds of the same machine state under unknowns that agree with `ρ` on those in use; the table is as it
was; the thing speaks only of unknowns in use and terms of the table; and it stands for the value `v`. -/
abbrev Named (ctx : Ctx) (s0 st : State) (ρ : Nat → Int) (s s' : Sym) (wv : WVal) (v : Val) : Prop :=
  ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ s'.tab = s.tab ∧ wv.ok s'.nvars s'.terms.length = true ∧ WDen ctx s0 ρ' s'.terms wv v

/-- `nameval` with so much fuel is right: of an expression that has a value, under names that stand for
the values of the expression's names. -/
abbrev NamevalOk (ctx : Ctx) (s0 st : State) (fuel : Nat) : Prop :=
  ∀ (k : Nat) {ρ : Nat → Int} {s s' : Sym} {env : List (String × WVal)} {env' : List (String × Val)} {e : SExpr} {wv : WVal} {v : Val},
    Holds ctx s0 ρ s st → WF ctx s → ctx.contract.preVals ctx.defs s0 → EnvDen ctx s0 ρ s.terms env env' → EnvOk s.nvars s.terms.length env →
    nameval ctx fuel s env e = some (wv, s') → evalSpec ctx.defs k env' e = some v → Named ctx s0 st ρ s s' wv v

/-- What `weval` works out of an expression that has a value stands for that value. -/
theorem weval_value {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (hpv : ctx.contract.preVals ctx.defs s0)
    {env : List (String × WVal)} {env' : List (String × Val)} {e : SExpr} {w : WVal} {v : Val} {k : Nat}
    (hw : weval ctx s.tab.find s WFUEL env e = some w) (hE : EnvDen ctx s0 ρ s.terms env env')
    (hev : evalSpec ctx.defs k env' e = some v) : WDen ctx s0 ρ s.terms w v := by
  obtain ⟨B, hB⟩ := held_bound H hpv
  obtain ⟨a, ea, da⟩ := weval_sound H wf hpv hB WFUEL env env' e w hw hE
  have e1 := evalSpec_mono ctx.defs _ ea (max (WFUEL + B) k) (Nat.le_max_left _ _)
  have e2 := evalSpec_mono ctx.defs _ hev (max (WFUEL + B) k) (Nat.le_max_right _ _)
  rw [e1] at e2
  injection e2 with e2
  rw [← e2]; exact da

theorem okAll_words {n t : Nat} : ∀ (ids : List Nat), ids.all (· < t) = true → WVal.okAll n t (ids.map fun i => WVal.word [i]) = true
  | [], _ => by simp [WVal.okAll]
  | i :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_cons, WVal.okAll, WVal.ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.1, okAll_words rest h.2⟩

/-- The things a use is given, worked out one after another by `nameval`. -/
theorem namevalList_sound {ctx : Ctx} {s0 st : State} {fuel : Nat} (ih : NamevalOk ctx s0 st fuel) (k : Nat)
    {env : List (String × WVal)} {env' : List (String × Val)} :
    ∀ (args : SExpr) {ρ : Nat → Int} {s s' : Sym} {vs : List WVal} {as : List Val},
      Holds ctx s0 ρ s st → WF ctx s → ctx.contract.preVals ctx.defs s0 → EnvDen ctx s0 ρ s.terms env env' → EnvOk s.nvars s.terms.length env →
      namevalList (fun s e => nameval ctx fuel s env e) s args = some (vs, s') →
      evalList (evalSpec ctx.defs k env') args = some as →
      ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ s'.tab = s.tab ∧ WVal.okAll s'.nvars s'.terms.length vs = true ∧
        WDen ctx s0 ρ' s'.terms (.list vs) (.list as) := by
  intro args
  induction args with
  | nil =>
    intro ρ s s' vs as H wf _ hE hO h hev
    simp only [namevalList, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [evalList, Option.some.injEq] at hev
    subst hev
    exact ⟨ρ, Carried.here H wf, rfl, by simp [WVal.okAll], WDen.nil⟩
  | cons a rest _ ih2 =>
    intro ρ s s' vs as H wf hpv hE hO h hev
    simp only [namevalList] at h
    cases ha : nameval ctx fuel s env a with
    | none => simp [ha] at h
    | some p1 =>
      obtain ⟨x, s1⟩ := p1
      simp only [ha] at h
      cases hr : namevalList (fun s e => nameval ctx fuel s env e) s1 rest with
      | none => simp [hr] at h
      | some p2 =>
        obtain ⟨xs, s2⟩ := p2
        simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [evalList] at hev
        cases eva : evalSpec ctx.defs k env' a with
        | none => simp [eva] at hev
        | some va =>
          cases evr : evalList (evalSpec ctx.defs k env') rest with
          | none => simp [eva, evr] at hev
          | some vr =>
            simp only [eva, evr, Option.some.injEq] at hev
            subst hev
            obtain ⟨ρ1, C1, t1, ok1, d1⟩ := ih k H wf hpv hE hO ha eva
            obtain ⟨ρ2, C2, t2, ok2, d2⟩ := ih2 C1.holds C1.wf hpv (C1.envDen wf t1 hE hO) (C1.envOk t1 hO) hr evr
            refine ⟨ρ2, C1.then C2, t2.trans t1, ?_, WDen.cons (C2.wden C1.wf t2 d1 ok1) d2⟩
            simp only [WVal.okAll, Bool.and_eq_true]
            exact ⟨C2.wok t2 ok1, ok2⟩
  | _ => intro ρ s s' vs as H wf _ hE hO h hev; simp [namevalList] at h

theorem nameval_sound {ctx : Ctx} {s0 st : State} (fuel : Nat) : NamevalOk ctx s0 st fuel := by
  induction fuel with
  | zero => intro k ρ s s' env env' e wv v _ _ _ _ _ h _; simp [nameval] at h
  | succ fuel ih =>
    intro k ρ s s' env env' e wv v H wf hpv hE hO h hev
    simp only [nameval] at h
    cases hw : weval ctx s.tab.find s WFUEL env e with
    | some w =>
      -- what `weval` works out as it is
      simp only [hw] at h
      split at h
      next hok =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨ρ, Carried.here H wf, rfl, by rwa [Tab.size_eq_length] at hok, wnorm_den (weval_value H wf hpv hw hE hev)⟩
      next => cases h
    | none =>
      simp only [hw] at h
      cases e with
      | bin op a b =>
        simp only at h
        cases k with
        | zero => simp [evalSpec] at hev
        | succ k =>
          simp only [evalSpec] at hev
          cases ha : nameval ctx fuel s env a with
          | none => simp [ha] at h
          | some p1 =>
            obtain ⟨x, s1⟩ := p1
            simp only [ha] at h
            cases hb : nameval ctx fuel s1 env b with
            | none => simp [hb] at h
            | some p2 =>
              obtain ⟨y, s2⟩ := p2
              simp only [hb] at h
              cases eva : evalSpec ctx.defs k env' a with
              | none => simp [eva] at hev
              | some va =>
                cases evb : evalSpec ctx.defs k env' b with
                | none => simp [eva, evb] at hev
                | some vb =>
                  simp only [eva, evb] at hev
                  obtain ⟨ρ1, C1, t1, ok1, d1⟩ := ih k H wf hpv hE hO ha eva
                  obtain ⟨ρ2, C2, t2, ok2, d2⟩ := ih k C1.holds C1.wf hpv (C1.envDen wf t1 hE hO) (C1.envOk t1 hO) hb evb
                  have d1' : WDen ctx s0 ρ2 s2.terms x va := C2.wden C1.wf t2 d1 ok1
                  unfold namebin at h
                  cases hwb : wbin s2.tab.find s2 op x y with
                  | some w =>
                    simp only [hwb] at h
                    split at h
                    next hokw =>
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      obtain ⟨r, er, dr⟩ := wbin_sound C2.holds C2.wf hwb d1' d2
                      rw [hev] at er
                      injection er with er
                      subst er
                      exact ⟨ρ2, C1.then C2, t2.trans t1, hokw, dr⟩
                    next => cases h
                  | none =>
                    -- the bits of a row and of a number of the text, put together: a new unknown where the state has none
                    simp only [hwb] at h
                    split at h
                    next ar bn =>
                      split at h
                      next hcond =>
                        obtain ⟨hop, hb0⟩ := hcond
                        have eop : op = "|" := by simpa using hop
                        subst eop
                        unfold nameOr at h
                        split at h
                        next hchk =>
                          simp only [Bool.and_eq_true] at hchk
                          obtain ⟨⟨⟨ka, pa⟩, kb⟩, pb⟩ := hchk
                          cases hso : symOrKnown s2 ar (Lin.const bn) (Items.ofList []) with
                          | error _ => simp [hso] at h
                          | ok res =>
                            obtain ⟨⟨u, s3⟩, rest⟩ := res
                            simp only [hso] at h
                            cases u with
                            | lin r =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at h
                              obtain ⟨rfl, rfl⟩ := h
                              cases d1'
                              cases d2
                              have a0 := knownNonneg_sound C2.holds ka
                              have a1 := plain_sound pa ρ2 C2.holds.facts
                              have b1 := plain_sound pb ρ2 C2.holds.facts
                              simp only [ev_sub, ev_const] at a1 b1
                              have bx : bounded s2.nvars ar := by
                                have : (WVal.num ar).ok s2.nvars s2.terms.length = true := C2.wok t2 ok1
                                show ar.coeff.length ≤ s2.nvars
                                simpa [WVal.ok] using this
                              have hx : EV.sem ρ2 s2.nvars (ev ρ2 ar).toNat (.lin ar) :=
                                ⟨by unfold top at a1; unfold M64; omega, by omega, bx⟩
                              have hy : EV.sem ρ2 s2.nvars bn.toNat (.lin (Lin.const bn)) :=
                                ⟨by unfold top at b1; unfold M64; omega, by rw [ev_const]; omega, by show (Lin.const bn).coeff.length ≤ s2.nvars; simp [Lin.const]⟩
                              obtain ⟨ρ3, C3, _, sx⟩ := symOrKnown_sound hso C2.holds C2.wf _ _ hx hy
                              have t3 := symOrKnown_tab hso
                              have hv : v = .int (((ev ρ2 ar).toNat ||| bn.toNat : Nat) : Int) := by
                                simp only [binop] at hev
                                simp only [String.reduceBEq, Bool.false_eq_true, if_false, if_true] at hev
                                rw [if_pos ⟨a0, hb0⟩] at hev
                                injection hev with hev
                                exact hev.symm
                              refine ⟨ρ3, C1.then (C2.then C3), t3.trans (t2.trans t1), ?_, ?_⟩
                              · have := sx.2.2
                                show decide (r.coeff.length ≤ s3.nvars) = true
                                exact decide_eq_true this
                              · rw [hv, sx.2.1]; exact WDen.num r
                            | equal _ _ => simp at h
                            | below _ _ => simp at h
                        next => cases h
                      next => cases h
                    next => cases h
      | ifx c a b =>
        simp only at h
        cases k with
        | zero => simp [evalSpec] at hev
        | succ k =>
          simp only [evalSpec] at hev
          cases hc : weval ctx s.tab.find s WFUEL env c with
          | none => simp [hc] at h
          | some wc =>
            cases evc : evalSpec ctx.defs k env' c with
            | none => simp [evc] at hev
            | some vc =>
              have dc := weval_value H wf hpv hc hE evc
              simp only [hc] at h
              simp only [evc] at hev
              split at h
              next heq =>
                injection heq with heq; subst heq
                cases dc
                simp only at hev
                exact ih k H wf hpv hE hO h hev
              next heq =>
                injection heq with heq; subst heq
                cases dc
                simp only at hev
                exact ih k H wf hpv hE hO h hev
              next => cases h
      | letx x a rest =>
        simp only at h
        cases k with
        | zero => simp [evalSpec] at hev
        | succ k =>
          simp only [evalSpec] at hev
          cases ha : nameval ctx fuel s env a with
          | none => simp [ha] at h
          | some p1 =>
            obtain ⟨xv, s1⟩ := p1
            simp only [ha] at h
            cases eva : evalSpec ctx.defs k env' a with
            | none => simp [eva] at hev
            | some va =>
              simp only [eva] at hev
              obtain ⟨ρ1, C1, t1, ok1, d1⟩ := ih k H wf hpv hE hO ha eva
              have hE1 : EnvDen ctx s0 ρ1 s1.terms ((x, xv) :: env) ((x, va) :: env') :=
                ⟨rfl, d1, C1.envDen wf t1 hE hO⟩
              obtain ⟨ρ2, C2, t2, ok2, d2⟩ := ih k C1.holds C1.wf hpv hE1 (EnvOk.cons ok1 (C1.envOk t1 hO)) h hev
              exact ⟨ρ2, C1.then C2, t2.trans t1, ok2, d2⟩
      | call f args =>
        simp only at h
        split at h
        · cases h
        next hnot =>
          have hn1 : ¬ (f == "len") = true := fun e => hnot (by simp [e])
          have hn2 : ¬ own.contains f = true := fun e => hnot (by rw [e, Bool.or_true])
          cases k with
          | zero => simp [evalSpec] at hev
          | succ k =>
            simp only [evalSpec] at hev
            cases hl : namevalList (fun s e => nameval ctx fuel s env e) s args with
            | none => simp [hl] at h
            | some p1 =>
              obtain ⟨vs, s1⟩ := p1
              cases hd : findDef ctx.defs f with
              | none => simp [hl, hd] at h
              | some d =>
                simp only [hl, hd] at h
                cases evl : evalList (evalSpec ctx.defs k env') args with
                | none => simp [evl] at hev
                | some as =>
                  simp only [evl] at hev
                  rw [if_neg hn1, if_neg hn2] at hev
                  simp only [hd] at hev
                  obtain ⟨ρ1, C1, t1, okvs, dvs⟩ := namevalList_sound ih k args H wf hpv hE hO hl evl
                  split at h
                  · cases h
                  next hplen =>
                    have hpl : d.params.length = vs.length := by simpa using hplen
                    have hp : (d.params.length == as.length) = true := by rw [← WDen.length dvs]; simpa using hpl
                    rw [if_pos hp] at hev
                    have hEz : EnvDen ctx s0 ρ1 s1.terms (d.params.zip vs) (d.params.zip as) := EnvDen.zip dvs
                    have hOz : EnvOk s1.nvars s1.terms.length (d.params.zip vs) := EnvOk.zip okvs
                    cases hfk : flatKeys s1.tab.find vs with
                    | none =>
                      -- no keys: the definition is opened
                      simp only [hfk] at h
                      obtain ⟨ρ2, C2, t2, ok2, d2⟩ := ih k C1.holds C1.wf hpv hEz hOz h hev
                      exact ⟨ρ2, C1.then C2, t2.trans t1, ok2, d2⟩
                    | some keys =>
                      simp only [hfk] at h
                      have eas : as = keys.map (Key.val ctx s0 ρ1 s1.terms) := flatKeys_den C1.wf dvs hfk
                      obtain ⟨B, hB⟩ := held_bound C1.holds hpv
                      cases hh : heldIds s1.facts f keys s1.known with
                      | some ids =>
                        -- a use the state holds the words of
                        simp only [hh] at h
                        split at h
                        next hids =>
                          simp only [Option.some.injEq, Prod.mk.injEq] at h
                          obtain ⟨rfl, rfl⟩ := h
                          obtain ⟨keys', hm, same⟩ := heldIds_mem hh
                          obtain ⟨d', hd', hlen', hev'⟩ := hB _ hm
                          rw [hd] at hd'
                          injection hd' with hd'
                          subst hd'
                          have ekeys : keys'.map (Key.val ctx s0 ρ1 s1.terms) = keys.map (Key.val ctx s0 ρ1 s1.terms) :=
                            sameKeys_sound C1.holds.facts same
                          rw [ekeys, ← eas] at hev'
                          have e1 := evalSpec_mono ctx.defs _ hev' (max B k) (Nat.le_max_left _ _)
                          have e2 := evalSpec_mono ctx.defs _ hev (max B k) (Nat.le_max_right _ _)
                          rw [e1] at e2
                          injection e2 with e2
                          refine ⟨ρ1, C1, t1, ?_, ?_⟩
                          · simp only [WVal.ok]; rw [Tab.size_eq_length] at hids; exact okAll_words ids hids
                          · rw [← e2]; exact WDen.wordsOf C1.wf ids
                        next => cases h
                      | none =>
                        simp only [hh] at h
                        cases hu : usedAs s1.facts f keys s1.known with
                        | some u =>
                          -- a use the state has given a number
                          simp only [hu] at h
                          split at h
                          next hlt =>
                            simp only [Option.some.injEq, Prod.mk.injEq] at h
                            obtain ⟨rfl, rfl⟩ := h
                            obtain ⟨keys', hm, same⟩ := usedAs_mem hu
                            obtain ⟨d', hd', hlen', hev'⟩ := hB _ hm
                            rw [hd] at hd'
                            injection hd' with hd'
                            subst hd'
                            have ekeys : keys'.map (Key.val ctx s0 ρ1 s1.terms) = keys.map (Key.val ctx s0 ρ1 s1.terms) :=
                              sameKeys_sound C1.holds.facts same
                            rw [ekeys, ← eas] at hev'
                            have e1 := evalSpec_mono ctx.defs _ hev' (max B k) (Nat.le_max_left _ _)
                            have e2 := evalSpec_mono ctx.defs _ hev (max B k) (Nat.le_max_right _ _)
                            rw [e1] at e2
                            injection e2 with e2
                            refine ⟨ρ1, C1, t1, ?_, ?_⟩
                            · simp only [WVal.ok]; exact decide_eq_true hlt
                            · rw [← e2]; exact WDen.use u
                          next => cases h
                        | none =>
                          simp only [hu] at h
                          have useBranch :
                              (if keys.all (Key.ok s1.nvars s1.tab.size) = true then
                                some (WVal.use s1.nvars, { s1 with nvars := s1.nvars + 1, known := Known.use f keys s1.nvars :: s1.known })
                               else none) = some (wv, s') → Named ctx s0 st ρ s s' wv v := by
                            intro h'
                            split at h'
                            next hkeys =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at h'
                              obtain ⟨rfl, rfl⟩ := h'
                              rw [Tab.size_eq_length] at hkeys
                              have wk : ∀ key ∈ keys, key.wf s1.nvars s1.terms.length :=
                                fun key m => Key.ok_wf (List.all_eq_true.mp hkeys key m)
                              have hlenk : d.params.length = keys.length := by
                                have h1 : as.length = keys.length := by rw [eas, List.length_map]
                                have h2 := WDen.length dvs
                                omega
                              have ag := extend_agree ρ1 s1.nvars (Val.code v : Int)
                              have ekv : keys.map (Key.val ctx s0 (extend ρ1 s1.nvars (Val.code v : Int)) s1.terms) =
                                  keys.map (Key.val ctx s0 ρ1 s1.terms) :=
                                List.map_congr_left fun key m => Key.val_mono (wk key m) ag C1.wf.words.table C1.wf.words.atoms (Ext.refl _)
                              have C2 := Carried.fresh C1.holds C1.wf (Val.code v : Int) [] (.use f keys s1.nvars)
                                (fun f' m => nomatch m)
                                ⟨fun key m => Key.wf_mono (Nat.le_succ _) (Nat.le_refl _) (wk key m), Nat.lt_succ_self _⟩
                                (fun f' m => nomatch m)
                                (fun _ => ⟨d, hd, hlenk, k, by
                                  rw [ekv, ← eas, extend_new]
                                  simp only [Int.toNat_natCast, Val.decode_code]
                                  exact hev⟩)
                              refine ⟨_, C1.then C2, t1, ?_, ?_⟩
                              · simp [WVal.ok]
                              · have key := WDen.use (ctx := ctx) (s0 := s0) (ρ := extend ρ1 s1.nvars (Val.code v : Int)) (T := s1.terms) s1.nvars
                                rw [extend_new] at key
                                simp only [Int.toNat_natCast, Val.decode_code] at key
                                exact key
                            next => cases h'
                          cases hcan : canName d.body with
                          | false =>
                            simp only [hcan, Bool.false_eq_true, ↓reduceIte] at h
                            exact useBranch h
                          | true =>
                            simp only [hcan, ↓reduceIte] at h
                            cases ho : nameval ctx fuel s1 (d.params.zip vs) d.body with
                            | some r =>
                              obtain ⟨wr, sr⟩ := r
                              simp only [ho, Option.some.injEq, Prod.mk.injEq] at h
                              obtain ⟨rfl, rfl⟩ := h
                              obtain ⟨ρ2, C2, t2, ok2, d2⟩ := ih k C1.holds C1.wf hpv hEz hOz ho hev
                              exact ⟨ρ2, C1.then C2, t2.trans t1, ok2, d2⟩
                            | none =>
                              simp only [ho] at h
                              exact useBranch h
      | _ => simp at h

private theorem namevalList_carried_vacuous {ctx : Ctx} {s0 st : State} {fuel : Nat}
    (ih : ∀ {ρ : Nat → Int} {s s' : Sym} {env : List (String × WVal)} {e : SExpr} {wv : WVal},
      Holds ctx s0 ρ s st → WF ctx s → EnvOk s.nvars s.terms.length env →
      nameval ctx fuel s env e = some (wv, s') →
      ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ s'.tab = s.tab ∧ wv.ok s'.nvars s'.terms.length = true)
    {env : List (String × WVal)} :
    ∀ (args : SExpr) {ρ : Nat → Int} {s s' : Sym} {vs : List WVal},
      Holds ctx s0 ρ s st → WF ctx s → EnvOk s.nvars s.terms.length env →
      namevalList (fun s e => nameval ctx fuel s env e) s args = some (vs, s') →
      ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ s'.tab = s.tab ∧ WVal.okAll s'.nvars s'.terms.length vs = true := by
  intro args
  induction args with
  | nil =>
    intro ρ s s' vs H wf _ h
    simp only [namevalList, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨ρ, Carried.here H wf, rfl, by simp [WVal.okAll]⟩
  | cons a rest _ ih2 =>
    intro ρ s s' vs H wf hO h
    simp only [namevalList] at h
    cases ha : nameval ctx fuel s env a with
    | none => simp [ha] at h
    | some p1 =>
      obtain ⟨x, s1⟩ := p1; simp only [ha] at h
      cases hr : namevalList (fun s e => nameval ctx fuel s env e) s1 rest with
      | none => simp [hr] at h
      | some p2 =>
        obtain ⟨xs, s2⟩ := p2; simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ρ1, C1, t1, ok1⟩ := ih H wf hO ha
        obtain ⟨ρ2, C2, t2, ok2⟩ := ih2 C1.holds C1.wf (C1.envOk t1 hO) hr
        exact ⟨ρ2, C1.then C2, t2.trans t1, by simp only [WVal.okAll, Bool.and_eq_true]; exact ⟨C2.wok t2 ok1, ok2⟩⟩
  | _ => intro _ _ _ _ _ _ _ h; simp [namevalList] at h

/-- When `ctx.contract.preVals ctx.defs s0` is false, every `Known.use` added by `nameval` holds vacuously,
so `nameval` still carries `Holds` and `WF` without needing value-array assumptions. -/
private theorem nameval_carried_vacuous {ctx : Ctx} {s0 st : State} (nhpv : ¬ ctx.contract.preVals ctx.defs s0) :
    ∀ (fuel : Nat) {ρ : Nat → Int} {s s' : Sym} {env : List (String × WVal)} {e : SExpr} {wv : WVal},
      Holds ctx s0 ρ s st → WF ctx s → EnvOk s.nvars s.terms.length env →
      nameval ctx fuel s env e = some (wv, s') →
      ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ s'.tab = s.tab ∧ wv.ok s'.nvars s'.terms.length = true
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [nameval] at h
  | fuel + 1, ρ, s, s', env, e, wv, H, wf, hO, h => by
    simp only [nameval] at h
    cases hw : weval ctx s.tab.find s WFUEL env e with
    | some w =>
      simp only [hw] at h; split at h
      next hok =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨ρ, Carried.here H wf, rfl, by rwa [Tab.size_eq_length] at hok⟩
      next => cases h
    | none =>
      simp only [hw] at h
      cases e with
      | bin op a b =>
        simp only at h
        cases ha : nameval ctx fuel s env a with
        | none => simp [ha] at h
        | some p1 =>
          obtain ⟨x, s1⟩ := p1; simp only [ha] at h
          cases hb : nameval ctx fuel s1 env b with
          | none => simp [hb] at h
          | some p2 =>
            obtain ⟨y, s2⟩ := p2; simp only [hb] at h
            obtain ⟨ρ1, C1, t1, ok1⟩ := nameval_carried_vacuous nhpv fuel H wf hO ha
            obtain ⟨ρ2, C2, t2, ok2⟩ := nameval_carried_vacuous nhpv fuel C1.holds C1.wf (C1.envOk t1 hO) hb
            unfold namebin at h
            cases hwb : wbin s2.tab.find s2 op x y with
            | some w =>
              simp only [hwb] at h; split at h
              next hokw =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                exact ⟨ρ2, C1.then C2, t2.trans t1, by rwa [Tab.size_eq_length] at hokw⟩
              next => cases h
            | none =>
              simp only [hwb] at h
              split at h
              next ar bn =>
                split at h
                next hcond =>
                  unfold nameOr at h; split at h
                  next hchk =>
                    simp only [Bool.and_eq_true] at hchk
                    obtain ⟨⟨⟨ka, pa⟩, _⟩, pb⟩ := hchk
                    cases hso : symOrKnown s2 ar (Lin.const bn) (Items.ofList []) with
                    | error _ => simp [hso] at h
                    | ok res =>
                      obtain ⟨⟨u, s3⟩, rest⟩ := res; simp only [hso] at h
                      cases u with
                      | lin r =>
                        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                        have a0 := knownNonneg_sound C2.holds ka
                        have a1 := plain_sound pa ρ2 C2.holds.facts
                        have b1 := plain_sound pb ρ2 C2.holds.facts
                        simp only [ev_sub, ev_const] at a1 b1
                        have bx : bounded s2.nvars ar := by
                          have : (WVal.num ar).ok s2.nvars s2.terms.length = true := C2.wok t2 ok1
                          show ar.coeff.length ≤ s2.nvars; simpa [WVal.ok] using this
                        have hx : EV.sem ρ2 s2.nvars (ev ρ2 ar).toNat (.lin ar) :=
                          ⟨by unfold top at a1; unfold M64; omega, by omega, bx⟩
                        have hy : EV.sem ρ2 s2.nvars bn.toNat (.lin (Lin.const bn)) :=
                          ⟨by unfold top at b1; unfold M64; omega, by rw [ev_const]; omega, by show (Lin.const bn).coeff.length ≤ s2.nvars; simp [Lin.const]⟩
                        obtain ⟨ρ3, C3, _, sx⟩ := symOrKnown_sound hso C2.holds C2.wf _ _ hx hy
                        exact ⟨ρ3, (C1.then C2).then C3, (symOrKnown_tab hso).trans (t2.trans t1), by simp only [WVal.ok, decide_eq_true_eq]; exact sx.2.2⟩
                      | _ => simp at h
                  next => cases h
                next => cases h
              next => cases h
      | ifx c a b =>
        simp only at h
        cases hc : weval ctx s.tab.find s WFUEL env c with
        | none => simp [hc] at h
        | some wc =>
          simp only [hc] at h
          cases wc with
          | bool b0 =>
            cases b0 with
            | true => exact nameval_carried_vacuous nhpv fuel H wf hO h
            | false => exact nameval_carried_vacuous nhpv fuel H wf hO h
          | _ => simp at h
      | letx x a rest =>
        simp only at h
        cases ha : nameval ctx fuel s env a with
        | none => simp [ha] at h
        | some p1 =>
          obtain ⟨xv, s1⟩ := p1; simp only [ha] at h
          obtain ⟨ρ1, C1, t1, ok1⟩ := nameval_carried_vacuous nhpv fuel H wf hO ha
          obtain ⟨ρ2, C2, t2, ok2⟩ := nameval_carried_vacuous nhpv fuel C1.holds C1.wf (EnvOk.cons ok1 (C1.envOk t1 hO)) h
          exact ⟨ρ2, C1.then C2, t2.trans t1, ok2⟩
      | call f args =>
        simp only at h
        split at h
        · cases h
        next =>
          cases hl : namevalList (fun s e => nameval ctx fuel s env e) s args with
          | none => simp [hl] at h
          | some p1 =>
            obtain ⟨vs, s1⟩ := p1
            cases hd : findDef ctx.defs f with
            | none => simp [hl, hd] at h
            | some d =>
              simp only [hl, hd] at h
              obtain ⟨ρ1, C1, t1, okvs⟩ := namevalList_carried_vacuous (nameval_carried_vacuous nhpv fuel) args H wf hO hl
              split at h
              · cases h
              next =>
                have hOz : EnvOk s1.nvars s1.terms.length (d.params.zip vs) := EnvOk.zip okvs
                cases hfk : flatKeys s1.tab.find vs with
                | none =>
                  simp only [hfk] at h
                  obtain ⟨ρ2, C2, t2, ok2⟩ := nameval_carried_vacuous nhpv fuel C1.holds C1.wf hOz h
                  exact ⟨ρ2, C1.then C2, t2.trans t1, ok2⟩
                | some keys =>
                  simp only [hfk] at h
                  cases hh : heldIds s1.facts f keys s1.known with
                  | some ids =>
                    simp only [hh] at h; split at h
                    next hids =>
                      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                      rw [Tab.size_eq_length] at hids
                      exact ⟨ρ1, C1, t1, okAll_words ids hids⟩
                    next => cases h
                  | none =>
                    simp only [hh] at h
                    cases hu : usedAs s1.facts f keys s1.known with
                    | some u =>
                      simp only [hu] at h; split at h
                      next hlt =>
                        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                        exact ⟨ρ1, C1, t1, by simp [WVal.ok, hlt]⟩
                      next => cases h
                    | none =>
                      simp only [hu] at h
                      have useBranch :
                          (if keys.all (Key.ok s1.nvars s1.tab.size) = true then
                            some (WVal.use s1.nvars, { s1 with nvars := s1.nvars + 1, known := Known.use f keys s1.nvars :: s1.known })
                           else none) = some (wv, s') →
                          ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ s'.tab = s.tab ∧ wv.ok s'.nvars s'.terms.length = true := by
                        intro h'; split at h'
                        next hkeys =>
                          simp only [Option.some.injEq, Prod.mk.injEq] at h'; obtain ⟨rfl, rfl⟩ := h'
                          rw [Tab.size_eq_length] at hkeys
                          have wk : ∀ key ∈ keys, key.wf s1.nvars s1.terms.length :=
                            fun key m => Key.ok_wf (List.all_eq_true.mp hkeys key m)
                          have C2 := Carried.fresh C1.holds C1.wf 0 [] (.use f keys s1.nvars)
                            (fun _ m => nomatch m)
                            ⟨fun key m => Key.wf_mono (Nat.le_succ _) (Nat.le_refl _) (wk key m), Nat.lt_succ_self _⟩
                            (fun _ m => nomatch m) (fun hpv => (nhpv hpv).elim)
                          exact ⟨_, C1.then C2, t1, by simp [WVal.ok]⟩
                        next => cases h'
                      cases hcan : canName d.body with
                      | false => simp only [hcan, Bool.false_eq_true, ↓reduceIte] at h; exact useBranch h
                      | true =>
                        simp only [hcan, ↓reduceIte] at h
                        cases ho : nameval ctx fuel s1 (d.params.zip vs) d.body with
                        | some r =>
                          obtain ⟨wr, sr⟩ := r; simp only [ho, Option.some.injEq, Prod.mk.injEq] at h
                          obtain ⟨rfl, rfl⟩ := h
                          obtain ⟨ρ2, C2, t2, ok2⟩ := nameval_carried_vacuous nhpv fuel C1.holds C1.wf hOz ho
                          exact ⟨ρ2, C1.then C2, t2.trans t1, ok2⟩
                        | none => simp only [ho] at h; exact useBranch h
      | _ => simp at h

/-! ## The lanes of the table -/

/-- Where a lane's blocks lie (`P`: their address): in a run of a fixed count this function was given to
read, in a variable-length region this function was given to read, or in its frame at or above the stack
pointer, apart from the part the called function writes. -/
def LaneAt (ctx : Ctx) (s0 : State) (s : Sym) (P nb : Nat) (cw : Int) (nout : Nat) : Prop :=
  (∃ x0 b n0 c, (x0, b, n0) ∈ ctx.contract.fixeds ∧ P = s0.reg b + c ∧ c + 64 * nb ≤ n0) ∨
  (∃ b len c, (b, len) ∈ ctx.contract.regions ∧ P = s0.reg b + c ∧ c + 64 * nb ≤ s0.reg len) ∨
  (∃ o sp, s.sp = some sp ∧ (P : Int) = s0.reg RSP + o ∧ sp ≤ o ∧ o + 64 * (nb : Int) ≤ 0 ∧
     (o + 64 * (nb : Int) ≤ cw ∨ cw + (nout : Int) ≤ o))

/-- The words of a lane's blocks, as `laneWords` puts them into the table (`P`: the address the lane's cell
holds): the table is only added to; there is a term for each word, and it is the word memory holds there
now; and the blocks are a part of a run this function was given to read, or a part of its frame at or above
the stack pointer that lies apart from the part the called function writes. -/
theorem laneWords_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) {a : Row} {nb : Nat} {cw : Int} {nout : Nat} {ids : List Nat} {T : Tab} {P : Nat}
    (hP : (P : Int) = ev ρ a) (h : laneWords ctx s a nb cw nout = some (ids, T)) :
    Ext s.terms T.list ∧ TableOk s.nvars T.list ∧ ids.length = 16 * nb ∧ (∀ i ∈ ids, i < T.list.length) ∧
    (∀ k, k < 16 * nb → den (inpOf ctx s0) ρ T.list (ids.getD k 0) = load st.mem (P + 4 * k) 4) ∧
    LaneAt ctx s0 s P nb cw nout := by
  unfold laneWords at h
  have frameCase : ∀ {o sp : Int}, Lin.isConst (Lin.sub a (Lin.var RSP)) = some o → s.sp = some sp →
      (sp ≤ o ∧ o + 64 * (nb : Int) ≤ 0 ∧ (o + 64 * (nb : Int) ≤ cw ∨ cw + (nout : Int) ≤ o)) →
      ∀ {rows : List Row}, frameRows s o (16 * nb) 0 = some rows → termsOf wAtom rows s.tab = (ids, T) →
      Ext s.terms T.list ∧ TableOk s.nvars T.list ∧ ids.length = 16 * nb ∧ (∀ i ∈ ids, i < T.list.length) ∧
      (∀ k, k < 16 * nb → den (inpOf ctx s0) ρ T.list (ids.getD k 0) = load st.mem (P + 4 * k) 4) ∧
      LaneAt ctx s0 s P nb cw nout := by
    intro o sp ho hsp hcond rows hrows hT
    have eo := ev_isConst (ρ := ρ) ho
    rw [ev_sub, ev_var, H.entry RSP ctx.rsp_lt] at eo
    obtain ⟨rlen, rw4⟩ := frameRows_sound H E.stackAt o (16 * nb) 0 hrows
    have rb := frameRows_bounded wf o (16 * nb) 0 hrows
    obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := wAtom) (val := fun r => (ev ρ r % W32i).toNat)
      (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms) rows s.tab
      (fun r mr T' _ okT => wAtom_step okT (rb r mr)) (Ext.refl _) wf.words.ok
    rw [hT] at e ok len lt dn
    refine ⟨e, ok, by rw [len, rlen], lt, fun k hk => ?_, Or.inr (Or.inr ⟨o, sp, hsp, by omega, hcond⟩)⟩
    have hk' : k < rows.length := by omega
    rw [dn k hk']
    obtain ⟨_, _, hl⟩ := rw4 k hk
    have eg : rows.getD k (Lin.const 0) = rows[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; rfl
    rw [eg] at hl
    have ea : ((s0.reg RSP : Int) + (o + 4 * ((0 + k : Nat) : Int))).toNat = P + 4 * k := by omega
    rw [ea] at hl
    omega
  cases hf : findOut a ctx.contract.fixeds 0 with
  | some wh =>
    obtain ⟨j', o, name, base, n0, rfl, _, hl, ho⟩ := findOut_spec hf
    simp only [Nat.sub_zero] at hl
    simp only [hf] at h
    cases hc : Lin.isConst o with
    | none => simp [hc] at h
    | some c =>
      simp only [hc, hl] at h
      split at h
      next hcond =>
        obtain ⟨c0, c4, cn⟩ := hcond
        simp only [Option.some.injEq] at h
        have hm0 := List.mem_of_getElem? hl
        obtain ⟨f1, f2, f3, f4⟩ := E.fixedAt hm0
        have ec := ev_isConst (ρ := ρ) hc
        rw [ho, ev_sub, ev_var, H.entry base (fixeds_lt hm0)] at ec
        have hPc : P = s0.reg base + c.toNat := by omega
        obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := intern)
          (val := fun nd => match nd with | .input j k => inpOf ctx s0 j k | _ => 0)
          (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms)
          ((List.range (16 * nb)).map fun k => Node.input j' (c.toNat / 4 + k)) s.tab
          (fun nd ma T' _ okT => by
            obtain ⟨k, _, rfl⟩ := List.mem_map.mp ma
            exact input_step okT) (Ext.refl _) wf.words.ok
        rw [h] at e ok len lt dn
        refine ⟨e, ok, by rw [len]; simp, lt, fun k hk => ?_, Or.inl ⟨name, base, n0, c.toNat, hm0, hPc, by omega⟩⟩
        have hk' : k < ((List.range (16 * nb)).map fun k => Node.input j' (c.toNat / 4 + k)).length := by simpa using hk
        rw [dn k hk']
        simp only [List.getElem_map, List.getElem_range]
        have hwr : ctx.contract.wordRuns[j']? = some (name, base, n0) :=
          wordRuns_of (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl)
        show inpOf ctx s0 j' (c.toNat / 4 + k) = load st.mem (P + 4 * k) 4
        unfold inpOf
        rw [hwr]
        show load s0.mem (s0.reg base + 4 * (c.toNat / 4 + k)) 4 = load st.mem (P + 4 * k) 4
        have ea : s0.reg base + 4 * (c.toNat / 4 + k) = P + 4 * k := by omega
        rw [ea]
        apply load_congr
        intro x hx1 hx2
        symm
        exact H.mem x (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
          (by
            unfold Contract.inOut
            rw [List.any_eq_false]
            intro ⟨x'', r'', n''⟩ hm
            have := f4 x'' r'' n'' hm
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            omega)
      next => simp at h
  | none =>
    simp only [hf] at h
    cases hr : findRegion a ctx.contract.regions 0 with
    | some wh =>
      obtain ⟨k', o, base, len, rfl, _, hl, ho⟩ := findRegion_spec hr
      simp only [Nat.sub_zero] at hl
      simp only [hr] at h
      cases hc : Lin.isConst o with
      | none => simp [hc] at h
      | some c =>
        simp only [hc, hl] at h
        split at h
        next hcond =>
          obtain ⟨c0, c4, hpl⟩ := hcond
          simp only [Option.some.injEq] at h
          have hm0 := List.mem_of_getElem? hl
          obtain ⟨r1, r2⟩ := E.regionAt hm0
          have ec := ev_isConst (ρ := ρ) hc
          rw [ho, ev_sub, ev_var, H.entry base (regions_lt hm0).1] at ec
          have hPc : P = s0.reg base + c.toNat := by omega
          have hple := plain_sound hpl ρ H.facts
          rw [ev_sub, ev_var, ev_const, H.entry len (regions_lt hm0).2] at hple
          let j' := ctx.contract.fixeds.length + ctx.contract.inouts.length + k'
          obtain ⟨e, ok, len', lt, dn⟩ := termsOf_step (mk := intern)
            (val := fun nd => match nd with | .input j k => inpOf ctx s0 j k | _ => 0)
            (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms)
            ((List.range (16 * nb)).map fun i => Node.input j' (c.toNat / 4 + i)) s.tab
            (fun nd ma T' _ okT => by
              obtain ⟨i, _, rfl⟩ := List.mem_map.mp ma
              exact input_step okT) (Ext.refl _) wf.words.ok
          rw [h] at e ok len' lt dn
          refine ⟨e, ok, by rw [len']; simp, lt, fun k hk => ?_, Or.inr (Or.inl ⟨base, len, c.toNat, hm0, hPc, by omega⟩)⟩
          have hk' : k < ((List.range (16 * nb)).map fun i => Node.input j' (c.toNat / 4 + i)).length := by simpa using hk
          rw [dn k hk']
          simp only [List.getElem_map, List.getElem_range]
          have hwr : ctx.contract.wordRuns[j']? = some ("", base, 0) := by
            unfold Contract.wordRuns
            have hk_lt : k' < ctx.contract.regions.length := (List.getElem?_eq_some_iff.mp hl).1
            rw [List.getElem?_append_left (by simp [j']; omega)]
            have hge : (ctx.contract.fixeds ++ ctx.contract.inouts).length ≤ j' := by simp [j']
            rw [List.getElem?_append_right hge]
            have hsub : j' - (ctx.contract.fixeds ++ ctx.contract.inouts).length = k' := by simp [j']
            rw [hsub, List.getElem?_map, hl]; rfl
          show inpOf ctx s0 j' (c.toNat / 4 + k) = load st.mem (P + 4 * k) 4
          unfold inpOf
          rw [hwr]
          show load s0.mem (s0.reg base + 4 * (c.toNat / 4 + k)) 4 = load st.mem (P + 4 * k) 4
          have ea : s0.reg base + 4 * (c.toNat / 4 + k) = P + 4 * k := by omega
          rw [ea]
          apply load_congr
          intro x hx1 hx2
          symm
          exact H.mem x (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (by
              unfold Contract.inOut
              rw [List.any_eq_false]
              intro ⟨x'', r'', n''⟩ hm
              have := E.outRegion hm hm0
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              omega)
        next => simp at h
    | none =>
      simp only [hr] at h
      cases ho : Lin.isConst (Lin.sub a (Lin.var RSP)) with
      | none => simp [ho] at h
      | some o =>
        cases hsp : s.sp with
        | none => simp [ho, hsp] at h
        | some sp =>
          simp only [ho, hsp] at h
          split at h
          next hcond =>
            cases hrows : frameRows s o (16 * nb) 0 with
            | none => simp [hrows] at h
            | some rows =>
              simp only [hrows, Option.map_some, Option.some.injEq] at h
              exact frameCase ho hsp hcond hrows h
          next => simp at h

/-- A lane's words, in blocks of sixteen, stand for the lane's blocks as the account has them: where each
term is the word memory holds at its place. -/
theorem lane_den {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} (wf : WF ctx s) (mem : Nat → Byte) (P : Nat) :
    ∀ (nb : Nat) (ids : List Nat) (off : Nat), ids.length = 16 * nb →
      (∀ k, k < 16 * nb → den (inpOf ctx s0) ρ s.terms (ids.getD k 0) = load mem (P + 64 * off + 4 * k) 4) →
      WDen ctx s0 ρ s.terms (.list (blocksOf nb (ids.map fun i => WVal.word [i])))
        (.list ((List.range nb).map fun b => blockWords mem (P + 64 * (off + b))))
  | 0, _, _, _, _ => by simp only [blocksOf, List.range_zero, List.map_nil]; exact WDen.nil
  | nb + 1, ids, off, hlen, hden => by
    simp only [blocksOf, List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [← List.map_take, ← List.map_drop]
    refine WDen.cons ?_ ?_
    · -- the first block
      rw [Nat.add_zero]
      have h16 : (ids.take 16).length = 16 := by rw [List.length_take]; omega
      have e : (ids.take 16).map (fun i => Val.word (den (inpOf ctx s0) ρ s.terms i)) =
          (List.range 16).map fun w => Val.word (load mem (P + 64 * off + 4 * w) 4) := by
        apply List.ext_getElem
        · simp only [List.length_map, List.length_range]; exact h16
        · intro w h1 h2
          have hw : w < 16 := by simpa using h2
          simp only [List.getElem_map, List.getElem_range, List.getElem_take]
          have hg : ids.getD w 0 = ids[w]'(by omega) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
          rw [← hg, hden w (by omega)]
      have key := WDen.wordsOf (ctx := ctx) (s0 := s0) (ρ := ρ) wf (ids.take 16)
      rw [e] at key
      exact key
    · -- the blocks after it
      have ih := lane_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf mem P nb (ids.drop 16) (off + 1) (by rw [List.length_drop]; omega)
        (fun k hk => by
          have hg : (ids.drop 16).getD k 0 = ids.getD (16 + k) 0 := by
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
          rw [hg, hden (16 + k) (by omega)]
          congr 1
          omega)
      have em : (List.range nb).map ((fun b => blockWords mem (P + 64 * (off + b))) ∘ Nat.succ) =
          (List.range nb).map fun b => blockWords mem (P + 64 * (off + 1 + b)) :=
        List.map_congr_left fun b _ => by
          show blockWords mem (P + 64 * (off + (b + 1))) = blockWords mem (P + 64 * (off + 1 + b))
          rw [show off + (b + 1) = off + 1 + b by omega]
      rw [em]
      exact ih

theorem okAll_iff {n t : Nat} : ∀ (l : List WVal), WVal.okAll n t l = true ↔ ∀ v ∈ l, v.ok n t = true
  | [] => by simp [WVal.okAll]
  | v :: rest => by
    simp only [WVal.okAll, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    rw [okAll_iff rest]

/-- Things in blocks of sixteen speak of no more than the things did. -/
theorem blocksOf_ok {n t : Nat} : ∀ (k : Nat) (l : List WVal), WVal.okAll n t l = true → WVal.okAll n t (blocksOf k l) = true
  | 0, _, _ => by simp [blocksOf, WVal.okAll]
  | k + 1, l, h => by
    simp only [blocksOf, WVal.okAll, WVal.ok, Bool.and_eq_true]
    exact ⟨(okAll_iff _).mpr fun v m => (okAll_iff l).mp h v (List.mem_of_mem_take m),
      blocksOf_ok k _ ((okAll_iff _).mpr fun v m => (okAll_iff l).mp h v (List.mem_of_mem_drop m))⟩

/-- The blocks at an address are the same in two memories that hold the same bytes there. -/
theorem laneBlocks_congr (mem mem' : Nat → Byte) (P nb : Nat) (h : ∀ x, P ≤ x → x < P + 64 * nb → mem x = mem' x) :
    laneBlocks mem P nb = laneBlocks mem' P nb := by
  unfold laneBlocks blockWords
  congr 1
  apply List.map_congr_left
  intro b hb
  have hb' : b < nb := List.mem_range.mp hb
  congr 1
  apply List.map_congr_left
  intro w hw
  have hw' : w < 16 := List.mem_range.mp hw
  congr 1
  exact load_congr mem mem' _ 4 (fun x h1 h2 => h x (by omega) (by omega))

/-- The lanes of a table in the frame, as `tableLanes` reads them from lane `i` on: the table of terms is
only added to; the lanes stand for the blocks at the addresses the table's cells hold now; and each lane's
blocks lie where this function may read them, apart from what the called function writes. -/
theorem tableLanes_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) {ct : Int} {nb : Nat} {cw : Int} {nout : Nat} :
    ∀ (count i : Nat) {T T' : Tab} {lanes : List WVal}, Ext s.terms T.list → TableOk s.nvars T.list →
      tableLanes ctx s ct nb cw nout count i T = some (lanes, T') →
      Ext T.list T'.list ∧ TableOk s.nvars T'.list ∧ WVal.okAll s.nvars T'.list.length lanes = true ∧
      WDen ctx s0 ρ T'.list (.list lanes)
        (.list ((List.range count).map fun j =>
          laneBlocks st.mem (load st.mem ((s0.reg RSP : Int) + (ct + 8 * ((i + j : Nat) : Int))).toNat 8) nb)) ∧
      ∀ j, j < count → LaneAt ctx s0 s (load st.mem ((s0.reg RSP : Int) + (ct + 8 * ((i + j : Nat) : Int))).toNat 8) nb cw nout
  | 0, i, T, T', lanes, e, ok, h => by
    simp only [tableLanes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.range_zero, List.map_nil]
    exact ⟨Ext.refl _, ok, by simp [WVal.okAll], WDen.nil, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | count + 1, i, T, T', lanes, e, ok, h => by
    simp only [tableLanes] at h
    cases hfind : s.frame.find? (fun cell => cell.1 == ct + 8 * (i : Int)) with
    | none => simp [hfind] at h
    | some cell =>
      obtain ⟨o, a⟩ := cell
      simp only [hfind] at h
      cases hl : laneWords ctx { s with tab := T } a nb cw nout with
      | none => simp [hl] at h
      | some pr =>
        obtain ⟨ids, T1⟩ := pr
        simp only [hl] at h
        cases hr : tableLanes ctx s ct nb cw nout count (i + 1) T1 with
        | none => simp [hr] at h
        | some pr2 =>
          obtain ⟨rest, T2⟩ := pr2
          simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hm := List.mem_of_find?_eq_some hfind
          have ho : o = ct + 8 * (i : Int) := by simpa using List.find?_some hfind
          obtain ⟨g1, g2, g3⟩ := H.frame o a hm
          have CT := Carried.terms H wf e ok
          obtain ⟨e1, ok1, len1, lt1, den1, at1⟩ := laneWords_sound E CT.holds CT.wf g3 hl
          obtain ⟨e2, ok2, okr, d2, at2⟩ := tableLanes_sound E H wf count (i + 1) (e.trans e1) ok1 hr
          have CT2 := Carried.terms H wf (e.trans (e1.trans e2)) ok2
          have dl := lane_den (ctx := ctx) (s0 := s0) (ρ := ρ) CT2.wf st.mem (load st.mem ((s0.reg RSP : Int) + o).toNat 8) nb ids 0 len1
            (fun k hk => by
              have hi : ids.getD k 0 < T1.list.length := lt1 _ (getD_mem ids 0 (by omega))
              have := den_ext (inp := inpOf ctx s0) (ρ := ρ) ok1.wf e2 hi
              rw [Nat.mul_zero, Nat.add_zero]
              exact this.trans (den1 k hk))
          simp only [Nat.zero_add] at dl
          refine ⟨e1.trans e2, ok2, ?_, ?_, ?_⟩
          · simp only [WVal.okAll, WVal.ok, Bool.and_eq_true]
            exact ⟨blocksOf_ok nb _ (okAll_words ids
              (List.all_eq_true.mpr fun i m => decide_eq_true (Nat.lt_of_lt_of_le (lt1 i m) e2.le))), okr⟩
          · simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
            refine WDen.cons ?_ ?_
            · rw [← ho]; exact dl
            · have em : (List.range count).map ((fun j =>
                    laneBlocks st.mem (load st.mem ((s0.reg RSP : Int) + (ct + 8 * ((i + j : Nat) : Int))).toNat 8) nb) ∘ Nat.succ) =
                  (List.range count).map fun j =>
                    laneBlocks st.mem (load st.mem ((s0.reg RSP : Int) + (ct + 8 * ((i + 1 + j : Nat) : Int))).toNat 8) nb :=
                List.map_congr_left fun j _ => by
                  show laneBlocks st.mem (load st.mem ((s0.reg RSP : Int) + (ct + 8 * ((i + (j + 1) : Nat) : Int))).toNat 8) nb = _
                  rw [show i + (j + 1) = i + 1 + j by omega]
              rw [em]
              exact d2
          · intro j hj
            cases j with
            | zero =>
              rw [Nat.add_zero, ← ho]
              exact at1
            | succ j =>
              have := at2 j (by omega)
              rw [show i + 1 + j = i + (j + 1) by omega] at this
              exact this

/-! ## The names of the called function -/

theorem frameWordId_lt {ctx : Ctx} {s : Sym} (wf : WF ctx s) {o : Int} {id : Nat} (h : frameWordId s o = some id) :
    id < s.terms.length := by
  unfold frameWordId at h
  cases hf : s.frameW.find? (fun cell => cell.1 == o) with
  | some cell =>
    simp only [hf, Option.some.injEq] at h; subst h
    exact wf.frameW cell.1 cell.2 (List.mem_of_find?_eq_some hf)
  | none =>
    simp only [hf] at h
    cases hw : frameWord s o with
    | none => simp [hw] at h
    | some x =>
      simp only [hw, Option.bind_some] at h
      exact (List.getElem?_eq_some_iff.mp (Looks.found (look := s.tab.find) h)).1

theorem frameRunIds_lt {ctx : Ctx} {s : Sym} (wf : WF ctx s) (c : Int) :
    ∀ (count k : Nat) {ids : List Nat}, frameRunIds s c count k = some ids → ∀ i ∈ ids, i < s.terms.length
  | 0, _, _, h, _, m => by simp only [frameRunIds, Option.some.injEq] at h; subst h; cases m
  | count + 1, k, ids, h, i, m => by
    simp only [frameRunIds] at h
    cases hw : frameWordId s (c + 4 * (k : Int)) with
    | none => simp [hw] at h
    | some id =>
      cases hr : frameRunIds s c count (k + 1) with
      | none => simp [hw, hr] at h
      | some rest =>
        simp only [hw, hr, Option.some.injEq] at h; subst h
        rcases List.mem_cons.mp m with rfl | m
        · exact frameWordId_lt wf hw
        · exact frameRunIds_lt wf c count (k + 1) hr i m

theorem frameRun_lt {ctx : Ctx} {s : Sym} (wf : WF ctx s) {r n : Nat} {c : Int} {ids : List Nat}
    (h : frameRun s r n = some (c, ids)) : ∀ i ∈ ids, i < s.terms.length := by
  unfold frameRun at h
  cases hf : frameAt s r with
  | none => simp [hf] at h
  | some c' =>
    cases hsp : s.sp with
    | none => simp [hf, hsp] at h
    | some sp =>
      simp only [hf, hsp] at h
      split at h
      · cases hi : frameRunIds s c' (n / 4) 0 with
        | none => simp [hi] at h
        | some ids' =>
          simp only [hi, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact frameRunIds_lt wf c' (n / 4) 0 hi
      · cases h

/-- The called function's names on words (`calleeL`) stand for its names as the account has them in the
state it starts in (`s1`): a number is its register; a part of a run of a fixed count is the bytes there
(either from an entry run or from the caller's frame); of the table's own bytes nothing is said. -/
theorem calleeL_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) {T : List Node}
    (c : Contract) (hm : c.regs = ctx.nreg) {s1 : State} {tx : String} {tr nt : Nat}
    (hreg : ∀ r ∈ c.argRegs, s1.reg r = st.reg r)
    (hfix : ∀ r n j b cst, r ∈ c.argRegs → fixedPart ctx s r n = some (j, b, cst) →
      ∀ k, k < n → s1.mem (st.reg r + k) = s0.mem (s0.reg b + cst + k) ∧ (s0.mem (s0.reg b + cst + k)).val < 256)
    (hfr : ∀ r n cf fids, r ∈ c.argRegs → frameRun s r n = some (cf, fids) →
      (List.range n).map (fun k => Val.int (s1.mem (s1.reg r + k))) = wordBytes (fids.map (den (inpOf ctx s0) ρ T))) :
    ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × WVal)}, (∀ r ∈ regs, r ∈ c.argRegs) →
      calleeL ctx s tx tr nt args regs = some env → EnvDen ctx s0 ρ T env (envWIn c s1 args regs)
  | [], _, env, _, h => by
    simp only [calleeL, Option.some.injEq] at h; subst h; simp [envWIn, EnvDen]
  | _ :: _, [], env, _, h => by
    simp only [calleeL, Option.some.injEq] at h; subst h; simp [envWIn, EnvDen]
  | (x, .number) :: args, r :: regs, env, hr, h => by
    simp only [calleeL] at h
    cases hrec : calleeL ctx s tx tr nt args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
      have ih := calleeL_sound (T := T) H c hm hreg hfix hfr args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec
      simp only [envWIn]
      refine ⟨rfl, ?_, ih⟩
      have ra := hr r (List.mem_cons_self ..)
      have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := T) (s.reg r)
      rw [← H.reg r (hm ▸ argRegs_lt ra), ← hreg r ra] at this
      exact this
  | (x, .fixed n) :: args, r :: regs, env, hr, h => by
    simp only [calleeL] at h
    split at h
    · split at h
      · cases hrec : calleeL ctx s tx tr nt args regs with
        | none => simp [hrec] at h
        | some env' =>
          simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
          have ih := calleeL_sound (T := T) H c hm hreg hfix hfr args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec
          simp only [envWIn]
          exact ⟨rfl, WDen.other _, ih⟩
      · cases h
    · cases hf : fixedPart ctx s r n with
      | none =>
        cases hrec : calleeL ctx s tx tr nt args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          simp only [hf, hrec] at h
          cases hfrun : frameRun s r n with
          | none => simp [hfrun] at h
          | some pr =>
            obtain ⟨cf, fids⟩ := pr
            simp only [hfrun, Option.map_some, Option.some.injEq] at h; subst h
            have ih := calleeL_sound (T := T) H c hm hreg hfix hfr args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec
            simp only [envWIn]
            refine ⟨rfl, ?_, ih⟩
            have ra := hr r (List.mem_cons_self ..)
            simp only [Val.bytes, List.map_map]
            show WDen ctx s0 ρ T (.wbytes fids) (.list ((List.range n).map fun k => Val.int (s1.mem (s1.reg r + k))))
            rw [hfr r n cf fids ra hfrun]
            exact WDen.wbytes fids
      | some pp =>
        obtain ⟨j, b, cst⟩ := pp
        cases hrec : calleeL ctx s tx tr nt args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          simp only [hf, hrec, Option.some.injEq] at h; subst h
          have ih := calleeL_sound (T := T) H c hm hreg hfix hfr args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec
          simp only [envWIn]
          refine ⟨rfl, ?_, ih⟩
          have ra := hr r (List.mem_cons_self ..)
          have hb : ∀ k, k < n → (s0.mem (s0.reg b + cst + k)).val < 256 := fun k hk => (hfix r n j b cst ra hf k hk).2
          have e : (List.range n).map (fun k => Val.int (s1.mem (s1.reg r + k))) =
              (List.range n).map fun k => Val.int (s0.mem (s0.reg b + cst + k)) :=
            List.map_congr_left fun k mk => by
              rw [hreg r ra, (hfix r n j b cst ra hf k (List.mem_range.mp mk)).1]
          simp only [Val.bytes, List.map_map]
          show WDen ctx s0 ρ T (.part b cst n) (.list ((List.range n).map fun k => Val.int (s1.mem (s1.reg r + k))))
          rw [e]
          exact WDen.part b cst n hb
  | (x, .out n) :: args, r :: regs, env, hr, h => by
    simp only [calleeL] at h
    simp only [envWIn]
    exact calleeL_sound (T := T) H c hm hreg hfix hfr args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) h
  | (x, .inout n) :: args, r :: regs, env, _, h => by simp [calleeL] at h
  | (x, .bytes len) :: args, r :: regs, env, _, h => by simp [calleeL] at h

/-- The called function's names on words speak only of unknowns in use and terms of the table. -/
theorem calleeL_ok {ctx : Ctx} {s : Sym} (wf : WF ctx s) {tx : String} {tr nt : Nat} :
    ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × WVal)}, (∀ r ∈ regs, r < ctx.nreg) →
      calleeL ctx s tx tr nt args regs = some env → EnvOk s.nvars s.terms.length env
  | [], _, env, _, h => by
    simp only [calleeL, Option.some.injEq] at h; subst h; intro p m; cases m
  | _ :: _, [], env, _, h => by
    simp only [calleeL, Option.some.injEq] at h; subst h; intro p m; cases m
  | (x, .number) :: args, r :: regs, env, hr, h => by
    simp only [calleeL] at h
    cases hrec : calleeL ctx s tx tr nt args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
      refine EnvOk.cons ?_ (calleeL_ok wf args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec)
      have := wf.reg r (hr r (List.mem_cons_self ..))
      simp only [WVal.ok, decide_eq_true_eq]
      exact this
  | (x, .fixed n) :: args, r :: regs, env, hr, h => by
    simp only [calleeL] at h
    split at h
    · split at h
      · cases hrec : calleeL ctx s tx tr nt args regs with
        | none => simp [hrec] at h
        | some env' =>
          simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
          exact EnvOk.cons (by simp [WVal.ok]) (calleeL_ok wf args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec)
      · cases h
    · cases hf : fixedPart ctx s r n with
      | none =>
        cases hrec : calleeL ctx s tx tr nt args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          simp only [hf, hrec] at h
          cases hfrun : frameRun s r n with
          | none => simp [hfrun] at h
          | some pr =>
            obtain ⟨cf, fids⟩ := pr
            simp only [hfrun, Option.map_some, Option.some.injEq] at h; subst h
            refine EnvOk.cons ?_ (calleeL_ok wf args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec)
            simp only [WVal.ok, List.all_eq_true, decide_eq_true_eq]
            exact frameRun_lt wf hfrun
      | some pp =>
        obtain ⟨j, b, cst⟩ := pp
        cases hrec : calleeL ctx s tx tr nt args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          simp only [hf, hrec, Option.some.injEq] at h; subst h
          exact EnvOk.cons (by simp [WVal.ok]) (calleeL_ok wf args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec)
  | (x, .out n) :: args, r :: regs, env, hr, h => by
    simp only [calleeL] at h
    exact calleeL_ok wf args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) h
  | (x, .inout n) :: args, r :: regs, env, _, h => by simp [calleeL] at h
  | (x, .bytes len) :: args, r :: regs, env, _, h => by simp [calleeL] at h

/-- Each run of a fixed count the called function is given is the table itself, in its register and of its
count of bytes, or a part of one of this function's runs, or a part of this function's frame. -/
theorem calleeL_fixeds {ctx : Ctx} {s : Sym} {tx : String} {tr nt : Nat} :
    ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × WVal)}, calleeL ctx s tx tr nt args regs = some env →
    ∀ x r n, (x, r, n) ∈ fixedsIn args regs →
      (x = tx ∧ r = tr ∧ n = nt) ∨ (x ≠ tx ∧ ((∃ j b cst, fixedPart ctx s r n = some (j, b, cst)) ∨ (∃ cf fids, frameRun s r n = some (cf, fids))))
  | [], _, _, _, x, r, n, m => by simp [fixedsIn] at m
  | _ :: _, [], _, _, x, r, n, m => by simp [fixedsIn] at m
  | (y, .number) :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeL] at h
    cases hrec : calleeL ctx s tx tr nt args regs with
    | none => simp [hrec] at h
    | some env' => simp only [fixedsIn] at m; exact calleeL_fixeds args regs hrec x r n m
  | (y, .fixed n') :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeL] at h
    simp only [fixedsIn, List.mem_cons] at m
    split at h
    next hx =>
      split at h
      next hrn =>
        cases hrec : calleeL ctx s tx tr nt args regs with
        | none => simp [hrec] at h
        | some env' =>
          rcases m with e | m
          · have ex : x = y ∧ r = r' ∧ n = n' := by simpa using e
            obtain ⟨ex, er, en⟩ := ex
            rw [ex, er, en]
            exact Or.inl ⟨by simpa using hx, hrn.1, hrn.2⟩
          · exact calleeL_fixeds args regs hrec x r n m
      next => cases h
    next hx =>
      cases hf : fixedPart ctx s r' n' with
      | none =>
        cases hrec : calleeL ctx s tx tr nt args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          simp only [hf, hrec] at h
          cases hfrun : frameRun s r' n' with
          | none => simp [hfrun] at h
          | some pr =>
            obtain ⟨cf, fids⟩ := pr
            rcases m with e | m
            · have ex : x = y ∧ r = r' ∧ n = n' := by simpa using e
              obtain ⟨ex, er, en⟩ := ex
              rw [ex, er, en]
              exact Or.inr ⟨by simpa using hx, Or.inr ⟨cf, fids, hfrun⟩⟩
            · exact calleeL_fixeds args regs hrec x r n m
      | some pp =>
        obtain ⟨j, b, cst⟩ := pp
        cases hrec : calleeL ctx s tx tr nt args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          rcases m with e | m
          · have ex : x = y ∧ r = r' ∧ n = n' := by simpa using e
            obtain ⟨ex, er, en⟩ := ex
            rw [ex, er, en]
            exact Or.inr ⟨by simpa using hx, Or.inl ⟨j, b, cst, hf⟩⟩
          · exact calleeL_fixeds args regs hrec x r n m
  | (y, .out n') :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeL] at h
    simp only [fixedsIn] at m
    exact calleeL_fixeds args regs h x r n m
  | (y, .inout n') :: args, r' :: regs, env, h, _, _, _, _ => by simp [calleeL] at h
  | (y, .bytes len) :: args, r' :: regs, env, h, _, _, _, _ => by simp [calleeL] at h

/-! ## The state after the call -/

/-- A cell that pairs of words make: which pair, and where. -/
theorem cellsOf_mem (c : Int) : ∀ (j : Nat) (rows : List Row) {o : Int} {v : Row}, (o, v) ∈ cellsOf c j rows →
    ∃ i, 2 * i + 1 < rows.length ∧ o = c + 8 * ((j + i : Nat) : Int) ∧
      v = Lin.add (rows.getD (2 * i) (Lin.const 0)) (Lin.scale W32i (rows.getD (2 * i + 1) (Lin.const 0)))
  | j, [], o, v, h => by simp [cellsOf] at h
  | j, [_], o, v, h => by simp [cellsOf] at h
  | j, lo :: hi :: rest, o, v, h => by
    simp only [cellsOf, List.mem_cons] at h
    rcases h with h | h
    · have e : o = c + 8 * (j : Int) ∧ v = Lin.add lo (Lin.scale W32i hi) := by simpa using h
      exact ⟨0, by simp only [List.length_cons]; omega, by rw [Nat.add_zero]; exact e.1, by simpa using e.2⟩
    · obtain ⟨i, hi', ho, hv⟩ := cellsOf_mem c (j + 1) rest h
      refine ⟨i + 1, by simp only [List.length_cons]; omega, by rw [ho, show j + 1 + i = j + (i + 1) by omega], ?_⟩
      rw [hv, show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
      simp only [List.getD_cons_succ]

theorem afterCallL_wf {ctx : Ctx} {s : Sym} (wf : WF ctx s) (ct : Contract) (hm : ct.regs = ctx.nreg) (sp cw : Int) (n : Nat) {rows : List Row} (hb : ∀ r ∈ rows, bounded s.nvars r) :
    WF ctx (Sym.afterCallL ct s sp cw n rows) := by
  have le : s.nvars ≤ s.nvars + ct.regs := Nat.le_add_right _ _
  refine ⟨Nat.le_trans wf.base le, ?_, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨wf.words.table, fun j r h => bounded_mono le (wf.words.atoms j r h), (fun x ids h => by simp [Sym.afterCallL] at h),
     wf.words.rotrs, wf.words.wrote, fun _ _ h => nomatch h⟩,
    fun k m => Known.wf_mono le (Nat.le_refl _) (wf.known k m), fun _ h => nomatch h⟩
  · intro r hr
    show bounded (s.nvars + ct.regs) (if ct.scratch.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    split
    · exact bounded_var (by omega)
    · exact bounded_mono le (wf.reg r hr)
  · intro o v mm
    have mm' : (o, v) ∈ cellsOf cw 0 rows ++
        s.frame.filter (fun cell => decide (sp ≤ cell.1) && (decide (cell.1 + 8 ≤ cw) || decide (cw + (n : Int) ≤ cell.1))) := mm
    rcases List.mem_append.mp mm' with mn | mo
    · obtain ⟨i, hi, _, hv⟩ := cellsOf_mem cw 0 rows mn
      rw [hv]
      exact bounded_add (bounded_mono le (hb _ (getD_mem rows _ (by omega))))
        (bounded_scale _ (bounded_mono le (hb _ (getD_mem rows _ (by omega)))))
    · exact bounded_mono le (wf.frame o v (List.mem_filter.mp mo).1)
  · intro o i mm
    exact wf.frameW o i (List.mem_filter.mp mm).1
  · intro f m
    simp only [Sym.afterCallL, List.mem_append] at m
    rcases m with m | m
    · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp m
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
      have hr := scratch_lt hr
      simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · exact bounded_var (show s.nvars + r < s.nvars + ct.regs by omega)
      · exact bounded_sub (bounded_const _ _) (bounded_var (show s.nvars + r < s.nvars + ct.regs by omega))
    · exact bounded_mono le (wf.facts f m)
  · intro v r o m
    have := wf.bytes v r o m
    exact ⟨Nat.lt_of_lt_of_le this.1 le, bounded_mono le this.2⟩
  · intro f m
    exact SFact.bounded_mono le (wf.spec f m)
  · intro w o x m
    exact ⟨bounded_mono le (wf.wrote w o x m).1, bounded_mono le (wf.wrote w o x m).2⟩

/-- After a call of a function that has written a part of the frame, where the rows are the words it left
there: what the verifier then holds is so. -/
theorem afterCallL_holds {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st s2 : State}
    {sp : Int} (ct : Contract) (cst : Nat) (hm : ct.regs = ctx.nreg) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (hsp : (st.reg RSP : Int) = s0.reg RSP + sp) (hlow : -(ctx.contract.stackAt s0 : Int) ≤ sp - ct.slot - cst) (hsp0 : sp ≤ 0)
    (hkeep : ∀ r, r < ctx.nreg → ct.scratch.contains r = false → s2.reg r = st.reg r)
    (hsmall : ∀ r, s2.reg r < M64)
    {c : Int} {n : Nat} {rows : List Row} (hc : sp ≤ c) (hce : c + (n : Int) ≤ 0) (hn : rows.length * 4 = n)
    (hb : ∀ r ∈ rows, bounded s.nvars r)
    (hmem : ∀ a : Nat, a + ct.slot + cst < st.reg RSP ∨ st.reg RSP ≤ a →
      (a : Int) < s0.reg RSP + c ∨ (s0.reg RSP : Int) + c + (n : Int) ≤ a → s2.mem a = st.mem a)
    (hdata : s2.data = st.data)
    (hrows : ∀ k, k < rows.length →
      (load s2.mem (((s0.reg RSP : Int) + c).toNat + 4 * k) 4 : Int) = ev ρ (rows.getD k (Lin.const 0))) :
    Holds ctx s0 (afterRho ct.regs s.nvars ρ s2) (Sym.afterCallL ct s sp c n rows) s2 := by
  have hstack := E.stackAt
  have ag := afterRho_agree ct.regs s.nvars ρ s2
  have H' := H.agree wf ag
  refine ⟨H'.entry, ⟨H'.data.1, hdata.trans H.data.2⟩, ?_, hsmall, trivial, trivial, ?_, ?_, ?_, H'.bytes, H'.spec, ?_, ?_,
    ⟨(fun x ids h => by simp [Sym.afterCallL] at h), ?_, ?_, fun _ _ h => nomatch h⟩, H'.known, fun _ h => nomatch h⟩
  · intro r hr
    show (s2.reg r : Int) = ev _ (if ct.scratch.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    cases hcs : ct.scratch.contains r with
    | true => rw [if_pos rfl, ev_var, afterRho_new _ _ _ _ (hm ▸ hr)]
    | false =>
      rw [if_neg (by decide), hkeep r hr hcs]
      exact H'.reg r hr
  · -- the frame's cells: the new ones are two of the words left each; the others were not written
    intro o v mm
    have mm' : (o, v) ∈ cellsOf c 0 rows ++
        s.frame.filter (fun cell => decide (sp ≤ cell.1) && (decide (cell.1 + 8 ≤ c) || decide (c + (n : Int) ≤ cell.1))) := mm
    rcases List.mem_append.mp mm' with mn | mo
    · obtain ⟨i, hi, ho, hv⟩ := cellsOf_mem c 0 rows mn
      rw [Nat.zero_add] at ho
      subst o
      refine ⟨by omega, by omega, ?_⟩
      have a0 : ((s0.reg RSP : Int) + (c + 8 * (i : Int))).toNat = ((s0.reg RSP : Int) + c).toNat + 4 * (2 * i) := by omega
      have a1 : ((s0.reg RSP : Int) + (c + 8 * (i : Int))).toNat + 4 = ((s0.reg RSP : Int) + c).toNat + 4 * (2 * i + 1) := by omega
      have r0 := hrows (2 * i) (by omega)
      have r1 := hrows (2 * i + 1) (by omega)
      have b0 := hb _ (getD_mem rows (Lin.const 0) (show 2 * i < rows.length by omega))
      have b1 := hb _ (getD_mem rows (Lin.const 0) (show 2 * i + 1 < rows.length by omega))
      rw [hv, load_halves, a1, a0, ev_add, ev_scale, ← ev_agree b0 ag, ← ev_agree b1 ag, ← r0, ← r1]
      unfold W32i
      omega
    · obtain ⟨m1, m2⟩ := List.mem_filter.mp mo
      have m2' : sp ≤ o ∧ (o + 8 ≤ c ∨ c + (n : Int) ≤ o) := by simpa using m2
      obtain ⟨h1, h2, h3⟩ := H'.frame o v m1
      refine ⟨h1, h2, ?_⟩
      have e : load s2.mem ((s0.reg RSP : Int) + o).toNat 8 = load st.mem ((s0.reg RSP : Int) + o).toNat 8 :=
        load_congr _ _ _ _ (fun a hx1 hx2 => hmem a (Or.inr (by omega)) (by omega))
      rw [e]; exact h3
  · intro o i mm
    obtain ⟨m1, m2⟩ := List.mem_filter.mp mm
    have m2' : sp ≤ o ∧ (o + 4 ≤ c ∨ c + (n : Int) ≤ o) := by simpa using m2
    obtain ⟨h1, h2, h3⟩ := H'.frameW o i m1
    refine ⟨h1, h2, ?_⟩
    have e : load s2.mem ((s0.reg RSP : Int) + o).toNat 4 = load st.mem ((s0.reg RSP : Int) + o).toNat 4 :=
      load_congr _ _ _ _ (fun a hx1 hx2 => hmem a (Or.inr (by omega)) (by omega))
    rw [e]; exact h3
  · intro f m
    simp only [Sym.afterCallL, List.mem_append] at m
    rcases m with m | m
    · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp m
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
      have hr := scratch_lt hr
      have sm := hsmall r
      unfold M64 at sm
      have val := afterRho_new ct.regs s.nvars ρ s2 hr
      simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · rw [holds_iff, ev_var, val]; omega
      · rw [holds_iff, ev_sub, ev_const, ev_var, val]; simp only [top]; omega
    · exact H'.facts f m
  · intro a ha ho
    have hfr : a + ct.slot + cst < st.reg RSP ∨ st.reg RSP ≤ a := by
      simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at ha
      omega
    have hout : (a : Int) < s0.reg RSP + c ∨ (s0.reg RSP : Int) + c + (n : Int) ≤ a := by
      simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at ha
      omega
    rw [hmem a hfr hout]
    exact H.mem a ha ho
  · -- what this function wrote for its caller, byte by byte, is of runs that lie apart from the frame
    intro w' o x' mw
    obtain ⟨name, r', n', g1, g2, g3, g4⟩ := H'.wrote w' o x' mw
    refine ⟨name, r', n', g1, g2, g3, ?_⟩
    have ho' := E.outAt (List.mem_of_getElem? g1)
    rw [hmem _ (by omega) (by omega)]
    exact g4
  · intro w' mw' x' r' n' ho' k hk
    have hor := E.outAt (List.mem_of_getElem? ho')
    rw [hmem _ (by omega) (by omega)]
    exact H'.words.intact w' mw' x' r' n' ho' k hk
  · intro w' j i mw' x' r' n' ho'
    obtain ⟨h1, h2⟩ := H'.words.wrote w' j i mw' x' r' n' ho'
    have hor := E.outAt (List.mem_of_getElem? ho')
    refine ⟨h1, fun bb hbb => ?_⟩
    rw [hmem _ (by omega) (by omega)]
    exact h2 bb hbb

/-! ## What the lanes leave -/

/-- The unknowns from `n` on are what `f` says; those below stay. -/
def extendFrom (ρ : Nat → Int) (n : Nat) (f : Nat → Int) : Nat → Int := fun k => if n ≤ k then f (k - n) else ρ k

theorem extendFrom_agree (ρ : Nat → Int) (n : Nat) (f : Nat → Int) : Agree n ρ (extendFrom ρ n f) := fun k hk => by
  show ρ k = if n ≤ k then f (k - n) else ρ k
  rw [if_neg (by omega)]

theorem extendFrom_new (ρ : Nat → Int) (n : Nat) (f : Nat → Int) (k : Nat) : extendFrom ρ n f (n + k) = f k := by
  show (if n ≤ n + k then f (n + k - n) else ρ (n + k)) = f k
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- The use that has a number is among what is known. -/
theorem useOf_mem {h : Nat} : ∀ {known : List Known} {f : String} {keys : List Key},
    useOf h known = some (f, keys) → Known.use f keys h ∈ known
  | [], _, _, e => by simp [useOf] at e
  | k :: more, f, keys, e => by
    cases k with
    | use f' keys' h' =>
      simp only [useOf] at e
      split at e
      next heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        subst heq
        exact List.mem_cons_self ..
      next => exact List.mem_cons_of_mem _ (useOf_mem e)
    | _ => simp only [useOf] at e; exact List.mem_cons_of_mem _ (useOf_mem e)

theorem WDen.use_inv {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {T : List Node} {h : Nat} {a : Val}
    (d : WDen ctx s0 ρ T (.use h) a) : a = Val.decode (ρ h).toNat := by cases d; rfl

/-- The bytes a contract says a run holds, where they are `bytes_of` of something: that thing has a value
that is words below 2^32, and the bytes are theirs. -/
theorem bytes_of_inv {defs : List Def} {env : List (String × Val)} {x : SExpr} {l : List Nat}
    (hv : Value defs env (.call "bytes_of" (.cons x .nil)) (.bytes l)) :
    ∃ (fuel : Nat) (nums : List Nat), evalSpec defs fuel env x = some (.list (nums.map Val.word)) ∧
      (∀ v ∈ nums, v < W32) ∧ l.map (fun (b : Nat) => Val.int b) = wordBytes nums := by
  obtain ⟨fuel, hf⟩ := hv
  cases fuel with
  | zero => simp [evalSpec] at hf
  | succ f1 =>
    simp only [evalSpec, evalList] at hf
    cases h1 : evalSpec defs f1 env x with
    | none => simp [h1] at hf
    | some v1 =>
      simp only [h1] at hf
      have o1 : own.contains "bytes_of" = true := by decide
      have o2 : ("bytes_of" == "len") = false := by decide
      simp only [o1, o2, Bool.false_eq_true, ↓reduceIte] at hf
      cases v1 with
      | list ws =>
        cases ho : ofWords ws with
        | none => simp [builtin, ho] at hf
        | some bs =>
          simp [builtin, ho, Val.bytes] at hf
          obtain ⟨nums, e1, e2, e3⟩ := ofWords_spec ho
          subst e1
          exact ⟨f1, nums, h1, e2, by rw [← hf, e3]⟩
      | _ => simp [builtin] at hf

/-- The use a lane's expression comes to (`laneUse`), where the expression has the value `l`, a list of
bytes: the state it comes back with is carried, with the table as it was; and where there is a use, the
things it is used with are in order, and it gives words below 2^32 whose bytes are `l`. -/
theorem laneUse_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s s1 : Sym} {env : List (String × WVal)}
    {env' : List (String × Val)} {e : SExpr} {l : List Nat} {use : Option (String × List Key)}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hpv : ctx.contract.preVals ctx.defs s0)
    (hE : EnvDen ctx s0 ρ s.terms env env') (hO : EnvOk s.nvars s.terms.length env)
    (hv : Value ctx.defs env' e (.bytes l)) (hu : laneUse ctx s env e = (s1, use)) :
    ∃ ρ1, Carried ctx s0 ρ s ρ1 s1 st ∧ s1.tab = s.tab ∧
      ∀ f keys, use = some (f, keys) → (∀ k ∈ keys, k.wf s1.nvars s1.terms.length) ∧
        ∃ d nums, findDef ctx.defs f = some d ∧ d.params.length = keys.length ∧
          Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ1 s1.terms))) d.body (.list (nums.map Val.word)) ∧
          (∀ v ∈ nums, v < W32) ∧ l.map (fun (b : Nat) => Val.int b) = wordBytes nums := by
  unfold laneUse at hu
  split at hu
  next f x =>
    split at hu
    next hf =>
      have ef : f = "bytes_of" := by simpa using hf
      subst ef
      split at hu
      next h s1' hnv =>
        simp only [Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        obtain ⟨fuel, nums, hx, hlt, hb⟩ := bytes_of_inv hv
        obtain ⟨ρ1, C1, t1, ok1, d1⟩ := nameval_sound WFUEL fuel H wf hpv hE hO hnv hx
        have inv := d1.use_inv
        refine ⟨ρ1, C1, t1, fun f' keys hu' => ?_⟩
        have hm := useOf_mem hu'
        obtain ⟨d, hd, hlen, hval⟩ := C1.holds.known _ hm hpv
        have hwf := C1.wf.known _ hm
        exact ⟨hwf.1, d, nums, hd, hlen, by rw [inv]; exact hval, hlt, hb⟩
      next =>
        simp only [Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact ⟨ρ, Carried.here H wf, rfl, fun f keys h => nomatch h⟩
    next =>
      simp only [Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      exact ⟨ρ, Carried.here H wf, rfl, fun f keys h => nomatch h⟩
  next =>
    simp only [Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    exact ⟨ρ, Carried.here H wf, rfl, fun f keys h => nomatch h⟩

private theorem laneUse_carried_vacuous {ctx : Ctx} {s0 st : State} (nhpv : ¬ ctx.contract.preVals ctx.defs s0)
    {ρ : Nat → Int} {s s1 : Sym} {env : List (String × WVal)} {e : SExpr} {use : Option (String × List Key)}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hO : EnvOk s.nvars s.terms.length env)
    (hu : laneUse ctx s env e = (s1, use)) :
    ∃ ρ1, Carried ctx s0 ρ s ρ1 s1 st ∧ s1.tab = s.tab ∧
      ∀ f keys, use = some (f, keys) → ∀ k ∈ keys, k.wf s1.nvars s1.terms.length := by
  unfold laneUse at hu
  split at hu
  next f x =>
    split at hu
    next =>
      split at hu
      next h s1' hnv =>
        simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu
        obtain ⟨ρ1, C1, t1, _⟩ := nameval_carried_vacuous nhpv WFUEL H wf hO hnv
        exact ⟨ρ1, C1, t1, fun f' keys hu' => (C1.wf.known _ (useOf_mem hu')).1⟩
      next => simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu; exact ⟨ρ, Carried.here H wf, rfl, fun _ _ h => nomatch h⟩
    next => simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu; exact ⟨ρ, Carried.here H wf, rfl, fun _ _ h => nomatch h⟩
  next => simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu; exact ⟨ρ, Carried.here H wf, rfl, fun _ _ h => nomatch h⟩

/-- The terms made for `m` new words whose unknowns begin at `s.nvars`. -/
def madeN (s : Sym) (m : Nat) : List Nat × Tab := termsOf wAtom ((List.range m).map fun k => Lin.var (s.nvars + k)) s.tab

theorem madeN_table {s : Sym} (wf : WF ctx s) (m : Nat) (inp : Nat → Nat → Nat) (ρ : Nat → Int) :
    Ext s.terms (madeN s m).2.list ∧ TableOk (s.nvars + m) (madeN s m).2.list ∧ (madeN s m).1.length = m ∧
    (∀ i ∈ (madeN s m).1, i < (madeN s m).2.list.length) ∧
    ∀ k, k < m → den inp ρ (madeN s m).2.list ((madeN s m).1.getD k 0) = (ev ρ (Lin.var (s.nvars + k)) % W32i).toNat := by
  obtain ⟨ext, ok, len, lt, dn⟩ := termsOf_step (mk := wAtom) (val := fun r => (ev ρ r % W32i).toNat)
    (inp := inp) (ρ := ρ) (nv := s.nvars + m) (T0 := s.terms)
    ((List.range m).map fun k => Lin.var (s.nvars + k)) s.tab
    (fun a ma T _ okT => wAtom_step okT (by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ma
      have := List.mem_range.mp hk
      exact bounded_var (by omega)))
    (Ext.refl _) (wf.words.ok.mono (by omega))
  refine ⟨ext, ok, ?_, lt, ?_⟩
  · have := len
    simp only [List.length_map, List.length_range] at this
    exact this
  · intro k hk
    have := dn k (by simpa using hk)
    simp only [List.getElem_map, List.getElem_range] at this
    exact this

/-- `m` words as new unknowns (`Sym.newWords`), where the unknowns are given the values `w`, each below
2^32, and, where there is a use, the use gives the words `w`: the state is carried; the rows speak of
unknowns in use and stand for the words. -/
theorem newWords_carried {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (m : Nat) (w : Nat → Nat) (hw : ∀ k, k < m → w k < W32) (use : Option (String × List Key))
    (huse : ∀ f keys, use = some (f, keys) → (∀ k ∈ keys, k.wf s.nvars s.terms.length) ∧
      (ctx.contract.preVals ctx.defs s0 → ∃ d, findDef ctx.defs f = some d ∧ d.params.length = keys.length ∧
        Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ s.terms))) d.body
          (.list ((List.range m).map fun k => Val.word (w k))))) :
    Carried ctx s0 ρ s (extendFrom ρ s.nvars fun k => (w k : Int)) (s.newWords m use).2 st ∧
    (s.newWords m use).1.length = m ∧
    (∀ r ∈ (s.newWords m use).1, bounded (s.nvars + m) r) ∧
    (s.newWords m use).2.nvars = s.nvars + m ∧
    Ext s.terms (s.newWords m use).2.terms ∧
    ∀ k, k < m → ev (extendFrom ρ s.nvars fun k => (w k : Int)) ((s.newWords m use).1.getD k (Lin.const 0)) = (w k : Int) := by
  have ag := extendFrom_agree ρ s.nvars fun k => (w k : Int)
  have hval : ∀ k, extendFrom ρ s.nvars (fun k => (w k : Int)) (s.nvars + k) = (w k : Int) := fun k => extendFrom_new _ _ _ k
  have Ca := Carried.unknowns H wf m ag
  obtain ⟨e, ok, len, lt, dn⟩ := madeN_table wf m (inpOf ctx s0) (extendFrom ρ s.nvars fun k => (w k : Int))
  have Cb : Carried ctx s0 (extendFrom ρ s.nvars fun k => (w k : Int)) { s with nvars := s.nvars + m }
      (extendFrom ρ s.nvars fun k => (w k : Int)) { s with nvars := s.nvars + m, tab := (madeN s m).2 } st :=
    Carried.terms Ca.holds Ca.wf e ok
  have hden : ∀ k, k < m →
      den (inpOf ctx s0) (extendFrom ρ s.nvars fun k => (w k : Int)) (madeN s m).2.list ((madeN s m).1.getD k 0) = w k := by
    intro k hk
    rw [dn k hk, ev_var, hval k]
    have := hw k hk
    unfold W32 at this
    unfold W32i
    omega
  have hfb : ∀ f ∈ ((List.range m).map fun k => ranged32 (s.nvars + k)).flatten, bounded (s.nvars + m) f := by
    intro f mf
    obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
    have hk := List.mem_range.mp hk
    simp only [ranged32, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl
    · exact bounded_var (show s.nvars + k < s.nvars + m by omega)
    · exact bounded_sub (bounded_const _ _) (bounded_var (show s.nvars + k < s.nvars + m by omega))
  have hfh : ∀ f ∈ ((List.range m).map fun k => ranged32 (s.nvars + k)).flatten,
      f.holds (extendFrom ρ s.nvars fun k => (w k : Int)) := by
    intro f mf
    obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
    have hk := List.mem_range.mp hk
    have vlt := hw k hk
    unfold W32 at vlt
    simp only [ranged32, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl
    · rw [holds_iff, ev_var, hval k]; omega
    · rw [holds_iff, ev_sub, ev_const, ev_var, hval k]; unfold W32i; omega
  refine ⟨?_, by simp [Sym.newWords], ?_, rfl, e, ?_⟩
  · cases use with
    | none =>
      exact Ca.then (Cb.then ⟨Agree.refl _ _, Nat.le_refl _, Holds.more Cb.holds _ hfh, WF.more Cb.wf _ hfb⟩)
    | some fk =>
      obtain ⟨f, keys⟩ := fk
      obtain ⟨hk, hv0⟩ := huse f keys rfl
      have e1 : keys.map (Key.val ctx s0 (extendFrom ρ s.nvars fun k => (w k : Int)) (madeN s m).2.list) =
          keys.map (Key.val ctx s0 ρ s.terms) :=
        List.map_congr_left fun k' mk' => Key.val_mono (hk k' mk') ag wf.words.table wf.words.atoms e
      have e2 : (madeN s m).1.map (fun i => Val.word (den (inpOf ctx s0) (extendFrom ρ s.nvars fun k => (w k : Int)) (madeN s m).2.list i)) =
          (List.range m).map fun k => Val.word (w k) := by
        apply List.ext_getElem
        · simp [len]
        · intro i h1 h2
          have hi : i < m := by simpa [len] using h1
          have := hden i hi
          rw [getD_of_lt _ _ (by omega)] at this
          simp only [List.getElem_map, List.getElem_range, this]
      exact Ca.then (Cb.then (Carried.more Cb.holds Cb.wf 0 (Agree.refl _ _) _ (Known.held f keys (madeN s m).1) hfb
        ⟨fun k' mk' => Key.wf_mono (show s.nvars ≤ s.nvars + m + 0 by omega) e.le (hk k' mk'), lt⟩ hfh
        (fun hpv => by obtain ⟨d, hd, hlen, hv⟩ := hv0 hpv; exact ⟨d, hd, hlen, by rw [e1, e2]; exact hv⟩)))
  · intro r mr
    have mr' : r ∈ (List.range m).map (fun k => Lin.var (s.nvars + k)) := mr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp mr'
    exact bounded_var (by have := List.mem_range.mp hk; omega)
  · intro k hk
    have : (s.newWords m use).1.getD k (Lin.const 0) = Lin.var (s.nvars + k) := by
      show ((List.range m).map fun k => Lin.var (s.nvars + k)).getD k (Lin.const 0) = _
      rw [getD_of_lt _ _ (by simpa using hk)]
      simp
    rw [this, ev_var, hval k]

theorem getD_append_left' {α : Type} (l l' : List α) (d : α) {k : Nat} (h : k < l.length) : (l ++ l').getD k d = l.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type} (l l' : List α) (d : α) {k : Nat} (h : l.length ≤ k) :
    (l ++ l').getD k d = l'.getD (k - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- What the lanes leave (`nameLanes`), where memory `mem` holds from the address `R` on the run as the
called function left it, and each lane's part of the run is the bytes its `ensures` says: the state is
carried; the rows speak of unknowns in use; and each row stands for the word of the run at its place
(`a`: where the first of these lanes begins in the run). -/
theorem nameLanes_sound {ctx : Ctx} {s0 st : State} {run : String} {env : List (String × WVal)} {env' : List (String × Val)}
    (mem : Nat → Byte) (R : Nat) (hpv : ctx.contract.preVals ctx.defs s0) :
    ∀ (es : List EnsureW) {ρ : Nat → Int} {s s' : Sym} {a : Nat} {rows : List Row},
      Holds ctx s0 ρ s st → WF ctx s → EnvDen ctx s0 ρ s.terms env env' → EnvOk s.nvars s.terms.length env →
      nameLanes ctx run env s a es = some (rows, s') →
      (∀ e ∈ es, ∀ a' m, e.part = some (a', m) → ∃ l : List Nat, Value ctx.defs env' e.value (.bytes l) ∧ l.length = m ∧
        ∀ k (h : k < l.length), (mem (R + a' + k)).val = l[k]) →
      ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ (∀ r ∈ rows, bounded s'.nvars r) ∧
        ∀ k, k < rows.length → ev ρ' (rows.getD k (Lin.const 0)) = (load mem (R + a + 4 * k) 4 : Nat)
  | [], ρ, s, s', a, rows, H, wf, hE, hO, h, hpost => by
    simp only [nameLanes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ρ, Carried.here H wf, (by intro r m; cases m), fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | e :: rest, ρ, s, s', a, rows, H, wf, hE, hO, h, hpost => by
    simp only [nameLanes] at h
    cases hp : e.part with
    | none => simp [hp] at h
    | some am =>
      obtain ⟨a', m⟩ := am
      simp only [hp] at h
      split at h
      next hcond =>
        obtain ⟨_, ha, hm4⟩ := hcond
        rw [ha] at hp
        obtain ⟨l, hval, hlen, hbytes⟩ := hpost e (List.mem_cons_self ..) a m hp
        cases hu : laneUse ctx s env e.value with
        | mk s1 use =>
          obtain ⟨ρ1, C1, t1, huse⟩ := laneUse_sound H wf hpv hE hO hval hu
          have et : s1.terms = s.terms := by show s1.tab.list = s.tab.list; rw [t1]
          -- the words the lane left
          have h256 : (256 : Nat) ^ 4 = 4294967296 := by decide
          have hw : ∀ k, k < m / 4 → load mem (R + a + 4 * k) 4 < W32 := fun k _ => by
            have := load_lt mem (R + a + 4 * k) 4
            rw [h256] at this
            unfold W32
            omega
          have huse' : ∀ f keys, use = some (f, keys) → (∀ k ∈ keys, k.wf s1.nvars s1.terms.length) ∧
              (ctx.contract.preVals ctx.defs s0 → ∃ d, findDef ctx.defs f = some d ∧ d.params.length = keys.length ∧
                Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ1 s1.terms))) d.body
                  (.list ((List.range (m / 4)).map fun k => Val.word (load mem (R + a + 4 * k) 4)))) := by
            intro f keys hfk
            obtain ⟨hk, d, nums, hd, hdl, hv, hlt, hb⟩ := huse f keys hfk
            obtain ⟨hl4, hlget⟩ := wordBytes_get nums l hb
            have hnl : nums.length = m / 4 := by omega
            have hrun : ∀ k, k < m / 4 → load mem (R + a + 4 * k) 4 = nums.getD k 0 := by
              intro k hk4
              apply load4_of_bytes _ _ _ (by have := hlt (nums.getD k 0) (getD_mem _ _ (by omega)); unfold W32 at this; omega)
              intro bb hbb
              have lt' : 4 * k + bb < l.length := by omega
              have := hbytes (4 * k + bb) lt'
              rw [← Nat.add_assoc] at this
              rw [this, ← getD_of_lt l 0 lt']
              exact hlget k (by omega) bb hbb
            have en : nums.map Val.word = (List.range (m / 4)).map fun k => Val.word (load mem (R + a + 4 * k) 4) := by
              apply List.ext_getElem
              · simp [hnl]
              · intro i h1 h2
                have hi : i < m / 4 := by simpa [hnl] using h1
                simp only [List.getElem_map, List.getElem_range]
                rw [hrun i hi, getD_of_lt nums 0 (by omega)]
            exact ⟨hk, fun _ => ⟨d, hd, hdl, by rw [← en]; exact hv⟩⟩
          obtain ⟨C2, len2, hb2, nv2, ext2, hev2⟩ :=
            newWords_carried C1.holds C1.wf (m / 4) (fun k => load mem (R + a + 4 * k) 4) hw use huse'
          cases hnw : s1.newWords (m / 4) use with
          | mk rows1 s2 =>
            simp only [hnw] at C2 len2 hb2 nv2 ext2 hev2
            simp only [hu, hnw] at h
            cases hrec : nameLanes ctx run env s2 (a + m) rest with
            | none => simp [hrec] at h
            | some pr =>
              obtain ⟨rows2, s3⟩ := pr
              simp only [hrec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have C12 := C1.then C2
              have hE2 : EnvDen ctx s0 _ s2.terms env env' :=
                EnvDen.mono C12.agree wf.words.table wf.words.atoms (et ▸ ext2) hE hO
              have hO2 : EnvOk s2.nvars s2.terms.length env :=
                hO.mono C12.mono (by have := ext2.le; rw [et] at this; exact this)
              obtain ⟨ρ3, C3, hb3, hev3⟩ := nameLanes_sound mem R hpv rest C2.holds C2.wf hE2 hO2 hrec
                (fun e' me' => hpost e' (List.mem_cons_of_mem _ me'))
              refine ⟨ρ3, C12.then C3, ?_, ?_⟩
              · intro r mr
                rcases List.mem_append.mp mr with m1 | m2
                · exact bounded_mono (by rw [← nv2]; exact C3.mono) (hb2 r m1)
                · exact hb3 r m2
              · intro k hk
                rw [List.length_append] at hk
                by_cases hk1 : k < rows1.length
                · rw [getD_append_left' _ _ _ hk1]
                  have hbk : bounded s2.nvars (rows1.getD k (Lin.const 0)) := by
                    rw [nv2]; exact hb2 _ (getD_mem rows1 _ hk1)
                  rw [← ev_agree hbk C3.agree, hev2 k (by omega)]
                · have eaddr : R + (a + m) + 4 * (k - rows1.length) = R + a + 4 * k := by omega
                  rw [getD_append_right' _ _ _ (by omega), hev3 (k - rows1.length) (by omega), eaddr]
      next => simp at h

private theorem nameLanes_vacuous {ctx : Ctx} {s0 st : State} {run : String} {env : List (String × WVal)}
    (mem : Nat → Byte) (R : Nat) (nhpv : ¬ ctx.contract.preVals ctx.defs s0) :
    ∀ (es : List EnsureW) {ρ : Nat → Int} {s s' : Sym} {a : Nat} {rows : List Row},
      Holds ctx s0 ρ s st → WF ctx s → EnvOk s.nvars s.terms.length env →
      nameLanes ctx run env s a es = some (rows, s') →
      ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ (∀ r ∈ rows, bounded s'.nvars r) ∧
        ∀ k, k < rows.length → ev ρ' (rows.getD k (Lin.const 0)) = (load mem (R + a + 4 * k) 4 : Nat)
  | [], ρ, s, s', _, rows, H, wf, _, h => by
    simp only [nameLanes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ρ, Carried.here H wf, (by intro r m; cases m), fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | e :: rest, ρ, s, s', a, rows, H, wf, hO, h => by
    simp only [nameLanes] at h
    cases hp : e.part with
    | none => simp [hp] at h
    | some am =>
      obtain ⟨a', m⟩ := am; simp only [hp] at h
      split at h
      next hcond =>
        obtain ⟨_, _, hm4⟩ := hcond
        cases hu : laneUse ctx s env e.value with
        | mk s1 use =>
          obtain ⟨ρ1, C1, t1, huse⟩ := laneUse_carried_vacuous nhpv H wf hO hu
          have et : s1.terms = s.terms := by show s1.tab.list = s.tab.list; rw [t1]
          have h256 : (256 : Nat) ^ 4 = 4294967296 := by decide
          have hw : ∀ k, k < m / 4 → load mem (R + a + 4 * k) 4 < W32 := fun k _ => by
            have := load_lt mem (R + a + 4 * k) 4; rw [h256] at this; unfold W32; omega
          obtain ⟨C2, len2, hb2, nv2, ext2, hev2⟩ :=
            newWords_carried C1.holds C1.wf (m / 4) (fun k => load mem (R + a + 4 * k) 4) hw use
              (fun f keys hfk => ⟨huse f keys hfk, fun hpv => (nhpv hpv).elim⟩)
          cases hnw : s1.newWords (m / 4) use with
          | mk rows1 s2 =>
            simp only [hnw] at C2 len2 hb2 nv2 ext2 hev2
            simp only [hu, hnw] at h
            cases hrec : nameLanes ctx run env s2 (a + m) rest with
            | none => simp [hrec] at h
            | some pr =>
              obtain ⟨rows2, s3⟩ := pr
              simp only [hrec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have C12 := C1.then C2
              have hO2 : EnvOk s2.nvars s2.terms.length env :=
                hO.mono C12.mono (by have := ext2.le; rw [et] at this; exact this)
              obtain ⟨ρ3, C3, hb3, hev3⟩ := nameLanes_vacuous mem R nhpv rest C2.holds C2.wf hO2 hrec
              refine ⟨ρ3, C12.then C3, ?_, ?_⟩
              · intro r mr
                rcases List.mem_append.mp mr with m1 | m2
                · exact bounded_mono (by rw [← nv2]; exact C3.mono) (hb2 r m1)
                · exact hb3 r m2
              · intro k hk
                rw [List.length_append] at hk
                by_cases hk1 : k < rows1.length
                · rw [getD_append_left' _ _ _ hk1]
                  have hbk : bounded s2.nvars (rows1.getD k (Lin.const 0)) := by
                    rw [nv2]; exact hb2 _ (getD_mem rows1 _ hk1)
                  rw [← ev_agree hbk C3.agree, hev2 k (by omega)]
                · have eaddr : R + (a + m) + 4 * (k - rows1.length) = R + a + 4 * k := by omega
                  rw [getD_append_right' _ _ _ (by omega), hev3 (k - rows1.length) (by omega), eaddr]
      next => simp at h

/-! ## The call -/

/-- What a table of a contract is: a run of a fixed count that `lanes` names, with the register of the
count of blocks; it holds an eighth of its bytes as addresses. -/
theorem tableAt_spec {c : Contract} {j : Nat} {x : String} {r count l : Nat} (h : c.tableAt j = some (x, r, count, l)) :
    ∃ n y, c.fixeds[j]? = some (x, r, n) ∧ c.lanes.lookup x = some y ∧ c.regOf y = some l ∧ count = n / 8 := by
  unfold Contract.tableAt at h
  cases hf : c.fixeds[j]? with
  | none => simp [hf] at h
  | some f =>
    obtain ⟨x', r', n'⟩ := f
    simp only [hf] at h
    cases hl : c.lanes.lookup x' with
    | none => simp [hl] at h
    | some y =>
      simp only [hl] at h
      cases hr : c.regOf y with
      | none => simp [hr] at h
      | some l' =>
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨e1, e2, e3, e4⟩ := h
        exact ⟨n', y, by rw [← e1, ← e2], by rw [← e1]; exact hl, by rw [← e4]; exact hr, e3.symm⟩

/-- A lane's blocks, by where they lie: in memory below 2^64 and apart from this function's frame and the
address it returns to, or in the frame at or above the stack pointer and apart from the part written; and
this function may read them. -/
theorem LaneAt.where_ {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s : Sym} {P nb : Nat} {cw : Int} {nout : Nat}
    {sp : Int} (hsp : s.sp = some sp) (h : LaneAt ctx s0 s P nb cw nout) :
    ((P + 64 * nb ≤ M64 ∧ (P + 64 * nb ≤ s0.reg RSP - ctx.contract.stackAt s0 ∨ s0.reg RSP + ctx.contract.slot ≤ P)) ∨
     (∃ o : Int, (P : Int) = s0.reg RSP + o ∧ sp ≤ o ∧ o + 64 * (nb : Int) ≤ 0 ∧
        (o + 64 * (nb : Int) ≤ cw ∨ cw + (nout : Int) ≤ o))) ∧
    (-(ctx.contract.stackAt s0 : Int) ≤ sp → ∀ a, P ≤ a → a < P + 64 * nb → (ctx.contract.perm ctx.pieces s0).read a = true) := by
  have hstack := E.stackAt
  rcases h with ⟨x0, b, n0, c, hm, hP, hle⟩ | ⟨b, len, c, hm, hP, hle⟩ | ⟨o, sp', hsp', hP, h1, h2, h3⟩
  · obtain ⟨f1, f2, f3, f4⟩ := E.fixedAt hm
    refine ⟨Or.inl ⟨by omega, by omega⟩, fun _ a ha1 ha2 => ?_⟩
    simp only [Contract.perm, Contract.inFixed, Bool.or_eq_true]
    left; left; left; right; left
    exact List.any_eq_true.mpr ⟨(x0, b, n0), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
  · obtain ⟨r1, r2⟩ := E.regionAt hm
    refine ⟨Or.inl ⟨by omega, by omega⟩, fun _ a ha1 ha2 => ?_⟩
    simp only [Contract.perm, Bool.or_eq_true]
    left; left; left; left; right
    exact List.any_eq_true.mpr ⟨(b, len), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
  · have esp : sp' = sp := Option.some.inj (hsp'.symm.trans hsp)
    subst esp
    refine ⟨Or.inr ⟨o, hP, h1, h2, h3⟩, fun hlow a ha1 ha2 => ?_⟩
    simp only [Contract.perm, Bool.or_eq_true]
    left; left; left; left; left; left
    simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]
    omega

/-- What `symCallL'` has looked up, where it lets a call through. -/
theorem symCallL'_spec {ctx : Ctx} {s s' : Sym} {c : Contract} {items rest : Items} (h : symCallL' ctx s c items = .ok (s', rest)) :
    ∃ (sp : Int) (run : String) (r n : Nat) (tx : String) (tr count l : Nat) (nb cw ct : Int) (lanes : List WVal) (T : Tab)
      (env : List (String × WVal)) (rows : List Row) (s1 : Sym),
      s.sp = some sp ∧
      (c.inouts = [] ∧ c.regions = []) ∧
      (∀ x k, (x, k) ∈ c.atLeast → ∀ r', c.regOf x = some r' → plain s.facts (Lin.sub (s.reg r') (Lin.const (k : Int))) = true) ∧
      c.outs = [(run, r, n)] ∧ c.tables = [(tx, tr, count, l)] ∧
      Lin.isConst (s.reg l) = some nb ∧ frameAt s r = some cw ∧ frameAt s tr = some ct ∧
      (0 ≤ nb ∧ sp ≤ cw ∧ cw + (n : Int) ≤ 0 ∧ n % 8 = 0 ∧ sp ≤ ct ∧ ct + 8 * (count : Int) ≤ 0 ∧
        (ct + 8 * (count : Int) ≤ cw ∨ cw + (n : Int) ≤ ct)) ∧
      (∀ x r' n', (x, r', n') ∈ c.fixeds → ∀ cf, frameAt s r' = some cf → cf + (n' : Int) ≤ cw ∨ cw + (n : Int) ≤ cf) ∧
      tableLanes ctx s ct nb.toNat cw n count 0 (termsOf intern (partNodes ctx s c.args c.argRegs) s.tab).2 = some (lanes, T) ∧
      calleeL ctx { s with tab := T } tx tr (8 * count) c.args c.argRegs = some env ∧
      nameLanes ctx run ((tx, WVal.list lanes) :: env) { s with tab := T } 0 c.ensuresW = some (rows, s1) ∧
      rows.length * 4 = n ∧
      (∀ x bd, (x, bd) ∈ c.bounds → ∀ r', c.regOf x = some r' →
        ∃ items' res, entail s.facts (Lin.sub (Lin.const ((bd : Int) - 1)) (s.reg r')) items' = .ok res) ∧
      s' = Sym.afterCallL c s1 sp cw n rows := by
  cases hsp : s.sp with
  | none => simp only [symCallL', hsp] at h; exact (refuse_ok h).elim
  | some sp =>
    simp only [symCallL', hsp] at h
    · split at h
      next => exact (refuse_ok h).elim
      next hshape =>
        have hs : c.inouts = [] ∧ c.ensures = [] ∧ c.regions = [] ∧
            c.returns = none ∧ c.result = none := by
          simpa [List.isEmpty_iff, Option.isNone_iff_eq_none, and_assoc] using hshape
        obtain ⟨hinouts, -, hregions, -, -⟩ := hs
        split at h
        next => exact (refuse_ok h).elim
        next hat =>
          have hat' : (c.atLeast.all fun (xk : String × Nat) =>
              match c.regOf xk.1 with
              | some rb => plain s.facts (Lin.sub (s.reg rb) (Lin.const xk.2))
              | none => true) = true := by
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hat; exact hat
          obtain ⟨run, r, n, houts⟩ : ∃ run r n, c.outs = [(run, r, n)] := by
            rcases ho : c.outs with _ | ⟨⟨run0, r, n⟩, _ | ⟨o2, omore⟩⟩
            · simp only [ho] at h; exact (refuse_ok h).elim
            · exact ⟨_, _, _, rfl⟩
            · simp only [ho] at h; exact (refuse_ok h).elim
          simp only [houts] at h
          obtain ⟨tx, tr, count, l, htab⟩ : ∃ tx tr count l, c.tables = [(tx, tr, count, l)] := by
            rcases ht : c.tables with _ | ⟨⟨tx, tr, count, l⟩, _ | ⟨t2, tmore⟩⟩
            · simp only [ht] at h; exact (refuse_ok h).elim
            · exact ⟨_, _, _, _, rfl⟩
            · simp only [ht] at h; exact (refuse_ok h).elim
          simp only [htab] at h
          cases hnb : Lin.isConst (s.reg l) with
          | none => simp only [hnb] at h; exact (refuse_ok h).elim
          | some nb =>
          cases hcw : frameAt s r with
          | none => simp only [hnb, hcw] at h; exact (refuse_ok h).elim
          | some cw =>
          cases hct : frameAt s tr with
          | none => simp only [hnb, hcw, hct] at h; exact (refuse_ok h).elim
          | some ct =>
          simp only [hnb, hcw, hct] at h
          split at h
          next => exact (refuse_ok h).elim
          next hfr =>
          have hfr2 := hfr
          simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hfr2
          obtain ⟨⟨⟨⟨⟨⟨⟨hnb0, hcw1⟩, hcw2⟩, hn8⟩, hct1⟩, hct2⟩, hapart⟩, hfixall⟩ := hfr2
          cases hlanes : tableLanes ctx s ct nb.toNat cw n count 0 (termsOf intern (partNodes ctx s c.args c.argRegs) s.tab).2 with
          | none => simp only [hlanes] at h; exact (refuse_ok h).elim
          | some pr =>
          obtain ⟨lanes, T⟩ := pr
          simp only [hlanes] at h
          cases hcal : calleeL ctx { s with tab := T } tx tr (8 * count) c.args c.argRegs with
          | none => simp only [hcal] at h; exact (refuse_ok h).elim
          | some env =>
          simp only [hcal] at h
          cases hnl : nameLanes ctx run ((tx, WVal.list lanes) :: env) { s with tab := T } 0 c.ensuresW with
          | none => simp only [hnl] at h; exact (refuse_ok h).elim
          | some pr2 =>
          obtain ⟨rows, s1⟩ := pr2
          simp only [hnl] at h
          split at h
          next => exact (refuse_ok h).elim
          next hrl =>
          have hrl' : rows.length * 4 = n := by simpa using hrl
          obtain ⟨⟨u, items1⟩, r1, hbounds, h⟩ := V.bind_ok h
          have hfin := V.pure_ok h
          injection hfin with hs' _
          exact ⟨sp, run, r, n, tx, tr, count, l, nb, cw, ct, lanes, T, env, rows, s1, rfl, ⟨hinouts, hregions⟩,
            (fun x k m r' hr' => by
              have hall := List.all_eq_true.mp hat' (x, k) m
              simp only [hr'] at hall
              exact hall),
            houts, htab, hnb, hcw, hct, ⟨hnb0, hcw1, hcw2, hn8, hct1, hct2, hapart⟩,
            (fun x r' n' m cf hcf => by
              have ha := List.all_eq_true.mp hfixall (x, r', n') m
              simp only [hcf, Bool.or_eq_true, decide_eq_true_eq] at ha
              exact ha),
            hlanes, hcal, hnl, hrl',
            (fun x bd m r' hr' => by
              obtain ⟨items', res, he⟩ := each_mem hbounds (x, bd) m
              simp only [hr'] at he
              exact ⟨items', res, he⟩),
            hs'⟩

/-- The state the called function starts in is one its contract's caller has seen to (the facts are those
`symCallL'` has looked up, and what they say of the machine at the call). -/
theorem symCallL_pre {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s : Sym} {c : Contract} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (q : Program) (hq : q.fits) (i : Instr) (F : Fits ctx st i c) (hex : CallExtra ctx s0 st c (afterCall p q i st))
    {sp cw ct nb : Int} {run tx : String} {r n tr count l : Nat} {T : Tab}
    (hsp : s.sp = some sp) (hg : sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot - (c.stackAt (afterCall p q i st) : Int))
    (hregions' : c.regions = [])
    (hatL : ∀ x k, (x, k) ∈ c.atLeast → ∀ r', c.regOf x = some r' →
      plain s.facts (Lin.sub (s.reg r') (Lin.const (k : Int))) = true)
    (houts : c.outs = [(run, r, n)]) (htab : c.tables = [(tx, tr, count, l)])
    (hcw1 : sp ≤ cw) (hcw2 : cw + (n : Int) ≤ 0) (hct1 : sp ≤ ct) (hct2 : ct + 8 * (count : Int) ≤ 0)
    (hapart : ct + 8 * (count : Int) ≤ cw ∨ cw + (n : Int) ≤ ct)
    (hfixApart : ∀ x r' n', (x, r', n') ∈ c.fixeds → ∀ cf, frameAt s r' = some cf → cf + (n' : Int) ≤ cw ∨ cw + (n : Int) ≤ cf)
    (hbounds : ∀ x bd, (x, bd) ∈ c.bounds → ∀ r', c.regOf x = some r' →
      ∃ items' res, entail s.facts (Lin.sub (Lin.const ((bd : Int) - 1)) (s.reg r')) items' = .ok res)
    (hrsp : (st.reg RSP : Int) = s0.reg RSP + sp)
    (s1rsp : (afterCall p q i st).reg RSP = st.reg RSP - c.slot)
    (s1reg : ∀ r, CallKeeps r → (afterCall p q i st).reg r = st.reg r)
    (s1r : (afterCall p q i st).reg r = ((s0.reg RSP : Int) + cw).toNat)
    (s1t : (afterCall p q i st).reg tr = ((s0.reg RSP : Int) + ct).toNat)
    (s1l : (afterCall p q i st).reg l = nb.toNat)
    (HT : Holds ctx s0 ρ { s with tab := T } st) (wfT : WF ctx { s with tab := T })
    (hfixs : ∀ x r n, (x, r, n) ∈ fixedsIn c.args c.argRegs →
      (x = tx ∧ r = tr ∧ n = 8 * count) ∨
      (x ≠ tx ∧ ((∃ j b cst, fixedPart ctx { s with tab := T } r n = some (j, b, cst)) ∨
        (∃ cf fids, frameRun { s with tab := T } r n = some (cf, fids)))))
    (hptr : ∀ j, j < count → lanePtr (afterCall p q i st) tr j =
      load st.mem ((s0.reg RSP : Int) + (ct + 8 * (j : Int))).toNat 8)
    (atLanes : ∀ j, j < count →
      LaneAt ctx s0 s (load st.mem ((s0.reg RSP : Int) + (ct + 8 * ((j : Nat) : Int))).toNat 8) nb.toNat cw n)
    (hva : c.valArrays = []) :
    c.pre q (afterCall p q i st) := by
  have hstack := E.stackAt
  have habove := E.above
  have hsmallsp := H.small RSP
  have hslot := F.slot
  have h8 : c.slot ≤ st.reg RSP := by omega
  refine ⟨afterCall_rip p q i st, ?_, ?_, ?_, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, afterCall_aligned F p q, hex.preLines,
    fun _ _ _ _ _ m => by rw [hva] at m; cases m⟩
  · exact afterCall_small F.link H.small
  · rw [s1rsp]; omega
  · rw [s1rsp]; omega
  · intro r' l' m; rw [hregions'] at m; cases m
  · intro x' r' n' m
    rw [houts] at m
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m
    obtain ⟨_, e1, e2⟩ := m
    rw [e1, e2]
    refine ⟨by rw [s1r]; omega, by rw [s1r, s1rsp]; omega, ?_⟩
    intro r'' l'' m'; rw [hregions'] at m'; cases m'
  · rw [houts]; exact List.pairwise_singleton _ _
  · intro x' r' n' m
    rcases hfixs x' r' n' m with ⟨_, er, en⟩ | ⟨_, ⟨j', b', cst, hf⟩ | ⟨cf, fids, hfrun⟩⟩
    · rw [er, en]
      refine ⟨by rw [s1t]; omega, by rw [s1t, s1rsp]; omega, ?_⟩
      intro x'' r'' n'' m''
      rw [houts] at m''
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
      obtain ⟨_, e1, e2⟩ := m''
      rw [e1, e2, s1t, s1r]
      omega
    · have ra := fixedsIn_mem c.args c.argRegs x' r' n' m
      obtain ⟨g3, -, f1, f2, f3, f4, -⟩ := fixedPart_sound E HT (F.arg ra).1 hf
      have rne' := (F.arg ra).2
      refine ⟨by rw [s1reg r' rne', g3]; omega, by rw [s1reg r' rne', g3, s1rsp]; omega, ?_⟩
      intro x'' r'' n'' m''
      rw [houts] at m''
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
      obtain ⟨_, e1, e2⟩ := m''
      rw [e1, e2, s1reg r' rne', g3, s1r]
      omega
    · have ra := fixedsIn_mem c.args c.argRegs x' r' n' m
      obtain ⟨⟨sp', hsp', hle⟩, hn0, _, hreg', _, _⟩ := frameRun_sound E HT wfT (F.arg ra).1 hfrun
      have esp' : sp' = sp := Option.some.inj (hsp'.symm.trans hsp)
      subst esp'
      have hcf : frameAt s r' = some cf := show frameAt { s with tab := T } r' = some cf from frameRun_at hfrun
      have hfa := hfixApart x' r' n' m cf hcf
      have rne' := (F.arg ra).2
      refine ⟨by rw [s1reg r' rne']; omega, by rw [s1reg r' rne', s1rsp]; omega, ?_⟩
      intro x'' r'' n'' m''
      rw [houts] at m''
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
      obtain ⟨_, e1, e2⟩ := m''
      rw [e1, e2, s1reg r' rne', s1r]
      omega
  · intro x' bd m r' hr'
    obtain ⟨items', res, he⟩ := hbounds x' bd m r' hr'
    have hge := entail_sound he ρ H.facts
    rw [ev_sub, ev_const] at hge
    have ra := regOfIn_mem x' c.args c.argRegs r' hr'
    have hreg' := H.reg r' (F.arg ra).1
    rw [s1reg r' (F.arg ra).2]
    omega
  · exact hex.mbounds
  · -- the blocks each address of the table points to
    intro j' x' r' count' l' m' i' hi'
    obtain ⟨nt', y', hfj', _, _, _⟩ := tableAt_spec m'
    have mm : (x', r', count', l') ∈ c.tables :=
      List.mem_filterMap.mpr ⟨j', List.mem_range.mpr (List.getElem?_eq_some_iff.mp hfj').1, m'⟩
    rw [htab] at mm
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at mm
    obtain ⟨_, e2, e3, e4⟩ := mm
    rw [e3] at hi'
    rw [e2, e4, hptr i' hi', s1l, s1rsp]
    rcases (LaneAt.where_ E hsp (atLanes i' hi')).1 with ⟨a1, a2⟩ | ⟨o, hP, o1, o2, o3⟩
    · refine ⟨a1, by omega, ?_⟩
      intro x'' r'' n'' m''
      rw [houts] at m''
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
      obtain ⟨_, e1', e2'⟩ := m''
      rw [e1', e2', s1r]
      omega
    · refine ⟨by omega, by omega, ?_⟩
      intro x'' r'' n'' m''
      rw [houts] at m''
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
      obtain ⟨_, e1', e2'⟩ := m''
      rw [e1', e2', s1r]
      omega
  · -- a number the contract asks to be no less than another
    intro x' k' m' r' hr'
    have hall := hatL x' k' m' r' hr'
    have h0 : 0 ≤ ev ρ (Lin.sub (s.reg r') (Lin.const (k' : Int))) := plain_sound hall ρ H.facts
    rw [ev_sub, ev_const] at h0
    have ra := regOfIn_mem x' c.args c.argRegs r' hr'
    have hreg' := H.reg r' (F.arg ra).1
    rw [s1reg r' (F.arg ra).2]
    omega

/-- **A call, by contract, of a function that is given a table of addresses (`symCallL'`).** -/
theorem symCallL'_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallL' ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) (i : Instr) (F : Fits ctx st i c) (hret : p.base + i.next < M64)
    (hex : CallExtra ctx s0 st c (afterCall p q i st)) (hva : c.valArrays = []) :
    c.slot ≤ st.reg RSP ∧ allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  obtain ⟨sp, run, r, n, tx, tr, count, l, nb, cw, ct, lanes, T, env, rows, s1, hsp, ⟨hinouts, hregions⟩, hatL,
    houts, htab, hnb, hcw, hct, ⟨hnb0, hcw1, hcw2, hn8, hct1, hct2, hapart⟩, hfixApart, hlanes, hcal, hnl, hrl', hbounds, hs'⟩ := symCallL'_spec h
  subst hs'
  -- the machine at the call
  have esp := ev_isConst (ρ := ρ) hsp
  simp only [ev_sub, ev_var] at esp
  have h1 := H.reg RSP ctx.rsp_lt
  have h2 := H.entry RSP ctx.rsp_lt
  have hrsp : (st.reg RSP : Int) = s0.reg RSP + sp := by omega
  have hg : sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot - (c.stackAt (afterCall p q i st) : Int) := by
    have := hex.stack; omega
  have hstack := E.stackAt
  have habove := E.above
  have hsmallsp := H.small RSP
  have hslot := F.slot
  have h8 : c.slot ≤ st.reg RSP := by omega
  have s1rsp : (afterCall p q i st).reg RSP = st.reg RSP - c.slot := afterCall_rsp F.link
  have s1reg : ∀ r, CallKeeps r → (afterCall p q i st).reg r = st.reg r := fun r hr => afterCall_reg F.link hr
  have s1mem : ∀ x, x < st.reg RSP - c.slot ∨ st.reg RSP ≤ x → (afterCall p q i st).mem x = st.mem x :=
    fun x hx => afterCall_mem F.link h8 hx
  -- the run handed over to be written: a part of this function's frame
  have rmem : (run, r, n) ∈ c.outs := by rw [houts]; exact List.mem_cons_self ..
  have rarg : r ∈ c.argRegs := outsIn_mem c.args c.argRegs run r n rmem
  obtain ⟨r16, rne⟩ := F.arg rarg
  have ecw := ev_isConst (ρ := ρ) hcw
  simp only [ev_sub, ev_var] at ecw
  have hregr := H.reg r r16
  have s1r : (afterCall p q i st).reg r = ((s0.reg RSP : Int) + cw).toNat := by rw [s1reg r rne]; omega
  -- the table: a run of a fixed count of the called function, a part of this function's frame
  have tmem : (tx, tr, count, l) ∈ c.tables := by rw [htab]; exact List.mem_cons_self ..
  obtain ⟨j, hj, htj⟩ := List.mem_filterMap.mp (show (tx, tr, count, l) ∈ (List.range c.fixeds.length).filterMap c.tableAt from tmem)
  obtain ⟨nt, y, hfj, hly, hry, hcount⟩ := tableAt_spec htj
  have tfix : (tx, tr, nt) ∈ c.fixeds := List.mem_of_getElem? hfj
  have targ : tr ∈ c.argRegs := fixedsIn_mem c.args c.argRegs tx tr nt tfix
  have larg : l ∈ c.argRegs := regOfIn_mem y c.args c.argRegs l hry
  obtain ⟨t16, tne⟩ := F.arg targ
  obtain ⟨l16, lne⟩ := F.arg larg
  have ect := ev_isConst (ρ := ρ) hct
  simp only [ev_sub, ev_var] at ect
  have hregt := H.reg tr t16
  have s1t : (afterCall p q i st).reg tr = ((s0.reg RSP : Int) + ct).toNat := by rw [s1reg tr tne]; omega
  have enb := ev_isConst (ρ := ρ) hnb
  have hregl := H.reg l l16
  have s1l : (afterCall p q i st).reg l = nb.toNat := by rw [s1reg l lne]; omega
  have hregions' : c.regions = [] := hregions
  -- the table of terms with the words of the parts handed over and of the lanes
  obtain ⟨extT0, okT0⟩ := inputs_table wf (partNodes ctx s c.args c.argRegs) (partNodes_inputs c.args c.argRegs)
  obtain ⟨extL, okL, okLanes, dLanes, atLanes⟩ := tableLanes_sound E H wf count 0 extT0 okT0 hlanes
  simp only [Nat.zero_add] at dLanes atLanes
  have extT : Ext s.terms T.list := extT0.trans extL
  have CT := Carried.terms H wf extT okL
  have HT := CT.holds
  have wfT := CT.wf
  -- the lanes: where the table's cells point
  have hptr : ∀ j, j < count → lanePtr (afterCall p q i st) tr j =
      load st.mem ((s0.reg RSP : Int) + (ct + 8 * (j : Int))).toNat 8 := by
    intro j hj
    unfold lanePtr
    rw [s1t, show ((s0.reg RSP : Int) + (ct + 8 * (j : Int))).toNat = ((s0.reg RSP : Int) + ct).toNat + 8 * j by omega]
    exact load_congr _ _ _ _ (fun x hx1 hx2 => s1mem x (Or.inr (by omega)))
  have hlanemem : ∀ j, j < count → ∀ x, load st.mem ((s0.reg RSP : Int) + (ct + 8 * (j : Int))).toNat 8 ≤ x →
      x < load st.mem ((s0.reg RSP : Int) + (ct + 8 * (j : Int))).toNat 8 + 64 * nb.toNat →
      (afterCall p q i st).mem x = st.mem x := by
    intro j hj x hx1 hx2
    rcases (LaneAt.where_ E hsp (atLanes j hj)).1 with ⟨a1, a2⟩ | ⟨o, hP, o1, o2, o3⟩
    · exact s1mem x (by omega)
    · exact s1mem x (Or.inr (by omega))
  -- each part handed over to be read lies in one of this function's runs given to read
  have hfixmem : ∀ r' n' j b' cst, r' ∈ c.argRegs → fixedPart ctx { s with tab := T } r' n' = some (j, b', cst) →
      ∀ k, k < n' → (afterCall p q i st).mem (st.reg r' + k) = s0.mem (s0.reg b' + cst + k) ∧ (s0.mem (s0.reg b' + cst + k)).val < 256 := by
    intro r' n' j b' cst ra hf k hk
    obtain ⟨g3, -, f1, f2, f3, f4, -⟩ := fixedPart_sound E HT (F.arg ra).1 hf
    refine ⟨?_, f3 k hk⟩
    rw [g3, s1mem _ (by omega)]
    exact H.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
      (by
        unfold Contract.inOut
        rw [List.any_eq_false]
        intro ⟨x'', r'', n''⟩ hm
        have := f4 x'' r'' n'' hm
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega)
  have hframe : ∀ r' n' cf fids, r' ∈ c.argRegs → frameRun { s with tab := T } r' n' = some (cf, fids) →
      (List.range n').map (fun k => Val.int ((afterCall p q i st).mem ((afterCall p q i st).reg r' + k))) =
        wordBytes (fids.map (den (inpOf ctx s0) ρ T.list)) := by
    intro r' n' cf fids ra hfrun
    obtain ⟨⟨sp', hsp', hle⟩, hn0, hn8', hreg', hlen, hwords⟩ := frameRun_sound E HT wfT (F.arg ra).1 hfrun
    have esp' : sp' = sp := Option.some.inj (hsp'.symm.trans hsp)
    subst esp'
    have hA : (afterCall p q i st).reg r' = ((s0.reg RSP : Int) + cf).toNat := by
      rw [s1reg r' (F.arg ra).2]; omega
    have := wordBytes_range (afterCall p q i st).mem (fids.map (den (inpOf ctx s0) ρ T.list)) ((afterCall p q i st).reg r')
      (fun j hj bb hbb => by
        have hj' : j < fids.length := by simpa using hj
        obtain ⟨_, hlow, hld⟩ := hwords j (by omega)
        have hb : (st.mem (((s0.reg RSP : Int) + cf).toNat + 4 * j + bb)).val =
            den (inpOf ctx s0) ρ T.list (fids.getD j 0) / 256 ^ bb % 256 := by
          rw [← hld]
          exact (load4_byteAt st.mem _ bb hbb (fun _ _ => Fin.isLt _)).symm
        rw [hA, s1mem _ (by omega), hb, getD_of_lt _ _ hj, getD_of_lt _ _ hj', List.getElem_map])
    rw [List.length_map, hlen, show 4 * (n' / 4) = n' by omega] at this
    exact this
  have hfixs := calleeL_fixeds c.args c.argRegs hcal
  have hnt : nt = 8 * count := by
    rcases hfixs tx tr nt tfix with ⟨_, _, e⟩ | ⟨ne, _⟩
    · exact e
    · exact absurd rfl ne
  -- the names of the called function
  have henvW : c.envW (afterCall p q i st) =
      (tx, Val.list ((List.range count).map fun i' =>
        laneBlocks (afterCall p q i st).mem (lanePtr (afterCall p q i st) tr i') ((afterCall p q i st).reg l))) ::
        envWIn c (afterCall p q i st) c.args c.argRegs := by
    simp [Contract.envW, Contract.lanesEnv, htab]
  have elanes : (List.range count).map (fun i' =>
        laneBlocks (afterCall p q i st).mem (lanePtr (afterCall p q i st) tr i') ((afterCall p q i st).reg l)) =
      (List.range count).map fun (j : Nat) =>
        laneBlocks st.mem (load st.mem ((s0.reg RSP : Int) + (ct + 8 * ((j : Nat) : Int))).toNat 8) nb.toNat :=
    List.map_congr_left fun j hj => by
      have hj' := List.mem_range.mp hj
      rw [hptr j hj', s1l]
      exact laneBlocks_congr _ _ _ _ (hlanemem j hj')
  have henv : EnvDen ctx s0 ρ T.list ((tx, WVal.list lanes) :: env)
      ((tx, Val.list ((List.range count).map fun i' =>
        laneBlocks (afterCall p q i st).mem (lanePtr (afterCall p q i st) tr i') ((afterCall p q i st).reg l))) ::
        envWIn c (afterCall p q i st) c.args c.argRegs) := by
    refine ⟨rfl, ?_, calleeL_sound (T := T.list) HT c F.regs (fun r' m => s1reg r' (F.arg m).2) hfixmem hframe c.args c.argRegs (fun _ m => m) hcal⟩
    rw [elanes]
    exact dLanes
  have hokenv : EnvOk s.nvars T.list.length ((tx, WVal.list lanes) :: env) :=
    EnvOk.cons (by simp only [WVal.ok]; exact okLanes) (calleeL_ok wfT c.args c.argRegs (fun r' m => (F.arg m).1) hcal)
  have hpre : c.pre q (afterCall p q i st) :=
    symCallL_pre E H wf q hq i F hex hsp hg hregions' hatL houts htab hcw1 hcw2 hct1 hct2 hapart hfixApart hbounds hrsp s1rsp s1reg
      s1r s1t s1l HT wfT hfixs hptr atLanes hva
  have hread : ∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true := by
    intro a ha
    rw [perm_read_split, Bool.or_eq_true] at ha
    refine ha.elim (fun ha => ?_) (fun ha => read_pieces H p q i ha)
    simp only [Contract.perm, inPieces_nil, Bool.or_false, Bool.or_eq_true] at ha
    rcases ha with ((((ha | ha) | ha) | ha) | ha) | ha
    · simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha
      simp only [Contract.perm, Bool.or_eq_true]
      left; left; left; left; left; left
      simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]
      omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha
      simp only [Contract.perm, Bool.or_eq_true]
      left; left; left; left; left; left
      simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]
      omega
    · rw [hregions'] at ha; simp at ha
    · simp only [Contract.inFixed, Bool.or_eq_true] at ha
      rcases ha with ha | ha
      · obtain ⟨⟨x', r', n'⟩, m, hin⟩ := List.any_eq_true.mp ha
        rcases hfixs x' r' n' m with ⟨_, er, en⟩ | ⟨_, ⟨j', b', cst, hf⟩ | ⟨cf, fids, hfrun⟩⟩
        · rw [er, en] at hin
          simp only [Bool.and_eq_true, decide_eq_true_eq, s1t] at hin
          simp only [Contract.perm, Bool.or_eq_true]
          left; left; left; left; left; left
          simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]
          omega
        · have ra := fixedsIn_mem c.args c.argRegs x' r' n' m
          obtain ⟨g3, -, -, -, -, -, fw⟩ := fixedPart_sound E HT (F.arg ra).1 hf
          simp only [Bool.and_eq_true, decide_eq_true_eq, s1reg r' (F.arg ra).2, g3] at hin
          rcases fw with ⟨x0, n0, hm0, hle⟩ | ⟨l0, hm0, hle⟩
          · simp only [Contract.perm, Contract.inFixed, Bool.or_eq_true]
            left; left; left; right; left
            exact List.any_eq_true.mpr ⟨(x0, b', n0), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
          · simp only [Contract.perm, Bool.or_eq_true]
            left; left; left; left; right
            exact List.any_eq_true.mpr ⟨(b', l0), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        · have ra := fixedsIn_mem c.args c.argRegs x' r' n' m
          obtain ⟨⟨sp', hsp', hle⟩, hn0, _, hreg', _, _⟩ := frameRun_sound E HT wfT (F.arg ra).1 hfrun
          have esp' : sp' = sp := Option.some.inj (hsp'.symm.trans hsp)
          subst esp'
          simp only [Bool.and_eq_true, decide_eq_true_eq, s1reg r' (F.arg ra).2] at hin
          simp only [Contract.perm, Bool.or_eq_true]
          left; left; left; left; left; left
          simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]
          omega
      · rw [hinouts] at ha; simp at ha
    · -- the blocks of a lane
      simp only [Contract.inLane, htab, List.any_cons, List.any_nil, Bool.or_false] at ha
      obtain ⟨j', hj', hin⟩ := List.any_eq_true.mp ha
      have hj' := List.mem_range.mp hj'
      simp only [Bool.and_eq_true, decide_eq_true_eq, hptr j' hj', s1l] at hin
      exact (LaneAt.where_ E hsp (atLanes j' hj')).2 (by omega) a hin.1 hin.2
    · simp only [Contract.inValArray, hva, List.any_nil] at ha; cases ha
  have hwrite : ∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true := by
    intro a ha
    simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
    rcases ha with ha | ha
    · left; omega
    · left
      simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
      omega
  have hwr : allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true := by
    apply allowed_of
    intro x hx1 hx2
    simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    left; omega
  refine ⟨h8, hwr, hpre, hread, hwrite, ?_⟩
  intro s2 post hdata2
  obtain ⟨prip, prsp, psaved, pmem, pret, psmall, pens⟩ := post
  have pensW := (pens (fun _ _ _ _ _ m => by rw [hva] at m; cases m)).2
  have hrip : s2.rip = p.base + i.next := by
    rw [prip]
    exact afterCall_back F.link hret h8
  have hkeep : ∀ r, r < ctx.nreg → c.scratch.contains r = false → s2.reg r = st.reg r := by
    intro r' hr hc
    by_cases h4 : r' = RSP
    · rw [h4, prsp, s1rsp]; omega
    · have hmemr : r' ∈ c.keeps := kept_of_not_scratch (F.regs ▸ hr) h4 hc
      rw [psaved r' hmemr, s1reg r' (callKeeps h4 (keeps_spec hmemr).2.2)]
  -- memory when the called function has returned: as before but in its frame, at the address it
  -- returned to and in the run it wrote
  have hmem2 : ∀ a : Nat, a + c.slot + c.stackAt (afterCall p q i st) < st.reg RSP ∨ st.reg RSP ≤ a →
      (a : Int) < s0.reg RSP + cw ∨ (s0.reg RSP : Int) + cw + (n : Int) ≤ a → s2.mem a = st.mem a := by
    intro a ha hb
    rw [pmem a (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1rsp]; omega)
      (by simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1r]; omega)]
    exact s1mem a (by omega)
  -- what the contract of the called function says of each lane's part of the run
  have hpostL : ∀ e ∈ c.ensuresW, ∀ a' m, e.part = some (a', m) → ∃ l' : List Nat,
      Value ctx.defs ((tx, Val.list ((List.range count).map fun i' =>
        laneBlocks (afterCall p q i st).mem (lanePtr (afterCall p q i st) tr i') ((afterCall p q i st).reg l))) ::
        envWIn c (afterCall p q i st) c.args c.argRegs) e.value (.bytes l') ∧ l'.length = m ∧
      ∀ k (h : k < l'.length), (s2.mem ((afterCall p q i st).reg r + a' + k)).val = l'[k] := by
    intro e me a' m hp
    obtain ⟨r_, n_, l', hrm, hval, hll, _, hlm⟩ := pensW e me
    rw [houts] at hrm
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hrm
    obtain ⟨_, e1, e2⟩ := hrm
    rw [e1] at hlm
    simp only [EnsureW.size, hp] at hll
    simp only [EnsureW.first, hp] at hlm
    rw [henvW] at hval
    exact ⟨l', hval, hll, hlm⟩
  obtain ⟨ρ1, C1, hb1, hev1⟩ : ∃ ρ1, Carried ctx s0 ρ { s with tab := T } ρ1 s1 st ∧ (∀ r ∈ rows, bounded s1.nvars r) ∧
      ∀ k, k < rows.length → ev ρ1 (rows.getD k (Lin.const 0)) = (load s2.mem ((afterCall p q i st).reg r + 0 + 4 * k) 4 : Nat) := by
    by_cases hpv : ctx.contract.preVals ctx.defs s0
    · exact nameLanes_sound (ctx := ctx) (s0 := s0) (st := st) s2.mem ((afterCall p q i st).reg r) hpv
        c.ensuresW HT wfT henv hokenv hnl hpostL
    · exact nameLanes_vacuous (ctx := ctx) (s0 := s0) (st := st) s2.mem ((afterCall p q i st).reg r) hpv
        c.ensuresW HT wfT hokenv hnl
  have C01 := CT.then C1
  have Hafter := afterCallL_holds E c (c.stackAt (afterCall p q i st)) F.regs C1.holds C1.wf hrsp hg.2 hg.1 hkeep psmall hcw1 hcw2 hrl' hb1 hmem2 hdata2
    (fun k hk => by rw [hev1 k hk, s1r, Nat.add_zero])
  have wafter := afterCallL_wf C1.wf c F.regs sp cw n hb1
  exact ⟨hrip, afterRho c.regs s1.nvars ρ1 s2, Agree.trans C01.mono C01.agree (afterRho_agree c.regs s1.nvars ρ1 s2),
    Nat.le_trans C01.mono (Nat.le_add_right _ _), Hafter, wafter⟩

/-- **A call, by contract, of a function that is given a table of addresses (`symCallL`).** -/
theorem symCallL_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallL ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) (i : Instr) (F : Fits ctx st i c) (hret : p.base + i.next < M64)
    (hex : CallExtra ctx s0 st c (afterCall p q i st)) (hva : c.valArrays = []) :
    c.slot ≤ st.reg RSP ∧ allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  have C := callFrameTouch_carried c (c.fixeds ++ c.inouts) H wf
  obtain ⟨h8, hw, hpre, hread, hwrite, hpost⟩ := symCallL'_sound E h C.holds C.wf q hq i F hret hex hva
  refine ⟨h8, hw, hpre, hread, hwrite, fun s2 p2 d2 => ?_⟩
  obtain ⟨hrip, ρ', C'⟩ := hpost s2 p2 d2
  exact ⟨hrip, ρ', C.then C'⟩

/-- A call, by one of the rules (`symCall'`): see `symCall_sound`. -/
theorem symCall'_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCall' ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) (i : Instr) (F : Fits ctx st i c) (hret : p.base + i.next < M64)
    (hex : CallExtra ctx s0 st c (afterCall p q i st)) :
    c.slot ≤ st.reg RSP ∧ allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  unfold symCall' at h
  split at h
  · split at h
    next hva => exact symCallL_sound E h H wf q hq i F hret hex (List.isEmpty_iff.mp hva)
    · exact (refuse_ok h).elim
  next hlanes =>
    have hl : c.lanes = [] := by simpa using hlanes
    split at h
    · split at h
      next hva => exact symCallPlain_sound E h H wf q hq i F hret hl (List.isEmpty_iff.mp hva) hex
      · exact (refuse_ok h).elim
    · split at h
      · split at h
        next hva => exact symCallB_sound E h H wf q hq i F hret hl (List.isEmpty_iff.mp hva) hex
        · exact (refuse_ok h).elim
      · split at h
        · exact symCallF_sound E h H wf q hq i F hret hl hex
        · exact symCallW_sound E h H wf q hq i F hret hl hex

/-- **A call, by contract.** If the verifier has gone through a call, then of the machine at the call: the
address to come back to can be written; the state the called function starts in is one its contract's
caller has seen to; what the called function may touch, this function may touch; and of every state the
contract lets it return in, what the verifier holds after the call is so, at the next instruction. (The
rows the proof file gives before the rule, `symKnow`, are shown, and only add to the facts.) -/
theorem symCall_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {name : String} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCall ctx s name c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) (i : Instr) (F : Fits ctx st i c) (hret : p.base + i.next < M64) :
    c.slot ≤ st.reg RSP ∧ allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true ∧
    c.pre q (afterCall p q i st) ∧
    (ctx.selfName = some name → ∀ d r, c.decreases = some d → c.regOf d = some r → (afterCall p q i st).reg r < s0.reg r) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  unfold symCall at h
  obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
  have C := symKnow_sound (ctx := ctx) KNOWN e1 H wf
  obtain ⟨_, r2, e2, h⟩ := V.bind_ok h
  obtain ⟨hex, hdec⟩ := callPreOk_sound E F C.holds e2
  obtain ⟨h8, hw, hpre, hread, hwrite, hpost⟩ := symCall'_sound E h C.holds C.wf q hq i F hret hex
  refine ⟨h8, hw, hpre, hdec, hread, hwrite, fun s2 p2 d2 => ?_⟩
  obtain ⟨hrip, ρ', C'⟩ := hpost s2 p2 d2
  exact ⟨hrip, ρ', ⟨Agree.mono C.mono C'.agree, Nat.le_trans C.mono C'.mono, C'.holds, C'.wf⟩⟩

end Ode
