import SoundStep
/-!
# Why the verifier's yes is right, 5: the specification on symbols and the specification's values
-/
namespace Ode
open Arithmetic

/-! ## A value, once had, is had with more fuel; so an expression has at most one value -/

theorem evalList_mono {ev ev' : SExpr → Option Val} (h : ∀ a v, ev a = some v → ev' a = some v) :
    ∀ (l : SExpr) {vs : List Val}, evalList ev l = some vs → evalList ev' l = some vs := by
  intro l
  induction l with
  | nil => intro vs h1; simpa [evalList] using h1
  | cons a rest _ ih =>
    intro vs h1
    simp only [evalList] at h1 ⊢
    cases hv : ev a with
    | none => simp [hv] at h1
    | some v =>
      cases hr : evalList ev rest with
      | none => simp [hv, hr] at h1
      | some vs' =>
        rw [h a v hv, ih hr]
        simpa [hv, hr] using h1
  | num _ => intro vs h1; simp [evalList] at h1
  | name _ => intro vs h1; simp [evalList] at h1
  | bin _ _ _ _ _ => intro vs h1; simp [evalList] at h1
  | ifx _ _ _ _ _ _ => intro vs h1; simp [evalList] at h1
  | index _ _ _ _ => intro vs h1; simp [evalList] at h1
  | call _ _ _ => intro vs h1; simp [evalList] at h1

theorem evalSpec_mono (defs : List Def) : ∀ (fuel : Nat) {env : List (String × Val)} {e : SExpr} {v : Val},
    evalSpec defs fuel env e = some v → ∀ fuel', fuel ≤ fuel' → evalSpec defs fuel' env e = some v
  | 0, _, _, _, h, _, _ => by simp [evalSpec] at h
  | fuel + 1, env, e, v, h, fuel', le => by
    cases fuel' with
    | zero => omega
    | succ f' =>
      have ih : ∀ {env : List (String × Val)} {e : SExpr} {v : Val}, evalSpec defs fuel env e = some v → evalSpec defs f' env e = some v :=
        fun h => evalSpec_mono defs fuel h f' (by omega)
      cases e with
      | num n => simpa [evalSpec] using h
      | name x => simpa [evalSpec] using h
      | nil => simp [evalSpec] at h
      | cons _ _ => simp [evalSpec] at h
      | bin op a b =>
        simp only [evalSpec] at h ⊢
        cases ha : evalSpec defs fuel env a with
        | none => simp [ha] at h
        | some x =>
          cases hb : evalSpec defs fuel env b with
          | none => simp [ha, hb] at h
          | some y => rw [ih ha, ih hb]; simpa [ha, hb] using h
      | index a i =>
        simp only [evalSpec] at h ⊢
        cases ha : evalSpec defs fuel env a with
        | none => simp [ha] at h
        | some x =>
          cases hb : evalSpec defs fuel env i with
          | none => simp [ha, hb] at h
          | some y => rw [ih ha, ih hb]; simpa [ha, hb] using h
      | ifx c a b =>
        simp only [evalSpec] at h ⊢
        cases hc : evalSpec defs fuel env c with
        | none => simp [hc] at h
        | some cv =>
          rw [ih hc]
          simp only [hc] at h
          cases cv with
          | int _ => simp at h
          | bytes _ => simp at h
          | bool t =>
            cases t with
            | true => simp only at h ⊢; exact ih h
            | false => simp only at h ⊢; exact ih h
      | call f args =>
        simp only [evalSpec] at h ⊢
        cases hl : evalList (evalSpec defs fuel env) args with
        | none => simp [hl] at h
        | some vs =>
          rw [evalList_mono (fun a v h => ih h) args hl]
          simp only [hl] at h
          simp only
          split at h
          next hlen => rw [if_pos hlen]; exact h
          next hlen =>
            rw [if_neg hlen]
            cases hd : findDef defs f with
            | none => simp [hd] at h
            | some d =>
              simp only [hd] at h ⊢
              split at h
              next hp => rw [if_pos hp]; exact ih h
              next => contradiction

theorem Value.unique {defs : List Def} {env : List (String × Val)} {e : SExpr} {v v' : Val}
    (h : Value defs env e v) (h' : Value defs env e v') : v = v' := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨f', hf'⟩ := h'
  have a := evalSpec_mono defs f hf (max f f') (Nat.le_max_left _ _)
  have b := evalSpec_mono defs f' hf' (max f f') (Nat.le_max_right _ _)
  rw [a] at b
  injection b

/-- The things a definition is used with have these values. -/
def Values (defs : List Def) (env : List (String × Val)) (l : SExpr) (vs : List Val) : Prop :=
  ∃ fuel, evalList (evalSpec defs fuel env) l = some vs

theorem Values.at_least {defs : List Def} {env : List (String × Val)} {l : SExpr} {vs : List Val} {fuel fuel' : Nat}
    (h : evalList (evalSpec defs fuel env) l = some vs) (le : fuel ≤ fuel') : evalList (evalSpec defs fuel' env) l = some vs :=
  evalList_mono (fun _ _ h => evalSpec_mono defs fuel h fuel' le) l h

theorem Values.unique {defs : List Def} {env : List (String × Val)} {l : SExpr} {vs vs' : List Val}
    (h : Values defs env l vs) (h' : Values defs env l vs') : vs = vs' := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨f', hf'⟩ := h'
  have a := Values.at_least hf (Nat.le_max_left f f')
  have b := Values.at_least hf' (Nat.le_max_right f f')
  rw [a] at b
  injection b

/-! ## The value of an expression from the values of its parts -/

section
variable {defs : List Def} {env : List (String × Val)}

theorem Value.num {n : Int} (h : 0 ≤ n) : Value defs env (.num n) (.int n) := ⟨1, by simp [evalSpec, h]⟩

theorem Value.name {x : String} {v : Val} (h : env.lookup x = some v) : Value defs env (.name x) v := ⟨1, by simp [evalSpec, h]⟩

theorem Value.bin {op : String} {a b : SExpr} {x y z : Val} (ha : Value defs env a x) (hb : Value defs env b y)
    (hz : binop op x y = some z) : Value defs env (.bin op a b) z := by
  obtain ⟨f, hf⟩ := ha
  obtain ⟨f', hf'⟩ := hb
  refine ⟨max f f' + 1, ?_⟩
  simp only [evalSpec]
  rw [evalSpec_mono defs f hf _ (Nat.le_max_left _ _), evalSpec_mono defs f' hf' _ (Nat.le_max_right _ _)]
  exact hz

theorem Value.index {a i : SExpr} {l : List Nat} {k : Int} {b : Nat} (ha : Value defs env a (.bytes l)) (hi : Value defs env i (.int k))
    (h0 : 0 ≤ k) (hb : l[k.toNat]? = some b) : Value defs env (.index a i) (.int b) := by
  obtain ⟨f, hf⟩ := ha
  obtain ⟨f', hf'⟩ := hi
  refine ⟨max f f' + 1, ?_⟩
  simp only [evalSpec]
  rw [evalSpec_mono defs f hf _ (Nat.le_max_left _ _), evalSpec_mono defs f' hf' _ (Nat.le_max_right _ _)]
  simp [h0, hb]

/-- Where the condition is true or false, an `if` has the values of the branch taken, and no others. -/
theorem Value.ifx {c a b : SExpr} {t : Bool} (hc : Value defs env c (.bool t)) (x : Val) :
    Value defs env (.ifx c a b) x ↔ Value defs env (if t then a else b) x := by
  obtain ⟨f, hf⟩ := hc
  constructor
  · rintro ⟨g, hg⟩
    cases g with
    | zero => simp [evalSpec] at hg
    | succ g =>
      simp only [evalSpec] at hg
      cases hcv : evalSpec defs g env c with
      | none => simp [hcv] at hg
      | some cv =>
        have : cv = .bool t := Value.unique ⟨g, hcv⟩ ⟨f, hf⟩
        subst this
        simp only [hcv] at hg
        cases t with
        | true => exact ⟨g, hg⟩
        | false => exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩
    refine ⟨max f g + 1, ?_⟩
    simp only [evalSpec]
    rw [evalSpec_mono defs f hf _ (Nat.le_max_left _ _)]
    cases t with
    | true => exact evalSpec_mono defs g hg _ (Nat.le_max_right _ _)
    | false => exact evalSpec_mono defs g hg _ (Nat.le_max_right _ _)

theorem Value.len {args : SExpr} {l : List Nat} (h : Values defs env args [.bytes l]) :
    Value defs env (.call "len" args) (.int l.length) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f + 1, by simp [evalSpec, hf]⟩

/-- A use of a definition (not `len`) has the values of the definition's body, with the definition's names
standing for the values of the things it is used with, and no others. -/
theorem Value.call {f : String} {args : SExpr} {vs : List Val} {d : Def} (hf : (f == "len") = false)
    (hd : findDef defs f = some d) (hp : (d.params.length == vs.length) = true) (h : Values defs env args vs) (x : Val) :
    Value defs env (.call f args) x ↔ Value defs (d.params.zip vs) d.body x := by
  constructor
  · rintro ⟨g, hg⟩
    cases g with
    | zero => simp [evalSpec] at hg
    | succ g =>
      simp only [evalSpec] at hg
      cases hl : evalList (evalSpec defs g env) args with
      | none => simp [hl] at hg
      | some vs' =>
        have : vs' = vs := Values.unique ⟨g, hl⟩ h
        subst this
        simp only [hl, hf, hd, hp, if_true] at hg
        exact ⟨g, by simpa using hg⟩
  · rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := h
    refine ⟨max k g + 1, ?_⟩
    simp only [evalSpec]
    rw [Values.at_least hk (Nat.le_max_left _ _)]
    simp only [hf, hd, hp, if_true]
    simpa using evalSpec_mono defs g hg _ (Nat.le_max_right _ _)

theorem Values.nil : Values defs env .nil [] := ⟨0, rfl⟩

theorem Values.cons {a rest : SExpr} {v : Val} {vs : List Val} (ha : Value defs env a v) (hr : Values defs env rest vs) :
    Values defs env (.cons a rest) (v :: vs) := by
  obtain ⟨f, hf⟩ := ha
  obtain ⟨f', hf'⟩ := hr
  refine ⟨max f f', ?_⟩
  simp only [evalList]
  rw [evalSpec_mono defs f hf _ (Nat.le_max_left _ _), Values.at_least hf' (Nat.le_max_right _ _)]

end

/-! ## The specification on symbols -/

/-- Names on symbols, as names with values. -/
def semEnv (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (env : List (String × SVal)) : List (String × Val) :=
  env.map fun nv => (nv.1, semv ctx s0 ρ nv.2)

theorem lookup_semEnv (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (x : String) : ∀ (env : List (String × SVal)),
    (semEnv ctx s0 ρ env).lookup x = (env.lookup x).map (semv ctx s0 ρ)
  | [] => rfl
  | (n, v) :: rest => by
    have ih := lookup_semEnv ctx s0 ρ x rest
    simp only [semEnv, List.map, List.lookup] at ih ⊢
    cases h : x == n with
    | true => rfl
    | false => exact ih

def EnvB (n : Nat) (env : List (String × SVal)) : Prop := ∀ nv ∈ env, nv.2.bounded n

theorem EnvB.mono {n m : Nat} {env : List (String × SVal)} (h : n ≤ m) (hb : EnvB n env) : EnvB m env :=
  fun nv mem => SVal.bounded_mono h (hb nv mem)

theorem semEnv_agree {ctx : Ctx} {s0 : State} {n : Nat} {ρ ρ' : Nat → Int} {env : List (String × SVal)} (hb : EnvB n env) (a : Agree n ρ ρ') :
    semEnv ctx s0 ρ env = semEnv ctx s0 ρ' env := by
  unfold semEnv
  exact List.map_congr_left fun nv m => by rw [semv_agree (hb nv m) a]

/-- What a result on symbols says of the expression it is the result of. -/
def SRes.sem (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (env : List (String × Val)) (e : SExpr) : SRes → Prop
  | .val v => Value ctx.defs env e (semv ctx s0 ρ v)
  | .tail c => ∀ x, Value ctx.defs env e x ↔ CallValue ctx s0 ρ c x
  | .list vs => Values ctx.defs env e (vs.map (semv ctx s0 ρ))

def SRes.bounded (n : Nat) : SRes → Prop
  | .val v => v.bounded n
  | .tail c => c.bounded n
  | .list vs => ∀ v ∈ vs, v.bounded n

theorem SRes.bounded_mono {n m : Nat} {res : SRes} (h : n ≤ m) (hb : res.bounded n) : res.bounded m := by
  cases res with
  | val v => exact SVal.bounded_mono h hb
  | tail c => exact SCall.bounded_mono h hb
  | list vs => exact fun v mem => SVal.bounded_mono h (hb v mem)

theorem SRes.sem_agree {ctx : Ctx} {s0 : State} {n : Nat} {ρ ρ' : Nat → Int} {env : List (String × SVal)} {e : SExpr} {res : SRes}
    (h : res.sem ctx s0 ρ (semEnv ctx s0 ρ env) e) (hb : res.bounded n) (he : EnvB n env) (a : Agree n ρ ρ') :
    res.sem ctx s0 ρ' (semEnv ctx s0 ρ' env) e := by
  rw [← semEnv_agree he a]
  cases res with
  | val v => simp only [SRes.sem] at h ⊢; rw [← semv_agree hb a]; exact h
  | tail c => intro x; rw [← CallValue_agree hb a x]; exact h x
  | list vs =>
    simp only [SRes.sem] at h ⊢
    rw [← List.map_congr_left (fun v m => semv_agree (hb v m) a)]; exact h

theorem cmp_facts {ρ : Nat → Int} {x y : Row} {c : Cmp}
    (cs : (c = .lt → ev ρ x < ev ρ y) ∧ (c = .eq → ev ρ x = ev ρ y) ∧ (c = .gt → ev ρ y < ev ρ x)) :
    (ev ρ x == ev ρ y) = c.isEq ∧ (ev ρ x != ev ρ y) = (!c.isEq) ∧ decide (ev ρ x < ev ρ y) = c.isLt ∧
    decide (ev ρ x ≤ ev ρ y) = (!c.isGt) ∧ decide (ev ρ y < ev ρ x) = c.isGt ∧ decide (ev ρ y ≤ ev ρ x) = (!c.isLt) := by
  obtain ⟨h1, h2, h3⟩ := cs
  cases c with
  | lt => have := h1 rfl; simp [Cmp.isEq, Cmp.isLt, Cmp.isGt]; omega
  | eq => have := h2 rfl; simp [Cmp.isEq, Cmp.isLt, Cmp.isGt]; omega
  | gt => have := h3 rfl; simp [Cmp.isEq, Cmp.isLt, Cmp.isGt]; omega

theorem sbin_sound (ctx : Ctx) (s0 : State) {op : String} {s s' : Sym} {x y : Row} {res : SRes} {items rest : List Item} {ρ : Nat → Int} {n : Nat}
    (h : sbin op s x y items = .ok ((res, s'), rest)) (hf : ∀ g ∈ s.facts, g.holds ρ) (hx : bounded n x) (hy : bounded n y) :
    s' = s ∧ ∃ v, res = .val v ∧ v.bounded n ∧ binop op (.int (ev ρ x)) (.int (ev ρ y)) = some (semv ctx s0 ρ v) := by
  unfold sbin at h
  split at h
  next h1 =>
    have := V.pure_ok h
    injection this with hp _
    injection hp with e1 e2
    subst e1 e2
    exact ⟨rfl, _, rfl, bounded_add hx hy, by simp [binop, h1, semv]⟩
  next h1 =>
    split at h
    next h2 =>
      obtain ⟨_, r1, g1, h⟩ := V.bind_ok h
      have g := entail_sound g1 ρ hf
      rw [ev_sub] at g
      have := V.pure_ok h
      injection this with hp _
      injection hp with e1 e2
      subst e1 e2
      refine ⟨rfl, _, rfl, bounded_sub hx hy, ?_⟩
      simp only [binop, h1, h2, semv, Bool.false_eq_true, if_false, if_true, ev_sub]
      rw [if_pos (by omega)]
    next h2 =>
      split at h
      next h3 =>
        cases hcx : Lin.isConst x with
        | some k =>
          simp only [hcx] at h
          have := V.pure_ok h
          injection this with hp _
          injection hp with e1 e2
          subst e1 e2
          exact ⟨rfl, _, rfl, bounded_scale _ hy, by simp [binop, h1, h2, h3, semv, ev_isConst hcx]⟩
        | none =>
          cases hcy : Lin.isConst y with
          | some k =>
            simp only [hcx, hcy] at h
            have := V.pure_ok h
            injection this with hp _
            injection hp with e1 e2
            subst e1 e2
            exact ⟨rfl, _, rfl, bounded_scale _ hx, by simp [binop, h1, h2, h3, semv, ev_isConst hcy, Int.mul_comm]⟩
          | none => simp only [hcx, hcy] at h; exact (refuse_ok h).elim
      next h3 =>
        obtain ⟨c, r1, e1, h⟩ := V.bind_ok h
        obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cmp_facts (compare_sound e1 ρ hf)
        split at h
        next h4 =>
          have := V.pure_ok h
          injection this with hp _
          injection hp with e1 e2
          subst e1 e2
          exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, semv, ← c1]⟩
        next h4 =>
          split at h
          next h5 =>
            have := V.pure_ok h
            injection this with hp _
            injection hp with e1 e2
            subst e1 e2
            exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, h5, semv, ← c2]⟩
          next h5 =>
            split at h
            next h6 =>
              have := V.pure_ok h
              injection this with hp _
              injection hp with e1 e2
              subst e1 e2
              exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, h5, h6, semv, ← c3]⟩
            next h6 =>
              split at h
              next h7 =>
                have := V.pure_ok h
                injection this with hp _
                injection hp with e1 e2
                subst e1 e2
                exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, h5, h6, h7, semv, ← c4]⟩
              next h7 =>
                split at h
                next h8 =>
                  have := V.pure_ok h
                  injection this with hp _
                  injection hp with e1 e2
                  subst e1 e2
                  exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, h5, h6, h7, h8, semv, ← c5]⟩
                next h8 =>
                  split at h
                  next h9 =>
                    have := V.pure_ok h
                    injection this with hp _
                    injection hp with e1 e2
                    subst e1 e2
                    exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, h5, h6, h7, h8, h9, semv, ← c6]⟩
                  next => exact (refuse_ok h).elim

theorem runBytes_get (s0 : State) (base len k : Nat) (h : k < s0.reg len) : (runBytes s0 base len)[k]? = some (s0.mem (s0.reg base + k)) := by
  simp [runBytes, h]

theorem scall_sound {ctx : Ctx} {s0 : State} {f : String} {vs : List SVal} {s s' : Sym} {res : SRes} {items rest : List Item}
    {ρ : Nat → Int} {st : State} (h : scall ctx f vs s items = .ok ((res, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hb : ∀ v ∈ vs, v.bounded s.nvars) (env : List (String × Val)) (args : SExpr)
    (ha : Values ctx.defs env args (vs.map (semv ctx s0 ρ))) :
    s' = s ∧ res.sem ctx s0 ρ env (.call f args) ∧ res.bounded s.nvars := by
  unfold scall at h
  split at h
  next hlen =>
    have fl : f = "len" := by simpa using hlen
    subst fl
    cases vs with
    | nil => exact (refuse_ok h).elim
    | cons v more =>
      cases more with
      | cons _ _ => cases v <;> exact (refuse_ok h).elim
      | nil =>
        cases v with
        | lin _ => exact (refuse_ok h).elim
        | bool _ => exact (refuse_ok h).elim
        | region r =>
          simp only at h
          cases hreg : ctx.contract.regions[r]? with
          | none => simp only [hreg] at h; exact (refuse_ok h).elim
          | some bl =>
            obtain ⟨base, len⟩ := bl
            simp only [hreg] at h
            have := V.pure_ok h
            injection this with hp _
            injection hp with e1 e2
            subst e1 e2
            have hlt := (regions_lt (List.mem_of_getElem? hreg)).2
            refine ⟨rfl, ?_, bounded_var (Nat.lt_of_lt_of_le hlt wf.base)⟩
            simp only [List.map, semv, hreg] at ha
            have := Value.len ha
            simp only [SRes.sem, semv, ev_var, H.entry len hlt]
            simpa [runBytes] using this
  next hlen =>
    cases hd : findDef ctx.defs f with
    | none => simp only [hd] at h; exact (refuse_ok h).elim
    | some d =>
      simp only [hd] at h
      split at h
      next hp =>
        have := V.pure_ok h
        injection this with hp' _
        injection hp' with e1 e2
        subst e1 e2
        refine ⟨rfl, ?_, hb⟩
        intro x
        simp only [CallValue, hd]
        exact Value.call (by simpa using hlen) hd (by simpa using hp) ha x
      next => exact (refuse_ok h).elim

theorem ifx_finish {r res : SRes} {s2 s' : Sym} {r2 rest : List Item}
    (h : (match r with
          | .list _ => refuse "a list of things where a value is expected"
          | _ => pure (r, s2) : V (SRes × Sym)) r2 = .ok ((res, s'), rest)) :
    r = res ∧ s2 = s' ∧ ∀ vs, r ≠ .list vs := by
  cases r with
  | list _ => exact (refuse_ok h).elim
  | val v =>
    have := V.pure_ok h
    injection this with hp _
    injection hp with e1 e2
    exact ⟨e1.symm, e2.symm, fun vs h => by cases h⟩
  | tail c =>
    have := V.pure_ok h
    injection this with hp _
    injection hp with e1 e2
    exact ⟨e1.symm, e2.symm, fun vs h => by cases h⟩

/-- An expression of the specification worked out on symbols: what comes out is what the expression means. -/
theorem seval_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (env : List (String × SVal)) :
    ∀ (e : SExpr) {s s' : Sym} {res : SRes} {items rest : List Item} {ρ : Nat → Int} {st : State},
    seval ctx env s e items = .ok ((res, s'), rest) → Holds ctx s0 ρ s st → WF s → EnvB s.nvars env →
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ res.sem ctx s0 ρ' (semEnv ctx s0 ρ' env) e ∧ res.bounded s'.nvars := by
  intro e
  induction e with
  | num n =>
    intro s s' res items rest ρ st h H wf hb
    simp only [seval] at h
    split at h
    next => exact (refuse_ok h).elim
    next hn =>
      have := V.pure_ok h
      injection this with hp _
      injection hp with e1 e2
      subst e1 e2
      exact ⟨ρ, Carried.here H wf, by simpa [SRes.sem, semv] using Value.num (Int.not_lt.mp hn), bounded_const _ _⟩
  | name x =>
    intro s s' res items rest ρ st h H wf hb
    simp only [seval] at h
    cases hl : env.lookup x with
    | none => simp only [hl] at h; exact (refuse_ok h).elim
    | some v =>
      simp only [hl] at h
      have := V.pure_ok h
      injection this with hp _
      injection hp with e1 e2
      subst e1 e2
      exact ⟨ρ, Carried.here H wf, Value.name (by rw [lookup_semEnv, hl]; rfl), hb _ (lookup_mem hl)⟩
  | nil =>
    intro s s' res items rest ρ st h H wf hb
    simp only [seval] at h
    have := V.pure_ok h
    injection this with hp _
    injection hp with e1 e2
    subst e1 e2
    exact ⟨ρ, Carried.here H wf, Values.nil, fun _ m => by cases m⟩
  | cons a more iha ihm =>
    intro s s' res items rest ρ st h H wf hb
    simp only [seval] at h
    obtain ⟨⟨v, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨⟨vs, s2⟩, r2, e2, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1, sa, ba⟩ := iha e1 H wf hb
    have hb1 := hb.mono c1.mono
    obtain ⟨ρ2, c2, sm, bm⟩ := ihm e2 c1.holds c1.wf hb1
    have sa2 := SRes.sem_agree sa ba hb1 c2.agree
    cases v with
    | tail _ => exact (refuse_ok h).elim
    | list _ => exact (refuse_ok h).elim
    | val v =>
      cases vs with
      | tail _ => exact (refuse_ok h).elim
      | val _ => exact (refuse_ok h).elim
      | list vs =>
        simp only at h
        have := V.pure_ok h
        injection this with hp _
        injection hp with e1 e2
        subst e1 e2
        refine ⟨ρ2, c1.then c2, Values.cons sa2 sm, ?_⟩
        intro w m
        cases m with
        | head => exact SVal.bounded_mono c2.mono ba
        | tail _ m => exact bm w m
  | bin op a b iha ihb =>
    intro s s' res items rest ρ st h H wf hb
    simp only [seval] at h
    obtain ⟨⟨x, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨⟨y, s2⟩, r2, e2, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1, sa, ba⟩ := iha e1 H wf hb
    have hb1 := hb.mono c1.mono
    obtain ⟨ρ2, c2, sb, bb⟩ := ihb e2 c1.holds c1.wf hb1
    have sa2 := SRes.sem_agree sa ba hb1 c2.agree
    cases x with
    | tail _ => exact (refuse_ok h).elim
    | list _ => exact (refuse_ok h).elim
    | val x =>
      cases x with
      | region _ => exact (refuse_ok h).elim
      | bool _ => exact (refuse_ok h).elim
      | lin x =>
        cases y with
        | tail _ => exact (refuse_ok h).elim
        | list _ => exact (refuse_ok h).elim
        | val y =>
          cases y with
          | region _ => exact (refuse_ok h).elim
          | bool _ => exact (refuse_ok h).elim
          | lin y =>
            simp only at h
            obtain ⟨hs, v, hres, bv, hz⟩ := sbin_sound ctx s0 h c2.holds.facts (bounded_mono c2.mono ba) bb
            subst hs hres
            exact ⟨ρ2, c1.then c2, Value.bin sa2 sb hz, bv⟩
  | index a i iha ihi =>
    intro s s' res items rest ρ st h H wf hb
    simp only [seval] at h
    obtain ⟨⟨x, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨⟨y, s2⟩, r2, e2, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1, sa, ba⟩ := iha e1 H wf hb
    have hb1 := hb.mono c1.mono
    obtain ⟨ρ2, c2, sb, bb⟩ := ihi e2 c1.holds c1.wf hb1
    have hb2 := hb1.mono c2.mono
    have sa2 := SRes.sem_agree sa ba hb1 c2.agree
    cases x with
    | tail _ => exact (refuse_ok h).elim
    | list _ => exact (refuse_ok h).elim
    | val x =>
      cases x with
      | lin _ => exact (refuse_ok h).elim
      | bool _ => exact (refuse_ok h).elim
      | region r =>
        cases y with
        | tail _ => exact (refuse_ok h).elim
        | list _ => exact (refuse_ok h).elim
        | val y =>
          cases y with
          | region _ => exact (refuse_ok h).elim
          | bool _ => exact (refuse_ok h).elim
          | lin o =>
            simp only at h
            obtain ⟨⟨v, s3⟩, r3, e3, h⟩ := V.bind_ok h
            have := V.pure_ok h
            injection this with hp _
            injection hp with e1 e2
            subst e1 e2
            obtain ⟨ρ3, c3, bv, base, len, hreg, g1, g2, g3⟩ := readByte_sound E e3 c2.holds c2.wf bb
            have sa3 := SRes.sem_agree sa2 (show (SRes.val (.region r)).bounded s2.nvars from trivial) hb2 c3.agree
            have sb3 := SRes.sem_agree sb bb hb2 c3.agree
            simp only [SRes.sem, semv, hreg] at sa3 sb3
            refine ⟨ρ3, (c1.then c2).then c3, ?_, bv⟩
            simp only [SRes.sem, semv, g3]
            exact Value.index sa3 sb3 g1 (runBytes_get s0 base len _ (by omega))
  | call f args iha =>
    intro s s' res items rest ρ st h H wf hb
    simp only [seval] at h
    obtain ⟨⟨vs, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1, sa, ba⟩ := iha e1 H wf hb
    cases vs with
    | tail _ => exact (refuse_ok h).elim
    | val _ => exact (refuse_ok h).elim
    | list vs =>
      simp only at h
      obtain ⟨hs, sem, bd⟩ := scall_sound h c1.holds c1.wf ba (semEnv ctx s0 ρ1 env) args sa
      subst hs
      exact ⟨ρ1, c1, sem, bd⟩
  | ifx c a b ihc iha ihb =>
    intro s s' res items rest ρ st h H wf hb
    simp only [seval] at h
    obtain ⟨⟨cv, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1, sc, bc⟩ := ihc e1 H wf hb
    have hb1 := hb.mono c1.mono
    cases cv with
    | tail _ => exact (refuse_ok h).elim
    | list _ => exact (refuse_ok h).elim
    | val cv =>
      cases cv with
      | lin _ => exact (refuse_ok h).elim
      | region _ => exact (refuse_ok h).elim
      | bool t =>
        simp only at h
        cases t with
        | true =>
          simp only [if_true] at h
          obtain ⟨⟨r, s2⟩, r2, e2, h⟩ := V.bind_ok h
          obtain ⟨ρ2, c2, sr, br⟩ := iha e2 c1.holds c1.wf hb1
          have sc2 := SRes.sem_agree sc bc hb1 c2.agree
          simp only [SRes.sem, semv] at sc2
          obtain ⟨hres, hs, nl⟩ := ifx_finish h
          subst hres hs
          refine ⟨ρ2, c1.then c2, ?_, br⟩
          cases r with
          | list vs => exact (nl vs rfl).elim
          | val v => exact (Value.ifx sc2 _).mpr sr
          | tail c' => exact fun x => (Value.ifx sc2 x).trans (sr x)
        | false =>
          simp only [Bool.false_eq_true, if_false] at h
          obtain ⟨⟨r, s2⟩, r2, e2, h⟩ := V.bind_ok h
          obtain ⟨ρ2, c2, sr, br⟩ := ihb e2 c1.holds c1.wf hb1
          have sc2 := SRes.sem_agree sc bc hb1 c2.agree
          simp only [SRes.sem, semv] at sc2
          obtain ⟨hres, hs, nl⟩ := ifx_finish h
          subst hres hs
          refine ⟨ρ2, c1.then c2, ?_, br⟩
          cases r with
          | list vs => exact (nl vs rfl).elim
          | val v => exact (Value.ifx sc2 _).mpr sr
          | tail c' => exact fun x => (Value.ifx sc2 x).trans (sr x)

/-! ## Uses of definitions: opening one, and which are the same -/

theorem semEnv_zip (ctx : Ctx) (s0 : State) (ρ : Nat → Int) : ∀ (params : List String) (args : List SVal),
    semEnv ctx s0 ρ (params.zip args) = params.zip (args.map (semv ctx s0 ρ))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, a :: as => by
    have ih := semEnv_zip ctx s0 ρ ps as
    simp only [semEnv, List.zip_cons_cons, List.map_cons] at ih ⊢
    rw [ih]

theorem mem_zip_right {α β : Type} : ∀ {l : List α} {m : List β} {a : α} {b : β}, (a, b) ∈ l.zip m → b ∈ m
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: l, y :: m, a, b, h => by
    simp only [List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · injection h with h1 h2; subst h2; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_zip_right h)

theorem Holds.withSpec {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (f : SFact) (hf : f.holds ctx s0 ρ) : Holds ctx s0 ρ { s with spec := f :: s.spec } st :=
  ⟨H.entry, H.reg, H.small, H.zf, H.cf, H.frame, H.facts, H.bytes,
   fun g m => by
     cases m with
     | head => exact hf
     | tail _ m => exact H.spec g m,
   H.mem⟩

theorem WF.withSpec {s : Sym} (wf : WF s) (f : SFact) (hf : f.bounded s.nvars) : WF { s with spec := f :: s.spec } :=
  ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.facts, wf.bytes,
   fun g m => by
     cases m with
     | head => exact hf
     | tail _ m => exact wf.spec g m⟩

theorem openCall_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : SCall}
    {items rest : List Item} {ρ : Nat → Int} {st : State}
    (h : openCall ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (hc : c.bounded s.nvars) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st := by
  cases hd : findDef ctx.defs c.f with
  | none => simp only [openCall, hd] at h; exact (refuse_ok h).elim
  | some d =>
    simp only [openCall, hd] at h
    split at h
    next => exact (refuse_ok h).elim
    next =>
      obtain ⟨⟨res, s1⟩, r1, e1, h⟩ := V.bind_ok h
      have hbenv : EnvB s.nvars (d.params.zip c.args) := fun nv m => hc nv.2 (mem_zip_right m)
      obtain ⟨ρ1, c1, sem, bd⟩ := seval_sound E _ d.body e1 H wf hbenv
      rw [semEnv_zip] at sem
      have hc1 := SCall.bounded_mono c1.mono hc
      cases res with
      | list _ => exact (refuse_ok h).elim
      | tail c' =>
        simp only at h
        have := V.pure_ok h
        injection this with h1 _
        subst h1
        refine ⟨ρ1, c1.agree, c1.mono, c1.holds.withSpec _ ?_, c1.wf.withSpec _ ⟨hc1, bd⟩⟩
        intro x
        simp only [CallValue, hd]
        exact sem x
      | val v =>
        cases v with
        | region _ => exact (refuse_ok h).elim
        | bool _ => exact (refuse_ok h).elim
        | lin v =>
          simp only at h
          have := V.pure_ok h
          injection this with h1 _
          subst h1
          refine ⟨ρ1, c1.agree, c1.mono, c1.holds.withSpec _ ?_, c1.wf.withSpec _ ⟨hc1, bd⟩⟩
          simp only [SFact.holds, CallValue, hd]
          exact sem

/-- Two uses of definitions have the same values. -/
def Eqv (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (a b : SCall) : Prop := ∀ x, CallValue ctx s0 ρ a x ↔ CallValue ctx s0 ρ b x

theorem mem_insert {c x : SCall} {l : List SCall} (h : c ∈ insert x l) : c ∈ l ∨ c = x := by
  unfold insert at h
  split at h
  · exact Or.inl h
  · simpa using h

theorem reachStep_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} (a : SCall) {f : SFact} {seen : List SCall}
    (hf : f.holds ctx s0 ρ) (hs : ∀ c ∈ seen, Eqv ctx s0 ρ a c) : ∀ c ∈ reachStep seen f, Eqv ctx s0 ρ a c := by
  cases f with
  | value _ _ => exact hs
  | same x y =>
    intro c m
    simp only [reachStep] at m
    split at m
    next hx =>
      rcases mem_insert m with m | rfl
      · exact hs c m
      · have := hs x (by simpa using hx)
        exact fun v => (this v).trans (hf v)
    next =>
      split at m
      next hy =>
        rcases mem_insert m with m | rfl
        · exact hs c m
        · have := hs y (by simpa using hy)
          exact fun v => (this v).trans (hf v).symm
      next => exact hs c m

theorem foldl_reach {ctx : Ctx} {s0 : State} {ρ : Nat → Int} (a : SCall) : ∀ (facts : List SFact) (seen : List SCall),
    (∀ f ∈ facts, f.holds ctx s0 ρ) → (∀ c ∈ seen, Eqv ctx s0 ρ a c) → ∀ c ∈ facts.foldl reachStep seen, Eqv ctx s0 ρ a c
  | [], _, _, hs => hs
  | f :: more, seen, hf, hs =>
    foldl_reach a more (reachStep seen f) (fun g m => hf g (List.mem_cons_of_mem _ m))
      (reachStep_sound a (hf f (List.mem_cons_self ..)) hs)

theorem reach_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} (a : SCall) (facts : List SFact) (hf : ∀ f ∈ facts, f.holds ctx s0 ρ) :
    ∀ (fuel : Nat) (seen : List SCall), (∀ c ∈ seen, Eqv ctx s0 ρ a c) → ∀ c ∈ reach facts fuel seen, Eqv ctx s0 ρ a c
  | 0, _, hs => hs
  | fuel + 1, seen, hs => reach_sound a facts hf fuel _ (foldl_reach a facts seen hf hs)

theorem holdsSpec_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {facts : List SFact} {goal : SFact}
    (h : holdsSpec facts goal = true) (hf : ∀ f ∈ facts, f.holds ctx s0 ρ) : goal.holds ctx s0 ρ := by
  cases goal with
  | same a b =>
    simp only [holdsSpec] at h
    have m : b ∈ reach facts (facts.length + 1) [a] := by simpa using h
    exact reach_sound a facts hf _ [a] (fun c mc => by simp only [List.mem_singleton] at mc; subst mc; exact fun _ => Iff.rfl) b m
  | value c v =>
    simp only [holdsSpec] at h
    obtain ⟨c', m, hv⟩ := List.any_eq_true.mp h
    have hv' : SFact.value c' v ∈ facts := by simpa using hv
    have e := reach_sound c facts hf _ [c] (fun x mx => by simp only [List.mem_singleton] at mx; subst mx; exact fun _ => Iff.rfl) c' m
    exact (e _).mpr (hf _ hv')

theorem mem_foldl_insert {c : SCall} : ∀ (xs acc : List SCall), c ∈ xs.foldl (fun l c => insert c l) acc → c ∈ acc ∨ c ∈ xs
  | [], _, h => Or.inl h
  | x :: xs, acc, h => by
    simp only [List.foldl] at h
    rcases mem_foldl_insert xs _ h with h | h
    · rcases mem_insert h with h | rfl
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem callsIn_bounded {n : Nat} {f : SFact} (hb : f.bounded n) : ∀ c ∈ callsIn f, c.bounded n := by
  cases f with
  | same a b =>
    intro c m
    simp only [callsIn, List.mem_cons, List.mem_nil_iff, or_false] at m
    rcases m with rfl | rfl
    · exact hb.1
    · exact hb.2
  | value a v =>
    intro c m
    simp only [callsIn, List.mem_cons, List.mem_nil_iff, or_false] at m
    subst m
    exact hb.1

theorem callsOf_bounded {n : Nat} {facts : List SFact} {goal : SFact} (hf : ∀ f ∈ facts, f.bounded n) (hg : goal.bounded n) :
    ∀ c ∈ callsOf facts goal, c.bounded n := by
  intro c m
  unfold callsOf at m
  rcases mem_foldl_insert _ _ m with m | m
  · cases m
  · obtain ⟨l, hl, hc⟩ := List.mem_flatten.mp m
    obtain ⟨f, hfm, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_append.mp hfm with hfm | hfm
    · exact callsIn_bounded (hf f (List.mem_reverse.mp hfm)) c hc
    · simp only [List.mem_singleton] at hfm
      subst hfm
      exact callsIn_bounded hg c hc

/-- A fact of the specification the verifier has come to: it is so. -/
theorem specGoal_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) :
    ∀ (fuel : Nat) {s s' : Sym} {goal : SFact} {items rest : List Item} {ρ : Nat → Int} {st : State},
    specGoal ctx fuel s goal items = .ok (s', rest) → Holds ctx s0 ρ s st → WF s → goal.bounded s.nvars →
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ goal.holds ctx s0 ρ'
  | 0, s, s', goal, items, rest, ρ, st, h, H, wf, hg => by
    simp only [specGoal] at h
    exact (refuse_ok h).elim
  | fuel + 1, s, s', goal, items, rest, ρ, st, h, H, wf, hg => by
    simp only [specGoal] at h
    split at h
    next hh =>
      have := V.pure_ok h
      injection this with h1 _
      subst h1
      exact ⟨ρ, Carried.here H wf, holdsSpec_sound hh H.spec⟩
    next =>
      obtain ⟨item, r1, _, h⟩ := V.bind_ok h
      cases item with
      | none => cases h
      | some it =>
        cases it with
        | proof _ _ => exact (refuse_ok h).elim
        | tag name n =>
          simp only at h
          split at h
          next =>
            cases hc : (callsOf s.spec goal)[n]? with
            | none => simp only [hc] at h; exact (refuse_ok h).elim
            | some c =>
              simp only [hc] at h
              obtain ⟨s1, r2, e1, h⟩ := V.bind_ok h
              have hcb := callsOf_bounded wf.spec hg c (List.mem_of_getElem? hc)
              obtain ⟨ρ1, c1⟩ := openCall_sound E e1 H wf hcb
              obtain ⟨ρ2, c2, gh⟩ := specGoal_sound E fuel h c1.holds c1.wf (SFact.bounded_mono c1.mono hg)
              exact ⟨ρ2, c1.then c2, gh⟩
          next => exact (refuse_ok h).elim

/-! ## The contract's names -/

theorem symEnvIn_bounded (c : Contract) : ∀ (args : List (String × Kind)) (regs : List Nat) (k : Nat),
    (∀ r ∈ regs, r < 16) → EnvB 16 (symEnvIn c args regs k)
  | [], _, _, _ => by intro nv m; simp [symEnvIn] at m
  | _ :: _, [], _, _ => by intro nv m; simp [symEnvIn] at m
  | (n, .number) :: args, r :: regs, k, hr => by
    intro nv m
    simp only [symEnvIn, List.mem_cons] at m
    rcases m with rfl | m
    · exact bounded_var (hr r (List.mem_cons_self ..))
    · exact symEnvIn_bounded c args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m')) nv m
  | (n, .bytes len) :: args, r :: regs, k, hr => by
    intro nv m
    simp only [symEnvIn] at m
    split at m
    · simp only [List.mem_cons] at m
      rcases m with rfl | m
      · trivial
      · exact symEnvIn_bounded c args regs (k + 1) (fun r' m' => hr r' (List.mem_cons_of_mem _ m')) nv m
    · exact symEnvIn_bounded c args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m')) nv m

theorem symEnv_bounded (c : Contract) : EnvB 16 (symEnv c) :=
  symEnvIn_bounded c c.args argRegs 0 (fun _ m => argRegs_lt m)

theorem semEnv_symEnvIn (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (hρ : ∀ r, r < 16 → ρ r = s0.reg r) :
    ∀ (args : List (String × Kind)) (regs : List Nat) (k : Nat), (∀ r ∈ regs, r < 16) →
    (∀ j, (regionsIn ctx.contract args regs)[j]? = ctx.contract.regions[k + j]?) →
    semEnv ctx s0 ρ (symEnvIn ctx.contract args regs k) = envIn ctx.contract s0 args regs
  | [], _, _, _, _ => by simp [symEnvIn, envIn, semEnv]
  | _ :: _, [], _, _, _ => by simp [symEnvIn, envIn, semEnv]
  | (n, .number) :: args, r :: regs, k, hr, hj => by
    have ih := semEnv_symEnvIn ctx s0 ρ hρ args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m'))
      (by intro j; have := hj j; simpa only [regionsIn] using this)
    simp only [symEnvIn, envIn, semEnv, List.map_cons, semv, ev_var] at ih ⊢
    rw [hρ r (hr r (List.mem_cons_self ..)), ih]
  | (n, .bytes len) :: args, r :: regs, k, hr, hj => by
    cases hl : ctx.contract.regOf len with
    | none =>
      have ih := semEnv_symEnvIn ctx s0 ρ hρ args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m'))
        (by intro j; have := hj j; simpa only [regionsIn, hl] using this)
      simp only [symEnvIn, envIn, hl]
      exact ih
    | some l =>
      have ih := semEnv_symEnvIn ctx s0 ρ hρ args regs (k + 1) (fun r' m' => hr r' (List.mem_cons_of_mem _ m'))
        (by intro j
            have := hj (j + 1)
            simp only [regionsIn, hl, List.getElem?_cons_succ] at this
            rw [this]; congr 1; omega)
      have h0 := hj 0
      simp only [regionsIn, hl, List.getElem?_cons_zero, Nat.add_zero] at h0
      simp only [symEnvIn, envIn, hl, semEnv, List.map_cons, semv, ← h0, runBytes] at ih ⊢
      rw [ih]

/-- The contract's names on symbols mean the contract's names in the state at entry. -/
theorem semEnv_symEnv (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (hρ : ∀ r, r < 16 → ρ r = s0.reg r) :
    semEnv ctx s0 ρ (symEnv ctx.contract) = ctx.contract.env s0 :=
  semEnv_symEnvIn ctx s0 ρ hρ ctx.contract.args argRegs 0 (fun _ m => argRegs_lt m) (by intro j; simp [Contract.regions])

end Ode
