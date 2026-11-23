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
  | list _ _ => intro vs h1; simp [evalList] at h1
  | name _ => intro vs h1; simp [evalList] at h1
  | bin _ _ _ _ _ => intro vs h1; simp [evalList] at h1
  | ifx _ _ _ _ _ _ => intro vs h1; simp [evalList] at h1
  | index _ _ _ _ => intro vs h1; simp [evalList] at h1
  | call _ _ _ => intro vs h1; simp [evalList] at h1
  | letx _ _ _ _ _ => intro vs h1; simp [evalList] at h1
  | each _ _ _ _ _ _ _ => intro vs h1; simp [evalList] at h1
  | slice _ _ _ _ _ _ => intro vs h1; simp [evalList] at h1
  | withx _ _ _ _ => intro vs h1; simp [evalList] at h1
  | record _ _ _ => intro vs h1; simp [evalList] at h1
  | field _ _ _ => intro vs h1; simp [evalList] at h1
  | theNumber _ _ _ _ _ _ _ _ => intro vs h1; simp [evalList] at h1
  | thePower _ _ _ _ => intro vs h1; simp [evalList] at h1

theorem evalEach_mono {ev ev' : Int → Option Val} (h : ∀ i v, ev i = some v → ev' i = some v) :
    ∀ (n : Nat) (i : Int) {vs : List Val}, evalEach ev n i = some vs → evalEach ev' n i = some vs := by
  intro n
  induction n with
  | zero => intro i vs h1; simpa [evalEach] using h1
  | succ n ih =>
    intro i vs h1
    simp only [evalEach] at h1 ⊢
    cases hv : ev i with
    | none => simp [hv] at h1
    | some v =>
      cases hr : evalEach ev n (i + 1) with
      | none => simp [hv, hr] at h1
      | some vs' =>
        rw [h i v hv, ih (i + 1) hr]
        simpa [hv, hr] using h1

theorem firstWith_mono {ev ev' : Int → Option Val} (h : ∀ i v, ev i = some v → ev' i = some v) :
    ∀ (l : List Int) {v : Val}, firstWith ev l = some v → firstWith ev' l = some v := by
  intro l
  induction l with
  | nil => intro v h1; simp [firstWith] at h1
  | cons n rest ih =>
    intro v h1
    simp only [firstWith] at h1 ⊢
    cases hv : ev n with
    | none => simp [hv] at h1
    | some c =>
      rw [h n c hv]
      simp only [hv] at h1
      cases c with
      | bool t =>
        cases t with
        | true => simpa using h1
        | false => simp only at h1 ⊢; exact ih h1
      | _ => simp at h1

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
      | list items =>
        simp only [evalSpec] at h ⊢
        cases hl : evalList (evalSpec defs fuel env) items with
        | none => simp [hl] at h
        | some vs =>
          rw [evalList_mono (fun a v h => ih h) items hl]
          simpa [hl] using h
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
          | bool t =>
            cases t with
            | true => simp only at h ⊢; exact ih h
            | false => simp only at h ⊢; exact ih h
          | _ => simp at h
      | letx x e rest =>
        simp only [evalSpec] at h ⊢
        cases he : evalSpec defs fuel env e with
        | none => simp [he] at h
        | some v1 => rw [ih he]; simp only [he] at h; exact ih h
      | each e x a b =>
        simp only [evalSpec] at h ⊢
        cases ha : evalSpec defs fuel env a with
        | none => simp [ha] at h
        | some va =>
          cases hb : evalSpec defs fuel env b with
          | none => simp [ha, hb] at h
          | some vb =>
            rw [ih ha, ih hb]
            simp only [ha, hb] at h
            cases va with
            | int lo =>
              cases vb with
              | int hi =>
                simp only at h ⊢
                cases hl : evalEach (fun i => evalSpec defs fuel ((x, .int i) :: env) e) (hi - lo).toNat lo with
                | none => simp [hl] at h
                | some vs => rw [evalEach_mono (fun i v h => ih h) _ _ hl]; simpa [hl] using h
              | _ => simp at h
            | _ => simp at h
      | slice a lo hi =>
        simp only [evalSpec] at h ⊢
        cases ha : evalSpec defs fuel env a with
        | none => simp [ha] at h
        | some va =>
          cases hl : evalSpec defs fuel env lo with
          | none => simp [ha, hl] at h
          | some vl =>
            cases hh : evalSpec defs fuel env hi with
            | none => simp [ha, hl, hh] at h
            | some vh => rw [ih ha, ih hl, ih hh]; simpa [ha, hl, hh] using h
      | withx a puts =>
        simp only [evalSpec] at h ⊢
        cases ha : evalSpec defs fuel env a with
        | none => simp [ha] at h
        | some va =>
          cases hp : evalList (evalSpec defs fuel env) puts with
          | none => simp [ha, hp] at h
          | some ps => rw [ih ha, evalList_mono (fun a v h => ih h) puts hp]; simpa [ha, hp] using h
      | record names items =>
        simp only [evalSpec] at h ⊢
        cases hl : evalList (evalSpec defs fuel env) items with
        | none => simp [hl] at h
        | some vs => rw [evalList_mono (fun a v h => ih h) items hl]; simpa [hl] using h
      | field e x =>
        simp only [evalSpec] at h ⊢
        cases he : evalSpec defs fuel env e with
        | none => simp [he] at h
        | some ve => rw [ih he]; simpa [he] using h
      | theNumber greatest x a b cond =>
        simp only [evalSpec] at h ⊢
        cases ha : evalSpec defs fuel env a with
        | none => simp [ha] at h
        | some va =>
          cases hb : evalSpec defs fuel env b with
          | none => simp [ha, hb] at h
          | some vb =>
            rw [ih ha, ih hb]
            simp only [ha, hb] at h
            cases va with
            | int lo =>
              cases vb with
              | int hi => simp only at h ⊢; exact firstWith_mono (fun i v h => ih h) _ h
              | _ => simp at h
            | _ => simp at h
      | thePower greatest x cond =>
        simp only [evalSpec] at h ⊢
        exact firstWith_mono (fun i v h => ih h) _ h
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
            split at h
            next ho => rw [if_pos ho]; exact h
            next ho =>
              rw [if_neg ho]
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
  simp [Val.bytes, h0, hb]

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
  exact ⟨f + 1, by simp [evalSpec, hf, Val.bytes]⟩

/-- A use of a definition (not `len`) has the values of the definition's body, with the definition's names
standing for the values of the things it is used with, and no others. -/
theorem Value.call {f : String} {args : SExpr} {vs : List Val} {d : Def} (hf : (f == "len") = false) (ho : own.contains f = false)
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
        simp only [hl, hf, ho, hd, hp, if_true] at hg
        exact ⟨g, by simpa using hg⟩
  · rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := h
    refine ⟨max k g + 1, ?_⟩
    simp only [evalSpec]
    rw [Values.at_least hk (Nat.le_max_left _ _)]
    simp only [hf, ho, hd, hp, if_true]
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

theorem sbin_sound (ctx : Ctx) (s0 : State) {op : String} {s s' : Sym} {x y : Row} {res : SRes} {items rest : Items} {ρ : Nat → Int} {n : Nat}
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
        split at h
        next h4 =>
          obtain ⟨c, r1, e1, h⟩ := V.bind_ok h
          obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cmp_facts (compare_sound e1 ρ hf)
          have := V.pure_ok h
          injection this with hp _
          injection hp with e1 e2
          subst e1 e2
          exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, semv, ← c1]⟩
        next h4 =>
          split at h
          next h5 =>
            obtain ⟨c, r1, e1, h⟩ := V.bind_ok h
            obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cmp_facts (compare_sound e1 ρ hf)
            have := V.pure_ok h
            injection this with hp _
            injection hp with e1 e2
            subst e1 e2
            exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, h5, semv, ← c2]⟩
          next h5 =>
            split at h
            next h6 =>
              obtain ⟨t, r1, e1, h⟩ := V.bind_ok h
              have ht := isBelow_sound e1 ρ hf
              have := V.pure_ok h
              injection this with hp _
              injection hp with e1 e2
              subst e1 e2
              exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, h5, h6, semv, ht]⟩
            next h6 =>
              split at h
              next h7 =>
                obtain ⟨t, r1, e1, h⟩ := V.bind_ok h
                have ht := isBelow_sound e1 ρ hf
                have := V.pure_ok h
                injection this with hp _
                injection hp with e1 e2
                subst e1 e2
                have hd : decide (ev ρ x ≤ ev ρ y) = !decide (ev ρ y < ev ρ x) := by
                  by_cases hc : ev ρ y < ev ρ x <;> simp [hc] <;> omega
                exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, h5, h6, h7, semv, ht, hd]⟩
              next h7 =>
                split at h
                next h8 =>
                  obtain ⟨t, r1, e1, h⟩ := V.bind_ok h
                  have ht := isBelow_sound e1 ρ hf
                  have := V.pure_ok h
                  injection this with hp _
                  injection hp with e1 e2
                  subst e1 e2
                  exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, h5, h6, h7, h8, semv, ht]⟩
                next h8 =>
                  split at h
                  next h9 =>
                    obtain ⟨t, r1, e1, h⟩ := V.bind_ok h
                    have ht := isBelow_sound e1 ρ hf
                    have := V.pure_ok h
                    injection this with hp _
                    injection hp with e1 e2
                    subst e1 e2
                    have hd : decide (ev ρ y ≤ ev ρ x) = !decide (ev ρ x < ev ρ y) := by
                      by_cases hc : ev ρ x < ev ρ y <;> simp [hc] <;> omega
                    exact ⟨rfl, _, rfl, trivial, by simp [binop, h1, h2, h3, h4, h5, h6, h7, h8, h9, semv, ht, hd]⟩
                  next => exact (refuse_ok h).elim

theorem runBytes_get (s0 : State) (base len k : Nat) (h : k < s0.reg len) : (runBytes s0 base len)[k]? = some (s0.mem (s0.reg base + k)).val := by
  simp [runBytes, h]

theorem scall_sound {ctx : Ctx} {s0 : State} {f : String} {vs : List SVal} {s s' : Sym} {res : SRes} {items rest : Items}
    {ρ : Nat → Int} {st : State} (h : scall ctx f vs s items = .ok ((res, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
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
            refine ⟨rfl, ?_, bounded_var (Nat.lt_of_lt_of_le hlt wf.regs)⟩
            simp only [List.map, semv, hreg] at ha
            have := Value.len ha
            simp only [SRes.sem, semv, ev_var, H.entry len hlt]
            simpa [runBytes] using this
  next hlen =>
    split at h
    next ho => exact (refuse_ok h).elim
    next ho =>
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
          exact Value.call (by simpa using hlen) (by simpa using ho) hd (by simpa using hp) ha x
        next => exact (refuse_ok h).elim

theorem ifx_finish {r res : SRes} {s2 s' : Sym} {r2 rest : Items}
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

/-- A remainder: what `Sym.quotRem` gives is the remainder there is. -/
theorem smod_sound {ctx : Ctx} {s0 : State} {s s' : Sym} {x y : Row} {res : SRes} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : smod s x y items = .ok ((res, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (hx : bounded s.nvars x) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ ∃ v, res = .val v ∧ v.bounded s'.nvars ∧
      binop "%" (.int (ev ρ x)) (.int (ev ρ y)) = some (semv ctx s0 ρ' v) := by
  cases hm : Lin.isConst y with
  | none => simp only [smod, hm] at h; exact (refuse_ok h).elim
  | some m =>
    simp only [smod, hm] at h
    split at h
    next pos =>
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      obtain ⟨ρ', c, _, nr, _, br⟩ := quotRem_sound (ctx := ctx) (s0 := s0) H wf hx pos
      refine ⟨ρ', c, _, rfl, br, ?_⟩
      have ym : ev ρ y = m := ev_isConst hm
      simp [binop, semv, nr, ym, pos]
    next => exact (refuse_ok h).elim

/-- A quotient: what `Sym.quotRem` gives is the quotient there is. -/
theorem sdiv_sound {ctx : Ctx} {s0 : State} {s s' : Sym} {x y : Row} {res : SRes} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : sdiv s x y items = .ok ((res, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (hx : bounded s.nvars x) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ ∃ v, res = .val v ∧ v.bounded s'.nvars ∧
      binop "/" (.int (ev ρ x)) (.int (ev ρ y)) = some (semv ctx s0 ρ' v) := by
  cases hm : Lin.isConst y with
  | none => simp only [sdiv, hm] at h; exact (refuse_ok h).elim
  | some m =>
    simp only [sdiv, hm] at h
    split at h
    next pos =>
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      obtain ⟨ρ', c, nq, _, bq, _⟩ := quotRem_sound (ctx := ctx) (s0 := s0) H wf hx pos
      refine ⟨ρ', c, _, rfl, bq, ?_⟩
      have ym : ev ρ y = m := ev_isConst hm
      simp [binop, semv, nq, ym, pos]
    next => exact (refuse_ok h).elim

theorem knownValue_mem : ∀ {facts : List SFact} {c : SCall} {v : Row}, knownValue facts c = some v → SFact.value c v ∈ facts
  | [], _, _, h => by simp [knownValue] at h
  | .same _ _ :: more, c, v, h => by
    simp only [knownValue] at h
    exact List.mem_cons_of_mem _ (knownValue_mem h)
  | .value c' v' :: more, c, v, h => by
    simp only [knownValue] at h
    split at h
    next e =>
      injection h with h
      have e' : c' = c := by simpa using e
      subst e' h
      exact List.mem_cons_self ..
    next => exact List.mem_cons_of_mem _ (knownValue_mem h)

theorem heldValues_mem : ∀ {facts : List SFact} {c : SCall} {v : Row}, (c, v) ∈ heldValues facts → SFact.value c v ∈ facts
  | [], _, _, h => by simp [heldValues] at h
  | .same _ _ :: more, c, v, h => by
    simp only [heldValues] at h
    exact List.mem_cons_of_mem _ (heldValues_mem h)
  | .value c' v' :: more, c, v, h => by
    simp only [heldValues, List.mem_cons] at h
    rcases h with h | h
    · injection h with h1 h2
      subst h1 h2
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (heldValues_mem h)

/-- The things two uses are used with, shown the same, mean the same. -/
theorem sameArgs_sound (ctx : Ctx) (s0 : State) {facts : List Row} {ρ : Nat → Int} (hf : ∀ g ∈ facts, g.holds ρ) :
    ∀ (as bs : List SVal) {items rest : Items}, sameArgs facts as bs items = .ok ((), rest) →
    as.map (semv ctx s0 ρ) = bs.map (semv ctx s0 ρ)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp only [sameArgs] at h; exact (refuse_ok h).elim
  | _ :: _, [], _, _, h => by simp only [sameArgs] at h; exact (refuse_ok h).elim
  | a :: as, b :: bs, items, rest, h => by
    cases a with
    | lin x =>
      cases b with
      | lin y =>
        simp only [sameArgs] at h
        obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
        obtain ⟨_, r2, e2, h⟩ := V.bind_ok h
        have g1 := entailAs_sound e1 ρ hf
        have g2 := entailAs_sound e2 ρ hf
        rw [ev_sub] at g1 g2
        have e : ev ρ x = ev ρ y := by omega
        simp only [List.map_cons, semv, e, sameArgs_sound ctx s0 hf as bs h]
      | region r =>
        simp only [sameArgs] at h
        split at h
        next hc => cases hc
        next => exact (refuse_ok h).elim
      | bool t =>
        simp only [sameArgs] at h
        split at h
        next hc => cases hc
        next => exact (refuse_ok h).elim
    | region r =>
      simp only [sameArgs] at h
      split at h
      next hc => subst hc; simp only [List.map_cons, sameArgs_sound ctx s0 hf as bs h]
      next => exact (refuse_ok h).elim
    | bool t =>
      simp only [sameArgs] at h
      split at h
      next hc => subst hc; simp only [List.map_cons, sameArgs_sound ctx s0 hf as bs h]
      next => exact (refuse_ok h).elim

/-- Two uses the verifier takes to have the same value have the same value. -/
theorem sameUse_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    {c c' : SCall} {items rest : Items} (h : sameUse s c c' items = .ok ((), rest)) : Eqv ctx s0 ρ c c' := by
  unfold sameUse at h
  split at h
  next hm =>
    have m : c' ∈ reach s.spec (s.spec.length + 1) [c] := by simpa using hm
    exact reach_sound c s.spec H.spec _ [c] (fun x mx => by simp only [List.mem_singleton] at mx; subst mx; exact fun _ => Iff.rfl) c' m
  next =>
    split at h
    next hf =>
      have ef : c'.f = c.f := by simpa using hf
      have ea := sameArgs_sound ctx s0 H.facts c.args c'.args h
      intro x
      simp only [CallValue, ef, ea]
    next => exact (refuse_ok h).elim

/-- What is asked of a way to open a use of a definition: what the verifier holds after it is so. -/
def DeeperSound (ctx : Ctx) (s0 : State) (deeper : Sym → SCall → V Sym) : Prop :=
  ∀ {s s' : Sym} {c : SCall} {items rest : Items} {ρ : Nat → Int} {st : State},
    deeper s c items = .ok (s', rest) → Holds ctx s0 ρ s st → WF ctx s → c.bounded s.nvars → ∃ ρ', Carried ctx s0 ρ s ρ' s' st

/-- The value the verifier takes a use of a definition to have is its value. -/
theorem heldFor_sound {ctx : Ctx} {s0 : State} {deeper : Sym → SCall → V Sym} (D : DeeperSound ctx s0 deeper)
    {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    {c : SCall} (hc : c.bounded s.nvars) {x : Row} {s' : Sym} {items rest : Items}
    (h : heldFor deeper s c items = .ok ((x, s'), rest)) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ CallValue ctx s0 ρ' c (.int (ev ρ' x)) ∧ bounded s'.nvars x := by
  unfold heldFor at h
  cases hk : knownValue s.spec c with
  | some v =>
    simp only [hk] at h
    have := V.pure_ok h
    injection this with h1 _
    injection h1 with h1 h2
    subst h1 h2
    have m := knownValue_mem hk
    exact ⟨ρ, Carried.here H wf, H.spec _ m, (wf.spec _ m).2⟩
  | none =>
    simp only [hk] at h
    obtain ⟨item, r1, _, h⟩ := V.bind_ok h
    cases item with
    | none => cases h
    | some it =>
      cases it with
      | proof _ _ => exact (refuse_ok h).elim
      | know _ => exact (refuse_ok h).elim
      | clear _ _ _ => exact (refuse_ok h).elim
      | tag name k =>
        simp only at h
        split at h
        next =>
          cases hv : (heldValues s.spec)[k]? with
          | none => simp only [hv] at h; exact (refuse_ok h).elim
          | some cv =>
            obtain ⟨c', v⟩ := cv
            simp only [hv] at h
            obtain ⟨_, r2, e2, h⟩ := V.bind_ok h
            have := V.pure_ok h
            injection this with h1 _
            injection h1 with h1 h2
            subst h1 h2
            have m := heldValues_mem (List.mem_of_getElem? hv)
            have same := sameUse_sound H e2
            exact ⟨ρ, Carried.here H wf, (same _).mpr (H.spec _ m), (wf.spec _ m).2⟩
        next =>
          split at h
          next =>
            obtain ⟨s1, r2, e2, h⟩ := V.bind_ok h
            obtain ⟨ρ1, c1⟩ := D e2 H wf hc
            cases hk1 : knownValue s1.spec c with
            | none => simp only [hk1] at h; exact (refuse_ok h).elim
            | some v =>
              simp only [hk1] at h
              have := V.pure_ok h
              injection this with h1 _
              injection h1 with h1 h2
              subst h1 h2
              have m := knownValue_mem hk1
              exact ⟨ρ1, c1, c1.holds.spec _ m, (c1.wf.spec _ m).2⟩
          next => exact (refuse_ok h).elim

/-- A result taken where a number is needed: the expression has that number as its value. -/
theorem numberV_sound {ctx : Ctx} {s0 : State} {deeper : Sym → SCall → V Sym} (D : DeeperSound ctx s0 deeper)
    {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    {env : List (String × Val)} {e : SExpr} {res : SRes} {x : Row} {s' : Sym} {items rest : Items}
    (h : numberV deeper s res items = .ok ((x, s'), rest)) (sem : res.sem ctx s0 ρ env e) (bd : res.bounded s.nvars) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ Value ctx.defs env e (.int (ev ρ' x)) ∧ bounded s'.nvars x := by
  cases res with
  | list _ => simp only [numberV] at h; exact (refuse_ok h).elim
  | val v =>
    cases v with
    | region _ => simp only [numberV] at h; exact (refuse_ok h).elim
    | bool _ => simp only [numberV] at h; exact (refuse_ok h).elim
    | lin y =>
      simp only [numberV] at h
      have := V.pure_ok h
      injection this with h1 _
      injection h1 with h1 h2
      subst h1 h2
      exact ⟨ρ, Carried.here H wf, sem, bd⟩
  | tail c =>
    simp only [numberV] at h
    obtain ⟨ρ1, c1, cv, b⟩ := heldFor_sound D H wf bd h
    exact ⟨ρ1, c1, (sem _).mpr ((CallValue_agree bd c1.agree _).mpr cv), b⟩

/-- A result taken as one of the things a definition is used with: the expression has that value. -/
theorem argumentV_sound {ctx : Ctx} {s0 : State} {deeper : Sym → SCall → V Sym} (D : DeeperSound ctx s0 deeper)
    {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    {env : List (String × Val)} {e : SExpr} {res : SRes} {v : SVal} {s' : Sym} {items rest : Items}
    (h : argumentV deeper s res items = .ok ((v, s'), rest)) (sem : res.sem ctx s0 ρ env e) (bd : res.bounded s.nvars) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ Value ctx.defs env e (semv ctx s0 ρ' v) ∧ v.bounded s'.nvars := by
  cases res with
  | list _ => simp only [argumentV] at h; exact (refuse_ok h).elim
  | val w =>
    simp only [argumentV] at h
    have := V.pure_ok h
    injection this with h1 _
    injection h1 with h1 h2
    subst h1 h2
    exact ⟨ρ, Carried.here H wf, sem, bd⟩
  | tail c =>
    simp only [argumentV] at h
    obtain ⟨⟨x, s1⟩, r1, e1, h⟩ := V.bind_ok h
    have := V.pure_ok h
    injection this with h1 _
    injection h1 with h1 h2
    subst h1 h2
    obtain ⟨ρ1, c1, cv, b⟩ := heldFor_sound D H wf bd e1
    exact ⟨ρ1, c1, (sem _).mpr ((CallValue_agree bd c1.agree _).mpr cv), b⟩

/-- An expression of the specification worked out on symbols: what comes out is what the expression means. -/
theorem sevalWith_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {deeper : Sym → SCall → V Sym}
    (D : DeeperSound ctx s0 deeper) (env : List (String × SVal)) :
    ∀ (e : SExpr) {s s' : Sym} {res : SRes} {items rest : Items} {ρ : Nat → Int} {st : State},
    sevalWith ctx deeper env s e items = .ok ((res, s'), rest) → Holds ctx s0 ρ s st → WF ctx s → EnvB s.nvars env →
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ res.sem ctx s0 ρ' (semEnv ctx s0 ρ' env) e ∧ res.bounded s'.nvars := by
  intro e
  induction e with
  | list _ _ =>
    intro s s' res items rest ρ st h H wf hb
    simp only [sevalWith] at h
    exact (refuse_ok h).elim
  | letx _ _ _ _ _ => intro s s' res items rest ρ st h H wf hb; simp only [sevalWith] at h; exact (refuse_ok h).elim
  | each _ _ _ _ _ _ _ => intro s s' res items rest ρ st h H wf hb; simp only [sevalWith] at h; exact (refuse_ok h).elim
  | slice _ _ _ _ _ _ => intro s s' res items rest ρ st h H wf hb; simp only [sevalWith] at h; exact (refuse_ok h).elim
  | withx _ _ _ _ => intro s s' res items rest ρ st h H wf hb; simp only [sevalWith] at h; exact (refuse_ok h).elim
  | record _ _ _ => intro s s' res items rest ρ st h H wf hb; simp only [sevalWith] at h; exact (refuse_ok h).elim
  | field _ _ _ => intro s s' res items rest ρ st h H wf hb; simp only [sevalWith] at h; exact (refuse_ok h).elim
  | theNumber _ _ _ _ _ _ _ _ => intro s s' res items rest ρ st h H wf hb; simp only [sevalWith] at h; exact (refuse_ok h).elim
  | thePower _ _ _ _ => intro s s' res items rest ρ st h H wf hb; simp only [sevalWith] at h; exact (refuse_ok h).elim
  | num n =>
    intro s s' res items rest ρ st h H wf hb
    simp only [sevalWith] at h
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
    simp only [sevalWith] at h
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
    simp only [sevalWith] at h
    have := V.pure_ok h
    injection this with hp _
    injection hp with e1 e2
    subst e1 e2
    exact ⟨ρ, Carried.here H wf, Values.nil, fun _ m => by cases m⟩
  | cons a more iha ihm =>
    intro s s' res items rest ρ st h H wf hb
    simp only [sevalWith] at h
    obtain ⟨⟨v, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨⟨vs, s2⟩, r2, e2, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1, sa, ba⟩ := iha e1 H wf hb
    have hb1 := hb.mono c1.mono
    obtain ⟨ρ2, c2, sm, bm⟩ := ihm e2 c1.holds c1.wf hb1
    have hb2 := hb1.mono c2.mono
    have sa2 := SRes.sem_agree sa ba hb1 c2.agree
    obtain ⟨⟨av, s3⟩, r3, e3, h⟩ := V.bind_ok h
    obtain ⟨ρ3, c3, va, bva⟩ := argumentV_sound D c2.holds c2.wf e3 sa2 (SRes.bounded_mono c2.mono ba)
    have sm3 := SRes.sem_agree sm bm hb2 c3.agree
    cases vs with
    | tail _ => exact (refuse_ok h).elim
    | val _ => exact (refuse_ok h).elim
    | list vs =>
      simp only at h
      have := V.pure_ok h
      injection this with hp _
      injection hp with e1 e2
      subst e1 e2
      refine ⟨ρ3, (c1.then c2).then c3, Values.cons ?_ sm3, ?_⟩
      · rw [← semEnv_agree hb2 c3.agree]; exact va
      · intro w m
        cases m with
        | head => exact bva
        | tail _ m => exact SVal.bounded_mono c3.mono (bm w m)
  | bin op a b iha ihb =>
    intro s s' res items rest ρ st h H wf hb
    simp only [sevalWith] at h
    obtain ⟨⟨x, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨⟨y, s2⟩, r2, e2, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1, sa, ba⟩ := iha e1 H wf hb
    have hb1 := hb.mono c1.mono
    obtain ⟨ρ2, c2, sb, bb⟩ := ihb e2 c1.holds c1.wf hb1
    have hb2 := hb1.mono c2.mono
    have sa2 := SRes.sem_agree sa ba hb1 c2.agree
    obtain ⟨⟨xr, s3⟩, r3, e3, h⟩ := V.bind_ok h
    obtain ⟨⟨yr, s4⟩, r4, e4, h⟩ := V.bind_ok h
    obtain ⟨ρ3, c3, vx, bx⟩ := numberV_sound D c2.holds c2.wf e3 sa2 (SRes.bounded_mono c2.mono ba)
    have hb3 := hb2.mono c3.mono
    have sb3 := SRes.sem_agree sb bb hb2 c3.agree
    obtain ⟨ρ4, c4, vy, by'⟩ := numberV_sound D c3.holds c3.wf e4 sb3 (SRes.bounded_mono c3.mono bb)
    have hb4 := hb3.mono c4.mono
    have vx4 : Value ctx.defs (semEnv ctx s0 ρ4 env) a (.int (ev ρ4 xr)) := by
      rw [← semEnv_agree hb3 c4.agree, ← semEnv_agree hb2 c3.agree, ← ev_agree bx c4.agree]; exact vx
    have vy4 : Value ctx.defs (semEnv ctx s0 ρ4 env) b (.int (ev ρ4 yr)) := by
      rw [← semEnv_agree hb3 c4.agree]; exact vy
    have bx4 := bounded_mono c4.mono bx
    split at h
    next hop =>
      have eop : op = "%" := by simpa using hop
      obtain ⟨ρ5, c5, v, hres, bv, hz⟩ := smod_sound h c4.holds c4.wf bx4
      subst hres
      refine ⟨ρ5, (((c1.then c2).then c3).then c4).then c5, ?_, bv⟩
      show Value ctx.defs (semEnv ctx s0 ρ5 env) (.bin op a b) (semv ctx s0 ρ5 v)
      rw [← semEnv_agree hb4 c5.agree, eop]
      exact Value.bin vx4 vy4 hz
    next =>
      split at h
      next hop =>
        have eop : op = "/" := by simpa using hop
        obtain ⟨ρ5, c5, v, hres, bv, hz⟩ := sdiv_sound h c4.holds c4.wf bx4
        subst hres
        refine ⟨ρ5, (((c1.then c2).then c3).then c4).then c5, ?_, bv⟩
        show Value ctx.defs (semEnv ctx s0 ρ5 env) (.bin op a b) (semv ctx s0 ρ5 v)
        rw [← semEnv_agree hb4 c5.agree, eop]
        exact Value.bin vx4 vy4 hz
      next =>
        obtain ⟨hs, v, hres, bv, hz⟩ := sbin_sound ctx s0 h c4.holds.facts bx4 by'
        subst hs hres
        exact ⟨ρ4, ((c1.then c2).then c3).then c4, Value.bin vx4 vy4 hz, bv⟩
  | index a i iha ihi =>
    intro s s' res items rest ρ st h H wf hb
    simp only [sevalWith] at h
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
    simp only [sevalWith] at h
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
    simp only [sevalWith] at h
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
  ⟨H.entry, H.data, H.reg, H.small, H.zf, H.cf, H.frame, H.facts, H.bytes,
   fun g m => by
     cases m with
     | head => exact hf
     | tail _ m => exact H.spec g m,
   H.mem, H.wrote, H.words, H.known, H.range⟩

theorem WF.withSpec {s : Sym} (wf : WF ctx s) (f : SFact) (hf : f.bounded s.nvars) : WF ctx { s with spec := f :: s.spec } :=
  ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.facts, wf.bytes,
   (fun g m => by
     cases m with
     | head => exact hf
     | tail _ m => exact wf.spec g m),
   wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, wf.range⟩

theorem openCallWith_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {deeper : Sym → SCall → V Sym}
    (D : DeeperSound ctx s0 deeper) : DeeperSound ctx s0 (openCallWith ctx deeper) := by
  intro s s' c items rest ρ st h H wf hc
  cases hd : findDef ctx.defs c.f with
  | none => simp only [openCallWith, hd] at h; exact (refuse_ok h).elim
  | some d =>
    simp only [openCallWith, hd] at h
    split at h
    next => exact (refuse_ok h).elim
    next =>
      obtain ⟨⟨res, s1⟩, r1, e1, h⟩ := V.bind_ok h
      have hbenv : EnvB s.nvars (d.params.zip c.args) := fun nv m => hc nv.2 (mem_zip_right m)
      obtain ⟨ρ1, c1, sem, bd⟩ := sevalWith_sound E D _ d.body e1 H wf hbenv
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

/-- Opening a use of a definition, to any depth: what the verifier holds after it is so. -/
theorem opener_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) : ∀ n, DeeperSound ctx s0 (opener ctx n)
  | 0 => by
    intro h H wf hc
    simp only [opener] at h
    exact (refuse_ok h).elim
  | n + 1 => by
    intro h H wf hc
    simp only [opener] at h
    exact openCallWith_sound E (opener_sound E n) h H wf hc

/-- An expression of the specification worked out on symbols: what comes out is what the expression means. -/
theorem seval_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (env : List (String × SVal)) :
    ∀ (e : SExpr) {s s' : Sym} {res : SRes} {items rest : Items} {ρ : Nat → Int} {st : State},
    seval ctx env s e items = .ok ((res, s'), rest) → Holds ctx s0 ρ s st → WF ctx s → EnvB s.nvars env →
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ res.sem ctx s0 ρ' (semEnv ctx s0 ρ' env) e ∧ res.bounded s'.nvars :=
  fun e => sevalWith_sound E (opener_sound E DEEP) env e

theorem openCall_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : SCall}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : openCall ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hc : c.bounded s.nvars) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st :=
  openCallWith_sound E (opener_sound E DEEP) h H wf hc

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

/-- A fact of a value carried over from a value held: it is so. -/
theorem carry_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    {goal : SFact} {k : Nat} {items rest : Items} (h : carry s goal k items = .ok ((), rest)) : goal.holds ctx s0 ρ := by
  unfold carry at h
  cases goal with
  | same a b => simp only at h; exact (refuse_ok h).elim
  | value c v =>
    cases hv : (heldValues s.spec)[k]? with
    | none => simp only [hv] at h; exact (refuse_ok h).elim
    | some cv =>
      obtain ⟨c', v'⟩ := cv
      simp only [hv] at h
      obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
      obtain ⟨_, r2, e2, e3⟩ := V.bind_ok h
      have g1 := entail_sound e2 ρ H.facts
      have g2 := entail_sound e3 ρ H.facts
      rw [ev_sub] at g1 g2
      have e : ev ρ v = ev ρ v' := by omega
      have m := heldValues_mem (List.mem_of_getElem? hv)
      have same := sameUse_sound H e1
      show CallValue ctx s0 ρ c (.int (ev ρ v))
      rw [e]
      exact (same _).mpr (H.spec _ m)

/-- A fact of the specification the verifier has come to: it is so. -/
theorem specGoal_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) :
    ∀ (fuel : Nat) {s s' : Sym} {goal : SFact} {items rest : Items} {ρ : Nat → Int} {st : State},
    specGoal ctx fuel s goal items = .ok (s', rest) → Holds ctx s0 ρ s st → WF ctx s → goal.bounded s.nvars →
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
        | know _ => exact (refuse_ok h).elim
        | clear _ _ _ => exact (refuse_ok h).elim
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
          next =>
            split at h
            next =>
              obtain ⟨_, r2, e1, h⟩ := V.bind_ok h
              have := V.pure_ok h
              injection this with h1 _
              subst h1
              exact ⟨ρ, Carried.here H wf, carry_sound H e1⟩
            next => exact (refuse_ok h).elim

/-! ## The contract's names -/

theorem symEnvIn_bounded (c : Contract) {N : Nat} : ∀ (args : List (String × Kind)) (regs : List Nat) (k : Nat),
    (∀ r ∈ regs, r < N) → EnvB N (symEnvIn c args regs k)
  | [], _, _, _ => by intro nv m; simp [symEnvIn] at m
  | _ :: _, [], _, _ => by intro nv m; simp [symEnvIn] at m
  | (n, .number) :: args, r :: regs, k, hr => by
    intro nv m
    simp only [symEnvIn, List.mem_cons] at m
    rcases m with rfl | m
    · exact bounded_var (hr r (List.mem_cons_self ..))
    · exact symEnvIn_bounded c args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m')) nv m
  | (n, .out _) :: args, r :: regs, k, hr => by
    intro nv m
    simp only [symEnvIn] at m
    exact symEnvIn_bounded c args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m')) nv m
  | (n, .fixed _) :: args, r :: regs, k, hr => by
    intro nv m
    simp only [symEnvIn] at m
    exact symEnvIn_bounded c args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m')) nv m
  | (n, .inout _) :: args, r :: regs, k, hr => by
    intro nv m
    simp only [symEnvIn] at m
    exact symEnvIn_bounded c args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m')) nv m
  | (n, .bytes len) :: args, r :: regs, k, hr => by
    intro nv m
    simp only [symEnvIn] at m
    split at m
    · simp only [List.mem_cons] at m
      rcases m with rfl | m
      · trivial
      · exact symEnvIn_bounded c args regs (k + 1) (fun r' m' => hr r' (List.mem_cons_of_mem _ m')) nv m
    · exact symEnvIn_bounded c args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m')) nv m

theorem symEnv_bounded (c : Contract) : EnvB c.regs (symEnv c) :=
  symEnvIn_bounded c c.args c.argRegs 0 (fun _ m => argRegs_lt m)

theorem semEnv_symEnvIn (ctx : Ctx) (s0 : State) (ρ : Nat → Int) {N : Nat} (hρ : ∀ r, r < N → ρ r = s0.reg r) :
    ∀ (args : List (String × Kind)) (regs : List Nat) (k : Nat), (∀ r ∈ regs, r < N) →
    (∀ j, (regionsIn ctx.contract args regs)[j]? = ctx.contract.regions[k + j]?) →
    semEnv ctx s0 ρ (symEnvIn ctx.contract args regs k) = envIn ctx.contract s0 args regs
  | [], _, _, _, _ => by simp [symEnvIn, envIn, semEnv]
  | _ :: _, [], _, _, _ => by simp [symEnvIn, envIn, semEnv]
  | (n, .number) :: args, r :: regs, k, hr, hj => by
    have ih := semEnv_symEnvIn ctx s0 ρ hρ args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m'))
      (by intro j; have := hj j; simpa only [regionsIn] using this)
    simp only [symEnvIn, envIn, semEnv, List.map_cons, semv, ev_var] at ih ⊢
    rw [hρ r (hr r (List.mem_cons_self ..)), ih]
  | (n, .out _) :: args, r :: regs, k, hr, hj => by
    have ih := semEnv_symEnvIn ctx s0 ρ hρ args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m'))
      (by intro j; have := hj j; simpa only [regionsIn] using this)
    simp only [symEnvIn, envIn]
    exact ih
  | (n, .fixed _) :: args, r :: regs, k, hr, hj => by
    have ih := semEnv_symEnvIn ctx s0 ρ hρ args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m'))
      (by intro j; have := hj j; simpa only [regionsIn] using this)
    simp only [symEnvIn, envIn]
    exact ih
  | (n, .inout _) :: args, r :: regs, k, hr, hj => by
    have ih := semEnv_symEnvIn ctx s0 ρ hρ args regs k (fun r' m' => hr r' (List.mem_cons_of_mem _ m'))
      (by intro j; have := hj j; simpa only [regionsIn] using this)
    simp only [symEnvIn, envIn]
    exact ih
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
theorem semEnv_symEnv (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (hρ : ∀ r, r < ctx.nreg → ρ r = s0.reg r) :
    semEnv ctx s0 ρ (symEnv ctx.contract) = ctx.contract.env s0 :=
  semEnv_symEnvIn ctx s0 ρ hρ ctx.contract.args ctx.contract.argRegs 0 (fun _ m => argRegs_lt m) (by intro j; simp [Contract.regions])

end Ode
