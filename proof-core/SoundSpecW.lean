import SoundCall
import SoundList
import SoundVec

/-!
# The specification on words: what `weval` gives is what the account's `evalSpec` gives

`weval` (Core.lean) works an expression of the specification out on the terms of the table. Here: the value
it gives stands for the value `evalSpec` gives with the same fuel, the names being the contract's at entry.
So an `ensures` of a whole run of words that the verifier has passed holds of the machine's state.
-/

namespace Ode

open Arithmetic

/-- The four bytes of each word, the lowest first (as `ofWords` of the account gives them). -/
def wordBytes : List Nat → List Val
  | [] => []
  | w :: rest => .int (w % 256 : Nat) :: .int (w / 256 % 256 : Nat) :: .int (w / 65536 % 256 : Nat) :: .int (w / 16777216 % 256 : Nat) :: wordBytes rest

/-- What a value on words stands for, the unknowns being `ρ` and the table `T`: a value of the account. -/
inductive WDen (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (T : List Node) : WVal → Val → Prop
  | int (n : Int) : WDen ctx s0 ρ T (.int n) (.int n)
  | bool (b : Bool) : WDen ctx s0 ρ T (.bool b) (.bool b)
  | num (r : Row) : WDen ctx s0 ρ T (.num r) (.int (ev ρ r))
  | word (xs : List Nat) : WDen ctx s0 ρ T (.word xs) (.word (sumList (xs.map (den (inpOf ctx s0) ρ T)) % W32))
  | counter (r : Row) (h : 0 ≤ ev ρ r) : WDen ctx s0 ρ T (.counter r) (.counter ((ev ρ r).toNat % 2 ^ 64))
  | nil : WDen ctx s0 ρ T (.list []) (.list [])
  | cons {v : WVal} {a : Val} {vs : List WVal} {as : List Val} :
      WDen ctx s0 ρ T v a → WDen ctx s0 ρ T (.list vs) (.list as) → WDen ctx s0 ρ T (.list (v :: vs)) (.list (a :: as))
  | run (r n : Nat) (hb : ∀ k, k < n → s0.mem (s0.reg r + k) < 256) :
      WDen ctx s0 ρ T (.run r n) (.list ((List.range n).map fun k => Val.int (s0.mem (s0.reg r + k))))
  | part (r off n : Nat) (hb : ∀ k, k < n → s0.mem (s0.reg r + off + k) < 256) :
      WDen ctx s0 ρ T (.part r off n) (.list ((List.range n).map fun k => Val.int (s0.mem (s0.reg r + off + k))))
  | wbytes (ids : List Nat) : WDen ctx s0 ρ T (.wbytes ids) (.list (wordBytes (ids.map (den (inpOf ctx s0) ρ T))))
  | rnil : WDen ctx s0 ρ T (.record []) (.record [])
  | rcons {x : String} {v : WVal} {a : Val} {fs : List (String × WVal)} {fs' : List (String × Val)} :
      WDen ctx s0 ρ T v a → WDen ctx s0 ρ T (.record fs) (.record fs') → WDen ctx s0 ρ T (.record ((x, v) :: fs)) (.record ((x, a) :: fs'))
  | lanes (j count l : Nat) (x : String) (r : Nat) (h : ctx.contract.tableAt j = some (x, r, count, l)) :
      WDen ctx s0 ρ T (.lanes j count l) (.list ((List.range count).map fun i => laneBlocks s0.mem (lanePtr s0 r i) (s0.reg l)))
  | lane (j c l : Nat) (x : String) (r count : Nat) (h : ctx.contract.tableAt j = some (x, r, count, l)) (hc : c % 8 = 0) (hi : c / 8 < count) :
      WDen ctx s0 ρ T (.lane j c l) (laneBlocks s0.mem (lanePtr s0 r (c / 8)) (s0.reg l))
  | other (a : Val) : WDen ctx s0 ρ T .other a

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {T : List Node}

theorem WDen.int_inv {n : Int} {a : Val} (h : WDen ctx s0 ρ T (.int n) a) : a = .int n := by cases h; rfl
theorem WDen.bool_inv {b : Bool} {a : Val} (h : WDen ctx s0 ρ T (.bool b) a) : a = .bool b := by cases h; rfl
theorem WDen.list_inv {l : List WVal} {a : Val} (h : WDen ctx s0 ρ T (.list l) a) : ∃ l', a = .list l' := by
  cases h with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

theorem WDen.length : ∀ {l : List WVal} {l' : List Val}, WDen ctx s0 ρ T (.list l) (.list l') → l.length = l'.length
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by
    cases h with
    | cons h1 h2 => simp [WDen.length h2]

theorem WDen.getElem? : ∀ {l : List WVal} {l' : List Val} {k : Nat} {v : WVal}, WDen ctx s0 ρ T (.list l) (.list l') → l[k]? = some v →
    ∃ a, l'[k]? = some a ∧ WDen ctx s0 ρ T v a
  | [], _, _, _, _, hk => by simp at hk
  | x :: xs, _, k, v, h, hk => by
    cases h with
    | cons h1 h2 =>
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero] at hk
        injection hk with hk; subst hk
        exact ⟨_, by simp, h1⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        obtain ⟨a, ha, hd⟩ := WDen.getElem? h2 hk
        exact ⟨a, by simpa using ha, hd⟩

theorem WDen.append : ∀ {l1 : List WVal} {l1' : List Val} {l2 : List WVal} {l2' : List Val}, WDen ctx s0 ρ T (.list l1) (.list l1') →
    WDen ctx s0 ρ T (.list l2) (.list l2') → WDen ctx s0 ρ T (.list (l1 ++ l2)) (.list (l1' ++ l2'))
  | [], _, _, _, h1, h2 => by cases h1; exact h2
  | _ :: _, _, _, _, h1, h2 => by
    cases h1 with
    | cons ha hr => exact WDen.cons ha (WDen.append hr h2)

theorem WDen.set : ∀ {l : List WVal} {l' : List Val} {k : Nat} {x : WVal} {a : Val}, WDen ctx s0 ρ T (.list l) (.list l') →
    WDen ctx s0 ρ T x a → WDen ctx s0 ρ T (.list (l.set k x)) (.list (l'.set k a))
  | [], _, _, _, _, h, _ => by cases h; exact WDen.nil
  | _ :: _, _, k, _, _, h, hx => by
    cases h with
    | cons h1 h2 =>
      cases k with
      | zero => exact WDen.cons hx h2
      | succ k => exact WDen.cons h1 (WDen.set h2 hx)

/-- The names on words stand for the names of the account, one for one. -/
def EnvDen (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (T : List Node) : List (String × WVal) → List (String × Val) → Prop
  | [], [] => True
  | (x, v) :: e, (y, a) :: e' => x = y ∧ WDen ctx s0 ρ T v a ∧ EnvDen ctx s0 ρ T e e'
  | _, _ => False

theorem EnvDen.lookup {x : String} : ∀ {env : List (String × WVal)} {env' : List (String × Val)} {v : WVal},
    EnvDen ctx s0 ρ T env env' → env.lookup x = some v → ∃ a, env'.lookup x = some a ∧ WDen ctx s0 ρ T v a
  | [], [], _, _, h => by simp at h
  | [], _ :: _, _, hE, _ => by simp [EnvDen] at hE
  | _ :: _, [], _, hE, _ => by simp [EnvDen] at hE
  | (y, w) :: e, (y', a) :: e', v, hE, h => by
    obtain ⟨rfl, hw, hE'⟩ := hE
    simp only [List.lookup] at h ⊢
    cases hxy : x == y with
    | true =>
      simp only [hxy] at h ⊢
      injection h with h; subst h
      exact ⟨a, rfl, hw⟩
    | false =>
      simp only [hxy] at h ⊢
      exact EnvDen.lookup hE' h

theorem EnvDen.zip : ∀ {ps : List String} {vs : List WVal} {as : List Val}, WDen ctx s0 ρ T (.list vs) (.list as) →
    EnvDen ctx s0 ρ T (ps.zip vs) (ps.zip as)
  | [], _, _, _ => by simp [EnvDen]
  | _ :: _, [], _, h => by cases h; simp [EnvDen]
  | p :: ps, _ :: _, _, h => by
    cases h with
    | cons h1 h2 => exact ⟨rfl, h1, EnvDen.zip h2⟩

theorem WDen.record_inv {fs : List (String × WVal)} {a : Val} (h : WDen ctx s0 ρ T (.record fs) a) : ∃ fs', a = .record fs' := by
  cases h with
  | rnil => exact ⟨_, rfl⟩
  | rcons _ _ => exact ⟨_, rfl⟩

/-- A record of the things of a list, by names: of both sides alike. -/
theorem WDen.zipRecord : ∀ {ps : List String} {vs : List WVal} {as : List Val}, WDen ctx s0 ρ T (.list vs) (.list as) →
    WDen ctx s0 ρ T (.record (ps.zip vs)) (.record (ps.zip as))
  | [], _, _, _ => by simp only [List.zip_nil_left]; exact WDen.rnil
  | _ :: _, [], _, h => by cases h; simp only [List.zip_nil_right]; exact WDen.rnil
  | p :: ps, _ :: _, _, h => by
    cases h with
    | cons h1 h2 => exact WDen.rcons h1 (WDen.zipRecord h2)

theorem WDen.lookupRecord {x : String} : ∀ {fs : List (String × WVal)} {fs' : List (String × Val)} {v : WVal},
    WDen ctx s0 ρ T (.record fs) (.record fs') → fs.lookup x = some v → ∃ a, fs'.lookup x = some a ∧ WDen ctx s0 ρ T v a
  | [], _, _, _, h => by simp at h
  | (y, w) :: fs, _, v, hd, h => by
    cases hd with
    | rcons hw hrest =>
      simp only [List.lookup] at h ⊢
      cases hxy : x == y with
      | true =>
        simp only [hxy] at h ⊢
        injection h with h; subst h
        exact ⟨_, rfl, hw⟩
      | false =>
        simp only [hxy] at h ⊢
        exact WDen.lookupRecord hrest h

end

theorem heldIds_mem {f : String} {keys : List Key} : ∀ {l : List Known} {ids : List Nat}, heldIds f keys l = some ids → Known.held f keys ids ∈ l
  | [], _, h => by simp [heldIds] at h
  | k :: more, ids, h => by
    cases k with
    | held f' keys' ids' =>
      simp only [heldIds] at h
      split at h
      next e =>
        injection h with h
        obtain ⟨e1, e2⟩ := e
        subst h e1 e2
        exact List.mem_cons_self ..
      next => exact List.mem_cons_of_mem _ (heldIds_mem h)
    | load v j c => simp only [heldIds] at h; exact List.mem_cons_of_mem _ (heldIds_mem h)
    | or v x y => simp only [heldIds] at h; exact List.mem_cons_of_mem _ (heldIds_mem h)
    | block j c off vs => simp only [heldIds] at h; exact List.mem_cons_of_mem _ (heldIds_mem h)

/-- Every use of a definition that the state holds the words of: the definition gives those words within
`B` steps. -/
def HeldWithin (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (T : List Node) (known : List Known) (B : Nat) : Prop :=
  ∀ f keys ids, Known.held f keys ids ∈ known → ∃ d, findDef ctx.defs f = some d ∧ d.params.length = keys.length ∧
    evalSpec ctx.defs B (d.params.zip (keys.map (Key.val ctx s0 ρ T))) d.body =
      some (.list (ids.map fun i => Val.word (den (inpOf ctx s0) ρ T i)))

/-- There is such a number of steps: the largest any of them needs. -/
theorem held_bound_list (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (T : List Node) : ∀ (l : List Known),
    (∀ k ∈ l, k.holds ctx s0 ρ T) → ∃ B, HeldWithin ctx s0 ρ T l B
  | [], _ => ⟨0, fun _ _ _ m => nomatch m⟩
  | k :: more, h => by
    obtain ⟨B, hB⟩ := held_bound_list ctx s0 ρ T more (fun k' m => h k' (List.mem_cons_of_mem _ m))
    cases k with
    | held f keys ids =>
      obtain ⟨d, hd, hlen, fuel, hev⟩ := h _ (List.mem_cons_self ..)
      refine ⟨max B fuel, ?_⟩
      intro f' keys' ids' m
      rcases List.mem_cons.mp m with e | m
      · injection e with e1 e2 e3
        subst e1 e2 e3
        exact ⟨d, hd, hlen, evalSpec_mono _ fuel hev _ (Nat.le_max_right _ _)⟩
      · obtain ⟨d', hd', hlen', hev'⟩ := hB f' keys' ids' m
        exact ⟨d', hd', hlen', evalSpec_mono _ B hev' _ (Nat.le_max_left _ _)⟩
    | load v j c =>
      refine ⟨B, ?_⟩
      intro f' keys' ids' m
      rcases List.mem_cons.mp m with e | m
      · cases e
      · exact hB _ _ _ m
    | or v x y =>
      refine ⟨B, ?_⟩
      intro f' keys' ids' m
      rcases List.mem_cons.mp m with e | m
      · cases e
      · exact hB _ _ _ m
    | block j c off vs =>
      refine ⟨B, ?_⟩
      intro f' keys' ids' m
      rcases List.mem_cons.mp m with e | m
      · cases e
      · exact hB _ _ _ m


/-! ## What is looked up -/

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

/-- A division the facts held already say: the unknowns are the quotient and the remainder. -/
theorem divided_spec (H : Holds ctx s0 ρ s st) {x : Row} {m : Int} (pos : 0 < m) {q : Nat} (hd : divided s x m = some q) :
    ρ q = ev ρ x / m ∧ ρ (q + 1) = ev ρ x % m := by
  have hq := List.find?_some hd
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hq
  obtain ⟨_, ⟨⟨m1, m2⟩, m3⟩, m4⟩ := hq
  have f1 := H.facts _ m1
  have f2 := H.facts _ m2
  have f3 := H.facts _ m3
  have f4 := H.facts _ m4
  rw [holds_iff] at f1 f2 f3 f4
  simp only [ev_sub, ev_add, ev_scale, ev_var, ev_const] at f1 f2 f3 f4
  have u := (Int.ediv_emod_unique (a := ev ρ x) (r := ρ (q + 1)) (q := ρ q) pos).mpr ⟨by omega, f3, by omega⟩
  exact ⟨u.1.symm, u.2.symm⟩

theorem knownNonneg_sound (H : Holds ctx s0 ρ s st) {r : Row} (h : knownNonneg s r = true) : 0 ≤ ev ρ r := by
  unfold knownNonneg at h
  split at h
  next k hk => rw [ev_isConst hk]; simpa using h
  next =>
    have := H.facts r (List.contains_iff_mem.mp h)
    rw [holds_iff] at this; exact this

theorem lowOf_sound (H : Holds ctx s0 ρ s st) {x r : Row} {m : Int} (pos : 0 < m) (h : lowOf s x m = some r) : ev ρ r = ev ρ x % m := by
  unfold lowOf at h
  split at h
  next hk =>
    injection h with h; subst h
    rw [ev_const, ev_low_exact hk]
  next =>
    split at h
    next hs =>
      injection h with h; subst h
      simp only [Bool.and_eq_true] at hs
      have g0 := knownNonneg_sound H hs.1
      have g1 := plain_sound hs.2 ρ H.facts
      simp only [ev_sub, ev_const] at g1
      exact (Int.emod_eq_of_lt g0 (by omega)).symm
    next =>
      cases hd : divided s x m with
      | none => simp [hd] at h
      | some q =>
        simp only [hd, Option.map_some] at h
        injection h with h; subst h
        rw [ev_var]; exact (divided_spec H pos hd).2

theorem highOf_sound (H : Holds ctx s0 ρ s st) {x q : Row} (h : highOf s x = some q) : ev ρ q = ev ρ x / W32i := by
  unfold highOf at h
  split at h
  next =>
    cases hd : divided s x W32i with
    | none => simp [hd] at h
    | some k =>
      simp only [hd, Option.map_some] at h
      injection h with h; subst h
      rw [ev_var]; exact (divided_spec H (by decide) hd).1
  next =>
    split at h
    next hc =>
      injection h with h; subst h
      cases hk : Lin.isConst (Lin.word x) with
      | none => simp [hk] at hc
      | some cst =>
        have e1 := ev_isConst (ρ := ρ) hk
        have e2 : cst = x.constant % W32i := isConst_constant hk
        have eh := ev_high ρ x
        have c0 := Int.emod_nonneg x.constant (show W32i ≠ 0 by decide)
        have c1 := Int.emod_lt_of_pos x.constant (show (0 : Int) < W32i by decide)
        rw [e1, e2] at eh
        unfold W32i at eh c0 c1 ⊢
        omega
    next => cases h

/-- Every term of the state's table is a word. -/
theorem Holds.den_lt (wf : WF s) (i : Nat) : den (inpOf ctx s0) ρ s.terms i < W32 :=
  Ode.den_lt wf.words.table (inpOf_lt ctx s0) wf.words.rotrs i

/-- The term a word is, where it is one: the sum of the word's terms, wrapping. -/
theorem idOf_den (wf : WF s) {xs : List Nat} {a : Nat} (h : idOf (fun n => findNode n s.terms 0) xs = some a) :
    den (inpOf ctx s0) ρ s.terms a = sumList (xs.map (den (inpOf ctx s0) ρ s.terms)) % W32 := by
  have key : ∀ ys, findNode (.add ys) s.terms 0 = some a →
      den (inpOf ctx s0) ρ s.terms a = sumList (ys.map (den (inpOf ctx s0) ρ s.terms)) % W32 := by
    intro ys hf
    have hn := (findNode_spec _ _ _ _ hf).2
    rw [den_node wf.words.table (by simpa using hn)]
    rfl
  match xs, h with
  | [], h => exact key [] h
  | [b], h =>
    simp only [idOf] at h
    injection h with h; subst h
    simp only [List.map, sumList, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (Holds.den_lt wf b)).symm
  | b :: c :: more, h => exact key _ h

/-- A term found in the table: it is what its node says. -/
theorem found_den (wf : WF s) {n : Node} {i : Nat} (h : findNode n s.terms 0 = some i) :
    den (inpOf ctx s0) ρ s.terms i = n.value (inpOf ctx s0) ρ (den (inpOf ctx s0) ρ s.terms) := by
  have hn := (findNode_spec _ _ _ _ h).2
  exact den_node wf.words.table (by simpa using hn)

/-- One term as a word. -/
theorem WDen.one (wf : WF s) (i : Nat) :
    WDen ctx s0 ρ s.terms (.word [i]) (.word (den (inpOf ctx s0) ρ s.terms i)) := by
  have h := WDen.word (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) [i]
  simp only [List.map, sumList, Nat.add_zero, Nat.mod_eq_of_lt (Holds.den_lt (ctx := ctx) (s0 := s0) (ρ := ρ) wf i)] at h
  exact h

/-- The terms of a list, each as a word. -/
theorem WDen.wordsOf (wf : WF s) : ∀ (ids : List Nat),
    WDen ctx s0 ρ s.terms (.list (ids.map fun i => WVal.word [i])) (.list (ids.map fun i => Val.word (den (inpOf ctx s0) ρ s.terms i)))
  | [] => WDen.nil
  | i :: rest => WDen.cons (WDen.one wf i) (WDen.wordsOf wf rest)

/-! ## A block of a lane -/

theorem sameRow_sound {facts : List Row} {ρ : Nat → Int} (hf : ∀ f ∈ facts, f.holds ρ) {a b : Row}
    (h : sameRow facts a b = true) : ev ρ a = ev ρ b := by
  simp only [sameRow, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
  rcases h with h | ⟨h1, h2⟩
  · rw [h]
  · have g1 := plainTimes_sound h1 ρ hf
    have g2 := plainTimes_sound h2 ρ hf
    rw [ev_sub] at g1 g2
    omega

/-- Two numbers held as rows: what `wnum` gives of them is what the account's `binop` gives of the numbers. -/
theorem wnum_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    {op : String} {x y : Row} {v : WVal} (h : wnum s op x y = some v) :
    ∃ a, binop op (.int (ev ρ x)) (.int (ev ρ y)) = some a ∧ WDen ctx s0 ρ s.terms v a := by
  unfold wnum at h
  split at h
  next hop =>
    have oe : op = "+" := by simpa using hop
    subst oe
    injection h with h; subst h
    refine ⟨.int (ev ρ x + ev ρ y), by simp [binop], ?_⟩
    have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.add x y)
    rw [ev_add] at this; exact this
  next =>
    split at h
    next hop =>
      have oe : op = "-" := by simpa using hop
      subst oe
      split at h
      next hp =>
        injection h with h; subst h
        have g := plain_sound hp ρ H.facts
        rw [ev_sub] at g
        have g' : ev ρ y ≤ ev ρ x := by omega
        refine ⟨.int (ev ρ x - ev ρ y), by simp [binop, g'], ?_⟩
        have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.sub x y)
        rw [ev_sub] at this; exact this
      next => cases h
    next =>
      split at h
      next hop =>
        have oe : op = "==" := by simpa using hop
        subst oe
        split at h
        next hs =>
          injection h with h; subst h
          have e := sameRow_sound H.facts hs
          exact ⟨.bool true, by simp [binop, e], WDen.bool true⟩
        next =>
          split at h
          next hd =>
            injection h with h; subst h
            have ne : ev ρ x ≠ ev ρ y := by
              rcases Bool.or_eq_true_iff.mp hd with hd | hd
              · have g := plain_sound hd ρ H.facts
                simp only [ev_sub, ev_const] at g
                omega
              · have g := plain_sound hd ρ H.facts
                simp only [ev_sub, ev_const] at g
                omega
            exact ⟨.bool false, by simp [binop, ne], WDen.bool false⟩
          next => cases h
      next => cases h

theorem knownBlock_mem {facts : List Row} {j c : Nat} {off : Row} : ∀ {l : List Known} {vs : List Nat},
    knownBlock facts j c off l = some vs → ∃ off', Known.block j c off' vs ∈ l ∧ sameRow facts off' off = true
  | [], _, h => by simp [knownBlock] at h
  | k :: more, vs, h => by
    cases k with
    | block j' c' off' vs' =>
      simp only [knownBlock] at h
      split at h
      next e =>
        injection h with h
        obtain ⟨e1, e2, e3⟩ := e
        subst h e1 e2
        exact ⟨off', List.mem_cons_self .., e3⟩
      next =>
        obtain ⟨o, m, hs⟩ := knownBlock_mem h
        exact ⟨o, List.mem_cons_of_mem _ m, hs⟩
    | load _ _ _ | or _ _ _ | held _ _ _ =>
      simp only [knownBlock] at h
      obtain ⟨o, m, hs⟩ := knownBlock_mem h
      exact ⟨o, List.mem_cons_of_mem _ m, hs⟩

/-- Unknowns whose terms are in the table, as words: each is its unknown's remainder by 2^32. -/
theorem atomWords_sound (wf : WF s) : ∀ {vs : List Nat} {ws : List WVal},
    atomWords (fun n => findNode n s.terms 0) vs = some ws →
    WDen ctx s0 ρ s.terms (.list ws) (.list (vs.map fun v => Val.word ((ρ v % W32i).toNat)))
  | [], _, h => by simp only [atomWords, Option.some.injEq] at h; subst h; exact WDen.nil
  | v :: more, ws, h => by
    simp only [atomWords] at h
    cases hf : findNode (.atom (Lin.word (Lin.var v))) s.terms 0 with
    | none => simp [hf] at h
    | some i =>
      cases hr : atomWords (fun n => findNode n s.terms 0) more with
      | none => simp [hf, hr] at h
      | some rest =>
        simp only [hf, hr, Option.some.injEq] at h; subst h
        have hd := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hf
        simp only [Node.value] at hd
        rw [ev_word, ev_var] at hd
        have one := WDen.one (ctx := ctx) (s0 := s0) (ρ := ρ) wf i
        rw [hd] at one
        exact WDen.cons one (atomWords_sound wf hr)

/-- The block `weval` finds at byte `off` of a lane is the block the account has at that place of the lane:
the function read it there, within the lane's blocks. -/
theorem blockAt_sound (H : Holds ctx s0 ρ s st) (wf : WF s) {j c : Nat} {off : Row} {v : WVal}
    (h : blockAt (fun n => findNode n s.terms 0) s j c off = some v) {k : Int} (hk : ev ρ off = 64 * k)
    {x : String} {r count l : Nat} (ht : ctx.contract.tableAt j = some (x, r, count, l)) :
    0 ≤ k ∧ ∃ a, ((List.range (s0.reg l)).map fun b => blockWords s0.mem (lanePtr s0 r (c / 8) + 64 * b))[k.toNat]? = some a ∧
      WDen ctx s0 ρ s.terms v a := by
  unfold blockAt at h
  obtain ⟨vs, hkb, hws⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ws, haw, rfl⟩ := Option.map_eq_some_iff.mp hws
  obtain ⟨off', m, same⟩ := knownBlock_mem hkb
  obtain ⟨x', r', count', l', ht', c8, clt, o0, o1, len, words⟩ := H.known _ m
  rw [ht] at ht'
  simp only [Option.some.injEq, Prod.mk.injEq] at ht'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ht'
  have eo := sameRow_sound H.facts same
  rw [eo, hk] at o0 o1
  have k0 : 0 ≤ k := by omega
  have klt : k.toNat < s0.reg l := by omega
  refine ⟨k0, _, by rw [List.getElem?_map, List.getElem?_range klt]; rfl, ?_⟩
  have hw := atomWords_sound (ctx := ctx) (s0 := s0) (ρ := ρ) wf haw
  have e : (vs.map fun v => Val.word ((ρ v % W32i).toNat)) =
      (List.range 16).map fun w => Val.word (load s0.mem (lanePtr s0 r (c / 8) + 64 * k.toNat + 4 * w) 4) := by
    apply List.ext_getElem
    · simp [len]
    · intro w h1 h2
      have hw16 : w < 16 := by simpa using h2
      simp only [List.getElem_map, List.getElem_range]
      have hval := words w hw16
      rw [getD_index (by omega) 0, eo, hk] at hval
      have lt := load_lt s0.mem (lanePtr s0 r (c / 8) + (64 * k).toNat + 4 * w) 4
      have p4 : (256 : Nat) ^ 4 = 4294967296 := by decide
      rw [p4] at lt
      have ek : (64 * k).toNat = 64 * k.toNat := by omega
      rw [ek] at hval lt
      rw [hval]
      congr 1
      unfold W32i
      omega
  rw [e] at hw
  exact hw

/-- The terms of a list of words, where each is one: the words are those terms'. -/
theorem wordIds_den (wf : WF s) : ∀ {l : List WVal} {l' : List Val} {ids : List Nat},
    WDen ctx s0 ρ s.terms (.list l) (.list l') → wordIds (fun n => findNode n s.terms 0) l = some ids →
    l' = ids.map fun i => Val.word (den (inpOf ctx s0) ρ s.terms i)
  | [], _, _, hd, h => by
    cases hd
    simp only [wordIds, Option.some.injEq] at h; subst h; rfl
  | v :: rest, _, ids, hd, h => by
    cases hd with
    | cons hv hrest =>
      cases v with
      | word xs =>
        cases hv
        simp only [wordIds] at h
        cases hi : idOf (fun n => findNode n s.terms 0) xs <;> cases hr : wordIds (fun n => findNode n s.terms 0) rest <;>
          simp only [hi, hr, reduceCtorEq, Option.some.injEq] at h
        rename_i i is
        subst h
        rw [wordIds_den wf hrest hr, ← idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hi]
        rfl
      | _ => simp [wordIds] at h

/-- A thing a definition is used with, as a key: the key's value is the thing's. -/
theorem flatKey_den (wf : WF s) {v : WVal} {a : Val} {k : Key}
    (hd : WDen ctx s0 ρ s.terms v a) (h : flatKey (fun n => findNode n s.terms 0) v = some k) : a = k.val ctx s0 ρ s.terms := by
  cases v with
  | int n =>
    cases hd
    simp only [flatKey, Option.some.injEq] at h; subst h
    simp only [Key.val, ev_const]
  | num r =>
    cases hd
    simp only [flatKey, Option.some.injEq] at h; subst h
    rfl
  | counter r =>
    cases hd
    simp only [flatKey, Option.some.injEq] at h; subst h
    rfl
  | list l =>
    obtain ⟨l', rfl⟩ := WDen.list_inv hd
    simp only [flatKey] at h
    cases hw : wordIds (fun n => findNode n s.terms 0) l with
    | none => simp [hw] at h
    | some ids =>
      simp only [hw, Option.map_some, Option.some.injEq] at h; subst h
      rw [wordIds_den wf hd hw]
      rfl
  | _ => simp [flatKey] at h

theorem flatKeys_den (wf : WF s) : ∀ {vs : List WVal} {as : List Val} {keys : List Key},
    WDen ctx s0 ρ s.terms (.list vs) (.list as) → flatKeys (fun n => findNode n s.terms 0) vs = some keys →
    as = keys.map (Key.val ctx s0 ρ s.terms)
  | [], _, _, hd, h => by
    cases hd
    simp only [flatKeys, Option.some.injEq] at h; subst h; rfl
  | v :: rest, _, keys, hd, h => by
    cases hd with
    | cons hv hrest =>
      simp only [flatKeys] at h
      cases hk : flatKey (fun n => findNode n s.terms 0) v <;> cases hr : flatKeys (fun n => findNode n s.terms 0) rest <;>
        simp only [hk, hr, reduceCtorEq, Option.some.injEq] at h
      rename_i k ks
      subst h
      rw [flatKey_den wf hv hk, flatKeys_den wf hrest hr]
      rfl

theorem held_bound (H : Holds ctx s0 ρ s st) : ∃ B, HeldWithin ctx s0 ρ s.terms s.known B :=
  held_bound_list ctx s0 ρ s.terms s.known H.known

end

/-! ## Operators -/

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

local notation "𝔻" => den (inpOf ctx s0) ρ s.terms

theorem wbin_sound (H : Holds ctx s0 ρ s st) (wf : WF s) {op : String} {x y v : WVal} {xa ya : Val}
    (h : wbin (fun n => findNode n s.terms 0) s op x y = some v) (hx : WDen ctx s0 ρ s.terms x xa) (hy : WDen ctx s0 ρ s.terms y ya) :
    ∃ a, binop op xa ya = some a ∧ WDen ctx s0 ρ s.terms v a := by
  cases x with
  | int a =>
    cases y with
    | int b =>
      cases hx; cases hy
      simp only [wbin] at h
      cases hb : binop op (.int a) (.int b) with
      | none => simp [hb] at h
      | some r =>
        cases r with
        | int n => simp only [hb, Option.some.injEq] at h; subst h; exact ⟨_, rfl, WDen.int n⟩
        | bool c => simp only [hb, Option.some.injEq] at h; subst h; exact ⟨_, rfl, WDen.bool c⟩
        | _ => simp [hb] at h
    | num r =>
      cases hx; cases hy
      simp only [wbin] at h
      split at h
      next hop =>
        have oe : op = "|" := by simpa using hop
        subst oe
        split at h
        next hc =>
          obtain ⟨a0, hn⟩ := hc
          subst a0
          injection h with h; subst h
          have r0 := knownNonneg_sound H hn
          exact ⟨.int (ev ρ r), by simp [binop, r0, Int.max_eq_left r0], WDen.num r⟩
        next => cases h
      next =>
        have := wnum_sound H h
        rwa [ev_const] at this
    | _ => simp [wbin] at h
  | word xs =>
    cases y with
    | word ys =>
      cases hx; cases hy
      simp only [wbin] at h
      split at h
      next hop =>
        have oe : op = "+" := by simpa using hop
        subst oe
        simp only [Option.some.injEq] at h; subst h
        refine ⟨.word ((sumList (xs.map 𝔻) % W32 + sumList (ys.map 𝔻) % W32) % W32), by simp [binop, wordop], ?_⟩
        have e : (sumList (xs.map 𝔻) % W32 + sumList (ys.map 𝔻) % W32) % W32 =
            sumList (((xs ++ ys).foldr insertSorted []).map 𝔻) % W32 := by
          rw [sumList_sorted, sumList_append]; exact (Nat.add_mod _ _ _).symm
        rw [e]; exact WDen.word _
      next hop =>
        split at h
        next hop2 =>
          have oe : op = "^" := by simpa using hop2
          subst oe
          cases ha : idOf (fun n => findNode n s.terms 0) xs <;> cases hb : idOf (fun n => findNode n s.terms 0) ys <;> simp only [ha, hb, reduceCtorEq] at h
          rename_i a b
          cases hf : findNode (.xor (min a b) (max a b)) s.terms 0 with
          | none => simp [hf] at h
          | some i =>
            simp only [hf, Option.map_some, Option.some.injEq] at h; subst h
            have di := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hf
            have da := idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf ha
            have db := idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hb
            refine ⟨.word (sumList (xs.map 𝔻) % W32 ^^^ sumList (ys.map 𝔻) % W32), by simp [binop, wordop], ?_⟩
            have e : sumList (xs.map 𝔻) % W32 ^^^ sumList (ys.map 𝔻) % W32 = 𝔻 i := by
              rw [di, ← da, ← db]
              simp only [Node.value]
              cases Nat.le_total a b with
              | inl le => rw [Nat.min_eq_left le, Nat.max_eq_right le]
              | inr le => rw [Nat.min_eq_right le, Nat.max_eq_left le, Nat.xor_comm]
            rw [e]; exact WDen.one wf i
        next => simp at h
    | int n =>
      cases hx; cases hy
      simp only [wbin] at h
      split at h
      next hc =>
        obtain ⟨hop, n0, n32⟩ := hc
        have oe : op = ">>>" := by simpa using hop
        subst oe
        cases ha : idOf (fun n => findNode n s.terms 0) xs with
        | none => simp [ha] at h
        | some a =>
          simp only [ha] at h
          cases hf : findNode (.rotr a n.toNat) s.terms 0 with
          | none => simp [hf] at h
          | some i =>
            simp only [hf, Option.map_some, Option.some.injEq] at h; subst h
            have di := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hf
            have da := idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf ha
            refine ⟨.word (rotr (sumList (xs.map 𝔻) % W32) n.toNat), by simp [binop, n0, n32], ?_⟩
            have e : rotr (sumList (xs.map 𝔻) % W32) n.toNat = 𝔻 i := by rw [di, ← da]; rfl
            rw [e]; exact WDen.one wf i
      next => simp at h
    | _ => simp [wbin] at h
  | num r =>
    cases y with
    | int m =>
      cases hx; cases hy
      simp only [wbin] at h
      split at h
      next hop =>
        have oe : op = "%" := by simpa using hop
        subst oe
        split at h
        next mpos =>
          cases hl : lowOf s r m with
          | none => simp [hl] at h
          | some r' =>
            simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
            refine ⟨.int (ev ρ r % m), by simp [binop, mpos], ?_⟩
            rw [← lowOf_sound H mpos hl]; exact WDen.num r'
        next => cases h
      next =>
        split at h
        next hop =>
          -- the quotient the state knows of
          have oe : op = "/" := by simpa using hop
          subst oe
          split at h
          next mpos =>
            cases hd : divided s r m with
            | none => simp [hd] at h
            | some q =>
              simp only [hd, Option.map_some, Option.some.injEq] at h; subst h
              refine ⟨.int (ev ρ r / m), by simp [binop, mpos], ?_⟩
              have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.var q)
              rw [ev_var, (divided_spec H mpos hd).1] at this
              exact this
          next => cases h
        next =>
          split at h
          next hop =>
            have oe : op = "|" := by simpa using hop
            subst oe
            split at h
            next hc =>
              obtain ⟨m0, hn⟩ := hc
              subst m0
              injection h with h; subst h
              have r0 := knownNonneg_sound H hn
              exact ⟨.int (ev ρ r), by simp [binop, r0, Int.max_eq_left r0], WDen.num r⟩
            next => cases h
          next =>
            have := wnum_sound H h
            rwa [ev_const] at this
    | num y2 =>
      cases hx; cases hy
      simp only [wbin] at h
      split at h
      next hop =>
        have oe : op = "|" := by simpa using hop
        subst oe
        cases hk : knownOr r y2 s.known with
        | none => simp [hk] at h
        | some v =>
          simp only [hk, Option.map_some, Option.some.injEq] at h; subst h
          have hv : 0 ≤ ev ρ r ∧ 0 ≤ ev ρ y2 ∧ ρ v = (((ev ρ r).toNat ||| (ev ρ y2).toNat : Nat) : Int) := by
            rcases knownOr_mem hk with m | m
            · exact H.known _ m
            · obtain ⟨g1, g2, g3⟩ := H.known _ m
              exact ⟨g2, g1, by rw [g3, Nat.or_comm]⟩
          refine ⟨.int (((ev ρ r).toNat ||| (ev ρ y2).toNat : Nat) : Int), by simp [binop, hv.1, hv.2.1], ?_⟩
          have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.var v)
          rw [ev_var, hv.2.2] at this
          exact this
      next => exact wnum_sound H h
    | _ => simp [wbin] at h
  | list a =>
    cases y with
    | list b =>
      obtain ⟨a', rfl⟩ := WDen.list_inv hx
      obtain ⟨b', rfl⟩ := WDen.list_inv hy
      simp only [wbin] at h
      split at h
      next hop =>
        have oe : op = "++" := by simpa using hop
        subst oe
        simp only [Option.some.injEq] at h; subst h
        exact ⟨.list (a' ++ b'), by simp [binop], WDen.append hx hy⟩
      next => simp at h
    | _ => simp [wbin] at h
  | _ => cases y <;> simp [wbin] at h

end

/-! ## The words of a run of bytes -/

theorem map_range_succ {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl

theorem map_range_add4 {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 4)).map f = f 0 :: f 1 :: f 2 :: f 3 :: (List.range n).map (fun i => f (i + 4)) := by
  rw [show n + 4 = n + 1 + 1 + 1 + 1 from rfl, map_range_succ, map_range_succ, map_range_succ, map_range_succ]

/-- A part of a run of bytes, cut out of the list of them. -/
theorem slice_run (mem : Nat → Nat) (base n a b : Nat) (h : a + b ≤ n) :
    (((List.range n).map fun k => Val.int (mem (base + k))).drop a).take b = (List.range b).map fun k => Val.int (mem (base + a + k)) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp [Nat.add_assoc]

/-- The number that bytes of memory are, the lowest first: what the machine's `load` reads there. -/
theorem numberLE_load (mem : Nat → Nat) : ∀ (n a : Nat), (∀ k, k < n → mem (a + k) < 256) →
    numberLE ((List.range n).map fun k => Val.int (mem (a + k))) = some (load mem a n)
  | 0, a, _ => by simp [numberLE, load]
  | n + 1, a, hb => by
    have ih := numberLE_load mem n (a + 1) (fun k hk => by
      have := hb (k + 1) (by omega)
      rwa [show a + (k + 1) = a + 1 + k by omega] at this)
    have b0 := hb 0 (by omega)
    rw [Nat.add_zero] at b0
    have e : (fun i => Val.int (mem (a + (i + 1)))) = fun k => Val.int (mem (a + 1 + k)) := by
      funext k
      rw [show a + (k + 1) = a + 1 + k by omega]
    rw [map_range_succ, e]
    simp only [numberLE, Nat.add_zero, ih, load]
    rw [if_pos ⟨by omega, by omega⟩]
    simp only [Option.map_some, Int.toNat_natCast, Nat.mod_eq_of_lt b0]

/-- The words of the bytes of words are those words. -/
theorem toWords_wordBytes : ∀ (ws : List Nat), (∀ w ∈ ws, w < W32) → toWords (wordBytes ws) = some (ws.map Val.word)
  | [], _ => rfl
  | w :: rest, h => by
    have lt := h w (List.mem_cons_self ..)
    unfold W32 at lt
    simp only [wordBytes, toWords]
    rw [if_pos ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
      toWords_wordBytes rest (fun x m => h x (List.mem_cons_of_mem _ m))]
    simp only [Option.map_some, List.map_cons, Option.some.injEq, List.cons.injEq, Val.word.injEq, and_true, Int.toNat_natCast]
    omega


section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

/-- The words of the table that are a run's words: they are what the account's `words` makes of the run's
bytes, four bytes a word, the lowest first. -/
theorem toWords_fn (wf : WF s) {j : Nat} : ∀ (count k : Nat) (g : Nat → Nat) (wvs : List WVal),
    inputWords (fun n => findNode n s.terms 0) j count k = some wvs → (∀ i, i < 4 * count → g i < 256) →
    (∀ q a, a = 4 * q → q < count →
      inpOf ctx s0 j (k + q) = g a + 256 * g (a + 1) + 65536 * g (a + 2) + 16777216 * g (a + 3)) →
    ∃ ws, toWords ((List.range (4 * count)).map fun i => Val.int (g i)) = some ws ∧ WDen ctx s0 ρ s.terms (.list wvs) (.list ws)
  | 0, k, g, wvs, h, _, _ => by
    simp only [inputWords, Option.some.injEq] at h; subst h
    exact ⟨[], by simp [toWords], WDen.nil⟩
  | count + 1, k, g, wvs, h, hb, hwd => by
    simp only [inputWords] at h
    cases hf : findNode (.input j k) s.terms 0 <;> cases hr : inputWords (fun n => findNode n s.terms 0) j count (k + 1) <;>
      simp only [hf, hr, reduceCtorEq, Option.some.injEq] at h
    rename_i i rest
    subst h
    obtain ⟨ws, hw, hd⟩ := toWords_fn wf count (k + 1) (fun i => g (i + 4)) rest hr (fun i hi => hb (i + 4) (by omega))
      (fun q a ha hq => by
        have := hwd (q + 1) (a + 4) (by omega) (by omega)
        have e : k + 1 + q = k + (q + 1) := by omega
        rw [e, this, Nat.add_right_comm a 1 4, Nat.add_right_comm a 2 4, Nat.add_right_comm a 3 4])
    have b0 := hb 0 (by omega)
    have b1 := hb 1 (by omega)
    have b2 := hb 2 (by omega)
    have b3 := hb 3 (by omega)
    have h0 := hwd 0 0 rfl (by omega)
    simp only [Nat.zero_add, Nat.add_zero] at h0
    have di : den (inpOf ctx s0) ρ s.terms i = inpOf ctx s0 j k := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hf
    refine ⟨.word (inpOf ctx s0 j k) :: ws, ?_, WDen.cons (by rw [← di]; exact WDen.one wf i) hd⟩
    rw [show 4 * (count + 1) = 4 * count + 4 from rfl, map_range_add4]
    simp only [toWords]
    rw [if_pos ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩, hw]
    simp only [Option.map_some, Option.some.injEq, List.cons.injEq, Val.word.injEq, and_true]
    omega

end

/-! ## The language's own names -/

theorem load4 (mem : Nat → Nat) (a : Nat) :
    load mem a 4 = mem a % 256 + 256 * (mem (a + 1) % 256 + 256 * (mem (a + 1 + 1) % 256 + 256 * (mem (a + 1 + 1 + 1) % 256 + 256 * 0))) := rfl

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

local notation "𝔻" => den (inpOf ctx s0) ρ s.terms

theorem wown_sound (H : Holds ctx s0 ρ s st) (wf : WF s) {f : String} {vs : List WVal} {as : List Val} {v : WVal}
    (h : wown ctx (fun n => findNode n s.terms 0) s f vs = some v) (hv : WDen ctx s0 ρ s.terms (.list vs) (.list as)) :
    ∃ a, builtin f as = some a ∧ WDen ctx s0 ρ s.terms v a := by
  rcases vs with _ | ⟨x, _ | ⟨y, more⟩⟩
  · simp [wown] at h
  · cases hv with
    | cons hx hnil =>
      cases hnil
      cases x with
      | int n =>
        cases hx
        simp only [wown] at h
        split at h
        next hf =>
          have fe : f = "word" := by simpa using hf
          subst fe
          split at h
          next n0 =>
            cases hfn : findNode (.atom (Lin.word (Lin.const n))) s.terms 0 with
            | none => simp [hfn] at h
            | some i =>
              simp only [hfn, Option.map_some, Option.some.injEq] at h; subst h
              have di : 𝔻 i = (ev ρ (Lin.word (Lin.const n)) % W32i).toNat := found_den wf hfn
              refine ⟨.word (n.toNat % W32), by simp [builtin, n0], ?_⟩
              have e : n.toNat % W32 = 𝔻 i := by rw [di, ev_word, ev_const]; unfold W32 W32i; omega
              rw [e]; exact WDen.one wf i
          next => simp at h
        next hf =>
          split at h
          next hf2 =>
            have fe : f = "counter" := by simpa using hf2
            subst fe
            split at h
            next n0 =>
              simp only [Option.some.injEq] at h; subst h
              refine ⟨.counter (n.toNat % 2 ^ 64), by simp [builtin, n0], ?_⟩
              have := WDen.counter (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.const n) (by rw [ev_const]; exact n0)
              rw [ev_const] at this; exact this
            next => simp at h
          next => simp at h
      | num r =>
        cases hx
        simp only [wown] at h
        split at h
        next => simp at h
        next hk =>
          have r0 : 0 ≤ ev ρ r := knownNonneg_sound H (by simpa using hk)
          split at h
          next hf =>
            have fe : f = "word" := by simpa using hf
            subst fe
            cases hfn : findNode (.atom (Lin.word r)) s.terms 0 with
            | none => simp [hfn] at h
            | some i =>
              simp only [hfn, Option.map_some, Option.some.injEq] at h; subst h
              have di : 𝔻 i = (ev ρ (Lin.word r) % W32i).toNat := found_den wf hfn
              refine ⟨.word ((ev ρ r).toNat % W32), by simp [builtin, r0], ?_⟩
              have e : (ev ρ r).toNat % W32 = 𝔻 i := by rw [di, ev_word]; unfold W32 W32i; omega
              rw [e]; exact WDen.one wf i
          next hf =>
            split at h
            next hf2 =>
              have fe : f = "counter" := by simpa using hf2
              subst fe
              simp only [Option.some.injEq] at h; subst h
              exact ⟨.counter ((ev ρ r).toNat % 2 ^ 64), by simp [builtin, r0], WDen.counter r r0⟩
            next => simp at h
      | word xs =>
        cases hx
        simp only [wown] at h
        split at h
        next hf =>
          have fe : f = "word" := by simpa using hf
          subst fe
          simp only [Option.some.injEq] at h; subst h
          exact ⟨_, by simp [builtin], WDen.word xs⟩
        next => simp at h
      | counter r =>
        cases hx with
        | counter _ r0 =>
          simp only [wown] at h
          split at h
          next hf =>
            have fe : f = "counter" := by simpa using hf
            subst fe
            simp only [Option.some.injEq] at h; subst h
            exact ⟨_, by simp [builtin], WDen.counter r r0⟩
          next hf =>
            split at h
            next hf2 =>
              have fe : f = "lo" := by simpa using hf2
              subst fe
              cases hfn : findNode (.atom (Lin.word r)) s.terms 0 with
              | none => simp [hfn] at h
              | some i =>
                simp only [hfn, Option.map_some, Option.some.injEq] at h; subst h
                have di : 𝔻 i = (ev ρ (Lin.word r) % W32i).toNat := found_den wf hfn
                refine ⟨.word ((ev ρ r).toNat % 2 ^ 64 % W32), by simp [builtin], ?_⟩
                have e : (ev ρ r).toNat % 2 ^ 64 % W32 = 𝔻 i := by rw [di, ev_word]; unfold W32 W32i; omega
                rw [e]; exact WDen.one wf i
            next hf2 =>
              split at h
              next hf3 =>
                have fe : f = "hi" := by simpa using hf3
                subst fe
                cases hq : highOf s r with
                | none => simp [hq] at h
                | some q =>
                  simp only [hq, Option.bind_some] at h
                  cases hfn : findNode (.atom (Lin.word q)) s.terms 0 with
                  | none => simp [hfn] at h
                  | some i =>
                    simp only [hfn, Option.map_some, Option.some.injEq] at h; subst h
                    have di : 𝔻 i = (ev ρ (Lin.word q) % W32i).toNat := found_den wf hfn
                    have eq := highOf_sound H hq
                    refine ⟨.word ((ev ρ r).toNat % 2 ^ 64 / W32), by simp [builtin], ?_⟩
                    have e : (ev ρ r).toNat % 2 ^ 64 / W32 = 𝔻 i := by rw [di, ev_word, eq]; unfold W32 W32i; omega
                    rw [e]; exact WDen.one wf i
              next => simp at h
      | run r n =>
        cases hx with
        | run _ _ hb =>
          simp only [wown] at h
          split at h
          next hc =>
            obtain ⟨hf, n4⟩ := hc
            have fe : f = "words" := by simpa using hf
            subst fe
            cases hra : runAt r (ctx.contract.fixeds ++ ctx.contract.inouts) 0 with
            | none => simp [hra] at h
            | some j =>
              simp only [hra, Option.bind_some] at h
              cases hin : inputWords (fun n => findNode n s.terms 0) j (n / 4) 0 with
              | none => simp [hin] at h
              | some wvs =>
                simp only [hin, Option.map_some, Option.some.injEq] at h; subst h
                obtain ⟨_, x', n', hj⟩ := runAt_spec hra
                have hj' : (ctx.contract.fixeds ++ ctx.contract.inouts)[j]? = some (x', r, n') := by simpa using hj
                obtain ⟨ws, hw, hd⟩ := toWords_fn (ctx := ctx) (s0 := s0) (ρ := ρ) wf (n / 4) 0 (fun i => s0.mem (s0.reg r + i)) wvs hin
                  (fun i hi => hb i (by omega))
                  (fun q a ha hq => by
                    subst ha
                    have b0 := hb (4 * q) (by omega)
                    have b1 := hb (4 * q + 1) (by omega)
                    have b2 := hb (4 * q + 2) (by omega)
                    have b3 := hb (4 * q + 3) (by omega)
                    have e0 : inpOf ctx s0 j (0 + q) = load s0.mem (s0.reg r + 4 * q) 4 := by simp only [inpOf, hj', Nat.zero_add]
                    have e1 : s0.reg r + 4 * q + 1 = s0.reg r + (4 * q + 1) := by omega
                    have e2 : s0.reg r + 4 * q + 1 + 1 = s0.reg r + (4 * q + 2) := by omega
                    have e3 : s0.reg r + 4 * q + 1 + 1 + 1 = s0.reg r + (4 * q + 3) := by omega
                    rw [e0, load4, e3, e2, e1]
                    omega)
                have en : 4 * (n / 4) = n := by omega
                rw [en] at hw
                exact ⟨.list ws, by simp [builtin, hw], hd⟩
          next => simp at h
      | part r off n =>
        cases hx with
        | part _ _ _ hb =>
          simp only [wown] at h
          split at h
          next hc =>
            obtain ⟨hf, o4, n4⟩ := hc
            have fe : f = "words" := by simpa using hf
            subst fe
            cases hra : runAt r (ctx.contract.fixeds ++ ctx.contract.inouts) 0 with
            | none => simp [hra] at h
            | some j =>
              simp only [hra, Option.bind_some] at h
              cases hin : inputWords (fun n => findNode n s.terms 0) j (n / 4) (off / 4) with
              | none => simp [hin] at h
              | some wvs =>
                simp only [hin, Option.map_some, Option.some.injEq] at h; subst h
                obtain ⟨_, x', n', hj⟩ := runAt_spec hra
                have hj' : (ctx.contract.fixeds ++ ctx.contract.inouts)[j]? = some (x', r, n') := by simpa using hj
                obtain ⟨ws, hw, hd⟩ := toWords_fn (ctx := ctx) (s0 := s0) (ρ := ρ) wf (n / 4) (off / 4) (fun i => s0.mem (s0.reg r + off + i)) wvs hin
                  (fun i hi => hb i (by omega))
                  (fun q a ha hq => by
                    subst ha
                    have b0 := hb (4 * q) (by omega)
                    have b1 := hb (4 * q + 1) (by omega)
                    have b2 := hb (4 * q + 2) (by omega)
                    have b3 := hb (4 * q + 3) (by omega)
                    have ea : s0.reg r + 4 * (off / 4 + q) = s0.reg r + off + 4 * q := by omega
                    have e0 : inpOf ctx s0 j (off / 4 + q) = load s0.mem (s0.reg r + off + 4 * q) 4 := by simp only [inpOf, hj', ea]
                    have e1 : s0.reg r + off + 4 * q + 1 = s0.reg r + off + (4 * q + 1) := by omega
                    have e2 : s0.reg r + off + 4 * q + 1 + 1 = s0.reg r + off + (4 * q + 2) := by omega
                    have e3 : s0.reg r + off + 4 * q + 1 + 1 + 1 = s0.reg r + off + (4 * q + 3) := by omega
                    rw [e0, load4, e3, e2, e1]
                    omega)
                have en : 4 * (n / 4) = n := by omega
                rw [en] at hw
                exact ⟨.list ws, by simp [builtin, hw], hd⟩
          next =>
            split at h
            next hc =>
              obtain ⟨hf, n8⟩ := hc
              have fe : f = "number.le" := by simpa using hf
              subst fe
              subst n8
              cases hra : runAt r ctx.contract.fixeds 0 with
              | none => simp [hra] at h
              | some j =>
                simp only [hra, Option.bind_some] at h
                cases hk : knownLoad j off s.known with
                | none => simp [hk] at h
                | some v =>
                  simp only [hk, Option.map_some, Option.some.injEq] at h; subst h
                  obtain ⟨_, x', n', hj⟩ := runAt_spec hra
                  have hj' : ctx.contract.fixeds[j]? = some (x', r, n') := by simpa using hj
                  obtain ⟨x2, r2, n2, g1, g2, g3⟩ := H.known _ (knownLoad_mem hk)
                  rw [hj'] at g1
                  injection g1 with g1
                  injection g1 with _ g1
                  injection g1 with g1 _
                  subst g1
                  refine ⟨.int (load s0.mem (s0.reg r + off) 8 : Nat), ?_, ?_⟩
                  · simp [builtin, numberLE_load s0.mem 8 (s0.reg r + off) hb]
                  · have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.var v)
                    rw [ev_var, g3] at this
                    exact this
            next => simp at h
      | wbytes ids =>
        cases hx
        simp only [wown] at h
        split at h
        next hf =>
          have fe : f = "words" := by simpa using hf
          subst fe
          simp only [Option.some.injEq] at h; subst h
          refine ⟨.list (ids.map fun i => Val.word (𝔻 i)), ?_, WDen.wordsOf wf ids⟩
          have e := toWords_wordBytes (ids.map 𝔻) (fun w m => by
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp m
            exact Holds.den_lt wf i)
          simp [builtin, e]
        next => simp at h
      | _ => simp [wown] at h
  · cases x <;> simp [wown] at h

/-! ## Lists of expressions -/

theorem wevalList_sound {ev : SExpr → Option WVal} {ev' : SExpr → Option Val}
    (hev : ∀ e v, ev e = some v → ∃ a, ev' e = some a ∧ WDen ctx s0 ρ s.terms v a) :
    ∀ (args : SExpr) (vs : List WVal), wevalList ev args = some vs →
      ∃ as, evalList ev' args = some as ∧ WDen ctx s0 ρ s.terms (.list vs) (.list as) := by
  intro args
  induction args with
  | nil => intro vs h; simp only [wevalList, Option.some.injEq] at h; subst h; exact ⟨[], rfl, WDen.nil⟩
  | cons a rest _ ih =>
    intro vs h
    simp only [wevalList] at h
    cases ha : ev a <;> cases hr : wevalList ev rest <;> simp only [ha, hr, reduceCtorEq, Option.some.injEq] at h
    rename_i v vs'
    subst h
    obtain ⟨a', ea, da⟩ := hev a v ha
    obtain ⟨as, eas, das⟩ := ih vs' hr
    exact ⟨a' :: as, by simp only [evalList, ea, eas], WDen.cons da das⟩
  | _ => intro vs h; simp [wevalList] at h

theorem wevalEach_sound {ev : Int → Option WVal} {ev' : Int → Option Val}
    (hev : ∀ i v, ev i = some v → ∃ a, ev' i = some a ∧ WDen ctx s0 ρ s.terms v a) :
    ∀ (count : Nat) (i : Int) (vs : List WVal), wevalEach ev count i = some vs →
      ∃ as, evalEach ev' count i = some as ∧ WDen ctx s0 ρ s.terms (.list vs) (.list as)
  | 0, i, vs, h => by simp only [wevalEach, Option.some.injEq] at h; subst h; exact ⟨[], rfl, WDen.nil⟩
  | count + 1, i, vs, h => by
    simp only [wevalEach] at h
    cases ha : ev i <;> cases hr : wevalEach ev count (i + 1) <;> simp only [ha, hr, reduceCtorEq, Option.some.injEq] at h
    rename_i v vs'
    subst h
    obtain ⟨a', ea, da⟩ := hev i v ha
    obtain ⟨as, eas, das⟩ := wevalEach_sound hev count (i + 1) vs' hr
    exact ⟨a' :: as, by simp only [evalEach, ea, eas], WDen.cons da das⟩

theorem wputAll_sound : ∀ (ps : List WVal) (ps' : List Val) (l : List WVal) (l' : List Val) (l2 : List WVal),
    WDen ctx s0 ρ s.terms (.list l) (.list l') → WDen ctx s0 ρ s.terms (.list ps) (.list ps') → wputAll l ps = some l2 →
    ∃ l2', putAll l' ps' = some l2' ∧ WDen ctx s0 ρ s.terms (.list l2) (.list l2')
  | [], ps', l, l', l2, hl, hp, h => by
    cases hp
    simp only [wputAll, Option.some.injEq] at h; subst h
    exact ⟨l', by simp [putAll], hl⟩
  | [p], ps', l, l', l2, hl, hp, h => by cases p <;> simp [wputAll] at h
  | p :: x :: rest, ps', l, l', l2, hl, hp, h => by
    cases hp with
    | cons hp1 hp2 =>
      cases hp2 with
      | cons hx hrest =>
        cases p with
        | int i =>
          cases hp1
          simp only [wputAll] at h
          split at h
          next hc =>
            obtain ⟨l2', e, d⟩ := wputAll_sound rest _ (l.set i.toNat x) _ l2 (WDen.set hl hx) hrest h
            refine ⟨l2', ?_, d⟩
            simp only [putAll]
            rw [if_pos ⟨hc.1, by rw [← WDen.length hl]; exact hc.2⟩]
            exact e
          next => simp at h
        | _ => simp [wputAll] at h

end

/-! ## An expression -/

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

/-- What `weval` gives of an expression stands for what `evalSpec` gives of it with the same fuel and `B`
more, the names on words standing for the names of the account: `B` being steps enough for every use of a
definition whose words the state holds (such a use costs `weval` nothing, and `evalSpec` works it out). -/
theorem weval_sound (H : Holds ctx s0 ρ s st) (wf : WF s) {B : Nat} (hB : HeldWithin ctx s0 ρ s.terms s.known B) :
    ∀ (fuel : Nat) (env : List (String × WVal)) (env' : List (String × Val)) (e : SExpr) (v : WVal),
      weval ctx (fun n => findNode n s.terms 0) s fuel env e = some v → EnvDen ctx s0 ρ s.terms env env' →
      ∃ a, evalSpec ctx.defs (fuel + B) env' e = some a ∧ WDen ctx s0 ρ s.terms v a
  | 0, _, _, _, _, h, _ => by simp [weval] at h
  | fuel + 1, env, env', e, v, h, hE => by
    have ih := weval_sound H wf hB fuel
    have e1 : fuel + 1 + B = (fuel + B) + 1 := by omega
    rw [e1]
    cases e with
    | num n =>
      simp only [weval] at h
      split at h
      next n0 =>
        simp only [Option.some.injEq] at h; subst h
        refine ⟨.int n, ?_, WDen.int n⟩
        simp only [evalSpec]; rw [if_pos n0]
      next => simp at h
    | name x =>
      simp only [weval] at h
      obtain ⟨a, ha, hd⟩ := EnvDen.lookup hE h
      refine ⟨a, ?_, hd⟩
      simp only [evalSpec]; exact ha
    | bin op a b =>
      simp only [weval] at h
      cases ha : weval ctx (fun n => findNode n s.terms 0) s fuel env a <;> cases hb : weval ctx (fun n => findNode n s.terms 0) s fuel env b <;>
        simp only [ha, hb, reduceCtorEq] at h
      rename_i x y
      obtain ⟨xa, ea, da⟩ := ih env env' a x ha hE
      obtain ⟨ya, eb, db⟩ := ih env env' b y hb hE
      obtain ⟨r, er, dr⟩ := wbin_sound H wf h da db
      refine ⟨r, ?_, dr⟩
      simp only [evalSpec, ea, eb]; exact er
    | ifx c a b =>
      simp only [weval] at h
      cases hc : weval ctx (fun n => findNode n s.terms 0) s fuel env c with
      | none => simp [hc] at h
      | some cv =>
        obtain ⟨ca, ec, dc⟩ := ih env env' c cv hc hE
        cases cv with
        | bool t =>
          cases dc
          cases t with
          | true =>
            simp only [hc] at h
            obtain ⟨r, er, dr⟩ := ih env env' a v h hE
            refine ⟨r, ?_, dr⟩
            simp only [evalSpec, ec]; exact er
          | false =>
            simp only [hc] at h
            obtain ⟨r, er, dr⟩ := ih env env' b v h hE
            refine ⟨r, ?_, dr⟩
            simp only [evalSpec, ec]; exact er
        | _ => simp [hc] at h
    | index a i =>
      simp only [weval] at h
      cases ha : weval ctx (fun n => findNode n s.terms 0) s fuel env a <;> cases hi : weval ctx (fun n => findNode n s.terms 0) s fuel env i <;>
        simp only [ha, hi, reduceCtorEq] at h
      rename_i av iv
      obtain ⟨aa, ea, da⟩ := ih env env' a av ha hE
      obtain ⟨ia, ei, di⟩ := ih env env' i iv hi hE
      cases av with
      | list l =>
        cases iv with
        | int k =>
          cases di
          obtain ⟨l', rfl⟩ := WDen.list_inv da
          simp only at h
          split at h
          next k0 =>
            obtain ⟨r, er, dr⟩ := WDen.getElem? da h
            refine ⟨r, ?_, dr⟩
            simp only [evalSpec, ea, ei]; rw [if_pos k0]; exact er
          next => simp at h
        | _ => simp at h
      | lanes j count l =>
        cases iv with
        | int k =>
          cases di
          cases da with
          | lanes _ _ _ x r ht =>
            simp only at h
            split at h
            next hk =>
              simp only [Option.some.injEq] at h; subst h
              refine ⟨laneBlocks s0.mem (lanePtr s0 r k.toNat) (s0.reg l), ?_, ?_⟩
              · simp only [evalSpec, ea, ei]; rw [if_pos hk.1, List.getElem?_map, List.getElem?_range hk.2]; rfl
              · have := WDen.lane (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) j (8 * k.toNat) l x r count ht (by omega) (by omega)
                rw [Nat.mul_div_cancel_left _ (by decide : 0 < 8)] at this
                exact this
            next => simp at h
        | _ => simp at h
      | lane j c l =>
        cases da with
        | lane _ _ _ x r count ht c8 clt =>
          cases iv with
          | int k =>
            cases di
            simp only at h
            split at h
            next k0 =>
              obtain ⟨_, a', ha', hd⟩ := blockAt_sound H wf h (k := k) (by simp) ht
              refine ⟨a', ?_, hd⟩
              simp only [evalSpec, ea, ei, laneBlocks]; rw [if_pos k0]; exact ha'
            next => simp at h
          | num r' =>
            cases di
            simp only at h
            obtain ⟨k0, a', ha', hd⟩ := blockAt_sound H wf h (k := ev ρ r') (by simp) ht
            refine ⟨a', ?_, hd⟩
            simp only [evalSpec, ea, ei, laneBlocks]; rw [if_pos k0]; exact ha'
          | _ => simp at h
      | _ => cases iv <;> simp at h
    | call f args =>
      simp only [weval] at h
      cases hl : wevalList (weval ctx (fun n => findNode n s.terms 0) s fuel env) args with
      | none => simp [hl] at h
      | some vs =>
        simp only [hl] at h
        obtain ⟨as, el, dl⟩ := wevalList_sound (ev' := evalSpec ctx.defs (fuel + B) env') (fun e v hv => ih env env' e v hv hE) args vs hl
        split at h
        next => simp at h
        next hlen =>
          split at h
          next hown =>
            obtain ⟨r, er, dr⟩ := wown_sound H wf h dl
            refine ⟨r, ?_, dr⟩
            simp only [evalSpec, el]; rw [if_neg hlen, if_pos hown]; exact er
          next hown =>
            cases hh : ((flatKeys (fun n => findNode n s.terms 0) vs).bind fun keys => heldIds f keys s.known) with
            | some ids =>
              -- a use the state holds the words of: the definition gives them within `B` steps
              simp only [hh, Option.some.injEq] at h; subst h
              obtain ⟨keys, hk, hi⟩ := Option.bind_eq_some_iff.mp hh
              obtain ⟨d, hd, hlen', hev⟩ := hB f keys ids (heldIds_mem hi)
              have eas : as = keys.map (Key.val ctx s0 ρ s.terms) := flatKeys_den wf dl hk
              have hp' : (d.params.length == as.length) = true := by rw [eas, List.length_map]; simpa using hlen'
              refine ⟨.list (ids.map fun i => Val.word (den (inpOf ctx s0) ρ s.terms i)), ?_, WDen.wordsOf wf ids⟩
              simp only [evalSpec, el]; rw [if_neg hlen, if_neg hown]; simp only [hd]; rw [if_pos hp', eas]
              exact evalSpec_mono ctx.defs B hev (fuel + B) (Nat.le_add_left _ _)
            | none =>
              simp only [hh] at h
              cases hd : findDef ctx.defs f with
              | none => simp [hd] at h
              | some d =>
                simp only [hd] at h
                split at h
                next hp =>
                  obtain ⟨r, er, dr⟩ := ih (d.params.zip vs) (d.params.zip as) d.body v h (EnvDen.zip dl)
                  have hp' : (d.params.length == as.length) = true := by rw [← WDen.length dl]; exact hp
                  refine ⟨r, ?_, dr⟩
                  simp only [evalSpec, el]; rw [if_neg hlen, if_neg hown]; simp only [hd]; rw [if_pos hp']; exact er
                next => simp at h
    | list items =>
      simp only [weval] at h
      cases hl : wevalList (weval ctx (fun n => findNode n s.terms 0) s fuel env) items with
      | none => simp [hl] at h
      | some vs =>
        simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
        obtain ⟨as, el, dl⟩ := wevalList_sound (ev' := evalSpec ctx.defs (fuel + B) env') (fun e v hv => ih env env' e v hv hE) items vs hl
        refine ⟨.list as, ?_, dl⟩
        simp only [evalSpec, el, Option.map_some]
    | letx x e rest =>
      simp only [weval] at h
      cases he : weval ctx (fun n => findNode n s.terms 0) s fuel env e with
      | none => simp [he] at h
      | some xv =>
        simp only [he] at h
        obtain ⟨xa, ex, dx⟩ := ih env env' e xv he hE
        obtain ⟨r, er, dr⟩ := ih ((x, xv) :: env) ((x, xa) :: env') rest v h ⟨rfl, dx, hE⟩
        refine ⟨r, ?_, dr⟩
        simp only [evalSpec, ex]; exact er
    | each e x a b =>
      simp only [weval] at h
      cases ha : weval ctx (fun n => findNode n s.terms 0) s fuel env a <;> cases hb : weval ctx (fun n => findNode n s.terms 0) s fuel env b <;>
        simp only [ha, hb, reduceCtorEq] at h
      rename_i av bv
      obtain ⟨aa, ea, da⟩ := ih env env' a av ha hE
      obtain ⟨ba, eb, db⟩ := ih env env' b bv hb hE
      cases av with
      | int lo =>
        cases bv with
        | int hi =>
          cases da; cases db
          simp only at h
          cases hl : wevalEach (fun i => weval ctx (fun n => findNode n s.terms 0) s fuel ((x, .int i) :: env) e) (hi - lo).toNat lo with
          | none => simp [hl] at h
          | some vs =>
            simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
            obtain ⟨as, el, dl⟩ := wevalEach_sound (ev' := fun i => evalSpec ctx.defs (fuel + B) ((x, .int i) :: env') e)
              (fun i v hv => ih ((x, .int i) :: env) ((x, .int i) :: env') e v hv ⟨rfl, WDen.int i, hE⟩) (hi - lo).toNat lo vs hl
            refine ⟨.list as, ?_, dl⟩
            simp only [evalSpec, ea, eb, el, Option.map_some]
        | _ => simp at h
      | _ => cases bv <;> simp at h
    | withx a puts =>
      simp only [weval] at h
      cases ha : weval ctx (fun n => findNode n s.terms 0) s fuel env a <;> cases hp : wevalList (weval ctx (fun n => findNode n s.terms 0) s fuel env) puts <;>
        simp only [ha, hp, reduceCtorEq] at h
      rename_i av ps
      obtain ⟨aa, ea, da⟩ := ih env env' a av ha hE
      obtain ⟨ps', ep, dp⟩ := wevalList_sound (ev' := evalSpec ctx.defs (fuel + B) env') (fun e v hv => ih env env' e v hv hE) puts ps hp
      cases av with
      | list l =>
        obtain ⟨l', rfl⟩ := WDen.list_inv da
        simp only at h
        cases hw : wputAll l ps with
        | none => simp [hw] at h
        | some l2 =>
          simp only [hw, Option.map_some, Option.some.injEq] at h; subst h
          obtain ⟨l2', e2, d2⟩ := wputAll_sound ps ps' l l' l2 da dp hw
          refine ⟨.list l2', ?_, d2⟩
          simp only [evalSpec, ea, ep, e2, Option.map_some]
      | _ => simp at h
    | slice a lo hi =>
      simp only [weval] at h
      cases ha : weval ctx (fun n => findNode n s.terms 0) s fuel env a <;> cases hlo : weval ctx (fun n => findNode n s.terms 0) s fuel env lo <;>
        cases hhi : weval ctx (fun n => findNode n s.terms 0) s fuel env hi <;> simp only [ha, hlo, hhi, reduceCtorEq] at h
      rename_i av lv hv
      obtain ⟨aa, ea, da⟩ := ih env env' a av ha hE
      obtain ⟨la, elo, dlo⟩ := ih env env' lo lv hlo hE
      obtain ⟨ha', ehi, dhi⟩ := ih env env' hi hv hhi hE
      cases av with
      | run r n =>
        cases lv with
        | int i =>
          cases hv with
          | int j =>
            cases dlo; cases dhi
            cases da with
            | run _ _ hb =>
              simp only at h
              split at h
              next hc =>
                simp only [Option.some.injEq] at h; subst h
                obtain ⟨i0, ij, jn⟩ := hc
                have hb' : ∀ k, k < (j - i).toNat → s0.mem (s0.reg r + i.toNat + k) < 256 := fun k hk => by
                  have := hb (i.toNat + k) (by omega)
                  rwa [← Nat.add_assoc] at this
                refine ⟨_, ?_, WDen.part r i.toNat (j - i).toNat hb'⟩
                simp only [evalSpec, ea, elo, ehi]
                rw [if_pos ⟨i0, ij, by simpa using jn⟩, slice_run s0.mem (s0.reg r) n i.toNat (j - i).toNat (by omega)]
              next => simp at h
          | _ => simp at h
        | _ => cases hv <;> simp at h
      | part r off n =>
        cases lv with
        | int i =>
          cases hv with
          | int j =>
            cases dlo; cases dhi
            cases da with
            | part _ _ _ hb =>
              simp only at h
              split at h
              next hc =>
                simp only [Option.some.injEq] at h; subst h
                obtain ⟨i0, ij, jn⟩ := hc
                have eo : ∀ k, s0.reg r + (off + i.toNat) + k = s0.reg r + off + i.toNat + k := fun k => by omega
                have hb' : ∀ k, k < (j - i).toNat → s0.mem (s0.reg r + (off + i.toNat) + k) < 256 := fun k hk => by
                  have := hb (i.toNat + k) (by omega)
                  rw [eo]; rwa [← Nat.add_assoc] at this
                have key := WDen.part (ctx := ctx) (ρ := ρ) (T := s.terms) (s0 := s0) r (off + i.toNat) (j - i).toNat hb'
                simp only [eo] at key
                refine ⟨_, ?_, key⟩
                simp only [evalSpec, ea, elo, ehi]
                rw [if_pos ⟨i0, ij, by simpa using jn⟩, slice_run s0.mem (s0.reg r + off) n i.toNat (j - i).toNat (by omega)]
              next => simp at h
          | _ => simp at h
        | _ => cases hv <;> simp at h
      | _ => cases lv <;> cases hv <;> simp at h
    | record names items =>
      simp only [weval] at h
      cases hl : wevalList (weval ctx (fun n => findNode n s.terms 0) s fuel env) items with
      | none => simp [hl] at h
      | some vs =>
        simp only [hl] at h
        obtain ⟨as, el, dl⟩ := wevalList_sound (ev' := evalSpec ctx.defs (fuel + B) env') (fun e v hv => ih env env' e v hv hE) items vs hl
        split at h
        next hn =>
          simp only [Option.some.injEq] at h; subst h
          have hn' : (names.length == as.length) = true := by rw [← WDen.length dl]; exact hn
          refine ⟨.record (names.zip as), ?_, WDen.zipRecord dl⟩
          simp only [evalSpec, el]; rw [if_pos hn']
        next => simp at h
    | field e x =>
      simp only [weval] at h
      cases he : weval ctx (fun n => findNode n s.terms 0) s fuel env e with
      | none => simp [he] at h
      | some rv =>
        obtain ⟨ra, ee, de⟩ := ih env env' e rv he hE
        cases rv with
        | record fields =>
          simp only [he] at h
          obtain ⟨fs', rfl⟩ := WDen.record_inv de
          obtain ⟨a, ha, hd⟩ := WDen.lookupRecord de h
          refine ⟨a, ?_, hd⟩
          simp only [evalSpec, ee]; exact ha
        | _ => simp [he] at h
    | _ => simp [weval] at h

end

/-! ## The names of the contract, and the `ensures` -/

theorem fixedsIn_tail {y : String × Nat × Nat} (a : String × Kind) (r : Nat) {args : List (String × Kind)} {regs : List Nat}
    (m : y ∈ fixedsIn args regs) : y ∈ fixedsIn (a :: args) (r :: regs) := by
  obtain ⟨n, k⟩ := a
  cases k <;> simp [fixedsIn, m]

theorem inoutsIn_tail {y : String × Nat × Nat} (a : String × Kind) (r : Nat) {args : List (String × Kind)} {regs : List Nat}
    (m : y ∈ inoutsIn args regs) : y ∈ inoutsIn (a :: args) (r :: regs) := by
  obtain ⟨n, k⟩ := a
  cases k <;> simp [inoutsIn, m]

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

local notation "𝔻" => den (inpOf ctx s0) ρ s.terms

/-- The names on words stand for the contract's names as the account has them at entry. -/
theorem wenvIn_sound (H : Holds ctx s0 ρ s st) {T : List Node} (c : Contract) :
    ∀ (args : List (String × Kind)) (regs : List Nat), (∀ r ∈ regs, r < 16) →
      (∀ x r n, (x, r, n) ∈ fixedsIn args regs → ∀ k, k < n → s0.mem (s0.reg r + k) < 256) →
      (∀ x r n, (x, r, n) ∈ inoutsIn args regs → ∀ k, k < n → s0.mem (s0.reg r + k) < 256) →
      EnvDen ctx s0 ρ T (wenvIn c args regs) (envWIn c s0 args regs)
  | [], _, _, _, _ => by simp [wenvIn, envWIn, EnvDen]
  | _ :: _, [], _, _, _ => by simp [wenvIn, envWIn, EnvDen]
  | (n, kind) :: args, r :: regs, hreg, hf, hi => by
    have ih := wenvIn_sound H (T := T) c args regs (fun r' m => hreg r' (List.mem_cons_of_mem _ m))
      (fun x r' n' m => hf x r' n' (fixedsIn_tail (n, kind) r m)) (fun x r' n' m => hi x r' n' (inoutsIn_tail (n, kind) r m))
    cases kind with
    | number =>
      simp only [wenvIn, envWIn]
      refine ⟨rfl, ?_, ih⟩
      have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := T) (Lin.var r)
      rw [ev_var, H.entry r (hreg r (List.mem_cons_self ..))] at this
      exact this
    | bytes len =>
      simp only [wenvIn, envWIn]
      cases c.regOf len with
      | none => exact ih
      | some l => exact ⟨rfl, WDen.other _, ih⟩
    | out k =>
      simp only [wenvIn, envWIn]
      exact ih
    | fixed count =>
      simp only [wenvIn, envWIn]
      refine ⟨rfl, ?_, ih⟩
      simp only [Val.bytes, List.map_map]
      exact WDen.run r count (hf n r count (by simp [fixedsIn]))
    | inout count =>
      simp only [wenvIn, envWIn]
      refine ⟨rfl, ?_, ih⟩
      simp only [Val.bytes, List.map_map]
      exact WDen.run r count (hi n r count (by simp [inoutsIn]))

theorem EnvDen.append {T : List Node} : ∀ {a : List (String × WVal)} {a' : List (String × Val)} {b : List (String × WVal)} {b' : List (String × Val)},
    EnvDen ctx s0 ρ T a a' → EnvDen ctx s0 ρ T b b' → EnvDen ctx s0 ρ T (a ++ b) (a' ++ b')
  | [], [], _, _, _, hb => hb
  | [], _ :: _, _, _, ha, _ => by simp [EnvDen] at ha
  | _ :: _, [], _, _, ha, _ => by simp [EnvDen] at ha
  | (x, v) :: a, (y, w) :: a', _, _, ha, hb => ⟨ha.1, ha.2.1, EnvDen.append ha.2.2 hb⟩

/-- The tables of addresses by their names: each stands for the list of its lanes. -/
theorem lanesW_den {T : List Node} : ∀ (js : List Nat),
    EnvDen ctx s0 ρ T (js.filterMap fun j => (ctx.contract.tableAt j).map fun (x, _, count, l) => (x, WVal.lanes j count l))
      ((js.filterMap ctx.contract.tableAt).map fun (x, r, count, l) =>
        (x, Val.list ((List.range count).map fun i => laneBlocks s0.mem (lanePtr s0 r i) (s0.reg l))))
  | [] => by simp [EnvDen]
  | j :: js => by
    cases ht : ctx.contract.tableAt j with
    | none => simp only [List.filterMap_cons, ht, Option.map_none]; exact lanesW_den js
    | some t =>
      obtain ⟨x, r, count, l⟩ := t
      simp only [List.filterMap_cons, ht, Option.map_some, List.map_cons]
      exact ⟨rfl, WDen.lanes j count l x r ht, lanesW_den js⟩

theorem wenvIn_all {p : Program} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) {T : List Node} :
    EnvDen ctx s0 ρ T (wenvIn ctx.contract ctx.contract.args argRegs) (envWIn ctx.contract s0 ctx.contract.args argRegs) :=
  wenvIn_sound H ctx.contract ctx.contract.args argRegs (fun _ m => argRegs_lt m)
    (fun _ _ _ m k hk => (E.fixed m).2.2.1 k hk) (fun _ _ _ m _ hk => E.inoutByte m hk)

/-- The contract's names on words stand for its names in the account, a table's name first. -/
theorem wenv_sound {p : Program} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) {T : List Node} :
    EnvDen ctx s0 ρ T (wenv ctx.contract) (ctx.contract.envW s0) :=
  EnvDen.append (lanesW_den _) (wenvIn_all E H)

/-- The words the specification gives are the words known written: the bytes of the run are the bytes of
those words, four a word, the lowest first. -/
theorem written_words (H : Holds ctx s0 ρ s st) (wf : WF s) {w : Nat} {x : String} {r n : Nat}
    (hw : ctx.contract.outs[w]? = some (x, r, n)) :
    ∀ (l : List WVal) (ws : List Val) (j : Nat), wordsWritten (fun n => findNode n s.terms 0) s.wroteW w j l = true →
      WDen ctx s0 ρ s.terms (.list l) (.list ws) →
      ∃ bs : List Nat, ofWords ws = some (bs.map fun (b : Nat) => Val.int b) ∧ bs.length = 4 * l.length ∧
        ∀ k, k < bs.length → bs[k]? = some (st.mem (s0.reg r + 4 * j + k))
  | [], ws, j, _, hd => by
    cases hd
    exact ⟨[], by simp [ofWords], rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | v :: rest, ws, j, hww, hd => by
    cases hd with
    | cons hv hrest =>
      cases v with
      | word xs =>
        cases hv
        simp only [wordsWritten, Bool.and_eq_true] at hww
        obtain ⟨h1, h2⟩ := hww
        cases hi : idOf (fun n => findNode n s.terms 0) xs with
        | none => simp [hi] at h1
        | some i =>
          simp only [hi] at h1
          have m : (w, j, i) ∈ s.wroteW := List.contains_iff_mem.mp h1
          obtain ⟨g1, g2⟩ := H.words.wrote w j i m x r n hw
          obtain ⟨bs, eo, len, hm⟩ := written_words H wf hw rest _ (j + 1) h2 hrest
          have dw := idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hi
          refine ⟨[𝔻 i % 256, 𝔻 i / 256 % 256, 𝔻 i / 65536 % 256, 𝔻 i / 16777216 % 256] ++ bs, ?_, ?_, ?_⟩
          · have lt := Holds.den_lt (ctx := ctx) (s0 := s0) (ρ := ρ) wf i
            rw [← dw]; simp [ofWords, eo, lt]
          · simp only [List.length_append, List.length_cons, List.length_nil, len]; omega
          · intro k hk
            match k, hk with
            | 0, _ => rw [g2 0 (by omega)]; simp
            | 1, _ => rw [g2 1 (by omega)]; simp
            | 2, _ => rw [g2 2 (by omega)]; simp
            | 3, _ => rw [g2 3 (by omega)]; simp
            | k + 4, hk =>
              have := hm k (by simp at hk; omega)
              simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
              rw [this]; congr 2; omega
      | _ => simp [wordsWritten] at hww

/-- An `ensures` of a whole run of words that the verifier has passed holds: the run's bytes at the return
are the bytes of the words the specification gives of the names at entry. -/
theorem symEnsureW_sound {p : Program} (E : Setting ctx p s0) {e : EnsureW} {items : Items}
    {r : Unit × Items} {st' : State}
    (h : symEnsureW ctx s e items = .ok r) (H : Holds ctx s0 ρ s st) (wf : WF s) (hmem : st'.mem = st.mem) :
    e.holds ctx.contract ctx.defs s0 st' := by
  unfold symEnsureW at h
  cases hv : e.value with
  | call f args =>
    simp only [hv] at h
    cases args with
    | cons x tl =>
      cases tl with
      | nil =>
        dsimp only at h
        split at h
        next hf =>
          have fe : f = "bytes_of" := by simpa using hf
          subst fe
          cases hfo : findOutNamed e.run ctx.contract.outs 0 with
          | none => simp only [hfo] at h; exact (refuse_ok h).elim
          | some wn =>
            obtain ⟨w, n⟩ := wn
            simp only [hfo] at h
            have hl : (fun n => (termIndex s.terms)[n]?) = fun n => findNode n s.terms 0 :=
              funext fun n => termIndex_spec s.terms n
            rw [hl] at h
            obtain ⟨rr, _, hw⟩ := findOutNamed_spec hfo
            have hw' : ctx.contract.outs[w]? = some (e.run, rr, n) := by simpa using hw
            cases hwv : weval ctx (fun n => findNode n s.terms 0) s WFUEL (wenv ctx.contract) x with
            | none => simp only [hwv] at h; exact (refuse_ok h).elim
            | some v =>
              cases v with
              | list l =>
                simp only [hwv] at h
                split at h
                next hc =>
                  obtain ⟨hlen, hww⟩ := hc
                  obtain ⟨B, hB⟩ := held_bound H
                  obtain ⟨a, ea, da⟩ := weval_sound H wf hB WFUEL _ _ x _ hwv (wenv_sound E H)
                  obtain ⟨ws, rfl⟩ := WDen.list_inv da
                  obtain ⟨bs, eo, blen, hm⟩ := written_words H wf hw' l ws 0 hww da
                  refine ⟨rr, n, bs, List.mem_of_getElem? hw', ⟨WFUEL + B + 1, ?_⟩, by omega, ?_⟩
                  · rw [hv]
                    simp only [evalSpec, evalList, ea]
                    simp [own, builtin, eo, Val.bytes]
                  · intro k hk
                    have hk' := hm k hk
                    simp only [Nat.mul_zero, Nat.add_zero] at hk'
                    obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.mp hk'
                    rw [hmem]; exact e.symm
                next => exact (refuse_ok h).elim
              | _ => simp only [hwv] at h; exact (refuse_ok h).elim
        next => exact (refuse_ok h).elim
      | _ => exact (refuse_ok h).elim
    | _ => exact (refuse_ok h).elim
  | _ => simp only [hv] at h; exact (refuse_ok h).elim

end

end Ode
