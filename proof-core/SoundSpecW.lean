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
  | run (r n : Nat) (hb : ∀ k, k < n → (s0.mem (s0.reg r + k)).val < 256) :
      WDen ctx s0 ρ T (.run r n) (.list ((List.range n).map fun k => Val.int (s0.mem (s0.reg r + k))))
  | part (r off n : Nat) (hb : ∀ k, k < n → (s0.mem (s0.reg r + off + k)).val < 256) :
      WDen ctx s0 ρ T (.part r off n) (.list ((List.range n).map fun k => Val.int (s0.mem (s0.reg r + off + k))))
  | pbyte (r off : Nat) (hb : (s0.mem (s0.reg r + off)).val < 256) :
      WDen ctx s0 ρ T (.pbyte r off) (.int (s0.mem (s0.reg r + off)))
  | region (r l : Nat) (hl : ρ l = s0.reg l) (hb : ∀ k, k < s0.reg l → (s0.mem (s0.reg r + k)).val < 256) :
      WDen ctx s0 ρ T (.region r l) (.list ((List.range (s0.reg l)).map fun k => Val.int (s0.mem (s0.reg r + k))))
  | span (r : Nat) (off len : Row) (ho : 0 ≤ ev ρ off) (hn : 0 ≤ ev ρ len) :
      WDen ctx s0 ρ T (.span r off len) (.list ((List.range (ev ρ len).toNat).map fun k => Val.int (s0.mem (s0.reg r + (ev ρ off).toNat + k))))
  | wbytes (ids : List Nat) : WDen ctx s0 ρ T (.wbytes ids) (.list (wordBytes (ids.map (den (inpOf ctx s0) ρ T))))
  | rnil : WDen ctx s0 ρ T (.record []) (.record [])
  | rcons {x : String} {v : WVal} {a : Val} {fs : List (String × WVal)} {fs' : List (String × Val)} :
      WDen ctx s0 ρ T v a → WDen ctx s0 ρ T (.record fs) (.record fs') → WDen ctx s0 ρ T (.record ((x, v) :: fs)) (.record ((x, a) :: fs'))
  | lanes (j count l : Nat) (x : String) (r : Nat) (h : ctx.contract.tableAt j = some (x, r, count, l)) :
      WDen ctx s0 ρ T (.lanes j count l) (.list ((List.range count).map fun i => laneBlocks s0.mem (lanePtr s0 r i) (s0.reg l)))
  | lane (j c l : Nat) (x : String) (r count : Nat) (h : ctx.contract.tableAt j = some (x, r, count, l)) (hc : c % 8 = 0) (hi : c / 8 < count) :
      WDen ctx s0 ρ T (.lane j c l) (laneBlocks s0.mem (lanePtr s0 r (c / 8)) (s0.reg l))
  | use (h : Nat) : WDen ctx s0 ρ T (.use h) (Val.decode (ρ h).toNat)
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

/-- The words found for a use of a definition are those the state holds of a use with keys that are the
same things. -/
theorem heldIds_mem {facts : List Row} {f : String} {keys : List Key} : ∀ {l : List Known} {ids : List Nat},
    heldIds facts f keys l = some ids → ∃ keys', Known.held f keys' ids ∈ l ∧ sameKeys facts keys' keys = true
  | [], _, h => by simp [heldIds] at h
  | k :: more, ids, h => by
    cases k with
    | held f' keys' ids' =>
      simp only [heldIds] at h
      split at h
      next e =>
        injection h with h
        obtain ⟨e1, e2⟩ := e
        subst h e1
        exact ⟨keys', List.mem_cons_self .., e2⟩
      next =>
        obtain ⟨k', m, same⟩ := heldIds_mem h
        exact ⟨k', List.mem_cons_of_mem _ m, same⟩
    | load _ _ _ | or _ _ _ | heldB _ _ _ | div _ _ _ | block _ _ _ _ | use _ _ _ | record _ _ _ =>
      simp only [heldIds] at h
      obtain ⟨k', m, same⟩ := heldIds_mem h
      exact ⟨k', List.mem_cons_of_mem _ m, same⟩

/-- The same of a use of a definition that the state holds as bytes. -/
theorem heldBytes_mem {facts : List Row} {f : String} {keys : List Key} : ∀ {l : List Known} {ids : List Nat},
    heldBytes facts f keys l = some ids → ∃ keys', Known.heldB f keys' ids ∈ l ∧ sameKeys facts keys' keys = true
  | [], _, h => by simp [heldBytes] at h
  | k :: more, ids, h => by
    cases k with
    | heldB f' keys' ids' =>
      simp only [heldBytes] at h
      split at h
      next e =>
        injection h with h
        obtain ⟨e1, e2⟩ := e
        subst h e1
        exact ⟨keys', List.mem_cons_self .., e2⟩
      next =>
        obtain ⟨k', m, same⟩ := heldBytes_mem h
        exact ⟨k', List.mem_cons_of_mem _ m, same⟩
    | load _ _ _ | or _ _ _ | held _ _ _ | div _ _ _ | block _ _ _ _ | use _ _ _ | record _ _ _ =>
      simp only [heldBytes] at h
      obtain ⟨k', m, same⟩ := heldBytes_mem h
      exact ⟨k', List.mem_cons_of_mem _ m, same⟩

/-- Of a use of a definition that the state holds the words of, or the bytes of, or has given a number: the
definition gives that within `B` steps. (Of what else is known, nothing is said.) -/
def Known.within (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (T : List Node) (B : Nat) : Known → Prop
  | .held f keys ids => ∃ d, findDef ctx.defs f = some d ∧ d.params.length = keys.length ∧
      evalSpec ctx.defs B (d.params.zip (keys.map (Key.val ctx s0 ρ T))) d.body =
        some (.list (ids.map fun i => Val.word (den (inpOf ctx s0) ρ T i)))
  | .heldB f keys ids => ∃ d, findDef ctx.defs f = some d ∧ d.params.length = keys.length ∧
      evalSpec ctx.defs B (d.params.zip (keys.map (Key.val ctx s0 ρ T))) d.body =
        some (.list (wordBytes (ids.map fun i => den (inpOf ctx s0) ρ T i)))
  | .use f keys h => ∃ d, findDef ctx.defs f = some d ∧ d.params.length = keys.length ∧
      evalSpec ctx.defs B (d.params.zip (keys.map (Key.val ctx s0 ρ T))) d.body = some (Val.decode (ρ h).toNat)
  | _ => True

theorem Known.within_mono {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {T : List Node} {B B' : Nat} (hb : B ≤ B') {k : Known}
    (h : k.within ctx s0 ρ T B) : k.within ctx s0 ρ T B' := by
  cases k with
  | held f keys ids => obtain ⟨d, hd, hlen, hev⟩ := h; exact ⟨d, hd, hlen, evalSpec_mono _ B hev _ hb⟩
  | heldB f keys ids => obtain ⟨d, hd, hlen, hev⟩ := h; exact ⟨d, hd, hlen, evalSpec_mono _ B hev _ hb⟩
  | use f keys u => obtain ⟨d, hd, hlen, hev⟩ := h; exact ⟨d, hd, hlen, evalSpec_mono _ B hev _ hb⟩
  | load _ _ _ | or _ _ _ | div _ _ _ | block _ _ _ _ | record _ _ _ => trivial

theorem Known.within_of_holds {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {T : List Node} {k : Known}
    (hpv : ctx.contract.preVals ctx.defs s0) (h : k.holds ctx s0 ρ T) : ∃ B, k.within ctx s0 ρ T B := by
  cases k with
  | held f keys ids => obtain ⟨d, hd, hlen, fuel, hev⟩ := h hpv; exact ⟨fuel, d, hd, hlen, hev⟩
  | heldB f keys ids => obtain ⟨d, hd, hlen, fuel, hev⟩ := h hpv; exact ⟨fuel, d, hd, hlen, hev⟩
  | use f keys u => obtain ⟨d, hd, hlen, fuel, hev⟩ := h hpv; exact ⟨fuel, d, hd, hlen, hev⟩
  | load _ _ _ | or _ _ _ | div _ _ _ | block _ _ _ _ | record _ _ _ => exact ⟨0, trivial⟩

/-- Every use of a definition that the state holds the words of, or the bytes of, or has given a number: the
definition gives that within `B` steps. -/
abbrev HeldWithin (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (T : List Node) (known : List Known) (B : Nat) : Prop :=
  ∀ k ∈ known, k.within ctx s0 ρ T B

/-- There is such a number of steps: the largest any of them needs. -/
theorem held_bound_list (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (T : List Node)
    (hpv : ctx.contract.preVals ctx.defs s0) : ∀ (l : List Known),
    (∀ k ∈ l, k.holds ctx s0 ρ T) → ∃ B, HeldWithin ctx s0 ρ T l B
  | [], _ => ⟨0, fun _ m => (nomatch m)⟩
  | k :: more, h => by
    obtain ⟨B, hB⟩ := held_bound_list ctx s0 ρ T hpv more (fun k' m => h k' (List.mem_cons_of_mem _ m))
    obtain ⟨Bk, hk⟩ := Known.within_of_holds hpv (h k (List.mem_cons_self ..))
    refine ⟨max B Bk, fun k' m => ?_⟩
    rcases List.mem_cons.mp m with e | m
    · subst e; exact Known.within_mono (Nat.le_max_right _ _) hk
    · exact Known.within_mono (Nat.le_max_left _ _) (hB k' m)

/-- The number found for a use of a definition is that of a use with keys that are the same things. -/
theorem usedAs_mem {facts : List Row} {f : String} {keys : List Key} : ∀ {l : List Known} {u : Nat},
    usedAs facts f keys l = some u → ∃ keys', Known.use f keys' u ∈ l ∧ sameKeys facts keys' keys = true
  | [], _, h => by simp [usedAs] at h
  | k :: more, u, h => by
    cases k with
    | use f' keys' u' =>
      simp only [usedAs] at h
      split at h
      next e =>
        injection h with h
        obtain ⟨e1, e2⟩ := e
        subst h e1
        exact ⟨keys', List.mem_cons_self .., e2⟩
      next =>
        obtain ⟨k', m, same⟩ := usedAs_mem h
        exact ⟨k', List.mem_cons_of_mem _ m, same⟩
    | load _ _ _ | or _ _ _ | held _ _ _ | heldB _ _ _ | div _ _ _ | block _ _ _ _ | record _ _ _ =>
      simp only [usedAs] at h
      obtain ⟨k', m, same⟩ := usedAs_mem h
      exact ⟨k', List.mem_cons_of_mem _ m, same⟩

/-! ## What is looked up -/

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}
variable {look : Node → Option Nat} [Looks look s.terms]

/-- A division the facts held already say: the unknowns are the quotient and the remainder. -/
theorem divided_spec (H : Holds ctx s0 ρ s st) {x : Row} {m : Int} (pos : 0 < m) {q : Nat} (hd : divided s x m = some q) :
    ρ q = ev ρ x / m ∧ ρ (q + 1) = ev ρ x % m := by
  exact H.known _ (divided_known hd) pos


/-- A row is the row with its number's remainder in that number's place, and a multiple of the divisor. -/
theorem ev_rest (ρ : Nat → Int) (x : Row) (m : Int) : ev ρ x = ev ρ (Lin.rest x m) + m * (x.constant / m) := by
  simp only [ev, Lin.rest]
  have := Int.emod_add_mul_ediv x.constant m
  omega

theorem within_sound {facts : List Row} {y : Row} {m : Int} (h : within facts y m = true) (ρ : Nat → Int)
    (hf : ∀ f ∈ facts, f.holds ρ) : 0 ≤ ev ρ y ∧ ev ρ y < m := by
  unfold within at h
  simp only [Bool.and_eq_true] at h
  have g1 := plain_sound h.1 ρ hf
  have g2 := plain_sound h.2 ρ hf
  simp only [ev_sub, ev_const] at g2
  exact ⟨g1, by omega⟩

/-- A multiple of the divisor and a number from 0 to below the divisor: that number is the remainder, and the
multiple's quotient is the quotient. -/
theorem rest_sound (H : Holds ctx s0 ρ s st) {x : Row} {m : Int} (pos : 0 < m) (h : within s.facts (Lin.rest x m) m = true) :
    ev ρ (Lin.rest x m) = ev ρ x % m ∧ x.constant / m = ev ρ x / m := by
  obtain ⟨g0, g1⟩ := within_sound h ρ H.facts
  rw [ev_rest ρ x m]
  constructor
  · rw [Int.add_mul_emod_self_left]; exact (Int.emod_eq_of_lt g0 g1).symm
  · rw [Int.add_mul_ediv_left _ _ (by omega : m ≠ 0), Int.ediv_eq_zero_of_lt g0 g1]; simp

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
      | some q =>
        simp only [hd] at h
        injection h with h; subst h
        rw [ev_var]; exact (divided_spec H pos hd).2
      | none =>
        simp only [hd] at h
        split at h
        next hw =>
          injection h with h; subst h
          exact (rest_sound H pos hw).1
        next => cases h

/-- The quotient `quotOf` gives is the quotient. -/
theorem quotOf_sound (H : Holds ctx s0 ρ s st) {x r : Row} {m : Int} (pos : 0 < m) (h : quotOf s x m = some r) : ev ρ r = ev ρ x / m := by
  unfold quotOf at h
  cases hd : divided s x m with
  | some q =>
    simp only [hd] at h
    injection h with h; subst h
    rw [ev_var]; exact (divided_spec H pos hd).1
  | none =>
    simp only [hd] at h
    split at h
    next hw =>
      injection h with h; subst h
      rw [ev_const]; exact (rest_sound H pos hw).2
    next => cases h

/-- What `orSmall` gives is the two numbers' bits put together. -/
theorem orSmall_sound (H : Holds ctx s0 ρ s st) {x r : Row} {k : Int} (h : orSmall s x k = some r) :
    0 ≤ ev ρ x ∧ 0 ≤ k ∧ ev ρ r = (((ev ρ x).toNat ||| k.toNat : Nat) : Int) := by
  unfold orSmall at h
  cases hj : smallBits s.facts x with
  | none => simp [hj] at h
  | some j =>
    simp only [hj] at h
    obtain ⟨x0, xlt, _⟩ := smallBits_sound hj ρ H.facts
    split at h
    next kge =>
      have ppos : (0 : Int) < 2 ^ j := Int.pow_pos (by decide)
      have k0 : 0 ≤ k := by omega
      have ex := Int.toNat_of_nonneg x0
      have ek := Int.toNat_of_nonneg k0
      have small : (ev ρ x).toNat < 2 ^ j := Int.ofNat_lt.mp (by rw [ex]; simpa using xlt)
      have split' := or_small (k := k.toNat) small
      have kmod := emod_two_pow_toNat k0 j
      have whole := Nat.div_add_mod k.toNat (2 ^ j)
      refine ⟨x0, k0, ?_⟩
      split at h
      next h0 =>
        injection h with h; subst h
        have m0 : k.toNat % 2 ^ j = 0 := by rw [kmod] at h0; exact Int.natCast_eq_zero.mp h0
        have e : (ev ρ x).toNat ||| k.toNat = (ev ρ x).toNat + k.toNat := by rw [split', m0, Nat.or_zero]; omega
        rw [ev_add, ev_const, e]; omega
      next h0 =>
        cases hk : knownOr x (Lin.const (k % 2 ^ j)) s.known with
        | none => simp [hk] at h
        | some v =>
          simp only [hk, Option.some.injEq] at h; subst h
          have hv : ρ v = (((ev ρ x).toNat ||| (k.toNat % 2 ^ j) : Nat) : Int) := by
            rcases knownOr_mem hk with mm | mm
            · obtain ⟨_, _, g3⟩ := H.known _ mm
              rw [g3, ev_const, kmod, Int.toNat_natCast]
            · obtain ⟨_, _, g3⟩ := H.known _ mm
              rw [g3, ev_const, kmod, Int.toNat_natCast, Nat.or_comm]
          rw [ev_add, ev_const, ev_var, hv, split', kmod]; omega
    next => cases h

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
    next =>
      cases hd : divided s x W32i with
      | none => simp [hd] at h
      | some k =>
        simp only [hd, Option.map_some] at h
        injection h with h; subst h
        rw [ev_var]; exact (divided_spec H (by decide) hd).1

/-- Every term of the state's table is a word. -/
theorem Holds.den_lt (wf : WF ctx s) (i : Nat) : den (inpOf ctx s0) ρ s.terms i < W32 :=
  Ode.den_lt wf.words.table (inpOf_lt ctx s0) wf.words.rotrs i

/-- The term a word is, where it is one: the sum of the word's terms, wrapping. -/
theorem idOf_den (wf : WF ctx s) {xs : List Nat} {a : Nat} (h : idOf look xs = some a) :
    den (inpOf ctx s0) ρ s.terms a = sumList (xs.map (den (inpOf ctx s0) ρ s.terms)) % W32 := by
  have key : ∀ ys, look (.add ys) = some a →
      den (inpOf ctx s0) ρ s.terms a = sumList (ys.map (den (inpOf ctx s0) ρ s.terms)) % W32 := by
    intro ys hf
    rw [den_node wf.words.table (Looks.found hf)]
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
theorem found_den (wf : WF ctx s) {n : Node} {i : Nat} (h : look n = some i) :
    den (inpOf ctx s0) ρ s.terms i = n.value (inpOf ctx s0) ρ (den (inpOf ctx s0) ρ s.terms) := by
  exact den_node wf.words.table (Looks.found h)

/-- One term as a word. -/
theorem WDen.one (wf : WF ctx s) (i : Nat) :
    WDen ctx s0 ρ s.terms (.word [i]) (.word (den (inpOf ctx s0) ρ s.terms i)) := by
  have h := WDen.word (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) [i]
  simp only [List.map, sumList, Nat.add_zero, Nat.mod_eq_of_lt (Holds.den_lt (ctx := ctx) (s0 := s0) (ρ := ρ) wf i)] at h
  exact h

/-- The terms of a list, each as a word. -/
theorem WDen.wordsOf (wf : WF ctx s) : ∀ (ids : List Nat),
    WDen ctx s0 ρ s.terms (.list (ids.map fun i => WVal.word [i])) (.list (ids.map fun i => Val.word (den (inpOf ctx s0) ρ s.terms i)))
  | [] => WDen.nil
  | i :: rest => WDen.cons (WDen.one wf i) (WDen.wordsOf wf rest)

/-! ## A block of a lane -/

theorem sameRow_sound {facts : List Row} {ρ : Nat → Int} (hf : ∀ f ∈ facts, f.holds ρ) {a b : Row}
    (h : sameRow facts a b = true) : ev ρ a = ev ρ b := by
  simp only [sameRow, Bool.or_eq_true, Lin.same_iff, Bool.and_eq_true] at h
  rcases h with h | ⟨h1, h2⟩
  · rw [h]
  · have g1 := plainTimes_sound h1 ρ hf
    have g2 := plainTimes_sound h2 ρ hf
    rw [ev_sub] at g1 g2
    omega

/-- Two keys the verifier takes for one thing are one value. -/
theorem sameKey_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {T : List Node} {facts : List Row} (hf : ∀ f ∈ facts, f.holds ρ)
    {a b : Key} (h : sameKey facts a b = true) : a.val ctx s0 ρ T = b.val ctx s0 ρ T := by
  cases a <;> cases b
  all_goals first
    | (simp only [Key.val]; rw [sameRow_sound hf h])
    | exact congrArg (Key.val ctx s0 ρ T) (eq_of_beq h)
    | (simp only [sameKey, Bool.and_eq_true, decide_eq_true_eq] at h
       obtain ⟨⟨rfl, h1⟩, h2⟩ := h
       simp only [Key.val]; rw [sameRow_sound hf h1, sameRow_sound hf h2])

theorem sameKeys_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {T : List Node} {facts : List Row} (hf : ∀ f ∈ facts, f.holds ρ) :
    ∀ {as bs : List Key}, sameKeys facts as bs = true → as.map (Key.val ctx s0 ρ T) = bs.map (Key.val ctx s0 ρ T)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [sameKeys] at h
  | _ :: _, [], h => by simp [sameKeys] at h
  | a :: as, b :: bs, h => by
    simp only [sameKeys, Bool.and_eq_true] at h
    simp only [List.map_cons]
    rw [sameKey_sound hf h.1, sameKeys_sound hf h.2]

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
      next =>
        split at h
        next hop =>
          have oe : op = "<" := by simpa using hop
          subst oe
          split at h
          next hp =>
            injection h with h; subst h
            have g := plain_sound hp ρ H.facts
            simp only [ev_sub, ev_const] at g
            have lt : ev ρ x < ev ρ y := by omega
            exact ⟨.bool true, by simp [binop, lt], WDen.bool true⟩
          next =>
            split at h
            next hp =>
              injection h with h; subst h
              have g := plain_sound hp ρ H.facts
              simp only [ev_sub] at g
              have nlt : ¬ ev ρ x < ev ρ y := by omega
              exact ⟨.bool false, by simp [binop, nlt], WDen.bool false⟩
            next => cases h
        next =>
          split at h
          next hop =>
            have oe : op = ">=" := by simpa using hop
            subst oe
            split at h
            next hp =>
              injection h with h; subst h
              have g := plain_sound hp ρ H.facts
              simp only [ev_sub] at g
              have le : ev ρ y ≤ ev ρ x := by omega
              exact ⟨.bool true, by simp [binop, le], WDen.bool true⟩
            next =>
              split at h
              next hp =>
                injection h with h; subst h
                have g := plain_sound hp ρ H.facts
                simp only [ev_sub, ev_const] at g
                have nle : ¬ ev ρ y ≤ ev ρ x := by omega
                exact ⟨.bool false, by simp [binop, nle], WDen.bool false⟩
              next => cases h
          next =>
            split at h
            next hop =>
              have oe : op = "<=" := by simpa using hop
              subst oe
              split at h
              next hp =>
                injection h with h; subst h
                have g := plain_sound hp ρ H.facts
                simp only [ev_sub] at g
                have le : ev ρ x ≤ ev ρ y := by omega
                exact ⟨.bool true, by simp [binop, le], WDen.bool true⟩
              next =>
                split at h
                next hp =>
                  injection h with h; subst h
                  have g := plain_sound hp ρ H.facts
                  simp only [ev_sub, ev_const] at g
                  have nle : ¬ ev ρ x ≤ ev ρ y := by omega
                  exact ⟨.bool false, by simp [binop, nle], WDen.bool false⟩
                next => cases h
            next =>
              split at h
              next hop =>
                have oe : op = ">" := by simpa using hop
                subst oe
                split at h
                next hp =>
                  injection h with h; subst h
                  have g := plain_sound hp ρ H.facts
                  simp only [ev_sub, ev_const] at g
                  have gt : ev ρ y < ev ρ x := by omega
                  exact ⟨.bool true, by simp [binop, gt], WDen.bool true⟩
                next =>
                  split at h
                  next hp =>
                    injection h with h; subst h
                    have g := plain_sound hp ρ H.facts
                    simp only [ev_sub] at g
                    have ngt : ¬ ev ρ y < ev ρ x := by omega
                    exact ⟨.bool false, by simp [binop, ngt], WDen.bool false⟩
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
    | load _ _ _ | or _ _ _ | held _ _ _ | heldB _ _ _ | div _ _ _ | use _ _ _ | record _ _ _ =>
      simp only [knownBlock] at h
      obtain ⟨o, m, hs⟩ := knownBlock_mem h
      exact ⟨o, List.mem_cons_of_mem _ m, hs⟩

/-- Unknowns whose terms are in the table, as words: each is its unknown's remainder by 2^32. -/
theorem atomWords_sound (wf : WF ctx s) : ∀ {vs : List Nat} {ws : List WVal},
    atomWords look vs = some ws →
    WDen ctx s0 ρ s.terms (.list ws) (.list (vs.map fun v => Val.word ((ρ v % W32i).toNat)))
  | [], _, h => by simp only [atomWords, Option.some.injEq] at h; subst h; exact WDen.nil
  | v :: more, ws, h => by
    simp only [atomWords] at h
    cases hf : look (.atom (Lin.word (Lin.var v))) with
    | none => simp [hf] at h
    | some i =>
      cases hr : atomWords look more with
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
theorem blockAt_sound (H : Holds ctx s0 ρ s st) (wf : WF ctx s) {j c : Nat} {off : Row} {v : WVal}
    (h : blockAt look s j c off = some v) {k : Int} (hk : ev ρ off = 64 * k)
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
theorem wordIds_den (wf : WF ctx s) : ∀ {l : List WVal} {l' : List Val} {ids : List Nat},
    WDen ctx s0 ρ s.terms (.list l) (.list l') → wordIds look l = some ids →
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
        cases hi : idOf look xs <;> cases hr : wordIds look rest <;>
          simp only [hi, hr, reduceCtorEq, Option.some.injEq] at h
        rename_i i is
        subst h
        rw [wordIds_den wf hrest hr, ← idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hi]
        rfl
      | _ => simp [wordIds] at h

/-- A thing a definition is used with, as a key: the key's value is the thing's. -/
theorem flatKey_den (wf : WF ctx s) {v : WVal} {a : Val} {k : Key}
    (hd : WDen ctx s0 ρ s.terms v a) (h : flatKey look v = some k) : a = k.val ctx s0 ρ s.terms := by
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
    cases hw : wordIds look l with
    | none => simp [hw] at h
    | some ids =>
      simp only [hw, Option.map_some, Option.some.injEq] at h; subst h
      rw [wordIds_den wf hd hw]
      rfl
  | lane j c l =>
    cases hd with
    | lane _ _ _ x r count ht c8 clt =>
      simp only [flatKey, Option.some.injEq] at h; subst h
      simp only [Key.val, ht]
  | span r off len =>
    cases hd
    simp only [flatKey, Option.some.injEq] at h; subst h
    rfl
  | use u =>
    cases hd
    simp only [flatKey, Option.some.injEq] at h; subst h
    rfl
  | region r l =>
    cases hd with
    | region _ _ hl hb =>
      simp only [flatKey, Option.some.injEq] at h; subst h
      have e1 : (ρ l).toNat = s0.reg l := by rw [hl]; omega
      simp only [Key.val, ev_var, ev_const, e1, Int.toNat_zero, Nat.add_zero]
  | part r off n =>
    cases hd with
    | part _ _ _ hb =>
      simp only [flatKey, Option.some.injEq] at h; subst h
      simp only [Key.val, ev_const, Int.toNat_natCast]
  | _ => simp [flatKey] at h

theorem flatKeys_den (wf : WF ctx s) : ∀ {vs : List WVal} {as : List Val} {keys : List Key},
    WDen ctx s0 ρ s.terms (.list vs) (.list as) → flatKeys look vs = some keys →
    as = keys.map (Key.val ctx s0 ρ s.terms)
  | [], _, _, hd, h => by
    cases hd
    simp only [flatKeys, Option.some.injEq] at h; subst h; rfl
  | v :: rest, _, keys, hd, h => by
    cases hd with
    | cons hv hrest =>
      simp only [flatKeys] at h
      cases hk : flatKey look v <;> cases hr : flatKeys look rest <;>
        simp only [hk, hr, reduceCtorEq, Option.some.injEq] at h
      rename_i k ks
      subst h
      rw [flatKey_den wf hv hk, flatKeys_den wf hrest hr]
      rfl

theorem held_bound (H : Holds ctx s0 ρ s st) (hpv : ctx.contract.preVals ctx.defs s0) :
    ∃ B, HeldWithin ctx s0 ρ s.terms s.known B :=
  held_bound_list ctx s0 ρ s.terms hpv s.known H.known

end

/-! ## Operators -/

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}
variable {look : Node → Option Nat} [Looks look s.terms]

local notation "𝔻" => den (inpOf ctx s0) ρ s.terms

theorem wbin_sound (H : Holds ctx s0 ρ s st) (wf : WF ctx s) {op : String} {x y v : WVal} {xa ya : Val}
    (h : wbin look s op x y = some v) (hx : WDen ctx s0 ρ s.terms x xa) (hy : WDen ctx s0 ρ s.terms y ya) :
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
      next hmul =>
        obtain ⟨hop, hm0⟩ := hmul
        have oe : op = "*" := by simpa using hop
        subst oe
        simp only [Option.some.injEq] at h; subst h
        refine ⟨.int (a * ev ρ r), by simp [binop], ?_⟩
        have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.scale a r)
        rwa [ev_scale] at this
      next =>
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
          cases ha : idOf look xs <;> cases hb : idOf look ys <;> simp only [ha, hb, reduceCtorEq] at h
          rename_i a b
          cases hf : look (.xor (min a b) (max a b)) with
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
        cases ha : idOf look xs with
        | none => simp [ha] at h
        | some a =>
          simp only [ha] at h
          cases hf : look (.rotr a n.toNat) with
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
      next hmul =>
        obtain ⟨hop, hm0⟩ := hmul
        have oe : op = "*" := by simpa using hop
        subst oe
        simp only [Option.some.injEq] at h; subst h
        refine ⟨.int (ev ρ r * m), by simp [binop], ?_⟩
        have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.scale m r)
        rw [ev_scale, Int.mul_comm] at this
        exact this
      next =>
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
              cases hq : quotOf s r m with
              | none => simp [hq] at h
              | some r' =>
                simp only [hq, Option.map_some, Option.some.injEq] at h; subst h
                refine ⟨.int (ev ρ r / m), by simp [binop, mpos], ?_⟩
                rw [← quotOf_sound H mpos hq]; exact WDen.num r'
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
              next =>
                cases hk : knownOr r (Lin.const m) s.known with
                | none =>
                  simp only [hk] at h
                  cases ho : orSmall s r m with
                  | none => simp [ho] at h
                  | some r' =>
                    simp only [ho, Option.map_some, Option.some.injEq] at h; subst h
                    obtain ⟨r0, m0, e⟩ := orSmall_sound H ho
                    refine ⟨.int (((ev ρ r).toNat ||| m.toNat : Nat) : Int), by simp [binop, r0, m0], ?_⟩
                    rw [← e]; exact WDen.num r'
                | some v =>
                  simp only [hk, Option.some.injEq] at h; subst h
                  have hv : 0 ≤ ev ρ r ∧ 0 ≤ ev ρ (Lin.const m) ∧ ρ v = (((ev ρ r).toNat ||| (ev ρ (Lin.const m)).toNat : Nat) : Int) := by
                    rcases knownOr_mem hk with mm | mm
                    · exact H.known _ mm
                    · obtain ⟨g1, g2, g3⟩ := H.known _ mm
                      exact ⟨g2, g1, by rw [g3, Nat.or_comm]⟩
                  rw [ev_const] at hv
                  refine ⟨.int (((ev ρ r).toNat ||| m.toNat : Nat) : Int), by simp [binop, hv.1, hv.2.1], ?_⟩
                  have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.var v)
                  rw [ev_var, hv.2.2] at this
                  exact this
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
  | counter r =>
    cases y with
    | int n =>
      cases hy
      cases hx with
      | counter _ r0 =>
        simp only [wbin] at h
        split at h
        next hc =>
          obtain ⟨hop, n0⟩ := hc
          have oe : op = "+" := by simpa using hop
          subst oe
          injection h with h; subst h
          refine ⟨.counter (((ev ρ r).toNat % 2 ^ 64 + n.toNat) % 2 ^ 64), by simp [binop, n0], ?_⟩
          by_cases nz : n = 0
          · subst nz
            have e : ((ev ρ r).toNat % 2 ^ 64 + (0 : Int).toNat) % 2 ^ 64 = (ev ρ r).toNat % 2 ^ 64 := by omega
            rw [if_pos rfl, e]; exact WDen.counter r r0
          · have r1 : 0 ≤ ev ρ (Lin.add r (Lin.const n)) := by rw [ev_add, ev_const]; omega
            have e : ((ev ρ r).toNat % 2 ^ 64 + n.toNat) % 2 ^ 64 = (ev ρ (Lin.add r (Lin.const n))).toNat % 2 ^ 64 := by
              rw [ev_add, ev_const]; omega
            rw [if_neg nz, e]; exact WDen.counter _ r1
        next => cases h
    | _ => simp [wbin] at h
  | _ => cases y <;> simp [wbin] at h

/-- The high word of a counter that is a number and a number of the text more: what `hiPlus` finds is it. -/
theorem hiPlus_sound (H : Holds ctx s0 ρ s st) (wf : WF ctx s) {r : Row} {i : Nat}
    (h : hiPlus look s r = some i) :
    den (inpOf ctx s0) ρ s.terms i = (ev ρ r).toNat % 2 ^ 64 / W32 := by
  unfold hiPlus at h
  split at h
  next hc =>
    obtain ⟨c0, c1, hn⟩ := hc
    split at h
    next a l hh one ha hl hhh hone =>
      cases hm : look (.ult a l) with
      | none => simp [hm] at h
      | some m =>
        cases hs : look (.add (insertSorted hh (insertSorted one []))) with
        | none => simp [hm, hs] at h
        | some h1 =>
          simp only [hm, hs, Option.bind_some] at h
          cases hq : highOf s ⟨r.coeff, 0⟩ with
          | none => simp [hq] at hhh
          | some q =>
            simp only [hq, Option.bind_some] at hhh
            have di := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf h
            have dm := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hm
            have d1 := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hs
            have da := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf ha
            have dl := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hl
            have dh := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hhh
            have d0 := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hone
            have eq := highOf_sound (ρ := ρ) H hq
            have b0 := knownNonneg_sound (ρ := ρ) H hn
            have er : ev ρ r = ev ρ ⟨r.coeff, 0⟩ + r.constant := by simp [ev]
            simp only [Node.value] at di dm d1 da dl dh d0
            have fs : insertSorted hh (insertSorted one []) = [hh, one].foldr insertSorted [] := rfl
            rw [fs, sumList_sorted] at d1
            simp only [List.map, sumList, Nat.add_zero] at d1
            rw [ev_word] at da dl dh d0
            rw [ev_const] at d0
            rw [di, dm, d1, da, dl, dh, d0, eq, er]
            generalize ev ρ ⟨r.coeff, 0⟩ = R at b0 ⊢
            generalize r.constant = c at c0 c1 ⊢
            unfold W32i at c1 ⊢
            unfold W32
            by_cases lt : ((R + c) % 4294967296).toNat < (R % 4294967296).toNat
            · rw [if_pos lt, if_neg (by decide)]; omega
            · rw [if_neg lt, if_pos rfl]; omega
    next => cases h
  next => cases h

end

/-! ## The words of a run of bytes -/

theorem map_range_succ {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl

theorem map_range_add4 {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 4)).map f = f 0 :: f 1 :: f 2 :: f 3 :: (List.range n).map (fun i => f (i + 4)) := by
  rw [show n + 4 = n + 1 + 1 + 1 + 1 from rfl, map_range_succ, map_range_succ, map_range_succ, map_range_succ]

/-- A part of a run of bytes, cut out of the list of them. -/
theorem slice_run (mem : Nat → Byte) (base n a b : Nat) (h : a + b ≤ n) :
    (((List.range n).map fun k => Val.int (mem (base + k))).drop a).take b = (List.range b).map fun k => Val.int (mem (base + a + k)) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp [Nat.add_assoc]

/-- The number that bytes of memory are, the lowest first: what the machine's `load` reads there. -/
theorem numberLE_load (mem : Nat → Byte) : ∀ (n a : Nat), (∀ k, k < n → (mem (a + k)).val < 256) →
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

/-- The four bytes of each word, in `flatMap` form. -/
theorem wordBytes_eq_flatMap : ∀ (ws : List Nat),
    wordBytes ws = ws.flatMap (fun w =>
      [.int (w % 256 : Nat), .int (w / 256 % 256 : Nat), .int (w / 65536 % 256 : Nat), .int (w / 16777216 % 256 : Nat)])
  | [] => rfl
  | w :: rest => by simp [wordBytes, wordBytes_eq_flatMap rest]

theorem wordBytes_length : ∀ (ws : List Nat), (wordBytes ws).length = 4 * ws.length
  | [] => rfl
  | _ :: rest => by simp [wordBytes, wordBytes_length rest]; omega

theorem wordBytes_drop : ∀ (ws : List Nat) (k : Nat), (wordBytes ws).drop (4 * k) = wordBytes (ws.drop k)
  | [], _ => by simp only [wordBytes, List.drop_nil]
  | _, 0 => by simp only [Nat.mul_zero, List.drop_zero]
  | w :: rest, k + 1 => by
    have e : 4 * (k + 1) = (4 * k + 3) + 1 := by omega
    rw [e, wordBytes, List.drop_succ_cons, List.drop_succ_cons, List.drop_succ_cons, List.drop_succ_cons]
    exact wordBytes_drop rest k

theorem wordBytes_take : ∀ (ws : List Nat) (k : Nat), (wordBytes ws).take (4 * k) = wordBytes (ws.take k)
  | [], _ => by simp only [wordBytes, List.take_nil]
  | _, 0 => by simp only [Nat.mul_zero, List.take_zero, wordBytes]
  | w :: rest, k + 1 => by
    have e : 4 * (k + 1) = (4 * k + 3) + 1 := by omega
    rw [e, wordBytes, List.take_succ_cons, List.take_succ_cons, List.take_succ_cons, List.take_succ_cons]
    exact congrArg (fun t => _ :: _ :: _ :: _ :: t) (wordBytes_take rest k)

theorem numberLE_wordBytes1 {w : Nat} (h : w < W32) (rest : List Val) {n : Nat}
    (hr : numberLE rest = some n) :
    numberLE (wordBytes [w] ++ rest) = some (w + W32 * n) := by
  unfold W32 at h ⊢
  simp only [wordBytes, List.cons_append, List.nil_append]
  rw [numberLE, if_pos ⟨by omega, by omega⟩, numberLE, if_pos ⟨by omega, by omega⟩,
      numberLE, if_pos ⟨by omega, by omega⟩, numberLE, if_pos ⟨by omega, by omega⟩, hr]
  simp only [Option.map_some, Int.toNat_natCast, Option.some.injEq]; omega

theorem numberLE_wordBytes2 {w1 w2 : Nat} (h1 : w1 < W32) (h2 : w2 < W32) :
    numberLE (wordBytes [w1, w2]) = some (w1 + W32 * w2) := by
  have h2' := numberLE_wordBytes1 h2 [] rfl
  simp only [List.append_nil, Nat.mul_zero, Nat.add_zero] at h2'
  have h1' := numberLE_wordBytes1 h1 (wordBytes [w2]) h2'
  simpa [wordBytes] using h1'

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
variable {look : Node → Option Nat} [Looks look s.terms]

/-- The words of the table that are a run's words: they are what the account's `words` makes of the run's
bytes, four bytes a word, the lowest first. -/
theorem toWords_fn (wf : WF ctx s) {j : Nat} : ∀ (count k : Nat) (g : Nat → Nat) (wvs : List WVal),
    inputWords look j count k = some wvs → (∀ i, i < 4 * count → g i < 256) →
    (∀ q a, a = 4 * q → q < count →
      inpOf ctx s0 j (k + q) = g a + 256 * g (a + 1) + 65536 * g (a + 2) + 16777216 * g (a + 3)) →
    ∃ ws, toWords ((List.range (4 * count)).map fun i => Val.int (g i)) = some ws ∧ WDen ctx s0 ρ s.terms (.list wvs) (.list ws)
  | 0, k, g, wvs, h, _, _ => by
    simp only [inputWords, Option.some.injEq] at h; subst h
    exact ⟨[], by simp [toWords], WDen.nil⟩
  | count + 1, k, g, wvs, h, hb, hwd => by
    simp only [inputWords] at h
    cases hf : look (.input j k) <;> cases hr : inputWords look j count (k + 1) <;>
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

theorem load4 (mem : Nat → Byte) (a : Nat) :
    load mem a 4 = mem a % 256 + 256 * (mem (a + 1) % 256 + 256 * (mem (a + 1 + 1) % 256 + 256 * (mem (a + 1 + 1 + 1) % 256 + 256 * 0))) := by
  simp only [load]; omega

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}
variable {look : Node → Option Nat} [Looks look s.terms]

local notation "𝔻" => den (inpOf ctx s0) ρ s.terms

theorem pbytesSpan_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {T : List Node} :
    ∀ (r off : Nat) (bs : List WVal) (as : List Val),
      WDen ctx s0 ρ T (.list bs) (.list as) → pbytesSpan r off bs = true →
      as = (List.range bs.length).map (fun k => Val.int (s0.mem (s0.reg r + off + k))) ∧
      ∀ k, k < bs.length → (s0.mem (s0.reg r + off + k)).val < 256
  | _, _, [], _, hd, _ => by cases hd; exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | r, off, b :: more, _, hd, hp => by
    cases hd with
    | cons h1 h2 =>
      cases b with
      | pbyte r' off' =>
        simp only [pbytesSpan, Bool.and_eq_true, decide_eq_true_eq] at hp
        obtain ⟨⟨hr, hoff⟩, hpm⟩ := hp
        subst hr; subst hoff
        cases h1 with
        | pbyte _ _ hb =>
          obtain ⟨has, hbm⟩ := pbytesSpan_sound r' (off' + 1) more _ h2 hpm
          refine ⟨?_, ?_⟩
          · rw [has, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
            simp only [Nat.add_zero]
            congr 1
            apply List.map_congr_left
            intro k _
            have e : s0.reg r' + (off' + 1) + k = s0.reg r' + off' + (k + 1) := by omega
            simp [Function.comp, e]
          · intro k hk
            simp only [List.length_cons] at hk
            cases k with
            | zero => simp [hb]
            | succ k =>
              have := hbm k (by omega)
              have e : s0.reg r' + off' + (k + 1) = s0.reg r' + (off' + 1) + k := by omega
              rw [e]; exact this
      | _ => simp [pbytesSpan] at hp

theorem wown_sound (H : Holds ctx s0 ρ s st) (wf : WF ctx s) {f : String} {vs : List WVal} {as : List Val} {v : WVal}
    (h : wown ctx look s f vs = some v) (hv : WDen ctx s0 ρ s.terms (.list vs) (.list as)) :
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
            cases hfn : look (.atom (Lin.word (Lin.const n))) with
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
          have r0 : 0 ≤ ev ρ r := plain_sound (g := r) (by simpa using hk) ρ H.facts
          split at h
          next hf =>
            have fe : f = "word" := by simpa using hf
            subst fe
            cases hfn : look (.atom (Lin.word r)) with
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
              cases hfn : look (.atom (Lin.word r)) with
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
                split at h
                next v hold =>
                  injection h with h; subst h
                  have h := hold
                  cases hq : highOf s r with
                  | none => simp [hq] at h
                  | some q =>
                    simp only [hq, Option.bind_some] at h
                    cases hfn : look (.atom (Lin.word q)) with
                    | none => simp [hfn] at h
                    | some i =>
                      simp only [hfn, Option.map_some, Option.some.injEq] at h; subst h
                      have di : 𝔻 i = (ev ρ (Lin.word q) % W32i).toNat := found_den wf hfn
                      have eq := highOf_sound H hq
                      refine ⟨.word ((ev ρ r).toNat % 2 ^ 64 / W32), by simp [builtin], ?_⟩
                      have e : (ev ρ r).toNat % 2 ^ 64 / W32 = 𝔻 i := by rw [di, ev_word, eq]; unfold W32 W32i; omega
                      rw [e]; exact WDen.one wf i
                next =>
                  -- the counter is a number and a number of the text more
                  cases hp : hiPlus look s r with
                  | none => simp [hp] at h
                  | some i =>
                    simp only [hp, Option.map_some, Option.some.injEq] at h; subst h
                    refine ⟨.word ((ev ρ r).toNat % 2 ^ 64 / W32), by simp [builtin], ?_⟩
                    rw [← hiPlus_sound H wf hp]; exact WDen.one wf i
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
            cases hra : runAt r ctx.contract.wordRuns 0 with
            | none => simp [hra] at h
            | some j =>
              simp only [hra, Option.bind_some] at h
              cases hin : inputWords look j (n / 4) 0 with
              | none => simp [hin] at h
              | some wvs =>
                simp only [hin, Option.map_some, Option.some.injEq] at h; subst h
                obtain ⟨_, x', n', hj⟩ := runAt_spec hra
                have hj' : ctx.contract.wordRuns[j]? = some (x', r, n') := by simpa using hj
                obtain ⟨ws, hw, hd⟩ := toWords_fn (ctx := ctx) (s0 := s0) (ρ := ρ) wf (n / 4) 0 (fun i => (s0.mem (s0.reg r + i)).val) wvs hin
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
            cases hra : runAt r ctx.contract.wordRuns 0 with
            | none => simp [hra] at h
            | some j =>
              simp only [hra, Option.bind_some] at h
              cases hin : inputWords look j (n / 4) (off / 4) with
              | none => simp [hin] at h
              | some wvs =>
                simp only [hin, Option.map_some, Option.some.injEq] at h; subst h
                obtain ⟨_, x', n', hj⟩ := runAt_spec hra
                have hj' : ctx.contract.wordRuns[j]? = some (x', r, n') := by simpa using hj
                obtain ⟨ws, hw, hd⟩ := toWords_fn (ctx := ctx) (s0 := s0) (ρ := ρ) wf (n / 4) (off / 4) (fun i => (s0.mem (s0.reg r + off + i)).val) wvs hin
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
        next =>
          split at h
          next hf =>
            have fe : f = "number.le" := by simpa using hf
            subst fe
            cases ids with
            | nil => simp at h
            | cons a rest =>
              cases rest with
              | nil => simp at h
              | cons b rest2 =>
                cases rest2 with
                | cons _ _ => simp at h
                | nil =>
                  simp only at h
                  cases ha : s.tab.arr[a]? with
                  | none => simp [ha] at h
                  | some na =>
                    cases na with
                    | atom r1 =>
                      cases hb : s.tab.arr[b]? with
                      | none => simp [ha, hb] at h
                      | some nb =>
                        cases nb with
                        | atom r2 =>
                          simp only [ha, hb] at h
                          split at h
                          next hc =>
                            simp only [Option.some.injEq] at h; subst h
                            simp only [Bool.and_eq_true] at hc
                            obtain ⟨⟨⟨k1, p1⟩, k2⟩, p2⟩ := hc
                            have h1_0 := knownNonneg_sound H k1
                            have h1_u := plain_sound p1 ρ H.facts
                            have h2_0 := knownNonneg_sound H k2
                            have h2_u := plain_sound p2 ρ H.facts
                            simp only [ev_sub, ev_const] at h1_u h2_u
                            have ha' : s.terms[a]? = some (.atom r1) := by simpa [Sym.terms, Tab.list] using ha
                            have hb' : s.terms[b]? = some (.atom r2) := by simpa [Sym.terms, Tab.list] using hb
                            have da : 𝔻 a = (ev ρ r1).toNat := by
                              have := den_node (inp := inpOf ctx s0) (ρ := ρ) wf.words.table ha'
                              simp only [Node.value] at this
                              rw [this, Int.emod_eq_of_lt h1_0 (by unfold W32i at h1_u ⊢; omega)]
                            have db : 𝔻 b = (ev ρ r2).toNat := by
                              have := den_node (inp := inpOf ctx s0) (ρ := ρ) wf.words.table hb'
                              simp only [Node.value] at this
                              rw [this, Int.emod_eq_of_lt h2_0 (by unfold W32i at h2_u ⊢; omega)]
                            have hlt1 : 𝔻 a < W32 := Holds.den_lt wf a
                            have hlt2 : 𝔻 b < W32 := Holds.den_lt wf b
                            have hle := numberLE_wordBytes2 hlt1 hlt2
                            refine ⟨.int (𝔻 a + W32 * 𝔻 b : Nat), ?_, ?_⟩
                            · simp [builtin, hle]
                            · have key := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.add r1 (Lin.scale W32i r2))
                              have ev_eq : ev ρ (Lin.add r1 (Lin.scale W32i r2)) = ((𝔻 a + W32 * 𝔻 b : Nat) : Int) := by
                                rw [ev_add, ev_scale, da, db]
                                unfold W32i at h1_u h2_u ⊢; unfold W32
                                omega
                              rw [ev_eq] at key; exact key
                          next => cases h
                        | _ => simp [ha, hb] at h
                    | _ => simp [ha] at h
          next => simp at h
      | list bs =>
        cases bs with
        | nil => simp [wown] at h
        | cons b0 more =>
          cases b0 with
          | pbyte r off =>
            obtain ⟨as', rfl⟩ := WDen.list_inv hx
            simp only [wown] at h
            split at h
            next hc =>
              obtain ⟨hf, o4, n4, hps⟩ := hc
              have fe : f = "words" := by simpa using hf
              subst fe
              cases hra : runAt r ctx.contract.wordRuns 0 with
              | none => simp [hra] at h
              | some j =>
                simp only [hra, Option.bind_some] at h
                cases hin : inputWords look j ((more.length + 1) / 4) (off / 4) with
                | none => simp [hin] at h
                | some wvs =>
                  simp only [hin, Option.map_some, Option.some.injEq] at h; subst h
                  obtain ⟨_, x', n', hj⟩ := runAt_spec hra
                  have hj' : ctx.contract.wordRuns[j]? = some (x', r, n') := by simpa using hj
                  obtain ⟨has', hb⟩ := pbytesSpan_sound r off (.pbyte r off :: more) as' hx hps
                  simp only [List.length_cons] at has' hb
                  obtain ⟨ws, hw, hd⟩ := toWords_fn (ctx := ctx) (s0 := s0) (ρ := ρ) wf ((more.length + 1) / 4) (off / 4)
                    (fun i => (s0.mem (s0.reg r + off + i)).val) wvs hin
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
                  have en : 4 * ((more.length + 1) / 4) = more.length + 1 := by omega
                  rw [en] at hw
                  rw [has']
                  exact ⟨.list ws, by simp [builtin, hw], hd⟩
            next => simp at h
          | _ => simp [wown] at h
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

/-- The first number of which the condition is true, found on the terms: the account finds the same. -/
theorem wfirstWith_sound {ev : Int → Option WVal} {ev' : Int → Option Val}
    (hev : ∀ i v, ev i = some v → ∃ a, ev' i = some a ∧ WDen ctx s0 ρ s.terms v a) :
    ∀ (l : List Int) (v : WVal), wfirstWith ev l = some v →
      ∃ a, firstWith ev' l = some a ∧ WDen ctx s0 ρ s.terms v a
  | [], v, h => by simp [wfirstWith] at h
  | n :: rest, v, h => by
    simp only [wfirstWith] at h
    cases hn : ev n with
    | none => simp [hn] at h
    | some r =>
      obtain ⟨a, ea, da⟩ := hev n r hn
      cases r with
      | bool c =>
        cases da
        cases c with
        | true =>
          simp only [hn, Option.some.injEq] at h; subst h
          exact ⟨.int n, by simp only [firstWith, ea], WDen.int n⟩
        | false =>
          simp only [hn] at h
          obtain ⟨a, e, d⟩ := wfirstWith_sound hev rest v h
          exact ⟨a, by simp only [firstWith, ea]; exact e, d⟩
      | _ => simp [hn] at h

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
variable {look : Node → Option Nat} [Looks look s.terms]

theorem isWordIds_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} (wf : WF ctx s) :
    ∀ {ws : List WVal} {ids : List Nat} {vs : List Val},
    isWordIds ws ids = true → WDen ctx s0 ρ s.terms (.list ws) (.list vs) →
    vs = ids.map (fun i => Val.word (den (inpOf ctx s0) ρ s.terms i))
  | [], [], _, _, hd => by cases hd; rfl
  | [], _ :: _, _, hm, _ => by simp [isWordIds] at hm
  | _ :: _, [], _, hm, _ => by cases ‹WVal› <;> simp [isWordIds] at hm
  | w :: ws, j :: js, vs, hm, hd => by
    cases w with
    | word xs =>
      cases xs with
      | nil => simp [isWordIds] at hm
      | cons i xs2 =>
        cases xs2 with
        | cons _ _ => simp [isWordIds] at hm
        | nil =>
          simp only [isWordIds, Bool.and_eq_true, beq_iff_eq] at hm
          obtain ⟨rfl, hm'⟩ := hm
          cases hd with
          | cons h1 hrest =>
            cases h1
            have hlt := Holds.den_lt (s0 := s0) (ρ := ρ) wf i
            simp only [List.map_cons, List.map_nil, sumList, Nat.add_zero, Nat.mod_eq_of_lt hlt]
            rw [isWordIds_sound wf hm' hrest]
    | _ => simp [isWordIds] at hm

theorem recMatches_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) :
    ∀ {fields : List RecField} {ids : List Nat} {fvs : List (String × WVal)} {fs' fs0 : List (String × Val)},
    recMatches s.facts s.tab.arr fields ids fvs = true →
    WDen ctx s0 ρ s.terms (.record fvs) (.record fs') →
    RecFieldsHolds fields (ids.map (den (inpOf ctx s0) ρ s.terms)) fs0 →
    fs0 = fs'
  | [], [], [], _, fs0, _, hd, hr => by
    cases hd
    cases fs0 with
    | nil => rfl
    | cons _ _ => exact hr.elim
  | [], _ :: _, _, _, _, hm, _, _ => by simp [recMatches] at hm
  | [], [], _ :: _, _, _, hm, _, _ => by simp [recMatches] at hm
  | .words fn n :: fs, ids, fvs, fs', fs0, hm, hd, hr => by
    cases fvs with
    | nil => simp [recMatches] at hm
    | cons fv rest =>
      obtain ⟨x, v⟩ := fv
      cases v with
      | list ws =>
        simp only [recMatches, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
        obtain ⟨⟨⟨rfl, hlen⟩, hwi⟩, hrm⟩ := hm
        cases hd with
        | rcons hv hrest =>
          obtain ⟨as', rfl⟩ := WDen.list_inv hv
          cases fs0 with
          | nil => exact hr.elim
          | cons p0 r0 =>
            obtain ⟨x0, v0⟩ := p0
            cases v0 with
            | list vs0 =>
              obtain ⟨hx0, _, hvs0, hr'⟩ := hr
              have hwas := isWordIds_sound wf hwi hv
              have heq : vs0 = as' := by
                rw [hvs0, hwas, ← List.map_take, List.map_map]
                rfl
              have htail := recMatches_sound H wf hrm hrest (by rwa [← List.map_drop] at hr')
              subst hx0; subst heq; subst htail; rfl
            | _ => exact hr.elim
      | _ => simp [recMatches] at hm
  | .bytes fn n :: fs, ids, fvs, fs', fs0, hm, hd, hr => by
    cases fvs with
    | nil => simp [recMatches] at hm
    | cons fv rest =>
      obtain ⟨x, v⟩ := fv
      cases v with
      | wbytes bs =>
        simp only [recMatches, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
        obtain ⟨⟨⟨⟨rfl, hmod⟩, hlen⟩, hbs⟩, hrm⟩ := hm
        cases hd with
        | rcons hv hrest =>
          cases hv
          cases fs0 with
          | nil => exact hr.elim
          | cons p0 r0 =>
            obtain ⟨x0, v0⟩ := p0
            cases v0 with
            | list vs0 =>
              obtain ⟨hx0, _, _, hvs0, hr'⟩ := hr
              have heq : vs0 = wordBytes (bs.map (den (inpOf ctx s0) ρ s.terms)) := by
                rw [hvs0, hbs, ← List.map_take, wordBytes_eq_flatMap]
              have htail := recMatches_sound H wf hrm hrest (by rwa [← List.map_drop] at hr')
              subst hx0; subst heq; subst htail; rfl
            | _ => exact hr.elim
      | _ => simp [recMatches] at hm
  | .u64 fn bd :: fs, ids, fvs, fs', fs0, hm, hd, hr => by
    cases ids with
    | nil => simp [recMatches] at hm
    | cons a ids1 =>
      cases ids1 with
      | nil => simp [recMatches] at hm
      | cons b more =>
        cases fvs with
        | nil => simp [recMatches] at hm
        | cons fv rest =>
          obtain ⟨x, v⟩ := fv
          cases v with
          | num r =>
            simp only [recMatches, Bool.and_eq_true, beq_iff_eq] at hm
            obtain ⟨⟨rfl, hab⟩, hrm⟩ := hm
            cases ha : s.tab.arr[a]? with
            | none => simp [ha] at hab
            | some na =>
              cases na with
              | atom r1 =>
                cases hb : s.tab.arr[b]? with
                | none => simp [ha, hb] at hab
                | some nb =>
                  cases nb with
                  | atom r2 =>
                    simp only [ha, hb, Bool.and_eq_true] at hab
                    obtain ⟨⟨⟨⟨p1, p1u⟩, p2⟩, p2u⟩, hsr⟩ := hab
                    have h1_0 := plain_sound p1 ρ H.facts
                    have h1_u := plain_sound p1u ρ H.facts
                    have h2_0 := plain_sound p2 ρ H.facts
                    have h2_u := plain_sound p2u ρ H.facts
                    simp only [ev_sub, ev_const] at h1_u h2_u
                    have ha' : s.terms[a]? = some (.atom r1) := by simpa [Sym.terms, Tab.list] using ha
                    have hb' : s.terms[b]? = some (.atom r2) := by simpa [Sym.terms, Tab.list] using hb
                    have da : den (inpOf ctx s0) ρ s.terms a = (ev ρ r1).toNat := by
                      have := den_node (inp := inpOf ctx s0) (ρ := ρ) wf.words.table ha'
                      simp only [Node.value] at this
                      rw [this, Int.emod_eq_of_lt h1_0 (by unfold W32i at h1_u ⊢; omega)]
                    have db : den (inpOf ctx s0) ρ s.terms b = (ev ρ r2).toNat := by
                      have := den_node (inp := inpOf ctx s0) (ρ := ρ) wf.words.table hb'
                      simp only [Node.value] at this
                      rw [this, Int.emod_eq_of_lt h2_0 (by unfold W32i at h2_u ⊢; omega)]
                    have hsame := sameRow_sound H.facts hsr
                    rw [ev_add, ev_scale] at hsame
                    cases hd with
                    | rcons hv hrest =>
                      cases hv
                      cases fs0 with
                      | nil => exact hr.elim
                      | cons p0 r0 =>
                        obtain ⟨x0, v0⟩ := p0
                        cases v0 with
                        | int v0 =>
                          obtain ⟨hx0, _, _, _, hv0, _, _, hr'⟩ := hr
                          have hv_eq : v0 = ev ρ r := by
                            rw [hv0, da, db, Int.toNat_of_nonneg h1_0, Int.toNat_of_nonneg h2_0, hsame]
                          have htail := recMatches_sound H wf hrm hrest hr'
                          subst hx0; subst hv_eq; subst htail; rfl
                        | _ => exact hr.elim
                  | _ => simp [ha, hb] at hab
              | _ => simp [ha] at hab
          | _ => simp [recMatches] at hm

theorem knownRec_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hpv : ctx.contract.preVals ctx.defs s0)
    {fvs : List (String × WVal)} {fs' : List (String × Val)} :
    ∀ {l : List Known} {h : Nat}, (∀ k ∈ l, k.holds ctx s0 ρ s.terms) →
    knownRec s.facts s.tab.arr fvs l = some h →
    WDen ctx s0 ρ s.terms (.record fvs) (.record fs') →
    Val.decode (ρ h).toNat = .record fs'
  | [], _, _, hk, _ => by simp [knownRec] at hk
  | k :: more, h, hkh, hk, hd => by
    cases k with
    | record u fields ids =>
      simp only [knownRec] at hk
      split at hk
      next hm =>
        injection hk with hk; subst hk
        obtain ⟨fs0, hdec, hrf⟩ := hkh _ (List.mem_cons_self ..) hpv
        rw [hdec, recMatches_sound H wf hm hd hrf]
      next => exact knownRec_sound H wf hpv (fun k' m => hkh k' (List.mem_cons_of_mem _ m)) hk hd
    | load _ _ _ | or _ _ _ | held _ _ _ | heldB _ _ _ | div _ _ _ | block _ _ _ _ | use _ _ _ =>
      simp only [knownRec] at hk
      exact knownRec_sound H wf hpv (fun k' m => hkh k' (List.mem_cons_of_mem _ m)) hk hd

/-- What `weval` gives of an expression stands for what `evalSpec` gives of it with the same fuel and `B`
more, the names on words standing for the names of the account: `B` being steps enough for every use of a
definition whose words the state holds (such a use costs `weval` nothing, and `evalSpec` works it out). -/
theorem weval_sound (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hpv : ctx.contract.preVals ctx.defs s0)
    {B : Nat} (hB : HeldWithin ctx s0 ρ s.terms s.known B) :
    ∀ (fuel : Nat) (env : List (String × WVal)) (env' : List (String × Val)) (e : SExpr) (v : WVal),
      weval ctx look s fuel env e = some v → EnvDen ctx s0 ρ s.terms env env' →
      ∃ a, evalSpec ctx.defs (fuel + B) env' e = some a ∧ WDen ctx s0 ρ s.terms v a
  | 0, _, _, _, _, h, _ => by simp [weval] at h
  | fuel + 1, env, env', e, v, h, hE => by
    have ih := weval_sound H wf hpv hB fuel
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
      cases ha : weval ctx look s fuel env a <;> cases hb : weval ctx look s fuel env b <;>
        simp only [ha, hb, reduceCtorEq] at h
      rename_i x y
      obtain ⟨xa, ea, da⟩ := ih env env' a x ha hE
      obtain ⟨ya, eb, db⟩ := ih env env' b y hb hE
      obtain ⟨r, er, dr⟩ := wbin_sound H wf h da db
      refine ⟨r, ?_, dr⟩
      simp only [evalSpec, ea, eb]; exact er
    | ifx c a b =>
      simp only [weval] at h
      cases hc : weval ctx look s fuel env c with
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
      cases ha : weval ctx look s fuel env a <;> cases hi : weval ctx look s fuel env i <;>
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
      | run r n =>
        cases iv with
        | int k =>
          cases di
          cases da with
          | run _ _ hb =>
            simp only at h
            split at h
            next hk =>
              simp only [Option.some.injEq] at h; subst h
              refine ⟨Val.int (s0.mem (s0.reg r + k.toNat)), ?_, WDen.pbyte r k.toNat (hb k.toNat hk.2)⟩
              simp only [evalSpec, ea, ei]; rw [if_pos hk.1, List.getElem?_map, List.getElem?_range hk.2]; rfl
            next => simp at h
        | _ => simp at h
      | part r off n =>
        cases iv with
        | int k =>
          cases di
          cases da with
          | part _ _ _ hb =>
            simp only at h
            split at h
            next hk =>
              simp only [Option.some.injEq] at h; subst h
              have e : s0.reg r + (off + k.toNat) = s0.reg r + off + k.toNat := by omega
              refine ⟨Val.int (s0.mem (s0.reg r + off + k.toNat)), ?_, ?_⟩
              · simp only [evalSpec, ea, ei]; rw [if_pos hk.1, List.getElem?_map, List.getElem?_range hk.2]; rfl
              · rw [← e]; exact WDen.pbyte r (off + k.toNat) (by rw [e]; exact hb k.toNat hk.2)
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
      cases hl : wevalList (weval ctx look s fuel env) args with
      | none => simp [hl] at h
      | some vs =>
        simp only [hl] at h
        obtain ⟨as, el, dl⟩ := wevalList_sound (ev' := evalSpec ctx.defs (fuel + B) env') (fun e v hv => ih env env' e v hv hE) args vs hl
        split at h
        next hlen =>
          -- how many bytes a run of bytes with a length is, or a part of one
          split at h
          next r l =>
            simp only [Option.some.injEq] at h; subst h
            cases dl with
            | cons hv hrest =>
              cases hrest
              cases hv with
              | region _ _ hl hb =>
                have key := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (Lin.var l)
                rw [ev_var, hl] at key
                refine ⟨_, ?_, key⟩
                simp only [evalSpec, el]; rw [if_pos hlen]; simp
          next r off len =>
            simp only [Option.some.injEq] at h; subst h
            cases dl with
            | cons hv hrest =>
              cases hrest
              cases hv with
              | span _ _ _ ho hn =>
                have key := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) len
                refine ⟨_, ?_, key⟩
                simp only [evalSpec, el]; rw [if_pos hlen]
                simp only [List.length_map, List.length_range, Option.some.injEq, Val.int.injEq]
                omega
          next r n =>
            simp only [Option.some.injEq] at h; subst h
            cases dl with
            | cons hv hrest =>
              cases hrest
              cases hv with
              | run _ _ _ =>
                refine ⟨_, ?_, WDen.int n⟩
                simp only [evalSpec, el]; rw [if_pos hlen]; simp
          next r off n =>
            simp only [Option.some.injEq] at h; subst h
            cases dl with
            | cons hv hrest =>
              cases hrest
              cases hv with
              | part _ _ _ _ =>
                refine ⟨_, ?_, WDen.int n⟩
                simp only [evalSpec, el]; rw [if_pos hlen]; simp
          next l =>
            simp only [Option.some.injEq] at h; subst h
            cases dl with
            | cons hv hrest =>
              cases hrest
              obtain ⟨as', rfl⟩ := WDen.list_inv hv
              refine ⟨_, ?_, WDen.int l.length⟩
              simp only [evalSpec, el]; rw [if_pos hlen, ← WDen.length hv]
          next ids =>
            simp only [Option.some.injEq] at h; subst h
            cases dl with
            | cons hv hrest =>
              cases hrest
              cases hv
              refine ⟨_, ?_, WDen.int (4 * ids.length)⟩
              simp only [evalSpec, el]; rw [if_pos hlen]
              simp [wordBytes_length]
          next => simp at h
        next hlen =>
          split at h
          next hown =>
            obtain ⟨r, er, dr⟩ := wown_sound H wf h dl
            refine ⟨r, ?_, dr⟩
            simp only [evalSpec, el]; rw [if_neg hlen, if_pos hown]; exact er
          next hown =>
            split at h
            next =>
              -- the state knows nothing of the definition: its text is followed
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
            next =>
            cases hh : ((flatKeys look vs).bind fun keys => heldIds s.facts f keys s.known) with
            | some ids =>
              -- a use the state holds the words of (of the same things, by the facts): the definition gives
              -- them within `B` steps
              simp only [hh, Option.some.injEq] at h; subst h
              obtain ⟨keys, hk, hi⟩ := Option.bind_eq_some_iff.mp hh
              obtain ⟨keys', hm, same⟩ := heldIds_mem hi
              obtain ⟨d, hd, hlen', hev⟩ := hB _ hm
              have eas : as = keys.map (Key.val ctx s0 ρ s.terms) := flatKeys_den wf dl hk
              have ekeys : keys'.map (Key.val ctx s0 ρ s.terms) = keys.map (Key.val ctx s0 ρ s.terms) := sameKeys_sound H.facts same
              have hp' : (d.params.length == as.length) = true := by rw [eas, ← ekeys, List.length_map]; simpa using hlen'
              refine ⟨.list (ids.map fun i => Val.word (den (inpOf ctx s0) ρ s.terms i)), ?_, WDen.wordsOf wf ids⟩
              simp only [evalSpec, el]; rw [if_neg hlen, if_neg hown]; simp only [hd]; rw [if_pos hp', eas, ← ekeys]
              exact evalSpec_mono ctx.defs B hev (fuel + B) (Nat.le_add_left _ _)
            | none =>
              simp only [hh] at h
              cases hh2 : ((flatKeys look vs).bind fun keys => heldBytes s.facts f keys s.known) with
              | some ids =>
                -- a use the state holds the bytes of: the definition gives them within `B` steps
                simp only [hh2, Option.some.injEq] at h; subst h
                obtain ⟨keys, hk, hi⟩ := Option.bind_eq_some_iff.mp hh2
                obtain ⟨keys', hm, same⟩ := heldBytes_mem hi
                obtain ⟨d, hd, hlen', hev⟩ := hB _ hm
                have eas : as = keys.map (Key.val ctx s0 ρ s.terms) := flatKeys_den wf dl hk
                have ekeys : keys'.map (Key.val ctx s0 ρ s.terms) = keys.map (Key.val ctx s0 ρ s.terms) := sameKeys_sound H.facts same
                have hp' : (d.params.length == as.length) = true := by rw [eas, ← ekeys, List.length_map]; simpa using hlen'
                refine ⟨.list (wordBytes (ids.map fun i => den (inpOf ctx s0) ρ s.terms i)), ?_, WDen.wbytes ids⟩
                simp only [evalSpec, el]; rw [if_neg hlen, if_neg hown]; simp only [hd]; rw [if_pos hp', eas, ← ekeys]
                exact evalSpec_mono ctx.defs B hev (fuel + B) (Nat.le_add_left _ _)
              | none =>
              simp only [hh2] at h
              cases hh3 : ((flatKeys look vs).bind fun keys => usedAs s.facts f keys s.known) with
              | some u =>
                -- a use the state has given a number: the definition gives, within `B` steps, what the unknown
                -- of that number stands for
                simp only [hh3, Option.some.injEq] at h; subst h
                obtain ⟨keys, hk, hi⟩ := Option.bind_eq_some_iff.mp hh3
                obtain ⟨keys', hm, same⟩ := usedAs_mem hi
                obtain ⟨d, hd, hlen', hev⟩ := hB _ hm
                have eas : as = keys.map (Key.val ctx s0 ρ s.terms) := flatKeys_den wf dl hk
                have ekeys : keys'.map (Key.val ctx s0 ρ s.terms) = keys.map (Key.val ctx s0 ρ s.terms) := sameKeys_sound H.facts same
                have hp' : (d.params.length == as.length) = true := by rw [eas, ← ekeys, List.length_map]; simpa using hlen'
                refine ⟨Val.decode (ρ u).toNat, ?_, WDen.use u⟩
                simp only [evalSpec, el]; rw [if_neg hlen, if_neg hown]; simp only [hd]; rw [if_pos hp', eas, ← ekeys]
                exact evalSpec_mono ctx.defs B hev (fuel + B) (Nat.le_add_left _ _)
              | none =>
              simp only [hh3] at h
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
      cases hl : wevalList (weval ctx look s fuel env) items with
      | none => simp [hl] at h
      | some vs =>
        simp only [hl, Option.map_some, Option.some.injEq] at h; subst h
        obtain ⟨as, el, dl⟩ := wevalList_sound (ev' := evalSpec ctx.defs (fuel + B) env') (fun e v hv => ih env env' e v hv hE) items vs hl
        refine ⟨.list as, ?_, dl⟩
        simp only [evalSpec, el, Option.map_some]
    | letx x e rest =>
      simp only [weval] at h
      cases he : weval ctx look s fuel env e with
      | none => simp [he] at h
      | some xv =>
        simp only [he] at h
        obtain ⟨xa, ex, dx⟩ := ih env env' e xv he hE
        obtain ⟨r, er, dr⟩ := ih ((x, xv) :: env) ((x, xa) :: env') rest v h ⟨rfl, dx, hE⟩
        refine ⟨r, ?_, dr⟩
        simp only [evalSpec, ex]; exact er
    | each e x a b =>
      simp only [weval] at h
      cases ha : weval ctx look s fuel env a <;> cases hb : weval ctx look s fuel env b <;>
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
          cases hl : wevalEach (fun i => weval ctx look s fuel ((x, .int i) :: env) e) (hi - lo).toNat lo with
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
      cases ha : weval ctx look s fuel env a <;> cases hp : wevalList (weval ctx look s fuel env) puts <;>
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
      cases ha : weval ctx look s fuel env a <;> cases hlo : weval ctx look s fuel env lo <;>
        cases hhi : weval ctx look s fuel env hi <;> simp only [ha, hlo, hhi, reduceCtorEq] at h
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
                have hb' : ∀ k, k < (j - i).toNat → (s0.mem (s0.reg r + i.toNat + k)).val < 256 := fun k hk => by
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
                have hb' : ∀ k, k < (j - i).toNat → (s0.mem (s0.reg r + (off + i.toNat) + k)).val < 256 := fun k hk => by
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
      | region r l =>
        cases lv with
        | int i =>
          cases hv with
          | int j =>
            cases dlo; cases dhi
            cases da with
            | region _ _ hl hb =>
              simp only at h
              split at h
              next hc =>
                simp only [Option.some.injEq] at h; subst h
                obtain ⟨i0, ij, jn⟩ := hc
                have hj := plain_sound jn ρ H.facts
                rw [ev_sub, ev_var, ev_const, hl] at hj
                have hb' : ∀ k, k < (j - i).toNat → (s0.mem (s0.reg r + i.toNat + k)).val < 256 := fun k hk => by
                  have := hb (i.toNat + k) (by omega)
                  rwa [← Nat.add_assoc] at this
                refine ⟨_, ?_, WDen.part r i.toNat (j - i).toNat hb'⟩
                simp only [evalSpec, ea, elo, ehi]
                rw [if_pos ⟨i0, ij, by simp only [List.length_map, List.length_range]; omega⟩,
                  slice_run s0.mem (s0.reg r) (s0.reg l) i.toNat (j - i).toNat (by omega)]
              next => simp at h
          | num jr =>
            cases dlo; cases dhi
            cases da with
            | region _ _ hl hb =>
              simp only at h
              split at h
              next hc =>
                simp only [Option.some.injEq] at h; subst h
                obtain ⟨i0, ij, jn⟩ := hc
                have hij := plain_sound ij ρ H.facts
                rw [ev_sub, ev_const] at hij
                have hj := plain_sound jn ρ H.facts
                rw [ev_sub, ev_var, hl] at hj
                have key := WDen.span (ctx := ctx) (ρ := ρ) (T := s.terms) (s0 := s0) r (Lin.const i) (Lin.sub jr (Lin.const i))
                  (by rw [ev_const]; exact i0) (by rw [ev_sub, ev_const]; omega)
                rw [ev_sub, ev_const] at key
                refine ⟨_, ?_, key⟩
                simp only [evalSpec, ea, elo, ehi]
                rw [if_pos ⟨i0, by omega, by simp only [List.length_map, List.length_range]; omega⟩,
                  slice_run s0.mem (s0.reg r) (s0.reg l) i.toNat (ev ρ jr - i).toNat (by omega)]
              next => simp at h
          | _ => simp at h
        | num ir =>
          cases hv with
          | num jr =>
            cases dlo; cases dhi
            cases da with
            | region _ _ hl hb =>
              simp only at h
              split at h
              next hc =>
                simp only [Option.some.injEq] at h; subst h
                obtain ⟨i0, ij, jn⟩ := hc
                have hi0 := plain_sound i0 ρ H.facts
                have hij := plain_sound ij ρ H.facts; rw [ev_sub] at hij
                have hjn := plain_sound jn ρ H.facts; rw [ev_sub, ev_var, hl] at hjn
                have key := WDen.span (ctx := ctx) (ρ := ρ) (T := s.terms) (s0 := s0) r ir (Lin.sub jr ir)
                  hi0 (by rw [ev_sub]; omega)
                rw [ev_sub] at key
                refine ⟨_, ?_, key⟩
                simp only [evalSpec, ea, elo, ehi]
                rw [if_pos ⟨hi0, by omega, by simp only [List.length_map, List.length_range]; omega⟩,
                  slice_run s0.mem (s0.reg r) (s0.reg l) (ev ρ ir).toNat (ev ρ jr - ev ρ ir).toNat (by omega)]
              next => simp at h
          | _ => simp at h
        | _ => cases hv <;> simp at h
      | span r off slen =>
        cases lv with
        | int i =>
          cases hv with
          | int j =>
            cases dlo; cases dhi
            cases da with
            | span _ _ _ hoff hslen =>
              simp only at h
              split at h
              next hc =>
                obtain ⟨i0, ij, jn⟩ := hc
                have hj := plain_sound jn ρ H.facts; rw [ev_sub, ev_const] at hj
                cases hco : Lin.isConst off with
                | some c =>
                  simp only [hco] at h
                  have ec := ev_isConst (ρ := ρ) hco
                  split at h
                  next hc0 =>
                    simp only [Option.some.injEq] at h; subst h
                    have eo : ∀ k, s0.reg r + (c.toNat + i.toNat) + k = s0.reg r + (ev ρ off).toNat + i.toNat + k := fun k => by omega
                    have key := WDen.part (ctx := ctx) (ρ := ρ) (T := s.terms) (s0 := s0) r (c.toNat + i.toNat) (j - i).toNat (fun k _ => (s0.mem _).isLt)
                    simp only [eo] at key
                    refine ⟨_, ?_, key⟩
                    simp only [evalSpec, ea, elo, ehi]
                    rw [if_pos ⟨i0, ij, by simp only [List.length_map, List.length_range]; omega⟩,
                      slice_run s0.mem (s0.reg r + (ev ρ off).toNat) (ev ρ slen).toNat i.toNat (j - i).toNat (by omega)]
                  next =>
                    simp only [Option.some.injEq] at h; subst h
                    have key := WDen.span (ctx := ctx) (ρ := ρ) (T := s.terms) (s0 := s0) r (Lin.add off (Lin.const i)) (Lin.const (j - i))
                      (by rw [ev_add, ev_const]; omega) (by rw [ev_const]; omega)
                    have eo : ∀ k, s0.reg r + (ev ρ (Lin.add off (Lin.const i))).toNat + k = s0.reg r + (ev ρ off).toNat + i.toNat + k := fun k => by rw [ev_add, ev_const]; omega
                    rw [ev_const] at key
                    simp only [eo] at key
                    refine ⟨_, ?_, key⟩
                    simp only [evalSpec, ea, elo, ehi]
                    rw [if_pos ⟨i0, ij, by simp only [List.length_map, List.length_range]; omega⟩,
                      slice_run s0.mem (s0.reg r + (ev ρ off).toNat) (ev ρ slen).toNat i.toNat (j - i).toNat (by omega)]
                | none =>
                  simp only [hco, Option.some.injEq] at h; subst h
                  have key := WDen.span (ctx := ctx) (ρ := ρ) (T := s.terms) (s0 := s0) r (Lin.add off (Lin.const i)) (Lin.const (j - i))
                    (by rw [ev_add, ev_const]; omega) (by rw [ev_const]; omega)
                  have eo : ∀ k, s0.reg r + (ev ρ (Lin.add off (Lin.const i))).toNat + k = s0.reg r + (ev ρ off).toNat + i.toNat + k := fun k => by rw [ev_add, ev_const]; omega
                  rw [ev_const] at key
                  simp only [eo] at key
                  refine ⟨_, ?_, key⟩
                  simp only [evalSpec, ea, elo, ehi]
                  rw [if_pos ⟨i0, ij, by simp only [List.length_map, List.length_range]; omega⟩,
                    slice_run s0.mem (s0.reg r + (ev ρ off).toNat) (ev ρ slen).toNat i.toNat (j - i).toNat (by omega)]
              next => simp at h
          | _ => simp at h
        | num ir =>
          cases hv with
          | num jr =>
            cases dlo; cases dhi
            cases da with
            | span _ _ _ hoff hslen =>
              simp only at h
              split at h
              next hc =>
                simp only [Option.some.injEq] at h; subst h
                obtain ⟨i0, ij, jn⟩ := hc
                have hi0 := plain_sound i0 ρ H.facts
                have hij := plain_sound ij ρ H.facts; rw [ev_sub] at hij
                have hjn := plain_sound jn ρ H.facts; rw [ev_sub] at hjn
                have key := WDen.span (ctx := ctx) (ρ := ρ) (T := s.terms) (s0 := s0) r (Lin.add off ir) (Lin.sub jr ir)
                  (by rw [ev_add]; omega) (by rw [ev_sub]; omega)
                have eo : ∀ k, s0.reg r + (ev ρ (Lin.add off ir)).toNat + k = s0.reg r + (ev ρ off).toNat + (ev ρ ir).toNat + k := fun k => by rw [ev_add]; omega
                rw [ev_sub] at key
                simp only [eo] at key
                refine ⟨_, ?_, key⟩
                simp only [evalSpec, ea, elo, ehi]
                rw [if_pos ⟨hi0, by omega, by simp only [List.length_map, List.length_range]; omega⟩,
                  slice_run s0.mem (s0.reg r + (ev ρ off).toNat) (ev ρ slen).toNat (ev ρ ir).toNat (ev ρ jr - ev ρ ir).toNat (by omega)]
              next => simp at h
          | _ => simp at h
        | _ => cases hv <;> simp at h
      | wbytes ids =>
        cases lv with
        | int i =>
          cases hv with
          | int j =>
            cases dlo; cases dhi
            cases da
            simp only at h
            split at h
            next hc =>
              simp only [Option.some.injEq] at h; subst h
              obtain ⟨i0, ij, im4, jm4, jle⟩ := hc
              have ei : i.toNat = 4 * (i.toNat / 4) := by omega
              have ed : (j - i).toNat = 4 * ((j - i).toNat / 4) := by omega
              refine ⟨_, ?_, WDen.wbytes ((ids.drop (i.toNat / 4)).take ((j - i).toNat / 4))⟩
              simp only [evalSpec, ea, elo, ehi]
              rw [if_pos ⟨i0, ij, by rw [wordBytes_length, List.length_map]; omega⟩]
              simp only [Option.some.injEq, Val.list.injEq]
              rw [List.map_take, List.map_drop, ← wordBytes_take, ← wordBytes_drop, ← ei, ← ed]
            next => simp at h
          | _ => simp at h
        | _ => cases hv <;> simp at h
      | _ => cases lv <;> cases hv <;> simp at h
    | record names items =>
      simp only [weval] at h
      cases hl : wevalList (weval ctx look s fuel env) items with
      | none => simp [hl] at h
      | some vs =>
        simp only [hl] at h
        obtain ⟨as, el, dl⟩ := wevalList_sound (ev' := evalSpec ctx.defs (fuel + B) env') (fun e v hv => ih env env' e v hv hE) items vs hl
        split at h
        next hn =>
          have hn' : (names.length == as.length) = true := by rw [← WDen.length dl]; exact hn
          have hzr : WDen ctx s0 ρ s.terms (.record (names.zip vs)) (.record (names.zip as)) := WDen.zipRecord dl
          cases hkr : knownRec s.facts s.tab.arr (names.zip vs) s.known with
          | some u =>
            simp only [hkr, Option.some.injEq] at h; subst h
            have hdec := knownRec_sound H wf hpv H.known hkr hzr
            refine ⟨.record (names.zip as), ?_, ?_⟩
            · simp only [evalSpec, el]; rw [if_pos hn']
            · rw [← hdec]; exact WDen.use u
          | none =>
            simp only [hkr, Option.some.injEq] at h; subst h
            refine ⟨.record (names.zip as), ?_, hzr⟩
            simp only [evalSpec, el]; rw [if_pos hn']
        next => simp at h
    | field e x =>
      simp only [weval] at h
      cases he : weval ctx look s fuel env e with
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
    | theNumber greatest x a b cond =>
      simp only [weval] at h
      cases ha : weval ctx look s fuel env a <;> cases hb : weval ctx look s fuel env b <;>
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
          obtain ⟨r, er, dr⟩ := wfirstWith_sound (ev' := fun n => evalSpec ctx.defs (fuel + B) ((x, .int n) :: env') cond)
            (fun i v hv => ih ((x, .int i) :: env) ((x, .int i) :: env') cond v hv ⟨rfl, WDen.int i, hE⟩) _ v h
          refine ⟨r, ?_, dr⟩
          simp only [evalSpec, ea, eb]
          exact er
        | _ => simp at h
      | _ => cases bv <;> simp at h
    | thePower greatest x cond =>
      simp only [weval] at h
      obtain ⟨r, er, dr⟩ := wfirstWith_sound (ev' := fun n => evalSpec ctx.defs (fuel + B) ((x, .int n) :: env') cond)
        (fun i v hv => ih ((x, .int i) :: env) ((x, .int i) :: env') cond v hv ⟨rfl, WDen.int i, hE⟩) _ v h
      refine ⟨r, ?_, dr⟩
      simp only [evalSpec]
      exact er
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

theorem regionsIn_tail (c : Contract) {y : Nat × Nat} (a : String × Kind) (r : Nat) {args : List (String × Kind)} {regs : List Nat}
    (m : y ∈ regionsIn c args regs) : y ∈ regionsIn c (a :: args) (r :: regs) := by
  obtain ⟨n, k⟩ := a
  cases k with
  | bytes len =>
    simp only [regionsIn]
    cases c.regOf len with
    | none => exact m
    | some l => exact List.mem_cons_of_mem _ m
  | number => simpa [regionsIn] using m
  | out _ => simpa [regionsIn] using m
  | fixed _ => simpa [regionsIn] using m
  | inout _ => simpa [regionsIn] using m
  | valArray _ _ _ => simpa [regionsIn] using m

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}
variable {look : Node → Option Nat} [Looks look s.terms]

local notation "𝔻" => den (inpOf ctx s0) ρ s.terms

/-- The names on words stand for the contract's names as the account has them at entry. -/
theorem wenvIn_sound (H : Holds ctx s0 ρ s st) {T : List Node} (c : Contract) (hc : c.regs ≤ ctx.nreg) :
    ∀ (args : List (String × Kind)) (regs : List Nat), (∀ r ∈ regs, r < ctx.nreg) →
      (∀ x r n, (x, r, n) ∈ fixedsIn args regs → ∀ k, k < n → (s0.mem (s0.reg r + k)).val < 256) →
      (∀ x r n, (x, r, n) ∈ inoutsIn args regs → ∀ k, k < n → (s0.mem (s0.reg r + k)).val < 256) →
      (∀ r l, (r, l) ∈ regionsIn c args regs → ∀ k, k < s0.reg l → (s0.mem (s0.reg r + k)).val < 256) →
      EnvDen ctx s0 ρ T (wenvIn c args regs) (envWIn c s0 args regs)
  | [], _, _, _, _, _ => by simp [wenvIn, envWIn, EnvDen]
  | _ :: _, [], _, _, _, _ => by simp [wenvIn, envWIn, EnvDen]
  | (n, kind) :: args, r :: regs, hreg, hf, hi, hrg => by
    have ih := wenvIn_sound H (T := T) c hc args regs (fun r' m => hreg r' (List.mem_cons_of_mem _ m))
      (fun x r' n' m => hf x r' n' (fixedsIn_tail (n, kind) r m)) (fun x r' n' m => hi x r' n' (inoutsIn_tail (n, kind) r m))
      (fun r' l' m => hrg r' l' (regionsIn_tail c (n, kind) r m))
    cases kind with
    | number =>
      simp only [wenvIn, envWIn]
      refine ⟨rfl, ?_, ih⟩
      have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := T) (Lin.var r)
      rw [ev_var, H.entry r (hreg r (List.mem_cons_self ..))] at this
      exact this
    | bytes len =>
      simp only [wenvIn, envWIn]
      cases hlen : c.regOf len with
      | none => exact ih
      | some l =>
        refine ⟨rfl, ?_, ih⟩
        simp only [Val.bytes, List.map_map]
        exact WDen.region r l (H.entry l (Nat.lt_of_lt_of_le (argRegs_lt (regOfIn_mem len c.args c.argRegs l hlen)) hc))
          (hrg r l (by simp [regionsIn, hlen]))
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
    | valArray _ _ _ =>
      simp only [wenvIn, envWIn]
      exact ih

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
    EnvDen ctx s0 ρ T (wenvIn ctx.contract ctx.contract.args ctx.contract.argRegs) (envWIn ctx.contract s0 ctx.contract.args ctx.contract.argRegs) :=
  wenvIn_sound H ctx.contract (Nat.le_refl _) ctx.contract.args ctx.contract.argRegs (fun _ m => argRegs_lt m)
    (fun _ _ _ m k hk => (E.fixed m).2.2.1 k hk) (fun _ _ _ m _ hk => E.inoutByte m hk) (fun _ _ m k hk => E.byte m k hk)

/-- The contract's names on words stand for its names in the account, a table's name first. -/
theorem wenv_sound {p : Program} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) {T : List Node} :
    EnvDen ctx s0 ρ T (wenv ctx.contract) (ctx.contract.envW s0) :=
  EnvDen.append (lanesW_den _) (wenvIn_all E H)

/-- The words the specification gives are the words known written: the bytes of the run are the bytes of
those words, four a word, the lowest first. -/
theorem written_words (H : Holds ctx s0 ρ s st) (wf : WF ctx s) {w : Nat} {x : String} {r n : Nat}
    (hw : ctx.contract.outs[w]? = some (x, r, n)) :
    ∀ (l : List WVal) (ws : List Val) (j : Nat), wordsWritten look s.wroteW w j l = true →
      WDen ctx s0 ρ s.terms (.list l) (.list ws) →
      ∃ bs : List Nat, ofWords ws = some (bs.map fun (b : Nat) => Val.int b) ∧ bs.length = 4 * l.length ∧
        ∀ k, k < bs.length → bs[k]? = some (st.mem (s0.reg r + 4 * j + k)).val
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
        cases hi : idOf look xs with
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
              rw [this]; congr 3; omega
      | _ => simp [wordsWritten] at hww

private theorem keyOk_wf {n t : Nat} {k : Key} (h : k.ok n t = true) : k.wf n t := by
  cases k with
  | num r => simpa [Key.ok, Key.wf, bounded] using h
  | counter r => simpa [Key.ok, Key.wf, bounded] using h
  | words ids => intro i hi; exact of_decide_eq_true (List.all_eq_true.mp h i hi)
  | lane _ _ _ => trivial
  | span _ off len =>
    simp only [Key.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, h.2⟩
  | use u => simpa [Key.ok, Key.wf] using h

private theorem value_call_inv {defs : List Def} {env : List (String × Val)} {f : String} {args : SExpr} {v : Val} {d : Def}
    (hv : Value defs env (.call f args) v) (hown : own.contains f = false) (hlen : (f == "len") = false)
    (hd : findDef defs f = some d) :
    ∃ vs, (∃ fuel, evalList (evalSpec defs fuel env) args = some vs) ∧ d.params.length = vs.length ∧
      Value defs (d.params.zip vs) d.body v := by
  obtain ⟨fuel, hf⟩ := hv
  cases fuel with
  | zero => simp [evalSpec] at hf
  | succ fuel =>
    simp only [evalSpec] at hf
    cases hl : evalList (evalSpec defs fuel env) args with
    | none => simp [hl] at hf
    | some vs =>
      simp only [hl, hlen, Bool.false_eq_true, ↓reduceIte, hown, hd] at hf
      split at hf
      next hlen_p =>
        exact ⟨vs, ⟨fuel, hl⟩, by simpa using hlen_p, ⟨fuel, hf⟩⟩
      next => simp at hf

private theorem envDen_wenv_carry {p : Program} (E : Setting ctx p s0) {s1 : Sym} {ρ1 : Nat → Int}
    (H1 : Holds ctx s0 ρ1 s1 st) {idx : String} {i : Int} :
    EnvDen ctx s0 ρ1 s1.terms ((idx, .int i) :: wenv ctx.contract) ((idx, .int i) :: ctx.contract.envW s0) :=
  ⟨rfl, WDen.int i, wenv_sound E H1⟩

private theorem fixedInputNodes_inputs : ∀ (fs : List (String × Nat × Nat)) (j : Nat) (nd : Node),
    nd ∈ fixedInputNodes fs j → ∃ a b, nd = Node.input a b
  | [], _, _, m => by simp [fixedInputNodes] at m
  | (_, _, n) :: more, j, nd, m => by
    simp only [fixedInputNodes, List.mem_append] at m
    rcases m with m1 | m2
    · split at m1
      · obtain ⟨k, _, rfl⟩ := List.mem_map.mp m1; exact ⟨j, k, rfl⟩
      · cases m1
    · exact fixedInputNodes_inputs more (j + 1) nd m2

private theorem findInputIds_sound {s1 : Sym} {ρ1 : Nat → Int} (wf1 : WF ctx s1)
    {j : Nat} {x : String} {r : Nat} (hwr : ctx.contract.wordRuns[j]? = some (x, r, 0)) :
    ∀ (count start : Nat) (ids : List Nat),
      findInputIds s1.tab.find j start count = some ids →
      ids.length = count ∧ (∀ id ∈ ids, id < s1.terms.length) ∧
      ids.map (fun id => Val.word (den (inpOf ctx s0) ρ1 s1.terms id)) =
        (List.range count).map (fun m => Val.word (load s0.mem (s0.reg r + 4 * (start + m)) 4))
  | 0, _, ids, h => by
    simp only [findInputIds, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun _ m => (nomatch m), rfl⟩
  | count + 1, start, ids, h => by
    simp only [findInputIds] at h
    cases hf : s1.tab.find (.input j start) with
    | none => simp [hf] at h
    | some id =>
      cases hr : findInputIds s1.tab.find j (start + 1) count with
      | none => simp [hf, hr] at h
      | some rest =>
        simp only [hf, hr, Option.some.injEq] at h; subst h
        obtain ⟨rlen, rlt, rmap⟩ := findInputIds_sound wf1 hwr count (start + 1) rest hr
        have hid_lt : id < s1.terms.length := (List.getElem?_eq_some_iff.mp (Looks.found hf)).1
        have hden : den (inpOf ctx s0) ρ1 s1.terms id = load s0.mem (s0.reg r + 4 * start) 4 := by
          have := found_den (ctx := ctx) (s0 := s0) (ρ := ρ1) (s := s1) wf1 hf
          simp only [Node.value, inpOf, hwr] at this
          exact this
        refine ⟨by simp [rlen], fun id' m => ?_, ?_⟩
        · rcases List.mem_cons.mp m with rfl | m
          · exact hid_lt
          · exact rlt id' m
        · rw [List.map_cons, hden, List.range_succ_eq_map, List.map_cons, List.map_map]
          congr 1
          rw [rmap]
          apply List.map_congr_left
          intro m _
          simp only [Function.comp_apply]
          congr 2; omega

mutual
private theorem registerValArg_sound {p : Program} (E : Setting ctx p s0)
    (hpv : ctx.contract.preVals ctx.defs s0) {idx : String} {i : Int} :
    ∀ (fuel : Nat) {s1 s2 : Sym} {ρ1 : Nat → Int} {e : SExpr} {k : Key} {v : Val},
      Holds ctx s0 ρ1 s1 st → WF ctx s1 →
      Value ctx.defs ((idx, .int i) :: ctx.contract.envW s0) e v →
      registerValArg ctx ((idx, .int i) :: wenv ctx.contract) fuel s1 e = some (k, s2) →
      ∃ ρ2, Carried ctx s0 ρ1 s1 ρ2 s2 st ∧ s2.terms = s1.terms ∧ s2.facts = s1.facts ∧
        k.wf s2.nvars s2.terms.length ∧ Key.val ctx s0 ρ2 s2.terms k = v
  | fuel, s1, s2, ρ1, e, k, v, H1, wf1, hv, hreg => by
    let envW := (idx, .int i) :: wenv ctx.contract
    let envV := (idx, .int i) :: ctx.contract.envW s0
    have hE1 : EnvDen ctx s0 ρ1 s1.terms envW envV := envDen_wenv_carry E H1
    have wev_branch :
        (match weval ctx s1.tab.find s1 WFUEL envW e with
         | some wv =>
           match flatKey s1.tab.find wv with
           | some k0 => if k0.ok s1.nvars s1.tab.size then some (k0, s1) else none
           | none => none
         | none => none) = some (k, s2) →
        ∃ ρ2, Carried ctx s0 ρ1 s1 ρ2 s2 st ∧ s2.terms = s1.terms ∧ s2.facts = s1.facts ∧
          k.wf s2.nvars s2.terms.length ∧ Key.val ctx s0 ρ2 s2.terms k = v := by
      intro hw
      cases hwv : weval ctx s1.tab.find s1 WFUEL envW e with
      | none => simp [hwv] at hw
      | some wv =>
        simp only [hwv] at hw
        cases hfk : flatKey s1.tab.find wv with
        | none => simp [hfk] at hw
        | some k0 =>
          simp only [hfk] at hw
          split at hw
          next hok =>
            injection hw with hw; injection hw with hk hs
            subst hk hs
            obtain ⟨B, hB⟩ := held_bound H1 hpv
            obtain ⟨a, ea, da⟩ := weval_sound H1 wf1 hpv hB WFUEL envW envV e wv hwv hE1
            have hav : a = v := Value.unique ⟨WFUEL + B, ea⟩ hv
            subst hav
            have hkv := (flatKey_den wf1 da hfk).symm
            have kwf : Key.wf s1.nvars s1.terms.length k0 := by
              rw [← Tab.size_eq_length]; exact keyOk_wf hok
            exact ⟨ρ1, Carried.here H1 wf1, rfl, rfl, kwf, hkv⟩
          next => cases hw
    cases fuel with
    | zero =>
      simp only [registerValArg] at hreg
      exact wev_branch hreg
    | succ fuel =>
      cases e with
      | call g gargs =>
        simp only [registerValArg] at hreg
        by_cases hb : (own.contains g || g == "len") = true
        · rw [if_pos hb] at hreg; exact wev_branch hreg
        · rw [if_neg hb] at hreg
          have hown : own.contains g = false := by cases h1 : own.contains g <;> simp_all
          have hlen : (g == "len") = false := by cases h1 : (g == "len") <;> simp_all
          cases hd : findDef ctx.defs g with
          | none => simp [hd] at hreg
          | some d =>
            simp only [hd] at hreg
            cases ha : registerValArgs ctx ((idx, .int i) :: wenv ctx.contract) fuel s1 gargs with
            | none => simp [ha] at hreg
            | some res =>
              obtain ⟨gkeys, sm⟩ := res
              simp only [ha] at hreg
              split at hreg
              next hok =>
                simp only [Bool.and_eq_true, beq_iff_eq] at hok
                obtain ⟨hplen, hgok⟩ := hok
                obtain ⟨gvs, hgvs, _, hbody⟩ := value_call_inv hv hown hlen hd
                obtain ⟨ρm, cm, htm, hfm, hkwf, hkv⟩ := registerValArgs_sound E hpv fuel H1 wf1 hgvs ha
                cases hu : usedAs sm.facts g gkeys sm.known with
                | some h =>
                  simp only [hu, Option.some.injEq, Prod.mk.injEq] at hreg
                  obtain ⟨rfl, rfl⟩ := hreg
                  obtain ⟨keys', hm_use, hsame⟩ := usedAs_mem hu
                  have hkw : Known.wf sm.nvars sm.terms.length (.use g keys' h) := cm.wf.known _ hm_use
                  obtain ⟨d', hd', _, hval'⟩ := cm.holds.known _ hm_use hpv
                  rw [hd] at hd'; injection hd' with hd'; subst hd'
                  have heq_keys : keys'.map (Key.val ctx s0 ρm sm.terms) = gkeys.map (Key.val ctx s0 ρm sm.terms) :=
                    sameKeys_sound cm.holds.facts hsame
                  rw [heq_keys, hkv] at hval'
                  have hv_eq : Val.decode (ρm h).toNat = v := Value.unique hval' hbody
                  exact ⟨ρm, cm, htm, hfm, hkw.2, hv_eq⟩
                | none =>
                  simp only [hu, Option.some.injEq, Prod.mk.injEq] at hreg
                  obtain ⟨rfl, rfl⟩ := hreg
                  let ρ2 : Nat → Int := fun r => if r = sm.nvars then (v.code : Int) else ρm r
                  have ag2 : Agree sm.nvars ρm ρ2 := fun r hr => by simp [ρ2, Nat.ne_of_lt hr]
                  have hH2 := cm.holds.agree cm.wf ag2
                  have hdec : Val.decode (ρ2 sm.nvars).toNat = v := by simp [ρ2, Val.decode_code]
                  have hkwf_m : ∀ k' ∈ gkeys, k'.wf sm.nvars sm.terms.length := fun k' mk' => by
                    rw [← Tab.size_eq_length]; exact keyOk_wf (List.all_eq_true.mp hgok k' mk')
                  have hmap_eq : gkeys.map (Key.val ctx s0 ρ2 sm.terms) = gkeys.map (Key.val ctx s0 ρm sm.terms) :=
                    List.map_congr_left fun k' mk' => Key.val_mono (ctx := ctx) (s0 := s0) (hkwf_m k' mk') ag2 cm.wf.words.table cm.wf.words.atoms (Ext.refl _)
                  have huse_holds : Known.holds ctx s0 ρ2 sm.terms (.use g gkeys sm.nvars) := by
                    intro _; exact ⟨d, hd, hplen, by rw [hmap_eq, hkv, hdec]; exact hbody⟩
                  have hkn_final : ∀ k' ∈ (.use g gkeys sm.nvars :: sm.known), k'.holds ctx s0 ρ2 sm.terms := by
                    intro k' mk'
                    rcases List.mem_cons.mp mk' with rfl | mk'
                    · exact huse_holds
                    · exact hH2.known k' mk'
                  have hH_final : Holds ctx s0 ρ2 { sm with nvars := sm.nvars + 1, known := .use g gkeys sm.nvars :: sm.known } st :=
                    { hH2 with known := hkn_final }
                  have hwf_final : WF ctx { sm with nvars := sm.nvars + 1, known := .use g gkeys sm.nvars :: sm.known } := by
                    have hle : sm.nvars ≤ sm.nvars + 1 := Nat.le_succ _
                    exact ⟨Nat.le_trans cm.wf.base hle,
                      fun r hr => bounded_mono hle (cm.wf.reg r hr),
                      Flag.bounded_mono hle cm.wf.zf, Flag.bounded_mono hle cm.wf.cf,
                      fun o w m => bounded_mono hle (cm.wf.frame o w m), cm.wf.frameW,
                      fun f m => bounded_mono hle (cm.wf.facts f m),
                      fun u r o m => ⟨Nat.lt_of_lt_of_le (cm.wf.bytes u r o m).1 hle, bounded_mono hle (cm.wf.bytes u r o m).2⟩,
                      fun f m => SFact.bounded_mono hle (cm.wf.spec f m),
                      fun w o x m => ⟨bounded_mono hle (cm.wf.wrote w o x m).1, bounded_mono hle (cm.wf.wrote w o x m).2⟩,
                      ⟨cm.wf.words.table, fun j r hj => bounded_mono hle (cm.wf.words.atoms j r hj),
                       cm.wf.words.vec, cm.wf.words.rotrs, cm.wf.words.wrote,
                       fun o ids m => ⟨bounded_mono hle (cm.wf.words.spill o ids m).1, (cm.wf.words.spill o ids m).2⟩⟩,
                      fun k' mk' => by
                        rcases List.mem_cons.mp mk' with rfl | mk'
                        · exact ⟨fun x mx => Key.wf_mono hle (Nat.le_refl _) (hkwf_m x mx), Nat.lt_succ_self _⟩
                        · exact Known.wf_mono hle (Nat.le_refl _) (cm.wf.known k' mk'),
                      fun rg hrg => ⟨bounded_mono hle (cm.wf.range rg hrg).1, fun x mx => SVal.bounded_mono hle ((cm.wf.range rg hrg).2 x mx)⟩⟩
                  have hC2 : Carried ctx s0 ρ1 s1 ρ2 { sm with nvars := sm.nvars + 1, known := .use g gkeys sm.nvars :: sm.known } st :=
                    ⟨fun r hr => (cm.agree r hr).trans (ag2 r (Nat.lt_of_lt_of_le hr cm.mono)),
                     Nat.le_trans cm.mono (Nat.le_succ _), hH_final, hwf_final⟩
                  exact ⟨ρ2, hC2, htm, hfm, Nat.lt_succ_self _, hdec⟩
              next => cases hreg
      | num _ | name _ | bin _ _ _ | ifx _ _ _ | index _ _ | list _ | nil | cons _ _ | letx _ _ _
      | each _ _ _ _ | slice _ _ _ | withx _ _ | record _ _ | field _ _ | theNumber _ _ _ _ _ | thePower _ _ _ =>
        simp only [registerValArg] at hreg
        exact wev_branch hreg

private theorem registerValArgs_sound {p : Program} (E : Setting ctx p s0)
    (hpv : ctx.contract.preVals ctx.defs s0) {idx : String} {i : Int} :
    ∀ (fuel : Nat) {s1 s2 : Sym} {ρ1 : Nat → Int} {args : SExpr} {ks : List Key} {vs : List Val},
      Holds ctx s0 ρ1 s1 st → WF ctx s1 →
      (∃ fl, evalList (evalSpec ctx.defs fl ((idx, .int i) :: ctx.contract.envW s0)) args = some vs) →
      registerValArgs ctx ((idx, .int i) :: wenv ctx.contract) fuel s1 args = some (ks, s2) →
      ∃ ρ2, Carried ctx s0 ρ1 s1 ρ2 s2 st ∧ s2.terms = s1.terms ∧ s2.facts = s1.facts ∧
        (∀ k ∈ ks, k.wf s2.nvars s2.terms.length) ∧ ks.map (Key.val ctx s0 ρ2 s2.terms) = vs
  | fuel, s1, s2, ρ1, args, ks, vs, H1, wf1, hvs, hreg => by
    cases args with
    | nil =>
      simp only [registerValArgs, Option.some.injEq, Prod.mk.injEq] at hreg
      obtain ⟨rfl, rfl⟩ := hreg
      obtain ⟨fl, hfl⟩ := hvs
      simp only [evalList, Option.some.injEq] at hfl; subst hfl
      exact ⟨ρ1, Carried.here H1 wf1, rfl, rfl, fun _ m => (nomatch m), rfl⟩
    | cons a rest =>
      simp only [registerValArgs] at hreg
      obtain ⟨fl, hfl⟩ := hvs
      simp only [evalList] at hfl
      cases ha : evalSpec ctx.defs fl ((idx, .int i) :: ctx.contract.envW s0) a with
      | none => simp [ha] at hfl
      | some va =>
        cases hr : evalList (evalSpec ctx.defs fl ((idx, .int i) :: ctx.contract.envW s0)) rest with
        | none => simp [ha, hr] at hfl
        | some vrest =>
          simp only [ha, hr, Option.some.injEq] at hfl; subst hfl
          cases h1 : registerValArg ctx ((idx, .int i) :: wenv ctx.contract) fuel s1 a with
          | none => simp [h1] at hreg
          | some r1 =>
            obtain ⟨k, sm⟩ := r1
            simp only [h1] at hreg
            cases h2 : registerValArgs ctx ((idx, .int i) :: wenv ctx.contract) fuel sm rest with
            | none => simp [h2] at hreg
            | some r2 =>
              obtain ⟨krest, s2'⟩ := r2
              simp only [h2, Option.some.injEq, Prod.mk.injEq] at hreg
              obtain ⟨rfl, rfl⟩ := hreg
              obtain ⟨ρm, cm, htm, hfm, hkwf, hkv⟩ := registerValArg_sound E hpv fuel H1 wf1 ⟨fl, ha⟩ h1
              obtain ⟨ρ2, c2, ht2, hf2, hkwf2, hkv2⟩ := registerValArgs_sound E hpv fuel cm.holds cm.wf ⟨fl, hr⟩ h2
              have hkv' : Key.val ctx s0 ρ2 s2'.terms k = va := by
                have hext : Ext sm.terms s2'.terms := by rw [ht2]; exact Ext.refl _
                have := Key.val_mono (ctx := ctx) (s0 := s0) hkwf c2.agree cm.wf.words.table cm.wf.words.atoms hext
                exact this.trans hkv
              refine ⟨ρ2, cm.then c2, ht2.trans htm, hf2.trans hfm, ?_, ?_⟩
              · intro x mx
                rcases List.mem_cons.mp mx with rfl | mx
                · rw [ht2]; exact Key.wf_mono c2.mono (Nat.le_refl _) hkwf
                · exact hkwf2 x mx
              · simp [hkv', hkv2]
    | num _ | name _ | bin _ _ _ | ifx _ _ _ | index _ _ | call _ _ | list _ | letx _ _ _
    | each _ _ _ _ | slice _ _ _ | withx _ _ | record _ _ | field _ _ | theNumber _ _ _ _ _ | thePower _ _ _ =>
      simp [registerValArgs] at hreg
end

private theorem registerValEntry_sound {p : Program} (E : Setting ctx p s0)
    (hpv : ctx.contract.preVals ctx.defs s0) {idx : String} {i : Int} {s1 s2 : Sym} {ρ1 : Nat → Int}
    {ids : List Nat} {expr : SExpr}
    (H1 : Holds ctx s0 ρ1 s1 st) (wf1 : WF ctx s1)
    (hval : Value ctx.defs ((idx, .int i) :: ctx.contract.envW s0) expr
      (.list (ids.map fun id => Val.word (den (inpOf ctx s0) ρ1 s1.terms id))))
    (hreg : registerValEntry ctx s1 ((idx, .int i) :: wenv ctx.contract) ids expr = some s2) :
    ∃ ρ2, Carried ctx s0 ρ1 s1 ρ2 s2 st ∧ s2.terms = s1.terms ∧ s2.facts = s1.facts := by
  cases expr with
  | call f args =>
    simp only [registerValEntry] at hreg
    by_cases hb : (own.contains f || f == "len") = true
    · rw [if_pos hb] at hreg; cases hreg
    · rw [if_neg hb] at hreg
      have hown : own.contains f = false := by cases h1 : own.contains f <;> simp_all
      have hlen : (f == "len") = false := by cases h1 : (f == "len") <;> simp_all
      cases hd : findDef ctx.defs f with
      | none => simp [hd] at hreg
      | some d =>
        simp only [hd] at hreg
        cases ha : registerValArgs ctx ((idx, .int i) :: wenv ctx.contract) 4 s1 args with
        | none => simp [ha] at hreg
        | some res =>
          obtain ⟨keys, sm⟩ := res
          simp only [ha] at hreg
          split at hreg
          next hok =>
            simp only [Option.some.injEq] at hreg; subst hreg
            simp only [Bool.and_eq_true, beq_iff_eq] at hok
            obtain ⟨⟨hplen, hkok⟩, hids_ok⟩ := hok
            obtain ⟨vs, hvs, _, hbody⟩ := value_call_inv hval hown hlen hd
            obtain ⟨ρm, cm, htm, hfm, hkwf, hkv⟩ := registerValArgs_sound E hpv 4 H1 wf1 hvs ha
            have hids_lt : ∀ id ∈ ids, id < sm.terms.length := fun id mid => by
              rw [← Tab.size_eq_length]; exact of_decide_eq_true (List.all_eq_true.mp hids_ok id mid)
            have hden_eq : (ids.map fun id => Val.word (den (inpOf ctx s0) ρm sm.terms id)) =
                (ids.map fun id => Val.word (den (inpOf ctx s0) ρ1 s1.terms id)) :=
              List.map_congr_left fun id mid => by
                have hext : Ext s1.terms sm.terms := by rw [htm]; exact Ext.refl _
                have := den_mono (inp := inpOf ctx s0) wf1.words.table wf1.words.atoms cm.agree hext (by rw [← htm]; exact hids_lt id mid)
                rw [this]
            have hheld : Known.holds ctx s0 ρm sm.terms (.held f keys ids) := by
              intro _; refine ⟨d, hd, hplen, ?_⟩; rw [hkv, hden_eq]; exact hbody
            have hkn_final : ∀ k' ∈ (.held f keys ids :: sm.known), k'.holds ctx s0 ρm sm.terms := by
              intro k' mk'
              rcases List.mem_cons.mp mk' with rfl | mk'
              · exact hheld
              · exact cm.holds.known k' mk'
            have hwf_kn : ∀ k' ∈ (.held f keys ids :: sm.known), k'.wf sm.nvars sm.terms.length := by
              intro k' mk'
              rcases List.mem_cons.mp mk' with rfl | mk'
              · exact ⟨hkwf, hids_lt⟩
              · exact cm.wf.known k' mk'
            have hH_final : Holds ctx s0 ρm { sm with known := .held f keys ids :: sm.known } st :=
              { cm.holds with known := hkn_final }
            have hwf_final : WF ctx { sm with known := .held f keys ids :: sm.known } :=
              ⟨cm.wf.base, cm.wf.reg, cm.wf.zf, cm.wf.cf, cm.wf.frame, cm.wf.frameW,
               cm.wf.facts, cm.wf.bytes, cm.wf.spec, cm.wf.wrote,
               ⟨cm.wf.words.table, cm.wf.words.atoms, cm.wf.words.vec, cm.wf.words.rotrs, cm.wf.words.wrote, cm.wf.words.spill⟩,
               hwf_kn, cm.wf.range⟩
            exact ⟨ρm, ⟨cm.agree, cm.mono, hH_final, hwf_final⟩, htm, hfm⟩
          next => cases hreg
  | num _ | name _ | bin _ _ _ | ifx _ _ _ | index _ _ | list _ | nil | cons _ _ | letx _ _ _
  | each _ _ _ _ | slice _ _ _ | withx _ _ | record _ _ | field _ _ | theNumber _ _ _ _ _ | thePower _ _ _ =>
    simp [registerValEntry] at hreg

private theorem attachValArrays_sound {p : Program} (E : Setting ctx p s0)
    (hpv : ctx.contract.preVals ctx.defs s0) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) :
    ∃ ρ', Carried ctx s0 ρ s ρ' (attachValArrays ctx s) st := by
  unfold attachValArrays
  split
  · exact ⟨ρ, Carried.here H wf⟩
  · obtain ⟨eT, okT, _, _, _⟩ := termsOf_step (mk := intern) (val := fun nd => nd.value (inpOf ctx s0) ρ (den (inpOf ctx s0) ρ s.terms))
      (inp := inpOf ctx s0) (ρ := ρ) (nv := s.nvars) (T0 := s.terms)
      (fixedInputNodes ctx.contract.fixeds 0) s.tab
      (fun nd m T _ okT => by
        obtain ⟨a, b, rfl⟩ := fixedInputNodes_inputs _ 0 nd m
        exact input_step okT)
      (Ext.refl _) wf.words.ok
    have C0 : Carried ctx s0 ρ s ρ { s with tab := (termsOf intern (fixedInputNodes ctx.contract.fixeds 0) s.tab).2 } st :=
      Carried.terms H wf eT okT
    let baseJ := ctx.contract.fixeds.length + ctx.contract.inouts.length + ctx.contract.regions.length
    have fold_vas : ∀ (l : List ((String × Nat × Nat × Nat × Nat) × Nat)) (acc : Sym) (ρa : Nat → Int),
        (∀ item ∈ l, ctx.contract.valArrays[item.2]? = some item.1) →
        Carried ctx s0 ρ s ρa acc st →
        ∃ ρb, Carried ctx s0 ρ s ρb (l.foldl (fun acc ((x, _, l, ch, el), k) =>
          match ctx.contract.valSpecOf x with
          | none => acc
          | some (idx, expr) =>
            let j := baseJ + k
            let nw := el / 4
            if nw == 0 || ch == 0 then acc
            else
              let idxs := (acc.tab.list.filterMap fun nd =>
                match nd with
                | .input j' m => if j' == j then some (m / nw) else none
                | _ => none).eraseDups
              idxs.foldl (fun st (i : Nat) =>
                if plain st.facts (Lin.sub (Lin.var l) (Lin.const ((i + 1) * ch))) then
                  match findInputIds st.tab.find j (i * nw) nw with
                  | some ids => (registerValEntry ctx st ((idx, .int (i : Int)) :: wenv ctx.contract) ids expr).getD st
                  | none => st
                else st) acc) acc) st := by
      intro l
      induction l with
      | nil => intro acc ρa _ ca; exact ⟨ρa, ca⟩
      | cons hd tl ih =>
        intro acc ρa hmem ca
        obtain ⟨⟨x, r, lenR, ch, el⟩, k⟩ := hd
        have hk : ctx.contract.valArrays[k]? = some (x, r, lenR, ch, el) := hmem _ (List.mem_cons_self ..)
        simp only [List.foldl_cons]
        cases hvs : ctx.contract.valSpecOf x with
        | none => exact ih acc ρa (fun it mit => hmem it (List.mem_cons_of_mem _ mit)) ca
        | some spec =>
          obtain ⟨idx, expr⟩ := spec
          simp only
          split
          · exact ih acc ρa (fun it mit => hmem it (List.mem_cons_of_mem _ mit)) ca
          next hnz =>
            have hnw0 : el / 4 ≠ 0 := by intro h0; simp [h0] at hnz
            have hch0 : ch ≠ 0 := by intro h0; simp [h0] at hnz
            have hm_va := List.mem_of_getElem? hk
            obtain ⟨_, hl_lt, hch_pos, hel_pos, hel4⟩ := valArrays_lt hm_va
            have hwr := wordRuns_of_valArray hk
            have fold_idxs : ∀ (is : List Nat) (st0 : Sym) (ρ0 : Nat → Int),
                Carried ctx s0 ρ s ρ0 st0 st →
                ∃ ρ1, Carried ctx s0 ρ s ρ1 (is.foldl (fun st0 (i : Nat) =>
                  if plain st0.facts (Lin.sub (Lin.var lenR) (Lin.const ((i + 1) * ch))) then
                    match findInputIds st0.tab.find (baseJ + k) (i * (el / 4)) (el / 4) with
                    | some ids => (registerValEntry ctx st0 ((idx, .int (i : Int)) :: wenv ctx.contract) ids expr).getD st0
                    | none => st0
                  else st0) st0) st := by
              intro is
              induction is with
              | nil => intro st0 ρ0 c0; exact ⟨ρ0, c0⟩
              | cons i more ihi =>
                intro st0 ρ0 c0
                simp only [List.foldl_cons]
                by_cases hp : plain st0.facts (Lin.sub (Lin.var lenR) (Lin.const ((i + 1) * ch))) = true
                · rw [if_pos hp]
                  cases hf : findInputIds st0.tab.find (baseJ + k) (i * (el / 4)) (el / 4) with
                  | none => exact ihi st0 ρ0 c0
                  | some ids =>
                    simp only
                    cases hre : registerValEntry ctx st0 ((idx, .int (i : Int)) :: wenv ctx.contract) ids expr with
                    | none => exact ihi st0 ρ0 c0
                    | some st1 =>
                      simp only [Option.getD_some]
                      have hpl := plain_sound hp ρ0 c0.holds.facts
                      rw [ev_sub, ev_var, ev_const, c0.holds.entry lenR hl_lt] at hpl
                      have hi_lt : i < s0.reg lenR / ch := by
                        have h0 : (((i + 1) * ch : Nat) : Int) = (↑i + 1) * ↑ch := by rw [Int.natCast_mul, Int.natCast_add]; rfl
                        have h1 : (i + 1) * ch ≤ s0.reg lenR := by omega
                        have h2 := (Nat.le_div_iff_mul_le hch_pos).mpr h1
                        omega
                      have hval0 := hpv x r lenR ch el hm_va idx expr hvs i hi_lt
                      obtain ⟨_, _, hmap⟩ := findInputIds_sound c0.wf hwr (el / 4) (i * (el / 4)) ids hf
                      have hmap2 : ids.map (fun id => Val.word (den (inpOf ctx s0) ρ0 st0.terms id)) =
                          (List.range (el / 4)).map (fun m => Val.word (load s0.mem (s0.reg r + el * i + 4 * m) 4)) := by
                        rw [hmap]
                        apply List.map_congr_left
                        intro m _
                        congr 2
                        have h4e : 4 * (el / 4) = el := by omega
                        have h4m : 4 * (i * (el / 4) + m) = el * i + 4 * m := by
                          rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 4 i, Nat.mul_assoc, h4e, Nat.mul_comm i el]
                        omega
                      rw [← hmap2] at hval0
                      obtain ⟨ρ1, c1, _, _⟩ := registerValEntry_sound E hpv c0.holds c0.wf hval0 hre
                      exact ihi st1 ρ1 (c0.then c1)
                · rw [if_neg hp]; exact ihi st0 ρ0 c0
            obtain ⟨ρ1, c1⟩ := fold_idxs _ acc ρa ca
            exact ih _ ρ1 (fun it mit => hmem it (List.mem_cons_of_mem _ mit)) c1
    exact fold_vas ctx.contract.valArrays.zipIdx _ ρ (fun it mit => List.mem_zipIdx_iff_getElem?.mp mit) C0

/-- An `ensures` of a whole run of words that the verifier has passed holds: the run's bytes at the return
are the bytes of the words the specification gives of the names at entry. -/
theorem symEnsureW_sound {p : Program} (E : Setting ctx p s0) (hpv : ctx.contract.preVals ctx.defs s0)
    {e : EnsureW} {items : Items} {r : Unit × Items} {st' : State}
    (h : symEnsureW ctx s e items = .ok r) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hmem : st'.mem = st.mem) :
    e.holds ctx.contract ctx.defs s0 st' := by
  unfold symEnsureW at h
  obtain ⟨ρa, ca⟩ := attachValArrays_sound E hpv H wf
  generalize hsa : attachValArrays ctx s = sa at h ca
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
            obtain ⟨rr, _, hw⟩ := findOutNamed_spec hfo
            have hw' : ctx.contract.outs[w]? = some (e.run, rr, n) := by simpa using hw
            cases hwv : weval ctx sa.tab.find sa WFUEL (wenv ctx.contract) x with
            | none => simp only [hwv] at h; exact (refuse_ok h).elim
            | some v =>
              cases v with
              | list l =>
                simp only [hwv] at h
                split at h
                next hc =>
                  obtain ⟨hal, hlen, hin, hww⟩ := hc
                  obtain ⟨B, hB⟩ := held_bound ca.holds hpv
                  obtain ⟨a, ea, da⟩ := weval_sound ca.holds ca.wf hpv hB WFUEL _ _ x _ hwv (wenv_sound E ca.holds)
                  obtain ⟨ws, rfl⟩ := WDen.list_inv da
                  obtain ⟨bs, eo, blen, hm⟩ := written_words ca.holds ca.wf hw' l ws (e.first / 4) hww da
                  refine ⟨rr, n, bs, List.mem_of_getElem? hw', ⟨WFUEL + B + 1, ?_⟩, by omega, hin, ?_⟩
                  · rw [hv]
                    simp only [evalSpec, evalList, ea]
                    simp [own, builtin, eo, Val.bytes]
                  · intro k hk
                    have hk' := hm k hk
                    have e4 : 4 * (e.first / 4) = e.first := by omega
                    rw [e4] at hk'
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
