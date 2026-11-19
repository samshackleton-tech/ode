import SoundVec
/-!
# Soundness of 512-bit vector effects

The verifier records term numbers for the lanes it knows. Reading a 512-bit register requires all
sixteen lanes; writing a 128-bit register does not preserve facts about its upper lanes.
-/
namespace Ode
open Arithmetic

theorem symVec512_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} {bind : Bind} {e : Expr} {l : List Nat}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (h : symVec512 bind s e = some l) :
    l.length = 16 ∧ (∀ i ∈ l, i < s.terms.length) ∧
      vecArg512 bind st e = some (l.map (den (inpOf ctx s0) ρ s.terms)) := by
  cases e with
  | name n =>
    simp only [symVec512] at h
    cases hr : vecOf512 bind n with
    | none => simp [hr] at h
    | some r =>
      cases hl : s.vec.lookup r with
      | none => simp [hr, hl] at h
      | some ids =>
        simp only [hr, hl, Option.bind_some, Option.filter_some] at h
        split at h
        next le =>
          injection h with he; subst l
          have len : ids.length = 16 := by simpa using le
          refine ⟨len, (wf.words.vec r ids hl).2, ?_⟩
          simp only [vecArg512, hr, Option.map_some, Option.some.injEq]
          apply List.ext_getElem
          · simp [len]
          · intro k h1 h2
            simp only [List.getElem_map, List.getElem_range]
            have hk : k < ids.length := by simpa only [List.length_map] using h2
            simpa only [List.getD, List.getElem?_eq_getElem hk, Option.getD_some] using H.words.vec r ids hl k hk
        next => cases h
  | number _ => simp [symVec512] at h
  | lane _ _ => simp [symVec512] at h
  | call _ _ => simp [symVec512] at h

/-- The term numbers stand for all sixteen machine lanes. -/
def WideValue (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (s : Sym) (l lanes : List Nat) : Prop :=
  l.length = 16 ∧ (∀ i ∈ l, i < s.terms.length) ∧ lanes = l.map (den (inpOf ctx s0) ρ s.terms)

theorem wideReplicate {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {r : Row}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (hb : bounded s.nvars r) :
    let made := wAtom r s.terms
    let s' := { s with terms := made.2 }
    Carried ctx s0 ρ s ρ s' st ∧ WideValue ctx s0 ρ s' (List.replicate 16 made.1) (List.replicate 16 (ev ρ r % W32i).toNat) := by
  have h := wAtom_step (inp := inpOf ctx s0) (ρ := ρ) wf.words.ok hb
  exact ⟨Carried.terms H wf h.ext h.ok, by simp [WideValue, h.lt, h.den]⟩

theorem symSpreadScalar16_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind)
    {s s' : Sym} {a : Expr} {items rest : Items} {ρ : Nat → Int} {st : State} {l : List Nat}
    (h : symSpreadScalar16 ctx bind s a items = .ok ((l, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) :
    ∃ ρ' x, Carried ctx s0 ρ s ρ' s' st ∧ value (ctx.contract.perm s0) bind st a = some x ∧
      WideValue ctx s0 ρ' s' l (List.replicate 16 (x % W32)) := by
  unfold symSpreadScalar16 at h
  obtain ⟨⟨v, s1⟩, r1, h1, h⟩ := V.bind_ok h
  obtain ⟨ρ1, x, c, hx, sem⟩ := symValue_sound E bind a h1 H wf
  cases v with
  | lin r =>
    obtain ⟨rfl, rfl⟩ := pure_pair h
    obtain ⟨c', val⟩ := wideReplicate c.holds c.wf sem.2.2
    have eq : (ev ρ1 r % W32i).toNat = x % W32 := by
      rw [← sem.2.1]
      change ((x : Int) % (W32 : Int)).toNat = x % W32
      rw [← Int.natCast_emod]
      rfl
    exact ⟨ρ1, x, c.then c', hx, eq ▸ val⟩
  | equal _ _ => exact (refuse_ok h).elim
  | below _ _ => exact (refuse_ok h).elim

theorem symSpread16_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind)
    {s s' : Sym} {a : Expr} {items rest : Items} {ρ : Nat → Int} {st : State} {l : List Nat}
    (h : symSpread16 ctx bind s a items = .ok ((l, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) :
    ∃ ρ' x, Carried ctx s0 ρ s ρ' s' st ∧ value (ctx.contract.perm s0) bind st a = some x ∧
      WideValue ctx s0 ρ' s' l (List.replicate 16 (x % W32)) := by
  cases a with
  | number _ | name _ | lane _ _ => exact symSpreadScalar16_sound E bind h H wf
  | call f args =>
    simp only [symSpread16] at h
    split at h
    next hf =>
      simp only [beq_iff_eq] at hf; subst f
      obtain ⟨⟨ids, s1⟩, r1, h1, h⟩ := V.bind_ok h
      obtain ⟨vs, vv, al, c, len, lt, dn⟩ := symMemWords_sound E H wf (by decide) h1
      obtain ⟨rfl, rfl⟩ := pure_pair h
      let b := sumList vs % M64
      have hword : Ode.load st.mem b 4 < W32 := load_lt _ _ _
      have h0 : 0 < ids.length := by omega
      have i0 := lt (ids.getD 0 0) (by rw [getD_index h0]; exact List.getElem_mem h0)
      have eq0 := dn 0 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero] at eq0
      refine ⟨ρ, Ode.load st.mem b 4, c, ?_, ?_⟩
      · simp [value, vv, memSize, b, al]
      · rw [Nat.mod_eq_of_lt hword]
        refine ⟨List.length_replicate, fun i m => ?_, ?_⟩
        · rw [(List.mem_replicate.mp m).2]; exact i0
        · have h0 := eq0
          change Ode.load st.mem b 4 = _ at h0
          rw [List.map_replicate, h0]
    next =>
      split at h
      next hl =>
        -- the low half of a number, as a word, is the number as a word
        simp only [beq_iff_eq] at hl; subst f
        match args, h with
        | [b], h =>
          obtain ⟨ρ', y, c, hy, val⟩ := symSpreadScalar16_sound E bind h H wf
          refine ⟨ρ', y % 2 ^ 32, c, by simp [value, values, hy, memSize, prim], ?_⟩
          have e : y % 2 ^ 32 % W32 = y % W32 := by unfold W32; exact Nat.mod_mod _ _
          rw [e]; exact val
        | [], h => exact (refuse_ok h).elim
        | _ :: _ :: _, h => exact (refuse_ok h).elim
      next => exact symSpreadScalar16_sound E bind h H wf

/-- Lane-wise arithmetic uses the existing word terms and their soundness lemmas. -/
theorem symLaneTerms_sound {α : Type} {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s s' : Sym} {l : List Nat}
    {mk : α → List Node → Nat × List Node} {xs : List α} {val : α → Nat} {items rest : Items}
    (h : symLaneTerms s mk xs items = .ok ((l, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (xlen : xs.length = 16)
    (step : ∀ a ∈ xs, ∀ T, Ext s.terms T → TableOk s.nvars T → Step (inpOf ctx s0) ρ s.nvars T (mk a T).2 (mk a T).1 (val a)) :
    Carried ctx s0 ρ s ρ s' st ∧ WideValue ctx s0 ρ s' l (xs.map val) := by
  unfold symLaneTerms at h
  obtain ⟨rfl, rfl⟩ := pure_pair h
  obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step xs s.terms step (Ext.refl _) wf.words.ok
  refine ⟨Carried.terms H wf e ok, len.trans xlen, lt, ?_⟩
  apply List.ext_getElem
  · simp [len]
  · intro k h1 h2
    have hmk : k < (termsOf mk xs s.terms).1.length := by simpa only [List.length_map] using h2
    simpa only [List.getElem_map, List.getD, List.getElem?_eq_getElem hmk, Option.getD_some] using (dn k (by simpa using h1)).symm

theorem symPair512_ok {bind : Bind} {s s' : Sym} {a b : Expr} {f : List Nat → List Nat → V (List Nat × Sym)}
    {items rest : Items} {l : List Nat} (h : symPair512 bind s a b f items = .ok ((l, s'), rest)) :
    ∃ x y, symVec512 bind s a = some x ∧ symVec512 bind s b = some y ∧ f x y items = .ok ((l, s'), rest) := by
  unfold symPair512 at h
  cases hx : symVec512 bind s a <;> cases hy : symVec512 bind s b <;> simp only [hx, hy] at h
  all_goals first | exact (refuse_ok h).elim | exact ⟨_, _, rfl, rfl, h⟩

theorem symNumber_notWide {bind : Bind} {e : Expr} {n : Int} (h : symNumber bind e = some n) :
    ∀ st, vecArg512 bind st e = none := by
  intro st
  cases e with
  | name name =>
    by_cases hX : name = "X512"
    · simp [symNumber, isNumberLetter, hX] at h
    by_cases hY : name = "Y512"
    · simp [symNumber, isNumberLetter, hY] at h
    by_cases hZ : name = "Z512"
    · simp [symNumber, isNumberLetter, hZ] at h
    simp [vecArg512, vecOf512, hX, hY, hZ]
  | number _ | lane _ _ | call _ _ => rfl

@[local simp] theorem mapM_some {α β : Type} (xs : List α) (f : α → β) :
    xs.mapM (fun a => some (f a)) = some (xs.map f) := List.mapM_pure (m := Option)

theorem each512_binary_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s s' : Sym} {l x y : List Nat}
    {bind : Bind} {a b : Expr} {op : String} {mk : Nat → Nat → List Node → Nat × List Node} {fn : Nat → Nat → Nat}
    {items rest : Items} (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hx : symVec512 bind s a = some x) (hy : symVec512 bind s b = some y)
    (h : symLaneTerms s (fun (q : Nat × Nat) => mk q.1 q.2) (x.zip y) items = .ok ((l, s'), rest))
    (prim : ∀ p q, prim32 op p q = some (fn p q))
    (step : ∀ (T : List Node) (p q : Nat), TableOk s.nvars T → p < T.length → q < T.length →
      Step (inpOf ctx s0) ρ s.nvars T (mk p q T).2 (mk p q T).1 (fn (den (inpOf ctx s0) ρ T p) (den (inpOf ctx s0) ρ T q))) :
    ∃ lanes, Carried ctx s0 ρ s ρ s' st ∧ lanesOf512 (ctx.contract.perm s0) bind st (.call "each32" [.name op, a, b]) = some lanes ∧
      WideValue ctx s0 ρ s' l lanes := by
  obtain ⟨lx, ltx, evx⟩ := symVec512_sound H wf hx
  obtain ⟨ly, lty, evy⟩ := symVec512_sound H wf hy
  let d := den (inpOf ctx s0) ρ s.terms
  let val (p : Nat × Nat) := fn (d p.1) (d p.2)
  obtain ⟨c, vv⟩ := symLaneTerms_sound (val := val) h H wf (by simp [lx, ly]) (by
    intro p mp T e ok
    obtain ⟨mx, my⟩ := List.of_mem_zip mp
    have bx := ltx _ mx
    have by' := lty _ my
    have z := step T p.1 p.2 ok (Nat.lt_of_lt_of_le bx e.le) (Nat.lt_of_lt_of_le by' e.le)
    simpa only [val, d, den_ext wf.words.table e bx, den_ext wf.words.table e by'] using z)
  refine ⟨_, c, ?_, vv⟩
  simp [lanesOf512, evx, evy, prim, List.zip_map, val, d, Function.comp_def]

theorem symEach512_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s s' : Sym} {l : List Nat}
    {bind : Bind} {a b : Expr} {op : String} {items rest : Items} (H : Holds ctx s0 ρ s st) (wf : WF s)
    (h : symEach512 bind s op a b items = .ok ((l, s'), rest)) :
    ∃ lanes, Carried ctx s0 ρ s ρ s' st ∧ lanesOf512 (ctx.contract.perm s0) bind st (.call "each32" [.name op, a, b]) = some lanes ∧
      WideValue ctx s0 ρ s' l lanes := by
  unfold symEach512 at h
  split at h
  next hr =>
    simp only [beq_iff_eq] at hr
    subst op
    cases hv : symVec512 bind s a <;> cases hn : symNumber bind b <;> simp only [hv, hn] at h
    all_goals try exact (refuse_ok h).elim
    rename_i x n
    obtain ⟨len, lt, vx⟩ := symVec512_sound H wf hv
    obtain ⟨_, _, vn, _⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) hn
    let val (i : Nat) := rotr (den (inpOf ctx s0) ρ s.terms i) (n.toNat % 32)
    obtain ⟨c, vv⟩ := symLaneTerms_sound (val := val) h H wf len (by
      intro i mi T e ok
      have bi := lt i mi
      have z := wRotr_step (inp := inpOf ctx s0) (ρ := ρ) (n := n.toNat % 32) ok (Nat.lt_of_lt_of_le bi e.le) (by omega)
      simpa only [val, den_ext wf.words.table e bi] using z)
    refine ⟨_, c, ?_, vv⟩
    simp [lanesOf512, vx, symNumber_notWide hn st, vn, prim32, List.map_map, val, Function.comp_def]
  next =>
    obtain ⟨x, y, hx, hy, he⟩ := symPair512_ok h
    split at he
    next hA =>
      simp only [beq_iff_eq] at hA
      subst op
      exact each512_binary_sound H wf hx hy he (fun _ _ => rfl) (fun _ _ _ ok hp hq => wAdd_step ok hp hq)
    next =>
      split at he
      next hX =>
        simp only [beq_iff_eq] at hX
        subst op
        exact each512_binary_sound H wf hx hy he (fun _ _ => rfl) (fun _ _ _ ok hp hq => wXor_step ok hp hq)
      next => exact (refuse_ok he).elim

theorem getD_map_index {xs : List Nat} {k : Nat} (h : k < xs.length) (d : Nat → Nat) :
    (xs.map d).getD k 0 = d (xs.getD k 0) := by
  rw [getD_index (by simpa using h), getD_index h, List.getElem_map]

theorem flatMap_congr_in {α β : Type} {f g : α → List β} {xs : List α} (h : ∀ x ∈ xs, f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..), ih (fun y my => h y (List.mem_cons_of_mem _ my))]

theorem wideInQuarters {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {x y pick : List Nat}
    (lx : x.length = 16) (ly : y.length = 16) (ltx : ∀ i ∈ x, i < s.terms.length) (lty : ∀ i ∈ y, i < s.terms.length)
    (lp : pick.length = 4) :
    let d := den (inpOf ctx s0) ρ s.terms
    WideValue ctx s0 ρ s (inQuarters x y pick) (inQuarters (x.map d) (y.map d) pick) := by
  dsimp only
  refine ⟨by simp [inQuarters, List.length_flatMap, lp, List.map_const'], ?_, ?_⟩
  · intro i hi
    simp only [inQuarters] at hi
    obtain ⟨q, hq, hi⟩ := List.mem_flatMap.mp hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    have bq := List.mem_range.mp hq
    have b : 4 * q + j % 4 < 16 := by omega
    split
    · rw [getD_index (by omega)]
      exact ltx _ (List.getElem_mem (by omega))
    · rw [getD_index (by omega)]
      exact lty _ (List.getElem_mem (by omega))
  · unfold inQuarters
    rw [List.map_flatMap]
    apply flatMap_congr_in
    intro q mq
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro j _
    have bq := List.mem_range.mp mq
    have b : 4 * q + j % 4 < 16 := by omega
    split
    · exact getD_map_index (by omega) _
    · exact getD_map_index (by omega) _

theorem wideQuarters {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {x y : List Nat}
    (lx : x.length = 16) (ly : y.length = 16) (ltx : ∀ i ∈ x, i < s.terms.length) (lty : ∀ i ∈ y, i < s.terms.length) (n : Nat) :
    let d := den (inpOf ctx s0) ρ s.terms
    WideValue ctx s0 ρ s (quarters x y n) (quarters (x.map d) (y.map d) n) := by
  dsimp only
  refine ⟨by simp [quarters], ?_, ?_⟩
  · intro i hi
    simp only [quarters] at hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    have b : 4 * (n / 4 ^ (j / 4) % 4) + j % 4 < 16 := by omega
    split
    · rw [getD_index (by omega)]
      exact ltx _ (List.getElem_mem (by omega))
    · rw [getD_index (by omega)]
      exact lty _ (List.getElem_mem (by omega))
  · simp only [quarters, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro j _
    have b : 4 * (n / 4 ^ (j / 4) % 4) + j % 4 < 16 := by omega
    split
    · exact getD_map_index (by omega) _
    · exact getD_map_index (by omega) _

theorem symShuffle512_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s s' : Sym} {l : List Nat}
    {bind : Bind} {f : String} {args : List Expr} {items rest : Items} (H : Holds ctx s0 ρ s st) (wf : WF s)
    (h : symShuffle512 bind s f args items = .ok ((l, s'), rest)) :
    ∃ lanes, Carried ctx s0 ρ s ρ s' st ∧ lanesOf512 (ctx.contract.perm s0) bind st (.call f args) = some lanes ∧
      WideValue ctx s0 ρ s' l lanes := by
  unfold symShuffle512 at h
  split at h
  next a b p0 p1 p2 p3 =>
    obtain ⟨x, y, hx, hy, he⟩ := symPair512_ok h
    split at he
    next hf =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hf
      obtain ⟨rfl, hp⟩ := hf
      obtain ⟨rfl, rfl⟩ := pure_pair he
      obtain ⟨lx, ltx, vx⟩ := symVec512_sound H wf hx
      obtain ⟨ly, lty, vy⟩ := symVec512_sound H wf hy
      exact ⟨_, Carried.here H wf, by simp [lanesOf512, vx, vy, hp], wideInQuarters lx ly ltx lty rfl⟩
    next => exact (refuse_ok he).elim
  next a b i =>
    obtain ⟨x, y, hx, hy, he⟩ := symPair512_ok h
    split at he
    next hf =>
      simp only [beq_iff_eq] at hf
      subst f
      cases hn : symNumber bind i <;> simp only [hn] at he
      · exact (refuse_ok he).elim
      rename_i n
      obtain ⟨rfl, rfl⟩ := pure_pair he
      obtain ⟨lx, ltx, vx⟩ := symVec512_sound H wf hx
      obtain ⟨ly, lty, vy⟩ := symVec512_sound H wf hy
      obtain ⟨_, _, vi, _⟩ := symNumber_sound (perm := ctx.contract.perm s0) (st := st) hn
      exact ⟨_, Carried.here H wf, by simp [lanesOf512, vx, vy, vi], wideQuarters lx ly ltx lty n.toNat⟩
    next => exact (refuse_ok he).elim
  next => exact (refuse_ok h).elim

theorem wideAddress {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {bind : Bind} {b n : Expr} {x : Row} {k : Int}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (hx : symReg bind s b = some x) (hk : symNumber bind n = some k) :
    ∃ a, addr512 (ctx.contract.perm s0) bind st "mem512" [b, n] = some a ∧
      ∀ A : Nat, (A : Int) = ev ρ (Lin.add (signed x) (signed (Lin.const k))) → A < M64 → a = A := by
  obtain ⟨xb, vs, ha⟩ := wordAddress_sound H wf hx hk
  exact ⟨(xb + k.toNat) % M64, by simp [addr512, vs, sumList], ha⟩

theorem symLoad512_sound {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s s' : Sym} {l : List Nat}
    {bind : Bind} {args : List Expr} {items rest : Items} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (h : symMemWords ctx bind s args 16 items = .ok ((l, s'), rest)) :
    ∃ lanes, Carried ctx s0 ρ s ρ s' st ∧ lanesOf512 (ctx.contract.perm s0) bind st (.call "mem512" args) = some lanes ∧
      WideValue ctx s0 ρ s' l lanes := by
  obtain ⟨vs, vv, al, c, len, lt, dn⟩ := symMemWords_sound E H wf (by decide) h
  let a := sumList vs % M64
  refine ⟨(List.range 16).map (fun k => Ode.load st.mem (a + 4 * k) 4), c, ?_, len, lt, ?_⟩
  · simp [lanesOf512, addr512, vv, al, a]
  · apply List.ext_getElem
    · simp [len]
    · intro k h1 h2
      have hk : k < 16 := by simpa using h1
      simp only [List.getElem_map, List.getElem_range]
      simpa only [getD_index (by rw [len]; exact hk)] using dn k hk

/-! ## A block read through an address a table holds -/

theorem findLane_spec {c : Contract} {addr : Row} : ∀ {l : List Known} {v j p lr : Nat},
    findLane c addr l = some (v, j, p, lr) → Known.load v j p ∈ l ∧ ∃ x r count, c.tableAt j = some (x, r, count, lr)
  | [], _, _, _, _, h => by simp [findLane] at h
  | k :: more, v, j, p, lr, h => by
    cases k with
    | load v' j' p' =>
      simp only [findLane] at h
      cases ht : c.tableAt j' with
      | none =>
        simp only [ht] at h
        obtain ⟨m, t⟩ := findLane_spec h
        exact ⟨List.mem_cons_of_mem _ m, t⟩
      | some t =>
        obtain ⟨x, r, count, l'⟩ := t
        simp only [ht] at h
        split at h
        next =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨List.mem_cons_self .., x, r, count, ht⟩
        next =>
          obtain ⟨m, t⟩ := findLane_spec h
          exact ⟨List.mem_cons_of_mem _ m, t⟩
    | or _ _ _ | held _ _ _ | block _ _ _ _ =>
      simp only [findLane] at h
      obtain ⟨m, t⟩ := findLane_spec h
      exact ⟨List.mem_cons_of_mem _ m, t⟩

/-- Sixty-four bytes read through an address a table holds: the read is one the contract allows, within the
lane's blocks, which hold what they held at entry; the sixteen new unknowns can be the block's words. -/
theorem symLoadBlock_sound {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s s' : Sym} {l : List Nat}
    {v j pl lr : Nat} {addr : Row} {items rest : Items} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hk : Known.load v j pl ∈ s.known) {x : String} {r count : Nat} (ht : ctx.contract.tableAt j = some (x, r, count, lr))
    (hb : bounded s.nvars addr)
    (h : symLoadBlock s v j pl lr addr items = .ok ((l, s'), rest)) (a : Nat)
    (ha : ∀ A : Nat, (A : Int) = ev ρ addr → A < M64 → a = A) :
    allowed (ctx.contract.perm s0).read a 64 = true ∧
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ WideValue ctx s0 ρ' s' l ((List.range 16).map fun k => load st.mem (a + 4 * k) 4) := by
  unfold symLoadBlock at h
  split at h
  · exact (refuse_ok h).elim
  next hp8 =>
    have p8 : pl % 8 = 0 := by simpa using hp8
    obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨_, r2, e2, h⟩ := V.bind_ok h
    have g1 := entail_sound e1 ρ H.facts
    have g2 := entail_sound e2 ρ H.facts
    simp only [ev_sub, ev_scale, ev_var, ev_const] at g1 g2
    -- the address the table holds
    obtain ⟨x', r', n, hj, pn, hv⟩ := H.known _ hk
    obtain ⟨n', hj', hcount⟩ := tableAt_fixed ht
    rw [hj] at hj'
    simp only [Option.some.injEq, Prod.mk.injEq] at hj'
    obtain ⟨rfl, rfl, rfl⟩ := hj'
    have vlt : v < s.nvars := wf.known _ hk
    have ilt : pl / 8 < count := by rw [hcount]; omega
    have eptr : lanePtr s0 r' (pl / 8) = load s0.mem (s0.reg r' + pl) 8 := by
      unfold lanePtr; rw [show 8 * (pl / 8) = pl by omega]
    obtain ⟨fit, apart, bytes, outs⟩ := E.lane ht ilt
    have lr16 : lr < 16 := tableAt_lt ht
    have hlr := H.entry lr lr16
    rw [hlr, hv, ← eptr] at g2
    rw [hv, ← eptr] at g1
    have boff : bounded s.nvars (Lin.sub addr (Lin.var v)) := bounded_sub hb (bounded_var vlt)
    have eoff : ev ρ (Lin.sub addr (Lin.var v)) = ev ρ addr - (lanePtr s0 r' (pl / 8) : Nat) := by rw [ev_sub, ev_var, hv, ← eptr]
    have A : a = lanePtr s0 r' (pl / 8) + (ev ρ (Lin.sub addr (Lin.var v))).toNat := by
      apply ha
      · rw [eoff]; omega
      · rw [eoff]; unfold M64 at fit ⊢; omega
    have inside : ∀ y, a ≤ y → y < a + 64 → lanePtr s0 r' (pl / 8) ≤ y ∧ y < lanePtr s0 r' (pl / 8) + 64 * s0.reg lr := by
      intro y h1 h2
      rw [A, eoff] at h1 h2
      omega
    have same : ∀ y, a ≤ y → y < a + 64 → st.mem y = s0.mem y := by
      intro y h1 h2
      obtain ⟨i1, i2⟩ := inside y h1 h2
      apply H.mem
      · simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        omega
      · unfold Contract.inOut
        rw [List.any_eq_false]
        intro ⟨x'', r'', n''⟩ m
        have := outs x'' r'' n'' m
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
    have hread : allowed (ctx.contract.perm s0).read a 64 = true := by
      apply allowed_of
      intro y h1 h2
      obtain ⟨i1, i2⟩ := inside y h1 h2
      simp only [Contract.perm, Bool.or_eq_true]
      right
      unfold Contract.inLane
      exact List.any_eq_true.mpr ⟨(x', r', count, lr), tableAt_mem ht,
        List.any_eq_true.mpr ⟨pl / 8, List.mem_range.mpr ilt, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩⟩
    refine ⟨hread, ?_⟩
    -- the sixteen unknowns: the block's words
    let ρ' : Nat → Int := fun k => if s.nvars ≤ k ∧ k < s.nvars + 16 then ((load s0.mem (a + 4 * (k - s.nvars)) 4 : Nat) : Int) else ρ k
    have ag : Agree s.nvars ρ ρ' := by
      intro k hk'
      show ρ k = if s.nvars ≤ k ∧ k < s.nvars + 16 then ((load s0.mem (a + 4 * (k - s.nvars)) 4 : Nat) : Int) else ρ k
      rw [if_neg (by omega)]
    have new : ∀ w, w < 16 → ρ' (s.nvars + w) = (load s0.mem (a + 4 * w) 4 : Nat) := by
      intro w hw
      show (if s.nvars ≤ s.nvars + w ∧ s.nvars + w < s.nvars + 16 then ((load s0.mem (a + 4 * (s.nvars + w - s.nvars)) 4 : Nat) : Int) else ρ (s.nvars + w)) = _
      rw [if_pos (by omega), Nat.add_sub_cancel_left]
    have word : ∀ w, load s0.mem (a + 4 * w) 4 < 4294967296 := by
      intro w
      have lt := load_lt s0.mem (a + 4 * w) 4
      have p4 : (256 : Nat) ^ 4 = 4294967296 := by decide
      rw [p4] at lt; exact lt
    have eoff' : ev ρ' (Lin.sub addr (Lin.var v)) = ev ρ (Lin.sub addr (Lin.var v)) := (ev_agree boff ag).symm
    have c1 := Carried.more (ctx := ctx) (s0 := s0) (st := st) H wf 16 ag []
      (.block j pl (Lin.sub addr (Lin.var v)) ((List.range 16).map (s.nvars + ·)))
      (fun f m => nomatch m)
      ⟨bounded_mono (Nat.le_add_right _ _) boff, by
        intro u hu
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
        have := List.mem_range.mp hw
        omega⟩
      (fun f m => nomatch m)
      ⟨x', r', count, lr, ht, p8, ilt, by rw [eoff', eoff]; omega, by rw [eoff', eoff]; omega, by simp, by
        intro w hw
        have e : ((List.range 16).map (s.nvars + ·)).getD w 0 = s.nvars + w := by
          rw [getD_index (by simpa using hw) 0]; simp
        rw [e, new w hw, eoff', ← A]⟩
    have c2 := symLaneTerms_sound (val := fun r => (ev ρ' r % W32i).toNat) h c1.holds c1.wf (by simp)
      (fun r m T _ ok => wAtom_step ok (by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp m
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
        have := List.mem_range.mp hw
        exact bounded_var (show s.nvars + w < s.nvars + 16 by omega)))
    refine ⟨ρ', c1.then c2.1, c2.2.1, c2.2.2.1, ?_⟩
    rw [← c2.2.2.2]
    apply List.ext_getElem
    · simp
    · intro w h1 h2
      have hw : w < 16 := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, ev_var]
      rw [new w hw]
      have := word w
      have hl : load st.mem (a + 4 * w) 4 = load s0.mem (a + 4 * w) 4 :=
        load_congr _ _ _ _ fun y h1 h2 => same y (by omega) (by omega)
      rw [hl]
      unfold W32i
      omega

/-- A 512-bit load through an address a table holds, as the machine does it. -/
theorem symLoadLane512_sound {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s s' : Sym} {l : List Nat}
    {bind : Bind} {args : List Expr} {addr : Row} {v j pl lr : Nat} {items rest : Items} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hw : symWordAddr bind s args = some addr) (hf : findLane ctx.contract addr s.known = some (v, j, pl, lr))
    (h : symLoadBlock s v j pl lr addr items = .ok ((l, s'), rest)) :
    ∃ ρ' lanes, Carried ctx s0 ρ s ρ' s' st ∧ lanesOf512 (ctx.contract.perm s0) bind st (.call "mem512" args) = some lanes ∧
      WideValue ctx s0 ρ' s' l lanes := by
  obtain ⟨vs, vv, ba, loc⟩ := symWordAddr_sound H wf hw
  obtain ⟨hk, x, r, count, ht⟩ := findLane_spec hf
  obtain ⟨al, ρ', c, val⟩ := symLoadBlock_sound E H wf hk ht ba h (sumList vs % M64) loc
  refine ⟨ρ', _, c, ?_, val⟩
  simp [lanesOf512, addr512, vv, al]

private theorem dot_aligned : ∀ (cs : List Int) (ρ : Nat → Int), cs.all (fun x => x % 64 == 0) = true → (64 : Int) ∣ dot cs ρ
  | [], _, _ => Int.dvd_zero _
  | c :: cs, ρ, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    exact Int.dvd_add (Int.dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero h.1)) (dot_aligned cs _ h.2)

private theorem aligned64_sound {addr : Row} (h : aligned64 addr = true) (ρ : Nat → Int) : ev ρ addr % 64 = 0 := by
  simp only [aligned64, Bool.and_eq_true, beq_iff_eq] at h
  exact Int.dvd_iff_emod_eq_zero.mp (Int.dvd_add (dot_aligned addr.coeff ρ h.1) (Int.dvd_of_emod_eq_zero h.2))

theorem alignedFrameAddress {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym} {addr : Row}
    {bind : Bind} {args : List Expr} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hw : symWordAddr bind s args = some addr) (hm : aligned64 addr = true)
    (ok : ∀ g ∈ frameSpanGoals ctx s addr 64, g.holds ρ) :
    ∃ a, addr512 (ctx.contract.perm s0) bind st "mem512a" args = some a ∧ (a : Int) = ev ρ addr ∧
      s0.reg RSP - ctx.contract.stack ≤ a ∧ a + 64 ≤ s0.reg RSP ∧ bounded s.nvars (frameOffset addr) := by
  obtain ⟨vs, vv, b, mod⟩ := symWordAddr_sound H wf hw
  obtain ⟨a, ea, lt, lo, hi⟩ := frameSpan_sound E H ok
  have hmod := mod a ea lt
  have dal := aligned64_sound hm ρ
  rw [← ea] at dal
  change (a : Int) % ((64 : Nat) : Int) = 0 at dal
  rw [← Int.natCast_emod a 64] at dal
  have ha : a % 64 = 0 := by exact_mod_cast dal
  refine ⟨a, by simp [addr512, vv, hmod, ha], ea, lo, hi, ?_⟩
  exact bounded_sub b (bounded_var (x := RSP) (Nat.lt_of_lt_of_le (by decide) wf.base))

theorem symSpillLoad_sound {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s s' : Sym} {l : List Nat}
    {bind : Bind} {args : List Expr} {items rest : Items} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (h : symSpillLoad ctx bind s args items = .ok ((l, s'), rest)) :
    ∃ lanes, Carried ctx s0 ρ s ρ s' st ∧ lanesOf512 (ctx.contract.perm s0) bind st (.call "mem512a" args) = some lanes ∧
      WideValue ctx s0 ρ s' l lanes := by
  unfold symSpillLoad at h
  cases ha : symWordAddr bind s args <;> cases hs : s.spill <;> simp only [ha, hs] at h
  all_goals try exact (refuse_ok h).elim
  rename_i addr pair
  obtain ⟨o, ids⟩ := pair
  simp only at h
  split at h
  next hal =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hal
    obtain ⟨_, _, hc, he⟩ := V.bind_ok h
    obtain ⟨hl, hstate⟩ := pure_pair he
    subst l s'
    obtain ⟨a, va, ea, lo, hi, _⟩ := alignedFrameAddress E H wf ha hal.1 (entails_sound H.facts hc)
    have perm := (frameSpan_perm (ctx := ctx) lo hi).1
    obtain ⟨_, len, lt⟩ := wf.words.spill o ids hs
    have ea' : ((s0.reg RSP : Int) + ev ρ o).toNat = a := by
      rw [← hal.2, frameOffset_eval H, ← ea]
      omega
    refine ⟨(List.range 16).map (fun k => Ode.load st.mem (a + 4 * k) 4), Carried.here H wf, ?_, len, lt, ?_⟩
    · simp [lanesOf512, va, perm]
    · apply List.ext_getElem
      · simp [len]
      · intro k h1 h2
        have hk : k < ids.length := by simpa only [List.length_map] using h2
        simp only [List.getElem_map, List.getElem_range]
        simpa only [ea', getD_index hk] using H.words.spill o ids hs k hk
  next => exact (refuse_ok h).elim

theorem symLanes512_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind)
    {s s' : Sym} {v : Expr} {items rest : Items} {ρ : Nat → Int} {st : State} {l : List Nat}
    (h : symLanes512 ctx bind s v items = .ok ((l, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) :
    ∃ ρ' lanes, Carried ctx s0 ρ s ρ' s' st ∧ lanesOf512 (ctx.contract.perm s0) bind st v = some lanes ∧
      WideValue ctx s0 ρ' s' l lanes := by
  cases v with
  | number _ => simp only [symLanes512] at h; exact (refuse_ok h).elim
  | lane _ _ => simp only [symLanes512] at h; exact (refuse_ok h).elim
  | name n =>
    simp only [symLanes512] at h
    cases hv : symVec512 bind s (.name n) <;> simp only [hv] at h
    · exact (refuse_ok h).elim
    · obtain ⟨rfl, rfl⟩ := pure_pair h
      obtain ⟨len, lt, move⟩ := symVec512_sound H wf hv
      exact ⟨ρ, _, Carried.here H wf, move, len, lt, rfl⟩
  | call f args =>
    simp only [symLanes512] at h
    split at h
    next hz =>
      obtain ⟨rfl, rfl⟩ := pure_pair h
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hz
      obtain ⟨rfl, rfl⟩ := hz
      obtain ⟨c, val⟩ := wideReplicate H wf (bounded_const s.nvars 0)
      exact ⟨ρ, _, c, rfl, by simpa [ev_const] using val⟩
    next =>
      split at h
      next hf =>
        have hf' : f = "spread16" := by simpa using hf
        subst f
        split at h
        next =>
          split at h
          next hg =>
            simp only [beq_iff_eq] at hg
            subst_vars
            obtain ⟨ρ', x, c, eval, val⟩ := symSpread16_sound E bind h H wf
            exact ⟨ρ', _, c, by simp [lanesOf512, eval], val⟩
          next => exact (refuse_ok h).elim
        next => exact (refuse_ok h).elim
      next =>
        split at h
        next hf =>
          simp only [beq_iff_eq] at hf
          subst f
          split at h
          next =>
            obtain ⟨lanes, c, eval, val⟩ := symEach512_sound H wf h
            exact ⟨ρ, lanes, c, eval, val⟩
          next => exact (refuse_ok h).elim
        next =>
          split at h
          next hf =>
            simp only [beq_iff_eq] at hf
            subst f
            cases hfl : (symWordAddr bind s args).bind fun a => (findLane ctx.contract a s.known).map fun x => (a, x) with
            | none =>
              simp only [hfl] at h
              obtain ⟨lanes, c, eval, val⟩ := symLoad512_sound E H wf h
              exact ⟨ρ, lanes, c, eval, val⟩
            | some t =>
              obtain ⟨a, v, j, pl, lr⟩ := t
              simp only [hfl] at h
              obtain ⟨a', hw, hx⟩ := Option.bind_eq_some_iff.mp hfl
              obtain ⟨y, hfy, hy⟩ := Option.map_eq_some_iff.mp hx
              simp only [Prod.mk.injEq] at hy
              obtain ⟨rfl, rfl⟩ := hy
              exact symLoadLane512_sound E H wf hw hfy h
          next =>
            split at h
            next hf =>
              simp only [beq_iff_eq] at hf; subst f
              obtain ⟨lanes, c, eval, val⟩ := symSpillLoad_sound E H wf h
              exact ⟨ρ, lanes, c, eval, val⟩
            next =>
              obtain ⟨lanes, c, eval, val⟩ := symShuffle512_sound H wf h
              exact ⟨ρ, lanes, c, eval, val⟩

theorem load_spilled_word (mem : Nat → Nat) (a : Nat) (lanes : List Nat) {k : Nat} (hk : k < lanes.length)
    (hv : lanes.getD k 0 < W32) : load (storeWords mem a lanes) (a + 4 * k) 4 = lanes.getD k 0 := by
  let base := a + 4 * k
  calc
    _ = load (store mem base (lanes.getD k 0) 4) base 4 := by
      apply load_congr
      intro y hy1 hy2
      have e : y = base + (y - base) := by omega
      rw [e]
      exact (storeWords_at mem a lanes k (y - base) hk (by omega)).trans (store_at 4 mem base _ _ (by omega)).symm
    _ = _ := load_store_same _ _ _ _ hv

theorem symSpillStore_sound {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s s' : Sym} {l : List Nat}
    {bind : Bind} {args : List Expr} {items rest : Items} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (h : symSpillStore ctx bind s args l items = .ok (s', rest)) (len : l.length = 16) (lt : ∀ i ∈ l, i < s.terms.length) :
    ∃ a, addr512 (ctx.contract.perm s0) bind st "mem512a" args = some a ∧ allowed (ctx.contract.perm s0).write a 64 = true ∧
      Carried ctx s0 ρ s ρ s' { st with mem := storeWords st.mem a (l.map (den (inpOf ctx s0) ρ s.terms)) } := by
  unfold symSpillStore at h
  cases ha : symWordAddr bind s args <;> simp only [ha] at h
  · exact (refuse_ok h).elim
  rename_i addr
  split at h
  next hm =>
    obtain ⟨_, _, hc, h1⟩ := V.bind_ok h
    obtain ⟨_, _, hd, he⟩ := V.bind_ok h1
    have hy := V.pure_ok he
    injection hy with e _; subst s'
    obtain ⟨a, va, ea, lo, hi, ba⟩ := alignedFrameAddress E H wf ha hm (entails_sound H.facts hc)
    have apart := savedWordSpan_sound H ea (entails_sound H.facts hd)
    have off := frameOffset_eval H addr
    let lanes := l.map (den (inpOf ctx s0) ρ s.terms)
    have hlen : lanes.length = 16 := by simp [lanes, len]
    refine ⟨a, va, (frameSpan_perm (ctx := ctx) lo hi).2, ⟨Agree.refl _ _, Nat.le_refl _, ?_, ?_⟩⟩
    · refine H.frameSpanWrite E lo hi apart (fun y hy => storeWords_other _ _ _ _ (by rw [hlen]; exact hy)) ?_
      intro o ids hs k hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      have aa : ((s0.reg RSP : Int) + ev ρ (frameOffset addr)).toNat = a := by rw [off, ← ea]; omega
      have kl : k < lanes.length := by simpa only [lanes, List.length_map] using hk
      have ev := getD_map_index hk (den (inpOf ctx s0) ρ s.terms)
      have val : lanes.getD k 0 < W32 := by
        rw [ev]
        exact den_lt wf.words.table (inpOf_lt ctx s0) wf.words.rotrs _
      rw [aa, load_spilled_word _ _ _ kl val, ev]
    · exact ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.facts, wf.bytes, wf.spec, wf.wrote,
        ⟨wf.words.table, wf.words.atoms, wf.words.vec, wf.words.rotrs, wf.words.wrote, fun o ids h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨ba, len, lt⟩⟩, wf.known⟩
  next => exact (refuse_ok h).elim

theorem lanesOf512_of_vecArg {perm : Perm} {bind : Bind} {st : State} {v : Expr} {lanes : List Nat}
    (h : vecArg512 bind st v = some lanes) : lanesOf512 perm bind st v = some lanes := by
  cases v with
  | name _ => exact h
  | number _ | lane _ _ | call _ _ => simp [vecArg512] at h

theorem symVset512_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) {s s' : Sym} {place v : Expr}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symStmt ctx bind s (.vset512 place v) items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (base u : Nat) :
    ∃ ρ' st', Carried ctx s0 ρ s ρ' s' st' ∧ execStmt (ctx.contract.perm s0) bind base u st (.vset512 place v) = some st' ∧
      st'.rip = st.rip := by
  cases place with
  | number _ => simp only [symStmt] at h; exact (refuse_ok h).elim
  | lane _ _ => simp only [symStmt] at h; exact (refuse_ok h).elim
  | call f args =>
    rcases args with _ | ⟨b, _ | ⟨n, _ | ⟨_, _⟩⟩⟩
    · simp only [symStmt] at h; exact (refuse_ok h).elim
    · simp only [symStmt] at h; exact (refuse_ok h).elim
    · simp only [symStmt] at h
      split at h
      next hf =>
        simp only [beq_iff_eq] at hf
        subst f
        cases hv : symVec512 bind s v <;> cases hx : symReg bind s b <;> cases hk : symNumber bind n <;> simp only [hv, hx, hk] at h
        all_goals try exact (refuse_ok h).elim
        rename_i l x k
        obtain ⟨len, lt, src⟩ := symVec512_sound H wf hv
        let d := den (inpOf ctx s0) ρ s.terms
        let lanes := l.map d
        have load := lanesOf512_of_vecArg (perm := ctx.contract.perm s0) src
        have hl : lanes.length = 16 := by simp [lanes, len]
        obtain ⟨a, va, ha⟩ := wideAddress H wf hx hk
        obtain ⟨al, c⟩ := symStoreWords_sound E H wf (by decide) h ha hl lt (fun j hj => getD_map_index (by omega) d)
        refine ⟨ρ, _, c, ?_, rfl⟩
        simp [execStmt, execVec512, load, len, va, al, lanes, d]
      next =>
        split at h
        next hf =>
          simp only [beq_iff_eq] at hf; subst f
          cases hv : symVec512 bind s v <;> simp only [hv] at h
          · exact (refuse_ok h).elim
          obtain ⟨len, lt, src⟩ := symVec512_sound H wf hv
          obtain ⟨a, va, al, c⟩ := symSpillStore_sound E H wf h len lt
          have load := lanesOf512_of_vecArg (perm := ctx.contract.perm s0) src
          refine ⟨ρ, _, c, ?_, rfl⟩
          simp [execStmt, execVec512, load, len, va, al]
        next => exact (refuse_ok h).elim
    · simp only [symStmt] at h; exact (refuse_ok h).elim
  | name n =>
    simp only [symStmt] at h
    cases hr : vecOf512 bind n <;> simp only [hr] at h
    · exact (refuse_ok h).elim
    rename_i r
    obtain ⟨⟨l, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨ρ', lanes, c, ev, len, lt, eq⟩ := symLanes512_sound E bind e1 H wf
    simp only [len, beq_self_eq_true, ite_true] at h
    have he := V.pure_ok h
    injection he with h1 _; subst s'
    refine ⟨ρ', setVec512 st r lanes, ⟨c.agree, c.mono, ?_, ?_⟩, ?_, rfl⟩
    · exact ⟨c.holds.entry, c.holds.reg, c.holds.small, c.holds.zf, c.holds.cf, c.holds.frame, c.holds.facts, c.holds.bytes,
        c.holds.spec, c.holds.mem, c.holds.wrote,
        ⟨fun x ids hx k hk => by
          show (if x = r then lanes.getD k 0 else st.vec x k) = _
          rcases lookup_cons_cases hx with ⟨rfl, rfl⟩ | ⟨ne, hx'⟩
          · rw [ite_eq_left rfl, eq]
            simp only [List.getD, List.getElem?_eq_getElem hk, List.getElem?_map, Option.map_some, Option.getD_some]
          · rw [ite_eq_right ne]; exact c.holds.words.vec x ids hx' k hk,
         c.holds.words.intact, c.holds.words.wrote, c.holds.words.spill⟩, c.holds.known⟩
    · exact ⟨c.wf.base, c.wf.reg, c.wf.zf, c.wf.cf, c.wf.frame, c.wf.facts, c.wf.bytes, c.wf.spec, c.wf.wrote,
        ⟨c.wf.words.table, c.wf.words.atoms,
         fun x ids hx => by
           rcases lookup_cons_cases hx with ⟨_, rfl⟩ | ⟨_, hx'⟩
           · exact ⟨Or.inr len, lt⟩
           · exact c.wf.words.vec x ids hx',
         c.wf.words.rotrs, c.wf.words.wrote, c.wf.words.spill⟩, c.wf.known⟩
    · have l16 : lanes.length = 16 := by simp [eq, len]
      simp [execStmt, execVec512, ev, l16, hr]

/-- An effect the verifier accepts runs in the machine model and preserves the verifier's invariant. -/
theorem symStmt_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) {s s' : Sym} {stmt : Stmt}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symStmt ctx bind s stmt items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (base u : Nat) :
    ∃ ρ' st', Carried ctx s0 ρ s ρ' s' st' ∧ execStmt (ctx.contract.perm s0) bind base u st stmt = some st' ∧ st'.rip = st.rip := by
  cases stmt with
  | vset _ _ => exact symVset_sound E bind h H wf base u
  | vset512 _ _ => exact symVset512_sound E bind h H wf base u
  | nothing | ret | call _ | jump _ _ | set _ _ =>
    exact symStmt_scalar E bind h H wf base u (fun _ _ e => by cases e) (fun _ _ e => by cases e)

end Ode
