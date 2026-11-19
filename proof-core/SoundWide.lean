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
            simpa only [List.getD, List.getElem?_eq_getElem hk, Option.getD_some] using H.words.1 r ids hl k hk
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
            obtain ⟨lanes, c, eval, val⟩ := symLoad512_sound E H wf h
            exact ⟨ρ, lanes, c, eval, val⟩
          next =>
            obtain ⟨lanes, c, eval, val⟩ := symShuffle512_sound H wf h
            exact ⟨ρ, lanes, c, eval, val⟩

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
        have load : lanesOf512 (ctx.contract.perm s0) bind st v = some lanes := by
          cases v with
          | name n => exact src
          | number _ | lane _ _ | call _ _ => simp [vecArg512] at src
        have hl : lanes.length = 16 := by simp [lanes, len]
        obtain ⟨a, va, ha⟩ := wideAddress H wf hx hk
        obtain ⟨al, c⟩ := symStoreWords_sound E H wf (by decide) h ha hl lt (fun j hj => getD_map_index (by omega) d)
        refine ⟨ρ, _, c, ?_, rfl⟩
        simp [execStmt, execVec512, load, hl, va, al]
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
          · rw [ite_eq_right ne]; exact c.holds.words.1 x ids hx' k hk,
         c.holds.words.2.1, c.holds.words.2.2⟩, c.holds.known⟩
    · exact ⟨c.wf.base, c.wf.reg, c.wf.zf, c.wf.cf, c.wf.frame, c.wf.facts, c.wf.bytes, c.wf.spec, c.wf.wrote,
        ⟨c.wf.words.table, c.wf.words.atoms,
         fun x ids hx => by
           rcases lookup_cons_cases hx with ⟨_, rfl⟩ | ⟨_, hx'⟩
           · exact ⟨Or.inr len, lt⟩
           · exact c.wf.words.vec x ids hx',
         c.wf.words.rotrs, c.wf.words.wrote⟩, c.wf.known⟩
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
