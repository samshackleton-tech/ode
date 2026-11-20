import SoundCallW
/-!
# Why the verifier's yes is right, 7c: a place of a loop, and the vector registers there

A loop is cut at a place the proof names. Here: what a place says of a state of the machine there
(`AtPlace`): of the registers it names, and of the vector registers lane by lane (`LaneSays`). Then the
verifier's work on first coming to a place (`generalize`) and on coming there again (`arrive`): of the state
it came in, the place says what it says; and of every state of which the place says so, what the general
state holds is so. The words of the vector registers are, in the general state, unknowns of their own:
each is given the word the machine's register holds, and the definition the place names is then known to
give those words.
-/
namespace Ode
open Arithmetic

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
  · exact (symEnv_bounded ctx.contract).mono wf.base16 nv m

/-! ## What a place says of vector registers -/

/-- The names of a place as values, for what it says of vector registers: a name the place gives is what its
register holds; the contract's names are what they are for an `ensures` of a whole run of words (`envW`). -/
def placeValsW (ctx : Ctx) (pl : Place) (s0 st : State) : List (String × Val) :=
  pl.names.map (fun nr => (nr.1, Val.int (st.reg nr.2))) ++ ctx.contract.envW s0

/-- What a place says of lane `i` of vector registers, of a state of the machine there: the definition, used
with the place's things (the lane's number under its name), is the list of the words the registers hold in
that lane; and each of those is a word (below 2^32). -/
def LaneSays (ctx : Ctx) (pl : Place) (s0 st : State) (L : PlaceLanes) (i : Nat) : Prop :=
  (∀ r ∈ L.regs, st.vec r i < W32) ∧
  Value ctx.defs ((L.x, Val.int (i : Int)) :: placeValsW ctx pl s0 st) (.call L.f L.args)
    (.list (L.regs.map fun r => Val.word (st.vec r i)))

/-- What a place says of a cell of the frame, of a state of the machine there: word `i` of the sixty-four
bytes that lie `C.off` bytes above the stack pointer is the word the place's expression gives, with the word's
number under its name. -/
def CellSays (ctx : Ctx) (pl : Place) (s0 st : State) (C : PlaceCell) : Prop :=
  ∀ i : Nat, i < 16 → Value ctx.defs ((C.x, Val.int (i : Int)) :: placeValsW ctx pl s0 st) C.e
    (.word (load st.mem (st.reg RSP + C.off + 4 * i) 4))

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}

theorem namesW_den (H : Holds ctx s0 ρ s st) : ∀ (names : List (String × Nat)), (∀ nr ∈ names, nr.2 < 16) →
    EnvDen ctx s0 ρ s.terms (names.map fun nr => (nr.1, WVal.num (s.reg nr.2))) (names.map fun nr => (nr.1, Val.int (st.reg nr.2)))
  | [], _ => by simp [EnvDen]
  | (x, r) :: more, hn => by
    have hd := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := s.terms) (s.reg r)
    rw [← H.reg r (hn (x, r) (List.mem_cons_self ..))] at hd
    exact ⟨rfl, hd, namesW_den H more (fun nr m => hn nr (List.mem_cons_of_mem _ m))⟩

/-- The names at a place on words stand for the names at the place in the account. -/
theorem placeW_den {p : Program} (E : Setting ctx p s0) (pl : Place) (H : Holds ctx s0 ρ s st) (hn : ∀ nr ∈ pl.names, nr.2 < 16) :
    EnvDen ctx s0 ρ s.terms (placeW ctx pl s) (placeValsW ctx pl s0 st) :=
  EnvDen.append (namesW_den H pl.names hn) (wenv_sound E H)

/-- The terms the verifier holds in a lane of vector registers are the words the machine's registers hold there. -/
theorem laneTerms_sound (H : Holds ctx s0 ρ s st) {i : Nat} : ∀ {regs ids : List Nat},
    laneTerms s i regs = some ids → ids.map (den (inpOf ctx s0) ρ s.terms) = regs.map fun r => st.vec r i
  | [], ids, h => by
    simp only [laneTerms, Option.some.injEq] at h
    subst h; rfl
  | r :: more, ids, h => by
    simp only [laneTerms] at h
    cases ha : (s.vec.lookup r).bind (·[i]?) with
    | none => simp [ha] at h
    | some a =>
      cases hr : laneTerms s i more with
      | none => simp [ha, hr] at h
      | some rest =>
        simp only [ha, hr, Option.some.injEq] at h
        subst h
        obtain ⟨lanes, hl, hi⟩ := Option.bind_eq_some_iff.mp ha
        have hlt : i < lanes.length := (List.getElem?_eq_some_iff.mp hi).1
        have e := H.words.vec r lanes hl i hlt
        have ea : lanes.getD i 0 = a := by simp [List.getD, hi]
        simp only [List.map_cons]
        rw [laneTerms_sound H hr, e, ea]

/-- What the verifier has shown of a place's lanes is so of the machine's state. -/
theorem lanesShown_sound {p : Program} (E : Setting ctx p s0) (pl : Place) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hn : ∀ nr ∈ pl.names, nr.2 < 16) {L : PlaceLanes} (h : lanesShown ctx pl s L = true) :
    ∀ i, i < 16 → LaneSays ctx pl s0 st L i := by
  intro i hi
  unfold lanesShown at h
  have hi' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  unfold laneShown at hi'
  cases hw : weval ctx s.tab.find s WFUEL ((L.x, .int i) :: placeW ctx pl s) (.call L.f L.args) with
  | none => simp [hw] at hi'
  | some v =>
    cases v with
    | list l =>
      simp only [hw] at hi'
      cases hids : wordIds s.tab.find l with
      | none => simp [hids] at hi'
      | some ids =>
        cases hheld : laneTerms s i L.regs with
        | none => simp [hids, hheld] at hi'
        | some held =>
          simp only [hids, hheld, beq_iff_eq] at hi'
          subst hi'
          obtain ⟨B, hB⟩ := held_bound H
          obtain ⟨a, ea, da⟩ := weval_sound H wf hB WFUEL ((L.x, .int i) :: placeW ctx pl s)
            ((L.x, Val.int (i : Int)) :: placeValsW ctx pl s0 st) _ _ hw ⟨rfl, WDen.int i, placeW_den E pl H hn⟩
          obtain ⟨ws, rfl⟩ := WDen.list_inv da
          have ews := wordIds_den wf da hids
          have evec := laneTerms_sound H hheld
          refine ⟨?_, WFUEL + B, ?_⟩
          · intro r mr
            have m : st.vec r i ∈ ids.map (den (inpOf ctx s0) ρ s.terms) := by
              rw [evec]; exact List.mem_map.mpr ⟨r, mr, rfl⟩
            obtain ⟨id, _, e⟩ := List.mem_map.mp m
            rw [← e]; exact Holds.den_lt wf id
          · have e2 : ids.map (fun i => Val.word (den (inpOf ctx s0) ρ s.terms i)) = L.regs.map (fun r => Val.word (st.vec r i)) := by
              have e3 := congrArg (List.map Val.word) evec
              simp only [List.map_map] at e3
              exact e3
            rw [ea, ews, e2]
    | _ => simp [hw] at hi'

end

/-! ## A use of a definition, turned inside out -/

/-- The value of a use of a definition of the specification is the value of the definition's text, with the
values of the things it is used with under its names. -/
theorem Value.call_inv {defs : List Def} {env : List (String × Val)} {f : String} {args : SExpr} {v : Val}
    (hlen : (f == "len") = false) (hown : own.contains f = false) (h : Value defs env (.call f args) v) :
    ∃ d as fuel, findDef defs f = some d ∧ evalList (evalSpec defs fuel env) args = some as ∧
      d.params.length = as.length ∧ evalSpec defs fuel (d.params.zip as) d.body = some v := by
  obtain ⟨fuel, hf⟩ := h
  cases fuel with
  | zero => simp [evalSpec] at hf
  | succ fuel =>
    simp only [evalSpec] at hf
    cases hl : evalList (evalSpec defs fuel env) args with
    | none => simp [hl] at hf
    | some as =>
      simp only [hl, hlen, hown, Bool.false_eq_true, if_false] at hf
      cases hd : findDef defs f with
      | none => simp [hd] at hf
      | some d =>
        simp only [hd] at hf
        split at hf
        next hp => exact ⟨d, as, fuel, rfl, hl, by simpa using hp, hf⟩
        next => simp at hf

/-! ## Lists by their places -/

theorem lookup_map_mem {α : Type} (a : α → Nat) (b : α → List Nat) {x : Nat} {ids : List Nat} : ∀ {xs : List α},
    (xs.map fun k => (a k, b k)).lookup x = some ids → ∃ k ∈ xs, a k = x ∧ b k = ids
  | [], h => by simp at h
  | k :: more, h => by
    simp only [List.map_cons, List.lookup_cons] at h
    cases hx : (x == a k) with
    | true =>
      rw [hx] at h
      injection h with h
      exact ⟨k, List.mem_cons_self .., (by simpa using hx : x = a k).symm, h⟩
    | false =>
      rw [hx] at h
      obtain ⟨k', m, e⟩ := lookup_map_mem a b h
      exact ⟨k', List.mem_cons_of_mem _ m, e⟩

theorem lookup_append_or {β : Type} {x : Nat} {v : β} : ∀ {l l' : List (Nat × β)}, (l ++ l').lookup x = some v →
    l.lookup x = some v ∨ l'.lookup x = some v
  | [], _, h => Or.inr h
  | (k, b) :: more, l', h => by
    simp only [List.cons_append, List.lookup_cons] at h ⊢
    cases hx : (x == k) with
    | true => rw [hx] at h; exact Or.inl h
    | false => rw [hx] at h; exact lookup_append_or h

theorem laneKeysOf_spec {key : Nat → Option (List Key)} : ∀ {l : List Nat} {ks : List (List Key)},
    laneKeysOf key l = some ks → ∀ k (hk : k < l.length), key l[k] = some (ks.getD k [])
  | [], ks, h => fun k hk => absurd hk (Nat.not_lt_zero _)
  | i :: more, ks, h => by
    simp only [laneKeysOf] at h
    cases hi : key i with
    | none => simp [hi] at h
    | some k0 =>
      cases hr : laneKeysOf key more with
      | none => simp [hi, hr] at h
      | some rest =>
        simp only [hi, hr, Option.some.injEq] at h
        subst h
        intro k hk
        cases k with
        | zero => simpa using hi
        | succ k => simpa using laneKeysOf_spec hr k (by simpa using hk)

/-- With `m` registers, the word in lane `i` of the `k`-th is the unknown of number `m * i + k` among the new ones. -/
theorem lane_index {m i k : Nat} (hi : i < 16) (hk : k < m) : m * i + k < 16 * m := by
  have := Nat.mul_le_mul_left m (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at this
  omega

theorem lane_mod {m i k : Nat} (hk : k < m) : (m * i + k) % m = k := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk]

theorem lane_div {m i k : Nat} (hk : k < m) : (m * i + k) / m = i := by
  rw [Nat.mul_add_div (by omega : m > 0), Nat.div_eq_of_lt hk, Nat.add_zero]

/-! ## The general state, with what the place says of vector registers -/

/-- The unknowns with those of a place's lanes given the words the machine's vector registers hold: with `m`
registers, the unknown `n + m * i + k` is the word in lane `i` of the `k`-th of them. -/
def laneRho (ρ : Nat → Int) (n : Nat) (regs : List Nat) (st : State) : Nat → Int := fun u =>
  if n ≤ u ∧ u < n + 16 * regs.length then (st.vec (regs.getD ((u - n) % regs.length) 0) ((u - n) / regs.length) : Int) else ρ u

theorem laneRho_agree (ρ : Nat → Int) (n : Nat) (regs : List Nat) (st : State) : Agree n ρ (laneRho ρ n regs st) := by
  intro u hu
  show ρ u = if n ≤ u ∧ u < n + 16 * regs.length then _ else ρ u
  rw [if_neg (by omega)]

theorem laneRho_new {ρ : Nat → Int} {n : Nat} {regs : List Nat} {st : State} {i k : Nat} (hi : i < 16) (hk : k < regs.length) :
    laneRho ρ n regs st (n + (regs.length * i + k)) = (st.vec (regs.getD k 0) i : Int) := by
  have h1 := lane_index hi hk
  show (if n ≤ n + (regs.length * i + k) ∧ n + (regs.length * i + k) < n + 16 * regs.length then _ else _) = _
  rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left, lane_mod hk, lane_div hk]

section
variable {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {g : Sym} {st : State}

/-- More known of vector registers and of numbers that are no rows: what the state held stays so, where
what is added is so. -/
theorem Carried.vecKnown (H : Holds ctx s0 ρ g st) (wf : WF g) (vec : List (Nat × List Nat)) (known : List Known)
    (hv : ∀ x ids, vec.lookup x = some ids → ids.length = 16 ∧ (∀ i ∈ ids, i < g.terms.length) ∧
      ∀ k, k < ids.length → st.vec x k = den (inpOf ctx s0) ρ g.terms (ids.getD k 0))
    (hk : ∀ k ∈ known, k.wf g.nvars g.terms.length ∧ k.holds ctx s0 ρ g.terms) :
    Carried ctx s0 ρ g ρ { g with vec := vec ++ g.vec, known := known ++ g.known } st := by
  refine ⟨Agree.refl _ _, Nat.le_refl _, ?_, ?_⟩
  · exact {
      range := H.range
      entry := H.entry, data := H.data, reg := H.reg, small := H.small, zf := H.zf, cf := H.cf, frame := H.frame, facts := H.facts,
      bytes := H.bytes, spec := H.spec, mem := H.mem, wrote := H.wrote,
      words := ⟨fun x ids hx k hk' => (lookup_append_or hx).elim (fun h => (hv x ids h).2.2 k hk') (fun h => H.words.vec x ids h k hk'),
                H.words.intact, H.words.wrote, H.words.spill⟩,
      known := fun k m => (List.mem_append.mp m).elim (fun m => (hk k m).2) (H.known k) }
  · exact {
      range := wf.range
      base := wf.base, reg := wf.reg, zf := wf.zf, cf := wf.cf, frame := wf.frame, facts := wf.facts, bytes := wf.bytes,
      spec := wf.spec, wrote := wf.wrote,
      words := ⟨wf.words.table, wf.words.atoms,
                fun x ids hx => (lookup_append_or hx).elim (fun h => ⟨Or.inr (hv x ids h).1, (hv x ids h).2.1⟩) (wf.words.vec x ids),
                wf.words.rotrs, wf.words.wrote, wf.words.spill⟩,
      known := fun k m => (List.mem_append.mp m).elim (fun m => (hk k m).1) (wf.known k) }

/-- What a place says of vector registers, taken as known of the general state: where the definition, used
with each lane's keys, is the list of the words the machine's registers hold in that lane, the new unknowns
can be those words, and what the state then holds is so. -/
theorem withLanes_carried (H : Holds ctx s0 ρ g st) (wf : WF g) (L : PlaceLanes) (keys : List (List Key))
    (hkeys : ∀ i, i < 16 → (∀ k ∈ keys.getD i [], k.wf g.nvars g.terms.length) ∧
      ∃ d, findDef ctx.defs L.f = some d ∧ d.params.length = (keys.getD i []).length ∧
        Value ctx.defs (d.params.zip ((keys.getD i []).map (Key.val ctx s0 ρ g.terms))) d.body
          (.list (L.regs.map fun r => Val.word (st.vec r i))))
    (hsmall : ∀ i, i < 16 → ∀ r ∈ L.regs, st.vec r i < W32) :
    ∃ ρ', Carried ctx s0 ρ g ρ' (g.withLanes L keys) st := by
  have ag := laneRho_agree ρ g.nvars L.regs st
  -- the unknowns
  have c1 := Carried.unknowns H wf (16 * L.regs.length) ag
  -- the terms of the unknowns
  obtain ⟨e, ok, len, lt, dn⟩ := termsOf_step (mk := wAtom) (val := fun r => (ev (laneRho ρ g.nvars L.regs st) r % W32i).toNat)
    (inp := inpOf ctx s0) (ρ := laneRho ρ g.nvars L.regs st) (nv := g.nvars + 16 * L.regs.length) (T0 := g.terms)
    ((List.range (16 * L.regs.length)).map fun u => Lin.var (g.nvars + u)) g.tab
    (fun r mr T _ ok => wAtom_step ok (by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp mr
      have := List.mem_range.mp hu
      exact bounded_var (by omega)))
    (Ext.refl _) c1.wf.words.ok
  have c2 := Carried.terms c1.holds c1.wf e ok
  have len' : (termsOf wAtom ((List.range (16 * L.regs.length)).map fun u => Lin.var (g.nvars + u)) g.tab).1.length = 16 * L.regs.length := by
    rw [len]; simp
  -- each new term is the word the machine's register holds
  have dterm : ∀ i k, i < 16 → k < L.regs.length →
      den (inpOf ctx s0) (laneRho ρ g.nvars L.regs st)
        (termsOf wAtom ((List.range (16 * L.regs.length)).map fun u => Lin.var (g.nvars + u)) g.tab).2.list
        ((termsOf wAtom ((List.range (16 * L.regs.length)).map fun u => Lin.var (g.nvars + u)) g.tab).1.getD (L.regs.length * i + k) 0) =
      st.vec (L.regs.getD k 0) i := by
    intro i k hi hk
    have hlt := lane_index hi hk
    have := dn (L.regs.length * i + k) (by simpa using hlt)
    simp only [List.getElem_map, List.getElem_range, ev_var] at this
    rw [this, laneRho_new hi hk]
    have sm : st.vec (L.regs.getD k 0) i < W32 := hsmall i hi _ (by rw [getD_index hk]; exact List.getElem_mem hk)
    unfold W32 at sm
    unfold W32i
    omega
  have tlt : ∀ i k, i < 16 → k < L.regs.length →
      (termsOf wAtom ((List.range (16 * L.regs.length)).map fun u => Lin.var (g.nvars + u)) g.tab).1.getD (L.regs.length * i + k) 0 <
      (termsOf wAtom ((List.range (16 * L.regs.length)).map fun u => Lin.var (g.nvars + u)) g.tab).2.list.length := by
    intro i k hi hk
    have hlt := lane_index hi hk
    rw [← len'] at hlt
    rw [getD_index hlt]
    exact lt _ (List.getElem_mem hlt)
  -- the registers, and what the definition is known to give
  have c3 := Carried.vecKnown c2.holds c2.wf
    ((List.range L.regs.length).map fun k => (L.regs.getD k 0, (List.range 16).map fun i =>
      (termsOf wAtom ((List.range (16 * L.regs.length)).map fun u => Lin.var (g.nvars + u)) g.tab).1.getD (L.regs.length * i + k) 0))
    ((List.range 16).map fun i => Known.held L.f (keys.getD i []) ((List.range L.regs.length).map fun k =>
      (termsOf wAtom ((List.range (16 * L.regs.length)).map fun u => Lin.var (g.nvars + u)) g.tab).1.getD (L.regs.length * i + k) 0))
    (by
      intro x ids hx
      obtain ⟨k, mk, rfl, rfl⟩ := lookup_map_mem _ _ hx
      have hk := List.mem_range.mp mk
      refine ⟨by simp, ?_, ?_⟩
      · intro id mid
        obtain ⟨i, mi, rfl⟩ := List.mem_map.mp mid
        exact tlt i k (List.mem_range.mp mi) hk
      · intro j hj
        have hj' : j < 16 := by simpa using hj
        rw [getD_index hj, List.getElem_map, List.getElem_range]
        exact (dterm j k hj' hk).symm)
    (by
      intro kn mkn
      obtain ⟨i, mi, rfl⟩ := List.mem_map.mp mkn
      have hi := List.mem_range.mp mi
      obtain ⟨kwf, d, hd, hlen, val⟩ := hkeys i hi
      have le : g.nvars ≤ g.nvars + 16 * L.regs.length := Nat.le_add_right _ _
      constructor
      · refine ⟨(Known.wf_mono le e.le (show (Known.held L.f (keys.getD i []) []).wf g.nvars g.terms.length from ⟨kwf, fun _ m => nomatch m⟩)).1, ?_⟩
        intro id mid
        obtain ⟨k, mk, rfl⟩ := List.mem_map.mp mid
        exact tlt i k hi (List.mem_range.mp mk)
      · refine ⟨d, hd, hlen, ?_⟩
        have ekeys : (keys.getD i []).map (Key.val ctx s0 (laneRho ρ g.nvars L.regs st)
            (termsOf wAtom ((List.range (16 * L.regs.length)).map fun u => Lin.var (g.nvars + u)) g.tab).2.list) =
            (keys.getD i []).map (Key.val ctx s0 ρ g.terms) :=
          List.map_congr_left fun k mk => Key.val_mono (kwf k mk) ag wf.words.table wf.words.atoms e
        have ewords : ((List.range L.regs.length).map fun k =>
              (termsOf wAtom ((List.range (16 * L.regs.length)).map fun u => Lin.var (g.nvars + u)) g.tab).1.getD (L.regs.length * i + k) 0).map
              (fun id => Val.word (den (inpOf ctx s0) (laneRho ρ g.nvars L.regs st)
                (termsOf wAtom ((List.range (16 * L.regs.length)).map fun u => Lin.var (g.nvars + u)) g.tab).2.list id)) =
            L.regs.map fun r => Val.word (st.vec r i) := by
          apply List.ext_getElem
          · simp
          · intro k h1 h2
            have hk : k < L.regs.length := by simpa using h2
            simp only [List.getElem_map, List.getElem_range]
            rw [dterm i k hi hk, getD_index hk]
        show Value ctx.defs _ d.body _
        rw [ekeys, ewords]
        exact val)
  exact ⟨laneRho ρ g.nvars L.regs st, c1.then (c2.then c3)⟩

/-- The keys of a lane's things stand for the values of those things at the place. -/
theorem laneKey_den {p : Program} (E : Setting ctx p s0) (pl : Place) (H : Holds ctx s0 ρ g st) (wf : WF g)
    (hn : ∀ nr ∈ pl.names, nr.2 < 16) {L : PlaceLanes} {i : Nat} {keys : List Key}
    (h : laneKey ctx g.tab.find (placeW ctx pl g) g L i = some keys) :
    (∀ k ∈ keys, k.wf g.nvars g.terms.length) ∧
    ∃ F, evalList (evalSpec ctx.defs F ((L.x, Val.int (i : Int)) :: placeValsW ctx pl s0 st)) L.args =
      some (keys.map (Key.val ctx s0 ρ g.terms)) := by
  unfold laneKey at h
  cases hw : wevalList (weval ctx g.tab.find g WFUEL ((L.x, .int i) :: placeW ctx pl g)) L.args with
  | none => simp [hw] at h
  | some vs =>
    cases hk : flatKeys g.tab.find vs with
    | none => simp [hw, hk] at h
    | some keys' =>
      simp only [hw, hk] at h
      split at h
      next hok =>
        injection h with h
        subst h
        obtain ⟨B, hB⟩ := held_bound H
        obtain ⟨as, el, dl⟩ := wevalList_sound
          (ev' := evalSpec ctx.defs (WFUEL + B) ((L.x, Val.int (i : Int)) :: placeValsW ctx pl s0 st))
          (fun e v hv => weval_sound H wf hB WFUEL ((L.x, .int i) :: placeW ctx pl g)
            ((L.x, Val.int (i : Int)) :: placeValsW ctx pl s0 st) e v hv ⟨rfl, WDen.int i, placeW_den E pl H hn⟩) L.args vs hw
        refine ⟨fun k mk => Key.ok_wf (List.all_eq_true.mp hok k mk), WFUEL + B, ?_⟩
        rw [el, flatKeys_den wf dl hk]
      next => cases h

/-- What a place says of vector registers, taken as known of the general state: what the state then holds is
so, of every state of the machine of which the place says it. -/
theorem supposeLanes_sound {p : Program} (E : Setting ctx p s0) (pl : Place) (hn : ∀ nr ∈ pl.names, nr.2 < 16)
    {g' : Sym} {L : PlaceLanes} {items rest : Items}
    (h : supposeLanes ctx pl g L items = .ok (g', rest)) (H : Holds ctx s0 ρ g st) (wf : WF g)
    (says : ∀ i, i < 16 → LaneSays ctx pl s0 st L i) :
    ∃ ρ', Carried ctx s0 ρ g ρ' g' st := by
  unfold supposeLanes at h
  split at h
  next => exact (refuse_ok h).elim
  next hf =>
    have hlen : (L.f == "len") = false := by
      cases c : (L.f == "len") with
      | true => exact absurd (by simp [c]) hf
      | false => rfl
    have hown : own.contains L.f = false := by
      cases c : own.contains L.f with
      | true => exact absurd (by rw [c, Bool.or_true]) hf
      | false => rfl
    cases hks : laneKeysOf (laneKey ctx g.tab.find (placeW ctx pl g) g L) (List.range 16) with
    | none => simp only [hks] at h; exact (refuse_ok h).elim
    | some keys =>
      simp only [hks] at h
      have hp := V.pure_ok h
      injection hp with e1 _
      subst e1
      refine withLanes_carried H wf L keys ?_ (fun i hi => (says i hi).1)
      intro i hi
      have hkey := laneKeysOf_spec hks i (by simpa using hi)
      rw [List.getElem_range] at hkey
      obtain ⟨kwf, F, hF⟩ := laneKey_den E pl H wf hn hkey
      obtain ⟨d, as, fuel, hd, hargs, hlen', hbody⟩ := Value.call_inv hlen hown (says i hi).2
      have e1 := evalList_mono (fun a v hv => evalSpec_mono ctx.defs F hv (max F fuel) (Nat.le_max_left _ _)) L.args hF
      have e2 := evalList_mono (fun a v hv => evalSpec_mono ctx.defs fuel hv (max F fuel) (Nat.le_max_right _ _)) L.args hargs
      rw [e1] at e2
      injection e2 with e2
      subst e2
      exact ⟨kwf, d, hd, by simpa using hlen', fuel, hbody⟩

theorem supposeLanes_all {p : Program} (E : Setting ctx p s0) (pl : Place) (hn : ∀ nr ∈ pl.names, nr.2 < 16) :
    ∀ (lanes : List PlaceLanes) {g g' : Sym} {items rest : Items} {ρ : Nat → Int},
    fold (supposeLanes ctx pl) g lanes items = .ok (g', rest) → Holds ctx s0 ρ g st → WF g →
    (∀ L ∈ lanes, ∀ i, i < 16 → LaneSays ctx pl s0 st L i) → ∃ ρ', Carried ctx s0 ρ g ρ' g' st
  | [], g, g', items, rest, ρ, h, H, wf, _ => by
    simp only [fold] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨ρ, Carried.here H wf⟩
  | L :: more, g, g', items, rest, ρ, h, H, wf, says => by
    simp only [fold] at h
    obtain ⟨g1, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨ρ1, c1⟩ := supposeLanes_sound E pl hn e1 H wf (says L (List.mem_cons_self ..))
    obtain ⟨ρ2, c2⟩ := supposeLanes_all E pl hn more h c1.holds c1.wf (fun L' m => says L' (List.mem_cons_of_mem _ m))
    exact ⟨ρ2, c1.then c2⟩

/-! ### What a place says of cells of the frame -/

theorem eachSome_spec {f : Nat → Option Nat} : ∀ {l ids : List Nat}, eachSome f l = some ids →
    ids.length = l.length ∧ ∀ k (hk : k < l.length), f l[k] = some (ids.getD k 0)
  | [], ids, h => by
    simp only [eachSome, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | i :: more, ids, h => by
    simp only [eachSome] at h
    cases hi : f i with
    | none => simp [hi] at h
    | some a =>
      cases hr : eachSome f more with
      | none => simp [hi, hr] at h
      | some rest =>
        simp only [hi, hr, Option.some.injEq] at h
        subst h
        obtain ⟨len, each⟩ := eachSome_spec hr
        refine ⟨by simp [len], ?_⟩
        intro k hk
        cases k with
        | zero => simpa using hi
        | succ k => simpa using each k (by simpa using hk)

/-- The terms `cellIds` gives are sixteen, and each is the term, of the table, of the word the place's
expression gives for that word's number. -/
theorem cellIds_spec {s : Sym} {look : Node → Option Nat} {env : List (String × WVal)} {C : PlaceCell} {ids : List Nat}
    (h : cellIds ctx look env s C = some ids) :
    ids.length = 16 ∧ ∀ i : Nat, i < 16 → ∃ xs, weval ctx look s WFUEL ((C.x, .int i) :: env) C.e = some (.word xs) ∧
      idOf look xs = some (ids.getD i 0) ∧ ids.getD i 0 < s.terms.length := by
  unfold cellIds at h
  obtain ⟨len, each⟩ := eachSome_spec h
  refine ⟨by simpa using len, ?_⟩
  intro i hi
  have e := each i (by simpa using hi)
  rw [List.getElem_range] at e
  cases hw : weval ctx look s WFUEL ((C.x, .int i) :: env) C.e with
  | none => simp [hw] at e
  | some v =>
    cases v with
    | word xs =>
      simp only [hw] at e
      cases hid : idOf look xs with
      | none => simp [hid] at e
      | some a =>
        simp only [hid, Option.filter] at e
        split at e
        next hlt =>
          injection e with e
          subst e
          exact ⟨xs, rfl, hid, by simpa using hlt⟩
        next => cases e
    | _ => simp [hw] at e

/-- Where the cell lies: `cellRow` is how far it is from where the stack pointer was at entry. -/
theorem cellRow_eval {s : Sym} (H : Holds ctx s0 ρ s st) (C : PlaceCell) :
    (s0.reg RSP : Int) + ev ρ (cellRow s C) = ((st.reg RSP + C.off : Nat) : Int) := by
  have e1 := frameOffset_eval H (s.reg RSP)
  have e2 := H.reg RSP (by decide)
  simp only [cellRow, ev_add, ev_const, e1]
  omega

/-- What the verifier has shown of a cell of the frame is so of the machine's state. -/
theorem cellShown_sound {p : Program} {s : Sym} (E : Setting ctx p s0) (pl : Place) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hn : ∀ nr ∈ pl.names, nr.2 < 16) {C : PlaceCell} (h : cellShown ctx pl s C = true) : CellSays ctx pl s0 st C := by
  intro i hi
  unfold cellShown at h
  cases hids : cellIds ctx s.tab.find (placeW ctx pl s) s C with
  | none => simp [hids] at h
  | some ids =>
    cases hf : s.spill.find? (fun (o, _) => o == cellRow s C) with
    | none => simp [hids, hf] at h
    | some found =>
      obtain ⟨o, held⟩ := found
      simp only [hids, hf, beq_iff_eq] at h
      subst h
      have hs : (o, ids) ∈ s.spill := List.mem_of_find?_eq_some hf
      have heq : o = cellRow s C := by simpa only [beq_iff_eq] using List.find?_some hf
      subst heq
      obtain ⟨len, each⟩ := cellIds_spec hids
      obtain ⟨xs, hw, hid, _⟩ := each i hi
      obtain ⟨B, hB⟩ := held_bound H
      obtain ⟨a, ea, da⟩ := weval_sound H wf hB WFUEL ((C.x, .int i) :: placeW ctx pl s)
        ((C.x, Val.int (i : Int)) :: placeValsW ctx pl s0 st) _ _ hw ⟨rfl, WDen.int i, placeW_den E pl H hn⟩
      cases da
      have ew := (H.words.spill _ ids hs).2 i (by omega)
      rw [cellRow_eval H C, Int.toNat_natCast] at ew
      refine ⟨WFUEL + B, ?_⟩
      rw [ea, ew, idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hid]

/-- What a place says of a cell of the frame, taken as known of the general state: what the state then
holds is so, of every state of the machine of which the place says it. -/
theorem supposeCell_sound {p : Program} (E : Setting ctx p s0) (pl : Place) (hn : ∀ nr ∈ pl.names, nr.2 < 16)
    {g g' : Sym} {C : PlaceCell} {items rest : Items}
    (h : supposeCell ctx pl g C items = .ok (g', rest)) (H : Holds ctx s0 ρ g st) (wf : WF g)
    (says : CellSays ctx pl s0 st C) : Carried ctx s0 ρ g ρ g' st := by
  unfold supposeCell at h
  cases hids : cellIds ctx g.tab.find (placeW ctx pl g) g C with
  | none => simp only [hids] at h; exact (refuse_ok h).elim
  | some ids =>
    simp only [hids] at h
    have hp := V.pure_ok h
    injection hp with e1 _
    subst e1
    obtain ⟨len, each⟩ := cellIds_spec hids
    obtain ⟨B, hB⟩ := held_bound H
    have addr := cellRow_eval H C
    have pos : 0 ≤ (s0.reg RSP : Int) + ev ρ (cellRow g C) := by rw [addr]; omega
    have words : ∀ k, k < ids.length →
        load st.mem (((s0.reg RSP : Int) + ev ρ (cellRow g C)).toNat + 4 * k) 4 = den (inpOf ctx s0) ρ g.terms (ids.getD k 0) := by
      intro k hk
      obtain ⟨xs, hw, hid, _⟩ := each k (by omega)
      obtain ⟨a, ea, da⟩ := weval_sound H wf hB WFUEL ((C.x, .int k) :: placeW ctx pl g)
        ((C.x, Val.int (k : Int)) :: placeValsW ctx pl s0 st) _ _ hw ⟨rfl, WDen.int k, placeW_den E pl H hn⟩
      cases da
      obtain ⟨fuel, hv⟩ := says k (by omega)
      have u := Value.unique ⟨_, ea⟩ ⟨fuel, hv⟩
      injection u with u
      rw [addr, Int.toNat_natCast, ← u, idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hid]
    have bd : bounded g.nvars (cellRow g C) :=
      bounded_add (bounded_sub (wf.reg RSP (by decide)) (bounded_var (Nat.lt_of_lt_of_le (by decide : RSP < 17) wf.base)))
        (bounded_const _ _)
    have lt : ∀ i ∈ ids, i < g.terms.length := by
      intro i mi
      obtain ⟨k, hk, ek⟩ := List.getElem_of_mem mi
      obtain ⟨_, _, _, l⟩ := each k (by omega)
      have eg : ids.getD k 0 = i := by simp [List.getD, List.getElem?_eq_getElem hk, ek]
      rw [eg] at l; exact l
    refine ⟨Agree.refl _ _, Nat.le_refl _, ?_, ?_⟩
    · exact {
        range := H.range
        entry := H.entry, data := H.data, reg := H.reg, small := H.small, zf := H.zf, cf := H.cf, frame := H.frame, facts := H.facts,
        bytes := H.bytes, spec := H.spec, mem := H.mem, wrote := H.wrote, known := H.known,
        words := ⟨H.words.vec, H.words.intact, H.words.wrote, fun off ids' m =>
          (List.mem_cons.mp m).elim
            (fun e => by
              injection e with eo ei
              subst eo; subst ei
              exact ⟨pos, words⟩)
            (H.words.spill off ids')⟩ }
    · exact {
        range := wf.range
        base := wf.base, reg := wf.reg, zf := wf.zf, cf := wf.cf, frame := wf.frame, facts := wf.facts, bytes := wf.bytes,
        spec := wf.spec, wrote := wf.wrote, known := wf.known,
        words := ⟨wf.words.table, wf.words.atoms, wf.words.vec, wf.words.rotrs, wf.words.wrote, fun off ids' m =>
          (List.mem_cons.mp m).elim
            (fun e => by
              injection e with eo ei
              subst eo; subst ei
              exact ⟨bd, len, lt⟩)
            (wf.words.spill off ids')⟩ }

theorem supposeCells_all {p : Program} (E : Setting ctx p s0) (pl : Place) (hn : ∀ nr ∈ pl.names, nr.2 < 16) :
    ∀ (cells : List PlaceCell) {g g' : Sym} {items rest : Items},
    fold (supposeCell ctx pl) g cells items = .ok (g', rest) → Holds ctx s0 ρ g st → WF g →
    (∀ C ∈ cells, CellSays ctx pl s0 st C) → Carried ctx s0 ρ g ρ g' st
  | [], g, g', items, rest, h, H, wf, _ => by
    simp only [fold] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact Carried.here H wf
  | C :: more, g, g', items, rest, h, H, wf, says => by
    simp only [fold] at h
    obtain ⟨g1, r1, e1, h⟩ := V.bind_ok h
    have c1 := supposeCell_sound E pl hn e1 H wf (says C (List.mem_cons_self ..))
    exact c1.then (supposeCells_all E pl hn more h c1.holds c1.wf (fun C' m => says C' (List.mem_cons_of_mem _ m)))

end

/-! ## A place, and the general state -/

/-- What a place says a loop has written, of a state of the machine there: the run is one given to write;
the definition is a list made thing by thing, of no more things than the run has places; and each place
of the run from `lo` on holds the list's thing there. -/
def RangeSays (ctx : Ctx) (pl : Place) (s0 st : State) : Prop :=
  ∀ run lo f args, pl.wrote = some (run, lo, f, args) →
    ∃ w r n a vs params x b hi, findOutNamed run ctx.contract.outs 0 = some (w, n) ∧ ctx.contract.outs[w]? = some (run, r, n) ∧
      Value ctx.defs (placeVals ctx pl s0 st) lo (.int a) ∧ 0 ≤ a ∧
      Values ctx.defs (placeVals ctx pl s0 st) args vs ∧
      eachOf ctx f vs.length = some (params, x, b, hi) ∧ hi ≤ n ∧
      ∀ j : Nat, a ≤ j → j < hi → Value ctx.defs ((x, .int (j : Int)) :: params.zip vs) b (.int (st.mem (s0.reg r + j)))

theorem Holds.setRange (H : Holds ctx s0 ρ s st) (rg : RangeF) (h : RangeHolds ctx s0 ρ rg st.mem) :
    Holds ctx s0 ρ { s with range := some rg } st :=
  ⟨H.entry, H.data, H.reg, H.small, H.zf, H.cf, H.frame, H.facts, H.bytes, H.spec, H.mem, H.wrote, H.words, H.known,
   fun rg' e => by injection e with e; subst e; exact h⟩

theorem WF.setRange (wf : WF s) (rg : RangeF) (bl : bounded s.nvars rg.lo) (ba : ∀ v ∈ rg.args, v.bounded s.nvars) :
    WF { s with range := some rg } :=
  ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.facts, wf.bytes, wf.spec, wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known,
   fun rg' e => by injection e with e; subst e; exact ⟨bl, ba⟩⟩

/-- What the verifier has gone through of what a place says a loop has written is so of the machine's state. -/
theorem rangeShown_sound {p : Program} (E : Setting ctx p s0) (pl : Place) (hn : ∀ nr ∈ pl.names, nr.2 < 16)
    {s' : Sym} {got : Option RangeF} {items rest : Items}
    (h : rangeShown ctx pl s items = .ok ((got, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ RangeSays ctx pl s0 st := by
  unfold rangeShown at h
  cases hpw : pl.wrote with
  | none =>
    simp only [hpw] at h
    obtain ⟨_, rfl⟩ := pure_pair h
    exact ⟨ρ, Carried.here H wf, fun _ _ _ _ e => by rw [hpw] at e; cases e⟩
  | some q =>
    obtain ⟨run, lo, f, args⟩ := q
    simp only [hpw] at h
    cases hfo : findOutNamed run ctx.contract.outs 0 with
    | none => simp only [hfo] at h; exact (refuse_ok h).elim
    | some wn =>
      obtain ⟨w, n⟩ := wn
      simp only [hfo] at h
      obtain ⟨r, _, hw⟩ := findOutNamed_spec hfo
      simp only [Nat.sub_zero] at hw
      have envb : EnvB s.nvars (placeEnv ctx pl s.reg) := placeEnv_bounded pl wf hn
      have env0 := semEnv_placeEnv (ctx := ctx) pl H.entry H.reg hn
      obtain ⟨⟨rlo, s1⟩, r1, e1, h⟩ := V.bind_ok h
      obtain ⟨⟨L, s2⟩, r2, e2, h⟩ := V.bind_ok h
      obtain ⟨⟨res, s3⟩, r3, e3, h⟩ := V.bind_ok h
      obtain ⟨ρ1, c1, sem1, bd1⟩ := seval_sound E _ lo e1 H wf envb
      obtain ⟨ρ2, c2, vlo, bL⟩ := numberV_sound (opener_sound E DEEP) c1.holds c1.wf e2 sem1 bd1
      have c12 := c1.then c2
      obtain ⟨ρ3, c3, sem3, bd3⟩ := seval_sound E _ args e3 c2.holds c2.wf (envb.mono c12.mono)
      have c13 := c12.then c3
      cases res with
      | val _ => exact (refuse_ok h).elim
      | tail _ => exact (refuse_ok h).elim
      | list vs =>
        simp only at h
        cases heach : eachOf ctx f vs.length with
        | none => simp only [heach] at h; exact (refuse_ok h).elim
        | some q =>
          obtain ⟨params, x, b, hi⟩ := q
          simp only [heach] at h
          split at h
          next => exact (refuse_ok h).elim
          next hnhi =>
          obtain ⟨_, r4, g1, h⟩ := V.bind_ok h
          have g1 : 0 ≤ ev ρ3 L := entail_sound g1 ρ3 c3.holds.facts
          cases hk : Lin.isConst (Lin.sub (rangeBase s3 w f vs hi) L) with
          | none => simp only [hk] at h; exact (refuse_ok h).elim
          | some k =>
            simp only [hk] at h
            split at h
            next => exact (refuse_ok h).elim
            next hkk =>
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt] at hkk
            obtain ⟨s4, r5, e5, h⟩ := V.bind_ok h
            obtain ⟨_, rfl⟩ := pure_pair h
            have bvs : ∀ v ∈ vs, v.bounded s3.nvars := bd3
            obtain ⟨ρ4, c4, fill⟩ := filled_sound E hw k.toNat 0 e5 c3.holds c3.wf (EnvB.zip params vs bvs) (bounded_mono c3.mono bL)
            refine ⟨ρ4, c13.then c4, ?_⟩
            intro run' lo' f' args' e
            rw [hpw] at e
            injection e with e
            injection e with e1 e; injection e with e2 e; injection e with e3 e4
            subst e1 e2 e3 e4
            have eL : ev ρ2 L = ev ρ4 L := ev_agree bL (c3.then c4).agree
            have same : vs.map (semv ctx s0 ρ3) = vs.map (semv ctx s0 ρ4) :=
              List.map_congr_left fun v hv => semv_agree (bvs v hv) c4.agree
            have vlo' : Value ctx.defs (placeVals ctx pl s0 st) lo (.int (ev ρ4 L)) := by
              rw [← eL, ← env0, semEnv_agree envb c1.agree]; exact vlo
            have vargs : Values ctx.defs (placeVals ctx pl s0 st) args (vs.map (semv ctx s0 ρ4)) := by
              rw [← same, ← env0, semEnv_agree envb c13.agree]; exact sem3
            have g1' : 0 ≤ ev ρ4 L := by rw [← ev_agree (bounded_mono c3.mono bL) c4.agree]; exact g1
            refine ⟨w, r, n, ev ρ4 L, vs.map (semv ctx s0 ρ4), params, x, b, hi, hfo, hw, vlo', g1', vargs,
              by rw [List.length_map]; exact heach, by omega, ?_⟩
            intro j lej hj
            have ek := ev_isConst (ρ := ρ4) hk
            rw [ev_sub] at ek
            by_cases near : (j : Int) < ev ρ4 L + k
            · -- a place gone through just now
              have := fill (j - (ev ρ4 L).toNat) (by omega)
              have e1 : ev ρ4 L + ((0 + (j - (ev ρ4 L).toNat) : Nat) : Int) = (j : Int) := by omega
              rw [e1, semEnv_zip] at this
              simpa using this
            · -- a place held since an earlier coming
              unfold rangeBase at ek
              cases hr : s3.range with
              | none => rw [hr] at ek; simp only [ev_const] at ek; omega
              | some rg =>
                rw [hr] at ek
                simp only at ek
                split at ek
                next hsame =>
                  simp only [Bool.and_eq_true, beq_iff_eq] at hsame
                  obtain ⟨⟨hw', hf'⟩, hargs⟩ := hsame
                  obtain ⟨name', r', n', params', x', b', hi', q1, q2, q3, q4, q5⟩ :=
                    RangeHolds.agree (c3.wf.range rg hr).1 (c3.wf.range rg hr).2 c4.agree (c3.holds.range rg hr)
                  rw [hw', hw] at q1
                  injection q1 with q1; injection q1 with _ q1; injection q1 with q1 qn
                  subst q1 qn
                  rw [hf', hargs, heach] at q2
                  injection q2 with q2
                  injection q2 with p1 q2; injection q2 with p2 q2; injection q2 with p3 p4
                  subst p1 p2 p3 p4
                  have := q5 j (by omega) hj
                  rw [hargs] at this
                  exact this
                next => simp only [ev_const] at ek; omega


/-- What a place says a loop has written, taken as known in the place's general state: it is so there. -/
theorem supposeRange_sound {p : Program} (E : Setting ctx p s0) (pl : Place) (hn : ∀ nr ∈ pl.names, nr.2 < 16)
    {g' : Sym} {items rest : Items}
    (h : supposeRange ctx pl g items = .ok (g', rest)) (H : Holds ctx s0 ρ g st) (wf : WF g)
    (says : RangeSays ctx pl s0 st) : ∃ ρ', Carried ctx s0 ρ g ρ' g' st := by
  unfold supposeRange at h
  cases hpw : pl.wrote with
  | none =>
    simp only [hpw] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨ρ, Carried.here H wf⟩
  | some q =>
    obtain ⟨run, lo, f, args⟩ := q
    simp only [hpw] at h
    cases hfo : findOutNamed run ctx.contract.outs 0 with
    | none => simp only [hfo] at h; exact (refuse_ok h).elim
    | some wn =>
      obtain ⟨w, n⟩ := wn
      simp only [hfo] at h
      have envb : EnvB g.nvars (placeEnv ctx pl g.reg) := placeEnv_bounded pl wf hn
      have env0 := semEnv_placeEnv (ctx := ctx) pl H.entry H.reg hn
      obtain ⟨⟨rlo, g1⟩, r1, e1, h⟩ := V.bind_ok h
      obtain ⟨⟨L, g2⟩, r2, e2, h⟩ := V.bind_ok h
      obtain ⟨⟨res, g3⟩, r3, e3, h⟩ := V.bind_ok h
      obtain ⟨ρ1, c1, sem1, bd1⟩ := seval_sound E _ lo e1 H wf envb
      obtain ⟨ρ2, c2, vlo, bL⟩ := numberV_sound (opener_sound E DEEP) c1.holds c1.wf e2 sem1 bd1
      have c12 := c1.then c2
      obtain ⟨ρ3, c3, sem3, bd3⟩ := seval_sound E _ args e3 c2.holds c2.wf (envb.mono c12.mono)
      have c13 := c12.then c3
      cases res with
      | val _ => exact (refuse_ok h).elim
      | tail _ => exact (refuse_ok h).elim
      | list vs =>
        simp only at h
        have := V.pure_ok h
        injection this with h1 _
        subst h1
        have bvs : ∀ v ∈ vs, v.bounded g3.nvars := bd3
        obtain ⟨w', r, n', a, vsem, params, x, b, hi, hfo', hw, va, a0, vargs, heach, hin, hall⟩ := says run lo f args hpw
        rw [hfo] at hfo'
        injection hfo' with hfo'
        injection hfo' with hw' hn'
        subst hw' hn'
        have eL : ev ρ2 L = ev ρ3 L := ev_agree bL c3.agree
        have vlo' : Value ctx.defs (placeVals ctx pl s0 st) lo (.int (ev ρ3 L)) := by
          rw [← eL, ← env0, semEnv_agree envb c1.agree]; exact vlo
        have ea : a = ev ρ3 L := by
          have := Value.unique va vlo'
          injection this
        have vargs' : Values ctx.defs (placeVals ctx pl s0 st) args (vs.map (semv ctx s0 ρ3)) := by
          rw [← env0, semEnv_agree envb c13.agree]; exact sem3
        have evs : vsem = vs.map (semv ctx s0 ρ3) := Values.unique vargs vargs'
        subst evs
        rw [List.length_map] at heach
        refine ⟨ρ3, c13.agree, c13.mono, c3.holds.setRange ⟨w, L, f, vs⟩ ?_, c3.wf.setRange ⟨w, L, f, vs⟩ (bounded_mono c3.mono bL) bvs⟩
        exact ⟨run, r, n, params, x, b, hi, hw, heach, hin, by rw [← ea]; exact a0, fun j lej hj => hall j (by rw [ea]; exact lej) hj⟩

/-- What a place says of a state of the machine there, `first` being what the verifier held when a path
first came there and `ρs` what its unknowns then were: those unknowns are still what they were, the
registers kept and the frame are as `first` has them, memory outside the frame is as at entry, the
place's facts are so of what the named registers hold, and the vector registers hold, lane by lane, what
the place says of them. -/
structure AtPlace (ctx : Ctx) (pl : Place) (s0 : State) (first : Sym) (ρs ρ : Nat → Int) (st : State) : Prop where
  outer : Agree first.nvars ρs ρ
  entry : ∀ r, r < 16 → ρ r = s0.reg r
  data : ρ 16 = s0.data ∧ st.data = s0.data
  kept : ∀ r, r < 16 → pl.keep.contains r = true → (st.reg r : Int) = ev ρ (first.reg r)
  small : ∀ r, st.reg r < M64
  frame : ∀ o v, (o, v) ∈ first.frame →
    -(ctx.contract.stack : Int) ≤ o ∧ o + 8 ≤ 0 ∧ (load st.mem ((s0.reg RSP : Int) + o).toNat 8 : Int) = ev ρ v
  mem : ∀ a, ctx.contract.inFrame s0 a = false → ctx.contract.inOut s0 a = false → st.mem a = s0.mem a
  facts : ∀ e ∈ pl.facts, Asserts ctx.defs (placeVals ctx pl s0 st) e
  lanes : ∀ L ∈ pl.lanes, ∀ i, i < 16 → LaneSays ctx pl s0 st L i
  cells : ∀ C ∈ pl.cells, CellSays ctx pl s0 st C
  wrote : RangeSays ctx pl s0 st

theorem general_wf (pl : Place) {first : Sym} (wf : WF first) : WF (first.general pl) := by
  have le : first.nvars ≤ first.nvars + 16 := Nat.le_add_right _ _
  refine ⟨Nat.le_trans wf.base le, ?_, trivial, trivial, ?_, ?_,
          (fun v r o m => ⟨Nat.lt_of_lt_of_le (wf.bytes v r o m).1 le, bounded_mono le (wf.bytes v r o m).2⟩),
          (fun f m => SFact.bounded_mono le (wf.spec f m)), (fun _ _ _ m => nomatch m),
          ⟨wf.words.table, fun j r h => bounded_mono le (wf.words.atoms j r h), fun x ids h => by simp [Sym.general] at h,
           wf.words.rotrs, (fun w j i h => by simp [Sym.general] at h), fun _ _ h => nomatch h⟩,
          fun k m => Known.wf_mono le (Nat.le_refl _) (wf.known k m), fun _ h => nomatch h⟩
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
unknowns of before, when the path first came there, is so still. (What the place says of vector registers
is taken as known after this: `supposeLanes_all`.) -/
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
  have hdata : (fun k => if first.nvars ≤ k ∧ k < first.nvars + 16 then (st.reg (k - first.nvars) : Int) else ρ k) 16 = s0.data := by
    show (if first.nvars ≤ 16 ∧ 16 < first.nvars + 16 then (st.reg (16 - first.nvars) : Int) else ρ 16) = s0.data
    rw [if_neg (by omega)]
    exact A.data.1
  have Hg := Hf.agree wf (Agree.trans (Nat.le_refl _) A.outer ag)
  refine ⟨hentry, ⟨hdata, A.data.2⟩, ?_, A.small, trivial, trivial, ?_, ?_, Hg.bytes, Hg.spec, A.mem, (fun _ _ _ m => nomatch m),
    ⟨(fun x ids h => by simp [Sym.general] at h), (fun w m => by simp [Sym.general] at m),
     (fun w j i m => by simp [Sym.general] at m), fun _ _ h => nomatch h⟩,
    Hg.known, fun _ h => nomatch h⟩
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
    split at h
    next => exact (refuse_ok h).elim
    next hshown =>
    have shown : ∀ L ∈ pl.lanes, lanesShown ctx pl s1 L = true := by
      intro L mL
      have all : pl.lanes.all (lanesShown ctx pl s1) = true := by simpa using hshown
      exact List.all_eq_true.mp all L mL
    split at h
    next => exact (refuse_ok h).elim
    next hcells =>
    have cshown : ∀ C ∈ pl.cells, cellShown ctx pl s1 C = true := by
      intro C mC
      have all : pl.cells.all (cellShown ctx pl s1) = true := by simpa using hcells
      exact List.all_eq_true.mp all C mC
    obtain ⟨⟨got, s1b⟩, rb, eb, h⟩ := V.bind_ok h
    obtain ⟨g1, r2, e2, h⟩ := V.bind_ok h
    obtain ⟨gl, rl, el, h⟩ := V.bind_ok h
    obtain ⟨gc, rc, ec, h⟩ := V.bind_ok h
    obtain ⟨gr, rr, er, h⟩ := V.bind_ok h
    obtain ⟨⟨dres, g2⟩, r3, e3, h⟩ := V.bind_ok h
    have envb : EnvB s.nvars (placeEnv ctx pl s.reg) := placeEnv_bounded pl wf hnames
    obtain ⟨ρ1, c1', a1⟩ := establish_all E _ pl.facts e1 H wf envb
    obtain ⟨ρ1b, c1b, says⟩ := rangeShown_sound E pl hnames eb c1'.holds c1'.wf
    have c1 := c1'.then c1b
    have env1 : semEnv ctx s0 ρ1 (placeEnv ctx pl s.reg) = placeVals ctx pl s0 st := by
      rw [← semEnv_agree envb c1'.agree]
      exact semEnv_placeEnv pl H.entry H.reg hnames
    have first_at : AtPlace ctx pl s0 s1b ρ1b ρ1b st :=
      ⟨Agree.refl _ _, c1.holds.entry, c1.holds.data, fun r hr _ => c1.holds.reg r hr, c1.holds.small, c1.holds.frame, c1.holds.mem,
       fun e m => by rw [← env1]; exact a1 e m,
       fun L mL => lanesShown_sound E pl c1'.holds c1'.wf hnames (shown L mL),
       fun C mC => cellShown_sound E pl c1'.holds c1'.wf hnames (cshown C mC), says⟩
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
        have G : ∀ ρ' st', AtPlace ctx pl s0 s1b ρ1b ρ' st' →
            ∃ ρ'', Holds ctx s0 ρ'' g2 st' ∧ WF g2 ∧ s1b.nvars ≤ g2.nvars ∧ Agree s1b.nvars ρ' ρ'' ∧ bounded g2.nvars d' ∧ 0 ≤ ev ρ'' d' ∧
              Value ctx.defs (placeVals ctx pl s0 st') pl.decreases (.int (ev ρ'' d')) := by
          intro ρ' st' A
          have H0 := general_holds pl c1.wf c1.holds A
          have ag0 : Agree s1b.nvars ρ' (fun k => if s1b.nvars ≤ k ∧ k < s1b.nvars + 16 then (st'.reg (k - s1b.nvars) : Int) else ρ' k) := by
            intro k hk
            show ρ' k = if s1b.nvars ≤ k ∧ k < s1b.nvars + 16 then (st'.reg (k - s1b.nvars) : Int) else ρ' k
            rw [if_neg (by omega)]
          have w0 := general_wf pl c1.wf
          have envb0 : EnvB (s1b.general pl).nvars (placeEnv ctx pl (s1b.general pl).reg) := placeEnv_bounded pl w0 hnames
          have env0 := semEnv_placeEnv (ctx := ctx) pl H0.entry H0.reg hnames
          obtain ⟨ρa, ca⟩ := suppose_all E _ pl.facts e2 H0 w0 envb0 (fun e m => by rw [env0]; exact A.facts e m)
          obtain ⟨ρl, cl0⟩ := supposeLanes_all E pl hnames pl.lanes el ca.holds ca.wf A.lanes
          have cl' := cl0.then (supposeCells_all E pl hnames pl.cells ec cl0.holds cl0.wf A.cells)
          obtain ⟨ρr, cr⟩ := supposeRange_sound E pl hnames er cl'.holds cl'.wf A.wrote
          have cl := cl'.then cr
          obtain ⟨ρb, cb, sem, bd⟩ := seval_sound E _ pl.decreases e3 cl.holds cl.wf (envb0.mono (ca.then cl).mono)
          have env2 : semEnv ctx s0 ρb (placeEnv ctx pl (s1b.general pl).reg) = placeVals ctx pl s0 st' := by
            rw [← semEnv_agree envb0 (ca.then (cl.then cb)).agree]; exact env0
          rw [env2] at sem
          exact ⟨ρb, cb.holds, cb.wf, Nat.le_trans (Nat.le_add_right _ 16) (ca.then (cl.then cb)).mono,
                 Agree.trans (Nat.le_add_right _ 16) ag0 (ca.then (cl.then cb)).agree, bd, entail_sound e4 ρb cb.holds.facts, sem⟩
        obtain ⟨ρx, Hx, wg, leg, _, bdd, _, _⟩ := G ρ1b st first_at
        refine ⟨hnames, ρ1b, c1.agree, c1.mono, first_at, wg, leg, bdd, ?_⟩
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
    next =>
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
      split at h
      next => exact (refuse_ok h).elim
      next hshown =>
      have shown : ∀ L ∈ pl.lanes, lanesShown ctx pl s1 L = true := by
        intro L mL
        have all : pl.lanes.all (lanesShown ctx pl s1) = true := by simpa using hshown
        exact List.all_eq_true.mp all L mL
      split at h
      next => exact (refuse_ok h).elim
      next hcells =>
      have cshown : ∀ C ∈ pl.cells, cellShown ctx pl s1 C = true := by
        intro C mC
        have all : pl.cells.all (cellShown ctx pl s1) = true := by simpa using hcells
        exact List.all_eq_true.mp all C mC
      obtain ⟨⟨got, s1b⟩, rb, eb, h⟩ := V.bind_ok h
      obtain ⟨⟨dres, s2⟩, r2, e2, h⟩ := V.bind_ok h
      have envb : EnvB s.nvars (placeEnv ctx pl s.reg) := placeEnv_bounded pl wf hn
      have env0 := semEnv_placeEnv (ctx := ctx) pl H.entry H.reg hn
      obtain ⟨ρ1, c1', a1⟩ := establish_all E _ pl.facts e1 H wf envb
      obtain ⟨ρ1b, c1b, says⟩ := rangeShown_sound E pl hn eb c1'.holds c1'.wf
      have c1 := c1'.then c1b
      obtain ⟨ρ2, c2, sem, bd⟩ := seval_sound E _ pl.decreases e2 c1.holds c1.wf (envb.mono c1.mono)
      have env1 : semEnv ctx s0 ρ1 (placeEnv ctx pl s.reg) = placeVals ctx pl s0 st := by
        rw [← semEnv_agree envb c1'.agree]; exact env0
      have env2 : semEnv ctx s0 ρ2 (placeEnv ctx pl s.reg) = placeVals ctx pl s0 st := by
        rw [← semEnv_agree envb (c1.then c2).agree]; exact env0
      refine ⟨⟨Agree.refl _ _, H.entry, H.data, (fun r hr hk => by rw [← hkeep r hk]; exact H.reg r hr), H.small,
               (fun o v m => H.frame o v (hfr o v m)), H.mem, (fun e m => by rw [← env1]; exact a1 e m),
               fun L mL => lanesShown_sound E pl c1'.holds c1'.wf hn (shown L mL),
               fun C mC => cellShown_sound E pl c1'.holds c1'.wf hn (cshown C mC), says⟩, ?_⟩
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
