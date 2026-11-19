import SoundSpecW
/-!
# Why the verifier's yes is right, 7b: a call of a function that writes a run of words for its caller

The called function reads and writes one run of words and reads parts of runs of a fixed count; its
contract says the run then holds the bytes of the words a definition gives of its arguments (`symCallW` of
Core.lean). Here: what its contract asks is so of the state it starts in; what it may touch, this function
may touch; and of every state the contract lets it return in, what the verifier holds after the call is so:
each word of the run is the new unknown made for it, and the definition, used with what the function was
given, is those words.
-/
namespace Ode
open Arithmetic

/-! ## What the verifier looked up before the call -/

theorem writtenIds_spec {wroteW : List (Nat × Nat × Nat)} {w : Nat} : ∀ (count k : Nat) {ids : List Nat},
    writtenIds wroteW w count k = some ids → ids.length = count ∧ ∀ q, q < count → (w, k + q, ids.getD q 0) ∈ wroteW
  | 0, k, ids, h => by
    simp only [writtenIds, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun q hq => absurd hq (Nat.not_lt_zero _)⟩
  | count + 1, k, ids, h => by
    simp only [writtenIds] at h
    cases hf : wroteW.find? (fun e => e.1 == w && e.2.1 == k) <;> cases hr : writtenIds wroteW w count (k + 1) <;>
      simp only [hf, hr, reduceCtorEq, Option.some.injEq] at h
    rename_i e rest
    subst h
    obtain ⟨len, hm⟩ := writtenIds_spec count (k + 1) hr
    have he := List.find?_some hf
    have hmem := List.mem_of_find?_eq_some hf
    obtain ⟨e1, e2, e3⟩ := e
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨by simp [len], ?_⟩
    intro q hq
    cases q with
    | zero => simpa using hmem
    | succ q =>
      have := hm q (by omega)
      rw [show e2 + (q + 1) = e2 + 1 + q by omega]
      simpa using this

/-- The run a called function is given to read and write: one of this function's runs given to read and
write, whole, at the address the register holds, with no single byte of it written and every word known. -/
theorem callRun_spec {ctx : Ctx} {s : Sym} {r n w : Nat} {ids : List Nat} (h : callRun ctx s r n = some (w, ids)) :
    ∃ x b, ctx.contract.outs[w]? = some (x, b, n) ∧ (x, b, n) ∈ ctx.contract.inouts ∧ n % 4 = 0 ∧
      (∀ ρ : Nat → Int, ev ρ (s.reg r) = ρ b) ∧ (∀ e ∈ s.wrote, e.1 ≠ w) ∧ writtenIds s.wroteW w (n / 4) 0 = some ids := by
  unfold callRun at h
  cases hf : findOut (s.reg r) ctx.contract.outs 0 with
  | none => simp [hf] at h
  | some wh =>
    obtain ⟨w', o, name, base, n', rfl, _, hl, ho⟩ := findOut_spec hf
    simp only [Nat.sub_zero] at hl
    simp only [hf, hl] at h
    split at h
    next hc =>
      obtain ⟨c0, cn, c4, ci, cw⟩ := hc
      cases hwi : writtenIds s.wroteW w' (n / 4) 0 with
      | none => simp [hwi] at h
      | some ids' =>
        simp only [hwi, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst cn
        refine ⟨name, base, hl, by simpa using ci, c4, ?_, ?_, hwi⟩
        · intro ρ
          have := ev_isConst (ρ := ρ) c0
          rw [ho, ev_sub, ev_var] at this
          omega
        · intro e me
          have := List.all_eq_true.mp cw e me
          simpa using this
    next => simp at h

/-- The part of a run of a fixed count a called function is given to read: it lies in one of this
function's runs of a fixed count, at the address the register holds. -/
theorem fixedPart_spec {ctx : Ctx} {s : Sym} {r n j b c : Nat} (h : fixedPart ctx s r n = some (j, b, c)) :
    ∃ x n0, ctx.contract.fixeds[j]? = some (x, b, n0) ∧ c + n ≤ n0 ∧ ∀ ρ : Nat → Int, ev ρ (s.reg r) = ρ b + c := by
  unfold fixedPart at h
  cases hf : findOut (s.reg r) ctx.contract.fixeds 0 with
  | none => simp [hf] at h
  | some wh =>
    obtain ⟨j', o, name, base, n0, rfl, _, hl, ho⟩ := findOut_spec hf
    simp only [Nat.sub_zero] at hl
    simp only [hf] at h
    cases hc : Lin.isConst o with
    | none => simp [hc] at h
    | some cst =>
      simp only [hc, hl] at h
      split at h
      next hcond =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨name, n0, hl, by omega, fun ρ => ?_⟩
        have := ev_isConst (ρ := ρ) hc
        rw [ho, ev_sub, ev_var] at this
        omega
      next => simp at h

/-- A key the verifier has looked at speaks only of unknowns in use and of terms of the table. -/
theorem Key.ok_wf {n t : Nat} {k : Key} (h : k.ok n t = true) : k.wf n t := by
  cases k with
  | num r => show r.coeff.length ≤ n; simpa [Key.ok] using h
  | counter r => show r.coeff.length ≤ n; simpa [Key.ok] using h
  | words ids =>
    intro i mi
    have := List.all_eq_true.mp h i mi
    simpa using this

/-- The words whose bytes the account's `bytes_of` gives: each is below 2^32, and the bytes are theirs. -/
theorem ofWords_spec : ∀ {ws bs : List Val}, ofWords ws = some bs →
    ∃ nums : List Nat, ws = nums.map Val.word ∧ (∀ v ∈ nums, v < W32) ∧ bs = wordBytes nums
  | [], bs, h => by
    simp only [ofWords, Option.some.injEq] at h; subst h
    exact ⟨[], rfl, (fun v m => nomatch m), rfl⟩
  | v :: rest, bs, h => by
    cases v with
    | word w =>
      simp only [ofWords] at h
      split at h
      next lt =>
        cases hr : ofWords rest with
        | none => simp [hr] at h
        | some bs' =>
          simp only [hr, Option.map_some, Option.some.injEq] at h; subst h
          obtain ⟨nums, e1, e2, e3⟩ := ofWords_spec hr
          refine ⟨w :: nums, by simp [e1], ?_, by simp [wordBytes, e3]⟩
          intro v m
          rcases List.mem_cons.mp m with rfl | m
          · exact lt
          · exact e2 v m
      next => simp at h
    | _ => simp [ofWords] at h

/-- Bytes of memory that are the bytes of words, word by word: the list of them is `wordBytes` of the words. -/
theorem wordBytes_range (mem : Nat → Nat) : ∀ (ds : List Nat) (base : Nat),
    (∀ q, q < ds.length → ∀ b, b < 4 → mem (base + 4 * q + b) = ds.getD q 0 / 256 ^ b % 256) →
    (List.range (4 * ds.length)).map (fun k => Val.int (mem (base + k))) = wordBytes ds
  | [], base, _ => rfl
  | d :: rest, base, h => by
    have ih := wordBytes_range mem rest (base + 4) (fun q hq b hb => by
      have := h (q + 1) (by simp; omega) b hb
      rw [show base + 4 + 4 * q + b = base + 4 * (q + 1) + b by omega]
      simpa using this)
    have h0 := h 0 (by simp) 0 (by omega)
    have h1 := h 0 (by simp) 1 (by omega)
    have h2 := h 0 (by simp) 2 (by omega)
    have h3 := h 0 (by simp) 3 (by omega)
    simp only [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one, Nat.pow_one] at h0 h1 h2 h3
    have e : (fun i => Val.int (mem (base + (i + 4)))) = fun k => Val.int (mem (base + 4 + k)) := by
      funext k
      rw [show base + (k + 4) = base + 4 + k by omega]
    rw [show 4 * (d :: rest).length = 4 * rest.length + 4 by simp; omega, map_range_add4, e, ih]
    simp only [wordBytes, Nat.add_zero, h0, h1, h2, h3]

theorem getD_of_lt {α : Type} (l : List α) (d : α) {k : Nat} (h : k < l.length) : l.getD k d = l[k] := by
  simp [List.getD, List.getElem?_eq_getElem h]

theorem getD_mem {α : Type} (l : List α) (d : α) {k : Nat} (h : k < l.length) : l.getD k d ∈ l := by
  rw [getD_of_lt l d h]; exact List.getElem_mem h

/-! ## The names of the called function -/

/-- A called function taken by this rule is given no run of bytes whose length is a number. -/
theorem calleeW_regions {ctx : Ctx} {s : Sym} {ids : List Nat} (c : Contract) : ∀ (args : List (String × Kind)) (regs : List Nat)
    {env : List (String × WVal)}, calleeW ctx s ids args regs = some env → regionsIn c args regs = []
  | [], _, _, _ => by simp [regionsIn]
  | _ :: _, [], _, _ => by simp [regionsIn]
  | (x, .number) :: args, r :: regs, env, h => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx s ids args regs with
    | none => simp [hrec] at h
    | some env' => simp only [regionsIn]; exact calleeW_regions c args regs hrec
  | (x, .fixed n) :: args, r :: regs, env, h => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx s ids args regs with
    | none => cases hf : fixedPart ctx s r n <;> simp [hf, hrec] at h
    | some env' => simp only [regionsIn]; exact calleeW_regions c args regs hrec
  | (x, .inout n) :: args, r :: regs, env, h => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx s ids args regs with
    | none => simp [hrec] at h
    | some env' => simp only [regionsIn]; exact calleeW_regions c args regs hrec
  | (x, .bytes len) :: args, r :: regs, env, h => by simp [calleeW] at h
  | (x, .out n) :: args, r :: regs, env, h => by simp [calleeW] at h

/-- Each run of a fixed count it is given is a part of one of this function's. -/
theorem calleeW_fixeds {ctx : Ctx} {s : Sym} {ids : List Nat} : ∀ (args : List (String × Kind)) (regs : List Nat)
    {env : List (String × WVal)}, calleeW ctx s ids args regs = some env →
    ∀ x r n, (x, r, n) ∈ fixedsIn args regs → ∃ j b cst, fixedPart ctx s r n = some (j, b, cst)
  | [], _, _, _, x, r, n, m => by simp [fixedsIn] at m
  | _ :: _, [], _, _, x, r, n, m => by simp [fixedsIn] at m
  | (y, .number) :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx s ids args regs with
    | none => simp [hrec] at h
    | some env' => simp only [fixedsIn] at m; exact calleeW_fixeds args regs hrec x r n m
  | (y, .fixed n') :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeW] at h
    cases hf : fixedPart ctx s r' n' with
    | none => simp [hf] at h
    | some pp =>
      obtain ⟨j, b, cst⟩ := pp
      cases hrec : calleeW ctx s ids args regs with
      | none => simp [hf, hrec] at h
      | some env' =>
        simp only [fixedsIn, List.mem_cons] at m
        rcases m with e | m
        · injection e with _ e
          injection e with e1 e2
          subst e1 e2
          exact ⟨j, b, cst, hf⟩
        · exact calleeW_fixeds args regs hrec x r n m
  | (y, .inout n') :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx s ids args regs with
    | none => simp [hrec] at h
    | some env' => simp only [fixedsIn] at m; exact calleeW_fixeds args regs hrec x r n m
  | (y, .bytes len) :: args, r' :: regs, env, h, _, _, _, _ => by simp [calleeW] at h
  | (y, .out n') :: args, r' :: regs, env, h, _, _, _, _ => by simp [calleeW] at h

/-- The called function's names on words stand for its names as the account has them in the state it
starts in (`s1`): a number is its register; a part of a run of a fixed count is the bytes there, as at
entry; the run it reads and writes is the bytes of the words known written. -/
theorem calleeW_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) {T : List Node}
    (c : Contract) {s1 : State} {ids : List Nat}
    (hreg : ∀ r ∈ argRegs, s1.reg r = st.reg r)
    (hfix : ∀ r n j b cst, r ∈ argRegs → fixedPart ctx s r n = some (j, b, cst) →
      ∀ k, k < n → s1.mem (st.reg r + k) = s0.mem (s0.reg b + cst + k) ∧ s0.mem (s0.reg b + cst + k) < 256) :
    ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × WVal)}, (∀ r ∈ regs, r ∈ argRegs) →
      (∀ x r n, (x, r, n) ∈ inoutsIn args regs →
        (List.range n).map (fun k => Val.int (s1.mem (s1.reg r + k))) = wordBytes (ids.map (den (inpOf ctx s0) ρ T))) →
      calleeW ctx s ids args regs = some env → EnvDen ctx s0 ρ T env (envWIn c s1 args regs)
  | [], _, env, _, _, h => by
    simp only [calleeW, Option.some.injEq] at h; subst h; simp [envWIn, EnvDen]
  | _ :: _, [], env, _, _, h => by
    simp only [calleeW, Option.some.injEq] at h; subst h; simp [envWIn, EnvDen]
  | (x, .number) :: args, r :: regs, env, hr, hio, h => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx s ids args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
      have ih := calleeW_sound H c hreg hfix args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
        (fun x' r' n' m => hio x' r' n' (inoutsIn_tail (x, .number) r m)) hrec
      simp only [envWIn]
      refine ⟨rfl, ?_, ih⟩
      have ra := hr r (List.mem_cons_self ..)
      have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := T) (s.reg r)
      rw [← H.reg r (argRegs_lt ra), ← hreg r ra] at this
      exact this
  | (x, .fixed n) :: args, r :: regs, env, hr, hio, h => by
    simp only [calleeW] at h
    cases hf : fixedPart ctx s r n with
    | none => simp [hf] at h
    | some pp =>
      obtain ⟨j, b, cst⟩ := pp
      cases hrec : calleeW ctx s ids args regs with
      | none => simp [hf, hrec] at h
      | some env' =>
        simp only [hf, hrec, Option.some.injEq] at h; subst h
        have ih := calleeW_sound H c hreg hfix args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
          (fun x' r' n' m => hio x' r' n' (inoutsIn_tail (x, .fixed n) r m)) hrec
        simp only [envWIn]
        refine ⟨rfl, ?_, ih⟩
        have ra := hr r (List.mem_cons_self ..)
        have hb : ∀ k, k < n → s0.mem (s0.reg b + cst + k) < 256 := fun k hk => (hfix r n j b cst ra hf k hk).2
        have e : (List.range n).map (fun k => Val.int (s1.mem (s1.reg r + k))) =
            (List.range n).map fun k => Val.int (s0.mem (s0.reg b + cst + k)) :=
          List.map_congr_left fun k mk => by
            rw [hreg r ra, (hfix r n j b cst ra hf k (List.mem_range.mp mk)).1]
        simp only [Val.bytes, List.map_map]
        show WDen ctx s0 ρ T (.part b cst n) (.list ((List.range n).map fun k => Val.int (s1.mem (s1.reg r + k))))
        rw [e]
        exact WDen.part b cst n hb
  | (x, .inout n) :: args, r :: regs, env, hr, hio, h => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx s ids args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
      have ih := calleeW_sound H c hreg hfix args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
        (fun x' r' n' m => hio x' r' n' (inoutsIn_tail (x, .inout n) r m)) hrec
      simp only [envWIn]
      refine ⟨rfl, ?_, ih⟩
      have e := hio x r n (by simp [inoutsIn])
      simp only [Val.bytes, List.map_map]
      show WDen ctx s0 ρ T (.wbytes ids) (.list ((List.range n).map fun k => Val.int (s1.mem (s1.reg r + k))))
      rw [e]
      exact WDen.wbytes ids
  | (x, .bytes len) :: args, r :: regs, env, _, _, h => by simp [calleeW] at h
  | (x, .out n) :: args, r :: regs, env, _, _, h => by simp [calleeW] at h

/-- The terms put into the table for the parts handed over are words of runs. -/
theorem partNodes_inputs {ctx : Ctx} {s : Sym} : ∀ (args : List (String × Kind)) (regs : List Nat) (nd : Node),
    nd ∈ partNodes ctx s args regs → ∃ j k, nd = Node.input j k
  | [], _, nd, m => by simp [partNodes] at m
  | _ :: _, [], nd, m => by simp [partNodes] at m
  | (x, .fixed n) :: args, r :: regs, nd, m => by
    simp only [partNodes, List.mem_append] at m
    rcases m with m | m
    · split at m
      next j _ c _ =>
        split at m
        · obtain ⟨k, _, rfl⟩ := List.mem_map.mp m
          exact ⟨j, c / 4 + k, rfl⟩
        · simp at m
      next => simp at m
    · exact partNodes_inputs args regs nd m
  | (x, .number) :: args, r :: regs, nd, m => by simp only [partNodes] at m; exact partNodes_inputs args regs nd m
  | (x, .bytes len) :: args, r :: regs, nd, m => by simp only [partNodes] at m; exact partNodes_inputs args regs nd m
  | (x, .out n) :: args, r :: regs, nd, m => by simp only [partNodes] at m; exact partNodes_inputs args regs nd m
  | (x, .inout n) :: args, r :: regs, nd, m => by simp only [partNodes] at m; exact partNodes_inputs args regs nd m

/-- With words of runs put into it, the table is still one the verifier may hold, and has grown at most. -/
theorem inputs_table {s : Sym} (wf : WF s) (nodes : List Node) (hn : ∀ nd ∈ nodes, ∃ j k, nd = Node.input j k) :
    Ext s.terms (termsOf intern nodes s.terms).2 ∧ TableOk s.nvars (termsOf intern nodes s.terms).2 := by
  obtain ⟨e, ok, _, _, _⟩ := termsOf_step (mk := intern) (val := fun nd => match nd with | .input _ _ => 0 | _ => 0)
    (inp := fun _ _ => 0) (ρ := fun _ => 0) (nv := s.nvars) (T0 := s.terms) nodes s.terms
    (fun a ma T _ okT => by
      obtain ⟨j, k, rfl⟩ := hn a ma
      exact input_step okT) (Ext.refl _) wf.words.ok
  exact ⟨e, ok⟩

/-! ## The state after the call -/

/-- The terms made for the words of the run the called function wrote, and the table with them. -/
def madeW (s : Sym) (m : Nat) : List Nat × List Node :=
  termsOf wAtom ((List.range m).map fun k => Lin.var (s.nvars + 16 + k)) s.terms

theorem afterCallW_facts (s : Sym) (sp : Int) (w m : Nat) (g : String) (keys : List Key) :
    (s.afterCallW sp w m g keys).facts = ((List.range m).map fun k => ranged32 (s.nvars + 16 + k)).flatten ++
      ((callerSaved.map fun r => ranged (s.nvars + r)).flatten ++ s.facts) := rfl
theorem afterCallW_wroteW (s : Sym) (sp : Int) (w m : Nat) (g : String) (keys : List Key) :
    (s.afterCallW sp w m g keys).wroteW = ((List.range m).map fun k => (w, k, (madeW s m).1.getD k 0)) ++ s.wroteW.filter fun e => e.1 != w := rfl
theorem afterCallW_intact (s : Sym) (sp : Int) (w m : Nat) (g : String) (keys : List Key) :
    (s.afterCallW sp w m g keys).intact = s.intact.filter (· != w) := rfl
theorem afterCallW_known (s : Sym) (sp : Int) (w m : Nat) (g : String) (keys : List Key) :
    (s.afterCallW sp w m g keys).known = .held g keys (madeW s m).1 :: s.known := rfl
theorem afterCallW_terms (s : Sym) (sp : Int) (w m : Nat) (g : String) (keys : List Key) :
    (s.afterCallW sp w m g keys).terms = (madeW s m).2 := rfl
theorem afterCallW_nvars (s : Sym) (sp : Int) (w m : Nat) (g : String) (keys : List Key) :
    (s.afterCallW sp w m g keys).nvars = s.nvars + 16 + m := rfl

/-- The table with the terms of the new words: it has grown at most, is one the verifier may hold with the
new unknowns in use, has one term a word, each in the table. -/
theorem madeW_table {s : Sym} (wf : WF s) (m : Nat) (inp : Nat → Nat → Nat) (ρ : Nat → Int) :
    Ext s.terms (madeW s m).2 ∧ TableOk (s.nvars + 16 + m) (madeW s m).2 ∧ (madeW s m).1.length = m ∧
    (∀ i ∈ (madeW s m).1, i < (madeW s m).2.length) ∧
    ∀ k, k < m → den inp ρ (madeW s m).2 ((madeW s m).1.getD k 0) = (ev ρ (Lin.var (s.nvars + 16 + k)) % W32i).toNat := by
  obtain ⟨ext, ok, len, lt, dn⟩ := termsOf_step (mk := wAtom) (val := fun r => (ev ρ r % W32i).toNat)
    (inp := inp) (ρ := ρ) (nv := s.nvars + 16 + m) (T0 := s.terms)
    ((List.range m).map fun k => Lin.var (s.nvars + 16 + k)) s.terms
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

theorem afterCallW_wf {s : Sym} (wf : WF s) (sp : Int) (w m : Nat) (g : String) {keys : List Key}
    (hkeys : ∀ k ∈ keys, k.wf s.nvars s.terms.length) : WF (s.afterCallW sp w m g keys) := by
  have le : s.nvars ≤ s.nvars + 16 + m := by omega
  obtain ⟨ext, ok, len, lt, _⟩ := madeW_table wf m (fun _ _ => 0) (fun _ => 0)
  refine ⟨Nat.le_trans wf.base le, ?_, trivial, trivial, ?_, ?_, ?_, ?_, ?_,
    ⟨ok.wf, ok.atoms, (fun x ids h => by simp [Sym.afterCallW] at h), ok.rotrs, ?_, fun _ _ h => nomatch h⟩, ?_⟩
  · intro r hr
    show bounded (s.nvars + 16 + m) (if callerSaved.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    split
    · exact bounded_var (by omega)
    · exact bounded_mono le (wf.reg r hr)
  · intro o v mm
    exact bounded_mono le (wf.frame o v (List.mem_filter.mp mm).1)
  · intro f mf
    rw [afterCallW_facts] at mf
    rcases List.mem_append.mp mf with mf | mf
    · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
      have hk := List.mem_range.mp hk
      simp only [ranged32, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · exact bounded_var (show s.nvars + 16 + k < s.nvars + 16 + m by omega)
      · exact bounded_sub (bounded_const _ _) (bounded_var (show s.nvars + 16 + k < s.nvars + 16 + m by omega))
    · rcases List.mem_append.mp mf with mf | mf
      · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        have hr := callerSaved_lt hr
        simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with rfl | rfl
        · exact bounded_var (show s.nvars + r < s.nvars + 16 + m by omega)
        · exact bounded_sub (bounded_const _ _) (bounded_var (show s.nvars + r < s.nvars + 16 + m by omega))
      · exact bounded_mono le (wf.facts f mf)
  · intro v r o mm
    have := wf.bytes v r o mm
    exact ⟨Nat.lt_of_lt_of_le this.1 le, bounded_mono le this.2⟩
  · intro f mm
    exact SFact.bounded_mono le (wf.spec f mm)
  · intro w' o x mm
    exact ⟨bounded_mono le (wf.wrote w' o x mm).1, bounded_mono le (wf.wrote w' o x mm).2⟩
  · intro w' j i h
    rw [afterCallW_wroteW] at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨k, hk, e⟩ := List.mem_map.mp h
      have hk := List.mem_range.mp hk
      injection e with _ e
      injection e with _ e
      rw [← e]
      exact lt _ (getD_mem _ _ (by omega))
    · exact Nat.lt_of_lt_of_le (wf.words.wrote w' j i (List.mem_filter.mp h).1) ext.le
  · intro k mk
    rw [afterCallW_known] at mk
    rcases List.mem_cons.mp mk with rfl | mk
    · exact ⟨(Known.wf_mono le ext.le (k := .held g keys []) ⟨hkeys, fun i mi => nomatch mi⟩).1, lt⟩
    · exact Known.wf_mono le ext.le (wf.known k mk)

/-- What the unknowns are after such a call: those made for the registers are what the registers then hold,
and those made for the words of the run are the words. -/
def afterRhoW (n : Nat) (ρ : Nat → Int) (s2 : State) (nums : List Nat) : Nat → Int :=
  fun k => if n ≤ k ∧ k < n + 16 then (s2.reg (k - n) : Int)
    else if n + 16 ≤ k ∧ k < n + 16 + nums.length then (nums.getD (k - (n + 16)) 0 : Int) else ρ k

theorem afterRhoW_agree (n : Nat) (ρ : Nat → Int) (s2 : State) (nums : List Nat) : Agree n ρ (afterRhoW n ρ s2 nums) := by
  intro k hk
  show ρ k = if n ≤ k ∧ k < n + 16 then (s2.reg (k - n) : Int)
    else if n + 16 ≤ k ∧ k < n + 16 + nums.length then (nums.getD (k - (n + 16)) 0 : Int) else ρ k
  rw [if_neg (by omega), if_neg (by omega)]

theorem afterRhoW_reg (n : Nat) (ρ : Nat → Int) (s2 : State) (nums : List Nat) {r : Nat} (hr : r < 16) :
    afterRhoW n ρ s2 nums (n + r) = s2.reg r := by
  show (if n ≤ n + r ∧ n + r < n + 16 then (s2.reg (n + r - n) : Int)
    else if n + 16 ≤ n + r ∧ n + r < n + 16 + nums.length then (nums.getD (n + r - (n + 16)) 0 : Int) else ρ (n + r)) = s2.reg r
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

theorem afterRhoW_word (n : Nat) (ρ : Nat → Int) (s2 : State) (nums : List Nat) {k : Nat} (hk : k < nums.length) :
    afterRhoW n ρ s2 nums (n + 16 + k) = nums.getD k 0 := by
  show (if n ≤ n + 16 + k ∧ n + 16 + k < n + 16 then (s2.reg (n + 16 + k - n) : Int)
    else if n + 16 ≤ n + 16 + k ∧ n + 16 + k < n + 16 + nums.length then (nums.getD (n + 16 + k - (n + 16)) 0 : Int)
    else ρ (n + 16 + k)) = nums.getD k 0
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

/-- Of the machine's state when the called function has returned, what the verifier holds after the call is
so: given that the registers a callee keeps and the stack pointer are as before the call; memory is as
before but in the called function's frame, at the address it returned to and in the run `w`; the run holds
the bytes of the words `nums`; and the definition `g`, used with `keys`, gives those words. -/
theorem afterCallW_holds {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st s2 : State}
    {sp : Int} (cs : Nat) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hsp : (st.reg RSP : Int) = s0.reg RSP + sp) (hlow : -(ctx.contract.stack : Int) ≤ sp - 8 - cs) (hsp0 : sp ≤ 0)
    (hkeep : ∀ r, r < 16 → callerSaved.contains r = false → s2.reg r = st.reg r)
    (hsmall : ∀ r, s2.reg r < M64)
    {w m : Nat} {x : String} {b n : Nat} (hw : ctx.contract.outs[w]? = some (x, b, n)) (hn : n = 4 * m)
    (hnow : ∀ e ∈ s.wrote, e.1 ≠ w)
    (hmem : ∀ a, a + 8 + cs < st.reg RSP ∨ st.reg RSP ≤ a → a < s0.reg b ∨ s0.reg b + n ≤ a → s2.mem a = st.mem a)
    {nums : List Nat} (hlen : nums.length = m) (hlt : ∀ v ∈ nums, v < W32)
    (hrun : ∀ k, k < m → ∀ bb, bb < 4 → s2.mem (s0.reg b + 4 * k + bb) = nums.getD k 0 / 256 ^ bb % 256)
    {g : String} {keys : List Key} (hkeys : ∀ k ∈ keys, k.wf s.nvars s.terms.length)
    (hheld : ∃ d, findDef ctx.defs g = some d ∧ d.params.length = keys.length ∧
      Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ s.terms))) d.body (.list (nums.map Val.word))) :
    Holds ctx s0 (afterRhoW s.nvars ρ s2 nums) (s.afterCallW sp w m g keys) s2 := by
  have hstack := E.stack
  have hwm := List.mem_of_getElem? hw
  have hout := E.out hwm
  have ag := afterRhoW_agree s.nvars ρ s2 nums
  have H' := H.agree wf ag
  obtain ⟨ext, ok, len, lt, dn⟩ := madeW_table wf m (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums)
  -- the terms of the new words are the words
  have hden : ∀ k, k < m → den (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums) (madeW s m).2 ((madeW s m).1.getD k 0) = nums.getD k 0 := by
    intro k hk
    rw [dn k hk, ev_var, afterRhoW_word _ _ _ _ (by omega)]
    have := hlt (nums.getD k 0) (getD_mem _ _ (by omega))
    unfold W32 at this
    unfold W32i
    omega
  -- the terms there were are as they were
  have hold : ∀ i, i < s.terms.length →
      den (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums) (madeW s m).2 i = den (inpOf ctx s0) ρ s.terms i :=
    fun i hi => den_mono wf.words.table wf.words.atoms ag ext hi
  refine ⟨H'.entry, ?_, hsmall, trivial, trivial, ?_, ?_, H'.bytes, H'.spec, ?_, ?_, ⟨(fun x ids h => by simp [Sym.afterCallW] at h), ?_, ?_, fun _ _ h => nomatch h⟩, ?_⟩
  · intro r hr
    show (s2.reg r : Int) = ev _ (if callerSaved.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    cases hc : callerSaved.contains r with
    | true => rw [if_pos rfl, ev_var, afterRhoW_reg _ _ _ _ hr]
    | false =>
      rw [if_neg (by decide), hkeep r hr hc]
      exact H'.reg r hr
  · intro o v mm
    obtain ⟨m1, m2⟩ := List.mem_filter.mp mm
    have m2' : sp ≤ o := by simpa using m2
    obtain ⟨h1, h2, h3⟩ := H'.frame o v m1
    refine ⟨h1, h2, ?_⟩
    have e : load s2.mem ((s0.reg RSP : Int) + o).toNat 8 = load st.mem ((s0.reg RSP : Int) + o).toNat 8 :=
      load_congr _ _ _ _ (fun a hx1 hx2 => hmem a (Or.inr (by omega)) (by omega))
    rw [e]; exact h3
  · intro f mf
    rw [afterCallW_facts] at mf
    rcases List.mem_append.mp mf with mf | mf
    · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
      have hk := List.mem_range.mp hk
      have val := afterRhoW_word s.nvars ρ s2 nums (k := k) (by omega)
      have vlt := hlt (nums.getD k 0) (getD_mem _ _ (by omega))
      unfold W32 at vlt
      simp only [ranged32, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · rw [holds_iff, ev_var, val]; omega
      · rw [holds_iff, ev_sub, ev_const, ev_var, val]; unfold W32i; omega
    · rcases List.mem_append.mp mf with mf | mf
      · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        have hr := callerSaved_lt hr
        have sm := hsmall r
        unfold M64 at sm
        have val := afterRhoW_reg s.nvars ρ s2 nums hr
        simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with rfl | rfl
        · rw [holds_iff, ev_var, val]; omega
        · rw [holds_iff, ev_sub, ev_const, ev_var, val]; simp only [top]; omega
      · exact H'.facts f mf
  · intro a ha ho
    have hfr : a + 8 + cs < st.reg RSP ∨ st.reg RSP ≤ a := by
      simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at ha
      omega
    have hnot : a < s0.reg b ∨ s0.reg b + n ≤ a := by
      unfold Contract.inOut at ho
      have := List.any_eq_false.mp ho (x, b, n) hwm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      omega
    rw [hmem a hfr hnot]
    exact H.mem a ha ho
  · -- what this function wrote for its caller, byte by byte, is of other runs: they lie apart from the run written
    intro w' o x' mw
    obtain ⟨name, r', n', g1, g2, g3, g4⟩ := H'.wrote w' o x' mw
    refine ⟨name, r', n', g1, g2, g3, ?_⟩
    have ne : w' ≠ w := hnow (w', o, x') mw
    have ho' := E.out (List.mem_of_getElem? g1)
    have ap := E.outOut g1 hw ne
    rw [hmem _ (by omega) (by omega)]
    exact g4
  · -- a run nothing was written to, but the one handed over
    intro w' mw' x' r' n' ho' k hk
    rw [afterCallW_intact] at mw'
    obtain ⟨mi, ne⟩ := List.mem_filter.mp mw'
    have ne' : w' ≠ w := by simpa using ne
    have hor := E.out (List.mem_of_getElem? ho')
    have ap := E.outOut ho' hw ne'
    rw [hmem _ (by omega) (by omega)]
    exact H.words.intact w' mi x' r' n' ho' k hk
  · -- the words known written: those of the run handed over are the new ones; the others are as they were
    intro w' j i mw' x' r' n' ho'
    rw [afterCallW_wroteW] at mw'
    rcases List.mem_append.mp mw' with mn | mo
    · obtain ⟨k, hk, e⟩ := List.mem_map.mp mn
      have hk := List.mem_range.mp hk
      injection e with e1 e
      injection e with e2 e3
      subst e1 e2 e3
      rw [hw] at ho'
      injection ho' with ho'
      injection ho' with _ ho'
      injection ho' with hb' hn'
      subst hb' hn'
      refine ⟨by omega, fun bb hbb => ?_⟩
      rw [hrun k hk bb hbb, afterCallW_terms, hden k hk]
    · obtain ⟨mo, ne⟩ := List.mem_filter.mp mo
      have ne' : w' ≠ w := by simpa using ne
      obtain ⟨h1, h2⟩ := H.words.wrote w' j i mo x' r' n' ho'
      have hor := E.out (List.mem_of_getElem? ho')
      have ap := E.outOut ho' hw ne'
      refine ⟨h1, fun bb hbb => ?_⟩
      rw [hmem _ (by omega) (by omega), h2 bb hbb, afterCallW_terms, hold i (wf.words.wrote w' j i mo)]
  · intro k mk
    rw [afterCallW_known] at mk
    rcases List.mem_cons.mp mk with rfl | mk
    · -- the definition, used with what the called function was given, is the new words
      obtain ⟨d, hd, hlen', hv⟩ := hheld
      refine ⟨d, hd, hlen', ?_⟩
      have e1 : keys.map (Key.val ctx s0 (afterRhoW s.nvars ρ s2 nums) (madeW s m).2) = keys.map (Key.val ctx s0 ρ s.terms) :=
        List.map_congr_left fun k' mk' => Key.val_mono (hkeys k' mk') ag wf.words.table wf.words.atoms ext
      have e2 : (madeW s m).1.map (fun i => Val.word (den (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums) (madeW s m).2 i)) = nums.map Val.word := by
        apply List.ext_getElem
        · simp [len, hlen]
        · intro i h1 h2
          have hi : i < m := by simpa [len] using h1
          have := hden i hi
          rw [getD_of_lt _ _ (by omega), getD_of_lt _ _ (by omega)] at this
          simp only [List.getElem_map, this]
      show Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 (afterRhoW s.nvars ρ s2 nums) (madeW s m).2))) d.body
        (.list ((madeW s m).1.map fun i => Val.word (den (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums) (madeW s m).2 i)))
      rw [e1, e2]
      exact hv
    · exact Known.holds_mono (wf.known k mk) ag wf.words.table wf.words.atoms ext (H.known k mk)

/-! ## The call -/

/-- What `callW` has looked up, where it says how the call is taken. -/
theorem callW_spec {ctx : Ctx} {s : Sym} {c : Contract} {plan : CallW} (h : callW ctx s c = .ok plan) :
    ∃ (run : String) (r n : Nat) (e : EnsureW) (ids : List Nat) (env : List (String × WVal)) (args : SExpr) (vs : List WVal) (d : Def),
      c.mbounds = [] ∧ c.outs = [(run, r, n)] ∧ c.inouts = [(run, r, n)] ∧ c.ensuresW = [e] ∧ e.run = run ∧
      callRun ctx s r n = some (plan.w, ids) ∧ calleeW ctx s ids c.args argRegs = some env ∧
      e.value = .call "bytes_of" (.cons (.call plan.g args) .nil) ∧ own.contains plan.g = false ∧ plan.g ≠ "len" ∧
      plan.terms = (termsOf intern (partNodes ctx s c.args argRegs) s.terms).2 ∧
      wevalList (weval ctx (fun n => findNode n plan.terms 0) { s with terms := plan.terms } WFUEL env) args = some vs ∧
      findDef ctx.defs plan.g = some d ∧ flatKeys (fun n => findNode n plan.terms 0) vs = some plan.keys ∧
      (∀ k ∈ plan.keys, k.wf s.nvars plan.terms.length) ∧ d.params.length = plan.keys.length ∧ plan.words = n / 4 := by
  unfold callW at h
  split at h
  next => cases h
  next hmb =>
    have hmb' : c.mbounds = [] := by simpa using hmb
    rcases houts : c.outs with _ | ⟨⟨run, r, n⟩, _ | ⟨o2, omore⟩⟩
    · simp only [houts] at h; cases h
    · rcases hinouts : c.inouts with _ | ⟨⟨run', r', n'⟩, _ | ⟨i2, imore⟩⟩
      · simp only [houts, hinouts] at h; cases h
      · rcases hens : c.ensuresW with _ | ⟨e, _ | ⟨e2, emore⟩⟩
        · simp only [houts, hinouts, hens] at h; cases h
        · simp only [houts, hinouts, hens] at h
          split at h
          next => cases h
          next hsame =>
            have hs : ((run = run' ∧ r = r') ∧ n = n') ∧ e.run = run := by simpa using hsame
            obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, erun⟩ := hs
            cases hcr : callRun ctx s r n with
            | none => simp only [hcr] at h; cases h
            | some wi =>
              obtain ⟨w, ids⟩ := wi
              simp only [hcr] at h
              cases hce : calleeW ctx s ids c.args argRegs with
              | none => simp only [hce] at h; cases h
              | some env =>
                simp only [hce] at h
                cases hv : e.value with
                | call f a =>
                  cases a with
                  | cons a1 a2 =>
                    cases a1 with
                    | call g args =>
                      cases a2 with
                      | nil =>
                        simp only [hv] at h
                        split at h
                        next hfg =>
                          have hfg' : (f = "bytes_of" ∧ own.contains g = false) ∧ g ≠ "len" := by simpa using hfg
                          obtain ⟨⟨rfl, hown⟩, hlen⟩ := hfg'
                          have hl : (fun n => (termIndex (termsOf intern (partNodes ctx s c.args argRegs) s.terms).2)[n]?) =
                              fun n => findNode n (termsOf intern (partNodes ctx s c.args argRegs) s.terms).2 0 :=
                            funext fun n => termIndex_spec _ n
                          simp only [hl] at h
                          split at h
                          next vs d hwl hfd =>
                            split at h
                            next keys hfk =>
                              split at h
                              next => cases h
                              next hok =>
                                split at h
                                next hdl =>
                                  injection h with h
                                  subst h
                                  have hok' : (keys.all (Key.ok s.nvars (termsOf intern (partNodes ctx s c.args argRegs) s.terms).2.length)) = true := by
                                    simpa using hok
                                  exact ⟨run, r, n, e, ids, env, args, vs, d, hmb', rfl, rfl, rfl, erun, hcr, hce, hv, hown, hlen, rfl, hwl, hfd, hfk,
                                    (fun k mk => Key.ok_wf (List.all_eq_true.mp hok' k mk)), by simpa using hdl, rfl⟩
                                next => cases h
                            next => cases h
                          next => cases h
                        next => cases h
                      | _ => simp only [hv] at h; cases h
                    | _ => simp only [hv] at h; cases h
                  | _ => simp only [hv] at h; cases h
                | _ => simp only [hv] at h; cases h
        · simp only [houts, hinouts, hens] at h; cases h
      · simp only [houts, hinouts] at h; cases h
    · simp only [houts] at h; cases h

/-- An address in a run of a fixed count given to read is in no run given to write. -/
theorem fixed_notOut {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {x : String} {r n : Nat}
    (h : (x, r, n) ∈ ctx.contract.fixeds) {a : Nat} (h1 : s0.reg r ≤ a) (h2 : a < s0.reg r + n) :
    ctx.contract.inOut s0 a = false := by
  unfold Contract.inOut
  rw [List.any_eq_false]
  intro ⟨x', r', n'⟩ hm
  have := (E.fixed h).2.2.2 x' r' n' hm
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- Bytes that are the bytes of words: four a word, each byte the word's. -/
theorem wordBytes_get : ∀ (nums : List Nat) (l : List Nat), l.map (fun (b : Nat) => Val.int b) = wordBytes nums →
    l.length = 4 * nums.length ∧ ∀ k, k < nums.length → ∀ bb, bb < 4 → l.getD (4 * k + bb) 0 = nums.getD k 0 / 256 ^ bb % 256
  | [], l, h => by
    cases l with
    | nil => exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    | cons a l' => simp [wordBytes] at h
  | d :: rest, l, h => by
    match l, h with
    | [], h => simp [wordBytes] at h
    | [_], h => simp [wordBytes] at h
    | [_, _], h => simp [wordBytes] at h
    | [_, _, _], h => simp [wordBytes] at h
    | a :: b :: c :: e :: l', h =>
      simp only [wordBytes, List.map_cons, List.cons.injEq, Val.int.injEq] at h
      obtain ⟨ha, hb, hc, he, hl⟩ := h
      obtain ⟨len, hk⟩ := wordBytes_get rest l' hl
      refine ⟨by simp [len]; omega, ?_⟩
      intro k hk' bb hbb
      cases k with
      | zero =>
        match bb, hbb with
        | 0, _ => simp; omega
        | 1, _ => simp; omega
        | 2, _ => simp; omega
        | 3, _ => simp; omega
      | succ k =>
        have := hk k (by simpa using hk') bb hbb
        rw [show 4 * (k + 1) + bb = (4 * k + bb) + 1 + 1 + 1 + 1 by omega]
        simpa using this

/-- The bytes a function's contract says its run holds, where they are `bytes_of` of a use of a definition:
the definition, used with the values of the things there, gives words below 2^32, and the bytes are theirs. -/
theorem bytes_of_call {defs : List Def} {env : List (String × Val)} {g : String} {args : SExpr} {l : List Nat}
    (hown : own.contains g = false) (hlen : g ≠ "len")
    (hv : Value defs env (.call "bytes_of" (.cons (.call g args) .nil)) (.bytes l)) :
    ∃ (fuel : Nat) (as : List Val) (d : Def) (nums : List Nat), evalList (evalSpec defs fuel env) args = some as ∧
      findDef defs g = some d ∧ d.params.length = as.length ∧
      evalSpec defs fuel (d.params.zip as) d.body = some (.list (nums.map Val.word)) ∧
      (∀ v ∈ nums, v < W32) ∧ l.map (fun (b : Nat) => Val.int b) = wordBytes nums := by
  obtain ⟨fuel, hf⟩ := hv
  cases fuel with
  | zero => simp [evalSpec] at hf
  | succ f1 =>
    simp only [evalSpec, evalList] at hf
    cases h1 : evalSpec defs f1 env (.call g args) with
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
          cases f1 with
          | zero => simp [evalSpec] at h1
          | succ f2 =>
            simp only [evalSpec] at h1
            cases ha : evalList (evalSpec defs f2 env) args with
            | none => simp [ha] at h1
            | some as =>
              have hl : (g == "len") = false := by simpa using hlen
              simp only [ha, hl, hown, Bool.false_eq_true, ↓reduceIte] at h1
              cases hd : findDef defs g with
              | none => simp [hd] at h1
              | some d =>
                simp only [hd] at h1
                split at h1
                next hp =>
                  exact ⟨f2, as, d, nums, ha, rfl, by simpa using hp, h1, e2, by rw [← hf, e3]⟩
                next => simp at h1
      | _ => simp [builtin] at hf

/-- **A call, by contract, of a function that writes a run of words for its caller.** If the verifier has
gone through such a call, then of the machine at the call: the address to come back to can be written; the
state the called function starts in is one its contract's caller has seen to; what the called function may
touch, this function may touch; and of every state the contract lets it return in, what the verifier holds
after the call is so, at the next instruction. -/
theorem symCallW_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallW ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (q : Program) (hq : q.fits) (i : Instr) (hret : p.base + i.next < M64) :
    8 ≤ st.reg RSP ∧ allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true) ∧
    (∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  cases hsp : s.sp with
  | none => simp only [symCallW, hsp] at h; exact (refuse_ok h).elim
  | some sp =>
    simp only [symCallW, hsp] at h
    split at h
    next => exact (refuse_ok h).elim
    next hguard =>
      have hg : sp ≤ 0 ∧ -(ctx.contract.stack : Int) ≤ sp - 8 - c.stack := by simpa using hguard
      cases hplan : callW ctx s c with
      | error what => simp only [hplan] at h; exact (refuse_ok h).elim
      | ok plan =>
        simp only [hplan] at h
        obtain ⟨⟨u, items1⟩, r1, hbounds, h⟩ := V.bind_ok h
        have hfin := V.pure_ok h
        injection hfin with hs' _
        subst hs'
        obtain ⟨run, r, n, e, ids, env, args, vs, d, hmb, houts, hinouts, hens, erun, hcr, hce, hv, hown, hglen, hT, hwl, hfd, hfk,
          hkeys, hdl, hwords⟩ := callW_spec hplan
        obtain ⟨xw, b, how, hio, n4, hreg_r, hnow, hwi⟩ := callRun_spec hcr
        obtain ⟨idlen, hwritten⟩ := writtenIds_spec (n / 4) 0 hwi
        -- the machine at the call
        have esp := ev_isConst (ρ := ρ) hsp
        simp only [ev_sub, ev_var] at esp
        have h1 := H.reg RSP (by decide)
        have h2 := H.entry RSP (by decide)
        have hrsp : (st.reg RSP : Int) = s0.reg RSP + sp := by omega
        have hstack := E.stack
        have habove := E.above
        have hsmallsp := H.small RSP
        have h8 : 8 ≤ st.reg RSP := by omega
        have s1rsp : (afterCall p q i st).reg RSP = st.reg RSP - 8 := by simp [afterCall]
        have s1reg : ∀ r, r ≠ RSP → (afterCall p q i st).reg r = st.reg r := fun r hr => by simp [afterCall, hr]
        have s1mem : ∀ x, x < st.reg RSP - 8 ∨ st.reg RSP ≤ x → (afterCall p q i st).mem x = st.mem x := fun x hx => by
          show store st.mem (st.reg RSP - 8) (p.base + i.next) 8 x = st.mem x
          exact store_other _ _ _ _ _ (by omega)
        -- the run handed over to be read and written: one of this function's, whole
        have hwm := List.mem_of_getElem? how
        have hout := E.out hwm
        have rmem : (run, r, n) ∈ c.outs := by rw [houts]; exact List.mem_cons_self ..
        have rarg : r ∈ argRegs := outsIn_mem c.args argRegs run r n rmem
        obtain ⟨r16, rne⟩ := argRegs_not_rsp rarg
        have b16 := outs_lt hwm
        have hrb : st.reg r = s0.reg b := by
          have := H.reg r r16
          rw [hreg_r ρ, H.entry b b16] at this
          omega
        have s1r : (afterCall p q i st).reg r = s0.reg b := by rw [s1reg r rne, hrb]
        have hregions : c.regions = [] := calleeW_regions c c.args argRegs hce
        -- the table with the words of the parts handed over
        obtain ⟨extT, okT⟩ := inputs_table wf (partNodes ctx s c.args argRegs) (partNodes_inputs c.args argRegs)
        rw [← hT] at extT okT
        have CT := Carried.terms H wf extT okT
        have HT := CT.holds
        have wfT := CT.wf
        -- each part handed over to be read lies in one of this function's runs of a fixed count
        have hpart : ∀ x' r' n', (x', r', n') ∈ c.fixeds → ∃ j b' cst x0 n0, fixedPart ctx s r' n' = some (j, b', cst) ∧
            ctx.contract.fixeds[j]? = some (x0, b', n0) ∧ cst + n' ≤ n0 ∧ st.reg r' = s0.reg b' + cst ∧ r' ∈ argRegs := by
          intro x' r' n' m
          obtain ⟨j, b', cst, hf⟩ := calleeW_fixeds c.args argRegs hce x' r' n' m
          obtain ⟨x0, n0, g1, g2, g3⟩ := fixedPart_spec hf
          have ra := fixedsIn_mem c.args argRegs x' r' n' m
          have b16' := fixeds_lt (List.mem_of_getElem? g1)
          have := H.reg r' (argRegs_lt ra)
          rw [g3 ρ, H.entry b' b16'] at this
          exact ⟨j, b', cst, x0, n0, hf, g1, g2, by omega, ra⟩
        have hfixmem : ∀ r' n' j b' cst, r' ∈ argRegs → fixedPart ctx s r' n' = some (j, b', cst) →
            ∀ k, k < n' → (afterCall p q i st).mem (st.reg r' + k) = s0.mem (s0.reg b' + cst + k) ∧ s0.mem (s0.reg b' + cst + k) < 256 := by
          intro r' n' j b' cst ra hf k hk
          obtain ⟨x0, n0, g1, g2, g3⟩ := fixedPart_spec hf
          have hm0 := List.mem_of_getElem? g1
          have b16' := fixeds_lt hm0
          obtain ⟨f1, f2, f3, f4⟩ := E.fixed hm0
          have hreg' := H.reg r' (argRegs_lt ra)
          rw [g3 ρ, H.entry b' b16'] at hreg'
          have ea : st.reg r' + k = s0.reg b' + cst + k := by omega
          have hb := f3 (cst + k) (by omega)
          rw [← Nat.add_assoc] at hb
          refine ⟨?_, hb⟩
          rw [ea, s1mem _ (by omega)]
          exact H.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (fixed_notOut E hm0 (by omega) (by omega))
        -- the bytes of the run handed over are the bytes of the words known written
        have hbytes : ∀ j, j < n / 4 → ∀ bb, bb < 4 →
            (afterCall p q i st).mem (s0.reg b + 4 * j + bb) = den (inpOf ctx s0) ρ plan.terms (ids.getD j 0) / 256 ^ bb % 256 := by
          intro j hj bb hbb
          have m := hwritten j hj
          rw [Nat.zero_add] at m
          obtain ⟨g1, g2⟩ := HT.words.wrote plan.w j (ids.getD j 0) m xw b n how
          rw [s1mem _ (by omega)]
          exact g2 bb hbb
        have hiobytes : (List.range n).map (fun k => Val.int ((afterCall p q i st).mem ((afterCall p q i st).reg r + k))) =
            wordBytes (ids.map (den (inpOf ctx s0) ρ plan.terms)) := by
          have := wordBytes_range (afterCall p q i st).mem (ids.map (den (inpOf ctx s0) ρ plan.terms)) ((afterCall p q i st).reg r)
            (fun j hj bb hbb => by
              have hj' : j < ids.length := by simpa using hj
              rw [s1r, hbytes j (by omega) bb hbb, getD_of_lt _ _ hj, getD_of_lt _ _ hj', List.getElem_map])
          rw [List.length_map, idlen, show 4 * (n / 4) = n by omega] at this
          exact this
        have henv : EnvDen ctx s0 ρ plan.terms env (c.envW (afterCall p q i st)) :=
          calleeW_sound H c (fun r' m => s1reg r' (argRegs_not_rsp m).2) hfixmem c.args argRegs (fun _ m => m)
            (fun x' r' n' m => by
              have m' : (x', r', n') ∈ c.inouts := m
              rw [hinouts] at m'
              simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m'
              obtain ⟨_, e1, e2⟩ := m'
              subst r' n'
              exact hiobytes) hce
        have hpre : c.pre q (afterCall p q i st) := by
          refine ⟨rfl, ?_, ?_, ?_, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro r'
            by_cases hr : r' = RSP
            · rw [hr, s1rsp]; omega
            · rw [s1reg r' hr]; exact H.small r'
          · rw [s1rsp]; omega
          · rw [s1rsp]; omega
          · intro r' l m; rw [hregions] at m; cases m
          · intro x' r' n' m
            rw [houts] at m
            simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m
            obtain ⟨_, e1, e2⟩ := m
            subst r' n'
            refine ⟨by rw [s1r]; exact hout.1, by rw [s1r, s1rsp]; have := hout.2; omega, ?_⟩
            intro r'' l m'; rw [hregions] at m'; cases m'
          · rw [houts]; exact List.pairwise_singleton _ _
          · intro x' r' n' m
            obtain ⟨j, b', cst, x0, n0, hf, g1, g2, g3, ra⟩ := hpart x' r' n' m
            have hm0 := List.mem_of_getElem? g1
            obtain ⟨f1, f2, f3, f4⟩ := E.fixed hm0
            have rne' := (argRegs_not_rsp ra).2
            refine ⟨by rw [s1reg r' rne', g3]; omega, by rw [s1reg r' rne', g3, s1rsp]; omega, ?_, ?_⟩
            · intro k hk
              rw [s1reg r' rne', (hfixmem r' n' j b' cst ra hf k hk).1]
              exact (hfixmem r' n' j b' cst ra hf k hk).2
            · intro x'' r'' n'' m''
              rw [houts] at m''
              simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
              obtain ⟨_, e1, e2⟩ := m''
              subst r'' n''
              have := f4 xw b n hwm
              rw [s1reg r' rne', g3, s1r]
              omega
          · intro x' r' n' m k hk
            rw [hinouts] at m
            simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m
            obtain ⟨_, e1, e2⟩ := m
            subst r' n'
            have := hbytes (k / 4) (by omega) (k % 4) (by omega)
            rw [s1r, show s0.reg b + k = s0.reg b + 4 * (k / 4) + k % 4 by omega, this]
            exact Nat.mod_lt _ (by decide)
          · intro x' bd m r' hr'
            obtain ⟨items', res, he⟩ := each_mem hbounds (x', bd) m
            simp only [hr'] at he
            have hge := entail_sound he ρ H.facts
            rw [ev_sub, ev_const] at hge
            have ra := regOfIn_mem x' c.args argRegs r' hr'
            have hreg' := H.reg r' (argRegs_lt ra)
            rw [s1reg r' (argRegs_not_rsp ra).2]
            omega
          · intro x' off bd m; rw [hmb] at m; cases m
        have hread : ∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true := by
          intro a ha
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          rcases ha with ((ha | ha) | ha) | ha
          · left; left; left; omega
          · left; left; left; omega
          · rw [hregions] at ha; simp at ha
          · right
            simp only [Contract.inFixed, Bool.or_eq_true] at ha ⊢
            rcases ha with ha | ha
            · left
              obtain ⟨⟨x', r', n'⟩, m, hin⟩ := List.any_eq_true.mp ha
              obtain ⟨j, b', cst, x0, n0, hf, g1, g2, g3, ra⟩ := hpart x' r' n' m
              simp only [Bool.and_eq_true, decide_eq_true_eq, s1reg r' (argRegs_not_rsp ra).2, g3] at hin
              exact List.any_eq_true.mpr ⟨(x0, b', n0), List.mem_of_getElem? g1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
            · right
              rw [hinouts] at ha
              simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
              exact List.any_eq_true.mpr ⟨(xw, b, n), hio, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ha⟩
        have hwrite : ∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true := by
          intro a ha
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          rcases ha with ha | ha
          · left; omega
          · right
            simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
            unfold Contract.inOut
            exact List.any_eq_true.mpr ⟨(xw, b, n), hwm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ha⟩
        have hwr : allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true := by
          apply allowed_of
          intro x hx1 hx2
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          left; omega
        refine ⟨h8, hwr, hpre, hread, hwrite, ?_⟩
        intro s2 post
        obtain ⟨prip, prsp, psaved, pmem, pret, psmall, _, pensW⟩ := post
        have hrip : s2.rip = p.base + i.next := by
          rw [prip, s1rsp]
          show load (store st.mem (st.reg RSP - 8) (p.base + i.next) 8) (st.reg RSP - 8) 8 = p.base + i.next
          exact load_store_same _ _ _ _ (by unfold M64 at hret; omega)
        have hkeep : ∀ r, r < 16 → callerSaved.contains r = false → s2.reg r = st.reg r := by
          intro r' hr hc
          by_cases h4 : r' = RSP
          · rw [h4, prsp, s1rsp]; omega
          · have hmemr : r' ∈ calleeSaved := by
              unfold RSP at h4
              simp [callerSaved] at hc
              simp only [calleeSaved, List.mem_cons, List.mem_nil_iff, or_false]
              omega
            rw [psaved r' hmemr, s1reg r' h4]
        -- memory when the called function has returned: as before but in its frame, at the address it
        -- returned to and in the run it wrote
        have hmem2 : ∀ a, a + 8 + c.stack < st.reg RSP ∨ st.reg RSP ≤ a → a < s0.reg b ∨ s0.reg b + n ≤ a → s2.mem a = st.mem a := by
          intro a ha hb
          rw [pmem a (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1rsp]; omega)
            (by simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1r]; omega)]
          exact s1mem a (by omega)
        -- what the contract of the called function says of the run
        obtain ⟨r_, n_, l, hrm, hval, hll, hlm⟩ := pensW e (by rw [hens]; exact List.mem_cons_self ..)
        rw [erun, houts] at hrm
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq, true_and] at hrm
        obtain ⟨e1, e2⟩ := hrm
        subst r_ n_
        rw [hv] at hval
        obtain ⟨f2, as2, d2, nums, ha2, hd2, hlen2, hev2, hlt, hlb⟩ := bytes_of_call hown hglen hval
        rw [hfd] at hd2
        injection hd2 with hd2
        subst hd2
        obtain ⟨hl4, hlget⟩ := wordBytes_get nums l hlb
        -- the things the definition is used with there are the keys the verifier holds
        obtain ⟨B, hB⟩ := held_bound HT
        obtain ⟨as, eas, das⟩ := wevalList_sound (ev' := evalSpec ctx.defs (WFUEL + B) (c.envW (afterCall p q i st)))
          (fun e' v' hv' => weval_sound HT wfT hB WFUEL env _ e' v' hv' henv) args vs hwl
        have same : as2 = as := by
          have a1 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.envW (afterCall p q i st)))
            (fun a v hh => evalSpec_mono ctx.defs f2 hh _ (Nat.le_max_left _ _)) args ha2
          have a2 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.envW (afterCall p q i st)))
            (fun a v hh => evalSpec_mono ctx.defs (WFUEL + B) hh _ (Nat.le_max_right _ _)) args eas
          rw [a1] at a2
          injection a2
        subst same
        have ekeys : as2 = plan.keys.map (Key.val ctx s0 ρ plan.terms) := flatKeys_den wfT das hfk
        have hheld : ∃ d', findDef ctx.defs plan.g = some d' ∧ d'.params.length = plan.keys.length ∧
            Value ctx.defs (d'.params.zip (plan.keys.map (Key.val ctx s0 ρ plan.terms))) d'.body (.list (nums.map Val.word)) :=
          ⟨d, hfd, hdl, f2, by rw [← ekeys]; exact hev2⟩
        have hnums : nums.length = n / 4 := by omega
        have hrun : ∀ k, k < n / 4 → ∀ bb, bb < 4 → s2.mem (s0.reg b + 4 * k + bb) = nums.getD k 0 / 256 ^ bb % 256 := by
          intro k hk bb hbb
          have lt' : 4 * k + bb < l.length := by omega
          have := hlm (4 * k + bb) lt'
          rw [s1r, ← Nat.add_assoc] at this
          rw [this, ← getD_of_lt l 0 lt']
          exact hlget k (by omega) bb hbb
        have Hafter := afterCallW_holds E c.stack HT wfT hrsp hg.2 hg.1 hkeep psmall how (show n = 4 * (n / 4) by omega) hnow hmem2
          hnums hlt hrun hkeys hheld
        have wafter := afterCallW_wf wfT sp plan.w (n / 4) plan.g hkeys
        rw [hwords]
        exact ⟨hrip, _, afterRhoW_agree s.nvars ρ s2 nums, by rw [afterCallW_nvars]; show s.nvars ≤ s.nvars + 16 + n / 4; omega, Hafter, wafter⟩

/-- **A call, by contract.** If the verifier has gone through a call, then of the machine at the call: the
address to come back to can be written; the state the called function starts in is one its contract's
caller has seen to; what the called function may touch, this function may touch; and of every state the
contract lets it return in, what the verifier holds after the call is so, at the next instruction. -/
theorem symCall_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCall ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (q : Program) (hq : q.fits) (i : Instr) (hret : p.base + i.next < M64) :
    8 ≤ st.reg RSP ∧ allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true) ∧
    (∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  unfold symCall at h
  split at h
  · exact symCallPlain_sound E h H wf q hq i hret
  · exact symCallW_sound E h H wf q hq i hret

end Ode
