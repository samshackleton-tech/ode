import SoundSpecW
import SoundFrame
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

/-- The run a called function is given to read and write: whole words of one of this function's runs given
to read and write, at the address the register holds, with no single byte of the run written and every
word of the part known written. -/
theorem callRun_spec {ctx : Ctx} {s : Sym} {r n w o : Nat} {ids : List Nat}
    (h : callRun ctx s r n = some (w, o, ids)) :
    ∃ x b n0, ctx.contract.outs[w]? = some (x, b, n0) ∧ (x, b, n0) ∈ ctx.contract.inouts ∧ n % 4 = 0 ∧ 4 * o + n ≤ n0 ∧
      (∀ ρ : Nat → Int, ev ρ (s.reg r) = ρ b + ((4 * o : Nat) : Int)) ∧ (∀ e ∈ s.wrote, e.1 ≠ w) ∧
      writtenIds s.wroteW w (n / 4) o = some ids := by
  unfold callRun at h
  cases hf : findOut (s.reg r) ctx.contract.outs 0 with
  | none => simp [hf] at h
  | some wh =>
    obtain ⟨w', off, name, base, n', rfl, _, hl, ho⟩ := findOut_spec hf
    simp only [Nat.sub_zero] at hl
    cases hc : Lin.isConst off with
    | none => simp [hf, hc] at h
    | some c =>
      simp only [hf, hl, hc] at h
      split at h
      next hcond =>
        obtain ⟨c0, c4, cn, n4, ci, cw⟩ := hcond
        cases hwi : writtenIds s.wroteW w' (n / 4) (c.toNat / 4) with
        | none => simp [hwi] at h
        | some ids' =>
          simp only [hwi, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hreg : ∀ ρ : Nat → Int, ev ρ (s.reg r) = ρ base + ((4 * (c.toNat / 4) : Nat) : Int) := fun ρ => by
            have := ev_isConst (ρ := ρ) hc
            rw [ho, ev_sub, ev_var] at this
            omega
          have hnow : ∀ e ∈ s.wrote, e.1 ≠ w' := fun e me => by
            have := List.all_eq_true.mp cw e me
            simpa using this
          exact ⟨name, base, n', hl, by simpa using ci, n4, by omega, hreg, hnow, hwi⟩
      next => simp at h

/-- The part of a run a called function is given to read, as a run of a fixed count: it lies in one of
this function's runs of a fixed count, or in one of its runs of bytes with a length, at the address the
register holds. So it lies in memory, apart from this function's frame, from the address to return to and
from every run given to write, and holds bytes. -/
theorem fixedPart_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) {r n j b c : Nat} (hr : r < 16) (h : fixedPart ctx s r n = some (j, b, c)) :
    st.reg r = s0.reg b + c ∧ (∃ x n0, ctx.contract.wordRuns[j]? = some (x, b, n0)) ∧
    s0.reg b + c + n ≤ M64 ∧
    (s0.reg b + c + n ≤ s0.reg RSP - ctx.contract.stack ∨ s0.reg RSP + 8 ≤ s0.reg b + c) ∧
    (∀ k, k < n → (s0.mem (s0.reg b + c + k)).val < 256) ∧
    (∀ x' r' n', (x', r', n') ∈ ctx.contract.outs → s0.reg b + c + n ≤ s0.reg r' ∨ s0.reg r' + n' ≤ s0.reg b + c) ∧
    ((∃ x0 n0, (x0, b, n0) ∈ ctx.contract.fixeds ∧ c + n ≤ n0) ∨ (∃ l, (b, l) ∈ ctx.contract.regions ∧ c + n ≤ s0.reg l)) := by
  unfold fixedPart at h
  have hreg := H.reg r hr
  cases hf : findOut (s.reg r) ctx.contract.fixeds 0 with
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
        have hm0 := List.mem_of_getElem? hl
        obtain ⟨f1, f2, f3, f4⟩ := E.fixed hm0
        have := ev_isConst (ρ := ρ) hc
        rw [ho, ev_sub, ev_var, H.entry base (fixeds_lt hm0)] at this
        refine ⟨by omega, ⟨name, n0, wordRuns_of (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl)⟩,
          by omega, by omega, fun k hk => ?_, fun x' r' n' m => ?_, Or.inl ⟨name, n0, hm0, by omega⟩⟩
        · have := f3 (cst.toNat + k) (by omega)
          rwa [← Nat.add_assoc] at this
        · have := f4 x' r' n' m
          omega
      next => simp at h
  | none =>
    simp only [hf] at h
    cases hg : findRegion (s.reg r) ctx.contract.regions 0 with
    | none => simp [hg] at h
    | some wh =>
      obtain ⟨k', o, base, len, rfl, _, hl, ho⟩ := findRegion_spec hg
      simp only [Nat.sub_zero] at hl
      simp only [hg] at h
      cases hc : Lin.isConst o with
      | none => simp [hc] at h
      | some cst =>
        simp only [hc, hl] at h
        split at h
        next hcond =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨c0, hplain⟩ := hcond
          have hm0 := List.mem_of_getElem? hl
          obtain ⟨b16, l16⟩ := regions_lt hm0
          obtain ⟨g1, g2⟩ := E.region hm0
          have hlen := plain_sound hplain ρ H.facts
          rw [ev_sub, ev_var, ev_const, H.entry len l16] at hlen
          have := ev_isConst (ρ := ρ) hc
          rw [ho, ev_sub, ev_var, H.entry base b16] at this
          refine ⟨by omega, ⟨"", 0, ?_⟩, by omega, by omega, fun k hk => ?_, fun x' r' n' m => ?_, Or.inr ⟨len, hm0, by omega⟩⟩
          · unfold Contract.wordRuns
            rw [List.getElem?_append_right (by simp), List.getElem?_map]
            simp only [List.length_append, Nat.add_sub_cancel_left, hl, Option.map_some]
          · have := E.byte hm0 (cst.toNat + k) (by omega)
            rwa [← Nat.add_assoc] at this
          · have := E.outRegion m hm0
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
  | lane j c l => trivial
  | span r off len =>
    have : off.coeff.length ≤ n ∧ len.coeff.length ≤ n := by simpa [Key.ok] using h
    exact this
  | use u => show u < n; simpa [Key.ok] using h

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
theorem wordBytes_range (mem : Nat → Byte) : ∀ (ds : List Nat) (base : Nat),
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
    ∀ x r n, (x, r, n) ∈ fixedsIn args regs →
      (∃ j b cst, fixedPart ctx s r n = some (j, b, cst)) ∨ ∃ cf fids, frameRun s r n = some (cf, fids)
  | [], _, _, _, x, r, n, m => by simp [fixedsIn] at m
  | _ :: _, [], _, _, x, r, n, m => by simp [fixedsIn] at m
  | (y, .number) :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx s ids args regs with
    | none => simp [hrec] at h
    | some env' => simp only [fixedsIn] at m; exact calleeW_fixeds args regs hrec x r n m
  | (y, .fixed n') :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx s ids args regs with
    | none => cases hf : fixedPart ctx s r' n' <;> simp [hf, hrec] at h
    | some env' =>
      simp only [fixedsIn, List.mem_cons] at m
      rcases m with e | m
      · injection e with _ e
        injection e with e1 e2
        subst e1 e2
        cases hf : fixedPart ctx s r n with
        | some pp => obtain ⟨j, b, cst⟩ := pp; exact Or.inl ⟨j, b, cst, rfl⟩
        | none =>
          cases hfr : frameRun s r n with
          | none => simp [hf, hrec, hfr] at h
          | some pr => obtain ⟨cf, fids⟩ := pr; exact Or.inr ⟨cf, fids, rfl⟩
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
      ∀ k, k < n → s1.mem (st.reg r + k) = s0.mem (s0.reg b + cst + k) ∧ (s0.mem (s0.reg b + cst + k)).val < 256)
    (hfr : ∀ r n cf fids, r ∈ argRegs → frameRun s r n = some (cf, fids) →
      (List.range n).map (fun k => Val.int (s1.mem (s1.reg r + k))) = wordBytes (fids.map (den (inpOf ctx s0) ρ T))) :
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
      have ih := calleeW_sound H c hreg hfix hfr args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
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
    | none =>
      cases hrec : calleeW ctx s ids args regs with
      | none => simp [hf, hrec] at h
      | some env' =>
        cases hfrun : frameRun s r n with
        | none => simp [hf, hrec, hfrun] at h
        | some pr =>
          obtain ⟨cf, fids⟩ := pr
          simp only [hf, hrec, hfrun, Option.map_some, Option.some.injEq] at h; subst h
          have ih := calleeW_sound H c hreg hfix hfr args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
            (fun x' r' n' m => hio x' r' n' (inoutsIn_tail (x, .fixed n) r m)) hrec
          simp only [envWIn]
          refine ⟨rfl, ?_, ih⟩
          have e := hfr r n cf fids (hr r (List.mem_cons_self ..)) hfrun
          simp only [Val.bytes, List.map_map]
          show WDen ctx s0 ρ T (.wbytes fids) (.list ((List.range n).map fun k => Val.int (s1.mem (s1.reg r + k))))
          rw [e]
          exact WDen.wbytes fids
    | some pp =>
      obtain ⟨j, b, cst⟩ := pp
      cases hrec : calleeW ctx s ids args regs with
      | none => simp [hf, hrec] at h
      | some env' =>
        simp only [hf, hrec, Option.some.injEq] at h; subst h
        have ih := calleeW_sound H c hreg hfix hfr args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
          (fun x' r' n' m => hio x' r' n' (inoutsIn_tail (x, .fixed n) r m)) hrec
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
  | (x, .inout n) :: args, r :: regs, env, hr, hio, h => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx s ids args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
      have ih := calleeW_sound H c hreg hfix hfr args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
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
    Ext s.terms (termsOf intern nodes s.tab).2.list ∧ TableOk s.nvars (termsOf intern nodes s.tab).2.list := by
  obtain ⟨e, ok, _, _, _⟩ := termsOf_step (mk := intern) (val := fun nd => match nd with | .input _ _ => 0 | _ => 0)
    (inp := fun _ _ => 0) (ρ := fun _ => 0) (nv := s.nvars) (T0 := s.terms) nodes s.tab
    (fun a ma T _ okT => by
      obtain ⟨j, k, rfl⟩ := hn a ma
      exact input_step okT) (Ext.refl _) wf.words.ok
  exact ⟨e, ok⟩

/-! ## The state after the call -/

/-- The terms made for the words of the run the called function wrote, and the table with them. -/
def madeW (s : Sym) (m : Nat) : List Nat × List Node :=
  ((termsOf wAtom ((List.range m).map fun k => Lin.var (s.nvars + 16 + k)) s.tab).1,
   (termsOf wAtom ((List.range m).map fun k => Lin.var (s.nvars + 16 + k)) s.tab).2.list)

theorem afterCallW_facts (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) :
    (s.afterCallW sp w o m g keys b).facts = ((List.range m).map fun k => ranged32 (s.nvars + 16 + k)).flatten ++
      ((callerSaved.map fun r => ranged (s.nvars + r)).flatten ++ s.facts) := rfl
theorem afterCallW_wroteW (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) :
    (s.afterCallW sp w o m g keys b).wroteW = ((List.range m).map fun k => (w, o + k, (madeW s m).1.getD k 0)) ++
      s.wroteW.filter fun e => e.1 != w || decide (e.2.1 < o) || decide (o + m ≤ e.2.1) := rfl
theorem afterCallW_intact (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) :
    (s.afterCallW sp w o m g keys b).intact = s.intact.filter (· != w) := rfl
theorem afterCallW_known (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) :
    (s.afterCallW sp w o m g keys b).known = (if b then Known.heldB g keys (madeW s m).1 else Known.held g keys (madeW s m).1) :: s.known := rfl
theorem afterCallW_terms (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) :
    (s.afterCallW sp w o m g keys b).terms = (madeW s m).2 := rfl
theorem afterCallW_nvars (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) :
    (s.afterCallW sp w o m g keys b).nvars = s.nvars + 16 + m := rfl

/-- The table with the terms of the new words: it has grown at most, is one the verifier may hold with the
new unknowns in use, has one term a word, each in the table. -/
theorem madeW_table {s : Sym} (wf : WF s) (m : Nat) (inp : Nat → Nat → Nat) (ρ : Nat → Int) :
    Ext s.terms (madeW s m).2 ∧ TableOk (s.nvars + 16 + m) (madeW s m).2 ∧ (madeW s m).1.length = m ∧
    (∀ i ∈ (madeW s m).1, i < (madeW s m).2.length) ∧
    ∀ k, k < m → den inp ρ (madeW s m).2 ((madeW s m).1.getD k 0) = (ev ρ (Lin.var (s.nvars + 16 + k)) % W32i).toNat := by
  obtain ⟨ext, ok, len, lt, dn⟩ := termsOf_step (mk := wAtom) (val := fun r => (ev ρ r % W32i).toNat)
    (inp := inp) (ρ := ρ) (nv := s.nvars + 16 + m) (T0 := s.terms)
    ((List.range m).map fun k => Lin.var (s.nvars + 16 + k)) s.tab
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

theorem afterCallW_wf {s : Sym} (wf : WF s) (sp : Int) (w o m : Nat) (g : String) {keys : List Key}
    (hkeys : ∀ k ∈ keys, k.wf s.nvars s.terms.length) (b : Bool) : WF (s.afterCallW sp w o m g keys b) := by
  have le : s.nvars ≤ s.nvars + 16 + m := by omega
  obtain ⟨ext, ok, len, lt, _⟩ := madeW_table wf m (fun _ _ => 0) (fun _ => 0)
  refine ⟨Nat.le_trans wf.base le, ?_, trivial, trivial, ?_, ?_, ?_, ?_, ?_,
    ⟨ok.wf, ok.atoms, (fun x ids h => by simp [Sym.afterCallW] at h), ok.rotrs, ?_, fun _ _ h => nomatch h⟩, ?_, fun _ h => nomatch h⟩
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
    · cases b
      · exact ⟨(Known.wf_mono le ext.le (k := .held g keys []) ⟨hkeys, fun i mi => nomatch mi⟩).1, lt⟩
      · exact ⟨(Known.wf_mono le ext.le (k := .heldB g keys []) ⟨hkeys, fun i mi => nomatch mi⟩).1, lt⟩
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
before but in the called function's frame, at the address it returned to and in the `m` words of the run
`w` from word `o` on; those hold the bytes of the words `nums`; and the definition `g`, used with `keys`,
gives those words. -/
theorem afterCallW_holds {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st s2 : State}
    {sp : Int} (cs : Nat) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hsp : (st.reg RSP : Int) = s0.reg RSP + sp) (hlow : -(ctx.contract.stack : Int) ≤ sp - 8 - cs) (hsp0 : sp ≤ 0)
    (hkeep : ∀ r, r < 16 → callerSaved.contains r = false → s2.reg r = st.reg r)
    (hsmall : ∀ r, s2.reg r < M64)
    {w o m : Nat} {x : String} {b n : Nat} (hw : ctx.contract.outs[w]? = some (x, b, n)) (hn : 4 * (o + m) ≤ n)
    (hnow : ∀ e ∈ s.wrote, e.1 ≠ w)
    (hmem : ∀ a, a + 8 + cs < st.reg RSP ∨ st.reg RSP ≤ a → a < s0.reg b + 4 * o ∨ s0.reg b + 4 * (o + m) ≤ a → s2.mem a = st.mem a)
    (hdata : s2.data = st.data)
    {nums : List Nat} (hlen : nums.length = m) (hlt : ∀ v ∈ nums, v < W32)
    (hrun : ∀ k, k < m → ∀ bb, bb < 4 → s2.mem (s0.reg b + 4 * (o + k) + bb) = nums.getD k 0 / 256 ^ bb % 256)
    {g : String} {keys : List Key} (hkeys : ∀ k ∈ keys, k.wf s.nvars s.terms.length) {bytes : Bool}
    (hheld : ∃ d, findDef ctx.defs g = some d ∧ d.params.length = keys.length ∧
      Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ s.terms))) d.body
        (if bytes then .list (wordBytes nums) else .list (nums.map Val.word))) :
    Holds ctx s0 (afterRhoW s.nvars ρ s2 nums) (s.afterCallW sp w o m g keys bytes) s2 := by
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
  refine ⟨H'.entry, ⟨H'.data.1, hdata.trans H.data.2⟩, ?_, hsmall, trivial, trivial, ?_, ?_, H'.bytes, H'.spec, ?_, ?_, ⟨(fun x ids h => by simp [Sym.afterCallW] at h), ?_, ?_, fun _ _ h => nomatch h⟩, ?_, fun _ h => nomatch h⟩
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
    rw [hmem a hfr (by omega)]
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
    · -- a word of another run, or of this run outside the part written
      obtain ⟨mo, ne⟩ := List.mem_filter.mp mo
      obtain ⟨h1, h2⟩ := H.words.wrote w' j i mo x' r' n' ho'
      have hor := E.out (List.mem_of_getElem? ho')
      refine ⟨h1, fun bb hbb => ?_⟩
      have keep : s2.mem (s0.reg r' + 4 * j + bb) = st.mem (s0.reg r' + 4 * j + bb) := by
        by_cases hww : w' = w
        · subst w'
          rw [hw] at ho'
          injection ho' with ho'
          injection ho' with _ ho'
          injection ho' with hb' hn'
          subst hb' hn'
          have ne' : j < o ∨ o + m ≤ j := by simpa using ne
          exact hmem _ (by omega) (by omega)
        · have ap := E.outOut ho' hw hww
          exact hmem _ (by omega) (by omega)
      rw [keep, h2 bb hbb, afterCallW_terms, hold i (wf.words.wrote w' j i mo)]
  · intro k mk
    rw [afterCallW_known] at mk
    rcases List.mem_cons.mp mk with rfl | mk
    · -- the definition, used with what the called function was given, is the new words, or their bytes
      obtain ⟨d, hd, hlen', hv⟩ := hheld
      have e1 : keys.map (Key.val ctx s0 (afterRhoW s.nvars ρ s2 nums) (madeW s m).2) = keys.map (Key.val ctx s0 ρ s.terms) :=
        List.map_congr_left fun k' mk' => Key.val_mono (hkeys k' mk') ag wf.words.table wf.words.atoms ext
      cases bytes
      · have e2 : (madeW s m).1.map (fun i => Val.word (den (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums) (madeW s m).2 i)) = nums.map Val.word := by
          apply List.ext_getElem
          · simp [len, hlen]
          · intro i h1 h2
            have hi : i < m := by simpa [len] using h1
            have := hden i hi
            rw [getD_of_lt _ _ (by omega), getD_of_lt _ _ (by omega)] at this
            simp only [List.getElem_map, this]
        refine ⟨d, hd, hlen', ?_⟩
        show Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 (afterRhoW s.nvars ρ s2 nums) (madeW s m).2))) d.body
          (.list ((madeW s m).1.map fun i => Val.word (den (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums) (madeW s m).2 i)))
        rw [e1, e2]
        exact hv
      · have e2 : (madeW s m).1.map (fun i => den (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums) (madeW s m).2 i) = nums := by
          apply List.ext_getElem
          · simp [len, hlen]
          · intro i h1 h2
            have hi : i < m := by simpa [len] using h1
            have := hden i hi
            rw [getD_of_lt _ _ (by omega), getD_of_lt _ _ (by omega)] at this
            simp only [List.getElem_map, this]
        refine ⟨d, hd, hlen', ?_⟩
        show Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 (afterRhoW s.nvars ρ s2 nums) (madeW s m).2))) d.body
          (.list (wordBytes ((madeW s m).1.map fun i => den (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums) (madeW s m).2 i)))
        rw [e1, e2]
        exact hv
    · exact Known.holds_mono (wf.known k mk) ag wf.words.table wf.words.atoms ext (H.known k mk)

/-! ## A call that writes words of the frame

The called function is given a part of this function's frame to write (and to read). After it, each word
of the part is a new unknown, and two words make the number of a cell of the frame. -/

theorem afterCallF_facts (s : Sym) (sp c : Int) (m : Nat) (g : String) (keys : List Key) :
    (s.afterCallF sp c m g keys).facts = ((List.range m).map fun k => ranged32 (s.nvars + 16 + k)).flatten ++
      ((callerSaved.map fun r => ranged (s.nvars + r)).flatten ++ s.facts) := rfl
theorem afterCallF_known (s : Sym) (sp c : Int) (m : Nat) (g : String) (keys : List Key) :
    (s.afterCallF sp c m g keys).known = Known.held g keys (madeW s m).1 :: s.known := rfl
theorem afterCallF_terms (s : Sym) (sp c : Int) (m : Nat) (g : String) (keys : List Key) :
    (s.afterCallF sp c m g keys).terms = (madeW s m).2 := rfl
theorem afterCallF_frame (s : Sym) (sp c : Int) (m : Nat) (g : String) (keys : List Key) :
    (s.afterCallF sp c m g keys).frame = ((List.range (m / 2)).map fun (j : Nat) =>
        (c + 8 * (j : Int), Lin.add (Lin.var (s.nvars + 16 + 2 * j)) (Lin.scale W32i (Lin.var (s.nvars + 16 + 2 * j + 1))))) ++
      s.frame.filter fun cell => decide (sp ≤ cell.1) && (decide (cell.1 + 8 ≤ c) || decide (c + 4 * (m : Int) ≤ cell.1)) := rfl

theorem afterCallF_wf {s : Sym} (wf : WF s) (sp c : Int) (m : Nat) (g : String) {keys : List Key}
    (hkeys : ∀ k ∈ keys, k.wf s.nvars s.terms.length) : WF (s.afterCallF sp c m g keys) := by
  have le : s.nvars ≤ s.nvars + 16 + m := by omega
  obtain ⟨ext, ok, len, lt, _⟩ := madeW_table wf m (fun _ _ => 0) (fun _ => 0)
  refine ⟨Nat.le_trans wf.base le, ?_, trivial, trivial, ?_, ?_, ?_, ?_, ?_,
    ⟨ok.wf, ok.atoms, (fun x ids h => by simp [Sym.afterCallF] at h), ok.rotrs, ?_, fun _ _ h => nomatch h⟩, ?_, fun _ h => nomatch h⟩
  · intro r hr
    show bounded (s.nvars + 16 + m) (if callerSaved.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    split
    · exact bounded_var (by omega)
    · exact bounded_mono le (wf.reg r hr)
  · intro o v mm
    rw [afterCallF_frame] at mm
    rcases List.mem_append.mp mm with mn | mo
    · obtain ⟨j, hj, e⟩ := List.mem_map.mp mn
      have hj := List.mem_range.mp hj
      injection e with _ e
      rw [← e]
      exact bounded_add (bounded_var (show s.nvars + 16 + 2 * j < s.nvars + 16 + m by omega))
        (bounded_scale _ (bounded_var (show s.nvars + 16 + 2 * j + 1 < s.nvars + 16 + m by omega)))
    · exact bounded_mono le (wf.frame o v (List.mem_filter.mp mo).1)
  · intro f mf
    rw [afterCallF_facts] at mf
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
    exact Nat.lt_of_lt_of_le (wf.words.wrote w' j i h) ext.le
  · intro k mk
    rw [afterCallF_known] at mk
    rcases List.mem_cons.mp mk with rfl | mk
    · exact ⟨(Known.wf_mono le ext.le (k := .held g keys []) ⟨hkeys, fun i mi => nomatch mi⟩).1, lt⟩
    · exact Known.wf_mono le ext.le (wf.known k mk)

/-- After a call of a function that has written words of the frame, what the verifier then holds is so. -/
theorem afterCallF_holds {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st s2 : State}
    {sp : Int} (cs : Nat) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hsp : (st.reg RSP : Int) = s0.reg RSP + sp) (hlow : -(ctx.contract.stack : Int) ≤ sp - 8 - cs) (hsp0 : sp ≤ 0)
    (hkeep : ∀ r, r < 16 → callerSaved.contains r = false → s2.reg r = st.reg r)
    (hsmall : ∀ r, s2.reg r < M64)
    {c : Int} {m : Nat} (hc : sp ≤ c) (hce : c + 4 * (m : Int) ≤ 0)
    (hmem : ∀ a : Nat, a + 8 + cs < st.reg RSP ∨ st.reg RSP ≤ a →
      (a : Int) < s0.reg RSP + c ∨ (s0.reg RSP : Int) + c + 4 * (m : Int) ≤ a → s2.mem a = st.mem a)
    (hdata : s2.data = st.data)
    {nums : List Nat} (hlen : nums.length = m) (hlt : ∀ v ∈ nums, v < W32)
    (hrun : ∀ k, k < m → load s2.mem (((s0.reg RSP : Int) + c).toNat + 4 * k) 4 = nums.getD k 0)
    {g : String} {keys : List Key} (hkeys : ∀ k ∈ keys, k.wf s.nvars s.terms.length)
    (hheld : ∃ d, findDef ctx.defs g = some d ∧ d.params.length = keys.length ∧
      Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ s.terms))) d.body (.list (nums.map Val.word))) :
    Holds ctx s0 (afterRhoW s.nvars ρ s2 nums) (s.afterCallF sp c m g keys) s2 := by
  have hstack := E.stack
  have ag := afterRhoW_agree s.nvars ρ s2 nums
  have H' := H.agree wf ag
  obtain ⟨ext, ok, len, lt, dn⟩ := madeW_table wf m (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums)
  have hden : ∀ k, k < m → den (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums) (madeW s m).2 ((madeW s m).1.getD k 0) = nums.getD k 0 := by
    intro k hk
    rw [dn k hk, ev_var, afterRhoW_word _ _ _ _ (by omega)]
    have := hlt (nums.getD k 0) (getD_mem _ _ (by omega))
    unfold W32 at this
    unfold W32i
    omega
  have hold : ∀ i, i < s.terms.length →
      den (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums) (madeW s m).2 i = den (inpOf ctx s0) ρ s.terms i :=
    fun i hi => den_mono wf.words.table wf.words.atoms ag ext hi
  refine ⟨H'.entry, ⟨H'.data.1, hdata.trans H.data.2⟩, ?_, hsmall, trivial, trivial, ?_, ?_, H'.bytes, H'.spec, ?_, ?_,
    ⟨(fun x ids h => by simp [Sym.afterCallF] at h), ?_, ?_, fun _ _ h => nomatch h⟩, ?_, fun _ h => nomatch h⟩
  · intro r hr
    show (s2.reg r : Int) = ev _ (if callerSaved.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    cases hcs : callerSaved.contains r with
    | true => rw [if_pos rfl, ev_var, afterRhoW_reg _ _ _ _ hr]
    | false =>
      rw [if_neg (by decide), hkeep r hr hcs]
      exact H'.reg r hr
  · -- the frame's cells: the new ones are two of the new words each; the others were not written
    intro o v mm
    rw [afterCallF_frame] at mm
    rcases List.mem_append.mp mm with mn | mo
    · obtain ⟨j, hj, e⟩ := List.mem_map.mp mn
      have hj := List.mem_range.mp hj
      injection e with e1 e2
      subst e1 e2
      refine ⟨by omega, by omega, ?_⟩
      have a0 : ((s0.reg RSP : Int) + (c + 8 * (j : Int))).toNat = ((s0.reg RSP : Int) + c).toNat + 4 * (2 * j) := by omega
      have a1 : ((s0.reg RSP : Int) + (c + 8 * (j : Int))).toNat + 4 = ((s0.reg RSP : Int) + c).toNat + 4 * (2 * j + 1) := by omega
      have e8 : load s2.mem ((s0.reg RSP : Int) + (c + 8 * (j : Int))).toNat 8 = nums.getD (2 * j) 0 + 4294967296 * nums.getD (2 * j + 1) 0 := by
        rw [load_halves, a1, a0, hrun (2 * j) (by omega), hrun (2 * j + 1) (by omega)]
      have v0 := afterRhoW_word s.nvars ρ s2 nums (k := 2 * j) (by omega)
      have v1 := afterRhoW_word s.nvars ρ s2 nums (k := 2 * j + 1) (by omega)
      rw [show s.nvars + 16 + (2 * j + 1) = s.nvars + 16 + 2 * j + 1 by omega] at v1
      rw [e8, ev_add, ev_scale, ev_var, ev_var, v0, v1]
      unfold W32i
      omega
    · obtain ⟨m1, m2⟩ := List.mem_filter.mp mo
      have m2' : sp ≤ o ∧ (o + 8 ≤ c ∨ c + 4 * (m : Int) ≤ o) := by simpa using m2
      obtain ⟨h1, h2, h3⟩ := H'.frame o v m1
      refine ⟨h1, h2, ?_⟩
      have e : load s2.mem ((s0.reg RSP : Int) + o).toNat 8 = load st.mem ((s0.reg RSP : Int) + o).toNat 8 :=
        load_congr _ _ _ _ (fun a hx1 hx2 => hmem a (Or.inr (by omega)) (by omega))
      rw [e]; exact h3
  · intro f mf
    rw [afterCallF_facts] at mf
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
    have hout : (a : Int) < s0.reg RSP + c ∨ (s0.reg RSP : Int) + c + 4 * (m : Int) ≤ a := by
      simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at ha
      omega
    rw [hmem a hfr hout]
    exact H.mem a ha ho
  · -- what this function wrote for its caller, byte by byte, is of runs that lie apart from the frame
    intro w' o x' mw
    obtain ⟨name, r', n', g1, g2, g3, g4⟩ := H'.wrote w' o x' mw
    refine ⟨name, r', n', g1, g2, g3, ?_⟩
    have ho' := E.out (List.mem_of_getElem? g1)
    rw [hmem _ (by omega) (by omega)]
    exact g4
  · intro w' mw' x' r' n' ho' k hk
    have hor := E.out (List.mem_of_getElem? ho')
    rw [hmem _ (by omega) (by omega)]
    exact H.words.intact w' mw' x' r' n' ho' k hk
  · intro w' j i mw' x' r' n' ho'
    obtain ⟨h1, h2⟩ := H.words.wrote w' j i mw' x' r' n' ho'
    have hor := E.out (List.mem_of_getElem? ho')
    refine ⟨h1, fun bb hbb => ?_⟩
    rw [hmem _ (by omega) (by omega), h2 bb hbb, afterCallF_terms, hold i (wf.words.wrote w' j i mw')]
  · intro k mk
    rw [afterCallF_known] at mk
    rcases List.mem_cons.mp mk with rfl | mk
    · obtain ⟨d, hd, hlen', hv⟩ := hheld
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
      refine ⟨d, hd, hlen', ?_⟩
      show Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 (afterRhoW s.nvars ρ s2 nums) (madeW s m).2))) d.body
        (.list ((madeW s m).1.map fun i => Val.word (den (inpOf ctx s0) (afterRhoW s.nvars ρ s2 nums) (madeW s m).2 i)))
      rw [e1, e2]
      exact hv
    · exact Known.holds_mono (wf.known k mk) ag wf.words.table wf.words.atoms ext (H.known k mk)

/-! ## The call -/

/-- What `callW` has looked up, where it says how the call is taken. -/
theorem callWby_spec {find : Nat → Nat → Option (Nat × Nat × List Nat)} {ctx : Ctx} {s : Sym} {c : Contract} {plan : CallW}
    (h : callWby find ctx s c = .ok plan) :
    ∃ (run : String) (r n : Nat) (e : EnsureW) (ids : List Nat) (env : List (String × WVal)) (args : SExpr) (vs : List WVal) (d : Def),
      c.mbounds = [] ∧ c.outs = [(run, r, n)] ∧ c.inouts = [(run, r, n)] ∧ c.ensuresW = [e] ∧ e.run = run ∧ e.part = none ∧
      find r n = some (plan.w, plan.first, ids) ∧ calleeW ctx s ids c.args argRegs = some env ∧
      e.value = .call "bytes_of" (.cons (.call plan.g args) .nil) ∧ own.contains plan.g = false ∧ plan.g ≠ "len" ∧
      plan.tab = (termsOf intern (partNodes ctx s c.args argRegs) s.tab).2 ∧
      wevalList (weval ctx plan.tab.find { s with tab := plan.tab } WFUEL env) args = some vs ∧
      findDef ctx.defs plan.g = some d ∧ flatKeys plan.tab.find vs = some plan.keys ∧
      (∀ k ∈ plan.keys, k.wf s.nvars plan.terms.length) ∧ d.params.length = plan.keys.length ∧ plan.words = n / 4 := by
  unfold callWby at h
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
            have hs : (((run = run' ∧ r = r') ∧ n = n') ∧ e.run = run) ∧ e.part = none := by simpa using hsame
            obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, erun⟩, epart⟩ := hs
            cases hcr : find r n with
            | none => simp only [hcr] at h; cases h
            | some wi =>
              obtain ⟨w, o, ids⟩ := wi
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
                                  have hok' : (keys.all (Key.ok s.nvars (termsOf intern (partNodes ctx s c.args argRegs) s.tab).2.list.length)) = true := by
                                    simpa using hok
                                  exact ⟨run, r, n, e, ids, env, args, vs, d, hmb', rfl, rfl, rfl, erun, epart, hcr, hce, hv, hown, hlen, rfl, hwl, hfd, hfk,
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

/-- A byte of four that are all bytes: the byte at its place of the number the four are. -/
theorem load4_byteAt (mem : Nat → Byte) (a bb : Nat) (hbb : bb < 4) (h : ∀ k, k < 4 → (mem (a + k)).val < 256) :
    load mem a 4 / 256 ^ bb % 256 = mem (a + bb) := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  rw [Nat.add_zero] at h0
  rw [load4]
  have e2 : a + 1 + 1 = a + 2 := by omega
  have e3 : a + 1 + 1 + 1 = a + 3 := by omega
  rw [e3, e2]
  have hbb' : bb = 0 ∨ bb = 1 ∨ bb = 2 ∨ bb = 3 := by omega
  rcases hbb' with rfl | rfl | rfl | rfl
  · simp only [Nat.pow_zero, Nat.div_one, Nat.add_zero]; omega
  · simp only [Nat.pow_one]; omega
  · rw [show (256 : Nat) ^ 2 = 65536 from rfl]; omega
  · rw [show (256 : Nat) ^ 3 = 16777216 from rfl]; omega

/-- **A call, by contract, of a function that writes a run of words for its caller.** If the verifier has
gone through such a call, then of the machine at the call: the address to come back to can be written; the
state the called function starts in is one its contract's caller has seen to; what the called function may
touch, this function may touch; and of every state the contract lets it return in, what the verifier holds
after the call is so, at the next instruction. -/
theorem symCallW'_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallW' ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (q : Program) (hq : q.fits) (i : Instr) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hal : c.atLeast = []) (hd : c.data = []) :
    8 ≤ st.reg RSP ∧ allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true) ∧
    (∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  cases hsp : s.sp with
  | none => simp only [symCallW', hsp] at h; exact (refuse_ok h).elim
  | some sp =>
    simp only [symCallW', hsp] at h
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
        obtain ⟨run, r, n, e, ids, env, args, vs, d, hmb, houts, hinouts, hens, erun, epart, hcr, hce, hv, hown, hglen, hT, hwl, hfd, hfk,
          hkeys, hdl, hwords⟩ := callWby_spec (find := callRun ctx s) hplan
        obtain ⟨xw, b, n0, how, hio, n4, hfit, hreg_r, hnow, hwi⟩ := callRun_spec hcr
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
        -- the run handed over to be read and written: whole words of one of this function's
        have hwm := List.mem_of_getElem? how
        have hout := E.out hwm
        have rmem : (run, r, n) ∈ c.outs := by rw [houts]; exact List.mem_cons_self ..
        have rarg : r ∈ argRegs := outsIn_mem c.args argRegs run r n rmem
        obtain ⟨r16, rne⟩ := argRegs_not_rsp rarg
        have b16 := outs_lt hwm
        have hrb : st.reg r = s0.reg b + 4 * plan.first := by
          have := H.reg r r16
          rw [hreg_r ρ, H.entry b b16] at this
          omega
        have s1r : (afterCall p q i st).reg r = s0.reg b + 4 * plan.first := by rw [s1reg r rne, hrb]
        have hregions : c.regions = [] := calleeW_regions c c.args argRegs hce
        -- the table with the words of the parts handed over
        obtain ⟨extT, okT⟩ := inputs_table wf (partNodes ctx s c.args argRegs) (partNodes_inputs c.args argRegs)
        rw [← hT] at extT okT
        have CT := Carried.terms H wf extT okT
        have HT := CT.holds
        have wfT := CT.wf
        -- each part handed over to be read lies in one of this function's runs given to read
        have hpart : ∀ x' r' n', (x', r', n') ∈ c.fixeds → r' ∈ argRegs ∧
            ((∃ j b' cst, fixedPart ctx s r' n' = some (j, b', cst)) ∨ ∃ cf fids, frameRun s r' n' = some (cf, fids)) := by
          intro x' r' n' m
          exact ⟨fixedsIn_mem c.args argRegs x' r' n' m, calleeW_fixeds c.args argRegs hce x' r' n' m⟩
        have hfixmem : ∀ r' n' j b' cst, r' ∈ argRegs → fixedPart ctx s r' n' = some (j, b', cst) →
            ∀ k, k < n' → (afterCall p q i st).mem (st.reg r' + k) = s0.mem (s0.reg b' + cst + k) ∧ (s0.mem (s0.reg b' + cst + k)).val < 256 := by
          intro r' n' j b' cst ra hf k hk
          obtain ⟨g3, -, f1, f2, f3, f4, -⟩ := fixedPart_sound E H (argRegs_lt ra) hf
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
        -- the bytes of the part handed over are the bytes of the words known written
        have hidsb : ids.length = n / 4 ∧ ∀ j, j < n / 4 → ∀ bb, bb < 4 →
            (afterCall p q i st).mem (s0.reg b + 4 * (plan.first + j) + bb) = den (inpOf ctx s0) ρ plan.terms (ids.getD j 0) / 256 ^ bb % 256 := by
          obtain ⟨idlen, hwritten⟩ := writtenIds_spec (n / 4) plan.first hwi
          refine ⟨idlen, fun j hj bb hbb => ?_⟩
          have m := hwritten j hj
          obtain ⟨g1, g2⟩ := HT.words.wrote plan.w (plan.first + j) (ids.getD j 0) m xw b n0 how
          rw [s1mem _ (by omega)]
          exact g2 bb hbb
        obtain ⟨idlen, hbytes⟩ := hidsb
        have hiobytes : (List.range n).map (fun k => Val.int ((afterCall p q i st).mem ((afterCall p q i st).reg r + k))) =
            wordBytes (ids.map (den (inpOf ctx s0) ρ plan.terms)) := by
          have := wordBytes_range (afterCall p q i st).mem (ids.map (den (inpOf ctx s0) ρ plan.terms)) ((afterCall p q i st).reg r)
            (fun j hj bb hbb => by
              have hj' : j < ids.length := by simpa using hj
              rw [s1r, show s0.reg b + 4 * plan.first + 4 * j + bb = s0.reg b + 4 * (plan.first + j) + bb by omega,
                hbytes j (by omega) bb hbb, getD_of_lt _ _ hj, getD_of_lt _ _ hj', List.getElem_map])
          rw [List.length_map, idlen, show 4 * (n / 4) = n by omega] at this
          exact this
        -- a part of the frame handed over to be read: where it lies, and that its bytes are the bytes of its words
        have hframe : ∀ r' n' cf fids, r' ∈ argRegs → frameRun s r' n' = some (cf, fids) →
            (afterCall p q i st).reg r' = ((s0.reg RSP : Int) + cf).toNat ∧ sp ≤ cf ∧ cf + n' ≤ 0 ∧
            (List.range n').map (fun k => Val.int ((afterCall p q i st).mem ((afterCall p q i st).reg r' + k))) =
              wordBytes (fids.map (den (inpOf ctx s0) ρ plan.terms)) := by
          intro r' n' cf fids ra hfr
          obtain ⟨⟨sp', hsp', hle⟩, hn0, hn8, hreg', hlen, hwords⟩ := frameRun_sound E H wf (argRegs_lt ra) hfr
          have esp' : sp' = sp := Option.some.inj (hsp'.symm.trans hsp)
          subst esp'
          have hA : (afterCall p q i st).reg r' = ((s0.reg RSP : Int) + cf).toNat := by
            rw [s1reg r' (argRegs_not_rsp ra).2]; omega
          refine ⟨hA, hle, hn0, ?_⟩
          have := wordBytes_range (afterCall p q i st).mem (fids.map (den (inpOf ctx s0) ρ plan.terms)) ((afterCall p q i st).reg r')
            (fun j hj bb hbb => by
              have hj' : j < fids.length := by simpa using hj
              obtain ⟨hlt, hlow, hld⟩ := hwords j (by omega)
              have hb : (st.mem (((s0.reg RSP : Int) + cf).toNat + 4 * j + bb)).val =
                  den (inpOf ctx s0) ρ plan.terms (fids.getD j 0) / 256 ^ bb % 256 := by
                rw [den_ext wf.words.table extT hlt, ← hld]
                exact (load4_byteAt st.mem _ bb hbb (fun _ _ => Fin.isLt _)).symm
              rw [hA, s1mem _ (by omega), hb, getD_of_lt _ _ hj, getD_of_lt _ _ hj', List.getElem_map])
          rw [List.length_map, hlen, show 4 * (n' / 4) = n' by omega] at this
          exact this
        have henv : EnvDen ctx s0 ρ plan.terms env (c.envW (afterCall p q i st)) := by
          rw [envW_plain hl]
          exact calleeW_sound H c (fun r' m => s1reg r' (argRegs_not_rsp m).2) hfixmem
            (fun r' n' cf fids ra hfr => (hframe r' n' cf fids ra hfr).2.2.2) c.args argRegs (fun _ m => m)
            (fun x' r' n' m => by
              have m' : (x', r', n') ∈ c.inouts := m
              rw [hinouts] at m'
              simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m'
              obtain ⟨_, e1, e2⟩ := m'
              subst r' n'
              exact hiobytes) hce
        have hpre : c.pre q (afterCall p q i st) := by
          refine ⟨rfl, ?_, ?_, ?_, hq, ?_, ?_, ?_, ?_, ?_, ?_,
            (fun j x r count l m => by rw [tableAt_none hl] at m; cases m), (fun x k m => by rw [hal] at m; cases m), fun h => absurd hd h⟩
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
            refine ⟨by rw [s1r]; have := hout.1; omega, by rw [s1r, s1rsp]; have := hout.2; omega, ?_⟩
            intro r'' l m'; rw [hregions] at m'; cases m'
          · rw [houts]; exact List.pairwise_singleton _ _
          · intro x' r' n' m
            obtain ⟨ra, hf | hf⟩ := hpart x' r' n' m
            · obtain ⟨j, b', cst, hf⟩ := hf
              obtain ⟨g3, -, f1, f2, f3, f4, -⟩ := fixedPart_sound E H (argRegs_lt ra) hf
              have rne' := (argRegs_not_rsp ra).2
              refine ⟨by rw [s1reg r' rne', g3]; omega, by rw [s1reg r' rne', g3, s1rsp]; omega, ?_⟩
              intro x'' r'' n'' m''
              rw [houts] at m''
              simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
              obtain ⟨_, e1, e2⟩ := m''
              subst r'' n''
              have := f4 xw b n0 hwm
              rw [s1reg r' rne', g3, s1r]
              omega
            · -- a part of the frame: at or above the stack pointer, so apart from the called function's frame
              -- and from the address to return to; apart from the run it writes, which is no part of the frame
              obtain ⟨cf, fids, hfr⟩ := hf
              obtain ⟨hA, hle, hn0, -⟩ := hframe r' n' cf fids ra hfr
              refine ⟨by rw [hA]; omega, by rw [hA, s1rsp]; omega, ?_⟩
              intro x'' r'' n'' m''
              rw [houts] at m''
              simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
              obtain ⟨_, e1, e2⟩ := m''
              subst r'' n''
              rw [hA, s1r]
              omega
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
          simp only [Contract.perm, inLane_false hl, inData_false hd, Bool.or_false, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          left; left
          rcases ha with ((ha | ha) | ha) | ha
          · left; left; left; omega
          · left; left; left; omega
          · rw [hregions] at ha; simp at ha
          · simp only [Contract.inFixed, Bool.or_eq_true] at ha ⊢
            rcases ha with ha | ha
            · obtain ⟨⟨x', r', n'⟩, m, hin⟩ := List.any_eq_true.mp ha
              obtain ⟨ra, hf | hf⟩ := hpart x' r' n' m
              · obtain ⟨j, b', cst, hf⟩ := hf
                obtain ⟨g3, -, -, -, -, -, fw⟩ := fixedPart_sound E H (argRegs_lt ra) hf
                simp only [Bool.and_eq_true, decide_eq_true_eq, s1reg r' (argRegs_not_rsp ra).2, g3] at hin
                rcases fw with ⟨x0, n0, hm0, hle⟩ | ⟨l0, hm0, hle⟩
                · right; left
                  exact List.any_eq_true.mpr ⟨(x0, b', n0), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
                · left; right
                  exact List.any_eq_true.mpr ⟨(b', l0), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
              · -- a part of the frame is within this function's frame
                obtain ⟨cf, fids, hfr⟩ := hf
                obtain ⟨hA, hle, hn0, -⟩ := hframe r' n' cf fids ra hfr
                simp only [Bool.and_eq_true, decide_eq_true_eq, hA] at hin
                left; left; left
                omega
            · right; right
              rw [hinouts] at ha
              simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
              exact List.any_eq_true.mpr ⟨(xw, b, n0), hio, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        have hwrite : ∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true := by
          intro a ha
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          rcases ha with ha | ha
          · left; omega
          · right
            simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
            unfold Contract.inOut
            exact List.any_eq_true.mpr ⟨(xw, b, n0), hwm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        have hwr : allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true := by
          apply allowed_of
          intro x hx1 hx2
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          left; omega
        refine ⟨h8, hwr, hpre, hread, hwrite, ?_⟩
        intro s2 post hdata2
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
        have hmem2 : ∀ a, a + 8 + c.stack < st.reg RSP ∨ st.reg RSP ≤ a →
            a < s0.reg b + 4 * plan.first ∨ s0.reg b + 4 * (plan.first + n / 4) ≤ a → s2.mem a = st.mem a := by
          intro a ha hb
          rw [pmem a (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1rsp]; omega)
            (by simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1r]; omega)]
          exact s1mem a (by omega)
        -- what the contract of the called function says of the run
        obtain ⟨r_, n_, l, hrm, hval, hll, hlm⟩ := (EnsureW.holds_whole epart).mp (pensW e (by rw [hens]; exact List.mem_cons_self ..))
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
        have hrun : ∀ k, k < n / 4 → ∀ bb, bb < 4 → s2.mem (s0.reg b + 4 * (plan.first + k) + bb) = nums.getD k 0 / 256 ^ bb % 256 := by
          intro k hk bb hbb
          have lt' : 4 * k + bb < l.length := by omega
          have := hlm (4 * k + bb) lt'
          rw [s1r, ← Nat.add_assoc] at this
          rw [show s0.reg b + 4 * (plan.first + k) + bb = s0.reg b + 4 * plan.first + 4 * k + bb by omega, this, ← getD_of_lt l 0 lt']
          exact hlget k (by omega) bb hbb
        have Hafter := afterCallW_holds E c.stack HT wfT hrsp hg.2 hg.1 hkeep psmall how (show 4 * (plan.first + n / 4) ≤ n0 by omega) hnow hmem2 hdata2
          hnums hlt hrun hkeys (bytes := false) hheld
        have wafter := afterCallW_wf wfT sp plan.w plan.first (n / 4) plan.g hkeys false
        rw [hwords]
        exact ⟨hrip, _, afterRhoW_agree s.nvars ρ s2 nums, by rw [afterCallW_nvars]; show s.nvars ≤ s.nvars + 16 + n / 4; omega, Hafter, wafter⟩


/-- **A call of a function that writes a part of this function's frame.** As `symCallW'_sound`: the run the
called function reads and writes is a part of the frame, at or above the stack pointer, and after the call
its words are new cells of the frame. -/
theorem symCallF'_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallF' ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (q : Program) (hq : q.fits) (i : Instr) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hal : c.atLeast = []) (hd : c.data = []) :
    8 ≤ st.reg RSP ∧ allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true) ∧
    (∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  cases hsp : s.sp with
  | none => simp only [symCallF', hsp] at h; exact (refuse_ok h).elim
  | some sp =>
    simp only [symCallF', hsp] at h
    split at h
    next => exact (refuse_ok h).elim
    next hguard =>
      have hg : sp ≤ 0 ∧ -(ctx.contract.stack : Int) ≤ sp - 8 - c.stack := by simpa using hguard
      obtain ⟨run0, r, n, houts0⟩ : ∃ run0 r n, c.outs = [(run0, r, n)] := by
        rcases ho : c.outs with _ | ⟨⟨run0, r, n⟩, _ | ⟨o2, omore⟩⟩
        · simp only [ho] at h; exact (refuse_ok h).elim
        · exact ⟨_, _, _, rfl⟩
        · simp only [ho] at h; exact (refuse_ok h).elim
      simp only [houts0] at h
      obtain ⟨⟨cw, ids0⟩, hfw⟩ : ∃ pr, frameRun s r n = some pr := by
        cases hx : frameRun s r n with
        | none => simp only [hx] at h; exact (refuse_ok h).elim
        | some pr => exact ⟨pr, rfl⟩
      simp only [hfw] at h
      split at h
      · exact (refuse_ok h).elim
      rename_i hapart
      have hapart : (c.fixeds.all fun x =>
          match frameAt s x.2.1 with
          | some cf => decide (cf + (x.2.2 : Int) ≤ cw) || decide (cw + (n : Int) ≤ cf)
          | none => true) = true := by
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hapart; exact hapart
      obtain ⟨plan, hplan⟩ : ∃ plan, callWby (fun r n => (frameRun s r n).map fun x => (0, 0, x.2)) ctx s c = .ok plan := by
        cases hx : callWby (fun r n => (frameRun s r n).map fun x => (0, 0, x.2)) ctx s c with
        | error what => simp only [hx] at h; exact (refuse_ok h).elim
        | ok plan => exact ⟨plan, rfl⟩
      simp only [hplan] at h
      obtain ⟨⟨u, items1⟩, r1, hbounds, h⟩ := V.bind_ok h
      have hfin := V.pure_ok h
      injection hfin with hs' _
      subst hs'
      obtain ⟨run, r_, n_, e, ids, env, args, vs, d, hmb, houts, hinouts, hens, erun, epart, hcr, hce, hv, hown, hglen, hT, hwl, hfd, hfk,
        hkeys, hdl, hwords⟩ := callWby_spec hplan
      have e0 : r = r_ ∧ n = n_ := by
        rw [houts0] at houts
        injection houts with e1 _
        injection e1 with _ e2
        injection e2 with e3 e4
        exact ⟨e3, e4⟩
      obtain ⟨rfl, rfl⟩ := e0
      have eids : ids = ids0 := by
        simp only [hfw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcr
        exact hcr.2.2.symm
      subst eids
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
      -- the run handed over to be read and written: a part of this function's frame
      have rmem : (run, r, n) ∈ c.outs := by rw [houts]; exact List.mem_cons_self ..
      have rarg : r ∈ argRegs := outsIn_mem c.args argRegs run r n rmem
      obtain ⟨r16, rne⟩ := argRegs_not_rsp rarg
      obtain ⟨⟨spw, hspw, hlew⟩, hn0w, hn8w, hregr, hidlen, -⟩ := frameRun_sound E H wf r16 hfw
      have espw : sp = spw := Option.some.inj (hsp.symm.trans hspw)
      subst espw
      have s1r : (afterCall p q i st).reg r = ((s0.reg RSP : Int) + cw).toNat := by rw [s1reg r rne]; omega
      have hregions : c.regions = [] := calleeW_regions c c.args argRegs hce
      -- the table with the words of the parts handed over
      obtain ⟨extT, okT⟩ := inputs_table wf (partNodes ctx s c.args argRegs) (partNodes_inputs c.args argRegs)
      rw [← hT] at extT okT
      have CT := Carried.terms H wf extT okT
      have HT := CT.holds
      have wfT := CT.wf
      -- each part handed over to be read lies in one of this function's runs given to read
      have hpart : ∀ x' r' n', (x', r', n') ∈ c.fixeds → r' ∈ argRegs ∧
          ((∃ j b' cst, fixedPart ctx s r' n' = some (j, b', cst)) ∨ ∃ cf fids, frameRun s r' n' = some (cf, fids)) := by
        intro x' r' n' m
        exact ⟨fixedsIn_mem c.args argRegs x' r' n' m, calleeW_fixeds c.args argRegs hce x' r' n' m⟩
      have hfixmem : ∀ r' n' j b' cst, r' ∈ argRegs → fixedPart ctx s r' n' = some (j, b', cst) →
          ∀ k, k < n' → (afterCall p q i st).mem (st.reg r' + k) = s0.mem (s0.reg b' + cst + k) ∧ (s0.mem (s0.reg b' + cst + k)).val < 256 := by
        intro r' n' j b' cst ra hf k hk
        obtain ⟨g3, -, f1, f2, f3, f4, -⟩ := fixedPart_sound E H (argRegs_lt ra) hf
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
      -- a part of the frame handed over to be read: where it lies, and that its bytes are the bytes of its words
      have hframe : ∀ r' n' cf fids, r' ∈ argRegs → frameRun s r' n' = some (cf, fids) →
          (afterCall p q i st).reg r' = ((s0.reg RSP : Int) + cf).toNat ∧ sp ≤ cf ∧ cf + n' ≤ 0 ∧
          (List.range n').map (fun k => Val.int ((afterCall p q i st).mem ((afterCall p q i st).reg r' + k))) =
            wordBytes (fids.map (den (inpOf ctx s0) ρ plan.terms)) := by
        intro r' n' cf fids ra hfr
        obtain ⟨⟨sp', hsp', hle⟩, hn0, hn8, hreg', hlen, hwords⟩ := frameRun_sound E H wf (argRegs_lt ra) hfr
        have esp' : sp' = sp := Option.some.inj (hsp'.symm.trans hsp)
        subst esp'
        have hA : (afterCall p q i st).reg r' = ((s0.reg RSP : Int) + cf).toNat := by
          rw [s1reg r' (argRegs_not_rsp ra).2]; omega
        refine ⟨hA, hle, hn0, ?_⟩
        have := wordBytes_range (afterCall p q i st).mem (fids.map (den (inpOf ctx s0) ρ plan.terms)) ((afterCall p q i st).reg r')
          (fun j hj bb hbb => by
            have hj' : j < fids.length := by simpa using hj
            obtain ⟨hlt, hlow, hld⟩ := hwords j (by omega)
            have hb : (st.mem (((s0.reg RSP : Int) + cf).toNat + 4 * j + bb)).val =
                den (inpOf ctx s0) ρ plan.terms (fids.getD j 0) / 256 ^ bb % 256 := by
              rw [den_ext wf.words.table extT hlt, ← hld]
              exact (load4_byteAt st.mem _ bb hbb (fun _ _ => Fin.isLt _)).symm
            rw [hA, s1mem _ (by omega), hb, getD_of_lt _ _ hj, getD_of_lt _ _ hj', List.getElem_map])
        rw [List.length_map, hlen, show 4 * (n' / 4) = n' by omega] at this
        exact this
      have hiobytes := (hframe r n cw ids rarg hfw).2.2.2
      have henv : EnvDen ctx s0 ρ plan.terms env (c.envW (afterCall p q i st)) := by
        rw [envW_plain hl]
        exact calleeW_sound H c (fun r' m => s1reg r' (argRegs_not_rsp m).2) hfixmem
          (fun r' n' cf fids ra hfr => (hframe r' n' cf fids ra hfr).2.2.2) c.args argRegs (fun _ m => m)
          (fun x' r' n' m => by
            have m' : (x', r', n') ∈ c.inouts := m
            rw [hinouts] at m'
            simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m'
            obtain ⟨_, e1, e2⟩ := m'
            subst r' n'
            exact hiobytes) hce
      have hpre : c.pre q (afterCall p q i st) := by
        refine ⟨rfl, ?_, ?_, ?_, hq, ?_, ?_, ?_, ?_, ?_, ?_,
          (fun j x r count l m => by rw [tableAt_none hl] at m; cases m), (fun x k m => by rw [hal] at m; cases m), fun h => absurd hd h⟩
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
          refine ⟨by rw [s1r]; omega, by rw [s1r, s1rsp]; omega, ?_⟩
          intro r'' l m'; rw [hregions] at m'; cases m'
        · rw [houts]; exact List.pairwise_singleton _ _
        · intro x' r' n' m
          obtain ⟨ra, hf | hf⟩ := hpart x' r' n' m
          · obtain ⟨j, b', cst, hf⟩ := hf
            obtain ⟨g3, -, f1, f2, f3, f4, -⟩ := fixedPart_sound E H (argRegs_lt ra) hf
            have rne' := (argRegs_not_rsp ra).2
            refine ⟨by rw [s1reg r' rne', g3]; omega, by rw [s1reg r' rne', g3, s1rsp]; omega, ?_⟩
            intro x'' r'' n'' m''
            rw [houts] at m''
            simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
            obtain ⟨_, e1, e2⟩ := m''
            subst r'' n''
            rw [s1reg r' rne', g3, s1r]
            omega
          · -- a part of the frame: at or above the stack pointer, so apart from the called function's frame
            -- and from the address to return to; apart from the run it writes, which is no part of the frame
            obtain ⟨cf, fids, hfr⟩ := hf
            obtain ⟨hA, hle, hn0, -⟩ := hframe r' n' cf fids ra hfr
            refine ⟨by rw [hA]; omega, by rw [hA, s1rsp]; omega, ?_⟩
            intro x'' r'' n'' m''
            rw [houts] at m''
            simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
            obtain ⟨_, e1, e2⟩ := m''
            subst r'' n''
            have hdis := List.all_eq_true.mp hapart (x', r', n') m
            simp only [frameRun_at hfr, Bool.or_eq_true, decide_eq_true_eq] at hdis
            rw [hA, s1r]
            omega
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
        simp only [Contract.perm, inLane_false hl, inData_false hd, Bool.or_false, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
        left; left
        rcases ha with ((ha | ha) | ha) | ha
        · left; left; left; omega
        · left; left; left; omega
        · rw [hregions] at ha; simp at ha
        · simp only [Contract.inFixed, Bool.or_eq_true] at ha ⊢
          rcases ha with ha | ha
          · obtain ⟨⟨x', r', n'⟩, m, hin⟩ := List.any_eq_true.mp ha
            obtain ⟨ra, hf | hf⟩ := hpart x' r' n' m
            · obtain ⟨j, b', cst, hf⟩ := hf
              obtain ⟨g3, -, -, -, -, -, fw⟩ := fixedPart_sound E H (argRegs_lt ra) hf
              simp only [Bool.and_eq_true, decide_eq_true_eq, s1reg r' (argRegs_not_rsp ra).2, g3] at hin
              rcases fw with ⟨x0, n0, hm0, hle⟩ | ⟨l0, hm0, hle⟩
              · right; left
                exact List.any_eq_true.mpr ⟨(x0, b', n0), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
              · left; right
                exact List.any_eq_true.mpr ⟨(b', l0), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
            · -- a part of the frame is within this function's frame
              obtain ⟨cf, fids, hfr⟩ := hf
              obtain ⟨hA, hle, hn0, -⟩ := hframe r' n' cf fids ra hfr
              simp only [Bool.and_eq_true, decide_eq_true_eq, hA] at hin
              left; left; left
              omega
          · rw [hinouts] at ha
            simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
            left; left; left
            omega
      have hwrite : ∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true := by
        intro a ha
        simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
        rcases ha with ha | ha
        · left; omega
        · left
          simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
          omega
      have hwr : allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true := by
        apply allowed_of
        intro x hx1 hx2
        simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        left; omega
      refine ⟨h8, hwr, hpre, hread, hwrite, ?_⟩
      intro s2 post hdata2
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
      have hmem2 : ∀ a : Nat, a + 8 + c.stack < st.reg RSP ∨ st.reg RSP ≤ a →
          (a : Int) < s0.reg RSP + cw ∨ (s0.reg RSP : Int) + cw + 4 * ((n / 4 : Nat) : Int) ≤ a → s2.mem a = st.mem a := by
        intro a ha hb
        rw [pmem a (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1rsp]; omega)
          (by simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1r]; omega)]
        exact s1mem a (by omega)
      -- what the contract of the called function says of the run
      obtain ⟨r_, n_, l, hrm, hval, hll, hlm⟩ := (EnsureW.holds_whole epart).mp (pensW e (by rw [hens]; exact List.mem_cons_self ..))
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
      have hrun : ∀ k, k < n / 4 → load s2.mem (((s0.reg RSP : Int) + cw).toNat + 4 * k) 4 = nums.getD k 0 := by
        intro k hk
        apply load4_of_bytes _ _ _ (by have := hlt (nums.getD k 0) (getD_mem _ _ (by omega)); unfold W32 at this; omega)
        intro bb hbb
        have lt' : 4 * k + bb < l.length := by omega
        have := hlm (4 * k + bb) lt'
        rw [s1r, ← Nat.add_assoc] at this
        rw [this, ← getD_of_lt l 0 lt']
        exact hlget k (by omega) bb hbb
      have Hafter := afterCallF_holds E c.stack HT wfT hrsp hg.2 hg.1 hkeep psmall hlew (show cw + 4 * ((n / 4 : Nat) : Int) ≤ 0 by omega) hmem2 hdata2
        hnums hlt hrun hkeys hheld
      have wafter := afterCallF_wf wfT sp cw (n / 4) plan.g hkeys
      rw [hwords]
      exact ⟨hrip, _, afterRhoW_agree s.nvars ρ s2 nums, by show s.nvars ≤ s.nvars + 16 + n / 4; omega, Hafter, wafter⟩

/-- A run given to read and write that nothing was written to yet, taken as written with the words it held
at entry: what the verifier then holds is so of the same machine state. -/
theorem touch_carried {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (w : Nat) : Carried ctx s0 ρ s ρ (s.touch ctx w) st := by
  unfold Sym.touch
  split
  next x b n how =>
    split
    next hc =>
      obtain ⟨hint, hio, n4⟩ := hc
      split
      next j hj =>
        obtain ⟨_, x', n', hj'⟩ := runAt_spec hj
        have hj'' : ctx.contract.wordRuns[j]? = some (x', b, n') := by simpa using hj'
        have hint' : w ∈ s.intact := by simpa using hint
        have hio' : (x, b, n) ∈ ctx.contract.inouts := by simpa using hio
        have hsame : ∀ k, k < n → st.mem (s0.reg b + k) = s0.mem (s0.reg b + k) := H.words.intact w hint' x b n how
        have L := loadWords_terms H wf hj'' (c := 0) (width := n / 4)
          (fun k hk => by rw [Nat.add_zero]; exact hsame k (by omega)) rfl
        dsimp only at L
        rw [show ((List.range (n / 4)).map fun i => Node.input j (0 / 4 + i)) = (List.range (n / 4)).map fun k => Node.input j k from
          List.map_congr_left fun i _ => by simp] at L
        obtain ⟨CT, len, lt, dn⟩ := L
        have HT := CT.holds
        have wfT := CT.wf
        refine ⟨Agree.refl _ _, Nat.le_refl _, ?_, ?_⟩
        · refine ⟨HT.entry, HT.data, HT.reg, HT.small, HT.zf, HT.cf, HT.frame, HT.facts, HT.bytes, HT.spec, HT.mem, HT.wrote,
            ⟨HT.words.vec, (fun w' mw' => HT.words.intact w' (List.mem_filter.mp mw').1), ?_, HT.words.spill⟩, HT.known, HT.range⟩
          intro w' k i mw' x'' r'' n'' ho'
          rcases List.mem_append.mp mw' with mn | mo
          · obtain ⟨k', hk', e⟩ := List.mem_map.mp mn
            have hk' := List.mem_range.mp hk'
            injection e with e1 e
            injection e with e2 e3
            subst e1 e2 e3
            rw [how] at ho'
            injection ho' with ho'
            injection ho' with _ ho'
            injection ho' with hb' hn'
            subst hb' hn'
            refine ⟨by omega, fun bb hbb => ?_⟩
            have hd := dn k' hk'
            rw [Nat.add_zero] at hd
            show st.mem (s0.reg b + 4 * k' + bb) = den (inpOf ctx s0) ρ _ _ / 256 ^ bb % 256
            rw [← hd, load4_byteAt st.mem (s0.reg b + 4 * k') bb hbb (fun q hq => by
              rw [Nat.add_assoc, hsame (4 * k' + q) (by omega)]
              exact E.inoutByte hio' (by omega))]
          · exact HT.words.wrote w' k i mo x'' r'' n'' ho'
        · refine ⟨wfT.base, wfT.reg, wfT.zf, wfT.cf, wfT.frame, wfT.facts, wfT.bytes, wfT.spec, wfT.wrote,
            ⟨wfT.words.table, wfT.words.atoms, wfT.words.vec, wfT.words.rotrs, ?_, wfT.words.spill⟩, wfT.known, wfT.range⟩
          intro w' k i mw'
          rcases List.mem_append.mp mw' with mn | mo
          · obtain ⟨k', hk', e⟩ := List.mem_map.mp mn
            have hk' := List.mem_range.mp hk'
            injection e with _ e
            injection e with _ e
            rw [← e]
            exact lt _ (getD_mem _ _ (by omega))
          · exact wfT.words.wrote w' k i mo
      next => exact Carried.here H wf
    next => exact Carried.here H wf
  next => exact Carried.here H wf

theorem callTouch_carried {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (c : Contract) : Carried ctx s0 ρ s ρ (callTouch ctx s c) st := by
  unfold callTouch
  split
  · split
    · exact touch_carried E H wf _
    · exact Carried.here H wf
  · exact Carried.here H wf

/-! ## Eight bytes of a number stored as two words of a run -/

/-- Eight bytes of a number stored: the number's low half stored as a word, and its high half as the next. -/
theorem store8_words (mem : Nat → Byte) (a x : Nat) : storeWords mem a [x % 4294967296, x / 4294967296] = store mem a x 8 := by
  funext y
  by_cases hy : y < a ∨ a + 8 ≤ y
  · rw [storeWords_other _ _ _ _ (by simpa using hy), store_other _ _ _ _ _ hy]
  · obtain ⟨j, rfl, hj⟩ : ∃ j, y = a + j ∧ j < 8 := ⟨y - a, by omega, by omega⟩
    apply Fin.eq_of_val_eq
    rw [store_at 8 mem a x j hj]
    have e : a + j = a + 4 * (j / 4) + j % 4 := by omega
    rw [e, storeWords_at _ _ _ (j / 4) (j % 4) (by simp only [List.length_cons, List.length_nil]; omega) (by omega)]
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [List.getD] <;> omega

theorem touch_wrote (ctx : Ctx) (s : Sym) (w : Nat) : (s.touch ctx w).wrote = s.wrote := by
  unfold Sym.touch
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

theorem symDivide_wrote (s : Sym) (x : Row) (m : Int) : (symDivide s x m).2.2.wrote = s.wrote := by
  unfold symDivide
  split <;> rfl

/-- **Eight bytes of a number stored into a run given to write, as two words**: the store is allowed, and
what the verifier then holds is so of the machine's state after it. -/
theorem symStore8_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {w n base : Nat} {name : String}
    {o xr : Row} {items rest : Items} {ρ : Nat → Int} {st : State} (a x : Nat)
    (h : symStore8 ctx s w n o xr items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hw : ctx.contract.outs[w]? = some (name, base, n))
    (ha : ∀ c : Int, ev ρ o = c → 0 ≤ c → c + 8 ≤ n → a = s0.reg base + c.toNat)
    (sx : EV.sem ρ s.nvars x (.lin xr)) :
    allowed (ctx.contract.perm s0).write a 8 = true ∧
      ∃ ρ', Carried ctx s0 ρ s ρ' s' { st with mem := store st.mem a x 8 } := by
  unfold symStore8 at h
  cases hc : Lin.isConst o with
  | none => simp only [hc] at h; exact (refuse_ok h).elim
  | some c =>
    simp only [hc] at h
    split at h
    next hcond =>
      obtain ⟨c0, c4, cn, hnw⟩ := hcond
      have hs := V.pure_ok h
      injection hs with h1 _
      subst h1
      have hA : a = s0.reg base + c.toNat := ha c (ev_isConst hc) c0 cn
      have hm := List.mem_of_getElem? hw
      -- the run taken as written with the words it held; the number's high half; the terms of the two words
      have CT := touch_carried E H wf w
      have sxT := EV.sem_agree sx CT.agree CT.mono
      have x0 : 0 ≤ ev ρ xr := by rw [← sxT.2.1]; exact Int.natCast_nonneg _
      obtain ⟨ρ', CD, eq, _, bq, _⟩ := symDivide_sound CT.holds CT.wf sxT.2.2 (show (0 : Int) < W32i by decide) x0
      have sxD := EV.sem_agree sxT CD.agree CD.mono
      have S1 := wAtom_step (inp := inpOf ctx s0) (ρ := ρ') CD.wf.words.ok sxD.2.2
      have S2 := wAtom_step (inp := inpOf ctx s0) (ρ := ρ') S1.ok bq
      have C5 := Carried.terms CD.holds CD.wf (S1.ext.trans S2.ext) S2.ok
      have hnw' : ((symDivide (s.touch ctx w) xr W32i).2.2.wrote.any fun e => e.1 == w) = false := by
        rw [symDivide_wrote, touch_wrote, List.any_eq_false]
        intro e me
        have := List.all_eq_true.mp hnw e me
        simpa using this
      have hx1 := sx.1
      have ex1 := sxT.2.1
      have ex2 := sxD.2.1
      have d1 := S1.den
      have d2 := S2.den
      have d1' := den_ext (inp := inpOf ctx s0) (ρ := ρ') S1.ok.wf S2.ext S1.lt
      have Hs := C5.holds.storeRunWords E hw (c := c.toNat)
        (l := [(wAtom xr (symDivide (s.touch ctx w) xr W32i).2.2.tab).1,
               (wAtom (symDivide (s.touch ctx w) xr W32i).1 (wAtom xr (symDivide (s.touch ctx w) xr W32i).2.2.tab).2).1])
        (lanes := [x % 4294967296, x / 4294967296]) rfl (by omega)
        (by simp only [List.length_cons, List.length_nil]; omega) hnw'
        (fun k hk => by
          have hk : k = 0 ∨ k = 1 := by simp only [List.length_cons, List.length_nil] at hk; omega
          rcases hk with rfl | rfl
          · have e : x % 4294967296 = (ev ρ' xr % W32i).toNat := by unfold W32i; omega
            exact e.trans (d1'.trans d1).symm
          · have e : x / 4294967296 = (ev ρ' (symDivide (s.touch ctx w) xr W32i).1 % W32i).toNat := by
              rw [eq]; unfold M64 at hx1; unfold W32i; omega
            exact e.trans d2.symm) a hA
      rw [store8_words] at Hs
      refine ⟨allowed_of _ _ _ ?_, ρ', CT.then (CD.then (C5.then ⟨Agree.refl _ _, Nat.le_refl _, Hs, ?_⟩))⟩
      · intro y hy1 hy2
        simp only [Contract.perm, Bool.or_eq_true]
        right
        unfold Contract.inOut
        exact List.any_eq_true.mpr ⟨(name, base, n), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
      · have wf5 := C5.wf
        exact ⟨wf5.base, wf5.reg, wf5.zf, wf5.cf, wf5.frame, wf5.facts, wf5.bytes, wf5.spec, wf5.wrote,
          ⟨wf5.words.table, wf5.words.atoms, wf5.words.vec, wf5.words.rotrs,
           fun w' j i m => by
             rcases List.mem_append.mp m with m | m
             · obtain ⟨q, mq, eq'⟩ := List.mem_map.mp m
               have hq : q = 0 ∨ q = 1 := by have := List.mem_range.mp mq; simp only [List.length_cons, List.length_nil] at this; omega
               injection eq' with _ e2
               injection e2 with _ e3
               rw [← e3]
               rcases hq with rfl | rfl
               · exact Nat.lt_of_lt_of_le S1.lt S2.ext.le
               · exact S2.lt
             · exact wf5.words.wrote w' j i (List.mem_filter.mp m).1,
           fun _ _ hs => nomatch hs⟩, wf5.known, fun _ h => nomatch h⟩
    next => exact (refuse_ok h).elim

/-- **A call, by contract, of a function that writes a run of words for its caller**, the run of this
function it is given a part of being first taken as written with the words it held at entry. -/
theorem symCallW_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallW ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (q : Program) (hq : q.fits) (i : Instr) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hal : c.atLeast = []) (hd : c.data = []) :
    8 ≤ st.reg RSP ∧ allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true) ∧
    (∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  have T := callTouch_carried E H wf c
  have F := callFrameTouch_carried (ctx := ctx) (s0 := s0) (ρ := ρ) (st := st) c (c.fixeds ++ c.inouts) T.holds T.wf
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := symCallW'_sound E
    (show symCallW' ctx (callFrameTouch (callTouch ctx s c) c) c items = .ok (s', rest) from h)
    F.holds F.wf q hq i hret hl hal hd
  refine ⟨g1, g2, g3, g4, g5, fun s2 post hdata => ?_⟩
  obtain ⟨hrip, ρ', C⟩ := g6 s2 post hdata
  exact ⟨hrip, ρ', T.then (F.then C)⟩

/-! ## A call of a function that writes a run of bytes -/

/-- What `regionPart` has looked up: the part lies in one of this function's runs of bytes, at the address
the register holds, and is as long as the other register says. -/
theorem regionPart_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) {r l b : Nat} {off n : Row} (hr : r < 16) (hl : l < 16)
    (h : regionPart ctx s r l = some (b, off, n)) :
    ∃ lb, (b, lb) ∈ ctx.contract.regions ∧ n = s.reg l ∧ 0 ≤ ev ρ off ∧ (st.reg r : Int) = s0.reg b + ev ρ off ∧
      ev ρ off + st.reg l ≤ s0.reg lb := by
  have _ := E
  unfold regionPart at h
  cases hf : findRegion (s.reg r) ctx.contract.regions 0 with
  | none => simp [hf] at h
  | some wh =>
    obtain ⟨k, o, base, len, rfl, _, hk, ho⟩ := findRegion_spec hf
    simp only [Nat.sub_zero] at hk
    simp only [hf, hk] at h
    split at h
    next hc =>
      obtain ⟨c1, c2⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨e1, e2, e3⟩ := h
      subst e1 e2 e3
      have hm := List.mem_of_getElem? hk
      obtain ⟨b16, l16⟩ := regions_lt hm
      have g1 := plain_sound c1 ρ H.facts
      have g2 := plain_sound c2 ρ H.facts
      rw [ev_sub, ev_var, ev_add] at g2
      have hreg := H.reg r hr
      have hlen := H.reg l hl
      have hb := H.entry base b16
      have hlb := H.entry len l16
      have eo : ev ρ o = (st.reg r : Int) - s0.reg base := by rw [ho, ev_sub, ev_var, ← hreg, hb]
      exact ⟨len, hm, rfl, g1, by omega, by omega⟩
    next => simp at h

/-- Each run of bytes a called function is given by this rule is a part of one of this function's. -/
theorem calleeB_regions {ctx : Ctx} {s : Sym} (c : Contract) : ∀ (args : List (String × Kind)) (regs : List Nat)
    {env : List (String × WVal)}, calleeB ctx c s args regs = some env →
    ∀ r l, (r, l) ∈ regionsIn c args regs → ∃ b off n, regionPart ctx s r l = some (b, off, n)
  | [], _, _, _, r, l, m => by simp [regionsIn] at m
  | _ :: _, [], _, _, r, l, m => by simp [regionsIn] at m
  | (y, .number) :: args, r' :: regs, env, h, r, l, m => by
    simp only [calleeB] at h
    cases hrec : calleeB ctx c s args regs with
    | none => simp [hrec] at h
    | some env' => simp only [regionsIn] at m; exact calleeB_regions c args regs hrec r l m
  | (y, .bytes len) :: args, r' :: regs, env, h, r, l, m => by
    simp only [calleeB] at h
    cases hl : c.regOf len with
    | none =>
      simp only [hl] at h
      simp only [regionsIn, hl] at m
      exact calleeB_regions c args regs h r l m
    | some l' =>
      simp only [hl] at h
      cases hp : regionPart ctx s r' l' with
      | none => simp [hp] at h
      | some pp =>
        obtain ⟨b, off, n⟩ := pp
        cases hrec : calleeB ctx c s args regs with
        | none => simp [hp, hrec] at h
        | some env' =>
          simp only [regionsIn, hl, List.mem_cons] at m
          rcases m with e | m
          · injection e with e1 e2
            subst e1 e2
            exact ⟨b, off, n, hp⟩
          · exact calleeB_regions c args regs hrec r l m
  | (y, .out n') :: args, r' :: regs, env, h, r, l, m => by
    simp only [calleeB] at h
    simp only [regionsIn] at m
    exact calleeB_regions c args regs h r l m
  | (y, .fixed n') :: args, r' :: regs, env, h, _, _, _ => by simp [calleeB] at h
  | (y, .inout n') :: args, r' :: regs, env, h, _, _, _ => by simp [calleeB] at h

/-- The called function's names on words stand for its names as the account has them in the state it
starts in (`s1`): a number is its register; a part of a run of bytes is the bytes there, as at entry. -/
theorem calleeB_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) {T : List Node}
    (c : Contract) {s1 : State}
    (hreg : ∀ r ∈ argRegs, s1.reg r = st.reg r)
    (hspan : ∀ r l b off n, r ∈ argRegs → l ∈ argRegs → regionPart ctx s r l = some (b, off, n) →
      0 ≤ ev ρ off ∧ (ev ρ n).toNat = s1.reg l ∧ 0 ≤ ev ρ n ∧
      ∀ k, k < s1.reg l → s1.mem (s1.reg r + k) = s0.mem (s0.reg b + (ev ρ off).toNat + k)) :
    ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × WVal)}, (∀ r ∈ regs, r ∈ argRegs) →
      calleeB ctx c s args regs = some env → EnvDen ctx s0 ρ T env (envIn c s1 args regs)
  | [], _, env, _, h => by
    simp only [calleeB, Option.some.injEq] at h; subst h; simp [envIn, EnvDen]
  | _ :: _, [], env, _, h => by
    simp only [calleeB, Option.some.injEq] at h; subst h; simp [envIn, EnvDen]
  | (x, .number) :: args, r :: regs, env, hr, h => by
    simp only [calleeB] at h
    cases hrec : calleeB ctx c s args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
      have ih := calleeB_sound (T := T) H c hreg hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec
      simp only [envIn]
      refine ⟨rfl, ?_, ih⟩
      have ra := hr r (List.mem_cons_self ..)
      have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := T) (s.reg r)
      rw [← H.reg r (argRegs_lt ra), ← hreg r ra] at this
      exact this
  | (x, .bytes len) :: args, r :: regs, env, hr, h => by
    simp only [calleeB] at h
    cases hl : c.regOf len with
    | none =>
      simp only [hl] at h
      simp only [envIn, hl]
      exact calleeB_sound (T := T) H c hreg hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) h
    | some l =>
      simp only [hl] at h
      cases hp : regionPart ctx s r l with
      | none => simp [hp] at h
      | some pp =>
        obtain ⟨b, off, n⟩ := pp
        cases hrec : calleeB ctx c s args regs with
        | none => simp [hp, hrec] at h
        | some env' =>
          simp only [hp, hrec, Option.some.injEq] at h; subst h
          have ih := calleeB_sound (T := T) H c hreg hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec
          simp only [envIn, hl]
          refine ⟨rfl, ?_, ih⟩
          have ra := hr r (List.mem_cons_self ..)
          obtain ⟨o0, en, n0, hm⟩ := hspan r l b off n ra (regOfIn_mem len c.args argRegs l hl) hp
          have e : (List.range (s1.reg l)).map (fun k => Val.int (s1.mem (s1.reg r + k))) =
              (List.range (ev ρ n).toNat).map fun k => Val.int (s0.mem (s0.reg b + (ev ρ off).toNat + k)) := by
            rw [en]
            exact List.map_congr_left fun k mk => by rw [hm k (List.mem_range.mp mk)]
          simp only [Val.bytes, List.map_map]
          show WDen ctx s0 ρ T (.span b off n) (.list ((List.range (s1.reg l)).map fun k => Val.int (s1.mem (s1.reg r + k))))
          rw [e]
          exact WDen.span b off n o0 n0
  | (x, .out n) :: args, r :: regs, env, hr, h => by
    simp only [calleeB] at h
    simp only [envIn]
    exact calleeB_sound (T := T) H c hreg hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) h
  | (x, .fixed n) :: args, r :: regs, env, _, h => by simp [calleeB] at h
  | (x, .inout n) :: args, r :: regs, env, _, h => by simp [calleeB] at h

/-- What `callB` has looked up, where it says how the call is taken. -/
theorem callB_spec {ctx : Ctx} {s : Sym} {c : Contract} {plan : CallW} (h : callB ctx s c = .ok plan) :
    ∃ (run : String) (r n : Nat) (e : Ensure) (ids : List Nat) (env : List (String × WVal)) (args : SExpr) (vs : List WVal) (d : Def),
      c.mbounds = [] ∧ c.fixeds = [] ∧ c.inouts = [] ∧ c.returns = none ∧ c.result = none ∧
      c.outs = [(run, r, n)] ∧ c.ensures = [e] ∧ e.run = run ∧ e.lo = .num 0 ∧ e.hi = .num (n : Int) ∧
      callRun ctx s r n = some (plan.w, plan.first, ids) ∧ calleeB ctx c s c.args argRegs = some env ∧
      e.value = .call plan.g args ∧ own.contains plan.g = false ∧ plan.g ≠ "len" ∧
      wevalList (weval ctx s.tab.find s WFUEL env) args = some vs ∧
      findDef ctx.defs plan.g = some d ∧ flatKeys s.tab.find vs = some plan.keys ∧
      (∀ k ∈ plan.keys, k.wf s.nvars s.terms.length) ∧ d.params.length = plan.keys.length ∧ plan.words = n / 4 := by
  unfold callB at h
  split at h
  next => cases h
  next hguard =>
    have hg' : ((((c.mbounds = [] ∧ c.fixeds = []) ∧ c.inouts = []) ∧ c.ensuresW = []) ∧ c.returns = none) ∧ c.result = none := by
      simpa using hguard
    obtain ⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, _⟩, g5⟩, g6⟩ := hg'
    rcases houts : c.outs with _ | ⟨⟨run, r, n⟩, _ | ⟨o2, omore⟩⟩
    · simp only [houts] at h; cases h
    · rcases hens : c.ensures with _ | ⟨e, _ | ⟨e2, emore⟩⟩
      · simp only [houts, hens] at h; cases h
      · simp only [houts, hens] at h
        split at h
        next a b hlo hhi =>
          split at h
          next => cases h
          next hsame =>
            have hs : (e.run = run ∧ a = 0) ∧ b = (n : Int) := by simpa using hsame
            obtain ⟨⟨erun, ha⟩, hb⟩ := hs
            cases hcr : callRun ctx s r n with
            | none => simp only [hcr] at h; cases h
            | some wi =>
              obtain ⟨w, o, ids⟩ := wi
              simp only [hcr] at h
              cases hce : calleeB ctx c s c.args argRegs with
              | none => simp only [hce] at h; cases h
              | some env =>
                simp only [hce] at h
                cases hv : e.value with
                | call g args =>
                  simp only [hv] at h
                  split at h
                  next hfg =>
                    have hfg' : own.contains g = false ∧ g ≠ "len" := by simpa using hfg
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
                            have hok' : (keys.all (Key.ok s.nvars s.terms.length)) = true := by simpa using hok
                            exact ⟨run, r, n, e, ids, env, args, vs, d, g1, g2, g3, by simpa using g5, by simpa using g6, rfl, rfl, erun,
                              by rw [hlo, ha], by rw [hhi, hb], hcr, rfl, hv, hfg'.1, hfg'.2, hwl, hfd, hfk,
                              (fun k mk => Key.ok_wf (List.all_eq_true.mp hok' k mk)), by simpa using hdl, rfl⟩
                          next => cases h
                      next => cases h
                    next => cases h
                  next => cases h
                | _ => simp only [hv] at h; cases h
        next => cases h
      · simp only [houts, hens] at h; cases h
    · simp only [houts] at h; cases h

/-- An expression that is a number of the text has that number as its value. -/
theorem value_num {defs : List Def} {env : List (String × Val)} {k a : Int} (h : Value defs env (.num k) (.int a)) : a = k := by
  obtain ⟨fuel, hf⟩ := h
  cases fuel with
  | zero => simp [evalSpec] at hf
  | succ f =>
    simp only [evalSpec] at hf
    split at hf
    · injection hf with hf; injection hf with hf; exact hf.symm
    · cases hf

/-- A use of a definition, with its value: the definition, used with the values of the things there, gives it. -/
theorem call_def {defs : List Def} {env : List (String × Val)} {g : String} {args : SExpr} {v : Val}
    (hown : own.contains g = false) (hlen : g ≠ "len") (hv : Value defs env (.call g args) v) :
    ∃ (fuel : Nat) (as : List Val) (d : Def), evalList (evalSpec defs fuel env) args = some as ∧
      findDef defs g = some d ∧ d.params.length = as.length ∧ evalSpec defs fuel (d.params.zip as) d.body = some v := by
  obtain ⟨fuel, hf⟩ := hv
  cases fuel with
  | zero => simp [evalSpec] at hf
  | succ f2 =>
    simp only [evalSpec] at hf
    cases ha : evalList (evalSpec defs f2 env) args with
    | none => simp [ha] at hf
    | some as =>
      have hl : (g == "len") = false := by simpa using hlen
      simp only [ha, hl, hown, Bool.false_eq_true, ↓reduceIte] at hf
      cases hd : findDef defs g with
      | none => simp [hd] at hf
      | some d =>
        simp only [hd] at hf
        split at hf
        next hp => exact ⟨f2, as, d, ha, rfl, by simpa using hp, hf⟩
        next => simp at hf

/-- **A call, by contract, of a function that writes a run of bytes for its caller.** If the verifier has
gone through such a call, then of the machine at the call: the address to come back to can be written; the
state the called function starts in is one its contract's caller has seen to; what the called function may
touch, this function may touch; and of every state the contract lets it return in, what the verifier
holds after the call is so, at the next instruction. -/
theorem symCallB'_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallB' ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (q : Program) (hq : q.fits) (i : Instr) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hal : c.atLeast = []) (hd : c.data = []) :
    8 ≤ st.reg RSP ∧ allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true) ∧
    (∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  cases hsp : s.sp with
  | none => simp only [symCallB', hsp] at h; exact (refuse_ok h).elim
  | some sp =>
    simp only [symCallB', hsp] at h
    split at h
    next => exact (refuse_ok h).elim
    next hguard =>
      have hg : sp ≤ 0 ∧ -(ctx.contract.stack : Int) ≤ sp - 8 - c.stack := by simpa using hguard
      cases hplan : callB ctx s c with
      | error what => simp only [hplan] at h; exact (refuse_ok h).elim
      | ok plan =>
        simp only [hplan] at h
        obtain ⟨⟨u, items1⟩, r1, hbounds, h⟩ := V.bind_ok h
        have hfin := V.pure_ok h
        injection hfin with hs' _
        subst hs'
        obtain ⟨run, r, n, e, ids, env, args, vs, d, hmb, hfx, hinouts, hret0, hres, houts, hens, erun, elo, ehi, hcr, hce, hv, hown, hglen,
          hwl, hfd, hfk, hkeys, hdl, hwords⟩ := callB_spec hplan
        obtain ⟨xw, b, n0, how, hio, n4, hfit, hreg_r, hnow, hwi⟩ := callRun_spec hcr
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
        -- the run handed over to be written: whole words of one of this function's
        have hwm := List.mem_of_getElem? how
        have hout := E.out hwm
        have rmem : (run, r, n) ∈ c.outs := by rw [houts]; exact List.mem_cons_self ..
        have rarg : r ∈ argRegs := outsIn_mem c.args argRegs run r n rmem
        obtain ⟨r16, rne⟩ := argRegs_not_rsp rarg
        have b16 := outs_lt hwm
        have hrb : st.reg r = s0.reg b + 4 * plan.first := by
          have := H.reg r r16
          rw [hreg_r ρ, H.entry b b16] at this
          omega
        have s1r : (afterCall p q i st).reg r = s0.reg b + 4 * plan.first := by rw [s1reg r rne, hrb]
        -- a part of a run of bytes handed over to be read: where it lies, and that memory there is as at entry
        have hspan : ∀ r' l' b' off nn, r' ∈ argRegs → l' ∈ argRegs → regionPart ctx s r' l' = some (b', off, nn) →
            0 ≤ ev ρ off ∧ (ev ρ nn).toNat = (afterCall p q i st).reg l' ∧ 0 ≤ ev ρ nn ∧
            ∀ k, k < (afterCall p q i st).reg l' →
              (afterCall p q i st).mem ((afterCall p q i st).reg r' + k) = s0.mem (s0.reg b' + (ev ρ off).toNat + k) := by
          intro r' l' b' off nn ra la hp
          obtain ⟨lb, g1, g2, g3, g4, g5⟩ := regionPart_sound E H (argRegs_lt ra) (argRegs_lt la) hp
          have hlen := H.reg l' (argRegs_lt la)
          have er := s1reg r' (argRegs_not_rsp ra).2
          have el := s1reg l' (argRegs_not_rsp la).2
          have hregn := E.region g1
          subst g2
          refine ⟨g3, by rw [el, ← hlen]; omega, by rw [← hlen]; omega, fun k hk => ?_⟩
          rw [el] at hk
          have ea : st.reg r' = s0.reg b' + (ev ρ off).toNat := by omega
          rw [er, ea, s1mem _ (by omega)]
          exact H.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (E.region_notOut g1 (by omega) (by omega))
        have hpart : ∀ r' l', (r', l') ∈ c.regions → ∃ b' off nn lb, regionPart ctx s r' l' = some (b', off, nn) ∧ r' ∈ argRegs ∧ l' ∈ argRegs ∧
            (b', lb) ∈ ctx.contract.regions ∧ 0 ≤ ev ρ off ∧ (st.reg r' : Int) = s0.reg b' + ev ρ off ∧ ev ρ off + st.reg l' ≤ s0.reg lb := by
          intro r' l' m
          obtain ⟨b', off, nn, hp⟩ := calleeB_regions c c.args argRegs hce r' l' m
          obtain ⟨ra, len, hlen⟩ := regionsIn_mem c c.args argRegs r' l' m
          have la := regOfIn_mem len c.args argRegs l' hlen
          obtain ⟨lb, g1, _, g3, g4, g5⟩ := regionPart_sound E H (argRegs_lt ra) (argRegs_lt la) hp
          exact ⟨b', off, nn, lb, hp, ra, la, g1, g3, g4, g5⟩
        -- the bytes of the part handed over to be written are bytes: its words are known written
        obtain ⟨idlen, hwritten⟩ := writtenIds_spec (n / 4) plan.first hwi
        have hcell : ∀ j, j < n → (st.mem (s0.reg b + 4 * plan.first + j)).val < 256 := by
          intro j hj
          have m := hwritten (j / 4) (by omega)
          obtain ⟨g1, g2⟩ := H.words.wrote plan.w (plan.first + j / 4) (ids.getD (j / 4) 0) m xw b n0 how
          have := g2 (j % 4) (by omega)
          rw [show s0.reg b + 4 * plan.first + j = s0.reg b + 4 * (plan.first + j / 4) + j % 4 by omega, this]
          exact Nat.mod_lt _ (by decide)
        have henv : EnvDen ctx s0 ρ s.terms env (c.env (afterCall p q i st)) :=
          calleeB_sound H c (fun r' m => s1reg r' (argRegs_not_rsp m).2) hspan c.args argRegs (fun _ m => m) hce
        have hpre : c.pre q (afterCall p q i st) := by
          refine ⟨rfl, ?_, ?_, ?_, hq, ?_, ?_, ?_, ?_, ?_, ?_,
            (fun j x r count l m => by rw [tableAt_none hl] at m; cases m), (fun x k m => by rw [hal] at m; cases m), fun h => absurd hd h⟩
          · intro r'
            by_cases hr : r' = RSP
            · rw [hr, s1rsp]; omega
            · rw [s1reg r' hr]; exact H.small r'
          · rw [s1rsp]; omega
          · rw [s1rsp]; omega
          · intro r' l' m
            obtain ⟨b', off, nn, lb, hp, ra, la, g1, g3, g4, g5⟩ := hpart r' l' m
            have hregn := E.region g1
            have er := s1reg r' (argRegs_not_rsp ra).2
            have el := s1reg l' (argRegs_not_rsp la).2
            exact ⟨by rw [er, el]; omega, by rw [er, el, s1rsp]; omega⟩
          · intro x' r' n' m
            rw [houts] at m
            simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m
            obtain ⟨_, e1, e2⟩ := m
            subst r' n'
            refine ⟨by rw [s1r]; have := hout.1; omega, by rw [s1r, s1rsp]; have := hout.2; omega, ?_⟩
            intro r'' l'' m'
            obtain ⟨b', off, nn, lb, hp, ra, la, g1, g3, g4, g5⟩ := hpart r'' l'' m'
            have ap := E.outRegion hwm g1
            rw [s1r, s1reg r'' (argRegs_not_rsp ra).2, s1reg l'' (argRegs_not_rsp la).2]
            omega
          · rw [houts]; exact List.pairwise_singleton _ _
          · intro x' r' n' m; rw [hfx] at m; cases m
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
          simp only [Contract.perm, inLane_false hl, inData_false hd, Bool.or_false, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          left; left
          rcases ha with ((ha | ha) | ha) | ha
          · left; left; left; omega
          · left; left; left; omega
          · obtain ⟨⟨r', l'⟩, m, hin⟩ := List.any_eq_true.mp ha
            obtain ⟨b', off, nn, lb, hp, ra, la, g1, g3, g4, g5⟩ := hpart r' l' m
            simp only [Bool.and_eq_true, decide_eq_true_eq, s1reg r' (argRegs_not_rsp ra).2, s1reg l' (argRegs_not_rsp la).2] at hin
            left; right
            exact List.any_eq_true.mpr ⟨(b', lb), g1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
          · simp only [Contract.inFixed, hfx, hinouts, List.any_nil, Bool.or_self] at ha
            cases ha
        have hwrite : ∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true := by
          intro a ha
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          rcases ha with ha | ha
          · left; omega
          · right
            simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
            unfold Contract.inOut
            exact List.any_eq_true.mpr ⟨(xw, b, n0), hwm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        have hwr : allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true := by
          apply allowed_of
          intro x hx1 hx2
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          left; omega
        refine ⟨h8, hwr, hpre, hread, hwrite, ?_⟩
        intro s2 post hdata2
        have hbytes2 : ∀ a, s2.mem a = (afterCall p q i st).mem a ∨ (s2.mem a).val < 256 := fun a => Or.inr (s2.mem a).isLt
        obtain ⟨prip, prsp, psaved, pmem, pret, psmall, pens, _⟩ := post
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
        -- returned to and in the part it wrote
        have hmem2 : ∀ a, a + 8 + c.stack < st.reg RSP ∨ st.reg RSP ≤ a →
            a < s0.reg b + 4 * plan.first ∨ s0.reg b + 4 * (plan.first + n / 4) ≤ a → s2.mem a = st.mem a := by
          intro a ha hb
          rw [pmem a (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1rsp]; omega)
            (by simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1r]; omega)]
          exact s1mem a (by omega)
        -- what the contract of the called function says of the run: its bytes are the list the definition gives
        obtain ⟨r_, n_, a_, b_, l, hrm, hlo, hhi, hval, ha0, hab, hbn, hlm⟩ := pens e (by rw [hens]; exact List.mem_cons_self ..)
        rw [erun, houts] at hrm
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq, true_and] at hrm
        obtain ⟨e1, e2⟩ := hrm
        subst r_ n_
        rw [elo] at hlo
        rw [ehi] at hhi
        have ea := value_num hlo
        have eb := value_num hhi
        subst ea eb
        have hll : l.length = n := by omega
        have henvA : c.envAfter (afterCall p q i st) s2 = c.env (afterCall p q i st) := by simp only [Contract.envAfter, hres]
        rw [hv, henvA] at hval
        obtain ⟨f2, as2, d2, ha2, hd2, hlen2, hev2⟩ := call_def hown hglen hval
        rw [hfd] at hd2
        injection hd2 with hd2
        subst hd2
        -- each byte of the part is a byte: it is as it was (the bytes of a word known), or a byte stored
        have hcell2 : ∀ j, j < n → (s2.mem (s0.reg b + 4 * plan.first + j)).val < 256 := by
          intro j hj
          rcases hbytes2 (s0.reg b + 4 * plan.first + j) with hsame | hlt
          · rw [hsame, s1mem _ (by omega)]; exact hcell j hj
          · exact hlt
        -- the words the part holds
        have hnl : ((List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4).length = n / 4 := by simp
        have hlt : ∀ v ∈ (List.range (n / 4)).map (fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4), v < W32 := by
          intro v mv
          obtain ⟨k, _, rfl⟩ := List.mem_map.mp mv
          have := load_lt s2.mem (s0.reg b + 4 * (plan.first + k)) 4
          unfold W32
          exact this
        have hget : ∀ k, k < n / 4 → ((List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4).getD k 0 =
            load s2.mem (s0.reg b + 4 * (plan.first + k)) 4 := by
          intro k hk
          rw [getD_of_lt _ _ (by simpa using hk)]
          simp only [List.getElem_map, List.getElem_range]
        have hrun : ∀ k, k < n / 4 → ∀ bb, bb < 4 → s2.mem (s0.reg b + 4 * (plan.first + k) + bb) =
            ((List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4).getD k 0 / 256 ^ bb % 256 := by
          intro k hk bb hbb
          rw [hget k hk, load4_byteAt s2.mem (s0.reg b + 4 * (plan.first + k)) bb hbb (fun q hq => by
            have := hcell2 (4 * k + q) (by omega)
            rw [show s0.reg b + 4 * (plan.first + k) + q = s0.reg b + 4 * plan.first + (4 * k + q) by omega]
            exact this)]
        -- the list the contract speaks of is the bytes of those words
        have hlb : l.map (fun (x : Nat) => Val.int x) =
            wordBytes ((List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4) := by
          have W := wordBytes_range s2.mem ((List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4)
            (s0.reg b + 4 * plan.first) (fun k hk bb hbb => by
              have hk' : k < n / 4 := by simpa using hk
              rw [show s0.reg b + 4 * plan.first + 4 * k + bb = s0.reg b + 4 * (plan.first + k) + bb by omega]
              exact hrun k hk' bb hbb)
          rw [← W, hnl]
          apply List.ext_getElem
          · simp only [List.length_map, List.length_range]; omega
          · intro k h1 h2
            have hk : k < l.length := by simpa using h1
            have := hlm k hk
            rw [s1r] at this
            simp only [List.getElem_map, List.getElem_range]
            rw [← this]
            simp
        -- the things the definition is used with there are the keys the verifier holds
        obtain ⟨B, hB⟩ := held_bound H
        obtain ⟨as, eas, das⟩ := wevalList_sound (ev' := evalSpec ctx.defs (WFUEL + B) (c.env (afterCall p q i st)))
          (fun e' v' hv' => weval_sound H wf hB WFUEL env _ e' v' hv' henv) args vs hwl
        have same : as2 = as := by
          have a1 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.env (afterCall p q i st)))
            (fun a v hh => evalSpec_mono ctx.defs f2 hh _ (Nat.le_max_left _ _)) args ha2
          have a2 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.env (afterCall p q i st)))
            (fun a v hh => evalSpec_mono ctx.defs (WFUEL + B) hh _ (Nat.le_max_right _ _)) args eas
          rw [a1] at a2
          injection a2
        subst same
        have ekeys : as2 = plan.keys.map (Key.val ctx s0 ρ s.terms) := flatKeys_den wf das hfk
        have hheld : ∃ d', findDef ctx.defs plan.g = some d' ∧ d'.params.length = plan.keys.length ∧
            Value ctx.defs (d'.params.zip (plan.keys.map (Key.val ctx s0 ρ s.terms))) d'.body
              (if true then .list (wordBytes ((List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4))
                else .list (((List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4).map Val.word)) :=
          ⟨d, hfd, hdl, f2, by rw [← ekeys, if_pos rfl, ← hlb]; exact hev2⟩
        have Hafter := afterCallW_holds E c.stack H wf hrsp hg.2 hg.1 hkeep psmall how (show 4 * (plan.first + n / 4) ≤ n0 by omega) hnow hmem2 hdata2
          hnl hlt hrun hkeys (bytes := true) hheld
        have wafter := afterCallW_wf wf sp plan.w plan.first (n / 4) plan.g hkeys true
        rw [hwords]
        exact ⟨hrip, _, afterRhoW_agree s.nvars ρ s2 _, by rw [afterCallW_nvars]; show s.nvars ≤ s.nvars + 16 + n / 4; omega, Hafter, wafter⟩

/-- **A call, by contract, of a function that writes a run of bytes for its caller**, the run of this
function it is given a part of being first taken as written with the words it held at entry. -/
theorem symCallB_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallB ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (q : Program) (hq : q.fits) (i : Instr) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hal : c.atLeast = []) (hd : c.data = []) :
    8 ≤ st.reg RSP ∧ allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true) ∧
    (∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  have T := callTouch_carried E H wf c
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := symCallB'_sound E (show symCallB' ctx (callTouch ctx s c) c items = .ok (s', rest) from h)
    T.holds T.wf q hq i hret hl hal hd
  refine ⟨g1, g2, g3, g4, g5, fun s2 post hdata => ?_⟩
  obtain ⟨hrip, ρ', C⟩ := g6 s2 post hdata
  exact ⟨hrip, ρ', T.then C⟩

/-- Rows the proof file gives and the verifier has shown join the facts (`symKnow`): what the verifier
holds is still so, of the same state of the machine and the same unknowns. (Whatever the advice is: it
only words what is printed where a proof has run out.) -/
theorem symKnow_sound {ctx : Ctx} {s0 : State} {advice : Sym → List Row} {ρ : Nat → Int} {st : State} :
    ∀ (fuel : Nat) {s s' : Sym} {items rest : Items}, symKnow advice fuel s items = .ok (s', rest) →
      Holds ctx s0 ρ s st → WF s → Carried ctx s0 ρ s ρ s' st
  | 0, s, s', items, rest, h, H, wf => by
    simp only [symKnow] at h
    have hs := V.pure_ok h
    injection hs with heq _; subst s'
    exact Carried.here H wf
  | fuel + 1, s, s', items, rest, h, H, wf => by
    simp only [symKnow] at h
    obtain ⟨g, r1, _, h⟩ := V.bind_ok h
    cases g with
    | none =>
      have hs := V.pure_ok h
      injection hs with heq _; subst s'
      exact Carried.here H wf
    | some g =>
      simp only at h
      split at h
      next hb =>
        obtain ⟨_, r2, e2, h⟩ := V.bind_ok h
        have hrow : g.holds ρ := entail_sound e2 ρ H.facts
        have C := symKnow_sound fuel h
          (⟨H.entry, H.data, H.reg, H.small, H.zf, H.cf, H.frame,
            fun g' m => by
              rcases List.mem_cons.mp m with rfl | m
              · exact hrow
              · exact H.facts g' m,
            H.bytes, H.spec, H.mem, H.wrote, H.words, H.known, H.range⟩ :
            Holds ctx s0 ρ { s with facts := g :: s.facts } st)
          ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame,
            fun g' m => by
              rcases List.mem_cons.mp m with rfl | m
              · exact hb
              · exact wf.facts g' m,
            wf.bytes, wf.spec, wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, wf.range⟩
        exact ⟨C.agree, C.mono, C.holds, C.wf⟩
      next => exact (refuse_ok h).elim

/-- A call of a function that writes a part of this function's frame (`symCallF`). -/
theorem symCallF_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallF ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (q : Program) (hq : q.fits) (i : Instr) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hal : c.atLeast = []) (hd : c.data = []) :
    8 ≤ st.reg RSP ∧ allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true) ∧
    (∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  have F := callFrameTouch_carried (ctx := ctx) (s0 := s0) (ρ := ρ) (st := st) c (c.fixeds ++ c.inouts) H wf
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := symCallF'_sound E
    (show symCallF' ctx (callFrameTouch s c) c items = .ok (s', rest) from h) F.holds F.wf q hq i hret hl hal hd
  refine ⟨g1, g2, g3, g4, g5, fun s2 post hdata => ?_⟩
  obtain ⟨hrip, ρ', C⟩ := g6 s2 post hdata
  exact ⟨hrip, ρ', F.then C⟩

/-- A call, by one of the three rules (`symCall'`): see `symCall_sound`. -/
theorem symCall'_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCall' ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (q : Program) (hq : q.fits) (i : Instr) (hret : p.base + i.next < M64) :
    8 ≤ st.reg RSP ∧ allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true) ∧
    (∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  unfold symCall' at h
  split at h
  · exact (refuse_ok h).elim
  next hno =>
    have both : (c.lanes = [] ∧ c.atLeast = []) ∧ c.data = [] := by simpa using hno
    split at h
    · exact symCallPlain_sound E h H wf q hq i hret both.1.1 both.1.2 both.2
    · split at h
      · exact symCallB_sound E h H wf q hq i hret both.1.1 both.1.2 both.2
      · split at h
        · exact symCallF_sound E h H wf q hq i hret both.1.1 both.1.2 both.2
        · exact symCallW_sound E h H wf q hq i hret both.1.1 both.1.2 both.2

/-- **A call, by contract.** If the verifier has gone through a call, then of the machine at the call: the
address to come back to can be written; the state the called function starts in is one its contract's
caller has seen to; what the called function may touch, this function may touch; and of every state the
contract lets it return in, what the verifier holds after the call is so, at the next instruction. (The
rows the proof file gives before the rule, `symKnow`, are shown, and only add to the facts.) -/
theorem symCall_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCall ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (q : Program) (hq : q.fits) (i : Instr) (hret : p.base + i.next < M64) :
    8 ≤ st.reg RSP ∧ allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true) ∧
    (∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  unfold symCall at h
  obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
  have C := symKnow_sound (ctx := ctx) KNOWN e1 H wf
  obtain ⟨h8, hw, hpre, hread, hwrite, hpost⟩ := symCall'_sound E h C.holds C.wf q hq i hret
  refine ⟨h8, hw, hpre, hread, hwrite, fun s2 p2 d2 => ?_⟩
  obtain ⟨hrip, ρ', C'⟩ := hpost s2 p2 d2
  exact ⟨hrip, ρ', ⟨Agree.mono C.mono C'.agree, Nat.le_trans C.mono C'.mono, C'.holds, C'.wf⟩⟩

end Ode
