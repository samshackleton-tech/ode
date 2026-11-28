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
    (H : Holds ctx s0 ρ s st) {r n j b c : Nat} (hr : r < ctx.nreg) (h : fixedPart ctx s r n = some (j, b, c)) :
    st.reg r = s0.reg b + c ∧ (∃ x n0, ctx.contract.wordRuns[j]? = some (x, b, n0)) ∧
    s0.reg b + c + n ≤ M64 ∧
    (s0.reg b + c + n ≤ s0.reg RSP - ctx.contract.stackAt s0 ∨ s0.reg RSP + ctx.contract.slot ≤ s0.reg b + c) ∧
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
        obtain ⟨f1, f2, f3, f4⟩ := E.fixedAt hm0
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
          obtain ⟨g1, g2⟩ := E.regionAt hm0
          have hlen := plain_sound hplain ρ H.facts
          rw [ev_sub, ev_var, ev_const, H.entry len l16] at hlen
          have := ev_isConst (ρ := ρ) hc
          rw [ho, ev_sub, ev_var, H.entry base b16] at this
          refine ⟨by omega, ⟨"", 0, ?_⟩, by omega, by omega, fun k hk => ?_, fun x' r' n' m => ?_, Or.inr ⟨len, hm0, by omega⟩⟩
          · exact wordRuns_of_region hl
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

/-- What `regionPart` has looked up: the part lies in one of this function's runs of bytes, at the address
the register holds, and is as long as the other register says. -/
theorem regionPart_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) {r l b : Nat} {off n : Row} (hr : r < ctx.nreg) (hl : l < ctx.nreg)
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
theorem calleeW_regions {ctx : Ctx} {s : Sym} {ids : List Nat} (c : Contract) : ∀ (args : List (String × Kind)) (regs : List Nat)
    {env : List (String × WVal)}, calleeW ctx c s ids args regs = some env →
    ∀ r l, (r, l) ∈ regionsIn c args regs → ∃ b off n, regionPart ctx s r l = some (b, off, n)
  | [], _, _, _, r, l, m => by simp [regionsIn] at m
  | _ :: _, [], _, _, r, l, m => by simp [regionsIn] at m
  | (x, .number) :: args, r' :: regs, env, h, r, l, m => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx c s ids args regs with
    | none => simp [hrec] at h
    | some env' => simp only [regionsIn] at m; exact calleeW_regions c args regs hrec r l m
  | (x, .fixed n) :: args, r' :: regs, env, h, r, l, m => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx c s ids args regs with
    | none => cases hf : fixedPart ctx s r' n <;> simp [hf, hrec] at h
    | some env' => simp only [regionsIn] at m; exact calleeW_regions c args regs hrec r l m
  | (x, .inout n) :: args, r' :: regs, env, h, r, l, m => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx c s ids args regs with
    | none => simp [hrec] at h
    | some env' => simp only [regionsIn] at m; exact calleeW_regions c args regs hrec r l m
  | (x, .bytes len) :: args, r' :: regs, env, h, r, l, m => by
    simp only [calleeW] at h
    cases hl : c.regOf len with
    | none => simp [hl] at h
    | some l' =>
      simp only [hl] at h
      cases hp : regionPart ctx s r' l' with
      | none => simp [hp] at h
      | some pp =>
        obtain ⟨b, off, n⟩ := pp
        cases hrec : calleeW ctx c s ids args regs with
        | none => simp [hp, hrec] at h
        | some env' =>
          simp only [regionsIn, hl, List.mem_cons] at m
          rcases m with e | m
          · injection e with e1 e2; subst e1 e2; exact ⟨b, off, n, hp⟩
          · exact calleeW_regions c args regs hrec r l m
  | (x, .valArray _ _ _) :: args, r' :: regs, env, h, r, l, m => by
    simp only [calleeW] at h
    simp only [regionsIn] at m
    exact calleeW_regions c args regs h r l m
  | (x, .out n) :: args, r' :: regs, env, h, _, _, _ => by simp [calleeW] at h

/-- Each run of a fixed count it is given is a part of one of this function's. -/
theorem calleeW_fixeds {ctx : Ctx} {c : Contract} {s : Sym} {ids : List Nat} : ∀ (args : List (String × Kind)) (regs : List Nat)
    {env : List (String × WVal)}, calleeW ctx c s ids args regs = some env →
    ∀ x r n, (x, r, n) ∈ fixedsIn args regs →
      (∃ j b cst, fixedPart ctx s r n = some (j, b, cst)) ∨ ∃ cf fids, frameRun s r n = some (cf, fids)
  | [], _, _, _, x, r, n, m => by simp [fixedsIn] at m
  | _ :: _, [], _, _, x, r, n, m => by simp [fixedsIn] at m
  | (y, .number) :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx c s ids args regs with
    | none => simp [hrec] at h
    | some env' => simp only [fixedsIn] at m; exact calleeW_fixeds args regs hrec x r n m
  | (y, .fixed n') :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx c s ids args regs with
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
    cases hrec : calleeW ctx c s ids args regs with
    | none => simp [hrec] at h
    | some env' => simp only [fixedsIn] at m; exact calleeW_fixeds args regs hrec x r n m
  | (y, .bytes len) :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeW] at h
    cases hl : c.regOf len with
    | none => simp [hl] at h
    | some l' =>
      simp only [hl] at h
      cases hp : regionPart ctx s r' l' with
      | none => simp [hp] at h
      | some pp =>
        cases hrec : calleeW ctx c s ids args regs with
        | none => simp [hp, hrec] at h
        | some env' => simp only [fixedsIn] at m; exact calleeW_fixeds args regs hrec x r n m
  | (y, .valArray _ _ _) :: args, r' :: regs, env, h, x, r, n, m => by
    simp only [calleeW] at h
    simp only [fixedsIn] at m
    exact calleeW_fixeds args regs h x r n m
  | (y, .out n') :: args, r' :: regs, env, h, _, _, _, _ => by simp [calleeW] at h

/-- The called function's names on words stand for its names as the account has them in the state it
starts in (`s1`): a number is its register; a part of a run of a fixed count is the bytes there, as at
entry; a part of a run of bytes with a length is the bytes there; the run it reads and writes is the bytes
of the words known written. -/
theorem calleeW_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) {T : List Node}
    (c : Contract) (hm : c.regs = ctx.nreg) {s1 : State} {ids : List Nat}
    (hreg : ∀ r ∈ c.argRegs, s1.reg r = st.reg r)
    (hfix : ∀ r n j b cst, r ∈ c.argRegs → fixedPart ctx s r n = some (j, b, cst) →
      ∀ k, k < n → s1.mem (st.reg r + k) = s0.mem (s0.reg b + cst + k) ∧ (s0.mem (s0.reg b + cst + k)).val < 256)
    (hfr : ∀ r n cf fids, r ∈ c.argRegs → frameRun s r n = some (cf, fids) →
      (List.range n).map (fun k => Val.int (s1.mem (s1.reg r + k))) = wordBytes (fids.map (den (inpOf ctx s0) ρ T)))
    (hspan : ∀ r l b off n, r ∈ c.argRegs → l ∈ c.argRegs → regionPart ctx s r l = some (b, off, n) →
      0 ≤ ev ρ off ∧ (ev ρ n).toNat = s1.reg l ∧ 0 ≤ ev ρ n ∧
      ∀ k, k < s1.reg l → s1.mem (s1.reg r + k) = s0.mem (s0.reg b + (ev ρ off).toNat + k)) :
    ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × WVal)}, (∀ r ∈ regs, r ∈ c.argRegs) →
      (∀ x r n, (x, r, n) ∈ inoutsIn args regs →
        (List.range n).map (fun k => Val.int (s1.mem (s1.reg r + k))) = wordBytes (ids.map (den (inpOf ctx s0) ρ T))) →
      calleeW ctx c s ids args regs = some env → EnvDen ctx s0 ρ T env (envWIn c s1 args regs)
  | [], _, env, _, _, h => by
    simp only [calleeW, Option.some.injEq] at h; subst h; simp [envWIn, EnvDen]
  | _ :: _, [], env, _, _, h => by
    simp only [calleeW, Option.some.injEq] at h; subst h; simp [envWIn, EnvDen]
  | (x, .number) :: args, r :: regs, env, hr, hio, h => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx c s ids args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
      have ih := calleeW_sound H c hm hreg hfix hfr hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
        (fun x' r' n' m => hio x' r' n' (inoutsIn_tail (x, .number) r m)) hrec
      simp only [envWIn]
      refine ⟨rfl, ?_, ih⟩
      have ra := hr r (List.mem_cons_self ..)
      have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := T) (s.reg r)
      rw [← H.reg r (hm ▸ argRegs_lt ra), ← hreg r ra] at this
      exact this
  | (x, .fixed n) :: args, r :: regs, env, hr, hio, h => by
    simp only [calleeW] at h
    cases hf : fixedPart ctx s r n with
    | none =>
      cases hrec : calleeW ctx c s ids args regs with
      | none => simp [hf, hrec] at h
      | some env' =>
        cases hfrun : frameRun s r n with
        | none => simp [hf, hrec, hfrun] at h
        | some pr =>
          obtain ⟨cf, fids⟩ := pr
          simp only [hf, hrec, hfrun, Option.map_some, Option.some.injEq] at h; subst h
          have ih := calleeW_sound H c hm hreg hfix hfr hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
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
      cases hrec : calleeW ctx c s ids args regs with
      | none => simp [hf, hrec] at h
      | some env' =>
        simp only [hf, hrec, Option.some.injEq] at h; subst h
        have ih := calleeW_sound H c hm hreg hfix hfr hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
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
    cases hrec : calleeW ctx c s ids args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
      have ih := calleeW_sound H c hm hreg hfix hfr hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
        (fun x' r' n' m => hio x' r' n' (inoutsIn_tail (x, .inout n) r m)) hrec
      simp only [envWIn]
      refine ⟨rfl, ?_, ih⟩
      have e := hio x r n (by simp [inoutsIn])
      simp only [Val.bytes, List.map_map]
      show WDen ctx s0 ρ T (.wbytes ids) (.list ((List.range n).map fun k => Val.int (s1.mem (s1.reg r + k))))
      rw [e]
      exact WDen.wbytes ids
  | (x, .bytes len) :: args, r :: regs, env, hr, hio, h => by
    simp only [calleeW] at h
    cases hl : c.regOf len with
    | none => simp [hl] at h
    | some l =>
      simp only [hl] at h
      cases hp : regionPart ctx s r l with
      | none => simp [hp] at h
      | some pp =>
        obtain ⟨b, off, n⟩ := pp
        cases hrec : calleeW ctx c s ids args regs with
        | none => simp [hp, hrec] at h
        | some env' =>
          simp only [hp, hrec, Option.some.injEq] at h; subst h
          have ih := calleeW_sound H c hm hreg hfix hfr hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
            (fun x' r' n' m => hio x' r' n' (inoutsIn_tail (x, .bytes len) r m)) hrec
          simp only [envWIn, hl]
          refine ⟨rfl, ?_, ih⟩
          have ra := hr r (List.mem_cons_self ..)
          obtain ⟨o0, en, n0, hm⟩ := hspan r l b off n ra (regOfIn_mem len c.args c.argRegs l hl) hp
          have e : (List.range (s1.reg l)).map (fun k => Val.int (s1.mem (s1.reg r + k))) =
              (List.range (ev ρ n).toNat).map fun k => Val.int (s0.mem (s0.reg b + (ev ρ off).toNat + k)) := by
            rw [en]
            exact List.map_congr_left fun k mk => by rw [hm k (List.mem_range.mp mk)]
          simp only [Val.bytes, List.map_map]
          show WDen ctx s0 ρ T (.span b off n) (.list ((List.range (s1.reg l)).map fun k => Val.int (s1.mem (s1.reg r + k))))
          rw [e]
          exact WDen.span b off n o0 n0
  | (x, .valArray len ch el) :: args, r :: regs, env, hr, hio, h => by
    simp only [calleeW] at h
    simp only [envWIn]
    exact calleeW_sound H c hm hreg hfix hfr hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m))
      (fun x' r' n' m => hio x' r' n' (inoutsIn_tail (x, .valArray len ch el) r m)) h
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
  | (x, .valArray _ _ _) :: args, r :: regs, nd, m => by simp only [partNodes] at m; exact partNodes_inputs args regs nd m

/-- With words of runs put into it, the table is still one the verifier may hold, and has grown at most. -/
theorem inputs_table {s : Sym} (wf : WF ctx s) (nodes : List Node) (hn : ∀ nd ∈ nodes, ∃ j k, nd = Node.input j k) :
    Ext s.terms (termsOf intern nodes s.tab).2.list ∧ TableOk s.nvars (termsOf intern nodes s.tab).2.list := by
  obtain ⟨e, ok, _, _, _⟩ := termsOf_step (mk := intern) (val := fun nd => match nd with | .input _ _ => 0 | _ => 0)
    (inp := fun _ _ => 0) (ρ := fun _ => 0) (nv := s.nvars) (T0 := s.terms) nodes s.tab
    (fun a ma T _ okT => by
      obtain ⟨j, k, rfl⟩ := hn a ma
      exact input_step okT) (Ext.refl _) wf.words.ok
  exact ⟨e, ok⟩

/-! ## The state after the call -/

/-- The terms made for the words of the run the called function wrote, and the table with them. -/
def madeW (R : Nat) (s : Sym) (m : Nat) : List Nat × List Node :=
  ((termsOf wAtom ((List.range m).map fun k => Lin.var (s.nvars + R + k)) s.tab).1,
   (termsOf wAtom ((List.range m).map fun k => Lin.var (s.nvars + R + k)) s.tab).2.list)

theorem afterCallW_facts (ct : Contract) (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) (rfs : List RecField) :
    (s.afterCallW ct sp w o m g keys b rfs).facts =
      (if !rfs.isEmpty then recBoundFacts (s.nvars + ct.regs) 0 rfs else []) ++
      ((List.range m).map fun k => ranged32 (s.nvars + ct.regs + k)).flatten ++
      ((ct.scratch.map fun r => ranged (s.nvars + r)).flatten ++ s.facts) := rfl
theorem afterCallW_wroteW (ct : Contract) (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) (rfs : List RecField) :
    (s.afterCallW ct sp w o m g keys b rfs).wroteW = ((List.range m).map fun k => (w, o + k, (madeW ct.regs s m).1.getD k 0)) ++
      s.wroteW.filter fun e => e.1 != w || decide (e.2.1 < o) || decide (o + m ≤ e.2.1) := rfl
theorem afterCallW_intact (ct : Contract) (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) (rfs : List RecField) :
    (s.afterCallW ct sp w o m g keys b rfs).intact = s.intact.filter (· != w) := rfl
theorem afterCallW_known (ct : Contract) (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) (rfs : List RecField) :
    (s.afterCallW ct sp w o m g keys b rfs).known =
      (if !rfs.isEmpty then [Known.use g keys (s.nvars + ct.regs + m), Known.record (s.nvars + ct.regs + m) rfs (madeW ct.regs s m).1]
       else [if b then Known.heldB g keys (madeW ct.regs s m).1 else Known.held g keys (madeW ct.regs s m).1]) ++ s.known := rfl
theorem afterCallW_terms (ct : Contract) (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) (rfs : List RecField) :
    (s.afterCallW ct sp w o m g keys b rfs).terms = (madeW ct.regs s m).2 := rfl
theorem afterCallW_nvars (ct : Contract) (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (b : Bool) (rfs : List RecField) :
    (s.afterCallW ct sp w o m g keys b rfs).nvars = s.nvars + ct.regs + m + (if !rfs.isEmpty then 1 else 0) := rfl

theorem recBoundFacts_wf (base nv : Nat) : ∀ (off : Nat) (rfs : List RecField),
    base + off + (rfs.map RecField.nwords).sum ≤ nv → ∀ f ∈ recBoundFacts base off rfs, bounded nv f
  | _, [], _, _, hm => nomatch hm
  | off, .words _ n :: rest, hle, f, hm =>
    recBoundFacts_wf base nv (off + n) rest (by simp [RecField.nwords] at hle ⊢; omega) f hm
  | off, .bytes _ n :: rest, hle, f, hm =>
    recBoundFacts_wf base nv (off + n / 4) rest (by simp [RecField.nwords] at hle ⊢; omega) f hm
  | off, .u64 _ bd :: rest, hle, f, hm => by
    simp only [RecField.nwords, List.map_cons, List.sum_cons] at hle
    simp only [recBoundFacts, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact bounded_sub (bounded_const _ _) (bounded_add (bounded_var (by omega)) (bounded_scale _ (bounded_var (by omega))))
    · exact recBoundFacts_wf base nv (off + 2) rest (by omega) f hm

theorem recBoundFacts_holds (base : Nat) (ρ : Nat → Int) (nums : List Nat) :
    ∀ (off : Nat) (rfs : List RecField) (fvs : List (String × Val)),
      RecFieldsHolds rfs (nums.drop off) fvs →
      (∀ k, off ≤ k → k < nums.length → ρ (base + k) = nums.getD k 0) →
      ∀ f ∈ recBoundFacts base off rfs, f.holds ρ
  | _, [], _, _, _, _, hm => nomatch hm
  | off, .words fn n :: rest, fvs, hr, hρ, f, hm => by
    cases fvs with
    | nil => exact hr.elim
    | cons fv frest =>
      obtain ⟨x, v⟩ := fv
      cases v with
      | list vs =>
        obtain ⟨_, _, _, hr'⟩ := hr
        rw [List.drop_drop] at hr'
        exact recBoundFacts_holds base ρ nums (off + n) rest frest hr' (fun k hk1 hk2 => hρ k (by omega) hk2) f hm
      | _ => exact hr.elim
  | off, .bytes fn n :: rest, fvs, hr, hρ, f, hm => by
    cases fvs with
    | nil => exact hr.elim
    | cons fv frest =>
      obtain ⟨x, v⟩ := fv
      cases v with
      | list vs =>
        obtain ⟨_, _, _, _, hr'⟩ := hr
        rw [List.drop_drop] at hr'
        exact recBoundFacts_holds base ρ nums (off + n / 4) rest frest hr' (fun k hk1 hk2 => hρ k (by omega) hk2) f hm
      | _ => exact hr.elim
  | off, .u64 fn bd :: rest, fvs, hr, hρ, f, hm => by
    cases hd : nums.drop off with
    | nil => rw [hd] at hr; exact hr.elim
    | cons lo d1 =>
      cases d1 with
      | nil => rw [hd] at hr; exact hr.elim
      | cons hi d2 =>
        rw [hd] at hr
        cases fvs with
        | nil => exact hr.elim
        | cons fv frest =>
          obtain ⟨x, v⟩ := fv
          cases v with
          | int v0 =>
            obtain ⟨_, _, hvlt, _, hveq, _, _, hr'⟩ := hr
            have hlen : off + 2 ≤ nums.length := by
              have := congrArg List.length hd; simp only [List.length_drop, List.length_cons] at this; omega
            have hlo : nums.getD off 0 = lo := by
              have hg : nums[off]? = (nums.drop off)[0]? := by rw [List.getElem?_drop, Nat.add_zero]
              rw [hd] at hg; simp [List.getD, hg]
            have hhi : nums.getD (off + 1) 0 = hi := by
              have hg : nums[off + 1]? = (nums.drop off)[1]? := by rw [List.getElem?_drop]
              rw [hd] at hg; simp [List.getD, hg]
            have hd2 : nums.drop (off + 2) = d2 := by
              rw [← List.drop_drop, hd]; rfl
            simp only [recBoundFacts, List.mem_cons] at hm
            rcases hm with rfl | hm
            · rw [holds_iff, ev_sub, ev_const, ev_add, ev_scale, ev_var, ev_var,
                  hρ off (by omega) (by omega),
                  show base + off + 1 = base + (off + 1) by omega,
                  hρ (off + 1) (by omega) (by omega), hlo, hhi]
              omega
            · exact recBoundFacts_holds base ρ nums (off + 2) rest frest (by rw [hd2]; exact hr')
                (fun k hk1 hk2 => hρ k (by omega) hk2) f hm
          | _ => exact hr.elim

/-- The table with the terms of the new words: it has grown at most, is one the verifier may hold with the
new unknowns in use, has one term a word, each in the table. -/
theorem madeW_table {ctx : Ctx} {s : Sym} (wf : WF ctx s) (R m : Nat) (inp : Nat → Nat → Nat) (ρ : Nat → Int) :
    Ext s.terms (madeW R s m).2 ∧ TableOk (s.nvars + R + m) (madeW R s m).2 ∧ (madeW R s m).1.length = m ∧
    (∀ i ∈ (madeW R s m).1, i < (madeW R s m).2.length) ∧
    ∀ k, k < m → den inp ρ (madeW R s m).2 ((madeW R s m).1.getD k 0) = (ev ρ (Lin.var (s.nvars + R + k)) % W32i).toNat := by
  obtain ⟨ext, ok, len, lt, dn⟩ := termsOf_step (mk := wAtom) (val := fun r => (ev ρ r % W32i).toNat)
    (inp := inp) (ρ := ρ) (nv := s.nvars + R + m) (T0 := s.terms)
    ((List.range m).map fun k => Lin.var (s.nvars + R + k)) s.tab
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

theorem afterCallW_wf {ctx : Ctx} {s : Sym} (wf : WF ctx s) (ct : Contract) (hm : ct.regs = ctx.nreg) (sp : Int) (w o m : Nat) (g : String) {keys : List Key}
    (hkeys : ∀ k ∈ keys, k.wf s.nvars s.terms.length) (b : Bool) (rfs : List RecField := [])
    (hsum : !rfs.isEmpty → (rfs.map RecField.nwords).sum ≤ m) : WF ctx (s.afterCallW ct sp w o m g keys b rfs) := by
  let nv := s.nvars + ct.regs + m + (if !rfs.isEmpty then 1 else 0)
  have le : s.nvars ≤ nv := by omega
  have lem : s.nvars + ct.regs + m ≤ nv := by omega
  obtain ⟨ext, ok, len, lt, _⟩ := madeW_table wf ct.regs m (fun _ _ => 0) (fun _ => 0)
  have ok' := ok.mono lem
  refine ⟨Nat.le_trans wf.base le, ?_, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨ok'.wf, ok'.atoms, (fun x ids h => by simp [Sym.afterCallW] at h), ok'.rotrs, ?_, fun _ _ h => nomatch h⟩, ?_, fun _ h => nomatch h⟩
  · intro r hr
    show bounded nv (if ct.scratch.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    split
    · exact bounded_var (by omega)
    · exact bounded_mono le (wf.reg r hr)
  · intro o v mm
    exact bounded_mono le (wf.frame o v (List.mem_filter.mp mm).1)
  · intro o i mm
    exact Nat.lt_of_lt_of_le (wf.frameW o i (List.mem_filter.mp mm).1) ext.le
  · intro f mf
    rw [afterCallW_facts] at mf
    show bounded nv f
    rcases List.mem_append.mp mf with mf | mf
    · rcases List.mem_append.mp mf with mf | mf
      · split at mf
        next hne =>
          have hs := hsum hne
          exact recBoundFacts_wf (s.nvars + ct.regs) nv 0 rfs (by omega) f mf
        next => cases mf
      · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
        have hk := List.mem_range.mp hk
        simp only [ranged32, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with rfl | rfl
        · exact bounded_var (by omega)
        · exact bounded_sub (bounded_const _ _) (bounded_var (by omega))
    · rcases List.mem_append.mp mf with mf | mf
      · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        have hr := scratch_lt hr
        simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with rfl | rfl
        · exact bounded_var (by omega)
        · exact bounded_sub (bounded_const _ _) (bounded_var (by omega))
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
    rcases List.mem_append.mp mk with mk | mk
    · split at mk
      next hne =>
        have hnv : s.nvars + ct.regs + m < nv := by simp [nv, hne]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at mk
        rcases mk with rfl | rfl
        · exact ⟨(Known.wf_mono le ext.le (k := .held g keys []) ⟨hkeys, fun _ m => nomatch m⟩).1, hnv⟩
        · exact ⟨hnv, lt⟩
      next =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at mk
        subst mk
        cases b
        · exact ⟨(Known.wf_mono le ext.le (k := .held g keys []) ⟨hkeys, fun _ m => nomatch m⟩).1, lt⟩
        · exact ⟨(Known.wf_mono le ext.le (k := .heldB g keys []) ⟨hkeys, fun _ m => nomatch m⟩).1, lt⟩
    · exact Known.wf_mono le ext.le (wf.known k mk)

/-- What the unknowns are after such a call: those made for the registers are what the registers then hold,
those made for the words of the run are the words, and (for a serialized record) one more holds the encoded
record value. -/
noncomputable def afterRhoW (R n : Nat) (ρ : Nat → Int) (s2 : State) (nums : List Nat) (recVal : Option Val := none) : Nat → Int :=
  fun k => if n ≤ k ∧ k < n + R then (s2.reg (k - n) : Int)
    else if n + R ≤ k ∧ k < n + R + nums.length then (nums.getD (k - (n + R)) 0 : Int)
    else if k = n + R + nums.length then match recVal with | some v => (v.code : Int) | none => ρ k
    else ρ k

theorem afterRhoW_agree (R n : Nat) (ρ : Nat → Int) (s2 : State) (nums : List Nat) (recVal : Option Val := none) :
    Agree n ρ (afterRhoW R n ρ s2 nums recVal) := by
  intro k hk
  show ρ k = if n ≤ k ∧ k < n + R then (s2.reg (k - n) : Int)
    else if n + R ≤ k ∧ k < n + R + nums.length then (nums.getD (k - (n + R)) 0 : Int)
    else if k = n + R + nums.length then match recVal with | some v => (v.code : Int) | none => ρ k
    else ρ k
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem afterRhoW_reg (R n : Nat) (ρ : Nat → Int) (s2 : State) (nums : List Nat) (recVal : Option Val := none) {r : Nat} (hr : r < R) :
    afterRhoW R n ρ s2 nums recVal (n + r) = s2.reg r := by
  show (if n ≤ n + r ∧ n + r < n + R then (s2.reg (n + r - n) : Int)
    else if n + R ≤ n + r ∧ n + r < n + R + nums.length then (nums.getD (n + r - (n + R)) 0 : Int)
    else if n + r = n + R + nums.length then match recVal with | some v => (v.code : Int) | none => ρ (n + r)
    else ρ (n + r)) = s2.reg r
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

theorem afterRhoW_word (R n : Nat) (ρ : Nat → Int) (s2 : State) (nums : List Nat) (recVal : Option Val := none) {k : Nat} (hk : k < nums.length) :
    afterRhoW R n ρ s2 nums recVal (n + R + k) = nums.getD k 0 := by
  show (if n ≤ n + R + k ∧ n + R + k < n + R then (s2.reg (n + R + k - n) : Int)
    else if n + R ≤ n + R + k ∧ n + R + k < n + R + nums.length then (nums.getD (n + R + k - (n + R)) 0 : Int)
    else if n + R + k = n + R + nums.length then match recVal with | some v => (v.code : Int) | none => ρ (n + R + k)
    else ρ (n + R + k)) = nums.getD k 0
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem afterRhoW_rec (R n : Nat) (ρ : Nat → Int) (s2 : State) (nums : List Nat) (v : Val) :
    afterRhoW R n ρ s2 nums (some v) (n + R + nums.length) = (v.code : Int) := by
  show (if n ≤ n + R + nums.length ∧ n + R + nums.length < n + R then _
    else if n + R ≤ n + R + nums.length ∧ n + R + nums.length < n + R + nums.length then _
    else if n + R + nums.length = n + R + nums.length then (v.code : Int)
    else _) = (v.code : Int)
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- Of the machine's state when the called function has returned, what the verifier holds after the call is
so: given that the registers a callee keeps and the stack pointer are as before the call; memory is as
before but in the called function's frame, at the address it returned to and in the `m` words of the run
`w` from word `o` on; those hold the bytes of the words `nums`; and the definition `g`, used with `keys`,
gives those words (or a serialized record). -/
theorem afterCallW_holds {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st s2 : State}
    {sp : Int} (ct : Contract) (cst : Nat) (hm : ct.regs = ctx.nreg) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (hsp : (st.reg RSP : Int) = s0.reg RSP + sp) (hlow : -(ctx.contract.stackAt s0 : Int) ≤ sp - cst) (hsp0 : sp ≤ 0)
    (hkeep : ∀ r, r < ctx.nreg → ct.scratch.contains r = false → s2.reg r = st.reg r)
    (hsmall : ∀ r, s2.reg r < M64)
    {w o m : Nat} {x : String} {b n : Nat} (hw : ctx.contract.outs[w]? = some (x, b, n)) (hn : 4 * (o + m) ≤ n)
    (hnow : ∀ e ∈ s.wrote, e.1 ≠ w)
    (hmem : ∀ a, a + cst < st.reg RSP ∨ st.reg RSP ≤ a → a < s0.reg b + 4 * o ∨ s0.reg b + 4 * (o + m) ≤ a → s2.mem a = st.mem a)
    (hdata : s2.data = st.data)
    {nums : List Nat} (hlen : nums.length = m) (hlt : ∀ v ∈ nums, v < W32)
    (hrun : ∀ k, k < m → ∀ bb, bb < 4 → s2.mem (s0.reg b + 4 * (o + k) + bb) = nums.getD k 0 / 256 ^ bb % 256)
    {g : String} {keys : List Key} (hkeys : ∀ k ∈ keys, k.wf s.nvars s.terms.length) {bytes : Bool}
    {rfs : List RecField} {recVal : Option Val}
    (hheld :
      (rfs = [] ∧ (ctx.contract.preVals ctx.defs s0 → ∃ d, findDef ctx.defs g = some d ∧ d.params.length = keys.length ∧
        Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ s.terms))) d.body
          (if bytes then .list (wordBytes nums) else .list (nums.map Val.word)))) ∨
      (!rfs.isEmpty ∧ ∃ d fvs, recVal = some (.record fvs) ∧ RecFieldsHolds rfs nums fvs ∧
        (ctx.contract.preVals ctx.defs s0 → findDef ctx.defs g = some d ∧ d.params.length = keys.length ∧
          Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ s.terms))) d.body (.record fvs))))
    (hvec : ∀ r ∈ ct.keepsVec, s2.vec r = st.vec r) :
    Holds ctx s0 (afterRhoW ct.regs s.nvars ρ s2 nums recVal) (s.afterCallW ct sp w o m g keys bytes rfs) s2 := by
  let ρ' := afterRhoW ct.regs s.nvars ρ s2 nums recVal
  have hstack := E.stackAt
  have hwm := List.mem_of_getElem? hw
  have hout := E.outAt hwm
  have ag := afterRhoW_agree ct.regs s.nvars ρ s2 nums recVal
  have H' := H.agree wf ag
  obtain ⟨ext, ok, len, lt, dn⟩ := madeW_table wf ct.regs m (inpOf ctx s0) ρ'
  -- the terms of the new words are the words
  have hden : ∀ k, k < m → den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 ((madeW ct.regs s m).1.getD k 0) = nums.getD k 0 := by
    intro k hk
    rw [dn k hk, ev_var]
    dsimp only [ρ']
    rw [afterRhoW_word _ _ _ _ _ _ (by omega)]
    have := hlt (nums.getD k 0) (getD_mem _ _ (by omega))
    unfold W32 at this
    unfold W32i
    omega
  -- the terms there were are as they were
  have hold : ∀ i, i < s.terms.length →
      den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 i = den (inpOf ctx s0) ρ s.terms i :=
    fun i hi => den_mono wf.words.table wf.words.atoms ag ext hi
  refine ⟨H'.entry, ⟨H'.data.1, hdata.trans H.data.2⟩, ?_, hsmall, trivial, trivial, ?_, ?_, ?_, H'.bytes, H'.spec, ?_, ?_,
    ⟨(fun x ids h => by simp [Sym.afterCallW] at h), ?_, ?_, fun _ _ h => nomatch h⟩, ?_, (fun _ h => nomatch h),
    fun r hr => by
      obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
      rw [hvec r (List.contains_iff_mem.mp hr2)]
      exact H'.vecIntact r hr1⟩
  · intro r hr
    show (s2.reg r : Int) = ev _ (if ct.scratch.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    cases hc : ct.scratch.contains r with
    | true => rw [if_pos rfl, ev_var, afterRhoW_reg _ _ _ _ _ _ (hm ▸ hr)]
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
  · intro o i mm
    obtain ⟨m1, m2⟩ := List.mem_filter.mp mm
    have m2' : sp ≤ o := by simpa using m2
    obtain ⟨h1, h2, h3⟩ := H.frameW o i m1
    refine ⟨h1, h2, ?_⟩
    have e : load s2.mem ((s0.reg RSP : Int) + o).toNat 4 = load st.mem ((s0.reg RSP : Int) + o).toNat 4 :=
      load_congr _ _ _ _ (fun a hx1 hx2 => hmem a (Or.inr (by omega)) (by omega))
    rw [e, h3, afterCallW_terms, hold i (wf.frameW o i m1)]
  · intro f mf
    rw [afterCallW_facts] at mf
    rcases List.mem_append.mp mf with mf | mf
    · rcases List.mem_append.mp mf with mf | mf
      · split at mf
        next hne =>
          rcases hheld with ⟨rfl, _⟩ | ⟨_, _, fvs, _, hrf, _⟩
          · simp at hne
          · exact recBoundFacts_holds (s.nvars + ct.regs) ρ' nums 0 rfs fvs (by simpa using hrf)
              (fun k _ hk => afterRhoW_word ct.regs s.nvars ρ s2 nums recVal hk) f mf
        next => cases mf
      · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
        have hk := List.mem_range.mp hk
        have val := afterRhoW_word ct.regs s.nvars ρ s2 nums recVal (k := k) (by omega)
        have vlt := hlt (nums.getD k 0) (getD_mem _ _ (by omega))
        unfold W32 at vlt
        simp only [ranged32, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with rfl | rfl
        · rw [holds_iff, ev_var, val]; omega
        · rw [holds_iff, ev_sub, ev_const, ev_var, val]; unfold W32i; omega
    · rcases List.mem_append.mp mf with mf | mf
      · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        have hr := scratch_lt hr
        have sm := hsmall r
        unfold M64 at sm
        have val := afterRhoW_reg ct.regs s.nvars ρ s2 nums recVal hr
        simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with rfl | rfl
        · rw [holds_iff, ev_var, val]; omega
        · rw [holds_iff, ev_sub, ev_const, ev_var, val]; simp only [top]; omega
      · exact H'.facts f mf
  · intro a ha ho
    have hfr : a + cst < st.reg RSP ∨ st.reg RSP ≤ a := by
      simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at ha
      omega
    have hnot : a < s0.reg b ∨ s0.reg b + n ≤ a := by
      unfold Contract.inOut at ho
      have := List.any_eq_false.mp ho (x, b, n) hwm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      omega
    rw [hmem a hfr (by omega)]
    exact H.mem a ha ho
  · intro w' o x' mw
    obtain ⟨name, r', n', g1, g2, g3, g4⟩ := H'.wrote w' o x' mw
    refine ⟨name, r', n', g1, g2, g3, ?_⟩
    have ne : w' ≠ w := hnow (w', o, x') mw
    have ho' := E.outAt (List.mem_of_getElem? g1)
    have ap := E.outOut g1 hw ne
    rw [hmem _ (by omega) (by omega)]
    exact g4
  · intro w' mw' x' r' n' ho' k hk
    rw [afterCallW_intact] at mw'
    obtain ⟨mi, ne⟩ := List.mem_filter.mp mw'
    have ne' : w' ≠ w := by simpa using ne
    have hor := E.outAt (List.mem_of_getElem? ho')
    have ap := E.outOut ho' hw ne'
    rw [hmem _ (by omega) (by omega)]
    exact H.words.intact w' mi x' r' n' ho' k hk
  · intro w' j i mw' x' r' n' ho'
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
      obtain ⟨h1, h2⟩ := H.words.wrote w' j i mo x' r' n' ho'
      have hor := E.outAt (List.mem_of_getElem? ho')
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
    have e1 : keys.map (Key.val ctx s0 ρ' (madeW ct.regs s m).2) = keys.map (Key.val ctx s0 ρ s.terms) :=
      List.map_congr_left fun k' mk' => Key.val_mono (hkeys k' mk') ag wf.words.table wf.words.atoms ext
    have emap : (madeW ct.regs s m).1.map (fun i => den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 i) = nums := by
      apply List.ext_getElem
      · simp [len, hlen]
      · intro i h1 h2
        have hi : i < m := by simpa [len] using h1
        have := hden i hi
        rw [getD_of_lt _ _ (by omega), getD_of_lt _ _ (by omega)] at this
        simp only [List.getElem_map, this]
    rcases List.mem_append.mp mk with mk | mk
    · split at mk
      next hne =>
        rcases hheld with ⟨rfl, _⟩ | ⟨_, d, fvs, rfl, hrf, hv⟩
        · simp at hne
        · have hdec : Val.decode (ρ' (s.nvars + ct.regs + m)).toNat = .record fvs := by
            dsimp only [ρ']
            rw [← hlen, afterRhoW_rec, Int.toNat_natCast, Val.decode_code]
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at mk
          rcases mk with rfl | rfl
          · intro hpv
            obtain ⟨hd, hlen', hval⟩ := hv hpv
            refine ⟨d, hd, hlen', ?_⟩
            show Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ' (madeW ct.regs s m).2))) d.body (Val.decode (ρ' (s.nvars + ct.regs + m)).toNat)
            rw [e1, hdec]; exact hval
          · intro _
            refine ⟨fvs, hdec, ?_⟩
            show RecFieldsHolds rfs ((madeW ct.regs s m).1.map (fun i => den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 i)) fvs
            rw [emap]; exact hrf
      next hne =>
        have mk := List.mem_singleton.mp mk
        subst mk
        rcases hheld with ⟨rfl, hhv⟩ | ⟨hnon, _⟩
        · cases bytes
          · intro hpv
            obtain ⟨d, hd, hlen', hv⟩ := hhv hpv
            refine ⟨d, hd, hlen', ?_⟩
            show Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ' (madeW ct.regs s m).2))) d.body
              (.list ((madeW ct.regs s m).1.map fun i => Val.word (den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 i)))
            have e2 : (madeW ct.regs s m).1.map (fun i => Val.word (den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 i)) = nums.map Val.word := by
              rw [← emap, List.map_map]; rfl
            rw [e1, e2]; exact hv
          · intro hpv
            obtain ⟨d, hd, hlen', hv⟩ := hhv hpv
            refine ⟨d, hd, hlen', ?_⟩
            show Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ' (madeW ct.regs s m).2))) d.body
              (.list (wordBytes ((madeW ct.regs s m).1.map fun i => den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 i)))
            rw [e1, emap]; exact hv
        · exact absurd hnon hne
    · exact Known.holds_mono (wf.known k mk) ag wf.words.table wf.words.atoms ext (H.known k mk)

/-! ## A call that writes words of the frame

The called function is given a part of this function's frame to write (and to read). After it, each word
of the part is a new unknown, and two words make the number of a cell of the frame. -/

theorem afterCallF_facts (ct : Contract) (s : Sym) (sp c : Int) (m : Nat) (g : String) (keys : List Key) (rfs : List RecField) :
    (s.afterCallF ct sp c m g keys rfs).facts =
      (if !rfs.isEmpty then recBoundFacts (s.nvars + ct.regs) 0 rfs else []) ++
      ((List.range m).map fun k => ranged32 (s.nvars + ct.regs + k)).flatten ++
      ((ct.scratch.map fun r => ranged (s.nvars + r)).flatten ++ s.facts) := rfl
theorem afterCallF_known (ct : Contract) (s : Sym) (sp c : Int) (m : Nat) (g : String) (keys : List Key) (rfs : List RecField) :
    (s.afterCallF ct sp c m g keys rfs).known =
      (if !rfs.isEmpty then [Known.use g keys (s.nvars + ct.regs + m), Known.record (s.nvars + ct.regs + m) rfs (madeW ct.regs s m).1]
       else [Known.held g keys (madeW ct.regs s m).1]) ++ s.known := rfl
theorem afterCallF_terms (ct : Contract) (s : Sym) (sp c : Int) (m : Nat) (g : String) (keys : List Key) (rfs : List RecField) :
    (s.afterCallF ct sp c m g keys rfs).terms = (madeW ct.regs s m).2 := rfl
theorem afterCallF_nvars (ct : Contract) (s : Sym) (sp c : Int) (m : Nat) (g : String) (keys : List Key) (rfs : List RecField) :
    (s.afterCallF ct sp c m g keys rfs).nvars = s.nvars + ct.regs + m + (if !rfs.isEmpty then 1 else 0) := rfl
theorem afterCallF_frame (ct : Contract) (s : Sym) (sp c : Int) (m : Nat) (g : String) (keys : List Key) (rfs : List RecField) :
    (s.afterCallF ct sp c m g keys rfs).frame = ((List.range (m / 2)).map fun (j : Nat) =>
        (c + 8 * (j : Int), Lin.add (Lin.var (s.nvars + ct.regs + 2 * j)) (Lin.scale W32i (Lin.var (s.nvars + ct.regs + 2 * j + 1))))) ++
      s.frame.filter fun cell => decide (sp ≤ cell.1) && (decide (cell.1 + 8 ≤ c) || decide (c + 4 * (m : Int) ≤ cell.1)) := rfl

theorem afterCallF_wf {ctx : Ctx} {s : Sym} (wf : WF ctx s) (ct : Contract) (hm : ct.regs = ctx.nreg) (sp c : Int) (m : Nat) (g : String) {keys : List Key}
    (hkeys : ∀ k ∈ keys, k.wf s.nvars s.terms.length) (rfs : List RecField := [])
    (hsum : !rfs.isEmpty → (rfs.map RecField.nwords).sum ≤ m) : WF ctx (s.afterCallF ct sp c m g keys rfs) := by
  let nv := s.nvars + ct.regs + m + (if !rfs.isEmpty then 1 else 0)
  have le : s.nvars ≤ nv := by omega
  have lem : s.nvars + ct.regs + m ≤ nv := by omega
  obtain ⟨ext, ok, len, lt, _⟩ := madeW_table wf ct.regs m (fun _ _ => 0) (fun _ => 0)
  have ok' := ok.mono lem
  refine ⟨Nat.le_trans wf.base le, ?_, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨ok'.wf, ok'.atoms, (fun x ids h => by simp [Sym.afterCallF] at h), ok'.rotrs, ?_, fun _ _ h => nomatch h⟩, ?_, fun _ h => nomatch h⟩
  · intro r hr
    show bounded nv (if ct.scratch.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    split
    · exact bounded_var (by omega)
    · exact bounded_mono le (wf.reg r hr)
  · intro o v mm
    rw [afterCallF_frame] at mm
    show bounded nv v
    rcases List.mem_append.mp mm with mn | mo
    · obtain ⟨j, hj, e⟩ := List.mem_map.mp mn
      have hj := List.mem_range.mp hj
      injection e with _ e
      rw [← e]
      exact bounded_add (bounded_var (by omega)) (bounded_scale _ (bounded_var (by omega)))
    · exact bounded_mono le (wf.frame o v (List.mem_filter.mp mo).1)
  · intro o i mm
    exact Nat.lt_of_lt_of_le (wf.frameW o i (List.mem_filter.mp mm).1) ext.le
  · intro f mf
    rw [afterCallF_facts] at mf
    show bounded nv f
    rcases List.mem_append.mp mf with mf | mf
    · rcases List.mem_append.mp mf with mf | mf
      · split at mf
        next hne =>
          have hs := hsum hne
          exact recBoundFacts_wf (s.nvars + ct.regs) nv 0 rfs (by omega) f mf
        next => cases mf
      · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
        have hk := List.mem_range.mp hk
        simp only [ranged32, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with rfl | rfl
        · exact bounded_var (by omega)
        · exact bounded_sub (bounded_const _ _) (bounded_var (by omega))
    · rcases List.mem_append.mp mf with mf | mf
      · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        have hr := scratch_lt hr
        simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with rfl | rfl
        · exact bounded_var (by omega)
        · exact bounded_sub (bounded_const _ _) (bounded_var (by omega))
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
    rcases List.mem_append.mp mk with mk | mk
    · split at mk
      next hne =>
        have hnv : s.nvars + ct.regs + m < nv := by simp [nv, hne]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at mk
        rcases mk with rfl | rfl
        · exact ⟨(Known.wf_mono le ext.le (k := .held g keys []) ⟨hkeys, fun _ m => nomatch m⟩).1, hnv⟩
        · exact ⟨hnv, lt⟩
      next =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at mk
        subst mk
        exact ⟨(Known.wf_mono le ext.le (k := .held g keys []) ⟨hkeys, fun _ m => nomatch m⟩).1, lt⟩
    · exact Known.wf_mono le ext.le (wf.known k mk)

/-- After a call of a function that has written words of the frame, what the verifier then holds is so. -/
theorem afterCallF_holds {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st s2 : State}
    {sp : Int} (ct : Contract) (cst : Nat) (hm : ct.regs = ctx.nreg) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (hsp : (st.reg RSP : Int) = s0.reg RSP + sp) (hlow : -(ctx.contract.stackAt s0 : Int) ≤ sp - ct.slot - cst) (hsp0 : sp ≤ 0)
    (hkeep : ∀ r, r < ctx.nreg → ct.scratch.contains r = false → s2.reg r = st.reg r)
    (hsmall : ∀ r, s2.reg r < M64)
    {c : Int} {m : Nat} (hc : sp ≤ c) (hce : c + 4 * (m : Int) ≤ 0)
    (hmem : ∀ a : Nat, a + ct.slot + cst < st.reg RSP ∨ st.reg RSP ≤ a →
      (a : Int) < s0.reg RSP + c ∨ (s0.reg RSP : Int) + c + 4 * (m : Int) ≤ a → s2.mem a = st.mem a)
    (hdata : s2.data = st.data)
    {nums : List Nat} (hlen : nums.length = m) (hlt : ∀ v ∈ nums, v < W32)
    (hrun : ∀ k, k < m → load s2.mem (((s0.reg RSP : Int) + c).toNat + 4 * k) 4 = nums.getD k 0)
    {g : String} {keys : List Key} (hkeys : ∀ k ∈ keys, k.wf s.nvars s.terms.length)
    {rfs : List RecField} {recVal : Option Val}
    (hheld :
      (rfs = [] ∧ (ctx.contract.preVals ctx.defs s0 → ∃ d, findDef ctx.defs g = some d ∧ d.params.length = keys.length ∧
        Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ s.terms))) d.body (.list (nums.map Val.word)))) ∨
      (!rfs.isEmpty ∧ ∃ d fvs, recVal = some (.record fvs) ∧ RecFieldsHolds rfs nums fvs ∧
        (ctx.contract.preVals ctx.defs s0 → findDef ctx.defs g = some d ∧ d.params.length = keys.length ∧
          Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ s.terms))) d.body (.record fvs))))
    (hvec : ∀ r ∈ ct.keepsVec, s2.vec r = st.vec r) :
    Holds ctx s0 (afterRhoW ct.regs s.nvars ρ s2 nums recVal) (s.afterCallF ct sp c m g keys rfs) s2 := by
  let ρ' := afterRhoW ct.regs s.nvars ρ s2 nums recVal
  have hstack := E.stackAt
  have ag := afterRhoW_agree ct.regs s.nvars ρ s2 nums recVal
  have H' := H.agree wf ag
  obtain ⟨ext, ok, len, lt, dn⟩ := madeW_table wf ct.regs m (inpOf ctx s0) ρ'
  have hden : ∀ k, k < m → den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 ((madeW ct.regs s m).1.getD k 0) = nums.getD k 0 := by
    intro k hk
    rw [dn k hk, ev_var]
    dsimp only [ρ']
    rw [afterRhoW_word _ _ _ _ _ _ (by omega)]
    have := hlt (nums.getD k 0) (getD_mem _ _ (by omega))
    unfold W32 at this
    unfold W32i
    omega
  have hold : ∀ i, i < s.terms.length →
      den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 i = den (inpOf ctx s0) ρ s.terms i :=
    fun i hi => den_mono wf.words.table wf.words.atoms ag ext hi
  refine ⟨H'.entry, ⟨H'.data.1, hdata.trans H.data.2⟩, ?_, hsmall, trivial, trivial, ?_, ?_, ?_, H'.bytes, H'.spec, ?_, ?_,
    ⟨(fun x ids h => by simp [Sym.afterCallF] at h), ?_, ?_, fun _ _ h => nomatch h⟩, ?_, (fun _ h => nomatch h),
    fun r hr => by
      obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
      rw [hvec r (List.contains_iff_mem.mp hr2)]
      exact H'.vecIntact r hr1⟩
  · intro r hr
    show (s2.reg r : Int) = ev _ (if ct.scratch.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    cases hcs : ct.scratch.contains r with
    | true => rw [if_pos rfl, ev_var, afterRhoW_reg _ _ _ _ _ _ (hm ▸ hr)]
    | false =>
      rw [if_neg (by decide), hkeep r hr hcs]
      exact H'.reg r hr
  · intro o v mm
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
      have v0 := afterRhoW_word ct.regs s.nvars ρ s2 nums recVal (k := 2 * j) (by omega)
      have v1 := afterRhoW_word ct.regs s.nvars ρ s2 nums recVal (k := 2 * j + 1) (by omega)
      rw [show s.nvars + ct.regs + (2 * j + 1) = s.nvars + ct.regs + 2 * j + 1 by omega] at v1
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
  · intro o i mm
    obtain ⟨m1, m2⟩ := List.mem_filter.mp mm
    have m2' : sp ≤ o ∧ (o + 4 ≤ c ∨ c + 4 * (m : Int) ≤ o) := by simpa using m2
    obtain ⟨h1, h2, h3⟩ := H.frameW o i m1
    refine ⟨h1, h2, ?_⟩
    have e : load s2.mem ((s0.reg RSP : Int) + o).toNat 4 = load st.mem ((s0.reg RSP : Int) + o).toNat 4 :=
      load_congr _ _ _ _ (fun a hx1 hx2 => hmem a (Or.inr (by omega)) (by omega))
    rw [e, h3, afterCallF_terms, hold i (wf.frameW o i m1)]
  · intro f mf
    rw [afterCallF_facts] at mf
    rcases List.mem_append.mp mf with mf | mf
    · rcases List.mem_append.mp mf with mf | mf
      · split at mf
        next hne =>
          rcases hheld with ⟨rfl, _⟩ | ⟨_, _, fvs, _, hrf, _⟩
          · simp at hne
          · exact recBoundFacts_holds (s.nvars + ct.regs) ρ' nums 0 rfs fvs (by simpa using hrf)
              (fun k _ hk => afterRhoW_word ct.regs s.nvars ρ s2 nums recVal hk) f mf
        next => cases mf
      · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
        have hk := List.mem_range.mp hk
        have val := afterRhoW_word ct.regs s.nvars ρ s2 nums recVal (k := k) (by omega)
        have vlt := hlt (nums.getD k 0) (getD_mem _ _ (by omega))
        unfold W32 at vlt
        simp only [ranged32, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with rfl | rfl
        · rw [holds_iff, ev_var, val]; omega
        · rw [holds_iff, ev_sub, ev_const, ev_var, val]; unfold W32i; omega
    · rcases List.mem_append.mp mf with mf | mf
      · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp mf
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        have hr := scratch_lt hr
        have sm := hsmall r
        unfold M64 at sm
        have val := afterRhoW_reg ct.regs s.nvars ρ s2 nums recVal hr
        simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with rfl | rfl
        · rw [holds_iff, ev_var, val]; omega
        · rw [holds_iff, ev_sub, ev_const, ev_var, val]; simp only [top]; omega
      · exact H'.facts f mf
  · intro a ha ho
    have hfr : a + ct.slot + cst < st.reg RSP ∨ st.reg RSP ≤ a := by
      simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at ha
      omega
    have hout : (a : Int) < s0.reg RSP + c ∨ (s0.reg RSP : Int) + c + 4 * (m : Int) ≤ a := by
      simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at ha
      omega
    rw [hmem a hfr hout]
    exact H.mem a ha ho
  · intro w' o x' mw
    obtain ⟨name, r', n', g1, g2, g3, g4⟩ := H'.wrote w' o x' mw
    refine ⟨name, r', n', g1, g2, g3, ?_⟩
    have ho' := E.outAt (List.mem_of_getElem? g1)
    rw [hmem _ (by omega) (by omega)]
    exact g4
  · intro w' mw' x' r' n' ho' k hk
    have hor := E.outAt (List.mem_of_getElem? ho')
    rw [hmem _ (by omega) (by omega)]
    exact H.words.intact w' mw' x' r' n' ho' k hk
  · intro w' j i mw' x' r' n' ho'
    obtain ⟨h1, h2⟩ := H.words.wrote w' j i mw' x' r' n' ho'
    have hor := E.outAt (List.mem_of_getElem? ho')
    refine ⟨h1, fun bb hbb => ?_⟩
    rw [hmem _ (by omega) (by omega), h2 bb hbb, afterCallF_terms, hold i (wf.words.wrote w' j i mw')]
  · intro k mk
    rw [afterCallF_known] at mk
    have e1 : keys.map (Key.val ctx s0 ρ' (madeW ct.regs s m).2) = keys.map (Key.val ctx s0 ρ s.terms) :=
      List.map_congr_left fun k' mk' => Key.val_mono (hkeys k' mk') ag wf.words.table wf.words.atoms ext
    have emap : (madeW ct.regs s m).1.map (fun i => den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 i) = nums := by
      apply List.ext_getElem
      · simp [len, hlen]
      · intro i h1 h2
        have hi : i < m := by simpa [len] using h1
        have := hden i hi
        rw [getD_of_lt _ _ (by omega), getD_of_lt _ _ (by omega)] at this
        simp only [List.getElem_map, this]
    rcases List.mem_append.mp mk with mk | mk
    · split at mk
      next hne =>
        rcases hheld with ⟨rfl, _⟩ | ⟨_, d, fvs, rfl, hrf, hv⟩
        · simp at hne
        · have hdec : Val.decode (ρ' (s.nvars + ct.regs + m)).toNat = .record fvs := by
            dsimp only [ρ']
            rw [← hlen, afterRhoW_rec, Int.toNat_natCast, Val.decode_code]
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at mk
          rcases mk with rfl | rfl
          · intro hpv
            obtain ⟨hd, hlen', hval⟩ := hv hpv
            refine ⟨d, hd, hlen', ?_⟩
            show Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ' (madeW ct.regs s m).2))) d.body (Val.decode (ρ' (s.nvars + ct.regs + m)).toNat)
            rw [e1, hdec]; exact hval
          · intro _
            refine ⟨fvs, hdec, ?_⟩
            show RecFieldsHolds rfs ((madeW ct.regs s m).1.map (fun i => den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 i)) fvs
            rw [emap]; exact hrf
      next hne =>
        have mk := List.mem_singleton.mp mk
        subst mk
        rcases hheld with ⟨rfl, hhv⟩ | ⟨hnon, _⟩
        · intro hpv
          obtain ⟨d, hd, hlen', hv⟩ := hhv hpv
          refine ⟨d, hd, hlen', ?_⟩
          show Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ' (madeW ct.regs s m).2))) d.body
            (.list ((madeW ct.regs s m).1.map fun i => Val.word (den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 i)))
          have e2 : (madeW ct.regs s m).1.map (fun i => Val.word (den (inpOf ctx s0) ρ' (madeW ct.regs s m).2 i)) = nums.map Val.word := by
            rw [← emap, List.map_map]; rfl
          rw [e1, e2]; exact hv
        · exact absurd hnon hne
    · exact Known.holds_mono (wf.known k mk) ag wf.words.table wf.words.atoms ext (H.known k mk)

/-! ## Serialized record lemmas -/

theorem evalSpec_none_fail (defs : List Def) (fuel : Nat) (env : List (String × Val)) :
    evalSpec defs fuel env (.index (.list (.cons (.num 0) .nil)) (.num 1)) = none := by
  cases fuel with
  | zero => rfl
  | succ f1 =>
    cases f1 with
    | zero => rfl
    | succ f2 =>
      cases f2 with
      | zero => rfl
      | succ f3 => simp [evalSpec, evalList]

theorem toWords_eq_some_inv : ∀ {vs : List Val} {ws : List Nat},
    toWords vs = some (ws.map Val.word) → (∀ w ∈ ws, w < W32) → vs = wordBytes ws
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [toWords] at h
  | [_], _, h, _ => by simp [toWords] at h
  | [_, _], _, h, _ => by simp [toWords] at h
  | [_, _, _], _, h, _ => by simp [toWords] at h
  | a :: b :: c :: d :: rest, ws, h, hlt => by
    cases a <;> cases b <;> cases c <;> cases d <;> simp only [toWords] at h <;> try cases h
    rename_i i0 i1 i2 i3
    split at h
    next hb =>
      cases hr : toWords rest with
      | none => simp [hr] at h
      | some wrest =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        cases ws with
        | nil => simp at h
        | cons w wtail =>
          simp only [List.map_cons, List.cons.injEq, Val.word.injEq] at h
          obtain ⟨hw, htail⟩ := h
          have hrest := toWords_eq_some_inv (by rw [hr, htail]) (fun x m => hlt x (List.mem_cons_of_mem _ m))
          have hw0 : w < W32 := hlt w (List.mem_cons_self ..)
          unfold W32 at hw0
          obtain ⟨h0a, h0b, h1a, h1b, h2a, h2b, h3a, h3b⟩ := hb
          rw [hrest, wordBytes, ← hw]
          simp only [List.cons.injEq, Val.int.injEq, and_true]
          have e0 : (i0.toNat : Int) = i0 := Int.toNat_of_nonneg h0a
          have e1 : (i1.toNat : Int) = i1 := Int.toNat_of_nonneg h1a
          have e2 : (i2.toNat : Int) = i2 := Int.toNat_of_nonneg h2a
          have e3 : (i3.toNat : Int) = i3 := Int.toNat_of_nonneg h3a
          refine ⟨by omega, by omega, by omega, by omega⟩
    next => cases h

theorem returnsRecord_sound (defs : List Def) (fnames : List String) :
    ∀ (fuel : Nat) (env : List (String × Val)) (e : SExpr) (rv : Val),
      returnsRecord fnames e = true → evalSpec defs fuel env e = some rv →
      ∃ vs, rv = .record (fnames.zip vs) ∧ vs.length = fnames.length
  | 0, _, _, _, _, hev => by simp [evalSpec] at hev
  | fuel + 1, env, e, rv, hrr, hev => by
    cases e with
    | letx x a body =>
      simp only [returnsRecord] at hrr
      simp only [evalSpec] at hev
      cases ha : evalSpec defs fuel env a with
      | none => simp [ha] at hev
      | some v =>
        simp only [ha] at hev
        exact returnsRecord_sound defs fnames fuel ((x, v) :: env) body rv hrr hev
    | ifx c a b =>
      simp only [returnsRecord, Bool.and_eq_true] at hrr
      simp only [evalSpec] at hev
      cases hc : evalSpec defs fuel env c with
      | none => simp [hc] at hev
      | some vc =>
        cases vc with
        | bool t =>
          cases t
          · simp only [hc] at hev; exact returnsRecord_sound defs fnames fuel env b rv hrr.2 hev
          · simp only [hc] at hev; exact returnsRecord_sound defs fnames fuel env a rv hrr.1 hev
        | _ => simp [hc] at hev
    | record ns items =>
      simp only [returnsRecord, beq_iff_eq] at hrr
      subst hrr
      simp only [evalSpec] at hev
      cases hl : evalList (evalSpec defs fuel env) items with
      | none => simp [hl] at hev
      | some vs =>
        simp only [hl] at hev
        split at hev
        next hlen =>
          injection hev with hev; subst hev
          have hlen' : ns.length = vs.length := by simpa using hlen
          exact ⟨vs, rfl, hlen'.symm⟩
        next => cases hev
    | _ => simp [returnsRecord] at hrr

theorem parseRecPart_sound {defs : List Def} {x : String} {fvs : List (String × Val)} {env : List (String × Val)}
    {fuel : Nat} {a : SExpr} {rf : RecField} {ws : List Nat}
    (hp : parseRecPart x a = some rf)
    (hev : evalSpec defs fuel ((x, .record fvs) :: env) a = some (.list (ws.map Val.word)))
    (hlt : ∀ w ∈ ws, w < W32) :
    ws.length = rf.nwords ∧
    match rf with
    | .words fn _ => fvs.lookup fn = some (.list (ws.map Val.word))
    | .bytes fn k => k % 4 = 0 ∧ fvs.lookup fn = some (.list (wordBytes ws))
    | .u64 fn bd => ∃ v lo hi, fvs.lookup fn = some (.int v) ∧ 0 ≤ v ∧ v < (bd : Int) ∧ bd ≤ M64 ∧
        ws = [lo, hi] ∧ v = (lo : Int) + W32i * (hi : Int) ∧ lo < W32 ∧ hi < W32 := by
  cases fuel with
  | zero => simp [evalSpec] at hev
  | succ f1 =>
    unfold parseRecPart at hp
    split at hp
    · -- words field
      rename_i x1 fn1 k x2 fn2
      split at hp
      next hc =>
        injection hp with hp; subst hp
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨hx1, hx2⟩, hfn⟩, hk0⟩ := hc
        subst x1; subst x2; subst fn2
        simp only [evalSpec] at hev
        cases hcond : evalSpec defs f1 ((x, .record fvs) :: env) (.bin "==" (.call "len" (.cons (.field (.name x) fn1) .nil)) (.num k)) with
        | none => simp [hcond] at hev
        | some vc =>
          cases vc with
          | bool t =>
            cases t
            · simp only [hcond, evalSpec_none_fail] at hev; cases hev
            · simp only [hcond] at hev
              cases f1 with
              | zero => simp [evalSpec] at hev
              | succ f2 =>
                cases f2 with
                | zero => simp [evalSpec] at hev
                | succ f3 =>
                  simp only [evalSpec, List.lookup, beq_self_eq_true, ↓reduceIte] at hev hcond
                  cases f3 with
                  | zero => simp [evalSpec, evalList] at hcond
                  | succ f4 =>
                    cases f4 with
                    | zero => simp [evalSpec, evalList] at hcond
                    | succ f5 =>
                      simp only [evalSpec, evalList, List.lookup, beq_self_eq_true, ↓reduceIte] at hcond
                      cases hl : fvs.lookup fn1 with
                      | none => simp [hl] at hev
                      | some v =>
                        simp only [hl, Option.some.injEq] at hev
                        subst hev
                        simp only [hl, beq_self_eq_true, ↓reduceIte] at hcond
                        rw [if_pos hk0] at hcond
                        simp [binop] at hcond
                        exact ⟨by simp only [RecField.nwords]; omega, hl⟩
          | _ => simp [hcond] at hev
      next => cases hp
    · -- bytes field
      rename_i x1 fn1 k x2 fn2
      split at hp
      next hc =>
        injection hp with hp; subst hp
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨hx1, hx2⟩, hfn⟩, hk0⟩, hkm4⟩ := hc
        subst x1; subst x2; subst fn2
        simp only [evalSpec] at hev
        cases hcond : evalSpec defs f1 ((x, .record fvs) :: env) (.bin "==" (.call "len" (.cons (.field (.name x) fn1) .nil)) (.num k)) with
        | none => simp [hcond] at hev
        | some vc =>
          cases vc with
          | bool t =>
            cases t
            · simp only [hcond, evalSpec_none_fail] at hev; cases hev
            · simp only [hcond] at hev
              cases f1 with
              | zero => simp [evalSpec] at hev
              | succ f2 =>
                cases f2 with
                | zero => simp [evalSpec, evalList] at hev
                | succ f3 =>
                  cases f3 with
                  | zero => simp [evalSpec, evalList] at hev
                  | succ f4 =>
                    simp only [evalSpec, evalList, List.lookup, beq_self_eq_true, ↓reduceIte] at hev hcond
                    cases hl : fvs.lookup fn1 with
                    | none => simp [hl] at hev
                    | some v =>
                      cases v with
                      | list bs =>
                        have hownw : own.contains "words" = true := by decide
                        have hlenw : ("words" == "len") = false := by decide
                        simp only [hl, hownw, hlenw, Bool.false_eq_true, ↓reduceIte] at hev
                        have htw : toWords bs = some (ws.map Val.word) := by
                          cases htw0 : toWords bs with
                          | none => simp [builtin, htw0] at hev
                          | some res => simp [builtin, htw0] at hev; rw [hev]
                        have hbs : bs = wordBytes ws := toWords_eq_some_inv htw hlt
                        cases f4 with
                        | zero => simp [evalSpec, evalList] at hcond
                        | succ f5 =>
                          simp only [evalSpec, evalList, List.lookup, beq_self_eq_true, ↓reduceIte, hl] at hcond
                          rw [if_pos hk0] at hcond
                          simp [binop] at hcond
                          rw [hbs, wordBytes_length] at hcond
                          exact ⟨by simp only [RecField.nwords]; omega, by omega, by rw [hl, hbs]⟩
                      | _ =>
                        have hownw : own.contains "words" = true := by decide
                        have hlenw : ("words" == "len") = false := by decide
                        simp only [hl, hownw, hlenw, Bool.false_eq_true, ↓reduceIte] at hev
                        simp [builtin] at hev
          | _ => simp [hcond] at hev
      next => cases hp
    · -- u64 field
      rename_i x1 fn1 bd x2 fn2 x3 fn3
      split at hp
      next hc =>
        injection hp with hp; subst hp
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨⟨⟨hx1, hx2⟩, hx3⟩, hfn2⟩, hfn3⟩, hbd0⟩, hbdM⟩ := hc
        subst x1; subst x2; subst x3; subst fn2; subst fn3
        simp only [evalSpec] at hev
        cases hcond : evalSpec defs f1 ((x, .record fvs) :: env) (.bin "<" (.field (.name x) fn1) (.num bd)) with
        | none => simp [hcond] at hev
        | some vc =>
          cases vc with
          | bool t =>
            cases t
            · simp only [hcond, evalSpec_none_fail] at hev; cases hev
            · simp only [hcond] at hev
              cases f1 with
              | zero => simp [evalSpec] at hev
              | succ f2 =>
                cases f2 with
                | zero => simp [evalSpec, evalList] at hev
                | succ f3 =>
                  cases f3 with
                  | zero => simp [evalSpec, evalList] at hev
                  | succ f4 =>
                    cases f4 with
                    | zero => simp [evalSpec, evalList] at hev
                    | succ f5 =>
                      cases f5 with
                      | zero => simp [evalSpec, evalList] at hev
                      | succ f6 =>
                        have hownc : own.contains "counter" = true := by decide
                        have hownl : own.contains "lo" = true := by decide
                        have hownh : own.contains "hi" = true := by decide
                        have hlenc : ("counter" == "len") = false := by decide
                        have hlenl : ("lo" == "len") = false := by decide
                        have hlenh : ("hi" == "len") = false := by decide
                        simp only [evalSpec, evalList, List.lookup, beq_self_eq_true, ↓reduceIte,
                          hownc, hownl, hownh, hlenc, hlenl, hlenh, Bool.false_eq_true] at hev hcond
                        cases hl : fvs.lookup fn1 with
                        | none => simp [hl] at hev
                        | some v =>
                          cases v with
                          | int iv =>
                            simp only [hl] at hcond hev
                            rw [if_pos (by omega : (0 : Int) ≤ bd)] at hcond
                            simp [binop] at hcond
                            have hbc : builtin "counter" [Val.int iv] = if 0 ≤ iv then some (Val.counter (iv.toNat % 2 ^ 64)) else none := by
                              simp [builtin]
                            rw [hbc] at hev
                            by_cases hiv0 : (0 : Int) ≤ iv
                            · rw [if_pos hiv0] at hev
                              dsimp only at hev
                              have hbl : builtin "lo" [Val.counter (iv.toNat % 2 ^ 64)] = some (Val.word (iv.toNat % 2 ^ 64 % W32)) := by
                                simp [builtin]
                              have hbh : builtin "hi" [Val.counter (iv.toNat % 2 ^ 64)] = some (Val.word (iv.toNat % 2 ^ 64 / W32)) := by
                                simp [builtin]
                              simp [hbl, hbh] at hev
                              cases ws with
                              | nil => simp at hev
                              | cons lo ws1 =>
                                cases ws1 with
                                | nil => simp at hev
                                | cons hi ws2 =>
                                  cases ws2 with
                                  | cons _ _ => simp at hev
                                  | nil =>
                                    simp only [List.map_cons, List.map_nil, List.cons.injEq, Val.word.injEq, and_true] at hev
                                    obtain ⟨hlo, hhi⟩ := hev
                                    have hmod : iv.toNat % 2 ^ 64 = iv.toNat := Nat.mod_eq_of_lt (by unfold M64 at hbdM; omega)
                                    rw [hmod] at hlo hhi
                                    refine ⟨rfl, iv, lo, hi, hl, hiv0, by omega, by omega, rfl, ?_, hlt lo (by simp), hlt hi (by simp)⟩
                                    rw [← hlo, ← hhi]
                                    unfold W32 W32i; omega
                            · rw [if_neg hiv0] at hev; cases hev
                          | _ =>
                            simp only [hl] at hcond
                            rw [if_pos (by omega : (0 : Int) ≤ bd)] at hcond
                            simp [binop, wordop] at hcond
          | _ => simp [hcond] at hev
      next => cases hp
    · cases hp

theorem map_word_append {ws : List Nat} {l1 l2 : List Val} (h : l1 ++ l2 = ws.map Val.word) :
    ∃ w1 w2, ws = w1 ++ w2 ∧ l1 = w1.map Val.word ∧ l2 = w2.map Val.word := by
  refine ⟨ws.take l1.length, ws.drop l1.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · have h1 := congrArg (List.take l1.length) h
    rw [List.take_left' rfl, ← List.map_take] at h1
    exact h1
  · have h2 := congrArg (List.drop l1.length) h
    rw [List.drop_left' rfl, ← List.map_drop] at h2
    exact h2

theorem lookup_of_map_fst_head {fn : String} {v : Val} {frest : List (String × Val)} :
    ((fn, v) :: frest).lookup fn = some v := by simp [List.lookup]

theorem lookup_of_not_mem_fst {x y : String} {v : Val} {frest : List (String × Val)} (hne : x ≠ y) :
    ((x, v) :: frest).lookup y = frest.lookup y := by
  simp [List.lookup, show (y == x) = false from beq_false_of_ne hne.symm]

theorem parseRecBody_lookup {defs : List Def} {x : String} {fvs : List (String × Val)} {env : List (String × Val)} :
    ∀ {fuel : Nat} {body : SExpr} {rfs : List RecField} {ws : List Nat} {sub : List (String × Val)},
      parseRecBody x body = some rfs →
      evalSpec defs fuel ((x, .record fvs) :: env) body = some (.list (ws.map Val.word)) →
      (∀ w ∈ ws, w < W32) →
      sub.map Prod.fst = rfs.map RecField.name →
      allDistinct (rfs.map RecField.name) = true →
      (∀ p ∈ sub, fvs.lookup p.1 = some p.2) →
      RecFieldsHolds rfs ws sub
  | 0, _, _, _, _, _, hev, _, _, _, _ => by simp [evalSpec] at hev
  | fuel + 1, body, rfs, ws, sub, hp, hev, hlt, hnames, hdist, hsub => by
    unfold parseRecBody at hp
    split at hp
    · rename_i a' b'
      cases ha : parseRecPart x a' with
      | none => simp [ha] at hp
      | some rf =>
        cases hb : parseRecBody x b' with
        | none => simp [ha, hb] at hp
        | some rest =>
          simp only [ha, hb, Option.some.injEq] at hp; subst hp
          simp only [evalSpec] at hev
          cases hea : evalSpec defs fuel ((x, .record fvs) :: env) a' with
          | none => simp [hea] at hev
          | some va =>
            cases heb : evalSpec defs fuel ((x, .record fvs) :: env) b' with
            | none => simp [hea, heb] at hev
            | some vb =>
              simp only [hea, heb] at hev
              cases va with
              | list l1 =>
                cases vb with
                | list l2 =>
                  simp only [binop, beq_self_eq_true, ↓reduceIte, Option.some.injEq, Val.list.injEq] at hev
                  obtain ⟨w1, w2, rfl, rfl, rfl⟩ := map_word_append hev
                  have hlt1 : ∀ w ∈ w1, w < W32 := fun w m => hlt w (List.mem_append_left _ m)
                  have hlt2 : ∀ w ∈ w2, w < W32 := fun w m => hlt w (List.mem_append_right _ m)
                  obtain ⟨hw1, hrf⟩ := parseRecPart_sound ha hea hlt1
                  cases sub with
                  | nil => simp at hnames
                  | cons p0 srest =>
                    simp only [List.map_cons, List.cons.injEq] at hnames
                    obtain ⟨hfn, hnames'⟩ := hnames
                    simp only [allDistinct, List.map_cons, Bool.and_eq_true] at hdist
                    have hl0 := hsub p0 (List.mem_cons_self ..)
                    have hrest := parseRecBody_lookup hb heb hlt2 hnames' hdist.2 (fun p mp => hsub p (List.mem_cons_of_mem _ mp))
                    cases rf with
                    | words fn n =>
                      simp only [RecField.name, RecField.nwords] at hfn hw1 hrf
                      rw [← hfn] at hrf
                      rw [hl0] at hrf; injection hrf with hp2
                      cases p0 with
                      | mk px pv =>
                        simp only at hfn hp2; subst hfn; subst hp2
                        refine ⟨rfl, by simp [hw1], ?_, ?_⟩
                        · rw [← hw1, List.take_left]
                        · rwa [← hw1, List.drop_left]
                    | bytes fn n =>
                      simp only [RecField.name, RecField.nwords] at hfn hw1 hrf
                      rw [← hfn] at hrf
                      rw [hl0] at hrf; injection hrf.2 with hp2
                      cases p0 with
                      | mk px pv =>
                        simp only at hfn hp2; subst hfn; subst hp2
                        refine ⟨rfl, hrf.1, by simp [hw1], ?_, ?_⟩
                        · rw [← hw1, List.take_left, wordBytes_eq_flatMap]
                        · rwa [← hw1, List.drop_left]
                    | u64 fn bd =>
                      simp only [RecField.name, RecField.nwords] at hfn hw1 hrf
                      rw [← hfn] at hrf
                      obtain ⟨v0, lo, hi, hlk, hv0, hvbd, hbdM, hw1e, hveq, hlo, hhi⟩ := hrf
                      rw [hl0] at hlk; injection hlk with hp2
                      cases p0 with
                      | mk px pv =>
                        simp only at hfn hp2; subst hfn; subst hp2; subst hw1e
                        exact ⟨rfl, hv0, hvbd, hbdM, hveq, hlo, hhi, hrest⟩
                | _ => simp [binop] at hev
              | _ => cases vb <;> simp [binop, wordop] at hev
    · cases ha : parseRecPart x body with
      | none => simp [ha] at hp
      | some rf =>
        simp only [ha, Option.map_some, Option.some.injEq] at hp; subst hp
        obtain ⟨hw, hrf⟩ := parseRecPart_sound ha hev hlt
        cases sub with
        | nil => simp at hnames
        | cons p0 srest =>
          cases srest with
          | cons _ _ => simp at hnames
          | nil =>
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hnames
            have hl0 := hsub p0 (List.mem_cons_self ..)
            cases rf with
            | words fn n =>
              simp only [RecField.name, RecField.nwords] at hnames hw hrf
              rw [← hnames] at hrf; rw [hl0] at hrf; injection hrf with hp2
              cases p0 with
              | mk px pv =>
                simp only at hnames hp2; subst hnames; subst hp2
                refine ⟨rfl, by omega, by rw [← hw, List.take_length], by rw [← hw, List.drop_length]; trivial⟩
            | bytes fn n =>
              simp only [RecField.name, RecField.nwords] at hnames hw hrf
              rw [← hnames] at hrf; rw [hl0] at hrf; injection hrf.2 with hp2
              cases p0 with
              | mk px pv =>
                simp only at hnames hp2; subst hnames; subst hp2
                refine ⟨rfl, hrf.1, by omega, by rw [← hw, List.take_length, wordBytes_eq_flatMap], by rw [← hw, List.drop_length]; trivial⟩
            | u64 fn bd =>
              simp only [RecField.name, RecField.nwords] at hnames hw hrf
              rw [← hnames] at hrf
              obtain ⟨v0, lo, hi, hlk, hv0, hvbd, hbdM, hwe, hveq, hlo, hhi⟩ := hrf
              rw [hl0] at hlk; injection hlk with hp2
              cases p0 with
              | mk px pv =>
                simp only at hnames hp2; subst hnames; subst hp2; subst hwe
                exact ⟨rfl, hv0, hvbd, hbdM, hveq, hlo, hhi, trivial⟩

theorem lookup_of_allDistinct : ∀ (fvs : List (String × Val)),
    allDistinct (fvs.map Prod.fst) = true → ∀ p ∈ fvs, fvs.lookup p.1 = some p.2
  | [], _, _, m => nomatch m
  | (k, v) :: rest, hd, p, m => by
    simp only [List.map_cons, allDistinct, Bool.and_eq_true, Bool.not_eq_true'] at hd
    rcases List.mem_cons.mp m with rfl | m
    · simp [List.lookup]
    · have hne : p.1 ≠ k := by
        intro heq
        have hmem : k ∈ rest.map Prod.fst := heq ▸ List.mem_map.mpr ⟨p, m, rfl⟩
        have hc : (rest.map Prod.fst).contains k = true := List.contains_iff_mem.mpr hmem
        rw [hd.1] at hc; cases hc
      rw [lookup_of_not_mem_fst hne.symm]
      exact lookup_of_allDistinct rest hd.2 p m

theorem bytes_of_let_call {defs : List Def} {env : List (String × Val)} {x g : String} {args body : SExpr} {l : List Nat}
    (hown : own.contains g = false) (hlen : g ≠ "len")
    (hv : Value defs env (.call "bytes_of" (.cons (.letx x (.call g args) body) .nil)) (.bytes l)) :
    ∃ (fuel : Nat) (as : List Val) (d : Def) (rv : Val) (nums : List Nat),
      evalList (evalSpec defs fuel env) args = some as ∧
      findDef defs g = some d ∧ d.params.length = as.length ∧
      evalSpec defs fuel (d.params.zip as) d.body = some rv ∧
      evalSpec defs fuel ((x, rv) :: env) body = some (.list (nums.map Val.word)) ∧
      (∀ v ∈ nums, v < W32) ∧ l.map (fun (b : Nat) => Val.int b) = wordBytes nums := by
  obtain ⟨fuel, hf⟩ := hv
  cases fuel with
  | zero => simp [evalSpec] at hf
  | succ f1 =>
    simp only [evalSpec, evalList] at hf
    cases h1 : evalSpec defs f1 env (.letx x (.call g args) body) with
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
            cases hg : evalSpec defs f2 env (.call g args) with
            | none => simp [hg] at h1
            | some rv =>
              simp only [hg] at h1
              cases f2 with
              | zero => simp [evalSpec] at hg
              | succ f3 =>
                simp only [evalSpec] at hg
                cases ha : evalList (evalSpec defs f3 env) args with
                | none => simp [ha] at hg
                | some as =>
                  have hl : (g == "len") = false := by simpa using hlen
                  simp only [ha, hl, hown, Bool.false_eq_true, ↓reduceIte] at hg
                  cases hd : findDef defs g with
                  | none => simp [hd] at hg
                  | some d =>
                    simp only [hd] at hg
                    split at hg
                    next hp =>
                      refine ⟨f3 + 1, as, d, rv, nums,
                        evalList_mono (fun _ _ h => evalSpec_mono defs f3 h (f3 + 1) (Nat.le_succ _)) args ha,
                        rfl, by simpa using hp,
                        evalSpec_mono defs f3 hg (f3 + 1) (Nat.le_succ _),
                        h1, e2, by rw [← hf, e3]⟩
                    next => simp at hg
      | _ => simp [builtin] at hf

/-! ## The call -/

/-- What `callW` has looked up, where it says how the call is taken (either a direct `bytes_of(g(args))`
or a serialized record `bytes_of(let x = g(args) in body)`). -/
theorem callWby_spec {find : Nat → Nat → Option (Nat × Nat × List Nat)} {ctx : Ctx} {s : Sym} {c : Contract} {plan : CallW}
    (h : callWby find ctx s c = .ok plan) :
    ∃ (run : String) (r n : Nat) (e : EnsureW) (ids : List Nat) (env : List (String × WVal)) (args : SExpr) (vs : List WVal) (d : Def),
      c.outs = [(run, r, n)] ∧ c.inouts = [(run, r, n)] ∧ c.ensuresW = [e] ∧ e.run = run ∧ e.part = none ∧
      find r n = some (plan.w, plan.first, ids) ∧ calleeW ctx c s ids c.args c.argRegs = some env ∧
      plan.env = env ∧
      own.contains plan.g = false ∧ plan.g ≠ "len" ∧
      plan.tab = (termsOf intern (partNodes ctx s c.args c.argRegs) s.tab).2 ∧
      wevalList (weval ctx plan.tab.find { s with tab := plan.tab } WFUEL env) args = some vs ∧
      findDef ctx.defs plan.g = some d ∧ flatKeys plan.tab.find vs = some plan.keys ∧
      (∀ k ∈ plan.keys, k.wf s.nvars plan.terms.length) ∧ d.params.length = plan.keys.length ∧ plan.words = n / 4 ∧
      ((plan.recFields = [] ∧ e.value = .call "bytes_of" (.cons (.call plan.g args) .nil)) ∨
       (∃ x body, !plan.recFields.isEmpty ∧ c.valArrays = [] ∧ e.value = .call "bytes_of" (.cons (.letx x (.call plan.g args) body) .nil) ∧
         parseRecBody x body = some plan.recFields ∧
         (plan.recFields.map RecField.nwords).sum = n / 4 ∧
         allDistinct (plan.recFields.map RecField.name) = true ∧
         returnsRecord (plan.recFields.map RecField.name) d.body = true)) := by
  unfold callWby at h
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
            cases hce : calleeW ctx c s ids c.args c.argRegs with
            | none => simp only [hce] at h; cases h
            | some env =>
              simp only [hce] at h
              cases hv : e.value with
              | call f a =>
                cases a with
                | cons a1 a2 =>
                  cases a2 with
                  | nil =>
                    cases a1 with
                    | call g args =>
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
                                injection h with h; subst h
                                have hok' : (keys.all (Key.ok s.nvars (termsOf intern (partNodes ctx s c.args c.argRegs) s.tab).2.list.length)) = true := by
                                  rw [← Tab.size_eq_length]; simpa using hok
                                exact ⟨run, r, n, e, ids, env, args, vs, d, rfl, rfl, rfl, erun, epart, hcr, hce, rfl, hown, hlen, rfl, hwl, hfd, hfk,
                                  (fun k mk => Key.ok_wf (List.all_eq_true.mp hok' k mk)), by simpa using hdl, rfl, Or.inl ⟨rfl, hv⟩⟩
                              next => cases h
                          next => cases h
                        next => cases h
                      next => cases h
                    | letx x a1' body =>
                      cases a1' with
                      | call g args =>
                        simp only [hv] at h
                        split at h
                        next hfg =>
                          have hfg' : ((f = "bytes_of" ∧ own.contains g = false) ∧ g ≠ "len") ∧ c.valArrays = [] := by simpa using hfg
                          obtain ⟨⟨⟨rfl, hown⟩, hlen⟩, hcva⟩ := hfg'
                          split at h
                          next fields vs d hpb hwl hfd =>
                            split at h
                            next hrec =>
                              simp only [Bool.and_eq_true, beq_iff_eq] at hrec
                              obtain ⟨⟨⟨hsum, hdist⟩, hrr⟩, hne⟩ := hrec
                              split at h
                              next keys hfk =>
                                split at h
                                next => cases h
                                next hok =>
                                  split at h
                                  next hdl =>
                                    injection h with h; subst h
                                    have hok' : (keys.all (Key.ok s.nvars (termsOf intern (partNodes ctx s c.args c.argRegs) s.tab).2.list.length)) = true := by
                                      rw [← Tab.size_eq_length]; simpa using hok
                                    exact ⟨run, r, n, e, ids, env, args, vs, d, rfl, rfl, rfl, erun, epart, hcr, hce, rfl, hown, hlen, rfl, hwl, hfd, hfk,
                                      (fun k mk => Key.ok_wf (List.all_eq_true.mp hok' k mk)), by simpa using hdl, rfl,
                                      Or.inr ⟨x, body, hne, hcva, hv, hpb, hsum, hdist, hrr⟩⟩
                                  next => cases h
                              next => cases h
                            next => cases h
                          next => cases h
                        next => cases h
                      | _ => simp only [hv] at h; cases h
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

private abbrev WVal.calleeBd (nv : Nat) : WVal → Prop
  | .num r => bounded nv r
  | .span _ off len => bounded nv off ∧ bounded nv len
  | .part _ _ _ | .wbytes _ => True
  | _ => False

private theorem den_agree_same {inp : Nat → Nat → Nat} {ρ1 ρ2 : Nat → Int} {T : List Node} {nv : Nat}
    (hw : WFT T) (ha : ∀ (j : Nat) (r : Row), T[j]? = some (Node.atom r) → bounded nv r) (ag : Agree nv ρ1 ρ2) (i : Nat) :
    den inp ρ2 T i = den inp ρ1 T i := by
  by_cases hi : i < T.length
  · exact den_mono hw ha ag (Ext.refl T) hi
  · cases hlen : T.length with
    | zero => simp [den, denF, hlen]
    | succ n => simp [den, denF, hlen, List.getElem?_eq_none (Nat.not_lt.mp hi)]

private theorem WDen_agree_callee {ctx : Ctx} {s0 : State} {ρ1 ρ2 : Nat → Int} {T : List Node} {nv : Nat}
    (hw : WFT T) (ha : ∀ (j : Nat) (r : Row), T[j]? = some (Node.atom r) → bounded nv r) (ag : Agree nv ρ1 ρ2)
    {v : WVal} {a : Val} (hd : WDen ctx s0 ρ1 T v a) (hb : v.calleeBd nv) : WDen ctx s0 ρ2 T v a := by
  cases hd with
  | num r =>
    have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ2) (T := T) r
    rwa [← ev_agree hb ag] at this
  | part r off n h => exact WDen.part r off n h
  | span r off len ho hn =>
    have eo := ev_agree hb.1 ag
    have en := ev_agree hb.2 ag
    have := WDen.span (ctx := ctx) (s0 := s0) (ρ := ρ2) (T := T) r off len (by omega) (by omega)
    rwa [← eo, ← en] at this
  | wbytes ids =>
    have em : ids.map (den (inpOf ctx s0) ρ2 T) = ids.map (den (inpOf ctx s0) ρ1 T) :=
      List.map_congr_left fun i _ => den_agree_same hw ha ag i
    have := WDen.wbytes (ctx := ctx) (s0 := s0) (ρ := ρ2) (T := T) ids
    rwa [em] at this
  | _ => simp [WVal.calleeBd] at hb

private theorem calleeW_bounded {ctx : Ctx} {c : Contract} {s : Sym} {ids : List Nat} (wf : WF ctx s) (hm : c.regs = ctx.nreg) :
    ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × WVal)},
      (∀ r ∈ regs, r ∈ c.argRegs) → calleeW ctx c s ids args regs = some env →
      ∀ p ∈ env, p.2.calleeBd s.nvars
  | [], _, env, _, h => by simp only [calleeW, Option.some.injEq] at h; subst h; intro _ m; cases m
  | _ :: _, [], env, _, h => by simp only [calleeW, Option.some.injEq] at h; subst h; intro _ m; cases m
  | (_, .number) :: args, r :: regs, env, hr, h => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx c s ids args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
      intro p mp
      rcases List.mem_cons.mp mp with rfl | mp
      · exact wf.reg r (hm ▸ argRegs_lt (hr r (List.mem_cons_self ..)))
      · exact calleeW_bounded wf hm args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec p mp
  | (_, .fixed n) :: args, r :: regs, env, hr, h => by
    simp only [calleeW] at h
    cases hf : fixedPart ctx s r n with
    | none =>
      cases hrec : calleeW ctx c s ids args regs with
      | none => simp [hf, hrec] at h
      | some env' =>
        cases hfr : frameRun s r n with
        | none => simp [hf, hrec, hfr] at h
        | some pr =>
          simp only [hf, hrec, hfr, Option.map_some, Option.some.injEq] at h; subst h
          intro p mp
          rcases List.mem_cons.mp mp with rfl | mp
          · trivial
          · exact calleeW_bounded wf hm args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec p mp
    | some pp =>
      cases hrec : calleeW ctx c s ids args regs with
      | none => simp [hf, hrec] at h
      | some env' =>
        simp only [hf, hrec, Option.some.injEq] at h; subst h
        intro p mp
        rcases List.mem_cons.mp mp with rfl | mp
        · trivial
        · exact calleeW_bounded wf hm args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec p mp
  | (_, .inout _) :: args, _ :: regs, env, hr, h => by
    simp only [calleeW] at h
    cases hrec : calleeW ctx c s ids args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map_some, Option.some.injEq] at h; subst h
      intro p mp
      rcases List.mem_cons.mp mp with rfl | mp
      · trivial
      · exact calleeW_bounded wf hm args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec p mp
  | (_, .bytes len) :: args, r :: regs, env, hr, h => by
    simp only [calleeW] at h
    cases hl : c.regOf len with
    | none => simp [hl] at h
    | some l =>
      simp only [hl] at h
      cases hp : regionPart ctx s r l with
      | none => simp [hp] at h
      | some pp =>
        obtain ⟨b, off, n⟩ := pp
        cases hrec : calleeW ctx c s ids args regs with
        | none => simp [hp, hrec] at h
        | some env' =>
          simp only [hp, hrec, Option.some.injEq] at h; subst h
          intro p mp
          rcases List.mem_cons.mp mp with rfl | mp
          · unfold regionPart at hp
            cases hfr : findRegion (s.reg r) ctx.contract.regions 0 with
            | none => simp [hfr] at hp
            | some wh =>
              obtain ⟨k, o, base, len0, rfl, _, hk, ho⟩ := findRegion_spec hfr
              simp only [Nat.sub_zero] at hk
              simp only [hfr, hk] at hp
              split at hp
              · injection hp with hp; injection hp with e1 e2; injection e2 with e2 e3; subst e1 e2 e3
                have hm0 := List.mem_of_getElem? hk
                have b16 : base < ctx.nreg := (regions_lt hm0).1
                have hr_lt : r < ctx.nreg := hm ▸ argRegs_lt (hr r (List.mem_cons_self ..))
                have hl_lt : l < ctx.nreg := hm ▸ argRegs_lt (regOfIn_mem len c.args c.argRegs l hl)
                refine ⟨?_, wf.reg l hl_lt⟩
                rw [ho]; exact bounded_sub (wf.reg r hr_lt) (bounded_var (by have := wf.base; omega))
              · simp at hp
          · exact calleeW_bounded wf hm args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec p mp
  | (_, .valArray _ _ _) :: args, _ :: regs, env, hr, h => by
    simp only [calleeW] at h
    exact calleeW_bounded wf hm args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) h
  | (_, .out _) :: _, _ :: _, _, _, h => by simp [calleeW] at h

private theorem envDen_agree_callee {ctx : Ctx} {s0 : State} {ρ1 ρ2 : Nat → Int} {T : List Node} {nv : Nat}
    (hw : WFT T) (ha : ∀ (j : Nat) (r : Row), T[j]? = some (Node.atom r) → bounded nv r) (ag : Agree nv ρ1 ρ2) :
    ∀ {env : List (String × WVal)} {env' : List (String × Val)},
      (∀ p ∈ env, p.2.calleeBd nv) →
      EnvDen ctx s0 ρ1 T env env' → EnvDen ctx s0 ρ2 T env env'
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => h
  | _ :: _, [], _, h => h
  | (x, v) :: more, (y, w) :: more', hb, ⟨hxy, hv, hrest⟩ =>
    ⟨hxy, WDen_agree_callee hw ha ag hv (hb (x, v) (List.mem_cons_self ..)),
     envDen_agree_callee hw ha ag (fun p mp => hb p (List.mem_cons_of_mem _ mp)) hrest⟩

private theorem valExprMatch_wev {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hpv : ctx.contract.preVals ctx.defs s0)
    {env1 env2 : List (String × WVal)} {env1' env2' : List (String × Val)}
    (hE1 : EnvDen ctx s0 ρ s.terms env1 env1') (hE2 : EnvDen ctx s0 ρ s.terms env2 env2')
    {e1 e2 : SExpr} {v : Val}
    (hm : (match weval ctx s.tab.find s WFUEL env1 e1, weval ctx s.tab.find s WFUEL env2 e2 with
      | some v1, some v2 =>
        match flatKey s.tab.find v1, flatKey s.tab.find v2 with
        | some k1, some k2 => sameKey s.facts k1 k2
        | _, _ => false
      | _, _ => false) = true)
    (hv : Value ctx.defs env2' e2 v) : Value ctx.defs env1' e1 v := by
  cases hw1 : weval ctx s.tab.find s WFUEL env1 e1 with
  | none => simp [hw1] at hm
  | some v1 =>
    cases hw2 : weval ctx s.tab.find s WFUEL env2 e2 with
    | none => simp [hw1, hw2] at hm
    | some v2 =>
      simp only [hw1, hw2] at hm
      cases fk1 : flatKey s.tab.find v1 with
      | none => simp [fk1] at hm
      | some k1 =>
        cases fk2 : flatKey s.tab.find v2 with
        | none => simp [fk1, fk2] at hm
        | some k2 =>
          simp only [fk1, fk2] at hm
          obtain ⟨B, hB⟩ := held_bound H hpv
          obtain ⟨a1, ea1, da1⟩ := weval_sound H wf hpv hB WFUEL env1 env1' e1 v1 hw1 hE1
          obtain ⟨a2, ea2, da2⟩ := weval_sound H wf hpv hB WFUEL env2 env2' e2 v2 hw2 hE2
          have e1k := flatKey_den wf da1 fk1
          have e2k := flatKey_den wf da2 fk2
          have eqk := sameKey_sound (ctx := ctx) (s0 := s0) (T := s.terms) H.facts hm
          have ha2v : a2 = v := Value.unique ⟨WFUEL + B, ea2⟩ hv
          have ha1v : a1 = v := by rw [e1k, eqk, ← e2k, ha2v]
          subst ha1v
          exact ⟨WFUEL + B, ea1⟩

mutual
private theorem valExprMatch_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hpv : ctx.contract.preVals ctx.defs s0)
    {env1 env2 : List (String × WVal)} {env1' env2' : List (String × Val)}
    (hE1 : EnvDen ctx s0 ρ s.terms env1 env1') (hE2 : EnvDen ctx s0 ρ s.terms env2 env2') :
    ∀ {e1 e2 : SExpr} {v : Val}, valExprMatch ctx s env1 env2 e1 e2 = true →
      Value ctx.defs env2' e2 v → Value ctx.defs env1' e1 v
  | e1, e2, v, hm, hv => by
    cases e1 with
    | call f1 a1 =>
      cases e2 with
      | call f2 a2 =>
        simp only [valExprMatch] at hm
        by_cases hb : (own.contains f1 || f1 == "len") = true
        · rw [if_pos hb] at hm; exact valExprMatch_wev H wf hpv hE1 hE2 hm hv
        · rw [if_neg hb] at hm
          simp only [Bool.and_eq_true, beq_iff_eq] at hm
          obtain ⟨rfl, hal⟩ := hm
          have hown : own.contains f1 = false := by cases h1 : own.contains f1 <;> simp_all
          have hlen : (f1 == "len") = false := by cases h1 : (f1 == "len") <;> simp_all
          obtain ⟨fuel, hf⟩ := hv
          cases fuel with
          | zero => simp [evalSpec] at hf
          | succ fuel =>
            simp only [evalSpec] at hf
            cases hl : evalList (evalSpec ctx.defs fuel env2') a2 with
            | none => simp [hl] at hf
            | some vs =>
              simp only [hl, hlen, Bool.false_eq_true, ↓reduceIte, hown] at hf
              cases hd : findDef ctx.defs f1 with
              | none => simp [hd] at hf
              | some d =>
                simp only [hd] at hf
                split at hf
                next hplen =>
                  obtain ⟨fl1, hl1⟩ := valExprMatchList_sound H wf hpv hE1 hE2 hal ⟨fuel, hl⟩
                  let F := max fuel fl1
                  have hL1 := evalList_mono (ev' := evalSpec ctx.defs F env1')
                    (fun a w h => evalSpec_mono ctx.defs fl1 h F (Nat.le_max_right _ _)) a1 hl1
                  have hB1 := evalSpec_mono ctx.defs fuel hf F (Nat.le_max_left _ _)
                  refine ⟨F + 1, ?_⟩
                  simp only [evalSpec, hL1, hlen, Bool.false_eq_true, ↓reduceIte, hown, hd, hplen, hB1]
                next => simp at hf
      | num _ | name _ | bin _ _ _ | ifx _ _ _ | index _ _ | list _ | nil | cons _ _ | letx _ _ _
      | each _ _ _ _ | slice _ _ _ | withx _ _ | record _ _ | field _ _ | theNumber _ _ _ _ _ | thePower _ _ _ =>
        simp only [valExprMatch] at hm; exact valExprMatch_wev H wf hpv hE1 hE2 hm hv
    | num _ | name _ | bin _ _ _ | ifx _ _ _ | index _ _ | list _ | nil | cons _ _ | letx _ _ _
    | each _ _ _ _ | slice _ _ _ | withx _ _ | record _ _ | field _ _ | theNumber _ _ _ _ _ | thePower _ _ _ =>
      simp only [valExprMatch] at hm; exact valExprMatch_wev H wf hpv hE1 hE2 hm hv

private theorem valExprMatchList_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hpv : ctx.contract.preVals ctx.defs s0)
    {env1 env2 : List (String × WVal)} {env1' env2' : List (String × Val)}
    (hE1 : EnvDen ctx s0 ρ s.terms env1 env1') (hE2 : EnvDen ctx s0 ρ s.terms env2 env2') :
    ∀ {a1 a2 : SExpr} {vs : List Val}, valExprMatchList ctx s env1 env2 a1 a2 = true →
      (∃ fl, evalList (evalSpec ctx.defs fl env2') a2 = some vs) →
      ∃ fl', evalList (evalSpec ctx.defs fl' env1') a1 = some vs
  | a1, a2, vs, hm, ⟨fl, hfl⟩ => by
    cases a1 with
    | nil =>
      cases a2 with
      | nil => simp only [evalList, Option.some.injEq] at hfl; subst hfl; exact ⟨0, rfl⟩
      | _ => simp [valExprMatchList] at hm
    | cons x1 r1 =>
      cases a2 with
      | cons x2 r2 =>
        simp only [valExprMatchList, Bool.and_eq_true] at hm
        simp only [evalList] at hfl
        cases hx : evalSpec ctx.defs fl env2' x2 with
        | none => simp [hx] at hfl
        | some vx =>
          cases hr : evalList (evalSpec ctx.defs fl env2') r2 with
          | none => simp [hx, hr] at hfl
          | some vr =>
            simp only [hx, hr, Option.some.injEq] at hfl; subst hfl
            obtain ⟨fx, hfx⟩ := valExprMatch_sound H wf hpv hE1 hE2 hm.1 ⟨fl, hx⟩
            obtain ⟨fr, hfr⟩ := valExprMatchList_sound H wf hpv hE1 hE2 hm.2 ⟨fl, hr⟩
            let F := max fx fr
            refine ⟨F, ?_⟩
            simp only [evalList, evalSpec_mono ctx.defs fx hfx F (Nat.le_max_left _ _),
              evalList_mono (ev' := evalSpec ctx.defs F env1') (fun a w h => evalSpec_mono ctx.defs fr h F (Nat.le_max_right _ _)) r1 hfr]
      | _ => simp [valExprMatchList] at hm
    | _ => simp [valExprMatchList] at hm
end

private theorem mapM_findAtom_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} (wf : WF ctx s) :
    ∀ {rows : List Row} {ids : List Nat}, (rows.mapM fun r => s.tab.find (.atom (Lin.word r))) = some ids →
      ids.length = rows.length ∧ ∀ k, k < rows.length →
        (den (inpOf ctx s0) ρ s.terms (ids.getD k 0) : Int) = ev ρ (rows.getD k (Lin.const 0)) % W32i
  | [], ids, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | r :: more, ids, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hf : s.tab.find (.atom (Lin.word r)) with
    | none => simp [hf] at h
    | some id =>
      simp only [hf, Option.bind_some] at h
      cases hrest : (more.mapM fun r => s.tab.find (.atom (Lin.word r))) with
      | none => simp [hrest] at h
      | some rest =>
        simp only [hrest, Option.bind_some, Option.pure_def, Option.some.injEq] at h; subst h
        obtain ⟨rlen, rden⟩ := mapM_findAtom_sound wf hrest
        refine ⟨by simp [rlen], fun k hk => ?_⟩
        cases k with
        | zero =>
          simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
          have hd := found_den (ctx := ctx) (s0 := s0) (ρ := ρ) (s := s) wf hf
          simp only [Node.value] at hd
          rw [hd, ev_word, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
        | succ k => exact rden k (by simpa using hk)

private theorem frameWordIds_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hst : ctx.contract.stackAt s0 ≤ s0.reg RSP)
    {off : Int} {nw : Nat} {ids : List Nat} (h : frameWordIds s off nw = some ids) :
    ids.length = nw ∧
    ids.map (fun id => Val.word (den (inpOf ctx s0) ρ s.terms id)) =
      (List.range nw).map (fun m => Val.word (load st.mem (((s0.reg RSP : Int) + off).toNat + 4 * m) 4)) := by
  unfold frameWordIds at h
  cases hpr : (if nw % 2 == 0 then framePairRows s off (nw / 2) else none) with
  | some rows =>
    simp only [hpr] at h
    have heven : nw % 2 = 0 ∧ framePairRows s off (nw / 2) = some rows := by
      split at hpr
      next he => exact ⟨by simpa using he, hpr⟩
      next => cases hpr
    obtain ⟨rlen, _, rmem⟩ := framePairRows_sound H wf hst (nw / 2) off heven.2
    obtain ⟨ilen, iden⟩ := mapM_findAtom_sound (ctx := ctx) (s0 := s0) (ρ := ρ) wf h
    have hnw : 2 * (nw / 2) = nw := by omega
    refine ⟨by omega, ?_⟩
    apply List.ext_getElem
    · simp; omega
    · intro m h1 h2
      have hm : m < nw := by simpa using h2
      simp only [List.getElem_map, List.getElem_range]
      have h1' := (rmem m (by omega)).2.2
      have h2' := iden m (by omega)
      rw [getD_of_lt ids 0 (by omega)] at h2'
      congr 1; omega
  | none =>
    simp only [hpr] at h
    obtain ⟨ilen, _, imem⟩ := frameWIds_sound H wf hst nw 0 off h
    refine ⟨ilen, ?_⟩
    apply List.ext_getElem
    · rw [List.length_map, List.length_map, List.length_range, ilen]
    · intro m h1 h2
      have hm : m < nw := by simpa using h2
      simp only [List.getElem_map, List.getElem_range]
      have h3 : load st.mem (((s0.reg RSP : Int) + off).toNat + 4 * m) 4 = den (inpOf ctx s0) ρ s.terms (ids.getD m 0) := by
        simpa using (imem m hm).2.2
      rw [getD_of_lt ids 0 (by omega)] at h3
      exact congrArg Val.word h3.symm

private theorem wvalsMatchIds_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} (wf : WF ctx s) :
    ∀ {ws : List WVal} {ids : List Nat} {as : List Val},
      wvalsMatchIds s.tab.find ws ids = true → WDen ctx s0 ρ s.terms (.list ws) (.list as) →
      as = ids.map fun id => Val.word (den (inpOf ctx s0) ρ s.terms id)
  | ws, ids, as, hm, hd => by
    cases ws with
    | nil =>
      cases ids with
      | nil => cases hd; rfl
      | cons _ _ => simp [wvalsMatchIds] at hm
    | cons w ws =>
      cases ids with
      | nil => simp [wvalsMatchIds] at hm
      | cons id ids =>
        cases w with
        | word xs =>
          cases hd with
          | cons hw hrest =>
            cases hw
            simp only [wvalsMatchIds, Bool.and_eq_true, beq_iff_eq] at hm
            rw [wvalsMatchIds_sound wf hm.2 hrest, ← idOf_den (ctx := ctx) (s0 := s0) (ρ := ρ) wf hm.1]
            rfl
        | _ => simp [wvalsMatchIds] at hm

private theorem countFrameValEntries_sound {ctx : Ctx} {s : Sym} {env : List (String × WVal)}
    {cf : Int} {el : Nat} {idx : String} {expr : SExpr} :
    ∀ (fuel start i : Nat), start ≤ i → i < countFrameValEntries ctx s env cf el idx expr fuel start →
      cf + (el : Int) * (i : Int) + (el : Int) ≤ 0 ∧
      ∃ ids ws, frameWordIds s (cf + (el : Int) * (i : Int)) (el / 4) = some ids ∧
        weval ctx s.tab.find s WFUEL ((idx, .int i) :: env) expr = some (.list ws) ∧
        ws.length = el / 4 ∧ wvalsMatchIds s.tab.find ws ids = true
  | 0, start, i, hle, hlt => by simp [countFrameValEntries] at hlt; omega
  | fuel + 1, start, i, hle, hlt => by
    simp only [countFrameValEntries] at hlt
    split at hlt
    · omega
    next hfit =>
      cases hf : frameWordIds s (cf + (el : Int) * (start : Int)) (el / 4) with
      | none => simp [hf] at hlt; omega
      | some ids =>
        simp only [hf] at hlt
        cases hw : weval ctx s.tab.find s WFUEL ((idx, .int start) :: env) expr with
        | none => simp [hw] at hlt; omega
        | some v =>
          cases v with
          | list ws =>
            simp only [hw] at hlt
            split at hlt
            next hok =>
              simp only [Bool.and_eq_true, beq_iff_eq] at hok
              by_cases heq : i = start
              · subst heq
                exact ⟨by simpa using hfit, ids, ws, hf, hw, hok.1, hok.2⟩
              · exact countFrameValEntries_sound fuel (start + 1) i (by omega) hlt
            next => omega
          | _ => simp [hw] at hlt; omega

private theorem callValArraysOk_sound {ctx : Ctx} {p q : Program} {s0 st : State} (E : Setting ctx p s0)
    {ρ : Nat → Int} {sT : Sym} {c : Contract} {sp : Int} {cw : Option (Int × Nat)}
    {env : List (String × WVal)} {items : Items} {res : Unit × Items} {i : Instr}
    (hva : callValArraysOk ctx sT sp cw env c items = .ok res)
    (HT : Holds ctx s0 ρ sT st) (wfT : WF ctx sT)
    (F : Fits ctx st i c)
    (henv : EnvDen ctx s0 ρ sT.terms env (c.envW (afterCall p q i st)))
    (henv_bd : ∀ pair ∈ env, pair.2.calleeBd sT.nvars)
    (hrsp : (st.reg RSP : Int) = s0.reg RSP + sp)
    (hg : sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot - (c.stackAt (afterCall p q i st) : Int))
    (houts_disj_va : ∀ x0 r0 l0 ch0 el0, (x0, r0, l0, ch0, el0) ∈ ctx.contract.valArrays →
      ∀ x' r' n', (x', r', n') ∈ c.outs →
        s0.reg r0 + el0 * (s0.reg l0 / ch0) ≤ (afterCall p q i st).reg r' ∨
        (afterCall p q i st).reg r' + n' ≤ s0.reg r0)
    (houts_disj_frame : ∀ cf nbytes, sp ≤ cf → cf + (nbytes : Int) ≤ 0 →
      (∀ cwo nout, cw = some (cwo, nout) → cf + (nbytes : Int) ≤ cwo ∨ cwo + (nout : Int) ≤ cf) →
      ∀ x' r' n', (x', r', n') ∈ c.outs →
        ((s0.reg RSP : Int) + cf).toNat + nbytes ≤ (afterCall p q i st).reg r' ∨
        (afterCall p q i st).reg r' + n' ≤ ((s0.reg RSP : Int) + cf).toNat) :
    let s1 := afterCall p q i st
    (∀ x r l ch el, (x, r, l, ch, el) ∈ c.valArrays →
      s1.reg r + el * (s1.reg l / ch) < M64 ∧
      (s1.reg r + el * (s1.reg l / ch) ≤ s1.reg RSP - c.stackAt s1 ∨ s1.reg RSP + c.slot ≤ s1.reg r) ∧
      ∀ x' r' n', (x', r', n') ∈ c.outs → s1.reg r + el * (s1.reg l / ch) ≤ s1.reg r' ∨ s1.reg r' + n' ≤ s1.reg r) ∧
    (∀ a, c.inValArray s1 a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (ctx.contract.preVals ctx.defs s0 → c.preVals ctx.defs s1) := by
  intro s1
  change sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot - (c.stackAt s1 : Int) at hg
  change ∀ x0 r0 l0 ch0 el0, (x0, r0, l0, ch0, el0) ∈ ctx.contract.valArrays →
      ∀ x' r' n', (x', r', n') ∈ c.outs →
        s0.reg r0 + el0 * (s0.reg l0 / ch0) ≤ s1.reg r' ∨ s1.reg r' + n' ≤ s0.reg r0 at houts_disj_va
  change ∀ cf nbytes, sp ≤ cf → cf + (nbytes : Int) ≤ 0 →
      (∀ cwo nout, cw = some (cwo, nout) → cf + (nbytes : Int) ≤ cwo ∨ cwo + (nout : Int) ≤ cf) →
      ∀ x' r' n', (x', r', n') ∈ c.outs →
        ((s0.reg RSP : Int) + cf).toNat + nbytes ≤ s1.reg r' ∨ s1.reg r' + n' ≤ ((s0.reg RSP : Int) + cf).toNat at houts_disj_frame
  have hstack := E.stackAt
  have habove := E.above
  have hsmallsp := HT.small RSP
  have hslot := F.slot
  have h8 : c.slot ≤ st.reg RSP := by omega
  have s1rsp : s1.reg RSP = st.reg RSP - c.slot := afterCall_rsp F.link
  have s1reg : ∀ r, CallKeeps r → s1.reg r = st.reg r := fun r hr => afterCall_reg F.link hr
  have s1mem : ∀ x, x < st.reg RSP - c.slot ∨ st.reg RSP ≤ x → s1.mem x = st.mem x :=
    fun x hx => afterCall_mem F.link h8 hx
  have per : ∀ x r l ch el, (x, r, l, ch, el) ∈ c.valArrays →
      (s1.reg r + el * (s1.reg l / ch) < M64 ∧
       (s1.reg r + el * (s1.reg l / ch) ≤ s1.reg RSP - c.stackAt s1 ∨ s1.reg RSP + c.slot ≤ s1.reg r) ∧
       ∀ x' r' n', (x', r', n') ∈ c.outs → s1.reg r + el * (s1.reg l / ch) ≤ s1.reg r' ∨ s1.reg r' + n' ≤ s1.reg r) ∧
      (∀ a, s1.reg r ≤ a → a < s1.reg r + el * (s1.reg l / ch) → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
      (ctx.contract.preVals ctx.defs s0 → ∀ idx expr, c.valSpecOf x = some (idx, expr) →
        ∀ j, j < s1.reg l / ch →
          Value ctx.defs ((idx, .int j) :: c.envW s1) expr
            (.list ((List.range (el / 4)).map fun m => Val.word (load s1.mem (s1.reg r + el * j + 4 * m) 4)))) := by
    intro x r l ch el mva
    obtain ⟨ra, hch_pos, hel_pos, hel4, lenNm, hlenReg⟩ := valArraysIn_mem c c.args c.argRegs x r l ch el mva
    have la := regOfIn_mem lenNm c.args c.argRegs l hlenReg
    obtain ⟨r_lt, r_keep⟩ := F.arg ra
    obtain ⟨l_lt, l_keep⟩ := F.arg la
    have hs1r : s1.reg r = st.reg r := s1reg r r_keep
    have hs1l : s1.reg l = st.reg l := s1reg l l_keep
    have hreg_r := HT.reg r r_lt
    have hreg_l := HT.reg l l_lt
    obtain ⟨items1, res1, hitem⟩ := each_mem hva (x, r, l, ch, el) mva
    dsimp only at hitem
    rw [if_neg (by simp [hch_pos, hel_pos, hel4])] at hitem
    obtain ⟨_, items2, _, hitem⟩ := V.bind_ok hitem
    cases hfv : findValArray (sT.reg r) ctx.contract.valArrays 0 with
    | some found =>
      obtain ⟨k0, x0, r0, l0, ch0, el0, d⟩ := found
      simp only [hfv] at hitem
      obtain ⟨_, hk0, hdo, hd0, hd4⟩ := findValArray_spec ctx.contract.valArrays 0 k0 hfv
      simp only [Nat.sub_zero] at hk0
      have mva0 := List.mem_of_getElem? hk0
      obtain ⟨r0_lt, l0_lt, _, _, _⟩ := valArrays_lt mva0
      obtain ⟨hva0_m64, hva0_fr, hva0_out⟩ := E.valArray mva0
      split at hitem
      · exact (refuse_ok hitem).elim
      next halign =>
        have ha' : ch = ch0 ∧ el = el0 ∧ d % (el : Int) = 0 := by simpa using halign
        obtain ⟨rfl, rfl, hdel⟩ := ha'
        obtain ⟨_, items3, hlen_ent, hitem⟩ := V.bind_ok hitem
        have hle0 := entail_sound hlen_ent ρ HT.facts
        rw [ev_sub, ev_var, ev_add, ev_const, ← hreg_l, HT.entry l0 l0_lt] at hle0
        have hr0_eq : (st.reg r : Int) = s0.reg r0 + d := by
          have := ev_isConst (ρ := ρ) hdo
          rw [ev_sub, ev_var, ← hreg_r, HT.entry r0 r0_lt] at this; omega
        let shift := d.toNat / el
        have hd_eq : d.toNat = el * shift := by
          have h1 : d.toNat % el = 0 := by
            have h0 : (d.toNat : Int) = d := Int.toNat_of_nonneg hd0
            have h2 : ((d.toNat % el : Nat) : Int) = (d.toNat : Int) % (el : Int) := Int.natCast_emod d.toNat el
            rw [h0, hdel] at h2; exact Int.ofNat.inj h2
          exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h1)).symm
        have hs1r_eq : s1.reg r = s0.reg r0 + el * shift := by omega
        have hlen_nat : shift * ch + s1.reg l ≤ s0.reg l0 := by
          change 0 ≤ (s0.reg l0 : Int) - (((shift * ch : Nat) : Int) + (st.reg l : Int)) at hle0
          omega
        have hdiv_le : shift + s1.reg l / ch ≤ s0.reg l0 / ch := by
          have h1 : (shift * ch + s1.reg l) / ch = shift + s1.reg l / ch := by
            rw [Nat.mul_comm, Nat.mul_add_div hch_pos]
          rw [← h1]; exact Nat.div_le_div_right hlen_nat
        have hend_le : s1.reg r + el * (s1.reg l / ch) ≤ s0.reg r0 + el * (s0.reg l0 / ch) := by
          rw [hs1r_eq, Nat.add_assoc, ← Nat.mul_add]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left el hdiv_le) _
        refine ⟨⟨by omega, by
          rw [s1rsp]
          rcases hva0_fr with hl | hr
          · left; omega
          · right; omega, fun x' r' n' mo => by
          have := houts_disj_va x0 r0 l0 ch el mva0 x' r' n' mo; omega⟩, ?_, ?_⟩
        · intro a ha1 ha2
          simp only [Contract.perm, Bool.or_eq_true]
          left; right
          unfold Contract.inValArray
          exact List.any_eq_true.mpr ⟨(x0, r0, l0, ch, el), mva0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        · intro hpv idx expr hvs j hj
          simp only [hvs] at hitem
          cases hvs0 : ctx.contract.valSpecOf x0 with
          | none => simp only [hvs0] at hitem; exact (refuse_ok hitem).elim
          | some spec0 =>
            obtain ⟨idx0, expr0⟩ := spec0
            simp only [hvs0] at hitem
            split at hitem
            next hmatch =>
              let u := sT.nvars
              let ρu : Nat → Int := fun v => if v = u then (j : Int) else ρ v
              have agu : Agree u ρ ρu := fun v hv => by simp [ρu, Nat.ne_of_lt hv]
              have hHTu := HT.agree wfT agu
              have hch_j : (ch : Int) * (j : Int) + (ch : Int) ≤ (s1.reg l : Int) := by
                have h1 : (j + 1) * ch ≤ s1.reg l := by
                  have h2 := Nat.mul_le_mul_right ch (Nat.succ_le_of_lt hj)
                  exact Nat.le_trans h2 (Nat.div_mul_le_self (s1.reg l) ch)
                have h0 : ((j + 1) * ch : Nat) = j * ch + ch := by rw [Nat.add_mul, Nat.one_mul]
                have hcast : ((j * ch : Nat) : Int) = (ch : Int) * (j : Int) := by rw [Nat.mul_comm, Int.natCast_mul]
                omega
              have hch_sj : (ch : Int) * (j : Int) + ((shift + 1) * ch : Nat) ≤ (s0.reg l0 : Int) := by
                have h1 : ((shift + 1) * ch : Nat) = shift * ch + ch := by rw [Nat.add_mul, Nat.one_mul]
                omega
              have hl0_lt_u : l0 < u := by have := wfT.base; have : l0 < ctx.nreg := l0_lt; omega
              have hfacts_u : ∀ f ∈ ([Lin.var u, Lin.scale ch (Lin.var u),
                  Lin.sub (sT.reg l) (Lin.add (Lin.scale ch (Lin.var u)) (Lin.const ch)),
                  Lin.sub (Lin.var l0) (Lin.add (Lin.scale ch (Lin.var u)) (Lin.const ((shift + 1) * ch)))] ++ sT.facts),
                  f.holds ρu := by
                intro f mf
                rcases List.mem_append.mp mf with mf | mf
                · simp only [List.mem_cons, List.mem_nil_iff, or_false] at mf
                  rcases mf with rfl | rfl | rfl | rfl
                  · rw [holds_iff, ev_var]; simp [ρu]
                  · rw [holds_iff, ev_scale, ev_var]; simp [ρu]; exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
                  · rw [holds_iff, ev_sub, ev_add, ev_scale, ev_var, ev_const, ← ev_agree (wfT.reg l l_lt) agu, ← hreg_l]
                    simp only [ρu, ↓reduceIte]; omega
                  · rw [holds_iff, ev_sub, ev_add, ev_scale, ev_var, ev_var, ev_const,
                      ← agu l0 hl0_lt_u, HT.entry l0 l0_lt]
                    simp only [ρu, ↓reduceIte]
                    have hmul_s1 : (((shift + 1) * ch : Nat) : Int) = ((shift : Int) + 1) * (ch : Int) := by
                      rw [Int.natCast_mul, Int.natCast_add]; rfl
                    omega
                · exact hHTu.facts f mf
              have hle_u : u ≤ u + 1 := Nat.le_succ _
              have hHu : Holds ctx s0 ρu { sT with nvars := u + 1, facts := [Lin.var u, Lin.scale ch (Lin.var u),
                  Lin.sub (sT.reg l) (Lin.add (Lin.scale ch (Lin.var u)) (Lin.const ch)),
                  Lin.sub (Lin.var l0) (Lin.add (Lin.scale ch (Lin.var u)) (Lin.const ((shift + 1) * ch)))] ++ sT.facts } st :=
                { hHTu with facts := hfacts_u }
              have hwf_facts : ∀ f ∈ ([Lin.var u, Lin.scale ch (Lin.var u),
                  Lin.sub (sT.reg l) (Lin.add (Lin.scale ch (Lin.var u)) (Lin.const ch)),
                  Lin.sub (Lin.var l0) (Lin.add (Lin.scale ch (Lin.var u)) (Lin.const ((shift + 1) * ch)))] ++ sT.facts),
                  bounded (u + 1) f := by
                intro f mf
                rcases List.mem_append.mp mf with mf | mf
                · simp only [List.mem_cons, List.mem_nil_iff, or_false] at mf
                  rcases mf with rfl | rfl | rfl | rfl
                  · exact bounded_var (Nat.lt_succ_self u)
                  · exact bounded_scale ch (bounded_var (Nat.lt_succ_self u))
                  · exact bounded_sub (bounded_mono hle_u (wfT.reg l l_lt))
                      (bounded_add (bounded_scale ch (bounded_var (Nat.lt_succ_self u))) (bounded_const _ _))
                  · exact bounded_sub (bounded_var (Nat.lt_of_lt_of_le hl0_lt_u hle_u))
                      (bounded_add (bounded_scale ch (bounded_var (Nat.lt_succ_self u))) (bounded_const _ _))
                · exact bounded_mono hle_u (wfT.facts f mf)
              have hwfu : WF ctx { sT with nvars := u + 1, facts := [Lin.var u, Lin.scale ch (Lin.var u),
                  Lin.sub (sT.reg l) (Lin.add (Lin.scale ch (Lin.var u)) (Lin.const ch)),
                  Lin.sub (Lin.var l0) (Lin.add (Lin.scale ch (Lin.var u)) (Lin.const ((shift + 1) * ch)))] ++ sT.facts } :=
                ⟨Nat.le_trans wfT.base hle_u,
                 fun r' hr' => bounded_mono hle_u (wfT.reg r' hr'),
                 Flag.bounded_mono hle_u wfT.zf, Flag.bounded_mono hle_u wfT.cf,
                 fun o w m => bounded_mono hle_u (wfT.frame o w m), wfT.frameW, hwf_facts,
                 fun u' r' o m => ⟨Nat.lt_of_lt_of_le (wfT.bytes u' r' o m).1 hle_u, bounded_mono hle_u (wfT.bytes u' r' o m).2⟩,
                 fun f m => SFact.bounded_mono hle_u (wfT.spec f m),
                 fun w o x' m => ⟨bounded_mono hle_u (wfT.wrote w o x' m).1, bounded_mono hle_u (wfT.wrote w o x' m).2⟩,
                 ⟨wfT.words.table, fun j' r' hj' => bounded_mono hle_u (wfT.words.atoms j' r' hj'),
                  wfT.words.vec, wfT.words.rotrs, wfT.words.wrote,
                  fun o ids' m => ⟨bounded_mono hle_u (wfT.words.spill o ids' m).1, (wfT.words.spill o ids' m).2⟩⟩,
                 fun k' mk' => Known.wf_mono hle_u (Nat.le_refl _) (wfT.known k' mk'),
                 fun rg hrg => ⟨bounded_mono hle_u (wfT.range rg hrg).1, fun x' mx' => SVal.bounded_mono hle_u ((wfT.range rg hrg).2 x' mx')⟩⟩
              have hE1u : EnvDen ctx s0 ρu sT.terms ((idx, .num (Lin.var u)) :: env) ((idx, .int j) :: c.envW s1) := by
                refine ⟨rfl, ?_, envDen_agree_callee wfT.words.table wfT.words.atoms agu henv_bd henv⟩
                have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρu) (T := sT.terms) (Lin.var u)
                simpa [ev_var, ρu] using this
              have hE2u : EnvDen ctx s0 ρu sT.terms ((idx0, .num (Lin.add (Lin.const shift) (Lin.var u))) :: wenv ctx.contract)
                  ((idx0, .int ((shift + j : Nat) : Int)) :: ctx.contract.envW s0) := by
                refine ⟨rfl, ?_, wenv_sound E hHu⟩
                have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρu) (T := sT.terms) (Lin.add (Lin.const shift) (Lin.var u))
                have hev : ev ρu (Lin.add (Lin.const shift) (Lin.var u)) = ((shift + j : Nat) : Int) := by
                  rw [ev_add, ev_const, ev_var]; simp [ρu]
                rwa [hev] at this
              have hval0 := hpv x0 r0 l0 ch el mva0 idx0 expr0 hvs0 (shift + j) (by omega)
              have hmem_va : ∀ m, m < el / 4 →
                  load s0.mem (s0.reg r0 + el * (shift + j) + 4 * m) 4 = load s1.mem (s1.reg r + el * j + 4 * m) 4 := by
                intro m hm
                have heq_addr : s0.reg r0 + el * (shift + j) + 4 * m = s1.reg r + el * j + 4 * m := by
                  rw [hs1r_eq, Nat.mul_add]; omega
                rw [heq_addr]
                apply load_congr
                intro a ha1 ha2
                have ha_hi : a < s0.reg r0 + el * (s0.reg l0 / ch) := by
                  have h4e : 4 * m + 4 ≤ el := by omega
                  have h1 : el * j + el ≤ el * (s1.reg l / ch) := by
                    have := Nat.mul_le_mul_left el (Nat.succ_le_of_lt hj)
                    simpa [Nat.mul_succ] using this
                  have h2 : el * (shift + j) = el * shift + el * j := Nat.mul_add el shift j
                  omega
                have ha_in0 : s0.reg r0 ≤ a ∧ a < s0.reg r0 + el * (s0.reg l0 / ch) := by
                  have h2 : el * (shift + j) = el * shift + el * j := Nat.mul_add el shift j
                  omega
                rw [s1mem a (by omega)]
                exact (HT.mem a
                  (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
                  (by unfold Contract.inOut; rw [List.any_eq_false]; intro o mo
                      obtain ⟨x', r', n'⟩ := o
                      have := hva0_out x' r' n' mo
                      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; omega)).symm
              have hlist_eq : ((List.range (el / 4)).map fun m => Val.word (load s0.mem (s0.reg r0 + el * (shift + j) + 4 * m) 4)) =
                  ((List.range (el / 4)).map fun m => Val.word (load s1.mem (s1.reg r + el * j + 4 * m) 4)) :=
                List.map_congr_left fun m mm => congrArg Val.word (hmem_va m (List.mem_range.mp mm))
              rw [hlist_eq] at hval0
              exact valExprMatch_sound hHu hwfu hpv hE1u hE2u hmatch hval0
            next => exact (refuse_ok hitem).elim
    | none =>
      simp only [hfv] at hitem
      cases hfa : frameAt sT r with
      | none => simp only [hfa] at hitem; exact (refuse_ok hitem).elim
      | some cf =>
        simp only [hfa] at hitem
        split at hitem
        · exact (refuse_ok hitem).elim
        next hcf =>
          have hcf' : sp ≤ cf ∧ cf ≤ 0 := by simpa using hcf
          obtain ⟨hsp_cf, hcf0⟩ := hcf'
          have hframe_body : ∀ (count : Nat) (b : Bool),
              count = (match c.valSpecOf x with
                | none => (-cf).toNat / el
                | some (idx, expr) => countFrameValEntries ctx sT env cf el idx expr (min ((-cf).toNat / el) 64) 0) →
              (b = true → sp ≤ cf ∧ cf + (el : Int) * (count : Int) ≤ 0 ∧
                ∀ cwo nout, cw = some (cwo, nout) → cf + (el : Int) * (count : Int) ≤ cwo ∨ cwo + (nout : Int) ≤ cf) →
              (if (!b) = true
                then refuse "a called function's value array in the frame overlaps the buffer it writes or exceeds the frame"
                else entail sT.facts (Lin.sub (Lin.const ((((count + 1) : Int) * (ch : Int)) - 1)) (sT.reg l))) items2 = .ok res1 →
              (s1.reg r + el * (s1.reg l / ch) < M64 ∧
               (s1.reg r + el * (s1.reg l / ch) ≤ s1.reg RSP - c.stackAt s1 ∨ s1.reg RSP + c.slot ≤ s1.reg r) ∧
               ∀ x' r' n', (x', r', n') ∈ c.outs → s1.reg r + el * (s1.reg l / ch) ≤ s1.reg r' ∨ s1.reg r' + n' ≤ s1.reg r) ∧
              (∀ a, s1.reg r ≤ a → a < s1.reg r + el * (s1.reg l / ch) → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
              (ctx.contract.preVals ctx.defs s0 → ∀ idx expr, c.valSpecOf x = some (idx, expr) →
                ∀ j, j < s1.reg l / ch →
                  Value ctx.defs ((idx, .int j) :: c.envW s1) expr
                    (.list ((List.range (el / 4)).map fun m => Val.word (load s1.mem (s1.reg r + el * j + 4 * m) 4)))) := by
            intro count b hcnt hb hite
            cases b with
            | false =>
              simp only [Bool.not_false, ↓reduceIte] at hite
              exact (refuse_ok hite).elim
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hite
              obtain ⟨_, hcf_end, hdisj⟩ := hb rfl
              have hle_cnt := entail_sound hite ρ HT.facts
              rw [ev_sub, ev_const, ← hreg_l] at hle_cnt
              have hmul_ch : (((count + 1) * ch : Nat) : Int) = ((count + 1) : Int) * (ch : Int) := by
                rw [Int.natCast_mul, Int.natCast_add]; rfl
              have hdiv_cnt : s1.reg l / ch ≤ count := by
                have h1 : s1.reg l < (count + 1) * ch := by omega
                have h2 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h1)
                omega
              have hreg_cf : (st.reg r : Int) = s0.reg RSP + cf := by
                have e := ev_isConst (ρ := ρ) (show Lin.isConst (Lin.sub (sT.reg r) (Lin.var RSP)) = some cf from hfa)
                rw [ev_sub, ev_var, ← hreg_r, HT.entry RSP ctx.rsp_lt] at e; omega
              have hs1r_cf : s1.reg r = ((s0.reg RSP : Int) + cf).toNat := by omega
              have hcf_mul_le : el * (s1.reg l / ch) ≤ el * count := Nat.mul_le_mul_left el hdiv_cnt
              have hmul_el : ((el * count : Nat) : Int) = (el : Int) * (count : Int) := Int.natCast_mul el count
              refine ⟨⟨by omega, Or.inr (by rw [s1rsp]; omega), fun x' r' n' mo => by
                have := houts_disj_frame cf (el * count) hsp_cf (by omega)
                  (fun cwo nout hcw => by have := hdisj cwo nout hcw; omega) x' r' n' mo
                omega⟩, ?_, ?_⟩
              · intro a ha1 ha2
                simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
                left; left; left; left; left; left; omega
              · intro hpv idx expr hvs j hj
                have hj_cnt : j < countFrameValEntries ctx sT env cf el idx expr (min ((-cf).toNat / el) 64) 0 := by
                  simp only [hvs] at hcnt; omega
                obtain ⟨hfit_j, ids, ws, hfw, hwev, hwlen, hmatch⟩ :=
                  countFrameValEntries_sound (min ((-cf).toNat / el) 64) 0 j (Nat.zero_le j) hj_cnt
                obtain ⟨B, hB⟩ := held_bound HT hpv
                obtain ⟨a, ea, da⟩ := weval_sound HT wfT hpv hB WFUEL ((idx, .int j) :: env) ((idx, .int j) :: c.envW s1) expr (.list ws) hwev ⟨rfl, WDen.int j, henv⟩
                obtain ⟨as, rfl⟩ := WDen.list_inv da
                have has := wvalsMatchIds_sound wfT hmatch da
                obtain ⟨_, hids_map⟩ := frameWordIds_sound HT wfT hstack hfw
                rw [has, hids_map] at ea
                have hmem_eq : ((List.range (el / 4)).map fun m => Val.word (load st.mem (((s0.reg RSP : Int) + (cf + (el : Int) * (j : Int))).toNat + 4 * m) 4)) =
                    ((List.range (el / 4)).map fun m => Val.word (load s1.mem (s1.reg r + el * j + 4 * m) 4)) := by
                  apply List.map_congr_left
                  intro m mm
                  have hm := List.mem_range.mp mm
                  have haddr : ((s0.reg RSP : Int) + (cf + (el : Int) * (j : Int))).toNat + 4 * m = s1.reg r + el * j + 4 * m := by
                    have : (el : Int) * (j : Int) = ((el * j : Nat) : Int) := (Int.natCast_mul el j).symm
                    omega
                  rw [haddr]
                  congr 1
                  apply load_congr
                  intro a ha1 ha2
                  exact (s1mem a (Or.inr (by omega))).symm
                rw [hmem_eq] at ea
                exact ⟨WFUEL + B, ea⟩
          cases hsp_v : c.valSpecOf x with
          | none =>
            simp only [hsp_v] at hitem
            have hres := hframe_body ((-cf).toNat / el) _ (by simp [hsp_v]) (fun hbt => by
              cases cw with
              | none => simp only [Bool.and_eq_true, decide_eq_true_eq] at hbt; exact ⟨hbt.1.1, hbt.1.2, fun _ _ h => nomatch h⟩
              | some p => simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hbt; exact ⟨hbt.1.1, hbt.1.2, fun cwo nout h => by injection h with h; cases h; exact hbt.2⟩) hitem
            exact ⟨hres.1, hres.2.1, fun hpv idx expr h => nomatch h⟩
          | some p_v =>
            obtain ⟨idx_v, expr_v⟩ := p_v
            simp only [hsp_v] at hitem
            have hres := hframe_body (countFrameValEntries ctx sT env cf el idx_v expr_v (min ((-cf).toNat / el) 64) 0) _ (by simp [hsp_v]) (fun hbt => by
              cases cw with
              | none => simp only [Bool.and_eq_true, decide_eq_true_eq] at hbt; exact ⟨hbt.1.1, hbt.1.2, fun _ _ h => nomatch h⟩
              | some p => simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hbt; exact ⟨hbt.1.1, hbt.1.2, fun cwo nout h => by injection h with h; cases h; exact hbt.2⟩) hitem
            exact ⟨hres.1, hres.2.1, fun hpv idx expr h => hres.2.2 hpv idx expr (by rw [hsp_v, h])⟩
  refine ⟨fun x r l ch el m => (per x r l ch el m).1, ?_, fun hpv x r l ch el m => (per x r l ch el m).2.2 hpv⟩
  intro a ha
  obtain ⟨⟨x, r, l, ch, el⟩, m, hin⟩ := List.any_eq_true.mp ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
  exact (per x r l ch el m).2.1 a hin.1 hin.2

private theorem nums_eq_of_bytes {mem : Nat → Byte} {base n : Nat} {nums l : List Nat}
    (hn4 : n % 4 = 0) (hnums : nums.length = n / 4) (hlt : ∀ v ∈ nums, v < W32)
    (hlb : l.map (fun (b : Nat) => Val.int b) = wordBytes nums) (hll : l.length = n)
    (hlm : ∀ k (hk : k < n), (mem (base + k)).val = l[k]'(hll ▸ hk)) :
    nums = (List.range (n / 4)).map fun k => load mem (base + 4 * k) 4 := by
  obtain ⟨hl4, hlget⟩ := wordBytes_get nums l hlb
  apply List.ext_getElem
  · simp [hnums]
  · intro k h1 h2
    have hk : k < n / 4 := by simpa using h2
    simp only [List.getElem_map, List.getElem_range]
    have hlt_k : nums[k] < 4294967296 := hlt nums[k] (List.getElem_mem h1)
    symm
    apply load4_of_bytes mem (base + 4 * k) nums[k] hlt_k
    intro bb hbb
    have hlt' : 4 * k + bb < l.length := by omega
    have hm := hlm (4 * k + bb) (by omega)
    rw [show base + (4 * k + bb) = base + 4 * k + bb by omega] at hm
    rw [hm, ← getD_of_lt l 0 hlt', hlget k (by omega) bb hbb, getD_of_lt nums 0 h1]

theorem postW_plain {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {c : Contract} {s1 : State}
    {plan : CallW} {env : List (String × WVal)} {args : SExpr} {vs : List WVal} {d : Def} {n : Nat} {l : List Nat}
    (HT : Holds ctx s0 ρ { s with tab := plan.tab } st) (wfT : WF ctx { s with tab := plan.tab })
    (hpv : ctx.contract.preVals ctx.defs s0)
    (henv : EnvDen ctx s0 ρ plan.terms env (c.envW s1))
    (hown : own.contains plan.g = false) (hglen : plan.g ≠ "len")
    (hwl : wevalList (weval ctx plan.tab.find { s with tab := plan.tab } WFUEL env) args = some vs)
    (hfd : findDef ctx.defs plan.g = some d) (hfk : flatKeys plan.tab.find vs = some plan.keys)
    (hdl : d.params.length = plan.keys.length) (hll : l.length = n) (hn4 : n % 4 = 0)
    (hval : Value ctx.defs (c.envW s1) (.call "bytes_of" (.cons (.call plan.g args) .nil)) (.bytes l)) :
    ∃ nums : List Nat, nums.length = n / 4 ∧ (∀ v ∈ nums, v < W32) ∧
      l.map (fun (b : Nat) => Val.int b) = wordBytes nums ∧
      Value ctx.defs (d.params.zip (plan.keys.map (Key.val ctx s0 ρ plan.terms))) d.body (.list (nums.map Val.word)) := by
  obtain ⟨B, hB⟩ := held_bound HT hpv
  obtain ⟨as, eas, das⟩ := wevalList_sound (ev' := evalSpec ctx.defs (WFUEL + B) (c.envW s1))
    (fun e' v' hv' => weval_sound HT wfT hpv hB WFUEL env _ e' v' hv' henv) args vs hwl
  have ekeys : as = plan.keys.map (Key.val ctx s0 ρ plan.terms) := flatKeys_den wfT das hfk
  obtain ⟨f2, as2, d2, nums, ha2, hd2, hlen2, hev2, hlt, hlb⟩ := bytes_of_call hown hglen hval
  rw [hfd] at hd2; injection hd2 with hd2; subst hd2
  obtain ⟨hl4, _⟩ := wordBytes_get nums l hlb
  have same : as2 = as := by
    have a1 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.envW s1))
      (fun a v hh => evalSpec_mono ctx.defs f2 hh _ (Nat.le_max_left _ _)) args ha2
    have a2 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.envW s1))
      (fun a v hh => evalSpec_mono ctx.defs (WFUEL + B) hh _ (Nat.le_max_right _ _)) args eas
    rw [a1] at a2; injection a2
  subst same
  exact ⟨nums, by omega, hlt, hlb, f2, by rw [← ekeys]; exact hev2⟩

theorem postW_rec {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {c : Contract} {s1 : State}
    {plan : CallW} {env : List (String × WVal)} {args : SExpr} {vs : List WVal} {d : Def} {n : Nat} {l : List Nat}
    {x : String} {body : SExpr}
    (HT : Holds ctx s0 ρ { s with tab := plan.tab } st) (wfT : WF ctx { s with tab := plan.tab })
    (henv : EnvDen ctx s0 ρ plan.terms env (c.envW s1))
    (hown : own.contains plan.g = false) (hglen : plan.g ≠ "len")
    (hwl : wevalList (weval ctx plan.tab.find { s with tab := plan.tab } WFUEL env) args = some vs)
    (hfd : findDef ctx.defs plan.g = some d) (hfk : flatKeys plan.tab.find vs = some plan.keys)
    (hdl : d.params.length = plan.keys.length) (hll : l.length = n) (hn4 : n % 4 = 0)
    (hval : Value ctx.defs (c.envW s1) (.call "bytes_of" (.cons (.letx x (.call plan.g args) body) .nil)) (.bytes l))
    (hpb : parseRecBody x body = some plan.recFields)
    (hsum : (plan.recFields.map RecField.nwords).sum = n / 4)
    (hdist : allDistinct (plan.recFields.map RecField.name) = true)
    (hrr : returnsRecord (plan.recFields.map RecField.name) d.body = true) :
    ∃ (nums : List Nat) (fvs : List (String × Val)),
      nums.length = n / 4 ∧ (∀ v ∈ nums, v < W32) ∧
      l.map (fun (b : Nat) => Val.int b) = wordBytes nums ∧
      RecFieldsHolds plan.recFields nums fvs ∧
      (ctx.contract.preVals ctx.defs s0 →
        findDef ctx.defs plan.g = some d ∧ d.params.length = plan.keys.length ∧
        Value ctx.defs (d.params.zip (plan.keys.map (Key.val ctx s0 ρ plan.terms))) d.body (.record fvs)) := by
  obtain ⟨f2, as2, d2, rv, nums, ha2, hd2, hlen2, hev_g, hev_body, hlt, hlb⟩ := bytes_of_let_call hown hglen hval
  rw [hfd] at hd2; injection hd2 with hd2; subst hd2
  obtain ⟨hl4, _⟩ := wordBytes_get nums l hlb
  obtain ⟨fvals, rfl, hfvlen⟩ := returnsRecord_sound ctx.defs (plan.recFields.map RecField.name) f2 _ d.body rv hrr hev_g
  let fvs := (plan.recFields.map RecField.name).zip fvals
  have hmapfst : fvs.map Prod.fst = plan.recFields.map RecField.name := by
    simp [fvs, List.map_fst_zip (by omega : (plan.recFields.map RecField.name).length ≤ fvals.length)]
  have hlook : ∀ p ∈ fvs, fvs.lookup p.1 = some p.2 :=
    lookup_of_allDistinct fvs (by rw [hmapfst]; exact hdist)
  have hrf : RecFieldsHolds plan.recFields nums fvs :=
    parseRecBody_lookup hpb hev_body hlt hmapfst hdist hlook
  refine ⟨nums, fvs, by omega, hlt, hlb, hrf, fun hpv => ?_⟩
  obtain ⟨B, hB⟩ := held_bound HT hpv
  obtain ⟨as, eas, das⟩ := wevalList_sound (ev' := evalSpec ctx.defs (WFUEL + B) (c.envW s1))
    (fun e' v' hv' => weval_sound HT wfT hpv hB WFUEL env _ e' v' hv' henv) args vs hwl
  have ekeys : as = plan.keys.map (Key.val ctx s0 ρ plan.terms) := flatKeys_den wfT das hfk
  have same : as2 = as := by
    have a1 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.envW s1))
      (fun a v hh => evalSpec_mono ctx.defs f2 hh _ (Nat.le_max_left _ _)) args ha2
    have a2 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.envW s1))
      (fun a v hh => evalSpec_mono ctx.defs (WFUEL + B) hh _ (Nat.le_max_right _ _)) args eas
    rw [a1] at a2; injection a2
  subst same
  exact ⟨hfd, hdl, f2, by rw [← ekeys]; exact hev_g⟩

/-- **A call, by contract, of a function that writes a run of words for its caller.** If the verifier has
gone through such a call, then of the machine at the call: the address to come back to can be written; the
state the called function starts in is one its contract's caller has seen to; what the called function may
touch, this function may touch; and of every state the contract lets it return in, what the verifier holds
after the call is so, at the next instruction. -/
theorem symCallW'_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallW' ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) (i : Instr) (F : Fits ctx st i c) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hex : CallExtra ctx s0 st c (afterCall p q i st)) :
    c.slot ≤ st.reg RSP ∧ allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  cases hsp : s.sp with
  | none => simp only [symCallW', hsp] at h; exact (refuse_ok h).elim
  | some sp =>
    simp only [symCallW', hsp] at h
    · have esp0 := ev_isConst (ρ := ρ) hsp; simp only [ev_sub, ev_var] at esp0
      have h10 := H.reg RSP ctx.rsp_lt; have h20 := H.entry RSP ctx.rsp_lt
      have hg : sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot - (c.stackAt (afterCall p q i st) : Int) := by
        have := hex.stack; omega
      cases hplan : callW ctx s c with
      | error what => simp only [hplan] at h; exact (refuse_ok h).elim
      | ok plan =>
        simp only [hplan] at h
        obtain ⟨⟨u, items1⟩, r1, hbounds, h⟩ := V.bind_ok h
        obtain ⟨⟨u2, items2⟩, r2, hvaOk, h⟩ := V.bind_ok h
        have hfin := V.pure_ok h
        injection hfin with hs' _
        subst hs'
        obtain ⟨run, r, n, e, ids, env, args, vs, d, houts, hinouts, hens, erun, epart, hcr, hce, hpenv, hown, hglen, hT, hwl, hfd, hfk,
          hkeys, hdl, hwords, hshape⟩ := callWby_spec (find := callRun ctx s) hplan
        obtain ⟨xw, b, n0, how, hio, n4, hfit, hreg_r, hnow, hwi⟩ := callRun_spec hcr
        -- the machine at the call
        have esp := ev_isConst (ρ := ρ) hsp
        simp only [ev_sub, ev_var] at esp
        have h1 := H.reg RSP ctx.rsp_lt
        have h2 := H.entry RSP ctx.rsp_lt
        have hrsp : (st.reg RSP : Int) = s0.reg RSP + sp := by omega
        have hstack := E.stackAt
        have habove := E.above
        have hsmallsp := H.small RSP
        have hslot := F.slot
        have h8 : c.slot ≤ st.reg RSP := by omega
        have s1rsp : (afterCall p q i st).reg RSP = st.reg RSP - c.slot := afterCall_rsp F.link
        have s1reg : ∀ r, CallKeeps r → (afterCall p q i st).reg r = st.reg r := fun r hr => afterCall_reg F.link hr
        have s1mem : ∀ x, x < st.reg RSP - c.slot ∨ st.reg RSP ≤ x → (afterCall p q i st).mem x = st.mem x :=
          fun x hx => afterCall_mem F.link h8 hx
        -- the run handed over to be read and written: whole words of one of this function's
        have hwm := List.mem_of_getElem? how
        have hout := E.outAt hwm
        have rmem : (run, r, n) ∈ c.outs := by rw [houts]; exact List.mem_cons_self ..
        have rarg : r ∈ c.argRegs := outsIn_mem c.args c.argRegs run r n rmem
        obtain ⟨r16, rne⟩ := F.arg rarg
        have b16 := outs_lt hwm
        have hrb : st.reg r = s0.reg b + 4 * plan.first := by
          have := H.reg r r16
          rw [hreg_r ρ, H.entry b b16] at this
          omega
        have s1r : (afterCall p q i st).reg r = s0.reg b + 4 * plan.first := by rw [s1reg r rne, hrb]
        -- runs of bytes handed over to be read
        have hspan : ∀ r' l' b' off nn, r' ∈ c.argRegs → l' ∈ c.argRegs → regionPart ctx s r' l' = some (b', off, nn) →
            0 ≤ ev ρ off ∧ (ev ρ nn).toNat = (afterCall p q i st).reg l' ∧ 0 ≤ ev ρ nn ∧
            ∀ k, k < (afterCall p q i st).reg l' →
              (afterCall p q i st).mem ((afterCall p q i st).reg r' + k) = s0.mem (s0.reg b' + (ev ρ off).toNat + k) := by
          intro r' l' b' off nn ra la hp
          obtain ⟨lb, g1, g2, g3, g4, g5⟩ := regionPart_sound E H (F.arg ra).1 (F.arg la).1 hp
          have hlen := H.reg l' (F.arg la).1
          have er := s1reg r' (F.arg ra).2
          have el := s1reg l' (F.arg la).2
          have hregn := E.regionAt g1
          subst g2
          refine ⟨g3, by rw [el, ← hlen]; omega, by rw [← hlen]; omega, fun k hk => ?_⟩
          rw [el] at hk
          have ea : st.reg r' = s0.reg b' + (ev ρ off).toNat := by omega
          rw [er, ea, s1mem _ (by omega)]
          exact H.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (E.region_notOut g1 (by omega) (by omega))
        have hregpart : ∀ r' l', (r', l') ∈ c.regions → ∃ b' off nn lb, regionPart ctx s r' l' = some (b', off, nn) ∧ r' ∈ c.argRegs ∧ l' ∈ c.argRegs ∧
            (b', lb) ∈ ctx.contract.regions ∧ 0 ≤ ev ρ off ∧ (st.reg r' : Int) = s0.reg b' + ev ρ off ∧ ev ρ off + st.reg l' ≤ s0.reg lb := by
          intro r' l' m
          obtain ⟨b', off, nn, hp⟩ := calleeW_regions c c.args c.argRegs hce r' l' m
          obtain ⟨ra, len, hlen⟩ := regionsIn_mem c c.args c.argRegs r' l' m
          have la := regOfIn_mem len c.args c.argRegs l' hlen
          obtain ⟨lb, g1, _, g3, g4, g5⟩ := regionPart_sound E H (F.arg ra).1 (F.arg la).1 hp
          exact ⟨b', off, nn, lb, hp, ra, la, g1, g3, g4, g5⟩
        -- the table with the words of the parts handed over
        obtain ⟨extT, okT⟩ := inputs_table wf (partNodes ctx s c.args c.argRegs) (partNodes_inputs c.args c.argRegs)
        rw [← hT] at extT okT
        have CT := Carried.terms H wf extT okT
        have HT := CT.holds
        have wfT := CT.wf
        -- each part handed over to be read lies in one of this function's runs given to read
        have hpart : ∀ x' r' n', (x', r', n') ∈ c.fixeds → r' ∈ c.argRegs ∧
            ((∃ j b' cst, fixedPart ctx s r' n' = some (j, b', cst)) ∨ ∃ cf fids, frameRun s r' n' = some (cf, fids)) := by
          intro x' r' n' m
          exact ⟨fixedsIn_mem c.args c.argRegs x' r' n' m, calleeW_fixeds c.args c.argRegs hce x' r' n' m⟩
        have hfixmem : ∀ r' n' j b' cst, r' ∈ c.argRegs → fixedPart ctx s r' n' = some (j, b', cst) →
            ∀ k, k < n' → (afterCall p q i st).mem (st.reg r' + k) = s0.mem (s0.reg b' + cst + k) ∧ (s0.mem (s0.reg b' + cst + k)).val < 256 := by
          intro r' n' j b' cst ra hf k hk
          obtain ⟨g3, -, f1, f2, f3, f4, -⟩ := fixedPart_sound E H (F.arg ra).1 hf
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
        have hframe : ∀ r' n' cf fids, r' ∈ c.argRegs → frameRun s r' n' = some (cf, fids) →
            (afterCall p q i st).reg r' = ((s0.reg RSP : Int) + cf).toNat ∧ sp ≤ cf ∧ cf + n' ≤ 0 ∧
            (List.range n').map (fun k => Val.int ((afterCall p q i st).mem ((afterCall p q i st).reg r' + k))) =
              wordBytes (fids.map (den (inpOf ctx s0) ρ plan.terms)) := by
          intro r' n' cf fids ra hfr
          obtain ⟨⟨sp', hsp', hle⟩, hn0, hn8, hreg', hlen, hwords⟩ := frameRun_sound E H wf (F.arg ra).1 hfr
          have esp' : sp' = sp := Option.some.inj (hsp'.symm.trans hsp)
          subst esp'
          have hA : (afterCall p q i st).reg r' = ((s0.reg RSP : Int) + cf).toNat := by
            rw [s1reg r' (F.arg ra).2]; omega
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
          exact calleeW_sound H c F.regs (fun r' m => s1reg r' (F.arg m).2) hfixmem
            (fun r' n' cf fids ra hfr => (hframe r' n' cf fids ra hfr).2.2.2) hspan c.args c.argRegs (fun _ m => m)
            (fun x' r' n' m => by
              have m' : (x', r', n') ∈ c.inouts := m
              rw [hinouts] at m'
              simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m'
              obtain ⟨_, e1, e2⟩ := m'
              subst r' n'
              exact hiobytes) hce
        have henv_bd := calleeW_bounded wf F.regs c.args c.argRegs (fun _ m => m) hce
        obtain ⟨hva_pre, hva_read, hva_vals⟩ := callValArraysOk_sound E (hpenv ▸ hvaOk) HT wfT F henv henv_bd hrsp hg
          (fun x0 r0 l0 ch0 el0 mva0 x' r' n' mo => by
            rw [houts] at mo; simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at mo
            obtain ⟨_, rfl, rfl⟩ := mo
            have := (E.valArray mva0).2.2 xw b n0 hwm
            rw [s1r]; omega)
          (fun cf nbytes hsp_cf hcf_end _ x' r' n' mo => by
            rw [houts] at mo; simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at mo
            obtain ⟨_, rfl, rfl⟩ := mo
            rw [s1r]; have := hout.2; omega)
        have hpre : c.pre q (afterCall p q i st) := by
          refine ⟨afterCall_rip p q i st, ?_, ?_, ?_, hq, ?_, ?_, ?_, ?_, ?_, hex.mbounds,
            (fun j x r count l m => by rw [tableAt_none hl] at m; cases m), hex.atLeast, afterCall_aligned F p q, hex.preLines, hva_pre, hex.aligns, hex.lineDisjoint⟩
          · exact afterCall_small F.link H.small
          · rw [s1rsp]; omega
          · rw [s1rsp]; omega
          · intro r' l' m
            obtain ⟨b', off, nn, lb, _, ra, la, g1, g3, g4, g5⟩ := hregpart r' l' m
            have hregn := E.regionAt g1
            rw [s1reg r' (F.arg ra).2, s1reg l' (F.arg la).2, s1rsp]
            refine ⟨by omega, by omega⟩
          · intro x' r' n' m
            rw [houts] at m
            simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m
            obtain ⟨_, e1, e2⟩ := m
            subst r' n'
            refine ⟨by rw [s1r]; have := hout.1; omega, by rw [s1r, s1rsp]; have := hout.2; omega, ?_⟩
            intro r'' l'' m'
            obtain ⟨b', off, nn, lb, _, ra, la, g1, g3, g4, g5⟩ := hregpart r'' l'' m'
            have hap := E.outRegion hwm g1
            rw [s1r, s1reg r'' (F.arg ra).2, s1reg l'' (F.arg la).2]; omega
          · rw [houts]; exact List.pairwise_singleton _ _
          · intro x' r' n' m
            obtain ⟨ra, hf | hf⟩ := hpart x' r' n' m
            · obtain ⟨j, b', cst, hf⟩ := hf
              obtain ⟨g3, -, f1, f2, f3, f4, -⟩ := fixedPart_sound E H (F.arg ra).1 hf
              have rne' := (F.arg ra).2
              refine ⟨by rw [s1reg r' rne', g3]; omega, by rw [s1reg r' rne', g3, s1rsp]; omega, ?_⟩
              intro x'' r'' n'' m''
              rw [houts] at m''
              simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
              obtain ⟨_, e1, e2⟩ := m''
              subst r'' n''
              have := f4 xw b n0 hwm
              rw [s1reg r' rne', g3, s1r]
              omega
            · obtain ⟨cf, fids, hfr⟩ := hf
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
            have ra := regOfIn_mem x' c.args c.argRegs r' hr'
            have hreg' := H.reg r' (F.arg ra).1
            rw [s1reg r' (F.arg ra).2]
            omega
        have hread : ∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true := by
          intro a ha
          rw [perm_read_split, Bool.or_eq_true] at ha
          refine ha.elim (fun ha => ?_) (fun ha => read_pieces H p q i ha)
          simp only [Contract.perm, inLane_false hl, inPieces_nil, Bool.or_false, Bool.or_eq_true] at ha
          rcases ha with ha | ha
          · simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
            left; left; left
            rcases ha with ((ha | ha) | ha) | ha
            · left; left; left; omega
            · left; left; left; omega
            · obtain ⟨⟨r', l'⟩, m, hin⟩ := List.any_eq_true.mp ha
              obtain ⟨b', off, nn, lb, _, ra, la, g1, g3, g4, g5⟩ := hregpart r' l' m
              simp only [Bool.and_eq_true, decide_eq_true_eq, s1reg r' (F.arg ra).2, s1reg l' (F.arg la).2] at hin
              left; right
              exact List.any_eq_true.mpr ⟨(b', lb), g1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
            · simp only [Contract.inFixed, Bool.or_eq_true] at ha ⊢
              rcases ha with ha | ha
              · obtain ⟨⟨x', r', n'⟩, m, hin⟩ := List.any_eq_true.mp ha
                obtain ⟨ra, hf | hf⟩ := hpart x' r' n' m
                · obtain ⟨j, b', cst, hf⟩ := hf
                  obtain ⟨g3, -, -, -, -, -, fw⟩ := fixedPart_sound E H (F.arg ra).1 hf
                  simp only [Bool.and_eq_true, decide_eq_true_eq, s1reg r' (F.arg ra).2, g3] at hin
                  rcases fw with ⟨x0, n0, hm0, hle⟩ | ⟨l0, hm0, hle⟩
                  · right; left
                    exact List.any_eq_true.mpr ⟨(x0, b', n0), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
                  · left; right
                    exact List.any_eq_true.mpr ⟨(b', l0), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
                · obtain ⟨cf, fids, hfr⟩ := hf
                  obtain ⟨hA, hle, hn0, -⟩ := hframe r' n' cf fids ra hfr
                  simp only [Bool.and_eq_true, decide_eq_true_eq, hA] at hin
                  left; left; left
                  omega
              · right; right
                rw [hinouts] at ha
                simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
                exact List.any_eq_true.mpr ⟨(xw, b, n0), hio, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
          · exact hva_read a ha
        have hwrite : ∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true := by
          intro a ha
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          rcases ha with ha | ha
          · left; omega
          · right
            simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
            unfold Contract.inOut
            exact List.any_eq_true.mpr ⟨(xw, b, n0), hwm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        have hwr : allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true := by
          apply allowed_of
          intro x hx1 hx2
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          left; omega
        refine ⟨h8, hwr, hpre, hread, hwrite, ?_⟩
        intro s2 post hdata2
        obtain ⟨prip, prsp, psaved, pmem, pret, psmall, hpost_ens, pvec⟩ := post
        have hvec2 : ∀ r ∈ c.keepsVec, s2.vec r = st.vec r := fun r hr =>
          (pvec r hr).trans (congrFun (afterCall_vec p q i st) r)
        have hrip : s2.rip = p.base + i.next := by
          rw [prip]
          exact afterCall_back F.link hret h8
        have hkeep : ∀ r, r < ctx.nreg → c.scratch.contains r = false → s2.reg r = st.reg r := by
          intro r' hr hc
          by_cases h4 : r' = RSP
          · rw [h4, prsp, s1rsp]; omega
          · have hmemr : r' ∈ c.keeps := kept_of_not_scratch (F.regs ▸ hr) h4 hc
            rw [psaved r' hmemr, s1reg r' (callKeeps h4 (keeps_spec hmemr).2.2)]
        have hmem2 : ∀ a, a + c.slot + c.stackAt (afterCall p q i st) < st.reg RSP ∨ st.reg RSP ≤ a →
            a < s0.reg b + 4 * plan.first ∨ s0.reg b + 4 * (plan.first + n / 4) ≤ a → s2.mem a = st.mem a := by
          intro a ha hb
          rw [pmem a (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1rsp]; omega)
            (by simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1r]; omega)]
          exact s1mem a (by omega)
        rcases hshape with ⟨hnoRec, hveq⟩ | ⟨x, body, hne, hcva, hveq, hpb, hsum, hdist, hrr⟩
        · let nums := (List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4
          have hnums : nums.length = n / 4 := by simp [nums]
          have hlt : ∀ v ∈ nums, v < W32 := by
            intro v mv; obtain ⟨k, _, rfl⟩ := List.mem_map.mp mv; exact load_lt s2.mem _ 4
          have hrun : ∀ k, k < n / 4 → ∀ bb, bb < 4 → s2.mem (s0.reg b + 4 * (plan.first + k) + bb) = nums.getD k 0 / 256 ^ bb % 256 := by
            intro k hk bb hbb
            have hget : nums.getD k 0 = load s2.mem (s0.reg b + 4 * (plan.first + k)) 4 := by
              rw [getD_of_lt nums 0 (by simpa [nums] using hk)]; simp [nums]
            rw [hget]; exact (load4_byteAt s2.mem _ bb hbb (fun _ _ => Fin.isLt _)).symm
          have hheld : (plan.recFields = [] ∧ (ctx.contract.preVals ctx.defs s0 → ∃ d', findDef ctx.defs plan.g = some d' ∧ d'.params.length = plan.keys.length ∧
              Value ctx.defs (d'.params.zip (plan.keys.map (Key.val ctx s0 ρ plan.terms))) d'.body (if false then .list (wordBytes nums) else .list (nums.map Val.word)))) ∨
              (!plan.recFields.isEmpty ∧ ∃ d' fvs, none = some (Val.record fvs) ∧ RecFieldsHolds plan.recFields nums fvs ∧
                (ctx.contract.preVals ctx.defs s0 → findDef ctx.defs plan.g = some d' ∧ d'.params.length = plan.keys.length ∧
                  Value ctx.defs (d'.params.zip (plan.keys.map (Key.val ctx s0 ρ plan.terms))) d'.body (Val.record fvs))) := by
            left; refine ⟨hnoRec, fun hpv => ?_⟩
            obtain ⟨r_, n_, l, hrm, hval, hll, hlm⟩ := (EnsureW.holds_whole epart).mp ((hpost_ens (hva_vals hpv)).2 e (by rw [hens]; exact List.mem_cons_self ..))
            rw [erun, houts] at hrm
            simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq, true_and] at hrm
            obtain ⟨e1, e2⟩ := hrm; cases e1.symm; cases e2.symm
            rw [hveq] at hval
            obtain ⟨nums', hnums', hlt', hlb', hv'⟩ := postW_plain HT wfT hpv henv hown hglen hwl hfd hfk hdl hll n4 hval
            have heqn : nums' = nums := by
              have := nums_eq_of_bytes n4 hnums' hlt' hlb' hll (fun k hk => by
                have := hlm k (by omega); rwa [s1r] at this)
              rw [this]; apply List.map_congr_left; intro k _
              rw [show s0.reg b + 4 * plan.first + 4 * k = s0.reg b + 4 * (plan.first + k) by omega]
            subst heqn
            exact ⟨d, hfd, hdl, hv'⟩
          have Hafter := afterCallW_holds E c (c.slot + c.stackAt (afterCall p q i st)) F.regs HT wfT hrsp (by omega) hg.1 hkeep psmall how (show 4 * (plan.first + n / 4) ≤ n0 by omega) hnow (fun a ha hb => hmem2 a (by omega) hb) hdata2
            hnums hlt hrun hkeys (bytes := false) (rfs := plan.recFields) (recVal := none) hheld hvec2
          have wafter := afterCallW_wf wfT c F.regs sp plan.w plan.first (n / 4) plan.g hkeys false plan.recFields (fun h => by simp [hnoRec] at h)
          rw [hwords]
          exact ⟨hrip, _, afterRhoW_agree c.regs s.nvars ρ s2 nums none,
            by rw [afterCallW_nvars]; show s.nvars ≤ s.nvars + c.regs + n / 4 + _; omega, Hafter, wafter⟩
        · have hcpre : c.preVals ctx.defs (afterCall p q i st) := fun _ _ _ _ _ m => by rw [hcva] at m; cases m
          obtain ⟨r_, n_, l, hrm, hval, hll, hlm⟩ := (EnsureW.holds_whole epart).mp ((hpost_ens hcpre).2 e (by rw [hens]; exact List.mem_cons_self ..))
          rw [erun, houts] at hrm
          simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq, true_and] at hrm
          obtain ⟨e1, e2⟩ := hrm; cases e1.symm; cases e2.symm
          rw [hveq] at hval
          obtain ⟨nums, fvs, hnums, hlt, hlb, hrf, hv⟩ := postW_rec HT wfT henv hown hglen hwl hfd hfk hdl hll n4 hval hpb hsum hdist hrr
          obtain ⟨hl4, hlget⟩ := wordBytes_get nums l hlb
          have hrun : ∀ k, k < n / 4 → ∀ bb, bb < 4 → s2.mem (s0.reg b + 4 * (plan.first + k) + bb) = nums.getD k 0 / 256 ^ bb % 256 := by
            intro k hk bb hbb
            have lt' : 4 * k + bb < l.length := by omega
            have := hlm (4 * k + bb) lt'
            rw [s1r, ← Nat.add_assoc] at this
            rw [show s0.reg b + 4 * (plan.first + k) + bb = s0.reg b + 4 * plan.first + 4 * k + bb by omega, this, ← getD_of_lt l 0 lt']
            exact hlget k (by omega) bb hbb
          have Hafter := afterCallW_holds E c (c.slot + c.stackAt (afterCall p q i st)) F.regs HT wfT hrsp (by omega) hg.1 hkeep psmall how (show 4 * (plan.first + n / 4) ≤ n0 by omega) hnow (fun a ha hb => hmem2 a (by omega) hb) hdata2
            hnums hlt hrun hkeys (bytes := false) (rfs := plan.recFields) (recVal := some (.record fvs)) (Or.inr ⟨hne, d, fvs, rfl, hrf, hv⟩) hvec2
          have wafter := afterCallW_wf wfT c F.regs sp plan.w plan.first (n / 4) plan.g hkeys false plan.recFields (fun _ => by omega)
          rw [hwords]
          exact ⟨hrip, _, afterRhoW_agree c.regs s.nvars ρ s2 nums (some (.record fvs)),
            by rw [afterCallW_nvars]; show s.nvars ≤ s.nvars + c.regs + n / 4 + _; omega, Hafter, wafter⟩


/-- **A call of a function that writes a part of this function's frame.** As `symCallW'_sound`: the run the
called function reads and writes is a part of the frame, at or above the stack pointer, and after the call
its words are new cells of the frame. -/
theorem symCallF'_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallF' ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) (i : Instr) (F : Fits ctx st i c) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hex : CallExtra ctx s0 st c (afterCall p q i st)) :
    c.slot ≤ st.reg RSP ∧ allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  cases hsp : s.sp with
  | none => simp only [symCallF', hsp] at h; exact (refuse_ok h).elim
  | some sp =>
    simp only [symCallF', hsp] at h
    · have esp0 := ev_isConst (ρ := ρ) hsp; simp only [ev_sub, ev_var] at esp0
      have h10 := H.reg RSP ctx.rsp_lt; have h20 := H.entry RSP ctx.rsp_lt
      have hg : sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot - (c.stackAt (afterCall p q i st) : Int) := by
        have := hex.stack; omega
      obtain ⟨run0, r, n, houts0⟩ : ∃ run0 r n, c.outs = [(run0, r, n)] := by
        rcases ho : c.outs with _ | ⟨⟨run0, r, n⟩, _ | ⟨o2, omore⟩⟩
        · simp only [ho] at h; exact (refuse_ok h).elim
        · exact ⟨_, _, _, rfl⟩
        · simp only [ho] at h; exact (refuse_ok h).elim
      simp only [houts0] at h
      cases hfa : frameAt s r with
      | none => simp only [hfa] at h; exact (refuse_ok h).elim
      | some cw =>
        simp only [hfa] at h
        split at h
        · exact (refuse_ok h).elim
        rename_i hcw
        have hcw' : sp ≤ cw ∧ cw + n ≤ 0 ∧ n % 8 = 0 := by simpa using hcw
        obtain ⟨hlew, hn0w, hn8w⟩ := hcw'
        split at h
        · exact (refuse_ok h).elim
        rename_i hapart
        have hapart : (c.fixeds.all fun x =>
            match frameAt s x.2.1 with
            | some cf => decide (cf + (x.2.2 : Int) ≤ cw) || decide (cw + (n : Int) ≤ cf)
            | none => true) = true := by
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hapart; exact hapart
        -- fill writable frame buffer [cw .. cw + n) with known or fresh terms
        have hfill := frameFill_sound (ctx := ctx) (s0 := s0) (st := st) E.stackAt cw (n / 4) 0 (by omega) H wf
        rcases hfpair : frameFill s cw (n / 4) 0 with ⟨outIds, sFill⟩
        rw [hfpair] at hfill
        simp only [hfpair] at h
        obtain ⟨ρ1, Cfill, _, hregF, _, _, _, _, hfactsF, _, _, _, _, _, _, _, _, _, hidlen, hfillw⟩ := hfill
        have H1 := Cfill.holds
        have wf1 := Cfill.wf
        have hsp1 : sFill.sp = some sp := by simp only [Sym.sp, hregF]; exact hsp
        obtain ⟨plan, hplan⟩ : ∃ plan, callWby (fun r' n' => if r' == r && n' == n then some (0, 0, outIds) else none) ctx sFill c = .ok plan := by
          cases hx : callWby (fun r' n' => if r' == r && n' == n then some (0, 0, outIds) else none) ctx sFill c with
          | error what => simp only [hx] at h; exact (refuse_ok h).elim
          | ok plan => exact ⟨plan, rfl⟩
        simp only [hplan] at h
        obtain ⟨⟨u, items1⟩, r1, hbounds, h⟩ := V.bind_ok h
        obtain ⟨⟨u2, items2⟩, r2, hvaOk, h⟩ := V.bind_ok h
        have hfin := V.pure_ok h
        injection hfin with hs' _
        subst hs'
        obtain ⟨run, r_, n_, e, ids, env, args, vs, d, houts, hinouts, hens, erun, epart, hcr, hce, hpenv, hown, hglen, hT, hwl, hfd, hfk,
          hkeys, hdl, hwords, hshape⟩ := callWby_spec hplan
        have e0 : r = r_ ∧ n = n_ := by
          rw [houts0] at houts
          injection houts with e1 _
          injection e1 with _ e2
          injection e2 with e3 e4
          exact ⟨e3, e4⟩
        obtain ⟨rfl, rfl⟩ := e0
        have eids : ids = outIds := by
          simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hcr
          exact hcr.2.2.symm
        subst eids
        -- the machine at the call
        have esp := ev_isConst (ρ := ρ1) hsp1
        simp only [ev_sub, ev_var] at esp
        have h1 := H1.reg RSP ctx.rsp_lt
        have h2 := H1.entry RSP ctx.rsp_lt
        have hrsp : (st.reg RSP : Int) = s0.reg RSP + sp := by omega
        have hstack := E.stackAt
        have habove := E.above
        have hsmallsp := H1.small RSP
        have hslot := F.slot
        have h8 : c.slot ≤ st.reg RSP := by omega
        have s1rsp : (afterCall p q i st).reg RSP = st.reg RSP - c.slot := afterCall_rsp F.link
        have s1reg : ∀ r, CallKeeps r → (afterCall p q i st).reg r = st.reg r := fun r hr => afterCall_reg F.link hr
        have s1mem : ∀ x, x < st.reg RSP - c.slot ∨ st.reg RSP ≤ x → (afterCall p q i st).mem x = st.mem x :=
          fun x hx => afterCall_mem F.link h8 hx
        -- the run handed over to be read and written: a part of this function's frame
        have rmem : (run, r, n) ∈ c.outs := by rw [houts]; exact List.mem_cons_self ..
        have rarg : r ∈ c.argRegs := outsIn_mem c.args c.argRegs run r n rmem
        obtain ⟨r16, rne⟩ := F.arg rarg
        have hregr : (st.reg r : Int) = s0.reg RSP + cw := by
          have e := ev_isConst (ρ := ρ) (show Lin.isConst (Lin.sub (s.reg r) (Lin.var RSP)) = some cw from hfa)
          rw [ev_sub, ev_var] at e
          have h1' := H.reg r r16; have h2' := H.entry RSP ctx.rsp_lt; omega
        have s1r : (afterCall p q i st).reg r = ((s0.reg RSP : Int) + cw).toNat := by rw [s1reg r rne]; omega
        -- runs of bytes handed over to be read
        have hspan : ∀ r' l' b' off nn, r' ∈ c.argRegs → l' ∈ c.argRegs → regionPart ctx sFill r' l' = some (b', off, nn) →
            0 ≤ ev ρ1 off ∧ (ev ρ1 nn).toNat = (afterCall p q i st).reg l' ∧ 0 ≤ ev ρ1 nn ∧
            ∀ k, k < (afterCall p q i st).reg l' →
              (afterCall p q i st).mem ((afterCall p q i st).reg r' + k) = s0.mem (s0.reg b' + (ev ρ1 off).toNat + k) := by
          intro r' l' b' off nn ra la hp
          obtain ⟨lb, g1, g2, g3, g4, g5⟩ := regionPart_sound E H1 (F.arg ra).1 (F.arg la).1 hp
          have hlen := H1.reg l' (F.arg la).1
          have er := s1reg r' (F.arg ra).2
          have el := s1reg l' (F.arg la).2
          have hregn := E.regionAt g1
          subst g2
          refine ⟨g3, by rw [el, ← hlen]; omega, by rw [← hlen]; omega, fun k hk => ?_⟩
          rw [el] at hk
          have ea : st.reg r' = s0.reg b' + (ev ρ1 off).toNat := by omega
          rw [er, ea, s1mem _ (by omega)]
          exact H1.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (E.region_notOut g1 (by omega) (by omega))
        have hregpart : ∀ r' l', (r', l') ∈ c.regions → ∃ b' off nn lb, regionPart ctx sFill r' l' = some (b', off, nn) ∧ r' ∈ c.argRegs ∧ l' ∈ c.argRegs ∧
            (b', lb) ∈ ctx.contract.regions ∧ 0 ≤ ev ρ1 off ∧ (st.reg r' : Int) = s0.reg b' + ev ρ1 off ∧ ev ρ1 off + st.reg l' ≤ s0.reg lb := by
          intro r' l' m
          obtain ⟨b', off, nn, hp⟩ := calleeW_regions c c.args c.argRegs hce r' l' m
          obtain ⟨ra, len, hlen⟩ := regionsIn_mem c c.args c.argRegs r' l' m
          have la := regOfIn_mem len c.args c.argRegs l' hlen
          obtain ⟨lb, g1, _, g3, g4, g5⟩ := regionPart_sound E H1 (F.arg ra).1 (F.arg la).1 hp
          exact ⟨b', off, nn, lb, hp, ra, la, g1, g3, g4, g5⟩
        -- the table with the words of the parts handed over
        obtain ⟨extT, okT⟩ := inputs_table wf1 (partNodes ctx sFill c.args c.argRegs) (partNodes_inputs c.args c.argRegs)
        rw [← hT] at extT okT
        have CT := Carried.terms H1 wf1 extT okT
        have HT := CT.holds
        have wfT := CT.wf
        have hpart : ∀ x' r' n', (x', r', n') ∈ c.fixeds → r' ∈ c.argRegs ∧
            ((∃ j b' cst, fixedPart ctx sFill r' n' = some (j, b', cst)) ∨ ∃ cf fids, frameRun sFill r' n' = some (cf, fids)) := by
          intro x' r' n' m
          exact ⟨fixedsIn_mem c.args c.argRegs x' r' n' m, calleeW_fixeds c.args c.argRegs hce x' r' n' m⟩
        have hfixmem : ∀ r' n' j b' cst, r' ∈ c.argRegs → fixedPart ctx sFill r' n' = some (j, b', cst) →
            ∀ k, k < n' → (afterCall p q i st).mem (st.reg r' + k) = s0.mem (s0.reg b' + cst + k) ∧ (s0.mem (s0.reg b' + cst + k)).val < 256 := by
          intro r' n' j b' cst ra hf k hk
          obtain ⟨g3, -, f1, f2, f3, f4, -⟩ := fixedPart_sound E H1 (F.arg ra).1 hf
          refine ⟨?_, f3 k hk⟩
          rw [g3, s1mem _ (by omega)]
          exact H1.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (by
              unfold Contract.inOut
              rw [List.any_eq_false]
              intro ⟨x'', r'', n''⟩ hm
              have := f4 x'' r'' n'' hm
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              omega)
        have hframe : ∀ r' n' cf fids, r' ∈ c.argRegs → frameRun sFill r' n' = some (cf, fids) →
            (afterCall p q i st).reg r' = ((s0.reg RSP : Int) + cf).toNat ∧ sp ≤ cf ∧ cf + n' ≤ 0 ∧
            (List.range n').map (fun k => Val.int ((afterCall p q i st).mem ((afterCall p q i st).reg r' + k))) =
              wordBytes (fids.map (den (inpOf ctx s0) ρ1 plan.terms)) := by
          intro r' n' cf fids ra hfr
          obtain ⟨⟨sp', hsp', hle⟩, hn0, hn8, hreg', hlen, hwords⟩ := frameRun_sound E H1 wf1 (F.arg ra).1 hfr
          have esp' : sp' = sp := Option.some.inj (hsp'.symm.trans hsp1)
          subst esp'
          have hA : (afterCall p q i st).reg r' = ((s0.reg RSP : Int) + cf).toNat := by
            rw [s1reg r' (F.arg ra).2]; omega
          refine ⟨hA, hle, hn0, ?_⟩
          have := wordBytes_range (afterCall p q i st).mem (fids.map (den (inpOf ctx s0) ρ1 plan.terms)) ((afterCall p q i st).reg r')
            (fun j hj bb hbb => by
              have hj' : j < fids.length := by simpa using hj
              obtain ⟨hlt, hlow, hld⟩ := hwords j (by omega)
              have hb : (st.mem (((s0.reg RSP : Int) + cf).toNat + 4 * j + bb)).val =
                  den (inpOf ctx s0) ρ1 plan.terms (fids.getD j 0) / 256 ^ bb % 256 := by
                rw [den_ext wf1.words.table extT hlt, ← hld]
                exact (load4_byteAt st.mem _ bb hbb (fun _ _ => Fin.isLt _)).symm
              rw [hA, s1mem _ (by omega), hb, getD_of_lt _ _ hj, getD_of_lt _ _ hj', List.getElem_map])
          rw [List.length_map, hlen, show 4 * (n' / 4) = n' by omega] at this
          exact this
        have hiobytes : (List.range n).map (fun k => Val.int ((afterCall p q i st).mem ((afterCall p q i st).reg r + k))) =
            wordBytes (ids.map (den (inpOf ctx s0) ρ1 plan.terms)) := by
          have := wordBytes_range (afterCall p q i st).mem (ids.map (den (inpOf ctx s0) ρ1 plan.terms)) ((afterCall p q i st).reg r)
            (fun j hj bb hbb => by
              have hj' : j < ids.length := by simpa using hj
              obtain ⟨hlt, hld⟩ := hfillw j (by omega)
              simp only [Nat.zero_add] at hld
              have ea : ((s0.reg RSP : Int) + (cw + 4 * (j : Int))).toNat = ((s0.reg RSP : Int) + cw).toNat + 4 * j := by omega
              rw [ea] at hld
              have hb : (st.mem (((s0.reg RSP : Int) + cw).toNat + 4 * j + bb)).val =
                  den (inpOf ctx s0) ρ1 plan.terms (ids.getD j 0) / 256 ^ bb % 256 := by
                rw [den_ext wf1.words.table extT hlt, ← hld]
                exact (load4_byteAt st.mem _ bb hbb (fun _ _ => Fin.isLt _)).symm
              rw [s1r, s1mem _ (by omega), hb, getD_of_lt _ _ hj, getD_of_lt _ _ hj', List.getElem_map])
          rw [List.length_map, hidlen, show 4 * (n / 4) = n by omega] at this
          exact this
        have henv : EnvDen ctx s0 ρ1 plan.terms env (c.envW (afterCall p q i st)) := by
          rw [envW_plain hl]
          exact calleeW_sound H1 c F.regs (fun r' m => s1reg r' (F.arg m).2) hfixmem
            (fun r' n' cf fids ra hfr => (hframe r' n' cf fids ra hfr).2.2.2) hspan c.args c.argRegs (fun _ m => m)
            (fun x' r' n' m => by
              have m' : (x', r', n') ∈ c.inouts := m
              rw [hinouts] at m'
              simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m'
              obtain ⟨_, e1, e2⟩ := m'
              subst r' n'
              exact hiobytes) hce
        have henv_bd := calleeW_bounded wf1 F.regs c.args c.argRegs (fun _ m => m) hce
        obtain ⟨hva_pre, hva_read, hva_vals⟩ := callValArraysOk_sound E (hpenv ▸ hvaOk) HT wfT F henv henv_bd hrsp hg
          (fun x0 r0 l0 ch0 el0 mva0 x' r' n' mo => by
            rw [houts] at mo; simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at mo
            obtain ⟨_, rfl, rfl⟩ := mo
            have := (E.valArray mva0).2.1
            rw [s1r]; omega)
          (fun cf nbytes hsp_cf hcf_end hdisj x' r' n' mo => by
            rw [houts] at mo; simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at mo
            obtain ⟨_, rfl, rfl⟩ := mo
            have := hdisj _ _ rfl
            rw [s1r]; omega)
        have hpre : c.pre q (afterCall p q i st) := by
          refine ⟨afterCall_rip p q i st, ?_, ?_, ?_, hq, ?_, ?_, ?_, ?_, ?_, hex.mbounds,
            (fun j x r count l m => by rw [tableAt_none hl] at m; cases m), hex.atLeast, afterCall_aligned F p q, hex.preLines, hva_pre, hex.aligns, hex.lineDisjoint⟩
          · exact afterCall_small F.link H1.small
          · rw [s1rsp]; omega
          · rw [s1rsp]; omega
          · intro r' l' m
            obtain ⟨b', off, nn, lb, _, ra, la, g1, g3, g4, g5⟩ := hregpart r' l' m
            have hregn := E.regionAt g1
            rw [s1reg r' (F.arg ra).2, s1reg l' (F.arg la).2, s1rsp]
            refine ⟨by omega, by omega⟩
          · intro x' r' n' m
            rw [houts] at m
            simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m
            obtain ⟨_, e1, e2⟩ := m
            subst r' n'
            refine ⟨by rw [s1r]; omega, by rw [s1r, s1rsp]; omega, ?_⟩
            intro r'' l'' m'
            obtain ⟨b', off, nn, lb, _, ra, la, g1, g3, g4, g5⟩ := hregpart r'' l'' m'
            have hregn := E.regionAt g1
            rw [s1r, s1reg r'' (F.arg ra).2, s1reg l'' (F.arg la).2]; omega
          · rw [houts]; exact List.pairwise_singleton _ _
          · intro x' r' n' m
            obtain ⟨ra, hf | hf⟩ := hpart x' r' n' m
            · obtain ⟨j, b', cst, hf⟩ := hf
              obtain ⟨g3, -, f1, f2, f3, f4, -⟩ := fixedPart_sound E H1 (F.arg ra).1 hf
              have rne' := (F.arg ra).2
              refine ⟨by rw [s1reg r' rne', g3]; omega, by rw [s1reg r' rne', g3, s1rsp]; omega, ?_⟩
              intro x'' r'' n'' m''
              rw [houts] at m''
              simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
              obtain ⟨_, e1, e2⟩ := m''
              subst r'' n''
              rw [s1reg r' rne', g3, s1r]
              omega
            · obtain ⟨cf, fids, hfr⟩ := hf
              obtain ⟨hA, hle, hn0, -⟩ := hframe r' n' cf fids ra hfr
              refine ⟨by rw [hA]; omega, by rw [hA, s1rsp]; omega, ?_⟩
              intro x'' r'' n'' m''
              rw [houts] at m''
              simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
              obtain ⟨_, e1, e2⟩ := m''
              subst r'' n''
              have hdis := List.all_eq_true.mp hapart (x', r', n') m
              have hfa' : frameAt s r' = some cf := by
                have := frameRun_at hfr; unfold frameAt at this ⊢; rwa [hregF] at this
              simp only [hfa', Bool.or_eq_true, decide_eq_true_eq] at hdis
              rw [hA, s1r]
              omega
          · intro x' bd m r' hr'
            obtain ⟨items', res, he⟩ := each_mem hbounds (x', bd) m
            simp only [hr'] at he
            have hge := entail_sound he ρ1 H1.facts
            rw [ev_sub, ev_const] at hge
            have ra := regOfIn_mem x' c.args c.argRegs r' hr'
            have hreg' := H1.reg r' (F.arg ra).1
            rw [s1reg r' (F.arg ra).2]
            omega
        have hread : ∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true := by
          intro a ha
          rw [perm_read_split, Bool.or_eq_true] at ha
          refine ha.elim (fun ha => ?_) (fun ha => read_pieces H1 p q i ha)
          simp only [Contract.perm, inLane_false hl, inPieces_nil, Bool.or_false, Bool.or_eq_true] at ha
          rcases ha with ha | ha
          · simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
            left; left; left
            rcases ha with ((ha | ha) | ha) | ha
            · left; left; left; omega
            · left; left; left; omega
            · obtain ⟨⟨r', l'⟩, m, hin⟩ := List.any_eq_true.mp ha
              obtain ⟨b', off, nn, lb, _, ra, la, g1, g3, g4, g5⟩ := hregpart r' l' m
              simp only [Bool.and_eq_true, decide_eq_true_eq, s1reg r' (F.arg ra).2, s1reg l' (F.arg la).2] at hin
              left; right
              exact List.any_eq_true.mpr ⟨(b', lb), g1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
            · simp only [Contract.inFixed, Bool.or_eq_true] at ha ⊢
              rcases ha with ha | ha
              · obtain ⟨⟨x', r', n'⟩, m, hin⟩ := List.any_eq_true.mp ha
                obtain ⟨ra, hf | hf⟩ := hpart x' r' n' m
                · obtain ⟨j, b', cst, hf⟩ := hf
                  obtain ⟨g3, -, -, -, -, -, fw⟩ := fixedPart_sound E H1 (F.arg ra).1 hf
                  simp only [Bool.and_eq_true, decide_eq_true_eq, s1reg r' (F.arg ra).2, g3] at hin
                  rcases fw with ⟨x0, n0, hm0, hle⟩ | ⟨l0, hm0, hle⟩
                  · right; left
                    exact List.any_eq_true.mpr ⟨(x0, b', n0), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
                  · left; right
                    exact List.any_eq_true.mpr ⟨(b', l0), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
                · obtain ⟨cf, fids, hfr⟩ := hf
                  obtain ⟨hA, hle, hn0, -⟩ := hframe r' n' cf fids ra hfr
                  simp only [Bool.and_eq_true, decide_eq_true_eq, hA] at hin
                  left; left; left
                  omega
              · rw [hinouts] at ha
                simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
                left; left; left
                omega
          · exact hva_read a ha
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
        obtain ⟨prip, prsp, psaved, pmem, pret, psmall, hpost_ens, pvec⟩ := post
        have hvec2 : ∀ r ∈ c.keepsVec, s2.vec r = st.vec r := fun r hr =>
          (pvec r hr).trans (congrFun (afterCall_vec p q i st) r)
        have hrip : s2.rip = p.base + i.next := by
          rw [prip]
          exact afterCall_back F.link hret h8
        have hkeep : ∀ r, r < ctx.nreg → c.scratch.contains r = false → s2.reg r = st.reg r := by
          intro r' hr hc
          by_cases h4 : r' = RSP
          · rw [h4, prsp, s1rsp]; omega
          · have hmemr : r' ∈ c.keeps := kept_of_not_scratch (F.regs ▸ hr) h4 hc
            rw [psaved r' hmemr, s1reg r' (callKeeps h4 (keeps_spec hmemr).2.2)]
        have hmem2 : ∀ a : Nat, a + c.slot + c.stackAt (afterCall p q i st) < st.reg RSP ∨ st.reg RSP ≤ a →
            (a : Int) < s0.reg RSP + cw ∨ (s0.reg RSP : Int) + cw + 4 * ((n / 4 : Nat) : Int) ≤ a → s2.mem a = st.mem a := by
          intro a ha hb
          rw [pmem a (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1rsp]; omega)
            (by simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1r]; omega)]
          exact s1mem a (by omega)
        rcases hshape with ⟨hnoRec, hveq⟩ | ⟨x, body, hne, hcva, hveq, hpb, hsum, hdist, hrr⟩
        · let nums := (List.range (n / 4)).map fun k => load s2.mem (((s0.reg RSP : Int) + cw).toNat + 4 * k) 4
          have hnums : nums.length = n / 4 := by simp [nums]
          have hlt : ∀ v ∈ nums, v < W32 := by
            intro v mv; obtain ⟨k, _, rfl⟩ := List.mem_map.mp mv; exact load_lt s2.mem _ 4
          have hrun : ∀ k, k < n / 4 → load s2.mem (((s0.reg RSP : Int) + cw).toNat + 4 * k) 4 = nums.getD k 0 := by
            intro k hk; rw [getD_of_lt nums 0 (by simpa [nums] using hk)]; simp [nums]
          have hheld : (plan.recFields = [] ∧ (ctx.contract.preVals ctx.defs s0 → ∃ d', findDef ctx.defs plan.g = some d' ∧ d'.params.length = plan.keys.length ∧
              Value ctx.defs (d'.params.zip (plan.keys.map (Key.val ctx s0 ρ1 plan.terms))) d'.body (.list (nums.map Val.word)))) ∨
              (!plan.recFields.isEmpty ∧ ∃ d' fvs, none = some (Val.record fvs) ∧ RecFieldsHolds plan.recFields nums fvs ∧
                (ctx.contract.preVals ctx.defs s0 → findDef ctx.defs plan.g = some d' ∧ d'.params.length = plan.keys.length ∧
                  Value ctx.defs (d'.params.zip (plan.keys.map (Key.val ctx s0 ρ1 plan.terms))) d'.body (Val.record fvs))) := by
            left; refine ⟨hnoRec, fun hpv => ?_⟩
            obtain ⟨r_, n_, l, hrm, hval, hll, hlm⟩ := (EnsureW.holds_whole epart).mp ((hpost_ens (hva_vals hpv)).2 e (by rw [hens]; exact List.mem_cons_self ..))
            rw [erun, houts] at hrm
            simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq, true_and] at hrm
            obtain ⟨e1, e2⟩ := hrm; cases e1.symm; cases e2.symm
            rw [hveq] at hval
            obtain ⟨nums', hnums', hlt', hlb', hv'⟩ := postW_plain HT wfT hpv henv hown hglen hwl hfd hfk hdl hll (by omega) hval
            have heqn : nums' = nums := nums_eq_of_bytes (by omega) hnums' hlt' hlb' hll (fun k hk => by
              have := hlm k (by omega); rwa [s1r] at this)
            subst heqn
            exact ⟨d, hfd, hdl, hv'⟩
          have Hafter := afterCallF_holds E c (c.stackAt (afterCall p q i st)) F.regs HT wfT hrsp hg.2 hg.1 hkeep psmall hlew (show cw + 4 * ((n / 4 : Nat) : Int) ≤ 0 by omega) hmem2 hdata2
            hnums hlt hrun hkeys (rfs := plan.recFields) (recVal := none) hheld hvec2
          have wafter := afterCallF_wf wfT c F.regs sp cw (n / 4) plan.g hkeys plan.recFields (fun h => by simp [hnoRec] at h)
          rw [hwords]
          have Cafter : Carried ctx s0 ρ1 sFill (afterRhoW c.regs sFill.nvars ρ1 s2 nums none)
              (Sym.afterCallF c { sFill with tab := plan.tab } sp cw (n / 4) plan.g plan.keys plan.recFields) s2 :=
            ⟨afterRhoW_agree c.regs sFill.nvars ρ1 s2 nums none,
             by rw [afterCallF_nvars]; show sFill.nvars ≤ sFill.nvars + c.regs + n / 4 + _; omega, Hafter, wafter⟩
          exact ⟨hrip, _, Cfill.then Cafter⟩
        · have hcpre : c.preVals ctx.defs (afterCall p q i st) := fun _ _ _ _ _ m => by rw [hcva] at m; cases m
          obtain ⟨r_, n_, l, hrm, hval, hll, hlm⟩ := (EnsureW.holds_whole epart).mp ((hpost_ens hcpre).2 e (by rw [hens]; exact List.mem_cons_self ..))
          rw [erun, houts] at hrm
          simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq, true_and] at hrm
          obtain ⟨e1, e2⟩ := hrm; cases e1.symm; cases e2.symm
          rw [hveq] at hval
          obtain ⟨nums, fvs, hnums, hlt, hlb, hrf, hv⟩ := postW_rec HT wfT henv hown hglen hwl hfd hfk hdl hll (by omega) hval hpb hsum hdist hrr
          obtain ⟨hl4, hlget⟩ := wordBytes_get nums l hlb
          have hrun : ∀ k, k < n / 4 → load s2.mem (((s0.reg RSP : Int) + cw).toNat + 4 * k) 4 = nums.getD k 0 := by
            intro k hk
            apply load4_of_bytes _ _ _ (by have := hlt (nums.getD k 0) (getD_mem _ _ (by omega)); unfold W32 at this; omega)
            intro bb hbb
            have lt' : 4 * k + bb < l.length := by omega
            have := hlm (4 * k + bb) lt'
            rw [s1r, ← Nat.add_assoc] at this
            rw [this, ← getD_of_lt l 0 lt']
            exact hlget k (by omega) bb hbb
          have Hafter := afterCallF_holds E c (c.stackAt (afterCall p q i st)) F.regs HT wfT hrsp hg.2 hg.1 hkeep psmall hlew (show cw + 4 * ((n / 4 : Nat) : Int) ≤ 0 by omega) hmem2 hdata2
            hnums hlt hrun hkeys (rfs := plan.recFields) (recVal := some (.record fvs)) (Or.inr ⟨hne, d, fvs, rfl, hrf, hv⟩) hvec2
          have wafter := afterCallF_wf wfT c F.regs sp cw (n / 4) plan.g hkeys plan.recFields (fun _ => by omega)
          rw [hwords]
          have Cafter : Carried ctx s0 ρ1 sFill (afterRhoW c.regs sFill.nvars ρ1 s2 nums (some (.record fvs)))
              (Sym.afterCallF c { sFill with tab := plan.tab } sp cw (n / 4) plan.g plan.keys plan.recFields) s2 :=
            ⟨afterRhoW_agree c.regs sFill.nvars ρ1 s2 nums (some (.record fvs)),
             by rw [afterCallF_nvars]; show sFill.nvars ≤ sFill.nvars + c.regs + n / 4 + _; omega, Hafter, wafter⟩
          exact ⟨hrip, _, Cfill.then Cafter⟩

/-- A run given to read and write that nothing was written to yet, taken as written with the words it held
at entry: what the verifier then holds is so of the same machine state. -/
theorem touch_carried {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (w : Nat) : Carried ctx s0 ρ s ρ (s.touch ctx w) st := by
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
        · refine ⟨HT.entry, HT.data, HT.reg, HT.small, HT.zf, HT.cf, HT.frame, HT.frameW, HT.facts, HT.bytes, HT.spec, HT.mem, HT.wrote,
            ⟨HT.words.vec, (fun w' mw' => HT.words.intact w' (List.mem_filter.mp mw').1), ?_, HT.words.spill⟩, HT.known, HT.range, HT.vecIntact⟩
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
        · refine ⟨wfT.base, wfT.reg, wfT.zf, wfT.cf, wfT.frame, wfT.frameW, wfT.facts, wfT.bytes, wfT.spec, wfT.wrote,
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
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (c : Contract) : Carried ctx s0 ρ s ρ (callTouch ctx s c) st := by
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
    (h : symStore8 ctx s w n o xr items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (hw : ctx.contract.outs[w]? = some (name, base, n))
    (ha : ∀ c : Int, ev ρ o = c → 0 ≤ c → c + 8 ≤ n → a = s0.reg base + c.toNat)
    (sx : EV.sem ρ s.nvars x (.lin xr)) :
    allowed (ctx.contract.perm ctx.pieces s0).write a 8 = true ∧
      ∃ ρ', Carried ctx s0 ρ s ρ' s' { st with mem := store st.mem a x 8 } := by
  unfold symStore8 at h
  cases hc : Lin.isConst o with
  | none => simp only [hc] at h; exact (refuse_ok h).elim
  | some c =>
    simp only [hc] at h
    split at h
    next hcond =>
      obtain ⟨c0, c4, cn, hnw⟩ := hcond
      split at h
      next hk =>
        -- the row of the remainders by 2^32 is a word: the high half is the row of the quotients, nothing is divided
        have ⟨w0, w1⟩ := isWord32Row_sound H (Bool.and_eq_true_iff.mp hk).2
        have hs := V.pure_ok h
        injection hs with h1 _
        subst h1
        have hA : a = s0.reg base + c.toNat := ha c (ev_isConst hc) c0 cn
        have hm := List.mem_of_getElem? hw
        have CT := touch_carried E H wf w
        have sxT := EV.sem_agree sx CT.agree CT.mono
        have eh := ev_high ρ xr
        have S1 := wAtomK_step_of CT.holds CT.wf (Ext.refl _) CT.wf.words.ok sxT.2.2
        have S2 := wAtomK_step_of CT.holds CT.wf S1.ext S1.ok (bounded_high sxT.2.2)
        have C5 := Carried.terms CT.holds CT.wf (S1.ext.trans S2.ext) S2.ok
        have hnw' : ((s.touch ctx w).wrote.any fun e => e.1 == w) = false := by
          rw [touch_wrote, List.any_eq_false]
          intro e me
          have := List.all_eq_true.mp hnw e me
          simpa using this
        have hx1 := sx.1
        have ex1 := sxT.2.1
        have d1 := S1.den
        have d2 := S2.den
        have d1' := den_ext (inp := inpOf ctx s0) (ρ := ρ) S1.ok.wf S2.ext S1.lt
        have Hs := C5.holds.storeRunWords E hw (c := c.toNat)
          (l := [(wAtomK (s.touch ctx w).known xr (s.touch ctx w).tab).1,
                 (wAtomK (s.touch ctx w).known (Lin.high xr) (wAtomK (s.touch ctx w).known xr (s.touch ctx w).tab).2).1])
          (lanes := [x % 4294967296, x / 4294967296]) rfl (by omega)
          (by simp only [List.length_cons, List.length_nil]; omega) hnw'
          (fun k hk => by
            have hk : k = 0 ∨ k = 1 := by simp only [List.length_cons, List.length_nil] at hk; omega
            rcases hk with rfl | rfl
            · have e : x % 4294967296 = (ev ρ xr % W32i).toNat := by unfold W32i; omega
              exact e.trans (d1'.trans d1).symm
            · have e : x / 4294967296 = (ev ρ (Lin.high xr) % W32i).toNat := by
                unfold M64 at hx1; unfold W32i at w1 eh ⊢; omega
              exact e.trans d2.symm) a hA
        rw [store8_words] at Hs
        refine ⟨allowed_of _ _ _ ?_, ρ, CT.then (C5.then ⟨Agree.refl _ _, Nat.le_refl _, Hs, ?_⟩)⟩
        · intro y hy1 hy2
          simp only [Contract.perm, Bool.or_eq_true]
          right
          unfold Contract.inOut
          exact List.any_eq_true.mpr ⟨(name, base, n), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        · have wf5 := C5.wf
          exact ⟨wf5.base, wf5.reg, wf5.zf, wf5.cf, wf5.frame, wf5.frameW, wf5.facts, wf5.bytes, wf5.spec, wf5.wrote,
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
      next =>
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
        have S1 := wAtomK_step_of CD.holds CD.wf (Ext.refl _) CD.wf.words.ok sxD.2.2
        have S2 := wAtomK_step_of CD.holds CD.wf S1.ext S1.ok bq
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
          (l := [(wAtomK (symDivide (s.touch ctx w) xr W32i).2.2.known xr (symDivide (s.touch ctx w) xr W32i).2.2.tab).1,
                 (wAtomK (symDivide (s.touch ctx w) xr W32i).2.2.known (symDivide (s.touch ctx w) xr W32i).1
                   (wAtomK (symDivide (s.touch ctx w) xr W32i).2.2.known xr (symDivide (s.touch ctx w) xr W32i).2.2.tab).2).1])
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
          exact ⟨wf5.base, wf5.reg, wf5.zf, wf5.cf, wf5.frame, wf5.frameW, wf5.facts, wf5.bytes, wf5.spec, wf5.wrote,
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

theorem store4_words (mem : Nat → Byte) (a x : Nat) : storeWords mem a [x % W32] = store mem a x 4 := by
  have h0 : x % W32 % 256 = x % 256 := by unfold W32; omega
  have h1 : x % W32 / 256 % 256 = x / 256 % 256 := by unfold W32; omega
  have h2 : x % W32 / 256 / 256 % 256 = x / 256 / 256 % 256 := by unfold W32; omega
  have h3 : x % W32 / 256 / 256 / 256 % 256 = x / 256 / 256 / 256 % 256 := by unfold W32; omega
  funext y
  simp only [storeWords, store, h0, h1, h2, h3]

/-- **Four bytes of a number stored into either a run given to write or the stack frame**:
delegates directly to `symStoreWords_sound` at width 1. -/
theorem symStore4_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) : Store4Ok E := by
  intro s s' addr xr items rest ρ st a x h H wf hlt ha sx
  unfold symStore4 at h
  let t0 := (match findOut addr ctx.contract.outs 0 with | some (.out w _) => s.touch ctx w | _ => s)
  have C0 : Carried ctx s0 ρ s ρ t0 st := by
    show Carried ctx s0 ρ s ρ (match findOut addr ctx.contract.outs 0 with | some (.out w _) => s.touch ctx w | _ => s) st
    cases findOut addr ctx.contract.outs 0 with
    | none => exact Carried.here H wf
    | some loc =>
      cases loc with
      | out w _ => exact touch_carried E H wf w
      | frame _ | region _ _ | data _ => exact Carried.here H wf
  have sx0 := EV.sem_agree sx C0.agree C0.mono
  have S1 := wAtomK_step_of C0.holds C0.wf (Ext.refl _) C0.wf.words.ok sx0.2.2
  have C1 := Carried.terms C0.holds C0.wf S1.ext S1.ok
  have hloc : ∀ A : Nat, (A : Int) = ev ρ addr → A < M64 → a = A := by
    intro A eA ltA; unfold M64 at hlt ltA; omega
  obtain ⟨al, C2⟩ := symStoreWords_sound E C1.holds C1.wf (by decide) h hloc (lanes := [x % W32]) rfl
    (fun i mi => by simp at mi; subst mi; exact S1.lt)
    (fun k hk => by
      have hk0 : k = 0 := by omega
      subst hk0
      change x % W32 = den (inpOf ctx s0) ρ (wAtomK t0.known xr t0.tab).2.list (wAtomK t0.known xr t0.tab).1
      rw [S1.den, ← sx0.2.1]; unfold W32 W32i; omega)
  rw [store4_words] at C2
  exact ⟨al, ρ, C0.then (C1.then C2)⟩

/-- **A call, by contract, of a function that writes a run of words for its caller**, the run of this
function it is given a part of being first taken as written with the words it held at entry. -/
theorem symCallW_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallW ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) (i : Instr) (Fi : Fits ctx st i c) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hex : CallExtra ctx s0 st c (afterCall p q i st)) :
    c.slot ≤ st.reg RSP ∧ allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  have T := callTouch_carried E H wf c
  have F := callFrameTouch_carried (ctx := ctx) (s0 := s0) (ρ := ρ) (st := st) c (c.fixeds ++ c.inouts) T.holds T.wf
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := symCallW'_sound E
    (show symCallW' ctx (callFrameTouch (callTouch ctx s c) c) c items = .ok (s', rest) from h)
    F.holds F.wf q hq i Fi hret hl hex
  refine ⟨g1, g2, g3, g4, g5, fun s2 post hdata => ?_⟩
  obtain ⟨hrip, ρ', C⟩ := g6 s2 post hdata
  exact ⟨hrip, ρ', T.then (F.then C)⟩

/-! ## A call of a function that writes a run of bytes -/

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
  | (y, .valArray _ _ _) :: args, r' :: regs, env, h, _, _, _ => by simp [calleeB] at h

/-- The called function's names on words stand for its names as the account has them in the state it
starts in (`s1`): a number is its register; a part of a run of bytes is the bytes there, as at entry. -/
theorem calleeB_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) {T : List Node}
    (c : Contract) (hm : c.regs = ctx.nreg) {s1 : State}
    (hreg : ∀ r ∈ c.argRegs, s1.reg r = st.reg r)
    (hspan : ∀ r l b off n, r ∈ c.argRegs → l ∈ c.argRegs → regionPart ctx s r l = some (b, off, n) →
      0 ≤ ev ρ off ∧ (ev ρ n).toNat = s1.reg l ∧ 0 ≤ ev ρ n ∧
      ∀ k, k < s1.reg l → s1.mem (s1.reg r + k) = s0.mem (s0.reg b + (ev ρ off).toNat + k)) :
    ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × WVal)}, (∀ r ∈ regs, r ∈ c.argRegs) →
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
      have ih := calleeB_sound (T := T) H c hm hreg hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec
      simp only [envIn]
      refine ⟨rfl, ?_, ih⟩
      have ra := hr r (List.mem_cons_self ..)
      have := WDen.num (ctx := ctx) (s0 := s0) (ρ := ρ) (T := T) (s.reg r)
      rw [← H.reg r (hm ▸ argRegs_lt ra), ← hreg r ra] at this
      exact this
  | (x, .bytes len) :: args, r :: regs, env, hr, h => by
    simp only [calleeB] at h
    cases hl : c.regOf len with
    | none =>
      simp only [hl] at h
      simp only [envIn, hl]
      exact calleeB_sound (T := T) H c hm hreg hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) h
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
          have ih := calleeB_sound (T := T) H c hm hreg hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) hrec
          simp only [envIn, hl]
          refine ⟨rfl, ?_, ih⟩
          have ra := hr r (List.mem_cons_self ..)
          obtain ⟨o0, en, n0, hm⟩ := hspan r l b off n ra (regOfIn_mem len c.args c.argRegs l hl) hp
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
    exact calleeB_sound (T := T) H c hm hreg hspan args regs (fun r' m => hr r' (List.mem_cons_of_mem _ m)) h
  | (x, .fixed n) :: args, r :: regs, env, _, h => by simp [calleeB] at h
  | (x, .inout n) :: args, r :: regs, env, _, h => by simp [calleeB] at h
  | (x, .valArray _ _ _) :: args, r :: regs, env, _, h => by simp [calleeB] at h

/-- What `callB` has looked up, where it says how the call is taken. -/
theorem callB_spec {ctx : Ctx} {s : Sym} {c : Contract} {plan : CallW} (h : callB ctx s c = .ok plan) :
    ∃ (run : String) (r n : Nat) (e : Ensure) (ids : List Nat) (env : List (String × WVal)) (args : SExpr) (vs : List WVal) (d : Def),
      c.mbounds = [] ∧ c.fixeds = [] ∧ c.inouts = [] ∧ c.returns = none ∧ c.result = none ∧
      c.outs = [(run, r, n)] ∧ c.ensures = [e] ∧ e.run = run ∧ e.lo = .num 0 ∧ e.hi = .num (n : Int) ∧
      callRun ctx s r n = some (plan.w, plan.first, ids) ∧ calleeB ctx c s c.args c.argRegs = some env ∧
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
              cases hce : calleeB ctx c s c.args c.argRegs with
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
                            have hok' : (keys.all (Key.ok s.nvars s.terms.length)) = true := by
                              rw [← Tab.size_eq_length]; simpa using hok
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
    (h : symCallB' ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) (i : Instr) (F : Fits ctx st i c) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hva : c.valArrays = []) (hex : CallExtra ctx s0 st c (afterCall p q i st)) :
    c.slot ≤ st.reg RSP ∧ allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  cases hsp : s.sp with
  | none => simp only [symCallB', hsp] at h; exact (refuse_ok h).elim
  | some sp =>
    simp only [symCallB', hsp] at h
    · have esp0 := ev_isConst (ρ := ρ) hsp; simp only [ev_sub, ev_var] at esp0
      have h10 := H.reg RSP ctx.rsp_lt; have h20 := H.entry RSP ctx.rsp_lt
      have hg : sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot - (c.stackAt (afterCall p q i st) : Int) := by
        have := hex.stack; omega
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
        have h1 := H.reg RSP ctx.rsp_lt
        have h2 := H.entry RSP ctx.rsp_lt
        have hrsp : (st.reg RSP : Int) = s0.reg RSP + sp := by omega
        have hstack := E.stackAt
        have habove := E.above
        have hsmallsp := H.small RSP
        have hslot := F.slot
        have h8 : c.slot ≤ st.reg RSP := by omega
        have s1rsp : (afterCall p q i st).reg RSP = st.reg RSP - c.slot := afterCall_rsp F.link
        have s1reg : ∀ r, CallKeeps r → (afterCall p q i st).reg r = st.reg r := fun r hr => afterCall_reg F.link hr
        have s1mem : ∀ x, x < st.reg RSP - c.slot ∨ st.reg RSP ≤ x → (afterCall p q i st).mem x = st.mem x :=
          fun x hx => afterCall_mem F.link h8 hx
        -- the run handed over to be written: whole words of one of this function's
        have hwm := List.mem_of_getElem? how
        have hout := E.outAt hwm
        have rmem : (run, r, n) ∈ c.outs := by rw [houts]; exact List.mem_cons_self ..
        have rarg : r ∈ c.argRegs := outsIn_mem c.args c.argRegs run r n rmem
        obtain ⟨r16, rne⟩ := F.arg rarg
        have b16 := outs_lt hwm
        have hrb : st.reg r = s0.reg b + 4 * plan.first := by
          have := H.reg r r16
          rw [hreg_r ρ, H.entry b b16] at this
          omega
        have s1r : (afterCall p q i st).reg r = s0.reg b + 4 * plan.first := by rw [s1reg r rne, hrb]
        -- a part of a run of bytes handed over to be read: where it lies, and that memory there is as at entry
        have hspan : ∀ r' l' b' off nn, r' ∈ c.argRegs → l' ∈ c.argRegs → regionPart ctx s r' l' = some (b', off, nn) →
            0 ≤ ev ρ off ∧ (ev ρ nn).toNat = (afterCall p q i st).reg l' ∧ 0 ≤ ev ρ nn ∧
            ∀ k, k < (afterCall p q i st).reg l' →
              (afterCall p q i st).mem ((afterCall p q i st).reg r' + k) = s0.mem (s0.reg b' + (ev ρ off).toNat + k) := by
          intro r' l' b' off nn ra la hp
          obtain ⟨lb, g1, g2, g3, g4, g5⟩ := regionPart_sound E H (F.arg ra).1 (F.arg la).1 hp
          have hlen := H.reg l' (F.arg la).1
          have er := s1reg r' (F.arg ra).2
          have el := s1reg l' (F.arg la).2
          have hregn := E.regionAt g1
          subst g2
          refine ⟨g3, by rw [el, ← hlen]; omega, by rw [← hlen]; omega, fun k hk => ?_⟩
          rw [el] at hk
          have ea : st.reg r' = s0.reg b' + (ev ρ off).toNat := by omega
          rw [er, ea, s1mem _ (by omega)]
          exact H.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (E.region_notOut g1 (by omega) (by omega))
        have hpart : ∀ r' l', (r', l') ∈ c.regions → ∃ b' off nn lb, regionPart ctx s r' l' = some (b', off, nn) ∧ r' ∈ c.argRegs ∧ l' ∈ c.argRegs ∧
            (b', lb) ∈ ctx.contract.regions ∧ 0 ≤ ev ρ off ∧ (st.reg r' : Int) = s0.reg b' + ev ρ off ∧ ev ρ off + st.reg l' ≤ s0.reg lb := by
          intro r' l' m
          obtain ⟨b', off, nn, hp⟩ := calleeB_regions c c.args c.argRegs hce r' l' m
          obtain ⟨ra, len, hlen⟩ := regionsIn_mem c c.args c.argRegs r' l' m
          have la := regOfIn_mem len c.args c.argRegs l' hlen
          obtain ⟨lb, g1, _, g3, g4, g5⟩ := regionPart_sound E H (F.arg ra).1 (F.arg la).1 hp
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
          calleeB_sound H c F.regs (fun r' m => s1reg r' (F.arg m).2) hspan c.args c.argRegs (fun _ m => m) hce
        have hpre : c.pre q (afterCall p q i st) := by
          refine ⟨afterCall_rip p q i st, ?_, ?_, ?_, hq, ?_, ?_, ?_, ?_, ?_, ?_,
            (fun j x r count l m => by rw [tableAt_none hl] at m; cases m), hex.atLeast, afterCall_aligned F p q, hex.preLines,
            (fun _ _ _ _ _ m => by rw [hva] at m; cases m), hex.aligns, hex.lineDisjoint⟩
          · exact afterCall_small F.link H.small
          · rw [s1rsp]; omega
          · rw [s1rsp]; omega
          · intro r' l' m
            obtain ⟨b', off, nn, lb, hp, ra, la, g1, g3, g4, g5⟩ := hpart r' l' m
            have hregn := E.regionAt g1
            have er := s1reg r' (F.arg ra).2
            have el := s1reg l' (F.arg la).2
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
            rw [s1r, s1reg r'' (F.arg ra).2, s1reg l'' (F.arg la).2]
            omega
          · rw [houts]; exact List.pairwise_singleton _ _
          · intro x' r' n' m; rw [hfx] at m; cases m
          · intro x' bd m r' hr'
            obtain ⟨items', res, he⟩ := each_mem hbounds (x', bd) m
            simp only [hr'] at he
            have hge := entail_sound he ρ H.facts
            rw [ev_sub, ev_const] at hge
            have ra := regOfIn_mem x' c.args c.argRegs r' hr'
            have hreg' := H.reg r' (F.arg ra).1
            rw [s1reg r' (F.arg ra).2]
            omega
          · intro x' off bd m; rw [hmb] at m; cases m
        have hread : ∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true := by
          intro a ha
          rw [perm_read_split, Bool.or_eq_true] at ha
          refine ha.elim (fun ha => ?_) (fun ha => read_pieces H p q i ha)
          simp only [Contract.perm, inLane_false hl, Contract.inValArray, hva, List.any_nil, inPieces_nil, Bool.or_false, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          left; left; left
          rcases ha with ((ha | ha) | ha) | ha
          · left; left; left; omega
          · left; left; left; omega
          · obtain ⟨⟨r', l'⟩, m, hin⟩ := List.any_eq_true.mp ha
            obtain ⟨b', off, nn, lb, hp, ra, la, g1, g3, g4, g5⟩ := hpart r' l' m
            simp only [Bool.and_eq_true, decide_eq_true_eq, s1reg r' (F.arg ra).2, s1reg l' (F.arg la).2] at hin
            left; right
            exact List.any_eq_true.mpr ⟨(b', lb), g1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
          · simp only [Contract.inFixed, hfx, hinouts, List.any_nil, Bool.or_self] at ha
            cases ha
        have hwrite : ∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true := by
          intro a ha
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          rcases ha with ha | ha
          · left; omega
          · right
            simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, s1r] at ha
            unfold Contract.inOut
            exact List.any_eq_true.mpr ⟨(xw, b, n0), hwm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        have hwr : allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true := by
          apply allowed_of
          intro x hx1 hx2
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          left; omega
        refine ⟨h8, hwr, hpre, hread, hwrite, ?_⟩
        intro s2 post hdata2
        have hbytes2 : ∀ a, s2.mem a = (afterCall p q i st).mem a ∨ (s2.mem a).val < 256 := fun a => Or.inr (s2.mem a).isLt
        obtain ⟨prip, prsp, psaved, pmem, pret, psmall, hpost_ens, pvec⟩ := post
        have hvec2 : ∀ r ∈ c.keepsVec, s2.vec r = st.vec r := fun r hr =>
          (pvec r hr).trans (congrFun (afterCall_vec p q i st) r)
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
        -- returned to and in the part it wrote
        have hmem2 : ∀ a, a + c.slot + c.stackAt (afterCall p q i st) < st.reg RSP ∨ st.reg RSP ≤ a →
            a < s0.reg b + 4 * plan.first ∨ s0.reg b + 4 * (plan.first + n / 4) ≤ a → s2.mem a = st.mem a := by
          intro a ha hb
          rw [pmem a (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1rsp]; omega)
            (by simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1r]; omega)]
          exact s1mem a (by omega)
        -- what the contract of the called function says of the run: its bytes are the list the definition gives
        have hcpre : c.preVals ctx.defs (afterCall p q i st) := fun _ _ _ _ _ m => by rw [hva] at m; cases m
        obtain ⟨r_, n_, a_, b_, l, hrm, hlo, hhi, hval, ha0, hab, hbn, hlm⟩ := (hpost_ens hcpre).1 e (by rw [hens]; exact List.mem_cons_self ..)
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
        have hheld : ctx.contract.preVals ctx.defs s0 → ∃ d', findDef ctx.defs plan.g = some d' ∧ d'.params.length = plan.keys.length ∧
            Value ctx.defs (d'.params.zip (plan.keys.map (Key.val ctx s0 ρ s.terms))) d'.body
              (if true then .list (wordBytes ((List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4))
                else .list (((List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4).map Val.word)) := by
          intro hpv
          obtain ⟨B, hB⟩ := held_bound H hpv
          obtain ⟨as, eas, das⟩ := wevalList_sound (ev' := evalSpec ctx.defs (WFUEL + B) (c.env (afterCall p q i st)))
            (fun e' v' hv' => weval_sound H wf hpv hB WFUEL env _ e' v' hv' henv) args vs hwl
          have same : as2 = as := by
            have a1 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.env (afterCall p q i st)))
              (fun a v hh => evalSpec_mono ctx.defs f2 hh _ (Nat.le_max_left _ _)) args ha2
            have a2 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.env (afterCall p q i st)))
              (fun a v hh => evalSpec_mono ctx.defs (WFUEL + B) hh _ (Nat.le_max_right _ _)) args eas
            rw [a1] at a2
            injection a2
          subst same
          have ekeys : as2 = plan.keys.map (Key.val ctx s0 ρ s.terms) := flatKeys_den wf das hfk
          exact ⟨d, hfd, hdl, f2, by rw [← ekeys, if_pos rfl, ← hlb]; exact hev2⟩
        have Hafter := afterCallW_holds E c (c.slot + c.stackAt (afterCall p q i st)) F.regs H wf hrsp (by omega) hg.1 hkeep psmall how (show 4 * (plan.first + n / 4) ≤ n0 by omega) hnow (fun a ha hb => hmem2 a (by omega) hb) hdata2
          hnl hlt hrun hkeys (bytes := true) (rfs := []) (recVal := none) (Or.inl ⟨rfl, hheld⟩) hvec2
        have wafter := afterCallW_wf wf c F.regs sp plan.w plan.first (n / 4) plan.g hkeys true [] (fun h => by simp at h)
        rw [hwords]
        exact ⟨hrip, _, afterRhoW_agree c.regs s.nvars ρ s2 _, by rw [afterCallW_nvars]; show s.nvars ≤ s.nvars + c.regs + n / 4 + _; omega, Hafter, wafter⟩

/-- **A call, by contract, of a function that writes a run of bytes for its caller**, the run of this
function it is given a part of being first taken as written with the words it held at entry. -/
theorem symCallB_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallB ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) (i : Instr) (Fi : Fits ctx st i c) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hva : c.valArrays = []) (hex : CallExtra ctx s0 st c (afterCall p q i st)) :
    c.slot ≤ st.reg RSP ∧ allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  have T := callTouch_carried E H wf c
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := symCallB'_sound E (show symCallB' ctx (callTouch ctx s c) c items = .ok (s', rest) from h)
    T.holds T.wf q hq i Fi hret hl hva hex
  refine ⟨g1, g2, g3, g4, g5, fun s2 post hdata => ?_⟩
  obtain ⟨hrip, ρ', C⟩ := g6 s2 post hdata
  exact ⟨hrip, ρ', T.then C⟩

/-- Rows the proof file gives and the verifier has shown join the facts (`symKnow`): what the verifier
holds is still so, of the same state of the machine and the same unknowns. (Whatever the advice is: it
only words what is printed where a proof has run out.) -/
theorem symKnow_sound {ctx : Ctx} {s0 : State} {advice : Sym → List Row} {ρ : Nat → Int} {st : State} :
    ∀ (fuel : Nat) {s s' : Sym} {items rest : Items}, symKnow advice fuel s items = .ok (s', rest) →
      Holds ctx s0 ρ s st → WF ctx s → Carried ctx s0 ρ s ρ s' st
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
          (⟨H.entry, H.data, H.reg, H.small, H.zf, H.cf, H.frame, H.frameW,
            fun g' m => by
              rcases List.mem_cons.mp m with rfl | m
              · exact hrow
              · exact H.facts g' m,
            H.bytes, H.spec, H.mem, H.wrote, H.words, H.known, H.range, H.vecIntact⟩ :
            Holds ctx s0 ρ { s with facts := g :: s.facts } st)
          ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.frameW,
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
    (h : symCallF ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) (i : Instr) (Fi : Fits ctx st i c) (hret : p.base + i.next < M64) (hl : c.lanes = []) (hex : CallExtra ctx s0 st c (afterCall p q i st)) :
    c.slot ≤ st.reg RSP ∧ allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  have F := callFrameTouch_carried (ctx := ctx) (s0 := s0) (ρ := ρ) (st := st) c (c.fixeds ++ c.inouts) H wf
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := symCallF'_sound E
    (show symCallF' ctx (callFrameTouch s c) c items = .ok (s', rest) from h) F.holds F.wf q hq i Fi hret hl hex
  refine ⟨g1, g2, g3, g4, g5, fun s2 post hdata => ?_⟩
  obtain ⟨hrip, ρ', C⟩ := g6 s2 post hdata
  exact ⟨hrip, ρ', F.then C⟩

end Ode
