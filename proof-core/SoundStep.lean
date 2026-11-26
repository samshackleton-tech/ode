import SoundState
/-!
# Why the verifier's yes is right, 3: an instruction on symbols and the instruction on the machine
-/
namespace Ode
open Arithmetic

/-- The setting of every lemma here: the verifier's `ctx` is of the program `p`, and `s0` is a state at the
function's entry of which the caller has seen to what the contract asks; the program is loaded there, and
no byte of its files' read-only data is one the function may write. -/
structure Setting (ctx : Ctx) (p : Program) (s0 : State) : Prop where
  code : p.code = ctx.code
  pre : ctx.contract.pre p s0
  quiet : ctx.contract.quietAt s0
  loaded : Loaded ctx.pieces s0
  dataQuiet : ∀ k pc, ctx.pieces[k]? = some pc → ∀ j, j < pc.bytes.length → s0.marks.mem (s0.data k + j) = false
  apart : ∀ a, inPieces ctx.pieces s0 a = true → ctx.contract.inFrame s0 a = false ∧ ctx.contract.inOut s0 a = false

namespace Setting
variable {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0)
include E
theorem rip : s0.rip = p.base := E.pre.1
theorem small (r : Nat) : s0.reg r < M64 := E.pre.2.1 r
theorem stackAt : ctx.contract.stackAt s0 ≤ s0.reg RSP := E.pre.2.2.1
theorem stack : ctx.contract.stack ≤ s0.reg RSP := Nat.le_trans (Contract.stack_le_stackAt _ _) E.stackAt
theorem above : s0.reg RSP + ctx.contract.slot < M64 := E.pre.2.2.2.1
theorem fits {o : Nat} {i : Instr} (h : (o, i) ∈ p.code) : p.base + i.next < M64 := E.pre.2.2.2.2.1 (o, i) h
theorem regionAt {r l : Nat} (h : (r, l) ∈ ctx.contract.regions) :
    s0.reg r + s0.reg l ≤ M64 ∧ (s0.reg r + s0.reg l ≤ s0.reg RSP - ctx.contract.stackAt s0 ∨ s0.reg RSP + ctx.contract.slot ≤ s0.reg r) :=
  E.pre.2.2.2.2.2.1 r l h
theorem region {r l : Nat} (h : (r, l) ∈ ctx.contract.regions) :
    s0.reg r + s0.reg l ≤ M64 ∧ (s0.reg r + s0.reg l ≤ s0.reg RSP - ctx.contract.stack ∨ s0.reg RSP + ctx.contract.slot ≤ s0.reg r) := by
  obtain ⟨h1, h2⟩ := E.regionAt h
  have hle := Contract.stack_le_stackAt ctx.contract s0
  exact ⟨h1, h2.elim (fun ha => Or.inl (by omega)) Or.inr⟩
theorem byte {r l : Nat} (h : (r, l) ∈ ctx.contract.regions) (k : Nat) (hk : k < s0.reg l) : (s0.mem (s0.reg r + k)).val < 256 :=
  (s0.mem _).isLt
/-- A run given to write: in memory, and apart from the frame and the address to return to. -/
theorem outAt {x : String} {r n : Nat} (h : (x, r, n) ∈ ctx.contract.outs) :
    s0.reg r + n ≤ M64 ∧ (s0.reg r + n ≤ s0.reg RSP - ctx.contract.stackAt s0 ∨ s0.reg RSP + ctx.contract.slot ≤ s0.reg r) :=
  ⟨(E.pre.2.2.2.2.2.2.1 x r n h).1, (E.pre.2.2.2.2.2.2.1 x r n h).2.1⟩
theorem out {x : String} {r n : Nat} (h : (x, r, n) ∈ ctx.contract.outs) :
    s0.reg r + n ≤ M64 ∧ (s0.reg r + n ≤ s0.reg RSP - ctx.contract.stack ∨ s0.reg RSP + ctx.contract.slot ≤ s0.reg r) := by
  obtain ⟨h1, h2⟩ := E.outAt h
  have hle := Contract.stack_le_stackAt ctx.contract s0
  exact ⟨h1, h2.elim (fun ha => Or.inl (by omega)) Or.inr⟩
theorem outRegion {x : String} {r n : Nat} (h : (x, r, n) ∈ ctx.contract.outs) {r' l : Nat} (h' : (r', l) ∈ ctx.contract.regions) :
    s0.reg r + n ≤ s0.reg r' ∨ s0.reg r' + s0.reg l ≤ s0.reg r := (E.pre.2.2.2.2.2.2.1 x r n h).2.2 r' l h'
/-- Two runs given to write, not the same one, lie apart. -/
theorem outOut {i j : Nat} {x x' : String} {r n r' n' : Nat} (hi : ctx.contract.outs[i]? = some (x, r, n))
    (hj : ctx.contract.outs[j]? = some (x', r', n')) (ne : i ≠ j) :
    s0.reg r + n ≤ s0.reg r' ∨ s0.reg r' + n' ≤ s0.reg r := by
  have P := List.pairwise_iff_getElem.mp E.pre.2.2.2.2.2.2.2.1
  obtain ⟨li, ei⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨lj, ej⟩ := List.getElem?_eq_some_iff.mp hj
  rcases Nat.lt_or_gt_of_ne ne with lt | gt
  · have := P i j li lj lt
    rw [ei, ej] at this
    exact this
  · have := P j i lj li gt
    rw [ei, ej] at this
    exact this.symm
/-- An address in a run given to read is in no run given to write. -/
theorem region_notOut {r l : Nat} (h : (r, l) ∈ ctx.contract.regions) {a : Nat} (h1 : s0.reg r ≤ a) (h2 : a < s0.reg r + s0.reg l) :
    ctx.contract.inOut s0 a = false := by
  unfold Contract.inOut
  rw [List.any_eq_false]
  intro ⟨x, r', n⟩ hm
  have := E.outRegion hm h
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega
theorem frame_notOutAt {a : Nat} (h1 : s0.reg RSP - ctx.contract.stackAt s0 ≤ a) (h2 : a < s0.reg RSP + ctx.contract.slot) :
    ctx.contract.inOut s0 a = false := by
  unfold Contract.inOut
  rw [List.any_eq_false]
  intro ⟨x, r', n⟩ hm
  have := (E.outAt hm).2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega
/-- An address of the frame, or of the address to return to, is in no run given to write. -/
theorem frame_notOut {a : Nat} (h1 : s0.reg RSP - ctx.contract.stack ≤ a) (h2 : a < s0.reg RSP + ctx.contract.slot) :
    ctx.contract.inOut s0 a = false := by
  have hle := Contract.stack_le_stackAt ctx.contract s0
  exact E.frame_notOutAt (by omega) h2
end Setting

theorem indexOf_lt (name : String) : ∀ (l : List String) (k r : Nat), indexOf name l k = some r → r < k + l.length
  | [], _, _, h => by simp [indexOf] at h
  | n :: ns, k, r, h => by
    simp only [indexOf] at h
    split at h
    · injection h with h; subst h; simp
    · have := indexOf_lt name ns (k + 1) r h
      simp only [List.length_cons]; omega

/-- A register's number, by its name on either machine, is below thirty-two. -/
theorem regIndex_lt {name : String} {r : Nat} (h : regIndex name = some r) : r < 32 := by
  unfold regIndex at h
  split at h
  next r' e =>
    injection h with h; subst h
    have := indexOf_lt name regNames 0 r' e
    simp [regNames] at this
    omega
  next =>
    have := indexOf_lt name regNamesArm 0 r h
    simpa [regNamesArm] using this

theorem regOf_lt {bind : Bind} {n : String} {r : Nat} (h : regOf bind n = some r) : r < 32 := by
  unfold regOf at h
  split at h
  · cases hb : bind.lookup n with
    | none => simp [hb] at h
    | some x => simp [hb] at h; exact regIndex_lt h
  · exact regIndex_lt h

/-- The register the verifier reads a name as: the register the machine reads it as, and one the function's
machine has. -/
theorem Ctx.regOf_some {ctx : Ctx} {bind : Bind} {n : String} {r : Nat} (h : ctx.regOf bind n = some r) :
    Ode.regOf bind n = some r ∧ r < ctx.nreg := by
  unfold Ctx.regOf at h
  cases hr : Ode.regOf bind n with
  | none => rw [hr] at h; cases h
  | some r' =>
    rw [hr] at h
    simp only [Option.filter] at h
    split at h
    next hlt => injection h with h; subst h; exact ⟨rfl, of_decide_eq_true hlt⟩
    next => cases h

theorem regOfIn_mem (name : String) : ∀ (args : List (String × Kind)) (regs : List Nat) (r : Nat),
    regOfIn name args regs = some r → r ∈ regs
  | [], _, _, h => by simp [regOfIn] at h
  | _ :: _, [], _, h => by simp [regOfIn] at h
  | (n, _) :: args, x :: regs, r, h => by
    simp only [regOfIn] at h
    split at h
    · injection h with h; subst h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (regOfIn_mem name args regs r h)

theorem regionsIn_mem (c : Contract) : ∀ (args : List (String × Kind)) (regs : List Nat) (b l : Nat),
    (b, l) ∈ regionsIn c args regs → b ∈ regs ∧ ∃ len, c.regOf len = some l
  | [], _, _, _, h => by simp [regionsIn] at h
  | _ :: _, [], _, _, h => by simp [regionsIn] at h
  | (_, .number) :: args, x :: regs, b, l, h => by
    simp only [regionsIn] at h
    have := regionsIn_mem c args regs b l h
    exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
  | (_, .out _) :: args, x :: regs, b, l, h => by
    simp only [regionsIn] at h
    have := regionsIn_mem c args regs b l h
    exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
  | (_, .fixed _) :: args, x :: regs, b, l, h => by
    simp only [regionsIn] at h
    have := regionsIn_mem c args regs b l h
    exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
  | (_, .inout _) :: args, x :: regs, b, l, h => by
    simp only [regionsIn] at h
    have := regionsIn_mem c args regs b l h
    exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
  | (_, .valArray _ _ _) :: args, x :: regs, b, l, h => by
    simp only [regionsIn] at h
    have := regionsIn_mem c args regs b l h
    exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
  | (_, .bytes len) :: args, x :: regs, b, l, h => by
    simp only [regionsIn] at h
    split at h
    next l' hl =>
      cases h with
      | head => exact ⟨List.mem_cons_self .., len, hl⟩
      | tail _ h =>
        have := regionsIn_mem c args regs b l h
        exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    next =>
      have := regionsIn_mem c args regs b l h
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

/-- A register an argument is in is a register of the function's machine. -/
theorem argRegs_lt {c : Contract} {r : Nat} (h : r ∈ c.argRegs) : r < c.regs := (argRegs_spec h).1

theorem regions_lt {c : Contract} {b l : Nat} (h : (b, l) ∈ c.regions) : b < c.regs ∧ l < c.regs := by
  obtain ⟨hb, len, hl⟩ := regionsIn_mem c c.args c.argRegs b l h
  exact ⟨argRegs_lt hb, argRegs_lt (regOfIn_mem len c.args c.argRegs l hl)⟩

theorem signed_ev (ρ : Nat → Int) (r : Row) : ev ρ (signed r) = ev ρ r ∨ ev ρ (signed r) = ev ρ r - 2 ^ 64 := by
  unfold signed
  split
  next k hk =>
    split
    · right; rw [ev_isConst hk]; simp
    · left; rfl
  next => left; rfl

theorem lookupByte_mem {r : Nat} {o : Row} : ∀ {l : List (Nat × Nat × Row)} {v : Nat}, lookupByte r o l = some v → (v, r, o) ∈ l
  | [], _, h => by simp [lookupByte] at h
  | (v', r', o') :: rest, v, h => by
    simp only [lookupByte] at h
    split at h
    next e => injection h with h; subst h; rw [e.1, e.2]; exact List.mem_cons_self ..
    next => exact List.mem_cons_of_mem _ (lookupByte_mem h)

/-- From one state of the verifier to a later one: the unknowns in use keep their values, and what the
later state holds is so. -/
structure Carried (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (s : Sym) (ρ' : Nat → Int) (s' : Sym) (st' : State) : Prop where
  agree : Agree s.nvars ρ ρ'
  mono : s.nvars ≤ s'.nvars
  holds : Holds ctx s0 ρ' s' st'
  wf : WF ctx s'

theorem Carried.here {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF ctx s) :
    Carried ctx s0 ρ s ρ s st := ⟨Agree.refl _ _, Nat.le_refl _, H, wf⟩

theorem Carried.then {ctx : Ctx} {s0 : State} {ρ ρ1 ρ2 : Nat → Int} {s s1 s2 : Sym} {st1 st2 : State}
    (a : Carried ctx s0 ρ s ρ1 s1 st1) (b : Carried ctx s0 ρ1 s1 ρ2 s2 st2) : Carried ctx s0 ρ s ρ2 s2 st2 :=
  ⟨Agree.trans a.mono a.agree b.agree, Nat.le_trans a.mono b.mono, b.holds, b.wf⟩

/-- The unknowns with one more given a value. -/
def extend (ρ : Nat → Int) (n : Nat) (x : Int) : Nat → Int := fun k => if k = n then x else ρ k

theorem extend_new (ρ : Nat → Int) (n : Nat) (x : Int) : extend ρ n x n = x := by simp [extend]

theorem extend_agree (ρ : Nat → Int) (n : Nat) (x : Int) : Agree n ρ (extend ρ n x) := fun k hk => by
  show ρ k = if k = n then x else ρ k
  rw [if_neg (by omega)]

/-- One more unknown, with facts of it and one thing known of it: what the state held stays so, where the
facts and the thing known are so of the value the unknown is given. -/
theorem Carried.fresh {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (x : Int) (rows : List Row) (k : Known)
    (hb : ∀ f ∈ rows, bounded (s.nvars + 1) f) (hk : k.wf (s.nvars + 1) s.terms.length)
    (hrows : ∀ f ∈ rows, f.holds (extend ρ s.nvars x)) (hknown : k.holds ctx s0 (extend ρ s.nvars x) s.terms) :
    Carried ctx s0 ρ s (extend ρ s.nvars x) { s with nvars := s.nvars + 1, known := k :: s.known, facts := rows ++ s.facts } st := by
  have ag := extend_agree ρ s.nvars x
  have H' := H.agree wf ag
  have le : s.nvars ≤ s.nvars + 1 := Nat.le_succ _
  refine ⟨ag, le, ?_, ?_⟩
  · exact {
      range := H'.range
      vecIntact := H'.vecIntact
      entry := H'.entry, data := H'.data, reg := H'.reg, small := H'.small, zf := H'.zf, cf := H'.cf, frame := H'.frame, frameW := H'.frameW, bytes := H'.bytes,
      spec := H'.spec, mem := H'.mem, wrote := H'.wrote, words := H'.words,
      facts := fun f m => (List.mem_append.mp m).elim (hrows f) (H'.facts f),
      known := fun k' m => by
        rcases List.mem_cons.mp m with rfl | m
        · exact hknown
        · exact H'.known k' m }
  · exact {
      range := fun rg hr => ⟨bounded_mono le (wf.range rg hr).1, fun v hv => SVal.bounded_mono le ((wf.range rg hr).2 v hv)⟩
      base := Nat.le_trans wf.base le
      reg := fun r hr => bounded_mono le (wf.reg r hr)
      zf := Flag.bounded_mono le wf.zf
      cf := Flag.bounded_mono le wf.cf
      frame := fun o v m => bounded_mono le (wf.frame o v m)
      frameW := wf.frameW
      bytes := fun v r o m => ⟨Nat.lt_of_lt_of_le (wf.bytes v r o m).1 le, bounded_mono le (wf.bytes v r o m).2⟩
      spec := fun f m => SFact.bounded_mono le (wf.spec f m)
      wrote := fun w o x m => ⟨bounded_mono le (wf.wrote w o x m).1, bounded_mono le (wf.wrote w o x m).2⟩
      words := wf.words.mono rfl rfl rfl le
      facts := fun f m => (List.mem_append.mp m).elim (hb f) (fun m => bounded_mono le (wf.facts f m))
      known := fun k' m => by
        rcases List.mem_cons.mp m with rfl | m
        · exact hk
        · exact Known.wf_mono le (Nat.le_refl _) (wf.known k' m) }

/-- More unknowns at once, with facts of them and one thing known of them: what the state held stays so,
where the facts and the thing known are so of the values the unknowns are given. -/
theorem Carried.more {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (m : Nat) (ag : Agree s.nvars ρ ρ') (rows : List Row) (k : Known)
    (hb : ∀ f ∈ rows, bounded (s.nvars + m) f) (hk : k.wf (s.nvars + m) s.terms.length)
    (hrows : ∀ f ∈ rows, f.holds ρ') (hknown : k.holds ctx s0 ρ' s.terms) :
    Carried ctx s0 ρ s ρ' { s with nvars := s.nvars + m, known := k :: s.known, facts := rows ++ s.facts } st := by
  have H' := H.agree wf ag
  have le : s.nvars ≤ s.nvars + m := Nat.le_add_right _ _
  refine ⟨ag, le, ?_, ?_⟩
  · exact {
      range := H'.range
      vecIntact := H'.vecIntact
      entry := H'.entry, data := H'.data, reg := H'.reg, small := H'.small, zf := H'.zf, cf := H'.cf, frame := H'.frame, frameW := H'.frameW, bytes := H'.bytes,
      spec := H'.spec, mem := H'.mem, wrote := H'.wrote, words := H'.words,
      facts := fun f m => (List.mem_append.mp m).elim (hrows f) (H'.facts f),
      known := fun k' m => by
        rcases List.mem_cons.mp m with rfl | m
        · exact hknown
        · exact H'.known k' m }
  · exact {
      range := fun rg hr => ⟨bounded_mono le (wf.range rg hr).1, fun v hv => SVal.bounded_mono le ((wf.range rg hr).2 v hv)⟩
      base := Nat.le_trans wf.base le
      reg := fun r hr => bounded_mono le (wf.reg r hr)
      zf := Flag.bounded_mono le wf.zf
      cf := Flag.bounded_mono le wf.cf
      frame := fun o v m => bounded_mono le (wf.frame o v m)
      frameW := wf.frameW
      bytes := fun v r o m => ⟨Nat.lt_of_lt_of_le (wf.bytes v r o m).1 le, bounded_mono le (wf.bytes v r o m).2⟩
      spec := fun f m => SFact.bounded_mono le (wf.spec f m)
      wrote := fun w o x m => ⟨bounded_mono le (wf.wrote w o x m).1, bounded_mono le (wf.wrote w o x m).2⟩
      words := wf.words.mono rfl rfl rfl le
      facts := fun f m => (List.mem_append.mp m).elim (hb f) (fun m => bounded_mono le (wf.facts f m))
      known := fun k' m => by
        rcases List.mem_cons.mp m with rfl | m
        · exact hk
        · exact Known.wf_mono le (Nat.le_refl _) (wf.known k' m) }

/-- More unknowns at once, of which nothing is said: what the state held stays so. -/
theorem Carried.unknowns {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (m : Nat) (ag : Agree s.nvars ρ ρ') :
    Carried ctx s0 ρ s ρ' { s with nvars := s.nvars + m } st := by
  have H' := H.agree wf ag
  have le : s.nvars ≤ s.nvars + m := Nat.le_add_right _ _
  refine ⟨ag, le, ?_, ?_⟩
  · exact {
      range := H'.range
      vecIntact := H'.vecIntact
      entry := H'.entry, data := H'.data, reg := H'.reg, small := H'.small, zf := H'.zf, cf := H'.cf, frame := H'.frame, frameW := H'.frameW, bytes := H'.bytes,
      spec := H'.spec, mem := H'.mem, wrote := H'.wrote, words := H'.words, facts := H'.facts, known := H'.known }
  · exact {
      range := fun rg hr => ⟨bounded_mono le (wf.range rg hr).1, fun v hv => SVal.bounded_mono le ((wf.range rg hr).2 v hv)⟩
      base := Nat.le_trans wf.base le
      reg := fun r hr => bounded_mono le (wf.reg r hr)
      zf := Flag.bounded_mono le wf.zf
      cf := Flag.bounded_mono le wf.cf
      frame := fun o v m => bounded_mono le (wf.frame o v m)
      frameW := wf.frameW
      bytes := fun v r o m => ⟨Nat.lt_of_lt_of_le (wf.bytes v r o m).1 le, bounded_mono le (wf.bytes v r o m).2⟩
      spec := fun f m => SFact.bounded_mono le (wf.spec f m)
      wrote := fun w o x m => ⟨bounded_mono le (wf.wrote w o x m).1, bounded_mono le (wf.wrote w o x m).2⟩
      words := wf.words.mono rfl rfl rfl le
      facts := fun f m => bounded_mono le (wf.facts f m)
      known := fun k' m => Known.wf_mono le (Nat.le_refl _) (wf.known k' m) }

/-- The register with a table's count of blocks is one of the machine's. -/
theorem tableAt_lt {c : Contract} {j : Nat} {x : String} {r count l : Nat} (h : c.tableAt j = some (x, r, count, l)) : l < c.regs := by
  unfold Contract.tableAt at h
  cases hj : c.fixeds[j]? with
  | none => rw [hj] at h; cases h
  | some t =>
    obtain ⟨x', r', n⟩ := t
    rw [hj] at h
    simp only at h
    cases hl : c.lanes.lookup x' with
    | none => rw [hl] at h; cases h
    | some y =>
      rw [hl] at h
      simp only at h
      cases hr : c.regOf y with
      | none => rw [hr] at h; cases h
      | some l' =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, _, rfl⟩ := h
        exact argRegs_lt (regOfIn_mem y c.args c.argRegs l' hr)

theorem lookupByteVar_mem {v r : Nat} {o : Row} : ∀ {l : List (Nat × Nat × Row)}, lookupByteVar v r l = some o → (v, r, o) ∈ l
  | [], h => by simp [lookupByteVar] at h
  | (v', r', o') :: rest, h => by
    unfold lookupByteVar at h
    split at h
    next he =>
      injection h with h; subst h; obtain ⟨rfl, rfl⟩ := he
      exact List.mem_cons_self ..
    next => exact List.mem_cons_of_mem _ (lookupByteVar_mem h)

theorem readByte_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {r : Nat} {o v : Row}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : readByte ctx s r o items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hb : bounded s.nvars o) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ bounded s'.nvars v ∧
      ∃ base len, ctx.contract.regions[r]? = some (base, len) ∧ 0 ≤ ev ρ' o ∧ ev ρ' o < s0.reg len ∧
        ev ρ' v = s0.mem (s0.reg base + (ev ρ' o).toNat) := by
  cases hreg : ctx.contract.regions[r]? with
  | none => simp only [readByte, hreg] at h; exact (refuse_ok h).elim
  | some bl =>
    obtain ⟨base, len⟩ := bl
    simp only [readByte, hreg] at h
    obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨_, r2, e2, h⟩ := V.bind_ok h
    have g1 := entail_sound e1 ρ H.facts
    have g2 := entail_sound e2 ρ H.facts
    have hlen : len < ctx.nreg := (regions_lt (List.mem_of_getElem? hreg)).2
    simp only [ev_sub, ev_var, ev_const] at g2
    rw [H.entry len hlen] at g2
    cases hv : lookupByte r o s.bytes with
    | some v0 =>
      simp only [hv] at h
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      have m := lookupByte_mem hv
      obtain ⟨base', len', hr', _, _, h4⟩ := H.bytes v0 r o m
      rw [hreg] at hr'
      injection hr' with hr'
      injection hr' with hb1 hb2
      subst hb1 hb2
      refine ⟨ρ, Carried.here H wf, bounded_var (wf.bytes v0 r o m).1, base, len, rfl, g1, by omega, ?_⟩
      rw [ev_var]; exact h4
    | none =>
      simp only [hv] at h
      obtain ⟨opt, r3, _, h⟩ := V.bind_ok h
      cases opt with
      | some v0 =>
        cases hlv : lookupByteVar v0 r s.bytes with
        | none => simp only [hlv] at h; exact (refuse_ok h).elim
        | some o' =>
          simp only [hlv] at h
          obtain ⟨_, r4, e3, h⟩ := V.bind_ok h
          obtain ⟨_, r5, e4, h⟩ := V.bind_ok h
          have hp := V.pure_ok h; injection hp with hp _; injection hp with h1 h2; subst h1 h2
          have m := lookupByteVar_mem hlv
          obtain ⟨base', len', hr', _, _, h4⟩ := H.bytes v0 r o' m
          rw [hreg] at hr'; injection hr' with hr'; injection hr' with hb1 hb2; subst hb1 hb2
          have g3 := entail_sound e3 ρ H.facts
          have g4 := entail_sound e4 ρ H.facts
          simp only [ev_sub] at g3 g4
          have heq : ev ρ o = ev ρ o' := by omega
          refine ⟨ρ, Carried.here H wf, bounded_var (wf.bytes v0 r o' m).1, base, len, rfl, g1, by omega, ?_⟩
          rw [ev_var, heq]; exact h4
      | none =>
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      let ρ' : Nat → Int := fun k => if k = s.nvars then (s0.mem (s0.reg base + (ev ρ o).toNat) : Int) else ρ k
      have ag : Agree s.nvars ρ ρ' := fun k hk => by
        show ρ k = if k = s.nvars then _ else ρ k
        rw [if_neg (by omega)]
      have H' := H.agree wf ag
      have eo : ev ρ' o = ev ρ o := (ev_agree hb ag).symm
      have new : ρ' s.nvars = (s0.mem (s0.reg base + (ev ρ o).toNat) : Int) := by
        show (if s.nvars = s.nvars then _ else ρ s.nvars) = _
        rw [if_pos rfl]
      have le : s.nvars ≤ s.nvars + 1 := Nat.le_succ _
      refine ⟨ρ', ⟨ag, le, ?_, ?_⟩, bounded_var (Nat.lt_succ_self _), base, len, rfl, by rw [eo]; exact g1, by rw [eo]; omega, ?_⟩
      · exact {
          range := H'.range
          vecIntact := H'.vecIntact
          entry := H'.entry, data := H'.data, reg := H'.reg, small := H'.small, zf := H'.zf, cf := H'.cf, frame := H'.frame, frameW := H'.frameW,
          spec := H'.spec, mem := H'.mem, wrote := H'.wrote, words := H'.words, known := H'.known,
          facts := by
            intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | rfl | hf
            · rw [holds_iff, ev_var, new]; exact Int.natCast_nonneg _
            · rw [holds_iff, ev_sub, ev_const, ev_var, new]
              have := E.byte (List.mem_of_getElem? hreg) (ev ρ o).toNat (by omega)
              omega
            · exact H'.facts f hf
          bytes := by
            intro v1 r1 o1 hm
            simp only [List.mem_cons] at hm
            rcases hm with heq | hm
            · injection heq with h1 h2
              injection h2 with h2 h3
              subst h1 h2 h3
              exact ⟨base, len, hreg, by rw [eo]; exact g1, by rw [eo]; omega, by rw [new, eo]⟩
            · exact H'.bytes v1 r1 o1 hm }
      · exact {
          range := fun rg hr => ⟨bounded_mono le (wf.range rg hr).1, fun v hv => SVal.bounded_mono le ((wf.range rg hr).2 v hv)⟩
          base := Nat.le_trans wf.base le
          reg := fun r hr => bounded_mono le (wf.reg r hr)
          zf := Flag.bounded_mono le wf.zf
          cf := Flag.bounded_mono le wf.cf
          frame := fun o v m => bounded_mono le (wf.frame o v m)
          frameW := wf.frameW
          spec := fun f m => SFact.bounded_mono le (wf.spec f m)
          wrote := fun w o x m => ⟨bounded_mono le (wf.wrote w o x m).1, bounded_mono le (wf.wrote w o x m).2⟩
          words := wf.words.mono rfl rfl rfl le
          known := fun k m => Known.wf_mono le (Nat.le_refl _) (wf.known k m)
          facts := by
            intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | rfl | hf
            · exact bounded_var (Nat.lt_succ_self _)
            · exact bounded_sub (bounded_const _ _) (bounded_var (Nat.lt_succ_self _))
            · exact bounded_mono le (wf.facts f hf)
          bytes := by
            intro v1 r1 o1 hm
            simp only [List.mem_cons] at hm
            rcases hm with heq | hm
            · injection heq with h1 h2
              injection h2 with h2 h3
              subst h1 h2 h3
              exact ⟨Nat.lt_succ_self _, bounded_mono le hb⟩
            · exact ⟨Nat.lt_of_lt_of_le (wf.bytes v1 r1 o1 hm).1 le, bounded_mono le (wf.bytes v1 r1 o1 hm).2⟩ }
      · rw [ev_var, new, eo]

/-! ## The value of an effect's expression -/

/-- What a value on symbols says of the number `x` the machine works out. -/
def EV.sem (ρ : Nat → Int) (n : Nat) (x : Nat) : EV → Prop
  | .lin r => x < M64 ∧ (x : Int) = ev ρ r ∧ bounded n r
  | .equal a b => x = (if ev ρ a = ev ρ b then 1 else 0) ∧ bounded n a ∧ bounded n b
  | .below a b => x = (if ev ρ a < ev ρ b then 1 else 0) ∧ bounded n a ∧ bounded n b

theorem EV.sem_agree {ρ ρ' : Nat → Int} {n m x : Nat} {v : EV} (h : EV.sem ρ n x v) (a : Agree n ρ ρ') (le : n ≤ m) : EV.sem ρ' m x v := by
  cases v with
  | lin r => exact ⟨h.1, by rw [← ev_agree h.2.2 a]; exact h.2.1, bounded_mono le h.2.2⟩
  | equal x y => exact ⟨by rw [← ev_agree h.2.1 a, ← ev_agree h.2.2 a]; exact h.1, bounded_mono le h.2.1, bounded_mono le h.2.2⟩
  | below x y => exact ⟨by rw [← ev_agree h.2.1 a, ← ev_agree h.2.2 a]; exact h.1, bounded_mono le h.2.1, bounded_mono le h.2.2⟩

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] : ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (a', b') :: rest, a, b, h => by
    simp only [List.lookup] at h
    split at h
    next e =>
      injection h with h; subst h
      have : a = a' := by simpa using e
      subst this
      exact List.mem_cons_self ..
    next => exact List.mem_cons_of_mem _ (lookup_mem h)

theorem findRegion_spec {addr : Row} : ∀ {l : List (Nat × Nat)} {k : Nat} {w : Where}, findRegion addr l k = some w →
    ∃ r o base len, w = .region r o ∧ k ≤ r ∧ l[r - k]? = some (base, len) ∧ o = Lin.sub addr (Lin.var base)
  | [], _, _, h => by simp [findRegion] at h
  | (base, len) :: more, k, w, h => by
    simp only [findRegion] at h
    split at h
    next =>
      injection h with h; subst h
      exact ⟨k, _, base, len, rfl, Nat.le_refl _, by simp, rfl⟩
    next =>
      obtain ⟨r, o, b, l, hw, hk, hr, ho⟩ := findRegion_spec h
      refine ⟨r, o, b, l, hw, by omega, ?_, ho⟩
      have : r - k = (r - (k + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]; exact hr

theorem findOut_spec {addr : Row} : ∀ {l : List (String × Nat × Nat)} {k : Nat} {w : Where}, findOut addr l k = some w →
    ∃ r o name base n, w = .out r o ∧ k ≤ r ∧ l[r - k]? = some (name, base, n) ∧ o = Lin.sub addr (Lin.var base)
  | [], _, _, h => by simp [findOut] at h
  | (name, base, n) :: more, k, w, h => by
    simp only [findOut] at h
    split at h
    next =>
      injection h with h; subst h
      exact ⟨k, _, name, base, n, rfl, Nat.le_refl _, by simp, rfl⟩
    next =>
      obtain ⟨r, o, nm, b, n', hw, hk, hr, ho⟩ := findOut_spec h
      refine ⟨r, o, nm, b, n', hw, by omega, ?_, ho⟩
      have : r - k = (r - (k + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]; exact hr

theorem outsIn_mem : ∀ (args : List (String × Kind)) (regs : List Nat) (x : String) (r n : Nat),
    (x, r, n) ∈ outsIn args regs → r ∈ regs
  | [], _, _, _, _, h => by simp [outsIn] at h
  | _ :: _, [], _, _, _, h => by simp [outsIn] at h
  | (name, .out k) :: args, reg :: regs, x, r, n, h => by
    simp only [outsIn, List.mem_cons] at h
    rcases h with e | h
    · injection e with _ e; injection e with e _; rw [e]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (outsIn_mem args regs x r n h)
  | (name, .number) :: args, reg :: regs, x, r, n, h => by
    simp only [outsIn] at h
    exact List.mem_cons_of_mem _ (outsIn_mem args regs x r n h)
  | (name, .bytes _) :: args, reg :: regs, x, r, n, h => by
    simp only [outsIn] at h
    exact List.mem_cons_of_mem _ (outsIn_mem args regs x r n h)
  | (name, .fixed _) :: args, reg :: regs, x, r, n, h => by
    simp only [outsIn] at h
    exact List.mem_cons_of_mem _ (outsIn_mem args regs x r n h)
  | (name, .inout k) :: args, reg :: regs, x, r, n, h => by
    simp only [outsIn, List.mem_cons] at h
    rcases h with e | h
    · injection e with _ e; injection e with e _; rw [e]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (outsIn_mem args regs x r n h)
  | (name, .valArray _ _ _) :: args, reg :: regs, x, r, n, h => by
    simp only [outsIn] at h
    exact List.mem_cons_of_mem _ (outsIn_mem args regs x r n h)

theorem outs_lt {c : Contract} {x : String} {r n : Nat} (h : (x, r, n) ∈ c.outs) : r < c.regs :=
  argRegs_lt (outsIn_mem c.args c.argRegs x r n h)

/-- What `keepWrote` keeps was known before, and is of another run or of another place of this run. -/
theorem keepWrote_spec {w : Nat} {o : Row} : ∀ {l rest : List (Nat × Row × Row)}, keepWrote w o l = some rest →
    ∀ w' o' x', (w', o', x') ∈ rest → (w', o', x') ∈ l ∧ (w' ≠ w ∨ w' = w ∧ ∃ k, Lin.isConst (Lin.sub o o') = some k ∧ k ≠ 0)
  | [], rest, h => by
    simp only [keepWrote] at h
    injection h with h; subst h
    intro _ _ _ m; cases m
  | (w1, o1, x1) :: more, rest, h => by
    simp only [keepWrote] at h
    cases hr : keepWrote w o more with
    | none => simp [hr] at h
    | some rest' =>
      simp only [hr] at h
      have ih := keepWrote_spec hr
      intro w' o' x' m
      split at h
      next ne =>
        injection h with h; subst h
        rcases List.mem_cons.mp m with e | m
        · injection e with e1 e2; injection e2 with e2 e3; subst e1 e2 e3
          exact ⟨List.mem_cons_self .., Or.inl ne⟩
        · exact ⟨List.mem_cons_of_mem _ (ih w' o' x' m).1, (ih w' o' x' m).2⟩
      next eq =>
        have eq : w1 = w := Decidable.of_not_not eq
        split at h
        next k hk =>
          split at h
          next k0 => injection h with h; subst h; exact ⟨List.mem_cons_of_mem _ (ih w' o' x' m).1, (ih w' o' x' m).2⟩
          next kne =>
            injection h with h; subst h
            rcases List.mem_cons.mp m with e | m
            · injection e with e1 e2; injection e2 with e2 e3; subst e1 e2 e3
              exact ⟨List.mem_cons_self .., Or.inr ⟨eq, k, hk, kne⟩⟩
            · exact ⟨List.mem_cons_of_mem _ (ih w' o' x' m).1, (ih w' o' x' m).2⟩
        next => cases h

theorem locate_frame {ctx : Ctx} {addr : Row} {c : Int} (h : locate ctx addr = some (.frame c)) :
    Lin.isConst (Lin.sub addr (Lin.var RSP)) = some c := by
  cases hk : Lin.isConst (Lin.sub addr (Lin.var RSP)) with
  | some c' => simp only [locate, hk] at h; injection h with h; injection h with h; rw [h]
  | none =>
    cases hd : dataOff ctx addr with
    | some c' => simp only [locate, hk, hd] at h; injection h with h; cases h
    | none =>
      simp only [locate, hk, hd] at h
      cases hf : findRegion addr ctx.contract.regions 0 with
      | some w =>
        simp only [hf] at h
        obtain ⟨r, o, b, l, hw, _⟩ := findRegion_spec hf
        injection h with h; rw [hw] at h; cases h
      | none =>
        simp only [hf] at h
        obtain ⟨r, o, nm, b, n, hw, _⟩ := findOut_spec h
        cases hw

theorem locate_region {ctx : Ctx} {addr : Row} {r : Nat} {o : Row} (h : locate ctx addr = some (.region r o)) :
    ∃ base len, ctx.contract.regions[r]? = some (base, len) ∧ o = Lin.sub addr (Lin.var base) := by
  cases hk : Lin.isConst (Lin.sub addr (Lin.var RSP)) with
  | some c' => simp only [locate, hk] at h; injection h with h; cases h
  | none =>
    cases hd : dataOff ctx addr with
    | some c' => simp only [locate, hk, hd] at h; injection h with h; cases h
    | none =>
      simp only [locate, hk, hd] at h
      cases hf : findRegion addr ctx.contract.regions 0 with
      | some w =>
        simp only [hf] at h
        injection h with h
        subst h
        obtain ⟨r', o', b, l, hw, _, hr, ho⟩ := findRegion_spec hf
        injection hw with h1 h2
        subst h1 h2
        exact ⟨b, l, by simpa using hr, ho⟩
      | none =>
        simp only [hf] at h
        obtain ⟨r', o', nm, b, n, hw, _⟩ := findOut_spec h
        cases hw

theorem locate_out {ctx : Ctx} {addr : Row} {w : Nat} {o : Row} (h : locate ctx addr = some (.out w o)) :
    ∃ name base n, ctx.contract.outs[w]? = some (name, base, n) ∧ o = Lin.sub addr (Lin.var base) := by
  cases hk : Lin.isConst (Lin.sub addr (Lin.var RSP)) with
  | some c' => simp only [locate, hk] at h; injection h with h; cases h
  | none =>
    cases hd : dataOff ctx addr with
    | some c' => simp only [locate, hk, hd] at h; injection h with h; cases h
    | none =>
      simp only [locate, hk, hd] at h
      cases hf : findRegion addr ctx.contract.regions 0 with
      | some w' =>
        simp only [hf] at h
        injection h with h
        subst h
        obtain ⟨r', o', b, l, hw, _⟩ := findRegion_spec hf
        cases hw
      | none =>
        simp only [hf] at h
        obtain ⟨r', o', nm, b, n, hw, _, hr, ho⟩ := findOut_spec h
        injection hw with h1 h2
        subst h1 h2
        exact ⟨nm, b, n, by simpa using hr, ho⟩

/-- An address the verifier places in the file's data: the function's file has data, and the address is the
unknown that is the data's address, plus that number. -/
theorem locate_data {ctx : Ctx} {addr : Row} {c : Int} (h : locate ctx addr = some (.data c)) :
    ctx.data ≠ [] ∧ Lin.isConst (Lin.sub addr (Lin.var (dataVar ctx))) = some c := by
  cases hk : Lin.isConst (Lin.sub addr (Lin.var RSP)) with
  | some c' => simp only [locate, hk] at h; injection h with h; cases h
  | none =>
    cases hd : dataOff ctx addr with
    | some c' =>
      simp only [locate, hk, hd] at h
      injection h with h; injection h with h; subst h
      unfold dataOff at hd
      split at hd
      · cases hd
      next he => exact ⟨fun e => he (by rw [e]; rfl), hd⟩
    | none =>
      simp only [locate, hk, hd] at h
      cases hf : findRegion addr ctx.contract.regions 0 with
      | some w =>
        simp only [hf] at h
        obtain ⟨r, o, b, l, hw, _⟩ := findRegion_spec hf
        injection h with h; rw [hw] at h; cases h
      | none =>
        simp only [hf] at h
        obtain ⟨r, o, nm, b, n, hw, _⟩ := findOut_spec h
        cases hw

theorem inFrame_spec {ctx : Ctx} {s : Sym} {c : Int} (h : inFrame ctx s c = true) :
    ∃ sp, s.sp = some sp ∧ sp ≤ c ∧ c + 8 ≤ 0 ∧ -(ctx.contract.stack : Int) ≤ c := by
  unfold inFrame at h
  split at h
  next sp hsp =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨sp, hsp, h.1.1, h.1.2, h.2⟩
  next => contradiction

theorem pow8 : (256 : Nat) ^ 8 = M64 := by decide

/-- Eight bytes of the frame, at `c` from where the stack pointer was at entry: where they are, and that the
function may read and write them. -/
theorem frame_address {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {c : Int}
    (h1 : -(ctx.contract.stack : Int) ≤ c) (h2 : c + 8 ≤ 0) (a : Nat) (ha : (a : Int) = (s0.reg RSP : Int) + c) :
    allowed (ctx.contract.perm ctx.pieces s0).read a 8 = true ∧ allowed (ctx.contract.perm ctx.pieces s0).write a 8 = true ∧
    ((s0.reg RSP : Int) + c).toNat = a := by
  have hs := E.stack
  have hle := Contract.stack_le_stackAt ctx.contract s0
  refine ⟨allowed_of _ _ _ ?_, allowed_of _ _ _ ?_, by omega⟩
  · intro x hx1 hx2
    simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    left; left; left; left; left; left; omega
  · intro x hx1 hx2
    simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    left; omega

/-! ## Runs of a fixed count -/

namespace Setting
variable {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0)
include E
/-- A run of a fixed count given to read: in memory, apart from the frame and the address to return to,
holding bytes, and apart from every run given to write. -/
theorem fixedAt {x : String} {r n : Nat} (h : (x, r, n) ∈ ctx.contract.fixeds) :
    s0.reg r + n ≤ M64 ∧ (s0.reg r + n ≤ s0.reg RSP - ctx.contract.stackAt s0 ∨ s0.reg RSP + ctx.contract.slot ≤ s0.reg r) ∧
    (∀ k, k < n → (s0.mem (s0.reg r + k)).val < 256) ∧
    ∀ x' r' n', (x', r', n') ∈ ctx.contract.outs → s0.reg r + n ≤ s0.reg r' ∨ s0.reg r' + n' ≤ s0.reg r :=
  have h' := E.pre.2.2.2.2.2.2.2.2.1 x r n h
  ⟨h'.1, h'.2.1, fun _ _ => (s0.mem _).isLt, h'.2.2⟩
theorem fixed {x : String} {r n : Nat} (h : (x, r, n) ∈ ctx.contract.fixeds) :
    s0.reg r + n ≤ M64 ∧ (s0.reg r + n ≤ s0.reg RSP - ctx.contract.stack ∨ s0.reg RSP + ctx.contract.slot ≤ s0.reg r) ∧
    (∀ k, k < n → (s0.mem (s0.reg r + k)).val < 256) ∧
    ∀ x' r' n', (x', r', n') ∈ ctx.contract.outs → s0.reg r + n ≤ s0.reg r' ∨ s0.reg r' + n' ≤ s0.reg r := by
  obtain ⟨h1, h2, h3, h4⟩ := E.fixedAt h
  have hle := Contract.stack_le_stackAt ctx.contract s0
  exact ⟨h1, h2.elim (fun ha => Or.inl (by omega)) Or.inr, h3, h4⟩
theorem inoutByte {x : String} {r n : Nat} (h : (x, r, n) ∈ ctx.contract.inouts) {k : Nat} (hk : k < n) :
    (s0.mem (s0.reg r + k)).val < 256 := (s0.mem _).isLt

/-- A number the contract bounds is below its bound at entry. -/
theorem bound {x : String} {b r : Nat}
    (h : (x, b) ∈ ctx.contract.bounds) (hr : ctx.contract.regOf x = some r) : s0.reg r < b :=
  E.pre.2.2.2.2.2.2.2.2.2.1 x b h r hr

/-- A number in memory the contract bounds (the eight bytes at a place of a run given to read) is below its
bound at entry. -/
theorem mbound {x : String} {off b r n : Nat}
    (h : (x, off, b) ∈ ctx.contract.mbounds) (hf : (x, r, n) ∈ ctx.contract.fixeds) : load s0.mem (s0.reg r + off) 8 < b :=
  E.pre.2.2.2.2.2.2.2.2.2.2.1 x off b h r n hf

/-- The blocks an address of a table points to: in memory, apart from the frame and the address to return
to, holding bytes, and apart from every run given to write. -/
theorem laneAt {j : Nat} {x : String} {r count l : Nat} (h : ctx.contract.tableAt j = some (x, r, count, l)) {i : Nat} (hi : i < count) :
    lanePtr s0 r i + 64 * s0.reg l ≤ M64 ∧
    (lanePtr s0 r i + 64 * s0.reg l ≤ s0.reg RSP - ctx.contract.stackAt s0 ∨ s0.reg RSP + ctx.contract.slot ≤ lanePtr s0 r i) ∧
    (∀ k, k < 64 * s0.reg l → (s0.mem (lanePtr s0 r i + k)).val < 256) ∧
    ∀ x' r' n', (x', r', n') ∈ ctx.contract.outs → lanePtr s0 r i + 64 * s0.reg l ≤ s0.reg r' ∨ s0.reg r' + n' ≤ lanePtr s0 r i :=
  have h' := E.pre.2.2.2.2.2.2.2.2.2.2.2.1 j x r count l h i hi
  ⟨h'.1, h'.2.1, fun _ _ => (s0.mem _).isLt, h'.2.2⟩
theorem lane {j : Nat} {x : String} {r count l : Nat} (h : ctx.contract.tableAt j = some (x, r, count, l)) {i : Nat} (hi : i < count) :
    lanePtr s0 r i + 64 * s0.reg l ≤ M64 ∧
    (lanePtr s0 r i + 64 * s0.reg l ≤ s0.reg RSP - ctx.contract.stack ∨ s0.reg RSP + ctx.contract.slot ≤ lanePtr s0 r i) ∧
    (∀ k, k < 64 * s0.reg l → (s0.mem (lanePtr s0 r i + k)).val < 256) ∧
    ∀ x' r' n', (x', r', n') ∈ ctx.contract.outs → lanePtr s0 r i + 64 * s0.reg l ≤ s0.reg r' ∨ s0.reg r' + n' ≤ lanePtr s0 r i := by
  obtain ⟨h1, h2, h3, h4⟩ := E.laneAt h hi
  have hle := Contract.stack_le_stackAt ctx.contract s0
  exact ⟨h1, h2.elim (fun ha => Or.inl (by omega)) Or.inr, h3, h4⟩

/-- A number the contract asks to be no less than another is so at entry. -/
theorem atLeast {x : String} {k r : Nat} (h : (x, k) ∈ ctx.contract.atLeast) (hr : ctx.contract.regOf x = some r) : k ≤ s0.reg r :=
  E.pre.2.2.2.2.2.2.2.2.2.2.2.2.1 x k h r hr
/-- On AArch64 the stack pointer is a multiple of 16 at entry. -/
theorem aligned (h : ctx.contract.arm64 = true) : s0.reg RSP % 16 = 0 := E.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h
/-- Each multi-variable linear entry precondition holds at entry. -/
theorem preLine {k : Int} {ts : List (String × Int)} (h : (k, ts) ∈ ctx.contract.preLines) :
    0 ≤ preLineVal ctx.contract s0 k ts := E.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k ts h
/-- Each read-only `valArray` lies below 2^64, apart from the frame and every output run. -/
theorem valArray {x : String} {r l ch el : Nat} (h : (x, r, l, ch, el) ∈ ctx.contract.valArrays) :
    s0.reg r + el * (s0.reg l / ch) < M64 ∧
    (s0.reg r + el * (s0.reg l / ch) ≤ s0.reg RSP - ctx.contract.stackAt s0 ∨ s0.reg RSP + ctx.contract.slot ≤ s0.reg r) ∧
    ∀ x' r' n', (x', r', n') ∈ ctx.contract.outs → s0.reg r + el * (s0.reg l / ch) ≤ s0.reg r' ∨ s0.reg r' + n' ≤ s0.reg r :=
  E.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 x r l ch el h
/-- The read-only data of the function's own file, where it has any, ends below 2^64. -/
theorem data_fits (hd : ctx.data ≠ []) : ctx.own s0 + ctx.data.length < M64 := by
  obtain ⟨k, pc, hk, hq, e⟩ := Ctx.data_piece hd
  rw [Ctx.own_eq hk, e]
  exact (E.loaded k pc hq).1
/-- An address in the data of the function's own file is in the read-only data of the program. -/
theorem data_in (hd : ctx.data ≠ []) {a : Nat} (h1 : ctx.own s0 ≤ a) (h2 : a < ctx.own s0 + ctx.data.length) :
    inPieces ctx.pieces s0 a = true := by
  obtain ⟨k, pc, hk, hq, e⟩ := Ctx.data_piece hd
  rw [Ctx.own_eq hk] at h1 h2
  rw [e] at h2
  exact inPieces_iff.mpr ⟨k, pc, hq, h1, h2⟩
/-- An address in the file's data is not in the frame. -/
theorem data_notFrame (hd : ctx.data ≠ []) {a : Nat} (h1 : ctx.own s0 ≤ a) (h2 : a < ctx.own s0 + ctx.data.length) :
    ctx.contract.inFrame s0 a = false := (E.apart a (E.data_in hd h1 h2)).1
/-- An address in the file's data is in no run given to write. -/
theorem data_notOut (hd : ctx.data ≠ []) {a : Nat} (h1 : ctx.own s0 ≤ a) (h2 : a < ctx.own s0 + ctx.data.length) :
    ctx.contract.inOut s0 a = false := (E.apart a (E.data_in hd h1 h2)).2
/-- At entry each byte of the file's data is in memory where the data lies. -/
theorem data_byte (hd : ctx.data ≠ []) {k : Nat} (hk : k < ctx.data.length) :
    s0.mem (ctx.own s0 + k) = ctx.data.getD k 0 := by
  obtain ⟨j, pc, hj, hq, e⟩ := Ctx.data_piece hd
  have hk' : k < pc.bytes.length := by rw [← e]; exact hk
  rw [Ctx.own_eq hj, (E.loaded j pc hq).2.2 k hk', e]
  simp [List.getD, List.getElem?_eq_getElem hk']
/-- At entry no byte of the file's data is marked. -/
theorem data_quiet (hd : ctx.data ≠ []) {k : Nat} (hk : k < ctx.data.length) :
    s0.marks.mem (ctx.own s0 + k) = false := by
  obtain ⟨j, pc, hj, hq, e⟩ := Ctx.data_piece hd
  have hk' : k < pc.bytes.length := by rw [← e]; exact hk
  rw [Ctx.own_eq hj]
  exact E.dataQuiet j pc hq k hk'
end Setting

theorem fixedsIn_mem : ∀ (args : List (String × Kind)) (regs : List Nat) (x : String) (r n : Nat),
    (x, r, n) ∈ fixedsIn args regs → r ∈ regs
  | [], _, _, _, _, h => by simp [fixedsIn] at h
  | _ :: _, [], _, _, _, h => by simp [fixedsIn] at h
  | (name, .fixed k) :: args, reg :: regs, x, r, n, h => by
    simp only [fixedsIn, List.mem_cons] at h
    rcases h with e | h
    · injection e with _ e; injection e with e _; rw [e]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (fixedsIn_mem args regs x r n h)
  | (name, .number) :: args, reg :: regs, x, r, n, h => by
    simp only [fixedsIn] at h
    exact List.mem_cons_of_mem _ (fixedsIn_mem args regs x r n h)
  | (name, .bytes _) :: args, reg :: regs, x, r, n, h => by
    simp only [fixedsIn] at h
    exact List.mem_cons_of_mem _ (fixedsIn_mem args regs x r n h)
  | (name, .out _) :: args, reg :: regs, x, r, n, h => by
    simp only [fixedsIn] at h
    exact List.mem_cons_of_mem _ (fixedsIn_mem args regs x r n h)
  | (name, .inout _) :: args, reg :: regs, x, r, n, h => by
    simp only [fixedsIn] at h
    exact List.mem_cons_of_mem _ (fixedsIn_mem args regs x r n h)
  | (name, .valArray _ _ _) :: args, reg :: regs, x, r, n, h => by
    simp only [fixedsIn] at h
    exact List.mem_cons_of_mem _ (fixedsIn_mem args regs x r n h)

theorem fixeds_lt {c : Contract} {x : String} {r n : Nat} (h : (x, r, n) ∈ c.fixeds) : r < c.regs :=
  argRegs_lt (fixedsIn_mem c.args c.argRegs x r n h)

theorem valArraysIn_mem (c : Contract) : ∀ (args : List (String × Kind)) (regs : List Nat) (x : String) (r l ch el : Nat),
    (x, r, l, ch, el) ∈ valArraysIn c args regs → r ∈ regs ∧ 0 < ch ∧ 0 < el ∧ el % 4 = 0 ∧ ∃ len, c.regOf len = some l
  | [], _, _, _, _, _, _, h => by simp [valArraysIn] at h
  | _ :: _, [], _, _, _, _, _, h => by simp [valArraysIn] at h
  | (nm, .valArray len ch' el') :: args, reg :: regs, x, r, l, ch, el, h => by
    simp only [valArraysIn] at h
    cases hl : c.regOf len with
    | none => simp only [hl] at h; have := valArraysIn_mem c args regs x r l ch el h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    | some l' =>
      simp only [hl] at h
      split at h
      next hc =>
        simp only [List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl, rfl, rfl, rfl⟩ | h
        · exact ⟨List.mem_cons_self .., hc.1, hc.2.1, hc.2.2, len, hl⟩
        · have := valArraysIn_mem c args regs x r l ch el h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
      next => have := valArraysIn_mem c args regs x r l ch el h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
  | (_, .number) :: args, _ :: regs, x, r, l, ch, el, h
  | (_, .bytes _) :: args, _ :: regs, x, r, l, ch, el, h
  | (_, .out _) :: args, _ :: regs, x, r, l, ch, el, h
  | (_, .fixed _) :: args, _ :: regs, x, r, l, ch, el, h
  | (_, .inout _) :: args, _ :: regs, x, r, l, ch, el, h => by
    simp only [valArraysIn] at h
    have := valArraysIn_mem c args regs x r l ch el h
    exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem valArrays_lt {c : Contract} {x : String} {r l ch el : Nat} (h : (x, r, l, ch, el) ∈ c.valArrays) :
    r < c.regs ∧ l < c.regs ∧ 0 < ch ∧ 0 < el ∧ el % 4 = 0 := by
  obtain ⟨hr, hch, hel, h4, len, hl⟩ := valArraysIn_mem c c.args c.argRegs x r l ch el h
  exact ⟨argRegs_lt hr, argRegs_lt (regOfIn_mem len c.args c.argRegs l hl), hch, hel, h4⟩

theorem knownLoad_mem {j c : Nat} : ∀ {l : List Known} {v : Nat}, knownLoad j c l = some v → Known.load v j c ∈ l
  | [], _, h => by simp [knownLoad] at h
  | k :: more, v, h => by
    cases k with
    | load v' j' c' =>
      simp only [knownLoad] at h
      split at h
      next e =>
        injection h with h
        obtain ⟨e1, e2⟩ := e
        subst h e1 e2
        exact List.mem_cons_self ..
      next => exact List.mem_cons_of_mem _ (knownLoad_mem h)
    | or _ _ _ => simp only [knownLoad] at h; exact List.mem_cons_of_mem _ (knownLoad_mem h)
    | held _ _ _ => simp only [knownLoad] at h; exact List.mem_cons_of_mem _ (knownLoad_mem h)
    | heldB _ _ _ => simp only [knownLoad] at h; exact List.mem_cons_of_mem _ (knownLoad_mem h)
    | div _ _ _ => simp only [knownLoad] at h; exact List.mem_cons_of_mem _ (knownLoad_mem h)
    | block _ _ _ _ => simp only [knownLoad] at h; exact List.mem_cons_of_mem _ (knownLoad_mem h)
    | use _ _ _ => simp only [knownLoad] at h; exact List.mem_cons_of_mem _ (knownLoad_mem h)
    | record _ _ _ => simp only [knownLoad] at h; exact List.mem_cons_of_mem _ (knownLoad_mem h)

/-- Eight bytes read of a run of a fixed count given to read: the number the state knows there. The run is
as it was at entry (the function may not write it), so the number is what `load` reads there at entry. -/
theorem symLoadFixed_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {addr : Row} {size : Nat} {v : EV}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symLoadFixed ctx s addr size items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (a : Nat) (hlt : a < M64) (ha : (a : Int) % 2 ^ 64 = ev ρ addr % 2 ^ 64) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ allowed (ctx.contract.perm ctx.pieces s0).read a size = true ∧ EV.sem ρ' s'.nvars (load st.mem a size) v := by
  unfold symLoadFixed at h
  cases hf : findOut addr ctx.contract.fixeds 0 with
  | none => simp only [hf] at h; exact (refuse_ok h).elim
  | some w =>
    obtain ⟨j, off, name, base, count, hw, _, hj, ho⟩ := findOut_spec hf
    subst hw
    simp only [hf] at h
    have hj' : ctx.contract.fixeds[j]? = some (name, base, count) := by simpa using hj
    cases hc : Lin.isConst off with
    | none => simp only [hc] at h; exact (refuse_ok h).elim
    | some c =>
      simp only [hc, hj'] at h
      split at h
      next hcond =>
        obtain ⟨hsize, c0, cle⟩ := hcond
        subst hsize
        have hm := List.mem_of_getElem? hj'
        have b16 := fixeds_lt hm
        obtain ⟨fit, apart, _, outs⟩ := E.fixedAt hm
        have e := ev_isConst (ρ := ρ) hc
        rw [ho, ev_sub, ev_var, H.entry base b16] at e
        unfold M64 at hlt fit
        have hadr : a = s0.reg base + c.toNat := by omega
        -- the run is as it was at entry
        have same : ∀ x, s0.reg base ≤ x → x < s0.reg base + count → st.mem x = s0.mem x := by
          intro x h1 h2
          apply H.mem
          · simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]
            omega
          · unfold Contract.inOut
            rw [List.any_eq_false]
            intro ⟨x', r', n'⟩ hm'
            have := outs x' r' n' hm'
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            omega
        have hload : load st.mem a 8 = load s0.mem (s0.reg base + c.toNat) 8 := by
          rw [hadr]
          exact load_congr _ _ _ _ fun x h1 h2 => same x (by omega) (by omega)
        have hread : allowed (ctx.contract.perm ctx.pieces s0).read a 8 = true := by
          apply allowed_of
          intro x h1 h2
          simp only [Contract.perm, Contract.inFixed, Bool.or_eq_true]
          left; left; left; right; left
          exact List.any_eq_true.mpr ⟨(name, base, count), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        have lt := load_lt s0.mem (s0.reg base + c.toNat) 8
        have lt2 : load s0.mem (s0.reg base + c.toNat) 8 < 2 ^ 64 := by have := lt; rw [pow8] at this; unfold M64 at this; exact this
        rw [pow8] at lt
        cases hk : knownLoad j c.toNat s.known with
        | some v0 =>
          simp only [hk] at h
          have := V.pure_ok h
          injection this with hp _
          injection hp with h1 h2
          subst h1 h2
          have m := knownLoad_mem hk
          obtain ⟨x', r', n', g1, _, g3⟩ := H.known _ m
          rw [hj'] at g1
          injection g1 with g1; injection g1 with _ g1; injection g1 with g1 _
          subst g1
          exact ⟨ρ, Carried.here H wf, hread, by rw [hload]; exact lt, by rw [ev_var, g3, hload], bounded_var (wf.known _ m)⟩
        | none =>
          simp only [hk] at h
          have := V.pure_ok h
          injection this with hp _
          injection hp with h1 h2
          subst h1 h2
          have new := extend_new ρ s.nvars (load s0.mem (s0.reg base + c.toNat) 8 : Nat)
          have bv : bounded (s.nvars + 1) (Lin.var s.nvars) := bounded_var (Nat.lt_succ_self _)
          refine ⟨_, Carried.fresh H wf (load s0.mem (s0.reg base + c.toNat) 8 : Nat) _ (.load s.nvars j c.toNat) ?_ (Nat.lt_succ_self _) ?_
            ⟨name, base, count, hj', by omega, new⟩, hread, by rw [hload]; exact lt, by rw [ev_var, new, hload], bv⟩
          · intro f m
            rcases List.mem_append.mp m with m | m
            · simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at m
              rcases m with rfl | rfl
              · exact bv
              · exact bounded_sub (bounded_const _ _) bv
            · obtain ⟨⟨x, o, b⟩, _, e⟩ := List.mem_filterMap.mp m
              split at e
              · injection e with e; subst e
                exact bounded_sub (bounded_const _ _) bv
              · cases e
          · intro f m
            rcases List.mem_append.mp m with m | m
            · simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at m
              rcases m with rfl | rfl
              · rw [holds_iff, ev_var, new]; exact Int.natCast_nonneg _
              · rw [holds_iff, ev_sub, ev_const, ev_var, new]; simp only [top]; omega
            · obtain ⟨⟨x, o, b⟩, mb, e⟩ := List.mem_filterMap.mp m
              split at e
              next hx =>
                injection e with e; subst e
                obtain ⟨hx1, hx2⟩ := hx
                have hx1' : x = name := by simpa using hx1
                subst hx1' hx2
                have := E.mbound mb hm
                rw [holds_iff, ev_sub, ev_const, ev_var, new]
                omega
              next => cases e
      next => exact (refuse_ok h).elim

/-- An address the verifier places in the file's data, some bytes from it lying within the data: the
machine's address is the data's address plus that number. -/
theorem dataAddr {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) {addr : Row} {c : Int} {size : Nat}
    (hl : locate ctx addr = some (.data c)) (h0 : 0 ≤ c) (h1 : c + size ≤ ctx.data.length)
    {a : Nat} (hlt : a < M64) (ha : (a : Int) % 2 ^ 64 = ev ρ addr % 2 ^ 64) :
    ctx.data ≠ [] ∧ a = ctx.own s0 + c.toNat := by
  obtain ⟨hd, hc⟩ := locate_data hl
  have e := ev_isConst (ρ := ρ) hc
  rw [ev_sub, ev_var] at e
  have pin : ρ (dataVar ctx) = ctx.own s0 := H.data.1
  have fit := E.data_fits hd
  unfold M64 at hlt fit
  refine ⟨hd, ?_⟩
  omega

theorem readBytes_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {r base len : Nat}
    (hreg : ctx.contract.regions[r]? = some (base, len)) :
    ∀ (n : Nat) {s s' : Sym} {o v : Row} {items rest : Items} {ρ : Nat → Int} {st : State},
    readBytes ctx s r o n items = .ok ((v, s'), rest) →
    Holds ctx s0 ρ s st → WF ctx s → bounded s.nvars o →
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ bounded s'.nvars v ∧
      (∀ k, k < n → 0 ≤ ev ρ' o + k ∧ ev ρ' o + k < s0.reg len) ∧
      (0 < n → ev ρ' v = load s0.mem (s0.reg base + (ev ρ' o).toNat) n) ∧
      (n = 0 → ev ρ' v = 0)
  | 0, s, s', o, v, items, rest, ρ, st, h, H, wf, _ => by
    simp only [readBytes] at h
    have hp := V.pure_ok h; injection hp with hp _; injection hp with hv hs; subst hv hs
    exact ⟨ρ, Carried.here H wf, bounded_const _ _, fun _ hk => by omega, fun hk => by omega, fun _ => ev_const _ _⟩
  | n + 1, s, s', o, v, items, rest, ρ, st, h, H, wf, hbo => by
    simp only [readBytes] at h
    obtain ⟨⟨b, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨⟨hi, s2⟩, r2, e2, h⟩ := V.bind_ok h
    have hp := V.pure_ok h; injection hp with hp _; injection hp with hv hs; subst hv hs
    obtain ⟨ρ1, c1, hbb, base1, len1, hreg1, g1, g2, g3⟩ := readByte_sound E e1 H wf hbo
    rw [hreg] at hreg1; injection hreg1 with hreg1; injection hreg1 with hb1 hl1; subst hb1 hl1
    have hbo1 : bounded s1.nvars (Lin.add o (Lin.const 1)) :=
      bounded_add (bounded_mono c1.mono hbo) (bounded_const _ _)
    obtain ⟨ρ2, c2, hbhi, hbounds, hloadn, hz⟩ := readBytes_sound E hreg n e2 c1.holds c1.wf hbo1
    have c12 := Carried.then c1 c2
    have eo12 : ev ρ2 o = ev ρ1 o := (ev_agree (bounded_mono c1.mono hbo) c2.agree).symm
    have eo1 : ev ρ2 (Lin.add o (Lin.const 1)) = ev ρ2 o + 1 := by rw [ev_add, ev_const]
    have eb12 : ev ρ2 b = ev ρ1 b := (ev_agree hbb c2.agree).symm
    have hbv : bounded s'.nvars (Lin.add b (Lin.scale 256 hi)) :=
      bounded_add (bounded_mono c2.mono hbb) (bounded_scale _ hbhi)
    refine ⟨ρ2, c12, hbv, ?_, ?_, fun h0 => by omega⟩
    · intro k hk
      cases k with
      | zero => rw [eo12]; omega
      | succ k' =>
        have hk' := hbounds k' (by omega)
        rw [eo1] at hk'; omega
    · intro _
      rw [ev_add, ev_scale, eb12, g3, ← eo12]
      cases n with
      | zero =>
        rw [hz rfl]
        simp only [load, Nat.mul_zero, Nat.add_zero, Int.mul_zero, Int.add_zero]
      | succ m =>
        have hl := hloadn (by omega)
        rw [hl, eo1]
        have hpos : 0 ≤ ev ρ2 o := by rw [eo12]; exact g1
        have hidx : s0.reg base + (ev ρ2 o + 1).toNat = s0.reg base + (ev ρ2 o).toNat + 1 := by omega
        rw [hidx]
        have hld : load s0.mem (s0.reg base + (ev ρ2 o).toNat) (m + 2) =
            (s0.mem (s0.reg base + (ev ρ2 o).toNat)).val + 256 * load s0.mem (s0.reg base + (ev ρ2 o).toNat + 1) (m + 1) := rfl
        rw [hld, Int.natCast_add, Int.natCast_mul]
        rfl

theorem symLoad_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {addr : Row} {size : Nat} {v : EV}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symLoad ctx s addr size items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hb : bounded s.nvars addr)
    (a : Nat) (hlt : a < M64) (ha : (a : Int) % 2 ^ 64 = ev ρ addr % 2 ^ 64) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ allowed (ctx.contract.perm ctx.pieces s0).read a size = true ∧ EV.sem ρ' s'.nvars (load st.mem a size) v := by
  have hstack := E.stack
  have habove := E.above
  have hrsp : ρ RSP = s0.reg RSP := H.entry RSP ctx.rsp_lt
  unfold M64 at hlt habove
  cases hl : locate ctx addr with
  | none =>
    simp only [symLoad, hl] at h
    exact symLoadFixed_sound E h H wf a (by unfold M64; exact hlt) ha
  | some w =>
    cases w with
    | out _ _ => simp only [symLoad, hl] at h; exact (refuse_ok h).elim
    | data c =>
      -- the file's read-only data: memory there is as at entry, and at entry it holds the file's bytes
      simp only [symLoad, hl] at h
      split at h
      next hok =>
        obtain ⟨hsize, h0, h1⟩ := hok
        have := V.pure_ok h
        injection this with hp _
        injection hp with hv hs
        subst hv hs
        obtain ⟨hd, hadr⟩ := dataAddr E H hl h0 h1 (by unfold M64; exact hlt) ha
        have hload : load st.mem a size = dataWord ctx.data c.toNat size := by
          rw [hadr]
          unfold dataWord
          exact load_list _ _ size _ _ fun k hk => by
            rw [H.mem _ (E.data_notFrame hd (by omega) (by omega)) (E.data_notOut hd (by omega) (by omega))]
            rw [Nat.add_assoc]
            exact E.data_byte hd (by omega)
        refine ⟨ρ, Carried.here H wf, allowed_of _ _ _ (fun x x1 x2 => ?_), ?_, ?_, bounded_const _ _⟩
        · simp only [Contract.perm, Bool.or_eq_true]
          right
          exact E.data_in hd (by omega) (by omega)
        · rw [hload]
          have lt := load_lt (fun x => ⟨ctx.data.getD x 0 % 256, Nat.mod_lt _ (by decide)⟩) c.toNat size
          have le : 256 ^ size ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
          unfold dataWord M64
          have e8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
          omega
        · rw [hload, ev_const]
      next => exact (refuse_ok h).elim
    | frame c =>
      simp only [symLoad, hl] at h
      split at h
      next hc =>
        obtain ⟨hsize, hin⟩ := hc
        subst hsize
        obtain ⟨sp, _, _, h8, hst⟩ := inFrame_spec hin
        have e := ev_isConst (ρ := ρ) (locate_frame hl)
        simp only [ev_sub, ev_var, hrsp] at e
        have hadr : (a : Int) = (s0.reg RSP : Int) + c := by omega
        obtain ⟨hr, _, hn⟩ := frame_address E hst h8 a hadr
        cases hf : s.frame.lookup c with
        | none => simp only [hf] at h; exact (refuse_ok h).elim
        | some v0 =>
          simp only [hf] at h
          have := V.pure_ok h
          injection this with hp _
          injection hp with h1 h2
          subst h1 h2
          have m := lookup_mem hf
          obtain ⟨_, _, hv⟩ := H.frame c v0 m
          rw [hn] at hv
          have lt := load_lt st.mem a 8
          rw [pow8] at lt
          exact ⟨ρ, Carried.here H wf, hr, lt, hv, wf.frame c v0 m⟩
      next => exact (refuse_ok h).elim
    | region r o =>
      simp only [symLoad, hl] at h
      obtain ⟨base, len, hreg, ho⟩ := locate_region hl
      have hmem := List.mem_of_getElem? hreg
      have hbl := regions_lt hmem
      split at h
      next hsize =>
        subst hsize
        obtain ⟨⟨v0, s1⟩, r1, e1, h⟩ := V.bind_ok h
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        have hbo : bounded s.nvars o := by
          rw [ho]; exact bounded_sub hb (bounded_var (Nat.lt_of_lt_of_le hbl.1 wf.regs))
        obtain ⟨ρ', c1, bv, base', len', hreg', g1, g2, g3⟩ := readByte_sound E e1 H wf hbo
        rw [hreg] at hreg'
        injection hreg' with hreg'
        injection hreg' with hb1 hb2
        subst hb1 hb2
        have eo : ev ρ' o = ev ρ addr - s0.reg base := by
          rw [← ev_agree hbo c1.agree, ho, ev_sub, ev_var, H.entry base hbl.1]
        obtain ⟨hfit, hapart⟩ := E.regionAt hmem
        unfold M64 at hfit
        have hadr : a = s0.reg base + (ev ρ' o).toNat := by omega
        have hmem0 : st.mem a = s0.mem a := by
          apply c1.holds.mem
          · simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]
            omega
          · exact E.region_notOut hmem (by omega) (by omega)
        have hbyte := E.byte hmem (ev ρ' o).toNat (by omega)
        rw [← hadr] at hbyte
        refine ⟨ρ', c1, ?_, ?_, ?_, bv⟩
        · simp only [allowed, Bool.and_true, Contract.perm, Bool.or_eq_true]
          left; left; left; left; right
          exact List.any_eq_true.mpr ⟨(base, len), hmem, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        · simp only [load]; unfold M64; omega
        · rw [g3, ← hadr]; simp only [load, hmem0]; omega
      next hne1 =>
        split at h
        next hsz =>
          obtain ⟨⟨v0, s1⟩, r1, e1, h⟩ := V.bind_ok h
          have hp := V.pure_ok h; injection hp with hp _; injection hp with hv hs; subst hv hs
          have hbo : bounded s.nvars o := by
            rw [ho]; exact bounded_sub hb (bounded_var (Nat.lt_of_lt_of_le hbl.1 wf.regs))
          obtain ⟨ρ', c1, bv, hbounds, hloadn, _⟩ := readBytes_sound E hreg size e1 H wf hbo
          have hpos : 0 < size := by rcases hsz with rfl | rfl | rfl <;> decide
          have hle8 : size ≤ 8 := by rcases hsz with rfl | rfl | rfl <;> decide
          have hb0 := hbounds 0 hpos
          have eo : ev ρ' o = ev ρ addr - s0.reg base := by
            rw [← ev_agree hbo c1.agree, ho, ev_sub, ev_var, H.entry base hbl.1]
          obtain ⟨hfit, hapart⟩ := E.regionAt hmem
          unfold M64 at hfit
          have hadr : a = s0.reg base + (ev ρ' o).toNat := by omega
          have hmem_eq : load st.mem a size = load s0.mem a size := by
            have hstep : ∀ (n : Nat) (k : Nat), (∀ j, j < n → a + k + j < s0.reg base + s0.reg len ∧ s0.reg base ≤ a + k + j) →
                load st.mem (a + k) n = load s0.mem (a + k) n := by
              intro n
              induction n with
              | zero => intro _ _; rfl
              | succ m ih =>
                intro k hkj
                simp only [load]
                have h0 := hkj 0 (by omega)
                have hm0 : st.mem (a + k) = s0.mem (a + k) := by
                  apply c1.holds.mem
                  · simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
                  · exact E.region_notOut hmem (by omega) (by omega)
                rw [hm0]
                have hnext := ih (k + 1) (fun j hj => by
                  have := hkj (j + 1) (by omega)
                  have heq : a + (k + 1) + j = a + k + (j + 1) := by omega
                  rw [heq]; exact this)
                have ha1 : a + k + 1 = a + (k + 1) := by omega
                rw [ha1, hnext]
            have := hstep size 0 (fun j hj => by
              have hbj := hbounds j hj
              omega)
            simpa using this
          refine ⟨ρ', c1, allowed_of _ _ _ (fun x x1 x2 => ?_), ?_, ?_, bv⟩
          · have hbj := hbounds (x - a) (by omega)
            simp only [Contract.perm, Bool.or_eq_true]
            left; left; left; left; right
            exact List.any_eq_true.mpr ⟨(base, len), hmem, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
          · have lt := load_lt st.mem a size
            have le : 256 ^ size ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hle8
            have e8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
            unfold M64; omega
          · rw [hmem_eq, hadr, hloadn hpos]
        next => exact (refuse_ok h).elim

/-- What `divided` finds is a division the state knows. -/
theorem divided_known {s : Sym} {x : Row} {m : Int} {q : Nat} (hd : divided s x m = some q) : Known.div x m q ∈ s.known := by
  obtain ⟨k, hk, e⟩ := List.mem_filterMap.mp (leastNat_mem hd)
  cases k with
  | div x' m' q' =>
    simp only at e
    split at e
    next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq, Lin.same_iff] at hc
      obtain ⟨rfl, rfl⟩ := hc
      injection e with e; subst e
      exact hk
    next => cases e
  | load _ _ _ => cases e
  | or _ _ _ => cases e
  | held _ _ _ => cases e
  | heldB _ _ _ => cases e
  | block _ _ _ _ => cases e
  | use _ _ _ => cases e
  | record _ _ _ => cases e

/-- A number divided by a number above zero: the two new unknowns can be the quotient and the remainder. -/
theorem divide_sound {ctx : Ctx} {s0 : State} {s : Sym} {x : Row} {m : Int} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hx : bounded s.nvars x) (pos : 0 < m) :
    ∃ ρ', Carried ctx s0 ρ s ρ' (s.divide x m) st ∧ ρ' s.nvars = ev ρ x / m ∧ ρ' (s.nvars + 1) = ev ρ x % m := by
  let ρ' : Nat → Int := fun k => if k = s.nvars then ev ρ x / m else if k = s.nvars + 1 then ev ρ x % m else ρ k
  have ag : Agree s.nvars ρ ρ' := fun k hk => by
    show ρ k = if k = s.nvars then _ else if k = s.nvars + 1 then _ else ρ k
    rw [if_neg (by omega), if_neg (by omega)]
  have H' := H.agree wf ag
  have ex : ev ρ' x = ev ρ x := (ev_agree hx ag).symm
  have nq : ρ' s.nvars = ev ρ x / m := by
    show (if s.nvars = s.nvars then _ else _) = _
    rw [if_pos rfl]
  have nr : ρ' (s.nvars + 1) = ev ρ x % m := by
    show (if s.nvars + 1 = s.nvars then _ else if s.nvars + 1 = s.nvars + 1 then _ else _) = _
    rw [if_neg (by omega), if_pos rfl]
  have le : s.nvars ≤ s.nvars + 2 := Nat.le_add_right _ _
  have bq : bounded (s.nvars + 2) (Lin.var s.nvars) := bounded_var (by omega)
  have br : bounded (s.nvars + 2) (Lin.var (s.nvars + 1)) := bounded_var (by omega)
  have bd : bounded (s.nvars + 2) (Lin.sub x (Lin.add (Lin.scale m (Lin.var s.nvars)) (Lin.var (s.nvars + 1)))) :=
    bounded_sub (bounded_mono le hx) (bounded_add (bounded_scale _ bq) br)
  have dv : ev ρ' (Lin.sub x (Lin.add (Lin.scale m (Lin.var s.nvars)) (Lin.var (s.nvars + 1)))) = 0 := by
    rw [ev_sub, ev_add, ev_scale, ev_var, ev_var, nq, nr, ex]
    have := Int.mul_ediv_add_emod (ev ρ x) m
    omega
  refine ⟨ρ', ⟨ag, le, ?_, ?_⟩, nq, nr⟩
  · exact {
      range := H'.range
      vecIntact := H'.vecIntact
      entry := H'.entry, data := H'.data, reg := H'.reg, small := H'.small, zf := H'.zf, cf := H'.cf, frame := H'.frame, frameW := H'.frameW,
      spec := H'.spec, mem := H'.mem, bytes := H'.bytes, wrote := H'.wrote, words := H'.words,
      known := by
        intro k hk
        simp only [Sym.divide, List.mem_cons] at hk
        rcases hk with rfl | hk
        · intro _
          exact ⟨by rw [nq, ex], by rw [nr, ex]⟩
        · exact H'.known k hk
      facts := by
        intro f hf
        simp only [Sym.divide, List.mem_cons] at hf
        rcases hf with rfl | rfl | rfl | rfl | hf
        · rw [holds_iff, dv]; omega
        · rw [holds_iff, ev_scale, dv]; omega
        · rw [holds_iff, ev_var, nr]; exact Int.emod_nonneg _ (by omega)
        · rw [holds_iff, ev_sub, ev_const, ev_var, nr]
          have := Int.emod_lt_of_pos (ev ρ x) pos
          omega
        · exact H'.facts f hf }
  · exact {
      range := fun rg hr => ⟨bounded_mono le (wf.range rg hr).1, fun v hv => SVal.bounded_mono le ((wf.range rg hr).2 v hv)⟩
      base := Nat.le_trans wf.base le
      reg := fun r hr => bounded_mono le (wf.reg r hr)
      zf := Flag.bounded_mono le wf.zf
      cf := Flag.bounded_mono le wf.cf
      frame := fun o v m => bounded_mono le (wf.frame o v m)
      frameW := wf.frameW
      spec := fun f m => SFact.bounded_mono le (wf.spec f m)
      wrote := fun w o x m => ⟨bounded_mono le (wf.wrote w o x m).1, bounded_mono le (wf.wrote w o x m).2⟩
      words := wf.words.mono rfl rfl rfl le
      known := by
        intro k hk
        simp only [Sym.divide, List.mem_cons] at hk
        rcases hk with rfl | hk
        · exact ⟨bounded_mono le hx, show s.nvars + 1 < s.nvars + 2 by omega⟩
        · exact Known.wf_mono le (Nat.le_refl _) (wf.known k hk)
      bytes := fun v r o m => ⟨Nat.lt_of_lt_of_le (wf.bytes v r o m).1 le, bounded_mono le (wf.bytes v r o m).2⟩
      facts := by
        intro f hf
        simp only [Sym.divide, List.mem_cons] at hf
        rcases hf with rfl | rfl | rfl | rfl | hf
        · exact bd
        · exact bounded_scale _ bd
        · exact br
        · exact bounded_sub (bounded_const _ _) br
        · exact bounded_mono le (wf.facts f hf) }

/-- A number of the machine divided by a number above zero: what `symDivide` gives is the quotient and the
remainder. -/
theorem symDivide_sound {ctx : Ctx} {s0 : State} {s : Sym} {x : Row} {m : Int} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hx : bounded s.nvars x) (pos : 0 < m) (x0 : 0 ≤ ev ρ x) :
    ∃ ρ', Carried ctx s0 ρ s ρ' (symDivide s x m).2.2 st ∧
      ev ρ' (symDivide s x m).1 = ev ρ x / m ∧ ev ρ' (symDivide s x m).2.1 = ev ρ x % m ∧
      bounded (symDivide s x m).2.2.nvars (symDivide s x m).1 ∧ bounded (symDivide s x m).2.2.nvars (symDivide s x m).2.1 := by
  cases hd : divided s x m with
  | some q =>
    simp only [symDivide, hd]
    have u := H.known _ (divided_known hd) pos
    have b := wf.known _ (divided_known hd)
    exact ⟨ρ, Carried.here H wf, by rw [ev_var]; exact u.1, by rw [ev_var]; exact u.2,
           bounded_var (Nat.lt_of_succ_lt b.2), bounded_var b.2⟩
  | none =>
    simp only [symDivide, hd]
    obtain ⟨ρ', c, hq, hr⟩ := divide_sound (ctx := ctx) (s0 := s0) H wf hx pos
    have le : s.nvars ≤ s.nvars + 2 := Nat.le_add_right _ _
    have bq : bounded (s.nvars + 2) (Lin.var s.nvars) := bounded_var (by omega)
    have br : bounded (s.nvars + 2) (Lin.var (s.nvars + 1)) := bounded_var (by omega)
    refine ⟨ρ', ⟨c.agree, c.mono, ?_, ?_⟩, by rw [ev_var]; exact hq, by rw [ev_var]; exact hr, bq, br⟩
    · exact {
        range := c.holds.range
        vecIntact := c.holds.vecIntact
        entry := c.holds.entry, data := c.holds.data, reg := c.holds.reg, small := c.holds.small, zf := c.holds.zf, cf := c.holds.cf,
        frame := c.holds.frame, frameW := c.holds.frameW, spec := c.holds.spec, mem := c.holds.mem, bytes := c.holds.bytes, wrote := c.holds.wrote, words := c.holds.words, known := c.holds.known,
        facts := by
          intro f hf
          rcases List.mem_append.mp hf with hb | hf
          · -- the quotient's bound
            unfold quotientBound at hb
            split at hb
            next k hk =>
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb
              rw [holds_iff, ev_sub, ev_const, ev_var, hq]
              have le := Int.ediv_le_ediv pos (boundOf_sound hk ρ H.facts)
              omega
            next => cases hb
          · simp only [List.mem_cons] at hf
            rcases hf with rfl | hf
            · rw [holds_iff, ev_var, hq]; exact Int.ediv_nonneg x0 (by omega)
            · exact c.holds.facts f hf }
    · exact {
        range := c.wf.range
        base := c.wf.base, reg := c.wf.reg, zf := c.wf.zf, cf := c.wf.cf, frame := c.wf.frame, frameW := c.wf.frameW, spec := c.wf.spec,
        bytes := c.wf.bytes, wrote := c.wf.wrote, words := c.wf.words.mono rfl rfl rfl (Nat.le_refl _), known := c.wf.known,
        facts := by
          intro f hf
          rcases List.mem_append.mp hf with hb | hf
          · unfold quotientBound at hb
            split at hb
            next k hk =>
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb
              exact bounded_sub (bounded_const _ _) bq
            next => cases hb
          · simp only [List.mem_cons] at hf
            rcases hf with rfl | hf
            · exact bq
            · exact c.wf.facts f hf }

/-- A row seen at once to be no less than zero is no less than zero. -/
theorem knownNonneg_sound {ctx : Ctx} {s0 : State} {s : Sym} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) {r : Row} (h : knownNonneg s r = true) : 0 ≤ ev ρ r := by
  unfold knownNonneg at h
  split at h
  next k hk => rw [ev_isConst hk]; simpa using h
  next =>
    have := H.facts r (among_iff.mp h)
    rw [holds_iff] at this; exact this

/-- Any number divided by a number above zero: what `Sym.quotRem` gives is the quotient and the remainder. -/
theorem quotRem_sound {ctx : Ctx} {s0 : State} {s : Sym} {x : Row} {m : Int} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hx : bounded s.nvars x) (pos : 0 < m) :
    ∃ ρ', Carried ctx s0 ρ s ρ' (s.quotRem x m).2.2 st ∧
      ev ρ' (s.quotRem x m).1 = ev ρ x / m ∧ ev ρ' (s.quotRem x m).2.1 = ev ρ x % m ∧
      bounded (s.quotRem x m).2.2.nvars (s.quotRem x m).1 ∧ bounded (s.quotRem x m).2.2.nvars (s.quotRem x m).2.1 := by
  cases hn : knownNonneg s x with
  | true =>
    simp only [Sym.quotRem, hn, ↓reduceIte]
    exact symDivide_sound (ctx := ctx) (s0 := s0) H wf hx pos (knownNonneg_sound H hn)
  | false =>
  cases hd : divided s x m with
  | some q =>
    simp only [Sym.quotRem, hn, hd, Bool.false_eq_true, ↓reduceIte]
    have u := H.known _ (divided_known hd) pos
    have b := wf.known _ (divided_known hd)
    exact ⟨ρ, Carried.here H wf, by rw [ev_var]; exact u.1, by rw [ev_var]; exact u.2,
           bounded_var (Nat.lt_of_succ_lt b.2), bounded_var b.2⟩
  | none =>
    simp only [Sym.quotRem, hn, hd, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨ρ', c, hq, hr⟩ := divide_sound (ctx := ctx) (s0 := s0) H wf hx pos
    exact ⟨ρ', c, by rw [ev_var]; exact hq, by rw [ev_var]; exact hr,
           bounded_var (show s.nvars < s.nvars + 2 by omega), bounded_var (show s.nvars + 1 < s.nvars + 2 by omega)⟩

theorem rowUpperAux_sound {facts : List Row} {ρ : Nat → Int} (hf : ∀ f ∈ facts, f.holds ρ) :
    ∀ (cs : List Int) (i : Nat) {u : Int}, rowUpperAux facts cs i = some u →
      0 ≤ dot cs (fun k => ρ (i + k)) ∧ dot cs (fun k => ρ (i + k)) ≤ u
  | [], _, _, h => by simp only [rowUpperAux, Option.some.injEq] at h; subst h; simp [dot]
  | c :: cs, i, u, h => by
    unfold rowUpperAux at h
    split at h
    · next hc =>
      have hc0 : c = 0 := beq_iff_eq.mp hc
      have ih := rowUpperAux_sound hf cs (i + 1) h
      simp only [dot, hc0, Int.zero_mul, Int.zero_add]
      have hfn : (fun k => ρ (i + (k + 1))) = (fun k => ρ (i + 1 + k)) := by funext k; congr 1; omega
      rw [hfn]; exact ih
    · next hc =>
      split at h
      · cases h
      · next hneg =>
        split at h
        · next hp =>
          cases hb : boundOf facts (Lin.var i) with
          | none => simp [hb] at h
          | some ub =>
            cases hr : rowUpperAux facts cs (i + 1) with
            | none => simp [hb, hr] at h
            | some rest =>
              simp only [hb, hr, Option.some.injEq] at h
              subst h
              have hlo := plain_sound hp ρ hf
              rw [ev_var] at hlo
              have hhi := boundOf_sound hb ρ hf
              rw [ev_var] at hhi
              have ih := rowUpperAux_sound hf cs (i + 1) hr
              have hfn : (fun k => ρ (i + (k + 1))) = (fun k => ρ (i + 1 + k)) := by funext k; congr 1; omega
              have h0 : 0 ≤ c * ρ i := Int.mul_nonneg (by omega) hlo
              have h1 : c * ρ i ≤ c * ub := Int.mul_le_mul_of_nonneg_left hhi (by omega)
              simp only [dot, Nat.add_zero, hfn]
              omega
        · cases h

theorem rowUpper_sound {facts : List Row} {ρ : Nat → Int} (hf : ∀ f ∈ facts, f.holds ρ)
    {r : Row} {u : Int} (h : rowUpper facts r = some u) : 0 ≤ ev ρ r ∧ ev ρ r ≤ u := by
  unfold rowUpper at h
  split at h
  · cases h
  · next hneg =>
    cases ha : rowUpperAux facts r.coeff 0 with
    | none => simp [ha] at h
    | some v =>
      simp only [ha, Option.map_some, Option.some.injEq] at h
      subst h
      have ih := rowUpperAux_sound hf r.coeff 0 ha
      have hfn : (fun k => ρ (0 + k)) = ρ := by funext k; simp
      rw [hfn] at ih
      simp only [ev]
      omega

theorem symSplit_sound {facts : List Row} {ρ : Nat → Int} (hf : ∀ f ∈ facts, f.holds ρ)
    {n : Nat} {x q r : Row} {m : Int} (hx : bounded n x) (pos : 0 < m)
    (h : symSplit facts x m = some (q, r)) :
    ev ρ q = ev ρ x / m ∧ ev ρ r = ev ρ x % m ∧ bounded n q ∧ bounded n r := by
  unfold symSplit at h
  cases hu : rowUpper facts (Lin.splitMod x m).2 with
  | none => simp [hu] at h
  | some u =>
    simp only [hu] at h
    split at h
    · next hlt =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hq, hr⟩ := h
      subst hq hr
      have hb := rowUpper_sound hf hu
      have hev := ev_splitMod ρ x m
      have hdiv : ev ρ x / m = ev ρ (Lin.splitMod x m).1 := by
        rw [hev, Int.mul_add_ediv_left _ _ (Int.ne_of_gt pos), Int.ediv_eq_zero_of_lt hb.1 (by omega), Int.add_zero]
      have hmod : ev ρ x % m = ev ρ (Lin.splitMod x m).2 := by
        rw [hev, Int.mul_add_emod_self_left, Int.emod_eq_of_lt hb.1 (by omega)]
      refine ⟨hdiv.symm, hmod.symm, ?_, ?_⟩
      · exact Nat.le_trans (strip_length _) (by rw [List.length_map]; exact hx)
      · exact Nat.le_trans (strip_length _) (by rw [List.length_map]; exact hx)
    · cases h

theorem symLow_sound {ctx : Ctx} {s0 : State} {s : Sym} {x : Row} {m : Int} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hx : bounded s.nvars x) (pos : 0 < m) (x0 : 0 ≤ ev ρ x) :
    ∃ ρ', Carried ctx s0 ρ s ρ' (symLow s x m).2 st ∧ ev ρ' (symLow s x m).1 = ev ρ x % m ∧
      bounded (symLow s x m).2.nvars (symLow s x m).1 := by
  cases hk : (x.coeff.all fun c => c % m == 0) with
  | true =>
    simp only [symLow, hk, ↓reduceIte]
    exact ⟨ρ, Carried.here H wf, by rw [ev_const, ev_low_exact hk], bounded_const _ _⟩
  | false =>
    cases hp : plain s.facts (Lin.sub (Lin.const (m - 1)) x) with
    | true =>
      -- a number seen at once to be below the divisor is its own remainder
      simp only [symLow, hk, hp, Bool.false_eq_true, ↓reduceIte]
      have g := plain_sound hp ρ H.facts
      rw [ev_sub, ev_const] at g
      exact ⟨ρ, Carried.here H wf, (Int.emod_eq_of_lt x0 (by omega)).symm, hx⟩
    | false =>
      cases hs : symSplit s.facts x m with
      | some qr =>
        obtain ⟨q, r⟩ := qr
        simp only [symLow, hk, hp, hs, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨_, hr, _, br⟩ := symSplit_sound H.facts hx pos hs
        exact ⟨ρ, Carried.here H wf, hr, br⟩
      | none =>
        simp only [symLow, hk, hp, hs, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨ρ', c, _, hr, _, br⟩ := symDivide_sound (ctx := ctx) (s0 := s0) H wf hx pos x0
        exact ⟨ρ', c, hr, br⟩

theorem symQuot_sound {ctx : Ctx} {s0 : State} {s : Sym} {x : Row} {m : Int} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hx : bounded s.nvars x) (pos : 0 < m) (x0 : 0 ≤ ev ρ x) :
    ∃ ρ', Carried ctx s0 ρ s ρ' (symQuot s x m).2 st ∧ ev ρ' (symQuot s x m).1 = ev ρ x / m ∧
      bounded (symQuot s x m).2.nvars (symQuot s x m).1 := by
  cases hk : (x.coeff.all fun c => c % m == 0) with
  | true =>
    simp only [symQuot, hk, ↓reduceIte]
    refine ⟨ρ, Carried.here H wf, ev_quot_exact pos hk, ?_⟩
    exact Nat.le_trans (strip_length _) (by rw [List.length_map]; exact hx)
  | false =>
    cases hs : symSplit s.facts x m with
    | some qr =>
      obtain ⟨q, r⟩ := qr
      simp only [symQuot, hk, hs, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hq, _, bq, _⟩ := symSplit_sound H.facts hx pos hs
      exact ⟨ρ, Carried.here H wf, hq, bq⟩
    | none =>
      simp only [symQuot, hk, hs, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨ρ', c, hq, _, bq, _⟩ := symDivide_sound (ctx := ctx) (s0 := s0) H wf hx pos x0
      exact ⟨ρ', c, hq, bq⟩

theorem knownOr_mem {x y : Row} : ∀ {l : List Known} {v : Nat}, knownOr x y l = some v → Known.or v x y ∈ l ∨ Known.or v y x ∈ l
  | [], _, h => by simp [knownOr] at h
  | k :: more, v, h => by
    cases k with
    | or v' x' y' =>
      simp only [knownOr] at h
      split at h
      next e =>
        injection h with h
        subst h
        rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · subst e1 e2; exact Or.inl (List.mem_cons_self ..)
        · subst e1 e2; exact Or.inr (List.mem_cons_self ..)
      next => exact (knownOr_mem h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
    | load _ _ _ => simp only [knownOr] at h; exact (knownOr_mem h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
    | held _ _ _ => simp only [knownOr] at h; exact (knownOr_mem h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
    | heldB _ _ _ => simp only [knownOr] at h; exact (knownOr_mem h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
    | div _ _ _ => simp only [knownOr] at h; exact (knownOr_mem h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
    | block _ _ _ _ => simp only [knownOr] at h; exact (knownOr_mem h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
    | use _ _ _ => simp only [knownOr] at h; exact (knownOr_mem h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
    | record _ _ _ => simp only [knownOr] at h; exact (knownOr_mem h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)

/-- Two numbers' bits put together: the unknown the state knows as that number is it. -/
theorem symOrKnown_sound {ctx : Ctx} {s0 : State} {s s' : Sym} {x y : Row} {v : EV} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symOrKnown s x y items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (xa xb : Nat) (hx : EV.sem ρ s.nvars xa (.lin x)) (hy : EV.sem ρ s.nvars xb (.lin y)) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ xa ||| xb < M64 ∧ EV.sem ρ' s'.nvars (xa ||| xb) v := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  have lt : xa ||| xb < M64 := by unfold M64 at *; exact Nat.or_lt_two_pow hx1 hy1
  unfold symOrKnown at h
  cases hk : knownOr x y s.known with
  | some v0 =>
    simp only [hk] at h
    have := V.pure_ok h
    injection this with hp _
    injection hp with h1 h2
    subst h1 h2
    rcases knownOr_mem hk with m | m
    · obtain ⟨_, _, g⟩ := H.known _ m
      refine ⟨ρ, Carried.here H wf, lt, lt, ?_, bounded_var (wf.known _ m).1⟩
      rw [ev_var, g, ← hx2, ← hy2]; simp
    · obtain ⟨_, _, g⟩ := H.known _ m
      refine ⟨ρ, Carried.here H wf, lt, lt, ?_, bounded_var (wf.known _ m).1⟩
      rw [ev_var, g, ← hx2, ← hy2]; simp [Nat.or_comm]
  | none =>
    simp only [hk] at h
    have := V.pure_ok h
    injection this with hp _
    injection hp with h1 h2
    subst h1 h2
    have new := extend_new ρ s.nvars ((xa ||| xb : Nat) : Int)
    have bv : bounded (s.nvars + 1) (Lin.var s.nvars) := bounded_var (Nat.lt_succ_self _)
    have le : s.nvars ≤ s.nvars + 1 := Nat.le_succ _
    have ag := extend_agree ρ s.nvars ((xa ||| xb : Nat) : Int)
    have ex : ev (extend ρ s.nvars ((xa ||| xb : Nat) : Int)) x = xa := by rw [← ev_agree hx3 ag]; exact hx2.symm
    have ey : ev (extend ρ s.nvars ((xa ||| xb : Nat) : Int)) y = xb := by rw [← ev_agree hy3 ag]; exact hy2.symm
    have bx := bounded_mono le hx3
    have by' := bounded_mono le hy3
    have l1 : xa ≤ xa ||| xb := Nat.left_le_or
    have l2 : xb ≤ xa ||| xb := Nat.right_le_or
    have lt2 : xa ||| xb < 2 ^ 64 := by have := lt; unfold M64 at this; exact this
    refine ⟨_, Carried.fresh H wf ((xa ||| xb : Nat) : Int) _ (.or s.nvars x y) ?_ ⟨Nat.lt_succ_self _, bx, by'⟩ ?_ ?_, lt, lt, by rw [ev_var, new], bv⟩
    · intro f m
      rcases List.mem_append.mp m with m | m
      · rcases List.mem_append.mp m with m | m
        · simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at m
          rcases m with rfl | rfl
          · exact bv
          · exact bounded_sub (bounded_const _ _) bv
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
          rcases m with rfl | rfl
          · exact bounded_sub bv bx
          · exact bounded_sub bv by'
      · unfold orBound at m
        split at m
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
          subst m
          exact bounded_sub (bounded_const _ _) bv
        · cases m
    · intro f m
      rcases List.mem_append.mp m with m | m
      · rcases List.mem_append.mp m with m | m
        · simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at m
          rcases m with rfl | rfl
          · rw [holds_iff, ev_var, new]; exact Int.natCast_nonneg _
          · rw [holds_iff, ev_sub, ev_const, ev_var, new]; simp only [top]; omega
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
          rcases m with rfl | rfl
          · rw [holds_iff, ev_sub, ev_var, new, ex]; omega
          · rw [holds_iff, ev_sub, ev_var, new, ey]; omega
      · unfold orBound at m
        split at m
        next k hfind =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
          subst m
          have hp := List.find?_some hfind
          simp only [Bool.and_eq_true] at hp
          have g1 := plain_sound hp.1 ρ H.facts
          have g2 := plain_sound hp.2 ρ H.facts
          simp only [ev_sub, ev_const] at g1 g2
          have cast : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
          have a1 : xa < 2 ^ k := Int.ofNat_lt.mp (by rw [cast]; omega)
          have a2 : xb < 2 ^ k := Int.ofNat_lt.mp (by rw [cast]; omega)
          have a3 : ((xa ||| xb : Nat) : Int) < ((2 ^ k : Nat) : Int) := Int.ofNat_lt.mpr (Nat.or_lt_two_pow a1 a2)
          rw [holds_iff, ev_sub, ev_const, ev_var, new]
          rw [cast] at a3
          omega
        next => cases m
    · refine ⟨by rw [ex]; exact Int.natCast_nonneg _, by rw [ey]; exact Int.natCast_nonneg _, ?_⟩
      rw [new, ex, ey]; simp

/-- The bits of a number below 2^j and of any number, put together: the second number's bits from bit j on,
and what the first number's bits and the second's lower bits make. -/
theorem or_small {x k j : Nat} (hx : x < 2 ^ j) : x ||| k = 2 ^ j * (k / 2 ^ j) + (x ||| k % 2 ^ j) := by
  have h := (Nat.div_add_mod (x ||| k) (2 ^ j)).symm
  rw [Nat.or_div_two_pow, Nat.or_mod_two_pow, Nat.div_eq_of_lt hx, Nat.mod_eq_of_lt hx, Nat.zero_or] at h
  exact h

/-- What `smallBits` finds: the number lies from 0 to below 2^j, and j is at most 32. -/
theorem smallBits_sound {facts : List Row} {x : Row} {j : Nat} (h : smallBits facts x = some j) (ρ : Nat → Int)
    (hf : ∀ f ∈ facts, f.holds ρ) : 0 ≤ ev ρ x ∧ ev ρ x < (2 : Int) ^ j ∧ j ≤ 32 := by
  unfold smallBits at h
  have hp := List.find?_some h
  have hm := List.mem_of_find?_eq_some h
  simp only [Bool.and_eq_true] at hp
  have g1 := plain_sound hp.1 ρ hf
  have g2 := plain_sound hp.2 ρ hf
  simp only [ev_sub, ev_const] at g2
  refine ⟨g1, by omega, ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl <;> decide

/-- The remainder by 2^j of a number that is no less than zero, as a number of the machine. -/
theorem emod_two_pow_toNat {k : Int} (k0 : 0 ≤ k) (j : Nat) : k % (2 : Int) ^ j = ((k.toNat % 2 ^ j : Nat) : Int) := by
  rw [Int.natCast_emod, Int.toNat_of_nonneg k0]; simp

/-- What `orParts` finds: the second number is that number of the table, which is 2^j or more; the first lies
from 0 to below 2^j; and j is at most 32. -/
theorem orParts_sound {facts : List Row} {x y : Row} {k : Int} {j : Nat} (h : orParts facts x y = some (k, j)) (ρ : Nat → Int)
    (hf : ∀ f ∈ facts, f.holds ρ) : ev ρ y = k ∧ 0 ≤ ev ρ x ∧ ev ρ x < (2 : Int) ^ j ∧ j ≤ 32 := by
  unfold orParts at h
  cases hc : constOf facts y with
  | none => simp [hc] at h
  | some k' =>
    cases hj : smallBits facts x with
    | none => simp [hc, hj] at h
    | some j' =>
      simp only [hc, hj] at h
      split at h
      next =>
        injection h with h
        injection h with h1 h2
        subst h1 h2
        exact ⟨constOf_sound hc ρ hf, smallBits_sound hj ρ hf⟩
      next => cases h

/-- The bits of a small number and of a number of the table that is 2^j or more, put together: what
`symOrSmall` gives is that number. -/
theorem symOrSmall_sound {ctx : Ctx} {s0 : State} {s s' : Sym} {x : Row} {k : Int} {j : Nat} {v : EV} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symOrSmall s x k j items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (xa xb : Nat) (hx : EV.sem ρ s.nvars xa (.lin x)) (hk : (xb : Int) = k) (hb : xb < M64)
    (small : xa < 2 ^ j) (j32 : j ≤ 32) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ xa ||| xb < M64 ∧ EV.sem ρ' s'.nvars (xa ||| xb) v := by
  have lt : xa ||| xb < M64 := by unfold M64 at *; exact Nat.or_lt_two_pow hx.1 hb
  have split := or_small (k := xb) small
  have k0 : 0 ≤ k := by rw [← hk]; exact Int.natCast_nonneg _
  have kn : k.toNat = xb := by rw [← hk]; exact Int.toNat_natCast xb
  have kmod : k % (2 : Int) ^ j = ((xb % 2 ^ j : Nat) : Int) := by rw [emod_two_pow_toNat k0, kn]
  have whole := Nat.div_add_mod xb (2 ^ j)
  unfold symOrSmall at h
  split at h
  next h0 =>
    have := V.pure_ok h
    injection this with hp _
    injection hp with h1 h2
    subst h1 h2
    have m0 : xb % 2 ^ j = 0 := by rw [kmod] at h0; exact Int.natCast_eq_zero.mp h0
    have e : xa ||| xb = xa + xb := by rw [split, m0, Nat.or_zero]; omega
    refine ⟨ρ, Carried.here H wf, lt, lt, ?_, bounded_add hx.2.2 (bounded_const _ _)⟩
    rw [ev_add, ev_const, ← hx.2.1, ← hk, e]; omega
  next h0 =>
    obtain ⟨⟨u, s1⟩, r1, hor, h⟩ := V.bind_ok h
    have plt : 2 ^ j ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) j32
    have k0lt : xb % 2 ^ j < M64 := by
      have := Nat.mod_lt xb (Nat.two_pow_pos j)
      unfold M64; omega
    have hy0 : EV.sem ρ s.nvars (xb % 2 ^ j) (.lin (Lin.const (k % 2 ^ j))) := ⟨k0lt, by rw [ev_const, kmod], bounded_const _ _⟩
    obtain ⟨ρ', c, _, sem⟩ := symOrKnown_sound hor H wf xa (xb % 2 ^ j) hx hy0
    cases u with
    | lin ur =>
      simp only at h
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      refine ⟨ρ', c, lt, lt, ?_, bounded_add sem.2.2 (bounded_const _ _)⟩
      rw [ev_add, ev_const, ← sem.2.1, split, kmod, ← hk]; omega
    | equal _ _ => exact (refuse_ok h).elim
    | below _ _ => exact (refuse_ok h).elim

/-- Two numbers' bits put together, one of the two being the number zero or neither. -/
theorem symOr_sound {ctx : Ctx} {s0 : State} {s s' : Sym} {x y : Row} {v : EV} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symOr s x y items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (xa xb : Nat) (hx : EV.sem ρ s.nvars xa (.lin x)) (hy : EV.sem ρ s.nvars xb (.lin y)) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ xa ||| xb < M64 ∧ EV.sem ρ' s'.nvars (xa ||| xb) v := by
  unfold symOr at h
  split at h
  next hy0 =>
    have := V.pure_ok h
    injection this with hp _
    injection hp with h1 h2
    subst h1 h2
    have e := ev_isConst (ρ := ρ) hy0
    have xb0 : xb = 0 := by have := hy.2.1; omega
    subst xb0
    rw [Nat.or_zero]
    exact ⟨ρ, Carried.here H wf, hx.1, hx⟩
  next =>
    split at h
    next hx0 =>
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      have e := ev_isConst (ρ := ρ) hx0
      have xa0 : xa = 0 := by have := hx.2.1; omega
      subst xa0
      rw [Nat.zero_or]
      exact ⟨ρ, Carried.here H wf, hy.1, hy⟩
    next =>
      cases hp : orParts s.facts x y with
      | some kj =>
        obtain ⟨k, j⟩ := kj
        simp only [hp] at h
        obtain ⟨ek, x0, xlt, j32⟩ := orParts_sound hp ρ H.facts
        have small : xa < 2 ^ j := Int.ofNat_lt.mp (by rw [hx.2.1]; simpa using xlt)
        exact symOrSmall_sound h H wf xa xb hx (by rw [hy.2.1, ek]) hy.1 small j32
      | none =>
        simp only [hp] at h
        cases hq : orParts s.facts y x with
        | some kj =>
          obtain ⟨k, j⟩ := kj
          simp only [hq] at h
          obtain ⟨ek, y0, ylt, j32⟩ := orParts_sound hq ρ H.facts
          have small : xb < 2 ^ j := Int.ofNat_lt.mp (by rw [hy.2.1]; simpa using ylt)
          rw [Nat.or_comm]
          exact symOrSmall_sound h H wf xb xa hy (by rw [hx.2.1, ek]) hx.1 small j32
        | none =>
          simp only [hq] at h
          exact symOrKnown_sound h H wf xa xb hx hy

/-- The 64-bit mask ending in six zero bits rounds an address down to a multiple of 64. -/
theorem align64_mask {x : Nat} (hx : x < M64) : x &&& (M64 - 64) = 64 * (x / 64) := by
  have div : (x &&& (M64 - 64)) / 64 = x / 64 := by
    change (x &&& (M64 - 64)) / 2 ^ 6 = _
    rw [Nat.and_div_two_pow, show (M64 - 64) / (2 ^ 6) = 2 ^ 58 - 1 by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by unfold M64 at hx; omega)
  have rem : (x &&& (M64 - 64)) % 64 = 0 := by
    change (x &&& (M64 - 64)) % (2 ^ 6) = 0
    rw [Nat.and_mod_two_pow, show (M64 - 64) % (2 ^ 6) = 0 by decide, Nat.and_zero]
  omega

private theorem findSome_mem_step {α β : Type} {p : α → Option β} {xs : List α} {b : β}
    (h : xs.findSome? p = some b) : ∃ x ∈ xs, p x = some b := by
  induction xs with
  | nil => simp at h
  | cons a rest ih =>
    simp only [List.findSome?] at h
    cases ha : p a with
    | some v =>
      rw [ha] at h
      injection h with hv
      subst hv
      exact ⟨a, List.mem_cons_self .., ha⟩
    | none =>
      rw [ha] at h
      obtain ⟨x, hx, hpx⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem _ hx, hpx⟩

theorem maskSpan_spec {m : Int} {k w : Nat} (h : maskSpan m = some (k, w)) :
    k < 64 ∧ 1 ≤ w ∧ k + w ≤ 64 ∧ m = (((2 ^ w - 1) * 2 ^ k : Nat) : Int) := by
  unfold maskSpan at h
  split at h
  next => cases h
  next =>
    obtain ⟨k', hk'mem, hk'⟩ := findSome_mem_step h
    have hk'lt : k' < 64 := List.mem_range.mp hk'mem
    dsimp only at hk'
    split at hk'
    next hmod =>
      obtain ⟨w', hw'mem, hw'⟩ := findSome_mem_step hk'
      have hw'lt : w' < 65 - k' := List.mem_range.mp hw'mem
      split at hw'
      next hcond =>
        injection hw' with heq
        injection heq with ek ew
        subst ek ew
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond hmod
        refine ⟨hk'lt, hcond.1, by omega, ?_⟩
        have hm1 : m = (m / (2 : Int) ^ k') * (2 : Int) ^ k' := by
          have := Int.mul_ediv_add_emod m ((2 : Int) ^ k')
          rw [hmod, Int.add_zero, Int.mul_comm] at this
          exact this.symm
        have hpoww : ((2 ^ w' : Nat) : Int) = (2 : Int) ^ w' := by simp
        have hnat : ((2 ^ w' - 1 : Nat) : Int) = (2 : Int) ^ w' - 1 := by
          have := Nat.two_pow_pos w'
          rw [← hpoww]; omega
        have hpow : ((2 ^ k' : Nat) : Int) = (2 : Int) ^ k' := by simp
        rw [Int.natCast_mul, hnat, hpow, hm1, ← hcond.2]
      next => cases hw'
    next => cases hk'

theorem and_maskSpan (xa k w : Nat) :
    xa &&& ((2 ^ w - 1) * 2 ^ k) = ((xa / 2 ^ k) % 2 ^ w) * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq,
      Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  by_cases hki : k ≤ i
  · simp only [decide_eq_true hki, Bool.true_and, Nat.testBit_two_pow_sub_one,
               Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    rw [Nat.sub_add_cancel hki, Bool.and_comm]
  · simp [hki]

theorem symAndConst_sound {ctx : Ctx} {s0 : State} {s s' : Sym} {x : Row} {m : Int} {v : EV}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symAndConst s x m items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (xa xb : Nat) (hx : EV.sem ρ s.nvars xa (.lin x)) (hxb : (xb : Int) = m) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ EV.sem ρ' s'.nvars ((xa &&& xb) % M64) v := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hx1' : xa < M64 := hx1
  unfold symAndConst at h
  split at h
  next hm0 =>
    simp only [beq_iff_eq] at hm0
    have hxb0 : xb = 0 := by omega
    subst hxb0
    have := V.pure_ok h
    injection this with hp _
    injection hp with h1 h2
    subst h1 h2
    refine ⟨ρ, Carried.here H wf, Nat.mod_lt _ (by decide), ?_, bounded_const _ _⟩
    simp [ev_const]
  next =>
    cases hms : maskSpan m with
    | none => simp only [hms] at h; exact (refuse_ok h).elim
    | some kw =>
      rcases kw with ⟨k, w⟩
      obtain ⟨hk64, hw1, hkw64, hmeq⟩ := maskSpan_spec hms
      have hxb_eq : xb = (2 ^ w - 1) * 2 ^ k := by omega
      subst hxb_eq
      have hand := and_maskSpan xa k w
      have hlt : ((xa / 2 ^ k) % 2 ^ w) * 2 ^ k < M64 := by
        have h1 : (xa / 2 ^ k) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
        have h2 : ((xa / 2 ^ k) % 2 ^ w) * 2 ^ k < 2 ^ w * 2 ^ k :=
          Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos k)
        have h3 : 2 ^ w * 2 ^ k ≤ M64 := by
          rw [← Nat.pow_add]; unfold M64; exact Nat.pow_le_pow_right (by decide) (by omega)
        omega
      cases k with
      | zero =>
        simp only [hms] at h
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        have posw : (0 : Int) < (2 : Int) ^ w := Int.pow_pos (by decide)
        obtain ⟨ρ', c, hr, br⟩ := symLow_sound (ctx := ctx) (s0 := s0) (m := (2 : Int) ^ w) H wf hx3 posw (by rw [← hx2]; omega)
        have castw : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by simp
        refine ⟨ρ', c, Nat.mod_lt _ (by decide), ?_, br⟩
        rw [hand, Nat.pow_zero, Nat.div_one, Nat.mul_one, Nat.mod_eq_of_lt (by simpa using hlt),
            hr, ← hx2, Int.natCast_emod, castw]
      | succ k' =>
        simp only [hms] at h
        split at h
        next h64 =>
          simp only [beq_iff_eq] at h64
          have := V.pure_ok h
          injection this with hp _
          injection hp with h1 h2
          subst h1 h2
          have posk : (0 : Int) < (2 : Int) ^ (k' + 1) := Int.pow_pos (by decide)
          obtain ⟨ρ', c, hq, bq⟩ := symQuot_sound (ctx := ctx) (s0 := s0) (m := (2 : Int) ^ (k' + 1)) H wf hx3 posk (by rw [← hx2]; omega)
          have castk : ((2 ^ (k' + 1) : Nat) : Int) = (2 : Int) ^ (k' + 1) := by simp
          have hdiv_lt : xa / 2 ^ (k' + 1) < 2 ^ w := by
            have hm64 : M64 = 2 ^ w * 2 ^ (k' + 1) := by
              rw [← Nat.pow_add, show w + (k' + 1) = 64 by omega]; rfl
            rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← hm64]
            exact hx1'
          refine ⟨ρ', c, Nat.mod_lt _ (by decide), ?_, bounded_scale _ bq⟩
          rw [hand, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hdiv_lt, ev_scale, hq, ← hx2,
              Int.natCast_mul, Int.natCast_ediv, castk, Int.mul_comm]
        next =>
          have := V.pure_ok h
          injection this with hp _
          injection hp with h1 h2
          subst h1 h2
          have posk : (0 : Int) < (2 : Int) ^ (k' + 1) := Int.pow_pos (by decide)
          have posw : (0 : Int) < (2 : Int) ^ w := Int.pow_pos (by decide)
          obtain ⟨ρ1, c1, hq1, bq1⟩ := symQuot_sound (ctx := ctx) (s0 := s0) (m := (2 : Int) ^ (k' + 1)) H wf hx3 posk (by rw [← hx2]; omega)
          have hq1_nn : 0 ≤ ev ρ1 (symQuot s x ((2 : Int) ^ (k' + 1))).1 := by
            rw [hq1, ← hx2]; exact Int.ediv_nonneg (Int.natCast_nonneg _) (Int.le_of_lt posk)
          obtain ⟨ρ2, c2, hr2, br2⟩ := symLow_sound (ctx := ctx) (s0 := s0) (m := (2 : Int) ^ w) c1.holds c1.wf bq1 posw hq1_nn
          have castk : ((2 ^ (k' + 1) : Nat) : Int) = (2 : Int) ^ (k' + 1) := by simp
          have castw : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by simp
          refine ⟨ρ2, c1.then c2, Nat.mod_lt _ (by decide), ?_, bounded_scale _ br2⟩
          rw [hand, Nat.mod_eq_of_lt hlt, ev_scale, hr2, hq1, ← hx2,
              Int.natCast_mul, Int.natCast_emod, Int.natCast_ediv, castk, castw, Int.mul_comm]

theorem symPrim_sound {ctx : Ctx} {s0 : State} {f : String} {s s' : Sym} {x y : Row} {v : EV} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symPrim f s x y items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (xa xb : Nat) (hx : EV.sem ρ s.nvars xa (.lin x)) (hy : EV.sem ρ s.nvars xb (.lin y)) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ ∃ z, prim f [xa, xb] = some z ∧ EV.sem ρ' s'.nvars z v := by
  have hf := H.facts
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  have hx1' : xa < M64 := hx1
  have sx := signed_ev ρ x
  have sy := signed_ev ρ y
  unfold M64 at hx1 hy1
  unfold symPrim at h
  split at h
  next hc =>
    obtain ⟨w, r0, _, h⟩ := V.bind_ok h
    cases w with
    | true =>
      simp only [ite_true] at h
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      have hpos : (0 : Int) < (M64 : Int) := by decide
      have hnn : 0 ≤ ev ρ (Lin.add x y) := by rw [ev_add, ← hx2, ← hy2]; omega
      obtain ⟨ρ', hc', er, br⟩ := symLow_sound (ctx := ctx) (s0 := s0) (m := (M64 : Int)) H wf
        (bounded_add hx3 hy3) hpos hnn
      refine ⟨ρ', hc', (xa + xb) % M64, by simp only [prim]; rw [if_pos hc], Nat.mod_lt _ (by decide), ?_, br⟩
      rw [er, ev_add, ← hx2, ← hy2, Int.natCast_emod, Int.natCast_add]
    | false =>
      simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
      unfold inRange at e1
      obtain ⟨_, r2, e2, e3⟩ := V.bind_ok e1
      have g1 := entail_sound e2 ρ hf
      have g2 := entail_sound e3 ρ hf
      simp only [ev_sub, ev_add, ev_const, top] at g1 g2
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      refine ⟨ρ, Carried.here H wf, (xa + xb) % M64, by simp only [prim]; rw [if_pos hc], ?_, ?_, bounded_add (bounded_signed hx3) (bounded_signed hy3)⟩
      · exact Nat.mod_lt _ (by decide)
      · rw [ev_add]; unfold M64; omega
  next hc =>
    split at h
    next hc2 =>
      obtain ⟨w, r0, _, h⟩ := V.bind_ok h
      cases w with
      | true =>
        simp only [ite_true] at h
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        have hpos : (0 : Int) < (M64 : Int) := by decide
        have hnn : 0 ≤ ev ρ (Lin.add (Lin.sub x y) (Lin.const (M64 : Int))) := by
          rw [ev_add, ev_sub, ev_const, ← hx2, ← hy2]; unfold M64; omega
        obtain ⟨ρ', hc', er, br⟩ := symLow_sound (ctx := ctx) (s0 := s0) (m := (M64 : Int)) H wf
          (bounded_add (bounded_sub hx3 hy3) (bounded_const s.nvars _)) hpos hnn
        refine ⟨ρ', hc', (xa + (M64 - xb % M64)) % M64, by simp only [prim]; rw [if_neg hc, if_pos hc2], Nat.mod_lt _ (by decide), ?_, br⟩
        rw [er, ev_add, ev_sub, ev_const, ← hx2, ← hy2]
        have hbmod : xb % M64 = xb := Nat.mod_eq_of_lt (by unfold M64; exact hy1)
        rw [hbmod, Int.natCast_emod]
        have hcast : ((xa + (M64 - xb) : Nat) : Int) = (xa : Int) - (xb : Int) + (M64 : Int) := by
          unfold M64; omega
        rw [hcast]
      | false =>
        simp only [Bool.false_eq_true, ite_false] at h
        obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
        unfold inRange at e1
        obtain ⟨_, r2, e2, e3⟩ := V.bind_ok e1
        have g1 := entail_sound e2 ρ hf
        have g2 := entail_sound e3 ρ hf
        simp only [ev_sub, ev_const, top] at g1 g2
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        refine ⟨ρ, Carried.here H wf, (xa + (M64 - xb % M64)) % M64, by simp only [prim]; rw [if_neg hc, if_pos hc2], ?_, ?_, bounded_sub (bounded_signed hx3) (bounded_signed hy3)⟩
        · exact Nat.mod_lt _ (by decide)
        · rw [ev_sub]; unfold M64; omega
    next hc2 =>
      split at h
      next hc3 =>
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        have fe : f = "equal" := by simpa using hc3
        subst fe
        refine ⟨ρ, Carried.here H wf, (if xa % M64 = xb % M64 then 1 else 0), by simp [prim], ?_, hx3, hy3⟩
        unfold M64
        rw [Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hy1, ← hx2, ← hy2]
        simp only [Int.natCast_inj]
      next hc3 =>
        split at h
        next hc4 =>
          have := V.pure_ok h
          injection this with hp _
          injection hp with h1 h2
          subst h1 h2
          have fe : f = "below" := by simpa using hc4
          subst fe
          refine ⟨ρ, Carried.here H wf, (if xa % M64 < xb % M64 then 1 else 0), by simp [prim], ?_, hx3, hy3⟩
          unfold M64
          rw [Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hy1, ← hx2, ← hy2]
          simp only [Int.ofNat_lt]
        next hc4 =>
          split at h
          next hc5 =>
            have fe : f = "shl64" := by simpa using hc5
            subst fe
            cases hk : constOf s.facts y with
            | none => simp only [hk] at h; exact (refuse_ok h).elim
            | some k =>
              simp only [hk] at h
              split at h
              next hk2 =>
                have yk : (xb : Int) = k := by rw [hy2]; exact constOf_sound hk ρ hf
                have e : xb = k.toNat := by omega
                subst e
                have k64 : k.toNat < 64 := by omega
                have cast : ((2 ^ k.toNat : Nat) : Int) = (2 : Int) ^ k.toNat := by simp
                have castm : ((2 ^ (64 - k.toNat) : Nat) : Int) = (2 : Int) ^ (64 - k.toNat) := by simp
                have full : 2 ^ (64 - k.toNat) * 2 ^ k.toNat = M64 := by
                  rw [← Nat.pow_add, show 64 - k.toNat + k.toNat = 64 by omega]; rfl
                obtain ⟨kept, rest1, ek, h⟩ := V.bind_ok h
                cases kept with
                | true =>
                  -- the number is shown to be small enough: the doublings stay below 2^64
                  have g2 := staysBelow_sound ek ρ hf
                  simp only [if_true] at h
                  have := V.pure_ok h
                  injection this with hp _
                  injection hp with h1 h2
                  subst h1 h2
                  have small : xa < 2 ^ (64 - k.toNat) := by
                    have : ((xa : Nat) : Int) < ((2 ^ (64 - k.toNat) : Nat) : Int) := by rw [castm, hx2]; omega
                    exact Int.ofNat_lt.mp this
                  have lt : xa * 2 ^ k.toNat < M64 := by
                    rw [← full]; exact Nat.mul_lt_mul_of_pos_right small (Nat.pow_pos (by decide))
                  refine ⟨ρ, Carried.here H wf, (xa <<< k.toNat) % M64, by simp [prim], Nat.mod_lt _ (by decide), ?_, bounded_scale _ hx3⟩
                  rw [ev_scale, ← hx2, Nat.shiftLeft_eq, Nat.mod_eq_of_lt lt, Int.natCast_mul, cast, Int.mul_comm]
                | false =>
                  -- else: so many doublings of the remainder by 2^(64 - k)
                  simp only [Bool.false_eq_true, if_false] at h
                  have := V.pure_ok h
                  injection this with hp _
                  injection hp with h1 h2
                  subst h1 h2
                  have pos : (0 : Int) < 2 ^ (64 - k.toNat) := Int.pow_pos (by decide)
                  obtain ⟨ρ', hc, er, br⟩ := symLow_sound (ctx := ctx) (s0 := s0) (m := 2 ^ (64 - k.toNat)) H wf hx3 pos (by rw [← hx2]; omega)
                  refine ⟨ρ', hc, (xa <<< k.toNat) % M64, by simp [prim], Nat.mod_lt _ (by decide), ?_, bounded_scale _ br⟩
                  rw [ev_scale, er, ← hx2, Nat.shiftLeft_eq, ← full, Nat.mul_mod_mul_right, Int.natCast_mul, cast, Int.natCast_emod, castm,
                    Int.mul_comm]
              next => exact (refuse_ok h).elim
          next hc5 =>
            split at h
            next hc6 =>
              have fe : f = "shr64" := by simpa using hc6
              subst fe
              cases hk : constOf s.facts y with
              | none => simp only [hk] at h; exact (refuse_ok h).elim
              | some k =>
                simp only [hk] at h
                split at h
                next hk2 =>
                  have := V.pure_ok h
                  injection this with hp _
                  injection hp with h1 h2
                  subst h1 h2
                  have yk : (xb : Int) = k := by rw [hy2]; exact constOf_sound hk ρ hf
                  have e : xb = k.toNat := by omega
                  subst e
                  have pos : (0 : Int) < 2 ^ k.toNat := Int.pow_pos (by decide)
                  obtain ⟨ρ', c, hq, bq⟩ := symQuot_sound (ctx := ctx) (s0 := s0) H wf hx3 pos (by rw [← hx2]; omega)
                  have cast : ((2 ^ k.toNat : Nat) : Int) = (2 : Int) ^ k.toNat := by simp
                  refine ⟨ρ', c, (xa % M64) >>> k.toNat, by simp [prim], ?_, ?_, bq⟩
                  · rw [Nat.mod_eq_of_lt hx1', Nat.shiftRight_eq_div_pow]
                    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx1'
                  · rw [hq, ← hx2, Nat.mod_eq_of_lt hx1', Nat.shiftRight_eq_div_pow, Int.natCast_ediv, cast]
                next => exact (refuse_ok h).elim
            next hc6 =>
              split at h
              next hc7 =>
                have fe : f = "and64" := by simpa using hc7
                subst fe
                cases hk : constOf s.facts y with
                | some m =>
                  simp only [hk] at h
                  have ym : (xb : Int) = m := by rw [hy2]; exact constOf_sound hk ρ hf
                  obtain ⟨ρ', c, hsem⟩ := symAndConst_sound h H wf xa xb ⟨hx1, hx2, hx3⟩ ym
                  exact ⟨ρ', c, (xa &&& xb) % M64, by simp [prim], hsem⟩
                | none =>
                  simp only [hk] at h
                  cases hkx : constOf s.facts x with
                  | none => simp only [hkx] at h; exact (refuse_ok h).elim
                  | some m =>
                    simp only [hkx] at h
                    have xm : (xa : Int) = m := by rw [hx2]; exact constOf_sound hkx ρ hf
                    obtain ⟨ρ', c, hsem⟩ := symAndConst_sound h H wf xb xa ⟨hy1, hy2, hy3⟩ xm
                    rw [Nat.and_comm] at hsem
                    exact ⟨ρ', c, (xa &&& xb) % M64, by simp [prim], hsem⟩
              next =>
                split at h
                next hc8 =>
                  have fe : f = "sub8" := by simpa using hc8
                  subst fe
                  have := V.pure_ok h
                  injection this with hp _
                  injection hp with h1 h2
                  subst h1 h2
                  obtain ⟨ρ1, c1, e1, b1⟩ := symLow_sound (ctx := ctx) (s0 := s0) (m := 256) H wf hy3 (by decide) (by rw [← hy2]; omega)
                  have ex : ev ρ1 x = ev ρ x := (ev_agree hx3 c1.agree).symm
                  obtain ⟨ρ2, c2, e2, b2⟩ := symLow_sound (ctx := ctx) (s0 := s0) (m := 256)
                    (x := Lin.sub (Lin.add x (Lin.const 256)) (symLow s y 256).1)
                    c1.holds c1.wf (bounded_sub (bounded_add (bounded_mono c1.mono hx3) (bounded_const _ _)) b1)
                    (by decide) (by
                      rw [ev_sub, ev_add, ev_const, ex, e1, ← hx2]
                      have := Int.emod_lt_of_pos (ev ρ y) (show (0 : Int) < 256 by decide)
                      omega)
                  refine ⟨ρ2, c1.then c2, (xa + (256 - xb % 256)) % 256, by simp [prim], ?_, ?_, b2⟩
                  · have := Nat.mod_lt (xa + (256 - xb % 256)) (show 0 < 256 by decide)
                    unfold M64; omega
                  · rw [e2, ev_sub, ev_add, ev_const, ex, e1, ← hx2, ← hy2]
                    omega
                next =>
                  split at h
                  next hc9 =>
                    have fe : f = "setlow8" := by simpa using hc9
                    subst fe
                    have := V.pure_ok h
                    injection this with hp _
                    injection hp with h1 h2
                    subst h1 h2
                    obtain ⟨ρ1, c1, e1, b1⟩ := symQuot_sound (ctx := ctx) (s0 := s0) (m := 256) H wf hx3 (by decide) (by rw [← hx2]; omega)
                    have ey : ev ρ1 y = ev ρ y := (ev_agree hy3 c1.agree).symm
                    obtain ⟨ρ2, c2, e2, b2⟩ := symLow_sound (ctx := ctx) (s0 := s0) (m := 256) (x := y) c1.holds c1.wf
                      (bounded_mono c1.mono hy3) (by decide) (by rw [ey, ← hy2]; omega)
                    have eq : ev ρ2 (symQuot s x 256).1 = ev ρ1 (symQuot s x 256).1 := (ev_agree b1 c2.agree).symm
                    refine ⟨ρ2, c1.then c2, xa % M64 / 256 * 256 + xb % 256, by simp [prim], ?_, ?_,
                      bounded_add (bounded_scale _ (bounded_mono c2.mono b1)) b2⟩
                    · unfold M64; omega
                    · rw [ev_add, ev_scale, eq, e1, e2, ey, ← hx2, ← hy2]
                      unfold M64; omega
                  next => exact (refuse_ok h).elim

theorem M64_cast : (M64 : Int) = 2 ^ 64 := by decide

/-- `on16`: in a function for AArch64 the stack pointer is a multiple of 16 where it is a multiple of 16 away
from where it was at the function's entry (there the caller has seen to it that it is one). So the
processor does not fault, and the value is the stack pointer. -/
theorem symOn16_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {x : Row} {v : EV}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symOn16 ctx s x items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (xa : Nat) (hx : EV.sem ρ s.nvars xa (.lin x)) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ ∃ z, prim "on16" [xa] = some z ∧ EV.sem ρ' s'.nvars z v := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  unfold symOn16 at h
  cases hc : Lin.isConst (Lin.sub x (Lin.var RSP)) with
  | none => simp only [hc] at h; exact (refuse_ok h).elim
  | some c =>
    simp only [hc] at h
    split at h
    next hcond =>
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have e := ev_isConst (ρ := ρ) hc
      rw [ev_sub, ev_var, H.entry RSP ctx.rsp_lt] at e
      have al := E.aligned hcond.1
      have hz : xa % 16 = 0 := by omega
      exact ⟨ρ, Carried.here H wf, xa, by simp [prim, hz], hx1, hx2, hx3⟩
    next => exact (refuse_ok h).elim

/-- A primitive of one number: what the verifier holds for it is what the account says of it; and it is no
reading of memory. -/
theorem symPrim1_sound {ctx : Ctx} {s0 : State} {f : String} {s s' : Sym} {x : Row} {v : EV} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symPrim1 f s x items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (xa : Nat) (hx : EV.sem ρ s.nvars xa (.lin x)) :
    memSize f = none ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ ∃ z, prim f [xa] = some z ∧ EV.sem ρ' s'.nvars z v := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hx1' : xa < M64 := hx1
  unfold symPrim1 at h
  split at h
  next hc =>
    have fe : f = "low32" := by simpa using hc
    subst fe
    have := V.pure_ok h
    injection this with hp _
    injection hp with h1 h2
    subst h1 h2
    obtain ⟨ρ', c, hr, br⟩ := symLow_sound (ctx := ctx) (s0 := s0) (m := 2 ^ 32) H wf hx3 (by decide) (by rw [← hx2]; omega)
    refine ⟨by decide, ρ', c, xa % 2 ^ 32, by simp [prim], Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx1', ?_, br⟩
    rw [hr, ← hx2]; omega
  next =>
    split at h
    next hc =>
      have fe : f = "low8" := by simpa using hc
      subst fe
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      obtain ⟨ρ', c, hr, br⟩ := symLow_sound (ctx := ctx) (s0 := s0) (m := 256) H wf hx3 (by decide) (by rw [← hx2]; omega)
      refine ⟨by decide, ρ', c, xa % 256, by simp [prim], Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx1', ?_, br⟩
      rw [hr, ← hx2]; omega
    next => exact (refuse_ok h).elim

theorem flagVal_none_regOf {bind : Bind} {n : String} {r : Nat} {s : State} (h : regOf bind n = some r) :
    flagVal s n = none := by
  have no : ∀ s, isRegisterLetter s = false → regIndex s = none → regOf bind s ≠ some r := by
    intro s h1 h2 he; unfold regOf at he; rw [h1] at he; simp [h2] at he
  unfold flagVal
  by_cases h1 : n = "zf"
  · subst h1; exact absurd h (no "zf" (by decide) (by decide))
  by_cases h2 : n = "nzf"
  · subst h2; exact absurd h (no "nzf" (by decide) (by decide))
  by_cases h3 : n = "cf"
  · subst h3; exact absurd h (no "cf" (by decide) (by decide))
  by_cases h4 : n = "ncf"
  · subst h4; exact absurd h (no "ncf" (by decide) (by decide))
  by_cases h5 : n = "hi"
  · subst h5; exact absurd h (no "hi" (by decide) (by decide))
  by_cases h6 : n = "nhi"
  · subst h6; exact absurd h (no "nhi" (by decide) (by decide))
  simp [h1, h2, h3, h4, h5, h6]

theorem symValue_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) :
    ∀ (e : Expr) {s s' : Sym} {v : EV} {items rest : Items} {ρ : Nat → Int} {st : State},
    symValue ctx bind s e items = .ok ((v, s'), rest) → Holds ctx s0 ρ s st → WF ctx s →
    ∃ ρ' x, Carried ctx s0 ρ s ρ' s' st ∧ value (ctx.contract.perm ctx.pieces s0) bind st e = some x ∧ EV.sem ρ' s'.nvars x v
  | .number n, s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    split at h
    next hn =>
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      exact ⟨ρ, n, Carried.here H wf, by simp [value], by unfold M64; exact hn, by simp, bounded_const _ _⟩
    next => exact (refuse_ok h).elim
  | .lane _ _, s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    exact (refuse_ok h).elim
  | .name n, s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    split at h
    next hletter =>
      cases hb : (bind.lookup n).bind readInt with
      | none => simp only [hb] at h; exact (refuse_ok h).elim
      | some i =>
        simp only [hb] at h
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        refine ⟨ρ, (i % (M64 : Int)).toNat, Carried.here H wf, by simp [value, hletter, hb], ?_, ?_, bounded_const _ _⟩
        · rw [M64_cast]; unfold M64; omega
        · rw [ev_const, M64_cast]; omega
    next hletter =>
      cases hr : ctx.regOf bind n with
      | none => simp only [hr] at h; exact (refuse_ok h).elim
      | some r =>
        simp only [hr] at h
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        obtain ⟨hr', lt⟩ := Ctx.regOf_some hr
        exact ⟨ρ, st.reg r, Carried.here H wf, by simp [value, hletter, hr', flagVal_none_regOf hr'], H.small r, H.reg r lt, wf.reg r lt⟩
  | .call f [a, b], s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    obtain ⟨⟨x, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨⟨y, s2⟩, r2, e2, h⟩ := V.bind_ok h
    obtain ⟨ρ1, xa, c1, va, sa⟩ := symValue_sound E bind a e1 H wf
    obtain ⟨ρ2, xb, c2, vb, sb⟩ := symValue_sound E bind b e2 c1.holds c1.wf
    have sa2 := EV.sem_agree sa c2.agree c2.mono
    cases x with
    | equal _ _ => exact (refuse_ok h).elim
    | below _ _ => exact (refuse_ok h).elim
    | lin x =>
      cases y with
      | equal _ _ => exact (refuse_ok h).elim
      | below _ _ => exact (refuse_ok h).elim
      | lin y =>
        simp only at h
        cases hm : memSize f with
        | some size =>
          simp only [hm] at h
          have sx := signed_ev ρ2 x
          have sy := signed_ev ρ2 y
          have hx1 := sa2.1
          have hy1 := sb.1
          unfold M64 at hx1 hy1
          have hmod : (((xa + (xb + 0)) % M64 : Nat) : Int) % 2 ^ 64 = ev ρ2 (Lin.add (signed x) (signed y)) % 2 ^ 64 := by
            rw [ev_add]; unfold M64; have := sa2.2.1; have := sb.2.1; omega
          obtain ⟨ρ3, c3, al, sv⟩ := symLoad_sound E h c2.holds c2.wf (bounded_add (bounded_signed sa2.2.2) (bounded_signed sb.2.2))
            ((xa + (xb + 0)) % M64) (Nat.mod_lt _ (by decide)) hmod
          exact ⟨ρ3, _, (c1.then c2).then c3, by simp only [value, values, va, vb, hm, sumList, al, if_true], sv⟩
        | none =>
          simp only [hm] at h
          split at h
          next hor =>
            have fe : f = "or64" := by simpa using hor
            obtain ⟨ρ3, c3, lt, sem⟩ := symOr_sound h c2.holds c2.wf xa xb sa2 sb
            have hz : prim f [xa, xb] = some ((xa ||| xb) % M64) := by rw [fe]; simp [prim]
            have hnd : (f == "data") = false := by rw [fe]; decide
            refine ⟨ρ3, (xa ||| xb) % M64, (c1.then c2).then c3, by simp only [value, values, va, vb, hm, hz, hnd, Bool.false_eq_true, if_false], ?_⟩
            rw [Nat.mod_eq_of_lt lt]; exact sem
          next =>
            obtain ⟨ρ3, c3, z, hz, sz⟩ := symPrim_sound h c2.holds c2.wf xa xb sa2 sb
            have hnd : (f == "data") = false := by
              cases hd : (f == "data") with
              | false => rfl
              | true => have fe : f = "data" := by simpa using hd
                        rw [fe] at hz; simp [prim] at hz
            exact ⟨ρ3, z, (c1.then c2).then c3, by simp only [value, values, va, vb, hm, hz, hnd, Bool.false_eq_true, if_false], sz⟩
  | .call f [], s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    exact (refuse_ok h).elim
  | .call f [a], s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    obtain ⟨⟨x, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨ρ1, xa, c1, va, sa⟩ := symValue_sound E bind a e1 H wf
    cases x with
    | equal _ _ => exact (refuse_ok h).elim
    | below _ _ => exact (refuse_ok h).elim
    | lin x =>
      simp only at h
      split at h
      next hdta =>
        -- `data(I)`: the address of a place in the file's data
        have fe : f = "data" := by simpa using hdta
        obtain ⟨hx1, hx2, hx3⟩ := sa
        unfold symData at h
        split at h
        next hpiece =>
          -- (the instruction takes the address in the data of the function's own file)
          cases hc : Lin.isConst x with
          | none => simp only [hc] at h; exact (refuse_ok h).elim
          | some c =>
            simp only [hc] at h
            by_cases hin : 0 ≤ c ∧ c < (ctx.data.length : Int)
            · rw [if_pos hin] at h
              have := V.pure_ok h
              injection this with hp _
              injection hp with hv hs
              subst hv hs
              have hd : ctx.data ≠ [] := by
                intro e
                rw [e] at hin
                simp only [List.length_nil] at hin
                omega
              obtain ⟨k, _, hk, _, _⟩ := Ctx.data_piece hd
              have hpb : pieceOf bind = some k := hpiece.trans hk
              have ec := ev_isConst (ρ := ρ1) hc
              have fit := E.data_fits hd
              have pin := c1.holds.data
              have pin1 : ρ1 (dataVar ctx) = ctx.own s0 := pin.1
              rw [Ctx.own_eq hk] at fit pin1
              refine ⟨ρ1, (st.data k + sumList [xa]) % M64, c1, by simp [value, values, va, memSize, fe, hpb], Nat.mod_lt _ (by decide), ?_,
                bounded_add (bounded_var (x := dataVar ctx) c1.wf.base) (bounded_const _ _)⟩
              rw [ev_add, ev_var, ev_const, pin1, pin.2]
              simp only [sumList]
              unfold M64 at *
              omega
            · rw [if_neg hin] at h; exact (refuse_ok h).elim
        next => exact (refuse_ok h).elim
      next hnd0 =>
        have hnd : (f == "data") = false := by simpa using hnd0
        split at h
        next hon =>
          -- `on16(sp)`: the stack pointer as the base of a load or store
          have fe : f = "on16" := by simpa using hon
          obtain ⟨ρ2, c2, z, hz, sz⟩ := symOn16_sound E h c1.holds c1.wf xa sa
          subst fe
          have hm : memSize "on16" = none := by decide
          exact ⟨ρ2, z, c1.then c2, by simp only [value, values, va, hm, hz, hnd, Bool.false_eq_true, if_false], sz⟩
        next =>
          obtain ⟨hm, ρ2, c2, z, hz, sz⟩ := symPrim1_sound h c1.holds c1.wf xa sa
          exact ⟨ρ2, z, c1.then c2, by simp only [value, values, va, hm, hz, hnd, Bool.false_eq_true, if_false], sz⟩
  | .call f (_ :: _ :: _ :: _), s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    exact (refuse_ok h).elim

/-! ## A statement of an effect -/

theorem Holds.setZf {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (f : Flag) (b : Bool) (hf : f.holds ρ b) : Holds ctx s0 ρ { s with zf := f } { st with zf := b } :=
  ⟨H.entry, H.data, H.reg, H.small, hf, H.cf, H.frame, H.frameW, H.facts, H.bytes, H.spec, H.mem, H.wrote, H.words, H.known, H.range, H.vecIntact⟩

theorem Holds.setCf {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (f : Flag) (b : Bool) (hf : f.holds ρ b) : Holds ctx s0 ρ { s with cf := f } { st with cf := b } :=
  ⟨H.entry, H.data, H.reg, H.small, H.zf, hf, H.frame, H.frameW, H.facts, H.bytes, H.spec, H.mem, H.wrote, H.words, H.known, H.range, H.vecIntact⟩

theorem WF.setZf {s : Sym} (wf : WF ctx s) (f : Flag) (hb : f.bounded s.nvars) : WF ctx { s with zf := f } :=
  ⟨wf.base, wf.reg, hb, wf.cf, wf.frame, wf.frameW, wf.facts, wf.bytes, wf.spec, wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, wf.range⟩

theorem WF.setCf {s : Sym} (wf : WF ctx s) (f : Flag) (hb : f.bounded s.nvars) : WF ctx { s with cf := f } :=
  ⟨wf.base, wf.reg, wf.zf, hb, wf.frame, wf.frameW, wf.facts, wf.bytes, wf.spec, wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, wf.range⟩

theorem Holds.put {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (r x : Nat) (xr : Row) (hx : x < M64) (hxr : (x : Int) = ev ρ xr) : Holds ctx s0 ρ (s.put r xr) (setReg st r x) where
  range := H.range
  vecIntact := H.vecIntact
  entry := H.entry
  data := H.data
  reg r' hr' := by
    simp only [Sym.put, setReg]
    split
    · rw [Nat.mod_eq_of_lt hx]; exact hxr
    · exact H.reg r' hr'
  small r' := by
    simp only [setReg]
    split
    · exact Nat.mod_lt _ (by decide)
    · exact H.small r'
  zf := H.zf
  cf := H.cf
  frame := H.frame
  frameW := H.frameW
  facts := H.facts
  bytes := H.bytes
  spec := H.spec
  mem := H.mem
  wrote := H.wrote
  words := H.words
  known := H.known

theorem WF.put {s : Sym} (wf : WF ctx s) (r : Nat) (xr : Row) (hb : bounded s.nvars xr) : WF ctx (s.put r xr) where
  range := wf.range
  base := wf.base
  reg r' hr' := by
    simp only [Sym.put]
    split
    · exact hb
    · exact wf.reg r' hr'
  zf := wf.zf
  cf := wf.cf
  frame := wf.frame
  frameW := wf.frameW
  facts := wf.facts
  bytes := wf.bytes
  spec := wf.spec
  wrote := wf.wrote
  words := wf.words.mono rfl rfl rfl (Nat.le_refl _)
  known := wf.known

theorem Flag.equal_holds {ρ : Nat → Int} {a b : Row} {x : Nat} (h : x = if ev ρ a = ev ρ b then 1 else 0) :
    (Flag.equal a b).holds ρ (x != 0) := by
  simp only [Flag.holds]
  by_cases e : ev ρ a = ev ρ b <;> simp [h, e]

theorem Flag.below_holds {ρ : Nat → Int} {a b : Row} {x : Nat} (h : x = if ev ρ a < ev ρ b then 1 else 0) :
    (Flag.below a b).holds ρ (x != 0) := by
  simp only [Flag.holds]
  by_cases e : ev ρ a < ev ρ b <;> simp [h, e]

/-- Eight bytes of the frame written. -/
theorem Holds.write {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (c : Int) (h1 : -(ctx.contract.stack : Int) ≤ c) (h2 : c + 8 ≤ 0)
    (a : Nat) (ha : (a : Int) = (s0.reg RSP : Int) + c) (x : Nat) (xr : Row) (hx : x < M64) (hxr : (x : Int) = ev ρ xr) :
    Holds ctx s0 ρ { s with spill := [],
                            frame := (c, xr) :: s.frame.filter fun (o, _) => decide (o + 8 ≤ c) || decide (c + 8 ≤ o),
                            frameW := s.frameW.filter fun (o, _) => decide (o + 4 ≤ c) || decide (c + 8 ≤ o) }
      { st with mem := store st.mem a x 8 } where
  range rg hrg := by
    obtain ⟨name, r, n, params, bx, bb, hi, g1, g2, g3, g4, g5⟩ := H.range rg hrg
    refine ⟨name, r, n, params, bx, bb, hi, g1, g2, g3, g4, fun j hj1 hj2 => ?_⟩
    have hs := E.stack
    have ho := (E.out (List.mem_of_getElem? g1)).2
    show Value ctx.defs _ bb (.int (store st.mem a x 8 (s0.reg r + j)))
    rw [store_other _ _ _ _ _ (by omega)]
    exact g5 j hj1 hj2
  vecIntact := H.vecIntact
  entry := H.entry
  data := H.data
  reg := H.reg
  small := H.small
  zf := H.zf
  cf := H.cf
  facts := H.facts
  bytes := H.bytes
  spec := H.spec
  frame o v m := by
    have hs := E.stackAt
    have hle := Contract.stack_le_stackAt ctx.contract s0
    simp only [List.mem_cons] at m
    rcases m with heq | m
    · injection heq with e1 e2
      subst e1 e2
      refine ⟨by omega, h2, ?_⟩
      have : ((s0.reg RSP : Int) + o).toNat = a := by omega
      rw [this, load_store_same _ _ _ _ (by rw [pow8]; exact hx)]
      exact hxr
    · obtain ⟨m, hk⟩ := List.mem_filter.mp m
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
      obtain ⟨g1, g2, g3⟩ := H.frame o v m
      refine ⟨g1, g2, ?_⟩
      rw [load_store_other _ _ _ _ _ _ (by omega)]
      exact g3
  frameW o i m := by
    have hs := E.stackAt
    obtain ⟨m, hk⟩ := List.mem_filter.mp m
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
    obtain ⟨g1, g2, g3⟩ := H.frameW o i m
    refine ⟨g1, g2, ?_⟩
    rw [load_store_other _ _ _ _ _ _ (by omega)]
    exact g3
  mem x' hx' ho := by
    have hs := E.stack
    have hle := Contract.stack_le_stackAt ctx.contract s0
    simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hx'
    show store st.mem a x 8 x' = s0.mem x'
    rw [store_other _ _ _ _ _ (by omega)]
    apply H.mem _ _ ho
    simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact hx'
  wrote w o v m := by
    obtain ⟨name, r, n, g1, g2, g3, g4⟩ := H.wrote w o v m
    refine ⟨name, r, n, g1, g2, g3, ?_⟩
    have hs := E.stack
    have ho := (E.out (List.mem_of_getElem? g1)).2
    show (store st.mem a x 8 (s0.reg r + (ev ρ o).toNat) : Int) = ev ρ v
    rw [store_other _ _ _ _ _ (by omega)]
    exact g4
  words := by
    have hs := E.stack
    refine ⟨H.words.vec, ?_, ?_, (fun _ _ h => nomatch h)⟩
    · intro w m x' r n g1 k hk
      have ho := (E.out (List.mem_of_getElem? g1)).2
      show store st.mem a x 8 (s0.reg r + k) = s0.mem (s0.reg r + k)
      rw [store_other _ _ _ _ _ (by omega)]
      exact H.words.intact w m x' r n g1 k hk
    · intro w j i m x' r n g1
      obtain ⟨g2, g3⟩ := H.words.wrote w j i m x' r n g1
      have ho := (E.out (List.mem_of_getElem? g1)).2
      refine ⟨g2, fun b hb => ?_⟩
      show (store st.mem a x 8 (s0.reg r + 4 * j + b)).val = _
      rw [store_other _ _ _ _ _ (by omega)]
      exact g3 b hb
  known := H.known

theorem WF.write {s : Sym} (wf : WF ctx s) (c : Int) (xr : Row) (hb : bounded s.nvars xr) :
    WF ctx { s with spill := [],
                    frame := (c, xr) :: s.frame.filter fun (o, _) => decide (o + 8 ≤ c) || decide (c + 8 ≤ o),
                    frameW := s.frameW.filter fun (o, _) => decide (o + 4 ≤ c) || decide (c + 8 ≤ o) } where
  range := wf.range
  base := wf.base
  reg := wf.reg
  zf := wf.zf
  cf := wf.cf
  facts := wf.facts
  bytes := wf.bytes
  spec := wf.spec
  wrote := wf.wrote
  frame o v m := by
    simp only [List.mem_cons] at m
    rcases m with heq | m
    · injection heq with e1 e2; subst e2; exact hb
    · exact wf.frame o v (List.mem_filter.mp m).1
  frameW o i m := wf.frameW o i (List.mem_filter.mp m).1
  words := wf.words.mono rfl rfl rfl (Nat.le_refl _)
  known := wf.known

/-- One byte written into a run given to write lies outside the tracked range. -/
theorem belowRange_sound {s : Sym} {w : Nat} {o : Row} {items : Items} {r : Unit × Items} {ρ : Nat → Int}
    (h : belowRange s w o items = .ok r) (hf : ∀ f ∈ s.facts, f.holds ρ) :
    ∀ rg, s.range = some rg → rg.w = w →
      if rg.fromStart then ev ρ rg.lo ≤ ev ρ o else ev ρ o + 1 ≤ ev ρ rg.lo := by
  intro rg hr hw
  simp only [belowRange, hr, hw, beq_self_eq_true, if_true] at h
  cases hfs : rg.fromStart <;> simp only [hfs, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · have := entail_sound h ρ hf
    simp only [ev_sub, ev_const] at this
    omega
  · have := entail_sound h ρ hf
    simp only [ev_sub] at this
    omega

theorem Holds.writeOut {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) {w : Nat} {name : String} {r n : Nat} (hw : ctx.contract.outs[w]? = some (name, r, n))
    (o xr : Row) (h1 : 0 ≤ ev ρ o) (h2 : ev ρ o < n) (x : Nat) (hx : x < 256) (hxr : (x : Int) = ev ρ xr)
    {rest : List (Nat × Row × Row)} (hk : keepWrote w o s.wrote = some rest)
    (hnw : (s.wroteW.any fun e => e.1 == w) = false)
    (a : Nat) (ha : a = s0.reg r + (ev ρ o).toNat)
    (below : ∀ rg, s.range = some rg → rg.w = w →
      if rg.fromStart then ev ρ rg.lo ≤ ev ρ o else ev ρ o + 1 ≤ ev ρ rg.lo) :
    Holds ctx s0 ρ { s with wrote := (w, o, xr) :: rest, intact := s.intact.filter (· != w), spill := [] }
      { st with mem := store st.mem a x 1 } where
  vecIntact := H.vecIntact
  range rg hr := by
    obtain ⟨name', r', n', params, y, b, hi, g1, g2, g3, g4, g5⟩ := H.range rg hr
    refine ⟨name', r', n', params, y, b, hi, g1, g2, g3, g4, fun j lo hj => ?_⟩
    show Value ctx.defs _ b (.int (store st.mem a x 1 (s0.reg r' + j)))
    have hne : s0.reg r' + j < a ∨ a + 1 ≤ s0.reg r' + j := by
      by_cases e : rg.w = w
      · have hb := below rg hr e
        rw [e, hw] at g1
        injection g1 with g1; injection g1 with _ g1; injection g1 with g1 gn
        subst g1 gn
        cases hfs : rg.fromStart <;> simp only [hfs, Bool.false_eq_true, ↓reduceIte] at hb lo <;> omega
      · have := E.outOut hw g1 (Ne.symm e)
        omega
    rw [store_other _ _ _ _ _ hne]
    exact g5 j lo hj
  entry := H.entry
  data := H.data
  reg := H.reg
  small := H.small
  zf := H.zf
  cf := H.cf
  facts := H.facts
  spec := H.spec
  bytes := H.bytes
  frame o' v m := by
    obtain ⟨g1, g2, g3⟩ := H.frame o' v m
    refine ⟨g1, g2, ?_⟩
    have hs := E.stackAt
    have ho := (E.outAt (List.mem_of_getElem? hw)).2
    rw [load_store_other _ _ _ _ _ _ (by omega)]
    exact g3
  mem x' hx' ho' := by
    show store st.mem a x 1 x' = s0.mem x'
    have hne : x' ≠ a := by
      intro e
      have : ctx.contract.inOut s0 x' = true := by
        unfold Contract.inOut
        exact List.any_eq_true.mpr ⟨(name, r, n), List.mem_of_getElem? hw, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
      rw [this] at ho'; cases ho'
    rw [store_other _ _ _ _ _ (by omega)]
    exact H.mem x' hx' ho'
  wrote w' o' v m := by
    rcases List.mem_cons.mp m with e | m
    · injection e with e1 e2; injection e2 with e2 e3; subst e1 e2 e3
      refine ⟨name, r, n, hw, h1, h2, ?_⟩
      show (store st.mem a x 1 (s0.reg r + (ev ρ o').toNat) : Int) = ev ρ v
      rw [← ha, ← hxr]
      simp only [store, if_pos]
      omega
    · obtain ⟨m', apart⟩ := keepWrote_spec hk w' o' v m
      obtain ⟨name', r', n', g1, g2, g3, g4⟩ := H.wrote w' o' v m'
      refine ⟨name', r', n', g1, g2, g3, ?_⟩
      show (store st.mem a x 1 (s0.reg r' + (ev ρ o').toNat) : Int) = ev ρ v
      have hne : s0.reg r' + (ev ρ o').toNat < a ∨ a + 1 ≤ s0.reg r' + (ev ρ o').toNat := by
        rcases apart with ne | ⟨eq, k, hk', kne⟩
        · have := E.outOut hw g1 (Ne.symm ne)
          omega
        · subst eq
          rw [hw] at g1
          injection g1 with g1; injection g1 with _ g1; injection g1 with g1 gn
          subst g1 gn
          have e := ev_isConst (ρ := ρ) hk'
          simp only [ev_sub] at e
          omega
      rw [store_other _ _ _ _ _ hne]
      exact g4
  words := by
    refine ⟨H.words.vec, ?_, ?_, (fun _ _ h => nomatch h)⟩
    · intro w' m x' r' n' g1 k hk'
      obtain ⟨m', ne⟩ := List.mem_filter.mp m
      have ne' : w' ≠ w := by simpa using ne
      have := E.outOut hw g1 (Ne.symm ne')
      show store st.mem a x 1 (s0.reg r' + k) = s0.mem (s0.reg r' + k)
      rw [store_other _ _ _ _ _ (by omega)]
      exact H.words.intact w' m' x' r' n' g1 k hk'
    · intro w' j i m x' r' n' g1
      obtain ⟨g2, g3⟩ := H.words.wrote w' j i m x' r' n' g1
      have ne' : w' ≠ w := by
        intro e
        rw [e] at m
        exact (List.any_eq_false.mp hnw) _ m (by simp)
      have := E.outOut hw g1 (Ne.symm ne')
      refine ⟨g2, fun b hb => ?_⟩
      show (store st.mem a x 1 (s0.reg r' + 4 * j + b)).val = _
      rw [store_other _ _ _ _ _ (by omega)]
      exact g3 b hb
  frameW o i m := by
    obtain ⟨g1, g2, g3⟩ := H.frameW o i m
    have hs := E.stackAt
    have ho := (E.outAt (List.mem_of_getElem? hw)).2
    refine ⟨g1, g2, ?_⟩
    rw [load_store_other _ _ _ _ _ _ (by omega)]
    exact g3
  known := H.known

theorem WF.writeOut {s : Sym} (wf : WF ctx s) {w : Nat} {o xr : Row} (ho : bounded s.nvars o) (hx : bounded s.nvars xr)
    {rest : List (Nat × Row × Row)} (hk : keepWrote w o s.wrote = some rest) :
    WF ctx { s with wrote := (w, o, xr) :: rest, intact := s.intact.filter (· != w), spill := [] } where
  range := wf.range
  base := wf.base
  reg := wf.reg
  zf := wf.zf
  cf := wf.cf
  frame := wf.frame
  frameW := wf.frameW
  facts := wf.facts
  bytes := wf.bytes
  spec := wf.spec
  wrote w' o' v m := by
    rcases List.mem_cons.mp m with e | m
    · injection e with e1 e2; injection e2 with e2 e3; subst e2 e3; exact ⟨ho, hx⟩
    · exact wf.wrote w' o' v (keepWrote_spec hk w' o' v m).1
  words := wf.words.mono rfl rfl rfl (Nat.le_refl _)
  known := wf.known

theorem values_two {perm : Perm} {bind : Bind} {st : State} {a b : Expr} {xa xb : Nat}
    (h1 : value perm bind st a = some xa) (h2 : value perm bind st b = some xb) : values perm bind st [a, b] = some [xa, xb] := by
  simp [values, h1, h2]

theorem frameOffset_eval {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} (H : Holds ctx s0 ρ s st) (addr : Row) :
    ev ρ (frameOffset addr) = ev ρ addr - s0.reg RSP := by
  simp only [frameOffset, ev_sub, ev_var, H.entry RSP ctx.rsp_lt]

theorem frameSpan_sound {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym} {addr : Row} {n : Nat}
    (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) (ok : ∀ g ∈ frameSpanGoals ctx s addr n, g.holds ρ) :
    ∃ a : Nat, (a : Int) = ev ρ addr ∧ a < M64 ∧ s0.reg RSP - ctx.contract.stack ≤ a ∧ a + n ≤ s0.reg RSP := by
  let o := frameOffset addr
  have lo := ok (Lin.add o (Lin.const ctx.contract.stack)) (by simp [frameSpanGoals, o])
  have hi := ok (Lin.sub (Lin.const (-(n : Int))) o) (by simp [frameSpanGoals, o])
  simp only [holds_iff, ev_add, ev_sub, ev_const, o, frameOffset_eval H] at lo hi
  have hs := E.stack
  have hl := E.small RSP
  exact ⟨(ev ρ addr).toNat, by omega, by omega, by omega, by omega⟩

theorem frameSpan_perm {ctx : Ctx} {s0 : State} {a n : Nat}
    (lo : s0.reg RSP - ctx.contract.stack ≤ a) (hi : a + n ≤ s0.reg RSP) :
    allowed (ctx.contract.perm ctx.pieces s0).read a n = true ∧ allowed (ctx.contract.perm ctx.pieces s0).write a n = true := by
  have hle := Contract.stack_le_stackAt ctx.contract s0
  have inside (x : Nat) (hx : a ≤ x) (hy : x < a + n) : ctx.contract.inFrame s0 x = true := by
    simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact ⟨allowed_of _ _ _ (fun x h1 h2 => by simp [Contract.perm, inside x h1 h2]),
    allowed_of _ _ _ (fun x h1 h2 => by simp [Contract.perm, inside x h1 h2])⟩

/-- A store wholly inside the frame and below the saved scalar words does not affect other regions. -/
theorem Holds.frameSpanWrite {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym}
    (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) {mem' : Nat → Byte} {a n : Nat} {spill : List (Row × List Nat)}
    (lo : s0.reg RSP - ctx.contract.stack ≤ a) (hi : a + n ≤ s0.reg RSP)
    (apart : ∀ o v, (o, v) ∈ s.frame → a + n ≤ ((s0.reg RSP : Int) + o).toNat)
    (same : ∀ y, y < a ∨ a + n ≤ y → mem' y = st.mem y)
    (saved : ∀ o ids, (o, ids) ∈ spill → 0 ≤ (s0.reg RSP : Int) + ev ρ o ∧ ∀ k, k < ids.length →
      load mem' (((s0.reg RSP : Int) + ev ρ o).toNat + 4 * k) 4 = den (inpOf ctx s0) ρ s.terms (ids.getD k 0)) :
    Holds ctx s0 ρ { s with spill := spill, frameW := [], range := none } { st with mem := mem' } where
  range := fun _ h => nomatch h
  vecIntact := H.vecIntact
  entry := H.entry
  data := H.data
  reg := H.reg
  small := H.small
  zf := H.zf
  cf := H.cf
  facts := H.facts
  bytes := H.bytes
  spec := H.spec
  frameW := fun _ _ h => nomatch h
  frame o v m := by
    obtain ⟨h1, h2, h3⟩ := H.frame o v m
    have space := apart o v m
    have e := load_congr mem' st.mem ((s0.reg RSP : Int) + o).toNat 8 (fun y hy _ => same y (Or.inr (by omega)))
    exact ⟨h1, h2, by rw [e]; exact h3⟩
  mem y outside hout := by
    have out := outside
    have hle := Contract.stack_le_stackAt ctx.contract s0
    simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at out
    show mem' y = s0.mem y
    rw [same y (by omega)]
    exact H.mem y outside hout
  wrote w o x m := by
    obtain ⟨nm, r, count, hr, h1, h2, val⟩ := H.wrote w o x m
    have disjoint := (E.out (List.mem_of_getElem? hr)).2
    refine ⟨nm, r, count, hr, h1, h2, ?_⟩
    show (mem' (s0.reg r + (ev ρ o).toNat) : Int) = ev ρ x
    rw [same _ (by omega)]
    exact val
  words := by
    refine ⟨H.words.vec, ?_, ?_, saved⟩
    · intro w m x r count hr k hk
      have disjoint := (E.out (List.mem_of_getElem? hr)).2
      show mem' (s0.reg r + k) = s0.mem (s0.reg r + k)
      rw [same _ (by omega)]
      exact H.words.intact w m x r count hr k hk
    · intro w j i m x r count hr
      obtain ⟨within, hh⟩ := H.words.wrote w j i m x r count hr
      have disjoint := (E.out (List.mem_of_getElem? hr)).2
      refine ⟨within, fun b hb => ?_⟩
      show (mem' (s0.reg r + 4 * j + b)).val = _
      rw [same _ (by omega)]
      exact hh b hb
  known := H.known

theorem savedWordSpan_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {addr : Row} {a n : Nat}
    (H : Holds ctx s0 ρ s st) (ea : (a : Int) = ev ρ addr) (ok : ∀ g ∈ savedWordGoals s addr n, g.holds ρ) :
    ∀ o v, (o, v) ∈ s.frame → a + n ≤ ((s0.reg RSP : Int) + o).toNat := by
  intro o v m
  have hh := ok (Lin.sub (Lin.const (o - n)) (frameOffset addr)) (List.mem_map.mpr ⟨(o, v), m, rfl⟩)
  simp only [holds_iff, ev_sub, ev_const, frameOffset_eval H, ← ea] at hh
  omega

theorem symTouchFrame_sound {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s s' : Sym} {addr : Row}
    {items rest : Items} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (h : symTouchFrame ctx s addr items = .ok (s', rest)) (a x : Nat)
    (matchAddr : ∀ A : Nat, (A : Int) = ev ρ addr → A < M64 → a = A) :
    allowed (ctx.contract.perm ctx.pieces s0).write a 1 = true ∧ Carried ctx s0 ρ s ρ s' { st with mem := store st.mem a x 1 } := by
  unfold symTouchFrame at h
  obtain ⟨_, _, hc, h1⟩ := V.bind_ok h
  obtain ⟨_, _, hd, he⟩ := V.bind_ok h1
  have hs := V.pure_ok he
  injection hs with eq _; subst s'
  obtain ⟨A, ea, lt, lo, hi⟩ := frameSpan_sound E H (entails_sound H.facts hc)
  have e := matchAddr A ea lt
  subst a
  refine ⟨(frameSpan_perm (ctx := ctx) lo hi).2, ⟨Agree.refl _ _, Nat.le_refl _, ?_, ?_⟩⟩
  · exact H.frameSpanWrite E lo hi (savedWordSpan_sound H ea (entails_sound H.facts hd))
      (fun y hy => store_other _ _ _ _ _ hy) (fun _ _ h => nomatch h)
  · exact ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, (fun _ _ h => nomatch h), wf.facts, wf.bytes, wf.spec, wf.wrote,
      wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, fun _ h => nomatch h⟩

theorem symStmt_scalar {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) {s s' : Sym} {stmt : Stmt}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symStmt ctx bind s stmt items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (base u : Nat)
    (hv : ∀ place v, stmt ≠ .vset place v) (hw : ∀ place v, stmt ≠ .vset512 place v)
    -- (a store of eight bytes as two words of a run: its rule is shown where the words of runs are, SoundCallW.lean)
    (h8 : ∀ {s s' : Sym} {w n base : Nat} {name : String} {o xr : Row} {items rest : Items} {ρ : Nat → Int} {st : State} (a x : Nat),
      symStore8 ctx s w n o xr items = .ok (s', rest) → Holds ctx s0 ρ s st → WF ctx s →
      ctx.contract.outs[w]? = some (name, base, n) →
      (∀ c : Int, ev ρ o = c → 0 ≤ c → c + 8 ≤ n → a = s0.reg base + c.toNat) →
      EV.sem ρ s.nvars x (.lin xr) →
      allowed (ctx.contract.perm ctx.pieces s0).write a 8 = true ∧
        ∃ ρ', Carried ctx s0 ρ s ρ' s' { st with mem := store st.mem a x 8 }) :
    ∃ ρ' st', Carried ctx s0 ρ s ρ' s' st' ∧ execStmt (ctx.contract.perm ctx.pieces s0) bind base u st stmt = some st' ∧ st'.rip = st.rip := by
  cases stmt with
  | nothing =>
    simp only [symStmt] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨ρ, st, Carried.here H wf, rfl, rfl⟩
  | ret => simp only [symStmt] at h; exact (refuse_ok h).elim
  | call t => simp only [symStmt] at h; exact (refuse_ok h).elim
  | retLink r => simp only [symStmt] at h; exact (refuse_ok h).elim
  | callLink t r => simp only [symStmt] at h; exact (refuse_ok h).elim
  | jump t c => simp only [symStmt] at h; exact (refuse_ok h).elim
  | vset place v => exact (hv place v rfl).elim
  | vset512 place v => exact (hw place v rfl).elim
  | set place v =>
    simp only [symStmt] at h
    split at h
    next hu =>
      cases place with
      | number _ => exact (refuse_ok h).elim
      | lane _ _ => exact (refuse_ok h).elim
      | call _ _ => exact (refuse_ok h).elim
      | name n =>
        simp only at h
        split at h
        next hz =>
          have := V.pure_ok h
          injection this with h1 _
          subst h1
          exact ⟨ρ, { st with zf := u != 0 }, ⟨Agree.refl _ _, Nat.le_refl _, H.setZf .unknown _ trivial, wf.setZf .unknown trivial⟩,
            by simp [execStmt, hu, hz], rfl⟩
        next hz =>
          split at h
          next hc =>
            have := V.pure_ok h
            injection this with h1 _
            subst h1
            exact ⟨ρ, { st with cf := u != 0 }, ⟨Agree.refl _ _, Nat.le_refl _, H.setCf .unknown _ trivial, wf.setCf .unknown trivial⟩,
              by simp [execStmt, hu, hz, hc], rfl⟩
          next => exact (refuse_ok h).elim
    next hu =>
      obtain ⟨⟨ev, s1⟩, r1, e1, h⟩ := V.bind_ok h
      obtain ⟨ρ1, x, c1, vx, sx⟩ := symValue_sound E bind v e1 H wf
      cases place with
      | number _ => exact (refuse_ok h).elim
      | lane _ _ => exact (refuse_ok h).elim
      | name n =>
        simp only at h
        split at h
        next hz =>
          cases ev with
          | lin _ => exact (refuse_ok h).elim
          | equal a b =>
            have := V.pure_ok h
            injection this with h1 _
            subst h1
            exact ⟨ρ1, { st with zf := x != 0 }, ⟨c1.agree, c1.mono, c1.holds.setZf _ _ (Flag.equal_holds sx.1), c1.wf.setZf _ sx.2⟩,
              by simp [execStmt, hu, hz, vx], rfl⟩
          | below a b =>
            have := V.pure_ok h
            injection this with h1 _
            subst h1
            exact ⟨ρ1, { st with zf := x != 0 }, ⟨c1.agree, c1.mono, c1.holds.setZf _ _ (Flag.below_holds sx.1), c1.wf.setZf _ sx.2⟩,
              by simp [execStmt, hu, hz, vx], rfl⟩
        next hz =>
          split at h
          next hc =>
            cases ev with
            | lin _ => exact (refuse_ok h).elim
            | equal a b =>
              have := V.pure_ok h
              injection this with h1 _
              subst h1
              exact ⟨ρ1, { st with cf := x != 0 }, ⟨c1.agree, c1.mono, c1.holds.setCf _ _ (Flag.equal_holds sx.1), c1.wf.setCf _ sx.2⟩,
                by simp [execStmt, hu, hz, hc, vx], rfl⟩
            | below a b =>
              have := V.pure_ok h
              injection this with h1 _
              subst h1
              exact ⟨ρ1, { st with cf := x != 0 }, ⟨c1.agree, c1.mono, c1.holds.setCf _ _ (Flag.below_holds sx.1), c1.wf.setCf _ sx.2⟩,
                by simp [execStmt, hu, hz, hc, vx], rfl⟩
          next hc =>
            cases hr : regOf bind n with
            | none => simp only [hr] at h; exact (refuse_ok h).elim
            | some r =>
              cases ev with
              | equal _ _ => simp only [hr] at h; exact (refuse_ok h).elim
              | below _ _ => simp only [hr] at h; exact (refuse_ok h).elim
              | lin xr =>
                simp only [hr] at h
                have := V.pure_ok h
                injection this with h1 _
                subst h1
                exact ⟨ρ1, setReg st r x, ⟨c1.agree, c1.mono, c1.holds.put r x xr sx.1 sx.2.1, c1.wf.put r xr sx.2.2⟩,
                  by simp [execStmt, hu, hz, hc, vx, hr], rfl⟩
      | call f args =>
        cases args with
        | nil => exact (refuse_ok h).elim
        | cons a more =>
          cases more with
          | nil => exact (refuse_ok h).elim
          | cons b more2 =>
            cases more2 with
            | cons _ _ => exact (refuse_ok h).elim
            | nil =>
              simp only at h
              obtain ⟨⟨ea, s2⟩, r2, e2, h⟩ := V.bind_ok h
              obtain ⟨⟨eb, s3⟩, r3, e3, h⟩ := V.bind_ok h
              obtain ⟨ρ2, xa, c2, va, sa⟩ := symValue_sound E bind a e2 c1.holds c1.wf
              obtain ⟨ρ3, xb, c3, vb, sb⟩ := symValue_sound E bind b e3 c2.holds c2.wf
              have sx3 := EV.sem_agree (EV.sem_agree sx c2.agree c2.mono) c3.agree c3.mono
              have sa3 := EV.sem_agree sa c3.agree c3.mono
              cases ev with
              | equal _ _ => exact (refuse_ok h).elim
              | below _ _ => exact (refuse_ok h).elim
              | lin xr =>
                cases ea with
                | equal _ _ => exact (refuse_ok h).elim
                | below _ _ => exact (refuse_ok h).elim
                | lin ar =>
                  cases eb with
                  | equal _ _ => exact (refuse_ok h).elim
                  | below _ _ => exact (refuse_ok h).elim
                  | lin br =>
                    simp only at h
                    cases hl : locate ctx (Lin.add (signed ar) (signed br)) with
                    | none =>
                      simp only [hl] at h
                      split at h
                      next hs =>
                        have sgx := signed_ev ρ3 ar
                        have sgy := signed_ev ρ3 br
                        have hx := sa3.1
                        have hy := sb.1
                        have ex := sa3.2.1
                        have ey := sb.2.1
                        obtain ⟨perm, c4⟩ := symTouchFrame_sound E c3.holds c3.wf h ((xa + xb) % M64) x (by
                          intro A ea lt
                          rw [ev_add] at ea
                          unfold M64 at hx hy lt ⊢
                          omega)
                        refine ⟨ρ3, _, c1.then (c2.then (c3.then c4)), ?_, rfl⟩
                        simp [execStmt, hu, vx, hs.1, values_two va vb, sumList, perm]
                      next => exact (refuse_ok h).elim
                    | some w =>
                      cases w with
                      | region _ _ => simp only [hl] at h; exact (refuse_ok h).elim
                      | data _ => simp only [hl] at h; exact (refuse_ok h).elim      -- (the file's data is not written)
                      | out w o =>
                        simp only [hl] at h
                        obtain ⟨name, base, n, hw, ho⟩ := locate_out hl
                        simp only [hw] at h
                        split at h
                        next hsize =>
                          obtain ⟨_, r4, g1, h⟩ := V.bind_ok h
                          obtain ⟨_, r5, g2, h⟩ := V.bind_ok h
                          obtain ⟨_, r6, g3, h⟩ := V.bind_ok h
                          obtain ⟨_, r7, g4, h⟩ := V.bind_ok h
                          have hnw : (s3.wroteW.any fun e => e.1 == w) = false := by
                            cases hnw : (s3.wroteW.any fun e => e.1 == w) with
                            | false => rfl
                            | true => simp only [hnw, ↓reduceIte] at h; exact (refuse_ok h).elim
                          simp only [hnw, Bool.false_eq_true, ↓reduceIte] at h
                          cases hkw : keepWrote w o s3.wrote with
                          | none => simp only [hkw] at h; exact (refuse_ok h).elim
                          | some rest =>
                            simp only [hkw] at h
                            obtain ⟨_, r8, gb, h⟩ := V.bind_ok h
                            have below := belowRange_sound gb c3.holds.facts
                            have := V.pure_ok h
                            injection this with h1 _
                            subst h1
                            have g1 := entail_sound g1 ρ3 c3.holds.facts
                            have g2 := entail_sound g2 ρ3 c3.holds.facts
                            have g3 := entail_sound g3 ρ3 c3.holds.facts
                            have g4 := entail_sound g4 ρ3 c3.holds.facts
                            simp only [ev_sub, ev_const] at g2 g4
                            have hm := List.mem_of_getElem? hw
                            have hbase : ρ3 base = s0.reg base := c3.holds.entry base (outs_lt hm)
                            have hfit := (E.out hm).1
                            have eo : ev ρ3 o = ev ρ3 (signed ar) + ev ρ3 (signed br) - s0.reg base := by
                              rw [ho, ev_sub, ev_add, ev_var, hbase]
                            have sgx := signed_ev ρ3 ar
                            have sgy := signed_ev ρ3 br
                            have hx1 := sa3.1
                            have hy1 := sb.1
                            have hx2 := sa3.2.1
                            have hy2 := sb.2.1
                            unfold M64 at hx1 hy1 hfit
                            have hadr : (xa + xb) % M64 = s0.reg base + (ev ρ3 o).toNat := by unfold M64; omega
                            have hx8 : x < 256 := by have := sx3.2.1; omega
                            have hw1 : allowed (ctx.contract.perm ctx.pieces s0).write ((xa + xb) % M64) 1 = true := by
                              apply allowed_of
                              intro y hy1' hy2'
                              simp only [Contract.perm, Bool.or_eq_true]
                              right
                              unfold Contract.inOut
                              exact List.any_eq_true.mpr ⟨(name, base, n), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
                            have hbo : bounded s3.nvars o := by
                              rw [ho]
                              exact bounded_sub (bounded_add (bounded_signed sa3.2.2) (bounded_signed sb.2.2)) (bounded_var (Nat.lt_of_lt_of_le (outs_lt hm) c3.wf.regs))
                            refine ⟨ρ3, { st with mem := store st.mem ((xa + xb) % M64) x 1 },
                              ⟨Agree.trans c1.mono c1.agree (Agree.trans c2.mono c2.agree c3.agree),
                               Nat.le_trans c1.mono (Nat.le_trans c2.mono c3.mono),
                               c3.holds.writeOut E hw o xr g1 (by omega) x hx8 sx3.2.1 hkw hnw _ hadr below,
                               c3.wf.writeOut hbo sx3.2.2 hkw⟩, ?_, rfl⟩
                            simp [execStmt, hu, vx, hsize, values_two va vb, sumList, hw1]
                        next =>
                          split at h
                          next hsize8 =>
                            have hm := List.mem_of_getElem? hw
                            have hbase : ρ3 base = s0.reg base := c3.holds.entry base (outs_lt hm)
                            have hfit := (E.out hm).1
                            have eo : ev ρ3 o = ev ρ3 (signed ar) + ev ρ3 (signed br) - s0.reg base := by
                              rw [ho, ev_sub, ev_add, ev_var, hbase]
                            have sgx := signed_ev ρ3 ar
                            have sgy := signed_ev ρ3 br
                            have hx1 := sa3.1
                            have hy1 := sb.1
                            have hx2 := sa3.2.1
                            have hy2 := sb.2.1
                            unfold M64 at hx1 hy1 hfit
                            obtain ⟨perm, ρ4, c4⟩ := h8 ((xa + xb) % M64) x h c3.holds c3.wf hw
                              (fun c ec c0 cn => by unfold M64; omega) sx3
                            refine ⟨ρ4, _, c1.then (c2.then (c3.then c4)), ?_, rfl⟩
                            simp [execStmt, hu, vx, hsize8, values_two va vb, sumList, perm]
                          next => exact (refuse_ok h).elim
                      | frame c =>
                        simp only [hl] at h
                        split at h
                        next hc =>
                          obtain ⟨hsize, hin⟩ := hc
                          have := V.pure_ok h
                          injection this with h1 _
                          subst h1
                          obtain ⟨sp, _, _, h8, hst⟩ := inFrame_spec hin
                          have hstack := E.stack
                          have habove := E.above
                          have hrsp : ρ3 RSP = s0.reg RSP := c3.holds.entry RSP ctx.rsp_lt
                          have e := ev_isConst (ρ := ρ3) (locate_frame hl)
                          simp only [ev_sub, ev_add, ev_var, hrsp] at e
                          have sgx := signed_ev ρ3 ar
                          have sgy := signed_ev ρ3 br
                          have hx1 := sa3.1
                          have hy1 := sb.1
                          have hx2 := sa3.2.1
                          have hy2 := sb.2.1
                          unfold M64 at hx1 hy1 habove
                          have hadr : (((xa + xb) % M64 : Nat) : Int) = (s0.reg RSP : Int) + c := by unfold M64; omega
                          obtain ⟨_, hw, _⟩ := frame_address E hst h8 _ hadr
                          refine ⟨ρ3, { st with mem := store st.mem ((xa + xb) % M64) x 8 },
                            ⟨Agree.trans c1.mono c1.agree (Agree.trans c2.mono c2.agree c3.agree),
                             Nat.le_trans c1.mono (Nat.le_trans c2.mono c3.mono),
                             c3.holds.write E c hst h8 _ hadr x xr sx3.1 sx3.2.1, c3.wf.write c xr sx3.2.2⟩, ?_, rfl⟩
                          simp [execStmt, hu, vx, hsize, values_two va vb, sumList, hw]
                        next => exact (refuse_ok h).elim

end Ode
