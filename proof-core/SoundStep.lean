import SoundState
/-!
# Why the verifier's yes is right, 3: an instruction on symbols and the instruction on the machine
-/
namespace Ode
open Arithmetic

/-- The setting of every lemma here: the verifier's `ctx` is of the program `p`, and `s0` is a state at the
function's entry of which the caller has seen to what the contract asks. -/
structure Setting (ctx : Ctx) (p : Program) (s0 : State) : Prop where
  code : p.code = ctx.code
  pre : ctx.contract.pre p s0
  quiet : ctx.contract.quietAt s0

namespace Setting
variable {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0)
include E
theorem rip : s0.rip = p.base := E.pre.1
theorem small (r : Nat) : s0.reg r < M64 := E.pre.2.1 r
theorem stack : ctx.contract.stack ≤ s0.reg RSP := E.pre.2.2.1
theorem above : s0.reg RSP + 8 < M64 := E.pre.2.2.2.1
theorem fits {o : Nat} {i : Instr} (h : (o, i) ∈ p.code) : p.base + i.next < M64 := E.pre.2.2.2.2.1 (o, i) h
theorem region {r l : Nat} (h : (r, l) ∈ ctx.contract.regions) :
    s0.reg r + s0.reg l ≤ M64 ∧ (s0.reg r + s0.reg l ≤ s0.reg RSP - ctx.contract.stack ∨ s0.reg RSP + 8 ≤ s0.reg r) :=
  ⟨(E.pre.2.2.2.2.2.1 r l h).1, (E.pre.2.2.2.2.2.1 r l h).2.1⟩
theorem byte {r l : Nat} (h : (r, l) ∈ ctx.contract.regions) (k : Nat) (hk : k < s0.reg l) : s0.mem (s0.reg r + k) < 256 :=
  (E.pre.2.2.2.2.2.1 r l h).2.2 k hk
/-- A run given to write: in memory, and apart from the frame and the address to return to. -/
theorem out {x : String} {r n : Nat} (h : (x, r, n) ∈ ctx.contract.outs) :
    s0.reg r + n ≤ M64 ∧ (s0.reg r + n ≤ s0.reg RSP - ctx.contract.stack ∨ s0.reg RSP + 8 ≤ s0.reg r) :=
  ⟨(E.pre.2.2.2.2.2.2.1 x r n h).1, (E.pre.2.2.2.2.2.2.1 x r n h).2.1⟩
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
/-- An address of the frame, or of the address to return to, is in no run given to write. -/
theorem frame_notOut {a : Nat} (h1 : s0.reg RSP - ctx.contract.stack ≤ a) (h2 : a < s0.reg RSP + 8) :
    ctx.contract.inOut s0 a = false := by
  unfold Contract.inOut
  rw [List.any_eq_false]
  intro ⟨x, r', n⟩ hm
  have := (E.out hm).2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega
end Setting

theorem indexOf_lt (name : String) : ∀ (l : List String) (k r : Nat), indexOf name l k = some r → r < k + l.length
  | [], _, _, h => by simp [indexOf] at h
  | n :: ns, k, r, h => by
    simp only [indexOf] at h
    split at h
    · injection h with h; subst h; simp
    · have := indexOf_lt name ns (k + 1) r h
      simp only [List.length_cons]; omega

theorem regIndex_lt {name : String} {r : Nat} (h : regIndex name = some r) : r < 16 := by
  have := indexOf_lt name regNames 0 r h
  simpa [regNames] using this

theorem regOf_lt {bind : Bind} {n : String} {r : Nat} (h : regOf bind n = some r) : r < 16 := by
  unfold regOf at h
  split at h
  · cases hb : bind.lookup n with
    | none => simp [hb] at h
    | some x => simp [hb] at h; exact regIndex_lt h
  · exact regIndex_lt h

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

theorem argRegs_lt {r : Nat} (h : r ∈ argRegs) : r < 16 := by
  simp [argRegs] at h; omega

theorem regions_lt {c : Contract} {b l : Nat} (h : (b, l) ∈ c.regions) : b < 16 ∧ l < 16 := by
  obtain ⟨hb, len, hl⟩ := regionsIn_mem c c.args argRegs b l h
  exact ⟨argRegs_lt hb, argRegs_lt (regOfIn_mem len c.args argRegs l hl)⟩

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
  wf : WF s'

theorem Carried.here {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF s) :
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
theorem Carried.fresh {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF s)
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
      entry := H'.entry, data := H'.data, reg := H'.reg, small := H'.small, zf := H'.zf, cf := H'.cf, frame := H'.frame, bytes := H'.bytes,
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
theorem Carried.more {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF s)
    (m : Nat) (ag : Agree s.nvars ρ ρ') (rows : List Row) (k : Known)
    (hb : ∀ f ∈ rows, bounded (s.nvars + m) f) (hk : k.wf (s.nvars + m) s.terms.length)
    (hrows : ∀ f ∈ rows, f.holds ρ') (hknown : k.holds ctx s0 ρ' s.terms) :
    Carried ctx s0 ρ s ρ' { s with nvars := s.nvars + m, known := k :: s.known, facts := rows ++ s.facts } st := by
  have H' := H.agree wf ag
  have le : s.nvars ≤ s.nvars + m := Nat.le_add_right _ _
  refine ⟨ag, le, ?_, ?_⟩
  · exact {
      range := H'.range
      entry := H'.entry, data := H'.data, reg := H'.reg, small := H'.small, zf := H'.zf, cf := H'.cf, frame := H'.frame, bytes := H'.bytes,
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
theorem Carried.unknowns {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF s)
    (m : Nat) (ag : Agree s.nvars ρ ρ') :
    Carried ctx s0 ρ s ρ' { s with nvars := s.nvars + m } st := by
  have H' := H.agree wf ag
  have le : s.nvars ≤ s.nvars + m := Nat.le_add_right _ _
  refine ⟨ag, le, ?_, ?_⟩
  · exact {
      range := H'.range
      entry := H'.entry, data := H'.data, reg := H'.reg, small := H'.small, zf := H'.zf, cf := H'.cf, frame := H'.frame, bytes := H'.bytes,
      spec := H'.spec, mem := H'.mem, wrote := H'.wrote, words := H'.words, facts := H'.facts, known := H'.known }
  · exact {
      range := fun rg hr => ⟨bounded_mono le (wf.range rg hr).1, fun v hv => SVal.bounded_mono le ((wf.range rg hr).2 v hv)⟩
      base := Nat.le_trans wf.base le
      reg := fun r hr => bounded_mono le (wf.reg r hr)
      zf := Flag.bounded_mono le wf.zf
      cf := Flag.bounded_mono le wf.cf
      frame := fun o v m => bounded_mono le (wf.frame o v m)
      bytes := fun v r o m => ⟨Nat.lt_of_lt_of_le (wf.bytes v r o m).1 le, bounded_mono le (wf.bytes v r o m).2⟩
      spec := fun f m => SFact.bounded_mono le (wf.spec f m)
      wrote := fun w o x m => ⟨bounded_mono le (wf.wrote w o x m).1, bounded_mono le (wf.wrote w o x m).2⟩
      words := wf.words.mono rfl rfl rfl le
      facts := fun f m => bounded_mono le (wf.facts f m)
      known := fun k' m => Known.wf_mono le (Nat.le_refl _) (wf.known k' m) }

/-- The register with a table's count of blocks is one of the sixteen. -/
theorem tableAt_lt {c : Contract} {j : Nat} {x : String} {r count l : Nat} (h : c.tableAt j = some (x, r, count, l)) : l < 16 := by
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
        exact argRegs_lt (regOfIn_mem y c.args argRegs l' hr)

theorem readByte_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {r : Nat} {o v : Row}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : readByte ctx s r o items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (hb : bounded s.nvars o) :
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
    have hlen : len < 16 := (regions_lt (List.mem_of_getElem? hreg)).2
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
          entry := H'.entry, data := H'.data, reg := H'.reg, small := H'.small, zf := H'.zf, cf := H'.cf, frame := H'.frame,
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

theorem outs_lt {c : Contract} {x : String} {r n : Nat} (h : (x, r, n) ∈ c.outs) : r < 16 :=
  argRegs_lt (outsIn_mem c.args argRegs x r n h)

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

/-- An address the verifier places in the file's data: the contract has data, and the address is the
unknown that is the data's address, plus that number. -/
theorem locate_data {ctx : Ctx} {addr : Row} {c : Int} (h : locate ctx addr = some (.data c)) :
    ctx.contract.data ≠ [] ∧ Lin.isConst (Lin.sub addr (Lin.var dataVar)) = some c := by
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
    allowed (ctx.contract.perm s0).read a 8 = true ∧ allowed (ctx.contract.perm s0).write a 8 = true ∧
    ((s0.reg RSP : Int) + c).toNat = a := by
  have hs := E.stack
  refine ⟨allowed_of _ _ _ ?_, allowed_of _ _ _ ?_, by omega⟩
  · intro x hx1 hx2
    simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    left; left; left; left; omega
  · intro x hx1 hx2
    simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    left; omega

/-! ## Runs of a fixed count -/

namespace Setting
variable {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0)
include E
/-- A run of a fixed count given to read: in memory, apart from the frame and the address to return to,
holding bytes, and apart from every run given to write. -/
theorem fixed {x : String} {r n : Nat} (h : (x, r, n) ∈ ctx.contract.fixeds) :
    s0.reg r + n ≤ M64 ∧ (s0.reg r + n ≤ s0.reg RSP - ctx.contract.stack ∨ s0.reg RSP + 8 ≤ s0.reg r) ∧
    (∀ k, k < n → s0.mem (s0.reg r + k) < 256) ∧
    ∀ x' r' n', (x', r', n') ∈ ctx.contract.outs → s0.reg r + n ≤ s0.reg r' ∨ s0.reg r' + n' ≤ s0.reg r :=
  E.pre.2.2.2.2.2.2.2.2.1 x r n h
theorem inoutByte {x : String} {r n : Nat} (h : (x, r, n) ∈ ctx.contract.inouts) {k : Nat} (hk : k < n) :
    s0.mem (s0.reg r + k) < 256 := E.pre.2.2.2.2.2.2.2.2.2.1 x r n h k hk

/-- A number the contract bounds is below its bound at entry. -/
theorem bound {x : String} {b r : Nat}
    (h : (x, b) ∈ ctx.contract.bounds) (hr : ctx.contract.regOf x = some r) : s0.reg r < b :=
  E.pre.2.2.2.2.2.2.2.2.2.2.1 x b h r hr

/-- A number in memory the contract bounds (the eight bytes at a place of a run given to read) is below its
bound at entry. -/
theorem mbound {x : String} {off b r n : Nat}
    (h : (x, off, b) ∈ ctx.contract.mbounds) (hf : (x, r, n) ∈ ctx.contract.fixeds) : load s0.mem (s0.reg r + off) 8 < b :=
  E.pre.2.2.2.2.2.2.2.2.2.2.2.1 x off b h r n hf

/-- The blocks an address of a table points to: in memory, apart from the frame and the address to return
to, holding bytes, and apart from every run given to write. -/
theorem lane {j : Nat} {x : String} {r count l : Nat} (h : ctx.contract.tableAt j = some (x, r, count, l)) {i : Nat} (hi : i < count) :
    lanePtr s0 r i + 64 * s0.reg l ≤ M64 ∧
    (lanePtr s0 r i + 64 * s0.reg l ≤ s0.reg RSP - ctx.contract.stack ∨ s0.reg RSP + 8 ≤ lanePtr s0 r i) ∧
    (∀ k, k < 64 * s0.reg l → s0.mem (lanePtr s0 r i + k) < 256) ∧
    ∀ x' r' n', (x', r', n') ∈ ctx.contract.outs → lanePtr s0 r i + 64 * s0.reg l ≤ s0.reg r' ∨ s0.reg r' + n' ≤ lanePtr s0 r i :=
  E.pre.2.2.2.2.2.2.2.2.2.2.2.2.1 j x r count l h i hi

/-- A number the contract asks to be no less than another is so at entry. -/
theorem atLeast {x : String} {k r : Nat} (h : (x, k) ∈ ctx.contract.atLeast) (hr : ctx.contract.regOf x = some r) : k ≤ s0.reg r :=
  E.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.1 x k h r hr
/-- The file's read-only data, where the contract has it: in memory, each byte the file's, apart from the
frame, the address to return to and the runs given to write. -/
theorem dataAt : ctx.contract.dataAt s0 := E.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2
theorem data_fits (hd : ctx.contract.data ≠ []) : s0.data + ctx.contract.data.length < M64 := (E.dataAt hd).1
/-- An address in the file's data is not in the frame. -/
theorem data_notFrame (hd : ctx.contract.data ≠ []) {a : Nat} (h1 : s0.data ≤ a) (h2 : a < s0.data + ctx.contract.data.length) :
    ctx.contract.inFrame s0 a = false := by
  have := (E.dataAt hd).2.1
  simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega
/-- An address in the file's data is in no run given to write. -/
theorem data_notOut (hd : ctx.contract.data ≠ []) {a : Nat} (h1 : s0.data ≤ a) (h2 : a < s0.data + ctx.contract.data.length) :
    ctx.contract.inOut s0 a = false := by
  unfold Contract.inOut
  rw [List.any_eq_false]
  intro ⟨x, r', n⟩ hm
  have := (E.dataAt hd).2.2.2 x r' n hm
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega
/-- At entry each byte of the file's data is in memory where the data lies. -/
theorem data_byte (hd : ctx.contract.data ≠ []) {k : Nat} (hk : k < ctx.contract.data.length) :
    s0.mem (s0.data + k) = ctx.contract.data.getD k 0 := by
  rw [(E.dataAt hd).2.2.1 k hk]
  simp [List.getD, List.getElem?_eq_getElem hk]
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

theorem fixeds_lt {c : Contract} {x : String} {r n : Nat} (h : (x, r, n) ∈ c.fixeds) : r < 16 :=
  argRegs_lt (fixedsIn_mem c.args argRegs x r n h)

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
    | block _ _ _ _ => simp only [knownLoad] at h; exact List.mem_cons_of_mem _ (knownLoad_mem h)

/-- Eight bytes read of a run of a fixed count given to read: the number the state knows there. The run is
as it was at entry (the function may not write it), so the number is what `load` reads there at entry. -/
theorem symLoadFixed_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {addr : Row} {size : Nat} {v : EV}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symLoadFixed ctx s addr size items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (a : Nat) (hlt : a < M64) (ha : (a : Int) % 2 ^ 64 = ev ρ addr % 2 ^ 64) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ allowed (ctx.contract.perm s0).read a size = true ∧ EV.sem ρ' s'.nvars (load st.mem a size) v := by
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
        obtain ⟨fit, apart, _, outs⟩ := E.fixed hm
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
        have hread : allowed (ctx.contract.perm s0).read a 8 = true := by
          apply allowed_of
          intro x h1 h2
          simp only [Contract.perm, Contract.inFixed, Bool.or_eq_true]
          left; left; right; left
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
    (hl : locate ctx addr = some (.data c)) (h0 : 0 ≤ c) (h1 : c + size ≤ ctx.contract.data.length)
    {a : Nat} (hlt : a < M64) (ha : (a : Int) % 2 ^ 64 = ev ρ addr % 2 ^ 64) :
    ctx.contract.data ≠ [] ∧ a = s0.data + c.toNat := by
  obtain ⟨hd, hc⟩ := locate_data hl
  have e := ev_isConst (ρ := ρ) hc
  rw [ev_sub, ev_var] at e
  have pin : ρ dataVar = s0.data := H.data.1
  have fit := E.data_fits hd
  unfold M64 at hlt fit
  refine ⟨hd, ?_⟩
  omega

theorem symLoad_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {addr : Row} {size : Nat} {v : EV}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symLoad ctx s addr size items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (hb : bounded s.nvars addr)
    (a : Nat) (hlt : a < M64) (ha : (a : Int) % 2 ^ 64 = ev ρ addr % 2 ^ 64) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ allowed (ctx.contract.perm s0).read a size = true ∧ EV.sem ρ' s'.nvars (load st.mem a size) v := by
  have hstack := E.stack
  have habove := E.above
  have hrsp : ρ RSP = s0.reg RSP := H.entry RSP (by decide)
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
        have hload : load st.mem a size = dataWord ctx.contract.data c.toNat size := by
          rw [hadr]
          unfold dataWord
          exact load_list _ _ size _ _ fun k hk => by
            rw [H.mem _ (E.data_notFrame hd (by omega) (by omega)) (E.data_notOut hd (by omega) (by omega))]
            rw [Nat.add_assoc]
            exact E.data_byte hd (by omega)
        refine ⟨ρ, Carried.here H wf, allowed_of _ _ _ (fun x x1 x2 => ?_), ?_, ?_, bounded_const _ _⟩
        · simp only [Contract.perm, Contract.inData, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          right; omega
        · rw [hload]
          have lt := load_lt (fun x => ctx.contract.data.getD x 0) c.toNat size
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
          rw [ho]; exact bounded_sub hb (bounded_var (Nat.lt_of_lt_of_le hbl.1 wf.base16))
        obtain ⟨ρ', c1, bv, base', len', hreg', g1, g2, g3⟩ := readByte_sound E e1 H wf hbo
        rw [hreg] at hreg'
        injection hreg' with hreg'
        injection hreg' with hb1 hb2
        subst hb1 hb2
        have eo : ev ρ' o = ev ρ addr - s0.reg base := by
          rw [← ev_agree hbo c1.agree, ho, ev_sub, ev_var, H.entry base hbl.1]
        obtain ⟨hfit, hapart⟩ := E.region hmem
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
          left; left; left; right
          exact List.any_eq_true.mpr ⟨(base, len), hmem, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        · simp only [load]; unfold M64; omega
        · rw [g3, ← hadr]; simp only [load, hmem0]; omega
      next => exact (refuse_ok h).elim

/-- A number divided by a number above zero: the two new unknowns can be the quotient and the remainder. -/
theorem divide_sound {ctx : Ctx} {s0 : State} {s : Sym} {x : Row} {m : Int} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (hx : bounded s.nvars x) (pos : 0 < m) :
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
      entry := H'.entry, data := H'.data, reg := H'.reg, small := H'.small, zf := H'.zf, cf := H'.cf, frame := H'.frame,
      spec := H'.spec, mem := H'.mem, bytes := H'.bytes, wrote := H'.wrote, words := H'.words, known := H'.known,
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
      spec := fun f m => SFact.bounded_mono le (wf.spec f m)
      wrote := fun w o x m => ⟨bounded_mono le (wf.wrote w o x m).1, bounded_mono le (wf.wrote w o x m).2⟩
      words := wf.words.mono rfl rfl rfl le
      known := fun k m => Known.wf_mono le (Nat.le_refl _) (wf.known k m)
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

/-- Any number divided by a number above zero: what `Sym.quotRem` gives is the quotient and the remainder. -/
theorem quotRem_sound {ctx : Ctx} {s0 : State} {s : Sym} {x : Row} {m : Int} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (hx : bounded s.nvars x) (pos : 0 < m) :
    ∃ ρ', Carried ctx s0 ρ s ρ' (s.quotRem x m).2.2 st ∧
      ev ρ' (s.quotRem x m).1 = ev ρ x / m ∧ ev ρ' (s.quotRem x m).2.1 = ev ρ x % m ∧
      bounded (s.quotRem x m).2.2.nvars (s.quotRem x m).1 ∧ bounded (s.quotRem x m).2.2.nvars (s.quotRem x m).2.1 := by
  cases hd : divided s x m with
  | some q =>
    simp only [Sym.quotRem, hd]
    have hq := (List.mem_filter.mp (leastNat_mem hd)).2
    simp only [Bool.and_eq_true, among_iff, decide_eq_true_eq] at hq
    obtain ⟨hlt, ⟨⟨m1, m2⟩, m3⟩, m4⟩ := hq
    have f1 := H.facts _ m1
    have f2 := H.facts _ m2
    have f3 := H.facts _ m3
    have f4 := H.facts _ m4
    rw [holds_iff] at f1 f2 f3 f4
    simp only [ev_sub, ev_add, ev_scale, ev_var, ev_const] at f1 f2 f3 f4
    have u := (Int.ediv_emod_unique (a := ev ρ x) (r := ρ (q + 1)) (q := ρ q) pos).mpr ⟨by omega, f3, by omega⟩
    exact ⟨ρ, Carried.here H wf, by rw [ev_var]; exact u.1.symm, by rw [ev_var]; exact u.2.symm,
           bounded_var hlt, wf.facts _ m3⟩
  | none =>
    simp only [Sym.quotRem, hd]
    obtain ⟨ρ', c, hq, hr⟩ := divide_sound (ctx := ctx) (s0 := s0) H wf hx pos
    exact ⟨ρ', c, by rw [ev_var]; exact hq, by rw [ev_var]; exact hr,
           bounded_var (show s.nvars < s.nvars + 2 by omega), bounded_var (show s.nvars + 1 < s.nvars + 2 by omega)⟩

/-- A number of the machine divided by a number above zero: what `symDivide` gives is the quotient and the
remainder. -/
theorem symDivide_sound {ctx : Ctx} {s0 : State} {s : Sym} {x : Row} {m : Int} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (hx : bounded s.nvars x) (pos : 0 < m) (x0 : 0 ≤ ev ρ x) :
    ∃ ρ', Carried ctx s0 ρ s ρ' (symDivide s x m).2.2 st ∧
      ev ρ' (symDivide s x m).1 = ev ρ x / m ∧ ev ρ' (symDivide s x m).2.1 = ev ρ x % m ∧
      bounded (symDivide s x m).2.2.nvars (symDivide s x m).1 ∧ bounded (symDivide s x m).2.2.nvars (symDivide s x m).2.1 := by
  cases hd : divided s x m with
  | some q =>
    simp only [symDivide, hd]
    have hq := (List.mem_filter.mp (leastNat_mem hd)).2
    simp only [Bool.and_eq_true, among_iff, decide_eq_true_eq] at hq
    obtain ⟨hlt, ⟨⟨m1, m2⟩, m3⟩, m4⟩ := hq
    have f1 := H.facts _ m1
    have f2 := H.facts _ m2
    have f3 := H.facts _ m3
    have f4 := H.facts _ m4
    rw [holds_iff] at f1 f2 f3 f4
    simp only [ev_sub, ev_add, ev_scale, ev_var, ev_const] at f1 f2 f3 f4
    have u := (Int.ediv_emod_unique (a := ev ρ x) (r := ρ (q + 1)) (q := ρ q) pos).mpr ⟨by omega, f3, by omega⟩
    exact ⟨ρ, Carried.here H wf, by rw [ev_var]; exact u.1.symm, by rw [ev_var]; exact u.2.symm,
           bounded_var hlt, wf.facts _ m3⟩
  | none =>
    simp only [symDivide, hd]
    obtain ⟨ρ', c, hq, hr⟩ := divide_sound (ctx := ctx) (s0 := s0) H wf hx pos
    have le : s.nvars ≤ s.nvars + 2 := Nat.le_add_right _ _
    have bq : bounded (s.nvars + 2) (Lin.var s.nvars) := bounded_var (by omega)
    have br : bounded (s.nvars + 2) (Lin.var (s.nvars + 1)) := bounded_var (by omega)
    refine ⟨ρ', ⟨c.agree, c.mono, ?_, ?_⟩, by rw [ev_var]; exact hq, by rw [ev_var]; exact hr, bq, br⟩
    · exact {
        range := c.holds.range
        entry := c.holds.entry, data := c.holds.data, reg := c.holds.reg, small := c.holds.small, zf := c.holds.zf, cf := c.holds.cf,
        frame := c.holds.frame, spec := c.holds.spec, mem := c.holds.mem, bytes := c.holds.bytes, wrote := c.holds.wrote, words := c.holds.words, known := c.holds.known,
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
        base := c.wf.base, reg := c.wf.reg, zf := c.wf.zf, cf := c.wf.cf, frame := c.wf.frame, spec := c.wf.spec,
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

theorem symLow_sound {ctx : Ctx} {s0 : State} {s : Sym} {x : Row} {m : Int} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (hx : bounded s.nvars x) (pos : 0 < m) (x0 : 0 ≤ ev ρ x) :
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
      simp only [symLow, hk, hp, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨ρ', c, _, hr, _, br⟩ := symDivide_sound (ctx := ctx) (s0 := s0) H wf hx pos x0
      exact ⟨ρ', c, hr, br⟩

theorem symQuot_sound {ctx : Ctx} {s0 : State} {s : Sym} {x : Row} {m : Int} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (hx : bounded s.nvars x) (pos : 0 < m) (x0 : 0 ≤ ev ρ x) :
    ∃ ρ', Carried ctx s0 ρ s ρ' (symQuot s x m).2 st ∧ ev ρ' (symQuot s x m).1 = ev ρ x / m ∧
      bounded (symQuot s x m).2.nvars (symQuot s x m).1 := by
  cases hk : (x.coeff.all fun c => c % m == 0) with
  | true =>
    simp only [symQuot, hk, ↓reduceIte]
    refine ⟨ρ, Carried.here H wf, ev_quot_exact pos hk, ?_⟩
    exact Nat.le_trans (strip_length _) (by rw [List.length_map]; exact hx)
  | false =>
    simp only [symQuot, hk, Bool.false_eq_true, ↓reduceIte]
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
    | block _ _ _ _ => simp only [knownOr] at h; exact (knownOr_mem h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)

/-- Two numbers' bits put together: the unknown the state knows as that number is it. -/
theorem symOr_sound {ctx : Ctx} {s0 : State} {s s' : Sym} {x y : Row} {v : EV} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symOr s x y items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (xa xb : Nat) (hx : EV.sem ρ s.nvars xa (.lin x)) (hy : EV.sem ρ s.nvars xb (.lin y)) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ xa ||| xb < M64 ∧ EV.sem ρ' s'.nvars (xa ||| xb) v := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  have lt : xa ||| xb < M64 := by unfold M64 at *; exact Nat.or_lt_two_pow hx1 hy1
  unfold symOr at h
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

theorem symPrim_sound {ctx : Ctx} {s0 : State} {f : String} {s s' : Sym} {x y : Row} {v : EV} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symPrim f s x y items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
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
            cases hk : Lin.isConst y with
            | none => simp only [hk] at h; exact (refuse_ok h).elim
            | some k =>
              simp only [hk] at h
              split at h
              next hk2 =>
                have yk : (xb : Int) = k := by rw [hy2]; exact ev_isConst hk
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
              cases hk : Lin.isConst y with
              | none => simp only [hk] at h; exact (refuse_ok h).elim
              | some k =>
                simp only [hk] at h
                split at h
                next hk2 =>
                  have := V.pure_ok h
                  injection this with hp _
                  injection hp with h1 h2
                  subst h1 h2
                  have yk : (xb : Int) = k := by rw [hy2]; exact ev_isConst hk
                  have e : xb = k.toNat := by omega
                  subst e
                  have pos : (0 : Int) < 2 ^ k.toNat := Int.pow_pos (by decide)
                  obtain ⟨ρ', c, hq, _, bq, _⟩ := symDivide_sound (ctx := ctx) (s0 := s0) H wf hx3 pos (by rw [← hx2]; omega)
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
                cases hk : Lin.isConst y with
                | none => simp only [hk] at h; exact (refuse_ok h).elim
                | some m =>
                  simp only [hk] at h
                  have ym : (xb : Int) = m := by rw [hy2]; exact ev_isConst hk
                  split at h
                  next hm =>
                    simp only [beq_iff_eq] at hm
                    have xbm : xb = M64 - 64 := by unfold M64; omega
                    subst xb
                    have := V.pure_ok h
                    injection this with hp _
                    injection hp with h1 h2
                    subst h1 h2
                    obtain ⟨ρ', c, hq, _, bq, _⟩ := symDivide_sound (ctx := ctx) (s0 := s0) (m := 64) H wf hx3 (by decide) (by rw [← hx2]; omega)
                    have lt : 64 * (xa / 64) < M64 := by unfold M64 at hx1' ⊢; omega
                    refine ⟨ρ', c, (xa &&& (M64 - 64)) % M64, by simp [prim], Nat.mod_lt _ (by decide), ?_, bounded_scale 64 bq⟩
                    rw [align64_mask hx1', Nat.mod_eq_of_lt lt, ev_scale, hq, ← hx2]
                    simp [Int.natCast_ediv]
                  next =>
                    cases hfind : (List.range 65).find? (fun k => (2 : Int) ^ k - 1 == m) with
                    | none => simp only [hfind] at h; exact (refuse_ok h).elim
                    | some k =>
                      simp only [hfind] at h
                      have := V.pure_ok h
                      injection this with hp _
                      injection hp with h1 h2
                      subst h1 h2
                      have hm : (2 : Int) ^ k - 1 = m := by simpa using List.find?_some hfind
                      have pos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
                      have cast : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
                      have xbk : xb = 2 ^ k - 1 := by
                        have := Nat.two_pow_pos k
                        omega
                      subst xbk
                      obtain ⟨ρ', c, _, hr, _, br⟩ := symDivide_sound (ctx := ctx) (s0 := s0) H wf hx3 pos (by rw [← hx2]; omega)
                      have lt : xa % 2 ^ k < M64 := Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx1'
                      refine ⟨ρ', c, (xa &&& (2 ^ k - 1)) % M64, by simp [prim], Nat.mod_lt _ (by decide), ?_, br⟩
                      rw [hr, ← hx2, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt lt, Int.natCast_emod, cast]
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

/-- A primitive of one number: what the verifier holds for it is what the account says of it; and it is no
reading of memory. -/
theorem symPrim1_sound {ctx : Ctx} {s0 : State} {f : String} {s s' : Sym} {x : Row} {v : EV} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symPrim1 f s x items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
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

theorem symValue_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) :
    ∀ (e : Expr) {s s' : Sym} {v : EV} {items rest : Items} {ρ : Nat → Int} {st : State},
    symValue ctx bind s e items = .ok ((v, s'), rest) → Holds ctx s0 ρ s st → WF s →
    ∃ ρ' x, Carried ctx s0 ρ s ρ' s' st ∧ value (ctx.contract.perm s0) bind st e = some x ∧ EV.sem ρ' s'.nvars x v
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
      cases hr : regOf bind n with
      | none => simp only [hr] at h; exact (refuse_ok h).elim
      | some r =>
        simp only [hr] at h
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        have lt := regOf_lt hr
        exact ⟨ρ, st.reg r, Carried.here H wf, by simp [value, hletter, hr], H.small r, H.reg r lt, wf.reg r lt⟩
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
        cases hc : Lin.isConst x with
        | none => simp only [symData, hc] at h; exact (refuse_ok h).elim
        | some c =>
          simp only [symData, hc] at h
          by_cases hin : 0 ≤ c ∧ c < (ctx.contract.data.length : Int)
          · rw [if_pos hin] at h
            have := V.pure_ok h
            injection this with hp _
            injection hp with hv hs
            subst hv hs
            have hd : ctx.contract.data ≠ [] := by
              intro e
              rw [e] at hin
              simp only [List.length_nil] at hin
              omega
            have ec := ev_isConst (ρ := ρ1) hc
            have fit := E.data_fits hd
            have pin := c1.holds.data
            have pin1 : ρ1 dataVar = s0.data := pin.1
            refine ⟨ρ1, (st.data + sumList [xa]) % M64, c1, by simp [value, values, va, memSize, fe], Nat.mod_lt _ (by decide), ?_,
              bounded_add (bounded_var (Nat.lt_of_lt_of_le (show dataVar < 17 by decide) c1.wf.base)) (bounded_const _ _)⟩
            rw [ev_add, ev_var, ev_const, pin1, pin.2]
            simp only [sumList]
            unfold M64 at *
            omega
          · rw [if_neg hin] at h; exact (refuse_ok h).elim
      next hnd0 =>
        obtain ⟨hm, ρ2, c2, z, hz, sz⟩ := symPrim1_sound h c1.holds c1.wf xa sa
        have hnd : (f == "data") = false := by simpa using hnd0
        exact ⟨ρ2, z, c1.then c2, by simp only [value, values, va, hm, hz, hnd, Bool.false_eq_true, if_false], sz⟩
  | .call f (_ :: _ :: _ :: _), s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    exact (refuse_ok h).elim

/-! ## A statement of an effect -/

theorem Holds.setZf {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (f : Flag) (b : Bool) (hf : f.holds ρ b) : Holds ctx s0 ρ { s with zf := f } { st with zf := b } :=
  ⟨H.entry, H.data, H.reg, H.small, hf, H.cf, H.frame, H.facts, H.bytes, H.spec, H.mem, H.wrote, H.words, H.known, H.range⟩

theorem Holds.setCf {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (f : Flag) (b : Bool) (hf : f.holds ρ b) : Holds ctx s0 ρ { s with cf := f } { st with cf := b } :=
  ⟨H.entry, H.data, H.reg, H.small, H.zf, hf, H.frame, H.facts, H.bytes, H.spec, H.mem, H.wrote, H.words, H.known, H.range⟩

theorem WF.setZf {s : Sym} (wf : WF s) (f : Flag) (hb : f.bounded s.nvars) : WF { s with zf := f } :=
  ⟨wf.base, wf.reg, hb, wf.cf, wf.frame, wf.facts, wf.bytes, wf.spec, wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, wf.range⟩

theorem WF.setCf {s : Sym} (wf : WF s) (f : Flag) (hb : f.bounded s.nvars) : WF { s with cf := f } :=
  ⟨wf.base, wf.reg, wf.zf, hb, wf.frame, wf.facts, wf.bytes, wf.spec, wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, wf.range⟩

theorem Holds.put {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (r x : Nat) (xr : Row) (hx : x < M64) (hxr : (x : Int) = ev ρ xr) : Holds ctx s0 ρ (s.put r xr) (setReg st r x) where
  range := H.range
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
  facts := H.facts
  bytes := H.bytes
  spec := H.spec
  mem := H.mem
  wrote := H.wrote
  words := H.words
  known := H.known

theorem WF.put {s : Sym} (wf : WF s) (r : Nat) (xr : Row) (hb : bounded s.nvars xr) : WF (s.put r xr) where
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
    Holds ctx s0 ρ { s with spill := [], range := none, frame := (c, xr) :: s.frame.filter fun (o, _) => decide (o + 8 ≤ c) || decide (c + 8 ≤ o) }
      { st with mem := store st.mem a x 8 } where
  range := fun _ h => nomatch h
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
    have hs := E.stack
    simp only [List.mem_cons] at m
    rcases m with heq | m
    · injection heq with e1 e2
      subst e1 e2
      refine ⟨h1, h2, ?_⟩
      have : ((s0.reg RSP : Int) + o).toNat = a := by omega
      rw [this, load_store_same _ _ _ _ (by rw [pow8]; exact hx)]
      exact hxr
    · obtain ⟨m, hk⟩ := List.mem_filter.mp m
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
      obtain ⟨g1, g2, g3⟩ := H.frame o v m
      refine ⟨g1, g2, ?_⟩
      rw [load_store_other _ _ _ _ _ _ (by omega)]
      exact g3
  mem x' hx' ho := by
    have hs := E.stack
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
      show store st.mem a x 8 (s0.reg r + 4 * j + b) = _
      rw [store_other _ _ _ _ _ (by omega)]
      exact g3 b hb
  known := H.known

theorem WF.write {s : Sym} (wf : WF s) (c : Int) (xr : Row) (hb : bounded s.nvars xr) :
    WF { s with spill := [], range := none, frame := (c, xr) :: s.frame.filter fun (o, _) => decide (o + 8 ≤ c) || decide (c + 8 ≤ o) } where
  range := fun _ h => nomatch h
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
  words := wf.words.mono rfl rfl rfl (Nat.le_refl _)
  known := wf.known

/-- One byte written into a run given to write. -/
theorem belowRange_sound {s : Sym} {w : Nat} {o : Row} {items : Items} {r : Unit × Items} {ρ : Nat → Int}
    (h : belowRange s w o items = .ok r) (hf : ∀ f ∈ s.facts, f.holds ρ) :
    ∀ rg, s.range = some rg → rg.w = w → ev ρ o + 1 ≤ ev ρ rg.lo := by
  intro rg hr hw
  simp only [belowRange, hr, hw, beq_self_eq_true, if_true] at h
  have := entail_sound h ρ hf
  simp only [ev_sub, ev_const] at this
  omega

theorem Holds.writeOut {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) {w : Nat} {name : String} {r n : Nat} (hw : ctx.contract.outs[w]? = some (name, r, n))
    (o xr : Row) (h1 : 0 ≤ ev ρ o) (h2 : ev ρ o < n) (x : Nat) (hx : x < 256) (hxr : (x : Int) = ev ρ xr)
    {rest : List (Nat × Row × Row)} (hk : keepWrote w o s.wrote = some rest)
    (hnw : (s.wroteW.any fun e => e.1 == w) = false)
    (a : Nat) (ha : a = s0.reg r + (ev ρ o).toNat)
    (below : ∀ rg, s.range = some rg → rg.w = w → ev ρ o + 1 ≤ ev ρ rg.lo) :
    Holds ctx s0 ρ { s with wrote := (w, o, xr) :: rest, intact := s.intact.filter (· != w), spill := [] }
      { st with mem := store st.mem a x 1 } where
  range rg hr := by
    obtain ⟨name', r', n', params, y, b, hi, g1, g2, g3, g4, g5⟩ := H.range rg hr
    refine ⟨name', r', n', params, y, b, hi, g1, g2, g3, g4, fun j lo hj => ?_⟩
    show Value ctx.defs _ b (.int (store st.mem a x 1 (s0.reg r' + j)))
    have hne : s0.reg r' + j < a ∨ a + 1 ≤ s0.reg r' + j := by
      by_cases e : rg.w = w
      · have := below rg hr e
        rw [e, hw] at g1
        injection g1 with g1; injection g1 with _ g1; injection g1 with g1 gn
        subst g1 gn
        omega
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
    have hs := E.stack
    have ho := (E.out (List.mem_of_getElem? hw)).2
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
      show store st.mem a x 1 (s0.reg r' + 4 * j + b) = _
      rw [store_other _ _ _ _ _ (by omega)]
      exact g3 b hb
  known := H.known

theorem WF.writeOut {s : Sym} (wf : WF s) {w : Nat} {o xr : Row} (ho : bounded s.nvars o) (hx : bounded s.nvars xr)
    {rest : List (Nat × Row × Row)} (hk : keepWrote w o s.wrote = some rest) :
    WF { s with wrote := (w, o, xr) :: rest, intact := s.intact.filter (· != w), spill := [] } where
  range := wf.range
  base := wf.base
  reg := wf.reg
  zf := wf.zf
  cf := wf.cf
  frame := wf.frame
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
  simp only [frameOffset, ev_sub, ev_var, H.entry RSP (by decide)]

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
    allowed (ctx.contract.perm s0).read a n = true ∧ allowed (ctx.contract.perm s0).write a n = true := by
  have inside (x : Nat) (hx : a ≤ x) (hy : x < a + n) : ctx.contract.inFrame s0 x = true := by
    simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact ⟨allowed_of _ _ _ (fun x h1 h2 => by simp [Contract.perm, inside x h1 h2]),
    allowed_of _ _ _ (fun x h1 h2 => by simp [Contract.perm, inside x h1 h2])⟩

/-- A store wholly inside the frame and below the saved scalar words does not affect other regions. -/
theorem Holds.frameSpanWrite {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym}
    (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) {mem' : Nat → Nat} {a n : Nat} {spill : List (Row × List Nat)}
    (lo : s0.reg RSP - ctx.contract.stack ≤ a) (hi : a + n ≤ s0.reg RSP)
    (apart : ∀ o v, (o, v) ∈ s.frame → a + n ≤ ((s0.reg RSP : Int) + o).toNat)
    (same : ∀ y, y < a ∨ a + n ≤ y → mem' y = st.mem y)
    (saved : ∀ o ids, (o, ids) ∈ spill → 0 ≤ (s0.reg RSP : Int) + ev ρ o ∧ ∀ k, k < ids.length →
      load mem' (((s0.reg RSP : Int) + ev ρ o).toNat + 4 * k) 4 = den (inpOf ctx s0) ρ s.terms (ids.getD k 0)) :
    Holds ctx s0 ρ { s with spill := spill, range := none } { st with mem := mem' } where
  range := fun _ h => nomatch h
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
    obtain ⟨h1, h2, h3⟩ := H.frame o v m
    have space := apart o v m
    have e := load_congr mem' st.mem ((s0.reg RSP : Int) + o).toNat 8 (fun y hy _ => same y (Or.inr (by omega)))
    exact ⟨h1, h2, by rw [e]; exact h3⟩
  mem y outside hout := by
    have out := outside
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
      show mem' (s0.reg r + 4 * j + b) = _
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
    {items rest : Items} (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (h : symTouchFrame ctx s addr items = .ok (s', rest)) (a x : Nat)
    (matchAddr : ∀ A : Nat, (A : Int) = ev ρ addr → A < M64 → a = A) :
    allowed (ctx.contract.perm s0).write a 1 = true ∧ Carried ctx s0 ρ s ρ s' { st with mem := store st.mem a x 1 } := by
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
  · exact ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.facts, wf.bytes, wf.spec, wf.wrote,
      wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, fun _ h => nomatch h⟩

theorem symStmt_scalar {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) {s s' : Sym} {stmt : Stmt}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symStmt ctx bind s stmt items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (base u : Nat)
    (hv : ∀ place v, stmt ≠ .vset place v) (hw : ∀ place v, stmt ≠ .vset512 place v) :
    ∃ ρ' st', Carried ctx s0 ρ s ρ' s' st' ∧ execStmt (ctx.contract.perm s0) bind base u st stmt = some st' ∧ st'.rip = st.rip := by
  cases stmt with
  | nothing =>
    simp only [symStmt] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨ρ, st, Carried.here H wf, rfl, rfl⟩
  | ret => simp only [symStmt] at h; exact (refuse_ok h).elim
  | call t => simp only [symStmt] at h; exact (refuse_ok h).elim
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
                            have hw1 : allowed (ctx.contract.perm s0).write ((xa + xb) % M64) 1 = true := by
                              apply allowed_of
                              intro y hy1' hy2'
                              simp only [Contract.perm, Bool.or_eq_true]
                              right
                              unfold Contract.inOut
                              exact List.any_eq_true.mpr ⟨(name, base, n), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
                            have hbo : bounded s3.nvars o := by
                              rw [ho]
                              exact bounded_sub (bounded_add (bounded_signed sa3.2.2) (bounded_signed sb.2.2)) (bounded_var (Nat.lt_of_lt_of_le (outs_lt hm) c3.wf.base16))
                            refine ⟨ρ3, { st with mem := store st.mem ((xa + xb) % M64) x 1 },
                              ⟨Agree.trans c1.mono c1.agree (Agree.trans c2.mono c2.agree c3.agree),
                               Nat.le_trans c1.mono (Nat.le_trans c2.mono c3.mono),
                               c3.holds.writeOut E hw o xr g1 (by omega) x hx8 sx3.2.1 hkw hnw _ hadr below,
                               c3.wf.writeOut hbo sx3.2.2 hkw⟩, ?_, rfl⟩
                            simp [execStmt, hu, vx, hsize, values_two va vb, sumList, hw1]
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
                          have hrsp : ρ3 RSP = s0.reg RSP := c3.holds.entry RSP (by decide)
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
