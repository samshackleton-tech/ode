import SoundCallW
import SoundTrace
/-!
# Why the verifier's yes is right, 13: tail calls (`jmp` / `b` to a named function)

At a tail call the caller has restored its stack pointer to entry (`sp = 0`), restored every
callee-saved register and vector register it promises to keep (which the callee also preserves),
restored its link register on AArch64, and passed no stack-frame operand. Control jumps straight to
the callee (`afterTail q st`), whose own `ret` returns directly to the caller's caller.
-/
namespace Ode
open Arithmetic

/-- Expanded structural requirements checked by `tailFits`. -/
structure TailOk (ctx : Ctx) (s : Sym) (name : String) (c : Contract) : Prop where
  notSelf : ctx.selfName ≠ some name
  machine : c.arm64 = ctx.contract.arm64
  sp0 : s.sp = some 0
  rspClean : RSP ∈ s.q.regq
  linkOk : ctx.contract.arm64 = true → s.reg LINK = Lin.var LINK ∧ LINK ∈ s.q.regq
  keeps : ∀ r ∈ ctx.contract.keeps, s.reg r = Lin.var r ∧ r ∈ c.keeps
  keepsVec : ∀ v ∈ ctx.contract.keepsVec, v ∈ s.vecIntact ∧ v ∈ c.keepsVec
  noLanes : c.lanes = []
  noValArrays : c.valArrays = []
  noFrameOut : ∀ x ∈ c.outs, frameAt s x.2.1 = none
  noFrameFix : ∀ x ∈ c.fixeds, frameAt s x.2.1 = none

theorem TailOk.regs {ctx : Ctx} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c) :
    c.regs = ctx.nreg := by
  unfold Ctx.nreg Contract.regs; rw [T.machine]

theorem TailOk.slot {ctx : Ctx} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c) :
    c.slot = ctx.contract.slot := by
  unfold Contract.slot; rw [T.machine]

theorem TailOk.arg_lt {ctx : Ctx} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c)
    {r : Nat} (hr : r ∈ c.argRegs) : r < ctx.nreg :=
  T.regs ▸ (argRegs_spec hr).1

theorem tailFits_spec {ctx : Ctx} {s : Sym} {name : String} {c : Contract}
    (h : tailFits ctx s name c = true) : TailOk ctx s name c := by
  unfold tailFits at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, beq_iff_eq,
    List.all_eq_true, List.contains_iff_mem, Option.isNone_iff_eq_none, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, h6, h7, h8, h9, h10, h11⟩
  intro ha
  rcases h5 with h5 | h5
  · rw [ha] at h5; cases h5
  · exact h5

theorem TailOk.withFacts {ctx : Ctx} {s : Sym} {name : String} {c : Contract}
    (T : TailOk ctx s name c) (fs : List Row) : TailOk ctx { s with facts := fs } name c :=
  ⟨T.notSelf, T.machine, T.sp0, T.rspClean, T.linkOk, T.keeps, T.keepsVec, T.noLanes, T.noValArrays,
   T.noFrameOut, T.noFrameFix⟩

theorem symKnow_tailOk {ctx : Ctx} {s s' : Sym} {name : String} {c : Contract} {advice : Sym → List Row}
    {items rest : Items} (T : TailOk ctx s name c) :
    ∀ k, symKnow advice k s items = .ok (s', rest) → TailOk ctx s' name c
  | 0, h => by simp only [symKnow] at h; cases V.pure_ok h; exact T
  | k + 1, h => by
    simp only [symKnow] at h
    obtain ⟨o, _, _, h⟩ := V.bind_ok h
    cases o with
    | none => cases V.pure_ok h; exact T
    | some g =>
      by_cases hlen : g.coeff.length ≤ s.nvars
      · simp only [hlen, ite_true] at h
        obtain ⟨_, _, _, h⟩ := V.bind_ok h
        exact symKnow_tailOk (T.withFacts _) k h
      · simp only [hlen, ite_false] at h
        exact (refuse_ok h).elim

theorem stackAt_afterTail (c : Contract) (q : Program) (st : State) :
    c.stackAt (afterTail q st) = c.stackAt st := by
  unfold Contract.stackAt
  cases c.stackBits <;> rfl

theorem inFrame_afterTail (c : Contract) (q : Program) (st : State) (a : Nat) :
    c.inFrame (afterTail q st) a = c.inFrame st a := by
  unfold Contract.inFrame; rw [stackAt_afterTail]; rfl

theorem symKnow_sp {s s' : Sym} {advice : Sym → List Row} {items rest : Items} :
    ∀ k, symKnow advice k s items = .ok (s', rest) → s'.sp = s.sp ∧ s'.q = s.q ∧ s'.reg = s.reg
  | 0, h => by simp only [symKnow] at h; cases V.pure_ok h; exact ⟨rfl, rfl, rfl⟩
  | k + 1, h => by
    simp only [symKnow] at h
    obtain ⟨o, _, _, h⟩ := V.bind_ok h
    cases o with
    | none => cases V.pure_ok h; exact ⟨rfl, rfl, rfl⟩
    | some g =>
      by_cases hlen : g.coeff.length ≤ s.nvars
      · simp only [hlen, ite_true] at h
        obtain ⟨_, _, _, h⟩ := V.bind_ok h
        exact symKnow_sp (s := { s with facts := g :: s.facts }) k h
      · simp only [hlen, ite_false] at h
        exact (refuse_ok h).elim

theorem TailOk.rsp_eq {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {name : String} {c : Contract}
    (T : TailOk ctx s name c) (H : Holds ctx s0 ρ s st) : st.reg RSP = s0.reg RSP := by
  have esp := ev_isConst (ρ := ρ) T.sp0
  simp only [ev_sub, ev_var] at esp
  have h1 := H.reg RSP ctx.rsp_lt
  have h2 := H.entry RSP ctx.rsp_lt
  omega

theorem TailOk.backTo_eq {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym} {name : String} {c : Contract}
    (E : Setting ctx p s0) (T : TailOk ctx s name c) (H : Holds ctx s0 ρ s st) (q : Program) :
    c.backTo (afterTail q st) = ctx.contract.backTo s0 := by
  unfold Contract.backTo
  rw [T.machine]
  cases ha : ctx.contract.arm64 with
  | true =>
    simp only [afterTail, ite_true]
    have hlt : LINK < ctx.nreg := by unfold Ctx.nreg Contract.regs; rw [ha]; decide
    have hreg := H.reg LINK hlt
    rw [(T.linkOk ha).1, ev_var, H.entry LINK hlt] at hreg
    omega
  | false =>
    simp only [afterTail, Bool.false_eq_true, ite_false]
    rw [T.rsp_eq H]
    apply load_congr
    intro a ha1 ha2
    have hslot : ctx.contract.slot = 8 := by unfold Contract.slot; rw [ha]; rfl
    have hnf : ctx.contract.inFrame s0 a = false := by
      simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    have hno : ctx.contract.inOut s0 a = false := by
      unfold Contract.inOut
      rw [List.any_eq_false]
      intro ⟨x, r, n⟩ hm
      have hdis := (E.outAt hm).2
      rw [hslot] at hdis
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    exact H.mem a hnf hno

/-- Callee entry preconditions at a tail call (`sp = 0`, `extra = 0`). -/
structure TailExtra (ctx : Ctx) (s0 st : State) (c : Contract) : Prop where
  stack : c.stackAt st ≤ ctx.contract.stackAt s0
  mbounds : ∀ x off b, (x, off, b) ∈ c.mbounds → ∀ r n, (x, r, n) ∈ c.fixeds → load st.mem (st.reg r + off) 8 < b
  atLeast : ∀ x k, (x, k) ∈ c.atLeast → ∀ r, c.regOf x = some r → k ≤ st.reg r
  preLines : ∀ k ts, (k, ts) ∈ c.preLines → 0 ≤ preLineVal c st k ts
  aligns : ∀ x al, (x, al) ∈ c.aligns → 0 < al → ∀ r, c.regOf x = some r → st.reg r % al = 0
  disjoint : ∀ x y L, (x, y, L) ∈ c.disjoint → 0 < L →
    ∀ bx lx by_ ly, c.bufSpan st x = some (bx, lx) → c.bufSpan st y = some (by_, ly) →
      ∀ i < lx, ∀ j < ly, (bx + i) / L ≠ (by_ + j) / L

theorem tailMbounds_sound {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym} {name : String}
    {c : Contract} (E : Setting ctx p s0) (T : TailOk ctx s name c) (H : Holds ctx s0 ρ s st) :
    ∀ (mbs : List (String × Nat × Nat)) {items rest : Items},
    each (fun (xob : String × Nat × Nat) =>
      let (x, o, bd) := xob
      each (fun (xrn : String × Nat × Nat) =>
        if xrn.1 != x then pure ()
        else
          let (_, r, n) := xrn
          if !(o + 8 ≤ n) then refuse "a called function bounds bytes outside its fixed run"
          else
            match fixedPart ctx s r n with
            | some (j, _, c0) =>
              match ctx.contract.fixeds[j]? with
              | some (x0, _, _) =>
                if ctx.contract.mbounds.any fun (x', o', bd') => x' == x0 && o' == c0 + o && bd' ≤ bd then pure ()
                else refuse "a called function bounds a number in a fixed run that is not bounded in this function's contract"
              | none => refuse "a called function bounds a number in memory that is not known to lie below that bound"
            | none =>
              match frameAt s r with
              | some cf =>
                if 0 ≤ cf + (o : Int) ∧ cf + (o : Int) + 8 ≤ 0 then
                  match s.frame.find? (fun cell => cell.1 == cf + (o : Int)) with
                  | some (_, row) => entail s.facts (Lin.sub (Lin.const ((bd : Int) - 1)) row)
                  | none => refuse "a called function bounds a number in the frame that is not a known cell"
                else refuse "a called function bounds a number outside the frame"
              | none => refuse "a called function bounds a number in memory that is not known to lie below that bound") c.fixeds) mbs items = .ok ((), rest) →
    ∀ x o bd, (x, o, bd) ∈ mbs → ∀ r n, (x, r, n) ∈ c.fixeds → load st.mem (st.reg r + o) 8 < bd := by
  intro mbs items rest h x o bd hmb r n hfix
  obtain ⟨_, _, h1⟩ := each_mem h (x, o, bd) hmb
  obtain ⟨_, _, h2⟩ := each_mem h1 (x, r, n) hfix
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at h2
  split at h2
  · exact (refuse_ok h2).elim
  next ho8 =>
    have ho8' : o + 8 ≤ n := by simpa using ho8
    cases hfp : fixedPart ctx s r n with
    | none =>
      simp only [hfp, T.noFrameFix (x, r, n) hfix] at h2
      exact (refuse_ok h2).elim
    | some jbc =>
      obtain ⟨j, b0, c0⟩ := jbc
      simp only [hfp] at h2
      cases hj : ctx.contract.fixeds[j]? with
      | none => simp [hj] at h2; exact (refuse_ok h2).elim
      | some xrn0 =>
        obtain ⟨x0, r0, n0⟩ := xrn0
        simp only [hj] at h2
        split at h2
        next hany =>
          obtain ⟨⟨x', o', bd'⟩, hmb', hcond⟩ := List.any_eq_true.mp hany
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          obtain ⟨⟨rfl, rfl⟩, hbdle⟩ := hcond
          have hfx0 : (x', r0, n0) ∈ ctx.contract.fixeds := List.mem_of_getElem? hj
          obtain ⟨off, hfo, hoff, hcn, _⟩ := fixedPart_of_fixeds hfp hj
          obtain ⟨j', off', _, r'', _, hloc, _, hj', hregf⟩ := findOut_spec hfo
          have ej' : j' = j := by cases hloc; rfl
          have eo' : off' = off := by cases hloc; rfl
          rw [ej', Nat.sub_zero, hj] at hj'
          have er' : r'' = r0 := by cases hj'; rfl
          rw [eo', er'] at hregf
          have r_arg : r ∈ c.argRegs := fixedsIn_mem c.args c.argRegs x r n hfix
          have hreg := H.reg r (T.arg_lt r_arg)
          have eoff := ev_isConst (ρ := ρ) hoff
          rw [hregf, ev_sub, ev_var, H.entry r0 (fixeds_lt hfx0)] at eoff
          have hre : st.reg r = s0.reg r0 + c0 := by omega
          have hmem_eq : load st.mem (st.reg r + o) 8 = load s0.mem (s0.reg r0 + (c0 + o)) 8 := by
            rw [hre, Nat.add_assoc]
            refine load_congr _ _ _ _ fun a ha1 ha2 => ?_
            have hfx_pre := E.fixedAt hfx0
            have hnf : ctx.contract.inFrame s0 a = false := by
              simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
            have hno : ctx.contract.inOut s0 a = false := by
              unfold Contract.inOut
              rw [List.any_eq_false]
              intro ⟨xo, ro, no⟩ hmo
              have hdis := hfx_pre.2.2.2 xo ro no hmo
              simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
            exact H.mem a hnf hno
          rw [hmem_eq]
          exact Nat.lt_of_lt_of_le (E.mbound hmb' hfx0) hbdle
        next => exact (refuse_ok h2).elim

theorem tailPreOk_sound {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym} {name : String}
    {c : Contract} (E : Setting ctx p s0) (T : TailOk ctx s name c) (H : Holds ctx s0 ρ s st) {items rest items_dj rest_dj : Items}
    (h : tailPreOk ctx s c items = .ok ((), rest))
    (hdj : callDisjointOk ctx s c items_dj = .ok ((), rest_dj)) : TailExtra ctx s0 st c := by
  unfold tailPreOk at h
  obtain ⟨_, r0, e0, h⟩ := V.bind_ok h
  obtain ⟨_, rm, em, h⟩ := V.bind_ok h
  obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
  obtain ⟨_, r2, e2, e3⟩ := V.bind_ok h
  have hg := stackFitsMAt_sound T.machine H e0
  have hmb := tailMbounds_sound E T H c.mbounds em
  have hreg : ∀ r ∈ c.argRegs, (st.reg r : Int) = ev ρ (s.reg r) := fun r hr => H.reg r (T.arg_lt hr)
  have hspBound : ∀ sp', s.sp = some sp' → -(ctx.contract.stackAt s0 : Int) ≤ sp' := by
    intro sp' h'; rw [T.sp0] at h'; cases h'; omega
  refine ⟨by omega, hmb, ?_, ?_, callAlignsOk_sound_of E H hreg c.aligns e3, callDisjointOk_sound_of E H hspBound hreg c.disjoint hdj⟩
  · intro x k m r hr
    obtain ⟨_, _, he⟩ := each_mem e1 (x, k) m
    simp only [hr] at he
    have hge := entail_sound he ρ H.facts
    rw [ev_sub, ev_const] at hge
    have ra := regOfIn_mem x c.args c.argRegs r hr
    have hreg := H.reg r (T.arg_lt ra)
    omega
  · intro k ts m
    obtain ⟨_, _, he⟩ := each_mem e2 (k, ts) m
    have hge := entail_sound he ρ H.facts
    simp only [ev_preLineRow] at hge
    unfold preLineVal
    have hcongr := foldl_preLine_congr c (fun r => ev ρ (s.reg r)) (fun r => (st.reg r : Int))
      (fun x r hr => (H.reg r (T.arg_lt (regOfIn_mem x c.args c.argRegs r hr))).symm) ts 0
    exact (congrArg (0 ≤ k + ·) hcongr).mp hge

theorem loaded_tail {ctx : Ctx} {p : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym}
    (E : Setting ctx p s0) (H : Holds ctx s0 ρ s st) (q : Program) :
    Loaded ctx.pieces (afterTail q st) := by
  intro k pc hpc
  obtain ⟨h1, h2, h3⟩ := E.loaded k pc hpc
  refine ⟨by rw [afterTail_data, H.data.2]; exact h1, by rw [afterTail_data, H.data.2]; exact h2, fun j hj => ?_⟩
  obtain ⟨hf, ho⟩ := E.apart _ (inPieces_iff.mpr ⟨k, pc, hpc, Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩)
  show (st.mem (st.data k + j)).val = pc.bytes[j]
  rw [H.data.2, H.mem (s0.data k + j) hf ho]
  exact h3 j hj

theorem clear_tail {world : List Program} {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym}
    {name : String} {c : Contract} (Kc : ctx.contract.clear world ctx.pieces s0)
    (T : TailOk ctx s name c) (H : Holds ctx s0 ρ s st) (q : Program)
    (hwrite : ∀ a, (c.perm ctx.pieces (afterTail q st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) :
    c.clear world ctx.pieces (afterTail q st) := by
  intro a hfix
  have hfix0 : Fixed world ctx.pieces s0 a := by
    rcases hfix with hin | hcode
    · left; unfold inPieces at hin ⊢; rw [afterTail_data, H.data.2] at hin; exact hin
    · exact Or.inr hcode
  obtain ⟨hf0, ho0, hs0⟩ := Kc a hfix0
  have hnw : (c.perm ctx.pieces (afterTail q st)).write a = false := by
    cases hw : (c.perm ctx.pieces (afterTail q st)).write a
    · rfl
    · have := hwrite a hw
      simp [Contract.perm, hf0, ho0] at this
  simp only [Contract.perm, Bool.or_eq_false_iff] at hnw
  refine ⟨hnw.1, hnw.2, ?_⟩
  show ¬(st.reg RSP ≤ a ∧ a < st.reg RSP + c.slot)
  rw [T.rsp_eq H, T.slot]
  exact hs0

theorem read_pieces_tail {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} (H : Holds ctx s0 ρ s st)
    (q : Program) {a : Nat} (ha : inPieces ctx.pieces (afterTail q st) a = true) :
    (ctx.contract.perm ctx.pieces s0).read a = true := by
  simp only [Contract.perm, Bool.or_eq_true]
  right
  unfold inPieces at ha ⊢
  rw [afterTail_data, H.data.2] at ha
  exact ha

/-- Core functional soundness of `symCall'` at a tail call (`sp = 0`, `extra = 0`, no lanes, no valArrays,
no frame operands). For any state `s2` returned by `q` satisfying `c.post ctx.defs (afterTail q st) s2`,
the pre-pop state `setReg s2 RSP (s0.reg RSP)` satisfies `Carried ctx s0 ρ s ρ' s'`. -/
theorem tailCall'_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {name : String}
    {c : Contract} {items rest : Items} {ρ : Nat → Int} {st : State}
    (T : TailOk ctx s name c) (EX : TailExtra ctx s0 st c)
    (h : symCall' ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) :
    c.pre q (afterTail q st) ∧
    (∀ a, (c.perm ctx.pieces (afterTail q st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterTail q st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterTail q st) s2 → s2.data = st.data →
      ∃ ρ', Carried ctx s0 ρ s ρ' s' (setReg s2 RSP (s0.reg RSP)) := by
  have hrsp_eq : st.reg RSP = s0.reg RSP := T.rsp_eq H
  have hrsp : (st.reg RSP : Int) = s0.reg RSP + 0 := by omega
  have hstack := E.stackAt
  have habove := E.above
  have hslot := T.slot
  have hcst := EX.stack
  have harm_align : c.arm64 = true → st.reg RSP % 16 = 0 := fun ha => by
    rw [hrsp_eq]; exact E.aligned (T.machine ▸ ha)
  have hnoFrameOut : c.outs.any (fun x => (frameAt s x.2.1).isSome) = false := by
    rw [List.any_eq_false]; intro x hx; simp [T.noFrameOut x hx]
  have hl : c.lanes = [] := T.noLanes
  have hva : c.valArrays = [] := T.noValArrays
  have hregs : c.regs = ctx.nreg := T.regs
  -- Helper: restoring RSP to s0.reg RSP after q's return keeps all other registers and satisfies `s2pre.reg < M64`
  have mkPre : ∀ s2, c.post ctx.defs (afterTail q st) s2 →
      let s2p := setReg s2 RSP (s0.reg RSP)
      (∀ r, s2p.reg r < M64) ∧
      (∀ r, r < ctx.nreg → c.scratch.contains r = false → s2p.reg r = st.reg r) ∧
      (∀ r ∈ c.keepsVec, s2p.vec r = st.vec r) := by
    intro s2 post
    obtain ⟨_, prsp, psaved, _, _, psmall, _, pvec⟩ := post
    refine ⟨fun r => ?_, fun r hr hc => ?_, fun r hr => pvec r hr⟩
    · show (if r = RSP then s0.reg RSP % M64 else s2.reg r) < M64
      split
      · exact Nat.mod_lt _ (by decide)
      · exact psmall r
    · show (if r = RSP then s0.reg RSP % M64 else s2.reg r) = st.reg r
      by_cases h4 : r = RSP
      · rw [if_pos h4, h4, hrsp_eq, Nat.mod_eq_of_lt (H.small RSP |> fun hh => by rwa [hrsp_eq] at hh)]
      · rw [if_neg h4]
        have hmemr : r ∈ c.keeps := kept_of_not_scratch (hregs ▸ hr) h4 hc
        exact psaved r hmemr
  unfold symCall' at h
  simp only [hl, hva, hnoFrameOut, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at h
  split at h
  · -- Branch 1: `symCallPlain` (no outs, no ensures, no fixeds, no inouts, no ensuresW)
    next hplain =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hplain
    obtain ⟨⟨houts, hens⟩, ⟨hfix, ⟨hinouts, hensW⟩⟩⟩ := hplain
    unfold symCallPlain at h
    simp only [T.sp0, houts, hens, hfix, hinouts, hensW, List.isEmpty_nil, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false] at h
    cases henv : calleeEnv ctx c s c.args c.argRegs with
    | none => simp [henv] at h; exact (refuse_ok h).elim
    | some env =>
      simp only [henv] at h
      obtain ⟨_, r0, hbounds, h⟩ := V.bind_ok h
      have hregion : ∀ r l, (r, l) ∈ c.regions → ∃ b0 l0, (b0, l0) ∈ ctx.contract.regions ∧ st.reg r = s0.reg b0 ∧ st.reg l = s0.reg l0 := by
        intro r l m
        obtain ⟨_, b0, l0, hget, er, el⟩ := calleeEnv_regions c.args c.argRegs henv r l m
        have hm : (b0, l0) ∈ ctx.contract.regions := List.mem_of_getElem? hget
        obtain ⟨ra, len, hlen⟩ := regionsIn_mem c c.args c.argRegs r l m
        have la := regOfIn_mem len c.args c.argRegs l hlen
        have hr := H.reg r (T.arg_lt ra); have hl' := H.reg l (T.arg_lt la)
        obtain ⟨hb0, hl0⟩ := regions_lt hm
        rw [er, ev_var, H.entry b0 hb0] at hr; rw [el, ev_var, H.entry l0 hl0] at hl'
        exact ⟨b0, l0, hm, by omega, by omega⟩
      have hno : ∀ s1 a, c.inOut s1 a = false := fun s1 a => by simp [Contract.inOut, houts]
      have hnf : ∀ s1 a, c.inFixed s1 a = false := fun s1 a => by simp [Contract.inFixed, hfix, hinouts]
      have hpre : c.pre q (afterTail q st) := by
        refine ⟨rfl, H.small, by show c.stackAt st ≤ st.reg RSP; omega, by show st.reg RSP + c.slot < M64; omega, hq,
          fun r l m => ?_, fun _ _ _ m => (by rw [houts] at m; cases m), (by rw [houts]; exact List.Pairwise.nil),
          fun _ _ _ m => (by rw [hfix] at m; cases m), fun x bd m r hr => ?_,
          fun _ _ _ _ _ _ m => (by rw [hfix] at m; cases m),
          fun _ _ _ _ _ ht => (by rw [tableAt_none hl] at ht; cases ht),
          EX.atLeast, harm_align, EX.preLines, (fun _ _ _ _ _ m => (by rw [hva] at m; cases m)), EX.aligns, EX.disjoint⟩
        · obtain ⟨b0, l0, hm, er, el⟩ := hregion r l m
          obtain ⟨fit, apart⟩ := E.regionAt hm
          show st.reg r + st.reg l ≤ M64 ∧ (st.reg r + st.reg l ≤ st.reg RSP - c.stackAt (afterTail q st) ∨ st.reg RSP + c.slot ≤ st.reg r)
          rw [stackAt_afterTail, er, el, hrsp_eq, hslot]; exact ⟨fit, by omega⟩
        · obtain ⟨_, _, he⟩ := each_mem hbounds (x, bd) m
          simp only [hr] at he
          have hge := entail_sound he ρ H.facts
          rw [ev_sub, ev_const] at hge
          have ra := regOfIn_mem x c.args c.argRegs r hr
          have := H.reg r (T.arg_lt ra); show st.reg r < bd; omega
      have hread : ∀ a, (c.perm ctx.pieces (afterTail q st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true := by
        intro a ha
        rw [perm_read_split, Bool.or_eq_true] at ha
        refine ha.elim (fun ha => ?_) (fun ha => read_pieces_tail H q ha)
        have hnv : c.inValArray (afterTail q st) a = false := by simp [Contract.inValArray, hva]
        simp only [Contract.perm, hnf, inLane_false hl, hnv, inPieces_nil, inFrame_afterTail, Bool.or_false] at ha
        simp only [Contract.inFrame, afterTail, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
        simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        left; left; left
        rcases ha with (ha | ha) | ha
        · left; left; left; rw [hrsp_eq] at ha; omega
        · left; left; right
          have h1 : st.reg RSP ≤ a := of_decide_eq_true ha.1
          have h2 : a < st.reg RSP + c.slot := of_decide_eq_true ha.2
          exact ⟨by omega, by omega⟩
        · left; right
          obtain ⟨⟨r, l⟩, m, hin⟩ := List.any_eq_true.mp ha
          obtain ⟨b0, l0, hm, er, el⟩ := hregion r l m
          simp only [Bool.and_eq_true, decide_eq_true_eq, er, el] at hin
          exact List.any_eq_true.mpr ⟨(b0, l0), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hin⟩
      have hwrite : ∀ a, (c.perm ctx.pieces (afterTail q st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true := by
        intro a ha
        simp only [Contract.perm, hno, inFrame_afterTail, Bool.or_false] at ha
        simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq] at ha
        simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        left; rw [hrsp_eq] at ha; omega
      refine ⟨hpre, hread, hwrite, fun s2 post hdata2 => ?_⟩
      let s2p := setReg s2 RSP (s0.reg RSP)
      obtain ⟨psmall, hkeep, hvec2⟩ := mkPre s2 post
      have pmem := post.2.2.2.1
      have pret := post.2.2.2.2.1
      have hmem2 : ∀ a, a + c.stackAt st < st.reg RSP ∨ st.reg RSP ≤ a → s2p.mem a = st.mem a := fun a ha =>
        pmem a (by rw [inFrame_afterTail]; simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega) (hno _ a)
      have Hafter := afterCall_holds c (c.stackAt st) hregs H wf hrsp (by omega) (by omega) hstack hkeep psmall hmem2 (fun x r n m => (E.outAt m).2) hdata2 hvec2
      have wafter := afterCall_wf wf c hregs 0
      have ag := afterRho_agree c.regs s.nvars ρ s2p
      cases hret' : c.returns with
      | none =>
        simp only [hret'] at h
        cases V.pure_ok h
        exact ⟨_, ag, Nat.le_add_right _ _, Hafter, wafter⟩
      | some e =>
        simp only [hret'] at h
        obtain ⟨⟨res, s3⟩, r1, e1, h⟩ := V.bind_ok h
        have envb : EnvB s.nvars env := calleeEnv_bounded wf c.args c.argRegs (fun r m => T.arg_lt m) henv
        obtain ⟨ρ3, c3, sem, bd⟩ := seval_sound E env e e1 Hafter wafter (envb.mono (Nat.le_add_right _ _))
        have ag3 : Agree s.nvars ρ ρ3 := Agree.trans (Nat.le_add_right _ _) ag c3.agree
        have henv3 : semEnv ctx s0 ρ3 env = c.env (afterTail q st) := by
          rw [← semEnv_agree envb ag3]
          exact semEnv_calleeEnv (s1 := afterTail q st) H.entry (fun r m => H.reg r (T.arg_lt m))
            (fun b0 l0 hm k hk => by
              obtain ⟨fit, apart⟩ := E.regionAt hm
              exact H.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
                (E.region_notOut hm (Nat.le_add_right _ _) (by omega)))
            c.args c.argRegs (fun r m => m) henv
        rw [henv3] at sem
        have val := pret e hret'
        have pos : c.retReg < c.regs := (retReg_spec c).1
        have hret_ne : c.retReg ≠ RSP := (retReg_spec c).2.1
        have hs2p_ret : s2p.reg c.retReg = s2.reg c.retReg := by simp [s2p, setReg, hret_ne]
        have hnew : ev ρ3 (Lin.var (s.nvars + c.retReg)) = s2.reg c.retReg := by
          rw [ev_var, ← c3.agree (s.nvars + c.retReg) (by simp only [Sym.afterCall]; omega), afterRho_new c.regs s.nvars ρ s2p pos, hs2p_ret]
        have bvar : bounded s3.nvars (Lin.var (s.nvars + c.retReg)) :=
          bounded_var (Nat.lt_of_lt_of_le (show s.nvars + c.retReg < s.nvars + c.regs by omega) c3.mono)
        cases res with
        | list _ => exact (refuse_ok h).elim
        | tail call =>
          simp only at h; cases V.pure_ok h
          have hv : SFact.holds ctx s0 ρ3 (.value call (Lin.var (s.nvars + c.retReg))) := by
            show CallValue ctx s0 ρ3 call (.int (ev ρ3 (Lin.var (s.nvars + c.retReg))))
            rw [hnew]; exact (sem _).mp val
          exact ⟨ρ3, ag3, Nat.le_trans (Nat.le_add_right _ _) c3.mono, c3.holds.withSpec _ hv, c3.wf.withSpec _ ⟨bd, bvar⟩⟩
        | val v =>
          cases v with
          | region _ | bool _ => exact (refuse_ok h).elim
          | lin v =>
            simp only at h; cases V.pure_ok h
            have same := Value.unique sem val
            simp only [semv] at same; injection same with same
            exact ⟨ρ3, ag3, Nat.le_trans (Nat.le_add_right _ _) c3.mono,
              c3.holds.more _ (all_two (by rw [holds_iff, ev_sub, hnew]; omega) (by rw [holds_iff, ev_sub, hnew]; omega)),
              c3.wf.more _ (all_two (bounded_sub bd bvar) (bounded_sub bvar bd))⟩
  · -- Branch 2 or 3: `symCallB` or `symCallW`
    split at h
    · -- Branch 2: `symCallB`
      next hbyte =>
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hbyte
      obtain ⟨hinouts, hensW⟩ := hbyte
      have hct := callTouch_carried E H wf c
      have H0 := hct.holds; have wf0 := hct.wf
      have hsp0 : (callTouch ctx s c).sp = some 0 := by
        unfold callTouch; split
        · split
          · unfold Sym.touch; split
            · split
              · split <;> exact T.sp0
              · exact T.sp0
            · exact T.sp0
          · exact T.sp0
        · exact T.sp0
      unfold symCallB symCallB' at h
      simp only [hsp0] at h
      cases hplan : callB ctx (callTouch ctx s c) c with
      | error _ => simp [hplan] at h; exact (refuse_ok h).elim
      | ok plan =>
        simp only [hplan] at h
        obtain ⟨_, r1, hbounds, h⟩ := V.bind_ok h
        cases V.pure_ok h
        obtain ⟨run, r, n, e, ids, env, args, vs, d, hmb, hfx, _, hret0, hres, houts, hens, erun, elo, ehi, hcr, hce, hv, hown, hglen,
          hwl, hfd, hfk, hkeys, hdl, hwords⟩ := callB_spec hplan
        obtain ⟨xw, b, n0, how, hio, n4, hfit, hreg_r, hnow, hwi⟩ := callRun_spec hcr
        have hwm := List.mem_of_getElem? how
        have hout := E.outAt hwm
        have rmem : (run, r, n) ∈ c.outs := by rw [houts]; exact List.mem_cons_self ..
        have rarg : r ∈ c.argRegs := outsIn_mem c.args c.argRegs run r n rmem
        have b16 := outs_lt hwm
        have hrb : st.reg r = s0.reg b + 4 * plan.first := by
          have := H0.reg r (T.arg_lt rarg); rw [hreg_r ρ, H0.entry b b16] at this; omega
        have hregpart : ∀ r' l', (r', l') ∈ c.regions → ∃ b' off nn lb, regionPart ctx (callTouch ctx s c) r' l' = some (b', off, nn) ∧
            r' ∈ c.argRegs ∧ l' ∈ c.argRegs ∧ (b', lb) ∈ ctx.contract.regions ∧ 0 ≤ ev ρ off ∧
            (st.reg r' : Int) = s0.reg b' + ev ρ off ∧ ev ρ off + st.reg l' ≤ s0.reg lb := by
          intro r' l' m
          obtain ⟨b', off, nn, hp⟩ := calleeB_regions c c.args c.argRegs hce r' l' m
          obtain ⟨ra, len, hlen⟩ := regionsIn_mem c c.args c.argRegs r' l' m
          have la := regOfIn_mem len c.args c.argRegs l' hlen
          obtain ⟨lb, g1, _, g3, g4, g5⟩ := regionPart_sound E H0 (T.arg_lt ra) (T.arg_lt la) hp
          exact ⟨b', off, nn, lb, hp, ra, la, g1, g3, g4, g5⟩
        have hspan : ∀ r' l' b' off nn, r' ∈ c.argRegs → l' ∈ c.argRegs → regionPart ctx (callTouch ctx s c) r' l' = some (b', off, nn) →
            0 ≤ ev ρ off ∧ (ev ρ nn).toNat = st.reg l' ∧ 0 ≤ ev ρ nn ∧
            ∀ k, k < st.reg l' → st.mem (st.reg r' + k) = s0.mem (s0.reg b' + (ev ρ off).toNat + k) := by
          intro r' l' b' off nn ra la hp
          obtain ⟨lb, g1, g2, g3, g4, g5⟩ := regionPart_sound E H0 (T.arg_lt ra) (T.arg_lt la) hp
          have hlen := H0.reg l' (T.arg_lt la); have hregn := E.regionAt g1; subst g2
          refine ⟨g3, by omega, by omega, fun k hk => ?_⟩
          have ea : st.reg r' = s0.reg b' + (ev ρ off).toNat := by omega
          rw [ea]
          exact H0.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (E.region_notOut g1 (by omega) (by omega))
        have henv : EnvDen ctx s0 ρ (callTouch ctx s c).terms env (c.env (afterTail q st)) :=
          calleeB_sound (T := (callTouch ctx s c).terms) (s1 := afterTail q st) H0 c hregs (fun _ _ => rfl) hspan c.args c.argRegs (fun _ m => m) hce
        have hpre : c.pre q (afterTail q st) := by
          refine ⟨rfl, H0.small, by show c.stackAt st ≤ st.reg RSP; omega, by show st.reg RSP + c.slot < M64; omega, hq,
            fun r' l' m => ?_, fun x' r' n' m => ?_, (by rw [houts]; exact List.Pairwise.cons (fun _ m => nomatch m) List.Pairwise.nil),
            fun _ _ _ m => (by rw [hfx] at m; cases m), fun x' bd m r' hr' => ?_,
            fun _ _ _ _ _ _ m => (by rw [hfx] at m; cases m),
            fun _ _ _ _ _ ht => (by rw [tableAt_none hl] at ht; cases ht),
            EX.atLeast, harm_align, EX.preLines, (fun _ _ _ _ _ m => (by rw [hva] at m; cases m)), EX.aligns, EX.disjoint⟩
          · obtain ⟨b', off, nn, lb, _, _, _, g1, g3, g4, g5⟩ := hregpart r' l' m
            obtain ⟨fit, apart⟩ := E.regionAt g1
            show st.reg r' + st.reg l' ≤ M64 ∧ (st.reg r' + st.reg l' ≤ st.reg RSP - c.stackAt (afterTail q st) ∨ st.reg RSP + c.slot ≤ st.reg r')
            rw [stackAt_afterTail, hrsp_eq, hslot]; omega
          · rw [houts] at m; simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m
            obtain ⟨_, er', en'⟩ := m
            rw [er', en']
            show st.reg r + n ≤ M64 ∧ (st.reg r + n ≤ st.reg RSP - c.stackAt (afterTail q st) ∨ st.reg RSP + c.slot ≤ st.reg r) ∧
              ∀ r'' l'', (r'', l'') ∈ c.regions → st.reg r + n ≤ st.reg r'' ∨ st.reg r'' + st.reg l'' ≤ st.reg r
            refine ⟨by omega, by rw [stackAt_afterTail, hrsp_eq, hslot]; omega, fun r'' l'' m' => ?_⟩
            obtain ⟨b', off, nn, lb, _, _, _, g1, g3, g4, g5⟩ := hregpart r'' l'' m'
            have hap := E.outRegion hwm g1; omega
          · obtain ⟨_, _, he⟩ := each_mem hbounds (x', bd) m
            simp only [hr'] at he
            have hge := entail_sound he ρ H0.facts; rw [ev_sub, ev_const] at hge
            have ra := regOfIn_mem x' c.args c.argRegs r' hr'
            have := H0.reg r' (T.arg_lt ra); show st.reg r' < bd; omega
        have hread : ∀ a, (c.perm ctx.pieces (afterTail q st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true := by
          intro a ha
          rw [perm_read_split, Bool.or_eq_true] at ha
          refine ha.elim (fun ha => ?_) (fun ha => read_pieces_tail H0 q ha)
          have hnf : c.inFixed (afterTail q st) a = false := by simp [Contract.inFixed, hfx, hinouts]
          have hnv : c.inValArray (afterTail q st) a = false := by simp [Contract.inValArray, hva]
          simp only [Contract.perm, hnf, inLane_false hl, hnv, inPieces_nil, inFrame_afterTail, Bool.or_false] at ha
          simp only [Contract.inFrame, afterTail, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          left; left; left
          rcases ha with (ha | ha) | ha
          · left; left; left; rw [hrsp_eq] at ha; omega
          · left; left; right
            have h1 : st.reg RSP ≤ a := of_decide_eq_true ha.1
            have h2 : a < st.reg RSP + c.slot := of_decide_eq_true ha.2
            exact ⟨by omega, by omega⟩
          · left; right
            obtain ⟨⟨r', l'⟩, m, hin⟩ := List.any_eq_true.mp ha
            obtain ⟨b', off, nn, lb, _, _, _, g1, g3, g4, g5⟩ := hregpart r' l' m
            rw [Bool.and_eq_true] at hin
            have hi1 : st.reg r' ≤ a := of_decide_eq_true hin.1
            have hi2 : a < st.reg r' + st.reg l' := of_decide_eq_true hin.2
            exact List.any_eq_true.mpr ⟨(b', lb), g1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        have hwrite : ∀ a, (c.perm ctx.pieces (afterTail q st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true := by
          intro a ha
          simp only [Contract.perm, inFrame_afterTail, Bool.or_eq_true] at ha
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          rcases ha with ha | ha
          · left; simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq] at ha; rw [hrsp_eq] at ha; omega
          · right
            simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, afterTail, hrb] at ha
            unfold Contract.inOut
            exact List.any_eq_true.mpr ⟨(xw, b, n0), hwm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        refine ⟨hpre, hread, hwrite, fun s2 post hdata2 => ?_⟩
        let s2p := setReg s2 RSP (s0.reg RSP)
        obtain ⟨psmall, hkeep, hvec2⟩ := mkPre s2 post
        obtain ⟨_, _, _, pmem, _, _, hpost_ens, _⟩ := post
        have hmem2 : ∀ a, a + c.stackAt st < st.reg RSP ∨ st.reg RSP ≤ a →
            a < s0.reg b + 4 * plan.first ∨ s0.reg b + 4 * (plan.first + n / 4) ≤ a → s2p.mem a = st.mem a := fun a ha hb =>
          pmem a (by rw [inFrame_afterTail]; simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (by simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not, afterTail, hrb]; omega)
        have hcpre : c.preVals ctx.defs (afterTail q st) := fun _ _ _ _ _ m => by rw [hva] at m; cases m
        obtain ⟨r_, n_, a_, b_, l, hrm, hlo, hhi, hval, ha0, hab, hbn, hlm⟩ := (hpost_ens hcpre).1 e (by rw [hens]; exact List.mem_cons_self ..)
        rw [erun, houts] at hrm
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq, true_and] at hrm
        obtain ⟨e1, e2⟩ := hrm; subst r_ n_
        rw [elo] at hlo; rw [ehi] at hhi
        have ea := value_num hlo; have eb := value_num hhi; subst ea eb
        have hll : l.length = n := by omega
        have henvA : c.envAfter (afterTail q st) s2 = c.env (afterTail q st) := by simp only [Contract.envAfter, hres]
        rw [hv, henvA] at hval
        obtain ⟨f2, as2, d2, ha2, hd2, hlen2, hev2⟩ := call_def hown hglen hval
        rw [hfd] at hd2; injection hd2 with hd2; subst hd2
        let nums := (List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4
        have hnl : nums.length = n / 4 := by simp [nums]
        have hlt : ∀ v ∈ nums, v < W32 := fun v mv => by obtain ⟨k, _, rfl⟩ := List.mem_map.mp mv; exact load_lt s2.mem _ 4
        have hrun : ∀ k, k < n / 4 → ∀ bb, bb < 4 → s2p.mem (s0.reg b + 4 * (plan.first + k) + bb) = nums.getD k 0 / 256 ^ bb % 256 := by
          intro k hk bb hbb
          have hget : nums.getD k 0 = load s2.mem (s0.reg b + 4 * (plan.first + k)) 4 := by
            rw [getD_of_lt nums 0 (by simpa [nums] using hk)]; simp [nums]
          rw [hget]; exact (load4_byteAt s2.mem _ bb hbb (fun _ _ => Fin.isLt _)).symm
        have hlb : l.map (fun (x : Nat) => Val.int x) = wordBytes nums := by
          have W := wordBytes_range s2.mem nums (s0.reg b + 4 * plan.first) (fun k hk bb hbb => by
            have hk' : k < n / 4 := by simpa [nums] using hk
            rw [show s0.reg b + 4 * plan.first + 4 * k + bb = s0.reg b + 4 * (plan.first + k) + bb by omega]
            exact hrun k hk' bb hbb)
          rw [← W, hnl]
          apply List.ext_getElem
          · simp only [List.length_map, List.length_range]; omega
          · intro k h1 _; have hk : k < l.length := by simpa using h1
            have := hlm k hk; simp only [afterTail, hrb] at this; simp only [List.getElem_map, List.getElem_range]; rw [← this]; simp
        have hheld : ctx.contract.preVals ctx.defs s0 → ∃ d', findDef ctx.defs plan.g = some d' ∧ d'.params.length = plan.keys.length ∧
            Value ctx.defs (d'.params.zip (plan.keys.map (Key.val ctx s0 ρ (callTouch ctx s c).terms))) d'.body
              (if true then .list (wordBytes nums) else .list (nums.map Val.word)) := by
          intro hpv
          obtain ⟨B, hB⟩ := held_bound H0 hpv
          obtain ⟨as, eas, das⟩ := wevalList_sound (ev' := evalSpec ctx.defs (WFUEL + B) (c.env (afterTail q st)))
            (fun e' v' hv' => weval_sound H0 wf0 hpv hB WFUEL env _ e' v' hv' henv) args vs hwl
          have same : as2 = as := by
            have a1 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.env (afterTail q st)))
              (fun a v hh => evalSpec_mono ctx.defs f2 hh _ (Nat.le_max_left _ _)) args ha2
            have a2 := evalList_mono (ev' := evalSpec ctx.defs (max f2 (WFUEL + B)) (c.env (afterTail q st)))
              (fun a v hh => evalSpec_mono ctx.defs (WFUEL + B) hh _ (Nat.le_max_right _ _)) args eas
            rw [a1] at a2; injection a2
          subst same
          have ekeys : as2 = plan.keys.map (Key.val ctx s0 ρ (callTouch ctx s c).terms) := flatKeys_den wf0 das hfk
          exact ⟨d, hfd, hdl, f2, by rw [← ekeys, if_pos rfl, ← hlb]; exact hev2⟩
        have Hafter := afterCallW_holds E c (c.stackAt st) hregs H0 wf0 hrsp (by omega) (by omega) hkeep psmall how
          (show 4 * (plan.first + n / 4) ≤ n0 by omega) hnow hmem2 hdata2 hnl hlt hrun hkeys (bytes := true) (rfs := []) (recVal := none) (Or.inl ⟨rfl, hheld⟩) hvec2
        have wafter := afterCallW_wf wf0 c hregs 0 plan.w plan.first (n / 4) plan.g hkeys true [] (fun h => by simp at h)
        rw [hwords]
        exact ⟨_, hct.then ⟨afterRhoW_agree c.regs (callTouch ctx s c).nvars ρ s2p nums none,
          by rw [afterCallW_nvars]; show (callTouch ctx s c).nvars ≤ (callTouch ctx s c).nvars + c.regs + n / 4 + _; omega, Hafter, wafter⟩⟩
    · -- Branch 3: `symCallW`
      have hct := callTouch_carried E H wf c
      have hft := callFrameTouch_carried (ctx := ctx) (s0 := s0) (ρ := ρ) (st := st) c (c.fixeds ++ c.inouts) hct.holds hct.wf
      let s1 := callFrameTouch (callTouch ctx s c) c
      have H0 : Holds ctx s0 ρ s1 st := hft.holds
      have wf0 : WF ctx s1 := hft.wf
      have hs1_meta : s1.sp = some 0 ∧ ∀ x ∈ c.fixeds, frameAt s1 x.2.1 = none := by
        have hreg_eq : s1.reg = s.reg := by
          have h1 : (callFrameTouch (callTouch ctx s c) c).reg = (callTouch ctx s c).reg := by
            unfold callFrameTouch
            have go : ∀ (l : List (String × Nat × Nat)) (stx : Sym),
                (l.foldl (fun s (x : String × Nat × Nat) => match frameAt s x.2.1 with | some k => { s with tab := touchFrameRange s k (x.2.2 / 4) 0 } | none => s) stx).reg = stx.reg := by
              intro l; induction l with | nil => intro _; rfl | cons x xs ih =>
                intro stx; simp only [List.foldl_cons]; rw [ih]; cases frameAt stx x.2.1 <;> rfl
            exact go _ _
          have h2 : (callTouch ctx s c).reg = s.reg := by
            unfold callTouch; split
            · split
              · unfold Sym.touch; split
                · split
                  · split <;> rfl
                  · rfl
                · rfl
              · rfl
            · rfl
          exact h1.trans h2
        refine ⟨by unfold Sym.sp; rw [hreg_eq]; exact T.sp0, fun x hx => by unfold frameAt; rw [hreg_eq]; exact T.noFrameFix x hx⟩
      have h : symCallW' ctx s1 c items = .ok (s', rest) := h
      unfold symCallW' at h
      rw [hs1_meta.1] at h
      cases hplan : callW ctx s1 c with
      | error _ => rw [hplan] at h; exact (refuse_ok h).elim
      | ok plan =>
        rw [hplan] at h
        obtain ⟨_, r1, hbounds, h⟩ := V.bind_ok h
        obtain ⟨_, r2, _, h⟩ := V.bind_ok h
        cases V.pure_ok h
        obtain ⟨run, r, n, e, ids, env, args, vs, d, houts, hinouts, hens, erun, epart, hcr, hce, hpenv, hown, hglen, hT, hwl, hfd, hfk,
          hkeys, hdl, hwords, hshape⟩ := callWby_spec (find := callRun ctx s1) hplan
        obtain ⟨xw, b, n0, how, hio, n4, hfit, hreg_r, hnow, hwi⟩ := callRun_spec hcr
        have hwm := List.mem_of_getElem? how
        have hout := E.outAt hwm
        have rmem : (run, r, n) ∈ c.outs := by rw [houts]; exact List.mem_cons_self ..
        have rarg : r ∈ c.argRegs := outsIn_mem c.args c.argRegs run r n rmem
        have b16 := outs_lt hwm
        have hrb : st.reg r = s0.reg b + 4 * plan.first := by
          have := H0.reg r (T.arg_lt rarg); rw [hreg_r ρ, H0.entry b b16] at this; omega
        have hspan : ∀ r' l' b' off nn, r' ∈ c.argRegs → l' ∈ c.argRegs → regionPart ctx s1 r' l' = some (b', off, nn) →
            0 ≤ ev ρ off ∧ (ev ρ nn).toNat = st.reg l' ∧ 0 ≤ ev ρ nn ∧
            ∀ k, k < st.reg l' → st.mem (st.reg r' + k) = s0.mem (s0.reg b' + (ev ρ off).toNat + k) := by
          intro r' l' b' off nn ra la hp
          obtain ⟨lb, g1, g2, g3, g4, g5⟩ := regionPart_sound E H0 (T.arg_lt ra) (T.arg_lt la) hp
          have hlen := H0.reg l' (T.arg_lt la); have hregn := E.regionAt g1; subst g2
          refine ⟨g3, by omega, by omega, fun k hk => ?_⟩
          have ea : st.reg r' = s0.reg b' + (ev ρ off).toNat := by omega
          rw [ea]
          exact H0.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (E.region_notOut g1 (by omega) (by omega))
        have hregpart : ∀ r' l', (r', l') ∈ c.regions → ∃ b' off nn lb, regionPart ctx s1 r' l' = some (b', off, nn) ∧
            r' ∈ c.argRegs ∧ l' ∈ c.argRegs ∧ (b', lb) ∈ ctx.contract.regions ∧ 0 ≤ ev ρ off ∧
            (st.reg r' : Int) = s0.reg b' + ev ρ off ∧ ev ρ off + st.reg l' ≤ s0.reg lb := by
          intro r' l' m
          obtain ⟨b', off, nn, hp⟩ := calleeW_regions c c.args c.argRegs hce r' l' m
          obtain ⟨ra, len, hlen⟩ := regionsIn_mem c c.args c.argRegs r' l' m
          have la := regOfIn_mem len c.args c.argRegs l' hlen
          obtain ⟨lb, g1, _, g3, g4, g5⟩ := regionPart_sound E H0 (T.arg_lt ra) (T.arg_lt la) hp
          exact ⟨b', off, nn, lb, hp, ra, la, g1, g3, g4, g5⟩
        obtain ⟨extT, okT⟩ := inputs_table wf0 (partNodes ctx s1 c.args c.argRegs) (partNodes_inputs c.args c.argRegs)
        rw [← hT] at extT okT
        have CT := Carried.terms H0 wf0 extT okT
        have HT := CT.holds; have wfT := CT.wf
        have hpart : ∀ x' r' n', (x', r', n') ∈ c.fixeds → r' ∈ c.argRegs ∧ ∃ j b' cst, fixedPart ctx s1 r' n' = some (j, b', cst) := by
          intro x' r' n' m
          refine ⟨fixedsIn_mem c.args c.argRegs x' r' n' m, ?_⟩
          rcases calleeW_fixeds c.args c.argRegs hce x' r' n' m with hf | ⟨cf, fids, hfr⟩
          · exact hf
          · exfalso
            unfold frameRun at hfr
            rw [hs1_meta.2 (x', r', n') m] at hfr; simp at hfr
        have hfixmem : ∀ r' n' j b' cst, r' ∈ c.argRegs → fixedPart ctx s1 r' n' = some (j, b', cst) →
            ∀ k, k < n' → st.mem (st.reg r' + k) = s0.mem (s0.reg b' + cst + k) ∧ (s0.mem (s0.reg b' + cst + k)).val < 256 := by
          intro r' n' j b' cst ra hf k hk
          obtain ⟨g3, -, f1, f2, f3, f4, -⟩ := fixedPart_sound E H0 (T.arg_lt ra) hf
          refine ⟨?_, f3 k hk⟩
          rw [g3]
          exact H0.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (by
              unfold Contract.inOut; rw [List.any_eq_false]
              intro ⟨x'', r'', n''⟩ hm; have := f4 x'' r'' n'' hm
              simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
        have hidsb : ids.length = n / 4 ∧ ∀ j, j < n / 4 → ∀ bb, bb < 4 →
            st.mem (s0.reg b + 4 * (plan.first + j) + bb) = den (inpOf ctx s0) ρ plan.terms (ids.getD j 0) / 256 ^ bb % 256 := by
          obtain ⟨idlen, hwritten⟩ := writtenIds_spec (n / 4) plan.first hwi
          refine ⟨idlen, fun j hj bb hbb => ?_⟩
          obtain ⟨_, g2⟩ := HT.words.wrote plan.w (plan.first + j) (ids.getD j 0) (hwritten j hj) xw b n0 how
          exact g2 bb hbb
        obtain ⟨idlen, hbytes⟩ := hidsb
        have hiobytes : (List.range n).map (fun k => Val.int (st.mem (st.reg r + k))) =
            wordBytes (ids.map (den (inpOf ctx s0) ρ plan.terms)) := by
          have := wordBytes_range st.mem (ids.map (den (inpOf ctx s0) ρ plan.terms)) (st.reg r)
            (fun j hj bb hbb => by
              have hj' : j < ids.length := by simpa using hj
              rw [hrb, show s0.reg b + 4 * plan.first + 4 * j + bb = s0.reg b + 4 * (plan.first + j) + bb by omega,
                hbytes j (by omega) bb hbb, getD_of_lt _ _ hj, getD_of_lt _ _ hj', List.getElem_map])
          rw [List.length_map, idlen, show 4 * (n / 4) = n by omega] at this
          exact this
        have hframe_vac : ∀ r' n' cf fids, r' ∈ c.argRegs → frameRun s1 r' n' = some (cf, fids) →
            (List.range n').map (fun k => Val.int (st.mem (st.reg r' + k))) = wordBytes (fids.map (den (inpOf ctx s0) ρ plan.terms)) := by
          intro r' n' cf fids ra hfr
          obtain ⟨⟨sp', hsp', hle⟩, hn0, _, hreg', hlen, hwords⟩ := frameRun_sound E H0 wf0 (T.arg_lt ra) hfr
          rw [hs1_meta.1] at hsp'; cases hsp'
          have := wordBytes_range st.mem (fids.map (den (inpOf ctx s0) ρ plan.terms)) (st.reg r')
            (fun j hj bb hbb => by
              have hj' : j < fids.length := by simpa using hj
              obtain ⟨hlt, _, hld⟩ := hwords j (by omega)
              have hA : st.reg r' = ((s0.reg RSP : Int) + cf).toNat := by omega
              have hb : (st.mem (((s0.reg RSP : Int) + cf).toNat + 4 * j + bb)).val =
                  den (inpOf ctx s0) ρ plan.terms (fids.getD j 0) / 256 ^ bb % 256 := by
                rw [den_ext wf0.words.table extT hlt, ← hld]
                exact (load4_byteAt st.mem _ bb hbb (fun _ _ => Fin.isLt _)).symm
              rw [hA, hb, getD_of_lt _ _ hj, getD_of_lt _ _ hj', List.getElem_map])
          rw [List.length_map, hlen, show 4 * (n' / 4) = n' by omega] at this
          exact this
        have henv : EnvDen ctx s0 ρ plan.terms env (c.envW (afterTail q st)) := by
          rw [envW_plain hl]
          exact calleeW_sound (T := plan.terms) (s1 := afterTail q st) H0 c hregs (fun _ _ => rfl) hfixmem hframe_vac hspan c.args c.argRegs (fun _ m => m)
            (fun x' r' n' m => by
              change (x', r', n') ∈ c.inouts at m
              rw [hinouts] at m; simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m
              obtain ⟨_, er', en'⟩ := m; rw [er', en']; exact hiobytes) hce
        have hpre : c.pre q (afterTail q st) := by
          refine ⟨rfl, H0.small, by show c.stackAt (afterTail q st) ≤ st.reg RSP; rw [stackAt_afterTail]; omega,
            by show st.reg RSP + c.slot < M64; omega, hq,
            fun r' l' m => ?_, fun x' r' n' m => ?_, (by rw [houts]; exact List.Pairwise.cons (fun _ m => nomatch m) List.Pairwise.nil),
            fun x' r' n' m => ?_, fun x' bd m r' hr' => ?_, EX.mbounds,
            fun _ _ _ _ _ ht => (by rw [tableAt_none hl] at ht; cases ht),
            EX.atLeast, harm_align, EX.preLines, (fun _ _ _ _ _ m => (by rw [hva] at m; cases m)), EX.aligns, EX.disjoint⟩
          · obtain ⟨b', off, nn, lb, _, _, _, g1, g3, g4, g5⟩ := hregpart r' l' m
            obtain ⟨fit, apart⟩ := E.regionAt g1
            show st.reg r' + st.reg l' ≤ M64 ∧ (st.reg r' + st.reg l' ≤ st.reg RSP - c.stackAt (afterTail q st) ∨ st.reg RSP + c.slot ≤ st.reg r')
            rw [stackAt_afterTail, hrsp_eq, hslot]; omega
          · rw [houts] at m; simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m
            obtain ⟨_, er', en'⟩ := m; rw [er', en']
            show st.reg r + n ≤ M64 ∧ (st.reg r + n ≤ st.reg RSP - c.stackAt (afterTail q st) ∨ st.reg RSP + c.slot ≤ st.reg r) ∧
              ∀ r'' l'', (r'', l'') ∈ c.regions → st.reg r + n ≤ st.reg r'' ∨ st.reg r'' + st.reg l'' ≤ st.reg r
            refine ⟨by omega, by rw [stackAt_afterTail, hrsp_eq, hslot]; omega, fun r'' l'' m' => ?_⟩
            obtain ⟨b', off, nn, lb, _, _, _, g1, g3, g4, g5⟩ := hregpart r'' l'' m'
            have hap := E.outRegion hwm g1; omega
          · obtain ⟨ra, j, b', cst, hf⟩ := hpart x' r' n' m
            obtain ⟨g3, -, f1, f2, -, f4, -⟩ := fixedPart_sound E H0 (T.arg_lt ra) hf
            show st.reg r' + n' ≤ M64 ∧ (st.reg r' + n' ≤ st.reg RSP - c.stackAt (afterTail q st) ∨ st.reg RSP + c.slot ≤ st.reg r') ∧
              ∀ x'' r'' n'', (x'', r'', n'') ∈ c.outs → st.reg r' + n' ≤ st.reg r'' ∨ st.reg r'' + n'' ≤ st.reg r'
            refine ⟨by omega, by rw [stackAt_afterTail, hrsp_eq, hslot]; omega, fun x'' r'' n'' m'' => ?_⟩
            rw [houts] at m''; simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at m''
            obtain ⟨_, er'', en''⟩ := m''; rw [er'', en'']
            have := f4 xw b n0 hwm; omega
          · obtain ⟨_, _, he⟩ := each_mem hbounds (x', bd) m
            simp only [hr'] at he
            have hge := entail_sound he ρ H0.facts; rw [ev_sub, ev_const] at hge
            have ra := regOfIn_mem x' c.args c.argRegs r' hr'
            have := H0.reg r' (T.arg_lt ra); show st.reg r' < bd; omega
        have hread : ∀ a, (c.perm ctx.pieces (afterTail q st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true := by
          intro a ha
          rw [perm_read_split, Bool.or_eq_true] at ha
          refine ha.elim (fun ha => ?_) (fun ha => read_pieces_tail H0 q ha)
          have hnv : c.inValArray (afterTail q st) a = false := by simp [Contract.inValArray, hva]
          simp only [Contract.perm, inLane_false hl, hnv, inPieces_nil, inFrame_afterTail, Bool.or_false] at ha
          simp only [Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true] at ha
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          left; left; left
          rcases ha with ((ha | ha) | ha) | ha
          · left; left; left; simp only [decide_eq_true_eq] at ha; rw [hrsp_eq] at ha; omega
          · left; left; right
            have h1 : st.reg RSP ≤ a := of_decide_eq_true ha.1
            have h2 : a < st.reg RSP + c.slot := of_decide_eq_true ha.2
            exact ⟨by omega, by omega⟩
          · left; right
            obtain ⟨⟨r', l'⟩, m, hin⟩ := List.any_eq_true.mp ha
            obtain ⟨b', off, nn, lb, _, _, _, g1, g3, g4, g5⟩ := hregpart r' l' m
            rw [Bool.and_eq_true] at hin
            have hi1 : st.reg r' ≤ a := of_decide_eq_true hin.1
            have hi2 : a < st.reg r' + st.reg l' := of_decide_eq_true hin.2
            exact List.any_eq_true.mpr ⟨(b', lb), g1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
          · simp only [Contract.inFixed, Bool.or_eq_true] at ha ⊢
            rcases ha with ha | ha
            · obtain ⟨⟨x', r', n'⟩, m, hin⟩ := List.any_eq_true.mp ha
              obtain ⟨ra, j, b', cst, hf⟩ := hpart x' r' n' m
              obtain ⟨g3, -, -, -, -, -, fw⟩ := fixedPart_sound E H0 (T.arg_lt ra) hf
              simp only [Bool.and_eq_true, decide_eq_true_eq, afterTail, g3] at hin
              rcases fw with ⟨x0, n0', hm0, hle⟩ | ⟨l0, hm0, hle⟩
              · right; left; exact List.any_eq_true.mpr ⟨(x0, b', n0'), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
              · left; right; exact List.any_eq_true.mpr ⟨(b', l0), hm0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
            · right; right
              rw [hinouts] at ha
              simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, afterTail, hrb] at ha
              exact List.any_eq_true.mpr ⟨(xw, b, n0), hio, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        have hwrite : ∀ a, (c.perm ctx.pieces (afterTail q st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true := by
          intro a ha
          simp only [Contract.perm, inFrame_afterTail, Bool.or_eq_true] at ha
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          rcases ha with ha | ha
          · left; simp only [Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq] at ha; rw [hrsp_eq] at ha; omega
          · right
            simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, afterTail, hrb] at ha
            unfold Contract.inOut
            exact List.any_eq_true.mpr ⟨(xw, b, n0), hwm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        refine ⟨hpre, hread, hwrite, fun s2 post hdata2 => ?_⟩
        let s2p := setReg s2 RSP (s0.reg RSP)
        obtain ⟨psmall, hkeep, hvec2⟩ := mkPre s2 post
        obtain ⟨_, _, _, pmem, _, _, hpost_ens, _⟩ := post
        have hmem2 : ∀ a, a + c.stackAt st < st.reg RSP ∨ st.reg RSP ≤ a →
            a < s0.reg b + 4 * plan.first ∨ s0.reg b + 4 * (plan.first + n / 4) ≤ a → s2p.mem a = st.mem a := fun a ha hb =>
          pmem a (by rw [inFrame_afterTail]; simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
            (by simp only [Contract.inOut, houts, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not, afterTail, hrb]; omega)
        have hcpre : c.preVals ctx.defs (afterTail q st) := fun _ _ _ _ _ m => by rw [hva] at m; cases m
        rcases hshape with ⟨hnoRec, hveq⟩ | ⟨x, body, hne, _, hveq, hpb, hsum, hdist, hrr⟩
        · let nums := (List.range (n / 4)).map fun k => load s2.mem (s0.reg b + 4 * (plan.first + k)) 4
          have hnums : nums.length = n / 4 := by simp [nums]
          have hlt : ∀ v ∈ nums, v < W32 := fun v mv => by obtain ⟨k, _, rfl⟩ := List.mem_map.mp mv; exact load_lt s2.mem _ 4
          have hrun : ∀ k, k < n / 4 → ∀ bb, bb < 4 → s2p.mem (s0.reg b + 4 * (plan.first + k) + bb) = nums.getD k 0 / 256 ^ bb % 256 := by
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
            obtain ⟨r_, n_, l, hrm, hval, hll, hlm⟩ := (EnsureW.holds_whole epart).mp ((hpost_ens hcpre).2 e (by rw [hens]; exact List.mem_cons_self ..))
            rw [erun, houts] at hrm; simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq, true_and] at hrm
            obtain ⟨e1, e2⟩ := hrm; cases e1.symm; cases e2.symm
            rw [hveq] at hval
            obtain ⟨nums', hnums', hlt', hlb', hv'⟩ := postW_plain HT wfT hpv henv hown hglen hwl hfd hfk hdl hll n4 hval
            have heqn : nums' = nums := by
              obtain ⟨hl4, hlget⟩ := wordBytes_get nums' l hlb'
              apply List.ext_getElem
              · simp [nums, hnums']
              · intro k h1 h2
                have hk : k < n / 4 := by simpa [nums] using h2
                simp only [nums, List.getElem_map, List.getElem_range]
                have hlt_k : nums'[k] < 4294967296 := hlt' nums'[k] (List.getElem_mem h1)
                symm
                apply load4_of_bytes s2.mem (s0.reg b + 4 * (plan.first + k)) nums'[k] hlt_k
                intro bb hbb
                have hlt' : 4 * k + bb < l.length := by omega
                have := hlm (4 * k + bb) (by omega)
                simp only [afterTail, hrb] at this
                rw [show s0.reg b + 4 * (plan.first + k) + bb = s0.reg b + 4 * plan.first + (4 * k + bb) by omega, this, ← getD_of_lt l 0 hlt']
                exact (hlget k (by omega) bb hbb).trans (by rw [getD_of_lt nums' 0 h1])
            subst heqn; exact ⟨d, hfd, hdl, hv'⟩
          have Hafter := afterCallW_holds E c (c.stackAt st) hregs HT wfT hrsp (by omega) (by omega) hkeep psmall how
            (show 4 * (plan.first + n / 4) ≤ n0 by omega) hnow hmem2 hdata2 hnums hlt hrun hkeys (bytes := false) (rfs := plan.recFields) (recVal := none) hheld hvec2
          have wafter := afterCallW_wf wfT c hregs 0 plan.w plan.first (n / 4) plan.g hkeys false plan.recFields (fun h => by simp [hnoRec] at h)
          rw [hwords]
          exact ⟨_, hct.then (hft.then (CT.then ⟨afterRhoW_agree c.regs s1.nvars ρ s2p nums none,
            by rw [afterCallW_nvars]; show s1.nvars ≤ s1.nvars + c.regs + n / 4 + _; omega, Hafter, wafter⟩))⟩
        · obtain ⟨r_, n_, l, hrm, hval, hll, hlm⟩ := (EnsureW.holds_whole epart).mp ((hpost_ens hcpre).2 e (by rw [hens]; exact List.mem_cons_self ..))
          rw [erun, houts] at hrm; simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq, true_and] at hrm
          obtain ⟨e1, e2⟩ := hrm; cases e1.symm; cases e2.symm
          rw [hveq] at hval
          obtain ⟨nums, fvs, hnums, hlt, hlb, hrf, hv⟩ := postW_rec HT wfT henv hown hglen hwl hfd hfk hdl hll n4 hval hpb hsum hdist hrr
          obtain ⟨hl4, hlget⟩ := wordBytes_get nums l hlb
          have hrun : ∀ k, k < n / 4 → ∀ bb, bb < 4 → s2p.mem (s0.reg b + 4 * (plan.first + k) + bb) = nums.getD k 0 / 256 ^ bb % 256 := by
            intro k hk bb hbb
            show (s2.mem (s0.reg b + 4 * (plan.first + k) + bb)).val = nums.getD k 0 / 256 ^ bb % 256
            have lt' : 4 * k + bb < l.length := by omega
            have := hlm (4 * k + bb) lt'; simp only [afterTail, hrb] at this
            rw [show s0.reg b + 4 * (plan.first + k) + bb = s0.reg b + 4 * plan.first + (4 * k + bb) by omega, this, ← getD_of_lt l 0 lt']
            exact hlget k (by omega) bb hbb
          have Hafter := afterCallW_holds E c (c.stackAt st) hregs HT wfT hrsp (by omega) (by omega) hkeep psmall how
            (show 4 * (plan.first + n / 4) ≤ n0 by omega) hnow hmem2 hdata2 hnums hlt hrun hkeys (bytes := false) (rfs := plan.recFields) (recVal := some (.record fvs)) (Or.inr ⟨hne, d, fvs, rfl, hrf, hv⟩) hvec2
          have wafter := afterCallW_wf wfT c hregs 0 plan.w plan.first (n / 4) plan.g hkeys false plan.recFields (fun _ => by omega)
          rw [hwords]
          exact ⟨_, hct.then (hft.then (CT.then ⟨afterRhoW_agree c.regs s1.nvars ρ s2p nums (some (.record fvs)),
            by rw [afterCallW_nvars]; show s1.nvars ≤ s1.nvars + c.regs + n / 4 + _; omega, Hafter, wafter⟩))⟩

/-! ## Trace non-interference at a tail call -/

theorem tailArgClean_same {ctx : Ctx} {p q : Program} {a0 b0 sta stb : State}
    (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0)
    {ρa ρb : Nat → Int} {s : Sym} {name : String} {c : Contract}
    (T : TailOk ctx s name c)
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb)
    (Ma : MarksOk ctx a0 s.q sta) (A : Alike sta stb) :
    ∀ (args : List (String × Kind)) (regs : List Nat) (x : String),
      (∀ r ∈ regs, r ∈ c.argRegs) →
      callArgClean.go ctx s c x args regs = true →
      ∀ v, (envIn c (afterTail q sta) args regs).lookup x = some v →
           (envIn c (afterTail q stb) args regs).lookup x = some v
  | [], _, _, _, h, _, _ => by simp [callArgClean.go] at h
  | _, [], _, _, h, _, _ => by simp [callArgClean.go] at h
  | (n, k) :: args, r :: regs, x, hregs, h, v, hv => by
    have hr_in : r ∈ c.argRegs := hregs r (List.mem_cons_self ..)
    have hregs' : ∀ r' ∈ regs, r' ∈ c.argRegs := fun r' hr' => hregs r' (List.mem_cons_of_mem _ hr')
    cases k with
    | number =>
      simp only [envIn, List.lookup_cons] at hv ⊢
      cases hnx : (x == n) with
      | true =>
        simp only [callArgClean.go, str_beq_comm n x, hnx, ite_true] at h
        have hreq : sta.reg r = stb.reg r := A.reg r (Ma.reg r (List.contains_iff_mem.mp h))
        simp only [hnx, ite_true, afterTail, hreq] at hv ⊢; exact hv
      | false =>
        simp only [callArgClean.go, str_beq_comm n x, hnx, Bool.false_eq_true, ite_false] at h
        simp only [hnx, Bool.false_eq_true, ite_false] at hv ⊢
        exact tailArgClean_same Ea Eb ta T Ha Hb Ma A args regs x hregs' h v hv
    | bytes len =>
      cases hrl : c.regOf len with
      | none =>
        simp only [envIn, hrl] at hv ⊢
        simp only [callArgClean.go] at h
        cases hxn : (n == x) with
        | true => simp [hxn, hrl] at h
        | false => simp only [hxn, Bool.false_eq_true, ite_false] at h; exact tailArgClean_same Ea Eb ta T Ha Hb Ma A args regs x hregs' h v hv
      | some l =>
        simp only [envIn, hrl, List.lookup_cons] at hv ⊢
        cases hnx : (x == n) with
        | true =>
          simp only [callArgClean.go, str_beq_comm n x, hnx, hrl, ite_true, Bool.and_eq_true] at h
          obtain ⟨hlq, hfr⟩ := h
          have hleq : sta.reg l = stb.reg l := A.reg l (Ma.reg l (List.contains_iff_mem.mp hlq))
          cases hfind : findRun s r l ctx.contract.regions 0 with
          | none => simp [hfind] at hfr
          | some j =>
            obtain ⟨b0', l0', _, hget, er, el⟩ := findRun_spec hfind
            have hnh : ctx.contract.hiddenAt b0' = false := by
              rw [hfind] at hfr
              have hget' : ctx.contract.regions[j]? = some (b0', l0') := by simpa using hget
              simp only [hget', Bool.not_eq_true'] at hfr; exact hfr
            have hm0 : (b0', l0') ∈ ctx.contract.regions := List.mem_of_getElem? hget
            obtain ⟨hb0', hl0'⟩ := regions_lt hm0
            have l_in : l ∈ c.argRegs := regOfIn_mem len c.args c.argRegs l hrl
            have vra : sta.reg r = a0.reg b0' := by have := Ha.reg r (T.arg_lt hr_in); rw [er, ev_var, Ha.entry b0' hb0'] at this; omega
            have vla : sta.reg l = a0.reg l0' := by have := Ha.reg l (T.arg_lt l_in); rw [el, ev_var, Ha.entry l0' hl0'] at this; omega
            have vrb : stb.reg r = b0.reg b0' := by have := Hb.reg r (T.arg_lt hr_in); rw [er, ev_var, Hb.entry b0' hb0'] at this; omega
            have vlb : stb.reg l = b0.reg l0' := by have := Hb.reg l (T.arg_lt l_in); rw [el, ev_var, Hb.entry l0' hl0'] at this; omega
            have hbytes : ((List.range (sta.reg l)).map fun t => (sta.mem (sta.reg r + t)).val) =
                (List.range (stb.reg l)).map fun t => (stb.mem (stb.reg r + t)).val := by
              rw [hleq]; apply List.map_congr_left; intro t ht
              have ht' : t < stb.reg l := List.mem_range.mp ht
              have hta : t < a0.reg l0' := by omega
              have htb : t < b0.reg l0' := by omega
              have hma := Ha.mem (a0.reg b0' + t)
                (by have := (Ea.regionAt hm0).2; simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
                (Ea.region_notOut hm0 (Nat.le_add_right _ _) (by omega))
              have hmb := Hb.mem (b0.reg b0' + t)
                (by have := (Eb.regionAt hm0).2; simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
                (Eb.region_notOut hm0 (Nat.le_add_right _ _) (by omega))
              rw [vra, vrb, hma, hmb]
              have htb' := (ta.2.2.2.2.2.2.1 b0' l0' hm0 hnh).2 t hta
              exact congrArg Fin.val htb'
            simp only [hnx, ite_true, afterTail] at hv ⊢; rw [← hbytes]; exact hv
        | false =>
          simp only [callArgClean.go, str_beq_comm n x, hnx, Bool.false_eq_true, ite_false] at h
          simp only [hnx, Bool.false_eq_true, ite_false] at hv ⊢
          exact tailArgClean_same Ea Eb ta T Ha Hb Ma A args regs x hregs' h v hv
    | out _ | fixed _ | inout _ | valArray _ _ =>
      simp only [envIn] at hv ⊢
      simp only [callArgClean.go] at h
      exact tailArgClean_same Ea Eb ta T Ha Hb Ma A args regs x hregs' h v hv

theorem tailAllClean_imp {ctx : Ctx} {p q : Program} {a0 b0 sta stb : State}
    (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0)
    {ρa ρb : Nat → Int} {s : Sym} {name : String} {c : Contract}
    (T : TailOk ctx s name c)
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb)
    (Ma : MarksOk ctx a0 s.q sta) (A : Alike sta stb) :
    ∀ (e : SExpr) (ext : List (String × Val)),
    callAllClean ctx s c (ext.map Prod.fst) e = true →
    ExprImp ctx.defs (ext ++ c.env (afterTail q sta)) (ext ++ c.env (afterTail q stb)) e e := by
  intro e
  induction e with
  | num _ =>
    intro ext _
    exact ExprImp.of_val rfl fun _ ⟨f, hf⟩ => by cases f with | zero => cases hf | succ _ => exact ⟨1, by simpa [evalSpec] using hf⟩
  | nil =>
    intro ext _
    exact ⟨fun _ ⟨f, hf⟩ => by cases f <;> simp [evalSpec] at hf, fun _ _ hl => ⟨0, by simpa [evalList] using hl⟩⟩
  | cons a1 r1 iha ihr =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.cons (iha ext h.1) (ihr ext h.2)
  | name x =>
    intro ext h; simp only [callAllClean, Bool.or_eq_true] at h
    refine ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_
    cases f with | zero => cases hf | succ f =>
    simp only [evalSpec] at hf
    rcases h with hbd | harg
    · rw [lookup_append_mem hbd] at hf
      exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
    · cases hmem : (ext.map Prod.fst).contains x with
      | true =>
        rw [lookup_append_mem hmem] at hf
        exact ⟨1, by simp only [evalSpec, lookup_append_mem hmem]; exact hf⟩
      | false =>
        rw [lookup_append_not_mem hmem] at hf
        exact ⟨1, by simp only [evalSpec, lookup_append_not_mem hmem]; exact tailArgClean_same Ea Eb ta T Ha Hb Ma A c.args c.argRegs x (fun _ m => m) harg v hf⟩
  | bin _ _ _ iha ihb => intro ext h; simp only [callAllClean, Bool.and_eq_true] at h; exact ExprImp.bin (iha ext h.1) (ihb ext h.2)
  | ifx _ _ _ ihc iha ihb => intro ext h; simp only [callAllClean, Bool.and_eq_true] at h; exact ExprImp.ifx (ihc ext h.1.1) (iha ext h.1.2) (ihb ext h.2)
  | index _ _ iha ihi => intro ext h; simp only [callAllClean, Bool.and_eq_true] at h; exact ExprImp.index (iha ext h.1) (ihi ext h.2)
  | call _ _ iha => intro ext h; simp only [callAllClean] at h; exact ExprImp.call (iha ext h)
  | list _ ihi => intro ext h; simp only [callAllClean] at h; exact ExprImp.list (ihi ext h)
  | letx x _ _ ihr ihb => intro ext h; simp only [callAllClean, Bool.and_eq_true] at h; exact ExprImp.letx (ihr ext h.1) (fun w => ihb ((x, w) :: ext) h.2)
  | each _ x _ _ ihb iha ihhi => intro ext h; simp only [callAllClean, Bool.and_eq_true] at h; exact ExprImp.each (iha ext h.1.1) (ihhi ext h.1.2) (fun i => ihb ((x, .int i) :: ext) h.2)
  | slice _ _ _ iha ihlo ihhi => intro ext h; simp only [callAllClean, Bool.and_eq_true] at h; exact ExprImp.slice (iha ext h.1.1) (ihlo ext h.1.2) (ihhi ext h.2)
  | withx _ _ iha ihp => intro ext h; simp only [callAllClean, Bool.and_eq_true] at h; exact ExprImp.withx (iha ext h.1) (ihp ext h.2)
  | record _ _ ihi => intro ext h; simp only [callAllClean] at h; exact ExprImp.record (ihi ext h)
  | field _ _ ihe => intro ext h; simp only [callAllClean] at h; exact ExprImp.field (ihe ext h)
  | theNumber _ x _ _ _ iha ihb ihc => intro ext h; simp only [callAllClean, Bool.and_eq_true] at h; exact ExprImp.theNumber (iha ext h.1.1) (ihb ext h.1.2) (fun i => ihc ((x, .int i) :: ext) h.2)
  | thePower _ x _ ihc => intro ext h; simp only [callAllClean] at h; exact ExprImp.thePower (fun i => ihc ((x, .int i) :: ext) h)

theorem tailArgExpr_spec {ctx : Ctx} {p q : Program} {s0 st : State} (E : Setting ctx p s0)
    {ρ : Nat → Int} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c) (H : Holds ctx s0 ρ s st) :
    ∀ (args : List (String × Kind)) (regs : List Nat) (x : String) (e' : SExpr),
      (∀ r ∈ regs, r ∈ c.argRegs) →
      callArgExpr.go ctx s c x args regs = some e' →
      ∃ v, (envIn c (afterTail q st) args regs).lookup x = some v ∧
        ((∃ k : Int, e' = .num k ∧ 0 ≤ k ∧ v = .int k) ∨
         (∃ y : String, e' = .name y ∧ (ctx.contract.env s0).lookup y = some v))
  | [], _, _, _, _, h => by simp [callArgExpr.go] at h
  | _, [], _, _, _, h => by simp [callArgExpr.go] at h
  | (n, k) :: args, r :: regs, x, e', hregs, h => by
    have hr_in : r ∈ c.argRegs := hregs r (List.mem_cons_self ..)
    have hregs' : ∀ r' ∈ regs, r' ∈ c.argRegs := fun r' hr' => hregs r' (List.mem_cons_of_mem _ hr')
    cases k with
    | number =>
      simp only [envIn, List.lookup_cons]
      cases hnx : (x == n) with
      | true =>
        simp only [callArgExpr.go, str_beq_comm n x, hnx, ite_true] at h
        cases hc : Lin.isConst (s.reg r) with
        | some kv =>
          simp only [hc] at h
          split at h
          next hk0 =>
            injection h with he'; subst he'
            have hv := H.reg r (T.arg_lt hr_in)
            rw [ev_isConst (ρ := ρ) hc] at hv
            exact ⟨.int (st.reg r), by simp [afterTail], Or.inl ⟨kv, rfl, hk0, by rw [hv]⟩⟩
          next => cases h
        | none =>
          simp only [hc] at h
          obtain ⟨r0, hr0lt, hr0f⟩ := findSome?_range_some h
          split at hr0f
          next heq =>
            have hsr : s.reg r = Lin.var r0 := beq_iff_eq.mp heq
            cases hcn : callerNumName ctx.contract r0 with
            | none => simp [hcn] at hr0f
            | some y =>
              simp only [hcn, Option.map_some, Option.some.injEq] at hr0f; subst hr0f
              obtain ⟨_, hl⟩ := callerNumName_spec [] ctx.contract.args ctx.contract.argRegs y hcn
              have hval := H.reg r (T.arg_lt hr_in)
              rw [hsr, ev_var, H.entry r0 hr0lt] at hval
              have hr_eq : st.reg r = s0.reg r0 := by omega
              exact ⟨.int (st.reg r), by simp [hnx, afterTail], Or.inr ⟨y, rfl, by rw [hr_eq]; exact hl⟩⟩
          next => cases hr0f
      | false =>
        simp only [callArgExpr.go, str_beq_comm n x, hnx, Bool.false_eq_true, ite_false] at h
        exact tailArgExpr_spec E T H args regs x e' hregs' h
    | bytes len =>
      cases hrl : c.regOf len with
      | none =>
        simp only [envIn, hrl]
        simp only [callArgExpr.go] at h
        cases hxn : (n == x) with
        | true => simp [hxn, hrl] at h
        | false => simp only [hxn, Bool.false_eq_true, ite_false] at h; exact tailArgExpr_spec E T H args regs x e' hregs' h
      | some l =>
        simp only [envIn, hrl, List.lookup_cons]
        cases hnx : (x == n) with
        | true =>
          simp only [callArgExpr.go, str_beq_comm n x, hnx, ite_true, hrl] at h
          cases hfind : findRun s r l ctx.contract.regions 0 with
          | none => simp [hfind] at h
          | some j =>
            rw [hfind] at h
            cases hcrn : callerRegionName ctx.contract j with
            | none => simp [hcrn] at h
            | some y =>
              simp only [hcrn, Option.map_some, Option.some.injEq] at h; subst h
              obtain ⟨b0, l0, _, hget, er, el⟩ := findRun_spec hfind
              obtain ⟨_, b0', l0', hget', _, hl⟩ := callerRegionName_spec [] ctx.contract.args ctx.contract.argRegs 0 y hcrn
              have hget0 : ctx.contract.regions[j]? = some (b0', l0') := by simpa [Contract.regions] using hget'
              have heq_bl : (b0, l0) = (b0', l0') := by
                have h1 : ctx.contract.regions[j]? = some (b0, l0) := by simpa using hget
                rw [h1] at hget0; exact Option.some.inj hget0
              injection heq_bl with eb0 el0; subst eb0 el0
              have hm0 : (b0, l0) ∈ ctx.contract.regions := List.mem_of_getElem? hget
              obtain ⟨hb0, hl0⟩ := regions_lt hm0
              have l_in : l ∈ c.argRegs := regOfIn_mem len c.args c.argRegs l hrl
              have vr : st.reg r = s0.reg b0 := by have := H.reg r (T.arg_lt hr_in); rw [er, ev_var, H.entry b0 hb0] at this; omega
              have vl : st.reg l = s0.reg l0 := by have := H.reg l (T.arg_lt l_in); rw [el, ev_var, H.entry l0 hl0] at this; omega
              have hbytes : ((List.range (st.reg l)).map fun t => (st.mem (st.reg r + t)).val) =
                  (List.range (s0.reg l0)).map fun t => (s0.mem (s0.reg b0 + t)).val := by
                rw [vr, vl]; apply List.map_congr_left; intro t ht
                have ht' : t < s0.reg l0 := List.mem_range.mp ht
                have hma := H.mem (s0.reg b0 + t)
                  (by have := (E.regionAt hm0).2; simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
                  (E.region_notOut hm0 (Nat.le_add_right _ _) (by omega))
                rw [hma]
              exact ⟨.bytes ((List.range (st.reg l)).map fun t => (st.mem (st.reg r + t)).val),
                by simp [hnx, afterTail], Or.inr ⟨y, rfl, by rw [hbytes]; exact hl⟩⟩
        | false =>
          simp only [callArgExpr.go, str_beq_comm n x, hnx, Bool.false_eq_true, ite_false] at h
          exact tailArgExpr_spec E T H args regs x e' hregs' h
    | out _ | fixed _ | inout _ | valArray _ _ =>
      simp only [envIn]; simp only [callArgExpr.go] at h
      exact tailArgExpr_spec E T H args regs x e' hregs' h

theorem tailSubst_equiv {ctx : Ctx} {p q : Program} {s0 st : State} (E : Setting ctx p s0)
    {ρ : Nat → Int} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c) (H : Holds ctx s0 ρ s st) :
    ∀ (e : SExpr) (ext : List (String × Val)) {e' : SExpr},
    substCallExpr ctx s c (ext.map Prod.fst) e = some e' →
    ExprImp ctx.defs (ext ++ c.env (afterTail q st)) (ext ++ ctx.contract.env s0) e e' ∧
    ExprImp ctx.defs (ext ++ ctx.contract.env s0) (ext ++ c.env (afterTail q st)) e' e := by
  intro e
  induction e with
  | num n =>
    intro ext e' h; simp only [substCallExpr, Option.some.injEq] at h; subst h
    refine ⟨ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_, ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_⟩
    · cases f with | zero => cases hf | succ f => exact ⟨1, by simpa [evalSpec] using hf⟩
    · cases f with | zero => cases hf | succ f => exact ⟨1, by simpa [evalSpec] using hf⟩
  | nil =>
    intro ext e' h; simp only [substCallExpr, Option.some.injEq] at h; subst h
    refine ⟨⟨fun _ ⟨f, hf⟩ => by cases f <;> simp [evalSpec] at hf, fun _ _ hl => ⟨0, by simpa [evalList] using hl⟩⟩,
            ⟨fun _ ⟨f, hf⟩ => by cases f <;> simp [evalSpec] at hf, fun _ _ hl => ⟨0, by simpa [evalList] using hl⟩⟩⟩
  | cons a1 r1 iha ihr =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, r2, hr, rfl⟩ := h
    exact ⟨ExprImp.cons (iha ext ha).1 (ihr ext hr).1, ExprImp.cons (iha ext ha).2 (ihr ext hr).2⟩
  | name x =>
    intro ext e' h; simp only [substCallExpr] at h
    cases hbd : (ext.map Prod.fst).contains x with
    | true =>
      simp only [hbd, ite_true, Option.some.injEq] at h; subst h
      refine ⟨ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_, ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_⟩
      · cases f with | zero => cases hf | succ f => simp only [evalSpec, lookup_append_mem hbd] at hf; exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
      · cases f with | zero => cases hf | succ f => simp only [evalSpec, lookup_append_mem hbd] at hf; exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
    | false =>
      simp only [hbd, Bool.false_eq_true, ite_false] at h
      cases harg : callArgExpr ctx s c x with
      | none => simp [harg] at h
      | some e0 =>
        rw [harg] at h
        obtain ⟨v0, hv0, ⟨k, rfl, hk, rfl⟩ | ⟨y, rfl, hy⟩⟩ := tailArgExpr_spec (q := q) E T H c.args c.argRegs x e0 (fun _ m => m) harg
        · simp only [Option.some.injEq] at h; subst h
          refine ⟨ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_, ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_⟩
          · cases f with | zero => cases hf | succ f => simp only [evalSpec, lookup_append_not_mem hbd, Contract.env, hv0, Option.some.injEq] at hf; subst hf; exact ⟨1, by simp [evalSpec, hk]⟩
          · cases f with | zero => cases hf | succ f => simp only [evalSpec, hk, ite_true, Option.some.injEq] at hf; subst hf; exact ⟨1, by simp only [evalSpec, lookup_append_not_mem hbd, Contract.env, hv0]⟩
        · simp only at h
          cases hby : (ext.map Prod.fst).contains y with
          | true => simp only [hby, ite_true] at h; cases h
          | false =>
            simp only [hby, Bool.false_eq_true, ite_false, Option.some.injEq] at h; subst h
            refine ⟨ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_, ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_⟩
            · cases f with | zero => cases hf | succ f => simp only [evalSpec, lookup_append_not_mem hbd, Contract.env, hv0, Option.some.injEq] at hf; subst hf; exact ⟨1, by simp only [evalSpec, lookup_append_not_mem hby, hy]⟩
            · cases f with | zero => cases hf | succ f => simp only [evalSpec, lookup_append_not_mem hby, hy, Option.some.injEq] at hf; subst hf; exact ⟨1, by simp only [evalSpec, lookup_append_not_mem hbd, Contract.env, hv0]⟩
  | bin op a1 b1 iha ihb =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, b2, hb, rfl⟩ := h
    exact ⟨ExprImp.bin (iha ext ha).1 (ihb ext hb).1, ExprImp.bin (iha ext ha).2 (ihb ext hb).2⟩
  | ifx c1 a1 b1 ihc iha ihb =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨c2, hc, a2, ha, b2, hb, rfl⟩ := h
    exact ⟨ExprImp.ifx (ihc ext hc).1 (iha ext ha).1 (ihb ext hb).1, ExprImp.ifx (ihc ext hc).2 (iha ext ha).2 (ihb ext hb).2⟩
  | index a1 i1 iha ihi =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, i2, hi, rfl⟩ := h
    exact ⟨ExprImp.index (iha ext ha).1 (ihi ext hi).1, ExprImp.index (iha ext ha).2 (ihi ext hi).2⟩
  | call fn args iha =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, rfl⟩ := h; exact ⟨ExprImp.call (iha ext ha).1, ExprImp.call (iha ext ha).2⟩
  | list items ihi =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨i2, hi, rfl⟩ := h; exact ⟨ExprImp.list (ihi ext hi).1, ExprImp.list (ihi ext hi).2⟩
  | letx x r1 b1 ihr ihb =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨r2, hr, b2, hb, rfl⟩ := h
    exact ⟨ExprImp.letx (ihr ext hr).1 (fun w => (ihb ((x, w) :: ext) hb).1), ExprImp.letx (ihr ext hr).2 (fun w => (ihb ((x, w) :: ext) hb).2)⟩
  | each body x a1 b1 ihb iha ihhi =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨body2, hbd, a2, ha, b2, hb, rfl⟩ := h
    exact ⟨ExprImp.each (iha ext ha).1 (ihhi ext hb).1 (fun i => (ihb ((x, .int i) :: ext) hbd).1),
           ExprImp.each (iha ext ha).2 (ihhi ext hb).2 (fun i => (ihb ((x, .int i) :: ext) hbd).2)⟩
  | slice a1 lo1 hi1 iha ihlo ihhi =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, lo2, hlo, hi2, hhi, rfl⟩ := h
    exact ⟨ExprImp.slice (iha ext ha).1 (ihlo ext hlo).1 (ihhi ext hhi).1, ExprImp.slice (iha ext ha).2 (ihlo ext hlo).2 (ihhi ext hhi).2⟩
  | withx a1 p1 iha ihp =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, p2, hp, rfl⟩ := h
    exact ⟨ExprImp.withx (iha ext ha).1 (ihp ext hp).1, ExprImp.withx (iha ext ha).2 (ihp ext hp).2⟩
  | record ns items ihi =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨i2, hi, rfl⟩ := h; exact ⟨ExprImp.record (ihi ext hi).1, ExprImp.record (ihi ext hi).2⟩
  | field e1 fn ihe =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨e2, he, rfl⟩ := h; exact ⟨ExprImp.field (ihe ext he).1, ExprImp.field (ihe ext he).2⟩
  | theNumber g x a1 b1 cond iha ihb ihc =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, b2, hb, c2, hc, rfl⟩ := h
    exact ⟨ExprImp.theNumber (iha ext ha).1 (ihb ext hb).1 (fun i => (ihc ((x, .int i) :: ext) hc).1),
           ExprImp.theNumber (iha ext ha).2 (ihb ext hb).2 (fun i => (ihc ((x, .int i) :: ext) hc).2)⟩
  | thePower g x cond ihc =>
    intro ext e' h; simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨c2, hc, rfl⟩ := h
    exact ⟨ExprImp.thePower (fun i => (ihc ((x, .int i) :: ext) hc).1), ExprImp.thePower (fun i => (ihc ((x, .int i) :: ext) hc).2)⟩

theorem tailExprClean_same {ctx : Ctx} {p q : Program} {a0 b0 sta stb : State}
    (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0)
    {ρa ρb : Nat → Int} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c)
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb)
    (Ma : MarksOk ctx a0 s.q sta) (Mb : MarksOk ctx b0 s.q stb) (A : Alike sta stb)
    {e : SExpr} (he : callExprClean ctx s c e = true) (v : Val) :
    Value ctx.defs (c.env (afterTail q sta)) e v ↔ Value ctx.defs (c.env (afterTail q stb)) e v := by
  simp only [callExprClean, Bool.or_eq_true] at he
  rcases he with hall | hsub
  · have As : Alike stb sta := ⟨A.marks.symm, A.rip.symm, A.data.symm, A.trace.symm,
      fun r hr => (A.reg r (A.marks ▸ hr)).symm, fun h => (A.zf (A.marks ▸ h)).symm,
      fun h => (A.cf (A.marks ▸ h)).symm, fun a ha => (A.mem a (A.marks ▸ ha)).symm,
      fun r hr => (A.low r (A.marks ▸ hr)).symm⟩
    exact ⟨(tailAllClean_imp Ea Eb ta T Ha Hb Ma A e [] hall).1 v,
           (tailAllClean_imp Eb Ea (traceAgree_symm ta) T Hb Ha Mb As e [] hall).1 v⟩
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hsub
    obtain ⟨_, hsub⟩ := hsub
    cases hs : substCallExpr ctx s c [] e with
    | none => rw [hs] at hsub; cases hsub
    | some e' =>
      rw [hs] at hsub
      obtain ⟨ea1, ea2⟩ := tailSubst_equiv Ea T Ha e [] hs
      obtain ⟨eb1, eb2⟩ := tailSubst_equiv Eb T Hb e [] hs
      have hsame := traceClean_same ta hsub v
      exact ⟨fun h => eb2.1 v (hsame.mp (ea1.1 v h)), fun h => ea2.1 v (hsame.mpr (eb1.1 v h))⟩

theorem tailQuiet_traceAgree {ctx : Ctx} {p q : Program} {a0 b0 sta stb : State}
    (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0)
    {ρa ρb : Nat → Int} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c)
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb)
    (Ma : MarksOk ctx a0 s.q sta) (Mb : MarksOk ctx b0 s.q stb) (A : Alike sta stb)
    (hq : callQuiet ctx s c = true) :
    c.traceAgree ctx.defs (afterTail q sta) (afterTail q stb) := by
  simp only [callQuiet, Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨hregs, hfix⟩, _⟩, hrun⟩, htexpr⟩ := hq
  have regs : ∀ r ∈ c.cleanAtEntry, sta.marks.reg r = false := fun r hr =>
    Ma.reg r (List.contains_iff_mem.mp (List.all_eq_true.mp hregs r hr))
  have At : Alike (afterTail q sta) (afterTail q stb) := afterTail_alike A
  refine ⟨rfl, At.data, At.trace, At.reg RSP (regs RSP (List.mem_cons_self ..)), ?_,
    fun r hr => At.reg r (regs r hr), fun r l hm hnh => ?_, fun x r n hm hnh k hk => ?_,
    fun e he v => tailExprClean_same Ea Eb ta T Ha Hb Ma Mb A (List.all_eq_true.mp htexpr e he) v⟩
  · -- `c.backTo (afterTail q sta) = c.backTo (afterTail q stb)`
    rw [T.backTo_eq Ea Ha q, T.backTo_eq Eb Hb q]
    exact ta.2.2.2.2.1
  · -- clean region bytes agree
    have hfound := List.all_eq_true.mp hrun (r, l) hm
    simp only [hnh, Bool.false_or, Bool.and_eq_true] at hfound
    have hfound := hfound.2
    cases hf : findRun s r l ctx.contract.regions 0 with
    | none => simp [hf] at hfound
    | some j =>
      obtain ⟨b0', l0', _, hget, er, el⟩ := findRun_spec hf
      have hnh0 : ctx.contract.hiddenAt b0' = false := by
        rw [hf] at hfound; have hget' : ctx.contract.regions[j]? = some (b0', l0') := by simpa using hget
        simp only [hget', Bool.not_eq_true'] at hfound; exact hfound
      have hm0 : (b0', l0') ∈ ctx.contract.regions := List.mem_of_getElem? hget
      obtain ⟨hb0', hl0'⟩ := regions_lt hm0
      obtain ⟨ra, len, hlen⟩ := regionsIn_mem c c.args c.argRegs r l hm
      have la := regOfIn_mem len c.args c.argRegs l hlen
      have vra : sta.reg r = a0.reg b0' := by have := Ha.reg r (T.arg_lt ra); rw [er, ev_var, Ha.entry b0' hb0'] at this; omega
      have vla : sta.reg l = a0.reg l0' := by have := Ha.reg l (T.arg_lt la); rw [el, ev_var, Ha.entry l0' hl0'] at this; omega
      have vrb : stb.reg r = b0.reg b0' := by have := Hb.reg r (T.arg_lt ra); rw [er, ev_var, Hb.entry b0' hb0'] at this; omega
      have vlb : stb.reg l = b0.reg l0' := by have := Hb.reg l (T.arg_lt la); rw [el, ev_var, Hb.entry l0' hl0'] at this; omega
      have ⟨hlen_eq, htb_bytes⟩ := ta.2.2.2.2.2.2.1 b0' l0' hm0 hnh0
      refine ⟨by show sta.reg l = stb.reg l; omega, fun k hk => ?_⟩
      show sta.mem (sta.reg r + k) = stb.mem (stb.reg r + k)
      have hka : k < a0.reg l0' := by simp only [afterTail] at hk; omega
      have hkb : k < b0.reg l0' := by omega
      have hma := Ha.mem (a0.reg b0' + k)
        (by have := (Ea.regionAt hm0).2; simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
        (Ea.region_notOut hm0 (Nat.le_add_right _ _) (by omega))
      have hmb := Hb.mem (b0.reg b0' + k)
        (by have := (Eb.regionAt hm0).2; simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
        (Eb.region_notOut hm0 (Nat.le_add_right _ _) (by omega))
      rw [vra, vrb, hma, hmb]
      exact htb_bytes k hka
  · -- clean fixed-run bytes agree (at a tail call, `noFrameFix` forces every fixed run of `c` to be in `c.hidden`)
    have hff := List.all_eq_true.mp hfix (x, r, n) hm
    simp only [T.noFrameFix (x, r, n) hm, Bool.or_false, List.contains_iff_mem] at hff
    exact absurd hff hnh

/-- Single-run-marks version of `tailArgClean_agree` (for functions with `hasSelect = true`). -/
theorem tailArgClean_alike {ctx : Ctx} {p q : Program} {a0 sta stb : State}
    (Ea : Setting ctx p a0) (hq0 : ctx.contract.quietAt a0)
    {ρa : Nat → Int} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c)
    (Ha : Holds ctx a0 ρa s sta) (Ma : MarksOk ctx a0 s.q sta) (A : Alike sta stb)
    (hclean : c.cleanAtEntry.all s.q.regq.contains = true) :
    ∀ (args : List (String × Kind)) (regs : List Nat) (x : String),
    (∀ r ∈ regs, r ∈ c.argRegs) →
    (∀ r ∈ cleanIn c args regs, r ∈ c.cleanAtEntry) →
    callArgClean.go ctx s c x args regs = true →
    (envIn c (afterTail q sta) args regs).lookup x = (envIn c (afterTail q stb) args regs).lookup x
  | [], _, _, _, _, h => by simp [callArgClean.go] at h
  | _ :: _, [], _, _, _, h => by simp [callArgClean.go] at h
  | (n, k) :: args, r :: regs, x, hregs, hcin, h => by
    have hr_in : r ∈ c.argRegs := hregs r (List.mem_cons_self ..)
    have hregs' : ∀ r' ∈ regs, r' ∈ c.argRegs := fun r' hm => hregs r' (List.mem_cons_of_mem _ hm)
    have hcin' : ∀ r' ∈ cleanIn c args regs, r' ∈ c.cleanAtEntry := fun r' hm =>
      hcin r' (by simp only [cleanIn, List.mem_append]; exact Or.inr hm)
    cases k with
    | number =>
      simp only [envIn, List.lookup_cons]
      cases hxn : (x == n) with
      | true =>
        simp only [callArgClean.go, str_beq_comm n x, hxn, ite_true] at h
        have hmk : sta.marks.reg r = false := Ma.reg r (List.contains_iff_mem.mp h)
        simp only [hxn, afterTail]
        rw [A.reg r hmk]
      | false =>
        simp only [callArgClean.go, str_beq_comm n x, hxn, Bool.false_eq_true, ite_false] at h
        exact tailArgClean_alike Ea hq0 T Ha Ma A hclean args regs x hregs' hcin' h
    | bytes len =>
      cases hl : c.regOf len with
      | none =>
        simp only [envIn, hl]
        simp only [callArgClean.go] at h
        cases hnx : (n == x) with
        | true => simp [hnx, hl] at h
        | false =>
          simp only [hnx, Bool.false_eq_true, ite_false] at h
          exact tailArgClean_alike Ea hq0 T Ha Ma A hclean args regs x hregs' hcin' h
      | some l =>
        simp only [envIn, hl, List.lookup_cons]
        cases hxn : (x == n) with
        | true =>
          simp only [callArgClean.go, str_beq_comm n x, hxn, ite_true, hl, Bool.and_eq_true] at h
          obtain ⟨hlq, hfind⟩ := h
          have hr_clean : r ∈ c.cleanAtEntry :=
            hcin r (by simp [cleanIn])
          have hrmk : sta.marks.reg r = false :=
            Ma.reg r (List.contains_iff_mem.mp (List.all_eq_true.mp hclean r hr_clean))
          have hlmk : sta.marks.reg l = false := Ma.reg l (List.contains_iff_mem.mp hlq)
          have hreq : sta.reg r = stb.reg r := A.reg r hrmk
          have hleq : sta.reg l = stb.reg l := A.reg l hlmk
          cases hf : findRun s r l ctx.contract.regions 0 with
          | none => simp [hf] at hfind
          | some j =>
            obtain ⟨b0r, l0r, _, hget, er, el⟩ := findRun_spec hf
            have hnh0 : ctx.contract.hiddenAt b0r = false := by
              rw [hf] at hfind; simp only at hfind
              have hget' : ctx.contract.regions[j]? = some (b0r, l0r) := by simpa using hget
              rw [hget'] at hfind; simpa using hfind
            have hmem : (b0r, l0r) ∈ ctx.contract.regions := List.mem_of_getElem? hget
            obtain ⟨hb0, hl0⟩ := regions_lt hmem
            have hl_in : l ∈ c.argRegs := regOfIn_mem len c.args c.argRegs l hl
            have vra : sta.reg r = a0.reg b0r := by have := Ha.reg r (T.arg_lt hr_in); rw [er, ev_var, Ha.entry b0r hb0] at this; omega
            have vla : sta.reg l = a0.reg l0r := by have := Ha.reg l (T.arg_lt hl_in); rw [el, ev_var, Ha.entry l0r hl0] at this; omega
            simp only [hxn, afterTail]
            congr 2
            rw [hleq]
            apply List.map_congr_left
            intro k hk
            have hk' : k < a0.reg l0r := by rw [← vla, hleq]; exact List.mem_range.mp hk
            obtain ⟨_, r2⟩ := Ea.regionAt hmem
            have hnf : ctx.contract.inFrame a0 (a0.reg b0r + k) = false := notFrame (by omega)
            have hno : ctx.contract.inOut a0 (a0.reg b0r + k) = false := Ea.region_notOut hmem (by omega) (by omega)
            have hmk_mem : sta.marks.mem (a0.reg b0r + k) = false := by
              rw [Ma.stable _ hnf hno]; exact hq0.2.2.1 b0r l0r hmem hnh0 k hk'
            rw [← hreq, vra, A.mem _ hmk_mem]
        | false =>
          simp only [callArgClean.go, str_beq_comm n x, hxn, Bool.false_eq_true, ite_false] at h
          exact tailArgClean_alike Ea hq0 T Ha Ma A hclean args regs x hregs' hcin' h
    | out _ | fixed _ | inout _ | valArray _ _ =>
      simp only [envIn]
      simp only [callArgClean.go] at h
      exact tailArgClean_alike Ea hq0 T Ha Ma A hclean args regs x hregs' hcin' h

theorem tailAllClean_alike {ctx : Ctx} {p q : Program} {a0 sta stb : State}
    (Ea : Setting ctx p a0) (hq0 : ctx.contract.quietAt a0)
    {ρa : Nat → Int} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c)
    (Ha : Holds ctx a0 ρa s sta) (Ma : MarksOk ctx a0 s.q sta) (A : Alike sta stb)
    (hclean : c.cleanAtEntry.all s.q.regq.contains = true) :
    ∀ (e : SExpr) (ext : List (String × Val)),
    callAllClean ctx s c (ext.map Prod.fst) e = true →
    ExprImp ctx.defs (ext ++ c.env (afterTail q sta)) (ext ++ c.env (afterTail q stb)) e e := by
  have arg_eq : ∀ x, callArgClean ctx s c x = true →
      (c.env (afterTail q sta)).lookup x = (c.env (afterTail q stb)).lookup x := fun x hx =>
    tailArgClean_alike Ea hq0 T Ha Ma A hclean c.args c.argRegs x (fun _ hm => hm)
      (fun r hr => List.mem_cons_of_mem _ hr) hx
  intro e
  induction e with
  | num _ =>
    intro ext _
    exact ExprImp.of_val rfl fun v ⟨f, hf⟩ => by cases f with | zero => cases hf | succ f => exact ⟨1, by simpa [evalSpec] using hf⟩
  | nil =>
    intro ext _
    exact ⟨fun _ ⟨f, hf⟩ => by cases f <;> simp [evalSpec] at hf,
      fun _ _ hl => by simp only [evalList, Option.some.injEq] at hl; subst hl; exact ⟨0, rfl⟩⟩
  | cons a1 r1 iha ihr =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.cons (iha ext h.1) (ihr ext h.2)
  | name x =>
    intro ext h
    simp only [callAllClean, Bool.or_eq_true] at h
    exact ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
      cases f with
      | zero => cases hf
      | succ f =>
        simp only [evalSpec] at hf
        rcases h with hbd | hcl
        · rw [lookup_append_mem hbd] at hf
          exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
        · cases hbd : (ext.map Prod.fst).contains x with
          | true =>
            rw [lookup_append_mem hbd] at hf
            exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
          | false =>
            rw [lookup_append_not_mem hbd] at hf
            rw [arg_eq x hcl] at hf
            exact ⟨1, by simp only [evalSpec, lookup_append_not_mem hbd]; exact hf⟩
  | bin op a1 b1 iha ihb =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.bin (iha ext h.1) (ihb ext h.2)
  | ifx cond a1 b1 ihc iha ihb =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.ifx (ihc ext h.1.1) (iha ext h.1.2) (ihb ext h.2)
  | index a1 i1 iha ihi =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.index (iha ext h.1) (ihi ext h.2)
  | call fn args iha =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.call (iha ext h)
  | list items ihi =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.list (ihi ext h)
  | letx x r1 b1 ihr ihb =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.letx (ihr ext h.1) (fun w => ihb ((x, w) :: ext) h.2)
  | each body x a1 b1 ihb iha ihhi =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.each (iha ext h.1.1) (ihhi ext h.1.2) (fun i => ihb ((x, .int i) :: ext) h.2)
  | slice a1 lo1 hi1 iha ihlo ihhi =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.slice (iha ext h.1.1) (ihlo ext h.1.2) (ihhi ext h.2)
  | withx a1 p1 iha ihp =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.withx (iha ext h.1) (ihp ext h.2)
  | record ns items ihi =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.record (ihi ext h)
  | field e1 fn ihe =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.field (ihe ext h)
  | theNumber g x a1 b1 cond iha ihb ihc =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.theNumber (iha ext h.1.1) (ihb ext h.1.2) (fun i => ihc ((x, .int i) :: ext) h.2)
  | thePower g x cond ihc =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.thePower (fun i => ihc ((x, .int i) :: ext) h)

theorem tailAllClean_alike_symm {ctx : Ctx} {p q : Program} {a0 sta stb : State}
    (Ea : Setting ctx p a0) (hq0 : ctx.contract.quietAt a0)
    {ρa : Nat → Int} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c)
    (Ha : Holds ctx a0 ρa s sta) (Ma : MarksOk ctx a0 s.q sta) (A : Alike sta stb)
    (hclean : c.cleanAtEntry.all s.q.regq.contains = true) :
    ∀ (e : SExpr) (ext : List (String × Val)),
    callAllClean ctx s c (ext.map Prod.fst) e = true →
    ExprImp ctx.defs (ext ++ c.env (afterTail q stb)) (ext ++ c.env (afterTail q sta)) e e := by
  have arg_eq : ∀ x, callArgClean ctx s c x = true →
      (c.env (afterTail q stb)).lookup x = (c.env (afterTail q sta)).lookup x := fun x hx =>
    (tailArgClean_alike Ea hq0 T Ha Ma A hclean c.args c.argRegs x (fun _ hm => hm)
      (fun r hr => List.mem_cons_of_mem _ hr) hx).symm
  intro e
  induction e with
  | num _ =>
    intro ext _
    exact ExprImp.of_val rfl fun v ⟨f, hf⟩ => by cases f with | zero => cases hf | succ f => exact ⟨1, by simpa [evalSpec] using hf⟩
  | nil =>
    intro ext _
    exact ⟨fun _ ⟨f, hf⟩ => by cases f <;> simp [evalSpec] at hf,
      fun _ _ hl => by simp only [evalList, Option.some.injEq] at hl; subst hl; exact ⟨0, rfl⟩⟩
  | cons a1 r1 iha ihr =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.cons (iha ext h.1) (ihr ext h.2)
  | name x =>
    intro ext h
    simp only [callAllClean, Bool.or_eq_true] at h
    exact ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
      cases f with
      | zero => cases hf
      | succ f =>
        simp only [evalSpec] at hf
        rcases h with hbd | hcl
        · rw [lookup_append_mem hbd] at hf
          exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
        · cases hbd : (ext.map Prod.fst).contains x with
          | true =>
            rw [lookup_append_mem hbd] at hf
            exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
          | false =>
            rw [lookup_append_not_mem hbd] at hf
            rw [arg_eq x hcl] at hf
            exact ⟨1, by simp only [evalSpec, lookup_append_not_mem hbd]; exact hf⟩
  | bin op a1 b1 iha ihb =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.bin (iha ext h.1) (ihb ext h.2)
  | ifx cond a1 b1 ihc iha ihb =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.ifx (ihc ext h.1.1) (iha ext h.1.2) (ihb ext h.2)
  | index a1 i1 iha ihi =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.index (iha ext h.1) (ihi ext h.2)
  | call fn args iha =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.call (iha ext h)
  | list items ihi =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.list (ihi ext h)
  | letx x r1 b1 ihr ihb =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.letx (ihr ext h.1) (fun w => ihb ((x, w) :: ext) h.2)
  | each body x a1 b1 ihb iha ihhi =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.each (iha ext h.1.1) (ihhi ext h.1.2) (fun i => ihb ((x, .int i) :: ext) h.2)
  | slice a1 lo1 hi1 iha ihlo ihhi =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.slice (iha ext h.1.1) (ihlo ext h.1.2) (ihhi ext h.2)
  | withx a1 p1 iha ihp =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.withx (iha ext h.1) (ihp ext h.2)
  | record ns items ihi =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.record (ihi ext h)
  | field e1 fn ihe =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.field (ihe ext h)
  | theNumber g x a1 b1 cond iha ihb ihc =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.theNumber (iha ext h.1.1) (ihb ext h.1.2) (fun i => ihc ((x, .int i) :: ext) h.2)
  | thePower g x cond ihc =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.thePower (fun i => ihc ((x, .int i) :: ext) h)

theorem tailExprClean_alike {ctx : Ctx} {p q : Program} {a0 sta stb : State}
    (Ea : Setting ctx p a0) (hq0 : ctx.contract.quietAt a0) (hsel : hasSelect ctx.code = true)
    {ρa : Nat → Int} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c)
    (Ha : Holds ctx a0 ρa s sta) (Ma : MarksOk ctx a0 s.q sta) (A : Alike sta stb)
    (hclean : c.cleanAtEntry.all s.q.regq.contains = true)
    {e : SExpr} (he : callExprClean ctx s c e = true) (v : Val) :
    Value ctx.defs (c.env (afterTail q sta)) e v ↔ Value ctx.defs (c.env (afterTail q stb)) e v := by
  simp only [callExprClean, hsel, Bool.not_true, Bool.false_and, Bool.or_false] at he
  exact ⟨(tailAllClean_alike Ea hq0 T Ha Ma A hclean e [] he).1 v,
         (tailAllClean_alike_symm Ea hq0 T Ha Ma A hclean e [] he).1 v⟩

/-- Single-run-marks version of `tailQuiet_traceAgree` (for functions with `hasSelect = true`). -/
theorem tailQuiet_traceAgree_alike {ctx : Ctx} {p q : Program} {a0 sta stb : State}
    (Ea : Setting ctx p a0) (hq0 : ctx.contract.quietAt a0) (hsel : hasSelect ctx.code = true)
    {ρa : Nat → Int} {s : Sym} {name : String} {c : Contract} (T : TailOk ctx s name c)
    (Ha : Holds ctx a0 ρa s sta) (Ma : MarksOk ctx a0 s.q sta) (A : Alike sta stb)
    (hq : callQuiet ctx s c = true) :
    c.traceAgree ctx.defs (afterTail q sta) (afterTail q stb) := by
  simp only [callQuiet, Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨hregs, hfix⟩, _⟩, hrun⟩, htexpr⟩ := hq
  have regs : ∀ r ∈ c.cleanAtEntry, sta.marks.reg r = false := fun r hr =>
    Ma.reg r (List.contains_iff_mem.mp (List.all_eq_true.mp hregs r hr))
  have At : Alike (afterTail q sta) (afterTail q stb) := afterTail_alike A
  refine ⟨rfl, At.data, At.trace, At.reg RSP (regs RSP (List.mem_cons_self ..)), ?_,
    fun r hr => At.reg r (regs r hr), fun r l hm hnh => ?_, fun x r n hm hnh k hk => ?_,
    fun e he v => tailExprClean_alike Ea hq0 hsel T Ha Ma A hregs (List.all_eq_true.mp htexpr e he) v⟩
  · -- `c.backTo (afterTail q sta) = c.backTo (afterTail q stb)`
    unfold Contract.backTo
    rw [T.machine]
    cases ha : ctx.contract.arm64 with
    | true =>
      simp only [afterTail, ite_true]
      exact A.reg LINK (Ma.reg LINK (T.linkOk ha).2)
    | false =>
      simp only [afterTail, Bool.false_eq_true, ite_false]
      have hrsp_eq : sta.reg RSP = stb.reg RSP := A.reg RSP (Ma.reg RSP T.rspClean)
      rw [hrsp_eq]
      apply load_same
      intro a ha1 ha2
      have hslot : ctx.contract.slot = 8 := by unfold Contract.slot; rw [ha]; rfl
      have hrsp_a0 : sta.reg RSP = a0.reg RSP := T.rsp_eq Ha
      have ha1' : a0.reg RSP ≤ a := by omega
      have ha2' : a < a0.reg RSP + 8 := by omega
      have hnf : ctx.contract.inFrame a0 a = false := by
        simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      have hno : ctx.contract.inOut a0 a = false := by
        unfold Contract.inOut
        rw [List.any_eq_false]
        intro ⟨x, r, n⟩ hm
        have hdis := (Ea.outAt hm).2
        rw [hslot] at hdis
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      have hbq := hq0.2.1
      unfold Contract.backQuiet at hbq
      simp only [ha, Bool.false_eq_true, ite_false] at hbq
      have hmk_a0 : a0.marks.mem a = false := by
        have hk := hbq (a - a0.reg RSP) (by omega)
        have heq : a0.reg RSP + (a - a0.reg RSP) = a := by omega
        rwa [heq] at hk
      exact A.mem a (by rw [Ma.stable a hnf hno, hmk_a0])
  · -- clean region bytes agree
    have hfound := List.all_eq_true.mp hrun (r, l) hm
    simp only [hnh, Bool.false_or, Bool.and_eq_true] at hfound
    have hlq : sta.marks.reg l = false := Ma.reg l (List.contains_iff_mem.mp hfound.1)
    have hfound := hfound.2
    cases hf : findRun s r l ctx.contract.regions 0 with
    | none => simp [hf] at hfound
    | some j =>
      obtain ⟨b0', l0', _, hget, er, el⟩ := findRun_spec hf
      have hnh0 : ctx.contract.hiddenAt b0' = false := by
        rw [hf] at hfound; have hget' : ctx.contract.regions[j]? = some (b0', l0') := by simpa using hget
        simp only [hget', Bool.not_eq_true'] at hfound; exact hfound
      have hm0 : (b0', l0') ∈ ctx.contract.regions := List.mem_of_getElem? hget
      obtain ⟨hb0', hl0'⟩ := regions_lt hm0
      obtain ⟨ra, len, hlen⟩ := regionsIn_mem c c.args c.argRegs r l hm
      have la := regOfIn_mem len c.args c.argRegs l hlen
      have hr_clean : r ∈ c.cleanAtEntry := List.mem_cons_of_mem _ (by
        suffices ∀ args regs, (r, l) ∈ regionsIn c args regs → r ∈ cleanIn c args regs from this c.args c.argRegs hm
        intro args; induction args with
        | nil => intro regs h; simp [regionsIn] at h
        | cons ak more ih =>
          intro regs h; cases regs with | nil => simp [regionsIn] at h | cons r0 rs =>
          obtain ⟨nm, kd⟩ := ak; cases kd with
          | bytes ln =>
            simp only [regionsIn] at h; cases hrl : c.regOf ln with
            | none => rw [hrl] at h; exact List.mem_append_right _ (ih rs h)
            | some l0 =>
              rw [hrl] at h; rcases List.mem_cons.mp h with he | ht
              · injection he with er _; subst er; exact List.mem_append_left _ (List.mem_cons_self ..)
              · exact List.mem_append_right _ (ih rs ht)
          | number | out _ | fixed _ | inout _ | valArray _ _ => simp only [regionsIn] at h; exact List.mem_append_right _ (ih rs h))
      have hreq : sta.reg r = stb.reg r := A.reg r (regs r hr_clean)
      have hleq : sta.reg l = stb.reg l := A.reg l hlq
      have vra : sta.reg r = a0.reg b0' := by have := Ha.reg r (T.arg_lt ra); rw [er, ev_var, Ha.entry b0' hb0'] at this; omega
      have vla : sta.reg l = a0.reg l0' := by have := Ha.reg l (T.arg_lt la); rw [el, ev_var, Ha.entry l0' hl0'] at this; omega
      refine ⟨hleq, fun k hk => ?_⟩
      show sta.mem (sta.reg r + k) = stb.mem (stb.reg r + k)
      have hka : k < a0.reg l0' := by simp only [afterTail] at hk; omega
      have hnf : ctx.contract.inFrame a0 (a0.reg b0' + k) = false := by
        have := (Ea.regionAt hm0).2; simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      have hno : ctx.contract.inOut a0 (a0.reg b0' + k) = false :=
        Ea.region_notOut hm0 (Nat.le_add_right _ _) (by omega)
      have hmk_mem : sta.marks.mem (a0.reg b0' + k) = false := by
        rw [Ma.stable _ hnf hno]; exact hq0.2.2.1 b0' l0' hm0 hnh0 k hka
      rw [← hreq, vra]
      exact A.mem _ hmk_mem
  · -- clean fixed-run bytes agree
    have hff := List.all_eq_true.mp hfix (x, r, n) hm
    simp only [T.noFrameFix (x, r, n) hm, Bool.or_false, List.contains_iff_mem] at hff
    exact absurd hff hnh

end Ode
