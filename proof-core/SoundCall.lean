import SoundPlace
/-!
# Why the verifier's yes is right, 7: a call, by the called function's contract

At a call the verifier shows what the called function's contract asks of its caller, and goes on from what
the contract leaves. Here: that the machine's call then goes as `Runs` says a call goes, given that the
called function meets that contract (`CalleesMeet`).
-/
namespace Ode
open Arithmetic

theorem Holds.more {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (rows : List Row) (hr : ∀ r ∈ rows, r.holds ρ) : Holds ctx s0 ρ { s with facts := rows ++ s.facts } st :=
  ⟨H.entry, H.data, H.reg, H.small, H.zf, H.cf, H.frame, H.frameW,
   fun f m => (List.mem_append.mp m).elim (hr f) (H.facts f), H.bytes, H.spec, H.mem, H.wrote, H.words, H.known, H.range, H.vecIntact⟩

theorem WF.more {ctx : Ctx} {s : Sym} (wf : WF ctx s) (rows : List Row) (hb : ∀ r ∈ rows, bounded s.nvars r) : WF ctx { s with facts := rows ++ s.facts } :=
  ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, wf.frameW, fun f m => (List.mem_append.mp m).elim (hb f) (wf.facts f), wf.bytes, wf.spec, wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, wf.range⟩

/-- The function meets its contract for all entry states whose recursion measure (when `bound = some (r, m)`)
is strictly below `m`. When `bound = none`, this is equivalent to `Meets`. -/
def MeetsBelow (world : List Program) (pieces : List Piece) (c : Contract) (defs : List Def) (p : Program)
    (bound : Option (Nat × Nat)) : Prop :=
  ∀ s, (∀ r m, bound = some (r, m) → s.reg r < m) →
    Loaded pieces s → c.clear world pieces s → c.pre p s → RunsPlain world (c.perm pieces s) p (c.post defs s) s

theorem Meets.below {world : List Program} {pieces : List Piece} {c : Contract} {defs : List Def} {p : Program}
    (M : Meets world pieces c defs p) (bound : Option (Nat × Nat)) : MeetsBelow world pieces c defs p bound :=
  fun s _ hl hc hp => M s hl hc hp

/-- When `name` is this function itself (`ctx.selfName = some name`), the strict upper bound on its
`decreases` register at entry `s0`. For any non-self callee, `none`. -/
def Ctx.recBound (ctx : Ctx) (name : String) (c : Contract) (s0 : State) : Option (Nat × Nat) :=
  if ctx.selfName == some name then
    c.decreases.bind fun d => (c.regOf d).map fun r => (r, s0.reg r)
  else none

/-- Every function this one calls is among the functions there are, lies in memory, and meets the contract
its call is taken by (for a direct recursive self-call, on all strictly smaller values of `decreases`). -/
def CalleesMeet (world : List Program) (ctx : Ctx) : Prop :=
  ∀ name c, ctx.callees.lookup name = some c →
    ∃ q, findProgram world name = some q ∧ q.fits ∧ Meets world ctx.pieces c ctx.defs q

/-- Every function this one calls is among the functions there are, lies in memory, and meets the contract
its call is taken by (for a direct recursive self-call, on all strictly smaller values of `decreases`). -/
def CalleesMeetAt (world : List Program) (ctx : Ctx) (s0 : State) : Prop :=
  ∀ name c, ctx.callees.lookup name = some c →
    ∃ q, findProgram world name = some q ∧ q.fits ∧ MeetsBelow world ctx.pieces c ctx.defs q (ctx.recBound name c s0)

/-- Callee entry preconditions checked uniformly by `callPreOk`: stack fit, `atLeast`, and `preLines`. -/
structure CallExtra (ctx : Ctx) (s0 st : State) (c : Contract) (st1 : State) : Prop where
  stack : (st.reg RSP : Int) ≤ s0.reg RSP ∧ -(ctx.contract.stackAt s0 : Int) ≤ (st.reg RSP : Int) - s0.reg RSP - c.slot - (c.stackAt st1 : Int)
  mbounds : ∀ x off b, (x, off, b) ∈ c.mbounds → ∀ r n, (x, r, n) ∈ c.fixeds → load st1.mem (st1.reg r + off) 8 < b
  atLeast : ∀ x k, (x, k) ∈ c.atLeast → ∀ r, c.regOf x = some r → k ≤ st1.reg r
  preLines : ∀ k ts, (k, ts) ∈ c.preLines → 0 ≤ preLineVal c st1 k ts

theorem bitsNat_le_of_lt_pow {n d : Nat} (h : n < 2 ^ d) : bitsNat n ≤ d := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ m =>
    have hlog : Nat.log2 (m + 1) < d := (Nat.log2_lt (Nat.succ_ne_zero m)).mpr h
    simp only [bitsNat]; omega

theorem le_bitsNat_of_pow_le {n d : Nat} (h : 2 ^ d ≤ n) : d + 1 ≤ bitsNat n := by
  cases n with
  | zero =>
    have hp : 0 < 2 ^ d := Nat.two_pow_pos d
    omega
  | succ m =>
    have hlog : d ≤ Nat.log2 (m + 1) := (Nat.le_log2 (Nat.succ_ne_zero m)).mpr h
    simp only [bitsNat]; omega

theorem bitsNat_mono {a b : Nat} (h : a ≤ b) : bitsNat a ≤ bitsNat b := by
  cases a with
  | zero => exact Nat.zero_le _
  | succ m =>
    cases b with
    | zero => omega
    | succ k =>
      simp only [bitsNat]
      have hpow : 2 ^ Nat.log2 (m + 1) ≤ m + 1 := Nat.log2_self_le (Nat.succ_ne_zero m)
      exact Nat.add_le_add_right ((Nat.le_log2 (Nat.succ_ne_zero k)).mpr (Nat.le_trans hpow h)) 1

theorem bitsNat_succ_le_of_double {a b : Nat} (hb : 0 < b) (h : 2 * a ≤ b) : bitsNat a + 1 ≤ bitsNat b := by
  cases a with
  | zero =>
    exact le_bitsNat_of_pow_le (n := b) (d := 0) (by simp only [Nat.pow_zero]; omega)
  | succ m =>
    have hpow : 2 ^ Nat.log2 (m + 1) ≤ m + 1 := Nat.log2_self_le (Nat.succ_ne_zero m)
    have hpow2 : 2 ^ (Nat.log2 (m + 1) + 1) ≤ b := by rw [Nat.pow_succ]; omega
    have hle := le_bitsNat_of_pow_le hpow2
    show (Nat.log2 (m + 1) + 1) + 1 ≤ bitsNat b
    omega

theorem div_lt_of_sub_lt {a sub div k : Nat} (hdiv : 0 < div) (hk : 0 < k) (h : a < sub + div * k) : (a - sub) / div < k := by
  have hpos : 0 < div * k := Nat.mul_pos hdiv hk
  rw [Nat.div_lt_iff_lt_mul hdiv, Nat.mul_comm]
  omega

theorem le_div_of_le_sub {a sub div k : Nat} (hdiv : 0 < div) (h : sub + div * k ≤ a) : k ≤ (a - sub) / div := by
  rw [Nat.le_div_iff_mul_le hdiv, Nat.mul_comm]
  omega

theorem ev_preLineRow_go (c : Contract) (val : Nat → Row) (ρ : Nat → Int) :
    ∀ (ts : List (String × Int)) (init : Row),
      ev ρ (ts.foldl (fun acc (x, a) => match c.regOf x with | some r => Lin.add acc (Lin.scale a (val r)) | none => acc) init) =
      ev ρ init + ts.foldl (fun acc (x, a) => match c.regOf x with | some r => acc + a * ev ρ (val r) | none => acc) 0
  | [], init => by simp
  | (x, a) :: rest, init => by
    simp only [List.foldl_cons]
    cases hr : c.regOf x with
    | none =>
      simp only [hr]
      exact ev_preLineRow_go c val ρ rest init
    | some r =>
      simp only [hr]
      rw [ev_preLineRow_go c val ρ rest (Lin.add init (Lin.scale a (val r)))]
      have hfold : ∀ (l : List (String × Int)) (z1 z2 : Int),
          l.foldl (fun acc (x, a) => match c.regOf x with | some r => acc + a * ev ρ (val r) | none => acc) (z1 + z2) =
          z1 + l.foldl (fun acc (x, a) => match c.regOf x with | some r => acc + a * ev ρ (val r) | none => acc) z2 := by
        intro l; induction l with
        | nil => intro z1 z2; simp
        | cons p ps ih =>
          intro z1 z2; simp only [List.foldl_cons]
          cases hr' : c.regOf p.1 with
          | none => simp only [hr']; exact ih z1 z2
          | some r' =>
            simp only [hr']
            have : z1 + z2 + p.2 * ev ρ (val r') = z1 + (z2 + p.2 * ev ρ (val r')) := by omega
            rw [this]; exact ih z1 _
      have := hfold rest (a * ev ρ (val r)) 0
      simp only [Int.add_zero, Int.zero_add] at this ⊢
      rw [this, ev_add, ev_scale]; omega

theorem ev_preLineRow (c : Contract) (val : Nat → Row) (ρ : Nat → Int) (k : Int) (ts : List (String × Int)) :
    ev ρ (preLineRow c val k ts) =
    k + ts.foldl (fun acc (x, a) => match c.regOf x with | some r => acc + a * ev ρ (val r) | none => acc) 0 := by
  unfold preLineRow
  have h := ev_preLineRow_go c val ρ ts (Lin.const k)
  rw [ev_const] at h
  exact h

theorem preLineRow_bounded_go (c : Contract) (val : Nat → Row) (n : Nat)
    (hv : ∀ x r, c.regOf x = some r → bounded n (val r)) :
    ∀ (ts : List (String × Int)) (init : Row), bounded n init →
      bounded n (ts.foldl (fun acc (x, a) => match c.regOf x with | some r => Lin.add acc (Lin.scale a (val r)) | none => acc) init)
  | [], init, hi => hi
  | (x, a) :: rest, init, hi => by
    simp only [List.foldl_cons]
    cases hr : c.regOf x with
    | none => simp only [hr]; exact preLineRow_bounded_go c val n hv rest init hi
    | some r => simp only [hr]; exact preLineRow_bounded_go c val n hv rest _ (bounded_add hi (bounded_scale a (hv x r hr)))

theorem preLineRow_bounded (c : Contract) (val : Nat → Row) (n : Nat)
    (hv : ∀ x r, c.regOf x = some r → bounded n (val r)) (k : Int) (ts : List (String × Int)) :
    bounded n (preLineRow c val k ts) :=
  preLineRow_bounded_go c val n hv ts (Lin.const k) (bounded_const n k)

theorem foldl_preLine_congr (c : Contract) (f g : Nat → Int) (heq : ∀ x r, c.regOf x = some r → f r = g r) :
    ∀ (ts : List (String × Int)) (init : Int),
      ts.foldl (fun acc (x, a) => match c.regOf x with | some r => acc + a * f r | none => acc) init =
      ts.foldl (fun acc (x, a) => match c.regOf x with | some r => acc + a * g r | none => acc) init
  | [], _ => rfl
  | (x, a) :: rest, init => by
    simp only [List.foldl_cons]
    cases hr : c.regOf x with
    | none => simp only [hr]; exact foldl_preLine_congr c f g heq rest init
    | some r => simp only [hr, heq x r hr]; exact foldl_preLine_congr c f g heq rest _

theorem findRun_spec {s : Sym} {b l : Nat} : ∀ {regs : List (Nat × Nat)} {k j : Nat}, findRun s b l regs k = some j →
    ∃ b0 l0, k ≤ j ∧ regs[j - k]? = some (b0, l0) ∧ s.reg b = Lin.var b0 ∧ s.reg l = Lin.var l0
  | [], _, _, h => by simp [findRun] at h
  | (b0, l0) :: more, k, j, h => by
    simp only [findRun] at h
    split at h
    next hc =>
      injection h with h; subst h
      have hc' : s.reg b = Lin.var b0 ∧ s.reg l = Lin.var l0 := by simpa using hc
      exact ⟨b0, l0, Nat.le_refl _, by simp, hc'.1, hc'.2⟩
    next =>
      obtain ⟨b1, l1, hk, hr, e1, e2⟩ := findRun_spec h
      refine ⟨b1, l1, by omega, ?_, e1, e2⟩
      have : j - k = (j - (k + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]; exact hr

theorem regions_args {c : Contract} {b l : Nat} (h : (b, l) ∈ c.regions) : b ∈ c.argRegs ∧ l ∈ c.argRegs := by
  obtain ⟨hb, len, hl⟩ := regionsIn_mem c c.args c.argRegs b l h
  exact ⟨hb, regOfIn_mem len c.args c.argRegs l hl⟩

/-! ## A call, on either machine

`callFits` has seen to it that the call is one the function's machine makes of a function for the same
machine: the instruction puts the address to come back to where the called function's contract has it,
below the stack pointer (x86-64) or in the register x30 (AArch64). The lemmas here say what such a call
does in the words of the contract (`slot`: how many bytes of that address lie at the stack pointer, eight
or none), so that each rule for a call is shown once, for both machines. -/

/-- A register a call instruction leaves as it is: neither the stack pointer nor the register that holds
the address to come back to on AArch64. (A word of its own, so that `omega` does not take the two
inequalities for facts to split on: with three such registers in sight it took eight times as long.) -/
def CallKeeps (r : Nat) : Prop := r ≠ RSP ∧ r ≠ LINK

theorem callKeeps {r : Nat} (h1 : r ≠ RSP) (h2 : r ≠ LINK) : CallKeeps r := ⟨h1, h2⟩

/-- What `callFits` has seen to, at a call of a function with the contract `c`, `st` being the machine's
state at the call: the called function is for this function's machine; the call instruction puts the
address to come back to where the called function's contract has it; and on AArch64 the stack pointer is
a multiple of 16. -/
structure Fits (ctx : Ctx) (st : State) (i : Instr) (c : Contract) : Prop where
  machine : c.arm64 = ctx.contract.arm64
  link : callLink i = c.link
  aligned : c.arm64 = true → st.reg RSP % 16 = 0

/-- On AArch64 the stack pointer is a multiple of 16 at a call: it is a multiple of 16 away from where it
was at this function's entry, where it was one. -/
theorem callFits_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s : Sym} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) {i : Instr} {c : Contract} (h : callFits ctx s i c = true) : Fits ctx st i c := by
  unfold callFits at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun ha => ?_⟩
  rcases h3 with h3 | h3
  · rw [ha] at h3; cases h3
  · cases hs : s.sp with
    | none => rw [hs] at h3; cases h3
    | some sp =>
      rw [hs] at h3
      have h16 : sp % 16 = 0 := by simpa using h3
      have e := ev_isConst (ρ := ρ) hs
      simp only [ev_sub, ev_var] at e
      have r1 := H.reg RSP ctx.rsp_lt
      have r2 := H.entry RSP ctx.rsp_lt
      have al := E.aligned (h1 ▸ ha)
      omega

namespace Fits
variable {ctx : Ctx} {st : State} {i : Instr} {c : Contract} (F : Fits ctx st i c)
include F
/-- The called function's machine has the registers this function's has. -/
theorem regs : c.regs = ctx.nreg := by unfold Ctx.nreg Contract.regs; rw [F.machine]
theorem slot : c.slot = ctx.contract.slot := by unfold Contract.slot; rw [F.machine]
/-- A register an argument of the called function is in: one of this function's machine's, and neither the
stack pointer nor the register that holds the address to come back to. -/
theorem arg {r : Nat} (h : r ∈ c.argRegs) : r < ctx.nreg ∧ CallKeeps r :=
  ⟨F.regs ▸ (argRegs_spec h).1, (argRegs_spec h).2⟩
end Fits

theorem Contract.link_none {c : Contract} (h : c.link = none) : c.arm64 = false ∧ c.slot = 8 := by
  cases ha : c.arm64
  · exact ⟨rfl, by simp only [Contract.slot, ha, Bool.false_eq_true, ↓reduceIte]⟩
  · simp only [Contract.link, ha, ↓reduceIte] at h; cases h

theorem Contract.link_some {c : Contract} {l : Nat} (h : c.link = some l) : c.arm64 = true ∧ l = LINK ∧ c.slot = 0 := by
  cases ha : c.arm64
  · simp only [Contract.link, ha, Bool.false_eq_true, ↓reduceIte] at h; cases h
  · simp only [Contract.link, ha, ↓reduceIte] at h
    injection h with h
    exact ⟨rfl, h.symm, by simp only [Contract.slot, ha, ↓reduceIte]⟩

/-- The stack pointer the called function starts with: below the caller's by the bytes of the address to
come back to. -/
theorem afterCall_rsp {c : Contract} {p q : Program} {i : Instr} {st : State} (hl : callLink i = c.link) :
    (afterCall p q i st).reg RSP = st.reg RSP - c.slot := by
  cases h : c.link with
  | none =>
    rw [afterCall_stack (hl.trans h), (Contract.link_none h).2]
    show (if RSP = RSP then st.reg RSP - 8 else st.reg RSP) = st.reg RSP - 8
    rw [if_pos rfl]
  | some l =>
    obtain ⟨_, rfl, e⟩ := Contract.link_some h
    rw [afterCall_link (hl.trans h), e]
    show (if RSP = LINK then (p.base + i.next) % M64 else st.reg RSP) = st.reg RSP - 0
    rw [if_neg (by decide)]; rfl

/-- Every other register, but the one that holds the address to come back to on AArch64, is as it was. -/
theorem afterCall_reg {c : Contract} {p q : Program} {i : Instr} {st : State} (hl : callLink i = c.link)
    {r : Nat} (hrk : CallKeeps r) : (afterCall p q i st).reg r = st.reg r := by
  obtain ⟨hr, hk⟩ := hrk
  cases h : c.link with
  | none =>
    rw [afterCall_stack (hl.trans h)]
    show (if r = RSP then st.reg RSP - 8 else st.reg r) = st.reg r
    rw [if_neg hr]
  | some l =>
    obtain ⟨_, rfl, _⟩ := Contract.link_some h
    rw [afterCall_link (hl.trans h)]
    show (if r = LINK then (p.base + i.next) % M64 else st.reg r) = st.reg r
    rw [if_neg hk]

/-- Memory is as it was, but for the bytes of the address to come back to below the stack pointer. -/
theorem afterCall_mem {c : Contract} {p q : Program} {i : Instr} {st : State} (hl : callLink i = c.link)
    (h8 : c.slot ≤ st.reg RSP) {x : Nat} (hx : x < st.reg RSP - c.slot ∨ st.reg RSP ≤ x) :
    (afterCall p q i st).mem x = st.mem x := by
  cases h : c.link with
  | none =>
    rw [afterCall_stack (hl.trans h)]
    rw [(Contract.link_none h).2] at hx h8
    show store st.mem (st.reg RSP - 8) (p.base + i.next) 8 x = st.mem x
    exact store_other _ _ _ _ _ (by omega)
  | some l => rw [afterCall_link (hl.trans h)]

/-- On AArch64 the stack pointer the called function starts with is a multiple of 16, as its contract asks. -/
theorem afterCall_aligned {ctx : Ctx} {st : State} {i : Instr} {c : Contract} (F : Fits ctx st i c) (p q : Program)
    (ha : c.arm64 = true) : (afterCall p q i st).reg RSP % 16 = 0 := by
  have hs : c.slot = 0 := by simp only [Contract.slot, ha, ↓reduceIte]
  rw [afterCall_rsp F.link, hs]
  exact F.aligned ha

/-- The registers hold numbers below 2^64 in the state the called function starts in. -/
theorem afterCall_small {c : Contract} {p q : Program} {i : Instr} {st : State} (hl : callLink i = c.link)
    (hs : ∀ r, st.reg r < M64) (r : Nat) : (afterCall p q i st).reg r < M64 := by
  cases h : c.link with
  | none =>
    rw [afterCall_stack (hl.trans h)]
    show (if r = RSP then st.reg RSP - 8 else st.reg r) < M64
    split
    · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (hs RSP)
    · exact hs r
  | some l =>
    rw [afterCall_link (hl.trans h)]
    show (if r = l then (p.base + i.next) % M64 else st.reg r) < M64
    split
    · exact Nat.mod_lt _ (by decide)
    · exact hs r

/-- The address the called function's contract has it return to is the instruction after the call. -/
theorem afterCall_back {c : Contract} {p q : Program} {i : Instr} {st : State} (hl : callLink i = c.link)
    (hret : p.base + i.next < M64) (h8 : c.slot ≤ st.reg RSP) : c.backTo (afterCall p q i st) = p.base + i.next := by
  cases h : c.link with
  | none =>
    obtain ⟨ha, hs⟩ := Contract.link_none h
    rw [hs] at h8
    simp only [Contract.backTo, ha, Bool.false_eq_true, ↓reduceIte]
    rw [afterCall_stack (hl.trans h)]
    show load (store st.mem (st.reg RSP - 8) (p.base + i.next) 8) (if RSP = RSP then st.reg RSP - 8 else st.reg RSP) 8 = p.base + i.next
    rw [if_pos rfl]
    exact load_store_same _ _ _ _ (by unfold M64 at hret; omega)
  | some l =>
    obtain ⟨ha, rfl, _⟩ := Contract.link_some h
    simp only [Contract.backTo, ha, ↓reduceIte]
    rw [afterCall_link (hl.trans h)]
    show (if LINK = LINK then (p.base + i.next) % M64 else st.reg LINK) = p.base + i.next
    rw [if_pos rfl, Nat.mod_eq_of_lt hret]

/-- Each run of bytes a called function is given is one of this function's own, whole. -/
theorem calleeEnv_regions {ctx : Ctx} {c : Contract} {s : Sym} : ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × SVal)},
    calleeEnv ctx c s args regs = some env → ∀ r l, (r, l) ∈ regionsIn c args regs →
    ∃ (j b0 l0 : Nat), ctx.contract.regions[j]? = some (b0, l0) ∧ s.reg r = Lin.var b0 ∧ s.reg l = Lin.var l0
  | [], _, _, _, r, l, m => by simp [regionsIn] at m
  | _ :: _, [], _, _, r, l, m => by simp [regionsIn] at m
  | (n, .number) :: args, x :: regs, env, h, r, l, m => by
    simp only [calleeEnv] at h
    cases hrec : calleeEnv ctx c s args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [regionsIn] at m
      exact calleeEnv_regions args regs hrec r l m
  | (n, .bytes len) :: args, x :: regs, env, h, r, l, m => by
    simp only [calleeEnv] at h
    cases hl : c.regOf len with
    | none =>
      simp only [hl] at h
      simp only [regionsIn, hl] at m
      exact calleeEnv_regions args regs h r l m
    | some l1 =>
      simp only [hl] at h
      cases hf : findRun s x l1 ctx.contract.regions 0 with
      | none => simp [hf] at h
      | some j =>
        cases hrec : calleeEnv ctx c s args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          simp only [regionsIn, hl, List.mem_cons] at m
          rcases m with m | m
          · injection m with m1 m2
            subst m1 m2
            obtain ⟨b0, l0, _, hr, e1, e2⟩ := findRun_spec hf
            exact ⟨j, b0, l0, by simpa using hr, e1, e2⟩
          · exact calleeEnv_regions args regs hrec r l m

theorem calleeEnv_bounded {ctx : Ctx} {c : Contract} {s : Sym} (wf : WF ctx s) : ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × SVal)},
    (∀ r ∈ regs, r < ctx.nreg) → calleeEnv ctx c s args regs = some env → EnvB s.nvars env
  | [], _, env, _, h => by
    simp only [calleeEnv] at h; injection h with h; subst h; exact fun nv m => nomatch m
  | _ :: _, [], env, _, h => by
    simp only [calleeEnv] at h; injection h with h; subst h; exact fun nv m => nomatch m
  | (n, .number) :: args, x :: regs, env, hr, h => by
    simp only [calleeEnv] at h
    cases hrec : calleeEnv ctx c s args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map] at h
      injection h with h
      subst h
      intro nv m
      cases m with
      | head => exact wf.reg x (hr x (List.mem_cons_self ..))
      | tail _ m => exact calleeEnv_bounded wf args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) hrec nv m
  | (n, .bytes len) :: args, x :: regs, env, hr, h => by
    simp only [calleeEnv] at h
    cases hl : c.regOf len with
    | none =>
      simp only [hl] at h
      exact calleeEnv_bounded wf args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) h
    | some l1 =>
      simp only [hl] at h
      cases hf : findRun s x l1 ctx.contract.regions 0 with
      | none => simp [hf] at h
      | some j =>
        cases hrec : calleeEnv ctx c s args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          simp only [hf, hrec] at h
          injection h with h
          subst h
          intro nv m
          cases m with
          | head => trivial
          | tail _ m => exact calleeEnv_bounded wf args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) hrec nv m

/-- A called function's names on symbols mean its names in the state it starts in. -/
theorem semEnv_calleeEnv {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {c : Contract} {s1 : State}
    (hentry : ∀ r, r < ctx.nreg → ρ r = s0.reg r)
    (hreg : ∀ r ∈ c.argRegs, (s1.reg r : Int) = ev ρ (s.reg r))
    (hmem : ∀ b0 l0, (b0, l0) ∈ ctx.contract.regions → ∀ k, k < s0.reg l0 → s1.mem (s0.reg b0 + k) = s0.mem (s0.reg b0 + k)) :
    ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × SVal)}, (∀ r ∈ regs, r ∈ c.argRegs) →
    calleeEnv ctx c s args regs = some env → semEnv ctx s0 ρ env = envIn c s1 args regs
  | [], _, env, _, h => by
    simp only [calleeEnv] at h; injection h with h; subst h; simp [semEnv, envIn]
  | _ :: _, [], env, _, h => by
    simp only [calleeEnv] at h; injection h with h; subst h; simp [semEnv, envIn]
  | (n, .number) :: args, x :: regs, env, hr, h => by
    simp only [calleeEnv] at h
    cases hrec : calleeEnv ctx c s args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map] at h
      injection h with h
      subst h
      have ih := semEnv_calleeEnv hentry hreg hmem args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) hrec
      simp only [semEnv, List.map_cons, envIn, semv] at ih ⊢
      rw [ih, hreg x (hr x (List.mem_cons_self ..))]
  | (n, .bytes len) :: args, x :: regs, env, hr, h => by
    simp only [calleeEnv] at h
    cases hl : c.regOf len with
    | none =>
      simp only [hl] at h
      have ih := semEnv_calleeEnv hentry hreg hmem args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) h
      simp only [envIn, hl]
      exact ih
    | some l1 =>
      simp only [hl] at h
      cases hf : findRun s x l1 ctx.contract.regions 0 with
      | none => simp [hf] at h
      | some j =>
        cases hrec : calleeEnv ctx c s args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          simp only [hf, hrec] at h
          injection h with h
          subst h
          have ih := semEnv_calleeEnv hentry hreg hmem args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) hrec
          obtain ⟨b0, l0, _, hreg0, e1, e2⟩ := findRun_spec hf
          have hreg0' : ctx.contract.regions[j]? = some (b0, l0) := by simpa using hreg0
          have hm := List.mem_of_getElem? hreg0'
          have lt := regions_lt hm
          have hl1 : l1 ∈ c.argRegs := regOfIn_mem len c.args c.argRegs l1 hl
          have rx : s1.reg x = s0.reg b0 := by
            have := hreg x (hr x (List.mem_cons_self ..))
            rw [e1, ev_var, hentry b0 lt.1] at this
            omega
          have rl : s1.reg l1 = s0.reg l0 := by
            have := hreg l1 hl1
            rw [e2, ev_var, hentry l0 lt.2] at this
            omega
          have hbytes : (List.range (s0.reg l0)).map (fun k => (s1.mem (s0.reg b0 + k)).val) = (List.range (s0.reg l0)).map (fun k => (s0.mem (s0.reg b0 + k)).val) :=
            List.map_congr_left fun k hk => congrArg Fin.val (hmem b0 l0 hm k (List.mem_range.mp hk))
          simp only [semEnv, List.map_cons, envIn, hl, semv, hreg0', runBytes] at ih ⊢
          rw [ih, rx, rl, hbytes]

/-! ## The state after a call -/

/-- What the unknowns are after a call: those made for the registers (`m` of them, from `n` on) are what
the registers then hold. -/
def afterRho (m n : Nat) (ρ : Nat → Int) (s2 : State) : Nat → Int :=
  fun k => if n ≤ k ∧ k < n + m then (s2.reg (k - n) : Int) else ρ k

theorem afterRho_agree (m n : Nat) (ρ : Nat → Int) (s2 : State) : Agree n ρ (afterRho m n ρ s2) := by
  intro k hk
  show ρ k = if n ≤ k ∧ k < n + m then (s2.reg (k - n) : Int) else ρ k
  rw [if_neg (by omega)]

theorem afterRho_new (m n : Nat) (ρ : Nat → Int) (s2 : State) {r : Nat} (hr : r < m) : afterRho m n ρ s2 (n + r) = s2.reg r := by
  show (if n ≤ n + r ∧ n + r < n + m then (s2.reg (n + r - n) : Int) else ρ (n + r)) = s2.reg r
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

theorem afterCall_wf {ctx : Ctx} {s : Sym} (wf : WF ctx s) (c : Contract) (hm : c.regs = ctx.nreg) (sp : Int) : WF ctx (s.afterCall c sp) := by
  refine ⟨Nat.le_trans wf.base (Nat.le_add_right _ _), ?_, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨wf.words.table, fun j r h => bounded_mono (Nat.le_add_right _ _) (wf.words.atoms j r h), fun x ids h => by simp [Sym.afterCall] at h,
     wf.words.rotrs, (fun _ _ _ h => by simp [Sym.afterCall] at h), fun _ _ h => nomatch h⟩,
    fun k m => Known.wf_mono (Nat.le_add_right _ _) (Nat.le_refl _) (wf.known k m),
    fun rg h => let ⟨b1, b2⟩ := wf.range rg h; ⟨bounded_mono (Nat.le_add_right _ _) b1, fun v mv => SVal.bounded_mono (Nat.le_add_right _ _) (b2 v mv)⟩⟩
  · intro r hr
    show bounded (s.nvars + c.regs) (if c.scratch.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    split
    · exact bounded_var (by omega)
    · exact bounded_mono (Nat.le_add_right _ _) (wf.reg r hr)
  · intro o v m
    exact bounded_mono (Nat.le_add_right _ _) (wf.frame o v (List.mem_filter.mp m).1)
  · intro o i m
    exact wf.frameW o i (List.mem_filter.mp m).1
  · intro f m
    simp only [Sym.afterCall, List.mem_append] at m
    rcases m with m | m
    · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp m
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
      have hr := scratch_lt hr
      simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · exact bounded_var (show s.nvars + r < s.nvars + c.regs by omega)
      · exact bounded_sub (bounded_const _ _) (bounded_var (show s.nvars + r < s.nvars + c.regs by omega))
    · exact bounded_mono (Nat.le_add_right _ _) (wf.facts f m)
  · intro v r o m
    have := wf.bytes v r o m
    exact ⟨Nat.lt_of_lt_of_le this.1 (Nat.le_add_right _ _), bounded_mono (Nat.le_add_right _ _) this.2⟩
  · intro f m
    exact SFact.bounded_mono (Nat.le_add_right _ _) (wf.spec f m)
  · intro w o x m
    exact ⟨bounded_mono (Nat.le_add_right _ _) (wf.wrote w o x m).1, bounded_mono (Nat.le_add_right _ _) (wf.wrote w o x m).2⟩

theorem each_bounds_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {c : Contract}
    {i : Instr} (F : Fits ctx st i c) (p q : Program) (H : Holds ctx s0 ρ s st) :
    ∀ (bs : List (String × Nat)) {items rest : Items},
    each (fun (xb : String × Nat) =>
      match c.regOf xb.1 with
      | some rb => entail s.facts (Lin.sub (Lin.const ((xb.2 : Int) - 1)) (s.reg rb))
      | none => pure ()) bs items = .ok ((), rest) →
    ∀ x b, (x, b) ∈ bs → ∀ r, c.regOf x = some r → (afterCall p q i st).reg r < b
  | [], _, _, _, _, _, m, _, _ => nomatch m
  | (x0, b0) :: more, items, rest, h, x, b, m, r, hr => by
    simp only [each] at h
    obtain ⟨_, r1, e1, e2⟩ := V.bind_ok h
    cases m with
    | head =>
      rw [hr] at e1
      have hok := entail_sound e1 ρ H.facts
      simp only [holds_iff, ev_sub, ev_const] at hok
      have rarg : r ∈ c.argRegs := regOfIn_mem x0 c.args c.argRegs r hr
      obtain ⟨r16, rne⟩ := F.arg rarg
      have hreg := H.reg r r16
      rw [afterCall_reg F.link rne]; omega
    | tail _ mt => exact each_bounds_sound F p q H more e2 x b mt r hr

theorem each_atLeast_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {c : Contract}
    {i : Instr} (F : Fits ctx st i c) (p q : Program) (H : Holds ctx s0 ρ s st) :
    ∀ (al : List (String × Nat)) {items rest : Items},
    each (fun (xk : String × Nat) =>
      match c.regOf xk.1 with
      | some rb => entail s.facts (Lin.sub (s.reg rb) (Lin.const xk.2))
      | none => pure ()) al items = .ok ((), rest) →
    ∀ x k, (x, k) ∈ al → ∀ r, c.regOf x = some r → k ≤ (afterCall p q i st).reg r
  | [], _, _, _, _, _, m, _, _ => nomatch m
  | (x0, k0) :: more, items, rest, h, x, k, m, r, hr => by
    simp only [each] at h
    obtain ⟨_, r1, e1, e2⟩ := V.bind_ok h
    cases m with
    | head =>
      rw [hr] at e1
      have hok := entail_sound e1 ρ H.facts
      simp only [holds_iff, ev_sub, ev_const] at hok
      have rarg : r ∈ c.argRegs := regOfIn_mem x0 c.args c.argRegs r hr
      obtain ⟨r16, rne⟩ := F.arg rarg
      have hreg := H.reg r r16
      rw [afterCall_reg F.link rne]; omega
    | tail _ mt => exact each_atLeast_sound F p q H more e2 x k mt r hr

theorem each_preLines_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {c : Contract}
    {i : Instr} (F : Fits ctx st i c) (p q : Program) (H : Holds ctx s0 ρ s st) :
    ∀ (pl : List (Int × List (String × Int))) {items rest : Items},
    each (fun (kt : Int × List (String × Int)) =>
      entail s.facts (preLineRow c s.reg kt.1 kt.2)) pl items = .ok ((), rest) →
    ∀ k ts, (k, ts) ∈ pl → 0 ≤ preLineVal c (afterCall p q i st) k ts
  | [], _, _, _, _, _, m => nomatch m
  | (k0, ts0) :: more, items, rest, h, k, ts, m => by
    simp only [each] at h
    obtain ⟨_, r1, e1, e2⟩ := V.bind_ok h
    cases m with
    | head =>
      have hok := entail_sound e1 ρ H.facts
      simp only [ev_preLineRow] at hok
      unfold preLineVal
      have hcongr := foldl_preLine_congr c (fun r => ev ρ (s.reg r)) (fun r => ((afterCall p q i st).reg r : Int))
        (fun x r hr => by
          have rarg : r ∈ c.argRegs := regOfIn_mem x c.args c.argRegs r hr
          obtain ⟨r16, rne⟩ := F.arg rarg
          rw [afterCall_reg F.link rne, H.reg r r16]) ts0 0
      exact (congrArg (0 ≤ k0 + ·) hcongr).mp hok
    | tail _ mt => exact each_preLines_sound F p q H more e2 k ts mt

theorem stackAt_afterCall {ctx : Ctx} {st : State} {i : Instr} {c : Contract} (F : Fits ctx st i c) (p q : Program) :
    c.stackAt (afterCall p q i st) = c.stackAt st := by
  unfold Contract.stackAt
  cases hsb : c.stackBits with
  | none => rfl
  | some sb =>
    cases hr : c.regOf sb.arg with
    | none => simp only [hr]
    | some r =>
      have rarg : r ∈ c.argRegs := regOfIn_mem sb.arg c.args c.argRegs r hr
      simp only [hr, afterCall_reg F.link (F.arg rarg).2]

private theorem div_le_of_lt_succ {a sub div d : Nat} (hd : 0 < div) (h : a < sub + div * (d + 1)) :
    (a - sub) / div ≤ d := by
  have hpos : 0 < div * (d + 1) := Nat.mul_pos hd (Nat.succ_pos d)
  have : (a - sub) / div < d + 1 := (Nat.div_lt_iff_lt_mul hd).mpr (by rw [Nat.mul_comm]; omega)
  omega

private theorem div_succ_le_of_sub {a b sub div : Nat} (hd : 0 < div) (h1 : a + div ≤ b) (h2 : sub + div ≤ b) :
    (a - sub) / div + 1 ≤ (b - sub) / div := by
  have hle : a - sub + div ≤ b - sub := by omega
  have : (a - sub) / div + 1 = (a - sub + div) / div := by rw [Nat.add_div_right _ hd]
  rw [this]; exact Nat.div_le_div_right hle

theorem stackFitsAt_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {sp : Int} {extra : Nat} {c : Contract}
    (harm : c.arm64 = ctx.contract.arm64) (H : Holds ctx s0 ρ s st)
    (hg : stackFitsAt ctx s sp extra c = true) :
    sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - extra - (c.stackAt st : Int) := by
  have hregs : c.regs = ctx.nreg := by unfold Ctx.nreg Contract.regs; rw [harm]
  unfold stackFitsAt at hg
  obtain ⟨hsp0, hrest⟩ := Bool.and_eq_true_iff.mp hg
  have hsp0' : sp ≤ 0 := by simpa using hsp0
  refine ⟨hsp0', ?_⟩
  have hle0 := Contract.stack_le_stackAt ctx.contract s0
  cases hcb : c.stackBits with
  | none =>
    simp only [hcb] at hrest
    have hlow : -(ctx.contract.stack : Int) ≤ sp - extra - c.stack := by simpa using hrest
    simp only [Contract.stackAt, hcb, Nat.add_zero]; omega
  | some cb =>
    simp only [hcb] at hrest
    cases hrcal : c.regOf cb.arg with
    | none =>
      simp only [hrcal] at hrest
      have hlow : -(ctx.contract.stack : Int) ≤ sp - extra - c.stack := by simpa using hrest
      simp only [Contract.stackAt, hcb, hrcal, Nat.add_zero]; omega
    | some rcal =>
      simp only [hrcal] at hrest
      have rcal_arg : rcal ∈ c.argRegs := regOfIn_mem cb.arg c.args c.argRegs rcal hrcal
      have hrcal_val : (st.reg rcal : Int) = ev ρ (s.reg rcal) := H.reg rcal (hregs ▸ (argRegs_spec rcal_arg).1)
      cases hlin : cb.linear with
      | true =>
        simp only [hlin, ↓reduceIte, Bool.or_eq_true] at hrest
        rcases hrest with hconst | hpar
        · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hconst
          obtain ⟨hdiv, hrem, hcap⟩ := hconst
          simp only [Contract.stackAt, StackBits.units, hcb, hrcal, hlin, ↓reduceIte]
          rcases hcap with hstep0 | hpl
          · rw [hstep0]; omega
          · have hok := plain_sound hpl ρ H.facts
            simp only [ev_sub, ev_const, ← hrcal_val] at hok
            let rem := (ctx.contract.stack : Int) + sp - extra - c.stack
            let d := rem.toNat / cb.step
            have hq : (st.reg rcal - cb.sub) / cb.div ≤ d := div_le_of_lt_succ hdiv (by dsimp only [d, rem]; omega)
            have hmul : cb.step * ((st.reg rcal - cb.sub) / cb.div) ≤ rem.toNat :=
              Nat.le_trans (Nat.mul_le_mul_left cb.step hq) (Nat.mul_div_le _ _)
            omega
        · cases hpb : ctx.contract.stackBits with
          | none => simp [hpb] at hpar
          | some pb =>
            simp only [hpb, Bool.and_eq_true] at hpar
            obtain ⟨hpblin, hpar⟩ := hpar
            cases hrpar : ctx.contract.regOf pb.arg with
            | none => simp [hrpar] at hpar
            | some rpar =>
              simp only [hrpar, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hpar
              obtain ⟨⟨⟨hstep, hdiv_eq⟩, hdivc⟩, hcases⟩ := hpar
              have rpar_arg : rpar ∈ ctx.contract.argRegs := regOfIn_mem pb.arg ctx.contract.args ctx.contract.argRegs rpar hrpar
              have hrpar_lt : rpar < ctx.nreg := (argRegs_spec rpar_arg).1
              have hrpar_val : ρ rpar = (s0.reg rpar : Int) := H.entry rpar hrpar_lt
              simp only [Contract.stackAt, StackBits.units, hcb, hrcal, hpb, hrpar, hlin, hpblin, ↓reduceIte]
              rcases hcases with ⟨⟨hsub_le, hlow⟩, hpl⟩ | ⟨⟨⟨hsub_eq, hlow⟩, hpl1⟩, hpl2⟩
              · have hok := plain_sound hpl ρ H.facts
                simp only [ev_sub, ev_var, hrpar_val, ← hrcal_val] at hok
                have hdiv_le : (st.reg rcal - cb.sub) / cb.div ≤ (s0.reg rpar - pb.sub) / pb.div := by
                  rw [hdiv_eq]; exact Nat.div_le_div_right (by omega)
                have hmul : cb.step * ((st.reg rcal - cb.sub) / cb.div) ≤
                    pb.step * ((s0.reg rpar - pb.sub) / pb.div) := Nat.mul_le_mul hstep hdiv_le
                omega
              · have hok1 := plain_sound hpl1 ρ H.facts
                have hok2 := plain_sound hpl2 ρ H.facts
                simp only [ev_sub, ev_var, ev_const, hrpar_val, ← hrcal_val] at hok1 hok2
                have hsucc : (st.reg rcal - cb.sub) / cb.div + 1 ≤ (s0.reg rpar - pb.sub) / pb.div := by
                  rw [← hdiv_eq, hsub_eq]; exact div_succ_le_of_sub hdivc (by omega) (by omega)
                have hmul1 : cb.step * ((st.reg rcal - cb.sub) / cb.div) ≤
                    pb.step * ((st.reg rcal - cb.sub) / cb.div) := Nat.mul_le_mul_right _ hstep
                have hmul2 : pb.step * ((st.reg rcal - cb.sub) / cb.div + 1) ≤
                    pb.step * ((s0.reg rpar - pb.sub) / pb.div) := Nat.mul_le_mul_left pb.step hsucc
                have hmul3 : pb.step * ((st.reg rcal - cb.sub) / cb.div + 1) =
                    pb.step * ((st.reg rcal - cb.sub) / cb.div) + pb.step := Nat.mul_succ _ _
                omega
      | false =>
        simp only [hlin, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true] at hrest
        rcases hrest with hconst | hpar
        · obtain ⟨d, _, hd⟩ := List.any_eq_true.mp hconst
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
          obtain ⟨⟨hdiv, hlow⟩, hpl⟩ := hd
          have hok := plain_sound hpl ρ H.facts
          simp only [ev_sub, ev_const, ← hrcal_val] at hok
          have hpow : 0 < 2 ^ d := Nat.two_pow_pos d
          have hlt : st.reg rcal < cb.sub + cb.div * 2 ^ d := by omega
          have hbits : bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤ d :=
            bitsNat_le_of_lt_pow (div_lt_of_sub_lt hdiv hpow hlt)
          have hmul : cb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤ cb.step * d :=
            Nat.mul_le_mul_left cb.step hbits
          simp only [Contract.stackAt, StackBits.units, hcb, hrcal, hlin, Bool.false_eq_true, ↓reduceIte]; omega
        · cases hpb : ctx.contract.stackBits with
          | none => simp [hpb] at hpar
          | some pb =>
            simp only [hpb, Bool.and_eq_true, Bool.not_eq_true'] at hpar
            obtain ⟨hpblin, hpar⟩ := hpar
            cases hrpar : ctx.contract.regOf pb.arg with
            | none => simp [hrpar] at hpar
            | some rpar =>
              simp only [hrpar, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hpar
              obtain ⟨hstep, hcases⟩ := hpar
              have rpar_arg : rpar ∈ ctx.contract.argRegs := regOfIn_mem pb.arg ctx.contract.args ctx.contract.argRegs rpar hrpar
              have hrpar_lt : rpar < ctx.nreg := (argRegs_spec rpar_arg).1
              have hrpar_val : ρ rpar = (s0.reg rpar : Int) := H.entry rpar hrpar_lt
              simp only [Contract.stackAt, StackBits.units, hcb, hrcal, hpb, hrpar, hlin, hpblin, Bool.false_eq_true, ↓reduceIte]
              rcases hcases with (⟨⟨⟨hdiv_eq, hsub_le⟩, hlow⟩, hpl⟩ | ⟨⟨⟨hdivc, hdivp⟩, hlow⟩, hex⟩) | ⟨⟨⟨⟨⟨hdiv_eq, hsub_eq⟩, hdivc⟩, hlow⟩, hpl1⟩, hpl2⟩
              · have hok := plain_sound hpl ρ H.facts
                simp only [ev_sub, ev_var, hrpar_val, ← hrcal_val] at hok
                have hdiv_le : (st.reg rcal - cb.sub) / cb.div ≤ (s0.reg rpar - pb.sub) / pb.div := by
                  rw [hdiv_eq]; exact Nat.div_le_div_right (by omega)
                have hbits := bitsNat_mono hdiv_le
                have hmul : cb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤
                    pb.step * bitsNat ((s0.reg rpar - pb.sub) / pb.div) :=
                  Nat.mul_le_mul hstep hbits
                omega
              · obtain ⟨d, _, hd⟩ := List.any_eq_true.mp hex
                simp only [Bool.and_eq_true] at hd
                obtain ⟨hpl1, hpl2⟩ := hd
                have hok1 := plain_sound hpl1 ρ H.facts
                have hok2 := plain_sound hpl2 ρ H.facts
                simp only [ev_sub, ev_const, ← hrcal_val] at hok1
                simp only [ev_sub, ev_var, ev_const, hrpar_val] at hok2
                have hpow : 0 < 2 ^ d := Nat.two_pow_pos d
                have hlt : st.reg rcal < cb.sub + cb.div * 2 ^ d := by omega
                have hge : pb.sub + pb.div * 2 ^ d ≤ s0.reg rpar := by omega
                have hb1 : bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤ d :=
                  bitsNat_le_of_lt_pow (div_lt_of_sub_lt hdivc hpow hlt)
                have hb2 : d + 1 ≤ bitsNat ((s0.reg rpar - pb.sub) / pb.div) :=
                  le_bitsNat_of_pow_le (le_div_of_le_sub hdivp hge)
                have hmul1 : cb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤ pb.step * d :=
                  Nat.mul_le_mul hstep hb1
                have hmul2 : pb.step * (d + 1) ≤ pb.step * bitsNat ((s0.reg rpar - pb.sub) / pb.div) :=
                  Nat.mul_le_mul_left pb.step hb2
                have hmul3 : pb.step * (d + 1) = pb.step * d + pb.step := Nat.mul_succ pb.step d
                omega
              · have hok1 := plain_sound hpl1 ρ H.facts
                have hok2 := plain_sound hpl2 ρ H.facts
                simp only [ev_sub, ev_add, ev_var, ev_const, ev_scale, hrpar_val, ← hrcal_val] at hok1 hok2
                have hq_pos : 0 < (s0.reg rpar - pb.sub) / pb.div := by
                  rw [← hdiv_eq, ← hsub_eq]
                  exact (Nat.le_div_iff_mul_le hdivc).mpr (by omega)
                have hq_dbl : 2 * ((st.reg rcal - cb.sub) / cb.div) ≤ (s0.reg rpar - pb.sub) / pb.div := by
                  rw [← hdiv_eq, ← hsub_eq, Nat.le_div_iff_mul_le hdivc]
                  have hdm : cb.div * ((st.reg rcal - cb.sub) / cb.div) ≤ st.reg rcal - cb.sub :=
                    Nat.mul_div_le (st.reg rcal - cb.sub) cb.div
                  have hmul_comm : 2 * ((st.reg rcal - cb.sub) / cb.div) * cb.div =
                      2 * (cb.div * ((st.reg rcal - cb.sub) / cb.div)) := by
                    rw [Nat.mul_assoc, Nat.mul_comm _ cb.div]
                  omega
                have hbits := bitsNat_succ_le_of_double hq_pos hq_dbl
                have hmul1 : cb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤
                    pb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) := Nat.mul_le_mul_right _ hstep
                have hmul2 : pb.step * (bitsNat ((st.reg rcal - cb.sub) / cb.div) + 1) ≤
                    pb.step * bitsNat ((s0.reg rpar - pb.sub) / pb.div) := Nat.mul_le_mul_left pb.step hbits
                have hmul3 : pb.step * (bitsNat ((st.reg rcal - cb.sub) / cb.div) + 1) =
                    pb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) + pb.step := Nat.mul_succ _ _
                omega

theorem stackFits_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {sp : Int} {c : Contract}
    {i : Instr} (F : Fits ctx st i c) (p q : Program) (H : Holds ctx s0 ρ s st)
    (hg : stackFits ctx s sp c = true) :
    sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot - (c.stackAt (afterCall p q i st) : Int) := by
  rw [stackAt_afterCall F p q]
  exact stackFitsAt_sound F.machine H hg

private theorem stackFitsMLin_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym}
    {sp : Int} {extra : Nat} {c : Contract} {cb : StackBits} {rcal : Nat}
    (H : Holds ctx s0 ρ s st) (hcb : c.stackBits = some cb) (hrcal : c.regOf cb.arg = some rcal)
    (hdivc' : 0 < cb.div) (hlin : cb.linear = true)
    (hrcal_val : (st.reg rcal : Int) = ev ρ (s.reg rcal)) {items rest : Items}
    (h : stackFitsMLin ctx s sp extra c cb (s.reg rcal) items = .ok ((), rest)) :
    -(ctx.contract.stackAt s0 : Int) ≤ sp - extra - (c.stackAt st : Int) := by
  have hle0 := Contract.stack_le_stackAt ctx.contract s0
  unfold stackFitsMLin at h
  cases hpb : ctx.contract.stackBits with
  | none =>
    simp only [hpb] at h
    split at h
    next hrem =>
      simp only [Contract.stackAt, StackBits.units, hcb, hrcal, hpb, hlin, ↓reduceIte]
      split at h
      next hstep0 =>
        have hs0 : cb.step = 0 := by simpa using hstep0
        rw [hs0]; omega
      next =>
        let rem := (ctx.contract.stack : Int) + sp - extra - c.stack
        let d := rem.toNat / cb.step
        have hok := entail_sound h ρ H.facts
        simp only [ev_sub, ev_const, ← hrcal_val] at hok
        have hq : (st.reg rcal - cb.sub) / cb.div ≤ d := div_le_of_lt_succ hdivc' (by dsimp only [d, rem]; omega)
        have hmul : cb.step * ((st.reg rcal - cb.sub) / cb.div) ≤ rem.toNat :=
          Nat.le_trans (Nat.mul_le_mul_left cb.step hq) (Nat.mul_div_le _ _)
        omega
    next => exact (refuse_ok h).elim
  | some pb =>
    simp only [hpb] at h
    cases hpblin : pb.linear with
    | false => simp [hpblin] at h; exact (refuse_ok h).elim
    | true =>
      simp only [hpblin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hrpar : ctx.contract.regOf pb.arg with
      | none => simp [hrpar] at h; exact (refuse_ok h).elim
      | some rpar =>
        simp only [hrpar] at h
        have rpar_arg : rpar ∈ ctx.contract.argRegs := regOfIn_mem pb.arg ctx.contract.args ctx.contract.argRegs rpar hrpar
        have hrpar_lt : rpar < ctx.nreg := (argRegs_spec rpar_arg).1
        have hrpar_val : ρ rpar = (s0.reg rpar : Int) := H.entry rpar hrpar_lt
        simp only [Contract.stackAt, StackBits.units, hcb, hrcal, hpb, hrpar, hlin, hpblin, ↓reduceIte]
        split at h
        · exact (refuse_ok h).elim
        next hspb =>
          have hspb' : cb.step ≤ pb.step ∧ cb.div = pb.div := by simp at hspb; exact hspb
          obtain ⟨hstep, hdiv_eq⟩ := hspb'
          split at h
          next hmono =>
            have hmono' : pb.sub ≤ cb.sub ∧ -(ctx.contract.stack : Int) ≤ sp - extra - c.stack := by
              simpa using hmono
            have hok := entail_sound h ρ H.facts
            simp only [ev_sub, ev_var, hrpar_val, ← hrcal_val] at hok
            have hdiv_le : (st.reg rcal - cb.sub) / cb.div ≤ (s0.reg rpar - pb.sub) / pb.div := by
              rw [hdiv_eq]; exact Nat.div_le_div_right (by omega)
            have hmul : cb.step * ((st.reg rcal - cb.sub) / cb.div) ≤
                pb.step * ((s0.reg rpar - pb.sub) / pb.div) := Nat.mul_le_mul hstep hdiv_le
            omega
          next =>
            split at h
            next hdec =>
              have hdec' : pb.sub = cb.sub ∧ -(ctx.contract.stack : Int) - (pb.step : Int) ≤ sp - extra - c.stack := by
                simpa using hdec
              obtain ⟨_, r1, e1, e2⟩ := V.bind_ok h
              have hok1 := entail_sound e1 ρ H.facts
              have hok2 := entail_sound e2 ρ H.facts
              simp only [ev_sub, ev_var, ev_const, hrpar_val, ← hrcal_val] at hok1 hok2
              have hsucc : (st.reg rcal - cb.sub) / cb.div + 1 ≤ (s0.reg rpar - pb.sub) / pb.div := by
                rw [← hdiv_eq, hdec'.1]; exact div_succ_le_of_sub hdivc' (by omega) (by omega)
              have hmul1 : cb.step * ((st.reg rcal - cb.sub) / cb.div) ≤
                  pb.step * ((st.reg rcal - cb.sub) / cb.div) := Nat.mul_le_mul_right _ hstep
              have hmul2 : pb.step * ((st.reg rcal - cb.sub) / cb.div + 1) ≤
                  pb.step * ((s0.reg rpar - pb.sub) / pb.div) := Nat.mul_le_mul_left pb.step hsucc
              have hmul3 : pb.step * ((st.reg rcal - cb.sub) / cb.div + 1) =
                  pb.step * ((st.reg rcal - cb.sub) / cb.div) + pb.step := Nat.mul_succ _ _
              omega
            next => exact (refuse_ok h).elim

private theorem stackFitsMBits_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym}
    {sp : Int} {extra : Nat} {c : Contract} {cb : StackBits} {rcal : Nat}
    (H : Holds ctx s0 ρ s st) (hcb : c.stackBits = some cb) (hrcal : c.regOf cb.arg = some rcal)
    (hdivc' : 0 < cb.div) (hlin : cb.linear = false)
    (hrcal_val : (st.reg rcal : Int) = ev ρ (s.reg rcal)) {items rest : Items}
    (h : stackFitsMBits ctx s sp extra c cb (s.reg rcal) items = .ok ((), rest)) :
    -(ctx.contract.stackAt s0 : Int) ≤ sp - extra - (c.stackAt st : Int) := by
  have hle0 := Contract.stack_le_stackAt ctx.contract s0
  unfold stackFitsMBits at h
  cases hpb : ctx.contract.stackBits with
  | none =>
    simp only [hpb] at h
    split at h
    next hrem =>
      let rem := (ctx.contract.stack : Int) + sp - extra - c.stack
      let d := if cb.step == 0 then 63 else min 63 (rem.toNat / cb.step)
      have hok := entail_sound h ρ H.facts
      simp only [ev_sub, ev_const, ← hrcal_val] at hok
      have hpow : 0 < 2 ^ d := Nat.two_pow_pos d
      have hlt : st.reg rcal < cb.sub + cb.div * 2 ^ d := by dsimp only [d, rem]; omega
      have hbits : bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤ d :=
        bitsNat_le_of_lt_pow (div_lt_of_sub_lt hdivc' hpow hlt)
      have hstep_d : cb.step * d ≤ rem.toNat := by
        show cb.step * (if cb.step == 0 then 63 else min 63 (rem.toNat / cb.step)) ≤ rem.toNat
        cases hst0 : cb.step with
        | zero => simp
        | succ k =>
          simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
          exact Nat.le_trans (Nat.mul_le_mul_left (k + 1) (Nat.min_le_right 63 _)) (Nat.mul_div_le _ _)
      have hmul : cb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤ rem.toNat :=
        Nat.le_trans (Nat.mul_le_mul_left cb.step hbits) hstep_d
      simp only [Contract.stackAt, StackBits.units, hcb, hrcal, hpb, hlin, Bool.false_eq_true, ↓reduceIte]; omega
    next => exact (refuse_ok h).elim
  | some pb =>
    simp only [hpb] at h
    cases hpblin : pb.linear with
    | true => simp [hpblin] at h; exact (refuse_ok h).elim
    | false =>
      simp only [hpblin, Bool.false_eq_true, ↓reduceIte] at h
      cases hrpar : ctx.contract.regOf pb.arg with
      | none => simp [hrpar] at h; exact (refuse_ok h).elim
      | some rpar =>
        simp only [hrpar] at h
        have rpar_arg : rpar ∈ ctx.contract.argRegs := regOfIn_mem pb.arg ctx.contract.args ctx.contract.argRegs rpar hrpar
        have hrpar_lt : rpar < ctx.nreg := (argRegs_spec rpar_arg).1
        have hrpar_val : ρ rpar = (s0.reg rpar : Int) := H.entry rpar hrpar_lt
        simp only [Contract.stackAt, StackBits.units, hcb, hrcal, hpb, hrpar, hlin, hpblin, Bool.false_eq_true, ↓reduceIte]
        split at h
        · exact (refuse_ok h).elim
        next hspb =>
          have hspb' : cb.step ≤ pb.step ∧ 0 < pb.div := by simp at hspb; omega
          obtain ⟨hstep, hdivp⟩ := hspb'
          split at h
          next hmono =>
            have hmono' : cb.div = pb.div ∧ pb.sub ≤ cb.sub ∧ -(ctx.contract.stack : Int) ≤ sp - extra - c.stack := by
              simp at hmono; exact ⟨hmono.1.1, hmono.1.2, hmono.2⟩
            have hok := entail_sound h ρ H.facts
            simp only [ev_sub, ev_var, hrpar_val, ← hrcal_val] at hok
            have hdiv_le : (st.reg rcal - cb.sub) / cb.div ≤ (s0.reg rpar - pb.sub) / pb.div := by
              rw [hmono'.1]; exact Nat.div_le_div_right (by omega)
            have hbits := bitsNat_mono hdiv_le
            have hmul : cb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤
                pb.step * bitsNat ((s0.reg rpar - pb.sub) / pb.div) := Nat.mul_le_mul hstep hbits
            omega
          next =>
            split at h
            next hlow =>
              cases hkc : Lin.isConst (s.reg rcal) with
              | some k =>
                simp only [hkc] at h
                split at h
                next hk0 =>
                  split at h
                  next hd64 =>
                    have ek := ev_isConst (ρ := ρ) hkc
                    have hok := entail_sound h ρ H.facts
                    simp only [ev_sub, ev_var, ev_const, hrpar_val] at hok
                    let d := bitsNat ((k.toNat - cb.sub) / cb.div)
                    have hge : pb.sub + pb.div * 2 ^ d ≤ s0.reg rpar := by dsimp only [d]; omega
                    have hb2 : d + 1 ≤ bitsNat ((s0.reg rpar - pb.sub) / pb.div) :=
                      le_bitsNat_of_pow_le (le_div_of_le_sub hdivp hge)
                    have hkeq : st.reg rcal = k.toNat := by omega
                    have hmul1 : cb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤ pb.step * d := by
                      rw [hkeq]; exact Nat.mul_le_mul_right d hstep
                    have hmul2 : pb.step * (d + 1) ≤ pb.step * bitsNat ((s0.reg rpar - pb.sub) / pb.div) :=
                      Nat.mul_le_mul_left pb.step hb2
                    have hmul3 : pb.step * (d + 1) = pb.step * d + pb.step := Nat.mul_succ pb.step d
                    omega
                  next => exact (refuse_ok h).elim
                next => exact (refuse_ok h).elim
              | none =>
                simp only [hkc] at h
                cases hdiff : Lin.isConst (Lin.sub (Lin.var rpar) (s.reg rcal)) with
                | some diff =>
                  simp only [hdiff] at h
                  split at h
                  next hdpos =>
                    split at h
                    next hd64 =>
                      obtain ⟨_, r1, e1, e2⟩ := V.bind_ok h
                      have hok1 := entail_sound e1 ρ H.facts
                      have hok2 := entail_sound e2 ρ H.facts
                      simp only [ev_sub, ev_const, ← hrcal_val] at hok1
                      simp only [ev_sub, ev_var, ev_const, hrpar_val] at hok2
                      let d := Nat.log2 (diff.toNat / cb.div)
                      have hpow : 0 < 2 ^ d := Nat.two_pow_pos d
                      have hlt : st.reg rcal < cb.sub + cb.div * 2 ^ d := by dsimp only [d]; omega
                      have hge : pb.sub + pb.div * 2 ^ d ≤ s0.reg rpar := by dsimp only [d]; omega
                      have hb1 : bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤ d :=
                        bitsNat_le_of_lt_pow (div_lt_of_sub_lt hdivc' hpow hlt)
                      have hb2 : d + 1 ≤ bitsNat ((s0.reg rpar - pb.sub) / pb.div) :=
                        le_bitsNat_of_pow_le (le_div_of_le_sub hdivp hge)
                      have hmul1 : cb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤ pb.step * d :=
                        Nat.mul_le_mul hstep hb1
                      have hmul2 : pb.step * (d + 1) ≤ pb.step * bitsNat ((s0.reg rpar - pb.sub) / pb.div) :=
                        Nat.mul_le_mul_left pb.step hb2
                      have hmul3 : pb.step * (d + 1) = pb.step * d + pb.step := Nat.mul_succ pb.step d
                      omega
                    next => exact (refuse_ok h).elim
                  next => exact (refuse_ok h).elim
                | none =>
                  simp only [hdiff] at h
                  split at h
                  next hds =>
                    have hds' : cb.div = pb.div ∧ cb.sub = pb.sub := by simpa using hds
                    obtain ⟨hdiv_eq, hsub_eq⟩ := hds'
                    obtain ⟨_, r1, e1, e2⟩ := V.bind_ok h
                    have hok1 := entail_sound e1 ρ H.facts
                    have hok2 := entail_sound e2 ρ H.facts
                    simp only [ev_sub, ev_add, ev_var, ev_const, ev_scale, hrpar_val, ← hrcal_val] at hok1 hok2
                    have hq_pos : 0 < (s0.reg rpar - pb.sub) / pb.div := by
                      rw [← hdiv_eq, ← hsub_eq]
                      exact (Nat.le_div_iff_mul_le hdivc').mpr (by omega)
                    have hq_dbl : 2 * ((st.reg rcal - cb.sub) / cb.div) ≤ (s0.reg rpar - pb.sub) / pb.div := by
                      rw [← hdiv_eq, ← hsub_eq, Nat.le_div_iff_mul_le hdivc']
                      have hdm : cb.div * ((st.reg rcal - cb.sub) / cb.div) ≤ st.reg rcal - cb.sub :=
                        Nat.mul_div_le (st.reg rcal - cb.sub) cb.div
                      have hmul_comm : 2 * ((st.reg rcal - cb.sub) / cb.div) * cb.div =
                          2 * (cb.div * ((st.reg rcal - cb.sub) / cb.div)) := by
                        rw [Nat.mul_assoc, Nat.mul_comm _ cb.div]
                      omega
                    have hbits := bitsNat_succ_le_of_double hq_pos hq_dbl
                    have hmul1 : cb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) ≤
                        pb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) := Nat.mul_le_mul_right _ hstep
                    have hmul2 : pb.step * (bitsNat ((st.reg rcal - cb.sub) / cb.div) + 1) ≤
                        pb.step * bitsNat ((s0.reg rpar - pb.sub) / pb.div) := Nat.mul_le_mul_left pb.step hbits
                    have hmul3 : pb.step * (bitsNat ((st.reg rcal - cb.sub) / cb.div) + 1) =
                        pb.step * bitsNat ((st.reg rcal - cb.sub) / cb.div) + pb.step := Nat.mul_succ _ _
                    omega
                  next => exact (refuse_ok h).elim
            next => exact (refuse_ok h).elim

theorem stackFitsMAt_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {sp : Int} {extra : Nat} {c : Contract}
    (harm : c.arm64 = ctx.contract.arm64) (H : Holds ctx s0 ρ s st) {items rest : Items}
    (h : stackFitsMAt ctx s sp extra c items = .ok ((), rest)) :
    sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - extra - (c.stackAt st : Int) := by
  have hregs : c.regs = ctx.nreg := by unfold Ctx.nreg Contract.regs; rw [harm]
  by_cases hfast : stackFitsAt ctx s sp extra c = true
  · exact stackFitsAt_sound harm H hfast
  · unfold stackFitsMAt at h
    rw [if_neg hfast] at h
    split at h
    · exact (refuse_ok h).elim
    next hsp0 =>
      have hsp0' : sp ≤ 0 := by simpa using hsp0
      refine ⟨hsp0', ?_⟩
      cases hcb : c.stackBits with
      | none => simp [hcb] at h; exact (refuse_ok h).elim
      | some cb =>
        simp only [hcb] at h
        cases hrcal : c.regOf cb.arg with
        | none => simp [hrcal] at h; exact (refuse_ok h).elim
        | some rcal =>
          simp only [hrcal] at h
          split at h
          · exact (refuse_ok h).elim
          next hdivc =>
            have hdivc' : 0 < cb.div := by simp at hdivc; omega
            have rcal_arg : rcal ∈ c.argRegs := regOfIn_mem cb.arg c.args c.argRegs rcal hrcal
            have hrcal_val : (st.reg rcal : Int) = ev ρ (s.reg rcal) := H.reg rcal (hregs ▸ (argRegs_spec rcal_arg).1)
            cases hlin : cb.linear with
            | true =>
              simp only [hlin, ↓reduceIte] at h
              exact stackFitsMLin_sound H hcb hrcal hdivc' hlin hrcal_val h
            | false =>
              simp only [hlin, Bool.false_eq_true, ↓reduceIte] at h
              exact stackFitsMBits_sound H hcb hrcal hdivc' hlin hrcal_val h

theorem stackFitsM_sound {ctx : Ctx} {s0 st : State} {ρ : Nat → Int} {s : Sym} {sp : Int} {c : Contract}
    {i : Instr} (F : Fits ctx st i c) (p q : Program) (H : Holds ctx s0 ρ s st) {items rest : Items}
    (h : stackFitsM ctx s sp c items = .ok ((), rest)) :
    sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot - (c.stackAt (afterCall p q i st) : Int) := by
  rw [stackAt_afterCall F p q]
  exact stackFitsMAt_sound F.machine H h

theorem fixedPart_of_fixeds {ctx : Ctx} {s : Sym} {r n j b0 c0 : Nat}
    (hfp : fixedPart ctx s r n = some (j, b0, c0))
    {x0 : String} {r0 n0 : Nat} (hj : ctx.contract.fixeds[j]? = some (x0, r0, n0)) :
    ∃ off : Row, findOut (s.reg r) ctx.contract.fixeds 0 = some (.out j off) ∧
      Lin.isConst off = some (c0 : Int) ∧ c0 + n ≤ n0 ∧ b0 = r0 := by
  unfold fixedPart at hfp
  cases hfo : findOut (s.reg r) ctx.contract.fixeds 0 with
  | none =>
    simp only [hfo] at hfp
    cases hfr : findRegion (s.reg r) ctx.contract.regions 0 with
    | none => simp only [hfr] at hfp; cases hfp
    | some loc =>
      cases loc with
      | out _ _ => simp only [hfr] at hfp; cases hfp
      | frame _ => simp only [hfr] at hfp; cases hfp
      | data _ => simp only [hfr] at hfp; cases hfp
      | region k off =>
        simp only [hfr] at hfp
        cases hc : Lin.isConst off with
        | none => simp only [hc] at hfp; cases hfp
        | some c1 =>
          cases hrg : ctx.contract.regions[k]? with
          | none => simp only [hc, hrg] at hfp; cases hfp
          | some bl =>
            simp only [hc, hrg] at hfp
            split at hfp
            next =>
              injection hfp with hfp; injection hfp with ej _
              have hlt := (List.getElem?_eq_some_iff.mp hj).1
              omega
            next => cases hfp
  | some loc =>
    obtain ⟨j', off, x'', r'', n'', rfl, _, hj', _⟩ := findOut_spec hfo
    simp only [hfo] at hfp
    have hj'' : ctx.contract.fixeds[j']? = some (x'', r'', n'') := by simpa using hj'
    simp only [hj''] at hfp
    cases hc : Lin.isConst off with
    | none => simp only [hc] at hfp; cases hfp
    | some c1 =>
      simp only [hc] at hfp
      split at hfp
      next hcc =>
        injection hfp with hfp; injection hfp with ej eb; injection eb with eb ec
        subst ej eb ec
        rw [hj] at hj''; injection hj'' with hfx; injection hfx with ex er; injection er with er en
        subst ex er en
        have hcc' : 0 ≤ c1 ∧ c1 + (n : Int) ≤ (n0 : Int) := by simpa using hcc
        refine ⟨off, rfl, ?_, by omega, rfl⟩
        rw [Int.toNat_of_nonneg hcc'.1]; exact hc
      next => cases hfp

theorem callMboundsItem_sound {ctx : Ctx} {p q : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym} {sp : Int}
    {c : Contract} {i : Instr} (E : Setting ctx p s0) (F : Fits ctx st i c) (H : Holds ctx s0 ρ s st)
    (hsp : (st.reg RSP : Int) = s0.reg RSP + sp) (hsp0 : sp ≤ 0)
    (hlow : -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot)
    {x : String} {o bd r1 n1 : Nat} {items rest : Items}
    (hfxmem : (x, r1, n1) ∈ c.fixeds)
    (e1 : (if !(o + 8 ≤ n1) then refuse "a called function bounds bytes outside its fixed run"
      else
        match fixedPart ctx s r1 n1 with
        | some (j, _, c0) =>
          match ctx.contract.fixeds[j]? with
          | some (x0, _, _) =>
            if ctx.contract.mbounds.any fun (x', o', bd') => x' == x0 && o' == c0 + o && bd' ≤ bd then pure ()
            else refuse "a called function bounds a number in a fixed run that is not bounded in this function's contract"
          | none => refuse "a called function bounds a number in memory that is not known to lie below that bound"
        | none =>
          match frameAt s r1 with
          | some cf =>
            if sp ≤ cf + (o : Int) ∧ cf + (o : Int) + 8 ≤ 0 then
              match s.frame.find? (fun cell => cell.1 == cf + (o : Int)) with
              | some (_, row) => entail s.facts (Lin.sub (Lin.const ((bd : Int) - 1)) row)
              | none => refuse "a called function bounds a number in the frame that is not a known cell"
            else refuse "a called function bounds a number outside the frame"
          | none => refuse "a called function bounds a number in memory that is not known to lie below that bound") items = .ok ((), rest)) :
    load (afterCall p q i st).mem ((afterCall p q i st).reg r1 + o) 8 < bd := by
  split at e1
  next => exact (refuse_ok e1).elim
  next hon =>
    have hon' : o + 8 ≤ n1 := by simpa using hon
    have hrarg : r1 ∈ c.argRegs := fixedsIn_mem c.args c.argRegs x r1 n1 hfxmem
    obtain ⟨r16, rne⟩ := F.arg hrarg
    have hreg1 : (afterCall p q i st).reg r1 = st.reg r1 := afterCall_reg F.link rne
    have hreg := H.reg r1 r16
    cases hfp : fixedPart ctx s r1 n1 with
    | some p0 =>
      obtain ⟨j, b0, c0⟩ := p0
      simp only [hfp] at e1
      cases hj : ctx.contract.fixeds[j]? with
      | none => simp only [hj] at e1; exact (refuse_ok e1).elim
      | some fx0 =>
        obtain ⟨x0, r0, n0⟩ := fx0
        simp only [hj] at e1
        split at e1
        next hany =>
          clear e1
          obtain ⟨⟨x', o', bd'⟩, hmb, hcond⟩ := List.any_eq_true.mp hany
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          obtain ⟨⟨hx', ho'⟩, hbd⟩ := hcond
          rw [hx', ho'] at hmb
          obtain ⟨off, hfo, hc, hcn, _⟩ := fixedPart_of_fixeds hfp hj
          obtain ⟨j', off', x'', r'', n'', hloc, _, hj', hoff⟩ := findOut_spec hfo
          have ej' : j' = j := by cases hloc; rfl
          have eo' : off' = off := by cases hloc; rfl
          rw [ej', Nat.sub_zero, hj] at hj'
          have er' : r'' = r0 := by cases hj'; rfl
          rw [eo', er'] at hoff
          have hm0 : (x0, r0, n0) ∈ ctx.contract.fixeds := List.mem_of_getElem? hj
          obtain ⟨hfit, hapart, _, hout0⟩ := E.fixedAt hm0
          have hmb0 : load s0.mem (s0.reg r0 + (c0 + o)) 8 < bd' := E.mbound hmb hm0
          have eoff := ev_isConst (ρ := ρ) hc
          rw [hoff, ev_sub, ev_var, H.entry r0 (fixeds_lt hm0)] at eoff
          have hst_r : st.reg r1 = s0.reg r0 + c0 := by omega
          have hstack := E.stackAt
          have hmem_eq : load (afterCall p q i st).mem ((afterCall p q i st).reg r1 + o) 8 =
              load s0.mem (s0.reg r0 + (c0 + o)) 8 := by
            rw [hreg1, hst_r, Nat.add_assoc]
            refine load_congr _ _ _ _ fun a ha1 ha2 => ?_
            have hslot : a < st.reg RSP - c.slot ∨ st.reg RSP ≤ a := by omega
            rw [afterCall_mem F.link (by omega) hslot]
            refine H.mem a ?_ ?_
            · simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
            · unfold Contract.inOut; rw [List.any_eq_false]
              intro ⟨x', r', n'⟩ hm'
              have := hout0 x' r' n' hm'
              simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
          rw [hmem_eq]; omega
        next => exact (refuse_ok e1).elim
    | none =>
      simp only [hfp] at e1
      cases hfa : frameAt s r1 with
      | none => simp only [hfa] at e1; exact (refuse_ok e1).elim
      | some cf =>
        simp only [hfa] at e1
        split at e1
        next hfr =>
          cases hfnd : s.frame.find? (fun cell => cell.1 == cf + (o : Int)) with
          | none => simp only [hfnd] at e1; exact (refuse_ok e1).elim
          | some cell =>
            simp only [hfnd] at e1
            have hmem := List.mem_of_find?_eq_some hfnd
            have hcell : cell.1 = cf + (o : Int) := by simpa using List.find?_some hfnd
            obtain ⟨g1, g2, g3⟩ := H.frame cell.1 cell.2 hmem
            rw [hcell] at g1 g2 g3
            have hok := entail_sound e1 ρ H.facts
            clear e1
            simp only [holds_iff, ev_sub, ev_const] at hok
            unfold frameAt at hfa
            have ecf := ev_isConst (ρ := ρ) hfa
            rw [ev_sub, ev_var, H.entry RSP ctx.rsp_lt] at ecf
            have hstack := E.stackAt
            have haddr : (afterCall p q i st).reg r1 + o = ((s0.reg RSP : Int) + (cf + (o : Int))).toNat := by
              rw [hreg1]; omega
            rw [haddr]
            have hmem_eq : load (afterCall p q i st).mem ((s0.reg RSP : Int) + (cf + (o : Int))).toNat 8 =
                load st.mem ((s0.reg RSP : Int) + (cf + (o : Int))).toNat 8 :=
              load_congr _ _ _ _ fun a ha1 ha2 => afterCall_mem F.link (by omega) (Or.inr (by omega))
            rw [hmem_eq]; omega
        next => exact (refuse_ok e1).elim

theorem callMboundsOne_sound {ctx : Ctx} {p q : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym} {sp : Int}
    {c : Contract} {i : Instr} (E : Setting ctx p s0) (F : Fits ctx st i c) (H : Holds ctx s0 ρ s st)
    (hsp : (st.reg RSP : Int) = s0.reg RSP + sp) (hsp0 : sp ≤ 0)
    (hlow : -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot)
    {x : String} {o bd : Nat} :
    ∀ (fxs : List (String × Nat × Nat)) {items rest : Items},
    (∀ x' r' n', (x', r', n') ∈ fxs → (x', r', n') ∈ c.fixeds) →
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
              if sp ≤ cf + (o : Int) ∧ cf + (o : Int) + 8 ≤ 0 then
                match s.frame.find? (fun cell => cell.1 == cf + (o : Int)) with
                | some (_, row) => entail s.facts (Lin.sub (Lin.const ((bd : Int) - 1)) row)
                | none => refuse "a called function bounds a number in the frame that is not a known cell"
              else refuse "a called function bounds a number outside the frame"
            | none => refuse "a called function bounds a number in memory that is not known to lie below that bound") fxs items = .ok ((), rest) →
    ∀ r n, (x, r, n) ∈ fxs → load (afterCall p q i st).mem ((afterCall p q i st).reg r + o) 8 < bd
  | [], _, _, _, _, _, _, m => nomatch m
  | (x1, r1, n1) :: more, items, rest, hsub, h, r, n, m => by
    simp only [each] at h
    obtain ⟨_, r_mid, e1, e2⟩ := V.bind_ok h
    cases m with
    | tail _ mt => exact callMboundsOne_sound E F H hsp hsp0 hlow more (fun a b d hm => hsub a b d (List.mem_cons_of_mem _ hm)) e2 r n mt
    | head =>
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at e1
      exact callMboundsItem_sound E F H hsp hsp0 hlow (hsub x r1 n1 (List.mem_cons_self ..)) e1

theorem callMboundsOk_sound {ctx : Ctx} {p q : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym} {sp : Int}
    {c : Contract} {i : Instr} (E : Setting ctx p s0) (F : Fits ctx st i c) (H : Holds ctx s0 ρ s st)
    (hsp : (st.reg RSP : Int) = s0.reg RSP + sp) (hsp0 : sp ≤ 0)
    (hlow : -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot) :
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
                if sp ≤ cf + (o : Int) ∧ cf + (o : Int) + 8 ≤ 0 then
                  match s.frame.find? (fun cell => cell.1 == cf + (o : Int)) with
                  | some (_, row) => entail s.facts (Lin.sub (Lin.const ((bd : Int) - 1)) row)
                  | none => refuse "a called function bounds a number in the frame that is not a known cell"
                else refuse "a called function bounds a number outside the frame"
              | none => refuse "a called function bounds a number in memory that is not known to lie below that bound") c.fixeds) mbs items = .ok ((), rest) →
    ∀ x o bd, (x, o, bd) ∈ mbs → ∀ r n, (x, r, n) ∈ c.fixeds → load (afterCall p q i st).mem ((afterCall p q i st).reg r + o) 8 < bd
  | [], _, _, _, _, _, _, m, _, _, _ => nomatch m
  | (x0, o0, bd0) :: more, items, rest, h, x, o, bd, m, r, n, hfx => by
    simp only [each] at h
    obtain ⟨_, r1, e1, e2⟩ := V.bind_ok h
    cases m with
    | head => exact callMboundsOne_sound E F H hsp hsp0 hlow c.fixeds (fun _ _ _ hm => hm) e1 r n hfx
    | tail _ mt => exact callMboundsOk_sound E F H hsp hsp0 hlow more e2 x o bd mt r n hfx

theorem callPreOk_sound {ctx : Ctx} {p q : Program} {s0 st : State} {ρ : Nat → Int} {s : Sym} {name : String} {c : Contract}
    {i : Instr} (E : Setting ctx p s0) (F : Fits ctx st i c) (H : Holds ctx s0 ρ s st) {items rest : Items}
    (h : callPreOk ctx s name c items = .ok ((), rest)) :
    CallExtra ctx s0 st c (afterCall p q i st) ∧
    (ctx.selfName = some name → ∀ d r, c.decreases = some d → c.regOf d = some r → (afterCall p q i st).reg r < s0.reg r) := by
  unfold callPreOk at h
  cases hsp : s.sp with
  | none =>
    simp only [hsp] at h
    obtain ⟨_, _, e0, _⟩ := V.bind_ok h
    exact (refuse_ok e0).elim
  | some sp =>
    simp only [hsp] at h
    obtain ⟨_, r0, e0, h⟩ := V.bind_ok h
    obtain ⟨_, rm, em, h⟩ := V.bind_ok h
    obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨_, r2, e2, h⟩ := V.bind_ok h
    have hg := stackFitsM_sound F p q H e0
    have esp := ev_isConst (ρ := ρ) hsp
    simp only [ev_sub, ev_var] at esp
    have h1 := H.reg RSP ctx.rsp_lt
    have h2 := H.entry RSP ctx.rsp_lt
    have hst : (st.reg RSP : Int) ≤ s0.reg RSP ∧
        -(ctx.contract.stackAt s0 : Int) ≤ (st.reg RSP : Int) - s0.reg RSP - c.slot - (c.stackAt (afterCall p q i st) : Int) := by
      omega
    have hmb := callMboundsOk_sound (q := q) E F H (by omega) hg.1 (by omega) c.mbounds em
    refine ⟨⟨hst, hmb, each_atLeast_sound F p q H c.atLeast e1, each_preLines_sound F p q H c.preLines e2⟩, ?_⟩
    intro hself d r hdec hr
    have hbeq : (ctx.selfName == some name) = true := by simp [hself]
    simp only [hbeq, ↓reduceIte, hdec, hr] at h
    have hok := entail_sound h ρ H.facts
    simp only [ev_sub, ev_sub, ev_var, ev_const] at hok
    have rarg : r ∈ c.argRegs := regOfIn_mem d c.args c.argRegs r hr
    obtain ⟨r16, rne⟩ := F.arg rarg
    have hreg := H.reg r r16
    have hent := H.entry r r16
    rw [afterCall_reg F.link rne]; omega

/-- Of the machine's state when the called function has returned, what the verifier holds after the call is
so: given that the registers a callee keeps and the stack pointer are as before the call, and memory is as
before but in the called function's frame and at the address it returned to (where that is in memory). -/
theorem afterCall_holds {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st s2 : State} {sp : Int} (c : Contract) (cst : Nat)
    (hm : c.regs = ctx.nreg) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (hsp : (st.reg RSP : Int) = s0.reg RSP + sp) (hlow : -(ctx.contract.stackAt s0 : Int) ≤ sp - cst) (hsp0 : sp ≤ 0)
    (hstack : ctx.contract.stackAt s0 ≤ s0.reg RSP)
    (hkeep : ∀ r, r < ctx.nreg → c.scratch.contains r = false → s2.reg r = st.reg r)
    (hsmall : ∀ r, s2.reg r < M64)
    (hmem : ∀ a, a + cst < st.reg RSP ∨ st.reg RSP ≤ a → s2.mem a = st.mem a)
    (hout : ∀ x r n, (x, r, n) ∈ ctx.contract.outs →
      s0.reg r + n ≤ s0.reg RSP - ctx.contract.stackAt s0 ∨ s0.reg RSP + ctx.contract.slot ≤ s0.reg r)
    (hdata : s2.data = st.data)
    (hvec : ∀ r ∈ c.keepsVec, s2.vec r = st.vec r) :
    Holds ctx s0 (afterRho c.regs s.nvars ρ s2) (s.afterCall c sp) s2 := by
  have ag := afterRho_agree c.regs s.nvars ρ s2
  have H' := H.agree wf ag
  refine ⟨H'.entry, ⟨H'.data.1, hdata.trans H.data.2⟩, ?_, hsmall, trivial, trivial, ?_, ?_, ?_, H'.bytes, H'.spec, ?_, ?_,
    ⟨(fun x ids h => by simp [Sym.afterCall] at h), (fun w m => by simp [Sym.afterCall] at m),
     (fun w j i m => by simp [Sym.afterCall] at m), fun _ _ h => nomatch h⟩,
    H'.known,
    (fun rg hrg => by
      obtain ⟨name, r, n, params, x, b, hi, g1, g2, g3, g4, g5⟩ := H'.range rg hrg
      refine ⟨name, r, n, params, x, b, hi, g1, g2, g3, g4, fun j hj1 hj2 => ?_⟩
      have ho := hout name r n (List.mem_of_getElem? g1)
      rw [hmem _ (by omega)]
      exact g5 j hj1 hj2),
    fun r hr => by
      obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
      rw [hvec r (List.contains_iff_mem.mp hr2)]
      exact H'.vecIntact r hr1⟩
  · intro r hr
    show (s2.reg r : Int) = ev _ (if c.scratch.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    cases hc : c.scratch.contains r with
    | true => rw [if_pos rfl, ev_var, afterRho_new _ _ _ _ (hm ▸ hr)]
    | false =>
      rw [if_neg (by decide), hkeep r hr hc]
      exact H'.reg r hr
  · intro o v m
    obtain ⟨m1, m2⟩ := List.mem_filter.mp m
    have m2' : sp ≤ o := by simpa using m2
    obtain ⟨h1, h2, h3⟩ := H'.frame o v m1
    refine ⟨h1, h2, ?_⟩
    have e : load s2.mem ((s0.reg RSP : Int) + o).toNat 8 = load st.mem ((s0.reg RSP : Int) + o).toNat 8 :=
      load_congr _ _ _ _ (fun x hx1 hx2 => hmem x (Or.inr (by omega)))
    rw [e]; exact h3
  · intro o i m
    obtain ⟨m1, m2⟩ := List.mem_filter.mp m
    have m2' : sp ≤ o := by simpa using m2
    obtain ⟨h1, h2, h3⟩ := H'.frameW o i m1
    refine ⟨h1, h2, ?_⟩
    have e : load s2.mem ((s0.reg RSP : Int) + o).toNat 4 = load st.mem ((s0.reg RSP : Int) + o).toNat 4 :=
      load_congr _ _ _ _ (fun x hx1 hx2 => hmem x (Or.inr (by omega)))
    rw [e]; exact h3
  · intro f m
    simp only [Sym.afterCall, List.mem_append] at m
    rcases m with m | m
    · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp m
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
      have hr := scratch_lt hr
      have sm := hsmall r
      unfold M64 at sm
      have val := afterRho_new c.regs s.nvars ρ s2 hr
      simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · rw [holds_iff, ev_var, val]; omega
      · rw [holds_iff, ev_sub, ev_const, ev_var, val]; simp only [top]; omega
    · exact H'.facts f m
  · intro a ha ho
    have hfr : a + cst < st.reg RSP ∨ st.reg RSP ≤ a := by
      simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at ha
      omega
    rw [hmem a hfr]
    exact H.mem a ha ho
  · -- what this function wrote for its caller lies outside its own frame, so outside the called function's
    intro w o x m
    obtain ⟨name, r, n, g1, g2, g3, g4⟩ := H'.wrote w o x m
    refine ⟨name, r, n, g1, g2, g3, ?_⟩
    have ho := hout name r n (List.mem_of_getElem? g1)
    rw [hmem _ (by omega)]
    exact g4

/-- **A call, by contract, of a function that writes nothing for its caller.** If the verifier has gone
through such a call, then of the machine at the call: the
address to come back to can be written; the state the called function starts in is one its contract's
caller has seen to; what the called function may touch, this function may touch; and of every state the
contract lets it return in, what the verifier holds after the call is so, at the next instruction. -/
theorem symCallPlain_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symCallPlain ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (q : Program) (hq : q.fits) (i : Instr) (F : Fits ctx st i c) (hret : p.base + i.next < M64)
    (hl : c.lanes = []) (hva : c.valArrays = []) (hex : CallExtra ctx s0 st c (afterCall p q i st)) :
    c.slot ≤ st.reg RSP ∧ allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true) ∧
    (∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.data = st.data →
      s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  cases hsp : s.sp with
  | none => simp only [symCallPlain, hsp] at h; exact (refuse_ok h).elim
  | some sp =>
    simp only [symCallPlain, hsp] at h
    · have e := ev_isConst (ρ := ρ) hsp
      simp only [ev_sub, ev_var] at e
      have h1 := H.reg RSP ctx.rsp_lt
      have h2 := H.entry RSP ctx.rsp_lt
      have hrsp : (st.reg RSP : Int) = s0.reg RSP + sp := by omega
      have hg : sp ≤ 0 ∧ -(ctx.contract.stackAt s0 : Int) ≤ sp - c.slot - (c.stackAt (afterCall p q i st) : Int) := by
        have := hex.stack; omega
      -- the called function writes nothing for its caller (the verifier has no rule for that yet)
      have hw : (c.outs.isEmpty && c.ensures.isEmpty && (c.fixeds.isEmpty && (c.inouts.isEmpty && c.ensuresW.isEmpty))) = true := by
        cases hw : (c.outs.isEmpty && c.ensures.isEmpty && (c.fixeds.isEmpty && (c.inouts.isEmpty && c.ensuresW.isEmpty))) with
        | true => rfl
        | false => simp only [hw, Bool.not_false, ↓reduceIte] at h; exact (refuse_ok h).elim
      simp only [hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      have hall : (c.outs = [] ∧ c.ensures = []) ∧ c.fixeds = [] ∧ c.inouts = [] ∧ c.ensuresW = [] := by simpa using hw
      have hout := hall.1
      have hfx := hall.2.1
      have hio := hall.2.2.1
      have hew := hall.2.2.2
      have hno : ∀ (x : State) (a : Nat), c.inOut x a = false := fun x a => by simp [Contract.inOut, hout.1]
      have hnf : ∀ (x : State) (a : Nat), c.inFixed x a = false := fun x a => by simp [Contract.inFixed, hfx, hio]
      cases henv : calleeEnv ctx c s c.args c.argRegs with
      | none => simp only [henv] at h; exact (refuse_ok h).elim
      | some env =>
        simp only [henv] at h
        obtain ⟨_, r0, hbounds, h⟩ := V.bind_ok h
        have hbd := each_bounds_sound F p q H c.bounds hbounds
        have e := ev_isConst (ρ := ρ) hsp
        simp only [ev_sub, ev_var] at e
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
        have hregion : ∀ r l, (r, l) ∈ c.regions → ∃ b0 l0, (b0, l0) ∈ ctx.contract.regions ∧
            (afterCall p q i st).reg r = s0.reg b0 ∧ (afterCall p q i st).reg l = s0.reg l0 := by
          intro r l m
          obtain ⟨j, b0, l0, hj, e1, e2⟩ := calleeEnv_regions c.args c.argRegs henv r l m
          have hm := List.mem_of_getElem? hj
          have lt := regions_lt hm
          obtain ⟨ar, al⟩ := regions_args m
          obtain ⟨r16, rne⟩ := F.arg ar
          obtain ⟨l16, lne⟩ := F.arg al
          refine ⟨b0, l0, hm, ?_, ?_⟩
          · rw [s1reg r rne]
            have := H.reg r r16
            rw [e1, ev_var, H.entry b0 lt.1] at this
            omega
          · rw [s1reg l lne]
            have := H.reg l l16
            rw [e2, ev_var, H.entry l0 lt.2] at this
            omega
        have hpre : c.pre q (afterCall p q i st) := by
          refine ⟨afterCall_rip p q i st, ?_, ?_, ?_, hq, ?_, (fun x r n m => by rw [hout.1] at m; cases m), (by rw [hout.1]; exact List.Pairwise.nil),
            (fun x r n m => by rw [hfx] at m; cases m),
            hbd, (fun x off b m r n mf => by rw [hfx] at mf; cases mf),
            (fun j x r count l m => by rw [tableAt_none hl] at m; cases m), hex.atLeast,
            afterCall_aligned F p q, hex.preLines, (fun x r l ch el m => by rw [hva] at m; cases m)⟩
          · exact afterCall_small F.link H.small
          · rw [s1rsp]; omega
          · rw [s1rsp]; omega
          · intro r l m
            obtain ⟨b0, l0, hm, er, el⟩ := hregion r l m
            obtain ⟨fit, apart⟩ := E.regionAt hm
            rw [er, el, s1rsp]
            exact ⟨fit, by omega⟩
        have hread : ∀ a, (c.perm ctx.pieces (afterCall p q i st)).read a = true → (ctx.contract.perm ctx.pieces s0).read a = true := by
          intro a ha
          rw [perm_read_split, Bool.or_eq_true] at ha
          refine ha.elim (fun ha => ?_) (fun ha => read_pieces H p q i ha)
          have hnv : c.inValArray (afterCall p q i st) a = false := by simp [Contract.inValArray, hva]
          simp only [Contract.perm, hnf, inLane_false hl, hnv, inPieces_nil, Bool.or_false, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          left; left; left
          rcases ha with (ha | ha) | ha
          · left; left; left; omega
          · left; left; left; omega
          · left; right
            obtain ⟨⟨r, l⟩, m, hin⟩ := List.any_eq_true.mp ha
            obtain ⟨b0, l0, hm, er, el⟩ := hregion r l m
            simp only [Bool.and_eq_true, decide_eq_true_eq, er, el] at hin
            exact List.any_eq_true.mpr ⟨(b0, l0), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hin⟩
        have hwrite : ∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true := by
          intro a ha
          simp only [Contract.perm, hno, Bool.or_false, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          left; omega
        have hwr : allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true := by
          apply allowed_of
          intro x hx1 hx2
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          left; omega
        refine ⟨h8, hwr, hpre, hread, hwrite, ?_⟩
        intro s2 post hdata2
        obtain ⟨prip, prsp, psaved, pmem, pret, psmall, _, pvec⟩ := post
        have hrip : s2.rip = p.base + i.next := by
          rw [prip]
          exact afterCall_back F.link hret h8
        have hkeep : ∀ r, r < ctx.nreg → c.scratch.contains r = false → s2.reg r = st.reg r := by
          intro r hr hc
          by_cases h4 : r = RSP
          · rw [h4, prsp, s1rsp]; omega
          · have hmemr : r ∈ c.keeps := kept_of_not_scratch (F.regs ▸ hr) h4 hc
            rw [psaved r hmemr, s1reg r (callKeeps h4 (keeps_spec hmemr).2.2)]
        have hmem2 : ∀ a, a + c.slot + c.stackAt (afterCall p q i st) < st.reg RSP ∨ st.reg RSP ≤ a → s2.mem a = st.mem a := by
          intro a ha
          rw [pmem a (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1rsp]; omega) (hno _ a)]
          exact s1mem a (by omega)
        have hvec2 : ∀ r ∈ c.keepsVec, s2.vec r = st.vec r := fun r hr =>
          (pvec r hr).trans (congrFun (afterCall_vec p q i st) r)
        have Hafter := afterCall_holds c (c.slot + c.stackAt (afterCall p q i st)) F.regs H wf hrsp (by omega) hg.1 hstack hkeep psmall (fun a ha => hmem2 a (by omega)) (fun x r n m => (E.outAt m).2) hdata2 hvec2
        have wafter := afterCall_wf wf c F.regs sp
        have ag := afterRho_agree c.regs s.nvars ρ s2
        cases hret' : c.returns with
        | none =>
          simp only [hret'] at h
          have := V.pure_ok h
          injection this with h1 _
          subst h1
          exact ⟨hrip, _, ag, Nat.le_add_right _ _, Hafter, wafter⟩
        | some e =>
          simp only [hret'] at h
          obtain ⟨⟨res, s3⟩, r1, e1, h⟩ := V.bind_ok h
          have envb : EnvB s.nvars env := calleeEnv_bounded wf c.args c.argRegs (fun r m => (F.arg m).1) henv
          obtain ⟨ρ3, c3, sem, bd⟩ := seval_sound E env e e1 Hafter wafter (envb.mono (Nat.le_add_right _ _))
          have ag3 : Agree s.nvars ρ ρ3 := Agree.trans (Nat.le_add_right _ _) ag c3.agree
          have henv3 : semEnv ctx s0 ρ3 env = c.env (afterCall p q i st) := by
            rw [← semEnv_agree envb ag3]
            exact semEnv_calleeEnv H.entry
              (fun r m => by rw [s1reg r (F.arg m).2]; exact H.reg r (F.arg m).1)
              (fun b0 l0 hm k hk => by
                obtain ⟨fit, apart⟩ := E.regionAt hm
                rw [s1mem _ (by omega)]
                exact H.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
                  (E.region_notOut hm (Nat.le_add_right _ _) (by omega)))
              c.args c.argRegs (fun r m => m) henv
          rw [henv3] at sem
          have val := pret e hret'
          have pos : c.retReg < c.regs := (retReg_spec c).1
          have hnew : ev ρ3 (Lin.var (s.nvars + c.retReg)) = s2.reg c.retReg := by
            rw [ev_var, ← c3.agree (s.nvars + c.retReg) (by simp only [Sym.afterCall]; omega)]
            exact afterRho_new c.regs s.nvars ρ s2 (r := c.retReg) pos
          have bvar : bounded s3.nvars (Lin.var (s.nvars + c.retReg)) :=
            bounded_var (Nat.lt_of_lt_of_le (show s.nvars + c.retReg < s.nvars + c.regs by omega) c3.mono)
          cases res with
          | list _ => exact (refuse_ok h).elim
          | tail call =>
            simp only at h
            have := V.pure_ok h
            injection this with h1 _
            subst h1
            have hv : SFact.holds ctx s0 ρ3 (.value call (Lin.var (s.nvars + c.retReg))) := by
              show CallValue ctx s0 ρ3 call (.int (ev ρ3 (Lin.var (s.nvars + c.retReg))))
              rw [hnew]
              exact (sem _).mp val
            exact ⟨hrip, ρ3, ag3, Nat.le_trans (Nat.le_add_right _ _) c3.mono, c3.holds.withSpec _ hv, c3.wf.withSpec _ ⟨bd, bvar⟩⟩
          | val v =>
            cases v with
            | region _ => exact (refuse_ok h).elim
            | bool _ => exact (refuse_ok h).elim
            | lin v =>
              simp only at h
              have := V.pure_ok h
              injection this with h1 _
              subst h1
              have same := Value.unique sem val
              simp only [semv] at same
              injection same with same
              exact ⟨hrip, ρ3, ag3, Nat.le_trans (Nat.le_add_right _ _) c3.mono,
                c3.holds.more _ (all_two (by rw [holds_iff, ev_sub, hnew]; omega) (by rw [holds_iff, ev_sub, hnew]; omega)),
                c3.wf.more _ (all_two (bounded_sub bd bvar) (bounded_sub bvar bd))⟩

end Ode
