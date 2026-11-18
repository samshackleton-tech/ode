import SoundLin
/-!
# Why the verifier's yes is right, 2: what a state on symbols says of a state of the machine

`Holds` is the tie between what the verifier holds at a point of a path (`Sym`) and a state of the machine
there, the unknowns being the whole numbers `ρ`. `WF` says that the verifier's state speaks only of unknowns
in use, so that an unknown brought into use later can be given any value.
-/
namespace Ode
open Arithmetic

/-! ## Unknowns in use -/

def bounded (n : Nat) (r : Row) : Prop := r.coeff.length ≤ n

theorem dot_agree (cs : List Int) (ρ ρ' : Nat → Int) (h : ∀ k, k < cs.length → ρ k = ρ' k) : dot cs ρ = dot cs ρ' := by
  induction cs generalizing ρ ρ' with
  | nil => rfl
  | cons c cs ih =>
    simp only [dot]
    rw [h 0 (by simp), ih (fun n => ρ (n + 1)) (fun n => ρ' (n + 1)) (fun k hk => h (k + 1) (by simp; omega))]

theorem ev_agree {n : Nat} {r : Row} {ρ ρ' : Nat → Int} (hb : bounded n r) (h : ∀ k, k < n → ρ k = ρ' k) : ev ρ r = ev ρ' r := by
  unfold ev
  rw [dot_agree r.coeff ρ ρ' (fun k hk => h k (Nat.lt_of_lt_of_le hk hb))]

theorem strip_length (cs : List Int) : (Lin.strip cs).length ≤ cs.length := by
  induction cs with
  | nil => simp [Lin.strip]
  | cons c cs ih =>
    unfold Lin.strip
    split
    next => split <;> simp
    next d ds h => rw [h] at ih; simp at ih ⊢; omega

theorem sum_length (xs ys : List Int) (n : Nat) (hx : xs.length ≤ n) (hy : ys.length ≤ n) : (sum xs ys).length ≤ n := by
  induction xs generalizing ys n with
  | nil => simpa [sum] using hy
  | cons x xs ih =>
    cases ys with
    | nil => simpa [sum] using hx
    | cons y ys =>
      simp only [sum, List.length_cons] at hx hy ⊢
      have := ih ys (n - 1) (by omega) (by omega)
      omega

theorem scale_length (k : Int) (cs : List Int) : (scale k cs).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [scale, ih]

theorem bounded_const (n : Nat) (k : Int) : bounded n (Lin.const k) := by simp [bounded, Lin.const]
theorem bounded_var {n x : Nat} (h : x < n) : bounded n (Lin.var x) := by simp [bounded, Lin.var]; omega
theorem bounded_add {n : Nat} {a b : Row} (ha : bounded n a) (hb : bounded n b) : bounded n (Lin.add a b) :=
  Nat.le_trans (strip_length _) (sum_length _ _ n ha hb)
theorem bounded_scale {n : Nat} {a : Row} (k : Int) (ha : bounded n a) : bounded n (Lin.scale k a) :=
  Nat.le_trans (strip_length _) (by rw [scale_length]; exact ha)
theorem bounded_sub {n : Nat} {a b : Row} (ha : bounded n a) (hb : bounded n b) : bounded n (Lin.sub a b) :=
  bounded_add ha (bounded_scale _ hb)
theorem bounded_mono {n m : Nat} {a : Row} (h : n ≤ m) (ha : bounded n a) : bounded m a := Nat.le_trans ha h

theorem bounded_signed {n : Nat} {a : Row} (ha : bounded n a) : bounded n (signed a) := by
  unfold signed
  split
  next => split
          · exact bounded_const _ _
          · exact ha
  next => exact ha

def Flag.bounded (n : Nat) : Flag → Prop
  | .unknown => True
  | .equal a b => Ode.bounded n a ∧ Ode.bounded n b
  | .below a b => Ode.bounded n a ∧ Ode.bounded n b

def SVal.bounded (n : Nat) : SVal → Prop
  | .lin r => Ode.bounded n r
  | _ => True

def SCall.bounded (n : Nat) (c : SCall) : Prop := ∀ v ∈ c.args, v.bounded n

def SFact.bounded (n : Nat) : SFact → Prop
  | .same a b => a.bounded n ∧ b.bounded n
  | .value c v => c.bounded n ∧ Ode.bounded n v

/-- The verifier's state speaks only of unknowns in use. -/
structure WF (s : Sym) : Prop where
  base : 16 ≤ s.nvars
  reg : ∀ r, r < 16 → bounded s.nvars (s.reg r)
  zf : s.zf.bounded s.nvars
  cf : s.cf.bounded s.nvars
  frame : ∀ o v, (o, v) ∈ s.frame → bounded s.nvars v
  facts : ∀ f ∈ s.facts, bounded s.nvars f
  bytes : ∀ v r o, (v, r, o) ∈ s.bytes → v < s.nvars ∧ bounded s.nvars o
  spec : ∀ f ∈ s.spec, f.bounded s.nvars

/-! ## What the verifier's state says -/

/-- The bytes of a run given, as memory held them at entry. -/
def runBytes (s0 : State) (base len : Nat) : List Nat := (List.range (s0.reg len)).map fun k => s0.mem (s0.reg base + k)

/-- A value of the specification on symbols, as a value. -/
def semv (ctx : Ctx) (s0 : State) (ρ : Nat → Int) : SVal → Val
  | .lin r => .int (ev ρ r)
  | .region k =>
    match ctx.contract.regions[k]? with
    | some (base, len) => .bytes (runBytes s0 base len)
    | none => .bytes []
  | .bool b => .bool b

/-- The use of a definition has the value `x`. -/
def CallValue (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (c : SCall) (x : Val) : Prop :=
  match findDef ctx.defs c.f with
  | some d => Value ctx.defs (d.params.zip (c.args.map (semv ctx s0 ρ))) d.body x
  | none => False

def SFact.holds (ctx : Ctx) (s0 : State) (ρ : Nat → Int) : SFact → Prop
  | .same a b => ∀ x, CallValue ctx s0 ρ a x ↔ CallValue ctx s0 ρ b x
  | .value c v => CallValue ctx s0 ρ c (.int (ev ρ v))

def Flag.holds (ρ : Nat → Int) (set : Bool) : Flag → Prop
  | .unknown => True
  | .equal a b => set = decide (ev ρ a = ev ρ b)
  | .below a b => set = decide (ev ρ a < ev ρ b)

/-- What the verifier holds (`s`) is so of the machine's state `st`, the unknowns being `ρ`, and `s0` the
state at the function's entry. -/
structure Holds (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (s : Sym) (st : State) : Prop where
  entry : ∀ r, r < 16 → ρ r = s0.reg r
  reg : ∀ r, r < 16 → (st.reg r : Int) = ev ρ (s.reg r)
  small : ∀ r, st.reg r < M64
  zf : s.zf.holds ρ st.zf
  cf : s.cf.holds ρ st.cf
  frame : ∀ o v, (o, v) ∈ s.frame →
    -(ctx.contract.stack : Int) ≤ o ∧ o + 8 ≤ 0 ∧ (load st.mem ((s0.reg RSP : Int) + o).toNat 8 : Int) = ev ρ v
  facts : ∀ f ∈ s.facts, f.holds ρ
  bytes : ∀ v r o, (v, r, o) ∈ s.bytes → ∃ base len, ctx.contract.regions[r]? = some (base, len) ∧
    0 ≤ ev ρ o ∧ ev ρ o < s0.reg len ∧ ρ v = s0.mem (s0.reg base + (ev ρ o).toNat)
  spec : ∀ f ∈ s.spec, f.holds ctx s0 ρ
  mem : ∀ a, ctx.contract.inFrame s0 a = false → ctx.contract.inOut s0 a = false → st.mem a = s0.mem a

/-- The unknowns in use keep their values. -/
def Agree (n : Nat) (ρ ρ' : Nat → Int) : Prop := ∀ k, k < n → ρ k = ρ' k

theorem Agree.refl (n : Nat) (ρ : Nat → Int) : Agree n ρ ρ := fun _ _ => rfl
theorem Agree.trans {n m : Nat} {ρ ρ' ρ'' : Nat → Int} (h : n ≤ m) (a : Agree n ρ ρ') (b : Agree m ρ' ρ'') : Agree n ρ ρ'' :=
  fun k hk => (a k hk).trans (b k (Nat.lt_of_lt_of_le hk h))
theorem Agree.mono {n m : Nat} {ρ ρ' : Nat → Int} (h : n ≤ m) (a : Agree m ρ ρ') : Agree n ρ ρ' :=
  fun k hk => a k (Nat.lt_of_lt_of_le hk h)

theorem semv_agree {ctx : Ctx} {s0 : State} {n : Nat} {ρ ρ' : Nat → Int} {v : SVal} (hb : v.bounded n) (a : Agree n ρ ρ') :
    semv ctx s0 ρ v = semv ctx s0 ρ' v := by
  cases v with
  | lin r => simp only [semv]; rw [ev_agree hb a]
  | region k => rfl
  | bool b => rfl

theorem CallValue_agree {ctx : Ctx} {s0 : State} {n : Nat} {ρ ρ' : Nat → Int} {c : SCall} (hb : c.bounded n) (a : Agree n ρ ρ') (x : Val) :
    CallValue ctx s0 ρ c x ↔ CallValue ctx s0 ρ' c x := by
  unfold CallValue
  have : c.args.map (semv ctx s0 ρ) = c.args.map (semv ctx s0 ρ') :=
    List.map_congr_left fun v hv => semv_agree (hb v hv) a
  rw [this]

theorem SFact.holds_agree {ctx : Ctx} {s0 : State} {n : Nat} {ρ ρ' : Nat → Int} {f : SFact} (hb : f.bounded n) (a : Agree n ρ ρ')
    (h : f.holds ctx s0 ρ) : f.holds ctx s0 ρ' := by
  cases f with
  | same c c' =>
    intro x
    rw [← CallValue_agree hb.1 a x, ← CallValue_agree hb.2 a x]
    exact h x
  | value c v =>
    simp only [SFact.holds] at h ⊢
    rw [← CallValue_agree hb.1 a, ← ev_agree hb.2 a]
    exact h

theorem Flag.holds_agree {n : Nat} {ρ ρ' : Nat → Int} {f : Flag} {set : Bool} (hb : f.bounded n) (a : Agree n ρ ρ')
    (h : f.holds ρ set) : f.holds ρ' set := by
  cases f with
  | unknown => trivial
  | equal x y => simp only [Flag.holds] at h ⊢; rw [← ev_agree hb.1 a, ← ev_agree hb.2 a]; exact h
  | below x y => simp only [Flag.holds] at h ⊢; rw [← ev_agree hb.1 a, ← ev_agree hb.2 a]; exact h

/-- What holds, holds whatever values the unknowns not yet in use are given. -/
theorem Holds.agree {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {s : Sym} {st : State}
    (h : Holds ctx s0 ρ s st) (wf : WF s) (a : Agree s.nvars ρ ρ') : Holds ctx s0 ρ' s st where
  entry r hr := (a r (Nat.lt_of_lt_of_le hr wf.base)).symm.trans (h.entry r hr)
  reg r hr := (h.reg r hr).trans (ev_agree (wf.reg r hr) a)
  small := h.small
  zf := Flag.holds_agree wf.zf a h.zf
  cf := Flag.holds_agree wf.cf a h.cf
  frame o v m := by
    obtain ⟨h1, h2, h3⟩ := h.frame o v m
    exact ⟨h1, h2, h3.trans (ev_agree (wf.frame o v m) a)⟩
  facts f m := by
    have := h.facts f m
    rw [holds_iff] at this ⊢
    rw [← ev_agree (wf.facts f m) a]; exact this
  bytes v r o m := by
    obtain ⟨base, len, h1, h2, h3, h4⟩ := h.bytes v r o m
    have e := ev_agree (wf.bytes v r o m).2 a
    refine ⟨base, len, h1, ?_, ?_, ?_⟩
    · rw [← e]; exact h2
    · rw [← e]; exact h3
    · rw [← e, ← a v (wf.bytes v r o m).1]; exact h4
  spec f m := SFact.holds_agree (wf.spec f m) a (h.spec f m)
  mem := h.mem

/-- More unknowns in use: the verifier's state still speaks only of unknowns in use. -/
theorem Flag.bounded_mono {n m : Nat} {f : Flag} (h : n ≤ m) (hb : f.bounded n) : f.bounded m := by
  cases f with
  | unknown => trivial
  | equal x y => exact ⟨Ode.bounded_mono h hb.1, Ode.bounded_mono h hb.2⟩
  | below x y => exact ⟨Ode.bounded_mono h hb.1, Ode.bounded_mono h hb.2⟩

theorem SVal.bounded_mono {n m : Nat} {v : SVal} (h : n ≤ m) (hb : v.bounded n) : v.bounded m := by
  cases v with
  | lin r => exact Ode.bounded_mono h hb
  | region k => trivial
  | bool b => trivial

theorem SCall.bounded_mono {n m : Nat} {c : SCall} (h : n ≤ m) (hb : c.bounded n) : c.bounded m :=
  fun v hv => SVal.bounded_mono h (hb v hv)

theorem SFact.bounded_mono {n m : Nat} {f : SFact} (h : n ≤ m) (hb : f.bounded n) : f.bounded m := by
  cases f with
  | same a b => exact ⟨SCall.bounded_mono h hb.1, SCall.bounded_mono h hb.2⟩
  | value c v => exact ⟨SCall.bounded_mono h hb.1, Ode.bounded_mono h hb.2⟩

/-! ## Memory -/

theorem load_lt (mem : Nat → Nat) (a n : Nat) : load mem a n < 256 ^ n := by
  induction n generalizing a with
  | zero => simp [load]
  | succ n ih =>
    simp only [load]
    have := ih (a + 1)
    have h256 : mem a % 256 < 256 := Nat.mod_lt _ (by decide)
    rw [Nat.pow_succ]
    omega

theorem store_other (mem : Nat → Nat) (a v n x : Nat) (h : x < a ∨ a + n ≤ x) : store mem a v n x = mem x := by
  induction n generalizing mem a v with
  | zero => rfl
  | succ n ih =>
    simp only [store]
    rw [ih _ _ _ (by omega)]
    split
    · omega
    · rfl

theorem load_congr (mem mem' : Nat → Nat) (a n : Nat) (h : ∀ x, a ≤ x → x < a + n → mem x = mem' x) : load mem a n = load mem' a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [load]
    rw [h a (by omega) (by omega), ih (a + 1) (fun x h1 h2 => h x (by omega) (by omega))]

theorem load_store_other (mem : Nat → Nat) (a v n b k : Nat) (h : b + k ≤ a ∨ a + n ≤ b) : load (store mem a v n) b k = load mem b k :=
  load_congr _ _ _ _ fun x h1 h2 => store_other mem a v n x (by omega)

theorem load_store_same (mem : Nat → Nat) (a v n : Nat) (h : v < 256 ^ n) : load (store mem a v n) a n = v := by
  induction n generalizing mem a v with
  | zero => simp at h; simp [load, h]
  | succ n ih =>
    simp only [load, store]
    rw [store_other _ _ _ _ _ (by omega)]
    rw [ih _ _ _ (by rw [Nat.pow_succ] at h; omega)]
    simp only [ite_true]
    omega

theorem allowed_of (p : Nat → Bool) (a n : Nat) (h : ∀ x, a ≤ x → x < a + n → p x = true) : allowed p a n = true := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [allowed, Bool.and_eq_true]
    exact ⟨h a (by omega) (by omega), ih (a + 1) fun x h1 h2 => h x (by omega) (by omega)⟩

end Ode
