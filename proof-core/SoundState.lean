import SoundWord
import SoundCode
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
  | .neq r => Ode.bounded n r

def Key.wf (n t : Nat) : Key → Prop
  | .num r => bounded n r
  | .counter r => bounded n r
  | .words ids => ∀ i ∈ ids, i < t
  | .lane _ _ _ => True
  | .span _ off len => bounded n off ∧ bounded n len
  | .use h => h < n

theorem Tab.size_eq_length (t : Tab) : t.size = t.list.length := by
  simp [Tab.size, Tab.list]

/-- A serialized record layout matches `fvs` against the word values `ws`: each `.words` field has `n`
words, each `.bytes` field has `n` bytes (`n % 4 = 0`) equal to `wordBytes` of `n / 4` words, and each
`.u64` field is an integer `< bd` split into low/high 32-bit words `lo + 2^32 * hi`. -/
def RecFieldsHolds : List RecField → List Nat → List (String × Val) → Prop
  | [], [], [] => True
  | .words fn n :: fs, ws, (x, .list vs) :: rest =>
    x = fn ∧ n ≤ ws.length ∧ vs = (ws.take n).map Val.word ∧ RecFieldsHolds fs (ws.drop n) rest
  | .bytes fn n :: fs, ws, (x, .list vs) :: rest =>
    x = fn ∧ n % 4 = 0 ∧ n / 4 ≤ ws.length ∧ vs = (ws.take (n / 4)).flatMap (fun w =>
      [.int (w % 256 : Nat), .int (w / 256 % 256 : Nat), .int (w / 65536 % 256 : Nat), .int (w / 16777216 % 256 : Nat)]) ∧
    RecFieldsHolds fs (ws.drop (n / 4)) rest
  | .u64 fn bd :: fs, lo :: hi :: ws, (x, .int v) :: rest =>
    x = fn ∧ 0 ≤ v ∧ v < (bd : Int) ∧ bd ≤ M64 ∧ v = (lo : Int) + W32i * (hi : Int) ∧
    lo < W32 ∧ hi < W32 ∧ RecFieldsHolds fs ws rest
  | _, _, _ => False

/-- What is known of a number that is no row speaks only of unknowns in use (`n` of them) and of terms of
the table (`t` of them). -/
def Known.wf (n t : Nat) : Known → Prop
  | .load v _ _ => v < n
  | .or v x y => v < n ∧ bounded n x ∧ bounded n y
  | .held _ keys ids => (∀ k ∈ keys, k.wf n t) ∧ ∀ i ∈ ids, i < t
  | .heldB _ keys ids => (∀ k ∈ keys, k.wf n t) ∧ ∀ i ∈ ids, i < t
  | .div x _ q => bounded n x ∧ q + 1 < n
  | .block _ _ off vs => bounded n off ∧ ∀ v ∈ vs, v < n
  | .use _ keys h => (∀ k ∈ keys, k.wf n t) ∧ h < n
  | .record u _ ids => u < n ∧ ∀ i ∈ ids, i < t
  | .word32 _ hi => hi ≤ n
  | .termVal v id => v < n ∧ id < t

/-- The table of words is in order: a term stands after the terms it is made of; the rows of its terms
speak of unknowns in use; each known vector register has four or sixteen lanes in the table. -/
structure WordsWF (s : Sym) : Prop where
  table : WFT s.terms
  atoms : ∀ (j : Nat) (r : Row), s.terms[j]? = some (Node.atom r) → bounded s.nvars r
  vec : ∀ x ids, s.vec.lookup x = some ids → (ids.length = 4 ∨ ids.length = 16) ∧ ∀ i ∈ ids, i < s.terms.length
  rotrs : ∀ (j a n : Nat), s.terms[j]? = some (Node.rotr a n) → n ≤ 32
  wrote : ∀ w j i, (w, j, i) ∈ s.wroteW → i < s.terms.length
  spill : ∀ off ids, (off, ids) ∈ s.spill → bounded s.nvars off ∧ ids.length = 16 ∧ ∀ i ∈ ids, i < s.terms.length

/-- A machine has sixteen general registers at least. -/
theorem Ctx.nreg_ge (ctx : Ctx) : 16 ≤ ctx.nreg := by
  unfold Ctx.nreg Contract.regs
  split <;> decide

/-- A register of the first sixteen is a register of the function's machine. -/
theorem Ctx.lt_nreg (ctx : Ctx) {r : Nat} (h : r < 16) : r < ctx.nreg := Nat.lt_of_lt_of_le h ctx.nreg_ge

theorem Ctx.rsp_lt (ctx : Ctx) : RSP < ctx.nreg := ctx.lt_nreg (by decide)

/-- The verifier's state speaks only of unknowns in use. (`ctx` is here for the count of the machine's
registers alone.) -/
structure WF (ctx : Ctx) (s : Sym) : Prop where
  base : ctx.nreg + 1 ≤ s.nvars           -- (the registers at entry, and where the file's data lies)
  reg : ∀ r, r < ctx.nreg → bounded s.nvars (s.reg r)
  zf : s.zf.bounded s.nvars
  cf : s.cf.bounded s.nvars
  frame : ∀ o v, (o, v) ∈ s.frame → bounded s.nvars v
  frameW : ∀ o i, (o, i) ∈ s.frameW → i < s.terms.length
  facts : ∀ f ∈ s.facts, bounded s.nvars f
  bytes : ∀ v r o, (v, r, o) ∈ s.bytes → v < s.nvars ∧ bounded s.nvars o
  spec : ∀ f ∈ s.spec, f.bounded s.nvars
  wrote : ∀ w o x, (w, o, x) ∈ s.wrote → bounded s.nvars o ∧ bounded s.nvars x
  words : WordsWF s
  known : ∀ k ∈ s.known, k.wf s.nvars s.terms.length
  range : ∀ rg, s.range = some rg → bounded s.nvars rg.lo ∧ ∀ v ∈ rg.args, v.bounded s.nvars

/-- The unknowns of the registers at entry are in use. -/
theorem WF.regs {ctx : Ctx} {s : Sym} (wf : WF ctx s) : ctx.nreg ≤ s.nvars := Nat.le_of_succ_le wf.base

/-! ## A contract with no table of addresses -/

theorem tableAt_none {c : Contract} (h : c.lanes = []) (j : Nat) : c.tableAt j = none := by
  unfold Contract.tableAt
  rw [h]
  cases c.fixeds[j]? with
  | none => rfl
  | some x => rfl

theorem tables_nil {c : Contract} (h : c.lanes = []) : c.tables = [] := by
  unfold Contract.tables
  exact List.filterMap_eq_nil_iff.mpr fun j _ => tableAt_none h j

theorem inLane_false {c : Contract} (h : c.lanes = []) (s : State) (a : Nat) : c.inLane s a = false := by
  simp [Contract.inLane, tables_nil h]

/-- An address is in the read-only data of a file: the file's number, and where in its data the address is. -/
theorem inPieces_iff {pieces : List Piece} {s : State} {a : Nat} :
    inPieces pieces s a = true ↔ ∃ k pc, pieces[k]? = some pc ∧ s.data k ≤ a ∧ a < s.data k + pc.bytes.length := by
  unfold inPieces
  rw [List.any_eq_true]
  constructor
  · intro h
    obtain ⟨⟨pc, k⟩, m, h⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨k, pc, List.mem_zipIdx_iff_getElem?.mp m, h.1, h.2⟩
  · intro h
    obtain ⟨k, pc, e, h1, h2⟩ := h
    exact ⟨(pc, k), List.mem_zipIdx_iff_getElem?.mpr e, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, h2⟩⟩

/-- Where the files' data lies is all that `inPieces` reads of a state. -/
theorem inPieces_data {pieces : List Piece} {s s' : State} (h : s'.data = s.data) (a : Nat) : inPieces pieces s' a = inPieces pieces s a := by
  unfold inPieces
  rw [h]

theorem inPieces_nil (s : State) (a : Nat) : inPieces [] s a = false := rfl

/-- What a function may read: what its contract lets it read whatever the program's read-only data is, and
that data. -/
theorem perm_read_split {c : Contract} {pieces : List Piece} {s : State} {a : Nat} :
    (c.perm pieces s).read a = ((c.perm [] s).read a || inPieces pieces s a) := by
  simp only [Contract.perm, inPieces_nil, Bool.or_false]

theorem perm_read_pieces {c : Contract} {pieces : List Piece} {s : State} {a : Nat} (h : inPieces pieces s a = true) :
    (c.perm pieces s).read a = true := by
  simp only [Contract.perm, h, Bool.or_true]

theorem lanesEnv_nil {c : Contract} (h : c.lanes = []) (s : State) : c.lanesEnv s = [] := by
  simp [Contract.lanesEnv, tables_nil h]

theorem envW_plain {c : Contract} (h : c.lanes = []) (s : State) : c.envW s = envWIn c s c.args c.argRegs := by
  simp [Contract.envW, lanesEnv_nil h]

/-- A table of the contract is one of its tables. -/
theorem tableAt_mem {c : Contract} {j : Nat} {t : String × Nat × Nat × Nat} (h : c.tableAt j = some t) : t ∈ c.tables := by
  unfold Contract.tables
  refine List.mem_filterMap.mpr ⟨j, List.mem_range.mpr ?_, h⟩
  unfold Contract.tableAt at h
  cases hj : c.fixeds[j]? with
  | none => rw [hj] at h; cases h
  | some x => exact (List.getElem?_eq_some_iff.mp hj).1

/-- A table is the fixed run of its number: its register, and an eighth of its bytes as its count. -/
theorem tableAt_fixed {c : Contract} {j : Nat} {x : String} {r count l : Nat} (h : c.tableAt j = some (x, r, count, l)) :
    ∃ n, c.fixeds[j]? = some (x, r, n) ∧ count = n / 8 := by
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
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨n, rfl, rfl⟩

/-! ## What the verifier's state says -/

/-- Word `k` of the run of words of number `j` (the runs of a fixed count given to read, then those given to
read and to write, then the runs of bytes with a length), as memory held it at entry. -/
def inpOf (ctx : Ctx) (s0 : State) (j k : Nat) : Nat :=
  match ctx.contract.wordRuns[j]? with
  | some (_, r, _) => load s0.mem (s0.reg r + 4 * k) 4
  | none => 0

/-- A run of a fixed count, or one given to read and write, has among the runs of words the number it has
among those two. -/
theorem wordRuns_of {c : Contract} {j : Nat} {x : String × Nat × Nat} (h : (c.fixeds ++ c.inouts)[j]? = some x) :
    c.wordRuns[j]? = some x := by
  unfold Contract.wordRuns
  have hj := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map]; simp only [List.length_append] at hj; omega)]
  rw [List.getElem?_append_left hj]
  exact h

theorem wordRuns_of_region {c : Contract} {k : Nat} {r l : Nat} (h : c.regions[k]? = some (r, l)) :
    c.wordRuns[c.fixeds.length + c.inouts.length + k]? = some ("", r, 0) := by
  unfold Contract.wordRuns
  have hk := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map]; omega)]
  rw [List.getElem?_append_right (by simp only [List.length_append]; omega)]
  simp only [List.length_append, Nat.add_sub_cancel_left, List.getElem?_map, h, Option.map_some]

theorem wordRuns_of_valArray {c : Contract} {k : Nat} {x : String} {r l ch el : Nat}
    (h : c.valArrays[k]? = some (x, r, l, ch, el)) :
    c.wordRuns[c.fixeds.length + c.inouts.length + c.regions.length + k]? = some (x, r, 0) := by
  unfold Contract.wordRuns
  rw [List.getElem?_append_right (by simp only [List.length_append, List.length_map]; omega)]
  simp only [List.length_append, List.length_map, Nat.add_sub_cancel_left, List.getElem?_map, h, Option.map_some]

/-- Known words agree with the machine's vector registers and memory. -/
structure WordFacts (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (terms : List Node)
    (vectors : List (Nat × List Nat)) (untouched : List Nat) (written : List (Nat × Nat × Nat))
    (saved : List (Row × List Nat)) (reg : Nat → Nat → Nat) (mem : Nat → Byte) : Prop where
  vec : ∀ x ids, vectors.lookup x = some ids → ∀ k, k < ids.length → reg x k = den (inpOf ctx s0) ρ terms (ids.getD k 0)
  intact : ∀ w ∈ untouched, ∀ x r n, ctx.contract.outs[w]? = some (x, r, n) → ∀ k, k < n → mem (s0.reg r + k) = s0.mem (s0.reg r + k)
  wrote : ∀ w j i, (w, j, i) ∈ written → ∀ x r n, ctx.contract.outs[w]? = some (x, r, n) →
    4 * j + 4 ≤ n ∧ ∀ b, b < 4 → mem (s0.reg r + 4 * j + b) = den (inpOf ctx s0) ρ terms i / 256 ^ b % 256
  spill : ∀ off ids, (off, ids) ∈ saved → 0 ≤ (s0.reg RSP : Int) + ev ρ off ∧ ∀ k, k < ids.length →
    load mem (((s0.reg RSP : Int) + ev ρ off).toNat + 4 * k) 4 = den (inpOf ctx s0) ρ terms (ids.getD k 0)

abbrev VecOk (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (s : Sym) (st : State) : Prop :=
  WordFacts ctx s0 ρ s.terms s.vec s.intact s.wroteW s.spill st.vec st.mem

/-- The four bytes of each word, the lowest first (as `ofWords` of the account gives them). -/
def wordBytes : List Nat → List Val
  | [] => []
  | w :: rest => .int (w % 256 : Nat) :: .int (w / 256 % 256 : Nat) :: .int (w / 65536 % 256 : Nat) :: .int (w / 16777216 % 256 : Nat) :: wordBytes rest

/-- What a thing a definition is used with stands for: a value of the account. -/
noncomputable def Key.val (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (T : List Node) : Key → Val
  | .num r => .int (ev ρ r)
  | .counter r => .counter ((ev ρ r).toNat % 2 ^ 64)
  | .words ids => .list (ids.map fun i => Val.word (den (inpOf ctx s0) ρ T i))
  | .lane j c l =>
    match ctx.contract.tableAt j with
    | some (_, r, _, _) => laneBlocks s0.mem (lanePtr s0 r (c / 8)) (s0.reg l)
    | none => .list []
  | .span r off len => .list ((List.range (ev ρ len).toNat).map fun k => Val.int (s0.mem (s0.reg r + (ev ρ off).toNat + k)))
  | .use h => Val.decode (ρ h).toNat      -- (the unknown of the use's number stands for what the use gives: SoundCode.lean)

/-- What is known of a number that is no row is so. -/
def Known.holds (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (T : List Node) : Known → Prop
  | .load v j c => ∃ x r n, ctx.contract.fixeds[j]? = some (x, r, n) ∧ c + 8 ≤ n ∧ ρ v = (Ode.load s0.mem (s0.reg r + c) 8 : Nat)
  | .or v x y => 0 ≤ ev ρ x ∧ 0 ≤ ev ρ y ∧ ρ v = (((ev ρ x).toNat ||| (ev ρ y).toNat : Nat) : Int)
  | .held f keys ids => ctx.contract.preVals ctx.defs s0 → ∃ d, findDef ctx.defs f = some d ∧ d.params.length = keys.length ∧
      Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ T))) d.body (.list (ids.map fun i => Val.word (den (inpOf ctx s0) ρ T i)))
  | .heldB f keys ids => ctx.contract.preVals ctx.defs s0 → ∃ d, findDef ctx.defs f = some d ∧ d.params.length = keys.length ∧
      Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ T))) d.body (.list (wordBytes (ids.map fun i => den (inpOf ctx s0) ρ T i)))
  | .div x m q => 0 < m → ρ q = ev ρ x / m ∧ ρ (q + 1) = ev ρ x % m
  | .block j c off vs => ∃ x r count l, ctx.contract.tableAt j = some (x, r, count, l) ∧ c % 8 = 0 ∧ c / 8 < count ∧
      0 ≤ ev ρ off ∧ ev ρ off + 64 ≤ 64 * (s0.reg l : Int) ∧ vs.length = 16 ∧
      ∀ w, w < 16 → ρ (vs.getD w 0) = (Ode.load s0.mem (lanePtr s0 r (c / 8) + (ev ρ off).toNat + 4 * w) 4 : Nat)
  | .use f keys h => ctx.contract.preVals ctx.defs s0 → ∃ d, findDef ctx.defs f = some d ∧ d.params.length = keys.length ∧
      Value ctx.defs (d.params.zip (keys.map (Key.val ctx s0 ρ T))) d.body (Val.decode (ρ h).toNat)
  | .record u fields ids => ctx.contract.preVals ctx.defs s0 → ∃ fvs, Val.decode (ρ u).toNat = .record fvs ∧
      RecFieldsHolds fields (ids.map fun i => den (inpOf ctx s0) ρ T i) fvs
  | .word32 lo hi => ∀ v, lo ≤ v → v < hi → 0 ≤ ρ v ∧ ρ v < W32i
  | .termVal v id => ρ v = (den (inpOf ctx s0) ρ T id : Int)

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
  | .neq r => ev ρ r ≠ 0

def Flag.holds (ρ : Nat → Int) (set : Bool) : Flag → Prop
  | .unknown => True
  | .equal a b => set = decide (ev ρ a = ev ρ b)
  | .below a b => set = decide (ev ρ a < ev ρ b)

/-- What a place has said a loop has written is so of memory: the run is one given to write; the definition
is a list made thing by thing, of no more things than the run has places; and each place in the prefix
(`0..lo`) or suffix (`lo..hi`) holds the list's thing there. -/
def RangeHolds (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (rg : RangeF) (mem : Nat → Byte) : Prop :=
  ∃ name r n params x b hi, ctx.contract.outs[rg.w]? = some (name, r, n) ∧
    eachOf ctx rg.f rg.args.length = some (params, x, b, hi) ∧ hi ≤ n ∧ 0 ≤ ev ρ rg.lo ∧
    ∀ j : Nat, (if rg.fromStart then (j : Int) < ev ρ rg.lo else ev ρ rg.lo ≤ j) → j < hi →
      Value ctx.defs ((x, .int j) :: params.zip (rg.args.map (semv ctx s0 ρ))) b (.int (mem (s0.reg r + j)))

/-- Where the read-only data of the function's own file lies, `s0` being the state at entry. -/
def Ctx.own (ctx : Ctx) (s0 : State) : Nat := s0.data (ctx.piece.getD 0)

/-- Where the function's own file has read-only data: the file's number, and its data among the program's. -/
theorem Ctx.data_piece {ctx : Ctx} (hd : ctx.data ≠ []) :
    ∃ k pc, ctx.piece = some k ∧ ctx.pieces[k]? = some pc ∧ ctx.data = pc.bytes := by
  cases hp : ctx.piece with
  | none => exact absurd (by simp only [Ctx.data, hp]) hd
  | some k =>
    cases hq : ctx.pieces[k]? with
    | none => exact absurd (by simp only [Ctx.data, hp, hq]) hd
    | some pc => exact ⟨k, pc, rfl, hq, by simp only [Ctx.data, hp, hq]⟩

theorem Ctx.own_eq {ctx : Ctx} {k : Nat} (h : ctx.piece = some k) (s0 : State) : ctx.own s0 = s0.data k := by
  unfold Ctx.own
  rw [h]
  rfl

/-- What the verifier holds (`s`) is so of the machine's state `st`, the unknowns being `ρ`, and `s0` the
state at the function's entry. -/
structure Holds (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (s : Sym) (st : State) : Prop where
  entry : ∀ r, r < ctx.nreg → ρ r = s0.reg r
  data : ρ (dataVar ctx) = ctx.own s0 ∧ st.data = s0.data      -- the unknown after the registers' is where the data of the function's own file lies; every file's lies where it did
  reg : ∀ r, r < ctx.nreg → (st.reg r : Int) = ev ρ (s.reg r)
  small : ∀ r, st.reg r < M64
  zf : s.zf.holds ρ st.zf
  cf : s.cf.holds ρ st.cf
  frame : ∀ o v, (o, v) ∈ s.frame →
    -(ctx.contract.stackAt s0 : Int) ≤ o ∧ o + 8 ≤ 0 ∧ (load st.mem ((s0.reg RSP : Int) + o).toNat 8 : Int) = ev ρ v
  frameW : ∀ o i, (o, i) ∈ s.frameW →
    -(ctx.contract.stackAt s0 : Int) ≤ o ∧ o + 4 ≤ 0 ∧
    load st.mem ((s0.reg RSP : Int) + o).toNat 4 = den (inpOf ctx s0) ρ s.terms i
  facts : ∀ f ∈ s.facts, f.holds ρ
  bytes : ∀ v r o, (v, r, o) ∈ s.bytes → ∃ base len, ctx.contract.regions[r]? = some (base, len) ∧
    0 ≤ ev ρ o ∧ ev ρ o < s0.reg len ∧ ρ v = s0.mem (s0.reg base + (ev ρ o).toNat)
  spec : ∀ f ∈ s.spec, f.holds ctx s0 ρ
  mem : ∀ a, ctx.contract.inFrame s0 a = false → ctx.contract.inOut s0 a = false → st.mem a = s0.mem a
  wrote : ∀ w o x, (w, o, x) ∈ s.wrote → ∃ name r n, ctx.contract.outs[w]? = some (name, r, n) ∧
    0 ≤ ev ρ o ∧ ev ρ o < n ∧ (st.mem (s0.reg r + (ev ρ o).toNat) : Int) = ev ρ x
  words : VecOk ctx s0 ρ s st
  known : ∀ k ∈ s.known, k.holds ctx s0 ρ s.terms
  range : ∀ rg, s.range = some rg → RangeHolds ctx s0 ρ rg st.mem
  vecIntact : ∀ r ∈ s.vecIntact, st.vec r = s0.vec r

/-- What a called function may read of the program's read-only data, its caller may read: the data lies at
the call where it lay at the caller's entry. -/
theorem read_pieces {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (p q : Program) (i : Instr) {a : Nat} (h : inPieces ctx.pieces (afterCall p q i st) a = true) :
    (ctx.contract.perm ctx.pieces s0).read a = true := by
  rw [inPieces_data (show (afterCall p q i st).data = s0.data from (afterCall_data p q i st).trans H.data.2) a] at h
  exact perm_read_pieces h

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
  | neq r =>
    simp only [SFact.holds] at h ⊢
    rw [← ev_agree hb a]
    exact h

theorem Flag.holds_agree {n : Nat} {ρ ρ' : Nat → Int} {f : Flag} {set : Bool} (hb : f.bounded n) (a : Agree n ρ ρ')
    (h : f.holds ρ set) : f.holds ρ' set := by
  cases f with
  | unknown => trivial
  | equal x y => simp only [Flag.holds] at h ⊢; rw [← ev_agree hb.1 a, ← ev_agree hb.2 a]; exact h
  | below x y => simp only [Flag.holds] at h ⊢; rw [← ev_agree hb.1 a, ← ev_agree hb.2 a]; exact h

theorem WordsWF.mono {s s' : Sym} (W : WordsWF s) (ht : s'.terms = s.terms) (hv : s'.vec = s.vec) (hw : s'.wroteW = s.wroteW)
    (le : s.nvars ≤ s'.nvars)
    (hs : s'.spill = s.spill ∨ s'.spill = [] := by first | exact Or.inl rfl | exact Or.inr rfl) : WordsWF s' :=
  ⟨by rw [ht]; exact W.table, fun j r h => by rw [ht] at h; exact bounded_mono le (W.atoms j r h),
   fun x ids h => by rw [hv] at h; rw [ht]; exact W.vec x ids h, fun j a n h => by rw [ht] at h; exact W.rotrs j a n h,
   fun w j i h => by rw [hw] at h; rw [ht]; exact W.wrote w j i h,
   fun o ids h => by
     rcases hs with e | e
     · rw [e] at h
       obtain ⟨bound, len, lt⟩ := W.spill o ids h
       rw [ht]; exact ⟨bounded_mono le bound, len, lt⟩
     · rw [e] at h; cases h⟩

theorem VecOk.agree {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {s : Sym} {st : State}
    (W : WordsWF s) (a : Agree s.nvars ρ ρ') (h : VecOk ctx s0 ρ s st) : VecOk ctx s0 ρ' s st := by
  refine ⟨?_, h.intact, ?_, ?_⟩
  · intro x ids hx k hk
    obtain ⟨len, lt⟩ := W.vec x ids hx
    have hk' : k < ids.length := by omega
    have e : ids.getD k 0 = ids[k] := by simp [List.getD, List.getElem?_eq_getElem hk']
    rw [h.vec x ids hx k hk]
    refine (den_agree W.table (fun j r hj => (ev_agree (W.atoms j r hj) a).symm) ?_).symm
    rw [e]; exact lt _ (List.getElem_mem hk')
  · intro w j i m x r n ho
    obtain ⟨h1, h2⟩ := h.wrote w j i m x r n ho
    refine ⟨h1, fun b hb => ?_⟩
    rw [h2 b hb, den_agree W.table (fun j r hj => (ev_agree (W.atoms j r hj) a).symm) (W.wrote w j i m)]
  · intro o ids hs
    obtain ⟨bo, _, lt⟩ := W.spill o ids hs
    rw [← ev_agree bo a]
    refine ⟨(h.spill o ids hs).1, fun k hk => ?_⟩
    have eq : ids.getD k 0 = ids[k] := by simp [List.getD, List.getElem?_eq_getElem hk]
    rw [(h.spill o ids hs).2 k hk, eq]
    exact (den_agree W.table (fun j r hj => (ev_agree (W.atoms j r hj) a).symm) (lt _ (List.getElem_mem hk))).symm

/-- A term of the table is the same word under other unknowns that agree on those in use, and in a table
with more terms after it. -/
theorem den_mono {inp : Nat → Nat → Nat} {ρ ρ' : Nat → Int} {T T' : List Node} {n : Nat} (hw : WFT T)
    (ha : ∀ (j : Nat) (r : Row), T[j]? = some (Node.atom r) → bounded n r) (a : Agree n ρ ρ') (e : Ext T T') {i : Nat} (hi : i < T.length) :
    den inp ρ' T' i = den inp ρ T i := by
  rw [den_ext hw e hi]
  exact den_agree hw (fun j r hj => (ev_agree (ha j r hj) a).symm) hi

theorem Key.val_mono {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {T T' : List Node} {n : Nat} {k : Key}
    (wk : k.wf n T.length) (a : Agree n ρ ρ') (hw : WFT T)
    (ha : ∀ (j : Nat) (r : Row), T[j]? = some (Node.atom r) → bounded n r) (e : Ext T T') :
    k.val ctx s0 ρ' T' = k.val ctx s0 ρ T := by
  cases k with
  | num r => simp only [Key.val]; rw [← ev_agree wk a]
  | counter r => simp only [Key.val]; rw [← ev_agree wk a]
  | words ids =>
    simp only [Key.val]
    congr 1
    exact List.map_congr_left fun i hi => by rw [den_mono hw ha a e (wk i hi)]
  | lane j c l => rfl
  | span r off len => simp only [Key.val]; rw [← ev_agree wk.1 a, ← ev_agree wk.2 a]
  | use h => simp only [Key.val]; rw [← a h wk]

/-- What is known of numbers that are no rows stays so under other unknowns that agree on those in use,
and in a table with more terms after it. -/
theorem Known.holds_mono {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {T T' : List Node} {n : Nat} {k : Known}
    (wk : k.wf n T.length) (a : Agree n ρ ρ') (hw : WFT T)
    (ha : ∀ (j : Nat) (r : Row), T[j]? = some (Node.atom r) → bounded n r) (e : Ext T T')
    (h : k.holds ctx s0 ρ T) : k.holds ctx s0 ρ' T' := by
  cases k with
  | load v j c =>
    obtain ⟨x, r, m, h1, h2, h3⟩ := h
    exact ⟨x, r, m, h1, h2, by rw [← a v wk]; exact h3⟩
  | or v x y =>
    obtain ⟨h1, h2, h3⟩ := h
    simp only [Known.holds]
    rw [← ev_agree wk.2.1 a, ← ev_agree wk.2.2 a, ← a v wk.1]
    exact ⟨h1, h2, h3⟩
  | held f keys ids =>
    intro hpv
    obtain ⟨d, h1, h2, h3⟩ := h hpv
    refine ⟨d, h1, h2, ?_⟩
    have ek : keys.map (Key.val ctx s0 ρ' T') = keys.map (Key.val ctx s0 ρ T) :=
      List.map_congr_left fun k hk => Key.val_mono (wk.1 k hk) a hw ha e
    have ei : (ids.map fun i => Val.word (den (inpOf ctx s0) ρ' T' i)) = ids.map fun i => Val.word (den (inpOf ctx s0) ρ T i) :=
      List.map_congr_left fun i hi => by rw [den_mono hw ha a e (wk.2 i hi)]
    rw [ek, ei]; exact h3
  | heldB f keys ids =>
    intro hpv
    obtain ⟨d, h1, h2, h3⟩ := h hpv
    refine ⟨d, h1, h2, ?_⟩
    have ek : keys.map (Key.val ctx s0 ρ' T') = keys.map (Key.val ctx s0 ρ T) :=
      List.map_congr_left fun k hk => Key.val_mono (wk.1 k hk) a hw ha e
    have ei : (ids.map fun i => den (inpOf ctx s0) ρ' T' i) = ids.map fun i => den (inpOf ctx s0) ρ T i :=
      List.map_congr_left fun i hi => by rw [den_mono hw ha a e (wk.2 i hi)]
    rw [ek, ei]; exact h3
  | div x m q =>
    intro pos
    have hq := h pos
    simp only [Known.wf] at wk
    rw [← ev_agree wk.1 a, ← a q (by omega), ← a (q + 1) wk.2]
    exact hq
  | block j c off vs =>
    obtain ⟨x, r, count, l, h1, h2, h3, h4, h5, h6, h7⟩ := h
    have eo := ev_agree wk.1 a
    refine ⟨x, r, count, l, h1, h2, h3, by rw [← eo]; exact h4, by rw [← eo]; exact h5, h6, fun w hw => ?_⟩
    have hm : vs.getD w 0 ∈ vs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    rw [← eo, ← a _ (wk.2 _ hm)]; exact h7 w hw
  | use f keys u =>
    intro hpv
    obtain ⟨d, h1, h2, h3⟩ := h hpv
    refine ⟨d, h1, h2, ?_⟩
    have ek : keys.map (Key.val ctx s0 ρ' T') = keys.map (Key.val ctx s0 ρ T) :=
      List.map_congr_left fun k hk => Key.val_mono (wk.1 k hk) a hw ha e
    rw [ek, ← a u wk.2]; exact h3
  | record u fields ids =>
    intro hpv
    obtain ⟨fvs, h1, h2⟩ := h hpv
    refine ⟨fvs, by rw [← a u wk.1]; exact h1, ?_⟩
    have ei : (ids.map fun i => den (inpOf ctx s0) ρ' T' i) = ids.map fun i => den (inpOf ctx s0) ρ T i :=
      List.map_congr_left fun i hi => den_mono hw ha a e (wk.2 i hi)
    rw [ei]; exact h2
  | word32 lo hi =>
    intro v hv1 hv2
    rw [← a v (Nat.lt_of_lt_of_le hv2 wk)]
    exact h v hv1 hv2
  | termVal v id =>
    simp only [Known.holds] at h ⊢
    rw [← a v wk.1, den_mono hw ha a e wk.2]
    exact h

theorem Key.wf_mono {n n' t t' : Nat} {k : Key} (hn : n ≤ n') (ht : t ≤ t') (wk : k.wf n t) : k.wf n' t' := by
  cases k with
  | num r => exact bounded_mono hn wk
  | counter r => exact bounded_mono hn wk
  | words js => exact fun i hi => Nat.lt_of_lt_of_le (wk i hi) ht
  | lane j c l => trivial
  | span r off len => exact ⟨bounded_mono hn wk.1, bounded_mono hn wk.2⟩
  | use h => exact Nat.lt_of_lt_of_le wk hn

theorem Known.wf_mono {n n' t t' : Nat} {k : Known} (hn : n ≤ n') (ht : t ≤ t') (wk : k.wf n t) : k.wf n' t' := by
  cases k with
  | load v j c => exact Nat.lt_of_lt_of_le wk hn
  | or v x y => exact ⟨Nat.lt_of_lt_of_le wk.1 hn, bounded_mono hn wk.2.1, bounded_mono hn wk.2.2⟩
  | held f keys ids => exact ⟨fun k hk => Key.wf_mono hn ht (wk.1 k hk), fun i hi => Nat.lt_of_lt_of_le (wk.2 i hi) ht⟩
  | heldB f keys ids => exact ⟨fun k hk => Key.wf_mono hn ht (wk.1 k hk), fun i hi => Nat.lt_of_lt_of_le (wk.2 i hi) ht⟩
  | div x m q => exact ⟨bounded_mono hn wk.1, Nat.lt_of_lt_of_le wk.2 hn⟩
  | block j c off vs => exact ⟨bounded_mono hn wk.1, fun v hv => Nat.lt_of_lt_of_le (wk.2 v hv) hn⟩
  | use f keys h => exact ⟨fun k hk => Key.wf_mono hn ht (wk.1 k hk), Nat.lt_of_lt_of_le wk.2 hn⟩
  | record u fields ids => exact ⟨Nat.lt_of_lt_of_le wk.1 hn, fun i hi => Nat.lt_of_lt_of_le (wk.2 i hi) ht⟩
  | word32 _ _ => exact Nat.le_trans wk hn
  | termVal _ _ => exact ⟨Nat.lt_of_lt_of_le wk.1 hn, Nat.lt_of_lt_of_le wk.2 ht⟩

/-- What holds, holds whatever values the unknowns not yet in use are given. -/
theorem RangeHolds.agree {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {rg : RangeF} {mem : Nat → Byte} {n : Nat}
    (bl : bounded n rg.lo) (ba : ∀ v ∈ rg.args, v.bounded n) (a : Agree n ρ ρ') (h : RangeHolds ctx s0 ρ rg mem) :
    RangeHolds ctx s0 ρ' rg mem := by
  obtain ⟨name, r, m, params, x, b, hi, h1, h2, h3, h4, h5⟩ := h
  have el := ev_agree bl a
  have ea : rg.args.map (semv ctx s0 ρ') = rg.args.map (semv ctx s0 ρ) :=
    List.map_congr_left fun v hv => (semv_agree (ba v hv) a).symm
  refine ⟨name, r, m, params, x, b, hi, h1, h2, h3, by rw [← el]; exact h4, fun j lo hj => ?_⟩
  rw [ea]
  exact h5 j (by rw [el]; exact lo) hj

theorem Holds.agree {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {s : Sym} {st : State}
    (h : Holds ctx s0 ρ s st) (wf : WF ctx s) (a : Agree s.nvars ρ ρ') : Holds ctx s0 ρ' s st where
  entry r hr := (a r (Nat.lt_of_lt_of_le hr wf.regs)).symm.trans (h.entry r hr)
  data := ⟨(a (dataVar ctx) wf.base).symm.trans h.data.1, h.data.2⟩
  reg r hr := (h.reg r hr).trans (ev_agree (wf.reg r hr) a)
  small := h.small
  zf := Flag.holds_agree wf.zf a h.zf
  cf := Flag.holds_agree wf.cf a h.cf
  frame o v m := by
    obtain ⟨h1, h2, h3⟩ := h.frame o v m
    exact ⟨h1, h2, h3.trans (ev_agree (wf.frame o v m) a)⟩
  frameW o i m := by
    obtain ⟨h1, h2, h3⟩ := h.frameW o i m
    exact ⟨h1, h2, h3.trans (den_agree wf.words.table (fun j r hj => (ev_agree (wf.words.atoms j r hj) a).symm) (wf.frameW o i m)).symm⟩
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
  wrote w o x m := by
    obtain ⟨name, r, n, h1, h2, h3, h4⟩ := h.wrote w o x m
    have eo := ev_agree (wf.wrote w o x m).1 a
    have ex := ev_agree (wf.wrote w o x m).2 a
    exact ⟨name, r, n, h1, by rw [← eo]; exact h2, by rw [← eo]; exact h3, by rw [← eo, ← ex]; exact h4⟩
  words := VecOk.agree wf.words a h.words
  known k m := Known.holds_mono (wf.known k m) a wf.words.table wf.words.atoms (Ext.refl _) (h.known k m)
  range rg hr := RangeHolds.agree (wf.range rg hr).1 (wf.range rg hr).2 a (h.range rg hr)
  vecIntact := h.vecIntact

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
  | neq r => exact Ode.bounded_mono h hb

/-! ## Memory -/

theorem load_lt (mem : Nat → Byte) (a n : Nat) : load mem a n < 256 ^ n := by
  induction n generalizing a with
  | zero => simp [load]
  | succ n ih =>
    simp only [load]
    have := ih (a + 1)
    have h256 : (mem a).val < 256 := (mem a).isLt
    rw [Nat.pow_succ]
    omega

theorem inpOf_lt (ctx : Ctx) (s0 : State) (j k : Nat) : inpOf ctx s0 j k < W32 := by
  unfold inpOf
  split
  · exact load_lt _ _ 4
  · decide

theorem store_other (mem : Nat → Byte) (a v n x : Nat) (h : x < a ∨ a + n ≤ x) : store mem a v n x = mem x := by
  induction n generalizing mem a v with
  | zero => rfl
  | succ n ih =>
    simp only [store]
    rw [ih _ _ _ (by omega)]
    split
    · omega
    · rfl

theorem load_congr (mem mem' : Nat → Byte) (a n : Nat) (h : ∀ x, a ≤ x → x < a + n → mem x = mem' x) : load mem a n = load mem' a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [load]
    rw [h a (by omega) (by omega), ih (a + 1) (fun x h1 h2 => h x (by omega) (by omega))]

/-- A load of memory whose bytes are those of a list, from a place of the list on, is the load of the list. -/
theorem load_list (mem : Nat → Byte) (l : List Nat) : ∀ (n a c : Nat), (∀ k, k < n → mem (a + k) = l.getD (c + k) 0) →
    load mem a n = load (fun x => ⟨l.getD x 0 % 256, Nat.mod_lt _ (by decide)⟩) c n
  | 0, _, _, _ => rfl
  | n + 1, a, c, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    have hlt : l.getD c 0 < 256 := by rw [← h0]; exact (mem a).isLt
    simp only [load]
    rw [h0, load_list mem l n (a + 1) (c + 1) (fun k hk => by
      have := h (k + 1) (by omega)
      rw [show a + 1 + k = a + (k + 1) by omega, show c + 1 + k = c + (k + 1) by omega]
      exact this)]
    rw [Nat.mod_eq_of_lt hlt]

theorem load_store_other (mem : Nat → Byte) (a v n b k : Nat) (h : b + k ≤ a ∨ a + n ≤ b) : load (store mem a v n) b k = load mem b k :=
  load_congr _ _ _ _ fun x h1 h2 => store_other mem a v n x (by omega)

theorem load_store_same (mem : Nat → Byte) (a v n : Nat) (h : v < 256 ^ n) : load (store mem a v n) a n = v := by
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

theorem noDupB_nodup : ∀ (rs : List Nat), noDupB rs = true → rs.Nodup
  | [], _ => List.Pairwise.nil
  | r :: rs, h => by
    simp only [noDupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, noDupB_nodup rs h.2⟩
    have hc : rs.contains r = true := List.contains_iff_mem.mpr hm
    rw [h.1] at hc; cases hc

theorem validRegList_spec {nreg : Nat} {rs : List Nat} (hv : validRegList nreg rs = true) :
    (∀ r ∈ rs, r < nreg ∧ r ≠ RSP ∧ r ≠ LINK) ∧ rs.Nodup := by
  simp only [validRegList, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, decide_eq_true_eq] at hv
  exact ⟨fun r hr => by have := hv.1 r hr; exact ⟨this.1.1, this.1.2, this.2⟩, noDupB_nodup rs hv.2⟩

theorem retReg_spec (c : Contract) :
    c.retReg < c.regs ∧ c.retReg ≠ RSP ∧ c.retReg ≠ LINK ∧ (c.result.isSome = true → c.retReg = 0) := by
  have h0 : 0 < c.regs ∧ 0 ≠ RSP ∧ 0 ≠ LINK := by
    cases ha : c.arm64 <;> simp [Contract.regs, RSP, LINK, ha]
  unfold Contract.retReg
  cases hr : c.customRet with
  | none => exact ⟨h0.1, h0.2.1, h0.2.2, fun _ => rfl⟩
  | some r =>
    simp only
    by_cases hv : (decide (r < c.regs) && r != RSP && r != LINK && !c.result.isSome) = true
    · simp only [hv, ↓reduceIte]
      simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at hv
      exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2, fun h => by rw [h] at hv; exact absurd hv.2 (by decide)⟩
    · simp only [hv]
      exact ⟨h0.1, h0.2.1, h0.2.2, fun _ => rfl⟩

theorem argRegs_spec {c : Contract} {r : Nat} (h : r ∈ c.argRegs) : r < c.regs ∧ r ≠ RSP ∧ r ≠ LINK := by
  have hdef : r ∈ (if c.arm64 then argRegsArm else argRegsX86) → r < c.regs ∧ r ≠ RSP ∧ r ≠ LINK := by
    cases ha : c.arm64
    · have all : ∀ r ∈ argRegsX86, r < 16 ∧ r ≠ RSP ∧ r ≠ LINK := by decide
      simp only [Contract.regs, ha, Bool.false_eq_true, ↓reduceIte]; exact all r
    · have all : ∀ r ∈ argRegsArm, r < 32 ∧ r ≠ RSP ∧ r ≠ LINK := by decide
      simp only [Contract.regs, ha, ↓reduceIte]; exact all r
  unfold Contract.argRegs at h
  cases hc : c.customArgs with
  | none => rw [hc] at h; exact hdef h
  | some rs =>
    rw [hc] at h; simp only at h
    by_cases hv : validRegList c.regs rs = true
    · simp only [hv, ↓reduceIte] at h; exact (validRegList_spec hv).1 r h
    · simp only [hv] at h; exact hdef h

theorem argRegs_nodup (c : Contract) : c.argRegs.Nodup := by
  have hdef : (if c.arm64 then argRegsArm else argRegsX86).Nodup := by
    cases c.arm64
    · have nd : argRegsX86.Nodup := by decide
      simp only [Bool.false_eq_true, ↓reduceIte]; exact nd
    · have nd : argRegsArm.Nodup := by decide
      simp only [↓reduceIte]; exact nd
  unfold Contract.argRegs
  cases hc : c.customArgs with
  | none => exact hdef
  | some rs =>
    simp only
    by_cases hv : validRegList c.regs rs = true
    · simp only [hv, ↓reduceIte]; exact (validRegList_spec hv).2
    · simp only [hv]; exact hdef

theorem keeps_spec {c : Contract} {r : Nat} (h : r ∈ c.keeps) : r < c.regs ∧ r ≠ RSP ∧ r ≠ LINK := by
  have hdef : r ∈ (if c.arm64 then calleeSavedArm else calleeSavedX86) → r < c.regs ∧ r ≠ RSP ∧ r ≠ LINK := by
    cases ha : c.arm64
    · have all : ∀ r ∈ calleeSavedX86, r < 16 ∧ r ≠ RSP ∧ r ≠ LINK := by decide
      simp only [Contract.regs, ha, Bool.false_eq_true, ↓reduceIte]; exact all r
    · have all : ∀ r ∈ calleeSavedArm, r < 32 ∧ r ≠ RSP ∧ r ≠ LINK := by decide
      simp only [Contract.regs, ha, ↓reduceIte]; exact all r
  unfold Contract.keeps at h
  have hraw : r ∈ (match c.customKeeps with
      | some rs => if validRegList c.regs rs then rs else if c.arm64 then calleeSavedArm else calleeSavedX86
      | none => if c.arm64 then calleeSavedArm else calleeSavedX86) := by
    cases hg : c.givesNumber with
    | false => simp only [hg, Bool.false_eq_true, ↓reduceIte] at h; exact h
    | true => simp only [hg, ↓reduceIte] at h; exact (List.mem_filter.mp h).1
  cases hc : c.customKeeps with
  | none => rw [hc] at hraw; exact hdef hraw
  | some rs =>
    rw [hc] at hraw; simp only at hraw
    by_cases hv : validRegList c.regs rs = true
    · simp only [hv, ↓reduceIte] at hraw; exact (validRegList_spec hv).1 r hraw
    · simp only [hv] at hraw; exact hdef hraw

theorem retReg_not_kept {c : Contract} (hg : c.givesNumber = true) : c.keeps.contains c.retReg = false := by
  cases hk : c.keeps.contains c.retReg with
  | false => rfl
  | true =>
    have hm : c.retReg ∈ c.keeps := List.contains_iff_mem.mp hk
    unfold Contract.keeps at hm
    simp only [hg, ↓reduceIte] at hm
    have hne := (List.mem_filter.mp hm).2
    simp only [bne_self_eq_false] at hne
    cases hne

theorem scratch_lt {c : Contract} {r : Nat} (h : r ∈ c.scratch) : r < c.regs := by
  unfold Contract.scratch at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

theorem kept_of_not_scratch {c : Contract} {r : Nat} (hr : r < c.regs) (h4 : r ≠ RSP) (hc : c.scratch.contains r = false) :
    r ∈ c.keeps := by
  cases hk : c.keeps.contains r with
  | true => exact List.contains_iff_mem.mp hk
  | false =>
    have hmem : r ∈ c.scratch := by
      unfold Contract.scratch
      refine List.mem_filter.mpr ⟨List.mem_range.mpr hr, ?_⟩
      simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true']
      exact ⟨h4, hk⟩
    have hct : c.scratch.contains r = true := List.contains_iff_mem.mpr hmem
    rw [hc] at hct; cases hct

theorem afterCall_vec (p q : Program) (i : Instr) (st : State) : (afterCall p q i st).vec = st.vec := by
  unfold afterCall
  cases callLink i <;> rfl

end Ode
