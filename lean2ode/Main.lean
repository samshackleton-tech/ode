import Lean
open Lean Meta

/-! # lean2ode: strict Lean 4 → OdeSpecL translator/extractor

Uses Lean 4's own elaborator and kernel `Expr` + equation lemmas (`getEqnsFor?`) to
translate a strictly allowlisted pure-functional fragment of Lean 4 into OdeSpecL.

Design rule: NEVER guess or silently approximate. Any construct outside the exact
supported fragment fails immediately with a non-zero exit code naming the definition
and the unsupported Lean construct.
-/

namespace Lean2Ode

inductive ValKind where
  | nat
  | u8
  | u32
  | u64
  | bool
  | seq (elem : ValKind)
  deriving BEq, Repr

structure TrState where
  locals    : NameSet          -- all user definitions present in the elaborated file
  deps      : List Name        -- local helper definitions referenced by current def
  curDef    : Name             -- current definition being translated (for error messages)
  lifted    : List String      -- top-level helper defs emitted when hoisting nested lets
  liftIdx   : Nat := 0
  odeNames  : NameMap String   -- Lean Name -> clean OdeSpecL identifier
  usedNames : Std.HashSet String

abbrev TrM := StateT TrState MetaM

def fail {α : Type} (msg : String) : TrM α := do
  let cur := (← get).curDef
  throwError s!"lean2ode: cannot reliably translate `{cur}`: {msg}"

def sanitizeName (n : Name) : String :=
  let s := n.toString
  let chars := s.toList.map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  let base := String.ofList chars
  if base.isEmpty then "v"
  else if base.toList.head!.isDigit then "_" ++ base
  else base

def shortOdeName (n : Name) : TrM String := do
  let st ← get
  if let some existing := st.odeNames.find? n then
    return existing
  let raw := match n with
    | .str _ s => sanitizeName (.mkSimple s)
    | _ => sanitizeName n
  let candidate :=
    if !st.usedNames.contains raw && !["def", "let", "if", "then", "else", "for", "in", "const", "len", "word", "words", "bytes_of", "contract", "sequence", "with"].contains raw then
      raw
    else
      sanitizeName n
  let mut final := candidate
  let mut k := 1
  while (← get).usedNames.contains final do
    final := s!"{candidate}_{k}"
    k := k + 1
  modify fun s => { s with
    odeNames := s.odeNames.insert n final
    usedNames := s.usedNames.insert final }
  return final

def recordDep (n : Name) : TrM Unit := do
  let st ← get
  if st.locals.contains n && n != st.curDef && !st.deps.contains n then
    modify fun s => { s with deps := s.deps ++ [n] }

/-- Extract a Nat literal from `Nat.lit`, `OfNat.ofNat`, `Nat.zero`, `Nat.succ`, etc. -/
partial def asNatLit? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  match e with
  | .lit (.natVal n) => return some n
  | .const `Nat.zero _ => return some 0
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf `OfNat.ofNat && args.size >= 2 then
      asNatLit? args[1]!
    else if fn.isConstOf `Nat.succ && args.size == 1 then
      return (← asNatLit? args[0]!).map (· + 1)
    else if fn.isConstOf `UInt8.ofNat && args.size == 1 then
      return (← asNatLit? args[0]!).map (· % 256)
    else if fn.isConstOf `UInt32.ofNat && args.size == 1 then
      return (← asNatLit? args[0]!).map (· % 4294967296)
    else if fn.isConstOf `UInt64.ofNat && args.size == 1 then
      return (← asNatLit? args[0]!).map (· % (2 ^ 64))
    else if fn.isConstOf `Nat.toUInt8 && args.size == 1 then
      return (← asNatLit? args[0]!).map (· % 256)
    else if fn.isConstOf `Nat.toUInt32 && args.size == 1 then
      return (← asNatLit? args[0]!).map (· % 4294967296)
    else if fn.isConstOf `Fin.mk && args.size == 3 then
      asNatLit? args[1]!
    else
      return none

/-- Classify a Lean type into the strictly supported OdeSpecL value kinds (or fail loudly). -/
partial def classifyType (ty : Expr) : TrM ValKind := do
  let ty ← whnf ty
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  if fn.isConstOf `Nat then return .nat
  if fn.isConstOf `UInt8 then return .u8
  if fn.isConstOf `UInt32 then return .u32
  if fn.isConstOf `UInt64 then return .u64
  if fn.isConstOf `Bool then return .bool
  if fn.isConstOf `ByteArray then return .seq .u8
  if fn.isConstOf `Fin && args.size == 1 then
    return .nat
  if (fn.isConstOf `List || fn.isConstOf `Array) && args.size == 1 then
    let ek ← classifyType args[0]!
    match ek with
    | .seq _ => fail s!"nested sequence type `{← ppExpr ty}` is not supported"
    | .bool  => fail s!"sequence of Bool `{← ppExpr ty}` is not supported"
    | _      => return .seq ek
  if fn.isConstOf `Vector && args.size == 2 then
    let some _ ← asNatLit? args[1]!
      | fail s!"Vector with non-literal length `{← ppExpr ty}` is not supported"
    let ek ← classifyType args[0]!
    match ek with
    | .seq _ => fail s!"nested Vector type `{← ppExpr ty}` is not supported"
    | .bool  => fail s!"Vector of Bool `{← ppExpr ty}` is not supported"
    | _      => return .seq ek
  fail s!"unsupported type `{← ppExpr ty}`"

/-- Classify the scalar/word kind of an operator's type argument `α`. -/
def classifyOpType (ty : Expr) : TrM ValKind := do
  let ty ← whnf ty
  let fn := ty.getAppFn
  if fn.isConstOf `Nat then return .nat
  if fn.isConstOf `UInt8 then return .u8
  if fn.isConstOf `UInt32 then return .u32
  if fn.isConstOf `UInt64 then return .u64
  if fn.isConstOf `Fin then return .nat
  fail s!"unsupported operator operand type `{← ppExpr ty}`"

/-- Check whether `e` is a `UInt32` shift-right `x >>> k` or shift-left `x <<< k`, returning `(x, kExpr)`. -/
def matchU32Shift (isRight : Bool) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  let wantH := if isRight then `HShiftRight.hShiftRight else `HShiftLeft.hShiftLeft
  let wantD := if isRight then `UInt32.shiftRight else `UInt32.shiftLeft
  if fn.isConstOf wantH && args.size == 6 then
    let ty ← whnf args[0]!
    if ty.isConstOf `UInt32 then
      return some (args[4]!, args[5]!)
  if fn.isConstOf wantD && args.size == 2 then
    return some (args[0]!, args[1]!)
  return none

/-- Unwrap `Nat.toUInt32 e` or `UInt32.ofNat e` when extracting a shift count. -/
def unwrapShiftCount (e : Expr) : Expr :=
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf `Nat.toUInt32 || fn.isConstOf `UInt32.ofNat) && args.size == 1 then
    args[0]!.consumeMData
  else e

/-- Check whether `lCount` represents `32 - rCount` (either both literals summing to 32, or `32 - x` matching `x`). -/
def isComplement32 (rCount lCount : Expr) : MetaM Bool := do
  let rLit? ← asNatLit? rCount
  let lLit? ← asNatLit? lCount
  match rLit?, lLit? with
  | some r, some l => return (r > 0 && r < 32 && r + l == 32)
  | _, _ =>
    let rU := unwrapShiftCount rCount
    let lU := unwrapShiftCount lCount
    let fn := lU.getAppFn
    let args := lU.getAppArgs
    if fn.isConstOf `HSub.hSub && args.size == 6 then
      let some c32 ← asNatLit? args[4]! | return false
      return c32 == 32 && args[5]!.consumeMData == rU
    if fn.isConstOf `Nat.sub && args.size == 2 then
      let some c32 ← asNatLit? args[0]! | return false
      return c32 == 32 && args[1]!.consumeMData == rU
    return false

/-- Try to recognize an exact 32-bit rotate-right `(x >>> k) ||| (x <<< (32 - k))` (either operand order). -/
def matchU32RotateRight (a b : Expr) : MetaM (Option (Expr × Expr)) := do
  if let (some (xr, rk), some (xl, lk)) := (← matchU32Shift true a, ← matchU32Shift false b) then
    if xr == xl && (← isComplement32 rk lk) then
      return some (xr, unwrapShiftCount rk)
  if let (some (xl, lk), some (xr, rk)) := (← matchU32Shift false a, ← matchU32Shift true b) then
    if xr == xl && (← isComplement32 rk lk) then
      return some (xr, unwrapShiftCount rk)
  return none

/-- Try to extract a finite Lean list literal `[e1, e2, ...]`. -/
partial def asListElems? (e : Expr) : Option (List Expr) :=
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf `List.nil then some []
  else if fn.isConstOf `List.cons && args.size == 3 then
    (asListElems? args[2]!).map (args[1]! :: ·)
  else if (fn.isConstOf `Array.mk && args.size == 2) then
    asListElems? args[1]!
  else if (fn.isConstOf `List.toArray && args.size == 2) then
    asListElems? args[1]!
  else if (fn.isConstOf `Vector.mk && args.size == 4) then
    asListElems? args[2]!
  else none

/-- Pick a fresh parameter/variable name avoiding collisions with `envNames`. -/
def freshVar (hint : Name) (used : List String) : String :=
  let clean := hint.eraseMacroScopes
  let base := sanitizeName (match clean with | .str _ s => .mkSimple s | _ => clean)
  let base := if base.isEmpty || base == "_" || ["def", "let", "if", "then", "else", "for", "in", "const", "len", "word"].contains base then "x" else base
  if !used.contains base then base
  else Id.run do
    let mut k := 1
    while used.contains s!"{base}_{k}" do
      k := k + 1
    return s!"{base}_{k}"

/-- Check if an expression is already safe to inline without lifting a `let`. -/
def isSimpleOdeAtom (s : String) : Bool :=
  s.all fun c => c.isAlphanum || c == '_'

/-- Main strict kernel `Expr` → OdeSpecL expression translator.
    `fvarMap` maps Lean FVarIds to their OdeSpecL variable names.
    `topLevel` is true only at the root of a `def` body (where OdeSpecL permits `let x = ...`). -/
partial def trExpr (fvarMap : Std.HashMap FVarId String) (usedVars : List String)
    (topLevel : Bool) (e : Expr) : TrM (List (String × String) × String) := do
  let e := e.consumeMData
  if e.hasSorry then
    fail "expression contains `sorry`"

  match e with
  | .fvar fid =>
    match fvarMap.get? fid with
    | some nm => return ([], nm)
    | none => fail s!"unexpected free variable `{← ppExpr e}`"

  | .lit (.natVal n) =>
    return ([], toString n)

  | .lit (.strVal s) =>
    fail s!"string literal {repr s} is not supported in OdeSpecL"

  | .const nm _ =>
    if nm == `Bool.true then return ([], "(0 == 0)")
    if nm == `Bool.false then return ([], "(0 == 1)")
    if nm == `Nat.zero then return ([], "0")
    if nm == `List.nil then return ([], "[]")
    if (← get).locals.contains nm then
      recordDep nm
      let onm ← shortOdeName nm
      return ([], onm)
    fail s!"unsupported constant `{nm}`"

  | .letE hint ty val body _ =>
    let _ ← classifyType ty
    let (vLets, vStr) ← trExpr fvarMap usedVars false val
    let vnm := freshVar hint usedVars
    let res ← withLocalDeclD hint ty fun fv => do
      let bodyInst := body.instantiate1 fv
      let map' := fvarMap.insert fv.fvarId! vnm
      let used' := vnm :: usedVars
      if topLevel then
        let (bLets, bStr) ← trExpr map' used' true bodyInst
        return (vLets ++ [(vnm, vStr)] ++ bLets, bStr)
      else
        -- Inside an expression where OdeSpecL does not allow inline `let`,
        -- lift cleanly into a helper `def` (or inline if trivial atom).
        if vLets.isEmpty && isSimpleOdeAtom vStr then
          let mapInline := fvarMap.insert fv.fvarId! vStr
          trExpr mapInline usedVars false bodyInst
        else
          let (bLets, bStr) ← trExpr map' used' true bodyInst
          -- Collect live fvars referenced in bodyInst + val (actually capture all current fvarMap vars deterministically)
          let envPairs := fvarMap.toList.mergeSort (fun a b => a.2 < b.2)
          let pnames := envPairs.map (·.2)
          let curShort ← shortOdeName (← get).curDef
          let idx := (← get).liftIdx
          modify fun s => { s with liftIdx := idx + 1 }
          let helperName := s!"{curShort}_let{idx}"
          let letLines := (vLets ++ [(vnm, vStr)] ++ bLets).map fun (x, rhs) => s!"    let {x} = {rhs}"
          let bodyBlock := String.intercalate "\n" (letLines ++ [s!"    {bStr}"])
          let defStr := s!"def {helperName}({String.intercalate ", " pnames}) \{\n{bodyBlock}\n}"
          modify fun s => { s with lifted := s.lifted ++ [defStr] }
          return ([], s!"{helperName}({String.intercalate ", " pnames})")
    return res

  | .lam .. =>
    fail s!"unsupported lambda abstraction `{← ppExpr e}`"

  | .mdata _ b =>
    trExpr fvarMap usedVars topLevel b

  | .forallE .. | .sort .. | .mvar .. | .bvar .. | .proj .. =>
    fail s!"unsupported kernel term `{← ppExpr e}`"

  | .app .. =>
    let fn := e.getAppFn.consumeMData
    let args := e.getAppArgs
    let .const nm _ := fn
      | fail s!"unsupported higher-order application `{← ppExpr e}`"

    -- 1. Reject forbidden / non-functional constructs immediately
    if nm == `sorryAx then fail "expression contains `sorry`"
    if nm == `Id.run || nm == `Bind.bind || nm == `Pure.pure || nm == `ForIn.forIn || nm == `ForInStep.yield then
      fail s!"monadic/imperative construct `{nm}` cannot be directly translated to declarative OdeSpecL"
    if nm == `Option.some || nm == `Option.none || nm == `Except.ok || nm == `Except.error then
      fail s!"algebraic sum/error construct `{nm}` is not in OdeSpecL"

    -- 2. Numeric literals (`OfNat.ofNat α n inst`)
    if nm == `OfNat.ofNat && args.size == 3 then
      let some n ← asNatLit? args[1]!
        | fail s!"non-literal OfNat `{← ppExpr e}`"
      let k ← classifyOpType args[0]!
      match k with
      | .u32 => return ([], s!"word({n % 4294967296})")
      | .u8  => return ([], toString (n % 256))
      | _    => return ([], toString n)

    if nm == `Nat.succ && args.size == 1 then
      if let some n ← asNatLit? e then return ([], toString n)
      let (l, s) ← trExpr fvarMap usedVars false args[0]!
      return (l, s!"({s} + 1)")

    -- 3. Explicit coercions / wrappers
    if nm == `UInt8.toNat && args.size == 1 then
      return ← trExpr fvarMap usedVars false args[0]!
    if (nm == `Nat.toUInt8 || nm == `UInt8.ofNat) && args.size == 1 then
      if let some n ← asNatLit? args[0]! then return ([], toString (n % 256))
      let (l, s) ← trExpr fvarMap usedVars false args[0]!
      return (l, s!"({s} % 256)")
    if (nm == `Nat.toUInt32 || nm == `UInt32.ofNat) && args.size == 1 then
      if let some n ← asNatLit? args[0]! then return ([], s!"word({n % 4294967296})")
      let (l, s) ← trExpr fvarMap usedVars false args[0]!
      return (l, s!"word({s})")
    if nm == `Fin.val && args.size == 2 then
      return ← trExpr fvarMap usedVars false args[1]!
    if nm == `Fin.mk && args.size == 3 then
      return ← trExpr fvarMap usedVars false args[1]!
    if nm == `Decidable.decide && args.size == 2 then
      return ← trExpr fvarMap usedVars false args[0]!

    -- 4. Conditionals (`ite`, `dite`, `cond`)
    if nm == `ite && args.size == 5 then
      let (lc, sc) ← trExpr fvarMap usedVars false args[1]!
      let (lt, st) ← trExpr fvarMap usedVars false args[3]!
      let (le, se) ← trExpr fvarMap usedVars false args[4]!
      return (lc ++ lt ++ le, s!"(if {sc} then {st} else {se})")

    if nm == `dite && args.size == 5 then
      let (lc, sc) ← trExpr fvarMap usedVars false args[1]!
      match args[3]!.consumeMData, args[4]!.consumeMData with
      | .lam _ _ tb _, .lam _ _ eb _ =>
        if tb.hasLooseBVars || eb.hasLooseBVars then
          fail "dependent `if h : ...` where branches inspect the proof term `h` is not supported"
        let (lt, st) ← trExpr fvarMap usedVars false tb
        let (le, se) ← trExpr fvarMap usedVars false eb
        return (lc ++ lt ++ le, s!"(if {sc} then {st} else {se})")
      | _, _ => fail "unsupported `dite` branch shape"

    if nm == `cond && args.size == 4 then
      let (lc, sc) ← trExpr fvarMap usedVars false args[1]!
      let (lt, st) ← trExpr fvarMap usedVars false args[2]!
      let (le, se) ← trExpr fvarMap usedVars false args[3]!
      return (lc ++ lt ++ le, s!"(if {sc} then {st} else {se})")

    -- 5. Boolean logic
    if (nm == `Bool.and || nm == `And) && args.size == 2 then
      let (la, sa) ← trExpr fvarMap usedVars false args[0]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[1]!
      return (la ++ lb, s!"({sa} && {sb})")

    if (nm == `Bool.or || nm == `Or) && args.size == 2 then
      let (la, sa) ← trExpr fvarMap usedVars false args[0]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[1]!
      return (la ++ lb, s!"({sa} || {sb})")

    if (nm == `Bool.not || nm == `Not) && args.size == 1 then
      let (la, sa) ← trExpr fvarMap usedVars false args[0]!
      return (la, s!"(if {sa} then (0 == 1) else (0 == 0))")

    -- 6. Comparisons (strictly on supported scalar/word types)
    if (nm == `LT.lt || nm == `LE.le || nm == `GT.gt || nm == `GE.ge) && args.size == 4 then
      let _ ← classifyOpType args[0]!
      let op := if nm == `LT.lt then "<" else if nm == `LE.le then "<=" else if nm == `GT.gt then ">" else ">="
      let (la, sa) ← trExpr fvarMap usedVars false args[2]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[3]!
      return (la ++ lb, s!"({sa} {op} {sb})")

    if (nm == `BEq.beq || nm == `bne) && args.size == 4 then
      let ty ← whnf args[0]!
      if ty.isConstOf `Bool then
        let (la, sa) ← trExpr fvarMap usedVars false args[2]!
        let (lb, sb) ← trExpr fvarMap usedVars false args[3]!
        let isNe := nm == `bne
        if args[3]!.consumeMData.isConstOf `Bool.true then
          return (la, if isNe then s!"(if {sa} then (0 == 1) else (0 == 0))" else sa)
        if args[3]!.consumeMData.isConstOf `Bool.false then
          return (la, if isNe then sa else s!"(if {sa} then (0 == 1) else (0 == 0))")
        return (la ++ lb, if isNe then s!"(if {sa} then (if {sb} then (0 == 1) else (0 == 0)) else {sb})"
                          else s!"(if {sa} then {sb} else (if {sb} then (0 == 1) else (0 == 0)))")
      let _ ← classifyOpType args[0]!
      let op := if nm == `BEq.beq then "==" else "!="
      let (la, sa) ← trExpr fvarMap usedVars false args[2]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[3]!
      return (la ++ lb, s!"({sa} {op} {sb})")

    if nm == `Eq && args.size == 3 then
      let ty ← whnf args[0]!
      if ty.isConstOf `Bool then
        let (la, sa) ← trExpr fvarMap usedVars false args[1]!
        if args[2]!.consumeMData.isConstOf `Bool.true then
          return (la, sa)
        if args[2]!.consumeMData.isConstOf `Bool.false then
          return (la, s!"(if {sa} then (0 == 1) else (0 == 0))")
        let (lb, sb) ← trExpr fvarMap usedVars false args[2]!
        return (la ++ lb, s!"(if {sa} then {sb} else (if {sb} then (0 == 1) else (0 == 0)))")
      let _ ← classifyOpType args[0]!
      let (la, sa) ← trExpr fvarMap usedVars false args[1]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[2]!
      return (la ++ lb, s!"({sa} == {sb})")

    if (nm == `Nat.beq || nm == `Nat.blt || nm == `Nat.ble) && args.size == 2 then
      let op := if nm == `Nat.beq then "==" else if nm == `Nat.blt then "<" else "<="
      let (la, sa) ← trExpr fvarMap usedVars false args[0]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[1]!
      return (la ++ lb, s!"({sa} {op} {sb})")

    -- 7. Arithmetic & Bitwise Ops (type-checked & semantically exact!)
    if nm == `HAdd.hAdd && args.size == 6 then
      let k ← classifyOpType args[0]!
      let (la, sa) ← trExpr fvarMap usedVars false args[4]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[5]!
      match k with
      | .nat | .u32 => return (la ++ lb, s!"({sa} + {sb})")
      | .u8 => return (la ++ lb, s!"(({sa} + {sb}) % 256)")
      | .u64 => fail "UInt64 wrapping addition is not directly mapped to OdeSpecL unbounded `+`"
      | _ => fail "unsupported addition type"

    if nm == `Nat.add && args.size == 2 then
      let (la, sa) ← trExpr fvarMap usedVars false args[0]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[1]!
      return (la ++ lb, s!"({sa} + {sb})")

    if nm == `HSub.hSub && args.size == 6 then
      let k ← classifyOpType args[0]!
      let (la, sa) ← trExpr fvarMap usedVars false args[4]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[5]!
      match k with
      | .nat =>
        -- Lean Nat.sub truncates at 0! Emit exact truncating semantics unless both are literals with a >= b.
        match ← asNatLit? args[4]!, ← asNatLit? args[5]! with
        | some aLit, some bLit => return ([], toString (aLit - bLit))
        | _, _ => return (la ++ lb, s!"(if {sa} >= {sb} then {sa} - {sb} else 0)")
      | .u8 => return (la ++ lb, s!"(({sa} + 256 - {sb}) % 256)")
      | _ => fail s!"unsupported subtraction on `{← ppExpr args[0]!}`"

    if nm == `Nat.sub && args.size == 2 then
      let (la, sa) ← trExpr fvarMap usedVars false args[0]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[1]!
      match ← asNatLit? args[0]!, ← asNatLit? args[1]! with
      | some aLit, some bLit => return ([], toString (aLit - bLit))
      | _, _ => return (la ++ lb, s!"(if {sa} >= {sb} then {sa} - {sb} else 0)")

    if nm == `HMul.hMul && args.size == 6 then
      let k ← classifyOpType args[0]!
      let (la, sa) ← trExpr fvarMap usedVars false args[4]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[5]!
      match k with
      | .nat => return (la ++ lb, s!"({sa} * {sb})")
      | .u8  => return (la ++ lb, s!"(({sa} * {sb}) % 256)")
      | _    => fail s!"unsupported multiplication on `{← ppExpr args[0]!}`"

    if nm == `Nat.mul && args.size == 2 then
      let (la, sa) ← trExpr fvarMap usedVars false args[0]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[1]!
      return (la ++ lb, s!"({sa} * {sb})")

    if (nm == `HDiv.hDiv && args.size == 6) || (nm == `Nat.div && args.size == 2) then
      let (aExpr, bExpr, isNat) :=
        if nm == `Nat.div then (args[0]!, args[1]!, true)
        else (args[4]!, args[5]!, true)
      if nm == `HDiv.hDiv then
        let k ← classifyOpType args[0]!
        if k != .nat && k != .u8 then fail s!"unsupported division on `{← ppExpr args[0]!}`"
      let some d ← asNatLit? bExpr
        | fail s!"symbolic division divisor `{← ppExpr bExpr}` (Lean defines x / 0 = 0; divisor must be a nonzero literal)"
      if d == 0 then fail "division by literal 0"
      let (la, sa) ← trExpr fvarMap usedVars false aExpr
      let _ := isNat
      return (la, s!"({sa} / {d})")

    if (nm == `HMod.hMod && args.size == 6) || (nm == `Nat.mod && args.size == 2) then
      let (aExpr, bExpr) :=
        if nm == `Nat.mod then (args[0]!, args[1]!)
        else (args[4]!, args[5]!)
      if nm == `HMod.hMod then
        let k ← classifyOpType args[0]!
        if k != .nat && k != .u8 then fail s!"unsupported modulo on `{← ppExpr args[0]!}`"
      let some d ← asNatLit? bExpr
        | fail s!"symbolic modulo divisor `{← ppExpr bExpr}` (Lean defines x % 0 = x; modulus must be a nonzero literal)"
      if d == 0 then fail "modulo by literal 0"
      let (la, sa) ← trExpr fvarMap usedVars false aExpr
      return (la, s!"({sa} % {d})")

    if nm == `HPow.hPow && args.size == 6 then
      let some b ← asNatLit? args[4]!
        | fail "non-literal exponentiation (`^` in OdeSpecL is bitwise XOR, not power)"
      let some p ← asNatLit? args[5]!
        | fail "non-literal exponent (`^` in OdeSpecL is bitwise XOR, not power)"
      if p > 64 then fail s!"literal exponent {p} too large"
      return ([], toString (b ^ p))

    if nm == `HXor.hXor && args.size == 6 then
      let k ← classifyOpType args[0]!
      if k != .u32 && k != .u8 then fail s!"bitwise XOR on `{← ppExpr args[0]!}` is not supported"
      let (la, sa) ← trExpr fvarMap usedVars false args[4]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[5]!
      return (la ++ lb, s!"({sa} ^ {sb})")

    if nm == `HAnd.hAnd && args.size == 6 then
      let k ← classifyOpType args[0]!
      if k != .u32 && k != .u8 then fail s!"bitwise AND on `{← ppExpr args[0]!}` is not supported"
      let (la, sa) ← trExpr fvarMap usedVars false args[4]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[5]!
      return (la ++ lb, s!"({sa} & {sb})")

    if nm == `HOr.hOr && args.size == 6 then
      let k ← classifyOpType args[0]!
      if k == .u32 then
        -- Check for exact 32-bit rotate right pattern `(x >>> k) ||| (x <<< (32 - k))`!
        if let some (xr, rk) ← matchU32RotateRight args[4]! args[5]! then
          let (lx, sx) ← trExpr fvarMap usedVars false xr
          let (lk, sk) ← trExpr fvarMap usedVars false rk
          return (lx ++ lk, s!"({sx} >>> {sk})")
        let (la, sa) ← trExpr fvarMap usedVars false args[4]!
        let (lb, sb) ← trExpr fvarMap usedVars false args[5]!
        return (la ++ lb, s!"({sa} | {sb})")
      if k == .u8 then
        let (la, sa) ← trExpr fvarMap usedVars false args[4]!
        let (lb, sb) ← trExpr fvarMap usedVars false args[5]!
        return (la ++ lb, s!"({sa} | {sb})")
      fail s!"bitwise OR on `{← ppExpr args[0]!}` is not supported"

    if nm == `HShiftRight.hShiftRight && args.size == 6 then
      let k ← classifyOpType args[0]!
      if k == .u8 then
        let some sh ← asNatLit? args[5]!
          | fail "non-literal UInt8 right shift"
        if sh >= 8 then return ([], "0")
        let (la, sa) ← trExpr fvarMap usedVars false args[4]!
        return (la, s!"({sa} / {2 ^ sh})")
      if k == .u32 then
        fail "bare `UInt32` logical right shift (`>>>`) cannot map to OdeSpecL `>>>` (which is rotate-right); only rotate pattern `(x >>> k) ||| (x <<< (32 - k))` is supported"
      fail s!"unsupported shift-right on `{← ppExpr args[0]!}`"

    if nm == `HShiftLeft.hShiftLeft && args.size == 6 then
      let k ← classifyOpType args[0]!
      if k == .u8 then
        let some sh ← asNatLit? args[5]!
          | fail "non-literal UInt8 left shift"
        if sh >= 8 then return ([], "0")
        let (la, sa) ← trExpr fvarMap usedVars false args[4]!
        return (la, s!"(({sa} * {2 ^ sh}) % 256)")
      fail s!"unsupported shift-left on `{← ppExpr args[0]!}`"

    -- 8. Sequences: literals, cons, append, length, indexing, fixed comprehension
    if let some elems := asListElems? e then
      let mut allLets := []
      let mut parts := []
      for el in elems do
        let (l, s) ← trExpr fvarMap usedVars false el
        allLets := allLets ++ l
        parts := parts ++ [s]
      return (allLets, "[" ++ String.intercalate ", " parts ++ "]")

    if nm == `List.cons && args.size == 3 then
      let (lh, sh) ← trExpr fvarMap usedVars false args[1]!
      let (lt, st) ← trExpr fvarMap usedVars false args[2]!
      return (lh ++ lt, s!"([{sh}] ++ {st})")

    if nm == `HAppend.hAppend && args.size == 6 then
      let (la, sa) ← trExpr fvarMap usedVars false args[4]!
      let (lb, sb) ← trExpr fvarMap usedVars false args[5]!
      return (la ++ lb, s!"({sa} ++ {sb})")

    if (nm == `List.length || nm == `Array.size) && args.size == 2 then
      let (la, sa) ← trExpr fvarMap usedVars false args[1]!
      return (la, s!"len({sa})")

    if nm == `ByteArray.size && args.size == 1 then
      let (la, sa) ← trExpr fvarMap usedVars false args[0]!
      return (la, s!"len({sa})")

    if nm == `GetElem.getElem && args.size == 8 then
      let (lc, sc) ← trExpr fvarMap usedVars false args[5]!
      let (li, si) ← trExpr fvarMap usedVars false args[6]!
      return (lc ++ li, s!"{sc}[{si}]")

    if nm == `ByteArray.get! && args.size == 2 then
      let (lc, sc) ← trExpr fvarMap usedVars false args[0]!
      let (li, si) ← trExpr fvarMap usedVars false args[1]!
      return (lc ++ li, s!"{sc}[{si}]")

    if nm == `Array.get! && args.size == 4 then
      let (lc, sc) ← trExpr fvarMap usedVars false args[2]!
      let (li, si) ← trExpr fvarMap usedVars false args[3]!
      return (lc ++ li, s!"{sc}[{si}]")

    if nm == `List.getD && args.size == 4 then
      let (lc, sc) ← trExpr fvarMap usedVars false args[1]!
      let (li, si) ← trExpr fvarMap usedVars false args[2]!
      let (ld, sd) ← trExpr fvarMap usedVars false args[3]!
      return (lc ++ li ++ ld, s!"(if {si} < len({sc}) then {sc}[{si}] else {sd})")

    if (nm == `Vector.ofFn || nm == `List.ofFn) && args.size == 3 then
      -- Lean signature: `ofFn {n : Nat} {α : Type} (f : Fin n → α)` (so n = args[0], f = args[2])
      let some nLit ← asNatLit? args[0]!
        | fail s!"{nm} with non-literal bound `{← ppExpr args[0]!}`"
      match args[2]!.consumeMData with
      | .lam hint bty body _ =>
        let iv := freshVar hint usedVars
        let (lb, sb) ← withLocalDeclD hint bty fun fv => do
          trExpr (fvarMap.insert fv.fvarId! iv) (iv :: usedVars) false (body.instantiate1 fv)
        if !lb.isEmpty then
          fail s!"cannot lift let-bindings out of `{nm}` comprehension"
        return ([], s!"[{sb} for {iv} in 0..{nLit}]")
      | _ => fail s!"{nm} expects a lambda argument"

    -- 9. Calls to other local definitions in the same Lean file
    if (← get).locals.contains nm then
      recordDep nm
      let onm ← shortOdeName nm
      let mut allLets := []
      let mut rendered := []
      for a in args do
        let (l, s) ← trExpr fvarMap usedVars false a
        allLets := allLets ++ l
        rendered := rendered ++ [s]
      if rendered.isEmpty then
        return (allLets, onm)
      else
        return (allLets, s!"{onm}({String.intercalate ", " rendered})")

    fail s!"unsupported Lean constant/operation `{nm}` in `{← ppExpr e}`"

/-- Analyze a single kernel equation lemma `∀ x1 ... xk, fn lhs1 ... lhsm = rhs`. -/
structure ParsedEq where
  fvars   : Array Expr
  lhsArgs : Array Expr
  rhs     : Expr

def parseEqLemma (eqName : Name) (targetFn : Name) : TrM ParsedEq := do
  let ci ← getConstInfo eqName
  forallTelescopeReducing ci.type fun fvars body => do
    let fn := body.getAppFn
    let args := body.getAppArgs
    if !(fn.isConstOf `Eq && args.size == 3) then
      fail s!"equation lemma `{eqName}` is not an equality"
    let lhs := args[1]!.consumeMData
    let rhs := args[2]!.consumeMData
    if !lhs.getAppFn.isConstOf targetFn then
      fail s!"equation lemma `{eqName}` LHS does not match `{targetFn}`"
    return { fvars, lhsArgs := lhs.getAppArgs, rhs }

/-- Check if an LHS argument is `0` or `Nat.succ v` / `v + 1`. -/
def isZeroArg (e : Expr) : MetaM Bool := do
  return (← asNatLit? e) == some 0

def asSuccFVar? (e : Expr) : MetaM (Option FVarId) := do
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf `Nat.succ && args.size == 1 then
    match args[0]!.consumeMData with
    | .fvar fid => return some fid
    | _ => return none
  if fn.isConstOf `HAdd.hAdd && args.size == 6 then
    if (← asNatLit? args[5]!) == some 1 then
      match args[4]!.consumeMData with
      | .fvar fid => return some fid
      | _ => return none
  return none

/-- Render a single definition `nm` (either `const` or `def`) into OdeSpecL text. -/
def translateDef (nm : Name) : TrM String := do
  modify fun s => { s with curDef := nm }
  let ci ← getConstInfo nm
  match ci with
  | .defnInfo di =>
    if di.safety != .safe then
      fail "definition is `partial` or `unsafe`"
    if di.value.hasSorry then
      fail "definition contains `sorry`"
    -- Check parameter & return types strictly
    let (paramTypes, retType) ← forallTelescopeReducing di.type fun fvars ret => do
      let mut pts := #[]
      for fv in fvars do
        pts := pts.push (← inferType fv)
      return (pts, ret)
    for pt in paramTypes do
      let _ ← classifyType pt
    let _ ← classifyType retType

    let onm ← shortOdeName nm

    -- Zero-argument definition -> `const NAME = ...`
    if paramTypes.isEmpty then
      let (lets, body) ← trExpr {} [] false di.value
      if !lets.isEmpty then
        fail "top-level constant contains unliftable `let` binding"
      return s!"const {onm} = {body}"

    -- Parameterized definition -> use Lean 4's kernel-proved equation lemmas `getEqnsFor?`!
    let some eqs ← getEqnsFor? nm
      | fail "Lean 4 did not generate equation lemmas (possible `partial` / opaque / non-equational def)"
    if eqs.isEmpty then
      fail "no equation lemmas generated"

    if eqs.size == 1 then
      let ciEq ← getConstInfo eqs[0]!
      let res ← forallTelescopeReducing ciEq.type fun _fvars body => do
        let fn := body.getAppFn
        let args := body.getAppArgs
        if !(fn.isConstOf `Eq && args.size == 3) then
          fail s!"unexpected equation shape `{eqs[0]!}`"
        let lhs := args[1]!.consumeMData
        let rhs := args[2]!.consumeMData
        if !lhs.getAppFn.isConstOf nm then
          fail s!"unexpected equation LHS in `{eqs[0]!}`"
        let lhsArgs := lhs.getAppArgs
        if lhsArgs.size != paramTypes.size then
          fail "partial application / eta-reduced equation is not supported"
        let mut fvarMap : Std.HashMap FVarId String := {}
        let mut pnames : List String := []
        for la in lhsArgs do
          match la.consumeMData with
          | .fvar fid =>
            if fvarMap.contains fid then
              fail "non-linear pattern (repeated variable) in equation LHS"
            let ldecl ← fid.getDecl
            let vnm := freshVar ldecl.userName pnames
            fvarMap := fvarMap.insert fid vnm
            pnames := pnames ++ [vnm]
          | _ =>
            fail s!"unsupported pattern `{← ppExpr la}` in single-equation LHS"
        let (lets, bodyStr) ← trExpr fvarMap pnames true rhs
        let letLines := lets.map fun (x, v) => s!"    let {x} = {v}"
        let inner := String.intercalate "\n" (letLines ++ [s!"    {bodyStr}"])
        return s!"def {onm}({String.intercalate ", " pnames}) \{\n{inner}\n}"
      return res

    if eqs.size == 2 then
      -- Support exact 2-case Nat structural recursion (`0` vs `n + 1`) or Bool split (`false` vs `true`)
      let ci0 ← getConstInfo eqs[0]!
      let ci1 ← getConstInfo eqs[1]!
      let res ← forallTelescopeReducing ci0.type fun _ b0 =>
        forallTelescopeReducing ci1.type fun _ b1 => do
          let a0 := b0.getAppArgs
          let a1 := b1.getAppArgs
          if !(b0.getAppFn.isConstOf `Eq && a0.size == 3 && b1.getAppFn.isConstOf `Eq && a1.size == 3) then
            fail "unexpected equation lemma shape"
          let l0 := a0[1]!.consumeMData.getAppArgs
          let r0 := a0[2]!.consumeMData
          let l1 := a1[1]!.consumeMData.getAppArgs
          let r1 := a1[2]!.consumeMData
          if l0.size != paramTypes.size || l1.size != paramTypes.size then
            fail "mismatched arity in 2-equation pattern match"
          -- Find the unique discriminating position `discIdx`
          let mut discIdx? : Option Nat := none
          for i in [:l0.size] do
            if !l0[i]!.consumeMData.isFVar || !l1[i]!.consumeMData.isFVar then
              match discIdx? with
              | none => discIdx? := some i
              | some _ => fail "multi-column pattern matching is not supported"
          let some disc := discIdx?
            | fail "2 equations with no pattern discriminator"
          -- Check Nat `0` / `n + 1` (either order)
          let is01 := (← isZeroArg l0[disc]!) && (← asSuccFVar? l1[disc]!).isSome
          let is10 := (← isZeroArg l1[disc]!) && (← asSuccFVar? l0[disc]!).isSome
          if is01 || is10 then
            let (lZ, rZ, lS, rS) := if is01 then (l0, r0, l1, r1) else (l1, r1, l0, r0)
            let some predFid ← asSuccFVar? lS[disc]! | fail "internal error"
            -- Build canonical parameter names from the succ equation
            let mut pnames : List String := []
            let mut mapZ : Std.HashMap FVarId String := {}
            let mut mapS : Std.HashMap FVarId String := {}
            for i in [:lS.size] do
              if i == disc then
                let vnm := freshVar `n pnames
                pnames := pnames ++ [vnm]
                mapS := mapS.insert predFid s!"({vnm} - 1)"
              else
                match lS[i]!.consumeMData, lZ[i]!.consumeMData with
                | .fvar fs, .fvar fz =>
                  let ldecl ← fs.getDecl
                  let vnm := freshVar ldecl.userName pnames
                  pnames := pnames ++ [vnm]
                  mapS := mapS.insert fs vnm
                  mapZ := mapZ.insert fz vnm
                | _, _ => fail "non-variable argument outside discriminator column"
            let discName := pnames[disc]!
            let (lz, sz) ← trExpr mapZ pnames false rZ
            let (ls, ss) ← trExpr mapS pnames false rS
            if !lz.isEmpty || !ls.isEmpty then
              fail "cannot hoist let-binding out of Nat pattern-match branch"
            return s!"def {onm}({String.intercalate ", " pnames}) \{\n    if {discName} == 0 then {sz}\n    else {ss}\n}"
          fail "only 2-case `Nat` (`0` / `n + 1`) pattern matches are supported"
      return res

    fail s!"{eqs.size}-branch pattern match is not supported (write explicit `if`/`else` or 2-case `Nat` recursion)"

  | .axiomInfo _   => fail "axioms cannot be translated"
  | .opaqueInfo _  => fail "opaque or `partial` definitions cannot be translated"
  | .thmInfo _     => fail "theorems are proofs, not specifications"
  | .inductInfo _  => fail "custom inductive types are not supported in OdeSpecL"
  | _              => fail "unsupported declaration kind"

/-- Resolve a requested `--def` name against the module's user definitions (exact or unique suffix). -/
def resolveDefName (locals : List Name) (query : String) : Except String Name :=
  let exact := locals.filter fun n => n.toString == query
  if exact.length == 1 then .ok exact.head!
  else
    let suffix := locals.filter fun n =>
      match n with
      | .str _ s => s == query
      | _ => false
    if suffix.length == 1 then .ok suffix.head!
    else if suffix.length > 1 then
      .error s!"ambiguous `--def {query}`; matches: {suffix.map Name.toString}"
    else
      .error s!"definition `{query}` not found in file"

def isUserDefName (n : Name) : Bool :=
  if n.isInternal then false
  else
    let s := n.toString
    (s.splitOn "._").length == 1 && !s.endsWith ".eq_1" && !s.endsWith ".eq_2" &&
    !s.endsWith ".eq_def" && !s.endsWith ".match_1" && !s.endsWith ".induct"

/-- Translate requested roots and all their local dependencies in exact topological post-order
    (dependencies always emitted before dependents; mutual recursion rejected loudly). -/
partial def translateAll (roots : List Name) (localsList : List Name) : MetaM (Except String String) := do
  let mut localSet : NameSet := {}
  for n in localsList do
    localSet := localSet.insert n
  let initState : TrState := {
    locals := localSet
    deps := []
    curDef := roots.headD Name.anonymous
    lifted := []
    liftIdx := 0
    odeNames := {}
    usedNames := {}
  }
  let rec visit (nm : Name) (visiting : NameSet) (done : NameSet) (acc : List String)
      : TrM (NameSet × List String) := do
    if done.contains nm then
      return (done, acc)
    if visiting.contains nm then
      modify fun s => { s with curDef := nm }
      fail "mutual recursion across definitions is not supported in OdeSpecL"
    modify fun s => { s with deps := [], lifted := [] }
    let defTxt ← translateDef nm
    let myDeps := (← get).deps
    let myLifted := (← get).lifted
    let chunk := String.intercalate "\n\n" (myLifted ++ [defTxt])
    let visiting' := visiting.insert nm
    let mut done' := done
    let mut acc' := acc
    for d in myDeps do
      let (d2, a2) ← visit d visiting' done' acc'
      done' := d2
      acc' := a2
    return (done'.insert nm, acc' ++ [chunk])

  let action : TrM String := do
    let mut done : NameSet := {}
    let mut acc : List String := []
    for r in roots do
      let (d2, a2) ← visit r {} done acc
      done := d2
      acc := a2
    return String.intercalate "\n\n" acc
  try
    let (out, _) ← action.run initState
    return .ok out
  catch e =>
    return .error (← e.toMessageData.toString)

end Lean2Ode

unsafe def main (args : List String) : IO UInt32 := do
  let mut filePath? : Option String := none
  let mut reqDefs : List String := []
  let mut doAll := false
  let mut outPath? : Option String := none
  let mut i := 0
  let arr := args.toArray
  while i < arr.size do
    let a := arr[i]!
    if a == "--def" && i + 1 < arr.size then
      reqDefs := reqDefs ++ [arr[i + 1]!]
      i := i + 2
    else if a == "--all" then
      doAll := true
      i := i + 1
    else if a == "--out" && i + 1 < arr.size then
      outPath? := some arr[i + 1]!
      i := i + 2
    else if a == "--help" || a == "-h" then
      IO.println "Usage: lean2ode FILE.lean [--def NAME ...] [--all] [--out OUT.spec]"
      return 0
    else if !a.startsWith "-" && filePath?.isNone then
      filePath? := some a
      i := i + 1
    else
      IO.eprintln s!"lean2ode: unrecognized argument `{a}`"
      return 2

  let some filePath := filePath? | do
    IO.eprintln "Usage: lean2ode FILE.lean [--def NAME ...] [--all] [--out OUT.spec]"
    return 2

  Lean.enableInitializersExecution
  let sysroot ← do
    match ← IO.getEnv "LEAN_SYSROOT" with
    | some s => pure (System.FilePath.mk s)
    | none =>
      try
        Lean.findSysroot
      catch _ =>
        -- Fall back to finding Lean's sysroot from lean2ode's own directory (holds `lean-toolchain`)
        let appDir := (← IO.appPath).parent.getD (System.FilePath.mk ".")
        let pkgDir := appDir / ".." / ".." / ".."
        let out ← IO.Process.output { cmd := "lean", args := #["--print-prefix"], cwd := some pkgDir }
        if out.exitCode != 0 then
          throw (IO.userError s!"lean2ode: cannot locate Lean sysroot (set LEAN_SYSROOT): {out.stderr}")
        pure (System.FilePath.mk out.stdout.trimAscii.toString)
  Lean.initSearchPath sysroot
  let input ← IO.FS.readFile filePath
  let some env ← Lean.Elab.runFrontend input {} filePath `Lean2OdeInput | do
    IO.eprintln s!"lean2ode: Lean 4 elaboration failed for `{filePath}`"
    return 1

  -- Collect all user `def`s defined in the main module (not imported stdlib!)
  let mut locals : List Name := []
  for (nm, ci) in env.constants.map₂.toList do
    if Lean2Ode.isUserDefName nm then
      match ci with
      | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ => locals := nm :: locals
      | _ => pure ()
  locals := locals.reverse

  let roots ←
    if doAll then
      if locals.isEmpty then
        IO.eprintln s!"lean2ode: no definitions found in `{filePath}`"
        return 1
      pure locals
    else if reqDefs.isEmpty then
      IO.eprintln "lean2ode: specify at least one `--def NAME` or `--all`"
      return 2
    else do
      let mut resolved : List Name := []
      for q in reqDefs do
        match Lean2Ode.resolveDefName locals q with
        | .ok nm => resolved := resolved ++ [nm]
        | .error msg =>
          IO.eprintln s!"lean2ode: {msg}"
          return 1
      pure resolved

  let coreCtx : Core.Context := { fileName := filePath, fileMap := FileMap.ofString input }
  let coreState : Core.State := { env := env }
  match ← ((Lean2Ode.translateAll roots locals).run' {} {} |>.run' coreCtx coreState).toIO' with
  | .error e =>
    IO.eprintln s!"lean2ode: internal error: {← e.toMessageData.toString}"
    return 1
  | .ok (.error msg) =>
    IO.eprintln msg
    return 1
  | .ok (.ok specText) =>
    let baseName := (System.FilePath.mk filePath).fileName.getD filePath
    let header := s!"// Automatically translated from `{baseName}` by lean2ode.\n\n"
    let full := header ++ specText ++ "\n"
    match outPath? with
    | some p => IO.FS.writeFile p full
    | none   => IO.print full
    return 0
