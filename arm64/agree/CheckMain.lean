import Table
import Machine
import Agree

/-! Checks that `Agree.lean`'s row effects match `../arm64.tab` as `Ode.readTable` parses it,
checks `Ode.findRow` / `Ode.regOf` / `Ode.vecOf` / `Ode.readInt` on concrete instances, and
(with `--words`) prints encoded 32-bit words for cross-checking against `../word.py`. -/

def hex32 (w : BitVec 32) : String :=
  let digits := "0123456789abcdef".toList
  let rec go (k : Nat) (v : Nat) (acc : List Char) : List Char :=
    match k with
    | 0 => acc
    | k' + 1 => go k' (v / 16) (digits.getD (v % 16) '0' :: acc)
  String.ofList (go 8 w.toNat [])

def checkRow (table : Array Ode.TRow) (name : String) (eff : List Ode.Stmt) : IO Unit := do
  match table.find? (fun r => r.name == name) with
  | none => throw (IO.userError s!"missing row {name} in arm64.tab")
  | some row =>
    if reprStr row.effect != reprStr eff then
      throw (IO.userError s!"effect mismatch for {name}:\n  table: {reprStr row.effect}\n  agree: {reprStr eff}")

def parseOne (s : String) : IO (List Ode.Sexp) :=
  match Ode.parseSexp s with
  | some [Ode.Sexp.list xs] => pure xs
  | _ => throw (IO.userError s!"cannot parse sexp: {s}")

def checkInstance (table : Array Ode.TRow) (wantRow : String) (sexp : String)
    (check : Ode.Bind → Bool) : IO Unit := do
  let xs ← parseOne sexp
  match Ode.findRow table xs with
  | none => throw (IO.userError s!"findRow failed for {sexp}")
  | some (row, bind) =>
    if row.name != wantRow then
      throw (IO.userError s!"wrong row for {sexp}: got {row.name}, expected {wantRow}")
    if !check bind then
      throw (IO.userError s!"binding check failed for {sexp}")

def main (args : List String) : IO Unit := do
  let wordsOnly := args.contains "--words"
  let tabPath := (args.filter (fun a => a != "--words")).headD "../arm64.tab"
  let text ← IO.FS.readFile tabPath
  let table ← match Ode.readTable text with
    | .ok t => pure t
    | .error e => throw (IO.userError s!"readTable failed: {e}")

  -- 1. Check that each proved row's AST matches arm64.tab verbatim.
  checkRow table "add_rrr" ArmAgree.effectAddRrr
  checkRow table "ldr64_sp" ArmAgree.effectLdr64Sp
  checkRow table "eor_v" ArmAgree.effectEorV
  checkRow table "rev32_8h" ArmAgree.effectRev32

  -- 2. Check Ode.findRow and register/immediate lookup for all 31/32 register indices.
  for i in List.range 31 do
    let s := (i + 7) % 31
    let p := (i + 19) % 31
    let ins := s!"(.add .x{i} .x{s} .x{p})"
    checkInstance table "add_rrr" ins (fun b =>
      Ode.regOf b "D" == some (ArmAgree.armSlot i) &&
      Ode.regOf b "S" == some (ArmAgree.armSlot s) &&
      Ode.regOf b "P" == some (ArmAgree.armSlot p))
    if hi : i < 31 then
      if wordsOnly then
        let w := ArmAgree.encodeAddRrr ⟨i, hi⟩ ⟨s, Nat.mod_lt _ (by decide)⟩ ⟨p, Nat.mod_lt _ (by decide)⟩
        IO.println s!"add_rrr {hex32 w} {ins}"

  let offsets : List Nat := [0, 1, 2, 3, 7, 15, 64, 511, 2048, 4095]
  for i in List.range 31 do
    for n in offsets do
      if i == 0 || i == 1 || i == 29 || i == 30 || n == 2 then
        let ins := s!"(.ldr64_sp .x{i} {n * 8})"
        checkInstance table "ldr64_sp" ins (fun b =>
          Ode.regOf b "D" == some (ArmAgree.armSlot i) &&
          match b.find? (fun kv => kv.1 == "N") with
          | some (_, v) => Ode.readInt v == some (n * 8)
          | none => false)
        if hi : i < 31 then
          if hn : n < 4096 then
            if wordsOnly then
              let w := ArmAgree.encodeLdr64Sp ⟨i, hi⟩ ⟨n, hn⟩
              IO.println s!"ldr64_sp {hex32 w} {ins}"

  for i in List.range 32 do
    let y := (i + 5) % 32
    let z := (i + 17) % 32
    let insE := s!"(.eor {i} {y} {z})"
    checkInstance table "eor_v" insE (fun b =>
      Ode.vecOf b "X" == some i && Ode.vecOf b "Y" == some y && Ode.vecOf b "Z" == some z)
    let insR := s!"(.rev32 {i} {y})"
    checkInstance table "rev32_8h" insR (fun b =>
      Ode.vecOf b "X" == some i && Ode.vecOf b "Y" == some y)
    if hi : i < 32 then
      if wordsOnly then
        let wE := ArmAgree.encodeEorV ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩
        IO.println s!"eor_v {hex32 wE} {insE}"
        let wR := ArmAgree.encodeRev32 ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩
        IO.println s!"rev32_8h {hex32 wR} {insR}"

  if !wordsOnly then
    IO.println "agree-check: 4 rows match arm64.tab"
