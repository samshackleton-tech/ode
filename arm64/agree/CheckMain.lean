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

  -- 1. Check that each proved row's AST matches arm64.tab verbatim (20 of 36 rows).
  checkRow table "add_rrr" ArmAgree.effectAddRrr
  checkRow table "ldr64_sp" ArmAgree.effectLdr64Sp
  checkRow table "eor_v" ArmAgree.effectEorV
  checkRow table "rev32_8h" ArmAgree.effectRev32
  checkRow table "ldrb" ArmAgree.effectLdrb
  checkRow table "cmp_rr" ArmAgree.effectCmpRr
  checkRow table "b_hs" ArmAgree.effectBHs
  checkRow table "b_lo" ArmAgree.effectBLo
  checkRow table "nop" ArmAgree.effectNop
  checkRow table "mov_ri" ArmAgree.effectMovRi
  checkRow table "mov32_ri" ArmAgree.effectMovRi
  checkRow table "mov_rr" ArmAgree.effectMovRr
  checkRow table "add_rri" ArmAgree.effectAddRri
  checkRow table "sub_rri" ArmAgree.effectSubRri
  checkRow table "sub_rrr" ArmAgree.effectSubRrr
  checkRow table "cmp_ri" ArmAgree.effectCmpRi
  checkRow table "b" ArmAgree.effectB
  checkRow table "b_eq" ArmAgree.effectBEq
  checkRow table "b_ne" ArmAgree.effectBNe
  checkRow table "strb" ArmAgree.effectStrb

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

  let ldrbOffsets : List Nat := [0, 1, 7, 31, 63, 1024, 4095]
  for i in List.range 31 do
    let b := (i + 11) % 31
    for n in ldrbOffsets do
      if i == 0 || i == 4 || i == 30 || n == 7 then
        let ins := s!"(.ldrb .x{i} .x{b} {n})"
        checkInstance table "ldrb" ins (fun bd =>
          Ode.regOf bd "D" == some (ArmAgree.armSlot i) &&
          Ode.regOf bd "B" == some (ArmAgree.armSlot b) &&
          match bd.find? (fun kv => kv.1 == "N") with
          | some (_, v) => Ode.readInt v == some (n : Int)
          | none => false)
        if hi : i < 31 then
          if hn : n < 4096 then
            if wordsOnly then
              let w := ArmAgree.encodeLdrb ⟨i, hi⟩ ⟨b, Nat.mod_lt _ (by decide)⟩ ⟨n, hn⟩
              IO.println s!"ldrb {hex32 w} {ins}"

  for i in List.range 31 do
    let p := (i + 13) % 31
    let ins := s!"(.cmp .x{i} .x{p})"
    checkInstance table "cmp_rr" ins (fun bd =>
      Ode.regOf bd "S" == some (ArmAgree.armSlot i) &&
      Ode.regOf bd "P" == some (ArmAgree.armSlot p))
    if hi : i < 31 then
      if wordsOnly then
        let w := ArmAgree.encodeCmpRr ⟨i, hi⟩ ⟨p, Nat.mod_lt _ (by decide)⟩
        IO.println s!"cmp_rr {hex32 w} {ins}"

  let branchDeltas : List Int := [0, 4, 16, 64, 1024, -4, -12, -28, -512]
  for delta in branchDeltas do
    let insHs := s!"(.bhs {delta})"
    checkInstance table "b_hs" insHs (fun bd =>
      match bd.find? (fun kv => kv.1 == "I") with
      | some (_, v) => Ode.readInt v == some delta
      | none => false)
    let insLo := s!"(.blo {delta})"
    checkInstance table "b_lo" insLo (fun bd =>
      match bd.find? (fun kv => kv.1 == "I") with
      | some (_, v) => Ode.readInt v == some delta
      | none => false)
    if wordsOnly then
      let q : Int := delta / 4
      let imm19 : BitVec 19 := BitVec.ofInt 19 q
      let imm26 : BitVec 26 := BitVec.ofInt 26 q
      IO.println s!"b_hs {hex32 (ArmAgree.encodeBHs imm19)} {insHs}"
      IO.println s!"b_lo {hex32 (ArmAgree.encodeBLo imm19)} {insLo}"
      IO.println s!"b {hex32 (ArmAgree.encodeB imm26)} (.b {delta})"
      IO.println s!"b_eq {hex32 (ArmAgree.encodeBEq imm19)} (.beq {delta})"
      IO.println s!"b_ne {hex32 (ArmAgree.encodeBNe imm19)} (.bne {delta})"
    checkInstance table "b" s!"(.b {delta})" (fun bd =>
      match bd.find? (fun kv => kv.1 == "I") with
      | some (_, v) => Ode.readInt v == some delta
      | none => false)
    checkInstance table "b_eq" s!"(.beq {delta})" (fun bd =>
      match bd.find? (fun kv => kv.1 == "I") with
      | some (_, v) => Ode.readInt v == some delta
      | none => false)
    checkInstance table "b_ne" s!"(.bne {delta})" (fun bd =>
      match bd.find? (fun kv => kv.1 == "I") with
      | some (_, v) => Ode.readInt v == some delta
      | none => false)

  checkInstance table "nop" "(.nop)" (fun _ => true)
  if wordsOnly then
    IO.println s!"nop {hex32 ArmAgree.encodeNop} (.nop)"

  let movImms : List Nat := [0, 1, 64, 1024, 65535]
  for i in List.range 31 do
    for imm in movImms do
      if i == 0 || i == 7 || i == 30 || imm == 64 then
        let ins64 := s!"(.movi .x{i} {imm})"
        checkInstance table "mov_ri" ins64 (fun bd =>
          Ode.regOf bd "D" == some (ArmAgree.armSlot i) &&
          match bd.find? (fun kv => kv.1 == "I") with
          | some (_, v) => Ode.readInt v == some (imm : Int)
          | none => false)
        let ins32 := s!"(.movi32 .x{i} {imm})"
        checkInstance table "mov32_ri" ins32 (fun bd =>
          Ode.regOf bd "D" == some (ArmAgree.armSlot i) &&
          match bd.find? (fun kv => kv.1 == "I") with
          | some (_, v) => Ode.readInt v == some (imm : Int)
          | none => false)
        if hi : i < 31 then
          if himm : imm < 65536 then
            if wordsOnly then
              IO.println s!"mov_ri {hex32 (ArmAgree.encodeMovRi ⟨i, hi⟩ ⟨imm, himm⟩)} {ins64}"
              IO.println s!"mov32_ri {hex32 (ArmAgree.encodeMov32Ri ⟨i, hi⟩ ⟨imm, himm⟩)} {ins32}"

  for i in List.range 31 do
    let s := (i + 9) % 31
    let p := (i + 23) % 31
    let insM := s!"(.mov .x{i} .x{s})"
    checkInstance table "mov_rr" insM (fun bd =>
      Ode.regOf bd "D" == some (ArmAgree.armSlot i) &&
      Ode.regOf bd "S" == some (ArmAgree.armSlot s))
    let insSub := s!"(.sub .x{i} .x{s} .x{p})"
    checkInstance table "sub_rrr" insSub (fun bd =>
      Ode.regOf bd "D" == some (ArmAgree.armSlot i) &&
      Ode.regOf bd "S" == some (ArmAgree.armSlot s) &&
      Ode.regOf bd "P" == some (ArmAgree.armSlot p))
    if hi : i < 31 then
      if wordsOnly then
        IO.println s!"mov_rr {hex32 (ArmAgree.encodeMovRr ⟨i, hi⟩ ⟨s, Nat.mod_lt _ (by decide)⟩)} {insM}"
        IO.println s!"sub_rrr {hex32 (ArmAgree.encodeSubRrr ⟨i, hi⟩ ⟨s, Nat.mod_lt _ (by decide)⟩ ⟨p, Nat.mod_lt _ (by decide)⟩)} {insSub}"

  let imm12s : List Nat := [0, 1, 8, 64, 1024, 4095]
  for i in List.range 31 do
    let s := (i + 3) % 31
    for imm in imm12s do
      if i == 0 || i == 2 || i == 30 || imm == 1 then
        let insAdd := s!"(.addi .x{i} .x{s} {imm})"
        checkInstance table "add_rri" insAdd (fun bd =>
          Ode.regOf bd "D" == some (ArmAgree.armSlot i) &&
          Ode.regOf bd "S" == some (ArmAgree.armSlot s) &&
          match bd.find? (fun kv => kv.1 == "I") with
          | some (_, v) => Ode.readInt v == some (imm : Int)
          | none => false)
        let insSub := s!"(.subi .x{i} .x{s} {imm})"
        checkInstance table "sub_rri" insSub (fun bd =>
          Ode.regOf bd "D" == some (ArmAgree.armSlot i) &&
          Ode.regOf bd "S" == some (ArmAgree.armSlot s) &&
          match bd.find? (fun kv => kv.1 == "I") with
          | some (_, v) => Ode.readInt v == some (imm : Int)
          | none => false)
        let insCmp := s!"(.cmpi .x{i} {imm})"
        checkInstance table "cmp_ri" insCmp (fun bd =>
          Ode.regOf bd "S" == some (ArmAgree.armSlot i) &&
          match bd.find? (fun kv => kv.1 == "I") with
          | some (_, v) => Ode.readInt v == some (imm : Int)
          | none => false)
        let insStrb := s!"(.strb .x{i} .x{s} {imm})"
        checkInstance table "strb" insStrb (fun bd =>
          Ode.regOf bd "S" == some (ArmAgree.armSlot i) &&
          Ode.regOf bd "B" == some (ArmAgree.armSlot s) &&
          match bd.find? (fun kv => kv.1 == "N") with
          | some (_, v) => Ode.readInt v == some (imm : Int)
          | none => false)
        if hi : i < 31 then
          if himm : imm < 4096 then
            if wordsOnly then
              IO.println s!"add_rri {hex32 (ArmAgree.encodeAddRri ⟨i, hi⟩ ⟨s, Nat.mod_lt _ (by decide)⟩ ⟨imm, himm⟩)} {insAdd}"
              IO.println s!"sub_rri {hex32 (ArmAgree.encodeSubRri ⟨i, hi⟩ ⟨s, Nat.mod_lt _ (by decide)⟩ ⟨imm, himm⟩)} {insSub}"
              IO.println s!"cmp_ri {hex32 (ArmAgree.encodeCmpRi ⟨i, hi⟩ ⟨imm, himm⟩)} {insCmp}"
              IO.println s!"strb {hex32 (ArmAgree.encodeStrb ⟨i, hi⟩ ⟨s, Nat.mod_lt _ (by decide)⟩ ⟨imm, himm⟩)} {insStrb}"

  if !wordsOnly then
    IO.println "agree-check: 20 rows match arm64.tab"
