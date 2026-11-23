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

  -- 1. Check that ALL 47 rows of arm64.tab match Agree.lean's effect ASTs verbatim.
  if table.size != 47 then
    throw (IO.userError s!"expected 47 rows in arm64.tab, found {table.size}")
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
  checkRow table "add_sp" ArmAgree.effectAddSp
  checkRow table "sub_sp" ArmAgree.effectSubSp
  checkRow table "add_of_sp" ArmAgree.effectAddOfSp
  checkRow table "ldr64" ArmAgree.effectLdr64
  checkRow table "str64" ArmAgree.effectStr64
  checkRow table "ldr32" ArmAgree.effectLdr32
  checkRow table "str32" ArmAgree.effectStr32
  checkRow table "str64_sp" ArmAgree.effectStr64Sp
  checkRow table "bl" ArmAgree.effectBl
  checkRow table "ret" ArmAgree.effectRet
  checkRow table "orr_v" ArmAgree.effectOrrV
  checkRow table "add_4s" ArmAgree.effectAdd4s
  checkRow table "ushr_4s" ArmAgree.effectUshr4s
  checkRow table "shl_4s" ArmAgree.effectShl4s
  checkRow table "ld1_4s" ArmAgree.effectLd1_4s
  checkRow table "st1_4s" ArmAgree.effectSt1_4s
  checkRow table "lsl_ri" ArmAgree.effectLslRi
  checkRow table "fmov_d" ArmAgree.effectFmovD
  checkRow table "uzp1_4s" ArmAgree.effectUzp1_4s
  checkRow table "uzp2_4s" ArmAgree.effectUzp2_4s
  checkRow table "zip1_4s" ArmAgree.effectZip1_4s
  checkRow table "zip2_4s" ArmAgree.effectZip2_4s
  checkRow table "zip1_2d" ArmAgree.effectZip1_2d
  checkRow table "zip2_2d" ArmAgree.effectZip2_2d
  checkRow table "ext_4" ArmAgree.effectExt4
  checkRow table "ext_8" ArmAgree.effectExt8
  checkRow table "ext_12" ArmAgree.effectExt12

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

  for imm in imm12s do
    checkInstance table "add_sp" s!"(.add_sp {imm})" (fun bd =>
      match bd.find? (fun kv => kv.1 == "I") with
      | some (_, v) => Ode.readInt v == some (imm : Int)
      | none => false)
    checkInstance table "sub_sp" s!"(.sub_sp {imm})" (fun bd =>
      match bd.find? (fun kv => kv.1 == "I") with
      | some (_, v) => Ode.readInt v == some (imm : Int)
      | none => false)
    if himm : imm < 4096 then
      if wordsOnly then
        IO.println s!"add_sp {hex32 (ArmAgree.encodeAddSp ⟨imm, himm⟩)} (.add_sp {imm})"
        IO.println s!"sub_sp {hex32 (ArmAgree.encodeSubSp ⟨imm, himm⟩)} (.sub_sp {imm})"

  for i in List.range 31 do
    let b := (i + 5) % 31
    for imm in imm12s do
      if i == 0 || i == 7 || i == 30 || imm == 2 then
        let insAosp := s!"(.add_of_sp .x{i} {imm})"
        checkInstance table "add_of_sp" insAosp (fun bd =>
          Ode.regOf bd "D" == some (ArmAgree.armSlot i) &&
          match bd.find? (fun kv => kv.1 == "I") with
          | some (_, v) => Ode.readInt v == some (imm : Int)
          | none => false)
        let insL64 := s!"(.ldr64 .x{i} .x{b} {imm * 8})"
        checkInstance table "ldr64" insL64 (fun bd =>
          Ode.regOf bd "D" == some (ArmAgree.armSlot i) &&
          Ode.regOf bd "B" == some (ArmAgree.armSlot b) &&
          match bd.find? (fun kv => kv.1 == "N") with
          | some (_, v) => Ode.readInt v == some (imm * 8 : Int)
          | none => false)
        let insS64 := s!"(.str64 .x{i} .x{b} {imm * 8})"
        checkInstance table "str64" insS64 (fun bd =>
          Ode.regOf bd "S" == some (ArmAgree.armSlot i) &&
          Ode.regOf bd "B" == some (ArmAgree.armSlot b) &&
          match bd.find? (fun kv => kv.1 == "N") with
          | some (_, v) => Ode.readInt v == some (imm * 8 : Int)
          | none => false)
        let insL32 := s!"(.ldr32 .x{i} .x{b} {imm * 4})"
        checkInstance table "ldr32" insL32 (fun bd =>
          Ode.regOf bd "D" == some (ArmAgree.armSlot i) &&
          Ode.regOf bd "B" == some (ArmAgree.armSlot b) &&
          match bd.find? (fun kv => kv.1 == "N") with
          | some (_, v) => Ode.readInt v == some (imm * 4 : Int)
          | none => false)
        let insS32 := s!"(.str32 .x{i} .x{b} {imm * 4})"
        checkInstance table "str32" insS32 (fun bd =>
          Ode.regOf bd "S" == some (ArmAgree.armSlot i) &&
          Ode.regOf bd "B" == some (ArmAgree.armSlot b) &&
          match bd.find? (fun kv => kv.1 == "N") with
          | some (_, v) => Ode.readInt v == some (imm * 4 : Int)
          | none => false)
        let insS64Sp := s!"(.str64_sp .x{i} {imm * 8})"
        checkInstance table "str64_sp" insS64Sp (fun bd =>
          Ode.regOf bd "S" == some (ArmAgree.armSlot i) &&
          match bd.find? (fun kv => kv.1 == "N") with
          | some (_, v) => Ode.readInt v == some (imm * 8 : Int)
          | none => false)
        if hi : i < 31 then
          if himm : imm < 4096 then
            if wordsOnly then
              IO.println s!"add_of_sp {hex32 (ArmAgree.encodeAddOfSp ⟨i, hi⟩ ⟨imm, himm⟩)} {insAosp}"
              IO.println s!"ldr64 {hex32 (ArmAgree.encodeLdr64 ⟨i, hi⟩ ⟨b, Nat.mod_lt _ (by decide)⟩ ⟨imm, himm⟩)} {insL64}"
              IO.println s!"str64 {hex32 (ArmAgree.encodeStr64 ⟨i, hi⟩ ⟨b, Nat.mod_lt _ (by decide)⟩ ⟨imm, himm⟩)} {insS64}"
              IO.println s!"ldr32 {hex32 (ArmAgree.encodeLdr32 ⟨i, hi⟩ ⟨b, Nat.mod_lt _ (by decide)⟩ ⟨imm, himm⟩)} {insL32}"
              IO.println s!"str32 {hex32 (ArmAgree.encodeStr32 ⟨i, hi⟩ ⟨b, Nat.mod_lt _ (by decide)⟩ ⟨imm, himm⟩)} {insS32}"
              IO.println s!"str64_sp {hex32 (ArmAgree.encodeStr64Sp ⟨i, hi⟩ ⟨imm, himm⟩)} {insS64Sp}"

  checkInstance table "ret" "(.ret)" (fun _ => true)
  if wordsOnly then
    IO.println s!"ret {hex32 ArmAgree.encodeRet} (.ret)"
  for q in ([0, 1, 5, 1024, 65535] : List Nat) do
    checkInstance table "bl" s!"(.bl {q})" (fun bd =>
      match bd.find? (fun kv => kv.1 == "I") with
      | some (_, v) => Ode.readInt v == some (q : Int)
      | none => false)
    if wordsOnly then
      IO.println s!"bl {hex32 (ArmAgree.encodeBl (BitVec.ofNat 26 q))} (.bl {q})"

  let shiftVals : List Nat := [0, 1, 7, 8, 12, 16, 24, 31]
  for i in List.range 32 do
    let y := (i + 7) % 32
    let z := (i + 19) % 32
    let b := i % 31
    let insO := s!"(.orr {i} {y} {z})"
    checkInstance table "orr_v" insO (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y && Ode.vecOf bd "Z" == some z)
    let insA := s!"(.add4s {i} {y} {z})"
    checkInstance table "add_4s" insA (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y && Ode.vecOf bd "Z" == some z)
    let insLd := s!"(.ld1 {i} .x{b})"
    checkInstance table "ld1_4s" insLd (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.regOf bd "B" == some (ArmAgree.armSlot b))
    let insSt := s!"(.st1 {i} .x{b})"
    checkInstance table "st1_4s" insSt (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.regOf bd "B" == some (ArmAgree.armSlot b))
    if hi : i < 32 then
      if wordsOnly then
        IO.println s!"orr_v {hex32 (ArmAgree.encodeOrrV ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩)} {insO}"
        IO.println s!"add_4s {hex32 (ArmAgree.encodeAdd4s ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩)} {insA}"
        IO.println s!"ld1_4s {hex32 (ArmAgree.encodeLd1_4s ⟨i, hi⟩ ⟨b, Nat.mod_lt _ (by decide)⟩)} {insLd}"
        IO.println s!"st1_4s {hex32 (ArmAgree.encodeSt1_4s ⟨i, hi⟩ ⟨b, Nat.mod_lt _ (by decide)⟩)} {insSt}"
      for sh in shiftVals do
        if i == 0 || i == 15 || i == 31 || sh == 16 then
          let insUshr := s!"(.ushr {i} {y} {32 - sh})"
          checkInstance table "ushr_4s" insUshr (fun bd =>
            Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y &&
            match bd.find? (fun kv => kv.1 == "I") with
            | some (_, v) => Ode.readInt v == some ((32 - sh : Nat) : Int)
            | none => false)
          let insShl := s!"(.shl {i} {y} {sh})"
          checkInstance table "shl_4s" insShl (fun bd =>
            Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y &&
            match bd.find? (fun kv => kv.1 == "I") with
            | some (_, v) => Ode.readInt v == some (sh : Int)
            | none => false)
          if hsh : sh < 32 then
            if wordsOnly then
              IO.println s!"ushr_4s {hex32 (ArmAgree.encodeUshr4s ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨sh, hsh⟩)} {insUshr}"
              IO.println s!"shl_4s {hex32 (ArmAgree.encodeShl4s ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨sh, hsh⟩)} {insShl}"

  let lslShifts : List Nat := [0, 1, 7, 15, 31, 47, 62]
  for i in List.range 31 do
    let s := (i + 7) % 31
    for sh in lslShifts do
      if i == 0 || i == 9 || i == 30 || sh == 31 then
        let insLsl := s!"(.lsl .x{i} .x{s} {sh + 1})"
        checkInstance table "lsl_ri" insLsl (fun bd =>
          Ode.regOf bd "D" == some (ArmAgree.armSlot i) &&
          Ode.regOf bd "S" == some (ArmAgree.armSlot s) &&
          match bd.find? (fun kv => kv.1 == "I") with
          | some (_, v) => Ode.readInt v == some ((sh + 1 : Nat) : Int)
          | none => false)
        if hi : i < 31 then
          if hsh : sh < 63 then
            if wordsOnly then
              IO.println s!"lsl_ri {hex32 (ArmAgree.encodeLslRi ⟨i, hi⟩ ⟨s, Nat.mod_lt _ (by decide)⟩ ⟨sh, hsh⟩)} {insLsl}"

  for i in List.range 32 do
    let y := (i + 5) % 32
    let z := (i + 13) % 32
    let s := i % 31
    let insFm := s!"(.fmovd {i} .x{s})"
    checkInstance table "fmov_d" insFm (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.regOf bd "S" == some (ArmAgree.armSlot s))
    let insUzp1 := s!"(.uzp1_4s {i} {y} {z})"
    checkInstance table "uzp1_4s" insUzp1 (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y && Ode.vecOf bd "Z" == some z)
    let insUzp2 := s!"(.uzp2_4s {i} {y} {z})"
    checkInstance table "uzp2_4s" insUzp2 (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y && Ode.vecOf bd "Z" == some z)
    let insZip1 := s!"(.zip1_4s {i} {y} {z})"
    checkInstance table "zip1_4s" insZip1 (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y && Ode.vecOf bd "Z" == some z)
    let insZip2 := s!"(.zip2_4s {i} {y} {z})"
    checkInstance table "zip2_4s" insZip2 (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y && Ode.vecOf bd "Z" == some z)
    let insZip1d := s!"(.zip1_2d {i} {y} {z})"
    checkInstance table "zip1_2d" insZip1d (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y && Ode.vecOf bd "Z" == some z)
    let insZip2d := s!"(.zip2_2d {i} {y} {z})"
    checkInstance table "zip2_2d" insZip2d (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y && Ode.vecOf bd "Z" == some z)
    let insExt4 := s!"(.ext4 {i} {y} {z})"
    checkInstance table "ext_4" insExt4 (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y && Ode.vecOf bd "Z" == some z)
    let insExt8 := s!"(.ext8 {i} {y} {z})"
    checkInstance table "ext_8" insExt8 (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y && Ode.vecOf bd "Z" == some z)
    let insExt12 := s!"(.ext12 {i} {y} {z})"
    checkInstance table "ext_12" insExt12 (fun bd =>
      Ode.vecOf bd "X" == some i && Ode.vecOf bd "Y" == some y && Ode.vecOf bd "Z" == some z)
    if hi : i < 32 then
      if wordsOnly then
        IO.println s!"fmov_d {hex32 (ArmAgree.encodeFmovD ⟨i, hi⟩ ⟨s, Nat.mod_lt _ (by decide)⟩)} {insFm}"
        IO.println s!"uzp1_4s {hex32 (ArmAgree.encodeUzp1_4s ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩)} {insUzp1}"
        IO.println s!"uzp2_4s {hex32 (ArmAgree.encodeUzp2_4s ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩)} {insUzp2}"
        IO.println s!"zip1_4s {hex32 (ArmAgree.encodeZip1_4s ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩)} {insZip1}"
        IO.println s!"zip2_4s {hex32 (ArmAgree.encodeZip2_4s ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩)} {insZip2}"
        IO.println s!"zip1_2d {hex32 (ArmAgree.encodeZip1_2d ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩)} {insZip1d}"
        IO.println s!"zip2_2d {hex32 (ArmAgree.encodeZip2_2d ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩)} {insZip2d}"
        IO.println s!"ext_4 {hex32 (ArmAgree.encodeExt4 ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩)} {insExt4}"
        IO.println s!"ext_8 {hex32 (ArmAgree.encodeExt8 ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩)} {insExt8}"
        IO.println s!"ext_12 {hex32 (ArmAgree.encodeExt12 ⟨i, hi⟩ ⟨y, Nat.mod_lt _ (by decide)⟩ ⟨z, Nat.mod_lt _ (by decide)⟩)} {insExt12}"

  if !wordsOnly then
    IO.println "agree-check: all 47 rows match arm64.tab"
