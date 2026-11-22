import Machine
/-!
The machine as a program:  `odemachine TABLE CASES`

For the comparison of `Machine.lean` with `../core/conc.py` (test_machine.py). A line of CASES is one
instruction run from one state:

    c BASE NEXT UNKNOWN ZF CF R0 … R15 START BYTES LANES | ROW…

BYTES are the bytes of memory from START, in hexadecimal; everything may be read and written. LANES are the
vector registers' lanes, eight hexadecimal digits each, sixteen a register, register 0 first (none: all
zero); after the thirty-two vector registers come the eight mask registers, a bit a lane. The answer is a
line: `next` or `returned`, then the instruction pointer, the two flags, the sixteen registers, the bytes of
memory from START, and all sixteen lanes of each of the 32 vector registers and the 8 mask registers; or
`none` where the row has no meaning here; or `norow`.
-/
open Ode

def parseHex (s : String) : Array Nat :=
  let cs := s.toList.toArray
  (Array.range (cs.size / 2)).map fun i => (hexDigit cs[2 * i]!).getD 0 * 16 + (hexDigit cs[2 * i + 1]!).getD 0

def toHex2 (n : Nat) : String :=
  let d := "0123456789abcdef".toList.toArray
  String.ofList [d[n / 16 % 16]!, d[n % 16]!]

/-- Numbers of eight hexadecimal digits each. -/
def parseWords (s : String) : Array Nat :=
  let b := parseHex s
  (Array.range (b.size / 4)).map fun i => ((b[4 * i]! * 256 + b[4 * i + 1]!) * 256 + b[4 * i + 2]!) * 256 + b[4 * i + 3]!

def toHex8 (n : Nat) : String := toHex2 (n / 16777216 % 256) ++ toHex2 (n / 65536 % 256) ++ toHex2 (n / 256 % 256) ++ toHex2 (n % 256)

def runCase (table : Array TRow) (line : String) : String :=
  match line.splitOn " | " with
  | [head, rowText] =>
    match (head.splitOn " ").filter (· ≠ "") with
    | "c" :: base :: next :: u :: zf :: cf :: more =>
      let regs := ((more.take 16).map String.toNat!).toArray
      let start := (more.getD 16 "0").toNat!
      let bytes := parseHex (more.getD 17 "")
      let vecs := parseWords (more.getD 18 "")
      match parseSexp rowText with
      | some ins =>
        match findRow table ins with
        | some (row, bind) =>
          let s : State := { reg := fun k => regs.getD k 0, zf := zf == "1", cf := cf == "1", rip := 0, vec := fun x k => vecs.getD (16 * x + k) 0, data := fun _ => 0,
                             mem := fun a => ⟨(if start ≤ a ∧ a < start + bytes.size then bytes[a - start]! else 0) % 256, Nat.mod_lt _ (by decide)⟩ }
          let perm : Perm := ⟨fun _ => true, fun _ => true⟩
          match exec perm ⟨"", base.toNat!, []⟩ ⟨row.effect, bind, next.toNat!⟩ (fun _ => u.toNat!) s with
          | none => "none"
          | some o =>
            let (kind, s') := match o with
              | .next s' => ("next", s')
              | .returned s' => ("returned", s')
            let regsOut := " ".intercalate ((List.range 16).map fun k => toString (s'.reg k))
            let memOut := String.join ((List.range bytes.size).map fun k => toHex2 (s'.mem (start + k)))
            let vecOut := String.join ((List.range 40).map fun x => String.join ((List.range 16).map fun k => toHex8 (s'.vec x k)))
            s!"{kind} {s'.rip} {if s'.zf then 1 else 0} {if s'.cf then 1 else 0} {regsOut} {memOut} {vecOut}"
        | none => "norow"
      | none => "unreadable"
    | _ => "unreadable"
  | _ => "unreadable"

def main (args : List String) : IO UInt32 := do
  match args with
  | [tablePath, casesPath] =>
    let table ← match readTable (← IO.FS.readFile tablePath) with
      | .ok t => pure t
      | .error e => IO.println e; return 2
    for l in ((← IO.FS.readFile casesPath).splitOn "\n").filter (· ≠ "") do
      IO.println (runCase table l)
    return 0
  | _ => IO.println "odemachine TABLE CASES"; return 2
