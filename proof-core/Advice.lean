import Core
/-!
Advice for a PROVER's helper. Nobody relies on this file, and `odeverify` is built without it.

Before an `ensures` of a run of words, and before a call, the proof file may give rows for the verifier
to show from the facts and then keep among them (`know` items; `symKnow` in Core.lean). Which rows are
worth giving is found here, for `odeprove` to print where a proof that is still being written has run
out at such a point (`need know`): the prover then tries to show one of them.

- Before an `ensures` of a run of words: the first comparison of two numbers that stops the working out
  of the specification's words, because no one fact says how the two compare (`wask`, which goes the way
  `weval` goes). Two rows are proposed: the first number is below the second, or it is not.
- Before a call: the bounds of the parts of runs handed over that the call's rules will look for among
  the facts and that no one fact says (`callNeeds`).
-/
namespace Ode
open Arithmetic (Row Step)

/-- Among numbers gone through in order, of each of which something is worked out: where it is not
followed of one of them (and, with `first`, was not followed and true of one before): that number; or,
with `middle`, the middle one of the run of numbers from there on of which it is not followed.
(Where the thing is a comparison that turns once along the numbers, as `1024 * k < len` does along the
powers of two, a row about the middle one says it of half the run at once: six rows for sixty-four
powers. Where it does not turn once, the row about the middle one may be one that cannot be shown,
though a search from the first would have ended before it: the prover then finds no proof.) -/
def askAt (first middle : Bool) (followed : Int → Option WVal) (l : List Int) : Option Int :=
  let rest := l.dropWhile fun n =>
    match followed n with
    | some (.bool true) => !first
    | some _ => true
    | none => false
  match rest with
  | [] => none
  | n :: more =>
    if (followed n).isSome then none
    else if !middle then some n
    else
      let run := n :: more.takeWhile fun m => (followed m).isNone
      run[run.length / 2]?

mutual
  /-- Where `weval` does not follow the expression because two numbers are compared (or one taken from
  the other, or a part of a run of bytes is to end within it) and the facts do not say at once how they
  compare: those two numbers, the first such in `weval`'s order. -/
  def wask (ctx : Ctx) (look : Node → Option Nat) (s : Sym) : Nat → List (String × WVal) → SExpr → Option (Row × Row)
    | 0, _, _ => none
    | fuel + 1, env, e =>
      if (weval ctx look s (fuel + 1) env e).isSome then none
      else
        match e with
        | .bin op a b =>
          match weval ctx look s fuel env a, weval ctx look s fuel env b with
          | some x, some y =>
            let pair := fun (p q : Row) =>
              -- (only where `wnum` turns on how the two compare)
              if !(op == "-" || op == "==" || op == "<" || op == ">=") then none
              -- `==`, where the first is known to be no less than the second: is the second below the first?
              else if op == "==" && plain s.facts (Lin.sub p q) then some (q, p) else some (p, q)
            (match x, y with
             | .num p, .num q => pair p q
             | .num p, .int m => pair p (Lin.const m)
             | .int m, .num q => pair (Lin.const m) q
             | _, _ => none)
          | none, _ => wask ctx look s fuel env a
          | some _, none => wask ctx look s fuel env b
        | .ifx c a b =>
          match weval ctx look s fuel env c with
          | some (.bool true) => wask ctx look s fuel env a
          | some (.bool false) => wask ctx look s fuel env b
          | some _ => none
          | none => wask ctx look s fuel env c
        | .index a i => (wask ctx look s fuel env a).orElse fun _ => wask ctx look s fuel env i
        | .call f args =>
          match wevalList (weval ctx look s fuel env) args with
          | none => waskList ctx look s fuel env args
          | some vs =>
            if f == "len" || own.contains f then none
            else
              match findDef ctx.defs f with
              | some d => if d.params.length == vs.length then wask ctx look s fuel (d.params.zip vs) d.body else none
              | none => none
        | .list items => waskList ctx look s fuel env items
        | .letx x e1 rest =>
          match weval ctx look s fuel env e1 with
          | some v => wask ctx look s fuel ((x, v) :: env) rest
          | none => wask ctx look s fuel env e1
        | .each e1 x a b =>
          match weval ctx look s fuel env a, weval ctx look s fuel env b with
          | some (.int lo), some (.int hi) =>
            match askAt false false (fun n => weval ctx look s fuel ((x, .int n) :: env) e1) ((List.range (hi - lo).toNat).map fun (k : Nat) => lo + (k : Int)) with
            | some n => wask ctx look s fuel ((x, .int n) :: env) e1
            | none => none
          | none, _ => wask ctx look s fuel env a
          | _, _ => wask ctx look s fuel env b
        | .withx a puts => (wask ctx look s fuel env a).orElse fun _ => waskList ctx look s fuel env puts
        | .slice a lo hi =>
          match weval ctx look s fuel env a, weval ctx look s fuel env lo, weval ctx look s fuel env hi with
          | some (.region _ l), some (.int i), some (.int j) =>
            if 0 ≤ i ∧ i ≤ j then some (Lin.var l, Lin.const j) else none        -- is the run shorter than the part's end?
          | some (.region _ l), some (.int i), some (.num j) =>
            if 0 ≤ i then (if plain s.facts (Lin.sub j (Lin.const i)) then some (Lin.var l, j) else some (j, Lin.const i)) else none
          | none, _, _ => wask ctx look s fuel env a
          | some _, none, _ => wask ctx look s fuel env lo
          | some _, some _, none => wask ctx look s fuel env hi
          | _, _, _ => none
        | .record _ items => waskList ctx look s fuel env items
        | .field e1 _ => wask ctx look s fuel env e1
        | .theNumber greatest x a b cond =>
          match weval ctx look s fuel env a, weval ctx look s fuel env b with
          | some (.int lo), some (.int hi) =>
            let among := (List.range (hi - lo).toNat).map fun (k : Nat) => lo + (k : Int)
            match askAt true false (fun n => weval ctx look s fuel ((x, .int n) :: env) cond) (if greatest then among.reverse else among) with
            | some n => wask ctx look s fuel ((x, .int n) :: env) cond
            | none => none
          | none, _ => wask ctx look s fuel env a
          | _, _ => wask ctx look s fuel env b
        | .thePower greatest x cond =>
          let among := (List.range 64).map fun (k : Nat) => (2 : Int) ^ k
          match askAt true true (fun n => weval ctx look s fuel ((x, .int n) :: env) cond) (if greatest then among.reverse else among) with
          | some n => wask ctx look s fuel ((x, .int n) :: env) cond
          | none => none
        | _ => none
  /-- The first of the things of a list that `weval` does not follow: what is proposed there. -/
  def waskList (ctx : Ctx) (look : Node → Option Nat) (s : Sym) : Nat → List (String × WVal) → SExpr → Option (Row × Row)
    | fuel, env, .cons a rest =>
      if (weval ctx look s fuel env a).isSome then waskList ctx look s fuel env rest else wask ctx look s fuel env a
    | _, _, _ => none
end

/-- Before an `ensures` of a run of words: where a comparison stops the working out of the
specification's words, the two rows of which one is to be shown: the first number is below the second;
or it is not. (None where a number speaks of an unknown that is not in use.) -/
def ensureRows (ctx : Ctx) (s : Sym) (e : EnsureW) : List Row :=
  match e.value with
  | .call _ (.cons x .nil) =>
    match wask ctx s.tab.find s WFUEL (wenv ctx.contract) x with
    | some (a, b) =>
      if a.coeff.length ≤ s.nvars ∧ b.coeff.length ≤ s.nvars then [Lin.sub (Lin.sub b a) (Lin.const 1), Lin.sub a b] else []
    | none => []
  | _ => []

/-- The rows a call's rules look for among the facts: that each part of a run of bytes with a length
that the called function is given ends within the run, and does not begin before it. -/
def callNeeds (ctx : Ctx) (s : Sym) (c : Contract) : List (String × Kind) → List Nat → List Row
  | (_, .fixed n) :: args, r :: regs =>
    (match findOut (s.reg r) ctx.contract.fixeds 0 with
     | some _ => []
     | none =>
       match findRegion (s.reg r) ctx.contract.regions 0 with
       | some (.region k off) =>
         match Lin.isConst off, ctx.contract.regions[k]? with
         | some c0, some (_, l) => [Lin.sub (Lin.var l) (Lin.const (c0 + n))]
         | _, _ => []
       | _ => []) ++ callNeeds ctx s c args regs
  | (_, .bytes len) :: args, r :: regs =>
    (match c.regOf len with
     | some l =>
       match findRegion (s.reg r) ctx.contract.regions 0 with
       | some (.region k off) =>
         match ctx.contract.regions[k]? with
         | some (_, lb) => [off, Lin.sub (Lin.var lb) (Lin.add off (s.reg l))]
         | none => []
       | _ => []
     | none => []) ++ callNeeds ctx s c args regs
  | _ :: args, _ :: regs => callNeeds ctx s c args regs
  | _, _ => []

/-- Before a call: the rows its rules will look for that no one fact says. -/
def callRows (ctx : Ctx) (s : Sym) (c : Contract) : List Row :=
  (callNeeds ctx s c c.args argRegs).filter fun g => decide (g.coeff.length ≤ s.nvars) && !plain s.facts g

/-- The advice `odeprove` gives the verifier's rules to print. -/
def adviceFor (ctx : Ctx) : Advice := { ensures := ensureRows ctx, call := callRows ctx }

end Ode
