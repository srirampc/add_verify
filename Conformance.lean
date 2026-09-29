import Add
import FuzzVectors

/-!
# Executable conformance harness

`Add.lean` proves the statements; `Add.Fuzz` kernel-checks every fuzzed operand pair
via `decide`. This executable closes the loop at *runtime*: it re-evaluates the model
on the same kind of boundary cases and prints the outcome, so the specification is
demonstrably computable rather than an axiom in disguise (`#print axioms` in
`Add.lean` already reports an empty axiom set; this shows the terms also reduce).

Run with `lake exe conformance`.
-/

open Add
open Add.Fuzz

/-- Evaluate the model `vadd` on two literals and compare with the expected sum.
This is `decide` on the same proposition shape as every theorem in `Add.Fuzz`. -/
def agrees (a b c : Int) : Bool :=
  decide (VInt.toMath (vadd (ofInt a) (ofInt b)) = c)

/-- Boundary and chain cases: fixed-width boundaries, the docstring's own example,
and the identity/cancellation laws from `Add.lean` witnessed concretely. -/
def cases : List (String × Int × Int × Int) :=
  [ ("docstring example        ", 3, 5, 8)
  , ("both operands zero       ", 0, 0, 0)
  , ("negatives                ", -1, 1, 0)
  , ("32-bit boundary          ", 2147483647, 1, 2147483648)
  , ("64-bit boundary          ", 9223372036854775807, 1, 9223372036854775808)
  , ("2^64 boundary            ", 18446744073709551615, 1, 18446744073709551616)
  , ("well past 64 bits        ", 170141183460469231731687303715884105728, 1,
     170141183460469231731687303715884105729)
  , ("both very negative       ", -9223372036854775808, -9223372036854775808,
     -18446744073709551616)
  ]

def main : IO Unit := do
  IO.println "Lean conformance run: model `vadd` vs the fuzzer's CPython results"
  IO.println s!"  kernel-checked vectors imported from Add.Fuzz: {numVectors}"
  IO.println ""
  let mut failures := 0
  for (label, a, b, c) in cases do
    let ok := agrees a b c
    if !ok then failures := failures + 1
    IO.println s!"  [{if ok then "PASS" else "FAIL"}] {label} {a} + {b} = {c}"
  IO.println ""
  if failures == 0 then
    IO.println "RESULT: PASS — the model is computable and agrees on every case."
  else
    IO.println s!"RESULT: FAIL — {failures} case(s) disagreed."
