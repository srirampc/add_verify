import Add

/-!
# Negative control: implementations that MUST be rejected

A verification suite that only ever says "PASS" proves nothing about its own
sensitivity. This file contains deliberately **buggy** models of `add` together with
the claims those bugs would license. Every `example` below must therefore *fail*.

It is intentionally **not** a `lake build` target. `verify.sh` runs it directly and
requires a non-zero exit status; if this file ever compiles, the suite is vacuous and
`verify.sh` reports failure.

The two bugs chosen are the ones that actually matter for an integer-adder:

* an off-by-one arithmetic error, and
* the classic fixed-width overflow (`int64`-style wrap) — precisely the bug that the
  exactness precondition in `Add.lean` exists to rule out.
-/

open Add

/-- BUG 1: "addition" that is off by one. Correct code must not satisfy this claim. -/
def badadd (a b : VInt) : VInt := ⟨a.toMath + b.toMath + 1, 0⟩

/-- Rejected: `badadd` does not return `8` for the docstring's example. -/
example : VInt.toMath (badadd (ofInt 3) (ofInt 5)) = (8 : Int) := by decide

/-- BUG 2: fixed-width (64-bit wrapping) addition. -/
def wrapadd (a b : VInt) : VInt := ⟨wrap64 (a.toMath + b.toMath), 0⟩

/-- Rejected: `wrapadd` overflows at the $2^{63}$ boundary, so it cannot satisfy the
correctness claim the real `vadd_correct` establishes for every input. -/
example :
    VInt.toMath (wrapadd (ofInt 9223372036854775807) (ofInt 1)) = (9223372036854775808 : Int) :=
  by decide
