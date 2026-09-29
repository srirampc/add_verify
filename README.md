# Machine-checked correctness proof for `add.py`

`./add.py`:

```python
def add(a: int, b: int) -> int:
    """Return the sum of two integers."""
    return a + b
```

This directory contains a Lean 4 proof about that function, plus the executable
checks that keep the proof honest about the program it claims to describe.

```
./verify.sh        # everything: Python checks, Lean proofs, conformance, negative control
lake build         # just the proofs
lake exe conformance
```

## What is proven, exactly

`Add.lean` proves these about the model, for **all** integers — no bit-width
assumption, no overflow, no sampling:

| Theorem | Statement |
| --- | --- |
| `vadd_correct` | the modelled operation returns exactly $a + b$, and the result is still exactly `int` |
| `vadd_comm` / `vadd_assoc` | commutativity, associativity |
| `vadd_zero` / `zero_vadd` | `0` is a two-sided identity |
| `vadd_right_inverse` | every integer has an additive inverse (the result type is the group ℤ, not just a monoid) |
| `vadd_sub_cancel` | the cancellation law a *caller* relies on: subtract `b`, add `b`, get the original back |
| `vadd_refines_source` | the model equals the whole source program *given* the operands are exactly `int` |
| `vadd_source_disagrees`, `np_add_disagrees` | without that precondition the source genuinely does **not** compute the sum |
| `npInt64_not_exact` | the precondition is non-vacuous: a fixed-width operand is rejected by it |

Axiom audit (`#print axioms`, reported on every build):

```
'Add.vadd_correct'            does not depend on any axioms
'Add.vadd_comm'               depends on axioms: [propext]
'Add.vadd_assoc'              depends on axioms: [propext]
'Add.vadd_sub_cancel'         depends on axioms: [propext]
'Add.vadd_refines_source'     depends on axioms: [propext, Quot.sound]
'Add.vadd_source_disagrees'   does not depend on any axioms
'Add.np_add_disagrees'        does not depend on any axioms
```

`propext` and `Quot.sound` are Lean's standard logical primitives, not gaps in the
argument. There is **no `sorry`**, no `axiom`, and no `native_decide` anywhere.

## The honest boundary of the claim

`add.py` does not *define* addition; it calls CPython's `int.__add__`. So a proof can
only be about a **model** of that call. The model here (`vadd`) is the exact
arbitrary-precision one, matching CPython's `int`, which has no overflow.

That leaves one obligation that is not a theorem and cannot be: the claim that the
model matches what CPython actually does, and that the operands really are `int`.
Both are discharged **empirically and executably**:

* `refinement.py` is a transcription of CPython's dispatch —
  `if type(a) is int and type(b) is int: return int.__add__(a, b)` — including the
  fallback for non-`int` integer-ish types.
* It checks the docstring example, proves the precondition is load-bearing (the
  fallback wraps: `int64 max + 1` → `-2^63`), and fuzzes 256 operand pairs whose
  magnitudes reach ~128 bits, far past every fixed-width boundary.
* Each fuzzed pair is emitted into `FuzzVectors.lean` as
  `... = <value CPython produced> := by decide`, so **Lean's kernel re-checks every
  observed Python result**. A disagreement between the interpreter and the model is a
  compile error, not a comment.

`vadd_refines_source` then takes the constructor check as an explicit hypothesis and
shows it is *sufficient*; `vadd_source_disagrees` shows it is *necessary*. The
hypothesis is stated rather than smuggled in.

## Why the negative control exists

`NegativeControl.lean` contains two deliberately buggy adders — an off-by-one, and a
64-bit-wrapping one — together with the claims those bugs would license. Both must
**fail to compile**. `verify.sh` asserts that they do, and reports failure if they
ever succeed. A verifier that cannot reject a wrong program has not verified
anything, and this is the file that pins that down. The overflow bug it rejects is
exactly what `vadd_source_disagrees` rules out in the main proof.

## Files

| File | Role |
| --- | --- |
| `Add.lean` | the model, the proofs, the axiom audit |
| `refinement.py` | CPython dispatch model, differential checks, fuzz generator |
| `FuzzVectors.lean` | generated; 256 `decide`-checked vectors, one per fuzzed pair |
| `Conformance.lean` | runtime harness re-evaluating the model on boundary cases |
| `NegativeControl.lean` | buggy models that must be rejected |
| `verify.sh` | one-command end-to-end run |
| `lakefile.toml`, `lean-toolchain` | Lake project, pinned to Lean `v4.34.0` |

Built against **Lean 4.34.0 with core only** — no Mathlib. `omega`/`ring`/`linarith`
are Mathlib tactics and are not used; the proofs go through Lean's own `simp`, `rw`,
`decide`, and core `Int` lemmas (`Int.add_comm`, `Int.add_assoc`, `Int.add_left_neg`,
…). Two toolchain quirks worth knowing if you extend this:

* `⊔` notation is unavailable in this configuration; `max` is used instead.
* `decide` cannot reduce an `if` whose scrutinee is a semi-reducible `Prop`, so the
  branch test in `vadd_source` is written in `Bool` form (`a.tag == 0 && b.tag == 0`).
