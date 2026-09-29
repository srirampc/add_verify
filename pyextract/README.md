# `PyExtract` — deriving Python from Lean proofs

> **Bottom line.** Lean has **no Python backend**. This toolchain emits only C (`-c`)
> and LLVM bitcode (`-b`). "Derive Python from the proof" is therefore *not* a switch
> you flip — it is an extraction pass you have to write. This directory contains a
> working one (~200 lines), because the question is much better answered by building
> the thing and finding the wall than by guessing where the wall is.

```
lake build          # builds the extractor and all demos
```

## The insight that makes it work

The specification lives in the **type**; the computation lives in the **value**:

```lean
def add (a b : Int) : { c : Int // c = a + b } := ⟨a + b, rfl⟩
--              ^^^^^^^^^^^^^^^^^^^^^^ spec        ^^^^ computation  ^^^^ proof
```

Extraction is then mostly **erasure**: drop the proof, keep the computation. You
cannot write that definition without also producing `a + b = a + b`, so no
unproven function can exist to be extracted. The extractor reports exactly what it
dropped (`erased N proof term(s)`), so erasure is visible rather than implied.

## What it actually produces

Input (`Demo.lean`, `Helper.lean`) becomes, verified by `lake build`:

```python
def add(a, b):
    return a + b

def mul(a, b):
    return a * b

def sub(a, b):
    return a - b

def clampZero(a):
    return (a if a >= 0 else 0)

def addTwice(a, b):
    return add(a, b) + add(a, b)      # composition: proof reused from `add`'s spec
```

Lean reconstructs `a + b` from class projections (`HAdd.hAdd`, `LE.le`, `ite`/`dite`
with the proof-carrying hypothesis argument stripped), integer literals from
`Int.ofNat`/`Int.negSucc`, and calls to other **verified** definitions as plain Python
calls.

All demonstrated specs were then re-checked by executing the generated Python:
`add`/`mul`/`sub`/`clampZero`/`addTwice` hold over full ranges, including `2^200`.

## Where it genuinely breaks

The extractor **throws** rather than guessing. Each failure below was observed, not
predicted:

| Construct | What happens | Why |
| --- | --- | --- |
| Recursion / pattern matching | `recursion/pattern-matching is a recursor application (Nat.brecOn)` | Lean compiles `sumTo` to `Nat.brecOn x sumTo._f`, **not** source-level recursion. Needs a dedicated recursion pass that recovers source structure from the recursor encoding. |
| Unprovable specs | definition fails to elaborate; **no Python is emitted at all** | Claiming `{ c : Int // c = a + b + 1 }` is rejected by Lean. This is the property that matters most. |
| `Prop`-erased arguments used computationally | not representable | Erased proofs leave a genuine hole if the computation depended on them. Lean's erasure is designed so it cannot, but a hand-rolled pass must respect that. |
| Type classes, structures, inductives, `String` | `unsupported constant` / `structure projection` | Each needs its own rendering rule and a name for the generated Python class. |
| Termination | not solved | Generated Python can still loop; Lean's termination proof is erased with everything else. |

## The bug I found while building this (a real one, caught by testing)

The first operator table mapped Lean `/` to Python `//`. That is **wrong**, but only
on some inputs — which is exactly what makes it dangerous. Lean's `Int` division is
**Euclidean** (remainder always non-negative); Python's `//` **floors**, so the
remainder takes the divisor's sign:

| case | Lean `/`, `%` | Python `//`, `%` | same? |
| --- | --- | --- | --- |
| `-7 / 2` | `-4`, `1` | `-4`, `1` | ✅ |
| `7 / 2` | `3`, `1` | `3`, `1` | ✅ |
| `7 / -2` | `-3`, `1` | `-4`, `-1` | ❌ |
| `-7 / -2` | `4`, `1` | `3`, `-1` | ❌ |

They agree whenever the divisor is positive and diverge whenever it is negative. A
naive extractor therefore ships correct-looking code that breaks on one sign.

`PyExtract` now handles this **type-directedly**: `nat` division still renders as
`//`; `Int` division renders as a call to a generated `_lean_div` (emitted only when
used), which reproduces Euclidean semantics on top of Python's floor, along with
`_lean_emod`. Where the type cannot be determined, the extractor **refuses** rather
than guessing. Verified against Lean's own `#eval` output:

```
  case      Lean   Python//   extracted   matches Lean?
   -7/2    (-4,1)   (-4, 1)    (-4,1)      True
    7/2    ( 3,1)   ( 3, 1)    ( 3,1)      True
   7/-2    (-3,1)   (-4,-1)    (-3,1)      True
  -7/-2    ( 4,1)   ( 3,-1)    ( 4,1)      True

  a = b*q + r, r >= 0, r < |b|  over all sign combinations: True
```

This is the general shape of the risk: **the extractor is a trusted translation, and
a wrong rule yields plausible, silently-wrong Python**. It was caught by a
conformance test against Lean's own evaluator — not by the type checker, and not by
review. Any real deployment needs that test suite to be exhaustive over operator
edge cases.

## The honest architecture

This is why real systems that derive code from proofs — F\* with its OCaml/C
backends, and Delphi-style verified code generation generally — keep a hard split:

```
  verified core  ──extract──►  generated code  ──┐
   (proved)                                      ├─►  your program
  hand-written glue (I/O, FFI, errors)  ─────────┘
                                    ▲
                        tested, NOT proved (the "seam")
```

You get **internal validity** — the core does what its spec says — and you accept
that the *edges* (extraction correctness, FFI, operator semantics) are tested rather
than proved. Fully verified extraction requires mechanizing the target language's
semantics, which is research-scale.

## Does it fit "Python is prevalent and easy to learn"?

Partly, and the tension is worth naming:

**Wins.** There is only **one artifact**, so the model-drift problem that sank the
other approach (a proof about a hand-written transcription, silently detached from
the real source) **disappears**. When the spec changes, the proof must change, or
nothing compiles.

**Costs.** Lean, not Python, becomes the source of truth — which inverts the
"Python is easier for users" premise. The generated Python is also unidiomatic
(mechanical names, no docstrings, recursors rendered where they can be), so the
practical recipe is to generate the *algorithmic core* and wrap it in a
hand-written, idiomatic Python API, then test only the seam.

**Where it earns its keep.** Small, algorithmically hard, high-consequence cores —
a saturating/wrapping arithmetic kernel, a rate limiter, a serialization codec, a
parser — where the spec is subtle and the bug class is real. Not general application
code; the extraction pass and its operator semantics are too much surface area to
maintain for code that a test suite would cover anyway.

## Files

| File | Role |
| --- | --- |
| `PyExtract.lean` | the extractor: `Expr` walker, proof + `Prop`-parameter erasure, Euclidean-division handling, `python_export` macro |
| `Demo.lean` | verified `add`/`mul`/`sub`/`clampZero` + the export call |
| `Helper.lean` | composition: `addTwice` proved from `add`'s spec |
| `DivDemo.lean` | Euclidean `Int` division — the operator-semantics case, with its conformance result |
| `Check.lean` | deliberately recursive function, showing the recursor failure |
| `Sound.lean` | a false spec, showing nothing is emitted |

`Demo`, `Helper` and `Check` are intentionally **not** library targets in
`lakefile.toml` where they are expected to fail; run them with
`lake env lean <file>.lean` to see the errors.
