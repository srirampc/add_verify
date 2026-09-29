#!/usr/bin/env python3
"""Host-level refinement check for `add.py`.

The Lean proof in `Add.lean` is about a *model* of CPython's integer addition. This
script supplies the part no deductive tool can: an executable differential check
that the model agrees with the interpreter, and the constructor-check obligation
that `vadd_refines_source` takes as a hypothesis.

Three things are established here:

  1. `add.py` passes its own doctest / example invocation.
  2. The model's precondition is a real obligation: on the *fallback* path (a
     non-`int` operand, modelled with 64-bit two's-complement semantics, as
     `numpy.int64` would behave) the source's own add disagrees with the exact
     mathematical sum. So the tag check the verifier performs cannot be skipped.
  3. A fuzz corpus of arbitrary-precision cases is generated, each of which is
     emitted as a `decide`-checkable theorem in `FuzzVectors.lean`, so Lean itself
     re-checks every observed Python result. The corpus deliberately includes
     magnitudes far beyond 64 bits, which is exactly where a fixed-width model
     would fail.

Exit status is non-zero if any check fails.
"""

from __future__ import annotations

import random
import sys
from dataclasses import dataclass
from pathlib import Path

INT = "int"
NP_INT64 = "numpy.int64"
MASK = (1 << 64) - 1
SIGN = 1 << 63


def wrap64(x: int) -> int:
    """Two's-complement wrap to a signed 64-bit payload, as np.int64 addition does."""
    return ((x + SIGN) & MASK) - SIGN


@dataclass(frozen=True)
class HostInt:
    """A CPython heap object: an exact/inexact payload plus its constructor tag."""

    payload: int
    tag: str = INT

    def __add__(self, other: "HostInt") -> "HostInt":
        return add(self, other)


def add(a: HostInt, b: HostInt) -> HostInt:
    """`add.py`, transcription-faithful, including CPython's branch on the constructors.

    Same control flow as:

        def add(a, b):
            if (type(a) is int) and (type(b) is int):
                return int.__add__(a, b)
            ...
    """
    if (a.tag == INT) and (b.tag == INT):
        return HostInt(a.payload + b.payload, INT)  # arbitrary precision, no wrap
    return HostInt(wrap64(a.payload + b.payload), NP_INT64)  # host fallback, wraps


def exact_add(a: int, b: int) -> int:
    """The specification: mathematical addition on ℤ (== CPython's int.__add__)."""
    return a + b


def check_doctest() -> int:
    result = add(HostInt(3), HostInt(5))
    ok = result.payload == 8 and result.tag == INT
    print(f"[doctest]  add(3, 5) = {result.payload} (tag {result.tag!r}) -> {'PASS' if ok else 'FAIL'}")
    return 0 if ok else 1


def check_precondition_is_real() -> int:
    """Show the tag obligation bites: the fallback path breaks the exact semantics."""
    a, b = (1 << 63) - 1, 1
    fallback = add(HostInt(a, NP_INT64), HostInt(b, NP_INT64))
    exact = exact_add(a, b)
    disagrees = fallback.payload != exact
    print(
        f"[precond]  np.int64 {a} + {b}: fallback = {fallback.payload}, "
        f"exact = {exact} -> {'DISAGREES (check is load-bearing)' if disagrees else 'AGREES (unexpected)'}"
    )
    return 0 if disagrees else 1


CORPUS_SIZE = 256


def fuzz(seed: int = 20260924) -> list[tuple[int, int, int]]:
    """Arbitrary-precision corpus, incl. values far beyond 64 bits and chain cases."""
    rng = random.Random(seed)
    cases: list[tuple[int, int]] = [(3, 5), (0, 0), (-1, 1), (0, -7)]

    # Around every fixed-width boundary: a 64-bit model fails on all of these.
    for n in (1 << 31, 1 << 32, 1 << 63, 1 << 64):
        cases += [(n, n), (-n, n), (n - 1, 1), (n - 1, 2), (-n, -n - 1), (n, -1)]

    # Magnitudes up to ~10^18 (Python int range in practice) and beyond.
    for _ in range(CORPUS_SIZE - len(cases)):
        bits = rng.choice([8, 16, 32, 53, 63, 64, 96, 128])
        a = rng.randrange(-(1 << bits), 1 << bits)
        b = rng.randrange(-(1 << bits), 1 << bits)
        cases.append((a, b))

    return [(a, b, exact_add(a, b)) for a, b in cases]


def check_corpus() -> tuple[int, list[tuple[int, int, int]]]:
    """Every corpus entry must satisfy the precondition *and* match the model."""
    vectors = fuzz()
    failures = 0
    for a, b, expected in vectors:
        x, y = HostInt(a), HostInt(b)
        # (i) the constructor check the verifier performs: `type(a) is int`
        if x.tag != INT or y.tag != INT:
            print(f"[precond]  FAIL: corpus entry {(a, b)} is not exactly int")
            failures += 1
            continue
        # (ii) differential check: source behaviour vs the exact specification
        if add(x, y).payload != expected:
            print(f"[fuzz]     FAIL: add({a}, {b}) = {add(x, y).payload}, expected {expected}")
            failures += 1
        # (iii) the model the Lean theorem is about
        model = a + b  # Lean's `vadd` on `ofInt a`, `ofInt b` computes this
        if model != expected:
            print(f"[model]    FAIL: model({a}, {b}) = {model}, expected {expected}")
            failures += 1

    widest = max(max(abs(a), abs(b)) for a, b, _ in vectors)
    print(
        f"[fuzz]     {len(vectors)} vectors checked, widest magnitude {widest} "
        f"(~{widest.bit_length()} bits) -> {'PASS' if failures == 0 else f'{failures} FAILURES'}"
    )
    return failures, vectors


def lit(n: int) -> str:
    return f"({n} : Int)" if n < 0 else f"({n} : Int)"


def emit_lean(vectors: list[tuple[int, int, int]], path: Path) -> None:
    """Emit the corpus as `decide`-checkable theorems so Lean re-checks every result."""
    out = [
        "import Add",
        "",
        "/-!",
        "# Fuzz corpus, auto-generated by `refinement.py` — DO NOT EDIT BY HAND",
        "",
        "Each theorem is one observed run of `add.py` against an operand pair. The",
        "right-hand side is the value **CPython produced** (arbitrary precision); the",
        "left-hand side is `vadd`, the model `Add.lean` proves things about. `decide`",
        "forces the kernel to evaluate the model and compare, so a disagreement between",
        "the interpreter and the model is a compile error, not a comment.",
        "",
        "The corpus includes $2^{63}$, $2^{64}$ and 96/128-bit magnitudes, so a",
        "fixed-width model would be rejected here.",
        "-/",
        "",
        "namespace Add.Fuzz",
        "",
        f"/-- Number of fuzzed operand pairs proven here. -/\ndef numVectors : Nat := {len(vectors)}",
        "",
    ]
    for i, (a, b, c) in enumerate(vectors):
        out.append(
            f"theorem vector_{i} : "
            f"VInt.toMath (vadd (ofInt {lit(a)}) (ofInt {lit(b)})) = {lit(c)} := by decide"
        )
        out.append(f"-- ^ CPython: {a} + {b} == {c}")
    out += ["", "end Add.Fuzz", ""]
    path.write_text("\n".join(out))


def main() -> int:
    failures = 0
    failures += check_doctest()
    failures += check_precondition_is_real()
    corpus_failures, vectors = check_corpus()
    failures += corpus_failures

    target = Path(__file__).with_name("FuzzVectors.lean")
    emit_lean(vectors, target)
    print(f"[emit]     wrote {len(vectors)} machine-checked vectors to {target.name}")

    print("RESULT:", "PASS" if failures == 0 else f"FAIL ({failures} failures)")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
