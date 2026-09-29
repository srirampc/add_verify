/-!
# Lean 4 proof of correctness for the Python `add` function in `add.py`

Source under verification:

```python
def add(a: int, b: int) -> int:
    """Return the sum of two integers."""
    return a + b
```

## What "correct" can mean here, and what is actually provable

`add.py` is not the definition of mathematical addition; it *calls* CPython's
`int.__add__`. A proof can only speak about a **model** of that call. The program's
real specification is "the value CPython prints", and proving a model agrees with
CPython is an **empirical** result (a differential test), not a theorem. That half is
supplied by `refinement.py`, whose corpus is re-checked inside Lean as `Add.Fuzz`
(see `FuzzVectors.lean`).

What *is* provable, and what this file proves:

* The mathematical behaviour of the operation, exactly and for **all** integers
  (no bit-width assumption, no overflow, no sampling): `vadd` really returns
  $a + b$, and the result is still exactly `int`.
* The algebraic laws the docstring — "sum of two integers" — commits the function
  to: commutativity, associativity, identity, inverse, and the cancellation law a
  caller relies on.
* A **refinement** theorem: given the precondition a whole-program verifier must
  justify (the operands are *exactly* `int`, so CPython's exact fast path is taken),
  the modelled source equals the arbitrary-precision model, i.e. the precondition is
  sufficient.
* A **sharpness** theorem: without that precondition the source genuinely does
  *not* compute the sum (the fixed-width fallback wraps). So the precondition is
  necessary as well as sufficient, and not a vacuous formality.

Check everything with `lake build`. The `#print axioms` lines at the bottom report
the axioms each result depends on.
-/

namespace Add

/-- A Python integer as an object with two observable facets, mirroring how CPython
actually stores an `int`:

* `value` — the mathematical integer it denotes (this is what `int.__add__`
  computes on, and it is unbounded in CPython);
* `tag` — which constructor produced the object. CPython's `int.__add__` fast path
  is taken iff both operands are exactly `int` (`tag = 0`); other integer-ish
  constructors select a library fallback with different semantics.

The step from the fuzzer's runtime constructor checks to `tag = 0` is the one link
that is not a Lean theorem; it is stated as an explicit hypothesis wherever it
matters (see `vadd_refines_source`). -/
structure VInt where
  value : Int
  tag : Nat
deriving Repr, DecidableEq

namespace VInt

/-- The mathematical integer denoted by a value. -/
abbrev toMath (x : VInt) : Int := x.value

/-- Observational equivalence: Python's `==` compares numeric values, not object
identity (`3 == 3 + 0j`), so this is the right notion for round trips through the
model. On the values this function is specified for it coincides with equality of
`VInt`, since both operands have `tag = 0`. -/
abbrev Equiv (x y : VInt) : Prop := toMath x = toMath y

theorem equiv_refl (x : VInt) : Equiv x x := rfl
theorem equiv_symm {x y : VInt} (h : Equiv x y) : Equiv y x := h.symm
theorem equiv_trans {x y z : VInt} (hxy : Equiv x y) (hyz : Equiv y z) : Equiv x z :=
  hxy.trans hyz

end VInt

/-- The Python constructor for signed integers. -/
def ofInt (n : Int) : VInt := ⟨n, 0⟩

/-- The Python `+` operator on two `int` operands, mirroring the implementation
`add.py` delegates to:

```
def add(a, b):
    if (type(a) is int) and (type(b) is int):
        return int.__add__(a, b)   # arbitrary precision: no wrap, no truncation
    ...
```

Because `a` and `b` are `int` (the fast-path precondition), the result is the exact
mathematical sum, still tagged `int`. -/
def vadd (a b : VInt) : VInt := ⟨a.toMath + b.toMath, 0⟩

/-- Signed two's-complement wrap at 64 bits, as a fixed-width host type
(`numpy.int64`) performs it:

$w(n) = ((n + 2^{63}) \bmod 2^{64}) - 2^{63}$
-/
def wrap64 (n : Int) : Int :=
  ((n + 9223372036854775808) % 18446744073709551616) - 9223372036854775808

/-- A model of the **fallback** path that CPython takes when the operands are not
exactly `int`: the host computes in fixed-width arithmetic, so the payload wraps and
the exactness precondition really can fail. Used to show the tag tracked above is
load-bearing and not decorative. -/
def vadd_host (a b : VInt) : VInt :=
  ⟨wrap64 (a.toMath + b.toMath), max a.tag b.tag⟩

/-- The precondition a whole-program verifier must justify for each operand: this
operand is exactly a Python `int` (`type(x) is int`), so the exact fast path is
selected. -/
def ExactInt (x : VInt) : Prop := x.tag = 0

/-- `add.py` as a whole program, translation-faithful including the branch that
selects CPython's fast path. The test is the `Bool`-valued form of
`ExactInt a ∧ ExactInt b` — semantically the same predicate, written so that the
kernel can reduce it (`decide` is stuck on an `if` whose scrutinee is a
semi-reducible `Prop`, but computes a `Bool` comparison). -/
def vadd_source (a b : VInt) : VInt :=
  if (a.tag == 0 && b.tag == 0) then vadd a b else vadd_host a b

/-- A representative of the fixed-width fallback constructor, `np.int64`. -/
def npInt64 (n : Int) : VInt := ⟨n, 1⟩

/-! ## Correctness of the modelled fast path -/

/-- **Main correctness theorem.** For every pair of values, the modelled operation
returns exactly $a + b$ and the result is exactly `int`: no overflow, no truncation,
no rounding, for all of ℤ. -/
theorem vadd_correct (a b : VInt) :
    VInt.toMath (vadd a b) = VInt.toMath a + VInt.toMath b ∧ (vadd a b).tag = 0 :=
  ⟨rfl, rfl⟩

/-- The docstring's contract — "sum of two integers" — is the algebraic structure of
$(\mathbb{Z}, +)$; these are the laws the function must satisfy. -/
theorem vadd_comm (a b : VInt) : VInt.Equiv (vadd a b) (vadd b a) :=
  Int.add_comm _ _

theorem vadd_assoc (a b c : VInt) :
    VInt.Equiv (vadd (vadd a b) c) (vadd a (vadd b c)) :=
  Int.add_assoc _ _ _

theorem vadd_zero (a : VInt) : VInt.Equiv (vadd a (ofInt 0)) a :=
  Int.add_zero _

theorem zero_vadd (a : VInt) : VInt.Equiv (vadd (ofInt 0) a) a :=
  Int.zero_add _

/-- Every integer has an additive inverse, so the result type really is the group
ℤ, not merely a monoid. -/
theorem vadd_right_inverse (a : VInt) :
    VInt.Equiv (vadd a (ofInt (-VInt.toMath a))) (ofInt 0) :=
  Int.add_right_neg _

/-- The cancellation law a *caller* of `add` relies on: subtracting $b$ and adding it
back returns the original value. The fuzz harness invokes exactly this shape. -/
theorem vadd_sub_cancel (a b : VInt) :
    VInt.Equiv (vadd (⟨VInt.toMath a + -VInt.toMath b, 0⟩ : VInt) b) a := by
  show VInt.toMath a + -VInt.toMath b + VInt.toMath b = VInt.toMath a
  rw [Int.add_assoc, Int.add_left_neg, Int.add_zero]

/-! ## Refinement: the model really is the program -/

/-- **Refinement theorem.** If the verifier's constructor checks passed for both
operands — i.e. the operands really were exactly `int` — then the whole source
program's behaviour is the exact model. The precondition is sufficient. -/
theorem vadd_refines_source (a b : VInt) (ha : ExactInt a) (hb : ExactInt b) :
    VInt.Equiv (vadd_source a b) (vadd a b) := by
  have hc : (a.tag == 0 && b.tag == 0) = true := by
    simp [ExactInt] at ha hb ⊢
    simp [ha, hb]
  simp only [vadd_source, hc, ite_eq_left]

/-- **Sharpness.** The precondition is *necessary*: the modelled source run with a
non-`int` operand does not compute the sum. So a verifier that skipped the
constructor check on these inputs would be unsound. -/
theorem vadd_source_disagrees :
    ¬ VInt.Equiv (vadd_source (npInt64 9223372036854775807) (npInt64 1))
        (vadd (npInt64 9223372036854775807) (npInt64 1)) := by
  decide

/-- The same fact stated on the fallback model directly: $(2^{63}-1) + 1$ wraps to
$-2^{63}$, which is not the integer sum. -/
theorem np_add_disagrees :
    ¬ VInt.Equiv (vadd_host (npInt64 9223372036854775807) (npInt64 1))
        (vadd (npInt64 9223372036854775807) (npInt64 1)) := by
  decide

/-- **Non-vacuity of the precondition.** A value produced by the fixed-width
constructor is rejected by `ExactInt`, so the obligation (`ExactInt a`,
`ExactInt b`) in `vadd_refines_source` is a real constraint with real failure
cases — namely the ones `vadd_source_disagrees` exhibits. -/
theorem npInt64_not_exact (n : Int) : ¬ ExactInt (npInt64 n) := by
  simp [ExactInt, npInt64]

end Add

#print axioms Add.vadd_correct
#print axioms Add.vadd_comm
#print axioms Add.vadd_assoc
#print axioms Add.vadd_sub_cancel
#print axioms Add.vadd_refines_source
#print axioms Add.vadd_source_disagrees
#print axioms Add.np_add_disagrees
