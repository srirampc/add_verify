import PyExtract

/-! The division trap, made testable.

Lean's `Int` division is **Euclidean** (remainder always non-negative); Python's `//`
floors, so its remainder takes the divisor's sign. Mapping `Int.div` to `//` would
emit plausible, silently wrong Python. `PyExtract` instead emits `_lean_div` /
`_lean_emod`, and this file exists so the claim is checkable.

Note `hb` below: it is a **proof** (`0 < b`), so it is erased from the generated
Python signature — Prop-typed parameters carry no runtime content. -/

namespace DivDemo

/-- Euclidean division, proof-carrying: the quotient and a non-negative remainder. -/
def euclidDiv (a b : Int) (hb : 0 < b) :
    { q : Int // ∃ r, a = b * q + r ∧ 0 ≤ r ∧ r < b } :=
  ⟨a / b, ⟨a % b, ⟨(Int.mul_ediv_add_emod a b).symm,
    ⟨Int.emod_nonneg a (Int.ne_of_gt hb), Int.emod_lt_of_pos a hb⟩⟩⟩⟩

end DivDemo

python_export "DivDemo.euclidDiv"
