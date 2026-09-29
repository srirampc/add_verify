import PyExtract

/-! Demo: verified definitions, and what a Python backend can make of them. -/

namespace Demo

/-- Proof-carrying addition — exactly `add.py`'s contract, with the specification in
the *type*: you cannot write this definition without also producing the proof. -/
def add (a b : Int) : { c : Int // c = a + b } := ⟨a + b, rfl⟩

/-- Proof-carrying multiplication. -/
def mul (a b : Int) : { c : Int // c = a * b } := ⟨a * b, rfl⟩

/-- Proof-carrying subtraction, with a spec phrased for callers: `sub a b` is the
value `c` with `c + b = a`. -/
def sub (a b : Int) : { c : Int // c + b = a } :=
  ⟨a - b, by
    show a + -b + b = a
    rw [Int.add_assoc, Int.add_left_neg, Int.add_zero]⟩

/-- A branch: clamp negatives to zero. The spec records both behaviour and reason. -/
def clampZero (a : Int) : { c : Int // c ≥ 0 ∧ (a ≥ 0 → c = a) } :=
  if h : a ≥ 0 then
    ⟨a, ⟨h, fun _ => rfl⟩⟩
  else
    ⟨0, ⟨Int.le_refl 0, fun hge => absurd hge h⟩⟩

/-- Total, and Lean only accepts it because termination is proven. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

/-- The specification of `add`, as an axiom-free theorem. The extraction is faithful
precisely because this type is inhabited. -/
theorem add_spec (a b : Int) : (add a b).1 = a + b := rfl

/-- A law about the verified function, proved once and true of every call. -/
theorem add_zero_right (a : Int) : (add a 0).1 = a := Int.add_zero a

end Demo

python_export "Demo.add" "Demo.mul" "Demo.sub" "Demo.clampZero"
