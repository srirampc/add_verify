import PyExtract

/-! Composition: a verified function built from another verified function. This is
the case where deriving code from proofs starts to pay off — `addTwice` gets its
correctness from `add`'s proven specification, not from re-argument. -/

namespace H

def add (a b : Int) : { c : Int // c = a + b } := ⟨a + b, rfl⟩

/-- `addTwice a b = (a+b) + (a+b)`, proved by *using* `add`'s spec (`(add a b).2`). -/
def addTwice (a b : Int) : { c : Int // c = a + b + (a + b) } :=
  ⟨(add a b).1 + (add a b).1, by rw [(add a b).2]⟩

end H

python_export "H.add" "H.addTwice"
