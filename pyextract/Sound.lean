import PyExtract
namespace S
-- A FALSE spec: claim we compute a+b+1. Lean rejects the definition outright,
-- so there is no term to extract and no Python is ever emitted.
def badAdd (a b : Int) : { c : Int // c = a + b + 1 } := ⟨a + b, rfl⟩
end S
python_export "S.badAdd"
