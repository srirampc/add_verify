import PyExtract
namespace D2
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n
end D2
python_export "D2.sumTo"
