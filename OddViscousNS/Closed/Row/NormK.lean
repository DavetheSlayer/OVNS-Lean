import OddViscousNS.Closed.Row.ScalK

/-!
# Kernel-side norm and rounding sums

Cauchy-Schwarz bounds for the slots of the products, and the rounding constants `E^{ij}`, as radial
sums.  No Mathlib here.
-/

namespace OVNS
namespace Row

/-- `(2 n F(n))²`, a bound for the squared left entries (weights `x²`, `(x+y)²`, both `≤ 2n`). -/
noncomputable def phiL (F : Nat → Nat) (n : Nat) : Nat :=
  lit (Nat.mul (Nat.mul 2 n) (F n)) (fun x => Nat.mul x x)

/-- `F(n)²`. -/
noncomputable def phiR (F : Nat → Nat) (n : Nat) : Nat := lit (F n) (fun x => Nat.mul x x)

/-- The product of the norms is below `2¹⁶⁰`. -/
noncomputable def normChk (F G : Nat → Nat) : Bool :=
  Nat.ble (Nat.add (Nat.mul (rad78 (phiL F)) (rad78 (phiR G))) 1)
    1461501637330902918203684832716283019655932542976

/-- The numerator of the rounding error of a kernel. -/
noncomputable def errS (F G : Nat → Nat) : Nat :=
  Nat.add (rad78 (fun n => Nat.mul (F n) n))
    (Nat.mul 6084 (Nat.add (rad78 G) (rad78 (fun n => shell 6084 n 1))))

/-- `errS / 2^(f+g) ≤ Eb / 10²⁰`. -/
noncomputable def errChk (F G : Nat → Nat) (fg Eb : Nat) : Bool :=
  Nat.ble (Nat.mul (errS F G) 100000000000000000000) (Nat.mul Eb (Nat.shiftLeft 1 fg))

/-- The norm of the scalar array is below `2⁵⁰`. -/
noncomputable def normS : Bool :=
  Nat.ble (Nat.add (rad128 (phiR FA)) 1) 1125899906842624

end Row
end OVNS
