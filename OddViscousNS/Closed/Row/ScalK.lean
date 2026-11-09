import OddViscousNS.Closed.Row.RowK
import OddViscousNS.Closed.Row.RadK

/-!
# Kernel-side scalar band `44 ≤ K < 100`

`a(n) = v(n)/n`, rounded up on the grid `2⁻²¹`.  Specification: `Row/Scal.lean`.  No Mathlib here.
-/

namespace OVNS
namespace Row

/-- `⌈2²¹ a(n)⌉` for `0 < n ≤ 128²`, and `0` otherwise. -/
noncomputable def FA (n : Nat) : Nat :=
  cut 0 16384 n (lit (Nat.add 200000 (root n)) (fun u =>
    cdiv 188743680000000000 (Nat.mul (Nat.mul u u) n)))

/-- `∑_{0 < |p|² ≤ hi} ⌈2²¹ a(|p|²)⌉`. -/
noncomputable def psiSum (hi : Nat) : Nat := rad128 (fun n => cut 0 hi n (FA n))

/-- The right array of the band, `nz` layers from index `z0`. -/
noncomputable def arrS (nz z0 : Nat) : Nat :=
  arr 6372450 128 7 nz z0 (slice 17850 128 257 9 (fun _ => row0 50 128 16384 257 9 FA))

/-- The ceiling of `√C` for `1936 ≤ C ≤ 10000`, by bisection; the test re-checks `C ≤ cK²`. -/
noncomputable def csq (C : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ hi => hi)
    (fun _ ih lo hi => lit (Nat.shiftRight (Nat.add lo hi) 1) (fun m =>
      Bool.rec (motive := fun _ => Nat) (ih m hi) (ih lo m) (Nat.ble C (Nat.mul m m)))) 7) 43 100

/-- The test at the output `(x,y,z)`; `S` is the slot total. -/
noncomputable def scalTest (C S : Nat) : Bool :=
  litB (csq C) (fun cK => litB (Nat.sub 128 cK) (fun rho =>
    Bool.and (Nat.ble C (Nat.mul cK cK)) (Bool.and (Nat.ble cK 100)
      (Nat.ble (Nat.add (Nat.mul (Nat.mul S rho) 100000000000) 6597069766656000000000000)
        (Nat.mul (Nat.mul (Nat.mul 464 (gN C)) rho) 4398046511104)))))

/-- The output `(x,y,z)`: skipped unless `x ≥ y` and `1936 ≤ C < 10⁴`. -/
noncomputable def scalPt (r1 r2 r3 r4 y z x : Nat) : Bool :=
  litB (Nat.add (Nat.mul x x) (Nat.add (Nat.mul y y) (Nat.mul z z))) (fun C =>
    Bool.rec (motive := fun _ => Bool) true
      (Bool.rec (motive := fun _ => Bool)
        (scalTest C (Nat.add (rd 50 x r1) (Nat.mul 2 (Nat.add (rd 50 x r2)
          (Nat.add (rd 50 x r3) (rd 50 x r4))))))
        true (Nat.ble 10000 C))
      (Bool.and (Nat.ble y x) (Nat.ble 1936 C)))

/-- A layer of a product. -/
noncomputable def layer (c N : Nat) : Nat := win 6372450 c 1 N

/-- The outputs of a row of a layer, `0 ≤ x < 100`. -/
noncomputable def rowS (y L : Nat) : Nat :=
  win 50 (Nat.add 256 (Nat.mul 357 (Nat.add y 256))) 100 L

/-- One `y`: skipped when `y < z`. -/
noncomputable def scalY (l1 l2 l3 l4 z y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (litB (rowS y l1) (fun r1 => litB (rowS y l2) (fun r2 => litB (rowS y l3) (fun r3 =>
      litB (rowS y l4) (fun r4 => allN (scalPt r1 r2 r3 r4 y z) 100)))))
    (Nat.ble z y)

/-- One `z`. -/
noncomputable def scalZ (n1 n2 n3 n4 z : Nat) : Bool :=
  litB (layer z n1) (fun l1 => litB (layer (Nat.add z 64) n2) (fun l2 =>
    litB (layer (Nat.add z 64) n3) (fun l3 => litB (layer z n4) (fun l4 =>
      allN (scalY l1 l2 l3 l4 z) 71))))

/-- The whole band, from the four block products. -/
noncomputable def scalChk : Bool :=
  litB (Nat.mul (arrS 64 128) (arrS 64 128)) (fun n1 =>
  litB (Nat.mul (arrS 64 64) (arrS 64 128)) (fun n2 =>
  litB (Nat.mul (arrS 64 0) (arrS 65 192)) (fun n3 =>
  litB (Nat.mul (arrS 64 64) (arrS 65 192)) (fun n4 =>
    allN (scalZ n1 n2 n3 n4) 58))))

end Row
end OVNS
