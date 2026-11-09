import OddViscousNS.Closed.Row.Core

/-!
# Kernel-side radial sums

`theta` packs `∑_{|x|≤R} X^{x²}`, so the digits of `th3` are the representation numbers of the box
and `dsum` folds a function over them; `th4` holds their prefix sums.  No Mathlib here.
Specification: `Row/Radial.lean`.
-/

namespace OVNS
namespace Row

/-- `∑_{i<n} X^{(i-R)²}`, `X = 2^w`. -/
noncomputable def theta (w R n b : Nat) : Nat :=
  pkB 0 (fun i => Nat.shiftLeft 1 (Nat.mul w (sq R i))) n b 0

/-- The cube of `theta`. -/
noncomputable def th3 (w R n b : Nat) : Nat :=
  lit (theta w R n b) (fun t => Nat.mul (Nat.mul t t) t)

/-- `th3` times `1 + X + ... + X^(M-1)`. -/
noncomputable def th4 (w R n b M bM : Nat) : Nat :=
  Nat.mul (th3 w R n b) (pkB w (fun _ => 1) M bM 0)

/-- `∑_{i<2^m} φ(lo+i) · digit i of N`, by halving `N`. -/
noncomputable def dsum (w : Nat) (φ : Nat → Nat) (m : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun N lo => Nat.mul (φ lo) (Nat.mod N (Nat.shiftLeft 1 w)))
    (fun m ih N lo => lit N (fun N' => Nat.add
      (ih (Nat.mod N' (Nat.shiftLeft 1 (Nat.mul w (Nat.shiftLeft 1 m)))) lo)
      (ih (Nat.shiftRight N' (Nat.mul w (Nat.shiftLeft 1 m))) (Nat.add lo (Nat.shiftLeft 1 m))))) m

/-- The radial sum over the box of radius `78` (`m = 13`). -/
noncomputable def rad78 (φ : Nat → Nat) : Nat := lit (th3 32 78 157 8) (fun t => dsum 32 φ 13 t 0)

/-- The radial sum over the box of radius `128` (`m = 15`). -/
noncomputable def rad128 (φ : Nat → Nat) : Nat := lit (th3 32 128 257 9) (fun t => dsum 32 φ 15 t 0)

/-- The ball counts `N(t)` for `128 ≤ t ≤ 258` satisfy `39 (t+3)³ ≤ 10 N(t)`, `2 N(t) ≤ 9 (t-3)³`. -/
noncomputable def seedChk : Bool :=
  litB (th4 32 258 517 10 66565 17) (fun T => allN (fun i =>
    litB (Nat.add 128 i) (fun t =>
    litB (rd 32 (Nat.mul t t) T) (fun N =>
      Bool.and (Nat.ble (Nat.mul 2 N) (Nat.mul 9 (Nat.mul (Nat.mul (Nat.sub t 3) (Nat.sub t 3)) (Nat.sub t 3))))
        (Nat.ble (Nat.mul 39 (Nat.mul (Nat.mul (Nat.add t 3) (Nat.add t 3)) (Nat.add t 3)))
          (Nat.mul 10 N))))) 131)

/-- The cut `lo < n ≤ hi`. -/
noncomputable def cut (lo hi n x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0
    (Bool.rec (motive := fun _ => Nat) x 0 (Nat.ble n lo)) (Nat.ble n hi)

/-- `∑_{lo < |p|² ≤ hi} ⌈2^64/|p|⁴⌉`. -/
noncomputable def s4Sum (lo hi : Nat) : Nat :=
  rad128 (fun n => cut lo hi n (Nat.div (Nat.add 18446744073709551616 (Nat.sub (Nat.mul n n) 1)) (Nat.mul n n)))

end Row
end OVNS
