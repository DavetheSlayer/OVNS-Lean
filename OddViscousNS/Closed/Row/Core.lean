/-!
# Kernel-side definitions of the row certificate

No Mathlib here: the modules that run `decide +kernel` import only this file, which saves about 5 GB
of mapped `.olean` per worker.  Everything is written with raw `Nat.*` primitives and `Nat.rec`, so
that the kernel's GMP acceleration and its `whnf` cache do the work: `lit e k` forces `e` to a
literal before calling `k`, which memoizes rows keyed by literals
(`OddViscousNS_data/reports/t13_rowbound_route.md` §7).  Specifications: `Row/Arrays.lean`.
-/

namespace OVNS
namespace Row

/-- Evaluate `e`, then continue with `k`. -/
@[reducible] noncomputable def lit (e : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) e

/-- `∑_{i<2^n} g (lo+i) 2^(w i)` by binary splitting. -/
noncomputable def pk (w : Nat) (g : Nat → Nat) (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun lo => g lo)
    (fun n ih lo => Nat.add (ih lo)
      (Nat.shiftLeft (ih (Nat.add lo (Nat.shiftLeft 1 n))) (Nat.mul w (Nat.shiftLeft 1 n)))) n

/-- `∑_{i < n mod 2^b} g (lo+i) 2^(w i)`: the binary digits of `n` below `b` give the block sizes. -/
noncomputable def pkB (w : Nat) (g : Nat → Nat) (n : Nat) (b : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun b ih lo => Bool.rec (motive := fun _ => Nat) (ih lo)
      (Nat.add (pk w g b lo)
        (Nat.shiftLeft (ih (Nat.add lo (Nat.shiftLeft 1 b))) (Nat.mul w (Nat.shiftLeft 1 b))))
      (Nat.ble 1 (Nat.land 1 (Nat.shiftRight n b)))) b

/-- `(i - R)²` in natural numbers. -/
noncomputable def sq (R i : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.sub i R) (Nat.sub i R)) (Nat.mul (Nat.sub R i) (Nat.sub R i))

/-- A plain row keyed by `s`; `0` outside the ball. -/
noncomputable def row0 (w R R2 n b : Nat) (F : Nat → Nat) (s : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (pkB w (fun i => F (Nat.add s (sq R i))) n b 0) (Nat.ble s R2)

/-- The row of `i F`. -/
noncomputable def row1 (w R R2 n b : Nat) (F : Nat → Nat) (s : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0
    (pkB w (fun i => Nat.mul (F (Nat.add s (sq R i))) i) n b 0) (Nat.ble s R2)

/-- The row of `x² F`. -/
noncomputable def row2 (w R R2 n b : Nat) (F : Nat → Nat) (s : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0
    (pkB w (fun i => Nat.mul (F (Nat.add s (sq R i))) (sq R i)) n b 0) (Nat.ble s R2)

/-- The row of `(x+y)² F`, assembled from the three memoized rows;
`y₀ = (y)₊ = iy - R`, `y₁ = (-y)₊ = R - iy`. -/
noncomputable def rowXY (w R R2 n b : Nat) (F : Nat → Nat) (iy s : Nat) : Nat :=
  lit (row2 w R R2 n b F s) (fun r2 => lit (row1 w R R2 n b F s) (fun r1 =>
    lit (row0 w R R2 n b F s) (fun r0 =>
    Nat.sub (Nat.add r2 (Nat.add (Nat.mul (Nat.mul 2 (Nat.sub iy R)) r1)
        (Nat.mul (Nat.add (Nat.mul (Nat.sub iy R) (Nat.sub iy R))
          (Nat.add (Nat.mul (Nat.sub R iy) (Nat.sub R iy))
            (Nat.mul (Nat.mul 2 R) (Nat.sub R iy)))) r0)))
      (Nat.add (Nat.mul (Nat.mul 2 (Nat.sub R iy)) r1)
        (Nat.mul (Nat.mul (Nat.mul 2 R) (Nat.sub iy R)) r0)))))

/-- The memoized slice of a row family `rw`. -/
noncomputable def slice (wP R n b : Nat) (rw : Nat → Nat → Nat) (zz : Nat) : Nat :=
  pkB wP (fun iy => lit (Nat.add (sq R iy) zz) (rw iy)) n b 0

/-- The array: `nz` slices from `z0`. -/
noncomputable def arr (wPP R b nz z0 : Nat) (sl : Nat → Nat) : Nat :=
  pkB wPP (fun iz => lit (sq R iz) sl) nz b z0

/-- The cut `120 < A ≤ R2`. -/
noncomputable def shell (R2 A x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0
    (Bool.rec (motive := fun _ => Nat) x 0 (Nat.ble A 120)) (Nat.ble A R2)

/-- `⌊N A/(290A+234)⌋`, for `A^(3-2)/h_A`. -/
noncomputable def F3 (N R2 A : Nat) : Nat :=
  shell R2 A (Nat.div (Nat.mul N A) (Nat.add (Nat.mul 290 A) 234))

/-- `⌊N/(290A+234)⌋`, for `A^(2-2)/h_A`. -/
noncomputable def F2 (N R2 A : Nat) : Nat :=
  shell R2 A (Nat.div N (Nat.add (Nat.mul 290 A) 234))

/-- `⌊N/(A(290A+234))⌋`, for `A^(1-2)/h_A`. -/
noncomputable def F1 (N R2 A : Nat) : Nat :=
  shell R2 A (Nat.div N (Nat.mul A (Nat.add (Nat.mul 290 A) 234)))

/-- `⌊N/(A²(290A+234))⌋`, for `A^(0-2)/h_A`. -/
noncomputable def F0 (N R2 A : Nat) : Nat :=
  shell R2 A (Nat.div N (Nat.mul (Nat.mul A A) (Nat.add (Nat.mul 290 A) 234)))

/-- `N / X^s % X^n` for `X = 2^w`. -/
noncomputable def win (w s n N : Nat) : Nat :=
  Nat.mod (Nat.shiftRight N (Nat.mul w s)) (Nat.shiftLeft 1 (Nat.mul w n))

/-- The digit of `N` at position `i`, base `2^w`. -/
noncomputable def rd (w i N : Nat) : Nat :=
  Nat.mod (Nat.shiftRight N (Nat.mul w i)) (Nat.shiftLeft 1 w)

/-- Force evaluation, with a Boolean result. -/
@[reducible] noncomputable def litB (e : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) e

/-- `∀ i < n, g i`. -/
noncomputable def allN (g : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => Bool.and (g i) ih) n

/-- Compare the cube `[0,Z)³` of output digits of the product `N` with the table `T`. -/
noncomputable def cubeChk (w P wPP off Z T N : Nat) : Bool :=
  litB (win wPP off Z N) (fun Rg => allN (fun z =>
    litB (win wPP z 1 Rg) (fun sl => allN (fun y =>
      Nat.beq (win w (Nat.add off (Nat.mul P (Nat.add y off))) Z sl)
        (win w (Nat.mul Z (Nat.add y (Nat.mul Z z))) Z T)) Z)) Z)

/-! ### The fixed parameters of the matrix band: `R = 78`, `P = 201`, `w = 80` -/

/-- The right array of a kernel. -/
noncomputable def arrR78 (F : Nat → Nat) : Nat :=
  arr 3232080 78 8 157 0 (slice 16080 78 157 8 (fun _ => row0 80 78 6084 157 8 F))

/-- The left array with weight `x²`. -/
noncomputable def arrLx (F : Nat → Nat) : Nat :=
  arr 3232080 78 8 157 0 (slice 16080 78 157 8 (fun _ => row2 80 78 6084 157 8 F))

/-- The left array with weight `(x+y)²`. -/
noncomputable def arrLxy (F : Nat → Nat) : Nat :=
  arr 3232080 78 8 157 0 (slice 16080 78 157 8 (rowXY 80 78 6084 157 8 F))

/-- The table check of a product of the matrix band. -/
noncomputable def hhChk (T L R : Nat) : Bool :=
  cubeChk 80 201 3232080 156 44 T (Nat.mul L R)

/-- Reading the cube `[0,44)³`. -/
noncomputable def rdC (T x y z : Nat) : Nat :=
  rd 80 (Nat.add x (Nat.mul 44 (Nat.add y (Nat.mul 44 z)))) T

end Row
end OVNS
