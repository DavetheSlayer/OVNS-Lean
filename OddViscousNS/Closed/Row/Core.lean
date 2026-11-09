/-!
# Kernel-side definitions of the row certificate

No Mathlib here: the modules that run `decide +kernel` import only this file, which saves about 5 GB
of mapped `.olean` per worker.  Everything is written with raw `Nat.*` primitives and `Nat.rec`, so
that the kernel's GMP acceleration and its `whnf` cache do the work: `lit e k` forces `e` to a
literal before calling `k`, which memoizes rows keyed by literals
(`OddViscousNS_data/reports/t13_rowbound_route.md` §7).  The rows of the matrix band are not packed
slot by slot but read off one product (`rowW`), which evaluates each radial function once per radius
instead of once per slot (`OddViscousNS_data/reports/t13_evidence/refine_costs.md` §9).
Specifications: `Row/Arrays.lean`.
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

/-- Digits `[s, s+n)` of `N` in base `2^w`, by a shift and a bit mask. -/
noncomputable def winA (w s n N : Nat) : Nat :=
  Nat.land (Nat.shiftRight N (Nat.mul w s)) (Nat.sub (Nat.shiftLeft 1 (Nat.mul w n)) 1)

/-- The reversed radial table: digit `n j` holds `F (R2 - j)`, for `j ≤ R2`. -/
noncomputable def ftR (w n R2 bA : Nat) (F : Nat → Nat) : Nat :=
  pkB (Nat.mul w n) (fun j => F (Nat.sub R2 j)) (Nat.add R2 1) bA 0

/-- The weights: digit `t + n (t-R)²` holds `wt t`, for `t < n`. -/
noncomputable def qW (w n R b : Nat) (wt : Nat → Nat) : Nat :=
  pkB 0 (fun t => Nat.shiftLeft (wt t) (Nat.mul w (Nat.add t (Nat.mul n (sq R t))))) n b 0

/-- The product of the two, cut to its first `R2 + 1` rows of `n` digits: digit `t + n k` holds
`F (R2 - k + (t-R)²) wt t`, one term per digit. -/
noncomputable def prL (w n R R2 b bA : Nat) (F wt : Nat → Nat) : Nat :=
  Nat.land (Nat.mul (ftR w n R2 bA F) (qW w n R b wt))
    (Nat.sub (Nat.shiftLeft 1 (Nat.mul w (Nat.mul n (Nat.add R2 1)))) 1)

/-- Superblock `J`: rows `[1024 J, 1024 J + 1024)` of the product. -/
noncomputable def sblk (w n PR J : Nat) : Nat :=
  winA w (Nat.mul (Nat.mul 1024 n) J) (Nat.mul 1024 n) PR

/-- Block `jj` of superblock `J`: its rows `[64 jj, 64 jj + 64)`. -/
noncomputable def blk (w n PR J jj : Nat) : Nat :=
  winA w (Nat.mul (Nat.mul 64 n) jj) (Nat.mul 64 n) (sblk w n PR J)

/-- The row of `wt · F` keyed by `s`: row `k = R2 - s` of the product `PR = prL … F wt`, read through
its memoized superblock and block, so that no window copies more than its parent (the checkers keep
every intermediate number); `0` outside the ball. -/
noncomputable def rowW (w n R2 PR s : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (lit (Nat.sub R2 s) (fun k =>
    lit (Nat.div k 1024) (fun J => lit (Nat.mod (Nat.div k 64) 16) (fun jj =>
      winA w (Nat.mul n (Nat.mod k 64)) n (blk w n PR J jj))))) (Nat.ble s R2)

/-- The row plus its key `s` in the lowest slot.  The checkers' caches hash a number literal by its
lowest bits, and every row ends in a zero slot (`x = -R` lies outside the ball once `s ≥ 1`); without
the key, the sums that build a slice all fall into one hash bucket, which con-leche scans linearly.
`sliceT` takes the keys out of each slice. -/
noncomputable def rowWS (w n R2 PR s : Nat) : Nat := Nat.add (rowW w n R2 PR s) s

/-- The row of `(x+y)² F` plus its key, from the rows of `x² F` (`P2`, with its key), `i F` (`P1`) and
`F` (`P0`), by the sign of `y = iy - R`: `x² + 2 y i - y (2R - y)` if `y ≥ 0`,
`x² + |y| (2R + |y|) - 2 |y| i` if `y < 0`. -/
noncomputable def rowXYg (w n R R2 P0 P1 P2 iy s : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.sub (Nat.add (rowWS w n R2 P2 s)
        (Nat.mul (Nat.mul (Nat.sub R iy) (Nat.add (Nat.mul 2 R) (Nat.sub R iy))) (rowW w n R2 P0 s)))
      (Nat.mul (Nat.mul 2 (Nat.sub R iy)) (rowW w n R2 P1 s)))
    (Nat.sub (Nat.add (rowWS w n R2 P2 s) (Nat.mul (Nat.mul 2 (Nat.sub iy R)) (rowW w n R2 P1 s)))
      (Nat.mul (Nat.mul (Nat.sub iy R) (Nat.sub (Nat.mul 2 R) (Nat.sub iy R))) (rowW w n R2 P0 s)))
    (Nat.ble R iy)

/-- The memoized slice of a row family `rw`. -/
noncomputable def slice (wP R n b : Nat) (rw : Nat → Nat → Nat) (zz : Nat) : Nat :=
  pkB wP (fun iy => lit (Nat.add (sq R iy) zz) (rw iy)) n b 0

/-- A slice of keyed rows (`rowWS`) with the keys taken out: the keys of slice `zz` are
`∑_iy (sq R iy + zz) X^(P iy)`, made of two small constants. -/
noncomputable def sliceT (wP R n b : Nat) (rw : Nat → Nat → Nat) (zz : Nat) : Nat :=
  Nat.sub (slice wP R n b rw zz)
    (Nat.add (pkB wP (fun iy => sq R iy) n b 0) (Nat.mul zz (pkB wP (fun _ => 1) n b 0)))

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

/-- Compare the cube `[0,Z)³` of output digits of the product `N` with the table `T`, one
`z`-layer of each at a time. -/
noncomputable def cubeChk (w P wPP off Z T N : Nat) : Bool :=
  litB (winA wPP off Z N) (fun Rg => allN (fun z =>
    litB (winA wPP z 1 Rg) (fun sl => litB (winA w (Nat.mul (Nat.mul Z Z) z) (Nat.mul Z Z) T) (fun Tz =>
      allN (fun y => Nat.beq (winA w (Nat.add off (Nat.mul P (Nat.add y off))) Z sl)
        (winA w (Nat.mul Z y) Z Tz)) Z))) Z)

/-! ### The fixed parameters of the matrix band: `R = 78`, `P = 201`, `w = 80` -/

/-- The product of the band for the radial function `F` and the weight `wt`. -/
noncomputable def pr78 (F wt : Nat → Nat) : Nat := prL 80 157 78 6084 8 13 F wt

/-- The right array of a kernel. -/
noncomputable def arrR78 (F : Nat → Nat) : Nat :=
  arr 3232080 78 8 157 0 (sliceT 16080 78 157 8 (fun _ => rowWS 80 157 6084 (pr78 F (fun _ => 1))))

/-- The left array with weight `x²`. -/
noncomputable def arrLx (F : Nat → Nat) : Nat :=
  arr 3232080 78 8 157 0 (sliceT 16080 78 157 8 (fun _ => rowWS 80 157 6084 (pr78 F (fun t => sq 78 t))))

/-- The left array with weight `(x+y)²`. -/
noncomputable def arrLxy (F : Nat → Nat) : Nat :=
  arr 3232080 78 8 157 0 (sliceT 16080 78 157 8
    (rowXYg 80 157 78 6084 (pr78 F (fun _ => 1)) (pr78 F (fun t => t)) (pr78 F (fun t => sq 78 t))))

/-- The table check of a product of the matrix band. -/
noncomputable def hhChk (T L R : Nat) : Bool :=
  cubeChk 80 201 3232080 156 44 T (Nat.mul L R)

/-- Reading the cube `[0,44)³`. -/
noncomputable def rdC (T x y z : Nat) : Nat :=
  rd 80 (Nat.add x (Nat.mul 44 (Nat.add y (Nat.mul 44 z)))) T

end Row
end OVNS
