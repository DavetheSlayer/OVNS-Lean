import OddViscousNS.Quant.Defs
import OddViscousNS.Quant.Arith.Squarefree
import OddViscousNS.Quant.Arith.Resonant.Defs

/-!
# Lemma quant-weighted — definitions (integer geometry of the sorted resonant fibre)

Integer squared norms `nsqZ`, the sorted fast fibre `sortedFibre n` (as a `Finset`, legs `(m, k)`
with `m + k + n = 0`, `|m| ≤ |k| ≤ |n|`, all vertical components nonzero), the coefficient
`gammaCoef a b c m k n` (eq. quant-gamma with the pattern `(a, b, c)` on `(m, k, n)`), the full
weighted count `WfibA n` (all eight patterns), the named inputs `QuadraticNormCount`
(Lemma quant-norm) and `FewPointsNotAbsIrred`, both proved, the target `QuantWeighted`, the
integer-coordinate data `Coords` of a resonant sorted triad (`Δ, x, y, z, s₂, s₃` with
`|k|² = Δx²`, `|m|² = Δy²`, `|n|² = Δz²` and the integer resonance), its derived quantities
(`t = x − s₂y`, `w = k₃`, `v = |n₃|`, `g = gcd(v,t)`, `L = n_h·k_h`, `J = det(k_h, n_h)`, the conic
coefficients `ca, cb, cc, cM`), the fixed-`t`/fixed-`w` filters, and the joint surface polynomial.
Signs: `h_k = b`, `s₂ = h_m h_k`, `s₃ = h_n h_k`.
-/

open MvPolynomial

noncomputable section

namespace OVNS.Quant

/-- `±1` as an integer. -/
def sgZ (a : Sgn) : ℤ := if a then 1 else -1

/-- Integer squared norm and dot product. -/
def nsqZ (k : Mode) : ℤ := ∑ i, k i ^ 2
def dotZ (k l : Mode) : ℤ := ∑ i, k i * l i

theorem absk_eq_sqrt_nsqZ (k : Mode) : absk k = Real.sqrt (nsqZ k) := by
  simp only [absk, absSq, nsqZ]
  push_cast
  rfl

/-- The all-incoming phase of the triad `m + k + n = 0`. -/
def phase3 (a b c : Sgn) (m k n : Mode) : ℝ := lam a m + lam b k + lam c n

/-- The integer cube `|coords| ≤ R`. -/
def modeBox (R : ℕ) : Finset Mode := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R

/-- The sorted fast fibre of the largest output `n`. -/
def sortedFibre (n : Mode) : Finset (Mode × Mode) := by
  classical
  exact ((modeBox (Nat.sqrt (nsqZ n).toNat)) ×ˢ (modeBox (Nat.sqrt (nsqZ n).toNat))).filter
    fun p => p.1 + p.2 + n = 0 ∧ nsqZ p.1 ≤ nsqZ p.2 ∧ nsqZ p.2 ≤ nsqZ n ∧
      p.1 2 ≠ 0 ∧ p.2 2 ≠ 0 ∧ n 2 ≠ 0

/-- `|m × k|`. -/
def crossAbs (m k : Mode) : ℝ := Real.sqrt ((nsqZ m * nsqZ k - dotZ m k ^ 2 : ℤ) : ℝ)

/-- eq. quant-gamma for the pattern `(a, b, c)` on `(m, k, n)`. -/
def gammaCoef (a b c : Sgn) (m k n : Mode) : ℝ :=
  let x := sg a * absk m
  let y := sg b * absk k
  let z := sg c * absk n
  crossAbs m k * |(x + y + z) * (x - y) * (y - z) * (z - x)| /
    (12 * Real.sqrt 2 * (absk m * absk k * absk n) ^ 2)

/-- `W(n)` over all eight helicity patterns (twice the one-pattern count). -/
def WfibA (n : Mode) : ℝ := by
  classical
  exact ∑ p ∈ sortedFibre n, ∑ s : Sgn × Sgn × Sgn,
    if phase3 s.1 s.2.1 s.2.2 p.1 p.2 n = 0 then gammaCoef s.1 s.2.1 s.2.2 p.1 p.2 n ^ 2 else 0

/-- **Lemma quant-norm** (uniform quadratic norm count) as a named input. -/
def QuadraticNormCount : Prop :=
  ∀ (C : ℕ) (η : ℝ), 0 < η → ∃ K : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ a M : ℤ, a ≠ 0 → M ≠ 0 →
    (|a| : ℝ) ≤ B ^ C → (|M| : ℝ) ≤ B ^ C →
    (((boxPts 2 fun _ => B ^ C).filter fun p => p 0 ^ 2 - a * p 1 ^ 2 = M).card : ℝ) ≤ K * B ^ η

/-- A `ℚ`-irreducible plane curve that is not absolutely irreducible has at most `deg²` integer
points (Galois conjugates + plane Bézout). -/
def FewPointsNotAbsIrred : Prop :=
  ∀ H : MvPolynomial (Fin 2) ℤ, Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H) →
    ¬ AbsIrred H → ∀ B : Fin 2 → ℝ,
      ((boxZeros H B).card : ℝ) ≤ (H.totalDegree : ℝ) ^ 2

/-- The target of the arithmetic chain: `W(n) ≤ C_η |n|^{p* + η}`. -/
def QuantWeighted : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Mode, WfibA n ≤ C * absk n ^ (pStar + η)

/-- The integer coordinate polynomial `Ψ(t, w, k) ∈ ℤ[t, w, k]` (variables `0, 1, 2`). -/
def Psi (Δ z n3 ni nj : ℤ) (s3 : ℤ) : MvPolynomial (Fin 3) ℤ :=
  let t := X 0; let w := X 1; let k := X 2
  let twoN3L : MvPolynomial (Fin 3) ℤ :=
    -(C (Δ * n3)) * (t + C (s3 * z)) ^ 2 - 2 * (C (n3 ^ 2) + C Δ * t ^ 2) * w
  let n3x : MvPolynomial (Fin 3) ℤ := C n3 * (t + C (s3 * z)) + t * w
  C (4 * n3 ^ 2 * nj ^ 2) * k ^ 2 + (twoN3L - C (2 * n3 * ni) * k) ^ 2
    + C (4 * n3 ^ 2 * nj ^ 2) * w ^ 2 - C (4 * nj ^ 2 * Δ) * n3x ^ 2

/-- The data of one resonant sorted triad in integer coordinates. -/
structure Coords (n k : Mode) where
  Δ : ℤ
  x : ℤ
  y : ℤ
  z : ℤ
  s2 : ℤ
  s3 : ℤ
  hΔ : 0 < Δ
  hy : 1 ≤ y
  hyx : y ≤ x
  hxz : x ≤ z
  hs2 : s2 = 1 ∨ s2 = -1
  hs3 : s3 = 1 ∨ s3 = -1
  hk : nsqZ k = Δ * x ^ 2
  hm : nsqZ (-k - n) = Δ * y ^ 2
  hn : nsqZ n = Δ * z ^ 2
  hres : k 2 * x + s2 * (-k - n) 2 * y + s3 * n 2 * z = 0
  hk3 : k 2 ≠ 0
  hm3 : (-k - n) 2 ≠ 0
  hn3 : n 2 ≠ 0

namespace Coords
variable {n k : Mode} (c : Coords n k)

def t : ℤ := c.x - c.s2 * c.y
def w (_ : Coords n k) : ℤ := k 2
def v (_ : Coords n k) : ℕ := (n 2).natAbs
def g : ℕ := Nat.gcd (n 2).natAbs (c.t).natAbs
def L (_ : Coords n k) : ℤ := n 0 * k 0 + n 1 * k 1
def J (_ : Coords n k) : ℤ := k 0 * n 1 - k 1 * n 0
def nh2 (_ : Coords n k) : ℤ := n 0 ^ 2 + n 1 ^ 2

/-- The fixed-`t` conic `(2 n₃ J)² = ca w² + cb w + cc` and its discriminant `cM`. -/
def Bt : ℤ := c.Δ * c.t ^ 2
def ca : ℤ := 4 * (-(c.Bt) ^ 2 + (c.Δ * c.z ^ 2 - 3 * n 2 ^ 2) * c.Bt - c.Δ * c.z ^ 2 * n 2 ^ 2)
def cb : ℤ := 4 * c.Δ * n 2 * (c.t + c.s3 * c.z) *
    (2 * c.nh2 * c.t - (c.t + c.s3 * c.z) * (n 2 ^ 2 + c.Δ * c.t ^ 2))
def cc : ℤ := c.Δ * n 2 ^ 2 * (c.t + c.s3 * c.z) ^ 2 * (4 * c.nh2 - c.Δ * (c.t + c.s3 * c.z) ^ 2)
def cM : ℤ := 16 * n 2 ^ 2 * c.nh2 * (c.Bt - c.Δ * c.z ^ 2) ^ 2 * (c.Bt + 3 * n 2 ^ 2)

end Coords

/-- `x = √(|k|²/Δ)`, `t = x − s₂ y` as functions of the modes. -/
def xOf (Δ : ℕ) (k : Mode) : ℤ := Nat.sqrt ((nsqZ k).toNat / Δ)
def tOf (Δ : ℕ) (s2 : ℤ) (n k : Mode) : ℤ := xOf Δ k - s2 * xOf Δ (-k - n)
def caOf (Δ : ℕ) (z n3 t : ℤ) : ℤ :=
  4 * (-(Δ * t ^ 2) ^ 2 + (Δ * z ^ 2 - 3 * n3 ^ 2) * (Δ * t ^ 2) - Δ * z ^ 2 * n3 ^ 2)

/-- Active middle legs `k` of the output `n` with relative signs `(s₂, s₃)` and `γ ≠ 0`. -/
def activePts (n : Mode) (s2 s3 : ℤ) : Finset Mode := by
  classical
  exact (modeBox (Nat.sqrt (nsqZ n).toNat)).filter fun k => (-k - n, k) ∈ sortedFibre n ∧
    ∃ a b c : Sgn, sgZ a * sgZ b = s2 ∧ sgZ c * sgZ b = s3 ∧
      phase3 a b c (-k - n) k n = 0 ∧ gammaCoef a b c (-k - n) k n ≠ 0

/-- The `g`-part of the weighted fibre. -/
def Wg (Δ : ℕ) (n : Mode) (g : ℕ) : ℝ := by
  classical
  exact ∑ p ∈ sortedFibre n, ∑ s : Sgn × Sgn × Sgn,
    if phase3 s.1 s.2.1 s.2.2 p.1 p.2 n = 0 ∧
        Nat.gcd (n 2).natAbs (tOf Δ (sgZ s.1 * sgZ s.2.1) n p.2).natAbs = g
    then gammaCoef s.1 s.2.1 s.2.2 p.1 p.2 n ^ 2 else 0

/-- `F(X₁,X₂,X₃) = 4g²n_j²(|k|² − Δx²)` at `t = gX₁`, `w = n₃X₂/g`, `X₃ = k_i`. -/
def surfacePoly (Δ z n3 ni nj s3 g : ℤ) : MvPolynomial (Fin 3) ℤ :=
  let X1 : MvPolynomial (Fin 3) ℤ := X 0
  let X2 : MvPolynomial (Fin 3) ℤ := X 1
  let X3 : MvPolynomial (Fin 3) ℤ := X 2
  let twoGL : MvPolynomial (Fin 3) ℤ := -C (2 * Δ * g ^ 2) * X1 ^ 2 * X2 - C (Δ * g ^ 3) * X1 ^ 2
    - C (2 * Δ * g ^ 2 * s3 * z) * X1 - C (Δ * g * z ^ 2) - C (2 * n3 ^ 2) * X2
  let xs : MvPolynomial (Fin 3) ℤ := C g * X1 + C (s3 * z) + X1 * X2
  C (4 * g ^ 2 * nj ^ 2) * X3 ^ 2 + (twoGL - C (2 * g * ni) * X3) ^ 2
    + C (4 * nj ^ 2 * n3 ^ 2) * X2 ^ 2 - C (4 * g ^ 2 * nj ^ 2 * Δ) * xs ^ 2

end OVNS.Quant

end
