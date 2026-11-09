import Mathlib

/-!
# The physical coefficient of a resonant triad: elementary bounds

For a sorted fast triad with unsigned helical lengths `X ≤ Y ≤ Z ≤ X + Y` and `D = |m × k| ≤ XY`,
the dimensionless coefficient is `γ = D |(x+y+z)(x−y)(y−z)(z−x)| / (12√2 (XYZ)²)` where `x, y, z`
are the signed lengths (`|x| = X`, …).  `gamma_bound` gives `γ² ≤ C` (with the explicit constant
`32/(12√2)`, only existence matters), `gamma_small_difference` the same-sign inner-pair bound
`γ ≤ 8 (A − B)/(12√2 Z)`, i.e. `γ² ≤ (2/9)((A−B)/Z)²` (manuscript eq. quant-angle,
quant-small-difference).
-/

namespace OVNS.Quant

/-- Bound for the absolute value of a product of four factors. -/
private lemma abs_mul4_le {a b c d p q r t : ℝ} (ha : |a| ≤ p) (hb : |b| ≤ q) (hc : |c| ≤ r)
    (hd : |d| ≤ t) : |a * b * c * d| ≤ p * q * r * t := by
  rw [abs_mul, abs_mul, abs_mul]
  have hp : 0 ≤ p := (abs_nonneg a).trans ha
  have hq : 0 ≤ q := (abs_nonneg b).trans hb
  have hr : 0 ≤ r := (abs_nonneg c).trans hc
  gcongr

/-- `D |(x+y+z)(x−y)(y−z)(z−x)| ≤ 32 (XYZ)²` for a sorted triad with any signs. -/
theorem gamma_bound {X Y Z D x y z : ℝ} (hX : 0 < X) (hXY : X ≤ Y) (hYZ : Y ≤ Z) (hZ : Z ≤ X + Y)
    (hD0 : 0 ≤ D) (hD : D ≤ X * Y) (hx : |x| = X) (hy : |y| = Y) (hz : |z| = Z) :
    D * |(x + y + z) * (x - y) * (y - z) * (z - x)| ≤ 32 * (X * Y * Z) ^ 2 := by
  have hY0 : 0 < Y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hXZ : 0 ≤ X * Z ^ 3 := by positivity
  have key : |(x + y + z) * (x - y) * (y - z) * (z - x)| ≤ 16 * X * Z ^ 3 := by
    rcases (abs_eq hX.le).mp hx with h1 | h1 <;>
    rcases (abs_eq hY0.le).mp hy with h2 | h2 <;>
    rcases (abs_eq hZ0.le).mp hz with h3 | h3 <;>
    rw [h1, h2, h3]
    all_goals first
      | exact (abs_mul4_le (p := 3 * Z) (q := 2 * Z) (r := X) (t := 2 * Z)
          (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
          (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)).trans
          (by nlinarith)
      | exact (abs_mul4_le (p := 2 * X) (q := 2 * Z) (r := 2 * Z) (t := 2 * Z)
          (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
          (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)).trans
          (by nlinarith)
  calc D * |(x + y + z) * (x - y) * (y - z) * (z - x)| ≤ (X * Y) * (16 * X * Z ^ 3) :=
        mul_le_mul hD key (abs_nonneg _) (hD0.trans hD)
    _ = 16 * X ^ 2 * Y * Z * Z ^ 2 := by ring
    _ ≤ 16 * X ^ 2 * Y * (2 * Y) * Z ^ 2 := by gcongr; linarith
    _ = 32 * (X * Y * Z) ^ 2 := by ring

/-- Same-sign inner pair `x = A ≥ y = B > 0`, `|z| = Z` with `B ≤ A ≤ Z ≤ A + B`, `D ≤ AB`:
`D |(x+y+z)(x−y)(y−z)(z−x)| ≤ 8 ((A − B)/Z) (ABZ)²`. -/
theorem gamma_small_difference {A B Z D z : ℝ} (hB : 0 < B) (hBA : B ≤ A) (hAZ : A ≤ Z)
    (hZ : Z ≤ A + B) (hD0 : 0 ≤ D) (hD : D ≤ A * B) (hz : |z| = Z) :
    D * |(A + B + z) * (A - B) * (B - z) * (z - A)| ≤ 8 * ((A - B) / Z) * (A * B * Z) ^ 2 := by
  have hZ0 : 0 < Z := by linarith
  have hA0 : 0 < A := by linarith
  have hAB : 0 ≤ A - B := by linarith
  have hBZ : 0 ≤ B * Z ^ 2 * (A - B) := by positivity
  have key : |(A + B + z) * (A - B) * (B - z) * (z - A)| ≤ 4 * B * Z ^ 2 * (A - B) := by
    rcases (abs_eq hZ0.le).mp hz with h3 | h3 <;> rw [h3]
    · exact (abs_mul4_le (p := 3 * Z) (q := A - B) (r := Z) (t := B)
        (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
        (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)).trans
        (by nlinarith)
    · exact (abs_mul4_le (p := B) (q := A - B) (r := 2 * Z) (t := 2 * Z)
        (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
        (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)).trans
        (by nlinarith)
  have hR : 8 * ((A - B) / Z) * (A * B * Z) ^ 2 = 8 * (A - B) * A * B ^ 2 * Z * A := by
    field_simp
  rw [hR]
  calc D * |(A + B + z) * (A - B) * (B - z) * (z - A)|
        ≤ (A * B) * (4 * B * Z ^ 2 * (A - B)) :=
        mul_le_mul hD key (abs_nonneg _) (hD0.trans hD)
    _ = 4 * (A - B) * A * B ^ 2 * Z * Z := by ring
    _ ≤ 4 * (A - B) * A * B ^ 2 * Z * (2 * A) := by gcongr; linarith
    _ = 8 * (A - B) * A * B ^ 2 * Z * A := by ring

end OVNS.Quant
