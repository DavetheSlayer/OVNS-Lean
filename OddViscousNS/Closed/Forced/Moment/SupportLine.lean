import OddViscousNS.Closed.Moments

/-!
# The supporting line `Z ≥ ℓ Y − c_ℓ X`

With `ℓ = 13191/212` and `c_ℓ = 63940773/212000` (the chord of `j ↦ j h(j)` through `j = 24, 25`):
`j h(j) ≥ ℓ h(j) − c_ℓ` for every `j ≥ 1` (equality at `j = 24, 25`), hence
`Z ≥ ℓ Y − c_ℓ X` for admissible fields, and on a face `Y ≥ B > 0`, `X ≤ E`:
`Z/Y ≥ ℓ − c_ℓ E/B`, i.e. `t = Y/Z ≤ 1/(ℓ − c_ℓ E/B)` when the latter is positive.
-/

namespace OVNS

namespace Forced

/-- The per-shell supporting line. -/
theorem shell_supportline (j : ℕ) (hj : 1 ≤ j) :
    13191 / 212 * hmet j - 63940773 / 212000 ≤ (j : ℝ) * hmet j := by
  exact hmet_support_line hj

/-- `Z ≥ ℓ Y − c_ℓ X`. -/
theorem Zr_ge_supportline {w : Field} (hw : Adm 2 w) :
    13191 / 212 * Yr w - 63940773 / 212000 * Xr w ≤ Zr w := by
  have hX := (summable_X hw).hasSum
  have hY := (summable_Y hw).hasSum
  have hZ := (summable_Z hw).hasSum
  have h := (hZ.sub ((hY.mul_left (13191 / 212)).sub (hX.mul_left (63940773 / 212000)))).nonneg
    fun k ↦ by
    by_cases hk : k = 0
    · subst hk; simp [hw.mean]
    · have h1 : 1 ≤ nsq k := Nat.one_le_iff_ne_zero.2 fun h ↦ hk ((nsq_eq_zero_iff k).1 h)
      have hs := hmet_support_line h1
      rw [nsq_cast] at hs
      have ha : 0 ≤ ‖w k‖ ^ 2 := sq_nonneg _
      simp only [hk, ite_false, hm]
      nlinarith [mul_le_mul_of_nonneg_right hs ha]
  exact sub_nonneg.1 h

/-- The moment `t = Y/Z` on a face: `Y ≥ B`, `X ≤ E`, `ℓ − c_ℓ E/B ≥ 1/τ > 0` give `t ≤ τ`. -/
theorem tYZ_le_of_face {w : Field} (hw : Adm 2 w) (hw0 : w ≠ 0) {B E τ : ℝ} (hB : 0 < B)
    (hτ : 0 < τ) (hY : B ≤ Yr w) (hX : Xr w ≤ E)
    (hlate : 1 / τ ≤ 13191 / 212 - 63940773 / 212000 * (E / B)) : tYZ w ≤ τ := by
  have hZY := Zr_ge_supportline hw
  have hYp := Yr_pos_of_ne hw hw0
  have hZp := Zr_pos_of_ne hw hw0
  have hX0 := Xr_nonneg hw
  have hE0 : 0 ≤ E := hX0.trans hX
  have hEB : E / Yr w ≤ E / B := div_le_div_of_nonneg_left hE0 hB hY
  have hXY : Xr w ≤ E / B * Yr w := by
    calc Xr w ≤ E := hX
      _ = E / Yr w * Yr w := by field_simp
      _ ≤ E / B * Yr w := mul_le_mul_of_nonneg_right hEB hYp.le
  have h1 : 1 / τ * Yr w ≤ Zr w := by nlinarith [mul_le_mul_of_nonneg_right hlate hYp.le]
  have h2 : Yr w ≤ τ * Zr w := by
    have := mul_le_mul_of_nonneg_left h1 hτ.le
    rwa [← mul_assoc, mul_one_div_cancel hτ.ne', one_mul] at this
  unfold tYZ
  rw [div_le_iff₀ hZp]
  exact h2

end Forced

end OVNS
