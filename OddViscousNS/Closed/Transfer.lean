import OddViscousNS.Closed.Defs
import OddViscousNS.Physical

/-!
# Transfer of the metrics `X, Y, Z` between the heat solution and the physical solution

The filter `rotF` is unitary mode by mode and commutes with radial multipliers, so `X, Y, Z` are
invariant under it on solenoidal fields; real scalars pull out as squares; and the scaled physical
field `w(τ) = u(τ/ν)/(ν s)` of `u = scaleU ν r y` is `(1/s)·rotF (r τ) (y τ)`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

private lemma norm_rotF_eq (τ : ℝ) {w : Field} (hw : IsSolenoidal w) {k : Mode} (hk : k ≠ 0) :
    ‖rotF τ w k‖ = ‖w k‖ := by
  rw [show rotF τ w k = rot τ k (w k) from rfl, norm_rot, leray_of_perp hk (hw k)]

private lemma hmet_nsq_zero : hmet (nsq 0) = 0 := by
  simp [hmet, nsq]

theorem Xmet_rotF (τ : ℝ) {w : Field} (hw : IsSolenoidal w) : Xmet (rotF τ w) = Xmet w := by
  unfold Xmet
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte, norm_rotF_eq τ hw hk]

theorem Ymet_rotF (τ : ℝ) {w : Field} (hw : IsSolenoidal w) : Ymet (rotF τ w) = Ymet w := by
  unfold Ymet
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [hk, hmet_nsq_zero]
  · rw [norm_rotF_eq τ hw hk]

theorem Zmet_rotF (τ : ℝ) {w : Field} (hw : IsSolenoidal w) : Zmet (rotF τ w) = Zmet w := by
  unfold Zmet
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [hk, hmet_nsq_zero]
  · rw [norm_rotF_eq τ hw hk]

private lemma norm_smul_sq (c : ℝ) (w : Field) (k : Mode) :
    ‖((c : ℂ) • w) k‖ ^ 2 = c ^ 2 * ‖w k‖ ^ 2 := by
  rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem Xmet_smul (c : ℝ) (w : Field) : Xmet ((c : ℂ) • w) = ENNReal.ofReal (c ^ 2) * Xmet w := by
  rw [Xmet, Xmet, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg c)]
  congr 1
  split_ifs
  · simp
  · exact norm_smul_sq c w k

theorem Ymet_smul (c : ℝ) (w : Field) : Ymet ((c : ℂ) • w) = ENNReal.ofReal (c ^ 2) * Ymet w := by
  rw [Ymet, Ymet, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg c), norm_smul_sq]
  congr 1
  ring

theorem Zmet_smul (c : ℝ) (w : Field) : Zmet ((c : ℂ) • w) = ENNReal.ofReal (c ^ 2) * Zmet w := by
  rw [Zmet, Zmet, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg c), norm_smul_sq]
  congr 1
  ring

theorem scaled_scaleU {ν : ℝ} (hν : 0 < ν) (s r : ℝ) (y : ℝ → Field) (τ : ℝ) :
    scaled ν s (scaleU ν r y) τ = ((1 / s : ℝ) : ℂ) • rotF (r * τ) (y τ) := by
  have h := congrFun (scaleU_rescale hν r y) τ
  rw [← h, smul_smul]
  funext k
  simp only [scaled, Pi.smul_apply]
  congr 1
  push_cast
  field_simp

theorem Ymet_scaled_scaleU {ν : ℝ} (hν : 0 < ν) (s r : ℝ) {y : ℝ → Field} {τ : ℝ}
    (hy : IsSolenoidal (y τ)) :
    Ymet (scaled ν s (scaleU ν r y) τ) = ENNReal.ofReal ((1 / s) ^ 2) * Ymet (y τ) := by
  rw [scaled_scaleU hν, Ymet_smul, Ymet_rotF _ hy]

theorem Zmet_scaled_scaleU {ν : ℝ} (hν : 0 < ν) (s r : ℝ) {y : ℝ → Field} {τ : ℝ}
    (hy : IsSolenoidal (y τ)) :
    Zmet (scaled ν s (scaleU ν r y) τ) = ENNReal.ofReal ((1 / s) ^ 2) * Zmet (y τ) := by
  rw [scaled_scaleU hν, Zmet_smul, Zmet_rotF _ hy]

end OVNS
