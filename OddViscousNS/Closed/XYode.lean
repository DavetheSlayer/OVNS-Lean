import OddViscousNS.Closed.CubicFilter
import OddViscousNS.LocalBasic

/-!
# The `X` and `Y` laws along unforced filtered heat solutions

For `y` a heat solution of `y' = −Ay − Q_{rt}(y,y)` (`IsHeatSol (filtN r 0) (fun _ => 0) T y`),
on `0 ≤ s ≤ t < T`:
`X(y t) + 2∫_s^t J₁(y) = X(y s)` and `Y(y t) + 2∫_s^t Z(y) = Y(y s) − 2∫_s^t cubic(R(ru) y(u)) du`,
with `X, Y` continuous.  The odd term is absent on the filtered side (it is the filter), so these
hold for every real `r`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

variable {r : ℝ} {T : ℝ≥0∞} {y : ℝ → Field}

/-- The zero force is a good force. -/
private lemma goodForce_zero : GoodForce (fun _ => (0 : Field)) 0 := by
  refine ⟨fun _ => ⟨?_, ?_, ?_, ?_⟩, fun _ => by simp [hnorm_zero], fun _ => ?_⟩
  · simp [InH]
  · intro k; simp [conjV]; rfl
  · intro k; simp [dotM]
  · rfl
  · simp [hnorm_zero]

/-- The heat pair of the unforced filtered solution. -/
private lemma heatPair_y (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) :
    HeatPair 2 0 b y (fun t => 0 - filtN r 0 t (y t) (y t)) :=
  hy.heatPair (majorized_filtN r 0) goodForce_zero hb hbT

/-- Pairing against a negated force. -/
private lemma wPair_zero_sub (ω : Mode → ℝ) (c F : Field) :
    wPair ω c (0 - F) = -wPair ω c F := by
  unfold wPair
  rw [← tsum_neg]
  congr 1
  funext k
  simp [inner_neg_right]

private lemma wPair_X_y (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < T) :
    wPair ωX (y u) (0 - filtN r 0 u (y u) (y u)) = 0 := by
  rw [wPair_zero_sub, filtN, wPair_X_Qphase _ (hy.adm u hu huT), neg_zero]

private lemma wPair_Y_y (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < T) :
    wPair ωY (y u) (0 - filtN r 0 u (y u) (y u)) = -cubic (rotF (r * u) (y u)) := by
  rw [wPair_zero_sub, filtN, wPair_Y_Qphase _ (hy.adm u hu huT), add_zero]

private lemma lt_of_mem {s t u : ℝ} (hst : s ≤ t) (ht : ENNReal.ofReal t < T)
    (hu : u ∈ uIcc s t) : ENNReal.ofReal u < T := by
  rw [uIcc_of_le hst] at hu
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) ht

theorem X_law (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < T) :
    wE ωX (y t) + 2 * ∫ u in s..t, wDiss ωX (y u) = wE ωX (y s) := by
  have h := (heatPair_y hy (hs.trans hst) ht).weighted_energy_identity weightLE2_X hs hst le_rfl
  have h0 : ∫ u in s..t, wPair ωX (y u) (0 - filtN r 0 u (y u) (y u)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_]
    · simp
    · have hu' := hu; rw [uIcc_of_le hst] at hu'
      exact wPair_X_y hy (hs.trans hu'.1) (lt_of_mem hst ht hu)
  rw [h0] at h; linarith

theorem Y_law (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < T) :
    wE ωY (y t) + 2 * ∫ u in s..t, wDiss ωY (y u) =
      wE ωY (y s) - 2 * ∫ u in s..t, cubic (rotF (r * u) (y u)) := by
  have h := (heatPair_y hy (hs.trans hst) ht).weighted_energy_identity weightLE2_Y hs hst le_rfl
  have h0 : ∫ u in s..t, wPair ωY (y u) (0 - filtN r 0 u (y u) (y u)) =
      ∫ u in s..t, -cubic (rotF (r * u) (y u)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu' := hu; rw [uIcc_of_le hst] at hu'
    exact wPair_Y_y hy (hs.trans hu'.1) (lt_of_mem hst ht hu)
  rw [h0, intervalIntegral.integral_neg] at h; linarith

theorem continuousOn_X (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) : ContinuousOn (fun t => wE ωX (y t)) (Icc 0 b) := by
  exact (heatPair_y hy hb hbT).continuousOn_wE weightLE2_X hb

theorem continuousOn_Y (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) : ContinuousOn (fun t => wE ωY (y t)) (Icc 0 b) := by
  exact (heatPair_y hy hb hbT).continuousOn_wE weightLE2_Y hb

/-- The cubic along the solution is interval integrable. -/
theorem intervalIntegrable_cubic (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    IntervalIntegrable (fun u => cubic (rotF (r * u) (y u))) volume 0 b := by
  have h := ((heatPair_y hy hb hbT).intervalIntegrable_wPair weightLE2_Y hb).neg
  refine h.congr ?_
  intro u hu
  have hu' : u ∈ uIcc 0 b := uIoc_subset_uIcc hu
  have hu'' := hu'; rw [uIcc_of_le hb] at hu''
  simp only [Pi.neg_apply]
  rw [wPair_Y_y hy hu''.1 (lt_of_mem hb hbT hu'), neg_neg]

end OVNS
