import OddViscousNS.Quant.Joint.Force.H0Bound

/-!
# The thresholds of the `h₀` derivative (step J5, node N12)

Two ways to pay the whole `h₀` derivative at weight one, one at weight two:
* the multiplier mass of `(8.10)`, weight one and two: `Ch0 κ H₀ ≤ q`, `force0Y`, degree `(0, 3)`.
  The mass is `(Ch0 κ H₀/q)²/(4ζ)`, of size `q⁻² R⁶ L`, the printed mass;
* the source `N b_F`, weight one: `Ch0 κ P_F H₀ ≤ q`, `force0N`, degree `(1, 3)`, tied at `U R³`.
  This is the printed companion `P_F (1 + B_S) ‖h₀‖₁/q`.

`κ = kapH0 = 1 + W + c₄ B` has degree `(0, 2)`.  `force0Y_below`, `force0N_below`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace OVNS.Quant.Metric

open JDeg

/-- The threshold of the Young mass of `h₀`. -/
def force0Y (φ : ℝ) (caps : Caps) : ℝ := Ch0 * kapH0 caps * H0c φ caps

/-- The threshold of the source companion of `h₀`. -/
def force0N (φ : ℝ) (caps : Caps) : ℝ := Ch0 * kapH0 caps * cp caps.PF * H0c φ caps

theorem deg_kapH0 : JDeg 0 2 fun _ _ caps ↦ kapH0 caps :=
  (((const zero_le_one).up 0 2).add (WS.up 0 2)).add (BS.const_mul c4_pos.le)

/-- `Ch0 κ H₀`: `(0, 3)`; its square over `q²` is `q⁻² R⁶ L`. -/
theorem deg_force0Y : JDeg 0 3 fun X R caps ↦ force0Y (R - X) caps :=
  ((deg_kapH0.const_mul Ch0_pos.le).mul deg_H0c).up 0 3

/-- `Ch0 κ P_F H₀`: `(1, 3)`, tied at `U R³`. -/
theorem deg_force0N : JDeg 1 3 fun X R caps ↦ force0N (R - X) caps :=
  (((deg_kapH0.const_mul Ch0_pos.le).mul PF).mul deg_H0c).up 1 3

theorem force0Y_below : JointBelow fun X R caps ↦ force0Y (R - X) caps := deg_force0Y.toQ

theorem force0N_below : JointBelow fun X R caps ↦ force0N (R - X) caps := deg_force0N.toQ

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}
  {M C ex R D : ℝ} {q : Caps → ℝ} {near : Caps → ℝ → Prop}
  {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} {caps : Caps} {s t ζ : ℝ}

/-- **The whole `h₀` derivative as a source at weight one**, on a joint piece: `N b_F`,
`∫ N² ≤ 1` at `force0N ≤ q`. -/
theorem h0_joint_source (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hp' : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (hD : 1 ≤ D)
    (hq : force1Q φ D M caps ≤ q caps) (hN : force0N φ caps ≤ q caps) :
    (∀ u ∈ Icc s t, |h0Part 1 r g y u| ≤
        Ch0 * kapH0 caps * cp caps.PF * h0Bd φ r g y u / |r| * fastNorm 2 r g y u) ∧
      ∫ u in s..t, (Ch0 * kapH0 caps * cp caps.PF * h0Bd φ r g y u / |r|) ^ 2 ≤ 1 := by
  have hM : 0 ≤ M := slowSup_nonneg.trans (hp'.sup s ⟨le_rfl, hp'.hst⟩)
  have hκ0 : 0 ≤ Ch0 * kapH0 caps * cp caps.PF :=
    mul_nonneg (mul_nonneg Ch0_pos.le (kapH0_pos caps).le) (cp_nonneg _)
  exact ⟨fun u hu => h0Part_source_one h hr hp'.onPrefix hp'.hs hp'.ht hu,
    companion_paid h hp'.hs hp'.hst hp'.ht hp'.len hp'.onPrefix (by linarith) hM (hq.trans hp'.thr)
      hκ0 (hN.trans hp'.thr)⟩

/-- **The Young mass of `h₀`** on any clip of a joint piece: at `force0Y ≤ q` it is `≤ 1/(4ζ)`. -/
theorem h0_joint_mass (h : ActualSol μ φ r g y Ty)
    (hp' : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (hD : 1 ≤ D)
    (hq : force1Q φ D M caps ≤ q caps) (hY : force0Y φ caps ≤ q caps) (hζ : 0 < ζ) {u₁ u₂ : ℝ}
    (h1 : s ≤ u₁) (h2 : u₁ ≤ u₂) (h3 : u₂ ≤ t) :
    (∫ u in u₁..u₂, (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * ζ)) ≤ 1 / (4 * ζ) := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hM : 0 ≤ M := slowSup_nonneg.trans (hp'.sup s ⟨le_rfl, hp'.hst⟩)
  have hq' := hq.trans hp'.thr
  have hq1 := (force1Q_source hφ hM (by linarith) hq').1
  have hq0 : 0 < |r| := by linarith
  have hm := h0_mass_clip h hp'.hs hp'.hst hp'.ht hp'.len hp'.onPrefix (by linarith : 0 ≤ D) hM hq'
    hζ h1 h2 h3
  refine hm.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  have h0 : 0 ≤ Ch0 * kapH0 caps * H0c φ caps / |r| :=
    div_nonneg (mul_nonneg (mul_nonneg Ch0_pos.le (kapH0_pos caps).le) (H0c_nonneg hφ caps)) hq0.le
  have h4 : Ch0 * kapH0 caps * H0c φ caps / |r| ≤ 1 := by
    rw [div_le_iff₀ hq0, one_mul]
    exact hY.trans hp'.thr
  exact pow_le_one₀ h0 h4

end OVNS.Quant.Metric

end
