import OddViscousNS.Quant.Joint.Sources.Budget

/-!
# J4: the slow threshold against `Q`

`jointBudget_le`: on the scaled caps `jointBudget ≲ U R^{5/2}` up to the subpower, a polynomial gap
`R^{1/2}` below `Q = U R³`.  `jointBudget_below` is the field `belowS` of `JointInterfaces` for
`D.qS = jointBudget`.  `JointData.slowBudget_of_le` is `SlowBudget` at `qSFull`, the input of
`JointData.slowCaps_of_budget`, for every package whose `qS` dominates the threshold;
`JointData.slowCaps` is then the field `slow`.

The degrees at `(y, W_S, √J_S, φ) ≍ (T, R^{3/2}, R^{3/2}, R)`, `T² = U R`:
`((y + 1)² + φ)(W_S + y + √J_S + 1) ≍ U R · R^{3/2}`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace OVNS.Quant

/-- **The joint slow threshold on the scaled caps**: `≲ K³ U R^{5/2}` up to the subpower. -/
theorem jointBudget_le {K c R₀ X R : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c) (hdom : JDom R₀ X R)
    {caps : Caps} (hcaps : CapsScaledJ K c X R caps) :
    jointBudget (R - X) caps ≤
      2 ^ 17 * (1 + c4) ^ 3 * K ^ 3 * (jointU X * R ^ ((5 : ℝ) / 2)) * Ex (3 * c) R := by
  obtain ⟨-, ⟨-, hY⟩, -, -, -, hJ, hW, -, -, -⟩ := hcaps
  have hR1 := hdom.one_lt_R
  have hR0 := hdom.R_pos
  have hU1 := hdom.one_lt_U
  have hU0 : 0 < jointU X := by linarith
  have hX1 := hdom.one_lt_X
  have hXR := hdom.X_le_R
  have hT0 := hdom.T_pos
  have hT2 := hdom.T_sq
  have hEc : 1 ≤ Ex c R := hdom.one_le_Ex hc
  have hc4 := c4_pos
  set E := K * Ex c R with hE
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le hK hEc
  have hE0 : 0 ≤ E := by linarith
  set ρ := R ^ ((3 : ℝ) / 2) with hρ
  have hρ2 : ρ ^ 2 = R ^ 3 := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le, ← Real.rpow_natCast]
    norm_num
  have hRρ : R ≤ ρ := by
    calc R = R ^ (1 : ℝ) := (Real.rpow_one R).symm
      _ ≤ ρ := Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num)
  have h1ρ : 1 ≤ ρ := hR1.le.trans hRρ
  have hρ0 : 0 ≤ ρ := by linarith
  have hU : jointU X ≤ R := by
    refine hdom.U_le.trans ?_
    calc R ^ ((1 : ℝ) / 8) ≤ R ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num)
      _ = R := Real.rpow_one R
  have hT : jointT X R ≤ R := by
    have h1 : jointT X R ≤ Real.sqrt (R * R) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hU hR0.le)
    rwa [Real.sqrt_mul_self hR0.le] at h1
  have hT1 : 1 ≤ jointT X R := by
    have h1 : 1 ≤ jointT X R ^ 2 := by
      rw [hT2]
      exact one_le_mul_of_one_le_of_one_le hU1.le hR1.le
    nlinarith
  -- the three caps
  have hY' : cp caps.yF ≤ E * jointT X R := cp_le (by positivity) hY
  have hW' : cp caps.WS ≤ E * ρ := cp_le (by positivity) (by simpa [slowExpHA] using hW)
  have hJ' : cp caps.JS ≤ E * R ^ 3 := by
    refine cp_le (by positivity) ?_
    have e3 : R ^ slowExpHA.eJ = R ^ 3 := by
      simp only [slowExpHA]
      exact_mod_cast Real.rpow_natCast R 3
    rw [← e3]
    exact hJ
  have hj : capJ caps ≤ E * ρ := by
    rw [capJ, ← Real.sqrt_sq (by positivity : 0 ≤ E * ρ)]
    refine Real.sqrt_le_sqrt (hJ'.trans ?_)
    rw [mul_pow, hρ2]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have hY0 := cp_nonneg caps.yF
  have hW0 := cp_nonneg caps.WS
  have hj0 := capJ_nonneg caps
  -- the two factors
  have hET : 1 ≤ E * jointT X R := one_le_mul_of_one_le_of_one_le hE1 hT1
  have hP1 : (cp caps.yF + 1) ^ 2 + (R - X) ≤ 5 * E ^ 2 * (jointU X * R) := by
    have h1 : cp caps.yF + 1 ≤ 2 * (E * jointT X R) := by linarith
    have h2 : (cp caps.yF + 1) ^ 2 ≤ (2 * (E * jointT X R)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h1 2
    have e1 : (2 * (E * jointT X R)) ^ 2 = 4 * E ^ 2 * (jointU X * R) := by
      rw [← hT2]
      ring
    have h3 : R - X ≤ E ^ 2 * (jointU X * R) := by
      have h4 : R ≤ jointU X * R := le_mul_of_one_le_left hR0.le hU1.le
      have h5 : jointU X * R ≤ E ^ 2 * (jointU X * R) :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ hE1)
      linarith
    linarith
  have hP2 : cp caps.WS + cp caps.yF + capJ caps + 1 ≤ 4 * (E * ρ) := by
    have h1 : E * jointT X R ≤ E * ρ := mul_le_mul_of_nonneg_left (hT.trans hRρ) hE0
    have h2 : 1 ≤ E * ρ := one_le_mul_of_one_le_of_one_le hE1 h1ρ
    linarith
  have hφ0 : 0 ≤ R - X := by linarith
  have hP10 : 0 ≤ (cp caps.yF + 1) ^ 2 + (R - X) := by positivity
  have hP20 : 0 ≤ cp caps.WS + cp caps.yF + capJ caps + 1 := by positivity
  have hmain : ((cp caps.yF + 1) ^ 2 + (R - X)) * (cp caps.WS + cp caps.yF + capJ caps + 1) ≤
      (5 * E ^ 2 * (jointU X * R)) * (4 * (E * ρ)) :=
    mul_le_mul hP1 hP2 hP20 (by positivity)
  have hRρ' : R * ρ = R ^ ((5 : ℝ) / 2) := by
    rw [hρ]
    nth_rewrite 1 [← Real.rpow_one R]
    rw [← Real.rpow_add hR0]
    norm_num
  have hEx : Ex (3 * c) R = Ex c R ^ 3 := by
    rw [show 3 * c = c + (c + c) by ring, Ex_add, Ex_add]
    ring
  have hc1 : 0 ≤ 2 ^ 12 * (1 + c4) ^ 3 := by positivity
  unfold jointBudget
  calc 2 ^ 12 * (1 + c4) ^ 3 *
        (((cp caps.yF + 1) ^ 2 + (R - X)) * (cp caps.WS + cp caps.yF + capJ caps + 1))
      ≤ 2 ^ 12 * (1 + c4) ^ 3 * ((5 * E ^ 2 * (jointU X * R)) * (4 * (E * ρ))) :=
        mul_le_mul_of_nonneg_left hmain hc1
    _ = 5 * 2 ^ 14 * (1 + c4) ^ 3 * K ^ 3 * (jointU X * R ^ ((5 : ℝ) / 2)) * Ex (3 * c) R := by
        rw [← hRρ', hEx, hE]
        ring
    _ ≤ 2 ^ 17 * (1 + c4) ^ 3 * K ^ 3 * (jointU X * R ^ ((5 : ℝ) / 2)) * Ex (3 * c) R := by
        have h6 : 0 ≤ (1 + c4) ^ 3 * K ^ 3 * (jointU X * R ^ ((5 : ℝ) / 2)) * Ex (3 * c) R := by
          have := Ex_pos (3 * c) R
          positivity
        nlinarith

/-- **The field `belowS` for `D.qS = jointBudget`**: no monomial reaches `Q`. -/
theorem jointBudget_below : JointBelow fun X R caps ↦ jointBudget (R - X) caps := by
  intro K c hK hc
  refine ⟨2 ^ 17 * (1 + c4) ^ 3 * K ^ 3, 3 * c, 0, fun X R hdom caps hcaps =>
    (jointBudget_le hK hc hdom hcaps).trans ?_⟩
  have hR := hdom.R_pos
  have hR1 := hdom.one_lt_R
  have hU := hdom.one_lt_U
  have hc4 := c4_pos
  have h1 : R ^ ((5 : ℝ) / 2) ≤ R ^ 3 := by
    calc R ^ ((5 : ℝ) / 2) ≤ R ^ ((3 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num)
      _ = R ^ 3 := Real.rpow_natCast R 3
  have hC : 0 ≤ 2 ^ 17 * (1 + c4) ^ 3 * K ^ 3 := by
    have : 0 ≤ K := by linarith
    positivity
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC) (Ex_pos _ _).le
  exact mul_le_mul_of_nonneg_left h1 (by linarith)

/-- **`SlowBudget` at `qSFull`**, for every package whose `qS` dominates the threshold.  J6 takes
`D.qS X R caps = jointBudget (R − X) caps`. -/
theorem JointData.slowBudget_of_le (D : JointData) {R₀ : ℝ}
    (h : ∀ X R, JDom R₀ X R → ∀ caps, jointBudget (R - X) caps ≤ D.qS X R caps) :
    Slow.SlowBudget R₀ D.qSFull :=
  (slowBudget_jointBudget R₀).mono fun X R hdom caps => (h X R hdom caps).trans (le_max_left _ _)

/-- **E7-P for the package, with no remaining input**: the field `slow` of `JointInterfaces`. -/
theorem JointData.slowCaps (D : JointData) {R₀ : ℝ}
    (h : ∀ X R, JDom R₀ X R → ∀ caps, jointBudget (R - X) caps ≤ D.qS X R caps) :
    SlowCapsJoint (Slow.R₁ R₀) (fun _ _ => 4) D.qSFull Slow.slowL Slow.slowC 36
      (fun _ _ _ _ _ _ _ => True) :=
  Slow.JointData.slowCaps_of_budget D (D.slowBudget_of_le h)

/-- **The fields `slow`, `belowS` of `JointInterfaces`** for the package of J2 and J4: nothing is
left open in them.  This is the check that the statements above are the ones the package needs. -/
theorem JointData.slow_fields (D : JointData) {R₀ : ℝ} (hR : D.R₀ = Slow.R₁ R₀)
    (hT : D.Tp = fun _ _ => 4) (hL : D.L = Slow.slowL) (hC : D.CS = Slow.slowC) (hc : D.cS = 36)
    (hS : D.Sl = fun _ _ _ _ _ _ _ => True)
    (hq : D.qS = fun X R caps => jointBudget (R - X) caps) :
    SlowCapsJoint D.R₀ D.Tp D.qSFull D.L D.CS D.cS D.Sl ∧ JointBelow D.qS := by
  constructor
  · rw [hR, hT, hL, hC, hc, hS]
    exact D.slowCaps (R₀ := R₀) fun X R _ caps => by rw [hq]
  · rw [hq]
    exact jointBudget_below

end OVNS.Quant

end
