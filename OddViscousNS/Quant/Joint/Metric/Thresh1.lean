import OddViscousNS.Quant.Joint.Metric.Output2

/-!
# The threshold of the first energy (node N14)

`q1`: the maximum of the thresholds of the layers and of the shares of `Thr1`; `Thr1_of`: `q1 ≤ |r|` gives
`Thr1`; `q1_below`: `JointBelow`, one line per monomial, at `D₁ = R⁴`.

The largest monomials: the group `q⁻¹ R³`, tied at `R³`, the operator norm of the metric, and
`q⁻² R^{11/2}`, `q⁻⁴ R¹²`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic OVNS.Quant.NearFar JDeg
open GN (SupBd)

/-! ### Fractions -/

lemma frac_le {a q c : ℝ} (hq : 0 < q) (hc : 0 < c) (h : c * a ≤ q) : a / q ≤ 1 / c := by
  rw [div_le_div_iff₀ hq hc]
  linarith

lemma frac_pow_le {b q c : ℝ} {n : ℕ} (hn : 0 < n) (hq : 0 < q) (hc : 0 < c) (hb : 0 ≤ b)
    (h : rootQ (n : ℝ) (c * b) ≤ q) : b / q ^ n ≤ 1 / c := by
  have h1 := le_rpow_of_rootQ (e := (n : ℝ)) (by positivity) (by positivity) h
  rw [Real.rpow_natCast] at h1
  rw [div_le_div_iff₀ (by positivity) hc]
  linarith

lemma frac2 {b q c : ℝ} (hq : 0 < q) (hc : 0 < c) (hb : 0 ≤ b) (h : rootQ 2 (c * b) ≤ q) :
    b / q ^ 2 ≤ 1 / c := frac_pow_le (n := 2) (by norm_num) hq hc hb (by simpa using h)

lemma frac3 {b q c : ℝ} (hq : 0 < q) (hc : 0 < c) (hb : 0 ≤ b) (h : rootQ 3 (c * b) ≤ q) :
    b / q ^ 3 ≤ 1 / c := frac_pow_le (n := 3) (by norm_num) hq hc hb (by simpa using h)

lemma frac4 {b q c : ℝ} (hq : 0 < q) (hc : 0 < c) (hb : 0 ≤ b) (h : rootQ 4 (c * b) ≤ q) :
    b / q ^ 4 ≤ 1 / c := frac_pow_le (n := 4) (by norm_num) hq hc hb (by simpa using h)

/-! ### The operator norm of the metric -/

/-- The `q⁻¹` part. -/
def kapA (D M : ℝ) (caps : Caps) : ℝ :=
  2 ^ 8 * (1 + c4) * cp caps.BS +
    Cst * ((1 + Real.sqrt (1 + Real.log D)) * cp caps.AS ^ 2 + 2 * (cp caps.AS * cp caps.WS) +
      cp caps.BS ^ 2 / D) + CZ * M * cp caps.BS

/-- The `q⁻²` part. -/
def kapB (D : ℝ) (caps : Caps) : ℝ := Cst * (D * (cp caps.AS * cp caps.BS))

lemma kapQ_eq (r D M : ℝ) (caps : Caps) :
    kapQ r D M caps = kapA D M caps / |r| + kapB D caps / |r| ^ 2 := by
  unfold kapQ X2StC kapA kapB
  ring

/-! ### The shares of the group -/

/-- The `q⁻¹` part of the mass. -/
def Q11 (R M D C ex : ℝ) (caps : Caps) : ℝ :=
  A11 R M D (cp caps.BS) * (8 * (C * ex * R ^ 2)) + A12 D (cp caps.BS) * (4 * slowPrice C ex R 1) +
    4 * A13 R D (cp caps.BS)

/-- The `q⁻²` part of the mass. -/
def Q12 (φ R M D C ex : ℝ) (caps : Caps) : ℝ :=
  B11 φ D caps * (8 * (C * ex * R ^ 2)) + 4 * B13 M D (cp caps.AS) (cp caps.BS)

/-- The `q⁻⁴` part of the mass. -/
def Q14 (R C ex : ℝ) (caps : Caps) : ℝ :=
  2 ^ 10 * c4 ^ 2 * Kc caps ^ 2 * (8 * (C * ex * R ^ 2) + 4 * cp caps.PF ^ 2)

/-- The `q⁻¹` part of `ν`. -/
def n11 (M D : ℝ) (caps : Caps) : ℝ := 2 * (5 / D) ^ 2 * (2 ^ 18 * (cL + 1) * M * cp caps.AS ^ 2)

/-- The `q⁻²` part of `ν`. -/
def n12 (M D : ℝ) (caps : Caps) : ℝ :=
  2 * (5 / D) ^ 2 * (2 ^ 22 * M * (cp caps.AS * cp caps.BS))

lemma mass_eq (φ R M D q C ex : ℝ) (caps : Caps) :
    kap1 φ R M D q caps * (8 * (C * ex * R ^ 2)) + kap2 D q caps * (4 * slowPrice C ex R 1) +
        4 * kap3 R M D q caps =
      Q11 R M D C ex caps / q + Q12 φ R M D C ex caps / q ^ 2 + Q14 R C ex caps / q ^ 4 := by
  simp only [kap1, kap2, kap3, Q11, Q12, Q14]
  ring

lemma nu_eq (q D M : ℝ) (caps : Caps) :
    nu1 q D M caps = n11 M D caps / q + n12 M D caps / q ^ 2 := by
  simp only [nu1, X12, n11, n12]
  ring

section Thresholds

variable (CS cS X R : ℝ) (caps : Caps)

/-- `M_∞`. -/
abbrev Mi : ℝ := CS * Ex cS R * R

/-- The shares of `Thr1`. -/
def qS1 : ℝ :=
  max (64 * Q11 R (Mi CS cS R) (R ^ 4) CS (Ex cS R) caps) <|
  max (rootQ 2 (64 * Q12 (R - X) R (Mi CS cS R) (R ^ 4) CS (Ex cS R) caps)) <|
  max (rootQ 4 (64 * Q14 R CS (Ex cS R) caps)) <|
  max (128 * n11 (Mi CS cS R) (R ^ 4) caps) <|
  max (rootQ 2 (128 * n12 (Mi CS cS R) (R ^ 4) caps)) <|
  max (rootQ 2 (2 ^ 24 * Kc caps)) <|
  max (2 ^ 23 * kapA R (Mi CS cS R) caps) (rootQ 2 (2 ^ 23 * kapB R caps))

/-- **The threshold of the first energy.** -/
def q1 : ℝ :=
  max (jointSlowFloor X R caps) <|
  max (force1Q (R - X) R (Mi CS cS R) caps) <|
  max (etaQ * staticQ R (Mi CS cS R) caps) <|
  max (qOneFull amp1 X R caps) <|
  max (qNF₁ (1 / 256) X R caps) <|
  max (2 ^ 5 * force0Y (R - X) caps) (qS1 CS cS X R caps)

end Thresholds

variable {CS cS X R R₀ r : ℝ} {caps : Caps}

/-- The nonnegativity of the terms of `qS1`. -/
lemma Q_nonneg {φ M D C ex : ℝ} (hφ : 0 ≤ φ) (hR : 0 < R) (hM : 0 ≤ M) (hD : 1 ≤ D) (hC : 0 ≤ C * ex) :
    0 ≤ Q12 φ R M D C ex caps ∧ 0 ≤ Q14 R C ex caps ∧ 0 ≤ n12 M D caps ∧ 0 ≤ kapB D caps ∧
      0 ≤ Kc caps := by
  have hD0 : 0 < D := by linarith
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlog4 : 0 ≤ Real.log (4 * D) := Real.log_nonneg (by linarith)
  have hA := cp_nonneg caps.AS
  have hB := cp_nonneg caps.BS
  have hW := cp_nonneg caps.WS
  have hP := cp_nonneg caps.PF
  have hc := c4_pos
  have hT := T0_nonneg D
  have hS := hSrc_nonneg hφ caps
  have hZ : 0 ≤ Zs D := by unfold Zs; positivity
  have hZ4 : 0 ≤ Z4s D := by unfold Z4s; positivity
  have hK := Kc_nonneg caps
  have hCs := Cst_nonneg
  refine ⟨?_, ?_, ?_, ?_, hK⟩
  · unfold Q12 B11 B11g B13
    positivity
  · unfold Q14
    positivity
  · unfold n12
    positivity
  · unfold kapB
    positivity

/-- **`q1` gives `Thr1`.** -/
theorem Thr1_of (hdom : JDom R₀ X R) (hCS : 0 ≤ CS) (hq : q1 CS cS X R caps ≤ |r|) :
    Thr1 X R CS cS (R ^ 4) r caps := by
  simp only [q1, max_le_iff] at hq
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq
  simp only [qS1, max_le_iff] at h7
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := h7
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  obtain ⟨-, hφ, -, hr1, hr⟩ := floor_setup hdom h1
  have hq0 : 0 < |r| := by linarith
  have hEx := Ex_pos cS R
  have hM0 : 0 ≤ Mi CS cS R := by positivity
  have hC : 0 ≤ CS * Ex cS R := by positivity
  have hD : 1 ≤ R ^ 4 := one_le_pow₀ hR1
  obtain ⟨n2, n4, n12', -, nK⟩ := Q_nonneg (φ := R - X) (D := R ^ 4) (caps := caps) hφ hR0 hM0 hD hC
  obtain ⟨-, -, -, nkB, -⟩ := Q_nonneg (φ := R - X) (D := R) (caps := caps) hφ hR0 hM0 hR1 hC
  have m1 := frac_le hq0 (by norm_num : (0 : ℝ) < 64) t1
  have m2 := frac2 hq0 (by norm_num : (0 : ℝ) < 64) n2 t2
  have m4 := frac4 hq0 (by norm_num : (0 : ℝ) < 64) n4 t3
  have m5 := frac_le hq0 (by norm_num : (0 : ℝ) < 128) t4
  have m6 := frac2 hq0 (by norm_num : (0 : ℝ) < 128) n12' t5
  have m7 := frac2 hq0 (by positivity : (0 : ℝ) < 2 ^ 24) nK t6
  have m8 := frac_le hq0 (by positivity : (0 : ℝ) < 2 ^ 23) t7
  have m9 := frac2 hq0 (by positivity : (0 : ℝ) < 2 ^ 23) nkB t8
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, m7, ?_, ?_⟩
  · rw [nu_eq]
    norm_num at m5 m6 ⊢
    linarith only [m5, m6]
  · rw [kapQ_eq]
    norm_num at m8 m9 ⊢
    linarith only [m8, m9]
  · rw [mass_eq]
    norm_num at m1 m2 m4 ⊢
    linarith only [m1, m2, m4]

end OVNS.Quant.Metric

end
