import OddViscousNS.Quant.Joint.Metric.Thresh1

/-!
# The threshold of the second energy (node N15)

`Gm_eq`: the coefficient `Gm` of the group, in powers of `q⁻¹`, with the logarithm of `Z` apart.
`q2`, `Thr2_of`.  The logarithm is paid at its own threshold `qL`: `x log q ≤ q` for `q ≥ qL x`, the
first power of `q` being tied at `U R³`, so that `1 + log q ≤ C q^ε` would lose a power.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic OVNS.Quant.NearFar JDeg
open OVNS.Quant.H2 (cBil cBil_nonneg)
open GN (SupBd)

/-! ### The logarithm -/

/-- The threshold of a logarithm. -/
def qL (x : ℝ) : ℝ := 4 * max 1 x * (1 + Real.log (max 1 x))

/-- **`x log q ≤ q`** at `qL x ≤ q`. -/
theorem qL_spec {x q : ℝ} (hq : qL x ≤ q) : x * Real.log q ≤ q := by
  set A := max 1 x with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  have hxA : x ≤ A := le_max_right _ _
  have hA0 : 0 < A := by linarith
  have hL : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hqq : 4 * A * (1 + Real.log A) ≤ q := hq
  have hq4 : 4 * A ≤ q := by nlinarith only [hqq, hL, hA0]
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hl0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  set t := q / A with ht
  have ht0 : 0 < t := by positivity
  have e1 : q = A * t := by
    simp only [ht]
    field_simp
  have h1 : 4 * (1 + Real.log A) ≤ t := by
    rw [ht, le_div_iff₀ hA0]
    linarith only [hqq]
  have h2 : Real.log t ≤ t / 2 := by
    have h3 := Real.log_le_sub_one_of_pos (by positivity : 0 < t / 2)
    have h4 : Real.log (t / 2) = Real.log t - Real.log 2 := Real.log_div ht0.ne' (by norm_num)
    have h5 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith only [h3, h4, h5]
  have h3 : Real.log q ≤ t := by
    rw [e1, Real.log_mul hA0.ne' ht0.ne']
    linarith only [h1, h2, hL]
  calc x * Real.log q ≤ A * Real.log q := mul_le_mul_of_nonneg_right hxA hl0
    _ ≤ A * t := mul_le_mul_of_nonneg_left h3 hA0.le
    _ = q := e1.symm

/-! ### The expansion of `Gm` -/

section

variable (φ D M : ℝ) (caps : Caps)

/-- The `q⁻¹` part. -/
def N1 : ℝ :=
  (2 ^ 28 * cp caps.WS ^ 2 + 2 ^ 18 * (Zs D * cp caps.AS ^ 2) +
    CZh * (1 + M) * cp caps.BS) * (2 * CLow 1 * M) +
    (2 ^ 30 + 2 ^ 16) * (Real.sqrt 33 * (3 * M * cp caps.AS * cp caps.WS))

/-- The `q⁻¹ log q` part. -/
def N1L : ℝ := CZh * M * cp caps.BS * (2 * CLow 1 * M)

/-- The `q⁻²` part. -/
def N2 : ℝ :=
  2 ^ 19 * D * cls2 (cp caps.WS) (cp caps.WS) (cp caps.BS) (cp caps.BS) * (2 * CLow 1 * M) +
    2 ^ 36 * (2 * c4 * Real.sqrt (Zs D) * (cp caps.BS ^ 2 * cp caps.WS) +
      c4 ^ 2 * Real.sqrt (Zs D) * cp caps.BS ^ 3) +
    2 ^ 22 * D * (cp caps.BS * Real.sqrt 17 * (cp caps.AS * Real.sqrt (Z4s D)) * cp caps.WS) +
    2 ^ 18 * D * (c4 ^ 2 * ((41 * M * cp caps.BS) * cp caps.BS)) +
    2 * Kc caps * Xic caps + 2 ^ 36 * (hSrc φ caps * T0 D * (cp caps.WS ^ 2 + cp caps.AS ^ 2))

/-- The `q⁻³` part. -/
def N3 : ℝ := 2 ^ 23 * D ^ 2 * (c4 ^ 2 * (cp caps.BS ^ 2 * cp caps.WS))

/-- The numerator of `κ_y`. -/
def Ky : ℝ := 2 ^ 37 * c4 ^ 2 * (cp caps.BS * cp caps.WS)

/-- The `q⁻⁴` part. -/
def N4 : ℝ := 16 * (Ky caps / 128) ^ 2 * cp caps.yF ^ 2 + 16 * Om M caps ^ 2

end

lemma Gm_eq (φ D M : ℝ) {q : ℝ} (hq : q ≠ 0) (caps : Caps) :
    Gm φ D q M caps = N1 D M caps / q + N1L M caps * Real.log q / q + N2 φ D M caps / q ^ 2 +
      N3 D caps / q ^ 3 + N4 M caps / q ^ 4 := by
  simp only [Gm, gLow, Xcap, gSep, gHt, gBY, gSlot, kapY, N1, N1L, N2, N3, N4, Ky]
  field_simp
  ring

lemma kapY_eq (q : ℝ) (caps : Caps) : kapY q caps = Ky caps / q ^ 2 := rfl

section Thresholds

variable (CS cS X R : ℝ) (caps : Caps)

/-- The clip length. -/
abbrev lI : ℝ := lamI X R caps

/-- The root of the slow price of a clip. -/
def Spr : ℝ :=
  Real.sqrt (lamI X R caps * (4 * slowPrice CS (Ex cS R) R (lamI X R caps)))

/-- The shares of `Thr2`. -/
def qS2 : ℝ :=
  max (2 ^ 9 * (N1 (jointD R) (Mi CS cS R) caps * lamI X R caps)) <|
  max (qL (2 ^ 9 * (N1L (Mi CS cS R) caps * lamI X R caps))) <|
  max (rootQ 2 (2 ^ 9 * (N2 (R - X) (jointD R) (Mi CS cS R) caps * lamI X R caps +
    Ky caps * Spr CS cS X R caps))) <|
  max (rootQ 3 (2 ^ 9 * (N3 (jointD R) caps * lamI X R caps))) <|
  max (rootQ 4 (2 ^ 9 * (N4 (Mi CS cS R) caps * lamI X R caps))) <|
  max (cp caps.WS) <|
  max (2 ^ 11 * c4 * cp caps.yF) <|
  max (rootQ 2 (2 ^ 8 * Kc caps)) <|
  max (2 ^ 8 * cBil * cp caps.BS) <|
  max (2 ^ 9 * kapA R (Mi CS cS R) caps) (rootQ 2 (2 ^ 9 * kapB R caps))

/-- **The threshold of the second energy.** -/
def q2 : ℝ :=
  max (qTot₂ eta2 CS cS X R caps) <|
  max (force2Q (R - X) (jointD R) (Mi CS cS R) CS (Ex cS R) R caps) <|
  max (force1Q (R - X) R (Mi CS cS R) caps) <|
  max (etaQ2 * staticQ R (Mi CS cS R) caps) <|
  max (2 ^ 5 * force0Y (R - X) caps) (qS2 CS cS X R caps)

end Thresholds

variable {CS cS X R R₀ r : ℝ} {caps : Caps}

lemma lamI_nonneg : 0 ≤ lamI X R caps := by
  have h : 0 ≤ jointLam X R caps := by
    simp only [jointLam, lamStar, dZero]
    positivity
  simp only [lamI]
  positivity

/-- **`q2` gives `Thr2`.** -/
theorem Thr2_of (hdom : JDom R₀ X R) (hCS : 0 ≤ CS) (hq : q2 CS cS X R caps ≤ |r|) :
    Thr2 X R CS cS r caps := by
  simp only [q2, max_le_iff] at hq
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
  simp only [qS2, max_le_iff] at h6
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩ := h6
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  have hfl : jointSlowFloor X R caps ≤ |r| := (le_max_left _ _).trans ((le_max_left _ _).trans h1)
  obtain ⟨-, hφ, -, hr1, hr⟩ := floor_setup hdom hfl
  have hq0 : 0 < |r| := by linarith
  have hqne : |r| ≠ 0 := hq0.ne'
  have hEx := Ex_pos cS R
  have hM0 : 0 ≤ Mi CS cS R := by positivity
  have hC : 0 ≤ CS * Ex cS R := by positivity
  have hD : 1 ≤ jointD R := by
    unfold jointD
    nlinarith only [hR1]
  have hL0 : 0 ≤ lamI X R caps := lamI_nonneg
  obtain ⟨-, -, -, nkB, nK⟩ := Q_nonneg (φ := R - X) (D := R) (C := CS) (ex := Ex cS R) (caps := caps)
    hφ hR0 hM0 hR1 hC
  have hc := c4_pos
  have hA := cp_nonneg caps.AS
  have hB := cp_nonneg caps.BS
  have hW := cp_nonneg caps.WS
  have hY := cp_nonneg caps.yF
  have hC1 := CLow_nonneg 1
  have hlogD : 0 ≤ Real.log (jointD R) := Real.log_nonneg hD
  have hlog4 : 0 ≤ Real.log (4 * jointD R) := Real.log_nonneg (by linarith)
  have hT0 := T0_nonneg (jointD R)
  have hS := hSrc_nonneg hφ caps
  have hX : 0 ≤ Xic caps := by
    unfold Xic
    positivity
  have hD0 : 0 < jointD R := by linarith
  have hcl : 0 ≤ cls2 (cp caps.WS) (cp caps.WS) (cp caps.BS) (cp caps.BS) := by
    unfold cls2
    positivity
  have hN2 : 0 ≤ N2 (R - X) (jointD R) (Mi CS cS R) caps := by
    unfold N2
    positivity
  have hKy : 0 ≤ Ky caps := by
    unfold Ky
    positivity
  have hN3 : 0 ≤ N3 (jointD R) caps := by
    unfold N3
    positivity
  have hN4 : 0 ≤ N4 (Mi CS cS R) caps := by
    unfold N4
    positivity
  have hSp : 0 ≤ Spr CS cS X R caps := Real.sqrt_nonneg _
  refine ⟨h1, h2, h3, h4, h5, t6, t7, ?_, t9, ?_, ?_⟩
  · have := frac2 hq0 (by positivity : (0 : ℝ) < 2 ^ 8) nK t8
    exact this
  · have m1 := frac_le hq0 (by positivity : (0 : ℝ) < 2 ^ 9) t10
    have m2 := frac2 hq0 (by positivity : (0 : ℝ) < 2 ^ 9) nkB t11
    rw [kapQ_eq]
    have hq1 : kapB R caps / |r| ^ 2 ≤ 1 / 2 ^ 9 := m2
    norm_num at m1 hq1 ⊢
    linarith only [m1, hq1]
  · rw [Gm_eq _ _ _ hqne, kapY_eq]
    set ℓ := lamI X R caps with hℓ
    have m1 : N1 (jointD R) (Mi CS cS R) caps * ℓ / |r| ≤ 1 / 2 ^ 9 :=
      frac_le hq0 (by positivity) t1
    have m2 : (N1L (Mi CS cS R) caps * ℓ) * Real.log |r| / |r| ≤ 1 / 2 ^ 9 := by
      have := qL_spec t2
      rw [div_le_div_iff₀ hq0 (by positivity)]
      nlinarith only [this]
    have m3 : (N2 (R - X) (jointD R) (Mi CS cS R) caps * ℓ + Ky caps * Spr CS cS X R caps) / |r| ^ 2 ≤
        1 / 2 ^ 9 := frac2 hq0 (by positivity) (by positivity) t3
    have m4 : (N3 (jointD R) caps * ℓ) / |r| ^ 3 ≤ 1 / 2 ^ 9 :=
      frac3 hq0 (by positivity) (by positivity) t4
    have m5 : (N4 (Mi CS cS R) caps * ℓ) / |r| ^ 4 ≤ 1 / 2 ^ 9 :=
      frac4 hq0 (by positivity) (by positivity) t5
    have e : (N1 (jointD R) (Mi CS cS R) caps / |r| + N1L (Mi CS cS R) caps * Real.log |r| / |r| +
        N2 (R - X) (jointD R) (Mi CS cS R) caps / |r| ^ 2 + N3 (jointD R) caps / |r| ^ 3 +
        N4 (Mi CS cS R) caps / |r| ^ 4) * ℓ + Ky caps / |r| ^ 2 * Spr CS cS X R caps =
        N1 (jointD R) (Mi CS cS R) caps * ℓ / |r| +
        (N1L (Mi CS cS R) caps * ℓ) * Real.log |r| / |r| +
        (N2 (R - X) (jointD R) (Mi CS cS R) caps * ℓ + Ky caps * Spr CS cS X R caps) / |r| ^ 2 +
        (N3 (jointD R) caps * ℓ) / |r| ^ 3 + (N4 (Mi CS cS R) caps * ℓ) / |r| ^ 4 := by
      ring
    have e2 : Real.sqrt (ℓ * (4 * slowPrice CS (Ex cS R) R ℓ)) = Spr CS cS X R caps := rfl
    rw [e2, e]
    have n1 : (5 : ℝ) * (1 / 2 ^ 9) ≤ 1 / 2 ^ 6 := by norm_num
    linarith only [m1, m2, m3, m4, m5, n1]

end OVNS.Quant.Metric

end
