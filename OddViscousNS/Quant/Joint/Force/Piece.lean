import OddViscousNS.Quant.Joint.Force.Budget

/-!
# The force coefficient in `L²_t` on a piece (step J5, node N12)

`GF` is an integrable majorant of `gF²`; `budG` bounds its integral by the source constants:
`h_L, h_Q` (`filter_sq_le`), `j_L, j_Q`, `C_hist²` (`slow_three_piece_le`), `C_y²`
(`SlowOut.cy_piece_le`).  This is Bodies 40, 41 and LOCAL363 before the roots are extracted.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}

/-- An integrable majorant of `gF²`. -/
def GF (φ D M r : ℝ) (g : Field) (y : ℝ → Field) (caps : Caps) (u : ℝ) : ℝ :=
  4 * (gA D M r caps ^ 2 * hBd φ r g y u ^ 2 +
    Shc φ r caps ^ 2 * ((2 ^ 11 * c4 / |r|) ^ 2 * slowNorm 3 r g y u ^ 2 +
      (2 * Cm2 / |r| * cp caps.BS / D) ^ 2 * hnorm 3 (corrSlow r g y u) ^ 2 +
      (2 * Cm2 / |r| * cp caps.BS * delta0) ^ 2))

/-- The integral of `GF`, in the source constants. -/
def budG (φ D M r C ex R : ℝ) (caps : Caps) : ℝ :=
  4 * (gA D M r caps ^ 2 * (3 * (hLc φ caps / |r|) ^ 2 + 3 * (hQc φ / |r| ^ 2) ^ 2) +
    Shc φ r caps ^ 2 * ((2 ^ 11 * c4 / |r|) ^ 2 * chistSq C ex R caps +
      (2 * Cm2 / |r| * cp caps.BS / D) ^ 2 * (4 * slowPrice C ex R 1) +
      4 * (2 * Cm2 / |r| * cp caps.BS * delta0) ^ 2))

lemma GF_nonneg (φ D M r : ℝ) (g : Field) (y : ℝ → Field) (caps : Caps) (u : ℝ) :
    0 ≤ GF φ D M r g y caps u := by
  unfold GF
  positivity

/-- `gF² ≤ GF`. -/
lemma gF_sq_le (φ D M r : ℝ) (g : Field) (y : ℝ → Field) (caps : Caps) (u : ℝ) :
    gF φ D M r g y caps u ^ 2 ≤ GF φ D M r g y caps u := by
  set x₁ := gA D M r caps * hBd φ r g y u
  set A := Shc φ r caps
  set x₂ := A * (2 ^ 11 * c4 / |r| * slowNorm 3 r g y u)
  set x₃ := A * (2 * Cm2 / |r| * cp caps.BS / D * hnorm 3 (corrSlow r g y u))
  set x₄ := A * (2 * Cm2 / |r| * cp caps.BS * delta0)
  have e1 : gF φ D M r g y caps u = x₁ + x₂ + x₃ + x₄ := by
    simp only [gF, Vc, x₁, x₂, x₃, x₄, A]
    ring
  have e2 : GF φ D M r g y caps u = 4 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) := by
    simp only [GF, x₁, x₂, x₃, x₄, A]
    ring
  rw [e1, e2]
  nlinarith only [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ - x₃), sq_nonneg (x₁ - x₄),
    sq_nonneg (x₂ - x₃), sq_nonneg (x₂ - x₄), sq_nonneg (x₃ - x₄)]

/-- `hBd²` is integrable, and `filter_sq_le` in the constants `h_L`, `h_Q`. -/
lemma hBd_sq_int (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 4) (hP : OnPrefix caps r g y s t) :
    IntervalIntegrable (fun u => hBd φ r g y u ^ 2) volume s t ∧
      ∫ u in s..t, hBd φ r g y u ^ 2 ≤ 3 * (hLc φ caps / |r|) ^ 2 + 3 * (hQc φ / |r| ^ 2) ^ 2 := by
  have ht0 := hs.trans hst
  have hS := continuousOn_slow_two h hs hst ht
  have hF : ContinuousOn (fastNorm 2 r g y) (uIcc s t) := by
    rw [uIcc_of_le hst]
    exact (norms_continuous h ht0 ht).2.1.mono (Icc_subset_Icc_left hs)
  have hI : IntervalIntegrable (fun u => hBd φ r g y u ^ 2) volume s t :=
    (((continuousOn_const.mul (hS.add hF)).add continuousOn_const).pow 2).intervalIntegrable
  refine ⟨hI, ?_⟩
  have h1 := filter_sq_le h hs hst ht hlen hP
  have hJ : 0 ≤ cp caps.JS + cp caps.JF := add_nonneg (cp_nonneg _) (cp_nonneg _)
  have e : 3 * (hLc φ caps / |r|) ^ 2 + 3 * (hQc φ / |r| ^ 2) ^ 2 =
      3 * ((32 * c4 * φ / |r|) ^ 2 * (cp caps.JS + cp caps.JF)) +
        3 * ((32 * c4 * φ ^ 2 / r ^ 2) ^ 2 * 4) := by
    unfold hLc hQc
    rw [sq_abs, div_pow, div_pow, mul_pow (32 * c4 * φ), Real.sq_sqrt hJ, div_pow, div_pow]
    ring
  rw [e]
  exact h1

/-- **The integral of the coefficient**: `GF` is integrable and its integral is at most `budG`. -/
theorem GF_int (h : ActualSol μ φ r g y Ty) {C ex R D M : ℝ}
    {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} {caps : Caps} {s t : ℝ}
    (hO : SlowOut C ex R Sl r g y s t) (h0 : 0 ≤ C * ex) (hR : 0 ≤ R) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 4) (hthr : jointBudget φ caps ≤ |r|)
    (hP : OnPrefix caps r g y s t) :
    IntervalIntegrable (GF φ D M r g y caps) volume s t ∧
      ∫ u in s..t, GF φ D M r g y caps u ≤ budG φ D M r C ex R caps := by
  obtain ⟨hI1, hV1⟩ := hBd_sq_int h hs hst ht hlen hP
  have hI2 : IntervalIntegrable (fun u => slowNorm 3 r g y u ^ 2) volume s t :=
    H2.slow_c3_integrable h hs hst ht
  have hI3 : IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume s t := hO.cy_int
  have hV2 := slow_three_piece_le h hO h0 hR hs hst ht hlen hthr hP
  have hV3 := hO.cy_piece_le h0 hR hst hlen
  set a := gA D M r caps ^ 2
  set b := Shc φ r caps ^ 2
  set c := (2 ^ 11 * c4 / |r|) ^ 2
  set d := (2 * Cm2 / |r| * cp caps.BS / D) ^ 2
  set e := (2 * Cm2 / |r| * cp caps.BS * delta0) ^ 2
  have ha : 0 ≤ a := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  have hc : 0 ≤ c := sq_nonneg _
  have hd : 0 ≤ d := sq_nonneg _
  have he : 0 ≤ e := sq_nonneg _
  have i1 : IntervalIntegrable (fun u => c * slowNorm 3 r g y u ^ 2 +
      d * hnorm 3 (corrSlow r g y u) ^ 2) volume s t := (hI2.const_mul c).add (hI3.const_mul d)
  have i2 : IntervalIntegrable (fun u => c * slowNorm 3 r g y u ^ 2 +
      d * hnorm 3 (corrSlow r g y u) ^ 2 + e) volume s t := i1.add intervalIntegrable_const
  have i3 : IntervalIntegrable (fun u => a * hBd φ r g y u ^ 2 + b * (c * slowNorm 3 r g y u ^ 2 +
      d * hnorm 3 (corrSlow r g y u) ^ 2 + e)) volume s t :=
    (hI1.const_mul a).add (i2.const_mul b)
  have hval : ∫ u in s..t, GF φ D M r g y caps u = 4 * (a * (∫ u in s..t, hBd φ r g y u ^ 2) +
      b * (c * (∫ u in s..t, slowNorm 3 r g y u ^ 2) +
        d * (∫ u in s..t, hnorm 3 (corrSlow r g y u) ^ 2) + (t - s) * e)) := by
    have e0 : GF φ D M r g y caps = fun u => 4 * (a * hBd φ r g y u ^ 2 +
        b * (c * slowNorm 3 r g y u ^ 2 + d * hnorm 3 (corrSlow r g y u) ^ 2 + e)) := rfl
    rw [e0, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hI1.const_mul a) (i2.const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add i1 intervalIntegrable_const,
      intervalIntegral.integral_add (hI2.const_mul c) (hI3.const_mul d),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
  refine ⟨i3.const_mul 4, ?_⟩
  rw [hval]
  have h3 : (t - s) * e ≤ 4 * e := mul_le_mul_of_nonneg_right hlen he
  have h4 : c * (∫ u in s..t, slowNorm 3 r g y u ^ 2) ≤ c * chistSq C ex R caps :=
    mul_le_mul_of_nonneg_left hV2 hc
  have h5 : d * (∫ u in s..t, hnorm 3 (corrSlow r g y u) ^ 2) ≤ d * (4 * slowPrice C ex R 1) :=
    mul_le_mul_of_nonneg_left hV3 hd
  have h6 := mul_le_mul_of_nonneg_left hV1 ha
  have h7 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h4 h5) h3) hb
  have e0 : budG φ D M r C ex R caps = 4 * (a * (3 * (hLc φ caps / |r|) ^ 2 +
      3 * (hQc φ / |r| ^ 2) ^ 2) + b * (c * chistSq C ex R caps +
        d * (4 * slowPrice C ex R 1) + 4 * e)) := rfl
  rw [e0]
  linarith

/-- `W_S ≤ q` from the slow threshold. -/
lemma cpW_le_jointBudget (hφ : 0 ≤ φ) (caps : Caps) : cp caps.WS ≤ jointBudget φ caps := by
  have hc := c4_pos
  have hY := cp_nonneg caps.yF
  have hW := cp_nonneg caps.WS
  have hj := capJ_nonneg caps
  unfold jointBudget
  rw [← sub_nonneg]
  ring_nf
  positivity

/-- **The force on a piece**, before the roots: at almost every time `force2 ≤ gF · c_F`,
`gF² ≤ GF`, and `∫ GF ≤ budG` on every sub-interval. -/
theorem force2_piece (h : ActualSol μ φ r g y Ty) {C ex R D M : ℝ}
    {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} {caps : Caps} {s t : ℝ}
    (hO : SlowOut C ex R Sl r g y s t) (h0 : 0 ≤ C * ex) (hR : 0 ≤ R) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 4) (hthr : jointBudget φ caps ≤ |r|)
    (hP : OnPrefix caps r g y s t) (hsup : ∀ u ∈ Icc s t, slowSup r g y u ≤ M) (hD : 1 ≤ D) :
    IntervalIntegrable (GF φ D M r g y caps) volume s t ∧
      (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
        ∫ u in u₁..u₂, GF φ D M r g y caps u ≤ budG φ D M r C ex R caps) ∧
      ∀ᵐ u ∂(volume.restrict (Icc s t)),
        force2 r g y u ≤ gF φ D M r g y caps u * fastNorm 3 r g y u := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  obtain ⟨hI, hV⟩ := GF_int h (D := D) (M := M) hO h0 hR hs hst ht hlen hthr hP
  obtain ⟨hf1, -, -⟩ := jointBudget_floors hφ caps
  have hr1 : 1 ≤ |r| := hf1.trans hthr
  have hq : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hq
  have hWq : cp caps.WS ≤ |r| := (cpW_le_jointBudget hφ caps).trans hthr
  refine ⟨hI, fun u₁ u₂ h1 h12 h2 => ?_, ?_⟩
  · refine le_trans ?_ hV
    exact intervalIntegral.integral_mono_interval h1 h12 h2
      (Filter.Eventually.of_forall fun u => GF_nonneg _ _ _ _ _ _ _ _) hI
  · filter_upwards [H2.ae_inH3_split h hs hst ht, ae_inH3_corr h hr hs hst ht,
      ae_restrict_mem measurableSet_Icc] with u h3 hy3 hu
    exact force2_le_gF h hP hs ht hO.trace hsup hr1 hWq hD hu h3.1 h3.2 hy3

end OVNS.Quant.Metric

end
