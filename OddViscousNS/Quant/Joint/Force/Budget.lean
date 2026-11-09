import OddViscousNS.Quant.Joint.Force.Path

/-!
# The force coefficient of `c_F` on a piece (step J5, node N12)

LOCAL363, Bodies 40, 41: at an `H³` time `force2 ≤ g c_F`, and `g` splits into a part paired with
`h ∈ L²_t` and a part paired with `h ∈ L^∞_t`:
`g ≤ gA · hBd + Sh · (C₂/q c_S + 2 Cm₂/q B (c_y/D + δ₀))`, `hBd`, `Sh` the two norms of `h`.

Only the separated `X₁` and the high `X₂` use the `L^∞_t` bound of `h`, because of their factors
`c_S`, `b_>` in `L²_t`.  No pointwise `H¹` bound of `corrRes` is used; the slow `H³` histories are
those of the source budget (`slow_three_piece_le`, `SlowOut.cy_piece_le`).
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}

/-! ### The constants of the piece -/

/-- `h_L = 32 c₄ φ √(J_S + J_F)`: the linear part of `‖H_ψ‖₁` in `L²_t`. -/
def hLc (φ : ℝ) (caps : Caps) : ℝ := 32 * c4 * φ * Real.sqrt (cp caps.JS + cp caps.JF)

/-- `h_Q = 64 c₄ φ²`: the quadratic part in `L²_t`, on a piece of length `≤ 4`. -/
def hQc (φ : ℝ) : ℝ := 64 * c4 * φ ^ 2

/-- `j_L = 32 c₄ φ (B_S + y)`: the linear part of `‖H_ψ‖₁` in `L^∞_t`. -/
def jLc (φ : ℝ) (caps : Caps) : ℝ := 32 * c4 * φ * (cp caps.BS + cp caps.yF)

/-- `j_Q = 32 c₄ φ²`: the quadratic part in `L^∞_t`. -/
def jQc (φ : ℝ) : ℝ := 32 * c4 * φ ^ 2

/-- The time-dependent bound of `h = ‖H_ψ‖₁`: LOCAL363, `C[(φ/q)(‖S‖₂ + ‖F‖₂) + (φ/q)²]`. -/
def hBd (φ r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  32 * c4 * φ / |r| * (slowNorm 2 r g y u + fastNorm 2 r g y u) + 32 * c4 * φ ^ 2 / r ^ 2

/-- `‖h‖_{L^∞_t}`: `j_L/q + j_Q/q²`. -/
def Shc (φ r : ℝ) (caps : Caps) : ℝ := jLc φ caps / |r| + jQc φ / |r| ^ 2

/-- The baseline and the native filter: `1 + 48 c₄ P_F` (TeX `1 + 384 P_F`). -/
def E1c (caps : Caps) : ℝ := 1 + 48 * c4 * cp caps.PF

/-- The comparable `X₁`: `√(1/q)` of `C b`. -/
def E2c (caps : Caps) : ℝ := 1536 * Real.sqrt 17 * cp caps.BS

/-- The separated `X₁`: `C C_hist`. -/
def E3c (C ex R : ℝ) (caps : Caps) : ℝ := 2 ^ 11 * c4 * Real.sqrt (chistSq C ex R caps)

/-- The low `X₂`, ordinary part: `C (W² + (1 + ln D) a²)`, both slots. -/
def E4c (D : ℝ) (caps : Caps) : ℝ :=
  2 ^ 29 * cp caps.WS ^ 2 + 2 ^ 19 * (9 + 8 * Real.log D) * cp caps.AS ^ 2

/-- The low `X₂`, heat part: `C D b²`, both slots. -/
def E5c (D : ℝ) (caps : Caps) : ℝ :=
  2 ^ 20 * D * cls2 (cp caps.WS) (cp caps.WS) (cp caps.BS) (cp caps.BS)

/-- The coefficient of `‖H_ψ‖₁` paired in `L²_t`, in front of `c_F`. -/
def gA (D M r : ℝ) (caps : Caps) : ℝ :=
  E1c caps + E2c caps / Real.sqrt |r| + E4c D caps / |r| + E5c D caps / |r| ^ 2 +
    2 * (CZh / |r| * (1 + M * (1 + Real.log |r|)) * cp caps.BS)

/-- The coefficient of `c_F` paired in `L²_t` through `c_S` and `c_y`. -/
def Vc (D r : ℝ) (g : Field) (y : ℝ → Field) (caps : Caps) (u : ℝ) : ℝ :=
  2 ^ 11 * c4 / |r| * slowNorm 3 r g y u +
    2 * Cm2 / |r| * cp caps.BS * (hnorm 3 (corrSlow r g y u) / D + delta0)

/-- **LOCAL363's `g`**. -/
def gF (φ D M r : ℝ) (g : Field) (y : ℝ → Field) (caps : Caps) (u : ℝ) : ℝ :=
  gA D M r caps * hBd φ r g y u + Shc φ r caps * Vc D r g y caps u

/-! ### Elementary facts -/

lemma cls2_nonneg {W U : ℝ} (hW : 0 ≤ W) (hU : 0 ≤ U) : 0 ≤ cls2 W W U U := by
  have := c4_pos
  unfold cls2
  positivity

lemma E4c_nonneg {D : ℝ} (hD : 1 ≤ D) (caps : Caps) : 0 ≤ E4c D caps := by
  have := Real.log_nonneg hD
  unfold E4c
  positivity

lemma E5c_nonneg {D : ℝ} (hD : 1 ≤ D) (caps : Caps) : 0 ≤ E5c D caps := by
  have := cls2_nonneg (cp_nonneg caps.WS) (cp_nonneg caps.BS)
  have hD0 : 0 ≤ D := by linarith
  unfold E5c
  positivity

lemma E2c_nonneg (caps : Caps) : 0 ≤ E2c caps := by
  have := cp_nonneg caps.BS
  unfold E2c
  positivity

lemma E1c_nonneg (caps : Caps) : 0 ≤ E1c caps := by
  have := cp_nonneg caps.PF
  have := c4_pos
  unfold E1c
  positivity

lemma gA_nonneg {D M r : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M) (hr : 1 ≤ |r|) (caps : Caps) :
    0 ≤ gA D M r caps := by
  have h1 := E1c_nonneg caps
  have h2 := E2c_nonneg caps
  have h3 := E4c_nonneg hD caps
  have h4 := E5c_nonneg hD caps
  have h5 := CZh_pos
  have h6 := Real.log_nonneg hr
  have h7 := cp_nonneg caps.BS
  have h8 := Real.sqrt_nonneg |r|
  have h9 := abs_nonneg r
  unfold gA
  positivity

lemma hBd_nonneg (hφ : 0 ≤ φ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    0 ≤ hBd φ r g y u := by
  have h1 := hnorm_nonneg 2 (PiS (actual r g y u))
  have h2 := hnorm_nonneg 2 (PiF (actual r g y u))
  have hc := c4_pos
  have h3 : 0 ≤ slowNorm 2 r g y u + fastNorm 2 r g y u := add_nonneg h1 h2
  have h4 := abs_nonneg r
  unfold hBd
  positivity

lemma Vc_nonneg {D r : ℝ} (hD : 0 ≤ D) (g : Field) (y : ℝ → Field) (caps : Caps) (u : ℝ) :
    0 ≤ Vc D r g y caps u := by
  have h1 := hnorm_nonneg 3 (PiS (actual r g y u))
  have h2 := hnorm_nonneg 3 (corrSlow r g y u)
  have h3 := cp_nonneg caps.BS
  have h4 := Cm2_pos
  have h5 := delta0_pos
  have h6 := abs_nonneg r
  have h7 := c4_pos
  have h8 : 0 ≤ slowNorm 3 r g y u := h1
  unfold Vc
  positivity

lemma Shc_nonneg (hφ : 0 ≤ φ) (r : ℝ) (caps : Caps) : 0 ≤ Shc φ r caps := by
  have h1 := cp_nonneg caps.BS
  have h2 := cp_nonneg caps.yF
  have hc := c4_pos
  have h4 := abs_nonneg r
  unfold Shc jLc jQc
  positivity

/-- `‖h‖_{L^∞_t}`, on the prefix: `hnorm_one_Hpsi_sup`. -/
lemma hBd_le_Shc (hr : r ≠ 0) (hφ : 0 ≤ φ) {caps : Caps} {s t : ℝ}
    (hP : OnPrefix caps r g y s t) (hu : u ∈ Icc s t) : hBd φ r g y u ≤ Shc φ r caps := by
  have hrp : 0 < |r| := abs_pos.mpr hr
  have hc := c4_pos
  obtain ⟨-, hbF, -, hbS, -⟩ := hP.1 u hu
  have h1 : slowNorm 2 r g y u + fastNorm 2 r g y u ≤ cp caps.BS + cp caps.yF :=
    add_le_add (hbS.trans (le_cp _)) (hbF.trans (le_cp _))
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 32 * c4 * φ / |r|)
  unfold hBd Shc jLc jQc
  rw [sq_abs]
  have e : 32 * c4 * φ * (cp caps.BS + cp caps.yF) / |r| =
      32 * c4 * φ / |r| * (cp caps.BS + cp caps.yF) := by ring
  rw [e]
  linarith

/-! ### The pointwise bound -/

/-- `2 X₂^{lo}` at the caps. -/
lemma two_X2Lo_le {D : ℝ} (hD : 1 ≤ D) {S : Field} {caps : Caps} (hr : 0 < |r|)
    (hW : wiener S ≤ cp caps.WS) (hA : hnorm 1 S ≤ cp caps.AS) (hB : hnorm 2 S ≤ cp caps.BS) :
    2 * X2Lo r D S S ≤ E4c D caps / |r| + E5c D caps / |r| ^ 2 := by
  have hW0 := wiener_nonneg S
  have hA0 := hnorm_nonneg 1 S
  have hB0 := hnorm_nonneg 2 S
  have hL := Real.log_nonneg hD
  have hD0 : 0 ≤ D := by linarith
  have h1 : wiener S * wiener S ≤ cp caps.WS ^ 2 := by
    rw [sq]
    exact mul_le_mul hW hW hW0 (hW0.trans hW)
  have h2 : hnorm 1 S * hnorm 1 S ≤ cp caps.AS ^ 2 := by
    rw [sq]
    exact mul_le_mul hA hA hA0 (hA0.trans hA)
  have h3 := Fam.cls2_mono hW hW hB hB hW0 hW0 hB0 hB0
  have e : E4c D caps / |r| + E5c D caps / |r| ^ 2 =
      2 * (2 ^ 28 / |r| * cp caps.WS ^ 2 +
        2 ^ 18 / |r| * ((9 + 8 * Real.log D) * cp caps.AS ^ 2) +
        2 ^ 19 * D / |r| ^ 2 * cls2 (cp caps.WS) (cp caps.WS) (cp caps.BS) (cp caps.BS)) := by
    unfold E4c E5c
    ring
  rw [e]
  unfold X2Lo
  gcongr

/-- **The pointwise force bound**: `force2 ≤ gF · c_F`, at an `H³` time of the prefix. -/
theorem force2_le_gF (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t D M : ℝ}
    (hP : OnPrefix caps r g y s t) (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty)
    (htr : ∀ u ∈ Icc s t, hnorm 2 (slowCorr r g y u) ≤ delta0)
    (hsup : ∀ u ∈ Icc s t, slowSup r g y u ≤ M) (hr1 : 1 ≤ |r|) (hWq : cp caps.WS ≤ |r|)
    (hD : 1 ≤ D) (hu : u ∈ Icc s t) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u))
    (hy3 : InH 3 (corrSlow r g y u)) :
    force2 r g y u ≤ gF φ D M r g y caps u * fastNorm 3 r g y u := by
  have hq : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hq
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hx := actual_adm h hu0 huT
  obtain ⟨cF1, -, cS1, cS2, cW⟩ := hP.1 u hu
  have hM := hsup u hu
  have hM0 : 0 ≤ M := slowSup_nonneg.trans hM
  have hWc : wiener (Sp r g y u) ≤ cp caps.WS := cW.trans (le_cp _)
  have hAc : hnorm 1 (Sp r g y u) ≤ cp caps.AS := cS1.trans (le_cp _)
  have hBc : hnorm 2 (Sp r g y u) ≤ cp caps.BS := cS2.trans (le_cp _)
  have hPc : fastNorm 1 r g y u ≤ cp caps.PF := cF1.trans (le_cp _)
  have hmain := force2_le h hr1 hu0 huT hF3 hS3 hD hM (hWc.trans hWq)
  have hD0 : 0 < D := by linarith
  have hRS := slowCorr_adm h hr hu0 huT
  have hSA : SlowAt (cp caps.BS) (cp caps.WS) M (PiS (actual r g y u)) (corrSlow r g y u)
      (slowCorr r g y u) :=
    ⟨hx.PiS, PiS_PiS_eq _, hy3, hRS.inH, rfl, htr u hu, hBc, hWc,
      GN.supBd_slowSup hx.PiS.inH hM⟩
  have htail := hSA.tail_le hD0
  obtain ⟨-, hHle⟩ := Hf_one h hr hu0 huT
  have hh0 := hnorm_nonneg 1 (Hf r g y u)
  have hSh := hBd_le_Shc hr hφ hP hu
  have hc3 := hnorm_nonneg 3 (Fp r g y u)
  set h1 := hnorm 1 (Hf r g y u) with hh1
  have hle1 : h1 ≤ hBd φ r g y u := hHle
  have hV := Vc_nonneg (r := r) hD0.le g y caps u
  have hA0 := gA_nonneg hD hM0 hr1 caps
  -- the coefficient
  have hb0 := hnorm_nonneg 2 (Sp r g y u)
  have hcf : 1 + 48 * c4 * fastNorm 1 r g y u + X1Cf r (Sp r g y u) + 2 * X2Cf r D (Sp r g y u) +
      2 * ZCf r M (Sp r g y u) ≤ gA D M r caps + Vc D r g y caps u := by
    have c1 : 1 + 48 * c4 * fastNorm 1 r g y u ≤ E1c caps := by
      have := c4_pos
      unfold E1c
      gcongr
    have c2 : X1Cf r (Sp r g y u) ≤ E2c caps / Real.sqrt |r| +
        2 ^ 11 * c4 / |r| * slowNorm 3 r g y u := by
      unfold X1Cf E2c
      have e : 1536 * Real.sqrt 17 * cp caps.BS / Real.sqrt |r| =
          1536 * Real.sqrt 17 / Real.sqrt |r| * cp caps.BS := by ring
      rw [e]
      have hs0 := Real.sqrt_nonneg |r|
      have h17 := Real.sqrt_nonneg (17 : ℝ)
      have := mul_le_mul_of_nonneg_left hBc
        (by positivity : 0 ≤ 1536 * Real.sqrt 17 / Real.sqrt |r|)
      exact add_le_add this le_rfl
    have c3 := two_X2Lo_le (r := r) hD hq hWc hAc hBc
    have c4' : Cm2 / |r| * (hnorm 2 (Sp r g y u) * tailB D (Sp r g y u)) ≤
        Cm2 / |r| * cp caps.BS * (hnorm 3 (corrSlow r g y u) / D + delta0) := by
      have hC := Cm2_pos
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul hBc htail (tailB_nonneg _ _) (cp_nonneg _)
    have c5 : ZCf r M (Sp r g y u) ≤ CZh / |r| * (1 + M * (1 + Real.log |r|)) * cp caps.BS := by
      have h6 := CZh_pos
      have h7 := Real.log_nonneg hr1
      unfold ZCf
      gcongr
    have e : gA D M r caps + Vc D r g y caps u = E1c caps + E2c caps / Real.sqrt |r| +
        E4c D caps / |r| + E5c D caps / |r| ^ 2 +
        2 * (CZh / |r| * (1 + M * (1 + Real.log |r|)) * cp caps.BS) +
        (2 ^ 11 * c4 / |r| * slowNorm 3 r g y u + 2 * (Cm2 / |r| * cp caps.BS *
          (hnorm 3 (corrSlow r g y u) / D + delta0))) := by
      unfold gA Vc
      ring
    rw [e]
    unfold X2Cf
    linarith
  have hbd : (gA D M r caps + Vc D r g y caps u) * h1 ≤ gF φ D M r g y caps u := by
    have a1 := mul_le_mul_of_nonneg_left hle1 hA0
    have a2 := mul_le_mul_of_nonneg_left (hle1.trans hSh) hV
    unfold gF
    nlinarith only [a1, a2]
  have hP0 : 0 ≤ h1 * fastNorm 3 r g y u := mul_nonneg hh0 hc3
  calc force2 r g y u ≤ _ := hmain
    _ ≤ (gA D M r caps + Vc D r g y caps u) * (h1 * fastNorm 3 r g y u) :=
        mul_le_mul_of_nonneg_right hcf hP0
    _ = (gA D M r caps + Vc D r g y caps u) * h1 * fastNorm 3 r g y u := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbd hc3

end OVNS.Quant.Metric

end
