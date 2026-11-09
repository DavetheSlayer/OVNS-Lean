import OddViscousNS.Quant.Joint.Metric.Output1

/-!
# The bracket at weight two, at one time (node N15)

`TIMED_METRIC_PROOF_V2.md` §9.  The group of the last edge, `D_S Y[B]`, the exterior and the slow slots
of `O`, as `[Gm + κ_y c_y + rowG] b_F² + c_F²/32 + 2 K₃ ‖H_{ψ,F}‖₁ b_F`.  Every monomial of `Gm` is one line
of (9.10), (9.11).
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic OVNS.Quant.NearFar
open GN (SupBd)

/-- The low price of `X₂` at the caps. -/
def Xcap (D q : ℝ) (caps : Caps) : ℝ :=
  2 ^ 28 / q * cp caps.WS ^ 2 + 2 ^ 18 / q * (Zs D * cp caps.AS ^ 2) +
    2 ^ 19 * D / q ^ 2 * cls2 (cp caps.WS) (cp caps.WS) (cp caps.BS) (cp caps.BS)

/-- (9.4): the low last edge. -/
def gLow (D q M : ℝ) (caps : Caps) : ℝ :=
  (Xcap D q caps + CZh / q * (1 + M * (1 + Real.log q)) * cp caps.BS) * (2 * CLow 1 * M)

/-- The separated primitive, without its `c_S`. -/
def gSep (D q : ℝ) (caps : Caps) : ℝ :=
  2 ^ 36 / q ^ 2 * (2 * c4 * Real.sqrt (Zs D) * (cp caps.BS ^ 2 * cp caps.WS) +
      c4 ^ 2 * Real.sqrt (Zs D) * cp caps.BS ^ 3) +
    2 ^ 23 * D ^ 2 / q ^ 3 * (c4 ^ 2 * (cp caps.BS ^ 2 * cp caps.WS))

/-- The coefficient of `c_S`. -/
def kapY (q : ℝ) (caps : Caps) : ℝ := 2 ^ 37 * c4 ^ 2 * (cp caps.BS * cp caps.WS) / q ^ 2

/-- The heat of the comparable primitive. -/
def gHt (D q : ℝ) (caps : Caps) : ℝ :=
  2 ^ 22 * D / q ^ 2 * (cp caps.BS * Real.sqrt 17 * (cp caps.AS * Real.sqrt (Z4s D)) * cp caps.WS)

/-- The coefficient of `b_F c_F` in `D_S Y[B]`. -/
def Om (M : ℝ) (caps : Caps) : ℝ :=
  2 ^ 22 * cls2 (c4 * (41 * M * cp caps.BS)) (cp caps.WS) (41 * M * cp caps.BS) (cp caps.BS) +
    2 ^ 15 * (30 * ((41 * M * cp caps.BS) * cp caps.AS) +
      c4 * ((41 * M * cp caps.BS) * cp caps.WS) +
      Real.sqrt (34 * (9 + 4 / 1)) * ((41 * M * cp caps.BS) * cp caps.BS))

/-- The coefficient of `b_F²` in `D_S Y[B]`. -/
def gBY (D q M : ℝ) (caps : Caps) : ℝ :=
  (2 ^ 30 + 2 ^ 16) / q * (Real.sqrt 33 * (3 * M * cp caps.AS * cp caps.WS)) +
    2 ^ 18 * D / q ^ 2 * (c4 ^ 2 * ((41 * M * cp caps.BS) * cp caps.BS))

/-- The exterior of `O`. -/
def Xic (caps : Caps) : ℝ := 8 * (cp caps.WS + c4 * cp caps.BS + c4 * cp caps.yF)

/-- The slots of `O`. -/
def gSlot (φ D q : ℝ) (caps : Caps) : ℝ :=
  2 ^ 36 / q ^ 2 * (hSrc φ caps * T0 D * (cp caps.WS ^ 2 + cp caps.AS ^ 2))

/-- **The coefficient of `b_F²` at weight two.** -/
def Gm (φ D q M : ℝ) (caps : Caps) : ℝ :=
  gLow D q M caps + gSep D q caps + gHt D q caps + gBY D q M caps +
    2 * (Kc caps / q ^ 2) * Xic caps + gSlot φ D q caps +
    16 * (kapY q caps / 128) ^ 2 * cp caps.yF ^ 2 + 16 * (Om M caps / q ^ 2) ^ 2

variable {r τ D M : ℝ} {S : Field} {caps : Caps}

/-- The cap of `X2Lo`. -/
lemma X2Lo_le (hq : 0 < |r|) (hD : 1 ≤ D) (hA : hnorm 1 S ≤ cp caps.AS) (hB : hnorm 2 S ≤ cp caps.BS)
    (hW : wiener S ≤ cp caps.WS) : X2Lo r D S S ≤ Xcap D |r| caps := by
  have hW0 := wiener_nonneg S
  have hA0 := hnorm_nonneg 1 S
  have hB0 := hnorm_nonneg 2 S
  have hc := c4_pos
  have hlog := Real.log_nonneg hD
  have hZ : 0 ≤ Zs D := by unfold Zs; positivity
  have hWc := cp_nonneg caps.WS
  have hAc := cp_nonneg caps.AS
  have hBc := cp_nonneg caps.BS
  have e1 : wiener S * wiener S ≤ cp caps.WS ^ 2 := by nlinarith only [hW, hW0]
  have e2 : hnorm 1 S * hnorm 1 S ≤ cp caps.AS ^ 2 := by nlinarith only [hA, hA0]
  have hD0 : 0 < D := by linarith
  simp only [X2Lo, Xcap, Zs, cls2]
  gcongr

/-- **`sepB` at the caps**, with `c_S` kept. -/
lemma sepB_le (hq : 0 < |r|) (hD : 1 ≤ D) (hB : hnorm 2 S ≤ cp caps.BS)
    (hW : wiener S ≤ cp caps.WS) :
    sepB D |r| S S S ≤ kapY |r| caps * hnorm 3 S + gSep D |r| caps := by
  have hW0 := wiener_nonneg S
  have hB0 := hnorm_nonneg 2 S
  have hc3 := hnorm_nonneg 3 S
  have hc := c4_pos
  have hlog := Real.log_nonneg hD
  have hWc := cp_nonneg caps.WS
  have hBc := cp_nonneg caps.BS
  have hZ := Real.sqrt_nonneg (Zs D)
  set b := hnorm 2 S with hb
  set W := wiener S with hWd
  set BC := cp caps.BS with hBC
  set WC := cp caps.WS with hWC
  set Z := Real.sqrt (Zs D) with hZd
  have e0 : Real.sqrt (9 + 8 * Real.log D) = Z := rfl
  have s1 : (b * W + W * b) * hnorm 3 S ≤ 2 * (BC * WC) * hnorm 3 S := by
    have : b * W ≤ BC * WC := mul_le_mul hB hW hW0 hBc
    have h2 : b * W + W * b ≤ 2 * (BC * WC) := by linarith only [this, mul_comm W b]
    exact mul_le_mul_of_nonneg_right h2 hc3
  have s2 : (b * W + W * b) * b ≤ 2 * (BC ^ 2 * WC) := by
    have h1 : b * W ≤ BC * WC := mul_le_mul hB hW hW0 hBc
    have h2 : (b * W) * b ≤ (BC * WC) * BC := mul_le_mul h1 hB hB0 (by positivity)
    nlinarith only [h2]
  have s3 : b * b * b ≤ BC ^ 3 := by
    have h1 : b * b ≤ BC * BC := mul_le_mul hB hB hB0 hBc
    have h2 : (b * b) * b ≤ (BC * BC) * BC := mul_le_mul h1 hB hB0 (by positivity)
    nlinarith only [h2]
  have s4 : b * b * W ≤ BC ^ 2 * WC := by
    have h1 : b * b ≤ BC * BC := mul_le_mul hB hB hB0 hBc
    have h2 : (b * b) * W ≤ (BC * BC) * WC := mul_le_mul h1 hW hW0 (by positivity)
    nlinarith only [h2]
  simp only [sepB, kapY, gSep, e0]
  rw [← hb, ← hWd, ← hBC, ← hWC]
  have t1 := mul_le_mul_of_nonneg_left s1 (by positivity : 0 ≤ 2 ^ 36 / |r| ^ 2 * c4 ^ 2)
  have t2 := mul_le_mul_of_nonneg_left s2 (by positivity : 0 ≤ 2 ^ 36 / |r| ^ 2 * (c4 * Z))
  have t3 := mul_le_mul_of_nonneg_left s3 (by positivity : 0 ≤ 2 ^ 36 / |r| ^ 2 * (c4 ^ 2 * Z))
  have t4 := mul_le_mul_of_nonneg_left s4 (by positivity : 0 ≤ 2 ^ 23 * D ^ 2 / |r| ^ 3 * c4 ^ 2)
  have e1 : 2 ^ 36 / |r| ^ 2 * (c4 ^ 2 * ((b * W + W * b) * hnorm 3 S) +
      c4 * Z * ((b * W + W * b) * b) + c4 ^ 2 * Z * (b * b * b)) +
      2 ^ 23 * D ^ 2 / |r| ^ 3 * (c4 ^ 2 * (b * b * W)) =
      2 ^ 36 / |r| ^ 2 * c4 ^ 2 * ((b * W + W * b) * hnorm 3 S) +
      2 ^ 36 / |r| ^ 2 * (c4 * Z) * ((b * W + W * b) * b) +
      2 ^ 36 / |r| ^ 2 * (c4 ^ 2 * Z) * (b * b * b) +
      2 ^ 23 * D ^ 2 / |r| ^ 3 * c4 ^ 2 * (b * b * W) := by ring
  have e2 : 2 ^ 37 * c4 ^ 2 * (BC * WC) / |r| ^ 2 * hnorm 3 S + (2 ^ 36 / |r| ^ 2 *
      (2 * c4 * Z * (BC ^ 2 * WC) + c4 ^ 2 * Z * BC ^ 3) + 2 ^ 23 * D ^ 2 / |r| ^ 3 *
        (c4 ^ 2 * (BC ^ 2 * WC))) =
      2 ^ 36 / |r| ^ 2 * c4 ^ 2 * (2 * (BC * WC) * hnorm 3 S) +
      2 ^ 36 / |r| ^ 2 * (c4 * Z) * (2 * (BC ^ 2 * WC)) +
      2 ^ 36 / |r| ^ 2 * (c4 ^ 2 * Z) * BC ^ 3 +
      2 ^ 23 * D ^ 2 / |r| ^ 3 * c4 ^ 2 * (BC ^ 2 * WC) := by ring
  rw [e1, e2]
  linarith only [t1, t2, t3, t4]

/-- `cls2` is monotone. -/
lemma cls2_mono {a a' b b' c c' d d' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') (h4 : d ≤ d') : cls2 a b c d ≤ cls2 a' b' c' d' := by
  have := c4_pos
  have ha' : 0 ≤ a' := ha.trans h1
  have hb' : 0 ≤ b' := hb.trans h2
  have hc' : 0 ≤ c' := hc.trans h3
  have hd' : 0 ≤ d' := hd.trans h4
  unfold cls2
  gcongr

/-- **`diffB`, `zB` at the caps**. -/
lemma BY_two_le {f₀ f₁ a W b e c : ℝ} (hq : 0 < |r|) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hf₁0 : 0 ≤ f₁) (ha : 0 ≤ a) (hW0 : 0 ≤ W) (hb0 : 0 ≤ b) (he : 0 ≤ e) (hc : 0 ≤ c)
    (hf₀ : f₀ ≤ 3 * M * cp caps.AS) (hf₁ : f₁ ≤ 41 * M * cp caps.BS)
    (hA : a ≤ cp caps.AS) (hW : W ≤ cp caps.WS) (hB : b ≤ cp caps.BS) :
    diffB D |r| f₀ f₁ W b e e c c + zB 1 |r| f₀ f₁ W a b e e c c ≤
      gBY D |r| M caps * e ^ 2 + Om M caps / |r| ^ 2 * (c * e) := by
  have hc4 := c4_pos
  have hWc := cp_nonneg caps.WS
  have hAc := cp_nonneg caps.AS
  have hBc := cp_nonneg caps.BS
  have h33 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg _
  have h34 : 0 ≤ Real.sqrt (34 * (9 + 4 / 1)) := Real.sqrt_nonneg _
  have hf₁c : 0 ≤ 41 * M * cp caps.BS := by positivity
  have s1 : f₀ * W ≤ 3 * M * cp caps.AS * cp caps.WS := mul_le_mul hf₀ hW hW0 (by positivity)
  have s2 : cls2 (c4 * f₁) W f₁ b ≤ cls2 (c4 * (41 * M * cp caps.BS)) (cp caps.WS)
      (41 * M * cp caps.BS) (cp caps.BS) :=
    cls2_mono (by positivity) hW0 hf₁0 hb0 (mul_le_mul_of_nonneg_left hf₁ hc4.le) hW hf₁ hB
  have s3 : f₁ * b ≤ (41 * M * cp caps.BS) * cp caps.BS := mul_le_mul hf₁ hB hb0 hf₁c
  have s4 : 30 * (f₁ * a) + c4 * (f₁ * W) + Real.sqrt (34 * (9 + 4 / 1)) * (f₁ * b) ≤
      30 * ((41 * M * cp caps.BS) * cp caps.AS) + c4 * ((41 * M * cp caps.BS) * cp caps.WS) +
        Real.sqrt (34 * (9 + 4 / 1)) * ((41 * M * cp caps.BS) * cp caps.BS) := by
    have t1 : f₁ * a ≤ (41 * M * cp caps.BS) * cp caps.AS := mul_le_mul hf₁ hA ha hf₁c
    have t2 : f₁ * W ≤ (41 * M * cp caps.BS) * cp caps.WS := mul_le_mul hf₁ hW hW0 hf₁c
    gcongr
  have hce : 0 ≤ c * e := by positivity
  have he2 := sq_nonneg e
  have t1 : 2 ^ 30 / |r| * (Real.sqrt 33 * (e * e * (f₀ * W))) ≤
      2 ^ 30 / |r| * (Real.sqrt 33 * (3 * M * cp caps.AS * cp caps.WS)) * e ^ 2 := by
    have := mul_le_mul_of_nonneg_left s1 (by positivity : 0 ≤ 2 ^ 30 / |r| * Real.sqrt 33 * e ^ 2)
    nlinarith only [this]
  have t2 : 2 ^ 16 / |r| * (Real.sqrt 33 * (e * e * (f₀ * W))) ≤
      2 ^ 16 / |r| * (Real.sqrt 33 * (3 * M * cp caps.AS * cp caps.WS)) * e ^ 2 := by
    have := mul_le_mul_of_nonneg_left s1 (by positivity : 0 ≤ 2 ^ 16 / |r| * Real.sqrt 33 * e ^ 2)
    nlinarith only [this]
  have t3 := mul_le_mul_of_nonneg_left s2 (by positivity : 0 ≤ 2 ^ 22 / |r| ^ 2 * (c * e))
  have t4 := mul_le_mul_of_nonneg_left s4 (by positivity : 0 ≤ 2 ^ 15 / |r| ^ 2 * (c * e))
  have t5 := mul_le_mul_of_nonneg_left s3 (by positivity : 0 ≤ 2 ^ 18 * D / |r| ^ 2 * c4 ^ 2 * e ^ 2)
  have e1 : diffB D |r| f₀ f₁ W b e e c c + zB 1 |r| f₀ f₁ W a b e e c c =
      2 ^ 30 / |r| * (Real.sqrt 33 * (e * e * (f₀ * W))) +
      2 ^ 16 / |r| * (Real.sqrt 33 * (e * e * (f₀ * W))) +
      2 ^ 22 / |r| ^ 2 * (c * e) * cls2 (c4 * f₁) W f₁ b +
      2 ^ 15 / |r| ^ 2 * (c * e) * (30 * (f₁ * a) + c4 * (f₁ * W) +
        Real.sqrt (34 * (9 + 4 / 1)) * (f₁ * b)) +
      2 ^ 18 * D / |r| ^ 2 * c4 ^ 2 * e ^ 2 * (f₁ * b) := by
    simp only [diffB, zB]
    ring
  have e2 : gBY D |r| M caps * e ^ 2 + Om M caps / |r| ^ 2 * (c * e) =
      2 ^ 30 / |r| * (Real.sqrt 33 * (3 * M * cp caps.AS * cp caps.WS)) * e ^ 2 +
      2 ^ 16 / |r| * (Real.sqrt 33 * (3 * M * cp caps.AS * cp caps.WS)) * e ^ 2 +
      2 ^ 22 / |r| ^ 2 * (c * e) * cls2 (c4 * (41 * M * cp caps.BS)) (cp caps.WS)
        (41 * M * cp caps.BS) (cp caps.BS) +
      2 ^ 15 / |r| ^ 2 * (c * e) * (30 * ((41 * M * cp caps.BS) * cp caps.AS) +
        c4 * ((41 * M * cp caps.BS) * cp caps.WS) +
        Real.sqrt (34 * (9 + 4 / 1)) * ((41 * M * cp caps.BS) * cp caps.BS)) +
      2 ^ 18 * D / |r| ^ 2 * c4 ^ 2 * e ^ 2 * ((41 * M * cp caps.BS) * cp caps.BS) := by
    simp only [gBY, Om]
    ring
  rw [e1, e2]
  linarith only [t1, t2, t3, t4, t5]

/-- **The high ancestors of the group, against the multiplier**, from the tails. -/
lemma tail_part_le {B Wc K cy : ℝ} (hq : 0 < |r|) (hD : 0 < D) (hK : 0 ≤ K) (hM : 0 ≤ M) (hcy : 0 ≤ cy)
    (hb : hnorm 2 S ≤ B) (hW : wiener S ≤ Wc) (htW : tailW D S ≤ 5 / D * B)
    (htB : tailB D S ≤ cy / D + delta0) :
    Cm2 / |r| * (hnorm 2 S * tailB D S) * (K * M) + Cm3 / |r| *
        (tailW D S * hnorm 2 S ^ 2 + wiener S * hnorm 2 S * tailB D S) ≤
      highG (Cm2 * K + 5 * Cm3) D B Wc M cy / |r| := by
  have hC2 := Cm2_pos
  have hC3 := Cm3_pos
  have hd := delta0_pos
  have hb0 := hnorm_nonneg 2 S
  have hW0 := wiener_nonneg S
  have hB0 : 0 ≤ B := hb0.trans hb
  have hWc : 0 ≤ Wc := hW0.trans hW
  have hT : 0 ≤ cy / D + delta0 := by positivity
  have s1 : hnorm 2 S * tailB D S ≤ B * (cy / D + delta0) :=
    mul_le_mul hb htB (tailB_nonneg _ _) hB0
  have s2 : tailW D S * hnorm 2 S ^ 2 ≤ 5 * (B ^ 3 / D) := by
    calc tailW D S * hnorm 2 S ^ 2 ≤ 5 / D * B * B ^ 2 :=
          mul_le_mul htW (pow_le_pow_left₀ hb0 hb 2) (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have s3 : wiener S * hnorm 2 S * tailB D S ≤ Wc * B * (cy / D + delta0) :=
    mul_le_mul (mul_le_mul hW hb hb0 hWc) htB (tailB_nonneg _ _) (by positivity)
  set Y := B * (cy / D + delta0) with hY
  have hY0 : 0 ≤ Y := by positivity
  have e : highG (Cm2 * K + 5 * Cm3) D B Wc M cy =
      (Cm2 * K + 5 * Cm3) * (B ^ 3 / D + (Wc + M) * Y) := by
    simp only [highG, hY]
    ring
  rw [e, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  have hi : 0 ≤ (|r|)⁻¹ := by positivity
  have t1 := mul_le_mul_of_nonneg_left s1 (by positivity : 0 ≤ Cm2 * (|r|)⁻¹ * (K * M))
  have s3' : wiener S * hnorm 2 S * tailB D S ≤ Wc * Y := by
    refine s3.trans (le_of_eq ?_)
    simp only [hY]
    ring
  have t2 := mul_le_mul_of_nonneg_left (add_le_add s2 s3') (by positivity : 0 ≤ Cm3 * (|r|)⁻¹)
  have hp1 : 0 ≤ (|r|)⁻¹ * Cm2 * K * (B ^ 3 / D + Wc * Y) := by positivity
  have hp2 : 0 ≤ (|r|)⁻¹ * Cm3 * (M * Y) := by positivity
  have hp3 : 0 ≤ (|r|)⁻¹ * Cm3 * (Wc * Y) := by positivity
  have hp4 : 0 ≤ (|r|)⁻¹ * Cm3 * (B ^ 3 / D) := by positivity
  nlinarith only [t1, t2, hp1, hp2, hp3, hp4]

/-- `‖N_F‖₁`, with the fast filter. -/
theorem fastNL_one_Hf {μ φ : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}
    (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty)
    (hW : wiener (Sp r g y u) ≤ cp caps.WS) (hB : hnorm 2 (Sp r g y u) ≤ cp caps.BS)
    (hY : hnorm 2 (Fp r g y u) ≤ cp caps.yF) :
    InH 1 (fastNL r g y u) ∧ hnorm 1 (fastNL r g y u) ≤
      Xic caps * hnorm 2 (Fp r g y u) + hnorm 1 (Hf r g y u) := by
  have hx := actual_adm h hu huT
  have hF : Adm 2 (Fp r g y u) := hx.PiF
  obtain ⟨i1, b1⟩ := hnorm_PiF_Qphase_le (r * u) hx
  obtain ⟨hH, -⟩ := Hf_one h hr hu huT
  have e2 : fastNL r g y u = fastQ r g y u - Hf r g y u := by
    rw [fastQ_eq]
    abel
  have e3 : fastQ r g y u = -PiF (Qphase (r * u) (actual r g y u) (actual r g y u)) := rfl
  have iQ : InH 1 (fastQ r g y u) := by
    rw [e3]
    exact i1.neg
  have hin : InH 1 (fastNL r g y u) := by
    rw [e2]
    exact iQ.sub hH.inH
  refine ⟨hin, ?_⟩
  rw [e2]
  refine (hnorm_sub_le iQ hH.inH).trans ?_
  rw [e3, hnorm_neg]
  refine add_le_add_left ?_ _
  refine b1.trans ?_
  have hw : wiener (Fp r g y u) ≤ c4 * hnorm 2 (Fp r g y u) := wiener_le hF.mz
  have hc := c4_pos
  have hd0 := hnorm_nonneg 2 (Fp r g y u)
  have hb0 := hnorm_nonneg 2 (Sp r g y u)
  have hW0 := wiener_nonneg (Sp r g y u)
  have hw0 := wiener_nonneg (Fp r g y u)
  unfold fastXi Xic
  have e0 : wiener (PiS (actual r g y u)) = wiener (Sp r g y u) := rfl
  have e1 : hnorm 2 (PiS (actual r g y u)) = hnorm 2 (Sp r g y u) := rfl
  have e4 : hnorm 2 (PiF (actual r g y u)) = hnorm 2 (Fp r g y u) := rfl
  have e5 : wiener (PiF (actual r g y u)) = wiener (Fp r g y u) := rfl
  rw [e0, e1, e4, e5]
  set d := hnorm 2 (Fp r g y u) with hd
  have s1 : wiener (Sp r g y u) * d ≤ cp caps.WS * d := mul_le_mul_of_nonneg_right hW hd0
  have s2 : hnorm 2 (Sp r g y u) * wiener (Fp r g y u) ≤ cp caps.BS * (c4 * d) :=
    mul_le_mul hB hw hw0 (cp_nonneg _)
  have s3 : wiener (Fp r g y u) * d ≤ (c4 * cp caps.yF) * d :=
    mul_le_mul_of_nonneg_right (hw.trans (mul_le_mul_of_nonneg_left (hY.trans (le_refl _)) hc.le)) hd0
  nlinarith only [s1, s2, s3]

end OVNS.Quant.Metric

end
