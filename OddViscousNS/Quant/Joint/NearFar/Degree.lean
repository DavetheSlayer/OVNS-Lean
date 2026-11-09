import OddViscousNS.Quant.Joint.NearFar.Two

/-!
# The thresholds of the near and far differentials

`qNF₁`, `qNF₂` are the thresholds N14, N15 put into `q₁`, `q₂`.  Each contains `jointSlowFloor`,
which pays role 18, `r ≠ 0` and the sizes of the filter.  With `L ≍ U`, `y ≍ (UR)^{1/2}`, `B ≍ R²`,
`W ≍ R^{3/2}`, `M ≍ R`, `P_S ≍ U R⁴`:

| term | monomial | degree `(U, R)` | ratio to `Q` |
|---|---|---:|---:|
| FAR, weight one | `N_b y ≍ B y` | `(1/2, 5/2)` | `U^{−1/2} R^{−1/2}` |
| the transform of `c_S` | `c₄ y` | `(1/2, 1/2)` | `U^{−1/2} R^{−5/2}` |
| FAR, weight two | `M y` | `(1/2, 3/2)` | `U^{−1/2} R^{−3/2}` |
| | `√P y^{3/2}` | `(5/4, 3/4)` | `U^{1/4} R^{−9/4}` |
| | `L y` | `(3/2, 1/2)` | `U^{1/2} R^{−5/2}` |
| the old partner | `L √P_S` | `(3/2, 2)` | `U^{1/2} R⁻¹` |
| near, the slow leg of the filter | `φ √P_S` | `(1/2, 3)` | `U^{−1/2}` |
| proper FAR, `q^{−1/2} y` | `y²` | `(1, 1)` | `R⁻²` |
-/

noncomputable section

namespace OVNS.Quant.NearFar

open OVNS.Quant.Metric OVNS.Quant.Quartic JDeg

variable {η CS cS : ℝ}

/-- The FAR term of weight one: `‖N_F‖₁ ≤ N_b y + 1`. -/
def tNF₁ (caps : Caps) : ℝ := nbF caps * cp caps.yF + 1

/-- **The threshold of weight one.** -/
def qNF₁ (η X R : ℝ) (caps : Caps) : ℝ :=
  max (jointSlowFloor X R caps) (2 ^ 14 / η * tNF₁ caps)

/-- The terms of weight two. -/
def tNF₂ (η CS cS X R : ℝ) (caps : Caps) : ℝ :=
  2 ^ 11 * c4 * cp caps.yF +
    2 * H2.cFar / η * (lead₂ (CS * Ex cS R * R) caps + 1 + fibL R caps * cp caps.yF) +
    4 * H2.cFar / η * ((1 + 20 * fibL R caps) * Real.sqrt (priceS CS cS X R caps)) +
    64 * c4 * (R - X) * Real.sqrt (priceS CS cS X R caps) +
    (2 * H2.cHeat2 * cp caps.yF / η) ^ 2

/-- **The threshold of weight two.** -/
def qNF₂ (η CS cS X R : ℝ) (caps : Caps) : ℝ :=
  max (jointSlowFloor X R caps) (tNF₂ η CS cS X R caps)

lemma cFar_pos : 0 < H2.cFar := by
  have hc := c4_pos
  unfold H2.cFar
  positivity

/-- `P_S ≥ 0`. -/
lemma priceS_nonneg (hC : 0 ≤ CS) (cS X : ℝ) {R : ℝ} (hR : 0 ≤ R) (caps : Caps) :
    0 ≤ priceS CS cS X R caps := by
  have hl : 0 ≤ lamI X R caps := lamI_nonneg X R caps
  have hEx := Ex_pos cS R
  simp only [priceS, slowPrice]
  positivity

/-- The five terms of `tNF₂`, one by one. -/
lemma tNF₂_parts {X R r : ℝ} {caps : Caps} (hη : 0 < η) (hCS : 0 ≤ CS) (hR : 0 < R)
    (hφ : 0 ≤ R - X) (ht : tNF₂ η CS cS X R caps ≤ |r|) :
    2 ^ 11 * c4 * cp caps.yF ≤ |r| ∧
    2 * H2.cFar / η * (lead₂ (CS * Ex cS R * R) caps + 1 + fibL R caps * cp caps.yF) ≤ |r| ∧
    4 * H2.cFar / η * ((1 + 20 * fibL R caps) * Real.sqrt (priceS CS cS X R caps)) ≤ |r| ∧
    64 * c4 * (R - X) * Real.sqrt (priceS CS cS X R caps) ≤ |r| ∧
    (2 * H2.cHeat2 * cp caps.yF / η) ^ 2 ≤ |r| := by
  have hc4 := c4_pos
  have hcF := cFar_pos
  have hy := cp_nonneg caps.yF
  have hL0 := fibL_nonneg hR caps
  have hEx := Ex_pos cS R
  have hM0 : 0 ≤ CS * Ex cS R * R := by positivity
  have hlead := lead₂_nonneg hM0 caps
  have hrt := Real.sqrt_nonneg (priceS CS cS X R caps)
  have n1 : 0 ≤ 2 ^ 11 * c4 * cp caps.yF := by positivity
  have n2 : 0 ≤ 2 * H2.cFar / η *
      (lead₂ (CS * Ex cS R * R) caps + 1 + fibL R caps * cp caps.yF) := by positivity
  have n3 : 0 ≤ 4 * H2.cFar / η *
      ((1 + 20 * fibL R caps) * Real.sqrt (priceS CS cS X R caps)) := by positivity
  have n4 : 0 ≤ 64 * c4 * (R - X) * Real.sqrt (priceS CS cS X R caps) := by positivity
  have n5 : 0 ≤ (2 * H2.cHeat2 * cp caps.yF / η) ^ 2 := by positivity
  unfold tNF₂ at ht
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem deg_nbF : JDeg 0 2 fun _ _ caps ↦ nbF caps := by
  have c4n : 0 ≤ c4 := c4_pos.le
  exact (((WS.up 0 2).add (BS.const_mul c4n)).add ((yF.const_mul c4n).up 0 2)).const_mul
    (k := 8) (by norm_num)

theorem deg_tNF₁ : JDeg (1 / 2) (5 / 2) fun _ _ caps ↦ tNF₁ caps :=
  ((deg_nbF.mul yF).up (1 / 2) (5 / 2)).add ((const zero_le_one).up (1 / 2) (5 / 2))

/-- **The threshold of weight one is below `Q`.** -/
theorem qNF₁_below (hη : 0 < η) : JointBelow fun X R caps ↦ qNF₁ η X R caps :=
  jointSlowFloor_below.sup ((deg_tNF₁.const_mul (by positivity : 0 ≤ 2 ^ 14 / η)).toQ)

theorem deg_lead₂ (hCS : 0 ≤ CS) :
    JDeg 1 3 fun _ R caps ↦ lead₂ (CS * Ex cS R * R) caps := by
  have hc1 : 0 ≤ 2 * CLow 2 := mul_nonneg (by norm_num) (CLow_nonneg 2)
  have hc2 : 0 ≤ 16 * cI := mul_nonneg (by norm_num) cI_pos.le
  have h1 := ((Minf (e := cS) hCS).mul yF).const_mul hc1
  have h2 := (PF.sqrt.mul (yF.root ((3 : ℝ) / 2))).const_mul hc2
  exact (h1.up 1 3).add (h2.up 1 3)

theorem deg_price_root (hCS : 0 ≤ CS) :
    JDeg (1 / 2) 2 fun X R caps ↦ Real.sqrt (priceS CS cS X R caps) := by
  have h := (price (e := cS) hCS).sqrt
  exact h.up (1 / 2) 2

/-- The terms of weight two, envelope. -/
theorem deg_tNF₂ (hCS : 0 ≤ CS) (hη : 0 < η) :
    JDeg 1 3 fun X R caps ↦ tNF₂ η CS cS X R caps := by
  have hc := c4_pos
  have hcF := cFar_pos
  have hcH := H2.cHeat2_pos
  have t1 := (yF.const_mul (by positivity : 0 ≤ 2 ^ 11 * c4)).up 1 3
  have t2a : JDeg 1 3 fun X R caps ↦
      lead₂ (CS * Ex cS R * R) caps + 1 + fibL R caps * cp caps.yF :=
    ((deg_lead₂ (cS := cS) hCS).add ((const zero_le_one).up 1 3)).add
      ((deg_fibL.mul yF).up 1 3)
  have t2 := t2a.const_mul (by positivity : 0 ≤ 2 * H2.cFar / η)
  have t3a : JDeg (3 / 2) 2 fun X R caps ↦
      (1 + 20 * fibL R caps) * Real.sqrt (priceS CS cS X R caps) :=
    ((((const zero_le_one).up 1 0).add (deg_fibL.const_mul (by norm_num))).mul
      (deg_price_root (cS := cS) hCS)).up (3 / 2) 2
  have t3 := (t3a.const_mul (by positivity : 0 ≤ 4 * H2.cFar / η)).up 1 3
  have t4a : JDeg (1 / 2) 3 fun X R caps ↦
      64 * c4 * (R - X) * Real.sqrt (priceS CS cS X R caps) :=
    ((phi.const_mul (by positivity : 0 ≤ 64 * c4)).mul (deg_price_root (cS := cS) hCS)).up
      (1 / 2) 3
  have t5 : JDeg 1 3 fun _ _ caps ↦ (2 * H2.cHeat2 * cp caps.yF / η) ^ 2 := by
    have h1 := (yF.const_mul (by positivity : 0 ≤ 2 * H2.cHeat2 / η)).pow 2
    refine deg_congr (h1.up 1 3) fun X R caps => ?_
    ring
  exact ((((t1.add t2).add t3).add (t4a.up 1 3)).add t5)

/-- **The threshold of weight two is below `Q`.** -/
theorem qNF₂_below (hCS : 0 ≤ CS) (hη : 0 < η) :
    JointBelow fun X R caps ↦ qNF₂ η CS cS X R caps :=
  jointSlowFloor_below.sup ((deg_tNF₂ (cS := cS) hCS hη).toQ)

end OVNS.Quant.NearFar

end
