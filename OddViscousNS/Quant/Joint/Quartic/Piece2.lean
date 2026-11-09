import OddViscousNS.Quant.Joint.Quartic.Rows
import OddViscousNS.Quant.Joint.Sources.History

/-!
# `C_{4,2}` on a joint piece (step J5, node N11)

J3-v2 §4, in the form `E2' + c_c c_F² ≤ B b c_F + g₂ b² + h₂` of `JOINT_ASSEMBLY_V4.md` §4.

`quartic_two_piece`: on a piece with the caps, `M_∞`, the slow outputs, the near share
`P(q) ≤ Q^{−1/3}`
and the threshold `(2¹⁵/η) thrTwo + flrTwo ≤ q`:
* `|C_{4,2}| ≤ η b²`;
* at a.e. time `|Rem| ≤ η c_F² + m₄ b² + A₄ c_y² + B₄`;
* `m₄/λ_* ≤ η`: the clip mass;
* `∫_clip (A₄ c_y² + B₄) ≤ η T²`: the short price, against the earlier `P_S`, "`W_*` comparable to
  `y²`", and `W_* = (297/128) T²` here.
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (ae_inH3_split)

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {X R r η CS cS R₀ : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps} {s t : ℝ}

lemma lamI_nonneg (X R : ℝ) (caps : Caps) : 0 ≤ lamI X R caps := by
  have : 0 ≤ jointLam X R caps := by
    unfold jointLam lamStar dZero
    positivity
  unfold lamI
  positivity

lemma logL_nonneg (R : ℝ) : 0 ≤ logL R := by
  unfold logL
  positivity

lemma fibL_nonneg {R : ℝ} (hR : 0 < R) (caps : Caps) : 0 ≤ fibL R caps :=
  add_nonneg (mul_nonneg (logL_nonneg R) (cp_nonneg _))
    (mul_nonneg (by positivity) (cp_nonneg _))

lemma capCp_nonneg (caps : Caps) : 0 ≤ capCp caps := by
  have := cI_pos
  unfold capCp
  positivity

lemma co2_nn (hCS : 0 ≤ CS) (hR : 0 < R) : (co2 CS cS R caps).Nn where
  L := fibL_nonneg hR caps
  y := cp_nonneg _
  B := cp_nonneg _
  W := cp_nonneg _
  D := by simp only [co2]; positivity
  Lg := logL_nonneg R
  P₀ := by
    have h1 := CLow_nonneg 2
    have h2 := Ex_pos cS R
    have h3 := capCp_nonneg caps
    simp only [co2]
    positivity
  Cp := capCp_nonneg caps
  E := by
    have := c4_pos
    simp only [co2]
    positivity
  G := by
    have := c4_pos
    simp only [co2]
    positivity
  φ := hR.le

section Coefficients

variable {c : Co} (hc : c.Nn)
include hc

lemma Co.A₁_nn : 0 ≤ c.A₁ := by
  have := hc.L
  have := hc.E
  unfold Co.A₁
  positivity

lemma Co.A₂_nn : 0 ≤ c.A₂ := by
  have := hc.L
  have := hc.E
  have := hc.D
  unfold Co.A₂
  positivity

lemma Co.A₃_nn : 0 ≤ c.A₃ := by
  have := hc.W
  have := hc.E
  unfold Co.A₃
  positivity

lemma Co.P₁_nn : 0 ≤ c.P₁ := add_nonneg hc.P₀ hc.E

lemma Co.Mm_nn : 0 ≤ c.Mm := by
  have := hc.L
  have := hc.Lg
  unfold Co.Mm
  positivity

lemma Co.Cc_nn : 0 ≤ c.Cc := by
  have h1 := hc.L
  have h2 := hc.y
  have h3 := hc.B
  have h4 := hc.Cp
  have h5 := hc.E
  have a1 := Co.A₁_nn hc
  have a2 := Co.A₂_nn hc
  have a3 := Co.A₃_nn hc
  have a4 := Co.P₁_nn hc
  unfold Co.Cc
  positivity

lemma Co.Cy_nn : 0 ≤ c.Cy := by
  have h1 := hc.L
  have h2 := hc.y
  have h3 := hc.B
  have a1 := Co.A₁_nn hc
  have a2 := Co.A₂_nn hc
  have a3 := Co.A₃_nn hc
  unfold Co.Cy
  positivity

lemma Co.Ga_nn : 0 ≤ c.Ga := by
  have h1 := hc.L
  have h2 := hc.y
  have h3 := hc.B
  have h4 := hc.G
  have h5 := hc.φ
  unfold Co.Ga
  positivity

end Coefficients

/-- `3 √𝔐_P ≤ P(q)/6`. -/
lemma three_sqrt_le {q : ℝ} (hq : 0 ≤ q) : 3 * Real.sqrt (MomP q) ≤ nearP q / 6 := by
  have h : 0 ≤ q ^ (-(3 : ℝ) / 4) := Real.rpow_nonneg hq _
  unfold nearP
  linarith

/-- **The near share**: `κ T₀ ≤ η/12` when `T₀ Q^{−1/3}` is below the threshold. -/
lemma kap2_key {Z thr T₀ : ℝ} (hr : r ≠ 0) (hη : 0 < η) (hP : nearP |r| ≤ Z) (hT₀ : 0 ≤ T₀)
    (hle : T₀ * Z ≤ thr) (hthr : 2 ^ 15 / η * thr ≤ |r|) :
    kap2 r * T₀ ≤ η / 12 := by
  have hq : 0 < |r| := abs_pos.2 hr
  have h1 := (three_sqrt_le hq.le).trans (div_le_div_of_nonneg_right hP (by norm_num))
  have h2 : kap2 r ≤ 2 ^ 14 / |r| * (Z / 6) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 2 ^ 15 / η * (T₀ * Z) ≤ |r| :=
    (mul_le_mul_of_nonneg_left hle (by positivity)).trans hthr
  have h4 : kap2 r * T₀ ≤ 2 ^ 14 / |r| * (Z / 6) * T₀ := mul_le_mul_of_nonneg_right h2 hT₀
  refine h4.trans ?_
  have e0 : 2 ^ 14 / |r| * (Z / 6) * T₀ = 2 ^ 14 * (Z / 6) * T₀ / |r| := by ring
  rw [e0, div_le_iff₀ hq]
  have e : 2 ^ 15 / η * (T₀ * Z) * (η / 12) = 2 ^ 14 * (Z / 6) * T₀ := by
    field_simp
    ring
  have := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ η / 12)
  rw [e] at this
  linarith

/-- The Young inequality of the prices. -/
lemma young_eta {x c' : ℝ} (hη : 0 < η) : 2 * x * c' ≤ η / 4 * c' ^ 2 + 4 / η * x ^ 2 := by
  have h : η / 4 * c' ^ 2 + 4 / η * x ^ 2 - 2 * x * c' = (η * c' / 2 - 2 * x) ^ 2 / η := by
    field_simp
    ring
  have h1 : 0 ≤ (η * c' / 2 - 2 * x) ^ 2 / η := by positivity
  linarith

/-- **`L_h(F) ≤ fibL`.** -/
lemma lhB_fibL {V : Field} (hV : InH 2 V) (hF : PiF V = V) (hR : 1 ≤ R)
    (ha : hnorm 1 V ≤ cp caps.PF) (hb : hnorm 2 V ≤ cp caps.yF) :
    LhB (nrm V) (fibL R caps) := by
  have h1 := lhB_log hR hV hF
  refine h1.mono ?_
  have hlog := Real.log_nonneg hR
  have hR0 : 0 < R := by linarith
  have hs : Real.sqrt (9 + 8 * Real.log R) ≤ logL R := by
    unfold logL
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith only [hlog]
  have h2 := mul_le_mul hs ha (hnorm_nonneg _ _) (logL_nonneg R)
  have h3 := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 5 / R)
  unfold fibL
  linarith

/-- The bounds of `rem_two_caps` on a piece. -/
lemma at2_of_caps {φ' : ℝ} (hr : r ≠ 0) {u cy : ℝ} (hR : 1 ≤ R) (hφ0 : 0 ≤ φ') (hφ : φ' ≤ R)
    (hq : R ^ 3 ≤ |r|) (ha : hnorm 1 (Fp r g y u) ≤ caps.PF) (hb : hnorm 2 (Fp r g y u) ≤ caps.yF)
    (hB : hnorm 2 (Sp r g y u) ≤ caps.BS) (hW : wiener (Sp r g y u) ≤ caps.WS)
    (hsup : slowSup r g y u ≤ CS * Ex cS R * R) (hV : InH 2 (Fp r g y u))
    (hF : PiF (Fp r g y u) = Fp r g y u) (hcy : 0 ≤ cy)
    (hcS : hnorm 3 (Sp r g y u) ≤ cy + hnorm 3 (Fp r g y u) / 128) :
    At2 (co2 CS cS R caps) r g y u cy (CS * Ex cS R * R) φ' := by
  have ha' := ha.trans (le_cp _)
  have hb' := hb.trans (le_cp _)
  have hc := c4_pos
  have hR0 : 0 < R := by linarith
  have hqr : 0 < |r| := abs_pos.2 hr
  have hR3 : 0 < R ^ 3 := by positivity
  refine ⟨lhB_fibL hV hF hR ha' hb', hB.trans (le_cp _), hb', hW.trans (le_cp _), hsup, ?_, le_rfl,
    ?_, ?_, hφ, ?_, ?_, hcy, hcS⟩
  · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by have := cI_pos; positivity)
    exact mul_le_mul ha' hb' (hnorm_nonneg _ _) (cp_nonneg _)
  · simp only [co2]
    rw [div_le_div_iff₀ hqr (by positivity)]
    have h0 := mul_le_mul_of_nonneg_right hφ (sq_nonneg R)
    have : φ' * R ^ 2 ≤ |r| := by nlinarith only [h0, hq]
    have h2 := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 64 * c4)
    linarith only [h2]
  · simp only [co2]
    have hr2 : 0 < r ^ 2 := by positivity
    rw [div_le_div_iff₀ hr2 (by positivity), ← sq_abs r]
    have h1 : φ' ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hφ0 hφ 2
    have h2 : (R ^ 3) ^ 2 ≤ |r| ^ 2 := pow_le_pow_left₀ hR3.le hq 2
    have h3 : φ' ^ 2 * R ^ 4 ≤ |r| ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ R ^ 4)
      nlinarith only [this, h2]
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 64 * c4)
    linarith only [h4]
  · simp only [co2]
    nlinarith only [hR]
  · simp only [co2]
    have hlog := Real.log_nonneg hR
    unfold logL
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by positivity), Real.log_pow]
    push_cast
    nlinarith only [hlog]

/-- **`C_{4,2}` on a piece** (J3-v2 §4): the static bound, the pointwise remainder, the clip mass
and the short price.  `m₄ = 2 κ Mm`, `A₄ = (4/η)(κ Cy)²`, `B₄ = (4/η)(κ Ga)²`. -/
theorem quartic_two_piece {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} (hdom : JDom R₀ X R)
    (h : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) (hon : OnPrefix caps r g y s t)
    (hsup : ∀ u ∈ Set.Icc s t, slowSup r g y u ≤ CS * Ex cS R * R) (hCS : 0 ≤ CS)
    (hO : SlowOut CS (Ex cS R) R Sl r g y s t) (hη : 0 < η)
    (hthr : 2 ^ 15 / η * thrTwo CS cS X R caps + flrTwo R caps ≤ |r|)
    (hP : nearP |r| ≤ zq X R) :
    ∃ m₄ A₄ B₄ : ℝ, 0 ≤ m₄ ∧ 0 ≤ A₄ ∧ 0 ≤ B₄ ∧
      (∀ u ∈ Set.Icc s t, |C4 2 r g y u| ≤ η * fastNorm 2 r g y u ^ 2) ∧
      (∀ᵐ u ∂(volume.restrict (Set.Icc s t)), |Rem4 2 r g y u| ≤
        η * fastNorm 3 r g y u ^ 2 + m₄ * fastNorm 2 r g y u ^ 2 +
          (A₄ * hnorm 3 (corrSlow r g y u) ^ 2 + B₄)) ∧
      m₄ * lamI X R caps ≤ η ∧
      ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ lamI X R caps →
        (∫ u in u₁..u₂, (A₄ * hnorm 3 (corrSlow r g y u) ^ 2 + B₄)) ≤ η * jointT X R ^ 2 := by
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  have hU0 : 0 < jointU X := by linarith [hdom.one_lt_U]
  have hc4 := c4_pos
  set c := co2 CS cS R caps with hcd
  have hc : c.Nn := co2_nn hCS hR0
  set K := kap2 r with hK
  have hK0 : 0 ≤ K := kap2_nonneg r
  set Z := zq X R with hZd
  have hZ : 0 ≤ Z := by
    have := Real.rpow_nonneg hdom.Q_pos.le ((1 : ℝ) / 3)
    simp only [hZd, zq]
    positivity
  set Λ := lamI X R caps with hΛd
  have hΛ : 0 ≤ Λ := lamI_nonneg X R caps
  set PS := priceS CS cS X R caps with hPS
  have hEx := Ex_pos cS R
  have hPS0 : 0 ≤ PS := by
    simp only [hPS, priceS, slowPrice]
    positivity
  set uI := uInv X R with huI
  have huI0 : 0 ≤ uI := mul_nonneg (Real.rpow_nonneg hU0.le _) (Real.rpow_nonneg hR0.le _)
  have huI1 : uI * jointT X R ^ 2 = 1 := by
    rw [hdom.T_sq, huI, uInv, Real.rpow_neg_one, Real.rpow_neg_one]
    field_simp
  have hMm := Co.Mm_nn hc
  have hCc := Co.Cc_nn hc
  have hCy := Co.Cy_nn hc
  have hGa := Co.Ga_nn hc
  have hBL : 0 ≤ c.B * c.L := mul_nonneg hc.B hc.L
  -- the terms of the threshold
  have n1 : 0 ≤ tS CS cS X R caps := mul_nonneg hBL hZ
  have n2 : 0 ≤ tM CS cS X R caps := mul_nonneg (mul_nonneg hMm hΛ) hZ
  have n3 : 0 ≤ tC CS cS X R caps := mul_nonneg hCc hZ
  have n4 : 0 ≤ tY CS cS X R caps := mul_nonneg (Real.sqrt_nonneg _) hZ
  have n5 : 0 ≤ tG CS cS X R caps := mul_nonneg (Real.sqrt_nonneg _) hZ
  set thr := thrTwo CS cS X R caps with hthrd
  have hthr0 : 0 ≤ thr := by
    simp only [hthrd, thrTwo]
    positivity
  have hfl0 : 0 ≤ cp caps.yF := cp_nonneg _
  have hA0 : 0 ≤ 2 ^ 15 / η * thr := by positivity
  have hq3 : R ^ 3 ≤ |r| := by
    have : 0 ≤ 2 ^ 11 * c4 * cp caps.yF := by positivity
    simp only [flrTwo] at hthr
    linarith
  have hq11 : 2 ^ 11 * c4 * cp caps.yF ≤ |r| := by
    have : 0 ≤ R ^ 3 := by positivity
    simp only [flrTwo] at hthr
    linarith
  have hthr' : 2 ^ 15 / η * thr ≤ |r| := by
    have : 0 ≤ flrTwo R caps := by
      unfold flrTwo
      positivity
    linarith
  have hk : ∀ T₀ : ℝ, 0 ≤ T₀ → T₀ * Z ≤ thr → K * T₀ ≤ η / 12 := fun T₀ h0 h1 =>
    kap2_key hr hη hP h0 h1 hthr'
  have ks : K * (c.B * c.L) ≤ η / 12 := hk _ hBL (by
    have : c.B * c.L * Z = tS CS cS X R caps := rfl
    rw [this, hthrd, thrTwo]
    linarith)
  have km : K * (c.Mm * Λ) ≤ η / 12 := hk _ (mul_nonneg hMm hΛ) (by
    have : c.Mm * Λ * Z = tM CS cS X R caps := rfl
    rw [this, hthrd, thrTwo]
    linarith)
  have kc : K * c.Cc ≤ η / 12 := hk _ hCc (by
    have : c.Cc * Z = tC CS cS X R caps := rfl
    rw [this, hthrd, thrTwo]
    linarith)
  have ky : K * Real.sqrt (c.Cy ^ 2 * PS * uI) ≤ η / 12 := hk _ (Real.sqrt_nonneg _) (by
    have : Real.sqrt (c.Cy ^ 2 * PS * uI) * Z = tY CS cS X R caps := rfl
    rw [this, hthrd, thrTwo]
    linarith)
  have kg : K * Real.sqrt (c.Ga ^ 2 * Λ * uI) ≤ η / 12 := hk _ (Real.sqrt_nonneg _) (by
    have : Real.sqrt (c.Ga ^ 2 * Λ * uI) * Z = tG CS cS X R caps := rfl
    rw [this, hthrd, thrTwo]
    linarith)
  have hφ0 : 0 ≤ R - X := (hnorm_nonneg 2 g).trans h.force_le
  have hφR : R - X ≤ R := by linarith [hdom.one_lt_X]
  have hmem : ∀ u ∈ Set.Icc s t, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hs.trans hu.1, lt_lifespan hu.2 ht⟩
  have hcaps := hon.1
  refine ⟨2 * (K * c.Mm), 4 / η * (K * c.Cy) ^ 2, 4 / η * (K * c.Ga) ^ 2, by positivity,
    by positivity, by positivity, fun u hu => ?_, ?_, ?_, ?_⟩
  · -- the static bound
    obtain ⟨hu0, huT⟩ := hmem u hu
    obtain ⟨c1, c2, -, c4', -⟩ := hcaps u hu
    have hF := Fp_adm h hu0 huT
    have hL := lhB_fibL (R := R) (caps := caps) hF.inH (PiF_Fp r g y u) hR1 (c1.trans (le_cp _))
      (c2.trans (le_cp _))
    have hv := val_two_le hr h hu0 huT hL
    have hb0 := hnorm_nonneg 2 (Fp r g y u)
    have h1 : |C4 2 r g y u| ≤ 2 * ‖val4 2 r g y u‖ := by
      simp only [C4, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    have h2 : hnorm 2 (Sp r g y u) * fibL R caps * hnorm 2 (Fp r g y u) ^ 2 ≤
        c.B * c.L * hnorm 2 (Fp r g y u) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (c4'.trans (le_cp _)) hc.L)
        (sq_nonneg _)
    have h3 := mul_le_mul_of_nonneg_left h2 hK0
    have h4 := mul_le_mul_of_nonneg_right ks (sq_nonneg (hnorm 2 (Fp r g y u)))
    have e : fastNorm 2 r g y u = hnorm 2 (Fp r g y u) := rfl
    rw [e]
    have h5 : 0 ≤ η * hnorm 2 (Fp r g y u) ^ 2 := by positivity
    nlinarith only [h1, hv, h3, h4, h5]
  · -- the remainder at the `H³` times
    filter_upwards [ae_inH3_split h hs hst ht, ae_inH3_corr h hr hs hst ht,
      ae_restrict_mem measurableSet_Icc] with u hu3 huz hu
    obtain ⟨hu0, huT⟩ := hmem u hu
    obtain ⟨c1, c2, -, c4', c5⟩ := hcaps u hu
    have hF := Fp_adm h hu0 huT
    have hcS : slowNorm 3 r g y u ≤ hnorm 3 (corrSlow r g y u) + fastNorm 3 r g y u / 128 :=
      slow_three_le h hr hu0 huT hu3.1 huz (c2.trans (le_cp _)) hq11
    have hA := at2_of_caps (CS := CS) (cS := cS) (caps := caps) hr hR1 hφ0 hφR hq3 c1 c2 c4' c5
      (hsup u hu) hF.inH (PiF_Fp r g y u) (hnorm_nonneg 3 (corrSlow r g y u)) hcS
    have hb := rem_two_caps hr h hu0 huT hu3.1 hu3.2 hc hA
    set b := hnorm 2 (Fp r g y u) with hbd
    set cF := hnorm 3 (Fp r g y u) with hcFd
    set cy := hnorm 3 (corrSlow r g y u) with hcyd
    have h1 : |Rem4 2 r g y u| ≤ 2 * ‖rem4 2 r g y u‖ := by
      simp only [Rem4, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    have y1 := young_eta (η := η) (x := K * c.Cy * cy) (c' := cF) hη
    have y2 := young_eta (η := η) (x := K * c.Ga) (c' := cF) hη
    have h2 : 2 * (K * c.Cc) * cF ^ 2 ≤ 2 * (η / 12) * cF ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left kc (by norm_num)) (sq_nonneg _)
    have e1 : fastNorm 3 r g y u = cF := rfl
    have e2 : fastNorm 2 r g y u = b := rfl
    rw [e1, e2]
    have h3 : 0 ≤ η * cF ^ 2 := by positivity
    have e3 : 4 / η * (K * c.Cy) ^ 2 * cy ^ 2 = 4 / η * (K * c.Cy * cy) ^ 2 := by ring
    rw [e3]
    nlinarith only [h1, hb, y1, y2, h2, h3]
  · -- the clip mass
    have e : 2 * (K * c.Mm) * Λ = 2 * (K * (c.Mm * Λ)) := by ring
    rw [e]
    linarith
  · -- the short price
    intro u₁ u₂ h1 h12 h2 hlen
    have hC : 0 ≤ CS * Ex cS R := by positivity
    have hclip := slowOut_clip_le hO hC hR1 h1 h12 h2 hlen
    have hsub : Set.uIcc u₁ u₂ ⊆ Set.uIcc s t := by
      rw [Set.uIcc_of_le h12, Set.uIcc_of_le hst]
      exact Set.Icc_subset_Icc h1 h2
    have hi : IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume u₁ u₂ :=
      hO.cy_int.mono_set hsub
    set A₄ := 4 / η * (K * c.Cy) ^ 2 with hA₄
    set B₄ := 4 / η * (K * c.Ga) ^ 2 with hB₄
    have hA₄0 : 0 ≤ A₄ := by positivity
    have hB₄0 : 0 ≤ B₄ := by positivity
    rw [intervalIntegral.integral_add (hi.const_mul A₄) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    have t1 : A₄ * ∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2 ≤ A₄ * (4 * PS) :=
      mul_le_mul_of_nonneg_left hclip hA₄0
    have t2 : (u₂ - u₁) * B₄ ≤ Λ * B₄ := mul_le_mul_of_nonneg_right hlen hB₄0
    have hT2 : 0 ≤ jointT X R ^ 2 := by positivity
    have s1 : (K * c.Cy) ^ 2 * PS ≤ (η / 12) ^ 2 * jointT X R ^ 2 := by
      have h3 : 0 ≤ K * Real.sqrt (c.Cy ^ 2 * PS * uI) := by positivity
      have h4 := pow_le_pow_left₀ h3 ky 2
      rw [mul_pow, Real.sq_sqrt (by positivity)] at h4
      have h5 := mul_le_mul_of_nonneg_right h4 hT2
      have e : K ^ 2 * (c.Cy ^ 2 * PS * uI) * jointT X R ^ 2 = (K * c.Cy) ^ 2 * PS *
          (uI * jointT X R ^ 2) := by ring
      rw [e, huI1, mul_one] at h5
      exact h5
    have s2 : (K * c.Ga) ^ 2 * Λ ≤ (η / 12) ^ 2 * jointT X R ^ 2 := by
      have h3 : 0 ≤ K * Real.sqrt (c.Ga ^ 2 * Λ * uI) := by positivity
      have h4 := pow_le_pow_left₀ h3 kg 2
      rw [mul_pow, Real.sq_sqrt (by positivity)] at h4
      have h5 := mul_le_mul_of_nonneg_right h4 hT2
      have e : K ^ 2 * (c.Ga ^ 2 * Λ * uI) * jointT X R ^ 2 = (K * c.Ga) ^ 2 * Λ *
          (uI * jointT X R ^ 2) := by ring
      rw [e, huI1, mul_one] at h5
      exact h5
    have s3 : A₄ * (4 * PS) ≤ 16 / η * ((η / 12) ^ 2 * jointT X R ^ 2) := by
      have := mul_le_mul_of_nonneg_left s1 (by positivity : 0 ≤ 16 / η)
      calc A₄ * (4 * PS) = 16 / η * ((K * c.Cy) ^ 2 * PS) := by
            simp only [hA₄]
            ring
        _ ≤ _ := this
    have s4 : Λ * B₄ ≤ 4 / η * ((η / 12) ^ 2 * jointT X R ^ 2) := by
      have := mul_le_mul_of_nonneg_left s2 (by positivity : 0 ≤ 4 / η)
      calc Λ * B₄ = 4 / η * ((K * c.Ga) ^ 2 * Λ) := by
            simp only [hB₄]
            ring
        _ ≤ _ := this
    have e5 : 16 / η * ((η / 12) ^ 2 * jointT X R ^ 2) + 4 / η * ((η / 12) ^ 2 * jointT X R ^ 2) =
        5 / 36 * (η * jointT X R ^ 2) := by
      field_simp
      ring
    have h6 : 0 ≤ η * jointT X R ^ 2 := by positivity
    linarith

end OVNS.Quant.Quartic

end
