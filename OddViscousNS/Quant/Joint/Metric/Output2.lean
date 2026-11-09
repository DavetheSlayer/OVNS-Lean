import OddViscousNS.Quant.Joint.Metric.Energy2

/-!
# The output of the second energy (node N15)

`h2_output`: on a joint piece where `Thr2` and the guard hold, `H2Output` holds, with the energy
`W = En2`, a multiplier `G = (64/31)(…)` and a residual `H`.  `JOINT_ASSEMBLY_V4.md` §4.

The clip budget of the residual: `∫ H ≤ 2 (32 · 2⁻¹² + η T²)`, against `W_*/32 = (297/4096) T²`, where
`W_* = (33/32)(3 T/2)²`, and `T ≥ 1`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic OVNS.Quant.NearFar
open OVNS.Quant.H2 (fast_h2_law)
open GN (SupBd)

variable {X R CS cS KN KP R₀ r CH : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps}
  {s t : ℝ} {q : Caps → ℝ} {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop}

lemma Gm_nonneg {φ D q M : ℝ} (hφ : 0 ≤ φ) (hD : 1 ≤ D) (hq : 1 ≤ q) (hM : 0 ≤ M) (caps : Caps) :
    0 ≤ Gm φ D q M caps := by
  have hq0 : 0 < q := by linarith
  have hD0 : 0 < D := by linarith
  have hlog := Real.log_nonneg hD
  have hlq := Real.log_nonneg hq
  have hc := c4_pos
  have hA := cp_nonneg caps.AS
  have hB := cp_nonneg caps.BS
  have hW := cp_nonneg caps.WS
  have hY := cp_nonneg caps.yF
  have hC1 := CLow_nonneg 1
  have hZ := CZh_pos
  have hT := T0_nonneg D
  have hS := hSrc_nonneg hφ caps
  have hK := Kc_nonneg caps
  have hZs : 0 ≤ Zs D := by unfold Zs; positivity
  have hcls : 0 ≤ cls2 (cp caps.WS) (cp caps.WS) (cp caps.BS) (cp caps.BS) := by
    unfold cls2
    positivity
  have h1 : 0 ≤ gLow D q M caps := by
    unfold gLow Xcap
    positivity
  have h2 : 0 ≤ gSep D q caps := by
    unfold gSep
    positivity
  have h3 : 0 ≤ gHt D q caps := by
    unfold gHt
    positivity
  have h4 : 0 ≤ gBY D q M caps := by
    unfold gBY
    positivity
  have h5 : 0 ≤ Xic caps := by
    unfold Xic
    positivity
  have h6 : 0 ≤ gSlot φ D q caps := by
    unfold gSlot
    positivity
  unfold Gm
  positivity

lemma kapY_nonneg (q : ℝ) (caps : Caps) : 0 ≤ kapY q caps := by
  have := cp_nonneg caps.BS
  have := cp_nonneg caps.WS
  unfold kapY
  positivity

lemma highG_nonneg {Ch D B Wc M cy : ℝ} (hCh : 0 ≤ Ch) (hD : 0 < D) (hB : 0 ≤ B) (hW : 0 ≤ Wc)
    (hM : 0 ≤ M) (hcy : 0 ≤ cy) : 0 ≤ highG Ch D B Wc M cy := by
  have := delta0_pos
  unfold highG
  positivity

lemma Chigh_nonneg {K : ℝ} (hK : 0 ≤ K) : 0 ≤ Chigh K := by
  have := Cm3_pos
  have := Cm2_pos
  unfold Chigh
  positivity

lemma x2_nonneg {φ R M : ℝ} (hφ : 0 ≤ φ) (hR : 1 ≤ R) (hr : 1 ≤ |r|) (hM : 0 ≤ M) (caps : Caps)
    (g : Field) (y : ℝ → Field) (u : ℝ) : 0 ≤ x2 φ R M r g y caps u := by
  have hD : 1 ≤ jointD R := by
    unfold jointD
    nlinarith only [hR]
  have hq0 : 0 < |r| := by linarith
  have h1 := Gm_nonneg hφ hD hr hM caps
  have h2 := kapY_nonneg |r| caps
  have h3 := highG_nonneg (Chigh_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (CLow_nonneg 1)))
    (by linarith : 0 < jointD R) (cp_nonneg caps.BS) (cp_nonneg caps.WS) hM
    (hnorm_nonneg 3 (corrSlow r g y u))
  have h4 := hnorm_nonneg 3 (corrSlow r g y u)
  unfold x2
  positivity

/-- The high ancestors at the caps, as a function of `c_y`: an affine function. -/
lemma highG_integrable {Ch D B Wc M : ℝ} {c : ℝ → ℝ} {a b : ℝ}
    (hc : IntervalIntegrable c volume a b) :
    IntervalIntegrable (fun u => highG Ch D B Wc M (c u) / |r|) volume a b := by
  have h1 : IntervalIntegrable (fun u => (Ch * (B ^ 3 / D + (Wc + M) * B * delta0) +
      Ch * (Wc + M) * B / D * c u) / |r|) volume a b :=
    (intervalIntegrable_const.add (hc.const_mul _)).div_const _
  refine h1.congr fun u _ => ?_
  simp only [highG]
  ring

/-- `c_y` is integrable. -/
lemma cy_integrable {a b : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume a b) :
    IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u)) volume a b :=
  (clip_cauchy (P := ∫ u in a..b, hnorm 3 (corrSlow r g y u) ^ 2) hab
    (fun _ => hnorm_nonneg _ _) hi le_rfl).1

/-- `x2` is integrable. -/
lemma x2_integrable {μ φ R M : ℝ} (h : ActualSol μ φ r g y Ty) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : ENNReal.ofReal b < Ty)
    (hy : IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume a b) :
    IntervalIntegrable (x2 φ R M r g y caps) volume a b := by
  have ht0 := ha.trans hab
  have hsub : uIcc a b ⊆ Icc 0 b := by
    rw [uIcc_of_le hab]
    exact Icc_subset_Icc_left ha
  have c1 := (h0Bd_cont h ht0 hb).mono hsub
  have i1 : IntervalIntegrable (fun u => (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 /
      (4 * (1 / 64))) volume a b :=
    (((continuousOn_const.mul c1).div_const _).pow 2 |>.div_const _).intervalIntegrable
  have hc := cy_integrable hab hy
  have i2 := hc.const_mul (kapY |r| caps)
  have i3 := highG_integrable (r := r) (Ch := Chigh (2 * CLow 1)) (D := jointD R) (B := cp caps.BS)
    (Wc := cp caps.WS) (M := M) hc
  have i4 : IntervalIntegrable (fun _ : ℝ => Gm φ (jointD R) |r| M caps) volume a b :=
    intervalIntegrable_const
  exact i1.add ((i4.add i2).add i3)

/-- **The output of the second energy.** -/
theorem h2_output (hres : ResH2 ((281 : ℝ) / 1000) CH) (hdom : JDom R₀ X R) (hCS : 0 ≤ CS)
    (hKN : kN / eta2 ≤ KN) (hKP : kP / eta2 ≤ KP)
    (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece 4 (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t) (hT : Thr2 X R CS cS r caps)
    (hG : ∀ u ∈ Icc s t, CH * fastNorm ((281 : ℝ) / 1000) r g y u ≤ jointBs X R caps)
    (hrow : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      u₂ - u₁ ≤ 1 / lamStar 1 caps.PF (jointBs X R caps) →
      ∫ u in u₁..u₂, highG (Chigh (2 * CLow 1)) (jointD R) (cp caps.BS) (cp caps.WS)
        (CS * Ex cS R * R) (hnorm 3 (corrSlow r g y u)) / |r| ≤ 1 / 2 ^ 35) :
    H2Output caps.PF (jointBs X R caps) (1 / 4) r g y s t := by
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  have hfl : jointSlowFloor X R caps ≤ |r| :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hT.q)
  obtain ⟨-, hφ, -, hr1, hr⟩ := floor_setup hdom hfl
  set φ := R - X with hφd
  set M := CS * Ex cS R * R with hMd
  set Bs := jointBs X R caps with hBs
  have hq0 : 0 < |r| := by linarith
  have hEx := Ex_pos cS R
  have hM0 : 0 ≤ M := by positivity
  have hCex : 0 ≤ CS * Ex cS R := by positivity
  have hO : SlowOut CS (Ex cS R) R Sl r g y s t := hp.slow
  have hD : 1 ≤ jointD R := by
    unfold jointD
    nlinarith only [hR1]
  have hp' : JointPiece 4 M (fun _ => |r|)
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t :=
    { hp with thr := le_rfl }
  obtain ⟨m, A, B, g₃, hm, hA, hB, hg, hae, hclip⟩ := T2_ae hres hdom hCS hKN hKP h hp hT hG
  obtain ⟨iGF, hGF, -⟩ := force2_joint h hp' hCex hR0.le hD hT.f2
  have ht0 : 0 ≤ t := hp.hs.trans hp.hst
  have hcy : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume u₁ u₂ :=
    fun u₁ u₂ h1 h2 h3 => hO.cy_int.mono_set (by
      rw [uIcc_of_le h2, uIcc_of_le hp.hst]
      exact Icc_subset_Icc h1 h3)
  set Y := fun u => hnorm 3 (corrSlow r g y u) ^ 2 with hY
  set Xf := fun u => (m + g₃ * Y u) + x2 φ R M r g y caps u with hXf
  set Yf := fun u => 32 * GF φ (jointD R) M r g y caps u + (A * Y u + B) with hYf
  have hXf0 : ∀ u, 0 ≤ Xf u := fun u => by
    have h1 := x2_nonneg hφ hR1 hr1 hM0 caps g y u
    have h2 : 0 ≤ Y u := sq_nonneg _
    simp only [hXf]
    positivity
  have hYf0 : ∀ u, 0 ≤ Yf u := fun u => by
    have h1 := GF_nonneg φ (jointD R) M r g y caps u
    have h2 : 0 ≤ Y u := sq_nonneg _
    simp only [hYf]
    positivity
  have iXf : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → IntervalIntegrable Xf volume u₁ u₂ :=
    fun u₁ u₂ h1 h2 h3 => by
      have h0 : IntervalIntegrable (fun u => m + g₃ * Y u) volume u₁ u₂ :=
        intervalIntegrable_const.add ((hcy u₁ u₂ h1 h2 h3).const_mul _)
      exact h0.add (x2_integrable h (hp.hs.trans h1) h2 (lt_lifespan h3 hp.ht) (hcy u₁ u₂ h1 h2 h3))
  have iYf : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → IntervalIntegrable Yf volume u₁ u₂ :=
    fun u₁ u₂ h1 h2 h3 => by
      have h0 : IntervalIntegrable (fun u => A * Y u + B) volume u₁ u₂ :=
        ((hcy u₁ u₂ h1 h2 h3).const_mul _).add intervalIntegrable_const
      have h4 : IntervalIntegrable (GF φ (jointD R) M r g y caps) volume u₁ u₂ :=
        iGF.mono_set (by
          rw [uIcc_of_le h2, uIcc_of_le hp.hst]
          exact Icc_subset_Icc h1 h3)
      exact (h4.const_mul 32).add h0
  have hcoe := fun u (hu : u ∈ Icc s t) =>
    En2_coercive (D := jointD R) hdom hCS hKN hKP h hp hT hu
  refine ⟨En2 (jointD R) r g y, fun u => 64 / 31 * Xf u, fun u => 2 * Yf u, hcoe,
    (fast_h2_law h hp.hs hp.hst hp.ht).1, ?_, ?_, ?_, ?_, ?_⟩
  · -- the integrated inequality
    intro u₁ u₂ h1 h12 h2
    have hu₁ : 0 ≤ u₁ := hp.hs.trans h1
    have hu₂ : ENNReal.ofReal u₂ < Ty := lt_lifespan h2 hp.ht
    obtain ⟨hI, hid⟩ := En2_identity h hr (jointD R) hu₁ h12 hu₂
    have hc2 := (fast_h2_law h hu₁ h12 hu₂).1
    have hc1 : IntervalIntegrable (fastNorm 3 r g y) volume u₁ u₂ :=
      (clip_cauchy (P := ∫ u in u₁..u₂, fastNorm 3 r g y u ^ 2) h12 (fun _ => hnorm_nonneg _ _) hc2
        le_rfl).1
    have hsub : uIcc u₁ u₂ ⊆ Icc 0 u₂ := by
      rw [uIcc_of_le h12]
      exact Icc_subset_Icc_left hu₁
    have hb : ContinuousOn (fastNorm 2 r g y) (uIcc u₁ u₂) :=
      (norms_continuous h (hu₁.trans h12) hu₂).2.1.mono hsub
    have hW : ContinuousOn (En2 (jointD R) r g y) (uIcc u₁ u₂) := by
      rw [uIcc_of_le h12]
      exact En2_continuousOn h hr hu₁ h12 hu₂
    have i1 : IntervalIntegrable (fun u => 2 * Bs * fastNorm 2 r g y u * fastNorm 3 r g y u)
        volume u₁ u₂ := by
      have := (hc1.continuousOn_mul hb).const_mul (2 * Bs)
      refine this.congr fun u _ => ?_
      ring
    have i2 : IntervalIntegrable (fun u => 64 / 31 * Xf u * En2 (jointD R) r g y u) volume u₁ u₂ :=
      ((iXf u₁ u₂ h1 h12 h2).const_mul (64 / 31)).mul_continuousOn hW
    have i3 : IntervalIntegrable (fun u => 2 * Yf u) volume u₁ u₂ :=
      (iYf u₁ u₂ h1 h12 h2).const_mul 2
    have iF : IntervalIntegrable (fun u => -2 * dZero * fastNorm 3 r g y u ^ 2 +
        2 * Bs * fastNorm 2 r g y u * fastNorm 3 r g y u +
        64 / 31 * Xf u * En2 (jointD R) r g y u + 2 * Yf u) volume u₁ u₂ :=
      ((((hc2.const_mul (-2 * dZero))).add i1).add i2).add i3
    have hmono := intervalIntegral.integral_mono_ae_restrict h12 hI
      ((iF.const_mul (1 / 2)).add hc2) (by
        have hae' := ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc h1 h2) hae
        filter_upwards [hae', ae_restrict_mem measurableSet_Icc] with u hu hm'
        have hmem : u ∈ Icc s t := ⟨h1.trans hm'.1, hm'.2.trans h2⟩
        obtain ⟨c1, -⟩ := hcoe u hmem
        have hX := hXf0 u
        have h3 := mul_le_mul_of_nonneg_left c1 hX
        have e : dZero = 2 / 3 := rfl
        simp only [e]
        refine hu.trans ?_
        change _ ≤ 1 / 2 * (-2 * (2 / 3) * fastNorm 3 r g y u ^ 2 +
          2 * Bs * fastNorm 2 r g y u * fastNorm 3 r g y u +
          64 / 31 * Xf u * En2 (jointD R) r g y u + 2 * Yf u) + fastNorm 3 r g y u ^ 2
        have e2 : (m + g₃ * hnorm 3 (corrSlow r g y u) ^ 2 + x2 φ R M r g y caps u) = Xf u := rfl
        have e3 : 32 * GF φ (jointD R) M r g y caps u + (A * hnorm 3 (corrSlow r g y u) ^ 2 + B) =
            Yf u := rfl
        rw [e2, e3]
        nlinarith only [h3])
    rw [intervalIntegral.integral_add (iF.const_mul (1 / 2)) hc2,
      intervalIntegral.integral_const_mul] at hmono
    linarith only [hmono, hid]
  · intro u _
    exact ⟨mul_nonneg (by norm_num) (hXf0 u), mul_nonneg (by norm_num) (hYf0 u)⟩
  · exact (iXf s t le_rfl hp.hst le_rfl).const_mul _
  · exact (iYf s t le_rfl hp.hst le_rfl).const_mul _
  · intro u₁ u₂ h1 h12 h2 hl
    have hl' : u₂ - u₁ ≤ lamI X R caps := hl
    have hu₁ : 0 ≤ u₁ := hp.hs.trans h1
    have hu₂ : ENNReal.ofReal u₂ < Ty := lt_lifespan h2 hp.ht
    obtain ⟨c1, c2⟩ := hclip u₁ u₂ h1 h12 h2 hl'
    have hy := hcy u₁ u₂ h1 h12 h2
    have hsub : uIcc u₁ u₂ ⊆ Icc 0 u₂ := by
      rw [uIcc_of_le h12]
      exact Icc_subset_Icc_left hu₁
    -- the pieces of `x2`
    have i0 : IntervalIntegrable (fun u => m + g₃ * Y u) volume u₁ u₂ :=
      intervalIntegrable_const.add (hy.const_mul _)
    have i1 : IntervalIntegrable (fun u => (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 /
        (4 * (1 / 64))) volume u₁ u₂ :=
      (((continuousOn_const.mul ((h0Bd_cont h (hu₁.trans h12) hu₂).mono hsub)).div_const _).pow 2
        |>.div_const _).intervalIntegrable
    have icy := cy_integrable h12 hy
    have i2 : IntervalIntegrable (fun _ : ℝ => Gm φ (jointD R) |r| M caps) volume u₁ u₂ :=
      intervalIntegrable_const
    have i3 := icy.const_mul (kapY |r| caps)
    have i4 := highG_integrable (r := r) (Ch := Chigh (2 * CLow 1)) (D := jointD R)
      (B := cp caps.BS) (Wc := cp caps.WS) (M := M) icy
    have eX : ∫ u in u₁..u₂, Xf u = (∫ u in u₁..u₂, (m + g₃ * Y u)) +
        ((∫ u in u₁..u₂, (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * (1 / 64))) +
          ((u₂ - u₁) * Gm φ (jointD R) |r| M caps +
            kapY |r| caps * (∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u)) +
            ∫ u in u₁..u₂, highG (Chigh (2 * CLow 1)) (jointD R) (cp caps.BS) (cp caps.WS) M
              (hnorm 3 (corrSlow r g y u)) / |r|)) := by
      simp only [hXf, x2]
      rw [intervalIntegral.integral_add i0 (i1.add ((i2.add i3).add i4)),
        intervalIntegral.integral_add i1 ((i2.add i3).add i4),
        intervalIntegral.integral_add (i2.add i3) i4, intervalIntegral.integral_add i2 i3,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
    have hm0 := h0_mass_clip (ζ := 1 / 64) h hp.hs hp.hst hp.ht hp.len hp.onPrefix hR0.le hM0 hT.f1
      (by norm_num) h1 h12 h2
    have hYm : (Ch0 * kapH0 caps * H0c φ caps / |r|) ^ 2 / (4 * (1 / 64)) ≤ 1 / 64 := by
      have hf0 : 0 ≤ Ch0 * kapH0 caps * H0c φ caps := by
        have := Ch0_pos
        have := kapH0_pos caps
        have := H0c_nonneg hφ caps
        positivity
      have h3 : Ch0 * kapH0 caps * H0c φ caps / |r| ≤ 1 / 2 ^ 5 := by
        rw [div_le_iff₀ hq0]
        have : 2 ^ 5 * force0Y φ caps ≤ |r| := hT.h0
        unfold force0Y at this
        linarith only [this]
      have h4 := pow_le_pow_left₀ (div_nonneg hf0 hq0.le) h3 2
      norm_num at h4 ⊢
      linarith only [h4]
    have hGm0 := Gm_nonneg hφ hD hr1 hM0 caps
    have hk0 := kapY_nonneg |r| caps
    have s1 : (u₂ - u₁) * Gm φ (jointD R) |r| M caps ≤
        lamI X R caps * Gm φ (jointD R) |r| M caps := mul_le_mul_of_nonneg_right hl' hGm0
    set P₀ := 4 * slowPrice CS (Ex cS R) R (lamI X R caps) with hP₀
    have hyP : ∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2 ≤ P₀ :=
      slowOut_clip_le hO hCex hR1 h1 h12 h2 hl'
    have hL0 : 0 ≤ lamI X R caps := (sub_nonneg.2 h12).trans hl'
    have hP0 : 0 ≤ P₀ := by
      simp only [hP₀, slowPrice]
      positivity
    have s2 : ∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ≤ Real.sqrt (lamI X R caps * P₀) := by
      refine (clip_cauchy h12 (fun _ => hnorm_nonneg _ _) hy hyP).2.trans ?_
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hl' hP0)
    have s3 := mul_le_mul_of_nonneg_left s2 hk0
    have s4 := hrow u₁ u₂ h1 h12 h2 hl
    have hclipT : Gm φ (jointD R) |r| M caps * lamI X R caps +
        kapY |r| caps * Real.sqrt (lamI X R caps * P₀) ≤ 1 / 2 ^ 6 := hT.clip
    have hXm : ∫ u in u₁..u₂, Xf u ≤ 1 / 28 := by
      rw [eX]
      have e4 : 4 * eta2 = 1 / 2 ^ 9 := by norm_num [eta2]
      rw [e4] at c1
      have e5 : (∫ u in u₁..u₂, highG (Chigh (2 * CLow 1)) (jointD R) (cp caps.BS) (cp caps.WS) M
          (hnorm 3 (corrSlow r g y u)) / |r|) ≤ 1 / 2 ^ 35 := s4
      have n1 : (1 : ℝ) / 2 ^ 9 + 1 / 64 + 1 / 2 ^ 6 + 1 / 2 ^ 35 ≤ 1 / 28 := by norm_num
      have s5 := mul_comm (lamI X R caps) (Gm φ (jointD R) |r| M caps)
      linarith only [c1, hm0.trans hYm, s1, s3, e5, hclipT, n1, s5]
    have hYm2 : ∫ u in u₁..u₂, Yf u ≤ 1 / 2 ^ 7 + eta2 * jointT X R ^ 2 := by
      have i5 : IntervalIntegrable (GF φ (jointD R) M r g y caps) volume u₁ u₂ :=
        iGF.mono_set (by
          rw [uIcc_of_le h12, uIcc_of_le hp.hst]
          exact Icc_subset_Icc h1 h2)
      have i6 : IntervalIntegrable (fun u => A * Y u + B) volume u₁ u₂ :=
        (hy.const_mul _).add intervalIntegrable_const
      have e : ∫ u in u₁..u₂, Yf u = 32 * (∫ u in u₁..u₂, GF φ (jointD R) M r g y caps u) +
          ∫ u in u₁..u₂, (A * Y u + B) := by
        simp only [hYf]
        rw [intervalIntegral.integral_add (i5.const_mul 32) i6, intervalIntegral.integral_const_mul]
      rw [e]
      have h3 := hGF u₁ u₂ h1 h12 h2
      norm_num at h3 ⊢
      linarith only [h3, c2]
    constructor
    · rw [intervalIntegral.integral_const_mul]
      have := mul_le_mul_of_nonneg_left hXm (by norm_num : (0 : ℝ) ≤ 64 / 31)
      norm_num at this ⊢
      linarith only [this]
    · rw [intervalIntegral.integral_const_mul]
      have hW0 : 0 ≤ WStar 1 caps.PF Bs / 32 := by
        unfold WStar
        positivity
      have hPF0 : 0 ≤ caps.PF := by
        have h3 := (hp.onPrefix.1 s ⟨le_rfl, hp.hst⟩).1
        exact (hnorm_nonneg 1 _).trans h3
      rcases hPF0.eq_or_lt with hPF | hPF
      · have hl0 : u₂ - u₁ ≤ 0 := by
          refine hl.trans (le_of_eq ?_)
          simp [lamStar, ← hPF]
        have e : u₁ = u₂ := le_antisymm h12 (by linarith)
        rw [e, intervalIntegral.integral_same]
        linarith only [hW0]
      · have hT2 : jointT X R ^ 2 = jointU X * R := by
          have h3 : 0 ≤ jointU X * R := by
            have := hdom.one_lt_U
            positivity
          exact Real.sq_sqrt h3
        have hT1 : 1 ≤ jointT X R ^ 2 := by
          rw [hT2]
          have := hdom.one_lt_U
          nlinarith only [this, hR1]
        have hW : WStar 1 caps.PF Bs = 33 / 32 * (3 / 2) ^ 2 * jointT X R ^ 2 := by
          simp only [WStar, bStar, dZero, hBs, jointBs]
          field_simp
        rw [hW]
        have e : eta2 = 1 / 2 ^ 11 := rfl
        rw [e] at hYm2
        norm_num at hYm2 ⊢
        linarith only [hYm2, hT1]

end OVNS.Quant.Metric

end
