import OddViscousNS.Quant.Joint.Metric.Energy1

/-!
# The output of the first energy (node N14)

`h1_output`: on a joint piece where `Thr1` holds, `H1Output` holds, with the energy `En1`, the force
`N_f = 6 hBd`, the tested `f_f = 2 · 24 c₄ P_F² hBd`, and the multiplier `m1`.
`JOINT_ASSEMBLY_V4.md` §3: "the whole `h₀` derivative is either retained as its genuine form or paid by
the explicit J2 Young mass": here it is the Young mass, the first term of `m1`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic OVNS.Quant.NearFar
open OVNS.Quant.H2 (ae_inH3_split)
open GN (SupBd)

variable {X R CS cS KN KP D R₀ r Cs CN Cp φ : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}
  {caps : Caps} {s t : ℝ} {q : Caps → ℝ} {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop}

/-- `hBd` is continuous on the lifespan. -/
lemma hBd_cont {μ : ℝ} (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) : ContinuousOn (hBd φ r g y) (Icc 0 b) := by
  obtain ⟨-, c2, -, c4', -, -, -, -⟩ := norms_continuous h hb hbT
  unfold hBd
  exact (continuousOn_const.mul (c4'.add c2)).add continuousOn_const

/-- `h0Bd` is continuous on the lifespan. -/
lemma h0Bd_cont {μ : ℝ} (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) : ContinuousOn (h0Bd φ r g y) (Icc 0 b) := by
  obtain ⟨-, c2, -, -, -, -, -, -⟩ := norms_continuous h hb hbT
  unfold h0Bd
  exact (continuousOn_const.add (continuousOn_const.mul (c2.pow 2))).add (hBd_cont h hb hbT)

lemma half_le_ell1' : (1 : ℝ) / 2 ≤ ell1 := by
  unfold ell1
  norm_num

/-- **The multiplier is integrable.** -/
lemma m1_integrable {μ M : ℝ} (h : ActualSol μ φ r g y Ty) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : ENNReal.ofReal b < Ty)
    (hy : IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume a b) :
    IntervalIntegrable (m1 φ R M D r g y caps) volume a b := by
  have ht0 := ha.trans hab
  have hsub : uIcc a b ⊆ Icc 0 b := by
    rw [uIcc_of_le hab]
    exact Icc_subset_Icc_left ha
  have c1 := (h0Bd_cont h ht0 hb).mono hsub
  have c2 := (kinD_cont h ht0 hb).mono hsub
  have i1 : IntervalIntegrable (fun u => (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 /
      (4 * (1 / 64))) volume a b :=
    (((continuousOn_const.mul c1).div_const _).pow 2 |>.div_const _).intervalIntegrable
  have i2 : IntervalIntegrable (fun u => kap1 φ R M D |r| caps * kinD r g y u) volume a b :=
    (continuousOn_const.mul c2).intervalIntegrable
  have i3 := hy.const_mul (kap2 D |r| caps)
  have i4 : IntervalIntegrable (fun _ : ℝ => kap3 R M D |r| caps) volume a b :=
    intervalIntegrable_const
  exact i1.add ((i2.add i3).add i4)

/-- **The output of the first energy.** -/
theorem h1_output (hres : ResH1 ((281 : ℝ) / 1000) Cs) (hdom : JDom R₀ X R) (hCS : 0 ≤ CS)
    (hKN : 256 * kN ≤ KN) (hKP : 256 * kP ≤ KP) (hKP1 : 1 ≤ KP) (hD : 1 ≤ D)
    (hCN : 3 ≤ CN) (hCp : 2 ≤ Cp)
    (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece 4 (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t) (hT : Thr1 X R CS cS D r caps) :
    H1Output ((281 : ℝ) / 1000) Cs (CN * X) (Cp * X) r g y s t := by
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  have hX1 : 1 ≤ X := hdom.one_lt_X.le
  obtain ⟨-, hφ, -, hr1, hr⟩ := floor_setup hdom hT.fl
  set φ := R - X with hφd
  set M := CS * Ex cS R * R with hMd
  have hq0 : 0 < |r| := by linarith
  have hEx := Ex_pos cS R
  have hM0 : 0 ≤ M := by positivity
  have hCex : 0 ≤ CS * Ex cS R := by positivity
  have hO : SlowOut CS (Ex cS R) R Sl r g y s t := hp.slow
  have hp' : JointPiece 4 M (fun _ => |r|)
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t :=
    { hp with thr := le_rfl }
  obtain ⟨-, hI1, hI2⟩ := force1_joint h hp' hR1 hT.f1
  have hae := T1_ae hres hdom hCS hKN hKP hKP1 hD h hp hT
  have ht0 : 0 ≤ t := hp.hs.trans hp.hst
  have hsubst : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → uIcc u₁ u₂ ⊆ Icc 0 t := fun u₁ u₂ h1 h2 h3 => by
    rw [uIcc_of_le h2]
    exact Icc_subset_Icc (hp.hs.trans h1) h3
  have hcy : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume u₁ u₂ :=
    fun u₁ u₂ h1 h2 h3 => hO.cy_int.mono_set (by
      rw [uIcc_of_le h2, uIcc_of_le hp.hst]
      exact Icc_subset_Icc h1 h3)
  obtain ⟨cE, cD, -, -, -, -, -, -⟩ := norms_continuous h ht0 hp.ht
  have cB := hBd_cont h ht0 hp.ht
  refine ⟨En1 D r g y, fun u => 6 * hBd φ r g y u, fun u => 2 * (24 * c4 * cp caps.PF ^ 2 *
    hBd φ r g y u), m1 φ R M D r g y caps, fun u hu =>
    En1_coercive hdom hCS hKN hKP hKP1 h hp hT hu, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the integrated inequality
    intro u₁ u₂ h1 h12 h2
    have hu₁ : 0 ≤ u₁ := hp.hs.trans h1
    have hu₂ : ENNReal.ofReal u₂ < Ty := lt_lifespan h2 hp.ht
    obtain ⟨hI, hid⟩ := En1_identity h hr D hu₁ h12 hu₂
    have hs' := hsubst u₁ u₂ h1 h12 h2
    have cE' := cE.mono hs'
    have cD' := cD.mono hs'
    have cB' := cB.mono hs'
    have c1 : ContinuousOn (fun u => fastNorm 1 r g y u ^ (3 - (281 : ℝ) / 1000)) (uIcc u₁ u₂) :=
      cE'.rpow_const fun _ _ => Or.inr (by norm_num)
    have c2 : ContinuousOn (fun u => fastNorm 2 r g y u ^ ((281 : ℝ) / 1000)) (uIcc u₁ u₂) :=
      cD'.rpow_const fun _ _ => Or.inr (by norm_num)
    have i1 : IntervalIntegrable (fun u => Cs * fastNorm 1 r g y u ^ (3 - (281 : ℝ) / 1000) *
        fastNorm 2 r g y u ^ ((281 : ℝ) / 1000)) volume u₁ u₂ :=
      ((continuousOn_const.mul c1).mul c2).intervalIntegrable
    have i2 : IntervalIntegrable (fun u => 6 * hBd φ r g y u * fastNorm 2 r g y u) volume u₁ u₂ :=
      ((continuousOn_const.mul cB').mul cD').intervalIntegrable
    have i3 : IntervalIntegrable (fun u => 2 * (24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u))
        volume u₁ u₂ :=
      (continuousOn_const.mul (continuousOn_const.mul cB')).intervalIntegrable
    have i4 : IntervalIntegrable (fun u => m1 φ R M D r g y caps u * fastNorm 1 r g y u ^ 2)
        volume u₁ u₂ :=
      (m1_integrable h hu₁ h12 hu₂ (hcy u₁ u₂ h1 h12 h2)).mul_continuousOn (cE'.pow 2)
    have i5 : IntervalIntegrable (fun u => fastNorm 2 r g y u ^ 2) volume u₁ u₂ :=
      (cD'.pow 2).intervalIntegrable
    have iK := ((i1.add i2).add i3).add i4
    have hmono := intervalIntegral.integral_mono_ae_restrict h12 hI (iK.add (i5.const_mul (1 / 4)))
      (ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc h1 h2) hae)
    have e1 : ∫ u in u₁..u₂, (Cs * fastNorm 1 r g y u ^ (3 - (281 : ℝ) / 1000) *
          fastNorm 2 r g y u ^ ((281 : ℝ) / 1000) + 6 * hBd φ r g y u * fastNorm 2 r g y u +
          2 * (24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) +
          m1 φ R M D r g y caps u * fastNorm 1 r g y u ^ 2 + 1 / 4 * fastNorm 2 r g y u ^ 2) =
        (∫ u in u₁..u₂, (Cs * fastNorm 1 r g y u ^ (3 - (281 : ℝ) / 1000) *
          fastNorm 2 r g y u ^ ((281 : ℝ) / 1000) + 6 * hBd φ r g y u * fastNorm 2 r g y u +
          2 * (24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) +
          m1 φ R M D r g y caps u * fastNorm 1 r g y u ^ 2)) +
        1 / 4 * ∫ u in u₁..u₂, fastNorm 2 r g y u ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_add iK (i5.const_mul (1 / 4))
    rw [e1] at hmono
    have e2 : ∀ u, Cs * fastNorm 1 r g y u ^ (3 - (281 : ℝ) / 1000) *
          fastNorm 2 r g y u ^ ((281 : ℝ) / 1000) + 6 * hBd φ r g y u * fastNorm 2 r g y u +
          2 * (24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) +
          m1 φ R M D r g y caps u * fastNorm 1 r g y u ^ 2 =
        Cs * fastNorm 1 r g y u ^ (3 - (281 : ℝ) / 1000) *
          fastNorm 2 r g y u ^ ((281 : ℝ) / 1000) + (6 * hBd φ r g y u) * fastNorm 2 r g y u +
          2 * (24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) +
          m1 φ R M D r g y caps u * fastNorm 1 r g y u ^ 2 := fun _ => rfl
    linarith only [hmono, hid]
  · intro u _
    have h0 := hBd_nonneg hφ r g y u
    have hc := c4_pos
    obtain ⟨k1, k2, k3⟩ := kap_nonneg (φ := φ) (M := M) (D := D) hφ hR0 hM0 hD hq0 caps
    refine ⟨by positivity, ?_⟩
    have := kinD_nonneg r g y u
    simp only [m1]
    positivity
  · exact ((continuousOn_const.mul (cB.mono (by
      rw [uIcc_of_le hp.hst]
      exact Icc_subset_Icc_left hp.hs))).pow 2).intervalIntegrable
  · exact (continuousOn_const.mul (continuousOn_const.mul (cB.mono (by
      rw [uIcc_of_le hp.hst]
      exact Icc_subset_Icc_left hp.hs)))).intervalIntegrable
  · exact m1_integrable h hp.hs hp.hst hp.ht hO.cy_int
  · have e : ∀ u, (6 * hBd φ r g y u) ^ 2 = 9 * (2 * hBd φ r g y u) ^ 2 := fun u => by ring
    simp only [e]
    rw [intervalIntegral.integral_const_mul]
    have h1 : (3 : ℝ) ^ 2 ≤ (CN * X) ^ 2 := by
      have : (3 : ℝ) ≤ CN * X := by nlinarith only [hCN, hX1]
      exact pow_le_pow_left₀ (by norm_num) this 2
    nlinarith only [hI1, h1]
  · rw [intervalIntegral.integral_const_mul]
    have h1 : (2 : ℝ) ^ 2 ≤ (Cp * X) ^ 2 := by
      have : (2 : ℝ) ≤ Cp * X := by nlinarith only [hCp, hX1]
      exact pow_le_pow_left₀ (by norm_num) this 2
    nlinarith only [hI2, h1]
  · -- the mass
    obtain ⟨k1, k2, k3⟩ := kap_nonneg (φ := φ) (M := M) (D := D) hφ hR0 hM0 hD hq0 caps
    have hsub0 : uIcc s t ⊆ Icc 0 t := by
      rw [uIcc_of_le hp.hst]
      exact Icc_subset_Icc_left hp.hs
    have i0 : IntervalIntegrable (fun u => (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 /
        (4 * (1 / 64))) volume s t :=
      (((continuousOn_const.mul ((h0Bd_cont h ht0 hp.ht).mono hsub0)).div_const _).pow 2
        |>.div_const _).intervalIntegrable
    obtain ⟨ik, hk⟩ := kinD_piece_le h hO hp.hs hp.hst hp.ht hp.len
    have hy := hO.cy_piece_le hCex hR0.le hp.hst hp.len
    have i1 : IntervalIntegrable (fun u => kap1 φ R M D |r| caps * kinD r g y u) volume s t :=
      ik.const_mul _
    have i2 : IntervalIntegrable (fun u => kap2 D |r| caps * hnorm 3 (corrSlow r g y u) ^ 2)
        volume s t := hO.cy_int.const_mul _
    have i3 : IntervalIntegrable (fun _ : ℝ => kap3 R M D |r| caps) volume s t :=
      intervalIntegrable_const
    have e : ∫ u in s..t, m1 φ R M D r g y caps u =
        (∫ u in s..t, (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * (1 / 64))) +
          (kap1 φ R M D |r| caps * (∫ u in s..t, kinD r g y u) +
            kap2 D |r| caps * (∫ u in s..t, hnorm 3 (corrSlow r g y u) ^ 2) +
            (t - s) * kap3 R M D |r| caps) := by
      simp only [m1]
      rw [intervalIntegral.integral_add i0 ((i1.add i2).add i3),
        intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul]
    have hm0 := h0_mass_clip (ζ := 1 / 64) h hp.hs hp.hst hp.ht hp.len hp.onPrefix hR0.le hM0 hT.f1
      (by norm_num) le_rfl hp.hst le_rfl
    have hY : (Ch0 * kapH0 caps * H0c φ caps / |r|) ^ 2 / (4 * (1 / 64)) ≤ 1 / 64 := by
      have hf0 : 0 ≤ Ch0 * kapH0 caps * H0c φ caps := by
        have := Ch0_pos
        have := kapH0_pos caps
        have := H0c_nonneg hφ caps
        positivity
      have h1 : Ch0 * kapH0 caps * H0c φ caps / |r| ≤ 1 / 2 ^ 5 := by
        rw [div_le_iff₀ hq0]
        have : 2 ^ 5 * force0Y φ caps ≤ |r| := hT.h0
        unfold force0Y at this
        linarith only [this]
      have h2 := pow_le_pow_left₀ (div_nonneg hf0 hq0.le) h1 2
      norm_num at h2 ⊢
      linarith only [h2]
    have hk1 := mul_le_mul_of_nonneg_left hk k1
    have hk2 := mul_le_mul_of_nonneg_left hy k2
    have hk3 := mul_le_mul_of_nonneg_right hp.len k3
    have hm3 := hT.mass
    have hmass : ∫ u in s..t, m1 φ R M D r g y caps u ≤ 1 / 16 := by
      rw [e]
      linarith only [hm0, hY, hk1, hk2, hk3, hm3]
    have hell := half_le_ell1'
    have hell0 : 0 < ell1 := by linarith only [hell]
    have h4 : 2 / ell1 ≤ 4 := by
      rw [div_le_iff₀ hell0]
      linarith only [hell]
    by_cases hm : 0 ≤ ∫ u in s..t, m1 φ R M D r g y caps u
    · calc 2 / ell1 * (∫ u in s..t, m1 φ R M D r g y caps u) ≤ 4 * (1 / 16) :=
            mul_le_mul h4 hmass hm (by norm_num)
        _ ≤ 1 := by norm_num
    · have h5 : 0 ≤ 2 / ell1 := by positivity
      have := mul_nonneg h5 (le_of_lt (not_le.1 hm |> neg_pos.2))
      nlinarith only [this]

end OVNS.Quant.Metric

end
