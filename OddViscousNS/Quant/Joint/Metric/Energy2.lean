import OddViscousNS.Quant.Joint.Metric.Bracket2
import OddViscousNS.Quant.Joint.NearFar.Link

/-!
# The second energy on a joint piece (node N15)

`JOINT_ASSEMBLY_V4.md` §4: `E₂' + c c_F² ≤ B b c_F + g₂ b² + h₂`.  `Thr2`: what the threshold gives;
`T2_ae`: the right side of `E₂ = W₂/2`, at almost every time.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic OVNS.Quant.NearFar
open OVNS.Quant.H2 (ae_inH3_split cBil cBil_nonneg metBil2 metBil2_le metForm2_eq_bil metricCorr2
  cubicCorr2 h2Energy fast_h2_law)
open GN (SupBd)

/-- The share of the near, far and quartic terms at weight two. -/
def eta2 : ℝ := 1 / 2 ^ 11

/-- The share of the metric–`Q` insertion at weight two. -/
def etaQ2 : ℝ := 2 ^ 11 * (1 + c4)

lemma one_le_etaQ2 : 1 ≤ etaQ2 := by
  have := c4_pos
  unfold etaQ2
  nlinarith only [this]

lemma metQ_share2 : 32 * c4 / etaQ2 ≤ 1 / 64 := by
  have hc := c4_pos
  have h0 : 0 < etaQ2 := lt_of_lt_of_le one_pos one_le_etaQ2
  rw [div_le_iff₀ h0]
  unfold etaQ2
  nlinarith only [hc]

/-- **What the threshold of the second energy gives at `q = |r|`.** -/
structure Thr2 (X R CS cS r : ℝ) (caps : Caps) : Prop where
  /-- The near, far and quartic terms. -/
  q : qTot₂ eta2 CS cS X R caps ≤ |r|
  /-- The force at weight two. -/
  f2 : force2Q (R - X) (jointD R) (CS * Ex cS R * R) CS (Ex cS R) R caps ≤ |r|
  /-- The force at weight one, for the history of `h₀`. -/
  f1 : force1Q (R - X) R (CS * Ex cS R * R) caps ≤ |r|
  /-- The metric–`Q` insertion. -/
  st : etaQ2 * staticQ R (CS * Ex cS R * R) caps ≤ |r|
  /-- The mass of `h₀`. -/
  h0 : 2 ^ 5 * force0Y (R - X) caps ≤ |r|
  /-- `W ≤ q`. -/
  W : cp caps.WS ≤ |r|
  /-- Role 19. -/
  y : 2 ^ 11 * c4 * cp caps.yF ≤ |r|
  /-- The operator norm of `O`. -/
  K3 : Kc caps / |r| ^ 2 ≤ 1 / 2 ^ 8
  /-- The form `X₁` at weight two. -/
  bil : 2 ^ 8 * cBil * cp caps.BS ≤ |r|
  /-- The operator norm of the metric. -/
  kmet : kapQ r R (CS * Ex cS R * R) caps ≤ 1 / 2 ^ 8
  /-- The clip. -/
  clip : Gm (R - X) (jointD R) |r| (CS * Ex cS R * R) caps * lamI X R caps +
      kapY |r| caps * Real.sqrt (lamI X R caps *
        (4 * slowPrice CS (Ex cS R) R (lamI X R caps))) ≤ 1 / 2 ^ 6

/-- The multiplier of the group, without the near terms. -/
def x2 (φ R M r : ℝ) (g : Field) (y : ℝ → Field) (caps : Caps) (u : ℝ) : ℝ :=
  (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * (1 / 64)) +
    (Gm φ (jointD R) |r| M caps + kapY |r| caps * hnorm 3 (corrSlow r g y u) +
      highG (Chigh (2 * CLow 1)) (jointD R) (cp caps.BS) (cp caps.WS) M
        (hnorm 3 (corrSlow r g y u)) / |r|)

variable {X R CS cS KN KP R₀ r CH Bs : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps}
  {s t : ℝ} {q : Caps → ℝ} {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop}

/-- **The right side of `E₂`, at almost every time.** -/
theorem T2_ae (hres : ResH2 ((281 : ℝ) / 1000) CH) (hdom : JDom R₀ X R) (hCS : 0 ≤ CS)
    (hKN : kN / eta2 ≤ KN) (hKP : kP / eta2 ≤ KP)
    (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece 4 (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t) (hT : Thr2 X R CS cS r caps)
    (hG : ∀ u ∈ Icc s t, CH * fastNorm ((281 : ℝ) / 1000) r g y u ≤ Bs) :
    ∃ m A B g₃ : ℝ, 0 ≤ m ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ g₃ ∧
      (∀ᵐ u ∂(volume.restrict (Icc s t)), T2 (jointD R) r g y u ≤
        Bs * fastNorm 2 r g y u * fastNorm 3 r g y u + 1 / 3 * fastNorm 3 r g y u ^ 2 +
          ((m + g₃ * hnorm 3 (corrSlow r g y u) ^ 2) +
            x2 (R - X) R (CS * Ex cS R * R) r g y caps u) * fastNorm 2 r g y u ^ 2 +
          (32 * GF (R - X) (jointD R) (CS * Ex cS R * R) r g y caps u +
            (A * hnorm 3 (corrSlow r g y u) ^ 2 + B))) ∧
      ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ lamI X R caps →
        (∫ u in u₁..u₂, (m + g₃ * hnorm 3 (corrSlow r g y u) ^ 2)) ≤ 4 * eta2 ∧
        (∫ u in u₁..u₂, (A * hnorm 3 (corrSlow r g y u) ^ 2 + B)) ≤ eta2 * jointT X R ^ 2 := by
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  have hfl : jointSlowFloor X R caps ≤ |r| :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hT.q)
  obtain ⟨-, hφ, hFl, hr1, hr⟩ := floor_setup hdom hfl
  set φ := R - X with hφd
  set M := CS * Ex cS R * R with hMd
  have hq0 : 0 < |r| := by linarith
  have hEx := Ex_pos cS R
  have hM0 : 0 ≤ M := by positivity
  have hD : 1 ≤ jointD R := by
    unfold jointD
    nlinarith only [hR1]
  have hp' : JointPiece 4 M (fun _ => |r|)
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t :=
    { hp with thr := le_rfl }
  have hη : 0 < eta2 := by norm_num [eta2]
  have hη1 : eta2 ≤ 1 := by norm_num [eta2]
  obtain ⟨m, A, B, g₃, hm, hA, hB, hg, hL, hclip⟩ := joint2_left hdom h hp' hCS hη hη1 hKN hKP hT.q
    (D := jointD R) hD hT.f2 (ζ := 1 / 64) (by norm_num) one_le_etaQ2 hT.st
  refine ⟨m, A, B, g₃, hm, hA, hB, hg, ?_, hclip⟩
  filter_upwards [hL, ae_inH3_corr h hr hp.hs hp.hst hp.ht, ae_inH3_split h hp.hs hp.hst hp.ht,
    ae_restrict_mem measurableSet_Icc] with u a1 hy3 h3 hu
  have hu0 : 0 ≤ u := hp.hs.trans hu.1
  have huT := lt_lifespan hu.2 hp.ht
  obtain ⟨c1, c2, c3, c4', c5⟩ := hp.onPrefix.1 u hu
  have hx := actual_adm h hu0 huT
  have hFA : Adm 2 (Fp r g y u) := hx.PiF
  have hSA : Adm 2 (Sp r g y u) := hx.PiS
  have hF' := Fam.PiF_Fp r g y u
  have hε : hnorm 2 (psi r 0 g u) ≤ 1 := by
    obtain ⟨-, hψ⟩ := H2.psi_two_le h hr hu0
    refine hψ.trans ((div_le_one hq0).2 ?_)
    have := hFl.phi
    linarith
  obtain ⟨hsm, hs⟩ := slowNL_one_le h hp.onPrefix hu hp.hs huT hε
  have hbr := bracket_two_le (φ := φ) (M := M) (D := jointD R) h hr1 hD hu0 huT h3.1 h3.2 hy3
    (hp.slow.trace u hu) (c3.trans (le_cp _)) (c4'.trans (le_cp _)) (c5.trans (le_cp _))
    (c2.trans (le_cp _)) (hp.sup u hu) ((c5.trans (le_cp _)).trans hT.W) hs hsm hT.y
    (hT.K3.trans (by norm_num))
  have hb := bracket_le 2 (jointD R) r g y u hSA.real
  have hbare := bare_two (φ := φ) (D := jointD R) (M := M) (caps := caps) h hr1 hD hM0 hu0 huT
  -- the resonance
  have hFa3 : Adm 3 (Fp r g y u) := ⟨h3.1, hFA.real, hFA.sol, hFA.mean⟩
  have hR2 := hres (Fp r g y u) hFa3 hF'
  set d := fastNorm 2 r g y u with hd
  set c := fastNorm 3 r g y u with hc
  have hd0 : 0 ≤ d := hnorm_nonneg _ _
  have hc0 : 0 ≤ c := hnorm_nonneg _ _
  have hRes : -pair 2 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) ≤ Bs * d * c := by
    refine (neg_le_abs _).trans (hR2.trans ?_)
    have h1 := hG u hu
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hd0 hc0)
    have e : CH * hnorm ((281 : ℝ) / 1000) (Fp r g y u) * hnorm 2 (Fp r g y u) *
        hnorm 3 (Fp r g y u) = CH * fastNorm ((281 : ℝ) / 1000) r g y u * (d * c) := by
      simp only [hd, hc, fastNorm, Fp]
      ring
    rw [e]
    nlinarith only [h2]
  have hc2 := sq_nonneg c
  have hs1 : 32 * c4 / etaQ2 * c ^ 2 ≤ 1 / 64 * c ^ 2 := mul_le_mul_of_nonneg_right metQ_share2 hc2
  have hs2 : 5 * eta2 * c ^ 2 ≤ 1 / 64 * c ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num [eta2]) hc2
  simp only [T2, x2]
  have e1 : (m + g₃ * hnorm 3 (corrSlow r g y u) ^ 2 +
      ((Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * (1 / 64)) +
      (Gm φ (jointD R) |r| M caps + kapY |r| caps * hnorm 3 (corrSlow r g y u) +
      highG (Chigh (2 * CLow 1)) (jointD R) (cp caps.BS) (cp caps.WS) M
        (hnorm 3 (corrSlow r g y u)) / |r|))) * d ^ 2 =
      (m + g₃ * hnorm 3 (corrSlow r g y u) ^ 2) * d ^ 2 +
      (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * (1 / 64)) * d ^ 2 +
      (Gm φ (jointD R) |r| M caps + kapY |r| caps * hnorm 3 (corrSlow r g y u) +
      highG (Chigh (2 * CLow 1)) (jointD R) (cp caps.BS) (cp caps.WS) M
        (hnorm 3 (corrSlow r g y u)) / |r|) * d ^ 2 := by ring
  rw [e1]
  linarith only [a1, hbr, hb, hbare, hRes, hs1, hs2, hc2]

/-! ### Coercivity and continuity -/

/-- **`³¹⁄₃₂ b_F² ≤ W ≤ ³³⁄₃₂ b_F²`.** -/
theorem En2_coercive (hdom : JDom R₀ X R) (hCS : 0 ≤ CS) (hKN : kN / eta2 ≤ KN) (hKP : kP / eta2 ≤ KP)
    (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece 4 (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t) (hT : Thr2 X R CS cS r caps)
    {D u : ℝ} (hu : u ∈ Icc s t) :
    31 / 32 * fastNorm 2 r g y u ^ 2 ≤ En2 D r g y u ∧
      En2 D r g y u ≤ 33 / 32 * fastNorm 2 r g y u ^ 2 := by
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  have hfl : jointSlowFloor X R caps ≤ |r| :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hT.q)
  obtain ⟨-, -, -, hr1, hr⟩ := floor_setup hdom hfl
  set M := CS * Ex cS R * R with hMd
  have hq0 : 0 < |r| := by linarith
  have hEx := Ex_pos cS R
  have hM0 : 0 ≤ M := by positivity
  have hp' : JointPiece 4 M (fun _ => |r|)
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t :=
    { hp with thr := le_rfl }
  have hη : 0 < eta2 := by norm_num [eta2]
  have hη1 : eta2 ≤ 1 := by norm_num [eta2]
  obtain ⟨-, -, -, -, -, -, -, -, ht, -, -⟩ := total_two_joint hdom h hp' hCS hη hη1 hKN hKP hT.q
  have hto := ht u hu
  have hu0 : 0 ≤ u := hp.hs.trans hu.1
  have huT := lt_lifespan hu.2 hp.ht
  obtain ⟨c1, c2, c3, c4', c5⟩ := hp.onPrefix.1 u hu
  have hx := actual_adm h hu0 huT
  have hFA : Adm 2 (Fp r g y u) := hx.PiF
  have hSA : Adm 2 (Sp r g y u) := hx.PiS
  have hF' := Fam.PiF_Fp r g y u
  have hS' := Fam.PiS_Sp r g y u
  have hSup : SupBd (Sp r g y u) M := GN.supBd_slowSup hSA.inH (hp.sup u hu)
  set d := fastNorm 2 r g y u with hd
  have hd2 := sq_nonneg d
  have ed : hnorm 2 (Fp r g y u) = d := rfl
  have hm1 : |metricCorr2 r g y u| ≤ 1 / 2 ^ 8 * d ^ 2 := by
    have h1 := metBil2_le hr (r * u) hSA.mz hS' hFA.mz hF' hFA.real hFA.mz hFA.real
    have e : metricCorr2 r g y u = metBil2 r (r * u) (Sp r g y u) (Fp r g y u) (Fp r g y u) :=
      metForm2_eq_bil _ _ _ _
    rw [e]
    refine h1.trans ?_
    rw [ed]
    have h2 : hnorm 2 (Sp r g y u) ≤ cp caps.BS := c4'.trans (le_cp _)
    have h3 : cBil * hnorm 2 (Sp r g y u) / |r| ≤ 1 / 2 ^ 8 := by
      rw [div_le_iff₀ hq0]
      have := mul_le_mul_of_nonneg_left h2 cBil_nonneg
      have := hT.bil
      nlinarith only [this, ‹cBil * hnorm 2 (Sp r g y u) ≤ cBil * cp caps.BS›]
    have e2 : cBil * hnorm 2 (Sp r g y u) * d * d / |r| = cBil * hnorm 2 (Sp r g y u) / |r| * d ^ 2 := by
      ring
    rw [e2]
    exact mul_le_mul_of_nonneg_right h3 hd2
  obtain ⟨hX1, -⟩ := two_X2St hr (r * u) hR1 hSA.mz hS' hFA.mz hFA.mz hF' hF'
  obtain ⟨hZ1, -⟩ := two_ZSt hr (r * u) hSA hS' hSup hFA.mz hF' hFA.sol hFA.mz hF' hFA.sol
  rw [ed] at hX1 hZ1
  have hK := Kmet_le_kapQ (r := r) hR1 hM0 (S := Sp r g y u) (caps := caps) (c5.trans (le_cp _))
    (c3.trans (le_cp _)) (c4'.trans (le_cp _))
  have hK2 := hK.trans hT.kmet
  have hF2 : InH ((2 : ℕ) : ℝ) (Fp r g y u) := by simpa using hFA.inH
  obtain ⟨hzs, hzn⟩ := l2_zOf hF2 hFA.mean
  have hzn' : l2n (zOf 2 (Fp r g y u)) = d := by
    simp only [Nat.cast_ofNat] at hzn
    exact hzn
  have hV := Q3_val_le (s := 2) (Or.inr rfl) hr (r * u) D hSA.mz hS' hzs (Fam.PiF_zOf hF')
  rw [hzn'] at hV
  have hKq : K3 |r| (wiener (Sp r g y u)) (hnorm 2 (Sp r g y u)) ≤ Kc caps / |r| ^ 2 := by
    have := clsS_mono (wiener_nonneg _) (hnorm_nonneg 2 _) (c5.trans (le_cp _)) (c4'.trans (le_cp _))
    simp only [K3, Kc]
    have h2 : 0 ≤ 2 ^ 37 / |r| ^ 2 := by positivity
    refine (mul_le_mul_of_nonneg_left this h2).trans (le_of_eq ?_)
    ring
  have hV2 : ‖(famQ 2 r D).val 2 r g y u‖ ≤ 1 / 2 ^ 8 * d ^ 2 :=
    hV.trans (mul_le_mul_of_nonneg_right (hKq.trans hT.K3) hd2)
  have hvr := (Complex.abs_re_le_norm ((famQ 2 r D).val 2 r g y u)).trans hV2
  have e1 : (famX2 2 r).val 2 r g y u = X2Form 1 2 r (r * u) (Sp r g y u) (Sp r g y u)
      (zOf 2 (Fp r g y u)) (zOf 2 (Fp r g y u)) := famX2_form 2 r (r * u) _ _ _ _
  have e2 : (famZ 2 r).val 2 r g y u = ZForm 1 2 r (r * u) (Sp r g y u) (Sp r g y u)
      (zOf 2 (Fp r g y u)) (zOf 2 (Fp r g y u)) := famZ_form 2 r (r * u) _ _ _ _
  have hX2 : |((famX2 2 r).val 2 r g y u).re| ≤ X2St r R (Sp r g y u) * (d * d) :=
    (Complex.abs_re_le_norm _).trans (by rw [e1]; exact hX1)
  have hZ2 : |((famZ 2 r).val 2 r g y u).re| ≤ CZ / |r| * M * hnorm 2 (Sp r g y u) * (d * d) :=
    (Complex.abs_re_le_norm _).trans (by rw [e2]; exact hZ1)
  have hc := c4_pos
  have ek : X2St r R (Sp r g y u) * (d * d) + CZ / |r| * M * hnorm 2 (Sp r g y u) * (d * d) ≤
      Kmet r R M (Sp r g y u) * d ^ 2 := by
    have h1 : 0 ≤ 2 ^ 8 * (1 + c4) * hnorm 2 (Sp r g y u) / |r| * d ^ 2 := by
      have := hnorm_nonneg 2 (Sp r g y u)
      positivity
    have e0 : Kmet r R M (Sp r g y u) * d ^ 2 = 2 ^ 8 * (1 + c4) * hnorm 2 (Sp r g y u) / |r| * d ^ 2 +
        X2St r R (Sp r g y u) * (d * d) + CZ / |r| * M * hnorm 2 (Sp r g y u) * (d * d) := by
      simp only [Kmet]
      ring
    rw [e0]
    linarith only [h1]
  have hKe := mul_le_mul_of_nonneg_right hK2 hd2
  have a1 := abs_le.1 hm1
  have a2 := abs_le.1 hX2
  have a3 := abs_le.1 hZ2
  have a4 := abs_le.1 hvr
  have a5 := abs_le.1 hto
  have e3 : eta2 = 1 / 2 ^ 11 := rfl
  rw [e3] at a5
  have hE : En2 D r g y u = d ^ 2 + metricCorr2 r g y u + corrJ 2 r g y u +
      2 * ((famQ 2 r D).val 2 r g y u).re + 2 * (cubicCorr2 r g y u + C4 2 r g y u) := by
    simp only [En2, h2Energy]
    ring
  rw [hE]
  simp only [corrJ]
  constructor <;> linarith only [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2, ek, hKe, hd2]

/-- **`En2` is continuous**: it is a primitive. -/
theorem En2_continuousOn {μ φ D : ℝ} (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) : ContinuousOn (En2 D r g y) (Icc a b) := by
  set f : ℝ → ℝ := fun u => T2 D r g y u - fastNorm 3 r g y u ^ 2 with hf
  have hI : IntervalIntegrable f volume a b :=
    (En2_identity h hr D ha hab hb).1.sub (fast_h2_law h ha hab hb).1
  have hid : ∀ c ∈ Icc a b, En2 D r g y c = En2 D r g y a + 2 * ∫ u in a..c, f u := by
    intro c hc
    have hcT := lt_lifespan hc.2 hb
    obtain ⟨i1, e1⟩ := En2_identity h hr D ha hc.1 hcT
    have i2 := (fast_h2_law h ha hc.1 hcT).1
    have e2 : ∫ u in a..c, f u = (∫ u in a..c, T2 D r g y u) - ∫ u in a..c, fastNorm 3 r g y u ^ 2 :=
      intervalIntegral.integral_sub i1 i2
    rw [e2, ← e1]
    ring
  have hp : ContinuousOn (fun c => ∫ u in a..c, f u) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval
      (by rw [uIcc_of_le hab]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hI)
  rw [uIcc_of_le hab] at hp
  have hc : ContinuousOn (fun c => En2 D r g y a + 2 * ∫ u in a..c, f u) (Icc a b) :=
    continuousOn_const.add (continuousOn_const.mul hp)
  exact hc.congr hid

end OVNS.Quant.Metric

end
