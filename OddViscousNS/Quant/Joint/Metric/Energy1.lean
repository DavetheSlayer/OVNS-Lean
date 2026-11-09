import OddViscousNS.Quant.Joint.Metric.Bracket1
import OddViscousNS.Quant.Joint.NearFar.Main

/-!
# The first energy on a joint piece (node N14)

`JOINT_ASSEMBLY_V4.md` §3: `E₁' + c b² ≤ C_s a^{3−σ} b^σ + m₁ a² + N_f b + f_f`.

`Thr1` lists what the threshold has to give.  `T1_ae`: the right side of `E₁`, at almost every time.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic OVNS.Quant.NearFar
open OVNS.Quant.H2 (ae_inH3_split)
open GN (SupBd)

/-- The share of `C₄,₁`: `2⁻²³`. -/
def eta41 : ℝ := 1 / 2 ^ 23

/-- The amplitude of the threshold of `C₄,₁`. -/
def amp1 : ℝ := 2 ^ 26 * Real.exp 5 / eta41 ^ 2

/-- The share of the metric–`Q` insertion. -/
def etaQ : ℝ := 2 ^ 10 * (1 + c4)

lemma one_le_etaQ : 1 ≤ etaQ := by
  have := c4_pos
  unfold etaQ
  nlinarith only [this]

lemma metQ_share : 16 * c4 / etaQ ≤ 1 / 64 := by
  have hc := c4_pos
  have h0 : 0 < etaQ := lt_of_lt_of_le one_pos one_le_etaQ
  rw [div_le_iff₀ h0]
  unfold etaQ
  nlinarith only [hc]

/-- **What the threshold of the first energy gives at `q = |r|`.** -/
structure Thr1 (X R CS cS D r : ℝ) (caps : Caps) : Prop where
  /-- The slow floor. -/
  fl : jointSlowFloor X R caps ≤ |r|
  /-- The force. -/
  f1 : force1Q (R - X) R (CS * Ex cS R * R) caps ≤ |r|
  /-- The metric–`Q` insertion. -/
  st : etaQ * staticQ R (CS * Ex cS R * R) caps ≤ |r|
  /-- `C₄,₁`. -/
  q4 : qOneFull amp1 X R caps ≤ |r|
  /-- The near and far differentials. -/
  nf : qNF₁ (1 / 256) X R caps ≤ |r|
  /-- The mass of `h₀`. -/
  h0 : 2 ^ 5 * force0Y (R - X) caps ≤ |r|
  /-- The share of `b_F²` in the group. -/
  nu : nu1 |r| D (CS * Ex cS R * R) caps ≤ 1 / 64
  /-- The operator norm of `O`. -/
  K3 : Kc caps / |r| ^ 2 ≤ 1 / 2 ^ 24
  /-- The operator norm of the metric. -/
  kmet : kapQ r R (CS * Ex cS R * R) caps ≤ 1 / 2 ^ 22
  /-- The mass. -/
  mass : kap1 (R - X) R (CS * Ex cS R * R) D |r| caps * (8 * (CS * Ex cS R * R ^ 2)) +
      kap2 D |r| caps * (4 * slowPrice CS (Ex cS R) R 1) +
      4 * kap3 R (CS * Ex cS R * R) D |r| caps ≤ 3 / 64

/-- The multiplier of `a_F²`. -/
def m1 (φ R M D r : ℝ) (g : Field) (y : ℝ → Field) (caps : Caps) (u : ℝ) : ℝ :=
  (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * (1 / 64)) +
    (kap1 φ R M D |r| caps * kinD r g y u + kap2 D |r| caps * hnorm 3 (corrSlow r g y u) ^ 2 +
      kap3 R M D |r| caps)

variable {X R CS cS KN KP D R₀ r Cs : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps}
  {s t : ℝ} {q : Caps → ℝ} {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop}

/-- `P(q) ≤ Q^{−1/3}` on a joint piece. -/
lemma nearP_of_paid (hdom : JDom R₀ X R) (hKP : 1 ≤ KP)
    (h : NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP caps |r|) :
    nearP |r| ≤ zq X R := by
  have hP : 0 ≤ nearP |r| := nearP_nonneg (abs_nonneg r)
  obtain ⟨-, -, p3⟩ := proper_shares (by linarith : 0 ≤ KP) hdom hP h.2
  exact nearP_le_zq hdom hKP (abs_nonneg r) p3

/-- **The right side of `E₁`, at almost every time.** -/
theorem T1_ae (hres : ResH1 ((281 : ℝ) / 1000) Cs) (hdom : JDom R₀ X R) (hCS : 0 ≤ CS)
    (hKN : 256 * kN ≤ KN) (hKP : 256 * kP ≤ KP) (hKP1 : 1 ≤ KP) (hD : 1 ≤ D)
    (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece 4 (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t) (hT : Thr1 X R CS cS D r caps) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), T1 D r g y u ≤
      Cs * fastNorm 1 r g y u ^ (3 - (281 : ℝ) / 1000) * fastNorm 2 r g y u ^ ((281 : ℝ) / 1000) +
        6 * hBd (R - X) r g y u * fastNorm 2 r g y u +
        2 * (24 * c4 * cp caps.PF ^ 2 * hBd (R - X) r g y u) +
        m1 (R - X) R (CS * Ex cS R * R) D r g y caps u * fastNorm 1 r g y u ^ 2 +
        1 / 4 * fastNorm 2 r g y u ^ 2 := by
  have hX0 : 0 ≤ X := by linarith [hdom.one_lt_X]
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  obtain ⟨-, hφ, hFl, hr1, hr⟩ := floor_setup hdom hT.fl
  set φ := R - X with hφd
  set M := CS * Ex cS R * R with hMd
  have hq0 : 0 < |r| := by linarith
  have hEx := Ex_pos cS R
  have hM0 : 0 ≤ M := by positivity
  -- the constant threshold
  have hp' : JointPiece 4 M (fun _ => |r|)
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t :=
    { hp with thr := le_rfl }
  have hη : (0 : ℝ) < 1 / 256 := by norm_num
  have hKNe : kN / (1 / 256) ≤ KN := by
    rw [div_div_eq_mul_div, div_one]
    linarith
  have hKPe : kP / (1 / 256) ≤ KP := by
    rw [div_div_eq_mul_div, div_one]
    linarith
  have hnf := nf_one_joint hdom h hp' hCS hη hKNe hKPe hT.nf
  have hP := nearP_of_paid hdom hKP1 hp.nearPaid
  have hq4 := quartic_one_piece hdom h hr hp.hs hp.ht hp.onPrefix
    (by norm_num [eta41] : 0 < eta41) (by norm_num [eta41]) hT.q4 hP
  have hfin := joint1_final_le (ζ := 1 / 64) h hr hp' hR1 hT.f1 (by norm_num) hR1 one_le_etaQ hT.st
  obtain ⟨hF1, -, -⟩ := force1_joint h hp' hR1 hT.f1
  filter_upwards [hfin, ae_inH3_corr h hr hp.hs hp.hst hp.ht, ae_inH3_split h hp.hs hp.hst hp.ht,
    ae_restrict_mem measurableSet_Icc] with u a1 hy3 h3 hu
  have hu0 : 0 ≤ u := hp.hs.trans hu.1
  have huT := lt_lifespan hu.2 hp.ht
  obtain ⟨c1, c2, c3, c4', c5⟩ := hp.onPrefix.1 u hu
  obtain ⟨-, n2, n3, n4⟩ := hnf u hu
  obtain ⟨-, q2⟩ := hq4 u hu
  have f1 := hF1 u hu
  have hx := actual_adm h hu0 huT
  have hFA : Adm 2 (Fp r g y u) := hx.PiF
  have hSA : Adm 2 (Sp r g y u) := hx.PiS
  have hF' := Fam.PiF_Fp r g y u
  -- the slow direction
  have hε : hnorm 2 (psi r 0 g u) ≤ 1 := by
    obtain ⟨-, hψ⟩ := H2.psi_two_le h hr hu0
    refine hψ.trans ((div_le_one hq0).2 ?_)
    have := hFl.phi
    linarith
  obtain ⟨hsm, hs⟩ := slowNL_one_le h hp.onPrefix hu hp.hs huT hε
  have hbr := bracket_one_le (φ := φ) (R := R) (M := M) (D := D) h hr1 hD hR0 hu0 huT
    (c3.trans (le_cp _)) (c4'.trans (le_cp _)) (c5.trans (le_cp _)) (c1.trans (le_cp _))
    (hp.sup u hu) hy3 (hp.slow.trace u hu) hs hsm
  have hb := bracket_le 1 D r g y u hSA.real
  -- the native differential
  obtain ⟨-, -, hH2, -, -⟩ := link_facts h hr hu0 huT h3.1 h3.2
  obtain ⟨hN2, -, -, -, -⟩ := link_facts h hr hu0 huT h3.1 h3.2
  have hFm3 : MZ 3 (Fp r g y u) := ⟨h3.1, hFA.mean⟩
  have ecD : cubicD 1 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) =
      cubicD 1 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) +
        cubicD 1 (-1) r (r * u) (Fp r g y u) (Hf r g y u) := by
    rw [fastQ_eq]
    exact cubicD_add (Or.inl rfl) (Or.inr rfl) r (r * u) hFm3 hN2 hH2
  have esp := cubicD_split_one h hu0 huT
  -- the resonance
  have hR2 := hres (Fp r g y u) hFA hF'
  have hRes : -pair 1 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) ≤
      Cs * fastNorm 1 r g y u ^ (3 - (281 : ℝ) / 1000) * fastNorm 2 r g y u ^ ((281 : ℝ) / 1000) :=
    (neg_le_abs _).trans hR2
  -- the bare term in the force
  have hcD : |cubicD 1 (-1) r (r * u) (Fp r g y u) (Hf r g y u)| ≤ force1 r g y u := by
    unfold force1
    have := abs_nonneg (pair 1 (Fp r g y u) (Hpsi r g y u))
    have := abs_nonneg (2 * pair 1 (Fp r g y u) (X1op r (r * u) (Sp r g y u) (Hf r g y u)) +
      2 * pair 1 (Hf r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u)))
    have := norm_nonneg (X2Form 1 1 r (r * u) (Sp r g y u) (Sp r g y u) (zOf 1 (Hf r g y u))
      (zp 1 r g y u))
    have := norm_nonneg (X2Form 1 1 r (r * u) (Sp r g y u) (Sp r g y u) (zp 1 r g y u)
      (zOf 1 (Hf r g y u)))
    have := norm_nonneg (ZForm 1 1 r (r * u) (Sp r g y u) (Sp r g y u) (zOf 1 (Hf r g y u))
      (zp 1 r g y u))
    have := norm_nonneg (ZForm 1 1 r (r * u) (Sp r g y u) (Sp r g y u) (zp 1 r g y u)
      (zOf 1 (Hf r g y u)))
    linarith
  -- the sizes of the filter
  set e := fastNorm 1 r g y u with he
  set d := fastNorm 2 r g y u with hd
  have he0 : 0 ≤ e := hnorm_nonneg _ _
  have hd0 : 0 ≤ d := hnorm_nonneg _ _
  obtain ⟨-, hHf⟩ := Hf_one h hr hu0 huT
  have hHf' : hnorm 1 (Hf r g y u) ≤ hBd φ r g y u := hHf
  obtain ⟨-, hHp⟩ := hnorm_one_Hpsi_le h hr hu0 huT
  have hHp' : hnorm 1 (Hpsi r g y u) ≤ hBd φ r g y u := hHp
  have hB0 : 0 ≤ hBd φ r g y u := (hnorm_nonneg _ _).trans hHp'
  have hQ0 : 0 ≤ Kc caps / |r| ^ 2 := div_nonneg (Kc_nonneg caps) (by positivity)
  have t1 : 2 * (Kc caps / |r| ^ 2) * hnorm 1 (Hf r g y u) * d ≤ hBd φ r g y u * d := by
    have h1 : 2 * (Kc caps / |r| ^ 2) ≤ 1 := by
      have := hT.K3
      norm_num at this ⊢
      linarith
    have h2 := mul_le_mul h1 hHf' (hnorm_nonneg _ _) zero_le_one
    rw [one_mul] at h2
    exact mul_le_mul_of_nonneg_right h2 hd0
  have t2 : eta41 * hnorm 1 (Hpsi r g y u) * d ≤ hBd φ r g y u * d := by
    have h1 : eta41 ≤ 1 := by norm_num [eta41]
    have h2 := mul_le_mul h1 hHp' (hnorm_nonneg _ _) zero_le_one
    rw [one_mul] at h2
    exact mul_le_mul_of_nonneg_right h2 hd0
  have hd2 := sq_nonneg d
  have hs1 : 16 * c4 / etaQ * d ^ 2 ≤ 1 / 64 * d ^ 2 := mul_le_mul_of_nonneg_right metQ_share hd2
  have hs2 : nu1 |r| D M caps * d ^ 2 ≤ 1 / 64 * d ^ 2 := mul_le_mul_of_nonneg_right hT.nu hd2
  have hs3 : eta41 * d ^ 2 ≤ 1 / 64 * d ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num [eta41]) hd2
  have a2 := abs_le.1 n2
  have a3 := abs_le.1 n3
  have a4 := abs_le.1 n4
  have a5 := abs_le.1 hcD
  have a6 := abs_le.1 q2
  simp only [T1, m1]
  have e0 : joint1T r g y u = -pair 1 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) -
      cubicHeat r (r * u) (Fp r g y u) + cubicD 1 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) +
      1 / 2 * (insT (famX2 1 r) 1 r g y u).re + 1 / 2 * (insT (famZ 1 r) 1 r g y u).re := rfl
  rw [e0, ecD, esp] at a1
  have e6 : (((Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * (1 / 64))) +
      (kap1 φ R M D |r| caps * kinD r g y u + kap2 D |r| caps * hnorm 3 (corrSlow r g y u) ^ 2 +
        kap3 R M D |r| caps)) * e ^ 2 =
      (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * (1 / 64)) * e ^ 2 +
      (kap1 φ R M D |r| caps * kinD r g y u + kap2 D |r| caps * hnorm 3 (corrSlow r g y u) ^ 2 +
        kap3 R M D |r| caps) * e ^ 2 := by ring
  rw [e6]
  have e7 : (nu1 |r| D M caps + 1 / 32) * d ^ 2 = nu1 |r| D M caps * d ^ 2 + 1 / 32 * d ^ 2 := by ring
  rw [e7] at hbr
  linarith only [a1, hbr, hb, hRes, a2.1, a3.2, a4.2, a5.2, a6.2, f1, t1, t2, hs1, hs2, hs3, hd2]

/-! ### Nonnegativity -/

lemma kap_nonneg {φ R M D q : ℝ} (hφ : 0 ≤ φ) (hR : 0 < R) (hM : 0 ≤ M) (hD : 1 ≤ D) (hq : 0 < q)
    (caps : Caps) :
    0 ≤ kap1 φ R M D q caps ∧ 0 ≤ kap2 D q caps ∧ 0 ≤ kap3 R M D q caps := by
  have hD0 : 0 < D := by linarith
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlog4 : 0 ≤ Real.log (4 * D) := Real.log_nonneg (by linarith)
  have hC := Cm3_pos
  have hcL := cL_nonneg
  have hA := cp_nonneg caps.AS
  have hB := cp_nonneg caps.BS
  have hW := cp_nonneg caps.WS
  have hc := c4_pos
  have hT := T0_nonneg D
  have hS := hSrc_nonneg hφ caps
  have hZ : 0 ≤ Zs D := by unfold Zs; positivity
  have hZ4 : 0 ≤ Z4s D := by unfold Z4s; positivity
  have hcL1 : 0 ≤ cL + 1 := by linarith
  have a1 : 0 ≤ A11 R M D (cp caps.BS) := by
    unfold A11
    positivity
  have b1 : 0 ≤ B11 φ D caps := by
    unfold B11 B11g
    positivity
  refine ⟨?_, ?_, ?_⟩
  · have := Kc_nonneg caps
    unfold kap1
    positivity
  · unfold kap2 A12
    positivity
  · unfold kap3 A13 B13
    positivity

/-! ### Coercivity -/

/-- The arithmetic of coercivity (`Energy/H1/Main.lean`). -/
lemma coercive_core' {a2 m c : ℝ} (hm : |m| ≤ 1 / 2 ^ 20 * a2) (hc : |2 * c| ≤ 1 / 128 * a2) :
    ell1 * a2 ≤ a2 + m + 2 * c ∧ a2 + m + 2 * c ≤ u1 * a2 := by
  have h1 := abs_le.mp hm
  have h2 := abs_le.mp hc
  unfold ell1 u1
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

/-- **`ℓ₁ a_F² ≤ 2 E₁ ≤ u₁ a_F²`.** -/
theorem En1_coercive (hdom : JDom R₀ X R) (hCS : 0 ≤ CS)
    (hKN : 256 * kN ≤ KN) (hKP : 256 * kP ≤ KP) (hKP1 : 1 ≤ KP)
    (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece 4 (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t) (hT : Thr1 X R CS cS D r caps)
    {u : ℝ} (hu : u ∈ Icc s t) :
    ell1 * fastNorm 1 r g y u ^ 2 ≤ 2 * En1 D r g y u ∧
      2 * En1 D r g y u ≤ u1 * fastNorm 1 r g y u ^ 2 := by
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  obtain ⟨-, -, -, hr1, hr⟩ := floor_setup hdom hT.fl
  set φ := R - X with hφd
  set M := CS * Ex cS R * R with hMd
  have hq0 : 0 < |r| := by linarith
  have hEx := Ex_pos cS R
  have hM0 : 0 ≤ M := by positivity
  have hp' : JointPiece 4 M (fun _ => |r|)
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t :=
    { hp with thr := le_rfl }
  have hη : (0 : ℝ) < 1 / 256 := by norm_num
  have hKNe : kN / (1 / 256) ≤ KN := by
    rw [div_div_eq_mul_div, div_one]
    linarith
  have hKPe : kP / (1 / 256) ≤ KP := by
    rw [div_div_eq_mul_div, div_one]
    linarith
  obtain ⟨n1, -, -, -⟩ := nf_one_joint hdom h hp' hCS hη hKNe hKPe hT.nf u hu
  have hP := nearP_of_paid hdom hKP1 hp.nearPaid
  obtain ⟨q1, -⟩ := quartic_one_piece hdom h hr hp.hs hp.ht hp.onPrefix
    (by norm_num [eta41] : 0 < eta41) (by norm_num [eta41]) hT.q4 hP u hu
  have hu0 : 0 ≤ u := hp.hs.trans hu.1
  have huT := lt_lifespan hu.2 hp.ht
  obtain ⟨c1, c2, c3, c4', c5⟩ := hp.onPrefix.1 u hu
  have hx := actual_adm h hu0 huT
  have hFA : Adm 2 (Fp r g y u) := hx.PiF
  have hSA : Adm 2 (Sp r g y u) := hx.PiS
  have hF' := Fam.PiF_Fp r g y u
  have hS' := Fam.PiS_Sp r g y u
  have hSup : SupBd (Sp r g y u) M := GN.supBd_slowSup hSA.inH (hp.sup u hu)
  set e := fastNorm 1 r g y u with he
  have he2 := sq_nonneg e
  have ee : hnorm 1 (Fp r g y u) = e := rfl
  have hF1 : MZ 1 (Fp r g y u) := hFA.mz.mono' (by norm_num)
  have hm1 : |metricCorr r g y u| ≤ 2 ^ 8 * hnorm 2 (Sp r g y u) * e ^ 2 / |r| :=
    X1form_le hr (r * u) hSA.mz hSA.real hS' hFA.mz hF'
  obtain ⟨hX1, -⟩ := one_X2 hr (r * u) hR1 hSA.mz hS' hF1 hF1 hF' hF'
  obtain ⟨hZ1, -⟩ := one_Z hr (r * u) hSA hS' hSup hF1 hF' hFA.sol hF1 hF' hFA.sol
  rw [ee] at hX1 hZ1
  have hK := Kmet_le_kapQ (r := r) hR1 hM0 (S := Sp r g y u) (caps := caps) (c5.trans (le_cp _))
    (c3.trans (le_cp _)) (c4'.trans (le_cp _))
  have hK2 := hK.trans hT.kmet
  have hz1 : InH ((1 : ℕ) : ℝ) (Fp r g y u) := by
    simpa using hFA.inH.mono (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨hzs, hzn⟩ := l2_zOf hz1 hFA.mean
  have hzn' : l2n (zOf 1 (Fp r g y u)) = e := by
    simp only [Nat.cast_one] at hzn
    exact hzn
  have hV := Q3_val_le (s := 1) (Or.inl rfl) hr (r * u) D hSA.mz hS' hzs (Fam.PiF_zOf hF')
  rw [hzn'] at hV
  have hKq : K3 |r| (wiener (Sp r g y u)) (hnorm 2 (Sp r g y u)) ≤ Kc caps / |r| ^ 2 := by
    have := clsS_mono (wiener_nonneg _) (hnorm_nonneg 2 _) (c5.trans (le_cp _)) (c4'.trans (le_cp _))
    simp only [K3, Kc]
    have h2 : 0 ≤ 2 ^ 37 / |r| ^ 2 := by positivity
    refine (mul_le_mul_of_nonneg_left this h2).trans (le_of_eq ?_)
    ring
  have hV2 : ‖(famQ 1 r D).val 1 r g y u‖ ≤ 1 / 2 ^ 24 * e ^ 2 :=
    hV.trans (mul_le_mul_of_nonneg_right (hKq.trans hT.K3) he2)
  have hvr := (Complex.abs_re_le_norm ((famQ 1 r D).val 1 r g y u)).trans hV2
  have e1 : (famX2 1 r).val 1 r g y u = X2Form 1 1 r (r * u) (Sp r g y u) (Sp r g y u)
      (zOf 1 (Fp r g y u)) (zOf 1 (Fp r g y u)) := famX2_form 1 r (r * u) _ _ _ _
  have e2 : (famZ 1 r).val 1 r g y u = ZForm 1 1 r (r * u) (Sp r g y u) (Sp r g y u)
      (zOf 1 (Fp r g y u)) (zOf 1 (Fp r g y u)) := famZ_form 1 r (r * u) _ _ _ _
  have hX2 : |((famX2 1 r).val 1 r g y u).re| ≤ X2St r R (Sp r g y u) * (e * e) :=
    (Complex.abs_re_le_norm _).trans (by rw [e1]; exact hX1)
  have hZ2 : |((famZ 1 r).val 1 r g y u).re| ≤ CZ / |r| * M * hnorm 2 (Sp r g y u) * (e * e) :=
    (Complex.abs_re_le_norm _).trans (by rw [e2]; exact hZ1)
  -- the sum
  have hc := c4_pos
  set b := hnorm 2 (Sp r g y u) with hb
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have ek : (2 ^ 8 * b * e ^ 2 / |r|) + (X2St r R (Sp r g y u) * (e * e)) +
      (CZ / |r| * M * b * (e * e)) ≤ Kmet r R M (Sp r g y u) * e ^ 2 := by
    have h1 : 2 ^ 8 * b / |r| ≤ 2 ^ 8 * (1 + c4) * b / |r| := by
      gcongr
      linarith only [hc]
    have h2 := mul_le_mul_of_nonneg_right h1 he2
    have e0 : Kmet r R M (Sp r g y u) * e ^ 2 = 2 ^ 8 * (1 + c4) * b / |r| * e ^ 2 +
        X2St r R (Sp r g y u) * (e * e) + CZ / |r| * M * b * (e * e) := by
      simp only [Kmet]
      ring
    have e3 : 2 ^ 8 * b * e ^ 2 / |r| = 2 ^ 8 * b / |r| * e ^ 2 := by ring
    rw [e0, e3]
    linarith only [h2]
  have hKe := mul_le_mul_of_nonneg_right hK2 he2
  set m := metricCorr r g y u + corrJ 1 r g y u + 2 * ((famQ 1 r D).val 1 r g y u).re +
    2 * C4 1 r g y u with hm
  have hmle : |m| ≤ 1 / 2 ^ 20 * e ^ 2 := by
    have a1 := abs_le.1 hm1
    have a2 := abs_le.1 hX2
    have a3 := abs_le.1 hZ2
    have a4 := abs_le.1 hvr
    have a5 := abs_le.1 q1
    have ee4 : eta41 = 1 / 2 ^ 23 := rfl
    rw [ee4] at a5
    simp only [hm, corrJ]
    rw [abs_le]
    constructor <;> linarith only [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2, ek,
      hKe, he2]
  have hcc : |2 * cubicCorr r g y u| ≤ 1 / 128 * e ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have : |cubicCorr r g y u| ≤ 1 / 256 * e ^ 2 := n1
    linarith
  have hE : 2 * En1 D r g y u = e ^ 2 + m + 2 * cubicCorr r g y u := by
    simp only [En1, h1Energy, hm]
    ring
  rw [hE]
  exact coercive_core' hmle hcc

end OVNS.Quant.Metric

end
