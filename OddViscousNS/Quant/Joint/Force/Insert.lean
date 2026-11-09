import OddViscousNS.Quant.Joint.Force.H0Degree

/-!
# The full metric–`Q` insertion (step J5, node N12)

`FORCE_AND_JOINT_PAYMENTS_V2.md` §15.  With `N_Q = −Π_F Q(F, F)` (`NQp_pure`):
* `Q_sizes`: `(15.1)`, `‖Q(F, F)‖₁ ≤ C √a b^{3/2}`, `‖Q(F, F)‖₂ ≤ C √(a b) c`;
* `NQp_one_le`, `NQp_two_le`: the form used here, `‖N_Q‖₁ ≤ 8 c₄ b²`, `‖N_Q‖₂ ≤ 16 c₄ b c`, from
  `‖F̂‖_{ℓ¹} ≤ c₄ b`.  `(15.2)` does not need the interpolation: it only needs `b² ≤ a c`;
* `metS`: `Re⟨(X₁ + X₂ + Z) z, A^{s/2} H⟩` as it stands in the right sides, for a direction `H`;
* `metS_one_le`, `metS_two_le`: `|metS s H| ≤ K ‖H‖_s e_s`, `K` the operator norm `Kmet`;
* `metQ_one_le`, `metQ_two_le`: `(15.2)`, `|metQ 1| ≤ 8 c₄ K a b²`, `|metQ 2| ≤ 16 c₄ K a c²`.

**How `rowStatic` absorbs it.**  `staticQ D M` is the threshold of `P_F K`, and `Pkap_le` says that
`C staticQ ≤ q` gives `P_F K ≤ 2/C`.  At `D = R`, `staticQ_le_rowStatic`:
`staticQ R M ≤ CsQ rowStatic`, term by term: `P_F B` is below `P_F M b` (`M ≥ 1`), the logarithm
`1 + √L ≤ 2 L`, the heat root is `√Cst` times `√(P R a b)`.  So `q ≥ C CsQ rowStatic` pays the whole
insertion, with no further row: `metQ_joint`.  `deg_staticQ`: degree `(1, 3)`, tied at `U R³`, as
printed.

`joint1T`, `joint2T`: the right sides without force, `h₀` and `metQ`: what is left is the bracket
`−½⟨z, T_s z⟩` of `(2.5)` and the proper terms.  `ae_joint_final`: the four parts, a.e.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (Qm_two_le ae_inH3_split cubicHeat2)

noncomputable section

namespace OVNS.Quant.Metric

open GN (SupBd)

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}

/-! ### `(15.1)` -/

/-- **`(15.1)`** -/
theorem Q_sizes : ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (F : Field), (MZ 2 F → hnorm 1 (Qphase τ F F) ≤
      C * Real.sqrt (hnorm 1 F * hnorm 2 F) * hnorm 2 F) ∧
    (MZ 3 F → hnorm 2 (Qphase τ F F) ≤
      C * Real.sqrt (hnorm 1 F * hnorm 2 F) * hnorm 3 F) := by
  obtain ⟨cI, hc, hw⟩ := exists_wiener_interp
  refine ⟨16 * cI, by positivity, fun τ F => ⟨fun hF => ?_, fun hF => ?_⟩⟩
  · have h1 := (hnorm_one_Qm_le (phaseM_bdd τ) hF hF).2
    have h2 := hw F hF
    have hb := hnorm_nonneg 2 F
    have h3 := mul_le_mul_of_nonneg_right h2 hb
    have hs := mul_nonneg (mul_nonneg hc.le (Real.sqrt_nonneg (hnorm 1 F * hnorm 2 F))) hb
    have e : Qphase τ F F = Qm (phaseM τ) F F := rfl
    rw [e]
    nlinarith only [h1, h3, hs]
  · have hF2 : MZ 2 F := hF.mono' (by norm_num)
    have h1 := (Qm_two_le (phaseM_bdd τ) hF hF).2
    have h2 := hw F hF2
    have hd := hnorm_nonneg 3 F
    have h3 := mul_le_mul_of_nonneg_right h2 hd
    have hs := mul_nonneg (mul_nonneg hc.le (Real.sqrt_nonneg (hnorm 1 F * hnorm 2 F))) hd
    have e : Qphase τ F F = Qm (phaseM τ) F F := rfl
    rw [e]
    nlinarith only [h1, h3, hs]

/-- `N_Q` is a real solenoidal fast field. -/
theorem NQp_facts (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    IsReal (NQp r g y u) ∧ IsSolenoidal (NQp r g y u) ∧ PiF (NQp r g y u) = NQp r g y u ∧
      NQp r g y u 0 = 0 := by
  have hx := actual_adm h hu huT
  have hF : Adm 2 (Fp r g y u) := hx.PiF
  have hM := majorized_Qphase (r * u)
  have r1 : IsReal (Qphase (r * u) (Fp r g y u) (Fp r g y u)) := hM.real 0 _ _ hF hF
  have s1 := hM.sol 0 _ _ hF.mz hF.mz
  rw [NQp_pure hx]
  refine ⟨r1.PiF'.neg', fun k => ?_, ?_, by simp [PiF]⟩
  · by_cases hk : k 2 = 0
    · simp [PiF, hk, dotM]
    · have e : (-PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u))) k =
          (-1 : ℂ) • Qphase (r * u) (Fp r g y u) (Fp r g y u) k := by
        rw [Pi.neg_apply, PiF_apply_fast _ hk, neg_one_smul]
      rw [e, dotM_smul, s1 k, mul_zero]
  · funext k
    by_cases hk : k 2 = 0 <;> simp [PiF, hk]

/-- **`‖N_Q‖₁ ≤ 8 c₄ b²`**, at every time. -/
theorem NQp_one_le (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    MZ 1 (NQp r g y u) ∧ hnorm 1 (NQp r g y u) ≤ 8 * c4 * fastNorm 2 r g y u ^ 2 := by
  have hx := actual_adm h hu huT
  have hF : Adm 2 (Fp r g y u) := hx.PiF
  obtain ⟨iQ, bQ⟩ := hnorm_one_Qm_le (phaseM_bdd (r * u)) hF.mz hF.mz
  obtain ⟨-, -, -, h0⟩ := NQp_facts h hu huT
  have hb := hnorm_nonneg 2 (Fp r g y u)
  have hw := mul_le_mul_of_nonneg_right (wiener_le hF.mz) hb
  have e : NQp r g y u = -PiF (Qm (phaseM (r * u)) (Fp r g y u) (Fp r g y u)) := NQp_pure hx
  have e2 : fastNorm 2 r g y u = hnorm 2 (Fp r g y u) := rfl
  refine ⟨⟨by rw [e]; exact iQ.PiF.neg, h0⟩, ?_⟩
  rw [e, hnorm_neg, e2]
  refine (hnorm_PiF_le iQ).trans (bQ.trans ?_)
  nlinarith only [hw]

/-- **`‖N_Q‖₂ ≤ 16 c₄ b c`**, at an `H³` time. -/
theorem NQp_two_le (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty)
    (hF3 : InH 3 (Fp r g y u)) :
    MZ 2 (NQp r g y u) ∧
      hnorm 2 (NQp r g y u) ≤ 16 * c4 * (fastNorm 2 r g y u * fastNorm 3 r g y u) := by
  have hx := actual_adm h hu huT
  have hF : Adm 2 (Fp r g y u) := hx.PiF
  have hFM : MZ 3 (Fp r g y u) := ⟨hF3, hF.mean⟩
  obtain ⟨iQ, bQ⟩ := Qm_two_le (phaseM_bdd (r * u)) hFM hFM
  obtain ⟨-, -, -, h0⟩ := NQp_facts h hu huT
  have hd := hnorm_nonneg 3 (Fp r g y u)
  have hw := mul_le_mul_of_nonneg_right (wiener_le hF.mz) hd
  have e : NQp r g y u = -PiF (Qm (phaseM (r * u)) (Fp r g y u) (Fp r g y u)) := NQp_pure hx
  have e2 : fastNorm 2 r g y u = hnorm 2 (Fp r g y u) := rfl
  have e3 : fastNorm 3 r g y u = hnorm 3 (Fp r g y u) := rfl
  refine ⟨⟨by rw [e]; exact iQ.PiF.neg, h0⟩, ?_⟩
  rw [e, hnorm_neg, e2, e3]
  refine (hnorm_PiF_le iQ).trans (bQ.trans ?_)
  nlinarith only [hw]

/-! ### The static slots at weight two -/

section Static

variable {S F H : Field} {M : ℝ}

/-- The pair of `X₂` at weight two, by the operator norm. -/
theorem two_X2St (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 1 ≤ D) (hS : MZ 2 S) (hS' : PiS S = S)
    (hF : MZ 2 F) (hH : MZ 2 H) (hF' : PiF F = F) (hH' : PiF H = H) :
    ‖X2Form 1 2 r τ S S (zOf 2 H) (zOf 2 F)‖ ≤ X2St r D S * (hnorm 2 H * hnorm 2 F) ∧
      ‖X2Form 1 2 r τ S S (zOf 2 F) (zOf 2 H)‖ ≤ X2St r D S * (hnorm 2 H * hnorm 2 F) := by
  have hH1 : InH ((2 : ℕ) : ℝ) H := by simpa using hH.inH
  have hF1 : InH ((2 : ℕ) : ℝ) F := by simpa using hF.inH
  obtain ⟨s1, n1⟩ := l2_zOf hH1 hH.mean
  obtain ⟨s2, n2⟩ := l2_zOf hF1 hF.mean
  have hz : PiF (zOf 2 F) = zOf 2 F := Fam.PiF_zOf hF'
  have hz1 : PiF (zOf 2 H) = zOf 2 H := Fam.PiF_zOf hH'
  have hμ : ∀ x : I3, ‖(1 : I3 → ℂ) x‖ ≤ 1 := fun x => by simp
  have h1 := X2Form_static_le (s := 2) (Or.inr rfl) hr τ hD hS hS' hS hS' s1 s2 hz hμ
  have h2 := X2Form_static_le (s := 2) (Or.inr rfl) hr τ hD hS hS' hS hS' s2 s1 hz1 hμ
  rw [n1, n2] at h1 h2
  have e : ∀ A B : ℝ, Cst / |r| * ((1 + Real.sqrt (1 + Real.log D)) *
      (hnorm 1 S * hnorm 1 S) + hnorm 1 S * wiener S + hnorm 1 S * wiener S +
        hnorm 2 S * hnorm 2 S / D) * (A * B) +
      Cst / |r| ^ 2 * D * (hnorm 1 S * hnorm 2 S) * (A * B) = X2St r D S * (A * B) := fun A B => by
    unfold X2St
    ring
  rw [e] at h1 h2
  simp only [Nat.cast_ofNat] at h1 h2
  exact ⟨h1, h2.trans_eq (by ring)⟩

/-- The pair of `Z` at weight two, by the operator norm. -/
theorem two_ZSt (hr : r ≠ 0) (τ : ℝ) (hS : Adm 2 S) (hS' : PiS S = S) (hM : SupBd S M)
    (hF : MZ 2 F) (hF' : PiF F = F) (hFs : IsSolenoidal F) (hH : MZ 2 H) (hH' : PiF H = H)
    (hHs : IsSolenoidal H) :
    ‖ZForm 1 2 r τ S S (zOf 2 H) (zOf 2 F)‖ ≤ CZ / |r| * M * hnorm 2 S * (hnorm 2 H * hnorm 2 F) ∧
      ‖ZForm 1 2 r τ S S (zOf 2 F) (zOf 2 H)‖ ≤
        CZ / |r| * M * hnorm 2 S * (hnorm 2 H * hnorm 2 F) := by
  have hH1 : InH ((2 : ℕ) : ℝ) H := by simpa using hH.inH
  have hF1 : InH ((2 : ℕ) : ℝ) F := by simpa using hF.inH
  obtain ⟨s1, n1⟩ := l2_zOf hH1 hH.mean
  obtain ⟨s2, n2⟩ := l2_zOf hF1 hF.mean
  have hz : PiF (zOf 2 F) = zOf 2 F := Fam.PiF_zOf hF'
  have hz1 : PiF (zOf 2 H) = zOf 2 H := Fam.PiF_zOf hH'
  have h1 := ZForm_le (s := 2) (Or.inr rfl) hr τ hS hS' hM s1 hz1 s2 hz
    (leray_zOf hHs hH.mean · 2) (leray_zOf hFs hF.mean · 2)
  have h2 := ZForm_le (s := 2) (Or.inr rfl) hr τ hS hS' hM s2 hz s1 hz1
    (leray_zOf hFs hF.mean · 2) (leray_zOf hHs hH.mean · 2)
  rw [n1, n2] at h1 h2
  simp only [Nat.cast_ofNat] at h1 h2
  exact ⟨h1, h2.trans_eq (by ring)⟩

end Static

/-! ### The metric slots of a direction -/

/-- **The metric slots of a fast direction**, as they stand in the right sides. -/
def metS (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) (H : Field) : ℝ :=
  2 * (pair s (Fp r g y u) (X1op r (r * u) (Sp r g y u) H) +
      pair s H (X1op r (r * u) (Sp r g y u) (Fp r g y u))) +
    1 / 2 * (X2Form 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zOf s H) (zp s r g y u) +
      X2Form 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zOf s H)).re +
    1 / 2 * (ZForm 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zOf s H) (zp s r g y u) +
      ZForm 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zOf s H)).re

/-- The operator norm of the metric, on the slots. -/
def Kmet (r D M : ℝ) (S : Field) : ℝ :=
  2 ^ 8 * (1 + c4) * hnorm 2 S / |r| + X2St r D S + CZ / |r| * M * hnorm 2 S

private lemma met_triangle {c K₁ K₂ K₃ x : ℝ} {x₁ x₂ x₃ x₄ : ℂ} (hc : |c| ≤ K₁ * x)
    (h1 : ‖x₁‖ ≤ K₂ * x) (h2 : ‖x₂‖ ≤ K₂ * x) (h3 : ‖x₃‖ ≤ K₃ * x) (h4 : ‖x₄‖ ≤ K₃ * x) :
    |c + 1 / 2 * (x₁ + x₂).re + 1 / 2 * (x₃ + x₄).re| ≤ (K₁ + K₂ + K₃) * x := by
  have a1 := abs_le.1 ((Complex.abs_re_le_norm x₁).trans h1)
  have a2 := abs_le.1 ((Complex.abs_re_le_norm x₂).trans h2)
  have a3 := abs_le.1 ((Complex.abs_re_le_norm x₃).trans h3)
  have a4 := abs_le.1 ((Complex.abs_re_le_norm x₄).trans h4)
  have a0 := abs_le.1 hc
  rw [Complex.add_re, Complex.add_re, abs_le]
  constructor <;> nlinarith only [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

/-- **The metric slots at weight one**, at every time. -/
theorem metS_one_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) {D M : ℝ} {H : Field} (hD : 1 ≤ D) (hM : slowSup r g y u ≤ M)
    (hH : MZ 1 H) (hH' : PiF H = H) (hHs : IsSolenoidal H) :
    |metS 1 r g y u H| ≤ Kmet r D M (Sp r g y u) * (hnorm 1 H * hnorm 1 (Fp r g y u)) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hx := actual_adm h hu huT
  have hSA : Adm 2 (Sp r g y u) := hx.PiS
  have hFA : Adm 2 (Fp r g y u) := hx.PiF
  have hS' := Fam.PiS_Sp r g y u
  have hF' := Fam.PiF_Fp r g y u
  have hF1 : MZ 1 (Fp r g y u) := hFA.mz.mono' (by norm_num)
  have hSup : SupBd (Sp r g y u) M := GN.supBd_slowSup hSA.inH hM
  have hc := c4_pos
  have hb := hnorm_nonneg 2 (Sp r g y u)
  have hH0 := hnorm_nonneg 1 H
  have hF0 := hnorm_nonneg 1 (Fp r g y u)
  have t3 := X1bil_le hr (r * u) hSA.mz hSA.real hS' hFA.mz hF' hH hH'
  obtain ⟨t4, t5⟩ := one_X2 hr (r * u) hD hSA.mz hS' hF1 hH hF' hH'
  obtain ⟨t6, t7⟩ := one_Z hr (r * u) hSA hS' hSup hF1 hF' hFA.sol hH hH' hHs
  have c1 : |2 * (pair 1 (Fp r g y u) (X1op r (r * u) (Sp r g y u) H) +
      pair 1 H (X1op r (r * u) (Sp r g y u) (Fp r g y u)))| ≤
      2 ^ 8 * (1 + c4) * hnorm 2 (Sp r g y u) / |r| * (hnorm 1 H * hnorm 1 (Fp r g y u)) := by
    have e : 2 * (pair 1 (Fp r g y u) (X1op r (r * u) (Sp r g y u) H) +
        pair 1 H (X1op r (r * u) (Sp r g y u) (Fp r g y u))) =
        X1bil r (r * u) (Sp r g y u) (Fp r g y u) H := by
      unfold X1bil
      ring
    rw [e]
    refine t3.trans ?_
    have hm : 0 ≤ hnorm 2 (Sp r g y u) * hnorm 1 (Fp r g y u) * hnorm 1 H / |r| := by positivity
    have e2 : 2 ^ 8 * hnorm 2 (Sp r g y u) * hnorm 1 (Fp r g y u) * hnorm 1 H / |r| =
        2 ^ 8 * (hnorm 2 (Sp r g y u) * hnorm 1 (Fp r g y u) * hnorm 1 H / |r|) := by ring
    have e3 : 2 ^ 8 * (1 + c4) * hnorm 2 (Sp r g y u) / |r| * (hnorm 1 H * hnorm 1 (Fp r g y u)) =
        2 ^ 8 * (1 + c4) * (hnorm 2 (Sp r g y u) * hnorm 1 (Fp r g y u) * hnorm 1 H / |r|) := by
      ring
    rw [e2, e3]
    nlinarith only [hm, hc]
  unfold metS Kmet
  simp only [Nat.cast_one]
  exact met_triangle c1 t4 t5 t6 t7

/-- **The metric slots at weight two**, for an `H²` direction. -/
theorem metS_two_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) {D M : ℝ} {H : Field} (hD : 1 ≤ D) (hM : slowSup r g y u ≤ M)
    (hH : MZ 2 H) (hH' : PiF H = H) (hHr : IsReal H) (hHs : IsSolenoidal H) :
    |metS 2 r g y u H| ≤ Kmet r D M (Sp r g y u) * (hnorm 2 H * hnorm 2 (Fp r g y u)) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hx := actual_adm h hu huT
  have hSA : Adm 2 (Sp r g y u) := hx.PiS
  have hFA : Adm 2 (Fp r g y u) := hx.PiF
  have hS' := Fam.PiS_Sp r g y u
  have hF' := Fam.PiF_Fp r g y u
  have hSup : SupBd (Sp r g y u) M := GN.supBd_slowSup hSA.inH hM
  have hc := c4_pos
  have hb := hnorm_nonneg 2 (Sp r g y u)
  have hH0 := hnorm_nonneg 2 H
  have hF0 := hnorm_nonneg 2 (Fp r g y u)
  have t3 := H2.metBil2_le hr (r * u) hSA.mz hS' hFA.mz hF' hFA.real hH hHr
  obtain ⟨t4, t5⟩ := two_X2St hr (r * u) hD hSA.mz hS' hFA.mz hH hF' hH'
  obtain ⟨t6, t7⟩ := two_ZSt hr (r * u) hSA hS' hSup hFA.mz hF' hFA.sol hH hH' hHs
  have c1 : |2 * (pair 2 (Fp r g y u) (X1op r (r * u) (Sp r g y u) H) +
      pair 2 H (X1op r (r * u) (Sp r g y u) (Fp r g y u)))| ≤
      2 ^ 8 * (1 + c4) * hnorm 2 (Sp r g y u) / |r| * (hnorm 2 H * hnorm 2 (Fp r g y u)) := by
    have e : 2 * (pair 2 (Fp r g y u) (X1op r (r * u) (Sp r g y u) H) +
        pair 2 H (X1op r (r * u) (Sp r g y u) (Fp r g y u))) =
        H2.metBil2 r (r * u) (Sp r g y u) (Fp r g y u) H := by
      unfold H2.metBil2
      ring
    rw [e]
    refine t3.trans ?_
    have hm : 0 ≤ hnorm 2 (Sp r g y u) * hnorm 2 (Fp r g y u) * hnorm 2 H / |r| := by positivity
    have e2 : H2.cBil * hnorm 2 (Sp r g y u) * hnorm 2 (Fp r g y u) * hnorm 2 H / |r| =
        2 ^ 8 * c4 * (hnorm 2 (Sp r g y u) * hnorm 2 (Fp r g y u) * hnorm 2 H / |r|) := by
      unfold H2.cBil
      ring
    have e3 : 2 ^ 8 * (1 + c4) * hnorm 2 (Sp r g y u) / |r| * (hnorm 2 H * hnorm 2 (Fp r g y u)) =
        2 ^ 8 * (1 + c4) * (hnorm 2 (Sp r g y u) * hnorm 2 (Fp r g y u) * hnorm 2 H / |r|) := by
      ring
    rw [e2, e3]
    nlinarith only [hm]
  unfold metS Kmet
  simp only [Nat.cast_ofNat]
  exact met_triangle c1 t4 t5 t6 t7

/-! ### `(15.2)` -/

/-- `Re⟨(X₁ + X₂ + Z) z, A^{s/2} N_Q⟩`. -/
def metQ (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ := metS s r g y u (NQp r g y u)

lemma Kmet_nonneg (r : ℝ) {D M : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M) (S : Field) : 0 ≤ Kmet r D M S := by
  have h1 := X2St_nonneg r hD S
  have h2 := hnorm_nonneg 2 S
  have h3 := CZ_nonneg
  have h4 := abs_nonneg r
  have h5 := c4_pos
  unfold Kmet
  positivity

/-- **`(15.2)` at weight one.** -/
theorem metQ_one_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) {D M : ℝ} (hD : 1 ≤ D) (hM : slowSup r g y u ≤ M) :
    |metQ 1 r g y u| ≤ 8 * c4 * Kmet r D M (Sp r g y u) * fastNorm 1 r g y u *
      fastNorm 2 r g y u ^ 2 := by
  obtain ⟨hm, hb⟩ := NQp_one_le h hu huT
  obtain ⟨-, hs, hf, -⟩ := NQp_facts h hu huT
  have hM0 : 0 ≤ M := slowSup_nonneg.trans hM
  have hK := Kmet_nonneg r hD hM0 (Sp r g y u)
  have ha : 0 ≤ hnorm 1 (Fp r g y u) := hnorm_nonneg _ _
  refine (metS_one_le h hr hu huT hD hM hm hf hs).trans ?_
  have h1 := mul_le_mul_of_nonneg_right hb ha
  have h2 := mul_le_mul_of_nonneg_left h1 hK
  have e1 : fastNorm 1 r g y u = hnorm 1 (Fp r g y u) := rfl
  rw [e1]
  nlinarith only [h2]

/-- **`(15.2)` at weight two**, at an `H³` time. -/
theorem metQ_two_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) {D M : ℝ} (hD : 1 ≤ D)
    (hM : slowSup r g y u ≤ M) :
    |metQ 2 r g y u| ≤ 16 * c4 * Kmet r D M (Sp r g y u) * fastNorm 1 r g y u *
      fastNorm 3 r g y u ^ 2 := by
  obtain ⟨hm, hb⟩ := NQp_two_le h hu huT hF3
  obtain ⟨hr1, hs, hf, -⟩ := NQp_facts h hu huT
  have hM0 : 0 ≤ M := slowSup_nonneg.trans hM
  have hK := Kmet_nonneg r hD hM0 (Sp r g y u)
  have hb0 : 0 ≤ hnorm 2 (Fp r g y u) := hnorm_nonneg _ _
  have hc0 : 0 ≤ hnorm 3 (Fp r g y u) := hnorm_nonneg _ _
  refine (metS_two_le h hr hu huT hD hM hm hf hr1 hs).trans ?_
  have h1 := mul_le_mul_of_nonneg_right hb hb0
  have h2 := mul_le_mul_of_nonneg_left h1 hK
  have hbs : hnorm 2 (Fp r g y u) ^ 2 ≤ hnorm 1 (Fp r g y u) * hnorm 3 (Fp r g y u) := by
    have hF3' : InH (2 + 1) (Fp r g y u) := by
      rw [show (2 : ℝ) + 1 = 3 by norm_num]
      exact hF3
    have := hnorm_sq_le_mul (s := 2) hF3'
    rwa [show (2 : ℝ) - 1 = 1 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num] at this
  have hc := c4_pos
  have h3 : 0 ≤ 16 * c4 * Kmet r D M (Sp r g y u) * hnorm 3 (Fp r g y u) := by positivity
  have h4 := mul_le_mul_of_nonneg_left hbs h3
  have e1 : fastNorm 1 r g y u = hnorm 1 (Fp r g y u) := rfl
  have e2 : fastNorm 2 r g y u = hnorm 2 (Fp r g y u) := rfl
  have e3 : fastNorm 3 r g y u = hnorm 3 (Fp r g y u) := rfl
  rw [e2, e3] at h2
  rw [e1, e3]
  nlinarith only [h2, h4]

end OVNS.Quant.Metric

end
