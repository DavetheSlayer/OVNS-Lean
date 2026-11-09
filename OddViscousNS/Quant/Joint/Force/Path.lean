import OddViscousNS.Quant.Joint.Force.Pairs
import OddViscousNS.Quant.Energy.H1.Bounds

/-!
# The force slots along the actual solution (step J5, node N12)

`Hf = Π_F H_ψ` is the fast force.  In the joint identities (`joint1RHS`, `joint2RHS`) it enters
through `fastNL = −Π_F Q(x, x) − Hf`: the direct term, the native differential `cubicD`, both slots
of `X₁` in `coreRHS`, and both slots of `X₂`, `Z` in `insJ`.  `force1`, `force2` are the sums of the
moduli of these slots: the ten paired slots of Bodies 40, 41, 45, 47, LOCAL363.

* `force2_le`: at an `H³` time, `force2 ≤ (1 + 48 c₄ a_F + X₁ + 2 X₂ + 2 Z) ‖Hf‖₁ c_F`;
* `force1_le`: at every time, `force1 ≤ (1 + κ) ‖Hf‖₁ b_F + 24 c₄ ‖Hf‖₁ a_F²`.
The first is LOCAL363's `g(t) c_F`.  In the second `κ` is the operator norm of the metric, and the
last term is the tested force `q_force = 64 P_F² h` of Bodies 15, 45.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open GN (SupBd)

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}

/-- The fast force `H_{ψ,F}`. -/
def Hf (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : Field := PiF (Hpsi r g y u)

lemma PiF_Hf (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    PiF (Hf r g y u) = Hf r g y u := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [Hf, PiF, hk]

/-- `Hpsi` is real, solenoidal and mean zero. -/
lemma Hpsi_facts (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    IsReal (Hpsi r g y u) ∧ IsSolenoidal (Hpsi r g y u) ∧ Hpsi r g y u 0 = 0 := by
  have hy := h.sol.adm u hu huT
  have hx := actual_adm h hu huT
  have hM := majorized_Qphase (r * u)
  have r1 := hM.real 0 _ _ hy hy
  have r2 := hM.real 0 _ _ hx hx
  have s1 := hM.sol 0 _ _ hy.mz hy.mz
  have s2 := hM.sol 0 _ _ hx.mz hx.mz
  have m1 := hM.mean 0 _ _ hy.mz hy.mz
  have m2 := hM.mean 0 _ _ hx.mz hx.mz
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · have e : ∀ k, Hpsi r g y u k = Qphase (r * u) (y u) (y u) k -
        Qphase (r * u) (actual r g y u) (actual r g y u) k := fun _ => rfl
    rw [e, e, r1 k, r2 k]
    ext i
    simp [conjV]
  · have e : Hpsi r g y u k = Qphase (r * u) (y u) (y u) k +
        (-1 : ℂ) • Qphase (r * u) (actual r g y u) (actual r g y u) k := by
      rw [neg_one_smul, ← sub_eq_add_neg]
      rfl
    rw [e, dotM_add, dotM_smul, s1 k, s2 k]
    simp
  · simp only [Hpsi, Pi.sub_apply]
    rw [m1, m2, sub_zero]

/-- `Hf` is real, solenoidal and mean zero. -/
lemma Hf_facts (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    IsReal (Hf r g y u) ∧ IsSolenoidal (Hf r g y u) ∧ Hf r g y u 0 = 0 := by
  obtain ⟨h1, h2, h3⟩ := Hpsi_facts h hu huT
  refine ⟨h1.PiF', fun k => ?_, ?_⟩
  · by_cases hk : k 2 = 0
    · simp [Hf, PiF, hk, dotM]
    · simpa [Hf, PiF, hk] using h2 k
  · simp [Hf, PiF]

/-- `H¹` regularity of `Hf`, with the bound of LOCAL363. -/
lemma Hf_one (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    MZ 1 (Hf r g y u) ∧ hnorm 1 (Hf r g y u) ≤
      32 * c4 * φ / |r| * (slowNorm 2 r g y u + fastNorm 2 r g y u) + 32 * c4 * φ ^ 2 / r ^ 2 := by
  obtain ⟨hI, hle⟩ := hnorm_one_Hpsi_le h hr hu huT
  exact ⟨⟨hI.PiF, (Hf_facts h hu huT).2.2⟩, (hnorm_PiF_le hI).trans hle⟩

/-! ### The slots -/

/-- **The force slots at weight two.** -/
def force2 (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  |pair 2 (Fp r g y u) (Hpsi r g y u)| +
    |cubicD 2 (-1) r (r * u) (Fp r g y u) (Hf r g y u)| +
    |2 * pair 2 (Fp r g y u) (X1op r (r * u) (Sp r g y u) (Hf r g y u)) +
      2 * pair 2 (Hf r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u))| +
    ‖X2Form 1 2 r (r * u) (Sp r g y u) (Sp r g y u) (zOf 2 (Hf r g y u)) (zp 2 r g y u)‖ +
    ‖X2Form 1 2 r (r * u) (Sp r g y u) (Sp r g y u) (zp 2 r g y u) (zOf 2 (Hf r g y u))‖ +
    ‖ZForm 1 2 r (r * u) (Sp r g y u) (Sp r g y u) (zOf 2 (Hf r g y u)) (zp 2 r g y u)‖ +
    ‖ZForm 1 2 r (r * u) (Sp r g y u) (Sp r g y u) (zp 2 r g y u) (zOf 2 (Hf r g y u))‖

/-- **The force slots at weight one.** -/
def force1 (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  |pair 1 (Fp r g y u) (Hpsi r g y u)| +
    |cubicD 1 (-1) r (r * u) (Fp r g y u) (Hf r g y u)| +
    |2 * pair 1 (Fp r g y u) (X1op r (r * u) (Sp r g y u) (Hf r g y u)) +
      2 * pair 1 (Hf r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u))| +
    ‖X2Form 1 1 r (r * u) (Sp r g y u) (Sp r g y u) (zOf 1 (Hf r g y u)) (zp 1 r g y u)‖ +
    ‖X2Form 1 1 r (r * u) (Sp r g y u) (Sp r g y u) (zp 1 r g y u) (zOf 1 (Hf r g y u))‖ +
    ‖ZForm 1 1 r (r * u) (Sp r g y u) (Sp r g y u) (zOf 1 (Hf r g y u)) (zp 1 r g y u)‖ +
    ‖ZForm 1 1 r (r * u) (Sp r g y u) (Sp r g y u) (zp 1 r g y u) (zOf 1 (Hf r g y u))‖

/-! ### Nonnegativity of the coefficients -/

lemma slowSup_nonneg : 0 ≤ slowSup r g y u :=
  Real.iSup_nonneg fun _ => norm_nonneg _

lemma X1Cf_nonneg (r : ℝ) (S : Field) : 0 ≤ X1Cf r S := by
  have h1 := Real.sqrt_nonneg |r|
  have h2 := hnorm_nonneg 2 S
  have h3 := hnorm_nonneg 3 S
  have hc := c4_pos
  have h4 := Real.sqrt_nonneg (17 : ℝ)
  have h5 := abs_nonneg r
  unfold X1Cf
  positivity

lemma X2Lo_nonneg (r : ℝ) {D : ℝ} (hD : 1 ≤ D) (f g : Field) : 0 ≤ X2Lo r D f g := by
  have h1 := wiener_nonneg f
  have h2 := wiener_nonneg g
  have h3 := hnorm_nonneg 1 f
  have h4 := hnorm_nonneg 1 g
  have h5 := hnorm_nonneg 2 f
  have h6 := hnorm_nonneg 2 g
  have hL := Real.log_nonneg hD
  have hc := c4_pos
  have h7 := abs_nonneg r
  have hD0 : 0 ≤ D := by linarith
  unfold X2Lo cls2
  positivity

lemma X2Cf_nonneg (r : ℝ) {D : ℝ} (hD : 1 ≤ D) (S : Field) : 0 ≤ X2Cf r D S := by
  have h1 := X2Lo_nonneg r hD S S
  have h2 := hnorm_nonneg 2 S
  have h3 := tailB_nonneg D S
  have h4 := Cm2_pos
  have h5 := abs_nonneg r
  unfold X2Cf
  positivity

lemma ZCf_nonneg {r M : ℝ} (hr : 1 ≤ |r|) (hM : 0 ≤ M) (S : Field) : 0 ≤ ZCf r M S := by
  have h1 := CZh_pos
  have h2 := hnorm_nonneg 2 S
  have h3 := Real.log_nonneg hr
  have h4 := abs_nonneg r
  unfold ZCf
  positivity

lemma X2St_nonneg (r : ℝ) {D : ℝ} (hD : 1 ≤ D) (S : Field) : 0 ≤ X2St r D S := by
  have h1 := wiener_nonneg S
  have h3 := hnorm_nonneg 1 S
  have h5 := hnorm_nonneg 2 S
  have h7 := abs_nonneg r
  have h8 : 0 ≤ Cst := by unfold Cst; positivity
  have h9 := Real.sqrt_nonneg (1 + Real.log D)
  have hD0 : 0 ≤ D := by linarith
  unfold X2St
  positivity

/-! ### The bounds -/

private lemma sum_two {x1 x2 x3 x4 x5 x6 x7 h b c K X1 X2 Z : ℝ} (hh : 0 ≤ h) (hbc : b ≤ c)
    (hX1 : 0 ≤ X1) (hX2 : 0 ≤ X2) (hZ : 0 ≤ Z) (t1 : x1 ≤ h * c) (t2 : x2 ≤ K * (h * c))
    (t3 : x3 ≤ X1 * (h * b)) (t4 : x4 ≤ X2 * (h * b)) (t5 : x5 ≤ X2 * (h * b))
    (t6 : x6 ≤ Z * (h * b)) (t7 : x7 ≤ Z * (h * b)) :
    x1 + x2 + x3 + x4 + x5 + x6 + x7 ≤ (1 + K + X1 + 2 * X2 + 2 * Z) * (h * c) := by
  have hm : h * b ≤ h * c := mul_le_mul_of_nonneg_left hbc hh
  have m1 := mul_le_mul_of_nonneg_left hm hX1
  have m2 := mul_le_mul_of_nonneg_left hm hX2
  have m3 := mul_le_mul_of_nonneg_left hm hZ
  linarith

/-- **The ten pairs at weight two**, at an `H³` time: LOCAL363's coefficient
`g = [1 + C a_F + X₁ + X₂ + Z] ‖H_{ψ,F}‖₁` of `c_F`.  Body 16's `384 P_F` is `48 c₄ a_F`. -/
theorem force2_le (h : ActualSol μ φ r g y Ty) (hr1 : 1 ≤ |r|) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u)) {D M : ℝ}
    (hD : 1 ≤ D) (hM : slowSup r g y u ≤ M) (hW : wiener (Sp r g y u) ≤ |r|) :
    force2 r g y u ≤ (1 + 48 * c4 * fastNorm 1 r g y u + X1Cf r (Sp r g y u) +
      2 * X2Cf r D (Sp r g y u) + 2 * ZCf r M (Sp r g y u)) *
        (hnorm 1 (Hf r g y u) * fastNorm 3 r g y u) := by
  have hq : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hq
  have hx := actual_adm h hu huT
  have hSA : Adm 2 (Sp r g y u) := hx.PiS
  have hFA : Adm 2 (Fp r g y u) := hx.PiF
  have hS' := Fam.PiS_Sp r g y u
  have hF' := Fam.PiF_Fp r g y u
  obtain ⟨hHr, hHs, hH0⟩ := Hf_facts h hu huT
  obtain ⟨hH1, -⟩ := Hf_one h hr hu huT
  have hHI := (hnorm_two_Hpsi_J h hr hu huT hF3 hS3).1
  have hH2 : MZ 2 (Hf r g y u) := ⟨hHI.PiF, hH0⟩
  have hH' := PiF_Hf r g y u
  have hSM3 : MZ 3 (Sp r g y u) := ⟨hS3, hSA.mean⟩
  have hFM3 : MZ 3 (Fp r g y u) := ⟨hF3, hFA.mean⟩
  have hM0 : 0 ≤ M := slowSup_nonneg.trans hM
  have hSup : SupBd (Sp r g y u) M := GN.supBd_slowSup hSA.inH hM
  have hbc : hnorm 2 (Fp r g y u) ≤ fastNorm 3 r g y u := hnorm_mono (by norm_num) hF3
  have hh0 := hnorm_nonneg 1 (Hf r g y u)
  have t1 : |pair 2 (Fp r g y u) (Hpsi r g y u)| ≤
      hnorm 1 (Hf r g y u) * fastNorm 3 r g y u := by
    have e : pair 2 (Fp r g y u) (Hpsi r g y u) = pair 2 (Fp r g y u) (Hf r g y u) :=
      (pair_PiF_right 2 hF' _).symm
    rw [e]
    have hF1 : InH (2 + 1) (Fp r g y u) := by
      rw [show (2 : ℝ) + 1 = 3 by norm_num]
      exact hF3
    have hHI1 : InH (2 - 1) (Hf r g y u) := by
      rw [show (2 : ℝ) - 1 = 1 by norm_num]
      exact hH1.inH
    have := (pair_le hF1 hHI1).2
    rw [show (2 : ℝ) + 1 = 3 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num] at this
    rw [mul_comm]
    exact this
  have t2 : |cubicD 2 (-1) r (r * u) (Fp r g y u) (Hf r g y u)| ≤
      48 * c4 * fastNorm 1 r g y u * (hnorm 1 (Hf r g y u) * fastNorm 3 r g y u) :=
    (cubicD_tame_two (ε := -1) (Or.inr rfl) r (r * u) hFM3 hH1).trans_eq (by
      simp only [fastNorm, Fp]
      ring)
  exact sum_two hh0 hbc (X1Cf_nonneg r _) (X2Cf_nonneg r hD _) (ZCf_nonneg hr1 hM0 _) t1 t2
    (two_X1 hr (r * u) hSM3 hS' hSA.real hFA.mz hH2 hH')
    (two_X2 hr (r * u) hD hSA.mz hS' hFA.mz hH1 hF')
    (two_X2' hr (r * u) hD hSA.mz hS' hSA.real hFA.mz hH1 hF')
    (two_Z hr1 (r * u) hSA hS' hSup hW hFA.mz hF' hFA.sol hH2 hH' hHs)
    (two_Z' hr1 (r * u) hSA hS' hSup hW hFA.mz hF' hFA.sol hH2 hH' hHs)

private lemma sum_one {x1 x2 x3 x4 x5 x6 x7 h a b T K1 K2 K3 : ℝ} (hh : 0 ≤ h) (hab : a ≤ b)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (t1 : x1 ≤ h * b) (t2 : x2 ≤ T)
    (t3 : x3 ≤ K1 * (h * a)) (t4 : x4 ≤ K2 * (h * a)) (t5 : x5 ≤ K2 * (h * a))
    (t6 : x6 ≤ K3 * (h * a)) (t7 : x7 ≤ K3 * (h * a)) :
    x1 + x2 + x3 + x4 + x5 + x6 + x7 ≤ (1 + (K1 + 2 * K2 + 2 * K3)) * (h * b) + T := by
  have hm : h * a ≤ h * b := mul_le_mul_of_nonneg_left hab hh
  have m1 := mul_le_mul_of_nonneg_left hm hK1
  have m2 := mul_le_mul_of_nonneg_left hm hK2
  have m3 := mul_le_mul_of_nonneg_left hm hK3
  linarith

/-- **The pairs at weight one**: at every time. -/
theorem force1_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) {D M : ℝ} (hD : 1 ≤ D) (hM : slowSup r g y u ≤ M) :
    force1 r g y u ≤ (1 + (2 ^ 8 * hnorm 2 (Sp r g y u) / |r| + 2 * X2St r D (Sp r g y u) +
        2 * (CZ / |r| * M * hnorm 2 (Sp r g y u)))) *
        (hnorm 1 (Hf r g y u) * fastNorm 2 r g y u) +
      24 * c4 * hnorm 1 (Hf r g y u) * fastNorm 1 r g y u ^ 2 := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hx := actual_adm h hu huT
  have hSA : Adm 2 (Sp r g y u) := hx.PiS
  have hFA : Adm 2 (Fp r g y u) := hx.PiF
  have hS' := Fam.PiS_Sp r g y u
  have hF' := Fam.PiF_Fp r g y u
  obtain ⟨hHr, hHs, hH0⟩ := Hf_facts h hu huT
  obtain ⟨hH1, -⟩ := Hf_one h hr hu huT
  have hH' := PiF_Hf r g y u
  have hF1 : MZ 1 (Fp r g y u) := hFA.mz.mono' (by norm_num)
  have hM0 : 0 ≤ M := slowSup_nonneg.trans hM
  have hSup : SupBd (Sp r g y u) M := GN.supBd_slowSup hSA.inH hM
  have hb0 := hnorm_nonneg 2 (Fp r g y u)
  have hS0 := hnorm_nonneg 2 (Sp r g y u)
  have hab : hnorm 1 (Fp r g y u) ≤ fastNorm 2 r g y u := hnorm_mono (by norm_num) hFA.inH
  have hh0 := hnorm_nonneg 1 (Hf r g y u)
  have t1 : |pair 1 (Fp r g y u) (Hpsi r g y u)| ≤
      hnorm 1 (Hf r g y u) * fastNorm 2 r g y u := by
    have e : pair 1 (Fp r g y u) (Hpsi r g y u) = pair 1 (Fp r g y u) (Hf r g y u) :=
      (pair_PiF_right 1 hF' _).symm
    rw [e]
    have hF2 : InH (1 + 1) (Fp r g y u) := by
      rw [show (1 : ℝ) + 1 = 2 by norm_num]
      exact hFA.inH
    have hHI1 : InH (1 - 1) (Hf r g y u) := by
      rw [show (1 : ℝ) - 1 = 0 by norm_num]
      exact hH1.inH.mono (by norm_num)
    have := (pair_le hF2 hHI1).2
    rw [show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num] at this
    have h0 : hnorm 0 (Hf r g y u) ≤ hnorm 1 (Hf r g y u) := hnorm_mono (by norm_num) hH1.inH
    calc _ ≤ hnorm 2 (Fp r g y u) * hnorm 0 (Hf r g y u) := this
      _ ≤ hnorm 2 (Fp r g y u) * hnorm 1 (Hf r g y u) := mul_le_mul_of_nonneg_left h0 hb0
      _ = _ := mul_comm _ _
  have t2 := cubicD_tame_one (ε := -1) (Or.inr rfl) r (r * u) hF1 hH1
  have t3 : |2 * pair 1 (Fp r g y u) (X1op r (r * u) (Sp r g y u) (Hf r g y u)) +
      2 * pair 1 (Hf r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u))| ≤
      2 ^ 8 * hnorm 2 (Sp r g y u) / |r| *
        (hnorm 1 (Hf r g y u) * hnorm 1 (Fp r g y u)) := by
    have := X1bil_le hr (r * u) hSA.mz hSA.real hS' hFA.mz hF' hH1 hH'
    unfold X1bil at this
    rw [add_comm] at this
    exact this.trans_eq (by ring)
  obtain ⟨t4, t5⟩ := one_X2 hr (r * u) hD hSA.mz hS' hF1 hH1 hF' hH'
  obtain ⟨t6, t7⟩ := one_Z hr (r * u) hSA hS' hSup hF1 hF' hFA.sol hH1 hH' hHs
  have hZ0 : 0 ≤ CZ / |r| * M * hnorm 2 (Sp r g y u) := by
    have : 0 ≤ CZ := by
      have := Ce_pos
      unfold CZ
      positivity
    positivity
  exact sum_one hh0 hab (by positivity) (X2St_nonneg r hD _) hZ0 t1 t2 t3 t4 t5 t6 t7

end OVNS.Quant.Metric

end
