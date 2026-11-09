import OddViscousNS.Quant.Joint.Quartic.Source

/-!
# The real scalar quartic `C_{4,s}` (step J5, node N11)

J3-v2 §3, `JOINT_ASSEMBLY_V4.md` §3: `E_s = e_s + E_s⁰ + C_{3,s} + C_{4,s}`, `W_s = 2E_s`, and
`C_{4,s}` is "the REAL SCALAR quartic of J3 at weight `s`": each coefficient `C` of the signed source
`J_s` replaced by `−C/(−Σ₄ + i r Ψ)`, "with its sign exactly as there".

The right side of the energy identity has `cubicD s (−1) r τ F N_F` (`h1RHS`, `h2RHS`), with `N_F`
carrying `−2 Q_hi` (`fastNL_split`).  So `J_s = J4 s = D_s^N(F; −2 Q_hi)`, whose coefficient is `−2
core`, and `−C/(−Σ₄ + i r Ψ) = 2 core/(−Σ₄ + i r Ψ)`: that is `C4 s = 2 Re val4 s` exactly, with no
operator form to halve:

* `C4_identity_two`, `C4_identity_one`: `C_{4,s}(b) − C_{4,s}(a) = ∫ (−J_s + Rem)`, `Rem4 = 2 Re rem4`;
* `nearD_fastNL_split`: `D_s^N(F; N_F) = J_s + D_s^N(F; N_rest)`: so in `E_s + C_{4,s}` the high mixed
  near term has gone, and the low mixed, purefast and filter directions stay, with the FAR part.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (ae_inH3_split)

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- **The real scalar quartic** of J3-v2 §3 at weight `j`. -/
def C4 (j : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ := 2 * (val4 j r g y u).re

/-- **The signed high source** `J_j`: the near differential in the high mixed part of `N_F`, with
the sign it has on the right of the energy identity. -/
def J4 (j : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  nearD j (-1) r (r * u) (Fp r g y u) (mixHi (r * u) (Sp r g y u) (Fp r g y u))

/-- **The four source insertions of `C_{4,j}`**. -/
def Rem4 (j : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ := 2 * (rem4 j r g y u).re

lemma isReal_Fp (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    IsReal (Fp r g y u) := (Fp_adm h hu huT).real

/-- The source against the signed source. -/
lemma two_src_eq {j : ℕ} (hj : j = 1 ∨ j = 2) (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hFm : MZ ((j : ℝ) + 1) (Fp r g y u))
    (hG : MZ j (Qhi (r * u) (Sp r g y u) (Fp r g y u)))
    (hs : Summable fun x : L4 => srcQ j r x (r * u) (Sp r g y u x.2.2) (Fp r g y u (inL x))
      (Fp r g y u x.2.1) (Fp r g y u (outE x))) :
    2 * (src4 j r g y u).re = -J4 j r g y u := by
  have hS := Sp_adm h hu huT
  have hF := Fp_adm h hu huT
  have e := src_eq_nearD hS (Fam.PiS_Sp r g y u) hF (PiF_Fp r g y u) hj hFm hG hs
  have hR := isReal_Qhi (r * u) hS hF
  have hA : MZ j (Qhi (r * u) (Sp r g y u) (Fp r g y u) + Qhi (r * u) (Sp r g y u) (Fp r g y u)) :=
    ⟨hG.inH.add hG.inH, by simp [hG.mean]⟩
  simp only [J4, mixHi, src4]
  rw [e, nearD_neg hj (Or.inr rfl) r _ hFm hF.real hA (IsReal.add'' hR hR),
    nearD_add hj (Or.inr rfl) r _ hFm hF.real hG hG hR hR]
  ring

/-- The scalar identity from the complex one. -/
lemma C4_of_identity {j : ℕ} {a b : ℝ} (hab : a ≤ b)
    (hI : IntervalIntegrable (fun u => src4 j r g y u + rem4 j r g y u) volume a b)
    (key : val4 j r g y b - val4 j r g y a = ∫ u in a..b, (src4 j r g y u + rem4 j r g y u))
    (hae : ∀ᵐ u ∂(volume.restrict (Icc a b)), 2 * (src4 j r g y u).re = -J4 j r g y u) :
    IntervalIntegrable (fun u => -J4 j r g y u + Rem4 j r g y u) volume a b ∧
      C4 j r g y b - C4 j r g y a = ∫ u in a..b, (-J4 j r g y u + Rem4 j r g y u) := by
  have hRe : IntervalIntegrable (fun u => 2 * (src4 j r g y u + rem4 j r g y u).re) volume a b := by
    have h1 : IntervalIntegrable (fun u => Complex.reCLM (src4 j r g y u + rem4 j r g y u))
        volume a b := ⟨Complex.reCLM.integrable_comp hI.1, Complex.reCLM.integrable_comp hI.2⟩
    exact h1.const_mul 2
  have hsplit : ∀ᵐ u, u ∈ uIoc a b → 2 * (src4 j r g y u + rem4 j r g y u).re =
      -J4 j r g y u + Rem4 j r g y u := by
    rw [uIoc_of_le hab]
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hae] with u hu hmem
    have := hu (Ioc_subset_Icc_self hmem)
    simp only [Complex.add_re, mul_add, Rem4]
    rw [this]
  refine ⟨?_, ?_⟩
  · refine hRe.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hsplit
  · have e1 : ∫ u in a..b, (-J4 j r g y u + Rem4 j r g y u) =
        ∫ u in a..b, 2 * (src4 j r g y u + rem4 j r g y u).re :=
      (intervalIntegral.integral_congr_ae hsplit).symm
    have e2 : ∫ u in a..b, (src4 j r g y u + rem4 j r g y u).re =
        (∫ u in a..b, (src4 j r g y u + rem4 j r g y u)).re :=
      Complex.reCLM.intervalIntegral_comp_comm hI
    rw [e1, intervalIntegral.integral_const_mul, e2, ← key]
    simp only [C4, Complex.sub_re]
    ring

/-- **The identity of `C_{4,2}`** (J3-v2 §3, §6). -/
theorem C4_identity_two (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (fun u => -J4 2 r g y u + Rem4 2 r g y u) volume a b ∧
      C4 2 r g y b - C4 2 r g y a = ∫ u in a..b, (-J4 2 r g y u + Rem4 2 r g y u) := by
  obtain ⟨hI, key⟩ := Q4_identity_two h hr ha hab hb
  refine C4_of_identity hab hI key ?_
  filter_upwards [ae_inH3_split h ha hab hb, ae_restrict_mem measurableSet_Icc] with u hu3 hu
  have hu0 := ha.trans hu.1
  have huT := lt_lifespan hu.2 hb
  have hS := Sp_adm h hu0 huT
  have hF := Fp_adm h hu0 huT
  have hLF := lhB_two hF.inH (PiF_Fp r g y u)
  have hF3 : MZ 3 (Fp r g y u) := ⟨hu3.1, hF.mean⟩
  have hS3 : MZ 3 (Sp r g y u) := ⟨hu3.2, hS.mean⟩
  have hsb := J2_sb r (slots_val r g y u) hS3 hLF hF.inH hF.inH (r * u)
  obtain ⟨iQ, -⟩ := hnorm_two_Qhi (r * u) hS3 (Fam.PiS_Sp r g y u) (l2_of_adm hF) hLF
  refine two_src_eq (j := 2) (Or.inr rfl) h hu0 huT ?_ ?_ hsb.1.of_norm
  · have e : (((2 : ℕ) : ℝ) + 1) = 3 := by norm_num
    rw [e]
    exact hF3
  · have e : (((2 : ℕ) : ℝ)) = 2 := by norm_num
    rw [e]
    exact ⟨iQ, Qhi_zero⟩

/-- **The identity of `C_{4,1}`** (J3-v2 §3, §6). -/
theorem C4_identity_one (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (fun u => -J4 1 r g y u + Rem4 1 r g y u) volume a b ∧
      C4 1 r g y b - C4 1 r g y a = ∫ u in a..b, (-J4 1 r g y u + Rem4 1 r g y u) := by
  obtain ⟨hI, key⟩ := Q4_identity_one h hr ha hab hb
  refine C4_of_identity hab hI key ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hu0 := ha.trans hu.1
  have huT := lt_lifespan hu.2 hb
  have hS := Sp_adm h hu0 huT
  have hF := Fp_adm h hu0 huT
  have hLF := lhB_two hF.inH (PiF_Fp r g y u)
  have hsb := J1_sb r (slots_val r g y u) hS.inH hLF hF.inH hF.inH (r * u)
  obtain ⟨iQ, -⟩ := hnorm_one_Qhi (r * u) hS.mz (Fam.PiS_Sp r g y u) (l2_of_adm hF) hLF
  refine two_src_eq (j := 1) (Or.inl rfl) h hu0 huT ?_ ?_ hsb.1.of_norm
  · have e : (((1 : ℕ) : ℝ) + 1) = 2 := by norm_num
    rw [e]
    exact hF.mz
  · have e : (((1 : ℕ) : ℝ)) = 1 := by norm_num
    rw [e]
    exact ⟨iQ, Qhi_zero⟩

/-- `N_F` is real. -/
lemma isReal_fastNL (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) : IsReal (fastNL r g y u) := by
  have hy := h.sol.adm u hu huT
  have hQ : IsReal (Qphase (r * u) (y u) (y u)) :=
    (majorized_Qm (fun _ => phaseM (r * u)) (fun _ => phaseM_bdd _) (fun _ => phaseM_real _)
      fun _ _ _ _ _ => continuous_const).real 0 _ _ hy hy
  exact IsReal.neg' (IsReal.PiF' hQ)

/-- **The near differential of `N_F`**: the high source and the rest (the low mixed, purefast and
filter directions). -/
theorem nearD_fastNL_split {j : ℕ} (hj : j = 1 ∨ j = 2) (h : ActualSol μ φ r g y Ty) {u : ℝ}
    (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) (hFm : MZ ((j : ℝ) + 1) (Fp r g y u))
    (hG : MZ j (Qhi (r * u) (Sp r g y u) (Fp r g y u))) (hN : MZ j (fastNL r g y u)) :
    nearD j (-1) r (r * u) (Fp r g y u) (fastNL r g y u) =
      J4 j r g y u + nearD j (-1) r (r * u) (Fp r g y u) (fastRest r g y u) := by
  have hS := Sp_adm h hu huT
  have hF := Fp_adm h hu huT
  have hR := isReal_Qhi (r * u) hS hF
  have hAdd := IsReal.add'' hR hR
  have mA : MZ j (Qhi (r * u) (Sp r g y u) (Fp r g y u) + Qhi (r * u) (Sp r g y u) (Fp r g y u)) :=
    ⟨hG.inH.add hG.inH, by simp [hG.mean]⟩
  have m1 : MZ j (mixHi (r * u) (Sp r g y u) (Fp r g y u)) := ⟨mA.inH.neg, by simp [mixHi, mA.mean]⟩
  have m2 : MZ j (fastRest r g y u) := by
    rw [fastRest_eq h hu huT]
    exact ⟨hN.inH.add mA.inH, by simp [hN.mean, mA.mean]⟩
  have r1 : IsReal (mixHi (r * u) (Sp r g y u) (Fp r g y u)) := IsReal.neg' hAdd
  have r2 : IsReal (fastRest r g y u) := by
    rw [fastRest_eq h hu huT]
    exact IsReal.add'' (isReal_fastNL h hu huT) hAdd
  rw [fastNL_split h hu huT, nearD_add hj (Or.inr rfl) r _ hFm hF.real m1 m2 r1 r2]
  rfl

end OVNS.Quant.Quartic

end
