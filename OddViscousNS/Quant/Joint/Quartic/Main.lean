import OddViscousNS.Quant.Joint.Quartic.Piece1
import OddViscousNS.Quant.Energy.H1.Bounds

/-!
# The fourth correction: what the energies consume (step J5, node N11)

Sources: `upstream/theorem12_v4/J3_HIGH_MIXED_QUARTICS_V2.md`, `JOINT_ASSEMBLY_V4.md` §§3–4; Bodies
34, 35, 43, 46.  The energies of N14, N15 add `C_{4,s} = C4 s` to `E_s = e_s + E_s⁰ + C_{3,s}`:

* `C4_identity_one`, `C4_identity_two`: `C_{4,s}(b) − C_{4,s}(a) = ∫ (−J_s + Rem_s)`;
* `C4_continuousOn`: `C_{4,s}` is continuous in time;
* `cubicD_split_one`, `cubicD_split_two`: the term `cubicD s (−1) r (r u) F N_F` of `h1RHS`, `h2RHS`
  is `J_s + D_s^N(F; N_rest) + D_s^B(F; N_F)`.  So in the sum `J_s` cancels, and the low mixed,
  purefast, filter and FAR parts stay;
* `quartic_one_piece`, `quartic_two_piece`: the static bounds and `Rem_s` on a piece;
* `nearP_le_zq`: the near share of J6, from `EnergyData.near_shares`, with `K_P ≥ 1`;
* `qOneFull_below`, `qTwo_below`: the thresholds are `JointBelow`.
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- **The near share**: the floor `Q^{1/3}` of `jointLP` is all that the quartics use. -/
theorem nearP_le_zq {R₀ X R KP q : ℝ} (hdom : JDom R₀ X R) (hKP : 1 ≤ KP) (hq : 0 ≤ q)
    (h : KP * Ex 1 R * jointQ X R ^ ((1 : ℝ) / 3) * nearP q ≤ 1) : nearP q ≤ zq X R := by
  have hP0 : 0 ≤ nearP q := by
    have := Real.rpow_nonneg hq (-(3 : ℝ) / 4)
    unfold nearP
    positivity
  have hQ : 0 < jointQ X R ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hdom.Q_pos _
  have hE : 1 ≤ Ex 1 R := hdom.one_le_Ex zero_le_one
  have h1 : 1 ≤ KP * Ex 1 R := one_le_mul_of_one_le_of_one_le hKP hE
  have h2 : jointQ X R ^ ((1 : ℝ) / 3) * nearP q ≤ KP * Ex 1 R * jointQ X R ^ ((1 : ℝ) / 3) *
      nearP q := by
    have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hQ.le hP0)
    nlinarith only [this]
  have h3 := h2.trans h
  rw [zq, ← one_div, le_div_iff₀ hQ]
  linarith

/-- **`C_{4,s}` is continuous in time**: it is a primitive, by the identity. -/
theorem C4_continuousOn {j : ℕ} (hj : j = 1 ∨ j = 2) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    ContinuousOn (C4 j r g y) (Set.Icc a b) := by
  set f : ℝ → ℝ := fun u => -J4 j r g y u + Rem4 j r g y u with hf
  have hid : ∀ c ∈ Set.Icc a b, IntervalIntegrable f volume a c ∧
      C4 j r g y c - C4 j r g y a = ∫ u in a..c, f u := by
    intro c hc
    have hcT := lt_lifespan hc.2 hb
    rcases hj with rfl | rfl
    · exact C4_identity_one h hr ha hc.1 hcT
    · exact C4_identity_two h hr ha hc.1 hcT
  have hI := (hid b ⟨hab, le_rfl⟩).1
  have hp : ContinuousOn (fun c => ∫ u in a..c, f u) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval
      (by rw [Set.uIcc_of_le hab]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hI)
  rw [Set.uIcc_of_le hab] at hp
  have hc : ContinuousOn (fun c => C4 j r g y a + ∫ u in a..c, f u) (Set.Icc a b) :=
    continuousOn_const.add hp
  refine hc.congr fun c hc' => ?_
  have := (hid c hc').2
  simp only
  linarith

/-- `N_F` has mean zero. -/
lemma fastNL_zero (u : ℝ) : fastNL r g y u 0 = 0 := by
  simp [fastNL, PiF]

/-- **The differential of the cubic corrector at weight two**, at an `H³` time. -/
theorem cubicD_split_two (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u)) :
    cubicD 2 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) = J4 2 r g y u +
      nearD 2 (-1) r (r * u) (Fp r g y u) (fastRest r g y u) +
      farD 2 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) := by
  have hS := Sp_adm h hu huT
  have hF := Fp_adm h hu huT
  have hF3m : MZ 3 (Fp r g y u) := ⟨hF3, hF.mean⟩
  have hS3m : MZ 3 (Sp r g y u) := ⟨hS3, hS.mean⟩
  have hL := lhB_two hF.inH (PiF_Fp r g y u)
  obtain ⟨iR, -⟩ := hnorm_two_fastRest h hr hu huT hF3 hS3 le_rfl
  obtain ⟨iN, -⟩ := hnorm_two_fastNL h hu huT iR hS3 hL
  obtain ⟨iQ, -⟩ := hnorm_two_Qhi (r * u) hS3m (Fam.PiS_Sp r g y u) (l2_of_adm hF) hL
  have hN : MZ 2 (fastNL r g y u) := ⟨iN, fastNL_zero u⟩
  rw [H2.cubicD_two_eq_near_add_far (Or.inr rfl) r _ hF3m hN]
  have hsplit := nearD_fastNL_split (j := 2) (Or.inr rfl) h hu huT
    (by norm_num; exact hF3m) (by norm_num; exact ⟨iQ, Qhi_zero⟩) (by norm_num; exact hN)
  rw [hsplit]

/-- **The differential of the cubic corrector at weight one.** -/
theorem cubicD_split_one (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    cubicD 1 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) = J4 1 r g y u +
      nearD 1 (-1) r (r * u) (Fp r g y u) (fastRest r g y u) +
      farD 1 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) := by
  have hS := Sp_adm h hu huT
  have hF := Fp_adm h hu huT
  have hL := lhB_two hF.inH (PiF_Fp r g y u)
  obtain ⟨iQ, -⟩ := hnorm_one_Qhi (r * u) hS.mz (Fam.PiS_Sp r g y u) (l2_of_adm hF) hL
  obtain ⟨hI1, -⟩ := hnorm_PiF_Qphase_le (r * u) (h.sol.adm u hu huT)
  have hN : MZ 1 (fastNL r g y u) := ⟨InH.neg hI1, fastNL_zero u⟩
  rw [cubicD_eq_near_add_far' (Or.inr rfl) r _ hF.mz (PiF_Fp r g y u) hN]
  have hsplit := nearD_fastNL_split (j := 1) (Or.inl rfl) h hu huT
    (by norm_num; exact hF.mz) (by norm_num; exact ⟨iQ, Qhi_zero⟩) (by norm_num; exact hN)
  rw [hsplit]

end OVNS.Quant.Quartic

end
