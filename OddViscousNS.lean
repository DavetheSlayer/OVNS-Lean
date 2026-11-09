import OddViscousNS.Physical
import OddViscousNS.Closed
import OddViscousNS.Quant

/-!
# Norm-uniform global regularity for Navier–Stokes with large odd viscosity

Theorem 1.1 of the OVNS manuscript.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

/-- **Theorem 1.1 (Norm-uniform global regularity).** There is a finite nonnegative
`R(μ, φ)` such that, for every `ν > 0`, `M, F ≥ 0`, all real mean-zero divergence-free `H²` data
`‖u₀‖₂ ≤ M` and steady forces `‖f‖₂ ≤ F`, and every fixed real `α` with
`|α|/ν ≥ R(M/ν, F/ν²)`, there is a unique global strong solution in `C([0,∞); H²) ∩ L²_loc H³`.
It has uniform `H¹`, `H²` bounds and bounded `H³` square integrals on sliding intervals, all
controlled by `(M/ν, F/ν²)`. When `f = 0`, every initial `H^s` regularity (`s ≥ 2`) persists
(`u t ∈ H^s` for all `t ≥ 0`, continuously, with `u ∈ L²_loc H^{s+1}`) and the solution is smooth
at positive times. -/
theorem global_regularity :
    ∃ R Bd : ℝ → ℝ → ℝ, (∀ μ φ, 0 ≤ R μ φ) ∧
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F →
        Adm 2 u₀ → Adm 2 f → hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F →
        R (M / ν) (F / ν ^ 2) ≤ |α| / ν →
        ∃ u : ℝ → Field,
          IsStrongSolution ν α f u₀ u ∧
          (∀ u', IsStrongSolution ν α f u₀ u' → ∀ t, 0 ≤ t → u' t = u t) ∧
          L2locH 3 u ∧
          (∀ t, 0 ≤ t → hnorm 1 (u t) ≤ ν * Bd (M / ν) (F / ν ^ 2) ∧
            hnorm 2 (u t) ≤ ν * Bd (M / ν) (F / ν ^ 2)) ∧
          (∀ t h : ℝ, 0 ≤ t → 0 ≤ h →
            ∫⁻ s in Icc t (t + h), hsE 3 (u s) ≤
              ENNReal.ofReal (ν * ⌈ν * h⌉ * Bd (M / ν) (F / ν ^ 2))) ∧
          (f = 0 → (∀ s, 2 ≤ s → InH s u₀ → (∀ t, 0 ≤ t → InH s (u t)) ∧
              ContH s u ∧ L2locH (s + 1) u) ∧
            SmoothAtPositiveTimes u) := by
  have key : ∀ μ φ : ℝ, ∃ R Bd : ℝ, 0 ≤ R ∧ (0 ≤ μ → 0 ≤ φ →
      ∀ (r : ℝ) (g v₀ : Field), Adm 2 g → hnorm 2 g ≤ φ → Adm 2 v₀ → hnorm 2 v₀ ≤ μ → R ≤ |r| →
        ∃ y, IsHeatSol (filtN r 0) (filtG r 0 g) ⊤ y ∧ y 0 = v₀ ∧
          (∀ t, 0 ≤ t → hnorm 1 (y t) ≤ Bd ∧ hnorm 2 (y t) ≤ Bd) ∧
          (∀ t, 0 ≤ t → ∫ s in t..(t + 1), hnorm 3 (y s) ^ 2 ≤ Bd)) := by
    intro μ φ
    by_cases h : 0 ≤ μ ∧ 0 ≤ φ
    · obtain ⟨R, Bd, hR, -, H⟩ := normalized_main μ φ h.1 h.2
      exact ⟨R, Bd, hR, fun _ _ => H⟩
    · exact ⟨0, 0, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose R Bd hR hmain using key
  refine ⟨R, Bd, hR, fun ν M F α u₀ f hν hM hF hu₀ hf hu₀M hfF hRα => ?_⟩
  have hν2 : 0 < ν ^ 2 := pow_pos hν 2
  have hc : ((ν : ℂ) ^ 2)⁻¹ = (((ν ^ 2)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hc' : (ν⁻¹ : ℂ) = ((ν⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hg : Adm 2 (((ν : ℂ) ^ 2)⁻¹ • f) := by
    rw [hc]
    exact adm_smul_real _ hf
  have hv : Adm 2 ((ν⁻¹ : ℂ) • u₀) := by
    rw [hc']
    exact adm_smul_real _ hu₀
  have hgn : hnorm 2 (((ν : ℂ) ^ 2)⁻¹ • f) ≤ F / ν ^ 2 := by
    rw [hc, hnorm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hν2).le,
      div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hfF (inv_pos.2 hν2).le
  have hvn : hnorm 2 ((ν⁻¹ : ℂ) • u₀) ≤ M / ν := by
    rw [hc', hnorm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hν).le,
      div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hu₀M (inv_pos.2 hν).le
  have hRr : R (M / ν) (F / ν ^ 2) ≤ |α / ν| := by
    rwa [abs_div, abs_of_pos hν]
  obtain ⟨y, hy, h0, hB, hW⟩ := hmain (M / ν) (F / ν ^ 2) (div_nonneg hM hν.le)
    (div_nonneg hF hν2.le) (α / ν) _ _ hg hgn hv hvn hRr
  exact exists_physical_of_normalized hν hg hy h0 hB hW

end OVNS
