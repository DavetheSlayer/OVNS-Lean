import OddViscousNS.Closed.Forced.Common.Invariant
import OddViscousNS.Closed.Forced.RowConclusion

/-!
# The common row: physical conclusion from the certificate (modulo the kernel data)

`common_row_conclusion_of`: exactly `row_conclusion` (`Forced/RowConclusion.lean`) with
`common_metric_bounds` in place of `row_metric_bounds`.  `momentOracle_of`: the oracle from the
proved moment bounds and the kernel coverage facts.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

namespace Forced

namespace Com

open Chk Mom

/-- The moment oracle from the moment lemmas and the kernel coverage facts. -/
theorem momentOracle_of (hRB : RowBound gOVNS) (hAl : CoverAl) (hSm : CoverSm) (hbig : SmallBig)
    (hCf : CoverCf) : MomentOracle := by
  refine ⟨fun hw hw0 ht => ?_, fun hw hw0 ht1 ht2 => cubic_le_aligned hAl hRB hw hw0 ht1 ht2,
    fun hw hw0 ht1 ht2 => cubic_sq_le_cf hCf hRB hw hw0 ht1 ht2,
    fun hw => cubic_le_kappa (hRB.mono gOVNS_le_M₀) hw⟩
  have h := cubic_le_small hSm hbig hRB hw hw0 ht
  norm_num at h ⊢
  linarith

/-- The physical conclusion of a checked common row, given the moment oracle. -/
theorem common_row_conclusion_of (hO : MomentOracle) {k f0 s : ℚ} {J : ℕ} {cells : List CCell}
    {T : MTerm} {W : Win} (hs : 0 < s) (hk : (k : ℝ) = s * κ₀) (hf0 : f0 ≤ 1)
    (hR : CRowOK k f0 s J cells T W) (hRB : RowBound fun _ => M₀) : ∃ Bd : ℝ, 0 ≤ Bd ∧
    ∀ (ν α M F : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
      hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F → M / ν ≤ s → F / ν ^ 2 ≤ f0 * s →
      GlobalConclusion' ν α f u₀ Bd ∧
      ∀ u : ℝ → Field, IsStrongSolution ν α f u₀ u →
        ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ a + 1 →
          ∫⁻ τ in Icc a b, Zmet (scaled ν s u τ) ≤ (J : ℝ≥0∞) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨Bd, hBd, hglob⟩ := heat_global_of_metric s (max ((s : ℝ) ^ 2 * T.Y) 0)
    ((s : ℝ) ^ 2 * J) (f0 * s) hs'.le (le_max_right _ _) (by positivity)
  refine ⟨Bd, hBd, fun ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMν hFν => ?_⟩
  have hc' : (ν⁻¹ : ℂ) = ((ν⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hv : Adm 2 ((ν⁻¹ : ℂ) • u₀) := by
    rw [hc']
    exact adm_smul_real _ hu₀
  have hvn : hnorm 2 ((ν⁻¹ : ℂ) • u₀) ≤ s := by
    rw [hc', hnorm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hν).le]
    refine le_trans ?_ hMν
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hu₀M (inv_pos.2 hν).le
  have hν2 : (0 : ℝ) < (ν ^ 2)⁻¹ := by positivity
  have hc2 : ((ν : ℂ) ^ 2)⁻¹ = (((ν ^ 2)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hg : Adm 2 (((ν : ℂ) ^ 2)⁻¹ • f) := by
    rw [hc2]
    exact adm_smul_real _ hf
  have hgn : hnorm 2 (((ν : ℂ) ^ 2)⁻¹ • f) ≤ f0 * s := by
    rw [hc2, hnorm_smul, Complex.norm_real, Real.norm_of_nonneg hν2.le]
    refine le_trans ?_ hFν
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hfF hν2.le
  have hG : GoodForce (filtG (α / ν) 0 (((ν : ℂ) ^ 2)⁻¹ • f)) (f0 * s) := by
    have h := goodForce_filtG (α / ν) 0 hg
    have h12 : hnorm 1 (((ν : ℂ) ^ 2)⁻¹ • f) ≤ f0 * s :=
      (hnorm_mono (by norm_num) hg.inH).trans hgn
    exact ⟨h.adm, fun τ => (h.bd τ).trans h12, h.cont⟩
  obtain ⟨y, hy, hy0, hB, hW⟩ := hglob (majorized_filtN (α / ν) 0) hG hv hvn
    fun T y hy hy0 => by
      obtain ⟨h1, h2⟩ := common_metric_bounds hO hs hk hf0 hR hRB hg hgn hy (hy0 ▸ hvn)
      exact ⟨fun τ hτ hτT => (h1 τ hτ hτT).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _)), h2⟩
  obtain ⟨u, hS, huniq, hL, hBu, hWu, hZ⟩ := exists_physical_of_normalized hν hg hy hy0 hB hW
  refine ⟨⟨u, hS, huniq, hL, hBu, hWu, fun hf => ⟨(hZ hf).1, (hZ hf).2⟩⟩, ?_⟩
  intro u' hu' a b ha hab hba
  have hsol : ∀ τ, 0 ≤ τ → IsSolenoidal (y τ) :=
    fun τ hτ => (hy.adm τ hτ ENNReal.ofReal_lt_top).sol
  have heq : ∀ τ, 0 ≤ τ →
      scaled ν s u' τ = scaled ν s (scaleU ν (α / ν) y) τ := by
    intro τ hτ
    have := unique_scaleU hν hg hy hy0 hu' (div_nonneg hτ hν.le)
    unfold scaled
    rw [this]
  obtain ⟨-, hZb⟩ := common_metric_bounds hO hs hk hf0 hR hRB hg hgn hy (hy0 ▸ hvn)
  have hs3 : ENNReal.ofReal ((1 / (s : ℝ)) ^ 2) * ENNReal.ofReal ((s : ℝ) ^ 2 * J) = J := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have : (1 / (s : ℝ)) ^ 2 * ((s : ℝ) ^ 2 * J) = J := by
      field_simp
    rw [this, ENNReal.ofReal_natCast]
  have hcongr : ∫⁻ τ in Icc a b, Zmet (scaled ν s u' τ) =
      ∫⁻ τ in Icc a b, ENNReal.ofReal ((1 / (s : ℝ)) ^ 2) * Zmet (y τ) := by
    refine setLIntegral_congr_fun measurableSet_Icc fun τ hτ => ?_
    rw [heq τ (ha.trans hτ.1), Zmet_scaled_scaleU hν _ _ (hsol τ (ha.trans hτ.1))]
  rw [hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hs3]
  gcongr
  exact hZb a b ha hab hba ENNReal.ofReal_lt_top

end Com

end Forced

end OVNS
