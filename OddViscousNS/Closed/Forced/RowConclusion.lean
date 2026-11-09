import OddViscousNS.Closed.Forced.Invariant
import OddViscousNS.Closed.Conclusion
import OddViscousNS.Closed.Continuation
import OddViscousNS.Physical
import OddViscousNS.Closed.Transfer

/-!
# From a checked row certificate to the physical conclusion (one forced row)

Exactly as `closed_regions_unforced_aux` (`OddViscousNS/Closed/Unforced.lean`), with the force:
the normalized data are `v₀ = ν⁻¹ u₀` (`‖v₀‖₂ ≤ M/ν ≤ s`) and `g = ν⁻² f` (`‖g‖₂ ≤ F/ν² ≤ f₀ s`),
the heat solutions are those of `filtN (α/ν) 0` with force `filtG (α/ν) 0 g`
(`goodForce_filtG`, `Γ = hnorm 1 g ≤ ‖g‖₂ ≤ f₀ s`), the metric hypothesis of
`heat_global_of_metric s (s² Y*) (s² J) (f₀ s)` is `row_metric_bounds`, and the physical solution
is `exists_physical_of_normalized`; the window bound transfers by `Zmet_scaled_scaleU` and
uniqueness (`unique_scaleU`).
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

namespace Forced

open Chk

theorem row_conclusion {k f0 s : ℚ} {J : ℕ} {cells : List Cell} {t : Term} (hs : 0 < s)
    (hk : (k : ℝ) = s * κ₀) (hf0 : f0 ≤ 1) (hR : RowOK k f0 J cells t)
    (hRB : RowBound fun _ => M₀) : ∃ Bd : ℝ, 0 ≤ Bd ∧
    ∀ (ν α M F : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
      hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F → M / ν ≤ s → F / ν ^ 2 ≤ f0 * s →
      GlobalConclusion' ν α f u₀ Bd ∧
      ∀ u : ℝ → Field, IsStrongSolution ν α f u₀ u →
        ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ a + 1 →
          ∫⁻ τ in Icc a b, Zmet (scaled ν s u τ) ≤ (J : ℝ≥0∞) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨Bd, hBd, hglob⟩ := heat_global_of_metric s (max ((s : ℝ) ^ 2 * t.Y) 0)
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
      obtain ⟨h1, h2⟩ := row_metric_bounds hs hk hf0 hR hRB hg hgn hy (hy0 ▸ hvn)
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
  obtain ⟨-, hZb⟩ := row_metric_bounds hs hk hf0 hR hRB hg hgn hy (hy0 ▸ hvn)
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

/-- The conclusion of one row of the table, in the anchor's form. -/
def RowConcl (r : ℕ × ℕ × ℕ) (Bd : ℝ) : Prop :=
  ∀ (ν α M F : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
    hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F → 208013 * (M / ν) ≤ r.1 → 208013 * (F / ν ^ 2) ≤ r.2.1 →
    GlobalConclusion' ν α f u₀ Bd ∧
    ∀ u : ℝ → Field, IsStrongSolution ν α f u₀ u →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ a + 1 →
        ∫⁻ τ in Icc a b, Zmet (scaled ν ((r.1 : ℝ) / 208013) u τ) ≤ r.2.2

/-- `GlobalConclusion'` is monotone in the bound. -/
theorem GlobalConclusion'.mono {ν α : ℝ} {f u₀ : Field} {Bd Bd' : ℝ} (hν : 0 < ν)
    (hle : Bd ≤ Bd') (h : GlobalConclusion' ν α f u₀ Bd) : GlobalConclusion' ν α f u₀ Bd' := by
  obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨u, h1, h2, h3, fun t ht => ?_, fun t h ht hh => ?_, h6⟩
  · have hb : ν * Bd ≤ ν * Bd' := mul_le_mul_of_nonneg_left hle hν.le
    exact ⟨(h4 t ht).1.trans hb, (h4 t ht).2.trans hb⟩
  · refine (h5 t h ht hh).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : (0 : ℝ) ≤ ν * ⌈ν * h⌉ :=
      mul_nonneg hν.le (Int.cast_nonneg (Int.ceil_nonneg (mul_nonneg hν.le hh)))
    exact mul_le_mul_of_nonneg_left hle hc

end Forced

end OVNS
