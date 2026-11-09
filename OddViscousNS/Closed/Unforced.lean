import OddViscousNS.Closed.Invariance
import OddViscousNS.Closed.Conclusion
import OddViscousNS.Closed.Continuation
import OddViscousNS.Physical

/-!
# Theorem 1.3, unforced branch: assembly

From `unforced_metric_bounds` (the metric hypothesis of `heat_global_of_metric` with
`μ = s = 97/40`, `Ycap = s²`, `J = 100000 s²`, `Γ = 0`), `heat_global_of_metric` (global heat
solution with uniform bounds), `exists_physical_of_normalized` (the physical strong solution with
uniqueness, `L²_loc H³`, the `H¹,H²` caps, the `H³` windows, persistence and smoothness), and the
transfer lemmas (`Ymet_scaled_scaleU`, `Zmet_scaled_scaleU`, uniqueness to identify any strong
solution with the constructed one).
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

theorem closed_regions_unforced_aux (hRB : RowBound fun _ => M₀) : ∃ Bd : ℝ, 0 ≤ Bd ∧
    ∀ (ν α M : ℝ) (u₀ : Field), 0 < ν → 0 ≤ M → Adm 2 u₀ → hnorm 2 u₀ ≤ M → M / ν ≤ 97 / 40 →
      GlobalConclusion' ν α 0 u₀ Bd ∧
      ∀ u : ℝ → Field, IsStrongSolution ν α 0 u₀ u →
        (∀ τ, 0 ≤ τ → Ymet (scaled ν (97 / 40) u τ) ≤ 1) ∧
        ∫⁻ τ in Ici 0, Zmet (scaled ν (97 / 40) u τ) ≤ 100000 := by
  obtain ⟨Bd, hBd, hglob⟩ := heat_global_of_metric (97 / 40) ((97 / 40) ^ 2)
    (100000 * (97 / 40) ^ 2) 0 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Bd, hBd, fun ν α M u₀ hν hM hu₀ hu₀M hMν => ?_⟩
  have hc' : (ν⁻¹ : ℂ) = ((ν⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hv : Adm 2 ((ν⁻¹ : ℂ) • u₀) := by
    rw [hc']
    exact adm_smul_real _ hu₀
  have hvn : hnorm 2 ((ν⁻¹ : ℂ) • u₀) ≤ 97 / 40 := by
    rw [hc', hnorm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hν).le]
    refine le_trans ?_ hMν
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hu₀M (inv_pos.2 hν).le
  have hg : Adm 2 (((ν : ℂ) ^ 2)⁻¹ • (0 : Field)) := by
    rw [smul_zero]
    simpa using adm_smul_real 0 hu₀
  have hG0 : filtG (α / ν) 0 (((ν : ℂ) ^ 2)⁻¹ • (0 : Field)) = fun _ => 0 := by
    funext t
    rw [smul_zero]
    exact rotF_zero_field _
  have hG : GoodForce (fun _ : ℝ => (0 : Field)) 0 := by
    have := goodForce_filtG (α / ν) 0 hg
    rwa [hG0, smul_zero, hnorm_zero] at this
  obtain ⟨y, hy, hy0, hB, hW⟩ := hglob (majorized_filtN (α / ν) 0) hG hv hvn
    fun T y hy hy0 => by
      obtain ⟨h1, h2⟩ := unforced_metric_bounds hRB hy (hy0 ▸ hvn)
      exact ⟨h1, fun a b ha hab _ hbT => h2 a b ha hab hbT⟩
  have hy' : IsHeatSol (filtN (α / ν) 0) (filtG (α / ν) 0 (((ν : ℂ) ^ 2)⁻¹ • (0 : Field)))
      ⊤ y := by
    rw [hG0]
    exact hy
  obtain ⟨u, hS, huniq, hL, hBu, hWu, hZ⟩ := exists_physical_of_normalized hν hg hy' hy0 hB hW
  refine ⟨⟨u, hS, huniq, hL, hBu, hWu, fun hf => ⟨(hZ hf).1, (hZ hf).2⟩⟩, ?_⟩
  intro u' hu'
  have hsol : ∀ τ, 0 ≤ τ → IsSolenoidal (y τ) :=
    fun τ hτ => (hy.adm τ hτ ENNReal.ofReal_lt_top).sol
  have heq : ∀ τ, 0 ≤ τ →
      scaled ν (97 / 40) u' τ = scaled ν (97 / 40) (scaleU ν (α / ν) y) τ := by
    intro τ hτ
    have := unique_scaleU hν hg hy' hy0 hu' (div_nonneg hτ hν.le)
    unfold scaled
    rw [this]
  obtain ⟨hYb, hZb⟩ := unforced_metric_bounds hRB hy (hy0 ▸ hvn)
  have hs2 : ENNReal.ofReal ((1 / (97 / 40 : ℝ)) ^ 2) * ENNReal.ofReal ((97 / 40) ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    norm_num
  have hs3 : ENNReal.ofReal ((1 / (97 / 40 : ℝ)) ^ 2) *
      ENNReal.ofReal (100000 * (97 / 40) ^ 2) = 100000 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    norm_num
  refine ⟨fun τ hτ => ?_, ?_⟩
  · rw [heq τ hτ, Ymet_scaled_scaleU hν _ _ (hsol τ hτ), ← hs2]
    gcongr
    exact hYb τ hτ ENNReal.ofReal_lt_top
  · have hset : Ici (0 : ℝ) = ⋃ n : ℕ, Icc 0 (n : ℝ) := by
      ext x
      simp only [mem_Ici, mem_iUnion, mem_Icc]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_ge x
        exact ⟨n, hx, hn⟩
      · rintro ⟨n, hx, -⟩
        exact hx
    have hcongr : ∫⁻ τ in Ici 0, Zmet (scaled ν (97 / 40) u' τ) =
        ∫⁻ τ in Ici 0, ENNReal.ofReal ((1 / (97 / 40 : ℝ)) ^ 2) * Zmet (y τ) := by
      refine setLIntegral_congr_fun measurableSet_Ici fun τ hτ => ?_
      rw [heq τ hτ, Zmet_scaled_scaleU hν _ _ (hsol τ hτ)]
    rw [hcongr, hset, setLIntegral_iUnion_of_directed]
    · refine iSup_le fun n => ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hs3]
      gcongr
      exact hZb 0 n le_rfl (Nat.cast_nonneg n) ENNReal.ofReal_lt_top
    · exact Monotone.directed_le fun m n hmn => Icc_subset_Icc_right (by exact_mod_cast hmn)

end OVNS
