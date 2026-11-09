import Mathlib

/-!
# Abstract barrier lemmas (first-exit arguments on `[0, T)`)

Pure real analysis used by the invariant-region argument of Theorem 1.3:
* `barrier_of_local`: a continuous `φ` with `φ 0 ≤ 0` that is strictly negative immediately after
  each of its zeros stays `≤ 0`;
* `neg_after_of_integral`: if `φ τ ≤ ∫_{τ₀}^τ g` with `g` continuous at `τ₀` and `g τ₀ < 0`, then
  `φ < 0` immediately after `τ₀`;
* `integral_bound_of_le`: `Y t + c ∫_0^t Z ≤ Y 0` from `Y t = Y s − 2∫_s^t (Z + C)` and
  `Z + C ≥ (c/2) Z`.
-/

open Set MeasureTheory

namespace OVNS

/-- First-exit lemma on `[0, T)`. -/
theorem barrier_of_local {T : ℝ} {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Ico 0 T)) (h0 : φ 0 ≤ 0)
    (hloc : ∀ τ₀ ∈ Ico 0 T, φ τ₀ = 0 →
      ∃ δ > 0, ∀ τ ∈ Ioo τ₀ (τ₀ + δ), τ < T → φ τ < 0) :
    ∀ τ ∈ Ico 0 T, φ τ ≤ 0 := by
  intro τ₁ hτ₁
  by_contra hpos
  push Not at hpos
  set S : Set ℝ := Icc 0 τ₁ ∩ φ ⁻¹' Iic 0 with hS
  have hsub : Icc 0 τ₁ ⊆ Ico 0 T := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hτ₁.2⟩
  have hcl : IsClosed S := (hφ.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : S.Nonempty := ⟨0, ⟨le_rfl, hτ₁.1⟩, h0⟩
  have hbdd : BddAbove S := ⟨τ₁, fun x hx => hx.1.2⟩
  have hmem : sSup S ∈ S := hcl.csSup_mem hne hbdd
  set τ₀ := sSup S with hτ₀
  have hτ₀le : φ τ₀ ≤ 0 := hmem.2
  have hlt : τ₀ < τ₁ := by
    rcases lt_or_eq_of_le hmem.1.2 with h | h
    · exact h
    · exfalso
      have := hmem.2
      simp only [mem_preimage, mem_Iic] at this
      rw [h] at this
      linarith
  have hgt : ∀ u ∈ Ioc τ₀ τ₁, 0 < φ u := by
    intro u hu
    by_contra hu'
    push Not at hu'
    have : u ≤ τ₀ := le_csSup hbdd ⟨⟨le_trans hmem.1.1 hu.1.le, hu.2⟩, hu'⟩
    linarith [hu.1]
  have hpt : ∀ δ > 0, ∃ x ∈ Ioc τ₀ τ₁, x < τ₀ + δ := by
    intro δ hδ
    refine ⟨min (τ₀ + δ / 2) τ₁, ⟨lt_min (by linarith) hlt, min_le_right _ _⟩, ?_⟩
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hτ₀mem : τ₀ ∈ Ico 0 T := hsub hmem.1
  have hzero : φ τ₀ = 0 := by
    refine le_antisymm hτ₀le ?_
    by_contra hneg
    push Not at hneg
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.continuousWithinAt_iff.mp (hφ τ₀ hτ₀mem) (-φ τ₀) (by linarith)
    obtain ⟨x, hx, hxδ⟩ := hpt δ hδ
    have hd : dist x τ₀ < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1]
    have := hball (hsub ⟨le_trans hmem.1.1 hx.1.le, hx.2⟩) hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [hgt x hx, this.2]
  obtain ⟨δ, hδ, hneg⟩ := hloc τ₀ hτ₀mem hzero
  obtain ⟨x, hx, hxδ⟩ := hpt δ hδ
  have h1 := hneg x ⟨hx.1, hxδ⟩ (lt_of_le_of_lt hx.2 hτ₁.2)
  linarith [hgt x hx]

/-- Strict negativity immediately after `τ₀` from an integral upper bound with a continuous
integrand that is negative at `τ₀`. -/
theorem neg_after_of_integral {T τ₀ : ℝ} {φ g : ℝ → ℝ} (hτ₀ : τ₀ ∈ Ico 0 T)
    (hg : ContinuousOn g (Ico 0 T)) (hg0 : g τ₀ < 0)
    (hφ : ∀ τ ∈ Ico τ₀ T, φ τ ≤ ∫ u in τ₀..τ, g u) :
    ∃ δ > 0, ∀ τ ∈ Ioo τ₀ (τ₀ + δ), τ < T → φ τ < 0 := by
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.continuousWithinAt_iff.mp (hg τ₀ hτ₀) (-g τ₀ / 2) (by linarith)
  refine ⟨δ, hδ, fun τ hτ hτT => ?_⟩
  have hsub : uIcc τ₀ τ ⊆ Ico 0 T := by
    rw [uIcc_of_le hτ.1.le]
    exact fun x hx => ⟨le_trans hτ₀.1 hx.1, lt_of_le_of_lt hx.2 hτT⟩
  have hint : IntervalIntegrable g volume τ₀ τ := (hg.mono hsub).intervalIntegrable
  have hle : ∫ u in τ₀..τ, g u ≤ ∫ _ in τ₀..τ, g τ₀ / 2 := by
    refine intervalIntegral.integral_mono_on hτ.1.le hint intervalIntegrable_const ?_
    intro x hx
    have hd : dist x τ₀ < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2, hτ.2]
    have := hball (hsub (by rw [uIcc_of_le hτ.1.le]; exact hx)) hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  have : (τ - τ₀) * (g τ₀ / 2) < 0 := mul_neg_of_pos_of_neg (by linarith [hτ.1]) (by linarith)
  linarith [hφ τ ⟨hτ.1.le, hτT⟩]

/-- From `Y t = Y s − 2∫_s^t (Z + C)` on `[0,T)` and the pointwise heat `Z u + C u ≥ (c/2) Z u`:
`Y t + c ∫_0^t Z ≤ Y 0`. -/
theorem integral_bound_of_le {T c : ℝ} {Y Z C : ℝ → ℝ} (_hc : 0 ≤ c)
    (hZC : IntervalIntegrable (fun u => Z u + C u) volume 0 T)
    (hZ : IntervalIntegrable Z volume 0 T)
    (hlaw : ∀ t ∈ Icc 0 T, Y t = Y 0 - 2 * ∫ u in (0 : ℝ)..t, (Z u + C u))
    (hheat : ∀ u ∈ Icc 0 T, c / 2 * Z u ≤ Z u + C u) :
    ∀ t ∈ Icc 0 T, Y t + c * ∫ u in (0 : ℝ)..t, Z u ≤ Y 0 := by
  intro t ht
  have hsub : uIcc 0 t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2
  have hZt : IntervalIntegrable Z volume 0 t := hZ.mono_set hsub
  have hZCt : IntervalIntegrable (fun u => Z u + C u) volume 0 t := hZC.mono_set hsub
  have hle : ∫ u in (0 : ℝ)..t, c / 2 * Z u ≤ ∫ u in (0 : ℝ)..t, (Z u + C u) :=
    intervalIntegral.integral_mono_on ht.1 (hZt.const_mul _) hZCt
      (fun u hu => hheat u ⟨hu.1, hu.2.trans ht.2⟩)
  rw [intervalIntegral.integral_const_mul] at hle
  rw [hlaw t ht]
  linarith

end OVNS
