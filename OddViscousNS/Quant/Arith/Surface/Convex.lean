import OddViscousNS.Quant.Arith.Surface.Blocks

/-!
# Lower bounds for `Vs` (route L1, L5)

`Vs_lower`, and the Jensen step `sum_Vs_ge`.
-/

open Finset

namespace OVNS.Quant.Surf

section OL
open Real



lemma cast_tri (t : ℕ) : ((t * (t + 1) / 2 : ℕ) : ℝ) = (t : ℝ) * (t + 1) / 2 := by
  have h2 : 2 ∣ t * (t + 1) := (Nat.even_mul_succ_self t).two_dvd
  rw [Nat.cast_div h2 (by norm_num)]
  push_cast
  ring

lemma sum_tri (s T : ℕ) : ∑ t ∈ Icc 1 T, ((s : ℝ) - (t : ℝ) * (t + 1) / 2) =
    T * s - (T : ℝ) * (T + 1) * (T + 2) / 6 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

lemma Vs_ge (s T : ℕ) (hT : T ≤ s) :
    (T : ℝ) * s - (T : ℝ) * (T + 1) * (T + 2) / 6 ≤ Vs s := by
  rw [← sum_tri, Vs]
  push_cast
  calc ∑ t ∈ Icc 1 T, ((s : ℝ) - (t : ℝ) * (t + 1) / 2)
      ≤ ∑ t ∈ Icc 1 T, ((s - t * (t + 1) / 2 : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [← cast_tri]
        by_cases h : t * (t + 1) / 2 ≤ s
        · rw [Nat.cast_sub h]
        · have : (s : ℝ) ≤ ((t * (t + 1) / 2 : ℕ) : ℝ) := by
            exact_mod_cast (not_le.1 h).le
          have h0 : (0 : ℝ) ≤ ((s - t * (t + 1) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
    _ ≤ ∑ t ∈ Icc 1 s, ((s - t * (t + 1) / 2 : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hT) fun _ _ _ =>
          Nat.cast_nonneg _

/-- D1b. -/
theorem Vs_lower (s : ℕ) :
    2 * Real.sqrt 2 / 3 * (s : ℝ) ^ ((3 : ℝ) / 2) - 2 * s ≤ Vs s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [Real.zero_rpow]
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  set a : ℝ := Real.sqrt (2 * s) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * s := Real.sq_sqrt (by positivity)
  have ha1 : 1 ≤ a := by nlinarith
  set T := ⌊a⌋₊ with hT
  have hT1 : (T : ℝ) ≤ a := Nat.floor_le ha0
  have hT2 : a < T + 1 := Nat.lt_floor_add_one a
  have hTs : T ≤ s := by
    by_contra h
    have h' : s + 1 ≤ T := by omega
    have h2 : (s : ℝ) + 1 ≤ T := by exact_mod_cast h'
    nlinarith
  have hV := Vs_ge s T hTs
  have hrp : 2 * Real.sqrt 2 / 3 * (s : ℝ) ^ ((3 : ℝ) / 2) = a ^ 3 / 3 := by
    have e1 : (s : ℝ) ^ ((3 : ℝ) / 2) = s * Real.sqrt s := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
        Real.sqrt_eq_rpow]
    have e2 : a = Real.sqrt 2 * Real.sqrt s := by
      rw [ha, Real.sqrt_mul (by norm_num)]
    have e3 : a ^ 3 = a ^ 2 * a := by ring
    rw [e1, e3, ha2, e2]
    ring
  rw [hrp]
  set θ := a - T with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ < 1 := by linarith
  have hTa : (T : ℝ) = a - θ := by linarith
  have hsa : (s : ℝ) = a ^ 2 / 2 := by linarith
  have key : a ^ 3 / 3 - a ^ 2 ≤ (T : ℝ) * s - (T : ℝ) * (T + 1) * (T + 2) / 6 := by
    rw [hTa, hsa]
    have h1 : 0 ≤ θ * (1 - θ) * (2 - θ) := by
      apply mul_nonneg (mul_nonneg hθ0 (by linarith)) (by linarith)
    have h2 : 0 ≤ a * (θ - θ ^ 2 / 2) := by
      apply mul_nonneg ha0; nlinarith
    have h3 : 0 ≤ a * (a / 2 - 1 / 3) := by
      apply mul_nonneg ha0; linarith
    nlinarith
  have : (2 : ℝ) * s = a ^ 2 := by linarith
  linarith

/-- D5. Convexity. -/
theorem sum_Vs_ge {ι : Type*} (Ξ : Finset ι) (s : ι → ℕ) (n : ℝ) (_hn : 0 < n)
    (hΞ : (Ξ.card : ℝ) ≤ n) :
    2 * Real.sqrt 2 / 3 * ((∑ ξ ∈ Ξ, s ξ : ℕ) : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt n
      - 2 * ((∑ ξ ∈ Ξ, s ξ : ℕ) : ℝ) ≤ ((∑ ξ ∈ Ξ, Vs (s ξ) : ℕ) : ℝ) := by
  set E : ℝ := ((∑ ξ ∈ Ξ, s ξ : ℕ) : ℝ) with hE
  have hE' : E = ∑ ξ ∈ Ξ, (s ξ : ℝ) := by rw [hE]; push_cast; rfl
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  rcases Ξ.eq_empty_or_nonempty with rfl | hne
  · simp [hE, Real.zero_rpow]
  set m : ℝ := (Ξ.card : ℝ) with hm
  have hm0 : 0 < m := by rw [hm]; exact_mod_cast hne.card_pos
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Ξ (fun _ => m⁻¹) (fun ξ => (s ξ : ℝ))
    (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul, ← hm, mul_inv_cancel₀ hm0.ne']) (fun _ _ => Nat.cast_nonneg _)
    (p := (3 : ℝ) / 2) (by norm_num)
  simp only [← Finset.mul_sum] at hJ
  rw [← hE'] at hJ
  have h1 : E ^ ((3 : ℝ) / 2) / Real.sqrt m ≤ ∑ ξ ∈ Ξ, (s ξ : ℝ) ^ ((3 : ℝ) / 2) := by
    have e : (m⁻¹ * E) ^ ((3 : ℝ) / 2) = m⁻¹ * (E ^ ((3 : ℝ) / 2) / Real.sqrt m) := by
      rw [Real.mul_rpow (by positivity) hE0, Real.inv_rpow hm0.le,
        show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hm0, Real.rpow_one,
        ← Real.sqrt_eq_rpow, mul_inv]
      field_simp
    rw [e] at hJ
    exact le_of_mul_le_mul_left hJ (by positivity)
  have h2 : E ^ ((3 : ℝ) / 2) / Real.sqrt n ≤ E ^ ((3 : ℝ) / 2) / Real.sqrt m :=
    div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hm0) (Real.sqrt_le_sqrt hΞ)
  have h3 : ∑ ξ ∈ Ξ, (2 * Real.sqrt 2 / 3 * (s ξ : ℝ) ^ ((3 : ℝ) / 2) - 2 * s ξ) ≤
      ∑ ξ ∈ Ξ, (Vs (s ξ) : ℝ) := Finset.sum_le_sum fun ξ _ => Vs_lower (s ξ)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hE'] at h3
  push_cast
  have h4 : 0 ≤ 2 * Real.sqrt 2 / 3 := by positivity
  have h5 := mul_le_mul_of_nonneg_left (h2.trans h1) h4
  have e2 : 2 * Real.sqrt 2 / 3 * (E ^ ((3 : ℝ) / 2) / Real.sqrt n) =
      2 * Real.sqrt 2 / 3 * E ^ ((3 : ℝ) / 2) / Real.sqrt n := by ring
  rw [e2] at h5
  linarith


end OL

end OVNS.Quant.Surf
