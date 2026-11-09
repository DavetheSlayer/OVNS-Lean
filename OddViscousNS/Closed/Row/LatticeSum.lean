import OddViscousNS.Closed.Row.Count
import OddViscousNS.Closed.Row.Tail

/-!
# Lattice sums: `S₄(ρ) ≤ 15/ρ` for `ρ ≥ 128`, by discrete Abel summation

`Gs f ρ T = ∑_{ρ < |p| ≤ T} f(|p|²)`.  Shell by shell, with `N(t) ≤ 9/2 (t-3)³`, the quantity
`Gs + 18/T - N(T)/T⁴` does not increase, so `Gs ≤ 18/ρ - N(ρ)/ρ⁴ ≤ (18 - 39/10)/ρ`.
-/

open Finset
open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

/-- The sum of `f(|p|²)` over `ρ < |p| ≤ T`. -/
def Gs (f : ℕ → ℝ) (ρ T : ℕ) : ℝ :=
  ∑ p ∈ (ballF T).filter (fun p => ρ ^ 2 < nsq p), f (nsq p)

/-- One shell. -/
lemma Gs_step {f : ℕ → ℝ} {ρ T : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n, T ^ 2 < n → n ≤ (T + 1) ^ 2 → f n ≤ B) :
    Gs f ρ (T + 1) ≤ Gs f ρ T + ((ballC (T + 1) : ℝ) - ballC T) * B := by
  classical
  set S := (ballF (T + 1)).filter (fun p => ρ ^ 2 < nsq p) with hS
  set S' := (ballF T).filter (fun p => ρ ^ 2 < nsq p) with hS'
  have hsub : S' ⊆ S := filter_subset_filter _ (ballF_mono (Nat.le_succ T))
  have hin : ∀ p ∈ S \ S', T ^ 2 < nsq p ∧ nsq p ≤ (T + 1) ^ 2 := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_sdiff.1 hp
    obtain ⟨h3, h4⟩ := mem_filter.1 h1
    refine ⟨?_, mem_ballF.1 h3⟩
    by_contra h5
    exact h2 (mem_filter.2 ⟨mem_ballF.2 (by omega), h4⟩)
  have h1 : ∑ p ∈ S \ S', f (nsq p) ≤ (S \ S').card • B :=
    sum_le_card_nsmul _ _ _ fun p hp => hB _ (hin p hp).1 (hin p hp).2
  have hball : ballF T ⊆ ballF (T + 1) := ballF_mono (Nat.le_succ T)
  have h2 : ((S \ S').card : ℝ) ≤ (ballC (T + 1) : ℝ) - ballC T := by
    have h3 : (S \ S').card ≤ (ballF (T + 1) \ ballF T).card := by
      refine card_le_card fun p hp => ?_
      obtain ⟨h4, h5⟩ := hin p hp
      refine mem_sdiff.2 ⟨(mem_filter.1 (mem_sdiff.1 hp).1).1, fun h6 => ?_⟩
      have := mem_ballF.1 h6
      omega
    have h4 := card_sdiff_add_card_eq_card hball
    have h5 : ((ballF (T + 1) \ ballF T).card : ℝ) + (ballF T).card = (ballF (T + 1)).card := by
      exact_mod_cast h4
    have h6 : ((S \ S').card : ℝ) ≤ ((ballF (T + 1) \ ballF T).card : ℝ) := by exact_mod_cast h3
    unfold ballC
    linarith
  have h3 : Gs f ρ (T + 1) = ∑ p ∈ S \ S', f (nsq p) + Gs f ρ T := by
    unfold Gs
    rw [← hS, ← hS', sum_sdiff hsub]
  rw [h3, add_comm]
  have h4 : (S \ S').card • B ≤ ((ballC (T + 1) : ℝ) - ballC T) * B := by
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right h2 hB0
  linarith

lemma ball_upper_real (t : ℕ) (h : 128 ≤ t) : (ballC t : ℝ) ≤ 9 / 2 * ((t : ℝ) - 3) ^ 3 := by
  have h1 := ball_upper t h
  have h2 : ((2 * ballC t : ℕ) : ℝ) ≤ ((9 * (t - 3) ^ 3 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast [Nat.cast_sub (show 3 ≤ t by omega)] at h2
  linarith

lemma ball_lower_real (t : ℕ) (h : 128 ≤ t) : 39 / 10 * ((t : ℝ) + 3) ^ 3 ≤ (ballC t : ℝ) := by
  have h1 := ball_lower t h
  have h2 : ((39 * (t + 3) ^ 3 : ℕ) : ℝ) ≤ ((10 * ballC t : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith

private lemma key4 (T N : ℝ) (hT : 3 ≤ T) (hN : N ≤ 9 / 2 * (T - 2) ^ 3) :
    N * (T⁻¹ ^ 4 - (T + 1)⁻¹ ^ 4) ≤ 18 * (T⁻¹ - (T + 1)⁻¹) := by
  have hT0 : 0 < T := by linarith
  have hT1 : 0 < T + 1 := by linarith
  have e1 : T⁻¹ ^ 4 - (T + 1)⁻¹ ^ 4 = ((T + 1) ^ 4 - T ^ 4) / (T ^ 4 * (T + 1) ^ 4) := by
    field_simp
  have e2 : T⁻¹ - (T + 1)⁻¹ = 1 / (T * (T + 1)) := by
    field_simp
    ring
  rw [e1, e2, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (T + 1) ^ 4 - T ^ 4 ≤ 4 * (T + 1) ^ 3 := by nlinarith [sq_nonneg T, pow_pos hT0 3]
  have h0 : 0 ≤ (T + 1) ^ 4 - T ^ 4 := by
    have : T ^ 4 ≤ (T + 1) ^ 4 := pow_le_pow_left₀ hT0.le (by linarith) 4
    linarith
  have h2 : (T - 2) ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have h3 : 0 ≤ (T - 2) ^ 3 := pow_nonneg (by linarith) 3
  calc N * ((T + 1) ^ 4 - T ^ 4) * (T * (T + 1))
      ≤ (9 / 2 * (T - 2) ^ 3) * (4 * (T + 1) ^ 3) * (T * (T + 1)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hN h1 h0 (by positivity)
    _ ≤ (9 / 2 * T ^ 3) * (4 * (T + 1) ^ 3) * (T * (T + 1)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ = _ := by ring

/-- The invariant of the Abel summation. -/
private lemma Gs4_inv (ρ : ℕ) (hρ : 128 ≤ ρ) (T : ℕ) (hT : ρ ≤ T) :
    Gs (fun n => (n : ℝ)⁻¹ ^ 2) ρ T ≤ (ballC T : ℝ) * (T : ℝ)⁻¹ ^ 4 - 18 * (T : ℝ)⁻¹
      + (18 * (ρ : ℝ)⁻¹ - (ballC ρ : ℝ) * (ρ : ℝ)⁻¹ ^ 4) := by
  induction T, hT using Nat.le_induction with
  | base =>
    have : Gs (fun n => (n : ℝ)⁻¹ ^ 2) ρ ρ = 0 := by
      unfold Gs
      refine sum_eq_zero fun p hp => ?_
      have h1 := mem_ballF.1 (mem_filter.1 hp).1
      have h2 := (mem_filter.1 hp).2
      omega
    rw [this]
    linarith
  | succ T hT ih =>
    have hT128 : (128 : ℝ) ≤ T := by exact_mod_cast hρ.trans hT
    have hT0 : (0 : ℝ) < T := by linarith
    have hstep := Gs_step (f := fun n => (n : ℝ)⁻¹ ^ 2) (ρ := ρ) (B := (T : ℝ)⁻¹ ^ 4) (by positivity)
      (fun n h1 _ => by
        have h2 : ((T ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1.le
        push_cast at h2
        have h3 : (n : ℝ)⁻¹ ≤ ((T : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) h2
        calc (n : ℝ)⁻¹ ^ 2 ≤ (((T : ℝ) ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
          _ = _ := by rw [inv_pow, inv_pow]; congr 1; ring)
    have hN := ball_upper_real (T + 1) (by omega)
    push_cast at hN
    have hkey := key4 (T : ℝ) (ballC (T + 1) : ℝ) (by linarith)
      (by convert hN using 2; ring)
    push_cast
    nlinarith

/-- `∑_{ρ<|p|≤T} |p|⁻⁴ ≤ 14.1/ρ`. -/
theorem Gs4_le (ρ : ℕ) (hρ : 128 ≤ ρ) (T : ℕ) (hT : ρ ≤ T) :
    Gs (fun n => (n : ℝ)⁻¹ ^ 2) ρ T ≤ 141 / 10 * (ρ : ℝ)⁻¹ := by
  have h1 := Gs4_inv ρ hρ T hT
  have hT128 : (128 : ℝ) ≤ T := by exact_mod_cast hρ.trans hT
  have hρ128 : (128 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hT0 : (0 : ℝ) < T := by linarith
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have h2 : (ballC T : ℝ) * (T : ℝ)⁻¹ ^ 4 ≤ 18 * (T : ℝ)⁻¹ := by
    have h3 := ball_upper_real T (hρ.trans hT)
    have h4 : (ballC T : ℝ) ≤ 18 * (T : ℝ) ^ 3 := by
      have h5 : ((T : ℝ) - 3) ^ 3 ≤ (T : ℝ) ^ 3 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 3
      have := pow_pos hT0 3
      linarith
    calc (ballC T : ℝ) * (T : ℝ)⁻¹ ^ 4 ≤ 18 * (T : ℝ) ^ 3 * (T : ℝ)⁻¹ ^ 4 :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = _ := by field_simp
  have h3 : 39 / 10 * (ρ : ℝ)⁻¹ ≤ (ballC ρ : ℝ) * (ρ : ℝ)⁻¹ ^ 4 := by
    have h4 := ball_lower_real ρ hρ
    have h5 : (ρ : ℝ) ^ 3 ≤ ((ρ : ℝ) + 3) ^ 3 := pow_le_pow_left₀ hρ0.le (by linarith) 3
    have h6 : 39 / 10 * (ρ : ℝ) ^ 3 ≤ (ballC ρ : ℝ) := by linarith
    calc 39 / 10 * (ρ : ℝ)⁻¹ = 39 / 10 * (ρ : ℝ) ^ 3 * (ρ : ℝ)⁻¹ ^ 4 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h6 (by positivity)
  linarith

/-- From finite truncations to the series. -/
theorem Sm_le_of_Gs {m ρ : ℕ} {B : ℝ}
    (h : ∀ T, ρ ≤ T → Gs (fun n => (n : ℝ)⁻¹ ^ m) ρ T ≤ B) : Sm m ρ ≤ ENNReal.ofReal B := by
  classical
  unfold Sm
  rw [tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set T := ρ + ∑ p ∈ s, nsq p with hT
  have hsT : ∀ p ∈ s, nsq p ≤ T ^ 2 := by
    intro p hp
    have h1 : nsq p ≤ ∑ q ∈ s, nsq q :=
      single_le_sum (f := nsq) (fun _ _ => Nat.zero_le _) hp
    have h2 : T ≤ T ^ 2 := by nlinarith [Nat.zero_le T, sq_nonneg T, Nat.le_self_pow (n := 2) (by norm_num) T]
    omega
  set S := (ballF T).filter (fun p => ρ ^ 2 < nsq p) with hS
  have h1 : ∑ p ∈ s, ENNReal.ofReal (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ m else 0) ≤
      ∑ p ∈ S, ENNReal.ofReal (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ m else 0) := by
    refine sum_le_sum_of_ne_zero fun p hp hne => ?_
    have hU : ρ ^ 2 < nsq p := by
      by_contra h2
      apply hne
      simp [h2]
    exact mem_filter.2 ⟨mem_ballF.2 (hsT p hp), hU⟩
  refine h1.trans ?_
  have hnn : ∀ p ∈ S, 0 ≤ (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ m else 0 : ℝ) := by
    intro p _
    have := absSq_nonneg' p
    split_ifs <;> positivity
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) (h T (by omega)))
  refine sum_congr rfl fun p hp => ?_
  simp only [(mem_filter.1 hp).2, ↓reduceIte, nsq_cast]

/-- `S₄(ρ) ≤ 14.1/ρ` for `ρ ≥ 128`. -/
theorem S4_large (ρ : ℕ) (hρ : 128 ≤ ρ) : Sm 2 ρ ≤ ENNReal.ofReal (141 / 10 * (ρ : ℝ)⁻¹) :=
  Sm_le_of_Gs fun T hT => Gs4_le ρ hρ T hT

end Row
end OVNS
