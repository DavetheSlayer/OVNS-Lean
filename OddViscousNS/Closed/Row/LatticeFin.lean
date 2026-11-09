import OddViscousNS.Closed.Row.LatticeSum
import OddViscousNS.Closed.Row.Tables
import OddViscousNS.Closed.Row.Data.Rad

/-!
# `S₄(ρ) ≤ 15/ρ` for all `ρ ≥ 28`, and `ψ(t) ≤ 17 t` for all `t ≥ 33`

Below radius `128` these are exact finite sums run by the kernel at checkpoints (`Data/Rad.lean`);
above it they come from the discrete Abel summation with the two-sided counts.
-/

open Finset
open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

set_option maxRecDepth 20000
set_option linter.constructorNameAsVariable false

/-- The finite part of `S₄`, abstractly. -/
lemma Gs4_gen {R t L : ℕ} (φ : ℕ → ℕ)
    (hφ : ∀ n, t ^ 2 < n → n ≤ R ^ 2 → ((n : ℝ))⁻¹ ^ 2 ≤ (φ n : ℝ) / 18446744073709551616)
    (hL : ∑ p ∈ boxM R, φ (nsq p) ≤ L) :
    Gs (fun n => (n : ℝ)⁻¹ ^ 2) t R ≤ (L : ℝ) / 18446744073709551616 := by
  have hle : Gs (fun n => (n : ℝ)⁻¹ ^ 2) t R ≤
      ∑ p ∈ boxM R, (φ (nsq p) : ℝ) / 18446744073709551616 := by
    unfold Gs
    refine (sum_le_sum fun p hp => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => by positivity)
    · obtain ⟨h1, h2⟩ := mem_filter.1 hp
      exact hφ _ h2 (mem_ballF.1 h1)
    · exact mem_box_of_nsq (mem_ballF.1 (mem_filter.1 hp).1)
  refine hle.trans ?_
  rw [← sum_div]
  have : ((∑ p ∈ boxM R, φ (nsq p) : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  push_cast at this
  exact div_le_div_of_nonneg_right this (by norm_num)

/-- The ceiling of `2⁶⁴/n²`. -/
lemma ceil4_spec {n : ℕ} (hn : 0 < n) : ((n : ℝ))⁻¹ ^ 2 ≤
    ((Nat.div (Nat.add 18446744073709551616 (Nat.sub (Nat.mul n n) 1)) (Nat.mul n n) : ℕ) : ℝ) /
      18446744073709551616 := by
  have hd : 0 < n * n := by positivity
  have h4 := div_le_cdiv 18446744073709551616 (n * n) hd
  have h5 : ((n : ℝ))⁻¹ ^ 2 = ((18446744073709551616 : ℕ) : ℝ) / ((n * n : ℕ) : ℝ) /
      18446744073709551616 := by
    push_cast
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  rw [h5]
  exact div_le_div_of_nonneg_right h4 (by norm_num)

/-- The finite part of `S₄`, from a kernel sum. -/
lemma Gs4_fin {t lo L : ℕ} (hlo : lo = t ^ 2) (h : Nat.ble (s4Sum lo 16384) L = true) :
    Gs (fun n => (n : ℝ)⁻¹ ^ 2) t 128 ≤ (L : ℝ) / 18446744073709551616 := by
  subst hlo
  have hL := Nat.le_of_ble_eq_true h
  set φ : ℕ → ℕ := fun n => cut (t ^ 2) 16384 n
    (Nat.div (Nat.add 18446744073709551616 (Nat.sub (Nat.mul n n) 1)) (Nat.mul n n)) with hφ
  have hs : s4Sum (t ^ 2) 16384 = ∑ p ∈ boxM 128, φ (nsq p) := by
    unfold s4Sum
    refine rad128_eq φ fun s hs => ?_
    rw [hφ]
    simp only [cut_eq]
    simp only [show ¬ s ≤ 16384 by omega, and_false, ↓reduceIte]
  rw [hs] at hL
  refine Gs4_gen (R := 128) φ (fun n h1 h2 => ?_) hL
  have hn : 0 < n := by omega
  have h3 : n ≤ 16384 := by norm_num at h2; exact h2
  simp only [hφ, cut_eq, h1, h3, and_self, ↓reduceIte]
  exact ceil4_spec hn

/-- Splitting `S₄(t)` at a radius `R`. -/
lemma Sm2_split {t R : ℕ} : Sm 2 t ≤ ENNReal.ofReal (Gs (fun n => (n : ℝ)⁻¹ ^ 2) t R) + Sm 2 R := by
  classical
  set S := (ballF R).filter (fun p => t ^ 2 < nsq p) with hS
  have h1 : ENNReal.ofReal (Gs (fun n => (n : ℝ)⁻¹ ^ 2) t R) =
      ∑' p : Mode, if p ∈ S then ENNReal.ofReal ((nsq p : ℝ)⁻¹ ^ 2) else 0 := by
    unfold Gs
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← hS,
      tsum_eq_sum (s := S) (fun p hp => by simp [hp])]
    exact sum_congr rfl fun p hp => by simp [hp]
  unfold Sm
  rw [h1, ← tsum_add]
  refine tsum_le_tsum fun p => ?_
  by_cases hU : t ^ 2 < nsq p
  · by_cases hl : nsq p ≤ R ^ 2
    · have hp : p ∈ S := mem_filter.2 ⟨mem_ballF.2 hl, hU⟩
      simp [hU, hp, nsq_cast]
    · have hh : R ^ 2 < nsq p := by omega
      have hp : p ∉ S := fun h => hl (mem_ballF.1 (mem_filter.1 h).1)
      simp only [hU, hh, hp, ↓reduceIte, zero_add, le_refl]
  · simp [hU]

/-- `S₄` is antitone. -/
lemma Sm_anti {m s t : ℕ} (h : s ≤ t) : Sm m t ≤ Sm m s := by
  unfold Sm
  refine tsum_le_tsum fun p => ENNReal.ofReal_le_ofReal ?_
  have := absSq_nonneg' p
  by_cases h1 : t ^ 2 < nsq p
  · have h2 : s ^ 2 < nsq p := lt_of_le_of_lt (Nat.pow_le_pow_left h 2) h1
    simp [h1, h2]
  · simp only [h1, ↓reduceIte]
    split_ifs <;> positivity

/-- A checkpoint for `S₄`. -/
lemma S4_check {t t' lo L ρ : ℕ} (hlo : lo = t ^ 2) (h : Nat.ble (s4Sum lo 16384) L = true)
    (hL : (L : ℝ) / 18446744073709551616 + 141 / 10 * ((128 : ℕ) : ℝ)⁻¹ ≤ 15 * (t' : ℝ)⁻¹)
    (h1 : t ≤ ρ) (h2 : ρ ≤ t') (h3 : 0 < ρ) : Sm 2 ρ ≤ ENNReal.ofReal (15 * (ρ : ℝ)⁻¹) := by
  have e1 := Sm_anti (m := 2) h1
  have e2 := Sm2_split (t := t) (R := 128)
  have e3 := S4_large 128 le_rfl
  have e4 := Gs4_fin hlo h
  have hG : 0 ≤ Gs (fun n => (n : ℝ)⁻¹ ^ 2) t 128 := by
    unfold Gs
    exact sum_nonneg fun _ _ => by positivity
  refine e1.trans (e2.trans ((add_le_add (ENNReal.ofReal_le_ofReal e4) e3).trans ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (hL.trans ?_)
  have hρ : (0 : ℝ) < ρ := by exact_mod_cast h3
  have : (ρ : ℝ) ≤ t' := by exact_mod_cast h2
  have h5 : (t' : ℝ)⁻¹ ≤ (ρ : ℝ)⁻¹ := inv_anti₀ hρ this
  linarith

/-- **`S₄(ρ) ≤ 15/ρ` for `ρ ≥ 28`.** -/
theorem S4_le (ρ : ℕ) (hρ : 28 ≤ ρ) : Sm 2 ρ ≤ ENNReal.ofReal (15 * (ρ : ℝ)⁻¹) := by
  by_cases h28 : ρ ≤ 32
  · exact S4_check (t := 28) (t' := 32) (by norm_num) s4_28 (by norm_num) (by omega) h28 (by omega)
  by_cases h32 : ρ ≤ 37
  · exact S4_check (t := 32) (t' := 37) (by norm_num) s4_32 (by norm_num) (by omega) h32 (by omega)
  by_cases h37 : ρ ≤ 42
  · exact S4_check (t := 37) (t' := 42) (by norm_num) s4_37 (by norm_num) (by omega) h37 (by omega)
  by_cases h42 : ρ ≤ 48
  · exact S4_check (t := 42) (t' := 48) (by norm_num) s4_42 (by norm_num) (by omega) h42 (by omega)
  by_cases h48 : ρ ≤ 54
  · exact S4_check (t := 48) (t' := 54) (by norm_num) s4_48 (by norm_num) (by omega) h48 (by omega)
  by_cases h54 : ρ ≤ 61
  · exact S4_check (t := 54) (t' := 61) (by norm_num) s4_54 (by norm_num) (by omega) h54 (by omega)
  by_cases h61 : ρ ≤ 68
  · exact S4_check (t := 61) (t' := 68) (by norm_num) s4_61 (by norm_num) (by omega) h61 (by omega)
  by_cases h68 : ρ ≤ 76
  · exact S4_check (t := 68) (t' := 76) (by norm_num) s4_68 (by norm_num) (by omega) h68 (by omega)
  by_cases h76 : ρ ≤ 84
  · exact S4_check (t := 76) (t' := 84) (by norm_num) s4_76 (by norm_num) (by omega) h76 (by omega)
  by_cases h84 : ρ ≤ 92
  · exact S4_check (t := 84) (t' := 92) (by norm_num) s4_84 (by norm_num) (by omega) h84 (by omega)
  by_cases h92 : ρ ≤ 100
  · exact S4_check (t := 92) (t' := 100) (by norm_num) s4_92 (by norm_num) (by omega) h92 (by omega)
  by_cases h100 : ρ ≤ 108
  · exact S4_check (t := 100) (t' := 108) (by norm_num) s4_100 (by norm_num) (by omega) h100 (by omega)
  by_cases h108 : ρ ≤ 116
  · exact S4_check (t := 108) (t' := 116) (by norm_num) s4_108 (by norm_num) (by omega) h108 (by omega)
  by_cases h116 : ρ ≤ 124
  · exact S4_check (t := 116) (t' := 124) (by norm_num) s4_116 (by norm_num) (by omega) h116 (by omega)
  by_cases h124 : ρ ≤ 132
  · exact S4_check (t := 124) (t' := 132) (by norm_num) s4_124 (by norm_num) (by omega) h124 (by omega)
  have hρ0 : (0 : ℝ) < ρ := by
    have : 0 < ρ := by omega
    exact_mod_cast this
  refine (S4_large ρ (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
  have : 0 < (ρ : ℝ)⁻¹ := by positivity
  linarith

/-- `S₆(ρ) ≤ 15/ρ³`. -/
theorem S6_le (ρ : ℕ) (hρ : 28 ≤ ρ) :
    Sm 3 ρ ≤ ENNReal.ofReal (15 * (ρ : ℝ)⁻¹ ^ 3) := by
  have h1 := Sm3_le ρ (by omega)
  have h2 := S4_le ρ hρ
  refine h1.trans ((mul_le_mul_right h2 _).trans ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-- `ψ(t) = ∑_{|p|≤t} a(p)`. -/
def psiF (t : ℕ) : ℝ := ∑ p ∈ ballF t, aa (nsq p)

lemma aa_zero : aa 0 = 0 := by simp [aa]

lemma aa_high {n : ℕ} (h : 120 < n) : aa n = (n : ℝ)⁻¹ := by
  rw [aa, vv_gt h, one_div]

lemma psiF_eq_Gs (t : ℕ) : psiF t = Gs aa 0 t := by
  unfold psiF Gs
  rw [← sum_filter_add_sum_filter_not (ballF t) (fun p => 0 ^ 2 < nsq p)]
  have : ∑ p ∈ (ballF t).filter (fun p => ¬ 0 ^ 2 < nsq p), aa (nsq p) = 0 := by
    refine sum_eq_zero fun p hp => ?_
    have h := (mem_filter.1 hp).2
    have : nsq p = 0 := by
      norm_num at h
      omega
    rw [this, aa_zero]
  rw [this, add_zero]

lemma psiF_mono {s t : ℕ} (h : s ≤ t) : psiF s ≤ psiF t :=
  sum_le_sum_of_subset_of_nonneg (ballF_mono h) fun _ _ _ => aa_nonneg _

/-- The finite part of `ψ`, abstractly. -/
lemma psi_gen {R t L : ℕ} (φ : ℕ → ℕ)
    (hφ : ∀ n, 0 < n → n ≤ t ^ 2 → aa n ≤ (φ n : ℝ) / 2097152)
    (hsub : ∀ p, nsq p ≤ t ^ 2 → p ∈ boxM R)
    (hL : ∑ p ∈ boxM R, φ (nsq p) ≤ L) : psiF t ≤ (L : ℝ) / 2097152 := by
  have hle : psiF t ≤ ∑ p ∈ boxM R, (φ (nsq p) : ℝ) / 2097152 := by
    unfold psiF
    refine (sum_le_sum fun p hp => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (fun p hp => hsub p (mem_ballF.1 hp))
        fun _ _ _ => by positivity)
    rcases Nat.eq_zero_or_pos (nsq p) with h0 | h0
    · rw [h0, aa_zero]; positivity
    · exact hφ _ h0 (mem_ballF.1 hp)
  refine hle.trans ?_
  rw [← sum_div]
  have : ((∑ p ∈ boxM R, φ (nsq p) : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  push_cast at this
  exact div_le_div_of_nonneg_right this (by norm_num)

/-- The finite part of `ψ`, from a kernel sum. -/
lemma psi_fin2 {t L : ℕ} (φ : ℕ → ℕ) (hφ : φ = fun n => cut 0 (t ^ 2) n (FA n))
    (ht : t ^ 2 ≤ 16384) (hL : ∑ p ∈ boxM 128, φ (nsq p) ≤ L) : psiF t ≤ (L : ℝ) / 2097152 := by
  have e : (128 : ℕ) ^ 2 = 16384 := by norm_num
  have hsub : ∀ p, nsq p ≤ t ^ 2 → p ∈ boxM 128 := fun p hp =>
    mem_box_of_nsq (t := 128) (by rw [e]; exact hp.trans ht)
  refine psi_gen (R := 128) φ (fun n h1 h2 => ?_) hsub hL
  rw [hφ]
  simp only [cut_eq, h1, h2, and_self, ↓reduceIte]
  exact aa_le_FA h1 (h2.trans ht)

lemma rad_psi {t : ℕ} (φ : ℕ → ℕ) (hφ : φ = fun n => cut 0 (t ^ 2) n (FA n))
    (ht : t ^ 2 ≤ 16384) : rad128 φ = ∑ p ∈ boxM 128, φ (nsq p) := by
  refine rad128_eq φ fun s hs => ?_
  have h1 : 16384 < s := lt_of_lt_of_le (by norm_num) hs
  rw [hφ]
  simp only [cut_eq]
  simp only [show ¬ s ≤ t ^ 2 from fun h => absurd (h.trans ht) (by omega), and_false, ↓reduceIte]

lemma psi_fin {t hi L : ℕ} (hhi : hi = t ^ 2) (ht : hi ≤ 16384) (h : Nat.ble (psiSum hi) L = true) :
    psiF t ≤ (L : ℝ) / 2097152 := by
  subst hhi
  have hL := Nat.le_of_ble_eq_true h
  have hs : psiSum (t ^ 2) = rad128 (fun n => cut 0 (t ^ 2) n (FA n)) := rfl
  rw [hs, rad_psi _ rfl ht] at hL
  exact psi_fin2 _ rfl ht hL

private lemma key2 (T N : ℝ) (hT : 3 ≤ T) (hN : N ≤ 9 / 2 * (T - 2) ^ 3) :
    N * (T⁻¹ ^ 2 - (T + 1)⁻¹ ^ 2) ≤ 9 := by
  have hT0 : 0 < T := by linarith
  have hT1 : 0 < T + 1 := by linarith
  have e1 : T⁻¹ ^ 2 - (T + 1)⁻¹ ^ 2 = (2 * T + 1) / (T ^ 2 * (T + 1) ^ 2) := by
    field_simp
    ring
  rw [e1, mul_div_assoc', div_le_iff₀ (by positivity)]
  have h1 : (T - 2) ^ 3 * (2 * T + 1) ≤ 2 * T ^ 2 * (T + 1) ^ 2 := by
    nlinarith [mul_pos hT0 hT0, mul_pos (mul_pos hT0 hT0) hT0, mul_pos (mul_pos (mul_pos hT0 hT0) hT0) hT0]
  have h2 : 0 ≤ 2 * T + 1 := by positivity
  calc N * (2 * T + 1) ≤ (9 / 2 * (T - 2) ^ 3) * (2 * T + 1) := mul_le_mul_of_nonneg_right hN h2
    _ = 9 / 2 * ((T - 2) ^ 3 * (2 * T + 1)) := by ring
    _ ≤ 9 / 2 * (2 * T ^ 2 * (T + 1) ^ 2) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = _ := by ring

/-- The invariant of the Abel summation for `ψ`. -/
private lemma psi_inv (T : ℕ) (hT : 128 ≤ T) :
    psiF T ≤ (ballC T : ℝ) * (T : ℝ)⁻¹ ^ 2 + (psiF 128 - (ballC 128 : ℝ) * ((128 : ℕ) : ℝ)⁻¹ ^ 2)
      + 9 * ((T : ℝ) - 128) := by
  induction T, hT using Nat.le_induction with
  | base =>
    push_cast
    linarith
  | succ T hT ih =>
    have hT128 : (128 : ℝ) ≤ T := by exact_mod_cast hT
    have hT0 : (0 : ℝ) < T := by linarith
    have hstep := Gs_step (f := aa) (ρ := 0) (T := T) (B := (T : ℝ)⁻¹ ^ 2) (by positivity)
      (fun n h1 _ => by
        have hn : 120 < n := by
          have : 128 ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hT 2
          omega
        rw [aa_high hn]
        have h2 : ((T ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1.le
        push_cast at h2
        have h3 : (n : ℝ)⁻¹ ≤ ((T : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) h2
        rwa [inv_pow])
    rw [← psiF_eq_Gs, ← psiF_eq_Gs] at hstep
    have hN := ball_upper_real (T + 1) (by omega)
    push_cast at hN
    have hkey := key2 (T : ℝ) (ballC (T + 1) : ℝ) (by linarith) (by convert hN using 2; ring)
    push_cast
    generalize (ballC (T + 1) : ℝ) = N' at *
    generalize (ballC T : ℝ) = N at *
    generalize (T : ℝ)⁻¹ = u at *
    generalize ((T : ℝ) + 1)⁻¹ = v at *
    generalize psiF (T + 1) = P' at *
    generalize psiF T = P at *
    linarith

/-- `ψ(t) ≤ 17 t` for `t ≥ 128`. -/
theorem psi_large (T : ℕ) (hT : 128 ≤ T) : psiF T ≤ 17 * (T : ℝ) := by
  have h1 := psi_inv T hT
  have hT128 : (128 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have h2 : (ballC T : ℝ) * (T : ℝ)⁻¹ ^ 2 ≤ 9 / 2 * (T : ℝ) := by
    have h3 := ball_upper_real T hT
    have h4 : (ballC T : ℝ) ≤ 9 / 2 * (T : ℝ) ^ 3 := by
      have h5 : ((T : ℝ) - 3) ^ 3 ≤ (T : ℝ) ^ 3 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 3
      linarith
    calc (ballC T : ℝ) * (T : ℝ)⁻¹ ^ 2 ≤ 9 / 2 * (T : ℝ) ^ 3 * (T : ℝ)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = _ := by field_simp
  have h3 := psi_fin (t := 128) (by norm_num) (by norm_num) psi_all
  have h4 := ball_lower_real 128 le_rfl
  generalize psiF 128 = P at h1 h3
  generalize (ballC 128 : ℝ) = N at h1 h4
  generalize (ballC T : ℝ) * (T : ℝ)⁻¹ ^ 2 = Z at h1 h2
  norm_num at h1 h3 h4
  linarith

/-- **`ψ(t) ≤ 17 t` for `t ≥ 33`.** -/
theorem psi_le (t : ℕ) (ht : 33 ≤ t) : psiF t ≤ 17 * (t : ℝ) := by
  by_cases h44 : t < 44
  · have h1 := psi_fin (t := 44) (by norm_num) (by norm_num) psi_44
    have h2 := psiF_mono (show t ≤ 44 by omega)
    have h3 : (33 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 33 ≤ t by omega)
    norm_num at h1
    linarith
  by_cases h59 : t < 59
  · have h1 := psi_fin (t := 59) (by norm_num) (by norm_num) psi_59
    have h2 := psiF_mono (show t ≤ 59 by omega)
    have h3 : (44 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 44 ≤ t by omega)
    norm_num at h1
    linarith
  by_cases h79 : t < 79
  · have h1 := psi_fin (t := 79) (by norm_num) (by norm_num) psi_79
    have h2 := psiF_mono (show t ≤ 79 by omega)
    have h3 : (59 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 59 ≤ t by omega)
    norm_num at h1
    linarith
  by_cases h106 : t < 106
  · have h1 := psi_fin (t := 106) (by norm_num) (by norm_num) psi_106
    have h2 := psiF_mono (show t ≤ 106 by omega)
    have h3 : (79 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 79 ≤ t by omega)
    norm_num at h1
    linarith
  by_cases h128 : t < 128
  · have h1 := psi_fin (t := 128) (by norm_num) (by norm_num) psi_128
    have h2 := psiF_mono (show t ≤ 128 by omega)
    have h3 : (106 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 106 ≤ t by omega)
    norm_num at h1
    linarith
  exact psi_large t (by omega)

end Row
end OVNS
