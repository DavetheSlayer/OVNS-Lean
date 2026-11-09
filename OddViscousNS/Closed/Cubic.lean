import OddViscousNS.Closed.RowChain
import OddViscousNS.Closed.Affinity

/-!
# Lemma `weighted-cubic`: `|⟨B(w,w), h(A)w⟩| ≤ κ₀ √Y Z`, conditional on the row bound

Combining the row chain (`cubic_le_rowchain` with `g ≡ M₀`), the affinity bound applied to the
even probability law `P_k = A_k h_k ‖w_k‖²/Z` (even by reality of `w`), and the rational
comparison `M₀ F* < κ₀²` (`M₀_mul_Fstar_lt`).
-/

open scoped ENNReal

namespace OVNS

private lemma hm_pos' {k : Mode} (hk : k ≠ 0) : 0 < hm k :=
  hmet_pos (Nat.one_le_iff_ne_zero.2 fun h ↦ hk ((nsq_eq_zero_iff k).1 h))

private lemma hm_zero' : hm 0 = 0 := by
  simp [hm, hmet, nsq]

private lemma hm_nonneg' (k : Mode) : 0 ≤ hm k := by
  by_cases hk : k = 0
  · rw [hk, hm_zero']
  · exact (hm_pos' hk).le

private lemma absSq_zero' : absSq 0 = 0 := by
  simp [absSq]

private lemma aw_nonneg' (u : Field) (k : Mode) : 0 ≤ absSq k * hm k * ‖u k‖ ^ 2 :=
  mul_nonneg (mul_nonneg (absSq_nonneg k) (hm_nonneg' k)) (sq_nonneg _)

private lemma summable_aw' {u : Field} (hu : Adm 2 u) :
    Summable fun k ↦ absSq k * hm k * ‖u k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (aw_nonneg' u) (fun k ↦ ?_) hu.inH
  by_cases hk : k = 0
  · simp [hk, absSq_zero', sobWeight]
  · have h0 := absSq_nonneg k
    have hw : sobWeight 2 k = absSq k ^ 2 := by
      simp only [sobWeight, hk, ↓reduceIte]
      rw [absk, show (2 : ℝ) * 2 = (4 : ℕ) by norm_num, Real.rpow_natCast,
        show 4 = 2 * 2 by rfl, pow_mul, Real.sq_sqrt h0]
    have hh : hm k ≤ absSq k := by
      rw [← nsq_cast]; exact hmet_upper _
    rw [hw, sq (absSq k)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh h0) (sq_nonneg _)

private lemma hm_neg (k : Mode) : hm (-k) = hm k := by
  simp [hm, nsq, Int.natAbs_neg]

private lemma Pk_tsum_div {u : Field} : ∑' j, Pk u j / absSq j = tYZ u := by
  have h : ∀ j, Pk u j / absSq j = hm j * ‖u j‖ ^ 2 / Zr u := fun j ↦ by
    by_cases hj : j = 0
    · simp [hj, absSq_zero', hm_zero']
    · have := (lt_of_lt_of_le one_pos (one_le_absSq hj)).ne'
      unfold Pk
      field_simp
  simp_rw [h]
  rw [tsum_div_const]
  rfl

/-- The weighted cubic is bounded by `κ₀ √Y Z` under the row bound `M₀`. -/
theorem cubic_le_kappa (hRB : RowBound fun _ => M₀) {u : Field} (hu : Adm 2 u) :
    |cubic u| ≤ κ₀ * Real.sqrt (Yr u) * Zr u := by
  have hM : (0 : ℝ) < M₀ := by norm_num [M₀]
  have hc := cubic_le_rowchain (fun _ ↦ hM.le) (fun _ ↦ le_rfl) hRB hu
  have hZ0 : 0 ≤ Zr u := tsum_nonneg (aw_nonneg' u)
  by_cases hZ : Zr u = 0
  · rw [hZ, mul_zero, zero_mul] at hc
    rw [hZ, mul_zero]
    exact hc
  have hPs : Summable (Pk u) := (summable_aw' hu).div_const _
  have hP1 : ∑' k, Pk u k = 1 := by unfold Pk; rw [tsum_div_const]; exact div_self hZ
  have hA := affinity_bound (Pk u) (fun k ↦ div_nonneg (aw_nonneg' u k) hZ0)
    (by simp [Pk, absSq_zero']) (fun k ↦ by simp only [Pk, absSq_neg, hm_neg, hu.real k,
      norm_conjV]) hPs hP1
  rw [Pk_tsum_div] at hA
  have hS : ∑' k, Real.sqrt (Qk u k * Rk u k) ≤ Real.sqrt Fstar := by
    rw [← Real.sqrt_sq (tsum_nonneg fun k ↦ Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hA
  have heq : ∑' k, Real.sqrt (M₀ * Qk u k * Rk u k)
      = Real.sqrt M₀ * ∑' k, Real.sqrt (Qk u k * Rk u k) := by
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [mul_assoc, Real.sqrt_mul hM.le]
  have hκ : Real.sqrt M₀ * Real.sqrt Fstar ≤ κ₀ := by
    rw [← Real.sqrt_mul hM.le]
    calc Real.sqrt (M₀ * Fstar) ≤ Real.sqrt (κ₀ ^ 2) :=
        Real.sqrt_le_sqrt M₀_mul_Fstar_lt.le
      _ = κ₀ := Real.sqrt_sq (by norm_num [κ₀])
  have hT : ∑' k, Real.sqrt (M₀ * Qk u k * Rk u k) ≤ κ₀ := by
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg _)).trans hκ
  calc |cubic u| ≤ Real.sqrt (Yr u) * Zr u * ∑' k, Real.sqrt (M₀ * Qk u k * Rk u k) := hc
    _ ≤ Real.sqrt (Yr u) * Zr u * κ₀ :=
        mul_le_mul_of_nonneg_left hT (mul_nonneg (Real.sqrt_nonneg _) hZ0)
    _ = κ₀ * Real.sqrt (Yr u) * Zr u := by ring

/-- `RowBound` is monotone in the bound. -/
theorem RowBound.mono {g g' : ℕ → ℝ} (hRB : RowBound g) (hle : ∀ j, g j ≤ g' j) : RowBound g' := by
  intro k hk c hc
  refine (hRB k hk c hc).trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ hm k * ‖c‖ ^ 2 := mul_nonneg (hm_nonneg' k) (sq_nonneg _)
  have h1 := mul_le_mul_of_nonneg_right (hle (nsq k)) h0
  nlinarith

end OVNS
