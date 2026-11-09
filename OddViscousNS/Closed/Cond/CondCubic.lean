import OddViscousNS.Closed.Cond.LLH
import OddViscousNS.Closed.Cond.RestChain
import OddViscousNS.Closed.Cond.Deficit

/-!
# The conditional cubic bound (Theorem 3.2 of the U785 reconstruction)

`|⟨B(w,w),h(A)w⟩| ≤ C_cond(ρ, t, q) √Y Z` for every admissible `w`, under the row bound `M₀`:
the whole bound `κ₀` (`cubic_le_kappa`), and `|LLH| + |rest| ≤ (c₁ r √q + √(M₀(1+a)G)) √Y Z`
from `triadLLH_le`, `triadRest_le` and `deficit_bound` applied to `P_k = A_k h_k ‖w_k‖²/Z`.
-/

open scoped ENNReal

namespace OVNS

private lemma hm_zero_cc : hm 0 = 0 := by
  simp [hm, hmet, nsq]

private lemma absSq_zero_cc : absSq 0 = 0 := by
  simp [absSq]

private lemma hm_neg_cc (k : Mode) : hm (-k) = hm k := by
  simp [hm, nsq, Int.natAbs_neg]

private lemma hm_nonneg_cc (k : Mode) : 0 ≤ hm k := by
  by_cases hk : k = 0
  · rw [hk, hm_zero_cc]
  · exact (hmet_pos (Nat.one_le_iff_ne_zero.2 fun h ↦ hk ((nsq_eq_zero_iff k).1 h))).le

private lemma Pk_tsum_div_cc {u : Field} : ∑' j, Pk u j / absSq j = tYZ u := by
  have h : ∀ j, Pk u j / absSq j = hm j * ‖u j‖ ^ 2 / Zr u := fun j ↦ by
    by_cases hj : j = 0
    · simp [hj, absSq_zero_cc, hm_zero_cc]
    · have := (lt_of_lt_of_le one_pos (one_le_absSq hj)).ne'
      unfold Pk
      field_simp
  simp_rw [h]
  rw [tsum_div_const]
  rfl

private lemma Pk_shell_cc {u : Field} :
    ∑' k, (if nsq k = 1 then Pk u k else 0) = x1 u / Zr u := by
  have h : ∀ k, (if nsq k = 1 then Pk u k else 0) =
      (if nsq k = 1 then ‖u k‖ ^ 2 else 0) / Zr u := fun k ↦ by
    split_ifs with hk
    · have hA : absSq k = 1 := by rw [← nsq_cast, hk]; norm_num
      simp [Pk, hA, hm, hk, hmet_one]
    · simp
  simp_rw [h]
  rw [tsum_div_const]
  rfl

/-- The deficit bound for the law `Pk w`, in the variables `ρ = ρw w`, `t = tYZ w`. -/
private lemma deficit_w {w : Field} (hw : Adm 2 w) (hY : 0 < Yr w) (hZ : 0 < Zr w) :
    (∑' k, Real.sqrt (Qk w k * Rk' w k)) ^ 2 ≤ (1 + aC) * Gfun (1 - (ρw w * tYZ w) ^ 2)
      (max 0 (1 - ρw w * tYZ w * ρw w - DLH (ρw w) (tYZ w))) := by
  have hPs : Summable (Pk w) := (summable_Z hw).div_const _
  have hP1 : ∑' k, Pk w k = 1 := by unfold Pk; rw [tsum_div_const]; exact div_self hZ.ne'
  have hA := deficit_bound (Pk w)
    (fun k ↦ div_nonneg (mul_nonneg (mul_nonneg (absSq_nonneg k) (hm_nonneg_cc k))
      (sq_nonneg _)) hZ.le)
    (by simp [Pk, absSq_zero_cc]) (fun k ↦ by simp only [Pk, absSq_neg, hm_neg_cc, hw.real k,
      norm_conjV]) hPs hP1
  dsimp only at hA
  rw [Pk_tsum_div_cc, Pk_shell_cc] at hA
  have e1 : x1 w / Zr w = ρw w * tYZ w := by
    unfold ρw tYZ; field_simp
  have e2 : ρw w * tYZ w / tYZ w = ρw w := by
    unfold tYZ; field_simp
  rw [e1, e2] at hA
  exact hA

/-- The conditional cubic bound `|cubic w| ≤ C_cond(ρ,t,q) √Y Z`. -/
theorem cubic_le_cond (hRB : RowBound fun _ => M₀) {w : Field} (hw : Adm 2 w) :
    |cubic w| ≤ Ccond (ρw w) (tYZ w) (qw w) * Real.sqrt (Yr w) * Zr w := by
  have hZ0 : 0 ≤ Zr w := (Yr_le_Zr hw).trans' (le_trans (x1_nonneg hw)
    ((x1_le_Xr hw).trans (Xr_le_Yr hw)))
  have hK := cubic_le_kappa hRB hw
  unfold Ccond
  rw [mul_assoc, min_mul_of_nonneg _ _ (mul_nonneg (Real.sqrt_nonneg _) hZ0)]
  refine le_min (by rw [← mul_assoc]; exact hK) ?_
  by_cases hw0 : w = 0
  · have hZ : Zr w = 0 := by subst hw0; simp [Zr]
    simp only [hZ, mul_zero] at hK ⊢
    exact hK
  have hY := Yr_pos_of_ne hw hw0
  have hZ := Zr_pos_of_ne hw hw0
  have hM : (0 : ℝ) ≤ M₀ := by norm_num [M₀]
  have hS : ∑' k, Real.sqrt (Qk w k * Rk' w k) ≤
      Real.sqrt ((1 + aC) * Gfun (1 - (ρw w * tYZ w) ^ 2)
      (max 0 (1 - ρw w * tYZ w * ρw w - DLH (ρw w) (tYZ w)))) := by
    rw [← Real.sqrt_sq (tsum_nonneg fun k ↦ Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (deficit_w hw hY hZ)
  have heq : ∑' k, Real.sqrt (M₀ * Qk w k * Rk' w k)
      = Real.sqrt M₀ * ∑' k, Real.sqrt (Qk w k * Rk' w k) := by
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [mul_assoc, Real.sqrt_mul hM]
  have hT : ∑' k, Real.sqrt (M₀ * Qk w k * Rk' w k) ≤ Real.sqrt (M₀ * (1 + aC) *
      Gfun (1 - (ρw w * tYZ w) ^ 2)
        (max 0 (1 - ρw w * tYZ w * ρw w - DLH (ρw w) (tYZ w)))) := by
    rw [heq, mul_assoc M₀, Real.sqrt_mul hM]
    exact mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg _)
  have hL : c1 * x1 w * Real.sqrt (Y2r w) =
      c1 * (ρw w * tYZ w) * Real.sqrt (qw w) * (Real.sqrt (Yr w) * Zr w) := by
    have hq : Real.sqrt (qw w) * Real.sqrt (Yr w) = Real.sqrt (Y2r w) := by
      rw [← Real.sqrt_mul' _ hY.le]; unfold qw; congr 1; field_simp
    rw [← hq]; unfold ρw tYZ; field_simp
  rw [cubic_eq_LLH_add_rest hw]
  calc |triadLLH w + triadRest w| ≤ |triadLLH w| + |triadRest w| := abs_add_le _ _
    _ ≤ c1 * x1 w * Real.sqrt (Y2r w) +
        Real.sqrt (Yr w) * Zr w * ∑' k, Real.sqrt (M₀ * Qk w k * Rk' w k) :=
      add_le_add (triadLLH_le hw) (triadRest_le hRB hw)
    _ ≤ _ := by
      rw [hL, add_mul]
      refine add_le_add le_rfl ?_
      rw [mul_comm _ (Real.sqrt (Yr w) * Zr w)]
      exact mul_le_mul_of_nonneg_left hT (mul_nonneg (Real.sqrt_nonneg _) hZ.le)

end OVNS
