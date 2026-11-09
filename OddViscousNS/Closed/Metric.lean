import OddViscousNS.Closed.Defs

/-!
# The metric `h` and the energies `X, Y, Z`: elementary facts

`h(1) = 1`, `h` is strictly increasing on `j ≥ 1`, `.29 j ≤ h(j) ≤ j`, `h(j) ≤ (2 + j²)/3`,
`h(j) = 29j/100 + 117/500` for `j ≥ 33`, the supporting line `j h(j) ≥ ℓ h(j) − c` with
`ℓ = 13191/212`, `c = 63940773/212000`, and the comparison of `X, Y, Z` with the Sobolev norms.
-/

open scoped ENNReal

namespace OVNS

/-- `h(1) = 1`. -/
theorem hmet_one : hmet 1 = 1 := by
  norm_num [hmet, hmetTable]

/-- `h` is affine for `j ≥ 33`. -/
theorem hmet_affine {j : ℕ} (hj : 33 ≤ j) : hmet j = 29 * (j : ℝ) / 100 + 117 / 500 := by
  simp [hmet, show j ≠ 0 by omega, show ¬ j ≤ 32 by omega]

/-- `h(j) > 0` for `j ≥ 1`. -/
theorem hmet_pos {j : ℕ} (hj : 1 ≤ j) : 0 < hmet j := by
  rcases le_or_gt j 32 with h | h
  · interval_cases j <;> norm_num [hmet, hmetTable]
  · rw [hmet_affine (by omega)]; positivity

/-- One-step strict monotonicity of `h`. -/
private theorem hmet_succ {j : ℕ} (hj : 1 ≤ j) : hmet j < hmet (j + 1) := by
  rcases le_or_gt j 32 with h | h
  · interval_cases j <;> norm_num [hmet, hmetTable]
  · rw [hmet_affine (by omega), hmet_affine (by omega)]
    push_cast; linarith

/-- `h` is strictly increasing on `j ≥ 1`. -/
theorem hmet_lt_hmet {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : hmet i < hmet j := by
  induction j, hij using Nat.le_induction with
  | base => exact hmet_succ hi
  | succ n hn ih => exact ih.trans (hmet_succ (by omega))

/-- `.29 j ≤ h(j)`. -/
theorem hmet_lower {j : ℕ} (hj : 1 ≤ j) : 29 / 100 * (j : ℝ) ≤ hmet j := by
  rcases le_or_gt j 32 with h | h
  · interval_cases j <;> norm_num [hmet, hmetTable]
  · rw [hmet_affine (by omega)]; linarith

/-- `h(j) ≤ j`. -/
theorem hmet_upper (j : ℕ) : hmet j ≤ j := by
  rcases le_or_gt j 32 with h | h
  · interval_cases j <;> norm_num [hmet, hmetTable]
  · rw [hmet_affine (by omega)]
    have : (33 : ℝ) ≤ j := by exact_mod_cast h
    linarith

/-- `h(j) ≤ (2 + j²)/3`. -/
theorem hmet_le_quad (j : ℕ) : hmet j ≤ (2 + (j : ℝ) ^ 2) / 3 := by
  rcases le_or_gt j 32 with h | h
  · interval_cases j <;> norm_num [hmet, hmetTable]
  · rw [hmet_affine (by omega)]
    have : (33 : ℝ) ≤ j := by exact_mod_cast h
    nlinarith

/-- The supporting line of `moment_cubic.tex`: exact on shells 24 and 25. -/
theorem hmet_support_line {j : ℕ} (hj : 1 ≤ j) :
    13191 / 212 * hmet j - 63940773 / 212000 ≤ (j : ℝ) * hmet j := by
  rcases le_or_gt j 32 with h | h
  · interval_cases j <;> norm_num [hmet, hmetTable]
  · rw [hmet_affine (by omega)]
    have : (33 : ℝ) ≤ j := by exact_mod_cast h
    nlinarith [mul_nonneg (sub_nonneg.2 this) (sub_nonneg.2 this)]

/-- `nsq k` cast to `ℝ` is `|k|²`. -/
theorem nsq_cast (k : Mode) : (nsq k : ℝ) = absSq k := by
  simp only [nsq, absSq, Nat.cast_sum, Nat.cast_pow]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

/-- `nsq k = 0` iff `k = 0`. -/
theorem nsq_eq_zero_iff (k : Mode) : nsq k = 0 ↔ k = 0 := by
  simp only [nsq, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies, pow_eq_zero_iff,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Int.natAbs_eq_zero, funext_iff,
    Pi.zero_apply]

/-- The `H⁰` weight is `1` off the zero mode. -/
private theorem sobWeight_zero' {k : Mode} (hk : k ≠ 0) : sobWeight 0 k = 1 := by
  simp [sobWeight, hk]

/-- The `H¹` weight is `|k|²`. -/
private theorem sobWeight_one' {k : Mode} (hk : k ≠ 0) : sobWeight 1 k = absSq k := by
  have h0 : 0 ≤ absSq k := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  simp only [sobWeight, hk, ↓reduceIte]
  rw [absk, mul_one, Real.rpow_two, Real.sq_sqrt h0]

/-- The `H²` weight is `|k|⁴`. -/
private theorem sobWeight_two' {k : Mode} (hk : k ≠ 0) : sobWeight 2 k = absSq k ^ 2 := by
  have h0 : 0 ≤ absSq k := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  simp only [sobWeight, hk, ↓reduceIte]
  rw [absk, show (2 : ℝ) * 2 = (4 : ℕ) by norm_num, Real.rpow_natCast,
    show 4 = 2 * 2 by rfl, pow_mul, Real.sq_sqrt h0]

/-- Nonzero modes have `nsq ≥ 1`. -/
private theorem one_le_nsq {k : Mode} (hk : k ≠ 0) : 1 ≤ nsq k :=
  Nat.one_le_iff_ne_zero.2 fun h ↦ hk ((nsq_eq_zero_iff k).1 h)

/-- The zero mode has `h = 0`. -/
private theorem hmet_nsq_zero : hmet (nsq 0) = 0 := by
  simp [hmet, nsq]

/-- `X = ‖w‖₀²`. -/
theorem Xmet_eq (w : Field) : Xmet w = hsE 0 w := by
  refine tsum_congr fun k ↦ ?_
  by_cases hk : k = 0
  · simp [hk, sobWeight]
  · simp only [hk, ↓reduceIte, sobWeight_zero' hk, one_mul]

/-- `Y ≤ ‖w‖₁²` (from `h(j) ≤ j`). -/
theorem Ymet_le (w : Field) : Ymet w ≤ hsE 1 w := by
  refine tsum_le_tsum fun k ↦ ENNReal.ofReal_le_ofReal ?_
  by_cases hk : k = 0
  · subst hk; simp [hmet_nsq_zero, sobWeight]
  · rw [sobWeight_one' hk, ← nsq_cast]
    exact mul_le_mul_of_nonneg_right (hmet_upper _) (sq_nonneg _)

/-- `Z ≤ ‖w‖₂²` (from `h(j) ≤ j`). -/
theorem Zmet_le (w : Field) : Zmet w ≤ hsE 2 w := by
  refine tsum_le_tsum fun k ↦ ENNReal.ofReal_le_ofReal ?_
  by_cases hk : k = 0
  · subst hk; simp [hmet_nsq_zero, sobWeight]
  · rw [sobWeight_two' hk, ← nsq_cast, sq (nsq k : ℝ)]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left (hmet_upper _) (Nat.cast_nonneg _)

/-- `.29 ‖w‖₁² ≤ Y`. -/
theorem hsE_one_le_Ymet (w : Field) : ENNReal.ofReal (29 / 100) * hsE 1 w ≤ Ymet w := by
  rw [hsE, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun k ↦ ?_
  rw [← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hk : k = 0
  · subst hk; simp [hmet_nsq_zero, sobWeight]
  · rw [sobWeight_one' hk, ← nsq_cast, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hmet_lower (one_le_nsq hk)) (sq_nonneg _)

/-- `.29 ‖w‖₂² ≤ Z`. -/
theorem hsE_two_le_Zmet (w : Field) : ENNReal.ofReal (29 / 100) * hsE 2 w ≤ Zmet w := by
  rw [hsE, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun k ↦ ?_
  rw [← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hk : k = 0
  · subst hk; simp [hmet_nsq_zero, sobWeight]
  · rw [sobWeight_two' hk, ← nsq_cast]
    have h1 := hmet_lower (one_le_nsq hk)
    have h2 : (0 : ℝ) ≤ nsq k := Nat.cast_nonneg _
    have h3 : 0 ≤ ‖w k‖ ^ 2 := sq_nonneg _
    have : 29 / 100 * ((nsq k : ℝ) ^ 2) ≤ (nsq k : ℝ) * hmet (nsq k) := by nlinarith
    nlinarith

/-- `Y ≤ (2X + hsE 2)/3`, the shell inequality `h(j) ≤ (2 + j²)/3` summed. -/
theorem Ymet_le_quad (w : Field) : 3 * Ymet w ≤ 2 * Xmet w + hsE 2 w := by
  rw [Ymet, Xmet, hsE, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← tsum_add]
  refine tsum_le_tsum fun k ↦ ?_
  by_cases hk : k = 0
  · subst hk; simp [hmet_nsq_zero]
  · simp only [hk, ↓reduceIte]
    rw [sobWeight_two' hk, ← nsq_cast]
    have h3 : 0 ≤ ‖w k‖ ^ 2 := sq_nonneg _
    have h4 : 0 ≤ (nsq k : ℝ) ^ 2 * ‖w k‖ ^ 2 := by positivity
    have := hmet_le_quad (nsq k)
    have key : ENNReal.ofReal (3 * (hmet (nsq k) * ‖w k‖ ^ 2)) ≤
        ENNReal.ofReal (2 * ‖w k‖ ^ 2 + (nsq k : ℝ) ^ 2 * ‖w k‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal (by nlinarith)
    rwa [ENNReal.ofReal_add (by positivity) h4,
      ENNReal.ofReal_mul (p := 3) (by norm_num), ENNReal.ofReal_mul (p := 2) (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat] at key

end OVNS
