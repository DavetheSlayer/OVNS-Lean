import OddViscousNS.Quant.Joint.Metric.ZHeat

/-!
# The Fejér low pass (step J5, node N6)

Body 27, Body 42: a smooth low-pass multiplier, equal to one near zero, with compact support and
uniformly bounded `L¹` kernel.  Here it is the de la Vallée-Poussin trapezoid
`vp N n = 2 fej (2N + 1) n − fej N n`, a difference of Fejér multipliers.

`fej N n = (1 − |n|/(N+1))₊` is the Fourier coefficient of the positive kernel
`|D_N|²/(N + 1)`, so `fejer_avg`: the Fejér mean is an average of translates, and it contracts the
sup norm.  The trapezoid has norm at most `3`, per coordinate.
-/

open MeasureTheory Set Filter UnitAddTorus Finset
open scoped ENNReal ComplexConjugate Real

noncomputable section

namespace OVNS.Quant.Metric

/-- The Fejér multiplier. -/
def fej (N : ℕ) (n : ℤ) : ℝ := max 0 (1 - |(n : ℝ)| / (N + 1))

/-- The character. -/
def chr (m : ℤ) (t : ℝ) : ℂ := Complex.exp ((2 * π * Complex.I * (m : ℤ)) * t)

lemma chr_add (m n : ℤ) (t : ℝ) : chr (m + n) t = chr m t * chr n t := by
  simp only [chr, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma chr_zero (t : ℝ) : chr 0 t = 1 := by simp [chr]

lemma conj_chr (m : ℤ) (t : ℝ) : conj (chr m t) = chr (-m) t := by
  simp only [chr, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast,
    map_ofNat]
  congr 1
  push_cast
  ring

lemma norm_chr (m : ℤ) (t : ℝ) : ‖chr m t‖ = 1 := by
  have : (2 * π * Complex.I * (m : ℤ)) * t = ((2 * π * m * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [chr, this, Complex.norm_exp_ofReal_mul_I]

lemma continuous_chr (m : ℤ) : Continuous (chr m) := by
  unfold chr
  fun_prop

/-- Orthogonality on the unit interval. -/
lemma integral_chr (m : ℤ) : ∫ t in (0 : ℝ)..1, chr m t = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [chr]
  · rw [ite_eq_right hm]
    have hc : (2 * π * Complex.I * (m : ℤ)) ≠ 0 := by
      simp [Real.pi_ne_zero, hm]
    have := integral_exp_mul_complex (a := (0 : ℝ)) (b := 1) hc
    simp only [chr]
    rw [this]
    have e : (2 * π * Complex.I * (m : ℤ)) * ((1 : ℝ) : ℂ) = (m : ℂ) * (2 * π * Complex.I) := by
      push_cast
      ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- The Dirichlet sum. -/
def dirD (N : ℕ) (t : ℝ) : ℂ := ∑ a ∈ range (N + 1), chr a t

/-- The Fejér kernel. -/
def gR (N : ℕ) (t : ℝ) : ℝ := ‖dirD N t‖ ^ 2 / (N + 1)

lemma gR_nonneg (N : ℕ) (t : ℝ) : 0 ≤ gR N t := by
  unfold gR
  positivity

lemma continuous_gR (N : ℕ) : Continuous (gR N) := by
  unfold gR dirD
  have : Continuous fun t => ∑ a ∈ range (N + 1), chr (a : ℤ) t :=
    continuous_finsetSum _ fun a _ => continuous_chr a
  fun_prop

/-- The Fejér kernel as a double sum. -/
lemma gR_eq (N : ℕ) (t : ℝ) : ((gR N t : ℝ) : ℂ) = (1 / (N + 1) : ℂ) *
    ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), chr ((a : ℤ) - b) t := by
  have h1 : ((‖dirD N t‖ ^ 2 : ℝ) : ℂ) = dirD N t * conj (dirD N t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [gR]
  rw [Complex.ofReal_div, h1, dirD, map_sum, Finset.sum_mul_sum]
  simp only [conj_chr, ← chr_add]
  push_cast
  rw [div_eq_mul_inv, mul_comm, one_div]
  rfl

/-- The count of the pairs with a given difference. -/
lemma count_nat (N m : ℕ) :
    ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), (if (a : ℤ) - b + m = 0 then (1 : ℝ) else 0) =
      ((N + 1 - m : ℕ) : ℝ) := by
  have h : ∀ a : ℕ, ∑ b ∈ range (N + 1), (if (a : ℤ) - b + m = 0 then (1 : ℝ) else 0) =
      if a + m < N + 1 then 1 else 0 := fun a => by
    have e : ∀ b : ℕ, ((a : ℤ) - b + m = 0) ↔ (b = a + m) := fun b => by omega
    simp only [e]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range]
  simp only [h]
  rw [Finset.sum_boole]
  have e : ({a ∈ range (N + 1) | a + m < N + 1} : Finset ℕ) = range (N + 1 - m) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [e, Finset.card_range]

lemma count_pairs (N : ℕ) (n : ℤ) :
    ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), (if (a : ℤ) - b + n = 0 then (1 : ℝ) else 0) =
      max 0 ((N : ℝ) + 1 - |(n : ℝ)|) := by
  have hm : ∀ m : ℕ, ((N + 1 - m : ℕ) : ℝ) = max 0 ((N : ℝ) + 1 - m) := fun m => by
    by_cases h : m ≤ N + 1
    · rw [Nat.cast_sub h]
      push_cast
      rw [max_eq_right]
      have : (m : ℝ) ≤ N + 1 := by exact_mod_cast h
      linarith
    · rw [Nat.sub_eq_zero_of_le (by omega)]
      have : (N : ℝ) + 1 ≤ m := by
        exact_mod_cast (by omega : N + 1 ≤ m)
      rw [max_eq_left (by linarith)]
      simp
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have := count_nat N m
    rw [this, hm]
    simp
  · have e : ∀ a b : ℕ, ((a : ℤ) - b + -(m : ℤ) = 0) ↔ ((b : ℤ) - a + m = 0) := fun a b => by omega
    simp only [e]
    rw [Finset.sum_comm, count_nat, hm]
    simp

lemma chr_ii (m : ℤ) : IntervalIntegrable (chr m) volume 0 1 :=
  (continuous_chr m).intervalIntegrable _ _

lemma inner_int (N : ℕ) (n : ℤ) (a : ℕ) :
    ∫ t in (0 : ℝ)..1, ∑ b ∈ range (N + 1), chr ((a : ℤ) - b + n) t = ∑ b ∈ range (N + 1),
      (((if (a : ℤ) - b + n = 0 then (1 : ℝ) else 0) : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_finsetSum fun b _ => chr_ii _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_chr]
  split_ifs <;> simp

lemma double_int (N : ℕ) (n : ℤ) :
    ∫ t in (0 : ℝ)..1, ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), chr ((a : ℤ) - b + n) t =
      ((max 0 ((N : ℝ) + 1 - |(n : ℝ)|) : ℝ) : ℂ) := by
  have hi : ∀ a ∈ range (N + 1), IntervalIntegrable
      (fun t => ∑ b ∈ range (N + 1), chr ((a : ℤ) - b + n) t) volume 0 1 := fun a _ =>
    ((continuous_finsetSum _ fun b _ => continuous_chr _).intervalIntegrable _ _)
  rw [intervalIntegral.integral_finsetSum hi, Finset.sum_congr rfl fun a _ => inner_int N n a]
  simp only [← Complex.ofReal_sum]
  rw [count_pairs]

lemma fej_eq (N : ℕ) (n : ℤ) : fej N n = 1 / (N + 1) * max 0 ((N : ℝ) + 1 - |(n : ℝ)|) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  unfold fej
  by_cases h : |(n : ℝ)| ≤ N + 1
  · have h1 : 0 ≤ 1 - |(n : ℝ)| / (N + 1) := by
      rw [sub_nonneg, div_le_one hN]
      exact h
    have h2 : 0 ≤ (N : ℝ) + 1 - |(n : ℝ)| := by linarith
    rw [max_eq_right h1, max_eq_right h2]
    field_simp
  · rw [not_le] at h
    have h1 : 1 - |(n : ℝ)| / (N + 1) ≤ 0 := by
      rw [sub_nonpos, one_le_div hN]
      exact h.le
    have h2 : (N : ℝ) + 1 - |(n : ℝ)| ≤ 0 := by linarith
    rw [max_eq_left h1, max_eq_left h2]
    simp

/-- The Fourier coefficient of the Fejér kernel. -/
lemma integral_gR (N : ℕ) (n : ℤ) :
    ∫ t in (0 : ℝ)..1, ((gR N t : ℝ) : ℂ) * chr n t = ((fej N n : ℝ) : ℂ) := by
  have e : ∀ t : ℝ, ((gR N t : ℝ) : ℂ) * chr n t = (1 / (N + 1) : ℂ) *
      ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), chr ((a : ℤ) - b + n) t := fun t => by
    rw [gR_eq, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => (chr_add _ _ _).symm
  have h1 : (fun t : ℝ => ((gR N t : ℝ) : ℂ) * chr n t) = fun t : ℝ => (1 / (N + 1) : ℂ) *
      ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), chr ((a : ℤ) - b + n) t := funext e
  rw [h1, intervalIntegral.integral_const_mul, double_int, fej_eq]
  push_cast
  rfl

lemma fej_zero (N : ℕ) : fej N 0 = 1 := by simp [fej]

/-- The mass of the Fejér kernel. -/
lemma integral_gR_real (N : ℕ) : ∫ t in Ioc (0 : ℝ) 1, gR N t = 1 := by
  have h := integral_gR N 0
  simp only [chr_zero, mul_one, fej_zero, Complex.ofReal_one] at h
  rw [intervalIntegral.integral_of_le zero_le_one, integral_complex_ofReal] at h
  exact_mod_cast h

/-- **The Fejér mean is an average of translates.** -/
lemma fejer_avg {ι : Type*} [Countable ι] (N : ℕ) {n : ι → ℤ} {w : ι → V3}
    (hw : Summable fun k => ‖w k‖) {M : ℝ} (hM : ∀ t : ℝ, ‖∑' k, chr (n k) t • w k‖ ≤ M) :
    ‖∑' k, ((fej N (n k) : ℝ) : ℂ) • w k‖ ≤ M := by
  set μ₀ : Measure ℝ := volume.restrict (Ioc 0 1) with hμ
  have hgc := continuous_gR N
  have hG : Integrable (gR N) μ₀ := hgc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hc : ∀ m : ℤ, Integrable (fun t => ((gR N t : ℝ) : ℂ) * chr m t) μ₀ := fun m => by
    have : Continuous fun t => ((gR N t : ℝ) : ℂ) * chr m t :=
      (Complex.continuous_ofReal.comp hgc).mul (continuous_chr m)
    exact this.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint : ∀ k, Integrable (fun t => (((gR N t : ℝ) : ℂ) * chr (n k) t) • w k) μ₀ := fun k =>
    (hc (n k)).smul_const _
  have hnorm : ∀ k, ∫ t, ‖(((gR N t : ℝ) : ℂ) * chr (n k) t) • w k‖ ∂μ₀ = ‖w k‖ := fun k => by
    have e : ∀ t, ‖(((gR N t : ℝ) : ℂ) * chr (n k) t) • w k‖ = gR N t * ‖w k‖ := fun t => by
      rw [norm_smul, norm_mul, norm_chr, Complex.norm_real, Real.norm_of_nonneg (gR_nonneg N t),
        mul_one]
    simp only [e]
    rw [integral_mul_const, integral_gR_real, one_mul]
  have hsum : Summable fun k => ∫ t, ‖(((gR N t : ℝ) : ℂ) * chr (n k) t) • w k‖ ∂μ₀ := by
    simp only [hnorm]
    exact hw
  have hS := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ k, ∫ t, (((gR N t : ℝ) : ℂ) * chr (n k) t) • w k ∂μ₀ =
      ((fej N (n k) : ℝ) : ℂ) • w k := fun k => by
    rw [integral_smul_const, ← integral_gR, intervalIntegral.integral_of_le zero_le_one]
  simp only [hval] at hS
  rw [hS.tsum_eq]
  have hbi : Integrable (fun t => gR N t * M) μ₀ := hG.mul_const M
  have hle : ∀ t, ‖∑' k, (((gR N t : ℝ) : ℂ) * chr (n k) t) • w k‖ ≤ gR N t * M := fun t => by
    have e : ∑' k, (((gR N t : ℝ) : ℂ) * chr (n k) t) • w k =
        ((gR N t : ℝ) : ℂ) • ∑' k, chr (n k) t • w k := by
      rw [← tsum_const_smul'']
      exact tsum_congr fun k => mul_smul _ _ _
    rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg (gR_nonneg N t)]
    exact mul_le_mul_of_nonneg_left (hM t) (gR_nonneg N t)
  refine (norm_integral_le_of_norm_le hbi (Eventually.of_forall hle)).trans ?_
  rw [integral_mul_const, integral_gR_real, one_mul]

/-! ### The trapezoid -/

/-- The de la Vallée-Poussin multiplier: `1` on `|n| ≤ N + 1`, `0` on `|n| ≥ 2N + 2`. -/
def vp (N : ℕ) (n : ℤ) : ℝ := 2 * fej (2 * N + 1) n - fej N n

lemma fej_two (N : ℕ) (n : ℤ) : fej (2 * N + 1) n = max 0 (1 - |(n : ℝ)| / (2 * (N + 1))) := by
  unfold fej
  push_cast
  have : (2 * (N : ℝ) + 1 + 1) = 2 * (N + 1) := by ring
  rw [this]

lemma vp_one {N : ℕ} {n : ℤ} (h : |(n : ℝ)| ≤ N + 1) : vp N n = 1 := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  unfold vp
  rw [fej_two]
  unfold fej
  set x := |(n : ℝ)|
  have h1 : 0 ≤ 1 - x / (N + 1) := by
    rw [sub_nonneg, div_le_one hN]
    exact h
  have e : x / (2 * ((N : ℝ) + 1)) = (x / (N + 1)) / 2 := by
    field_simp
  rw [e]
  rw [max_eq_right h1, max_eq_right (by linarith)]
  ring

lemma vp_zero {N : ℕ} {n : ℤ} (h : 2 * ((N : ℝ) + 1) ≤ |(n : ℝ)|) : vp N n = 0 := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  unfold vp
  rw [fej_two]
  unfold fej
  set x := |(n : ℝ)|
  have h1 : 1 - x / (2 * ((N : ℝ) + 1)) ≤ 0 := by
    rw [sub_nonpos, one_le_div (by positivity)]
    exact h
  have h2 : 1 - x / ((N : ℝ) + 1) ≤ 0 := by
    rw [sub_nonpos, one_le_div hN]
    linarith
  rw [max_eq_left h1, max_eq_left h2]
  ring

lemma vp_nonneg (N : ℕ) (n : ℤ) : 0 ≤ vp N n := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  by_cases h : |(n : ℝ)| ≤ N + 1
  · rw [vp_one h]
    exact zero_le_one
  rw [not_le] at h
  unfold vp
  rw [fej_two]
  unfold fej
  set x := |(n : ℝ)|
  have h2 : 1 - x / ((N : ℝ) + 1) ≤ 0 := by
    rw [sub_nonpos, one_le_div hN]
    exact h.le
  rw [max_eq_left h2]
  have := le_max_left 0 (1 - x / (2 * ((N : ℝ) + 1)))
  linarith

lemma vp_le_one (N : ℕ) (n : ℤ) : vp N n ≤ 1 := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  by_cases h : |(n : ℝ)| ≤ N + 1
  · rw [vp_one h]
  rw [not_le] at h
  unfold vp
  rw [fej_two]
  unfold fej
  set x := |(n : ℝ)|
  have h2 : 1 - x / ((N : ℝ) + 1) ≤ 0 := by
    rw [sub_nonpos, one_le_div hN]
    exact h.le
  rw [max_eq_left h2]
  have e : x / (2 * ((N : ℝ) + 1)) = (x / (N + 1)) / 2 := by
    field_simp
  rw [e]
  have h3 : 1 ≤ x / (N + 1) := by
    rw [one_le_div hN]
    exact h.le
  by_cases h4 : 0 ≤ 1 - x / ((N : ℝ) + 1) / 2
  · rw [max_eq_right h4]
    linarith
  · rw [not_le] at h4
    rw [max_eq_left h4.le]
    norm_num

lemma vp_neg (N : ℕ) (n : ℤ) : vp N (-n) = vp N n := by
  simp [vp, fej]

open GN (SupBd)

/-- The trapezoid in the coordinate `i`. -/
def mulD (i : Fin 3) (N : ℕ) (S : Field) : Field := fun k => ((vp N (k i) : ℝ) : ℂ) • S k

lemma norm_mulD (i : Fin 3) (N : ℕ) (S : Field) (k : Mode) :
    ‖mulD i N S k‖ = vp N (k i) * ‖S k‖ := by
  rw [mulD, norm_smul, Complex.norm_real, Real.norm_of_nonneg (vp_nonneg _ _)]

lemma norm_mulD_le (i : Fin 3) (N : ℕ) (S : Field) (k : Mode) : ‖mulD i N S k‖ ≤ ‖S k‖ := by
  rw [norm_mulD]
  exact mul_le_of_le_one_left (norm_nonneg _) (vp_le_one _ _)

/-- **The trapezoid contracts the sup norm, up to `3`.** -/
theorem supBd_mulD {S : Field} (hs : Summable fun k => ‖S k‖) {M : ℝ} (hM : SupBd S M)
    (i : Fin 3) (N : ℕ) : SupBd (mulD i N S) (3 * M) := by
  intro x
  have hnw : ∀ k, ‖mFourier k x • S k‖ ≤ ‖S k‖ := fun k => by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (GN.norm_mFourier_le k x)
  have hw : Summable fun k => ‖mFourier k x • S k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnw hs
  have hT : ∀ t : ℝ, ‖∑' k : Mode, chr (k i) t • mFourier k x • S k‖ ≤ M := fun t => by
    have e : ∀ k : Mode, chr (k i) t • mFourier k x • S k =
        mFourier k (shiftT i x t) • S k := fun k => by
      rw [mFourier_shift, smul_smul, mul_comm]
      rfl
    simp only [e]
    exact hM _
  have h1 := fejer_avg (2 * N + 1) (n := fun k : Mode => k i) hw hT
  have h2 := fejer_avg N (n := fun k : Mode => k i) hw hT
  have hs1 : ∀ m : ℕ, Summable fun k : Mode => ((fej m (k i) : ℝ) : ℂ) • mFourier k x • S k :=
    fun m => by
    refine Summable.of_norm_bounded hw fun k => ?_
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [abs_of_nonneg (le_max_left _ _)]
    refine max_le zero_le_one ?_
    have : 0 ≤ |((k i : ℤ) : ℝ)| / ((m : ℝ) + 1) := by positivity
    linarith
  have e : ∑' k : Mode, mFourier k x • mulD i N S k =
      (2 : ℂ) • ∑' k : Mode, ((fej (2 * N + 1) (k i) : ℝ) : ℂ) • mFourier k x • S k -
        ∑' k : Mode, ((fej N (k i) : ℝ) : ℂ) • mFourier k x • S k := by
    rw [← tsum_const_smul'', ← (hs1 (2 * N + 1) |>.const_smul (2 : ℂ)).tsum_sub (hs1 N)]
    refine tsum_congr fun k => ?_
    simp only [mulD, vp, smul_smul]
    rw [← sub_smul]
    congr 1
    push_cast
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul]
  have h2' : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2']
  linarith

end OVNS.Quant.Metric

end
