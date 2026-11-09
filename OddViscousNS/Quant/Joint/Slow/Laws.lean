import OddViscousNS.Quant.Joint.Slow.Strain

/-!
# E7-P: the energy laws of the corrected slow field, with an `L²_t H¹` source

Step 1 and steps 7, 8 of `Joint/Slow/Plan.lean`.  The laws of `Energy/Slow/Energy.lean` with the
pointwise `Φ ≥ ‖corrRes‖₀` replaced by `‖corrRes‖₁²` under the integral (`corr_l2_law'`,
`corr_horiz_law'`: J4 pays only `L²_t H¹`), and the passive laws at the strain:
`vert_h1_law`, `horiz_h2_law`, `vert_h2_law`, `vert_h2_barrier`.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.Slow

open GN

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### Scalar and Young inequalities -/

/-- Young for the passive `H¹` laws. -/
private lemma young_one {P Q a b ρ Λ : ℝ} (hP : |P| ≤ b * ρ)
    (hQ : |Q| ≤ 2 * Λ * a ^ 2 + 10 * a * b) :
    2 * (P - Q) ≤ 1 * b ^ 2 + ((4 * Λ + 200) * a ^ 2 + 2 * ρ ^ 2) := by
  have h1 := le_abs_self P
  have h2 := neg_abs_le Q
  nlinarith [sq_nonneg (b - 2 * ρ), sq_nonneg (b - 20 * a)]

/-- Young for the passive `H²` law. -/
private lemma young_two {P Q a b d ρ Λ X : ℝ} (hX : 0 ≤ X) (hXe : X = Λ ^ 2 * a ^ 2 + 5 * a * b)
    (hP : |P| ≤ d * ρ)
    (hQ : |Q| ≤ 2 * Λ * b ^ 2 + 10 * b * d + 3 * d * Real.sqrt X) :
    2 * (P - Q) ≤ 3 / 4 * d ^ 2 + ((4 * Λ + 490) * b ^ 2 + (36 * Λ ^ 2 + 90) * a ^ 2 +
      4 * ρ ^ 2) := by
  have h1 := le_abs_self P
  have h2 := neg_abs_le Q
  have hs : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  nlinarith [sq_nonneg (d - 4 * ρ), sq_nonneg (d - 40 * b), sq_nonneg (d - 12 * Real.sqrt X),
    sq_nonneg (a - b)]

/-- The vertical drift of the barrier is nonpositive above `(10Λ + 500) A²`. -/
private lemma drift_nonpos {A Λ x : ℝ} (hA : 0 < A) (hΛ : 0 < Λ) (hx : (10 * Λ + 500) * A ^ 2 ≤ x) :
    -(x ^ 2 / A ^ 2) + (4 * Λ + 490) * x + (36 * Λ ^ 2 + 90) * A ^ 2 ≤ 0 := by
  have hA2 : 0 < A ^ 2 := by positivity
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have h1 : (4 * Λ + 490) * x + (36 * Λ ^ 2 + 90) * A ^ 2 ≤ x ^ 2 / A ^ 2 := by
    rw [le_div_iff₀ hA2]
    have h2 : (10 * Λ + 500) * A ^ 2 * x ≤ x * x := mul_le_mul_of_nonneg_right hx hx0
    have h3 : (36 * Λ ^ 2 + 90) * A ^ 2 ≤ (6 * Λ + 10) * x := by
      have h4 : (6 * Λ + 10) * ((10 * Λ + 500) * A ^ 2) ≤ (6 * Λ + 10) * x :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      nlinarith [mul_nonneg hΛ.le hA2.le, mul_nonneg (mul_nonneg hΛ.le hΛ.le) hA2.le]
    nlinarith
  linarith

/-! ### The coefficient sequences -/

private lemma sobWeight_nat {j : ℕ} {k : Mode} (hk : k ≠ 0) : sobWeight j k = absSq k ^ j := by
  have hw : sobWeight j k = absk k ^ (2 * (j : ℝ)) := by simp [sobWeight, hk]
  have e : (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) := by push_cast; ring
  rw [hw, e, Real.rpow_natCast, ← absk_sq, pow_mul]

/-- The vertical component is weighted-summable. -/
private lemma summable_cmp {z : Field} {j : ℕ} (hz : InH j z) (h0 : z 0 = 0) (a : Fin 3) :
    Summable fun k => absSq k ^ j * ‖GN.cmp z a k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg (absSq_nonneg k) _)
    (by positivity)) (fun k => ?_) hz
  by_cases hk : k = 0
  · subst hk
    simp [GN.cmp, h0, sobWeight]
  · rw [sobWeight_nat hk]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_cmp_le z a k) 2)
      (pow_nonneg (absSq_nonneg k) _)

private lemma norm_wC_sq_le (z : Field) (k : Mode) : ‖wC z k‖ ^ 2 ≤ 4 * (absSq k * ‖z k‖ ^ 2) := by
  have h : ‖wC z k‖ ≤ 2 * (absk k * ‖z k‖) := by
    rw [wC, curlL_apply, norm_mul, Complex.norm_I, one_mul]
    exact norm_cross_le _ _
  refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (le_of_eq ?_)
  rw [mul_pow, mul_pow, absk_sq]
  norm_num

/-- The vorticity is weighted-summable. -/
private lemma summable_wC {z : Field} {j : ℕ} (hz : InH ((j + 1 : ℕ) : ℝ) z) (h0 : z 0 = 0) :
    Summable fun k => absSq k ^ j * ‖wC z k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg (absSq_nonneg k) _)
    (by positivity)) (fun k => ?_) (hz.mul_left 4)
  by_cases hk : k = 0
  · subst hk
    simp [h0, wC_zero, sobWeight]
  · rw [sobWeight_nat hk, pow_succ]
    have h := mul_le_mul_of_nonneg_left (norm_wC_sq_le z k) (pow_nonneg (absSq_nonneg k) j)
    exact h.trans (le_of_eq (by ring))

private lemma cmp_two_neg {z : Field} (hz : IsReal z) (k : Mode) :
    GN.cmp z 2 (-k) = conj (GN.cmp z 2 k) := by
  simp [GN.cmp, hz k, conjV]

private lemma cmp_two_fast {z : Field} (hz' : PiS z = z) (k : Mode) (hk : k 2 ≠ 0) :
    GN.cmp z 2 k = 0 := by
  simp [GN.cmp, slow_zero' hz' hk]

private lemma wC_fast {z : Field} (hz' : PiS z = z) (k : Mode) (hk : k 2 ≠ 0) : wC z k = 0 := by
  simp [wC, curlL_apply, slow_zero' hz' hk]

/-! ### The commutators on fields -/

private lemma abs_pair_PiV_one {z : Field} (hz : Adm 2 z) (hz3 : InH 3 z) (hz' : PiS z = z)
    {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D) (hstr : StrainBd z q D)
    (hDΛ : D ^ q ≤ Λ ^ (q - 1)) :
    |pair 1 (PiV z) (Bsym z z)| ≤
      2 * Λ * hnorm 1 (PiV z) ^ 2 + 10 * hnorm 1 (PiV z) * hnorm 2 (PiV z) := by
  rw [pair_one_PiV hz hz']
  have h := abs_pairS_adv_le hz hz3 hz' (cmp_two_neg hz.real) (cmp_two_fast hz')
    (summable_cmp (hz3.mono (by norm_num)) hz.mean 2)
    (summable_cmp (hz3.mono (by norm_num)) hz.mean 2) hq hΛ hD hstr hDΛ
  have e1 := sn_cmp_two hz' hz.mean 1
  have e2 := sn_cmp_two hz' hz.mean 2
  rw [e1, e2, Nat.cast_one, Nat.cast_ofNat, Real.sqrt_sq (hnorm_nonneg _ _),
    Real.sqrt_sq (hnorm_nonneg _ _)] at h
  exact h

private lemma abs_pair_PiH_two {z : Field} (hz : Adm 2 z) (hz3 : InH 3 z) (hz' : PiS z = z)
    {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D) (hstr : StrainBd z q D)
    (hDΛ : D ^ q ≤ Λ ^ (q - 1)) :
    |pair 2 (PiH z) (Bsym z z)| ≤
      2 * Λ * hnorm 2 (PiH z) ^ 2 + 10 * hnorm 2 (PiH z) * hnorm 3 (PiH z) := by
  rw [pair_two_PiH hz hz']
  have h := abs_pairS_adv_le hz hz3 hz' (wC_neg hz.real) (wC_fast hz')
    (summable_wC (j := 1) (hz3.mono (by norm_num)) hz.mean)
    (summable_wC (j := 2) (hz3.mono (by norm_num)) hz.mean) hq hΛ hD hstr hDΛ
  have e1 := sn_wC hz hz' 1
  have e2 := sn_wC hz hz' 2
  have c1 : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
  have c2 : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
  rw [c1] at e1
  rw [c2] at e2
  rw [e1, e2, Real.sqrt_sq (hnorm_nonneg _ _), Real.sqrt_sq (hnorm_nonneg _ _)] at h
  exact h

private lemma abs_pair_PiV_two {z : Field} (hz : Adm 2 z) (hz3 : InH 3 z) (hz' : PiS z = z)
    {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D) (hstr : StrainBd z q D)
    (hstr2 : StrainBd z (2 * q) D) (hDΛ : D ^ q ≤ Λ ^ (q - 1)) :
    |pair 2 (PiV z) (Bsym z z)| ≤
      2 * Λ * hnorm 2 (PiV z) ^ 2 + 10 * hnorm 2 (PiV z) * hnorm 3 (PiV z) +
        3 * hnorm 3 (PiV z) * Real.sqrt (Λ ^ 2 * hnorm 1 (PiV z) ^ 2 +
          5 * hnorm 1 (PiV z) * hnorm 2 (PiV z)) := by
  rw [pair_two_PiV hz hz']
  have h := abs_pairS_two_adv_le hz hz3 hz' (cmp_two_neg hz.real) (cmp_two_fast hz')
    (by simp [GN.cmp, hz.mean])
    (summable_cmp (hz3.mono (by norm_num)) hz.mean 2)
    (summable_cmp (hz3.mono (by norm_num)) hz.mean 2)
    (summable_cmp (hz3.mono (by norm_num)) hz.mean 2) hq hΛ hD hstr hstr2 hDΛ
  have e1 := sn_cmp_two hz' hz.mean 1
  have e2 := sn_cmp_two hz' hz.mean 2
  have e3 := sn_cmp_two hz' hz.mean 3
  rw [e1, e2, e3, Nat.cast_one, Nat.cast_ofNat, Nat.cast_ofNat, Real.sqrt_sq (hnorm_nonneg _ _),
    Real.sqrt_sq (hnorm_nonneg _ _), Real.sqrt_sq (hnorm_nonneg _ _)] at h
  exact h

/-! ### The laws -/

/-- **F0 with an `L²_t` source**. -/
theorem corr_l2_law' (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    hnorm 0 (corrSlow r g y t) ^ 2 + ∫ u in s..t, hnorm 1 (corrSlow r g y u) ^ 2 ≤
      hnorm 0 (corrSlow r g y s) ^ 2 + ∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2 := by
  have hp : HeatPair 0 s t (corrSlow r g y) (corrForce r g y) :=
    (heatPair_corrSlow h hr (Or.inl rfl) (hs.trans hst) ht).mono hs le_rfl
  have key := hp.energy_le (τ := 1) (θ := 1) (R := fun u => hnorm 1 (corrRes r g y u) ^ 2)
    (by norm_num) hst (intervalIntegrable_corrRes_sq h hr hs hst ht) ?_
  · linarith
  filter_upwards [ae_inH1_corrRes h hr hs hst ht, ae_restrict_mem measurableSet_Icc]
    with u hres1 hu
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hz := corrSlow_adm h hr hu0 huT
  have hz1 : InH ((0 : ℝ) + 1) (corrSlow r g y u) := by
    rw [zero_add]; exact hz.inH.mono (by norm_num)
  rw [pair_corrForce h hr hu0 huT (by norm_num) hz1,
    pair_slow_cyc hz hz (fun _ _ => rfl), sub_zero]
  have hle := (pair_le hz1 ((corrRes_inH0 h hr hu0 huT).mono (by norm_num : (0 : ℝ) - 1 ≤ 0))).2
  rw [zero_add] at hle
  have h1 : hnorm ((0 : ℝ) - 1) (corrRes r g y u) ≤ hnorm 1 (corrRes r g y u) :=
    hnorm_mono (by norm_num) hres1
  have h2 := le_abs_self (pair 0 (corrSlow r g y u) (corrRes r g y u))
  have h3 := hnorm_nonneg 1 (corrSlow r g y u)
  nlinarith [sq_nonneg (hnorm 1 (corrSlow r g y u) - hnorm 1 (corrRes r g y u)),
    mul_le_mul_of_nonneg_left h1 h3]

/-- **F1 with an `L²_t` source**. -/
theorem corr_horiz_law' (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    hnorm 1 (PiH (corrSlow r g y t)) ^ 2 + ∫ u in s..t, hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤
      hnorm 1 (PiH (corrSlow r g y s)) ^ 2 + ∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2 := by
  have hp : HeatPair 1 s t (fun u => PiH (corrSlow r g y u)) (fun u => PiH (corrForce r g y u)) :=
    (heatPair_corrH h hr (Or.inr (Or.inl rfl)) (hs.trans hst) ht).mono hs le_rfl
  have key := hp.energy_le (τ := 2) (θ := 1) (R := fun u => hnorm 1 (corrRes r g y u) ^ 2)
    (by norm_num) hst (intervalIntegrable_corrRes_sq h hr hs hst ht) ?_
  · linarith
  filter_upwards [ae_inH1_corrRes h hr hs hst ht, ae_restrict_mem measurableSet_Icc]
    with u hres1 hu
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hz := corrSlow_adm h hr hu0 huT
  have hz' := PiS_corrSlow r g y u
  have hH : InH ((1 : ℝ) + 1) (PiH (corrSlow r g y u)) := by
    rw [one_add_one_eq_two]; exact hz.inH.PiH
  show 2 * pair 1 (PiH (corrSlow r g y u)) (PiH (corrForce r g y u)) ≤
    1 * hnorm 2 (PiH (corrSlow r g y u)) ^ 2 + hnorm 1 (corrRes r g y u) ^ 2
  have h0 : pair 1 (PiH (corrSlow r g y u)) (Bsym (corrSlow r g y u) (corrSlow r g y u)) = 0 := by
    rw [← pair_PiH]
    exact pair_slow_horizontal hz hz' (Or.inr rfl)
  rw [pair_PiH, pair_corrForce h hr hu0 huT le_rfl hH, h0, sub_zero]
  have hle := (pair_le hH ((corrRes_inH0 h hr hu0 huT).mono (by norm_num : (1 : ℝ) - 1 ≤ 0))).2
  rw [one_add_one_eq_two] at hle
  have h1 : hnorm ((1 : ℝ) - 1) (corrRes r g y u) ≤ hnorm 1 (corrRes r g y u) :=
    hnorm_mono (by norm_num) hres1
  have h2 := le_abs_self (pair 1 (PiH (corrSlow r g y u)) (corrRes r g y u))
  have h3 := hnorm_nonneg 2 (PiH (corrSlow r g y u))
  nlinarith [sq_nonneg (hnorm 2 (PiH (corrSlow r g y u)) - hnorm 1 (corrRes r g y u)),
    mul_le_mul_of_nonneg_left h1 h3]

/-- The strain of `y_S` on a time interval. -/
def StrainOn (r : ℝ) (g : Field) (y : ℝ → Field) (s t : ℝ) (q : ℕ) (D : ℝ) : Prop :=
  ∀ u ∈ Icc s t, StrainBd (corrSlow r g y u) q D

/-- **The passive `H¹` law for the vertical component.** -/
theorem vert_h1_law (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ)
    (hD : 0 ≤ D) (hS : StrainOn r g y s t q D) (hDΛ : D ^ q ≤ Λ ^ (q - 1)) :
    hnorm 1 (PiV (corrSlow r g y t)) ^ 2 + ∫ u in s..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤
      hnorm 1 (PiV (corrSlow r g y s)) ^ 2 + ∫ u in s..t,
        ((4 * Λ + 200) * hnorm 1 (PiV (corrSlow r g y u)) ^ 2 +
          2 * hnorm 1 (corrRes r g y u) ^ 2) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hp : HeatPair 1 s t (fun u => PiV (corrSlow r g y u)) (fun u => PiV (corrForce r g y u)) :=
    (heatPair_corrV h hr (Or.inr (Or.inl rfl)) ht0 ht).mono hs le_rfl
  have hc1 : ContinuousOn (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hR : IntervalIntegrable (fun u => (4 * Λ + 200) * hnorm 1 (PiV (corrSlow r g y u)) ^ 2 +
      2 * hnorm 1 (corrRes r g y u) ^ 2) volume s t :=
    ((continuousOn_const.mul hc1).intervalIntegrable_of_Icc hst).add
      ((intervalIntegrable_corrRes_sq h hr hs hst ht).const_mul 2)
  have key := hp.energy_le (τ := 2) (θ := 1) (by norm_num) hst hR ?_
  · linarith
  filter_upwards [ae_inH3_corr h hr hs hst ht, ae_inH1_corrRes h hr hs hst ht,
    ae_restrict_mem measurableSet_Icc] with u hz3 hres1 hu
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hz := corrSlow_adm h hr hu0 huT
  have hz' := PiS_corrSlow r g y u
  have hV : InH ((1 : ℝ) + 1) (PiV (corrSlow r g y u)) := by
    rw [one_add_one_eq_two]; exact hz.inH.PiV
  show 2 * pair 1 (PiV (corrSlow r g y u)) (PiV (corrForce r g y u)) ≤
    1 * hnorm 2 (PiV (corrSlow r g y u)) ^ 2 +
      ((4 * Λ + 200) * hnorm 1 (PiV (corrSlow r g y u)) ^ 2 + 2 * hnorm 1 (corrRes r g y u) ^ 2)
  rw [pair_PiV, pair_corrForce h hr hu0 huT le_rfl hV]
  have hle := (pair_le hV ((corrRes_inH0 h hr hu0 huT).mono (by norm_num : (1 : ℝ) - 1 ≤ 0))).2
  rw [one_add_one_eq_two] at hle
  have h1 : hnorm ((1 : ℝ) - 1) (corrRes r g y u) ≤ hnorm 1 (corrRes r g y u) :=
    hnorm_mono (by norm_num) hres1
  exact young_one (hle.trans (mul_le_mul_of_nonneg_left h1 (hnorm_nonneg _ _)))
    (abs_pair_PiV_one hz hz3 hz' hq hΛ hD (hS u hu) hDΛ)

/-- **The passive `H¹` law for the vorticity**, that is the `H²` law of `h`. -/
theorem horiz_h2_law (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ)
    (hD : 0 ≤ D) (hS : StrainOn r g y s t q D) (hDΛ : D ^ q ≤ Λ ^ (q - 1)) :
    hnorm 2 (PiH (corrSlow r g y t)) ^ 2 + ∫ u in s..t, hnorm 3 (PiH (corrSlow r g y u)) ^ 2 ≤
      hnorm 2 (PiH (corrSlow r g y s)) ^ 2 + ∫ u in s..t,
        ((4 * Λ + 200) * hnorm 2 (PiH (corrSlow r g y u)) ^ 2 +
          2 * hnorm 1 (corrRes r g y u) ^ 2) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hp : HeatPair 2 s t (fun u => PiH (corrSlow r g y u)) (fun u => PiH (corrForce r g y u)) :=
    (heatPair_corrH h hr (Or.inr (Or.inr rfl)) ht0 ht).mono hs le_rfl
  have hc2 : ContinuousOn (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrH_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hR : IntervalIntegrable (fun u => (4 * Λ + 200) * hnorm 2 (PiH (corrSlow r g y u)) ^ 2 +
      2 * hnorm 1 (corrRes r g y u) ^ 2) volume s t :=
    ((continuousOn_const.mul hc2).intervalIntegrable_of_Icc hst).add
      ((intervalIntegrable_corrRes_sq h hr hs hst ht).const_mul 2)
  have key := hp.energy_le (τ := 3) (θ := 1) (by norm_num) hst hR ?_
  · linarith
  filter_upwards [ae_inH3_corr h hr hs hst ht, ae_inH1_corrRes h hr hs hst ht,
    ae_restrict_mem measurableSet_Icc] with u hz3 hres1 hu
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hz := corrSlow_adm h hr hu0 huT
  have hz' := PiS_corrSlow r g y u
  have e3 : (2 : ℝ) + 1 = 3 := by norm_num
  have e1 : (2 : ℝ) - 1 = 1 := by norm_num
  have hH3 : InH ((2 : ℝ) + 1) (PiH (corrSlow r g y u)) := by
    rw [e3]; exact hz3.PiH
  have hres1' : InH ((2 : ℝ) - 1) (corrRes r g y u) := by
    rw [e1]; exact hres1
  have hB1 : InH ((2 : ℝ) - 1) (Bsym (corrSlow r g y u) (corrSlow r g y u)) := by
    rw [e1]; exact Bsym_corrSlow_inH1 h hr hu0 huT
  show 2 * pair 2 (PiH (corrSlow r g y u)) (PiH (corrForce r g y u)) ≤
    1 * hnorm 3 (PiH (corrSlow r g y u)) ^ 2 +
      ((4 * Λ + 200) * hnorm 2 (PiH (corrSlow r g y u)) ^ 2 + 2 * hnorm 1 (corrRes r g y u) ^ 2)
  rw [pair_PiH, corrForce, pair_sub hH3 hres1' hB1]
  have hle := (pair_le hH3 hres1').2
  rw [e3, e1] at hle
  exact young_one hle (abs_pair_PiH_two hz hz3 hz' hq hΛ hD (hS u hu) hDΛ)

/-- **The passive `H²` law for the vertical component.** -/
theorem vert_h2_law (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ)
    (hD : 0 ≤ D) (hS : StrainOn r g y s t q D) (hS2 : StrainOn r g y s t (2 * q) D)
    (hDΛ : D ^ q ≤ Λ ^ (q - 1)) :
    hnorm 2 (PiV (corrSlow r g y t)) ^ 2 +
        5 / 4 * ∫ u in s..t, hnorm 3 (PiV (corrSlow r g y u)) ^ 2 ≤
      hnorm 2 (PiV (corrSlow r g y s)) ^ 2 + ∫ u in s..t,
        ((4 * Λ + 490) * hnorm 2 (PiV (corrSlow r g y u)) ^ 2 +
          (36 * Λ ^ 2 + 90) * hnorm 1 (PiV (corrSlow r g y u)) ^ 2 +
          4 * hnorm 1 (corrRes r g y u) ^ 2) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hp : HeatPair 2 s t (fun u => PiV (corrSlow r g y u)) (fun u => PiV (corrForce r g y u)) :=
    (heatPair_corrV h hr (Or.inr (Or.inr rfl)) ht0 ht).mono hs le_rfl
  have hc1 : ContinuousOn (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hc2 : ContinuousOn (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hR : IntervalIntegrable (fun u => (4 * Λ + 490) * hnorm 2 (PiV (corrSlow r g y u)) ^ 2 +
      (36 * Λ ^ 2 + 90) * hnorm 1 (PiV (corrSlow r g y u)) ^ 2 +
      4 * hnorm 1 (corrRes r g y u) ^ 2) volume s t :=
    (((continuousOn_const.mul hc2).add (continuousOn_const.mul hc1)).intervalIntegrable_of_Icc
      hst).add ((intervalIntegrable_corrRes_sq h hr hs hst ht).const_mul 4)
  have key := hp.energy_le (τ := 3) (θ := 3 / 4) (by norm_num) hst hR ?_
  · have e : (2 : ℝ) - 3 / 4 = 5 / 4 := by norm_num
    rwa [e] at key
  filter_upwards [ae_inH3_corr h hr hs hst ht, ae_inH1_corrRes h hr hs hst ht,
    ae_restrict_mem measurableSet_Icc] with u hz3 hres1 hu
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hz := corrSlow_adm h hr hu0 huT
  have hz' := PiS_corrSlow r g y u
  have e3 : (2 : ℝ) + 1 = 3 := by norm_num
  have e1 : (2 : ℝ) - 1 = 1 := by norm_num
  have hV3 : InH ((2 : ℝ) + 1) (PiV (corrSlow r g y u)) := by
    rw [e3]; exact hz3.PiV
  have hres1' : InH ((2 : ℝ) - 1) (corrRes r g y u) := by
    rw [e1]; exact hres1
  have hB1 : InH ((2 : ℝ) - 1) (Bsym (corrSlow r g y u) (corrSlow r g y u)) := by
    rw [e1]; exact Bsym_corrSlow_inH1 h hr hu0 huT
  show 2 * pair 2 (PiV (corrSlow r g y u)) (PiV (corrForce r g y u)) ≤
    3 / 4 * hnorm 3 (PiV (corrSlow r g y u)) ^ 2 +
      ((4 * Λ + 490) * hnorm 2 (PiV (corrSlow r g y u)) ^ 2 +
        (36 * Λ ^ 2 + 90) * hnorm 1 (PiV (corrSlow r g y u)) ^ 2 +
        4 * hnorm 1 (corrRes r g y u) ^ 2)
  rw [pair_PiV, corrForce, pair_sub hV3 hres1' hB1]
  have hle := (pair_le hV3 hres1').2
  rw [e3, e1] at hle
  have ha := hnorm_nonneg 1 (PiV (corrSlow r g y u))
  have hb := hnorm_nonneg 2 (PiV (corrSlow r g y u))
  exact young_two (by positivity) rfl hle
    (abs_pair_PiV_two hz hz3 hz' hq hΛ hD (hS u hu) (hS2 u hu) hDΛ)

/-- The dissipation dominates the Riccati term: `Z²/A² ≤ d²` a.e. -/
private lemma integral_riccati_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t A : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) (hA : 0 < A)
    (ha : ∀ u ∈ Icc s t, hnorm 1 (PiV (corrSlow r g y u)) ≤ A) :
    ∫ u in s..t, (hnorm 2 (PiV (corrSlow r g y u)) ^ 2) ^ 2 / A ^ 2 ≤
      ∫ u in s..t, hnorm 3 (PiV (corrSlow r g y u)) ^ 2 := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hp : HeatPair 2 s t (fun u => PiV (corrSlow r g y u)) (fun u => PiV (corrForce r g y u)) :=
    (heatPair_corrV h hr (Or.inr (Or.inr rfl)) ht0 ht).mono hs le_rfl
  have hD3 : IntervalIntegrable (fun u => hnorm 3 (PiV (corrSlow r g y u)) ^ 2) volume s t := by
    have := hp.intervalIntegrable_dissipation hst
    have e : (2 : ℝ) + 1 = 3 := by norm_num
    rwa [e] at this
  have hZc : ContinuousOn (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  refine intervalIntegral.integral_mono_ae_restrict hst
    (((hZc.pow 2).div_const _).intervalIntegrable_of_Icc hst) hD3 ?_
  filter_upwards [ae_inH3_corr h hr hs hst ht, ae_restrict_mem measurableSet_Icc] with u hz3 hu
  have e3 : (2 : ℝ) + 1 = 3 := by norm_num
  have e1 : (2 : ℝ) - 1 = 1 := by norm_num
  have hV3 : InH ((2 : ℝ) + 1) (PiV (corrSlow r g y u)) := by
    rw [e3]; exact hz3.PiV
  have hint := hnorm_sq_le_mul hV3
  rw [e3, e1] at hint
  have h3 := hnorm_nonneg 3 (PiV (corrSlow r g y u))
  rw [div_le_iff₀ (by positivity)]
  have h4 : hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤ A * hnorm 3 (PiV (corrSlow r g y u)) :=
    hint.trans (mul_le_mul_of_nonneg_right (ha u hu) h3)
  calc (hnorm 2 (PiV (corrSlow r g y u)) ^ 2) ^ 2
      ≤ (A * hnorm 3 (PiV (corrSlow r g y u))) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
    _ = hnorm 3 (PiV (corrSlow r g y u)) ^ 2 * A ^ 2 := by ring

/-- The law `vert_h2_law` in the form of `barrier_sup`. -/
private lemma barrier_step (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {q : ℕ} (hq : 1 ≤ q) {Λ D A : ℝ} (hΛ : 0 < Λ)
    (hD : 0 ≤ D) (hS : StrainOn r g y s t q D) (hS2 : StrainOn r g y s t (2 * q) D)
    (hDΛ : D ^ q ≤ Λ ^ (q - 1)) (hA : 0 < A)
    (ha : ∀ u ∈ Icc s t, hnorm 1 (PiV (corrSlow r g y u)) ≤ A) :
    hnorm 2 (PiV (corrSlow r g y t)) ^ 2 ≤ hnorm 2 (PiV (corrSlow r g y s)) ^ 2 + ∫ u in s..t,
      (-((hnorm 2 (PiV (corrSlow r g y u)) ^ 2) ^ 2 / A ^ 2) +
        (4 * Λ + 490) * hnorm 2 (PiV (corrSlow r g y u)) ^ 2 + (36 * Λ ^ 2 + 90) * A ^ 2 +
        4 * hnorm 1 (corrRes r g y u) ^ 2) := by
  have ht0 : 0 ≤ t := hs.trans hst
  set Z : ℝ → ℝ := fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2 with hZ
  have hlaw := vert_h2_law h hr hs hst ht hq hΛ hD hS hS2 hDΛ
  have hdiss := integral_riccati_le h hr hs hst ht hA ha
  have hd0 : 0 ≤ ∫ u in s..t, hnorm 3 (PiV (corrSlow r g y u)) ^ 2 :=
    intervalIntegral.integral_nonneg hst fun _ _ => sq_nonneg _
  have hZc : ContinuousOn Z (Icc s t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hc1 : ContinuousOn (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hDi : IntervalIntegrable (fun u => Z u ^ 2 / A ^ 2) volume s t :=
    ((hZc.pow 2).div_const _).intervalIntegrable_of_Icc hst
  have hεi : IntervalIntegrable (fun u => 4 * hnorm 1 (corrRes r g y u) ^ 2) volume s t :=
    (intervalIntegrable_corrRes_sq h hr hs hst ht).const_mul 4
  have hZi : IntervalIntegrable (fun u => (4 * Λ + 490) * Z u + (36 * Λ ^ 2 + 90) * A ^ 2 +
      4 * hnorm 1 (corrRes r g y u) ^ 2) volume s t :=
    (((continuousOn_const.mul hZc).add continuousOn_const).intervalIntegrable_of_Icc hst).add hεi
  -- the low term is at most `(36Λ² + 90) A²`
  have hquad : ∫ u in s..t, ((4 * Λ + 490) * hnorm 2 (PiV (corrSlow r g y u)) ^ 2 +
      (36 * Λ ^ 2 + 90) * hnorm 1 (PiV (corrSlow r g y u)) ^ 2 +
      4 * hnorm 1 (corrRes r g y u) ^ 2) ≤
      ∫ u in s..t, ((4 * Λ + 490) * Z u + (36 * Λ ^ 2 + 90) * A ^ 2 +
        4 * hnorm 1 (corrRes r g y u) ^ 2) := by
    refine intervalIntegral.integral_mono_on hst
      ((((continuousOn_const.mul hZc).add (continuousOn_const.mul hc1)
        ).intervalIntegrable_of_Icc hst).add hεi) hZi fun u hu => ?_
    have hsq : hnorm 1 (PiV (corrSlow r g y u)) ^ 2 ≤ A ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg _ _) (ha u hu) 2
    have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 36 * Λ ^ 2 + 90)
    simp only [hZ]
    linarith
  have e : ∫ u in s..t, (-(Z u ^ 2 / A ^ 2) + (4 * Λ + 490) * Z u +
      (36 * Λ ^ 2 + 90) * A ^ 2 + 4 * hnorm 1 (corrRes r g y u) ^ 2) =
      -(∫ u in s..t, Z u ^ 2 / A ^ 2) + ∫ u in s..t,
        ((4 * Λ + 490) * Z u + (36 * Λ ^ 2 + 90) * A ^ 2 + 4 * hnorm 1 (corrRes r g y u) ^ 2) := by
    have h0 := intervalIntegral.integral_add hDi.neg hZi
    simp only [Pi.neg_apply] at h0
    rw [intervalIntegral.integral_neg] at h0
    rw [← h0]
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring
  rw [e]
  simp only [hZ] at hlaw hquad hdiss ⊢
  linarith

/-- **The `H²` barrier of the vertical component**: `b_v(u)² ≤ max(b_v(τ)², (10Λ + 500) A²) + 4E₂`
for `τ ≤ u` in the piece, if `a_v ≤ A`, `∫ ‖corrRes‖₁² ≤ E₂`. -/
theorem vert_h2_barrier (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {q : ℕ} (hq : 1 ≤ q) {Λ D A E₂ : ℝ} (hΛ : 0 < Λ)
    (hD : 0 ≤ D) (hS : StrainOn r g y s t q D) (hS2 : StrainOn r g y s t (2 * q) D)
    (hDΛ : D ^ q ≤ Λ ^ (q - 1)) (hA : 0 < A)
    (ha : ∀ u ∈ Icc s t, hnorm 1 (PiV (corrSlow r g y u)) ≤ A)
    (hE : (∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ E₂) :
    ∀ τ ∈ Icc s t, ∀ u ∈ Icc τ t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤
      max (hnorm 2 (PiV (corrSlow r g y τ)) ^ 2) ((10 * Λ + 500) * A ^ 2) + 4 * E₂ := by
  intro τ hτ
  have ht0 : 0 ≤ t := hs.trans hst
  have hτ0 : 0 ≤ τ := hs.trans hτ.1
  have hZc : ContinuousOn (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2) (Icc τ t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hτ0)
  have hεi : IntervalIntegrable (fun u => 4 * hnorm 1 (corrRes r g y u) ^ 2) volume τ t :=
    (intervalIntegrable_corrRes_sq h hr hτ0 hτ.2 (lt_lifespan le_rfl ht)).const_mul 4
  have hεE : (∫ u in τ..t, 4 * hnorm 1 (corrRes r g y u) ^ 2) ≤ 4 * E₂ := by
    rw [intervalIntegral.integral_const_mul]
    have : (∫ u in τ..t, hnorm 1 (corrRes r g y u) ^ 2) ≤
        ∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2 :=
      intervalIntegral.integral_mono_interval hτ.1 hτ.2 le_rfl
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (intervalIntegrable_corrRes_sq h hr hs hst ht)
    linarith
  refine barrier_sup (D := fun x => -(x ^ 2 / A ^ 2) + (4 * Λ + 490) * x +
    (36 * Λ ^ 2 + 90) * A ^ 2) hτ.2 hZc (by fun_prop) (fun x hx => drift_nonpos hA hΛ hx) hεi
    (fun _ _ => by positivity) hεE ?_
  intro s' t' hs' hst' ht'
  have hsub : Icc s' t' ⊆ Icc s t := Icc_subset_Icc (hτ.1.trans hs') ht'
  exact barrier_step h hr (hτ0.trans hs') hst' (lt_lifespan ht' ht) hq hΛ hD
    (fun u hu => hS u (hsub hu)) (fun u hu => hS2 u (hsub hu)) hDΛ hA fun u hu => ha u (hsub hu)

end OVNS.Quant.Slow
