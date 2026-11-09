import OddViscousNS.Quant.Joint.Slow.Smoothing

/-!
# E7-P: Sobolev on polynomials, and the passive scalar on Fourier coefficients

* `sobolev_poly`: `‖G‖²_{2·2ⁿ} ≲ ‖G‖₂² + ‖∇G‖₂²` on real slow polynomials, uniformly in the
  degree, by Moser itself on a fictitious past (step 4 of `Joint/Slow/Plan.lean`):
  `Ĝ_k(t) = e^{t|k|²} Ĝ_k` solves the heat equation on `[−1, 0]` with source `2|k|² Ĝ_k(t)`, of
  `L²_t L²_x` norm `≤ √2 ‖∇G‖₂`.  No Hausdorff–Young, no Young `ℓ^r`.
* `advC`, `Passive`: a scalar on Fourier coefficients solving `∂_t c = Δc − s·∇c + f`.
* `Passive.polyPath`: its box truncations are polynomial paths, with a commutator error
  `nn2_errP_le`, of size `‖s‖₂‖c‖₂/N`.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.Slow

open GN

/-! ### Sobolev on polynomials, by a fictitious past -/

/-- The fictitious past of `G`. -/
def pastC (G : Pol) (t : ℝ) (k : Mode) : ℂ := (Real.exp (t * absSq k) : ℂ) * G.coeff k

/-- Its time derivative. -/
def pastD (G : Pol) (t : ℝ) (k : Mode) : ℂ := (absSq k : ℂ) * pastC G t k

lemma absSq_neg' (k : Mode) : absSq (-k) = absSq k := by
  simp [absSq]

lemma coeff_past (G : Pol) (t : ℝ) (k : Mode) :
    (polyOf G.coeff.support (pastC G t)).coeff k = pastC G t k := by
  rw [coeff_polyOf]
  simp only [tr]
  split_ifs with hk
  · rfl
  · simp [pastC, Finsupp.notMem_support_iff.1 hk]

lemma coeff_pastD (G : Pol) (t : ℝ) (k : Mode) :
    (polyOf G.coeff.support (pastD G t)).coeff k = pastD G t k := by
  rw [coeff_polyOf]
  simp only [tr]
  split_ifs with hk
  · rfl
  · simp [pastD, pastC, Finsupp.notMem_support_iff.1 hk]

lemma polyOf_zero (A : Finset Mode) : polyOf A (fun _ => 0) = 0 := by
  ext k
  rw [coeff_polyOf]
  simp [tr]

theorem pastPath {G : Pol} (hR : RealC G) (hS : IsSlowP G) :
    PolyPath (-1) 0 G.coeff.support (pastC G) (pastD G) (fun _ _ _ => 0) where
  hab := by norm_num
  slow := fun k hk => hS k (Finsupp.mem_support_iff.1 hk)
  real := fun t _ k => by
    rw [coeff_past, coeff_past]
    simp only [pastC, absSq_neg', hR k, map_mul, Complex.conj_ofReal]
  deriv := fun k _ t _ => by
    have h1 : HasDerivAt (fun u : ℝ => u * absSq k) (absSq k) t := by
      simpa using (hasDerivAt_id t).mul_const (absSq k)
    have h2 := h1.exp.ofReal_comp.mul_const (G.coeff k)
    refine h2.hasDerivWithinAt.congr_deriv ?_
    simp only [pastD, pastC]
    push_cast
    ring
  cont' := fun k _ => by
    simp only [pastD, pastC]
    fun_prop
  contU := fun _ _ _ => continuousOn_const
  div := fun t _ => by
    simp only [DivFree, polyOf_zero]
    ext k
    simp [D]

lemma coeff_src_past (G : Pol) (t : ℝ) (k : Mode) :
    (srcP G.coeff.support (pastC G) (pastD G) (fun _ _ _ => 0) t).coeff k =
      2 * (absSq k : ℂ) * pastC G t k := by
  have e : trans (fun _ => polyOf G.coeff.support (fun _ => (0 : ℂ)))
      (polyOf G.coeff.support (pastC G t)) = 0 := by
    simp [trans, polyOf_zero]
  simp only [srcP, e, add_zero, sub_eq_add_neg, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, coeff_pastD, lap, coeff_mult, coeff_past]
  simp only [pastD]
  ring

lemma integral_past_le {l : ℝ} (hl : 0 ≤ l) :
    ∫ t in (-1 : ℝ)..0, (2 * l * Real.exp (t * l)) ^ 2 ≤ 2 * l := by
  have hd : ∀ t ∈ uIcc (-1 : ℝ) 0, HasDerivAt (fun t => 2 * l * Real.exp (2 * t * l))
      ((2 * l * Real.exp (t * l)) ^ 2) t := fun t _ => by
    have h1 : HasDerivAt (fun u : ℝ => 2 * u * l) (2 * l) t := by
      simpa using ((hasDerivAt_id t).const_mul 2).mul_const l
    have h2 := (h1.exp.const_mul (2 * l))
    refine h2.congr_deriv ?_
    have : Real.exp (2 * t * l) = Real.exp (t * l) ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [this]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have h3 : 0 ≤ 2 * l * Real.exp (2 * (-1) * l) := by positivity
  have h4 : Real.exp (2 * 0 * l) = 1 := by simp
  rw [h4]
  linarith

/-- **Sobolev on real slow polynomials**, uniformly in the degree. -/
theorem sobolev_poly {G : Pol} (hR : RealC G) (hS : IsSlowP G) {Y : ℝ} (hY : 0 < Y)
    (h1 : nn2 G ≤ Y) (h2 : 2 * grad2 G ≤ Y) (n : ℕ) :
    mP (2 ^ n) G ≤ (piM 1 n * Y) ^ (2 ^ n) := by
  have hp := pastPath hR hS
  have hG0 : polyOf G.coeff.support (pastC G 0) = G := by
    ext k
    rw [coeff_past]
    simp [pastC, absSq]
  set A := G.coeff.support with hA
  have hm : ∀ t ∈ Icc (-1 : ℝ) 0, mP 1 (polyOf A (pastC G t)) ≤ Y := fun t ht => by
    rw [mP_eq_nn2, pow_one]
    refine le_trans (hasSum_le (fun k => ?_) (hasSum_nn2 _) (hasSum_nn2 G)) h1
    rw [coeff_past]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simp only [pastC, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    have : Real.exp (t * absSq k) ≤ 1 := Real.exp_le_one_iff.2 (by
      nlinarith [ht.2, absSq_nonneg k])
    calc _ ≤ 1 * ‖G.coeff k‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := one_mul _
  have hnn : ∀ t, nn2 (srcP A (pastC G) (pastD G) (fun _ _ _ => 0) t) =
      ∑ k ∈ A, ‖G.coeff k‖ ^ 2 * (2 * absSq k * Real.exp (t * absSq k)) ^ 2 := fun t => by
    have hs := hasSum_nn2 (srcP A (pastC G) (pastD G) (fun _ _ _ => 0) t)
    have hf : ∀ k ∉ A, ‖(srcP A (pastC G) (pastD G) (fun _ _ _ => 0) t).coeff k‖ ^ 2 = 0 :=
      fun k hk => by
        rw [coeff_src_past]
        simp [pastC, Finsupp.notMem_support_iff.1 hk]
    rw [hs.unique (hasSum_sum_of_ne_finset_zero hf)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_src_past]
    simp only [pastC, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      Complex.norm_ofNat, abs_of_nonneg (absSq_nonneg k)]
    ring
  have hF : (∫ u in (-1 : ℝ)..0, nn2 (srcP A (pastC G) (pastD G) (fun _ _ _ => 0) u)) ≤ Y := by
    simp only [hnn]
    rw [intervalIntegral.integral_finsetSum fun k _ =>
      Continuous.intervalIntegrable (by fun_prop) _ _]
    simp only [intervalIntegral.integral_const_mul]
    refine le_trans ?_ h2
    have h3 : grad2 G = ∑ k ∈ A, absSq k * ‖G.coeff k‖ ^ 2 := by
      refine (hasSum_grad2 G).unique (hasSum_sum_of_ne_finset_zero fun k hk => ?_)
      simp [Finsupp.notMem_support_iff.1 hk]
    rw [h3, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h4 := integral_past_le (absSq_nonneg k)
    have h5 : 0 ≤ ‖G.coeff k‖ ^ 2 := by positivity
    calc _ ≤ ‖G.coeff k‖ ^ 2 * (2 * absSq k) := mul_le_mul_of_nonneg_left h4 h5
      _ = _ := by ring
  have hmain := hp.moser (T := 1) (by norm_num) (by norm_num) hY hm hF n
  have hmem : (0 : ℝ) ∈ Icc (-1 + 1 - 1 / 2 ^ n : ℝ) 0 := by
    constructor
    · have : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
      linarith
    · exact le_rfl
  have := hmain 0 hmem
  rwa [hG0] at this

/-! ### The passive scalar -/

/-- The transport `s·∇c` on coefficients: `∑_i (s_i ∗ ∂_i c)`. -/
def advC (s : Field) (c : Mode → ℂ) (m : Mode) : ℂ := ∑ i, cv (cmp s i) (dC i c) m

/-- The right side of the passive equation. -/
def rhsP (s : ℝ → Field) (c f : ℝ → Mode → ℂ) (t : ℝ) (k : Mode) : ℂ :=
  -(absSq k : ℂ) * c t k - advC (s t) (c t) k + f t k

/-- **A passive scalar on Fourier coefficients**: `∂_t c = Δc − s·∇c + f`, mode by mode. -/
structure Passive (a b : ℝ) (s : ℝ → Field) (c f : ℝ → Mode → ℂ) : Prop where
  hab : a ≤ b
  real : ∀ t ∈ Icc a b, ∀ k, c t (-k) = conj (c t k)
  sol : ∀ t ∈ Icc a b, IsSolenoidal (s t)
  contS : ∀ k i, ContinuousOn (fun t => cmp (s t) i k) (Icc a b)
  deriv : ∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => c u k) (rhsP s c f t k) (Icc a b) t
  contD : ∀ k, ContinuousOn (fun t => rhsP s c f t k) (Icc a b)

lemma neg_mem_slowBox {N : ℕ} {k : Mode} (hk : k ∈ slowBox N) : -k ∈ slowBox N := by
  rw [mem_slowBox] at hk ⊢
  simp [hk.1, abs_neg, hk.2]

lemma tr_neg_conj {A : Finset Mode} (hA : ∀ k, k ∈ A → -k ∈ A) {a : Mode → ℂ}
    (ha : ∀ k, a (-k) = conj (a k)) (k : Mode) : tr A a (-k) = conj (tr A a k) := by
  have hiff : -k ∈ A ↔ k ∈ A := ⟨fun h => by simpa using hA _ h, hA k⟩
  simp only [tr, hiff]
  split_ifs
  · exact ha k
  · simp

/-- The commutator of the truncation with the transport. -/
def errP (A : Finset Mode) (s : Field) (c : Mode → ℂ) : Pol :=
  trans (fun i => polyOf A (cmp s i)) (polyOf A c) - polyOf A (advC s c)

lemma polyOf_add (A : Finset Mode) (a b : Mode → ℂ) :
    polyOf A (fun k => a k + b k) = polyOf A a + polyOf A b := by
  simp [polyOf, Finset.sum_add_distrib, AddMonoidAlgebra.single_add]

lemma polyOf_neg (A : Finset Mode) (a : Mode → ℂ) :
    polyOf A (fun k => -a k) = -polyOf A a := by
  ext k
  simp only [coeff_polyOf, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, tr]
  split_ifs <;> simp

lemma lap_polyOf (A : Finset Mode) (a : Mode → ℂ) :
    lap (polyOf A a) = polyOf A fun k => -(absSq k : ℂ) * a k := mult_polyOf _ _ _

lemma srcP_passive (A : Finset Mode) (s : ℝ → Field) (c f : ℝ → Mode → ℂ) (t : ℝ) :
    srcP A c (rhsP s c f) (fun t i => cmp (s t) i) t = polyOf A (f t) + errP A (s t) (c t) := by
  have e : polyOf A (rhsP s c f t) = lap (polyOf A (c t)) - polyOf A (advC (s t) (c t)) +
      polyOf A (f t) := by
    rw [lap_polyOf, sub_eq_add_neg, ← polyOf_neg, ← polyOf_add, ← polyOf_add]
    rfl
  simp only [srcP, errP, e]
  ring

/-- The box truncations of a passive scalar are polynomial paths. -/
theorem Passive.polyPath {a b : ℝ} {s : ℝ → Field} {c f : ℝ → Mode → ℂ} (h : Passive a b s c f)
    (N : ℕ) : PolyPath a b (slowBox N) c (rhsP s c f) (fun t i => cmp (s t) i) where
  hab := h.hab
  slow := fun k hk => (mem_slowBox.1 hk).1
  real := fun t ht k => by
    rw [coeff_polyOf, coeff_polyOf]
    exact tr_neg_conj (fun _ => neg_mem_slowBox) (h.real t ht) k
  deriv := fun k _ t ht => h.deriv k t ht
  cont' := fun k _ => h.contD k
  contU := fun i k _ => h.contS k i
  div := fun t ht => by
    ext k
    simp only [D, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
      coeff_mult, coeff_polyOf, tr, dSym, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply]
    split_ifs with hk
    · have h1 := h.sol t ht k
      simp only [dotM] at h1
      have e : ∀ i, Complex.I * (k i : ℂ) * GN.cmp (s t) i k =
          Complex.I * ((s t k) i * (k i : ℂ)) := fun i => by
        change Complex.I * (k i : ℂ) * (s t k) i = _
        ring
      simp only [e, ← Finset.mul_sum, h1, mul_zero]
    · simp

/-! ### The commutator of the box truncation -/

/-- The indicator of the complement of a box. -/
def rhoN (N : ℕ) (k : Mode) : ℝ := if k ∈ slowBox N then 0 else 1

lemma rhoN_nonneg (N : ℕ) (k : Mode) : 0 ≤ rhoN N k := by
  unfold rhoN
  split_ifs <;> norm_num

lemma rhoN_le_one (N : ℕ) (k : Mode) : rhoN N k ≤ 1 := by
  unfold rhoN
  split_ifs <;> norm_num

lemma add_mem_box_two {N : ℕ} {p q : Mode} (hp : p ∈ slowBox N) (hq : q ∈ slowBox N) :
    p + q ∈ slowBox (2 * N) := by
  rw [mem_slowBox] at hp hq ⊢
  refine ⟨by simp [hp.1, hq.1], ?_, ?_⟩
  · have h := abs_add_le (p 0) (q 0)
    simp only [Pi.add_apply]
    push_cast
    linarith [hp.2.1, hq.2.1]
  · have h := abs_add_le (p 1) (q 1)
    simp only [Pi.add_apply]
    push_cast
    linarith [hp.2.2, hq.2.2]

lemma subset_box_two (N : ℕ) : slowBox N ⊆ slowBox (2 * N) := slowBox_mono (by omega)

lemma rhoN_mul_le {N : ℕ} {k : Mode} (hk : k 2 = 0) : rhoN N k * N ≤ absk k := by
  unfold rhoN
  split_ifs with h
  · simpa using absk_nonneg k
  · rw [mem_slowBox] at h
    push Not at h
    have h0 := absk_nonneg k
    rw [one_mul]
    by_cases h1 : |k 0| ≤ N
    · have h2 := h hk h1
      have h3 : ((k 1 : ℝ)) ^ 2 ≤ absSq k := sq_le_absSq 1 k
      have h4 : |((k 1 : ℤ) : ℝ)| ≤ absk k := Real.abs_le_sqrt h3
      have h5 : (N : ℝ) ≤ |((k 1 : ℤ) : ℝ)| := by exact_mod_cast h2.le
      linarith
    · push Not at h1
      have h3 : ((k 0 : ℝ)) ^ 2 ≤ absSq k := sq_le_absSq 0 k
      have h4 : |((k 0 : ℤ) : ℝ)| ≤ absk k := Real.abs_le_sqrt h3
      have h5 : (N : ℝ) ≤ |((k 0 : ℤ) : ℝ)| := by exact_mod_cast h1.le
      linarith

lemma tr_eq_mul (A : Finset Mode) (a : Mode → ℂ) (k : Mode) :
    tr A a k = (if k ∈ A then 1 else 0) * a k := by
  simp only [tr]
  split_ifs <;> simp

/-- The pointwise bound of the commutator of the truncation. -/
private lemma norm_ind_sub_le (N : ℕ) (u g : Mode → ℂ) (m p : Mode) :
    let ι : Mode → ℂ := fun k => if k ∈ slowBox (2 * N) then 1 else 0
    ‖ι p * u p * (ι (m - p) * g (m - p)) - ι m * (u p * g (m - p))‖ ≤
      rhoN N p * ‖u p‖ * ‖g (m - p)‖ + ‖u p‖ * (rhoN N (m - p) * ‖g (m - p)‖) := by
  intro ι
  set A := slowBox (2 * N) with hA
  have e : ι p * u p * (ι (m - p) * g (m - p)) - ι m * (u p * g (m - p)) =
      (ι p * ι (m - p) - ι m) * (u p * g (m - p)) := by ring
  have hup := norm_nonneg (u p)
  have hgq := norm_nonneg (g (m - p))
  have hP : 0 ≤ ‖u p‖ * ‖g (m - p)‖ := mul_nonneg hup hgq
  rw [e, norm_mul, norm_mul]
  have h3 : ‖ι p * ι (m - p) - ι m‖ ≤ 1 := by
    simp only [ι]
    split_ifs <;> simp
  by_cases hp : p ∈ slowBox N
  · by_cases hq : m - p ∈ slowBox N
    · have hpA : p ∈ A := subset_box_two N hp
      have hqA : m - p ∈ A := subset_box_two N hq
      have hmA : m ∈ A := by simpa using add_mem_box_two hp hq
      have h0 : ι p * ι (m - p) - ι m = 0 := by simp [ι, hpA, hqA, hmA, hA.symm]
      rw [h0, norm_zero, zero_mul]
      have h1 := rhoN_nonneg N p
      have h2 := rhoN_nonneg N (m - p)
      positivity
    · have h1 : rhoN N (m - p) = 1 := by simp [rhoN, hq]
      have h2 := rhoN_nonneg N p
      rw [h1]
      nlinarith [mul_nonneg h2 hP]
  · have h1 : rhoN N p = 1 := by simp [rhoN, hp]
    have h2 := rhoN_nonneg N (m - p)
    rw [h1]
    nlinarith [mul_nonneg h2 hP]

/-- **The commutator of the truncation, one bilinear term**, pointwise on coefficients. -/
lemma norm_cv_tr_sub_le {N : ℕ} {u g : Mode → ℂ}
    (hug : ∀ m, Summable fun p => ‖u p‖ * ‖g (m - p)‖) (m : Mode) :
    ‖cv (tr (slowBox (2 * N)) u) (tr (slowBox (2 * N)) g) m - tr (slowBox (2 * N)) (cv u g) m‖ ≤
      convR (fun k => rhoN N k * ‖u k‖) (fun k => ‖g k‖) m +
        convR (fun k => ‖u k‖) (fun k => rhoN N k * ‖g k‖) m := by
  set A := slowBox (2 * N) with hA
  set ι : Mode → ℂ := fun k => if k ∈ A then 1 else 0 with hι
  have hs1 : Summable fun p => rhoN N p * ‖u p‖ * ‖g (m - p)‖ :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (mul_nonneg (rhoN_nonneg _ _) (norm_nonneg _))
      (norm_nonneg _)) (fun p => by
        have := mul_le_mul_of_nonneg_right (rhoN_le_one N p)
          (mul_nonneg (norm_nonneg (u p)) (norm_nonneg (g (m - p))))
        nlinarith) (hug m)
  have hs2 : Summable fun p => ‖u p‖ * (rhoN N (m - p) * ‖g (m - p)‖) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (mul_nonneg (rhoN_nonneg _ _)
      (norm_nonneg _))) (fun p => by
        have := mul_le_mul_of_nonneg_right (rhoN_le_one N (m - p))
          (mul_nonneg (norm_nonneg (u p)) (norm_nonneg (g (m - p))))
        nlinarith) (hug m)
  have hbd : ∀ p, ‖ι p * u p * (ι (m - p) * g (m - p)) - ι m * (u p * g (m - p))‖ ≤
      rhoN N p * ‖u p‖ * ‖g (m - p)‖ + ‖u p‖ * (rhoN N (m - p) * ‖g (m - p)‖) :=
    fun p => norm_ind_sub_le N u g m p
  have hsum : Summable fun p => rhoN N p * ‖u p‖ * ‖g (m - p)‖ +
      ‖u p‖ * (rhoN N (m - p) * ‖g (m - p)‖) := hs1.add hs2
  have e1 : cv (tr A u) (tr A g) m = ∑' p, ι p * u p * (ι (m - p) * g (m - p)) := by
    refine tsum_congr fun p => ?_
    rw [tr_eq_mul, tr_eq_mul]
  have e2 : tr A (cv u g) m = ∑' p, ι m * (u p * g (m - p)) := by
    rw [tr_eq_mul, tsum_mul_left]
    rfl
  have hs3 : Summable fun p => ι p * u p * (ι (m - p) * g (m - p)) := by
    refine Summable.of_norm_bounded (hug m) fun p => ?_
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖ι p‖ ≤ 1 := by simp only [hι]; split_ifs <;> simp
    have h2 : ‖ι (m - p)‖ ≤ 1 := by simp only [hι]; split_ifs <;> simp
    exact mul_le_mul (mul_le_of_le_one_left (norm_nonneg _) h1)
      (mul_le_of_le_one_left (norm_nonneg _) h2) (by positivity) (norm_nonneg _)
  have hs4 : Summable fun p => ι m * (u p * g (m - p)) := by
    refine Summable.mul_left _ ?_
    exact Summable.of_norm (by simpa [norm_mul] using hug m)
  rw [e1, e2, ← hs3.tsum_sub hs4]
  refine (tsum_of_norm_bounded hsum.hasSum hbd).trans (le_of_eq ?_)
  rw [hs1.tsum_add hs2]
  rfl

lemma coeff_trans_polyOf (A : Finset Mode) (s : Field) (c : Mode → ℂ) (m : Mode) :
    (trans (fun i => polyOf A (GN.cmp s i)) (polyOf A c)).coeff m =
      ∑ i, cv (tr A (GN.cmp s i)) (tr A (dC i c)) m := by
  simp only [trans, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : D i (polyOf A c) = polyOf A (dC i c) := mult_polyOf _ _ _
  rw [e, ← coeff_ev, map_mul, ev_polyOf, ev_polyOf, coeff_tp_mul]

/-- The weighted scalar norms: `sn j c = ∑ |k|^{2j} |c_k|²`. -/
def sn (j : ℕ) (c : Mode → ℂ) : ℝ := ∑' k, absSq k ^ j * ‖c k‖ ^ 2

lemma sn_nonneg (j : ℕ) (c : Mode → ℂ) : 0 ≤ sn j c :=
  tsum_nonneg fun k => mul_nonneg (pow_nonneg (absSq_nonneg k) _) (by positivity)

lemma norm_dC_sq_le (i : Fin 3) (c : Mode → ℂ) (k : Mode) :
    ‖dC i c k‖ ^ 2 ≤ absSq k * ‖c k‖ ^ 2 := by
  rw [normSq_dC]
  exact mul_le_mul_of_nonneg_right (sq_le_absSq i k) (by positivity)

lemma rhoN_le_div {N : ℕ} (hN : 1 ≤ N) {k : Mode} (hk : k 2 = 0) :
    rhoN N k ≤ absk k / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hN0]
  exact rhoN_mul_le hk

/-- The `ℓ¹` tail of the coefficients of `s`, for `s ∈ H³`. -/
lemma tail_l1_le {N : ℕ} (hN : 1 ≤ N) {s : Field} (hs3 : MZ 3 s) (hsl : ∀ k, k 2 ≠ 0 → s k = 0)
    (i : Fin 3) :
    Summable (fun k => rhoN N k * ‖GN.cmp s i k‖) ∧
      ∑' k, rhoN N k * ‖GN.cmp s i k‖ ≤ c4 * hnorm 3 s / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨h1, h2⟩ := wiener_grad_le hs3
  have hle : ∀ k, rhoN N k * ‖GN.cmp s i k‖ ≤ absk k * ‖s k‖ / N := fun k => by
    by_cases hk : k 2 = 0
    · have h3 := rhoN_le_div hN hk
      have h4 := norm_cmp_le s i k
      calc rhoN N k * ‖GN.cmp s i k‖ ≤ absk k / N * ‖s k‖ :=
            mul_le_mul h3 h4 (norm_nonneg _) (div_nonneg (absk_nonneg k) hN0.le)
        _ = _ := by ring
    · have h3 : s k = 0 := hsl k hk
      have h4 : GN.cmp s i k = 0 := by
        change (s k) i = 0
        rw [h3]
        rfl
      rw [h4, h3]
      simp
  have hs : Summable fun k => absk k * ‖s k‖ / N := h1.div_const _
  refine ⟨Summable.of_nonneg_of_le (fun k => mul_nonneg (rhoN_nonneg _ _) (norm_nonneg _)) hle hs,
    ?_⟩
  calc _ ≤ ∑' k, absk k * ‖s k‖ / N := Summable.tsum_le_tsum hle
        (Summable.of_nonneg_of_le (fun k => mul_nonneg (rhoN_nonneg _ _) (norm_nonneg _)) hle hs) hs
    _ = (∑' k, absk k * ‖s k‖) / N := tsum_div_const
    _ ≤ _ := div_le_div_of_nonneg_right h2 hN0.le

/-- The `ℓ²` tail of the derivatives of `c`. -/
lemma tail_l2_le {N : ℕ} (hN : 1 ≤ N) {c : Mode → ℂ} (hcs : ∀ k, k 2 ≠ 0 → c k = 0)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2) (i : Fin 3) :
    Summable (fun k => (rhoN N k * ‖dC i c k‖) ^ 2) ∧
      ∑' k, (rhoN N k * ‖dC i c k‖) ^ 2 ≤ sn 2 c / N ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : ∀ k, (rhoN N k * ‖dC i c k‖) ^ 2 ≤ absSq k ^ 2 * ‖c k‖ ^ 2 / N ^ 2 := fun k => by
    by_cases hk : k 2 = 0
    · have h3 := rhoN_le_div hN hk
      have h4 := norm_dC_sq_le i c k
      have h5 : rhoN N k ^ 2 ≤ absSq k / N ^ 2 := by
        calc rhoN N k ^ 2 ≤ (absk k / N) ^ 2 := pow_le_pow_left₀ (rhoN_nonneg _ _) h3 2
          _ = absSq k / N ^ 2 := by rw [div_pow, absk_sq]
      calc (rhoN N k * ‖dC i c k‖) ^ 2 = rhoN N k ^ 2 * ‖dC i c k‖ ^ 2 := by ring
        _ ≤ absSq k / N ^ 2 * (absSq k * ‖c k‖ ^ 2) :=
            mul_le_mul h5 h4 (by positivity) (div_nonneg (absSq_nonneg k) (by positivity))
        _ = _ := by ring
    · have h3 : c k = 0 := hcs k hk
      simp [dC, h3]
  have hs : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2 / N ^ 2 := hc2.div_const _
  have hS := Summable.of_nonneg_of_le (fun _ => by positivity) hle hs
  refine ⟨hS, ?_⟩
  calc _ ≤ ∑' k, absSq k ^ 2 * ‖c k‖ ^ 2 / N ^ 2 := Summable.tsum_le_tsum hle hS hs
    _ = sn 2 c / N ^ 2 := tsum_div_const

/-- The coefficients of the commutator of the truncation. -/
private lemma coeff_errP (A : Finset Mode) (s : Field) (c : Mode → ℂ) (m : Mode) :
    (errP A s c).coeff m = ∑ i, (cv (tr A (GN.cmp s i)) (tr A (dC i c)) m -
      tr A (cv (GN.cmp s i) (dC i c)) m) := by
  have e1 : (errP A s c).coeff m = (trans (fun i => polyOf A (GN.cmp s i)) (polyOf A c)).coeff m -
      (polyOf A (advC s c)).coeff m := by
    simp only [errP, sub_eq_add_neg, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]
  rw [e1, coeff_trans_polyOf, coeff_polyOf, tr_eq_mul, advC, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tr_eq_mul]

/-- The elementary step of the commutator: `(∑ᵢ (xᵢ + yᵢ))² ≤ 6 ∑ᵢ (xᵢ² + yᵢ²)`. -/
private lemma sq_sum_three_le {r : ℝ} {x y : Fin 3 → ℝ} (h1 : r ≤ ∑ i, (x i + y i)) (h0 : 0 ≤ r) :
    r ^ 2 ≤ 6 * ∑ i, (x i ^ 2 + y i ^ 2) := by
  have h4 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
    (f := fun i => x i + y i)
  have h5 : ∑ i, (x i + y i) ^ 2 ≤ 2 * ∑ i, (x i ^ 2 + y i ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [sq_nonneg (x i - y i)]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at h4
  calc _ ≤ (∑ i, (x i + y i)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := by linarith

/-- The commutator of the truncation, from a bound `T` for the `ℓ¹` tail of `s`: the common part
of `nn2_errP_le` and `nn2_errP_le'`. -/
theorem nn2_errP_le_of_tail {N : ℕ} (hN : 1 ≤ N) {s : Field} {c : Mode → ℂ} (hs2 : MZ 2 s)
    (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2) (hcs : ∀ k, k 2 ≠ 0 → c k = 0) {T : ℝ}
    (hA1 : ∀ i, Summable (fun k => rhoN N k * ‖GN.cmp s i k‖) ∧
      ∑' k, rhoN N k * ‖GN.cmp s i k‖ ≤ T) :
    nn2 (errP (slowBox (2 * N)) s c) ≤
      18 * (T ^ 2 * sn 1 c + (c4 * hnorm 2 s) ^ 2 * (sn 2 c / N ^ 2)) := by
  set A := slowBox (2 * N) with hA
  set u : Fin 3 → Mode → ℂ := fun i => GN.cmp s i with hu
  set g : Fin 3 → Mode → ℂ := fun i => dC i c with hg
  have hu1 : ∀ i, Summable fun k => ‖u i k‖ := fun i =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_cmp_le s i k)
      (summable_wiener hs2.inH)
  have hb0 : ∀ i, Summable fun k => ‖g i k‖ ^ 2 := fun i =>
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun k => (norm_dC_sq_le i c k).trans (le_of_eq (by simp))) hc1
  have hY1 := fun i => young_l1_l2 (a := fun k => ‖u i k‖) (b := fun k => ‖g i k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (hu1 i) (hb0 i)
  have hB2 := fun i => tail_l2_le hN hcs hc2 i
  have hYX := fun i => young_l1_l2 (a := fun k => rhoN N k * ‖u i k‖) (b := fun k => ‖g i k‖)
    (fun _ => mul_nonneg (rhoN_nonneg _ _) (norm_nonneg _)) (fun _ => norm_nonneg _) (hA1 i).1
    (hb0 i)
  have hYY := fun i => young_l1_l2 (a := fun k => ‖u i k‖) (b := fun k => rhoN N k * ‖g i k‖)
    (fun _ => norm_nonneg _) (fun _ => mul_nonneg (rhoN_nonneg _ _) (norm_nonneg _)) (hu1 i)
    (hB2 i).1
  set X : Fin 3 → Mode → ℝ := fun i m => convR (fun k => rhoN N k * ‖u i k‖) (fun k => ‖g i k‖) m
    with hX
  set Y : Fin 3 → Mode → ℝ := fun i m => convR (fun k => ‖u i k‖) (fun k => rhoN N k * ‖g i k‖) m
    with hY
  have hpt : ∀ m, ‖(errP A s c).coeff m‖ ^ 2 ≤ 6 * ∑ i, (X i m ^ 2 + Y i m ^ 2) := fun m => by
    refine sq_sum_three_le ?_ (norm_nonneg _)
    rw [coeff_errP]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact norm_cv_tr_sub_le (N := N) (hY1 i).1 m
  have hsum : HasSum (fun m => 6 * ∑ i, (X i m ^ 2 + Y i m ^ 2))
      (6 * ∑ i, (∑' m, X i m ^ 2 + ∑' m, Y i m ^ 2)) :=
    (hasSum_sum fun i _ => (hYX i).2.1.hasSum.add (hYY i).2.1.hasSum).mul_left 6
  refine (hasSum_le hpt (hasSum_nn2 _) hsum).trans ?_
  have hS1 : ∀ i, ∑' k, ‖g i k‖ ^ 2 ≤ sn 1 c := fun i =>
    Summable.tsum_le_tsum (fun k => (norm_dC_sq_le i c k).trans (le_of_eq (by simp))) (hb0 i) hc1
  have hS2 : ∀ i, ∑' k, ‖u i k‖ ≤ c4 * hnorm 2 s := fun i =>
    (Summable.tsum_le_tsum (fun k => norm_cmp_le s i k) (hu1 i) (summable_wiener hs2.inH)).trans
      (wiener_le hs2)
  have hbdX : ∀ i, ∑' m, X i m ^ 2 ≤ T ^ 2 * sn 1 c := fun i => by
    refine (hYX i).2.2.trans (mul_le_mul (pow_le_pow_left₀ (tsum_nonneg fun k =>
      mul_nonneg (rhoN_nonneg _ _) (norm_nonneg _)) (hA1 i).2 2) (hS1 i)
      (tsum_nonneg fun _ => by positivity) (by positivity))
  have hbdY : ∀ i, ∑' m, Y i m ^ 2 ≤ (c4 * hnorm 2 s) ^ 2 * (sn 2 c / N ^ 2) := fun i => by
    refine (hYY i).2.2.trans (mul_le_mul (pow_le_pow_left₀ (tsum_nonneg fun k => norm_nonneg _)
      (hS2 i) 2) (hB2 i).2 (tsum_nonneg fun _ => by positivity) (by positivity))
  have hfin : 6 * ∑ i, (∑' m, X i m ^ 2 + ∑' m, Y i m ^ 2) ≤
      6 * ∑ _i : Fin 3, (T ^ 2 * sn 1 c + (c4 * hnorm 2 s) ^ 2 * (sn 2 c / N ^ 2)) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => add_le_add (hbdX i) (hbdY i))
      (by norm_num)
  refine hfin.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The size of the commutator of the truncation**: `‖Z_N‖₂ ≲ (‖s‖₃‖c‖₁ + ‖s‖₂‖c‖₂)/N`. -/
theorem nn2_errP_le {N : ℕ} (hN : 1 ≤ N) {s : Field} {c : Mode → ℂ} (hs3 : MZ 3 s)
    (hs2 : MZ 2 s) (hsl : ∀ k, k 2 ≠ 0 → s k = 0)
    (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2) (hcs : ∀ k, k 2 ≠ 0 → c k = 0) :
    nn2 (errP (slowBox (2 * N)) s c) ≤
      18 * c4 ^ 2 / N ^ 2 * (hnorm 3 s ^ 2 * sn 1 c + hnorm 2 s ^ 2 * sn 2 c) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine (nn2_errP_le_of_tail hN hs2 hc1 hc2 hcs fun i => tail_l1_le hN hs3 hsl i).trans_eq ?_
  field_simp

lemma nn2_add_le (P Q : Pol) : nn2 (P + Q) ≤ 2 * nn2 P + 2 * nn2 Q := by
  have hi : ∀ R : Pol, Integrable (fun x => ‖ev R x‖ ^ 2) μT := fun R => integrable_norm_pow R 2
  have h := integral_mono (hi (P + Q)) (((hi P).const_mul 2).add ((hi Q).const_mul 2)) fun x => by
    have h1 : ‖ev (P + Q) x‖ ≤ ‖ev P x‖ + ‖ev Q x‖ := by
      rw [map_add, ContinuousMap.add_apply]
      exact norm_add_le _ _
    have h2 : ‖ev (P + Q) x‖ ^ 2 ≤ (‖ev P x‖ + ‖ev Q x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖ev P x‖ - ‖ev Q x‖)]
  simpa [integral_add ((hi P).const_mul 2) ((hi Q).const_mul 2), integral_const_mul, nn2] using h

/-- The `L²` norm of a truncation. -/
lemma nn2_polyOf_le {A : Finset Mode} {a : Mode → ℂ} (ha : Summable fun k => ‖a k‖ ^ 2) :
    nn2 (polyOf A a) ≤ ∑' k, ‖a k‖ ^ 2 := by
  refine hasSum_le (fun k => ?_) (hasSum_nn2 _) ha.hasSum
  rw [coeff_polyOf]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  simp only [tr]
  split_ifs <;> simp

lemma sn_zero (c : Mode → ℂ) : sn 0 c = ∑' k, ‖c k‖ ^ 2 := by
  simp [sn]

variable {a b : ℝ} {s : ℝ → Field} {c f : ℝ → Mode → ℂ}

/-- The source of a truncation, integrated: the commutator is `O(1/N²)`. -/
theorem Passive.integral_src_le (h : Passive a b s c f) {N : ℕ} (hN : 1 ≤ N) {G E : ℝ → ℝ}
    (hG : IntervalIntegrable G volume a b) (hE : IntervalIntegrable E volume a b)
    (hae : ∀ᵐ t ∂(volume.restrict (Icc a b)), MZ 3 (s t) ∧ MZ 2 (s t) ∧
      (∀ k, k 2 ≠ 0 → s t k = 0) ∧ (∀ k, k 2 ≠ 0 → c t k = 0) ∧
      (Summable fun k => absSq k ^ 1 * ‖c t k‖ ^ 2) ∧
      (Summable fun k => absSq k ^ 2 * ‖c t k‖ ^ 2) ∧ (Summable fun k => ‖f t k‖ ^ 2) ∧
      sn 0 (f t) ≤ G t ∧ hnorm 3 (s t) ^ 2 * sn 1 (c t) + hnorm 2 (s t) ^ 2 * sn 2 (c t) ≤ E t) :
    ∫ t in a..b, nn2 (srcP (slowBox (2 * N)) c (rhsP s c f) (fun t i => cmp (s t) i) t) ≤
      2 * (∫ t in a..b, G t) + 36 * c4 ^ 2 / N ^ 2 * ∫ t in a..b, E t := by
  have hp := h.polyPath (2 * N)
  have hc : IntervalIntegrable
      (fun t => nn2 (srcP (slowBox (2 * N)) c (rhsP s c f) (fun t i => cmp (s t) i) t))
      volume a b := hp.continuousOn_srcNorm.intervalIntegrable_of_Icc h.hab
  have hR : IntervalIntegrable (fun t => 2 * G t + 36 * c4 ^ 2 / N ^ 2 * E t) volume a b :=
    (hG.const_mul 2).add (hE.const_mul _)
  have hmono := intervalIntegral.integral_mono_ae_restrict h.hab hc hR (by
    filter_upwards [hae] with t ⟨hs3, hs2, hsl, hcs, hc1, hc2, hfs, hG', hE'⟩
    rw [srcP_passive]
    have h1 := nn2_add_le (polyOf (slowBox (2 * N)) (f t)) (errP (slowBox (2 * N)) (s t) (c t))
    have h2 : nn2 (polyOf (slowBox (2 * N)) (f t)) ≤ G t :=
      (nn2_polyOf_le hfs).trans (by rw [← sn_zero]; exact hG')
    have h3 := nn2_errP_le hN hs3 hs2 hsl hc1 hc2 hcs
    have h4 : 18 * c4 ^ 2 / N ^ 2 *
        (hnorm 3 (s t) ^ 2 * sn 1 (c t) + hnorm 2 (s t) ^ 2 * sn 2 (c t)) ≤
        18 * c4 ^ 2 / N ^ 2 * E t := mul_le_mul_of_nonneg_left hE' (by positivity)
    have e : 2 * (18 * c4 ^ 2 / (N : ℝ) ^ 2 * E t) = 36 * c4 ^ 2 / N ^ 2 * E t := by ring
    linarith)
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add (hG.const_mul 2) (hE.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- The truncated `L²` norm is below `sn 0`. -/
lemma mP_one_polyOf_le {A : Finset Mode} {a : Mode → ℂ} (ha : Summable fun k => ‖a k‖ ^ 2) :
    mP 1 (polyOf A a) ≤ sn 0 a := by
  rw [mP_eq_nn2, pow_one, sn_zero]
  exact nn2_polyOf_le ha

end OVNS.Quant.Slow
