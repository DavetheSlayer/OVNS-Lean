import OddViscousNS.Quant.Joint.Kinetic.GN

/-!
# E7-P: trigonometric polynomials as a differential algebra

The group algebra `Pol = ℂ[ℤ³]` with its evaluation `ev : Pol →ₐ C(T3, ℂ)`, Fourier multipliers
`mult`, and the derivations `D i = mult (I k_i)`.  All the calculus of the even-power laws is
algebra here: `mean (D i P) = 0`, Leibniz, and the identities `mean_pow_lap`, `mean_pow_trans`,
`mean_trans_lap`.  See `Joint/Slow/Plan.lean`, steps 2, 7.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.Slow

open GN

/-- Trigonometric polynomials: the group algebra of the lattice. -/
abbrev Pol : Type := AddMonoidAlgebra ℂ Mode

open AddMonoidAlgebra (single)

/-- The characters, as a monoid homomorphism. -/
def chi : Multiplicative Mode →* C(T3, ℂ) where
  toFun k := mFourier k.toAdd
  map_one' := by
    ext x
    simp [mFourier_zero]
  map_mul' a b := by
    simpa using (mFourier_mul' a.toAdd b.toAdd).symm

/-- Evaluation of a polynomial on the torus. -/
def ev : Pol →ₐ[ℂ] C(T3, ℂ) := AddMonoidAlgebra.lift ℂ C(T3, ℂ) Mode chi

@[simp] lemma ev_single (k : Mode) (c : ℂ) : ev (single k c) = c • mFourier k := by
  simp [ev, chi]

/-- The polynomial with coefficients `a` on `A`. -/
def polyOf (A : Finset Mode) (a : Mode → ℂ) : Pol := ∑ k ∈ A, single k (a k)

lemma coeff_polyOf (A : Finset Mode) (a : Mode → ℂ) (k : Mode) :
    (polyOf A a).coeff k = tr A a k := by
  classical
  simp only [polyOf, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, tr]
  exact Finset.sum_ite_eq' A k _

lemma ev_polyOf (A : Finset Mode) (a : Mode → ℂ) : ev (polyOf A a) = tp A a := by
  simp [polyOf, tp, map_sum]

/-- Every polynomial is a `tp` on its support. -/
lemma ev_eq_tp (P : Pol) : ev P = tp P.coeff.support P.coeff := by
  have h : P = polyOf P.coeff.support P.coeff := by
    ext k
    rw [coeff_polyOf]
    simp only [tr]
    split_ifs with hk
    · rfl
    · simpa using hk
  conv_lhs => rw [h]
  exact ev_polyOf _ _

/-- The mean of a polynomial is its coefficient at the origin. -/
def mean (P : Pol) : ℂ := P.coeff 0

lemma mean_add (P Q : Pol) : mean (P + Q) = mean P + mean Q := rfl

lemma mean_sum {ι : Type*} (s : Finset ι) (f : ι → Pol) :
    mean (∑ i ∈ s, f i) = ∑ i ∈ s, mean (f i) := by
  simp [mean, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum]

lemma J_ev (P : Pol) : J (ev P) = mean P := by
  rw [ev_eq_tp]
  have h := coeff_tp P.coeff.support P.coeff 0
  rw [mFourierCoeff_eq] at h
  have e : ∫ x, mFourier (-0 : Mode) x * tp P.coeff.support P.coeff x ∂μT =
      J (tp P.coeff.support P.coeff) := by
    rw [J_apply]
    simp [mFourier_zero]
  rw [← e, h]
  simp only [tr, mean]
  split_ifs with hk
  · rfl
  · simpa using (Finsupp.notMem_support_iff.1 hk).symm

/-- The Fourier coefficients of `ev P`. -/
lemma coeff_ev (P : Pol) (m : Mode) : mFourierCoeff (ev P : C(T3, ℂ)) m = P.coeff m := by
  rw [ev_eq_tp, coeff_tp]
  simp only [tr]
  split_ifs with hk
  · rfl
  · simpa using (Finsupp.notMem_support_iff.1 hk).symm

/-- Parseval for polynomials. -/
theorem integral_norm_sq_ev (P : Pol) :
    ∫ x, ‖ev P x‖ ^ 2 ∂μT = ∑ k ∈ P.coeff.support, ‖P.coeff k‖ ^ 2 := by
  rw [ev_eq_tp, integral_norm_sq_tp]

/-! ### Fourier multipliers -/

/-- The Fourier multiplier with symbol `m`. -/
def mult (m : Mode → ℂ) (P : Pol) : Pol :=
  .ofCoeff (Finsupp.onFinset P.coeff.support (fun k => m k * P.coeff k) (fun k hk => by
    simp only [Finsupp.mem_support_iff]
    exact right_ne_zero_of_mul hk))

@[simp] lemma coeff_mult (m : Mode → ℂ) (P : Pol) (k : Mode) :
    (mult m P).coeff k = m k * P.coeff k := rfl

lemma mult_add (m : Mode → ℂ) (P Q : Pol) : mult m (P + Q) = mult m P + mult m Q := by
  ext k
  simp [mul_add]

lemma mult_smul (m : Mode → ℂ) (c : ℂ) (P : Pol) : mult m (c • P) = c • mult m P := by
  ext k
  simp only [coeff_mult, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  ring

lemma mult_single (m : Mode → ℂ) (k : Mode) (c : ℂ) :
    mult m (single k c) = single k (m k * c) := by
  classical
  ext l
  simp only [coeff_mult, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · rw [h]
  · simp

lemma mult_mult (m m' : Mode → ℂ) (P : Pol) :
    mult m (mult m' P) = mult (fun k => m k * m' k) P := by
  ext k
  simp [mul_assoc]

@[simp] lemma mult_zero (m : Mode → ℂ) : mult m 0 = 0 := by
  ext k
  simp

/-- A multiplier with additive symbol is a derivation. -/
theorem mult_mul_of_add {m : Mode → ℂ} (hm : ∀ a b, m (a + b) = m a + m b) (P Q : Pol) :
    mult m (P * Q) = mult m P * Q + P * mult m Q := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [add_mul, mult_add, hx, hy]; ring
  | single a c =>
    induction Q using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [mul_add, mult_add, hx, hy]; ring
    | single b d =>
      simp only [AddMonoidAlgebra.single_mul_single, mult_single, hm]
      rw [← AddMonoidAlgebra.single_add]
      congr 1
      ring

/-! ### The derivations -/

/-- The symbol `I k_i` of `∂_i`. -/
def dSym (i : Fin 3) (k : Mode) : ℂ := Complex.I * (k i : ℂ)

lemma dSym_add (i : Fin 3) (a b : Mode) : dSym i (a + b) = dSym i a + dSym i b := by
  simp only [dSym, Pi.add_apply, Int.cast_add]
  ring

/-- The derivation `∂_i`. -/
def D (i : Fin 3) : Pol → Pol := mult (dSym i)

lemma D_add (i : Fin 3) (P Q : Pol) : D i (P + Q) = D i P + D i Q := mult_add _ _ _

lemma D_smul (i : Fin 3) (c : ℂ) (P : Pol) : D i (c • P) = c • D i P := mult_smul _ _ _

lemma D_mul (i : Fin 3) (P Q : Pol) : D i (P * Q) = D i P * Q + P * D i Q :=
  mult_mul_of_add (dSym_add i) P Q

lemma D_comm (i j : Fin 3) (P : Pol) : D i (D j P) = D j (D i P) := by
  simp only [D, mult_mult]
  congr 1
  funext k
  exact mul_comm _ _

lemma D_sum {ι : Type*} (i : Fin 3) (s : Finset ι) (f : ι → Pol) :
    D i (∑ a ∈ s, f a) = ∑ a ∈ s, D i (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [D]
  | insert a s ha ih => simp only [Finset.sum_insert ha, D_add, ih]

lemma D_pow (i : Fin 3) (P : Pol) (n : ℕ) :
    D i (P ^ (n + 1)) = ((n + 1 : ℕ) : ℂ) • (P ^ n * D i P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, D_mul, ih, Nat.cast_succ, add_smul, one_smul]
    simp only [Nat.cast_succ, add_smul, one_smul, smul_mul_assoc, add_mul]
    ring_nf

lemma mean_D (i : Fin 3) (P : Pol) : mean (D i P) = 0 := by
  simp [mean, D, dSym]

/-- Integration by parts. -/
lemma mean_D_mul (i : Fin 3) (P Q : Pol) : mean (D i P * Q) = -mean (P * D i Q) := by
  have h := mean_D i (P * Q)
  rw [D_mul, mean_add] at h
  linear_combination h

lemma mean_smul (c : ℂ) (P : Pol) : mean (c • P) = c * mean P := by
  simp [mean]

/-! ### The Laplacian and the transport -/

/-- The Laplacian, as a multiplier. -/
def lap : Pol → Pol := mult fun k => -(absSq k : ℂ)

lemma lap_eq (P : Pol) : lap P = ∑ i, D i (D i P) := by
  ext k
  simp only [lap, coeff_mult, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    D, dSym, ← mul_assoc, ← Finset.sum_mul, absSq]
  congr 1
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (-(k i : ℂ) ^ 2) * Complex.I_sq

/-- The transport `U · ∇ g`. -/
def trans (U : Fin 3 → Pol) (g : Pol) : Pol := ∑ i, U i * D i g

/-- `U` is divergence free. -/
def DivFree (U : Fin 3 → Pol) : Prop := ∑ i, D i (U i) = 0

/-- **The even-power dissipation**: `∫ P^{n+1} ΔP = −(n+1) ∑_i ∫ P^n (∂_i P)²`. -/
theorem mean_pow_lap (P : Pol) (n : ℕ) :
    mean (P ^ (n + 1) * lap P) = -((n + 1 : ℕ) : ℂ) * ∑ i, mean (P ^ n * D i P ^ 2) := by
  rw [lap_eq, Finset.mul_sum, mean_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := mean_D_mul i (P ^ (n + 1)) (D i P)
  rw [D_pow] at h
  have e : mean (((n + 1 : ℕ) : ℂ) • (P ^ n * D i P) * D i P) =
      ((n + 1 : ℕ) : ℂ) * mean (P ^ n * D i P ^ 2) := by
    rw [smul_mul_assoc, mean_smul, mul_assoc, sq]
  rw [e] at h
  linear_combination h

/-- **The transport has no mean against powers**: `∫ P^n (U·∇P) = 0`, `div U = 0`. -/
theorem mean_pow_trans {U : Fin 3 → Pol} (hU : DivFree U) (P : Pol) (n : ℕ) :
    mean (P ^ n * trans U P) = 0 := by
  have h : ((n + 1 : ℕ) : ℂ) * mean (P ^ n * trans U P) =
      -mean ((∑ i, D i (U i)) * P ^ (n + 1)) := by
    rw [Finset.sum_mul, mean_sum, ← Finset.sum_neg_distrib, trans, Finset.mul_sum, mean_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 := mean_D_mul i (U i) (P ^ (n + 1))
    rw [h2, neg_neg, D_pow, mul_smul_comm, mean_smul]
    congr 2
    ring
  rw [hU, zero_mul] at h
  have h3 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h4 : mean (0 : Pol) = 0 := rfl
  rw [h4, neg_zero] at h
  exact (mul_eq_zero.1 h).resolve_left h3

/-- `∂_i (U·∇g) = (∂_i U)·∇g + U·∇(∂_i g)`. -/
lemma D_trans (i : Fin 3) (U : Fin 3 → Pol) (g : Pol) :
    D i (trans U g) = ∑ j, D i (U j) * D j g + trans U (D i g) := by
  simp only [trans, D_sum, D_mul, Finset.sum_add_distrib, D_comm i]

/-- **The `H¹` commutator**: `∫ (U·∇g) Δg = −∑_{i,j} ∫ ∂_i U_j ∂_j g ∂_i g` for `div U = 0`. -/
theorem mean_trans_lap {U : Fin 3 → Pol} (hU : DivFree U) (g : Pol) :
    mean (trans U g * lap g) = -∑ i, ∑ j, mean (D i (U j) * D j g * D i g) := by
  rw [lap_eq, Finset.mul_sum, mean_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := mean_D_mul i (trans U g) (D i g)
  have h1 : mean (trans U g * D i (D i g)) = -mean (D i (trans U g) * D i g) := by
    rw [h, neg_neg]
  rw [h1, D_trans, add_mul, mean_add, Finset.sum_mul, mean_sum]
  have h2 := mean_pow_trans hU (D i g) 1
  rw [pow_one, mul_comm] at h2
  rw [h2, add_zero]

/-! ### Real polynomials, slow polynomials -/

/-- Hermitian coefficients: `ev P` is real. -/
def RealC (P : Pol) : Prop := ∀ k, P.coeff (-k) = conj (P.coeff k)

lemma conj_mFourier (k : Mode) (x : T3) : conj (mFourier k x) = mFourier (-k) x := by
  simp [mFourier_neg]

lemma RealC.conj_ev {P : Pol} (hP : RealC P) (x : T3) : conj (ev P x) = ev P x := by
  classical
  rw [ev_eq_tp, tp_apply, map_sum]
  have hmem : ∀ k, k ∈ P.coeff.support ↔ -k ∈ P.coeff.support := fun k => by
    simp only [Finsupp.mem_support_iff, hP k]
    exact (map_ne_zero (starRingEnd ℂ)).symm
  refine Finset.sum_bij' (fun k _ => -k) (fun k _ => -k) (fun k hk => (hmem k).1 hk)
    (fun k hk => (hmem k).1 hk) (fun k _ => neg_neg k) (fun k _ => neg_neg k) ?_
  intro k _
  rw [map_mul, conj_mFourier, hP k]

lemma RealC.im_ev {P : Pol} (hP : RealC P) (x : T3) : (ev P x).im = 0 :=
  Complex.conj_eq_iff_im.1 (hP.conj_ev x)

/-- A real polynomial takes the value of its real part. -/
lemma RealC.ev_eq {P : Pol} (hP : RealC P) (x : T3) : ev P x = ((ev P x).re : ℂ) :=
  Complex.ext rfl (by simp [hP.im_ev x])

lemma RealC.ev_sq {P : Pol} (hP : RealC P) (x : T3) :
    ev P x ^ 2 = ((‖ev P x‖ ^ 2 : ℝ) : ℂ) := by
  have h := hP.ev_eq x
  set a := (ev P x).re
  rw [h, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  push_cast
  ring

lemma RealC.D {P : Pol} (hP : RealC P) (i : Fin 3) : RealC (D i P) := fun k => by
  simp only [Slow.D, coeff_mult, dSym, map_mul, Complex.conj_I, map_intCast, hP k,
    Pi.neg_apply, Int.cast_neg]
  ring

lemma RealC.add {P Q : Pol} (hP : RealC P) (hQ : RealC Q) : RealC (P + Q) := fun k => by
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP k, hQ k, map_add]

/-- A polynomial on the slow modes. -/
def IsSlowP (P : Pol) : Prop := ∀ k, P.coeff k ≠ 0 → k 2 = 0

lemma IsSlowP.mul {P Q : Pol} (hP : IsSlowP P) (hQ : IsSlowP Q) : IsSlowP (P * Q) := by
  classical
  intro k hk
  have h := AddMonoidAlgebra.support_coeff_mul_subset P Q (Finsupp.mem_support_iff.2 hk)
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 h
  have h1 := hP a (Finsupp.mem_support_iff.1 ha)
  have h2 := hQ b (Finsupp.mem_support_iff.1 hb)
  simp [h1, h2]

lemma isSlowP_one : IsSlowP 1 := by
  classical
  intro k hk
  rw [AddMonoidAlgebra.one_def] at hk
  have : k = 0 := by
    by_contra h0
    apply hk
    simp [AddMonoidAlgebra.coeff_single, Ne.symm h0]
  simp [this]

lemma IsSlowP.pow {P : Pol} (hP : IsSlowP P) (n : ℕ) : IsSlowP (P ^ n) := by
  induction n with
  | zero => simpa using isSlowP_one
  | succ n ih => rw [pow_succ]; exact ih.mul hP

lemma IsSlowP.D {P : Pol} (hP : IsSlowP P) (i : Fin 3) : IsSlowP (D i P) := fun k hk => by
  refine hP k fun h => hk ?_
  simp [Slow.D, h]

/-! ### Norms and Parseval -/

/-- `‖P‖₂²`. -/
def nn2 (P : Pol) : ℝ := ∫ x, ‖ev P x‖ ^ 2 ∂μT

/-- `‖P‖₄⁴`. -/
def nn4 (P : Pol) : ℝ := ∫ x, ‖ev P x‖ ^ 4 ∂μT

/-- `‖∇P‖₂²`. -/
def grad2 (P : Pol) : ℝ := ∑ i, nn2 (D i P)

lemma nn2_nonneg (P : Pol) : 0 ≤ nn2 P := integral_nonneg fun _ => by positivity

lemma nn4_nonneg (P : Pol) : 0 ≤ nn4 P := integral_nonneg fun _ => by positivity

lemma grad2_nonneg (P : Pol) : 0 ≤ grad2 P := Finset.sum_nonneg fun _ _ => nn2_nonneg _

theorem hasSum_nn2 (P : Pol) : HasSum (fun k => ‖P.coeff k‖ ^ 2) (nn2 P) := by
  have h := hasSum_sq_coeff (ev P)
  simp only [coeff_ev] at h
  exact h

theorem hasSum_grad2 (P : Pol) : HasSum (fun k => absSq k * ‖P.coeff k‖ ^ 2) (grad2 P) := by
  have h : HasSum (fun k => ∑ i : Fin 3, ‖(Slow.D i P).coeff k‖ ^ 2) (grad2 P) :=
    hasSum_sum fun i _ => hasSum_nn2 (Slow.D i P)
  have e : (fun k => ∑ i : Fin 3, ‖(Slow.D i P).coeff k‖ ^ 2) =
      fun k => absSq k * ‖P.coeff k‖ ^ 2 := by
    funext k
    simp only [Slow.D, coeff_mult, norm_mul, dSym, Complex.norm_I, one_mul, mul_pow,
      Complex.norm_intCast, sq_abs, absSq, Finset.sum_mul]
  rwa [e] at h

/-- The mean is `≤` the `L²` norm. -/
lemma norm_mean_sq_le (P : Pol) : ‖mean P‖ ^ 2 ≤ nn2 P :=
  (hasSum_nn2 P).summable.le_tsum 0 (fun _ _ => by positivity) |>.trans_eq (hasSum_nn2 P).tsum_eq

/-- Removing the mean. -/
def zeroMean (P : Pol) : Pol := mult (fun k => if k = 0 then 0 else 1) P

lemma mean_zeroMean (P : Pol) : mean (zeroMean P) = 0 := by
  simp [mean, zeroMean]

lemma eq_zeroMean_add (P : Pol) : P = zeroMean P + single 0 (mean P) := by
  classical
  ext k
  by_cases hk : k = 0
  · subst hk
    simp [zeroMean, mean, AddMonoidAlgebra.coeff_single]
  · simp [zeroMean, hk, AddMonoidAlgebra.coeff_single]

lemma IsSlowP.zeroMean {P : Pol} (hP : IsSlowP P) : IsSlowP (zeroMean P) := fun k hk => by
  refine hP k fun h => hk ?_
  simp [Slow.zeroMean, h]

lemma coeff_zeroMean_norm_le (P : Pol) (k : Mode) : ‖(zeroMean P).coeff k‖ ≤ ‖P.coeff k‖ := by
  simp only [Slow.zeroMean, coeff_mult]
  split_ifs <;> simp

lemma nn2_zeroMean_le (P : Pol) : nn2 (zeroMean P) ≤ nn2 P :=
  hasSum_le (fun k => pow_le_pow_left₀ (norm_nonneg _) (coeff_zeroMean_norm_le P k) 2)
    (hasSum_nn2 _) (hasSum_nn2 P)

lemma grad2_zeroMean (P : Pol) : grad2 (zeroMean P) = grad2 P := by
  refine (hasSum_grad2 _).unique ?_
  have e : (fun k => absSq k * ‖(zeroMean P).coeff k‖ ^ 2) =
      fun k => absSq k * ‖P.coeff k‖ ^ 2 := by
    funext k
    by_cases hk : k = 0
    · subst hk
      have : absSq (0 : Mode) = 0 := by simp [absSq]
      simp [this]
    · simp [Slow.zeroMean, hk]
  rw [e]
  exact hasSum_grad2 P

/-! ### Ladyzhenskaya on slow polynomials -/

/-- **Ladyzhenskaya on mean-zero slow polynomials**: `‖G‖₄⁴ ≤ 25 ‖G‖₂² ‖∇G‖₂²`. -/
theorem lady_zero {G : Pol} (hs : IsSlowP G) (h0 : mean G = 0) :
    nn4 G ≤ 25 * nn2 G * grad2 G := by
  set a : Mode → ℝ := fun k => ‖G.coeff k‖ with ha
  have hA : SlowSeq a :=
    { nonneg := fun _ => norm_nonneg _
      slow := fun k hk => by
        simp only [ha, norm_eq_zero]
        by_contra h
        exact hk (hs k h)
      zero := by simpa [ha, mean] using h0
      grad := (hasSum_grad2 G).summable }
  obtain ⟨-, h2, h3⟩ := lady2d hA hA
  have e1 : ∑' k, a k ^ 2 = nn2 G := (hasSum_nn2 G).tsum_eq
  have e2 : ∑' k, absSq k * a k ^ 2 = grad2 G := (hasSum_grad2 G).tsum_eq
  rw [e1, e2] at h3
  have hsq : Real.sqrt (nn2 G) * Real.sqrt (grad2 G) * Real.sqrt (nn2 G) * Real.sqrt (grad2 G) =
      nn2 G * grad2 G := by
    have h1 := Real.mul_self_sqrt (nn2_nonneg G)
    have h2 := Real.mul_self_sqrt (grad2_nonneg G)
    calc _ = (Real.sqrt (nn2 G) * Real.sqrt (nn2 G)) *
          (Real.sqrt (grad2 G) * Real.sqrt (grad2 G)) := by ring
      _ = _ := by rw [h1, h2]
  have hP := hasSum_cv G.coeff.support G.coeff.support G.coeff G.coeff
  rw [← ev_eq_tp] at hP
  have e3 : ∫ x, ‖ev G x‖ ^ 2 * ‖ev G x‖ ^ 2 ∂μT = nn4 G :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [e3] at hP
  have htr : tr G.coeff.support G.coeff = G.coeff := by
    funext k
    simp only [tr]
    split_ifs with hk
    · rfl
    · simpa using (Finsupp.notMem_support_iff.1 hk).symm
  rw [htr] at hP
  have hfin : ∀ m, Summable fun p => ‖G.coeff p‖ * ‖G.coeff (m - p)‖ := fun m => by
    refine summable_of_ne_finset_zero (s := G.coeff.support) fun p hp => ?_
    simp [Finsupp.notMem_support_iff.1 hp]
  have hle : ∀ m, ‖cv G.coeff G.coeff m‖ ^ 2 ≤ convR a a m ^ 2 := fun m =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_cv_le (hfin m)) 2
  have h4 : nn4 G ≤ ∑' m, convR a a m ^ 2 := by
    rw [← hP.tsum_eq]
    exact hP.summable.tsum_le_tsum hle h2
  calc nn4 G ≤ _ := h4.trans h3
    _ = 25 * nn2 G * grad2 G := by
      rw [show 25 * Real.sqrt (nn2 G) * Real.sqrt (grad2 G) * Real.sqrt (nn2 G) *
        Real.sqrt (grad2 G) = 25 * (Real.sqrt (nn2 G) * Real.sqrt (grad2 G) * Real.sqrt (nn2 G) *
        Real.sqrt (grad2 G)) by ring, hsq]
      ring

/-- **Ladyzhenskaya on slow polynomials**: `‖G‖₄⁴ ≤ 200 ‖G‖₂² (‖G‖₂² + ‖∇G‖₂²)`. -/
theorem lady_poly {G : Pol} (hs : IsSlowP G) :
    nn4 G ≤ 200 * nn2 G * (nn2 G + grad2 G) := by
  set G₀ := zeroMean G with hG₀
  set c := mean G with hc
  have h4 := lady_zero hs.zeroMean (mean_zeroMean G)
  have hc2 := norm_mean_sq_le G
  have hN := nn2_nonneg G
  have hg := grad2_nonneg G
  have h0 := nn2_nonneg G₀
  have hG := eq_zeroMean_add G
  have hpt : ∀ x, ‖ev G x‖ ^ 4 ≤ 8 * (‖c‖ ^ 4 + ‖ev G₀ x‖ ^ 4) := fun x => by
    have e : ev G x = ev G₀ x + c := by
      conv_lhs => rw [hG]
      simp only [map_add, ev_single, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        mFourier_zero, smul_eq_mul]
      simp [hG₀, hc]
    have h1 : ‖ev G x‖ ≤ ‖ev G₀ x‖ + ‖c‖ := by rw [e]; exact norm_add_le _ _
    have h2 : ‖ev G x‖ ^ 4 ≤ (‖ev G₀ x‖ + ‖c‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h1 4
    have ha := norm_nonneg (ev G₀ x)
    have hb := norm_nonneg c
    nlinarith [sq_nonneg (‖ev G₀ x‖ ^ 2 - ‖c‖ ^ 2), sq_nonneg (‖ev G₀ x‖ - ‖c‖),
      mul_nonneg ha hb, sq_nonneg (‖ev G₀ x‖ ^ 2 + ‖c‖ ^ 2 - 2 * ‖ev G₀ x‖ * ‖c‖),
      sq_nonneg (‖ev G₀ x‖ * ‖c‖), mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖ev G₀ x‖ - ‖c‖))]
  have hI : nn4 G ≤ 8 * (‖c‖ ^ 4 + nn4 G₀) := by
    have hi1 : Integrable (fun x => ‖ev G x‖ ^ 4) μT :=
      integrable_of_continuous ((ev G).continuous.norm.pow 4)
    have hi2 : Integrable (fun x => ‖ev G₀ x‖ ^ 4) μT :=
      integrable_of_continuous ((ev G₀).continuous.norm.pow 4)
    have := integral_mono hi1 (((integrable_const (‖c‖ ^ 4)).add hi2).const_mul 8) hpt
    simpa [integral_const_mul, integral_add (integrable_const _) hi2, nn4] using this
  have h5 : ‖c‖ ^ 4 ≤ nn2 G ^ 2 := by
    have : ‖c‖ ^ 4 = (‖c‖ ^ 2) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) hc2 2
  have h6 : nn4 G₀ ≤ 25 * nn2 G * grad2 G := by
    refine h4.trans ?_
    rw [grad2_zeroMean]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (nn2_zeroMean_le G) (by norm_num)) hg
  nlinarith [mul_nonneg hN hg, mul_nonneg hN hN]

end OVNS.Quant.Slow
