import OddViscousNS.Quant.Joint.Interfaces
import OddViscousNS.Quant.Energy.Kinetic.Defs

/-!
# E4-J input: physical products on the torus and Gagliardo–Nirenberg (step J3)

Body 30 (LOCAL390): `‖DU‖₄² ≤ C M b`, `M = ‖U‖_∞`, `b = ‖U‖₂`.  Body 56 (LOCAL383): `‖S·∇F‖₂ ≤
M_∞ a_F`, `‖F·∇S‖₂ ≲ a_F D₄`, `‖Q(S,S)‖₀ ≲ M_∞ a_S`, "undo the filter and restore it after the
physical product".  All proved here, with absolute constants and no `sorry`.  The library lives on
Fourier coefficients and Mathlib has no product-to-convolution theorem, no Sobolev spaces on the
torus and no Young `ℓ^p ∗ ℓ^q`: this file needs none of the three.

## The objects
* `T3 = UnitAddTorus (Fin 3)`, `Mode` being its character lattice; `μT` is the measure of Mathlib's
  `mFourierCoeff`, which Mathlib fixes by a `local instance`, so it is named here (`rfl`).
* `M_∞` is `slowSup` (`Joint/Interfaces.lean`), the true sup of the absolutely convergent series
  `physS` on the horizontal torus.  `SupBd u M` is the same bound on `T3`; everything below is
  3D and needs no slow structure, except `supBd_of_physS`, `supBd_slowSup` (the bridge).
* `tp A c = ∑_{k ∈ A} c_k e_k` (a polynomial), `cv` the convolution, `tr` the truncation, `dC i` the
  multiplier `I k_i`, that is `∂_i` on coefficients.

## The proof
* `coeff_tp_mul`: the coefficients of a product of polynomials are the convolution; with Mathlib's
  Parseval this gives `hasSum_cv`, `∑_m |(a ∗ b)_m|² = ∫ |a|²|b|²`.  So `‖v‖₄⁴ = ‖v ∗ v‖²_{ℓ²}`
  (`L4sq`, `L4sq_tr_sq`): the `L⁴` norm is a Fourier object, which needs no function space.
* `leibniz_four`: `∫ ∂_i (a b̄ c d̄) = 0`, a statement about finite sums: the whole calculus.
* `gn_tp`: `‖∂_i u‖₄⁴ ≤ 9 ‖u‖_∞² ‖∂_i² u‖₂²` on polynomials, from `∫ ∂_i (u v̄ v v̄) = 0`,
  `v = ∂_i u`, and Young.  One direction at a time, in any dimension: no tensors.
* `cv_fatou`: Fatou in the truncation.  For `u ∈ H²` the coefficients of `u` are `ℓ¹` but those of
  `∂_i u` need not be; `u` is approximated uniformly by its truncations (`norm_tp_le`,
  `tendsto_tailN`), so the sup norm passes to the limit.  No heat regularization, no `H³`: all at
  fixed time on `H²`.
* `sob_conv`: Sobolev `H¹ ⊂ L⁴` on `T³`, `‖a ∗ a‖²_{ℓ²} ≤ c₄² ‖a‖₁⁴`, by weighted Cauchy–Schwarz
  with the library's `c₄² = ∑|k|⁻⁴` (it replaces Hausdorff–Young and the inverse fourth sum).
* Outputs: `gn_cv`, `gn_field`, `gn_tensor` (Gagliardo–Nirenberg), `gn_product`, `sup_product`
  (scalar products), `advect_gn`, `advect_sup`, `hnorm_Qphase_mixed`, `hnorm_Qphase_slow` (fields).
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.GN

/-! ### The torus, its Haar measure and trigonometric polynomials -/

/-- The physical 3-torus `ℝ³/ℤ³`; `Mode = Fin 3 → ℤ` is its character lattice. -/
abbrev T3 : Type := UnitAddTorus (Fin 3)

/-- The normalized Haar measure of `T3`: this is the measure of Mathlib's `mFourierCoeff`, which
Mathlib fixes through a `local instance`. -/
def μT : Measure T3 := Measure.pi fun _ => AddCircle.haarAddCircle

instance : IsProbabilityMeasure μT := by
  unfold μT
  infer_instance

section Local

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Orthogonality of the characters. -/
theorem integral_mFourier (k : Mode) :
    ∫ x, mFourier k x ∂μT = if k = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin 3))) 0 k
  rw [ContinuousMap.inner_toLp] at h
  have e : ∀ x : T3, mFourier k x * conj (mFourier (0 : Mode) x) = mFourier k x := fun x => by
    simp [mFourier_zero]
  simp only [e] at h
  refine h.trans ?_
  simp only [eq_comm]

/-- **Parseval** for a continuous function on `T3` (Mathlib, through the `toLp` embedding). -/
theorem hasSum_sq_coeff (h : C(T3, ℂ)) :
    HasSum (fun m => ‖mFourierCoeff h m‖ ^ 2) (∫ x, ‖h x‖ ^ 2 ∂μT) := by
  have h1 := hasSum_sq_mFourierCoeff (ContinuousMap.toLp 2 (volume : Measure T3) ℂ h)
  simp only [mFourierCoeff_toLp] at h1
  have e : ∫ t, ‖(ContinuousMap.toLp 2 (volume : Measure T3) ℂ h) t‖ ^ 2 ∂volume =
      ∫ x, ‖h x‖ ^ 2 ∂μT := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure T3) h] with x hx
    rw [hx]
  rw [e] at h1
  exact h1

end Local

theorem mFourierCoeff_eq (h : T3 → ℂ) (m : Mode) :
    mFourierCoeff h m = ∫ x, mFourier (-m) x * h x ∂μT := rfl

/-- Continuous functions are integrable on the torus. -/
lemma integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {f : T3 → E}
    (hf : Continuous f) : Integrable f μT :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The mean of a continuous function, as a linear functional. -/
def J : C(T3, ℂ) →ₗ[ℂ] ℂ where
  toFun h := ∫ x, h x ∂μT
  map_add' f g := integral_add (integrable_of_continuous f.continuous)
    (integrable_of_continuous g.continuous)
  map_smul' c f := by
    simp only [ContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    exact integral_const_mul c _

lemma J_apply (h : C(T3, ℂ)) : J h = ∫ x, h x ∂μT := rfl

lemma J_mFourier (k : Mode) : J (mFourier k) = if k = 0 then 1 else 0 := integral_mFourier k

/-- The trigonometric polynomial `∑_{k ∈ A} c_k e_k`. -/
def tp (A : Finset Mode) (c : Mode → ℂ) : C(T3, ℂ) := ∑ k ∈ A, c k • mFourier k

lemma tp_apply (A : Finset Mode) (c : Mode → ℂ) (x : T3) :
    tp A c x = ∑ k ∈ A, c k * mFourier k x := by
  simp [tp, ContinuousMap.sum_apply]

lemma mFourier_mul' (k l : Mode) :
    (mFourier k * mFourier l : C(T3, ℂ)) = mFourier (k + l) := by
  ext x
  simp [mFourier_add]

lemma star_mFourier' (k : Mode) : star (mFourier k : C(T3, ℂ)) = mFourier (-k) := by
  ext x
  simp [mFourier_neg]

lemma star_tp (A : Finset Mode) (c : Mode → ℂ) :
    star (tp A c) = ∑ k ∈ A, conj (c k) • mFourier (-k) := by
  simp only [tp, star_sum, star_smul, star_mFourier']
  rfl

/-- The four-fold expansion of the mean of `a b̄ c d̄`. -/
lemma J_four (A : Finset Mode) (a b c d : Mode → ℂ) :
    J (tp A a * star (tp A b) * tp A c * star (tp A d)) =
      ∑ k₄ ∈ A, ∑ k₃ ∈ A, ∑ k₂ ∈ A, ∑ k₁ ∈ A,
        a k₁ * conj (b k₂) * c k₃ * conj (d k₄) *
          (if k₁ + -k₂ + k₃ + -k₄ = 0 then 1 else 0) := by
  rw [star_tp, star_tp]
  unfold tp
  have e : (∑ k ∈ A, a k • (mFourier k : C(T3, ℂ))) * (∑ k ∈ A, conj (b k) • mFourier (-k)) *
      (∑ k ∈ A, c k • mFourier k) * (∑ k ∈ A, conj (d k) • mFourier (-k)) =
      ∑ k₄ ∈ A, ∑ k₃ ∈ A, ∑ k₂ ∈ A, ∑ k₁ ∈ A,
        (a k₁ * conj (b k₂) * c k₃ * conj (d k₄)) • mFourier (k₁ + -k₂ + k₃ + -k₄) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k₄ _ => Finset.sum_congr rfl fun k₃ _ =>
      Finset.sum_congr rfl fun k₂ _ => Finset.sum_congr rfl fun k₁ _ => ?_
    simp only [smul_mul_smul_comm, mFourier_mul']
  rw [e]
  simp only [map_sum, map_smul, J_mFourier, smul_eq_mul]

/-- The Fourier multiplier `I k_i`: the derivative `∂_i` on coefficients. -/
def dC (i : Fin 3) (c : Mode → ℂ) : Mode → ℂ := fun k => Complex.I * (k i : ℂ) * c k

/-- **The Leibniz rule under the mean**: `∫ ∂_i (a b̄ c d̄) = 0` on trigonometric polynomials.  This
is all the calculus the Gagliardo–Nirenberg inequality needs: a statement about finite sums. -/
theorem leibniz_four (A : Finset Mode) (a b c d : Mode → ℂ) (i : Fin 3) :
    J (tp A (dC i a) * star (tp A b) * tp A c * star (tp A d)) +
      J (tp A a * star (tp A (dC i b)) * tp A c * star (tp A d)) +
      J (tp A a * star (tp A b) * tp A (dC i c) * star (tp A d)) +
      J (tp A a * star (tp A b) * tp A c * star (tp A (dC i d))) = 0 := by
  simp only [J_four, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k₄ _ => Finset.sum_eq_zero fun k₃ _ =>
    Finset.sum_eq_zero fun k₂ _ => Finset.sum_eq_zero fun k₁ _ => ?_
  by_cases h : k₁ + -k₂ + k₃ + -k₄ = 0
  · have hi : (k₁ i : ℂ) - k₂ i + k₃ i - k₄ i = 0 := by
      have := congrFun h i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at this
      have h' : (k₁ i : ℤ) - k₂ i + k₃ i - k₄ i = 0 := by omega
      exact_mod_cast h'
    simp only [h, ↓reduceIte, dC, map_mul, Complex.conj_I, map_intCast, mul_one]
    linear_combination (Complex.I * a k₁ * conj (b k₂) * c k₃ * conj (d k₄)) * hi
  · simp [h]

/-! ### The Gagliardo–Nirenberg inequality on trigonometric polynomials -/

/-- The mean of a function dominated by a continuous `g`. -/
lemma norm_J_le {h : C(T3, ℂ)} {g : T3 → ℝ} (hg : Continuous g) (hle : ∀ x, ‖h x‖ ≤ g x) :
    ‖J h‖ ≤ ∫ x, g x ∂μT := by
  rw [J_apply]
  refine (norm_integral_le_integral_norm _).trans ?_
  exact integral_mono (integrable_of_continuous h.continuous.norm)
    (integrable_of_continuous hg) hle

/-- **Gagliardo–Nirenberg on polynomials** (Body 30, one derivative direction at a time):
`‖∂_i u‖₄⁴ ≤ 9 ‖u‖_∞² ‖∂_i² u‖₂²`.  From `∫ ∂_i (u v̄ v v̄) = 0`, `v = ∂_i u`, `w = ∂_i v`:
`∫|v|⁴ ≤ 3 M ∫ |v|²|w|`, and Young with weight `3M`. -/
theorem gn_tp (A : Finset Mode) (u : Mode → ℂ) (i : Fin 3) {M : ℝ}
    (hM : ∀ x, ‖tp A u x‖ ≤ M) :
    ∫ x, ‖tp A (dC i u) x‖ ^ 4 ∂μT ≤ 9 * M ^ 2 * ∫ x, ‖tp A (dC i (dC i u)) x‖ ^ 2 ∂μT := by
  set f := tp A u with hf
  set v := tp A (dC i u) with hv
  set w := tp A (dC i (dC i u)) with hw
  have hL := leibniz_four A u (dC i u) (dC i u) (dC i u) i
  rw [← hf, ← hv, ← hw] at hL
  have hcv : Continuous fun x => ‖v x‖ := v.continuous.norm
  have hcw : Continuous fun x => ‖w x‖ := w.continuous.norm
  set X := ∫ x, ‖v x‖ ^ 4 ∂μT with hX
  set Z := ∫ x, ‖w x‖ ^ 2 ∂μT with hZ
  have hX0 : 0 ≤ X := integral_nonneg fun x => by positivity
  have e1 : J (v * star v * v * star v) = (X : ℂ) := by
    rw [J_apply, hX, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have h1 : (star (v x)) * v x = ((‖v x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow]
      exact Complex.conj_mul' (v x)
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply]
    calc v x * star (v x) * v x * star (v x) = (star (v x) * v x) ^ 2 := by ring
      _ = ((‖v x‖ ^ 4 : ℝ) : ℂ) := by rw [h1]; push_cast; ring
  set g : T3 → ℝ := fun x => M * (‖w x‖ * ‖v x‖ ^ 2) with hg
  have hgc : Continuous g := (continuous_const.mul (hcw.mul (hcv.pow 2)))
  have hfM : ∀ x, ‖f x‖ * (‖w x‖ * ‖v x‖ ^ 2) ≤ g x := fun x =>
    mul_le_mul_of_nonneg_right (hM x) (by positivity)
  have e2 : ‖J (f * star w * v * star v)‖ ≤ ∫ x, g x ∂μT := norm_J_le hgc fun x => by
    refine le_trans (le_of_eq ?_) (hfM x)
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, norm_mul, norm_star]
    ring
  have e3 : ‖J (f * star v * w * star v)‖ ≤ ∫ x, g x ∂μT := norm_J_le hgc fun x => by
    refine le_trans (le_of_eq ?_) (hfM x)
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, norm_mul, norm_star]
    ring
  have e4 : ‖J (f * star v * v * star w)‖ ≤ ∫ x, g x ∂μT := norm_J_le hgc fun x => by
    refine le_trans (le_of_eq ?_) (hfM x)
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, norm_mul, norm_star]
    ring
  have hX3 : X ≤ 3 * ∫ x, g x ∂μT := by
    have h := congrArg norm (show (X : ℂ) = -(J (f * star w * v * star v) +
        J (f * star v * w * star v) + J (f * star v * v * star w)) by
      rw [← e1]
      linear_combination hL)
    rw [Complex.norm_real, Real.norm_of_nonneg hX0, norm_neg] at h
    rw [h]
    exact (norm_add₃_le).trans (by linarith)
  have hY : 3 * ∫ x, g x ∂μT ≤ (9 * M ^ 2 * Z + X) / 2 := by
    have hc1 : Continuous fun x => 9 * M ^ 2 * ‖w x‖ ^ 2 := continuous_const.mul (hcw.pow 2)
    have hc2 : Continuous fun x => ‖v x‖ ^ 4 := hcv.pow 4
    have h1 : ∫ x, 3 * g x ∂μT ≤ ∫ x, (9 * M ^ 2 * ‖w x‖ ^ 2 + ‖v x‖ ^ 4) / 2 ∂μT := by
      refine integral_mono (integrable_of_continuous (continuous_const.mul hgc))
        (integrable_of_continuous ((hc1.add hc2).div_const _)) fun x => ?_
      simp only [hg]
      nlinarith [sq_nonneg (3 * M * ‖w x‖ - ‖v x‖ ^ 2)]
    have h2 : ∫ x, (9 * M ^ 2 * ‖w x‖ ^ 2 + ‖v x‖ ^ 4) / 2 ∂μT = (9 * M ^ 2 * Z + X) / 2 := by
      rw [integral_div, integral_add (integrable_of_continuous hc1) (integrable_of_continuous hc2),
        integral_const_mul]
    rw [integral_const_mul] at h1
    linarith
  linarith

/-! ### Convolution of coefficient sequences -/

/-- The convolution `∑_p a_p b_{m−p}`. -/
def cv (a b : Mode → ℂ) (m : Mode) : ℂ := ∑' p, a p * b (m - p)

/-- The truncation of a sequence to `A`. -/
def tr (A : Finset Mode) (c : Mode → ℂ) : Mode → ℂ := fun k => if k ∈ A then c k else 0

lemma cv_tr (A B : Finset Mode) (a b : Mode → ℂ) (m : Mode) :
    cv (tr A a) (tr B b) m =
      ∑ p ∈ A, ∑ q ∈ B, a p * b q * (if -m + (p + q) = 0 then 1 else 0) := by
  rw [cv, tsum_eq_sum (s := A) fun p hp => by simp [tr, hp]]
  refine Finset.sum_congr rfl fun p hp => ?_
  have e : ∀ q, (-m + (p + q) = 0) ↔ q = m - p := fun q => by
    constructor
    · intro h
      funext i
      have := congrFun h i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, Pi.sub_apply] at this ⊢
      omega
    · rintro rfl
      funext i
      simp
  simp only [e, tr, hp, ↓reduceIte, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']

/-- The product of two polynomials has the convolution of their coefficients: this is the
product-to-convolution theorem, which Mathlib lacks, for finitely supported sequences. -/
theorem coeff_tp_mul (A B : Finset Mode) (a b : Mode → ℂ) (m : Mode) :
    mFourierCoeff (tp A a * tp B b : C(T3, ℂ)) m = cv (tr A a) (tr B b) m := by
  rw [mFourierCoeff_eq, cv_tr]
  have e : (mFourier (-m) : C(T3, ℂ)) * (tp A a * tp B b) =
      ∑ q ∈ B, ∑ p ∈ A, (a p * b q) • mFourier (-m + (p + q)) := by
    unfold tp
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    simp only [mul_smul_comm, smul_mul_assoc, mFourier_mul', smul_smul]
    rw [mul_comm (b q)]
  have e2 : ∫ x, mFourier (-m) x * (tp A a * tp B b : C(T3, ℂ)) x ∂μT =
      J ((mFourier (-m) : C(T3, ℂ)) * (tp A a * tp B b)) := rfl
  rw [e2, e, Finset.sum_comm]
  simp only [map_sum, map_smul, J_mFourier, smul_eq_mul]

lemma coeff_tp (A : Finset Mode) (c : Mode → ℂ) (m : Mode) :
    mFourierCoeff (tp A c : C(T3, ℂ)) m = tr A c m := by
  rw [mFourierCoeff_eq]
  have e : (mFourier (-m) : C(T3, ℂ)) * tp A c = ∑ p ∈ A, c p • mFourier (-m + p) := by
    unfold tp
    simp only [Finset.mul_sum, mul_smul_comm, mFourier_mul']
  have e2 : ∫ x, mFourier (-m) x * (tp A c : C(T3, ℂ)) x ∂μT =
      J ((mFourier (-m) : C(T3, ℂ)) * tp A c) := rfl
  rw [e2, e]
  simp only [map_sum, map_smul, J_mFourier, smul_eq_mul]
  have e3 : ∀ p, (-m + p = 0) ↔ p = m := fun p => by
    constructor
    · intro h
      funext i
      have := congrFun h i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at this
      omega
    · rintro rfl
      simp
  simp only [e3, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', tr]

/-- Parseval for a polynomial. -/
theorem integral_norm_sq_tp (A : Finset Mode) (c : Mode → ℂ) :
    ∫ x, ‖tp A c x‖ ^ 2 ∂μT = ∑ k ∈ A, ‖c k‖ ^ 2 := by
  have h := hasSum_sq_coeff (tp A c)
  simp only [coeff_tp] at h
  have h2 : HasSum (fun m => ‖tr A c m‖ ^ 2) (∑ k ∈ A, ‖tr A c k‖ ^ 2) :=
    hasSum_sum_of_ne_finset_zero fun m hm => by simp [tr, hm]
  rw [h.unique h2]
  exact Finset.sum_congr rfl fun k hk => by simp [tr, hk]

/-- Parseval for a product of two polynomials: `∑_m |(a ∗ b)_m|² = ∫ |a|²|b|²`. -/
theorem hasSum_cv (A B : Finset Mode) (a b : Mode → ℂ) :
    HasSum (fun m => ‖cv (tr A a) (tr B b) m‖ ^ 2)
      (∫ x, ‖tp A a x‖ ^ 2 * ‖tp B b x‖ ^ 2 ∂μT) := by
  have h := hasSum_sq_coeff (tp A a * tp B b)
  simp only [coeff_tp_mul, ContinuousMap.mul_apply, norm_mul, mul_pow] at h
  exact h

/-! ### Sobolev on `T³`: `‖G‖₄² ≤ c₄ ‖G‖₁²` for mean-zero `G` -/

/-- The shear `(k, p) ↦ (p, k − p)` of the lattice square. -/
private def shear : Mode × Mode ≃ Mode × Mode where
  toFun z := (z.2, z.1 - z.2)
  invFun z := (z.1 + z.2, z.1)
  left_inv z := by simp
  right_inv z := by simp

/-- Tonelli for the convolution of two nonnegative summable sequences. -/
private lemma tonelli_conv {α γ : Mode → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hγ0 : ∀ k, 0 ≤ γ k)
    (hα : Summable α) (hγ : Summable γ) :
    Summable (fun k => ∑' p, α p * γ (k - p)) ∧
      ∑' k, ∑' p, α p * γ (k - p) = (∑' k, α k) * ∑' k, γ k := by
  have hG : Summable fun z : Mode × Mode => α z.1 * γ z.2 := hα.mul_of_nonneg hγ hα0 hγ0
  have hF : Summable fun z : Mode × Mode => α z.2 * γ (z.1 - z.2) := shear.summable_iff.2 hG
  refine ⟨hF.prod, ?_⟩
  rw [hα.tsum_mul_tsum hγ hG, ← shear.tsum_eq (fun z : Mode × Mode => α z.1 * γ z.2)]
  exact (hF.tsum_prod).symm

/-- The inverse weight `|k|⁻²`, `0` at the origin. -/
private def kap (k : Mode) : ℝ := if k = 0 then 0 else (absSq k)⁻¹

private lemma kap_nonneg (k : Mode) : 0 ≤ kap k := by
  unfold kap
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.2 (absSq_nonneg k)

private lemma kap_sq (k : Mode) :
    kap k ^ 2 = if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2 := by
  unfold kap
  split_ifs <;> simp

private lemma summable_kap_sq : Summable fun k => kap k ^ 2 := by
  simpa only [kap_sq] using summable_inv4

private lemma tsum_kap_sq : ∑' k, kap k ^ 2 = c4 ^ 2 := by
  have h0 : 0 ≤ ∑' k : Mode, if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2 :=
    tsum_nonneg fun k => by split_ifs <;> positivity
  rw [c4, Real.sq_sqrt h0]
  simp only [kap_sq]

/-- `√κ_p √α_p = a_p`, for `α = |k|² a²`, `a₀ = 0`. -/
private lemma sqrt_kap_mul {a : Mode → ℝ} (ha0 : ∀ k, 0 ≤ a k) (hz : a 0 = 0) (p : Mode) :
    Real.sqrt (kap p) * Real.sqrt (absSq p * a p ^ 2) = a p := by
  by_cases hp : p = 0
  · subst hp
    simp [hz]
  · have h1 : absSq p ≠ 0 := by
      have := one_le_absSq hp
      linarith
    rw [← Real.sqrt_mul (kap_nonneg p)]
    simp only [kap, hp, ↓reduceIte]
    rw [← mul_assoc, inv_mul_cancel₀ h1, one_mul, Real.sqrt_sq (ha0 p)]

/-- **Sobolev `H¹ ⊂ L⁴` on `T³`, Fourier side**, by weighted Cauchy–Schwarz: no Young
`ℓ^{4/3} ∗ ℓ^{4/3}`, no Hausdorff–Young.  For `a ≥ 0`, `a₀ = 0`:
`‖a ∗ a‖²_{ℓ²} ≤ c₄² (∑ |k|² a_k²)²`, with `c₄² = ∑_{k ≠ 0} |k|⁻⁴`. -/
theorem sob_conv {a : Mode → ℝ} (ha0 : ∀ k, 0 ≤ a k) (hz : a 0 = 0)
    (hs : Summable fun k => absSq k * a k ^ 2) :
    Summable (fun m => convR a a m ^ 2) ∧
      ∑' m, convR a a m ^ 2 ≤ c4 ^ 2 * (∑' k, absSq k * a k ^ 2) ^ 2 := by
  set α : Mode → ℝ := fun k => absSq k * a k ^ 2 with hα
  have hα0 : ∀ k, 0 ≤ α k := fun k => mul_nonneg (absSq_nonneg k) (sq_nonneg _)
  obtain ⟨hT, hTe⟩ := tonelli_conv hα0 hα0 hs hs
  have hT0 : ∀ m, 0 ≤ ∑' p, α p * α (m - p) := fun m =>
    tsum_nonneg fun p => mul_nonneg (hα0 p) (hα0 _)
  have hpt : ∀ m, convR a a m ^ 2 ≤ c4 ^ 2 * ∑' p, α p * α (m - p) := fun m => by
    set x : Mode → ℝ := fun p => Real.sqrt (kap p) * Real.sqrt (kap (m - p)) with hx
    set y : Mode → ℝ := fun p => Real.sqrt (α p) * Real.sqrt (α (m - p)) with hy
    have hx0 : ∀ p, 0 ≤ x p := fun p => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hy0 : ∀ p, 0 ≤ y p := fun p => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hxy : ∀ p, x p * y p = a p * a (m - p) := fun p => by
      have e1 := sqrt_kap_mul ha0 hz p
      have e2 := sqrt_kap_mul ha0 hz (m - p)
      calc x p * y p = (Real.sqrt (kap p) * Real.sqrt (absSq p * a p ^ 2)) *
            (Real.sqrt (kap (m - p)) * Real.sqrt (absSq (m - p) * a (m - p) ^ 2)) := by
            simp only [hx, hy, hα]
            ring
        _ = a p * a (m - p) := by rw [e1, e2]
    have hx2 : ∀ p, x p ^ 2 = kap p * kap (m - p) := fun p => by
      simp only [hx]
      rw [mul_pow, Real.sq_sqrt (kap_nonneg p), Real.sq_sqrt (kap_nonneg _)]
    have hy2 : ∀ p, y p ^ 2 = α p * α (m - p) := fun p => by
      simp only [hy]
      rw [mul_pow, Real.sq_sqrt (hα0 p), Real.sq_sqrt (hα0 _)]
    have hk := cs_equiv kap_nonneg kap_nonneg summable_kap_sq summable_kap_sq (Equiv.subLeft m)
    simp only [Equiv.subLeft_apply] at hk
    have hxs : Summable fun p => x p ^ 2 := by
      simp only [hx2]
      exact hk.1
    have hys : Summable fun p => y p ^ 2 := by
      simp only [hy2]
      have hB : ∀ q, α q ≤ ∑' q, α q := fun q => hs.le_tsum q fun j _ => hα0 j
      exact Summable.of_nonneg_of_le (fun p => mul_nonneg (hα0 p) (hα0 _))
        (fun p => mul_le_mul_of_nonneg_left (hB _) (hα0 p)) (hs.mul_right (∑' q, α q))
    have hcs := cs_equiv hx0 hy0 hxs hys (Equiv.refl Mode)
    simp only [Equiv.refl_apply, hxy] at hcs
    have hc0 : 0 ≤ convR a a m := tsum_nonneg fun p => mul_nonneg (ha0 p) (ha0 _)
    have hX0 : 0 ≤ ∑' p, x p ^ 2 := tsum_nonneg fun p => sq_nonneg _
    have hY0 : 0 ≤ ∑' p, y p ^ 2 := tsum_nonneg fun p => sq_nonneg _
    have hXle : ∑' p, x p ^ 2 ≤ c4 ^ 2 := by
      simp only [hx2]
      refine hk.2.trans (le_of_eq ?_)
      rw [Real.mul_self_sqrt (tsum_nonneg fun k => sq_nonneg _), tsum_kap_sq]
    calc convR a a m ^ 2 ≤ (Real.sqrt (∑' p, x p ^ 2) * Real.sqrt (∑' p, y p ^ 2)) ^ 2 :=
          pow_le_pow_left₀ hc0 hcs.2 2
      _ = (∑' p, x p ^ 2) * ∑' p, y p ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hX0, Real.sq_sqrt hY0]
      _ ≤ c4 ^ 2 * ∑' p, y p ^ 2 := mul_le_mul_of_nonneg_right hXle hY0
      _ = c4 ^ 2 * ∑' p, α p * α (m - p) := by simp only [hy2]
  have hsum : Summable fun m => c4 ^ 2 * ∑' p, α p * α (m - p) := hT.mul_left _
  have hS := Summable.of_nonneg_of_le (fun m => sq_nonneg _) hpt hsum
  refine ⟨hS, ?_⟩
  calc ∑' m, convR a a m ^ 2 ≤ ∑' m, c4 ^ 2 * ∑' p, α p * α (m - p) :=
        hS.tsum_le_tsum hpt hsum
    _ = c4 ^ 2 * (∑' k, α k) ^ 2 := by rw [tsum_mul_left, hTe, sq (∑' k, α k)]

lemma norm_cv_le {a b : Mode → ℂ} {m : Mode} (h : Summable fun p => ‖a p‖ * ‖b (m - p)‖) :
    ‖cv a b m‖ ≤ convR (fun k => ‖a k‖) (fun k => ‖b k‖) m := by
  rw [cv, convR]
  exact tsum_of_norm_bounded h.hasSum fun p => (norm_mul_le _ _)

/-- `‖tp A G‖₄⁴ ≤ c₄² ‖G‖₁⁴` on mean-zero `G`, uniformly in the truncation. -/
theorem L4_tp_le (A : Finset Mode) {G : Mode → ℂ} (hG0 : G 0 = 0)
    (hs : Summable fun k => absSq k * ‖G k‖ ^ 2) :
    ∫ x, ‖tp A G x‖ ^ 4 ∂μT ≤ c4 ^ 2 * (∑' k, absSq k * ‖G k‖ ^ 2) ^ 2 := by
  set a : Mode → ℝ := fun k => ‖tr A G k‖ with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => norm_nonneg _
  have haz : a 0 = 0 := by
    simp only [ha, tr]
    split_ifs <;> simp [hG0]
  have hle1 : ∀ k, absSq k * a k ^ 2 ≤ absSq k * ‖G k‖ ^ 2 := fun k => by
    refine mul_le_mul_of_nonneg_left ?_ (absSq_nonneg k)
    simp only [ha, tr]
    split_ifs
    · exact le_rfl
    · simp
  have hsa : Summable fun k => absSq k * a k ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (absSq_nonneg k) (sq_nonneg _)) hle1 hs
  obtain ⟨h1, h2⟩ := sob_conv ha0 haz hsa
  have hP := hasSum_cv A A G G
  have e : ∫ x, ‖tp A G x‖ ^ 2 * ‖tp A G x‖ ^ 2 ∂μT = ∫ x, ‖tp A G x‖ ^ 4 ∂μT := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [e] at hP
  have hfin : ∀ m, Summable fun p => ‖tr A G p‖ * ‖tr A G (m - p)‖ := fun m => by
    refine summable_of_ne_finset_zero (s := A) fun p hp => ?_
    simp [tr, hp]
  have hpt : ∀ m, ‖cv (tr A G) (tr A G) m‖ ^ 2 ≤ convR a a m ^ 2 := fun m =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_cv_le (hfin m)) 2
  have h3 : ∑' m, ‖cv (tr A G) (tr A G) m‖ ^ 2 ≤ ∑' m, convR a a m ^ 2 :=
    hP.summable.tsum_le_tsum hpt h1
  have h4 : ∑' k, absSq k * a k ^ 2 ≤ ∑' k, absSq k * ‖G k‖ ^ 2 := hsa.tsum_le_tsum hle1 hs
  have h5 : 0 ≤ ∑' k, absSq k * a k ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (absSq_nonneg k) (sq_nonneg _)
  rw [← hP.tsum_eq]
  refine h3.trans (h2.trans ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h5 h4 2) (by positivity)

/-- Cauchy–Schwarz on the torus. -/
lemma integral_mul_le_sqrt {f g : T3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    ∫ x, f x * g x ∂μT ≤ Real.sqrt (∫ x, f x ^ 2 ∂μT) * Real.sqrt (∫ x, g x ^ 2 ∂μT) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μT) Real.HolderConjugate.two_two
    (Eventually.of_forall hf0) (Eventually.of_forall hg0)
    (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using h

/-! ### Passing to the limit: `ℓ¹` and Sobolev coefficients -/

/-- **Fatou in the truncation**: a bound on the polynomial truncations of `a`, `b` passes to the
`ℓ²` norm of `a ∗ b`.  This is the only limit taken; it needs no function space on the torus. -/
theorem cv_fatou {a b : Mode → ℂ} {B : ℝ} {B' : Finset Mode → ℝ}
    (hab : ∀ m, Summable fun p => ‖a p‖ * ‖b (m - p)‖)
    (hle : ∀ A, ∫ x, ‖tp A a x‖ ^ 2 * ‖tp A b x‖ ^ 2 ∂μT ≤ B' A)
    (hB : Tendsto B' atTop (𝓝 B)) :
    Summable (fun m => ‖cv a b m‖ ^ 2) ∧ ∑' m, ‖cv a b m‖ ^ 2 ≤ B := by
  have hpt : ∀ m, Tendsto (fun A : Finset Mode => cv (tr A a) (tr A b) m) atTop (𝓝 (cv a b m)) := by
    intro m
    refine tendsto_tsum_of_dominated_convergence (hab m) (fun p => ?_) (Eventually.of_forall ?_)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ({p, m - p} : Finset Mode)] with A hA
      have h1 : p ∈ A := hA (by simp)
      have h2 : m - p ∈ A := hA (by simp)
      simp [tr, h1, h2]
    · intro A p
      rw [norm_mul]
      refine mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _)
      · simp only [tr]
        split_ifs <;> simp
      · simp only [tr]
        split_ifs <;> simp
  have key : ∀ K : Finset Mode, ∑ m ∈ K, ‖cv a b m‖ ^ 2 ≤ B := fun K => by
    have h1 : Tendsto (fun A : Finset Mode => ∑ m ∈ K, ‖cv (tr A a) (tr A b) m‖ ^ 2) atTop
        (𝓝 (∑ m ∈ K, ‖cv a b m‖ ^ 2)) :=
      tendsto_finsetSum _ fun m _ => ((hpt m).norm).pow 2
    refine le_of_tendsto_of_tendsto' h1 hB fun A => ?_
    exact (sum_le_hasSum K (fun m _ => by positivity) (hasSum_cv A A a b)).trans (hle A)
  have h0 : 0 ≤ fun m => ‖cv a b m‖ ^ 2 := fun m => by positivity
  exact ⟨summable_of_sum_le h0 key, Real.tsum_le_of_sum_le h0 key⟩

/-- The `ℓ¹` tail of a truncation. -/
def tailN (u : Mode → ℂ) (A : Finset Mode) : ℝ := ∑' k, ‖u k - tr A u k‖

lemma tendsto_tailN {u : Mode → ℂ} (hu : Summable fun k => ‖u k‖) :
    Tendsto (tailN u) atTop (𝓝 0) := by
  have h : Tendsto (fun A : Finset Mode => ∑' k, ‖u k - tr A u k‖) atTop
      (𝓝 (∑' _ : Mode, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hu (fun k => ?_) (Eventually.of_forall ?_)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ({k} : Finset Mode)] with A hA
      have h1 : k ∈ A := hA (by simp)
      simp [tr, h1]
    · intro A k
      rw [norm_norm]
      simp only [tr]
      split_ifs <;> simp
  rw [tsum_zero] at h
  exact h

lemma tailN_nonneg (u : Mode → ℂ) (A : Finset Mode) : 0 ≤ tailN u A :=
  tsum_nonneg fun _ => norm_nonneg _

lemma summable_tailN {u : Mode → ℂ} (hu : Summable fun k => ‖u k‖) (A : Finset Mode) :
    Summable fun k => ‖u k - tr A u k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hu
  simp only [tr]
  split_ifs <;> simp

/-- The sup norm of a truncation. -/
lemma norm_tp_le {u : Mode → ℂ} (hu : Summable fun k => ‖u k‖) {M : ℝ}
    (hM : ∀ x, ‖∑' k, u k * mFourier k x‖ ≤ M) (A : Finset Mode) (x : T3) :
    ‖tp A u x‖ ≤ M + tailN u A := by
  have hn : ∀ k, ‖mFourier k x‖ = 1 := fun k => by
    have h1 : ‖mFourier k x‖ ≤ 1 :=
      (ContinuousMap.norm_coe_le_norm _ x).trans_eq mFourier_norm
    have h2 : ‖mFourier k x‖ ^ 2 = 1 := by
      have h3 : mFourier (-k + k) x = conj (mFourier k x) * mFourier k x := by
        rw [mFourier_add, mFourier_neg]
      rw [neg_add_cancel, mFourier_zero, Complex.conj_mul'] at h3
      have h4 : ((‖mFourier k x‖ ^ 2 : ℝ) : ℂ) = 1 := by
        push_cast
        simpa using h3.symm
      exact_mod_cast h4
    nlinarith [norm_nonneg (mFourier k x)]
  have hs1 : Summable fun k => u k * mFourier k x :=
    Summable.of_norm (by simpa [hn] using hu)
  have hs2 : Summable fun k => tr A u k * mFourier k x :=
    summable_of_ne_finset_zero (s := A) fun k hk => by simp [tr, hk]
  have e : tp A u x = ∑' k, tr A u k * mFourier k x := by
    rw [tp_apply, tsum_eq_sum (s := A) fun k hk => by simp [tr, hk]]
    exact Finset.sum_congr rfl fun k hk => by simp [tr, hk]
  have e2 : tp A u x = (∑' k, u k * mFourier k x) - ∑' k, (u k - tr A u k) * mFourier k x := by
    have : ∑' k, (u k - tr A u k) * mFourier k x =
        (∑' k, u k * mFourier k x) - ∑' k, tr A u k * mFourier k x := by
      simp only [sub_mul]
      exact hs1.tsum_sub hs2
    rw [this, e]
    ring
  rw [e2]
  refine (norm_sub_le _ _).trans (add_le_add (hM x) ?_)
  refine tsum_of_norm_bounded (summable_tailN hu A).hasSum fun k => ?_
  rw [norm_mul, hn, mul_one]

lemma summable_mul_of_l2 {a b : Mode → ℂ} (ha : Summable fun k => ‖a k‖ ^ 2)
    (hb : Summable fun k => ‖b k‖ ^ 2) (m : Mode) : Summable fun p => ‖a p‖ * ‖b (m - p)‖ :=
  (convR_le_of_l2 (a := fun k => ‖a k‖) (b := fun k => ‖b k‖) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) ha hb m).1

/-- `∑_{k ∈ A} ≤ ∑'`. -/
lemma sum_le_tsum_sq {c : Mode → ℂ} (hc : Summable fun k => ‖c k‖ ^ 2) (A : Finset Mode) :
    ∑ k ∈ A, ‖c k‖ ^ 2 ≤ ∑' k, ‖c k‖ ^ 2 :=
  hc.sum_le_tsum A fun _ _ => by positivity

/-- **Gagliardo–Nirenberg, Fourier form**: for `u` with `ℓ¹` coefficients, `∂_i u, ∂_i² u ∈ L²`
and `‖u‖_∞ ≤ M`, `‖∂_i u‖₄⁴ = ‖v ∗ v‖²_{ℓ²} ≤ (3M)² ‖∂_i² u‖₂²`, `v = ∂_i u`.  Here `‖v ∗ v‖_{ℓ²}`
is the honest `‖v²‖₂ = ‖v‖₄²` by Parseval (`hasSum_cv`).  It holds on all of `H²`, where `v` need
not have `ℓ¹` coefficients: this is why the polynomials are needed. -/
theorem gn_cv (i : Fin 3) {u : Mode → ℂ} (hu : Summable fun k => ‖u k‖)
    (hv : Summable fun k => ‖dC i u k‖ ^ 2) (hw : Summable fun k => ‖dC i (dC i u) k‖ ^ 2) {M : ℝ}
    (hM : ∀ x, ‖∑' k, u k * mFourier k x‖ ≤ M) :
    Summable (fun m => ‖cv (dC i u) (dC i u) m‖ ^ 2) ∧
      ∑' m, ‖cv (dC i u) (dC i u) m‖ ^ 2 ≤ (3 * M) ^ 2 * ∑' k, ‖dC i (dC i u) k‖ ^ 2 := by
  set W := ∑' k, ‖dC i (dC i u) k‖ ^ 2 with hW
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => by positivity
  have hB : Tendsto (fun A => (3 * (M + tailN u A)) ^ 2 * W) atTop (𝓝 ((3 * M) ^ 2 * W)) := by
    have h := tendsto_tailN hu
    have : Tendsto (fun A => (3 * (M + tailN u A)) ^ 2 * W) atTop (𝓝 ((3 * (M + 0)) ^ 2 * W)) :=
      (((tendsto_const_nhds.add h).const_mul 3).pow 2).mul_const W
    simpa using this
  refine cv_fatou (summable_mul_of_l2 hv hv) (fun A => ?_) hB
  have h1 := gn_tp A u i (norm_tp_le hu hM A)
  rw [integral_norm_sq_tp] at h1
  have e : ∫ x, ‖tp A (dC i u) x‖ ^ 2 * ‖tp A (dC i u) x‖ ^ 2 ∂μT =
      ∫ x, ‖tp A (dC i u) x‖ ^ 4 ∂μT :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [e]
  refine h1.trans ?_
  have h2 := sum_le_tsum_sq hw A
  have h3 : 9 * (M + tailN u A) ^ 2 = (3 * (M + tailN u A)) ^ 2 := by ring
  rw [h3]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `(a b)² ≤ …`: the square root of the Gagliardo–Nirenberg bound. -/
private lemma sqrt_le_of_sq {X b : ℝ} (hb : 0 ≤ b) (h : X ≤ b ^ 2) : Real.sqrt X ≤ b := by
  rw [← Real.sqrt_sq hb]
  exact Real.sqrt_le_sqrt h

/-- **The physical product `‖G ∂_i u‖₂² ≤ ‖G‖₄² ‖∂_i u‖₄²`, with Sobolev for `G` and
Gagliardo–Nirenberg for `u`**: `‖G ∗ ∂_i u‖²_{ℓ²} ≤ 3 M ‖∂_i² u‖₂ · c₄ ‖G‖₁²`. -/
theorem gn_product (i : Fin 3) {u G : Mode → ℂ} (hu : Summable fun k => ‖u k‖)
    (hv : Summable fun k => ‖dC i u k‖ ^ 2) (hw : Summable fun k => ‖dC i (dC i u) k‖ ^ 2)
    (hG0 : G 0 = 0) (hG : Summable fun k => absSq k * ‖G k‖ ^ 2) {M : ℝ}
    (hM : ∀ x, ‖∑' k, u k * mFourier k x‖ ≤ M) :
    Summable (fun m => ‖cv G (dC i u) m‖ ^ 2) ∧
      ∑' m, ‖cv G (dC i u) m‖ ^ 2 ≤
        (c4 * ∑' k, absSq k * ‖G k‖ ^ 2) * (3 * M * Real.sqrt (∑' k, ‖dC i (dC i u) k‖ ^ 2)) := by
  set W := ∑' k, ‖dC i (dC i u) k‖ ^ 2 with hW
  set S := ∑' k, absSq k * ‖G k‖ ^ 2 with hS
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => by positivity
  have hS0 : 0 ≤ S := tsum_nonneg fun k => mul_nonneg (absSq_nonneg k) (by positivity)
  have hc0 : 0 ≤ c4 := c4_pos.le
  have hG2 : Summable fun k => ‖G k‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_) hG
    by_cases hk : k = 0
    · subst hk
      simp [hG0]
    · have := one_le_absSq hk
      nlinarith [sq_nonneg ‖G k‖]
  have hB : Tendsto (fun A => (c4 * S) * (3 * (M + tailN u A) * Real.sqrt W)) atTop
      (𝓝 ((c4 * S) * (3 * M * Real.sqrt W))) := by
    have h := tendsto_tailN hu
    have : Tendsto (fun A => (c4 * S) * (3 * (M + tailN u A) * Real.sqrt W)) atTop
        (𝓝 ((c4 * S) * (3 * (M + 0) * Real.sqrt W))) :=
      (((tendsto_const_nhds.add h).const_mul 3).mul_const _).const_mul _
    simpa using this
  refine cv_fatou (summable_mul_of_l2 hG2 hv) (fun A => ?_) hB
  have hbd := norm_tp_le hu hM A
  have hM0 : 0 ≤ M + tailN u A := (norm_nonneg _).trans (hbd 0)
  have h1 := integral_mul_le_sqrt (f := fun x => ‖tp A G x‖ ^ 2)
    (g := fun x => ‖tp A (dC i u) x‖ ^ 2) ((tp A G).continuous.norm.pow 2)
    ((tp A (dC i u)).continuous.norm.pow 2) (fun _ => by positivity) (fun _ => by positivity)
  have e4 : ∀ c : C(T3, ℂ), ∫ x, (‖c x‖ ^ 2) ^ 2 ∂μT = ∫ x, ‖c x‖ ^ 4 ∂μT := fun c =>
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  simp only [e4] at h1
  refine h1.trans ?_
  have h2 : Real.sqrt (∫ x, ‖tp A G x‖ ^ 4 ∂μT) ≤ c4 * S := by
    refine sqrt_le_of_sq (by positivity) ?_
    rw [mul_pow]
    exact L4_tp_le A hG0 hG
  have h3 : Real.sqrt (∫ x, ‖tp A (dC i u) x‖ ^ 4 ∂μT) ≤ 3 * (M + tailN u A) * Real.sqrt W := by
    refine sqrt_le_of_sq (by positivity) ?_
    have h4 := gn_tp A u i hbd
    rw [integral_norm_sq_tp] at h4
    refine h4.trans ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt hW0]
    have := sum_le_tsum_sq hw A
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 9 * (M + tailN u A) ^ 2)]
  exact mul_le_mul h2 h3 (Real.sqrt_nonneg _) (by positivity)

/-- **The sup norm is the operator norm of multiplication**: `‖s ∗ g‖_{ℓ²} ≤ ‖s‖_∞ ‖g‖_{ℓ²}`. -/
theorem sup_product {s g : Mode → ℂ} (hs : Summable fun k => ‖s k‖)
    (hg : Summable fun k => ‖g k‖ ^ 2) {M : ℝ} (hM : ∀ x, ‖∑' k, s k * mFourier k x‖ ≤ M) :
    Summable (fun m => ‖cv s g m‖ ^ 2) ∧ ∑' m, ‖cv s g m‖ ^ 2 ≤ M ^ 2 * ∑' k, ‖g k‖ ^ 2 := by
  set W := ∑' k, ‖g k‖ ^ 2 with hW
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => by positivity
  have hB : Tendsto (fun A => (M + tailN s A) ^ 2 * W) atTop (𝓝 (M ^ 2 * W)) := by
    have h := tendsto_tailN hs
    have : Tendsto (fun A => (M + tailN s A) ^ 2 * W) atTop (𝓝 ((M + 0) ^ 2 * W)) :=
      ((tendsto_const_nhds.add h).pow 2).mul_const W
    simpa using this
  have hs2 : Summable fun k => ‖s k‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
      (hs.mul_left (∑' k, ‖s k‖))
    have := hs.le_tsum k fun j _ => norm_nonneg _
    nlinarith [norm_nonneg (s k)]
  refine cv_fatou (summable_mul_of_l2 hs2 hg) (fun A => ?_) hB
  have hbd := norm_tp_le hs hM A
  have hM0 : 0 ≤ M + tailN s A := (norm_nonneg _).trans (hbd 0)
  have hc1 : Continuous fun x => ‖tp A s x‖ ^ 2 * ‖tp A g x‖ ^ 2 :=
    ((tp A s).continuous.norm.pow 2).mul ((tp A g).continuous.norm.pow 2)
  have hc2 : Continuous fun x => (M + tailN s A) ^ 2 * ‖tp A g x‖ ^ 2 :=
    continuous_const.mul ((tp A g).continuous.norm.pow 2)
  calc ∫ x, ‖tp A s x‖ ^ 2 * ‖tp A g x‖ ^ 2 ∂μT
      ≤ ∫ x, (M + tailN s A) ^ 2 * ‖tp A g x‖ ^ 2 ∂μT :=
        integral_mono (integrable_of_continuous hc1) (integrable_of_continuous hc2) fun x =>
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hbd x) 2) (by positivity)
    _ = (M + tailN s A) ^ 2 * ∑ k ∈ A, ‖g k‖ ^ 2 := by
        rw [integral_const_mul, integral_norm_sq_tp]
    _ ≤ (M + tailN s A) ^ 2 * W :=
        mul_le_mul_of_nonneg_left (sum_le_tsum_sq hg A) (by positivity)

/-! ### From scalars to fields -/

/-- The component `a` of a field. -/
def cmp (u : Field) (a : Fin 3) : Mode → ℂ := fun k => u k a

/-- The sup bound on `T3`: `M` dominates the (absolutely convergent) physical field `u`. -/
def SupBd (u : Field) (M : ℝ) : Prop := ∀ x : T3, ‖∑' k, mFourier k x • u k‖ ≤ M

lemma norm_mFourier_le (k : Mode) (x : T3) : ‖mFourier k x‖ ≤ 1 :=
  (ContinuousMap.norm_coe_le_norm _ x).trans_eq mFourier_norm

lemma norm_cmp_le (u : Field) (a : Fin 3) (k : Mode) : ‖cmp u a k‖ ≤ ‖u k‖ :=
  PiLp.norm_apply_le (u k) a

/-- The components of a sup bound. -/
lemma SupBd.cmp {u : Field} {M : ℝ} (h : SupBd u M) (hu : Summable fun k => ‖u k‖) (a : Fin 3)
    (x : T3) : ‖∑' k, cmp u a k * mFourier k x‖ ≤ M := by
  have hs : Summable fun k => mFourier k x • u k :=
    Summable.of_norm_bounded hu fun k => by
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_mFourier_le k x)
  have e : ∑' k, GN.cmp u a k * mFourier k x = (∑' k, mFourier k x • u k) a := by
    have := (EuclideanSpace.proj (𝕜 := ℂ) a).map_tsum hs
    refine Eq.trans ?_ this.symm
    refine tsum_congr fun k => ?_
    simp [GN.cmp, mul_comm]
  rw [e]
  exact (PiLp.norm_apply_le _ a).trans (h x)

lemma normSq_dC (i : Fin 3) (c : Mode → ℂ) (k : Mode) :
    ‖dC i c k‖ ^ 2 = (k i : ℝ) ^ 2 * ‖c k‖ ^ 2 := by
  simp only [dC, norm_mul, Complex.norm_I, one_mul, mul_pow, Complex.norm_intCast, sq_abs]

lemma sq_le_absSq (i : Fin 3) (k : Mode) : (k i : ℝ) ^ 2 ≤ absSq k :=
  Finset.single_le_sum (f := fun i => (k i : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

lemma sum_norm_cmp_sq (u : Field) (k : Mode) : ∑ a, ‖cmp u a k‖ ^ 2 = ‖u k‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rfl

/-- The `H¹`-weight of a component. -/
lemma summable_absSq_cmp {u : Field} (hu : InH 1 u) (a : Fin 3) :
    Summable fun k => absSq k * ‖cmp u a k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (absSq_nonneg k) (by positivity))
    (fun k => ?_) hu
  rw [sobWeight_one]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_cmp_le u a k) 2)
    (absSq_nonneg k)

/-- `∑_a ∑_k |k|² |u_k^a|² = ‖u‖₁²`. -/
lemma sum_tsum_absSq_cmp {u : Field} (hu : InH 1 u) :
    ∑ a, ∑' k, absSq k * ‖cmp u a k‖ ^ 2 = hnorm 1 u ^ 2 := by
  have h0 : 0 ≤ ∑' k, sobWeight 1 k * ‖u k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg 1 k) (sq_nonneg _)
  rw [hnorm, Real.sq_sqrt h0, ← Summable.tsum_finsetSum fun a _ => summable_absSq_cmp hu a]
  refine tsum_congr fun k => ?_
  rw [sobWeight_one, ← Finset.mul_sum, sum_norm_cmp_sq]

lemma summable_dC_sq {u : Field} (hu : InH 1 u) (i a : Fin 3) :
    Summable fun k => ‖dC i (cmp u a) k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
    (summable_absSq_cmp hu a)
  rw [normSq_dC]
  exact mul_le_mul_of_nonneg_right (sq_le_absSq i k) (by positivity)

lemma tsum_dC_sq_le {u : Field} (hu : InH 1 u) (i a : Fin 3) :
    ∑' k, ‖dC i (cmp u a) k‖ ^ 2 ≤ ∑' k, absSq k * ‖cmp u a k‖ ^ 2 := by
  refine (summable_dC_sq hu i a).tsum_le_tsum (fun k => ?_) (summable_absSq_cmp hu a)
  rw [normSq_dC]
  exact mul_le_mul_of_nonneg_right (sq_le_absSq i k) (by positivity)

lemma normSq_dC_dC_le (u : Field) (i a : Fin 3) (k : Mode) :
    ‖dC i (dC i (cmp u a)) k‖ ^ 2 ≤ sobWeight 2 k * ‖u k‖ ^ 2 := by
  rw [normSq_dC, normSq_dC, sobWeight_two]
  have h1 := sq_le_absSq i k
  have h2 : ‖cmp u a k‖ ^ 2 ≤ ‖u k‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_cmp_le u a k) 2
  have h3 : (k i : ℝ) ^ 2 * (k i : ℝ) ^ 2 ≤ absSq k ^ 2 := by
    nlinarith [sq_nonneg (k i : ℝ), absSq_nonneg k]
  calc (k i : ℝ) ^ 2 * ((k i : ℝ) ^ 2 * ‖cmp u a k‖ ^ 2)
      = (k i : ℝ) ^ 2 * (k i : ℝ) ^ 2 * ‖cmp u a k‖ ^ 2 := by ring
    _ ≤ absSq k ^ 2 * ‖u k‖ ^ 2 := mul_le_mul h3 h2 (by positivity) (by positivity)

lemma summable_dC_dC_sq {u : Field} (hu : InH 2 u) (i a : Fin 3) :
    Summable fun k => ‖dC i (dC i (cmp u a)) k‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => by positivity) (normSq_dC_dC_le u i a) hu

lemma tsum_dC_dC_sq_le {u : Field} (hu : InH 2 u) (i a : Fin 3) :
    ∑' k, ‖dC i (dC i (cmp u a)) k‖ ^ 2 ≤ hnorm 2 u ^ 2 := by
  have h0 : 0 ≤ ∑' k, sobWeight 2 k * ‖u k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg 2 k) (sq_nonneg _)
  rw [hnorm, Real.sq_sqrt h0]
  exact (summable_dC_dC_sq hu i a).tsum_le_tsum (normSq_dC_dC_le u i a) hu

lemma summable_cmp {u : Field} (hu : Summable fun k => ‖u k‖) (a : Fin 3) :
    Summable fun k => ‖cmp u a k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_cmp_le u a) hu

/-- **Gagliardo–Nirenberg** (Body 30, `‖DU‖₄² ≲ M b`), on fields: for `u ∈ H²` with sup bound `M`,
each entry of `Du` obeys `‖∂_i u_a‖₄² ≤ 3 M ‖u‖₂`, where `‖v‖₄⁴ = ‖v ∗ v‖²_{ℓ²}` by Parseval. -/
theorem gn_field {u : Field} (hu : InH 2 u) {M : ℝ} (hM : SupBd u M) (i a : Fin 3) :
    Summable (fun m => ‖cv (dC i (cmp u a)) (dC i (cmp u a)) m‖ ^ 2) ∧
      ∑' m, ‖cv (dC i (cmp u a)) (dC i (cmp u a)) m‖ ^ 2 ≤ (3 * M * hnorm 2 u) ^ 2 := by
  have hu1 := summable_wiener hu
  have hu' : InH 1 u := hu.mono (by norm_num)
  obtain ⟨h1, h2⟩ := gn_cv i (summable_cmp hu1 a) (summable_dC_sq hu' i a)
    (summable_dC_dC_sq hu i a) (hM.cmp hu1 a)
  refine ⟨h1, h2.trans ?_⟩
  rw [mul_pow (3 * M)]
  exact mul_le_mul_of_nonneg_left (tsum_dC_dC_sq_le hu i a) (by positivity)

/-- The Fourier form of `‖v‖₄²`: `‖v²‖₂ = ‖v ∗ v‖_{ℓ²}`.  On polynomials it is the physical norm
(`L4sq_tr_sq`), and it makes sense for all of `H¹`, where `v` has no Lean function on the torus. -/
def L4sq (v : Mode → ℂ) : ℝ := Real.sqrt (∑' m, ‖cv v v m‖ ^ 2)

/-- `L4sq` is the physical `L⁴` norm squared, on polynomials (Parseval). -/
theorem L4sq_tr_sq (A : Finset Mode) (c : Mode → ℂ) :
    L4sq (tr A c) ^ 2 = ∫ x, ‖tp A c x‖ ^ 4 ∂μT := by
  have h := hasSum_cv A A c c
  have e : ∫ x, ‖tp A c x‖ ^ 2 * ‖tp A c x‖ ^ 2 ∂μT = ∫ x, ‖tp A c x‖ ^ 4 ∂μT :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [e] at h
  rw [L4sq, Real.sq_sqrt (tsum_nonneg fun _ => by positivity), h.tsum_eq]

/-- **`‖DU‖₄² ≲ M b`** (Body 30): the whole tensor, `∑_{i,a} ‖∂_i U_a‖₄² ≤ 27 M ‖U‖₂`. -/
theorem gn_tensor {u : Field} (hu : InH 2 u) {M : ℝ} (hM : SupBd u M) :
    ∑ i, ∑ a, L4sq (dC i (cmp u a)) ≤ 27 * M * hnorm 2 u := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h2 := hnorm_nonneg 2 u
  have h1 : ∀ i a, L4sq (dC i (cmp u a)) ≤ 3 * M * hnorm 2 u := fun i a => by
    rw [L4sq, ← Real.sqrt_sq (by positivity : 0 ≤ 3 * M * hnorm 2 u)]
    exact Real.sqrt_le_sqrt (gn_field hu hM i a).2
  calc ∑ i, ∑ a, L4sq (dC i (cmp u a)) ≤ ∑ _i : Fin 3, ∑ _a : Fin 3, 3 * M * hnorm 2 u :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => h1 i a
    _ = 27 * M * hnorm 2 u := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ### The advection terms: from `cv` to `advect`, `Bsym` and `Qphase` -/

lemma norm_dC_le (i : Fin 3) (c : Mode → ℂ) (q : Mode) : ‖dC i c q‖ ≤ absk q * ‖c q‖ := by
  simp only [dC, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
  exact mul_le_mul_of_nonneg_right (Real.abs_le_sqrt (sq_le_absSq i q)) (norm_nonneg _)

/-- The summability that makes `(f·∇)g` absolutely convergent. -/
lemma summable_adv {f g : Field} (hf : Summable fun k => ‖f k‖ ^ 2) (hg : InH 1 g) (k : Mode) :
    Summable fun p => ‖f p‖ * (absk (k - p) * ‖g (k - p)‖) := by
  have h2 : Summable fun q => (absk q * ‖g q‖) ^ 2 := by
    refine hg.congr fun q => ?_
    rw [sobWeight_one, mul_pow, absk_sq]
  exact (convR_le_of_l2 (a := fun k => ‖f k‖) (b := fun q => absk q * ‖g q‖)
    (fun _ => norm_nonneg _) (fun q => mul_nonneg (absk_nonneg q) (norm_nonneg _)) hf h2 k).1

lemma summable_adv_term {f g : Field} {k : Mode}
    (hs : Summable fun p => ‖f p‖ * (absk (k - p) * ‖g (k - p)‖)) :
    Summable fun p => (Complex.I * dotM (f p) (k - p)) • g (k - p) := by
  refine Summable.of_norm_bounded hs fun p => ?_
  rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
  calc ‖dotM (f p) (k - p)‖ * ‖g (k - p)‖
      ≤ (‖f p‖ * absk (k - p)) * ‖g (k - p)‖ :=
        mul_le_mul_of_nonneg_right (norm_dotM_le _ _) (norm_nonneg _)
    _ = ‖f p‖ * (absk (k - p) * ‖g (k - p)‖) := by ring

/-- `(f·∇)g` by components: `advect f g k a = ∑_i (f_i ∗ ∂_i g_a)_k`. -/
lemma advect_apply {f g : Field} {k : Mode}
    (hs : Summable fun p => ‖f p‖ * (absk (k - p) * ‖g (k - p)‖)) (a : Fin 3) :
    advect f g k a = ∑ i, cv (cmp f i) (dC i (cmp g a)) k := by
  have e := (EuclideanSpace.proj (𝕜 := ℂ) a).map_tsum (summable_adv_term hs)
  have hterm : ∀ p,
      (EuclideanSpace.proj (𝕜 := ℂ) a) ((Complex.I * dotM (f p) (k - p)) • g (k - p)) =
        ∑ i, cmp f i p * dC i (cmp g a) (k - p) := fun p => by
    simp only [map_smul, dotM, Finset.mul_sum, Finset.sum_mul, smul_eq_mul, cmp, dC]
    refine Finset.sum_congr rfl fun i _ => ?_
    change Complex.I * (f p i * ((k - p) i : ℂ)) * g (k - p) a =
      f p i * (Complex.I * ((k - p) i : ℂ) * g (k - p) a)
    ring
  simp only [hterm] at e
  have hsum : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun p => cmp f i p * dC i (cmp g a) (k - p) := fun i _ => by
    refine Summable.of_norm_bounded hs fun p => ?_
    rw [norm_mul]
    exact mul_le_mul (norm_cmp_le f i p) ((norm_dC_le i _ _).trans
      (mul_le_mul_of_nonneg_left (norm_cmp_le g a _) (absk_nonneg _))) (norm_nonneg _)
      (norm_nonneg _)
  rw [Summable.tsum_finsetSum hsum] at e
  exact e

/-- `‖(f·∇)g‖²` from the scalar convolutions. -/
lemma advect_sum {f g : Field}
    (hs : ∀ k, Summable fun p => ‖f p‖ * (absk (k - p) * ‖g (k - p)‖)) {B : Fin 3 → Fin 3 → ℝ}
    (h : ∀ a i, Summable (fun k => ‖cv (cmp f i) (dC i (cmp g a)) k‖ ^ 2) ∧
      ∑' k, ‖cv (cmp f i) (dC i (cmp g a)) k‖ ^ 2 ≤ B a i) :
    Summable (fun k => ‖advect f g k‖ ^ 2) ∧
      ∑' k, ‖advect f g k‖ ^ 2 ≤ 3 * ∑ a, ∑ i, B a i := by
  have hpt : ∀ k, ‖advect f g k‖ ^ 2 ≤
      3 * ∑ a, ∑ i, ‖cv (cmp f i) (dC i (cmp g a)) k‖ ^ 2 := fun k => by
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [advect_apply (hs k) a]
    calc ‖∑ i, cv (cmp f i) (dC i (cmp g a)) k‖ ^ 2
        ≤ (∑ i, ‖cv (cmp f i) (dC i (cmp g a)) k‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
          have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
            (f := fun i => ‖cv (cmp f i) (dC i (cmp g a)) k‖)
          simpa using this
  have hsum : Summable fun k => 3 * ∑ a, ∑ i, ‖cv (cmp f i) (dC i (cmp g a)) k‖ ^ 2 :=
    (summable_sum fun a _ => summable_sum fun i _ => (h a i).1).mul_left 3
  have hS := Summable.of_nonneg_of_le (fun _ => by positivity) hpt hsum
  refine ⟨hS, (hS.tsum_le_tsum hpt hsum).trans ?_⟩
  rw [tsum_mul_left, Summable.tsum_finsetSum fun a _ => summable_sum fun i _ => (h a i).1]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
  rw [Summable.tsum_finsetSum fun i _ => (h a i).1]
  exact Finset.sum_le_sum fun i _ => (h a i).2

/-- **`‖(G·∇)u‖₀² ≤ 27 c₄ M ‖u‖₂ ‖G‖₁²`** (Body 56: `‖F·∇S‖₂ ≲ a_F D₄`, `D₄² = M b`): the term
which the Fourier bound prices at `√(a_S b_S)`. -/
theorem advect_gn {u G : Field} (hu : InH 2 u) (hG : InH 1 G) (hG0 : G 0 = 0) {M : ℝ}
    (hM : SupBd u M) :
    Summable (fun k => ‖advect G u k‖ ^ 2) ∧
      ∑' k, ‖advect G u k‖ ^ 2 ≤ 27 * c4 * M * hnorm 2 u * hnorm 1 G ^ 2 := by
  have hu1 := summable_wiener hu
  have hu' : InH 1 u := hu.mono (by norm_num)
  have hG2 : Summable fun k => ‖G k‖ ^ 2 :=
    summable_norm_sq_of_inH (hG.mono (by norm_num))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hc := c4_pos.le
  have h2 := hnorm_nonneg 2 u
  have hz : ∀ i, cmp G i 0 = 0 := fun i => by simp [cmp, hG0]
  obtain ⟨h1, hle⟩ := advect_sum (B := fun _ i => (c4 * ∑' k, absSq k * ‖cmp G i k‖ ^ 2) *
      (3 * M * hnorm 2 u)) (summable_adv hG2 hu') fun a i => by
    obtain ⟨h1, h2'⟩ := gn_product i (summable_cmp hu1 a) (summable_dC_sq hu' i a)
      (summable_dC_dC_sq hu i a) (hz i) (summable_absSq_cmp hG i) (hM.cmp hu1 a)
    refine ⟨h1, h2'.trans ?_⟩
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
      (mul_nonneg hc (tsum_nonneg fun k => mul_nonneg (absSq_nonneg k) (by positivity)))
    exact (Real.sqrt_le_sqrt (tsum_dC_dC_sq_le hu i a)).trans (by rw [Real.sqrt_sq h2])
  refine ⟨h1, hle.trans (le_of_eq ?_)⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul,
    ← Finset.mul_sum, sum_tsum_absSq_cmp hG]
  push_cast
  ring

/-- **`‖(u·∇)G‖₀² ≤ 9 M² ‖G‖₁²`** (Body 56: `‖S·∇F‖₂ ≤ M_∞ a_F`). -/
theorem advect_sup {u G : Field} (hu : InH 2 u) (hG : InH 1 G) {M : ℝ} (hM : SupBd u M) :
    Summable (fun k => ‖advect u G k‖ ^ 2) ∧
      ∑' k, ‖advect u G k‖ ^ 2 ≤ 9 * M ^ 2 * hnorm 1 G ^ 2 := by
  have hu1 := summable_wiener hu
  have hu2 : Summable fun k => ‖u k‖ ^ 2 := summable_sq_of_summable hu1
  obtain ⟨h1, hle⟩ := advect_sum (B := fun a _ => M ^ 2 * ∑' k, absSq k * ‖cmp G a k‖ ^ 2)
      (summable_adv hu2 hG) fun a i => by
    obtain ⟨h1, h2⟩ := sup_product (summable_cmp hu1 i) (summable_dC_sq hG i a) (hM.cmp hu1 i)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (tsum_dC_sq_le hG i a) (by positivity))⟩
  refine ⟨h1, hle.trans (le_of_eq ?_)⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
    sum_tsum_absSq_cmp hG]
  push_cast
  ring

/-- The Leray symbol as a continuous linear map. -/
private def lerayCL (k : Mode) : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := leray k, map_add' := leray_add k, map_smul' := leray_smul k }

/-- `B(f,g) = ½ ℙ[(f·∇)g + (g·∇)f]`, in norm. -/
lemma norm_Bsym_le {f g : Field} {k : Mode}
    (hfg : Summable fun p => ‖f p‖ * (absk (k - p) * ‖g (k - p)‖))
    (hgf : Summable fun p => ‖g p‖ * (absk (k - p) * ‖f (k - p)‖)) :
    ‖Bsym f g k‖ ≤ 1 / 2 * (‖advect f g k‖ + ‖advect g f k‖) := by
  have hA : HasSum (fun p => (Complex.I * dotM (f p) (k - p)) • g (k - p)) (advect f g k) :=
    (summable_adv_term hfg).hasSum
  have hB : HasSum (fun p => (Complex.I * dotM (g (k - p)) p) • f p) (advect g f k) := by
    have e : (fun p => (Complex.I * dotM (g (k - p)) p) • f p) =
        (fun p => (Complex.I * dotM (g p) (k - p)) • f (k - p)) ∘ Equiv.subLeft k := by
      funext p
      simp only [Function.comp, Equiv.subLeft_apply, sub_sub_cancel]
    rw [e]
    exact (Equiv.subLeft k).hasSum_iff.mpr (summable_adv_term hgf).hasSum
  have hs := ((lerayCL k).hasSum (hA.add hB)).const_smul (1 / 2 : ℂ)
  have e : Bsym f g k = ∑' p, (1 / 2 : ℂ) • lerayCL k
      ((Complex.I * dotM (f p) (k - p)) • g (k - p) + (Complex.I * dotM (g (k - p)) p) • f p) := by
    refine tsum_congr fun p => ?_
    simp only [vert, add_sub_cancel]
    rfl
  rw [e, hs.tsum_eq]
  change ‖(1 / 2 : ℂ) • leray k (advect f g k + advect g f k)‖ ≤ _
  rw [norm_smul]
  have h1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h1]
  exact mul_le_mul_of_nonneg_left ((norm_leray_le k _).trans (norm_add_le _ _)) (by norm_num)

/-- A slow solenoidal field is fixed by the filter. -/
lemma rotF_slow {S : Field} (hS : Adm 2 S) (hS' : PiS S = S) (τ : ℝ) : rotF τ S = S := by
  funext k
  change rot τ k (S k) = S k
  by_cases hk : k 2 = 0
  · rw [rot_slow τ hk]
    by_cases h0 : k = 0
    · subst h0
      simp [leray, hS.mean]
    · exact leray_of_perp h0 (hS.sol k)
  · rw [slow_zero hS' hk]
    have h := rot_sub τ k (0 : V3) 0
    rw [sub_self, sub_self] at h
    exact h

/-- The filter preserves the `H¹` norm of a solenoidal field (cf. `term_rotF`, `Physical.lean`). -/
private lemma hnorm_rotF (σ τ : ℝ) {u : Field} (hu : IsSolenoidal u) :
    hnorm σ (rotF τ u) = hnorm σ u := by
  have e : ∀ k, sobWeight σ k * ‖rotF τ u k‖ ^ 2 = sobWeight σ k * ‖u k‖ ^ 2 := fun k => by
    by_cases hk : k = 0
    · subst hk
      simp [sobWeight]
    · rw [show rotF τ u k = rot τ k (u k) from rfl, norm_rot, leray_of_perp hk (hu k)]
  simp only [hnorm, e]

/-- `‖Qphase τ f g‖₀²` is at most the `ℓ²` norm of the unphased `Bsym`, by the filter. -/
private lemma hnorm_Qphase_sq_le (τ : ℝ) {f g : Field} (hf : Adm 2 f) (hg : Adm 2 g) {B : ℝ}
    (hB : Summable (fun k => ‖Bsym (rotF τ f) (rotF τ g) k‖ ^ 2) ∧
      ∑' k, ‖Bsym (rotF τ f) (rotF τ g) k‖ ^ 2 ≤ B) :
    hnorm 0 (Qphase τ f g) ^ 2 ≤ B := by
  have hQ := (hnorm_Qm_zero_le (phaseM_bdd τ) hf.mz hg.mz).1
  have h0 : 0 ≤ ∑' k, sobWeight 0 k * ‖Qphase τ f g k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg 0 k) (sq_nonneg _)
  rw [hnorm, Real.sq_sqrt h0]
  refine (Summable.tsum_le_tsum (f := fun k => sobWeight 0 k * ‖Qphase τ f g k‖ ^ 2)
    (fun k => ?_) hQ hB.1).trans hB.2
  have h1 : sobWeight 0 k ≤ 1 := by
    unfold sobWeight
    split_ifs <;> simp
  rw [Qphase_eq τ hf hg]
  change sobWeight 0 k * ‖rot (-τ) k (Bsym (rotF τ f) (rotF τ g) k)‖ ^ 2 ≤ _
  rw [norm_rot]
  have h2 := norm_leray_le k (Bsym (rotF τ f) (rotF τ g) k)
  calc sobWeight 0 k * ‖leray k (Bsym (rotF τ f) (rotF τ g) k)‖ ^ 2
      ≤ 1 * ‖Bsym (rotF τ f) (rotF τ g) k‖ ^ 2 :=
        mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by positivity) zero_le_one
    _ = _ := one_mul _

/-- **The mixed product** (Body 56, `‖Q(S,F)‖₀ ≲ (M_∞ + D₄) a_F`): undo the filter, restore it
after the physical product.  No fast/slow restriction on `F`, and no phase survives. -/
theorem hnorm_Qphase_mixed (τ : ℝ) {S F : Field} (hS : Adm 2 S) (hS' : PiS S = S) (hF : Adm 2 F)
    {M : ℝ} (hM : SupBd S M) :
    hnorm 0 (Qphase τ S F) ^ 2 ≤
      (9 / 2 * M ^ 2 + 27 / 2 * c4 * M * hnorm 2 S) * hnorm 1 F ^ 2 := by
  have hG : Adm 2 (rotF τ F) := hF.rotF τ
  have hG1 : InH 1 (rotF τ F) := hG.inH.mono (by norm_num)
  have hS1 : InH 1 S := hS.inH.mono (by norm_num)
  have hS2 : Summable fun k => ‖S k‖ ^ 2 := summable_sq_of_summable (summable_wiener hS.inH)
  have hG2 : Summable fun k => ‖rotF τ F k‖ ^ 2 :=
    summable_sq_of_summable (summable_wiener hG.inH)
  obtain ⟨h1, h1'⟩ := advect_sup hS.inH hG1 hM
  obtain ⟨h2, h2'⟩ := advect_gn hS.inH hG1 hG.mean hM
  rw [hnorm_rotF 1 τ hF.sol] at h1' h2'
  have hpt : ∀ k, ‖Bsym S (rotF τ F) k‖ ^ 2 ≤
      1 / 2 * (‖advect S (rotF τ F) k‖ ^ 2 + ‖advect (rotF τ F) S k‖ ^ 2) := fun k => by
    have h := norm_Bsym_le (summable_adv hS2 hG1 k) (summable_adv hG2 hS1 k)
    set x := ‖advect S (rotF τ F) k‖
    set y := ‖advect (rotF τ F) S k‖
    have h0 := norm_nonneg (Bsym S (rotF τ F) k)
    nlinarith [sq_nonneg (x - y), norm_nonneg (advect S (rotF τ F) k),
      norm_nonneg (advect (rotF τ F) S k)]
  have hs : Summable fun k =>
      1 / 2 * (‖advect S (rotF τ F) k‖ ^ 2 + ‖advect (rotF τ F) S k‖ ^ 2) :=
    (h1.add h2).mul_left _
  have hS3 := Summable.of_nonneg_of_le (fun _ => by positivity) hpt hs
  have := hnorm_Qphase_sq_le τ hS hF (B := (9 / 2 * M ^ 2 + 27 / 2 * c4 * M * hnorm 2 S) *
    hnorm 1 F ^ 2) (by
    rw [rotF_slow hS hS' τ]
    refine ⟨hS3, (hS3.tsum_le_tsum hpt hs).trans ?_⟩
    rw [tsum_mul_left, h1.tsum_add h2]
    nlinarith only [h1', h2'])
  exact this

/-- **The slow product** (Body 36, `‖Q(S,S)‖₀ ≲ M_∞ a_S`). -/
theorem hnorm_Qphase_slow (τ : ℝ) {S : Field} (hS : Adm 2 S) (hS' : PiS S = S) {M : ℝ}
    (hM : SupBd S M) : hnorm 0 (Qphase τ S S) ≤ 3 * M * hnorm 1 S := by
  have hS1 : InH 1 S := hS.inH.mono (by norm_num)
  have hS2 : Summable fun k => ‖S k‖ ^ 2 := summable_sq_of_summable (summable_wiener hS.inH)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨h1, h1'⟩ := advect_sup hS.inH hS1 hM
  have hpt : ∀ k, ‖Bsym S S k‖ ^ 2 ≤ ‖advect S S k‖ ^ 2 := fun k => by
    have h := norm_Bsym_le (summable_adv hS2 hS1 k) (summable_adv hS2 hS1 k)
    refine pow_le_pow_left₀ (norm_nonneg _) (h.trans (le_of_eq ?_)) 2
    ring
  have hS3 := Summable.of_nonneg_of_le (fun _ => by positivity) hpt h1
  have h3 := hnorm_Qphase_sq_le τ hS hS (B := 9 * M ^ 2 * hnorm 1 S ^ 2) (by
    rw [rotF_slow hS hS' τ]
    exact ⟨hS3, (hS3.tsum_le_tsum hpt h1).trans h1'⟩)
  have h4 : hnorm 0 (Qphase τ S S) ^ 2 ≤ (3 * M * hnorm 1 S) ^ 2 := by
    refine h3.trans (le_of_eq ?_)
    ring
  exact (abs_le_of_sq_le_sq' h4
    (mul_nonneg (mul_nonneg (by norm_num) hM0) (hnorm_nonneg _ _))).2

/-! ### The bridge to `slowSup` -/

/-- The horizontal modes. -/
private def iotaM (k : Fin 2 → ℤ) : Mode := ![k 0, k 1, 0]

private lemma iotaM_injective : Function.Injective iotaM := by
  intro a b hab
  funext i
  fin_cases i
  · exact congrFun hab 0
  · exact congrFun hab 1

/-- The horizontal shadow of a point of `T3`. -/
private def proj2 (x : T3) : UnitAddTorus (Fin 2) := ![x 0, x 1]

private lemma mFourier_iotaM (k : Fin 2 → ℤ) (x : T3) :
    mFourier (iotaM k) x = mFourier k (proj2 x) := by
  simp [mFourier, Fin.prod_univ_three, Fin.prod_univ_two, iotaM, proj2]

/-- On a slow field, the sup on `T3` is the sup on the horizontal torus. -/
theorem supBd_of_physS {u : Field} (hu : PiS u = u) {M : ℝ}
    (h : ∀ x : UnitAddTorus (Fin 2), ‖physS u x‖ ≤ M) : SupBd u M := fun x => by
  have hsupp : Function.support (fun k => mFourier k x • u k) ⊆ Set.range iotaM := fun k hk => by
    have h2 : k 2 = 0 := by
      by_contra h2
      apply hk
      simp only [slow_zero hu h2, smul_zero]
    refine ⟨![k 0, k 1], ?_⟩
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact h2.symm
  rw [← iotaM_injective.tsum_eq hsupp]
  have e : ∑' k, mFourier (iotaM k) x • u (iotaM k) = physS u (proj2 x) := by
    refine tsum_congr fun k => ?_
    rw [mFourier_iotaM]
    rfl
  rw [e]
  exact h _

/-- `slowSup` is a sup bound: this is the hypothesis of the physical products. -/
theorem supBd_slowSup {r : ℝ} {g : Field} {y : ℝ → Field} {t M : ℝ}
    (h : InH 2 (PiS (actual r g y t))) (hM : slowSup r g y t ≤ M) :
    SupBd (PiS (actual r g y t)) M := by
  have hS : PiS (PiS (actual r g y t)) = PiS (actual r g y t) := by
    funext k
    by_cases hk : k 2 = 0 <;> simp [PiS, hk]
  exact supBd_of_physS hS fun x => (norm_physS_le_slowSup h x).trans hM

end OVNS.Quant.GN
