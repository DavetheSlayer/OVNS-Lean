import OddViscousNS.Quant.Joint.Metric.JointId

/-!
# The heat flow contracts the sup norm (step J5, node N4)

Body 30: `‖E_u S‖_∞ ≤ ‖S‖_∞`.  The proof here is the Gaussian on the line, with no periodization:
along each coordinate, `e^{−u n²} = ∫_ℝ γ(t) e^{2πi n t} dt`, with `γ` a Gaussian of mass one, so
the heat flow in that coordinate is an average of translates of the field.  This needs neither the
Poisson formula nor positivity of the periodic kernel.

Also here: `‖B(S_u, S_u)‖₁ ≤ 41 M b e^{−u}` (Body 30, Body 40).
-/

open MeasureTheory Set Filter UnitAddTorus
open scoped ENNReal ComplexConjugate Real

noncomputable section

namespace OVNS.Quant.Metric

open GN (SupBd T3)

/-- The heat flow on the Fourier side. -/
def heatF (u : ℝ) (S : Field) : Field := fun k => ((Real.exp (-u * absSq k) : ℝ) : ℂ) • S k

/-- The heat flow in one coordinate. -/
def heatD (i : Fin 3) (u : ℝ) (S : Field) : Field :=
  fun k => ((Real.exp (-u * (k i : ℝ) ^ 2) : ℝ) : ℂ) • S k

/-- The Gaussian of mass one. -/
def gam (a t : ℝ) : ℂ := ((Real.sqrt (a / π) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * (t : ℂ) ^ 2)

/-- The Gaussian with a character. -/
def gamC (a : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  ((Real.sqrt (a / π) : ℝ) : ℂ) *
    Complex.exp (-(a : ℂ) * (t : ℂ) ^ 2 + (2 * π * Complex.I * n) * t + 0)

lemma gamC_integrable {a : ℝ} (ha : 0 < a) (n : ℤ) : Integrable (gamC a n) := by
  have hb : (-(a : ℂ)).re < 0 := by simpa using ha
  exact (integrable_cexp_quadratic' hb _ _).const_mul _

/-- `∫ γ(t) e^{2πi n t} dt = e^{−π²n²/a}`. -/
lemma gamC_integral {a : ℝ} (ha : 0 < a) (n : ℤ) :
    ∫ t, gamC a n t = ((Real.exp (-(π ^ 2 / a) * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
  have hb : (-(a : ℂ)).re < 0 := by simpa using ha
  have hpi : 0 < π / a := div_pos Real.pi_pos ha
  unfold gamC
  rw [integral_const_mul, integral_cexp_quadratic hb]
  have e1 : (π : ℂ) / - -(a : ℂ) = ((π / a : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((π / a : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (π / a) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hpi.le]
    norm_num
  have e3 : Real.sqrt (a / π) * Real.sqrt (π / a) = 1 := by
    rw [← Real.sqrt_mul (div_pos ha Real.pi_pos).le]
    have : a / π * (π / a) = 1 := by
      field_simp
    rw [this, Real.sqrt_one]
  rw [e1, e2, ← mul_assoc, ← Complex.ofReal_mul, e3, Complex.ofReal_one, one_mul]
  rw [Complex.ofReal_exp]
  congr 1
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hI := Complex.I_sq
  push_cast
  linear_combination ((π : ℂ) ^ 2 * (n : ℂ) ^ 2 / (a : ℂ)) * hI

/-- The mass of the Gaussian. -/
lemma gamC_norm (a : ℝ) (n : ℤ) (t : ℝ) :
    ‖gamC a n t‖ = Real.sqrt (a / π) * Real.exp (-a * t ^ 2) := by
  have h0 := Real.sqrt_nonneg (a / π)
  unfold gamC
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, Complex.norm_exp]
  congr 2
  have : (-(a : ℂ) * (t : ℂ) ^ 2 + (2 * π * Complex.I * n) * t + 0) =
      ((-a * t ^ 2 : ℝ) : ℂ) + ((2 * π * n * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
    add_zero]

lemma gam_mass {a : ℝ} (ha : 0 < a) :
    ∫ t, Real.sqrt (a / π) * Real.exp (-a * t ^ 2) = 1 := by
  rw [integral_const_mul, integral_gaussian, ← Real.sqrt_mul (div_pos ha Real.pi_pos).le]
  have : a / π * (π / a) = 1 := by
    field_simp
  rw [this, Real.sqrt_one]

/-- A shift of a torus point along one coordinate. -/
def shiftT (i : Fin 3) (x : T3) (t : ℝ) : T3 := Function.update x i (x i + (t : UnitAddCircle))

lemma mFourier_shift (i : Fin 3) (x : T3) (t : ℝ) (k : Mode) :
    mFourier k (shiftT i x t) = mFourier k x *
      Complex.exp ((2 * π * Complex.I * (k i : ℤ)) * t) := by
  have h1 : ∀ j, fourier (k j) (shiftT i x t j) = fourier (k j) (x j) *
      (if j = i then Complex.exp ((2 * π * Complex.I * (k i : ℤ)) * t) else 1) := fun j => by
    by_cases hj : j = i
    · subst hj
      have e : fourier (k j) ((t : ℝ) : UnitAddCircle) =
          Complex.exp ((2 * π * Complex.I * (k j : ℤ)) * t) := by
        rw [fourier_coe_apply]
        congr 1
        push_cast
        ring
      simp only [shiftT, Function.update_self, ite_true, ← e]
      rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
        Circle.coe_mul]
    · simp [shiftT, hj]
  change ∏ j, fourier (k j) (shiftT i x t j) = (∏ j, fourier (k j) (x j)) * _
  simp only [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i]
  simp

/-- A series of characters, averaged against the Gaussian. -/
lemma gauss_avg {ι : Type*} [Countable ι] {a : ℝ} (ha : 0 < a) {n : ι → ℤ} {w : ι → V3}
    (hw : Summable fun k => ‖w k‖) {M : ℝ}
    (hM : ∀ t : ℝ, ‖∑' k, Complex.exp ((2 * π * Complex.I * (n k : ℤ)) * t) • w k‖ ≤ M) :
    ‖∑' k, ((Real.exp (-(π ^ 2 / a) * (n k : ℝ) ^ 2) : ℝ) : ℂ) • w k‖ ≤ M := by
  have hint : ∀ k, Integrable fun t => gamC a (n k) t • w k := fun k =>
    (gamC_integrable ha (n k)).smul_const _
  have hnorm : ∀ k, ∫ t, ‖gamC a (n k) t • w k‖ = ‖w k‖ := fun k => by
    simp only [norm_smul, gamC_norm]
    rw [integral_mul_const, gam_mass ha, one_mul]
  have hsum : Summable fun k => ∫ t, ‖gamC a (n k) t • w k‖ := by
    simp only [hnorm]
    exact hw
  have hS := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ k, ∫ t, gamC a (n k) t • w k =
      ((Real.exp (-(π ^ 2 / a) * (n k : ℝ) ^ 2) : ℝ) : ℂ) • w k := fun k => by
    rw [integral_smul_const, gamC_integral ha]
  simp only [hval] at hS
  rw [hS.tsum_eq]
  have hpt : ∀ t, ∑' k, gamC a (n k) t • w k =
      gam a t • ∑' k, Complex.exp ((2 * π * Complex.I * (n k : ℤ)) * t) • w k := fun t => by
    rw [← tsum_const_smul'']
    refine tsum_congr fun k => ?_
    simp only [smul_smul, gamC, gam]
    congr 1
    rw [add_zero, Complex.exp_add]
    ring
  have hbi : Integrable fun t : ℝ => M * (Real.sqrt (a / π) * Real.exp (-a * t ^ 2)) :=
    ((integrable_exp_neg_mul_sq ha).const_mul _).const_mul _
  have hle : ∀ t, ‖∑' k, gamC a (n k) t • w k‖ ≤
      M * (Real.sqrt (a / π) * Real.exp (-a * t ^ 2)) := fun t => by
    rw [hpt, norm_smul, mul_comm]
    have hg : ‖gam a t‖ = Real.sqrt (a / π) * Real.exp (-a * t ^ 2) := by
      have h0 := Real.sqrt_nonneg (a / π)
      unfold gam
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, Complex.norm_exp]
      congr 2
      have : -(a : ℂ) * (t : ℂ) ^ 2 = ((-a * t ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [this, Complex.ofReal_re]
    rw [hg]
    exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
  refine (norm_integral_le_of_norm_le hbi (Filter.Eventually.of_forall hle)).trans ?_
  rw [integral_const_mul, gam_mass ha, mul_one]

/-- **One coordinate.** -/
theorem supBd_heatD {S : Field} (hs : Summable fun k => ‖S k‖) {M : ℝ} (hM : SupBd S M)
    (i : Fin 3) {u : ℝ} (hu : 0 < u) : SupBd (heatD i u S) M := by
  intro x
  have ha0 : 0 < π ^ 2 / u := by positivity
  have hnw : ∀ k, ‖mFourier k x • S k‖ ≤ ‖S k‖ := fun k => by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (GN.norm_mFourier_le k x)
  have hw : Summable fun k => ‖mFourier k x • S k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnw hs
  have h := gauss_avg (n := fun k : Mode => k i) ha0 hw fun t => by
    have e : ∀ k : Mode, Complex.exp ((2 * π * Complex.I * (k i : ℤ)) * t) • mFourier k x • S k =
        mFourier k (shiftT i x t) • S k := fun k => by
      rw [mFourier_shift, smul_smul, mul_comm]
    simp only [e]
    exact hM _
  have e2 : π ^ 2 / (π ^ 2 / u) = u := by
    field_simp
  rw [e2] at h
  simpa only [heatD, smul_comm (mFourier _ x)] using h

/-- The components of a heat flow are smaller. -/
lemma norm_heatD_le (i : Fin 3) {u : ℝ} (hu : 0 ≤ u) (S : Field) (k : Mode) :
    ‖heatD i u S k‖ ≤ ‖S k‖ := by
  simp only [heatD, norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
  have : 0 ≤ u * (k i : ℝ) ^ 2 := by positivity
  linarith

lemma heatF_eq (u : ℝ) (S : Field) :
    heatF u S = heatD 0 u (heatD 1 u (heatD 2 u S)) := by
  funext k
  simp only [heatF, heatD, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  simp only [absSq, Fin.sum_univ_three]
  ring

/-- **The heat flow contracts the sup norm** (Body 30). -/
theorem supBd_heatF {S : Field} (hs : Summable fun k => ‖S k‖) {M : ℝ} (hM : SupBd S M) {u : ℝ}
    (hu : 0 ≤ u) : SupBd (heatF u S) M := by
  rcases hu.eq_or_lt with rfl | hu
  · have : heatF 0 S = S := by
      funext k
      simp [heatF]
    rwa [this]
  rw [heatF_eq]
  have s2 : Summable fun k => ‖heatD 2 u S k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_heatD_le 2 hu.le S) hs
  have s1 : Summable fun k => ‖heatD 1 u (heatD 2 u S) k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_heatD_le 1 hu.le _) s2
  exact supBd_heatD s1 (supBd_heatD s2 (supBd_heatD hs hM 2 hu) 1 hu) 0 hu

/-! ### Elementary facts on the heat flow -/

variable {u : ℝ} {S G : Field}

lemma heat_c (u : ℝ) (k : Mode) : 0 ≤ Real.exp (-u * absSq k) := (Real.exp_pos _).le

lemma norm_heatF (u : ℝ) (S : Field) (k : Mode) :
    ‖heatF u S k‖ = Real.exp (-u * absSq k) * ‖S k‖ := by
  rw [heatF, norm_smul, Complex.norm_real, Real.norm_of_nonneg (heat_c u k)]

lemma heatF_zero_mode (hS : S 0 = 0) : heatF u S 0 = 0 := by simp [heatF, hS]

lemma PiS_heatF (hS : PiS S = S) : PiS (heatF u S) = heatF u S := by
  funext k
  by_cases hk : k 2 = 0
  · simp [PiS, hk]
  · have h : S k = 0 := slow_zero hS hk
    simp [PiS, hk, heatF, h]

lemma PiF_heatF (hS : PiF S = S) : PiF (heatF u S) = heatF u S := by
  funext k
  by_cases hk : k 2 = 0
  · have h : S k = 0 := fast_zero hS hk
    simp [PiF, hk, heatF, h]
  · simp [PiF, hk]

lemma leray_heatF {k : Mode} (h : leray k (S k) = S k) : leray k (heatF u S k) = heatF u S k := by
  simp only [heatF]
  rw [leray_smul, h]

/-- The exponential beats one power: `t e^{−ut} ≤ 1/u`. -/
lemma mul_exp_le (hu : 0 < u) (t : ℝ) : t * Real.exp (-u * t) ≤ 1 / u := by
  have h1 : u * t ≤ Real.exp (u * t) := by
    have := Real.add_one_le_exp (u * t)
    linarith
  rw [le_div_iff₀ hu]
  have e : Real.exp (-u * t) = (Real.exp (u * t))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [e, mul_right_comm, ← div_eq_mul_inv, mul_comm t u]
  exact (div_le_one (Real.exp_pos _)).2 h1

/-- On the modes `k ≠ 0`: `e^{−ut} ≤ e^{−u}`. -/
lemma exp_le_gap (hu : 0 ≤ u) {k : Mode} (hk : k ≠ 0) :
    Real.exp (-u * absSq k) ≤ Real.exp (-u) := by
  refine Real.exp_le_exp.2 ?_
  have := one_le_absSq hk
  nlinarith only [this, hu]

/-- `‖A^{1/2} E_u‖²`, with the gap. -/
lemma sq_mul_exp_le (hu : 0 < u) {k : Mode} (hk : k ≠ 0) :
    absSq k * Real.exp (-u * absSq k) ^ 2 ≤ Real.exp (-u) / u := by
  have h1 := mul_exp_le hu (absSq k)
  have h2 := exp_le_gap hu.le hk
  have h3 := heat_c u k
  calc absSq k * Real.exp (-u * absSq k) ^ 2
      = (absSq k * Real.exp (-u * absSq k)) * Real.exp (-u * absSq k) := by ring
    _ ≤ 1 / u * Real.exp (-u) := mul_le_mul h1 h2 h3 (by positivity)
    _ = _ := by ring

/-- `‖A E_u‖²`, with half the gap. -/
lemma sq4_mul_exp_le (hu : 0 < u) {k : Mode} (hk : k ≠ 0) :
    absSq k ^ 2 * Real.exp (-u * absSq k) ^ 2 ≤ Real.exp (-u) * (2 / u) ^ 2 := by
  have h1 := mul_exp_le (u := u / 2) (by positivity) (absSq k)
  have h2 : Real.exp (-u * absSq k) = Real.exp (-(u / 2) * absSq k) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h3 := exp_le_gap (u := u) hu.le hk
  have h4 : absSq k * Real.exp (-(u / 2) * absSq k) ≤ 2 / u := by
    have e : 1 / (u / 2) = 2 / u := by field_simp
    rwa [e] at h1
  have h5 : 0 ≤ absSq k * Real.exp (-(u / 2) * absSq k) :=
    mul_nonneg (absSq_nonneg k) (Real.exp_pos _).le
  calc absSq k ^ 2 * Real.exp (-u * absSq k) ^ 2
      = (absSq k * Real.exp (-(u / 2) * absSq k)) ^ 2 * Real.exp (-u * absSq k) := by
        rw [h2]
        ring
    _ ≤ (2 / u) ^ 2 * Real.exp (-u) :=
        mul_le_mul (pow_le_pow_left₀ h5 h4 2) h3 (heat_c u k) (by positivity)
    _ = _ := by ring

/-- `l2n` and a term comparison. -/
lemma l2n_le_of_sq {a b : Field} {c : ℝ} (hb : Summable fun k => ‖b k‖ ^ 2) (hc : 0 ≤ c)
    (h : ∀ k, ‖a k‖ ^ 2 ≤ c ^ 2 * ‖b k‖ ^ 2) :
    (Summable fun k => ‖a k‖ ^ 2) ∧ l2n a ≤ c * l2n b := by
  have hs : Summable fun k => ‖a k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => by positivity) h (hb.mul_left _)
  refine ⟨hs, ?_⟩
  have h1 : ∑' k, ‖a k‖ ^ 2 ≤ c ^ 2 * ∑' k, ‖b k‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact hs.tsum_le_tsum h (hb.mul_left _)
  unfold l2n
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c)]
  exact Real.sqrt_le_sqrt h1

/-- `hnorm` and a term comparison. -/
lemma hnorm_le_of_sq {a b : Field} {c s s' : ℝ} (hb : InH s' b) (hc : 0 ≤ c)
    (h : ∀ k, sobWeight s k * ‖a k‖ ^ 2 ≤ c ^ 2 * (sobWeight s' k * ‖b k‖ ^ 2)) :
    InH s a ∧ hnorm s a ≤ c * hnorm s' b := by
  have hb' : Summable fun k => sobWeight s' k * ‖b k‖ ^ 2 := hb
  have hs : Summable fun k => sobWeight s k * ‖a k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg _ k) (by positivity)) h
      (hb'.mul_left _)
  refine ⟨hs, ?_⟩
  have h1 : ∑' k, sobWeight s k * ‖a k‖ ^ 2 ≤ c ^ 2 * ∑' k, sobWeight s' k * ‖b k‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact hs.tsum_le_tsum h (hb'.mul_left _)
  unfold hnorm
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c)]
  exact Real.sqrt_le_sqrt h1

/-- `‖E_u G‖₀ ≤ e^{−u} ‖G‖₀`. -/
lemma l2n_heat_le (hu : 0 ≤ u) {G : Field} (hG : Summable fun k => ‖G k‖ ^ 2) (hG0 : G 0 = 0) :
    (Summable fun k => ‖heatF u G k‖ ^ 2) ∧ l2n (heatF u G) ≤ Real.exp (-u) * l2n G := by
  refine l2n_le_of_sq hG (Real.exp_pos _).le fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [hG0, heatF]
  rw [norm_heatF, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (heat_c u k) (exp_le_gap hu hk) 2) (by positivity)

/-- `‖A^{1/2} E_u G‖₀ ≤ e^{−u/2} u^{−1/2} ‖G‖₀`. -/
lemma l2n_half_heat_le (hu : 0 < u) {G : Field} (hG : Summable fun k => ‖G k‖ ^ 2)
    (hG0 : G 0 = 0) :
    (Summable fun k => ‖zOf 1 (heatF u G) k‖ ^ 2) ∧
      l2n (zOf 1 (heatF u G)) ≤ Real.sqrt (Real.exp (-u) / u) * l2n G := by
  have hc : 0 ≤ Real.exp (-u) / u := by positivity
  refine l2n_le_of_sq hG (Real.sqrt_nonneg _) fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [hG0, heatF, zOf]
  rw [Real.sq_sqrt hc]
  have e : ‖zOf 1 (heatF u G) k‖ ^ 2 = absSq k * Real.exp (-u * absSq k) ^ 2 * ‖G k‖ ^ 2 := by
    simp only [zOf, norm_smul, Complex.norm_real, norm_heatF, pow_one, Real.norm_of_nonneg
      (absk_nonneg k), mul_pow, absk_sq]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (sq_mul_exp_le hu hk) (by positivity)

/-- `‖A E_u G‖₀ ≤ e^{−u/2} (2/u) ‖G‖₀`. -/
lemma l2n_one_heat_le (hu : 0 < u) {G : Field} (hG : Summable fun k => ‖G k‖ ^ 2)
    (hG0 : G 0 = 0) :
    (Summable fun k => ‖zOf 2 (heatF u G) k‖ ^ 2) ∧
      l2n (zOf 2 (heatF u G)) ≤ Real.sqrt (Real.exp (-u)) * (2 / u) * l2n G := by
  have hc : 0 ≤ Real.sqrt (Real.exp (-u)) * (2 / u) := by positivity
  refine l2n_le_of_sq hG hc fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [hG0, heatF, zOf]
  rw [mul_pow, Real.sq_sqrt (Real.exp_pos _).le]
  have e : ‖zOf 2 (heatF u G) k‖ ^ 2 = absSq k ^ 2 * Real.exp (-u * absSq k) ^ 2 * ‖G k‖ ^ 2 := by
    simp only [zOf, norm_smul, Complex.norm_real, norm_heatF, mul_pow, absk_sq,
      Real.norm_eq_abs, sq_abs]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (sq4_mul_exp_le hu hk) (by positivity)

/-- `‖E_u S‖₂ ≤ e^{−u} ‖S‖₂`. -/
lemma hnorm_two_heat_le (hu : 0 ≤ u) (hS : MZ 2 S) :
    InH 2 (heatF u S) ∧ hnorm 2 (heatF u S) ≤ Real.exp (-u) * hnorm 2 S := by
  refine hnorm_le_of_sq hS.inH (Real.exp_pos _).le fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [hS.mean, heatF]
  rw [norm_heatF, mul_pow, mul_left_comm]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (sobWeight_nonneg _ _) (by positivity))
  exact pow_le_pow_left₀ (heat_c u k) (exp_le_gap hu hk) 2

/-- `‖E_u S‖₃ ≤ e^{−u/2} u^{−1/2} ‖S‖₂`. -/
lemma hnorm_three_heat_le (hu : 0 < u) (hS : MZ 2 S) :
    InH 3 (heatF u S) ∧ hnorm 3 (heatF u S) ≤ Real.sqrt (Real.exp (-u) / u) * hnorm 2 S := by
  have hc : 0 ≤ Real.exp (-u) / u := by positivity
  refine hnorm_le_of_sq hS.inH (Real.sqrt_nonneg _) fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [hS.mean, heatF]
  rw [Real.sq_sqrt hc, norm_heatF, OVNS.Quant.H2.sobWeight_three, sobWeight_two]
  have h := mul_le_mul_of_nonneg_right (sq_mul_exp_le hu hk)
    (mul_nonneg (sq_nonneg (absSq k)) (sq_nonneg ‖S k‖))
  refine le_trans (le_of_eq ?_) h
  ring

/-- The Wiener norm decreases. -/
lemma wiener_heat_le (hu : 0 ≤ u) (hS : Summable fun k => ‖S k‖) :
    (Summable fun k => ‖heatF u S k‖) ∧ wiener (heatF u S) ≤ wiener S := by
  have hle : ∀ k, ‖heatF u S k‖ ≤ ‖S k‖ := fun k => by
    rw [norm_heatF]
    refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
    have := absSq_nonneg k
    nlinarith only [this, hu]
  have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hS
  exact ⟨hs, hs.tsum_le_tsum hle hS⟩

private lemma conjV_smul_r (c : ℝ) (a : V3) : conjV ((c : ℂ) • a) = (c : ℂ) • conjV a := by
  ext i
  simp [conjV]

/-- The heat flow keeps a slow admissible field admissible. -/
lemma adm_heat (hu : 0 ≤ u) (hS : Adm 2 S) : Adm 2 (heatF u S) := by
  refine ⟨(hnorm_two_heat_le hu hS.mz).1, fun k => ?_, fun k => ?_, ?_⟩
  · have e : absSq (-k) = absSq k := by simp [absSq]
    simp only [heatF]
    rw [e, hS.real k, conjV_smul_r]
  · simp only [heatF]
    rw [dotM_smul, hS.sol k, mul_zero]
  · simp [heatF, hS.mean]

end OVNS.Quant.Metric

end
