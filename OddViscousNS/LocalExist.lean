import OddViscousNS.LocalBasic

/-! # Local existence: Banach fixed point for the Duhamel map with the heat kernel
(`Lemma fg:lem:lwp(a)`), uniform in the `Majorized` family, hence in `r`.

The phase space is the admissible class with the `H²` metric (`H2`, complete).  The Duhamel integral
is taken mode by mode; the gain `√T` comes from Cauchy-Schwarz in time at each mode, so no singular
kernel and no Hilbert-valued integral is needed.  The time-integrated `H¹` density `cF` dominates
the squared `H²` series uniformly in time, which gives continuity in `H²`. -/

open scoped ENNReal Topology
open MeasureTheory Set Filter
noncomputable section
namespace OVNS

/-! ### Scalar preliminaries -/

/-- The real exponential as a complex scalar. -/
private def ex (x : ℝ) : ℂ := ((Real.exp x : ℝ) : ℂ)

private lemma continuous_ex : Continuous ex := by
  unfold ex; fun_prop

private lemma norm_ex (x : ℝ) : ‖ex x‖ = Real.exp x := by
  simp [ex]

private lemma ex_zero : ex 0 = 1 := by simp [ex]

private lemma sobWeight_two (k : Mode) : sobWeight 2 k = absSq k ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    have : absSq 0 = 0 := by simp [absSq]
    simp [sobWeight, this]
  · have h : absk k ^ (2 * 2 : ℝ) = absk k ^ (4 : ℕ) := by
      rw [show (2 * 2 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [sobWeight, hk, ite_false, h, ← absk_sq]
    ring

private lemma sobWeight_one (k : Mode) : sobWeight 1 k = absSq k := by
  by_cases hk : k = 0
  · subst hk
    have : absSq 0 = 0 := by simp [absSq]
    simp [sobWeight, this]
  · have h : absk k ^ (2 * 1 : ℝ) = absk k ^ (2 : ℕ) := by
      rw [show (2 * 1 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [sobWeight, hk, ite_false, h, absk_sq]

private lemma absSq_pos {k : Mode} (hk : k ≠ 0) : 0 < absSq k :=
  lt_of_lt_of_le one_pos (one_le_absSq hk)

private lemma absSq_zero : absSq 0 = 0 := by simp [absSq]

/-- Cauchy-Schwarz on an interval, for continuous functions. -/
private lemma cs_interval {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) (t : ℝ)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, g s * h s) ^ 2 ≤
      (∫ s in (0 : ℝ)..t, g s ^ 2) * ∫ s in (0 : ℝ)..t, h s ^ 2 := by
  set A := ∫ s in (0 : ℝ)..t, g s ^ 2
  set B := ∫ s in (0 : ℝ)..t, h s ^ 2
  set I := ∫ s in (0 : ℝ)..t, g s * h s
  have key : ∀ x : ℝ, 0 ≤ A * (x * x) + (-2 * I) * x + B := by
    intro x
    have h1 : 0 ≤ ∫ s in (0 : ℝ)..t, (x * g s - h s) ^ 2 :=
      intervalIntegral.integral_nonneg ht fun s _ => sq_nonneg _
    have h2 : ∫ s in (0 : ℝ)..t, (x * g s - h s) ^ 2 =
        A * (x * x) + (-2 * I) * x + B := by
      have e : ∀ s, (x * g s - h s) ^ 2 =
          (x * x) * g s ^ 2 + (-2 * x) * (g s * h s) + h s ^ 2 := fun s => by ring
      simp only [e]
      rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      · simp only [A, B, I]; ring
      all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
    rwa [h2] at h1
  have := discrim_le_zero key
  simp only [discrim] at this
  nlinarith

/-- The heat-kernel gain, in the Cauchy-Schwarz form. -/
private lemma heat_gain {lam : ℝ} (hl : 0 < lam) {f : ℝ → V3} (hf : Continuous f) {t : ℝ}
    (ht : 0 ≤ t) :
    lam ^ 2 * ‖ex (-lam * t) • ∫ s in (0 : ℝ)..t, ex (lam * s) • f s‖ ^ 2 ≤
      (1 / 2) * ∫ s in (0 : ℝ)..t, lam * ‖f s‖ ^ 2 := by
  have h1 : ‖∫ s in (0 : ℝ)..t, ex (lam * s) • f s‖ ≤
      ∫ s in (0 : ℝ)..t, Real.exp (lam * s) * ‖f s‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm ht).trans_eq ?_
    simp only [norm_smul, norm_ex]
  have h0 : 0 ≤ ∫ s in (0 : ℝ)..t, Real.exp (lam * s) * ‖f s‖ :=
    intervalIntegral.integral_nonneg ht fun s _ => by positivity
  have h2 := cs_interval (g := fun s => Real.exp (lam * s)) (h := fun s => ‖f s‖)
    (by fun_prop) hf.norm t ht
  have h3 : ∫ s in (0 : ℝ)..t, Real.exp (lam * s) ^ 2 =
      (Real.exp (2 * lam * t) - 1) / (2 * lam) := by
    have e : ∀ s, Real.exp (lam * s) ^ 2 = Real.exp (2 * lam * s) := fun s => by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    simp only [e]
    have hd : ∀ x ∈ uIcc 0 t, HasDerivAt (fun s => Real.exp (2 * lam * s) / (2 * lam))
        (Real.exp (2 * lam * x)) x := fun x _ => by
      have h : HasDerivAt (fun s => Real.exp (2 * lam * s) / (2 * lam)) _ x :=
        ((hasDerivAt_id x).const_mul (2 * lam)).exp.div_const (2 * lam)
      refine h.congr_deriv ?_
      simp only [id]
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp; ring
  rw [intervalIntegral.integral_const_mul, norm_smul, norm_ex, mul_pow]
  set B := ∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2
  have hB : 0 ≤ B := intervalIntegral.integral_nonneg ht fun s _ => sq_nonneg _
  have h4 : ‖∫ s in (0 : ℝ)..t, ex (lam * s) • f s‖ ^ 2 ≤
      Real.exp (2 * lam * t) / (2 * lam) * B := by
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (h2.trans ?_)
    rw [h3]
    refine mul_le_mul_of_nonneg_right ?_ hB
    gcongr
    linarith
  have h5 : Real.exp (-lam * t) ^ 2 * Real.exp (2 * lam * t) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    simp only [Real.exp_eq_one_iff]; push_cast; ring
  calc lam ^ 2 * (Real.exp (-lam * t) ^ 2 * ‖∫ s in (0 : ℝ)..t, ex (lam * s) • f s‖ ^ 2)
      ≤ lam ^ 2 * (Real.exp (-lam * t) ^ 2 * (Real.exp (2 * lam * t) / (2 * lam) * B)) := by
        gcongr
    _ = lam ^ 2 * ((Real.exp (-lam * t) ^ 2 * Real.exp (2 * lam * t)) / (2 * lam) * B) := by ring
    _ = 1 / 2 * (lam * B) := by rw [h5]; field_simp


/-! ### The Duhamel integral, mode by mode -/

/-- The Duhamel integral `∫₀ᵗ e^{-|k|²(t-s)} F_k(s) ds`. -/
private def duh (F : ℝ → Field) (t : ℝ) : Field := fun k =>
  ex (-absSq k * t) • ∫ s in (0 : ℝ)..t, ex (absSq k * s) • F s k

private lemma hasDerivAt_ex (c t : ℝ) :
    HasDerivAt (fun t => ex (c * t)) ((c : ℂ) * ex (c * t)) t := by
  have h : HasDerivAt (fun t => ex (c * t)) _ t :=
    (((hasDerivAt_id t).const_mul c).exp).ofReal_comp
  refine h.congr_deriv ?_
  simp only [ex, id]
  push_cast
  ring

private lemma continuous_integrand {F : ℝ → Field} {k : Mode}
    (hc : Continuous fun s => F s k) (c : ℝ) : Continuous fun s => ex (c * s) • F s k :=
  (continuous_ex.comp (by fun_prop)).smul hc

/-- FTC for the Duhamel integral. -/
private lemma hasDerivAt_duh {F : ℝ → Field} {k : Mode} (hc : Continuous fun s => F s k) (t : ℝ) :
    HasDerivAt (fun t => duh F t k) ((-(absSq k : ℝ) : ℂ) • duh F t k + F t k) t := by
  have h1 := (continuous_integrand hc (absSq k)).integral_hasStrictDerivAt 0 t |>.hasDerivAt
  have h2 := hasDerivAt_ex (-absSq k) t
  have h3 : HasDerivAt (fun t => duh F t k) _ t := h2.smul h1
  have e : ex (-absSq k * t) * ex (absSq k * t) = 1 := by
    simp only [ex, ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  refine h3.congr_deriv ?_
  simp only [duh, smul_smul, e, one_smul]
  push_cast
  rw [add_comm]

/-- Free heat flow. -/
private lemma hasDerivAt_free (v : V3) (k : Mode) (t : ℝ) :
    HasDerivAt (fun t => ex (-absSq k * t) • v)
      ((-(absSq k : ℝ) : ℂ) • (ex (-absSq k * t) • v)) t := by
  have h2 := (hasDerivAt_ex (-absSq k) t).smul_const v
  refine h2.congr_deriv ?_
  rw [smul_smul]
  push_cast
  rfl

/-- `y₀`-part plus Duhamel part. -/
private def gam (y₀ : Field) (F : ℝ → Field) (t : ℝ) : Field := fun k =>
  ex (-absSq k * t) • y₀ k + duh F t k

private lemma hasDerivAt_gam (y₀ : Field) {F : ℝ → Field} {k : Mode}
    (hc : Continuous fun s => F s k) (t : ℝ) :
    HasDerivAt (fun t => gam y₀ F t k) ((-(absSq k : ℝ) : ℂ) • gam y₀ F t k + F t k) t := by
  have h : HasDerivAt (fun t => gam y₀ F t k) _ t :=
    (hasDerivAt_free (y₀ k) k t).add (hasDerivAt_duh hc t)
  refine h.congr_deriv ?_
  simp only [gam, smul_add]
  abel

private lemma continuous_gam (y₀ : Field) {F : ℝ → Field} {k : Mode}
    (hc : Continuous fun s => F s k) : Continuous fun t => gam y₀ F t k :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_gam y₀ hc t).continuousAt

private lemma gam_zero (y₀ : Field) (F : ℝ → Field) : gam y₀ F 0 = y₀ := by
  funext k
  simp [gam, duh, ex_zero]

/-- The per-mode Cauchy-Schwarz bound. -/
private lemma mode_duh_le {F : ℝ → Field} {k : Mode} (hc : Continuous fun s => F s k) {t : ℝ}
    (ht : 0 ≤ t) :
    sobWeight 2 k * ‖duh F t k‖ ^ 2 ≤ (1 / 2) * ∫ s in (0 : ℝ)..t, sobWeight 1 k * ‖F s k‖ ^ 2 := by
  rw [sobWeight_two, sobWeight_one]
  by_cases hk : k = 0
  · subst hk; simp [absSq_zero]
  · exact heat_gain (absSq_pos hk) hc ht

private lemma norm_free_le (k : Mode) (v : V3) {t : ℝ} (ht : 0 ≤ t) :
    ‖ex (-absSq k * t) • v‖ ≤ ‖v‖ := by
  rw [norm_smul, norm_ex]
  have : Real.exp (-absSq k * t) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [absSq_nonneg k])
  exact mul_le_of_le_one_left (norm_nonneg _) this

/-- Forces with continuous modes, bounded in `H¹`. -/
private structure Bd (F : ℝ → Field) (B : ℝ) : Prop where
  cont : ∀ k, Continuous fun s => F s k
  inH : ∀ s, InH 1 (F s)
  bd : ∀ s, hnorm 1 (F s) ≤ B

/-- The time-integrated `H¹` density of a force. -/
private def cF (F : ℝ → Field) (T : ℝ) (k : Mode) : ℝ :=
  ∫ s in (0 : ℝ)..T, sobWeight 1 k * ‖F s k‖ ^ 2

private lemma continuous_dens {F : ℝ → Field} {k : Mode} (hc : Continuous fun s => F s k) :
    Continuous fun s => sobWeight 1 k * ‖F s k‖ ^ 2 := by
  fun_prop

private lemma cF_nonneg (F : ℝ → Field) {T : ℝ} (hT : 0 ≤ T) (k : Mode) : 0 ≤ cF F T k :=
  intervalIntegral.integral_nonneg hT fun _ _ =>
    mul_nonneg (sobWeight_nonneg _ _) (sq_nonneg _)

private lemma cF_sum_le {F : ℝ → Field} {B T : ℝ} (hF : Bd F B) (hT : 0 ≤ T) (S : Finset Mode) :
    ∑ k ∈ S, cF F T k ≤ T * B ^ 2 := by
  unfold cF
  rw [← intervalIntegral.integral_finsetSum fun k _ =>
    (continuous_dens (hF.cont k)).intervalIntegrable _ _]
  have hc : Continuous fun s => ∑ k ∈ S, sobWeight 1 k * ‖F s k‖ ^ 2 :=
    continuous_finsetSum _ fun k _ => continuous_dens (hF.cont k)
  have hB : 0 ≤ B := (hnorm_nonneg 1 (F 0)).trans (hF.bd 0)
  have := intervalIntegral.integral_mono_on (μ := volume) hT (hc.intervalIntegrable _ _)
    ((continuous_const (y := B ^ 2)).intervalIntegrable _ _) fun s _ => ?_
  · simpa using this
  · calc ∑ k ∈ S, sobWeight 1 k * ‖F s k‖ ^ 2
        ≤ ∑' k, sobWeight 1 k * ‖F s k‖ ^ 2 := (hF.inH s).sum_le_tsum S fun k _ =>
          mul_nonneg (sobWeight_nonneg _ _) (sq_nonneg _)
      _ = hnorm 1 (F s) ^ 2 := (hnorm_sq (hF.inH s)).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) (hF.bd s) 2

private lemma cF_summable {F : ℝ → Field} {B T : ℝ} (hF : Bd F B) (hT : 0 ≤ T) :
    Summable (cF F T) :=
  summable_of_sum_le (cF_nonneg F hT) (cF_sum_le hF hT)

private lemma cF_mono {F : ℝ → Field} {t T : ℝ} (hc : ∀ k, Continuous fun s => F s k) (ht : 0 ≤ t)
    (htT : t ≤ T) (k : Mode) : cF F t k ≤ cF F T k :=
  intervalIntegral.integral_mono_interval le_rfl ht htT
    (Eventually.of_forall fun _ => mul_nonneg (sobWeight_nonneg _ _) (sq_nonneg _))
    ((continuous_dens (hc k)).intervalIntegrable _ _)

/-- A field whose partial `H^s` sums are bounded by `C²` is in `H^s` with norm at most `C`. -/
private lemma inH_of_sum_le {s C : ℝ} {u : Field} (hC : 0 ≤ C)
    (h : ∀ S : Finset Mode, ∑ k ∈ S, sobWeight s k * ‖u k‖ ^ 2 ≤ C ^ 2) :
    InH s u ∧ hnorm s u ≤ C := by
  have h0 : 0 ≤ fun k => sobWeight s k * ‖u k‖ ^ 2 := fun k =>
    mul_nonneg (sobWeight_nonneg _ _) (sq_nonneg _)
  exact ⟨summable_of_sum_le h0 h, Real.sqrt_le_iff.2 ⟨hC, Real.tsum_le_of_sum_le h0 h⟩⟩

private lemma duh_bound {F : ℝ → Field} {B T t : ℝ} (hF : Bd F B) (ht : 0 ≤ t) (htT : t ≤ T) :
    InH 2 (duh F t) ∧ hnorm 2 (duh F t) ≤ Real.sqrt (T / 2) * B := by
  have hB : 0 ≤ B := (hnorm_nonneg 1 (F 0)).trans (hF.bd 0)
  have hT : 0 ≤ T := ht.trans htT
  refine inH_of_sum_le (by positivity) fun S => ?_
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have h1 : ∑ k ∈ S, sobWeight 2 k * ‖duh F t k‖ ^ 2 ≤ ∑ k ∈ S, (1 / 2) * cF F T k :=
    Finset.sum_le_sum fun k _ => (mode_duh_le (hF.cont k) ht).trans
      (mul_le_mul_of_nonneg_left (cF_mono hF.cont ht htT k) (by norm_num))
  rw [← Finset.mul_sum] at h1
  have := cF_sum_le hF hT S
  linarith

/-- Uniform summable domination of the squared `H²` series gives `H²` continuity. -/
private lemma tendsto_hnorm_of_dom {X : Type*} [TopologicalSpace X] {u : X → Field} {d : Mode → ℝ}
    (hd : Summable d) (hc : ∀ k, Continuous fun x => u x k)
    (hb : ∀ x k, sobWeight 2 k * ‖u x k‖ ^ 2 ≤ d k) (x₀ : X) :
    Tendsto (fun x => hnorm 2 (u x - u x₀)) (𝓝 x₀) (𝓝 0) := by
  have key : Tendsto (fun x => ∑' k, sobWeight 2 k * ‖(u x - u x₀) k‖ ^ 2) (𝓝 x₀)
      (𝓝 (∑' _ : Mode, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun k => 4 * d k) (hd.mul_left 4)
      (fun k => ?_) (Eventually.of_forall fun x k => ?_)
    · have h : Continuous fun x => sobWeight 2 k * ‖(u x - u x₀) k‖ ^ 2 := by
        have := hc k
        simp only [Pi.sub_apply]
        fun_prop
      have := h.tendsto x₀
      simpa using this
    · have h0 := mul_nonneg (sobWeight_nonneg 2 k) (sq_nonneg ‖(u x - u x₀) k‖)
      rw [Real.norm_of_nonneg h0]
      have h1 : ‖(u x - u x₀) k‖ ^ 2 ≤ 2 * ‖u x k‖ ^ 2 + 2 * ‖u x₀ k‖ ^ 2 := by
        have := norm_sub_le (u x k) (u x₀ k)
        have h2 : ‖(u x - u x₀) k‖ = ‖u x k - u x₀ k‖ := rfl
        rw [h2]
        have h3 := norm_nonneg (u x k - u x₀ k)
        nlinarith [sq_nonneg (‖u x k‖ - ‖u x₀ k‖)]
      have h2 := mul_le_mul_of_nonneg_left h1 (sobWeight_nonneg 2 k)
      have h3 := hb x k
      have h4 := hb x₀ k
      nlinarith
  have := key.sqrt
  simpa [hnorm] using this


/-! ### Reality, incompressibility, mean -/

/-- Conjugation is real-linear and continuous. -/
private def conjL : V3 →L[ℝ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := conjV
      map_add' := fun a b => by ext i; simp [conjV]
      map_smul' := fun c a => by ext i; simp [conjV] }

private lemma conjL_apply (v : V3) : conjL v = conjV v := rfl

/-- Pairing with `k` is linear and continuous. -/
private def dotL (k : Mode) : V3 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => dotM v k
      map_add' := fun a b => by simp [dotM, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [dotM, Finset.mul_sum, mul_assoc] }

private lemma dotL_apply (k : Mode) (v : V3) : dotL k v = dotM v k := rfl

private lemma conjV_smul_ex (x : ℝ) (v : V3) : conjV (ex x • v) = ex x • conjV v := by
  ext i
  simp only [conjV, ex, PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]

/-- Real, solenoidal, mean-zero fields. -/
private structure Str (u : Field) : Prop where
  real : IsReal u
  sol : IsSolenoidal u
  mean : u 0 = 0

private lemma duh_str {F : ℝ → Field} (hc : ∀ k, Continuous fun s => F s k)
    (hF : ∀ s, Str (F s)) (t : ℝ) : Str (duh F t) := by
  have hint : ∀ (k : Mode), IntervalIntegrable (fun s => ex (absSq k * s) • F s k) volume 0 t :=
    fun k => (continuous_integrand (hc k) _).intervalIntegrable _ _
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · have : conjV (∫ s in (0 : ℝ)..t, ex (absSq k * s) • F s k) =
        ∫ s in (0 : ℝ)..t, ex (absSq k * s) • F s (-k) := by
      rw [← conjL_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hint k)]
      simp only [(hF _).real k, conjL_apply, conjV_smul_ex]
    simp only [duh, absSq_neg]
    rw [conjV_smul_ex, this]
  · have : dotM (∫ s in (0 : ℝ)..t, ex (absSq k * s) • F s k) k = 0 := by
      rw [← dotL_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hint k)]
      simp only [map_smul, dotL_apply, (hF _).sol k, smul_zero, intervalIntegral.integral_zero]
    change dotL k (_ • _) = 0
    rw [map_smul, dotL_apply, this, smul_zero]
  · simp [duh, (hF _).mean]

private lemma free_str {y₀ : Field} (h : Str y₀) (t : ℝ) :
    Str fun k => ex (-absSq k * t) • y₀ k := by
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · simp only [absSq_neg, conjV_smul_ex, h.real k]
  · change dotL k (_ • _) = 0
    rw [map_smul, dotL_apply, h.sol k, smul_zero]
  · simp [h.mean]

private lemma Str.add {u v : Field} (hu : Str u) (hv : Str v) : Str (u + v) := by
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, hu.real k, hv.real k, ← conjL_apply, map_add]
  · change dotL k (_ + _) = 0
    rw [map_add, dotL_apply, dotL_apply, hu.sol k, hv.sol k, add_zero]
  · simp [hu.mean, hv.mean]

private lemma Str.sub {u v : Field} (hu : Str u) (hv : Str v) : Str (u - v) := by
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · simp only [Pi.sub_apply, hu.real k, hv.real k, ← conjL_apply, map_sub]
  · change dotL k (_ - _) = 0
    rw [map_sub, dotL_apply, dotL_apply, hu.sol k, hv.sol k, sub_zero]
  · simp [hu.mean, hv.mean]

private lemma gam_eq (y₀ : Field) (F : ℝ → Field) (t : ℝ) :
    gam y₀ F t = (fun k => ex (-absSq k * t) • y₀ k) + duh F t := rfl

private lemma free_bound {y₀ : Field} (h : InH 2 y₀) {t : ℝ} (ht : 0 ≤ t) :
    InH 2 (fun k => ex (-absSq k * t) • y₀ k) ∧
      hnorm 2 (fun k => ex (-absSq k * t) • y₀ k) ≤ hnorm 2 y₀ := by
  refine inH_of_sum_le (hnorm_nonneg _ _) fun S => ?_
  rw [hnorm_sq h]
  refine (Finset.sum_le_sum fun k _ => ?_).trans
    (h.sum_le_tsum S fun k _ => mul_nonneg (sobWeight_nonneg _ _) (sq_nonneg _))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_free_le _ _ ht) 2)
    (sobWeight_nonneg _ _)


private lemma gam_adm {y₀ : Field} {F : ℝ → Field} {B : ℝ} (hy : Adm 2 y₀) (hF : Bd F B)
    (hS : ∀ s, Str (F s)) {t : ℝ} (ht : 0 ≤ t) : Adm 2 (gam y₀ F t) := by
  have h := (free_str (y₀ := y₀) ⟨hy.real, hy.sol, hy.mean⟩ t).add (duh_str hF.cont hS t)
  rw [← gam_eq] at h
  have hI : InH 2 (gam y₀ F t) := by
    rw [gam_eq]
    exact (free_bound hy.inH ht).1.add (duh_bound hF ht le_rfl).1
  exact ⟨hI, h.real, h.sol, h.mean⟩

private lemma gam_bound {y₀ : Field} {F : ℝ → Field} {B T t : ℝ} (hy : InH 2 y₀) (hF : Bd F B)
    (ht : 0 ≤ t) (htT : t ≤ T) :
    hnorm 2 (gam y₀ F t) ≤ hnorm 2 y₀ + Real.sqrt (T / 2) * B := by
  rw [gam_eq]
  exact (hnorm_add_le (free_bound hy ht).1 (duh_bound hF ht htT).1).trans
    (add_le_add (free_bound hy ht).2 (duh_bound hF ht htT).2)

private lemma gam_sub {y₀ : Field} {F F' : ℝ → Field} (hc : ∀ k, Continuous fun s => F s k)
    (hc' : ∀ k, Continuous fun s => F' s k) (t : ℝ) :
    gam y₀ F t - gam y₀ F' t = duh (fun s => F s - F' s) t := by
  funext k
  simp only [Pi.sub_apply, gam, duh, add_sub_add_left_eq_sub, smul_sub]
  rw [← smul_sub, ← intervalIntegral.integral_sub
    ((continuous_integrand (hc k) _).intervalIntegrable _ _)
    ((continuous_integrand (hc' k) _).intervalIntegrable _ _)]

private lemma gam_dom {y₀ : Field} {F : ℝ → Field} {B T t : ℝ} (hF : Bd F B)
    (ht : 0 ≤ t) (htT : t ≤ T) (k : Mode) :
    sobWeight 2 k * ‖gam y₀ F t k‖ ^ 2 ≤ 2 * (sobWeight 2 k * ‖y₀ k‖ ^ 2) + cF F T k := by
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_free_le k (y₀ k) ht) 2
  have h2 := (mode_duh_le (hF.cont k) ht).trans
    (mul_le_mul_of_nonneg_left (cF_mono hF.cont ht htT k) (by norm_num))
  have h3 : ‖gam y₀ F t k‖ ^ 2 ≤ 2 * ‖ex (-absSq k * t) • y₀ k‖ ^ 2 + 2 * ‖duh F t k‖ ^ 2 := by
    have h4 := norm_add_le (ex (-absSq k * t) • y₀ k) (duh F t k)
    have h5 : ‖gam y₀ F t k‖ = ‖ex (-absSq k * t) • y₀ k + duh F t k‖ := rfl
    rw [h5]
    have h6 := norm_nonneg (ex (-absSq k * t) • y₀ k + duh F t k)
    nlinarith [sq_nonneg (‖ex (-absSq k * t) • y₀ k‖ - ‖duh F t k‖)]
  have h7 := sobWeight_nonneg 2 k
  have h8 := mul_le_mul_of_nonneg_left h3 h7
  have h9 := mul_le_mul_of_nonneg_left h1 h7
  nlinarith

/-! ### The phase space `H²_sol` -/

/-- Coefficient bound for mean-zero fields. -/
private lemma norm_le_hnorm_one {f : Field} (hf : InH 1 f) (h0 : f 0 = 0) (k : Mode) :
    ‖f k‖ ≤ hnorm 1 f := by
  by_cases hk : k = 0
  · subst hk; rw [h0, norm_zero]; exact hnorm_nonneg _ _
  · have h := sobWeight_mul_norm_le hf k
    rw [sobWeight_one] at h
    have h1 := one_le_absSq hk
    refine abs_le_of_sq_le_sq' ?_ (hnorm_nonneg _ _) |>.2
    nlinarith [sq_nonneg ‖f k‖]

/-- The admissible class. -/
private def H2 : Type := {u : Field // Adm 2 u}

private lemma H2.sub_inH (u v : H2) : InH 2 (u.1 - v.1) := u.2.inH.sub v.2.inH

private noncomputable instance : MetricSpace H2 where
  dist u v := hnorm 2 (u.1 - v.1)
  dist_self u := by simp [hnorm_zero]
  dist_comm _ _ := hnorm_sub_comm
  dist_triangle u v w := by
    have e : u.1 - w.1 = (u.1 - v.1) + (v.1 - w.1) := by abel
    change hnorm 2 (u.1 - w.1) ≤ hnorm 2 (u.1 - v.1) + hnorm 2 (v.1 - w.1)
    rw [e]
    exact hnorm_add_le (H2.sub_inH u v) (H2.sub_inH v w)
  eq_of_dist_eq_zero := fun {u v} h => by
    refine Subtype.ext (sub_eq_zero.1 ?_)
    exact eq_zero_of_hnorm_eq_zero (H2.sub_inH u v) (by simp [u.2.mean, v.2.mean]) h

private lemma H2.dist_def (u v : H2) : dist u v = hnorm 2 (u.1 - v.1) := rfl

private lemma H2.sum_le (u v : H2) (S : Finset Mode) :
    ∑ k ∈ S, sobWeight 2 k * ‖u.1 k - v.1 k‖ ^ 2 ≤ dist u v ^ 2 := by
  rw [H2.dist_def, hnorm_sq (H2.sub_inH u v)]
  exact (H2.sub_inH u v).sum_le_tsum S fun k _ => mul_nonneg (sobWeight_nonneg _ _) (sq_nonneg _)

private lemma H2.norm_mode_le (u v : H2) (k : Mode) : ‖u.1 k - v.1 k‖ ≤ dist u v := by
  have h := norm_le_hnorm_one ((H2.sub_inH u v).mono (by norm_num))
    (by simp [u.2.mean, v.2.mean]) k
  exact h.trans (hnorm_mono (by norm_num) (H2.sub_inH u v))

private lemma H2.exists_limit {u : ℕ → H2} (hu : CauchySeq u) :
    ∃ v : Field, (∀ k, Tendsto (fun n => (u n).1 k) atTop (𝓝 (v k))) ∧
      ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, InH 2 (v - (u n).1) ∧ hnorm 2 (v - (u n).1) ≤ ε := by
  rw [Metric.cauchySeq_iff] at hu
  have hmode : ∀ k, CauchySeq fun n => (u n).1 k := fun k => by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨n₀, hn⟩ := hu ε hε
    exact ⟨n₀, fun m hm n hn' => by
      rw [dist_eq_norm]
      exact (H2.norm_mode_le (u m) (u n) k).trans_lt (hn m hm n hn')⟩
  choose v hv using fun k => cauchySeq_tendsto_of_complete (hmode k)
  refine ⟨v, hv, fun ε hε => ?_⟩
  obtain ⟨n₀, hn⟩ := hu ε hε
  refine ⟨n₀, fun n hnn => inH_of_sum_le hε.le fun S => ?_⟩
  have hlim : Tendsto (fun m => ∑ k ∈ S, sobWeight 2 k * ‖(u m).1 k - (u n).1 k‖ ^ 2) atTop
      (𝓝 (∑ k ∈ S, sobWeight 2 k * ‖(v - (u n).1) k‖ ^ 2)) :=
    tendsto_finsetSum _ fun k _ =>
      (((hv k).sub_const _).norm.pow 2).const_mul _
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop n₀] with m hm
  exact (H2.sum_le (u m) (u n) S).trans
    (pow_le_pow_left₀ dist_nonneg (hn m hm n hnn).le 2)

private instance : CompleteSpace H2 := Metric.complete_of_cauchySeq_tendsto fun u hu => by
  obtain ⟨v, hv, hlim⟩ := H2.exists_limit hu
  have hadm : Adm 2 v := by
    refine ⟨?_, fun k => ?_, fun k => ?_, ?_⟩
    · obtain ⟨n₀, hn⟩ := hlim 1 one_pos
      have := (hn n₀ le_rfl).1.add (u n₀).2.inH
      simpa using this
    · refine tendsto_nhds_unique (hv (-k)) ?_
      have h := (conjL.continuous.tendsto _).comp (hv k)
      refine h.congr fun n => ?_
      exact ((u n).2.real k).symm
    · refine tendsto_nhds_unique ?_ (tendsto_const_nhds (x := (0 : ℂ)) (f := atTop (α := ℕ)))
      have h := ((dotL k).continuous.tendsto _).comp (hv k)
      exact h.congr fun n => (u n).2.sol k
    · refine tendsto_nhds_unique (hv 0) ?_
      simp only [(u _).2.mean]
      exact tendsto_const_nhds
  refine ⟨⟨v, hadm⟩, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨n₀, hn⟩ := hlim (ε / 2) (half_pos hε)
  refine ⟨n₀, fun n hnn => ?_⟩
  change hnorm 2 ((u n).1 - v) < ε
  rw [hnorm_sub_comm]
  exact (hn n hnn).2.trans_lt (half_lt_self hε)


/-! ### The force along a path -/

section Force

variable {N : ℝ → Field → Field → Field} {G : ℝ → Field} {Γ : ℝ}

private lemma nl_bound (hN : Majorized N) (t : ℝ) {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) :
    InH 1 (N t f g) ∧ hnorm 1 (N t f g) ≤ 8 * c4 * (hnorm 2 f * hnorm 2 g) := by
  have h := hN.hnorm_le t (σ := 2) (by norm_num) hf hg hf hg
  rw [show (2 : ℝ) - 1 = 1 by norm_num, show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have h1 := mul_le_mul_of_nonneg_right (wiener_le hf) (hnorm_nonneg 2 g)
  have h2 := mul_le_mul_of_nonneg_left (wiener_le hg) (hnorm_nonneg 2 f)
  nlinarith

private lemma MZ.sub2 {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) : MZ 2 (f - g) :=
  ⟨hf.inH.sub hg.inH, by simp [hf.mean, hg.mean]⟩

private lemma nl_lip (hN : Majorized N) (t : ℝ) {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) :
    InH 1 (N t f f - N t g g) ∧
      hnorm 1 (N t f f - N t g g) ≤ 8 * c4 * ((hnorm 2 f + hnorm 2 g) * hnorm 2 (f - g)) := by
  have hd := MZ.sub2 hf hg
  have e : N t f f - N t g g = N t (f - g) f + N t g (f - g) := by
    rw [hN.sub_left t f g f hf hg hf, hN.sub_right t g f g hg hf hg]
    abel
  have h1 := nl_bound hN t hd hf
  have h2 := nl_bound hN t hg hd
  rw [e]
  refine ⟨h1.1.add h2.1, (hnorm_add_le h1.1 h2.1).trans ?_⟩
  nlinarith [h1.2, h2.2]

/-- The force along a path of admissible fields. -/
private def frc (N : ℝ → Field → Field → Field) (G : ℝ → Field) (p : ℝ → H2) (s : ℝ) : Field :=
  G s - N s (p s).1 (p s).1

private lemma H2.mz (u : H2) : MZ 2 u.1 := u.2.mz

private lemma cont_G (hG : GoodForce G Γ) (k : Mode) : Continuous fun s => G s k := by
  refine continuous_iff_continuousAt.2 fun s₀ => ?_
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_)
    (hG.cont s₀))
  exact norm_le_hnorm_one ((hG.adm t).inH.sub (hG.adm s₀).inH)
    (by simp [(hG.adm t).mean, (hG.adm s₀).mean]) k

private lemma cont_N (hN : Majorized N) {p : ℝ → H2} (hp : Continuous p) {R : ℝ}
    (hR : ∀ s, hnorm 2 (p s).1 ≤ R) (k : Mode) :
    Continuous fun s => N s (p s).1 (p s).1 k := by
  refine continuous_iff_continuousAt.2 fun s₀ => ?_
  set a := (p s₀).1
  have ha : MZ 2 a := (p s₀).mz
  have h1 : Tendsto (fun s => N s (p s).1 (p s).1 k - N s a a k) (𝓝 s₀) (𝓝 0) := by
    have hd : Tendsto (fun s => dist (p s) (p s₀)) (𝓝 s₀) (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 (hp.tendsto s₀)
    have hb : Tendsto (fun s => 8 * c4 * ((R + R) * dist (p s) (p s₀))) (𝓝 s₀) (𝓝 0) := by
      simpa [mul_assoc] using hd.const_mul (8 * c4 * (R + R))
    refine squeeze_zero_norm (fun s => ?_) hb
    have h := nl_lip hN s (p s).mz ha
    have hm : (N s (p s).1 (p s).1 - N s a a) 0 = 0 := by
      simp [hN.mean s _ _ (p s).mz (p s).mz, hN.mean s _ _ ha ha]
    refine (norm_le_hnorm_one h.1 hm k).trans (h.2.trans ?_)
    have h0 : 0 ≤ 8 * c4 := by have := c4_pos; positivity
    refine mul_le_mul_of_nonneg_left ?_ h0
    exact mul_le_mul_of_nonneg_right (add_le_add (hR s) (hR s₀)) (hnorm_nonneg _ _)
  have h2 : Tendsto (fun s => N s a a k) (𝓝 s₀) (𝓝 (N s₀ a a k)) :=
    (hN.cont a a k ha ha).tendsto s₀
  have := h1.add h2
  simp only [zero_add, sub_add_cancel] at this
  exact this

private lemma frc_cont (hN : Majorized N) (hG : GoodForce G Γ) {p : ℝ → H2} (hp : Continuous p)
    {R : ℝ} (hR : ∀ s, hnorm 2 (p s).1 ≤ R) (k : Mode) : Continuous fun s => frc N G p s k :=
  (cont_G hG k).sub (cont_N hN hp hR k)

private lemma frc_bd (hN : Majorized N) (hG : GoodForce G Γ) {p : ℝ → H2} (hp : Continuous p)
    {R : ℝ} (hR : ∀ s, hnorm 2 (p s).1 ≤ R) : Bd (frc N G p) (Γ + 8 * c4 * (R * R)) := by
  have h : ∀ s, InH 1 (N s (p s).1 (p s).1) ∧ hnorm 1 (N s (p s).1 (p s).1) ≤ 8 * c4 * (R * R) :=
    fun s => by
      refine (nl_bound hN s (p s).mz (p s).mz).imp_right fun h1 => h1.trans ?_
      have h0 : 0 ≤ 8 * c4 := by have := c4_pos; positivity
      refine mul_le_mul_of_nonneg_left ?_ h0
      exact mul_le_mul (hR s) (hR s) (hnorm_nonneg _ _) ((hnorm_nonneg _ _).trans (hR s))
  refine ⟨frc_cont hN hG hp hR, fun s => (hG.adm s).inH.sub (h s).1, fun s => ?_⟩
  exact (hnorm_sub_le (hG.adm s).inH (h s).1).trans (add_le_add (hG.bd s) (h s).2)

private lemma frc_sub_bd (hN : Majorized N) (hG : GoodForce G Γ) {p q : ℝ → H2}
    (hp : Continuous p) (hq : Continuous q) {R D : ℝ} (hR : ∀ s, hnorm 2 (p s).1 ≤ R)
    (hR' : ∀ s, hnorm 2 (q s).1 ≤ R) (hD : ∀ s, dist (p s) (q s) ≤ D) :
    Bd (fun s => frc N G p s - frc N G q s) (8 * c4 * ((R + R) * D)) := by
  have e : ∀ s, frc N G p s - frc N G q s = N s (q s).1 (q s).1 - N s (p s).1 (p s).1 :=
    fun s => by simp only [frc]; abel
  have h := fun s => nl_lip hN s (q s).mz (p s).mz
  refine ⟨fun k => (frc_cont hN hG hp hR k).sub (frc_cont hN hG hq hR' k), fun s => ?_,
    fun s => ?_⟩
  · rw [e]; exact (h s).1
  · rw [e]
    refine (h s).2.trans ?_
    have h0 : 0 ≤ 8 * c4 := by have := c4_pos; positivity
    refine mul_le_mul_of_nonneg_left ?_ h0
    have hD' : hnorm 2 ((q s).1 - (p s).1) ≤ D := by
      rw [hnorm_sub_comm]; exact hD s
    have hRR : 0 ≤ R + R := by
      have := (hnorm_nonneg 2 (p s).1).trans (hR s); linarith
    exact mul_le_mul (add_le_add (hR' s) (hR s)) hD' (hnorm_nonneg _ _) hRR

private lemma frc_str (hN : Majorized N) (hG : GoodForce G Γ) (p : ℝ → H2) (s : ℝ) :
    Str (frc N G p s) := by
  have h1 : Str (G s) := ⟨(hG.adm s).real, (hG.adm s).sol, (hG.adm s).mean⟩
  have h2 : Str (N s (p s).1 (p s).1) :=
    ⟨hN.real s _ _ (p s).2 (p s).2, hN.sol s _ _ (p s).mz (p s).mz,
      hN.mean s _ _ (p s).mz (p s).mz⟩
  exact h1.sub h2


/-! ### The fixed point -/

/-- The zero field, as a point of the phase space. -/
private def zH : H2 :=
  ⟨0, inH_zero, fun _ => (conjL.map_zero).symm, fun k => (dotL k).map_zero, rfl⟩

private lemma hnorm_eq_dist (u : H2) : hnorm 2 u.1 = dist u zH := by
  rw [H2.dist_def]
  congr 1
  exact (sub_zero u.1).symm

variable {y₀ : Field} {T : ℝ}

/-- A path on `[0,T]`, extended by constants to the line. -/
private def ext (hT : 0 ≤ T) (y : C(Icc 0 T, H2)) (t : ℝ) : H2 := y (projIcc 0 T hT t)

private lemma continuous_ext (hT : 0 ≤ T) (y : C(Icc 0 T, H2)) : Continuous (ext hT y) :=
  y.continuous.comp continuous_projIcc

private lemma ext_bound (hT : 0 ≤ T) (y : C(Icc 0 T, H2)) (s : ℝ) :
    hnorm 2 (ext hT y s).1 ≤ dist y (ContinuousMap.const _ zH) := by
  rw [hnorm_eq_dist]
  exact ContinuousMap.dist_apply_le_dist (g := ContinuousMap.const _ zH) _

/-- The force along a path has a bound. -/
private lemma ext_bd (hN : Majorized N) (hG : GoodForce G Γ) (hT : 0 ≤ T) (y : C(Icc 0 T, H2)) :
    ∃ B, Bd (frc N G (ext hT y)) B :=
  ⟨_, frc_bd hN hG (continuous_ext hT y) (ext_bound hT y)⟩

/-- The Duhamel map on paths. -/
private def dmap (hN : Majorized N) (hG : GoodForce G Γ) (hy : Adm 2 y₀) (hT : 0 ≤ T)
    (y : C(Icc 0 T, H2)) : C(Icc 0 T, H2) where
  toFun t := ⟨gam y₀ (frc N G (ext hT y)) t.1,
    gam_adm hy (ext_bd hN hG hT y).choose_spec (frc_str hN hG _) t.2.1⟩
  continuous_toFun := by
    have hF := (ext_bd hN hG hT y).choose_spec
    refine continuous_iff_continuousAt.2 fun t₀ => tendsto_iff_dist_tendsto_zero.2 ?_
    exact tendsto_hnorm_of_dom (u := fun x : Icc 0 T => gam y₀ (frc N G (ext hT y)) x.1)
      (d := fun k => 2 * (sobWeight 2 k * ‖y₀ k‖ ^ 2) + cF (frc N G (ext hT y)) T k)
      ((Summable.mul_left 2 hy.inH).add (cF_summable hF hT))
      (fun k => (continuous_gam y₀ (hF.cont k)).comp continuous_subtype_val)
      (fun x k => gam_dom hF x.2.1 x.2.2 k) t₀

private lemma dmap_apply (hN : Majorized N) (hG : GoodForce G Γ) (hy : Adm 2 y₀) (hT : 0 ≤ T)
    (y : C(Icc 0 T, H2)) (t : Icc 0 T) :
    (dmap hN hG hy hT y t).1 = gam y₀ (frc N G (ext hT y)) t.1 := rfl

/-- Banach's theorem for the Duhamel map. -/
private lemma exists_fixed (hN : Majorized N) (hG : GoodForce G Γ) (hy : Adm 2 y₀) (hT : 0 ≤ T)
    {R ρ : ℝ} (hρ : Real.sqrt (T / 2) = ρ) (hR : 0 ≤ R)
    (h1 : hnorm 2 y₀ + ρ * (Γ + 8 * c4 * (R * R)) ≤ R) (h2 : ρ * (8 * c4 * (R + R)) ≤ 1 / 2) :
    ∃ y, dmap hN hG hy hT y = y := by
  set z : C(Icc 0 T, H2) := ContinuousMap.const _ zH
  set s := Metric.closedBall z R
  have hρ0 : 0 ≤ ρ := hρ ▸ Real.sqrt_nonneg _
  have mem : ∀ y, y ∈ s ↔ ∀ t, hnorm 2 (y t).1 ≤ R := fun y => by
    rw [Metric.mem_closedBall, ContinuousMap.dist_le hR]
    exact forall_congr' fun t => by rw [hnorm_eq_dist]; rfl
  have hext : ∀ y ∈ s, ∀ t, hnorm 2 (ext hT y t).1 ≤ R := fun y hy t => (mem y).1 hy _
  have hmaps : MapsTo (dmap hN hG hy hT) s s := fun y hys => (mem _).2 fun t => by
    have hb := frc_bd hN hG (continuous_ext hT y) (hext y hys)
    rw [dmap_apply]
    refine (gam_bound hy.inH hb t.2.1 t.2.2).trans ?_
    rwa [hρ]
  have hcontr : ContractingWith (1 / 2) (hmaps.restrict (dmap hN hG hy hT) s s) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    have hDn : 0 ≤ dist a b := dist_nonneg
    have ha := hext a.1 a.2
    have hb := hext b.1 b.2
    have hca := continuous_ext hT a.1
    have hcb := continuous_ext hT b.1
    have hD : ∀ t, dist (ext hT a.1 t) (ext hT b.1 t) ≤ dist a b := fun t =>
      ContinuousMap.dist_apply_le_dist (f := a.1) (g := b.1) _
    have hbd := frc_sub_bd hN hG hca hcb ha hb hD
    rw [Subtype.dist_eq]
    refine (ContinuousMap.dist_le (by positivity)).2 fun t => ?_
    rw [H2.dist_def, MapsTo.val_restrict_apply, MapsTo.val_restrict_apply, dmap_apply, dmap_apply,
      gam_sub (frc_bd hN hG hca ha).cont (frc_bd hN hG hcb hb).cont]
    refine (duh_bound hbd t.2.1 t.2.2).2.trans ?_
    rw [hρ]
    have e : ρ * (8 * c4 * ((R + R) * dist a b)) = ρ * (8 * c4 * (R + R)) * dist a b := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h2 hDn
  obtain ⟨y, -, hfix, -⟩ := hcontr.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps
    (x := z) (Metric.mem_closedBall_self hR) (edist_ne_top _ _)
  exact ⟨y, hfix⟩

/-- The fixed point solves the mode equations. -/
private lemma sol_of_fixed (hN : Majorized N) (hG : GoodForce G Γ) (hy : Adm 2 y₀) (hT : 0 < T)
    {y : C(Icc 0 T, H2)} (hfix : dmap hN hG hy hT.le y = y) :
    IsHeatSol N G (ENNReal.ofReal T) (fun t => (ext hT.le y t).1) ∧ (ext hT.le y 0).1 = y₀ := by
  set F := frc N G (ext hT.le y)
  have hF : Bd F _ := frc_bd hN hG (continuous_ext hT.le y) (ext_bound hT.le y)
  have hval : ∀ t ∈ Icc 0 T, (ext hT.le y t).1 = gam y₀ F t := fun t ht => by
    have h1 : ext hT.le y t = y ⟨t, ht⟩ := by
      simp only [ext, projIcc_of_mem hT.le ht]
    rw [h1, ← dmap_apply hN hG hy hT.le y ⟨t, ht⟩, hfix]
  refine ⟨⟨fun t _ _ => (ext hT.le y t).2, fun t₀ _ _ => ?_, fun k t ht ht' => ?_⟩, ?_⟩
  · exact (tendsto_iff_dist_tendsto_zero.1 ((continuous_ext hT.le y).tendsto t₀)).mono_left
      nhdsWithin_le_nhds
  · have htT : t < T := (ENNReal.ofReal_lt_ofReal_iff hT).1 ht'
    have hm : t ∈ Icc 0 T := ⟨ht, htT.le⟩
    have hd := (hasDerivAt_gam y₀ (hF.cont k) t).hasDerivWithinAt (s := Ici 0)
    refine (hd.congr_of_eventuallyEq ?_ (congrFun (hval t hm) k)).congr_deriv ?_
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)]
        with s hs hs'
      exact congrFun (hval s ⟨hs, le_of_lt hs'⟩) k
    · rw [← hval t hm]
      simp only [F, frc, Pi.sub_apply]
      abel
  · rw [hval 0 ⟨le_rfl, hT.le⟩, gam_zero]

end Force

/-- Local existence with time depending only on `(‖y₀‖₂ bound, Γ)`. -/
theorem local_existence (m Γ : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (N : ℝ → Field → Field → Field) (G : ℝ → Field) (y₀ : Field),
      Majorized N → GoodForce G Γ → Adm 2 y₀ → hnorm 2 y₀ ≤ m →
      ∃ y, IsHeatSol N G (ENNReal.ofReal τ) y ∧ y 0 = y₀ := by
  set R : ℝ := |m| + 1
  have hR : 0 < R := by positivity
  have hc := c4_pos
  set X : ℝ := 8 * c4 * (R * R)
  set Y : ℝ := 8 * c4 * (R + R)
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  set A : ℝ := 1 + |Γ| + X + Y
  have hA : 0 < A := by positivity
  set ρ : ℝ := 1 / (2 * A)
  have hρ : 0 < ρ := by positivity
  have hρA : ρ * A = 1 / 2 := by simp only [ρ]; field_simp
  have hT : 0 < 2 * ρ ^ 2 := by positivity
  have hs : Real.sqrt (2 * ρ ^ 2 / 2) = ρ := by
    rw [mul_div_cancel_left₀ _ (two_ne_zero), Real.sqrt_sq hρ.le]
  refine ⟨2 * ρ ^ 2, hT, fun N G y₀ hN hG hy hm => ?_⟩
  have h1 : hnorm 2 y₀ + ρ * (Γ + X) ≤ R := by
    have h3 : ρ * (Γ + X) ≤ ρ * A := mul_le_mul_of_nonneg_left
      (by have := le_abs_self Γ; simp only [A]; linarith) hρ.le
    have h4 := le_abs_self m
    simp only [R]
    linarith
  have h2 : ρ * Y ≤ 1 / 2 := by
    rw [← hρA]
    exact mul_le_mul_of_nonneg_left (by simp only [A]; linarith [abs_nonneg Γ]) hρ.le
  obtain ⟨y, hfix⟩ := exists_fixed hN hG hy hT.le hs hR.le h1 h2
  exact ⟨_, sol_of_fixed hN hG hy hT hfix⟩

end OVNS
