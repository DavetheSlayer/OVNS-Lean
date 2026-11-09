import OddViscousNS.Quant.Joint.Slow.Smoothing

/-!
# E7-P: directional Hilbert transforms and Riesz transforms on `L^{2n}`

Step 5 of `Joint/Slow/Plan.lean`, on polynomials, with no Calderón–Zygmund theory, no circle
group, no density.

* `mP_hilbert_le`: for a real `f` and an additive `θ` with no zero on the spectrum of `f`, the
  function `f + i H_θ f` has spectrum in the open half space `θ > 0`, so all its positive powers
  have mean zero; this gives `2 ‖g‖^{2n}_{2n} ≤ ∫ (|f| + |g|)^{2n}` and by convexity
  `‖H_θ f‖^{2n}_{2n} ≤ 3 (4n+1)^{2n−1} ‖f‖^{2n}_{2n}`;
* `mP_riesz_le`: the rotation identity `∫_0^{2π} θ_j sgn(k·θ) dθ = 4 k_j/|k|`, on slow modes, with
  Jensen and Fubini in the direction.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.Slow

open GN

/-! ### The Riesz transforms -/

/-- The symbol `i k_j / |k|` of the Riesz transform. -/
def rieszSym (j : Fin 3) (k : Mode) : ℂ :=
  if k = 0 then 0 else Complex.I * (((k j : ℝ) / absk k : ℝ) : ℂ)

/-- The Riesz transform `R_j`. -/
def riesz (j : Fin 3) (f : Pol) : Pol := mult (rieszSym j) f

private lemma absk_neg (k : Mode) : absk (-k) = absk k := by
  simp [absk, absSq]

private lemma rieszSym_neg (j : Fin 3) (k : Mode) : rieszSym j (-k) = conj (rieszSym j k) := by
  by_cases hk : k = 0
  · simp [rieszSym, hk]
  · have h : -k ≠ 0 := neg_ne_zero.2 hk
    simp only [rieszSym, hk, h, ite_false, absk_neg, Pi.neg_apply, Int.cast_neg, map_mul,
      Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring

lemma RealC.riesz {f : Pol} (hf : RealC f) (j : Fin 3) : RealC (riesz j f) := fun k => by
  simp only [Slow.riesz, coeff_mult, map_mul, rieszSym_neg, hf k]

lemma IsSlowP.riesz {f : Pol} (hf : IsSlowP f) (j : Fin 3) : IsSlowP (riesz j f) := fun k hk => by
  refine hf k fun h => hk ?_
  simp [Slow.riesz, h]

lemma mean_riesz (j : Fin 3) (f : Pol) : mean (riesz j f) = 0 := by
  simp [mean, riesz, rieszSym]

/-! ### Spectrum in a half space -/

/-- Spectrum in the open half space `θ > 0`. -/
private def PosSpec (θ : Mode → ℝ) (P : Pol) : Prop := ∀ k, P.coeff k ≠ 0 → 0 < θ k

private lemma theta_zero {θ : Mode → ℝ} (hadd : ∀ a b, θ (a + b) = θ a + θ b) : θ 0 = 0 := by
  have h := hadd 0 0
  rw [add_zero] at h
  linarith

private lemma theta_neg {θ : Mode → ℝ} (hadd : ∀ a b, θ (a + b) = θ a + θ b) (k : Mode) :
    θ (-k) = -θ k := by
  have h := hadd k (-k)
  rw [add_neg_cancel, theta_zero hadd] at h
  linarith

private lemma PosSpec.mul {θ : Mode → ℝ} (hadd : ∀ a b, θ (a + b) = θ a + θ b) {P Q : Pol}
    (hP : PosSpec θ P) (hQ : PosSpec θ Q) : PosSpec θ (P * Q) := by
  classical
  intro k hk
  have h := AddMonoidAlgebra.support_coeff_mul_subset P Q (Finsupp.mem_support_iff.2 hk)
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 h
  rw [hadd]
  exact add_pos (hP a (Finsupp.mem_support_iff.1 ha)) (hQ b (Finsupp.mem_support_iff.1 hb))

private lemma PosSpec.pow {θ : Mode → ℝ} (hadd : ∀ a b, θ (a + b) = θ a + θ b) {P : Pol}
    (hP : PosSpec θ P) (m : ℕ) : PosSpec θ (P ^ (m + 1)) := by
  induction m with
  | zero => simpa using hP
  | succ m ih =>
    rw [pow_succ]
    exact ih.mul hadd hP

private lemma PosSpec.mean_eq_zero {θ : Mode → ℝ} (hadd : ∀ a b, θ (a + b) = θ a + θ b) {P : Pol}
    (hP : PosSpec θ P) : mean P = 0 := by
  by_contra h
  have h1 := hP 0 h
  rw [theta_zero hadd] at h1
  exact lt_irrefl _ h1

/-! ### Elementary inequalities -/

private lemma norm_add_pow_sub_pow_le (x y : ℂ) (m : ℕ) :
    ‖(x + y) ^ m - y ^ m‖ ≤ (‖x‖ + ‖y‖) ^ m - ‖y‖ ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (x + y) ^ (m + 1) - y ^ (m + 1) = (x + y) * ((x + y) ^ m - y ^ m) + x * y ^ m := by
      ring
    have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
    have h2 : ‖x + y‖ * ‖(x + y) ^ m - y ^ m‖ ≤ (‖x‖ + ‖y‖) * ((‖x‖ + ‖y‖) ^ m - ‖y‖ ^ m) :=
      mul_le_mul h1 ih (norm_nonneg _) (by positivity)
    rw [e]
    calc ‖(x + y) * ((x + y) ^ m - y ^ m) + x * y ^ m‖
        ≤ ‖x + y‖ * ‖(x + y) ^ m - y ^ m‖ + ‖x‖ * ‖y‖ ^ m := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ (‖x‖ + ‖y‖) * ((‖x‖ + ‖y‖) ^ m - ‖y‖ ^ m) + ‖x‖ * ‖y‖ ^ m := by linarith
      _ = (‖x‖ + ‖y‖) ^ (m + 1) - ‖y‖ ^ (m + 1) := by ring

private lemma mul_div_pow_succ (a : ℝ) {s : ℝ} (hs : s ≠ 0) (m : ℕ) :
    s * (a / s) ^ (m + 1) = (1 / s) ^ m * a ^ (m + 1) := by
  rw [one_div, inv_pow, div_pow, pow_succ s m]
  field_simp

/-- Convexity of `t^{m+1}`, with weights. -/
private lemma add_pow_le_weighted {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) (ht : 0 < t)
    (hst : s + t = 1) (m : ℕ) :
    (a + b) ^ (m + 1) ≤ (1 / s) ^ m * a ^ (m + 1) + (1 / t) ^ m * b ^ (m + 1) := by
  have h := (convexOn_pow (𝕜 := ℝ) (m + 1)).2 (x := a / s) (y := b / t)
    (mem_Ici.2 (by positivity)) (mem_Ici.2 (by positivity)) hs.le ht.le hst
  simp only [smul_eq_mul] at h
  have e1 : s * (a / s) + t * (b / t) = a + b := by
    field_simp
  rwa [e1, mul_div_pow_succ a hs.ne', mul_div_pow_succ b ht.ne'] at h

private lemma exp_half_le : Real.exp (1 / 2) ≤ 5 / 3 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  by_contra h
  nlinarith [not_le.1 h]

private lemma one_add_pow_le {n : ℕ} (hn : 1 ≤ n) :
    (1 / ((4 * (n : ℝ)) / (4 * n + 1))) ^ (2 * n - 1) ≤ 5 / 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : 1 / ((4 * (n : ℝ)) / (4 * n + 1)) = 1 + 1 / (4 * n) := by
    field_simp
  rw [e]
  have h1 : 1 + 1 / (4 * (n : ℝ)) ≤ Real.exp (1 / (4 * n)) := by
    linarith [Real.add_one_le_exp (1 / (4 * (n : ℝ)))]
  have h2 : (1 + 1 / (4 * (n : ℝ))) ^ (2 * n - 1) ≤ Real.exp (1 / (4 * n)) ^ (2 * n - 1) :=
    pow_le_pow_left₀ (by positivity) h1 _
  rw [← Real.exp_nat_mul] at h2
  have h3 : ((2 * n - 1 : ℕ) : ℝ) * (1 / (4 * (n : ℝ))) ≤ 1 / 2 := by
    have : ((2 * n - 1 : ℕ) : ℝ) ≤ 2 * n := by
      exact_mod_cast Nat.sub_le _ _
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  exact h2.trans ((Real.exp_le_exp.2 h3).trans exp_half_le)

/-! ### The directional Hilbert transform -/

/-- The directional Hilbert transform `H_θ`. -/
private abbrev hilb (θ : Mode → ℝ) (f : Pol) : Pol :=
  mult (fun k => -Complex.I * (Real.sign (θ k) : ℂ)) f

private lemma realC_hilb {f : Pol} (hR : RealC f) {θ : Mode → ℝ}
    (hadd : ∀ a b, θ (a + b) = θ a + θ b) : RealC (hilb θ f) := fun k => by
  simp only [hilb, coeff_mult, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, hR k,
    theta_neg hadd k, Real.sign_neg]
  push_cast
  ring

private lemma posSpec_add_I_hilb {f : Pol} {θ : Mode → ℝ}
    (hne : ∀ k, f.coeff k ≠ 0 → θ k ≠ 0) : PosSpec θ (f + Complex.I • hilb θ f) := by
  intro k hk
  by_contra hθ
  have hf : f.coeff k ≠ 0 := by
    intro h0
    apply hk
    simp [h0]
  have hlt : θ k < 0 := lt_of_le_of_ne (not_lt.1 hθ) (hne k hf)
  apply hk
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_smul,
    Finsupp.smul_apply, smul_eq_mul, hilb, coeff_mult, Real.sign_of_neg hlt]
  push_cast
  linear_combination (f.coeff k) * Complex.I_sq

/-- `2 ‖g‖^{2n}_{2n} ≤ ∫ (|f| + |g|)^{2n}`, for `g = H_θ f`. -/
private lemma two_mul_mP_hilb_le {f : Pol} (hR : RealC f) {θ : Mode → ℝ}
    (hadd : ∀ a b, θ (a + b) = θ a + θ b) (hne : ∀ k, f.coeff k ≠ 0 → θ k ≠ 0) {n : ℕ}
    (hn : 1 ≤ n) :
    2 * mP n (hilb θ f) ≤ ∫ x, (‖ev f x‖ + ‖ev (hilb θ f) x‖) ^ (2 * n) ∂μT := by
  set g := hilb θ f with hg
  have hgR : RealC g := realC_hilb hR hadd
  have hF0 : ∫ x, (ev f x + Complex.I * ev g x) ^ (2 * n) ∂μT = 0 := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    have h := PosSpec.mean_eq_zero hadd ((posSpec_add_I_hilb hne).pow hadd m)
    rw [← J_ev, J_apply, ← hm] at h
    simpa [map_pow, map_add, ContinuousMap.coe_pow] using h
  have hpow : ∀ x, (Complex.I * ev g x) ^ (2 * n) =
      (-1 : ℂ) ^ n * ((‖ev g x‖ ^ (2 * n) : ℝ) : ℂ) := fun x => by
    rw [pow_mul (Complex.I * _), mul_pow, Complex.I_sq, hgR.ev_sq, pow_mul ‖ev g x‖, mul_pow]
    push_cast
    rfl
  have cf := (ev f).continuous
  have cg := (ev g).continuous
  have hc1 : Continuous fun x => (Complex.I * ev g x) ^ (2 * n) := by fun_prop
  have hc2 : Continuous fun x => (ev f x + Complex.I * ev g x) ^ (2 * n) := by fun_prop
  have hc3 : Continuous fun x => (‖ev f x‖ + ‖ev g x‖) ^ (2 * n) := by fun_prop
  have e1 : ∫ x, (Complex.I * ev g x) ^ (2 * n) ∂μT = (-1 : ℂ) ^ n * (mP n g : ℂ) := by
    simp only [hpow, mP]
    rw [integral_const_mul, integral_complex_ofReal]
  have e2 : mP n g = ‖∫ x, ((ev f x + Complex.I * ev g x) ^ (2 * n) -
      (Complex.I * ev g x) ^ (2 * n)) ∂μT‖ := by
    rw [integral_sub (integrable_of_continuous hc2) (integrable_of_continuous hc1), hF0, e1,
      zero_sub, norm_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mP_nonneg n g)]
  have h3 : ‖∫ x, ((ev f x + Complex.I * ev g x) ^ (2 * n) -
      (Complex.I * ev g x) ^ (2 * n)) ∂μT‖ ≤
      ∫ x, ((‖ev f x‖ + ‖ev g x‖) ^ (2 * n) - ‖ev g x‖ ^ (2 * n)) ∂μT := by
    refine norm_integral_le_of_norm_le
      ((integrable_of_continuous hc3).sub (integrable_norm_pow g _))
      (Eventually.of_forall fun x => ?_)
    simpa [norm_mul] using norm_add_pow_sub_pow_le (ev f x) (Complex.I * ev g x) (2 * n)
  rw [integral_sub (integrable_of_continuous hc3) (integrable_norm_pow g _), ← e2] at h3
  have e3 : mP n g = ∫ x, ‖ev g x‖ ^ (2 * n) ∂μT := rfl
  linarith

/-- **The directional Hilbert transform on `L^{2n}`**: `θ` additive, nonzero on the spectrum of the
real `f`.  (`h0` is implied by `hne`, since `θ 0 = 0`; it is kept for the reader.) -/
theorem mP_hilbert_le {f : Pol} (hR : RealC f) (h0 : mean f = 0) {θ : Mode → ℝ}
    (hadd : ∀ a b, θ (a + b) = θ a + θ b) (hne : ∀ k, f.coeff k ≠ 0 → θ k ≠ 0) (n : ℕ)
    (hn : 1 ≤ n) :
    mP n (mult (fun k => -Complex.I * (Real.sign (θ k) : ℂ)) f) ≤
      3 * (4 * (n : ℝ) + 1) ^ (2 * n - 1) * mP n f := by
  have _ := h0
  have h1 := two_mul_mP_hilb_le hR hadd hne hn
  set g := hilb θ f with hg
  obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : 2 * n - 1 = m := by omega
  set K : ℝ := (4 * (n : ℝ) + 1) ^ (2 * n - 1) with hK
  have hpt : ∀ x, (‖ev f x‖ + ‖ev g x‖) ^ (2 * n) ≤
      K * ‖ev f x‖ ^ (2 * n) + (5 / 3) * ‖ev g x‖ ^ (2 * n) := fun x => by
    have hs : (0 : ℝ) < 1 / (4 * n + 1) := by positivity
    have ht : (0 : ℝ) < (4 * n) / (4 * n + 1) := by positivity
    have hst : (1 : ℝ) / (4 * n + 1) + (4 * n) / (4 * n + 1) = 1 := by
      field_simp
      ring
    have h := add_pow_le_weighted (norm_nonneg (ev f x)) (norm_nonneg (ev g x)) hs ht hst m
    rw [← hm] at h
    have e : 1 / (1 / (4 * (n : ℝ) + 1)) = 4 * n + 1 := by
      field_simp
    rw [e, ← hm', ← hK] at h
    refine h.trans (add_le_add_right ?_ _)
    exact mul_le_mul_of_nonneg_right (one_add_pow_le hn) (by positivity)
  have hc3 : Continuous fun x => (‖ev f x‖ + ‖ev g x‖) ^ (2 * n) := by
    have cf := (ev f).continuous
    have cg := (ev g).continuous
    fun_prop
  have h2 := integral_mono (integrable_of_continuous hc3)
    (((integrable_norm_pow f _).const_mul K).add ((integrable_norm_pow g _).const_mul (5 / 3))) hpt
  rw [integral_add' ((integrable_norm_pow f _).const_mul K)
    ((integrable_norm_pow g _).const_mul (5 / 3)), integral_const_mul, integral_const_mul] at h2
  have e1 : mP n g = ∫ x, ‖ev g x‖ ^ (2 * n) ∂μT := rfl
  have e2 : mP n f = ∫ x, ‖ev f x‖ ^ (2 * n) ∂μT := rfl
  rw [← e1, ← e2] at h2
  linarith

/-! ### Averages of multipliers: Jensen and Fubini -/

private lemma ev_mult_apply (m : Mode → ℂ) (f : Pol) (x : T3) :
    ev (mult m f) x = ∑ k ∈ f.coeff.support, m k * f.coeff k * mFourier k x := by
  have h : mult m f = polyOf f.coeff.support (fun k => m k * f.coeff k) := by
    ext k
    rw [coeff_polyOf]
    simp only [tr, coeff_mult]
    split_ifs with hk
    · rfl
    · simp [Finsupp.notMem_support_iff.1 hk]
  rw [h, ev_polyOf, tp_apply]

private lemma measurable_ev_mult {Ω : Type*} [MeasurableSpace Ω] {m : Ω → Mode → ℂ}
    (hm : ∀ k, Measurable fun ω => m ω k) (f : Pol) :
    Measurable fun p : Ω × T3 => ev (mult (m p.1) f) p.2 := by
  simp only [ev_mult_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (((hm k).comp measurable_fst).mul_const _).mul
    ((mFourier k).continuous.measurable.comp measurable_snd)

private lemma norm_ev_mult_le {m : Mode → ℂ} {C : ℝ} (hb : ∀ k, ‖m k‖ ≤ C) (f : Pol) (x : T3) :
    ‖ev (mult m f) x‖ ≤ ∑ k ∈ f.coeff.support, C * ‖f.coeff k‖ := by
  rw [ev_mult_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, ← mul_one (C * ‖f.coeff k‖)]
  exact mul_le_mul (mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _)) (norm_mFourier_le k x)
    (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans (hb k)) (norm_nonneg _))

/-- The value of the mean multiplier is the mean of the values. -/
private lemma ev_mult_integral {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] {m : Ω → Mode → ℂ} (hm : ∀ k, Measurable fun ω => m ω k) {C : ℝ}
    (hb : ∀ ω k, ‖m ω k‖ ≤ C) (f : Pol) (x : T3) :
    ev (mult (fun k => ∫ ω, m ω k ∂ν) f) x = ∫ ω, ev (mult (m ω) f) x ∂ν := by
  simp only [ev_mult_apply]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_mul_const, integral_mul_const]
  · intro k _
    exact ((Integrable.of_bound (hm k).aestronglyMeasurable C
      (ae_of_all _ fun ω => hb ω k)).mul_const _).mul_const _

/-- **An average of multipliers**: if `‖m_ω f‖_{2q}^{2q} ≤ B` for almost all `ω`, then the same
holds for the mean multiplier. -/
theorem mP_average_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (m : Ω → Mode → ℂ) (hm : ∀ k, Measurable fun ω => m ω k) {C : ℝ} (hb : ∀ ω k, ‖m ω k‖ ≤ C)
    (f : Pol) (q : ℕ) {B : ℝ} (hB : ∀ᵐ ω ∂ν, mP q (mult (m ω) f) ≤ B) :
    mP q (mult (fun k => ∫ ω, m ω k ∂ν) f) ≤ B := by
  have hmeas := measurable_ev_mult hm f
  set S : ℝ := ∑ k ∈ f.coeff.support, C * ‖f.coeff k‖ with hS
  have hbd : ∀ ω x, ‖ev (mult (m ω) f) x‖ ≤ S := fun ω x => norm_ev_mult_le (hb ω) f x
  set Φ : Ω → T3 → ℝ := fun ω x => ‖ev (mult (m ω) f) x‖ ^ (2 * q) with hΦ
  have hΦb : ∀ ω x, ‖Φ ω x‖ ≤ S ^ (2 * q) := fun ω x => by
    simp only [hΦ, norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd ω x) _
  have hΦm : Measurable (Function.uncurry Φ) := hmeas.norm.pow_const _
  have hΦi : Integrable (Function.uncurry Φ) (ν.prod μT) :=
    Integrable.of_bound hΦm.aestronglyMeasurable (S ^ (2 * q))
      (ae_of_all _ fun p => hΦb p.1 p.2)
  have hJ : ∀ x, ‖ev (mult (fun k => ∫ ω, m ω k ∂ν) f) x‖ ^ (2 * q) ≤ ∫ ω, Φ ω x ∂ν := fun x => by
    have hGm : Measurable fun ω => ev (mult (m ω) f) x := by
      simp only [ev_mult_apply]
      exact Finset.measurable_sum _ fun k _ => ((hm k).mul_const _).mul_const _
    have hi : Integrable (fun ω => ev (mult (m ω) f) x) ν :=
      Integrable.of_bound hGm.aestronglyMeasurable S (ae_of_all _ fun ω => hbd ω x)
    have hΦx : Integrable (fun ω => Φ ω x) ν :=
      Integrable.of_bound (hGm.norm.pow_const _).aestronglyMeasurable (S ^ (2 * q))
        (ae_of_all _ fun ω => hΦb ω x)
    rw [ev_mult_integral ν hm hb]
    have h1 := norm_integral_le_integral_norm (μ := ν) fun ω => ev (mult (m ω) f) x
    have h2 := (convexOn_pow (𝕜 := ℝ) (2 * q)).map_integral_le (continuous_pow _).continuousOn
      isClosed_Ici (ae_of_all _ fun ω => norm_nonneg (ev (mult (m ω) f) x)) hi.norm hΦx
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 _).trans h2
  calc mP q (mult (fun k => ∫ ω, m ω k ∂ν) f)
      ≤ ∫ x, ∫ ω, Φ ω x ∂ν ∂μT :=
        integral_mono (integrable_norm_pow _ _) hΦi.integral_prod_right hJ
    _ = ∫ ω, ∫ x, Φ ω x ∂μT ∂ν := (integral_integral_swap hΦi).symm
    _ ≤ ∫ _, B ∂ν := integral_mono_ae hΦi.integral_prod_left (integrable_const _) hB
    _ = B := by simp

/-! ### The rotation identity -/

section Rotation

open Real

private lemma exists_angle (a b : ℝ) :
    ∃ β, a = √(a ^ 2 + b ^ 2) * cos β ∧ b = √(a ^ 2 + b ^ 2) * sin β := by
  have e : ‖(⟨a, b⟩ : ℂ)‖ = √(a ^ 2 + b ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [sq]
  refine ⟨Complex.arg ⟨a, b⟩, ?_, ?_⟩
  · rw [← e]
    exact (Complex.norm_mul_cos_arg ⟨a, b⟩).symm
  · rw [← e]
    exact (Complex.norm_mul_sin_arg ⟨a, b⟩).symm

/-- The weighted integral of `sign (cos (α − β))`, over a period. -/
private lemma integral_mul_sign_cos {w : ℝ → ℝ} (hw : Continuous w)
    (hper : Function.Periodic w (2 * π)) (β : ℝ) :
    ∫ α in (0 : ℝ)..(2 * π), w α * Real.sign (cos (α - β)) =
      (∫ α in (β - π / 2)..(β + π / 2), w α) - ∫ α in (β + π / 2)..(β + π / 2 + π), w α := by
  set h : ℝ → ℝ := fun α => w α * Real.sign (cos (α - β)) with hh
  have hπ := pi_pos
  have hp : Function.Periodic h (2 * π) := fun α => by
    simp only [hh, hper α]
    rw [show α + 2 * π - β = (α - β) + 2 * π by ring, cos_add_two_pi]
  have e0 : ∫ α in (0 : ℝ)..(2 * π), h α = ∫ α in (β - π / 2)..(β - π / 2 + 2 * π), h α := by
    simpa using hp.intervalIntegral_add_eq 0 (β - π / 2)
  have h1 : EqOn w h (Ioo (β - π / 2) (β + π / 2)) := fun α hα => by
    have hc : 0 < cos (α - β) := cos_pos_of_mem_Ioo ⟨by linarith [hα.1], by linarith [hα.2]⟩
    simp [hh, Real.sign_of_pos hc]
  have h2 : EqOn (fun α => -w α) h (Ioo (β + π / 2) (β + π / 2 + π)) := fun α hα => by
    have hc : cos (α - β) < 0 :=
      cos_neg_of_pi_div_two_lt_of_lt (by linarith [hα.1]) (by linarith [hα.2])
    simp [hh, Real.sign_of_neg hc]
  have l1 : β - π / 2 ≤ β + π / 2 := by linarith
  have l2 : β + π / 2 ≤ β + π / 2 + π := by linarith
  have i1 : IntervalIntegrable h volume (β - π / 2) (β + π / 2) :=
    (hw.intervalIntegrable _ _).congr_uIoo (by rwa [uIoo_of_le l1])
  have i2 : IntervalIntegrable h volume (β + π / 2) (β + π / 2 + π) :=
    (hw.neg.intervalIntegrable _ _).congr_uIoo (by rwa [uIoo_of_le l2])
  rw [e0, show β - π / 2 + 2 * π = β + π / 2 + π by ring,
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    ← intervalIntegral.integral_congr_Ioo_of_le l1 h1,
    ← intervalIntegral.integral_congr_Ioo_of_le l2 h2, intervalIntegral.integral_neg]
  ring

private lemma integral_cos_mul_sign (β : ℝ) :
    ∫ α in (0 : ℝ)..(2 * π), cos α * Real.sign (cos (α - β)) = 4 * cos β := by
  rw [integral_mul_sign_cos continuous_cos cos_periodic, integral_cos, integral_cos,
    sin_add_pi, sin_add_pi_div_two, sin_sub_pi_div_two]
  ring

private lemma integral_sin_mul_sign (β : ℝ) :
    ∫ α in (0 : ℝ)..(2 * π), sin α * Real.sign (cos (α - β)) = 4 * sin β := by
  rw [integral_mul_sign_cos continuous_sin sin_periodic, integral_sin, integral_sin,
    cos_add_pi, cos_add_pi_div_two, cos_sub_pi_div_two]
  ring

private lemma sign_pos_mul {ρ : ℝ} (hρ : 0 < ρ) (y : ℝ) : Real.sign (ρ * y) = Real.sign y := by
  rcases lt_trichotomy y 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hρ h)]
  · simp [h]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hρ h)]

/-- The direction `(cos α, sin α)`, as an additive functional on the lattice. -/
def thetaA (α : ℝ) (k : Mode) : ℝ := (k 0 : ℝ) * cos α + (k 1 : ℝ) * sin α

lemma thetaA_add (α : ℝ) (a b : Mode) : thetaA α (a + b) = thetaA α a + thetaA α b := by
  simp only [thetaA, Pi.add_apply, Int.cast_add]
  ring

private lemma absk_pos {k : Mode} (hk : k ≠ 0) : 0 < absk k :=
  Real.sqrt_pos.2 (lt_of_lt_of_le one_pos (one_le_absSq hk))

/-- A slow mode, in polar coordinates. -/
private lemma slow_angle {k : Mode} (hk2 : k 2 = 0) :
    ∃ β, (k 0 : ℝ) = absk k * cos β ∧ (k 1 : ℝ) = absk k * sin β ∧
      ∀ α, thetaA α k = absk k * cos (α - β) := by
  have e : absk k = √((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2) := by
    simp [absk, absSq, Fin.sum_univ_three, hk2]
  obtain ⟨β, h0, h1⟩ := exists_angle (k 0 : ℝ) (k 1 : ℝ)
  rw [← e] at h0 h1
  refine ⟨β, h0, h1, fun α => ?_⟩
  rw [thetaA, h0, h1, cos_sub]
  ring

/-- `θ_α k ≠ 0` for almost all `α`, on a nonzero slow mode. -/
private lemma ae_thetaA_ne {k : Mode} (hk0 : k ≠ 0) (hk2 : k 2 = 0) : ∀ᵐ α, thetaA α k ≠ 0 := by
  obtain ⟨β, -, -, hθ⟩ := slow_angle hk2
  have hc : (range fun m : ℤ => (2 * (m : ℝ) + 1) * π / 2 + β).Countable := countable_range _
  filter_upwards [hc.ae_notMem volume] with α hα h0
  rw [hθ] at h0
  obtain ⟨m, hm⟩ := Real.cos_eq_zero_iff.1 ((mul_eq_zero.1 h0).resolve_left (absk_pos hk0).ne')
  exact hα ⟨m, by simp only; linarith⟩

/-- **The rotation identity**, for `cos`. -/
private lemma integral_cos_mul_sign_thetaA {k : Mode} (hk0 : k ≠ 0) (hk2 : k 2 = 0) :
    ∫ α in (0 : ℝ)..(2 * π), cos α * Real.sign (thetaA α k) = 4 * ((k 0 : ℝ) / absk k) := by
  obtain ⟨β, h0, -, hθ⟩ := slow_angle hk2
  have hρ := absk_pos hk0
  simp only [hθ, sign_pos_mul hρ]
  rw [integral_cos_mul_sign, h0]
  field_simp

/-- **The rotation identity**, for `sin`. -/
private lemma integral_sin_mul_sign_thetaA {k : Mode} (hk0 : k ≠ 0) (hk2 : k 2 = 0) :
    ∫ α in (0 : ℝ)..(2 * π), sin α * Real.sign (thetaA α k) = 4 * ((k 1 : ℝ) / absk k) := by
  obtain ⟨β, -, h1, hθ⟩ := slow_angle hk2
  have hρ := absk_pos hk0
  simp only [hθ, sign_pos_mul hρ]
  rw [integral_sin_mul_sign, h1]
  field_simp

/-! ### The Riesz transforms on `L^{2n}` -/

/-- The normalized Lebesgue measure on `(0, 2π]`. -/
private def nuA : Measure ℝ := ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Ioc 0 (2 * π))

private instance : IsProbabilityMeasure nuA := ⟨by
  have h : (0 : ℝ) < 2 * π := by positivity
  rw [nuA, smul_apply, Measure.restrict_apply_univ, volume_Ioc, smul_eq_mul, sub_zero,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ h.ne', ENNReal.ofReal_one]⟩

private lemma integral_nuA (φ : ℝ → ℝ) :
    ∫ α, φ α ∂nuA = (2 * π)⁻¹ * ∫ α in (0 : ℝ)..(2 * π), φ α := by
  rw [nuA, integral_smul_measure, intervalIntegral.integral_of_le (by positivity),
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- The weight `cos` or `sin`. -/
private def wt (j : Fin 3) (α : ℝ) : ℝ := if j = 0 then cos α else sin α

private lemma continuous_wt (j : Fin 3) : Continuous (wt j) := by
  by_cases h : j = 0
  · have e : wt j = cos := funext fun α => by simp [wt, h]
    rw [e]
    exact continuous_cos
  · have e : wt j = sin := funext fun α => by simp [wt, h]
    rw [e]
    exact continuous_sin

private lemma abs_wt_le (j : Fin 3) (α : ℝ) : |wt j α| ≤ 1 := by
  unfold wt
  split_ifs
  · exact abs_cos_le_one α
  · exact abs_sin_le_one α

private lemma integral_wt {j : Fin 3} (hj : j = 0 ∨ j = 1) {k : Mode} (hk0 : k ≠ 0)
    (hk2 : k 2 = 0) :
    ∫ α in (0 : ℝ)..(2 * π), wt j α * Real.sign (thetaA α k) = 4 * ((k j : ℝ) / absk k) := by
  rcases hj with rfl | rfl
  · simpa [wt] using integral_cos_mul_sign_thetaA hk0 hk2
  · simpa [wt] using integral_sin_mul_sign_thetaA hk0 hk2

private lemma measurable_realSign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

private lemma abs_sign_le (r : ℝ) : |Real.sign r| ≤ 1 := by
  rcases Real.sign_apply_eq r with h | h | h <;> simp [h]

/-- The symbol of the rotation. -/
private def mR (j : Fin 3) (α : ℝ) (k : Mode) : ℂ :=
  Complex.I * ((π / 2 * (wt j α * Real.sign (thetaA α k)) : ℝ) : ℂ)

private lemma measurable_mR (j : Fin 3) (k : Mode) : Measurable fun α => mR j α k := by
  have h1 : Continuous fun α => thetaA α k := by
    unfold thetaA
    fun_prop
  have h2 : Measurable fun α => wt j α * Real.sign (thetaA α k) :=
    (continuous_wt j).measurable.mul (measurable_realSign.comp h1.measurable)
  exact (Complex.measurable_ofReal.comp (h2.const_mul (π / 2))).const_mul Complex.I

private lemma norm_mR_le (j : Fin 3) (α : ℝ) (k : Mode) : ‖mR j α k‖ ≤ π / 2 := by
  rw [mR, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_mul, abs_of_pos (by positivity : 0 < π / 2)]
  have h := mul_le_mul (abs_wt_le j α) (abs_sign_le (thetaA α k)) (abs_nonneg _) zero_le_one
  have hπ := pi_pos
  nlinarith

private lemma integral_mR {j : Fin 3} (hj : j = 0 ∨ j = 1) {k : Mode} (hk0 : k ≠ 0)
    (hk2 : k 2 = 0) : ∫ α, mR j α k ∂nuA = rieszSym j k := by
  have hπ := pi_pos
  simp only [mR, rieszSym, hk0, ite_false]
  rw [integral_const_mul, integral_complex_ofReal, integral_nuA,
    intervalIntegral.integral_const_mul, integral_wt hj hk0 hk2]
  congr 2
  field_simp
  ring

private lemma mult_mR (j : Fin 3) (α : ℝ) (f : Pol) :
    mult (mR j α) f = ((-(π / 2) * wt j α : ℝ) : ℂ) •
      mult (fun k => -Complex.I * (Real.sign (thetaA α k) : ℂ)) f := by
  ext k
  simp only [coeff_mult, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, mR]
  push_cast
  ring

private lemma norm_wt_le (j : Fin 3) (α : ℝ) : ‖((-(π / 2) * wt j α : ℝ) : ℂ)‖ ≤ π / 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_pos (by positivity : 0 < π / 2)]
  have h := abs_wt_le j α
  have hπ := pi_pos
  nlinarith

private lemma mP_smul (c : ℂ) (P : Pol) (q : ℕ) : mP q (c • P) = ‖c‖ ^ (2 * q) * mP q P := by
  simp only [mP, map_smul, ContinuousMap.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [integral_const_mul]

private lemma const_le {n : ℕ} (hn : 1 ≤ n) :
    (π / 2) ^ (2 * n) * (3 * (4 * (n : ℝ) + 1) ^ (2 * n - 1)) ≤
      (4 * (4 * (n : ℝ) + 1)) ^ (2 * n) := by
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set N : ℝ := 4 * (n : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by linarith
  have h1 : (π / 2) ^ (2 * n) ≤ 2 ^ (2 * n) :=
    pow_le_pow_left₀ (by positivity) (by linarith [pi_le_four]) _
  have h2 : (3 : ℝ) ≤ 2 ^ (2 * n) :=
    calc (3 : ℝ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : N ^ (2 * n - 1) ≤ N ^ (2 * n) := pow_le_pow_right₀ hN1 (by omega)
  calc (π / 2) ^ (2 * n) * (3 * N ^ (2 * n - 1)) ≤ 2 ^ (2 * n) * (2 ^ (2 * n) * N ^ (2 * n)) := by
        gcongr
    _ = (4 * N) ^ (2 * n) := by
        rw [← mul_assoc, ← mul_pow, ← mul_pow]
        norm_num

/-- **The Riesz transforms on `L^{2n}`**, on slow polynomials. -/
theorem mP_riesz_le {f : Pol} (hR : RealC f) (hs : IsSlowP f) (h0 : mean f = 0) {j : Fin 3}
    (hj : j = 0 ∨ j = 1) (n : ℕ) (hn : 1 ≤ n) :
    mP n (riesz j f) ≤ (4 * (4 * (n : ℝ) + 1)) ^ (2 * n) * mP n f := by
  have hk0 : ∀ k, f.coeff k ≠ 0 → k ≠ 0 := fun k hk h => hk (by rw [h]; exact h0)
  have hae : ∀ᵐ α ∂nuA, ∀ k, f.coeff k ≠ 0 → thetaA α k ≠ 0 := by
    refine Measure.ae_smul_measure (ae_restrict_of_ae (ae_all_iff.2 fun k => ?_)) _
    by_cases hk : f.coeff k = 0
    · simp [hk]
    · filter_upwards [ae_thetaA_ne (hk0 k hk) (hs k hk)] with α h _ using h
  have hB : ∀ᵐ α ∂nuA, mP n (mult (mR j α) f) ≤
      (π / 2) ^ (2 * n) * (3 * (4 * (n : ℝ) + 1) ^ (2 * n - 1) * mP n f) := by
    filter_upwards [hae] with α hα
    rw [mult_mR, mP_smul]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_wt_le j α) _)
      (mP_hilbert_le hR h0 (thetaA_add α) hα n hn) (mP_nonneg _ _) (by positivity)
  have h := mP_average_le nuA (mR j) (measurable_mR j) (norm_mR_le j) f n hB
  have e : mult (fun k => ∫ α, mR j α k ∂nuA) f = riesz j f := by
    ext k
    by_cases hk : f.coeff k = 0
    · simp [riesz, hk]
    · simp only [riesz, coeff_mult]
      rw [integral_mR hj (hk0 k hk) (hs k hk)]
  rw [e] at h
  refine h.trans ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (const_le hn) (mP_nonneg _ _)

end Rotation

end OVNS.Quant.Slow
