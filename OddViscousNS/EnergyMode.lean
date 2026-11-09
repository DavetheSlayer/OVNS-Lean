import OddViscousNS.Sobolev

/-! # The master weighted energy identity for mode-wise heat equations

This is the only place where a truncated energy identity is passed to the limit.  Every energy
equality or inequality in the development is an instance. -/

open scoped ENNReal Topology
open MeasureTheory Set
noncomputable section
namespace OVNS

/-- Hypotheses: `c` is mode-wise differentiable on `[a,b]`, solves `c_k' = -|k|² c_k + F_k`, lies
in `H^σ` at every time, and `F ∈ L²_t H^{σ-1}`. -/
structure HeatPair (σ a b : ℝ) (c F : ℝ → Field) : Prop where
  inH : ∀ t ∈ Icc a b, InH σ (c t)
  mode : ∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => c s k)
    ((-(absSq k : ℝ) : ℂ) • c t k + F t k) (Icc a b) t
  force_cont : ∀ k, ContinuousOn (fun t => F t k) (Icc a b)
  force_l2 : ∫⁻ t in Icc a b, hsE (σ - 1) (F t) < ∞

variable {σ a b : ℝ} {c F : ℝ → Field}

/-! ### Truncated quantities -/

/-- The energy of the modes in `S`. -/
private def trE (s : ℝ) (S : Finset Mode) (u : Field) : ℝ :=
  ∑ k ∈ S, sobWeight s k * ‖u k‖ ^ 2

/-- The pairing restricted to the modes in `S`. -/
private def trP (σ : ℝ) (S : Finset Mode) (c F : Field) : ℝ :=
  ∑ k ∈ S, sobWeight σ k * (inner ℂ (c k) (F k)).re

private lemma trE_nonneg (s : ℝ) (S : Finset Mode) (u : Field) : 0 ≤ trE s S u :=
  Finset.sum_nonneg fun k _ => mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _)

/-- `|k|^{2σ+2} = |k|^{2σ} |k|²`. -/
private lemma sobWeight_succ (σ : ℝ) (k : Mode) :
    sobWeight (σ + 1) k = sobWeight σ k * absSq k := by
  by_cases hk : k = 0
  · simp [sobWeight, hk]
  · have hr : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
    simp only [sobWeight, hk, ite_false]
    rw [← absk_sq k, show 2 * (σ + 1) = 2 * σ + 2 by ring, Real.rpow_add hr]
    norm_num

/-- Young's inequality with the Sobolev weights. -/
private lemma young_term (σ : ℝ) (k : Mode) (x y : ℝ) :
    2 * (sobWeight σ k * (x * y)) ≤
      sobWeight (σ + 1) k * x ^ 2 + sobWeight (σ - 1) k * y ^ 2 := by
  by_cases hk : k = 0
  · simp [sobWeight, hk]
  · have hr : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
    simp only [sobWeight, hk, ite_false]
    have h1 : absk k ^ (2 * (σ + 1)) = (absk k ^ (σ + 1)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      congr 1
      push_cast
      ring
    have h2 : absk k ^ (2 * (σ - 1)) = (absk k ^ (σ - 1)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      congr 1
      push_cast
      ring
    have h3 : absk k ^ (2 * σ) = absk k ^ (σ + 1) * absk k ^ (σ - 1) := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    rw [h1, h2, h3]
    nlinarith [sq_nonneg (absk k ^ (σ + 1) * x - absk k ^ (σ - 1) * y)]

private lemma two_abs_trP_le (σ : ℝ) (S : Finset Mode) (c F : Field) :
    2 * |trP σ S c F| ≤ trE (σ + 1) S c + trE (σ - 1) S F := by
  have h1 : |trP σ S c F| ≤ ∑ k ∈ S, sobWeight σ k * (‖c k‖ * ‖F k‖) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_of_nonneg (sobWeight_nonneg σ k)]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)) (sobWeight_nonneg σ k)
  have h2 : 2 * ∑ k ∈ S, sobWeight σ k * (‖c k‖ * ‖F k‖) ≤
      trE (σ + 1) S c + trE (σ - 1) S F := by
    rw [Finset.mul_sum, trE, trE, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => young_term σ k _ _
  linarith

private lemma ofReal_trE_le (s : ℝ) (S : Finset Mode) (u : Field) :
    ENNReal.ofReal (trE s S u) ≤ hsE s u := by
  rw [trE, ENNReal.ofReal_sum_of_nonneg fun k _ =>
    mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _)]
  exact sum_le_tsum S

private lemma trE_le_hnorm_sq {s : ℝ} {u : Field} (hu : InH s u) (S : Finset Mode) :
    trE s S u ≤ hnorm s u ^ 2 := by
  rw [hnorm_sq hu]
  exact hu.sum_le_tsum S fun k _ => mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _)

private lemma tendsto_trE {s : ℝ} {u : Field} (hu : InH s u) :
    Filter.Tendsto (fun S => trE s S u) Filter.atTop (𝓝 (hnorm s u ^ 2)) := by
  rw [hnorm_sq hu]
  simpa [HasSum, trE] using hu.hasSum

private lemma tendsto_trP {σ : ℝ} {c F : Field} (hc : InH (σ + 1) c) (hF : InH (σ - 1) F) :
    Filter.Tendsto (fun S => trP σ S c F) Filter.atTop (𝓝 (pair σ c F)) := by
  have hs : Summable fun k => sobWeight σ k * (inner ℂ (c k) (F k)).re := by
    refine Summable.of_norm_bounded (pair_le hc hF).1 fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sobWeight_nonneg σ k), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)) (sobWeight_nonneg σ k)
  simpa [HasSum, trP, pair] using hs.hasSum

/-! ### Measurability and integrability from mode-wise continuity -/

private lemma aemeasurable_hsE {s : ℝ} {u : ℝ → Field}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b)) :
    AEMeasurable (fun t => hsE s (u t)) (volume.restrict (Icc a b)) := by
  refine AEMeasurable.tsum fun k => ?_
  have : ContinuousOn (fun t => sobWeight s k * ‖u t k‖ ^ 2) (Icc a b) :=
    continuousOn_const.mul ((hu k).norm.pow 2)
  exact (ENNReal.continuous_ofReal.comp_continuousOn this).aemeasurable measurableSet_Icc

private lemma ae_inH_of_lintegral {s : ℝ} {u : ℝ → Field}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b))
    (hl : ∫⁻ t in Icc a b, hsE s (u t) < ∞) :
    ∀ᵐ t ∂(volume.restrict (Icc a b)), InH s (u t) := by
  filter_upwards [ae_lt_top' (aemeasurable_hsE hu) hl.ne] with t ht
  exact inH_iff_hsE_lt_top.2 ht

private lemma integrableOn_hnorm_sq {s : ℝ} {u : ℝ → Field}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b))
    (hl : ∫⁻ t in Icc a b, hsE s (u t) < ∞) :
    IntegrableOn (fun t => hnorm s (u t) ^ 2) (Icc a b) := by
  have h := integrable_toReal_of_lintegral_ne_top (aemeasurable_hsE hu) hl.ne
  refine h.congr ?_
  filter_upwards [ae_inH_of_lintegral hu hl] with t ht
  rw [hsE_eq_ofReal ht, ENNReal.toReal_ofReal (sq_nonneg _)]

private lemma continuousOn_trE {s : ℝ} {u : ℝ → Field}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b)) (S : Finset Mode) :
    ContinuousOn (fun t => trE s S (u t)) (Icc a b) :=
  continuousOn_finsetSum S fun k _ => continuousOn_const.mul ((hu k).norm.pow 2)

private lemma continuousOn_trP {σ : ℝ} {u v : ℝ → Field}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b))
    (hv : ∀ k, ContinuousOn (fun t => v t k) (Icc a b)) (S : Finset Mode) :
    ContinuousOn (fun t => trP σ S (u t) (v t)) (Icc a b) :=
  continuousOn_finsetSum S fun k _ => continuousOn_const.mul
    (Complex.continuous_re.comp_continuousOn ((hu k).inner (hv k)))

private lemma lintegral_ofReal_trE {s : ℝ} {u : ℝ → Field}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b)) (hab : a ≤ b) (S : Finset Mode) :
    ∫⁻ t in Icc a b, ENNReal.ofReal (trE s S (u t)) =
      ENNReal.ofReal (∫ t in a..b, trE s S (u t)) := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((continuousOn_trE hu S).integrableOn_Icc) (.of_forall fun t => trE_nonneg s S _)).symm

/-- A bound on all truncated energies integrates to a bound on the full energy. -/
private lemma lintegral_hsE_le {s : ℝ} {u : ℝ → Field} {B : ℝ≥0∞}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b))
    (hB : ∀ S : Finset Mode, ∫⁻ t in Icc a b, ENNReal.ofReal (trE s S (u t)) ≤ B) :
    ∫⁻ t in Icc a b, hsE s (u t) ≤ B := by
  have hm : ∀ k, AEMeasurable (fun t => ENNReal.ofReal (sobWeight s k * ‖u t k‖ ^ 2))
      (volume.restrict (Icc a b)) := fun k =>
    (ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_const.mul ((hu k).norm.pow 2))).aemeasurable measurableSet_Icc
  simp only [hsE]
  rw [lintegral_tsum hm, tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  rw [← lintegral_finsetSum' S fun k _ => hm k]
  refine le_trans (le_of_eq ?_) (hB S)
  refine lintegral_congr fun t => ?_
  rw [trE, ENNReal.ofReal_sum_of_nonneg fun k _ =>
    mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _)]

/-! ### The truncated identity -/

private lemma HeatPair.cont (h : HeatPair σ a b c F) (k : Mode) :
    ContinuousOn (fun t => c t k) (Icc a b) := fun t ht => (h.mode k t ht).continuousWithinAt

private lemma HeatPair.mono_aux {a' b' : ℝ} (h : HeatPair σ a b c F) (ha : a ≤ a') (hb : b' ≤ b) :
    HeatPair σ a' b' c F := by
  have hsub : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha hb
  exact ⟨fun t ht => h.inH t (hsub ht), fun k t ht => (h.mode k t (hsub ht)).mono hsub,
    fun k => (h.force_cont k).mono hsub,
    (lintegral_mono_set hsub).trans_lt h.force_l2⟩

private lemma real_inner_V3 (x y : V3) : inner ℝ x y = (inner ℂ x y).re := by
  simp [PiLp.inner_apply, Complex.re_sum]

/-- `d/dt ‖c_k‖² = -2|k|²‖c_k‖² + 2Re⟨c_k, F_k⟩`. -/
private lemma HeatPair.deriv_norm_sq (h : HeatPair σ a b c F) (k : Mode) {t : ℝ}
    (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => ‖c s k‖ ^ 2)
      (-2 * absSq k * ‖c t k‖ ^ 2 + 2 * (inner ℂ (c t k) (F t k)).re) (Icc a b) t := by
  convert (h.mode k t ht).norm_sq using 1
  rw [real_inner_V3, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im]
  have hn : ((‖c t k‖ : ℂ) ^ 2).re = ‖c t k‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hi : ((‖c t k‖ : ℂ) ^ 2).im = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  simp only [RCLike.ofReal_eq_complex_ofReal, hn, hi]
  ring

/-- The truncated energy identity on the whole interval. -/
private lemma HeatPair.trunc_identity (h : HeatPair σ a b c F) (hab : a ≤ b) (S : Finset Mode) :
    trE σ S (c b) + 2 * ∫ u in a..b, trE (σ + 1) S (c u) =
      trE σ S (c a) + 2 * ∫ u in a..b, trP σ S (c u) (F u) := by
  have hD := continuousOn_trE (s := σ + 1) h.cont S
  have hP := continuousOn_trP (σ := σ) h.cont h.force_cont S
  have hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => trE σ S (c u))
      (-2 * trE (σ + 1) S (c t) + 2 * trP σ S (c t) (F t)) (Icc a b) t := by
    intro t ht
    have : -2 * trE (σ + 1) S (c t) + 2 * trP σ S (c t) (F t) = ∑ k ∈ S, sobWeight σ k *
        (-2 * absSq k * ‖c t k‖ ^ 2 + 2 * (inner ℂ (c t k) (F t k)).re) := by
      simp only [trE, trP, Finset.mul_sum, ← Finset.sum_add_distrib, sobWeight_succ]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact HasDerivWithinAt.fun_sum fun k _ => (h.deriv_norm_sq k ht).const_mul _
  have hI1 : IntervalIntegrable (fun u => trE (σ + 1) S (c u)) volume a b :=
    hD.intervalIntegrable_of_Icc (μ := volume) hab
  have hI2 : IntervalIntegrable (fun u => trP σ S (c u) (F u)) volume a b :=
    hP.intervalIntegrable_of_Icc (μ := volume) hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (fun t ht => (hderiv t ht).continuousWithinAt)
    (fun t ht => (hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    ((hI1.const_mul _).add (hI2.const_mul _))
  rw [intervalIntegral.integral_add (hI1.const_mul _) (hI2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
  linarith

private lemma HeatPair.trunc_diss (h : HeatPair σ a b c F) (hab : a ≤ b) (S : Finset Mode) :
    ∫ u in a..b, trE (σ + 1) S (c u) ≤
      trE σ S (c a) + ∫ u in a..b, trE (σ - 1) S (F u) := by
  have hD := (continuousOn_trE (s := σ + 1) h.cont S).intervalIntegrable_of_Icc (μ := volume) hab
  have hQ := (continuousOn_trE (s := σ - 1) h.force_cont S).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hP := (continuousOn_trP (σ := σ) h.cont h.force_cont S).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hle : 2 * ∫ u in a..b, trP σ S (c u) (F u) ≤
      ∫ u in a..b, (trE (σ + 1) S (c u) + trE (σ - 1) S (F u)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hab (hP.const_mul _) (hD.add hQ) fun u _ => ?_
    have := two_abs_trP_le σ S (c u) (F u)
    linarith [le_abs_self (trP σ S (c u) (F u))]
  rw [intervalIntegral.integral_add hD hQ] at hle
  have hid := h.trunc_identity hab S
  linarith [trE_nonneg σ S (c b)]

/-- Dissipation gain: `c ∈ L²_t H^{σ+1}`, with the a priori bound. -/
theorem HeatPair.dissipation_lt_top (h : HeatPair σ a b c F) (hab : a ≤ b) :
    ∫⁻ t in Icc a b, hsE (σ + 1) (c t) ≤
      ENNReal.ofReal (hnorm σ (c a) ^ 2) + ∫⁻ t in Icc a b, hsE (σ - 1) (F t) := by
  refine lintegral_hsE_le h.cont fun S => ?_
  rw [lintegral_ofReal_trE h.cont hab]
  have hQ := lintegral_ofReal_trE (s := σ - 1) h.force_cont hab S
  calc ENNReal.ofReal (∫ t in a..b, trE (σ + 1) S (c t))
      ≤ ENNReal.ofReal (trE σ S (c a) + ∫ t in a..b, trE (σ - 1) S (F t)) :=
        ENNReal.ofReal_le_ofReal (h.trunc_diss hab S)
    _ ≤ ENNReal.ofReal (trE σ S (c a)) + ENNReal.ofReal (∫ t in a..b, trE (σ - 1) S (F t)) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := by
        refine add_le_add
          (ENNReal.ofReal_le_ofReal (trE_le_hnorm_sq (h.inH a ⟨le_rfl, hab⟩) S)) ?_
        rw [← hQ]
        exact lintegral_mono fun t => ofReal_trE_le _ _ _

private lemma HeatPair.diss_lt_top (h : HeatPair σ a b c F) (hab : a ≤ b) :
    ∫⁻ t in Icc a b, hsE (σ + 1) (c t) < ∞ :=
  (h.dissipation_lt_top hab).trans_lt
    (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, h.force_l2⟩)

theorem HeatPair.ae_inH (h : HeatPair σ a b c F) (hab : a ≤ b) :
    ∀ᵐ t ∂(volume.restrict (Icc a b)), InH (σ + 1) (c t) :=
  ae_inH_of_lintegral h.cont (h.diss_lt_top hab)

/-- Almost every time has `c ∈ H^{σ+1}` and `F ∈ H^{σ-1}`. -/
private lemma HeatPair.ae_good (h : HeatPair σ a b c F) (hab : a ≤ b) :
    ∀ᵐ t ∂(volume.restrict (Icc a b)), InH (σ + 1) (c t) ∧ InH (σ - 1) (F t) := by
  filter_upwards [h.ae_inH hab, ae_inH_of_lintegral h.force_cont h.force_l2] with t h1 h2
  exact ⟨h1, h2⟩

private lemma HeatPair.integrableOn_diss (h : HeatPair σ a b c F) (hab : a ≤ b) :
    IntegrableOn (fun t => hnorm (σ + 1) (c t) ^ 2) (Icc a b) :=
  integrableOn_hnorm_sq h.cont (h.diss_lt_top hab)

/-- The dominating function of the pairing. -/
private lemma HeatPair.integrableOn_bound (h : HeatPair σ a b c F) (hab : a ≤ b) :
    IntegrableOn (fun t => hnorm (σ + 1) (c t) ^ 2 + hnorm (σ - 1) (F t) ^ 2) (Icc a b) :=
  (h.integrableOn_diss hab).add (integrableOn_hnorm_sq h.force_cont h.force_l2)

private lemma HeatPair.integrableOn_pair (h : HeatPair σ a b c F) (hab : a ≤ b) :
    IntegrableOn (fun t => pair σ (c t) (F t)) (Icc a b) := by
  refine Integrable.mono' (h.integrableOn_bound hab) ?_ ?_
  · refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset Mode))
      (f := fun S t => trP σ S (c t) (F t)) (fun S =>
        (continuousOn_trP h.cont h.force_cont S).aestronglyMeasurable measurableSet_Icc) ?_
    filter_upwards [h.ae_good hab] with t ht
    exact tendsto_trP ht.1 ht.2
  · filter_upwards [h.ae_good hab] with t ht
    rw [Real.norm_eq_abs]
    have := (pair_le ht.1 ht.2).2
    nlinarith [sq_nonneg (hnorm (σ + 1) (c t) - hnorm (σ - 1) (F t))]

/-- `t ↦ ‖c t‖²_{σ+1}` is integrable. -/
theorem HeatPair.intervalIntegrable_dissipation (h : HeatPair σ a b c F) (hab : a ≤ b) :
    IntervalIntegrable (fun t => hnorm (σ + 1) (c t) ^ 2) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((h.integrableOn_diss hab).mono_set Ioc_subset_Icc_self)

/-- `t ↦ ⟨c, Λ^{2σ} F⟩` is integrable. -/
theorem HeatPair.intervalIntegrable_pair (h : HeatPair σ a b c F) (hab : a ≤ b) :
    IntervalIntegrable (fun t => pair σ (c t) (F t)) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((h.integrableOn_pair hab).mono_set Ioc_subset_Icc_self)

/-- A property holding a.e. on `Icc a b` holds a.e. on the oriented interval. -/
private lemma ae_uIoc {P : ℝ → Prop} (hab : a ≤ b)
    (hP : ∀ᵐ t ∂(volume.restrict (Icc a b)), P t) : ∀ᵐ t, t ∈ uIoc a b → P t := by
  rw [uIoc_of_le hab]
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hP] with t ht ht'
  exact ht (Ioc_subset_Icc_self ht')

private lemma HeatPair.tendsto_diss (h : HeatPair σ a b c F) (hab : a ≤ b) :
    Filter.Tendsto (fun S => ∫ u in a..b, trE (σ + 1) S (c u)) Filter.atTop
      (𝓝 (∫ u in a..b, hnorm (σ + 1) (c u) ^ 2)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
    (h.intervalIntegrable_dissipation hab) ?_
  · refine .of_forall fun S => ?_
    rw [uIoc_of_le hab]
    exact ((continuousOn_trE h.cont S).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · refine .of_forall fun S => ?_
    filter_upwards [ae_uIoc hab (h.ae_inH hab)] with t ht ht'
    rw [Real.norm_eq_abs, abs_of_nonneg (trE_nonneg _ _ _)]
    exact trE_le_hnorm_sq (ht ht') S
  · filter_upwards [ae_uIoc hab (h.ae_inH hab)] with t ht ht'
    exact tendsto_trE (ht ht')

private lemma HeatPair.tendsto_pair (h : HeatPair σ a b c F) (hab : a ≤ b) :
    Filter.Tendsto (fun S => ∫ u in a..b, trP σ S (c u) (F u)) Filter.atTop
      (𝓝 (∫ u in a..b, pair σ (c u) (F u))) := by
  have hI := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((h.integrableOn_bound hab).mono_set Ioc_subset_Icc_self)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hI ?_
  · refine .of_forall fun S => ?_
    rw [uIoc_of_le hab]
    exact ((continuousOn_trP h.cont h.force_cont S).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine .of_forall fun S => ?_
    filter_upwards [ae_uIoc hab (h.ae_good hab)] with t ht ht'
    rw [Real.norm_eq_abs]
    have h1 := two_abs_trP_le σ S (c t) (F t)
    have h2 := trE_le_hnorm_sq (ht ht').1 S
    have h3 := trE_le_hnorm_sq (ht ht').2 S
    linarith [abs_nonneg (trP σ S (c t) (F t))]
  · filter_upwards [ae_uIoc hab (h.ae_good hab)] with t ht ht'
    exact tendsto_trP (ht ht').1 (ht ht').2

private lemma HeatPair.energy_identity_aux (h : HeatPair σ a b c F) (hab : a ≤ b) :
    hnorm σ (c b) ^ 2 + 2 * ∫ u in a..b, hnorm (σ + 1) (c u) ^ 2 =
      hnorm σ (c a) ^ 2 + 2 * ∫ u in a..b, pair σ (c u) (F u) := by
  have hL := (tendsto_trE (h.inH b ⟨hab, le_rfl⟩)).add ((h.tendsto_diss hab).const_mul 2)
  have hR := (tendsto_trE (h.inH a ⟨le_rfl, hab⟩)).add ((h.tendsto_pair hab).const_mul 2)
  refine tendsto_nhds_unique hL (hR.congr fun S => ?_)
  exact (h.trunc_identity hab S).symm

/-- The `H^σ` energy identity in integrated form. -/
theorem HeatPair.energy_identity (h : HeatPair σ a b c F) {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t)
    (ht : t ≤ b) :
    hnorm σ (c t) ^ 2 + 2 * ∫ u in s..t, hnorm (σ + 1) (c u) ^ 2 =
      hnorm σ (c s) ^ 2 + 2 * ∫ u in s..t, pair σ (c u) (F u) :=
  (h.mono_aux hs ht).energy_identity_aux hst

/-- The norm square is continuous. -/
theorem HeatPair.continuousOn_hnorm_sq (h : HeatPair σ a b c F) (hab : a ≤ b) :
    ContinuousOn (fun t => hnorm σ (c t) ^ 2) (Icc a b) := by
  have hP : ContinuousOn (fun t => ∫ u in a..t, pair σ (c u) (F u)) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (f := fun u => pair σ (c u) (F u)) (a := a) (b := b)
      (by rw [uIcc_of_le hab]; exact h.integrableOn_pair hab)
    rwa [uIcc_of_le hab] at this
  have hD : ContinuousOn (fun t => ∫ u in a..t, hnorm (σ + 1) (c u) ^ 2) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (f := fun u => hnorm (σ + 1) (c u) ^ 2) (a := a) (b := b)
      (by rw [uIcc_of_le hab]; exact h.integrableOn_diss hab)
    rwa [uIcc_of_le hab] at this
  have hC : ContinuousOn (fun t => hnorm σ (c a) ^ 2 + 2 * (∫ u in a..t, pair σ (c u) (F u)) -
      2 * ∫ u in a..t, hnorm (σ + 1) (c u) ^ 2) (Icc a b) :=
    (continuousOn_const.add (hP.const_mul 2)).sub (hD.const_mul 2)
  refine hC.congr fun t ht => ?_
  have := h.energy_identity le_rfl ht.1 ht.2
  linarith

/-- Restriction to a subinterval, and shift. -/
theorem HeatPair.mono {a' b' : ℝ} (h : HeatPair σ a b c F) (ha : a ≤ a') (hb : b' ≤ b) :
    HeatPair σ a' b' c F :=
  h.mono_aux ha hb

end OVNS
