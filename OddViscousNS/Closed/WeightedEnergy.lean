import OddViscousNS.EnergyMode
import OddViscousNS.Closed.Metric

/-!
# Energy identities for radial weights dominated by the `H²` weight

`EnergyMode.lean` proves the `H^σ` energy identity for `HeatPair σ a b c F`.  The graph arguments
of Theorem 1.3 need the same identity for the weights `X` (`ω k = 1` off the zero mode) and `Y`
(`ω k = h(|k|²)`), i.e. for any nonnegative weight `ω ≤ |k|⁴`.  With `wE ω u = ∑ ω_k ‖u_k‖²`,
`wDiss ω u = ∑ ω_k |k|² ‖u_k‖²` and `wPair ω c F = ∑ ω_k Re⟨c_k, F_k⟩`:
`wE ω (c t) + 2∫_s^t wDiss ω (c u) = wE ω (c s) + 2∫_s^t wPair ω (c u) (F u)`.
-/

open scoped ENNReal
open scoped Topology
open MeasureTheory Set Filter

noncomputable section

namespace OVNS

/-- A nonnegative weight vanishing at `0` and dominated by the `H²` weight `|k|⁴`. -/
structure WeightLE2 (ω : Mode → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ ω k
  zero : ω 0 = 0
  le : ∀ k, ω k ≤ sobWeight 2 k

/-- `∑_k ω_k ‖u_k‖²`. -/
def wE (ω : Mode → ℝ) (u : Field) : ℝ := ∑' k, ω k * ‖u k‖ ^ 2

/-- `∑_k ω_k |k|² ‖u_k‖²`. -/
def wDiss (ω : Mode → ℝ) (u : Field) : ℝ := ∑' k, ω k * absSq k * ‖u k‖ ^ 2

/-- `∑_k ω_k Re⟨c_k, F_k⟩`. -/
def wPair (ω : Mode → ℝ) (c F : Field) : ℝ := ∑' k, ω k * (inner ℂ (c k) (F k)).re

/-- The `X` weight. -/
def ωX : Mode → ℝ := fun k => if k = 0 then 0 else 1

/-- The `Y` weight `h(|k|²)`. -/
def ωY : Mode → ℝ := fun k => hmet (nsq k)

/-! ### Weight arithmetic -/

private theorem sobWeight_two'' {k : Mode} (hk : k ≠ 0) : sobWeight 2 k = absSq k ^ 2 := by
  have h0 : 0 ≤ absSq k := absSq_nonneg k
  simp only [sobWeight, hk, ↓reduceIte]
  rw [absk, show (2 : ℝ) * 2 = (4 : ℕ) by norm_num, Real.rpow_natCast,
    show 4 = 2 * 2 by rfl, pow_mul, Real.sq_sqrt h0]

private theorem one_le_nsq' {k : Mode} (hk : k ≠ 0) : 1 ≤ nsq k :=
  Nat.one_le_iff_ne_zero.2 fun h ↦ hk ((nsq_eq_zero_iff k).1 h)

private theorem hmet_nsq_zero' : hmet (nsq 0) = 0 := by
  simp [hmet, nsq]

theorem weightLE2_X : WeightLE2 ωX := by
  refine ⟨fun k => ?_, by simp [ωX], fun k => ?_⟩
  · unfold ωX; split_ifs <;> norm_num
  · by_cases hk : k = 0
    · simp [ωX, sobWeight, hk]
    · simp only [ωX, hk, ↓reduceIte]
      rw [sobWeight_two'' hk]
      nlinarith [one_le_absSq hk]

theorem weightLE2_Y : WeightLE2 ωY := by
  refine ⟨fun k => ?_, by simp [ωY, hmet_nsq_zero'], fun k => ?_⟩
  · rcases Nat.eq_zero_or_pos (nsq k) with h0 | h0
    · simp [ωY, h0, hmet]
    · exact (hmet_pos h0).le
  · by_cases hk : k = 0
    · subst hk; simp [ωY, hmet_nsq_zero', sobWeight]
    · simp only [ωY]
      rw [sobWeight_two'' hk, ← nsq_cast]
      have h1 := hmet_upper (nsq k)
      have h2 : (1 : ℝ) ≤ nsq k := by exact_mod_cast one_le_nsq' hk
      nlinarith

theorem wE_X (u : Field) : wE ωX u = ∑' k, (if k = 0 then 0 else ‖u k‖ ^ 2) := by
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0 <;> simp [ωX, hk]

theorem wE_Y (u : Field) : wE ωY u = ∑' k, hmet (nsq k) * ‖u k‖ ^ 2 := rfl

theorem wDiss_Y (u : Field) : wDiss ωY u = ∑' k, absSq k * hmet (nsq k) * ‖u k‖ ^ 2 := by
  refine tsum_congr fun k => ?_
  simp only [ωY]
  ring

variable {σ a b : ℝ} {c F : ℝ → Field}

/-- `|k|^{2σ+2} = |k|^{2σ} |k|²`. -/
private lemma sobWeight_succ' (σ : ℝ) (k : Mode) :
    sobWeight (σ + 1) k = sobWeight σ k * absSq k := by
  by_cases hk : k = 0
  · simp [sobWeight, hk]
  · have hr : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
    simp only [sobWeight, hk, ite_false]
    rw [← absk_sq k, show 2 * (σ + 1) = 2 * σ + 2 by ring, Real.rpow_add hr]
    norm_num

private lemma young_term' (σ : ℝ) (k : Mode) (x y : ℝ) :
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

private lemma WeightLE2.le3 {ω : Mode → ℝ} (hω : WeightLE2 ω) (k : Mode) :
    ω k * absSq k ≤ sobWeight 3 k := by
  rw [show (3 : ℝ) = 2 + 1 by norm_num, sobWeight_succ']
  exact mul_le_mul_of_nonneg_right (hω.le k) (absSq_nonneg k)

private lemma WeightLE2.pterm {ω : Mode → ℝ} (hω : WeightLE2 ω) (k : Mode) (x y : V3) :
    2 * |ω k * (inner ℂ x y).re| ≤
      sobWeight 3 k * ‖x‖ ^ 2 + sobWeight 1 k * ‖y‖ ^ 2 := by
  have hy := young_term' 2 k ‖x‖ ‖y‖
  rw [show (2 : ℝ) + 1 = 3 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num] at hy
  rw [abs_mul, abs_of_nonneg (hω.nonneg k)]
  have h1 : |(inner ℂ x y).re| ≤ ‖x‖ * ‖y‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : ω k * |(inner ℂ x y).re| ≤ sobWeight 2 k * (‖x‖ * ‖y‖) :=
    mul_le_mul (hω.le k) h1 (abs_nonneg _) (sobWeight_nonneg 2 k)
  linarith

/-! ### Truncations -/

private def wtE (ω : Mode → ℝ) (S : Finset Mode) (u : Field) : ℝ :=
  ∑ k ∈ S, ω k * ‖u k‖ ^ 2

private def wtD (ω : Mode → ℝ) (S : Finset Mode) (u : Field) : ℝ :=
  ∑ k ∈ S, ω k * absSq k * ‖u k‖ ^ 2

private def wtP (ω : Mode → ℝ) (S : Finset Mode) (c F : Field) : ℝ :=
  ∑ k ∈ S, ω k * (inner ℂ (c k) (F k)).re

private lemma abs_wtD_le {ω : Mode → ℝ} (hω : WeightLE2 ω) {u : Field} (hu : InH 3 u)
    (S : Finset Mode) : |wtD ω S u| ≤ hnorm 3 u ^ 2 := by
  rw [hnorm_sq hu, wtD, abs_of_nonneg (Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (hω.nonneg k) (absSq_nonneg k)) (sq_nonneg _))]
  refine (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hω.le3 k)
    (sq_nonneg _)).trans ?_
  exact hu.sum_le_tsum S fun k _ => mul_nonneg (sobWeight_nonneg 3 k) (sq_nonneg _)

private lemma abs_wtP_le {ω : Mode → ℝ} (hω : WeightLE2 ω) {c F : Field} (hc : InH 3 c)
    (hF : InH 1 F) (S : Finset Mode) :
    |wtP ω S c F| ≤ hnorm 3 c ^ 2 + hnorm 1 F ^ 2 := by
  have h1 : 2 * |wtP ω S c F| ≤
      ∑ k ∈ S, (sobWeight 3 k * ‖c k‖ ^ 2 + sobWeight 1 k * ‖F k‖ ^ 2) := by
    calc 2 * |wtP ω S c F| ≤ 2 * ∑ k ∈ S, |ω k * (inner ℂ (c k) (F k)).re| := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ S, 2 * |ω k * (inner ℂ (c k) (F k)).re| := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum fun k _ => hω.pterm k _ _
  rw [Finset.sum_add_distrib] at h1
  have h2 := hc.sum_le_tsum S fun k _ => mul_nonneg (sobWeight_nonneg 3 k) (sq_nonneg _)
  have h3 := hF.sum_le_tsum S fun k _ => mul_nonneg (sobWeight_nonneg 1 k) (sq_nonneg _)
  rw [← hnorm_sq hc] at h2
  rw [← hnorm_sq hF] at h3
  have := abs_nonneg (wtP ω S c F)
  have := sq_nonneg (hnorm 3 c)
  have := sq_nonneg (hnorm 1 F)
  linarith

private lemma tendsto_wtE {ω : Mode → ℝ} (hω : WeightLE2 ω) {u : Field} (hu : InH 2 u) :
    Tendsto (fun S => wtE ω S u) atTop (𝓝 (wE ω u)) := by
  have hs : Summable fun k => ω k * ‖u k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hω.nonneg k) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_right (hω.le k) (sq_nonneg _)) hu
  simpa [HasSum, wtE, wE] using hs.hasSum

private lemma tendsto_wtD {ω : Mode → ℝ} (hω : WeightLE2 ω) {u : Field} (hu : InH 3 u) :
    Tendsto (fun S => wtD ω S u) atTop (𝓝 (wDiss ω u)) := by
  have hs : Summable fun k => ω k * absSq k * ‖u k‖ ^ 2 :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (mul_nonneg (hω.nonneg k) (absSq_nonneg k)) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_right (hω.le3 k) (sq_nonneg _)) hu
  simpa [HasSum, wtD, wDiss] using hs.hasSum

private lemma tendsto_wtP {ω : Mode → ℝ} (hω : WeightLE2 ω) {c F : Field} (hc : InH 3 c)
    (hF : InH 1 F) :
    Tendsto (fun S => wtP ω S c F) atTop (𝓝 (wPair ω c F)) := by
  have hs : Summable fun k => ω k * (inner ℂ (c k) (F k)).re := by
    have hg : Summable fun k => sobWeight 3 k * ‖c k‖ ^ 2 + sobWeight 1 k * ‖F k‖ ^ 2 :=
      Summable.add hc hF
    refine Summable.of_norm_bounded hg fun k => ?_
    rw [Real.norm_eq_abs]
    have := hω.pterm k (c k) (F k)
    have := abs_nonneg (ω k * (inner ℂ (c k) (F k)).re)
    have := mul_nonneg (sobWeight_nonneg 3 k) (sq_nonneg ‖c k‖)
    have := mul_nonneg (sobWeight_nonneg 1 k) (sq_nonneg ‖F k‖)
    linarith
  simpa [HasSum, wtP, wPair] using hs.hasSum

private lemma abs_le_of_tendsto' {f : Finset Mode → ℝ} {x B : ℝ}
    (hf : Tendsto f atTop (𝓝 x)) (hB : ∀ S, |f S| ≤ B) : |x| ≤ B :=
  le_of_tendsto' hf.abs hB

/-! ### Continuity, measurability, integrability -/

private lemma HeatPair.cont' (h : HeatPair σ a b c F) (k : Mode) :
    ContinuousOn (fun t => c t k) (Icc a b) := fun t ht => (h.mode k t ht).continuousWithinAt

private lemma continuousOn_wtE {ω : Mode → ℝ} {u : ℝ → Field}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b)) (S : Finset Mode) :
    ContinuousOn (fun t => wtE ω S (u t)) (Icc a b) :=
  continuousOn_finsetSum S fun k _ => continuousOn_const.mul ((hu k).norm.pow 2)

private lemma continuousOn_wtD {ω : Mode → ℝ} {u : ℝ → Field}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b)) (S : Finset Mode) :
    ContinuousOn (fun t => wtD ω S (u t)) (Icc a b) :=
  continuousOn_finsetSum S fun k _ => continuousOn_const.mul ((hu k).norm.pow 2)

private lemma continuousOn_wtP {ω : Mode → ℝ} {u v : ℝ → Field}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b))
    (hv : ∀ k, ContinuousOn (fun t => v t k) (Icc a b)) (S : Finset Mode) :
    ContinuousOn (fun t => wtP ω S (u t) (v t)) (Icc a b) :=
  continuousOn_finsetSum S fun k _ => continuousOn_const.mul
    (Complex.continuous_re.comp_continuousOn ((hu k).inner (hv k)))

private lemma aemeasurable_hsE' {s : ℝ} {u : ℝ → Field}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b)) :
    AEMeasurable (fun t => hsE s (u t)) (volume.restrict (Icc a b)) := by
  refine AEMeasurable.tsum fun k => ?_
  have : ContinuousOn (fun t => sobWeight s k * ‖u t k‖ ^ 2) (Icc a b) :=
    continuousOn_const.mul ((hu k).norm.pow 2)
  exact (ENNReal.continuous_ofReal.comp_continuousOn this).aemeasurable measurableSet_Icc

private lemma HeatPair.aeF1 (h : HeatPair 2 a b c F) :
    ∀ᵐ t ∂(volume.restrict (Icc a b)), InH 1 (F t) := by
  have hl := h.force_l2
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at hl
  filter_upwards [ae_lt_top' (aemeasurable_hsE' h.force_cont) hl.ne] with t ht
  exact inH_iff_hsE_lt_top.2 ht

private lemma HeatPair.ae3 (h : HeatPair 2 a b c F) (hab : a ≤ b) :
    ∀ᵐ t ∂(volume.restrict (Icc a b)), InH 3 (c t) := by
  have := h.ae_inH hab
  rwa [show (2 : ℝ) + 1 = 3 by norm_num] at this

private lemma HeatPair.ae_good' (h : HeatPair 2 a b c F) (hab : a ≤ b) :
    ∀ᵐ t ∂(volume.restrict (Icc a b)), InH 3 (c t) ∧ InH 1 (F t) := by
  filter_upwards [h.ae3 hab, h.aeF1] with t h1 h2
  exact ⟨h1, h2⟩

private lemma HeatPair.integrableOn_d3 (h : HeatPair 2 a b c F) (hab : a ≤ b) :
    IntegrableOn (fun t => hnorm 3 (c t) ^ 2) (Icc a b) := by
  have := h.intervalIntegrable_dissipation hab
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at this
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 this

private lemma HeatPair.integrableOn_F1 (h : HeatPair 2 a b c F) :
    IntegrableOn (fun t => hnorm 1 (F t) ^ 2) (Icc a b) := by
  have hl := h.force_l2
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at hl
  have hi := integrable_toReal_of_lintegral_ne_top (aemeasurable_hsE' h.force_cont) hl.ne
  refine hi.congr ?_
  filter_upwards [h.aeF1] with t ht
  rw [hsE_eq_ofReal ht, ENNReal.toReal_ofReal (sq_nonneg _)]

private lemma HeatPair.integrableOn_bd (h : HeatPair 2 a b c F) (hab : a ≤ b) :
    IntegrableOn (fun t => hnorm 3 (c t) ^ 2 + hnorm 1 (F t) ^ 2) (Icc a b) :=
  (h.integrableOn_d3 hab).add h.integrableOn_F1

private lemma HeatPair.integrableOn_wDiss {ω : Mode → ℝ} (hω : WeightLE2 ω)
    (h : HeatPair 2 a b c F) (hab : a ≤ b) :
    IntegrableOn (fun t => wDiss ω (c t)) (Icc a b) := by
  refine Integrable.mono' (h.integrableOn_d3 hab) ?_ ?_
  · refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Mode))
      (f := fun S t => wtD ω S (c t)) (fun S =>
        (continuousOn_wtD h.cont' S).aestronglyMeasurable measurableSet_Icc) ?_
    filter_upwards [h.ae3 hab] with t ht
    exact tendsto_wtD hω ht
  · filter_upwards [h.ae3 hab] with t ht
    rw [Real.norm_eq_abs]
    exact abs_le_of_tendsto' (tendsto_wtD hω ht) (abs_wtD_le hω ht)

private lemma HeatPair.integrableOn_wPair {ω : Mode → ℝ} (hω : WeightLE2 ω)
    (h : HeatPair 2 a b c F) (hab : a ≤ b) :
    IntegrableOn (fun t => wPair ω (c t) (F t)) (Icc a b) := by
  refine Integrable.mono' (h.integrableOn_bd hab) ?_ ?_
  · refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Mode))
      (f := fun S t => wtP ω S (c t) (F t)) (fun S =>
        (continuousOn_wtP h.cont' h.force_cont S).aestronglyMeasurable measurableSet_Icc) ?_
    filter_upwards [h.ae_good' hab] with t ht
    exact tendsto_wtP hω ht.1 ht.2
  · filter_upwards [h.ae_good' hab] with t ht
    rw [Real.norm_eq_abs]
    exact abs_le_of_tendsto' (tendsto_wtP hω ht.1 ht.2) (abs_wtP_le hω ht.1 ht.2)

/-! ### The truncated identity -/

private lemma real_inner_V3' (x y : V3) : inner ℝ x y = (inner ℂ x y).re := by
  simp [PiLp.inner_apply, Complex.re_sum]

private lemma HeatPair.deriv_norm_sq' (h : HeatPair σ a b c F) (k : Mode) {t : ℝ}
    (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => ‖c s k‖ ^ 2)
      (-2 * absSq k * ‖c t k‖ ^ 2 + 2 * (inner ℂ (c t k) (F t k)).re) (Icc a b) t := by
  convert (h.mode k t ht).norm_sq using 1
  rw [real_inner_V3', inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im]
  have hn : ((‖c t k‖ : ℂ) ^ 2).re = ‖c t k‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hi : ((‖c t k‖ : ℂ) ^ 2).im = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  simp only [RCLike.ofReal_eq_complex_ofReal, hn, hi]
  ring

private lemma HeatPair.wtrunc_identity {ω : Mode → ℝ} (h : HeatPair σ a b c F) (hab : a ≤ b)
    (S : Finset Mode) :
    wtE ω S (c b) + 2 * ∫ u in a..b, wtD ω S (c u) =
      wtE ω S (c a) + 2 * ∫ u in a..b, wtP ω S (c u) (F u) := by
  have hD := continuousOn_wtD (ω := ω) h.cont' S
  have hP := continuousOn_wtP (ω := ω) h.cont' h.force_cont S
  have hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => wtE ω S (c u))
      (-2 * wtD ω S (c t) + 2 * wtP ω S (c t) (F t)) (Icc a b) t := by
    intro t ht
    have : -2 * wtD ω S (c t) + 2 * wtP ω S (c t) (F t) = ∑ k ∈ S, ω k *
        (-2 * absSq k * ‖c t k‖ ^ 2 + 2 * (inner ℂ (c t k) (F t k)).re) := by
      simp only [wtD, wtP, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact HasDerivWithinAt.fun_sum fun k _ => (h.deriv_norm_sq' k ht).const_mul _
  have hI1 : IntervalIntegrable (fun u => wtD ω S (c u)) volume a b :=
    hD.intervalIntegrable_of_Icc (μ := volume) hab
  have hI2 : IntervalIntegrable (fun u => wtP ω S (c u) (F u)) volume a b :=
    hP.intervalIntegrable_of_Icc (μ := volume) hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (fun t ht => (hderiv t ht).continuousWithinAt)
    (fun t ht => (hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    ((hI1.const_mul _).add (hI2.const_mul _))
  rw [intervalIntegral.integral_add (hI1.const_mul _) (hI2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
  linarith

/-! ### Passing to the limit -/

private lemma ae_uIoc' {P : ℝ → Prop} (hab : a ≤ b)
    (hP : ∀ᵐ t ∂(volume.restrict (Icc a b)), P t) : ∀ᵐ t, t ∈ uIoc a b → P t := by
  rw [uIoc_of_le hab]
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hP] with t ht ht'
  exact ht (Ioc_subset_Icc_self ht')

private lemma HeatPair.tendsto_wdiss {ω : Mode → ℝ} (hω : WeightLE2 ω)
    (h : HeatPair 2 a b c F) (hab : a ≤ b) :
    Tendsto (fun S => ∫ u in a..b, wtD ω S (c u)) atTop
      (𝓝 (∫ u in a..b, wDiss ω (c u))) := by
  have hI := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((h.integrableOn_d3 hab).mono_set Ioc_subset_Icc_self)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hI ?_
  · refine .of_forall fun S => ?_
    rw [uIoc_of_le hab]
    exact ((continuousOn_wtD h.cont' S).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · refine .of_forall fun S => ?_
    filter_upwards [ae_uIoc' hab (h.ae3 hab)] with t ht ht'
    rw [Real.norm_eq_abs]
    exact abs_wtD_le hω (ht ht') S
  · filter_upwards [ae_uIoc' hab (h.ae3 hab)] with t ht ht'
    exact tendsto_wtD hω (ht ht')

private lemma HeatPair.tendsto_wpair {ω : Mode → ℝ} (hω : WeightLE2 ω)
    (h : HeatPair 2 a b c F) (hab : a ≤ b) :
    Tendsto (fun S => ∫ u in a..b, wtP ω S (c u) (F u)) atTop
      (𝓝 (∫ u in a..b, wPair ω (c u) (F u))) := by
  have hI := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((h.integrableOn_bd hab).mono_set Ioc_subset_Icc_self)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hI ?_
  · refine .of_forall fun S => ?_
    rw [uIoc_of_le hab]
    exact ((continuousOn_wtP h.cont' h.force_cont S).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine .of_forall fun S => ?_
    filter_upwards [ae_uIoc' hab (h.ae_good' hab)] with t ht ht'
    rw [Real.norm_eq_abs]
    exact abs_wtP_le hω (ht ht').1 (ht ht').2 S
  · filter_upwards [ae_uIoc' hab (h.ae_good' hab)] with t ht ht'
    exact tendsto_wtP hω (ht ht').1 (ht ht').2

private lemma HeatPair.weighted_aux {ω : Mode → ℝ} (hω : WeightLE2 ω)
    (h : HeatPair 2 a b c F) (hab : a ≤ b) :
    wE ω (c b) + 2 * ∫ u in a..b, wDiss ω (c u) =
      wE ω (c a) + 2 * ∫ u in a..b, wPair ω (c u) (F u) := by
  have hL := (tendsto_wtE hω (h.inH b ⟨hab, le_rfl⟩)).add
    ((h.tendsto_wdiss hω hab).const_mul 2)
  have hR := (tendsto_wtE hω (h.inH a ⟨le_rfl, hab⟩)).add
    ((h.tendsto_wpair hω hab).const_mul 2)
  refine tendsto_nhds_unique hL (hR.congr fun S => ?_)
  exact (h.wtrunc_identity hab S).symm

/-- The weighted energy identity in integrated form. -/
theorem HeatPair.weighted_energy_identity {ω : Mode → ℝ} (hω : WeightLE2 ω)
    (h : HeatPair 2 a b c F) {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    wE ω (c t) + 2 * ∫ u in s..t, wDiss ω (c u) = wE ω (c s) + 2 * ∫ u in s..t, wPair ω (c u) (F u) := by
  exact (h.mono hs ht).weighted_aux hω hst

/-- The weighted energy is continuous in time. -/
theorem HeatPair.continuousOn_wE {ω : Mode → ℝ} (hω : WeightLE2 ω) (h : HeatPair 2 a b c F)
    (hab : a ≤ b) : ContinuousOn (fun t => wE ω (c t)) (Icc a b) := by
  have hP : ContinuousOn (fun t => ∫ u in a..t, wPair ω (c u) (F u)) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (f := fun u => wPair ω (c u) (F u)) (a := a) (b := b)
      (by rw [uIcc_of_le hab]; exact h.integrableOn_wPair hω hab)
    rwa [uIcc_of_le hab] at this
  have hD : ContinuousOn (fun t => ∫ u in a..t, wDiss ω (c u)) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (f := fun u => wDiss ω (c u)) (a := a) (b := b)
      (by rw [uIcc_of_le hab]; exact h.integrableOn_wDiss hω hab)
    rwa [uIcc_of_le hab] at this
  have hC : ContinuousOn (fun t => wE ω (c a) + 2 * (∫ u in a..t, wPair ω (c u) (F u)) -
      2 * ∫ u in a..t, wDiss ω (c u)) (Icc a b) :=
    (continuousOn_const.add (hP.const_mul 2)).sub (hD.const_mul 2)
  refine hC.congr fun t ht => ?_
  have := h.weighted_energy_identity hω le_rfl ht.1 ht.2
  linarith

/-- The weighted dissipation and pairing are interval integrable. -/
theorem HeatPair.intervalIntegrable_wDiss {ω : Mode → ℝ} (hω : WeightLE2 ω)
    (h : HeatPair 2 a b c F) (hab : a ≤ b) :
    IntervalIntegrable (fun u => wDiss ω (c u)) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((h.integrableOn_wDiss hω hab).mono_set Ioc_subset_Icc_self)

theorem HeatPair.intervalIntegrable_wPair {ω : Mode → ℝ} (hω : WeightLE2 ω)
    (h : HeatPair 2 a b c F) (hab : a ≤ b) :
    IntervalIntegrable (fun u => wPair ω (c u) (F u)) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((h.integrableOn_wPair hω hab).mono_set Ioc_subset_Icc_self)

end OVNS
