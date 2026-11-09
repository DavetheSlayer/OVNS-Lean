import OddViscousNS.Quant.Energy.Slow.ModeDeriv

/-!
# E7-F, the `H¹` bounds behind the slow residual

The analytic inputs of the `H²` level of the corrected slow field (`Equation.lean`):
* `hnorm_one_kinN_of_loss_le`: the `H¹` bound of the kinetic primitive with an input that loses
  one derivative, `‖f_p‖ ≤ |p| B_p`.  The output weight is split, `|k| ≤ |p| + |k−p|`, and the
  product `|p| |k−p|` is shared out by `2xy ≤ x² + y²`, so that both derivatives sit on one factor:
  no `H³` norm of the second slot is ever used.  Applied to `F' = −AF − Π_F Q(y,y)` this gives
  `hnorm_one_kinN_fastRHS_le`, `‖N(F',F)‖₁ ≲ (c₄‖F‖₂/q)(‖F‖₃ + 𝒜(y)‖y‖₂)` (the trilinear term
  `N(Π_F Q(F,F), F)` costs `𝒜²‖F‖₂` and not `‖F‖₁𝒜(F)‖F‖₃`).
* `hnorm_Qm_one_bound`, `hnorm_Qm_three_bound`: the `H¹` bounds of the convection (M4 at `σ = 2`).
* `heatPair_fast_level_two`: `F` is a heat pair at `σ = 2`, whence the fast `H²` law
  `fast_dissipation_le`, `∫ ‖F‖₃² ≤ ‖F s‖₂² + D²(t−s)` with `D ≥ ‖Q(y,y)‖₁`.
* `lintegral_hsE_one_lt_top`: an a.e. affine bound by `‖F‖₃` is square-integrable in time.
* `integrableOn_hnorm_sq'`: the integrability of `‖u‖_s²` from mode-wise measurability.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace OVNS

/-! ### Sequences -/

/-- Minkowski in `ℓ²` for nonnegative sequences. -/
private lemma sqrt_tsum_add_sq_le {f g : Mode → ℝ} (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfs : Summable fun i => f i ^ 2) (hgs : Summable fun i => g i ^ 2) :
    Summable (fun i => (f i + g i) ^ 2) ∧
      Real.sqrt (∑' i, (f i + g i) ^ 2) ≤
        Real.sqrt (∑' i, f i ^ 2) + Real.sqrt (∑' i, g i ^ 2) := by
  have h := Real.Lp_add_le_tsum_of_nonneg (p := 2) one_le_two
    hf hg (by simpa only [Real.rpow_two] using hfs) (by simpa only [Real.rpow_two] using hgs)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h

/-- `√(∑ c²) ≤ B √(∑ a²)` from the squared form of Young. -/
private lemma sqrt_tsum_le_mul {c a : Mode → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∑' k, c k ^ 2 ≤ B ^ 2 * ∑' k, a k ^ 2) :
    Real.sqrt (∑' k, c k ^ 2) ≤ B * Real.sqrt (∑' k, a k ^ 2) := by
  calc Real.sqrt (∑' k, c k ^ 2) ≤ Real.sqrt (B ^ 2 * ∑' k, a k ^ 2) := Real.sqrt_le_sqrt h
    _ = B * Real.sqrt (∑' k, a k ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]

/-- The shear `(k, p) ↦ (p, k − p)` of the lattice square. -/
private def shear' : Mode × Mode ≃ Mode × Mode where
  toFun z := (z.2, z.1 - z.2)
  invFun z := (z.1 + z.2, z.1)
  left_inv z := by simp
  right_inv z := by simp

/-- Young `ℓ¹ * ℓ¹ ⊂ ℓ¹`. -/
private lemma tonelli_convR {a c : Mode → ℝ} (ha0 : ∀ k, 0 ≤ a k) (hc0 : ∀ k, 0 ≤ c k)
    (ha : Summable a) (hc : Summable c) :
    Summable (fun k => ∑' p, a p * c (k - p)) ∧
      ∑' k, ∑' p, a p * c (k - p) = (∑' k, a k) * ∑' k, c k := by
  have hG : Summable fun z : Mode × Mode => a z.1 * c z.2 := ha.mul_of_nonneg hc ha0 hc0
  have hF : Summable fun z : Mode × Mode => a z.2 * c (z.1 - z.2) :=
    shear'.summable_iff.2 hG
  refine ⟨hF.prod, ?_⟩
  rw [ha.tsum_mul_tsum hc hG, ← shear'.tsum_eq (fun z : Mode × Mode => a z.1 * c z.2)]
  exact (hF.tsum_prod).symm

/-- `|k|^{2·2} = |k|⁴`, as a square of `|k|²`. -/
private lemma absk_rpow_four (k : Mode) : absk k ^ ((2 : ℝ) * 2) = absSq k ^ 2 := by
  rw [show ((2 : ℝ) * 2) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← absk_sq]
  ring

/-- `|k|⁶` is the `H³` weight. -/
private lemma sobWeight_three (k : Mode) : sobWeight 3 k = absk k ^ 6 := by
  unfold sobWeight
  split_ifs with hk
  · subst hk
    simp [absk, absSq]
  · rw [show ((2 : ℝ) * 3) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `hsE` is monotone in the exponent. -/
lemma hsE_le_of_le {s s' : ℝ} (h : s ≤ s') (f : Field) : hsE s f ≤ hsE s' f :=
  tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (sobWeight_mono h k) (sq_nonneg _))

/-- `‖A f‖₁ = ‖f‖₃`. -/
lemma hnorm_one_absSq_smul {f : Field} (hf : InH 3 f) :
    InH 1 (fun k => (absSq k : ℂ) • f k) ∧
      hnorm 1 (fun k => (absSq k : ℂ) • f k) = hnorm 3 f := by
  have e : ∀ k, sobWeight 1 k * ‖(absSq k : ℂ) • f k‖ ^ 2 = sobWeight 3 k * ‖f k‖ ^ 2 := fun k => by
    rw [norm_smul, mul_pow, sobWeight_one, sobWeight_three, Complex.norm_real,
      Real.norm_of_nonneg (absSq_nonneg k), ← absk_sq]
    ring
  refine ⟨?_, ?_⟩
  · show Summable fun k => sobWeight 1 k * ‖(absSq k : ℂ) • f k‖ ^ 2
    simp only [e]
    exact hf
  · unfold hnorm
    exact congrArg Real.sqrt (tsum_congr e)

/-! ### Measurability -/

private lemma aemeasurable_hsE' {s : ℝ} {u : ℝ → Field} {ν : Measure ℝ}
    (hu : ∀ k, AEStronglyMeasurable (fun t => u t k) ν) :
    AEMeasurable (fun t => hsE s (u t)) ν := by
  refine AEMeasurable.tsum fun k => ?_
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (aemeasurable_const.mul ((hu k).norm.aemeasurable.pow_const 2))

/-- `‖u‖_s²` is integrable on a set when the modes are measurable and `∫⁻ ‖u‖_s²` is finite. -/
lemma integrableOn_hnorm_sq' {s : ℝ} {u : ℝ → Field} {S : Set ℝ}
    (hu : ∀ k, AEStronglyMeasurable (fun t => u t k) (volume.restrict S))
    (hl : ∫⁻ t in S, hsE s (u t) < ∞) :
    IntegrableOn (fun t => hnorm s (u t) ^ 2) S := by
  have hm := aemeasurable_hsE' (s := s) hu
  have h := integrable_toReal_of_lintegral_ne_top hm hl.ne
  refine h.congr ?_
  filter_upwards [ae_lt_top' hm hl.ne] with t ht
  rw [hsE_eq_ofReal (inH_iff_hsE_lt_top.2 ht), ENNReal.toReal_ofReal (sq_nonneg _)]

/-- The energy identity turned into an inequality by an a.e. pointwise bound of the pairing:
`2⟨c, Λ^{2σ}F⟩ ≤ θ ‖c‖²_{σ+1} + R` a.e. gives
`‖c t‖_σ² + (2 − θ)∫ ‖c‖²_{σ+1} ≤ ‖c s‖_σ² + ∫ R`. -/
theorem HeatPair.energy_le {σ τ θ s t : ℝ} {c F : ℝ → Field} {R : ℝ → ℝ}
    (h : HeatPair σ s t c F) (hτ : σ + 1 = τ) (hst : s ≤ t)
    (hR : IntervalIntegrable R volume s t)
    (hp : ∀ᵐ u ∂(volume.restrict (Icc s t)),
      2 * pair σ (c u) (F u) ≤ θ * hnorm τ (c u) ^ 2 + R u) :
    hnorm σ (c t) ^ 2 + (2 - θ) * ∫ u in s..t, hnorm τ (c u) ^ 2 ≤
      hnorm σ (c s) ^ 2 + ∫ u in s..t, R u := by
  subst hτ
  have hid := h.energy_identity le_rfl hst le_rfl
  have hD := h.intervalIntegrable_dissipation hst
  have hP := h.intervalIntegrable_pair hst
  have hint : 2 * ∫ u in s..t, pair σ (c u) (F u) ≤
      θ * (∫ u in s..t, hnorm (σ + 1) (c u) ^ 2) + ∫ u in s..t, R u := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hD.const_mul θ) hR]
    exact intervalIntegral.integral_mono_ae_restrict hst (hP.const_mul 2) ((hD.const_mul θ).add hR)
      hp
  linarith

/-! ### The convection in `H¹` -/

/-- (M4) at `σ = 2`: `‖Q^♯(f,g)‖₁ ≤ 4(𝒜(f)‖g‖₂ + ‖f‖₂𝒜(g))`. -/
lemma hnorm_Qm_one_bound {m : Mult} (hm : m.Bdd) {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) :
    InH 1 (Qm m f g) ∧
      hnorm 1 (Qm m f g) ≤ 4 * (wiener f * hnorm 2 g + hnorm 2 f * wiener g) := by
  have h := hnorm_Qm_le hm (σ := 2) (by norm_num) hf hg hf hg
  have e1 : (2 : ℝ) - 1 = 1 := by norm_num
  have e2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
  rwa [e1, e2] at h

/-- `‖Q(X,Z) + Q(Z,X) + Q(Z,Z)‖₁ ≤ 8‖Z‖₂(𝒜(X) + c₄‖X‖₂ + c₄‖Z‖₂)`: a perturbation by a field `Z`
small in `H²`. -/
lemma hnorm_Qm_three_bound {m : Mult} (hm : m.Bdd) {X Z : Field} (hX : MZ 2 X) (hZ : MZ 2 Z) :
    InH 1 (Qm m X Z + Qm m Z X + Qm m Z Z) ∧
      hnorm 1 (Qm m X Z + Qm m Z X + Qm m Z Z) ≤
        8 * hnorm 2 Z * (wiener X + c4 * hnorm 2 X + c4 * hnorm 2 Z) := by
  obtain ⟨i1, b1⟩ := hnorm_Qm_one_bound hm hX hZ
  obtain ⟨i2, b2⟩ := hnorm_Qm_one_bound hm hZ hX
  obtain ⟨i3, b3⟩ := hnorm_Qm_one_bound hm hZ hZ
  have hw := wiener_le hZ
  have n1 := hnorm_nonneg 2 Z
  have n2 := hnorm_nonneg 2 X
  have t1 := hnorm_add_le (i1.add i2) i3
  have t2 := hnorm_add_le i1 i2
  refine ⟨(i1.add i2).add i3, ?_⟩
  have p1 := mul_le_mul_of_nonneg_left hw n2
  have p2 := mul_le_mul_of_nonneg_left hw n1
  nlinarith

/-! ### The primitive with a derivative-losing input -/

/-- **The `H¹` bound of the primitive when the first input loses a derivative**, `‖f_p‖ ≤ |p| B_p`
with `B ∈ ℓ¹`, `|·|²B ∈ ℓ²`: the two derivatives are put on one factor at a time, by
`(|p| + |k−p|)|p| ≤ (3/2)|p|² + (1/2)|k−p|²`. -/
theorem hnorm_one_kinN_of_loss_le {r τ : ℝ} (hr : r ≠ 0) {f g : Field} {B : Mode → ℝ}
    (hB0 : ∀ k, 0 ≤ B k) (hB1 : Summable B) (hB2 : Summable fun k => (absSq k * B k) ^ 2)
    (hf : ∀ p, ‖f p‖ ≤ absk p * B p) (hf2 : Summable fun k => ‖f k‖ ^ 2) (hg : MZ 2 g) :
    InH 1 (kinN r τ f g) ∧
      hnorm 1 (kinN r τ f g) ≤ 1 / |r| *
        (3 * (wiener g * Real.sqrt (∑' k, (absSq k * B k) ^ 2)) + (∑' k, B k) * hnorm 2 g) := by
  have hrp : 0 < |r| := abs_pos.mpr hr
  set A : Mode → ℝ := fun k => ‖g k‖ with hA
  set DB : Mode → ℝ := fun k => absSq k * B k with hDB
  set DA : Mode → ℝ := fun k => absSq k * A k with hDA
  have hA0 : ∀ k, 0 ≤ A k := fun _ => norm_nonneg _
  have hA1 : Summable A := summable_wiener hg.inH
  have hA2 : Summable fun k => A k ^ 2 := summable_sq hg
  have hDB0 : ∀ k, 0 ≤ DB k := fun k => mul_nonneg (absSq_nonneg k) (hB0 k)
  have hDA0 : ∀ k, 0 ≤ DA k := fun k => mul_nonneg (absSq_nonneg k) (hA0 k)
  have hDAe : ∀ k, DA k ^ 2 = sobWeight 2 k * ‖g k‖ ^ 2 := fun k => by
    rw [sobWeight_two, hDA, mul_pow]
  have hDA2 : Summable fun k => DA k ^ 2 := by
    simp only [hDAe]
    exact hg.inH
  obtain ⟨hU1, hU2, hU3⟩ := young_l1_l2 hA0 hDB0 hA1 hB2
  obtain ⟨hV1, hV2, hV3⟩ := young_l1_l2 hB0 hDA0 hB1 hDA2
  set U : Mode → ℝ := convR A DB with hU
  set V : Mode → ℝ := convR B DA with hV
  have hU0 : ∀ k, 0 ≤ U k := fun k => tsum_nonneg fun p => mul_nonneg (hA0 p) (hDB0 _)
  have hV0 : ∀ k, 0 ≤ V k := fun k => tsum_nonneg fun p => mul_nonneg (hB0 p) (hDA0 _)
  -- the pointwise bound
  have key : ∀ k, absk k * ‖kinN r τ f g k‖ ≤ 1 / |r| * (3 * U k + V k) := by
    intro k
    have hs := (convR_le_of_l2 (a := fun k => ‖f k‖) (b := A) (fun _ => norm_nonneg _) hA0 hf2 hA2
      k).1
    have hn := norm_kinN_le (τ := τ) hr hf2 hA2 k
    have hU1' : Summable fun p => DB p * A (k - p) := by
      refine ((Equiv.subLeft k).summable_iff.2 (hU1 k)).congr fun p => ?_
      simp [mul_comm]
    have hUc : U k = ∑' p, DB p * A (k - p) := convR_comm A DB k
    have hsum : absk k * ∑' p, ‖f p‖ * A (k - p) ≤ 3 / 2 * U k + 1 / 2 * V k := by
      rw [hUc, hV, convR, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
        ← (hU1'.mul_left (3 / 2)).tsum_add ((hV1 k).mul_left (1 / 2))]
      refine (hs.mul_left _).tsum_le_tsum (fun p => ?_)
        ((hU1'.mul_left (3 / 2)).add ((hV1 k).mul_left (1 / 2)))
      have hk : absk k ≤ absk p + absk (k - p) := by
        have := absk_add_le p (k - p)
        rwa [add_sub_cancel] at this
      have hp0 := absk_nonneg p
      have hq0 := absk_nonneg (k - p)
      have hz : 0 ≤ B p * A (k - p) := mul_nonneg (hB0 p) (hA0 _)
      have h1 : ‖f p‖ * A (k - p) ≤ absk p * (B p * A (k - p)) := by
        have := mul_le_mul_of_nonneg_right (hf p) (hA0 (k - p))
        linarith [this]
      have h2 : absk k * (‖f p‖ * A (k - p)) ≤
          (absk p + absk (k - p)) * (absk p * (B p * A (k - p))) :=
        mul_le_mul hk h1 (mul_nonneg (norm_nonneg _) (hA0 _)) (by positivity)
      simp only [hDB, hDA]
      rw [← absk_sq p, ← absk_sq (k - p)]
      nlinarith [mul_nonneg hz (sq_nonneg (absk p - absk (k - p)))]
    have hc : (0 : ℝ) ≤ absk k := absk_nonneg k
    calc absk k * ‖kinN r τ f g k‖
        ≤ absk k * (2 / |r| * ∑' p, ‖f p‖ * A (k - p)) := mul_le_mul_of_nonneg_left hn hc
      _ = 2 / |r| * (absk k * ∑' p, ‖f p‖ * A (k - p)) := by ring
      _ ≤ 2 / |r| * (3 / 2 * U k + 1 / 2 * V k) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 / |r| * (3 * U k + V k) := by ring
  -- Minkowski
  have h3U0 : ∀ k, 0 ≤ 3 * U k := fun k => mul_nonneg (by norm_num) (hU0 k)
  have h3U2 : Summable fun k => (3 * U k) ^ 2 := by
    simpa only [mul_pow] using hU2.mul_left ((3 : ℝ) ^ 2)
  obtain ⟨hM1, hM2⟩ := sqrt_tsum_add_sq_le h3U0 hV0 h3U2 hV2
  have hb : ∀ k, sobWeight 1 k * ‖kinN r τ f g k‖ ^ 2 ≤ (1 / |r|) ^ 2 * (3 * U k + V k) ^ 2 := by
    intro k
    have h1 : sobWeight 1 k * ‖kinN r τ f g k‖ ^ 2 = (absk k * ‖kinN r τ f g k‖) ^ 2 := by
      rw [sobWeight_one, mul_pow, absk_sq]
    rw [h1, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (absk_nonneg k) (norm_nonneg _)) (key k) 2
  have hs : Summable fun k => (1 / |r|) ^ 2 * (3 * U k + V k) ^ 2 := hM1.mul_left _
  have hI : InH 1 (kinN r τ f g) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg 1 k) (sq_nonneg _)) hb hs
  refine ⟨hI, ?_⟩
  have hU' : Real.sqrt (∑' k, (3 * U k) ^ 2) = 3 * Real.sqrt (∑' k, U k ^ 2) := by
    simp only [mul_pow]
    rw [tsum_mul_left, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hUb : Real.sqrt (∑' k, U k ^ 2) ≤ (∑' k, A k) * Real.sqrt (∑' k, DB k ^ 2) :=
    sqrt_tsum_le_mul (tsum_nonneg hA0) hU3
  have hVb : Real.sqrt (∑' k, V k ^ 2) ≤ (∑' k, B k) * Real.sqrt (∑' k, DA k ^ 2) :=
    sqrt_tsum_le_mul (tsum_nonneg hB0) hV3
  have hDAn : Real.sqrt (∑' k, DA k ^ 2) = hnorm 2 g := by
    unfold hnorm
    exact congrArg Real.sqrt (tsum_congr hDAe)
  rw [hDAn] at hVb
  calc hnorm 1 (kinN r τ f g) ≤ Real.sqrt (∑' k, (1 / |r|) ^ 2 * (3 * U k + V k) ^ 2) :=
        Real.sqrt_le_sqrt (hI.tsum_le_tsum hb hs)
    _ = 1 / |r| * Real.sqrt (∑' k, (3 * U k + V k) ^ 2) := by
        rw [tsum_mul_left, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ 1 / |r| * (3 * (wiener g * Real.sqrt (∑' k, DB k ^ 2)) + (∑' k, B k) * hnorm 2 g) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : wiener g = ∑' k, A k := rfl
        rw [this]
        linarith

namespace Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### The derivative of the fast part in the primitive -/

/-- `F' = −AF − Π_F Q(y,y)` loses one derivative over `|·|F + 2 |y| * |y|`
(`maj₂`, TeX (M2)). -/
private lemma norm_fastRHS_le (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (p : Mode) :
    ‖fastRHS r g y u p‖ ≤ absk p * (absk p * ‖PiF (actual r g y u) p‖ +
      2 * ∑' q, ‖y u q‖ * ‖y u (p - q)‖) := by
  have hy := (h.sol.adm u hu huT).mz
  have h1 := norm_Qm_le₂ (phaseM_bdd (r * u)) hy hy p
  have h2 : ‖PiF (Qphase (r * u) (y u) (y u)) p‖ ≤ ‖Qphase (r * u) (y u) (y u) p‖ := by
    by_cases hp : p 2 = 0
    · rw [PiF_apply_slow _ hp, norm_zero]
      exact norm_nonneg _
    · rw [PiF_apply_fast _ hp]
  have h3 : ‖(-(absSq p : ℝ) : ℂ) • PiF (actual r g y u) p‖ =
      absk p * (absk p * ‖PiF (actual r g y u) p‖) := by
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (absSq_nonneg p), ← absk_sq]
    ring
  have h4 : ‖fastRHS r g y u p‖ ≤ ‖(-(absSq p : ℝ) : ℂ) • PiF (actual r g y u) p‖ +
      ‖PiF (Qphase (r * u) (y u) (y u)) p‖ := norm_sub_le _ _
  have h5 : ‖Qphase (r * u) (y u) (y u) p‖ ≤ 2 * absk p * ∑' q, ‖y u q‖ * ‖y u (p - q)‖ := h1
  rw [h3] at h4
  have e : absk p * (absk p * ‖PiF (actual r g y u) p‖ + 2 * ∑' q, ‖y u q‖ * ‖y u (p - q)‖) =
      absk p * (absk p * ‖PiF (actual r g y u) p‖) +
        2 * absk p * ∑' q, ‖y u q‖ * ‖y u (p - q)‖ := by ring
  rw [e]
  linarith

/-- **The corrector derivative in `H¹`**, at a time with `F ∈ H³`:
`‖N(F',F)‖₁ ≤ (c₄‖F‖₂/q)(4‖F‖₃ + 26 𝒜(y)‖y‖₂)`. -/
theorem hnorm_one_kinN_fastRHS_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (τ : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (PiF (actual r g y u))) :
    InH 1 (kinN r τ (fastRHS r g y u) (PiF (actual r g y u))) ∧
      hnorm 1 (kinN r τ (fastRHS r g y u) (PiF (actual r g y u))) ≤
        c4 * hnorm 2 (PiF (actual r g y u)) / |r| *
          (4 * hnorm 3 (PiF (actual r g y u)) + 26 * (wiener (y u) * hnorm 2 (y u))) := by
  have hrp : 0 < |r| := abs_pos.mpr hr
  have hc := c4_pos
  have hx := actual_adm h hu huT
  have hF := hx.PiF
  have hy := (h.sol.adm u hu huT).mz
  set F := PiF (actual r g y u) with hFdef
  have hF3' : MZ 3 F := ⟨hF3, hF.mean⟩
  have hy1 : Summable fun k => ‖y u k‖ := summable_wiener hy.inH
  obtain ⟨hgrad, hgradle⟩ := wiener_grad_le hF3'
  set C : Mode → ℝ := fun k => ∑' q, ‖y u q‖ * ‖y u (k - q)‖ with hC
  have hC0 : ∀ k, 0 ≤ C k := fun k =>
    tsum_nonneg fun q => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  obtain ⟨hC1, hCs⟩ := tonelli_convR (a := fun k => ‖y u k‖) (c := fun k => ‖y u k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hy1 hy1
  obtain ⟨hP1, hP2⟩ := product_estimate (σ := 2) (by norm_num) hy hy hy1 hy1
  simp only [absk_rpow_four] at hP1 hP2
  -- the two pieces of `|·|²B`
  set a : Mode → ℝ := fun k => absSq k * (absk k * ‖F k‖) with ha
  set c : Mode → ℝ := fun k => 2 * (absSq k * C k) with hcdef
  have ha0 : ∀ k, 0 ≤ a k := fun k =>
    mul_nonneg (absSq_nonneg k) (mul_nonneg (absk_nonneg k) (norm_nonneg _))
  have hc0 : ∀ k, 0 ≤ c k := fun k =>
    mul_nonneg (by norm_num) (mul_nonneg (absSq_nonneg k) (hC0 k))
  have hae : ∀ k, a k ^ 2 = sobWeight 3 k * ‖F k‖ ^ 2 := fun k => by
    show (absSq k * (absk k * ‖F k‖)) ^ 2 = _
    rw [sobWeight_three, ← absk_sq]
    ring
  have hce : ∀ k, c k ^ 2 = 4 * (absSq k ^ 2 * C k ^ 2) := fun k => by
    show (2 * (absSq k * C k)) ^ 2 = _
    ring
  have ha2 : Summable fun k => a k ^ 2 := by
    simp only [hae]
    exact hF3
  have hc2 : Summable fun k => c k ^ 2 := by
    simp only [hce]
    exact hP1.mul_left 4
  obtain ⟨hM1, hM2⟩ := sqrt_tsum_add_sq_le ha0 hc0 ha2 hc2
  have han : Real.sqrt (∑' k, a k ^ 2) = hnorm 3 F := by
    unfold hnorm
    exact congrArg Real.sqrt (tsum_congr hae)
  have hcn : Real.sqrt (∑' k, c k ^ 2) ≤ 8 * (wiener (y u) * hnorm 2 (y u)) := by
    have e : ∑' k, c k ^ 2 = 4 * ∑' k, absSq k ^ 2 * C k ^ 2 := by
      simp only [hce]
      exact tsum_mul_left
    rw [e, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    have e2 : (2 : ℝ) ^ ((2 : ℝ) - 1) = 2 := by norm_num
    rw [e2] at hP2
    nlinarith
  -- the majorant
  set B : Mode → ℝ := fun k => absk k * ‖F k‖ + 2 * C k with hBdef
  have hB0 : ∀ k, 0 ≤ B k := fun k =>
    add_nonneg (mul_nonneg (absk_nonneg k) (norm_nonneg _)) (mul_nonneg (by norm_num) (hC0 k))
  have hB1 : Summable B := hgrad.add (hC1.mul_left 2)
  have hBe : ∀ k, absSq k * B k = a k + c k := fun k => by
    simp only [hBdef, ha, hcdef]
    ring
  have hB2 : Summable fun k => (absSq k * B k) ^ 2 := by
    simp only [hBe]
    exact hM1
  have hBs : ∑' k, B k ≤ c4 * hnorm 3 F + 2 * wiener (y u) ^ 2 := by
    have e : ∑' k, B k = ∑' k, absk k * ‖F k‖ + 2 * ∑' k, C k := by
      rw [← tsum_mul_left]
      exact hgrad.tsum_add (hC1.mul_left 2)
    rw [e, hCs]
    have : wiener (y u) = ∑' k, ‖y u k‖ := rfl
    rw [this]
    nlinarith
  have hBn : Real.sqrt (∑' k, (absSq k * B k) ^ 2) ≤
      hnorm 3 F + 8 * (wiener (y u) * hnorm 2 (y u)) := by
    simp only [hBe]
    rw [← han]
    exact hM2.trans (add_le_add le_rfl hcn)
  obtain ⟨hI, hle⟩ := hnorm_one_kinN_of_loss_le (τ := τ) hr (f := fastRHS r g y u) (g := F) hB0
    hB1 hB2 (fun p => norm_fastRHS_le h hu huT p) (fastRHS_l2 h hu huT).1 hF.mz
  refine ⟨hI, hle.trans ?_⟩
  -- the arithmetic
  have hwF : wiener F ≤ c4 * hnorm 2 F := wiener_le hF.mz
  have hwy : wiener (y u) ≤ c4 * hnorm 2 (y u) := wiener_le hy
  have n1 := hnorm_nonneg 2 F
  have n2 := hnorm_nonneg 3 F
  have n3 := wiener_nonneg (y u)
  have n4 := hnorm_nonneg 2 (y u)
  have n5 := wiener_nonneg F
  have hw2 : wiener (y u) ^ 2 ≤ c4 * (wiener (y u) * hnorm 2 (y u)) := by nlinarith
  have s1 : wiener F * Real.sqrt (∑' k, (absSq k * B k) ^ 2) ≤
      c4 * hnorm 2 F * (hnorm 3 F + 8 * (wiener (y u) * hnorm 2 (y u))) :=
    mul_le_mul hwF hBn (Real.sqrt_nonneg _) (by positivity)
  have s2 : (∑' k, B k) * hnorm 2 F ≤
      (c4 * hnorm 3 F + 2 * (c4 * (wiener (y u) * hnorm 2 (y u)))) * hnorm 2 F :=
    mul_le_mul_of_nonneg_right (by linarith) n1
  have e : c4 * hnorm 2 F / |r| * (4 * hnorm 3 F + 26 * (wiener (y u) * hnorm 2 (y u))) =
      1 / |r| * (3 * (c4 * hnorm 2 F * (hnorm 3 F + 8 * (wiener (y u) * hnorm 2 (y u)))) +
        (c4 * hnorm 3 F + 2 * (c4 * (wiener (y u) * hnorm 2 (y u)))) * hnorm 2 F) := by
    field_simp
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-! ### The fast `H²` law -/

/-- The sup bound of `‖Q_{rt}(y,y)‖₁` on `[0,b]`. -/
private lemma exists_Qphase_bound_one (h : ActualSol μ φ r g y Ty) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc 0 b, InH 1 (Qphase (r * t) (y t) (y t)) ∧
      hnorm 1 (Qphase (r * t) (y t) (y t)) ≤ D := by
  obtain ⟨M, hM⟩ := h.sol.exists_bound hbT
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hc := c4_pos
  refine ⟨8 * c4 * max M 0 ^ 2, by positivity, fun t ht => ?_⟩
  have hy := (h.sol.adm t ht.1 (lt_lifespan ht.2 hbT)).mz
  obtain ⟨hI, hle⟩ := hnorm_Qm_one_bound (phaseM_bdd (r * t)) hy hy
  refine ⟨hI, hle.trans ?_⟩
  have h1 : hnorm 2 (y t) ≤ max M 0 := (hM t ht).trans (le_max_left _ _)
  have h2 : wiener (y t) ≤ c4 * max M 0 :=
    (wiener_le hy).trans (mul_le_mul_of_nonneg_left h1 hc.le)
  have h3 := mul_le_mul h2 h1 (hnorm_nonneg _ _) (by positivity)
  have e : hnorm 2 (y t) * wiener (y t) = wiener (y t) * hnorm 2 (y t) := mul_comm _ _
  rw [e]
  nlinarith

/-- **`F` is a heat pair at `σ = 2`** with force `−Π_F Q_{rt}(y,y)`. -/
theorem heatPair_fast_level_two (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) :
    HeatPair 2 0 b (fun t => PiF (actual r g y t))
      (fun t => -PiF (Qphase (r * t) (y t) (y t))) := by
  have h1 := heatPair_fast h (σ := 1) (Or.inr rfl) hb hbT
  refine ⟨fun t ht => (actual_adm h ht.1 (lt_lifespan ht.2 hbT)).inH.PiF, h1.mode, h1.force_cont,
    ?_⟩
  obtain ⟨D, hD0, hD⟩ := exists_Qphase_bound_one h hbT
  calc ∫⁻ t in Icc 0 b, hsE (2 - 1) (-PiF (Qphase (r * t) (y t) (y t)))
      ≤ ∫⁻ _ in Icc 0 b, ENNReal.ofReal (D ^ 2) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        obtain ⟨hI, hle⟩ := hD t ht
        have e1 : (2 : ℝ) - 1 = 1 := by norm_num
        rw [e1]
        have e : hsE 1 (-PiF (Qphase (r * t) (y t) (y t))) =
            hsE 1 (PiF (Qphase (r * t) (y t) (y t))) := by
          simp [hsE]
        rw [e, hsE_eq_ofReal hI.PiF]
        exact ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (hnorm_nonneg _ _) ((hnorm_PiF_le hI).trans hle) 2)
    _ < ∞ := by
        rw [setLIntegral_const, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- `F ∈ H³` at almost every time of `[s, t]`. -/
lemma ae_fast_three (h : ActualSol μ φ r g y Ty) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), InH 3 (PiF (actual r g y u)) := by
  have hP := (heatPair_fast_level_two h (hs.trans hst) ht).mono hs le_rfl
  have := hP.ae_inH hst
  have e : (2 : ℝ) + 1 = 3 := by norm_num
  rwa [e] at this

/-- `∫ ‖F‖₃² < ∞` on `[0, b]`. -/
private lemma lintegral_fast_three_lt_top (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) :
    ∫⁻ t in Icc 0 b, hsE 3 (PiF (actual r g y t)) < ∞ := by
  have hP := heatPair_fast_level_two h hb hbT
  have := (hP.dissipation_lt_top hb).trans_lt
    (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hP.force_l2⟩)
  have e : (2 : ℝ) + 1 = 3 := by norm_num
  rwa [e] at this

/-- `t ↦ ‖F t‖₃²` is integrable. -/
lemma intervalIntegrable_fast_three (h : ActualSol μ φ r g y Ty) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (fun u => fastNorm 3 r g y u ^ 2) volume s t := by
  have hP := (heatPair_fast_level_two h (hs.trans hst) ht).mono hs le_rfl
  have := hP.intervalIntegrable_dissipation hst
  have e : (2 : ℝ) + 1 = 3 := by norm_num
  rwa [e] at this

/-- **The fast `H²` law, integrated**: `∫ₛᵗ ‖F‖₃² ≤ ‖F s‖₂² + D²(t−s)` as soon as
`‖Q(y,y)‖₁ ≤ D` on `[s,t]`. -/
theorem fast_dissipation_le (h : ActualSol μ φ r g y Ty) {s t D : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) (hD : ∀ u ∈ Icc s t, hnorm 1 (Qphase (r * u) (y u) (y u)) ≤ D) :
    ∫ u in s..t, fastNorm 3 r g y u ^ 2 ≤ fastNorm 2 r g y s ^ 2 + D ^ 2 * (t - s) := by
  have hP := (heatPair_fast_level_two h (hs.trans hst) ht).mono hs le_rfl
  have hu0 : ∀ u ∈ Icc s t, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hs.trans hu.1, lt_lifespan hu.2 ht⟩
  have hp : ∀ᵐ u ∂(volume.restrict (Icc s t)),
      2 * pair 2 (PiF (actual r g y u)) (-PiF (Qphase (r * u) (y u) (y u))) ≤
        1 * hnorm 3 (PiF (actual r g y u)) ^ 2 + D ^ 2 := by
    filter_upwards [ae_fast_three h hs hst ht, ae_restrict_mem measurableSet_Icc] with u hF3 hu
    have hy := (h.sol.adm u (hu0 u hu).1 (hu0 u hu).2).mz
    obtain ⟨hI, -⟩ := hnorm_Qm_one_bound (phaseM_bdd (r * u)) hy hy
    have hI' : InH 1 (-PiF (Qphase (r * u) (y u) (y u))) := hI.PiF.neg
    have e1 : (2 : ℝ) + 1 = 3 := by norm_num
    have e2 : (2 : ℝ) - 1 = 1 := by norm_num
    have hl := (pair_le (σ := 2) (c := PiF (actual r g y u))
      (F := -PiF (Qphase (r * u) (y u) (y u))) (by rw [e1]; exact hF3) (by rw [e2]; exact hI')).2
    rw [e1, e2, hnorm_neg] at hl
    have hb1 : hnorm 1 (PiF (Qphase (r * u) (y u) (y u))) ≤ D :=
      (hnorm_PiF_le hI).trans (hD u hu)
    have hD0 : 0 ≤ D := (hnorm_nonneg _ _).trans hb1
    have hb2 := hnorm_nonneg 1 (PiF (Qphase (r * u) (y u) (y u)))
    have hb3 := hnorm_nonneg 3 (PiF (actual r g y u))
    have := le_abs_self (pair 2 (PiF (actual r g y u)) (-PiF (Qphase (r * u) (y u) (y u))))
    nlinarith [sq_nonneg (hnorm 3 (PiF (actual r g y u)) -
      hnorm 1 (PiF (Qphase (r * u) (y u) (y u)))),
      pow_le_pow_left₀ hb2 hb1 2]
  have hE := hP.energy_le (τ := 3) (θ := 1) (by norm_num) hst
    (R := fun _ => D ^ 2) intervalIntegrable_const hp
  rw [intervalIntegral.integral_const, smul_eq_mul] at hE
  have hF := hnorm_nonneg 2 (PiF (actual r g y t))
  simp only [fastNorm]
  nlinarith [sq_nonneg (hnorm 2 (PiF (actual r g y t)))]

/-- An a.e. affine bound by `‖F‖₃` is square-integrable in time. -/
theorem lintegral_hsE_one_lt_top (h : ActualSol μ φ r g y Ty) {b a c : ℝ} {f : ℝ → Field}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty)
    (hbd : ∀ u ∈ Icc 0 b, InH 3 (PiF (actual r g y u)) →
      InH 1 (f u) ∧ hnorm 1 (f u) ≤ a + c * fastNorm 3 r g y u) :
    ∫⁻ t in Icc 0 b, hsE 1 (f t) < ∞ := by
  have hle : ∀ᵐ t ∂(volume.restrict (Icc 0 b)), hsE 1 (f t) ≤
      ENNReal.ofReal (2 * a ^ 2) + ENNReal.ofReal (2 * c ^ 2) * hsE 3 (PiF (actual r g y t)) := by
    filter_upwards [ae_fast_three h le_rfl hb hbT, ae_restrict_mem measurableSet_Icc] with t hF3 ht
    obtain ⟨hI, hn⟩ := hbd t ht hF3
    rw [hsE_eq_ofReal hI, hsE_eq_ofReal hF3, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 := hnorm_nonneg 1 (f t)
    have h3 := hnorm_nonneg 3 (PiF (actual r g y t))
    simp only [fastNorm] at hn
    have h4 : hnorm 1 (f t) ^ 2 ≤ (a + c * hnorm 3 (PiF (actual r g y t))) ^ 2 :=
      pow_le_pow_left₀ h0 hn 2
    nlinarith [sq_nonneg (a - c * hnorm 3 (PiF (actual r g y t)))]
  refine (lintegral_mono_ae hle).trans_lt ?_
  rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    setLIntegral_const, Real.volume_Icc]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_fast_three_lt_top h hb hbT)⟩

end Quant

end OVNS

end
