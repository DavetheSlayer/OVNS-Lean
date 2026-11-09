import OddViscousNS.Closed.Forced.Laws
import OddViscousNS.Closed.CubicCont

/-!
# Kinetic cap, elementary shell comparisons, and continuity along forced heat solutions

* `Xr_le_J1r`, `Yr_le_J1r`, `Yr_le_hnorm_sq`: `X ≤ J₁`, `Y ≤ J₁` (`h(j) ≤ j`), `Y ≤ ‖w‖₂²`.
* `kinetic_cap`: along a forced heat solution with force `g`,
  `X(y t) ≤ max (X(y 0)) (‖g‖₂²)` — from `½X' = −J₁ + ⟨R g, y⟩ ≤ −X + ‖g‖₂ √X`, by the
  comparison argument (at a first time where `X` exceeds the cap, the integrand is `≤ 0`).
* Continuity on `Icc 0 b` (`ofReal b < T`) of `t ↦ J1r (y t)`, `Zr (y t)`,
  `cubic (rotF (r t) (y t))`, and the force pairings.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

namespace Forced

private lemma absSq_zero'' : absSq 0 = 0 := by simp [absSq]

private lemma hm_le_absSq' (k : Mode) : hm k ≤ absSq k := by
  unfold hm; rw [← nsq_cast]; exact hmet_upper _

private lemma norm_rotF_eq' (τ : ℝ) {w : Field} (hw : Adm 2 w) (k : Mode) :
    ‖rotF τ w k‖ = ‖w k‖ := by
  by_cases hk : k = 0
  · subst hk
    simp [rotF, rot, hel, hw.mean]
  · rw [show rotF τ w k = rot τ k (w k) from rfl, norm_rot, leray_of_perp hk (hw.sol k)]

theorem Xr_le_J1r {w : Field} (hw : Adm 2 w) : Xr w ≤ J1r w := by
  refine (summable_X hw).tsum_le_tsum (fun k => ?_) (summable_J1 hw)
  by_cases hk : k = 0
  · simp [hk, absSq_zero'']
  · simp only [hk, ↓reduceIte]
    nlinarith [one_le_absSq hk, sq_nonneg ‖w k‖]

theorem Yr_le_J1r {w : Field} (hw : Adm 2 w) : Yr w ≤ J1r w :=
  (summable_Y hw).tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (hm_le_absSq' k)
    (sq_nonneg _)) (summable_J1 hw)

theorem Yr_le_hnorm_sq {w : Field} (hw : Adm 2 w) : Yr w ≤ hnorm 2 w ^ 2 := by
  rw [hnorm_sq hw.inH]
  refine (summable_Y hw).tsum_le_tsum (fun k => ?_) (show Summable _ from hw.inH)
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [sobWeight_two]
  by_cases hk : k = 0
  · subst hk; have := hm_le_absSq' 0; rw [absSq_zero''] at this ⊢; simpa using this
  · have h1 := one_le_absSq hk
    have h2 := hm_le_absSq' k
    nlinarith

theorem Xr_rotF (τ : ℝ) {w : Field} (hw : Adm 2 w) : Xr (rotF τ w) = Xr w := by
  unfold Xr
  simp_rw [norm_rotF_eq' τ hw]

theorem Yr_rotF (τ : ℝ) {w : Field} (hw : Adm 2 w) : Yr (rotF τ w) = Yr w := by
  unfold Yr
  simp_rw [norm_rotF_eq' τ hw]

theorem Zr_rotF (τ : ℝ) {w : Field} (hw : Adm 2 w) : Zr (rotF τ w) = Zr w := by
  unfold Zr
  simp_rw [norm_rotF_eq' τ hw]

theorem J1r_rotF (τ : ℝ) {w : Field} (hw : Adm 2 w) : J1r (rotF τ w) = J1r w := by
  unfold J1r
  simp_rw [norm_rotF_eq' τ hw]

variable {r : ℝ} {T : ℝ≥0∞} {y : ℝ → Field} {g : Field}

private lemma heatPair_k (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    HeatPair 2 0 b y (fun t => filtG r 0 g t - filtN r 0 t (y t) (y t)) :=
  hy.heatPair (majorized_filtN r 0) (goodForce_filtG r 0 hg) hb hbT

private lemma lt_T' {t b : ℝ} (htb : t ≤ b) (hbT : ENNReal.ofReal b < T) :
    ENNReal.ofReal t < T :=
  lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htb) hbT

private noncomputable def ωZ' : Mode → ℝ := fun k => absSq k * hmet (nsq k)

private noncomputable def ωJ' : Mode → ℝ := fun k => absSq k

private lemma weightLE2_Z' : WeightLE2 ωZ' := by
  refine ⟨fun k => mul_nonneg (absSq_nonneg k) (weightLE2_Y.nonneg k), by simp [ωZ', absSq],
    fun k => ?_⟩
  by_cases hk : k = 0
  · subst hk; simp [ωZ', absSq, sobWeight]
  · rw [sobWeight_two, sq]
    exact mul_le_mul_of_nonneg_left (by rw [← nsq_cast]; exact hmet_upper _) (absSq_nonneg k)

private lemma weightLE2_J' : WeightLE2 ωJ' := by
  refine ⟨absSq_nonneg, by simp [ωJ', absSq], fun k => ?_⟩
  by_cases hk : k = 0
  · subst hk; simp [ωJ', absSq, sobWeight]
  · rw [sobWeight_two]
    simp only [ωJ']
    nlinarith [one_le_absSq hk]

theorem continuousOn_J1_f (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    ContinuousOn (fun t => J1r (y t)) (Icc 0 b) :=
  (heatPair_k hg hy hb hbT).continuousOn_wE weightLE2_J' hb

theorem continuousOn_Z_f (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    ContinuousOn (fun t => Zr (y t)) (Icc 0 b) :=
  (heatPair_k hg hy hb hbT).continuousOn_wE weightLE2_Z' hb

theorem continuousOn_cubic_f (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    ContinuousOn (fun t => cubic (rotF (r * t) (y t))) (Icc 0 b) := by
  have _ := hg; have _ := hb
  exact continuousOn_cubic_rotF (fun _ ht => hy.adm _ ht.1 (lt_T' ht.2 hbT)) fun t₀ ht₀ =>
    (hy.cont t₀ ht₀.1 (lt_T' ht₀.2 hbT)).mono_left (nhdsWithin_mono _ Icc_subset_Ici_self)

/-! ### Continuity of the force pairings -/

private lemma abs_re_inner_le' (a b : V3) : |(inner ℂ a b).re| ≤ ‖a‖ * ‖b‖ :=
  (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)

private lemma cs_tsum'' {a b : Mode → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (ha2 : Summable fun k => a k ^ 2) (hb2 : Summable fun k => b k ^ 2) :
    Summable (fun k => a k * b k) ∧
      ∑' k, a k * b k ≤ Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, b k ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have ha2' : Summable fun k => a k ^ (2 : ℝ) := by simpa only [Real.rpow_two] using ha2
  have hb2' : Summable fun k => b k ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hb2
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq ha hb ha2' hb2'
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using h

/-- Summability and the bound `|⟨c, ω F⟩| ≤ ‖c‖₂ ‖F‖₁` for weights `0 ≤ ω ≤ |k|²`. -/
private lemma pair_core' {ω : Mode → ℝ} (h0 : ∀ k, 0 ≤ ω k) (hle : ∀ k, ω k ≤ absSq k)
    {c F : Field} (hc : InH 2 c) (hF : InH 1 F) :
    Summable (fun k => ω k * (inner ℂ (c k) (F k)).re) ∧
      |wPair ω c F| ≤ hnorm 2 c * hnorm 1 F := by
  set a : Mode → ℝ := fun k => absSq k * ‖c k‖ with ha
  set b : Mode → ℝ := fun k => Real.sqrt (sobWeight 1 k) * ‖F k‖ with hb
  have ha0 : ∀ k, 0 ≤ a k := fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _)
  have hb0 : ∀ k, 0 ≤ b k := fun k => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have ha2e : ∀ k, a k ^ 2 = sobWeight 2 k * ‖c k‖ ^ 2 := fun k => by
    simp only [ha]; rw [sobWeight_two]; ring
  have hb2e : ∀ k, b k ^ 2 = sobWeight 1 k * ‖F k‖ ^ 2 := fun k => by
    simp only [hb]; rw [mul_pow, Real.sq_sqrt (sobWeight_nonneg _ _)]
  have ha2 : Summable fun k => a k ^ 2 := (show Summable _ from hc).congr fun k => (ha2e k).symm
  have hb2 : Summable fun k => b k ^ 2 := (show Summable _ from hF).congr fun k => (hb2e k).symm
  obtain ⟨hs, hle'⟩ := cs_tsum'' ha0 hb0 ha2 hb2
  have hab : ∀ k, |ω k * (inner ℂ (c k) (F k)).re| ≤ a k * b k := fun k => by
    by_cases hk : k = 0
    · subst hk
      have : ω 0 = 0 := le_antisymm (by simpa [absSq_zero''] using hle 0) (h0 0)
      rw [this, zero_mul, abs_zero]; exact mul_nonneg (ha0 0) (hb0 0)
    · have h1 : 1 ≤ Real.sqrt (sobWeight 1 k) := by
        rw [Real.one_le_sqrt]
        simp only [sobWeight, hk, ↓reduceIte]
        exact Real.one_le_rpow (one_le_absk hk) (by norm_num)
      rw [abs_mul, abs_of_nonneg (h0 k)]
      calc ω k * |(inner ℂ (c k) (F k)).re| ≤ absSq k * (‖c k‖ * ‖F k‖) :=
            mul_le_mul (hle k) (abs_re_inner_le' _ _) (abs_nonneg _) (absSq_nonneg k)
        _ ≤ absSq k * (‖c k‖ * (Real.sqrt (sobWeight 1 k) * ‖F k‖)) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_left (norm_nonneg (F k)) h1) (norm_nonneg _)) (absSq_nonneg k)
        _ = a k * b k := by simp only [ha, hb]; ring
  have hs' : Summable fun k => ω k * (inner ℂ (c k) (F k)).re :=
    Summable.of_norm_bounded hs fun k => by rw [Real.norm_eq_abs]; exact hab k
  refine ⟨hs', ?_⟩
  have hn2 : hnorm 2 c = Real.sqrt (∑' k, a k ^ 2) := by
    unfold hnorm; congr 1; exact tsum_congr fun k => (ha2e k).symm
  have hn1 : hnorm 1 F = Real.sqrt (∑' k, b k ^ 2) := by
    unfold hnorm; congr 1; exact tsum_congr fun k => (hb2e k).symm
  rw [hn2, hn1]
  unfold wPair
  calc _ ≤ ∑' k, |ω k * (inner ℂ (c k) (F k)).re| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs'.norm
    _ ≤ ∑' k, a k * b k := hs'.abs.tsum_le_tsum hab hs
    _ ≤ _ := hle'

private lemma wPair_sub_left (ω : Mode → ℝ) (c₁ c₂ F : Field)
    (h₁ : Summable fun k => ω k * (inner ℂ (c₁ k) (F k)).re)
    (h₂ : Summable fun k => ω k * (inner ℂ (c₂ k) (F k)).re) :
    wPair ω (c₁ - c₂) F = wPair ω c₁ F - wPair ω c₂ F := by
  unfold wPair
  rw [← h₁.tsum_sub h₂]
  congr 1
  funext k
  simp [mul_sub]

private lemma wPair_sub_right (ω : Mode → ℝ) (c F₁ F₂ : Field)
    (h₁ : Summable fun k => ω k * (inner ℂ (c k) (F₁ k)).re)
    (h₂ : Summable fun k => ω k * (inner ℂ (c k) (F₂ k)).re) :
    wPair ω c (F₁ - F₂) = wPair ω c F₁ - wPair ω c F₂ := by
  unfold wPair
  rw [← h₁.tsum_sub h₂]
  congr 1
  funext k
  simp [mul_sub]

private lemma continuousOn_pair_gen {ω : Mode → ℝ} (h0 : ∀ k, 0 ≤ ω k)
    (hle : ∀ k, ω k ≤ absSq k) (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y)
    {b : ℝ} (hbT : ENNReal.ofReal b < T) :
    ContinuousOn (fun t => wPair ω (y t) (filtG r 0 g t)) (Icc 0 b) := by
  intro t₀ ht₀
  have hG := goodForce_filtG r 0 hg
  set G := filtG r 0 g
  have hy₀ : Adm 2 (y t₀) := hy.adm t₀ ht₀.1 (lt_T' ht₀.2 hbT)
  have hbound : ∀ t ∈ Icc 0 b, |wPair ω (y t) (G t) - wPair ω (y t₀) (G t₀)| ≤
      hnorm 2 (y t - y t₀) * hnorm 1 g + hnorm 2 (y t₀) * hnorm 1 (G t - G t₀) := by
    intro t ht
    have hyt : Adm 2 (y t) := hy.adm t ht.1 (lt_T' ht.2 hbT)
    have hGt := (hG.adm t).inH
    have hG₀ := (hG.adm t₀).inH
    have e : wPair ω (y t) (G t) - wPair ω (y t₀) (G t₀) =
        wPair ω (y t - y t₀) (G t) + wPair ω (y t₀) (G t - G t₀) := by
      rw [wPair_sub_left ω _ _ _ (pair_core' h0 hle hyt.inH hGt).1
          (pair_core' h0 hle hy₀.inH hGt).1,
        wPair_sub_right ω _ _ _ (pair_core' h0 hle hy₀.inH hGt).1
          (pair_core' h0 hle hy₀.inH hG₀).1]
      ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ (pair_core' h0 hle hy₀.inH (hGt.sub hG₀)).2)
    refine (pair_core' h0 hle (hyt.inH.sub hy₀.inH) hGt).2.trans ?_
    exact mul_le_mul_of_nonneg_left (hG.bd t) (hnorm_nonneg _ _)
  have h1 : Filter.Tendsto (fun t => hnorm 2 (y t - y t₀)) (nhdsWithin t₀ (Icc 0 b))
      (nhds 0) :=
    (hy.cont t₀ ht₀.1 (lt_T' ht₀.2 hbT)).mono_left (nhdsWithin_mono _ Icc_subset_Ici_self)
  have h2 : Filter.Tendsto (fun t => hnorm 1 (G t - G t₀)) (nhdsWithin t₀ (Icc 0 b))
      (nhds 0) := (hG.cont t₀).mono_left nhdsWithin_le_nhds
  have h3 := (h1.mul_const (hnorm 1 g)).add (h2.const_mul (hnorm 2 (y t₀)))
  simp only [zero_mul, mul_zero, add_zero] at h3
  show Filter.Tendsto _ _ _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ h3
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Real.norm_eq_abs]
  exact hbound t ht

theorem continuousOn_pairX_f (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    ContinuousOn (fun t => wPair ωX (y t) (filtG r 0 g t)) (Icc 0 b) := by
  have _ := hb
  refine continuousOn_pair_gen weightLE2_X.nonneg (fun k => ?_) hg hy hbT
  by_cases hk : k = 0
  · subst hk; simp [ωX, absSq_zero'']
  · simp only [ωX, hk, ↓reduceIte]; exact one_le_absSq hk

theorem continuousOn_pairY_f (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    ContinuousOn (fun t => wPair ωY (y t) (filtG r 0 g t)) (Icc 0 b) := by
  have _ := hb
  exact continuousOn_pair_gen weightLE2_Y.nonneg (fun k => hm_le_absSq' k) hg hy hbT

private lemma wDiss_X_eq' (u : Field) : wDiss ωX u = J1r u := by
  unfold wDiss J1r
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0 <;> simp [ωX, hk, absSq]

/-- The kinetic cap `X(t) ≤ max(X(0), ‖g‖₂²)`. -/
theorem kinetic_cap (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {t : ℝ}
    (ht : 0 ≤ t) (htT : ENNReal.ofReal t < T) :
    Xr (y t) ≤ max (Xr (y 0)) (hnorm 2 g ^ 2) := by
  set K := max (Xr (y 0)) (hnorm 2 g ^ 2) with hK
  by_contra hcon
  push Not at hcon
  have hX : ContinuousOn (fun u => Xr (y u)) (Icc 0 t) :=
    (continuousOn_X_f hg hy ht htT).congr fun u _ => (wE_X (y u)).symm
  set S := Icc 0 t ∩ (fun u => Xr (y u)) ⁻¹' Iic K with hS
  have hSc : IsCompact S :=
    isCompact_Icc.of_isClosed_subset (hX.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
      inter_subset_left
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, ht⟩, show Xr (y 0) ≤ K from le_max_left _ _⟩
  obtain ⟨σ, hσS, hσmax⟩ := hSc.exists_isGreatest ⟨0, h0S⟩
  have hσt : σ < t := by
    refine lt_of_le_of_ne hσS.1.2 fun h => ?_
    have := hσS.2; rw [h] at this
    exact absurd (show Xr (y t) ≤ K from this) (not_le.2 hcon)
  have hσ0 : 0 ≤ σ := hσS.1.1
  have habove : ∀ u ∈ Ioo σ t, K < Xr (y u) := fun u hu => by
    by_contra h
    push Not at h
    have : u ∈ S := ⟨⟨hσ0.trans hu.1.le, hu.2.le⟩, h⟩
    exact absurd (hσmax this) (not_le.2 hu.1)
  have law := X_law_f hg hy hσ0 hσt.le htT
  simp only [wDiss_X_eq', wE_X] at law
  have sub : uIcc σ t ⊆ Icc 0 t := by rw [uIcc_of_le hσt.le]; exact Icc_subset_Icc hσ0 le_rfl
  have iJ : IntervalIntegrable (fun u => J1r (y u)) volume σ t :=
    ((continuousOn_J1_f hg hy ht htT).mono sub).intervalIntegrable
  have iP : IntervalIntegrable (fun u => wPair ωX (y u) (filtG r 0 g u)) volume σ t :=
    ((continuousOn_pairX_f hg hy ht htT).mono sub).intervalIntegrable
  have hint : ∫ u in σ..t, wPair ωX (y u) (filtG r 0 g u) ≤ ∫ u in σ..t, J1r (y u) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hσt.le iP iJ fun u hu => ?_
    have hu0 : 0 ≤ u := hσ0.trans hu.1.le
    have hyu : Adm 2 (y u) := hy.adm u hu0 (lt_T' hu.2.le htT)
    have hP := force_pair_X_le (-(r * (u + 0))) hg hyu
    have hXJ := Xr_le_J1r hyu
    have hKu := habove u hu
    have hf0 := hnorm_nonneg 2 g
    have hfX : hnorm 2 g ≤ Real.sqrt (Xr (y u)) :=
      Real.le_sqrt_of_sq_le (le_trans (le_max_right _ _) hKu.le)
    have hsq := Real.mul_self_sqrt (Xr_nonneg hyu)
    have : hnorm 2 g * Real.sqrt (Xr (y u)) ≤ Xr (y u) := by
      nlinarith [Real.sqrt_nonneg (Xr (y u))]
    exact (le_abs_self _).trans (hP.trans (this.trans hXJ))
  have hσK : Xr (y σ) ≤ K := hσS.2
  change Xr (y t) + 2 * ∫ u in σ..t, J1r (y u) =
    Xr (y σ) + 2 * ∫ u in σ..t, wPair ωX (y u) (filtG r 0 g u) at law
  linarith

end Forced

end OVNS
