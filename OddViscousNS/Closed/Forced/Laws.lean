import OddViscousNS.Closed.Forced.Defs
import OddViscousNS.Closed.XYode
import OddViscousNS.Closed.CubicFilter
import OddViscousNS.Closed.CubicCont

/-!
# Forced energy laws and force bounds

For a heat solution `y` of the forced filtered system `y' = −Ay − Q_{rt}(y,y) + R(−rt)g`
(`IsHeatSol (filtN r 0) (filtG r 0 g) T y`), on `0 ≤ s ≤ t < T`:
`X(y t) + 2∫ J₁(y) = X(y s) + 2∫ ⟨R(−ru)g, y u⟩`, and
`Y(y t) + 2∫ Z(y) = Y(y s) − 2∫ cubic(R(ru) y u) + 2∫ ⟨R(−ru)g, h(A) y u⟩`.
The force pairings are bounded by `‖g‖₂ √X` (`h_k ≤ |k|²`, `|k|⁻⁴ ≤ 1`) and the mixed pairing
`⟨g, (rI + m h(A)) w⟩` by `‖g‖₂ √(N²)`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

namespace Forced

variable {r : ℝ} {T : ℝ≥0∞} {y : ℝ → Field} {g : Field}

private lemma lt_of_mem' {s t u : ℝ} (hst : s ≤ t) (ht : ENNReal.ofReal t < T)
    (hu : u ∈ uIcc s t) : ENNReal.ofReal u < T := by
  rw [uIcc_of_le hst] at hu
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) ht

private lemma heatPair_f (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    HeatPair 2 0 b y (fun t => filtG r 0 g t - filtN r 0 t (y t) (y t)) :=
  hy.heatPair (majorized_filtN r 0) (goodForce_filtG r 0 hg) hb hbT

private lemma abs_re_inner_le (a b : V3) : |(inner ℂ a b).re| ≤ ‖a‖ * ‖b‖ :=
  (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)

private lemma absSq_zero' : absSq 0 = 0 := by simp [absSq]

private lemma hm_le_absSq (k : Mode) : hm k ≤ absSq k := by
  unfold hm; rw [← nsq_cast]; exact hmet_upper _

private lemma hm_nonneg' (k : Mode) : 0 ≤ hm k := weightLE2_Y.nonneg k

private lemma ωX_le (k : Mode) : ωX k ≤ absSq k := by
  by_cases hk : k = 0
  · subst hk; simp [ωX, absSq_zero']
  · simp only [ωX, hk, ↓reduceIte]; exact one_le_absSq hk

private lemma summable_pair {ω : Mode → ℝ} (h0 : ∀ k, 0 ≤ ω k) (hle : ∀ k, ω k ≤ absSq k)
    {c F : Field} (hc : InH 2 c) (hF : InH 0 F) :
    Summable fun k => ω k * (inner ℂ (c k) (F k)).re := by
  refine Summable.of_norm_bounded ((show Summable _ from hc).add (show Summable _ from hF))
    fun k => ?_
  have hre := abs_re_inner_le (c k) (F k)
  by_cases hk : k = 0
  · subst hk
    have : ω 0 = 0 := le_antisymm (by simpa [absSq_zero'] using hle 0) (h0 0)
    simp only [this, zero_mul, norm_zero]
    exact add_nonneg (mul_nonneg (sobWeight_nonneg _ _) (sq_nonneg _))
      (mul_nonneg (sobWeight_nonneg _ _) (sq_nonneg _))
  · have hs0 : sobWeight 0 k = 1 := by simp [sobWeight, hk]
    rw [sobWeight_two, hs0, Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 k)]
    have h1 : ω k * |(inner ℂ (c k) (F k)).re| ≤ absSq k * (‖c k‖ * ‖F k‖) :=
      mul_le_mul (hle k) hre (abs_nonneg _) (absSq_nonneg k)
    nlinarith [sq_nonneg (absSq k * ‖c k‖ - ‖F k‖)]

private lemma wPair_sub' (ω : Mode → ℝ) (c F₁ F₂ : Field)
    (h₁ : Summable fun k => ω k * (inner ℂ (c k) (F₁ k)).re)
    (h₂ : Summable fun k => ω k * (inner ℂ (c k) (F₂ k)).re) :
    wPair ω c (F₁ - F₂) = wPair ω c F₁ - wPair ω c F₂ := by
  unfold wPair
  rw [← h₁.tsum_sub h₂]
  congr 1
  funext k
  simp [mul_sub]

private lemma cs_tsum' {a b : Mode → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
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

private lemma cs_bound {θ a b : Mode → ℝ} {c F : Field} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (ha2 : Summable fun k => a k ^ 2) (hb2 : Summable fun k => b k ^ 2)
    (hab : ∀ k, |θ k * (inner ℂ (c k) (F k)).re| ≤ a k * b k) :
    |∑' k, θ k * (inner ℂ (c k) (F k)).re| ≤
      Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, b k ^ 2) := by
  obtain ⟨hs, hle⟩ := cs_tsum' ha hb ha2 hb2
  have hs' : Summable fun k => θ k * (inner ℂ (c k) (F k)).re :=
    Summable.of_norm_bounded hs fun k => by rw [Real.norm_eq_abs]; exact hab k
  calc _ ≤ ∑' k, |θ k * (inner ℂ (c k) (F k)).re| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs'.norm
    _ ≤ ∑' k, a k * b k := hs'.abs.tsum_le_tsum hab hs
    _ ≤ _ := hle

private lemma summable_X {w : Field} (hw : InH 2 w) :
    Summable fun k : Mode => if k = 0 then 0 else ‖w k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (show Summable _ from hw)
  · split_ifs <;> positivity
  · by_cases hk : k = 0
    · simp [hk, sobWeight]
    · simp only [hk, ↓reduceIte, sobWeight_two]
      have h1 := one_le_absSq hk
      have : 1 ≤ absSq k ^ 2 := one_le_pow₀ h1
      nlinarith [sq_nonneg ‖w k‖]

private lemma force_core (τ : ℝ) (hg : Adm 2 g) {w : Field} {θ β : Mode → ℝ} (hθ0 : θ 0 = 0)
    (hθ : ∀ k, k ≠ 0 → |θ k| ≤ absSq k * β k) (hβ : ∀ k, 0 ≤ β k)
    (hb2 : Summable fun k => (β k * ‖w k‖) ^ 2) :
    |∑' k, θ k * (inner ℂ (w k) (rotF τ g k)).re| ≤
      hnorm 2 g * Real.sqrt (∑' k, (β k * ‖w k‖) ^ 2) := by
  have ha2 : Summable fun k => (absSq k * ‖g k‖) ^ 2 := by
    refine (show Summable _ from hg.inH).congr fun k => ?_
    rw [sobWeight_two]; ring
  have hn : hnorm 2 g = Real.sqrt (∑' k, (absSq k * ‖g k‖) ^ 2) := by
    unfold hnorm; congr 1; exact tsum_congr fun k => by rw [sobWeight_two]; ring
  rw [hn]
  refine cs_bound (fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _))
    (fun k => mul_nonneg (hβ k) (norm_nonneg _)) ha2 hb2 fun k => ?_
  by_cases hk : k = 0
  · subst hk; rw [hθ0]; simp only [zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg (absSq_nonneg _) (norm_nonneg _))
      (mul_nonneg (hβ _) (norm_nonneg _))
  · have hn' : ‖rotF τ g k‖ = ‖g k‖ := by
      rw [show rotF τ g k = rot τ k (g k) from rfl, norm_rot, leray_of_perp hk (hg.sol k)]
    have hre := abs_re_inner_le (w k) (rotF τ g k)
    rw [hn'] at hre
    rw [abs_mul]
    calc |θ k| * |(inner ℂ (w k) (rotF τ g k)).re| ≤ (absSq k * β k) * (‖w k‖ * ‖g k‖) :=
          mul_le_mul (hθ k hk) hre (abs_nonneg _)
            (mul_nonneg (absSq_nonneg k) (hβ k))
      _ = _ := by ring


private lemma pair_split {ω : Mode → ℝ} (h0 : ∀ k, 0 ≤ ω k) (hle : ∀ k, ω k ≤ absSq k)
    (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < T) :
    wPair ω (y u) (filtG r 0 g u - filtN r 0 u (y u) (y u)) =
      wPair ω (y u) (filtG r 0 g u) - wPair ω (y u) (Qphase (r * u) (y u) (y u)) := by
  have hya := hy.adm u hu huT
  have hQ := ((majorized_filtN r 0).hnorm_zero_le u hya.mz hya.mz).1
  have hG : InH 0 (filtG r 0 g u) := ((goodForce_filtG r 0 hg).adm u).inH.mono (by norm_num)
  rw [wPair_sub' ω _ _ _ (summable_pair h0 hle hya.inH hG) (summable_pair h0 hle hya.inH hQ)]
  simp only [filtN, add_zero]

theorem X_law_f (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    wE ωX (y t) + 2 * ∫ u in s..t, wDiss ωX (y u) =
      wE ωX (y s) + 2 * ∫ u in s..t, wPair ωX (y u) (filtG r 0 g u) := by
  have h := (heatPair_f hg hy (hs.trans hst) ht).weighted_energy_identity weightLE2_X hs hst le_rfl
  have h0 : ∫ u in s..t, wPair ωX (y u) (filtG r 0 g u - filtN r 0 u (y u) (y u)) =
      ∫ u in s..t, wPair ωX (y u) (filtG r 0 g u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu' := hu; rw [uIcc_of_le hst] at hu'
    have hu0 : 0 ≤ u := hs.trans hu'.1
    have huT := lt_of_mem' hst ht hu
    rw [pair_split weightLE2_X.nonneg ωX_le hg hy hu0 huT,
      wPair_X_Qphase _ (hy.adm u hu0 huT), sub_zero]
  rw [h0] at h; linarith

theorem Y_law_f (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    wE ωY (y t) + 2 * ∫ u in s..t, wDiss ωY (y u) =
      wE ωY (y s) - 2 * (∫ u in s..t, cubic (rotF (r * u) (y u))) +
        2 * ∫ u in s..t, wPair ωY (y u) (filtG r 0 g u) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hP := heatPair_f hg hy ht0 ht
  have h := hP.weighted_energy_identity weightLE2_Y hs hst le_rfl
  have hsub : uIcc s t ⊆ uIcc 0 t := uIcc_subset_uIcc (by
    rw [uIcc_of_le ht0]; exact ⟨hs, hst⟩) right_mem_uIcc
  have htot := (hP.intervalIntegrable_wPair weightLE2_Y ht0).mono_set hsub
  have hcub : IntervalIntegrable (fun u => cubic (rotF (r * u) (y u))) volume s t := by
    have hc := continuousOn_cubic_rotF (r := r) (y := y) (b := t)
      (fun u hu => hy.adm u hu.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) ht))
      (fun u hu => (hy.cont u hu.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) ht)).mono_left
        (nhdsWithin_mono _ Icc_subset_Ici_self))
    rw [← uIcc_of_le ht0] at hc
    exact (hc.intervalIntegrable).mono_set hsub
  have h0 : ∫ u in s..t, wPair ωY (y u) (filtG r 0 g u) =
      (∫ u in s..t, wPair ωY (y u) (filtG r 0 g u - filtN r 0 u (y u) (y u))) +
        ∫ u in s..t, cubic (rotF (r * u) (y u)) := by
    refine (intervalIntegral.integral_congr fun u hu => ?_).trans
      (intervalIntegral.integral_add htot hcub)
    have hu' := hu; rw [uIcc_of_le hst] at hu'
    have hu0 : 0 ≤ u := hs.trans hu'.1
    have huT := lt_of_mem' hst ht hu
    rw [pair_split weightLE2_Y.nonneg (fun k => hm_le_absSq k) hg hy hu0 huT,
      wPair_Y_Qphase _ (hy.adm u hu0 huT)]
    ring
  rw [h0]; linarith


theorem continuousOn_X_f (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) : ContinuousOn (fun t => wE ωX (y t)) (Icc 0 b) := by
  exact (heatPair_f hg hy hb hbT).continuousOn_wE weightLE2_X hb

theorem continuousOn_Y_f (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) : ContinuousOn (fun t => wE ωY (y t)) (Icc 0 b) := by
  exact (heatPair_f hg hy hb hbT).continuousOn_wE weightLE2_Y hb

/-- `|⟨R(τ)g, w⟩| ≤ ‖g‖₂ √X(w)`. -/
theorem force_pair_X_le (τ : ℝ) (hg : Adm 2 g) {w : Field} (hw : Adm 2 w) :
    |wPair ωX w (rotF τ g)| ≤ hnorm 2 g * Real.sqrt (Xr w) := by
  have hb2 := summable_X hw.inH
  have h := force_core τ hg (θ := ωX) (β := ωX) (w := w) (by simp [ωX])
    (fun k hk => by simp [ωX, hk, one_le_absSq hk]) weightLE2_X.nonneg
    (hb2.congr fun k => by by_cases hk : k = 0 <;> simp [ωX, hk])
  have he : ∑' k, (ωX k * ‖w k‖) ^ 2 = Xr w :=
    tsum_congr fun k => by by_cases hk : k = 0 <;> simp [ωX, hk]
  rw [he] at h
  exact h

/-- `|⟨R(τ)g, h(A)w⟩| ≤ ‖g‖₂ √X(w)`. -/
theorem force_pair_Y_le (τ : ℝ) (hg : Adm 2 g) {w : Field} (hw : Adm 2 w) :
    |wPair ωY w (rotF τ g)| ≤ hnorm 2 g * Real.sqrt (Xr w) := by
  have hb2 := summable_X hw.inH
  set β : Mode → ℝ := fun k => if k = 0 then 0 else hm k / absSq k with hβdef
  have hβ0 : ∀ k, 0 ≤ β k := fun k => by
    simp only [hβdef]; split_ifs
    · exact le_rfl
    · exact div_nonneg (hm_nonneg' k) (absSq_nonneg k)
  have hbb : ∀ k, (β k * ‖w k‖) ^ 2 ≤ if k = 0 then 0 else ‖w k‖ ^ 2 := fun k => by
    by_cases hk : k = 0
    · simp [hβdef, hk]
    · simp only [hβdef, hk, ↓reduceIte]
      have hA := one_le_absSq hk
      have h1 : hm k / absSq k ≤ 1 := (div_le_one (by linarith)).2 (hm_le_absSq k)
      have h2 : 0 ≤ hm k / absSq k := div_nonneg (hm_nonneg' k) (absSq_nonneg k)
      rw [mul_pow]
      have : (hm k / absSq k) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg ‖w k‖]
  have hs2 : Summable fun k => (β k * ‖w k‖) ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hbb hb2
  have h := force_core τ hg (θ := ωY) (β := β) (w := w) weightLE2_Y.zero
    (fun k hk => by
      simp only [hβdef, hk, ↓reduceIte]
      rw [abs_of_nonneg (weightLE2_Y.nonneg k), mul_div_cancel₀ _ (by
        linarith [one_le_absSq hk])]
      exact le_rfl) hβ0 hs2
  refine h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (hnorm_nonneg _ _))
  exact hs2.tsum_le_tsum hbb hb2

/-- `|⟨R(τ)g, (rI + m h(A)) w⟩| ≤ ‖g‖₂ √(N²(r,m;w))`. -/
theorem force_pair_N_le (τ : ℝ) (hg : Adm 2 g) {w : Field} (hw : Adm 2 w) {r m : ℝ} (hr : 0 ≤ r)
    (hm : 0 ≤ m) :
    |r * wPair ωX w (rotF τ g) + m * wPair ωY w (rotF τ g)| ≤
      hnorm 2 g * Real.sqrt (Nsq r m w) := by
  have hb2 := summable_X hw.inH
  have hG : InH 0 (rotF τ g) := (hg.rotF τ).inH.mono (by norm_num)
  have sX := summable_pair weightLE2_X.nonneg ωX_le hw.inH hG
  have sY := summable_pair weightLE2_Y.nonneg (fun k => hm_le_absSq k) hw.inH hG
  have hsum : r * wPair ωX w (rotF τ g) + m * wPair ωY w (rotF τ g) =
      ∑' k, (r * ωX k + m * ωY k) * (inner ℂ (w k) (rotF τ g k)).re := by
    unfold wPair
    rw [← tsum_mul_left, ← tsum_mul_left, ← (sX.mul_left r).tsum_add (sY.mul_left m)]
    exact tsum_congr fun k => by ring
  rw [hsum]
  set β : Mode → ℝ := fun k => if k = 0 then 0 else (r + m * OVNS.hm k) / absSq k with hβdef
  have hβ0 : ∀ k, 0 ≤ β k := fun k => by
    simp only [hβdef]; split_ifs
    · exact le_rfl
    · exact div_nonneg (by nlinarith [hm_nonneg' k]) (absSq_nonneg k)
  have hbb : ∀ k, (β k * ‖w k‖) ^ 2 ≤ (r + m) ^ 2 * if k = 0 then 0 else ‖w k‖ ^ 2 :=
    fun k => by
    by_cases hk : k = 0
    · simp [hβdef, hk]
    · simp only [hβdef, hk, ↓reduceIte]
      have hA := one_le_absSq hk
      have hh := hm_le_absSq k
      have hh0 := hm_nonneg' k
      have h1 : (r + m * OVNS.hm k) / absSq k ≤ r + m :=
        (div_le_iff₀ (by linarith)).2 (by nlinarith)
      have h2 : 0 ≤ (r + m * OVNS.hm k) / absSq k := div_nonneg (by nlinarith) (by linarith)
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h2 h1 2) (sq_nonneg _)
  have hs2 : Summable fun k => (β k * ‖w k‖) ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hbb (hb2.mul_left _)
  have h := force_core τ hg (θ := fun k => r * ωX k + m * ωY k) (β := β) (w := w)
    (by simp [ωX, weightLE2_Y.zero])
    (fun k hk => by
      simp only [hβdef, hk, ↓reduceIte, ωX]
      have hA := one_le_absSq hk
      rw [mul_div_cancel₀ _ (by linarith), abs_of_nonneg (by nlinarith [weightLE2_Y.nonneg k])]
      exact le_of_eq (by simp [ωY, OVNS.hm])) hβ0 hs2
  have he : ∑' k, (β k * ‖w k‖) ^ 2 = Nsq r m w := by
    unfold Nsq
    exact tsum_congr fun k => by by_cases hk : k = 0 <;> simp [hβdef, hk, mul_pow]
  rw [he] at h
  exact h

end Forced

end OVNS
