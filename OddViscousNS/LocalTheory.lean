import OddViscousNS.LocalMaximal

/-! # Integrated energy inequalities and uniform smoothing (`Lemma fg:lem:lwp(c,d)`, `fg:lem:smooth`) -/

open scoped ENNReal Topology
open MeasureTheory Set Filter
noncomputable section
namespace OVNS

variable {N : ℝ → Field → Field → Field} {G : ℝ → Field} {Γ : ℝ}

/-- The lifespan condition passes to earlier times. -/
private lemma ofReal_lt_of_le {T : ℝ≥0∞} {u t : ℝ} (h : u ≤ t) (ht : ENNReal.ofReal t < T) :
    ENNReal.ofReal u < T :=
  (ENNReal.ofReal_le_ofReal h).trans_lt ht

/-- A solution is `MZ 2` throughout its lifespan. -/
private lemma IsHeatSol.mz {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y) {u t : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ t) (ht : ENNReal.ofReal t < T) : MZ 2 (y u) :=
  let h := hy.adm u hu0 (ofReal_lt_of_le hu ht)
  ⟨h.inH, h.mean⟩

/-- The norm itself (not only its square) is continuous along a `HeatPair`. -/
private lemma HeatPair.continuousOn_hnorm {σ a b : ℝ} {c F : ℝ → Field} (h : HeatPair σ a b c F)
    (hab : a ≤ b) : ContinuousOn (fun t ↦ hnorm σ (c t)) (Icc a b) :=
  (h.continuousOn_hnorm_sq hab).sqrt.congr fun t _ ↦ (Real.sqrt_sq (hnorm_nonneg σ (c t))).symm

/-- The Wiener norm is Lipschitz for the `H²` norm. -/
private lemma abs_wiener_sub_le {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) :
    |wiener f - wiener g| ≤ c4 * hnorm 2 (f - g) := by
  have hmz : ∀ {f g : Field}, MZ 2 f → MZ 2 g → MZ 2 (f - g) := fun hf hg ↦
    ⟨hf.inH.sub hg.inH, by simp [hf.mean, hg.mean]⟩
  have hle : ∀ {f g : Field}, MZ 2 f → MZ 2 g → wiener f ≤ wiener g + c4 * hnorm 2 (f - g) := by
    intro f g hf hg
    have h := wiener_add_le (u := f - g) (v := g) (summable_wiener (hmz hf hg).inH)
      (summable_wiener hg.inH)
    rw [sub_add_cancel] at h
    linarith [wiener_le (hmz hf hg)]
  have h1 := hle hf hg
  have h2 := hle hg hf
  rw [hnorm_sub_comm] at h2
  rw [abs_le]
  constructor <;> linarith

/-- `t ↦ 𝒜(y t)` is continuous on compact subintervals of the lifespan. -/
private lemma IsHeatSol.continuousOn_wiener {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y)
    {t : ℝ} (ht : ENNReal.ofReal t < T) : ContinuousOn (fun u ↦ wiener (y u)) (Icc 0 t) := by
  intro t₀ ht₀
  have hlim := ((hy.cont t₀ ht₀.1 (ofReal_lt_of_le ht₀.2 ht)).mono_left
    (nhdsWithin_mono t₀ fun _ h ↦ h.1 : 𝓝[Icc 0 t] t₀ ≤ 𝓝[Ici 0] t₀)).const_mul c4
  rw [mul_zero] at hlim
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [Real.norm_eq_abs]
  exact abs_wiener_sub_le (hy.mz hu.1 hu.2 ht) (hy.mz ht₀.1 ht₀.2 ht)

/-- The elementary Young inequality closing the `H¹` estimate. -/
private lemma h1_young {a b r c w X : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : r ^ 2 = a * b)
    (hw : w ≤ c * r) (hX : X ≤ Γ + 2 * a * w) :
    2 * (b * X) ≤ b ^ 2 + 256 * c ^ 4 * a ^ 6 + 2 * Γ ^ 2 := by
  have h0 : b * X ≤ b * (Γ + 2 * a * (c * r)) :=
    mul_le_mul_of_nonneg_left (hX.trans (by gcongr)) hb
  have h1 : 2 * b * Γ ≤ b ^ 2 / 2 + 2 * Γ ^ 2 := by nlinarith [sq_nonneg (b - 2 * Γ)]
  have h2 : 4 * c * a * b * r ≤ b ^ 2 / 4 + 16 * c ^ 2 * a ^ 2 * r ^ 2 := by
    nlinarith [sq_nonneg (b / 2 - 4 * c * a * r)]
  have h3 : 16 * c ^ 2 * a ^ 2 * r ^ 2 = 16 * c ^ 2 * a ^ 3 * b := by rw [hr]; ring
  have h4 : 16 * c ^ 2 * a ^ 3 * b ≤ b ^ 2 / 4 + 256 * c ^ 4 * a ^ 6 := by
    nlinarith [sq_nonneg (b / 2 - 16 * c ^ 2 * a ^ 3)]
  nlinarith

/-- The `σ = 1` pairing estimate at a fixed time. -/
private lemma h1_pointwise {cI : ℝ}
    (hI : ∀ u : Field, MZ 2 u → wiener u ≤ cI * Real.sqrt (hnorm 1 u * hnorm 2 u))
    (hN : Majorized N) (hG : GoodForce G Γ) {v : Field} (hv : MZ 2 v) (t : ℝ) :
    2 * pair 1 v (G t - N t v v) ≤
      hnorm 2 v ^ 2 + 256 * cI ^ 4 * hnorm 1 v ^ 6 + 2 * Γ ^ 2 := by
  have hNb := hN.hnorm_zero_le t hv hv
  have hG0 : InH 0 (G t) := (hG.adm t).inH.mono (by norm_num)
  have e1 : (1 : ℝ) + 1 = 2 := by norm_num
  have e0 : (1 : ℝ) - 1 = 0 := by norm_num
  have hp := (pair_le (σ := 1) (c := v) (F := G t - N t v v) (by rw [e1]; exact hv.inH)
    (by rw [e0]; exact hG0.sub hNb.1)).2
  rw [e1, e0] at hp
  have hX : hnorm 0 (G t - N t v v) ≤ Γ + 2 * hnorm 1 v * wiener v := by
    have h1 := hnorm_sub_le hG0 hNb.1
    have h2 : hnorm 0 (G t) ≤ Γ := (hnorm_mono (by norm_num) (hG.adm t).inH).trans (hG.bd t)
    nlinarith [hNb.2]
  have ha := hnorm_nonneg 1 v
  have hb := hnorm_nonneg 2 v
  have hy := h1_young (Γ := Γ) ha hb
    (Real.sq_sqrt (mul_nonneg ha hb)) (hI v hv) hX
  have := le_of_abs_le hp
  linarith

/-- The `σ = 2` pairing estimate at a fixed time. -/
private lemma h2_pointwise (hN : Majorized N) (hG : GoodForce G Γ) {v : Field} (hv : MZ 2 v)
    (hv3 : InH 3 v) (t : ℝ) :
    2 * pair 2 v (G t - N t v v) ≤
      hnorm 3 v ^ 2 + 128 * wiener v ^ 2 * hnorm 2 v ^ 2 + 2 * Γ ^ 2 := by
  have hv1 : MZ 1 v := ⟨hv.inH.mono (by norm_num), hv.mean⟩
  have e3 : (2 : ℝ) + 1 = 3 := by norm_num
  have e1 : (2 : ℝ) - 1 = 1 := by norm_num
  have hNb := hN.hnorm_le t (σ := 2) (by norm_num) hv hv hv hv
  rw [e1, Real.rpow_two] at hNb
  have hp := (pair_le (σ := 2) (c := v) (F := G t - N t v v) (by rw [e3]; exact hv3)
    (by rw [e1]; exact (hG.adm t).inH.sub hNb.1)).2
  rw [e3, e1] at hp
  have hX : hnorm 1 (G t - N t v v) ≤ Γ + 8 * wiener v * hnorm 2 v := by
    have h1 := hnorm_sub_le (hG.adm t).inH hNb.1
    have h2 := hG.bd t
    nlinarith [hNb.2]
  have h3 := le_of_abs_le hp
  set c := hnorm 3 v
  set X := hnorm 1 (G t - N t v v)
  set W := wiener v * hnorm 2 v with hW
  have hc : 0 ≤ c := hnorm_nonneg 3 v
  have h4 : c * X ≤ c * (Γ + 8 * W) := mul_le_mul_of_nonneg_left (by rw [hW]; linarith) hc
  have h5 : wiener v ^ 2 * hnorm 2 v ^ 2 = W ^ 2 := by rw [hW]; ring
  nlinarith [sq_nonneg (c - (Γ + 8 * W)), sq_nonneg (Γ - 8 * W)]

/-- The `H¹` differential inequality, integrated (Lemma fg:lem:lwp(c), first): with a universal
`C`, `‖y(t)‖₁² + ∫‖y‖₂² ≤ ‖y(s)‖₁² + ∫ (C ‖y‖₁⁶ + 2‖G‖₀²)`. -/
theorem exists_h1_ineq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℝ → Field → Field → Field) (G : ℝ → Field) (Γ : ℝ) (T : ℝ≥0∞)
      (y : ℝ → Field), Majorized N → GoodForce G Γ → IsHeatSol N G T y →
      ∀ s t, 0 ≤ s → s ≤ t → ENNReal.ofReal t < T →
        hnorm 1 (y t) ^ 2 + ∫ u in s..t, hnorm 2 (y u) ^ 2 ≤
          hnorm 1 (y s) ^ 2 + ∫ u in s..t, (C * hnorm 1 (y u) ^ 6 + 2 * Γ ^ 2) := by
  obtain ⟨cI, hcI, hI⟩ := exists_wiener_interp
  refine ⟨256 * cI ^ 4, by positivity, ?_⟩
  intro N G Γ T y hN hG hy s t hs hst ht
  have e : (1 : ℝ) + 1 = 2 := by norm_num
  have hp := (hy.heatPair_low hN hG (σ := 1) (Or.inr rfl) (hs.trans hst) ht).mono hs le_rfl
  have hid := hp.energy_identity le_rfl hst le_rfl
  have hdiss := hp.intervalIntegrable_dissipation hst
  have hpair := hp.intervalIntegrable_pair hst
  rw [e] at hid hdiss
  beta_reduce at hid hpair
  have hg : IntervalIntegrable (fun u ↦ 256 * cI ^ 4 * hnorm 1 (y u) ^ 6 + 2 * Γ ^ 2)
      volume s t := ContinuousOn.intervalIntegrable (by
    rw [uIcc_of_le hst]
    exact (continuousOn_const.mul ((hp.continuousOn_hnorm hst).pow 6)).add continuousOn_const)
  have hle := intervalIntegral.integral_mono_on hst (hpair.const_mul 2) (hdiss.add hg)
    fun u hu ↦ by
      have := h1_pointwise hI hN hG (hy.mz (hs.trans hu.1) hu.2 ht) u
      linarith
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hdiss hg] at hle
  linarith

/-- The `H²` differential inequality, integrated (Lemma fg:lem:lwp(c), second). -/
theorem h2_ineq (hN : Majorized N) (hG : GoodForce G Γ) {T : ℝ≥0∞} {y : ℝ → Field}
    (hy : IsHeatSol N G T y) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 2 (y t) ^ 2 + ∫ u in s..t, hnorm 3 (y u) ^ 2 ≤
      hnorm 2 (y s) ^ 2 + ∫ u in s..t, (128 * wiener (y u) ^ 2 * hnorm 2 (y u) ^ 2 + 2 * Γ ^ 2) := by
  have e : (2 : ℝ) + 1 = 3 := by norm_num
  have hp := (hy.heatPair hN hG (hs.trans hst) ht).mono hs le_rfl
  have hid := hp.energy_identity le_rfl hst le_rfl
  have hdiss := hp.intervalIntegrable_dissipation hst
  have hpair := hp.intervalIntegrable_pair hst
  have hae := hp.ae_inH hst
  rw [e] at hid hdiss hae
  beta_reduce at hid hpair
  have hg : IntervalIntegrable (fun u ↦ 128 * wiener (y u) ^ 2 * hnorm 2 (y u) ^ 2 + 2 * Γ ^ 2)
      volume s t := ContinuousOn.intervalIntegrable (by
    rw [uIcc_of_le hst]
    have hw := (hy.continuousOn_wiener ht).mono (Icc_subset_Icc_left hs)
    exact ((continuousOn_const.mul (hw.pow 2)).mul ((hp.continuousOn_hnorm hst).pow 2)).add
      continuousOn_const)
  have hle := intervalIntegral.integral_mono_ae_restrict hst (hpair.const_mul 2) (hdiss.add hg) (by
    filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with u hu3 hu
    have := h2_pointwise hN hG (hy.mz (hs.trans hu.1) hu.2 ht) hu3 u
    linarith)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hdiss hg] at hle
  linarith

/-- The `H²` inequality with `𝒜²` absorbed through an `H¹` bound `R`, in Gronwall form. -/
private lemma h2_diff {cI : ℝ}
    (hI : ∀ u : Field, MZ 2 u → wiener u ≤ cI * Real.sqrt (hnorm 1 u * hnorm 2 u))
    (hN : Majorized N) (hG : GoodForce G Γ) {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y)
    {a t R : ℝ} (ha : 0 ≤ a) (ht : ENNReal.ofReal t < T)
    (hρ : ∀ u ∈ Icc a t, hnorm 1 (y u) ≤ R) (hcI : 0 < cI) :
    ∀ s t', a ≤ s → s ≤ t' → t' ≤ t → hnorm 2 (y t') ^ 2 ≤ hnorm 2 (y s) ^ 2 +
      ∫ u in s..t', (128 * cI ^ 2 * R * hnorm 2 (y u) * hnorm 2 (y u) ^ 2 + 2 * Γ ^ 2) := by
  intro s t' hs hst ht'
  have hs0 := ha.trans hs
  have ht'' := ofReal_lt_of_le ht' ht
  have h := h2_ineq hN hG hy hs0 hst ht''
  have hR : 0 ≤ R := (hnorm_nonneg 1 _).trans (hρ s ⟨hs, hst.trans ht'⟩)
  have hc := ((hy.heatPair hN hG (hs0.trans hst) ht'').mono hs0 le_rfl).continuousOn_hnorm hst
  have hw := (hy.continuousOn_wiener ht'').mono (Icc_subset_Icc_left hs0)
  have hf : IntervalIntegrable (fun u ↦ 128 * wiener (y u) ^ 2 * hnorm 2 (y u) ^ 2 + 2 * Γ ^ 2)
      volume s t' := ContinuousOn.intervalIntegrable (by
    rw [uIcc_of_le hst]
    exact ((continuousOn_const.mul (hw.pow 2)).mul (hc.pow 2)).add continuousOn_const)
  have hg : IntervalIntegrable
      (fun u ↦ 128 * cI ^ 2 * R * hnorm 2 (y u) * hnorm 2 (y u) ^ 2 + 2 * Γ ^ 2)
      volume s t' := ContinuousOn.intervalIntegrable (by
    rw [uIcc_of_le hst]
    exact ((continuousOn_const.mul hc).mul (hc.pow 2)).add continuousOn_const)
  have hle := intervalIntegral.integral_mono_on hst hf hg fun u hu ↦ by
    have hu0 := hs0.trans hu.1
    have hb := hnorm_nonneg 2 (y u)
    have h1 := hnorm_nonneg 1 (y u)
    have hw0 := wiener_nonneg (y u)
    have hle := hI (y u) (hy.mz hu0 hu.2 ht'')
    have hsq : wiener (y u) ^ 2 ≤ cI ^ 2 * (hnorm 1 (y u) * hnorm 2 (y u)) := by
      calc wiener (y u) ^ 2 ≤ (cI * Real.sqrt (hnorm 1 (y u) * hnorm 2 (y u))) ^ 2 :=
            pow_le_pow_left₀ hw0 hle 2
        _ = _ := by rw [mul_pow, Real.sq_sqrt (mul_nonneg h1 hb)]
    have hsq' : wiener (y u) ^ 2 ≤ cI ^ 2 * R * hnorm 2 (y u) := by
      have h3 := hρ u ⟨hs.trans hu.1, hu.2.trans ht'⟩
      have : cI ^ 2 * (hnorm 1 (y u) * hnorm 2 (y u)) ≤ cI ^ 2 * (R * hnorm 2 (y u)) := by gcongr
      linarith
    have := mul_le_mul_of_nonneg_right hsq' (sq_nonneg (hnorm 2 (y u)))
    linarith
  have hd : 0 ≤ ∫ u in s..t', hnorm 3 (y u) ^ 2 :=
    intervalIntegral.integral_nonneg hst fun _ _ ↦ sq_nonneg _
  linarith

/-- Bounds on a window of length at most `L`, from an `H¹` bound `R`: the dissipation, and the
end-point `H²` norm in the two forms used below (from the start point, or by averaging). -/
private lemma exists_window_bounds (R Γ L : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L) :
    ∃ J K : ℝ, 0 ≤ J ∧ 0 ≤ K ∧ ∀ (N : ℝ → Field → Field → Field) (G : ℝ → Field) (T : ℝ≥0∞)
      (y : ℝ → Field), Majorized N → GoodForce G Γ → IsHeatSol N G T y →
      ∀ a t, 0 ≤ a → a ≤ t → t - a ≤ L → ENNReal.ofReal t < T →
        (∀ u ∈ Icc a t, hnorm 1 (y u) ≤ R) →
        (∫ u in a..t, hnorm 2 (y u) ^ 2) ≤ J ∧
        hnorm 2 (y t) ^ 2 ≤ (hnorm 2 (y a) ^ 2 + L * (2 * Γ ^ 2)) * Real.exp K ∧
        (t - a = 1 → hnorm 2 (y t) ^ 2 ≤ (J + 2 * Γ ^ 2) * Real.exp K) := by
  obtain ⟨C, hC0, hC⟩ := exists_h1_ineq
  obtain ⟨cI, hcI, hI⟩ := exists_wiener_interp
  refine ⟨R ^ 2 + L * (C * R ^ 6 + 2 * Γ ^ 2),
    128 * cI ^ 2 * R * ((L + (R ^ 2 + L * (C * R ^ 6 + 2 * Γ ^ 2))) / 2),
    by positivity, by positivity, ?_⟩
  intro N G T y hN hG hy a t ha hat hL' ht hρ
  set J := R ^ 2 + L * (C * R ^ 6 + 2 * Γ ^ 2) with hJdef
  have hta : 0 ≤ t := ha.trans hat
  have hb := ((hy.heatPair hN hG hta ht).mono ha le_rfl).continuousOn_hnorm hat
  have ha1 := ((hy.heatPair_low hN hG (σ := 1) (Or.inr rfl) hta ht).mono ha
    le_rfl).continuousOn_hnorm hat
  have hbI : IntervalIntegrable (fun u ↦ hnorm 2 (y u)) volume a t :=
    ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hat]; exact hb)
  have hb2I : IntervalIntegrable (fun u ↦ hnorm 2 (y u) ^ 2) volume a t :=
    ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hat]; exact hb.pow 2)
  have hJ : ∫ u in a..t, hnorm 2 (y u) ^ 2 ≤ J := by
    have h := hC N G Γ T y hN hG hy a t ha hat ht
    have hgI : IntervalIntegrable (fun u ↦ C * hnorm 1 (y u) ^ 6 + 2 * Γ ^ 2) volume a t :=
      ContinuousOn.intervalIntegrable (by
        rw [uIcc_of_le hat]
        exact (continuousOn_const.mul (ha1.pow 6)).add continuousOn_const)
    have hint := intervalIntegral.integral_mono_on (g := fun _ ↦ C * R ^ 6 + 2 * Γ ^ 2) hat hgI
      intervalIntegrable_const fun u hu ↦ by
        have := pow_le_pow_left₀ (hnorm_nonneg 1 (y u)) (hρ u hu) 6
        have := mul_le_mul_of_nonneg_left this hC0
        linarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hint
    have h1 : hnorm 1 (y a) ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg 1 _) (hρ a ⟨le_rfl, hat⟩) 2
    have h2 : (t - a) * (C * R ^ 6 + 2 * Γ ^ 2) ≤ L * (C * R ^ 6 + 2 * Γ ^ 2) :=
      mul_le_mul_of_nonneg_right hL' (by positivity)
    linarith [sq_nonneg (hnorm 1 (y t))]
  have hκ : ∫ u in a..t, 128 * cI ^ 2 * R * hnorm 2 (y u) ≤ 128 * cI ^ 2 * R * ((L + J) / 2) := by
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hint := intervalIntegral.integral_mono_on hat hbI
      ((intervalIntegrable_const (c := (1 : ℝ))).add hb2I |>.div_const 2) fun u _ ↦ by
        nlinarith [sq_nonneg (hnorm 2 (y u) - 1)]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const hb2I,
      intervalIntegral.integral_const, smul_eq_mul, mul_one] at hint
    linarith
  have hκI : IntervalIntegrable (fun u ↦ 128 * cI ^ 2 * R * hnorm 2 (y u)) volume a t :=
    hbI.const_mul _
  have hκ0 : ∀ u, 0 ≤ 128 * cI ^ 2 * R * hnorm 2 (y u) := fun u ↦ by
    have := hnorm_nonneg 2 (y u)
    positivity
  have hdiff := h2_diff hI hN hG hy ha ht hρ hcI
  have hexp : Real.exp (∫ u in a..t, 128 * cI ^ 2 * R * hnorm 2 (y u)) ≤
      Real.exp (128 * cI ^ 2 * R * ((L + J) / 2)) := Real.exp_le_exp.2 hκ
  have hβ : ∫ _ in a..t, 2 * Γ ^ 2 = (t - a) * (2 * Γ ^ 2) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  refine ⟨hJ, ?_, fun h1 ↦ ?_⟩
  · have h := gronwall_simple (y := fun u ↦ hnorm 2 (y u) ^ 2)
      (κ := fun u ↦ 128 * cI ^ 2 * R * hnorm 2 (y u)) (β := fun _ ↦ 2 * Γ ^ 2) hat (hb.pow 2)
      hκI hκ0 intervalIntegrable_const (fun _ ↦ by positivity) hdiff a t le_rfl hat le_rfl
    refine h.trans ?_
    rw [hβ]
    have h3 : (t - a) * (2 * Γ ^ 2) ≤ L * (2 * Γ ^ 2) :=
      mul_le_mul_of_nonneg_right hL' (by positivity)
    gcongr
  · obtain rfl : a = t - 1 := by linarith
    have h := uniform_gronwall (y := fun u ↦ hnorm 2 (y u) ^ 2)
      (κ := fun u ↦ 128 * cI ^ 2 * R * hnorm 2 (y u)) (β := fun _ ↦ 2 * Γ ^ 2) (hb.pow 2)
      (fun _ ↦ sq_nonneg _) hκI hκ0 intervalIntegrable_const (fun _ ↦ by positivity) hdiff
    refine h.trans ?_
    rw [hβ, h1, one_mul]
    gcongr

/-- Uniform smoothing (`Lemma fg:lem:smooth`): an `H¹` bound on a unit window gives bounds on
`∫ ‖y‖₂²` and the end-point `H²` norm, depending only on `(ρ', Γ)`. -/
theorem exists_uniform_smoothing (ρ' Γ : ℝ) :
    ∃ J S : ℝ, 0 ≤ J ∧ 0 ≤ S ∧ ∀ (N : ℝ → Field → Field → Field) (G : ℝ → Field) (T : ℝ≥0∞)
      (y : ℝ → Field), Majorized N → GoodForce G Γ → IsHeatSol N G T y →
      ∀ t, 1 ≤ t → ENNReal.ofReal t < T → (∀ u ∈ Icc (t - 1) t, hnorm 1 (y u) ≤ ρ') →
        (∫ u in (t - 1)..t, hnorm 2 (y u) ^ 2) ≤ J ∧ hnorm 2 (y t) ≤ S := by
  obtain ⟨J, K, hJ, hK, h⟩ := exists_window_bounds |ρ'| Γ 1 (abs_nonneg _) zero_le_one
  refine ⟨J, Real.sqrt ((J + 2 * Γ ^ 2) * Real.exp K), hJ, Real.sqrt_nonneg _, ?_⟩
  intro N G T y hN hG hy t ht1 ht hρ
  obtain ⟨h1, -, h3⟩ := h N G T y hN hG hy (t - 1) t (by linarith) (by linarith) (by linarith) ht
    fun u hu ↦ (hρ u hu).trans (le_abs_self _)
  exact ⟨h1, Real.le_sqrt_of_sq_le (h3 (by ring))⟩

/-- Same near `t = 0`, from an initial `H²` bound: bounds on `[0,1]`. -/
theorem exists_initial_smoothing (ρ' Γ μ : ℝ) :
    ∃ J S : ℝ, 0 ≤ J ∧ 0 ≤ S ∧ ∀ (N : ℝ → Field → Field → Field) (G : ℝ → Field) (T : ℝ≥0∞)
      (y : ℝ → Field), Majorized N → GoodForce G Γ → IsHeatSol N G T y → hnorm 2 (y 0) ≤ μ →
      ∀ t ∈ Icc (0 : ℝ) 1, ENNReal.ofReal t < T → (∀ u ∈ Icc 0 t, hnorm 1 (y u) ≤ ρ') →
        (∫ u in (0 : ℝ)..t, hnorm 2 (y u) ^ 2) ≤ J ∧ hnorm 2 (y t) ≤ S := by
  obtain ⟨J, K, hJ, hK, h⟩ := exists_window_bounds |ρ'| Γ 1 (abs_nonneg _) zero_le_one
  refine ⟨J, Real.sqrt ((μ ^ 2 + 1 * (2 * Γ ^ 2)) * Real.exp K), hJ, Real.sqrt_nonneg _, ?_⟩
  intro N G T y hN hG hy hμ t ht ht' hρ
  obtain ⟨h1, h2, -⟩ := h N G T y hN hG hy 0 t le_rfl ht.1 (by linarith [ht.2]) ht'
    fun u hu ↦ (hρ u hu).trans (le_abs_self _)
  have h0 : hnorm 2 (y 0) ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ (hnorm_nonneg 2 _) hμ 2
  refine ⟨h1, Real.le_sqrt_of_sq_le (h2.trans ?_)⟩
  gcongr

/-- An `H¹` bound on a finite lifespan excludes blow-up: the solution extends. -/
theorem h1_bound_excludes_blowup (ρ Γ b : ℝ) (y₀H2 : ℝ) :
    ∃ C : ℝ, ∀ (N : ℝ → Field → Field → Field) (G : ℝ → Field) (T : ℝ≥0∞) (y : ℝ → Field),
      Majorized N → GoodForce G Γ → IsHeatSol N G T y → hnorm 2 (y 0) ≤ y₀H2 →
      T ≤ ENNReal.ofReal b →
      (∀ t, 0 ≤ t → ENNReal.ofReal t < T → hnorm 1 (y t) ≤ ρ) →
      ∀ t, 0 ≤ t → ENNReal.ofReal t < T → hnorm 2 (y t) ≤ C := by
  obtain ⟨J, K, -, -, h⟩ := exists_window_bounds |ρ| Γ |b| (abs_nonneg _) (abs_nonneg _)
  refine ⟨Real.sqrt ((y₀H2 ^ 2 + |b| * (2 * Γ ^ 2)) * Real.exp K), ?_⟩
  intro N G T y hN hG hy h0 hT hρ t ht ht'
  have htb : t ≤ |b| :=
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).1 (ht'.trans_le hT)).le.trans (le_abs_self b)
  obtain ⟨-, h2, -⟩ := h N G T y hN hG hy 0 t le_rfl ht (by linarith) ht'
    fun u hu ↦ (hρ u hu.1 (ofReal_lt_of_le hu.2 ht')).trans (le_abs_self _)
  have h0' : hnorm 2 (y 0) ^ 2 ≤ y₀H2 ^ 2 := pow_le_pow_left₀ (hnorm_nonneg 2 _) h0 2
  exact Real.le_sqrt_of_sq_le (h2.trans (by gcongr))

end OVNS
