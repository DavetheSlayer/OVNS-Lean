import OddViscousNS.Induction
import OddViscousNS.SmoothTime

/-!
# Physical pullback of normalized heat solutions

The helpers that turn a global normalized heat solution with bounds into a global strong solution
of the original equation (`exists_physical_of_normalized`), shared by Theorems 1.1 and 1.3.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS
section Helpers

open Filter Topology

variable {σ ν r : ℝ} {y : ℝ → Field}

/-- Admissibility is stable under real scalars. -/
lemma adm_smul_real {u : Field} (c : ℝ) (hu : Adm σ u) : Adm σ ((c : ℂ) • u) := by
  refine ⟨hu.inH.smul c, fun k => ?_, fun k => ?_, ?_⟩
  · simp only [Pi.smul_apply, hu.real k]
    ext i
    simp [conjV]
  · change dotM ((c : ℂ) • u k) k = 0
    rw [dotM_smul, hu.sol k, mul_zero]
  · simp [hu.mean]

/-- The filter preserves every Sobolev term of a solenoidal field. -/
lemma term_rotF (σ τ : ℝ) {u : Field} (hu : IsSolenoidal u) (k : Mode) :
    sobWeight σ k * ‖rotF τ u k‖ ^ 2 = sobWeight σ k * ‖u k‖ ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    simp [sobWeight]
  · rw [show rotF τ u k = rot τ k (u k) from rfl, norm_rot, leray_of_perp hk (hu k)]

lemma hsE_rotF (σ τ : ℝ) {u : Field} (hu : IsSolenoidal u) :
    hsE σ (rotF τ u) = hsE σ u := by
  simp only [hsE, term_rotF σ τ hu]

lemma inH_rotF (τ : ℝ) {u : Field} (hu : IsSolenoidal u) (h : InH σ u) :
    InH σ (rotF τ u) := by
  simpa only [InH, term_rotF σ τ hu] using h

lemma hsE_smul (σ : ℝ) {c : ℝ} (hc : 0 ≤ c) (u : Field) :
    hsE σ ((c : ℂ) • u) = ENNReal.ofReal (c ^ 2) * hsE σ u := by
  rw [hsE, hsE, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg c), Pi.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg hc]
  congr 1
  ring

lemma rotF_zero_field (τ : ℝ) : rotF τ 0 = 0 := by
  simpa using rotF_sub τ 0 0

lemma rotF_zero_time {u : Field} (h : Adm σ u) : rotF 0 u = u := by
  funext k
  change rot 0 k (u k) = u k
  rw [rot_zero_time]
  by_cases hk : k = 0
  · subst hk
    simp [leray, h.mean]
  · exact leray_of_perp hk (h.sol k)

/-- The physical field attached to a normalized filtered solution. -/
noncomputable def scaleU (ν r : ℝ) (y : ℝ → Field) (t : ℝ) : Field :=
  (ν : ℂ) • rotF (r * (ν * t)) (y (ν * t))

lemma scaleU_rescale (hν : 0 < ν) (r : ℝ) (y : ℝ → Field) :
    (fun τ => (ν⁻¹ : ℂ) • scaleU ν r y (τ / ν)) = fun τ => rotF (r * τ) (y τ) := by
  funext τ
  have hc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  rw [scaleU, mul_div_cancel₀ _ hν.ne', smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Change of variables `τ = ν s`, for arbitrary (not nec. measurable) integrands. -/
lemma lintegral_comp_scale (hν : 0 < ν) (w : ℝ → ℝ≥0∞) (a b : ℝ) :
    ∫⁻ s in Icc a b, w (ν * s) = ENNReal.ofReal ν⁻¹ * ∫⁻ τ in Icc (ν * a) (ν * b), w τ := by
  have hemb : MeasurableEmbedding (ν * ·) :=
    (Homeomorph.mulLeft₀ ν hν.ne').measurableEmbedding
  have hpre : (ν * ·) ⁻¹' Icc (ν * a) (ν * b) = Icc a b := by
    ext s
    simp only [mem_preimage, mem_Icc, mul_le_mul_iff_of_pos_left hν]
  have h1 : ∫⁻ τ in Icc (ν * a) (ν * b), w τ ∂(Measure.map (ν * ·) volume) =
      ∫⁻ s in Icc a b, w (ν * s) := by
    rw [Measure.restrict_map hemb.measurable measurableSet_Icc, hemb.lintegral_map, hpre]
  rw [← h1, Real.map_volume_mul_left hν.ne', Measure.restrict_smul, lintegral_smul_measure,
    abs_of_pos (inv_pos.2 hν)]
  rfl

lemma hsE_scaleU (hν : 0 < ν) {t : ℝ} (hsol : IsSolenoidal (y (ν * t))) :
    hsE σ (scaleU ν r y t) = ENNReal.ofReal (ν ^ 2) * hsE σ (y (ν * t)) := by
  rw [scaleU, hsE_smul _ hν.le, hsE_rotF _ _ hsol]

lemma lintegral_scaleU (hν : 0 < ν) (hsol : ∀ t, 0 ≤ t → IsSolenoidal (y t)) {a : ℝ}
    (ha : 0 ≤ a) (b : ℝ) :
    ∫⁻ t in Icc a b, hsE σ (scaleU ν r y t) =
      ENNReal.ofReal ν * ∫⁻ τ in Icc (ν * a) (ν * b), hsE σ (y τ) := by
  have h1 : ∫⁻ t in Icc a b, hsE σ (scaleU ν r y t) =
      ∫⁻ t in Icc a b, ENNReal.ofReal (ν ^ 2) * hsE σ (y (ν * t)) :=
    setLIntegral_congr_fun measurableSet_Icc fun t ht =>
      hsE_scaleU hν (hsol _ (mul_nonneg hν.le (ha.trans ht.1)))
  rw [h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_scale hν (fun τ => hsE σ (y τ)), ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg ν)]
  congr 2
  field_simp

lemma lintegral_cover {w : ℝ → ℝ≥0∞} {B : ℝ≥0∞}
    (hw : ∀ x, 0 ≤ x → ∫⁻ τ in Icc x (x + 1), w τ ≤ B) {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ∫⁻ τ in Icc a (a + n), w τ ≤ n * B := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsub : Icc a (a + (n + 1 : ℕ)) ⊆ Icc a (a + n) ∪ Icc (a + n) (a + n + 1) := by
      intro τ hτ
      push_cast at hτ
      by_cases h : τ ≤ a + n
      · exact Or.inl ⟨hτ.1, h⟩
      · exact Or.inr ⟨(not_le.1 h).le, by linarith [hτ.2]⟩
    calc ∫⁻ τ in Icc a (a + (n + 1 : ℕ)), w τ
        ≤ ∫⁻ τ in Icc a (a + n) ∪ Icc (a + n) (a + n + 1), w τ := lintegral_mono_set hsub
      _ ≤ (∫⁻ τ in Icc a (a + n), w τ) + ∫⁻ τ in Icc (a + n) (a + n + 1), w τ :=
          lintegral_union_le _ _ _
      _ ≤ n * B + B := add_le_add ih (hw _ (by positivity))
      _ = (n + 1 : ℕ) * B := by
          push_cast
          ring

lemma unit_bound {N : ℝ → Field → Field → Field} {G : ℝ → Field} {Γ : ℝ}
    (hN : Majorized N) (hG : GoodForce G Γ) (hy : IsHeatSol N G ⊤ y) {x B : ℝ} (hx : 0 ≤ x)
    (hW : ∫ s in x..(x + 1), hnorm 3 (y s) ^ 2 ≤ B) :
    ∫⁻ τ in Icc x (x + 1), hsE 3 (y τ) ≤ ENNReal.ofReal B := by
  have hle : x ≤ x + 1 := by linarith
  have hP := (hy.heatPair hN hG (hx.trans hle) ENNReal.ofReal_lt_top).mono hx le_rfl
  have hae := hP.ae_inH hle
  have hint := hP.intervalIntegrable_dissipation hle
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at hae hint
  have hI : IntegrableOn (fun t => hnorm 3 (y t) ^ 2) (Ioc x (x + 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hint
  calc ∫⁻ τ in Icc x (x + 1), hsE 3 (y τ)
      = ∫⁻ τ in Icc x (x + 1), ENNReal.ofReal (hnorm 3 (y τ) ^ 2) :=
        lintegral_congr_ae (hae.mono fun t ht => hsE_eq_ofReal ht)
    _ = ∫⁻ τ in Ioc x (x + 1), ENNReal.ofReal (hnorm 3 (y τ) ^ 2) :=
        setLIntegral_congr Ioc_ae_eq_Icc.symm
    _ = ENNReal.ofReal (∫ τ in Ioc x (x + 1), hnorm 3 (y τ) ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun _ => sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal B := by
        refine ENNReal.ofReal_le_ofReal ?_
        rwa [← intervalIntegral.integral_of_le hle]

/-- Continuity in `H^σ` passes from `y` to the rescaled, unfiltered field. -/
lemma contH_scaleU (hν : 0 < ν) (hadm : ∀ t, 0 ≤ t → Adm σ (y t)) (hc : ContH σ y) :
    ContH σ (scaleU ν r y) := by
  intro t₀ ht₀
  have ht : (0 : ℝ) ≤ t₀ := ht₀
  have ha : 0 ≤ ν * t₀ := mul_nonneg hν.le ht
  have h0 := hadm _ ha
  have hmul : Tendsto (fun t => ν * t) (𝓝[Ici 0] t₀) (𝓝[Ici 0] (ν * t₀)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (continuous_const.mul continuous_id).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_nonneg hν.le ht
  have h1 := (hc _ ha).comp hmul
  have hcτ : Continuous fun t : ℝ => r * (ν * t) := by fun_prop
  have h2 : Tendsto (fun t => hnorm σ (rotF (r * (ν * t)) (y (ν * t₀)) -
      rotF (r * (ν * t₀)) (y (ν * t₀)))) (𝓝[Ici 0] t₀) (𝓝 0) :=
    ((tendsto_hnorm_rotF h0.inH h0.sol _).comp (hcτ.tendsto t₀)).mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun t => ν * (hnorm σ (y (ν * t) - y (ν * t₀)) +
      hnorm σ (rotF (r * (ν * t)) (y (ν * t₀)) - rotF (r * (ν * t₀)) (y (ν * t₀)))))
      (𝓝[Ici 0] t₀) (𝓝 0) := by
    have h := (h1.add h2).const_mul ν
    rwa [add_zero, mul_zero] at h
  refine squeeze_zero' (.of_forall fun t => hnorm_nonneg _ _) ?_ h3
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hb := hadm _ (mul_nonneg hν.le ht)
  have hsub : IsSolenoidal (y (ν * t) - y (ν * t₀)) := by
    intro k
    have h : dotM ((y (ν * t) - y (ν * t₀)) k) k =
        dotM (y (ν * t) k) k - dotM (y (ν * t₀) k) k := by
      simp [dotM, sub_mul, Finset.sum_sub_distrib]
    rw [h, hb.sol k, h0.sol k, sub_zero]
  have e : scaleU ν r y t - scaleU ν r y t₀ =
      (ν : ℂ) • (rotF (r * (ν * t)) (y (ν * t) - y (ν * t₀)) +
        (rotF (r * (ν * t)) (y (ν * t₀)) - rotF (r * (ν * t₀)) (y (ν * t₀)))) := by
    rw [rotF_sub, sub_add_sub_cancel, smul_sub]
    simp only [scaleU]
  have h4 : InH σ (rotF (r * (ν * t)) (y (ν * t) - y (ν * t₀))) :=
    inH_rotF _ hsub (hb.inH.sub h0.inH)
  have h5 : InH σ (rotF (r * (ν * t)) (y (ν * t₀)) - rotF (r * (ν * t₀)) (y (ν * t₀))) :=
    (inH_rotF _ h0.sol h0.inH).sub (inH_rotF _ h0.sol h0.inH)
  rw [e, hnorm_smul, Complex.norm_real, Real.norm_of_nonneg hν.le]
  refine mul_le_mul_of_nonneg_left ((hnorm_add_le h4 h5).trans ?_) hν.le
  rw [hnorm_rotF _ hsub]

variable {α : ℝ} {f u₀ : Field}

lemma strong_scaleU (hν : 0 < ν) (hg : Adm 2 (((ν : ℂ) ^ 2)⁻¹ • f))
    (hy : IsHeatSol (filtN (α / ν) 0) (filtG (α / ν) 0 (((ν : ℂ) ^ 2)⁻¹ • f)) ⊤ y)
    (h0 : y 0 = (ν⁻¹ : ℂ) • u₀) : IsStrongSolution ν α f u₀ (scaleU ν (α / ν) y) := by
  rw [isStrongSolution_scale hν, scaleU_rescale hν, ← h0]
  exact hy.unfilter hg

lemma unique_scaleU (hν : 0 < ν) (hg : Adm 2 (((ν : ℂ) ^ 2)⁻¹ • f))
    (hy : IsHeatSol (filtN (α / ν) 0) (filtG (α / ν) 0 (((ν : ℂ) ^ 2)⁻¹ • f)) ⊤ y)
    (h0 : y 0 = (ν⁻¹ : ℂ) • u₀) {u' : ℝ → Field} (hu' : IsStrongSolution ν α f u₀ u') {t : ℝ}
    (ht : 0 ≤ t) : u' t = scaleU ν (α / ν) y t := by
  have hs := (isStrongSolution_scale hν).1 hu'
  have hf := hs.filter hg
  set v' : ℝ → Field := fun τ => (ν⁻¹ : ℂ) • u' (τ / ν) with hv'
  have hc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have h00 : y 0 = (fun t => rotF (-(α / ν * t)) (v' t)) 0 := by
    beta_reduce
    rw [mul_zero, neg_zero, rotF_zero_time (hs.adm 0 le_rfl), hs.init, h0]
  have hτ : 0 ≤ ν * t := mul_nonneg hν.le ht
  have heq := heatSol_unique (majorized_filtN _ 0) (goodForce_filtG _ 0 hg) hy hf h00 (ν * t) hτ
    ENNReal.ofReal_lt_top
  have hadm := hs.adm _ hτ
  have hback := rotF_rotF_neg (-(α / ν * (ν * t))) hadm.sol hadm.mean
  rw [neg_neg, ← heq] at hback
  rw [scaleU, hback]
  simp only [hv', mul_div_cancel_left₀ _ hν.ne', smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The unforced part of the theorem, transported from `y` to the physical field. -/
lemma zero_force_scaleU (hν : 0 < ν) (hz : Adm 2 (0 : Field))
    (hy : IsHeatSol (filtN r 0) (filtG r 0 0) ⊤ y) (h0 : y 0 = (ν⁻¹ : ℂ) • u₀)
    (hS : IsStrongSolution ν α 0 u₀ (scaleU ν r y)) :
    (∀ s, 2 ≤ s → InH s u₀ → (∀ t, 0 ≤ t → InH s (scaleU ν r y t)) ∧
      ContH s (scaleU ν r y) ∧ L2locH (s + 1) (scaleU ν r y)) ∧
      SmoothAtPositiveTimes (scaleU ν r y) := by
  have hadm : ∀ t, 0 ≤ t → Adm 2 (y t) := fun t ht => hy.adm t ht ENNReal.ofReal_lt_top
  have hN := majorized_filtN r 0
  have hG := goodForce_filtG r 0 hz
  have hG0 : filtG r 0 (0 : Field) = fun _ => 0 := by
    funext t
    exact rotF_zero_field _
  refine ⟨fun s hs hi => ?_, smoothAtPositiveTimes hν hS fun m a b ha hab => ?_⟩
  · have h0s : InH s (y 0) := h0 ▸ hi.smul _
    obtain ⟨hIn, hC, hL⟩ := persist hN hG hG0 hy hs h0s
    have hadms : ∀ t, 0 ≤ t → Adm s (y t) := fun t ht =>
      ⟨hIn t ht, (hadm t ht).real, (hadm t ht).sol, (hadm t ht).mean⟩
    refine ⟨fun t ht => ?_, contH_scaleU hν hadms hC, fun T hT => ?_⟩
    · have hτ : 0 ≤ ν * t := mul_nonneg hν.le ht
      exact (inH_rotF _ (hadm _ hτ).sol (hIn _ hτ)).smul _
    · rw [lintegral_scaleU hν (fun t ht => (hadm t ht).sol) le_rfl, mul_zero]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hL _ (mul_nonneg hν.le hT))
  · obtain ⟨C, hC⟩ := smoothing hN hG hG0 hy m (mul_pos hν ha)
      (mul_le_mul_of_nonneg_left hab hν.le)
    refine ⟨ν * C, fun t ht => ?_⟩
    have hmem : ν * t ∈ Icc (ν * a) (ν * b) :=
      ⟨mul_le_mul_of_nonneg_left ht.1 hν.le, mul_le_mul_of_nonneg_left ht.2 hν.le⟩
    obtain ⟨h1, h2⟩ := hC _ hmem
    have hsol := (hadm _ ((mul_pos hν ha).le.trans hmem.1)).sol
    refine ⟨(inH_rotF _ hsol h1).smul _, ?_⟩
    rw [scaleU, hnorm_smul, Complex.norm_real, Real.norm_of_nonneg hν.le, hnorm_rotF _ hsol]
    exact mul_le_mul_of_nonneg_left h2 hν.le

/-- The scaling bridge: a normalized filtered solution yields everything claimed in the theorem
for the physical solution. -/
lemma exists_physical_of_normalized {B : ℝ} (hν : 0 < ν)
    (hg : Adm 2 (((ν : ℂ) ^ 2)⁻¹ • f))
    (hy : IsHeatSol (filtN (α / ν) 0) (filtG (α / ν) 0 (((ν : ℂ) ^ 2)⁻¹ • f)) ⊤ y)
    (h0 : y 0 = (ν⁻¹ : ℂ) • u₀)
    (hB : ∀ t, 0 ≤ t → hnorm 1 (y t) ≤ B ∧ hnorm 2 (y t) ≤ B)
    (hW : ∀ t, 0 ≤ t → ∫ s in t..(t + 1), hnorm 3 (y s) ^ 2 ≤ B) :
    ∃ u : ℝ → Field,
      IsStrongSolution ν α f u₀ u ∧
      (∀ u', IsStrongSolution ν α f u₀ u' → ∀ t, 0 ≤ t → u' t = u t) ∧
      L2locH 3 u ∧
      (∀ t, 0 ≤ t → hnorm 1 (u t) ≤ ν * B ∧ hnorm 2 (u t) ≤ ν * B) ∧
      (∀ t h : ℝ, 0 ≤ t → 0 ≤ h →
        ∫⁻ s in Icc t (t + h), hsE 3 (u s) ≤ ENNReal.ofReal (ν * ⌈ν * h⌉ * B)) ∧
      (f = 0 → (∀ s, 2 ≤ s → InH s u₀ → (∀ t, 0 ≤ t → InH s (u t)) ∧
          ContH s u ∧ L2locH (s + 1) u) ∧
        SmoothAtPositiveTimes u) := by
  have hadm : ∀ t, 0 ≤ t → Adm 2 (y t) := fun t ht => hy.adm t ht ENNReal.ofReal_lt_top
  have hS := strong_scaleU hν hg hy h0
  have hwin : ∀ t h : ℝ, 0 ≤ t → 0 ≤ h →
      ∫⁻ s in Icc t (t + h), hsE 3 (scaleU ν (α / ν) y s) ≤
        ENNReal.ofReal (ν * ⌈ν * h⌉ * B) := by
    intro t h ht hh
    rw [lintegral_scaleU hν (fun t ht => (hadm t ht).sol) ht]
    have hνh : 0 ≤ ν * h := mul_nonneg hν.le hh
    have hc := lintegral_cover (w := fun τ => hsE 3 (y τ)) (B := ENNReal.ofReal B)
      (fun x hx => unit_bound (majorized_filtN _ 0) (goodForce_filtG _ 0 hg) hy hx (hW x hx))
      (mul_nonneg hν.le ht) ⌈ν * h⌉₊
    have hsub : Icc (ν * t) (ν * (t + h)) ⊆ Icc (ν * t) (ν * t + ⌈ν * h⌉₊) :=
      Icc_subset_Icc_right (by rw [mul_add]; linarith [Nat.le_ceil (ν * h)])
    rw [← natCast_ceil_eq_intCast_ceil hνh,
      ENNReal.ofReal_mul (mul_nonneg hν.le (Nat.cast_nonneg _)), ENNReal.ofReal_mul hν.le,
      ENNReal.ofReal_natCast, mul_assoc]
    gcongr
    exact (lintegral_mono_set hsub).trans hc
  refine ⟨_, hS, fun u' hu' t ht => unique_scaleU hν hg hy h0 hu' ht, fun T hT => ?_,
    fun t ht => ?_, hwin, ?_⟩
  · have h := hwin 0 T le_rfl hT
    rw [zero_add] at h
    exact h.trans_lt ENNReal.ofReal_lt_top
  · have hτ : 0 ≤ ν * t := mul_nonneg hν.le ht
    have hs := (hadm _ hτ).sol
    obtain ⟨h1, h2⟩ := hB _ hτ
    simp only [scaleU, hnorm_smul, Complex.norm_real, Real.norm_of_nonneg hν.le, hnorm_rotF _ hs]
    exact ⟨mul_le_mul_of_nonneg_left h1 hν.le, mul_le_mul_of_nonneg_left h2 hν.le⟩
  · rintro rfl
    rw [smul_zero] at hy hg
    exact zero_force_scaleU hν hg hy h0 hS

end Helpers

end OVNS
