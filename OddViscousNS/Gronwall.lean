import Mathlib

/-! # Integrated Gronwall inequalities -/

open MeasureTheory Set intervalIntegral
noncomputable section
namespace OVNS

/-- Contraction form of the comparison principle: a continuous `D` with `D a ≤ 0` and
`D t - D s ≤ ∫_s^t κ D` stays nonpositive. Past the last zero `t₀` before a positive value, pick an
interval on which `∫ |κ| ≤ 1/2`; the maximum `A > 0` of `D` there satisfies `A ≤ A / 2`. -/
private lemma nonpos_of_le_integral {D κ : ℝ → ℝ} {a b : ℝ}
    (hD : ContinuousOn D (Icc a b)) (hκ : IntervalIntegrable κ volume a b) (h0 : D a ≤ 0)
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b → D t ≤ D s + ∫ u in s..t, κ u * D u) :
    ∀ t, a ≤ t → t ≤ b → D t ≤ 0 := by
  intro t1 hat1 ht1b
  by_contra hpos
  push Not at hpos
  have hsub : Icc a t1 ⊆ Icc a b := Icc_subset_Icc_right ht1b
  have hclosed : IsClosed (Icc a t1 ∩ D ⁻¹' Iic 0) :=
    (hD.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  obtain ⟨t0, ⟨ht0, hDt0⟩, hmax⟩ :=
    (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).exists_isGreatest
      ⟨a, left_mem_Icc.2 hat1, h0⟩
  have hDt0' : D t0 ≤ 0 := hDt0
  have ht01 : t0 < t1 := lt_of_le_of_ne ht0.2 (by rintro rfl; linarith)
  have hDpos : ∀ u, t0 < u → u ≤ t1 → 0 < D u := by
    intro u h1 h2
    by_contra hn
    have := hmax ⟨⟨ht0.1.trans h1.le, h2⟩, not_lt.1 hn⟩
    linarith
  have hab' : a ≤ b := hat1.trans ht1b
  have hsub' : Icc t0 t1 ⊆ uIcc a b := by
    rw [uIcc_of_le hab']
    exact Icc_subset_Icc ht0.1 ht1b
  have habs : IntervalIntegrable (fun u ↦ |κ u|) volume a b := hκ.abs
  have hmemb : t0 ∈ uIcc a b := hsub' (left_mem_Icc.2 ht01.le)
  have hcont : ContinuousOn (fun t ↦ ∫ u in t0..t, |κ u|) (Icc t0 t1) :=
    (intervalIntegral.continuousOn_primitive_interval' habs hmemb).mono hsub'
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousOn_iff.1 hcont t0 (left_mem_Icc.2 ht01.le) (1 / 2)
    (by norm_num)
  obtain ⟨t2, ht02, ht21, hsmall⟩ : ∃ t2, t0 < t2 ∧ t2 ≤ t1 ∧ ∫ u in t0..t2, |κ u| ≤ 1 / 2 := by
    refine ⟨min t1 (t0 + δ / 2), lt_min ht01 (by linarith), min_le_left _ _, ?_⟩
    have hle : min t1 (t0 + δ / 2) ≤ t0 + δ / 2 := min_le_right _ _
    have hgt : t0 < min t1 (t0 + δ / 2) := lt_min ht01 (by linarith)
    have hd := hδ' (min t1 (t0 + δ / 2)) ⟨hgt.le, min_le_left _ _⟩ (by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith)
    simp only [intervalIntegral.integral_same, Real.dist_eq, sub_zero] at hd
    exact (le_abs_self _).trans hd.le
  have hsub2 : Icc t0 t2 ⊆ Icc a b :=
    (Icc_subset_Icc_right ht21).trans (by rw [← uIcc_of_le hab']; exact hsub')
  obtain ⟨ts, hts, hmaxD⟩ := isCompact_Icc.exists_isMaxOn ⟨t0, left_mem_Icc.2 ht02.le⟩
    (hD.mono hsub2)
  have hA : 0 < D ts :=
    (hDpos t2 ht02 ht21).trans_le (hmaxD (right_mem_Icc.2 ht02.le))
  have hkey := h t0 ts ht0.1 hts.1 ((hts.2.trans ht21).trans ht1b)
  have hint0 : ∀ c d, c ∈ Icc t0 t2 → d ∈ Icc t0 t2 → IntervalIntegrable κ volume c d :=
    fun c d hc hd ↦ hκ.mono_set (by
      rw [uIcc_of_le hab']
      exact uIcc_subset_Icc (hsub2 hc) (hsub2 hd))
  have hints := hint0 t0 ts (left_mem_Icc.2 ht02.le) hts
  have hDcont : ContinuousOn D (uIcc t0 ts) := hD.mono (by
    rw [uIcc_of_le hts.1]
    exact (Icc_subset_Icc_right hts.2).trans hsub2)
  have hle1 : ∫ u in t0..ts, κ u * D u ≤ ∫ u in t0..ts, |κ u| * D ts := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hts.1 (hints.mul_continuousOn hDcont)
      (hints.abs.mul_const _) fun u hu ↦ ?_
    have hu2 : u ∈ Icc t0 t2 := ⟨hu.1.le, hu.2.le.trans hts.2⟩
    have hDu := hDpos u hu.1 (hu2.2.trans ht21)
    have hDle : D u ≤ D ts := hmaxD hu2
    calc κ u * D u ≤ |κ u| * D u := mul_le_mul_of_nonneg_right (le_abs_self _) hDu.le
      _ ≤ |κ u| * D ts := mul_le_mul_of_nonneg_left hDle (abs_nonneg _)
  have hle2 : ∫ u in t0..ts, |κ u| ≤ ∫ u in t0..t2, |κ u| :=
    intervalIntegral.integral_mono_interval le_rfl hts.1 hts.2
      (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
      (hint0 t0 t2 (left_mem_Icc.2 ht02.le) (right_mem_Icc.2 ht02.le)).abs
  rw [intervalIntegral.integral_mul_const] at hle1
  have hle3 : (∫ u in t0..ts, |κ u|) * D ts ≤ 1 / 2 * D ts :=
    mul_le_mul_of_nonneg_right (hle2.trans hsmall) hA.le
  linarith

/-- The exponential of an absolutely continuous function is absolutely continuous. -/
private lemma ac_exp {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (f x)) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨K, hK⟩ := (Real.contDiff_exp (n := 1)).contDiffOn.exists_lipschitzOnWith (by decide)
    (convex_Icc (-C) C) isCompact_Icc
  exact hK.comp_absolutelyContinuousOnInterval (fun x hx ↦ abs_le.1 (hC x hx)) hf

/-- Fundamental theorem of calculus for an absolutely continuous function with a given a.e.
derivative. -/
private lemma ac_integral_eq {f g : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    ∫ x in a..b, g x = f b - f a := by
  rw [← hf.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hd] with x hx hxm
  exact (hx (uIoc_subset_uIcc hxm)).deriv.symm

/-- Duhamel's formula: the solution of `Z' = κ Z + β`, `Z a = c`, in integrated form. -/
private lemma exists_duhamel {κ β : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hκ : IntervalIntegrable κ volume a b) (hβ : IntervalIntegrable β volume a b) (c : ℝ) :
    ∃ Z : ℝ → ℝ, ContinuousOn Z (Icc a b) ∧
      Z b = Real.exp (∫ u in a..b, κ u) * c +
        (∫ u in a..b, Real.exp (∫ v in u..b, κ v) * β u) ∧
      ∀ t ∈ Icc a b, Z t = c + ∫ u in a..t, (κ u * Z u + β u) := by
  have hmema : a ∈ uIcc a b := left_mem_uIcc
  set K : ℝ → ℝ := fun x ↦ ∫ v in a..x, κ v with hK
  have hKac : AbsolutelyContinuousOnInterval K a b :=
    hκ.absolutelyContinuousOnInterval_intervalIntegral hmema
  have hE : AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (K x)) a b := ac_exp hKac
  have hE' : AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (-K x)) a b := ac_exp hKac.neg
  have hg : IntervalIntegrable (fun u ↦ Real.exp (-K u) * β u) volume a b :=
    hβ.continuousOn_mul hE'.continuousOn
  set Q : ℝ → ℝ := fun x ↦ ∫ u in a..x, Real.exp (-K u) * β u with hQ
  have hQac : AbsolutelyContinuousOnInterval Q a b :=
    hg.absolutelyContinuousOnInterval_intervalIntegral hmema
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) a b :=
    (contDiffOn_const (c := c)).absolutelyContinuousOnInterval
  have hZac : AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (K x) * (c + Q x)) a b :=
    hE.fun_mul (hc.add hQac)
  have hderiv : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (fun x ↦ Real.exp (K x) * (c + Q x))
      (κ x * (Real.exp (K x) * (c + Q x)) + β x) x := by
    filter_upwards [hκ.ae_hasDerivAt_integral, hg.ae_hasDerivAt_integral] with x h1 h2 hx
    have h3 : HasDerivAt K (κ x) x := h1 hx a hmema
    have h4 : HasDerivAt Q (Real.exp (-K x) * β x) x := h2 hx a hmema
    have h5 := (h3.exp).mul (h4.const_add c)
    refine h5.congr_deriv ?_
    have h6 : Real.exp (K x) * Real.exp (-K x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    linear_combination β x * h6
  refine ⟨fun x ↦ Real.exp (K x) * (c + Q x), ?_, ?_, ?_⟩
  · simpa [uIcc_of_le hab] using hZac.continuousOn
  · show Real.exp (K b) * (c + Q b) = _
    have hQb : Q b = ∫ u in a..b, Real.exp (-K u) * β u := rfl
    have hKb : ∫ u in a..b, κ u = K b := rfl
    have hcong : ∫ u in a..b, Real.exp (∫ v in u..b, κ v) * β u =
        ∫ u in a..b, Real.exp (K b) * (Real.exp (-K u) * β u) := by
      refine intervalIntegral.integral_congr fun u hu ↦ ?_
      have hu' : IntervalIntegrable κ volume a u :=
        hκ.mono_set (uIcc_subset_uIcc_left hu)
      have hsplit : ∫ v in u..b, κ v = K b - K u :=
        (intervalIntegral.integral_interval_sub_left hκ hu').symm
      simp only [hsplit, sub_eq_add_neg, Real.exp_add, mul_assoc]
    rw [hcong, hKb, intervalIntegral.integral_const_mul, ← hQb, mul_add]
  · intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le hab, uIcc_of_le ht.1]
      exact Icc_subset_Icc_right ht.2
    have hfin := ac_integral_eq (hZac.mono hsub)
      (by filter_upwards [hderiv] with x hx hxm using hx (hsub hxm))
    have hK0 : K a = 0 := intervalIntegral.integral_same
    have hQ0 : Q a = 0 := intervalIntegral.integral_same
    simp only [hK0, hQ0, Real.exp_zero, one_mul, add_zero] at hfin
    rw [hfin]
    ring

/-- `gronwall_integrated` on a whole interval, with `s = a` and `t = b`. -/
private lemma gronwall_core {y κ β : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b)) (hκ : IntervalIntegrable κ volume a b)
    (hβ : IntervalIntegrable β volume a b)
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b → y t ≤ y s + ∫ u in s..t, (κ u * y u + β u)) :
    y b ≤ Real.exp (∫ u in a..b, κ u) * y a +
      ∫ u in a..b, Real.exp (∫ v in u..b, κ v) * β u := by
  obtain ⟨Z, hZc, hZb, hZ⟩ := exists_duhamel hab hκ hβ (y a)
  have hsubI : ∀ s t, a ≤ s → s ≤ t → t ≤ b → uIcc s t ⊆ uIcc a b := fun s t hs hst ht ↦ by
    rw [uIcc_of_le hst, uIcc_of_le hab]
    exact Icc_subset_Icc hs ht
  have hint : ∀ {w : ℝ → ℝ}, ContinuousOn w (Icc a b) → ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      IntervalIntegrable (fun u ↦ κ u * w u + β u) volume s t := fun hw s t hs hst ht ↦ by
    have hsub := hsubI s t hs hst ht
    refine ((hκ.mono_set hsub).mul_continuousOn (hw.mono ?_)).add (hβ.mono_set hsub)
    rwa [uIcc_of_le hab] at hsub
  have hD : ∀ t, a ≤ t → t ≤ b → y t - Z t ≤ 0 := by
    refine nonpos_of_le_integral (hy.sub hZc) hκ ?_ ?_
    · rw [hZ a (left_mem_Icc.2 hab)]
      simp
    · intro s t hs hst ht
      have hys := h s t hs hst ht
      have hZs : Z t = Z s + ∫ u in s..t, (κ u * Z u + β u) := by
        rw [hZ t ⟨hs.trans hst, ht⟩, hZ s ⟨hs, hst.trans ht⟩,
          ← intervalIntegral.integral_add_adjacent_intervals (b := s)
            (hint hZc a s le_rfl hs (hst.trans ht)) (hint hZc s t hs hst ht)]
        ring
      have hdiff : ∫ u in s..t, κ u * (y u - Z u) =
          (∫ u in s..t, (κ u * y u + β u)) - ∫ u in s..t, (κ u * Z u + β u) := by
        rw [← intervalIntegral.integral_sub (hint hy s t hs hst ht) (hint hZc s t hs hst ht)]
        exact intervalIntegral.integral_congr fun u _ ↦ by ring
      rw [hdiff]
      linarith
  have := hD b hab le_rfl
  rw [hZb] at this
  linarith

/-- Integrated linear Gronwall with a signed integrable coefficient. -/
theorem gronwall_integrated {y κ β : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b)) (hκ : IntervalIntegrable κ volume a b)
    (hβ : IntervalIntegrable β volume a b)
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b → y t ≤ y s + ∫ u in s..t, (κ u * y u + β u)) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      y t ≤ Real.exp (∫ u in s..t, κ u) * y s +
        ∫ u in s..t, Real.exp (∫ v in u..t, κ v) * β u := by
  intro s t hs hst ht
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le hst, uIcc_of_le hab]
    exact Icc_subset_Icc hs ht
  exact gronwall_core hst (hy.mono (Icc_subset_Icc hs ht)) (hκ.mono_set hsub) (hβ.mono_set hsub)
    fun s' t' hs' hst' ht' ↦ h s' t' (hs.trans hs') hst' (ht'.trans ht)

/-- The form with a nonnegative coefficient and nonnegative force. -/
theorem gronwall_simple {y κ β : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b)) (hκ : IntervalIntegrable κ volume a b)
    (hκ0 : ∀ u, 0 ≤ κ u) (hβ : IntervalIntegrable β volume a b) (hβ0 : ∀ u, 0 ≤ β u)
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b → y t ≤ y s + ∫ u in s..t, (κ u * y u + β u)) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      y t ≤ (y s + ∫ u in s..t, β u) * Real.exp (∫ u in s..t, κ u) := by
  intro s t hs hst ht
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le hst, uIcc_of_le hab]
    exact Icc_subset_Icc hs ht
  have hκ' := hκ.mono_set hsub
  have hβ' := hβ.mono_set hsub
  have h1 := gronwall_integrated hab hy hκ hβ h s t hs hst ht
  have hE : ContinuousOn (fun u ↦ Real.exp (∫ v in u..t, κ v)) (uIcc s t) :=
    (intervalIntegral.continuousOn_primitive_interval_left
      (by rwa [uIcc_of_le hst, ← intervalIntegrable_iff_integrableOn_Icc_of_le hst])).rexp
  have h2 : ∫ u in s..t, Real.exp (∫ v in u..t, κ v) * β u ≤
      ∫ u in s..t, Real.exp (∫ v in s..t, κ v) * β u := by
    refine intervalIntegral.integral_mono_on hst (hβ'.continuousOn_mul hE) (hβ'.const_mul _)
      fun u hu ↦ mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hβ0 u)
    exact intervalIntegral.integral_mono_interval hu.1 hu.2 le_rfl
      (Filter.Eventually.of_forall hκ0) hκ'
  rw [intervalIntegral.integral_const_mul] at h2
  linarith

/-- Exponential decay from `y' + λ y ≤ β` (constant `β ≥ 0`, `λ > 0`), integrated form. -/
theorem gronwall_decay {y : ℝ → ℝ} {a b lam β : ℝ} (hab : a ≤ b) (hlam : 0 < lam) (hβ : 0 ≤ β)
    (hy : ContinuousOn y (Icc a b))
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b → y t + lam * ∫ u in s..t, y u ≤ y s + β * (t - s)) :
    ∀ t, a ≤ t → t ≤ b → y t ≤ Real.exp (-lam * (t - a)) * y a + β / lam := by
  intro t hat htb
  have hyi : ∀ s t', a ≤ s → s ≤ t' → t' ≤ b → IntervalIntegrable y volume s t' :=
    fun s t' hs hst ht ↦ ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le hst]
      exact hy.mono (Icc_subset_Icc hs ht))
  have h1 := gronwall_integrated (y := y) (κ := fun _ ↦ -lam) (β := fun _ ↦ β) hab hy
    intervalIntegrable_const intervalIntegrable_const (fun s t' hs hst ht ↦ by
      have h0 := h s t' hs hst ht
      rw [intervalIntegral.integral_add ((hyi s t' hs hst ht).const_mul _)
        intervalIntegrable_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul]
      linarith) a t le_rfl hat htb
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h1
  have h2 : ∫ u in a..t, Real.exp ((t - u) * -lam) * β =
      β / lam - β / lam * Real.exp ((t - a) * -lam) := by
    have hF : ∀ u ∈ uIcc a t, HasDerivAt (fun u ↦ β / lam * Real.exp ((t - u) * -lam))
        (Real.exp ((t - u) * -lam) * β) u := fun u _ ↦ by
      have h3 : HasDerivAt (fun u ↦ (t - u) * -lam) lam u := by
        simpa using ((hasDerivAt_id u).const_sub t).mul_const (-lam)
      refine (h3.exp.const_mul (β / lam)).congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp
  have h3 : 0 ≤ β / lam * Real.exp ((t - a) * -lam) := by positivity
  rw [show -lam * (t - a) = (t - a) * -lam by ring]
  linarith

/-- The uniform Gronwall lemma on a unit interval: if `y' ≤ κ y + β`, then
`y(t) ≤ (∫_{t-1}^t y + ∫_{t-1}^t β) exp ∫_{t-1}^t κ`. -/
theorem uniform_gronwall {y κ β : ℝ → ℝ} {t : ℝ} (hy : ContinuousOn y (Icc (t - 1) t))
    (hy0 : ∀ u, 0 ≤ y u) (hκ : IntervalIntegrable κ volume (t - 1) t) (hκ0 : ∀ u, 0 ≤ κ u)
    (hβ : IntervalIntegrable β volume (t - 1) t) (hβ0 : ∀ u, 0 ≤ β u)
    (h : ∀ s t', t - 1 ≤ s → s ≤ t' → t' ≤ t → y t' ≤ y s + ∫ u in s..t', (κ u * y u + β u)) :
    y t ≤ ((∫ u in (t - 1)..t, y u) + ∫ u in (t - 1)..t, β u) *
      Real.exp (∫ u in (t - 1)..t, κ u) := by
  have hle : t - 1 ≤ t := by linarith
  have hyi : IntervalIntegrable y volume (t - 1) t :=
    ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le hle])
  have hint : ∀ {f : ℝ → ℝ}, (∀ u, 0 ≤ f u) → IntervalIntegrable f volume (t - 1) t →
      ∀ s ∈ Icc (t - 1) t, ∫ u in s..t, f u ≤ ∫ u in (t - 1)..t, f u := fun hf0 hfi s hs ↦
    intervalIntegral.integral_mono_interval hs.1 hs.2 le_rfl
      (Filter.Eventually.of_forall hf0) hfi
  have key : ∀ s ∈ Icc (t - 1) t, y t ≤ (y s + ∫ u in (t - 1)..t, β u) *
      Real.exp (∫ u in (t - 1)..t, κ u) := fun s hs ↦ by
    refine (gronwall_simple hle hy hκ hκ0 hβ hβ0 h s t hs.1 hs.2 le_rfl).trans ?_
    have hB := add_le_add_right (hint hβ0 hβ s hs) (y s)
    have hnn : 0 ≤ y s + ∫ u in s..t, β u :=
      add_nonneg (hy0 s) (intervalIntegral.integral_nonneg hs.2 fun u _ ↦ hβ0 u)
    exact mul_le_mul hB (Real.exp_le_exp.2 (hint hκ0 hκ s hs)) (Real.exp_pos _).le
      (hnn.trans hB)
  have hmono := intervalIntegral.integral_mono_on hle intervalIntegrable_const
    ((hyi.add intervalIntegrable_const).mul_const _) key
  rw [intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add hyi intervalIntegrable_const,
    intervalIntegral.integral_const] at hmono
  simpa using hmono

end OVNS
