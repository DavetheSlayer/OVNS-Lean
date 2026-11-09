import OddViscousNS.Quant.Regimes.Algebra
import OddViscousNS.Gronwall

/-!
# Regimes layer, node 3: the virtual fast barrier (E10)

TeX quantitative_energies, "The virtual fast barrier and causal continuation"; spec §2.2 E10.
Proved here:
* `interp_fast`: the Sobolev interpolation `b_F² ≤ a_F c_F` for the fast part
  (`OVNS.hnorm_sq_le_mul` at `s = 2`), so `c_F ≥ b_F²/A` on a prefix with `a_F ≤ A`;
* `quadratic_peak`: off the barrier the damping term is at most `B² b_F²/(2d₀)`.
`virtual_damping` (on the barrier) is in `Algebra.lean`.
Proved: `barrier_cap`, the clipped last-contact comparison, with `0 < B` (false for `B = 0`; see
its docstring); the corrected `barrier_cap_of_pos` (`0 < B`) is proved at the end via a
signed-coefficient Gronwall for the discontinuous `W` (`le_duhamel`).  It is stated for a
*continuous* `b_F` (a solution property, see `Continuation.lean`) and the `H2EnergyInterface`
outputs `W, G, H`; `W` itself need not be continuous.  Its two conclusions are the ones the
bootstrap uses: on the first clip the incoming trace `W s` dominates, after a full clip the cap
`Y ≥ b_F` on the piece enters with the contraction factor `e^{m₀−1}·33/32` (`< 1` for
`m₀ ≤ 1/2`), plus a multiple of `W_*` — hence `b_F < y` for `y² ≳ max(b_F(s)², W_*)`.
-/

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace OVNS.Quant

/-- Sobolev interpolation for the fast part: `b_F² ≤ a_F c_F` whenever `F(t) ∈ H³`
(`OVNS.hnorm_sq_le_mul` at `s = 2`). -/
theorem interp_fast {r : ℝ} {g : Field} {y : ℝ → Field} {t : ℝ}
    (h3 : InH 3 (PiF (actual r g y t))) :
    fastNorm 2 r g y t ^ 2 ≤ fastNorm 1 r g y t * fastNorm 3 r g y t := by
  have h3' : InH ((2 : ℝ) + 1) (PiF (actual r g y t)) := by
    norm_num
    exact h3
  have := hnorm_sq_le_mul h3'
  norm_num at this
  exact this

/-- Off the barrier the damping term is bounded by its vertex value: for every `c`,
`−2d₀ c² + 2B b c ≤ B² b²/(2d₀)`. -/
theorem quadratic_peak (B b c : ℝ) :
    -2 * dZero * c ^ 2 + 2 * B * b * c ≤ B ^ 2 * b ^ 2 / (2 * dZero) := by
  unfold dZero
  rw [show B ^ 2 * b ^ 2 / (2 * (2 / 3)) = 3 / 4 * (B ^ 2 * b ^ 2) by ring]
  nlinarith [sq_nonneg (c - 3 / 4 * B * b)]

/-! ### Private helpers: signed Gronwall for a discontinuous `W` -/

/-- The exponential of an absolutely continuous function is absolutely continuous (a private
copy of the helper in `OddViscousNS.Gronwall`). -/
private lemma barrier_ac_exp {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (f x)) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨K, hK⟩ := (Real.contDiff_exp (n := 1)).contDiffOn.exists_lipschitzOnWith (by decide)
    (convex_Icc (-C) C) isCompact_Icc
  exact hK.comp_absolutelyContinuousOnInterval (fun x hx ↦ abs_le.1 (hC x hx)) hf

/-- Fundamental theorem of calculus for an absolutely continuous function with a given a.e.
derivative. -/
private lemma barrier_ac_integral_eq {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    ∫ x in a..b, g x = f b - f a := by
  rw [← hf.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hd] with x hx hxm
  exact (hx (uIoc_subset_uIcc hxm)).deriv.symm

/-- Duhamel's formula: the solution of `Z' = κ Z + β`, `Z a = c`, in integrated form. -/
private lemma barrier_duhamel {κ β : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hκ : IntervalIntegrable κ volume a b) (hβ : IntervalIntegrable β volume a b) (c : ℝ) :
    ∃ Z : ℝ → ℝ, ContinuousOn Z (Icc a b) ∧
      Z b = Real.exp (∫ u in a..b, κ u) * c +
        (∫ u in a..b, Real.exp (∫ v in u..b, κ v) * β u) ∧
      ∀ t ∈ Icc a b, Z t = c + ∫ u in a..t, (κ u * Z u + β u) := by
  have hmema : a ∈ uIcc a b := left_mem_uIcc
  set K : ℝ → ℝ := fun x ↦ ∫ v in a..x, κ v with hK
  have hKac : AbsolutelyContinuousOnInterval K a b :=
    hκ.absolutelyContinuousOnInterval_intervalIntegral hmema
  have hE : AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (K x)) a b := barrier_ac_exp hKac
  have hE' : AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (-K x)) a b := barrier_ac_exp hKac.neg
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
    have hfin := barrier_ac_integral_eq (hZac.mono hsub)
      (by filter_upwards [hderiv] with x hx hxm using hx (hsub hxm))
    have hK0 : K a = 0 := intervalIntegral.integral_same
    have hQ0 : Q a = 0 := intervalIntegral.integral_same
    simp only [hK0, hQ0, Real.exp_zero, one_mul, add_zero] at hfin
    rw [hfin]
    ring

/-- An upper bound by a nonnegative integrable function bounds the (possibly junk) integral. -/
private lemma integral_le_of_nonneg {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hg0 : ∀ u ∈ Icc a b, 0 ≤ g u)
    (hfg : ∀ u ∈ Icc a b, f u ≤ g u) : ∫ u in a..b, f u ≤ ∫ u in a..b, g u := by
  by_cases hf : IntervalIntegrable f volume a b
  · exact intervalIntegral.integral_mono_on hab hf hg hfg
  · rw [intervalIntegral.integral_undef hf]
    exact intervalIntegral.integral_nonneg hab hg0

/-- An integrable function times a bounded a.e.-measurable one is integrable. -/
private lemma mul_bdd_of_le {κ w : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hκ : IntervalIntegrable κ volume a b)
    (hw : AEStronglyMeasurable w (volume.restrict (Icc a b)))
    (hM : ∀ u ∈ Icc a b, |w u| ≤ M) :
    IntervalIntegrable (fun u => κ u * w u) volume a b := by
  rw [intervalIntegrable_iff, uIoc_of_le hab] at hκ ⊢
  have hw' : AEStronglyMeasurable w (volume.restrict (Ioc a b)) :=
    hw.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  refine Integrable.mono' (hκ.norm.mul_const M) (hκ.aestronglyMeasurable.mul hw') ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM u (Ioc_subset_Icc_self hu)) (abs_nonneg _)


/-- Comparison principle without continuity: if `z a ≤ 0` and `z t ≤ z s + ∫_s^t κ z` for all
`a ≤ s ≤ t ≤ b`, then `z ≤ 0` on `[a, b]`.  (Past the last nonpositive value `τ` the function
`z` is positive and dominated by the continuous `∫_τ^· |κ| z⁺`, which Gronwall kills.) -/
private lemma nonpos_of_le_integral' {z κ : ℝ → ℝ} {a b : ℝ}
    (hκ : IntervalIntegrable κ volume a b)
    (hκz : IntervalIntegrable (fun u => κ u * z u) volume a b)
    (hκz' : IntervalIntegrable (fun u => |κ u| * max (z u) 0) volume a b) (h0 : z a ≤ 0)
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b → z t ≤ z s + ∫ u in s..t, κ u * z u) :
    ∀ t, a ≤ t → t ≤ b → z t ≤ 0 := by
  intro u hau hub
  by_contra hpos
  push Not at hpos
  have hab : a ≤ b := hau.trans hub
  have hsub : ∀ c d, a ≤ c → c ≤ d → d ≤ b → uIcc c d ⊆ uIcc a b := fun c d hc hcd hd => by
    rw [uIcc_of_le hcd, uIcc_of_le hab]
    exact Icc_subset_Icc hc hd
  set S : Set ℝ := {r | r ∈ Icc a u ∧ z r ≤ 0} with hS
  have haS : a ∈ S := ⟨⟨le_rfl, hau⟩, h0⟩
  have hSne : S.Nonempty := ⟨a, haS⟩
  have hSbdd : BddAbove S := ⟨u, fun r hr => hr.1.2⟩
  set τ := sSup S with hτ
  have hτa : a ≤ τ := le_csSup hSbdd haS
  have hτu : τ ≤ u := csSup_le hSne fun r hr => hr.1.2
  have hzτ : z τ ≤ 0 := by
    by_contra hzτ
    push Not at hzτ
    have hPc : ContinuousOn (fun x => ∫ r in a..x, κ r * z r) (uIcc a b) :=
      intervalIntegral.continuousOn_primitive_interval' hκz left_mem_uIcc
    have hτm : τ ∈ uIcc a b := by
      rw [uIcc_of_le hab]
      exact ⟨hτa, hτu.trans hub⟩
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousOn_iff.1 hPc τ hτm (z τ) hzτ
    obtain ⟨r, hrS, hr⟩ := exists_lt_of_lt_csSup hSne (show τ - δ < τ by linarith)
    have hrτ : r ≤ τ := le_csSup hSbdd hrS
    have hkey := h r τ hrS.1.1 hrτ (hτu.trans hub)
    have hrm : r ∈ uIcc a b := by
      rw [uIcc_of_le hab]
      exact ⟨hrS.1.1, hrτ.trans (hτu.trans hub)⟩
    have hd := hδ' r hrm (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    have hsplit : ∫ x in r..τ, κ x * z x =
        (∫ x in a..τ, κ x * z x) - ∫ x in a..r, κ x * z x :=
      (intervalIntegral.integral_interval_sub_left (hκz.mono_set (hsub a τ le_rfl hτa
        (hτu.trans hub))) (hκz.mono_set (hsub a r le_rfl hrS.1.1
          (hrτ.trans (hτu.trans hub))))).symm
    rw [Real.dist_eq, abs_lt] at hd
    have := hrS.2
    linarith [hd.1]
  have hpos' : ∀ r, τ < r → r ≤ u → 0 < z r := by
    intro r h1 h2
    by_contra hn
    push Not at hn
    have := le_csSup hSbdd ⟨⟨hτa.trans h1.le, h2⟩, hn⟩
    linarith
  have hsubτ : uIcc τ u ⊆ uIcc a b := hsub τ u hτa hτu hub
  have hI' := hκz'.mono_set hsubτ
  set Φ : ℝ → ℝ := fun x => ∫ r in τ..x, |κ r| * max (z r) 0 with hΦ
  have hΦc : ContinuousOn Φ (Icc τ u) := by
    have := intervalIntegral.continuousOn_primitive_interval' hI' left_mem_uIcc
    rwa [uIcc_of_le hτu] at this
  have hsub2 : ∀ c d, τ ≤ c → c ≤ d → d ≤ u → uIcc c d ⊆ uIcc τ u := fun c d hc hcd hd => by
    rw [uIcc_of_le hcd, uIcc_of_le hτu]
    exact Icc_subset_Icc hc hd
  have hΦ0 : ∀ x ∈ Icc τ u, 0 ≤ Φ x := fun x hx =>
    intervalIntegral.integral_nonneg hx.1 fun r _ => mul_nonneg (abs_nonneg _) (le_max_right _ _)
  have hzΦ : ∀ x ∈ Icc τ u, z x ≤ Φ x := by
    intro x hx
    have h1 := h τ x hτa hx.1 (hx.2.trans hub)
    have h2 : ∫ r in τ..x, κ r * z r ≤ Φ x := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hx.1
        (hκz.mono_set (hsub τ x hτa hx.1 (hx.2.trans hub)))
        (hI'.mono_set (hsub2 τ x le_rfl hx.1 hx.2)) fun r hr => ?_
      have hzr := hpos' r hr.1 (hr.2.le.trans hx.2)
      rw [max_eq_left hzr.le]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hzr.le
    linarith
  have hall : ∀ c d, τ ≤ c → c ≤ d → d ≤ u →
      Φ d ≤ Φ c + ∫ x in c..d, (|κ x| * Φ x + 0) := by
    intro c d hc hcd hd
    have hadd : Φ d = Φ c + ∫ x in c..d, |κ x| * max (z x) 0 :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hI'.mono_set (hsub2 τ c le_rfl hc (hcd.trans hd)))
        (hI'.mono_set (hsub2 c d hc hcd hd))).symm
    rw [hadd]
    have hc' : ContinuousOn Φ (uIcc c d) := hΦc.mono (by
      rw [uIcc_of_le hcd]
      exact Icc_subset_Icc hc hd)
    have hm : ∫ x in c..d, |κ x| * max (z x) 0 ≤ ∫ x in c..d, (|κ x| * Φ x + 0) := by
      refine intervalIntegral.integral_mono_on hcd (hI'.mono_set (hsub2 c d hc hcd hd))
        (((hκ.abs.mono_set ((hsub2 c d hc hcd hd).trans hsubτ)).mul_continuousOn hc').add
          intervalIntegrable_const) fun x hx => ?_
      have hxm : x ∈ Icc τ u := ⟨hc.trans hx.1, hx.2.trans hd⟩
      rw [add_zero]
      exact mul_le_mul_of_nonneg_left (max_le (hzΦ x hxm) (hΦ0 x hxm)) (abs_nonneg _)
    linarith
  have hg := OVNS.gronwall_simple (κ := fun x => |κ x|) (β := fun _ => 0) hτu hΦc
    (hκ.abs.mono_set hsubτ) (fun _ => abs_nonneg _) intervalIntegrable_const (fun _ => le_rfl)
    hall τ u le_rfl hτu le_rfl
  have hΦτ : Φ τ = 0 := intervalIntegral.integral_same
  rw [hΦτ, intervalIntegral.integral_zero, add_zero, zero_mul] at hg
  linarith [hzΦ u ⟨hτu, le_rfl⟩]


/-- Signed-coefficient Gronwall for a bounded, a.e.-measurable (possibly discontinuous) `W`
satisfying the all-starts inequality `W t − W s ≤ ∫_s^t (κ W + β)`: `W b` is at most the value
of the Duhamel solution started from `W a`. -/
private lemma le_duhamel {W κ β : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hκ : IntervalIntegrable κ volume a b) (hβ : IntervalIntegrable β volume a b)
    (hW : AEStronglyMeasurable W (volume.restrict (Icc a b)))
    (hM : ∀ u ∈ Icc a b, |W u| ≤ M)
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b → W t - W s ≤ ∫ u in s..t, (κ u * W u + β u)) :
    W b ≤ Real.exp (∫ u in a..b, κ u) * W a +
      ∫ u in a..b, Real.exp (∫ v in u..b, κ v) * β u := by
  obtain ⟨Z, hZc, hZb, hZ⟩ := barrier_duhamel hab hκ hβ (W a)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hZc
  have hZm : AEStronglyMeasurable Z (volume.restrict (Icc a b)) :=
    hZc.aestronglyMeasurable measurableSet_Icc
  have hzm : AEStronglyMeasurable (fun u => W u - Z u) (volume.restrict (Icc a b)) := hW.sub hZm
  have hzb : ∀ u ∈ Icc a b, |W u - Z u| ≤ M + C := fun u hu =>
    (abs_sub _ _).trans (add_le_add (hM u hu) (by simpa using hC u hu))
  have hκz := mul_bdd_of_le hab hκ hzm hzb
  have hzm' : AEStronglyMeasurable (fun u => max (W u - Z u) 0) (volume.restrict (Icc a b)) :=
    hzm.sup aestronglyMeasurable_const
  have hκz' := mul_bdd_of_le hab hκ.abs hzm' (M := M + C) fun u hu => by
    have h1 := hzb u hu
    have h2 := le_abs_self (W u - Z u)
    have h3 : 0 ≤ M + C := (abs_nonneg _).trans h1
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (h2.trans h1) h3
  have hsubI : ∀ s t, a ≤ s → s ≤ t → t ≤ b → uIcc s t ⊆ uIcc a b := fun s t hs hst ht => by
    rw [uIcc_of_le hst, uIcc_of_le hab]
    exact Icc_subset_Icc hs ht
  have hWi : IntervalIntegrable (fun u => κ u * W u + β u) volume a b :=
    (mul_bdd_of_le hab hκ hW hM).add hβ
  have hZi : IntervalIntegrable (fun u => κ u * Z u + β u) volume a b :=
    (hκ.mul_continuousOn (by rwa [uIcc_of_le hab])).add hβ
  have key := nonpos_of_le_integral' (z := fun u => W u - Z u) hκ hκz hκz'
    (by simp [hZ a ⟨le_rfl, hab⟩]) (fun s t hs hst ht => by
      have hW' := h s t hs hst ht
      have hZs : Z t - Z s = ∫ u in s..t, (κ u * Z u + β u) := by
        rw [hZ t ⟨hs.trans hst, ht⟩, hZ s ⟨hs, hst.trans ht⟩, add_sub_add_left_eq_sub,
          intervalIntegral.integral_interval_sub_left
            (hZi.mono_set (hsubI a t le_rfl (hs.trans hst) ht))
            (hZi.mono_set (hsubI a s le_rfl hs (hst.trans ht)))]
      have hdiff : ∫ u in s..t, κ u * (W u - Z u) =
          (∫ u in s..t, (κ u * W u + β u)) - ∫ u in s..t, (κ u * Z u + β u) := by
        rw [← intervalIntegral.integral_sub (hWi.mono_set (hsubI s t hs hst ht))
          (hZi.mono_set (hsubI s t hs hst ht))]
        exact intervalIntegral.integral_congr fun u _ => by ring
      show W t - Z t ≤ W s - Z s + ∫ u in s..t, κ u * (W u - Z u)
      linarith) b hab le_rfl
  rw [← hZb]
  linarith


/-- Pointwise damping on and off the barrier: `−2d₀c² + 2Bbc ≤ −λ_* W + (3/2) λ_* W_*` for
every `W ≤ (33/32) b²` with `b² ≤ A c` (`virtual_damping` above `b_*`, the vertex bound
`quadratic_peak` below it, where `B² b²/(2d₀) ≤ λ_* W_*/2`). -/
private lemma damping_le {A B W bF cF : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hb0 : 0 ≤ bF)
    (hWu : W ≤ 33 / 32 * bF ^ 2) (hc : bF ^ 2 ≤ A * cF) :
    -2 * dZero * cF ^ 2 + 2 * B * bF * cF ≤
      -lamStar 1 A B * W + 3 / 2 * (lamStar 1 A B * WStar 1 A B) := by
  have hlW : lamStar 1 A B * WStar 1 A B = 3 / 2 * B ^ 2 * bStar 1 A B ^ 2 := by
    unfold lamStar WStar bStar dZero
    field_simp
  have hl0 : 0 ≤ lamStar 1 A B := by
    unfold lamStar dZero
    positivity
  have hb : 0 ≤ bStar 1 A B := by
    unfold bStar dZero
    positivity
  by_cases hbb : bStar 1 A B ≤ bF
  · have h := virtual_damping (cF := cF) le_rfl hA hB hWu (by rw [div_le_iff₀ hA]; linarith) hbb
    nlinarith [mul_nonneg hl0 (show 0 ≤ WStar 1 A B by unfold WStar; positivity)]
  · push Not at hbb
    have hq := quadratic_peak B bF cF
    have hsq : bF ^ 2 ≤ bStar 1 A B ^ 2 := pow_le_pow_left₀ hb0 hbb.le 2
    have hWs : W ≤ WStar 1 A B := by
      unfold WStar
      linarith
    have h1 : lamStar 1 A B * W ≤ lamStar 1 A B * WStar 1 A B :=
      mul_le_mul_of_nonneg_left hWs hl0
    have h2 : B ^ 2 * bF ^ 2 ≤ B ^ 2 * bStar 1 A B ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg B)
    unfold dZero at hq ⊢
    rw [show B ^ 2 * bF ^ 2 / (2 * (2 / 3)) = 3 / 4 * (B ^ 2 * bF ^ 2) by ring] at hq
    nlinarith


/-- Regularity of the `H²EnergyInterface`-shaped data: `W` is bounded and a.e.-measurable on
`[s, t]` (it differs from an antitone function by a continuous primitive) and the integrand of
the integrated inequality is integrable. -/
private lemma regularity {A B s t : ℝ} {W G H bF cF : ℝ → ℝ} (hA : 0 < A) (hst : s ≤ t)
    (hbc : ContinuousOn bF (Icc s t)) (hb0 : ∀ u, 0 ≤ bF u)
    (hco : ∀ u ∈ Icc s t, 31 / 32 * bF u ^ 2 ≤ W u ∧ W u ≤ 33 / 32 * bF u ^ 2)
    (hint : ∀ u ∈ Icc s t, bF u ^ 2 ≤ A * cF u)
    (hcI : IntervalIntegrable (fun u => cF u ^ 2) volume s t)
    (hineq : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
        W u₂ - W u₁ ≤ ∫ u in u₁..u₂,
          (-2 * dZero * cF u ^ 2 + 2 * B * bF u * cF u + G u * W u + H u))
    (hGH : ∀ u ∈ Icc s t, 0 ≤ G u ∧ 0 ≤ H u)
    (hGi : IntervalIntegrable G volume s t) (hHi : IntervalIntegrable H volume s t) :
    ∃ M, (∀ u ∈ Icc s t, |W u| ≤ M) ∧ AEStronglyMeasurable W (volume.restrict (Icc s t)) ∧
      IntervalIntegrable
        (fun u => -2 * dZero * cF u ^ 2 + 2 * B * bF u * cF u + G u * W u + H u) volume s t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hbc
  have hWM : ∀ u ∈ Icc s t, |W u| ≤ 33 / 32 * C ^ 2 := by
    intro u hu
    have h1 := hco u hu
    have h2 : bF u ≤ C := by
      have := hC u hu
      rwa [Real.norm_eq_abs, abs_of_nonneg (hb0 u)] at this
    have h3 : bF u ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (hb0 u) h2 2
    rw [abs_of_nonneg (by nlinarith)]
    linarith
  have hM0 : 0 ≤ 33 / 32 * C ^ 2 := by positivity
  -- `c_F` is integrable: it is the square root of `c_F²` on `[s, t]`
  have hcF : IntervalIntegrable cF volume s t := by
    have h1 : IntervalIntegrable (fun u => cF u ^ 2 + 1) volume s t :=
      hcI.add intervalIntegrable_const
    rw [intervalIntegrable_iff, uIoc_of_le hst] at hcI h1 ⊢
    have hm : AEStronglyMeasurable cF (volume.restrict (Ioc s t)) := by
      refine (Real.continuous_sqrt.comp_aestronglyMeasurable hcI.aestronglyMeasurable).congr ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
      have hc0 : 0 ≤ cF u := by
        have := hint u (Ioc_subset_Icc_self hu)
        nlinarith [sq_nonneg (bF u)]
      exact Real.sqrt_sq hc0
    refine Integrable.mono' h1 hm (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (cF u), sq_nonneg (|cF u| - 1)]
  have hbcF : IntervalIntegrable (fun u => bF u * cF u) volume s t :=
    hcF.continuousOn_mul (by rwa [uIcc_of_le hst])
  set F0 : ℝ → ℝ := fun u => -2 * dZero * cF u ^ 2 + 2 * B * bF u * cF u + H u with hF0
  have hF0i : IntervalIntegrable F0 volume s t := by
    have e : F0 = fun u => (-2 * dZero) * cF u ^ 2 + (2 * B) * (bF u * cF u) + H u := by
      funext u
      simp only [hF0]
      ring
    rw [e]
    exact ((hcI.const_mul _).add (hbcF.const_mul _)).add hHi
  set g0 : ℝ → ℝ := fun u => |F0 u| + G u * (33 / 32 * C ^ 2) with hg0
  have hg0i : IntervalIntegrable g0 volume s t := hF0i.abs.add (hGi.mul_const _)
  have hsubI : ∀ c d, s ≤ c → c ≤ d → d ≤ t → uIcc c d ⊆ uIcc s t := fun c d hc hcd hd => by
    rw [uIcc_of_le hcd, uIcc_of_le hst]
    exact Icc_subset_Icc hc hd
  have hstep : ∀ u₁ u₂, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      W u₂ - W u₁ ≤ ∫ u in u₁..u₂, g0 u := by
    intro u₁ u₂ h1 h12 h2
    refine (hineq u₁ u₂ h1 h12 h2).trans (integral_le_of_nonneg h12
      (hg0i.mono_set (hsubI u₁ u₂ h1 h12 h2)) (fun u hu => ?_) fun u hu => ?_)
    · have hu' : u ∈ Icc s t := ⟨h1.trans hu.1, hu.2.trans h2⟩
      exact add_nonneg (abs_nonneg _) (mul_nonneg (hGH u hu').1 hM0)
    · have hu' : u ∈ Icc s t := ⟨h1.trans hu.1, hu.2.trans h2⟩
      have hGW : G u * W u ≤ G u * (33 / 32 * C ^ 2) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hWM u hu')) (hGH u hu').1
      have := le_abs_self (F0 u)
      simp only [hg0, hF0] at this ⊢
      linarith
  set N : ℝ → ℝ := fun u => W u - ∫ x in s..u, g0 x with hN
  have hNa : AntitoneOn N (Icc s t) := by
    intro x hx y hy hxy
    have h1 := hstep x y hx.1 hxy hy.2
    have h2 := intervalIntegral.integral_interval_sub_left
      (hg0i.mono_set (hsubI s y le_rfl hy.1 hy.2)) (hg0i.mono_set (hsubI s x le_rfl hx.1 hx.2))
    simp only [hN]
    linarith
  have hNm : AEStronglyMeasurable N (volume.restrict (Icc s t)) :=
    (aemeasurable_restrict_of_antitoneOn measurableSet_Icc hNa).aestronglyMeasurable
  have hPc : ContinuousOn (fun u => ∫ x in s..u, g0 x) (Icc s t) := by
    have := intervalIntegral.continuousOn_primitive_interval' hg0i left_mem_uIcc
    rwa [uIcc_of_le hst] at this
  have hWm : AEStronglyMeasurable W (volume.restrict (Icc s t)) :=
    (hNm.add (hPc.aestronglyMeasurable measurableSet_Icc)).congr
      (Filter.Eventually.of_forall fun u => by simp [hN])
  refine ⟨_, hWM, hWm, ?_⟩
  have e : (fun u => -2 * dZero * cF u ^ 2 + 2 * B * bF u * cF u + G u * W u + H u) =
      fun u => F0 u + G u * W u := by
    funext u
    simp only [hF0]
    ring
  rw [e]
  exact hF0i.add (mul_bdd_of_le hst hGi hWm hWM)


/-- The clip estimate behind `barrier_cap`: for `B > 0` and `s ≤ a ≤ v ≤ t` with
`v − a ≤ 1/λ_*`, `W v ≤ e^{m₀ − λ_*(v−a)} W a + e^{m₀} (49/32) W_*`.  (Signed-coefficient
Gronwall `le_duhamel` with `κ = G − λ_*` and `β = (3/2) λ_* W_* + H`, from `damping_le`.) -/
private lemma clip_estimate {m₀ A B s t a v : ℝ} {W G H bF cF : ℝ → ℝ} (hA : 0 < A)
    (hB : 0 < B) (hst : s ≤ t)
    (hbc : ContinuousOn bF (Icc s t)) (hb0 : ∀ u, 0 ≤ bF u)
    (hco : ∀ u ∈ Icc s t, 31 / 32 * bF u ^ 2 ≤ W u ∧ W u ≤ 33 / 32 * bF u ^ 2)
    (hint : ∀ u ∈ Icc s t, bF u ^ 2 ≤ A * cF u)
    (hcI : IntervalIntegrable (fun u => cF u ^ 2) volume s t)
    (hineq : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
        W u₂ - W u₁ ≤ ∫ u in u₁..u₂,
          (-2 * dZero * cF u ^ 2 + 2 * B * bF u * cF u + G u * W u + H u))
    (hGH : ∀ u ∈ Icc s t, 0 ≤ G u ∧ 0 ≤ H u)
    (hGi : IntervalIntegrable G volume s t) (hHi : IntervalIntegrable H volume s t)
    (hclip : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ 1 / lamStar 1 A B →
        (∫ u in u₁..u₂, G u) ≤ m₀ ∧ (∫ u in u₁..u₂, H u) ≤ WStar 1 A B / 32)
    (ha : s ≤ a) (hav : a ≤ v) (hvt : v ≤ t) (hlen : v - a ≤ 1 / lamStar 1 A B) :
    W v ≤ Real.exp (m₀ - lamStar 1 A B * (v - a)) * W a +
      Real.exp m₀ * (49 / 32 * WStar 1 A B) := by
  obtain ⟨M, hWM, hWm, hfi⟩ := regularity hA hst hbc hb0 hco hint hcI hineq hGH hGi hHi
  set l := lamStar 1 A B with hl
  set Ws := WStar 1 A B with hWs
  have hl0 : 0 < l := by
    rw [hl]
    unfold lamStar bStar dZero
    positivity
  have hWs0 : 0 ≤ Ws := by
    rw [hWs]
    unfold WStar
    positivity
  have hsubI : ∀ c d, s ≤ c → c ≤ d → d ≤ t → uIcc c d ⊆ uIcc s t := fun c d hc hcd hd => by
    rw [uIcc_of_le hcd, uIcc_of_le hst]
    exact Icc_subset_Icc hc hd
  have hIcc : Icc a v ⊆ Icc s t := Icc_subset_Icc ha hvt
  have hκi : IntervalIntegrable (fun u => G u - l) volume s t := hGi.sub intervalIntegrable_const
  have hβi : IntervalIntegrable (fun u => 3 / 2 * (l * Ws) + H u) volume s t :=
    intervalIntegrable_const.add hHi
  have hgi : IntervalIntegrable (fun u => (G u - l) * W u + (3 / 2 * (l * Ws) + H u))
      volume s t := (mul_bdd_of_le hst hκi hWm hWM).add hβi
  have hsub := hsubI a v ha hav hvt
  have hd := le_duhamel (W := W) hav (hκi.mono_set hsub) (hβi.mono_set hsub)
    (hWm.mono_measure (Measure.restrict_mono hIcc le_rfl)) (fun u hu => hWM u (hIcc hu))
    (fun c d hc hcd hd => by
      have hsub' := hsubI c d (ha.trans hc) hcd (hd.trans hvt)
      refine (hineq c d (ha.trans hc) hcd (hd.trans hvt)).trans
        (intervalIntegral.integral_mono_on hcd (hfi.mono_set hsub') (hgi.mono_set hsub')
          fun u hu => ?_)
      have hu' : u ∈ Icc s t := ⟨(ha.trans hc).trans hu.1, hu.2.trans (hd.trans hvt)⟩
      have h1 := damping_le hA hB.le (hb0 u) (hco u hu').2 (hint u hu')
      have h2 : (G u - l) * W u = G u * W u - l * W u := by ring
      rw [← hl, ← hWs] at h1
      linarith)
  -- `∫_x^v (G − λ) = ∫_x^v G − λ (v − x)`
  have hκ : ∀ x ∈ Icc a v, ∫ u in x..v, (G u - l) = (∫ u in x..v, G u) - l * (v - x) := by
    intro x hx
    rw [intervalIntegral.integral_sub (hGi.mono_set (hsubI x v (ha.trans hx.1) hx.2 hvt))
      intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  have hlv : l * (v - a) ≤ 1 := by
    have := (le_div_iff₀ hl0).1 hlen
    linarith
  have hW0 : 0 ≤ W a := by
    have := hco a ⟨ha, hav.trans hvt⟩
    nlinarith [sq_nonneg (bF a)]
  have h1 : Real.exp (∫ u in a..v, (G u - l)) * W a ≤ Real.exp (m₀ - l * (v - a)) * W a := by
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hW0
    rw [hκ a ⟨le_rfl, hav⟩]
    linarith [(hclip a v ha hav hvt hlen).1]
  have h2 : ∫ u in a..v, Real.exp (∫ w in u..v, (G w - l)) * (3 / 2 * (l * Ws) + H u) ≤
      ∫ u in a..v, Real.exp m₀ * (3 / 2 * (l * Ws) + H u) := by
    refine integral_le_of_nonneg hav ((hβi.mono_set hsub).const_mul _) (fun u hu => ?_)
      fun u hu => ?_
    · have hu' : u ∈ Icc s t := hIcc hu
      exact mul_nonneg (Real.exp_pos _).le (add_nonneg (by positivity) (hGH u hu').2)
    · have hu' : u ∈ Icc s t := hIcc hu
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
        (add_nonneg (by positivity) (hGH u hu').2)
      rw [hκ u hu]
      have := (hclip u v hu'.1 hu.2 hvt (by linarith [hu.1])).1
      nlinarith [hu.2]
  have h3 : ∫ u in a..v, Real.exp m₀ * (3 / 2 * (l * Ws) + H u) ≤
      Real.exp m₀ * (49 / 32 * Ws) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
      (hHi.mono_set hsub), intervalIntegral.integral_const, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have := (hclip a v ha hav hvt hlen).2
    nlinarith [mul_le_mul_of_nonneg_right hlv hWs0]
  linarith


/-- **E10, clipped last-contact comparison for `B > 0`** (the corrected form of `barrier_cap`,
with `Cb = 3`).  Same conclusions as `barrier_cap`; the hypothesis `0 < B` makes `λ_* > 0`. -/
theorem barrier_cap_of_pos {m₀ : ℝ} (_hm₀ : 0 ≤ m₀) (hm₁ : m₀ ≤ 1 / 2) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ {A B s t : ℝ} {W G H bF cF : ℝ → ℝ}, 0 < A → 0 < B → s ≤ t →
      ContinuousOn bF (Icc s t) → (∀ u, 0 ≤ bF u) →
      (∀ u ∈ Icc s t, 31 / 32 * bF u ^ 2 ≤ W u ∧ W u ≤ 33 / 32 * bF u ^ 2) →
      (∀ u ∈ Icc s t, bF u ^ 2 ≤ A * cF u) →
      IntervalIntegrable (fun u => cF u ^ 2) volume s t →
      (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
        W u₂ - W u₁ ≤ ∫ u in u₁..u₂,
          (-2 * dZero * cF u ^ 2 + 2 * B * bF u * cF u + G u * W u + H u)) →
      (∀ u ∈ Icc s t, 0 ≤ G u ∧ 0 ≤ H u) →
      IntervalIntegrable G volume s t → IntervalIntegrable H volume s t →
      (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ 1 / lamStar 1 A B →
        (∫ u in u₁..u₂, G u) ≤ m₀ ∧ (∫ u in u₁..u₂, H u) ≤ WStar 1 A B / 32) →
      ∀ v ∈ Icc s t,
        (v - s ≤ 1 / lamStar 1 A B → W v ≤ Real.exp m₀ * (W s + Cb * WStar 1 A B)) ∧
        (1 / lamStar 1 A B ≤ v - s → ∀ Y : ℝ, (∀ u ∈ Icc s t, bF u ≤ Y) →
          W v ≤ Real.exp (m₀ - 1) * (33 / 32) * Y ^ 2 + Cb * WStar 1 A B) := by
  refine ⟨3, by norm_num, ?_⟩
  intro A B s t W G H bF cF hA hB hst hbc hb0 hco hint hcI hineq hGH hGi hHi hclip v hv
  have hce := fun a (ha : s ≤ a) (hav : a ≤ v) (hlen : v - a ≤ 1 / lamStar 1 A B) =>
    clip_estimate (m₀ := m₀) hA hB hst hbc hb0 hco hint hcI hineq hGH hGi hHi hclip ha hav
      hv.2 hlen
  have hl0 : 0 < lamStar 1 A B := by
    unfold lamStar bStar dZero
    positivity
  have hWs0 : 0 ≤ WStar 1 A B := by
    unfold WStar
    positivity
  have hexp : Real.exp m₀ * (49 / 32) ≤ 3 := by
    have h1 : Real.exp m₀ ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 hm₁
    have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 := Real.exp_one_lt_d9
    have h4 := Real.exp_pos (1 / 2)
    nlinarith
  have hW0 : ∀ u ∈ Icc s t, 0 ≤ W u := fun u hu => by
    have := hco u hu
    nlinarith [sq_nonneg (bF u)]
  have hrest : Real.exp m₀ * (49 / 32 * WStar 1 A B) ≤ 3 * WStar 1 A B := by
    nlinarith
  constructor
  · intro hlen
    have h1 := hce s le_rfl hv.1 hlen
    have h2 : Real.exp (m₀ - lamStar 1 A B * (v - s)) * W s ≤ Real.exp m₀ * W s := by
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hW0 s ⟨le_rfl, hst⟩)
      nlinarith [hv.1]
    have h3 : Real.exp m₀ * (49 / 32 * WStar 1 A B) ≤ Real.exp m₀ * (3 * WStar 1 A B) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    nlinarith
  · intro hlen Y hY
    set a := v - 1 / lamStar 1 A B with ha_def
    have ha : s ≤ a := by linarith
    have hav : a ≤ v := by
      have : 0 ≤ 1 / lamStar 1 A B := by positivity
      linarith
    have h1 := hce a ha hav (by rw [ha_def]; linarith)
    have hla : lamStar 1 A B * (v - a) = 1 := by
      rw [ha_def]
      field_simp
      ring
    rw [hla] at h1
    have haI : a ∈ Icc s t := ⟨ha, hav.trans hv.2⟩
    have hWa : W a ≤ 33 / 32 * Y ^ 2 := by
      have h2 := (hco a haI).2
      have h3 : bF a ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ (hb0 a) (hY a haI) 2
      linarith
    have h4 : Real.exp (m₀ - 1) * W a ≤ Real.exp (m₀ - 1) * (33 / 32 * Y ^ 2) :=
      mul_le_mul_of_nonneg_left hWa (Real.exp_pos _).le
    nlinarith


/-- **E10, clipped last-contact comparison** (locked; TeX "Integrating the positive part of
(quant-virtual) backward from a last contact, or over a full final clip with the true initial
trace").  For `m₀ ≤ 1/2` there is `Cb` such that for every `H2EnergyInterface`-shaped data on
`[s, t]` (coercivity, integrated inequality with `A > 0`, `B ≥ 0`, interpolation `b_F² ≤ A c_F`,
clip masses `∫G ≤ m₀`, `∫H ≤ W_*/32` on clips of length `≤ 1/λ_*`) with `b_F` continuous:
* within the first clip, `W v ≤ e^{m₀} (W s + Cb W_*)`;
* after a full clip, `W v ≤ e^{m₀−1} (33/32) Y² + Cb W_*` for every pointwise cap `Y ≥ b_F` on
  `[s, t]` (the cap `y` of the prefix).
Proof sketch: with `D = −2d₀c_F² + 2Bb_Fc_F`, `virtual_damping` gives `D ≤ −λ_*(W − W_*)`
whenever `W > W_*` (then `b_F > b_*` by coercivity) and `quadratic_peak` gives
`D ≤ B²b_F²/(2d₀) ≤ (33/62) λ_* W_*` otherwise; the last `b_F`-contact before `v` (a closed-set
`sSup` as in `first_exit`) splits the clip; `gronwall_fixed_start` on `Φ = b_F²` through the
coercivity gives the `e^{m₀}` factors, and `gronwall_decay`-type decay over a contact-free full
clip gives `e^{−1}`.
**False as stated for `B = 0`** (then `λ_* = W_* = 0` and `1/λ_* = 0`, so the clip masses
constrain nothing): `A = 1`, `s = 0`, `t = v = Y = 1`, `b_F = c_F = W = 1`, `G = 0`, `H = 4/3`
satisfy every hypothesis but `1 ≤ e^{m₀−1}·33/32` fails.  The corrected statement (`0 < B`,
`Cb = 3`) is `barrier_cap_of_pos` below, proved without a contact argument. -/
theorem barrier_cap {m₀ : ℝ} (hm₀ : 0 ≤ m₀) (hm₁ : m₀ ≤ 1 / 2) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ {A B s t : ℝ} {W G H bF cF : ℝ → ℝ}, 0 < A → 0 < B → s ≤ t →
      ContinuousOn bF (Icc s t) → (∀ u, 0 ≤ bF u) →
      (∀ u ∈ Icc s t, 31 / 32 * bF u ^ 2 ≤ W u ∧ W u ≤ 33 / 32 * bF u ^ 2) →
      (∀ u ∈ Icc s t, bF u ^ 2 ≤ A * cF u) →
      IntervalIntegrable (fun u => cF u ^ 2) volume s t →
      (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
        W u₂ - W u₁ ≤ ∫ u in u₁..u₂,
          (-2 * dZero * cF u ^ 2 + 2 * B * bF u * cF u + G u * W u + H u)) →
      (∀ u ∈ Icc s t, 0 ≤ G u ∧ 0 ≤ H u) →
      IntervalIntegrable G volume s t → IntervalIntegrable H volume s t →
      (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ 1 / lamStar 1 A B →
        (∫ u in u₁..u₂, G u) ≤ m₀ ∧ (∫ u in u₁..u₂, H u) ≤ WStar 1 A B / 32) →
      ∀ v ∈ Icc s t,
        (v - s ≤ 1 / lamStar 1 A B → W v ≤ Real.exp m₀ * (W s + Cb * WStar 1 A B)) ∧
        (1 / lamStar 1 A B ≤ v - s → ∀ Y : ℝ, (∀ u ∈ Icc s t, bF u ≤ Y) →
          W v ≤ Real.exp (m₀ - 1) * (33 / 32) * Y ^ 2 + Cb * WStar 1 A B) := by
  exact barrier_cap_of_pos hm₀ hm₁

end OVNS.Quant

end
