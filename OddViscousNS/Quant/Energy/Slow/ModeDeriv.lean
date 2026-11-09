import OddViscousNS.Quant.Energy.Slow.Continuity

/-!
# E7-F, the mode derivative of the kinetic primitive along the actual solution

The derivative `R_S' = Π_S Q_{rt}(F,F) + 2N(F',F)` of the corrector `R_S = N(F,F)`
(`Equation.lean`), mode by mode.  The `p`-sum of a mode of `N` is differentiated in integrated form:
each summand is differentiated by the product rule, the derivative summands are absolutely summable
with a sum bounded on compacts by `‖F‖₁‖F‖₀ + (1/q)‖F'‖_{ℓ²}‖F‖_{ℓ²}` (no term-by-term domination
in time is available: the `ℓ¹`-majorant of the `p`-sum moves with the solution), and the
right-hand side is continuous.

## Contents
* `integral_tsum_deriv'`: the vector-valued version of `integral_tsum_deriv`.
* `triV`, the `p`-summand of `Q^♯_m(f,g)_k`; `hasDerivWithinAt_triV`: its product rule;
  `triV_kinDM_eq`: on a slow output with fast inputs the derivative multiplier acts as the phase
  (the slow-output resonant null).
* `kinN_sub_left`, `kinN_sub_right`: bilinearity of the primitive on `ℓ²`;
  `continuous_kinN_frozen`, `continuousOn_kinN_mode`: its mode-continuity along `ℓ²`-continuous
  paths.
* `hasDerivWithinAt_kinN_fast`: the mode derivative of `N(F,F)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace OVNS

/-! ### The FTC for a summable vector-valued family -/

/-- **Fundamental theorem of calculus for a summable family of differentiable vector-valued
functions** (the vector-valued form of `integral_tsum_deriv`). -/
theorem integral_tsum_deriv' {ι E : Type*} [Countable ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {T T' : ℝ → ι → E} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ i, ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => T u i) (T' t i) (Icc a b) t)
    (hc : ∀ i, ContinuousOn (fun u => T' u i) (Icc a b))
    (hsa : Summable fun i => T a i) (hsb : Summable fun i => T b i)
    {C : ℝ} (hB : ∀ u ∈ Icc a b, Summable (fun i => ‖T' u i‖) ∧ ∑' i, ‖T' u i‖ ≤ C) :
    (∑' i, T b i) - ∑' i, T a i = ∫ u in a..b, ∑' i, T' u i := by
  have hfin : ∀ S : Finset ι,
      (∑ i ∈ S, T b i) - ∑ i ∈ S, T a i = ∫ u in a..b, ∑ i ∈ S, T' u i := by
    intro S
    have hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => ∑ i ∈ S, T u i)
        (∑ i ∈ S, T' t i) (Icc a b) t :=
      fun t ht => HasDerivWithinAt.fun_sum fun i _ => hd i t ht
    have hcont : ContinuousOn (fun u => ∑ i ∈ S, T' u i) (Icc a b) :=
      continuousOn_finsetSum S fun i _ => hc i
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (fun t ht => (hderiv t ht).continuousWithinAt)
      (fun t ht => (hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      (hcont.intervalIntegrable_of_Icc hab)]
  have hmem : ∀ u ∈ uIoc a b, u ∈ Icc a b := fun u hu => by
    rw [uIoc_of_le hab] at hu
    exact Ioc_subset_Icc_self hu
  have h1 : Tendsto (fun S : Finset ι => (∑ i ∈ S, T b i) - ∑ i ∈ S, T a i) atTop
      (𝓝 ((∑' i, T b i) - ∑' i, T a i)) := by
    have := hsb.hasSum.sub hsa.hasSum
    simpa [HasSum, Finset.sum_sub_distrib] using this
  have h2 : Tendsto (fun S : Finset ι => ∫ u in a..b, ∑ i ∈ S, T' u i) atTop
      (𝓝 (∫ u in a..b, ∑' i, T' u i)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
      ?_ ?_ intervalIntegrable_const ?_
    · refine .of_forall fun S => ?_
      exact ((continuousOn_finsetSum S fun i _ => hc i).mono hmem).aestronglyMeasurable
        measurableSet_uIoc
    · refine .of_forall fun S => .of_forall fun u hu => ?_
      have hu' := hmem u hu
      calc ‖∑ i ∈ S, T' u i‖ ≤ ∑ i ∈ S, ‖T' u i‖ := norm_sum_le _ _
        _ ≤ ∑' i, ‖T' u i‖ := (hB u hu').1.sum_le_tsum S (fun _ _ => norm_nonneg _)
        _ ≤ C := (hB u hu').2
    · refine .of_forall fun u hu => ?_
      have := ((hB u (hmem u hu)).1.of_norm).hasSum
      simpa [HasSum] using this
  exact tendsto_nhds_unique h1 (h2.congr fun S => (hfin S).symm)

/-! ### The vertex along paths -/

/-- The Leray symbol as a continuous linear map. -/
private def lerayCL (k : Mode) : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := leray k, map_add' := leray_add k, map_smul' := leray_smul k }

/-- The pairing with a mode as a continuous linear form. -/
private def dotCL (k : Mode) : V3 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => dotM v k, map_add' := fun a b => dotM_add a b k,
      map_smul' := fun c a => dotM_smul c a k }

private lemma hasDerivWithinAt_dotM {A : ℝ → V3} {A' : V3} {s : Set ℝ} {t : ℝ} (q : Mode)
    (hA : HasDerivWithinAt A A' s t) :
    HasDerivWithinAt (fun u => dotM (A u) q) (dotM A' q) s t :=
  ((dotCL q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hA

/-- The vertex is bilinear: the product rule along two paths. -/
private lemma hasDerivWithinAt_vert {p q : Mode} {A B : ℝ → V3} {A' B' : V3} {s : Set ℝ} {t : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hB : HasDerivWithinAt B B' s t) :
    HasDerivWithinAt (fun u => vert p q (A u) (B u))
      (vert p q A' (B t) + vert p q (A t) B') s t := by
  have h1 : HasDerivWithinAt (fun u => (Complex.I * dotM (A u) q) • B u)
      ((Complex.I * dotM (A t) q) • B' + (Complex.I * dotM A' q) • B t) s t :=
    ((hasDerivWithinAt_dotM q hA).const_mul Complex.I).smul hB
  have h2 : HasDerivWithinAt (fun u => (Complex.I * dotM (B u) p) • A u)
      ((Complex.I * dotM (B t) p) • A' + (Complex.I * dotM B' p) • A t) s t :=
    ((hasDerivWithinAt_dotM p hB).const_mul Complex.I).smul hA
  have h3 := ((lerayCL (p + q)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (h1.add h2)
  have h4 := h3.const_smul (1 / 2 : ℂ)
  refine h4.congr_deriv ?_
  simp only [ContinuousLinearMap.coe_restrictScalars', lerayCL,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, vert, ← smul_add,
    ← leray_add]
  congr 2
  abel

private lemma continuousOn_dotM {A : ℝ → V3} {s : Set ℝ} (hA : ContinuousOn A s) (q : Mode) :
    ContinuousOn (fun u => dotM (A u) q) s :=
  (dotCL q).continuous.comp_continuousOn hA

private lemma continuousOn_leray {A : ℝ → V3} {s : Set ℝ} (hA : ContinuousOn A s) (q : Mode) :
    ContinuousOn (fun u => leray q (A u)) s :=
  (lerayCL q).continuous.comp_continuousOn hA

lemma continuousOn_vert {p q : Mode} {A B : ℝ → V3} {s : Set ℝ} (hA : ContinuousOn A s)
    (hB : ContinuousOn B s) : ContinuousOn (fun u => vert p q (A u) (B u)) s := by
  have h3 : ContinuousOn (fun u => (Complex.I * dotM (A u) q) • B u) s :=
    (continuousOn_const.mul (continuousOn_dotM hA q)).smul hB
  have h4 : ContinuousOn (fun u => (Complex.I * dotM (B u) p) • A u) s :=
    (continuousOn_const.mul (continuousOn_dotM hB p)).smul hA
  have h5 : ContinuousOn (fun u => leray (p + q) ((Complex.I * dotM (A u) q) • B u +
      (Complex.I * dotM (B u) p) • A u)) s := continuousOn_leray (h3.add h4) (p + q)
  simp only [vert]
  exact h5.const_smul (1 / 2 : ℂ)

private lemma vert_sub_left (p q : Mode) (A A' B : V3) :
    vert p q (A - A') B = vert p q A B - vert p q A' B := by
  have h1 : dotM (A - A') q = dotM A q - dotM A' q := by
    simp [dotM, sub_mul, Finset.sum_sub_distrib]
  simp only [vert, h1, mul_sub, sub_smul, ← smul_sub, ← leray_sub]
  congr 2
  simp only [smul_sub]
  abel

private lemma vert_sub_right (p q : Mode) (A B B' : V3) :
    vert p q A (B - B') = vert p q A B - vert p q A B' := by
  have h1 : dotM (B - B') p = dotM B p - dotM B' p := by
    simp [dotM, sub_mul, Finset.sum_sub_distrib]
  simp only [vert, h1, mul_sub, sub_smul, ← smul_sub, ← leray_sub]
  congr 2
  simp only [smul_sub]
  abel

/-! ### The summand of `Q^♯` -/

/-- The `p`-summand of `Q^♯_m(f,g)_k`. -/
private def triV (m : Mult) (f g : Field) (k p : Mode) : V3 :=
  ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
    m a b c p (k - p) • hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p))))

private lemma triV_sub_left (m : Mult) (f f' g : Field) (k p : Mode) :
    triV m (f - f') g k p = triV m f g k p - triV m f' g k p := by
  simp only [triV, Pi.sub_apply, hel_sub, vert_sub_left, smul_sub, Finset.sum_sub_distrib]

private lemma triV_sub_right (m : Mult) (f g g' : Field) (k p : Mode) :
    triV m f (g - g') k p = triV m f g k p - triV m f g' k p := by
  simp only [triV, Pi.sub_apply, hel_sub, vert_sub_right, smul_sub, Finset.sum_sub_distrib]

/-- Product rule for the summand of `Q^♯` with a time-dependent multiplier. -/
private lemma hasDerivWithinAt_triV {m m' : ℝ → Mult} {X X' Y Y' : ℝ → Field} {s : Set ℝ} {t : ℝ}
    (k p : Mode)
    (hm : ∀ a b c, HasDerivWithinAt (fun u => m u a b c p (k - p)) (m' t a b c p (k - p)) s t)
    (hX : HasDerivWithinAt (fun u => X u p) (X' t p) s t)
    (hY : HasDerivWithinAt (fun u => Y u (k - p)) (Y' t (k - p)) s t) :
    HasDerivWithinAt (fun u => triV (m u) (X u) (Y u) k p)
      (triV (m' t) (X t) (Y t) k p + triV (m t) (X' t) (Y t) k p +
        triV (m t) (X t) (Y' t) k p) s t := by
  have key : ∀ a b c, HasDerivWithinAt (fun u => m u a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (X u p)) (hel b (k - p) (Y u (k - p)))))
      (m' t a b c p (k - p) •
          hel c k (vert p (k - p) (hel a p (X t p)) (hel b (k - p) (Y t (k - p)))) +
        m t a b c p (k - p) •
          hel c k (vert p (k - p) (hel a p (X' t p)) (hel b (k - p) (Y t (k - p)))) +
        m t a b c p (k - p) •
          hel c k (vert p (k - p) (hel a p (X t p)) (hel b (k - p) (Y' t (k - p))))) s t := by
    intro a b c
    have h1 := hasDerivWithinAt_hel (a := a) (k := p) hX
    have h2 := hasDerivWithinAt_hel (a := b) (k := k - p) hY
    have h3 := hasDerivWithinAt_vert (p := p) (q := k - p) h1 h2
    have h4 := hasDerivWithinAt_hel (a := c) (k := k) h3
    refine ((hm a b c).smul h4).congr_deriv ?_
    rw [hel_add, smul_add]
    abel
  have hsum := HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset Sgn)) fun a _ =>
    HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset Sgn)) fun b _ =>
      HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset Sgn)) fun c _ => key a b c
  simp only [triV]
  refine hsum.congr_deriv ?_
  simp only [Finset.sum_add_distrib]

/-- Continuity of the summand of `Q^♯` along continuous paths. -/
private lemma continuousOn_triV {m : ℝ → Mult} {X Y : ℝ → Field} {s : Set ℝ} (k p : Mode)
    (hm : ∀ a b c, ContinuousOn (fun u => m u a b c p (k - p)) s)
    (hX : ContinuousOn (fun u => X u p) s) (hY : ContinuousOn (fun u => Y u (k - p)) s) :
    ContinuousOn (fun u => triV (m u) (X u) (Y u) k p) s := by
  have key : ∀ a b c, ContinuousOn (fun u => m u a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (X u p)) (hel b (k - p) (Y u (k - p))))) s := by
    intro a b c
    have hA : ContinuousOn (fun u => hel a p (X u p)) s :=
      (continuous_hel a p).comp_continuousOn hX
    have hB : ContinuousOn (fun u => hel b (k - p) (Y u (k - p))) s :=
      (continuous_hel b (k - p)).comp_continuousOn hY
    exact (hm a b c).smul ((continuous_hel c k).comp_continuousOn (continuousOn_vert hA hB))
  simp only [triV]
  exact continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ =>
    continuousOn_finsetSum _ fun c _ => key a b c

/-! ### Bilinearity and mode-continuity of the primitive -/

section Primitive

variable {r τ : ℝ}

private lemma kinN_eq_tsum (f g : Field) (k : Mode) :
    kinN r τ f g k = ∑' p, triV (kinM r τ) f g k p := rfl

private lemma summable_triV_kinM (hr : r ≠ 0) {f g : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hg : Summable fun k => ‖g k‖ ^ 2) (k : Mode) : Summable (triV (kinM r τ) f g k) :=
  summable_kinN_term hr hf hg k

private lemma norm_triV_kinM_le (hr : r ≠ 0) (f g : Field) (k p : Mode) :
    ‖triV (kinM r τ) f g k p‖ ≤ 2 / |r| * (‖f p‖ * ‖g (k - p)‖) :=
  norm_kinN_term_le hr f g k p

/-- The primitive is additive in the first slot on `ℓ²`. -/
lemma kinN_sub_left (hr : r ≠ 0) {f f' g : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hf' : Summable fun k => ‖f' k‖ ^ 2) (hg : Summable fun k => ‖g k‖ ^ 2) :
    kinN r τ (f - f') g = kinN r τ f g - kinN r τ f' g := by
  funext k
  change ∑' p, triV (kinM r τ) (f - f') g k p =
    ∑' p, triV (kinM r τ) f g k p - ∑' p, triV (kinM r τ) f' g k p
  rw [← (summable_triV_kinM hr hf hg k).tsum_sub (summable_triV_kinM hr hf' hg k)]
  exact tsum_congr (triV_sub_left _ f f' g k)

/-- The primitive is additive in the second slot on `ℓ²`. -/
lemma kinN_sub_right (hr : r ≠ 0) {f g g' : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hg : Summable fun k => ‖g k‖ ^ 2) (hg' : Summable fun k => ‖g' k‖ ^ 2) :
    kinN r τ f (g - g') = kinN r τ f g - kinN r τ f g' := by
  funext k
  change ∑' p, triV (kinM r τ) f (g - g') k p =
    ∑' p, triV (kinM r τ) f g k p - ∑' p, triV (kinM r τ) f g' k p
  rw [← (summable_triV_kinM hr hf hg k).tsum_sub (summable_triV_kinM hr hf hg' k)]
  exact tsum_congr (triV_sub_right _ f g g' k)

/-- For frozen fields a mode of the primitive is continuous in time. -/
lemma continuous_kinN_frozen (hr : r ≠ 0) {f g : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hg : Summable fun k => ‖g k‖ ^ 2) (k : Mode) :
    Continuous fun u : ℝ => kinN r (r * u) f g k := by
  have hs := (convR_le_of_l2 (a := fun k => ‖f k‖) (b := fun k => ‖g k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hf hg k).1.mul_left (2 / |r|)
  refine continuous_tsum (f := fun p u => triV (kinM r (r * u)) f g k p) (fun p => ?_) hs
    (fun p u => norm_triV_kinM_le hr f g k p)
  simp only [triV]
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_finsetSum _ fun c _ => ?_
  exact (continuous_iff_continuousAt.2 fun u =>
    (hasDerivAt_kinM hr a b c p (k - p) u).continuousAt).smul continuous_const

/-- A mode of the primitive is dominated by the `H⁰` norms. -/
lemma norm_kinN_apply_le (hr : r ≠ 0) {f g : Field} (hf : MZ 0 f) (hg : MZ 0 g) (k : Mode) :
    ‖kinN r τ f g k‖ ≤ 2 / |r| * (hnorm 0 f * hnorm 0 g) := by
  rw [hnorm_zero_eq hf.mean, hnorm_zero_eq hg.mean]
  exact norm_kinN_le_l2 hr (summable_norm_sq_of_inH hf.inH) (summable_norm_sq_of_inH hg.inH) k

/-- **Mode-continuity of the primitive along `ℓ²`-continuous, `ℓ²`-bounded paths.** -/
theorem continuousOn_kinN_mode (hr : r ≠ 0) {f g : ℝ → Field} {s : Set ℝ}
    (hf : ∀ u ∈ s, MZ 0 (f u)) (hg : ∀ u ∈ s, MZ 0 (g u))
    (hfc : ∀ u₀ ∈ s, Tendsto (fun u => hnorm 0 (f u - f u₀)) (𝓝[s] u₀) (𝓝 0))
    (hgc : ∀ u₀ ∈ s, Tendsto (fun u => hnorm 0 (g u - g u₀)) (𝓝[s] u₀) (𝓝 0))
    {M : ℝ} (hM : ∀ u ∈ s, hnorm 0 (f u) ≤ M ∧ hnorm 0 (g u) ≤ M) (k : Mode) :
    ContinuousOn (fun u => kinN r (r * u) (f u) (g u) k) s := by
  intro u₀ hu₀
  have hM0 : 0 ≤ M := (hnorm_nonneg _ _).trans (hM u₀ hu₀).1
  have hf0 := hf u₀ hu₀
  have hg0 := hg u₀ hu₀
  have hr' : 0 ≤ 2 / |r| := by positivity
  have h3 : Tendsto (fun u => kinN r (r * u) (f u₀) (g u₀) k - kinN r (r * u₀) (f u₀) (g u₀) k)
      (𝓝[s] u₀) (𝓝 0) := by
    have := ((continuous_kinN_frozen hr (summable_norm_sq_of_inH hf0.inH)
      (summable_norm_sq_of_inH hg0.inH) k).tendsto u₀).sub_const
        (kinN r (r * u₀) (f u₀) (g u₀) k)
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hfg : Tendsto (fun u => 2 / |r| * (hnorm 0 (f u - f u₀) * M) +
      2 / |r| * (M * hnorm 0 (g u - g u₀))) (𝓝[s] u₀) (𝓝 0) := by
    have h1 := ((hfc u₀ hu₀).mul_const M).const_mul (2 / |r|)
    have h2 := ((hgc u₀ hu₀).const_mul M).const_mul (2 / |r|)
    simpa using h1.add h2
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using hfg.add h3.norm)
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hfu := hf u hu
  have hgu := hg u hu
  have hd1 : MZ 0 (f u - f u₀) := ⟨hfu.inH.sub hf0.inH, by simp [hfu.mean, hf0.mean]⟩
  have hd2 : MZ 0 (g u - g u₀) := ⟨hgu.inH.sub hg0.inH, by simp [hgu.mean, hg0.mean]⟩
  have l1 := summable_norm_sq_of_inH hfu.inH
  have l2 := summable_norm_sq_of_inH hf0.inH
  have l3 := summable_norm_sq_of_inH hgu.inH
  have l4 := summable_norm_sq_of_inH hg0.inH
  have e1 := kinN_sub_left (τ := r * u) hr l1 l2 l3
  have e2 := kinN_sub_right (τ := r * u) hr l2 l3 l4
  have esplitF : kinN r (r * u) (f u) (g u) - kinN r (r * u₀) (f u₀) (g u₀) =
      kinN r (r * u) (f u - f u₀) (g u) + kinN r (r * u) (f u₀) (g u - g u₀) +
        (kinN r (r * u) (f u₀) (g u₀) - kinN r (r * u₀) (f u₀) (g u₀)) := by
    rw [e1, e2]; abel
  have esplit : kinN r (r * u) (f u) (g u) k - kinN r (r * u₀) (f u₀) (g u₀) k =
      kinN r (r * u) (f u - f u₀) (g u) k + kinN r (r * u) (f u₀) (g u - g u₀) k +
        (kinN r (r * u) (f u₀) (g u₀) k - kinN r (r * u₀) (f u₀) (g u₀) k) := by
    have := congrFun esplitF k
    simpa only [Pi.sub_apply, Pi.add_apply] using this
  have b1 := norm_kinN_apply_le (τ := r * u) hr hd1 hgu k
  have b2 := norm_kinN_apply_le (τ := r * u) hr hf0 hd2 k
  have hgM := (hM u hu).2
  have hfM := (hM u₀ hu₀).1
  have n1 := hnorm_nonneg 0 (f u - f u₀)
  have n2 := hnorm_nonneg 0 (g u - g u₀)
  calc ‖kinN r (r * u) (f u) (g u) k - kinN r (r * u₀) (f u₀) (g u₀) k‖
      ≤ ‖kinN r (r * u) (f u - f u₀) (g u) k‖ + ‖kinN r (r * u) (f u₀) (g u - g u₀) k‖ +
        ‖kinN r (r * u) (f u₀) (g u₀) k - kinN r (r * u₀) (f u₀) (g u₀) k‖ := by
        rw [esplit]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2 / |r| * (hnorm 0 (f u - f u₀) * M) + 2 / |r| * (M * hnorm 0 (g u - g u₀)) +
        ‖kinN r (r * u) (f u₀) (g u₀) k - kinN r (r * u₀) (f u₀) (g u₀) k‖ := by
        gcongr
        · exact b1.trans (by gcongr)
        · exact b2.trans (by gcongr)

end Primitive

/-! ### The derivative summand -/

section Summand

variable {r : ℝ}

/-- The derivative multiplier is bounded. -/
private lemma kinDM_bdd (τ : ℝ) : (kinDM τ).Bdd := fun a b c p q => by
  unfold kinDM
  split_ifs
  · exact phaseM_bdd τ a b c p q
  · simp

/-- On a slow output with fast inputs the derivative multiplier acts as the full phase: the
excluded triads carry a vanishing vertex (the slow-output resonant null) or a slow input. -/
private lemma triV_kinDM_eq (τ : ℝ) {F : Field} (hF : PiF F = F) {k : Mode} (hk : k 2 = 0)
    (p : Mode) : triV (kinDM τ) F F k p = triV (phaseM τ) F F k p := by
  unfold triV
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  by_cases hp : p 2 = 0
  · rw [fast_zero hF hp, hel_zero_right, vert_zero_left, hel_zero_right, smul_zero, smul_zero]
  have h1 : (p + (k - p)) 2 = 0 := by
    rw [add_sub_cancel]
    exact hk
  by_cases hΦ : Phi a b c p (k - p) = 0
  · rw [vert_hel_zero _ _ (res_null h1 hp hΦ), hel_zero_right, smul_zero, smul_zero]
  · have h : (p + (k - p)) 2 = 0 ∧ p 2 ≠ 0 ∧ Phi a b c p (k - p) ≠ 0 := ⟨h1, hp, hΦ⟩
    simp only [kinDM, ite_eq_left h]

/-- The derivative multiplier vanishes on fast outputs. -/
private lemma triV_kinDM_fast (τ : ℝ) (F G : Field) {k : Mode} (hk : k 2 ≠ 0) (p : Mode) :
    triV (kinDM τ) F G k p = 0 := by
  have h1 : ∀ a b c, ¬ ((p + (k - p)) 2 = 0 ∧ p 2 ≠ 0 ∧ Phi a b c p (k - p) ≠ 0) :=
    fun a b c h => hk (by rw [add_sub_cancel] at h; exact h.1)
  unfold triV
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => ?_
  simp only [kinDM, ite_eq_right (h1 a b c), zero_smul]

/-- The sum of the frozen-amplitude slot is the slow projection of the phased convection. -/
private lemma tsum_triV_kinDM (τ : ℝ) {F : Field} (hF : PiF F = F) (k : Mode) :
    ∑' p, triV (kinDM τ) F F k p = PiS (Qphase τ F F) k := by
  by_cases hk : k 2 = 0
  · rw [PiS_apply_slow _ hk]
    exact tsum_congr (triV_kinDM_eq τ hF hk)
  · rw [PiS_apply_fast _ hk, ← tsum_zero (α := V3) (β := Mode)]
    exact tsum_congr (triV_kinDM_fast τ F F hk)

/-- The summand of a bounded multiplier is at most `2 (|p| + |k−p|) ‖f_p‖ ‖g_{k−p}‖`. -/
private lemma norm_triV_le {m : Mult} (hm : m.Bdd) (f g : Field) (k p : Mode) :
    ‖triV m f g k p‖ ≤
      2 * (absk p * ‖f p‖ * ‖g (k - p)‖) + 2 * (‖f p‖ * (absk (k - p) * ‖g (k - p)‖)) := by
  have hn1 := absk_nonneg p
  have hn2 := absk_nonneg (k - p)
  have h := norm_sum3_le (fun a b c => m a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p)))))
    (κ := 1 / 2 * (absk (k - p) + absk p)) (by positivity) p (k - p) (f p) (g (k - p))
    fun a b c => by
      rw [norm_smul]
      calc ‖m a b c p (k - p)‖ *
            ‖hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p))))‖
          ≤ 1 * ‖vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p)))‖ :=
            mul_le_mul (hm _ _ _ _ _) (norm_hel_le _ _ _) (norm_nonneg _) zero_le_one
        _ ≤ _ := by rw [one_mul]; exact norm_vert_le₁ _ _ _ _
  refine h.trans (le_of_eq ?_)
  ring

/-- The derivative summand of `N(F,F)_k` at `p`. -/
private def triD (r τ : ℝ) (F F' : Field) (k p : Mode) : V3 :=
  triV (kinDM τ) F F k p + triV (kinM r τ) F' F k p + triV (kinM r τ) F F' k p

/-- **The summability control** of the derivative summands at a fixed time. -/
private lemma triD_summable_bound (hr : r ≠ 0) (τ : ℝ) {F F' : Field}
    (hF2 : Summable fun k => ‖F k‖ ^ 2) (hFg : Summable fun k => (absk k * ‖F k‖) ^ 2)
    (hF'2 : Summable fun k => ‖F' k‖ ^ 2) (k : Mode) :
    Summable (fun p => ‖triD r τ F F' k p‖) ∧
      ∑' p, ‖triD r τ F F' k p‖ ≤
        4 * (Real.sqrt (∑' k, (absk k * ‖F k‖) ^ 2) * Real.sqrt (∑' k, ‖F k‖ ^ 2)) +
          4 / |r| * (Real.sqrt (∑' k, ‖F' k‖ ^ 2) * Real.sqrt (∑' k, ‖F k‖ ^ 2)) := by
  have hr' : 0 < |r| := abs_pos.mpr hr
  have hn : ∀ (W : Field) (k : Mode), 0 ≤ ‖W k‖ := fun W k => norm_nonneg _
  have hg : ∀ k, 0 ≤ absk k * ‖F k‖ := fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _)
  obtain ⟨s1, b1⟩ := convR_le_of_l2 (a := fun k => absk k * ‖F k‖) (b := fun k => ‖F k‖)
    hg (hn F) hFg hF2 k
  obtain ⟨s2, b2⟩ := convR_le_of_l2 (a := fun k => ‖F k‖) (b := fun k => absk k * ‖F k‖)
    (hn F) hg hF2 hFg k
  obtain ⟨s3, b3⟩ := convR_le_of_l2 (a := fun k => ‖F' k‖) (b := fun k => ‖F k‖)
    (hn F') (hn F) hF'2 hF2 k
  obtain ⟨s4, b4⟩ := convR_le_of_l2 (a := fun k => ‖F k‖) (b := fun k => ‖F' k‖)
    (hn F) (hn F') hF2 hF'2 k
  simp only [convR] at b1 b2 b3 b4
  set G : Mode → ℝ := fun p =>
    2 * (absk p * ‖F p‖ * ‖F (k - p)‖) + 2 * (‖F p‖ * (absk (k - p) * ‖F (k - p)‖)) +
      2 / |r| * (‖F' p‖ * ‖F (k - p)‖) + 2 / |r| * (‖F p‖ * ‖F' (k - p)‖) with hG
  have hGs : Summable G :=
    (((s1.mul_left 2).add (s2.mul_left 2)).add (s3.mul_left _)).add (s4.mul_left _)
  have hpt : ∀ p, ‖triD r τ F F' k p‖ ≤ G p := fun p => by
    have h1 := norm_triV_le (kinDM_bdd τ) F F k p
    have h2 := norm_triV_kinM_le (τ := τ) hr F' F k p
    have h3 := norm_triV_kinM_le (τ := τ) hr F F' k p
    have h4 : ‖triD r τ F F' k p‖ ≤ ‖triV (kinDM τ) F F k p‖ + ‖triV (kinM r τ) F' F k p‖ +
        ‖triV (kinM r τ) F F' k p‖ := norm_add₃_le
    rw [hG]
    linarith
  have hS0 : Summable fun p => ‖triD r τ F F' k p‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hGs
  refine ⟨hS0, (hS0.tsum_le_tsum hpt hGs).trans ?_⟩
  have eG : ∑' p, G p =
      2 * ∑' p, (absk p * ‖F p‖ * ‖F (k - p)‖) +
        2 * ∑' p, (‖F p‖ * (absk (k - p) * ‖F (k - p)‖)) +
        2 / |r| * ∑' p, (‖F' p‖ * ‖F (k - p)‖) + 2 / |r| * ∑' p, (‖F p‖ * ‖F' (k - p)‖) := by
    rw [hG, (((s1.mul_left 2).add (s2.mul_left 2)).add (s3.mul_left _)).tsum_add (s4.mul_left _),
      ((s1.mul_left 2).add (s2.mul_left 2)).tsum_add (s3.mul_left _),
      (s1.mul_left 2).tsum_add (s2.mul_left 2), tsum_mul_left, tsum_mul_left, tsum_mul_left,
      tsum_mul_left]
  rw [eG]
  have c1 := mul_le_mul_of_nonneg_left b1 (by norm_num : (0 : ℝ) ≤ 2)
  have c2 := mul_le_mul_of_nonneg_left b2 (by norm_num : (0 : ℝ) ≤ 2)
  have c3 := mul_le_mul_of_nonneg_left b3 (by positivity : (0 : ℝ) ≤ 2 / |r|)
  have c4 := mul_le_mul_of_nonneg_left b4 (by positivity : (0 : ℝ) ≤ 2 / |r|)
  have e1 : (4 : ℝ) / |r| = 2 / |r| + 2 / |r| := by ring
  rw [e1]
  nlinarith

end Summand

namespace Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### The mode derivative along the actual solution -/

/-- `F' = fastRHS` is a mean-zero `ℓ²` field. -/
lemma fastRHS_mz (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) : MZ 0 (fastRHS r g y u) :=
  ⟨inH_zero_of_summable (fastRHS_l2 h hu huT).1, by simp [fastRHS, PiF]⟩

/-- `u ↦ N(F', F)_k` is continuous on `[0, b]`. -/
theorem continuousOn_kinN_fastRHS_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => kinN r (r * u) (fastRHS r g y u) (PiF (actual r g y u)) k)
      (Icc 0 b) := by
  obtain ⟨M, hM0, hM⟩ := exists_actual_bound' h hr hbT
  obtain ⟨D, hD0, hD⟩ := exists_Qphase_bound h hbT
  have hadm : ∀ u ∈ Icc 0 b, Adm 2 (PiF (actual r g y u)) := fun u hu =>
    (actual_adm h hu.1 (lt_lifespan hu.2 hbT)).PiF
  refine continuousOn_kinN_mode hr (s := Icc 0 b) (M := M + D)
    (fun u hu => fastRHS_mz h hu.1 (lt_lifespan hu.2 hbT))
    (fun u hu => ⟨(hadm u hu).inH.mono (by norm_num), (hadm u hu).mean⟩)
    (fun u₀ hu₀ => tendsto_fastRHS_l2 h hr hbT hu₀) (fun u₀ hu₀ => ?_) (fun u hu => ⟨?_, ?_⟩) k
  · refine squeeze_zero' (Eventually.of_forall fun _ => hnorm_nonneg _ _) ?_ (fast_cont h hbT hu₀)
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hnorm_mono (by norm_num) ((hadm u hu).inH.sub (hadm u₀ hu₀).inH)
  · rw [hnorm_zero_eq (fastRHS_mz h hu.1 (lt_lifespan hu.2 hbT)).mean]
    exact (fastRHS_l2 h hu.1 (lt_lifespan hu.2 hbT)).2.trans
      (add_le_add (hM u hu).2.1 (hD u hu).2)
  · have := (hnorm_mono (by norm_num : (0 : ℝ) ≤ 2) (hadm u hu).inH).trans (hM u hu).2.1
    linarith

/-- The `Π_S`-projected phased fast convection is mode-continuous. -/
lemma continuousOn_PiS_Qphase_fast_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => PiS (Qphase (r * u) (PiF (actual r g y u)) (PiF (actual r g y u))) k)
      (Icc 0 b) := by
  by_cases hk : k 2 = 0
  · simp only [PiS_apply_slow _ hk]
    exact continuousOn_Qphase_fast_mode h hr hbT k
  · simp only [PiS_apply_fast _ hk]
    exact continuousOn_const

/-- **The mode derivative of the primitive along the actual solution**:
`N(F,F)_k' = Π_S Q_{rt}(F,F)_k + 2N(F',F)_k` on `[0, b]`. -/
theorem hasDerivWithinAt_kinN_fast (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) {t : ℝ} (ht : t ∈ Icc 0 b) :
    HasDerivWithinAt (fun u => kinN r (r * u) (PiF (actual r g y u)) (PiF (actual r g y u)) k)
      (PiS (Qphase (r * t) (PiF (actual r g y t)) (PiF (actual r g y t))) k +
        (2 : ℂ) • kinN r (r * t) (fastRHS r g y t) (PiF (actual r g y t)) k) (Icc 0 b) t := by
  have hmem : ∀ u ∈ Icc 0 b, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hu.1, lt_lifespan hu.2 hbT⟩
  set F : ℝ → Field := fun u => PiF (actual r g y u) with hFdef
  have hadm : ∀ u ∈ Icc 0 b, Adm 2 (F u) := fun u hu =>
    (actual_adm h (hmem u hu).1 (hmem u hu).2).PiF
  have hFF : ∀ u, PiF (F u) = F u := fun u => by
    funext k; by_cases hk : k 2 = 0 <;> simp [hFdef, PiF, hk]
  have hF2 : ∀ u ∈ Icc 0 b, Summable fun k => ‖F u k‖ ^ 2 := fun u hu =>
    summable_norm_sq_of_inH ((hadm u hu).inH.mono (by norm_num))
  have hFg : ∀ u ∈ Icc 0 b, Summable fun k => (absk k * ‖F u k‖) ^ 2 := fun u hu =>
    summable_grad_sq (hadm u hu).mz
  have hF'2 : ∀ u ∈ Icc 0 b, Summable fun k => ‖fastRHS r g y u k‖ ^ 2 := fun u hu =>
    (fastRHS_l2 h (hmem u hu).1 (hmem u hu).2).1
  -- the summands and their derivatives
  set H : ℝ → V3 := fun u => PiS (Qphase (r * u) (F u) (F u)) k +
    (2 : ℂ) • kinN r (r * u) (fastRHS r g y u) (F u) k with hHdef
  have hd : ∀ p, ∀ u ∈ Icc 0 b,
      HasDerivWithinAt (fun v => triV (kinM r (r * v)) (F v) (F v) k p)
        (triD r (r * u) (F u) (fastRHS r g y u) k p) (Icc 0 b) u := fun p u hu =>
    hasDerivWithinAt_triV (m := fun v => kinM r (r * v)) (m' := fun v => kinDM (r * v))
      (X := F) (X' := fastRHS r g y) (Y := F) (Y' := fastRHS r g y) k p
      (fun a b c => (hasDerivAt_kinM hr a b c p (k - p) u).hasDerivWithinAt)
      ((fast_mode h p (hmem u hu).1 (hmem u hu).2).mono Icc_subset_Ici_self)
      ((fast_mode h (k - p) (hmem u hu).1 (hmem u hu).2).mono Icc_subset_Ici_self)
  have hc : ∀ p, ContinuousOn (fun u => triD r (r * u) (F u) (fastRHS r g y u) k p) (Icc 0 b) := by
    intro p
    have hmc : ∀ a b' c, ContinuousOn (fun u => kinM r (r * u) a b' c p (k - p)) (Icc 0 b) :=
      fun a b' c u _ => (hasDerivAt_kinM hr a b' c p (k - p) u).continuousAt.continuousWithinAt
    have hm'c : ∀ a b' c, ContinuousOn (fun u => kinDM (r * u) a b' c p (k - p)) (Icc 0 b) :=
      fun a b' c => (continuous_kinDM a b' c p (k - p)).continuousOn
    have hXc := fun j => continuousOn_fast_mode h hbT j
    have hX'c := fun j => continuousOn_fastRHS_mode h hb hbT j
    have h1 := continuousOn_triV (X := F) (Y := F) k p hm'c (hXc p) (hXc (k - p))
    have h2 := continuousOn_triV (X := fastRHS r g y) (Y := F) k p hmc (hX'c p) (hXc (k - p))
    have h3 := continuousOn_triV (X := F) (Y := fastRHS r g y) k p hmc (hXc p) (hX'c (k - p))
    exact (h1.add h2).add h3
  -- the uniform bound
  obtain ⟨M, hM0, hM⟩ := exists_actual_bound' h hr hbT
  obtain ⟨D, hD0, hD⟩ := exists_Qphase_bound h hbT
  have hr' : 0 < |r| := abs_pos.mpr hr
  have hB : ∀ u ∈ Icc 0 b, Summable (fun p => ‖triD r (r * u) (F u) (fastRHS r g y u) k p‖) ∧
      ∑' p, ‖triD r (r * u) (F u) (fastRHS r g y u) k p‖ ≤
        4 * (M * M) + 4 / |r| * ((M + D) * M) := by
    intro u hu
    obtain ⟨hs, hle⟩ := triD_summable_bound hr (r * u) (hF2 u hu) (hFg u hu) (hF'2 u hu) k
    refine ⟨hs, hle.trans ?_⟩
    have hb2 : hnorm 2 (F u) ≤ M := (hM u hu).2.1
    have hG : Real.sqrt (∑' k, (absk k * ‖F u k‖) ^ 2) ≤ M := by
      rw [sqrt_tsum_grad_sq]
      exact (hnorm_mono (by norm_num) (hadm u hu).inH).trans hb2
    have hN : Real.sqrt (∑' k, ‖F u k‖ ^ 2) ≤ M := by
      rw [← hnorm_zero_eq (hadm u hu).mean]
      exact (hnorm_mono (by norm_num) (hadm u hu).inH).trans hb2
    have hN' : Real.sqrt (∑' k, ‖fastRHS r g y u k‖ ^ 2) ≤ M + D :=
      (fastRHS_l2 h (hmem u hu).1 (hmem u hu).2).2.trans (add_le_add hb2 (hD u hu).2)
    have n1 := Real.sqrt_nonneg (∑' k, (absk k * ‖F u k‖) ^ 2)
    have n2 := Real.sqrt_nonneg (∑' k, ‖F u k‖ ^ 2)
    have n3 := Real.sqrt_nonneg (∑' k, ‖fastRHS r g y u k‖ ^ 2)
    have hMD : 0 ≤ M + D := add_nonneg hM0 hD0
    gcongr
  -- the sum of the derivative summands
  have hsum : ∀ u ∈ Icc 0 b, ∑' p, triD r (r * u) (F u) (fastRHS r g y u) k p = H u := by
    intro u hu
    have s1 : Summable (triV (kinDM (r * u)) (F u) (F u) k) :=
      summable_Qm_term (kinDM_bdd _) (hadm u hu).mz (hadm u hu).mz k
    have s2 := summable_triV_kinM (τ := r * u) hr (hF'2 u hu) (hF2 u hu) k
    have s3 := summable_triV_kinM (τ := r * u) hr (hF2 u hu) (hF'2 u hu) k
    have e : ∑' p, triD r (r * u) (F u) (fastRHS r g y u) k p =
        ∑' p, triV (kinDM (r * u)) (F u) (F u) k p +
          ∑' p, triV (kinM r (r * u)) (fastRHS r g y u) (F u) k p +
          ∑' p, triV (kinM r (r * u)) (F u) (fastRHS r g y u) k p := by
      rw [← s1.tsum_add s2, ← (s1.add s2).tsum_add s3]
      rfl
    rw [e, tsum_triV_kinDM _ (hFF u), ← kinN_eq_tsum, ← kinN_eq_tsum,
      kinN_comm (F u) (fastRHS r g y u)]
    show _ = PiS (Qphase (r * u) (F u) (F u)) k + (2 : ℂ) • kinN r (r * u) (fastRHS r g y u) (F u) k
    rw [two_smul ℂ, add_assoc]
  -- the right-hand side is continuous
  have hHc : ContinuousOn H (Icc 0 b) := by
    have h1 := continuousOn_PiS_Qphase_fast_mode h hr hbT k
    have h2 := continuousOn_kinN_fastRHS_mode h hr hbT k
    exact h1.add (h2.const_smul (2 : ℂ))
  -- the integrated form
  have hint : ∀ v ∈ Icc 0 b, kinN r (r * v) (F v) (F v) k - kinN r (r * 0) (F 0) (F 0) k =
      ∫ u in (0 : ℝ)..v, H u := by
    intro v hv
    have hsub : Icc 0 v ⊆ Icc 0 b := Icc_subset_Icc_right hv.2
    have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb⟩
    have key := integral_tsum_deriv' (T := fun u p => triV (kinM r (r * u)) (F u) (F u) k p)
      (T' := fun u p => triD r (r * u) (F u) (fastRHS r g y u) k p) (a := 0) (b := v) hv.1
      (fun p u hu => (hd p u (hsub hu)).mono hsub) (fun p => (hc p).mono hsub)
      (summable_triV_kinM hr (hF2 0 h0) (hF2 0 h0) k)
      (summable_triV_kinM hr (hF2 v hv) (hF2 v hv) k)
      (fun u hu => hB u (hsub hu))
    rw [← kinN_eq_tsum, ← kinN_eq_tsum] at key
    rw [key]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hv.1] at hu
    exact hsum u (hsub hu)
  -- the derivative of the primitive of `H`
  have hI : IntervalIntegrable H volume 0 t :=
    (hHc.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have : Fact (t ∈ Icc 0 b) := ⟨ht⟩
  have hder : HasDerivWithinAt (fun v => ∫ u in (0 : ℝ)..v, H u) (H t) (Icc 0 b) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hI
      (hHc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hHc t ht)
  have hfin := hder.const_add (kinN r (r * 0) (F 0) (F 0) k)
  refine hfin.congr (fun v hv => ?_) ?_
  · rw [← hint v hv]; abel
  · rw [← hint t ht]; abel

end Quant

end OVNS

end
