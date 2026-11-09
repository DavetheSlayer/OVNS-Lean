import OddViscousNS.Quant.Energy.Kinetic.Actual

/-!
# E4.4: the derivative of the kinetic correction along the actual solution

The engineering core of E4 (survey `t12_energy_derivation.md` §2.1 (c): "the AC/product rule
for `t ↦ Re⟨N(F t, F t), S t⟩` along the actual path (mode-wise differentiation of an infinite
`p`-sum, plus a polarized `energy_identity`); spec risk R5, reusable verbatim for `E⁰`, `E⁰₂`,
`M_s` in E5/E8").  Everything is stated in the framework of `EnergyMode.lean`: per-mode ODEs,
finite truncations, dominated passage to the limit.

## A. The abstract fundamental theorem of calculus for a summable family
`integral_tsum_deriv`: if every `t ↦ T t i` is differentiable on `[a,b]` with continuous
derivative `T' t i`, the family is summable at the endpoints and `∑ᵢ ‖T' u i‖ ≤ C` uniformly, then
`∑ᵢ T b i − ∑ᵢ T a i = ∫ₐᵇ ∑ᵢ T' u i`.  (Truncate to a finite set of indices, apply the FTC,
pass to the limit by dominated convergence — exactly the route of `HeatPair.energy_identity`.)

## B. The multilinear correction lemma (general form)
`trilinear_integral_identity`: three mode-wise differentiable paths `X, Y, Z`, a mode-wise
differentiable multiplier family `m`, and the triad functional `∑_{(p,q)} tripT (m t) (X t) (Y t)
(Z t) p q` (which is `⟨Z, Q^♯_m(X,Y)⟩` by `inner_Qm`/`inner_kinN`).  Its increment is the integral
of the four-slot derivative `tripD` (product rule `hasDerivWithinAt_tripT`), under the uniform
summability control `hB` — the "summability control" of the per-mode ODE framework.

## C. The actual split solution (TeX eq. quant-actual-system)
`actual_mode`: `x' = −Ax − Q_{rt}(y,y) + Π_S g` for `x = y − ψ`; `fast_mode`, `slow_mode`: the
projected equations `F' = fastRHS`, `S' = slowRHS`; `heatPair_fast`: `F` is a `HeatPair` at
`σ ∈ {0,1}` with force `−Π_F Q_{rt}(y,y)`, whence the `L²` law `fast_energy_identity`.

## D. The exchange identities (E4.2, polarized cyclic identities; survey §2.1 (b))
`pair_Qphase_self`: `⟨Q_τ(F,F), F⟩ = 0`; `pair_fast_Qphase`:
`⟨Π_F Q_τ(x,x), F⟩ = −⟨Q_τ(F,F), S⟩`, i.e. `2⟨Q(S,F),F⟩ = −⟨Q(F,F),S⟩` (`pair_exchange`).

The kinetic multiplier along the solution (`hasDerivAt_kinM`, TeX (N4)) and the `ℓ¹ℓ²ℓ²` triple
sums are `Multiplier.lean`; the specialization to the actual solution — `kinCorr_identity` (E4.4
for E4) and `W0_identity` — is `Identity.lean` (bounds in `Bounds.lean`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS

/-! ### A. FTC for a summable family -/

/-- **Fundamental theorem of calculus for a summable family of differentiable functions.**
Truncate to a finite index set, apply the FTC, pass to the limit with the dominating constant. -/
theorem integral_tsum_deriv {ι : Type*} [Countable ι] {T T' : ℝ → ι → ℂ} {a b : ℝ} (hab : a ≤ b)
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

/-- The derivative sum of `integral_tsum_deriv` is interval integrable (an a.e. limit of continuous
truncations, bounded by the dominating constant). -/
theorem intervalIntegrable_tsum_of_bound {ι : Type*} [Countable ι] {T' : ℝ → ι → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hc : ∀ i, ContinuousOn (fun u => T' u i) (Icc a b))
    {C : ℝ} (hB : ∀ u ∈ Icc a b, Summable (fun i => ‖T' u i‖) ∧ ∑' i, ‖T' u i‖ ≤ C) :
    IntervalIntegrable (fun u => ∑' i, T' u i) volume a b := by
  have hmem : ∀ u ∈ uIoc a b, u ∈ Icc a b := fun u hu => by
    rw [uIoc_of_le hab] at hu
    exact Ioc_subset_Icc_self hu
  refine (intervalIntegrable_const (c := C)).mono_fun ?_ ?_
  · refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
      (f := fun S u => ∑ i ∈ S, T' u i) (fun S =>
        ((continuousOn_finsetSum S fun i _ => hc i).mono hmem).aestronglyMeasurable
          measurableSet_uIoc) ?_
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine .of_forall fun u hu => ?_
    have := ((hB u (hmem u hu)).1.of_norm).hasSum
    simpa [HasSum] using this
  · change ∀ᵐ u ∂(volume.restrict (uIoc a b)), ‖∑' i, T' u i‖ ≤ ‖C‖
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine .of_forall fun u hu => ?_
    have h := hB u (hmem u hu)
    calc ‖∑' i, T' u i‖ ≤ ∑' i, ‖T' u i‖ := norm_tsum_le_tsum_norm h.1
      _ ≤ C := h.2
      _ ≤ ‖C‖ := le_abs_self C

/-! ### B. The product rule for the triad summand -/

/-- The helical projector as a linear map. -/
def helLin (a : Sgn) (k : Mode) : V3 →ₗ[ℂ] V3 :=
  { toFun := hel a k, map_add' := hel_add a k, map_smul' := hel_smul a k }

lemma continuous_hel (a : Sgn) (k : Mode) : Continuous (hel a k) :=
  (helLin a k).continuous_of_finiteDimensional

lemma hasDerivWithinAt_hel {a : Sgn} {k : Mode} {X : ℝ → V3} {X' : V3} {s : Set ℝ} {t : ℝ}
    (hX : HasDerivWithinAt X X' s t) :
    HasDerivWithinAt (fun u => hel a k (X u)) (hel a k X') s t :=
  ((helLin a k).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hX

lemma continuous_tau (p q : Mode) :
    Continuous (fun v : V3 × V3 × V3 => tau p q v.1 v.2.1 v.2.2) := by
  simp only [tau, dotM_eq, bd]
  fun_prop

lemma continuousOn_tau_comp {p q : Mode} {A B C : ℝ → V3} {s : Set ℝ} (hA : ContinuousOn A s)
    (hB : ContinuousOn B s) (hC : ContinuousOn C s) :
    ContinuousOn (fun u => tau p q (A u) (B u) (C u)) s := by
  simp only [tau, dotM_eq, bd]
  fun_prop

/-- The triad form `tau` is trilinear: the product rule along three paths. -/
lemma hasDerivWithinAt_tau {p q : Mode} {A B C : ℝ → V3} {A' B' C' : V3} {s : Set ℝ} {t : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hB : HasDerivWithinAt B B' s t)
    (hC : HasDerivWithinAt C C' s t) :
    HasDerivWithinAt (fun u => tau p q (A u) (B u) (C u))
      (tau p q A' (B t) (C t) + tau p q (A t) B' (C t) + tau p q (A t) (B t) C') s t := by
  have hcoord : ∀ (X : ℝ → V3) (X' : V3), HasDerivWithinAt X X' s t → ∀ i : Fin 3,
      HasDerivWithinAt (fun u => X u i) (X' i) s t := fun X X' hX i =>
    ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hX
  have hA0 := hcoord A A' hA 0; have hA1 := hcoord A A' hA 1; have hA2 := hcoord A A' hA 2
  have hB0 := hcoord B B' hB 0; have hB1 := hcoord B B' hB 1; have hB2 := hcoord B B' hB 2
  have hC0 := hcoord C C' hC 0; have hC1 := hcoord C C' hC 1; have hC2 := hcoord C C' hC 2
  have h := (((((hA0.mul_const (q 0 : ℂ)).add (hA1.mul_const (q 1 : ℂ))).add
      (hA2.mul_const (q 2 : ℂ))).mul
      (((hB0.mul hC0).add (hB1.mul hC1)).add (hB2.mul hC2))).add
      ((((hB0.mul_const (p 0 : ℂ)).add (hB1.mul_const (p 1 : ℂ))).add
        (hB2.mul_const (p 2 : ℂ))).mul
      (((hA0.mul hC0).add (hA1.mul hC1)).add (hA2.mul hC2)))).const_mul
      ((1 : ℂ) / 2 * Complex.I)
  simp only [tau, dotM_eq, bd]
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

/-- The formal derivative of the triad summand: all four slots (multiplier and three inputs)
differentiated. -/
def tripD (m m' : Mult) (X X' Y Y' Z Z' : Field) (p q : Mode) : ℂ :=
  tripT m' X Y Z p q + tripT m X' Y Z p q + tripT m X Y' Z p q + tripT m X Y Z' p q

/-- Product rule for the triad summand with a time-dependent multiplier. -/
lemma hasDerivWithinAt_tripT {m m' : ℝ → Mult} {X X' Y Y' Z Z' : ℝ → Field} {s : Set ℝ}
    {t : ℝ} (p q : Mode)
    (hm : ∀ a b c, HasDerivWithinAt (fun u => m u a b c p q) (m' t a b c p q) s t)
    (hX : HasDerivWithinAt (fun u => X u p) (X' t p) s t)
    (hY : HasDerivWithinAt (fun u => Y u q) (Y' t q) s t)
    (hZ : HasDerivWithinAt (fun u => Z u (-(p + q))) (Z' t (-(p + q))) s t) :
    HasDerivWithinAt (fun u => tripT (m u) (X u) (Y u) (Z u) p q)
      (tripD (m t) (m' t) (X t) (X' t) (Y t) (Y' t) (Z t) (Z' t) p q) s t := by
  have key : ∀ a b c, HasDerivWithinAt (fun u => m u a b c p q *
      tau p q (hel a p (X u p)) (hel b q (Y u q)) (hel c (-(p + q)) (Z u (-(p + q)))))
      (m' t a b c p q *
          tau p q (hel a p (X t p)) (hel b q (Y t q)) (hel c (-(p + q)) (Z t (-(p + q)))) +
        m t a b c p q *
          (tau p q (hel a p (X' t p)) (hel b q (Y t q)) (hel c (-(p + q)) (Z t (-(p + q)))) +
            tau p q (hel a p (X t p)) (hel b q (Y' t q)) (hel c (-(p + q)) (Z t (-(p + q)))) +
            tau p q (hel a p (X t p)) (hel b q (Y t q)) (hel c (-(p + q)) (Z' t (-(p + q))))))
      s t := by
    intro a b c
    have h1 : HasDerivWithinAt (fun u => hel a p (X u p)) (hel a p (X' t p)) s t :=
      hasDerivWithinAt_hel hX
    have h2 : HasDerivWithinAt (fun u => hel b q (Y u q)) (hel b q (Y' t q)) s t :=
      hasDerivWithinAt_hel hY
    have h3 : HasDerivWithinAt (fun u => hel c (-(p + q)) (Z u (-(p + q))))
        (hel c (-(p + q)) (Z' t (-(p + q)))) s t := hasDerivWithinAt_hel hZ
    have h4 := hasDerivWithinAt_tau (p := p) (q := q) h1 h2 h3
    have h5 := (hm a b c).mul h4
    exact h5
  have hsum := HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset Sgn)) fun a _ =>
    HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset Sgn)) fun b _ =>
      HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset Sgn)) fun c _ => key a b c
  simp only [tripT, tripD]
  refine hsum.congr_deriv ?_
  simp only [Finset.sum_add_distrib, mul_add]
  ring

/-- The triad family along paths, `(u, (p,q)) ↦ tripT (m u) (X u) (Y u) (Z u) p q` (a first-order
head, which keeps the unifier away from the triad sums). -/
def tripPath (m : ℝ → Mult) (X Y Z : ℝ → Field) (u : ℝ) (x : Mode × Mode) : ℂ :=
  tripT (m u) (X u) (Y u) (Z u) x.1 x.2

/-- The derivative family along paths. -/
def tripDPath (m m' : ℝ → Mult) (X X' Y Y' Z Z' : ℝ → Field) (u : ℝ) (x : Mode × Mode) : ℂ :=
  tripD (m u) (m' u) (X u) (X' u) (Y u) (Y' u) (Z u) (Z' u) x.1 x.2

lemma hasDerivWithinAt_tripPath {m m' : ℝ → Mult} {X X' Y Y' Z Z' : ℝ → Field} {s : Set ℝ}
    {t : ℝ} (x : Mode × Mode)
    (hm : ∀ a b c, HasDerivWithinAt (fun u => m u a b c x.1 x.2) (m' t a b c x.1 x.2) s t)
    (hX : HasDerivWithinAt (fun u => X u x.1) (X' t x.1) s t)
    (hY : HasDerivWithinAt (fun u => Y u x.2) (Y' t x.2) s t)
    (hZ : HasDerivWithinAt (fun u => Z u (-(x.1 + x.2))) (Z' t (-(x.1 + x.2))) s t) :
    HasDerivWithinAt (fun u => tripPath m X Y Z u x) (tripDPath m m' X X' Y Y' Z Z' t x) s t := by
  have h := hasDerivWithinAt_tripT x.1 x.2 hm hX hY hZ
  exact h

/-- Continuity of the triad summand along continuous paths. -/
lemma continuousOn_tripT {m : ℝ → Mult} {X Y Z : ℝ → Field} {s : Set ℝ} (p q : Mode)
    (hm : ∀ a b c, ContinuousOn (fun u => m u a b c p q) s)
    (hX : ContinuousOn (fun u => X u p) s) (hY : ContinuousOn (fun u => Y u q) s)
    (hZ : ContinuousOn (fun u => Z u (-(p + q))) s) :
    ContinuousOn (fun u => tripT (m u) (X u) (Y u) (Z u) p q) s := by
  have key : ∀ a b c, ContinuousOn (fun u => m u a b c p q *
      tau p q (hel a p (X u p)) (hel b q (Y u q)) (hel c (-(p + q)) (Z u (-(p + q))))) s := by
    intro a b c
    have hA : ContinuousOn (fun u => hel a p (X u p)) s :=
      (continuous_hel a p).comp_continuousOn hX
    have hB : ContinuousOn (fun u => hel b q (Y u q)) s :=
      (continuous_hel b q).comp_continuousOn hY
    have hC : ContinuousOn (fun u => hel c (-(p + q)) (Z u (-(p + q)))) s :=
      (continuous_hel c _).comp_continuousOn hZ
    have h4 := continuousOn_tau_comp (p := p) (q := q) hA hB hC
    exact (hm a b c).mul h4
  simp only [tripT]
  exact continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ =>
    continuousOn_finsetSum _ fun c _ => key a b c

/-- **E4.4, general form: the multilinear correction lemma.**  For three mode-wise differentiable
paths `X, Y, Z` and a mode-wise differentiable multiplier family `m` on `[a,b]`, the triad
functional `∑_{(p,q)} tripPath m X Y Z t (p,q) = ∑ tripT (m t) (X t) (Y t) (Z t) p q`
(`= ⟨Z t, Q^♯_{m t}(X t, Y t)⟩`) has the increment `∫ₐᵇ ∑_{(p,q)} tripDPath` (product rule
`hasDerivWithinAt_tripT`), provided the family is summable at the endpoints and the derivative
family is uniformly absolutely summable (`hB`, the summability control: for the kinetic functional
it is supplied by `norm_tripT_kinM_le`, `norm_tau_le` and the `ℓ¹ℓ²ℓ²` triple bounds). -/
theorem trilinear_integral_identity {m m' : ℝ → Mult} {X X' Y Y' Z Z' : ℝ → Field} {a b : ℝ}
    (hab : a ≤ b)
    (hm : ∀ a' b' c p q, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun u => m u a' b' c p q) (m' t a' b' c p q) (Icc a b) t)
    (hm' : ∀ a' b' c p q, ContinuousOn (fun u => m' u a' b' c p q) (Icc a b))
    (hX : ∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => X u k) (X' t k) (Icc a b) t)
    (hX' : ∀ k, ContinuousOn (fun u => X' u k) (Icc a b))
    (hY : ∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => Y u k) (Y' t k) (Icc a b) t)
    (hY' : ∀ k, ContinuousOn (fun u => Y' u k) (Icc a b))
    (hZ : ∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => Z u k) (Z' t k) (Icc a b) t)
    (hZ' : ∀ k, ContinuousOn (fun u => Z' u k) (Icc a b))
    (hsa : Summable (tripPath m X Y Z a)) (hsb : Summable (tripPath m X Y Z b))
    {C : ℝ} (hB : ∀ u ∈ Icc a b, Summable (fun x => ‖tripDPath m m' X X' Y Y' Z Z' u x‖) ∧
      ∑' x, ‖tripDPath m m' X X' Y Y' Z Z' u x‖ ≤ C) :
    (∑' x, tripPath m X Y Z b x) - ∑' x, tripPath m X Y Z a x =
      ∫ u in a..b, ∑' x, tripDPath m m' X X' Y Y' Z Z' u x := by
  have hmc : ∀ a' b' c p q, ContinuousOn (fun u => m u a' b' c p q) (Icc a b) :=
    fun a' b' c p q t ht => (hm a' b' c p q t ht).continuousWithinAt
  have hXc : ∀ k, ContinuousOn (fun u => X u k) (Icc a b) :=
    fun k t ht => (hX k t ht).continuousWithinAt
  have hYc : ∀ k, ContinuousOn (fun u => Y u k) (Icc a b) :=
    fun k t ht => (hY k t ht).continuousWithinAt
  have hZc : ∀ k, ContinuousOn (fun u => Z u k) (Icc a b) :=
    fun k t ht => (hZ k t ht).continuousWithinAt
  have hd : ∀ x : Mode × Mode, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun u => tripPath m X Y Z u x) (tripDPath m m' X X' Y Y' Z Z' t x)
        (Icc a b) t :=
    fun x t ht => hasDerivWithinAt_tripPath x (fun a' b' c => hm a' b' c x.1 x.2 t ht)
      (hX x.1 t ht) (hY x.2 t ht) (hZ _ t ht)
  have hc : ∀ x : Mode × Mode,
      ContinuousOn (fun u => tripDPath m m' X X' Y Y' Z Z' u x) (Icc a b) := by
    intro x
    have h1 := continuousOn_tripT x.1 x.2 (fun a' b' c => hm' a' b' c _ _) (hXc _) (hYc _) (hZc _)
    have h2 := continuousOn_tripT x.1 x.2 (fun a' b' c => hmc a' b' c _ _) (hX' _) (hYc _) (hZc _)
    have h3 := continuousOn_tripT x.1 x.2 (fun a' b' c => hmc a' b' c _ _) (hXc _) (hY' _) (hZc _)
    have h4 := continuousOn_tripT x.1 x.2 (fun a' b' c => hmc a' b' c _ _) (hXc _) (hYc _) (hZ' _)
    have h5 := ((h1.add h2).add h3).add h4
    exact h5
  exact integral_tsum_deriv hab hd hc hsa hsb hB

end OVNS

end
