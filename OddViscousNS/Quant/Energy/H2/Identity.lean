import OddViscousNS.Quant.Energy.H2.Defs

/-!
# E8 — the AC identity of the corrected `H²` energy along the actual solution

The E4.4-type identity for `½W = ½ b_F² + ½⟨z₂, X₁ z₂⟩ + E⁰₂` (`h2Energy`, `Defs.lean`).  The route
is that of `H1/Identity.lean` with the test path `A²F`, but `A²F ∉ ℓ²` at a generic time: the
solution
is only `C_t H² ∩ L²_t H³`, so the derivative family of the triad sum is **not** uniformly summable
and `trilinear_integral_identity` does not apply as stated (its `hB` is a constant bound).  The
fix is the dominated form:

* **A. `integral_tsum_deriv_ae`, `trilinear_integral_identity_ae`**: the same FTC with
  `∑‖T'‖ ≤ g(u)` at almost every `u` and `g ∈ L¹` (TeX: "the right sides are `L¹` in time"; LOCAL210
  §12: "`K2` is the actual `H³`-time expression, locally `L¹` on `CH² ∩ L²_loc H³` paths").
* **B.** The bridge `pair 2 W (Q^♯_m(X,Y)) = Re ∑ tripT m X Y (A²W)` (`pair_two_eq_re_tsum`).
* **C.** The four slot bounds at a time when `X, Y, W ∈ H³`, with `X', Y', W' ∈ ℓ²`
  (`slotM`, `slotX`, `slotY`, `slotW`); the dominating function is linear in `‖·‖₃`, hence `L¹`.
* **D.** `path_identity_two`: the generic identity for `pair 2 W (Q^♯_{m(u)}(X,Y))`.
* **E.** The heat algebra at weight two: `tripT_corr_heat_combine`, `tripT_met_heat_combine` of
  `H1/Identity.lean` at the test `W = AF`.
* **F.** `cubicCorr2_identity`, `metricCorr2_identity`.
* **G.** `cat_neutral_two` (catalytic neutrality at weight two, see `Defs.lean`), `fast_h2_law`,
  `h2Energy_identity`: `½W(t) − ½W(s) + ∫ c_F² = ∫ h2RHS`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.H2

/-! ### A. The dominated FTC for a summable family -/

/-- **FTC for a summable family, dominated form**: as `integral_tsum_deriv`, with the bound
`∑ᵢ ‖T' u i‖ ≤ g u` only at almost every `u` and `g` integrable. -/
theorem integral_tsum_deriv_ae {ι : Type*} [Countable ι] {T T' : ℝ → ι → ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hd : ∀ i, ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => T u i) (T' t i) (Icc a b) t)
    (hc : ∀ i, ContinuousOn (fun u => T' u i) (Icc a b))
    (hsa : Summable fun i => T a i) (hsb : Summable fun i => T b i)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    (hB : ∀ᵐ u ∂(volume.restrict (Icc a b)),
      Summable (fun i => ‖T' u i‖) ∧ ∑' i, ‖T' u i‖ ≤ g u) :
    IntervalIntegrable (fun u => ∑' i, T' u i) volume a b ∧
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
  have hB' : ∀ᵐ u, u ∈ uIoc a b → Summable (fun i => ‖T' u i‖) ∧ ∑' i, ‖T' u i‖ ≤ g u := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hB] with u hu hmemu
    exact hu (hmem u hmemu)
  have hlim : ∀ᵐ u, u ∈ uIoc a b → Tendsto (fun S : Finset ι => ∑ i ∈ S, T' u i) atTop
      (𝓝 (∑' i, T' u i)) := by
    filter_upwards [hB'] with u hu hmemu
    have := ((hu hmemu).1.of_norm).hasSum
    simpa [HasSum] using this
  have hmeas : ∀ S : Finset ι, AEStronglyMeasurable (fun u => ∑ i ∈ S, T' u i)
      (volume.restrict (uIoc a b)) := fun S =>
    ((continuousOn_finsetSum S fun i _ => hc i).mono hmem).aestronglyMeasurable measurableSet_uIoc
  have hint : IntervalIntegrable (fun u => ∑' i, T' u i) volume a b := by
    refine hg.mono_fun ?_ ?_
    · refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
        (f := fun S u => ∑ i ∈ S, T' u i) hmeas ?_
      exact (ae_restrict_iff' measurableSet_uIoc).2 hlim
    · refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
      filter_upwards [hB'] with u hu hmemu
      have h := hu hmemu
      calc ‖∑' i, T' u i‖ ≤ ∑' i, ‖T' u i‖ := norm_tsum_le_tsum_norm h.1
        _ ≤ g u := h.2
        _ ≤ ‖g u‖ := le_abs_self _
  refine ⟨hint, ?_⟩
  have h1 : Tendsto (fun S : Finset ι => (∑ i ∈ S, T b i) - ∑ i ∈ S, T a i) atTop
      (𝓝 ((∑' i, T b i) - ∑' i, T a i)) := by
    have := hsb.hasSum.sub hsa.hasSum
    simpa [HasSum, Finset.sum_sub_distrib] using this
  have h2 : Tendsto (fun S : Finset ι => ∫ u in a..b, ∑ i ∈ S, T' u i) atTop
      (𝓝 (∫ u in a..b, ∑' i, T' u i)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence g
      (.of_forall hmeas) ?_ hg hlim
    refine .of_forall fun S => ?_
    filter_upwards [hB'] with u hu hmemu
    have h := hu hmemu
    calc ‖∑ i ∈ S, T' u i‖ ≤ ∑ i ∈ S, ‖T' u i‖ := norm_sum_le _ _
      _ ≤ ∑' i, ‖T' u i‖ := h.1.sum_le_tsum S (fun _ _ => norm_nonneg _)
      _ ≤ g u := h.2
  exact tendsto_nhds_unique h1 (h2.congr fun S => (hfin S).symm)

/-- **E4.4, dominated form**: `trilinear_integral_identity` with the summability control only at
almost every time, by an integrable function (for the `H²` energy the control is `≲ 1 + ‖·‖₃²`). -/
theorem trilinear_integral_identity_ae {m m' : ℝ → Mult} {X X' Y Y' Z Z' : ℝ → Field} {a b : ℝ}
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
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    (hB : ∀ᵐ u ∂(volume.restrict (Icc a b)),
      Summable (fun x => ‖tripDPath m m' X X' Y Y' Z Z' u x‖) ∧
        ∑' x, ‖tripDPath m m' X X' Y Y' Z Z' u x‖ ≤ g u) :
    IntervalIntegrable (fun u => ∑' x, tripDPath m m' X X' Y Y' Z Z' u x) volume a b ∧
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
      ContinuousOn (fun u => tripDPath m m' X X' Y Y' Z Z' u x) (Icc a b) := fun x =>
    Quant.continuousOn_tripDPath x (fun a' b' c => hmc a' b' c _ _) (fun a' b' c => hm' a' b' c _ _)
      (hXc _) (hX' _) (hYc _) (hY' _) (hZc _) (hZ' _)
  exact integral_tsum_deriv_ae hab hd hc hsa hsb hg hB

/-! ### B. The bridge at weight two -/

/-- `pair 2 F G = pair 1 (AF) G`. -/
lemma pair_two_eq_pair_one_lap (F G : Field) : pair 2 F G = pair 1 (lapF F) G := by
  unfold pair
  refine tsum_congr fun k => ?_
  rw [sobWeight_two, sobWeight_one, lapF, inner_smul_left, Complex.conj_ofReal,
    Complex.re_ofReal_mul]
  ring

/-- `‖(Af)_k‖ = |k|² ‖f_k‖`. -/
lemma norm_lapF (f : Field) (k : Mode) : ‖lapF f k‖ = absSq k * ‖f k‖ := by
  simp only [lapF, norm_smul, Complex.norm_real, Real.norm_of_nonneg (absSq_nonneg k)]

/-- `sobWeight 3 k = |k|⁶`. -/
lemma sobWeight_three (k : Mode) : sobWeight 3 k = absSq k ^ 3 := by
  by_cases hk : k = 0
  · subst hk
    simp [sobWeight, absSq]
  · simp only [sobWeight, hk, ite_false]
    rw [show (2 * 3 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← absk_sq]
    ring

/-- **The bridge**: `pair 2 W (Q^♯_m(X,Y)) = Re ∑_{(p,q)} tripT m X Y (A²W) p q`. -/
lemma pair_two_eq_re_tsum {m : Mult} {X Y W : Field} (hW : IsReal W)
    (hin : ∀ k, inner ℂ (lapF (lapF W) k) (Qm m X Y k) =
      ∑' p, tripT m X Y (lapF (lapF W)) p (k - p))
    (hs : Summable fun x : Mode × Mode => tripT m X Y (lapF (lapF W)) x.1 x.2) :
    pair 2 W (Qm m X Y) = (∑' x : Mode × Mode, tripT m X Y (lapF (lapF W)) x.1 x.2).re := by
  rw [pair_two_eq_pair_one_lap]
  exact pair_one_eq_re_tsum hW.lapF hin hs

/-- The bridge for a gain multiplier. -/
lemma pair_two_eq_re_tsum_gain {m : Mult}
    (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    {X Y W : Field} (hW : IsReal W) (hX2 : Summable fun p => ‖X p‖ ^ 2)
    (hY2 : Summable fun p => ‖Y p‖ ^ 2)
    (hg : (Summable fun p => (absk p * ‖X p‖) ^ 2) ∨ Summable fun p => (absk p * ‖Y p‖) ^ 2)
    (hs : Summable fun x : Mode × Mode => tripT m X Y (lapF (lapF W)) x.1 x.2) :
    pair 2 W (Qm m X Y) = (∑' x : Mode × Mode, tripT m X Y (lapF (lapF W)) x.1 x.2).re := by
  rw [pair_two_eq_pair_one_lap]
  exact pair_one_eq_re_tsum_gain hm hW.lapF hX2 hY2 hg hs

/-! ### C. The slot bounds at a time when the fields are in `H³` -/

/-- `𝒜(∇X) = ∑ |k| ‖X_k‖ ≤ c₄ ‖X‖₃`. -/
lemma summable_wtd_one {X : Field} (hX : MZ 3 X) :
    Summable (wtd 1 X) ∧ ∑' k, wtd 1 X k ≤ c4 * hnorm 3 X := by
  set G : Field := fun k => (absk k : ℂ) • X k with hG
  have hn : ∀ k, ‖G k‖ = wtd 1 X k := fun k => by
    simp [hG, wtd, norm_smul, Real.norm_of_nonneg (absk_nonneg k)]
  have hw : ∀ k, sobWeight 2 k * ‖G k‖ ^ 2 = sobWeight 3 k * ‖X k‖ ^ 2 := fun k => by
    rw [hn, sobWeight_two, sobWeight_three, wtd, pow_one, mul_pow, absk_sq]
    ring
  have hI : InH 2 G := hX.inH.congr fun k => (hw k).symm
  have hG0 : G 0 = 0 := by simp [hG, hX.mean]
  have hN : hnorm 2 G = hnorm 3 X := by
    unfold hnorm
    exact congrArg _ (tsum_congr hw)
  have hs := summable_wiener hI
  have hle := wiener_le ⟨hI, hG0⟩
  refine ⟨hs.congr hn, ?_⟩
  have e : wiener G = ∑' k, wtd 1 X k := tsum_congr hn
  rwa [e, hN] at hle

/-- `‖X‖₂ ≤` sequences: the `ℓ²` facts of an `H³` field. -/
lemma wtd_l2 {X : Field} (hX : MZ 3 X) {n : ℕ} (hn : n ≤ 3) :
    Summable (fun k => wtd n X k ^ 2) ∧ Real.sqrt (∑' k, wtd n X k ^ 2) = hnorm n X := by
  have hn' : ((n : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hn
  exact ⟨summable_wtd_sq n (hX.inH.mono hn') hX.mean, sqrt_tsum_wtd_sq n hX.mean⟩

/-- The `ℓ²` facts of an `H²` field. -/
lemma wtd_l2_two {X : Field} (hX : MZ 2 X) :
    Summable (fun k => wtd 2 X k ^ 2) ∧ Real.sqrt (∑' k, wtd 2 X k ^ 2) = hnorm 2 X := by
  have h : InH ((2 : ℕ) : ℝ) X := by simpa using hX.inH
  have e := sqrt_tsum_wtd_sq (u := X) 2 hX.mean
  exact ⟨summable_wtd_sq 2 h hX.mean, by simpa using e⟩

private lemma absk_opp_le (p q : Mode) : absk (-(p + q)) ≤ absk p + absk q := by
  rw [absk_neg]
  exact absk_add_le p q

private lemma absk_opp_le_left (p q : Mode) : absk p ≤ absk (-(p + q)) + absk q := by
  rw [absk_neg]
  have := absk_sub_le (p + q) q
  rwa [add_sub_cancel_right] at this

private lemma absk_opp_le_right (p q : Mode) : absk q ≤ absk (-(p + q)) + absk p := by
  rw [absk_neg]
  have := absk_sub_le (p + q) p
  rwa [add_sub_cancel_left] at this

/-- The multiplier-derivative slot (`m'` bounded, the test `A²W`): five derivatives on `X, Y, W`,
`(|p|+|q|)|k|⁴ ≤ 2(|p|²+|q|²)|k|³`. -/
lemma slotM {m : Mult} (hm : m.Bdd) (X Y W : Field) (p q : Mode) :
    ‖tripT m X Y (lapF (lapF W)) p q‖ ≤
      16 * (wtd 2 X p * ‖Y q‖ * wtd 3 W (-(p + q)) + ‖X p‖ * wtd 2 Y q * wtd 3 W (-(p + q))) := by
  have h := norm_tripT_le hm X Y (lapF (lapF W)) p q
  have e : ‖lapF (lapF W) (-(p + q))‖ = absk (-(p + q)) ^ 4 * ‖W (-(p + q))‖ := by
    rw [norm_lapF, norm_lapF, ← absk_sq]
    ring
  rw [e] at h
  refine h.trans ?_
  simp only [wtd]
  set P := absk p
  set Q := absk q
  set K := absk (-(p + q))
  have hK := absk_opp_le p q
  have hP : 0 ≤ P := absk_nonneg _
  have hQ : 0 ≤ Q := absk_nonneg _
  have hK0 : 0 ≤ K := absk_nonneg _
  have hA : 0 ≤ ‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖ * K ^ 3 := by positivity
  have h1 : (P + Q) * K ≤ 2 * (P ^ 2 + Q ^ 2) := by nlinarith [sq_nonneg (P - Q)]
  have h2 := mul_le_mul_of_nonneg_right h1 hA
  calc 8 * ((P + Q) * ‖X p‖ * ‖Y q‖ * (K ^ 4 * ‖W (-(p + q))‖))
      = 8 * ((P + Q) * K * (‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖ * K ^ 3)) := by ring
    _ ≤ 8 * (2 * (P ^ 2 + Q ^ 2) * (‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖ * K ^ 3)) := by linarith
    _ = _ := by ring

/-- The first input slot (`m` with the gain, the input `X' ∈ ℓ²`). -/
lemma slotX {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q)) (X Y W : Field)
    (p q : Mode) :
    ‖tripT m X Y (lapF (lapF W)) p q‖ ≤
      8 * (‖X p‖ * ‖Y q‖ * wtd 3 W (-(p + q)) +
        2 * (‖X p‖ * wtd 1 Y q * wtd 2 W (-(p + q)))) := by
  have h := norm_tripT_gain_lap hm X Y (lapF W) p q
  have e : ‖lapF W (-(p + q))‖ = absk (-(p + q)) ^ 2 * ‖W (-(p + q))‖ := by
    rw [norm_lapF, ← absk_sq]
  rw [e] at h
  refine h.trans ?_
  simp only [wtd, pow_one]
  have hK := absk_opp_le_left p q
  set P := absk p
  set Q := absk q
  set K := absk (-(p + q))
  have hQ : 0 ≤ Q := absk_nonneg _
  have hK0 : 0 ≤ K := absk_nonneg _
  have hA : 0 ≤ ‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖ * K ^ 2 := by positivity
  have h1 : P + Q ≤ K + 2 * Q := by linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hA
  calc 8 * ((P + Q) * ‖X p‖ * ‖Y q‖ * (K ^ 2 * ‖W (-(p + q))‖))
      = 8 * ((P + Q) * (‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖ * K ^ 2)) := by ring
    _ ≤ 8 * ((K + 2 * Q) * (‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖ * K ^ 2)) := by linarith
    _ = _ := by ring

/-- The second input slot. -/
lemma slotY {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q)) (X Y W : Field)
    (p q : Mode) :
    ‖tripT m X Y (lapF (lapF W)) p q‖ ≤
      8 * (‖X p‖ * ‖Y q‖ * wtd 3 W (-(p + q)) +
        2 * (wtd 1 X p * ‖Y q‖ * wtd 2 W (-(p + q)))) := by
  have h := norm_tripT_gain_lap hm X Y (lapF W) p q
  have e : ‖lapF W (-(p + q))‖ = absk (-(p + q)) ^ 2 * ‖W (-(p + q))‖ := by
    rw [norm_lapF, ← absk_sq]
  rw [e] at h
  refine h.trans ?_
  simp only [wtd, pow_one]
  have hK := absk_opp_le_right p q
  set P := absk p
  set Q := absk q
  set K := absk (-(p + q))
  have hP : 0 ≤ P := absk_nonneg _
  have hK0 : 0 ≤ K := absk_nonneg _
  have hA : 0 ≤ ‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖ * K ^ 2 := by positivity
  have h1 : P + Q ≤ K + 2 * P := by linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hA
  calc 8 * ((P + Q) * ‖X p‖ * ‖Y q‖ * (K ^ 2 * ‖W (-(p + q))‖))
      = 8 * ((P + Q) * (‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖ * K ^ 2)) := by ring
    _ ≤ 8 * ((K + 2 * P) * (‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖ * K ^ 2)) := by linarith
    _ = _ := by ring

/-- The test slot (`m` with the gain, the test `A²W'` with `W' ∈ ℓ²`). -/
lemma slotW {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q)) (X Y W : Field)
    (p q : Mode) :
    ‖tripT m X Y (lapF (lapF W)) p q‖ ≤
      32 * (wtd 3 X p * ‖Y q‖ * ‖W (-(p + q))‖ + ‖X p‖ * wtd 3 Y q * ‖W (-(p + q))‖) := by
  have h := norm_tripT_gain_lap hm X Y (lapF W) p q
  have e : ‖lapF W (-(p + q))‖ = absk (-(p + q)) ^ 2 * ‖W (-(p + q))‖ := by
    rw [norm_lapF, ← absk_sq]
  rw [e] at h
  refine h.trans ?_
  simp only [wtd]
  have hK := absk_opp_le p q
  set P := absk p
  set Q := absk q
  set K := absk (-(p + q))
  have hP : 0 ≤ P := absk_nonneg _
  have hQ : 0 ≤ Q := absk_nonneg _
  have hK0 : 0 ≤ K := absk_nonneg _
  have hA : 0 ≤ ‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖ := by positivity
  have hK2 : K ^ 2 ≤ (P + Q) ^ 2 := pow_le_pow_left₀ hK0 hK 2
  have h1 : (P + Q) * K ^ 2 ≤ 4 * (P ^ 3 + Q ^ 3) := by
    have h3 : (P + Q) * K ^ 2 ≤ (P + Q) * (P + Q) ^ 2 := mul_le_mul_of_nonneg_left hK2 (by linarith)
    have h4 : (P + Q) ^ 3 ≤ 4 * (P ^ 3 + Q ^ 3) := by
      nlinarith [mul_nonneg (add_nonneg hP hQ) (sq_nonneg (P - Q))]
    nlinarith
  have h2 := mul_le_mul_of_nonneg_right h1 hA
  calc 8 * ((P + Q) * ‖X p‖ * ‖Y q‖ * (K ^ 2 * ‖W (-(p + q))‖))
      = 8 * ((P + Q) * K ^ 2 * (‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖)) := by ring
    _ ≤ 8 * (4 * (P ^ 3 + Q ^ 3) * (‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖)) := by linarith
    _ = _ := by ring

/-- The sum of the multiplier slot. -/
lemma slotM_sum {m : Mult} (hm : m.Bdd) {X Y W : Field} (hX2 : MZ 2 X) (hY2 : MZ 2 Y)
    (hW : MZ 3 W) :
    (Summable fun x : Mode × Mode => ‖tripT m X Y (lapF (lapF W)) x.1 x.2‖) ∧
      ∑' x : Mode × Mode, ‖tripT m X Y (lapF (lapF W)) x.1 x.2‖ ≤
        16 * (wiener Y * (hnorm 2 X * hnorm 3 W) + wiener X * (hnorm 2 Y * hnorm 3 W)) := by
  obtain ⟨sX2, eX2⟩ := wtd_l2_two hX2
  obtain ⟨sY2, eY2⟩ := wtd_l2_two hY2
  obtain ⟨sW3, eW3⟩ := wtd_l2 hW (n := 3) (by norm_num)
  obtain ⟨s1, b1⟩ := summable_tri_second (a := wtd 2 X) (c := wtd 3 W) (b := fun k => ‖Y k‖)
    (wtd_nonneg 2 X) (fun k => norm_nonneg _) (wtd_nonneg 3 W) sX2 sW3 (summable_wiener hY2.inH)
  obtain ⟨s2, b2⟩ := summable_tri_first (b := fun k => ‖X k‖) (a := wtd 2 Y) (c := wtd 3 W)
    (fun k => norm_nonneg _) (wtd_nonneg 2 Y) (wtd_nonneg 3 W) (summable_wiener hX2.inH) sY2 sW3
  rw [eX2, eW3] at b1
  rw [eY2, eW3] at b2
  push_cast at b1 b2
  have hG := (s1.add s2).mul_left 16
  have hle := fun x : Mode × Mode => slotM hm X Y W x.1 x.2
  have hS := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hG
  refine ⟨hS, (hS.tsum_le_tsum hle hG).trans ?_⟩
  rw [tsum_mul_left, s1.tsum_add s2]
  exact mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by norm_num)

/-- The sum of the first input slot (`X' ∈ ℓ²`). -/
lemma slotX_sum {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    {X' Y W : Field} (hX' : Summable fun k => ‖X' k‖ ^ 2) (hY : MZ 3 Y) (hW : MZ 3 W) :
    (Summable fun x : Mode × Mode => ‖tripT m X' Y (lapF (lapF W)) x.1 x.2‖) ∧
      ∑' x : Mode × Mode, ‖tripT m X' Y (lapF (lapF W)) x.1 x.2‖ ≤
        8 * (wiener Y * (Real.sqrt (∑' k, ‖X' k‖ ^ 2) * hnorm 3 W) +
          2 * ((∑' k, wtd 1 Y k) * (Real.sqrt (∑' k, ‖X' k‖ ^ 2) * hnorm 2 W))) := by
  have hY2 : MZ 2 Y := hY.mono' (by norm_num)
  obtain ⟨sW3, eW3⟩ := wtd_l2 hW (n := 3) (by norm_num)
  obtain ⟨sW2, eW2⟩ := wtd_l2 hW (n := 2) (by norm_num)
  obtain ⟨s1, b1⟩ := summable_tri_second (a := fun k => ‖X' k‖) (c := wtd 3 W)
    (b := fun k => ‖Y k‖) (fun k => norm_nonneg _) (fun k => norm_nonneg _) (wtd_nonneg 3 W)
    hX' sW3 (summable_wiener hY2.inH)
  obtain ⟨s2, b2⟩ := summable_tri_second (a := fun k => ‖X' k‖) (c := wtd 2 W) (b := wtd 1 Y)
    (fun k => norm_nonneg _) (wtd_nonneg 1 Y) (wtd_nonneg 2 W) hX' sW2 (summable_wtd_one hY).1
  rw [eW3] at b1
  rw [eW2] at b2
  push_cast at b1 b2
  have hG := (s1.add (s2.mul_left 2)).mul_left 8
  have hle := fun x : Mode × Mode => slotX hm X' Y W x.1 x.2
  have hS := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hG
  refine ⟨hS, (hS.tsum_le_tsum hle hG).trans ?_⟩
  rw [tsum_mul_left, s1.tsum_add (s2.mul_left 2), tsum_mul_left]
  have h2 := mul_le_mul_of_nonneg_left b2 (by norm_num : (0 : ℝ) ≤ 2)
  exact mul_le_mul_of_nonneg_left (add_le_add b1 h2) (by norm_num)

/-- The sum of the second input slot (`Y' ∈ ℓ²`). -/
lemma slotY_sum {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    {X Y' W : Field} (hX : MZ 3 X) (hY' : Summable fun k => ‖Y' k‖ ^ 2) (hW : MZ 3 W) :
    (Summable fun x : Mode × Mode => ‖tripT m X Y' (lapF (lapF W)) x.1 x.2‖) ∧
      ∑' x : Mode × Mode, ‖tripT m X Y' (lapF (lapF W)) x.1 x.2‖ ≤
        8 * (wiener X * (Real.sqrt (∑' k, ‖Y' k‖ ^ 2) * hnorm 3 W) +
          2 * ((∑' k, wtd 1 X k) * (Real.sqrt (∑' k, ‖Y' k‖ ^ 2) * hnorm 2 W))) := by
  have hX2 : MZ 2 X := hX.mono' (by norm_num)
  obtain ⟨sW3, eW3⟩ := wtd_l2 hW (n := 3) (by norm_num)
  obtain ⟨sW2, eW2⟩ := wtd_l2 hW (n := 2) (by norm_num)
  obtain ⟨s1, b1⟩ := summable_tri_first (b := fun k => ‖X k‖) (a := fun k => ‖Y' k‖)
    (c := wtd 3 W) (fun k => norm_nonneg _) (fun k => norm_nonneg _) (wtd_nonneg 3 W)
    (summable_wiener hX2.inH) hY' sW3
  obtain ⟨s2, b2⟩ := summable_tri_first (b := wtd 1 X) (a := fun k => ‖Y' k‖) (c := wtd 2 W)
    (wtd_nonneg 1 X) (fun k => norm_nonneg _) (wtd_nonneg 2 W) (summable_wtd_one hX).1 hY' sW2
  rw [eW3] at b1
  rw [eW2] at b2
  push_cast at b1 b2
  have hG := (s1.add (s2.mul_left 2)).mul_left 8
  have hle := fun x : Mode × Mode => slotY hm X Y' W x.1 x.2
  have hS := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hG
  refine ⟨hS, (hS.tsum_le_tsum hle hG).trans ?_⟩
  rw [tsum_mul_left, s1.tsum_add (s2.mul_left 2), tsum_mul_left]
  have h2 := mul_le_mul_of_nonneg_left b2 (by norm_num : (0 : ℝ) ≤ 2)
  exact mul_le_mul_of_nonneg_left (add_le_add b1 h2) (by norm_num)

/-- The sum of the test slot (`W' ∈ ℓ²`). -/
lemma slotW_sum {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    {X Y W' : Field} (hX : MZ 3 X) (hY : MZ 3 Y) (hW' : Summable fun k => ‖W' k‖ ^ 2) :
    (Summable fun x : Mode × Mode => ‖tripT m X Y (lapF (lapF W')) x.1 x.2‖) ∧
      ∑' x : Mode × Mode, ‖tripT m X Y (lapF (lapF W')) x.1 x.2‖ ≤
        32 * (wiener Y * (hnorm 3 X * Real.sqrt (∑' k, ‖W' k‖ ^ 2)) +
          wiener X * (hnorm 3 Y * Real.sqrt (∑' k, ‖W' k‖ ^ 2))) := by
  have hX2 : MZ 2 X := hX.mono' (by norm_num)
  have hY2 : MZ 2 Y := hY.mono' (by norm_num)
  obtain ⟨sX3, eX3⟩ := wtd_l2 hX (n := 3) (by norm_num)
  obtain ⟨sY3, eY3⟩ := wtd_l2 hY (n := 3) (by norm_num)
  obtain ⟨s1, b1⟩ := summable_tri_second (a := wtd 3 X) (c := fun k => ‖W' k‖)
    (b := fun k => ‖Y k‖) (wtd_nonneg 3 X) (fun k => norm_nonneg _) (fun k => norm_nonneg _)
    sX3 hW' (summable_wiener hY2.inH)
  obtain ⟨s2, b2⟩ := summable_tri_first (b := fun k => ‖X k‖) (a := wtd 3 Y)
    (c := fun k => ‖W' k‖) (fun k => norm_nonneg _) (wtd_nonneg 3 Y) (fun k => norm_nonneg _)
    (summable_wiener hX2.inH) sY3 hW'
  rw [eX3] at b1
  rw [eY3] at b2
  push_cast at b1 b2
  have hG := (s1.add s2).mul_left 32
  have hle := fun x : Mode × Mode => slotW hm X Y W' x.1 x.2
  have hS := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hG
  refine ⟨hS, (hS.tsum_le_tsum hle hG).trans ?_⟩
  rw [tsum_mul_left, s1.tsum_add s2]
  exact mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by norm_num)

/-- **The summability control of the derivative family at a time when `X, Y, W ∈ H³`**: the
four slots are absolutely summable with a sum linear in the `H³` norms. -/
lemma tripD_two_le {m m' : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    (hm' : m'.Bdd) {X X' Y Y' W W' : Field} (hX : MZ 3 X) (hY : MZ 3 Y) (hW : MZ 3 W)
    (hX' : Summable fun k => ‖X' k‖ ^ 2) (hY' : Summable fun k => ‖Y' k‖ ^ 2)
    (hW' : Summable fun k => ‖W' k‖ ^ 2) {M D : ℝ} (hXM : hnorm 2 X ≤ M) (hYM : hnorm 2 Y ≤ M)
    (hWM : hnorm 2 W ≤ M) (hXD : Real.sqrt (∑' k, ‖X' k‖ ^ 2) ≤ D)
    (hYD : Real.sqrt (∑' k, ‖Y' k‖ ^ 2) ≤ D) (hWD : Real.sqrt (∑' k, ‖W' k‖ ^ 2) ≤ D) :
    (Summable fun x : Mode × Mode =>
      ‖tripD m m' X X' Y Y' (lapF (lapF W)) (lapF (lapF W')) x.1 x.2‖) ∧
      ∑' x : Mode × Mode, ‖tripD m m' X X' Y Y' (lapF (lapF W)) (lapF (lapF W')) x.1 x.2‖ ≤
        48 * c4 * M * (M + D) * (hnorm 3 X + hnorm 3 Y + hnorm 3 W) := by
  have hX2 : MZ 2 X := hX.mono' (by norm_num)
  have hY2 : MZ 2 Y := hY.mono' (by norm_num)
  obtain ⟨s1, b1⟩ := slotM_sum hm' hX2 hY2 hW
  obtain ⟨s2, b2⟩ := slotX_sum hm hX' hY hW
  obtain ⟨s3, b3⟩ := slotY_sum hm hX hY' hW
  obtain ⟨s4, b4⟩ := slotW_sum hm hX hY hW'
  have hG := ((s1.add s2).add s3).add s4
  have hle : ∀ x : Mode × Mode, ‖tripD m m' X X' Y Y' (lapF (lapF W)) (lapF (lapF W')) x.1 x.2‖ ≤
      ‖tripT m' X Y (lapF (lapF W)) x.1 x.2‖ + ‖tripT m X' Y (lapF (lapF W)) x.1 x.2‖ +
        ‖tripT m X Y' (lapF (lapF W)) x.1 x.2‖ + ‖tripT m X Y (lapF (lapF W')) x.1 x.2‖ :=
    fun x => (norm_add_le _ _).trans (add_le_add norm_add₃_le le_rfl)
  have hS := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hG
  refine ⟨hS, (hS.tsum_le_tsum hle hG).trans ?_⟩
  rw [((s1.add s2).add s3).tsum_add s4, (s1.add s2).tsum_add s3, s1.tsum_add s2]
  have hc := c4_pos
  have hM0 : 0 ≤ M := (hnorm_nonneg 2 X).trans hXM
  have hD0 : 0 ≤ D := (Real.sqrt_nonneg _).trans hXD
  set x3 := hnorm 3 X
  set y3 := hnorm 3 Y
  set w3 := hnorm 3 W
  have hx3 : 0 ≤ x3 := hnorm_nonneg _ _
  have hy3 : 0 ≤ y3 := hnorm_nonneg _ _
  have hw3 : 0 ≤ w3 := hnorm_nonneg _ _
  have aX : wiener X ≤ c4 * M := (wiener_le hX2).trans (mul_le_mul_of_nonneg_left hXM hc.le)
  have aY : wiener Y ≤ c4 * M := (wiener_le hY2).trans (mul_le_mul_of_nonneg_left hYM hc.le)
  have aX0 := wiener_nonneg X
  have aY0 := wiener_nonneg Y
  have gX := (summable_wtd_one hX).2
  have gY := (summable_wtd_one hY).2
  have gX0 : 0 ≤ ∑' k, wtd 1 X k := tsum_nonneg (wtd_nonneg 1 X)
  have gY0 : 0 ≤ ∑' k, wtd 1 Y k := tsum_nonneg (wtd_nonneg 1 Y)
  set dX := Real.sqrt (∑' k, ‖X' k‖ ^ 2)
  set dY := Real.sqrt (∑' k, ‖Y' k‖ ^ 2)
  set dW := Real.sqrt (∑' k, ‖W' k‖ ^ 2)
  have dX0 : 0 ≤ dX := Real.sqrt_nonneg _
  have dY0 : 0 ≤ dY := Real.sqrt_nonneg _
  have dW0 : 0 ≤ dW := Real.sqrt_nonneg _
  have hcM : 0 ≤ c4 * M := by positivity
  have t1 : wiener Y * (hnorm 2 X * w3) ≤ c4 * M * (M * w3) :=
    mul_le_mul aY (mul_le_mul_of_nonneg_right hXM hw3) (mul_nonneg (hnorm_nonneg _ _) hw3) hcM
  have t2 : wiener X * (hnorm 2 Y * w3) ≤ c4 * M * (M * w3) :=
    mul_le_mul aX (mul_le_mul_of_nonneg_right hYM hw3) (mul_nonneg (hnorm_nonneg _ _) hw3) hcM
  have t3 : wiener Y * (dX * w3) ≤ c4 * M * (D * w3) :=
    mul_le_mul aY (mul_le_mul_of_nonneg_right hXD hw3) (by positivity) hcM
  have t4 : (∑' k, wtd 1 Y k) * (dX * hnorm 2 W) ≤ c4 * y3 * (D * M) :=
    mul_le_mul gY (mul_le_mul hXD hWM (hnorm_nonneg _ _) hD0)
      (mul_nonneg dX0 (hnorm_nonneg _ _)) (by positivity)
  have t5 : wiener X * (dY * w3) ≤ c4 * M * (D * w3) :=
    mul_le_mul aX (mul_le_mul_of_nonneg_right hYD hw3) (by positivity) hcM
  have t6 : (∑' k, wtd 1 X k) * (dY * hnorm 2 W) ≤ c4 * x3 * (D * M) :=
    mul_le_mul gX (mul_le_mul hYD hWM (hnorm_nonneg _ _) hD0)
      (mul_nonneg dY0 (hnorm_nonneg _ _)) (by positivity)
  have t7 : wiener Y * (x3 * dW) ≤ c4 * M * (x3 * D) :=
    mul_le_mul aY (mul_le_mul_of_nonneg_left hWD hx3) (by positivity) hcM
  have t8 : wiener X * (y3 * dW) ≤ c4 * M * (y3 * D) :=
    mul_le_mul aX (mul_le_mul_of_nonneg_left hWD hy3) (by positivity) hcM
  have e : 48 * c4 * M * (M + D) * (x3 + y3 + w3) =
      16 * (c4 * M * (M * w3) + c4 * M * (M * w3)) +
      8 * (c4 * M * (D * w3) + 2 * (c4 * y3 * (D * M))) +
      8 * (c4 * M * (D * w3) + 2 * (c4 * x3 * (D * M))) +
      32 * (c4 * M * (x3 * D) + c4 * M * (y3 * D)) +
      (48 * c4 * M * M * x3 + 48 * c4 * M * M * y3 + 16 * c4 * M * M * w3 +
        32 * c4 * M * D * w3) := by ring
  have hrest : 0 ≤ 48 * c4 * M * M * x3 + 48 * c4 * M * M * y3 + 16 * c4 * M * M * w3 +
      32 * c4 * M * D * w3 := by positivity
  rw [e]
  linarith

/-! ### D. The generic path identity -/

/-- The derivative family of `pair 2 W (Q^♯_m(X,Y))` along paths. -/
def twoFam (m m' : ℝ → Mult) (X X' Y Y' W W' : ℝ → Field) (u : ℝ) : ℂ :=
  ∑' x, tripDPath m m' X X' Y Y' (fun v => lapF (lapF (W v))) (fun v => lapF (lapF (W' v))) u x

/-- **The generic weight-two identity**: along paths with `C_t H²`-type bounds, `L²_t H³` control
and derivative slots in `ℓ²`, `pair 2 W (Q^♯_{m(u)}(X,Y))` is absolutely continuous, with
derivative the real part of the four-slot family `twoFam`. -/
theorem path_identity_two {m m' : ℝ → Mult} {X X' Y Y' W W' : ℝ → Field} {s t : ℝ} (hst : s ≤ t)
    (hgain : ∀ u a b c p q, ‖m u a b c p q‖ ≤ 1 / absSq (p + q))
    (hm'B : ∀ u, (m' u).Bdd)
    (hmd : ∀ a b c p q, ∀ u ∈ Icc s t,
      HasDerivWithinAt (fun v => m v a b c p q) (m' u a b c p q) (Icc s t) u)
    (hm'c : ∀ a b c p q, ContinuousOn (fun u => m' u a b c p q) (Icc s t))
    (hXd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => X v k) (X' u k) (Icc s t) u)
    (hX'c : ∀ k, ContinuousOn (fun u => X' u k) (Icc s t))
    (hYd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => Y v k) (Y' u k) (Icc s t) u)
    (hY'c : ∀ k, ContinuousOn (fun u => Y' u k) (Icc s t))
    (hWd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => W v k) (W' u k) (Icc s t) u)
    (hW'c : ∀ k, ContinuousOn (fun u => W' u k) (Icc s t))
    (hX2 : ∀ u ∈ Icc s t, MZ 2 (X u)) (hY2 : ∀ u ∈ Icc s t, MZ 2 (Y u))
    (hW2 : ∀ u ∈ Icc s t, MZ 2 (W u)) (hWr : ∀ u ∈ Icc s t, IsReal (W u))
    {M D : ℝ} (hXM : ∀ u ∈ Icc s t, hnorm 2 (X u) ≤ M) (hYM : ∀ u ∈ Icc s t, hnorm 2 (Y u) ≤ M)
    (hWM : ∀ u ∈ Icc s t, hnorm 2 (W u) ≤ M)
    (hXD : ∀ u ∈ Icc s t, (Summable fun k => ‖X' u k‖ ^ 2) ∧
      Real.sqrt (∑' k, ‖X' u k‖ ^ 2) ≤ D)
    (hYD : ∀ u ∈ Icc s t, (Summable fun k => ‖Y' u k‖ ^ 2) ∧
      Real.sqrt (∑' k, ‖Y' u k‖ ^ 2) ≤ D)
    (hWD : ∀ u ∈ Icc s t, (Summable fun k => ‖W' u k‖ ^ 2) ∧
      Real.sqrt (∑' k, ‖W' u k‖ ^ 2) ≤ D)
    (hae : ∀ᵐ u ∂(volume.restrict (Icc s t)), InH 3 (X u) ∧ InH 3 (Y u) ∧ InH 3 (W u))
    (hc3 : IntervalIntegrable (fun u => hnorm 3 (X u) ^ 2 + hnorm 3 (Y u) ^ 2 + hnorm 3 (W u) ^ 2)
      volume s t) :
    IntervalIntegrable (fun u => (twoFam m m' X X' Y Y' W W' u).re) volume s t ∧
      pair 2 (W t) (Qm (m t) (X t) (Y t)) - pair 2 (W s) (Qm (m s) (X s) (Y s)) =
        ∫ u in s..t, (twoFam m m' X X' Y Y' W W' u).re := by
  set Z : ℝ → Field := fun v => lapF (lapF (W v)) with hZdef
  set Z' : ℝ → Field := fun v => lapF (lapF (W' v)) with hZ'def
  have hZd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => Z v k) (Z' u k) (Icc s t) u :=
    fun k u hu => ((hWd k u hu).const_smul (absSq k : ℂ)).const_smul (absSq k : ℂ)
  have hZ'c : ∀ k, ContinuousOn (fun u => Z' u k) (Icc s t) := fun k =>
    ((hW'c k).const_smul (absSq k : ℂ)).const_smul (absSq k : ℂ)
  have hdat : ∀ {V : Field}, MZ 2 V → (Summable fun k => ‖V k‖) ∧
      (Summable fun k => ‖V k‖ ^ 2) ∧ Summable fun k => (absk k * ‖V k‖) ^ 2 := fun {V} hV =>
    ⟨summable_wiener hV.inH, summable_norm_sq_of_inH (hV.inH.mono (by norm_num)),
      summable_grad_sq hV⟩
  have hsum : ∀ u ∈ Icc s t, Summable fun x : Mode × Mode =>
      tripT (m u) (X u) (Y u) (lapF (lapF (W u))) x.1 x.2 := fun u hu => by
    obtain ⟨x1, -, x3⟩ := hdat (hX2 u hu)
    obtain ⟨y1, -, y3⟩ := hdat (hY2 u hu)
    have hb := (gradTri_bound (fun k => norm_nonneg (X u k)) (fun k => norm_nonneg (Y u k))
      (fun k => norm_nonneg (lapF (W u) k)) x1 x3 y1 y3 (lapF_l2 (hW2 u hu).inH).1).1
    exact Summable.of_norm_bounded (hb.mul_left 8) fun x =>
      norm_tripT_gain_lap (hgain u) (X u) (Y u) (lapF (W u)) x.1 x.2
  have hL : ∀ u ∈ Icc s t, (∑' x, tripPath m X Y Z u x).re =
      pair 2 (W u) (Qm (m u) (X u) (Y u)) := fun u hu => by
    obtain ⟨-, x2, x3⟩ := hdat (hX2 u hu)
    obtain ⟨-, y2, -⟩ := hdat (hY2 u hu)
    exact (pair_two_eq_re_tsum_gain (hgain u) (hWr u hu) x2 y2 (Or.inl x3) (hsum u hu)).symm
  have hM0 : 0 ≤ M := (hnorm_nonneg 2 (X s)).trans (hXM s ⟨le_rfl, hst⟩)
  have hD0 : 0 ≤ D := (Real.sqrt_nonneg _).trans (hXD s ⟨le_rfl, hst⟩).2
  have hc := c4_pos
  set C := 48 * c4 * M * (M + D) with hCdef
  have hC0 : 0 ≤ C := by positivity
  set gf : ℝ → ℝ := fun u =>
    C * (3 + (hnorm 3 (X u) ^ 2 + hnorm 3 (Y u) ^ 2 + hnorm 3 (W u) ^ 2)) with hgf
  have hgi : IntervalIntegrable gf volume s t :=
    ((intervalIntegrable_const (c := (3 : ℝ))).add hc3).const_mul C
  have hB : ∀ᵐ u ∂(volume.restrict (Icc s t)),
      Summable (fun x => ‖tripDPath m m' X X' Y Y' Z Z' u x‖) ∧
        ∑' x, ‖tripDPath m m' X X' Y Y' Z Z' u x‖ ≤ gf u := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with u hu hmem
    obtain ⟨hx3, hy3, hw3⟩ := hu
    have hmx : MZ 3 (X u) := ⟨hx3, (hX2 u hmem).mean⟩
    have hmy : MZ 3 (Y u) := ⟨hy3, (hY2 u hmem).mean⟩
    have hmw : MZ 3 (W u) := ⟨hw3, (hW2 u hmem).mean⟩
    obtain ⟨hS, hle⟩ := tripD_two_le (hgain u) (hm'B u) hmx hmy hmw (hXD u hmem).1 (hYD u hmem).1
      (hWD u hmem).1 (hXM u hmem) (hYM u hmem) (hWM u hmem) (hXD u hmem).2 (hYD u hmem).2
      (hWD u hmem).2
    refine ⟨hS, hle.trans ?_⟩
    have h1 : hnorm 3 (X u) ≤ (1 + hnorm 3 (X u) ^ 2) / 2 := by
      nlinarith [sq_nonneg (hnorm 3 (X u) - 1)]
    have h2 : hnorm 3 (Y u) ≤ (1 + hnorm 3 (Y u) ^ 2) / 2 := by
      nlinarith [sq_nonneg (hnorm 3 (Y u) - 1)]
    have h3 : hnorm 3 (W u) ≤ (1 + hnorm 3 (W u) ^ 2) / 2 := by
      nlinarith [sq_nonneg (hnorm 3 (W u) - 1)]
    have h4 : hnorm 3 (X u) + hnorm 3 (Y u) + hnorm 3 (W u) ≤
        3 + (hnorm 3 (X u) ^ 2 + hnorm 3 (Y u) ^ 2 + hnorm 3 (W u) ^ 2) := by
      nlinarith [sq_nonneg (hnorm 3 (X u)), sq_nonneg (hnorm 3 (Y u)),
        sq_nonneg (hnorm 3 (W u))]
    exact mul_le_mul_of_nonneg_left h4 hC0
  obtain ⟨hI, key⟩ := trilinear_integral_identity_ae (m := m) (m' := m') (X := X) (X' := X')
    (Y := Y) (Y' := Y') (Z := Z) (Z' := Z') hst hmd hm'c hXd hX'c hYd hY'c hZd hZ'c
    (hsum s ⟨le_rfl, hst⟩) (hsum t ⟨hst, le_rfl⟩) hgi hB
  have hIre : IntervalIntegrable (fun u => (twoFam m m' X X' Y Y' W W' u).re) volume s t := by
    refine hI.mono_fun ?_ ?_
    · exact Complex.continuous_re.comp_aestronglyMeasurable
        ((intervalIntegrable_iff.1 hI).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall fun u => by
        simpa [Real.norm_eq_abs, twoFam, hZdef, hZ'def] using Complex.abs_re_le_norm _
  refine ⟨hIre, ?_⟩
  have hR := congrArg Complex.re key
  rw [Complex.sub_re, hL t ⟨hst, le_rfl⟩, hL s ⟨le_rfl, hst⟩] at hR
  rw [hR, ← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hI]
  rfl


variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### E. The heat pairs at `σ = 2` -/

private lemma two_rpow_two'' : (2 : ℝ) ^ (2 : ℝ) = 4 := by
  rw [Real.rpow_two]
  norm_num

/-- (M4) at `σ = 2`: `Q^♯_m(f,g) ∈ H¹`, `‖Q^♯_m(f,g)‖₁ ≤ 4(𝒜(f)‖g‖₂ + ‖f‖₂𝒜(g))`. -/
lemma Qm_one_le {m : Mult} (hm : m.Bdd) {f h : Field} (hf : MZ 2 f) (hh : MZ 2 h) :
    InH 1 (Qm m f h) ∧ hnorm 1 (Qm m f h) ≤ 4 * (wiener f * hnorm 2 h + hnorm 2 f * wiener h) := by
  have := hnorm_Qm_le hm (σ := 2) (by norm_num) hf hh hf hh
  rw [show (2 : ℝ) - 1 = 1 by norm_num, two_rpow_two''] at this
  exact this

/-- (M4) at `σ = 3`: `Q^♯_m(f,g) ∈ H²`, `‖Q^♯_m(f,g)‖₂ ≤ 8(𝒜(f)‖g‖₃ + ‖f‖₃𝒜(g))`. -/
lemma Qm_two_le {m : Mult} (hm : m.Bdd) {f h : Field} (hf : MZ 3 f) (hh : MZ 3 h) :
    InH 2 (Qm m f h) ∧ hnorm 2 (Qm m f h) ≤ 8 * (wiener f * hnorm 3 h + hnorm 3 f * wiener h) := by
  have := hnorm_Qm_le hm (σ := 3) (by norm_num) hf hh (hf.mono' (by norm_num))
    (hh.mono' (by norm_num))
  rw [show (3 : ℝ) - 1 = 2 by norm_num,
    show (2 : ℝ) ^ (3 : ℝ) = 8 by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num] at this
  exact this

/-- The sup bound of `‖Q_{rt}(y,y)‖₁` on `[0,b]`. -/
lemma exists_Qphase_one_bound (h : ActualSol μ φ r g y Ty) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc 0 b, InH 1 (Qphase (r * t) (y t) (y t)) ∧
      hnorm 1 (Qphase (r * t) (y t) (y t)) ≤ D := by
  obtain ⟨M, hM⟩ := h.sol.exists_bound hbT
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨8 * c4 * max M 0 ^ 2, by have := c4_pos; positivity, fun t ht => ?_⟩
  have hy := (h.sol.adm t ht.1 (lt_lifespan ht.2 hbT)).mz
  obtain ⟨hI, hle⟩ := Qm_one_le (phaseM_bdd (r * t)) hy hy
  refine ⟨hI, hle.trans ?_⟩
  have h1 : hnorm 2 (y t) ≤ max M 0 := (hM t ht).trans (le_max_left _ _)
  have h2 : wiener (y t) ≤ c4 * max M 0 :=
    (wiener_le hy).trans (mul_le_mul_of_nonneg_left h1 c4_pos.le)
  have h3 := hnorm_nonneg 2 (y t)
  have h4 := wiener_nonneg (y t)
  have h5 := c4_pos
  have h6 : wiener (y t) * hnorm 2 (y t) ≤ c4 * max M 0 * max M 0 :=
    mul_le_mul h2 h1 h3 (by positivity)
  nlinarith

private lemma force_l2_of_bound {u : ℝ → Field} {b D : ℝ}
    (hu : ∀ t ∈ Icc 0 b, InH 1 (u t) ∧ hnorm 1 (u t) ≤ D) :
    ∫⁻ t in Icc 0 b, hsE (2 - 1) (u t) < ∞ := by
  rw [show (2 : ℝ) - 1 = 1 by norm_num]
  calc ∫⁻ t in Icc 0 b, hsE 1 (u t)
      ≤ ∫⁻ _ in Icc 0 b, ENNReal.ofReal (D ^ 2) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        obtain ⟨hI, hle⟩ := hu t ht
        rw [hsE_eq_ofReal hI]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hnorm_nonneg _ _) hle 2)
    _ < ∞ := by
        rw [setLIntegral_const, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **The fast part is a `HeatPair` at `σ = 2`** (spec §E8: "the energy identity at `σ = 2`"), with
force `−Π_F Q_{rt}(y,y) ∈ L²_t H¹`. -/
theorem heatPair_fast_two (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) :
    HeatPair 2 0 b (fun t => PiF (actual r g y t)) (fun t => fastNL r g y t) := by
  refine ⟨fun t ht => (actual_adm h ht.1 (lt_lifespan ht.2 hbT)).inH.PiF, fun k t ht => ?_,
    fun k => ?_, ?_⟩
  · refine ((fast_mode h k ht.1 (lt_lifespan ht.2 hbT)).mono Icc_subset_Ici_self).congr_deriv ?_
    simp only [fastRHS, fastNL, Pi.neg_apply]
    abel
  · exact (continuousOn_PiF_Qphase_mode h hb hbT k).neg
  · obtain ⟨D, -, hD⟩ := exists_Qphase_one_bound h hbT
    refine force_l2_of_bound (D := D) fun t ht => ?_
    obtain ⟨hI, hle⟩ := hD t ht
    refine ⟨hI.PiF.neg, ?_⟩
    unfold fastNL
    rw [hnorm_neg]
    exact (hnorm_PiF_le hI).trans hle

/-- **The slow part is a `HeatPair` at `σ = 2`**, with force `−Π_S Q_{rt}(y,y) + Π_S g`. -/
theorem heatPair_slow_two (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) :
    HeatPair 2 0 b (fun t => PiS (actual r g y t)) (fun t => slowNL r g y t) := by
  have hg1 : InH 1 g := h.force_adm.inH.mono (by norm_num)
  refine ⟨fun t ht => (actual_adm h ht.1 (lt_lifespan ht.2 hbT)).inH.PiS, fun k t ht => ?_,
    fun k => ?_, ?_⟩
  · refine ((slow_mode h k ht.1 (lt_lifespan ht.2 hbT)).mono Icc_subset_Ici_self).congr_deriv ?_
    simp only [slowRHS, slowNL, Pi.add_apply, Pi.neg_apply]
    abel
  · exact (continuousOn_PiS_Qphase_mode h hb hbT k).neg.add continuousOn_const
  · obtain ⟨D, -, hD⟩ := exists_Qphase_one_bound h hbT
    refine force_l2_of_bound (D := D + hnorm 1 g) fun t ht => ?_
    obtain ⟨hI, hle⟩ := hD t ht
    refine ⟨hI.PiS.neg.add hg1.PiS, ?_⟩
    unfold slowNL
    refine (hnorm_add_le hI.PiS.neg hg1.PiS).trans ?_
    rw [hnorm_neg]
    exact add_le_add ((hnorm_PiS_le hI).trans hle) (hnorm_PiS_le hg1)

/-- `S(u), F(u) ∈ H³` at almost every time of a piece. -/
theorem ae_inH3_split (h : ActualSol μ φ r g y Ty) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)),
      InH 3 (PiF (actual r g y u)) ∧ InH 3 (PiS (actual r g y u)) := by
  have ht0 := hs.trans hst
  have h1 := ((heatPair_fast_two h ht0 ht).mono hs le_rfl).ae_inH hst
  have h2 := ((heatPair_slow_two h ht0 ht).mono hs le_rfl).ae_inH hst
  filter_upwards [h1, h2] with u hu1 hu2
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at hu1 hu2
  exact ⟨hu1, hu2⟩

/-- `c_F²` is integrable on a piece, and the `H²` law of the fast part (TeX:
`½(b_F²)' + c_F² = ⟨A²F, fastNL⟩`, integrated). -/
theorem fast_h2_law (h : ActualSol μ φ r g y Ty) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (fun u => fastNorm 3 r g y u ^ 2) volume s t ∧
      IntervalIntegrable (fun u => pair 2 (PiF (actual r g y u)) (fastNL r g y u)) volume s t ∧
      1 / 2 * fastNorm 2 r g y t ^ 2 - 1 / 2 * fastNorm 2 r g y s ^ 2 +
        (∫ u in s..t, fastNorm 3 r g y u ^ 2) =
        ∫ u in s..t, pair 2 (PiF (actual r g y u)) (fastNL r g y u) := by
  have hP := (heatPair_fast_two h (hs.trans hst) ht)
  have hid := hP.energy_identity hs hst le_rfl
  have hP' := hP.mono hs le_rfl
  have h1 := hP'.intervalIntegrable_dissipation hst
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at hid h1
  refine ⟨h1, hP'.intervalIntegrable_pair hst, ?_⟩
  unfold fastNorm
  linarith

/-- `c_S²` is integrable on a piece. -/
theorem slow_c3_integrable (h : ActualSol μ φ r g y Ty) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (fun u => hnorm 3 (PiS (actual r g y u)) ^ 2) volume s t := by
  have h1 := ((heatPair_slow_two h (hs.trans hst) ht).mono hs
    le_rfl).intervalIntegrable_dissipation hst
  rwa [show (2 : ℝ) + 1 = 3 by norm_num] at h1

/-! ### F. Along the actual solution -/

/-- The integrand of the derivative of `E⁰₂` along the actual solution (TeX: "the same
construction at weight two"): `⟨A²F, Q_nr(F,F)⟩ − E₂_heat + DE⁰₂[fastNL]`. -/
def cubicRHS2 (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  pair 2 (PiF (actual r g y u)) (Qnr (r * u) (PiF (actual r g y u)) (PiF (actual r g y u))) -
    cubicHeat2 r (r * u) (PiF (actual r g y u)) +
    cubicD 2 (-1) r (r * u) (PiF (actual r g y u)) (fastNL r g y u)

/-- The integrand of the derivative of `⟨z₂, X₁ z₂⟩` along the actual solution. -/
def metricRHS2 (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  4 * (pair 2 (PiF (actual r g y u))
      (Qm (metDM (r * u)) (PiS (actual r g y u)) (PiF (actual r g y u))) +
    pair 2 (PiF (actual r g y u)) (X1op r (r * u) (slowNL r g y u) (PiF (actual r g y u))) +
    pair 2 (PiF (actual r g y u)) (X1op r (r * u) (PiS (actual r g y u)) (fastNL r g y u)) +
    pair 2 (fastNL r g y u) (X1op r (r * u) (PiS (actual r g y u)) (PiF (actual r g y u))))

/-- The data of the paths on a piece: the sup bounds. -/
private lemma path_bounds (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (ht : ENNReal.ofReal t < Ty) :
    ∃ M D : ℝ, 0 ≤ D ∧ (∀ u ∈ Icc s t, hnorm 2 (PiF (actual r g y u)) ≤ M ∧
      hnorm 2 (PiS (actual r g y u)) ≤ M) ∧
      (∀ u ∈ Icc s t, (Summable fun k => ‖fastRHS r g y u k‖ ^ 2) ∧
        Real.sqrt (∑' k, ‖fastRHS r g y u k‖ ^ 2) ≤ D) ∧
      (∀ u ∈ Icc s t, (Summable fun k => ‖slowRHS r g y u k‖ ^ 2) ∧
        Real.sqrt (∑' k, ‖slowRHS r g y u k‖ ^ 2) ≤ D) := by
  obtain ⟨Mx, hMx0, hMx⟩ := exists_actual_bound h hr ht
  obtain ⟨D, hD0, hD⟩ := exists_Qphase_bound h ht
  have hg2 := hnorm_nonneg 2 g
  have hmem : ∀ u ∈ Icc s t, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hs.trans hu.1, lt_lifespan hu.2 ht⟩
  have hF : ∀ u ∈ Icc s t, hnorm 2 (PiF (actual r g y u)) ≤ Mx := fun u hu =>
    (hnorm_PiF_le (actual_adm h (hmem u hu).1 (hmem u hu).2).inH).trans
      (hMx u ⟨(hmem u hu).1, hu.2⟩)
  have hS : ∀ u ∈ Icc s t, hnorm 2 (PiS (actual r g y u)) ≤ Mx := fun u hu =>
    (hnorm_PiS_le (actual_adm h (hmem u hu).1 (hmem u hu).2).inH).trans
      (hMx u ⟨(hmem u hu).1, hu.2⟩)
  refine ⟨Mx, Mx + D + hnorm 2 g, by positivity, fun u hu => ⟨hF u hu, hS u hu⟩, fun u hu => ?_,
    fun u hu => ?_⟩
  · obtain ⟨h1, h2⟩ := fastRHS_l2 h (hmem u hu).1 (hmem u hu).2
    refine ⟨h1, h2.trans ?_⟩
    have := (hD u ⟨(hmem u hu).1, hu.2⟩).2
    have := hF u hu
    linarith
  · obtain ⟨h1, h2⟩ := slowRHS_l2 h (hmem u hu).1 (hmem u hu).2
    refine ⟨h1, h2.trans ?_⟩
    have := (hD u ⟨(hmem u hu).1, hu.2⟩).2
    have := hS u hu
    linarith

/-- **`E⁰₂` is absolutely continuous along the actual solution** with derivative `cubicRHS2`
(TeX "Its exact derivative is …", "the same construction at weight two"):
`E⁰₂(t) − E⁰₂(s) = ∫ₛᵗ (⟨A²F, Q_nr(F,F)⟩ − E₂_heat + DE⁰₂[fastNL])`.  Route: `path_identity_two`
with the paths `F, F, F`, the multiplier `corrM(−1, r, ru)`, the heat combination
`tripT_corr_heat_combine` at the test `W = AF`, at almost every time (`F(u) ∈ H³`). -/
theorem cubicCorr2_identity (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (cubicRHS2 r g y) volume s t ∧
      cubicCorr2 r g y t - cubicCorr2 r g y s = ∫ u in s..t, cubicRHS2 r g y u := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hmem : ∀ u ∈ Icc s t, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hs.trans hu.1, lt_lifespan hu.2 ht⟩
  set X : ℝ → Field := fun u => PiF (actual r g y u) with hXdef
  set X' : ℝ → Field := fastRHS r g y with hX'def
  set m : ℝ → Mult := fun u => corrM (-1) r (r * u) with hmdef
  set m' : ℝ → Mult := fun u => corrDM (-1) r (r * u) with hm'def
  have hgain : ∀ u a b c p q, ‖m u a b c p q‖ ≤ 1 / absSq (p + q) := fun u a b c p q =>
    corrM_gain (-1) r (r * u) (Or.inr rfl) a b c p q
  have hm'B : ∀ u, (m' u).Bdd := fun u => corrDM_bdd (Or.inr rfl) r (r * u)
  have hadm : ∀ u ∈ Icc s t, Adm 2 (X u) := fun u hu =>
    (actual_adm h (hmem u hu).1 (hmem u hu).2).PiF
  have hXd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => X v k) (X' u k) (Icc s t) u :=
    fun k u hu => (fast_mode h k (hmem u hu).1 (hmem u hu).2).mono fun v hv =>
      show v ∈ Ici 0 from hs.trans hv.1
  have hX'c : ∀ k, ContinuousOn (fun u => X' u k) (Icc s t) := fun k =>
    (continuousOn_fastRHS_mode h ht0 ht k).mono (Icc_subset_Icc_left hs)
  have hmd : ∀ a b c p q, ∀ u ∈ Icc s t,
      HasDerivWithinAt (fun v => m v a b c p q) (m' u a b c p q) (Icc s t) u :=
    fun a b c p q u _ => (hasDerivAt_corrM (-1) r a b c p q u).hasDerivWithinAt
  have hm'c : ∀ a b c p q, ContinuousOn (fun u => m' u a b c p q) (Icc s t) :=
    fun a b c p q => (continuous_corrDM (-1) r a b c p q).continuousOn
  obtain ⟨M, D, -, hMb, hDf, -⟩ := path_bounds h hr hs ht
  have hc3I := (fast_h2_law h hs hst ht).1
  have hae3 := ae_inH3_split h hs hst ht
  obtain ⟨hI, key⟩ := path_identity_two (m := m) (m' := m') (X := X) (X' := X') (Y := X) (Y' := X')
    (W := X) (W' := X') (M := M) (D := D) hst hgain hm'B hmd hm'c hXd hX'c hXd hX'c hXd hX'c
    (fun u hu => (hadm u hu).mz) (fun u hu => (hadm u hu).mz) (fun u hu => (hadm u hu).mz)
    (fun u hu => (hadm u hu).real) (fun u hu => (hMb u hu).1) (fun u hu => (hMb u hu).1)
    (fun u hu => (hMb u hu).1) hDf hDf hDf
    (hae3.mono fun u hu => ⟨hu.1, hu.1, hu.1⟩) ((hc3I.add hc3I).add hc3I)
  -- the integrand at almost every time
  have hre : ∀ᵐ u ∂(volume.restrict (Icc s t)),
      (twoFam m m' X X' X X' X X' u).re = cubicRHS2 r g y u := by
    filter_upwards [hae3, ae_restrict_mem measurableSet_Icc] with u hu3 hu
    have hu0 := (hmem u hu).1
    have huT := (hmem u hu).2
    have hF2 : MZ 2 (X u) := (hadm u hu).mz
    have hF3 : MZ 3 (X u) := ⟨hu3.1, hF2.mean⟩
    obtain ⟨hNr, hN2, -⟩ := fastNL_l2 h hu0 huT
    have hreal : IsReal (X u) := (hadm u hu).real
    have hl2 : Summable fun k => ‖X u k‖ ^ 2 := (adm_summables (hadm u hu)).2.1
    have hg2 : Summable fun k => (absk k * ‖X u k‖) ^ 2 := (adm_summables (hadm u hu)).2.2.1
    have hlap2 : Summable fun k => ‖lapF (X u) k‖ ^ 2 := (lapF_l2 (hadm u hu).inH).1
    have hX'eq : X' u = -lapF (X u) + fastNL r g y u := fastRHS_eq_lap u
    have hZ'eq : lapF (lapF (-lapF (X u) + fastNL r g y u)) =
        -lapF (lapF (lapF (X u))) + lapF (lapF (fastNL r g y u)) := by
      rw [lapF_add, lapF_add, lapF_neg, lapF_neg]
    have sA1 : Summable fun x : Mode × Mode =>
        tripT (nonresM (r * u)) (X u) (X u) (lapF (lapF (X u))) x.1 x.2 :=
      (slotM_sum (nonresM_bdd (r * u)) hF2 hF2 hF3).1.of_norm
    have sA2 : Summable fun x : Mode × Mode =>
        tripT (m u) (lapF (X u)) (X u) (lapF (lapF (X u))) x.1 x.2 :=
      (slotX_sum (hgain u) hlap2 hF3 hF3).1.of_norm
    have sA3 : Summable fun x : Mode × Mode =>
        tripT (m u) (fastNL r g y u) (X u) (lapF (lapF (X u))) x.1 x.2 :=
      (slotX_sum (hgain u) hN2 hF3 hF3).1.of_norm
    have sA4 : Summable fun x : Mode × Mode =>
        tripT (m u) (X u) (lapF (X u)) (lapF (lapF (X u))) x.1 x.2 :=
      (slotY_sum (hgain u) hF3 hlap2 hF3).1.of_norm
    have sA5 : Summable fun x : Mode × Mode =>
        tripT (m u) (X u) (fastNL r g y u) (lapF (lapF (X u))) x.1 x.2 :=
      (slotY_sum (hgain u) hF3 hN2 hF3).1.of_norm
    have sA6 : Summable fun x : Mode × Mode =>
        tripT (m u) (X u) (X u) (lapF (lapF (fastNL r g y u))) x.1 x.2 :=
      (slotW_sum (hgain u) hF3 hF3 hN2).1.of_norm
    have hpt : ∀ x : Mode × Mode, tripDPath m m' X X' X X' (fun v => lapF (lapF (X v)))
        (fun v => lapF (lapF (X' v))) u x =
        tripT (nonresM (r * u)) (X u) (X u) (lapF (lapF (X u))) x.1 x.2 +
        (-tripT (m u) (lapF (X u)) (X u) (lapF (lapF (X u))) x.1 x.2) +
        tripT (m u) (fastNL r g y u) (X u) (lapF (lapF (X u))) x.1 x.2 +
        (-tripT (m u) (X u) (lapF (X u)) (lapF (lapF (X u))) x.1 x.2) +
        tripT (m u) (X u) (fastNL r g y u) (lapF (lapF (X u))) x.1 x.2 +
        tripT (m u) (X u) (X u) (lapF (lapF (fastNL r g y u))) x.1 x.2 := by
      intro x
      simp only [tripDPath, tripD]
      rw [hX'eq, hZ'eq, tripT_add_left, tripT_add_mid, tripT_add_right, tripT_neg_left,
        tripT_neg_mid]
      have hc := tripT_corr_heat_combine r (r * u) (X u) (X u) (lapF (X u)) x.1 x.2
      simp only [hmdef, hm'def] at hc ⊢
      linear_combination hc
    have hsplit : twoFam m m' X X' X X' X X' u =
        (∑' x : Mode × Mode, tripT (nonresM (r * u)) (X u) (X u) (lapF (lapF (X u))) x.1 x.2) +
        (-∑' x : Mode × Mode, tripT (m u) (lapF (X u)) (X u) (lapF (lapF (X u))) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (fastNL r g y u) (X u) (lapF (lapF (X u))) x.1 x.2) +
        (-∑' x : Mode × Mode, tripT (m u) (X u) (lapF (X u)) (lapF (lapF (X u))) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (X u) (fastNL r g y u) (lapF (lapF (X u))) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (X u) (X u) (lapF (lapF (fastNL r g y u))) x.1 x.2) := by
      rw [← tsum_neg, ← tsum_neg, ← sA1.tsum_add sA2.neg, ← (sA1.add sA2.neg).tsum_add sA3,
        ← ((sA1.add sA2.neg).add sA3).tsum_add sA4.neg,
        ← (((sA1.add sA2.neg).add sA3).add sA4.neg).tsum_add sA5,
        ← ((((sA1.add sA2.neg).add sA3).add sA4.neg).add sA5).tsum_add sA6]
      exact tsum_congr hpt
    rw [hsplit]
    simp only [Complex.add_re, Complex.neg_re]
    have r1 : (∑' x : Mode × Mode,
        tripT (nonresM (r * u)) (X u) (X u) (lapF (lapF (X u))) x.1 x.2).re =
        pair 2 (X u) (Qnr (r * u) (X u) (X u)) :=
      (pair_two_eq_re_tsum hreal (fun k => inner_Qm (nonresM_bdd (r * u)) hreal.lapF.lapF
        hF2 hF2 k) sA1).symm
    have r2 : (∑' x : Mode × Mode, tripT (m u) (lapF (X u)) (X u) (lapF (lapF (X u))) x.1 x.2).re =
        pair 2 (X u) (corr (-1) r (r * u) (lapF (X u)) (X u)) :=
      (pair_two_eq_re_tsum_gain (hgain u) hreal hlap2 hl2 (Or.inr hg2) sA2).symm
    have r3 : (∑' x : Mode × Mode,
        tripT (m u) (fastNL r g y u) (X u) (lapF (lapF (X u))) x.1 x.2).re =
        pair 2 (X u) (corr (-1) r (r * u) (fastNL r g y u) (X u)) :=
      (pair_two_eq_re_tsum_gain (hgain u) hreal hN2 hl2 (Or.inr hg2) sA3).symm
    have r4 : (∑' x : Mode × Mode, tripT (m u) (X u) (lapF (X u)) (lapF (lapF (X u))) x.1 x.2).re =
        pair 2 (X u) (corr (-1) r (r * u) (X u) (lapF (X u))) :=
      (pair_two_eq_re_tsum_gain (hgain u) hreal hl2 hlap2 (Or.inl hg2) sA4).symm
    have r5 : (∑' x : Mode × Mode,
        tripT (m u) (X u) (fastNL r g y u) (lapF (lapF (X u))) x.1 x.2).re =
        pair 2 (X u) (corr (-1) r (r * u) (X u) (fastNL r g y u)) :=
      (pair_two_eq_re_tsum_gain (hgain u) hreal hl2 hN2 (Or.inl hg2) sA5).symm
    have r6 : (∑' x : Mode × Mode,
        tripT (m u) (X u) (X u) (lapF (lapF (fastNL r g y u))) x.1 x.2).re =
        pair 2 (fastNL r g y u) (corr (-1) r (r * u) (X u) (X u)) :=
      (pair_two_eq_re_tsum hNr (fun k => inner_Qm (corrM_bdd (Or.inr rfl) r (r * u))
        hNr.lapF.lapF hF2 hF2 k) sA6).symm
    rw [r1, r2, r3, r4, r5, r6]
    unfold cubicRHS2 cubicHeat2 cubicD
    rw [Nat.cast_ofNat, PiF_fastNL]
    ring
  have hae' : ∀ᵐ u, u ∈ uIoc s t → (twoFam m m' X X' X X' X X' u).re = cubicRHS2 r g y u := by
    rw [uIoc_of_le hst]
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hre] with u hu hmemu
    exact hu (Ioc_subset_Icc_self hmemu)
  have hIc : IntervalIntegrable (cubicRHS2 r g y) volume s t := by
    refine hI.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hae'
  refine ⟨hIc, ?_⟩
  have e1 : cubicCorr2 r g y t = pair 2 (X t) (Qm (m t) (X t) (X t)) := by
    simp only [cubicCorr2, cubicE, hXdef, hmdef, Nat.cast_ofNat, corr]
  have e2 : cubicCorr2 r g y s = pair 2 (X s) (Qm (m s) (X s) (X s)) := by
    simp only [cubicCorr2, cubicE, hXdef, hmdef, Nat.cast_ofNat, corr]
  rw [e1, e2, key]
  exact intervalIntegral.integral_congr_ae hae'

/-- **`⟨z₂, X₁ z₂⟩` is absolutely continuous along the actual solution** with derivative
`metricRHS2` (TeX eq. quant-metric at `s = 2`, the `X_{1,2}` part of "the literal polynomial
differentiation").  Route: `path_identity_two` with the paths `S, F, F`, the multiplier
`metM(r, ru)` and the heat combination `tripT_met_heat_combine` at the test `W = AF`: all three
heats
are in the denominator of `metM`. -/
theorem metricCorr2_identity (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (metricRHS2 r g y) volume s t ∧
      metricCorr2 r g y t - metricCorr2 r g y s = ∫ u in s..t, metricRHS2 r g y u := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hmem : ∀ u ∈ Icc s t, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hs.trans hu.1, lt_lifespan hu.2 ht⟩
  set X : ℝ → Field := fun u => PiS (actual r g y u) with hXdef
  set Y : ℝ → Field := fun u => PiF (actual r g y u) with hYdef
  set X' : ℝ → Field := slowRHS r g y with hX'def
  set Y' : ℝ → Field := fastRHS r g y with hY'def
  set m : ℝ → Mult := fun u => metM r (r * u) with hmdef
  set m' : ℝ → Mult := fun u => metDM' r (r * u) with hm'def
  have hgain : ∀ u a b c p q, ‖m u a b c p q‖ ≤ 1 / absSq (p + q) := fun u a b c p q =>
    norm_metM_le_absSq r (r * u) a b c p q
  have hm'B : ∀ u, (m' u).Bdd := fun u => metDM'_bdd r (r * u)
  have hadmX : ∀ u ∈ Icc s t, Adm 2 (X u) := fun u hu =>
    (actual_adm h (hmem u hu).1 (hmem u hu).2).PiS
  have hadmY : ∀ u ∈ Icc s t, Adm 2 (Y u) := fun u hu =>
    (actual_adm h (hmem u hu).1 (hmem u hu).2).PiF
  have hXd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => X v k) (X' u k) (Icc s t) u :=
    fun k u hu => (slow_mode h k (hmem u hu).1 (hmem u hu).2).mono fun v hv =>
      show v ∈ Ici 0 from hs.trans hv.1
  have hYd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => Y v k) (Y' u k) (Icc s t) u :=
    fun k u hu => (fast_mode h k (hmem u hu).1 (hmem u hu).2).mono fun v hv =>
      show v ∈ Ici 0 from hs.trans hv.1
  have hX'c : ∀ k, ContinuousOn (fun u => X' u k) (Icc s t) := fun k =>
    (continuousOn_slowRHS_mode h ht0 ht k).mono (Icc_subset_Icc_left hs)
  have hY'c : ∀ k, ContinuousOn (fun u => Y' u k) (Icc s t) := fun k =>
    (continuousOn_fastRHS_mode h ht0 ht k).mono (Icc_subset_Icc_left hs)
  have hmd : ∀ a b c p q, ∀ u ∈ Icc s t,
      HasDerivWithinAt (fun v => m v a b c p q) (m' u a b c p q) (Icc s t) u :=
    fun a b c p q u _ => (hasDerivAt_metM r a b c p q u).hasDerivWithinAt
  have hm'c : ∀ a b c p q, ContinuousOn (fun u => m' u a b c p q) (Icc s t) :=
    fun a b c p q => (continuous_metDM' r a b c p q).continuousOn
  obtain ⟨M, D, -, hMb, hDf, hDs⟩ := path_bounds h hr hs ht
  have hc3F := (fast_h2_law h hs hst ht).1
  have hc3S := slow_c3_integrable h hs hst ht
  have hae3 := ae_inH3_split h hs hst ht
  obtain ⟨hI, key⟩ := path_identity_two (m := m) (m' := m') (X := X) (X' := X') (Y := Y) (Y' := Y')
    (W := Y) (W' := Y') (M := M) (D := D) hst hgain hm'B hmd hm'c hXd hX'c hYd hY'c hYd hY'c
    (fun u hu => (hadmX u hu).mz) (fun u hu => (hadmY u hu).mz) (fun u hu => (hadmY u hu).mz)
    (fun u hu => (hadmY u hu).real) (fun u hu => (hMb u hu).2) (fun u hu => (hMb u hu).1)
    (fun u hu => (hMb u hu).1) hDs hDf hDf
    (hae3.mono fun u hu => ⟨hu.2, hu.1, hu.1⟩) ((hc3S.add hc3F).add hc3F)
  have hre : ∀ᵐ u ∂(volume.restrict (Icc s t)),
      4 * (twoFam m m' X X' Y Y' Y Y' u).re = metricRHS2 r g y u := by
    filter_upwards [hae3, ae_restrict_mem measurableSet_Icc] with u hu3 hu
    have hu0 := (hmem u hu).1
    have huT := (hmem u hu).2
    have hS2 : MZ 2 (X u) := (hadmX u hu).mz
    have hF2 : MZ 2 (Y u) := (hadmY u hu).mz
    have hF3 : MZ 3 (Y u) := ⟨hu3.1, hF2.mean⟩
    have hS3 : MZ 3 (X u) := ⟨hu3.2, hS2.mean⟩
    obtain ⟨hNr, hN2, -⟩ := fastNL_l2 h hu0 huT
    obtain ⟨-, hSN2, -⟩ := slowNL_l2 h hu0 huT
    have hrealY : IsReal (Y u) := (hadmY u hu).real
    have xl2 : Summable fun k => ‖X u k‖ ^ 2 := (adm_summables (hadmX u hu)).2.1
    have xg2 : Summable fun k => (absk k * ‖X u k‖) ^ 2 := (adm_summables (hadmX u hu)).2.2.1
    have yl2 : Summable fun k => ‖Y u k‖ ^ 2 := (adm_summables (hadmY u hu)).2.1
    have yg2 : Summable fun k => (absk k * ‖Y u k‖) ^ 2 := (adm_summables (hadmY u hu)).2.2.1
    have hX'eq : X' u = -lapF (X u) + slowNL r g y u := slowRHS_eq_lap u
    have hY'eq : Y' u = -lapF (Y u) + fastNL r g y u := fastRHS_eq_lap u
    have hZ'eq : lapF (lapF (-lapF (Y u) + fastNL r g y u)) =
        -lapF (lapF (lapF (Y u))) + lapF (lapF (fastNL r g y u)) := by
      rw [lapF_add, lapF_add, lapF_neg, lapF_neg]
    have sA1 : Summable fun x : Mode × Mode =>
        tripT (metDM (r * u)) (X u) (Y u) (lapF (lapF (Y u))) x.1 x.2 :=
      (slotM_sum (metDM_bdd (r * u)) hS2 hF2 hF3).1.of_norm
    have sA2 : Summable fun x : Mode × Mode =>
        tripT (m u) (slowNL r g y u) (Y u) (lapF (lapF (Y u))) x.1 x.2 :=
      (slotX_sum (hgain u) hSN2 hF3 hF3).1.of_norm
    have sA3 : Summable fun x : Mode × Mode =>
        tripT (m u) (X u) (fastNL r g y u) (lapF (lapF (Y u))) x.1 x.2 :=
      (slotY_sum (hgain u) hS3 hN2 hF3).1.of_norm
    have sA4 : Summable fun x : Mode × Mode =>
        tripT (m u) (X u) (Y u) (lapF (lapF (fastNL r g y u))) x.1 x.2 :=
      (slotW_sum (hgain u) hS3 hF3 hN2).1.of_norm
    have hpt : ∀ x : Mode × Mode, tripDPath m m' X X' Y Y' (fun v => lapF (lapF (Y v)))
        (fun v => lapF (lapF (Y' v))) u x =
        tripT (metDM (r * u)) (X u) (Y u) (lapF (lapF (Y u))) x.1 x.2 +
        tripT (m u) (slowNL r g y u) (Y u) (lapF (lapF (Y u))) x.1 x.2 +
        tripT (m u) (X u) (fastNL r g y u) (lapF (lapF (Y u))) x.1 x.2 +
        tripT (m u) (X u) (Y u) (lapF (lapF (fastNL r g y u))) x.1 x.2 := by
      intro x
      simp only [tripDPath, tripD]
      rw [hX'eq, hY'eq, hZ'eq, tripT_add_left, tripT_add_mid, tripT_add_right]
      have hc := tripT_met_heat_combine r (r * u) (X u) (Y u) (lapF (Y u)) x.1 x.2
      simp only [hmdef, hm'def] at hc ⊢
      linear_combination hc
    have hsplit : twoFam m m' X X' Y Y' Y Y' u =
        (∑' x : Mode × Mode, tripT (metDM (r * u)) (X u) (Y u) (lapF (lapF (Y u))) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (slowNL r g y u) (Y u) (lapF (lapF (Y u))) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (X u) (fastNL r g y u) (lapF (lapF (Y u))) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (X u) (Y u) (lapF (lapF (fastNL r g y u))) x.1 x.2) := by
      rw [← sA1.tsum_add sA2, ← (sA1.add sA2).tsum_add sA3, ← ((sA1.add sA2).add sA3).tsum_add sA4]
      exact tsum_congr hpt
    rw [hsplit]
    simp only [Complex.add_re]
    have r1 : (∑' x : Mode × Mode,
        tripT (metDM (r * u)) (X u) (Y u) (lapF (lapF (Y u))) x.1 x.2).re =
        pair 2 (Y u) (Qm (metDM (r * u)) (X u) (Y u)) :=
      (pair_two_eq_re_tsum hrealY (fun k => inner_Qm (metDM_bdd (r * u)) hrealY.lapF.lapF
        hS2 hF2 k) sA1).symm
    have r2 : (∑' x : Mode × Mode,
        tripT (m u) (slowNL r g y u) (Y u) (lapF (lapF (Y u))) x.1 x.2).re =
        pair 2 (Y u) (X1op r (r * u) (slowNL r g y u) (Y u)) :=
      (pair_two_eq_re_tsum_gain (hgain u) hrealY hSN2 yl2 (Or.inr yg2) sA2).symm
    have r3 : (∑' x : Mode × Mode,
        tripT (m u) (X u) (fastNL r g y u) (lapF (lapF (Y u))) x.1 x.2).re =
        pair 2 (Y u) (X1op r (r * u) (X u) (fastNL r g y u)) :=
      (pair_two_eq_re_tsum_gain (hgain u) hrealY xl2 hN2 (Or.inl xg2) sA3).symm
    have r4 : (∑' x : Mode × Mode,
        tripT (m u) (X u) (Y u) (lapF (lapF (fastNL r g y u))) x.1 x.2).re =
        pair 2 (fastNL r g y u) (X1op r (r * u) (X u) (Y u)) :=
      (pair_two_eq_re_tsum hNr (fun k => inner_Qm (metM_bdd r (r * u)) hNr.lapF.lapF
        hS2 hF2 k) sA4).symm
    rw [r1, r2, r3, r4]
    rfl
  have hae' : ∀ᵐ u, u ∈ uIoc s t →
      4 * (twoFam m m' X X' Y Y' Y Y' u).re = metricRHS2 r g y u := by
    rw [uIoc_of_le hst]
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hre] with u hu hmemu
    exact hu (Ioc_subset_Icc_self hmemu)
  have hIc : IntervalIntegrable (metricRHS2 r g y) volume s t := by
    refine (hI.const_mul 4).congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hae'
  refine ⟨hIc, ?_⟩
  have e1 : metricCorr2 r g y t = 4 * pair 2 (Y t) (Qm (m t) (X t) (Y t)) := rfl
  have e2 : metricCorr2 r g y s = 4 * pair 2 (Y s) (Qm (m s) (X s) (Y s)) := rfl
  rw [e1, e2, ← mul_sub, key, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr_ae hae'

/-! ### G. Catalytic neutrality at weight two and the energy identity -/

/-- **Catalytic neutrality at weight two** (TeX: "the exact zero-phase energy vertex vanishes
before division"; `Trilinear.lean`, `cat_term`, which holds at every weight): for slow `S ∈ H²` and
fast `F ∈ H³`, `⟨A²F, Q_res(S,F)⟩ = 0`.  The library's `cat_neutral` restricts to `σ ∈ {0, 1}` only
through the summability `summable_tripT`; the survey's "not neutral" (`t12_energy_derivation.md`
§2.3) is that restriction, not a failure: on the resonant set `|q| = |k|`. -/
theorem cat_neutral_two {S F : Field} (hS : Adm 2 S) (hF : Adm 3 F) (hS' : PiS S = S)
    (hF' : PiF F = F) : pair 2 F (Qres S F) = 0 := by
  have hF2 : Adm 2 F := ⟨hF.inH.mono (by norm_num), hF.real, hF.sol, hF.mean⟩
  have hF3 : MZ 3 F := ⟨hF.inH, hF.mean⟩
  have hT : Summable fun x : Mode × Mode =>
      (sobWeight 2 (x.1 + x.2) : ℂ) * tripT resM S F F x.1 x.2 := by
    have h1 := (slotM_sum resM_bdd hS.mz hF2.mz hF3).1
    refine h1.of_norm.congr fun x => ?_
    rw [tripT_lapF_right, tripT_lapF_right, sobWeight_two]
    push_cast
    ring
  rw [Qres, pair_eq_tsum (tripT resM S F F) (inner_Qm resM_bdd hF.real hS.mz hF2.mz) hT]
  have h0 : ∑' x : Mode × Mode, (sobWeight 2 (x.1 + x.2) : ℂ) * tripT resM S F F x.1 x.2 = 0 := by
    refine tsum_anti fun p q => ?_
    simp only
    set r := -(p + q) with hr
    have hrq : -(p + r) = q := by rw [hr]; abel
    have e : tripT resM S F F p r = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, resM a c b p r *
        tau p r (hel a p (S p)) (hel c r (F r)) (hel b q (F q)) := by
      simp only [tripT, hrq]
      exact sum3_swap fun a b c => resM a b c p r *
        tau p r (hel a p (S p)) (hel b r (F r)) (hel c q (F q))
    rw [eq_neg_iff_add_eq_zero, e, tripT, ← hr]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => ?_
    exact cat_term hS' hF' 2 a b c p q
  rw [h0]
  simp

/-- The slow–fast frozen term is the full slow–fast convection at weight two. -/
theorem pair_metDM_eq_two (τ : ℝ) {S F : Field} (hS : Adm 2 S) (hF : Adm 3 F) (hS' : PiS S = S)
    (hF' : PiF F = F) : pair 2 F (Qm (metDM τ) S F) = pair 2 F (Qphase τ S F) := by
  have hF2 : Adm 2 F := ⟨hF.inH.mono (by norm_num), hF.real, hF.sol, hF.mean⟩
  rw [Qm_metDM_eq_Qnr τ hS' hF', Qphase_eq_Qres_add_Qnr τ hS.mz hF2.mz]
  have hF1 : InH (2 + 1) F := by
    rw [show (2 : ℝ) + 1 = 3 by norm_num]
    exact hF.inH
  have hQr : InH (2 - 1) (Qres S F) := by
    rw [show (2 : ℝ) - 1 = 1 by norm_num]
    exact (Qm_one_le resM_bdd hS.mz hF2.mz).1
  have hQn : InH (2 - 1) (Qnr τ S F) := by
    rw [show (2 : ℝ) - 1 = 1 by norm_num]
    exact (Qm_one_le (nonresM_bdd τ) hS.mz hF2.mz).1
  rw [pair_add hF1 hQr hQn, cat_neutral_two hS hF hS' hF', zero_add]

/-- The split of the convection tested on the fast part at weight two. -/
theorem pair_two_Qphase_split (τ : ℝ) {x : Field} (hx : Adm 2 x) (hF3 : InH 3 (PiF x)) :
    pair 2 (PiF x) (Qphase τ x x) =
      2 * pair 2 (PiF x) (Qphase τ (PiS x) (PiF x)) +
        pair 2 (PiF x) (Qphase τ (PiF x) (PiF x)) := by
  set S := PiS x with hSdef
  set F := PiF x with hFdef
  have hS : Adm 2 S := hx.PiS
  have hF : Adm 2 F := hx.PiF
  have hS' : PiS S = S := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hSdef, PiS, hk]
  have hF' : PiF F = F := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hFdef, PiF, hk]
  have hM := majorized_Qphase τ
  have hx' : x = S + F := (PiS_add_PiF x).symm
  have hsum : MZ 2 (S + F) := by rw [← hx']; exact hx.mz
  have hcomm : Qphase τ F S = Qphase τ S F := Qm_comm_of_symm (phaseM_symm τ) hF.mz hS.mz
  have hsplit : Qphase τ x x = Qphase τ S S + Qphase τ S F + Qphase τ S F + Qphase τ F F := by
    conv_lhs => rw [hx']
    rw [hM.add_left 0 _ _ _ hS.mz hF.mz hsum, hM.add_right 0 _ _ _ hS.mz hS.mz hF.mz,
      hM.add_right 0 _ _ _ hF.mz hS.mz hF.mz, hcomm]
    abel
  have hQ : ∀ {u v : Field}, Adm 2 u → Adm 2 v → InH (2 - 1) (Qphase τ u v) := fun hu hv => by
    rw [show (2 : ℝ) - 1 = 1 by norm_num]
    exact (Qm_one_le (phaseM_bdd τ) hu.mz hv.mz).1
  have hF1 : InH (2 + 1) F := by
    rw [show (2 : ℝ) + 1 = 3 by norm_num]
    exact hF3
  rw [hsplit, pair_add hF1 ((hQ hS hS).add (hQ hS hF) |>.add (hQ hS hF)) (hQ hF hF),
    pair_add hF1 ((hQ hS hS).add (hQ hS hF)) (hQ hS hF), pair_add hF1 (hQ hS hS) (hQ hS hF),
    pair_eq_zero_of_disjoint 2 (fun k => by
      by_cases hk : k 2 = 0
      · exact Or.inl (fast_zero hF' hk)
      · exact Or.inr (Qphase_slow_slow τ hS' hk))]
  ring

/-- **The right-hand side of the energy identity** (the integrand of `½W' + c_F²`): the resonant
slot `−⟨A²F, Q_res(F,F)⟩` (paid by `ResH2`), the force `−⟨A²F, H_ψ⟩`, the three uncancelled `X₁`
insertions, minus the cubic heat, plus the native differential `DE⁰₂[fastNL]`. -/
def h2RHS (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -pair 2 (PiF (actual r g y u)) (Qres (PiF (actual r g y u)) (PiF (actual r g y u))) -
    pair 2 (PiF (actual r g y u)) (Hpsi r g y u) +
    2 * (pair 2 (PiF (actual r g y u)) (X1op r (r * u) (slowNL r g y u) (PiF (actual r g y u))) +
      pair 2 (PiF (actual r g y u)) (X1op r (r * u) (PiS (actual r g y u)) (fastNL r g y u)) +
      pair 2 (fastNL r g y u) (X1op r (r * u) (PiS (actual r g y u)) (PiF (actual r g y u)))) -
    cubicHeat2 r (r * u) (PiF (actual r g y u)) +
    cubicD 2 (-1) r (r * u) (PiF (actual r g y u)) (fastNL r g y u)

/-- The pointwise bookkeeping of the integrand at a time when `F ∈ H³`. -/
theorem h2RHS_eq (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty)
    (hF3 : InH 3 (PiF (actual r g y u))) :
    pair 2 (PiF (actual r g y u)) (fastNL r g y u) + 1 / 2 * metricRHS2 r g y u +
      cubicRHS2 r g y u = h2RHS r g y u := by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  set F := PiF (actual r g y u) with hFdef
  set S := PiS (actual r g y u) with hSdef
  have hF : Adm 2 F := hx.PiF
  have hS : Adm 2 S := hx.PiS
  have hFa3 : Adm 3 F := ⟨hF3, hF.real, hF.sol, hF.mean⟩
  have hF' : PiF F = F := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hFdef, PiF, hk]
  have hS' : PiS S = S := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hSdef, PiS, hk]
  have hF1 : InH (2 + 1) F := by
    rw [show (2 : ℝ) + 1 = 3 by norm_num]
    exact hF3
  have hQ : ∀ {v w : Field}, Adm 2 v → Adm 2 w → InH (2 - 1) (Qphase (r * u) v w) :=
    fun hv hw => by
      rw [show (2 : ℝ) - 1 = 1 by norm_num]
      exact (Qm_one_le (phaseM_bdd _) hv.mz hw.mz).1
  have hH : InH (2 - 1) (Hpsi r g y u) := (hQ hy hy).sub (hQ hx hx)
  have e1 : pair 2 F (fastNL r g y u) = -(pair 2 F (Qphase (r * u) (actual r g y u)
      (actual r g y u)) + pair 2 F (Hpsi r g y u)) := by
    have e : Qphase (r * u) (y u) (y u) =
        Qphase (r * u) (actual r g y u) (actual r g y u) + Hpsi r g y u := by
      simp [Hpsi]
    unfold fastNL
    rw [pair_neg_right, pair_PiF_right 2 hF', e, pair_add hF1 (hQ hx hx) hH]
  have e2 := pair_two_Qphase_split (r * u) hx hF3
  have e3 := pair_metDM_eq_two (r * u) hS hFa3 hS' hF'
  have hQr : InH (2 - 1) (Qres F F) := by
    rw [show (2 : ℝ) - 1 = 1 by norm_num]
    exact (Qm_one_le resM_bdd hF.mz hF.mz).1
  have hQn : InH (2 - 1) (Qnr (r * u) F F) := by
    rw [show (2 : ℝ) - 1 = 1 by norm_num]
    exact (Qm_one_le (nonresM_bdd _) hF.mz hF.mz).1
  have e4 : pair 2 F (Qphase (r * u) F F) = pair 2 F (Qres F F) + pair 2 F (Qnr (r * u) F F) := by
    rw [Qphase_eq_Qres_add_Qnr _ hF.mz hF.mz, pair_add hF1 hQr hQn]
  unfold metricRHS2 cubicRHS2 h2RHS
  rw [← hFdef, ← hSdef] at *
  rw [e1, e3] at *
  linarith [e2, e4]

/-- **E8, the energy identity** (the `H²` analogue of `h1Energy_identity`): along the actual
solution, on `[s,t]` inside the lifespan, `½W(t) − ½W(s) + ∫ₛᵗ c_F² = ∫ₛᵗ h2RHS`, with `h2RHS`
integrable.  The slow–fast term of the `H²` law is cancelled by the frozen derivative of `X₁`
(exactly, by `cat_neutral_two`) and the nonresonant fast–fast term by the frozen derivative of
`E⁰₂`.  The integrand identity holds at almost every time (`F(u) ∈ H³`). -/
theorem h2Energy_identity (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (h2RHS r g y) volume s t ∧
      1 / 2 * h2Energy r g y t - 1 / 2 * h2Energy r g y s +
        (∫ u in s..t, fastNorm 3 r g y u ^ 2) = ∫ u in s..t, h2RHS r g y u := by
  obtain ⟨-, hI1, hE1⟩ := fast_h2_law h hs hst ht
  obtain ⟨hI2, hE2⟩ := metricCorr2_identity h hr hs hst ht
  obtain ⟨hI3, hE3⟩ := cubicCorr2_identity h hr hs hst ht
  have hae : ∀ᵐ u, u ∈ uIoc s t →
      (pair 2 (PiF (actual r g y u)) (fastNL r g y u) + 1 / 2 * metricRHS2 r g y u) +
        cubicRHS2 r g y u = h2RHS r g y u := by
    rw [uIoc_of_le hst]
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 (ae_inH3_split h hs hst ht)]
      with u hu hmemu
    have hm := Ioc_subset_Icc_self hmemu
    exact h2RHS_eq h (hs.trans hm.1) (lt_lifespan hm.2 ht) (hu hm).1
  have hS12 := hI1.add (hI2.const_mul (1 / 2))
  have hI : IntervalIntegrable (h2RHS r g y) volume s t := by
    refine (hS12.add hI3).congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hae
  refine ⟨hI, ?_⟩
  have e : ∫ u in s..t, h2RHS r g y u =
      (∫ u in s..t, pair 2 (PiF (actual r g y u)) (fastNL r g y u)) +
        1 / 2 * (∫ u in s..t, metricRHS2 r g y u) + ∫ u in s..t, cubicRHS2 r g y u := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hI1
      (hI2.const_mul _), ← intervalIntegral.integral_add hS12 hI3]
    exact (intervalIntegral.integral_congr_ae hae).symm
  rw [e]
  unfold h2Energy
  linarith


end OVNS.Quant.H2

end
