import OddViscousNS.Quant.Joint.Slow.Laws
import OddViscousNS.Quant.Joint.Slow.Sup

/-!
# E7-P: the chain, on a time interval

From the laws of `Laws.lean` to the bounds of the slow field, with all the quantities free:
* `l2_stage`: contraction of `‖y_S‖₀²`, `a_h²`, and the dissipation integrals;
* `law_integrated`, `law_window`: the two consequences of a passive law;
* `strain_generic`, `strain_zero`: the strain on `[a + 1, t]`, or on `[0, t]` from the true zero;
* `nn2_errP_le'`: the commutator of the truncation for `v`, with no `H³` norm, so that the box in
  the sup bound is explicit.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.Slow

open GN

/-! ### Scalar consequences of the laws -/

/-- The three consequences of an `L²`-type law `x' + d ≤ f`, `x ≤ d`. -/
theorem l2_stage {x d f : ℝ → ℝ} {a b E : ℝ} (hab : a ≤ b) (hf0 : ∀ u, 0 ≤ f u)
    (hd0 : ∀ u, 0 ≤ d u) (hxd : ∀ u ∈ Icc a b, x u ≤ d u) (hx : ContinuousOn x (Icc a b))
    (hd : IntervalIntegrable d volume a b) (hf : IntervalIntegrable f volume a b)
    (hE : (∫ u in a..b, f u) ≤ E)
    (hlaw : ∀ u₁ u₂, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ b →
      x u₂ + (∫ u in u₁..u₂, d u) ≤ x u₁ + ∫ u in u₁..u₂, f u) :
    (∀ u ∈ Icc a b, x u ≤ x a + E) ∧
    (∀ u₁ u₂, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ b → (∫ u in u₁..u₂, d u) ≤ x u₁ + E - x u₂) ∧
    ∀ u ∈ Icc (a + 1) b, 2 * x u ≤ x (u - 1) + 2 * E := by
  have hfsub : ∀ {u₁ u₂ : ℝ}, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ b → (∫ u in u₁..u₂, f u) ≤ E :=
    fun h1 h2 h3 => (intervalIntegral.integral_mono_interval h1 h2 h3
      (Eventually.of_forall hf0) hf).trans hE
  have hdint0 : ∀ {u₁ u₂ : ℝ}, u₁ ≤ u₂ → 0 ≤ ∫ u in u₁..u₂, d u :=
    fun h => intervalIntegral.integral_nonneg h fun u _ => hd0 u
  refine ⟨fun u hu => ?_, fun u₁ u₂ h1 h2 h3 => ?_, fun u hu => ?_⟩
  · have h1 := hlaw a u le_rfl hu.1 hu.2
    have h2 := hfsub le_rfl hu.1 hu.2
    have h3 := hdint0 hu.1
    linarith
  · have h4 := hlaw u₁ u₂ h1 h2 h3
    have h5 := hfsub h1 h2 h3
    linarith
  · have hu1 : a ≤ u - 1 := by linarith [hu.1]
    have hle : u - 1 ≤ u := by linarith
    have hub : u ≤ b := hu.2
    have hsub : Icc (u - 1) u ⊆ Icc a b := Icc_subset_Icc hu1 hub
    obtain ⟨τ, hτ, hgood⟩ := OVNS.exists_le_average (by linarith : u - 1 < u) (hx.mono hsub)
    have e : u - (u - 1) = 1 := by ring
    rw [e, mul_one] at hgood
    have hxi : ∫ w in (u - 1)..u, x w ≤ ∫ w in (u - 1)..u, d w :=
      intervalIntegral.integral_mono_on hle ((hx.mono hsub).intervalIntegrable_of_Icc hle)
        (hd.mono_set (by
          rw [uIcc_of_le hab, uIcc_of_le hle]
          exact hsub)) fun w hw => hxd w (hsub hw)
    have h1 := hlaw (u - 1) u hu1 hle hub
    have h2 := hfsub hu1 hle hub
    have h3 := hlaw τ u (hu1.trans hτ.1) hτ.2 hub
    have h4 := hfsub (hu1.trans hτ.1) hτ.2 hub
    have h5 := hdint0 hτ.2
    linarith

/-- The integrated consequence of a passive law `x' + d ≤ κ x + 2f`. -/
theorem law_integrated {x d f : ℝ → ℝ} {a b κ I E : ℝ} (hκ : 0 ≤ κ) (hf0 : ∀ u, 0 ≤ f u)
    (hx : ContinuousOn x (Icc a b)) (hf : IntervalIntegrable f volume a b)
    (hI : ∀ u₁ u₂, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ b → (∫ u in u₁..u₂, x u) ≤ I)
    (hE : (∫ u in a..b, f u) ≤ E)
    (hlaw : ∀ u₁ u₂, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ b →
      x u₂ + (∫ u in u₁..u₂, d u) ≤ x u₁ + ∫ u in u₁..u₂, (κ * x u + 2 * f u)) :
    ∀ u₁ u₂, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ b →
      x u₂ + (∫ u in u₁..u₂, d u) ≤ x u₁ + κ * I + 2 * E := by
  intro u₁ u₂ h1 h2 h3
  have hsub : Icc u₁ u₂ ⊆ Icc a b := Icc_subset_Icc h1 h3
  have hab : a ≤ b := h1.trans (h2.trans h3)
  have hxi : IntervalIntegrable x volume u₁ u₂ := (hx.mono hsub).intervalIntegrable_of_Icc h2
  have hfi : IntervalIntegrable f volume u₁ u₂ := hf.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le h2]
    exact hsub)
  have e : ∫ u in u₁..u₂, (κ * x u + 2 * f u) =
      κ * (∫ u in u₁..u₂, x u) + 2 * ∫ u in u₁..u₂, f u := by
    rw [intervalIntegral.integral_add (hxi.const_mul κ) (hfi.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h4 := hlaw u₁ u₂ h1 h2 h3
  rw [e] at h4
  have h5 := hI u₁ u₂ h1 h2 h3
  have h6 : (∫ u in u₁..u₂, f u) ≤ E := (intervalIntegral.integral_mono_interval h1 h2 h3
    (Eventually.of_forall hf0) hf).trans hE
  have h7 := mul_le_mul_of_nonneg_left h5 hκ
  linarith

/-- The window consequence: `x(u) ≤ I/δ + κ I + 2E` past `a + δ`. -/
theorem law_window {x d : ℝ → ℝ} {a b κ I E δ : ℝ} (hδ : 0 < δ) (hd0 : ∀ u, 0 ≤ d u)
    (hx : ContinuousOn x (Icc a b))
    (hI : ∀ u₁ u₂, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ b → (∫ u in u₁..u₂, x u) ≤ I)
    (hlaw : ∀ u₁ u₂, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ b →
      x u₂ + (∫ u in u₁..u₂, d u) ≤ x u₁ + κ * I + 2 * E) :
    ∀ u, a + δ ≤ u → u ≤ b → x u ≤ I / δ + κ * I + 2 * E := by
  intro u hu hub
  have h1 : a ≤ u - δ := by linarith
  have h2 : u - δ ≤ u := by linarith
  obtain ⟨τ, hτ, hgood⟩ := OVNS.exists_le_average (by linarith : u - δ < u)
    (hx.mono (Icc_subset_Icc h1 hub))
  have e : u - (u - δ) = δ := by ring
  rw [e] at hgood
  have h3 : x τ ≤ I / δ := by
    rw [le_div_iff₀ hδ]
    exact hgood.trans (hI _ _ h1 h2 hub)
  have h4 := hlaw τ u (h1.trans hτ.1) hτ.2 hub
  have h5 : 0 ≤ ∫ w in τ..u, d w := intervalIntegral.integral_nonneg hτ.2 fun w _ => hd0 w
  linarith

/-! ### Weighted summability of the scalars -/

lemma sobWeight_natCast (n : ℕ) {k : Mode} (hk : k ≠ 0) :
    sobWeight (n : ℝ) k = absSq k ^ n := by
  have e : (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
  simp only [sobWeight, hk, ↓reduceIte]
  rw [e, Real.rpow_natCast, pow_mul, absk_sq]

lemma norm_wC_sq_le (u : Field) (k : Mode) : ‖wC u k‖ ^ 2 ≤ 4 * (absSq k * ‖u k‖ ^ 2) := by
  have h : ‖wC u k‖ ≤ 2 * (absk k * ‖u k‖) := by
    rw [wC, curlL_apply, norm_mul, Complex.norm_I, one_mul]
    exact norm_cross_le k (u k)
  calc ‖wC u k‖ ^ 2 ≤ (2 * (absk k * ‖u k‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 4 * (absSq k * ‖u k‖ ^ 2) := by rw [mul_pow, mul_pow, absk_sq]; norm_num

lemma summable_weight_of_le {u : Field} {j : ℕ} {σ : ℝ} (hu : InH σ u) (h0 : u 0 = 0)
    (hσ : σ = (j : ℝ)) (a : Mode → ℂ) (ha0 : a 0 = 0) {C : ℝ} {i : ℕ}
    (hle : ∀ k, absSq k ^ i * ‖a k‖ ^ 2 ≤ C * (absSq k ^ j * ‖u k‖ ^ 2)) :
    Summable fun k => absSq k ^ i * ‖a k‖ ^ 2 := by
  subst hσ
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (absSq_nonneg k) _) (by positivity))
    (fun k => ?_) (hu.mul_left C)
  by_cases hk : k = 0
  · subst hk
    have : ‖u 0‖ = 0 := by simp [h0]
    simp [ha0, sobWeight]
  · rw [sobWeight_natCast j hk]
    exact hle k

lemma summable_wC {u : Field} {j : ℕ} {σ : ℝ} (hu : InH σ u) (h0 : u 0 = 0)
    (hσ : σ = ((j + 1 : ℕ) : ℝ)) : Summable fun k => absSq k ^ j * ‖wC u k‖ ^ 2 :=
  summable_weight_of_le (C := 4) hu h0 hσ _ (wC_zero u) fun k => by
    have h1 := mul_le_mul_of_nonneg_left (norm_wC_sq_le u k) (pow_nonneg (absSq_nonneg k) j)
    refine h1.trans (le_of_eq ?_)
    ring

lemma summable_cmp {u : Field} {j : ℕ} {σ : ℝ} (hu : InH σ u) (h0 : u 0 = 0)
    (hσ : σ = (j : ℝ)) (i : Fin 3) : Summable fun k => absSq k ^ j * ‖GN.cmp u i k‖ ^ 2 :=
  summable_weight_of_le (C := 1) hu h0 hσ _ (by change (u 0) i = 0; rw [h0]; rfl) fun k => by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_cmp_le u i k) 2)
        (pow_nonneg (absSq_nonneg k) j)

lemma sn_zero_wC_le {f : Field} (hf : InH 1 f) :
    (Summable fun k => ‖wC f k‖ ^ 2) ∧ sn 0 (wC f) ≤ 4 * hnorm 1 f ^ 2 := by
  have hle : ∀ k, ‖wC f k‖ ^ 2 ≤ 4 * (sobWeight 1 k * ‖f k‖ ^ 2) := fun k => by
    rw [sobWeight_one]
    exact norm_wC_sq_le f k
  have hs : Summable fun k => 4 * (sobWeight 1 k * ‖f k‖ ^ 2) := hf.mul_left 4
  have hS := Summable.of_nonneg_of_le (fun _ => by positivity) hle hs
  refine ⟨hS, ?_⟩
  rw [sn_zero, hnorm_sq hf, ← tsum_mul_left]
  exact hS.tsum_le_tsum hle hs

lemma sn_zero_cmp_le {f : Field} (hf : InH 1 f) (h0 : f 0 = 0) (i : Fin 3) :
    (Summable fun k => ‖GN.cmp f i k‖ ^ 2) ∧ sn 0 (GN.cmp f i) ≤ hnorm 1 f ^ 2 := by
  have hle : ∀ k, ‖GN.cmp f i k‖ ^ 2 ≤ sobWeight 1 k * ‖f k‖ ^ 2 := fun k => by
    by_cases hk : k = 0
    · subst hk
      have : GN.cmp f i 0 = 0 := by change (f 0) i = 0; rw [h0]; rfl
      simp [this, h0]
    · have h1 := one_le_absSq hk
      have h2 : ‖GN.cmp f i k‖ ^ 2 ≤ ‖f k‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_cmp_le f i k) 2
      rw [sobWeight_one]
      nlinarith [sq_nonneg ‖f k‖]
  have hS := Summable.of_nonneg_of_le (fun _ => by positivity) hle hf
  refine ⟨hS, ?_⟩
  rw [sn_zero, hnorm_sq hf]
  exact hS.tsum_le_tsum hle hf

/-! ### The strain along the solution -/

section Actual

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- The source hypotheses for the vorticity, at almost every time. -/
lemma srcAe_curl (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbT : ENNReal.ofReal b < Ty) :
    SrcAe a b (corrSlow r g y) (fun t => wC (corrSlow r g y t)) (fun t => wC (corrRes r g y t))
      (fun t => 4 * hnorm 1 (corrRes r g y t) ^ 2)
      (fun t => 2 * (hnorm 2 (corrSlow r g y t) ^ 2 * hnorm 3 (corrSlow r g y t) ^ 2)) := by
  filter_upwards [ae_inH3_corr h hr ha hab hbT, ae_inH1_corrRes h hr ha hab hbT,
    ae_restrict_mem measurableSet_Icc] with u hz3 hf1 hu
  have hz := corrSlow_adm h hr (ha.trans hu.1) (lt_lifespan hu.2 hbT)
  have hz' := PiS_corrSlow r g y u
  obtain ⟨hf2, hf3⟩ := sn_zero_wC_le hf1
  refine ⟨⟨hz3, hz.mean⟩, hz.mz, fun k hk => slow_zero' hz' hk, fun k hk => ?_,
    summable_wC hz.inH hz.mean (by norm_num), summable_wC hz3 hz.mean (by norm_num), hf2, hf3, ?_⟩
  · rw [wC, slow_zero' hz' hk, map_zero]
  · have e1 : sn 1 (wC (corrSlow r g y u)) ≤ hnorm 2 (corrSlow r g y u) ^ 2 := by
      have := sn_wC hz hz' 1
      norm_num at this
      rw [this]
      exact pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_PiH_le' hz.inH) 2
    have e2 : sn 2 (wC (corrSlow r g y u)) ≤ hnorm 3 (corrSlow r g y u) ^ 2 := by
      have := sn_wC hz hz' 2
      norm_num at this
      rw [this]
      exact pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_PiH_le' hz3) 2
    have h3 := mul_le_mul_of_nonneg_left e1 (sq_nonneg (hnorm 3 (corrSlow r g y u)))
    have h4 := mul_le_mul_of_nonneg_left e2 (sq_nonneg (hnorm 2 (corrSlow r g y u)))
    linarith

lemma intervalIntegrable_E (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (fun t => 2 * (hnorm 2 (corrSlow r g y t) ^ 2 *
      hnorm 3 (corrSlow r g y t) ^ 2)) volume a b := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hp : HeatPair 2 a b (corrSlow r g y) (corrForce r g y) :=
    (heatPair_corrSlow h hr (Or.inr (Or.inr rfl)) hb0 hbT).mono ha le_rfl
  have hD : IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume a b := by
    have := hp.intervalIntegrable_dissipation hab
    have e : (2 : ℝ) + 1 = 3 := by norm_num
    rwa [e] at this
  have hc : ContinuousOn (fun u => hnorm 2 (corrSlow r g y u) ^ 2) (Set.uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (continuousOn_corr_sq h hr (Or.inr (Or.inr rfl)) hb0 hbT).mono (Icc_subset_Icc_left ha)
  exact (hD.continuousOn_mul hc).const_mul 2

/-- The Sobolev bound on box truncations. -/
lemma sobolev_box {a : Mode → ℂ} (haR : ∀ k, a (-k) = conj (a k))
    (ha2 : Summable fun k => ‖a k‖ ^ 2) (ha1 : Summable fun k => absSq k ^ 1 * ‖a k‖ ^ 2)
    (N : ℕ) {Y : ℝ} (hY : 0 < Y) (h0 : sn 0 a ≤ Y) (h1 : 2 * sn 1 a ≤ Y) (n : ℕ) :
    mP (2 ^ n) (polyOf (slowBox N) a) ≤ (piM 1 n * Y) ^ (2 ^ n) := by
  refine sobolev_poly (realC_polyOf_box haR N) (slow_polyOf_box a N) hY ?_ ?_ n
  · exact (nn2_polyOf_le ha2).trans (by rw [← sn_zero]; exact h0)
  · have hg : grad2 (polyOf (slowBox N) a) ≤ sn 1 a := by
      refine hasSum_le (fun k => ?_) (hasSum_grad2 _) ha1.hasSum
      rw [coeff_polyOf, pow_one]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (absSq_nonneg k)
      simp only [tr]
      split_ifs <;> simp
    linarith

/-- **The strain past the first unit**, from the `L²` level of the vorticity on `[a, t]`. -/
theorem strain_generic (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a t : ℝ} (ha : 0 ≤ a)
    (hat : a ≤ t) (ht : ENNReal.ofReal t < Ty) {T Y : ℝ} (hT : t - a ≤ T) (hT0 : 0 ≤ T)
    (hY : 0 < Y) (hL : ∀ u ∈ Icc a t, hnorm 1 (PiH (corrSlow r g y u)) ^ 2 ≤ Y)
    (hE : 16 * (∫ u in a..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ Y) (n : ℕ) :
    StrainOn r g y (a + 1) t (2 ^ n) (rK (2 ^ n) * Real.sqrt (piM T n * Y)) := by
  have hP := passive_curl h hr ha hat ht
  have hadm : ∀ u ∈ Icc a t, Adm 2 (corrSlow r g y u) := fun u hu =>
    corrSlow_adm h hr (ha.trans hu.1) (lt_lifespan hu.2 ht)
  have hI1 := intervalIntegrable_corrRes_sq h hr ha hat ht
  have hPi := one_le_piM hT0 n
  have hm := hP.moser_eventually hT hT0 hY (hI1.const_mul 4) (intervalIntegrable_E h hr ha hat ht)
    (srcAe_curl h hr ha hat ht) (by
      rw [intervalIntegral.integral_const_mul]
      linarith)
    (fun u hu => by
      have := summable_wC (j := 0) ((hadm u hu).inH.mono (by norm_num : (1 : ℝ) ≤ 2))
        (hadm u hu).mean (by norm_num)
      simpa using this)
    (fun u hu => by
      have e := sn_wC (hadm u hu) (PiS_corrSlow r g y u) 0
      norm_num at e
      rw [e]
      exact hL u hu) n
  intro u hu
  refine strainBd_of_poly (hadm u ⟨by linarith [hu.1], hu.2⟩) Nat.one_le_two_pow
    (by positivity) ?_
  filter_upwards [hm] with N hN
  refine hN u ⟨?_, hu.2⟩
  have : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
  linarith [hu.1]

/-- **The strain from the true zero.** -/
theorem strain_zero (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t < Ty) {T Y Y' : ℝ} (hT : t ≤ T) (hY : 0 < Y) (hY' : 0 < Y')
    (hE : 16 * (∫ u in (0 : ℝ)..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ Y)
    (h0 : hnorm 1 (PiH (corrSlow r g y 0)) ^ 2 ≤ Y')
    (h1 : 2 * hnorm 2 (PiH (corrSlow r g y 0)) ^ 2 ≤ Y') (n : ℕ) :
    StrainOn r g y 0 t (2 ^ n) (rK (2 ^ n) * Real.sqrt
      (Real.exp T * (2 * (piM 1 n * Y') + 201 * 2 ^ n * Y))) := by
  have hP := passive_curl h hr le_rfl ht0 ht
  have hz0 := corrSlow_adm h hr le_rfl ((ENNReal.ofReal_le_ofReal ht0).trans_lt ht)
  have hadm : ∀ u ∈ Icc 0 t, Adm 2 (corrSlow r g y u) := fun u hu =>
    corrSlow_adm h hr hu.1 (lt_lifespan hu.2 ht)
  have hI1 := intervalIntegrable_corrRes_sq h hr le_rfl ht0 ht
  have hPi := one_le_piM (zero_le_one) n
  have hY₀ : 0 < piM 1 n * Y' := by positivity
  have hst : ∀ᶠ N : ℕ in atTop, mP (2 ^ n) (polyOf (slowBox (2 * N)) (wC (corrSlow r g y 0))) ≤
      (piM 1 n * Y') ^ (2 ^ n) := by
    refine Eventually.of_forall fun N => sobolev_box (wC_neg hz0.real) ?_ ?_ _ hY' ?_ ?_ n
    · simpa using summable_wC (j := 0) (hz0.inH.mono (by norm_num : (1 : ℝ) ≤ 2)) hz0.mean
        (by norm_num)
    · exact summable_wC (j := 1) hz0.inH hz0.mean (by norm_num)
    · have e := sn_wC hz0 (PiS_corrSlow r g y 0) 0
      norm_num at e
      rw [e]
      exact h0
    · have e := sn_wC hz0 (PiS_corrSlow r g y 0) 1
      norm_num at e
      rw [e]
      exact h1
  have hm := hP.propagate_eventually (T := T) (by linarith) hY hY₀ (hI1.const_mul 4)
    (intervalIntegrable_E h hr le_rfl ht0 ht) (srcAe_curl h hr le_rfl ht0 ht) (by
      rw [intervalIntegral.integral_const_mul]
      linarith) hst
  intro u hu
  refine strainBd_of_poly (hadm u hu) Nat.one_le_two_pow (by positivity) ?_
  filter_upwards [hm] with N hN
  exact hN u hu

/-! ### The chain on a time interval -/

lemma mono_pow_mul {e R : ℝ} (he : 1 ≤ e) (hR : 1 ≤ R) {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    e ^ a * R ^ c ≤ e ^ b * R ^ d :=
  mul_le_mul (pow_le_pow_right₀ he hab) (pow_le_pow_right₀ hR hcd) (by positivity) (by positivity)

/-- The dissipation of `y_S` at level three, split into the sectors. -/
lemma integral_hnorm_three_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u₁ u₂ : ℝ} (hu₁ : 0 ≤ u₁)
    (h12 : u₁ ≤ u₂) (ht : ENNReal.ofReal u₂ < Ty) :
    (∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2) ≤
      (∫ u in u₁..u₂, hnorm 3 (PiH (corrSlow r g y u)) ^ 2) +
        ∫ u in u₁..u₂, hnorm 3 (PiV (corrSlow r g y u)) ^ 2 := by
  have hb0 : 0 ≤ u₂ := hu₁.trans h12
  have e3 : (2 : ℝ) + 1 = 3 := by norm_num
  have hS := (heatPair_corrSlow h hr (Or.inr (Or.inr rfl)) hb0 ht).mono hu₁ le_rfl
  have hH := (heatPair_corrH h hr (Or.inr (Or.inr rfl)) hb0 ht).mono hu₁ le_rfl
  have hV := (heatPair_corrV h hr (Or.inr (Or.inr rfl)) hb0 ht).mono hu₁ le_rfl
  have iS := hS.intervalIntegrable_dissipation h12
  have iH := hH.intervalIntegrable_dissipation h12
  have iV := hV.intervalIntegrable_dissipation h12
  rw [e3] at iS iH iV
  rw [← intervalIntegral.integral_add iH iV]
  refine intervalIntegral.integral_mono_ae_restrict h12 iS (iH.add iV) ?_
  filter_upwards [ae_inH3_corr h hr hu₁ h12 ht] with u hz3
  have e := hnorm_sq_split_slow hz3
  rw [PiS_corrSlow] at e
  exact e.le

/-- The conclusions of the chain, on abstract scalars. -/
structure ChainScalar (xv dv xh : ℝ → ℝ) (b₀ t e₀ R : ℝ) : Prop where
  av : ∀ u ∈ Icc b₀ t, xv u ≤ 75000 * e₀ ^ 4 * R ^ 3
  bh : ∀ u ∈ Icc b₀ t, xh u ≤ 75000 * e₀ ^ 4 * R ^ 4
  bv : ∀ u ∈ Icc b₀ t, dv u ≤ 39000000 * e₀ ^ 5 * R ^ 4
  Jv : ∫ u in b₀..t, dv u ≤ 75000 * e₀ ^ 4 * R ^ 3
  av1 : ∀ u ∈ Icc (b₀ + 1 / 2) t, xv u ≤ 35000 * e₀ * R ^ 3
  bh1 : ∀ u ∈ Icc (b₀ + 1 / 2) t, xh u ≤ 35000 * e₀ * R ^ 3
  bv1 : ∀ u ∈ Icc (b₀ + 1) t, dv u ≤ 18000000 * e₀ ^ 2 * R ^ 4

/-- The first barrier, from `b₀`. -/
private lemma chain_bv {xv dv : ℝ → ℝ} {b₀ t Λ R e₀ : ℝ} (hΛ1 : 1 ≤ Λ) (hR : 1 ≤ R) (he : 1 ≤ e₀)
    (hΛR : Λ ≤ e₀ * R)
    (hbar : ∀ {u₁ u₂ A : ℝ}, b₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → 0 < A →
      (∀ u ∈ Icc u₁ u₂, xv u ≤ A) → ∀ τ ∈ Icc u₁ u₂,
      dv u₂ ≤ max (dv τ) ((10 * Λ + 500) * A) + 96 * R ^ 2)
    (h0b : dv b₀ ≤ 18498601 * e₀ ^ 4 * R ^ 4)
    (hav : ∀ u ∈ Icc b₀ t, xv u ≤ 75000 * e₀ ^ 4 * R ^ 3) :
    ∀ u ∈ Icc b₀ t, dv u ≤ 39000000 * e₀ ^ 5 * R ^ 4 := fun u hu => by
  have hR0 : 0 < R := by linarith
  have he0 : 0 < e₀ := by linarith
  have h510 : 10 * Λ + 500 ≤ 510 * (e₀ * R) := by nlinarith
  have hA0 : 0 < 75000 * e₀ ^ 4 * R ^ 3 := by positivity
  have h1 := hbar (u₁ := b₀) (u₂ := u) le_rfl hu.1 hu.2 hA0
    (fun w hw => hav w ⟨hw.1, hw.2.trans hu.2⟩) b₀ ⟨le_rfl, hu.1⟩
  have h2 : (10 * Λ + 500) * (75000 * e₀ ^ 4 * R ^ 3) ≤ 38250000 * e₀ ^ 5 * R ^ 4 := by
    calc _ ≤ 510 * (e₀ * R) * (75000 * e₀ ^ 4 * R ^ 3) := mul_le_mul_of_nonneg_right h510 hA0.le
      _ = _ := by ring
  have h3 : 18498601 * e₀ ^ 4 * R ^ 4 ≤ 38250000 * e₀ ^ 5 * R ^ 4 := by
    have := mono_pow_mul he hR (a := 4) (b := 5) (c := 4) (d := 4) (by norm_num) le_rfl
    have h4 : (0 : ℝ) ≤ e₀ ^ 5 * R ^ 4 := by positivity
    nlinarith
  have h5 : max (dv b₀) ((10 * Λ + 500) * (75000 * e₀ ^ 4 * R ^ 3)) ≤
      38250000 * e₀ ^ 5 * R ^ 4 := max_le (h0b.trans h3) h2
  have h6 : R ^ 2 ≤ e₀ ^ 5 * R ^ 4 := by
    have := mono_pow_mul he hR (a := 0) (b := 5) (c := 2) (d := 4) (by norm_num) (by norm_num)
    simpa using this
  nlinarith

/-- The second barrier, from a good time of `[u − 1/2, u]`. -/
private lemma chain_bv1 {xv dv : ℝ → ℝ} {b₀ t Λ R e₀ K₁ K₂ : ℝ} (hΛ1 : 1 ≤ Λ) (hR : 1 ≤ R)
    (he : 1 ≤ e₀) (hΛR : Λ ≤ e₀ * R) (hxv0 : ∀ u, 0 ≤ xv u) (hcd : ContinuousOn dv (Icc b₀ t))
    (hbar : ∀ {u₁ u₂ A : ℝ}, b₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → 0 < A →
      (∀ u ∈ Icc u₁ u₂, xv u ≤ A) → ∀ τ ∈ Icc u₁ u₂,
      dv u₂ ≤ max (dv τ) ((10 * Λ + 500) * A) + 96 * R ^ 2)
    (hiv : ∀ u₁ u₂, b₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      xv u₂ + (∫ u in u₁..u₂, dv u) ≤ xv u₁ + K₁ + K₂) (hK : K₁ + K₂ ≤ 34524 * (e₀ * R ^ 3))
    (hav1 : ∀ u ∈ Icc (b₀ + 1 / 2) t, xv u ≤ 35000 * e₀ * R ^ 3) :
    ∀ u ∈ Icc (b₀ + 1) t, dv u ≤ 18000000 * e₀ ^ 2 * R ^ 4 := fun u hu => by
  have hR0 : 0 < R := by linarith
  have he0 : 0 < e₀ := by linarith
  have h510 : 10 * Λ + 500 ≤ 510 * (e₀ * R) := by nlinarith
  set w : ℝ := u - 1 / 2 with hw
  have hw1 : b₀ + 1 / 2 ≤ w := by simp only [hw]; linarith [hu.1]
  have hwu : w ≤ u := by simp only [hw]; linarith
  have hwb : b₀ ≤ w := by linarith
  have hsub : Icc w u ⊆ Icc b₀ t := Icc_subset_Icc hwb hu.2
  obtain ⟨τ, hτ, hgood⟩ := OVNS.exists_le_average (by simp only [hw]; linarith : w < u)
    (hcd.mono hsub)
  have e : u - w = 1 / 2 := by simp only [hw]; ring
  rw [e] at hgood
  have hI := hiv w u hwb hwu hu.2
  have hxw := hav1 w ⟨hw1, hwu.trans hu.2⟩
  have hdτ : dv τ ≤ 139048 * (e₀ * R ^ 3) := by
    have h0 := hxv0 u
    nlinarith
  have hA0 : 0 < 35000 * e₀ * R ^ 3 := by positivity
  have h1 := hbar hwb hwu hu.2 hA0 (fun v hv => hav1 v ⟨hw1.trans hv.1, hv.2.trans hu.2⟩) τ hτ
  have h2 : (10 * Λ + 500) * (35000 * e₀ * R ^ 3) ≤ 17850000 * e₀ ^ 2 * R ^ 4 := by
    calc _ ≤ 510 * (e₀ * R) * (35000 * e₀ * R ^ 3) := mul_le_mul_of_nonneg_right h510 hA0.le
      _ = _ := by ring
  have h3 : e₀ * R ^ 3 ≤ e₀ ^ 2 * R ^ 4 := by
    have := mono_pow_mul he hR (a := 1) (b := 2) (c := 3) (d := 4) (by norm_num) (by norm_num)
    simpa using this
  have h4 : (0 : ℝ) ≤ e₀ ^ 2 * R ^ 4 := by positivity
  have h5 : max (dv τ) ((10 * Λ + 500) * (35000 * e₀ * R ^ 3)) ≤ 17850000 * e₀ ^ 2 * R ^ 4 :=
    max_le (by nlinarith) h2
  have h6 : R ^ 2 ≤ e₀ ^ 2 * R ^ 4 := by
    have := mono_pow_mul he hR (a := 0) (b := 2) (c := 2) (d := 4) (by norm_num) (by norm_num)
    simpa using this
  nlinarith

/-- **The chain on scalars**: the laws, the windows, the barrier. -/
theorem chain_scalar {xv dv xh dh f : ℝ → ℝ} {b₀ t Λ R e₀ : ℝ} (hb₀t : b₀ ≤ t) (hΛ1 : 1 ≤ Λ)
    (hR : 1 ≤ R) (he : 1 ≤ e₀) (hΛR : Λ ≤ e₀ * R)
    (hxv0 : ∀ u, 0 ≤ xv u) (hdv0 : ∀ u, 0 ≤ dv u) (hdh0 : ∀ u, 0 ≤ dh u) (hf0 : ∀ u, 0 ≤ f u)
    (hcv : ContinuousOn xv (Icc b₀ t)) (hch : ContinuousOn xh (Icc b₀ t))
    (hcd : ContinuousOn dv (Icc b₀ t)) (hfi : IntervalIntegrable f volume b₀ t)
    (hE : (∫ u in b₀..t, f u) ≤ 24 * R ^ 2)
    (hIv : ∀ u₁ u₂, b₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → (∫ u in u₁..u₂, xv u) ≤ 169 * R ^ 2)
    (hIh : ∀ u₁ u₂, b₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → (∫ u in u₁..u₂, xh u) ≤ 169 * R ^ 2)
    (hlv : ∀ u₁ u₂, b₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      xv u₂ + (∫ u in u₁..u₂, dv u) ≤ xv u₁ + ∫ u in u₁..u₂, ((4 * Λ + 200) * xv u + 2 * f u))
    (hlh : ∀ u₁ u₂, b₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      xh u₂ + (∫ u in u₁..u₂, dh u) ≤ xh u₁ + ∫ u in u₁..u₂, ((4 * Λ + 200) * xh u + 2 * f u))
    (hbar : ∀ {u₁ u₂ A : ℝ}, b₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → 0 < A →
      (∀ u ∈ Icc u₁ u₂, xv u ≤ A) → ∀ τ ∈ Icc u₁ u₂,
      dv u₂ ≤ max (dv τ) ((10 * Λ + 500) * A) + 96 * R ^ 2)
    (h0v : xv b₀ ≤ 40401 * e₀ ^ 4 * R ^ 3) (h0h : xh b₀ ≤ 40401 * e₀ ^ 4 * R ^ 4)
    (h0b : dv b₀ ≤ 18498601 * e₀ ^ 4 * R ^ 4) :
    ChainScalar xv dv xh b₀ t e₀ R := by
  have hR0 : 0 < R := by linarith
  have he0 : 0 < e₀ := by linarith
  have hΛ0 : 0 < Λ := by linarith
  set κ : ℝ := 4 * Λ + 200 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκle : κ ≤ 204 * (e₀ * R) := by simp only [hκ]; nlinarith
  have hiv := law_integrated hκ0 hf0 hcv hfi hIv hE hlv
  have hih := law_integrated hκ0 hf0 hch hfi hIh hE hlh
  have hwv := law_window (δ := 1 / 2) (by norm_num) hdv0 hcv hIv hiv
  have hwh := law_window (δ := 1 / 2) (by norm_num) hdh0 hch hIh hih
  have hR23 : R ^ 2 ≤ e₀ * R ^ 3 := by
    have := mono_pow_mul he hR (a := 0) (b := 1) (c := 2) (d := 3) (by norm_num) (by norm_num)
    simpa using this
  have hκI : κ * (169 * R ^ 2) + 2 * (24 * R ^ 2) ≤ 34524 * (e₀ * R ^ 3) := by
    have h1 : κ * (169 * R ^ 2) ≤ 204 * (e₀ * R) * (169 * R ^ 2) :=
      mul_le_mul_of_nonneg_right hκle (by positivity)
    have e1 : 204 * (e₀ * R) * (169 * R ^ 2) = 34476 * (e₀ * R ^ 3) := by ring
    linarith
  have hR34 : e₀ * R ^ 3 ≤ e₀ ^ 4 * R ^ 3 := by
    have := mono_pow_mul he hR (a := 1) (b := 4) (c := 3) (d := 3) (by norm_num) le_rfl
    simpa using this
  have hR34' : e₀ * R ^ 3 ≤ e₀ ^ 4 * R ^ 4 := by
    have := mono_pow_mul he hR (a := 1) (b := 4) (c := 3) (d := 4) (by norm_num) (by norm_num)
    simpa using this
  have hint0 : ∀ {a b : ℝ} {w : ℝ → ℝ}, a ≤ b → (∀ u, 0 ≤ w u) → 0 ≤ ∫ u in a..b, w u :=
    fun hab hw => intervalIntegral.integral_nonneg hab fun u _ => hw u
  have hav : ∀ u ∈ Icc b₀ t, xv u ≤ 75000 * e₀ ^ 4 * R ^ 3 := fun u hu => by
    have h1 := hiv b₀ u le_rfl hu.1 hu.2
    have h2 : 0 ≤ ∫ w in b₀..u, dv w := hint0 hu.1 hdv0
    nlinarith
  have hbh : ∀ u ∈ Icc b₀ t, xh u ≤ 75000 * e₀ ^ 4 * R ^ 4 := fun u hu => by
    have h1 := hih b₀ u le_rfl hu.1 hu.2
    have h2 : 0 ≤ ∫ w in b₀..u, dh w := hint0 hu.1 hdh0
    nlinarith
  have hJv : ∫ u in b₀..t, dv u ≤ 75000 * e₀ ^ 4 * R ^ 3 := by
    have h1 := hiv b₀ t le_rfl hb₀t le_rfl
    have h2 := hxv0 t
    nlinarith
  have hav1 : ∀ u ∈ Icc (b₀ + 1 / 2) t, xv u ≤ 35000 * e₀ * R ^ 3 := fun u hu => by
    have h1 := hwv u hu.1 hu.2
    have e : 169 * R ^ 2 / (1 / 2) = 338 * R ^ 2 := by ring
    rw [e] at h1
    nlinarith
  have hbh1 : ∀ u ∈ Icc (b₀ + 1 / 2) t, xh u ≤ 35000 * e₀ * R ^ 3 := fun u hu => by
    have h1 := hwh u hu.1 hu.2
    have e : 169 * R ^ 2 / (1 / 2) = 338 * R ^ 2 := by ring
    rw [e] at h1
    nlinarith
  exact ⟨hav, hbh, chain_bv hΛ1 hR he hΛR hbar h0b hav, hJv, hav1, hbh1,
    chain_bv1 hΛ1 hR he hΛR hxv0 hcd hbar hiv hκI hav1⟩

/-- The scalar arithmetic of the clip. -/
lemma clip_arith {Λ R e₀ l Ih Iv : ℝ} (hΛ1 : 1 ≤ Λ) (hR : 1 ≤ R) (he : 1 ≤ e₀)
    (hΛR : Λ ≤ e₀ * R) (hl : 0 ≤ l)
    (hIh : Ih ≤ 75000 * e₀ ^ 4 * R ^ 4 + (4 * Λ + 200) * l * (75000 * e₀ ^ 4 * R ^ 4) + 48 * R ^ 2)
    (hIv : 5 / 4 * Iv ≤ 39000000 * e₀ ^ 5 * R ^ 4 +
      l * ((4 * Λ + 490) * (39000000 * e₀ ^ 5 * R ^ 4) +
        (36 * Λ ^ 2 + 90) * (75000 * e₀ ^ 4 * R ^ 3)) + 96 * R ^ 2) :
    Ih + Iv ≤ 20000000000 * e₀ ^ 6 * (R ^ 4 + l * R ^ 5) := by
  have hR0 : 0 < R := by linarith
  have he0 : 0 < e₀ := by linarith
  have h1 : (4 * Λ + 200) ≤ 204 * (e₀ * R) := by nlinarith
  have h2 : (4 * Λ + 490) ≤ 494 * (e₀ * R) := by nlinarith
  have h3 : 36 * Λ ^ 2 + 90 ≤ 126 * (e₀ * R) ^ 2 := by
    have : Λ ^ 2 ≤ (e₀ * R) ^ 2 := pow_le_pow_left₀ (by linarith) hΛR 2
    nlinarith
  set m6 : ℝ := e₀ ^ 6 * R ^ 5 with hm6
  set m4 : ℝ := e₀ ^ 6 * R ^ 4 with hm4
  have hm40 : 0 ≤ m4 := by positivity
  have hm60 : 0 ≤ m6 := by positivity
  have t1 : (4 * Λ + 200) * l * (75000 * e₀ ^ 4 * R ^ 4) ≤ 15300000 * (l * m6) := by
    have a1 : e₀ ^ 5 * R ^ 5 ≤ m6 := mono_pow_mul he hR (by norm_num) le_rfl
    calc _ ≤ 204 * (e₀ * R) * l * (75000 * e₀ ^ 4 * R ^ 4) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hl) (by positivity)
      _ = 15300000 * (l * (e₀ ^ 5 * R ^ 5)) := by ring
      _ ≤ _ := by gcongr
  have t2 : (4 * Λ + 490) * (39000000 * e₀ ^ 5 * R ^ 4) ≤ 19266000000 * m6 := by
    calc _ ≤ 494 * (e₀ * R) * (39000000 * e₀ ^ 5 * R ^ 4) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by simp only [hm6]; ring
  have t3 : (36 * Λ ^ 2 + 90) * (75000 * e₀ ^ 4 * R ^ 3) ≤ 9450000 * m6 := by
    calc _ ≤ 126 * (e₀ * R) ^ 2 * (75000 * e₀ ^ 4 * R ^ 3) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = _ := by simp only [hm6]; ring
  have t4 : e₀ ^ 4 * R ^ 4 ≤ m4 := mono_pow_mul he hR (by norm_num) le_rfl
  have t5 : e₀ ^ 5 * R ^ 4 ≤ m4 := mono_pow_mul he hR (by norm_num) le_rfl
  have t6 : R ^ 2 ≤ m4 := by
    have := mono_pow_mul he hR (a := 0) (b := 6) (c := 2) (d := 4) (by norm_num) (by norm_num)
    simpa using this
  have t7 := mul_le_mul_of_nonneg_left (add_le_add t2 t3) hl
  have hIv' : Iv ≤ 5 / 4 * Iv ∨ Iv < 0 := by
    by_cases h : 0 ≤ Iv
    · left; linarith
    · right; linarith
  have e : 20000000000 * e₀ ^ 6 * (R ^ 4 + l * R ^ 5) =
      20000000000 * m4 + 20000000000 * (l * m6) := by
    simp only [hm4, hm6]; ring
  rw [e]
  rcases hIv' with h | h
  · nlinarith
  · have : 0 ≤ l * m6 := mul_nonneg hl hm60
    nlinarith

/-- **The chain.** -/
theorem chain_core (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b₀ t : ℝ} (hb₀ : 0 ≤ b₀)
    (hb₀t : b₀ ≤ t) (ht : ENNReal.ofReal t < Ty) {q : ℕ} (hq : 1 ≤ q) {Λ D R e₀ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hD : 0 ≤ D) (hR : 1 ≤ R) (he : 1 ≤ e₀) (hΛR : Λ ≤ e₀ * R)
    (hS : StrainOn r g y b₀ t q D) (hS2 : StrainOn r g y b₀ t (2 * q) D)
    (hDΛ : D ^ q ≤ Λ ^ (q - 1))
    (hE : (∫ u in b₀..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 24 * R ^ 2)
    (hIz : ∀ u₁ u₂, b₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      (∫ u in u₁..u₂, hnorm 1 (corrSlow r g y u) ^ 2) ≤ 169 * R ^ 2)
    (hIh : ∀ u₁ u₂, b₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      (∫ u in u₁..u₂, hnorm 2 (PiH (corrSlow r g y u)) ^ 2) ≤ 169 * R ^ 2)
    (h0v : hnorm 1 (PiV (corrSlow r g y b₀)) ^ 2 ≤ 40401 * e₀ ^ 4 * R ^ 3)
    (h0h : hnorm 2 (PiH (corrSlow r g y b₀)) ^ 2 ≤ 40401 * e₀ ^ 4 * R ^ 4)
    (h0b : hnorm 2 (PiV (corrSlow r g y b₀)) ^ 2 ≤ 18498601 * e₀ ^ 4 * R ^ 4) :
    ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) b₀ t e₀ R := by
  have ht0 : 0 ≤ t := hb₀.trans hb₀t
  have hΛ0 : 0 < Λ := by linarith
  have hsub0 : Icc b₀ t ⊆ Icc 0 t := Icc_subset_Icc_left hb₀
  have hfi := intervalIntegrable_corrRes_sq h hr hb₀ hb₀t ht
  have hcv : ContinuousOn (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2) (Icc b₀ t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono hsub0
  have hcd : ContinuousOn (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2) (Icc b₀ t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono hsub0
  have hch : ContinuousOn (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (Icc b₀ t) :=
    (continuousOn_corrH_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono hsub0
  have hz1c : ContinuousOn (fun u => hnorm 1 (corrSlow r g y u) ^ 2) (Icc b₀ t) :=
    (continuousOn_corr_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono hsub0
  have hadm : ∀ u ∈ Icc b₀ t, Adm 2 (corrSlow r g y u) := fun u hu =>
    corrSlow_adm h hr (hb₀.trans hu.1) (lt_lifespan hu.2 ht)
  have hIv : ∀ u₁ u₂, b₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      (∫ u in u₁..u₂, hnorm 1 (PiV (corrSlow r g y u)) ^ 2) ≤ 169 * R ^ 2 := by
    intro u₁ u₂ h1 h2 h3
    have hsub : Icc u₁ u₂ ⊆ Icc b₀ t := Icc_subset_Icc h1 h3
    refine le_trans (intervalIntegral.integral_mono_on h2
      ((hcv.mono hsub).intervalIntegrable_of_Icc h2) ((hz1c.mono hsub).intervalIntegrable_of_Icc h2)
      fun u hu => ?_) (hIz u₁ u₂ h1 h2 h3)
    exact pow_le_pow_left₀ (hnorm_nonneg _ _)
      (hnorm_PiV_le' ((hadm u (hsub hu)).inH.mono (by norm_num))) 2
  refine chain_scalar hb₀t hΛ1 hR he hΛR (fun u => sq_nonneg _) (fun u => sq_nonneg _)
    (dh := fun u => hnorm 3 (PiH (corrSlow r g y u)) ^ 2) (fun u => sq_nonneg _)
    (f := fun u => hnorm 1 (corrRes r g y u) ^ 2) (fun u => sq_nonneg _) hcv hch hcd hfi hE hIv hIh
    (fun u₁ u₂ h1 h2 h3 => vert_h1_law h hr (hb₀.trans h1) h2 (lt_lifespan h3 ht) hq hΛ0 hD
      (fun u hu => hS u ⟨h1.trans hu.1, hu.2.trans h3⟩) hDΛ)
    (fun u₁ u₂ h1 h2 h3 => horiz_h2_law h hr (hb₀.trans h1) h2 (lt_lifespan h3 ht) hq hΛ0 hD
      (fun u hu => hS u ⟨h1.trans hu.1, hu.2.trans h3⟩) hDΛ) ?_ h0v h0h h0b
  intro u₁ u₂ A h1 h2 h3 hA ha τ hτ
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hEs : (∫ u in u₁..u₂, hnorm 1 (corrRes r g y u) ^ 2) ≤ 24 * R ^ 2 :=
    (intervalIntegral.integral_mono_interval h1 h2 h3
      (Eventually.of_forall fun _ => sq_nonneg _) hfi).trans hE
  have hb := vert_h2_barrier h hr (hb₀.trans h1) h2 (lt_lifespan h3 ht) hq hΛ0 hD
    (fun u hu => hS u ⟨h1.trans hu.1, hu.2.trans h3⟩)
    (fun u hu => hS2 u ⟨h1.trans hu.1, hu.2.trans h3⟩) hDΛ hsA
    (fun u hu => Real.le_sqrt_of_sq_le (ha u hu)) hEs τ hτ u₂ ⟨hτ.2, le_rfl⟩
  rw [Real.sq_sqrt hA.le] at hb
  linarith

lemma tail_l1_le' {N : ℕ} (hN : 1 ≤ N) {s : Field} (hs2 : MZ 2 s)
    (hsl : ∀ k, k 2 ≠ 0 → s k = 0) (i : Fin 3) :
    Summable (fun k => rhoN N k * ‖GN.cmp s i k‖) ∧
      ∑' k, rhoN N k * ‖GN.cmp s i k‖ ≤ 4 * hnorm 2 s / N := by
  have hle : ∀ k, rhoN N k * ‖GN.cmp s i k‖ ≤ if k ∈ slowBox N then 0 else ‖s k‖ := fun k => by
    simp only [rhoN]
    split_ifs
    · simp
    · simpa using norm_cmp_le s i k
  have hs : Summable fun k => if k ∈ slowBox N then 0 else ‖s k‖ :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> simp) (fun k => by
      split_ifs
      · exact norm_nonneg _
      · exact le_rfl) (summable_wiener hs2.inH)
  have hS := Summable.of_nonneg_of_le
    (fun k => mul_nonneg (rhoN_nonneg _ _) (norm_nonneg _)) hle hs
  exact ⟨hS, (hS.tsum_le_tsum hle hs).trans (tsum_tail_le hs2.inH hsl hs2.mean hN)⟩

/-- The commutator of the truncation with no `H³` norm: `‖Z_N‖₂ ≲ ‖s‖₂(‖c‖₁ + ‖c‖₂)/N`. -/
theorem nn2_errP_le' {N : ℕ} (hN : 1 ≤ N) {s : Field} {c : Mode → ℂ}
    (hs2 : MZ 2 s) (hsl : ∀ k, k 2 ≠ 0 → s k = 0)
    (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2) (hcs : ∀ k, k 2 ≠ 0 → c k = 0) :
    nn2 (errP (slowBox (2 * N)) s c) ≤
      18 * hnorm 2 s ^ 2 / N ^ 2 * (16 * sn 1 c + c4 ^ 2 * sn 2 c) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine (nn2_errP_le_of_tail hN hs2 hc1 hc2 hcs fun i => tail_l1_le' hN hs2 hsl i).trans_eq ?_
  field_simp
  ring

/-- The constant of the commutator in the bound for `v`. -/
def errK : ℝ := 36 * (16 + c4 ^ 2)

lemma errK_nonneg : 0 ≤ errK := by unfold errK; positivity

private lemma integral_le_of_le {w : ℝ → ℝ} {u₁ u₂ B : ℝ} (h2 : u₁ ≤ u₂)
    (hw : ContinuousOn w (Icc u₁ u₂)) (hB : ∀ u ∈ Icc u₁ u₂, w u ≤ B) :
    (∫ u in u₁..u₂, w u) ≤ (u₂ - u₁) * B := by
  have := intervalIntegral.integral_mono_on (g := fun _ => B) h2
    (hw.intervalIntegrable_of_Icc h2) (intervalIntegrable_const (μ := volume)) hB
  simpa using this

private lemma integral_lin_two {f₁ f₂ : ℝ → ℝ} {u₁ u₂ a b : ℝ}
    (h₁ : IntervalIntegrable f₁ volume u₁ u₂) (h₂ : IntervalIntegrable f₂ volume u₁ u₂) :
    (∫ u in u₁..u₂, (a * f₁ u + b * f₂ u)) =
      a * (∫ u in u₁..u₂, f₁ u) + b * ∫ u in u₁..u₂, f₂ u := by
  rw [intervalIntegral.integral_add (h₁.const_mul _) (h₂.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

private lemma integral_lin_three {f₁ f₂ f₃ : ℝ → ℝ} {u₁ u₂ a b c : ℝ}
    (h₁ : IntervalIntegrable f₁ volume u₁ u₂) (h₂ : IntervalIntegrable f₂ volume u₁ u₂)
    (h₃ : IntervalIntegrable f₃ volume u₁ u₂) :
    (∫ u in u₁..u₂, (a * f₁ u + b * f₂ u + c * f₃ u)) =
      a * (∫ u in u₁..u₂, f₁ u) + b * (∫ u in u₁..u₂, f₂ u) + c * ∫ u in u₁..u₂, f₃ u := by
  rw [intervalIntegral.integral_add ((h₁.const_mul _).add (h₂.const_mul _)) (h₃.const_mul _),
    intervalIntegral.integral_add (h₁.const_mul _) (h₂.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- **The clip of the chain.** -/
theorem chain_clip (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b₀ t : ℝ} (hb₀ : 0 ≤ b₀)
    (ht : ENNReal.ofReal t < Ty) {q : ℕ} (hq : 1 ≤ q) {Λ D R e₀ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hD : 0 ≤ D) (hR : 1 ≤ R) (he : 1 ≤ e₀) (hΛR : Λ ≤ e₀ * R)
    (hS : StrainOn r g y b₀ t q D) (hS2 : StrainOn r g y b₀ t (2 * q) D)
    (hDΛ : D ^ q ≤ Λ ^ (q - 1))
    (hE : (∫ u in b₀..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 24 * R ^ 2)
    (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) b₀ t e₀ R)
    {u₁ u₂ : ℝ} (h1 : b₀ ≤ u₁) (h2 : u₁ ≤ u₂) (h3 : u₂ ≤ t) :
    (∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2) ≤
      20000000000 * e₀ ^ 6 * (R ^ 4 + (u₂ - u₁) * R ^ 5) := by
  have hb0t : b₀ ≤ t := h1.trans (h2.trans h3)
  have ht0 : 0 ≤ t := hb₀.trans hb0t
  have hu₁ : 0 ≤ u₁ := hb₀.trans h1
  have hΛ0 : 0 < Λ := by linarith
  have hsub : Icc u₁ u₂ ⊆ Icc b₀ t := Icc_subset_Icc h1 h3
  have hsub0 : Icc u₁ u₂ ⊆ Icc 0 t := hsub.trans (Icc_subset_Icc_left hb₀)
  have hl : 0 ≤ u₂ - u₁ := by linarith
  have hfi0 := intervalIntegrable_corrRes_sq h hr hb₀ hb0t ht
  have hfi : IntervalIntegrable (fun u => hnorm 1 (corrRes r g y u) ^ 2) volume u₁ u₂ :=
    intervalIntegrable_corrRes_sq h hr hu₁ h2 (lt_lifespan h3 ht)
  have hEs : (∫ u in u₁..u₂, hnorm 1 (corrRes r g y u) ^ 2) ≤ 24 * R ^ 2 :=
    (intervalIntegral.integral_mono_interval h1 h2 h3
      (Eventually.of_forall fun _ => sq_nonneg _) hfi0).trans hE
  have hcv : ContinuousOn (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2) (Icc u₁ u₂) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono hsub0
  have hcd : ContinuousOn (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2) (Icc u₁ u₂) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono hsub0
  have hch : ContinuousOn (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (Icc u₁ u₂) :=
    (continuousOn_corrH_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono hsub0
  have hlH := horiz_h2_law h hr hu₁ h2 (lt_lifespan h3 ht) hq hΛ0 hD
    (fun u hu => hS u ⟨h1.trans hu.1, hu.2.trans h3⟩) hDΛ
  have hlV := vert_h2_law h hr hu₁ h2 (lt_lifespan h3 ht) hq hΛ0 hD
    (fun u hu => hS u ⟨h1.trans hu.1, hu.2.trans h3⟩)
    (fun u hu => hS2 u ⟨h1.trans hu.1, hu.2.trans h3⟩) hDΛ
  have hxh := integral_le_of_le h2 hch fun u hu => hC.bh u (hsub hu)
  have hxv := integral_le_of_le h2 hcv fun u hu => hC.av u (hsub hu)
  have hxd := integral_le_of_le h2 hcd fun u hu => hC.bv u (hsub hu)
  have e1 := integral_lin_two (a := 4 * Λ + 200) (b := 2) (hch.intervalIntegrable_of_Icc h2) hfi
  have e2 := integral_lin_three (a := 4 * Λ + 490) (b := 36 * Λ ^ 2 + 90) (c := 4)
    (hcd.intervalIntegrable_of_Icc h2) (hcv.intervalIntegrable_of_Icc h2) hfi
  rw [e1] at hlH
  rw [e2] at hlV
  have hH0 : 0 ≤ hnorm 2 (PiH (corrSlow r g y u₂)) ^ 2 := sq_nonneg _
  have hV0 : 0 ≤ hnorm 2 (PiV (corrSlow r g y u₂)) ^ 2 := sq_nonneg _
  have hb1 := hC.bh u₁ (hsub ⟨le_rfl, h2⟩)
  have hb2 := hC.bv u₁ (hsub ⟨le_rfl, h2⟩)
  have hκ1 : 0 ≤ 4 * Λ + 200 := by positivity
  have hκ2 : 0 ≤ 4 * Λ + 490 := by positivity
  have hκ3 : 0 ≤ 36 * Λ ^ 2 + 90 := by positivity
  refine (integral_hnorm_three_le h hr hu₁ h2 (lt_lifespan h3 ht)).trans
    (clip_arith hΛ1 hR he hΛR hl ?_ ?_)
  · have h4 := mul_le_mul_of_nonneg_left hxh hκ1
    nlinarith
  · have h4 := mul_le_mul_of_nonneg_left hxd hκ2
    have h5 := mul_le_mul_of_nonneg_left hxv hκ3
    nlinarith

/-! ### The sup bound of the vertical part: the box is explicit -/

lemma corrRes_zero_mode (h : ActualSol μ φ r g y Ty) (t : ℝ) : corrRes r g y t 0 = 0 := by
  have h1 : absSq (0 : Mode) = 0 := by simp [absSq]
  have h2 : g 0 = 0 := h.force_adm.mean
  have hQ : ∀ (m : Mult) (a b : Field), Qm m a b 0 = 0 := fun m a b => by
    simp [Qm, hel]
  have hB : ∀ a b : Field, Bsym a b 0 = 0 := fun a b => by
    simp [Bsym, vert, leray]
  simp only [corrRes, slowRes, h1, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, PiS, Hpsi]
  simp [h2, hB, kinN_zero_mode, Qphase, hQ]

/-- The source of the truncated vertical part, integrated. -/
lemma integral_src_vert_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbT : ENNReal.ofReal b < Ty) {N : ℕ} (hN : 1 ≤ N) {B2 : ℝ} (hB20 : 0 ≤ B2)
    (hB : ∀ u ∈ Icc a b, hnorm 2 (corrSlow r g y u) ^ 2 ≤ B2) :
    ∫ u in a..b, nn2 (srcP (slowBox (2 * N)) (fun t => GN.cmp (corrSlow r g y t) 2)
      (rhsP (corrSlow r g y) (fun t => GN.cmp (corrSlow r g y t) 2)
        (fun t => GN.cmp (corrRes r g y t) 2))
      (fun t i => GN.cmp (corrSlow r g y t) i) u) ≤
      2 * (∫ u in a..b, hnorm 1 (corrRes r g y u) ^ 2) + (b - a) * (errK * B2 ^ 2 / N ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hP := passive_vert h hr ha hab hbT
  have hp := hP.polyPath (2 * N)
  have hc := hp.continuousOn_srcNorm.intervalIntegrable_of_Icc (μ := volume) hab
  have hfi := intervalIntegrable_corrRes_sq h hr ha hab hbT
  have hR : IntervalIntegrable (fun u => 2 * hnorm 1 (corrRes r g y u) ^ 2 +
      errK * B2 ^ 2 / N ^ 2) volume a b :=
    (hfi.const_mul 2).add (intervalIntegrable_const (μ := volume))
  have hmono := intervalIntegral.integral_mono_ae_restrict hab hc hR (by
    filter_upwards [ae_inH1_corrRes h hr ha hab hbT, ae_restrict_mem measurableSet_Icc]
      with u hf1 hu
    have hz := corrSlow_adm h hr (ha.trans hu.1) (lt_lifespan hu.2 hbT)
    have hz' := PiS_corrSlow r g y u
    have hB0 : hnorm 2 (corrSlow r g y u) ^ 2 ≤ B2 := hB u hu
    have hsn1 : sn 1 (GN.cmp (corrSlow r g y u) 2) ≤ B2 := by
      have e := sn_cmp_two hz' hz.mean 1
      norm_num at e
      rw [e]
      refine le_trans (pow_le_pow_left₀ (hnorm_nonneg _ _) ?_ 2) hB0
      exact (hnorm_mono (by norm_num) hz.inH.PiV).trans (hnorm_PiV_le' hz.inH)
    have hsn2 : sn 2 (GN.cmp (corrSlow r g y u) 2) ≤ B2 := by
      have e := sn_cmp_two hz' hz.mean 2
      norm_num at e
      rw [e]
      exact (pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_PiV_le' hz.inH) 2).trans hB0
    rw [srcP_passive (slowBox (2 * N)) (corrSlow r g y)
      (fun t => GN.cmp (corrSlow r g y t) 2) (fun t => GN.cmp (corrRes r g y t) 2) u]
    have h2 := nn2_add_le (polyOf (slowBox (2 * N)) (GN.cmp (corrRes r g y u) 2))
      (errP (slowBox (2 * N)) (corrSlow r g y u) (GN.cmp (corrSlow r g y u) 2))
    obtain ⟨hs0, hs1⟩ := sn_zero_cmp_le hf1 (corrRes_zero_mode h u) 2
    have h3 : nn2 (polyOf (slowBox (2 * N)) (GN.cmp (corrRes r g y u) 2)) ≤
        hnorm 1 (corrRes r g y u) ^ 2 :=
      (nn2_polyOf_le hs0).trans (by rw [← sn_zero]; exact hs1)
    have h4 := nn2_errP_le' hN hz.mz (fun k hk => slow_zero' hz' hk)
      (summable_cmp (hz.inH.mono (by norm_num : (1 : ℝ) ≤ 2)) hz.mean (by norm_num) 2)
      (summable_cmp hz.inH hz.mean (by norm_num) 2) (fun k hk => cmp_slow hz' 2 k hk)
    have hc0 : 0 ≤ c4 ^ 2 := sq_nonneg _
    have h5 : hnorm 2 (corrSlow r g y u) ^ 2 * (16 * sn 1 (GN.cmp (corrSlow r g y u) 2) +
        c4 ^ 2 * sn 2 (GN.cmp (corrSlow r g y u) 2)) ≤ B2 * (16 * B2 + c4 ^ 2 * B2) :=
      mul_le_mul hB0 (add_le_add (by linarith) (mul_le_mul_of_nonneg_left hsn2 hc0))
        (add_nonneg (by have := sn_nonneg 1 (GN.cmp (corrSlow r g y u) 2); positivity)
          (mul_nonneg hc0 (sn_nonneg _ _))) hB20
    have h6 : 18 * hnorm 2 (corrSlow r g y u) ^ 2 / N ^ 2 *
        (16 * sn 1 (GN.cmp (corrSlow r g y u) 2) + c4 ^ 2 * sn 2 (GN.cmp (corrSlow r g y u) 2)) =
        18 / N ^ 2 * (hnorm 2 (corrSlow r g y u) ^ 2 * (16 * sn 1 (GN.cmp (corrSlow r g y u) 2) +
          c4 ^ 2 * sn 2 (GN.cmp (corrSlow r g y u) 2))) := by ring
    have h7 : 18 / (N : ℝ) ^ 2 * (hnorm 2 (corrSlow r g y u) ^ 2 *
        (16 * sn 1 (GN.cmp (corrSlow r g y u) 2) + c4 ^ 2 * sn 2 (GN.cmp (corrSlow r g y u) 2))) ≤
        18 / (N : ℝ) ^ 2 * (B2 * (16 * B2 + c4 ^ 2 * B2)) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    have h8 : 2 * (18 / (N : ℝ) ^ 2 * (B2 * (16 * B2 + c4 ^ 2 * B2))) = errK * B2 ^ 2 / N ^ 2 := by
      simp only [errK]
      ring
    rw [h6] at h4
    linarith)
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add (hfi.const_mul 2)
    (intervalIntegrable_const (μ := volume) (c := errK * B2 ^ 2 / (N : ℝ) ^ 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]

/-- **Moser for `v` past the first unit, in an explicit box.** -/
theorem vert_moser_box (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbT : ENNReal.ofReal b < Ty) {N : ℕ} (hN : 1 ≤ N) {T Y B2 : ℝ} (hT : b - a ≤ T)
    (hT0 : 0 ≤ T) (hY : 0 < Y) (hB20 : 0 ≤ B2)
    (hB : ∀ u ∈ Icc a b, hnorm 2 (corrSlow r g y u) ^ 2 ≤ B2)
    (hF : 2 * (∫ u in a..b, hnorm 1 (corrRes r g y u) ^ 2) + T * (errK * B2 ^ 2 / N ^ 2) ≤ Y)
    (hL : ∀ u ∈ Icc a b, hnorm 0 (corrSlow r g y u) ^ 2 ≤ Y) (n : ℕ) :
    ∀ u ∈ Icc (a + 1 - 1 / 2 ^ n) b, mP (2 ^ n)
      (polyOf (slowBox (2 * N)) (GN.cmp (corrSlow r g y u) 2)) ≤ (piM T n * Y) ^ (2 ^ n) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hP := passive_vert h hr ha hab hbT
  have hsrc := integral_src_vert_le h hr ha hab hbT hN hB20 hB
  have hE0 : 0 ≤ errK * B2 ^ 2 / N ^ 2 := by
    have := errK_nonneg
    positivity
  refine (hP.polyPath (2 * N)).moser hT hT0 hY (fun u hu => ?_) (hsrc.trans ?_) n
  · have hz := corrSlow_adm h hr (ha.trans hu.1) (lt_lifespan hu.2 hbT)
    obtain ⟨hs0, hs1⟩ := sn_zero_cmp_le (hz.inH.mono (by norm_num : (1 : ℝ) ≤ 2)) hz.mean 2
    have h1 : sn 0 (GN.cmp (corrSlow r g y u) 2) ≤ hnorm 0 (corrSlow r g y u) ^ 2 := by
      have e := sn_cmp_two (PiS_corrSlow r g y u) hz.mean 0
      norm_num at e
      rw [e]
      exact pow_le_pow_left₀ (hnorm_nonneg _ _)
        (hnorm_PiV_le' (hz.inH.mono (by norm_num))) 2
    exact (mP_one_polyOf_le hs0).trans (h1.trans (hL u hu))
  · have h1 := mul_le_mul_of_nonneg_right hT hE0
    linarith

/-- Sobolev for `v` at the true zero. -/
private lemma vert_zero_start (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hT : ENNReal.ofReal 0 < Ty) {N : ℕ} {Y' : ℝ} (hY' : 0 < Y')
    (h0 : hnorm 0 (corrSlow r g y 0) ^ 2 ≤ Y') (h1 : 2 * hnorm 1 (corrSlow r g y 0) ^ 2 ≤ Y')
    (n : ℕ) : mP (2 ^ n) (polyOf (slowBox (2 * N)) (GN.cmp (corrSlow r g y 0) 2)) ≤
      (piM 1 n * Y') ^ (2 ^ n) := by
  have hz0 := corrSlow_adm h hr le_rfl hT
  refine sobolev_box ?_ ?_ ?_ _ hY' ?_ ?_ n
  · intro k
    change (corrSlow r g y 0 (-k)) 2 = conj ((corrSlow r g y 0 k) 2)
    rw [hz0.real k]
    rfl
  · exact (sn_zero_cmp_le (hz0.inH.mono (by norm_num : (1 : ℝ) ≤ 2)) hz0.mean 2).1
  · exact summable_cmp (hz0.inH.mono (by norm_num : (1 : ℝ) ≤ 2)) hz0.mean (by norm_num) 2
  · have e := sn_cmp_two (PiS_corrSlow r g y 0) hz0.mean 0
    norm_num at e
    rw [e]
    exact (pow_le_pow_left₀ (hnorm_nonneg _ _)
      (hnorm_PiV_le' (hz0.inH.mono (by norm_num))) 2).trans h0
  · have e := sn_cmp_two (PiS_corrSlow r g y 0) hz0.mean 1
    norm_num at e
    rw [e]
    have h3 : hnorm 1 (PiV (corrSlow r g y 0)) ^ 2 ≤ hnorm 1 (corrSlow r g y 0) ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_PiV_le' (hz0.inH.mono (by norm_num))) 2
    linarith

/-- **`L^{2q}` of `v` from the true zero, in an explicit box.** -/
theorem vert_zero_box (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) {N : ℕ} (hN : 1 ≤ N) {T Y Y' B2 : ℝ} (hT : b ≤ T)
    (hY' : 0 < Y') (hB20 : 0 ≤ B2)
    (hB : ∀ u ∈ Icc 0 b, hnorm 2 (corrSlow r g y u) ^ 2 ≤ B2)
    (hF : 2 * (∫ u in (0 : ℝ)..b, hnorm 1 (corrRes r g y u) ^ 2) + T * (errK * B2 ^ 2 / N ^ 2) ≤ Y)
    (h0 : hnorm 0 (corrSlow r g y 0) ^ 2 ≤ Y') (h1 : 2 * hnorm 1 (corrSlow r g y 0) ^ 2 ≤ Y')
    (n : ℕ) :
    ∀ u ∈ Icc 0 b, mP (2 ^ n) (polyOf (slowBox (2 * N)) (GN.cmp (corrSlow r g y u) 2)) ≤
      (Real.exp T * (2 * (piM 1 n * Y') + 201 * 2 ^ n * Y)) ^ (2 ^ n) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hP := passive_vert h hr le_rfl hb hbT
  have hp := hP.polyPath (2 * N)
  have hsrc := integral_src_vert_le h hr le_rfl hb hbT hN hB20 hB
  have hE0 : 0 ≤ errK * B2 ^ 2 / N ^ 2 := by
    have := errK_nonneg
    positivity
  have hsrc' : (∫ u in (0 : ℝ)..b, nn2 (srcP (slowBox (2 * N))
      (fun t => GN.cmp (corrSlow r g y t) 2)
      (rhsP (corrSlow r g y) (fun t => GN.cmp (corrSlow r g y t) 2)
        (fun t => GN.cmp (corrRes r g y t) 2))
      (fun t i => GN.cmp (corrSlow r g y t) i) u)) ≤ Y := by
    refine hsrc.trans ?_
    have h2 := mul_le_mul_of_nonneg_right hT hE0
    simp only [sub_zero]
    linarith
  have hPi := one_le_piM (zero_le_one) n
  have hY₀ : 0 < piM 1 n * Y' := by positivity
  have hst := vert_zero_start h hr ((ENNReal.ofReal_le_ofReal hb).trans_lt hbT) (N := N) hY' h0 h1 n
  intro u hu
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine (hp.propagate hq le_rfl hu.1 hu.2 hY₀ hst).trans (pow_le_pow_left₀ ?_ ?_ _)
  · have : 0 ≤ ∫ w in (0 : ℝ)..u, nn2 (srcP (slowBox (2 * N))
        (fun t => GN.cmp (corrSlow r g y t) 2)
        (rhsP (corrSlow r g y) (fun t => GN.cmp (corrSlow r g y t) 2)
          (fun t => GN.cmp (corrRes r g y t) 2)) (fun t i => GN.cmp (corrSlow r g y t) i) w) :=
      intervalIntegral.integral_nonneg hu.1 fun _ _ => nn2_nonneg _
    positivity
  · have hint : (∫ w in (0 : ℝ)..u, nn2 (srcP (slowBox (2 * N))
        (fun t => GN.cmp (corrSlow r g y t) 2)
        (rhsP (corrSlow r g y) (fun t => GN.cmp (corrSlow r g y t) 2)
          (fun t => GN.cmp (corrRes r g y t) 2)) (fun t i => GN.cmp (corrSlow r g y t) i) w)) ≤ Y :=
      (intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2
        (Eventually.of_forall fun _ => nn2_nonneg _)
        (hp.continuousOn_srcNorm.intervalIntegrable_of_Icc hp.hab)).trans hsrc'
    have hexp : Real.exp ((u - 0) / ((2 ^ n : ℕ) : ℝ)) ≤ Real.exp T := by
      refine Real.exp_le_exp.2 ?_
      have h5 : (1 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hq
      have h4 : 0 ≤ u - 0 := by linarith [hu.1]
      exact (div_le_self h4 h5).trans (by linarith [hu.2])
    have hint0 : 0 ≤ ∫ w in (0 : ℝ)..u, nn2 (srcP (slowBox (2 * N))
        (fun t => GN.cmp (corrSlow r g y t) 2)
        (rhsP (corrSlow r g y) (fun t => GN.cmp (corrSlow r g y t) 2)
          (fun t => GN.cmp (corrRes r g y t) 2)) (fun t i => GN.cmp (corrSlow r g y t) i) w) :=
      intervalIntegral.integral_nonneg hu.1 fun _ _ => nn2_nonneg _
    refine mul_le_mul hexp ?_ (by positivity) (Real.exp_pos _).le
    push_cast
    have : (0 : ℝ) ≤ 201 * 2 ^ n := by positivity
    nlinarith

end Actual

end OVNS.Quant.Slow
