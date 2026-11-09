import OddViscousNS.Quant.Joint.Slow.Passive
import OddViscousNS.Quant.Energy.Slow.Barrier

/-!
# E7-P: the vertical component and the vorticity of the corrected slow field are passive

* `cmp_Bsym_two`: the third component of `B(z, z)` is the transport of the third component.
* `curlL`, `wC`: the scalar vorticity; `wC_Bsym`: the curl of `B(z, z)` is the transport of the
  vorticity, by the pointwise antisymmetry of the stretching term in the triad, which is the
  two-dimensional fact `linear_combination (q₀ b₁ − q₁ b₀) (a·p) + (a₁ p₀ − a₀ p₁) (b·q)`.
* `passive_vert`, `passive_curl`: the `Passive` instances along the actual solution, with sources
  the corresponding components of `corrRes`.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.Slow

open GN

/-! ### The transport as a series -/

lemma advC_eq_tsum {z : Field} {c : Mode → ℂ} {k : Mode}
    (hs : Summable fun p => ‖z p‖ * (absk (k - p) * ‖c (k - p)‖)) :
    advC z c k = ∑' p, Complex.I * dotM (z p) (k - p) * c (k - p) := by
  have hsum : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun p => GN.cmp z i p * dC i c (k - p) := fun i _ => by
    refine Summable.of_norm_bounded hs fun p => ?_
    rw [norm_mul]
    exact mul_le_mul (norm_cmp_le z i p) (norm_dC_le i _ _) (norm_nonneg _) (norm_nonneg _)
  simp only [advC, cv]
  rw [← Summable.tsum_finsetSum hsum]
  refine tsum_congr fun p => ?_
  simp only [dotM, GN.cmp, dC, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma norm_dotM_mul_le (v : V3) (q : Mode) (x : ℂ) :
    ‖Complex.I * dotM v q * x‖ ≤ ‖v‖ * (absk q * ‖x‖) := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  calc ‖dotM v q‖ * ‖x‖ ≤ (‖v‖ * absk q) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (norm_dotM_le _ _) (norm_nonneg _)
    _ = _ := by ring

lemma slow_zero' {z : Field} (hz : PiS z = z) {k : Mode} (hk : k 2 ≠ 0) : z k = 0 := by
  rw [← hz]
  simp [PiS, hk]

/-- Advection of a slow field vanishes on the fast modes. -/
lemma advect_comp_fast {z : Field} (hz : PiS z = z) {c : Mode → ℂ}
    (hc : ∀ k, k 2 ≠ 0 → c k = 0) {k : Mode} (hk : k 2 ≠ 0) (p : Mode) :
    Complex.I * dotM (z p) (k - p) * c (k - p) = 0 := by
  by_cases hp : p 2 = 0
  · have : (k - p) 2 ≠ 0 := by simpa [hp] using hk
    rw [hc _ this, mul_zero]
  · rw [slow_zero' hz hp]
    simp [dotM]

/-! ### The vertical component -/

lemma leray_two {k : Mode} (hk : k 2 = 0) (hk0 : k ≠ 0) (v : V3) : (leray k v) 2 = v 2 := by
  simp [leray, hk0, modeVec, hk]

/-- `∑_p (z_p · i(−p)) c_{−p} = 0`: the transport has zero mean. -/
lemma advC_zero {z : Field} (hz : IsSolenoidal z) (c : Mode → ℂ)
    (hs : Summable fun p => ‖z p‖ * (absk (0 - p) * ‖c (0 - p)‖)) : advC z c 0 = 0 := by
  rw [advC_eq_tsum hs]
  have : ∀ p, Complex.I * dotM (z p) (0 - p) * c (0 - p) = 0 := fun p => by
    have h1 : dotM (z p) (0 - p) = -dotM (z p) p := by
      simp [dotM, Finset.sum_neg_distrib]
    rw [h1, hz p]
    simp
  rw [tsum_congr this, tsum_zero]

lemma cmp_slow {z : Field} (hz : PiS z = z) (a : Fin 3) (k : Mode) (hk : k 2 ≠ 0) :
    GN.cmp z a k = 0 := by
  change (z k) a = 0
  rw [slow_zero' hz hk]
  rfl

lemma summable_adv_cmp {z : Field} (hz2 : InH 2 z) (a : Fin 3) (k : Mode) :
    Summable fun p => ‖z p‖ * (absk (k - p) * ‖GN.cmp z a (k - p)‖) := by
  have h0 : Summable fun k => ‖z k‖ ^ 2 := summable_sq_of_summable (summable_wiener hz2)
  refine Summable.of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (mul_nonneg (absk_nonneg _) (norm_nonneg _))) (fun p => ?_)
    (summable_adv h0 (hz2.mono (by norm_num : (1 : ℝ) ≤ 2)) k)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_cmp_le z a _) (absk_nonneg _))
    (norm_nonneg _)

/-- **The vertical component is transported.** -/
theorem cmp_Bsym_two {z : Field} (hz : Adm 2 z) (hz' : PiS z = z) (k : Mode) :
    GN.cmp (Bsym z z) 2 k = advC z (GN.cmp z 2) k := by
  have hB : Bsym z z k = leray k (advect z z k) := by
    rw [Bsym_self hz.mz]
    rfl
  have h1 := summable_adv (f := z) (g := z) (summable_sq_of_summable (summable_wiener hz.inH))
    (hz.inH.mono (by norm_num)) k
  have h2 : advect z z k 2 = advC z (GN.cmp z 2) k := advect_apply h1 2
  have hs := summable_adv_cmp hz.inH 2 k
  by_cases hk : k 2 = 0
  · by_cases hk0 : k = 0
    · subst hk0
      rw [advC_zero hz.sol _ hs]
      change (Bsym z z 0) 2 = 0
      rw [hB]
      simp [leray]
    · change (Bsym z z k) 2 = _
      rw [hB, leray_two hk hk0, h2]
  · have h3 : advC z (GN.cmp z 2) k = 0 := by
      rw [advC_eq_tsum hs, tsum_congr (advect_comp_fast hz' (cmp_slow hz' 2) hk), tsum_zero]
    have h4 : advect z z k = 0 := by
      refine (tsum_congr fun p => ?_).trans tsum_zero
      by_cases hp : p 2 = 0
      · have : (k - p) 2 ≠ 0 := by simpa [hp] using hk
        rw [slow_zero' hz' this, smul_zero]
      · rw [slow_zero' hz' hp]
        simp [dotM]
    rw [h3]
    change (Bsym z z k) 2 = 0
    rw [hB, h4]
    have e : leray k (0 : V3) = 0 := by
      simp [leray, dotM]
    rw [e]
    rfl

/-! ### The vorticity -/

/-- The scalar vorticity at mode `k`, as a linear functional. -/
def curlL (k : Mode) : V3 →L[ℂ] ℂ :=
  Complex.I • (((k 0 : ℂ)) • EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3) -
    ((k 1 : ℂ)) • EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3))

lemma curlL_apply (k : Mode) (v : V3) :
    curlL k v = Complex.I * ((k 0 : ℂ) * v 1 - (k 1 : ℂ) * v 0) := by
  simp [curlL]

/-- The scalar vorticity coefficients. -/
def wC (u : Field) (k : Mode) : ℂ := curlL k (u k)

lemma curlL_leray (k : Mode) (v : V3) : curlL k (leray k v) = curlL k v := by
  by_cases hk : k = 0
  · subst hk
    simp [leray, curlL_apply]
  · rw [curlL_apply, curlL_apply]
    simp only [leray, hk, ↓reduceIte, modeVec]
    simp
    ring

/-- The two-dimensional cancellation of the stretching term. -/
lemma stretch_anti {a b : V3} {p q : Mode} (hp2 : p 2 = 0) (hq2 : q 2 = 0)
    (ha : dotM a p = 0) (hb : dotM b q = 0) :
    dotM a q * ((p 0 : ℂ) * b 1 - (p 1 : ℂ) * b 0) +
      dotM b p * ((q 0 : ℂ) * a 1 - (q 1 : ℂ) * a 0) = 0 := by
  simp only [dotM, Fin.sum_univ_three, hp2, hq2, Int.cast_zero, mul_zero, add_zero] at ha hb ⊢
  linear_combination ((q 0 : ℂ) * b 1 - (q 1 : ℂ) * b 0) * ha +
    (a 1 * (p 0 : ℂ) - a 0 * (p 1 : ℂ)) * hb

/-- The vector with the weight `|k|`. -/
lemma summable_absk_sq {z : Field} (hz : InH 1 z) : Summable fun k => (absk k * ‖z k‖) ^ 2 := by
  refine hz.congr fun q => ?_
  rw [sobWeight_one, mul_pow, absk_sq]

lemma norm_cross_le (p : Mode) (v : V3) :
    ‖(p 0 : ℂ) * v 1 - (p 1 : ℂ) * v 0‖ ≤ 2 * (absk p * ‖v‖) := by
  have h0 : ‖v 0‖ ≤ ‖v‖ := PiLp.norm_apply_le v 0
  have h1 : ‖v 1‖ ≤ ‖v‖ := PiLp.norm_apply_le v 1
  have hp0 : |((p 0 : ℤ) : ℝ)| ≤ absk p := Real.abs_le_sqrt (sq_le_absSq 0 p)
  have hp1 : |((p 1 : ℤ) : ℝ)| ≤ absk p := Real.abs_le_sqrt (sq_le_absSq 1 p)
  calc _ ≤ ‖(p 0 : ℂ) * v 1‖ + ‖(p 1 : ℂ) * v 0‖ := norm_sub_le _ _
    _ ≤ absk p * ‖v‖ + absk p * ‖v‖ := by
        rw [norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_intCast]
        exact add_le_add (mul_le_mul hp0 h1 (norm_nonneg _) (absk_nonneg _))
          (mul_le_mul hp1 h0 (norm_nonneg _) (absk_nonneg _))
    _ = _ := by ring

/-- The weight of the transport of the vorticity. -/
private lemma summable_weight_wC {z : Field} (hz : Adm 2 z) (k : Mode) :
    Summable fun p => ‖z p‖ * (absk (k - p) * ‖wC z (k - p)‖) := by
  have hl2 : Summable fun k => ‖z k‖ ^ 2 := summable_sq_of_summable (summable_wiener hz.inH)
  have h2 : Summable fun w => (absk w * (2 * (absk w * ‖z w‖))) ^ 2 := by
    refine (((hz.inH).mul_left 4).congr fun w => ?_)
    rw [sobWeight_two, ← absk_sq]
    ring
  have h3 := (convR_le_of_l2 (a := fun k => ‖z k‖)
    (b := fun w => absk w * (2 * (absk w * ‖z w‖))) (fun _ => norm_nonneg _)
    (fun w => mul_nonneg (absk_nonneg w) (mul_nonneg (by norm_num) (mul_nonneg (absk_nonneg w)
      (norm_nonneg _)))) hl2 h2 k).1
  refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (mul_nonneg
    (absk_nonneg _) (norm_nonneg _))) (fun p => ?_) h3
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (absk_nonneg _)) (norm_nonneg _)
  rw [wC, curlL_apply, norm_mul, Complex.norm_I, one_mul]
  exact norm_cross_le _ _

/-- The stretching term of the transport of the vorticity sums to zero, by the antisymmetry in the
triad. -/
private lemma stretch_sum {z : Field} (hz : Adm 2 z) (hz' : PiS z = z) (k : Mode) :
    (Summable fun p => (Complex.I * dotM (z p) (k - p)) *
      (Complex.I * ((p 0 : ℂ) * (z (k - p)) 1 - (p 1 : ℂ) * (z (k - p)) 0))) ∧
    ∑' p, (Complex.I * dotM (z p) (k - p)) *
      (Complex.I * ((p 0 : ℂ) * (z (k - p)) 1 - (p 1 : ℂ) * (z (k - p)) 0)) = 0 := by
  constructor
  · have hbd := (convR_le_of_l2 (a := fun k => absk k * ‖z k‖) (b := fun k => absk k * ‖z k‖)
      (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _))
      (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _))
      (summable_absk_sq (hz.inH.mono (by norm_num))) (summable_absk_sq (hz.inH.mono (by norm_num)))
      k).1
    refine Summable.of_norm_bounded (hbd.mul_left 2) fun p => ?_
    have h4 := norm_dotM_le (z p) (k - p)
    have h5 := norm_cross_le p (z (k - p))
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
    calc _ ≤ (‖z p‖ * absk (k - p)) * (2 * (absk p * ‖z (k - p)‖)) :=
          mul_le_mul h4 h5 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (absk_nonneg _))
      _ = _ := by ring
  · set G : Mode → ℂ := fun p => (Complex.I * dotM (z p) (k - p)) *
      (Complex.I * ((p 0 : ℂ) * (z (k - p)) 1 - (p 1 : ℂ) * (z (k - p)) 0)) with hGdef
    have hanti : ∀ p, G (k - p) = -G p := fun p => by
      have e1 : k - (k - p) = p := by simp
      simp only [hGdef, e1]
      by_cases hp : p 2 = 0
      · by_cases hq2 : (k - p) 2 = 0
        · have h6 := stretch_anti hp hq2 (hz.sol p) (hz.sol (k - p))
          have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
          linear_combination (Complex.I * Complex.I) * h6 + (0 : ℂ) * hI
        · rw [slow_zero' hz' hq2]
          simp [dotM]
      · rw [slow_zero' hz' hp]
        simp [dotM]
    have h7 : ∑' p, G p = ∑' p, G (k - p) := ((Equiv.subLeft k).tsum_eq G).symm
    simp only [hanti, tsum_neg] at h7
    exact self_eq_neg.mp h7

/-- **The vorticity is transported**: `curl B(z, z) = z·∇ω` for slow admissible `z`. -/
theorem wC_Bsym {z : Field} (hz : Adm 2 z) (hz' : PiS z = z) (k : Mode) :
    wC (Bsym z z) k = advC z (wC z) k := by
  set q : Mode → Mode := fun p => k - p with hq
  have hB : wC (Bsym z z) k = curlL k (advect z z k) := by
    rw [Bsym_self hz.mz, wC]
    exact curlL_leray k _
  have hl2 : Summable fun k => ‖z k‖ ^ 2 := summable_sq_of_summable (summable_wiener hz.inH)
  have h1a := summable_adv hl2 (hz.inH.mono (by norm_num : (1 : ℝ) ≤ 2)) k
  -- the left side as a series
  have hL : curlL k (advect z z k) = ∑' p, (Complex.I * dotM (z p) (q p)) * curlL k (z (q p)) := by
    have h := (curlL k).map_tsum (summable_adv_term h1a)
    simp only [map_smul, smul_eq_mul] at h
    exact h
  -- summability of the three series
  have hweight : Summable fun p => ‖z p‖ * (absk (q p) * ‖wC z (q p)‖) :=
    summable_weight_wC hz k
  have hsR := fun p => norm_dotM_mul_le (z p) (q p) (wC z (q p))
  have hsumR : Summable fun p => Complex.I * dotM (z p) (q p) * wC z (q p) :=
    Summable.of_norm_bounded hweight hsR
  obtain ⟨hG, hG0⟩ : (Summable fun p => (Complex.I * dotM (z p) (q p)) *
      (Complex.I * ((p 0 : ℂ) * (z (q p)) 1 - (p 1 : ℂ) * (z (q p)) 0))) ∧
      ∑' p, (Complex.I * dotM (z p) (q p)) *
        (Complex.I * ((p 0 : ℂ) * (z (q p)) 1 - (p 1 : ℂ) * (z (q p)) 0)) = 0 :=
    stretch_sum hz hz' k
  rw [hB, hL, advC_eq_tsum hweight]
  have hdiff : ∀ p, (Complex.I * dotM (z p) (q p)) * curlL k (z (q p)) =
      Complex.I * dotM (z p) (q p) * wC z (q p) + (Complex.I * dotM (z p) (q p)) *
        (Complex.I * ((p 0 : ℂ) * (z (q p)) 1 - (p 1 : ℂ) * (z (q p)) 0)) := fun p => by
    rw [wC, curlL_apply, curlL_apply]
    have e0 : ((k 0 : ℤ) : ℂ) = (p 0 : ℂ) + (q p 0 : ℂ) := by
      simp [hq]
    have e1 : ((k 1 : ℤ) : ℂ) = (p 1 : ℂ) + (q p 1 : ℂ) := by
      simp [hq]
    rw [e0, e1]
    ring
  rw [tsum_congr hdiff, hsumR.tsum_add hG, hG0, add_zero]

/-! ### The `Passive` instances along the actual solution -/

section Actual

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- The vertical functional. -/
def vertC : Mode → V3 →L[ℂ] ℂ := fun _ => EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)

lemma continuousOn_corr_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => corrSlow r g y u k) (Icc 0 b) := fun _ ht =>
  (corrSlow_mode h hr hb hbT k ht).continuousWithinAt

/-- **A mode-wise functional of `y_S` that intertwines `B` with the transport is passive.** -/
theorem passive_of_L (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbT : ENNReal.ofReal b < Ty) (L : Mode → V3 →L[ℂ] ℂ)
    (hB : ∀ u, 0 ≤ u → ENNReal.ofReal u < Ty → ∀ k,
      L k (Bsym (corrSlow r g y u) (corrSlow r g y u) k) =
        advC (corrSlow r g y u) (fun k => L k (corrSlow r g y u k)) k)
    (hR : ∀ z : Field, IsReal z → ∀ k, L (-k) (z (-k)) = conj (L k (z k))) :
    Passive a b (corrSlow r g y) (fun t k => L k (corrSlow r g y t k))
      (fun t k => L k (corrRes r g y t k)) := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hsub : Icc a b ⊆ Icc 0 b := Icc_subset_Icc_left ha
  have hadm : ∀ t ∈ Icc a b, Adm 2 (corrSlow r g y t) := fun t ht =>
    corrSlow_adm h hr (ha.trans ht.1) (lt_lifespan ht.2 hbT)
  have hrhs : ∀ t ∈ Icc a b, ∀ k, rhsP (corrSlow r g y) (fun t k => L k (corrSlow r g y t k))
      (fun t k => L k (corrRes r g y t k)) t k =
      L k ((-(absSq k : ℝ) : ℂ) • corrSlow r g y t k + corrForce r g y t k) := fun t ht k => by
    have e := hB t (ha.trans ht.1) (lt_lifespan ht.2 hbT) k
    simp only [rhsP, map_add, map_smul, corrForce, Pi.sub_apply, map_sub, smul_eq_mul, ← e]
    ring
  refine ⟨hab, fun t ht k => hR _ (hadm t ht).real k, fun t ht => (hadm t ht).sol, ?_, ?_, ?_⟩
  · intro k i
    have h1 := (continuousOn_corr_mode h hr hb0 hbT k).mono hsub
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_continuousOn h1
  · intro k t ht
    have h1 := (corrSlow_mode h hr hb0 hbT k (hsub ht)).mono hsub
    have h2 : HasDerivWithinAt (fun s => L k (corrSlow r g y s k))
        (L k ((-(absSq k : ℝ) : ℂ) • corrSlow r g y t k + corrForce r g y t k)) (Icc a b) t :=
      ((L k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t h1
    rw [hrhs t ht k]
    exact h2
  · intro k
    have h1 : ContinuousOn (fun t => L k ((-(absSq k : ℝ) : ℂ) • corrSlow r g y t k +
        corrForce r g y t k)) (Icc a b) :=
      (L k).continuous.comp_continuousOn
        (((((continuousOn_corr_mode h hr hb0 hbT k).mono hsub).const_smul
          ((-(absSq k : ℝ) : ℂ))).add
          ((continuousOn_corrForce_mode h hr hb0 hbT k).mono hsub)))
    exact h1.congr fun t ht => hrhs t ht k

/-- The vertical component of `y_S` is passive, with source the vertical part of `corrRes`. -/
theorem passive_vert (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    Passive a b (corrSlow r g y) (fun t => GN.cmp (corrSlow r g y t) 2)
      (fun t => GN.cmp (corrRes r g y t) 2) :=
  passive_of_L h hr ha hab hbT vertC
    (fun u hu huT k => cmp_Bsym_two (corrSlow_adm h hr hu huT) (PiS_corrSlow r g y u) k)
    (fun z hz k => by
      change (z (-k)) 2 = conj ((z k) 2)
      rw [hz k]
      rfl)

/-- The vorticity of `y_S` is passive, with source the curl of `corrRes`. -/
theorem passive_curl (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    Passive a b (corrSlow r g y) (fun t => wC (corrSlow r g y t))
      (fun t => wC (corrRes r g y t)) :=
  passive_of_L h hr ha hab hbT curlL
    (fun u hu huT k => wC_Bsym (corrSlow_adm h hr hu huT) (PiS_corrSlow r g y u) k)
    (fun z hz k => by
      rw [curlL_apply, curlL_apply, hz k]
      simp only [conjV, Pi.neg_apply, Int.cast_neg, map_mul, map_sub, Complex.conj_I, map_intCast]
      ring)

end Actual

end OVNS.Quant.Slow
