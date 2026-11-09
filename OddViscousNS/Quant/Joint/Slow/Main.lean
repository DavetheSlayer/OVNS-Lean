import OddViscousNS.Quant.Joint.Slow.Large

/-!
# E7-P: `SlowCapsJoint`

The assembly of the chain of `Joint/Slow/Plan.lean`.

`SlowBudget` is the role of the slow threshold: it pays `∫ ‖corrRes‖₁² ≤ 4φ² + 4` on intervals of
length `≤ 2` where the caps hold.  `corrRes_budget` is that statement at `budgetPoly`, which is
above `Q` at the joint caps (the re-budget is step J4).  `slowCapsJoint_of_budget` needs no other
property of the threshold, but the floor of `slowCorr_le`.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter

noncomputable section

namespace OVNS.Quant.Slow

/-- **The role of the slow threshold.** -/
def SlowBudget (R₀ : ℝ) (q : ℝ → ℝ → Caps → ℝ) : Prop :=
  ∀ X R : ℝ, JDom R₀ X R → ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞),
    ActualSol X (R - X) r g y Ty → ∀ (caps : Caps) (s t : ℝ), 0 ≤ s → s ≤ t →
      ENNReal.ofReal t < Ty → t - s ≤ 2 → q X R caps ≤ |r| → OnPrefix caps r g y s t →
      (∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 4 * (R - X) ^ 2 + 4

/-- `budgetPoly` pays the role of the slow threshold (above `Q` at the joint caps). -/
theorem slowBudget_budgetPoly (R₀ : ℝ) :
    SlowBudget R₀ fun X R caps ↦ budgetPoly (R - X) caps :=
  fun _ _ _ _ _ _ _ h _ _ _ hs hst ht hlen hthr hP ↦ corrRes_budget h hs hst ht hlen hthr hP

/-- The slow levels `L₀, …, L₄`. -/
def slowL : Fin 5 → ℝ := ![10, 10, 200, 200, 4300]

/-- The constant of the slow caps. -/
def slowC : ℝ := 10 ^ 11 * (1 + c4)

lemma one_le_slowC : 1 ≤ slowC := by
  have := c4_pos
  unfold slowC
  nlinarith

lemma levels_zero (e : ℝ) : levelsJ slowL e 0 = 10 := by simp [levelsJ, slowL]
lemma levels_one (e : ℝ) : levelsJ slowL e 1 = 10 := by simp [levelsJ, slowL]
lemma levels_two (e : ℝ) : levelsJ slowL e 2 = 200 * e := by simp [levelsJ, slowL]
lemma levels_three (e : ℝ) : levelsJ slowL e 3 = 200 * e := by simp [levelsJ, slowL]
lemma levels_four (e : ℝ) : levelsJ slowL e 4 = 4300 * e := by simp [levelsJ, slowL]

/-! ### The common bounds on `[a, t]`, `a = max 0 (s − 1)` -/

section Piece

variable {X R r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps} {s t : ℝ}

lemma continuous_norms (hsol : ActualSol X (R - X) r g y Ty) (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t < Ty) {a : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fastNorm 2 r g y) (Icc a t) ∧ ContinuousOn (slowNorm 2 r g y) (Icc a t) := by
  obtain ⟨-, h2, -, h4, -⟩ := norms_continuous hsol ht0 ht
  exact ⟨h2.mono (Icc_subset_Icc_left ha), h4.mono (Icc_subset_Icc_left ha)⟩

/-- The budget on `[a, t]`, across the seam at `s`. -/
lemma piece_budget {R₀ : ℝ} {q : ℝ → ℝ → Caps → ℝ} (hb : SlowBudget R₀ q) (hdom : JDom R₀ X R)
    (hsol : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0) (hP : PieceHyp 4 (q X R) r g y Ty caps s t)
    (hH : OnPrefix caps r g y (max 0 (s - 1)) s) :
    (∫ u in (max 0 (s - 1))..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 24 * R ^ 2 := by
  set a := max 0 (s - 1) with ha
  have ha0 : 0 ≤ a := le_max_left _ _
  have has : a ≤ s := max_le hP.hs (by linarith)
  have hst := hP.hst
  have hs0 := hP.hs
  have ht := hP.ht
  have hsa : s - a ≤ 2 := by
    have : s - 1 ≤ a := le_max_right _ _
    linarith
  set m : ℝ := (s + t) / 2 with hm
  have hsm : s ≤ m := by simp only [hm]; linarith
  have hmt : m ≤ t := by simp only [hm]; linarith
  have hlen1 : m - s ≤ 2 := by
    have := hP.len
    simp only [hm]
    linarith
  have hlen2 : t - m ≤ 2 := by
    have := hP.len
    simp only [hm]
    linarith
  obtain ⟨hf, hS⟩ := continuous_norms hsol (hs0.trans hst) ht hs0
  have h1 := hb X R hdom r g y Ty hsol caps a s ha0 has (lt_lifespan hst ht) hsa hP.thr hH
  have h2 := hb X R hdom r g y Ty hsol caps s m hs0 hsm (lt_lifespan hmt ht) hlen1 hP.thr
    (onPrefix_restrict hP.onPrefix le_rfl hsm hmt hf hS)
  have h3 := hb X R hdom r g y Ty hsol caps m t (hs0.trans hsm) hmt ht hlen2 hP.thr
    (onPrefix_restrict hP.onPrefix hsm hmt le_rfl hf hS)
  have i1 := intervalIntegrable_corrRes_sq hsol hr ha0 has (lt_lifespan hst ht)
  have i2 := intervalIntegrable_corrRes_sq hsol hr hs0 hsm (lt_lifespan hmt ht)
  have i3 := intervalIntegrable_corrRes_sq hsol hr (hs0.trans hsm) hmt ht
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hXR := hdom.X_le_R
  have hX0 : 0 < X := by linarith [hdom.one_lt_X]
  have e : (∫ u in a..t, hnorm 1 (corrRes r g y u) ^ 2) =
      (∫ u in a..s, hnorm 1 (corrRes r g y u) ^ 2) +
      (∫ u in s..m, hnorm 1 (corrRes r g y u) ^ 2) +
      ∫ u in m..t, hnorm 1 (corrRes r g y u) ^ 2 := by
    rw [intervalIntegral.integral_add_adjacent_intervals i1 i2,
      intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3]
  rw [e]
  have h4 : 4 * (R - X) ^ 2 + 4 ≤ 8 * R ^ 2 := by nlinarith
  linarith

/-- The trace of the corrector on `[a, t]`. -/
lemma piece_trace (hsol : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0) {q : Caps → ℝ}
    (hfl : 2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 ≤ q caps)
    (hP : PieceHyp 4 q r g y Ty caps s t)
    (hH : OnPrefix caps r g y (max 0 (s - 1)) s) :
    ∀ u ∈ Icc (max 0 (s - 1)) t, hnorm 2 (slowCorr r g y u) ≤ delta0 := by
  intro u hu
  have hth := hfl.trans hP.thr
  have hu0 : 0 ≤ u := (le_max_left _ _).trans hu.1
  have huT := lt_lifespan hu.2 hP.ht
  rcases le_total u s with h | h
  · exact slowCorr_le hsol hr hu0 huT ((hH.1 u ⟨hu.1, h⟩).2.1.trans (le_cp _)) hth
  · exact slowCorr_le hsol hr hu0 huT ((hP.onPrefix.1 u ⟨h, hu.2⟩).2.1.trans (le_cp _)) hth

/-- The outputs of the `L²` stage. -/
structure L2Out (r : ℝ) (g : Field) (y : ℝ → Field) (a t R : ℝ) : Prop where
  y0 : ∀ u ∈ Icc a t, hnorm 0 (corrSlow r g y u) ^ 2 ≤ 145 * R ^ 2
  h1 : ∀ u ∈ Icc a t, hnorm 1 (PiH (corrSlow r g y u)) ^ 2 ≤ 145 * R ^ 2
  Iz : ∀ u₁ u₂, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
    (∫ u in u₁..u₂, hnorm 1 (corrSlow r g y u) ^ 2) ≤ 169 * R ^ 2
  Ih : ∀ u₁ u₂, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
    (∫ u in u₁..u₂, hnorm 2 (PiH (corrSlow r g y u)) ^ 2) ≤ 169 * R ^ 2
  y1 : ∀ u ∈ Icc (a + 1) t, hnorm 0 (corrSlow r g y u) ^ 2 ≤ 97 * R ^ 2
  h2 : ∀ u ∈ Icc (a + 1) t, hnorm 1 (PiH (corrSlow r g y u)) ^ 2 ≤ 97 * R ^ 2

/-- **The `L²` stage.** -/
theorem l2_out (hsol : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0) {a : ℝ} (ha : 0 ≤ a)
    (hat : a ≤ t) (ht : ENNReal.ofReal t < Ty)
    (hE : (∫ u in a..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 24 * R ^ 2)
    (h0 : hnorm 0 (corrSlow r g y a) ^ 2 ≤ 121 * R ^ 2)
    (h1 : hnorm 1 (PiH (corrSlow r g y a)) ^ 2 ≤ 121 * R ^ 2) : L2Out r g y a t R := by
  have ht0 : 0 ≤ t := ha.trans hat
  have hsub0 : Icc a t ⊆ Icc 0 t := Icc_subset_Icc_left ha
  have hadm : ∀ u ∈ Icc a t, Adm 2 (corrSlow r g y u) := fun u hu =>
    corrSlow_adm hsol hr (ha.trans hu.1) (lt_lifespan hu.2 ht)
  have hfi := intervalIntegrable_corrRes_sq hsol hr ha hat ht
  have pS : HeatPair 0 a t (corrSlow r g y) (corrForce r g y) :=
    (heatPair_corrSlow hsol hr (Or.inl rfl) ht0 ht).mono ha le_rfl
  have pH : HeatPair 1 a t (fun u => PiH (corrSlow r g y u)) (fun u => PiH (corrForce r g y u)) :=
    (heatPair_corrH hsol hr (Or.inr (Or.inl rfl)) ht0 ht).mono ha le_rfl
  have iS : IntervalIntegrable (fun u => hnorm 1 (corrSlow r g y u) ^ 2) volume a t := by
    have := pS.intervalIntegrable_dissipation hat
    rwa [zero_add] at this
  have iH : IntervalIntegrable (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) volume a t := by
    have := pH.intervalIntegrable_dissipation hat
    rwa [one_add_one_eq_two] at this
  obtain ⟨hS1, hS2, hS3⟩ := l2_stage (x := fun u => hnorm 0 (corrSlow r g y u) ^ 2)
    (d := fun u => hnorm 1 (corrSlow r g y u) ^ 2) hat (fun _ => sq_nonneg _)
    (fun _ => sq_nonneg _)
    (fun u hu => pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_mono (by norm_num)
      ((hadm u hu).inH.mono (by norm_num))) 2)
    ((continuousOn_corr_sq hsol hr (Or.inl rfl) ht0 ht).mono hsub0) iS hfi hE
    (fun u₁ u₂ h1 h2 h3 => corr_l2_law' hsol hr (ha.trans h1) h2 (lt_lifespan h3 ht))
  obtain ⟨hH1, hH2, hH3⟩ := l2_stage (x := fun u => hnorm 1 (PiH (corrSlow r g y u)) ^ 2)
    (d := fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) hat (fun _ => sq_nonneg _)
    (fun _ => sq_nonneg _)
    (fun u hu => pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_mono (by norm_num)
      (hadm u hu).inH.PiH) 2)
    ((continuousOn_corrH_sq hsol hr (Or.inr (Or.inl rfl)) ht0 ht).mono hsub0) iH hfi hE
    (fun u₁ u₂ h1 h2 h3 => corr_horiz_law' hsol hr (ha.trans h1) h2 (lt_lifespan h3 ht))
  have hy0 : ∀ u ∈ Icc a t, hnorm 0 (corrSlow r g y u) ^ 2 ≤ 145 * R ^ 2 := fun u hu => by
    have := hS1 u hu
    linarith
  have hh1 : ∀ u ∈ Icc a t, hnorm 1 (PiH (corrSlow r g y u)) ^ 2 ≤ 145 * R ^ 2 := fun u hu => by
    have := hH1 u hu
    linarith
  refine ⟨hy0, hh1, fun u₁ u₂ h1 h2 h3 => ?_, fun u₁ u₂ h1 h2 h3 => ?_, fun u hu => ?_,
    fun u hu => ?_⟩
  · have h4 := hS2 u₁ u₂ h1 h2 h3
    have h5 := hy0 u₁ ⟨h1, h2.trans h3⟩
    have h6 : 0 ≤ hnorm 0 (corrSlow r g y u₂) ^ 2 := sq_nonneg _
    linarith
  · have h4 := hH2 u₁ u₂ h1 h2 h3
    have h5 := hh1 u₁ ⟨h1, h2.trans h3⟩
    have h6 : 0 ≤ hnorm 1 (PiH (corrSlow r g y u₂)) ^ 2 := sq_nonneg _
    linarith
  · have h4 := hS3 u hu
    have h5 := hy0 (u - 1) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    linarith [sq_nonneg R]
  · have h4 := hH3 u hu
    have h5 := hh1 (u - 1) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    linarith [sq_nonneg R]

/-! ### The strain on the piece -/

lemma StrainOn.mono_D {a b : ℝ} {q : ℕ} {D D' : ℝ} (h : StrainOn r g y a b q D) (hD : 0 ≤ D)
    (hDD : D ≤ D') : StrainOn r g y a b q D' := fun u hu => by
  filter_upwards [h u hu] with N hN i j hi hj
  exact (hN i j hi hj).trans (pow_le_pow_left₀ hD hDD _)

lemma strainD_le (m : ℕ) {P R' : ℝ} (hR : 0 ≤ R') (hP : P ≤ Pstar m) :
    rK (2 ^ m) * Real.sqrt (P * R' ^ 2) ≤ Kn m * R' := by
  have hK : 0 ≤ rK (2 ^ m) := by
    have := one_le_rK (2 ^ m)
    linarith
  have h1 : Real.sqrt (P * R' ^ 2) ≤ Real.sqrt (Pstar m) * R' := by
    refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hP (sq_nonneg R'))).trans ?_
    rw [Real.sqrt_mul (by have := one_le_Pstar m; linarith), Real.sqrt_sq hR]
  calc _ ≤ rK (2 ^ m) * (Real.sqrt (Pstar m) * R') := mul_le_mul_of_nonneg_left h1 hK
    _ = Kn m * R' := by simp only [Kn]; ring

/-- The start of the chain. -/
def b0 (s : ℝ) : ℝ := if 1 ≤ s then s else 0

lemma Pstar_ge_one (m : ℕ) : piM 6 m * 400 ≤ Pstar m := by
  have : 0 ≤ Real.exp 6 * (2 * (piM 1 m * 8) + 201 * 2 ^ m * 400) := by
    have := one_le_piM (T := 1) (by norm_num) m
    positivity
  unfold Pstar
  linarith

lemma Pstar_ge_two (m : ℕ) :
    Real.exp 6 * (2 * (piM 1 m * 8) + 201 * 2 ^ m * 400) ≤ Pstar m := by
  have : 0 ≤ piM 6 m * 400 := by
    have := one_le_piM (T := 6) (by norm_num) m
    positivity
  unfold Pstar
  linarith

/-- **The strain on `[b₀, t]`.** -/
theorem piece_strain (hsol : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0) (hs0 : 0 ≤ s)
    (hst : s ≤ t) (hlen : t - s ≤ 4) (ht : ENNReal.ofReal t < Ty) (hR1 : 1 ≤ R)
    (hE : (∫ u in (max 0 (s - 1))..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 24 * R ^ 2)
    (hL : L2Out r g y (max 0 (s - 1)) t R)
    (hz0 : s < 1 → hnorm 2 (corrSlow r g y 0) ^ 2 ≤ 4 * R ^ 2) (m : ℕ) :
    StrainOn r g y (b0 s) t (2 ^ m) (Kn m * R) := by
  have hR0 : 0 ≤ R := by linarith
  have hY : 0 < 400 * R ^ 2 := by positivity
  by_cases h1 : 1 ≤ s
  · have ha : max 0 (s - 1) = s - 1 := max_eq_right (by linarith)
    rw [ha] at hE hL
    simp only [b0, h1, ↓reduceIte]
    have h2 := strain_generic hsol hr (a := s - 1) (by linarith) (by linarith) ht (T := 6)
      (Y := 400 * R ^ 2) (by linarith) (by norm_num) hY
      (fun u hu => (hL.h1 u hu).trans (by nlinarith [sq_nonneg R])) (by linarith) m
    rw [sub_add_cancel] at h2
    refine h2.mono_D (by have := one_le_rK (2 ^ m); positivity) ?_
    have e : piM 6 m * (400 * R ^ 2) = piM 6 m * 400 * R ^ 2 := by ring
    rw [e]
    exact strainD_le m hR0 (Pstar_ge_one m)
  · have ha : max 0 (s - 1) = 0 := max_eq_left (by linarith)
    rw [ha] at hE hL
    simp only [b0, h1, ↓reduceIte]
    have hs1 : s < 1 := not_le.1 h1
    have hz := hz0 hs1
    have ht0 : 0 ≤ t := hs0.trans hst
    have hzA := corrSlow_adm hsol hr le_rfl ((ENNReal.ofReal_le_ofReal ht0).trans_lt ht)
    have h3 : hnorm 2 (PiH (corrSlow r g y 0)) ^ 2 ≤ 4 * R ^ 2 :=
      (pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_PiH_le' hzA.inH) 2).trans hz
    have h4 : hnorm 1 (PiH (corrSlow r g y 0)) ^ 2 ≤ hnorm 2 (PiH (corrSlow r g y 0)) ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_mono (by norm_num) hzA.inH.PiH) 2
    have h2 := strain_zero hsol hr ht0 ht (T := 6) (Y := 400 * R ^ 2) (Y' := 8 * R ^ 2)
      (by linarith) hY (by positivity) (by linarith) (by nlinarith [sq_nonneg R])
      (by linarith) m
    refine h2.mono_D (by have := one_le_rK (2 ^ m); positivity) ?_
    have e : Real.exp 6 * (2 * (piM 1 m * (8 * R ^ 2)) + 201 * 2 ^ m * (400 * R ^ 2)) =
        Real.exp 6 * (2 * (piM 1 m * 8) + 201 * 2 ^ m * 400) * R ^ 2 := by ring
    rw [e]
    exact strainD_le m hR0 (Pstar_ge_two m)

/-! ### The start levels and the numbers -/

lemma delta0_le_one : delta0 ≤ 1 := by norm_num [delta0]

lemma delta0_nonneg : 0 ≤ delta0 := by norm_num [delta0]

lemma rpow_three_half_sq {R : ℝ} (hR : 0 ≤ R) : (R ^ ((3 : ℝ) / 2)) ^ 2 = R ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hR]
  norm_num

/-- The start levels at `b₀`, for the corrected field. -/
lemma start_levels (hsol : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) {e₀ : ℝ} (he : 1 ≤ e₀) (hR : 1 ≤ R)
    (hlev : SlowLevel (levelsJ slowL (e₀ ^ 2)) R slowExpHA r g y b)
    (htr : hnorm 2 (slowCorr r g y b) ≤ delta0) :
    hnorm 0 (corrSlow r g y b) ^ 2 ≤ 121 * R ^ 2 ∧
    hnorm 1 (PiH (corrSlow r g y b)) ^ 2 ≤ 121 * R ^ 2 ∧
    hnorm 1 (PiV (corrSlow r g y b)) ^ 2 ≤ 40401 * e₀ ^ 4 * R ^ 3 ∧
    hnorm 2 (PiH (corrSlow r g y b)) ^ 2 ≤ 40401 * e₀ ^ 4 * R ^ 4 ∧
    hnorm 2 (PiV (corrSlow r g y b)) ^ 2 ≤ 18498601 * e₀ ^ 4 * R ^ 4 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hlev
  rw [levels_zero] at h0
  rw [levels_one] at h1
  rw [levels_two] at h2
  rw [levels_three] at h3
  rw [levels_four] at h4
  have e3 : R ^ slowExpHA.eA = R ^ ((3 : ℝ) / 2) := rfl
  have e4 : R ^ slowExpHA.eB = R ^ 2 := by
    change R ^ (2 : ℝ) = R ^ 2
    exact Real.rpow_two R
  rw [e3] at h3
  rw [e4] at h4
  have hR0 : 0 ≤ R := by linarith
  set r3 : ℝ := R ^ ((3 : ℝ) / 2) with hr3
  have hr30 : 0 ≤ r3 := Real.rpow_nonneg hR0 _
  have hr3s : r3 ^ 2 = R ^ 3 := rpow_three_half_sq hR0
  have hr31 : 1 ≤ r3 := Real.one_le_rpow hR (by norm_num)
  have hd := delta0_le_one
  have hz : Adm 2 (corrSlow r g y b) := corrSlow_adm hsol hr hb hbT
  have hee : 1 ≤ e₀ ^ 2 := one_le_pow₀ he
  have s0 := (slowNorm_le_corr hsol hr hb hbT (σ := 0) (by norm_num)).2
  have s1 := (slowNorm_le_corr hsol hr hb hbT (σ := 1) (by norm_num)).2
  have s2 := (slowNorm_le_corr hsol hr hb hbT (σ := 2) le_rfl).2
  have t1 := (horizNorm_le_corr hsol hr hb hbT (σ := 1) (by norm_num)).2
  have t2 := (horizNorm_le_corr hsol hr hb hbT (σ := 2) le_rfl).2
  have v1 : hnorm 1 (PiV (corrSlow r g y b)) ≤ hnorm 1 (corrSlow r g y b) :=
    hnorm_PiV_le' (hz.inH.mono (by norm_num))
  have v2 : hnorm 2 (PiV (corrSlow r g y b)) ≤ hnorm 2 (corrSlow r g y b) :=
    hnorm_PiV_le' hz.inH
  have hR2 : (1 : ℝ) ≤ R ^ 2 := one_le_pow₀ hR
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h : hnorm 0 (corrSlow r g y b) ≤ 11 * R := by linarith
    calc _ ≤ (11 * R) ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) h 2
      _ = _ := by ring
  · have h : hnorm 1 (PiH (corrSlow r g y b)) ≤ 11 * R := by linarith
    calc _ ≤ (11 * R) ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) h 2
      _ = _ := by ring
  · have h : hnorm 1 (PiV (corrSlow r g y b)) ≤ 201 * e₀ ^ 2 * r3 := by
      have : 1 ≤ e₀ ^ 2 * r3 := by nlinarith
      nlinarith
    calc _ ≤ (201 * e₀ ^ 2 * r3) ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) h 2
      _ = 40401 * e₀ ^ 4 * r3 ^ 2 := by ring
      _ = _ := by rw [hr3s]
  · have h : hnorm 2 (PiH (corrSlow r g y b)) ≤ 201 * e₀ ^ 2 * R ^ 2 := by
      have : 1 ≤ e₀ ^ 2 * R ^ 2 := by nlinarith
      nlinarith
    calc _ ≤ (201 * e₀ ^ 2 * R ^ 2) ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) h 2
      _ = _ := by ring
  · have h : hnorm 2 (PiV (corrSlow r g y b)) ≤ 4301 * e₀ ^ 2 * R ^ 2 := by
      have : 1 ≤ e₀ ^ 2 * R ^ 2 := by nlinarith
      nlinarith
    calc _ ≤ (4301 * e₀ ^ 2 * R ^ 2) ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) h 2
      _ = _ := by ring

/-! ### The piece -/

lemma a_nonneg' (s : ℝ) : 0 ≤ max 0 (s - 1) := le_max_left _ _

lemma split_sq (hsol : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0) {u σ : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hσ : σ ≤ 2) :
    hnorm σ (corrSlow r g y u) ^ 2 = hnorm σ (PiH (corrSlow r g y u)) ^ 2 +
      hnorm σ (PiV (corrSlow r g y u)) ^ 2 := by
  have hz := corrSlow_adm hsol hr hu huT
  have e := hnorm_sq_split_slow (hz.inH.mono hσ)
  rwa [PiS_corrSlow] at e

/-- The hypotheses of the assembly, with the fast side and the threshold discharged. -/
structure PieceData (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞) (s t R e₀ : ℝ) : Prop where
  hs : 0 ≤ s
  hst : s ≤ t
  hlen : t - s ≤ 4
  ht : ENNReal.ofReal t < Ty
  hR : 1 ≤ R
  he : 1 ≤ e₀
  trace : ∀ u ∈ Icc (max 0 (s - 1)) t, hnorm 2 (slowCorr r g y u) ≤ delta0
  budget : (∫ u in (max 0 (s - 1))..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 24 * R ^ 2
  level : ∀ u ∈ Icc (max 0 (s - 1)) s, SlowLevel (levelsJ slowL (e₀ ^ 2)) R slowExpHA r g y u
  zero : s < 1 → hnorm 2 (corrSlow r g y 0) ^ 2 ≤ 4 * R ^ 2

namespace PieceData

variable {e₀ : ℝ} (hD : PieceData r g y Ty s t R e₀) (hsol : ActualSol X (R - X) r g y Ty)
  (hr : r ≠ 0)
include hD

lemma a_le_s : max 0 (s - 1) ≤ s := max_le hD.hs (by linarith)

lemma le_b0 : max 0 (s - 1) ≤ b0 s := by
  unfold b0
  split_ifs with h
  · exact hD.a_le_s
  · exact le_of_eq (max_eq_left (by linarith [not_le.1 h]))

lemma b0_le : b0 s ≤ s := by
  unfold b0
  split_ifs with h
  · exact le_rfl
  · exact hD.hs

lemma b0_nonneg : 0 ≤ b0 s := by
  unfold b0
  split_ifs with h
  · exact hD.hs
  · exact le_rfl

lemma le_b0_add : b0 s + 1 ≤ s + 1 := by linarith [hD.b0_le]

include hsol hr

lemma start : hnorm 0 (corrSlow r g y (max 0 (s - 1))) ^ 2 ≤ 121 * R ^ 2 ∧
    hnorm 1 (PiH (corrSlow r g y (max 0 (s - 1)))) ^ 2 ≤ 121 * R ^ 2 := by
  have ha := hD.a_le_s
  have h := start_levels hsol hr (a_nonneg' s) (lt_lifespan (ha.trans hD.hst) hD.ht) hD.he hD.hR
    (hD.level _ ⟨le_rfl, ha⟩) (hD.trace _ ⟨le_rfl, ha.trans hD.hst⟩)
  exact ⟨h.1, h.2.1⟩

lemma l2 : L2Out r g y (max 0 (s - 1)) t R :=
  l2_out hsol hr (a_nonneg' s) (hD.a_le_s.trans hD.hst) hD.ht hD.budget
    (hD.start hsol hr).1 (hD.start hsol hr).2

lemma strain (m : ℕ) : StrainOn r g y (b0 s) t (2 ^ m) (Kn m * R) :=
  piece_strain hsol hr hD.hs hD.hst hD.hlen hD.ht hD.hR hD.budget (hD.l2 hsol hr) hD.zero m

/-- The chain on `[b₀, t]`, at the strain of the levels `n`, `n + 1`. -/
lemma chain {n : ℕ} {Λ : ℝ} (hΛ1 : 1 ≤ Λ) (hΛR : Λ ≤ e₀ * R)
    (hDΛ : (KK n * R) ^ (2 ^ n) ≤ Λ ^ (2 ^ n - 1)) :
    ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R ∧
    (∀ u₁ u₂, b0 s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → (∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2) ≤
      20000000000 * e₀ ^ 6 * (R ^ 4 + (u₂ - u₁) * R ^ 5)) := by
  have hR := hD.hR
  have hR0 : 0 ≤ R := by linarith
  have hK0 : 0 ≤ KK n := by have := one_le_KK n; linarith
  have hb₀ := hD.b0_nonneg
  have hab := hD.le_b0
  have hb₀t : b0 s ≤ t := hD.b0_le.trans hD.hst
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hSn : StrainOn r g y (b0 s) t (2 ^ n) (KK n * R) :=
    (hD.strain hsol hr n).mono_D (by have := one_le_Kn n; positivity)
      (mul_le_mul_of_nonneg_right (by have := one_le_Kn (n + 1); unfold KK; linarith) hR0)
  have hSn2 : StrainOn r g y (b0 s) t (2 * 2 ^ n) (KK n * R) := by
    have e : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [pow_succ']
    rw [e]
    exact (hD.strain hsol hr (n + 1)).mono_D (by have := one_le_Kn (n + 1); positivity)
      (mul_le_mul_of_nonneg_right (by have := one_le_Kn n; unfold KK; linarith) hR0)
  have hL := hD.l2 hsol hr
  have hE : (∫ u in (b0 s)..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 24 * R ^ 2 :=
    (intervalIntegral.integral_mono_interval hab hb₀t le_rfl
      (Eventually.of_forall fun _ => sq_nonneg _)
      (intervalIntegrable_corrRes_sq hsol hr (a_nonneg' s) (hD.a_le_s.trans hD.hst) hD.ht)).trans
      hD.budget
  have hst := start_levels hsol hr hb₀ (lt_lifespan hb₀t hD.ht) hD.he hR
    (hD.level _ ⟨hab, hD.b0_le⟩) (hD.trace _ ⟨hab, hb₀t⟩)
  have hC := chain_core hsol hr hb₀ hb₀t hD.ht hq hΛ1 (by positivity) hR hD.he hΛR hSn hSn2 hDΛ hE
    (fun u₁ u₂ h1 h2 h3 => hL.Iz u₁ u₂ (hab.trans h1) h2 h3)
    (fun u₁ u₂ h1 h2 h3 => hL.Ih u₁ u₂ (hab.trans h1) h2 h3)
    hst.2.2.1 hst.2.2.2.1 hst.2.2.2.2
  exact ⟨hC, fun u₁ u₂ h1 h2 h3 => chain_clip hsol hr hb₀ hD.ht hq hΛ1 (by positivity) hR hD.he hΛR
    hSn hSn2 hDΛ hE hC h1 h2 h3⟩

/-- `‖y_S‖₂² ≤ B₂` on all of `[a, t]`. -/
lemma z2_le (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R) :
    ∀ u ∈ Icc (max 0 (s - 1)) t, hnorm 2 (corrSlow r g y u) ^ 2 ≤ 39075001 * e₀ ^ 6 * R ^ 4 := by
  intro u hu
  have hu0 : 0 ≤ u := (a_nonneg' s).trans hu.1
  have huT := lt_lifespan hu.2 hD.ht
  have hR := hD.hR
  have he := hD.he
  have m46 : e₀ ^ 4 * R ^ 4 ≤ e₀ ^ 6 * R ^ 4 := mono_pow_mul he hR (by norm_num) le_rfl
  have m56 : e₀ ^ 5 * R ^ 4 ≤ e₀ ^ 6 * R ^ 4 := mono_pow_mul he hR (by norm_num) le_rfl
  rw [split_sq hsol hr hu0 huT le_rfl]
  rcases le_total u (b0 s) with h | h
  · have hb := hD.b0_le
    have hst := start_levels hsol hr hu0 huT he hR (hD.level u ⟨hu.1, h.trans hb⟩)
      (hD.trace u hu)
    have h1 := hst.2.2.2.1
    have h2 := hst.2.2.2.2
    nlinarith
  · have h1 := hC.bh u ⟨h, hu.2⟩
    have h2 := hC.bv u ⟨h, hu.2⟩
    nlinarith

/-- The vertical part in `L^{2q}`, in the explicit box. -/
lemma vert_box {B2 : ℝ} (hB20 : 0 ≤ B2)
    (hB : ∀ u ∈ Icc (max 0 (s - 1)) t, hnorm 2 (corrSlow r g y u) ^ 2 ≤ B2) {N : ℕ} (hN : 1 ≤ N)
    (hF : 6 * (errK * B2 ^ 2 / N ^ 2) ≤ 352 * R ^ 2) (n : ℕ) :
    ∀ u ∈ Icc s t, mP (2 ^ n) (polyOf (slowBox (2 * N)) (GN.cmp (corrSlow r g y u) 2)) ≤
      (Pstar n * R ^ 2) ^ (2 ^ n) := by
  have hR := hD.hR
  have hR0 : 0 ≤ R := by linarith
  have hE := hD.budget
  have hL := hD.l2 hsol hr
  have hY : 0 < 400 * R ^ 2 := by positivity
  intro u hu
  by_cases h1 : 1 ≤ s
  · have ha : max 0 (s - 1) = s - 1 := max_eq_right (by linarith)
    rw [ha] at hE hL hB
    have hlen := hD.hlen
    have h2 := vert_moser_box hsol hr (a := s - 1) (b := t) (by linarith) (by linarith [hD.hst])
      hD.ht hN (T := 6) (Y := 400 * R ^ 2) (B2 := B2) (by linarith) (by norm_num) hY hB20 hB
      (by linarith) (fun v hv => (hL.y0 v hv).trans (by nlinarith [sq_nonneg R])) n u
      ⟨by
        have : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
        linarith [hu.1], hu.2⟩
    refine h2.trans (pow_le_pow_left₀ (by have := one_le_piM (T := 6) (by norm_num) n; positivity)
      ?_ _)
    have := Pstar_ge_one n
    nlinarith [sq_nonneg R]
  · have ha : max 0 (s - 1) = 0 := max_eq_left (by linarith)
    rw [ha] at hE hL hB
    have hs1 : s < 1 := not_le.1 h1
    have ht0 : 0 ≤ t := hD.hs.trans hD.hst
    have hz := hD.zero hs1
    have hzA := corrSlow_adm hsol hr le_rfl ((ENNReal.ofReal_le_ofReal ht0).trans_lt hD.ht)
    have h3 : hnorm 1 (corrSlow r g y 0) ^ 2 ≤ hnorm 2 (corrSlow r g y 0) ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_mono (by norm_num) hzA.inH) 2
    have h4 : hnorm 0 (corrSlow r g y 0) ^ 2 ≤ hnorm 1 (corrSlow r g y 0) ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_mono (by norm_num)
        (hzA.inH.mono (by norm_num))) 2
    have hlen := hD.hlen
    have hs0 := hD.hs
    have h2 := vert_zero_box hsol hr ht0 hD.ht hN (T := 6) (Y := 400 * R ^ 2)
      (Y' := 8 * R ^ 2) (B2 := B2) (by linarith) (by positivity) hB20 hB (by linarith)
      (by nlinarith [sq_nonneg R]) (by linarith) n u ⟨hs0.trans hu.1, hu.2⟩
    refine h2.trans (pow_le_pow_left₀ (by
      have := one_le_piM (T := 1) (by norm_num) n
      positivity) ?_ _)
    have := Pstar_ge_two n
    have e : Real.exp 6 * (2 * (piM 1 n * (8 * R ^ 2)) + 201 * 2 ^ n * (400 * R ^ 2)) =
        Real.exp 6 * (2 * (piM 1 n * 8) + 201 * 2 ^ n * 400) * R ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right this (sq_nonneg R)

end PieceData

/-- The norms of the slow field at a time. -/
structure Norms (r : ℝ) (g : Field) (y : ℝ → Field) (u R e₀ r3 : ℝ) : Prop where
  s0 : slowNorm 0 r g y u ≤ 14 * R
  h1 : horizNorm 1 r g y u ≤ 14 * R
  h2 : horizNorm 2 r g y u ≤ 275 * e₀ ^ 2 * R ^ 2
  s1 : slowNorm 1 r g y u ≤ 276 * e₀ ^ 2 * r3
  s2 : slowNorm 2 r g y u ≤ 6253 * e₀ ^ 3 * R ^ 2

lemma le_of_sq_le' {x b : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ^ 2 ≤ b ^ 2) : x ≤ b :=
  (pow_le_pow_iff_left₀ hx hb two_ne_zero).1 h

namespace PieceData

variable {e₀ : ℝ} (hD : PieceData r g y Ty s t R e₀) (hsol : ActualSol X (R - X) r g y Ty)
  (hr : r ≠ 0)
include hD hsol hr

/-- The norms on the piece. -/
lemma norms (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R) :
    ∀ u ∈ Icc s t, Norms r g y u R e₀ (R ^ ((3 : ℝ) / 2)) := by
  intro u hu
  have hR := hD.hR
  have he := hD.he
  have hR0 : 0 ≤ R := by linarith
  have hu0 : 0 ≤ u := hD.hs.trans hu.1
  have huT := lt_lifespan hu.2 hD.ht
  have hua : u ∈ Icc (max 0 (s - 1)) t := ⟨hD.a_le_s.trans hu.1, hu.2⟩
  have hub : u ∈ Icc (b0 s) t := ⟨hD.b0_le.trans hu.1, hu.2⟩
  have hL := hD.l2 hsol hr
  have htr := hD.trace u hua
  have hd := delta0_le_one
  set r3 : ℝ := R ^ ((3 : ℝ) / 2) with hr3
  have hr30 : 0 ≤ r3 := Real.rpow_nonneg hR0 _
  have hr3s : r3 ^ 2 = R ^ 3 := rpow_three_half_sq hR0
  have hr31 : 1 ≤ r3 := Real.one_le_rpow hR (by norm_num)
  have hee : 1 ≤ e₀ ^ 2 := one_le_pow₀ he
  have heee : 1 ≤ e₀ ^ 3 := one_le_pow₀ he
  have hR2 : (1 : ℝ) ≤ R ^ 2 := one_le_pow₀ hR
  have s0 := (slowNorm_le_corr hsol hr hu0 huT (σ := 0) (by norm_num)).1
  have s1 := (slowNorm_le_corr hsol hr hu0 huT (σ := 1) (by norm_num)).1
  have s2 := (slowNorm_le_corr hsol hr hu0 huT (σ := 2) le_rfl).1
  have t1 := (horizNorm_le_corr hsol hr hu0 huT (σ := 1) (by norm_num)).1
  have t2 := (horizNorm_le_corr hsol hr hu0 huT (σ := 2) le_rfl).1
  have hz0 : hnorm 0 (corrSlow r g y u) ≤ 13 * R := le_of_sq_le' (hnorm_nonneg _ _)
    (by positivity) ((hL.y0 u hua).trans (by nlinarith [sq_nonneg R]))
  have hh1 : hnorm 1 (PiH (corrSlow r g y u)) ≤ 13 * R := le_of_sq_le' (hnorm_nonneg _ _)
    (by positivity) ((hL.h1 u hua).trans (by nlinarith [sq_nonneg R]))
  have hh2 : hnorm 2 (PiH (corrSlow r g y u)) ≤ 274 * e₀ ^ 2 * R ^ 2 := by
    refine le_of_sq_le' (hnorm_nonneg _ _) (by positivity) ((hC.bh u hub).trans ?_)
    have e : (274 * e₀ ^ 2 * R ^ 2) ^ 2 = 75076 * (e₀ ^ 4 * R ^ 4) := by ring
    rw [e]
    have : 0 ≤ e₀ ^ 4 * R ^ 4 := by positivity
    linarith
  have hz1 : hnorm 1 (corrSlow r g y u) ≤ 275 * e₀ ^ 2 * r3 := by
    refine le_of_sq_le' (hnorm_nonneg _ _) (by positivity) ?_
    rw [split_sq hsol hr hu0 huT (by norm_num)]
    have e : (275 * e₀ ^ 2 * r3) ^ 2 = 75625 * (e₀ ^ 4 * R ^ 3) := by
      rw [mul_pow, mul_pow, hr3s]
      ring
    rw [e]
    have h1 := hL.h1 u hua
    have h2 := hC.av u hub
    have h3 : R ^ 2 ≤ e₀ ^ 4 * R ^ 3 := by
      have := mono_pow_mul he hR (a := 0) (b := 4) (c := 2) (d := 3) (by norm_num) (by norm_num)
      simpa using this
    have h4 : 0 ≤ e₀ ^ 4 * R ^ 3 := by positivity
    linarith
  have hz2 : hnorm 2 (corrSlow r g y u) ≤ 6252 * e₀ ^ 3 * R ^ 2 := by
    refine le_of_sq_le' (hnorm_nonneg _ _) (by positivity)
      ((hD.z2_le hsol hr hC u hua).trans ?_)
    have e : (6252 * e₀ ^ 3 * R ^ 2) ^ 2 = 39087504 * (e₀ ^ 6 * R ^ 4) := by ring
    rw [e]
    have : 0 ≤ e₀ ^ 6 * R ^ 4 := by positivity
    linarith
  have h1R : 1 ≤ e₀ ^ 2 * R ^ 2 := by nlinarith
  have h2R : 1 ≤ e₀ ^ 3 * R ^ 2 := by nlinarith
  have h3R : 1 ≤ e₀ ^ 2 * r3 := by nlinarith
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

omit hr in
/-- The Wiener norm from the slow norms, with the log. -/
lemma wiener_le' (hlg : 1 + Real.log (⌈R ^ 2⌉₊ : ℝ) ≤ e₀ ^ 2) {u : ℝ} (hu0 : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (h2 : slowNorm 2 r g y u ≤ 6253 * e₀ ^ 3 * R ^ 2) :
    slowWiener r g y u ≤ 4 * e₀ * slowNorm 1 r g y u + 25012 * e₀ ^ 3 := by
  have hR := hD.hR
  have he := hD.he
  have hx := (actual_adm hsol hu0 huT).PiS
  have hN : 1 ≤ ⌈R ^ 2⌉₊ := by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
    have := Nat.ceil_eq_zero.1 h0
    have h1 : (1 : ℝ) ≤ R ^ 2 := one_le_pow₀ hR
    linarith
  have hw := wiener_log_le hx.inH (fun k hk => by simp [PiS, hk]) hx.mean hN
  have hs : Real.sqrt (1 + Real.log (⌈R ^ 2⌉₊ : ℝ)) ≤ e₀ := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ e₀)]
    exact Real.sqrt_le_sqrt hlg
  have hN1 : R ^ 2 ≤ (⌈R ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hR2 : 0 < R ^ 2 := by positivity
  have hN0 : (0 : ℝ) < (⌈R ^ 2⌉₊ : ℝ) := by linarith
  have h3 : 4 * hnorm 2 (PiS (actual r g y u)) / (⌈R ^ 2⌉₊ : ℝ) ≤ 25012 * e₀ ^ 3 := by
    rw [div_le_iff₀ hN0]
    have h4 : hnorm 2 (PiS (actual r g y u)) ≤ 6253 * e₀ ^ 3 * R ^ 2 := h2
    have h5 : 0 ≤ e₀ ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hN1 h5]
  have h4 : 4 * Real.sqrt (1 + Real.log (⌈R ^ 2⌉₊ : ℝ)) * hnorm 1 (PiS (actual r g y u)) ≤
      4 * e₀ * hnorm 1 (PiS (actual r g y u)) :=
    mul_le_mul_of_nonneg_right (by linarith) (hnorm_nonneg _ _)
  change wiener (PiS (actual r g y u)) ≤ 4 * e₀ * hnorm 1 (PiS (actual r g y u)) + _
  linarith

omit hsol hr in
/-- `b_h` past the first unit. -/
lemma regain_h2 (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R) {v : ℝ}
    (hv : v ∈ Icc (s + 1) t) : hnorm 2 (PiH (corrSlow r g y v)) ≤ 188 * e₀ ^ 2 * R ^ 2 := by
  have hR := hD.hR
  have he := hD.he
  have hR0 : 0 ≤ R := by linarith
  have hb := hD.b0_le
  have hvb2 : v ∈ Icc (b0 s + 1 / 2) t := ⟨by linarith [hv.1], hv.2⟩
  refine le_of_sq_le' (hnorm_nonneg _ _) (by positivity) ((hC.bh1 v hvb2).trans ?_)
  have e : (188 * e₀ ^ 2 * R ^ 2) ^ 2 = 35344 * (e₀ ^ 4 * R ^ 4) := by ring
  rw [e]
  have := mono_pow_mul he hR (a := 1) (b := 4) (c := 3) (d := 4) (by norm_num) (by norm_num)
  simp only [pow_one] at this
  have h1 : 0 ≤ e₀ * R ^ 3 := by positivity
  linarith

/-- `a` past the first unit. -/
lemma regain_z1 (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R) {v : ℝ}
    (hv : v ∈ Icc (s + 1) t) : hnorm 1 (corrSlow r g y v) ≤ 188 * e₀ ^ 2 * R ^ ((3 : ℝ) / 2) := by
  have hR := hD.hR
  have he := hD.he
  have hR0 : 0 ≤ R := by linarith
  have hs0 := hD.hs
  have hv0 : 0 ≤ v := by linarith [hv.1]
  have hvT := lt_lifespan hv.2 hD.ht
  have hab := hD.a_le_s
  have hb := hD.b0_le
  have hL := hD.l2 hsol hr
  have hva : v ∈ Icc (max 0 (s - 1) + 1) t := ⟨by linarith [hv.1], hv.2⟩
  have hvb2 : v ∈ Icc (b0 s + 1 / 2) t := ⟨by linarith [hv.1], hv.2⟩
  set r3 : ℝ := R ^ ((3 : ℝ) / 2) with hr3
  have hr30 : 0 ≤ r3 := Real.rpow_nonneg hR0 _
  have hr3s : r3 ^ 2 = R ^ 3 := rpow_three_half_sq hR0
  refine le_of_sq_le' (hnorm_nonneg _ _) (by positivity) ?_
  rw [split_sq hsol hr hv0 hvT (by norm_num)]
  have e : (188 * e₀ ^ 2 * r3) ^ 2 = 35344 * (e₀ ^ 4 * R ^ 3) := by
    rw [mul_pow, mul_pow, hr3s]
    ring
  rw [e]
  have h1 := hL.h2 v hva
  have h2 := hC.av1 v hvb2
  have h3 : R ^ 2 ≤ e₀ ^ 4 * R ^ 3 := by
    have := mono_pow_mul he hR (a := 0) (b := 4) (c := 2) (d := 3) (by norm_num) (by norm_num)
    simpa using this
  have h4 : e₀ * R ^ 3 ≤ e₀ ^ 4 * R ^ 3 := by
    have := mono_pow_mul he hR (a := 1) (b := 4) (c := 3) (d := 3) (by norm_num) le_rfl
    simpa using this
  have h5 : 0 ≤ e₀ ^ 4 * R ^ 3 := by positivity
  nlinarith

/-- `b` past the first unit. -/
lemma regain_z2 (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R) {v : ℝ}
    (hv : v ∈ Icc (s + 1) t) : hnorm 2 (corrSlow r g y v) ≤ 4247 * e₀ ^ 2 * R ^ 2 := by
  have hR := hD.hR
  have he := hD.he
  have hR0 : 0 ≤ R := by linarith
  have hs0 := hD.hs
  have hv0 : 0 ≤ v := by linarith [hv.1]
  have hvT := lt_lifespan hv.2 hD.ht
  have hb := hD.b0_le
  have hvb1 : v ∈ Icc (b0 s + 1) t := ⟨by linarith [hv.1], hv.2⟩
  have hvb2 : v ∈ Icc (b0 s + 1 / 2) t := ⟨by linarith [hv.1], hv.2⟩
  refine le_of_sq_le' (hnorm_nonneg _ _) (by positivity) ?_
  rw [split_sq hsol hr hv0 hvT le_rfl]
  have e : (4247 * e₀ ^ 2 * R ^ 2) ^ 2 = 18037009 * (e₀ ^ 4 * R ^ 4) := by ring
  rw [e]
  have h1 := hC.bh1 v hvb2
  have h2 := hC.bv1 v hvb1
  have h3 : e₀ * R ^ 3 ≤ e₀ ^ 4 * R ^ 4 := by
    have := mono_pow_mul he hR (a := 1) (b := 4) (c := 3) (d := 4) (by norm_num) (by norm_num)
    simpa using this
  have h4 : e₀ ^ 2 * R ^ 4 ≤ e₀ ^ 4 * R ^ 4 := mono_pow_mul he hR (by norm_num) le_rfl
  have h5 : 0 ≤ e₀ ^ 4 * R ^ 4 := by positivity
  nlinarith

/-- **The levels are regained past the first unit.** -/
lemma regain (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R) :
    ∀ v ∈ Icc (s + 1) t, SlowLevel (levelsJ slowL (e₀ ^ 2)) R slowExpHA r g y v := by
  intro v hv
  have hR := hD.hR
  have he := hD.he
  have hR0 : 0 ≤ R := by linarith
  have hv0 : 0 ≤ v := by linarith [hv.1, hD.hs]
  have hvT := lt_lifespan hv.2 hD.ht
  have hab := hD.a_le_s
  have hL := hD.l2 hsol hr
  have hd := delta0_le_one
  have htr := hD.trace v ⟨by linarith [hv.1], hv.2⟩
  have hva : v ∈ Icc (max 0 (s - 1) + 1) t := ⟨by linarith [hv.1], hv.2⟩
  have hr31 : 1 ≤ R ^ ((3 : ℝ) / 2) := Real.one_le_rpow hR (by norm_num)
  have hR2 : (1 : ℝ) ≤ R ^ 2 := one_le_pow₀ hR
  have hee : 1 ≤ e₀ ^ 2 := one_le_pow₀ he
  have hz0 : hnorm 0 (corrSlow r g y v) ≤ 985 / 100 * R := le_of_sq_le' (hnorm_nonneg _ _)
    (by positivity) ((hL.y1 v hva).trans (by nlinarith [sq_nonneg R]))
  have hh1 : hnorm 1 (PiH (corrSlow r g y v)) ≤ 985 / 100 * R := le_of_sq_le' (hnorm_nonneg _ _)
    (by positivity) ((hL.h2 v hva).trans (by nlinarith [sq_nonneg R]))
  have hh2 := hD.regain_h2 hC hv
  have hz1 := hD.regain_z1 hsol hr hC hv
  have hz2 := hD.regain_z2 hsol hr hC hv
  have s0 := (slowNorm_le_corr hsol hr hv0 hvT (σ := 0) (by norm_num)).1
  have s1 := (slowNorm_le_corr hsol hr hv0 hvT (σ := 1) (by norm_num)).1
  have s2 := (slowNorm_le_corr hsol hr hv0 hvT (σ := 2) le_rfl).1
  have t1 := (horizNorm_le_corr hsol hr hv0 hvT (σ := 1) (by norm_num)).1
  have t2 := (horizNorm_le_corr hsol hr hv0 hvT (σ := 2) le_rfl).1
  have hd0 : delta0 ≤ 1 / 100 := by norm_num [delta0]
  have h1R : 1 ≤ e₀ ^ 2 * R ^ 2 := by nlinarith
  have h3R : 1 ≤ e₀ ^ 2 * R ^ ((3 : ℝ) / 2) := by nlinarith
  have e4 : R ^ slowExpHA.eB = R ^ 2 := by
    change R ^ (2 : ℝ) = R ^ 2
    exact Real.rpow_two R
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [levels_zero]
    linarith
  · rw [levels_one]
    linarith
  · rw [levels_two]
    linarith
  · rw [levels_three]
    change _ ≤ 200 * e₀ ^ 2 * R ^ ((3 : ℝ) / 2)
    linarith
  · rw [levels_four, e4]
    linarith

/-- `J_S`. -/
lemma J_le (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R) :
    (∫ u in s..t, slowNorm 2 r g y u ^ 2) ≤ 150400 * e₀ ^ 4 * R ^ 3 := by
  have hR := hD.hR
  have he := hD.he
  have hst := hD.hst
  have hs0 := hD.hs
  have ht0 : 0 ≤ t := hs0.trans hst
  have hL := hD.l2 hsol hr
  have hsub : Icc s t ⊆ Icc 0 t := Icc_subset_Icc_left hs0
  have hcS : ContinuousOn (fun u => slowNorm 2 r g y u ^ 2) (Icc s t) :=
    ((norms_continuous hsol ht0 hD.ht).2.2.2.1.mono hsub).pow 2
  have hcH : ContinuousOn (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrH_sq hsol hr (Or.inr (Or.inr rfl)) ht0 hD.ht).mono hsub
  have hcV : ContinuousOn (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2) (Icc 0 t) :=
    continuousOn_corrV_sq hsol hr (Or.inr (Or.inr rfl)) ht0 hD.ht
  have hiV := (hcV.mono hsub).intervalIntegrable_of_Icc (μ := volume) hst
  have hR1 : IntervalIntegrable (fun u => 2 * (hnorm 2 (PiH (corrSlow r g y u)) ^ 2 +
      hnorm 2 (PiV (corrSlow r g y u)) ^ 2) + 2) volume s t :=
    (((hcH.intervalIntegrable_of_Icc hst).add hiV).const_mul 2).add
      (intervalIntegrable_const (μ := volume))
  have h1 := intervalIntegral.integral_mono_on hst (hcS.intervalIntegrable_of_Icc hst) hR1
    fun u hu => by
      have hu0 : 0 ≤ u := hs0.trans hu.1
      have huT := lt_lifespan hu.2 hD.ht
      have h2 := (slowNorm_le_corr hsol hr hu0 huT (σ := 2) le_rfl).1
      have h3 := hD.trace u ⟨hD.a_le_s.trans hu.1, hu.2⟩
      have h4 := delta0_le_one
      have h5 : slowNorm 2 r g y u ≤ hnorm 2 (corrSlow r g y u) + 1 := by linarith
      have h6 : 0 ≤ slowNorm 2 r g y u := hnorm_nonneg _ _
      have h7 := split_sq hsol hr hu0 huT (σ := 2) le_rfl
      have h8 := hnorm_nonneg 2 (corrSlow r g y u)
      nlinarith [sq_nonneg (hnorm 2 (corrSlow r g y u) - 1)]
  refine h1.trans ?_
  rw [intervalIntegral.integral_add (((hcH.intervalIntegrable_of_Icc hst).add hiV).const_mul 2)
    (intervalIntegrable_const (μ := volume)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hcH.intervalIntegrable_of_Icc hst) hiV,
    intervalIntegral.integral_const, smul_eq_mul]
  have h2 := hL.Ih s t (hD.a_le_s) hst le_rfl
  have h3 : (∫ u in s..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2) ≤
      ∫ u in (b0 s)..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 :=
    intervalIntegral.integral_mono_interval hD.b0_le hst le_rfl
      (Eventually.of_forall fun _ => sq_nonneg _)
      ((hcV.mono (Icc_subset_Icc_left hD.b0_nonneg)).intervalIntegrable_of_Icc
        (hD.b0_le.trans hst))
  have h4 := hC.Jv
  have hlen := hD.hlen
  have h5 : R ^ 2 ≤ e₀ ^ 4 * R ^ 3 := by
    have := mono_pow_mul he hR (a := 0) (b := 4) (c := 2) (d := 3) (by norm_num) (by norm_num)
    simpa using this
  have h6 : 1 ≤ e₀ ^ 4 * R ^ 3 := by
    have := mono_pow_mul he hR (a := 0) (b := 4) (c := 0) (d := 3) (by norm_num) (by norm_num)
    simpa using this
  have e : 150400 * e₀ ^ 4 * R ^ 3 = 150400 * (e₀ ^ 4 * R ^ 3) := by ring
  have e' : 75000 * e₀ ^ 4 * R ^ 3 = 75000 * (e₀ ^ 4 * R ^ 3) := by ring
  rw [e]
  rw [e'] at h4
  nlinarith

/-- The unit histories of `a_S`, `W_S` (the slot `kin`). -/
lemma kin_le (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R)
    (hlg : 1 + Real.log (⌈R ^ 2⌉₊ : ℝ) ≤ e₀ ^ 2) {u₁ u₂ : ℝ} (h1 : s ≤ u₁) (h2 : u₁ ≤ u₂)
    (h3 : u₂ ≤ t) (hl : u₂ - u₁ ≤ 1) :
    (∫ u in u₁..u₂, slowNorm 1 r g y u ^ 2) ≤ 340 * R ^ 2 ∧
      (∫ u in u₁..u₂, slowWiener r g y u ^ 2) ≤
        32 * e₀ ^ 2 * (340 * R ^ 2) + 1251200288 * e₀ ^ 6 := by
  have hs0 := hD.hs
  have ht0 : 0 ≤ t := hs0.trans hD.hst
  have hR := hD.hR
  have he := hD.he
  have hL := hD.l2 hsol hr
  have hsub0 : Icc u₁ u₂ ⊆ Icc 0 t := Icc_subset_Icc (hs0.trans h1) h3
  have hsub : Icc u₁ u₂ ⊆ Icc s t := Icc_subset_Icc h1 h3
  obtain ⟨-, -, c1, -, c3, -⟩ := norms_continuous hsol ht0 hD.ht
  have hc1 : ContinuousOn (fun u => slowNorm 1 r g y u ^ 2) (Icc u₁ u₂) := (c1.mono hsub0).pow 2
  have hc3 : ContinuousOn (fun u => slowWiener r g y u ^ 2) (Icc u₁ u₂) := (c3.mono hsub0).pow 2
  have hcz : ContinuousOn (fun u => hnorm 1 (corrSlow r g y u) ^ 2) (Icc u₁ u₂) :=
    (continuousOn_corr_sq hsol hr (Or.inr (Or.inl rfl)) ht0 hD.ht).mono hsub0
  have hiz := hcz.intervalIntegrable_of_Icc (μ := volume) h2
  have hi1 := hc1.intervalIntegrable_of_Icc (μ := volume) h2
  have hb : (∫ u in u₁..u₂, slowNorm 1 r g y u ^ 2) ≤ 340 * R ^ 2 := by
    have hR1 : IntervalIntegrable (fun u => 2 * hnorm 1 (corrSlow r g y u) ^ 2 + 2) volume u₁ u₂ :=
      (hiz.const_mul 2).add (intervalIntegrable_const (μ := volume))
    have h4 := intervalIntegral.integral_mono_on h2 hi1 hR1 fun u hu => by
      have hu0 : 0 ≤ u := (hsub0 hu).1
      have huT := lt_lifespan (hu.2.trans h3) hD.ht
      have h5 := (slowNorm_le_corr hsol hr hu0 huT (σ := 1) (by norm_num)).1
      have h6 := hD.trace u ⟨hD.a_le_s.trans (hsub hu).1, (hsub hu).2⟩
      have h7 := delta0_le_one
      have h8 : slowNorm 1 r g y u ≤ hnorm 1 (corrSlow r g y u) + 1 := by linarith
      have h9 : 0 ≤ slowNorm 1 r g y u := hnorm_nonneg _ _
      nlinarith [sq_nonneg (hnorm 1 (corrSlow r g y u) - 1)]
    refine h4.trans ?_
    rw [intervalIntegral.integral_add (hiz.const_mul 2) (intervalIntegrable_const (μ := volume)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    have h5 := hL.Iz u₁ u₂ (hD.a_le_s.trans h1) h2 h3
    nlinarith [one_le_pow₀ (n := 2) hR]
  refine ⟨hb, ?_⟩
  have hb2 := hC
  have hNo := hD.norms hsol hr hC
  have hR2 : IntervalIntegrable (fun u => 32 * e₀ ^ 2 * slowNorm 1 r g y u ^ 2 +
      1251200288 * e₀ ^ 6) volume u₁ u₂ :=
    (hi1.const_mul _).add (intervalIntegrable_const (μ := volume))
  have h4 := intervalIntegral.integral_mono_on h2 (hc3.intervalIntegrable_of_Icc h2) hR2
    fun u hu => by
      have hu0 : 0 ≤ u := (hsub0 hu).1
      have huT := lt_lifespan (hu.2.trans h3) hD.ht
      have h5 := hD.wiener_le' hsol hlg hu0 huT (hNo u (hsub hu)).s2
      have h6 : 0 ≤ slowWiener r g y u := wiener_nonneg _
      have h7 : 0 ≤ 4 * e₀ * slowNorm 1 r g y u + 25012 * e₀ ^ 3 := by
        have : 0 ≤ slowNorm 1 r g y u := hnorm_nonneg _ _
        positivity
      have h8 := pow_le_pow_left₀ h6 h5 2
      refine h8.trans ?_
      nlinarith [sq_nonneg (4 * e₀ * slowNorm 1 r g y u - 25012 * e₀ ^ 3)]
  refine h4.trans ?_
  rw [intervalIntegral.integral_add (hi1.const_mul _) (intervalIntegrable_const (μ := volume)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
  have h5 : 0 ≤ e₀ ^ 2 := by positivity
  have h6 : 0 ≤ e₀ ^ 6 := by positivity
  have h7 := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 32 * e₀ ^ 2)
  have h8 : (u₂ - u₁) * (1251200288 * e₀ ^ 6) ≤ 1 * (1251200288 * e₀ ^ 6) :=
    mul_le_mul_of_nonneg_right hl (by positivity)
  linarith

omit hD hsol hr in
/-- The explicit box of the sup bound. -/
lemma box_choice {e₀ R : ℝ} {n : ℕ} (he : 1 ≤ e₀) (hcn : cN * e₀ ^ 6 ≤ R)
    (hq : (2 : ℝ) ^ n ≤ R) (hp6 : R ^ 6 ≤ e₀ ^ (2 ^ n)) (h5R : 5 ≤ R) :
    ∃ N : ℕ, 1 ≤ N ∧ 6 * (errK * (39075001 * e₀ ^ 6 * R ^ 4) ^ 2 / N ^ 2) ≤ 352 * R ^ 2 ∧
      4 * ((2 ^ n : ℕ) : ℝ) * N + 1 ≤ e₀ ^ (2 ^ n) ∧ 12504 * e₀ ^ 3 * R ^ 2 ≤ N := by
  have hR : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have he0 : 0 < e₀ := by linarith
  have herr := errK_nonneg
  have hcN : 10 ^ 8 * (1 + errK) = cN := rfl
  have hcN1 : (12504 : ℝ) ≤ cN := by rw [← hcN]; nlinarith
  set Nr : ℝ := cN * e₀ ^ 6 * R ^ 3 with hNr
  have hNge : Nr ≤ (⌈Nr⌉₊ : ℝ) := Nat.le_ceil _
  have hNr0 : 0 ≤ Nr := by
    simp only [hNr]
    have : 0 ≤ cN := by linarith
    positivity
  have hNlt : (⌈Nr⌉₊ : ℝ) < Nr + 1 := Nat.ceil_lt_add_one hNr0
  have hNr1 : 12504 * e₀ ^ 3 * R ^ 2 ≤ Nr := by
    have h3 : e₀ ^ 3 ≤ e₀ ^ 6 := pow_le_pow_right₀ he (by norm_num)
    have h4 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
    calc 12504 * e₀ ^ 3 * R ^ 2 ≤ cN * e₀ ^ 6 * R ^ 3 := by gcongr
      _ = Nr := rfl
  have hNr2 : (1 : ℝ) ≤ Nr := by
    have h1 : (1 : ℝ) ≤ e₀ ^ 3 * R ^ 2 := by
      have := mono_pow_mul he hR (a := 0) (b := 3) (c := 0) (d := 2) (by norm_num) (by norm_num)
      simpa using this
    nlinarith
  refine ⟨⌈Nr⌉₊, ?_, ?_, ?_, hNr1.trans hNge⟩
  · have : (1 : ℝ) ≤ (⌈Nr⌉₊ : ℝ) := hNr2.trans hNge
    exact_mod_cast this
  · have hN0 : (0 : ℝ) < (⌈Nr⌉₊ : ℝ) := by linarith
    have hN2 : Nr ^ 2 ≤ (⌈Nr⌉₊ : ℝ) ^ 2 := pow_le_pow_left₀ hNr0 hNge 2
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    have e1 : (39075001 * e₀ ^ 6 * R ^ 4) ^ 2 = 39075001 ^ 2 * (e₀ ^ 12 * R ^ 8) := by ring
    have e2 : R ^ 2 * Nr ^ 2 = cN ^ 2 * (e₀ ^ 12 * R ^ 8) := by simp only [hNr]; ring
    have h2 : 6 * errK * 39075001 ^ 2 ≤ 352 * cN ^ 2 := by
      rw [← hcN]
      nlinarith [sq_nonneg errK]
    have h3 : 0 ≤ e₀ ^ 12 * R ^ 8 := by positivity
    have h1 : 6 * (errK * (39075001 * e₀ ^ 6 * R ^ 4) ^ 2) ≤ 352 * R ^ 2 * Nr ^ 2 := by
      rw [e1, mul_assoc 352, e2]
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_left hN2 (by positivity))
  · refine le_trans ?_ hp6
    push_cast
    have h1 : (⌈Nr⌉₊ : ℝ) ≤ R ^ 4 + 1 := by
      have h2 : Nr ≤ R * R ^ 3 := by
        simp only [hNr]
        exact mul_le_mul_of_nonneg_right hcn (by positivity)
      have e : R * R ^ 3 = R ^ 4 := by ring
      linarith
    have h2 : 4 * (2 : ℝ) ^ n * (⌈Nr⌉₊ : ℝ) ≤ 4 * R * (R ^ 4 + 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num)) h1 (by positivity) (by positivity)
    have h3 : R ^ 6 = R * R ^ 5 := by ring
    have h4 : (5 : ℝ) ^ 5 ≤ R ^ 5 := pow_le_pow_left₀ (by norm_num) h5R 5
    have h5 : 0 < R ^ 5 := by positivity
    have e : 4 * R * (R ^ 4 + 1) = 4 * R ^ 5 + 4 * R := by ring
    nlinarith

/-- The Wiener norm of the horizontal part. -/
lemma wiener_h_le (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R)
    (hlg : 1 + Real.log (⌈R ^ 2⌉₊ : ℝ) ≤ e₀ ^ 2) {u : ℝ} (hu : u ∈ Icc s t) :
    wiener (PiH (corrSlow r g y u)) ≤ 52 * e₀ * R + 1096 * e₀ ^ 2 := by
  have hR := hD.hR
  have he := hD.he
  have hR0 : 0 < R := by linarith
  have he0 : 0 < e₀ := by linarith
  have hu0 : 0 ≤ u := hD.hs.trans hu.1
  have huT := lt_lifespan hu.2 hD.ht
  have hua : u ∈ Icc (max 0 (s - 1)) t := ⟨hD.a_le_s.trans hu.1, hu.2⟩
  have hub : u ∈ Icc (b0 s) t := ⟨hD.b0_le.trans hu.1, hu.2⟩
  have hL := hD.l2 hsol hr
  have hz := corrSlow_adm hsol hr hu0 huT
  have hHa := admPiH hz
  have hNp : 1 ≤ ⌈R ^ 2⌉₊ := by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
    have := Nat.ceil_eq_zero.1 h0
    have h1 : (1 : ℝ) ≤ R ^ 2 := one_le_pow₀ hR
    linarith
  have hw := wiener_log_le hHa.inH (fun k hk => PiH_fast _ hk) hHa.mean hNp
  have hs : Real.sqrt (1 + Real.log (⌈R ^ 2⌉₊ : ℝ)) ≤ e₀ := by
    rw [← Real.sqrt_sq he0.le]
    exact Real.sqrt_le_sqrt hlg
  have hh1 : hnorm 1 (PiH (corrSlow r g y u)) ≤ 13 * R := le_of_sq_le' (hnorm_nonneg _ _)
    (by positivity) ((hL.h1 u hua).trans (by nlinarith [sq_nonneg R]))
  have hh2 : hnorm 2 (PiH (corrSlow r g y u)) ≤ 274 * e₀ ^ 2 * R ^ 2 := by
    refine le_of_sq_le' (hnorm_nonneg _ _) (by positivity) ((hC.bh u hub).trans ?_)
    have e : (274 * e₀ ^ 2 * R ^ 2) ^ 2 = 75076 * (e₀ ^ 4 * R ^ 4) := by ring
    rw [e]
    have : 0 ≤ e₀ ^ 4 * R ^ 4 := by positivity
    linarith
  have hN1' : R ^ 2 ≤ (⌈R ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hR2 : 0 < R ^ 2 := by positivity
  have hN0' : (0 : ℝ) < (⌈R ^ 2⌉₊ : ℝ) := by linarith
  have h3 : 4 * hnorm 2 (PiH (corrSlow r g y u)) / (⌈R ^ 2⌉₊ : ℝ) ≤ 1096 * e₀ ^ 2 := by
    rw [div_le_iff₀ hN0']
    have h5 : 0 ≤ e₀ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hN1' h5]
  have h4 : 4 * Real.sqrt (1 + Real.log (⌈R ^ 2⌉₊ : ℝ)) * hnorm 1 (PiH (corrSlow r g y u)) ≤
      4 * e₀ * (13 * R) :=
    mul_le_mul (by linarith) hh1 (hnorm_nonneg _ _) (by positivity)
  linarith

omit hD hsol hr in
lemma sqrt_Pstar_le {n : ℕ} {R e₀ : ℝ} (hR : 0 ≤ R) (hK : KK n ≤ e₀) :
    Real.sqrt (Pstar n * R ^ 2) ≤ e₀ * R := by
  have hPs := one_le_Pstar n
  rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hR]
  have h1 : Real.sqrt (Pstar n) ≤ Kn n := by
    have h2 := one_le_rK (2 ^ n)
    have h3 : 0 ≤ Real.sqrt (Pstar n) := Real.sqrt_nonneg _
    unfold Kn
    nlinarith
  have h2 : Kn n ≤ KK n := by
    have := one_le_Kn (n + 1)
    unfold KK
    linarith
  exact mul_le_mul_of_nonneg_right (h1.trans (h2.trans hK)) hR

/-- **The physical maximum.** -/
lemma sup_le (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R) {n : ℕ}
    (hK : KK n ≤ e₀) (hlg : 1 + Real.log (⌈R ^ 2⌉₊ : ℝ) ≤ e₀ ^ 2) (hcn : cN * e₀ ^ 6 ≤ R)
    (hq : (2 : ℝ) ^ n ≤ R) (hp6 : R ^ 6 ≤ e₀ ^ (2 ^ n)) (h5R : 5 ≤ R) :
    ∀ u ∈ Icc s t, slowSup r g y u ≤
      e₀ ^ 2 * R + 1 + 52 * e₀ * R + 1096 * e₀ ^ 2 + c4 := by
  intro u hu
  have hR := hD.hR
  have he := hD.he
  have hR0 : 0 < R := by linarith
  have he0 : 0 < e₀ := by linarith
  have hu0 : 0 ≤ u := hD.hs.trans hu.1
  have huT := lt_lifespan hu.2 hD.ht
  have hua : u ∈ Icc (max 0 (s - 1)) t := ⟨hD.a_le_s.trans hu.1, hu.2⟩
  have hz := corrSlow_adm hsol hr hu0 huT
  have hz' := PiS_corrSlow r g y u
  have hB := hD.z2_le hsol hr hC
  obtain ⟨N, hN1, hF, hΛq, hNbig⟩ := box_choice he hcn hq hp6 h5R
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hV := hD.vert_box hsol hr (by positivity) hB hN1 hF n u hu
  have hqn : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hPs := one_le_Pstar n
  have hsqrt := sqrt_Pstar_le (n := n) hR0.le hK
  have hz2 : hnorm 2 (corrSlow r g y u) ≤ 6252 * e₀ ^ 3 * R ^ 2 := by
    refine le_of_sq_le' (hnorm_nonneg _ _) (by positivity) ((hB u hua).trans ?_)
    have e : (6252 * e₀ ^ 3 * R ^ 2) ^ 2 = 39087504 * (e₀ ^ 6 * R ^ 4) := by ring
    rw [e]
    have : 0 ≤ e₀ ^ 6 * R ^ 4 := by positivity
    linarith
  have htail : 2 * hnorm 2 (corrSlow r g y u) / N ≤ 1 := by
    rw [div_le_one hN0]
    linarith
  have hW := hD.wiener_h_le hsol hr hC hlg hu
  have hphys : ∀ x, ‖physS (corrSlow r g y u) x‖ ≤
      e₀ ^ 2 * R + 1 + (52 * e₀ * R + 1096 * e₀ ^ 2) := fun x => by
    have h1 := norm_physS_le_of_poly hz hz' hqn hN1 (by positivity) he0.le hV hΛq x
    have h2 : e₀ * Real.sqrt (Pstar n * R ^ 2) ≤ e₀ * (e₀ * R) :=
      mul_le_mul_of_nonneg_left hsqrt he0.le
    have e : e₀ * (e₀ * R) = e₀ ^ 2 * R := by ring
    linarith
  have hSi : InH 2 (PiS (actual r g y u)) := (actual_adm hsol hu0 huT).PiS.inH
  have hRi := slowCorr_adm hsol hr hu0 huT
  have h1 := slowSup_le_corrected hSi hRi.inH hphys
  have h2 : wiener (slowCorr r g y u) ≤ c4 * hnorm 2 (slowCorr r g y u) := wiener_le hRi.mz
  have h3 := hD.trace u hua
  have h4 := delta0_le_one
  have hc := c4_pos
  have h5 : c4 * hnorm 2 (slowCorr r g y u) ≤ c4 * 1 :=
    mul_le_mul_of_nonneg_left (h3.trans h4) hc.le
  linarith

end PieceData

/-- The start of the true zero. -/
lemma zero_le (hsol : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0) (hXR : X ≤ R) (hR : 1 ≤ R)
    (hT : ENNReal.ofReal 0 < Ty) (htr : hnorm 2 (slowCorr r g y 0) ≤ delta0) :
    hnorm 2 (corrSlow r g y 0) ^ 2 ≤ 4 * R ^ 2 := by
  have h1 := (slowNorm_le_corr hsol hr le_rfl hT (σ := 2) le_rfl).2
  have e : actual r g y 0 = y 0 := by simp [actual, psi_zero]
  have h2 : slowNorm 2 r g y 0 ≤ hnorm 2 (y 0) := by
    simp only [slowNorm, e]
    exact hnorm_PiS_le (hsol.sol.adm 0 le_rfl hT).inH
  have h3 := hsol.init_le
  have h4 := delta0_le_one
  have h5 : hnorm 2 (corrSlow r g y 0) ≤ 2 * R := by linarith
  calc _ ≤ (2 * R) ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) h5 2
    _ = _ := by ring

end Piece

/-! ### `SlowCapsJoint` -/

/-- The start of the domain. -/
def R₁ (R₀ : ℝ) : ℝ := max R₀ (max (Real.exp (Real.exp 16000)) (cN ^ 2))

lemma Ex_twelve (R : ℝ) : Ex 12 R = Ex 6 R ^ 2 := by
  rw [Ex_pow]
  simp only [Ex]
  congr 1
  push_cast
  ring

lemma Ex_thirtysix (R : ℝ) : Ex 36 R = Ex 6 R ^ 6 := by
  rw [Ex_pow]
  simp only [Ex]
  congr 1
  push_cast
  ring

/-- The numbers of the output. -/
lemma output_numbers {e₀ R : ℝ} (he : 1 ≤ e₀) (hR : 1 ≤ R) :
    (14 : ℝ) ≤ slowC * e₀ ^ 6 ∧ 275 * e₀ ^ 2 ≤ slowC * e₀ ^ 6 ∧ 276 * e₀ ^ 2 ≤ slowC * e₀ ^ 6 ∧
      6253 * e₀ ^ 3 ≤ slowC * e₀ ^ 6 ∧ 26116 * e₀ ^ 3 ≤ slowC * e₀ ^ 6 ∧
      20000000000 ≤ slowC ∧ 150400 * e₀ ^ 4 ≤ slowC * e₀ ^ 6 ∧
      e₀ ^ 2 * R + 1 + 52 * e₀ * R + 1096 * e₀ ^ 2 + c4 ≤ slowC * e₀ ^ 6 * R := by
  have hc := c4_pos
  have h6 : 1 ≤ e₀ ^ 6 := one_le_pow₀ he
  have hC : (10 : ℝ) ^ 11 ≤ slowC := by
    unfold slowC
    nlinarith
  have h26 : e₀ ^ 2 ≤ e₀ ^ 6 := pow_le_pow_right₀ he (by norm_num)
  have h36 : e₀ ^ 3 ≤ e₀ ^ 6 := pow_le_pow_right₀ he (by norm_num)
  have h46 : e₀ ^ 4 ≤ e₀ ^ 6 := pow_le_pow_right₀ he (by norm_num)
  have h16 : e₀ ≤ e₀ ^ 6 := by
    calc e₀ = e₀ ^ 1 := (pow_one _).symm
      _ ≤ e₀ ^ 6 := pow_le_pow_right₀ he (by norm_num)
  have hCe : (10 : ℝ) ^ 11 * e₀ ^ 6 ≤ slowC * e₀ ^ 6 :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by linarith, by
    nlinarith, ?_⟩
  have h1 : e₀ ^ 2 * R ≤ e₀ ^ 6 * R := mul_le_mul_of_nonneg_right h26 (by linarith)
  have h2 : e₀ * R ≤ e₀ ^ 6 * R := mul_le_mul_of_nonneg_right h16 (by linarith)
  have h3 : 1 ≤ e₀ ^ 6 * R := by nlinarith
  have h4 : e₀ ^ 2 ≤ e₀ ^ 6 * R := by nlinarith
  have e : slowC * e₀ ^ 6 * R = 10 ^ 11 * (e₀ ^ 6 * R) + 10 ^ 11 * c4 * (e₀ ^ 6 * R) := by
    unfold slowC
    ring
  rw [e]
  have h5 : c4 ≤ 10 ^ 11 * c4 * (e₀ ^ 6 * R) := by nlinarith
  nlinarith

lemma kin_numbers {e₀ R : ℝ} (he : 1 ≤ e₀) (hR : 1 ≤ R) :
    340 * R ^ 2 ≤ slowC * e₀ ^ 6 * R ^ 2 ∧
      32 * e₀ ^ 2 * (340 * R ^ 2) + 1251200288 * e₀ ^ 6 ≤ slowC * e₀ ^ 6 * R ^ 2 := by
  have hc := c4_pos
  have hC10 : (10 : ℝ) ^ 11 ≤ slowC := by
    unfold slowC
    nlinarith
  have h6' : (1 : ℝ) ≤ e₀ ^ 6 := one_le_pow₀ he
  have h26 : e₀ ^ 2 ≤ e₀ ^ 6 := pow_le_pow_right₀ he (by norm_num)
  have hRR2 : (1 : ℝ) ≤ R ^ 2 := one_le_pow₀ hR
  have hCe2 : (10 : ℝ) ^ 11 * e₀ ^ 6 ≤ slowC * e₀ ^ 6 :=
    mul_le_mul_of_nonneg_right hC10 (by positivity)
  have h11 : (10 : ℝ) ^ 11 * (e₀ ^ 6 * R ^ 2) ≤ slowC * e₀ ^ 6 * R ^ 2 := by
    have := mul_le_mul_of_nonneg_right hCe2 (by positivity : 0 ≤ R ^ 2)
    calc _ = (10 : ℝ) ^ 11 * e₀ ^ 6 * R ^ 2 := by ring
      _ ≤ _ := this
  have h10 : e₀ ^ 6 ≤ e₀ ^ 6 * R ^ 2 := by nlinarith
  have h12 : R ^ 2 ≤ e₀ ^ 6 * R ^ 2 := by nlinarith
  have h9 : 32 * e₀ ^ 2 * (340 * R ^ 2) ≤ 10880 * (e₀ ^ 6 * R ^ 2) := by
    have := mul_le_mul_of_nonneg_right h26 (by positivity : 0 ≤ R ^ 2)
    nlinarith
  have h0 : 0 ≤ e₀ ^ 6 * R ^ 2 := by positivity
  constructor
  · nlinarith
  · nlinarith

/-- The pointwise outputs of `SlowCapsJoint` from the chain. -/
lemma PieceData.caps_out {X R r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {s t e₀ : ℝ}
    (hD : PieceData r g y Ty s t R e₀) (hsol : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0)
    (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R)
    (hlg : 1 + Real.log (⌈R ^ 2⌉₊ : ℝ) ≤ e₀ ^ 2)
    (hsup : ∀ u ∈ Icc s t, slowSup r g y u ≤
      e₀ ^ 2 * R + 1 + 52 * e₀ * R + 1096 * e₀ ^ 2 + c4) :
    ∀ u ∈ Icc s t, SlowLevel (fun _ ↦ slowC * e₀ ^ 6) R slowExpHA r g y u ∧
      slowWiener r g y u ≤ slowC * e₀ ^ 6 * R ^ slowExpHA.eW ∧
      slowSup r g y u ≤ slowC * e₀ ^ 6 * R := by
  have he := hD.he
  have hR1 := hD.hR
  have hR0 : 0 < R := by linarith
  have hNo := hD.norms hsol hr hC
  obtain ⟨n1, n2, n3, n4, n5, -, -, n8⟩ := output_numbers he hR1
  set r3 : ℝ := R ^ ((3 : ℝ) / 2) with hr3
  have hr30 : 0 ≤ r3 := Real.rpow_nonneg hR0.le _
  have hr31 : 1 ≤ r3 := Real.one_le_rpow hR1 (by norm_num)
  have eB : R ^ slowExpHA.eB = R ^ 2 := by
    change R ^ (2 : ℝ) = R ^ 2
    exact Real.rpow_two R
  have eA : R ^ slowExpHA.eA = r3 := rfl
  have eW : R ^ slowExpHA.eW = r3 := rfl
  refine fun u hu => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (hNo u hu).s0.trans (mul_le_mul_of_nonneg_right n1 hR0.le)
  · exact (hNo u hu).h1.trans (mul_le_mul_of_nonneg_right n1 hR0.le)
  · exact (hNo u hu).h2.trans (mul_le_mul_of_nonneg_right n2 (by positivity))
  · rw [eA]
    exact (hNo u hu).s1.trans (mul_le_mul_of_nonneg_right n3 hr30)
  · rw [eB]
    exact (hNo u hu).s2.trans (mul_le_mul_of_nonneg_right n4 (by positivity))
  · rw [eW]
    have hu0 := hD.hs.trans hu.1
    have h3 := hD.wiener_le' hsol hlg hu0 (lt_lifespan hu.2 hD.ht) (hNo u hu).s2
    have h4 : 4 * e₀ * slowNorm 1 r g y u ≤ 1104 * e₀ ^ 3 * r3 := by
      have h5 := mul_le_mul_of_nonneg_left (hNo u hu).s1 (by positivity : 0 ≤ 4 * e₀)
      calc _ ≤ _ := h5
        _ = _ := by ring
    have h5 : 25012 * e₀ ^ 3 ≤ 25012 * e₀ ^ 3 * r3 := by
      have : 0 ≤ 25012 * e₀ ^ 3 := by positivity
      nlinarith
    have h6 := mul_le_mul_of_nonneg_right n5 hr30
    linarith
  · exact (hsup u hu).trans n8

/-- The slot `SlowOut` of `SlowCapsJoint`, from the chain. -/
lemma PieceData.slowOut {X R r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {s t e₀ : ℝ}
    (hD : PieceData r g y Ty s t R e₀) (hsol : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0)
    (hC : ChainScalar (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
      (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (b0 s) t e₀ R)
    (hclip : ∀ u₁ u₂, b0 s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      (∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2) ≤
        20000000000 * e₀ ^ 6 * (R ^ 4 + (u₂ - u₁) * R ^ 5))
    (hlg : 1 + Real.log (⌈R ^ 2⌉₊ : ℝ) ≤ e₀ ^ 2) :
    SlowOut slowC (e₀ ^ 6) R (fun _ _ _ _ _ => True) r g y s t := by
  have he := hD.he
  have hR1 := hD.hR
  obtain ⟨-, -, -, -, -, n6, -, -⟩ := output_numbers he hR1
  refine ⟨fun u hu => hD.trace u ⟨hD.a_le_s.trans hu.1, hu.2⟩, ?_, ?_, ?_, trivial⟩
  · have ht0 := hD.hs.trans hD.hst
    have hp : HeatPair 2 s t (corrSlow r g y) (corrForce r g y) :=
      (heatPair_corrSlow hsol hr (Or.inr (Or.inr rfl)) ht0 hD.ht).mono hD.hs le_rfl
    have := hp.intervalIntegrable_dissipation hD.hst
    have e : (2 : ℝ) + 1 = 3 := by norm_num
    rwa [e] at this
  · intro u₁ u₂ h3 h4 h5 _
    refine (hclip u₁ u₂ (hD.b0_le.trans h3) h4 h5).trans ?_
    have h6 : 0 ≤ u₂ - u₁ := by linarith
    have h7 : 0 ≤ R ^ 4 + (u₂ - u₁) * R ^ 5 := by positivity
    simp only [slowPrice]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right n6 (by positivity)) h7
  · intro u₁ u₂ h3 h4 h5 h6
    obtain ⟨k1, k2⟩ := hD.kin_le hsol hr hC hlg h3 h4 h5 h6
    obtain ⟨k3, k4⟩ := kin_numbers he hR1
    exact ⟨k1.trans k3, k2.trans k4⟩

/-- The data of a piece, from the hypotheses of `SlowCapsJoint`. -/
lemma pieceData {R₀ X R r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps} {s t : ℝ}
    {q : ℝ → ℝ → Caps → ℝ} (hb : SlowBudget R₀ q)
    (hfl : 2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 ≤ q X R caps) (hdom : JDom R₀ X R) (hR1 : 1 ≤ R)
    (he : 1 ≤ Ex 6 R) (hsol : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0)
    (hP : PieceHyp 4 (q X R) r g y Ty caps s t)
    (hH : SlowHistory caps (levelsJ slowL (Ex 6 R ^ 2)) R r g y s) :
    PieceData r g y Ty s t R (Ex 6 R) := by
  have htr := piece_trace hsol hr hfl hP hH.onUnit
  exact
    { hs := hP.hs
      hst := hP.hst
      hlen := hP.len
      ht := hP.ht
      hR := hR1
      he := he
      trace := htr
      budget := piece_budget hb hdom hsol hr hP hH.onUnit
      level := hH.level
      zero := fun hs1 => by
        have ha : max 0 (s - 1) = 0 := max_eq_left (by linarith)
        have hT : ENNReal.ofReal 0 < Ty := lt_lifespan (hP.hs.trans hP.hst) hP.ht
        exact zero_le hsol hr hdom.X_le_R hR1 hT
          (htr 0 ⟨by rw [ha], hP.hs.trans hP.hst⟩) }

/-- The level of the split. -/
lemma level_choice {R₀ X R : ℝ} (hdom : JDom R₀ X R) (hLR : LargeR R) (hR1 : 1 ≤ R) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ Λ ≤ Ex 6 R * R ∧
      (KK (nR R) * R) ^ (2 ^ nR R) ≤ Λ ^ (2 ^ nR R - 1) := by
  have hR0 : 0 < R := by linarith
  set n := nR R with hn
  have hK1 := one_le_KK n
  have hEx4 : 1 ≤ Ex 4 R := hdom.one_le_Ex (by norm_num)
  set D : ℝ := KK n * R with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hD1 : 1 ≤ D := by simp only [hDdef]; nlinarith
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine ⟨Ex 4 R * D, by nlinarith, ?_, ?_⟩
  · have h3 : Ex 4 R * KK n ≤ Ex 6 R := by
      calc Ex 4 R * KK n ≤ Ex 4 R * Ex 1 R :=
            mul_le_mul_of_nonneg_left hLR.kk (Ex_pos _ _).le
        _ = Ex 5 R := by rw [← Ex_add]; norm_num
        _ ≤ Ex 6 R := hdom.Ex_le_Ex (by norm_num)
    calc Ex 4 R * D = Ex 4 R * KK n * R := by simp only [hDdef]; ring
      _ ≤ Ex 6 R * R := mul_le_mul_of_nonneg_right h3 hR0.le
  · have e : D ^ (2 ^ n) = D * D ^ (2 ^ n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hq]
    have e2 : (Ex 4 R * D) ^ (2 ^ n - 1) = Ex 4 R ^ (2 ^ n - 1) * D ^ (2 ^ n - 1) := mul_pow _ _ _
    rw [e, e2]
    exact mul_le_mul_of_nonneg_right hLR.kkR (pow_nonneg hD0 _)

lemma five_le {R : ℝ} (h1 : Real.exp (Real.exp 16000) ≤ R) : 5 ≤ R := by
  have h4 : (1 : ℝ) + Real.exp 16000 ≤ Real.exp (Real.exp 16000) := by
    have := Real.add_one_le_exp (Real.exp 16000)
    linarith
  have h5 : (1 : ℝ) + 16000 ≤ Real.exp 16000 := by
    have := Real.add_one_le_exp (16000 : ℝ)
    linarith
  linarith

/-- **E7-P.**  At any threshold paying the source budget, and the floor of the corrector trace,
`SlowCapsJoint` holds, with bounded pieces, `Tp = 4`, and absolute constants. -/
theorem slowCapsJoint_of_budget {R₀ : ℝ} {q : ℝ → ℝ → Caps → ℝ} (hb : SlowBudget R₀ q)
    (hfl : ∀ X R, JDom R₀ X R → ∀ caps, 2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 ≤ q X R caps)
    (hone : ∀ X R, JDom R₀ X R → ∀ caps, 1 ≤ q X R caps) :
    SlowCapsJoint (R₁ R₀) (fun _ _ => 4) q slowL slowC 36 (fun _ _ _ _ _ _ _ => True) := by
  intro X R hdom r g y Ty hsol caps s t hP hH
  have hdom0 : JDom R₀ X R := hdom.mono (le_max_left _ _)
  have hRR := hdom.R₀_le
  have h1 : Real.exp (Real.exp 16000) ≤ R :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hRR
  have h2 : cN ^ 2 ≤ R := ((le_max_right _ _).trans (le_max_right _ _)).trans hRR
  have hLR := largeR h1 h2
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hP' : PieceHyp 4 (q X R) r g y Ty caps s t := hP
  have hr : r ≠ 0 := by
    intro h0
    have := (hone X R hdom0 caps).trans hP'.thr
    rw [h0, abs_zero] at this
    linarith
  have e12 : Ex (36 / 3) R = Ex 12 R := by norm_num
  rw [e12, Ex_twelve] at hH
  rw [e12, Ex_twelve, Ex_thirtysix]
  have he : 1 ≤ Ex 6 R := hdom.one_le_Ex (by norm_num)
  have hD := pieceData hb (hfl X R hdom0 caps) hdom0 hR1 he hsol hr hP' hH
  obtain ⟨Λ, hΛ1, hΛR, hDΛ⟩ := level_choice hdom hLR hR1
  obtain ⟨hC, hclip⟩ := hD.chain hsol hr hΛ1 hΛR hDΛ
  have hK : KK (nR R) ≤ Ex 6 R := hLR.kk.trans (hdom.Ex_le_Ex (by norm_num))
  have hsup := hD.sup_le hsol hr hC hK hLR.lg hLR.cn hLR.two hLR.pow6 (five_le h1)
  obtain ⟨-, -, -, -, -, -, n7, -⟩ := output_numbers he hR1
  have hJ : (∫ u in s..t, slowNorm 2 r g y u ^ 2) ≤ slowC * Ex 6 R ^ 6 * R ^ slowExpHA.eJ := by
    have eJ : R ^ slowExpHA.eJ = R ^ 3 := by
      change R ^ (3 : ℝ) = R ^ 3
      exact_mod_cast Real.rpow_natCast R 3
    rw [eJ]
    exact (hD.J_le hsol hr hC).trans (mul_le_mul_of_nonneg_right n7 (by positivity))
  exact ⟨hD.caps_out hsol hr hC hLR.lg hsup, hJ, hD.slowOut hsol hr hC hclip hLR.lg,
    hD.regain hsol hr hC⟩

/-- The budget passes to larger thresholds. -/
theorem SlowBudget.mono {R₀ : ℝ} {q q' : ℝ → ℝ → Caps → ℝ} (hb : SlowBudget R₀ q)
    (hq : ∀ X R, JDom R₀ X R → ∀ caps, q X R caps ≤ q' X R caps) : SlowBudget R₀ q' :=
  fun X R hdom r g y Ty hsol caps s t hs hst ht hlen hthr hP =>
    hb X R hdom r g y Ty hsol caps s t hs hst ht hlen ((hq X R hdom caps).trans hthr) hP

lemma one_le_slowL (i : Fin 5) : 1 ≤ slowL i := by
  fin_cases i <;> norm_num [slowL]

/-- **E7-P at the threshold of the package**: `qSFull` carries the floor of the corrector trace, so
the only role left to it is the source budget, step J4. -/
theorem JointData.slowCaps_of_budget (D : JointData) {R₀ : ℝ} (hb : SlowBudget R₀ D.qSFull) :
    SlowCapsJoint (R₁ R₀) (fun _ _ => 4) D.qSFull slowL slowC 36 (fun _ _ _ _ _ _ _ => True) := by
  have hc := c4_pos
  refine slowCapsJoint_of_budget hb (fun X R hdom caps => ?_) (fun X R hdom caps => ?_)
  · have hX : 0 ≤ X := by linarith [hdom.one_lt_X]
    have hφ : 0 ≤ R - X := by linarith [hdom.X_le_R]
    exact le_qS_of_floor hX hφ caps
  · have hX : 0 ≤ X := by linarith [hdom.one_lt_X]
    have hφ : 0 ≤ R - X := by linarith [hdom.X_le_R]
    have hy := cp_nonneg caps.yF
    have hB := cp_nonneg caps.BS
    have hY : 0 ≤ totalY X caps := by unfold totalY; positivity
    have h2 : 2 ≤ rootFloor X (R - X) caps := by
      have h3 : 0 ≤ 2 ^ 5 * c4 * totalY X caps * (R - X) := by positivity
      have h4 : 0 ≤ 2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 := by positivity
      unfold rootFloor
      nlinarith only [h3, h4, hY, hφ]
    have h5 : 2 ≤ Q0Prime X (R - X) (D.q₀ X R caps) caps := h2.trans (le_max_left _ _)
    exact le_trans (by linarith) (le_max_right _ _)

/-- **E7-P, unconditional, at the fixed-force budget**: at the threshold `budgetPoly` of
`corrRes_budget`, which is above `Q` at the joint caps. -/
theorem slowCapsJoint_budgetPoly (R₀ : ℝ) :
    SlowCapsJoint (R₁ R₀) (fun _ _ => 4)
      (fun X R caps => max (budgetPoly (R - X) caps) (2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 + 1))
      slowL slowC 36 (fun _ _ _ _ _ _ _ => True) := by
  refine slowCapsJoint_of_budget ((slowBudget_budgetPoly R₀).mono fun X R _ caps =>
    le_max_left _ _) (fun X R _ caps => ?_) (fun X R _ caps => ?_)
  · exact le_trans (by linarith) (le_max_right _ _)
  · have hc := c4_pos
    have : 0 ≤ 2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 := by
      have := cp_nonneg caps.yF
      positivity
    exact le_trans (by linarith) (le_max_right _ _)

end OVNS.Quant.Slow
