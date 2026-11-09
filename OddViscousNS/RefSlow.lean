import OddViscousNS.RefSector

/-! # The slow sectors of the reference, Fourier-native route (`viaUG`)

Horizontal: `Proposition fg:prop:h`.  Vertical: replaces the manuscript's `L⁴` maximum principle
(`fg:lem:L4`, `fg:lem:zH1`) by `y' + ‖ζ‖₂² ≤ 2 𝒜(h)² y + 2‖g‖²` and the uniform Gronwall lemma. -/

open MeasureTheory Set intervalIntegral
open scoped ENNReal
noncomputable section
namespace OVNS

variable {g : Field} {T : ℝ≥0∞} {w : ℝ → Field} {φ : ℝ}

/-! ### Sector algebra -/

private lemma PiS_PiS (u : Field) : PiS (PiS u) = PiS u := by
  ext1 k
  by_cases h : k 2 = 0 <;> simp [PiS, h]

private lemma PiH_PiS' (u : Field) : PiH (PiS u) = PiH u := by
  ext1 k
  by_cases h : k 2 = 0 <;> simp [PiH, PiS, h]

private lemma PiV_PiS' (u : Field) : PiV (PiS u) = PiV u := by
  ext1 k
  by_cases h : k 2 = 0 <;> simp [PiV, PiS, h]

private lemma mz_PiH {u : Field} (hu : Adm 2 u) : MZ 2 (PiH u) := by
  refine ⟨hu.inH.PiH, ?_⟩
  ext i
  fin_cases i <;> simp [PiH, hu.mean]

/-- The closed slow convection lies in `L²`. -/
private lemma inH_Bsym {u : Field} (hu : Adm 2 u) : InH 0 (Bsym (PiS u) (PiS u)) := by
  rw [← PiS_Qres hu]
  exact (majorized_res.hnorm_zero_le 0 hu.mz hu.mz).1.PiS

private lemma hnorm_PiH_le {f : Field} (hf : InH 0 f) (hφ : hnorm 0 f ≤ φ) :
    hnorm 0 (PiH f) ≤ φ := by
  refine le_trans ((sq_le_sq₀ (hnorm_nonneg _ _) (hnorm_nonneg _ _)).1 ?_) hφ
  rw [hnorm_sq_three hf (s := 0)]
  nlinarith [sq_nonneg (hnorm 0 (PiV f)), sq_nonneg (hnorm 0 (PiF f))]

private lemma hnorm_PiV_le {f : Field} (hf : InH 0 f) (hφ : hnorm 0 f ≤ φ) :
    hnorm 0 (PiV f) ≤ φ := by
  refine le_trans ((sq_le_sq₀ (hnorm_nonneg _ _) (hnorm_nonneg _ _)).1 ?_) hφ
  rw [hnorm_sq_three hf (s := 0)]
  nlinarith [sq_nonneg (hnorm 0 (PiH f)), sq_nonneg (hnorm 0 (PiF f))]

/-! ### Pointwise bounds on the pairings -/

private lemma horiz_pair (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) {u : Field} (hu : Adm 2 u) :
    2 * pair 1 (PiH u) (PiH g - PiH (Bsym (PiS u) (PiS u))) ≤ hnorm 2 (PiH u) ^ 2 + φ ^ 2 := by
  have hgi : InH 0 g := hg.inH.mono (by norm_num)
  have hc : InH (1 + 1) (PiH u) := by
    rw [one_add_one_eq_two]
    exact hu.inH.PiH
  have hF : InH (1 - 1) (PiH g) := by
    rw [sub_self]
    exact hgi.PiH
  have hB : InH (1 - 1) (PiH (Bsym (PiS u) (PiS u))) := by
    rw [sub_self]
    exact (inH_Bsym hu).PiH
  have hv := pair_slow_horizontal hu.PiS (PiS_PiS u) (σ := 1) (Or.inr rfl)
  rw [PiH_PiS'] at hv
  rw [pair_sub hc hF hB, hv, sub_zero]
  have hle := (pair_le hc hF).2
  rw [one_add_one_eq_two, sub_self] at hle
  have h1 := le_abs_self (pair 1 (PiH u) (PiH g))
  have h2 := mul_le_mul_of_nonneg_left (hnorm_PiH_le hgi hφ) (hnorm_nonneg 2 (PiH u))
  nlinarith [sq_nonneg (hnorm 2 (PiH u) - φ)]

private lemma vert_pair_zero (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) {u : Field} (hu : Adm 2 u) :
    2 * pair 0 (PiV u) (PiV g - PiV (Bsym (PiS u) (PiS u))) ≤ hnorm 1 (PiV u) ^ 2 + φ ^ 2 := by
  have hgi : InH 0 g := hg.inH.mono (by norm_num)
  have hc : InH (0 + 1) (PiV u) := by
    rw [zero_add]
    exact hu.inH.PiV.mono (by norm_num)
  have hF : InH (0 - 1) (PiV g) := hgi.PiV.mono (by norm_num)
  have hB : InH (0 - 1) (PiV (Bsym (PiS u) (PiS u))) := (inH_Bsym hu).PiV.mono (by norm_num)
  have hv := pair_slow_vertical hu.PiS (PiS_PiS u)
  rw [PiV_PiS'] at hv
  rw [pair_sub hc hF hB, hv, sub_zero]
  have hle := (pair_le hc hF).2
  rw [zero_add] at hle
  have h1 := le_abs_self (pair 0 (PiV u) (PiV g))
  have h0 : hnorm (0 - 1) (PiV g) ≤ φ :=
    (hnorm_mono (by norm_num) hgi.PiV).trans (hnorm_PiV_le hgi hφ)
  have h2 := mul_le_mul_of_nonneg_left h0 (hnorm_nonneg 1 (PiV u))
  nlinarith [sq_nonneg (hnorm 1 (PiV u) - φ)]

private lemma vert_pair_one (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) {u : Field} (hu : Adm 2 u) :
    2 * pair 1 (PiV u) (PiV g - PiV (Bsym (PiS u) (PiS u))) ≤ hnorm 2 (PiV u) ^ 2 +
      (2 * c4 ^ 2 * hnorm 2 (PiH u) ^ 2 * hnorm 1 (PiV u) ^ 2 + 2 * φ ^ 2) := by
  have hgi : InH 0 g := hg.inH.mono (by norm_num)
  have hc : InH (1 + 1) (PiV u) := by
    rw [one_add_one_eq_two]
    exact hu.inH.PiV
  have hF : InH (1 - 1) (PiV g) := by
    rw [sub_self]
    exact hgi.PiV
  have hB : InH (1 - 1) (PiV (Bsym (PiS u) (PiS u))) := by
    rw [sub_self]
    exact (inH_Bsym hu).PiV
  have hv := pair_slow_vertical_le hu.PiS (PiS_PiS u)
  rw [PiV_PiS', PiH_PiS'] at hv
  rw [pair_sub hc hF hB]
  have hle := (pair_le hc hF).2
  rw [one_add_one_eq_two, sub_self] at hle
  have h1 := le_abs_self (pair 1 (PiV u) (PiV g))
  have h2 := mul_le_mul_of_nonneg_left (hnorm_PiV_le hgi hφ) (hnorm_nonneg 2 (PiV u))
  have h3 := neg_abs_le (pair 1 (PiV u) (PiV (Bsym (PiS u) (PiS u))))
  have hYb := mul_nonneg (hnorm_nonneg 1 (PiV u)) (hnorm_nonneg 2 (PiV u))
  have h4 : wiener (PiH u) * (hnorm 1 (PiV u) * hnorm 2 (PiV u)) ≤
      c4 * hnorm 2 (PiH u) * (hnorm 1 (PiV u) * hnorm 2 (PiV u)) :=
    mul_le_mul_of_nonneg_right (wiener_le (mz_PiH hu)) hYb
  nlinarith [sq_nonneg (hnorm 2 (PiV u) - 2 * φ),
    sq_nonneg (hnorm 2 (PiV u) - 2 * c4 * hnorm 2 (PiH u) * hnorm 1 (PiV u))]

/-! ### Integrated inequalities -/

private lemma adm_mem (hw : RefSol g T w) {s t u : ℝ} (hs : 0 ≤ s) (hu : u ∈ Icc s t)
    (ht : ENNReal.ofReal t < T) : Adm 2 (w u) :=
  hw.adm u (hs.trans hu.1) ((ENNReal.ofReal_le_ofReal hu.2).trans_lt ht)

private lemma ii_sq {f : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t) (h : ContinuousOn f (Icc s t)) :
    IntervalIntegrable (fun u => f u ^ 2) volume s t :=
  ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hst]; exact h.pow 2)

private lemma cont_slow (hg : Adm 2 g) (hw : RefSol g T w) {σ s t : ℝ}
    (hσ : σ = 0 ∨ σ = 1 ∨ σ = 2) (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    ContinuousOn (fun u => hnorm σ (PiH (w u))) (Icc s t) ∧
      ContinuousOn (fun u => hnorm σ (PiV (w u))) (Icc s t) := by
  obtain ⟨-, -, h1, h2⟩ := hw.continuousOn_hnorm hg hσ (hs.trans hst) ht
  exact ⟨h1.mono (Icc_subset_Icc_left hs), h2.mono (Icc_subset_Icc_left hs)⟩

private lemma integral_const' (c s t : ℝ) : ∫ _ in s..t, c = c * (t - s) := by
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- The energy identity turned into an inequality by a pointwise bound of the pairing.  The pairing
need not be known integrable: otherwise its integral vanishes. -/
private lemma energy_bound {σ τ s t : ℝ} {c F : ℝ → Field} {R : ℝ → ℝ} (h : HeatPair σ s t c F)
    (hτ : σ + 1 = τ) (hst : s ≤ t) (hD : ContinuousOn (fun u => hnorm τ (c u)) (Icc s t))
    (hR : IntervalIntegrable R volume s t) (hR0 : ∀ u ∈ Icc s t, 0 ≤ R u)
    (hp : ∀ u ∈ Icc s t, 2 * pair σ (c u) (F u) ≤ hnorm τ (c u) ^ 2 + R u) :
    hnorm σ (c t) ^ 2 + ∫ u in s..t, hnorm τ (c u) ^ 2 ≤
      hnorm σ (c s) ^ 2 + ∫ u in s..t, R u := by
  subst hτ
  have hid := h.energy_identity le_rfl hst le_rfl
  have hDi := ii_sq hst hD
  have hint : 2 * ∫ u in s..t, pair σ (c u) (F u) ≤
      (∫ u in s..t, hnorm (σ + 1) (c u) ^ 2) + ∫ u in s..t, R u := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hDi hR]
    by_cases hi : IntervalIntegrable (fun u => 2 * pair σ (c u) (F u)) volume s t
    · exact intervalIntegral.integral_mono_on hst hi (hDi.add hR) hp
    · rw [intervalIntegral.integral_undef hi]
      exact intervalIntegral.integral_nonneg hst fun u hu => add_nonneg (sq_nonneg _) (hR0 u hu)
  linarith

/-- From `A² + ∫B² ≤ A² + φ²Δt` with `A ≤ B` to exponential decay. -/
private lemma decay_aux {A B : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t) (hA : ContinuousOn A (Icc s t))
    (hB : ContinuousOn B (Icc s t)) (hA0 : ∀ u, 0 ≤ A u) (hle : ∀ u ∈ Icc s t, A u ≤ B u)
    (h : ∀ s' t', s ≤ s' → s' ≤ t' → t' ≤ t →
      A t' ^ 2 + ∫ u in s'..t', B u ^ 2 ≤ A s' ^ 2 + φ ^ 2 * (t' - s')) :
    A t ^ 2 ≤ Real.exp (-(t - s)) * A s ^ 2 + φ ^ 2 := by
  have hy : ContinuousOn (fun u => A u ^ 2) (Icc s t) := hA.pow 2
  have key := gronwall_decay (y := fun u => A u ^ 2) (lam := 1) (β := φ ^ 2) hst one_pos
    (sq_nonneg φ) hy (fun s' t' h1 h2 h3 => ?_) t hst le_rfl
  · simpa only [neg_mul, one_mul, div_one] using key
  · have hsub : Icc s' t' ⊆ Icc s t := Icc_subset_Icc h1 h3
    have hmono : ∫ u in s'..t', A u ^ 2 ≤ ∫ u in s'..t', B u ^ 2 :=
      intervalIntegral.integral_mono_on h2 (ii_sq h2 (hA.mono hsub)) (ii_sq h2 (hB.mono hsub))
        fun u hu => pow_le_pow_left₀ (hA0 u) (hle u (hsub hu)) 2
    have := h s' t' h1 h2 h3
    simp only [one_mul]
    linarith

/-- `(a_h²)' + b_h² ≤ ‖g‖²`, integrated. -/
theorem RefSol.horiz_h1 (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 1 (PiH (w t)) ^ 2 + ∫ u in s..t, hnorm 2 (PiH (w u)) ^ 2 ≤
      hnorm 1 (PiH (w s)) ^ 2 + φ ^ 2 * (t - s) := by
  have hp : HeatPair 1 s t (fun u => PiH (w u))
      (fun u => PiH g - PiH (Bsym (PiS (w u)) (PiS (w u)))) :=
    (hw.heatPair_horiz hg (Or.inr rfl) (hs.trans hst) ht).mono hs le_rfl
  have hd : ContinuousOn (fun u => hnorm 2 (PiH (w u))) (Icc s t) :=
    (cont_slow hg hw (Or.inr (Or.inr rfl)) hs hst ht).1
  have hτ : (1 : ℝ) + 1 = 2 := by norm_num
  have h2 : ∀ u ∈ Icc s t, 2 * pair 1 (PiH (w u)) (PiH g - PiH (Bsym (PiS (w u)) (PiS (w u)))) ≤
      hnorm 2 (PiH (w u)) ^ 2 + φ ^ 2 := fun u hu => horiz_pair hg hφ (adm_mem hw hs hu ht)
  have h3 := energy_bound (R := fun _ => φ ^ 2) hp hτ hst hd intervalIntegrable_const
    (fun _ _ => sq_nonneg _) h2
  rwa [integral_const'] at h3

/-- Exponential decay of the horizontal enstrophy to the force level. -/
theorem RefSol.horiz_decay (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 1 (PiH (w t)) ^ 2 ≤ Real.exp (-(t - s)) * hnorm 1 (PiH (w s)) ^ 2 + φ ^ 2 := by
  have hA : ContinuousOn (fun u => hnorm 1 (PiH (w u))) (Icc s t) :=
    (cont_slow hg hw (Or.inr (Or.inl rfl)) hs hst ht).1
  have hB : ContinuousOn (fun u => hnorm 2 (PiH (w u))) (Icc s t) :=
    (cont_slow hg hw (Or.inr (Or.inr rfl)) hs hst ht).1
  have hA0 : ∀ u, 0 ≤ hnorm 1 (PiH (w u)) := fun u => hnorm_nonneg _ _
  have hle : ∀ u ∈ Icc s t, hnorm 1 (PiH (w u)) ≤ hnorm 2 (PiH (w u)) := fun u hu =>
    hnorm_mono (by norm_num) (adm_mem hw hs hu ht).inH.PiH
  have h4 : ∀ s' t', s ≤ s' → s' ≤ t' → t' ≤ t → hnorm 1 (PiH (w t')) ^ 2 +
      (∫ u in s'..t', hnorm 2 (PiH (w u)) ^ 2) ≤ hnorm 1 (PiH (w s')) ^ 2 + φ ^ 2 * (t' - s') :=
    fun s' t' h1 h2 h3 =>
      hw.horiz_h1 hg hφ (hs.trans h1) h2 ((ENNReal.ofReal_le_ofReal h3).trans_lt ht)
  have h5 := decay_aux (φ := φ) hst hA hB hA0 hle h4
  exact h5

/-- `E' + ‖ζ‖₁² ≤ ‖g‖²`, integrated. -/
theorem RefSol.vert_l2 (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 0 (PiV (w t)) ^ 2 + ∫ u in s..t, hnorm 1 (PiV (w u)) ^ 2 ≤
      hnorm 0 (PiV (w s)) ^ 2 + φ ^ 2 * (t - s) := by
  have hp : HeatPair 0 s t (fun u => PiV (w u))
      (fun u => PiV g - PiV (Bsym (PiS (w u)) (PiS (w u)))) :=
    (hw.heatPair_vert hg (Or.inl rfl) (hs.trans hst) ht).mono hs le_rfl
  have hd : ContinuousOn (fun u => hnorm 1 (PiV (w u))) (Icc s t) :=
    (cont_slow hg hw (Or.inr (Or.inl rfl)) hs hst ht).2
  have hτ : (0 : ℝ) + 1 = 1 := by norm_num
  have h2 : ∀ u ∈ Icc s t, 2 * pair 0 (PiV (w u)) (PiV g - PiV (Bsym (PiS (w u)) (PiS (w u)))) ≤
      hnorm 1 (PiV (w u)) ^ 2 + φ ^ 2 := fun u hu => vert_pair_zero hg hφ (adm_mem hw hs hu ht)
  have h3 := energy_bound (R := fun _ => φ ^ 2) hp hτ hst hd intervalIntegrable_const
    (fun _ _ => sq_nonneg _) h2
  rwa [integral_const'] at h3

/-- Decay of the vertical energy. -/
theorem RefSol.vert_decay (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 0 (PiV (w t)) ^ 2 ≤ Real.exp (-(t - s)) * hnorm 0 (PiV (w s)) ^ 2 + φ ^ 2 := by
  have hA : ContinuousOn (fun u => hnorm 0 (PiV (w u))) (Icc s t) :=
    (cont_slow hg hw (Or.inl rfl) hs hst ht).2
  have hB : ContinuousOn (fun u => hnorm 1 (PiV (w u))) (Icc s t) :=
    (cont_slow hg hw (Or.inr (Or.inl rfl)) hs hst ht).2
  have hA0 : ∀ u, 0 ≤ hnorm 0 (PiV (w u)) := fun u => hnorm_nonneg _ _
  have hle : ∀ u ∈ Icc s t, hnorm 0 (PiV (w u)) ≤ hnorm 1 (PiV (w u)) := fun u hu =>
    hnorm_mono (by norm_num) ((adm_mem hw hs hu ht).inH.PiV.mono (by norm_num))
  have h4 : ∀ s' t', s ≤ s' → s' ≤ t' → t' ≤ t → hnorm 0 (PiV (w t')) ^ 2 +
      (∫ u in s'..t', hnorm 1 (PiV (w u)) ^ 2) ≤ hnorm 0 (PiV (w s')) ^ 2 + φ ^ 2 * (t' - s') :=
    fun s' t' h1 h2 h3 =>
      hw.vert_l2 hg hφ (hs.trans h1) h2 ((ENNReal.ofReal_le_ofReal h3).trans_lt ht)
  have h5 := decay_aux (φ := φ) hst hA hB hA0 hle h4
  exact h5

/-- The vertical `H¹` inequality, integrated. -/
theorem RefSol.vert_h1 (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 1 (PiV (w t)) ^ 2 + ∫ u in s..t, hnorm 2 (PiV (w u)) ^ 2 ≤
      hnorm 1 (PiV (w s)) ^ 2 + ∫ u in s..t,
        (2 * c4 ^ 2 * hnorm 2 (PiH (w u)) ^ 2 * hnorm 1 (PiV (w u)) ^ 2 + 2 * φ ^ 2) := by
  have c1 : ContinuousOn (fun u => hnorm 2 (PiH (w u))) (Icc s t) :=
    (cont_slow hg hw (Or.inr (Or.inr rfl)) hs hst ht).1
  have c2 : ContinuousOn (fun u => hnorm 1 (PiV (w u))) (Icc s t) :=
    (cont_slow hg hw (Or.inr (Or.inl rfl)) hs hst ht).2
  have hc : ContinuousOn (fun u => 2 * c4 ^ 2 * hnorm 2 (PiH (w u)) ^ 2 *
      hnorm 1 (PiV (w u)) ^ 2 + 2 * φ ^ 2) (Icc s t) :=
    ((continuousOn_const.mul (c1.pow 2)).mul (c2.pow 2)).add continuousOn_const
  have hR : IntervalIntegrable (fun u => 2 * c4 ^ 2 * hnorm 2 (PiH (w u)) ^ 2 *
      hnorm 1 (PiV (w u)) ^ 2 + 2 * φ ^ 2) volume s t :=
    ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le hst])
  have hp : HeatPair 1 s t (fun u => PiV (w u))
      (fun u => PiV g - PiV (Bsym (PiS (w u)) (PiS (w u)))) :=
    (hw.heatPair_vert hg (Or.inr rfl) (hs.trans hst) ht).mono hs le_rfl
  have hd : ContinuousOn (fun u => hnorm 2 (PiV (w u))) (Icc s t) :=
    (cont_slow hg hw (Or.inr (Or.inr rfl)) hs hst ht).2
  have hτ : (1 : ℝ) + 1 = 2 := by norm_num
  have h2 : ∀ u ∈ Icc s t, 2 * pair 1 (PiV (w u)) (PiV g - PiV (Bsym (PiS (w u)) (PiS (w u)))) ≤
      hnorm 2 (PiV (w u)) ^ 2 + (2 * c4 ^ 2 * hnorm 2 (PiH (w u)) ^ 2 * hnorm 1 (PiV (w u)) ^ 2 +
        2 * φ ^ 2) := fun u hu => vert_pair_one hg hφ (adm_mem hw hs hu ht)
  have h0 : ∀ u ∈ Icc s t, 0 ≤ 2 * c4 ^ 2 * hnorm 2 (PiH (w u)) ^ 2 * hnorm 1 (PiV (w u)) ^ 2 +
      2 * φ ^ 2 := fun _ _ => by positivity
  have h3 := energy_bound hp hτ hst hd hR h0 h2
  exact h3

/-- `vert_h1`, with the dissipation dropped, in the form Gronwall consumes. -/
private lemma RefSol.vert_step (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 1 (PiV (w t)) ^ 2 ≤ hnorm 1 (PiV (w s)) ^ 2 + ∫ u in s..t,
      (2 * c4 ^ 2 * hnorm 2 (PiH (w u)) ^ 2 * hnorm 1 (PiV (w u)) ^ 2 + 2 * φ ^ 2) := by
  have h := hw.vert_h1 hg hφ hs hst ht
  have h0 : 0 ≤ ∫ u in s..t, hnorm 2 (PiV (w u)) ^ 2 :=
    intervalIntegral.integral_nonneg hst fun _ _ => sq_nonneg _
  linarith

/-- Gronwall from an arbitrary start: `y(t) ≤ (y(s) + 2φ²(t-s)) exp(2c₄²∫‖h‖₂²)`. -/
theorem RefSol.vert_gronwall (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 1 (PiV (w t)) ^ 2 ≤ (hnorm 1 (PiV (w s)) ^ 2 + 2 * φ ^ 2 * (t - s)) *
      Real.exp (2 * c4 ^ 2 * ∫ u in s..t, hnorm 2 (PiH (w u)) ^ 2) := by
  have hH := (cont_slow hg hw (Or.inr (Or.inr rfl)) hs hst ht).1
  have key := gronwall_simple (y := fun u => hnorm 1 (PiV (w u)) ^ 2)
    (κ := fun u => 2 * c4 ^ 2 * hnorm 2 (PiH (w u)) ^ 2) (β := fun _ => 2 * φ ^ 2) hst
    ((cont_slow hg hw (Or.inr (Or.inl rfl)) hs hst ht).2.pow 2) ((ii_sq hst hH).const_mul _)
    (fun _ => by positivity) intervalIntegrable_const (fun _ => by positivity)
    (fun s' t' h1 h2 h3 =>
      hw.vert_step hg hφ (hs.trans h1) h2 ((ENNReal.ofReal_le_ofReal h3).trans_lt ht))
    s t le_rfl hst le_rfl
  simpa only [integral_const', intervalIntegral.integral_const_mul, mul_assoc] using key

/-- The uniform Gronwall absorption on a unit window ending at `t ≥ 1`: if at time `t-1` the
horizontal enstrophy is `≤ A` and the vertical energy is `≤ B`, then
`‖ζ(t)‖₁² ≤ (B + 3φ²) exp(2c₄²(A + φ²))`. -/
theorem RefSol.vert_uniform (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {t A B : ℝ}
    (ht1 : 1 ≤ t) (ht : ENNReal.ofReal t < T) (hA : hnorm 1 (PiH (w (t - 1))) ^ 2 ≤ A)
    (hB : hnorm 0 (PiV (w (t - 1))) ^ 2 ≤ B) :
    hnorm 1 (PiV (w t)) ^ 2 ≤ (B + 3 * φ ^ 2) * Real.exp (2 * c4 ^ 2 * (A + φ ^ 2)) := by
  have h0 : 0 ≤ t - 1 := by linarith
  have hle : t - 1 ≤ t := by linarith
  have hH := (cont_slow hg hw (Or.inr (Or.inr rfl)) h0 hle ht).1
  have key := uniform_gronwall (y := fun u => hnorm 1 (PiV (w u)) ^ 2)
    (κ := fun u => 2 * c4 ^ 2 * hnorm 2 (PiH (w u)) ^ 2) (β := fun _ => 2 * φ ^ 2)
    ((cont_slow hg hw (Or.inr (Or.inl rfl)) h0 hle ht).2.pow 2) (fun _ => sq_nonneg _)
    ((ii_sq hle hH).const_mul _) (fun _ => by positivity) intervalIntegrable_const
    (fun _ => by positivity)
    (fun s' t' h1 h2 h3 =>
      hw.vert_step hg hφ (h0.trans h1) h2 ((ENNReal.ofReal_le_ofReal h3).trans_lt ht))
  simp only [integral_const', intervalIntegral.integral_const_mul, sub_sub_cancel] at key
  have e1 := hw.vert_l2 hg hφ h0 hle ht
  have e2 := hw.horiz_h1 hg hφ h0 hle ht
  rw [sub_sub_cancel] at e1 e2
  have n1 := sq_nonneg (hnorm 0 (PiV (w t)))
  have n2 := sq_nonneg (hnorm 1 (PiH (w t)))
  have n3 := sq_nonneg (hnorm 0 (PiV (w (t - 1))))
  have hB0 : 0 ≤ B + 3 * φ ^ 2 := by nlinarith [sq_nonneg φ]
  refine key.trans (mul_le_mul (by linarith) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hB0)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end OVNS
