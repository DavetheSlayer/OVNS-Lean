import OddViscousNS.RefFast
import OddViscousNS.RefSlow

/-! # Global reference bounds and end-of-window absorption
(`Proposition fg:prop:ref`, `fg:prop:abs`) -/

open MeasureTheory Set Filter intervalIntegral
open scoped ENNReal
noncomputable section
namespace OVNS

variable {g : Field} {T : ℝ≥0∞} {w : ℝ → Field} {φ : ℝ}

/-- Each sector norm is at most the total norm. -/
private lemma sectors_le {s : ℝ} {u : Field} (hu : InH s u) :
    hnorm s (PiH u) ≤ hnorm s u ∧ hnorm s (PiV u) ≤ hnorm s u ∧ hnorm s (PiF u) ≤ hnorm s u := by
  have h := hnorm_sq_three hu
  have a := sq_nonneg (hnorm s (PiH u))
  have b := sq_nonneg (hnorm s (PiV u))
  have c := sq_nonneg (hnorm s (PiF u))
  refine ⟨(sq_le_sq₀ (hnorm_nonneg _ _) (hnorm_nonneg _ _)).1 ?_,
    (sq_le_sq₀ (hnorm_nonneg _ _) (hnorm_nonneg _ _)).1 ?_,
    (sq_le_sq₀ (hnorm_nonneg _ _) (hnorm_nonneg _ _)).1 ?_⟩ <;> linarith

/-- Times below a time in the lifespan are in the lifespan. -/
private lemma lt_of_le' {u t : ℝ} (h : u ≤ t) (ht : ENNReal.ofReal t < T) :
    ENNReal.ofReal u < T :=
  (ENNReal.ofReal_le_ofReal h).trans_lt ht

/-- The integral of a constant, with the factors in the order used here. -/
private lemma integral_const'' (c s t : ℝ) : ∫ _ in s..t, c = c * (t - s) := by
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- Squares of functions continuous on an interval are integrable on it. -/
private lemma ii_sq' {f : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t) (h : ContinuousOn f (Icc s t)) :
    IntervalIntegrable (fun u => f u ^ 2) volume s t :=
  ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hst]; exact h.pow 2)

/-- `L²` pairing against the force; the nonlinearity conserves energy. -/
private lemma energy_pair (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) {u : Field} (hu : Adm 2 u) :
    2 * pair 0 u (PiS g - Qres u u) ≤ hnorm 1 u ^ 2 + φ ^ 2 := by
  have hgi : InH 0 (PiS g) := (hg.inH.mono (by norm_num)).PiS
  have hc : InH (0 + 1) u := by
    rw [zero_add]
    exact hu.inH.mono (by norm_num)
  have hF : InH (0 - 1) (PiS g) := hgi.mono (by norm_num)
  have hB : InH (0 - 1) (Qres u u) :=
    (majorized_res.hnorm_zero_le 0 hu.mz hu.mz).1.mono (by norm_num)
  rw [pair_sub hc hF hB, pair_Qres_self hu, sub_zero]
  have hle := (pair_le hc hF).2
  rw [zero_add] at hle
  have h1 := le_abs_self (pair 0 u (PiS g))
  have h0 : hnorm (0 - 1) (PiS g) ≤ φ :=
    (hnorm_mono (by norm_num) hgi).trans ((hnorm_PiS_le (hg.inH.mono (by norm_num))).trans hφ)
  have h2 := mul_le_mul_of_nonneg_left h0 (hnorm_nonneg 1 u)
  nlinarith [sq_nonneg (hnorm 1 u - φ)]

/-- The integrated energy inequality on `[s,t]`. -/
private lemma energy_step (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 0 (w t) ^ 2 + ∫ u in s..t, hnorm 1 (w u) ^ 2 ≤
      hnorm 0 (w s) ^ 2 + φ ^ 2 * (t - s) := by
  have hp := (IsHeatSol.heatPair_low majorized_res (goodForce_PiS hg) hw (σ := 0) (Or.inl rfl)
    (hs.trans hst) ht).mono hs le_rfl
  have hid := hp.energy_identity le_rfl hst le_rfl
  rw [zero_add] at hid
  have hDi := ii_sq' hst (((hw.continuousOn_hnorm hg (σ := 1) (Or.inr (Or.inl rfl))
    (hs.trans hst) ht).1).mono (Icc_subset_Icc_left hs))
  have hint : 2 * ∫ u in s..t, pair 0 (w u) (PiS g - Qres (w u) (w u)) ≤
      (∫ u in s..t, hnorm 1 (w u) ^ 2) + φ ^ 2 * (t - s) := by
    rw [← integral_const'', ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hDi intervalIntegrable_const]
    by_cases hi : IntervalIntegrable
        (fun u => 2 * pair 0 (w u) (PiS g - Qres (w u) (w u))) volume s t
    · exact intervalIntegral.integral_mono_on hst hi (hDi.add intervalIntegrable_const)
        fun u hu => energy_pair hg hφ (hw.adm u (hs.trans hu.1) (lt_of_le' hu.2 ht))
    · rw [intervalIntegral.integral_undef hi]
      exact intervalIntegral.integral_nonneg hst fun u _ => by positivity
  linarith

/-- The vertical enstrophy bound from time `0`. -/
private def Yz (ρ φ t : ℝ) : ℝ :=
  (ρ ^ 2 + 2 * φ ^ 2 * t) * Real.exp (2 * c4 ^ 2 * (ρ ^ 2 + φ ^ 2 * t))

/-- The square of the `H¹` bound on `[0,t]`. -/
private def Xsq (ρ φ t : ℝ) : ℝ :=
  ρ ^ 2 * Real.exp (CF ^ 2 * ρ ^ 2 / 2) + (ρ ^ 2 + φ ^ 2) + Yz ρ φ t

/-- The dissipation bound on `[0,t]`. -/
private def Jb (ρ φ t : ℝ) : ℝ :=
  ρ ^ 2 * (1 + CF ^ 2 * ρ ^ 2 / 2 * Real.exp (CF ^ 2 * ρ ^ 2 / 2)) + (ρ ^ 2 + φ ^ 2 * t) +
    (ρ ^ 2 + (2 * c4 ^ 2 * Yz ρ φ t * (ρ ^ 2 + φ ^ 2 * t) + 2 * φ ^ 2 * t))

private lemma Yz_nonneg (ρ φ : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Yz ρ φ t := by
  unfold Yz
  positivity

private lemma Yz_mono (ρ φ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : Yz ρ φ s ≤ Yz ρ φ t := by
  unfold Yz
  have : 0 ≤ t := hs.trans hst
  gcongr

private lemma Jb_nonneg (ρ φ : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Jb ρ φ t := by
  have := Yz_nonneg ρ φ ht
  unfold Jb
  positivity

/-- The sector squares of a time-`0` norm are bounded by the total bound. -/
private lemma sq_le_of {a b ρ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ρ) : a ^ 2 ≤ ρ ^ 2 :=
  pow_le_pow_left₀ ha (hab.trans hb) 2

/-- The horizontal dissipation bound. -/
private lemma horiz_int (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {ρ t : ℝ}
    (h0 : hnorm 1 (w 0) ≤ ρ) (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < T) :
    ∫ u in (0 : ℝ)..t, hnorm 2 (PiH (w u)) ^ 2 ≤ ρ ^ 2 + φ ^ 2 * t := by
  have h := hw.horiz_h1 hg hφ le_rfl ht0 ht
  have ad := hw.adm 0 le_rfl (lt_of_le' ht0 ht)
  have hb := sq_le_of (hnorm_nonneg _ _) (sectors_le (ad.inH.mono (by norm_num))).1 h0
  have := sq_nonneg (hnorm 1 (PiH (w t)))
  rw [sub_zero] at h
  linarith

/-- The vertical enstrophy bound. -/
private lemma vert_sup (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {ρ t : ℝ}
    (h0 : hnorm 1 (w 0) ≤ ρ) (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 1 (PiV (w t)) ^ 2 ≤ Yz ρ φ t := by
  have h := hw.vert_gronwall hg hφ le_rfl ht0 ht
  have ad := hw.adm 0 le_rfl (lt_of_le' ht0 ht)
  have hb := sq_le_of (hnorm_nonneg _ _) (sectors_le (ad.inH.mono (by norm_num))).2.1 h0
  have hi := horiz_int hg hφ hw h0 ht0 ht
  rw [sub_zero] at h
  refine h.trans ?_
  unfold Yz
  gcongr

/-- The `H¹` bound on the lifespan. -/
private lemma h1_bound (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {ρ t : ℝ}
    (h0 : hnorm 1 (w 0) ≤ ρ) (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 1 (w t) ^ 2 ≤ Xsq ρ φ t := by
  have ad0 := hw.adm 0 le_rfl (lt_of_le' ht0 ht)
  have adt := hw.adm t ht0 ht
  have hs := sectors_le (s := 1) (ad0.inH.mono (by norm_num))
  rw [hnorm_sq_three (adt.inH.mono (by norm_num) : InH 1 (w t))]
  have hF := hw.fast_h1 hg le_rfl ht0 ht
  have hH := hw.horiz_decay hg hφ le_rfl ht0 ht
  have hV := vert_sup hg hφ hw h0 ht0 ht
  have hbF := sq_le_of (hnorm_nonneg _ _) hs.2.2 h0
  have hbH := sq_le_of (hnorm_nonneg _ _) hs.1 h0
  have hF' : hnorm 1 (PiF (w t)) ^ 2 ≤ ρ ^ 2 * Real.exp (CF ^ 2 * ρ ^ 2 / 2) := by
    refine hF.trans ?_
    gcongr
  have hE : Real.exp (-(t - 0)) * hnorm 1 (PiH (w 0)) ^ 2 ≤ hnorm 1 (PiH (w 0)) ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) (Real.exp_le_one_iff.2 (by linarith))
  unfold Xsq
  linarith

/-- The vertical dissipation bound. -/
private lemma vert_int (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {ρ t : ℝ}
    (h0 : hnorm 1 (w 0) ≤ ρ) (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < T) :
    ∫ u in (0 : ℝ)..t, hnorm 2 (PiV (w u)) ^ 2 ≤
      ρ ^ 2 + (2 * c4 ^ 2 * Yz ρ φ t * (ρ ^ 2 + φ ^ 2 * t) + 2 * φ ^ 2 * t) := by
  have h := hw.vert_h1 hg hφ le_rfl ht0 ht
  have ad := hw.adm 0 le_rfl (lt_of_le' ht0 ht)
  have hb := sq_le_of (hnorm_nonneg _ _) (sectors_le (ad.inH.mono (by norm_num))).2.1 h0
  have hH := (hw.continuousOn_hnorm hg (σ := 2) (Or.inr (Or.inr rfl)) ht0 ht).2.2.1
  have hV := (hw.continuousOn_hnorm hg (σ := 1) (Or.inr (Or.inl rfl)) ht0 ht).2.2.2
  have hHi := ii_sq' ht0 hH
  have hL : IntervalIntegrable (fun u => 2 * c4 ^ 2 * hnorm 2 (PiH (w u)) ^ 2 *
      hnorm 1 (PiV (w u)) ^ 2 + 2 * φ ^ 2) volume 0 t :=
    ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le ht0]
      exact ((continuousOn_const.mul (hH.pow 2)).mul (hV.pow 2)).add continuousOn_const)
  have hR : IntervalIntegrable (fun u => 2 * c4 ^ 2 * Yz ρ φ t * hnorm 2 (PiH (w u)) ^ 2 +
      2 * φ ^ 2) volume 0 t := (hHi.const_mul _).add intervalIntegrable_const
  have hle := intervalIntegral.integral_mono_on ht0 hL hR fun u hu => by
    have h1 : hnorm 1 (PiV (w u)) ^ 2 ≤ Yz ρ φ t :=
      (vert_sup hg hφ hw h0 hu.1 (lt_of_le' hu.2 ht)).trans (Yz_mono ρ φ hu.1 hu.2)
    have h2 := mul_le_mul_of_nonneg_left h1
      (by positivity : 0 ≤ 2 * c4 ^ 2 * hnorm 2 (PiH (w u)) ^ 2)
    linarith
  rw [intervalIntegral.integral_add (hHi.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_const''] at hle
  have hi := mul_le_mul_of_nonneg_left (horiz_int hg hφ hw h0 ht0 ht)
    (by have := Yz_nonneg ρ φ ht0; positivity : 0 ≤ 2 * c4 ^ 2 * Yz ρ φ t)
  have := sq_nonneg (hnorm 1 (PiV (w t)))
  rw [sub_zero] at hle
  linarith

/-- The full dissipation bound. -/
private lemma h2_int (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {ρ t : ℝ}
    (h0 : hnorm 1 (w 0) ≤ ρ) (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < T) :
    ∫ u in (0 : ℝ)..t, hnorm 2 (w u) ^ 2 ≤ Jb ρ φ t := by
  obtain ⟨-, cF, cH, cV⟩ := hw.continuousOn_hnorm hg (σ := 2) (Or.inr (Or.inr rfl)) ht0 ht
  have iF := ii_sq' ht0 cF
  have iH := ii_sq' ht0 cH
  have iV := ii_sq' ht0 cV
  have e : ∫ u in (0 : ℝ)..t, hnorm 2 (w u) ^ 2 =
      (∫ u in (0 : ℝ)..t, hnorm 2 (PiH (w u)) ^ 2) + (∫ u in (0 : ℝ)..t, hnorm 2 (PiV (w u)) ^ 2) +
        ∫ u in (0 : ℝ)..t, hnorm 2 (PiF (w u)) ^ 2 := by
    rw [← intervalIntegral.integral_add iH iV, ← intervalIntegral.integral_add (iH.add iV) iF]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le ht0] at hu
    exact hnorm_sq_three (hw.adm u hu.1 (lt_of_le' hu.2 ht)).inH
  have ad := hw.adm 0 le_rfl (lt_of_le' ht0 ht)
  have hb := sq_le_of (hnorm_nonneg _ _)
    (sectors_le (s := 1) (ad.inH.mono (by norm_num))).2.2 h0
  have hF : ∫ u in (0 : ℝ)..t, hnorm 2 (PiF (w u)) ^ 2 ≤
      ρ ^ 2 * (1 + CF ^ 2 * ρ ^ 2 / 2 * Real.exp (CF ^ 2 * ρ ^ 2 / 2)) := by
    refine (hw.fast_h2_integral hg le_rfl ht0 ht).trans ?_
    gcongr
  have hH := horiz_int hg hφ hw h0 ht0 ht
  have hV := vert_int hg hφ hw h0 ht0 ht
  unfold Jb
  rw [e]
  linarith

/-- The `H²` bound: Gronwall on `h2_ineq` with `𝒜 ≤ c₄ ‖·‖₂`. -/
private lemma h2_sup (hg : Adm 2 g) (hg1 : hnorm 1 g ≤ φ) (hw : RefSol g T w) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 2 (w t) ^ 2 ≤ (hnorm 2 (w 0) ^ 2 + 2 * φ ^ 2 * t) *
      Real.exp (128 * c4 ^ 2 * ∫ u in (0 : ℝ)..t, hnorm 2 (w u) ^ 2) := by
  have G' : GoodForce (fun _ => PiS g) φ :=
    let G := goodForce_PiS hg
    ⟨G.adm, fun t => (G.bd t).trans hg1, G.cont⟩
  have hc := (hw.continuousOn_hnorm hg (σ := 2) (Or.inr (Or.inr rfl)) ht0 ht).1
  have hi := ii_sq' ht0 hc
  have step : ∀ s t', 0 ≤ s → s ≤ t' → t' ≤ t → hnorm 2 (w t') ^ 2 ≤ hnorm 2 (w s) ^ 2 +
      ∫ u in s..t', (128 * c4 ^ 2 * hnorm 2 (w u) ^ 2 * hnorm 2 (w u) ^ 2 + 2 * φ ^ 2) := by
    intro s t' hs hst ht'
    have htT := lt_of_le' ht' ht
    have h := h2_ineq majorized_res G' hw hs hst htT
    have hsub : Icc s t' ⊆ Icc 0 t := Icc_subset_Icc hs ht'
    have hc' := hc.mono hsub
    have hR : IntervalIntegrable (fun u => 128 * c4 ^ 2 * hnorm 2 (w u) ^ 2 *
        hnorm 2 (w u) ^ 2 + 2 * φ ^ 2) volume s t' :=
      ContinuousOn.intervalIntegrable (by
        rw [uIcc_of_le hst]
        exact ((continuousOn_const.mul (hc'.pow 2)).mul (hc'.pow 2)).add continuousOn_const)
    have h3 : 0 ≤ ∫ u in s..t', hnorm 3 (w u) ^ 2 :=
      intervalIntegral.integral_nonneg hst fun _ _ => sq_nonneg _
    have hle : ∫ u in s..t', (128 * wiener (w u) ^ 2 * hnorm 2 (w u) ^ 2 + 2 * φ ^ 2) ≤
        ∫ u in s..t', (128 * c4 ^ 2 * hnorm 2 (w u) ^ 2 * hnorm 2 (w u) ^ 2 + 2 * φ ^ 2) := by
      by_cases hi' : IntervalIntegrable
          (fun u => 128 * wiener (w u) ^ 2 * hnorm 2 (w u) ^ 2 + 2 * φ ^ 2) volume s t'
      · refine intervalIntegral.integral_mono_on hst hi' hR fun u hu => ?_
        have hw2 := wiener_le (hw.adm u (hs.trans hu.1) (lt_of_le' hu.2 htT)).mz
        have h1 : wiener (w u) ^ 2 ≤ (c4 * hnorm 2 (w u)) ^ 2 :=
          pow_le_pow_left₀ (wiener_nonneg _) hw2 2
        have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (hnorm 2 (w u)))
        nlinarith
      · rw [intervalIntegral.integral_undef hi']
        exact intervalIntegral.integral_nonneg hst fun u _ => by positivity
    linarith
  have key := gronwall_simple (y := fun u => hnorm 2 (w u) ^ 2)
    (κ := fun u => 128 * c4 ^ 2 * hnorm 2 (w u) ^ 2) (β := fun _ => 2 * φ ^ 2) ht0 (hc.pow 2)
    (hi.const_mul _) (fun _ => by positivity) intervalIntegrable_const (fun _ => by positivity)
    step 0 t le_rfl ht0 le_rfl
  simp only [integral_const'', intervalIntegral.integral_const_mul, sub_zero] at key
  rwa [mul_assoc 2 (φ ^ 2) t]

/-- The elementary absorption time bound. -/
private lemma exp_mul_sq_le {ρ t : ℝ} (hρ : 1 ≤ ρ) (ht : 2 * Real.log ρ ≤ t) :
    Real.exp (-t) * ρ ^ 2 ≤ 1 := by
  have hρ0 : 0 < ρ := by linarith
  have e : ρ ^ 2 = Real.exp (2 * Real.log ρ) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hρ0, Real.rpow_two]
  rw [e, ← Real.exp_add]
  exact Real.exp_le_one_iff.2 (by linarith)

/-- The end-of-window bound. -/
private lemma end_bound (hg : Adm 2 g) (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {ρ t : ℝ}
    (hρ : 1 ≤ ρ) (h0 : hnorm 1 (w 0) ≤ ρ)
    (hT : 3 + max 0 (Real.log (CF * ρ)) + 2 * Real.log ρ ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 1 (w t) ^ 2 ≤ 1 + (1 + φ ^ 2) +
      (1 + φ ^ 2 + 3 * φ ^ 2) * Real.exp (2 * c4 ^ 2 * (1 + φ ^ 2 + φ ^ 2)) := by
  have hlog : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have hmax : 0 ≤ max 0 (Real.log (CF * ρ)) := le_max_left _ _
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 ≤ t := by linarith
  have ht' : ENNReal.ofReal (t - 1) < T := lt_of_le' (by linarith) ht
  have ad0 := hw.adm 0 le_rfl (lt_of_le' ht0 ht)
  have adt := hw.adm t ht0 ht
  have hs := sectors_le (s := 1) (ad0.inH.mono (by norm_num))
  rw [hnorm_sq_three (adt.inH.mono (by norm_num) : InH 1 (w t))]
  have hF := hw.fast_absorb hg hρ (hs.2.2.trans h0) (t := t) (by linarith) ht
  have hF2 : hnorm 1 (PiF (w t)) ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (hnorm_nonneg 1 (PiF (w t))) hF 2
    simpa using this
  have hdec : ∀ a : ℝ, 2 * Real.log ρ ≤ a → 0 ≤ a → ∀ b : ℝ, 0 ≤ b → b ≤ ρ →
      Real.exp (-(a - 0)) * b ^ 2 ≤ 1 := by
    intro a ha _ b hb hbρ
    rw [sub_zero]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hbρ 2) (Real.exp_pos _).le).trans
      (exp_mul_sq_le hρ ha)
  have hH1 := hw.horiz_decay hg hφ le_rfl ht0 ht
  have hH2 := hw.horiz_decay hg hφ le_rfl (by linarith : (0 : ℝ) ≤ t - 1) ht'
  have hV2 := hw.vert_decay hg hφ le_rfl (by linarith : (0 : ℝ) ≤ t - 1) ht'
  have d1 := hdec t (by linarith) ht0 _ (hnorm_nonneg 1 (PiH (w 0))) (hs.1.trans h0)
  have d2 := hdec (t - 1) (by linarith) (by linarith) _ (hnorm_nonneg 1 (PiH (w 0)))
    (hs.1.trans h0)
  have hV1 : InH 1 (PiV (w 0)) := ad0.inH.PiV.mono (by norm_num)
  have hV0 : hnorm 0 (PiV (w 0)) ≤ ρ :=
    (hnorm_mono (by norm_num) hV1).trans (hs.2.1.trans h0)
  have d3 := hdec (t - 1) (by linarith) (by linarith) _ (hnorm_nonneg 0 (PiV (w 0))) hV0
  have hV := hw.vert_uniform hg hφ (A := 1 + φ ^ 2) (B := 1 + φ ^ 2) ht1 ht (by linarith)
    (by linarith)
  linarith

/-- The full energy of the reference decays to the force level. -/
theorem RefSol.energy_bound {g : Field} {T : ℝ≥0∞} {w : ℝ → Field} {φ : ℝ} (hg : Adm 2 g)
    (hφ : hnorm 0 g ≤ φ) (hw : RefSol g T w) {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 0 (w t) ^ 2 ≤ hnorm 0 (w 0) ^ 2 + φ ^ 2 := by
  have c0 := (hw.continuousOn_hnorm hg (σ := 0) (Or.inl rfl) ht0 ht).1
  have c2 := (hw.continuousOn_hnorm hg (σ := 1) (Or.inr (Or.inl rfl)) ht0 ht).1
  have hy : ContinuousOn (fun u => hnorm 0 (w u) ^ 2) (Icc 0 t) := c0.pow 2
  have key := gronwall_decay (y := fun u => hnorm 0 (w u) ^ 2) (lam := 1) (β := φ ^ 2) ht0 one_pos
    (sq_nonneg φ) hy (fun s' t' h1 h2 h3 => ?_) t ht0 le_rfl
  · have he : Real.exp (-1 * (t - 0)) * hnorm 0 (w 0) ^ 2 ≤ hnorm 0 (w 0) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (Real.exp_le_one_iff.2 (by linarith))
    simp only [div_one] at key
    linarith
  · have hsub : Icc s' t' ⊆ Icc 0 t := Icc_subset_Icc h1 h3
    have htT := lt_of_le' h3 ht
    have hmono : ∫ u in s'..t', hnorm 0 (w u) ^ 2 ≤ ∫ u in s'..t', hnorm 1 (w u) ^ 2 := by
      have i0 : IntervalIntegrable (fun u => hnorm 0 (w u) ^ 2) volume s' t' :=
        ii_sq' h2 (c0.mono hsub)
      have i1 : IntervalIntegrable (fun u => hnorm 1 (w u) ^ 2) volume s' t' :=
        ii_sq' h2 (c2.mono hsub)
      refine intervalIntegral.integral_mono_on h2 i0 i1 fun u hu => ?_
      have hi : InH 1 (w u) :=
        InH.mono (by norm_num) (hw.adm u (h1.trans hu.1) (lt_of_le' hu.2 htT)).inH
      have hle : hnorm 0 (w u) ≤ hnorm 1 (w u) := hnorm_mono (by norm_num) hi
      exact pow_le_pow_left₀ (hnorm_nonneg _ _) hle 2
    have := energy_step hg hφ hw h1 h2 htT
    simp only [one_mul]
    linarith

/-- A priori `H¹` control on finite times excludes reference blow-up: the reference is global. -/
theorem exists_refSol_global {g w₀ : Field} (hg : Adm 2 g) (hw₀ : Adm 2 w₀) :
    ∃ w, RefSol g ⊤ w ∧ w 0 = w₀ := by
  obtain ⟨T, y, -, hy, hy0, hmax⟩ := exists_maximal majorized_res (goodForce_PiS hg) hw₀
  by_cases hfin : T = ⊤
  · subst hfin
    exact ⟨y, hy, hy0⟩
  exfalso
  set φ := hnorm 0 g
  set ρ := hnorm 1 w₀
  obtain ⟨C, hC⟩ := h1_bound_excludes_blowup (Real.sqrt (Xsq ρ φ T.toReal)) (hnorm 1 g) T.toReal
    (hnorm 2 w₀)
  refine hmax hfin C (hC _ _ T y majorized_res (goodForce_PiS hg) hy (by rw [hy0])
    (ENNReal.ofReal_toReal hfin).ge fun t ht0 ht ↦ ?_)
  have htb : t ≤ T.toReal := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal ht0 hfin).1 ht
    exact this.le
  have h := h1_bound hg (le_refl φ) hy (ρ := ρ) (by rw [hy0]) ht0 ht
  refine Real.le_sqrt_of_sq_le (h.trans ?_)
  unfold Xsq
  linarith [Yz_mono ρ φ ht0 htb]

/-- The window theorem for the reference.  The chain of constants is
`φ → ρ_end`, then `ρ → T, X, E, J`, then `S → Y`.  `ρ_end` is independent of `ρ`. -/
theorem ref_absorption (φ : ℝ) (hφ : 0 ≤ φ) :
    ∃ ρend : ℝ, 0 ≤ ρend ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∃ T X E J : ℝ, 2 ≤ T ∧ 0 ≤ X ∧ 0 ≤ E ∧ 0 ≤ J ∧ ∀ S : ℝ, ∃ Y : ℝ, 0 ≤ Y ∧
        ∀ (g w : Field) (w' : ℝ → Field), Adm 2 g → hnorm 2 g ≤ φ →
          RefSol g ⊤ w' → w' 0 = w → hnorm 1 w ≤ ρ → hnorm 2 w ≤ S →
          (∀ t ∈ Icc 0 T, hnorm 1 (w' t) ≤ X ∧ hnorm 0 (w' t) ^ 2 ≤ E ∧ hnorm 2 (w' t) ≤ Y) ∧
          (∫ t in (0 : ℝ)..T, hnorm 2 (w' t) ^ 2) ≤ J ∧
          hnorm 1 (w' T) ≤ ρend := by
  have _ := hφ
  refine ⟨Real.sqrt (1 + (1 + φ ^ 2) +
    (1 + φ ^ 2 + 3 * φ ^ 2) * Real.exp (2 * c4 ^ 2 * (1 + φ ^ 2 + φ ^ 2))),
    Real.sqrt_nonneg _, fun ρ hρ ↦ ?_⟩
  set T : ℝ := 3 + max 0 (Real.log (CF * ρ)) + 2 * Real.log ρ with hTdef
  have hlog : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have hmax : 0 ≤ max 0 (Real.log (CF * ρ)) := le_max_left _ _
  have hT0 : 0 ≤ T := by linarith
  refine ⟨T, Real.sqrt (Xsq ρ φ T), ρ ^ 2 + φ ^ 2, Jb ρ φ T, by linarith, Real.sqrt_nonneg _,
    by positivity, Jb_nonneg ρ φ hT0, fun S ↦ ⟨Real.sqrt ((S ^ 2 + 2 * φ ^ 2 * T) *
      Real.exp (128 * c4 ^ 2 * Jb ρ φ T)), Real.sqrt_nonneg _, ?_⟩⟩
  intro g w₀ w hg hg2 hw hw0 h1 h2
  subst hw0
  have hg1 : hnorm 1 g ≤ φ := (hnorm_mono (by norm_num) hg.inH).trans hg2
  have hg0 : hnorm 0 g ≤ φ := (hnorm_mono (by norm_num) hg.inH).trans hg2
  have hlt : ∀ t : ℝ, ENNReal.ofReal t < ⊤ := fun _ ↦ ENNReal.ofReal_lt_top
  have ad0 := hw.adm 0 le_rfl (hlt 0)
  refine ⟨fun t ht ↦ ⟨?_, ?_, ?_⟩, h2_int hg hg0 hw h1 hT0 (hlt T), ?_⟩
  · have h := h1_bound hg hg0 hw h1 ht.1 (hlt t)
    refine Real.le_sqrt_of_sq_le (h.trans ?_)
    unfold Xsq
    linarith [Yz_mono ρ φ ht.1 ht.2]
  · have h := hw.energy_bound hg hg0 ht.1 (hlt t)
    have ad01 : InH 1 (w 0) := ad0.inH.mono (by norm_num)
    have h3 : hnorm 0 (w 0) ^ 2 ≤ ρ ^ 2 :=
      sq_le_of (hnorm_nonneg _ _) (hnorm_mono (by norm_num) ad01) h1
    linarith
  · have hsup := h2_sup hg hg1 hw ht.1 (hlt t)
    have hJ2 : ∫ u in (0 : ℝ)..t, hnorm 2 (w u) ^ 2 ≤ Jb ρ φ T := by
      have c := (hw.continuousOn_hnorm hg (σ := 2) (Or.inr (Or.inr rfl)) hT0 (hlt T)).1
      have hm := intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := T) (a := 0) (b := t)
        (f := fun u ↦ hnorm 2 (w u) ^ 2) le_rfl ht.1 ht.2
        (Eventually.of_forall fun _ ↦ sq_nonneg _) (ii_sq' hT0 c)
      exact hm.trans (h2_int hg hg0 hw h1 hT0 (hlt T))
    refine Real.le_sqrt_of_sq_le (hsup.trans ?_)
    have : 0 ≤ S ^ 2 + 2 * φ ^ 2 * T := by positivity
    have h3 : hnorm 2 (w 0) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) h2 2
    have ht2 := ht.2
    have ht1 := ht.1
    gcongr
  · exact Real.le_sqrt_of_sq_le (end_bound hg hg0 hw hρ h1 le_rfl (hlt T))

end OVNS
