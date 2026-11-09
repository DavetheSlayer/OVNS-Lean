import OddViscousNS.RefSector

/-! # The fast sector of the reference (`Proposition fg:prop:fast`) -/

open MeasureTheory Set intervalIntegral
open scoped ENNReal
noncomputable section
namespace OVNS

variable {g : Field} {T : ℝ≥0∞} {w : ℝ → Field}

/-- The pairing is odd in the second slot. -/
private lemma pair_neg (σ : ℝ) (c F : Field) : pair σ c (-F) = -pair σ c F := by
  simp only [pair, Pi.neg_apply, inner_neg_right, Complex.neg_re, mul_neg, tsum_neg]

/-- `Π_F` is idempotent. -/
private lemma PiF_idem (u : Field) : PiF (PiF u) = PiF u := by
  ext1 k
  by_cases h : k 2 = 0 <;> simp [PiF, h]

/-- `Π_S` is idempotent. -/
private lemma PiS_idem (u : Field) : PiS (PiS u) = PiS u := by
  ext1 k
  by_cases h : k 2 = 0 <;> simp [PiS, h]

/-- Tested against the fast part, only the fast-fast-fast interaction survives. -/
private lemma pair_fast_force {v : Field} (hv : Adm 2 v) {σ : ℝ} (hσ : σ = 0 ∨ σ = 1) :
    pair σ (PiF v) (-PiF (Qres v v)) = -pair σ (PiF v) (Qres (PiF v) (PiF v)) := by
  have hf : Adm 2 (PiF v) := hv.PiF
  have hs : Adm 2 (PiS v) := hv.PiS
  have hσ1 : σ + 1 ≤ 2 ∧ σ - 1 ≤ 2 - 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hc : InH (σ + 1) (PiF v) := hf.inH.mono hσ1.1
  have hq : ∀ {a b : Field}, Adm 2 a → Adm 2 b → InH (σ - 1) (Qres a b) := fun ha hb =>
    (hnorm_Qm_le resM_bdd (σ := 2) (by norm_num) ⟨ha.inH, ha.mean⟩ ⟨hb.inH, hb.mean⟩
      ⟨ha.inH, ha.mean⟩ ⟨hb.inH, hb.mean⟩).1.mono hσ1.2
  rw [PiF_Qres hv, pair_neg, two_smul, pair_add hc ((hq hs hf).add (hq hs hf)) (hq hf hf),
    pair_add hc (hq hs hf) (hq hs hf), cat_neutral hs hf (PiS_idem v) (PiF_idem v) hσ]
  ring

/-- Earlier times lie in the lifespan. -/
private lemma ofReal_lt_of_le' {u t : ℝ} (hut : u ≤ t) (ht : ENNReal.ofReal t < T) :
    ENNReal.ofReal u < T :=
  (ENNReal.ofReal_le_ofReal hut).trans_lt ht

/-- The fast part in `H²` at intermediate times. -/
private lemma fast_adm (hw : RefSol g T w) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t)
    (ht : ENNReal.ofReal t < T) : Adm 2 (PiF (w u)) :=
  (hw.adm u hu (ofReal_lt_of_le' hut ht)).PiF

/-- `‖f‖₀² ≤ ‖f‖₁²` for the fast part. -/
private lemma fast_zero_le_one (hw : RefSol g T w) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t)
    (ht : ENNReal.ofReal t < T) : hnorm 0 (PiF (w u)) ^ 2 ≤ hnorm 1 (PiF (w u)) ^ 2 :=
  pow_le_pow_left₀ (hnorm_nonneg _ _)
    (hnorm_mono (by norm_num) ((fast_adm hw hu hut ht).inH.mono (by norm_num))) 2

/-- Norms of the fast part are continuous on subintervals. -/
private lemma fast_contOn (hg : Adm 2 g) (hw : RefSol g T w) {σ s t : ℝ}
    (hσ : σ = 0 ∨ σ = 1 ∨ σ = 2) (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    ContinuousOn (fun u => hnorm σ (PiF (w u))) (Icc s t) :=
  (hw.continuousOn_hnorm hg hσ (hs.trans hst) ht).2.1.mono (Icc_subset_Icc_left hs)

/-- Squared norms of the fast part are continuous on subintervals. -/
private lemma fast_sq_contOn (hg : Adm 2 g) (hw : RefSol g T w) {σ s t : ℝ}
    (hσ : σ = 0 ∨ σ = 1 ∨ σ = 2) (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    ContinuousOn (fun u => hnorm σ (PiF (w u)) ^ 2) (Icc s t) :=
  fun u hu => ((fast_contOn hg hw hσ hs hst ht) u hu).pow 2

/-- Squared norms of the fast part are integrable. -/
private lemma fast_ii (hg : Adm 2 g) (hw : RefSol g T w) {σ s t : ℝ}
    (hσ : σ = 0 ∨ σ = 1 ∨ σ = 2) (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    IntervalIntegrable (fun u => hnorm σ (PiF (w u)) ^ 2) volume s t :=
  (fast_sq_contOn hg hw hσ hs hst ht).intervalIntegrable_of_Icc hst

/-- The quartic term is integrable. -/
private lemma fast_ii_four (hg : Adm 2 g) (hw : RefSol g T w) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    IntervalIntegrable (fun u => hnorm 1 (PiF (w u)) ^ 2 * hnorm 1 (PiF (w u)) ^ 2) volume s t :=
  have h := fast_sq_contOn hg hw (σ := 1) (Or.inr (Or.inl rfl)) hs hst ht
  (h.mul h).intervalIntegrable_of_Icc hst

/-- The fast `L²` energy identity: `‖f(t)‖₀² + 2∫‖f‖₁² = ‖f(s)‖₀²`. -/
theorem RefSol.fast_energy (hg : Adm 2 g) (hw : RefSol g T w) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < T) :
    hnorm 0 (PiF (w t)) ^ 2 + 2 * ∫ u in s..t, hnorm 1 (PiF (w u)) ^ 2 =
      hnorm 0 (PiF (w s)) ^ 2 := by
  have hP := hw.heatPair_fast hg (σ := 0) (Or.inl rfl) (hs.trans hst) ht
  have hid := hP.energy_identity hs hst le_rfl
  have hz : ∀ u ∈ uIcc s t, pair 0 (PiF (w u)) (-PiF (Qres (w u) (w u))) = 0 := fun u hu => by
    rw [uIcc_of_le hst] at hu
    have hv := hw.adm u (hs.trans hu.1) (ofReal_lt_of_le' hu.2 ht)
    rw [pair_fast_force hv (Or.inl rfl), pair_Qres_fast hv.PiF (PiF_idem _), neg_zero]
  simp only [zero_add] at hid
  rw [intervalIntegral.integral_congr hz] at hid
  simpa using hid

/-- Half the dissipation integral is controlled by the initial `L²` energy. -/
private lemma fast_int_le (hg : Adm 2 g) (hw : RefSol g T w) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < T) :
    ∫ u in s..t, hnorm 1 (PiF (w u)) ^ 2 ≤ hnorm 1 (PiF (w s)) ^ 2 / 2 := by
  have h := hw.fast_energy hg hs hst ht
  have h' := fast_zero_le_one hw hs hst ht
  linarith [sq_nonneg (hnorm 0 (PiF (w t)))]

/-- Exponential decay of the fast `L²` energy. -/
theorem RefSol.fast_decay (hg : Adm 2 g) (hw : RefSol g T w) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < T) :
    hnorm 0 (PiF (w t)) ^ 2 ≤ Real.exp (-2 * (t - s)) * hnorm 0 (PiF (w s)) ^ 2 := by
  have h := gronwall_decay (y := fun u => hnorm 0 (PiF (w u)) ^ 2) (lam := 2) (β := 0) hst
    two_pos le_rfl (fast_sq_contOn hg hw (Or.inl rfl) hs hst ht) (fun s' t' hs' hst' ht' => by
      have hs0 := hs.trans hs'
      have ht0 := ofReal_lt_of_le' ht' ht
      have e := hw.fast_energy hg hs0 hst' ht0
      have m := intervalIntegral.integral_mono_on hst'
        (fast_ii hg hw (Or.inl rfl) hs0 hst' ht0)
        (fast_ii hg hw (Or.inr (Or.inl rfl)) hs0 hst' ht0)
        (fun u hu => fast_zero_le_one hw (hs0.trans hu.1) hu.2 ht0)
      linarith) t hst le_rfl
  simpa only [zero_div, add_zero] using h

/-- The basic `H¹` inequality: with `a = ‖f‖₁`, `b = ‖f‖₂`,
`a²(t) + ∫b² ≤ a²(s) + C_F² ∫a⁴`. -/
private lemma fast_key (hg : Adm 2 g) (hw : RefSol g T w) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < T) :
    hnorm 1 (PiF (w t)) ^ 2 + ∫ u in s..t, hnorm 2 (PiF (w u)) ^ 2 ≤
      hnorm 1 (PiF (w s)) ^ 2 +
        CF ^ 2 * ∫ u in s..t, hnorm 1 (PiF (w u)) ^ 2 * hnorm 1 (PiF (w u)) ^ 2 := by
  have hP := hw.heatPair_fast hg (σ := 1) (Or.inr rfl) (hs.trans hst) ht
  have hid := hP.energy_identity hs hst le_rfl
  rw [show (1 : ℝ) + 1 = 2 by norm_num] at hid
  have hpt : ∀ u ∈ Icc s t, pair 1 (PiF (w u)) (-PiF (Qres (w u) (w u))) ≤
      (1 / 2) * hnorm 2 (PiF (w u)) ^ 2 +
        (1 / 2 * CF ^ 2) * (hnorm 1 (PiF (w u)) ^ 2 * hnorm 1 (PiF (w u)) ^ 2) := fun u hu => by
    have hv := hw.adm u (hs.trans hu.1) (ofReal_lt_of_le' hu.2 ht)
    rw [pair_fast_force hv (Or.inr rfl)]
    have h1 := flux_le hv.PiF (PiF_idem _)
    have h2 := neg_le_abs (pair 1 (PiF (w u)) (Qres (PiF (w u)) (PiF (w u))))
    nlinarith [sq_nonneg (hnorm 2 (PiF (w u)) - CF * hnorm 1 (PiF (w u)) ^ 2)]
  have hb := (fast_ii hg hw (σ := 2) (Or.inr (Or.inr rfl)) hs hst ht).const_mul (1 / 2)
  have ha := (fast_ii_four hg hw hs hst ht).const_mul (1 / 2 * CF ^ 2)
  have hI := intervalIntegral.integral_mono_on hst
    ((hP.mono hs le_rfl).intervalIntegrable_pair hst) (hb.add ha) hpt
  rw [intervalIntegral.integral_add hb ha, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hI
  linarith

/-- The fast `H¹` bound of `Theorem thm:limit`, from any starting time. -/
theorem RefSol.fast_h1 (hg : Adm 2 g) (hw : RefSol g T w) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < T) :
    hnorm 1 (PiF (w t)) ^ 2 ≤
      hnorm 1 (PiF (w s)) ^ 2 * Real.exp (CF ^ 2 * hnorm 1 (PiF (w s)) ^ 2 / 2) := by
  have hone : (1 : ℝ) = 0 ∨ (1 : ℝ) = 1 ∨ (1 : ℝ) = 2 := Or.inr (Or.inl rfl)
  have h := gronwall_simple (y := fun u => hnorm 1 (PiF (w u)) ^ 2)
    (κ := fun u => CF ^ 2 * hnorm 1 (PiF (w u)) ^ 2) (β := fun _ => 0) hst
    (fast_sq_contOn hg hw hone hs hst ht) ((fast_ii hg hw hone hs hst ht).const_mul _)
    (fun u => by positivity) intervalIntegrable_const (fun _ => le_rfl)
    (fun s' t' hs' hst' ht' => by
      have hs0 := hs.trans hs'
      have ht0 := ofReal_lt_of_le' ht' ht
      have k := fast_key hg hw hs0 hst' ht0
      have nn : 0 ≤ ∫ u in s'..t', hnorm 2 (PiF (w u)) ^ 2 :=
        intervalIntegral.integral_nonneg hst' fun _ _ => sq_nonneg _
      simp only [add_zero, mul_assoc, intervalIntegral.integral_const_mul]
      linarith) s t le_rfl hst le_rfl
  simp only [intervalIntegral.integral_zero, add_zero, intervalIntegral.integral_const_mul] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (sq_nonneg _))
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (fast_int_le hg hw hs hst ht) (sq_nonneg _)

/-- The fast dissipation bound on any interval. -/
theorem RefSol.fast_h2_integral (hg : Adm 2 g) (hw : RefSol g T w) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    ∫ u in s..t, hnorm 2 (PiF (w u)) ^ 2 ≤
      hnorm 1 (PiF (w s)) ^ 2 * (1 + CF ^ 2 * hnorm 1 (PiF (w s)) ^ 2 / 2 *
        Real.exp (CF ^ 2 * hnorm 1 (PiF (w s)) ^ 2 / 2)) := by
  have hone : (1 : ℝ) = 0 ∨ (1 : ℝ) = 1 ∨ (1 : ℝ) = 2 := Or.inr (Or.inl rfl)
  have k := fast_key hg hw hs hst ht
  have hA := fast_ii hg hw hone hs hst ht
  have m := intervalIntegral.integral_mono_on hst (fast_ii_four hg hw hs hst ht)
    (hA.const_mul (hnorm 1 (PiF (w s)) ^ 2 * Real.exp (CF ^ 2 * hnorm 1 (PiF (w s)) ^ 2 / 2)))
    (fun u hu => mul_le_mul_of_nonneg_right
      (hw.fast_h1 hg hs hu.1 (ofReal_lt_of_le' hu.2 ht)) (sq_nonneg _))
  rw [intervalIntegral.integral_const_mul] at m
  have hE : 0 ≤ hnorm 1 (PiF (w s)) ^ 2 * Real.exp (CF ^ 2 * hnorm 1 (PiF (w s)) ^ 2 / 2) := by
    positivity
  have m' := m.trans (mul_le_mul_of_nonneg_left (fast_int_le hg hw hs hst ht) hE)
  have m'' := mul_le_mul_of_nonneg_left m' (sq_nonneg CF)
  have hb : ∫ u in s..t, hnorm 2 (PiF (w u)) ^ 2 ≤ hnorm 1 (PiF (w s)) ^ 2 + CF ^ 2 *
      (hnorm 1 (PiF (w s)) ^ 2 * Real.exp (CF ^ 2 * hnorm 1 (PiF (w s)) ^ 2 / 2) *
        (hnorm 1 (PiF (w s)) ^ 2 / 2)) := by
    linarith [sq_nonneg (hnorm 1 (PiF (w t)))]
  refine hb.trans (le_of_eq ?_)
  ring

/-- A continuous function on a unit interval is somewhere at most its integral. -/
private lemma exists_le_integral {y : ℝ → ℝ} {a : ℝ} (hy : ContinuousOn y (Icc a (a + 1))) :
    ∃ s ∈ Icc a (a + 1), y s ≤ ∫ u in a..(a + 1), y u := by
  have hle : a ≤ a + 1 := by linarith
  obtain ⟨s, hs, hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hle) hy
  refine ⟨s, hs, ?_⟩
  have h := intervalIntegral.integral_mono_on hle
    (intervalIntegrable_const (μ := volume) (c := y s))
    (hy.intervalIntegrable_of_Icc hle) (fun u hu => hm hu)
  simpa using h

/-- The value of `C_F²`. -/
private lemma CF_sq : CF ^ 2 = 86400 := by
  rw [CF, mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- After time `t ≥ log(C_F ρ)`, the fast `L²` energy is at most `C_F⁻²`. -/
private lemma fast_small (hg : Adm 2 g) (hw : RefSol g T w) {ρ t : ℝ} (hρ : 1 ≤ ρ)
    (h0 : hnorm 1 (PiF (w 0)) ≤ ρ) (ht0 : 0 ≤ t) (hlog : Real.log (CF * ρ) ≤ t)
    (ht : ENNReal.ofReal t < T) : hnorm 0 (PiF (w t)) ^ 2 ≤ 1 / 86400 := by
  have hd := hw.fast_decay hg le_rfl ht0 ht
  have he := fast_zero_le_one hw le_rfl ht0 ht
  have hρ2 : hnorm 1 (PiF (w 0)) ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) h0 2
  have hx : 0 < CF * ρ := mul_pos CF_pos (by linarith)
  have hle : CF * ρ ≤ Real.exp t := (Real.log_le_iff_le_exp hx).1 hlog
  have hq : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hq0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hexp : Real.exp (-2 * (t - 0)) = Real.exp (-t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hqx : (Real.exp (-t) * (CF * ρ)) ^ 2 ≤ 1 := by
    refine pow_le_one₀ (by positivity) ?_
    rw [← hq]
    exact mul_le_mul_of_nonneg_left hle hq0.le
  have hmul : Real.exp (-t) ^ 2 * hnorm 0 (PiF (w 0)) ^ 2 ≤ Real.exp (-t) ^ 2 * ρ ^ 2 :=
    mul_le_mul_of_nonneg_left (he.trans hρ2) (by positivity)
  rw [hexp] at hd
  have hc := CF_sq
  have hfin : Real.exp (-t) ^ 2 * ρ ^ 2 * 86400 ≤ 1 := by
    rw [← hc]
    calc _ = (Real.exp (-t) * (CF * ρ)) ^ 2 := by ring
      _ ≤ 1 := hqx
  linarith

/-- Absorption: if `‖f(0)‖₁ ≤ ρ` then `‖f(t)‖₁ ≤ 1` once `t ≥ 2 + log₊(C_F ρ)`. -/
theorem RefSol.fast_absorb (hg : Adm 2 g) (hw : RefSol g T w) {ρ t : ℝ} (hρ : 1 ≤ ρ)
    (h0 : hnorm 1 (PiF (w 0)) ≤ ρ) (ht : 2 + max 0 (Real.log (CF * ρ)) ≤ t)
    (htT : ENNReal.ofReal t < T) : hnorm 1 (PiF (w t)) ≤ 1 := by
  have hm0 := le_max_left 0 (Real.log (CF * ρ))
  have hm1 := le_max_right 0 (Real.log (CF * ρ))
  have hone : (1 : ℝ) = 0 ∨ (1 : ℝ) = 1 ∨ (1 : ℝ) = 2 := Or.inr (Or.inl rfl)
  have hs0 : 0 ≤ t - 2 := by linarith
  have hle1 : t - 2 ≤ t - 2 + 1 := by linarith
  have hle2 : t - 2 + 1 ≤ t := by linarith
  have ht1 := ofReal_lt_of_le' hle2 htT
  have hsm := fast_small hg hw hρ h0 hs0 (by linarith) (ofReal_lt_of_le' (by linarith) htT)
  obtain ⟨s, hs, hsI⟩ := exists_le_integral (y := fun u => hnorm 1 (PiF (w u)) ^ 2)
    (fast_sq_contOn hg hw hone hs0 hle1 ht1)
  have hI := hw.fast_energy hg hs0 hle1 ht1
  have hX : hnorm 1 (PiF (w s)) ^ 2 ≤ 1 / 172800 := by
    linarith [sq_nonneg (hnorm 0 (PiF (w (t - 2 + 1))))]
  have hst := hw.fast_h1 hg (hs0.trans hs.1) (hs.2.trans hle2) htT
  rw [CF_sq] at hst
  have hexp : Real.exp (86400 * hnorm 1 (PiF (w s)) ^ 2 / 2) ≤ 3 := by
    have h1 : 86400 * hnorm 1 (PiF (w s)) ^ 2 / 2 ≤ 1 := by linarith
    have h2 := Real.exp_le_exp.2 h1
    linarith [Real.exp_one_lt_d9]
  have hfin : hnorm 1 (PiF (w t)) ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hexp (sq_nonneg (hnorm 1 (PiF (w s))))
    linarith
  exact (sq_le_one_iff₀ (hnorm_nonneg _ _)).1 hfin

end OVNS
