import OddViscousNS.Helical

/-! # Faithfulness sanity checks for the anchor (Phase A5)

* Vacuity: `u ≡ 0` is admissible and solves the system.
* Small instance that must HOLD: the decaying Kolmogorov flow `u = A e^{-νt}(sin x₂, 0, 0)` is an
  exact solution for every `α` (since `k₃ = 0`, `L` vanishes, and `(u·∇)u = 0`).
* Perturbation that must FAIL: the same flow decaying at the wrong rate `2ν`. -/

open Set
noncomputable section
namespace OVNS

/-- The wave vector `e₂`. -/
def e2M : Mode := ![0, 1, 0]

/-- `û_{±e₂}(t) = ∓(i/2) A e^{-c t} e₁`, the coefficients of `A e^{-ct}(sin x₂, 0, 0)`. -/
def kolm (A c t : ℝ) : Field := by
  classical
  exact fun k =>
    if k = e2M then ((-(Complex.I / 2) * A * Real.exp (-c * t) : ℂ)) • WithLp.toLp 2 ![1, 0, 0]
    else if k = -e2M then ((Complex.I / 2) * A * Real.exp (-c * t) : ℂ) • WithLp.toLp 2 ![1, 0, 0]
    else 0

/-- The unit vector `e₁`. -/
private def e1V : V3 := WithLp.toLp 2 ![1, 0, 0]

/-- The time-independent profile: `∓(i/2) e₁` at `±e₂`, zero elsewhere. -/
private def prof (k : Mode) : V3 := by
  classical
  exact if k = e2M then (-(Complex.I / 2) : ℂ) • e1V
    else if k = -e2M then (Complex.I / 2 : ℂ) • e1V else 0

/-- The amplitude `A e^{-ct}`. -/
private def amp (A c t : ℝ) : ℝ := A * Real.exp (-c * t)

private lemma e2M_ne_neg : e2M ≠ -e2M := by
  intro h
  have := congrFun h 1
  simp [e2M] at this

private lemma e2M_ne_zero : e2M ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [e2M] at this

private lemma neg_e2M_ne_zero : -e2M ≠ 0 := by
  simpa using e2M_ne_zero

private lemma prof_e2M : prof e2M = (-(Complex.I / 2) : ℂ) • e1V := by
  simp [prof]

private lemma prof_neg_e2M : prof (-e2M) = (Complex.I / 2 : ℂ) • e1V := by
  simp [prof, e2M_ne_neg.symm]

private lemma prof_other {k : Mode} (h : k ≠ e2M) (h' : k ≠ -e2M) : prof k = 0 := by
  simp [prof, h, h']

private lemma kolm_eq (A c t : ℝ) : kolm A c t = ((amp A c t : ℝ) : ℂ) • prof := by
  funext k
  by_cases h : k = e2M
  · subst h
    rw [Pi.smul_apply, prof_e2M, smul_smul]
    simp only [kolm, amp, ↓reduceIte, e1V]
    congr 1
    push_cast
    ring
  · by_cases h' : k = -e2M
    · subst h'
      rw [Pi.smul_apply, prof_neg_e2M, smul_smul]
      simp only [kolm, amp, e2M_ne_neg.symm, ↓reduceIte, e1V]
      congr 1
      push_cast
      ring
    · rw [Pi.smul_apply, prof_other h h', smul_zero]
      simp [kolm, h, h']

private lemma dotM_expand (v : V3) (k : Mode) :
    dotM v k = v 0 * (k 0 : ℂ) + v 1 * (k 1 : ℂ) + v 2 * (k 2 : ℂ) := by
  simp [dotM, Fin.sum_univ_three]

private lemma prof_one (k : Mode) : prof k 1 = 0 := by
  by_cases h : k = e2M
  · subst h; simp [prof_e2M, e1V]
  · by_cases h' : k = -e2M
    · subst h'; simp [prof_neg_e2M, e1V]
    · simp [prof_other h h']

private lemma prof_two (k : Mode) : prof k 2 = 0 := by
  by_cases h : k = e2M
  · subst h; simp [prof_e2M, e1V]
  · by_cases h' : k = -e2M
    · subst h'; simp [prof_neg_e2M, e1V]
    · simp [prof_other h h']

private lemma dotM_prof_smul (p q : Mode) : dotM (prof p) q • prof q = 0 := by
  by_cases h : q = e2M
  · subst h
    have : dotM (prof p) e2M = 0 := by
      simp [dotM_expand, prof_one, prof_two, e2M]
    rw [this, zero_smul]
  · by_cases h' : q = -e2M
    · subst h'
      have : dotM (prof p) (-e2M) = 0 := by
        simp [dotM_expand, prof_one, prof_two, e2M]
      rw [this, zero_smul]
    · rw [prof_other h h', smul_zero]

private lemma prof_sol : IsSolenoidal prof := by
  intro k
  by_cases h : k = e2M
  · subst h; rw [prof_e2M]; simp [dotM_expand, e1V, e2M]
  · by_cases h' : k = -e2M
    · subst h'; rw [prof_neg_e2M]; simp [dotM_expand, e1V, e2M]
    · simp [prof_other h h', dotM_expand]

private lemma conjV_e1 : conjV e1V = e1V := by
  ext i
  fin_cases i <;> simp [conjV, e1V]

private lemma conjV_real_smul (a : ℝ) (v : V3) : conjV ((a : ℂ) • v) = (a : ℂ) • conjV v := by
  ext i
  simp [conjV]

private lemma conjV_smul' (c : ℂ) (v : V3) : conjV (c • v) = (starRingEnd ℂ c) • conjV v := by
  ext i
  simp [conjV]

private lemma conj_half_I : starRingEnd ℂ (Complex.I / 2) = -(Complex.I / 2) := by
  have h : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [map_div₀, Complex.conj_I, h, Complex.conj_ofReal]
  ring

private lemma prof_real : IsReal prof := by
  intro k
  by_cases h : k = e2M
  · subst h
    rw [prof_neg_e2M, prof_e2M, conjV_smul', conjV_e1, map_neg, conj_half_I, neg_neg]
  · by_cases h' : k = -e2M
    · subst h'
      rw [neg_neg, prof_e2M, prof_neg_e2M, conjV_smul', conjV_e1, conj_half_I]
    · have h1 : -k ≠ e2M := fun e => h' (by rw [← e, neg_neg])
      have h2 : -k ≠ -e2M := fun e => h (neg_injective e)
      rw [prof_other h1 h2, prof_other h h']
      ext i
      simp [conjV]

private lemma prof_zero : prof 0 = 0 :=
  prof_other e2M_ne_zero.symm neg_e2M_ne_zero.symm

private lemma prof_inH (s : ℝ) : InH s prof := by
  refine summable_of_ne_finset_zero (s := {e2M, -e2M}) fun k hk => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [prof_other hk.1 hk.2]

private lemma absSq_e2M : absSq e2M = 1 := by
  simp [absSq, e2M, Fin.sum_univ_three]

private lemma absSq_smul_prof (k : Mode) : (absSq k : ℂ) • prof k = prof k := by
  by_cases h : k = e2M
  · subst h; simp [absSq_e2M]
  · by_cases h' : k = -e2M
    · subst h'; simp [absSq_neg, absSq_e2M]
    · simp [prof_other h h']

private lemma leray_cross_e1 (c : ℂ) : leray e2M (cross e3 (c • e1V)) = 0 := by
  simp only [leray, e2M_ne_zero, ↓reduceIte, absSq_e2M]
  ext i
  fin_cases i <;> simp [dotM_expand, cross, e3, e1V, modeVec, e2M]

private lemma leray_cross_e1' (c : ℂ) : leray (-e2M) (cross e3 (c • e1V)) = 0 := by
  simp only [leray, neg_e2M_ne_zero, ↓reduceIte, absSq_neg, absSq_e2M]
  ext i
  fin_cases i <;> simp [dotM_expand, cross, e3, e1V, modeVec, e2M]

private lemma oddSym_prof (k : Mode) : oddSym k (prof k) = 0 := by
  by_cases h : k = e2M
  · subst h
    rw [oddSym, prof_e2M, smul_smul]
    exact leray_cross_e1 _
  · by_cases h' : k = -e2M
    · subst h'
      rw [oddSym, prof_neg_e2M, smul_smul]
      exact leray_cross_e1' _
    · have hc : cross e3 0 = 0 := by
        ext i
        fin_cases i <;> simp [cross]
      have hl : leray k 0 = 0 := by
        by_cases hk : k = 0
        · simp [leray, hk]
        · simp [leray, hk, dotM]
      simp [oddSym, prof_other h h', hc, hl]

private lemma oddSym_smul' (k : Mode) (c : ℂ) (v : V3) :
    oddSym k (c • v) = c • oddSym k v := by
  simp only [oddSym, smul_comm _ c v, cross_smul_right, leray_smul]

private lemma convec_smul_prof (a : ℂ) (k : Mode) : convec (a • prof) k = 0 := by
  have h : advect (a • prof) (a • prof) k = 0 := by
    have : ∀ p : Mode, (Complex.I * dotM ((a • prof) p) (k - p)) • (a • prof) (k - p) = 0 := by
      intro p
      simp only [Pi.smul_apply, dotM_smul]
      have h0 := dotM_prof_smul p (k - p)
      calc (Complex.I * (a * dotM (prof p) (k - p))) • a • prof (k - p)
          = (Complex.I * a * a) • (dotM (prof p) (k - p) • prof (k - p)) := by
            simp only [smul_smul]
            ring_nf
        _ = 0 := by rw [h0, smul_zero]
    rw [advect]
    exact (tsum_congr this).trans tsum_zero
  have hl : leray k 0 = 0 := by
    by_cases hk : k = 0
    · simp [leray, hk]
    · simp [leray, hk, dotM]
  rw [convec, h, hl]

private lemma kolm_rhs (A c ν α t : ℝ) (k : Mode) :
    ((-(ν * absSq k : ℝ) : ℂ) • kolm A c t k + (α : ℂ) • oddSym k (kolm A c t k) -
      convec (kolm A c t) k + (0 : Field) k) = ((-ν * amp A c t : ℝ) : ℂ) • prof k := by
  rw [kolm_eq, convec_smul_prof, Pi.smul_apply, oddSym_smul', oddSym_prof, smul_zero,
    smul_zero, smul_smul]
  have : (-((ν * absSq k : ℝ) : ℂ) * (amp A c t : ℂ)) • prof k =
      ((-ν * amp A c t : ℝ) : ℂ) • ((absSq k : ℂ) • prof k) := by
    rw [smul_smul]
    congr 1
    push_cast
    ring
  rw [this, absSq_smul_prof]
  simp

private lemma amp_hasDeriv (A c t : ℝ) : HasDerivAt (amp A c) (-c * amp A c t) t := by
  have h1 : HasDerivAt (fun s : ℝ => -c * s) (-c) t := by
    simpa using (hasDerivAt_id t).const_mul (-c)
  have h2 := (h1.exp).const_mul A
  have h3 : -c * amp A c t = A * (Real.exp (-c * t) * -c) := by
    simp only [amp]
    ring
  rw [h3]
  exact h2

private lemma kolm_hasDeriv (A c t : ℝ) (k : Mode) :
    HasDerivWithinAt (fun s => kolm A c s k) (((-c * amp A c t : ℝ) : ℂ) • prof k) (Ici 0) t := by
  have h := ((amp_hasDeriv A c t).ofReal_comp).smul_const (prof k)
  simp only [kolm_eq, Pi.smul_apply]
  exact h.hasDerivWithinAt

private lemma kolm_adm (A c t s : ℝ) : Adm s (kolm A c t) := by
  rw [kolm_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (prof_inH s).mul_left (‖(amp A c t : ℂ)‖ ^ 2)
    refine h.congr fun k => ?_
    simp only [Pi.smul_apply, norm_smul]
    ring
  · intro k
    simp only [Pi.smul_apply]
    rw [prof_real k, conjV_real_smul]
  · intro k
    simp only [Pi.smul_apply]
    rw [dotM_smul, prof_sol k, mul_zero]
  · simp [prof_zero]

private lemma amp_continuous (A c : ℝ) : Continuous (amp A c) := by
  unfold amp
  fun_prop

private lemma kolm_cont (A c : ℝ) : ContH 2 (kolm A c) := by
  intro t₀ _
  have h1 : ∀ t, hnorm 2 (kolm A c t - kolm A c t₀) =
      |amp A c t - amp A c t₀| * hnorm 2 prof := by
    intro t
    have : kolm A c t - kolm A c t₀ = ((amp A c t - amp A c t₀ : ℝ) : ℂ) • prof := by
      rw [kolm_eq, kolm_eq]
      funext k
      simp only [Pi.sub_apply, Pi.smul_apply]
      push_cast
      rw [sub_smul]
    rw [this, hnorm_smul, Complex.norm_real, Real.norm_eq_abs]
  simp only [h1]
  have h2 : Filter.Tendsto (fun t => |amp A c t - amp A c t₀| * hnorm 2 prof) (nhds t₀)
      (nhds (|amp A c t₀ - amp A c t₀| * hnorm 2 prof)) := by
    have := amp_continuous A c
    exact (Continuous.tendsto (by fun_prop) t₀)
  rw [sub_self, abs_zero, zero_mul] at h2
  exact h2.mono_left nhdsWithin_le_nhds

/-- The decaying Kolmogorov flow is a strong solution. -/
theorem kolm_isStrong (A ν α : ℝ) : IsStrongSolution ν α 0 (kolm A ν 0) (kolm A ν) := by
  refine ⟨rfl, fun t _ => kolm_adm A ν t 2, kolm_cont A ν, fun k t _ => ?_⟩
  rw [kolm_rhs]
  exact kolm_hasDeriv A ν t k

/-- Vacuity: the zero field solves the unforced system for every coefficient. -/
theorem zero_isStrong (ν α : ℝ) : IsStrongSolution ν α 0 0 (fun _ => 0) := by
  have h : ∀ t, kolm 0 ν t = 0 := by
    intro t
    rw [kolm_eq]
    simp [amp]
  have := kolm_isStrong 0 ν α
  rw [h 0, show kolm 0 ν = fun _ => 0 from funext h] at this
  exact this

/-- The wrong decay rate is not a solution. -/
theorem kolm_wrong_rate (A ν α : ℝ) (hA : A ≠ 0) (hν : ν ≠ 0) :
    ¬ IsStrongSolution ν α 0 (kolm A (2 * ν) 0) (kolm A (2 * ν)) := by
  intro h
  have h1 := h.mode e2M 0 le_rfl
  rw [kolm_rhs] at h1
  have h2 := kolm_hasDeriv A (2 * ν) 0 e2M
  have hu : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := uniqueDiffWithinAt_Ici 0
  have h3 := hu.eq_deriv _ h1 h2
  have h4 := congrArg (fun v : V3 => v 0) h3
  simp [prof_e2M, e1V, amp] at h4
  rcases h4 with h5 | h5
  · have h6 : (ν : ℂ) = 0 := by linear_combination -h5
    exact hν (by exact_mod_cast h6)
  · exact hA h5

end OVNS
