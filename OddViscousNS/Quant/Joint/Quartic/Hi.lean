import OddViscousNS.Quant.Joint.Quartic.Identity
import OddViscousNS.Quant.Joint.Sources.Filter

/-!
# The high mixed source (step J5, node N11)

J3-v2 §2, §4 (`upstream/theorem12_v4/J3_HIGH_MIXED_QUARTICS_V2.md`), Bodies 27, 46.

* `Qphase_split`: `Q_τ(S, F) = Q_lo + Q_hi`: the low last edge of `LowPass.lean` and its exact high
  complement.
* `norm_Qhi_weight`: on the high complement `|p| ≤ (17/16)|s|`, so `|p|^m |Q_hi(p)| ≤ 10 (|s|^{m+1}‖S‖) ⋆ ‖F‖`.
* `hnorm_one_Qhi`, `hnorm_two_Qhi`: `‖Q_hi‖_m ≤ 10 ‖S‖_{m+1} L_h(F)`, "the positive bound".
* `lhB_Qhi`: `L_h(Q_hi) ≤ 9 W₁(S) L_h(F)`, the inner fast fibre.
* `fastNL_split`: `N_F = −2 Q_hi − 2 Q_lo − Π_F Q(F, F) − Π_F H_ψ`, the four source directions.
-/

open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {S F : Field} {τ : ℝ} {L W₁ : ℝ}

/-- **The low and the high product.** -/
theorem Qphase_split (τ : ℝ) (hS2 : Summable fun k => ‖S k‖ ^ 2)
    (hF2 : Summable fun k => ‖F k‖ ^ 2) : Qphase τ S F = Qlo τ S F + Qhi τ S F := by
  funext k
  have h1 := blk_norm_summable (phaseM_bdd τ) hS2 hF2 k
  have s0 : Summable fun p => blk (phaseM τ) p k (k - p) (S p) (F (k - p)) := h1.of_norm
  have e1 : Qphase τ S F k = ∑' p, blk (phaseM τ) p k (k - p) (S p) (F (k - p)) :=
    Qm_eq_tsum_blk (phaseM τ) S F k
  have e2 : Qhi τ S F k = ∑' p, ((hiMu p (k - p) : ℝ) : ℂ) •
      blk (phaseM τ) p k (k - p) (S p) (F (k - p)) := by
    have := Qm_eq_tsum_blk (hiM τ) S F k
    refine this.trans (tsum_congr fun p => ?_)
    rw [blk_hiM]
    rfl
  have sl : Summable fun p => ((lowM p (k - p) : ℝ) : ℂ) •
      blk (phaseM τ) p k (k - p) (S p) (F (k - p)) := by
    refine Summable.of_norm_bounded h1 fun p => ?_
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (lowM_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (lowM_le_one _ _)
  have sh : Summable fun p => ((hiMu p (k - p) : ℝ) : ℂ) •
      blk (phaseM τ) p k (k - p) (S p) (F (k - p)) := by
    refine Summable.of_norm_bounded h1 fun p => ?_
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hiMu_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hiMu_le_one _ _)
  rw [Pi.add_apply, e1, e2, Qlo, ← sl.tsum_add sh]
  refine tsum_congr fun p => ?_
  rw [← add_smul]
  have : ((lowM p (k - p) : ℝ) : ℂ) + ((hiMu p (k - p) : ℝ) : ℂ) = 1 := by
    simp only [hiMu]
    push_cast
    ring
  rw [this, one_smul]

/-- An edge at a weight. -/
lemma edge_weight (τ : ℝ) {m : ℕ} (hm : m ≤ 2) (s k : Mode) (v w : V3) :
    absk k ^ m * ‖blk (hiM τ) s k (k - s) v w‖ ≤ 10 * (absk s ^ (m + 1) * ‖v‖ * ‖w‖) := by
  have hk : s + (k - s) = k := by abel
  have h1 := norm_blk_hiM τ hk v
  have h2 := (blk (hiM τ) s k (k - s) v).le_opNorm w
  have h3 : ‖blk (hiM τ) s k (k - s) v w‖ ≤ hiMu s (k - s) * (8 * absk k * ‖v‖) * ‖w‖ :=
    h2.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  by_cases hμ : hiMu s (k - s) = 0
  · rw [hμ] at h3
    have h0 : ‖blk (hiM τ) s k (k - s) v w‖ = 0 :=
      le_antisymm (by simpa using h3) (norm_nonneg _)
    rw [h0, mul_zero]
    have := absk_nonneg s
    positivity
  have hsep := hi_sep hμ
  have hk0 := absk_nonneg k
  have hs0 := absk_nonneg s
  have hle : absk k ≤ 17 / 16 * absk s := by
    have h4 := absk_add_le s (k - s)
    rw [hk] at h4
    linarith
  have hμ0 := hiMu_nonneg s (k - s)
  have hμ1 := hiMu_le_one s (k - s)
  have hA : 0 ≤ ‖v‖ * ‖w‖ := by positivity
  have h5 : absk k ^ (m + 1) ≤ (17 / 16 * absk s) ^ (m + 1) := pow_le_pow_left₀ hk0 hle _
  have h6 : (17 / 16 : ℝ) ^ (m + 1) ≤ 5 / 4 := by
    have : (17 / 16 : ℝ) ^ (m + 1) ≤ (17 / 16) ^ 3 :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact this.trans (by norm_num)
  calc absk k ^ m * ‖blk (hiM τ) s k (k - s) v w‖
      ≤ absk k ^ m * (hiMu s (k - s) * (8 * absk k * ‖v‖) * ‖w‖) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = hiMu s (k - s) * (8 * (absk k ^ (m + 1) * (‖v‖ * ‖w‖))) := by ring
    _ ≤ 1 * (8 * (absk k ^ (m + 1) * (‖v‖ * ‖w‖))) :=
        mul_le_mul_of_nonneg_right hμ1 (by positivity)
    _ ≤ 8 * ((5 / 4 * absk s ^ (m + 1)) * (‖v‖ * ‖w‖)) := by
        rw [one_mul]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hA) (by norm_num)
        refine h5.trans ?_
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = _ := by ring

/-- **The pointwise majorant of the high source.** -/
theorem norm_Qhi_weight (τ : ℝ) {m : ℕ} (hm : m ≤ 2) (hS2 : Summable fun k => ‖S k‖ ^ 2)
    (hF2 : Summable fun k => ‖F k‖ ^ 2) {α : Mode → ℝ}
    (hα : ∀ s, absk s ^ (m + 1) * ‖S s‖ ≤ α s) (k : Mode)
    (hs : Summable fun s => α s * ‖F (k - s)‖) :
    absk k ^ m * ‖Qhi τ S F k‖ ≤ 10 * cvS α (nrm F) k := by
  have hb := blk_norm_summable (hiM_bdd τ) hS2 hF2 k
  have h1 : ‖Qhi τ S F k‖ ≤ ∑' s, ‖blk (hiM τ) s k (k - s) (S s) (F (k - s))‖ := by
    have e := Qm_eq_tsum_blk (hiM τ) S F k
    rw [Qhi, e]
    exact norm_tsum_le_tsum_norm hb
  have h2 : absk k ^ m * ‖Qhi τ S F k‖ ≤
      ∑' s, absk k ^ m * ‖blk (hiM τ) s k (k - s) (S s) (F (k - s))‖ := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left h1 (by have := absk_nonneg k; positivity)
  refine h2.trans ?_
  unfold cvS
  rw [← tsum_mul_left]
  refine (hb.mul_left _).tsum_le_tsum (fun s => ?_) (hs.mul_left _)
  refine (edge_weight τ hm s k (S s) (F (k - s))).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact mul_le_mul_of_nonneg_right (hα s) (norm_nonneg _)

/-- A sequence from its weighted majorant. -/
lemma inH_of_majorant {u : Field} {m : ℕ} {A₀ c : ℝ} {α : Mode → ℝ} (hc : 0 ≤ c)
    (h : L2B α A₀) (hu : ∀ k, absk k ^ m * ‖u k‖ ≤ c * α k) :
    InH m u ∧ hnorm m u ≤ c * A₀ := by
  have e : ∀ k, sobWeight m k * ‖u k‖ ^ 2 ≤ c ^ 2 * α k ^ 2 := fun k => by
    by_cases hk : k = 0
    · subst hk
      simp only [sobWeight, ite_true, zero_mul]
      have := h.nn 0
      positivity
    · have e1 : sobWeight m k = (absk k ^ m) ^ 2 := by
        simp only [sobWeight, hk, ite_false]
        rw [← pow_mul, ← Real.rpow_natCast]
        congr 1
        push_cast
        ring
      rw [e1, ← mul_pow, ← mul_pow]
      exact pow_le_pow_left₀ (by have := absk_nonneg k; positivity) (hu k) 2
  have hs : Summable fun k => c ^ 2 * α k ^ 2 := h.s.mul_left _
  have hI : InH m u := Summable.of_nonneg_of_le
    (fun k => mul_nonneg (sobWeight_nonneg _ _) (by positivity)) e hs
  refine ⟨hI, ?_⟩
  have h1 : ∑' k, sobWeight m k * ‖u k‖ ^ 2 ≤ c ^ 2 * ∑' k, α k ^ 2 := by
    rw [← tsum_mul_left]
    exact hI.tsum_le_tsum e hs
  unfold hnorm
  refine (Real.sqrt_le_sqrt h1).trans ?_
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc]
  exact mul_le_mul_of_nonneg_left h.le hc

/-- The convolution array of a slow field and a fibre. -/
lemma conv_hyp {α : Mode → ℝ} {A₀ : ℝ} (hα : L2B α A₀) (hαs : ∀ s, s 2 ≠ 0 → α s = 0)
    (hF : LhB (nrm F) L) : (∀ p, Summable fun s => α s * ‖F (p - s)‖) ∧
      L2B (cvS α (nrm F)) (A₀ * L) :=
  LhB.conv hα hαs hF

/-- **`‖Q_hi‖₁ ≤ 10 ‖S‖₂ L_h(F)`**. -/
theorem hnorm_one_Qhi (τ : ℝ) (hS : MZ 2 S) (hS' : PiS S = S) (hF2 : Summable fun k => ‖F k‖ ^ 2)
    (hF : LhB (nrm F) L) :
    InH 1 (Qhi τ S F) ∧ hnorm 1 (Qhi τ S F) ≤ 10 * (hnorm 2 S * L) := by
  have hU := l2B_up hS.inH
  obtain ⟨hs, hA⟩ := conv_hyp hU (fun s hs => by simp [up, nrm, slow_zero hS' hs]) hF
  have hS2 := summable_norm_sq_of_inH (hS.inH.mono (by norm_num : (0 : ℝ) ≤ 2))
  have h := inH_of_majorant (m := 1) (u := Qhi τ S F) (c := 10) (by norm_num) hA fun k => by
    refine norm_Qhi_weight τ (by norm_num) hS2 hF2 (α := up (nrm S)) (fun s => ?_) k (hs k)
    exact (le_of_eq (up_nrm S s).symm)
  simpa using h

/-- **`‖Q_hi‖₂ ≤ 10 ‖S‖₃ L_h(F)`**. -/
theorem hnorm_two_Qhi (τ : ℝ) (hS : MZ 3 S) (hS' : PiS S = S) (hF2 : Summable fun k => ‖F k‖ ^ 2)
    (hF : LhB (nrm F) L) :
    InH 2 (Qhi τ S F) ∧ hnorm 2 (Qhi τ S F) ≤ 10 * (hnorm 3 S * L) := by
  have hU := l2B_up_gr hS
  obtain ⟨hs, hA⟩ := conv_hyp hU (fun s hs => by simp [up, gr, slow_zero hS' hs]) hF
  have hS2 := summable_norm_sq_of_inH (hS.inH.mono (by norm_num : (0 : ℝ) ≤ 3))
  have h := inH_of_majorant (m := 2) (u := Qhi τ S F) (c := 10) (by norm_num) hA fun k => by
    refine norm_Qhi_weight τ (by norm_num) hS2 hF2 (α := up (gr S)) (fun s => ?_) k (hs k)
    exact (le_of_eq (up_gr S s).symm)
  simpa using h

/-- **The inner fast fibre** (Body 46, J3-v2 §4): `L_h(Q_hi) ≤ 10 W₁(S) L_h(F)`. -/
theorem lhB_Qhi (τ : ℝ) (hS : MZ 2 S) (hS' : PiS S = S) (hF2 : Summable fun k => ‖F k‖ ^ 2)
    (hW : L1B (gr S) W₁) (hF : LhB (nrm F) L) : LhB (nrm (Qhi τ S F)) (10 * (W₁ * L)) := by
  have h1 := LhB.conv_l1 hW (fun s hs => by simp [gr, slow_zero hS' hs]) hF
  have h2 := h1.const_mul (by norm_num : (0 : ℝ) ≤ 10)
  have hS2 := summable_norm_sq_of_inH (hS.inH.mono (by norm_num : (0 : ℝ) ≤ 2))
  have hsm : ∀ k, Summable fun s => gr S s * ‖F (k - s)‖ := fun k => by
    have hU := l2B_gr (hS.inH.mono (by norm_num : (1 : ℝ) ≤ 2))
    exact (conv_hyp hU (fun s hs => by simp [gr, slow_zero hS' hs]) hF).1 k
  refine h2.of_le (fun _ => norm_nonneg _) fun k => ?_
  have := norm_Qhi_weight τ (m := 0) (by norm_num) hS2 hF2 (α := gr S)
    (fun s => by simp [gr]) k (hsm k)
  simpa [nrm] using this

lemma blk_zero_leaf (m : Mult) (p k j : Mode) : blk m p k j 0 = 0 := by
  have h := blk_smul_leaf m p k j 0 0
  rw [zero_smul] at h
  refine h.trans ?_
  ext1 y
  simp only [smul_apply, zero_apply, zero_smul]

/-- The high source is fast. -/
lemma Qhi_slow_zero (hS' : PiS S = S) (hF' : PiF F = F) {k : Mode} (hk : k 2 = 0) :
    Qhi τ S F k = 0 := by
  have e := Qm_eq_tsum_blk (hiM τ) S F k
  rw [Qhi, e]
  refine (tsum_congr fun s => ?_).trans tsum_zero
  by_cases hs : s 2 = 0
  · have : (k - s) 2 = 0 := by simp [hk, hs]
    rw [fast_zero hF' this, map_zero]
  · rw [slow_zero hS' hs, blk_zero_leaf]
    simp

lemma PiF_Qhi (hS' : PiS S = S) (hF' : PiF F = F) : PiF (Qhi τ S F) = Qhi τ S F := by
  funext k
  by_cases hk : k 2 = 0
  · simp [PiF, hk, Qhi_slow_zero hS' hF' hk]
  · simp [PiF, hk]

/-- The high source of real fields is real. -/
lemma isReal_Qhi (τ : ℝ) (hS : Adm 2 S) (hF : Adm 2 F) : IsReal (Qhi τ S F) :=
  (majorized_Qm (fun _ => hiM τ) (fun _ => hiM_bdd τ) (fun _ => hiM_real τ)
    fun _ _ _ _ _ => continuous_const).real 0 S F hS hF

lemma Qhi_zero : Qhi τ S F 0 = 0 := by simp [Qhi, Qm, hel_zero_mode]

end OVNS.Quant.Quartic

end
