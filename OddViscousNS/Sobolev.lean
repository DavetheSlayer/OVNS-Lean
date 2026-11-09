import OddViscousNS.Mode

/-! # Calculus of the coefficient norms `hnorm`, `hsE`, `InH`, and the sector projections -/

open scoped ENNReal
noncomputable section
namespace OVNS

variable {s s' : ℝ} {f g : Field}

/-- Each term of the Sobolev series is nonnegative. -/
private lemma term_nonneg (s : ℝ) (f : Field) (k : Mode) : 0 ≤ sobWeight s k * ‖f k‖ ^ 2 :=
  mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _)

/-- The Sobolev series has nonnegative sum. -/
private lemma tsum_term_nonneg (s : ℝ) (f : Field) : 0 ≤ ∑' k, sobWeight s k * ‖f k‖ ^ 2 :=
  tsum_nonneg (term_nonneg s f)

/-- Cauchy-Schwarz for nonnegative real series. -/
private lemma cs_tsum {a b : Mode → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (ha2 : Summable fun k => a k ^ 2) (hb2 : Summable fun k => b k ^ 2) :
    Summable (fun k => a k * b k) ∧
      ∑' k, a k * b k ≤ Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, b k ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have ha2' : Summable fun k => a k ^ (2 : ℝ) := by simpa only [Real.rpow_two] using ha2
  have hb2' : Summable fun k => b k ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hb2
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq ha hb ha2' hb2'
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using h

/-- Weighted Cauchy-Schwarz for the Sobolev series. -/
private lemma cs_core {s₁ s₂ : ℝ} {c F : Field} (hc : InH s₁ c) (hF : InH s₂ F) :
    Summable (fun k => Real.sqrt (sobWeight s₁ k) * Real.sqrt (sobWeight s₂ k) *
        (‖c k‖ * ‖F k‖)) ∧
      ∑' k, Real.sqrt (sobWeight s₁ k) * Real.sqrt (sobWeight s₂ k) * (‖c k‖ * ‖F k‖) ≤
        hnorm s₁ c * hnorm s₂ F := by
  have key : ∀ (t : ℝ) (G : Field) (k : Mode),
      (Real.sqrt (sobWeight t k) * ‖G k‖) ^ 2 = sobWeight t k * ‖G k‖ ^ 2 := fun t G k => by
    rw [mul_pow, Real.sq_sqrt (sobWeight_nonneg t k)]
  have h := cs_tsum (a := fun k => Real.sqrt (sobWeight s₁ k) * ‖c k‖)
    (b := fun k => Real.sqrt (sobWeight s₂ k) * ‖F k‖)
    (fun k => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (fun k => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (by simp only [key]; exact hc) (by simp only [key]; exact hF)
  have e : ∀ k, (Real.sqrt (sobWeight s₁ k) * ‖c k‖) * (Real.sqrt (sobWeight s₂ k) * ‖F k‖) =
      Real.sqrt (sobWeight s₁ k) * Real.sqrt (sobWeight s₂ k) * (‖c k‖ * ‖F k‖) := fun k => by
    ring
  simpa only [e, key, hnorm] using h

/-- The geometric-mean identity `|k|^{2σ} = |k|^{σ+1}|k|^{σ-1}`. -/
private lemma sobWeight_eq_sqrt_mul (σ : ℝ) (k : Mode) :
    Real.sqrt (sobWeight (σ + 1) k) * Real.sqrt (sobWeight (σ - 1) k) = sobWeight σ k := by
  by_cases hk : k = 0
  · simp [sobWeight, hk]
  · have hpos : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
    have hw : 0 ≤ absk k ^ (2 * σ) := Real.rpow_nonneg hpos.le _
    simp only [sobWeight, hk, ite_false]
    rw [← Real.sqrt_mul (Real.rpow_nonneg hpos.le _), ← Real.rpow_add hpos]
    have : 2 * (σ + 1) + 2 * (σ - 1) = (2 * σ) + (2 * σ) := by ring
    rw [this, Real.rpow_add hpos, Real.sqrt_mul_self hw]

/-- The core pairing bound. -/
private lemma pair_core {σ : ℝ} {c F : Field} (hc : InH (σ + 1) c) (hF : InH (σ - 1) F) :
    Summable (fun k => sobWeight σ k * ‖c k‖ * ‖F k‖) ∧
      ∑' k, sobWeight σ k * ‖c k‖ * ‖F k‖ ≤ hnorm (σ + 1) c * hnorm (σ - 1) F := by
  have e : ∀ k, Real.sqrt (sobWeight (σ + 1) k) * Real.sqrt (sobWeight (σ - 1) k) *
      (‖c k‖ * ‖F k‖) = sobWeight σ k * ‖c k‖ * ‖F k‖ := fun k => by
    rw [sobWeight_eq_sqrt_mul, mul_assoc]
  simpa only [e] using cs_core hc hF

/-- Domination of coefficients gives membership. -/
private lemma InH.of_norm_le (hf : InH s f) (h : ∀ k, ‖g k‖ ≤ ‖f k‖) : InH s g :=
  Summable.of_nonneg_of_le (term_nonneg s g) (fun k =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h k) 2)
      (sobWeight_nonneg s k)) hf

/-- Domination of coefficients gives a norm bound. -/
private lemma hnorm_le_of_norm_le (hf : InH s f) (h : ∀ k, ‖g k‖ ≤ ‖f k‖) :
    hnorm s g ≤ hnorm s f :=
  Real.sqrt_le_sqrt <| (hf.of_norm_le h).tsum_le_tsum (fun k =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h k) 2)
      (sobWeight_nonneg s k)) hf

/-- A summand of the Sobolev series is below the square of the norm. -/
private lemma term_le_hnorm_sq (hf : InH s f) (k : Mode) :
    sobWeight s k * ‖f k‖ ^ 2 ≤ hnorm s f ^ 2 := by
  rw [hnorm, Real.sq_sqrt (tsum_term_nonneg s f)]
  exact hf.le_tsum k (fun j _ => term_nonneg s f j)

/-- The summand of `pair` is absolutely dominated. -/
private lemma norm_pair_term_le (σ : ℝ) (c F : Field) (k : Mode) :
    ‖sobWeight σ k * (inner ℂ (c k) (F k)).re‖ ≤ sobWeight σ k * ‖c k‖ * ‖F k‖ := by
  rw [norm_mul, Real.norm_of_nonneg (sobWeight_nonneg σ k), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (sobWeight_nonneg σ k)
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)

/-- The series defining `pair` converges. -/
private lemma pair_summable {σ : ℝ} {c F : Field} (hc : InH (σ + 1) c) (hF : InH (σ - 1) F) :
    Summable (fun k => sobWeight σ k * (inner ℂ (c k) (F k)).re) :=
  Summable.of_norm_bounded (pair_core hc hF).1 (norm_pair_term_le σ c F)

lemma hnorm_nonneg (s : ℝ) (f : Field) : 0 ≤ hnorm s f := Real.sqrt_nonneg _
lemma hnorm_sq (_hf : InH s f) : hnorm s f ^ 2 = ∑' k, sobWeight s k * ‖f k‖ ^ 2 :=
  Real.sq_sqrt (tsum_term_nonneg s f)
lemma InH.mono (h : s ≤ s') (hf : InH s' f) : InH s f :=
  Summable.of_nonneg_of_le (term_nonneg s f) (fun k =>
    mul_le_mul_of_nonneg_right (sobWeight_mono h k) (sq_nonneg _)) hf
lemma hnorm_mono (h : s ≤ s') (hf : InH s' f) : hnorm s f ≤ hnorm s' f :=
  Real.sqrt_le_sqrt <| (hf.mono h).tsum_le_tsum (fun k =>
    mul_le_mul_of_nonneg_right (sobWeight_mono h k) (sq_nonneg _)) hf
lemma InH.add (hf : InH s f) (hg : InH s g) : InH s (f + g) := by
  refine Summable.of_nonneg_of_le (term_nonneg s (f + g)) (fun k => ?_)
    ((hf.mul_left 2).add (hg.mul_left 2))
  have h1 : ‖(f + g) k‖ ≤ ‖f k‖ + ‖g k‖ := norm_add_le _ _
  have h2 : ‖(f + g) k‖ ^ 2 ≤ 2 * ‖f k‖ ^ 2 + 2 * ‖g k‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f k‖ - ‖g k‖), norm_nonneg ((f + g) k), norm_nonneg (f k),
      norm_nonneg (g k), pow_le_pow_left₀ (norm_nonneg ((f + g) k)) h1 2]
  have := mul_le_mul_of_nonneg_left h2 (sobWeight_nonneg s k)
  nlinarith
lemma InH.neg (hf : InH s f) : InH s (-f) :=
  hf.of_norm_le fun k => by simp
lemma InH.sub (hf : InH s f) (hg : InH s g) : InH s (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg
lemma InH.smul (c : ℂ) (hf : InH s f) : InH s (c • f) := by
  have : (fun k => sobWeight s k * ‖(c • f) k‖ ^ 2) =
      fun k => ‖c‖ ^ 2 * (sobWeight s k * ‖f k‖ ^ 2) := by
    funext k
    rw [Pi.smul_apply, norm_smul]
    ring
  change Summable fun k => sobWeight s k * ‖(c • f) k‖ ^ 2
  rw [this]
  exact hf.mul_left _
lemma inH_zero : InH s 0 := by
  simp [InH]
lemma hnorm_zero : hnorm s 0 = 0 := by simp [hnorm]
lemma hnorm_add_le (hf : InH s f) (hg : InH s g) : hnorm s (f + g) ≤ hnorm s f + hnorm s g := by
  obtain ⟨hs, hle⟩ := cs_core hf hg
  have hf' : Summable fun k => sobWeight s k * ‖f k‖ ^ 2 := hf
  have hg' : Summable fun k => sobWeight s k * ‖g k‖ ^ 2 := hg
  have e : ∀ k, Real.sqrt (sobWeight s k) * Real.sqrt (sobWeight s k) * (‖f k‖ * ‖g k‖) =
      sobWeight s k * (‖f k‖ * ‖g k‖) := fun k => by
    rw [Real.mul_self_sqrt (sobWeight_nonneg s k)]
  simp only [e] at hs hle
  refine Real.sqrt_le_iff.2 ⟨add_nonneg (hnorm_nonneg _ _) (hnorm_nonneg _ _), ?_⟩
  have hsum : ∑' k, (sobWeight s k * ‖f k‖ ^ 2 + 2 * (sobWeight s k * (‖f k‖ * ‖g k‖)) +
      sobWeight s k * ‖g k‖ ^ 2) = hnorm s f ^ 2 + 2 * ∑' k, sobWeight s k * (‖f k‖ * ‖g k‖) +
      hnorm s g ^ 2 := by
    rw [hnorm_sq hf, hnorm_sq hg, Summable.tsum_add (hf'.add (hs.mul_left 2)) hg',
      Summable.tsum_add hf' (hs.mul_left 2), tsum_mul_left]
  have hmain : ∑' k, sobWeight s k * ‖(f + g) k‖ ^ 2 ≤
      ∑' k, (sobWeight s k * ‖f k‖ ^ 2 + 2 * (sobWeight s k * (‖f k‖ * ‖g k‖)) +
        sobWeight s k * ‖g k‖ ^ 2) := by
    refine (hf.add hg).tsum_le_tsum (fun k => ?_) ((hf'.add (hs.mul_left 2)).add hg')
    have h1 : ‖(f + g) k‖ ^ 2 ≤ (‖f k‖ + ‖g k‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    have := mul_le_mul_of_nonneg_left h1 (sobWeight_nonneg s k)
    nlinarith
  rw [hsum] at hmain
  nlinarith
lemma hnorm_neg : hnorm s (-f) = hnorm s f := by simp [hnorm]
lemma hnorm_sub_le (hf : InH s f) (hg : InH s g) : hnorm s (f - g) ≤ hnorm s f + hnorm s g := by
  rw [sub_eq_add_neg]
  exact (hnorm_add_le hf hg.neg).trans_eq (by rw [hnorm_neg])
lemma hnorm_sub_comm : hnorm s (f - g) = hnorm s (g - f) := by
  simp only [hnorm, Pi.sub_apply, norm_sub_rev (f _)]
lemma hnorm_smul (c : ℂ) : hnorm s (c • f) = ‖c‖ * hnorm s f := by
  have : (fun k => sobWeight s k * ‖(c • f) k‖ ^ 2) =
      fun k => ‖c‖ ^ 2 * (sobWeight s k * ‖f k‖ ^ 2) := by
    funext k
    rw [Pi.smul_apply, norm_smul]
    ring
  rw [hnorm, this, tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), hnorm]
/-- `hnorm` vanishes only on `f = 0` for mean-zero fields. -/
lemma eq_zero_of_hnorm_eq_zero (hf : InH s f) (h0 : f 0 = 0) (h : hnorm s f = 0) : f = 0 := by
  funext k
  by_cases hk : k = 0
  · simpa [hk] using h0
  · have h1 := term_le_hnorm_sq hf k
    have hw : 0 < sobWeight s k := by
      simp only [sobWeight, hk, ite_false]
      exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_absk hk)) _
    rw [h] at h1
    have h2 : ‖f k‖ ^ 2 ≤ 0 := by
      by_contra hc
      have : 0 < sobWeight s k * ‖f k‖ ^ 2 := mul_pos hw (not_le.1 hc)
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1
      linarith
    have h3 : ‖f k‖ = 0 := by
      have := sq_nonneg ‖f k‖
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h2 this)
    simpa using h3
/-- Coefficient bound `|k|^s |f_k| ≤ ‖f‖_s`. -/
lemma sobWeight_mul_norm_le (hf : InH s f) (k : Mode) :
    sobWeight s k * ‖f k‖ ^ 2 ≤ hnorm s f ^ 2 := term_le_hnorm_sq hf k
lemma hsE_eq_ofReal (hf : InH s f) : hsE s f = ENNReal.ofReal (hnorm s f ^ 2) := by
  rw [hnorm_sq hf, ENNReal.ofReal_tsum_of_nonneg (term_nonneg s f) hf, hsE]
lemma inH_iff_hsE_lt_top : InH s f ↔ hsE s f < ∞ := by
  refine ⟨fun hf => by rw [hsE_eq_ofReal hf]; exact ENNReal.ofReal_lt_top, fun h => ?_⟩
  have := ENNReal.summable_toReal h.ne
  simp only [ENNReal.toReal_ofReal (term_nonneg s f _)] at this
  exact this
/-- Interpolation: `‖f‖_1² ≤ ‖f‖_0 ‖f‖_2`, and `‖f‖_{s}² ≤ ‖f‖_{s-1}‖f‖_{s+1}`. -/
lemma hnorm_sq_le_mul (hf : InH (s + 1) f) :
    hnorm s f ^ 2 ≤ hnorm (s - 1) f * hnorm (s + 1) f := by
  have hf' : InH (s - 1) f := hf.mono (by linarith)
  have h := (pair_core hf hf').2
  have e : ∀ k, sobWeight s k * ‖f k‖ * ‖f k‖ = sobWeight s k * ‖f k‖ ^ 2 := fun k => by ring
  simp only [e] at h
  rw [hnorm_sq (hf.mono (by linarith)), mul_comm]
  exact h
/-- The pairing bound `|Re⟨c, Λ^{2σ}F⟩| ≤ ‖c‖_{σ+1} ‖F‖_{σ-1}`, with absolute convergence. -/
lemma pair_le {σ : ℝ} {c F : Field} (hc : InH (σ + 1) c) (hF : InH (σ - 1) F) :
    Summable (fun k => sobWeight σ k * ‖c k‖ * ‖F k‖) ∧
      |pair σ c F| ≤ hnorm (σ + 1) c * hnorm (σ - 1) F := by
  obtain ⟨hs, hle⟩ := pair_core hc hF
  refine ⟨hs, le_trans ?_ hle⟩
  rw [pair, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded hs.hasSum (norm_pair_term_le σ c F)
/-- Pairing is additive in the second slot when the terms converge. -/
lemma pair_add {σ : ℝ} {c F F' : Field} (hc : InH (σ + 1) c) (hF : InH (σ - 1) F)
    (hF' : InH (σ - 1) F') : pair σ c (F + F') = pair σ c F + pair σ c F' := by
  simp only [pair]
  rw [← Summable.tsum_add (pair_summable hc hF) (pair_summable hc hF')]
  refine tsum_congr fun k => ?_
  rw [Pi.add_apply, inner_add_right, Complex.add_re, mul_add]
lemma pair_sub {σ : ℝ} {c F F' : Field} (hc : InH (σ + 1) c) (hF : InH (σ - 1) F)
    (hF' : InH (σ - 1) F') : pair σ c (F - F') = pair σ c F - pair σ c F' := by
  simp only [pair]
  rw [← Summable.tsum_sub (pair_summable hc hF) (pair_summable hc hF')]
  refine tsum_congr fun k => ?_
  rw [Pi.sub_apply, inner_sub_right, Complex.sub_re, mul_sub]

/-! ### Sector projections -/
/-- The norm of a vector of `ℂ³` in coordinates. -/
private lemma norm_sq_three (v : V3) : ‖v‖ ^ 2 = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 + ‖v 2‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

/-- Coefficients of `PiS` are dominated. -/
private lemma norm_PiS_le (u : Field) (k : Mode) : ‖PiS u k‖ ≤ ‖u k‖ := by
  by_cases h : k 2 = 0 <;> simp [PiS, h]

/-- Coefficients of `PiF` are dominated. -/
private lemma norm_PiF_le (u : Field) (k : Mode) : ‖PiF u k‖ ≤ ‖u k‖ := by
  by_cases h : k 2 = 0 <;> simp [PiF, h]

/-- Pointwise Pythagoras for the slow horizontal/vertical split. -/
private lemma norm_sq_PiS_split (u : Field) (k : Mode) :
    ‖PiS u k‖ ^ 2 = ‖PiH u k‖ ^ 2 + ‖PiV u k‖ ^ 2 := by
  by_cases h : k 2 = 0
  · rw [norm_sq_three (PiS u k), norm_sq_three (PiH u k), norm_sq_three (PiV u k)]
    simp [PiS, PiH, PiV, h]
  · simp [PiS, PiH, PiV, h]

/-- Coefficients of `PiH` are dominated. -/
private lemma norm_PiH_le (u : Field) (k : Mode) : ‖PiH u k‖ ≤ ‖u k‖ := by
  refine le_trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_) (norm_PiS_le u k)
  rw [norm_sq_PiS_split]
  nlinarith [sq_nonneg ‖PiV u k‖]

/-- Coefficients of `PiV` are dominated. -/
private lemma norm_PiV_le (u : Field) (k : Mode) : ‖PiV u k‖ ≤ ‖u k‖ := by
  refine le_trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_) (norm_PiS_le u k)
  rw [norm_sq_PiS_split]
  nlinarith [sq_nonneg ‖PiH u k‖]

lemma PiS_add_PiF (u : Field) : PiS u + PiF u = u := by
  funext k
  by_cases h : k 2 = 0 <;> simp [PiS, PiF, h]
lemma InH.PiS (hf : InH s f) : InH s (PiS f) := hf.of_norm_le (norm_PiS_le f)
lemma InH.PiF (hf : InH s f) : InH s (PiF f) := hf.of_norm_le (norm_PiF_le f)
lemma hnorm_sq_split (hf : InH s f) :
    hnorm s f ^ 2 = hnorm s (PiS f) ^ 2 + hnorm s (PiF f) ^ 2 := by
  rw [hnorm_sq hf, hnorm_sq hf.PiS, hnorm_sq hf.PiF, ← Summable.tsum_add hf.PiS hf.PiF]
  refine tsum_congr fun k => ?_
  by_cases h : k 2 = 0 <;> simp [OVNS.PiS, OVNS.PiF, h]
lemma hnorm_PiS_le (hf : InH s f) : hnorm s (PiS f) ≤ hnorm s f :=
  hnorm_le_of_norm_le hf (norm_PiS_le f)
lemma hnorm_PiF_le (hf : InH s f) : hnorm s (PiF f) ≤ hnorm s f :=
  hnorm_le_of_norm_le hf (norm_PiF_le f)
lemma Adm.PiS (hf : Adm s f) : Adm s (PiS f) := by
  refine ⟨hf.inH.PiS, fun k => ?_, fun k => ?_, ?_⟩
  · by_cases h : k 2 = 0
    · simpa [OVNS.PiS, h] using hf.real k
    · ext i
      simp [OVNS.PiS, h, conjV]
  · by_cases h : k 2 = 0
    · simpa [OVNS.PiS, h] using hf.sol k
    · simp [OVNS.PiS, h, dotM]
  · simpa [OVNS.PiS] using hf.mean
lemma Adm.PiF (hf : Adm s f) : Adm s (PiF f) := by
  refine ⟨hf.inH.PiF, fun k => ?_, fun k => ?_, ?_⟩
  · by_cases h : k 2 = 0
    · ext i
      simp [OVNS.PiF, h, conjV]
    · simpa [OVNS.PiF, h] using hf.real k
  · by_cases h : k 2 = 0
    · simp [OVNS.PiF, h, dotM]
    · simpa [OVNS.PiF, h] using hf.sol k
  · simp [OVNS.PiF]
lemma PiS_eq_PiH_add_PiV {u : Field} : PiS u = PiH u + PiV u := by
  funext k
  by_cases h : k 2 = 0
  · ext i
    fin_cases i <;> simp [PiS, PiH, PiV, h]
  · simp [PiS, PiH, PiV, h]
lemma InH.PiH (hf : InH s f) : InH s (PiH f) := hf.of_norm_le (norm_PiH_le f)
lemma InH.PiV (hf : InH s f) : InH s (PiV f) := hf.of_norm_le (norm_PiV_le f)
lemma hnorm_sq_split_slow (hf : InH s f) :
    hnorm s (PiS f) ^ 2 = hnorm s (PiH f) ^ 2 + hnorm s (PiV f) ^ 2 := by
  rw [hnorm_sq hf.PiS, hnorm_sq hf.PiH, hnorm_sq hf.PiV, ← Summable.tsum_add hf.PiH hf.PiV]
  refine tsum_congr fun k => ?_
  rw [norm_sq_PiS_split, mul_add]
lemma Adm.mz {f : Field} (h : Adm s f) : MZ s f := ⟨h.inH, h.mean⟩

/-! ### Spectral gap (Poincaré) on mean-zero fields is `hnorm_mono`; truncation -/
/-- Truncation to `|k| ≤ N`. -/
def lowPass (N : ℝ) (u : Field) : Field := by classical exact fun k => if absk k ≤ N then u k else 0
/-- High-frequency tail: `‖u - P_{≤N}u‖_s → 0`. -/
lemma tendsto_hnorm_highPass (hf : InH s f) :
    Filter.Tendsto (fun N : ℕ => hnorm s (f - lowPass N f)) Filter.atTop (nhds 0) := by
  have hpt : ∀ (N : ℕ) (k : Mode), ‖(f - lowPass N f) k‖ ≤ ‖f k‖ := fun N k => by
    by_cases h : absk k ≤ N <;> simp [lowPass, h]
  have hlim : Filter.Tendsto (fun N : ℕ => ∑' k, sobWeight s k * ‖(f - lowPass N f) k‖ ^ 2)
      Filter.atTop (nhds (∑' _ : Mode, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hf (fun k => ?_)
      (Filter.Eventually.of_forall fun N k => ?_)
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨M, hM⟩ := exists_nat_ge (absk k)
      filter_upwards [Filter.eventually_ge_atTop M] with N hN
      have h : absk k ≤ N := hM.trans (by exact_mod_cast hN)
      simp [lowPass, h]
    · rw [Real.norm_of_nonneg (term_nonneg s _ k)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hpt N k) 2)
        (sobWeight_nonneg s k)
  have := hlim.sqrt
  simpa [hnorm] using this

end OVNS
