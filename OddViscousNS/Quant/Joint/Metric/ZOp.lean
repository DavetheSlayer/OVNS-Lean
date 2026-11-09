import OddViscousNS.Quant.Joint.Metric.HeatForm

/-!
# `Z`: the static bound and the output half (step J5, node N5)

* `X1Form_mixed_le`: the mixed form of `X₁` with an `H¹` leaf (Body 40);
* `X1Form_free_le`: the phase-free output half, `‖A^{1/2} X₁[h]‖ ≲ ‖ĥ‖_{ℓ¹} + ‖h‖₂`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (Qm_two_le)

noncomputable section

namespace OVNS.Quant.Metric

variable {r : ℝ} {s : ℕ} {h G F : Field}

/-- `gr` from the energy coordinates. -/
lemma l2B_half {G : Field} (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2) :
    L2B (fun k => absk k * nrm G k) (l2n (zOf 1 G)) := by
  have e : ∀ k, ‖zOf 1 G k‖ = absk k * nrm G k := fun k => by
    simp only [zOf, norm_smul, Complex.norm_real, pow_one, Real.norm_of_nonneg (absk_nonneg k), nrm]
  simp only [← e]
  exact ⟨fun _ => norm_nonneg _, hG1, le_rfl⟩

private lemma ratio_le_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a / b + b / a ≤ a ^ 2 / b ^ 2 + b ^ 2 / a ^ 2 := by
  have e1 : a / b + b / a = (a ^ 3 * b + a * b ^ 3) / (a ^ 2 * b ^ 2) := by
    field_simp
  have e2 : a ^ 2 / b ^ 2 + b ^ 2 / a ^ 2 = (a ^ 4 + b ^ 4) / (a ^ 2 * b ^ 2) := by
    field_simp
  rw [e1, e2]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h1 : 0 ≤ (a - b) ^ 2 * (a ^ 2 + a * b + b ^ 2) := by positivity
  nlinarith only [h1]

/-- The block bound at both weights. -/
lemma norm_X1b_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {p k j : Mode} (hk : p + j = k)
    (hp : p 2 = 0) (hj : j 2 ≠ 0) (v : V3) :
    ‖X1b s r τ p k j v‖ ≤ 44 / |r| * ‖v‖ * (absSq k / absSq j + absSq j / absSq k) := by
  rcases hs with rfl | rfl
  · have hr0 : 0 < |r| := abs_pos.2 hr
    have hj0 : j ≠ 0 := fun h => hj (by simp [h])
    have hk2 : k 2 = j 2 := by rw [← hk]; simp [hp]
    have hk0 : k ≠ 0 := fun h => hj (by rw [← hk2, h]; rfl)
    have hJ : 0 < absk j := lt_of_lt_of_le one_pos (one_le_absk hj0)
    have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk0)
    have h1 := norm_X1b_one_le hr τ hk hp hj v
    have h2 := ratio_le_sq hK hJ
    rw [absk_sq, absk_sq] at h2
    have hv := norm_nonneg v
    calc _ ≤ 20 / |r| * ‖v‖ * (absk k / absk j + absk j / absk k) := h1
      _ ≤ 20 / |r| * ‖v‖ * (absSq k / absSq j + absSq j / absSq k) := by gcongr
      _ ≤ _ := by
          have : 0 ≤ absSq k / absSq j + absSq j / absSq k := by
            have := absSq_nonneg k
            have := absSq_nonneg j
            positivity
          gcongr
          norm_num
  · exact norm_X1b_two_le hr τ hk hp hj v

/-- The summand of `X1Form`. -/
lemma norm_X1summand_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hh' : PiS h = h)
    (hF' : PiF F = F) (x : Mode × Mode) :
    ‖inner ℂ (G x.1) (X1b s r τ x.2 x.1 (x.1 - x.2) (h x.2) (F (x.1 - x.2)))‖ ≤
      44 / |r| * (nrm G x.1 * nrm h x.2 * nrm F (x.1 - x.2) *
        (absSq x.1 / absSq (x.1 - x.2) + absSq (x.1 - x.2) / absSq x.1)) := by
  obtain ⟨k, p⟩ := x
  simp only
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hnn : 0 ≤ 44 / |r| * (nrm G k * nrm h p * nrm F (k - p) *
      (absSq k / absSq (k - p) + absSq (k - p) / absSq k)) := by
    have h1 := absSq_nonneg k
    have h2 := absSq_nonneg (k - p)
    have h3 : 0 ≤ nrm G k := norm_nonneg _
    have h4 : 0 ≤ nrm h p := norm_nonneg _
    have h5 : 0 ≤ nrm F (k - p) := norm_nonneg _
    positivity
  by_cases hj : (k - p) 2 = 0
  · rw [fast_zero hF' hj, map_zero, inner_zero_right, norm_zero]
    exact hnn
  by_cases hp : p 2 = 0
  swap
  · rw [slow_zero hh' hp, X1b_zero_leaf, zero_apply, inner_zero_right, norm_zero]
    exact hnn
  have h1 := norm_X1b_le hs hr τ (show p + (k - p) = k by abel) hp hj (h p)
  have h2 := (ContinuousLinearMap.le_opNorm (X1b s r τ p k (k - p) (h p)) (F (k - p))).trans
    (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    ((mul_le_mul_of_nonneg_left h2 (norm_nonneg _)).trans (le_of_eq ?_))
  simp only [nrm]
  ring

/-- **The mixed form of `X₁`** (Body 40), with no reality and at both weights. -/
theorem X1Form_mixed_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hh : MZ 1 h) (hh' : PiS h = h)
    (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2)
    (hG' : PiF G = G) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF1 : Summable fun k => ‖zOf 1 F k‖ ^ 2) (hF' : PiF F = F) :
    ‖X1Form s r τ h G F‖ ≤ 44 / |r| * (Ce * hnorm 1 h *
      (l2n (zOf 1 G) * l2n F + l2n G * l2n (zOf 1 F))) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hγ : SlowH1 (nrm h) (hnorm 1 h) :=
    ⟨fun _ => norm_nonneg _, fun p hp => by
      simp only [nrm]
      rw [slow_zero hh' hp, norm_zero], by
      simp only [nrm]
      rw [hh.mean, norm_zero], l2B_gr hh.inH⟩
  have hE := edge_mixed (l2B_nrm hG) (l2B_half hG1) (l2B_nrm hF) (l2B_half hF1) hγ
    (fun k hk => by
      simp only [nrm]
      rw [fast_zero hG' hk, norm_zero])
    (fun k hk => by
      simp only [nrm]
      rw [fast_zero hF' hk, norm_zero])
  have hsum := hE.1.mul_left (44 / |r|)
  have hle := norm_X1summand_le (G := G) hs hr τ hh' hF'
  have hn : Summable fun x : Mode × Mode =>
      ‖inner ℂ (G x.1) (X1b s r τ x.2 x.1 (x.1 - x.2) (h x.2) (F (x.1 - x.2)))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum
  refine (norm_tsum_le_tsum_norm hn).trans ((hn.tsum_le_tsum hle hsum).trans ?_)
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hE.2 (by positivity)

/-! ### The phase-free output half -/

/-- The phase-free size of an edge of `X₁`, with the output derivative. -/
lemma norm_X1b_free_le (hs : s = 1 ∨ s = 2) (r τ : ℝ) {p k j : Mode} (hk : p + j = k) (hk0 : k ≠ 0)
    (hj0 : j ≠ 0) (v : V3) :
    absk k * ‖X1b s r τ p k j v‖ ≤ 32 * ‖v‖ * (1 + absSq k / absSq j + absSq j / absSq k) := by
  have hJ : 0 < absk j := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk0)
  have hv := norm_nonneg v
  have hsq : ∀ q : Mode, 0 ≤ 1 / absSq q := fun q => by
    have := absSq_nonneg q
    positivity
  have h1 := norm_blk_le_of (m := metM r τ) (B := 1 / absSq k) (hsq k) (fun a b c => by
    have := norm_metM_le_absSq r τ a b c p j
    rwa [hk] at this) hk v
  have ek : -p + k = j := by rw [← hk]; abel
  have h2 := norm_blk_le_of (m := metM r τ) (B := 1 / absSq j) (hsq j) (fun a b c => by
    have := norm_metM_le_absSq r τ a b c (-p) k
    rwa [ek] at this) ek (conjV v)
  rw [norm_conjV] at h2
  have hw1 : 0 ≤ wt s k j := by unfold wt; positivity
  have hw2 : 0 ≤ wt s j k := by unfold wt; positivity
  have e1 : ‖((2 * wt s k j : ℝ) : ℂ) • blk (metM r τ) p k j v‖ ≤
      2 * wt s k j * (8 * (1 / absSq k) * absk k * ‖v‖) := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have e2 : ‖ContinuousLinearMap.adjoint
      (((2 * wt s j k : ℝ) : ℂ) • blk (metM r τ) (-p) j k (conjV v))‖ ≤
      2 * wt s j k * (8 * (1 / absSq j) * absk j * ‖v‖) := by
    rw [LinearIsometryEquiv.norm_map, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have h3 : ‖X1b s r τ p k j v‖ ≤ 2 * wt s k j * (8 * (1 / absSq k) * absk k * ‖v‖) +
      2 * wt s j k * (8 * (1 / absSq j) * absk j * ‖v‖) :=
    (norm_add_le _ _).trans (add_le_add e1 e2)
  refine (mul_le_mul_of_nonneg_left h3 hK.le).trans ?_
  rw [← absk_sq k, ← absk_sq j]
  set a := absk k
  set b := absk j
  have e3 : a * (2 * wt s k j * (8 * (1 / a ^ 2) * a * ‖v‖) +
      2 * wt s j k * (8 * (1 / b ^ 2) * b * ‖v‖)) =
      16 * ‖v‖ * (wt s k j + wt s j k * (a / b)) := by
    field_simp
    ring
  rw [e3]
  have hx : 0 < a / b := by positivity
  have hy : 0 < b / a := by positivity
  have hxy : a / b * (b / a) = 1 := by field_simp
  have e4 : a ^ 2 / b ^ 2 = (a / b) ^ 2 := by rw [div_pow]
  have e5 : b ^ 2 / a ^ 2 = (b / a) ^ 2 := by rw [div_pow]
  rw [e4, e5]
  have hkey : wt s k j + wt s j k * (a / b) ≤ 2 * (1 + (a / b) ^ 2 + (b / a) ^ 2) := by
    rcases hs with rfl | rfl
    · simp only [wt, pow_one]
      have e6 : b / a * (a / b) = 1 := by rw [mul_comm]; exact hxy
      rw [e6]
      nlinarith only [sq_nonneg (a / b - 1), sq_nonneg (b / a)]
    · simp only [wt]
      have e6 : (b / a) ^ 2 * (a / b) = b / a := by
        calc _ = b / a * (b / a * (a / b)) := by ring
          _ = _ := by rw [mul_comm (b / a) (a / b), hxy, mul_one]
      rw [e6]
      nlinarith only [sq_nonneg (b / a - 1), sq_nonneg (a / b)]
  calc _ ≤ 16 * ‖v‖ * (2 * (1 + (a / b) ^ 2 + (b / a) ^ 2)) := by gcongr
    _ = _ := by ring

/-- **The phase-free output half** of `X₁`: `‖A^{1/2} X₁[h]‖ ≲ ‖ĥ‖_{ℓ¹} + ‖h‖₂`. -/
theorem X1Form_free_le (hs : s = 1 ∨ s = 2) (r τ : ℝ) (hh : MZ 2 h) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hG' : PiF G = G) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) :
    ‖X1Form s r τ h (zOf 1 G) F‖ ≤
      32 * ((9 * wiener h + 16 * c4 * hnorm 2 h) * (l2n G * l2n F)) := by
  have hE := edge_free (l2B_nrm hG) (l2B_nrm hF) (l1B_nrm hh.inH) (l2B_up hh.inH)
    (by simp only [nrm]; rw [hh.mean, norm_zero])
    (fun k hk => by
      simp only [nrm]
      rw [fast_zero hG' hk, norm_zero])
    (fun k hk => by
      simp only [nrm]
      rw [fast_zero hF' hk, norm_zero])
  have hsum := hE.1.mul_left 32
  have hle : ∀ x : Mode × Mode, ‖inner ℂ (zOf 1 G x.1)
      (X1b s r τ x.2 x.1 (x.1 - x.2) (h x.2) (F (x.1 - x.2)))‖ ≤
      32 * (nrm G x.1 * nrm h x.2 * nrm F (x.1 - x.2) *
        (1 + absSq x.1 / absSq (x.1 - x.2) + absSq (x.1 - x.2) / absSq x.1)) := fun x => by
    obtain ⟨k, p⟩ := x
    simp only
    have hnn : 0 ≤ 32 * (nrm G k * nrm h p * nrm F (k - p) *
        (1 + absSq k / absSq (k - p) + absSq (k - p) / absSq k)) := by
      have h1 := absSq_nonneg k
      have h2 := absSq_nonneg (k - p)
      have h3 : 0 ≤ nrm G k := norm_nonneg _
      have h4 : 0 ≤ nrm h p := norm_nonneg _
      have h5 : 0 ≤ nrm F (k - p) := norm_nonneg _
      positivity
    by_cases hj : (k - p) 2 = 0
    · rw [fast_zero hF' hj, map_zero, inner_zero_right, norm_zero]
      exact hnn
    by_cases hk : k 2 = 0
    · have : zOf 1 G k = 0 := by simp [zOf, fast_zero hG' hk]
      rw [this, inner_zero_left, norm_zero]
      exact hnn
    have hk0 : k ≠ 0 := fun h => hk (by rw [h]; rfl)
    have hj0 : k - p ≠ 0 := fun h => hj (by rw [h]; rfl)
    have h1 := norm_X1b_free_le hs r τ (show p + (k - p) = k by abel) hk0 hj0 (h p)
    have h2 : ‖zOf 1 G k‖ = absk k * ‖G k‖ := by
      simp only [zOf, norm_smul, Complex.norm_real, pow_one, Real.norm_of_nonneg (absk_nonneg k)]
    have h3 := (norm_inner_le_norm (𝕜 := ℂ) (zOf 1 G k)
      (X1b s r τ p k (k - p) (h p) (F (k - p)))).trans (mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.le_opNorm (X1b s r τ p k (k - p) (h p)) (F (k - p))) (norm_nonneg _))
    refine h3.trans ?_
    rw [h2]
    have h4 := mul_le_mul_of_nonneg_right h1
      (mul_nonneg (norm_nonneg (G k)) (norm_nonneg (F (k - p))))
    refine le_trans (le_of_eq ?_) (h4.trans (le_of_eq ?_))
    · ring
    · simp only [nrm]
      ring
  have hn : Summable fun x : Mode × Mode => ‖inner ℂ (zOf 1 G x.1)
      (X1b s r τ x.2 x.1 (x.1 - x.2) (h x.2) (F (x.1 - x.2)))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum
  refine (norm_tsum_le_tsum_norm hn).trans ((hn.tsum_le_tsum hle hsum).trans ?_)
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hE.2 (by norm_num)

end OVNS.Quant.Metric

end
