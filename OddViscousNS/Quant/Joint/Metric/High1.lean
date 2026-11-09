import OddViscousNS.Quant.Joint.Metric.Sep1Form

/-!
# Weight one: a high ancestor on the high last edge (step J5, node N10)

On `K ≥ J` the last edge at weight one is below the last edge at weight two, and the blocks of
`X₂`, `Z` have the same bound at both weights.  So `E₃` pays, and with it the proof of rows 2, 3.
This sector does not exist in the unit, whose `Q₃,₁` has no cut.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {D : ℝ}

/-- **The kernel at weight one, on `K ≥ J`.** -/
theorem norm_YLb_one_hi {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g h : Field) {x : I4} (ha : x.2.1 2 = 0)
    (hb : x.2.2.1 2 = 0) (hc : x.2.2.2 2 = 0) (hj : inJ x 2 ≠ 0)
    (hKJ : absk (inJ x) ≤ absk (x.1 - x.2.1 - x.2.2.1)) :
    ‖YLb 1 r τ f g h x‖ ≤
      2 ^ 21 / |r| * (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) * E3 x := by
  obtain ⟨l, a, b, c⟩ := x
  simp only at ha hb hc ⊢
  have hjj : (l - a - b - c) 2 ≠ 0 := hj
  have hKJ' : absk (l - a - b - c) ≤ absk (l - a - b) := hKJ
  have hk : (l - a - b) 2 ≠ 0 := fun h0 => hjj (by simp only [Pi.sub_apply] at h0 ⊢; simp [hc, h0])
  obtain ⟨hl0, hm0, hk0⟩ := fast_labels ha hb hk
  have hj0 : l - a - b - c ≠ 0 := fun h0 => hjj (by rw [h0]; rfl)
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absSq l := by linarith [one_le_absSq hl0]
  have hJ : 0 < absSq (l - a - b - c) := by linarith [one_le_absSq hj0]
  have hK : 0 < absSq (l - a - b) := by linarith [one_le_absSq hk0]
  have hH := heat4_pos (l := l) hk0 a b
  have e1 : c + (l - a - b - c) = l - a - b := by abel
  have h1 := norm_X2b_le (s := 1) (Or.inl rfl) hr τ f g ha hb hk
  simp only [absk_sq] at h1
  have h2 := norm_Zb_le (s := 1) (Or.inl rfl) hr τ f g ha hb hk
  have h3 : ‖Lb 1 τ c (l - a - b) (l - a - b - c) (h c)‖ ≤
      16 * (absSq (l - a - b) / absSq (l - a - b - c)) * absk (l - a - b) * ‖h c‖ := by
    have h4 := norm_Lb_le 1 τ e1 (h c)
    simp only [wt, pow_one] at h4
    refine h4.trans ?_
    have hJp : 0 < absk (l - a - b - c) := lt_of_lt_of_le one_pos (one_le_absk hj0)
    have hKp := absk_nonneg (l - a - b)
    have h5 : absk (l - a - b) / absk (l - a - b - c) ≤
        absSq (l - a - b) / absSq (l - a - b - c) := by
      rw [← absk_sq, ← absk_sq]
      have h6 : 1 ≤ absk (l - a - b) / absk (l - a - b - c) := (one_le_div hJp).2 hKJ'
      rw [← div_pow]
      nlinarith only [h6]
    gcongr
  set A := absSq a
  set B := absSq b
  set C := absSq c
  set L2 := absSq l
  set M2 := absSq (l - a)
  set K2 := absSq (l - a - b)
  set J2 := absSq (l - a - b - c)
  set S4 := heat4 l (l - a - b) a b
  set M₁ := absk (l - a)
  set K₁ := absk (l - a - b)
  set P₁ := absk (a + b)
  have hA : 0 ≤ A := absSq_nonneg _
  have hB : 0 ≤ B := absSq_nonneg _
  have hC : 0 ≤ C := absSq_nonneg _
  have hM2 : 0 ≤ M2 := absSq_nonneg _
  have hM₁ : 0 ≤ M₁ := absk_nonneg _
  have hK₁ : 0 ≤ K₁ := absk_nonneg _
  have hP₁ : 0 ≤ P₁ := absk_nonneg _
  have t1 : L2 ≤ 4 * (J2 + A + B + C) := absSq_le₄ (by abel)
  have t2 : M2 ≤ 2 * (L2 + A) := (two_leaf_triangles l a b).2.2.1
  have t3 : M2 ≤ 3 * (J2 + B + C) := absSq_le₃ (by abel)
  have t4 : K2 ≤ 3 * (L2 + A + B) := by
    have := absSq_le₃ (k := l - a - b) (u := l) (v := -a) (w := -b) (by abel)
    rwa [absSq_neg, absSq_neg] at this
  have t5 : K2 ≤ 2 * (J2 + C) := absSq_le₂ (by abel)
  have hE : E3 (l, a, b, c) =
      1 + (A + B + C) / L2 + (A + B + C) / J2 + (A * B + A * C + B * C) / (L2 * J2) := rfl
  rw [hE]
  set E := 1 + (A + B + C) / L2 + (A + B + C) / J2 + (A * B + A * C + B * C) / (L2 * J2) with hEd
  have hE0 : 0 ≤ E := by positivity
  have hk1 := kerA_le hL hJ hM2 hK.le hA hB hC t1 t2 t3 t4 t5
  have hk2 := kerB_le hL hJ hK.le hA hB hC t1 t4 t5
  rw [← hEd] at hk1 hk2
  have hr1 : M₁ * K₁ / S4 ≤ 1 := (div_le_one hH).2 (chain_ratio_le hk0)
  have hr2 : P₁ * K₁ / S4 ≤ 1 := (div_le_one hH).2 (merged_ratio_le l a b)
  have hf0 := norm_nonneg (f a)
  have hg0 := norm_nonneg (g b)
  have hh0 := norm_nonneg (h c)
  have eK : Br L2 M2 K2 * (K2 / J2) = L2 / J2 + 2 * M2 ^ 2 / (L2 * J2) + K2 ^ 2 / (L2 * J2) := by
    simp only [Br]
    field_simp
  have eZ : (L2 / K2 + K2 / L2) * (K2 / J2) = L2 / J2 + K2 ^ 2 / (L2 * J2) := by
    field_simp
  have hBK : 0 ≤ Br L2 M2 K2 := by simp only [Br]; positivity
  have hRZ : 0 ≤ L2 / K2 + K2 / L2 := by positivity
  have hX : ‖X2b 1 r τ f g l a b‖ * ‖Lb 1 τ c (l - a - b) (l - a - b - c) (h c)‖ ≤
      2 ^ 16 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (22 * E) := by
    calc _ ≤ (2816 / |r| * (M₁ / S4) * (‖f a‖ * ‖g b‖) * Br L2 M2 K2) *
          (16 * (K2 / J2) * K₁ * ‖h c‖) := mul_le_mul h1 h3 (norm_nonneg _) (by positivity)
      _ = 45056 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (M₁ * K₁ / S4) *
            (Br L2 M2 K2 * (K2 / J2)) := by ring
      _ ≤ 45056 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * 1 * (22 * E) := by
          rw [eK]
          have hnn : 0 ≤ L2 / J2 + 2 * M2 ^ 2 / (L2 * J2) + K2 ^ 2 / (L2 * J2) := by positivity
          gcongr
      _ ≤ _ := by
          rw [mul_one]
          gcongr
          norm_num
  have hZ : ‖Zb 1 r τ f g l a b‖ * ‖Lb 1 τ c (l - a - b) (l - a - b - c) (h c)‖ ≤
      2 ^ 15 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (10 * E) := by
    calc _ ≤ (1408 / |r| * (P₁ / S4) * (‖f a‖ * ‖g b‖) * (L2 / K2 + K2 / L2)) *
          (16 * (K2 / J2) * K₁ * ‖h c‖) := mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
      _ = 22528 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (P₁ * K₁ / S4) *
            ((L2 / K2 + K2 / L2) * (K2 / J2)) := by ring
      _ ≤ 22528 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * 1 * (10 * E) := by
          rw [eZ]
          have hnn : 0 ≤ L2 / J2 + K2 ^ 2 / (L2 * J2) := by positivity
          gcongr
      _ ≤ _ := by
          rw [mul_one]
          gcongr
          norm_num
  have hcomp : ‖YLb 1 r τ f g h (l, a, b, c)‖ ≤
      (‖X2b 1 r τ f g l a b‖ + ‖Zb 1 r τ f g l a b‖) *
        ‖Lb 1 τ c (l - a - b) (l - a - b - c) (h c)‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
  refine hcomp.trans ?_
  rw [add_mul]
  refine (add_le_add hX hZ).trans ?_
  have hT : 0 ≤ (‖f a‖ * ‖g b‖ * ‖h c‖) * E / |r| := by positivity
  have e : 2 ^ 21 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * E -
      (2 ^ 16 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (22 * E) +
        2 ^ 15 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (10 * E)) =
      (2 ^ 21 - 2 ^ 16 * 22 - 2 ^ 15 * 10) * ((‖f a‖ * ‖g b‖ * ‖h c‖) * E / |r|) := by
    ring
  have h9 : (0 : ℝ) ≤ 2 ^ 21 - 2 ^ 16 * 22 - 2 ^ 15 * 10 := by norm_num
  have := mul_nonneg h9 hT
  linarith

/-- The support of the complement of the low pass. -/
lemma lowM_gt {p j : Mode} (h : (1 - lowM p j : ℝ) ≠ 0) : 16 * absk j < absk p := by
  by_contra hc
  rw [not_lt] at hc
  apply h
  have hJ := lt_two_pow_bnd j
  have hle : absk p ≤ 2 ^ (bnd j + 5) := by
    have e : (2 : ℝ) ^ (bnd j + 5) = 16 * 2 ^ (bnd j + 1) := by ring
    rw [e]
    linarith
  have : lowM p j = 1 := chiM_one hle
  rw [this]
  simp

/-- A term of the cubic form at weight one, on the high last edge. -/
lemma YL_one_summand {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {f g h G F : Field} (hf : PiS f = f)
    (hg : PiS g = g) (hh : PiS h = h) (hF : PiF F = F) {μ : ℂ} {x : I4}
    (hμ : μ ≠ 0 → 16 * absk (inJ x) < absk x.2.2.2) :
    ‖μ * inner ℂ (G x.1) (YLb 1 r τ f g h x (F (inJ x)))‖ ≤
      2 ^ 21 / |r| * (‖μ‖ * (‖G x.1‖ * ‖F (inJ x)‖ * (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖)) *
        E3 x) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hE := E3_nonneg x
  have hR : 0 ≤ 2 ^ 21 / |r| * (‖μ‖ * (‖G x.1‖ * ‖F (inJ x)‖ *
      (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖)) * E3 x) := by positivity
  have hzero : ∀ (hb0 : YLb 1 r τ f g h x = 0), ‖μ * inner ℂ (G x.1)
      (YLb 1 r τ f g h x (F (inJ x)))‖ ≤ 2 ^ 21 / |r| * (‖μ‖ * (‖G x.1‖ * ‖F (inJ x)‖ *
        (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖)) * E3 x) := fun hb0 => by
    simpa [hb0] using hR
  by_cases hm : μ = 0
  · simp [hm]
  by_cases ha : x.2.1 2 = 0
  swap
  · exact hzero (YLb_eq_zero (Or.inl (slow_zero hf ha)))
  by_cases hb : x.2.2.1 2 = 0
  swap
  · exact hzero (YLb_eq_zero (Or.inr (Or.inl (slow_zero hg hb))))
  by_cases hc : x.2.2.2 2 = 0
  swap
  · exact hzero (YLb_eq_zero (Or.inr (Or.inr (slow_zero hh hc))))
  by_cases hj : inJ x 2 = 0
  · have : F (inJ x) = 0 := fast_zero hF hj
    simp [this]
  obtain ⟨hK15, -⟩ := last_lengths (hμ hm)
  have hKJ : absk (inJ x) ≤ absk (x.1 - x.2.1 - x.2.2.1) := by
    have := absk_nonneg (inJ x)
    linarith
  have hK := norm_YLb_one_hi hr τ f g h ha hb hc hj hKJ
  rw [norm_mul]
  calc ‖μ‖ * ‖inner ℂ (G x.1) (YLb 1 r τ f g h x (F (inJ x)))‖
      ≤ ‖μ‖ * (‖G x.1‖ * ‖F (inJ x)‖ * ‖YLb 1 r τ f g h x‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_apply_le _ _ _) (norm_nonneg _)
    _ ≤ ‖μ‖ * (‖G x.1‖ * ‖F (inJ x)‖ * (2 ^ 21 / |r| *
        (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) * E3 x)) := by gcongr
    _ = _ := by ring

/-- **A high ancestor on the high last edge, at weight one**: the bound of rows 2, 3. -/
theorem YLForm_high_one {r : ℝ} (hr : r ≠ 0) (τ D : ℝ) {S G F : Field} (hS : MZ 2 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) {μ : I4 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ ‖hiMask₃ D x‖)
    (hμ2 : ∀ x, μ x ≠ 0 → 16 * absk (inJ x) < absk x.2.2.2) :
    (Summable fun x : I4 => μ x * inner ℂ (G x.1) (YLb 1 r τ S S S x (F (inJ x)))) ∧
    ‖YLForm μ 1 r τ S S S G F‖ ≤ Cm3 / |r| *
      (tailW D S * hnorm 2 S ^ 2 + wiener S * hnorm 2 S * tailB D S) * (l2n G * l2n F) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hc := c4_pos
  set b := hnorm 2 S with hb
  set W := wiener S with hWd
  set W' := tailW D S with hW'd
  set b' := tailB D S with hb'd
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have hb'0 : 0 ≤ b' := tailB_nonneg _ _
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => norm_nonneg _
  have hW'0 : 0 ≤ W' := tailW_nonneg _ _
  have hWb : W ≤ c4 * b := wiener_le hS
  have ha := l2B_nrm hG
  have hβ := l2B_nrm hF
  have W1 : L1B (nrm S) W := l1B_nrm hS.inH
  have U1 : L2B (up (nrm S)) b := l2B_up hS.inH
  have W2 : L1B (nrm (hiP D S)) W' := l1B_nrm (inH_hiP hS.inH)
  have U2 : L2B (up (nrm (hiP D S))) b' := l2B_up (inH_hiP hS.inH)
  have p1 := pos3_E3 ha hβ W2 W1 W1 U2 U1 U1
  have p2 := pos3_E3 ha hβ W1 W2 W1 U1 U2 U1
  have p3 := pos3_E3 ha hβ W1 W1 W2 U1 U1 U2
  have hK : (0 : ℝ) ≤ 2 ^ 21 / |r| := by positivity
  have hΨ := ((p1.add p2).add p3).const_mul hK
  have hpt : ∀ x : I4, ‖μ x * inner ℂ (G x.1) (YLb 1 r τ S S S x (F (inJ x)))‖ ≤
      2 ^ 21 / |r| * (Phi₃ (nrm G) (nrm F) (nrm (hiP D S)) (nrm S) (nrm S) x * E3 x +
        Phi₃ (nrm G) (nrm F) (nrm S) (nrm (hiP D S)) (nrm S) x * E3 x +
        Phi₃ (nrm G) (nrm F) (nrm S) (nrm S) (nrm (hiP D S)) x * E3 x) := fun x => by
    refine (YL_one_summand hr τ hS' hS' hS' hF' (hμ2 x)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK
    have hE := E3_nonneg x
    have h1 : ‖μ x‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖) ≤
        ‖hiMask₃ D x‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖) :=
      mul_le_mul_of_nonneg_right (hμ x) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left (h1.trans (mask₃_le D S x))
      (by positivity : 0 ≤ ‖G x.1‖ * ‖F (inJ x)‖ * E3 x)
    simp only [Phi₃, nrm]
    nlinarith only [h2]
  obtain ⟨hsum, hle⟩ := form_le hΨ hpt
  refine ⟨hsum, hle.trans ?_⟩
  have c1 := cls3_tail hW0 hb0 hW'0 hb'0 hWb
  have e2 : cls3 W W' W b b' b = cls3 W' W W b' b b := by simp only [cls3]; ring
  have e3 : cls3 W W W' b b b' = cls3 W' W W b' b b := by simp only [cls3]; ring
  have hL := mul_nonneg (l2n_nonneg G) (l2n_nonneg F)
  have hT1 : 0 ≤ c4 ^ 2 * (W' * b ^ 2) := by positivity
  have hT2 : 0 ≤ c4 ^ 2 * (W * b * b') := by positivity
  have htot : l2n G * l2n F * cls3 W' W W b' b b + l2n G * l2n F * cls3 W W' W b b' b +
      l2n G * l2n F * cls3 W W W' b b b' ≤
      l2n G * l2n F * (18 * c4 ^ 2 * (W' * b ^ 2 + W * b * b')) := by
    rw [e2, e3]
    have := mul_le_mul_of_nonneg_left c1 hL
    nlinarith only [this, mul_nonneg hL hT1, mul_nonneg hL hT2]
  calc 2 ^ 21 / |r| * (l2n G * l2n F * cls3 W' W W b' b b + l2n G * l2n F * cls3 W W' W b b' b +
        l2n G * l2n F * cls3 W W W' b b b')
      ≤ 2 ^ 21 / |r| * (l2n G * l2n F * (18 * c4 ^ 2 * (W' * b ^ 2 + W * b * b'))) :=
        mul_le_mul_of_nonneg_left htot hK
    _ = _ := by
        simp only [Cm3]
        ring

end OVNS.Quant.Metric

end
