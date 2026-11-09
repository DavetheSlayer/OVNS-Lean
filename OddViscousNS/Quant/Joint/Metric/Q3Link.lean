import OddViscousNS.Quant.Joint.Metric.Q3Leaf

/-!
# The third correction: the source and the heat error (step J5, node N8)

`YL_eq_src_add`: on the mask of `Q₃`, the cubic form `⟨G, μ Y 𝓛 F⟩` is the source of `O` plus the
heat form `HtQ`.  So the source of `O` cancels the cubic form on the mask, and `HtQ` stays:
`HtQ_le`: `‖HtQ‖ ≲ q⁻² D √(1 + ln D) W a b`, Body 33's "heat-sum terms ... the original low-ratio
`W a b`".
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open Classical in
/-- The heat sum, on the high sector. -/
def hQ (s : ℕ) (r τ : ℝ) (l a b : Mode) (v w : V3) : Blk :=
  if 4 * absk l ≤ absk (l - a) ∧ 4 * absk (l - a - b) ≤ absk (l - a) then
    tH s r τ l a b v w else 0

lemma tQ_eq (s : ℕ) (r τ : ℝ) (l a b : Mode) (v w : V3) :
    tQ s r τ l a b v w = tR s r τ l a b v w - hQ s r τ l a b v w := by
  simp only [tQ, hQ]
  split_ifs
  · rfl
  · rw [sub_zero]

lemma outerInv_neg (r H : ℝ) (l j : Mode) (T : Blk) :
    outerInv r H l j (-T) = -outerInv r H l j T := by
  simp only [outerInv, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, smul_neg,
    Finset.sum_neg_distrib]

/-- The two-leaf factor against `X₂ + Z`. -/
lemma Yq_eq (s : ℕ) (r τ : ℝ) (f g : Field) (l a b : Mode) :
    Yq s r τ l a b (f a) (g b) = X2b s r τ f g l a b + Zb s r τ f g l a b -
      outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (hQ s r τ l a b (f a) (g b)) := by
  simp only [Yq, X2b, Zb]
  rw [tQ_eq]
  have e : tR s r τ l a b (f a) (g b) - hQ s r τ l a b (f a) (g b) + zR s r τ l a b (f a) (g b) =
      twoRoot s r τ f g l a b + X1b s r τ (a + b) l (l - a - b) (slowV a b (f a) (g b)) +
        -hQ s r τ l a b (f a) (g b) := by
    have e1 : twoRoot s r τ f g l a b = tR s r τ l a b (f a) (g b) := rfl
    have e2 : X1b s r τ (a + b) l (l - a - b) (slowV a b (f a) (g b)) =
        zR s r τ l a b (f a) (g b) := rfl
    rw [e1, e2]
    abel
  rw [e, outerInv_add, outerInv_add, outerInv_neg]
  abel

/-- The block of the heat form. -/
def HB (s : ℕ) (r τ : ℝ) (f g h : Field) (x : I4) : Blk :=
  outerInv r (heat4 x.1 (x.1 - x.2.1 - x.2.2.1) x.2.1 x.2.2.1) x.1 (x.1 - x.2.1 - x.2.2.1)
      (hQ s r τ x.1 x.2.1 x.2.2.1 (f x.2.1) (g x.2.2.1)) ∘L
    Lb s τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x) (h x.2.2.2)

/-- The heat form. -/
def HtQ (D : ℝ) (s : ℕ) (r τ : ℝ) (f g h G F : Field) : ℂ :=
  ∑' x : I4, ((muQ D x : ℝ) : ℂ) * inner ℂ (G x.1) (HB s r τ f g h x (F (inJ x)))

/-- A source term of a three-leaf family on transverse vectors. -/
lemma srcT₃_eq {𝔉 : Fam3} {G F : Field} (hG : ∀ k, leray k (G k) = G k)
    (hF : ∀ k, leray k (F k) = F k) (x : I4) (t v w : V3) (τ : ℝ) :
    𝔉.srcT x (G x.1) (F (inJ x)) t v w τ = inner ℂ (G x.1) (𝔉.Sr x τ t v w (F (inJ x))) := by
  simp only [Fam3.srcT]
  rw [hF, inner_leray_right', hG]

/-- One term of the cubic form on the mask. -/
lemma YL_term (D : ℝ) (s : ℕ) (r τ : ℝ) (f g h : Field) {G F : Field}
    (hG : ∀ k, leray k (G k) = G k) (hF : ∀ k, leray k (F k) = F k) (x : I4) :
    ((muQ D x : ℝ) : ℂ) * inner ℂ (G x.1) (YLb s r τ f g h x (F (inJ x))) =
      (famQ s r D).srcT x (G x.1) (F (inJ x)) (f x.2.1) (g x.2.2.1) (h x.2.2.2) τ +
        ((muQ D x : ℝ) : ℂ) * inner ℂ (G x.1) (HB s r τ f g h x (F (inJ x))) := by
  rw [srcT₃_eq hG hF]
  have eB : YLb s r τ f g h x = Yq s r τ x.1 x.2.1 x.2.2.1 (f x.2.1) (g x.2.2.1) ∘L
      Lb s τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x) (h x.2.2.2) + HB s r τ f g h x := by
    rw [Yq_eq s r τ f g]
    ext1 y
    simp only [YLb, HB, inJ, add_apply, sub_apply, ContinuousLinearMap.comp_apply]
    abel
  have e : (famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1) (h x.2.2.2) (F (inJ x)) =
      ((muQ D x : ℝ) : ℂ) • ((Yq s r τ x.1 x.2.1 x.2.2.1 (f x.2.1) (g x.2.2.1)) ∘L
        Lb s τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x) (h x.2.2.2)) (F (inJ x)) := rfl
  rw [eB, add_apply, inner_add_right, mul_add, e, inner_smul_right]

/-- The arithmetic of the heat block. -/
lemma heat_block_arith {L M K J A B C D q V : ℝ} (hL : 0 < L) (hK : 0 < K) (hJ : 0 < J) (hq : 0 < q)
    (hM : 0 < M) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hV : 0 ≤ V) (hKL : K ≤ 2 * L) (hA : 3 * M ≤ 4 * A)
    (hB : 3 * M ≤ 4 * B) (hAD : A ≤ D) (hw : C ≤ K ^ 2 / J ^ 2) :
    2 ^ 15 * ((M / L) ^ 2 * (M / K) ^ 2) * (1 / q ^ 2) * (16 * C * K) * V ≤
      2 ^ 22 * D / q ^ 2 * (A ^ 2 * B * V * (L⁻¹ * J⁻¹ ^ 2)) := by
  have hD0 : 0 ≤ D := hA0.trans hAD
  have e1 : M ≤ 4 / 3 * D := by linarith
  have e2 : M ≤ 4 / 3 * A := by linarith
  have e3 : M ≤ 4 / 3 * B := by linarith
  have hM4 : M ^ 4 ≤ 4 / 3 * D * (4 / 3 * A) * (4 / 3 * A) * (4 / 3 * B) := by
    calc M ^ 4 = M * M * M * M := by ring
      _ ≤ _ := by gcongr
  have hl : 2 ^ 15 * ((M / L) ^ 2 * (M / K) ^ 2) * (1 / q ^ 2) * (16 * C * K) * V ≤
      2 ^ 15 * ((M / L) ^ 2 * (M / K) ^ 2) * (1 / q ^ 2) * (16 * (K ^ 2 / J ^ 2) * K) * V := by
    gcongr
  refine hl.trans ?_
  have e4 : 2 ^ 15 * ((M / L) ^ 2 * (M / K) ^ 2) * (1 / q ^ 2) * (16 * (K ^ 2 / J ^ 2) * K) * V =
      2 ^ 19 / q ^ 2 * (M ^ 4 * (K * L⁻¹) * V * (L⁻¹ * J⁻¹ ^ 2)) := by
    field_simp
    ring
  rw [e4]
  have hKL' : K * L⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hL]
    exact hKL
  have hp : 0 ≤ V * (L⁻¹ * J⁻¹ ^ 2) := by positivity
  have h1 : M ^ 4 * (K * L⁻¹) ≤ (4 / 3 * D * (4 / 3 * A) * (4 / 3 * A) * (4 / 3 * B)) * 2 :=
    mul_le_mul hM4 hKL' (by positivity) (by positivity)
  calc 2 ^ 19 / q ^ 2 * (M ^ 4 * (K * L⁻¹) * V * (L⁻¹ * J⁻¹ ^ 2))
      = 2 ^ 19 / q ^ 2 * ((M ^ 4 * (K * L⁻¹)) * (V * (L⁻¹ * J⁻¹ ^ 2))) := by ring
    _ ≤ 2 ^ 19 / q ^ 2 * ((4 / 3 * D * (4 / 3 * A) * (4 / 3 * A) * (4 / 3 * B)) * 2 *
        (V * (L⁻¹ * J⁻¹ ^ 2))) := by gcongr
    _ = 2 ^ 19 * (512 / 81) / q ^ 2 * (D * (A ^ 2 * B * V * (L⁻¹ * J⁻¹ ^ 2))) := by ring
    _ ≤ 2 ^ 19 * 8 / q ^ 2 * (D * (A ^ 2 * B * V * (L⁻¹ * J⁻¹ ^ 2))) := by
        have : 0 ≤ D * (A ^ 2 * B * V * (L⁻¹ * J⁻¹ ^ 2)) := by positivity
        gcongr
        norm_num
    _ = _ := by ring

/-- The block of the heat form on the mask. -/
lemma norm_HB_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ} {x : I4}
    (hx : Act₃ x) (hQ' : OnQ D x) (f g h : Field) :
    ‖HB s r τ f g h x‖ ≤ 2 ^ 22 * D / |r| ^ 2 * (absk x.2.1 ^ 2 * absk x.2.2.1 *
      (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) * (bandW (4 * D) x.1 * (absk (inJ x))⁻¹ ^ 2)) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  obtain ⟨ha, hb, hc, hj⟩ := hx
  have hk2 : (x.1 - x.2.1 - x.2.2.1) 2 ≠ 0 := by
    have e : (x.1 - x.2.1 - x.2.2.1) 2 = inJ x 2 := by
      simp [inJ, hc]
    rwa [e]
  obtain ⟨hl0, hm0, hk0⟩ := fast_labels ha hb hk2
  have hj0 : inJ x ≠ 0 := fun h => hj (by rw [h]; rfl)
  have hJ1 := one_le_absk hj0
  have hK1 := one_le_absk hk0
  have hL1 := one_le_absk hl0
  have hM1 := one_le_absk hm0
  obtain ⟨hK15, hL7⟩ := hQ'.lengths
  have hl4 : absk x.1 ≤ 4 * D := by
    have ek : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
      simp only [inJ]
      abel
    have hKJ := absk_add_le x.2.2.2 (inJ x)
    rw [ek] at hKJ
    linarith [hQ'.c_le, hQ'.c_gt, hQ'.l_le]
  have hbd : bandW (4 * D) x.1 = (absk x.1)⁻¹ := by simp [bandW, hl4]
  rw [hbd]
  have hA0 := absk_nonneg x.2.1
  have hB0 := absk_nonneg x.2.2.1
  have hV : 0 ≤ ‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖ := by positivity
  have hR0 : 0 ≤ 2 ^ 22 * D / |r| ^ 2 * (absk x.2.1 ^ 2 * absk x.2.2.1 *
      (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) * ((absk x.1)⁻¹ * (absk (inJ x))⁻¹ ^ 2)) := by
    have hD0 := hA0.trans hQ'.a_le
    positivity
  by_cases hi : 4 * absk x.1 ≤ absk (x.1 - x.2.1) ∧
      4 * absk (x.1 - x.2.1 - x.2.2.1) ≤ absk (x.1 - x.2.1)
  swap
  · have e0 : hQ s r τ x.1 x.2.1 x.2.2.1 (f x.2.1) (g x.2.2.1) = 0 := by
      simp only [hQ, hi, ite_false]
    have e1 : HB s r τ f g h x = 0 := by
      simp only [HB, e0, outerInv_zero, ContinuousLinearMap.zero_comp]
    rw [e1, norm_zero]
    exact hR0
  have e0 : hQ s r τ x.1 x.2.1 x.2.2.1 (f x.2.1) (g x.2.2.1) =
      tH s r τ x.1 x.2.1 x.2.2.1 (f x.2.1) (g x.2.2.1) := by
    simp only [hQ, hi, and_self, ite_true]
  have hX := norm_Xheat_le (show s ≤ 2 by omega) hr τ ha hb hk2 hi.1 hi.2 (f x.2.1) (g x.2.2.1)
  have ek : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
    simp only [inJ]
    abel
  have hE := norm_Lb_le s τ ek (h x.2.2.2)
  have hw : wt s (x.1 - x.2.1 - x.2.2.1) (inJ x) ≤
      absk (x.1 - x.2.1 - x.2.2.1) ^ 2 / absk (inJ x) ^ 2 := by
    have h1 : 1 ≤ absk (x.1 - x.2.1 - x.2.2.1) / absk (inJ x) := by
      rw [one_le_div (by linarith)]
      linarith
    rcases hs with rfl | rfl
    · simp only [wt, pow_one, ← div_pow]
      have : absk (x.1 - x.2.1 - x.2.2.1) / absk (inJ x) ≤
          (absk (x.1 - x.2.1 - x.2.2.1) / absk (inJ x)) ^ 2 := by nlinarith only [h1]
      exact this
    · simp only [wt, ← div_pow]
      exact le_rfl
  obtain ⟨p1, p2, p3, p4⟩ := two_leaf_paths x.1 x.2.1 x.2.2.1
  have hArr := heat_block_arith (L := absk x.1) (M := absk (x.1 - x.2.1))
    (K := absk (x.1 - x.2.1 - x.2.2.1)) (J := absk (inJ x)) (A := absk x.2.1) (B := absk x.2.2.1)
    (C := wt s (x.1 - x.2.1 - x.2.2.1) (inJ x)) (D := D) (q := |r|)
    (V := ‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) (by linarith) (by linarith) (by linarith) hr0
    (by linarith) hA0 hB0 hV hQ'.k_le (by linarith) (by linarith) hQ'.a_le hw
  simp only [HB, e0]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hw0 := wt_nonneg s (x.1 - x.2.1 - x.2.2.1) (inJ x)
  have hK0 := absk_nonneg (x.1 - x.2.1 - x.2.2.1)
  have hn1 := norm_nonneg (f x.2.1)
  have hn2 := norm_nonneg (g x.2.2.1)
  have hn3 := norm_nonneg (h x.2.2.2)
  refine (mul_le_mul hX hE (norm_nonneg _) (by positivity)).trans (le_trans (le_of_eq ?_) hArr)
  ring

/-- The block of the heat form vanishes on a zero leaf. -/
lemma HB_zero {s : ℕ} {r τ : ℝ} {f g h : Field} {x : I4}
    (hz : f x.2.1 = 0 ∨ g x.2.2.1 = 0 ∨ h x.2.2.2 = 0) : HB s r τ f g h x = 0 := by
  have hB := tH_isBil s r τ x.1 x.2.1 x.2.2.1
  rcases hz with hz | hz | hz
  · have e : hQ s r τ x.1 x.2.1 x.2.2.1 (f x.2.1) (g x.2.2.1) = 0 := by
      simp only [hQ, hz, hB.zero_l']
      split_ifs <;> rfl
    simp only [HB, e, outerInv_zero, ContinuousLinearMap.zero_comp]
  · have e : hQ s r τ x.1 x.2.1 x.2.2.1 (f x.2.1) (g x.2.2.1) = 0 := by
      simp only [hQ, hz, hB.zero_r']
      split_ifs <;> rfl
    simp only [HB, e, outerInv_zero, ContinuousLinearMap.zero_comp]
  · simp only [HB, hz, Lb_zero_leaf, ContinuousLinearMap.comp_zero]

/-- The majorant of the heat form. -/
def PsiH (D : ℝ) (f g h G F : Field) (x : I4) : ℝ :=
  nrm G x.1 * bandW (4 * D) x.1 * (nrm F (inJ x) * (absk (inJ x))⁻¹ ^ 2) *
    (up (nrm f) x.2.1 * gr g x.2.2.1 * nrm h x.2.2.2)

lemma PsiH_nonneg (D : ℝ) (f g h G F : Field) (x : I4) : 0 ≤ PsiH D f g h G F x := by
  have a1 := up_nrm_nonneg f x.2.1
  have a2 := gr_nonneg g x.2.2.1
  have a3 : 0 ≤ nrm h x.2.2.2 := norm_nonneg _
  have a4 : 0 ≤ nrm G x.1 := norm_nonneg _
  have a5 : 0 ≤ nrm F (inJ x) := norm_nonneg _
  have a6 := bandW_nonneg (4 * D) x.1
  have a7 := inv_nonneg.2 (absk_nonneg (inJ x))
  unfold PsiH
  positivity

/-- A term of the heat form. -/
lemma HtQ_term {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 1 ≤ D)
    {f g h G F : Field} (hf' : PiS f = f) (hg' : PiS g = g) (hh' : PiS h = h) (hF' : PiF F = F)
    (x : I4) :
    ‖((muQ D x : ℝ) : ℂ) * inner ℂ (G x.1) (HB s r τ f g h x (F (inJ x)))‖ ≤
      2 ^ 22 * D / |r| ^ 2 * PsiH D f g h G F x := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hD0 : 0 ≤ D := by linarith
  have hR : 0 ≤ 2 ^ 22 * D / |r| ^ 2 * PsiH D f g h G F x :=
    mul_nonneg (by positivity) (PsiH_nonneg _ _ _ _ _ _ _)
  by_cases hm : muQ D x = 0
  · rw [hm]
    simpa using hR
  by_cases ha : x.2.1 2 = 0
  swap
  · rw [HB_zero (Or.inl (slow_zero hf' ha))]
    simpa using hR
  by_cases hb : x.2.2.1 2 = 0
  swap
  · rw [HB_zero (Or.inr (Or.inl (slow_zero hg' hb)))]
    simpa using hR
  by_cases hc : x.2.2.2 2 = 0
  swap
  · rw [HB_zero (Or.inr (Or.inr (slow_zero hh' hc)))]
    simpa using hR
  by_cases hj : inJ x 2 = 0
  · rw [fast_zero hF' hj, map_zero, inner_zero_right, mul_zero, norm_zero]
    exact hR
  have hB := norm_HB_le hs hr τ ⟨ha, hb, hc, hj⟩ (onQ_of_ne hm) f g h
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (muQ_nonneg D x)]
  have h1 := norm_inner_apply_le (G x.1) (F (inJ x)) (HB s r τ f g h x)
  have hP : 0 ≤ ‖G x.1‖ * ‖F (inJ x)‖ := by positivity
  calc _ ≤ 1 * (‖G x.1‖ * ‖F (inJ x)‖ * ‖HB s r τ f g h x‖) :=
        mul_le_mul (muQ_le_one D x) h1 (norm_nonneg _) zero_le_one
    _ ≤ 1 * (‖G x.1‖ * ‖F (inJ x)‖ * (2 ^ 22 * D / |r| ^ 2 * (absk x.2.1 ^ 2 * absk x.2.2.1 *
        (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) *
          (bandW (4 * D) x.1 * (absk (inJ x))⁻¹ ^ 2)))) := by
        rw [one_mul, one_mul]
        exact mul_le_mul_of_nonneg_left hB hP
    _ = _ := by
        simp only [PsiH, nrm, up, gr, ← absk_sq x.2.1]
        ring

/-- **The heat form** of the mask: `q⁻² D √(1 + ln D) W a b`. -/
theorem HtQ_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 1 ≤ D)
    {f g h G F : Field} (hf : MZ 2 f) (hf' : PiS f = f) (hg : InH 1 g) (hg' : PiS g = g)
    (hh : InH 2 h) (hh' : PiS h = h) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) :
    (Summable fun x : I4 => ((muQ D x : ℝ) : ℂ) * inner ℂ (G x.1) (HB s r τ f g h x (F (inJ x)))) ∧
    ‖HtQ D s r τ f g h G F‖ ≤ 2 ^ 22 * D / |r| ^ 2 * (l2n G * hnorm 2 f * Real.sqrt 17 *
      (l2n F * hnorm 1 g * Real.sqrt (9 + 8 * Real.log (4 * D))) * wiener h) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hD0 : 0 ≤ D := by linarith
  have hS := pos3_band (D := 4 * D) (by linarith) (l2B_nrm hG) (l2B_nrm hF) (l2B_up hf.inH)
    (l2B_gr hg) (l1B_nrm hh)
    (fun p hp => by simp [up, nrm, slow_zero hf' hp])
    (fun p hp => by simp [gr, slow_zero hg' hp])
  have hS2 : SB (fun x => 2 ^ 22 * D / |r| ^ 2 * PsiH D f g h G F x) _ :=
    hS.const_mul (by positivity : 0 ≤ 2 ^ 22 * D / |r| ^ 2)
  exact form_le hS2 (HtQ_term hs hr τ hD hf' hg' hh' hF')

/-- The term of the source of `O` is summable. -/
lemma srcQ_summable {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ D : ℝ)
    {f g h G F : Field} (hf : MZ 2 f) (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g)
    (hh : MZ 2 h) (hh' : PiS h = h) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) :
    Summable fun x : I4 => (famQ s r D).srcT x (G x.1) (F (inJ x)) (f x.2.1) (g x.2.2.1)
      (h x.2.2.2) τ := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hP := (pos3_sep (l2B_nrm hG) (l2B_nrm hF) (l1B_nrm hf.inH) (l1B_nrm hg.inH) (l1B_nrm hh.inH)
    (l2B_up hf.inH) (l2B_up hg.inH) (l2B_up hh.inH)).const_mul
    (by positivity : 0 ≤ 2 ^ 34 / |r|)
  refine Summable.of_norm_bounded hP.1 fun x => ?_
  refine Fam3.srcT_form_le hf' hg' hh' hF' (B := fun x => 2 ^ 34 / |r| *
    (Phi₃ (nrm G) (nrm F) (nrm f) (nrm g) (nrm h) x * Esep x)) (fun x => ?_) (fun x hx => ?_) x
  · have h1 := Phi₃_nonneg (α := nrm G) (β := nrm F) (f₁ := nrm f) (f₂ := nrm g) (f₃ := nrm h)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) x
    have h2 := Esep_nonneg x
    positivity
  · have h0 := norm_source_le (D := D) hs hr τ hx (f x.2.1) (g x.2.2.1) (h x.2.2.2)
    have hn : ‖(famQ s r D).srcT x (G x.1) (F (inJ x)) (f x.2.1) (g x.2.2.1) (h x.2.2.2) τ‖ ≤
        ‖G x.1‖ * ‖F (inJ x)‖ * ‖(famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1) (h x.2.2.2)‖ := by
      refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
      have h1 := norm_leray_le x.1 ((famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1) (h x.2.2.2)
        (leray (inJ x) (F (inJ x))))
      have h2 := (ContinuousLinearMap.le_opNorm ((famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1)
        (h x.2.2.2)) (leray (inJ x) (F (inJ x)))).trans (mul_le_mul_of_nonneg_left
          (norm_leray_le _ _) (norm_nonneg _))
      calc _ ≤ ‖G x.1‖ * (‖(famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1) (h x.2.2.2)‖ *
            ‖F (inJ x)‖) := mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
        _ = _ := by ring
    refine hn.trans ?_
    have hP2 : 0 ≤ ‖G x.1‖ * ‖F (inJ x)‖ := by positivity
    refine (mul_le_mul_of_nonneg_left h0 hP2).trans (le_of_eq ?_)
    simp only [Phi₃, nrm]
    ring

/-- **The source of `O` is the cubic form on the mask, minus the heat form.** -/
theorem YL_eq_src_add {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 1 ≤ D)
    {f g h G F : Field} (hf : MZ 2 f) (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g)
    (hh : MZ 2 h) (hh' : PiS h = h) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) (hGl : ∀ k, leray k (G k) = G k)
    (hFl : ∀ k, leray k (F k) = F k) :
    YLForm (fun x => ((muQ D x : ℝ) : ℂ)) s r τ f g h G F =
      (famQ s r D).src τ f g h G F + HtQ D s r τ f g h G F := by
  have s1 := srcQ_summable hs hr τ D hf hf' hg hg' hh hh' hG hF hF'
  have s2 := (HtQ_le hs hr τ hD hf hf' (hg.inH.mono (by norm_num)) hg' hh.inH hh' hG hF hF').1
  simp only [YLForm, Fam3.src, HtQ]
  rw [← s1.tsum_add s2]
  exact tsum_congr fun x => YL_term D s r τ f g h hGl hFl x

/-- **`Q₃` on the actual path.** -/
theorem Q3_identity {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ENNReal} {s : ℕ}
    (hs : s = 1 ∨ s = 2) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (D : ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable ((famQ s r D).rhs s r g y) volume a b ∧
      (famQ s r D).val s r g y b - (famQ s r D).val s r g y a =
        ∫ u in a..b, (famQ s r D).rhs s r g y u :=
  Fam3.identity (famQ_bd hs hr D) hs h hr ha hab hb

end OVNS.Quant.Metric

end
