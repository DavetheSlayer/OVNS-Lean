import OddViscousNS.Quant.Joint.Metric.Q3Def

/-!
# The third correction: the blocks (step J5, node N8)

`norm_Yq_le`: on comparable `L, K` the two-leaf factor is at most `q⁻¹ (1/K + P₁ P₂/K³)`: the
ordinary kernel and the phase/noncommon kernel of Body 33.  With the last edge,
`norm_source_le`: the source of `Q₃` is at most `q⁻¹ (1 + (P₁² + P₂² + P₃²)/J²)`, which is Body 33's
`C L²/J²` and `C P₁ P₂/J²`.
`hi_last`: on the mask, `P₃ > 16 J`, so `L > 4 J`, and `norm_Q3_block_le`: the third inverse gains
`1/(q L)`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-- The kernel of the source of `Q₃`. -/
def Esep (x : I4) : ℝ := 1 + (absSq x.2.1 + absSq x.2.2.1 + absSq x.2.2.2) / absSq (inJ x)

lemma Esep_nonneg (x : I4) : 0 ≤ Esep x := by
  have h1 := absSq_nonneg x.2.1
  have h2 := absSq_nonneg x.2.2.1
  have h3 := absSq_nonneg x.2.2.2
  have h4 := absSq_nonneg (inJ x)
  unfold Esep
  positivity

lemma one_le_Esep (x : I4) : 1 ≤ Esep x := by
  have h1 := absSq_nonneg x.2.1
  have h2 := absSq_nonneg x.2.2.1
  have h3 := absSq_nonneg x.2.2.2
  have h4 := absSq_nonneg (inJ x)
  have : 0 ≤ (absSq x.2.1 + absSq x.2.2.1 + absSq x.2.2.2) / absSq (inJ x) := by positivity
  unfold Esep
  linarith

lemma Esep_le_E3 (x : I4) : Esep x ≤ E3 x := by
  have h1 := absSq_nonneg x.2.1
  have h2 := absSq_nonneg x.2.2.1
  have h3 := absSq_nonneg x.2.2.2
  have h4 := absSq_nonneg (inJ x)
  have h5 := absSq_nonneg x.1
  have t1 : 0 ≤ (absSq x.2.1 + absSq x.2.2.1 + absSq x.2.2.2) / absSq x.1 := by positivity
  have t2 : 0 ≤ (absSq x.2.1 * absSq x.2.2.1 + absSq x.2.1 * absSq x.2.2.2 +
      absSq x.2.2.1 * absSq x.2.2.2) / (absSq x.1 * absSq (inJ x)) := by positivity
  unfold Esep E3
  linarith

/-- The ordinary two-leaf factor. -/
lemma Yq_ord {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode}
    (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (h1 : absk l ≤ 2 * absk (l - a - b))
    (h2 : absk (l - a - b) ≤ 2 * absk l)
    (hM : ¬(4 * absk l ≤ absk (l - a) ∧ 4 * absk (l - a - b) ≤ absk (l - a))) (v w : V3) :
    ‖Yq s r τ l a b v w‖ ≤ 2 ^ 29 / |r| * (‖v‖ * ‖w‖) * (absk (l - a - b))⁻¹ := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hM0 : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hH : 0 < heat4 l (l - a - b) a b := heat4_pos hj0 a b
  have hV : 0 ≤ ‖v‖ * ‖w‖ := by positivity
  have eQ : tQ s r τ l a b v w = tR s r τ l a b v w := by
    simp only [tQ, hM, ite_false]
  have hM8L : absk (l - a) ≤ 8 * absk l := by
    by_contra h
    rw [not_le] at h
    exact hM ⟨by linarith, by linarith⟩
  have hM8K : absk (l - a) ≤ 8 * absk (l - a - b) := by
    by_contra h
    rw [not_le] at h
    exact hM ⟨by linarith, by linarith⟩
  have hHH : absk l ^ 2 + absk (l - a - b) ^ 2 ≤ heat4 l (l - a - b) a b := by
    unfold heat4
    rw [absk_sq, absk_sq]
    have := absSq_nonneg a
    have := absSq_nonneg b
    linarith
  have ho := half_ord hL hK hM0.le h1 h2 hM8L hM8K hHH
  have ee : Br (absk l ^ 2) (absk (l - a) ^ 2) (absk (l - a - b) ^ 2) =
      Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) := by
    rw [absk_sq, absk_sq, absk_sq]
  rw [ee] at ho
  set Br0 := Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) with hBr0
  set L := absk l
  set K := absk (l - a - b)
  set M := absk (l - a)
  set H := heat4 l (l - a - b) a b
  have hYq : Yq s r τ l a b v w = outerInv r H l (l - a - b)
      (tR s r τ l a b v w + zR s r τ l a b v w) := by
    simp only [Yq]
    rw [eQ]
  rw [hYq]
  refine (norm_outerInv_le hH r l (l - a - b) _).trans ?_
  have hR := norm_tR_le hs hr τ ha hb hj v w
  have hZ := norm_zR_le hs hr τ ha hb hj v w
  have hP : absk (a + b) ≤ L + K := by
    have e : a + b = l - (l - a - b) := by abel
    rw [e]
    exact absk_sub_le _ _
  have hra : absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l ≤ 8 := by
    rw [← absk_sq l, ← absk_sq (l - a - b)]
    have e1 : L ^ 2 / K ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [h1, hL, hK]
    have e2 : K ^ 2 / L ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [h2, hL, hK]
    linarith
  have hBq : 0 ≤ Br0 := by
    have := absSq_nonneg l
    have := absSq_nonneg (l - a)
    have := absSq_nonneg (l - a - b)
    simp only [hBr0, Br]
    positivity
  have e0 : (L + K) / H ≤ 2 * K⁻¹ := by
    have h8 : (L + K) * K ≤ 2 * H := by
      nlinarith only [hHH, sq_nonneg (L - K), sq_nonneg L, sq_nonneg K]
    have h9 : (L + K) * K / H ≤ 2 := by
      rw [div_le_iff₀ hH]
      exact h8
    calc (L + K) / H = (L + K) * K / H * K⁻¹ := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h9 (by positivity)
  have e1 : M / H * Br0 ≤ 131200 * K⁻¹ := by
    have h3 : L * (M / H) * Br0 ≤ 65600 := ho
    have h4 : M / H * Br0 ≤ 65600 * L⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hL]
      calc _ = L * (M / H) * Br0 := by ring
        _ ≤ _ := h3
    have h5 : L⁻¹ ≤ 2 * K⁻¹ := by
      rw [inv_le_comm₀ hL (by positivity), mul_inv, inv_inv]
      linarith
    linarith
  have hS : ‖tR s r τ l a b v w + zR s r τ l a b v w‖ ≤
      704 / |r| * M * (‖v‖ * ‖w‖) * Br0 + 352 / |r| * (L + K) * (‖v‖ * ‖w‖) * 8 := by
    refine (norm_add_le _ _).trans (add_le_add hR ?_)
    refine hZ.trans ?_
    have h7 : 0 ≤ absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l := by
      have := absSq_nonneg l
      have := absSq_nonneg (l - a - b)
      positivity
    gcongr
  have hmul := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 4 / H)
  refine hmul.trans ?_
  have e3 : 4 / H * (704 / |r| * M * (‖v‖ * ‖w‖) * Br0 + 352 / |r| * (L + K) * (‖v‖ * ‖w‖) * 8) =
      1 / |r| * (‖v‖ * ‖w‖) * (2816 * (M / H * Br0) + 11264 * ((L + K) / H)) := by
    field_simp
    ring
  rw [e3]
  have e4 : 2816 * (M / H * Br0) + 11264 * ((L + K) / H) ≤ 2 ^ 29 * K⁻¹ := by
    have : 0 ≤ K⁻¹ := by positivity
    nlinarith only [e0, e1, this]
  calc _ ≤ 1 / |r| * (‖v‖ * ‖w‖) * (2 ^ 29 * K⁻¹) := mul_le_mul_of_nonneg_left e4 (by positivity)
    _ = _ := by ring

/-- The two-leaf factor at a large intermediate. -/
lemma Yq_high {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode}
    (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (h1 : absk l ≤ 2 * absk (l - a - b))
    (h2 : absk (l - a - b) ≤ 2 * absk l)
    (hM : 4 * absk l ≤ absk (l - a) ∧ 4 * absk (l - a - b) ≤ absk (l - a)) (v w : V3) :
    ‖Yq s r τ l a b v w‖ ≤ 2 ^ 29 / |r| * (‖v‖ * ‖w‖) *
      ((absk (l - a - b))⁻¹ + absk a * absk b * (absk (l - a - b))⁻¹ ^ 3) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hM0 : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hH : 0 < heat4 l (l - a - b) a b := heat4_pos hj0 a b
  have hV : 0 ≤ ‖v‖ * ‖w‖ := by positivity
  have eQ : tQ s r τ l a b v w = tR s r τ l a b v w - tH s r τ l a b v w := by
    simp only [tQ, hM, and_self, ite_true]
  have hX := norm_Xph_le (show s ≤ 2 by omega) hr τ ha hb hj hM.1 hM.2 v w
  have hA0 := absk_nonneg a
  have hB0 := absk_nonneg b
  obtain ⟨p1, p2, p3, p4⟩ := two_leaf_paths l a b
  have hHH : absk l ^ 2 + absk (l - a - b) ^ 2 ≤ heat4 l (l - a - b) a b := by
    unfold heat4
    rw [absk_sq, absk_sq]
    have := absSq_nonneg a
    have := absSq_nonneg b
    linarith
  have hZ := norm_zR_le hs hr τ ha hb hj v w
  have hP : absk (a + b) ≤ absk l + absk (l - a - b) := by
    have e : a + b = l - (l - a - b) := by abel
    rw [e]
    exact absk_sub_le _ _
  have hYq : Yq s r τ l a b v w =
      outerInv r (heat4 l (l - a - b) a b) l (l - a - b)
        (tR s r τ l a b v w - tH s r τ l a b v w) +
      outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (zR s r τ l a b v w) := by
    simp only [Yq]
    rw [eQ, outerInv_add]
  rw [hYq]
  have hZ2 := norm_outerInv_le hH r l (l - a - b) (zR s r τ l a b v w)
  set L := absk l
  set K := absk (l - a - b)
  set M := absk (l - a)
  set A := absk a
  set B := absk b
  set H := heat4 l (l - a - b) a b
  have hra : absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l ≤ 8 := by
    rw [← absk_sq l, ← absk_sq (l - a - b)]
    have e1 : L ^ 2 / K ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [h1, hL, hK]
    have e2 : K ^ 2 / L ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [h2, hL, hK]
    linarith
  have e0 : (L + K) / H ≤ 2 * K⁻¹ := by
    have h8 : (L + K) * K ≤ 2 * H := by
      nlinarith only [hHH, sq_nonneg (L - K), sq_nonneg L, sq_nonneg K]
    have h9 : (L + K) * K / H ≤ 2 := by
      rw [div_le_iff₀ hH]
      exact h8
    calc (L + K) / H = (L + K) * K / H * K⁻¹ := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h9 (by positivity)
  have hS2 : ‖outerInv r H l (l - a - b) (zR s r τ l a b v w)‖ ≤
      22528 / |r| * (‖v‖ * ‖w‖) * K⁻¹ := by
    have h7 : 0 ≤ absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l := by
      have := absSq_nonneg l
      have := absSq_nonneg (l - a - b)
      positivity
    have h3 : ‖zR s r τ l a b v w‖ ≤ 352 / |r| * (L + K) * (‖v‖ * ‖w‖) * 8 := by
      refine hZ.trans ?_
      gcongr
    calc _ ≤ 4 / H * (352 / |r| * (L + K) * (‖v‖ * ‖w‖) * 8) :=
          hZ2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
      _ = 11264 / |r| * (‖v‖ * ‖w‖) * ((L + K) / H) := by
          field_simp
          ring
      _ ≤ 11264 / |r| * (‖v‖ * ‖w‖) * (2 * K⁻¹) := mul_le_mul_of_nonneg_left e0 (by positivity)
      _ = _ := by ring
  have hS1 : ‖outerInv r H l (l - a - b) (tR s r τ l a b v w - tH s r τ l a b v w)‖ ≤
      2 ^ 19 / |r| * (‖v‖ * ‖w‖) * (A * B * K⁻¹ ^ 3) := by
    refine hX.trans ?_
    have hA34 : 3 * M ≤ 4 * A := by linarith
    have hB34 : 3 * M ≤ 4 * B := by linarith
    have hMs : 9 * M ^ 2 ≤ 16 * (A * B) := by
      have := mul_le_mul hA34 hB34 (by positivity) (by positivity)
      nlinarith only [this]
    have e1 : (M / L) ^ 2 * (M / K) ^ 2 * ((L + K) / (|r| * M ^ 2)) =
        1 / |r| * (M ^ 2 * ((L + K) * L⁻¹ ^ 2) * K⁻¹ ^ 2) := by
      field_simp
    have h3 : (L + K) * L⁻¹ ^ 2 ≤ 6 * K⁻¹ := by
      have h4 : L + K ≤ 3 * L := by linarith
      have h5 : L⁻¹ ≤ 2 * K⁻¹ := by
        rw [inv_le_comm₀ hL (by positivity), mul_inv, inv_inv]
        linarith
      calc (L + K) * L⁻¹ ^ 2 = (L + K) * L⁻¹ * L⁻¹ := by ring
        _ ≤ 3 * L * L⁻¹ * L⁻¹ := by gcongr
        _ = 3 * L⁻¹ := by field_simp
        _ ≤ _ := by linarith
    have h6 : M ^ 2 * ((L + K) * L⁻¹ ^ 2) * K⁻¹ ^ 2 ≤ 16 / 9 * (A * B) * (6 * K⁻¹) * K⁻¹ ^ 2 := by
      have h7 : M ^ 2 ≤ 16 / 9 * (A * B) := by linarith
      gcongr
    calc 2 ^ 15 * ((M / L) ^ 2 * (M / K) ^ 2) * (‖v‖ * ‖w‖) * ((L + K) / (|r| * M ^ 2))
        = 2 ^ 15 * (‖v‖ * ‖w‖) * ((M / L) ^ 2 * (M / K) ^ 2 * ((L + K) / (|r| * M ^ 2))) := by ring
      _ = 2 ^ 15 * (‖v‖ * ‖w‖) * (1 / |r| * (M ^ 2 * ((L + K) * L⁻¹ ^ 2) * K⁻¹ ^ 2)) := by rw [e1]
      _ ≤ 2 ^ 15 * (‖v‖ * ‖w‖) * (1 / |r| * (16 / 9 * (A * B) * (6 * K⁻¹) * K⁻¹ ^ 2)) := by
          gcongr
      _ = 32 / 3 * 2 ^ 15 / |r| * (‖v‖ * ‖w‖) * (A * B * K⁻¹ ^ 3) := by ring
      _ ≤ _ := by
          have : 0 ≤ 1 / |r| * (‖v‖ * ‖w‖) * (A * B * K⁻¹ ^ 3) := by positivity
          have e2 : 32 / 3 * 2 ^ 15 / |r| * (‖v‖ * ‖w‖) * (A * B * K⁻¹ ^ 3) =
              (32 / 3 * 2 ^ 15) * (1 / |r| * (‖v‖ * ‖w‖) * (A * B * K⁻¹ ^ 3)) := by ring
          have e3 : 2 ^ 19 / |r| * (‖v‖ * ‖w‖) * (A * B * K⁻¹ ^ 3) =
              2 ^ 19 * (1 / |r| * (‖v‖ * ‖w‖) * (A * B * K⁻¹ ^ 3)) := by ring
          rw [e2, e3]
          nlinarith only [this]
  refine (norm_add_le _ _).trans ((add_le_add hS1 hS2).trans ?_)
  have hp1 : 0 ≤ 1 / |r| * (‖v‖ * ‖w‖) * (A * B * K⁻¹ ^ 3) := by positivity
  have hp2 : 0 ≤ 1 / |r| * (‖v‖ * ‖w‖) * K⁻¹ := by positivity
  have e4 : 2 ^ 29 / |r| * (‖v‖ * ‖w‖) * (K⁻¹ + A * B * K⁻¹ ^ 3) =
      2 ^ 29 * (1 / |r| * (‖v‖ * ‖w‖) * K⁻¹) + 2 ^ 29 * (1 / |r| * (‖v‖ * ‖w‖) * (A * B * K⁻¹ ^ 3)) := by
    ring
  have e5 : 2 ^ 19 / |r| * (‖v‖ * ‖w‖) * (A * B * K⁻¹ ^ 3) =
      2 ^ 19 * (1 / |r| * (‖v‖ * ‖w‖) * (A * B * K⁻¹ ^ 3)) := by ring
  have e6 : 22528 / |r| * (‖v‖ * ‖w‖) * K⁻¹ = 22528 * (1 / |r| * (‖v‖ * ‖w‖) * K⁻¹) := by ring
  rw [e4, e5, e6]
  nlinarith only [hp1, hp2]

/-- **The two-leaf factor of `Q₃`.** -/
theorem norm_Yq_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode}
    (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (h1 : absk l ≤ 2 * absk (l - a - b))
    (h2 : absk (l - a - b) ≤ 2 * absk l) (v w : V3) :
    ‖Yq s r τ l a b v w‖ ≤ 2 ^ 29 / |r| * (‖v‖ * ‖w‖) *
      ((absk (l - a - b))⁻¹ + absk a * absk b * (absk (l - a - b))⁻¹ ^ 3) := by
  by_cases hM : 4 * absk l ≤ absk (l - a) ∧ 4 * absk (l - a - b) ≤ absk (l - a)
  · exact Yq_high hs hr τ ha hb hj h1 h2 hM v w
  · refine (Yq_ord hs hr τ ha hb hj h1 h2 hM v w).trans ?_
    have hr0 : 0 < |r| := abs_pos.2 hr
    have hV : 0 ≤ ‖v‖ * ‖w‖ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h0 := absk_nonneg a
    have h3 := absk_nonneg b
    have h4 := inv_nonneg.2 (absk_nonneg (l - a - b))
    have : 0 ≤ absk a * absk b * (absk (l - a - b))⁻¹ ^ 3 := by positivity
    linarith

end OVNS.Quant.Metric

end
