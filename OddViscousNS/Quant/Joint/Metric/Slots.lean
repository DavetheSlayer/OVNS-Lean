import OddViscousNS.Quant.Joint.Metric.Leaf
import OddViscousNS.Quant.Joint.Metric.Ordinary

/-!
# The kernels of the two sources and of `Z`, at both weights (step J5, nodes N13, N5)

The block bounds the energy identity needs on the leaf vectors: `‖tR‖ ≲ (M/q) f g Br`,
`‖zR‖ ≲ (P/q) f g (L²/J² + J²/L²)`, `‖Zb‖ ≲ (P/Σ) (1/q) f g (L²/J² + J²/L²)`, at `s = 1, 2`, and the
ratios of the two prefactors `M/Σ`, `P/Σ` against the four lengths.
-/

open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-- `X₁ 𝓛 + 𝓛* X₁` at weight two, on the leaf vectors (inside of `norm_X2b_two_le`). -/
theorem norm_tR_two_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) (v w : V3) :
    ‖tR 2 r τ l a b v w‖ ≤ 704 / |r| * absk (l - a) * (‖v‖ * ‖w‖) *
      Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hm2 : (l - a) 2 ≠ 0 := fun h => hj (by simp only [Pi.sub_apply] at h ⊢; simpa [hb] using h)
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absSq l := by linarith [one_le_absSq hl0]
  have hM : 0 < absSq (l - a) := by linarith [one_le_absSq hm0]
  have hJ : 0 < absSq (l - a - b) := by linarith [one_le_absSq hj0]
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  have h1 := norm_X1b_two_le hr τ e1 ha hm2 v
  have h2 := norm_Lb_le 2 τ e2 w
  have h3 := norm_Lad_le 2 τ e1 v
  have h4 := norm_X1b_two_le hr τ e2 hb hj w
  rw [wt_two] at h2 h3
  set L := absSq l
  set M := absSq (l - a)
  set J := absSq (l - a - b)
  set M₁ := absk (l - a) with hM₁
  have hM₁0 : 0 ≤ M₁ := absk_nonneg _
  have hv := norm_nonneg v
  have hw := norm_nonneg w
  have ht1 : ‖X1b 2 r τ a l (l - a) v ∘L Lb 2 τ b (l - a) (l - a - b) w‖ ≤
      44 / |r| * ‖v‖ * (L / M + M / L) * (16 * (M / J) * M₁ * ‖w‖) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
  have ht2 : ‖Lad 2 τ a l (l - a) v ∘L X1b 2 r τ b (l - a) (l - a - b) w‖ ≤
      16 * (M / L) * M₁ * ‖v‖ * (44 / |r| * ‖w‖ * (M / J + J / M)) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul h3 h4 (norm_nonneg _) (by positivity))
  refine (norm_add_le _ _).trans ((add_le_add ht1 ht2).trans (le_of_eq ?_))
  simp only [Br]
  field_simp
  ring

/-- `X₁ 𝓛 + 𝓛* X₁` at weight one, on the leaf vectors. -/
theorem norm_tR_one_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) (v w : V3) :
    ‖tR 1 r τ l a b v w‖ ≤ 320 / |r| * absk (l - a) * (‖v‖ * ‖w‖) *
      Br₁ (absk l) (absk (l - a)) (absk (l - a - b)) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hm2 : (l - a) 2 ≠ 0 := fun h => hj (by simp only [Pi.sub_apply] at h ⊢; simpa [hb] using h)
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hJ : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  have h1 := norm_X1b_one_le hr τ e1 ha hm2 v
  have h2 := norm_Lb_le 1 τ e2 w
  have h3 := norm_Lad_le 1 τ e1 v
  have h4 := norm_X1b_one_le hr τ e2 hb hj w
  simp only [wt, pow_one] at h2 h3
  set L := absk l
  set M := absk (l - a)
  set J := absk (l - a - b)
  have hv := norm_nonneg v
  have hw := norm_nonneg w
  have ht1 : ‖X1b 1 r τ a l (l - a) v ∘L Lb 1 τ b (l - a) (l - a - b) w‖ ≤
      20 / |r| * ‖v‖ * (L / M + M / L) * (16 * (M / J) * M * ‖w‖) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
  have ht2 : ‖Lad 1 τ a l (l - a) v ∘L X1b 1 r τ b (l - a) (l - a - b) w‖ ≤
      16 * (M / L) * M * ‖v‖ * (20 / |r| * ‖w‖ * (M / J + J / M)) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul h3 h4 (norm_nonneg _) (by positivity))
  refine (norm_add_le _ _).trans ((add_le_add ht1 ht2).trans (le_of_eq ?_))
  simp only [Br₁]
  field_simp
  ring

/-- The two rootings separately, at weight two. -/
theorem parts_two_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) (v w : V3) :
    ‖X1b 2 r τ a l (l - a) v ∘L Lb 2 τ b (l - a) (l - a - b) w‖ ≤ 704 / |r| * absk (l - a) *
        (‖v‖ * ‖w‖) * Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) ∧
      ‖Lad 2 τ a l (l - a) v ∘L X1b 2 r τ b (l - a) (l - a - b) w‖ ≤ 704 / |r| * absk (l - a) *
        (‖v‖ * ‖w‖) * Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hm2 : (l - a) 2 ≠ 0 := fun h => hj (by simp only [Pi.sub_apply] at h ⊢; simpa [hb] using h)
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absSq l := by linarith [one_le_absSq hl0]
  have hM : 0 < absSq (l - a) := by linarith [one_le_absSq hm0]
  have hJ : 0 < absSq (l - a - b) := by linarith [one_le_absSq hj0]
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  have h1 := norm_X1b_two_le hr τ e1 ha hm2 v
  have h2 := norm_Lb_le 2 τ e2 w
  have h3 := norm_Lad_le 2 τ e1 v
  have h4 := norm_X1b_two_le hr τ e2 hb hj w
  rw [wt_two] at h2 h3
  set L := absSq l
  set M := absSq (l - a)
  set J := absSq (l - a - b)
  set M₁ := absk (l - a) with hM₁
  have hM₁0 : 0 ≤ M₁ := absk_nonneg _
  have hv := norm_nonneg v
  have hw := norm_nonneg w
  have hK : 0 ≤ 704 / |r| * M₁ * (‖v‖ * ‖w‖) := by positivity
  have hr1 : 0 ≤ L / J := by positivity
  have hr2 : 0 ≤ J / L := by positivity
  have hr3 : 0 ≤ M ^ 2 / (L * J) := by positivity
  have eBr : Br L M J = L / J + 2 * (M ^ 2 / (L * J)) + J / L := by
    simp only [Br]
    ring
  constructor
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans ?_)
    have e : 44 / |r| * ‖v‖ * (L / M + M / L) * (16 * (M / J) * M₁ * ‖w‖) =
        704 / |r| * M₁ * (‖v‖ * ‖w‖) * (L / J + M ^ 2 / (L * J)) := by
      field_simp
      ring
    rw [e, eBr]
    refine mul_le_mul_of_nonneg_left ?_ hK
    linarith
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul h3 h4 (norm_nonneg _) (by positivity)).trans ?_)
    have e : 16 * (M / L) * M₁ * ‖v‖ * (44 / |r| * ‖w‖ * (M / J + J / M)) =
        704 / |r| * M₁ * (‖v‖ * ‖w‖) * (M ^ 2 / (L * J) + J / L) := by
      field_simp
      ring
    rw [e, eBr]
    refine mul_le_mul_of_nonneg_left ?_ hK
    linarith

/-- The two rootings separately, at weight one. -/
theorem parts_one_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) (v w : V3) :
    ‖X1b 1 r τ a l (l - a) v ∘L Lb 1 τ b (l - a) (l - a - b) w‖ ≤ 320 / |r| * absk (l - a) *
        (‖v‖ * ‖w‖) * Br₁ (absk l) (absk (l - a)) (absk (l - a - b)) ∧
      ‖Lad 1 τ a l (l - a) v ∘L X1b 1 r τ b (l - a) (l - a - b) w‖ ≤ 320 / |r| * absk (l - a) *
        (‖v‖ * ‖w‖) * Br₁ (absk l) (absk (l - a)) (absk (l - a - b)) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hm2 : (l - a) 2 ≠ 0 := fun h => hj (by simp only [Pi.sub_apply] at h ⊢; simpa [hb] using h)
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hJ : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  have h1 := norm_X1b_one_le hr τ e1 ha hm2 v
  have h2 := norm_Lb_le 1 τ e2 w
  have h3 := norm_Lad_le 1 τ e1 v
  have h4 := norm_X1b_one_le hr τ e2 hb hj w
  simp only [wt, pow_one] at h2 h3
  set L := absk l
  set M := absk (l - a)
  set J := absk (l - a - b)
  have hv := norm_nonneg v
  have hw := norm_nonneg w
  have hK : 0 ≤ 320 / |r| * M * (‖v‖ * ‖w‖) := by positivity
  have hr1 : 0 ≤ L / J := by positivity
  have hr2 : 0 ≤ J / L := by positivity
  have hr3 : 0 ≤ M ^ 2 / (L * J) := by positivity
  have eBr : Br₁ L M J = L / J + 2 * (M ^ 2 / (L * J)) + J / L := by
    simp only [Br₁]
    ring
  constructor
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans ?_)
    have e : 20 / |r| * ‖v‖ * (L / M + M / L) * (16 * (M / J) * M * ‖w‖) =
        320 / |r| * M * (‖v‖ * ‖w‖) * (L / J + M ^ 2 / (L * J)) := by
      field_simp
      ring
    rw [e, eBr]
    refine mul_le_mul_of_nonneg_left ?_ hK
    linarith
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul h3 h4 (norm_nonneg _) (by positivity)).trans ?_)
    have e : 16 * (M / L) * M * ‖v‖ * (20 / |r| * ‖w‖ * (M / J + J / M)) =
        320 / |r| * M * (‖v‖ * ‖w‖) * (M ^ 2 / (L * J) + J / L) := by
      field_simp
      ring
    rw [e, eBr]
    refine mul_le_mul_of_nonneg_left ?_ hK
    linarith

/-- **The two rootings separately, at both weights.** -/
theorem parts_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode}
    (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (v w : V3) :
    ‖X1b s r τ a l (l - a) v ∘L Lb s τ b (l - a) (l - a - b) w‖ ≤ 704 / |r| * absk (l - a) *
        (‖v‖ * ‖w‖) * Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) ∧
      ‖Lad s τ a l (l - a) v ∘L X1b s r τ b (l - a) (l - a - b) w‖ ≤ 704 / |r| * absk (l - a) *
        (‖v‖ * ‖w‖) * Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) := by
  rcases hs with rfl | rfl
  · obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
    have hr0 : 0 < |r| := abs_pos.2 hr
    have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
    have hJ : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
    have h1 := Br₁_le (M := absk (l - a)) hL hJ
    simp only [absk_sq] at h1
    have hB : 0 ≤ Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) := by
      have := absSq_nonneg l
      have := absSq_nonneg (l - a)
      have := absSq_nonneg (l - a - b)
      simp only [Br]
      positivity
    have hm := absk_nonneg (l - a)
    have hK : 0 ≤ 1 / |r| * absk (l - a) * (‖v‖ * ‖w‖) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 320) hK)
    have h3 := mul_nonneg hK hB
    have key : 320 / |r| * absk (l - a) * (‖v‖ * ‖w‖) *
        Br₁ (absk l) (absk (l - a)) (absk (l - a - b)) ≤ 704 / |r| * absk (l - a) * (‖v‖ * ‖w‖) *
          Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) := by
      calc _ = 320 * (1 / |r| * absk (l - a) * (‖v‖ * ‖w‖)) *
            Br₁ (absk l) (absk (l - a)) (absk (l - a - b)) := by ring
        _ ≤ _ := h2
        _ ≤ 704 * (1 / |r| * absk (l - a) * (‖v‖ * ‖w‖) *
            Br (absSq l) (absSq (l - a)) (absSq (l - a - b))) := by linarith
        _ = _ := by ring
    obtain ⟨p1, p2⟩ := parts_one_le hr τ ha hb hj v w
    exact ⟨p1.trans key, p2.trans key⟩
  · exact parts_two_le hr τ ha hb hj v w

/-- **The source of `X₂` at both weights**, with the bracket of weight two. -/
theorem norm_tR_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode}
    (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (v w : V3) :
    ‖tR s r τ l a b v w‖ ≤ 704 / |r| * absk (l - a) * (‖v‖ * ‖w‖) *
      Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) := by
  rcases hs with rfl | rfl
  · obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
    have hr0 : 0 < |r| := abs_pos.2 hr
    have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
    have hJ : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
    have h1 := Br₁_le (M := absk (l - a)) hL hJ
    simp only [absk_sq] at h1
    have hB : 0 ≤ Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) := by
      have := absSq_nonneg l
      have := absSq_nonneg (l - a)
      have := absSq_nonneg (l - a - b)
      simp only [Br]
      positivity
    have hm := absk_nonneg (l - a)
    have hK : 0 ≤ 1 / |r| * absk (l - a) * (‖v‖ * ‖w‖) := by positivity
    refine (norm_tR_one_le hr τ ha hb hj v w).trans ?_
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 320) hK)
    have h3 := mul_nonneg hK hB
    calc _ = 320 * (1 / |r| * absk (l - a) * (‖v‖ * ‖w‖)) *
          Br₁ (absk l) (absk (l - a)) (absk (l - a - b)) := by ring
      _ ≤ _ := h2
      _ ≤ 704 * (1 / |r| * absk (l - a) * (‖v‖ * ‖w‖) *
          Br (absSq l) (absSq (l - a)) (absSq (l - a - b))) := by linarith
      _ = _ := by ring
  · exact norm_tR_two_le hr τ ha hb hj v w

/-- `R + R⁻¹ ≤ R² + R⁻²`, on the two lengths. -/
private lemma ratio_le_sq {L J : ℝ} (hL : 0 < L) (hJ : 0 < J) :
    L / J + J / L ≤ L ^ 2 / J ^ 2 + J ^ 2 / L ^ 2 := by
  set R := L / J with hR
  have hR0 : 0 < R := by positivity
  have e1 : J / L = R⁻¹ := by simp only [hR, inv_div]
  have e2 : L ^ 2 / J ^ 2 = R ^ 2 := by simp only [hR, div_pow]
  have e3 : J ^ 2 / L ^ 2 = (R⁻¹) ^ 2 := by simp only [hR, inv_div, div_pow]
  rw [e1, e2, e3]
  have h1 : R * R⁻¹ = 1 := mul_inv_cancel₀ hR0.ne'
  have h2 : 0 < R⁻¹ := inv_pos.2 hR0
  nlinarith [sq_nonneg (R - R⁻¹), sq_nonneg (R - 1), sq_nonneg (R⁻¹ - 1), sq_nonneg (R + R⁻¹ - 2)]

/-- **The source of `Z` at both weights.** -/
theorem norm_zR_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode}
    (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (v w : V3) :
    ‖zR s r τ l a b v w‖ ≤ 352 / |r| * absk (a + b) * (‖v‖ * ‖w‖) *
      (absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l) := by
  obtain ⟨hl0, -, hj0⟩ := fast_labels ha hb hj
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hJ : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have e1 : (a + b) + (l - a - b) = l := by abel
  have hab : (a + b) 2 = 0 := by simp [ha, hb]
  have h2 := norm_slowV_le a b v w
  have hP := absk_nonneg (a + b)
  have hv := norm_nonneg v
  have hw := norm_nonneg w
  set R := absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l with hR
  have hR0 : 0 ≤ R := by
    have := absSq_nonneg l
    have := absSq_nonneg (l - a - b)
    positivity
  rcases hs with rfl | rfl
  · have h1 := norm_X1b_one_le hr τ e1 hab hj (slowV a b v w)
    have hq := ratio_le_sq hL hJ
    simp only [absk_sq] at hq
    calc ‖zR 1 r τ l a b v w‖
        ≤ 20 / |r| * ‖slowV a b v w‖ * (absk l / absk (l - a - b) + absk (l - a - b) / absk l) := h1
      _ ≤ 44 / |r| * (8 * absk (a + b) * ‖v‖ * ‖w‖) * R := by
          have h3 : 20 / |r| ≤ 44 / |r| := by gcongr; norm_num
          exact mul_le_mul (mul_le_mul h3 h2 (norm_nonneg _) (by positivity)) hq (by positivity)
            (by positivity)
      _ = _ := by ring
  · have h1 := norm_X1b_two_le hr τ e1 hab hj (slowV a b v w)
    calc ‖zR 2 r τ l a b v w‖ ≤ 44 / |r| * ‖slowV a b v w‖ * R := h1
      _ ≤ 44 / |r| * (8 * absk (a + b) * ‖v‖ * ‖w‖) * R := by gcongr
      _ = _ := by ring

/-- **`Z` at both weights** (Body 12 §8; `norm_Zb_two_le` at `s = 2`). -/
theorem norm_Zb_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field)
    {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖Zb s r τ f g l a b‖ ≤ 1408 / |r| * (absk (a + b) / heat4 l (l - a - b) a b) *
      (‖f a‖ * ‖g b‖) * (absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l) := by
  obtain ⟨-, -, hj0⟩ := fast_labels ha hb hj
  have hH := heat4_pos (l := l) hj0 a b
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hP := absk_nonneg (a + b)
  calc ‖Zb s r τ f g l a b‖ ≤ 4 / heat4 l (l - a - b) a b * ‖zR s r τ l a b (f a) (g b)‖ :=
        norm_outerInv_le hH r l _ _
    _ ≤ 4 / heat4 l (l - a - b) a b * (352 / |r| * absk (a + b) * (‖f a‖ * ‖g b‖) *
          (absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l)) :=
        mul_le_mul_of_nonneg_left (norm_zR_le hs hr τ ha hb hj _ _) (by positivity)
    _ = _ := by ring

/-! ### The prefactors against the four lengths -/

/-- The bracket of the merged block against the bracket of `X₂`. -/
lemma ratio_le_Br (L M J : ℝ) (hL : 0 ≤ L) (hJ : 0 ≤ J) :
    L / J + J / L ≤ Br L M J := by
  have : 0 ≤ 2 * M ^ 2 / (L * J) := by positivity
  simp only [Br]
  linarith

/-- The ratio of `Z`: `P L ≤ Σ`. -/
lemma merged_left_le (l a b : Mode) (j : Mode) :
    absk l * absk (a + b) ≤ heat4 l j a b := by
  have h1 := absk_mul_absk_le l (a + b)
  have h2 := absSq_le₂ (k := a + b) rfl
  have h3 := absSq_nonneg j
  have h5 := absSq_nonneg l
  unfold heat4
  linarith

/-- The ratio of `Z` against a leaf. -/
lemma merged_leaf_le (l j a b : Mode) :
    absk a * absk (a + b) ≤ 2 * heat4 l j a b ∧ absk b * absk (a + b) ≤ 2 * heat4 l j a b := by
  have h1 := absk_mul_absk_le a (a + b)
  have h1' := absk_mul_absk_le b (a + b)
  have h2 := absSq_le₂ (k := a + b) rfl
  have h3 := absSq_nonneg j
  have h4 := absSq_nonneg l
  have h5 := absSq_nonneg a
  have h6 := absSq_nonneg b
  unfold heat4
  constructor <;> linarith

/-- `P/Σ ≤ 2`. -/
lemma merged_le_two {l a b : Mode} (hj : l - a - b ≠ 0) :
    absk (a + b) / heat4 l (l - a - b) a b ≤ 2 := by
  have hH := heat4_pos (l := l) hj a b
  rw [div_le_iff₀ hH]
  have h1 := merged_ratio_le l a b
  have h2 := one_le_absk hj
  have h3 := absk_nonneg (a + b)
  nlinarith only [h1, h2, h3, hH]

end OVNS.Quant.Metric

end
