import OddViscousNS.Quant.Joint.Metric.PathMain
import OddViscousNS.Quant.Joint.Metric.Whole

/-!
# `X₂` and `Z` on the actual path (step J5, node N13)

The two instances of `Fam`: `famX2`, `famZ`, at both weights, with `Fam.Bd`.  So
`X2_identity`, `Z_identity`: along the actual solution, at `s = 1, 2`,
`⟨z, X₂ z⟩' = ⟨z, (X₁𝓛 + 𝓛*X₁) z⟩ + ⟨N_z, X₂ z⟩ + ⟨z, X₂ N_z⟩ + ⟨z, D_S X₂[N_S] z⟩`,
`⟨z, Z z⟩' = ⟨z, X₁(B) z⟩ + ⟨N_z, Z z⟩ + ⟨z, Z N_z⟩ + ⟨z, D_S Z[N_S] z⟩`, integrated, with integrands
in `L¹`.  The heat of the four vectors and the phase have been used up: this is the homological
equation of LOCAL83 with moving amplitudes, "no time derivative of a cutoff or a cap".
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

lemma Hx_nonneg (x : I3) : 0 ≤ Hx x := by
  have h1 := absSq_nonneg x.1
  have h2 := absSq_nonneg (inJ₂ x)
  have h3 := absSq_nonneg x.2.1
  have h4 := absSq_nonneg x.2.2
  unfold Hx heat4
  linarith

/-- `X₂` as a family: the source is `X₁𝓛 + 𝓛*X₁`. -/
def famX2 (s : ℕ) (r : ℝ) : Fam where
  Sr x τ v w := tR s r τ x.1 x.2.1 x.2.2 v w
  Sr0 x := bilCLM (tR_isBil s r 0 x.1 x.2.1 x.2.2)
  cov x ha hb τ v w c e y := by
    have h := twoRoot_chan s r 0 τ (fun _ => v) (fun _ => w) (l := x.1) ha hb c e y
    rw [zero_add] at h
    exact h
  zero_l x τ w := by
    simp [tR, X1b_zero_leaf, Lad_zero_leaf]
  zero_r x τ v := by
    simp [tR, X1b_zero_leaf, Lb_zero_leaf]

/-- `Z` as a family: the source is `X₁(B)`. -/
def famZ (s : ℕ) (r : ℝ) : Fam where
  Sr x τ v w := zR s r τ x.1 x.2.1 x.2.2 v w
  Sr0 x := bilCLM (zR_isBil s r 0 x.1 x.2.1 x.2.2)
  cov x ha hb τ v w c e y := by
    have h := X1Z_chan s r 0 τ (fun _ => v) (fun _ => w) (l := x.1) ha hb c e y
    rw [zero_add] at h
    exact h
  zero_l x τ w := by
    simp [zR, slowV_eq_zero, X1b_zero_leaf]
  zero_r x τ v := by
    simp [zR, slowV_eq_zero, X1b_zero_leaf]

/-- The two-leaf kernel at both weights. -/
theorem norm_X2b_E2_both {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field)
    {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖X2b s r τ f g l a b‖ ≤ 39424 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) *
      (‖f a‖ * ‖g b‖) * E2 (l, a, b) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hL : 0 < absSq l := by linarith [one_le_absSq hl0]
  have hJ : 0 < absSq (l - a - b) := by linarith [one_le_absSq hj0]
  obtain ⟨t1, t2, t3, t4⟩ := two_leaf_triangles l a b
  have hBr := bracket₂_le hL hJ (absSq_nonneg (l - a)) (absSq_nonneg a) (absSq_nonneg b) t1 t2 t3 t4
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hH := heat4_pos (l := l) hj0 a b
  have hM := absk_nonneg (l - a)
  have hfg : 0 ≤ ‖f a‖ * ‖g b‖ := by positivity
  refine (norm_X2b_le hs hr τ f g ha hb hj).trans ?_
  simp only [absk_sq]
  calc 2816 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) * (‖f a‖ * ‖g b‖) *
        Br (absSq l) (absSq (l - a)) (absSq (l - a - b))
      ≤ 2816 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) * (‖f a‖ * ‖g b‖) *
        (14 * E2 (l, a, b)) := mul_le_mul_of_nonneg_left hBr (by positivity)
    _ = _ := by ring

/-- The bracket of weight two against `E₂`, on a block. -/
lemma Br_le_E2 {l a b : Mode} (hl : l ≠ 0) (hj : l - a - b ≠ 0) :
    Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) ≤ 14 * E2 (l, a, b) := by
  have hL : 0 < absSq l := by linarith [one_le_absSq hl]
  have hJ : 0 < absSq (l - a - b) := by linarith [one_le_absSq hj]
  obtain ⟨t1, t2, t3, t4⟩ := two_leaf_triangles l a b
  exact bracket₂_le hL hJ (absSq_nonneg (l - a)) (absSq_nonneg a) (absSq_nonneg b) t1 t2 t3 t4

/-- The analysis of `X₂`. -/
theorem famX2_bd {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) :
    (famX2 s r).Bd r (fun x => absk (x.1 - x.2.1) / Hx x) (39424 / |r|) (9856 / |r|) where
  K₁0 := by positivity
  K₂0 := by positivity
  ρ0 x := div_nonneg (absk_nonneg _) (Hx_nonneg x)
  ρ2 x hx := by
    obtain ⟨-, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    exact (chain_le_one hj0).trans (by norm_num)
  ρl x _ := half_ratio_le x.1 x.2.1 x.2.2
  ρj x hx := by
    obtain ⟨-, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    have h1 := chain_ratio_le (l := x.1) (a := x.2.1) (b := x.2.2) hj0
    have hH : 0 < Hx x := heat4_pos hj0 _ _
    have h2 : absk (inJ₂ x) * (absk (x.1 - x.2.1) / Hx x) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hH, mul_comm]
      exact h1
    linarith
  ρa x hx := by
    obtain ⟨-, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    exact (leaf_ratio_left_le hj0).trans (by norm_num)
  ρb x hx := by
    obtain ⟨-, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    exact (leaf_ratio_right_le hj0).trans (by norm_num)
  op x hx τ v w := norm_X2b_E2_both hs hr τ (fun _ => v) (fun _ => w) hx.1 hx.2.1 hx.2.2
  source x hx τ v w := by
    obtain ⟨hl0, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    have h1 := norm_tR_le hs hr τ hx.1 hx.2.1 hx.2.2 v w
    have hB := Br_le_E2 (a := x.2.1) (b := x.2.2) hl0 hj0
    have hr0 : 0 < |r| := abs_pos.2 hr
    have hv := norm_nonneg v
    have hw := norm_nonneg w
    have hE := E2_nonneg x
    have hM : absk (x.1 - x.2.1) ≤ absk x.1 + absk x.2.1 + absk x.2.2 := by
      have h2 := absk_sub_le x.1 x.2.1
      have := absk_nonneg x.2.2
      linarith
    have hM0 := absk_nonneg (x.1 - x.2.1)
    calc _ ≤ 704 / |r| * absk (x.1 - x.2.1) * (‖v‖ * ‖w‖) *
          Br (absSq x.1) (absSq (x.1 - x.2.1)) (absSq (x.1 - x.2.1 - x.2.2)) := h1
      _ ≤ 704 / |r| * absk (x.1 - x.2.1) * (‖v‖ * ‖w‖) * (14 * E2 x) := by gcongr
      _ = 9856 / |r| * absk (x.1 - x.2.1) * (‖v‖ * ‖w‖) * E2 x := by ring
      _ ≤ _ := by gcongr

/-- The analysis of `Z`. -/
theorem famZ_bd {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) :
    (famZ s r).Bd r (fun x => absk (x.2.1 + x.2.2) / Hx x) (19712 / |r|) (4928 / |r|) where
  K₁0 := by positivity
  K₂0 := by positivity
  ρ0 x := div_nonneg (absk_nonneg _) (Hx_nonneg x)
  ρ2 x hx := by
    obtain ⟨-, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    exact merged_le_two hj0
  ρl x hx := by
    obtain ⟨-, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    have hH : 0 < Hx x := heat4_pos hj0 _ _
    have h2 : absk x.1 * (absk (x.2.1 + x.2.2) / Hx x) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hH]
      exact merged_left_le _ _ _ _
    linarith
  ρj x hx := by
    obtain ⟨-, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    have hH : 0 < Hx x := heat4_pos hj0 _ _
    have h2 : absk (inJ₂ x) * (absk (x.2.1 + x.2.2) / Hx x) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hH, mul_comm]
      exact merged_ratio_le _ _ _
    linarith
  ρa x hx := by
    obtain ⟨-, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    have hH : 0 < Hx x := heat4_pos hj0 _ _
    rw [← mul_div_assoc, div_le_iff₀ hH]
    exact (merged_leaf_le _ _ _ _).1
  ρb x hx := by
    obtain ⟨-, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    have hH : 0 < Hx x := heat4_pos hj0 _ _
    rw [← mul_div_assoc, div_le_iff₀ hH]
    exact (merged_leaf_le _ _ _ _).2
  op x hx τ v w := by
    obtain ⟨hl0, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    have h1 := norm_Zb_le hs hr τ (fun _ => v) (fun _ => w) hx.1 hx.2.1 hx.2.2
    beta_reduce at h1
    have hB := Br_le_E2 (a := x.2.1) (b := x.2.2) hl0 hj0
    have hr' := ratio_le_Br (absSq x.1) (absSq (x.1 - x.2.1)) (absSq (x.1 - x.2.1 - x.2.2))
      (absSq_nonneg _) (absSq_nonneg _)
    have hr0 : 0 < |r| := abs_pos.2 hr
    have hH : 0 < Hx x := heat4_pos hj0 _ _
    have hP := absk_nonneg (x.2.1 + x.2.2)
    have hv := norm_nonneg v
    have hw := norm_nonneg w
    refine h1.trans ?_
    calc _ ≤ 1408 / |r| * (absk (x.2.1 + x.2.2) / Hx x) * (‖v‖ * ‖w‖) * (14 * E2 x) := by
          refine mul_le_mul_of_nonneg_left (hr'.trans hB) ?_
          have h3 : 0 ≤ absk (x.2.1 + x.2.2) / Hx x := div_nonneg hP (Hx_nonneg x)
          exact mul_nonneg (mul_nonneg (by positivity) h3) (by positivity)
      _ = _ := by ring
  source x hx τ v w := by
    obtain ⟨hl0, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
    have h1 := norm_zR_le hs hr τ hx.1 hx.2.1 hx.2.2 v w
    have hB := Br_le_E2 (a := x.2.1) (b := x.2.2) hl0 hj0
    have hr' := ratio_le_Br (absSq x.1) (absSq (x.1 - x.2.1)) (absSq (x.1 - x.2.1 - x.2.2))
      (absSq_nonneg _) (absSq_nonneg _)
    have hr0 : 0 < |r| := abs_pos.2 hr
    have hv := norm_nonneg v
    have hw := norm_nonneg w
    have hE := E2_nonneg x
    have hP0 := absk_nonneg (x.2.1 + x.2.2)
    have hP : absk (x.2.1 + x.2.2) ≤ absk x.1 + absk x.2.1 + absk x.2.2 := by
      have h2 := absk_add_le x.2.1 x.2.2
      have := absk_nonneg x.1
      linarith
    calc _ ≤ 352 / |r| * absk (x.2.1 + x.2.2) * (‖v‖ * ‖w‖) *
          (absSq x.1 / absSq (x.1 - x.2.1 - x.2.2) + absSq (x.1 - x.2.1 - x.2.2) / absSq x.1) := h1
      _ ≤ 352 / |r| * absk (x.2.1 + x.2.2) * (‖v‖ * ‖w‖) * (14 * E2 x) := by
          refine mul_le_mul_of_nonneg_left (hr'.trans hB) ?_
          positivity
      _ = 4928 / |r| * absk (x.2.1 + x.2.2) * (‖v‖ * ‖w‖) * E2 x := by ring
      _ ≤ _ := by gcongr

/-- `(famX2 s r).form` is `X2Form 1`. -/
lemma famX2_form (s : ℕ) (r τ : ℝ) (f g G F : Field) :
    (famX2 s r).form r τ f g G F = X2Form 1 s r τ f g G F := by
  unfold Fam.form X2Form
  refine tsum_congr fun x => ?_
  rw [Pi.one_apply, one_mul]
  dsimp only [Fam.T, oTerm, X2b, Hx, inJ₂, famX2, twoRoot, tR]

/-- `(famZ s r).form` is `ZForm 1`. -/
lemma famZ_form (s : ℕ) (r τ : ℝ) (f g G F : Field) :
    (famZ s r).form r τ f g G F = ZForm 1 s r τ f g G F := by
  unfold Fam.form ZForm
  refine tsum_congr fun x => ?_
  rw [Pi.one_apply, one_mul]
  dsimp only [Fam.T, oTerm, Zb, Hx, inJ₂, famZ, zR]

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- **`X₂` on the actual path**, at both weights. -/
theorem X2_identity {s : ℕ} (hs : s = 1 ∨ s = 2) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable ((famX2 s r).rhs s r g y) volume a b ∧
      (famX2 s r).val s r g y b - (famX2 s r).val s r g y a =
        ∫ u in a..b, (famX2 s r).rhs s r g y u :=
  Fam.identity (famX2_bd hs hr) hs h hr ha hab hb

/-- **`Z` on the actual path**, at both weights. -/
theorem Z_identity {s : ℕ} (hs : s = 1 ∨ s = 2) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable ((famZ s r).rhs s r g y) volume a b ∧
      (famZ s r).val s r g y b - (famZ s r).val s r g y a =
        ∫ u in a..b, (famZ s r).rhs s r g y u :=
  Fam.identity (famZ_bd hs hr) hs h hr ha hab hb

end OVNS.Quant.Metric

end
