import OddViscousNS.Quant.Joint.Metric.Q3Sep

/-!
# The third correction: the forms (step J5, node N8)

With `O` the directed operator of `famQ`:
* `Q3_half_left`, `Q3_half_right`, `Q3_static`: `‖A^{1/2} O‖, ‖O A^{1/2}‖, ‖O‖ ≲ q⁻² (W³ + W² b)`.

`Q3_half_left` with `G = A^{1/2} N` is Body 33's `Re⟨Q₃ z, A N⟩`.  It also pays the quartic: on the
actual path the fast insertion is the whole `fastNL ∈ H¹`, and `‖𝓛F‖₁ ≲ (W + b) b_F` gives Body 33's
`q⁻² W² b²`, so the two orientations of LOCAL466 are not needed.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {s : ℕ} {r τ D : ℝ} {x : I4} {G F t v w : V3}

/-- One term of `O`, with the output weight. -/
lemma T_half (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (hx : Act₃ x) :
    absk x.1 * ‖(famQ s r D).T r x G F t v w τ‖ ≤
      2 ^ 37 / |r| ^ 2 * (‖G‖ * ‖F‖ * (‖t‖ * ‖v‖ * ‖w‖)) * Esep x := by
  have hb := norm_O_le (D := D) hs hr τ hx t v w
  have h1 := norm_inner_apply_le G F (outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ t v w))
  have hL := absk_nonneg x.1
  have hP : 0 ≤ ‖G‖ * ‖F‖ := by positivity
  calc absk x.1 * ‖(famQ s r D).T r x G F t v w τ‖
      ≤ absk x.1 * (‖G‖ * ‖F‖ *
        ‖outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ t v w)‖) :=
        mul_le_mul_of_nonneg_left h1 hL
    _ = ‖G‖ * ‖F‖ * (absk x.1 * ‖outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ t v w)‖) := by
        ring
    _ ≤ ‖G‖ * ‖F‖ * (2 ^ 37 / |r| ^ 2 * (‖t‖ * ‖v‖ * ‖w‖) * Esep x) :=
        mul_le_mul_of_nonneg_left hb hP
    _ = _ := by ring

lemma act_l {x : I4} (hx : Act₃ x) : x.1 ≠ 0 := by
  obtain ⟨ha, hb, hc, hj⟩ := hx
  have hk2 : (x.1 - x.2.1 - x.2.2.1) 2 ≠ 0 := by
    have e : (x.1 - x.2.1 - x.2.2.1) 2 = inJ x 2 := by
      simp [inJ, hc]
    rwa [e]
  exact (fast_labels ha hb hk2).1

/-- A form with a majorant of `Phi₃ * Esep`. -/
lemma sep_form {f g h G₀ F₀ : Field} (hr : r ≠ 0) (hf : MZ 2 f)
    (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g) (hh : MZ 2 h) (hh' : PiS h = h)
    (hG : Summable fun k => ‖G₀ k‖ ^ 2) (hF : Summable fun k => ‖F₀ k‖ ^ 2) {G₁ F₁ : Field}
    (hF₁ : PiF F₁ = F₁)
    (hb : ∀ x, Act₃ x → ‖(famQ s r D).T r x (G₁ x.1) (F₁ (inJ x)) (f x.2.1) (g x.2.2.1)
      (h x.2.2.2) τ‖ ≤ 2 ^ 37 / |r| ^ 2 * (Phi₃ (nrm G₀) (nrm F₀) (nrm f) (nrm g) (nrm h) x * Esep x)) :
    ‖(famQ s r D).form r τ f g h G₁ F₁‖ ≤ 2 ^ 37 / |r| ^ 2 * (l2n G₀ * l2n F₀ *
      clsS (wiener f) (wiener g) (wiener h) (hnorm 2 f) (hnorm 2 g) (hnorm 2 h)) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hP := (pos3_sep (l2B_nrm hG) (l2B_nrm hF) (l1B_nrm hf.inH) (l1B_nrm hg.inH) (l1B_nrm hh.inH)
    (l2B_up hf.inH) (l2B_up hg.inH) (l2B_up hh.inH)).const_mul
    (by positivity : 0 ≤ 2 ^ 37 / |r| ^ 2)
  refine (form_le hP fun x => ?_).2
  refine Fam3.T_form_le hf' hg' hh' hF₁ (B := fun x => 2 ^ 37 / |r| ^ 2 *
    (Phi₃ (nrm G₀) (nrm F₀) (nrm f) (nrm g) (nrm h) x * Esep x)) (fun x => ?_) hb x
  have h1 := Phi₃_nonneg (α := nrm G₀) (β := nrm F₀) (f₁ := nrm f) (f₂ := nrm g) (f₃ := nrm h)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) x
  have h2 := Esep_nonneg x
  positivity

variable {f g h : Field}

/-- **The output half of `O`.** -/
theorem Q3_half_left (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ D : ℝ) (hf : MZ 2 f) (hf' : PiS f = f)
    (hg : MZ 2 g) (hg' : PiS g = g) (hh : MZ 2 h) (hh' : PiS h = h) {G₀ F₀ : Field}
    (hG : Summable fun k => ‖G₀ k‖ ^ 2) (hF : Summable fun k => ‖F₀ k‖ ^ 2) (hF₀ : PiF F₀ = F₀) :
    ‖(famQ s r D).form r τ f g h (zOf 1 G₀) F₀‖ ≤ 2 ^ 37 / |r| ^ 2 * (l2n G₀ * l2n F₀ *
      clsS (wiener f) (wiener g) (wiener h) (hnorm 2 f) (hnorm 2 g) (hnorm 2 h)) := by
  refine sep_form hr hf hf' hg hg' hh hh' hG hF hF₀ fun x hx => ?_
  have hn : ‖zOf 1 G₀ x.1‖ = absk x.1 * ‖G₀ x.1‖ := by
    simp only [zOf, norm_smul, Complex.norm_real, pow_one, Real.norm_of_nonneg (absk_nonneg _)]
  have hL : 0 < absk x.1 := lt_of_lt_of_le one_pos (one_le_absk (act_l hx))
  have h0 := norm_O_le (D := D) hs hr τ hx (f x.2.1) (g x.2.2.1) (h x.2.2.2)
  have h1 := norm_inner_apply_le (zOf 1 G₀ x.1) (F₀ (inJ x))
    (outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1) (h x.2.2.2)))
  have hP : 0 ≤ ‖G₀ x.1‖ * ‖F₀ (inJ x)‖ := by positivity
  refine h1.trans ?_
  rw [hn]
  have e : absk x.1 * ‖G₀ x.1‖ * ‖F₀ (inJ x)‖ *
      ‖outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1) (h x.2.2.2))‖ =
      ‖G₀ x.1‖ * ‖F₀ (inJ x)‖ * (absk x.1 *
        ‖outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1) (h x.2.2.2))‖) := by
    ring
  rw [e]
  refine (mul_le_mul_of_nonneg_left h0 hP).trans (le_of_eq ?_)
  simp only [Phi₃, nrm]
  ring

/-- The block is zero off the mask. -/
lemma O_zero {s : ℕ} {r D τ : ℝ} {x : I4} (hm : muQ D x = 0) (t v w : V3) :
    (famQ s r D).Sr x τ t v w = 0 := by
  change ((muQ D x : ℝ) : ℂ) • _ = 0
  rw [hm]
  ext1 y
  simp only [smul_apply, zero_apply, Complex.ofReal_zero, zero_smul]

/-- **The input half of `O`.** -/
theorem Q3_half_right (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ D : ℝ) (hf : MZ 2 f) (hf' : PiS f = f)
    (hg : MZ 2 g) (hg' : PiS g = g) (hh : MZ 2 h) (hh' : PiS h = h) {G₀ F₀ : Field}
    (hG : Summable fun k => ‖G₀ k‖ ^ 2) (hF : Summable fun k => ‖F₀ k‖ ^ 2) (hF₀ : PiF F₀ = F₀) :
    ‖(famQ s r D).form r τ f g h G₀ (zOf 1 F₀)‖ ≤ 2 ^ 37 / |r| ^ 2 * (l2n G₀ * l2n F₀ *
      clsS (wiener f) (wiener g) (wiener h) (hnorm 2 f) (hnorm 2 g) (hnorm 2 h)) := by
  have hF1 : PiF (zOf 1 F₀) = zOf 1 F₀ := Fam.PiF_zOf hF₀
  refine sep_form hr hf hf' hg hg' hh hh' hG hF hF1 fun x hx => ?_
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hR : 0 ≤ 2 ^ 37 / |r| ^ 2 * (Phi₃ (nrm G₀) (nrm F₀) (nrm f) (nrm g) (nrm h) x * Esep x) := by
    have h1 := Phi₃_nonneg (α := nrm G₀) (β := nrm F₀) (f₁ := nrm f) (f₂ := nrm g) (f₃ := nrm h)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) x
    have h2 := Esep_nonneg x
    positivity
  by_cases hm : muQ D x = 0
  · have : (famQ s r D).T r x (G₀ x.1) (zOf 1 F₀ (inJ x)) (f x.2.1) (g x.2.2.1) (h x.2.2.2) τ = 0 := by
      simp only [Fam3.T]
      rw [O_zero hm, outerInv_zero]
      simp
    rw [this, norm_zero]
    exact hR
  have hQ := onQ_of_ne hm
  have hJL : absk (inJ x) ≤ absk x.1 := by
    have := hQ.lengths.2
    have := absk_nonneg (inJ x)
    linarith
  have hn : ‖zOf 1 F₀ (inJ x)‖ = absk (inJ x) * ‖F₀ (inJ x)‖ := by
    simp only [zOf, norm_smul, Complex.norm_real, pow_one, Real.norm_of_nonneg (absk_nonneg _)]
  have h0 := norm_O_le (D := D) hs hr τ hx (f x.2.1) (g x.2.2.1) (h x.2.2.2)
  have h1 := norm_inner_apply_le (G₀ x.1) (zOf 1 F₀ (inJ x))
    (outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1) (h x.2.2.2)))
  have hP : 0 ≤ ‖G₀ x.1‖ * ‖F₀ (inJ x)‖ := by positivity
  refine h1.trans ?_
  rw [hn]
  set X := ‖outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1) (h x.2.2.2))‖
  have hX : 0 ≤ X := norm_nonneg _
  have h2 : absk (inJ x) * X ≤ absk x.1 * X := mul_le_mul_of_nonneg_right hJL hX
  calc ‖G₀ x.1‖ * (absk (inJ x) * ‖F₀ (inJ x)‖) * X
      = ‖G₀ x.1‖ * ‖F₀ (inJ x)‖ * (absk (inJ x) * X) := by ring
    _ ≤ ‖G₀ x.1‖ * ‖F₀ (inJ x)‖ * (absk x.1 * X) := mul_le_mul_of_nonneg_left h2 hP
    _ ≤ ‖G₀ x.1‖ * ‖F₀ (inJ x)‖ * (2 ^ 37 / |r| ^ 2 * (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) *
        Esep x) := mul_le_mul_of_nonneg_left h0 hP
    _ = _ := by
        simp only [Phi₃, nrm]
        ring

/-- **The static bound of `O`.** -/
theorem Q3_static (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ D : ℝ) (hf : MZ 2 f) (hf' : PiS f = f)
    (hg : MZ 2 g) (hg' : PiS g = g) (hh : MZ 2 h) (hh' : PiS h = h) {G₀ F₀ : Field}
    (hG : Summable fun k => ‖G₀ k‖ ^ 2) (hF : Summable fun k => ‖F₀ k‖ ^ 2) (hF₀ : PiF F₀ = F₀) :
    ‖(famQ s r D).form r τ f g h G₀ F₀‖ ≤ 2 ^ 37 / |r| ^ 2 * (l2n G₀ * l2n F₀ *
      clsS (wiener f) (wiener g) (wiener h) (hnorm 2 f) (hnorm 2 g) (hnorm 2 h)) := by
  refine sep_form hr hf hf' hg hg' hh hh' hG hF hF₀ fun x hx => ?_
  have hL : 1 ≤ absk x.1 := one_le_absk (act_l hx)
  have h0 := norm_O_le (D := D) hs hr τ hx (f x.2.1) (g x.2.2.1) (h x.2.2.2)
  have h1 := norm_inner_apply_le (G₀ x.1) (F₀ (inJ x))
    (outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1) (h x.2.2.2)))
  have hP : 0 ≤ ‖G₀ x.1‖ * ‖F₀ (inJ x)‖ := by positivity
  refine h1.trans ?_
  set X := ‖outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ (f x.2.1) (g x.2.2.1) (h x.2.2.2))‖
  have hX : 0 ≤ X := norm_nonneg _
  have h2 : X ≤ absk x.1 * X := le_mul_of_one_le_left hX hL
  calc ‖G₀ x.1‖ * ‖F₀ (inJ x)‖ * X
      ≤ ‖G₀ x.1‖ * ‖F₀ (inJ x)‖ * (2 ^ 37 / |r| ^ 2 * (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) *
        Esep x) := mul_le_mul_of_nonneg_left (h2.trans h0) hP
    _ = _ := by
        simp only [Phi₃, nrm]
        ring

end OVNS.Quant.Metric

end
