import OddViscousNS.Quant.Joint.Metric.HighAncestor

/-!
# The whole metric forms and their links to the library (step J5, pilot)

What the pilot gives beyond the high ancestors, by the same three layers, and the checks that the
block objects of `Defs.lean` are the library's.

## Whole forms
* `YLForm_le`: NEW378's "Full H2 multiplier":
  `|⟨G, μ (X₂ + Z) 𝓛 F⟩| ≤ (C/q) (W³ + W²b + Wb²) ‖G‖ ‖F‖`, `cls3 W W W b b b`, for every multiplier
  of modulus at most one.
* `X2Form_le`, `X2HalfForm_le`, `DSX2Form_le`: the three prices of LOCAL577 (`959`, `1758`, `7276`),
  with loose constants: operator, output half, genuine `H¹` direction.  The last one has no exterior
  derivative, as in LOCAL440: `M/Σ ≤ 1/R` is enough at `s = 2`.  (Body 12 (18) has `F_s G_s` in
  place of `F_s²`: it is weaker here, not needed at weight two.)
* `YLForm_split`: the form splits exactly into the high-ancestor sector and its complement.  So
  rows 2, 3 are a literal part of the group, and the other sectors of LOCAL440 are the rest.

## Links
* `inner_blk_eq_tripT`: `⟨Z_k, blk m p k q X_p Y_q⟩ = tripT m X Y Z p q`, on a real `Z`.  With
  `Qm_eq_tsum_blk`, `blk` is the summand of the library's `pair … (Qm …)`.
* `zOf_Lop`: `A^{s/2} 𝓛 F = ∑ Lb (A^{s/2} F)`: `Lb` is `Lop` on the energy coordinates.
* `Bslow_eq_tsum`: `Bslow S = ∑ slowV`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. Links to the library -/

/-- `blk` is the summand of the library's triad form. -/
theorem inner_blk_eq_tripT (m : Mult) {X Y Z : Field} (hZ : IsReal Z) (p q : Mode) :
    inner ℂ (Z (p + q)) (blk m p (p + q) q (X p) (Y q)) = tripT m X Y Z p q := by
  rw [blk_apply, tripT]
  simp only [inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [inner_hel_real hZ, bd_hel_vert]

/-- `blk` is linear in the input (the input is an argument of a continuous linear map). -/
lemma zOf_smul_blk (m : Mult) (p k j : Mode) (v w : V3) (c : ℂ) :
    blk m p k j v (c • w) = c • blk m p k j v w := map_smul _ _ _

/-- **`Lb` is `Lop` on the energy coordinates**:
`(A^{s/2} 𝓛_τ(S) F)_k = ∑_p (𝓛_s)_{k,k−p} (A^{s/2} F)` at a fast output, for a mean-zero input. -/
theorem zOf_Lop (s : ℕ) (τ : ℝ) {S F : Field} (hF0 : F 0 = 0) {k : Mode} (hk : k 2 ≠ 0) :
    zOf s (Lop τ S F) k = ∑' p, Lb s τ p k (k - p) (S p) (zOf s F (k - p)) := by
  have hL : Lop τ S F k = (2 : ℂ) • Qphase τ S F k := by simp [Lop, PiF, hk]
  simp only [zOf, hL, Qphase]
  rw [Qm_eq_tsum_blk, smul_smul, ← tsum_const_smul'']
  refine tsum_congr fun p => ?_
  by_cases hj : k - p = 0
  · simp [hj, hF0]
  have hJ : absk (k - p) ≠ 0 := absk_eq_zero.not.2 hj
  simp only [Lb, wt, smul_apply, map_smul, smul_smul]
  congr 1
  push_cast
  rw [div_pow]
  have hJ' : (absk (k - p) : ℂ) ≠ 0 := by exact_mod_cast hJ
  field_simp

/-- **`slowV` is the summand of `B_slow`**, at a slow output. -/
theorem Bslow_eq_tsum (S : Field) {k : Mode} (hk : k 2 = 0) :
    Bslow S k = ∑' a, slowV a (k - a) (S a) (S (k - a)) := by
  simp only [Bslow, PiS, hk, ite_true, slowV]
  rw [Qres, Qm_eq_tsum_blk]
  refine tsum_congr fun a => ?_
  rw [add_sub_cancel]

/-! ### B. The whole forms -/

/-- The summand of the undifferentiated group is summable, for a bounded multiplier. -/
theorem YL_bound {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S G F : Field} (hS : MZ 2 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) {μ : I4 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ 1) :
    (Summable fun x : I4 => μ x * inner ℂ (G x.1) (YLb 2 r τ S S S x (F (inJ x)))) ∧
      ‖YLForm μ 2 r τ S S S G F‖ ≤ 2 ^ 21 / |r| * (l2n G * l2n F *
        cls3 (wiener S) (wiener S) (wiener S) (hnorm 2 S) (hnorm 2 S) (hnorm 2 S)) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have W1 := l1B_nrm hS.inH
  have U1 := l2B_up hS.inH
  have hK : (0 : ℝ) ≤ 2 ^ 21 / |r| := by positivity
  have hΨ := (pos3_E3 (l2B_nrm hG) (l2B_nrm hF) W1 W1 W1 U1 U1 U1).const_mul hK
  refine form_le hΨ fun x => (norm_YL_summand_le hr τ hS' hS' hS' hF' (μ x) x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hK
  have hE := E3_nonneg x
  simp only [Phi₃, nrm]
  have h1 := mul_le_mul_of_nonneg_right (hμ x) (by positivity : 0 ≤ ‖G x.1‖ * ‖F (inJ x)‖ *
    (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖) * E3 x)
  nlinarith only [h1]

/-- **NEW378's whole multiplier**: `|⟨G, (X₂ + Z) 𝓛 F⟩| ≤ (C/q)(W³ + W²b + Wb²) ‖G‖ ‖F‖`. -/
theorem YLForm_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S G F : Field} (hS : MZ 2 S) (hS' : PiS S = S)
    (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F)
    {μ : I4 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ 1) :
    ‖YLForm μ 2 r τ S S S G F‖ ≤ 2 ^ 21 * (1 + c4) ^ 2 * 7 / |r| *
      (wiener S ^ 3 + wiener S ^ 2 * hnorm 2 S + wiener S * hnorm 2 S ^ 2) * (l2n G * l2n F) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hc := c4_pos
  have hb := hnorm_nonneg 2 S
  have hW : 0 ≤ wiener S := tsum_nonneg fun _ => norm_nonneg _
  have hL := mul_nonneg (l2n_nonneg G) (l2n_nonneg F)
  refine (YL_bound hr τ hS hS' hG hF hF' hμ).2.trans ?_
  have hcl : cls3 (wiener S) (wiener S) (wiener S) (hnorm 2 S) (hnorm 2 S) (hnorm 2 S) ≤
      (1 + c4) ^ 2 * 7 * (wiener S ^ 3 + wiener S ^ 2 * hnorm 2 S + wiener S * hnorm 2 S ^ 2) := by
    simp only [cls3]
    set W := wiener S
    set b := hnorm 2 S
    have h1 : 0 ≤ W ^ 3 := by positivity
    have h2 : 0 ≤ W ^ 2 * b := by positivity
    have h3 : 0 ≤ W * b ^ 2 := by positivity
    have e : W * W * W + 2 * c4 * (b * W * W + W * b * W + W * W * b) +
        c4 ^ 2 * (b * b * W + b * W * b + W * b * b) =
        W ^ 3 + 6 * c4 * (W ^ 2 * b) + 3 * c4 ^ 2 * (W * b ^ 2) := by ring
    rw [e]
    have h4 : 0 ≤ c4 * (W ^ 2 * b) := by positivity
    have h5 : 0 ≤ c4 ^ 2 * (W * b ^ 2) := by positivity
    have h6 : 0 ≤ c4 * W ^ 3 := by positivity
    have h7 : 0 ≤ c4 * (W * b ^ 2) := by positivity
    have h8 : 0 ≤ c4 ^ 2 * W ^ 3 := by positivity
    have h9 : 0 ≤ c4 ^ 2 * (W ^ 2 * b) := by positivity
    nlinarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have h1 := mul_le_mul_of_nonneg_left hcl hL
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 ^ 21 / |r|)
  refine h2.trans (le_of_eq ?_)
  ring

/-- **The group splits exactly** into the high-ancestor sector and its complement. -/
theorem YLForm_split {r : ℝ} (hr : r ≠ 0) (τ D : ℝ) {S G F : Field} (hS : MZ 2 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) :
    YLForm (fun _ => 1) 2 r τ S S S G F =
      YLForm (hiMask₃ D) 2 r τ S S S G F +
        YLForm (fun x => 1 - hiMask₃ D x) 2 r τ S S S G F := by
  have hm : ∀ x, ‖hiMask₃ D x‖ ≤ 1 := fun x => by
    unfold hiMask₃
    split_ifs <;> simp
  have hc : ∀ x, ‖1 - hiMask₃ D x‖ ≤ 1 := fun x => by
    unfold hiMask₃
    split_ifs <;> simp
  have h1 := (YL_bound hr τ hS hS' hG hF hF' hm).1
  have h2 := (YL_bound hr τ hS hS' hG hF hF' hc).1
  simp only [YLForm]
  rw [← h1.tsum_add h2]
  refine tsum_congr fun x => ?_
  ring

/-! ### C. The three prices of LOCAL577 -/

/-- `M/Σ ≤ 1` at a nonzero input. -/
lemma chain_le_one {l a b : Mode} (hj : l - a - b ≠ 0) :
    absk (l - a) / heat4 l (l - a - b) a b ≤ 1 := by
  have hH := heat4_pos (l := l) hj a b
  rw [div_le_one hH]
  have h1 := chain_ratio_le (l := l) (a := a) (b := b) hj
  have h2 := one_le_absk hj
  have h3 := absk_nonneg (l - a)
  nlinarith only [h1, h2, h3]

private lemma heat4_nonneg (l j a b : Mode) : 0 ≤ heat4 l j a b := by
  have := absSq_nonneg l
  have := absSq_nonneg j
  have := absSq_nonneg a
  have := absSq_nonneg b
  unfold heat4
  linarith

/-- **The operator price** (LOCAL577 `959`; Body 12 (16)):
`|⟨G, μ X₂(f,g) F⟩| ≤ (C/q) cls₂ ‖G‖ ‖F‖`, that is `C b²/q` on the diagonal. -/
theorem X2Form_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {f g G F : Field} (hf : MZ 2 f) (hf' : PiS f = f)
    (hg : MZ 2 g) (hg' : PiS g = g) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ 1) :
    ‖X2Form μ 2 r τ f g G F‖ ≤ 39424 / |r| *
      (l2n G * l2n F * cls2 (wiener f) (wiener g) (hnorm 2 f) (hnorm 2 g)) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hK : (0 : ℝ) ≤ 39424 / |r| := by positivity
  have hΨ := (pos2_E2 (l2B_nrm hG) (l2B_nrm hF) (l1B_nrm hf.inH) (l1B_nrm hg.inH)
    (l2B_up hf.inH) (l2B_up hg.inH)).const_mul hK
  have hB0 : ∀ x : I3, 0 ≤ 39424 / |r| * (‖f x.2.1‖ * ‖g x.2.2‖) * E2 x := fun x => by
    have := E2_nonneg x
    positivity
  refine (form_le hΨ fun x => (norm_X2_summand_le hf' hg' hF' hB0
    (fun x ha hb hj => ?_) _ x).trans ?_).2
  · refine (norm_X2b_E2_le hr τ f g ha hb hj).trans ?_
    obtain ⟨-, -, hj0⟩ := fast_labels ha hb hj
    have h1 := chain_le_one hj0
    have h2 := E2_nonneg x
    have h3 : 0 ≤ ‖f x.2.1‖ * ‖g x.2.2‖ := by positivity
    calc _ ≤ 39424 / |r| * 1 * (‖f x.2.1‖ * ‖g x.2.2‖) * E2 x := by gcongr
      _ = _ := by ring
  · have hE := E2_nonneg x
    have h1 := mul_le_mul_of_nonneg_right (hμ x) (by positivity :
      0 ≤ 39424 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * (‖f x.2.1‖ * ‖g x.2.2‖) * E2 x))
    simp only [Phi₂, nrm]
    calc _ = _ := by ring
      _ ≤ _ := h1
      _ = _ := by ring

/-- **The output-half price** (LOCAL577 `1758`; Body 12 (17)). -/
theorem X2HalfForm_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {f g G F : Field} (hf : MZ 2 f)
    (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ 1) :
    ‖X2HalfForm μ 2 r τ f g G F‖ ≤ 2 * 39424 / |r| *
      (l2n G * l2n F * cls2 (wiener f) (wiener g) (hnorm 2 f) (hnorm 2 g)) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hK : (0 : ℝ) ≤ 2 * 39424 / |r| := by positivity
  have hΨ := (pos2_E2 (l2B_nrm hG) (l2B_nrm hF) (l1B_nrm hf.inH) (l1B_nrm hg.inH)
    (l2B_up hf.inH) (l2B_up hg.inH)).const_mul hK
  have hB0 : ∀ x : I3, 0 ≤ 39424 / |r| * (absk (x.1 - x.2.1) /
      heat4 x.1 (x.1 - x.2.1 - x.2.2) x.2.1 x.2.2) * (‖f x.2.1‖ * ‖g x.2.2‖) * E2 x := fun x => by
    have h1 := heat4_nonneg x.1 (x.1 - x.2.1 - x.2.2) x.2.1 x.2.2
    have := E2_nonneg x
    have := absk_nonneg (x.1 - x.2.1)
    positivity
  refine (form_le hΨ fun x => (norm_X2_summand_le hf' hg' hF' hB0
    (fun x ha hb hj => ?_) _ x).trans ?_).2
  · refine (norm_X2b_E2_le hr τ f g ha hb hj).trans (le_of_eq ?_)
    ring
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (absk_nonneg _)]
    have hE := E2_nonneg x
    have hR := half_ratio_le x.1 x.2.1 x.2.2
    have h0 := heat4_nonneg x.1 (x.1 - x.2.1 - x.2.2) x.2.1 x.2.2
    set R := absk x.1 * (absk (x.1 - x.2.1) / heat4 x.1 (x.1 - x.2.1 - x.2.2) x.2.1 x.2.2)
      with hRd
    have hR0 : 0 ≤ R := by
      have := absk_nonneg x.1
      have := absk_nonneg (x.1 - x.2.1)
      positivity
    have hX : 0 ≤ ‖G x.1‖ * ‖F (inJ₂ x)‖ * (‖f x.2.1‖ * ‖g x.2.2‖) * E2 x := by positivity
    have h1 : ‖μ x‖ * R ≤ 1 * 2 := mul_le_mul (hμ x) hR hR0 zero_le_one
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity :
      0 ≤ 39424 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * (‖f x.2.1‖ * ‖g x.2.2‖) * E2 x))
    simp only [Phi₂, nrm]
    rw [hRd] at h2
    calc _ = ‖μ x‖ * (absk x.1 * (absk (x.1 - x.2.1) /
          heat4 x.1 (x.1 - x.2.1 - x.2.2) x.2.1 x.2.2)) *
            (39424 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * (‖f x.2.1‖ * ‖g x.2.2‖) * E2 x)) := by ring
      _ ≤ _ := h2
      _ = _ := by ring

/-- **The genuine `H¹` direction** (LOCAL577 `7276`; LOCAL440 "Both differentiated groups"): both
slots of `X₂`, `|⟨G, μ D_S X₂[h] F⟩| ≤ (C/q) ‖h‖₁ (W + b) ‖G‖ ‖F‖` for `h ∈ H¹`: no `H²` norm of
`h`, no exterior derivative, no log. -/
theorem DSX2Form_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {h S G F : Field} (hh : MZ 1 h)
    (hh' : PiS h = h) (hS : MZ 2 S) (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ 1) :
    ‖DSX2Form μ 2 r τ h S G F‖ ≤ 39424 / |r| * (l2n G * l2n F *
      (cls2 (c4 * hnorm 1 h) (wiener S) (hnorm 1 h) (hnorm 2 S) +
        cls2 (wiener S) (c4 * hnorm 1 h) (hnorm 2 S) (hnorm 1 h))) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hK : (0 : ℝ) ≤ 39424 / |r| := by positivity
  have hg := l2B_gr hh.inH
  have W1 : L1B (dv h) (c4 * hnorm 1 h) := hg.in2
  have U1 : L2B (up (dv h)) (hnorm 1 h) := by rw [up_dv]; exact hg
  have W2 := l1B_nrm hS.inH
  have U2 := l2B_up hS.inH
  have p1 := (pos2_E2 (l2B_nrm hG) (l2B_nrm hF) W1 W2 U1 U2).const_mul hK
  have p2 := (pos2_E2 (l2B_nrm hG) (l2B_nrm hF) W2 W1 U2 U1).const_mul hK
  have hB1 : ∀ x : I3, 0 ≤ 39424 / |r| * (dv h x.2.1 * ‖S x.2.2‖) * E2 x := fun x => by
    have := E2_nonneg x
    have := dv_nonneg h x.2.1
    positivity
  have hB2 : ∀ x : I3, 0 ≤ 39424 / |r| * (‖S x.2.1‖ * dv h x.2.2) * E2 x := fun x => by
    have := E2_nonneg x
    have := dv_nonneg h x.2.2
    positivity
  have h1 := (form_le p1 fun x => (norm_X2_summand_le hh' hS' hF' hB1
    (fun x ha hb hj => norm_X2b_left_le hr τ hh.mean ha hb hj) _ x).trans
      (show _ ≤ 39424 / |r| * (Phi₂ (nrm G) (nrm F) (dv h) (nrm S) x * E2 x) by
        have hE := E2_nonneg x
        have hd := dv_nonneg h x.2.1
        have h1 := mul_le_mul_of_nonneg_right (hμ x) (by positivity :
          0 ≤ 39424 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * (dv h x.2.1 * ‖S x.2.2‖) * E2 x))
        simp only [Phi₂, nrm]
        calc _ = _ := by ring
          _ ≤ _ := h1
          _ = _ := by ring)).2
  have h2 := (form_le p2 fun x => (norm_X2_summand_le hS' hh' hF' hB2
    (fun x ha hb hj => norm_X2b_right_le hr τ hh.mean ha hb hj) _ x).trans
      (show _ ≤ 39424 / |r| * (Phi₂ (nrm G) (nrm F) (nrm S) (dv h) x * E2 x) by
        have hE := E2_nonneg x
        have hd := dv_nonneg h x.2.2
        have h1 := mul_le_mul_of_nonneg_right (hμ x) (by positivity :
          0 ≤ 39424 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * (‖S x.2.1‖ * dv h x.2.2) * E2 x))
        simp only [Phi₂, nrm]
        calc _ = _ := by ring
          _ ≤ _ := h1
          _ = _ := by ring)).2
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  ring

end OVNS.Quant.Metric

end
