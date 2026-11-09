import OddViscousNS.Quant.Joint.Force.X1Block

/-!
# The output half of `X₁`: the form (step J5, node N12)

LOCAL363: `‖A^{1/2} X₁[S]‖ ≤ C (q^{−1/2} b + q⁻¹ c_S)`, at both weights, on `H³` times.

The comparable part of the block is `√(P/q)` times the slow coefficient, summed by Young with
`‖P^{1/2} f_p‖_{ℓ¹} ≤ √17 b`, "since the horizontal sum of `P⁻³` converges"; the separated part is
`q⁻¹ P³ f_p (K⁻² + J⁻²)`, by `sb_edgeB`, `sb_edgeC`: "the full 3D inverse fourth sum is finite".
Both are symmetric in the two fast legs, so the derivative can sit on either: `X1Form_half_le`,
`X1Form_half_right_le`; no Hermiticity of `X₁` on the form is used.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {s : ℕ} {r : ℝ} {S G F : Field}

/-- `√P f_p` for a slow field: `P³`, the horizontal sum, is summable. -/
def rootP (S : Field) (p : Mode) : ℝ := Real.sqrt (absk p) * ‖S p‖

/-- `‖P^{1/2} f_p‖_{ℓ¹} ≤ √17 b`. -/
lemma l1B_rootP (hS : MZ 2 S) (hS' : PiS S = S) : L1B (rootP S) (Real.sqrt 17 * hnorm 2 S) := by
  set w : Mode → ℝ := fun b => if b 2 = 0 then w3 (0 - b) else 0 with hw
  have hw0 : ∀ b, 0 ≤ w b := fun b => by
    simp only [hw]
    split_ifs
    · exact w3_nonneg _
    · exact le_rfl
  have hW : SB w 17 := fib_w3 0
  have h1 : SB (fun b => Real.sqrt (w b) ^ 2) (Real.sqrt 17 ^ 2) := by
    rw [Real.sq_sqrt (by norm_num)]
    refine hW.of_le (fun b => sq_nonneg _) fun b => ?_
    rw [Real.sq_sqrt (hw0 b)]
  have h2 := (l2B_up hS.inH).sq
  have hc := SB.cs (P := fun b => Real.sqrt (w b)) (Q := up (nrm S)) (fun _ => Real.sqrt_nonneg _)
    (l2B_up hS.inH).nn (Real.sqrt_nonneg _) (hnorm_nonneg _ _) h1 h2
  have hle : ∀ p, rootP S p ≤ Real.sqrt (w p) * up (nrm S) p := fun p => by
    by_cases hp : p 2 = 0
    swap
    · simp only [rootP]
      rw [slow_zero hS' hp, norm_zero, mul_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) ((l2B_up hS.inH).nn p)
    by_cases hp0 : p = 0
    · subst hp0
      simp only [rootP, hS.mean, norm_zero, mul_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) ((l2B_up hS.inH).nn 0)
    have hP : 0 < absk p := lt_of_lt_of_le one_pos (one_le_absk hp0)
    have e1 : w p = (absk p)⁻¹ ^ 3 := by
      simp only [hw, hp, ↓reduceIte, w3]
      rw [zero_sub, absk_neg]
    obtain ⟨t, ht0, ht⟩ : ∃ t : ℝ, 0 < t ∧ absk p = t ^ 2 :=
      ⟨Real.sqrt (absk p), Real.sqrt_pos.2 hP, (Real.sq_sqrt hP.le).symm⟩
    have e2 : Real.sqrt (w p) * up (nrm S) p = Real.sqrt (absk p) * ‖S p‖ := by
      have e3 : w p = (t⁻¹ ^ 3) ^ 2 := by
        rw [e1, ht]
        field_simp
      rw [e3, Real.sqrt_sq (by positivity), ht, Real.sqrt_sq ht0.le]
      simp only [up, nrm]
      rw [← absk_sq p, ht]
      field_simp
    rw [e2]
    rfl
  have h0 : ∀ p, 0 ≤ rootP S p := fun p => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hb := hc.of_le h0 hle
  exact ⟨h0, hb.1, hb.2⟩

/-- The majorant of the half: the comparable part and the two separated parts. -/
def psiH (r : ℝ) (S G F : Field) (x : Mode × Mode) : ℝ :=
  1536 / Real.sqrt |r| * (nrm G x.1 * (rootP S x.2 * nrm F (x.1 - x.2))) +
    2 ^ 10 / |r| * ((nrm G x.1 * nrm F (x.1 - x.2)) *
      (up (gr S) x.2 * if x.1 = 0 then 0 else (absk x.1)⁻¹ ^ 2)) +
    2 ^ 10 / |r| * ((nrm F (x.1 - x.2) * nrm G x.1) *
      (up (gr S) x.2 * if x.1 - x.2 = 0 then 0 else (absk (x.1 - x.2))⁻¹ ^ 2))

lemma psiH_nonneg (r : ℝ) (S G F : Field) (x : Mode × Mode) : 0 ≤ psiH r S G F x := by
  have h1 : 0 ≤ nrm G x.1 := norm_nonneg _
  have h2 : 0 ≤ nrm F (x.1 - x.2) := norm_nonneg _
  have h3 : 0 ≤ rootP S x.2 := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have h4 : 0 ≤ up (gr S) x.2 := mul_nonneg (absSq_nonneg _) (gr_nonneg S _)
  have h5 : 0 ≤ if x.1 = 0 then (0 : ℝ) else (absk x.1)⁻¹ ^ 2 := by
    split_ifs
    · exact le_rfl
    · positivity
  have h6 : 0 ≤ if x.1 - x.2 = 0 then (0 : ℝ) else (absk (x.1 - x.2))⁻¹ ^ 2 := by
    split_ifs
    · exact le_rfl
    · positivity
  have h7 := Real.sqrt_nonneg |r|
  have h8 := abs_nonneg r
  unfold psiH
  positivity

/-- The constant of the half. -/
def Chalf : ℝ := 1536 * Real.sqrt 17 + 2 ^ 11 * c4

/-- The sum of the majorant. -/
lemma sb_psiH (hS : MZ 3 S) (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) :
    SB (psiH r S G F) ((1536 * Real.sqrt 17 / Real.sqrt |r| * hnorm 2 S +
      2 ^ 11 * c4 / |r| * hnorm 3 S) * (l2n G * l2n F)) := by
  have hS2 : MZ 2 S := hS.mono' (by norm_num)
  have hα := l2B_nrm hG
  have hβ := l2B_nrm hF
  have hγ := l1B_rootP hS2 hS'
  have hg := l2B_up_gr hS
  obtain ⟨c1, d1⟩ := hγ.conv_l2 hβ
  have hA : SB (fun x : Mode × Mode => nrm G x.1 * (rootP S x.2 * nrm F (x.1 - x.2)))
      (l2n G * (Real.sqrt 17 * hnorm 2 S * l2n F)) := by
    have hc : SB (fun k => nrm G k * convR (rootP S) (nrm F) k)
        (l2n G * (Real.sqrt 17 * hnorm 2 S * l2n F)) := hα.pair d1
    have hin : ∀ k, SB (fun p => nrm G k * (rootP S p * nrm F (k - p)))
        (nrm G k * convR (rootP S) (nrm F) k) := fun k => by
      refine ⟨(c1 k).mul_left _, ?_⟩
      rw [tsum_mul_left]
      exact le_rfl
    exact SB.prod (H := fun x : Mode × Mode => nrm G x.1 * (rootP S x.2 * nrm F (x.1 - x.2)))
      (fun x => mul_nonneg (hα.nn _) (mul_nonneg (hγ.nn _) (hβ.nn _))) hin hc
  have hB := sb_edgeB hα hβ hg
  have hC := sb_edgeC hα hβ hg
  have h0 : 0 ≤ Real.sqrt |r| := Real.sqrt_nonneg _
  have h1 := abs_nonneg r
  have hs := ((hA.const_mul (by positivity : 0 ≤ 1536 / Real.sqrt |r|)).add
    (hB.const_mul (by positivity : 0 ≤ 2 ^ 10 / |r|))).add
      (hC.const_mul (by positivity : 0 ≤ 2 ^ 10 / |r|))
  refine hs.mono_bd (le_of_eq ?_)
  ring

/-- The summand, once the block is bounded. -/
private lemma half_terms (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {k p : Mode} (hp : p 2 = 0)
    (hj : (k - p) 2 ≠ 0) (v : V3) :
    max (absk k) (absk (k - p)) * ‖X1b s r τ p k (k - p) v‖ ≤
      1536 / Real.sqrt |r| * (Real.sqrt (absk p) * ‖v‖) + 2 ^ 10 / |r| *
        ((absk p ^ 3 * ‖v‖) * ((if k = 0 then 0 else (absk k)⁻¹ ^ 2) +
          if k - p = 0 then 0 else (absk (k - p))⁻¹ ^ 2)) := by
  have h := norm_X1b_max hs hr τ (show p + (k - p) = k by abel) hp hj v
  have hj0 : k - p ≠ 0 := fun h0 => hj (by rw [h0]; rfl)
  have hk0 : k ≠ 0 := fun h0 => hj (by
    have e : (k - p) 2 = k 2 := by simp [hp]
    rw [e, h0]; rfl)
  simp only [hk0, hj0, ↓reduceIte]
  refine h.trans (le_of_eq ?_)
  rw [Real.sqrt_div (absk_nonneg p)]
  ring

/-- The bound of the block, in the terms of the majorant. -/
private lemma halfX_summand (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hS' : PiS S = S)
    (hF' : PiF F = F) (x : Mode × Mode) {L : ℝ}
    (hL : L ≤ max (absk x.1) (absk (x.1 - x.2))) (hL0 : 0 ≤ L) :
    L * (‖G x.1‖ * ‖X1b s r τ x.2 x.1 (x.1 - x.2) (S x.2) (F (x.1 - x.2))‖) ≤ psiH r S G F x := by
  have hΨ := psiH_nonneg r S G F x
  obtain ⟨k, p⟩ := x
  simp only at hL ⊢
  by_cases hj : (k - p) 2 = 0
  · rw [fast_zero hF' hj, map_zero, norm_zero, mul_zero, mul_zero]
    exact hΨ
  by_cases hp : p 2 = 0
  swap
  · rw [slow_zero hS' hp, X1b_zero_leaf, zero_apply, norm_zero, mul_zero, mul_zero]
    exact hΨ
  have h1 := half_terms hs hr τ hp hj (S p)
  have h2 := (ContinuousLinearMap.le_opNorm (X1b s r τ p k (k - p) (S p)) (F (k - p)))
  have h3 := mul_le_mul_of_nonneg_left h2 hL0
  have h4 : L * ‖X1b s r τ p k (k - p) (S p)‖ ≤ max (absk k) (absk (k - p)) *
      ‖X1b s r τ p k (k - p) (S p)‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
  have h5 := (h4.trans h1)
  have hG0 := norm_nonneg (G k)
  have hF0 := norm_nonneg (F (k - p))
  calc L * (‖G k‖ * ‖X1b s r τ p k (k - p) (S p) (F (k - p))‖)
      ≤ L * (‖G k‖ * (‖X1b s r τ p k (k - p) (S p)‖ * ‖F (k - p)‖)) := by
        gcongr
    _ = ‖G k‖ * ‖F (k - p)‖ * (L * ‖X1b s r τ p k (k - p) (S p)‖) := by ring
    _ ≤ ‖G k‖ * ‖F (k - p)‖ * _ := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = psiH r S G F (k, p) := by
        simp only [psiH, nrm, rootP, up, gr]
        rw [← absk_sq p]
        ring

/-- **The output half of `X₁`** (LOCAL363): the derivative on the test. -/
theorem X1Form_half_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hS : MZ 3 S) (hS' : PiS S = S)
    (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) :
    ‖X1Form s r τ S (zOf 1 G) F‖ ≤ (1536 * Real.sqrt 17 / Real.sqrt |r| * hnorm 2 S +
      2 ^ 11 * c4 / |r| * hnorm 3 S) * (l2n G * l2n F) := by
  refine (form_le (sb_psiH hS hS' hG hF) fun x => ?_).2
  have h := halfX_summand (G := G) hs hr τ hS' hF' x (le_max_left _ _) (absk_nonneg _)
  refine le_trans ?_ h
  have e : ‖zOf 1 G x.1‖ = absk x.1 * ‖G x.1‖ := by
    simp only [zOf, norm_smul, Complex.norm_real, pow_one, Real.norm_of_nonneg (absk_nonneg _)]
  refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (le_of_eq ?_)
  rw [e]
  ring

/-- **The output half of `X₁`**: the derivative on the input. -/
theorem X1Form_half_right_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hS : MZ 3 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) :
    ‖X1Form s r τ S G (zOf 1 F)‖ ≤ (1536 * Real.sqrt 17 / Real.sqrt |r| * hnorm 2 S +
      2 ^ 11 * c4 / |r| * hnorm 3 S) * (l2n G * l2n F) := by
  refine (form_le (sb_psiH hS hS' hG hF) fun x => ?_).2
  have h := halfX_summand (G := G) hs hr τ hS' hF' x (le_max_right _ _) (absk_nonneg _)
  refine le_trans ?_ h
  have e : zOf 1 F (x.1 - x.2) = ((absk (x.1 - x.2) : ℝ) : ℂ) • F (x.1 - x.2) := by
    simp only [zOf, pow_one]
  rw [e, map_smul, inner_smul_right, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (absk_nonneg _)]
  refine mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℂ) _ _) (absk_nonneg _)

end OVNS.Quant.Metric

end
