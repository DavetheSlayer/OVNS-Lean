import OddViscousNS.Quant.Joint.Force.Native

/-!
# Hermiticity and the output half of the forms of `X₂`, `Z` (step J5, node N12)

The force sits in both slots of a form: `⟨N_z, X₂ z⟩ + ⟨z, X₂ N_z⟩`.  The output half
(`X2Half_lo_le`, `X2Half_high_le`, `ZForm_half_le`) puts the half derivative on the test, so the
second slot needs Hermiticity on the form: `X2Form_conj`, `ZForm_conj`, the summed `adjoint_X2b`,
`adjoint_Zb`.  `X2Half_total_le` is the whole output half of Body 41, `μ = 1`: the sum of the
low and the high ancestor masks.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. The forms are Hermitian -/

/-- The path reversal of `X₂`. -/
def revX2 : I3 ≃ I3 where
  toFun x := (x.1 - x.2.1 - x.2.2, -x.2.2, -x.2.1)
  invFun x := (x.1 - x.2.1 - x.2.2, -x.2.2, -x.2.1)
  left_inv := fun ⟨l, a, b⟩ => by
    refine Prod.ext ?_ (Prod.ext (neg_neg a) (neg_neg b))
    show l - a - b - -b - -a = l
    abel
  right_inv := fun ⟨l, a, b⟩ => by
    refine Prod.ext ?_ (Prod.ext (neg_neg a) (neg_neg b))
    show l - a - b - -b - -a = l
    abel

/-- The path reversal of `Z`. -/
def revZ : I3 ≃ I3 where
  toFun x := (x.1 - x.2.1 - x.2.2, -x.2.1, -x.2.2)
  invFun x := (x.1 - x.2.1 - x.2.2, -x.2.1, -x.2.2)
  left_inv := fun ⟨l, a, b⟩ => by
    refine Prod.ext ?_ (Prod.ext (neg_neg a) (neg_neg b))
    show l - a - b - -a - -b = l
    abel
  right_inv := fun ⟨l, a, b⟩ => by
    refine Prod.ext ?_ (Prod.ext (neg_neg a) (neg_neg b))
    show l - a - b - -a - -b = l
    abel

/-- **`X₂` is Hermitian on the form**, on real slow data. -/
theorem X2Form_conj (s : ℕ) (r τ : ℝ) {f g : Field} (hf : IsReal f) (hg : IsReal g) (G F : Field) :
    X2Form 1 s r τ f g G F = conj (X2Form 1 s r τ g f F G) := by
  unfold X2Form
  rw [Complex.conj_tsum, ← revX2.tsum_eq]
  refine tsum_congr fun x => ?_
  obtain ⟨l, a, b⟩ := x
  simp only [Pi.one_apply, one_mul, revX2, Equiv.coe_fn_mk]
  have e1 : l - a - b - -b - -a = l := by abel
  rw [e1, ← adjoint_X2b s r τ hg hf l a b, ContinuousLinearMap.adjoint_inner_right,
    inner_conj_symm]

/-- **`Z` is Hermitian on the form**, on real slow data. -/
theorem ZForm_conj (s : ℕ) (r τ : ℝ) {f g : Field} (hf : IsReal f) (hg : IsReal g) (G F : Field) :
    ZForm 1 s r τ f g G F = conj (ZForm 1 s r τ f g F G) := by
  unfold ZForm
  rw [Complex.conj_tsum, ← revZ.tsum_eq]
  refine tsum_congr fun x => ?_
  obtain ⟨l, a, b⟩ := x
  simp only [Pi.one_apply, one_mul, revZ, Equiv.coe_fn_mk]
  have e1 : l - a - b - -a - -b = l := by abel
  rw [e1, ← adjoint_Zb s r τ hf hg l a b, ContinuousLinearMap.adjoint_inner_right,
    inner_conj_symm]

/-! ### B. The output half -/

/-- The output half is the form with `zOf 1` on the test. -/
lemma X2Form_zOf (μ : I3 → ℂ) (s : ℕ) (r τ : ℝ) (f g G F : Field) :
    X2Form μ s r τ f g (zOf 1 G) F = X2HalfForm μ s r τ f g G F := by
  unfold X2Form X2HalfForm
  refine tsum_congr fun x => ?_
  simp only [zOf, pow_one, inner_smul_left, Complex.conj_ofReal]
  ring

variable {r τ : ℝ} {f g G F : Field}

/-- The summand of the output half at weight two. -/
private lemma half_term_le (hr : r ≠ 0) (τ : ℝ) (hf' : PiS f = f) (hg' : PiS g = g)
    (hF' : PiF F = F) {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ 1) (x : I3) :
    ‖μ x * ((absk x.1 : ℝ) : ℂ) * inner ℂ (G x.1)
        (X2b 2 r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))‖ ≤
      2 * 39424 / |r| * (Phi₂ (nrm G) (nrm F) (nrm f) (nrm g) x * E2 x) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hB0 : ∀ x : I3, 0 ≤ 39424 / |r| * (absk (x.1 - x.2.1) /
      heat4 x.1 (x.1 - x.2.1 - x.2.2) x.2.1 x.2.2) * (‖f x.2.1‖ * ‖g x.2.2‖) * E2 x := fun x => by
    have h1 := Hx_nonneg x
    have := E2_nonneg x
    have := absk_nonneg (x.1 - x.2.1)
    simp only [Hx, inJ₂] at h1
    positivity
  refine (norm_X2_summand_le hf' hg' hF' hB0
    (fun x ha hb hj => ?_) _ x).trans ?_
  · refine (norm_X2b_E2_le hr τ f g ha hb hj).trans (le_of_eq ?_)
    ring
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (absk_nonneg _)]
    have hE := E2_nonneg x
    have hR := half_ratio_le x.1 x.2.1 x.2.2
    have h0 := Hx_nonneg x
    simp only [Hx, inJ₂] at h0
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

/-- The series of the output half converges, for every multiplier of modulus at most one. -/
lemma X2Half_summable (hr : r ≠ 0) (τ : ℝ) (hf : MZ 2 f) (hf' : PiS f = f) (hg : MZ 2 g)
    (hg' : PiS g = g) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ 1) :
    Summable fun x : I3 => μ x * ((absk x.1 : ℝ) : ℂ) * inner ℂ (G x.1)
      (X2b 2 r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2))) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hΨ := (pos2_E2 (l2B_nrm hG) (l2B_nrm hF) (l1B_nrm hf.inH) (l1B_nrm hg.inH)
    (l2B_up hf.inH) (l2B_up hg.inH)).const_mul (by positivity : (0 : ℝ) ≤ 2 * 39424 / |r|)
  exact (form_le hΨ (half_term_le hr τ hf' hg' hF' hμ)).1

/-- The low price of the output half (Body 41): `q⁻¹(W² + (1 + ln D) a²) + q⁻² D b²`. -/
def X2Lo (r D : ℝ) (f g : Field) : ℝ :=
  2 ^ 28 / |r| * (wiener f * wiener g) +
    2 ^ 18 / |r| * ((9 + 8 * Real.log D) * (hnorm 1 f * hnorm 1 g)) +
    2 ^ 19 * D / |r| ^ 2 * cls2 (wiener f) (wiener g) (hnorm 2 f) (hnorm 2 g)

/-- **The whole output half of `X₂`** (Body 41): the low and the high ancestor masks at `D`. -/
theorem X2Half_total_le (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 1 ≤ D) {S : Field} (hS : MZ 2 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) :
    ‖X2HalfForm 1 2 r τ S S G F‖ ≤
      (X2Lo r D S S + Cm2 / |r| * (hnorm 2 S * tailB D S)) * (l2n G * l2n F) := by
  have hhi : ∀ x, ‖hiMask₂ D x‖ ≤ 1 := fun x => by
    unfold hiMask₂
    split_ifs <;> simp
  have s1 := X2Half_summable (G := G) (F := F) hr τ hS hS' hS hS' hG hF hF' hhi
  have s2 := X2Half_summable (G := G) (F := F) hr τ hS hS' hS hS' hG hF hF' (norm_loMask₂_le D)
  have e : X2HalfForm 1 2 r τ S S G F =
      X2HalfForm (hiMask₂ D) 2 r τ S S G F + X2HalfForm (loMask₂ D) 2 r τ S S G F := by
    simp only [X2HalfForm]
    rw [← s1.tsum_add s2]
    refine tsum_congr fun x => ?_
    rw [Pi.one_apply, ← add_mul, ← add_mul, hi_add_lo₂]
  have h1 := X2Half_high_le hr τ D hS hS' hG hF hF' (μ := hiMask₂ D) fun _ => le_rfl
  have h2 := X2Half_lo_le (Or.inr rfl) hr τ hD hS hS' hS hS' hG hF hF' (μ := loMask₂ D)
    fun _ => le_rfl
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  unfold X2Lo
  ring

end OVNS.Quant.Metric

end
