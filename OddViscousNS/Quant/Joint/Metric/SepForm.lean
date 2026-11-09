import OddViscousNS.Quant.Joint.Metric.SepKer

/-!
# The primitive-separated high-last sector: the form (step J5, node N9)

Body 43 (LOCAL663).  On the mask `muS` (`YLForm_sep_le`, with `W = ‖Ŝ‖_{ℓ¹}`, `b = ‖S‖₂`,
`c = ‖S‖₃`, `q = |r|`):
`|⟨G, μ (X₂ + Z) 𝓛 F⟩| ≲ [q⁻² W b c + q⁻² √(1 + ln D) (W b² + b³) + q⁻³ D² W b²] ‖G‖ ‖F‖`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {D : ℝ} {x : I4}

/-- The energy coordinates of a field, against the Sobolev weights. -/
lemma weight_zOf (σ m : ℕ) (u : Field) (k : Mode) :
    sobWeight (σ : ℝ) k * ‖zOf m u k‖ ^ 2 = sobWeight ((σ + m : ℕ) : ℝ) k * ‖u k‖ ^ 2 := by
  by_cases hk : k = 0
  · simp [sobWeight, hk]
  · rw [sobWeight_nat _ hk, sobWeight_nat _ hk]
    simp only [zOf, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (absk_nonneg k) _)]
    ring

lemma inH_zOf {σ m : ℕ} {u : Field} (hu : InH ((σ + m : ℕ) : ℝ) u) : InH (σ : ℝ) (zOf m u) :=
  hu.congr fun k => (weight_zOf σ m u k).symm

lemma hnorm_zOf (σ m : ℕ) (u : Field) : hnorm (σ : ℝ) (zOf m u) = hnorm ((σ + m : ℕ) : ℝ) u := by
  simp only [hnorm, weight_zOf]

lemma mz_zOf_one {u : Field} (hu : MZ 2 u) : MZ 1 (zOf 1 u) := by
  refine ⟨?_, by simp [zOf, hu.mean]⟩
  have h : InH ((1 + 1 : ℕ) : ℝ) u := by
    have := hu.inH
    norm_num at this ⊢
    exact this
  simpa using inH_zOf (σ := 1) (m := 1) h

lemma piS_zOf (m : ℕ) {u : Field} (hu : PiS u = u) : PiS (zOf m u) = zOf m u := by
  funext k
  by_cases hk : k 2 = 0
  · simp [PiS, hk]
  · have h0 : u k = 0 := slow_zero hu hk
    simp [PiS, hk, zOf, h0]

lemma l2B_zOf_three {u : Field} (hu : InH 3 u) : L2B (nrm (zOf 3 u)) (hnorm 3 u) := by
  have h3 : InH ((0 + 3 : ℕ) : ℝ) u := by simpa using hu
  have hz : Summable fun k => sobWeight ((0 + 3 : ℕ) : ℝ) k * ‖u k‖ ^ 2 := h3
  have hn : ∀ k, nrm (zOf 3 u) k ^ 2 = sobWeight ((0 + 3 : ℕ) : ℝ) k * ‖u k‖ ^ 2 := fun k => by
    by_cases hk : k = 0
    · simp [nrm, zOf, hk, sobWeight, absk, absSq]
    · rw [sobWeight_nat _ hk]
      simp only [nrm, zOf, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (pow_nonneg (absk_nonneg k) _)]
      ring
  refine ⟨fun _ => norm_nonneg _, ?_, ?_⟩
  · simp only [hn]
    exact hz
  · simp only [hn, hnorm]
    norm_num

/-- The majorant of the separated form. -/
def PsiS (D q : ℝ) (f g h G F : Field) (x : I4) : ℝ :=
  2 ^ 36 / q ^ 2 * (
    Phi₃ (in2 (nrm G)) (in2 (nrm F)) (up (nrm f)) (nrm g) (nrm (zOf 3 h)) x +
    Phi₃ (in2 (nrm G)) (in2 (nrm F)) (nrm f) (up (nrm g)) (nrm (zOf 3 h)) x +
    Phi₃ (nrm G) (in2 (nrm F)) (up (nrm f)) (nrm g) (nrm (loP D (zOf 1 h))) x +
    Phi₃ (nrm G) (in2 (nrm F)) (nrm f) (up (nrm g)) (nrm (loP D (zOf 1 h))) x +
    Phi₃ (in2 (nrm G)) (in2 (nrm F)) (up (nrm f)) (up (nrm g)) (nrm (loP D (zOf 1 h))) x) +
  2 ^ 23 * D ^ 2 / q ^ 3 *
    Phi₃ (in2 (nrm G)) (in2 (nrm F)) (up (nrm f)) (up (nrm g)) (nrm h) x

/-- The sum of the separated majorant. -/
def sepB (D q : ℝ) (f g h : Field) : ℝ :=
  2 ^ 36 / q ^ 2 * (
    c4 ^ 2 * ((hnorm 2 f * wiener g + wiener f * hnorm 2 g) * hnorm 3 h) +
    c4 * Real.sqrt (9 + 8 * Real.log D) * ((hnorm 2 f * wiener g + wiener f * hnorm 2 g) * hnorm 2 h) +
    c4 ^ 2 * Real.sqrt (9 + 8 * Real.log D) * (hnorm 2 f * hnorm 2 g * hnorm 2 h)) +
  2 ^ 23 * D ^ 2 / q ^ 3 * (c4 ^ 2 * (hnorm 2 f * hnorm 2 g * wiener h))

/-- **The sum of the separated form.** -/
lemma sb_PsiS {q : ℝ} (hq : 0 < q) (hD : 1 ≤ D) {f g h G F : Field} (hf : MZ 2 f) (hg : MZ 2 g)
    (hh : MZ 2 h) (hh3 : InH 3 h) (hh' : PiS h = h) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) :
    SB (PsiS D q f g h G F) (l2n G * l2n F * sepB D q f g h) := by
  have hα := l2B_nrm hG
  have hβ := l2B_nrm hF
  have hα2 := hα.in2
  have hβ2 := hβ.in2
  have uf := l2B_up hf.inH
  have ug := l2B_up hg.inH
  have wf := l1B_nrm hf.inH
  have wg := l1B_nrm hg.inH
  have wh := l1B_nrm hh.inH
  have c3 := l2B_zOf_three hh3
  have lo := l1B_lo hD (mz_zOf_one hh) (piS_zOf 1 hh')
  have e12 : hnorm 1 (zOf 1 h) = hnorm 2 h := by
    have := hnorm_zOf 1 1 h
    norm_num at this
    exact this
  rw [e12] at lo
  have t1 : SB (Phi₃ (in2 (nrm G)) (in2 (nrm F)) (up (nrm f)) (nrm g) (nrm (zOf 3 h))) _ :=
    SB.equiv swap23 (pos3_III hα2 hβ2 uf c3 wg) (Phi₃_swap23 _ _ _ _ _)
  have t2 : SB (Phi₃ (in2 (nrm G)) (in2 (nrm F)) (nrm f) (up (nrm g)) (nrm (zOf 3 h))) _ :=
    SB.equiv swap12 (SB.equiv swap23 (pos3_III hα2 hβ2 ug c3 wf) (Phi₃_swap23 _ _ _ _ _))
      (Phi₃_swap12 _ _ _ _ _)
  have t3 : SB (Phi₃ (nrm G) (in2 (nrm F)) (up (nrm f)) (nrm g) (nrm (loP D (zOf 1 h)))) _ :=
    pos3_II' hα hβ2 uf wg lo
  have t4 : SB (Phi₃ (nrm G) (in2 (nrm F)) (nrm f) (up (nrm g)) (nrm (loP D (zOf 1 h)))) _ :=
    SB.equiv swap12 (pos3_II' hα hβ2 ug wf lo) (Phi₃_swap12 _ _ _ _ _)
  have t5 : SB (Phi₃ (in2 (nrm G)) (in2 (nrm F)) (up (nrm f)) (up (nrm g))
      (nrm (loP D (zOf 1 h)))) _ := pos3_III hα2 hβ2 uf ug lo
  have t6 : SB (Phi₃ (in2 (nrm G)) (in2 (nrm F)) (up (nrm f)) (up (nrm g)) (nrm h)) _ :=
    pos3_III hα2 hβ2 uf ug wh
  have h1 := ((((t1.add t2).add t3).add t4).add t5).const_mul
    (by positivity : 0 ≤ 2 ^ 36 / q ^ 2)
  have h2 := t6.const_mul (by positivity : 0 ≤ 2 ^ 23 * D ^ 2 / q ^ 3)
  refine (h1.add h2).mono_bd (le_of_eq ?_)
  simp only [sepB]
  ring

lemma PsiS_nonneg {q : ℝ} (hq : 0 < q) (f g h G F : Field) (x : I4) : 0 ≤ PsiS D q f g h G F x := by
  have n1 : ∀ u : Field, ∀ k, 0 ≤ nrm u k := fun u k => norm_nonneg _
  have n2 : ∀ u : Field, ∀ k, 0 ≤ up (nrm u) k := fun u k => up_nrm_nonneg u k
  have n3 : ∀ u : Field, ∀ k, 0 ≤ in2 (nrm u) k := fun u k =>
    div_nonneg (norm_nonneg _) (absSq_nonneg k)
  have t := fun (α β f₁ f₂ f₃ : Mode → ℝ) (a b c d e) =>
    Phi₃_nonneg (α := α) (β := β) (f₁ := f₁) (f₂ := f₂) (f₃ := f₃) a b c d e x
  unfold PsiS
  have h1 := t _ _ _ _ _ (n3 G) (n3 F) (n2 f) (n1 g) (n1 (zOf 3 h))
  have h2 := t _ _ _ _ _ (n3 G) (n3 F) (n1 f) (n2 g) (n1 (zOf 3 h))
  have h3 := t _ _ _ _ _ (n1 G) (n3 F) (n2 f) (n1 g) (n1 (loP D (zOf 1 h)))
  have h4 := t _ _ _ _ _ (n1 G) (n3 F) (n1 f) (n2 g) (n1 (loP D (zOf 1 h)))
  have h5 := t _ _ _ _ _ (n3 G) (n3 F) (n2 f) (n2 g) (n1 (loP D (zOf 1 h)))
  have h6 := t _ _ _ _ _ (n3 G) (n3 F) (n2 f) (n2 g) (n1 h)
  positivity

/-- The majorant on the support, against the kernels. -/
lemma PsiS_eq {q : ℝ} (hS : OnS D x) (f g h G F : Field) :
    PsiS D q f g h G F x = ‖G x.1‖ * ‖F (inJ x)‖ *
      ((2 ^ 36 / q ^ 2 * (Eg x + El x + Em x) + 2 ^ 23 * D ^ 2 / q ^ 3 * Eh x) *
        (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖)) := by
  have hc := absk_nonneg x.2.2.2
  have e1 : nrm (zOf 3 h) x.2.2.2 = absk x.2.2.2 ^ 3 * ‖h x.2.2.2‖ := by
    simp only [nrm, zOf, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hc _)]
  have e2 : nrm (loP D (zOf 1 h)) x.2.2.2 = absk x.2.2.2 * ‖h x.2.2.2‖ := by
    have hn : ¬ D < absk x.2.2.2 := not_lt.2 hS.c_le
    simp only [nrm, loP, hn, ↓reduceIte, zOf, norm_smul, Complex.norm_real, pow_one,
      Real.norm_of_nonneg hc]
  simp only [PsiS, Phi₃, in2, up, e1, e2, Eg, El, Em, Eh]
  simp only [nrm, ← absk_sq]
  ring

/-- A term of the separated form. -/
lemma YLsep_term {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {f g h G F : Field} (hf' : PiS f = f)
    (hg' : PiS g = g) (hh' : PiS h = h) (hF' : PiF F = F) {μ : I4 → ℂ}
    (hμ : ∀ x, ‖μ x‖ ≤ muS D x) (x : I4) :
    ‖μ x * inner ℂ (G x.1) (YLb 2 r τ f g h x (F (inJ x)))‖ ≤ PsiS D |r| f g h G F x := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hR := PsiS_nonneg (D := D) hq f g h G F x
  by_cases hm : muS D x = 0
  · have h0 : μ x = 0 := by
      have := hμ x
      rw [hm] at this
      exact norm_le_zero_iff.1 this
    simpa [h0] using hR
  by_cases ha : x.2.1 2 = 0
  swap
  · rw [YLb_eq_zero (Or.inl (slow_zero hf' ha))]
    simpa using hR
  by_cases hb : x.2.2.1 2 = 0
  swap
  · rw [YLb_eq_zero (Or.inr (Or.inl (slow_zero hg' hb)))]
    simpa using hR
  by_cases hc : x.2.2.2 2 = 0
  swap
  · rw [YLb_eq_zero (Or.inr (Or.inr (slow_zero hh' hc)))]
    simpa using hR
  by_cases hj : inJ x 2 = 0
  · rw [fast_zero hF' hj, map_zero, inner_zero_right, mul_zero, norm_zero]
    exact hR
  have hS := onS_of_ne hm
  have hB := norm_YLb_sep hr τ ⟨ha, hb, hc, hj⟩ hS f g h
  rw [PsiS_eq hS, norm_mul]
  have h1 := norm_inner_apply_le (G x.1) (F (inJ x)) (YLb 2 r τ f g h x)
  have hμ1 : ‖μ x‖ ≤ 1 := (hμ x).trans (muS_le_one D x)
  have hP : 0 ≤ ‖G x.1‖ * ‖F (inJ x)‖ := by positivity
  calc _ ≤ 1 * (‖G x.1‖ * ‖F (inJ x)‖ * ‖YLb 2 r τ f g h x‖) :=
        mul_le_mul hμ1 h1 (norm_nonneg _) zero_le_one
    _ = ‖G x.1‖ * ‖F (inJ x)‖ * ‖YLb 2 r τ f g h x‖ := one_mul _
    _ ≤ _ := mul_le_mul_of_nonneg_left hB hP

/-- **The primitive-separated high-last sector** (Body 43), on the actual Fourier-side form. -/
theorem YLForm_sep_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hD : 1 ≤ D) {f g h G F : Field} (hf : MZ 2 f)
    (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g) (hh : MZ 2 h) (hh3 : InH 3 h)
    (hh' : PiS h = h) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) {μ : I4 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ muS D x) :
    (Summable fun x : I4 => μ x * inner ℂ (G x.1) (YLb 2 r τ f g h x (F (inJ x)))) ∧
      ‖YLForm μ 2 r τ f g h G F‖ ≤ l2n G * l2n F * sepB D |r| f g h :=
  form_le (sb_PsiS (abs_pos.2 hr) hD hf hg hh hh3 hh' hG hF) (YLsep_term hr τ hf' hg' hh' hF' hμ)

end OVNS.Quant.Metric

end
