import OddViscousNS.Quant.Joint.Metric.Edge

/-!
# The heat form of `H⁻¹` (step J5, node N5)

`form_heat`: for every family, `⟨G, O(f, g) F⟩ = −∫₀^∞ ⟨E_u G, T_{τ + r u}(E_u f, E_u g) E_u F⟩ du`,
the absolutely convergent form of `O = −∫₀^∞ E_u T(t + u; S_u) E_u du` (Body 12 §§7, 8; Body 40).
One channel is `outer_heat_integral`; the labels are summed by Fubini, with the majorant of the
source, in which `(L + A + B)/Σ ≤ 1`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### One channel -/

/-- One heat channel. -/
def chanF (H r φ τ : ℝ) (c : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (-u * H) : ℝ) : ℂ) * (Complex.exp (Complex.I * ((τ + r * u) * φ : ℝ)) * c)

lemma chanF_eq (H r φ τ : ℝ) (c : ℂ) (u : ℝ) :
    chanF H r φ τ c u = Complex.exp ((((-H : ℝ) : ℂ) + ((r * φ : ℝ) : ℂ) * Complex.I) * u) *
      (Complex.exp (Complex.I * (τ * φ : ℝ)) * c) := by
  have e : ((Real.exp (-u * H) : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ + r * u) * φ : ℝ)) =
      Complex.exp ((((-H : ℝ) : ℂ) + ((r * φ : ℝ) : ℂ) * Complex.I) * u) *
        Complex.exp (Complex.I * (τ * φ : ℝ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold chanF
  rw [← mul_assoc, e, mul_assoc]

lemma chanF_integrable {H : ℝ} (hH : 0 < H) (r φ τ : ℝ) (c : ℂ) :
    IntegrableOn (chanF H r φ τ c) (Ioi 0) := by
  have hre : (((-H : ℝ) : ℂ) + ((r * φ : ℝ) : ℂ) * Complex.I).re < 0 := by simpa using hH
  have h := (integrableOn_exp_mul_complex_Ioi hre 0).mul_const
    (Complex.exp (Complex.I * (τ * φ : ℝ)) * c)
  have e : chanF H r φ τ c = fun u : ℝ =>
      Complex.exp ((((-H : ℝ) : ℂ) + ((r * φ : ℝ) : ℂ) * Complex.I) * u) *
        (Complex.exp (Complex.I * (τ * φ : ℝ)) * c) := funext (chanF_eq H r φ τ c)
  rw [e]
  exact h

lemma chanF_integral {H : ℝ} (hH : 0 < H) (r φ τ : ℝ) (c : ℂ) :
    -∫ u in Ioi (0 : ℝ), chanF H r φ τ c u =
      resolv (-1) H (r * φ) * (Complex.exp (Complex.I * (τ * φ : ℝ)) * c) := by
  simp only [chanF_eq]
  rw [integral_mul_const, ← neg_mul, outer_heat_integral hH]

section Term

variable {r H : ℝ} {l j : Mode} {Sr : ℝ → V3 → V3 → Blk} {Sr0 : V3 →L[ℂ] V3 →L[ℂ] Blk}

lemma oTerm_eq' (hcov : ∀ τ v w c e y, hel c l (Sr τ v w (hel e j y)) =
      Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) • hel c l (Sr0 v w (hel e j y)))
    (G F v w : V3) (τ : ℝ) :
    oTerm r H l j Sr G F v w τ = ∑ c : Sgn, ∑ e : Sgn,
      resolv (-1) H (r * outerPhi c e l j) * (Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) *
        core Sr0 l j c e G F v w) := by
  rw [oTerm, inner_outerInv]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  rw [hcov, inner_smul_right]
  rfl

lemma source_eq' (hcov : ∀ τ v w c e y, hel c l (Sr τ v w (hel e j y)) =
      Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) • hel c l (Sr0 v w (hel e j y)))
    (G F v w : V3) (τ : ℝ) :
    inner ℂ G (leray l (Sr τ v w (leray j F))) = ∑ c : Sgn, ∑ e : Sgn,
      Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) * core Sr0 l j c e G F v w := by
  rw [inner_leray_leray]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  rw [hcov, inner_smul_right]
  rfl

/-- **One term as a heat integral.** -/
theorem oTerm_heat (hH : 0 < H) (hcov : ∀ τ v w c e y, hel c l (Sr τ v w (hel e j y)) =
      Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) • hel c l (Sr0 v w (hel e j y)))
    (G F v w : V3) (τ : ℝ) :
    IntegrableOn (fun u => ((Real.exp (-u * H) : ℝ) : ℂ) *
      inner ℂ G (leray l (Sr (τ + r * u) v w (leray j F)))) (Ioi 0) ∧
    oTerm r H l j Sr G F v w τ = -∫ u in Ioi (0 : ℝ), ((Real.exp (-u * H) : ℝ) : ℂ) *
      inner ℂ G (leray l (Sr (τ + r * u) v w (leray j F))) := by
  have e : ∀ u : ℝ, ((Real.exp (-u * H) : ℝ) : ℂ) *
      inner ℂ G (leray l (Sr (τ + r * u) v w (leray j F))) = ∑ c : Sgn, ∑ e : Sgn,
        chanF H r (outerPhi c e l j) τ (core Sr0 l j c e G F v w) u := fun u => by
    rw [source_eq' hcov, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    rfl
  simp only [e]
  have h1 : ∀ c ∈ (Finset.univ : Finset Sgn), IntegrableOn (fun u => ∑ e : Sgn,
      chanF H r (outerPhi c e l j) τ (core Sr0 l j c e G F v w) u) (Ioi 0) := fun c _ =>
    integrable_finsetSum _ fun e _ => chanF_integrable hH _ _ _ _
  refine ⟨integrable_finsetSum _ h1, ?_⟩
  rw [integral_finsetSum _ h1, oTerm_eq' hcov, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun e _ => chanF_integrable hH _ _ _ _, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [chanF_integral hH]

/-- The real homogeneity of a channel. -/
lemma core_smul (Sr0 : V3 →L[ℂ] V3 →L[ℂ] Blk) (c e : Sgn) (a b d f : ℝ) (G F v w : V3) :
    core Sr0 l j c e ((a : ℂ) • G) ((b : ℂ) • F) ((d : ℂ) • v) ((f : ℂ) • w) =
      ((a * b * d * f : ℝ) : ℂ) * core Sr0 l j c e G F v w := by
  simp only [core, map_smul, smul_apply, hel_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  push_cast
  ring

/-- The real homogeneity of a source term. -/
lemma source_smul (hcov : ∀ τ v w c e y, hel c l (Sr τ v w (hel e j y)) =
      Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) • hel c l (Sr0 v w (hel e j y)))
    (a b d f : ℝ) (G F v w : V3) (τ : ℝ) :
    inner ℂ ((a : ℂ) • G) (leray l (Sr τ ((d : ℂ) • v) ((f : ℂ) • w) (leray j ((b : ℂ) • F)))) =
      ((a * b * d * f : ℝ) : ℂ) * inner ℂ G (leray l (Sr τ v w (leray j F))) := by
  rw [source_eq' hcov, source_eq' hcov, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [core_smul]
  ring

end Term

/-! ### The labels -/

lemma absk_le_absSq (k : Mode) : absk k ≤ absSq k := by
  by_cases hk : k = 0
  · subst hk
    simp [absk, absSq]
  · rw [← absk_sq k]
    have := one_le_absk hk
    nlinarith only [this]

lemma Hx_pos {x : I3} (hx : Act x) : 0 < Hx x := by
  obtain ⟨hl, -, hj⟩ := fast_labels hx.1 hx.2.1 hx.2.2
  have h1 : 1 ≤ absSq x.1 := one_le_absSq hl
  simp only [Hx, heat4]
  have h2 := absSq_nonneg (inJ₂ x)
  have h3 := absSq_nonneg x.2.1
  have h4 := absSq_nonneg x.2.2
  linarith

lemma sum_le_Hx (x : I3) : absk x.1 + absk x.2.1 + absk x.2.2 ≤ Hx x := by
  simp only [Hx, heat4]
  have h1 := absk_le_absSq x.1
  have h2 := absk_le_absSq x.2.1
  have h3 := absk_le_absSq x.2.2
  have h4 := absSq_nonneg (inJ₂ x)
  linarith

/-- The integral of the exponential. -/
lemma integral_exp_Ioi {H : ℝ} (hH : 0 < H) : ∫ u in Ioi (0 : ℝ), Real.exp (-u * H) = 1 / H := by
  have h := integral_exp_mul_complex_Ioi (a := ((-H : ℝ) : ℂ)) (by simpa using hH) 0
  have e : ∀ u : ℝ, Complex.exp (((-H : ℝ) : ℂ) * u) = ((Real.exp (-u * H) : ℝ) : ℂ) := fun u => by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp only [e] at h
  rw [integral_complex_ofReal] at h
  have e2 : -((Real.exp (-0 * H) : ℝ) : ℂ) / ((-H : ℝ) : ℂ) = ((1 / H : ℝ) : ℂ) := by
    have : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
    simp only [neg_zero, zero_mul, Real.exp_zero]
    push_cast
    field_simp
  rw [e2] at h
  exact_mod_cast h

lemma exp_Ioi_integrable {H : ℝ} (hH : 0 < H) : IntegrableOn (fun u => Real.exp (-u * H)) (Ioi 0) := by
  have h := integrableOn_exp_mul_Ioi (a := -H) (by linarith) 0
  have e : (fun u => Real.exp (-u * H)) = fun u => Real.exp (-H * u) := funext fun u => by
    congr 1
    ring
  rw [e]
  exact h

namespace Fam

variable {𝔉 : Fam} {r : ℝ} {ρ : I3 → ℝ} {K₁ K₂ : ℝ}

/-- The heat summand of a form. -/
def Ht (𝔉 : Fam) (r τ : ℝ) (f g G F : Field) (x : I3) (u : ℝ) : ℂ :=
  ((Real.exp (-u * Hx x) : ℝ) : ℂ) *
    𝔉.srcT x (G x.1) (F (inJ₂ x)) (f x.2.1) (g x.2.2) (τ + r * u)

variable {f g G F : Field} {τ : ℝ}

lemma Ht_zero (hf : PiS f = f) (hg : PiS g = g) (hF : PiF F = F) {x : I3} (hx : ¬Act x) (u : ℝ) :
    𝔉.Ht r τ f g G F x u = 0 ∧
      𝔉.T r x (G x.1) (F (inJ₂ x)) (f x.2.1) (g x.2.2) τ = 0 := by
  by_cases ha : x.2.1 2 = 0
  swap
  · have h0 : f x.2.1 = 0 := slow_zero hf ha
    refine ⟨?_, ?_⟩
    · simp only [Ht, h0]
      rw [srcT_zero_l, mul_zero]
    · rw [h0]
      exact T_zero_l _ _ _ _ _ _
  by_cases hb : x.2.2 2 = 0
  swap
  · have h0 : g x.2.2 = 0 := slow_zero hg hb
    refine ⟨?_, ?_⟩
    · simp only [Ht, h0]
      rw [srcT_zero_r, mul_zero]
    · rw [h0]
      exact T_zero_r _ _ _ _ _ _
  have hj : inJ₂ x 2 = 0 := by
    by_contra hj
    exact hx ⟨ha, hb, hj⟩
  have h0 : F (inJ₂ x) = 0 := fast_zero hF hj
  refine ⟨?_, ?_⟩
  · simp only [Ht, h0]
    rw [srcT_zero_F, mul_zero]
  · rw [h0]
    exact T_zero_F _ _ _ _ _ _

lemma Ht_integrable (hf : PiS f = f) (hg : PiS g = g) (hF : PiF F = F) (x : I3) :
    IntegrableOn (𝔉.Ht r τ f g G F x) (Ioi 0) ∧
      𝔉.T r x (G x.1) (F (inJ₂ x)) (f x.2.1) (g x.2.2) τ =
        -∫ u in Ioi (0 : ℝ), 𝔉.Ht r τ f g G F x u := by
  by_cases hx : Act x
  · exact oTerm_heat (Hx_pos hx) (𝔉.cov x hx.1 hx.2.1) _ _ _ _ τ
  · have h0 : 𝔉.Ht r τ f g G F x = fun _ => 0 := funext fun u => (Ht_zero hf hg hF hx u).1
    rw [h0, (Ht_zero hf hg hF hx 0).2]
    simp

/-- The integral of the norm of a heat summand. -/
lemma Ht_norm_le (hB : 𝔉.Bd r ρ K₁ K₂) (hf : PiS f = f) (hg : PiS g = g) (hF : PiF F = F) (x : I3) :
    ∫ u in Ioi (0 : ℝ), ‖𝔉.Ht r τ f g G F x u‖ ≤
      K₂ * (Phi₂ (nrm G) (nrm F) (nrm f) (nrm g) x * E2 x) := by
  have hR : 0 ≤ K₂ * (Phi₂ (nrm G) (nrm F) (nrm f) (nrm g) x * E2 x) :=
    mul_nonneg hB.K₂0 (Phi₂_E2_nonneg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) x)
  by_cases hx : Act x
  swap
  · have h0 : ∀ u, ‖𝔉.Ht r τ f g G F x u‖ = 0 := fun u => by
      rw [(Ht_zero hf hg hF hx u).1, norm_zero]
    simp only [h0, integral_zero]
    exact hR
  have hH := Hx_pos hx
  set S := K₂ * (‖G x.1‖ * ‖F (inJ₂ x)‖ * (‖f x.2.1‖ * ‖g x.2.2‖) *
    (absk x.1 + absk x.2.1 + absk x.2.2) * E2 x) with hS
  have hle : ∀ u, ‖𝔉.Ht r τ f g G F x u‖ ≤ Real.exp (-u * Hx x) * S := fun u => by
    rw [Ht, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (norm_srcT_le hB hx) (Real.exp_pos _).le
  have hi : IntegrableOn (fun u => Real.exp (-u * Hx x) * S) (Ioi 0) :=
    (exp_Ioi_integrable hH).mul_const S
  have h1 : ∫ u in Ioi (0 : ℝ), ‖𝔉.Ht r τ f g G F x u‖ ≤
      ∫ u in Ioi (0 : ℝ), Real.exp (-u * Hx x) * S :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hi
      (Filter.Eventually.of_forall hle)
  refine h1.trans ?_
  rw [integral_mul_const, integral_exp_Ioi hH]
  have hE := E2_nonneg x
  have hK := hB.K₂0
  have hP : 0 ≤ ‖G x.1‖ * ‖F (inJ₂ x)‖ * (‖f x.2.1‖ * ‖g x.2.2‖) * E2 x := by positivity
  have hsum := sum_le_Hx x
  have e : 1 / Hx x * S = K₂ * (‖G x.1‖ * ‖F (inJ₂ x)‖ * (‖f x.2.1‖ * ‖g x.2.2‖) * E2 x) *
      ((absk x.1 + absk x.2.1 + absk x.2.2) / Hx x) := by
    simp only [hS]
    ring
  rw [e]
  have h2 : (absk x.1 + absk x.2.1 + absk x.2.2) / Hx x ≤ 1 := (div_le_one hH).2 hsum
  calc _ ≤ K₂ * (‖G x.1‖ * ‖F (inJ₂ x)‖ * (‖f x.2.1‖ * ‖g x.2.2‖) * E2 x) * 1 :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hK hP)
    _ = _ := by
        simp only [Phi₂, nrm]
        ring

/-- The heat summand at a label is the term of the source on the evolved fields. -/
lemma Ht_eq (hf : PiS f = f) (hg : PiS g = g) (hF : PiF F = F) (x : I3) (u : ℝ) :
    𝔉.Ht r τ f g G F x u = 𝔉.srcT x (heatF u G x.1) (heatF u F (inJ₂ x)) (heatF u f x.2.1)
      (heatF u g x.2.2) (τ + r * u) := by
  by_cases hx : Act x
  · have h := source_smul (τ := τ + r * u) (Sr := 𝔉.Sr x) (𝔉.cov x hx.1 hx.2.1)
      (Real.exp (-u * absSq x.1)) (Real.exp (-u * absSq (inJ₂ x)))
      (Real.exp (-u * absSq x.2.1)) (Real.exp (-u * absSq x.2.2))
      (G x.1) (F (inJ₂ x)) (f x.2.1) (g x.2.2)
    simp only [Ht, heatF, srcT]
    rw [h]
    congr 2
    simp only [← Real.exp_add, Hx, heat4]
    congr 1
    ring
  · rw [(Ht_zero hf hg hF hx u).1]
    by_cases ha : x.2.1 2 = 0
    swap
    · rw [slow_zero (PiS_heatF hf) ha]
      exact (srcT_zero_l _ _ _ _ _).symm
    by_cases hb : x.2.2 2 = 0
    swap
    · rw [slow_zero (PiS_heatF hg) hb]
      exact (srcT_zero_r _ _ _ _ _).symm
    have hj : inJ₂ x 2 = 0 := by
      by_contra hj
      exact hx ⟨ha, hb, hj⟩
    rw [fast_zero (PiF_heatF hF) hj]
    exact (srcT_zero_F _ _ _ _ _).symm

/-- **The heat form of a form.** -/
theorem form_heat (hB : 𝔉.Bd r ρ K₁ K₂) (hf : MZ 2 f) (hf' : PiS f = f) (hg : MZ 2 g)
    (hg' : PiS g = g) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) (τ : ℝ) :
    𝔉.form r τ f g G F = -∫ u in Ioi (0 : ℝ),
      𝔉.src (τ + r * u) (heatF u f) (heatF u g) (heatF u G) (heatF u F) := by
  have hP := pos2_E2 (l2B_nrm hG) (l2B_nrm hF) (l1B_nrm hf.inH) (l1B_nrm hg.inH) (l2B_up hf.inH)
    (l2B_up hg.inH)
  have hmaj : Summable fun x => K₂ * (Phi₂ (nrm G) (nrm F) (nrm f) (nrm g) x * E2 x) :=
    Summable.mul_left _ hP.1
  have hsum : Summable fun x => ∫ u in Ioi (0 : ℝ), ‖𝔉.Ht r τ f g G F x u‖ :=
    Summable.of_nonneg_of_le (fun x => integral_nonneg fun _ => norm_nonneg _)
      (fun x => Ht_norm_le hB hf' hg' hF' x) hmaj
  have hI : ∀ x, Integrable (𝔉.Ht r τ f g G F x) (volume.restrict (Ioi (0 : ℝ))) := fun x =>
    (Ht_integrable hf' hg' hF' x).1
  have hS : HasSum (fun x => ∫ u in Ioi (0 : ℝ), 𝔉.Ht r τ f g G F x u)
      (∫ u in Ioi (0 : ℝ), ∑' x, 𝔉.Ht r τ f g G F x u) :=
    hasSum_integral_of_summable_integral_norm hI hsum
  have e1 : 𝔉.form r τ f g G F = -∑' x, ∫ u in Ioi (0 : ℝ), 𝔉.Ht r τ f g G F x u := by
    rw [← tsum_neg]
    exact tsum_congr fun x => (Ht_integrable hf' hg' hF' x).2
  rw [e1, hS.tsum_eq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact tsum_congr fun x => Ht_eq hf' hg' hF' x u

end Fam

end OVNS.Quant.Metric

end
