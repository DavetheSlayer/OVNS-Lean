import OddViscousNS.Quant.Joint.Metric.DiffForm

/-!
# The differentiated group: the second slot of `X₂`, and `Z` (step J5, nodes N5, N7)

`X2diff_le'`: Hermiticity on the mask gives the second slot of `D_S X₂`.

Body 42, `D_S Z[h]`.  Comparable exteriors: `q⁻¹/J`, the band proof, `q⁻¹ f₀ W`.  Separated exteriors:
`|d₂| ≳ q F₀`: one `F₀` for the larger exterior, and the bracket `F₀/m² ≤ 1/m + (P_h + P_S)/m²`,
`m` the smaller exterior: LOCAL525's three weights, `q⁻² f₁ [a + W + ε^{−1/2} a_ε] ‖z‖ c_F`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {D ε : ℝ} {α β f₁ f₂ : Mode → ℝ} {A B U₁ U₂ : ℝ}

/-! ### Hermiticity on a mask -/

/-- `X₂` is Hermitian on a mask. -/
theorem X2Form_conjM (s : ℕ) (r τ : ℝ) {f g : Field} (hf : IsReal f) (hg : IsReal g) (μ : I3 → ℂ)
    (G F : Field) :
    X2Form μ s r τ f g G F = conj (X2Form (fun x => conj (μ (revE x))) s r τ g f F G) := by
  simp only [X2Form]
  rw [Complex.conj_tsum, ← revE.tsum_eq]
  refine tsum_congr fun x => ?_
  have e1 : (revE x).1 = inJ₂ x := rfl
  have e2 : (revE x).2.1 = -x.2.2 := rfl
  have e3 : (revE x).2.2 = -x.2.1 := rfl
  rw [e1, e2, e3, map_mul, Complex.conj_conj, inner_conj_symm]
  have e4 : inJ₂ x - -x.2.2 - -x.2.1 = x.1 := by
    simp only [inJ₂]
    abel
  rw [e4]
  have e5 : inJ₂ x = x.1 - x.2.1 - x.2.2 := rfl
  rw [e5, ← adjoint_X2b s r τ hg hf, ContinuousLinearMap.adjoint_inner_right]

/-- **`D_S X₂` off the high tail**, the direction in the second slot. -/
theorem X2diff_le' {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hD : 0 ≤ D) {h S G F : Field}
    (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF1 : Summable fun k => ‖zOf 1 F k‖ ^ 2)
    (hh2 : Summable fun k => ‖h k‖ ^ 2) (hh : InH 1 h) (hh' : PiS h = h) (hh0 : h 0 = 0)
    (hhr : IsReal h) (hS : MZ 2 S) (hS' : PiS S = S) (hSr : IsReal S) (hG' : PiF G = G)
    {μ : I3 → ℂ} (hμ1 : ∀ x, ‖μ x‖ ≤ 1)
    (hμ0 : ∀ x : I3, D < absk (x.1 - x.2.1) → 4 * absk x.1 ≤ absk (x.1 - x.2.1) →
      4 * absk (x.1 - x.2.1 - x.2.2) ≤ absk (x.1 - x.2.1) → μ x = 0) :
    ‖X2Form μ 2 r τ S h G F‖ ≤ diffB D |r| (l2n h) (hnorm 1 h) (wiener S) (hnorm 2 S) (l2n F)
      (l2n G) (l2n (zOf 1 F)) (l2n (zOf 1 G)) := by
  rw [X2Form_conjM 2 r τ hSr hhr, Complex.norm_conj]
  refine X2diff_le hr τ hD hF hF1 hG hG1 hh2 hh hh' hh0 hS hS' hG' (fun x => ?_) fun x h1 h2 h3 => ?_
  · simpa using hμ1 (revE x)
  · have e : (revE x).1 - (revE x).2.1 = x.1 - x.2.1 := by
      simp only [revE, Equiv.coe_fn_mk, inJ₂]
      abel
    have e2 : x.1 - x.2.1 - (revE x).2.2 = x.1 := by
      simp only [revE, Equiv.coe_fn_mk]
      abel
    have e3 : (revE x).1 = x.1 - x.2.1 - x.2.2 := rfl
    have h4 := hμ0 (revE x) (by rw [e]; exact h1) (by rw [e, e3]; exact h3) (by rw [e, e2]; exact h2)
    simp [h4]

/-! ### The block of `Z` -/

/-- The kernel of `Z` at separated exteriors. -/
def kZ (x : I3) : ℝ :=
  absk x.1 * ((absk (inJ₂ x))⁻¹ + (absk x.2.1 + absk x.2.2) * (absk (inJ₂ x))⁻¹ ^ 2) +
    absk (inJ₂ x) * ((absk x.1)⁻¹ + (absk x.2.1 + absk x.2.2) * (absk x.1)⁻¹ ^ 2)

lemma kZ_nonneg (x : I3) : 0 ≤ kZ x := by
  have h1 := absk_nonneg x.1
  have h2 := absk_nonneg (inJ₂ x)
  have h3 := absk_nonneg x.2.1
  have h4 := absk_nonneg x.2.2
  have h5 := inv_nonneg.2 h1
  have h6 := inv_nonneg.2 h2
  unfold kZ
  positivity

/-- The arithmetic of a separated exterior. -/
lemma zsep_arith {L J P S : ℝ} (hL : 0 < L) (hJ : 0 < J) (h1 : 2 * J ≤ L) (hP : P ≤ L + J)
    (hS0 : 0 ≤ S) (hLS : L ≤ J + S) :
    P / L * (L ^ 2 / J ^ 2 + J ^ 2 / L ^ 2) ≤ 3 * (L * (J⁻¹ + S * J⁻¹ ^ 2)) := by
  have hP2 : P / L ≤ 3 / 2 := by
    rw [div_le_iff₀ hL]
    linarith
  have e1 : J ^ 2 / L ^ 2 ≤ L ^ 2 / J ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : J ^ 2 ≤ L ^ 2 := by nlinarith only [h1, hL, hJ]
    exact mul_le_mul this this (by positivity) (by positivity)
  have hE : 0 ≤ L ^ 2 / J ^ 2 := by positivity
  have e2 : L ^ 2 / J ^ 2 = L * (L * J⁻¹ ^ 2) := by
    field_simp
  have e3 : L * J⁻¹ ^ 2 ≤ J⁻¹ + S * J⁻¹ ^ 2 := by
    have e4 : J⁻¹ = J * J⁻¹ ^ 2 := by
      field_simp
    calc L * J⁻¹ ^ 2 ≤ (J + S) * J⁻¹ ^ 2 := by gcongr
      _ = J * J⁻¹ ^ 2 + S * J⁻¹ ^ 2 := by ring
      _ = _ := by rw [← e4]
  have hB : 0 ≤ L * (J⁻¹ + S * J⁻¹ ^ 2) := by positivity
  calc P / L * (L ^ 2 / J ^ 2 + J ^ 2 / L ^ 2) ≤ 3 / 2 * (2 * (L ^ 2 / J ^ 2)) := by
        have h3 : 0 ≤ L ^ 2 / J ^ 2 + J ^ 2 / L ^ 2 := by positivity
        refine mul_le_mul hP2 (by linarith) h3 (by norm_num)
    _ = 3 * (L * (L * J⁻¹ ^ 2)) := by rw [e2]; ring
    _ ≤ _ := by gcongr

/-- **The block of `Z`.** -/
theorem norm_Z_diff {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖Zb 2 r τ f g l a b‖ ≤ (2 ^ 16 / |r| * kapC l (l - a - b) + 2 ^ 14 / |r| ^ 2 * kZ (l, a, b)) *
      (‖f a‖ * ‖g b‖) := by
  obtain ⟨hl0, -, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hJ : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hfg : 0 ≤ ‖f a‖ * ‖g b‖ := by positivity
  have hk0 := kapC_nonneg l (l - a - b)
  have hkZ := kZ_nonneg (l, a, b)
  have hab : a + b = l - (l - a - b) := by abel
  have hPle : absk (a + b) ≤ absk l + absk (l - a - b) := by
    rw [hab]
    exact absk_sub_le _ _
  have hH0 := heat4_pos (l := l) hj0 a b
  have hHL : absk (l - a - b) ^ 2 ≤ heat4 l (l - a - b) a b := by
    rw [heat4_eq]
    nlinarith only [sq_nonneg (absk a), sq_nonneg (absk b), sq_nonneg (absk l)]
  obtain ⟨-, -, p3, p4⟩ := two_leaf_paths l a b
  have hA0 := absk_nonneg a
  have hB0 := absk_nonneg b
  have ekz : kZ (l, a, b) = absk l * ((absk (l - a - b))⁻¹ +
      (absk a + absk b) * (absk (l - a - b))⁻¹ ^ 2) +
      absk (l - a - b) * ((absk l)⁻¹ + (absk a + absk b) * (absk l)⁻¹ ^ 2) := rfl
  set L := absk l with hLd
  set J := absk (l - a - b) with hJd
  set P := absk (a + b) with hPd
  set S := absk a + absk b with hSd
  have hS0 : 0 ≤ S := by positivity
  have t1 : 0 ≤ 2 ^ 16 / |r| * kapC l (l - a - b) := by positivity
  have t2 : 0 ≤ 2 ^ 14 / |r| ^ 2 * kZ (l, a, b) := by positivity
  by_cases hc : L ≤ 2 * J ∧ J ≤ 2 * L
  · have hN := norm_Zb_two_le hr τ f g ha hb hj
    rw [← absk_sq l, ← absk_sq (l - a - b)] at hN
    have hk : kapC l (l - a - b) = J⁻¹ := by
      simp only [kapC, hc.1, hc.2, and_self, ite_true, ← hLd, ← hJd]
    have e1 : L ^ 2 / J ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hc.1, hL, hJ]
    have e2 : J ^ 2 / L ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hc.2, hL, hJ]
    have e3 : P / heat4 l (l - a - b) a b ≤ 3 * J⁻¹ := by
      rw [div_le_iff₀ hH0]
      have h3 : P ≤ 3 * J := by linarith [hc.1]
      calc P ≤ 3 * J := h3
        _ = 3 * J ^ 2 * J⁻¹ := by field_simp
        _ ≤ 3 * heat4 l (l - a - b) a b * J⁻¹ := by gcongr
        _ = _ := by ring
    have hi : 0 ≤ J⁻¹ := (inv_pos.2 hJ).le
    have h4 : 1408 / |r| * (P / heat4 l (l - a - b) a b) * (L ^ 2 / J ^ 2 + J ^ 2 / L ^ 2) ≤
        2 ^ 16 / |r| * kapC l (l - a - b) := by
      rw [hk]
      have hE : 0 ≤ L ^ 2 / J ^ 2 + J ^ 2 / L ^ 2 := by positivity
      calc _ ≤ 1408 / |r| * (3 * J⁻¹) * 8 :=
            mul_le_mul (mul_le_mul_of_nonneg_left e3 (by positivity)) (by linarith) hE
              (by positivity)
        _ = 33792 / |r| * J⁻¹ := by ring
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ hi
            exact div_le_div_of_nonneg_right (by norm_num) hq.le
    calc _ ≤ _ := hN
      _ = 1408 / |r| * (P / heat4 l (l - a - b) a b) * (L ^ 2 / J ^ 2 + J ^ 2 / L ^ 2) *
          (‖f a‖ * ‖g b‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hfg
  · have hN : ∀ F : ℝ, 0 < F → F / 2 ≤ |J - L| → ‖Zb 2 r τ f g l a b‖ ≤
        2816 / |r| ^ 2 * (P / F) * (‖f a‖ * ‖g b‖) * (L ^ 2 / J ^ 2 + J ^ 2 / L ^ 2) := by
      intro F hF hsep
      have h1 := norm_Z_sep hr τ f g ha hb hj hF hsep
      rw [← absk_sq l, ← absk_sq (l - a - b)] at h1
      refine h1.trans (le_of_eq ?_)
      ring
    have hE0 : 0 ≤ L ^ 2 / J ^ 2 + J ^ 2 / L ^ 2 := by positivity
    have hK1 : 0 ≤ L * (J⁻¹ + S * J⁻¹ ^ 2) := by positivity
    have hK2 : 0 ≤ J * (L⁻¹ + S * L⁻¹ ^ 2) := by positivity
    have hZ : (‖Zb 2 r τ f g l a b‖ : ℝ) ≤ 2816 / |r| ^ 2 * (3 * (L * (J⁻¹ + S * J⁻¹ ^ 2) +
        J * (L⁻¹ + S * L⁻¹ ^ 2))) * (‖f a‖ * ‖g b‖) := by
      rcases not_and_or.1 hc with h1 | h1
      · rw [not_le] at h1
        have hA := hN L hL (by
          rw [abs_sub_comm]
          exact le_trans (by linarith) (le_abs_self _))
        have hB := zsep_arith hL hJ h1.le hPle hS0 (by simpa [hSd, add_assoc] using p3)
        calc _ ≤ _ := hA
          _ = 2816 / |r| ^ 2 * (P / L * (L ^ 2 / J ^ 2 + J ^ 2 / L ^ 2)) * (‖f a‖ * ‖g b‖) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hfg
      · rw [not_le] at h1
        have hA := hN J hJ (le_trans (by linarith) (le_abs_self _))
        have hB := zsep_arith (P := P) hJ hL h1.le (by linarith) hS0
          (by simpa [hSd, add_assoc] using p4)
        have e : L ^ 2 / J ^ 2 + J ^ 2 / L ^ 2 = J ^ 2 / L ^ 2 + L ^ 2 / J ^ 2 := add_comm _ _
        calc _ ≤ _ := hA
          _ = 2816 / |r| ^ 2 * (P / J * (J ^ 2 / L ^ 2 + L ^ 2 / J ^ 2)) * (‖f a‖ * ‖g b‖) := by
              rw [e]
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hfg
    refine hZ.trans (mul_le_mul_of_nonneg_right ?_ hfg)
    have e : 2816 / |r| ^ 2 * (3 * (L * (J⁻¹ + S * J⁻¹ ^ 2) + J * (L⁻¹ + S * L⁻¹ ^ 2))) =
        2816 * 3 / |r| ^ 2 * kZ (l, a, b) := by
      rw [ekz]
      ring
    rw [e]
    have h5 : 2816 * 3 / |r| ^ 2 * kZ (l, a, b) ≤ 2 ^ 14 / |r| ^ 2 * kZ (l, a, b) := by
      refine mul_le_mul_of_nonneg_right ?_ hkZ
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith

/-! ### The form of `Z` -/

/-- The transpose of `pos2_sub`. -/
lemma SlowHs.refl (h : SlowHs ε f₁ U₁) : SlowHs ε (Metric.refl f₁) U₁ := by
  refine ⟨fun p => h.nn _, fun p hp => h.slow _ ?_, ?_, ?_⟩
  · simpa using hp
  · simpa [Metric.refl] using h.mean
  · have := h.grad.refl
    refine L2B.mono (A := U₁) ?_ le_rfl
    convert this using 2 with p
    simp only [Metric.refl, absk_neg]

theorem pos2_sub' (hε : 0 < ε) (hα : L2B α A) (hβ : L2B β B) (h1 : SlowH1 f₁ U₁)
    (h2 : SlowHs ε f₂ U₂) :
    SB (Phi₂ (in2 α) β f₁ fun p => absk p * f₂ p)
      (Real.sqrt (34 * (9 + 4 / ε)) * (A * B * (U₁ * U₂))) := by
  have h3 := pos2_sub hε hβ hα h1.refl h2.refl
  have h4 : SB (Phi₂ β (in2 α) (fun p => absk p * Metric.refl f₂ p) (Metric.refl f₁)) _ :=
    SB.equiv swapL h3 fun x => Phi₂_swapL _ _ _ _ _
  refine (SB.equiv revE h4 fun x => ?_).mono_bd (le_of_eq (by ring))
  rw [Phi₂_rev]
  congr 1
  funext p
  simp only [Metric.refl, absk_neg]

/-- The majorant of `D_S Z`. -/
def PsiZ (q : ℝ) (G F f g : Field) (x : I3) : ℝ :=
  2 ^ 16 / q * (Phi₂ (nrm G) (nrm F) (nrm f) (nrm g) x * kapC x.1 (inJ₂ x)) +
  2 ^ 14 / q ^ 2 * (Phi₂ (gr G) (in1 (nrm F)) (nrm f) (nrm g) x +
    Phi₂ (gr G) (in2 (nrm F)) (gr f) (nrm g) x + Phi₂ (gr G) (in2 (nrm F)) (nrm f) (gr g) x +
    Phi₂ (in1 (nrm G)) (gr F) (nrm f) (nrm g) x + Phi₂ (in2 (nrm G)) (gr F) (gr f) (nrm g) x +
    Phi₂ (in2 (nrm G)) (gr F) (nrm f) (gr g) x)

/-- The bound of the form of `Z`. -/
def zB (ε q f₀ f₁ W a₀ aε A B A₁ B₁ : ℝ) : ℝ :=
  2 ^ 16 / q * (Real.sqrt 33 * (A * B * (f₀ * W))) +
  2 ^ 14 / q ^ 2 * ((A₁ * B + A * B₁) * (30 * (f₁ * a₀) + c4 * (f₁ * W) +
    Real.sqrt (34 * (9 + 4 / ε)) * (f₁ * aε)))

/-- The nonnegativity of the majorant. -/
lemma PsiZ_nonneg {q : ℝ} (hq : 0 < q) (G F f g : Field) (x : I3) : 0 ≤ PsiZ q G F f g x := by
  have n1 : ∀ u : Field, ∀ k, 0 ≤ nrm u k := fun u k => norm_nonneg _
  have n3 : ∀ u : Field, ∀ k, 0 ≤ in2 (nrm u) k := fun u k =>
    div_nonneg (norm_nonneg _) (absSq_nonneg k)
  have n5 : ∀ u : Field, ∀ k, 0 ≤ in1 (nrm u) k := fun u k =>
    div_nonneg (norm_nonneg _) (absk_nonneg k)
  have n4 := gr_nonneg
  have t := fun (α β f₁ f₂ : Mode → ℝ) (a b c d) =>
    Phi₂_nonneg (α := α) (β := β) (f₁ := f₁) (f₂ := f₂) a b c d x
  have h1 := t _ _ _ _ (n1 G) (n1 F) (n1 f) (n1 g)
  have h2 := t _ _ _ _ (n4 G) (n5 F) (n1 f) (n1 g)
  have h3 := t _ _ _ _ (n4 G) (n3 F) (n4 f) (n1 g)
  have h4 := t _ _ _ _ (n4 G) (n3 F) (n1 f) (n4 g)
  have h5 := t _ _ _ _ (n5 G) (n4 F) (n1 f) (n1 g)
  have h6 := t _ _ _ _ (n3 G) (n4 F) (n4 f) (n1 g)
  have h7 := t _ _ _ _ (n3 G) (n4 F) (n1 f) (n4 g)
  have h8 := kapC_nonneg x.1 (inJ₂ x)
  unfold PsiZ
  positivity

/-- A term of `D_S Z`. -/
lemma Zdiff_term {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {f g G F : Field} (hf' : PiS f = f)
    (hg' : PiS g = g) (hF' : PiF F = F) {μ : I3 → ℂ} (hμ1 : ∀ x, ‖μ x‖ ≤ 1) (x : I3) :
    ‖μ x * inner ℂ (G x.1) (Zb 2 r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))‖ ≤
      PsiZ |r| G F f g x := by
  have e0 : x.1 - x.2.1 - x.2.2 = inJ₂ x := rfl
  rw [e0]
  have hq : 0 < |r| := abs_pos.2 hr
  have hR := PsiZ_nonneg hq G F f g x
  by_cases ha : x.2.1 2 = 0
  swap
  · rw [Zb_eq_zero (Or.inl (slow_zero hf' ha))]
    simpa using hR
  by_cases hb : x.2.2 2 = 0
  swap
  · rw [Zb_eq_zero (Or.inr (slow_zero hg' hb))]
    simpa using hR
  by_cases hj : inJ₂ x 2 = 0
  · rw [fast_zero hF' hj, map_zero, inner_zero_right, mul_zero, norm_zero]
    exact hR
  have hj' : (x.1 - x.2.1 - x.2.2) 2 ≠ 0 := hj
  have hB := norm_Z_diff hr τ f g ha hb hj'
  have h1 := norm_inner_apply_le (G x.1) (F (inJ₂ x)) (Zb 2 r τ f g x.1 x.2.1 x.2.2)
  have hP0 : 0 ≤ ‖G x.1‖ * ‖F (inJ₂ x)‖ := by positivity
  rw [norm_mul]
  refine (mul_le_mul (hμ1 x) (h1.trans (mul_le_mul_of_nonneg_left hB hP0))
    (norm_nonneg _) zero_le_one).trans (le_of_eq ?_)
  have el : (absk x.1 : ℝ) ^ 2 = absSq x.1 := absk_sq _
  have ej : (absk (x.1 - x.2.1 - x.2.2) : ℝ) ^ 2 = absSq (x.1 - x.2.1 - x.2.2) := absk_sq _
  simp only [PsiZ, Phi₂, in1, in2, kZ, gr, nrm, inJ₂]
  rw [← el, ← ej]
  ring

/-- **The sum of the majorant of `D_S Z`.** -/
lemma sb_PsiZ {q : ℝ} (hq : 0 < q) (hε : 0 < ε) {G F h S : Field}
    (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF1 : Summable fun k => ‖zOf 1 F k‖ ^ 2)
    (hh2 : Summable fun k => ‖h k‖ ^ 2) (hh : MZ 1 h) (hh' : PiS h = h) (hS : MZ 2 S)
    (hSε : MZ (1 + ε) S) (hS' : PiS S = S) :
    SB (PsiZ q G F h S) (zB ε q (l2n h) (hnorm 1 h) (wiener S) (hnorm 1 S) (hnorm (1 + ε) S) (l2n G)
      (l2n F) (l2n (zOf 1 G)) (l2n (zOf 1 F))) := by
  have hα := l2B_nrm hG
  have hβ := l2B_nrm hF
  have gα := l2B_half hG1
  have gβ := l2B_half hF1
  have wS := l1B_nrm hS.inH
  have s1 : SlowH1 (nrm h) (hnorm 1 h) := by
    refine ⟨fun _ => norm_nonneg _, fun p hp => ?_, ?_, l2B_gr hh.inH⟩
    · simp only [nrm]
      rw [slow_zero hh' hp, norm_zero]
    · simp only [nrm]
      rw [hh.mean, norm_zero]
  have s2 := slowH1_nrm hS hS'
  have sε := slowHs_nrm hSε hS'
  have t1 := sb_kap₁ hα hβ (l2B_nrm hh2) wS fun p hp => by
    simp [nrm, slow_zero hh' hp]
  have t2 := pos2_base gα hβ s1 s2
  have t3 := pos2_II' gα hβ.in2 (l2B_gr hh.inH) wS
  have t4 := pos2_sub hε gα hβ s1 sε
  have t5 := pos2_base' hα gβ s1 s2
  have t6 := pos2_II hα.in2 gβ (l2B_gr hh.inH) wS
  have t7 := pos2_sub' hε hα gβ s1 sε
  have h1 := t1.const_mul (by positivity : 0 ≤ 2 ^ 16 / q)
  have h2 := (((((t2.add t3).add t4).add t5).add t6).add t7).const_mul
    (by positivity : 0 ≤ 2 ^ 14 / q ^ 2)
  refine (h1.add h2).mono_bd (le_of_eq ?_)
  simp only [zB]
  ring

lemma PsiZ_swap (q : ℝ) (G F f g : Field) (x : I3) :
    PsiZ q G F f g x = PsiZ q G F g f (swapL x) := by
  simp only [PsiZ, Phi₂_swapL _ _ _ _ x, inJ₂_swapL]
  have e : (swapL x).1 = x.1 := rfl
  rw [e]
  ring

/-- **`D_S Z`**, the direction in the first slot. -/
theorem Zdiff_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hε : 0 < ε) {h S G F : Field}
    (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF1 : Summable fun k => ‖zOf 1 F k‖ ^ 2)
    (hh2 : Summable fun k => ‖h k‖ ^ 2) (hh : MZ 1 h) (hh' : PiS h = h) (hS : MZ 2 S)
    (hSε : MZ (1 + ε) S) (hS' : PiS S = S) (hF' : PiF F = F) {μ : I3 → ℂ}
    (hμ1 : ∀ x, ‖μ x‖ ≤ 1) :
    ‖ZForm μ 2 r τ h S G F‖ ≤ zB ε |r| (l2n h) (hnorm 1 h) (wiener S) (hnorm 1 S) (hnorm (1 + ε) S)
      (l2n G) (l2n F) (l2n (zOf 1 G)) (l2n (zOf 1 F)) := by
  have hs := sb_PsiZ (abs_pos.2 hr) hε hG hG1 hF hF1 hh2 hh hh' hS hSε hS'
  refine (form_le hs fun x => ?_).2
  exact Zdiff_term hr τ hh' hS' hF' hμ1 x

/-- **`D_S Z`**, the direction in the second slot. -/
theorem Zdiff_le' {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hε : 0 < ε) {h S G F : Field}
    (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF1 : Summable fun k => ‖zOf 1 F k‖ ^ 2)
    (hh2 : Summable fun k => ‖h k‖ ^ 2) (hh : MZ 1 h) (hh' : PiS h = h) (hS : MZ 2 S)
    (hSε : MZ (1 + ε) S) (hS' : PiS S = S) (hF' : PiF F = F) {μ : I3 → ℂ}
    (hμ1 : ∀ x, ‖μ x‖ ≤ 1) :
    ‖ZForm μ 2 r τ S h G F‖ ≤ zB ε |r| (l2n h) (hnorm 1 h) (wiener S) (hnorm 1 S) (hnorm (1 + ε) S)
      (l2n G) (l2n F) (l2n (zOf 1 G)) (l2n (zOf 1 F)) := by
  have hs := sb_PsiZ (abs_pos.2 hr) hε hG hG1 hF hF1 hh2 hh hh' hS hSε hS'
  have hs' := SB.equiv swapL hs (PsiZ_swap |r| G F S h)
  refine (form_le hs' fun x => ?_).2
  exact Zdiff_term hr τ hS' hh' hF' hμ1 x

end OVNS.Quant.Metric

end
