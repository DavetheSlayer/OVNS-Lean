import OddViscousNS.Quant.Joint.Metric.LowSum

/-!
# The output half of `X₂` (step J5, node N7)

Body 41 (LOCAL655): on the mask `P₁, P₂ ≤ D`,
`‖A^{1/2} X_{2,lo}‖ ≲ q⁻¹ (W² + (1 + ln D) a²) + q⁻² D b²`, at both weights.

The block bound is `norm_X2b_half`, by the three sectors of Body 41:
* separated exteriors: the exterior phase `|δ_lj| ≥ F₀/2` replaces the heat;
* comparable exteriors, `M < 4 F₀`: everything is bounded;
* comparable exteriors, `M ≥ 4 F₀`: the signed block `norm_X2b_signed_le`; its phase part is
  `P₁ P₂/(L J)`, its heat part `D E₂`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-- The exterior phase, at separated exteriors. -/
lemma lam_sep {u v : Mode} (h2 : u 2 = v 2) (hn : v 2 ≠ 0) (c e : Sgn) :
    |absk v - absk u| ≤ |lam e v - lam c u| := by
  have hs : lam e v - lam c u = (v 2 : ℝ) * (sg e * absk v - sg c * absk u) := by
    simp only [lam, h2]
    ring
  have hu := absk_nonneg u
  have hv := absk_nonneg v
  have h1 : (1 : ℝ) ≤ |((v 2 : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |v 2| := Int.one_le_abs hn
    exact_mod_cast this
  have h3 : |absk v - absk u| ≤ |sg e * absk v - sg c * absk u| := by
    have hs1 : ∀ c : Sgn, sg c = 1 ∨ sg c = -1 := fun c => by
      cases c <;> simp [sg]
    have hsum : |absk v - absk u| ≤ absk v + absk u :=
      abs_le.2 ⟨by linarith, by linarith⟩
    rcases hs1 e with he | he <;> rcases hs1 c with hc | hc <;> rw [he, hc]
    · rw [one_mul, one_mul]
    · have e1 : 1 * absk v - -1 * absk u = absk v + absk u := by ring
      rw [e1]
      exact hsum.trans (le_abs_self _)
    · have e1 : -1 * absk v - 1 * absk u = -(absk v + absk u) := by ring
      rw [e1, abs_neg]
      exact hsum.trans (le_abs_self _)
    · have e1 : -1 * absk v - -1 * absk u = -(absk v - absk u) := by ring
      rw [e1, abs_neg]
  rw [hs, abs_mul]
  calc _ ≤ 1 * |sg e * absk v - sg c * absk u| := by rw [one_mul]; exact h3
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-- The outer inverse, at separated exteriors. -/
lemma norm_outerInv_sep {H d : ℝ} {r : ℝ} (hr : r ≠ 0) {l j : Mode} (h2 : l 2 = j 2)
    (hn : j 2 ≠ 0) (hd : 0 < d) (hsep : d ≤ |absk j - absk l|) (T : V3 →L[ℂ] V3) :
    ‖outerInv r H l j T‖ ≤ 4 / (|r| * d) * ‖T‖ := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hterm : ∀ c e, ‖resolv (-1) H (r * outerPhi c e l j) • (helL c l ∘L T ∘L helL e j)‖ ≤
      1 / (|r| * d) * ‖T‖ := fun c e => by
    rw [norm_smul]
    have hphi : d ≤ |outerPhi c e l j| := hsep.trans (lam_sep h2 hn c e)
    have hz : r * outerPhi c e l j ≠ 0 :=
      mul_ne_zero hr (abs_pos.1 (hd.trans_le hphi))
    have h1 : ‖resolv (-1) H (r * outerPhi c e l j)‖ ≤ 1 / (|r| * d) := by
      refine (norm_resolv_le_abs H hz).trans ?_
      rw [abs_mul]
      exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hphi hr0.le)
    have h3 : ‖helL c l ∘L T ∘L helL e j‖ ≤ ‖T‖ := by
      calc _ ≤ ‖helL c l‖ * ‖T ∘L helL e j‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * (‖T‖ * 1) := by
            refine mul_le_mul (norm_helL_le _ _) ?_ (norm_nonneg _) zero_le_one
            exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_left (norm_helL_le _ _) (norm_nonneg _))
        _ = ‖T‖ := by ring
    exact mul_le_mul h1 h3 (norm_nonneg _) (by positivity)
  unfold outerInv
  refine (norm_sum_le_of_le _ fun c _ => norm_sum_le_of_le _ fun e _ => hterm c e).trans
    (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

/-- The arithmetic of the ordinary comparable sector. -/
lemma half_ord {L M J H : ℝ} (hL : 0 < L) (hJ : 0 < J) (hM0 : 0 ≤ M) (h1 : L ≤ 2 * J)
    (h2 : J ≤ 2 * L) (h3 : M ≤ 8 * L) (h4 : M ≤ 8 * J) (hH : L ^ 2 + J ^ 2 ≤ H) :
    L * (M / H) * Br (L ^ 2) (M ^ 2) (J ^ 2) ≤ 65600 := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have e1 : L ^ 2 / J ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [h1, hL, hJ]
  have e2 : J ^ 2 / L ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [h2, hL, hJ]
  have e3 : 2 * (M ^ 2) ^ 2 / (L ^ 2 * J ^ 2) ≤ 8192 := by
    rw [div_le_iff₀ (by positivity)]
    have m1 : M ^ 2 ≤ 64 * L ^ 2 := by nlinarith only [h3, hM0, hL]
    have m2 : M ^ 2 ≤ 64 * J ^ 2 := by nlinarith only [h4, hM0, hJ]
    have m3 := mul_le_mul m1 m2 (sq_nonneg M) (by positivity)
    nlinarith only [m3]
  have hB : Br (L ^ 2) (M ^ 2) (J ^ 2) ≤ 8200 := by
    unfold Br
    linarith
  have hB0 : 0 ≤ Br (L ^ 2) (M ^ 2) (J ^ 2) := by
    unfold Br
    positivity
  have e4 : L * (M / H) ≤ 8 := by
    rw [mul_div_assoc', div_le_iff₀ hH0]
    nlinarith only [h3, hL, hJ, hH, sq_nonneg J]
  have h0 : 0 ≤ L * (M / H) := by positivity
  calc _ ≤ 8 * 8200 := mul_le_mul e4 hB hB0 (by norm_num)
    _ = _ := by norm_num

/-- **The block of the output half** (Body 41), on `P₁, P₂ ≤ D`. -/
theorem norm_X2b_half {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ}
    (f g : Field) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0)
    (hA : absk a ≤ D) (hB : absk b ≤ D) :
    absk l * ‖X2b s r τ f g l a b‖ ≤ 2 ^ 28 / |r| * (‖f a‖ * ‖g b‖) +
      2 ^ 18 / |r| * (gr f a * gr g b * (bandW D l * bandW D (l - a - b))) +
      2 ^ 19 * D / |r| ^ 2 * (‖f a‖ * ‖g b‖ * E2 (l, a, b)) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hJ : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  obtain ⟨p1, p2, p3, p4⟩ := two_leaf_paths l a b
  have hA0 := absk_nonneg a
  have hB0 := absk_nonneg b
  have hD0 : 0 ≤ D := hA0.trans hA
  set v := f a with hv
  set w := g b with hw
  have hv0 := norm_nonneg v
  have hw0 := norm_nonneg w
  have hvw : 0 ≤ ‖v‖ * ‖w‖ := by positivity
  have hE0 := E2_nonneg (l, a, b)
  have hT1 : 0 ≤ 2 ^ 28 / |r| * (‖v‖ * ‖w‖) := by positivity
  have hT2 : 0 ≤ 2 ^ 18 / |r| * (gr f a * gr g b * (bandW D l * bandW D (l - a - b))) := by
    have h1 := gr_nonneg f a
    have h2 := gr_nonneg g b
    have h3 := bandW_nonneg D l
    have h4 := bandW_nonneg D (l - a - b)
    positivity
  have hT3 : 0 ≤ 2 ^ 19 * D / |r| ^ 2 * (‖v‖ * ‖w‖ * E2 (l, a, b)) := by positivity
  have hX : X2b s r τ f g l a b =
      outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (tR s r τ l a b v w) := by
    rw [X2b, ← twoRoot_eq_tR]
  have hH : 0 < heat4 l (l - a - b) a b := heat4_pos hj0 a b
  have hRt := norm_tR_le hs hr τ ha hb hj v w
  have hBr := Br_le_E2 hl0 hj0
  set Br0 := Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) with hBr0
  have hBrn : 0 ≤ Br0 := by
    have := absSq_nonneg l
    have := absSq_nonneg (l - a)
    have := absSq_nonneg (l - a - b)
    simp only [hBr0, Br]
    positivity
  have hsepB : ∀ d : ℝ, 0 < d → d ≤ |absk (l - a - b) - absk l| → absk l ≤ 2 * d →
      absk (l - a) ≤ 5 * D → absk l * ‖X2b s r τ f g l a b‖ ≤
        2 ^ 19 * D / |r| ^ 2 * (‖v‖ * ‖w‖ * E2 (l, a, b)) := fun d hd hsep hLd hMD => by
    have h2 : l 2 = (l - a - b) 2 := by simp [ha, hb]
    have h1 := norm_outerInv_sep hr h2 hj (H := heat4 l (l - a - b) a b) hd hsep (tR s r τ l a b v w)
    rw [← hX] at h1
    have hq : absk l * (4 / (|r| * d)) ≤ 8 / |r| := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hr0]
      nlinarith only [hLd, hr0]
    have hB3 : ‖tR s r τ l a b v w‖ ≤ 704 / |r| * (5 * D) * (‖v‖ * ‖w‖) * (14 * E2 (l, a, b)) :=
      hRt.trans (by gcongr)
    calc absk l * ‖X2b s r τ f g l a b‖ ≤ absk l * (4 / (|r| * d) * ‖tR s r τ l a b v w‖) :=
          mul_le_mul_of_nonneg_left h1 hL.le
      _ = absk l * (4 / (|r| * d)) * ‖tR s r τ l a b v w‖ := by ring
      _ ≤ 8 / |r| * (704 / |r| * (5 * D) * (‖v‖ * ‖w‖) * (14 * E2 (l, a, b))) :=
          mul_le_mul hq hB3 (norm_nonneg _) (by positivity)
      _ = 394240 * D / |r| ^ 2 * (‖v‖ * ‖w‖ * E2 (l, a, b)) := by
          field_simp
          ring
      _ ≤ _ := by
          have : 0 ≤ D / |r| ^ 2 * (‖v‖ * ‖w‖ * E2 (l, a, b)) := by positivity
          have e1 : 394240 * D / |r| ^ 2 * (‖v‖ * ‖w‖ * E2 (l, a, b)) =
              394240 * (D / |r| ^ 2 * (‖v‖ * ‖w‖ * E2 (l, a, b))) := by ring
          have e2 : 2 ^ 19 * D / |r| ^ 2 * (‖v‖ * ‖w‖ * E2 (l, a, b)) =
              2 ^ 19 * (D / |r| ^ 2 * (‖v‖ * ‖w‖ * E2 (l, a, b))) := by ring
          rw [e1, e2]
          nlinarith only [this]
  rcases lt_or_ge (absk (l - a - b)) (absk l / 2) with hsep1 | hc1
  · have h1 := hsepB (absk l / 2) (by positivity) (by
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)) (by linarith) (by linarith)
    linarith
  rcases lt_or_ge (absk l) (absk (l - a - b) / 2) with hsep2 | hc2
  · have h1 := hsepB (absk (l - a - b) / 2) (by positivity)
      (le_trans (by linarith) (le_abs_self _)) (by linarith) (by linarith)
    linarith
  by_cases hhi : 4 * absk l ≤ absk (l - a) ∧ 4 * absk (l - a - b) ≤ absk (l - a)
  · obtain ⟨h4L, h4J⟩ := hhi
    have hsgn := norm_X2b_signed_le (show s ≤ 2 by omega) hr τ f g ha hb hj h4L h4J
    have hLD : absk l ≤ D := by linarith
    have hJD : absk (l - a - b) ≤ D := by linarith
    have e1 : bandW D l = (absk l)⁻¹ := by simp [bandW, hLD]
    have e2 : bandW D (l - a - b) = (absk (l - a - b))⁻¹ := by simp [bandW, hJD]
    rw [e1, e2]
    set L := absk l
    set J := absk (l - a - b)
    set M := absk (l - a)
    set A := absk a
    set B := absk b
    have hA34 : 3 * M ≤ 4 * A := by linarith
    have hB34 : 3 * M ≤ 4 * B := by linarith
    have hME : M ^ 2 * M ^ 2 / (L ^ 2 * J ^ 2) ≤ 256 / 81 * E2 (l, a, b) := by
      have h1 : A ^ 2 * B ^ 2 / (L ^ 2 * J ^ 2) ≤ E2 (l, a, b) := by
        have hl2 : absSq l = L ^ 2 := (absk_sq l).symm
        have hj2 : absSq (l - a - b) = J ^ 2 := (absk_sq _).symm
        have ha2 : absSq a = A ^ 2 := (absk_sq a).symm
        have hb2 : absSq b = B ^ 2 := (absk_sq b).symm
        simp only [E2, inJ₂, hl2, hj2, ha2, hb2]
        have n1 : 0 ≤ (A ^ 2 + B ^ 2) / L ^ 2 := by positivity
        have n2 : 0 ≤ (A ^ 2 + B ^ 2) / J ^ 2 := by positivity
        linarith
      have h2 : M ^ 2 * M ^ 2 ≤ 256 / 81 * (A ^ 2 * B ^ 2) := by
        have h3 : 9 * M ^ 2 ≤ 16 * A ^ 2 := by nlinarith only [hA34, hM, hA0]
        have h4 : 9 * M ^ 2 ≤ 16 * B ^ 2 := by nlinarith only [hB34, hM, hB0]
        have h5 := mul_le_mul h3 h4 (by positivity) (by positivity)
        nlinarith only [h5]
      calc _ ≤ 256 / 81 * (A ^ 2 * B ^ 2) / (L ^ 2 * J ^ 2) :=
            div_le_div_of_nonneg_right h2 (by positivity)
        _ = 256 / 81 * (A ^ 2 * B ^ 2 / (L ^ 2 * J ^ 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by norm_num)
    have hTa : L * ((M / L) ^ 2 * (M / J) ^ 2) ≤ 2 * D * E2 (l, a, b) := by
      have e : L * ((M / L) ^ 2 * (M / J) ^ 2) = L * (M ^ 2 * M ^ 2 / (L ^ 2 * J ^ 2)) := by
        field_simp
      rw [e]
      have hLM : L ≤ D / 3 := by linarith
      calc _ ≤ D / 3 * (256 / 81 * E2 (l, a, b)) :=
            mul_le_mul hLM hME (by positivity) (by positivity)
        _ ≤ _ := by nlinarith only [mul_nonneg hD0 hE0]
    have hTb : L * ((M / L) ^ 2 * (M / J) ^ 2) * ((L + J) / (|r| * M ^ 2)) ≤
        6 / |r| * (A * B * (L⁻¹ * J⁻¹)) := by
      have e : L * ((M / L) ^ 2 * (M / J) ^ 2) * ((L + J) / (|r| * M ^ 2)) =
          1 / |r| * (M ^ 2 * (L + J) * (L⁻¹ * J⁻¹ ^ 2)) := by
        field_simp
      rw [e]
      have e3 : 6 / |r| * (A * B * (L⁻¹ * J⁻¹)) = 1 / |r| * (6 * (A * B) * (L⁻¹ * J⁻¹)) := by ring
      rw [e3]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h3 : L + J ≤ 3 * J := by linarith
      have h4 : M ^ 2 ≤ 16 / 9 * (A * B) := by
        have := mul_le_mul hA34 hB34 (by positivity) (by positivity)
        nlinarith only [this]
      have e4 : M ^ 2 * (L + J) * (L⁻¹ * J⁻¹ ^ 2) = M ^ 2 * ((L + J) * J⁻¹) * (L⁻¹ * J⁻¹) := by ring
      rw [e4]
      have h5 : (L + J) * J⁻¹ ≤ 3 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hJ]
        exact h3
      have h6 : 0 ≤ (L + J) * J⁻¹ := by positivity
      have h7 : 0 ≤ L⁻¹ * J⁻¹ := by positivity
      have hAB : 0 ≤ A * B := by positivity
      calc _ ≤ 16 / 9 * (A * B) * 3 * (L⁻¹ * J⁻¹) := by gcongr
        _ ≤ _ := by
            have : 0 ≤ A * B * (L⁻¹ * J⁻¹) := by positivity
            nlinarith only [this]
    have hP : 0 ≤ (M / L) ^ 2 * (M / J) ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsgn hL.le
    refine h1.trans ?_
    have e5 : L * (2 ^ 15 * ((M / L) ^ 2 * (M / J) ^ 2) * (‖v‖ * ‖w‖) *
        (1 / |r| ^ 2 + (L + J) / (|r| * M ^ 2))) =
        2 ^ 15 * (‖v‖ * ‖w‖) * (L * ((M / L) ^ 2 * (M / J) ^ 2) * (1 / |r| ^ 2)) +
        2 ^ 15 * (‖v‖ * ‖w‖) * (L * ((M / L) ^ 2 * (M / J) ^ 2) * ((L + J) / (|r| * M ^ 2))) := by
      ring
    rw [e5]
    have s1 : 2 ^ 15 * (‖v‖ * ‖w‖) * (L * ((M / L) ^ 2 * (M / J) ^ 2) * (1 / |r| ^ 2)) ≤
        2 ^ 19 * D / |r| ^ 2 * (‖v‖ * ‖w‖ * E2 (l, a, b)) := by
      have h2 := mul_le_mul_of_nonneg_right hTa (by positivity : 0 ≤ 1 / |r| ^ 2)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 ^ 15 * (‖v‖ * ‖w‖))
      refine h3.trans ?_
      have h4 : 0 ≤ D * E2 (l, a, b) * (‖v‖ * ‖w‖) * (1 / |r| ^ 2) := by positivity
      have e7 : 2 ^ 15 * (‖v‖ * ‖w‖) * (2 * D * E2 (l, a, b) * (1 / |r| ^ 2)) =
          65536 * (D * E2 (l, a, b) * (‖v‖ * ‖w‖) * (1 / |r| ^ 2)) := by ring
      have e8 : 2 ^ 19 * D / |r| ^ 2 * (‖v‖ * ‖w‖ * E2 (l, a, b)) =
          524288 * (D * E2 (l, a, b) * (‖v‖ * ‖w‖) * (1 / |r| ^ 2)) := by ring
      rw [e7, e8]
      nlinarith only [h4]
    have s2 : 2 ^ 15 * (‖v‖ * ‖w‖) * (L * ((M / L) ^ 2 * (M / J) ^ 2) * ((L + J) / (|r| * M ^ 2))) ≤
        2 ^ 18 / |r| * (gr f a * gr g b * (L⁻¹ * J⁻¹)) := by
      have h3 := mul_le_mul_of_nonneg_left hTb (by positivity : 0 ≤ 2 ^ 15 * (‖v‖ * ‖w‖))
      refine h3.trans ?_
      have e6 : gr f a * gr g b = A * B * (‖v‖ * ‖w‖) := by
        simp only [gr, hv, hw, A, B]
        ring
      rw [e6]
      have h4 : 0 ≤ 1 / |r| * (A * B * (L⁻¹ * J⁻¹) * (‖v‖ * ‖w‖)) := by positivity
      have e7 : 2 ^ 15 * (‖v‖ * ‖w‖) * (6 / |r| * (A * B * (L⁻¹ * J⁻¹))) =
          196608 * (1 / |r| * (A * B * (L⁻¹ * J⁻¹) * (‖v‖ * ‖w‖))) := by ring
      have e8 : 2 ^ 18 / |r| * (A * B * (‖v‖ * ‖w‖) * (L⁻¹ * J⁻¹)) =
          262144 * (1 / |r| * (A * B * (L⁻¹ * J⁻¹) * (‖v‖ * ‖w‖))) := by ring
      rw [e7, e8]
      nlinarith only [h4]
    linarith
  · have hrw : ¬(4 * absk l ≤ absk (l - a) ∧ 4 * absk (l - a - b) ≤ absk (l - a)) := hhi
    have hM8L : absk (l - a) ≤ 8 * absk l := by
      by_contra h
      rw [not_le] at h
      exact hrw ⟨by linarith, by linarith⟩
    have hM8J : absk (l - a) ≤ 8 * absk (l - a - b) := by
      by_contra h
      rw [not_le] at h
      exact hrw ⟨by linarith, by linarith⟩
    have hHH : absk l ^ 2 + absk (l - a - b) ^ 2 ≤ heat4 l (l - a - b) a b := by
      unfold heat4
      rw [absk_sq, absk_sq]
      have := absSq_nonneg a
      have := absSq_nonneg b
      linarith
    have ho := half_ord hL hJ hM.le (by linarith) (by linarith) hM8L hM8J hHH
    have ee : Br (absk l ^ 2) (absk (l - a) ^ 2) (absk (l - a - b) ^ 2) = Br0 := by
      rw [absk_sq, absk_sq, absk_sq]
    rw [ee] at ho
    have h1 := norm_outerInv_le hH r l (l - a - b) (tR s r τ l a b v w)
    rw [← hX] at h1
    have h3 : absk l * ‖X2b s r τ f g l a b‖ ≤
        2816 / |r| * (‖v‖ * ‖w‖) * (absk l * (absk (l - a) / heat4 l (l - a - b) a b) * Br0) := by
      calc _ ≤ absk l * (4 / heat4 l (l - a - b) a b * (704 / |r| * absk (l - a) * (‖v‖ * ‖w‖) *
            Br0)) := by
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) hL.le
            exact mul_le_mul_of_nonneg_left hRt (by positivity)
        _ = _ := by
            field_simp
            ring
    have h4 := mul_le_mul_of_nonneg_left ho (by positivity : 0 ≤ 2816 / |r| * (‖v‖ * ‖w‖))
    have h5 : 2816 / |r| * (‖v‖ * ‖w‖) * 65600 ≤ 2 ^ 28 / |r| * (‖v‖ * ‖w‖) := by
      have : 0 ≤ 1 / |r| * (‖v‖ * ‖w‖) := by positivity
      have e1 : 2816 / |r| * (‖v‖ * ‖w‖) * 65600 = 184729600 * (1 / |r| * (‖v‖ * ‖w‖)) := by ring
      have e2 : 2 ^ 28 / |r| * (‖v‖ * ‖w‖) = 268435456 * (1 / |r| * (‖v‖ * ‖w‖)) := by ring
      rw [e1, e2]
      nlinarith only [this]
    linarith

open Classical in
/-- The low-ancestor mask of `X₂`: both slow leaves at most `D`. -/
def loMask₂ (D : ℝ) (x : I3) : ℂ := if absk x.2.1 ≤ D ∧ absk x.2.2 ≤ D then 1 else 0

lemma norm_loMask₂_le (D : ℝ) (x : I3) : ‖loMask₂ D x‖ ≤ 1 := by
  unfold loMask₂
  split_ifs <;> simp

/-- `hi + lo = 1`. -/
lemma hi_add_lo₂ (D : ℝ) (x : I3) : hiMask₂ D x + loMask₂ D x = 1 := by
  unfold hiMask₂ loMask₂
  by_cases h1 : absk x.2.1 ≤ D
  · by_cases h2 : absk x.2.2 ≤ D
    · simp [h1, h2, not_lt.2 h1, not_lt.2 h2]
    · have : D < absk x.2.2 := not_le.1 h2
      simp [h2, this]
  · have : D < absk x.2.1 := not_le.1 h1
    simp [h1, this]

/-- The band sum of the phase kernel: `κ₁ = 1/J`, `κ₂ = 1/L`, one log. -/
lemma pos2_band2 {α β u v : Mode → ℝ} {A B U V D : ℝ} (hD : 1 ≤ D) (hα : L2B α A) (hβ : L2B β B)
    (hu : L2B u U) (hv : L2B v V) (hus : ∀ p, p 2 ≠ 0 → u p = 0) (hvs : ∀ p, p 2 ≠ 0 → v p = 0) :
    SB (fun x : I3 => α x.1 * β (inJ₂ x) * (u x.2.1 * v x.2.2 *
      (bandW D x.1 * bandW D (inJ₂ x)))) ((9 + 8 * Real.log D) * (A * B * (U * V))) := by
  have hlog : 0 ≤ 9 + 8 * Real.log D := by
    have := Real.log_nonneg hD
    linarith
  have hF := fib_band hD
  set κ₁ : I3 → ℝ := fun x => if x.2.2 2 = 0 then bandW D (inJ₂ x) else 0 with h1
  set κ₂ : I3 → ℝ := fun x => if x.2.1 2 = 0 then bandW D x.1 else 0 with h2
  have h10 : ∀ x, 0 ≤ κ₁ x := fun x => by
    simp only [h1]
    split_ifs
    · exact bandW_nonneg _ _
    · exact le_rfl
  have h20 : ∀ x, 0 ≤ κ₂ x := fun x => by
    simp only [h2]
    split_ifs
    · exact bandW_nonneg _ _
    · exact le_rfl
  have c1 : ∀ l a, SB (fun b => κ₁ (l, a, b) ^ 2) (9 + 8 * Real.log D) := fun l a => by
    refine (hF (l - a)).of_le (fun b => sq_nonneg _) fun b => le_of_eq ?_
    by_cases hb : b 2 = 0
    · simp [h1, inJ₂, hb]
    · simp [h1, hb]
  have c2 : ∀ j b, SB (fun a => κ₂ (j + b + a, a, b) ^ 2) (9 + 8 * Real.log D) := fun j b => by
    refine (hF.add (j + b)).of_le (fun a => sq_nonneg _) fun a => le_of_eq ?_
    by_cases ha : a 2 = 0
    · simp [h2, ha]
    · simp [h2, ha]
  have hc := cs_mid h10 h20 c1 c2 hlog hlog hα hβ hu hv
  have hsq : Real.sqrt (9 + 8 * Real.log D) * Real.sqrt (9 + 8 * Real.log D) =
      9 + 8 * Real.log D := Real.mul_self_sqrt hlog
  have hle : (A * U * Real.sqrt (9 + 8 * Real.log D)) * (B * V * Real.sqrt (9 + 8 * Real.log D)) =
      (9 + 8 * Real.log D) * (A * B * (U * V)) := by
    calc _ = Real.sqrt (9 + 8 * Real.log D) * Real.sqrt (9 + 8 * Real.log D) *
        (A * B * (U * V)) := by ring
      _ = _ := by rw [hsq]
  rw [hle] at hc
  refine hc.of_le (fun x => ?_) fun x => le_of_eq ?_
  · have h3 := hα.nn x.1
    have h4 := hβ.nn (inJ₂ x)
    have h5 := hu.nn x.2.1
    have h6 := hv.nn x.2.2
    have h7 := bandW_nonneg D x.1
    have h8 := bandW_nonneg D (inJ₂ x)
    positivity
  · by_cases ha : x.2.1 2 = 0
    · by_cases hb : x.2.2 2 = 0
      · simp only [h1, h2, ha, hb, ↓reduceIte]
        ring
      · simp [hvs _ hb]
    · simp [hus _ ha]

/-- The majorant of the low output half. -/
def Psi2 (r D : ℝ) (f g G F : Field) (x : I3) : ℝ :=
  2 ^ 28 / |r| * Phi₂ (nrm G) (nrm F) (nrm f) (nrm g) x +
    2 ^ 18 / |r| * (nrm G x.1 * nrm F (inJ₂ x) * (gr f x.2.1 * gr g x.2.2 *
      (bandW D x.1 * bandW D (inJ₂ x)))) +
    2 ^ 19 * D / |r| ^ 2 * (Phi₂ (nrm G) (nrm F) (nrm f) (nrm g) x * E2 x)

/-- The sum of the majorant. -/
lemma sb_Psi2 {r D : ℝ} (hr : r ≠ 0) (hD : 1 ≤ D) {f g G F : Field} (hf : MZ 2 f) (hf' : PiS f = f)
    (hg : MZ 2 g) (hg' : PiS g = g) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) :
    SB (Psi2 r D f g G F) ((2 ^ 28 / |r| * (wiener f * wiener g) +
      2 ^ 18 / |r| * ((9 + 8 * Real.log D) * (hnorm 1 f * hnorm 1 g)) +
      2 ^ 19 * D / |r| ^ 2 * cls2 (wiener f) (wiener g) (hnorm 2 f) (hnorm 2 g)) *
        (l2n G * l2n F)) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hD0 : 0 ≤ D := by linarith
  have α := l2B_nrm hG
  have β := l2B_nrm hF
  have W1 := l1B_nrm hf.inH
  have W2 := l1B_nrm hg.inH
  have s1 := (pos2_I α β W1 W2).const_mul (by positivity : 0 ≤ 2 ^ 28 / |r|)
  have s2 := (pos2_band2 hD α β (l2B_gr (hf.inH.mono (by norm_num)))
    (l2B_gr (hg.inH.mono (by norm_num)))
    (fun p hp => by simp [gr, slow_zero hf' hp])
    (fun p hp => by simp [gr, slow_zero hg' hp])).const_mul (by positivity : 0 ≤ 2 ^ 18 / |r|)
  have s3 := (pos2_E2 α β W1 W2 (l2B_up hf.inH) (l2B_up hg.inH)).const_mul
    (by positivity : 0 ≤ 2 ^ 19 * D / |r| ^ 2)
  refine ((s1.add s2).add s3).mono_bd (le_of_eq ?_)
  ring

lemma Psi2_nonneg {r D : ℝ} (hD : 0 ≤ D) (f g G F : Field) (x : I3) : 0 ≤ Psi2 r D f g G F x := by
  have hr0 := abs_nonneg r
  have h1 : 0 ≤ Phi₂ (nrm G) (nrm F) (nrm f) (nrm g) x :=
    Phi₂_nonneg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) x
  have h2 := gr_nonneg f x.2.1
  have h3 := gr_nonneg g x.2.2
  have h4 := bandW_nonneg D x.1
  have h5 := bandW_nonneg D (inJ₂ x)
  have h6 : 0 ≤ nrm G x.1 := norm_nonneg _
  have h7 : 0 ≤ nrm F (inJ₂ x) := norm_nonneg _
  have h8 := E2_nonneg x
  unfold Psi2
  positivity

/-- A summand, with the block already bounded. -/
lemma summand_of_block {c : ℂ} (hc : ‖c‖ ≤ 1) {L X R n1 n2 : ℝ} {I : ℂ} (hL : 0 ≤ L) (hn1 : 0 ≤ n1)
    (hn2 : 0 ≤ n2) (hI : ‖I‖ ≤ n1 * n2 * X) (hk : L * X ≤ R) :
    ‖c * ((L : ℝ) : ℂ) * I‖ ≤ n1 * n2 * R := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hL]
  have h2 : ‖c‖ * L ≤ 1 * L := mul_le_mul_of_nonneg_right hc hL
  have h3 : ‖c‖ * L * ‖I‖ ≤ 1 * L * (n1 * n2 * X) :=
    mul_le_mul h2 hI (norm_nonneg _) (by positivity)
  have h4 := mul_le_mul_of_nonneg_left hk (mul_nonneg hn1 hn2)
  calc _ ≤ 1 * L * (n1 * n2 * X) := h3
    _ = n1 * n2 * (L * X) := by ring
    _ ≤ _ := h4

lemma Psi2_eq (r D : ℝ) (f g G F : Field) (x : I3) : Psi2 r D f g G F x =
    ‖G x.1‖ * ‖F (inJ₂ x)‖ * (2 ^ 28 / |r| * (‖f x.2.1‖ * ‖g x.2.2‖) +
      2 ^ 18 / |r| * (gr f x.2.1 * gr g x.2.2 * (bandW D x.1 * bandW D (inJ₂ x))) +
      2 ^ 19 * D / |r| ^ 2 * (‖f x.2.1‖ * ‖g x.2.2‖ * E2 x)) := by
  simp only [Psi2, Phi₂, nrm]
  ring

/-- The summand of the low output half, on a mask. -/
lemma half_summand {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 0 ≤ D)
    {f g G F : Field} (hf' : PiS f = f) (hg' : PiS g = g) (hF' : PiF F = F) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {x : I3} (hmask : absk x.2.1 ≤ D ∧ absk x.2.2 ≤ D) :
    ‖c * ((absk x.1 : ℝ) : ℂ) *
      inner ℂ (G x.1) (X2b s r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))‖ ≤
      Psi2 r D f g G F x := by
  have hΨ := Psi2_nonneg (r := r) hD f g G F x
  by_cases ha : x.2.1 2 = 0
  swap
  · have h0 : X2b s r τ f g x.1 x.2.1 x.2.2 = 0 := X2b_eq_zero (Or.inl (slow_zero hf' ha))
    rw [h0, zero_apply, inner_zero_right, mul_zero, norm_zero]
    exact hΨ
  by_cases hb2 : x.2.2 2 = 0
  swap
  · have h0 : X2b s r τ f g x.1 x.2.1 x.2.2 = 0 := X2b_eq_zero (Or.inr (slow_zero hg' hb2))
    rw [h0, zero_apply, inner_zero_right, mul_zero, norm_zero]
    exact hΨ
  by_cases hj : inJ₂ x 2 = 0
  · have h0 : F (x.1 - x.2.1 - x.2.2) = 0 := fast_zero hF' hj
    rw [h0, map_zero, inner_zero_right, mul_zero, norm_zero]
    exact hΨ
  have hk := norm_X2b_half hs hr τ f g ha hb2 hj hmask.1 hmask.2
  rw [Psi2_eq]
  exact summand_of_block hc (absk_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_inner_apply_le _ _ _) hk

/-- **The output half on the low mask** (Body 41). -/
theorem X2Half_lo_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 1 ≤ D)
    {f g G F : Field} (hf : MZ 2 f) (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g)
    (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F)
    {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ ‖loMask₂ D x‖) :
    ‖X2HalfForm μ s r τ f g G F‖ ≤ (2 ^ 28 / |r| * (wiener f * wiener g) +
      2 ^ 18 / |r| * ((9 + 8 * Real.log D) * (hnorm 1 f * hnorm 1 g)) +
      2 ^ 19 * D / |r| ^ 2 * cls2 (wiener f) (wiener g) (hnorm 2 f) (hnorm 2 g)) *
        (l2n G * l2n F) := by
  have hD0 : 0 ≤ D := by linarith
  have hb := sb_Psi2 hr hD hf hf' hg hg' hG hF
  refine (form_le hb fun x => ?_).2
  by_cases hmask : absk x.2.1 ≤ D ∧ absk x.2.2 ≤ D
  swap
  · have h2 : loMask₂ D x = 0 := by simp [loMask₂, hmask]
    have h3 : μ x = 0 := by
      have h1 := hμ x
      rw [h2, norm_zero] at h1
      exact norm_le_zero_iff.1 h1
    rw [h3, zero_mul, zero_mul, norm_zero]
    exact Psi2_nonneg hD0 f g G F x
  exact half_summand hs hr τ hD0 hf' hg' hF' ((hμ x).trans (norm_loMask₂_le D x)) hmask

end OVNS.Quant.Metric

end
