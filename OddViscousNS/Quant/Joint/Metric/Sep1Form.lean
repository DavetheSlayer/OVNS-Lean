import OddViscousNS.Quant.Joint.Metric.Sep1

/-!
# Weight one: the forms of the high last edge (step J5, node N10)

Unit: `TIMED_METRIC_PROOF_V2.md` §8.2, §8.3, with `a = ‖S‖₁`, `b = ‖S‖₂`, `W = ‖Ŝ‖_{ℓ¹}`:
* `YLForm_sep_one`: on `muS`: `q⁻² (1 + ln D) a b W`, (8.4) with `a` for `a_ε`, since every label is
  at most `4D`;
* `HtQ_one_le`: the heat of the comparable mask: `q⁻² (1 + ln D)^{3/2} a² b`, (8.5), the band in
  place of the fractional dissipation.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {D : ℝ} {x : I4} {α β u v w : Mode → ℝ} {A B U V W : ℝ}

/-- The band of the masks. -/
lemma labels_le {x : I4} (hA : absk x.2.1 ≤ D) (hB : absk x.2.2.1 ≤ D) (hC : absk x.2.2.2 ≤ D)
    (hgt : 16 * absk (inJ x) < absk x.2.2.2) : absk x.1 ≤ 4 * D ∧ absk (inJ x) ≤ 4 * D := by
  obtain ⟨-, h2⟩ := last_lengths hgt
  obtain ⟨-, -, p3, -⟩ := two_leaf_paths x.1 x.2.1 x.2.2.1
  have h4 := absk_nonneg (inJ x)
  have h5 := absk_nonneg x.2.2.2
  constructor <;> linarith

lemma bandW_of_le {E : ℝ} {k : Mode} (h : absk k ≤ E) : bandW E k = (absk k)⁻¹ := by
  simp [bandW, h]

/-- `pos3_band2` with the `ℓ¹` leaf in the second slot. -/
theorem pos3_band2₂ (hD : 1 ≤ D) (hα : L2B α A) (hβ : L2B β B) (hu : L2B u U) (hv : L2B v V)
    (hw : L1B w W) (hus : ∀ p, p 2 ≠ 0 → u p = 0) (hvs : ∀ p, p 2 ≠ 0 → v p = 0) :
    SB (fun x : I4 => α x.1 * bandW D x.1 * (β (inJ x) * bandW D (inJ x)) *
      (u x.2.1 * w x.2.2.1 * v x.2.2.2))
      (A * U * Real.sqrt (9 + 8 * Real.log D) * (B * V * Real.sqrt (9 + 8 * Real.log D)) * W) := by
  refine SB.equiv swap23 (pos3_band2 hD hα hβ hu hv hw hus hvs) fun x => ?_
  rw [inJ_swap23, swap23_apply]
  simp only
  ring

/-- `pos3_band2` with the `ℓ¹` leaf in the first slot. -/
theorem pos3_band2₁ (hD : 1 ≤ D) (hα : L2B α A) (hβ : L2B β B) (hu : L2B u U) (hv : L2B v V)
    (hw : L1B w W) (hus : ∀ p, p 2 ≠ 0 → u p = 0) (hvs : ∀ p, p 2 ≠ 0 → v p = 0) :
    SB (fun x : I4 => α x.1 * bandW D x.1 * (β (inJ x) * bandW D (inJ x)) *
      (w x.2.1 * u x.2.2.1 * v x.2.2.2))
      (A * U * Real.sqrt (9 + 8 * Real.log D) * (B * V * Real.sqrt (9 + 8 * Real.log D)) * W) := by
  refine SB.equiv swap12 (pos3_band2₂ hD hα hβ hu hv hw hus hvs) fun x => ?_
  rw [inJ_swap12, swap12_apply]
  simp only
  ring

/-- The majorant of the separated form at weight one. -/
def Ps1 (D : ℝ) (G F : Mode → ℝ) (S : Field) (x : I4) : ℝ :=
  G x.1 * bandW (4 * D) x.1 * (F (inJ x) * bandW (4 * D) (inJ x)) *
    (gr S x.2.1 * nrm S x.2.2.1 * up (nrm S) x.2.2.2 +
      nrm S x.2.1 * gr S x.2.2.1 * up (nrm S) x.2.2.2 +
      up (nrm S) x.2.1 * nrm S x.2.2.1 * gr S x.2.2.2 +
      nrm S x.2.1 * up (nrm S) x.2.2.1 * gr S x.2.2.2 +
      up (nrm S) x.2.1 * gr S x.2.2.1 * nrm S x.2.2.2)

/-- The sum of the separated form at weight one. -/
def sep1B (D : ℝ) (S : Field) : ℝ :=
  5 * ((9 + 8 * Real.log (4 * D)) * (hnorm 1 S * hnorm 2 S * wiener S))

lemma sb_Ps1 (hD : 1 ≤ D) {S : Field} (hS : MZ 2 S) (hS' : PiS S = S) (hα : L2B α A)
    (hβ : L2B β B) : SB (Ps1 D α β S) (A * B * sep1B D S) := by
  have hD4 : 1 ≤ 4 * D := by linarith
  have wS := l1B_nrm hS.inH
  have aS := l2B_gr (hS.inH.mono (by norm_num) : InH 1 S)
  have uS := l2B_up hS.inH
  have gs := gr_slow hS'
  have us : ∀ p : Mode, p 2 ≠ 0 → up (nrm S) p = 0 := fun p hp => by
    simp [up, nrm_slow hS' p hp]
  have t1 := pos3_band2₂ hD4 hα hβ aS uS wS gs us
  have t2 := pos3_band2₁ hD4 hα hβ aS uS wS gs us
  have t3 := pos3_band2₂ hD4 hα hβ uS aS wS us gs
  have t4 := pos3_band2₁ hD4 hα hβ uS aS wS us gs
  have t5 := pos3_band2 hD4 hα hβ uS aS wS us gs
  have hZ : Real.sqrt (9 + 8 * Real.log (4 * D)) * Real.sqrt (9 + 8 * Real.log (4 * D)) =
      9 + 8 * Real.log (4 * D) := by
    have := Real.log_nonneg hD4
    exact Real.mul_self_sqrt (by linarith)
  have h := (((t1.add t2).add t3).add t4).add t5
  refine SB.of_le (h.mono_bd (le_of_eq ?_)) (fun x => ?_) fun x => ?_
  · simp only [sep1B]
    calc _ = 5 * (A * B * (hnorm 1 S * hnorm 2 S * wiener S)) *
          (Real.sqrt (9 + 8 * Real.log (4 * D)) * Real.sqrt (9 + 8 * Real.log (4 * D))) := by ring
      _ = _ := by
          rw [hZ]
          ring
  · have n1 := hα.nn x.1
    have n2 := hβ.nn (inJ x)
    have n3 := bandW_nonneg (4 * D) x.1
    have n4 := bandW_nonneg (4 * D) (inJ x)
    have n5 := gr_nonneg S x.2.1
    have n6 := gr_nonneg S x.2.2.1
    have n7 := gr_nonneg S x.2.2.2
    have n8 : 0 ≤ nrm S x.2.1 := norm_nonneg _
    have n9 : 0 ≤ nrm S x.2.2.1 := norm_nonneg _
    have n10 : 0 ≤ nrm S x.2.2.2 := norm_nonneg _
    have n11 := up_nrm_nonneg S x.2.1
    have n12 := up_nrm_nonneg S x.2.2.1
    have n13 := up_nrm_nonneg S x.2.2.2
    unfold Ps1
    positivity
  · refine le_of_eq ?_
    simp only [Ps1]
    ring

/-- A term of the separated form at weight one. -/
lemma sep1_term {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S G F : Field} (hS' : PiS S = S) (hF' : PiF F = F)
    {μ : I4 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ muS D x) (x : I4) :
    ‖μ x * inner ℂ (G x.1) (YLb 1 r τ S S S x (F (inJ x)))‖ ≤
      2 ^ 28 / |r| ^ 2 * Ps1 D (nrm G) (nrm F) S x := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hR : 0 ≤ 2 ^ 28 / |r| ^ 2 * Ps1 D (nrm G) (nrm F) S x := by
    have n1 : 0 ≤ nrm G x.1 := norm_nonneg _
    have n2 : 0 ≤ nrm F (inJ x) := norm_nonneg _
    have n3 := bandW_nonneg (4 * D) x.1
    have n4 := bandW_nonneg (4 * D) (inJ x)
    have n5 := gr_nonneg S x.2.1
    have n6 := gr_nonneg S x.2.2.1
    have n7 := gr_nonneg S x.2.2.2
    have n8 : 0 ≤ nrm S x.2.1 := norm_nonneg _
    have n9 : 0 ≤ nrm S x.2.2.1 := norm_nonneg _
    have n10 : 0 ≤ nrm S x.2.2.2 := norm_nonneg _
    have n11 := up_nrm_nonneg S x.2.1
    have n12 := up_nrm_nonneg S x.2.2.1
    have n13 := up_nrm_nonneg S x.2.2.2
    unfold Ps1
    positivity
  by_cases hm : muS D x = 0
  · have h0 : μ x = 0 := by
      have := hμ x
      rw [hm] at this
      exact norm_le_zero_iff.1 this
    simpa [h0] using hR
  by_cases ha : x.2.1 2 = 0
  swap
  · rw [YLb_eq_zero (Or.inl (slow_zero hS' ha))]
    simpa using hR
  by_cases hb : x.2.2.1 2 = 0
  swap
  · rw [YLb_eq_zero (Or.inr (Or.inl (slow_zero hS' hb)))]
    simpa using hR
  by_cases hc : x.2.2.2 2 = 0
  swap
  · rw [YLb_eq_zero (Or.inr (Or.inr (slow_zero hS' hc)))]
    simpa using hR
  by_cases hj : inJ x 2 = 0
  · rw [fast_zero hF' hj, map_zero, inner_zero_right, mul_zero, norm_zero]
    exact hR
  have hSm := onS_of_ne hm
  have hB := norm_YLb_sep_one hr τ ⟨ha, hb, hc, hj⟩ hSm S S S
  obtain ⟨hl4, hj4⟩ := labels_le hSm.a_le hSm.b_le hSm.c_le hSm.c_gt
  have h1 := norm_inner_apply_le (G x.1) (F (inJ x)) (YLb 1 r τ S S S x)
  have hμ1 : ‖μ x‖ ≤ 1 := (hμ x).trans (muS_le_one D x)
  have hP : 0 ≤ ‖G x.1‖ * ‖F (inJ x)‖ := by positivity
  rw [norm_mul]
  calc _ ≤ 1 * (‖G x.1‖ * ‖F (inJ x)‖ * ‖YLb 1 r τ S S S x‖) :=
        mul_le_mul hμ1 h1 (norm_nonneg _) zero_le_one
    _ = ‖G x.1‖ * ‖F (inJ x)‖ * ‖YLb 1 r τ S S S x‖ := one_mul _
    _ ≤ ‖G x.1‖ * ‖F (inJ x)‖ * (2 ^ 28 / |r| ^ 2 * Es1 x *
        (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖)) := mul_le_mul_of_nonneg_left hB hP
    _ = _ := by
        simp only [Ps1, nrm, gr, up, Es1, bandW_of_le hl4, bandW_of_le hj4, ← absk_sq]
        ring

/-- **The separated high-last sector at weight one** (8.4). -/
theorem YLForm_sep_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hD : 1 ≤ D) {S G F : Field} (hS : MZ 2 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) {μ : I4 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ muS D x) :
    (Summable fun x : I4 => μ x * inner ℂ (G x.1) (YLb 1 r τ S S S x (F (inJ x)))) ∧
      ‖YLForm μ 1 r τ S S S G F‖ ≤ 2 ^ 28 / |r| ^ 2 * (l2n G * l2n F * sep1B D S) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hs := (sb_Ps1 hD hS hS' (l2B_nrm hG) (l2B_nrm hF)).const_mul
    (by positivity : 0 ≤ 2 ^ 28 / |r| ^ 2)
  exact form_le hs (sep1_term hr τ hS' hF' hμ)

/-! ### The heat of the comparable mask -/

/-- **The heat block at weight one.** -/
lemma norm_HB_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hx : Act₃ x) (hQ' : OnQ D x) (f g h : Field) :
    ‖HB 1 r τ f g h x‖ ≤ 2 ^ 21 / |r| ^ 2 * (absk x.2.1 * absk x.2.2.1 * absk x.2.2.2 *
      (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) * ((absk x.1)⁻¹ * (absk (inJ x))⁻¹)) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  obtain ⟨ha, hb, hc, hj⟩ := hx
  have hk2 : (x.1 - x.2.1 - x.2.2.1) 2 ≠ 0 := by
    have e : (x.1 - x.2.1 - x.2.2.1) 2 = inJ x 2 := by
      simp [inJ, hc]
    rwa [e]
  obtain ⟨hl0, hm0, hk0⟩ := fast_labels ha hb hk2
  have hj0 : inJ x ≠ 0 := fun h => hj (by rw [h]; rfl)
  have hL : 0 < absk x.1 := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (x.1 - x.2.1 - x.2.2.1) := lt_of_lt_of_le one_pos (one_le_absk hk0)
  have hJ : 0 < absk (inJ x) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hA0 := absk_nonneg x.2.1
  have hB0 := absk_nonneg x.2.2.1
  have hC0 := absk_nonneg x.2.2.2
  have hN1 := norm_nonneg (f x.2.1)
  have hN2 := norm_nonneg (g x.2.2.1)
  have hN3 := norm_nonneg (h x.2.2.2)
  have hLi := inv_pos.2 hL
  have hJi := inv_pos.2 hJ
  have hR0 : 0 ≤ 2 ^ 21 / |r| ^ 2 * (absk x.2.1 * absk x.2.2.1 * absk x.2.2.2 *
      (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) * ((absk x.1)⁻¹ * (absk (inJ x))⁻¹)) := by positivity
  by_cases hi : 4 * absk x.1 ≤ absk (x.1 - x.2.1) ∧
      4 * absk (x.1 - x.2.1 - x.2.2.1) ≤ absk (x.1 - x.2.1)
  swap
  · have e0 : hQ 1 r τ x.1 x.2.1 x.2.2.1 (f x.2.1) (g x.2.2.1) = 0 := by
      simp only [hQ, hi, ite_false]
    have e1 : HB 1 r τ f g h x = 0 := by
      simp only [HB, e0, outerInv_zero, ContinuousLinearMap.zero_comp]
    rw [e1, norm_zero]
    exact hR0
  have e0 : hQ 1 r τ x.1 x.2.1 x.2.2.1 (f x.2.1) (g x.2.2.1) =
      tH 1 r τ x.1 x.2.1 x.2.2.1 (f x.2.1) (g x.2.2.1) := by
    simp only [hQ, hi, and_self, ite_true]
  have hX := norm_Xheat_one hr τ ha hb hk2 hi.1 hi.2 (f x.2.1) (g x.2.2.1)
  have ek : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
    simp only [inJ]
    abel
  have hE := norm_Lb_le 1 τ ek (h x.2.2.2)
  simp only [wt, pow_one] at hE
  obtain ⟨p1, p2, -, -⟩ := two_leaf_paths x.1 x.2.1 x.2.2.1
  obtain ⟨-, hKc⟩ := last_lengths hQ'.c_gt
  have m1 : absk (x.1 - x.2.1) ≤ 4 / 3 * absk x.2.1 := by linarith [hi.1]
  have m2 : absk (x.1 - x.2.1) ≤ 4 / 3 * absk x.2.2.1 := by linarith [hi.2]
  have hM0 := absk_nonneg (x.1 - x.2.1)
  have hM2 : absk (x.1 - x.2.1) ^ 2 ≤ 16 / 9 * (absk x.2.1 * absk x.2.2.1) := by
    calc _ = absk (x.1 - x.2.1) * absk (x.1 - x.2.1) := by ring
      _ ≤ 4 / 3 * absk x.2.1 * (4 / 3 * absk x.2.2.1) := by gcongr
      _ = _ := by ring
  simp only [HB, e0]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hmul := mul_le_mul hX hE (norm_nonneg _) (by positivity)
  refine hmul.trans ?_
  set L := absk x.1
  set K := absk (x.1 - x.2.1 - x.2.2.1)
  set J := absk (inJ x)
  set M := absk (x.1 - x.2.1)
  set A := absk x.2.1
  set B := absk x.2.2.1
  set C := absk x.2.2.2
  set V := ‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖ with hV
  have hV0 : 0 ≤ V := by positivity
  have e1 : 2 ^ 15 / |r| ^ 2 * (M ^ 2 / (L * K)) * (‖f x.2.1‖ * ‖g x.2.2.1‖) *
      (16 * (K / J) * K * ‖h x.2.2.2‖) = 2 ^ 19 / |r| ^ 2 * (M ^ 2 * K * V * (L⁻¹ * J⁻¹)) := by
    simp only [hV]
    field_simp
    ring
  rw [e1]
  have hp : 0 ≤ V * (L⁻¹ * J⁻¹) := by positivity
  calc _ = 2 ^ 19 / |r| ^ 2 * ((M ^ 2 * K) * (V * (L⁻¹ * J⁻¹))) := by ring
    _ ≤ 2 ^ 19 / |r| ^ 2 * ((16 / 9 * (A * B) * (2 * C)) * (V * (L⁻¹ * J⁻¹))) := by gcongr
    _ = 2 ^ 19 * (32 / 9) / |r| ^ 2 * (A * B * C * V * (L⁻¹ * J⁻¹)) := by ring
    _ ≤ _ := by
        have : 0 ≤ A * B * C * V * (L⁻¹ * J⁻¹) := by positivity
        refine mul_le_mul_of_nonneg_right ?_ this
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- The majorant of the heat form at weight one. -/
def PsiH1 (D : ℝ) (S : Field) (G F : Mode → ℝ) (x : I4) : ℝ :=
  G x.1 * bandW (4 * D) x.1 * (F (inJ x) * bandW (4 * D) (inJ x)) *
    (gr S x.2.1 * gr S x.2.2.1 * nrm (loP D (zOf 1 S)) x.2.2.2)

/-- A term of the heat form at weight one. -/
lemma HtQ_one_term {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S G F : Field} (hS' : PiS S = S)
    (hF' : PiF F = F) (x : I4) :
    ‖((muQ D x : ℝ) : ℂ) * inner ℂ (G x.1) (HB 1 r τ S S S x (F (inJ x)))‖ ≤
      2 ^ 21 / |r| ^ 2 * PsiH1 D S (nrm G) (nrm F) x := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hR : 0 ≤ 2 ^ 21 / |r| ^ 2 * PsiH1 D S (nrm G) (nrm F) x := by
    have n1 : 0 ≤ nrm G x.1 := norm_nonneg _
    have n2 : 0 ≤ nrm F (inJ x) := norm_nonneg _
    have n3 := bandW_nonneg (4 * D) x.1
    have n4 := bandW_nonneg (4 * D) (inJ x)
    have n5 := gr_nonneg S x.2.1
    have n6 := gr_nonneg S x.2.2.1
    have n7 : 0 ≤ nrm (loP D (zOf 1 S)) x.2.2.2 := norm_nonneg _
    unfold PsiH1
    positivity
  by_cases hm : muQ D x = 0
  · rw [hm]
    simpa using hR
  by_cases ha : x.2.1 2 = 0
  swap
  · rw [HB_zero (Or.inl (slow_zero hS' ha))]
    simpa using hR
  by_cases hb : x.2.2.1 2 = 0
  swap
  · rw [HB_zero (Or.inr (Or.inl (slow_zero hS' hb)))]
    simpa using hR
  by_cases hc : x.2.2.2 2 = 0
  swap
  · rw [HB_zero (Or.inr (Or.inr (slow_zero hS' hc)))]
    simpa using hR
  by_cases hj : inJ x 2 = 0
  · rw [fast_zero hF' hj, map_zero, inner_zero_right, mul_zero, norm_zero]
    exact hR
  have hQ' := onQ_of_ne hm
  have hB := norm_HB_one hr τ ⟨ha, hb, hc, hj⟩ hQ' S S S
  obtain ⟨hl4, hj4⟩ := labels_le hQ'.a_le hQ'.b_le hQ'.c_le hQ'.c_gt
  have h1 := norm_inner_apply_le (G x.1) (F (inJ x)) (HB 1 r τ S S S x)
  have hP0 : 0 ≤ ‖G x.1‖ * ‖F (inJ x)‖ := by positivity
  have hlo : nrm (loP D (zOf 1 S)) x.2.2.2 = absk x.2.2.2 * ‖S x.2.2.2‖ := by
    have hn : ¬ D < absk x.2.2.2 := not_lt.2 hQ'.c_le
    simp only [nrm, loP, hn, ↓reduceIte, zOf, norm_smul, Complex.norm_real, pow_one,
      Real.norm_of_nonneg (absk_nonneg _)]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (muQ_nonneg D x)]
  calc _ ≤ 1 * (‖G x.1‖ * ‖F (inJ x)‖ * ‖HB 1 r τ S S S x‖) :=
        mul_le_mul (muQ_le_one D x) h1 (norm_nonneg _) zero_le_one
    _ = ‖G x.1‖ * ‖F (inJ x)‖ * ‖HB 1 r τ S S S x‖ := one_mul _
    _ ≤ _ := mul_le_mul_of_nonneg_left hB hP0
    _ = _ := by
        unfold PsiH1
        rw [hlo]
        simp only [nrm, gr, bandW_of_le hl4, bandW_of_le hj4]
        ring

/-- **The heat of the comparable mask at weight one** (8.5). -/
theorem HtQ_one_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hD : 1 ≤ D) {S G F : Field} (hS : MZ 2 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) :
    ‖HtQ D 1 r τ S S S G F‖ ≤ 2 ^ 21 / |r| ^ 2 *
      (l2n G * hnorm 1 S * Real.sqrt (9 + 8 * Real.log (4 * D)) *
        (l2n F * hnorm 1 S * Real.sqrt (9 + 8 * Real.log (4 * D))) *
        (Real.sqrt (9 + 8 * Real.log D) * hnorm 2 S)) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hD4 : 1 ≤ 4 * D := by linarith
  have aS := l2B_gr (hS.inH.mono (by norm_num) : InH 1 S)
  have lo := l1B_lo hD (mz_zOf_one hS) (piS_zOf 1 hS')
  have e12 : hnorm 1 (zOf 1 S) = hnorm 2 S := by
    have := hnorm_zOf 1 1 S
    norm_num at this
    exact this
  rw [e12] at lo
  have ht := (pos3_band2 hD4 (l2B_nrm hG) (l2B_nrm hF) aS aS lo (gr_slow hS') (gr_slow hS')).const_mul
    (by positivity : 0 ≤ 2 ^ 21 / |r| ^ 2)
  exact (form_le ht fun x => HtQ_one_term hr τ hS' hF' x).2

end OVNS.Quant.Metric

end
