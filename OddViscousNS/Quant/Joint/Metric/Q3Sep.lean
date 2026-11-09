import OddViscousNS.Quant.Joint.Metric.Q3Block

/-!
# The third correction: the third inverse (step J5, node N8)

`hi_last`: on the mask of `Q₃`, `P₃ > 16 J`, `K > 15 J`, `L > 7 J`: Body 42's "`L > 4J`, so the
old total separated `Q₃` mask covers the entire high-last ordinary and phase/noncommon terms".

`norm_source_le`: `‖T_sep‖ ≤ C q⁻¹ (1 + (P₁² + P₂² + P₃²)/J²)`.

`norm_O_le`: the third inverse gains `1/(q L)`: `|δ_lj| ≥ (3/4) L` on every exterior channel, "there
is no new denominator estimate across a zero phase".

`pos3_sep`: the classes of `Esep`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {D : ℝ} {x : I4}

/-- The support of the mask. -/
structure OnQ (D : ℝ) (x : I4) : Prop where
  a_le : absk x.2.1 ≤ D
  b_le : absk x.2.2.1 ≤ D
  c_le : absk x.2.2.2 ≤ D
  l_le : absk x.1 ≤ 2 * absk (x.1 - x.2.1 - x.2.2.1)
  k_le : absk (x.1 - x.2.1 - x.2.2.1) ≤ 2 * absk x.1
  c_gt : 16 * absk (inJ x) < absk x.2.2.2

lemma onQ_of_ne (h : muQ D x ≠ 0) : OnQ D x := by
  unfold muQ at h
  by_cases hm : absk x.2.1 ≤ D ∧ absk x.2.2.1 ≤ D ∧ absk x.2.2.2 ≤ D ∧
      absk x.1 ≤ 2 * absk (x.1 - x.2.1 - x.2.2.1) ∧ absk (x.1 - x.2.1 - x.2.2.1) ≤ 2 * absk x.1
  swap
  · simp [hm] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  by_contra hc
  rw [not_lt] at hc
  apply h
  have hJ := lt_two_pow_bnd (inJ x)
  have hle : absk x.2.2.2 ≤ 2 ^ (bnd (inJ x) + 5) := by
    have e : (2 : ℝ) ^ (bnd (inJ x) + 5) = 16 * 2 ^ (bnd (inJ x) + 1) := by ring
    rw [e]
    linarith
  have : lowM x.2.2.2 (inJ x) = 1 := chiM_one hle
  rw [this]
  simp

/-- The lengths on the mask. -/
lemma OnQ.lengths (h : OnQ D x) :
    15 * absk (inJ x) < absk (x.1 - x.2.1 - x.2.2.1) ∧ 7 * absk (inJ x) ≤ absk x.1 := by
  have e : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
    simp only [inJ]
    abel
  have h1 := absk_sub_le (x.1 - x.2.1 - x.2.2.1) (inJ x)
  have e2 : x.1 - x.2.1 - x.2.2.1 - inJ x = x.2.2.2 := by
    rw [← e]
    abel
  rw [e2] at h1
  have h2 := h.c_gt
  have h3 := h.k_le
  have h4 := absk_nonneg (inJ x)
  constructor <;> linarith

/-- The fine kernel of the source of `Q₃`: `(K² + P₁ P₂)/J²`. -/
def Efine (x : I4) : ℝ :=
  (absk (x.1 - x.2.1 - x.2.2.1) ^ 2 + absk x.2.1 * absk x.2.2.1) / absk (inJ x) ^ 2

lemma Efine_nonneg (x : I4) : 0 ≤ Efine x := by
  have h1 := absk_nonneg x.2.1
  have h2 := absk_nonneg x.2.2.1
  unfold Efine
  positivity

/-- The source of `Q₃`, with the fine kernel. -/
theorem norm_source_fine {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hx : Act₃ x)
    (t v w : V3) :
    ‖(famQ s r D).Sr x τ t v w‖ ≤ 2 ^ 33 / |r| * (‖t‖ * ‖v‖ * ‖w‖) * Efine x := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hE := Efine_nonneg x
  by_cases hm : muQ D x = 0
  · have : (famQ s r D).Sr x τ t v w = 0 := by
      change ((muQ D x : ℝ) : ℂ) • _ = 0
      rw [hm]
      ext1 y
      simp only [smul_apply, zero_apply, Complex.ofReal_zero, zero_smul]
    rw [this, norm_zero]
    positivity
  have hQ := onQ_of_ne hm
  obtain ⟨hK15, -⟩ := hQ.lengths
  obtain ⟨ha, hb, hc, hj⟩ := hx
  have hk2 : (x.1 - x.2.1 - x.2.2.1) 2 ≠ 0 := by
    have e : (x.1 - x.2.1 - x.2.2.1) 2 = inJ x 2 := by
      simp [inJ, hc]
    rwa [e]
  obtain ⟨-, -, hk0⟩ := fast_labels ha hb hk2
  have hj0 : inJ x ≠ 0 := fun h => hj (by rw [h]; rfl)
  have hJ1 := one_le_absk hj0
  have hK1 := one_le_absk hk0
  have hY := norm_Yq_le hs hr τ ha hb hk2 hQ.l_le hQ.k_le t v
  have ek : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
    simp only [inJ]
    abel
  have hL := norm_Lb_le s τ ek w
  have hw : wt s (x.1 - x.2.1 - x.2.2.1) (inJ x) ≤
      absk (x.1 - x.2.1 - x.2.2.1) ^ 2 / absk (inJ x) ^ 2 := by
    have h1 : 1 ≤ absk (x.1 - x.2.1 - x.2.2.1) / absk (inJ x) := by
      rw [one_le_div (by linarith)]
      linarith
    rcases hs with rfl | rfl
    · simp only [wt, pow_one, ← div_pow]
      have : absk (x.1 - x.2.1 - x.2.2.1) / absk (inJ x) ≤
          (absk (x.1 - x.2.1 - x.2.2.1) / absk (inJ x)) ^ 2 := by nlinarith only [h1]
      exact this
    · simp only [wt, ← div_pow]
      exact le_rfl
  have hw0 := wt_nonneg s (x.1 - x.2.1 - x.2.2.1) (inJ x)
  have hmu : ‖((muQ D x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (muQ_nonneg D x)]
    exact muQ_le_one D x
  have hV : 0 ≤ ‖t‖ * ‖v‖ := by positivity
  set K := absk (x.1 - x.2.1 - x.2.2.1) with hKd
  set J := absk (inJ x) with hJd
  set A := absk x.2.1 with hAd
  set B := absk x.2.2.1 with hBd
  have hK0 : 0 < K := by linarith
  have hJ0 : 0 < J := by linarith
  have hA0 : 0 ≤ A := absk_nonneg _
  have hB0 : 0 ≤ B := absk_nonneg _
  have hG : (K⁻¹ + A * B * K⁻¹ ^ 3) * (K * (K ^ 2 / J ^ 2)) = Efine x := by
    simp only [Efine, ← hKd, ← hJd, ← hAd, ← hBd]
    field_simp
  have hN : ‖Yq s r τ x.1 x.2.1 x.2.2.1 t v ∘L Lb s τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x) w‖ ≤
      2 ^ 33 / |r| * (‖t‖ * ‖v‖ * ‖w‖) * Efine x := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := mul_le_mul hY hL (norm_nonneg _) (by positivity)
    refine h1.trans ?_
    have e : 2 ^ 29 / |r| * (‖t‖ * ‖v‖) * (K⁻¹ + A * B * K⁻¹ ^ 3) *
        (16 * wt s (x.1 - x.2.1 - x.2.2.1) (inJ x) * K * ‖w‖) =
        2 ^ 33 / |r| * (‖t‖ * ‖v‖ * ‖w‖) *
          ((K⁻¹ + A * B * K⁻¹ ^ 3) * (K * wt s (x.1 - x.2.1 - x.2.2.1) (inJ x))) := by
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hG]
    gcongr
  change ‖((muQ D x : ℝ) : ℂ) • _‖ ≤ _
  rw [norm_smul]
  calc _ ≤ 1 * (2 ^ 33 / |r| * (‖t‖ * ‖v‖ * ‖w‖) * Efine x) :=
        mul_le_mul hmu hN (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- On the mask, the fine kernel against `Esep`. -/
lemma Efine_le_Esep (hQ : OnQ D x) : Efine x ≤ 2 * Esep x := by
  have hK := hQ.lengths.1
  have ek : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
    simp only [inJ]
    abel
  have hKJ := absk_add_le x.2.2.2 (inJ x)
  rw [ek] at hKJ
  by_cases hj0 : inJ x = 0
  · have h0 : absk (inJ x) = 0 := by rw [hj0]; simp [absk, absSq]
    have h1 := one_le_Esep x
    simp only [Efine, h0]
    norm_num
    linarith
  have hJ1 := one_le_absk hj0
  have hJ0 : 0 < absk (inJ x) := by linarith
  have e2 : Esep x = 1 + (absk x.2.1 ^ 2 + absk x.2.2.1 ^ 2 + absk x.2.2.2 ^ 2) / absk (inJ x) ^ 2 := by
    simp only [Esep, absk_sq]
  rw [e2]
  unfold Efine
  have hJ2 : 0 < absk (inJ x) ^ 2 := by positivity
  rw [div_le_iff₀ hJ2]
  have e3 : 2 * (1 + (absk x.2.1 ^ 2 + absk x.2.2.1 ^ 2 + absk x.2.2.2 ^ 2) / absk (inJ x) ^ 2) *
      absk (inJ x) ^ 2 = 2 * absk (inJ x) ^ 2 +
        2 * (absk x.2.1 ^ 2 + absk x.2.2.1 ^ 2 + absk x.2.2.2 ^ 2) := by
    field_simp
  rw [e3]
  set K := absk (x.1 - x.2.1 - x.2.2.1)
  set J := absk (inJ x)
  set A := absk x.2.1
  set B := absk x.2.2.1
  set C := absk x.2.2.2
  have hK0 : 0 ≤ K := absk_nonneg _
  have h3 : K ^ 2 ≤ (C + J) ^ 2 := pow_le_pow_left₀ hK0 hKJ 2
  nlinarith only [h3, sq_nonneg (A - B), sq_nonneg (J - C), sq_nonneg A, sq_nonneg B]

/-- The size of the source of `Q₃`. -/
theorem norm_source_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hx : Act₃ x)
    (t v w : V3) :
    ‖(famQ s r D).Sr x τ t v w‖ ≤ 2 ^ 34 / |r| * (‖t‖ * ‖v‖ * ‖w‖) * Esep x := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hE := Esep_nonneg x
  by_cases hm : muQ D x = 0
  · have : (famQ s r D).Sr x τ t v w = 0 := by
      change ((muQ D x : ℝ) : ℂ) • _ = 0
      rw [hm]
      ext1 y
      simp only [smul_apply, zero_apply, Complex.ofReal_zero, zero_smul]
    rw [this, norm_zero]
    positivity
  have hQ := onQ_of_ne hm
  refine (norm_source_fine hs hr τ hx t v w).trans ?_
  have hV : 0 ≤ ‖t‖ * ‖v‖ * ‖w‖ := by positivity
  calc _ ≤ 2 ^ 33 / |r| * (‖t‖ * ‖v‖ * ‖w‖) * (2 * Esep x) :=
        mul_le_mul_of_nonneg_left (Efine_le_Esep hQ) (by positivity)
    _ = _ := by ring

/-- The family of `Q₃` has the size of a three-leaf family. -/
theorem famQ_bd {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (D : ℝ) :
    (famQ s r D).Bd (2 ^ 34 / |r|) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  refine ⟨by positivity, fun x hx τ t v w => (norm_source_le hs hr τ hx t v w).trans ?_⟩
  obtain ⟨ha, hb, hc, hj⟩ := hx
  have hk2 : (x.1 - x.2.1 - x.2.2.1) 2 ≠ 0 := by
    have e : (x.1 - x.2.1 - x.2.2.1) 2 = inJ x 2 := by
      simp [inJ, hc]
    rwa [e]
  obtain ⟨hl0, -, -⟩ := fast_labels ha hb hk2
  have hL1 := one_le_absk hl0
  have h1 : 1 ≤ absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2 := by
    have := absk_nonneg x.2.1
    have := absk_nonneg x.2.2.1
    have := absk_nonneg x.2.2.2
    linarith
  have hE := Esep_le_E3 x
  have hE0 := Esep_nonneg x
  have hV : 0 ≤ ‖t‖ * ‖v‖ * ‖w‖ := by positivity
  calc 2 ^ 34 / |r| * (‖t‖ * ‖v‖ * ‖w‖) * Esep x
      = 2 ^ 34 / |r| * 1 * (‖t‖ * ‖v‖ * ‖w‖) * Esep x := by ring
    _ ≤ 2 ^ 34 / |r| * (absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2) *
        (‖t‖ * ‖v‖ * ‖w‖) * E3 x := by gcongr

/-- **The third inverse**: the block of `Q₃`, with its gain `1/(q L)`. -/
theorem norm_O_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hx : Act₃ x)
    (t v w : V3) :
    absk x.1 * ‖outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ t v w)‖ ≤
      2 ^ 37 / |r| ^ 2 * (‖t‖ * ‖v‖ * ‖w‖) * Esep x := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hE := Esep_nonneg x
  by_cases hm : muQ D x = 0
  · have : (famQ s r D).Sr x τ t v w = 0 := by
      change ((muQ D x : ℝ) : ℂ) • _ = 0
      rw [hm]
      ext1 y
      simp only [smul_apply, zero_apply, Complex.ofReal_zero, zero_smul]
    rw [this, outerInv_zero, norm_zero, mul_zero]
    positivity
  have hQ := onQ_of_ne hm
  obtain ⟨-, hL7⟩ := hQ.lengths
  have hS := norm_source_le (D := D) hs hr τ hx t v w
  obtain ⟨ha, hb, hc, hj⟩ := hx
  have hj0 : inJ x ≠ 0 := fun h => hj (by rw [h]; rfl)
  have hJ1 := one_le_absk hj0
  have hL : 0 < absk x.1 := by linarith
  have h2 : x.1 2 = inJ x 2 := by
    simp [inJ, ha, hb, hc]
  have hd : 3 / 4 * absk x.1 ≤ |absk (inJ x) - absk x.1| := by
    rw [abs_sub_comm]
    refine le_trans ?_ (le_abs_self _)
    linarith
  have h1 := norm_outerInv_sep hr h2 hj (H := Hx₃ x) (d := 3 / 4 * absk x.1) (by positivity) hd
    ((famQ s r D).Sr x τ t v w)
  have hV : 0 ≤ ‖t‖ * ‖v‖ * ‖w‖ := by positivity
  calc _ ≤ absk x.1 * (4 / (|r| * (3 / 4 * absk x.1)) *
        (2 ^ 34 / |r| * (‖t‖ * ‖v‖ * ‖w‖) * Esep x)) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) hL.le
        exact mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 16 / 3 * 2 ^ 34 / |r| ^ 2 * (‖t‖ * ‖v‖ * ‖w‖) * Esep x := by
        field_simp
        ring
    _ ≤ _ := by
        have : 0 ≤ 1 / |r| ^ 2 * (‖t‖ * ‖v‖ * ‖w‖) * Esep x := by positivity
        have e1 : 16 / 3 * 2 ^ 34 / |r| ^ 2 * (‖t‖ * ‖v‖ * ‖w‖) * Esep x =
            (16 / 3 * 2 ^ 34) * (1 / |r| ^ 2 * (‖t‖ * ‖v‖ * ‖w‖) * Esep x) := by ring
        have e2 : 2 ^ 37 / |r| ^ 2 * (‖t‖ * ‖v‖ * ‖w‖) * Esep x =
            2 ^ 37 * (1 / |r| ^ 2 * (‖t‖ * ‖v‖ * ‖w‖) * Esep x) := by ring
        rw [e1, e2]
        nlinarith only [this]

/-- The value of the classes of `Esep`. -/
def clsS (W₁ W₂ W₃ U₁ U₂ U₃ : ℝ) : ℝ :=
  W₁ * W₂ * W₃ + c4 * (U₁ * W₂ * W₃ + W₁ * U₂ * W₃ + W₁ * W₂ * U₃)

/-- **The classes of `Esep`.** -/
theorem pos3_sep {α β f₁ f₂ f₃ : Mode → ℝ} {A B W₁ W₂ W₃ U₁ U₂ U₃ : ℝ} (hα : L2B α A)
    (hβ : L2B β B) (h1 : L1B f₁ W₁) (h2 : L1B f₂ W₂) (h3 : L1B f₃ W₃) (u1 : L2B (up f₁) U₁)
    (u2 : L2B (up f₂) U₂) (u3 : L2B (up f₃) U₃) :
    SB (fun x => Phi₃ α β f₁ f₂ f₃ x * Esep x) (A * B * clsS W₁ W₂ W₃ U₁ U₂ U₃) := by
  have hb := hβ.in2
  have t0 : SB (Phi₃ α β f₁ f₂ f₃) (A * B * (W₁ * W₂ * W₃)) := pos3_I hα hβ h1 h2 h3
  have t4 : SB (Phi₃ α (in2 β) (up f₁) f₂ f₃) (A * (c4 * B) * (U₁ * W₂ * W₃)) :=
    pos3_II' hα hb u1 h2 h3
  have t5 : SB (Phi₃ α (in2 β) f₁ (up f₂) f₃) (A * (c4 * B) * (U₂ * W₁ * W₃)) :=
    SB.equiv swap12 (pos3_II' hα hb u2 h1 h3) (Phi₃_swap12 _ _ _ _ _)
  have t6 : SB (Phi₃ α (in2 β) f₁ f₂ (up f₃)) (A * (c4 * B) * (U₃ * W₁ * W₂)) :=
    SB.equiv swap23 (SB.equiv swap12 (pos3_II' hα hb u3 h1 h2) (Phi₃_swap12 _ _ _ _ _))
      (Phi₃_swap23 _ _ _ _ _)
  have h := ((t0.add t4).add t5).add t6
  have e : (fun x => Phi₃ α β f₁ f₂ f₃ x * Esep x) = fun x =>
      Phi₃ α β f₁ f₂ f₃ x + Phi₃ α (in2 β) (up f₁) f₂ f₃ x + Phi₃ α (in2 β) f₁ (up f₂) f₃ x +
        Phi₃ α (in2 β) f₁ f₂ (up f₃) x := by
    funext x
    simp only [Phi₃, Esep, in2, up]
    ring
  rw [e]
  refine h.mono_bd (le_of_eq ?_)
  simp only [clsS]
  ring

end OVNS.Quant.Metric

end
