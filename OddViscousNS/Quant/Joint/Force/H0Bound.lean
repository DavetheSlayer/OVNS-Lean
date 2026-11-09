import OddViscousNS.Quant.Joint.Force.H0Slot

/-!
# The size of the `h₀` derivative (step J5, node N12)

See `H0Slot.lean`.  `h0Y_le`: the slots of a family; `h0Part_one_le`, `h0Part_two_le`: the whole
derivative, `|h0Part σ| ≤ x e_σ d_σ + y e_σ²`; `h0Part_young_one`, `h0Part_young_two`: `(8.10)`;
`h0Part_source_one`: the printed companion `P_F (1 + B_S) ‖h₀‖₁/q` of `N b_F`; `companion_clip`,
`h0_mass_clip`: the mass on any subinterval of the piece, by the actual `L²` history of `h₀`;
`joint1_full_le`, `joint2_full_le`: the right sides on a joint piece.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}

/-! ### The slots of `X₂`, `Z` -/

/-- **The direction `h₀` in a family**, at the weight of the family. -/
theorem h0Y_le {𝔉 : Fam} {ρ : I3 → ℝ} {K₁ K₂ : ℝ} {s : ℕ} (hs : s = 1 ∨ s = 2)
    (hB : 𝔉.Bd r ρ K₁ K₂) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    ‖h0Y 𝔉 s r g y u‖ ≤ 12 * c4 * K₁ * (hnorm 1 (hp r g y u) *
      (wiener (Sp r g y u) + c4 * hnorm 2 (Sp r g y u))) * hnorm s (Fp r g y u) ^ 2 := by
  have hx := actual_adm h hu huT
  have h2 : ((s : ℕ) : ℝ) ≤ 2 := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨z1, z2⟩ := l2_zOf (hx.PiF.inH.mono h2) hx.PiF.mean
  obtain ⟨hm, -, hsl⟩ := hp_facts h hr hu huT
  obtain ⟨-, b1, -, b2⟩ := Fam.form_dir (τ := r * u) (S := Sp r g y u) (z := zp s r g y u) hB
    hm.inH hm.mean hsl hx.PiS.mz (Fam.PiS_Sp r g y u) z1 (Fam.PiF_zp s r g y u)
  have e1 : l2n (zp s r g y u) = hnorm s (Fp r g y u) := z2
  rw [e1] at b1 b2
  obtain ⟨c1, c2⟩ := cls2_dir (hnorm 1 (hp r g y u)) (wiener (Sp r g y u)) (hnorm 2 (Sp r g y u))
  rw [c1] at b1
  rw [c2] at b2
  unfold h0Y
  refine (norm_add_le _ _).trans ?_
  have e2 : 12 * c4 * K₁ * (hnorm 1 (hp r g y u) *
      (wiener (Sp r g y u) + c4 * hnorm 2 (Sp r g y u))) * hnorm s (Fp r g y u) ^ 2 =
    2 * K₁ * (hnorm s (Fp r g y u) * hnorm s (Fp r g y u) * (3 * c4 * (hnorm 1 (hp r g y u) *
      (wiener (Sp r g y u) + c4 * hnorm 2 (Sp r g y u))))) +
    2 * K₁ * (hnorm s (Fp r g y u) * hnorm s (Fp r g y u) * (3 * c4 * (hnorm 1 (hp r g y u) *
      (wiener (Sp r g y u) + c4 * hnorm 2 (Sp r g y u))))) := by ring
  rw [e2]
  exact add_le_add b1 b2

/-- The two families: `½ ‖X₂‖ + ½ ‖Z‖`. -/
theorem h0Y_both_le {s : ℕ} (hs : s = 1 ∨ s = 2) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    1 / 2 * ‖h0Y (famX2 s r) s r g y u‖ + 1 / 2 * ‖h0Y (famZ s r) s r g y u‖ ≤
      2 ^ 19 * c4 / |r| * (h0Bd φ r g y u *
        (wiener (Sp r g y u) + c4 * hnorm 2 (Sp r g y u))) * hnorm s (Fp r g y u) ^ 2 := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hc := c4_pos
  have b1 := h0Y_le hs (famX2_bd hs hr) h hr hu huT
  have b2 := h0Y_le hs (famZ_bd hs hr) h hr hu huT
  set f := hnorm 1 (hp r g y u) with hf
  set w := wiener (Sp r g y u) + c4 * hnorm 2 (Sp r g y u) with hw
  set e := hnorm s (Fp r g y u) ^ 2 with he
  have hw0 : 0 ≤ w := add_nonneg (wiener_nonneg _) (mul_nonneg hc.le (hnorm_nonneg _ _))
  have he0 : 0 ≤ e := sq_nonneg _
  have hf0 : 0 ≤ f := hnorm_nonneg _ _
  have hfb : f ≤ h0Bd φ r g y u := (hp_one_le h hr hu huT).2
  have hX : 0 ≤ c4 / |r| * (f * w) * e := by positivity
  have e1 : 1 / 2 * (12 * c4 * (39424 / |r|) * (f * w) * e) +
      1 / 2 * (12 * c4 * (19712 / |r|) * (f * w) * e) = 354816 * (c4 / |r| * (f * w) * e) := by
    ring
  have e2 : 2 ^ 19 * c4 / |r| * (f * w) * e = 524288 * (c4 / |r| * (f * w) * e) := by ring
  have h3 : 2 ^ 19 * c4 / |r| * (f * w) * e ≤ 2 ^ 19 * c4 / |r| * (h0Bd φ r g y u * w) * e := by
    gcongr
  linarith

/-! ### The whole derivative -/

private lemma three_abs {a b : ℝ} {x y : ℂ} (ha : |a| ≤ b) :
    |a + 1 / 2 * x.re + 1 / 2 * y.re| ≤ b + (1 / 2 * ‖x‖ + 1 / 2 * ‖y‖) := by
  have h1 := abs_le.1 (Complex.abs_re_le_norm x)
  have h2 := abs_le.1 (Complex.abs_re_le_norm y)
  have h3 := abs_le.1 ha
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **The whole `h₀` derivative at weight one**: `x a_F b_F + y a_F²`, at every time. -/
theorem h0Part_one_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    |h0Part 1 r g y u| ≤ 2 ^ 10 * h0Bd φ r g y u / |r| *
        (fastNorm 1 r g y u * fastNorm 2 r g y u) +
      2 ^ 19 * c4 / |r| * (h0Bd φ r g y u *
        (wiener (Sp r g y u) + c4 * hnorm 2 (Sp r g y u))) * fastNorm 1 r g y u ^ 2 := by
  have b1 := h0_slot_one (φ := φ) h hr hu huT
  have b2 := h0Y_both_le (φ := φ) (s := 1) (Or.inl rfl) h hr hu huT
  simp only [Nat.cast_one] at b2
  unfold h0Part
  simp only [Nat.cast_one]
  exact (three_abs b1).trans (add_le_add le_rfl b2)

/-- **The whole `h₀` derivative at weight two**: `x b_F c_F + y b_F²`, at an `H³` time. -/
theorem h0Part_two_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) :
    |h0Part 2 r g y u| ≤ 2 * H2.cSrc * h0Bd φ r g y u / |r| *
        (fastNorm 2 r g y u * fastNorm 3 r g y u) +
      2 ^ 19 * c4 / |r| * (h0Bd φ r g y u *
        (wiener (Sp r g y u) + c4 * hnorm 2 (Sp r g y u))) * fastNorm 2 r g y u ^ 2 := by
  have b1 := h0_slot_two (φ := φ) h hr hu huT hF3
  have b2 := h0Y_both_le (φ := φ) (s := 2) (Or.inr rfl) h hr hu huT
  simp only [Nat.cast_ofNat] at b2
  unfold h0Part
  simp only [Nat.cast_ofNat]
  exact (three_abs b1).trans (add_le_add le_rfl b2)

/-! ### Young, at the caps -/

/-- `κ = 1 + W + c₄ B`: the printed `1 + b`. -/
def kapH0 (caps : Caps) : ℝ := 1 + cp caps.WS + c4 * cp caps.BS

/-- The constant of `(8.10)`. -/
def Ch0 : ℝ := 2 ^ 10 + 2 ^ 8 * c4 + 2 ^ 19 * c4

lemma Ch0_pos : 0 < Ch0 := by
  have := c4_pos
  unfold Ch0
  positivity

lemma kapH0_pos (caps : Caps) : 0 < kapH0 caps := by
  have := c4_pos
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.BS
  unfold kapH0
  positivity

/-- The scalar step: `(x + y) e d` at the caps. -/
private lemma scalar_cap {A C2 h q e d w W B c : ℝ} (hq : 0 < q) (hh : 0 ≤ h) (he : 0 ≤ e)
    (hed : e ≤ d) (hc : 0 < c) (hW : 0 ≤ W) (hB : 0 ≤ B) (hA : 0 ≤ A) (hC2 : 0 ≤ C2)
    (hw : w ≤ W + c * B) (hw0 : 0 ≤ w) :
    A * h / q * (e * d) + C2 * c / q * (h * w) * e ^ 2 ≤
      (A + C2 * c) * (1 + W + c * B) * h / q * (e * d) := by
  have hed' : e ^ 2 ≤ e * d := by nlinarith only [he, hed]
  have hcB : 0 ≤ c * B := mul_nonneg hc.le hB
  have hk : w ≤ 1 + W + c * B := by linarith only [hw]
  have hk1 : 1 ≤ 1 + W + c * B := by linarith only [hW, hcB]
  have hed0 : 0 ≤ e * d := by nlinarith only [he, hed]
  have hx : 0 ≤ h / q := by positivity
  have t1 : A * h / q * (e * d) ≤ A * (1 + W + c * B) * h / q * (e * d) := by
    have h1 : A * h / q ≤ A * (1 + W + c * B) * h / q := by
      have e1 : A * h / q = A * (h / q) := by ring
      have e2 : A * (1 + W + c * B) * h / q = A * (1 + W + c * B) * (h / q) := by ring
      rw [e1, e2]
      gcongr
      nlinarith only [hA, hk1]
    gcongr
  have t2 : C2 * c / q * (h * w) * e ^ 2 ≤ C2 * c * (1 + W + c * B) * h / q * (e * d) := by
    have e1 : C2 * c / q * (h * w) * e ^ 2 = C2 * c * (h / q) * (w * e ^ 2) := by ring
    have e2 : C2 * c * (1 + W + c * B) * h / q * (e * d) =
        C2 * c * (h / q) * ((1 + W + c * B) * (e * d)) := by ring
    rw [e1, e2]
    have h3 : w * e ^ 2 ≤ (1 + W + c * B) * (e * d) :=
      mul_le_mul hk hed' (sq_nonneg _) (by linarith)
    gcongr
  have e3 : (A + C2 * c) * (1 + W + c * B) * h / q * (e * d) =
      A * (1 + W + c * B) * h / q * (e * d) + C2 * c * (1 + W + c * B) * h / q * (e * d) := by
    ring
  linarith

/-- The Young step. -/
private lemma young_ed {x e d ζ : ℝ} (hζ : 0 < ζ) :
    x * (e * d) ≤ ζ * d ^ 2 + x ^ 2 / (4 * ζ) * e ^ 2 := by
  have h1 : 0 ≤ (2 * ζ * d - x * e) ^ 2 / (4 * ζ) := by positivity
  have e1 : (2 * ζ * d - x * e) ^ 2 / (4 * ζ) =
      ζ * d ^ 2 - x * (e * d) + x ^ 2 / (4 * ζ) * e ^ 2 := by
    field_simp
    ring
  linarith

variable {s t ζ : ℝ} {caps : Caps}

/-- The size of the slow leaves on a prefix. -/
private lemma slow_caps (hP : OnPrefix caps r g y s t) (hu : u ∈ Icc s t) :
    wiener (Sp r g y u) + c4 * hnorm 2 (Sp r g y u) ≤ cp caps.WS + c4 * cp caps.BS := by
  have h1 : wiener (Sp r g y u) ≤ cp caps.WS := (hP.1 u hu).2.2.2.2.trans (le_cp _)
  have h2 : hnorm 2 (Sp r g y u) ≤ cp caps.BS := (hP.1 u hu).2.2.2.1.trans (le_cp _)
  have := mul_le_mul_of_nonneg_left h2 c4_pos.le
  linarith

/-- The total coefficient at weight one, at the caps. -/
theorem h0Part_ed_one (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hP : OnPrefix caps r g y s t)
    (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hu : u ∈ Icc s t) :
    |h0Part 1 r g y u| ≤ Ch0 * kapH0 caps * h0Bd φ r g y u / |r| *
      (fastNorm 1 r g y u * fastNorm 2 r g y u) := by
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT : ENNReal.ofReal u < Ty := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) ht
  have hx := actual_adm h hu0 huT
  have hq : 0 < |r| := abs_pos.2 hr
  have hc := c4_pos
  have hh0 : 0 ≤ h0Bd φ r g y u := (hnorm_nonneg _ _).trans (hp_one_le h hr hu0 huT).2
  have hab : fastNorm 1 r g y u ≤ fastNorm 2 r g y u := hnorm_mono (by norm_num) hx.PiF.inH
  have hw := slow_caps hP hu
  have hw0 : 0 ≤ wiener (Sp r g y u) + c4 * hnorm 2 (Sp r g y u) :=
    add_nonneg (wiener_nonneg _) (mul_nonneg hc.le (hnorm_nonneg _ _))
  have h1 := scalar_cap (A := 2 ^ 10) (C2 := 2 ^ 19) hq hh0 (hnorm_nonneg _ _) hab hc
    (cp_nonneg caps.WS) (cp_nonneg caps.BS) (by norm_num) (by norm_num) hw hw0
  refine (h0Part_one_le h hr hu0 huT).trans (h1.trans ?_)
  have hed : 0 ≤ fastNorm 1 r g y u * fastNorm 2 r g y u :=
    mul_nonneg (hnorm_nonneg _ _) (hnorm_nonneg _ _)
  have hk := kapH0_pos caps
  refine mul_le_mul_of_nonneg_right ?_ hed
  have e1 : ((2 : ℝ) ^ 10 + 2 ^ 19 * c4) ≤ Ch0 := by
    unfold Ch0
    nlinarith only [hc]
  have e2 : (1 : ℝ) + cp caps.WS + c4 * cp caps.BS = kapH0 caps := rfl
  rw [e2]
  gcongr

/-- The total coefficient at weight two, at the caps. -/
theorem h0Part_ed_two (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hP : OnPrefix caps r g y s t)
    (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hu : u ∈ Icc s t) (hF3 : InH 3 (Fp r g y u)) :
    |h0Part 2 r g y u| ≤ Ch0 * kapH0 caps * h0Bd φ r g y u / |r| *
      (fastNorm 2 r g y u * fastNorm 3 r g y u) := by
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT : ENNReal.ofReal u < Ty := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) ht
  have hq : 0 < |r| := abs_pos.2 hr
  have hc := c4_pos
  have hh0 : 0 ≤ h0Bd φ r g y u := (hnorm_nonneg _ _).trans (hp_one_le h hr hu0 huT).2
  have hbc : fastNorm 2 r g y u ≤ fastNorm 3 r g y u := hnorm_mono (by norm_num) hF3
  have hw := slow_caps hP hu
  have hw0 : 0 ≤ wiener (Sp r g y u) + c4 * hnorm 2 (Sp r g y u) :=
    add_nonneg (wiener_nonneg _) (mul_nonneg hc.le (hnorm_nonneg _ _))
  have hS0 := H2.cSrc_nonneg
  have h1 := scalar_cap (A := 2 * H2.cSrc) (C2 := 2 ^ 19) hq hh0 (hnorm_nonneg _ _) hbc hc
    (cp_nonneg caps.WS) (cp_nonneg caps.BS) (by positivity) (by norm_num) hw hw0
  refine (h0Part_two_le h hr hu0 huT hF3).trans (h1.trans ?_)
  have hed : 0 ≤ fastNorm 2 r g y u * fastNorm 3 r g y u :=
    mul_nonneg (hnorm_nonneg _ _) (hnorm_nonneg _ _)
  have hk := kapH0_pos caps
  refine mul_le_mul_of_nonneg_right ?_ hed
  have e1 : (2 * H2.cSrc + 2 ^ 19 * c4) ≤ Ch0 := by
    unfold Ch0 H2.cSrc
    nlinarith only [hc]
  have e2 : (1 : ℝ) + cp caps.WS + c4 * cp caps.BS = kapH0 caps := rfl
  rw [e2]
  gcongr

/-- **`(8.10)` at weight one.** -/
theorem h0Part_young_one (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hP : OnPrefix caps r g y s t)
    (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hu : u ∈ Icc s t) (hζ : 0 < ζ) :
    |h0Part 1 r g y u| ≤ ζ * fastNorm 2 r g y u ^ 2 +
      (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * ζ) * fastNorm 1 r g y u ^ 2 :=
  (h0Part_ed_one h hr hP hs ht hu).trans (young_ed hζ)

/-- **`(8.10)` at weight two**, at an `H³` time. -/
theorem h0Part_young_two (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hP : OnPrefix caps r g y s t)
    (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hu : u ∈ Icc s t) (hF3 : InH 3 (Fp r g y u))
    (hζ : 0 < ζ) :
    |h0Part 2 r g y u| ≤ ζ * fastNorm 3 r g y u ^ 2 +
      (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * ζ) * fastNorm 2 r g y u ^ 2 :=
  (h0Part_ed_two h hr hP hs ht hu hF3).trans (young_ed hζ)

/-- **The printed companion**: at weight one the whole derivative is `N b_F`,
`N = Ch0 P_F κ ‖h₀‖₁/q`. -/
theorem h0Part_source_one (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hP : OnPrefix caps r g y s t) (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hu : u ∈ Icc s t) :
    |h0Part 1 r g y u| ≤ Ch0 * kapH0 caps * cp caps.PF * h0Bd φ r g y u / |r| *
      fastNorm 2 r g y u := by
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT : ENNReal.ofReal u < Ty := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) ht
  have hq : 0 < |r| := abs_pos.2 hr
  have hh0 : 0 ≤ h0Bd φ r g y u := (hnorm_nonneg _ _).trans (hp_one_le h hr hu0 huT).2
  have ha : fastNorm 1 r g y u ≤ cp caps.PF := (hP.1 u hu).1.trans (le_cp _)
  have hb := hnorm_nonneg 2 (PiF (actual r g y u))
  have hk : 0 ≤ Ch0 * kapH0 caps * h0Bd φ r g y u / |r| :=
    div_nonneg (mul_nonneg (mul_nonneg Ch0_pos.le (kapH0_pos caps).le) hh0) hq.le
  refine (h0Part_ed_one h hr hP hs ht hu).trans ?_
  have h3 := mul_le_mul_of_nonneg_right ha hb
  have h4 := mul_le_mul_of_nonneg_left h3 hk
  have e : Ch0 * kapH0 caps * cp caps.PF * h0Bd φ r g y u / |r| * fastNorm 2 r g y u =
      Ch0 * kapH0 caps * h0Bd φ r g y u / |r| * (cp caps.PF * fastNorm 2 r g y u) := by ring
  rw [e]
  exact h4

/-! ### The mass -/

/-- **The mass of `h₀` on any subinterval.** -/
theorem companion_clip (h : ActualSol μ φ r g y Ty) {κ u₁ u₂ : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 4) (hP : OnPrefix caps r g y s t)
    (hx : hLc φ caps / |r| ≤ 1 / 8) (hz : hQc φ / |r| ^ 2 ≤ 1 / 8) (hr : r ≠ 0) (h1 : s ≤ u₁)
    (h2 : u₁ ≤ u₂) (h3 : u₂ ≤ t) :
    (∫ u in u₁..u₂, (κ * h0Bd φ r g y u / |r|) ^ 2) ≤ (κ * H0c φ caps / |r|) ^ 2 := by
  refine le_trans ?_ (companion_le h hs hst ht hlen hP hx hz hr)
  obtain ⟨hI, -⟩ := h0_sq_le (φ := φ) h hs hst ht hlen hP
  have e : (fun u => (κ * h0Bd φ r g y u / |r|) ^ 2) =
      fun u => (κ / |r|) ^ 2 * h0Bd φ r g y u ^ 2 := by
    funext u
    ring
  have hI2 : IntervalIntegrable (fun u => (κ * h0Bd φ r g y u / |r|) ^ 2) volume s t := by
    rw [e]
    exact hI.const_mul _
  exact intervalIntegral.integral_mono_interval h1 h2 h3
    (Filter.Eventually.of_forall fun u => sq_nonneg _) hI2

/-- **The Young mass on any subinterval**: `(Ch0 κ H₀/q)²/(4ζ)`, the printed `O(q⁻² R⁶ L)`. -/
theorem h0_mass_clip (h : ActualSol μ φ r g y Ty) {u₁ u₂ D M : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 4) (hP : OnPrefix caps r g y s t) (hD : 0 ≤ D)
    (hM : 0 ≤ M) (hq : force1Q φ D M caps ≤ |r|) (hζ : 0 < ζ) (h1 : s ≤ u₁) (h2 : u₁ ≤ u₂)
    (h3 : u₂ ≤ t) :
    (∫ u in u₁..u₂, (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * ζ)) ≤
      (Ch0 * kapH0 caps * H0c φ caps / |r|) ^ 2 / (4 * ζ) := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  obtain ⟨hq1, hx, hz⟩ := force1Q_source hφ hM hD hq
  have hr : r ≠ 0 := abs_pos.1 (by linarith)
  have hc := companion_clip (κ := Ch0 * kapH0 caps) h hs hst ht hlen hP hx hz hr h1 h2 h3
  rw [intervalIntegral.integral_div]
  exact div_le_div_of_nonneg_right hc (by positivity)

/-! ### On a joint piece -/

variable {M C ex R D : ℝ} {q : Caps → ℝ} {near : Caps → ℝ → Prop}
  {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop}

/-- **`joint1RHS` on a joint piece**, the force and `h₀` paid: `joint₁R` is what is left. -/
theorem joint1_full_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hp' : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (hD : 1 ≤ D)
    (hq : force1Q φ D M caps ≤ q caps) (hζ : 0 < ζ) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), joint1RHS r g y u ≤ joint1R r g y u +
      (2 * hBd φ r g y u * fastNorm 2 r g y u + 24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) +
      (ζ * fastNorm 2 r g y u ^ 2 +
        (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * ζ) * fastNorm 1 r g y u ^ 2) := by
  obtain ⟨h1, -, -⟩ := force1_joint h hp' hD hq
  filter_upwards [ae_joint_full h hr hp'.hs hp'.hst hp'.ht, ae_restrict_mem measurableSet_Icc]
    with u hu hm
  rw [hu.1]
  have h2 := (le_abs_self _).trans ((forceS_one_le r g y u).trans (h1 u hm))
  have h3 := (le_abs_self _).trans
    (h0Part_young_one (φ := φ) h hr hp'.onPrefix hp'.hs hp'.ht hm hζ)
  linarith

/-- **`joint2RHS` on a joint piece**, the force and `h₀` paid: `joint₂R` is what is left. -/
theorem joint2_full_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hp' : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (h0 : 0 ≤ C * ex)
    (hR : 0 ≤ R) (hD : 1 ≤ D) (hq : force2Q φ D M C ex R caps ≤ q caps) (hζ : 0 < ζ) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), joint2RHS r g y u ≤ joint2R r g y u +
      (1 / 64 * fastNorm 3 r g y u ^ 2 + 16 * GF φ D M r g y caps u) +
      (ζ * fastNorm 3 r g y u ^ 2 +
        (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * ζ) * fastNorm 2 r g y u ^ 2) := by
  obtain ⟨-, -, h1⟩ := force2_joint h hp' h0 hR hD hq
  filter_upwards [h1, ae_joint_full h hr hp'.hs hp'.hst hp'.ht,
    ae_restrict_mem measurableSet_Icc, OVNS.Quant.H2.ae_inH3_split h hp'.hs hp'.hst hp'.ht]
    with u hb hu hm h3F
  rw [hu.2]
  have h2 := (le_abs_self _).trans ((forceS_two_le r g y u).trans hb)
  have h3 := (le_abs_self _).trans
    (h0Part_young_two (φ := φ) h hr hp'.onPrefix hp'.hs hp'.ht hm h3F.1 hζ)
  linarith

end OVNS.Quant.Metric

end
