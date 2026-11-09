import OddViscousNS.Quant.Joint.Metric.Block

/-!
# The block of `X₂` at both weights, and the ordinary sector (step J5, node N3)

Body 36 "at both original weights": the block of `X₂` of Body 12 (15) at `s = 1`, and the envelope
of the bracket in the ordinary sector `M < 4 max(L, J)`.

* `norm_X1b_one_le`: `‖X₁(v)_{kj}‖ ≤ (20/q) ‖v‖ [K/J + J/K]`: the numerator of `inner_X1b` at
  `s = 1` is `(v − u)[l(v + u) − uv]/(KQ)`, the coefficient `5/2` of Body 12 §6, paid on eight
  channels.
* `norm_X2b_le`: `‖X₂‖ ≤ (2816/q) (M/Σ) f_a g_b Br`, at `s = 1, 2`, **with the bracket of weight two
  on both**: the bracket of weight one is at most `3/2` of it (`Br₁_le`).  This is Body 36: "For
  `s = 1` a ratio and its reciprocal are bounded by the squared-ratio bounds, and
  `M²/(LJ) ≤ 1 + M⁴/(L²J²)`".
* `ord_bracket_le`: `(M/Σ) Br ≤ 68 [1/J + 1/L + (P₁+P₂)/J² + (P₁+P₂)/L²]` for `M < 4 max(L, J)`.
* `high_bracket_le`: `(M/Σ) Br ≤ (32/9) M³/(L²J²)` at `M ≥ 4 max(L, J)`.
-/

open scoped ComplexConjugate

open OVNS.Quant.H2 (norm_metSym_mul_le)

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. `X₁` at weight one -/

/-- **The cancellation at `s = 1`** (Body 12 §6: "The `s1` coefficient `5/2` is smaller"). -/
theorem X1b_coeff_one_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (a b c : Sgn) {p k j : Mode} (hk : p + j = k)
    (hp : p 2 = 0) (hj : j 2 ≠ 0) :
    ‖metM r τ a b c p j‖ * |wt 1 k j * (sg a * absk p - sg b * absk j) -
        wt 1 j k * (sg a * absk p - sg c * absk k)| ≤
      5 / 2 / |r| * (absk k / absk j + absk j / absk k) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hj0 : j ≠ 0 := fun h => hj (by simp [h])
  have hk2 : k 2 = j 2 := by rw [← hk]; simp [hp]
  have hk0 : k ≠ 0 := fun h => hj (by rw [← hk2, h]; rfl)
  have hQ : 0 < absk j := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk0)
  have hR : 0 ≤ 5 / 2 / |r| * (absk k / absk j + absk j / absk k) := by positivity
  unfold metM
  split_ifs with h
  swap
  · rw [norm_zero, zero_mul]
    exact hR
  set l := sg a * absk p with hl
  set u := sg b * absk j with hu
  set v := sg c * absk k with hv
  have hsg : ∀ (e : Sgn) (x : ℝ), 0 ≤ x → |sg e * x| = x := fun e x hx => by
    rw [abs_mul, abs_of_nonneg hx]
    cases e <;> simp [sg]
  have hsq : ∀ (e : Sgn) (x : ℝ), (sg e * x) ^ 2 = x ^ 2 := fun e x => by
    rw [mul_pow, show sg e ^ 2 = 1 by cases e <;> simp [sg], one_mul]
  have hu2 : u ^ 2 = absk j ^ 2 := hsq _ _
  have hv2 : v ^ 2 = absk k ^ 2 := hsq _ _
  have hnum : wt 1 k j * (l - u) - wt 1 j k * (l - v) =
      (v - u) * (l * (v + u) - u * v) / (absk k * absk j) := by
    rw [eq_div_iff (by positivity)]
    simp only [wt, pow_one]
    have e : (absk k / absk j * (l - u) - absk j / absk k * (l - v)) * (absk k * absk j) =
        absk k ^ 2 * (l - u) - absk j ^ 2 * (l - v) := by
      field_simp
    rw [e, ← hu2, ← hv2]
    ring
  have hP : absk p ≤ absk k + absk j := by
    have := absk_sub_le k j
    rwa [show k - j = p by rw [← hk]; abel] at this
  have hn : |l * (v + u) - u * v| ≤ absk p * (absk k + absk j) + absk k * absk j := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, hsg a _ (absk_nonneg p)]
      refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (absk_nonneg p)
      rw [hsg c _ (absk_nonneg k), hsg b _ (absk_nonneg j)]
    · rw [abs_mul, hsg b _ (absk_nonneg j), hsg c _ (absk_nonneg k)]
      linarith [mul_comm (absk k) (absk j)]
  have hn' : |l * (v + u) - u * v| ≤ 5 / 2 * (absk k ^ 2 + absk j ^ 2) := by
    have h1 := absk_nonneg k
    have h2 := absk_nonneg j
    have h3 := absk_nonneg p
    have h4 : absk p * (absk k + absk j) ≤ (absk k + absk j) * (absk k + absk j) :=
      mul_le_mul_of_nonneg_right hP (by positivity)
    nlinarith [sq_nonneg (absk k - absk j)]
  have hm := norm_metSym_mul_le hr τ a b c hp hj h.2.2
  rw [hk] at hm
  rw [hnum, abs_div, abs_mul, abs_of_pos (by positivity : 0 < absk k * absk j)]
  set m := ‖metSym r τ a b c p j‖
  have hm0 : 0 ≤ m := norm_nonneg _
  calc m * (|v - u| * |l * (v + u) - u * v| / (absk k * absk j))
      = (m * |v - u|) * (|l * (v + u) - u * v| / (absk k * absk j)) := by ring
    _ ≤ (1 / |r|) * ((5 / 2 * (absk k ^ 2 + absk j ^ 2)) / (absk k * absk j)) :=
        mul_le_mul hm (div_le_div_of_nonneg_right hn' (by positivity)) (by positivity)
          (by positivity)
    _ = _ := by
        field_simp

/-- **The first correction at weight one** (Body 12 (11), `s = 1`):
`‖X₁(v)_{kj}‖ ≤ (20/q) ‖v‖ [K/J + J/K]`. -/
theorem norm_X1b_one_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {p k j : Mode} (hk : p + j = k)
    (hp : p 2 = 0) (hj : j 2 ≠ 0) (v : V3) :
    ‖X1b 1 r τ p k j v‖ ≤ 20 / |r| * ‖v‖ * (absk k / absk j + absk j / absk k) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hj0 : j ≠ 0 := fun h => hj (by simp [h])
  have hk2 : k 2 = j 2 := by rw [← hk]; simp [hp]
  have hk0 : k ≠ 0 := fun h => hj (by rw [← hk2, h]; rfl)
  have hJ := absk_nonneg j
  have hK := absk_nonneg k
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  refine norm_le_of_inner (by positivity) fun Z => ?_
  rw [inner_X1b 1 r τ hk hj0 hk0]
  set E := 5 / 2 / |r| * (absk k / absk j + absk j / absk k) * (‖v‖ * ‖w‖ * ‖Z‖) with hE
  have hterm : ∀ a b c, ‖metM r τ a b c p j *
      (((wt 1 k j * (sg a * absk p - sg b * absk j) -
        wt 1 j k * (sg a * absk p - sg c * absk k) : ℝ) : ℂ) * elt a b c p k j v w Z)‖ ≤ E := by
    intro a b c
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
    exact mul_le_mul (X1b_coeff_one_le hr τ a b c hk hp hj) (norm_elt_le _ _ _ _ _ _ _ _ _)
      (norm_nonneg _) (by positivity)
  refine (norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
    norm_sum_le_of_le _ fun c _ => hterm a b c).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, hE]
  push_cast
  ring

/-! ### B. `X₂` at weight one -/

/-- The bracket of Body 12 (15) at weight one, in the lengths. -/
def Br₁ (L M J : ℝ) : ℝ := L / J + 2 * M ^ 2 / (L * J) + J / L

/-- The bracket of weight one against the bracket of weight two (Body 36, Body 12 §7). -/
lemma Br₁_le {L M J : ℝ} (hL : 0 < L) (hJ : 0 < J) :
    Br₁ L M J ≤ 3 / 2 * Br (L ^ 2) (M ^ 2) (J ^ 2) := by
  set R := L / J with hR
  set x := M ^ 2 / (L * J) with hx
  have hR0 : 0 < R := by positivity
  have e1 : Br₁ L M J = R + 2 * x + R⁻¹ := by
    simp only [Br₁, hR, hx, inv_div]
    ring
  have e2 : Br (L ^ 2) (M ^ 2) (J ^ 2) = R ^ 2 + 2 * x ^ 2 + (R⁻¹) ^ 2 := by
    simp only [Br, hR, hx, inv_div]
    field_simp
  rw [e1, e2]
  have h1 : R * R⁻¹ = 1 := mul_inv_cancel₀ hR0.ne'
  have h2 : 0 < R⁻¹ := inv_pos.2 hR0
  nlinarith [sq_nonneg (R - R⁻¹), sq_nonneg (x - 1), sq_nonneg (R - 1), sq_nonneg (R⁻¹ - 1),
    sq_nonneg (R + R⁻¹ - 2), sq_nonneg x]

/-- `‖X₂‖ ≤ (1280/q) (M/Σ) f_a g_b [L/J + 2M²/(LJ) + J/L]`, Body 12 (15) at `s = 1`. -/
theorem norm_X2b_one_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖X2b 1 r τ f g l a b‖ ≤ 1280 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) *
      (‖f a‖ * ‖g b‖) * Br₁ (absk l) (absk (l - a)) (absk (l - a - b)) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hm2 : (l - a) 2 ≠ 0 := fun h => hj (by simp only [Pi.sub_apply] at h ⊢; simpa [hb] using h)
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hJ : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hH := heat4_pos (l := l) hj0 a b
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  have h1 := norm_X1b_one_le hr τ e1 ha hm2 (f a)
  have h2 := norm_Lb_le 1 τ e2 (g b)
  have h3 := norm_Lad_le 1 τ e1 (f a)
  have h4 := norm_X1b_one_le hr τ e2 hb hj (g b)
  simp only [wt, pow_one] at h2 h3
  set L := absk l
  set M := absk (l - a)
  set J := absk (l - a - b)
  have ha0 := norm_nonneg (f a)
  have hb0 := norm_nonneg (g b)
  have hT : ‖twoRoot 1 r τ f g l a b‖ ≤ 320 / |r| * M * (‖f a‖ * ‖g b‖) * Br₁ L M J := by
    have ht1 : ‖X1b 1 r τ a l (l - a) (f a) ∘L Lb 1 τ b (l - a) (l - a - b) (g b)‖ ≤
        20 / |r| * ‖f a‖ * (L / M + M / L) * (16 * (M / J) * M * ‖g b‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
    have ht2 : ‖Lad 1 τ a l (l - a) (f a) ∘L X1b 1 r τ b (l - a) (l - a - b) (g b)‖ ≤
        16 * (M / L) * M * ‖f a‖ * (20 / |r| * ‖g b‖ * (M / J + J / M)) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul h3 h4 (norm_nonneg _) (by positivity))
    refine (norm_add_le _ _).trans ((add_le_add ht1 ht2).trans (le_of_eq ?_))
    simp only [Br₁]
    field_simp
    ring
  have hB : 0 ≤ Br₁ L M J := by simp only [Br₁]; positivity
  calc ‖X2b 1 r τ f g l a b‖ ≤ 4 / heat4 l (l - a - b) a b * ‖twoRoot 1 r τ f g l a b‖ :=
        norm_outerInv_le hH r l _ _
    _ ≤ 4 / heat4 l (l - a - b) a b * (320 / |r| * M * (‖f a‖ * ‖g b‖) * Br₁ L M J) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = _ := by ring

/-- **Both rootings at both weights**, with the bracket of weight two (Body 36). -/
theorem norm_X2b_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field)
    {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖X2b s r τ f g l a b‖ ≤ 2816 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) *
      (‖f a‖ * ‖g b‖) * Br (absk l ^ 2) (absk (l - a) ^ 2) (absk (l - a - b) ^ 2) := by
  simp only [absk_sq]
  rcases hs with rfl | rfl
  · obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
    have hr0 : 0 < |r| := abs_pos.2 hr
    have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
    have hJ : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
    have hH := heat4_pos (l := l) hj0 a b
    have h1 := Br₁_le (M := absk (l - a)) hL hJ
    simp only [absk_sq] at h1
    have hB : 0 ≤ Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) := by
      have := absSq_nonneg l
      have := absSq_nonneg (l - a)
      have := absSq_nonneg (l - a - b)
      simp only [Br]
      positivity
    have hm := absk_nonneg (l - a)
    have hfg : 0 ≤ ‖f a‖ * ‖g b‖ := by positivity
    refine (norm_X2b_one_le hr τ f g ha hb hj).trans ?_
    have hK : 0 ≤ 1 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) * (‖f a‖ * ‖g b‖) := by
      positivity
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1280) hK)
    have h3 := mul_nonneg hK hB
    calc _ = 1280 * (1 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) * (‖f a‖ * ‖g b‖)) *
          Br₁ (absk l) (absk (l - a)) (absk (l - a - b)) := by ring
      _ ≤ _ := h2
      _ ≤ 2816 * (1 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) * (‖f a‖ * ‖g b‖) *
          Br (absSq l) (absSq (l - a)) (absSq (l - a - b))) := by linarith
      _ = _ := by ring
  · exact norm_X2b_two_le hr τ f g ha hb hj

/-! ### C. The bracket of weight two -/

/-- The ordinary sector, `L` the larger exterior (Body 36: "`M/Σ ≤ C/L` and `L ≤ J + P₁ + P₂`"; "for
the middle term use `M² ≤ 2Σ`, `M² ≤ 16 L²` and `M ≤ J + P₂`"). -/
lemma ord_side {L M J Pa Pb : ℝ} (hL : 0 < L) (hJ : 0 < J) (hM0 : 0 ≤ M) (hPa0 : 0 ≤ Pa)
    (hPb0 : 0 ≤ Pb) (h1 : M ≤ L + Pa) (h2 : M ≤ J + Pb) (h3 : L ≤ J + Pa + Pb) (hJL : J ≤ L)
    (hM : M ≤ 4 * L) :
    M / (L ^ 2 + J ^ 2 + Pa ^ 2 + Pb ^ 2) * Br (L ^ 2) (M ^ 2) (J ^ 2) ≤
      68 * (1 / J + 1 / L + (Pa + Pb) / J ^ 2) := by
  set S := L ^ 2 + J ^ 2 + Pa ^ 2 + Pb ^ 2 with hS
  have hS0 : 0 < S := by positivity
  have r1 : L ^ 2 / S ≤ 1 := by
    rw [div_le_one hS0]
    nlinarith [sq_nonneg J, sq_nonneg Pa, sq_nonneg Pb]
  have r2 : M ^ 2 / S ≤ 2 := by
    rw [div_le_iff₀ hS0]
    have : M ^ 2 ≤ (L + Pa) ^ 2 := pow_le_pow_left₀ hM0 h1 2
    nlinarith [sq_nonneg (L - Pa), sq_nonneg J, sq_nonneg Pb]
  have r3 : M ^ 2 / L ^ 2 ≤ 16 := by
    rw [div_le_iff₀ (by positivity)]
    have : M ^ 2 ≤ (4 * L) ^ 2 := pow_le_pow_left₀ hM0 hM 2
    nlinarith
  have r4 : J ^ 2 / L ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact pow_le_pow_left₀ hJ.le hJL 2
  have r5 : M / S ≤ 4 / L := by
    rw [div_le_div_iff₀ hS0 hL]
    nlinarith [sq_nonneg J, sq_nonneg Pa, sq_nonneg Pb]
  have hJ2 : 0 < J ^ 2 := by positivity
  have r2' : 0 ≤ M ^ 2 / S := by positivity
  have r3' : 0 ≤ M ^ 2 / L ^ 2 := by positivity
  have t1 : M / S * (L ^ 2 / J ^ 2) ≤ 4 / J + 4 * (Pa + Pb) / J ^ 2 := by
    have e : M / S * (L ^ 2 / J ^ 2) = M * (L ^ 2 / S) / J ^ 2 := by
      field_simp
    have e' : 4 / J + 4 * (Pa + Pb) / J ^ 2 = 4 * (J + Pa + Pb) / J ^ 2 := by
      field_simp
      ring
    rw [e, e']
    refine div_le_div_of_nonneg_right ?_ hJ2.le
    calc M * (L ^ 2 / S) ≤ M * 1 := mul_le_mul_of_nonneg_left r1 hM0
      _ ≤ _ := by linarith only [hM, h3]
  have t2 : M / S * (2 * (M ^ 2) ^ 2 / (L ^ 2 * J ^ 2)) ≤ 64 / J + 64 * Pb / J ^ 2 := by
    have e : M / S * (2 * (M ^ 2) ^ 2 / (L ^ 2 * J ^ 2)) =
        2 * M * (M ^ 2 / S) * (M ^ 2 / L ^ 2) / J ^ 2 := by
      field_simp
    have e' : 64 / J + 64 * Pb / J ^ 2 = 64 * (J + Pb) / J ^ 2 := by
      field_simp
    rw [e, e']
    refine div_le_div_of_nonneg_right ?_ hJ2.le
    calc 2 * M * (M ^ 2 / S) * (M ^ 2 / L ^ 2) ≤ 2 * M * 2 * 16 := by gcongr
      _ ≤ _ := by linarith only [h2]
  have t3 : M / S * (J ^ 2 / L ^ 2) ≤ 4 / L := by
    calc _ ≤ 4 / L * 1 := mul_le_mul r5 r4 (by positivity) (by positivity)
      _ = _ := mul_one _
  have e : M / S * Br (L ^ 2) (M ^ 2) (J ^ 2) = M / S * (L ^ 2 / J ^ 2) +
      M / S * (2 * (M ^ 2) ^ 2 / (L ^ 2 * J ^ 2)) + M / S * (J ^ 2 / L ^ 2) := by
    simp only [Br]
    ring
  rw [e]
  have h5 : 0 ≤ 1 / J := by positivity
  have h6 : 0 ≤ 1 / L := by positivity
  have h7 : 0 ≤ Pa / J ^ 2 := by positivity
  have h8 : 0 ≤ Pb / J ^ 2 := by positivity
  have e1 : 4 / J = 4 * (1 / J) := by ring
  have e2 : 64 / J = 64 * (1 / J) := by ring
  have e3 : 4 / L = 4 * (1 / L) := by ring
  have e4 : 4 * (Pa + Pb) / J ^ 2 = 4 * (Pa / J ^ 2) + 4 * (Pb / J ^ 2) := by ring
  have e5 : 64 * Pb / J ^ 2 = 64 * (Pb / J ^ 2) := by ring
  have e6 : (Pa + Pb) / J ^ 2 = Pa / J ^ 2 + Pb / J ^ 2 := by ring
  rw [e1, e4] at t1
  rw [e2, e5] at t2
  rw [e3] at t3
  rw [e6]
  linarith

/-- **The ordinary sector** (Body 36): `(M/Σ) Br ≤ 68 [1/J + 1/L + (P₁+P₂)/J² + (P₁+P₂)/L²]`, on
`M ≤ 4 max(L, J)`, from the paths alone. -/
lemma ord_bracket_le {L M J Pa Pb : ℝ} (hL : 0 < L) (hJ : 0 < J) (hM0 : 0 ≤ M) (hPa0 : 0 ≤ Pa)
    (hPb0 : 0 ≤ Pb) (h1 : M ≤ L + Pa) (h2 : M ≤ J + Pb) (h3 : L ≤ J + Pa + Pb)
    (h4 : J ≤ L + Pa + Pb) (hM : M ≤ 4 * L ∨ M ≤ 4 * J) :
    M / (L ^ 2 + J ^ 2 + Pa ^ 2 + Pb ^ 2) * Br (L ^ 2) (M ^ 2) (J ^ 2) ≤
      68 * (1 / J + 1 / L + (Pa + Pb) / J ^ 2 + (Pa + Pb) / L ^ 2) := by
  have h5 : 0 ≤ (Pa + Pb) / L ^ 2 := by positivity
  have h6 : 0 ≤ (Pa + Pb) / J ^ 2 := by positivity
  rcases le_total J L with hJL | hJL
  · have hM' : M ≤ 4 * L := hM.elim id fun h => h.trans (by linarith)
    have := ord_side hL hJ hM0 hPa0 hPb0 h1 h2 h3 hJL hM'
    linarith
  · have hM' : M ≤ 4 * J := hM.elim (fun h => h.trans (by linarith)) id
    have := ord_side hJ hL hM0 hPb0 hPa0 h2 h1 (by linarith) hJL hM'
    have e1 : J ^ 2 + L ^ 2 + Pb ^ 2 + Pa ^ 2 = L ^ 2 + J ^ 2 + Pa ^ 2 + Pb ^ 2 := by ring
    have e2 : Br (J ^ 2) (M ^ 2) (L ^ 2) = Br (L ^ 2) (M ^ 2) (J ^ 2) := by
      simp only [Br]
      field_simp
      ring
    have e3 : (Pb + Pa) / L ^ 2 = (Pa + Pb) / L ^ 2 := by ring
    rw [e1, e2, e3] at this
    linarith

/-- The old bracket on `M ≥ 4 max(L, J)`, with `Σ ≥ (9/8) M²` (Body 36: "The full old bracket times
`M/Σ` is at most `C M³/(L²J²)` on this sector at either `s`"). -/
lemma high_bracket_le {L M J S : ℝ} (hL : 0 < L) (hJ : 0 < J) (hM : 0 < M) (h1 : 4 * L ≤ M)
    (h2 : 4 * J ≤ M) (hS : 9 / 8 * M ^ 2 ≤ S) :
    M / S * Br (L ^ 2) (M ^ 2) (J ^ 2) ≤ 32 / 9 * (M ^ 3 / (L ^ 2 * J ^ 2)) := by
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hA : 0 < L ^ 2 * J ^ 2 := by positivity
  have hLM : L ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hL.le (by linarith) 2
  have hJM : J ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hJ.le (by linarith) 2
  have hB : Br (L ^ 2) (M ^ 2) (J ^ 2) ≤ 4 * ((M ^ 2) ^ 2 / (L ^ 2 * J ^ 2)) := by
    have e1 : L ^ 2 / J ^ 2 = (L ^ 2) ^ 2 / (L ^ 2 * J ^ 2) := by
      field_simp
    have e2 : J ^ 2 / L ^ 2 = (J ^ 2) ^ 2 / (L ^ 2 * J ^ 2) := by
      field_simp
    have a1 : (L ^ 2) ^ 2 / (L ^ 2 * J ^ 2) ≤ (M ^ 2) ^ 2 / (L ^ 2 * J ^ 2) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hLM 2) hA.le
    have a2 : (J ^ 2) ^ 2 / (L ^ 2 * J ^ 2) ≤ (M ^ 2) ^ 2 / (L ^ 2 * J ^ 2) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hJM 2) hA.le
    have e3 : 2 * (M ^ 2) ^ 2 / (L ^ 2 * J ^ 2) = 2 * ((M ^ 2) ^ 2 / (L ^ 2 * J ^ 2)) := by ring
    simp only [Br]
    rw [e1, e2, e3]
    linarith
  have hr : M / S ≤ 8 / 9 / M := by
    rw [div_le_div_iff₀ hS0 hM]
    nlinarith
  calc _ ≤ 8 / 9 / M * (4 * ((M ^ 2) ^ 2 / (L ^ 2 * J ^ 2))) :=
        mul_le_mul hr hB (by simp only [Br]; positivity) (by positivity)
    _ = _ := by
        field_simp
        ring

end OVNS.Quant.Metric

end
