import OddViscousNS.Quant.Joint.Force.X1Elt

/-!
# The output half of `X₁`: the block (step J5, node N12)

The channels and the block of LOCAL363: `K |X₁|_{kj} ≲ f_p √(P/q)` on comparable fast lengths
(`norm_X1b_cmp`), the old bound on separated lengths (`norm_X1b_sep`), and their maximum
(`norm_X1b_max`).  The elementary facts are in `X1Elt.lean`.
-/

open scoped ComplexConjugate

open OVNS.Quant.H2 (norm_metSym_mul_le)

noncomputable section

namespace OVNS.Quant.Metric

/-! ### D. The channels -/

variable {s : ℕ} {r : ℝ}

/-- The size of the multiplier: heat and phase. -/
lemma metM_facts (hr : r ≠ 0) (τ : ℝ) (a b c : Sgn) {p k j : Mode} (hk : p + j = k) (hp : p 2 = 0)
    (hj : j 2 ≠ 0) :
    ‖metM r τ a b c p j‖ * (absSq k + absSq j) ≤ 1 ∧
      ‖metM r τ a b c p j‖ * |sg c * absk k - sg b * absk j| ≤ 1 / |r| := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hS : 0 < absSq k + absSq j := by
    have hj0 : j ≠ 0 := fun h => hj (by simp [h])
    have := one_le_absSq hj0
    have := absSq_nonneg k
    linarith
  unfold metM
  split_ifs with h
  · have h1 := norm_metSym_le r τ a b c h.ne_zero
    have h2 := norm_metSym_mul_le hr τ a b c hp hj h.2.2
    rw [hk] at h2
    refine ⟨?_, h2⟩
    have hT : absSq k + absSq j ≤ triHeat p j := by
      unfold triHeat
      rw [hk]
      have := absSq_nonneg p
      linarith
    have hT0 : 0 < triHeat p j := lt_of_lt_of_le hS hT
    calc ‖metSym r τ a b c p j‖ * (absSq k + absSq j) ≤ 1 / triHeat p j * triHeat p j :=
          mul_le_mul h1 hT hS.le (by positivity)
      _ = 1 := by field_simp
  · simp only [norm_zero, zero_mul, zero_le_one, true_and]
    positivity

/-- Equal helicities: the phase is `K − J`, and `min(K/q, P/K) ≤ √(P/q)`. -/
private lemma chan_eq_le {K J P m q d N e T : ℝ} (hK : 0 < K)
    (hP : 0 ≤ P) (hm : 0 ≤ m) (hm1 : m * (K ^ 2 + J ^ 2) ≤ 1) (hm2 : m * d ≤ 1 / q) (hd0 : 0 ≤ d)
    (hdP : d ≤ P) (hN : N ≤ 16 * d) (he0 : 0 ≤ e) (he : e ≤ T) :
    K * (m * N * e) ≤ 16 * Real.sqrt (P / q) * T := by
  have hT : 0 ≤ T := he0.trans he
  have h1 : m * K ^ 2 ≤ 1 := by nlinarith only [hm1, mul_nonneg hm (sq_nonneg J)]
  have hz : K * (m * d) ≤ Real.sqrt (P / q) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h2 : (m * d) * K ^ 2 ≤ P := by
      calc (m * d) * K ^ 2 = (m * K ^ 2) * d := by ring
        _ ≤ 1 * P := mul_le_mul h1 hdP hd0 zero_le_one
        _ = P := one_mul P
    have h3 := mul_le_mul h2 hm2 (by positivity) hP
    calc (K * (m * d)) ^ 2 = (m * d) * K ^ 2 * (m * d) := by ring
      _ ≤ P * (1 / q) := h3
      _ = P / q := by ring
  have hs0 := Real.sqrt_nonneg (P / q)
  calc K * (m * N * e) = K * m * (N * e) := by ring
    _ ≤ K * m * (16 * d * T) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hN he he0 (by positivity)) (by positivity)
    _ = 16 * (K * (m * d)) * T := by ring
    _ ≤ 16 * Real.sqrt (P / q) * T := by gcongr

/-- Opposite helicities: the phase is `K + J`, the triple product has size `P/K`. -/
private lemma chan_opp_le {K J P m q d N e T : ℝ} (hK : 0 < K) (hJ : 0 < J) (hq : 0 < q)
    (hP : 0 ≤ P) (hPs : P ≤ K + J) (hm : 0 ≤ m) (hm1 : m * (K ^ 2 + J ^ 2) ≤ 1)
    (hm2 : m * d ≤ 1 / q) (hd : d = K + J) (hN : N ≤ 16 * d) (he0 : 0 ≤ e)
    (he : e ≤ 3 * (P / K) * T) (hT : 0 ≤ T) :
    K * (m * N * e) ≤ 96 * Real.sqrt (P / q) * T := by
  subst hd
  set z := m * (K + J) with hz
  have hz0 : 0 ≤ z := by positivity
  have h2 : z * (K + J) ≤ 2 := by
    have : (K + J) ^ 2 ≤ 2 * (K ^ 2 + J ^ 2) := by nlinarith only [sq_nonneg (K - J)]
    calc z * (K + J) = m * (K + J) ^ 2 := by rw [hz]; ring
      _ ≤ m * (2 * (K ^ 2 + J ^ 2)) := mul_le_mul_of_nonneg_left this hm
      _ ≤ 2 := by nlinarith only [hm1]
  have h3 : P * z ≤ 2 * Real.sqrt (P / q) := by
    have hx0 : 0 ≤ P / q := by positivity
    have h5 : P * z ≤ 2 := by
      calc P * z ≤ (K + J) * z := mul_le_mul_of_nonneg_right hPs hz0
        _ = z * (K + J) := mul_comm _ _
        _ ≤ 2 := h2
    have h6 : P * z * z ≤ 2 * (1 / q) := mul_le_mul h5 hm2 hz0 (by norm_num)
    have h4 : (P * z) * (P * z) ≤ (2 * Real.sqrt (P / q)) * (2 * Real.sqrt (P / q)) := by
      have e1 : (2 * Real.sqrt (P / q)) * (2 * Real.sqrt (P / q)) = 4 * (P / q) := by
        have := Real.mul_self_sqrt hx0
        nlinarith only [this]
      rw [e1]
      calc (P * z) * (P * z) = P * (P * z * z) := by ring
        _ ≤ P * (2 * (1 / q)) := mul_le_mul_of_nonneg_left h6 hP
        _ = 2 * (P / q) := by ring
        _ ≤ 4 * (P / q) := by nlinarith only [hx0]
    exact abs_le_of_sq_le_sq' (by nlinarith only [h4]) (by positivity) |>.2
  have hNe : N * e ≤ 16 * (K + J) * (3 * (P / K) * T) := mul_le_mul hN he he0 (by positivity)
  calc K * (m * N * e) = K * m * (N * e) := by ring
    _ ≤ K * m * (16 * (K + J) * (3 * (P / K) * T)) :=
        mul_le_mul_of_nonneg_left hNe (by positivity)
    _ = 48 * (P * z) * T := by
        rw [hz]
        field_simp
        ring
    _ ≤ 48 * (2 * Real.sqrt (P / q)) * T := by gcongr
    _ = _ := by ring

/-- **One channel on comparable lengths.** -/
theorem chan_cmp_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (a b c : Sgn) {p k j : Mode}
    (hk : p + j = k) (hp : p 2 = 0) (hj : j 2 ≠ 0) (h1 : absk k ≤ 2 * absk j)
    (h2 : absk j ≤ 2 * absk k) (v w Z : V3) :
    absk k * (‖metM r τ a b c p j‖ * |wt s k j * (sg a * absk p - sg b * absk j) -
        wt s j k * (sg a * absk p - sg c * absk k)| * ‖elt a b c p k j v w Z‖) ≤
      96 * Real.sqrt (absk p / |r|) * (‖v‖ * ‖w‖ * ‖Z‖) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hj0 : j ≠ 0 := fun h => hj (by simp [h])
  have hk2 : k 2 = j 2 := by rw [← hk]; simp [hp]
  have hk0 : k ≠ 0 := fun h => hj (by rw [← hk2, h]; rfl)
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk0)
  have hJ : 0 < absk j := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hP0 := absk_nonneg p
  have hPs : absk p ≤ absk k + absk j := by
    have := absk_sub_le k j
    rwa [show k - j = p by rw [← hk]; abel] at this
  have hsgn : ∀ (e : Sgn) (x : ℝ), sg e * x = x ∨ sg e * x = -x := fun e x => by
    cases e <;> simp [sg]
  have habs : |sg a * absk p| = absk p := by
    rw [abs_mul, abs_of_nonneg hP0]
    cases a <;> simp [sg]
  have hnum := num_cmp_le hs hK hJ h1 h2 hPs habs (hsgn b _) (hsgn c _)
  obtain ⟨hm1, hm2⟩ := metM_facts hr τ a b c hk hp hj
  rw [← absk_sq k, ← absk_sq j] at hm1
  have hm0 := norm_nonneg (metM r τ a b c p j)
  have he0 := norm_nonneg (elt a b c p k j v w Z)
  have hT0 : 0 ≤ ‖v‖ * ‖w‖ * ‖Z‖ := by positivity
  simp only [wt]
  by_cases hbc : b = c
  · subst hbc
    have hd : |sg b * absk k - sg b * absk j| ≤ absk p := by
      have e : sg b * absk k - sg b * absk j = sg b * (absk k - absk j) := by ring
      rw [e, abs_mul]
      have h3 : |sg b| = 1 := by cases b <;> simp [sg]
      rw [h3, one_mul]
      have a3 := absk_add_le k (-p)
      rw [show k + -p = j by rw [← hk]; abel, absk_neg] at a3
      have a4 := absk_add_le p j
      rw [hk] at a4
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have h := chan_eq_le hK hP0 hm0 hm1 hm2 (abs_nonneg _) hd hnum he0
      (norm_elt_le a b b p k j v w Z)
    have hs0 := Real.sqrt_nonneg (absk p / |r|)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hT0)
    gcongr
    norm_num
  · have hd : |sg c * absk k - sg b * absk j| = absk k + absk j := by
      have h3 : sg c = -sg b := by
        cases b <;> cases c <;> simp_all [sg]
      rw [h3]
      have e : -sg b * absk k - sg b * absk j = -(sg b * (absk k + absk j)) := by ring
      rw [e, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < absk k + absk j)]
      have h4 : |sg b| = 1 := by cases b <;> simp [sg]
      rw [h4, one_mul]
    exact chan_opp_le hK hJ hr0 hP0 hPs hm0 hm1 hm2 hd hnum he0
      (elt_opp_le hbc hk hk0 hj0 v w Z) hT0

/-! ### E. The block -/

/-- **The output half of `X₁` on comparable lengths** (LOCAL363):
`K ‖X₁(v)_{kj}‖ ≤ 768 √(P/q) ‖v‖`, at both weights. -/
theorem norm_X1b_cmp (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {p k j : Mode} (hk : p + j = k)
    (hp : p 2 = 0) (hj : j 2 ≠ 0) (h1 : absk k ≤ 2 * absk j) (h2 : absk j ≤ 2 * absk k) (v : V3) :
    absk k * ‖X1b s r τ p k j v‖ ≤ 768 * Real.sqrt (absk p / |r|) * ‖v‖ := by
  have hj0 : j ≠ 0 := fun h => hj (by simp [h])
  have hk2 : k 2 = j 2 := by rw [← hk]; simp [hp]
  have hk0 : k ≠ 0 := fun h => hj (by rw [← hk2, h]; rfl)
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk0)
  have hq := Real.sqrt_nonneg (absk p / |r|)
  have hop : ‖X1b s r τ p k j v‖ ≤ 768 * Real.sqrt (absk p / |r|) * ‖v‖ / absk k := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    refine norm_le_of_inner (by positivity) fun Z => ?_
    rw [inner_X1b s r τ hk hj0 hk0]
    set E := 96 * Real.sqrt (absk p / |r|) * (‖v‖ * ‖w‖ * ‖Z‖) / absk k with hE
    have hterm : ∀ a b c, ‖metM r τ a b c p j *
        (((wt s k j * (sg a * absk p - sg b * absk j) -
          wt s j k * (sg a * absk p - sg c * absk k) : ℝ) : ℂ) * elt a b c p k j v w Z)‖ ≤ E := by
      intro a b c
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc, hE,
        le_div_iff₀ hK, mul_comm]
      exact chan_cmp_le hs hr τ a b c hk hp hj h1 h2 v w Z
    refine (norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
      norm_sum_le_of_le _ fun c _ => hterm a b c).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, hE]
    push_cast
    ring
  calc absk k * ‖X1b s r τ p k j v‖ ≤ absk k * (768 * Real.sqrt (absk p / |r|) * ‖v‖ / absk k) :=
        mul_le_mul_of_nonneg_left hop hK.le
    _ = _ := by field_simp

/-- **The separated lengths** (LOCAL363): `P ≍ max(K, J)`, so the old bound gives
`max(K, J) ‖X₁(v)_{kj}‖ ≲ q⁻¹ P³ ‖v‖ / min(K, J)²`. -/
theorem norm_X1b_sep (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {p k j : Mode} (hk : p + j = k)
    (hp : p 2 = 0) (hj : j 2 ≠ 0) (h : 2 * absk j < absk k ∨ 2 * absk k < absk j) (v : V3) :
    max (absk k) (absk j) * ‖X1b s r τ p k j v‖ ≤
      2 ^ 10 / |r| * (absk p ^ 3 * ‖v‖) * ((absk k)⁻¹ ^ 2 + (absk j)⁻¹ ^ 2) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hj0 : j ≠ 0 := fun h => hj (by simp [h])
  have hk2 : k 2 = j 2 := by rw [← hk]; simp [hp]
  have hk0 : k ≠ 0 := fun h => hj (by rw [← hk2, h]; rfl)
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk0)
  have hJ : 0 < absk j := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hv := norm_nonneg v
  have hb := norm_X1b_le hs hr τ hk hp hj v
  rw [← absk_sq k, ← absk_sq j] at hb
  have a3 := absk_add_le k (-p)
  rw [show k + -p = j by rw [← hk]; abel, absk_neg] at a3
  have a4 := absk_add_le p j
  rw [hk] at a4
  set K := absk k
  set J := absk j
  set P := absk p
  have hP0 : 0 ≤ P := absk_nonneg p
  have hgen : ∀ {x y : ℝ}, 0 < x → 0 < y → 2 * y < x → x ≤ 2 * P →
      x * (x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2) ≤ 16 * (P ^ 3 * y⁻¹ ^ 2) := fun {x y} hx hy hxy hxP => by
    have h3 : y ^ 2 / x ^ 2 ≤ x ^ 2 / y ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : y ^ 2 ≤ x ^ 2 := by nlinarith only [hxy, hx, hy]
      nlinarith only [mul_le_mul this this (by positivity) (by positivity)]
    have h4 : x ^ 3 ≤ 8 * P ^ 3 := by
      have := pow_le_pow_left₀ hx.le hxP 3
      nlinarith only [this]
    calc x * (x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2) ≤ x * (2 * (x ^ 2 / y ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hx.le
          linarith
      _ = 2 * (x ^ 3 * y⁻¹ ^ 2) := by
          field_simp
      _ ≤ 2 * ((8 * P ^ 3) * y⁻¹ ^ 2) := by gcongr
      _ = _ := by ring
  have hbr : 0 ≤ (K)⁻¹ ^ 2 := by positivity
  have hbr2 : 0 ≤ (J)⁻¹ ^ 2 := by positivity
  have hmain : max K J * (K ^ 2 / J ^ 2 + J ^ 2 / K ^ 2) ≤ 16 * (P ^ 3 * (K⁻¹ ^ 2 + J⁻¹ ^ 2)) := by
    rcases h with hh | hh
    · have hm : max K J = K := max_eq_left (by linarith)
      rw [hm]
      have hx : K ≤ 2 * P := by linarith
      have := hgen hK hJ hh hx
      have h5 : 0 ≤ P ^ 3 * K⁻¹ ^ 2 := by positivity
      nlinarith only [this, h5]
    · have hm : max K J = J := max_eq_right (by linarith)
      rw [hm]
      have hx : J ≤ 2 * P := by linarith
      have := hgen hJ hK hh hx
      have h5 : 0 ≤ P ^ 3 * J⁻¹ ^ 2 := by positivity
      have e : K ^ 2 / J ^ 2 + J ^ 2 / K ^ 2 = J ^ 2 / K ^ 2 + K ^ 2 / J ^ 2 := add_comm _ _
      rw [e]
      nlinarith only [this, h5]
  have hM0 : 0 ≤ max K J := le_max_of_le_left hK.le
  calc max K J * ‖X1b s r τ p k j v‖
      ≤ max K J * (44 / |r| * ‖v‖ * (K ^ 2 / J ^ 2 + J ^ 2 / K ^ 2)) :=
        mul_le_mul_of_nonneg_left hb hM0
    _ = 44 / |r| * ‖v‖ * (max K J * (K ^ 2 / J ^ 2 + J ^ 2 / K ^ 2)) := by ring
    _ ≤ 44 / |r| * ‖v‖ * (16 * (P ^ 3 * (K⁻¹ ^ 2 + J⁻¹ ^ 2))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ ≤ _ := by
        have h6 : 0 ≤ 1 / |r| * (P ^ 3 * ‖v‖) * (K⁻¹ ^ 2 + J⁻¹ ^ 2) := by positivity
        have e1 : 44 / |r| * ‖v‖ * (16 * (P ^ 3 * (K⁻¹ ^ 2 + J⁻¹ ^ 2))) =
            704 * (1 / |r| * (P ^ 3 * ‖v‖) * (K⁻¹ ^ 2 + J⁻¹ ^ 2)) := by ring
        have e2 : 2 ^ 10 / |r| * (P ^ 3 * ‖v‖) * (K⁻¹ ^ 2 + J⁻¹ ^ 2) =
            1024 * (1 / |r| * (P ^ 3 * ‖v‖) * (K⁻¹ ^ 2 + J⁻¹ ^ 2)) := by ring
        rw [e1, e2]
        nlinarith only [h6]

/-- The block with the larger of the two derivatives, in one bound. -/
theorem norm_X1b_max (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {p k j : Mode} (hk : p + j = k)
    (hp : p 2 = 0) (hj : j 2 ≠ 0) (v : V3) :
    max (absk k) (absk j) * ‖X1b s r τ p k j v‖ ≤ 1536 * Real.sqrt (absk p / |r|) * ‖v‖ +
      2 ^ 10 / |r| * (absk p ^ 3 * ‖v‖) * ((absk k)⁻¹ ^ 2 + (absk j)⁻¹ ^ 2) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hv := norm_nonneg v
  have hn0 := norm_nonneg (X1b s r τ p k j v)
  have hP := absk_nonneg p
  have hq := Real.sqrt_nonneg (absk p / |r|)
  have h3 : 0 ≤ 2 ^ 10 / |r| * (absk p ^ 3 * ‖v‖) * ((absk k)⁻¹ ^ 2 + (absk j)⁻¹ ^ 2) := by
    positivity
  by_cases h : 2 * absk j < absk k ∨ 2 * absk k < absk j
  · have h4 := norm_X1b_sep hs hr τ hk hp hj h v
    have h5 : 0 ≤ 1536 * Real.sqrt (absk p / |r|) * ‖v‖ := by positivity
    linarith
  · rw [not_or, not_lt, not_lt] at h
    have h4 := norm_X1b_cmp hs hr τ hk hp hj h.1 h.2 v
    have hK := absk_nonneg k
    have h5 : max (absk k) (absk j) ≤ 2 * absk k := max_le (by linarith) h.2
    have h6 := mul_le_mul_of_nonneg_right h5 hn0
    linarith

end OVNS.Quant.Metric

end
