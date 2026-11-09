import OddViscousNS.Quant.Arith.Surface.NodeSum

/-!
# The exponent set at scale `ϑ`

`kappaHat l = √(l₀l₁l₂/(4l₀+2l₁))`.  For `Y = 5L + ϑ/√A`: `#𝓔(Y) ≥ ϑ²`, the total weight is at most
`c₀ κ̂ ϑ³ (1 + 1199/ϑ)`, and every exponent has `|e| ≤ 30 + 9ϑ` (`weight_bound`, `deg_of_mem_expSet`).
-/

open Finset

namespace OVNS.Quant.Surf

/-- `κ̂ = √(l₀l₁l₂/(4l₀+2l₁))`. -/
noncomputable def kappaHat (l : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (l 0 * l 1 * l 2 / (4 * l 0 + 2 * l 1))

/-- The scale `Y(ϑ) = 5L + ϑ/√A`. -/
noncomputable def scaleY (l : Fin 3 → ℝ) (L ϑ : ℝ) : ℝ := 5 * L + ϑ / Real.sqrt (expA l)

lemma expA_pos {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) : 0 < expA l := by
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  unfold expA
  positivity

/-- `A L² ≤ 108`. -/
lemma expA_mul_le {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) {L : ℝ} (hL6 : ∀ i, L ≤ 6 * l i)
    (hL0 : 0 < L) : expA l * L ^ 2 ≤ 108 := by
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  have e : expA l = 2 / (l 1 * l 2) + 1 / (l 0 * l 2) := by
    unfold expA
    field_simp
  have a1 : L ^ 2 ≤ 36 * (l 1 * l 2) := by nlinarith [hL6 1, hL6 2]
  have a2 : L ^ 2 ≤ 36 * (l 0 * l 2) := by nlinarith [hL6 0, hL6 2]
  have b1 : L ^ 2 / (l 1 * l 2) ≤ 36 := (div_le_iff₀ (by positivity)).2 a1
  have b2 : L ^ 2 / (l 0 * l 2) ≤ 36 := (div_le_iff₀ (by positivity)).2 a2
  have e2 : expA l * L ^ 2 = 2 * (L ^ 2 / (l 1 * l 2)) + L ^ 2 / (l 0 * l 2) := by
    rw [e]; ring
  rw [e2]
  linarith

/-- `A L² ≥ 2`. -/
lemma le_expA_mul {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) {L : ℝ} (hL : ∀ i, l i ≤ L) :
    2 ≤ expA l * L ^ 2 := by
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  have hL0 : 0 < L := lt_of_lt_of_le h0 (hL 0)
  have e : expA l = (2 * l 0 + l 1) / (l 0 * l 1 * l 2) := rfl
  rw [e, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have a1 : l 1 * l 2 ≤ L ^ 2 := by nlinarith [hL 1, hL 2]
  have : 2 * (l 0 * (l 1 * l 2)) ≤ 2 * (l 0 * L ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left a1 h0.le) (by norm_num)
  nlinarith [mul_pos h1 (pow_pos hL0 2)]

/-- `1/√A = √2 κ̂`. -/
lemma inv_sqrt_expA {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) :
    1 / Real.sqrt (expA l) = Real.sqrt 2 * kappaHat l := by
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  have hA := expA_pos hl
  have hk : 0 ≤ l 0 * l 1 * l 2 / (4 * l 0 + 2 * l 1) := by positivity
  rw [kappaHat, ← Real.sqrt_mul (by norm_num), one_div, ← Real.sqrt_inv]
  congr 1
  simp only [expA]
  field_simp
  ring

/-- `c₀ ≥ 2/3`. -/
lemma two_thirds_le_c0 : 2 / 3 ≤ c0 := by
  have : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  unfold c0
  linarith

/-- Size and weight of the exponent set at scale `ϑ`. -/
theorem weight_bound {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) {L : ℝ} (hL : ∀ i, l i ≤ L)
    (hL6 : ∀ i, L ≤ 6 * l i) {ϑ : ℝ} (hϑ : 77 ≤ ϑ) :
    ϑ ^ 2 ≤ ((expSet l (scaleY l L ϑ)).card : ℝ) ∧
      ∑ e ∈ expSet l (scaleY l L ϑ), wt l e ≤ c0 * kappaHat l * ϑ ^ 3 * (1 + 1199 / ϑ) := by
  have hL0 : 0 < L := lt_of_lt_of_le (hl 0) (hL 0)
  have hϑ0 : 0 < ϑ := by linarith
  set A := expA l with hA
  have hApos : 0 < A := expA_pos hl
  set s := Real.sqrt A with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hApos
  have hs2 : s ^ 2 = A := Real.sq_sqrt hApos.le
  have hAL := expA_mul_le hl hL6 hL0
  have hLs : L * s ≤ 11 := by
    by_contra hc
    push Not at hc
    have : (11 : ℝ) ^ 2 < (L * s) ^ 2 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    rw [mul_pow, hs2] at this
    nlinarith
  set W := ϑ / s with hW
  have hW0 : 0 < W := by positivity
  have hAW : A * W ^ 2 = ϑ ^ 2 := by
    rw [hW, div_pow, hs2]
    field_simp
  set τ := 11 / ϑ with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 / 7 := by
    rw [hτ, div_le_iff₀ hϑ0]
    linarith
  have hLW : L ≤ τ * W := by
    have : τ * W = 11 / s := by
      rw [hτ, hW]
      field_simp
    rw [this, le_div_iff₀ hs0]
    exact hLs
  have hY : scaleY l L ϑ = 5 * L + W := rfl
  have hY5 : 5 * L ≤ scaleY l L ϑ := by rw [hY]; linarith
  have h1 := expSet_card_ge hl hL hY5
  have h2 := expSet_weight_le hl hL hY5
  rw [hY] at h1 h2 ⊢
  have e1 : 5 * L + W - 5 * L = W := by ring
  rw [e1, ← hA, hAW] at h1
  refine ⟨h1, ?_⟩
  rw [← hA] at h2
  have e2 : 5 * L + W + 2 * L = W + 7 * L := by ring
  rw [e2] at h2
  set Q := 1 + 7 * τ with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ]; linarith
  have hQ2 : Q ≤ 2 := by rw [hQ]; linarith
  have hWL : W + 7 * L ≤ Q * W := by
    rw [hQ]
    nlinarith
  have hWL0 : 0 ≤ W + 7 * L := by positivity
  have c1 : (W + 7 * L) ^ 3 ≤ Q ^ 3 * W ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hWL0 hWL 3
  have c2 : (W + 7 * L) ^ 2 ≤ Q ^ 2 * W ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hWL0 hWL 2
  have c3 : 2 / 3 * A * (W + 7 * L) ^ 3 ≤ 2 / 3 * (ϑ ^ 2 * W) * Q ^ 3 := by
    have : A * W ^ 3 = ϑ ^ 2 * W := by rw [← hAW]; ring
    calc 2 / 3 * A * (W + 7 * L) ^ 3 ≤ 2 / 3 * A * (Q ^ 3 * W ^ 3) :=
          mul_le_mul_of_nonneg_left c1 (by positivity)
      _ = 2 / 3 * (A * W ^ 3) * Q ^ 3 := by ring
      _ = _ := by rw [this]
  have c4 : 10 * L * A * (W + 7 * L) ^ 2 ≤ 10 * τ * (ϑ ^ 2 * W) * Q ^ 2 := by
    have : A * W ^ 2 * W = ϑ ^ 2 * W := by rw [hAW]
    calc 10 * L * A * (W + 7 * L) ^ 2 ≤ 10 * (τ * W) * A * (Q ^ 2 * W ^ 2) := by
          have h3 : 10 * L * A ≤ 10 * (τ * W) * A :=
            mul_le_mul_of_nonneg_right (by linarith) hApos.le
          exact mul_le_mul h3 c2 (by positivity) (by positivity)
      _ = 10 * τ * (A * W ^ 2 * W) * Q ^ 2 := by ring
      _ = _ := by rw [this]
  have hq3 : Q ^ 3 ≤ 1 + 49 * τ := by
    have h7 : 0 ≤ 7 * τ := by positivity
    have h71 : 7 * τ ≤ 1 := by linarith
    rw [hQ]
    nlinarith [mul_nonneg h7 h7, mul_nonneg (mul_nonneg h7 h7) h7,
      mul_nonneg h7 (sub_nonneg.2 h71), mul_nonneg (mul_nonneg h7 h7) (sub_nonneg.2 h71)]
  have hq2 : Q ^ 2 ≤ 4 := by nlinarith
  have hbr : 2 / 3 * Q ^ 3 + 10 * τ * Q ^ 2 ≤ 2 / 3 * (1 + 109 * τ) := by nlinarith
  have hfin : ϑ ^ 2 * W * (2 / 3 * (1 + 109 * τ)) =
      c0 * kappaHat l * ϑ ^ 3 * (1 + 1199 / ϑ) := by
    have e3 : W = ϑ * (Real.sqrt 2 * kappaHat l) := by
      rw [← inv_sqrt_expA hl, hW, ← hA, ← hs]
      ring
    have e4 : 109 * τ = 1199 / ϑ := by rw [hτ]; ring
    rw [e4, e3]
    unfold c0
    ring
  have hP : 0 ≤ ϑ ^ 2 * W := by positivity
  calc _ ≤ 2 / 3 * A * (W + 7 * L) ^ 3 + 10 * L * A * (W + 7 * L) ^ 2 := h2
    _ ≤ 2 / 3 * (ϑ ^ 2 * W) * Q ^ 3 + 10 * τ * (ϑ ^ 2 * W) * Q ^ 2 := add_le_add c3 c4
    _ = ϑ ^ 2 * W * (2 / 3 * Q ^ 3 + 10 * τ * Q ^ 2) := by ring
    _ ≤ ϑ ^ 2 * W * (2 / 3 * (1 + 109 * τ)) := mul_le_mul_of_nonneg_left hbr hP
    _ = _ := hfin

/-- Total degree of an exponent in the set at scale `ϑ`. -/
theorem deg_of_mem_expSet {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) {L : ℝ} (hL : ∀ i, l i ≤ L)
    (hL6 : ∀ i, L ≤ 6 * l i) {ϑ : ℝ} (hϑ : 0 ≤ ϑ) {e : Fin 3 → ℕ}
    (he : e ∈ expSet l (scaleY l L ϑ)) : (∑ i, (e i : ℝ)) ≤ 30 + 9 * ϑ := by
  have hL0 : 0 < L := lt_of_lt_of_le (hl 0) (hL 0)
  have hw := ((mem_expSet hl).1 he).2
  have h1 : L * ∑ i, (e i : ℝ) ≤ 6 * wt l e := by
    rw [Finset.mul_sum, wt, Finset.mul_sum]
    refine sum_le_sum fun i _ => ?_
    have : (0 : ℝ) ≤ e i := Nat.cast_nonneg _
    nlinarith [hL6 i]
  have hA := expA_pos hl
  set s := Real.sqrt (expA l) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hA
  have hs2 : s ^ 2 = expA l := Real.sq_sqrt hA.le
  have hA2 := le_expA_mul hl hL
  have hLs : 1 ≤ L * s := by
    by_contra hc
    push Not at hc
    have h0 : 0 ≤ L * s := by positivity
    have : (L * s) ^ 2 < 1 ^ 2 := pow_lt_pow_left₀ hc h0 (by norm_num)
    rw [mul_pow, hs2] at this
    nlinarith
  have h2 : ϑ / s ≤ ϑ * L := by
    rw [div_le_iff₀ hs0]
    nlinarith
  have hY : scaleY l L ϑ = 5 * L + ϑ / s := rfl
  rw [hY] at hw
  have h3 : L * ∑ i, (e i : ℝ) ≤ L * (30 + 9 * ϑ) := by nlinarith
  exact le_of_mul_le_mul_left h3 hL0

end OVNS.Quant.Surf
