import OddViscousNS.Closed.Gram

/-!
# The two-band affinity bound (LOCAL685)

Item 6 of `OddViscousNS_data/reports/uf661_row_operator.md`.  For an even probability law `P` on
`ℤ³ ∖ {0}` put `t = ∑ P_j/A_j`, `Q_k = P_k/(t A_k)`, `R_k = ∑_{p+l=k, p×l≠0} P_p P_l`.  Then
`(∑_k √(Q_k R_k))² ≤ F* = F₀ − J₀ d₀ = 151004149/162240000`.

Route: with `a = 11/60`, `U = 1/(tA_p)`, `V = 1/(tA_l)` for independent `p, l ~ P` (so
`E U = E V = 1`), `W = 2UV/(U+V)`, `Δ = E[(U−V)²/(2(U+V))]` (so `E W = 1 − Δ`),
`δ(p,l) = (1+x)/(1+2x) − (1+x)/((1+x)²−y²) ≥ 0` with `x = 2a/W`, `y = 2a t p·l`, `D = E δ`:
(6.1) weighted Cauchy–Schwarz with `ξ_k = 1 + a t A_k` and the reflection `l ↦ −l` give
`H² ≤ F₀ − J₀Δ − (1+a)D`, `F₀ = 2911/3120`, `J₀ = 781/5408`;
(6.2) the input band `U ∈ [.53, 1.62]` and output band `A_b ≤ tA_k ≤ B_b` give
`P_band ≥ 1 − p*Δ`, `Q_band ≥ 1 − q*Δ`, `R_band ≤ 1 − (1 − p*Δ)² + D/d*`
(`p* = 30600/2209`, `q* = 21222/961`, `d* = 1759219/262985000`);
(6.3) `H ≤ √(Q_b R_b) + √((1−Q_b)(1−R_b))`;
(6.4) case split at `d₀ = .0157`: either `J₀Δ + (1+a)D ≥ J₀d₀` or `H² ≤ f(q₀,r₀)² < .929316 < F*`.
-/

open scoped ENNReal

namespace OVNS

private def dotR (p l : Mode) : ℝ := ∑ i, (p i : ℝ) * (l i : ℝ)

private lemma absSq_nonneg' (k : Mode) : 0 ≤ absSq k := by
  unfold absSq; positivity

private lemma absSq_add' (p l : Mode) : absSq (p + l) = absSq p + absSq l + 2 * dotR p l := by
  simp only [absSq, dotR, Fin.sum_univ_three, Pi.add_apply]; push_cast; ring

private lemma absSq_sub' (p l : Mode) : absSq (p - l) = absSq p + absSq l - 2 * dotR p l := by
  simp only [absSq, dotR, Fin.sum_univ_three, Pi.sub_apply]; push_cast; ring

private lemma dotR_sq_le (p l : Mode) : dotR p l ^ 2 ≤ absSq p * absSq l := by
  simp only [absSq, dotR, Fin.sum_univ_three]
  nlinarith [sq_nonneg ((p 0 : ℝ) * l 1 - p 1 * l 0), sq_nonneg ((p 0 : ℝ) * l 2 - p 2 * l 0),
    sq_nonneg ((p 1 : ℝ) * l 2 - p 2 * l 1)]

private lemma one_le_absSq' {k : Mode} (hk : k ≠ 0) : 1 ≤ absSq k := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hk
  have h1 : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
  have h2 : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (k i) ^ 2 := by nlinarith [sq_abs (k i)]
    exact_mod_cast this
  calc (1 : ℝ) ≤ (k i : ℝ) ^ 2 := h2
    _ ≤ absSq k := Finset.single_le_sum (f := fun j ↦ (k j : ℝ) ^ 2)
        (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)

private lemma absSq_eq_zero_or {k : Mode} : absSq k = 0 ∨ 1 ≤ absSq k := by
  by_cases hk : k = 0
  · left; subst hk; simp [absSq]
  · exact Or.inr (one_le_absSq' hk)

/-! ### Sums against `P` -/

section Sums
variable {P : Mode → ℝ}

private lemma summ_norm_S (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {f : Mode → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) : Summable fun k ↦ ‖P k * f k‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun k ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hP0 k), mul_comm]
      exact mul_le_mul_of_nonneg_right (hf k) (hP0 k)) (hPs.mul_left C)

private lemma summ_S (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {f : Mode → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) : Summable fun k ↦ P k * f k :=
  (summ_norm_S hP0 hPs hf).of_norm

private lemma summ_PP (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) :
    Summable fun z : Mode × Mode ↦ P z.1 * P z.2 :=
  hPs.mul_of_nonneg hPs (fun k ↦ hP0 k) (fun k ↦ hP0 k)

private lemma summ_E (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {F : Mode → Mode → ℝ}
    {C : ℝ}
    (hF : ∀ p l, |F p l| ≤ C) : Summable fun z : Mode × Mode ↦ P z.1 * P z.2 * F z.1 z.2 :=
  Summable.of_norm_bounded ((summ_PP hP0 hPs).mul_left C)
    (fun z ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hP0 _) (hP0 _)), mul_comm]
      exact mul_le_mul_of_nonneg_right (hF _ _) (mul_nonneg (hP0 _) (hP0 _)))

private lemma hasSum_pair (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {f g : Mode → ℝ}
    {C C' : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ C') :
    HasSum (fun z : Mode × Mode ↦ P z.1 * f z.1 * (P z.2 * g z.2))
      ((∑' k, P k * f k) * ∑' k, P k * g k) :=
  HasSum.mul (f := fun k ↦ P k * f k) (g := fun k ↦ P k * g k) (summ_S hP0 hPs hf).hasSum
    (summ_S hP0 hPs hg).hasSum
    (summable_mul_of_summable_norm (R := ℝ) (f := fun k ↦ P k * f k) (g := fun k ↦ P k * g k)
      (summ_norm_S hP0 hPs hf) (summ_norm_S hP0 hPs hg))

/-- The output sum `∑_k R_k g_k` is bounded by the pair expectation of `g (p + l)`. -/
private lemma R_sum_le (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {g : Mode → ℝ} {C : ℝ}
    (hg0 : ∀ k, 0 ≤ g k) (hgC : ∀ k, g k ≤ C) :
    Summable (fun k ↦ (∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0 then 0
        else P p * P (k - p))) * g k) ∧
      ∑' k, (∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0 then 0
        else P p * P (k - p))) * g k ≤ ∑' z : Mode × Mode, P z.1 * P z.2 * g (z.1 + z.2) := by
  set F : Mode × Mode → ℝ := fun w ↦ (if cross (modeVec w.2) (modeVec (w.1 - w.2)) = 0 then 0
    else P w.2 * P (w.1 - w.2)) * g w.1 with hFdef
  let e : Mode × Mode ≃ Mode × Mode :=
    { toFun := fun z ↦ (z.1 + z.2, z.1)
      invFun := fun w ↦ (w.2, w.1 - w.2)
      left_inv := fun z ↦ by simp
      right_inv := fun w ↦ by simp }
  have hFe : ∀ z, F (e z) = (if cross (modeVec z.1) (modeVec z.2) = 0 then 0
      else P z.1 * P z.2) * g (z.1 + z.2) := fun z ↦ by
    simp [hFdef, e]
  have hle : ∀ z, F (e z) ≤ P z.1 * P z.2 * g (z.1 + z.2) := fun z ↦ by
    rw [hFe]; split_ifs
    · simp only [zero_mul]; exact mul_nonneg (mul_nonneg (hP0 _) (hP0 _)) (hg0 _)
    · exact le_rfl
  have hnn : ∀ z, 0 ≤ F (e z) := fun z ↦ by
    rw [hFe]; split_ifs
    · simp
    · exact mul_nonneg (mul_nonneg (hP0 _) (hP0 _)) (hg0 _)
  have hS2 : Summable fun z : Mode × Mode ↦ P z.1 * P z.2 * g (z.1 + z.2) :=
    summ_E hP0 hPs (C := C) (F := fun p l ↦ g (p + l))
      (fun p l ↦ by rw [abs_of_nonneg (hg0 _)]; exact hgC _)
  have hSe : Summable (F ∘ e) := Summable.of_nonneg_of_le hnn hle hS2
  have hF : Summable F := e.summable_iff.1 hSe
  have hrw : (fun k ↦ (∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0 then 0
        else P p * P (k - p))) * g k) = fun k ↦ ∑' p, F (k, p) := by
    funext k; rw [← tsum_mul_right]
  rw [hrw]
  refine ⟨hF.prod, ?_⟩
  rw [← hF.tsum_prod, ← e.tsum_eq]
  exact hSe.tsum_le_tsum hle hS2

private lemma E_reflect (hPe : ∀ k, P (-k) = P k) (g : Mode → ℝ) :
    ∑' z : Mode × Mode, P z.1 * P z.2 * g (z.1 + z.2) =
      ∑' z : Mode × Mode, P z.1 * P z.2 * g (z.1 - z.2) := by
  let e : Mode × Mode ≃ Mode × Mode := (Equiv.refl Mode).prodCongr (Equiv.neg Mode)
  rw [← e.tsum_eq]
  congr 1; funext z
  simp [e, hPe, sub_eq_add_neg]

end Sums

/-- Weighted Cauchy–Schwarz for nonnegative series. -/
private lemma cs_weighted (Q R ξ : Mode → ℝ) (hQ : ∀ k, 0 ≤ Q k) (hR : ∀ k, 0 ≤ R k)
    (hξ : ∀ k, 0 < ξ k) (h1 : Summable fun k ↦ Q k * ξ k)
    (h2 : Summable fun k ↦ R k / ξ k) :
    (∑' k, Real.sqrt (Q k * R k)) ^ 2 ≤ (∑' k, Q k * ξ k) * ∑' k, R k / ξ k := by
  have amgm : ∀ s : ℝ, 0 < s → ∀ k, Real.sqrt (Q k * R k) ≤
      2⁻¹ * (s * (Q k * ξ k) + s⁻¹ * (R k / ξ k)) := by
    intro s hs k
    have hA : 0 ≤ s * (Q k * ξ k) := by have := hQ k; have := hξ k; positivity
    have hB : 0 ≤ s⁻¹ * (R k / ξ k) := by have := hR k; have := hξ k; positivity
    have hAB : Q k * R k = (s * (Q k * ξ k)) * (s⁻¹ * (R k / ξ k)) := by
      have := (hξ k).ne'; field_simp
    rw [hAB, Real.sqrt_mul hA]
    nlinarith [sq_nonneg (Real.sqrt (s * (Q k * ξ k)) - Real.sqrt (s⁻¹ * (R k / ξ k))),
      Real.sq_sqrt hA, Real.sq_sqrt hB]
  have hsum : ∀ s : ℝ, Summable fun k ↦ 2⁻¹ * (s * (Q k * ξ k) + s⁻¹ * (R k / ξ k)) :=
    fun s ↦ ((h1.mul_left s).add (h2.mul_left s⁻¹)).mul_left _
  have hHs : Summable fun k ↦ Real.sqrt (Q k * R k) :=
    Summable.of_nonneg_of_le (fun _ ↦ Real.sqrt_nonneg _) (by simpa using amgm 1 one_pos)
      (hsum 1)
  set H := ∑' k, Real.sqrt (Q k * R k)
  set A := ∑' k, Q k * ξ k
  set B := ∑' k, R k / ξ k
  have hH0 : 0 ≤ H := tsum_nonneg fun _ ↦ Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := tsum_nonneg fun k ↦ mul_nonneg (hQ k) (hξ k).le
  have hB0 : 0 ≤ B := tsum_nonneg fun k ↦ div_nonneg (hR k) (hξ k).le
  have key : ∀ s : ℝ, 0 < s → H ≤ 2⁻¹ * (s * A + s⁻¹ * B) := by
    intro s hs
    have := hHs.tsum_le_tsum (amgm s hs) (hsum s)
    rwa [tsum_mul_left, (h1.mul_left s).tsum_add (h2.mul_left s⁻¹), tsum_mul_left,
      tsum_mul_left] at this
  rcases hH0.eq_or_lt with h | h
  · rw [← h]; simp; positivity
  rcases hA0.eq_or_lt with hA | hA
  · exfalso
    have := key ((B + 1) / H) (by positivity)
    rw [← hA, inv_div] at this
    rw [mul_zero, zero_add, div_mul_eq_mul_div, ← mul_div_assoc,
      le_div_iff₀ (by positivity)] at this
    nlinarith
  · have := key (H / A) (by positivity)
    rw [inv_div, div_mul_cancel₀ _ hA.ne'] at this
    have h3 : H ≤ A * B / H := by
      have : A / H * B = A * B / H := by ring
      linarith
    rw [le_div_iff₀ h] at h3
    nlinarith

private lemma tang (U V : ℝ) (hU : 0 < U) (hV : 0 < V) :
    (1 + 11/60) * ((1 + 11/60 * (U⁻¹ + V⁻¹)) / (1 + 2 * (11/60) * (U⁻¹ + V⁻¹))) ≤
      2911/3120 + 781/5408 * (2 * U * V / (U + V) - 1) := by
  have hS : U⁻¹ + V⁻¹ = (U + V) / (U * V) := by field_simp; ring
  rw [hS]
  set W := 2 * U * V / (U + V) with hW
  have hWpos : 0 < W := by positivity
  have key : (1 + 11/60 * ((U + V) / (U * V))) / (1 + 2 * (11/60) * ((U + V) / (U * V)))
      = (W + 2 * (11/60)) / (W + 4 * (11/60)) := by
    rw [hW]; field_simp; ring
  rw [key, mul_div_assoc', div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg (W - 1)]

private lemma jens (U V : ℝ) (hU : 0 < U) (hV : 0 < V) :
    (U - 1) ^ 2 / (U + 1) + (1 - 4 * U ^ 2 / (U + 1) ^ 2) * (V - 1) ≤ (U - V) ^ 2 / (U + V) := by
  have h : (U - V) ^ 2 / (U + V) - ((U - 1) ^ 2 / (U + 1) + (1 - 4 * U ^ 2 / (U + 1) ^ 2) * (V - 1))
      = 4 * U ^ 2 * (V - 1) ^ 2 / ((U + V) * (U + 1) ^ 2) := by
    field_simp; ring
  have : 0 ≤ 4 * U ^ 2 * (V - 1) ^ 2 / ((U + V) * (U + 1) ^ 2) := by positivity
  linarith
private lemma outA (U : ℝ) (hU : 0 ≤ U) (h : ¬(53/100 ≤ U ∧ U ≤ 81/50)) :
    2209/15300 ≤ (U - 1) ^ 2 / (U + 1) := by
  rw [le_div_iff₀ (by linarith)]
  rcases not_and_or.1 h with h | h <;> push Not at h <;> nlinarith

private lemma outB (U : ℝ) (hU : 0 ≤ U) (h : ¬(53/100 ≤ U ∧ U ≤ 81/50)) :
    U ≤ 10611/961 * ((U - 1) ^ 2 / (U + 1)) := by
  rw [mul_div_assoc', le_div_iff₀ (by linarith)]
  rcases not_and_or.1 h with h | h <;> push Not at h <;> nlinarith

private lemma cosSmall (X Y s : ℝ) (hX1 : 50/81 ≤ X) (hX2 : X ≤ 100/53) (hY1 : 50/81 ≤ Y)
    (hY2 : Y ≤ 100/53) (hk1 : 50/81 ≤ X + Y + 2 * s) (hk2 : X + Y + 2 * s ≤ 100/53) :
    s ^ 2 < 47961/62500 * (X * Y) := by
  by_contra hc
  push Not at hc
  rcases le_or_gt 0 s with hs | hs
  · have hXY : (50/81:ℝ)^2 ≤ X * Y := by nlinarith
    have : (219/250 * (50/81)) ^ 2 ≤ s ^ 2 := by nlinarith
    have : 219/250 * (50/81) ≤ s := by nlinarith
    linarith
  · have h1 : 4 * s ^ 2 ≤ (X + Y - 50/81) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hX1) (sub_nonneg.2 hX2),
      mul_nonneg (sub_nonneg.2 hY1) (sub_nonneg.2 hY2),
      mul_nonneg (sub_nonneg.2 hX1) (sub_nonneg.2 hY1),
      mul_nonneg (sub_nonneg.2 hX2) (sub_nonneg.2 hY2),
      mul_nonneg (sub_nonneg.2 hX1) (sub_nonneg.2 hY2),
      mul_nonneg (sub_nonneg.2 hX2) (sub_nonneg.2 hY1)]

private lemma deltaFormula (x y : ℝ) (hx : 0 ≤ x) (hy : y ^ 2 ≤ x ^ 2) :
    (1 + x) / (1 + 2 * x) - (1 / (1 + x + y) + 1 / (1 + x - y)) / 2 =
      (1 + x) * (x ^ 2 - y ^ 2) / ((1 + 2 * x) * ((1 + x) ^ 2 - y ^ 2)) := by
  have h1 : 0 < 1 + x + y := by
    by_contra h; push Not at h; nlinarith
  have h2 : 0 < 1 + x - y := by
    by_contra h; push Not at h; nlinarith
  have h3 : 0 < (1 + x) ^ 2 - y ^ 2 := by nlinarith
  field_simp
  ring

private lemma deltaLower (x y : ℝ) (hx : 55/243 ≤ x) (hy : y ^ 2 ≤ 47961/62500 * x ^ 2) :
    1759219/262985000 ≤ (1 + x) * (x ^ 2 - y ^ 2) / ((1 + 2 * x) * ((1 + x) ^ 2 - y ^ 2)) := by
  have h3 : 0 < (1 + x) ^ 2 - y ^ 2 := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  have e1 : (14539/62500) * x ^ 2 * ((1 + x) ^ 2 - y ^ 2) ≤ (x ^ 2 - y ^ 2) * (1 + x) ^ 2 := by
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (sq_nonneg x),
      mul_nonneg (sub_nonneg.2 hy) (add_nonneg (sq_nonneg (1 + x)) (sq_nonneg x))]
  have e2 : 1759219/262985000 * ((1 + 2 * x) * (1 + x)) ≤ (14539/62500) * x ^ 2 := by
    nlinarith
  have hp : 0 < 1 + x := by linarith
  have := mul_le_mul_of_nonneg_left e2 (le_of_lt h3)
  nlinarith [mul_le_mul_of_nonneg_left e1 hp.le]
private lemma finalArith (Dl D π qo : ℝ) (hD : 0 ≤ D) (hπ0 : 0 ≤ π)
    (h1 : 781/5408 * Dl + (1 + 11/60) * D < 781/5408 * (157/10000))
    (hπ : 2209/15300 * π ≤ 2 * Dl) (hq : qo ≤ 10611/961 * (2 * Dl)) :
    (29/50 + 21/50 * qo) * (1 + 21/29 * (1 - (1 - π) ^ 2 + D / (1759219/262985000)))
      < 151004149 / 162240000 := by
  have hd0 : Dl < 157/10000 := by nlinarith
  have hπ' : π ≤ 30600/2209 * Dl := by linarith
  have hb : 30600/2209 * Dl ≤ 1 := by linarith
  have e1 : 1 - (1 - π) ^ 2 ≤ 1 - (1 - 30600/2209 * Dl) ^ 2 := by nlinarith
  have e2 : D / (1759219/262985000) ≤ (781/5408 * (157/10000) - 781/5408 * Dl) /
      ((1 + 11/60) * (1759219/262985000)) := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  have e3 : 1 - (1 - 30600/2209 * Dl) ^ 2 + (781/5408 * (157/10000) - 781/5408 * Dl) /
      ((1 + 11/60) * (1759219/262985000)) ≤ 1 - (1 - 30600/2209 * (157/10000)) ^ 2 := by
    have hid : 1 - (1 - 30600/2209 * (157/10000)) ^ 2 - (1 - (1 - 30600/2209 * Dl) ^ 2 +
        (781/5408 * (157/10000) - 781/5408 * Dl) / ((1 + 11/60) * (1759219/262985000))) =
        453112340380221/131888022947681 * (157/10000 - Dl) +
          936360000/4879681 * (157/10000 - Dl) ^ 2 := by ring
    nlinarith [sq_nonneg (157/10000 - Dl)]
  have hR : 0 ≤ 1 + 21/29 * (1 - (1 - π) ^ 2 + D / (1759219/262985000)) := by
    have : 0 ≤ 1 - (1 - π) ^ 2 := by nlinarith
    positivity
  have hQ : 29/50 + 21/50 * qo ≤ 29/50 + 21/50 * (21222/961 * (157/10000)) := by nlinarith
  calc (29/50 + 21/50 * qo) * (1 + 21/29 * (1 - (1 - π) ^ 2 + D / (1759219/262985000)))
      ≤ (29/50 + 21/50 * (21222/961 * (157/10000))) *
          (1 + 21/29 * (1 - (1 - 30600/2209 * (157/10000)) ^ 2)) := by
        apply mul_le_mul hQ _ hR (by norm_num)
        linarith
    _ < 151004149 / 162240000 := by norm_num

/-! ### The pair variables -/

/-- `X_k = t |k|²`. -/
private noncomputable def Xf (t : ℝ) (k : Mode) : ℝ := t * absSq k
/-- `U_k = 1/(t |k|²)` (and `0` at `k = 0`). -/
private noncomputable def Uf (t : ℝ) (k : Mode) : ℝ := (t * absSq k)⁻¹
/-- `φ(U) = (U-1)²/(U+1)`. -/
private noncomputable def phiU (t : ℝ) (k : Mode) : ℝ := (Uf t k - 1) ^ 2 / (Uf t k + 1)
/-- The slope `1 - 4U²/(U+1)²` of the conditional Jensen tangent. -/
private noncomputable def cU (t : ℝ) (k : Mode) : ℝ := 1 - 4 * Uf t k ^ 2 / (Uf t k + 1) ^ 2
/-- `(1+x)/(1+2x)` with `x = a (X_p + X_l)`. -/
private noncomputable def gx (t : ℝ) (p l : Mode) : ℝ :=
  (1 + 11/60 * ((Uf t p)⁻¹ + (Uf t l)⁻¹)) /
    (1 + 2 * (11/60) * ((Uf t p)⁻¹ + (Uf t l)⁻¹))
/-- `1/ξ_k`. -/
private noncomputable def gk (t : ℝ) (k : Mode) : ℝ := 1 / (1 + 11/60 * Xf t k)
/-- The reflection average `(1/ξ_{p+l} + 1/ξ_{p-l})/2`. -/
private noncomputable def hh (t : ℝ) (p l : Mode) : ℝ := (gk t (p + l) + gk t (p - l)) / 2
/-- The collinearity defect `δ(p,l)`. -/
private noncomputable def dlt (t : ℝ) (p l : Mode) : ℝ := gx t p l - hh t p l
/-- The band indicator `1_{U_k ∈ [.53, 1.62]}`. -/
private noncomputable def bI (t : ℝ) (k : Mode) : ℝ :=
  if 53/100 ≤ Uf t k ∧ Uf t k ≤ 81/50 then 1 else 0

private lemma Uf_inv (t : ℝ) (k : Mode) : (Uf t k)⁻¹ = Xf t k := inv_inv _

private lemma Uf_nonneg {t : ℝ} (ht : 0 < t) (k : Mode) : 0 ≤ Uf t k := by
  unfold Uf; have := absSq_nonneg' k; positivity

private lemma Uf_pos {t : ℝ} (ht : 0 < t) {k : Mode} (hk : k ≠ 0) : 0 < Uf t k := by
  unfold Uf; have := one_le_absSq' hk; have : 0 < absSq k := by linarith
  positivity

private lemma Uf_le {t : ℝ} (ht : 0 < t) (k : Mode) : Uf t k ≤ t⁻¹ := by
  unfold Uf
  rcases absSq_eq_zero_or (k := k) with h | h
  · rw [h, mul_zero, inv_zero]; positivity
  · exact inv_anti₀ ht (by nlinarith)

private lemma Xf_nonneg {t : ℝ} (ht : 0 < t) (k : Mode) : 0 ≤ Xf t k := by
  unfold Xf; have := absSq_nonneg' k; positivity

private lemma gx_eq {t : ℝ} (p l : Mode) :
    gx t p l = (1 + 11/60 * (Xf t p + Xf t l)) / (1 + 2 * (11/60 * (Xf t p + Xf t l))) := by
  unfold gx; rw [Uf_inv, Uf_inv]; ring

private lemma PW1 {t : ℝ} (ht : 0 < t) {p l : Mode} (hp : p ≠ 0) (hl : l ≠ 0) :
    (1 + 11/60) * hh t p l ≤ 2911/3120 - 781/5408/2 * (phiU t p + cU t p * (Uf t l - 1)) +
      781/5408 * ((Uf t p + Uf t l) / 2 - 1) - (1 + 11/60) * dlt t p l := by
  have hU := Uf_pos ht hp
  have hV := Uf_pos ht hl
  have T := tang _ _ hU hV
  have J := jens _ _ hU hV
  have id : 2 * Uf t p * Uf t l / (Uf t p + Uf t l) - 1 =
      (Uf t p + Uf t l) / 2 - 1 - (Uf t p - Uf t l) ^ 2 / (Uf t p + Uf t l) / 2 := by
    field_simp; ring
  unfold dlt phiU cU
  unfold gx at *
  linarith

private lemma xy_bound (t : ℝ) (p l : Mode) :
    (11/60 * (2 * (t * dotR p l))) ^ 2 ≤ (11/60 * (Xf t p + Xf t l)) ^ 2 := by
  have h1 := dotR_sq_le p l
  have hA := absSq_nonneg' p
  have hB := absSq_nonneg' l
  unfold Xf
  have : (2 * dotR p l) ^ 2 ≤ (absSq p + absSq l) ^ 2 := by
    nlinarith [sq_nonneg (absSq p - absSq l)]
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  nlinarith [mul_le_mul_of_nonneg_left this ht2]

private lemma dlt_eq {t : ℝ} (ht : 0 < t) (p l : Mode) :
    dlt t p l = (1 + 11/60 * (Xf t p + Xf t l)) *
      ((11/60 * (Xf t p + Xf t l)) ^ 2 - (11/60 * (2 * (t * dotR p l))) ^ 2) /
      ((1 + 2 * (11/60 * (Xf t p + Xf t l))) *
        ((1 + 11/60 * (Xf t p + Xf t l)) ^ 2 - (11/60 * (2 * (t * dotR p l))) ^ 2)) := by
  have hx : 0 ≤ 11/60 * (Xf t p + Xf t l) := by
    have := Xf_nonneg ht p; have := Xf_nonneg ht l; positivity
  rw [← deltaFormula _ _ hx (xy_bound t p l)]
  unfold dlt hh gk
  rw [gx_eq]
  have e1 : Xf t (p + l) = Xf t p + Xf t l + 2 * (t * dotR p l) := by
    simp only [Xf, absSq_add']; ring
  have e2 : Xf t (p - l) = Xf t p + Xf t l - 2 * (t * dotR p l) := by
    simp only [Xf, absSq_sub']; ring
  rw [e1, e2]; ring

private lemma dlt_nonneg {t : ℝ} (ht : 0 < t) (p l : Mode) : 0 ≤ dlt t p l := by
  rw [dlt_eq ht]
  have hx : 0 ≤ 11/60 * (Xf t p + Xf t l) := by
    have := Xf_nonneg ht p; have := Xf_nonneg ht l; positivity
  have hy := xy_bound t p l
  apply div_nonneg
  · exact mul_nonneg (by linarith) (by linarith)
  · apply mul_nonneg (by linarith); nlinarith

private lemma bI_X {t : ℝ} {k : Mode} (h : bI t k = 1) :
    50/81 ≤ Xf t k ∧ Xf t k ≤ 100/53 := by
  unfold bI at h
  split_ifs at h with hb
  · rw [← Uf_inv]
    have hU : 0 < Uf t k := by linarith [hb.1]
    constructor
    · rw [le_inv_comm₀ (by norm_num) hU]; norm_num; linarith [hb.2]
    · rw [inv_le_comm₀ hU (by norm_num)]; norm_num; linarith [hb.1]
  · norm_num at h

private lemma dlt_band {t : ℝ} (ht : 0 < t) {p l : Mode} (hp : bI t p = 1) (hl : bI t l = 1)
    (hpl : bI t (p + l) = 1) : 1759219/262985000 ≤ dlt t p l := by
  obtain ⟨hX1, hX2⟩ := bI_X hp
  obtain ⟨hY1, hY2⟩ := bI_X hl
  obtain ⟨hk1, hk2⟩ := bI_X hpl
  have e1 : Xf t (p + l) = Xf t p + Xf t l + 2 * (t * dotR p l) := by
    simp only [Xf, absSq_add']; ring
  rw [e1] at hk1 hk2
  have hc := cosSmall _ _ _ hX1 hX2 hY1 hY2 hk1 hk2
  rw [dlt_eq ht]
  apply deltaLower
  · linarith
  · nlinarith [sq_nonneg (Xf t p - Xf t l)]

private lemma bI_cases (t : ℝ) (k : Mode) : bI t k = 0 ∨ bI t k = 1 := by
  unfold bI; split_ifs <;> simp

private lemma PW4 {t : ℝ} (ht : 0 < t) (p l : Mode) :
    bI t (p + l) ≤ 1 - bI t p * bI t l + dlt t p l / (1759219/262985000) := by
  have hd := dlt_nonneg ht p l
  have hd' : 0 ≤ dlt t p l / (1759219/262985000) := by positivity
  rcases bI_cases t (p + l) with h | h
  · rw [h]
    rcases bI_cases t p with h1 | h1 <;> rcases bI_cases t l with h2 | h2 <;>
      rw [h1, h2] <;> linarith
  · rcases bI_cases t p with h1 | h1 <;> rcases bI_cases t l with h2 | h2
    · rw [h, h1, h2]; linarith
    · rw [h, h1, h2]; linarith
    · rw [h, h1, h2]; linarith
    · have := dlt_band ht h1 h2 h
      rw [h, h1, h2, le_div_iff₀ (by norm_num)] at *
      have : 1 ≤ dlt t p l / (1759219/262985000) := by rw [le_div_iff₀ (by norm_num)]; linarith
      linarith

private lemma phiU_nonneg {t : ℝ} (ht : 0 < t) (k : Mode) : 0 ≤ phiU t k := by
  unfold phiU; have := Uf_nonneg ht k; positivity

private lemma PW5a {t : ℝ} (ht : 0 < t) (k : Mode) : 2209/15300 * (1 - bI t k) ≤ phiU t k := by
  have := phiU_nonneg ht k
  unfold bI; split_ifs with h
  · linarith
  · rw [sub_zero, mul_one]; exact outA _ (Uf_nonneg ht k) h

private lemma PW5b {t : ℝ} (ht : 0 < t) (k : Mode) :
    Uf t k * (1 - bI t k) ≤ 10611/961 * phiU t k := by
  have := phiU_nonneg ht k
  unfold bI; split_ifs with h
  · simp only [sub_self, mul_zero]; positivity
  · rw [sub_zero, mul_one]; exact outB _ (Uf_nonneg ht k) h

/-! ### Assembly -/

/-- `R_k = ∑_{p} [p × (k-p) ≠ 0] P_p P_{k-p}`. -/
private noncomputable def Rs (P : Mode → ℝ) (k : Mode) : ℝ :=
  ∑' p : Mode, if cross (modeVec p) (modeVec (k - p)) = 0 then 0 else P p * P (k - p)

private lemma Rs_nonneg {P : Mode → ℝ} (hP0 : ∀ k, 0 ≤ P k) (k : Mode) : 0 ≤ Rs P k :=
  tsum_nonneg fun p ↦ by split_ifs <;> [exact le_rfl; exact mul_nonneg (hP0 _) (hP0 _)]

private lemma E_le_pw {P : Mode → ℝ} (hP0 : ∀ k, 0 ≤ P k) (hPz : P 0 = 0)
    {F G : Mode → Mode → ℝ} {a b : ℝ}
    (hF : HasSum (fun z : Mode × Mode ↦ P z.1 * P z.2 * F z.1 z.2) a)
    (hG : HasSum (fun z : Mode × Mode ↦ P z.1 * P z.2 * G z.1 z.2) b)
    (h : ∀ p l, p ≠ 0 → l ≠ 0 → F p l ≤ G p l) : a ≤ b := by
  refine hasSum_le (fun z ↦ ?_) hF hG
  by_cases h1 : z.1 = 0
  · simp [h1, hPz]
  by_cases h2 : z.2 = 0
  · simp [h2, hPz]
  exact mul_le_mul_of_nonneg_left (h _ _ h1 h2) (mul_nonneg (hP0 _) (hP0 _))

private lemma abs_le_of {x C : ℝ} (h0 : -C ≤ x) (h1 : x ≤ C) : |x| ≤ C :=
  abs_le.2 ⟨h0, h1⟩

private lemma gk_mem {t : ℝ} (ht : 0 < t) (k : Mode) : 0 ≤ gk t k ∧ gk t k ≤ 1 := by
  unfold gk
  have := Xf_nonneg ht k
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]; linarith

private lemma gx_mem {t : ℝ} (ht : 0 < t) (p l : Mode) : 0 ≤ gx t p l ∧ gx t p l ≤ 1 := by
  rw [gx_eq]
  have := Xf_nonneg ht p; have := Xf_nonneg ht l
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]; linarith

private lemma hh_mem {t : ℝ} (ht : 0 < t) (p l : Mode) : 0 ≤ hh t p l ∧ hh t p l ≤ 1 := by
  unfold hh
  have := gk_mem ht (p + l); have := gk_mem ht (p - l)
  constructor <;> linarith

theorem affinity_bound (P : Mode → ℝ) (hP0 : ∀ k, 0 ≤ P k) (hPz : P 0 = 0)
    (hPe : ∀ k, P (-k) = P k) (hPs : Summable P) (hP1 : ∑' k, P k = 1) :
    (∑' k : Mode, Real.sqrt ((if k = 0 then 0 else P k / ((∑' j : Mode, P j / absSq j) * absSq k)) *
      ∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0 then 0 else P p * P (k - p)))) ^ 2
      ≤ Fstar := by
  set t := ∑' j : Mode, P j / absSq j with ht_def
  have hPA : Summable fun j ↦ P j / absSq j := by
    refine Summable.of_nonneg_of_le (fun j ↦ div_nonneg (hP0 j) (absSq_nonneg' j))
      (fun j ↦ ?_) hPs
    rcases absSq_eq_zero_or (k := j) with h | h
    · rw [h, div_zero]; exact hP0 j
    · exact div_le_self (hP0 j) h
  obtain ⟨k0, hk0⟩ : ∃ k, 0 < P k := by
    by_contra h
    push Not at h
    have : ∀ k, P k = 0 := fun k ↦ le_antisymm (h k) (hP0 k)
    simp [this] at hP1
  have hk0ne : k0 ≠ 0 := by rintro rfl; rw [hPz] at hk0; exact lt_irrefl _ hk0
  have ht : 0 < t := hPA.tsum_pos (fun j ↦ div_nonneg (hP0 j) (absSq_nonneg' j)) k0
    (div_pos hk0 (by linarith [one_le_absSq' hk0ne]))
  have hQ : ∀ k, (if k = 0 then 0 else P k / (t * absSq k)) = P k * Uf t k := by
    intro k
    split_ifs with hk
    · rw [hk, hPz, zero_mul]
    · rw [div_eq_mul_inv]; rfl
  simp only [hQ]
  show (∑' k : Mode, Real.sqrt (P k * Uf t k * Rs P k)) ^ 2 ≤ Fstar
  set Hs := ∑' k : Mode, Real.sqrt (P k * Uf t k * Rs P k) with hHs
  -- bounds
  have bU : ∀ k, |Uf t k| ≤ t⁻¹ := fun k ↦
    abs_le_of (by linarith [Uf_nonneg ht k, inv_pos.2 ht]) (Uf_le ht k)
  have b1 : ∀ _k : Mode, |(1 : ℝ)| ≤ 1 := fun _ ↦ by simp
  have bphi : ∀ k, |phiU t k| ≤ t⁻¹ + 1 := fun k ↦ by
    have h0 := phiU_nonneg ht k
    have hU0 := Uf_nonneg ht k
    refine abs_le_of (by linarith [inv_pos.2 ht]) ?_
    unfold phiU
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Uf_le ht k]
  have bc : ∀ k, |cU t k| ≤ 3 := fun k ↦ by
    have hU0 := Uf_nonneg ht k
    have h1 : 0 ≤ 4 * Uf t k ^ 2 / (Uf t k + 1) ^ 2 := by positivity
    have h2 : 4 * Uf t k ^ 2 / (Uf t k + 1) ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    unfold cU; exact abs_le_of (by linarith) (by linarith)
  have bUm : ∀ k, |Uf t k - 1| ≤ t⁻¹ + 1 := fun k ↦
    abs_le_of (by linarith [Uf_nonneg ht k, inv_pos.2 ht]) (by linarith [Uf_le ht k])
  have bbI : ∀ k, |bI t k| ≤ 1 := fun k ↦ by rcases bI_cases t k with h | h <;> simp [h]
  have bdlt : ∀ p l, |dlt t p l| ≤ 1 := fun p l ↦ by
    have := gx_mem ht p l; have := hh_mem ht p l
    unfold dlt; exact abs_le_of (by linarith) (by linarith)
  -- basic sums
  have S1 : ∑' k, P k * 1 = 1 := by simp [hP1]
  have SU : ∑' k, P k * Uf t k = 1 := by
    have : ∀ k, P k * Uf t k = t⁻¹ * (P k / absSq k) := fun k ↦ by
      unfold Uf; rw [mul_inv]; ring
    simp only [this, tsum_mul_left, ← ht_def]
    exact inv_mul_cancel₀ ht.ne'
  have SUm : ∑' k, P k * (Uf t k - 1) = 0 := by
    have : ∀ k, P k * (Uf t k - 1) = P k * Uf t k - P k * 1 := fun k ↦ by ring
    simp only [this]
    rw [(summ_S hP0 hPs bU).tsum_sub (summ_S hP0 hPs b1), SU, S1, sub_self]
  set Φ := ∑' k, P k * phiU t k with hΦ
  set D := ∑' z : Mode × Mode, P z.1 * P z.2 * dlt t z.1 z.2 with hDdef
  have hD0 : 0 ≤ D := tsum_nonneg fun z ↦
    mul_nonneg (mul_nonneg (hP0 _) (hP0 _)) (dlt_nonneg ht _ _)
  have hDs := (summ_E hP0 hPs bdlt).hasSum
  have h11 := hasSum_pair hP0 hPs b1 b1
  -- Case 1: weighted Cauchy–Schwarz with `ξ_k = 1 + a t |k|²`
  have hξ1 : ∀ k, 0 < 1 + 11/60 * Xf t k := fun k ↦ by have := Xf_nonneg ht k; positivity
  have hQ1 : ∀ k, P k * Uf t k * (1 + 11/60 * Xf t k) = P k * Uf t k + 11/60 * P k := by
    intro k
    by_cases hk : k = 0
    · rw [hk, hPz]; ring
    · have : Uf t k * Xf t k = 1 := by
        rw [← Uf_inv]; exact mul_inv_cancel₀ (Uf_pos ht hk).ne'
      linear_combination 11/60 * P k * this
  have A1s : Summable fun k ↦ P k * Uf t k * (1 + 11/60 * Xf t k) := by
    simp only [hQ1]; exact (summ_S hP0 hPs bU).add (hPs.mul_left _)
  have A1 : ∑' k, P k * Uf t k * (1 + 11/60 * Xf t k) = 1 + 11/60 := by
    simp only [hQ1]
    rw [(summ_S hP0 hPs bU).tsum_add (hPs.mul_left _), tsum_mul_left, SU, hP1, mul_one]
  have hRg1 : ∀ k, Rs P k / (1 + 11/60 * Xf t k) = Rs P k * gk t k := fun k ↦ by
    unfold gk; rw [mul_one_div]
  obtain ⟨B1s, B1le⟩ := R_sum_le hP0 hPs (g := gk t) (C := 1) (fun k ↦ (gk_mem ht k).1)
    (fun k ↦ (gk_mem ht k).2)
  replace B1s : Summable fun k ↦ Rs P k * gk t k := B1s
  replace B1le :
      ∑' k, Rs P k * gk t k ≤ ∑' z : Mode × Mode, P z.1 * P z.2 * gk t (z.1 + z.2) :=
    B1le
  have hgs : ∀ g : Mode → ℝ, (∀ k, 0 ≤ g k ∧ g k ≤ 1) →
      Summable fun z : Mode × Mode ↦ P z.1 * P z.2 * g (z.1 + z.2) := fun g hg ↦
    summ_E hP0 hPs (F := fun p l ↦ g (p + l)) (C := 1)
      (fun p l ↦ abs_le_of (by linarith [(hg (p + l)).1]) (hg (p + l)).2)
  have hgs' : Summable fun z : Mode × Mode ↦ P z.1 * P z.2 * gk t (z.1 - z.2) :=
    summ_E hP0 hPs (F := fun p l ↦ gk t (p - l)) (C := 1)
      (fun p l ↦ abs_le_of (by linarith [(gk_mem ht (p - l)).1]) (gk_mem ht (p - l)).2)
  have Ehh : ∑' z : Mode × Mode, P z.1 * P z.2 * gk t (z.1 + z.2) =
      ∑' z : Mode × Mode, P z.1 * P z.2 * hh t z.1 z.2 := by
    have : ∀ z : Mode × Mode, P z.1 * P z.2 * hh t z.1 z.2 =
        2⁻¹ * (P z.1 * P z.2 * gk t (z.1 + z.2) + P z.1 * P z.2 * gk t (z.1 - z.2)) :=
      fun z ↦ by unfold hh; ring
    simp only [this]
    rw [tsum_mul_left, (hgs _ (gk_mem ht)).tsum_add hgs', ← E_reflect hPe]
    ring
  have CS1 := cs_weighted (fun k ↦ P k * Uf t k) (Rs P) (fun k ↦ 1 + 11/60 * Xf t k)
    (fun k ↦ mul_nonneg (hP0 k) (Uf_nonneg ht k)) (Rs_nonneg hP0) hξ1 A1s
    (by simp only [hRg1]; exact B1s)
  simp only [hRg1, A1] at CS1
  have hhs := (summ_E hP0 hPs (F := hh t) (C := 1)
    (fun p l ↦ abs_le_of (by linarith [(hh_mem ht p l).1]) (hh_mem ht p l).2)).hasSum
  have case1 : (1 + 11/60) * ∑' z : Mode × Mode, P z.1 * P z.2 * hh t z.1 z.2 ≤
      2911/3120 - 781/5408/2 * Φ - (1 + 11/60) * D := by
    have hφ := hasSum_pair hP0 hPs bphi b1
    have hc := hasSum_pair hP0 hPs bc bUm
    have hU1 := hasSum_pair hP0 hPs bU b1
    have h1U := hasSum_pair hP0 hPs b1 bU
    have hG := ((((h11.mul_left (2911/3120)).sub ((hφ.add hc).mul_left (781/5408/2))).add
      ((hU1.add h1U).mul_left (781/5408/2))).sub (h11.mul_left (781/5408))).sub
      (hDs.mul_left (1 + 11/60))
    rw [S1, SU, SUm, ← hΦ] at hG
    have hG' : HasSum (fun z : Mode × Mode ↦ P z.1 * P z.2 *
        (2911/3120 - 781/5408/2 * (phiU t z.1 + cU t z.1 * (Uf t z.2 - 1)) +
          781/5408 * ((Uf t z.1 + Uf t z.2) / 2 - 1) - (1 + 11/60) * dlt t z.1 z.2))
        (2911/3120 - 781/5408/2 * Φ - (1 + 11/60) * D) := by
      convert hG using 1
      · funext z; ring
      · ring
    have hF : HasSum (fun z : Mode × Mode ↦ P z.1 * P z.2 * ((1 + 11/60) * hh t z.1 z.2))
        ((1 + 11/60) * ∑' z : Mode × Mode, P z.1 * P z.2 * hh t z.1 z.2) := by
      convert hhs.mul_left (1 + 11/60) using 1
      funext z; ring
    exact E_le_pw hP0 hPz (F := fun p l ↦ (1 + 11/60) * hh t p l)
      (G := fun p l ↦ 2911/3120 - 781/5408/2 * (phiU t p + cU t p * (Uf t l - 1)) +
        781/5408 * ((Uf t p + Uf t l) / 2 - 1) - (1 + 11/60) * dlt t p l) hF hG'
      (fun p l hp hl ↦ PW1 ht hp hl)
  have H1 : Hs ^ 2 ≤ 2911/3120 - 781/5408/2 * Φ - (1 + 11/60) * D := by
    rw [← Ehh] at case1
    have := mul_le_mul_of_nonneg_left B1le (by norm_num : (0:ℝ) ≤ 1 + 11/60)
    linarith
  -- Case 2: two-mass weights `ξ_k = λ` on the band, `μ` off the band
  set PB := ∑' k, P k * bI t k with hPB
  set qo := ∑' k, P k * (Uf t k * (1 - bI t k)) with hqo
  have bUo : ∀ k, |Uf t k * (1 - bI t k)| ≤ t⁻¹ := fun k ↦ by
    have := Uf_nonneg ht k; have := Uf_le ht k
    rcases bI_cases t k with h | h <;> rw [h] <;>
      exact abs_le_of (by nlinarith [inv_pos.2 ht]) (by nlinarith)
  have b1o : ∀ k, |1 - bI t k| ≤ 1 := fun k ↦ by rcases bI_cases t k with h | h <;> simp [h]
  have hξ2 : ∀ k, 0 < 29/50 + 21/50 * (1 - bI t k) := fun k ↦ by
    rcases bI_cases t k with h | h <;> rw [h] <;> norm_num
  have hQ2 : ∀ k, P k * Uf t k * (29/50 + 21/50 * (1 - bI t k)) =
      29/50 * (P k * Uf t k) + 21/50 * (P k * (Uf t k * (1 - bI t k))) := fun k ↦ by ring
  have A2s : Summable fun k ↦ P k * Uf t k * (29/50 + 21/50 * (1 - bI t k)) := by
    simp only [hQ2]
    exact ((summ_S hP0 hPs bU).mul_left _).add ((summ_S hP0 hPs bUo).mul_left _)
  have A2 : ∑' k, P k * Uf t k * (29/50 + 21/50 * (1 - bI t k)) = 29/50 + 21/50 * qo := by
    simp only [hQ2]
    rw [((summ_S hP0 hPs bU).mul_left _).tsum_add ((summ_S hP0 hPs bUo).mul_left _),
      tsum_mul_left, tsum_mul_left, SU, mul_one]
  have hRg2 : ∀ k, Rs P k / (29/50 + 21/50 * (1 - bI t k)) = Rs P k * (1 + 21/29 * bI t k) :=
    fun k ↦ by
      rcases bI_cases t k with h | h <;> rw [h] <;> field_simp <;> ring
  have g2mem : ∀ k, 0 ≤ 1 + 21/29 * bI t k ∧ 1 + 21/29 * bI t k ≤ 2 := fun k ↦ by
    rcases bI_cases t k with h | h <;> rw [h] <;> norm_num
  obtain ⟨B2s, B2le⟩ := R_sum_le hP0 hPs (g := fun k ↦ 1 + 21/29 * bI t k) (C := 2)
    (fun k ↦ (g2mem k).1) (fun k ↦ (g2mem k).2)
  replace B2s : Summable fun k ↦ Rs P k * (1 + 21/29 * bI t k) := B2s
  replace B2le : ∑' k, Rs P k * (1 + 21/29 * bI t k) ≤
      ∑' z : Mode × Mode, P z.1 * P z.2 * (1 + 21/29 * bI t (z.1 + z.2)) := B2le
  have CS2 := cs_weighted (fun k ↦ P k * Uf t k) (Rs P) (fun k ↦ 29/50 + 21/50 * (1 - bI t k))
    (fun k ↦ mul_nonneg (hP0 k) (Uf_nonneg ht k)) (Rs_nonneg hP0) hξ2 A2s
    (by simp only [hRg2]; exact B2s)
  simp only [hRg2, A2] at CS2
  have hF2 := (summ_E hP0 hPs (F := fun p l ↦ 1 + 21/29 * bI t (p + l)) (C := 2)
    (fun p l ↦ abs_le_of (by linarith [(g2mem (p + l)).1]) (g2mem (p + l)).2)).hasSum
  have hBB := hasSum_pair hP0 hPs bbI bbI
  have hG2 := h11.add (((h11.sub hBB).add (hDs.div_const (1759219/262985000))).mul_left (21/29))
  rw [S1] at hG2
  have hG2' : HasSum (fun z : Mode × Mode ↦ P z.1 * P z.2 *
      (1 + 21/29 * (1 - bI t z.1 * bI t z.2 + dlt t z.1 z.2 / (1759219/262985000))))
      (1 + 21/29 * (1 - PB * PB + D / (1759219/262985000))) := by
    convert hG2 using 1
    · funext z; ring
    · ring
  have B2 := E_le_pw hP0 hPz (F := fun p l ↦ 1 + 21/29 * bI t (p + l))
    (G := fun p l ↦ 1 + 21/29 * (1 - bI t p * bI t l + dlt t p l / (1759219/262985000)))
    hF2 hG2' (fun p l _ _ ↦ by have := PW4 ht p l; linarith)
  -- band masses
  have Sout : ∑' k, P k * (1 - bI t k) = 1 - PB := by
    have : ∀ k, P k * (1 - bI t k) = P k * 1 - P k * bI t k := fun k ↦ by ring
    simp only [this]
    rw [(summ_S hP0 hPs b1).tsum_sub (summ_S hP0 hPs bbI), S1]
  have hπ : 2209/15300 * (1 - PB) ≤ Φ := by
    rw [← Sout, ← tsum_mul_left]
    refine (summ_S hP0 hPs b1o |>.mul_left _).tsum_le_tsum (fun k ↦ ?_) (summ_S hP0 hPs bphi)
    have := mul_le_mul_of_nonneg_left (PW5a ht k) (hP0 k)
    linarith
  have hq : qo ≤ 10611/961 * Φ := by
    rw [← tsum_mul_left]
    refine (summ_S hP0 hPs bUo).tsum_le_tsum (fun k ↦ ?_) ((summ_S hP0 hPs bphi).mul_left _)
    have := mul_le_mul_of_nonneg_left (PW5b ht k) (hP0 k)
    linarith
  have hπ0 : 0 ≤ 1 - PB := by
    rw [← Sout]
    exact tsum_nonneg fun k ↦ mul_nonneg (hP0 k) (by rcases bI_cases t k with h | h <;> simp [h])
  have hq0 : 0 ≤ qo := tsum_nonneg fun k ↦ mul_nonneg (hP0 k)
    (mul_nonneg (Uf_nonneg ht k) (by rcases bI_cases t k with h | h <;> simp [h]))
  -- conclusion
  by_contra hcon
  push Not at hcon
  have h1 : 781/5408 * (Φ / 2) + (1 + 11/60) * D < 781/5408 * (157/10000) := by
    unfold Fstar at hcon; linarith
  have fin := finalArith (Φ / 2) D (1 - PB) qo hD0 hπ0 h1 (by linarith) (by linarith)
  rw [sub_sub_cancel] at fin
  have hA2 : 0 ≤ 29/50 + 21/50 * qo := by positivity
  have := mul_le_mul_of_nonneg_left B2 hA2
  unfold Fstar at hcon
  nlinarith

end OVNS
