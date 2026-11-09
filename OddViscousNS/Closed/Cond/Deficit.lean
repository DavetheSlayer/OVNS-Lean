import OddViscousNS.Closed.Cond.Defs

/-!
# The first-shell deficit bound (weighted Cauchy–Schwarz and Jensen)

(vi)–(xi) of §3 of `OddViscousNS_data/reports/u785_unforced_graph.md`.  For an even probability
law `P` on `ℤ³∖{0}` with `t = ∑ P_j/A_j`, `Q_k = P_k/(tA_k)`, first-shell mass
`r = ∑_{|k|²=1} P_k`, `ρ = r/t`, and `R'_k = ∑_{p+l=k, (p,l)∉LL, p×l≠0} P_p P_l`:
`(∑_k √(Q_k R'_k))² ≤ (1+a) G(1 − r², max(0, 1 − rρ − D_LH(ρ,t)))`.
Steps: `ξ_k = 1 + a t A_k`, `∑ Q_k ξ_k = 1 + a`; weighted Cauchy–Schwarz; the reflection
`l ↦ −l`; `½(1/(1+x̃+ỹ) + 1/(1+x̃−ỹ)) ≤ (1+x̃)/(1+2x̃) = g(W)`, `W = 2/(t(A_p+A_l))`; Jensen for
the concave increasing `g` on the complement of `LL` (mass `m = 1 − r²`, mean
`w̄ = E[W 1_{∉LL}] = 1 − Δ − rρ`); `Δ ≥ D_LH` by conditional Jensen on the mixed orientations;
monotonicity of `G`.
-/

open scoped ENNReal

noncomputable section

namespace OVNS

/-! ### Lattice facts -/

private lemma df_absSq_nonneg (k : Mode) : 0 ≤ absSq k := by
  unfold absSq; positivity

private lemma df_one_le_absSq {k : Mode} (hk : k ≠ 0) : 1 ≤ absSq k := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hk
  have h1 : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
  have h2 : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (k i) ^ 2 := by nlinarith [sq_abs (k i)]
    exact_mod_cast this
  calc (1 : ℝ) ≤ (k i : ℝ) ^ 2 := h2
    _ ≤ absSq k := Finset.single_le_sum (f := fun j ↦ (k j : ℝ) ^ 2)
        (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)

private lemma df_nsq_neg (k : Mode) : nsq (-k) = nsq k := by
  simp [nsq]

private lemma df_absSq_of_nsq {k : Mode} (h : nsq k = 1) : absSq k = 1 := by
  have e : absSq k = (nsq k : ℝ) := by
    simp only [absSq, nsq, Nat.cast_sum, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [e, h, Nat.cast_one]

private lemma df_parallelogram (p l : Mode) :
    absSq (p + l) + absSq (p - l) = 2 * (absSq p + absSq l) := by
  simp only [absSq, Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply]; push_cast; ring

/-! ### Real inequalities -/

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


private lemma df_inv_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (2 * y - x) / y ^ 2 ≤ 1 / x := by
  rw [div_le_div_iff₀ (by positivity) hx]; nlinarith [sq_nonneg (x - y)]

private lemma df_refl_avg {a t s X Y : ℝ} (ha : 0 < a) (ht : 0 < t) (hs : 0 < s) (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hXY : X + Y = 2 * (a * t * s)) :
    (1 / (1 + X) + 1 / (1 + Y)) / 2 ≤ (2 / (t * s) + 2 * a) / (2 / (t * s) + 4 * a) := by
  have e : (2 / (t * s) + 2 * a) / (2 / (t * s) + 4 * a) = (2 + X + Y) / (2 * (1 + X + Y)) := by
    rw [show 2 + X + Y = 2 * (1 + a * t * s) by linarith,
      show 1 + X + Y = 1 + 2 * (a * t * s) by linarith]
    field_simp; ring
  rw [e, div_add_div _ _ (by positivity) (by positivity), div_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hX hY) (by positivity : (0 : ℝ) ≤ 2 + X + Y)]

private lemma df_g_tangent {a c W : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hW : 0 ≤ W) :
    (W + 2 * a) / (W + 4 * a) ≤
      1 - 2 * a * ((2 * (c + 4 * a) - (W + 4 * a)) / (c + 4 * a) ^ 2) := by
  have h := df_inv_tangent (x := W + 4 * a) (y := c + 4 * a) (by positivity) (by positivity)
  have e : (W + 2 * a) / (W + 4 * a) = 1 - 2 * a * (1 / (W + 4 * a)) := by
    field_simp; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * a)
  linarith

/-- Constant part of the tangent line of `v ↦ d(u,v)` at `c`. -/
private def Tα (u c : ℝ) : ℝ := u / 2 - 2 * u + 2 * u ^ 2 * (u + 2 * c) / (u + c) ^ 2
/-- Slope of the tangent line of `v ↦ d(u,v)` at `c`. -/
private def Tβ (u c : ℝ) : ℝ := 1 / 2 - 2 * u ^ 2 / (u + c) ^ 2
/-- The tangent line of `v ↦ d(u,v) = (u+v)/2 − 2uv/(u+v)` at `c`. -/
private def Tf (u c v : ℝ) : ℝ := Tα u c + Tβ u c * v

private lemma df_T_le {u c v : ℝ} (hu : 0 < u) (hc : 0 ≤ c) (hv : 0 < v) :
    Tf u c v ≤ (u + v) / 2 - 2 * u * v / (u + v) := by
  have h := df_inv_tangent (x := u + v) (y := u + c) (by positivity) (by positivity)
  have e1 : Tf u c v =
      (u + v) / 2 - 2 * u + 2 * u ^ 2 * ((2 * (u + c) - (u + v)) / (u + c) ^ 2) := by
    simp only [Tf, Tα, Tβ]; field_simp; ring
  have e2 : (u + v) / 2 - 2 * u * v / (u + v) =
      (u + v) / 2 - 2 * u + 2 * u ^ 2 * (1 / (u + v)) := by
    field_simp; ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * u ^ 2)
  linarith

private lemma df_alg {t r : ℝ} (ht : 0 < t) (hr1 : r < 1) (hrt : r ≤ t) :
    2 * r * (Tα (1 / t) ((1 - r / t) / (1 - r)) * (1 - r) +
      Tβ (1 / t) ((1 - r / t) / (1 - r)) * (1 - r / t)) =
      r / t * (1 - t) ^ 2 / (1 + (1 - 2 * (r / t)) * t) := by
  have hD : 0 < 1 + t - 2 * r := by linarith
  have h1r : (1 - r) ≠ 0 := by linarith
  have huc : 1 / t + (1 - r / t) / (1 - r) = (1 + t - 2 * r) / (t * (1 - r)) := by
    field_simp; ring
  have hden : 1 + (1 - 2 * (r / t)) * t = 1 + t - 2 * r := by field_simp; ring
  simp only [Tα, Tβ]
  rw [huc, hden]
  field_simp
  ring


/-! ### Sums over pairs -/

/-- Indicator of the complement of the first-shell pairs `LL`. -/
private def nLL (p l : Mode) : ℝ := if nsq p = 1 ∧ nsq l = 1 then 0 else 1

/-- The output weight `ξ_k = 1 + a t A_k`. -/
private def xi (t : ℝ) (k : Mode) : ℝ := 1 + aC * t * absSq k

/-- `W = 2/(t(A_p + A_l))`. -/
private def Wf (t : ℝ) (p l : Mode) : ℝ := 2 / (t * (absSq p + absSq l))

/-- `g(W) = (W + 2a)/(W + 4a)`. -/
private def gf (W : ℝ) : ℝ := (W + 2 * aC) / (W + 4 * aC)

private lemma aC_pos : 0 < aC := by norm_num [aC]

private lemma nLL_nonneg (p l : Mode) : 0 ≤ nLL p l := by
  unfold nLL; split_ifs <;> norm_num

private lemma nLL_le_one (p l : Mode) : nLL p l ≤ 1 := by
  unfold nLL; split_ifs <;> norm_num

private lemma xi_pos {t : ℝ} (ht : 0 < t) (k : Mode) : 0 < xi t k := by
  have := df_absSq_nonneg k; have := aC_pos; unfold xi; positivity

private lemma Wf_nonneg {t : ℝ} (ht : 0 < t) (p l : Mode) : 0 ≤ Wf t p l := by
  have := df_absSq_nonneg p; have := df_absSq_nonneg l; unfold Wf; positivity

private lemma gf_nonneg {W : ℝ} (hW : 0 ≤ W) : 0 ≤ gf W := by
  have := aC_pos; unfold gf; positivity

private lemma gf_le_one {W : ℝ} (hW : 0 ≤ W) : gf W ≤ 1 := by
  have := aC_pos; unfold gf; rw [div_le_one (by positivity)]; linarith

section Sums
variable {P : Mode → ℝ}

private lemma summ_PP (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) :
    Summable fun z : Mode × Mode ↦ P z.1 * P z.2 :=
  hPs.mul_of_nonneg hPs (fun k ↦ hP0 k) (fun k ↦ hP0 k)

private lemma summ_E (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {F : Mode → Mode → ℝ}
    {C : ℝ} (hF : ∀ p l, |F p l| ≤ C) :
    Summable fun z : Mode × Mode ↦ P z.1 * P z.2 * F z.1 z.2 :=
  Summable.of_norm_bounded ((summ_PP hP0 hPs).mul_left C)
    (fun z ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hP0 _) (hP0 _)), mul_comm]
      exact mul_le_mul_of_nonneg_right (hF _ _) (mul_nonneg (hP0 _) (hP0 _)))

private lemma hasSum_prod' {f g : Mode → ℝ} (hf : Summable f) (hg : Summable g) :
    HasSum (fun z : Mode × Mode ↦ f z.1 * g z.2) ((∑' k, f k) * ∑' k, g k) :=
  hf.hasSum.mul hg.hasSum
    (summable_mul_of_summable_norm (summable_norm_iff.mpr hf) (summable_norm_iff.mpr hg))

private lemma E_reflect (hPe : ∀ k, P (-k) = P k) (F : Mode → Mode → ℝ) :
    ∑' z : Mode × Mode, P z.1 * P z.2 * F z.1 z.2 =
      ∑' z : Mode × Mode, P z.1 * P z.2 * F z.1 (-z.2) := by
  let e : Mode × Mode ≃ Mode × Mode := (Equiv.refl Mode).prodCongr (Equiv.neg Mode)
  rw [← e.tsum_eq]
  congr 1; funext z
  simp [e, hPe]

/-- Output sum to pair sum: `∑_k R'_k/ξ_k ≤ ∑_{(p,l)} P_p P_l 1_{∉LL}/ξ_{p+l}`. -/
private lemma R_sum_le (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {t : ℝ} (ht : 0 < t) :
    Summable (fun k ↦ (∑' p : Mode, (if (nsq p = 1 ∧ nsq (k - p) = 1) ∨
        cross (modeVec p) (modeVec (k - p)) = 0 then 0 else P p * P (k - p))) / xi t k) ∧
      ∑' k, (∑' p : Mode, (if (nsq p = 1 ∧ nsq (k - p) = 1) ∨
        cross (modeVec p) (modeVec (k - p)) = 0 then 0 else P p * P (k - p))) / xi t k ≤
      ∑' z : Mode × Mode, P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 + z.2))) := by
  set F : Mode × Mode → ℝ := fun w ↦ (if (nsq w.2 = 1 ∧ nsq (w.1 - w.2) = 1) ∨
      cross (modeVec w.2) (modeVec (w.1 - w.2)) = 0 then 0
    else P w.2 * P (w.1 - w.2)) / xi t w.1 with hFdef
  let e : Mode × Mode ≃ Mode × Mode :=
    { toFun := fun z ↦ (z.1 + z.2, z.1)
      invFun := fun w ↦ (w.2, w.1 - w.2)
      left_inv := fun z ↦ by simp
      right_inv := fun w ↦ by simp }
  have hFe : ∀ z, F (e z) = (if (nsq z.1 = 1 ∧ nsq z.2 = 1) ∨
      cross (modeVec z.1) (modeVec z.2) = 0 then 0 else P z.1 * P z.2) / xi t (z.1 + z.2) :=
    fun z ↦ by simp [hFdef, e]
  have hle : ∀ z, F (e z) ≤ P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 + z.2))) :=
      fun z ↦ by
    have hx := xi_pos ht (z.1 + z.2)
    have hPP := mul_nonneg (hP0 z.1) (hP0 z.2)
    rw [hFe]; unfold nLL
    split_ifs with h1 h2 h2
    · simp only [zero_div]; positivity
    · simp only [zero_div]; positivity
    · exact absurd (Or.inl h2) h1
    · rw [one_mul, mul_one_div]
  have hnn : ∀ z, 0 ≤ F (e z) := fun z ↦ by
    have hx := xi_pos ht (z.1 + z.2)
    have hPP := mul_nonneg (hP0 z.1) (hP0 z.2)
    rw [hFe]; split_ifs
    · simp
    · positivity
  have hS2 : Summable fun z : Mode × Mode ↦
      P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 + z.2))) :=
    summ_E hP0 hPs (C := 1) (F := fun p l ↦ nLL p l * (1 / xi t (p + l)))
      (fun p l ↦ by
        have hx := xi_pos ht (p + l)
        have hx1 : 1 ≤ xi t (p + l) := by
          have := df_absSq_nonneg (p + l); have := aC_pos; unfold xi
          nlinarith [mul_nonneg (mul_nonneg this.le ht.le) (df_absSq_nonneg (p + l))]
        rw [abs_of_nonneg (mul_nonneg (nLL_nonneg _ _) (by positivity))]
        calc nLL p l * (1 / xi t (p + l)) ≤ 1 * 1 :=
              mul_le_mul (nLL_le_one _ _) (by rw [div_le_one hx]; exact hx1) (by positivity)
                (by norm_num)
          _ = 1 := by norm_num)
  have hSe : Summable (F ∘ e) := Summable.of_nonneg_of_le hnn hle hS2
  have hF : Summable F := e.summable_iff.1 hSe
  have hrw : (fun k ↦ (∑' p : Mode, (if (nsq p = 1 ∧ nsq (k - p) = 1) ∨
        cross (modeVec p) (modeVec (k - p)) = 0 then 0 else P p * P (k - p))) / xi t k) =
      fun k ↦ ∑' p, F (k, p) := by
    funext k; rw [← tsum_div_const]
  rw [hrw]
  refine ⟨hF.prod, ?_⟩
  rw [← hF.tsum_prod, ← e.tsum_eq]
  exact hSe.tsum_le_tsum hle hS2

private lemma summ_W (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {t : ℝ} (ht : 0 < t) :
    Summable fun z : Mode × Mode ↦ P z.1 * P z.2 * (nLL z.1 z.2 * Wf t z.1 z.2) :=
  summ_E hP0 hPs (C := 2 / t) (F := fun p l ↦ nLL p l * Wf t p l) (fun p l ↦ by
    have hW := Wf_nonneg ht p l
    rw [abs_of_nonneg (mul_nonneg (nLL_nonneg _ _) hW)]
    have hW2 : Wf t p l ≤ 2 / t := by
      unfold Wf
      rcases eq_or_ne p 0 with hp | hp
      · rcases eq_or_ne l 0 with hl | hl
        · simp [hp, hl, absSq]; positivity
        · have := df_one_le_absSq hl
          rw [div_le_div_iff₀ (by have := df_absSq_nonneg p; positivity) ht]
          nlinarith [df_absSq_nonneg p]
      · have := df_one_le_absSq hp
        rw [div_le_div_iff₀ (by have := df_absSq_nonneg l; positivity) ht]
        nlinarith [df_absSq_nonneg l]
    calc nLL p l * Wf t p l ≤ 1 * (2 / t) :=
          mul_le_mul (nLL_le_one p l) hW2 hW (by norm_num)
      _ = 2 / t := one_mul _)

private lemma summ_g (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {t : ℝ} (ht : 0 < t) :
    Summable fun z : Mode × Mode ↦ P z.1 * P z.2 * (nLL z.1 z.2 * gf (Wf t z.1 z.2)) :=
  summ_E hP0 hPs (C := 1) (F := fun p l ↦ nLL p l * gf (Wf t p l)) (fun p l ↦ by
    have hW := Wf_nonneg ht p l
    rw [abs_of_nonneg (mul_nonneg (nLL_nonneg _ _) (gf_nonneg hW))]
    calc nLL p l * gf (Wf t p l) ≤ 1 * 1 :=
          mul_le_mul (nLL_le_one p l) (gf_le_one hW) (gf_nonneg hW) (by norm_num)
      _ = 1 := by norm_num)

private lemma summ_fP (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) :
    Summable fun k : Mode ↦ if nsq k = 1 then P k else 0 :=
  Summable.of_nonneg_of_le (fun k ↦ by split_ifs <;> simp [hP0])
    (fun k ↦ by split_ifs <;> simp [hP0]) hPs

private lemma summ_hP (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) :
    Summable fun k : Mode ↦ if nsq k = 1 then 0 else P k :=
  Summable.of_nonneg_of_le (fun k ↦ by split_ifs <;> simp [hP0])
    (fun k ↦ by split_ifs <;> simp [hP0]) hPs

/-- The reflection average: `∑ P_pP_l 1_{∉LL}/ξ_{p+l} ≤ ∑ P_pP_l 1_{∉LL} g(W)`. -/
private lemma refl_bound (hP0 : ∀ k, 0 ≤ P k) (hPz : P 0 = 0) (hPe : ∀ k, P (-k) = P k)
    (hPs : Summable P) {t : ℝ} (ht : 0 < t) :
    ∑' z : Mode × Mode, P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 + z.2))) ≤
      ∑' z : Mode × Mode, P z.1 * P z.2 * (nLL z.1 z.2 * gf (Wf t z.1 z.2)) := by
  have hb : ∀ k, |1 / xi t k| ≤ 1 := fun k ↦ by
    have hx := xi_pos ht k
    have hx1 : 1 ≤ xi t k := by
      have := df_absSq_nonneg k; have := aC_pos; unfold xi
      nlinarith [mul_nonneg (mul_nonneg aC_pos.le ht.le) (df_absSq_nonneg k)]
    rw [abs_of_nonneg (by positivity), div_le_one hx]; exact hx1
  have hnb : ∀ p l x, |x| ≤ 1 → |nLL p l * x| ≤ 1 := fun p l x hx ↦ by
    rw [abs_mul, abs_of_nonneg (nLL_nonneg p l)]
    calc nLL p l * |x| ≤ 1 * 1 := mul_le_mul (nLL_le_one p l) hx (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have h1 : Summable fun z : Mode × Mode ↦
      P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 + z.2))) :=
    summ_E hP0 hPs (F := fun p l ↦ nLL p l * (1 / xi t (p + l))) (fun p l ↦ hnb p l _ (hb _))
  have h2 : Summable fun z : Mode × Mode ↦
      P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 - z.2))) :=
    summ_E hP0 hPs (F := fun p l ↦ nLL p l * (1 / xi t (p - l))) (fun p l ↦ hnb p l _ (hb _))
  have h3 : Summable fun z : Mode × Mode ↦ P z.1 * P z.2 * (nLL z.1 z.2 * gf (Wf t z.1 z.2)) :=
    summ_E hP0 hPs (F := fun p l ↦ nLL p l * gf (Wf t p l)) (fun p l ↦ hnb p l _ (by
      have hW := Wf_nonneg ht p l
      rw [abs_of_nonneg (gf_nonneg hW)]; exact gf_le_one hW))
  have hr : ∑' z : Mode × Mode, P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 + z.2))) =
      ∑' z : Mode × Mode, P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 - z.2))) := by
    have := E_reflect hPe (fun p l ↦ nLL p l * (1 / xi t (p + l)))
    rw [this]; congr 1; funext z
    simp only [nLL, df_nsq_neg, sub_eq_add_neg]
  calc _ = ((∑' z : Mode × Mode, P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 + z.2)))) +
        ∑' z : Mode × Mode, P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 - z.2)))) / 2 := by
          rw [← hr]; ring
    _ = ∑' z : Mode × Mode, (P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 + z.2))) +
        P z.1 * P z.2 * (nLL z.1 z.2 * (1 / xi t (z.1 - z.2)))) / 2 := by
          rw [← h1.tsum_add h2, tsum_div_const]
    _ ≤ _ := by
      refine ((h1.add h2).div_const 2).tsum_le_tsum (fun z ↦ ?_) h3
      by_cases hp : z.1 = 0
      · simp [hp, hPz]
      by_cases hl : z.2 = 0
      · simp [hl, hPz]
      have hs : 0 < absSq z.1 + absSq z.2 := by
        have := df_one_le_absSq hp; have := df_one_le_absSq hl; linarith
      have hX : 0 ≤ aC * t * absSq (z.1 + z.2) := by
        have := df_absSq_nonneg (z.1 + z.2); have := aC_pos; positivity
      have hY : 0 ≤ aC * t * absSq (z.1 - z.2) := by
        have := df_absSq_nonneg (z.1 - z.2); have := aC_pos; positivity
      have key := df_refl_avg aC_pos ht hs hX hY
        (by linear_combination (aC * t) * df_parallelogram z.1 z.2)
      have hnn : 0 ≤ P z.1 * P z.2 * nLL z.1 z.2 :=
        mul_nonneg (mul_nonneg (hP0 _) (hP0 _)) (nLL_nonneg _ _)
      have := mul_le_mul_of_nonneg_left key hnn
      simp only [xi, gf, Wf]
      linear_combination this

/-- The mass of the complement of `LL` is `1 − r²`. -/
private lemma mass_hasSum (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) (hP1 : ∑' k, P k = 1) :
    HasSum (fun z : Mode × Mode ↦ P z.1 * P z.2 * nLL z.1 z.2)
      (1 - (∑' k : Mode, if nsq k = 1 then P k else 0) ^ 2) := by
  have h := (hasSum_prod' hPs hPs).sub (hasSum_prod' (summ_fP hP0 hPs) (summ_fP hP0 hPs))
  rw [hP1] at h
  convert h using 1
  · funext z; unfold nLL
    by_cases h1 : nsq z.1 = 1 <;> by_cases h2 : nsq z.2 = 1 <;> simp [h1, h2]
  · ring

private lemma df_pw_w {t c Ap Al Pp Pl : ℝ} {fp fl : Prop} [Decidable fp] [Decidable fl]
    (ht : 0 < t) (hc : 0 ≤ c) (hAp : 1 ≤ Ap) (hAl : 1 ≤ Al) (hfp : fp → Ap = 1)
    (hfl : fl → Al = 1) (hPp : 0 ≤ Pp) (hPl : 0 ≤ Pl) :
    Pp * Pl * ((if fp ∧ fl then 0 else 1) * (2 / (t * (Ap + Al)))) ≤
      Pp * (1 / (t * Ap)) * Pl / 2 + Pp * (Pl * (1 / (t * Al))) / 2
      - (if fp then Pp else 0) * (if fl then Pl else 0) / t
      - (if fp then Pp else 0) * ((if fl then 0 else Pl) * Tf (1 / t) c (1 / (t * Al)))
      - ((if fp then 0 else Pp) * Tf (1 / t) c (1 / (t * Ap))) * (if fl then Pl else 0) := by
  have hPP : 0 ≤ Pp * Pl := mul_nonneg hPp hPl
  have hu : 0 < 1 / t := by positivity
  by_cases h1 : fp <;> by_cases h2 : fl
  · rw [hfp h1, hfl h2]
    simp only [h1, h2, and_self, ↓reduceIte]
    apply le_of_eq; field_simp; ring
  · rw [hfp h1]
    simp only [h1, h2, and_false, ↓reduceIte]
    have hv : 0 < 1 / (t * Al) := by positivity
    have hT := df_T_le hu hc hv
    have hW : 2 * (1 / t) * (1 / (t * Al)) / (1 / t + 1 / (t * Al)) = 2 / (t * (1 + Al)) := by
      field_simp; ring
    rw [hW] at hT
    have key := mul_le_mul_of_nonneg_left
      (show 2 / (t * (1 + Al)) ≤ (1 / t + 1 / (t * Al)) / 2 - Tf (1 / t) c (1 / (t * Al)) by
        linarith) hPP
    linear_combination key
  · rw [hfl h2]
    simp only [h1, h2, and_true, ↓reduceIte]
    have hv : 0 < 1 / (t * Ap) := by positivity
    have hT := df_T_le hu hc hv
    have hW : 2 * (1 / t) * (1 / (t * Ap)) / (1 / t + 1 / (t * Ap)) = 2 / (t * (Ap + 1)) := by
      field_simp
    rw [hW] at hT
    have key := mul_le_mul_of_nonneg_left
      (show 2 / (t * (Ap + 1)) ≤ (1 / t + 1 / (t * Ap)) / 2 - Tf (1 / t) c (1 / (t * Ap)) by
        linarith) hPP
    linear_combination key
  · simp only [h1, h2, and_self, ↓reduceIte]
    have hAM : 2 / (t * (Ap + Al)) ≤ (1 / (t * Ap) + 1 / (t * Al)) / 2 := by
      have e : (1 / (t * Ap) + 1 / (t * Al)) / 2 - 2 / (t * (Ap + Al)) =
          (Ap - Al) ^ 2 / (2 * t * Ap * Al * (Ap + Al)) := by
        field_simp; ring
      have : 0 ≤ (Ap - Al) ^ 2 / (2 * t * Ap * Al * (Ap + Al)) := by
        have : 0 < Ap := by linarith
        have : 0 < Al := by linarith
        positivity
      linarith
    have key := mul_le_mul_of_nonneg_left hAM hPP
    linear_combination key

/-- Jensen for the concave increasing `g` (tangent line at `c = M/m`). -/
private lemma jensen_bound (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {t m w M : ℝ} (ht : 0 < t)
    (hm : HasSum (fun z : Mode × Mode ↦ P z.1 * P z.2 * nLL z.1 z.2) m)
    (hw : HasSum (fun z : Mode × Mode ↦ P z.1 * P z.2 * (nLL z.1 z.2 * Wf t z.1 z.2)) w)
    (hm0 : 0 < m) (hM : 0 ≤ M) (hwM : w ≤ M) :
    ∑' z : Mode × Mode, P z.1 * P z.2 * (nLL z.1 z.2 * gf (Wf t z.1 z.2)) ≤ Gfun m M := by
  set c := M / m with hcdef
  have hc : 0 ≤ c := div_nonneg hM hm0.le
  have ha := aC_pos
  have hL := summ_g hP0 hPs ht
  have h := hasSum_le (fun z ↦ ?_) hL.hasSum
    ((hm.mul_left (1 - 2 * aC * ((2 * (c + 4 * aC) - 4 * aC) / (c + 4 * aC) ^ 2))).add
      (hw.mul_left (2 * aC / (c + 4 * aC) ^ 2)))
  · have hK : 0 ≤ 2 * aC / (c + 4 * aC) ^ 2 := by positivity
    calc _ ≤ _ := h
      _ ≤ (1 - 2 * aC * ((2 * (c + 4 * aC) - 4 * aC) / (c + 4 * aC) ^ 2)) * m +
          2 * aC / (c + 4 * aC) ^ 2 * M := by nlinarith
      _ = Gfun m M := by
        unfold Gfun; simp only [hm0.ne', ↓reduceIte]; rw [hcdef]
        have : 0 < M + 4 * aC * m := by positivity
        field_simp; ring
  · have hg := df_g_tangent ha hc (Wf_nonneg ht z.1 z.2)
    have hnn : 0 ≤ P z.1 * P z.2 * nLL z.1 z.2 :=
      mul_nonneg (mul_nonneg (hP0 _) (hP0 _)) (nLL_nonneg _ _)
    have := mul_le_mul_of_nonneg_left hg hnn
    simp only [gf]
    linear_combination this

/-- The mean of `W` off `LL`: `w̄ ≤ 1 − rρ − D_LH(ρ,t)` (conditional Jensen on the mixed
pairs). -/
private lemma wbar_le (hP0 : ∀ k, 0 ≤ P k) (hPz : P 0 = 0) (hPs : Summable P)
    (hP1 : ∑' k, P k = 1) {t r : ℝ} (ht : 0 < t) (htdef : t = ∑' j : Mode, P j / absSq j)
    (hrdef : r = ∑' k : Mode, if nsq k = 1 then P k else 0) (hr1 : r < 1) (hrt : r ≤ t) :
    ∑' z : Mode × Mode, P z.1 * P z.2 * (nLL z.1 z.2 * Wf t z.1 z.2) ≤
      1 - r * (r / t) - DLH (r / t) t := by
  set c := (1 - r / t) / (1 - r) with hcdef
  have hc0 : 0 ≤ c := div_nonneg (by rw [sub_nonneg, div_le_one ht]; exact hrt) (by linarith)
  have hfs := summ_fP hP0 hPs
  have hhs := summ_hP hP0 hPs
  have hPA_le : ∀ k, P k / absSq k ≤ P k := fun k ↦ by
    rcases eq_or_ne k 0 with h | h
    · simp [h, hPz]
    · exact div_le_self (hP0 k) (df_one_le_absSq h)
  have hPA_nn : ∀ k, 0 ≤ P k / absSq k := fun k ↦ div_nonneg (hP0 k) (df_absSq_nonneg k)
  have hPAs : Summable fun k ↦ P k / absSq k := Summable.of_nonneg_of_le hPA_nn hPA_le hPs
  have hPU : ∀ k, P k * (1 / (t * absSq k)) = P k / absSq k / t := fun k ↦ by ring
  have hPUs : Summable fun k ↦ P k * (1 / (t * absSq k)) := by
    simp_rw [hPU]; exact hPAs.div_const t
  have hPUsum : ∑' k, P k * (1 / (t * absSq k)) = 1 := by
    simp_rw [hPU]; rw [tsum_div_const, ← htdef, div_self ht.ne']
  have hU0 : ∀ k, 0 ≤ 1 / (t * absSq k) := fun k ↦ by
    have := df_absSq_nonneg k; positivity
  have hhU : Summable fun k ↦ (if nsq k = 1 then 0 else P k) * (1 / (t * absSq k)) :=
    Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (by split_ifs <;> simp [hP0]) (hU0 k))
      (fun k ↦ mul_le_mul_of_nonneg_right (by split_ifs <;> simp [hP0]) (hU0 k)) hPUs
  have hhsum : ∑' k, (if nsq k = 1 then 0 else P k) = 1 - r := by
    have e : (fun k : Mode ↦ if nsq k = 1 then 0 else P k) =
        fun k ↦ P k - if nsq k = 1 then P k else 0 := by
      funext k; split_ifs <;> ring
    rw [e, hPs.tsum_sub hfs, hP1, hrdef]
  have hhUsum : ∑' k, (if nsq k = 1 then 0 else P k) * (1 / (t * absSq k)) = 1 - r / t := by
    have e : (fun k : Mode ↦ (if nsq k = 1 then 0 else P k) * (1 / (t * absSq k))) =
        fun k ↦ P k * (1 / (t * absSq k)) - (if nsq k = 1 then P k else 0) / t := by
      funext k; split_ifs with h
      · rw [df_absSq_of_nsq h]; ring
      · ring
    rw [e, hPUs.tsum_sub (hfs.div_const t), hPUsum, tsum_div_const, hrdef]
  have hTs : HasSum (fun l ↦ (if nsq l = 1 then 0 else P l) * Tf (1 / t) c (1 / (t * absSq l)))
      (Tα (1 / t) c * (1 - r) + Tβ (1 / t) c * (1 - r / t)) := by
    have := (hhs.hasSum.mul_left (Tα (1 / t) c)).add (hhU.hasSum.mul_left (Tβ (1 / t) c))
    rw [hhsum, hhUsum] at this
    convert this using 1
    funext l; simp only [Tf]; ring
  have hR := ((((hasSum_prod' hPUs hPs).div_const 2).add
    ((hasSum_prod' hPs hPUs).div_const 2)).sub ((hasSum_prod' hfs hfs).div_const t)).sub
    (hasSum_prod' hfs hTs.summable) |>.sub (hasSum_prod' hTs.summable hfs)
  have hL := summ_W hP0 hPs ht
  have h := hasSum_le (fun z ↦ ?_) hL.hasSum hR
  · refine h.trans (le_of_eq ?_)
    rw [hPUsum, hP1, ← hrdef, hTs.tsum_eq]
    have hD : 1 + (1 - 2 * (r / t)) * t ≠ 0 := by
      have : 1 + (1 - 2 * (r / t)) * t = 1 + t - 2 * r := by field_simp; ring
      rw [this]; linarith
    have halg := df_alg ht hr1 hrt
    unfold DLH; simp only [hD, ↓reduceIte]
    rw [← halg, hcdef]; ring
  · by_cases hp : z.1 = 0
    · simp [hp, hPz]
    by_cases hl : z.2 = 0
    · simp [hl, hPz]
    exact df_pw_w ht hc0 (df_one_le_absSq hp) (df_one_le_absSq hl) df_absSq_of_nsq
      df_absSq_of_nsq (hP0 _) (hP0 _)

end Sums

/-! ### The main bound -/

theorem deficit_bound (P : Mode → ℝ) (hP0 : ∀ k, 0 ≤ P k) (hPz : P 0 = 0)
    (hPe : ∀ k, P (-k) = P k) (hPs : Summable P) (hP1 : ∑' k, P k = 1) :
    let t := ∑' j : Mode, P j / absSq j
    let r := ∑' k : Mode, if nsq k = 1 then P k else 0
    (∑' k : Mode, Real.sqrt ((if k = 0 then 0 else P k / (t * absSq k)) *
      ∑' p : Mode, (if (nsq p = 1 ∧ nsq (k - p) = 1) ∨ cross (modeVec p) (modeVec (k - p)) = 0
        then 0 else P p * P (k - p)))) ^ 2 ≤
      (1 + aC) * Gfun (1 - r ^ 2) (max 0 (1 - r * (r / t) - DLH (r / t) t)) := by
  intro t r
  have ha := aC_pos
  have hPA_le : ∀ k, P k / absSq k ≤ P k := fun k ↦ by
    rcases eq_or_ne k 0 with h | h
    · simp [h, hPz]
    · exact div_le_self (hP0 k) (df_one_le_absSq h)
  have hPA_nn : ∀ k, 0 ≤ P k / absSq k := fun k ↦ div_nonneg (hP0 k) (df_absSq_nonneg k)
  have hPAs : Summable fun k ↦ P k / absSq k := Summable.of_nonneg_of_le hPA_nn hPA_le hPs
  have ht1 : t ≤ 1 := by rw [← hP1]; exact hPAs.tsum_le_tsum hPA_le hPs
  have htpos : 0 < t := by
    obtain ⟨k, hk⟩ : ∃ k, P k ≠ 0 := by
      by_contra h; simp only [not_exists, not_not] at h; simp [h] at hP1
    have hk0 : k ≠ 0 := fun h ↦ hk (h ▸ hPz)
    have : 0 < P k / absSq k :=
      div_pos (lt_of_le_of_ne (hP0 k) (Ne.symm hk)) (by linarith [df_one_le_absSq hk0])
    exact hPAs.tsum_pos hPA_nn k this
  have hfle : ∀ k, (if nsq k = 1 then P k else 0) ≤ P k / absSq k := fun k ↦ by
    split_ifs with h
    · rw [df_absSq_of_nsq h, div_one]
    · exact hPA_nn k
  have hfnn : ∀ k, 0 ≤ (if nsq k = 1 then P k else 0) := fun k ↦ by
    split_ifs <;> simp [hP0]
  have hrt : r ≤ t := (summ_fP hP0 hPs).tsum_le_tsum hfle hPAs
  have hr0 : 0 ≤ r := tsum_nonneg hfnn
  have hQ : ∀ k, (if k = 0 then 0 else P k / (t * absSq k)) = P k * (1 / (t * absSq k)) := by
    intro k; split_ifs with h
    · simp [h, hPz]
    · ring
  simp only [hQ]
  have hR := R_sum_le hP0 hPs htpos
  have hQξ : ∀ k, P k * (1 / (t * absSq k)) * xi t k = P k / absSq k / t + aC * P k := by
    intro k; rcases eq_or_ne k 0 with h | h
    · simp [h, hPz]
    · have := df_one_le_absSq h; unfold xi; field_simp
  have h1 : Summable fun k ↦ P k * (1 / (t * absSq k)) * xi t k := by
    simp_rw [hQξ]; exact (hPAs.div_const t).add (hPs.mul_left aC)
  have h1v : ∑' k, P k * (1 / (t * absSq k)) * xi t k = 1 + aC := by
    simp_rw [hQξ]
    rw [(hPAs.div_const t).tsum_add (hPs.mul_left aC), tsum_div_const, tsum_mul_left, hP1,
      show (∑' j, P j / absSq j) = t from rfl, div_self htpos.ne', mul_one]
  have hRnn : ∀ k, 0 ≤ ∑' p : Mode, (if (nsq p = 1 ∧ nsq (k - p) = 1) ∨
      cross (modeVec p) (modeVec (k - p)) = 0 then 0 else P p * P (k - p)) := fun k ↦
    tsum_nonneg fun p ↦ by split_ifs <;> simp [mul_nonneg (hP0 _) (hP0 _)]
  have hcs := cs_weighted (fun k ↦ P k * (1 / (t * absSq k))) _ (xi t)
    (fun k ↦ mul_nonneg (hP0 k) (by have := df_absSq_nonneg k; positivity)) hRnn
    (xi_pos htpos) h1 hR.1
  have hY1 := hR.2.trans (refl_bound hP0 hPz hPe hPs htpos)
  have hm := mass_hasSum hP0 hPs hP1
  have hY : ∑' k, (∑' p : Mode, (if (nsq p = 1 ∧ nsq (k - p) = 1) ∨
      cross (modeVec p) (modeVec (k - p)) = 0 then 0 else P p * P (k - p))) / xi t k ≤
      Gfun (1 - r ^ 2) (max 0 (1 - r * (r / t) - DLH (r / t) t)) := by
    rcases (show r ≤ 1 by linarith).lt_or_eq with hr1 | hr1
    · have hm0 : 0 < 1 - r ^ 2 := by nlinarith
      have hw := wbar_le hP0 hPz hPs hP1 htpos rfl rfl hr1 hrt
      have hws := summ_W hP0 hPs htpos
      exact hY1.trans (jensen_bound hP0 hPs htpos hm hws.hasSum hm0 (le_max_left _ _)
        (hw.trans (le_max_right _ _)))
    · have hle : ∑' z : Mode × Mode, P z.1 * P z.2 * (nLL z.1 z.2 * gf (Wf t z.1 z.2)) ≤
          ∑' z : Mode × Mode, P z.1 * P z.2 * nLL z.1 z.2 := by
        refine Summable.tsum_le_tsum (fun z ↦ ?_) (summ_g hP0 hPs htpos) hm.summable
        have hW := Wf_nonneg htpos z.1 z.2
        have hnn : 0 ≤ P z.1 * P z.2 * nLL z.1 z.2 :=
          mul_nonneg (mul_nonneg (hP0 _) (hP0 _)) (nLL_nonneg _ _)
        have := mul_le_mul_of_nonneg_left (gf_le_one hW) hnn
        linear_combination this
      rw [hm.tsum_eq] at hle
      have hG : Gfun (1 - r ^ 2) (max 0 (1 - r * (r / t) - DLH (r / t) t)) = 0 := by
        rw [hr1]; simp [Gfun]
      rw [hG]
      have : (1 : ℝ) - (∑' k : Mode, if nsq k = 1 then P k else 0) ^ 2 = 0 := by
        rw [show (∑' k : Mode, if nsq k = 1 then P k else 0) = r from rfl, hr1]; norm_num
      linarith
  calc _ ≤ _ := hcs
    _ = (1 + aC) * _ := by rw [h1v]
    _ ≤ _ := mul_le_mul_of_nonneg_left hY (by positivity)

end OVNS

end
