import OddViscousNS.Closed.Forced.Moment.Defs
import OddViscousNS.Closed.Cond.Deficit
import OddViscousNS.Closed.GTable

/-!
# The moment master inequality

`moment_master`: for a probability `P` on modes (`P 0 = 0`, even, summable, total mass 1),
`t = ∑ P_j/|j|²`, a row price `0 ≤ g ≤ M₀`, weights `a, bL ≥ 0`, and `0 ≤ λ ≤ K` with the
pointwise bound `T(p,ℓ) − λ(V(p,ℓ) − 1) ≤ K` on non-collinear pairs,
`(∑_k √(Q_k g_k R_k))² ≤ (1 + a + bL ∑_k Q_k/h_k) K`
where `Q_k = P_k/(t|k|²)` and `R_k = ∑_{p+ℓ=k, p×ℓ≠0} P_p P_ℓ`.

`cubic_le_moment`: the field version through `cubic_le_rowchain` with `g = gOVNS`:
`|C(w)|² ≤ (1 + a + bL X/Y) K · Y Z²` under `RowBound gOVNS`, when the pointwise bound holds at
`t = Y/Z`.
-/

open scoped BigOperators

namespace OVNS

namespace Forced

/-! ### Lattice facts -/

private lemma mm_absSq_zero : absSq 0 = 0 := by
  simp [absSq]

private lemma mm_hm_zero : hm 0 = 0 := by
  simp [hm, hmet, nsq]

private lemma mm_hm_pos {k : Mode} (hk : k ≠ 0) : 0 < hm k :=
  hmet_pos (Nat.one_le_iff_ne_zero.2 fun h ↦ hk ((nsq_eq_zero_iff k).1 h))

private lemma mm_hm_nonneg (k : Mode) : 0 ≤ hm k := by
  by_cases hk : k = 0
  · rw [hk, mm_hm_zero]
  · exact (mm_hm_pos hk).le

private lemma mm_one_le_hm {k : Mode} (hk : k ≠ 0) : 1 ≤ hm k := by
  have hj : 1 ≤ nsq k := Nat.one_le_iff_ne_zero.2 fun h ↦ hk ((nsq_eq_zero_iff k).1 h)
  have h1 : hmet 1 = 1 := by norm_num [hmet, hmetTable]
  unfold hm
  rcases hj.eq_or_lt with h | h
  · rw [← h, h1]
  · calc (1 : ℝ) = hmet 1 := h1.symm
      _ ≤ hmet (nsq k) := (hmet_lt_hmet le_rfl h).le

private lemma mm_hm_neg (k : Mode) : hm (-k) = hm k := by
  simp [hm, nsq, Int.natAbs_neg]

private lemma mm_modeVec_neg (l : Mode) : modeVec (-l) = -modeVec l := by
  ext i; simp [modeVec]

private lemma mm_cross_neg (a b : V3) : cross a (-b) = -cross a b := by
  ext i; fin_cases i <;> simp [cross] <;> ring

private lemma mm_aw_nonneg (u : Field) (k : Mode) : 0 ≤ absSq k * hm k * ‖u k‖ ^ 2 :=
  mul_nonneg (mul_nonneg (absSq_nonneg k) (mm_hm_nonneg k)) (sq_nonneg _)

private lemma mm_summable_aw {u : Field} (hu : Adm 2 u) :
    Summable fun k ↦ absSq k * hm k * ‖u k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (mm_aw_nonneg u) (fun k ↦ ?_) hu.inH
  by_cases hk : k = 0
  · simp [hk, mm_absSq_zero, sobWeight]
  · have h0 := absSq_nonneg k
    have hw : sobWeight 2 k = absSq k ^ 2 := by
      simp only [sobWeight, hk, ↓reduceIte]
      rw [absk, show (2 : ℝ) * 2 = (4 : ℕ) by norm_num, Real.rpow_natCast,
        show 4 = 2 * 2 by rfl, pow_mul, Real.sq_sqrt h0]
    have hh : hm k ≤ absSq k := by
      rw [← nsq_cast]; exact hmet_upper _
    rw [hw, sq (absSq k)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh h0) (sq_nonneg _)

/-! ### Weights -/

private lemma mm_one_le_xi {a bL t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ bL) (ht : 0 ≤ t) (k : Mode) :
    1 ≤ xiM a bL t k := by
  have := absSq_nonneg k
  have := mm_hm_nonneg k
  have : 0 ≤ a * t * absSq k := by positivity
  have : 0 ≤ bL / hm k := by positivity
  unfold xiM
  linarith

private lemma mm_gxi_bound {g : ℕ → ℝ} (hg0 : ∀ j, 0 ≤ g j) (hgM : ∀ j, g j ≤ M₀)
    {a bL t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ bL) (ht : 0 ≤ t) (k : Mode) :
    0 ≤ g (nsq k) / xiM a bL t k ∧ g (nsq k) / xiM a bL t k ≤ M₀ := by
  have hx := mm_one_le_xi ha hb ht k
  refine ⟨div_nonneg (hg0 _) (by linarith), ?_⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith [hg0 (nsq k), hgM (nsq k), mul_le_mul_of_nonneg_left hx ((hg0 (nsq k)).trans (hgM (nsq k)))]

private lemma mm_Tpair_bound {g : ℕ → ℝ} (hg0 : ∀ j, 0 ≤ g j) (hgM : ∀ j, g j ≤ M₀)
    {a bL t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ bL) (ht : 0 ≤ t) (p l : Mode) :
    0 ≤ Tpair g a bL t p l ∧ Tpair g a bL t p l ≤ M₀ := by
  obtain ⟨h1, h2⟩ := mm_gxi_bound hg0 hgM ha hb ht (p + l)
  obtain ⟨h3, h4⟩ := mm_gxi_bound hg0 hgM ha hb ht (p - l)
  unfold Tpair
  constructor <;> linarith

/-- Indicator of non-collinearity. -/
private noncomputable def ncI (p l : Mode) : ℝ := if cross (modeVec p) (modeVec l) = 0 then 0 else 1

private lemma ncI_nonneg (p l : Mode) : 0 ≤ ncI p l := by
  unfold ncI; split_ifs <;> norm_num

private lemma ncI_le_one (p l : Mode) : ncI p l ≤ 1 := by
  unfold ncI; split_ifs <;> norm_num

private lemma ncI_neg (p l : Mode) : ncI p (-l) = ncI p l := by
  simp only [ncI, mm_modeVec_neg, mm_cross_neg, neg_eq_zero]

private lemma ncI_mul_bound {p l : Mode} {x : ℝ} (hx : |x| ≤ M₀) : |ncI p l * x| ≤ M₀ := by
  rw [abs_mul, abs_of_nonneg (ncI_nonneg p l)]
  have hM : 0 ≤ M₀ := (abs_nonneg x).trans hx
  calc ncI p l * |x| ≤ 1 * M₀ := mul_le_mul (ncI_le_one p l) hx (abs_nonneg _) zero_le_one
    _ = M₀ := one_mul _

/-- Weighted Cauchy–Schwarz for nonnegative series. -/
private lemma mm_cs_weighted (Q R ξ : Mode → ℝ) (hQ : ∀ k, 0 ≤ Q k) (hR : ∀ k, 0 ≤ R k)
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

/-! ### Sums over pairs -/

section Sums
variable {P : Mode → ℝ}

private lemma mm_summ_PP (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) :
    Summable fun z : Mode × Mode ↦ P z.1 * P z.2 :=
  hPs.mul_of_nonneg hPs (fun k ↦ hP0 k) (fun k ↦ hP0 k)

private lemma mm_summ_E (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {F : Mode → Mode → ℝ}
    {C : ℝ} (hF : ∀ p l, |F p l| ≤ C) :
    Summable fun z : Mode × Mode ↦ P z.1 * P z.2 * F z.1 z.2 :=
  Summable.of_norm_bounded ((mm_summ_PP hP0 hPs).mul_left C)
    (fun z ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hP0 _) (hP0 _)), mul_comm]
      exact mul_le_mul_of_nonneg_right (hF _ _) (mul_nonneg (hP0 _) (hP0 _)))

private lemma mm_hasSum_prod {f g : Mode → ℝ} (hf : Summable f) (hg : Summable g) :
    HasSum (fun z : Mode × Mode ↦ f z.1 * g z.2) ((∑' k, f k) * ∑' k, g k) :=
  hf.hasSum.mul hg.hasSum
    (summable_mul_of_summable_norm (summable_norm_iff.mpr hf) (summable_norm_iff.mpr hg))

private lemma mm_E_reflect (hPe : ∀ k, P (-k) = P k) (F : Mode → Mode → ℝ) :
    ∑' z : Mode × Mode, P z.1 * P z.2 * F z.1 z.2 =
      ∑' z : Mode × Mode, P z.1 * P z.2 * F z.1 (-z.2) := by
  let e : Mode × Mode ≃ Mode × Mode := (Equiv.refl Mode).prodCongr (Equiv.neg Mode)
  rw [← e.tsum_eq]
  congr 1; funext z
  simp [e, hPe]

private lemma mm_PA (hP0 : ∀ k, 0 ≤ P k) (hPz : P 0 = 0) (hPs : Summable P) :
    (∀ k, 0 ≤ P k / absSq k) ∧ (∀ k, P k / absSq k ≤ P k) ∧
      Summable fun k ↦ P k / absSq k := by
  have hle : ∀ k, P k / absSq k ≤ P k := fun k ↦ by
    rcases eq_or_ne k 0 with h | h
    · simp [h, hPz]
    · exact div_le_self (hP0 k) (one_le_absSq h)
  have hnn : ∀ k, 0 ≤ P k / absSq k := fun k ↦ div_nonneg (hP0 k) (absSq_nonneg k)
  exact ⟨hnn, hle, Summable.of_nonneg_of_le hnn hle hPs⟩

/-- Output sum to pair sum. -/
private lemma gR_sum (hP0 : ∀ k, 0 ≤ P k) (hPs : Summable P) {g : ℕ → ℝ}
    (hg0 : ∀ j, 0 ≤ g j) (hgM : ∀ j, g j ≤ M₀) {a bL t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ bL)
    (ht : 0 ≤ t) :
    Summable (fun k ↦ g (nsq k) * (∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0
        then 0 else P p * P (k - p))) / xiM a bL t k) ∧
      ∑' k, g (nsq k) * (∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0
        then 0 else P p * P (k - p))) / xiM a bL t k =
      ∑' z : Mode × Mode, P z.1 * P z.2 *
        (ncI z.1 z.2 * (g (nsq (z.1 + z.2)) / xiM a bL t (z.1 + z.2))) := by
  set F : Mode × Mode → ℝ := fun w ↦ g (nsq w.1) * (if cross (modeVec w.2)
      (modeVec (w.1 - w.2)) = 0 then 0 else P w.2 * P (w.1 - w.2)) / xiM a bL t w.1 with hFdef
  let e : Mode × Mode ≃ Mode × Mode :=
    { toFun := fun z ↦ (z.1 + z.2, z.1)
      invFun := fun w ↦ (w.2, w.1 - w.2)
      left_inv := fun z ↦ by simp
      right_inv := fun w ↦ by simp }
  have hFe : ∀ z, F (e z) = P z.1 * P z.2 *
      (ncI z.1 z.2 * (g (nsq (z.1 + z.2)) / xiM a bL t (z.1 + z.2))) := fun z ↦ by
    simp only [hFdef, e, Equiv.coe_fn_mk, add_sub_cancel_left, ncI]
    split_ifs <;> ring
  have hS : Summable fun z : Mode × Mode ↦ P z.1 * P z.2 *
      (ncI z.1 z.2 * (g (nsq (z.1 + z.2)) / xiM a bL t (z.1 + z.2))) :=
    mm_summ_E hP0 hPs (C := M₀)
      (F := fun p l ↦ ncI p l * (g (nsq (p + l)) / xiM a bL t (p + l)))
      (fun p l ↦ ncI_mul_bound (by
      obtain ⟨h0, h1⟩ := mm_gxi_bound hg0 hgM ha hb ht (p + l)
      rw [abs_of_nonneg h0]; exact h1))
  have hSe : Summable (F ∘ e) := hS.congr fun z ↦ (hFe z).symm
  have hF : Summable F := e.summable_iff.1 hSe
  have hrw : (fun k ↦ g (nsq k) * (∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0
        then 0 else P p * P (k - p))) / xiM a bL t k) = fun k ↦ ∑' p, F (k, p) := by
    funext k; rw [← tsum_mul_left, ← tsum_div_const]
  rw [hrw]
  refine ⟨hF.prod, ?_⟩
  rw [← hF.tsum_prod, ← e.tsum_eq]
  exact tsum_congr hFe

/-- The reflection `ℓ ↦ −ℓ` turns the pair sum into the pair value `T`. -/
private lemma refl_eq (hP0 : ∀ k, 0 ≤ P k) (hPe : ∀ k, P (-k) = P k) (hPs : Summable P)
    {g : ℕ → ℝ} (hg0 : ∀ j, 0 ≤ g j) (hgM : ∀ j, g j ≤ M₀) {a bL t : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ bL) (ht : 0 ≤ t) :
    ∑' z : Mode × Mode, P z.1 * P z.2 *
        (ncI z.1 z.2 * (g (nsq (z.1 + z.2)) / xiM a bL t (z.1 + z.2))) =
      ∑' z : Mode × Mode, P z.1 * P z.2 * (ncI z.1 z.2 * Tpair g a bL t z.1 z.2) := by
  have hB : ∀ k, |g (nsq k) / xiM a bL t k| ≤ M₀ := fun k ↦ by
    obtain ⟨h0, h1⟩ := mm_gxi_bound hg0 hgM ha hb ht k
    rw [abs_of_nonneg h0]; exact h1
  have h1 : Summable fun z : Mode × Mode ↦ P z.1 * P z.2 *
      (ncI z.1 z.2 * (g (nsq (z.1 + z.2)) / xiM a bL t (z.1 + z.2))) :=
    mm_summ_E hP0 hPs (C := M₀)
      (F := fun p l ↦ ncI p l * (g (nsq (p + l)) / xiM a bL t (p + l)))
      (fun p l ↦ ncI_mul_bound (hB _))
  have h2 : Summable fun z : Mode × Mode ↦ P z.1 * P z.2 *
      (ncI z.1 z.2 * (g (nsq (z.1 - z.2)) / xiM a bL t (z.1 - z.2))) :=
    mm_summ_E hP0 hPs (C := M₀)
      (F := fun p l ↦ ncI p l * (g (nsq (p - l)) / xiM a bL t (p - l)))
      (fun p l ↦ ncI_mul_bound (hB _))
  have hr : ∑' z : Mode × Mode, P z.1 * P z.2 *
        (ncI z.1 z.2 * (g (nsq (z.1 + z.2)) / xiM a bL t (z.1 + z.2))) =
      ∑' z : Mode × Mode, P z.1 * P z.2 *
        (ncI z.1 z.2 * (g (nsq (z.1 - z.2)) / xiM a bL t (z.1 - z.2))) := by
    rw [mm_E_reflect hPe (fun p l ↦ ncI p l * (g (nsq (p + l)) / xiM a bL t (p + l)))]
    congr 1; funext z
    simp only [ncI_neg, sub_eq_add_neg]
  calc _ = ((∑' z : Mode × Mode, P z.1 * P z.2 *
          (ncI z.1 z.2 * (g (nsq (z.1 + z.2)) / xiM a bL t (z.1 + z.2)))) +
        ∑' z : Mode × Mode, P z.1 * P z.2 *
          (ncI z.1 z.2 * (g (nsq (z.1 - z.2)) / xiM a bL t (z.1 - z.2)))) / 2 := by
          rw [← hr]; ring
    _ = ∑' z : Mode × Mode, (P z.1 * P z.2 *
          (ncI z.1 z.2 * (g (nsq (z.1 + z.2)) / xiM a bL t (z.1 + z.2))) +
        P z.1 * P z.2 *
          (ncI z.1 z.2 * (g (nsq (z.1 - z.2)) / xiM a bL t (z.1 - z.2)))) / 2 := by
          rw [← h1.tsum_add h2, tsum_div_const]
    _ = _ := tsum_congr fun z ↦ by simp only [Tpair]; ring

/-- The expectation argument: `E[1_{nc} T] ≤ K`. -/
private lemma expect_le (hP0 : ∀ k, 0 ≤ P k) (hPz : P 0 = 0) (hPs : Summable P)
    (hP1 : ∑' k, P k = 1) {g : ℕ → ℝ} (hg0 : ∀ j, 0 ≤ g j) (hgM : ∀ j, g j ≤ M₀)
    {a bL lam K t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ bL) (hlam : 0 ≤ lam) (hlamK : lam ≤ K)
    (htpos : 0 < t) (ht : t = ∑' j : Mode, P j / absSq j)
    (hpt : ∀ p l : Mode, p ≠ 0 → l ≠ 0 → NonColl p l →
      Tpair g a bL t p l - lam * (Vpair t p l - 1) ≤ K) :
    ∑' z : Mode × Mode, P z.1 * P z.2 * (ncI z.1 z.2 * Tpair g a bL t z.1 z.2) ≤ K := by
  obtain ⟨-, -, hPAs⟩ := mm_PA hP0 hPz hPs
  have hV : HasSum (fun z : Mode × Mode ↦ P z.1 * P z.2 * Vpair t z.1 z.2) 1 := by
    have h := ((mm_hasSum_prod hPAs hPs).add (mm_hasSum_prod hPs hPAs)).div_const (2 * t)
    rw [← ht, hP1] at h
    convert h using 1
    · funext z; simp only [Vpair]; ring
    · field_simp; ring
  have hR := ((mm_hasSum_prod hPs hPs).mul_left (K - lam)).add (hV.mul_left lam)
  rw [hP1] at hR
  have hT : Summable fun z : Mode × Mode ↦
      P z.1 * P z.2 * (ncI z.1 z.2 * Tpair g a bL t z.1 z.2) :=
    mm_summ_E hP0 hPs (C := M₀) (F := fun p l ↦ ncI p l * Tpair g a bL t p l)
      (fun p l ↦ ncI_mul_bound (by
      obtain ⟨h0, h1⟩ := mm_Tpair_bound hg0 hgM ha hb htpos.le p l
      rw [abs_of_nonneg h0]; exact h1))
  have h := hasSum_le (fun z ↦ ?_) hT.hasSum hR
  · linarith
  · have hPP := mul_nonneg (hP0 z.1) (hP0 z.2)
    have hV0 : 0 ≤ Vpair t z.1 z.2 := by
      have := absSq_nonneg z.1; have := absSq_nonneg z.2; unfold Vpair; positivity
    have h1 := mul_nonneg (sub_nonneg.2 hlamK) hPP
    have h2 := mul_nonneg hlam (mul_nonneg hPP hV0)
    by_cases hp : z.1 = 0
    · simp [hp, hPz]
    by_cases hl : z.2 = 0
    · simp [hl, hPz]
    unfold ncI
    split_ifs with hc
    · rw [zero_mul, mul_zero]; linarith
    · have h := mul_le_mul_of_nonneg_left (hpt z.1 z.2 hp hl hc) hPP
      rw [one_mul]
      linear_combination h

/-- The first Cauchy–Schwarz factor `∑ Q_k ξ_k = 1 + a + bL ∑ Q_k/h_k`. -/
private lemma first_factor (hP0 : ∀ k, 0 ≤ P k) (hPz : P 0 = 0) (hPs : Summable P)
    (hP1 : ∑' k, P k = 1) {a bL t : ℝ} (htpos : 0 < t) (ht : t = ∑' j : Mode, P j / absSq j) :
    Summable (fun k ↦ (if k = 0 then 0 else P k / (t * absSq k)) * xiM a bL t k) ∧
      ∑' k, (if k = 0 then 0 else P k / (t * absSq k)) * xiM a bL t k =
        1 + a + bL * ∑' k : Mode, (if k = 0 then 0 else P k / (t * absSq k * hm k)) := by
  obtain ⟨hPAn, -, hPAs⟩ := mm_PA hP0 hPz hPs
  have h3 : Summable fun k : Mode ↦ if k = 0 then 0 else P k / (t * absSq k * hm k) := by
    refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) (hPAs.div_const t)
    · split_ifs
      · exact le_rfl
      · have := absSq_nonneg k; have := mm_hm_nonneg k; have := hP0 k; positivity
    · split_ifs with hk
      · exact div_nonneg (hPAn k) htpos.le
      · have hA := one_le_absSq hk
        have hh := mm_one_le_hm hk
        rw [show P k / absSq k / t = P k / (t * absSq k) by ring]
        exact div_le_div_of_nonneg_left (hP0 k) (by positivity)
          (le_mul_of_one_le_right (by positivity) hh)
  have heq : ∀ k, (if k = 0 then 0 else P k / (t * absSq k)) * xiM a bL t k =
      P k / absSq k / t + a * P k +
        bL * (if k = 0 then 0 else P k / (t * absSq k * hm k)) := fun k ↦ by
    split_ifs with hk
    · simp [hk, hPz]
    · have hA : 0 < absSq k := lt_of_lt_of_le one_pos (one_le_absSq hk)
      have hh := mm_hm_pos hk
      unfold xiM
      field_simp
  simp_rw [heq]
  refine ⟨((hPAs.div_const t).add (hPs.mul_left a)).add (h3.mul_left bL), ?_⟩
  rw [((hPAs.div_const t).add (hPs.mul_left a)).tsum_add (h3.mul_left bL),
    (hPAs.div_const t).tsum_add (hPs.mul_left a), tsum_div_const, tsum_mul_left,
    tsum_mul_left, hP1, ← ht, div_self htpos.ne', mul_one]

end Sums

theorem Wpair_le_Vpair {t : ℝ} (ht : 0 < t) {p l : Mode} (hp : p ≠ 0) (hl : l ≠ 0) :
    Wpair t p l ≤ Vpair t p l := by
  have hA : 0 < absSq p := lt_of_lt_of_le one_pos (one_le_absSq hp)
  have hB : 0 < absSq l := lt_of_lt_of_le one_pos (one_le_absSq hl)
  have e : Vpair t p l - Wpair t p l =
      (absSq p - absSq l) ^ 2 / (2 * t * absSq p * absSq l * (absSq p + absSq l)) := by
    unfold Vpair Wpair; field_simp; ring
  have : 0 ≤ (absSq p - absSq l) ^ 2 / (2 * t * absSq p * absSq l * (absSq p + absSq l)) := by
    positivity
  linarith

theorem moment_master (P : Mode → ℝ) (hP0 : ∀ k, 0 ≤ P k) (hPz : P 0 = 0)
    (hPe : ∀ k, P (-k) = P k) (hPs : Summable P) (hP1 : ∑' k, P k = 1) {g : ℕ → ℝ}
    (hg0 : ∀ j, 0 ≤ g j) (hgM : ∀ j, g j ≤ M₀) {a bL lam K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ bL)
    (hlam : 0 ≤ lam) (hlamK : lam ≤ K) {t : ℝ} (ht : t = ∑' j : Mode, P j / absSq j)
    (hpt : ∀ p l : Mode, p ≠ 0 → l ≠ 0 → NonColl p l →
      Tpair g a bL t p l - lam * (Vpair t p l - 1) ≤ K) :
    (∑' k : Mode, Real.sqrt ((if k = 0 then 0 else P k / (t * absSq k)) * g (nsq k) *
      ∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0 then 0 else P p * P (k - p)))) ^ 2
      ≤ (1 + a + bL * ∑' k : Mode, (if k = 0 then 0 else P k / (t * absSq k * hm k))) * K := by
  obtain ⟨hPAn, -, hPAs⟩ := mm_PA hP0 hPz hPs
  have htpos : 0 < t := by
    obtain ⟨k, hk⟩ : ∃ k, P k ≠ 0 := by
      by_contra h; simp only [not_exists, not_not] at h; simp [h] at hP1
    have hk0 : k ≠ 0 := fun h ↦ hk (h ▸ hPz)
    have : 0 < P k / absSq k :=
      div_pos (lt_of_le_of_ne (hP0 k) (Ne.symm hk)) (by linarith [one_le_absSq hk0])
    rw [ht]; exact hPAs.tsum_pos hPAn k this
  obtain ⟨h1s, h1v⟩ := first_factor hP0 hPz hPs hP1 (a := a) (bL := bL) htpos ht
  obtain ⟨h2s, h2v⟩ := gR_sum hP0 hPs hg0 hgM ha hb htpos.le
  have hE := expect_le hP0 hPz hPs hP1 hg0 hgM ha hb hlam hlamK htpos ht hpt
  have hrefl := refl_eq hP0 hPe hPs hg0 hgM ha hb htpos.le
  have hQnn : ∀ k, 0 ≤ (if k = 0 then 0 else P k / (t * absSq k)) := fun k ↦ by
    split_ifs
    · exact le_rfl
    · have := absSq_nonneg k; have := hP0 k; positivity
  have hRnn : ∀ k, 0 ≤ g (nsq k) * ∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0
      then 0 else P p * P (k - p)) := fun k ↦
    mul_nonneg (hg0 _) (tsum_nonneg fun p ↦ by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hP0 _) (hP0 _))
  have hcs := mm_cs_weighted (fun k ↦ if k = 0 then 0 else P k / (t * absSq k))
    (fun k ↦ g (nsq k) * ∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0
      then 0 else P p * P (k - p)))
    (xiM a bL t) hQnn hRnn (fun k ↦ by linarith [mm_one_le_xi ha hb htpos.le k]) h1s h2s
  have hS0 : 0 ≤ ∑' k : Mode, (if k = 0 then 0 else P k / (t * absSq k * hm k)) :=
    tsum_nonneg fun k ↦ by
      split_ifs
      · exact le_rfl
      · have := absSq_nonneg k; have := mm_hm_nonneg k; have := hP0 k; positivity
  calc _ = (∑' k : Mode, Real.sqrt ((if k = 0 then 0 else P k / (t * absSq k)) * (g (nsq k) *
        ∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0 then 0
          else P p * P (k - p))))) ^ 2 := by
        congr 1; exact tsum_congr fun k ↦ by rw [mul_assoc]
    _ ≤ _ := hcs
    _ ≤ _ := by
        rw [h1v, h2v, hrefl]
        exact mul_le_mul_of_nonneg_left hE (by positivity)

-- `hw`, `hw0` are not needed: the identity holds for every field (`Z = 0` gives `0 = 0`).
set_option linter.unusedVariables false in
/-- `t = Y/Z = ∑ P_j/|j|²` for the dissipative law `P = Pk w`. -/
theorem tYZ_eq_tsum {w : Field} (hw : Adm 2 w) (hw0 : w ≠ 0) :
    tYZ w = ∑' j : Mode, Pk w j / absSq j := by
  have h : ∀ j, Pk w j / absSq j = hm j * ‖w j‖ ^ 2 / Zr w := fun j ↦ by
    by_cases hj : j = 0
    · simp [hj, mm_absSq_zero, mm_hm_zero]
    · have := (lt_of_lt_of_le one_pos (one_le_absSq hj)).ne'
      unfold Pk
      field_simp
  simp_rw [h]
  rw [tsum_div_const]
  rfl

/-- `X/Y = ∑_k Q_k/h_k`. -/
theorem XY_eq_tsum {w : Field} (hw : Adm 2 w) (hw0 : w ≠ 0) :
    Xr w / Yr w = ∑' k : Mode, (if k = 0 then 0 else Pk w k / (tYZ w * absSq k * hm k)) := by
  have hY := Yr_pos_of_ne hw hw0
  have hZ := Zr_pos_of_ne hw hw0
  have h : ∀ k, (if k = 0 then 0 else Pk w k / (tYZ w * absSq k * hm k)) =
      (if k = 0 then 0 else ‖w k‖ ^ 2) / Yr w := fun k ↦ by
    split_ifs with hk
    · simp
    · have hA : 0 < absSq k := lt_of_lt_of_le one_pos (one_le_absSq hk)
      have hh := mm_hm_pos hk
      unfold Pk tYZ
      field_simp
  simp_rw [h]
  rw [tsum_div_const]
  rfl

/-- The field-level moment bound. -/
theorem cubic_le_moment (hRB : RowBound gOVNS) {w : Field} (hw : Adm 2 w) (hw0 : w ≠ 0)
    {a bL lam K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ bL) (hlam : 0 ≤ lam) (hlamK : lam ≤ K)
    (hpt : PointwiseW gOVNS a bL (tYZ w) lam K) :
    |cubic w| ^ 2 ≤ (1 + a + bL * (Xr w / Yr w)) * K * Yr w * Zr w ^ 2 := by
  have hY := Yr_pos_of_ne hw hw0
  have hZ := Zr_pos_of_ne hw hw0
  have htpos : 0 < tYZ w := div_pos hY hZ
  have hc := cubic_le_rowchain gOVNS_nonneg gOVNS_le_M₀ hRB hw
  have hPs : Summable (Pk w) := (mm_summable_aw hw).div_const _
  have hP1 : ∑' k, Pk w k = 1 := by unfold Pk; rw [tsum_div_const]; exact div_self hZ.ne'
  have hM := moment_master (Pk w) (fun k ↦ div_nonneg (mm_aw_nonneg w k) hZ.le)
    (by simp [Pk, mm_absSq_zero])
    (fun k ↦ by simp only [Pk, absSq_neg, mm_hm_neg, hw.real k, norm_conjV])
    hPs hP1 gOVNS_nonneg gOVNS_le_M₀ ha hb hlam hlamK (tYZ_eq_tsum hw hw0)
    (fun p l hp hl hnc ↦ by
      have h1 := hpt p l hp hl hnc
      have h2 := mul_le_mul_of_nonneg_left (Wpair_le_Vpair htpos hp hl) hlam
      linarith)
  rw [← XY_eq_tsum hw hw0] at hM
  have hS : ∑' k, Real.sqrt (gOVNS (nsq k) * Qk w k * Rk w k) =
      ∑' k : Mode, Real.sqrt ((if k = 0 then 0 else Pk w k / (tYZ w * absSq k)) *
        gOVNS (nsq k) * ∑' p : Mode, (if cross (modeVec p) (modeVec (k - p)) = 0 then 0
          else Pk w p * Pk w (k - p))) :=
    tsum_congr fun k ↦ by rw [mul_comm (gOVNS (nsq k)) (Qk w k)]; rfl
  rw [hS] at hc
  rw [← hS] at hM hc
  have hS0 : 0 ≤ ∑' k, Real.sqrt (gOVNS (nsq k) * Qk w k * Rk w k) :=
    tsum_nonneg fun _ ↦ Real.sqrt_nonneg _
  have hc2 := pow_le_pow_left₀ (abs_nonneg _) hc 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hY.le] at hc2
  calc _ ≤ _ := hc2
    _ ≤ Yr w * Zr w ^ 2 * ((1 + a + bL * (Xr w / Yr w)) * K) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
    _ = _ := by ring

end Forced

end OVNS
