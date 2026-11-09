import OddViscousNS.Quant.Joint.Slow.Transport

/-!
# E7-P: the passive `H¹` and `H²` commutators, with `L^{2q}` control of the strain

Steps 6–8 of `Joint/Slow/Plan.lean`.  No Hölder at `p ≠ 2`, no interpolation of `‖∇v‖_{2p/(p−2)}`:
the level split `|A| ≤ Λ + |A|^q Λ^{1−q}` (`integral_split`) and Ladyzhenskaya for the rest.

* `StrainBd s q D`: the box truncations of `∂_i s_j`, `i, j ≠ 2`, have `‖·‖_{2q} ≤ D`, eventually.
* `abs_pairS_adv_le`: `|⟨s·∇c, Δc⟩| ≤ 2Λ ‖c‖₁² + 10 ‖c‖₁‖c‖₂`, if `D^q ≤ Λ^{q−1}`.
* `abs_pairS_two_adv_le`: the same at the next level, with the extra `∂s·∇c` term.
* the bridges to `pair` on fields, and the `sn` norms of `PiV`, `wC`.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.Slow

open GN

/-- `∑ |k|^{2j} Re(c̄_k d_k)`. -/
def pairS (j : ℕ) (c d : Mode → ℂ) : ℝ := ∑' k, absSq k ^ j * (conj (c k) * d k).re

/-- The `L^{2q}` control of the strain, on box truncations, for all large boxes. -/
def StrainBd (s : Field) (q : ℕ) (D : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ i j : Fin 3, i ≠ 2 → j ≠ 2 →
    mP q (Slow.D i (polyOf (slowBox (2 * N)) (GN.cmp s j))) ≤ D ^ (2 * q)

/-- The derivative of a field. -/
def dF (l : Fin 3) (s : Field) : Field := fun k => (Complex.I * (k l : ℂ)) • s k

/-- The pointwise split `t Λ^{q−1} ≤ Λ^q + t^q`. -/
private lemma level_pt {t Λ : ℝ} (ht : 0 ≤ t) (hΛ : 0 < Λ) {q : ℕ} (hq : 1 ≤ q) :
    t * Λ ^ (q - 1) ≤ Λ * Λ ^ (q - 1) + t ^ q := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases le_total t Λ with h | h
  · have h1 : t * Λ ^ m ≤ Λ * Λ ^ m := mul_le_mul_of_nonneg_right h (by positivity)
    have h2 : 0 ≤ t ^ (m + 1) := by positivity
    linarith
  · have h1 : Λ ^ m ≤ t ^ m := pow_le_pow_left₀ hΛ.le h m
    have h2 : t * Λ ^ m ≤ t ^ (m + 1) := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left h1 ht
    have h3 : 0 ≤ Λ * Λ ^ m := by positivity
    linarith

/-- **The level split.** -/
theorem integral_split {A g : Pol} {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D)
    (hA : mP q A ≤ D ^ (2 * q)) (hDΛ : D ^ q ≤ Λ ^ (q - 1)) :
    ∫ x, ‖ev A x‖ * ‖ev g x‖ ^ 2 ∂μT ≤ Λ * nn2 g + Real.sqrt (nn4 g) := by
  have hL : 0 < Λ ^ (q - 1) := by positivity
  set L := Λ ^ (q - 1) with hLdef
  have hi0 : Integrable (fun x => ‖ev A x‖ * ‖ev g x‖ ^ 2) μT :=
    integrable_of_continuous ((ev A).continuous.norm.mul ((ev g).continuous.norm.pow 2))
  have hi1 : Integrable (fun x => ‖ev A x‖ ^ q * ‖ev g x‖ ^ 2) μT :=
    integrable_of_continuous (((ev A).continuous.norm.pow q).mul ((ev g).continuous.norm.pow 2))
  have hi2 : Integrable (fun x => ‖ev g x‖ ^ 2) μT := integrable_norm_pow g 2
  have hpt : ∀ x, (‖ev A x‖ * ‖ev g x‖ ^ 2) * L ≤
      Λ * L * ‖ev g x‖ ^ 2 + ‖ev A x‖ ^ q * ‖ev g x‖ ^ 2 := fun x => by
    have h := level_pt (norm_nonneg (ev A x)) hΛ hq
    have h2 : 0 ≤ ‖ev g x‖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h h2]
  have hmono : ∫ x, (‖ev A x‖ * ‖ev g x‖ ^ 2) * L ∂μT ≤
      ∫ x, (Λ * L * ‖ev g x‖ ^ 2 + ‖ev A x‖ ^ q * ‖ev g x‖ ^ 2) ∂μT :=
    integral_mono (hi0.mul_const L) ((hi2.const_mul (Λ * L)).add hi1) hpt
  rw [integral_mul_const, integral_add (hi2.const_mul (Λ * L)) hi1, integral_const_mul] at hmono
  have hCS := integral_mul_le_sqrt (f := fun x => ‖ev A x‖ ^ q) (g := fun x => ‖ev g x‖ ^ 2)
    ((ev A).continuous.norm.pow q) ((ev g).continuous.norm.pow 2) (fun _ => by positivity)
    (fun _ => by positivity)
  have e1 : ∫ x, (‖ev A x‖ ^ q) ^ 2 ∂μT = mP q A :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  have e2 : ∫ x, (‖ev g x‖ ^ 2) ^ 2 ∂μT = nn4 g :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [e1, e2] at hCS
  have hsq : Real.sqrt (mP q A) ≤ D ^ q := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [← pow_mul]
    rwa [mul_comm q 2]
  have h3 : Real.sqrt (mP q A) * Real.sqrt (nn4 g) ≤ L * Real.sqrt (nn4 g) :=
    mul_le_mul_of_nonneg_right (hsq.trans hDΛ) (Real.sqrt_nonneg _)
  have h4 : (∫ x, ‖ev A x‖ * ‖ev g x‖ ^ 2 ∂μT) * L ≤ (Λ * nn2 g + Real.sqrt (nn4 g)) * L := by
    have : ∫ x, ‖ev g x‖ ^ 2 ∂μT = nn2 g := rfl
    rw [this] at hmono
    nlinarith
  exact le_of_mul_le_mul_right h4 hL

/-- The Cauchy inequality for square roots. -/
private lemma sqrt_cauchy {x0 x1 y0 y1 : ℝ} (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hy0 : 0 ≤ y0)
    (hy1 : 0 ≤ y1) :
    Real.sqrt x0 * Real.sqrt y0 + Real.sqrt x1 * Real.sqrt y1 ≤
      Real.sqrt (x0 + x1) * Real.sqrt (y0 + y1) := by
  rw [← Real.sqrt_mul (add_nonneg hx0 hx1)]
  refine Real.le_sqrt_of_sq_le ?_
  have a := Real.sq_sqrt hx0
  have b := Real.sq_sqrt hx1
  have c := Real.sq_sqrt hy0
  have d := Real.sq_sqrt hy1
  calc _ ≤ (Real.sqrt x0 ^ 2 + Real.sqrt x1 ^ 2) * (Real.sqrt y0 ^ 2 + Real.sqrt y1 ^ 2) := by
        nlinarith [sq_nonneg (Real.sqrt x0 * Real.sqrt y1 - Real.sqrt x1 * Real.sqrt y0)]
    _ = _ := by rw [a, b, c, d]

/-- `|∫ A g h| ≤ ½ ∫ |A| |g|² + ½ ∫ |A| |h|²`. -/
private lemma norm_mean_three_le (A g h : Pol) :
    ‖mean (A * g * h)‖ ≤
      (∫ x, ‖ev A x‖ * ‖ev g x‖ ^ 2 ∂μT) / 2 + (∫ x, ‖ev A x‖ * ‖ev h x‖ ^ 2 ∂μT) / 2 := by
  have hi : ∀ g : Pol, Integrable (fun x => ‖ev A x‖ * ‖ev g x‖ ^ 2) μT := fun g =>
    integrable_of_continuous ((ev A).continuous.norm.mul ((ev g).continuous.norm.pow 2))
  have hc : Continuous fun x => ‖ev A x‖ * ‖ev g x‖ ^ 2 / 2 + ‖ev A x‖ * ‖ev h x‖ ^ 2 / 2 :=
    (((ev A).continuous.norm.mul ((ev g).continuous.norm.pow 2)).div_const 2).add
      (((ev A).continuous.norm.mul ((ev h).continuous.norm.pow 2)).div_const 2)
  rw [← J_ev]
  refine (norm_J_le hc fun x => ?_).trans (le_of_eq ?_)
  · simp only [map_mul, ContinuousMap.mul_apply, norm_mul]
    nlinarith [mul_nonneg (norm_nonneg (ev A x)) (sq_nonneg (‖ev g x‖ - ‖ev h x‖))]
  · rw [integral_add ((hi g).div_const 2) ((hi h).div_const 2), integral_div, integral_div]

/-- Slow polynomials have no vertical derivative. -/
private lemma D_two_eq_zero {P : Pol} (hs : IsSlowP P) : Slow.D 2 P = 0 := by
  ext k
  by_cases h : P.coeff k = 0
  · simp [Slow.D, h]
  · simp [Slow.D, dSym, hs k h]

/-- Ladyzhenskaya, under the root. -/
private lemma sqrt_nn4_le {G : Pol} (hs : IsSlowP G) (h0 : mean G = 0) :
    Real.sqrt (nn4 G) ≤ 5 * Real.sqrt (nn2 G) * Real.sqrt (grad2 G) := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h := lady_zero hs h0
  rw [mul_pow, mul_pow, Real.sq_sqrt (nn2_nonneg G), Real.sq_sqrt (grad2_nonneg G)]
  linarith

/-- The two horizontal derivatives, by Ladyzhenskaya and Cauchy. -/
private lemma two_levels_le {P : Pol} (hs : IsSlowP P) {Λ : ℝ} (hΛ : 0 < Λ) :
    2 * (Λ * nn2 (Slow.D 0 P) + Real.sqrt (nn4 (Slow.D 0 P))) +
      2 * (Λ * nn2 (Slow.D 1 P) + Real.sqrt (nn4 (Slow.D 1 P))) ≤
      2 * Λ * grad2 P + 10 * Real.sqrt (grad2 P) * Real.sqrt (∑ i, grad2 (Slow.D i P)) := by
  have hx0 := nn2_nonneg (Slow.D 0 P)
  have hx1 := nn2_nonneg (Slow.D 1 P)
  have hy0 := grad2_nonneg (Slow.D 0 P)
  have hy1 := grad2_nonneg (Slow.D 1 P)
  have hG : nn2 (Slow.D 0 P) + nn2 (Slow.D 1 P) ≤ grad2 P := by
    simp only [grad2, Fin.sum_univ_three]
    linarith [nn2_nonneg (Slow.D 2 P)]
  have hY : grad2 (Slow.D 0 P) + grad2 (Slow.D 1 P) ≤ ∑ i, grad2 (Slow.D i P) := by
    simp only [Fin.sum_univ_three]
    linarith [grad2_nonneg (Slow.D 2 P)]
  have hC := sqrt_cauchy hx0 hx1 hy0 hy1
  have hC2 : Real.sqrt (nn2 (Slow.D 0 P) + nn2 (Slow.D 1 P)) *
      Real.sqrt (grad2 (Slow.D 0 P) + grad2 (Slow.D 1 P)) ≤
      Real.sqrt (grad2 P) * Real.sqrt (∑ i, grad2 (Slow.D i P)) :=
    mul_le_mul (Real.sqrt_le_sqrt hG) (Real.sqrt_le_sqrt hY) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have h40 := sqrt_nn4_le (hs.D 0) (mean_D 0 P)
  have h41 := sqrt_nn4_le (hs.D 1) (mean_D 1 P)
  nlinarith [mul_le_mul_of_nonneg_left hG hΛ.le]

/-- The polynomial `H¹` commutator. -/
theorem abs_mean_trans_lap_le {U : Fin 3 → Pol} {P : Pol} (hU : DivFree U) (hR : RealC P)
    (hs : IsSlowP P) {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D)
    (hstr : ∀ i j : Fin 3, i ≠ 2 → j ≠ 2 → mP q (Slow.D i (U j)) ≤ D ^ (2 * q))
    (hDΛ : D ^ q ≤ Λ ^ (q - 1)) :
    ‖mean (trans U P * lap P)‖ ≤
      2 * Λ * grad2 P + 10 * Real.sqrt (grad2 P) * Real.sqrt (∑ i, grad2 (Slow.D i P)) := by
  have _ := hR
  have hZ : Slow.D 2 P = 0 := D_two_eq_zero hs
  have hm0 : mean (0 : Pol) = 0 := rfl
  set S : Pol → ℝ := fun g => Λ * nn2 g + Real.sqrt (nn4 g) with hS
  have hT : ∀ i j : Fin 3, i ≠ 2 → j ≠ 2 → ‖mean (Slow.D i (U j) * Slow.D j P * Slow.D i P)‖ ≤
      (S (Slow.D j P) + S (Slow.D i P)) / 2 := fun i j hi hj => by
    have h1 := norm_mean_three_le (Slow.D i (U j)) (Slow.D j P) (Slow.D i P)
    have h2 := integral_split (g := Slow.D j P) hq hΛ hD (hstr i j hi hj) hDΛ
    have h3 := integral_split (g := Slow.D i P) hq hΛ hD (hstr i j hi hj) hDΛ
    simp only [hS]
    linarith
  have h01 : (0 : Fin 3) ≠ 2 := by decide
  have h11 : (1 : Fin 3) ≠ 2 := by decide
  have h00 := hT 0 0 h01 h01
  have h0' := hT 0 1 h01 h11
  have h1' := hT 1 0 h11 h01
  have h1'' := hT 1 1 h11 h11
  rw [mean_trans_lap hU, norm_neg]
  have hsum : ∑ i, ∑ j, mean (Slow.D i (U j) * Slow.D j P * Slow.D i P) =
      mean (Slow.D 0 (U 0) * Slow.D 0 P * Slow.D 0 P) +
      mean (Slow.D 0 (U 1) * Slow.D 1 P * Slow.D 0 P) +
      (mean (Slow.D 1 (U 0) * Slow.D 0 P * Slow.D 1 P) +
        mean (Slow.D 1 (U 1) * Slow.D 1 P * Slow.D 1 P)) := by
    simp only [Fin.sum_univ_three, hZ, mul_zero, zero_mul, hm0, add_zero]
  rw [hsum]
  have hn : ‖mean (Slow.D 0 (U 0) * Slow.D 0 P * Slow.D 0 P) +
      mean (Slow.D 0 (U 1) * Slow.D 1 P * Slow.D 0 P) +
      (mean (Slow.D 1 (U 0) * Slow.D 0 P * Slow.D 1 P) +
        mean (Slow.D 1 (U 1) * Slow.D 1 P * Slow.D 1 P))‖ ≤
      2 * S (Slow.D 0 P) + 2 * S (Slow.D 1 P) := by
    refine (norm_add_le _ _).trans ?_
    have h5 := norm_add_le (mean (Slow.D 0 (U 0) * Slow.D 0 P * Slow.D 0 P))
      (mean (Slow.D 0 (U 1) * Slow.D 1 P * Slow.D 0 P))
    have h6 := norm_add_le (mean (Slow.D 1 (U 0) * Slow.D 0 P * Slow.D 1 P))
      (mean (Slow.D 1 (U 1) * Slow.D 1 P * Slow.D 1 P))
    linarith
  exact hn.trans (two_levels_le hs hΛ)

/-! ### Box truncations of a real slow sequence -/

private lemma realC_polyOf {N : ℕ} {c : Mode → ℂ} (hcR : ∀ k, c (-k) = conj (c k)) :
    RealC (polyOf (slowBox N) c) := fun k => by
  rw [coeff_polyOf, coeff_polyOf]
  exact tr_neg_conj (fun _ => neg_mem_slowBox) hcR k

private lemma divFree_polyOf {s : Field} (hs : IsSolenoidal s) (A : Finset Mode) :
    DivFree (fun i => polyOf A (GN.cmp s i)) := by
  ext k
  simp only [Slow.D, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    coeff_mult, coeff_polyOf, tr, dSym, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply]
  split_ifs with hk
  · have h1 := hs k
    simp only [dotM] at h1
    have e : ∀ i, Complex.I * (k i : ℂ) * GN.cmp s i k =
        Complex.I * ((s k) i * (k i : ℂ)) := fun i => by
      change Complex.I * (k i : ℂ) * (s k) i = _
      ring
    simp only [e, ← Finset.mul_sum, h1, mul_zero]
  · simp

private lemma mean_polyOf_mul (A : Finset Mode) (a b : Mode → ℂ) :
    mean (polyOf A a * polyOf A b) = ∑ p ∈ A, a p * tr A b (-p) := by
  have e : mean (polyOf A a * polyOf A b) =
      mFourierCoeff (ev (polyOf A a * polyOf A b) : C(T3, ℂ)) 0 := (coeff_ev _ 0).symm
  rw [e, map_mul, ev_polyOf, ev_polyOf, coeff_tp_mul, cv,
    tsum_eq_sum (s := A) fun p hp => by simp [tr, hp]]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp [tr, hp]

private lemma mean_polyOf_mul_lap {N : ℕ} {c : Mode → ℂ} (hcR : ∀ k, c (-k) = conj (c k))
    (d : Mode → ℂ) :
    mean (polyOf (slowBox N) d * lap (polyOf (slowBox N) c)) =
      -∑ k ∈ slowBox N, (absSq k : ℂ) * (conj (c k) * d k) := by
  rw [lap_polyOf, mean_polyOf_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [tr, neg_mem_slowBox hp, ite_true, hcR, absSq_neg']
  ring

private lemma sq_norm_tr_le (A : Finset Mode) (a : Mode → ℂ) (k : Mode) :
    ‖tr A a k‖ ^ 2 ≤ ‖a k‖ ^ 2 := by
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  simp only [tr]
  split_ifs <;> simp

private lemma nn2_lap_polyOf_le {A : Finset Mode} {c : Mode → ℂ}
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2) : nn2 (lap (polyOf A c)) ≤ sn 2 c := by
  refine hasSum_le (fun k => ?_) (hasSum_nn2 _) hc2.hasSum
  simp only [lap, coeff_mult, coeff_polyOf, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  exact mul_le_mul_of_nonneg_left (sq_norm_tr_le A c k) (by positivity)

private lemma grad2_polyOf_le {A : Finset Mode} {c : Mode → ℂ}
    (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2) : grad2 (polyOf A c) ≤ sn 1 c := by
  refine hasSum_le (fun k => ?_) (hasSum_grad2 _) hc1.hasSum
  rw [pow_one, coeff_polyOf]
  exact mul_le_mul_of_nonneg_left (sq_norm_tr_le A c k) (absSq_nonneg k)

/-- `∑_i ‖∇∂_i P‖₂² = ‖ΔP‖₂²`, on coefficients. -/
private lemma hasSum_grad2_D (P : Pol) :
    HasSum (fun k => absSq k ^ 2 * ‖P.coeff k‖ ^ 2) (∑ i, grad2 (Slow.D i P)) := by
  have h : HasSum (fun k => ∑ i : Fin 3, absSq k * ‖(Slow.D i P).coeff k‖ ^ 2)
      (∑ i, grad2 (Slow.D i P)) := hasSum_sum fun i _ => hasSum_grad2 (Slow.D i P)
  have e : (fun k => ∑ i : Fin 3, absSq k * ‖(Slow.D i P).coeff k‖ ^ 2) =
      fun k => absSq k ^ 2 * ‖P.coeff k‖ ^ 2 := by
    funext k
    simp only [Slow.D, coeff_mult, norm_mul, dSym, Complex.norm_I, one_mul, mul_pow,
      Complex.norm_intCast, sq_abs, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [sq (absSq k), mul_assoc]
    rfl
  rwa [e] at h

private lemma sum_grad2_D_polyOf_le {A : Finset Mode} {c : Mode → ℂ}
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2) :
    ∑ i, grad2 (Slow.D i (polyOf A c)) ≤ sn 2 c := by
  refine hasSum_le (fun k => ?_) (hasSum_grad2_D _) hc2.hasSum
  rw [coeff_polyOf]
  exact mul_le_mul_of_nonneg_left (sq_norm_tr_le A c k) (by positivity)

/-- The polynomial commutator, seen on the coefficients of `c` and `s·∇c`. -/
private lemma norm_sum_box_le {s : Field} {c : Mode → ℂ} (hs : IsSolenoidal s)
    (hcR : ∀ k, c (-k) = conj (c k)) (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2) {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ)
    (hD : 0 ≤ D) (hDΛ : D ^ q ≤ Λ ^ (q - 1)) (N : ℕ)
    (hstr : ∀ i j : Fin 3, i ≠ 2 → j ≠ 2 →
      mP q (Slow.D i (polyOf (slowBox N) (GN.cmp s j))) ≤ D ^ (2 * q)) :
    ‖∑ k ∈ slowBox N, (absSq k : ℂ) * (conj (c k) * advC s c k)‖ ≤
      2 * Λ * sn 1 c + 10 * Real.sqrt (sn 1 c) * Real.sqrt (sn 2 c) +
        Real.sqrt (nn2 (errP (slowBox N) s c)) * Real.sqrt (sn 2 c) := by
  set A := slowBox N with hA
  set P := polyOf A c with hP
  set U : Fin 3 → Pol := fun i => polyOf A (GN.cmp s i) with hU
  have h1 := abs_mean_trans_lap_le (U := U) (P := P) (divFree_polyOf hs A) (realC_polyOf hcR)
    (isSlowP_polyOf (fun k hk => (mem_slowBox.1 hk).1) c) hq hΛ hD hstr hDΛ
  have e : trans U P = polyOf A (advC s c) + errP A s c := by
    simp only [errP, hU, hP]
    ring
  have e2 : mean (trans U P * lap P) = -(∑ k ∈ A, (absSq k : ℂ) * (conj (c k) * advC s c k)) +
      mean (errP A s c * lap P) := by
    rw [e, add_mul, mean_add, hA, mean_polyOf_mul_lap hcR]
  have h3 : ‖mean (errP A s c * lap P)‖ ≤
      Real.sqrt (nn2 (errP A s c)) * Real.sqrt (sn 2 c) :=
    (norm_mean_mul_le _ _).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (nn2_lap_polyOf_le hc2)) (Real.sqrt_nonneg _))
  have h4 : grad2 P ≤ sn 1 c := grad2_polyOf_le hc1
  have h5 : ∑ i, grad2 (Slow.D i P) ≤ sn 2 c := sum_grad2_D_polyOf_le hc2
  have h6 : 2 * Λ * grad2 P + 10 * Real.sqrt (grad2 P) * Real.sqrt (∑ i, grad2 (Slow.D i P)) ≤
      2 * Λ * sn 1 c + 10 * Real.sqrt (sn 1 c) * Real.sqrt (sn 2 c) := by
    have h7 := mul_le_mul (Real.sqrt_le_sqrt h4) (Real.sqrt_le_sqrt h5) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left h4 hΛ.le]
  have h8 : ∑ k ∈ A, (absSq k : ℂ) * (conj (c k) * advC s c k) =
      -mean (trans U P * lap P) + mean (errP A s c * lap P) := by
    rw [e2]
    ring
  rw [h8]
  have h9 := norm_add_le (-mean (trans U P * lap P)) (mean (errP A s c * lap P))
  rw [norm_neg] at h9
  linarith

/-! ### Passing to the limit -/

/-- The series of a slow summable sequence is the limit of the slow boxes. -/
private lemma tendsto_sum_slowBox {φ : Mode → ℂ} (hφ : Summable φ)
    (hs : ∀ k, k 2 ≠ 0 → φ k = 0) :
    Tendsto (fun N : ℕ => ∑ k ∈ slowBox N, φ k) atTop (𝓝 (∑' k, φ k)) := by
  set B : ℕ → Finset Mode := fun N => Finset.Icc (fun _ => -(N : ℤ)) (fun _ => (N : ℤ)) with hB
  have hmono : Monotone B := fun m n h => Finset.Icc_subset_Icc
    (fun i => by simpa using h) (fun i => by simpa using h)
  have hex : ∀ k, ∃ N, k ∈ B N := fun k => by
    refine ⟨∑ i, (k i).natAbs, ?_⟩
    have h : ∀ i, |k i| ≤ ((∑ i, (k i).natAbs : ℕ) : ℤ) := fun i => by
      have h1 : (k i).natAbs ≤ ∑ i, (k i).natAbs :=
        Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1
    simp only [hB, Finset.mem_Icc, Pi.le_def]
    exact ⟨fun i => (abs_le.1 (h i)).1, fun i => (abs_le.1 (h i)).2⟩
  have h1 := hφ.hasSum.comp (tendsto_atTop_finset_of_monotone hmono hex)
  refine h1.congr fun N => ?_
  have hsub : slowBox N ⊆ B N := fun k hk => by
    obtain ⟨h2, h0, h1⟩ := mem_slowBox.1 hk
    simp only [hB, Finset.mem_Icc, Pi.le_def]
    constructor <;> intro i <;> fin_cases i <;> simp [h2, (abs_le.1 h0).1, (abs_le.1 h0).2,
      (abs_le.1 h1).1, (abs_le.1 h1).2]
  refine (Finset.sum_subset hsub fun k hk hk' => hs k fun h2 => hk' ?_).symm
  simp only [hB, Finset.mem_Icc, Pi.le_def] at hk
  exact mem_slowBox.2 ⟨h2, abs_le.2 ⟨hk.1 0, hk.2 0⟩, abs_le.2 ⟨hk.1 1, hk.2 1⟩⟩

private lemma summable_cv_sq {a b : Mode → ℂ} (ha : Summable fun k => ‖a k‖)
    (hb : Summable fun k => ‖b k‖ ^ 2) : Summable fun k => ‖cv a b k‖ ^ 2 := by
  have h := young_l1_l2 (a := fun k => ‖a k‖) (b := fun k => ‖b k‖) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) ha hb
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun k => pow_le_pow_left₀ (norm_nonneg _) (norm_cv_le (h.1 k)) 2) h.2.1

private lemma summable_sum_sq {f : Fin 3 → Mode → ℂ} (hf : ∀ i, Summable fun k => ‖f i k‖ ^ 2) :
    Summable fun k => ‖∑ i, f i k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
    ((summable_sum fun i (_ : i ∈ Finset.univ) => hf i).mul_left 3)
  have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
    (f := fun i => ‖f i k‖)
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at h1
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans h1

private lemma summable_dC_sq' (i : Fin 3) {c : Mode → ℂ}
    (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2) : Summable fun k => ‖dC i c k‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun k => (norm_dC_sq_le i c k).trans (le_of_eq (by simp))) hc1

/-- The transport of an `H¹` sequence by an `H²` field is in `ℓ²`. -/
private lemma summable_advC_sq {s : Field} {c : Mode → ℂ} (hs : InH 2 s)
    (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2) : Summable fun k => ‖advC s c k‖ ^ 2 :=
  summable_sum_sq fun i => summable_cv_sq
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_cmp_le s i k)
      (summable_wiener hs)) (summable_dC_sq' i hc1)

/-- The pairing series converges. -/
private lemma summable_pair_term {a b : Mode → ℂ}
    (ha : Summable fun k => absSq k ^ 2 * ‖a k‖ ^ 2) (hb : Summable fun k => ‖b k‖ ^ 2) :
    Summable fun k => (absSq k : ℂ) * (conj (a k) * b k) := by
  refine Summable.of_norm_bounded (ha.add hb) fun k => ?_
  simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (absSq_nonneg k)]
  nlinarith [sq_nonneg (absSq k * ‖a k‖ - ‖b k‖), mul_nonneg (absSq_nonneg k) (norm_nonneg (a k)),
    norm_nonneg (b k)]

/-- `pairS 1` as the real part of a complex series. -/
private lemma pairS_one_eq {a b : Mode → ℂ}
    (ha : Summable fun k => absSq k ^ 2 * ‖a k‖ ^ 2) (hb : Summable fun k => ‖b k‖ ^ 2) :
    pairS 1 a b = (∑' k, (absSq k : ℂ) * (conj (a k) * b k)).re := by
  rw [Complex.re_tsum (summable_pair_term ha hb), pairS]
  refine tsum_congr fun k => ?_
  rw [pow_one, Complex.re_ofReal_mul]

/-- The commutator of the truncation vanishes in the limit. -/
private lemma tendsto_sqrt_nn2_errP {s : Field} {c : Mode → ℂ} (hs : Adm 2 s) (hs3 : InH 3 s)
    (hsl : PiS s = s) (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2) (hcs : ∀ k, k 2 ≠ 0 → c k = 0) :
    Tendsto (fun N : ℕ => Real.sqrt (nn2 (errP (slowBox (2 * N)) s c))) atTop (𝓝 0) := by
  set C := 18 * c4 ^ 2 * (hnorm 3 s ^ 2 * sn 1 c + hnorm 2 s ^ 2 * sn 2 c) with hC
  have hb : ∀ᶠ N : ℕ in atTop, Real.sqrt (nn2 (errP (slowBox (2 * N)) s c)) ≤
      Real.sqrt C / N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have h := nn2_errP_le hN ⟨hs3, hs.mean⟩ hs.mz (fun k hk => slow_zero' hsl hk) hc1 hc2 hcs
    have e : 18 * c4 ^ 2 / (N : ℝ) ^ 2 * (hnorm 3 s ^ 2 * sn 1 c + hnorm 2 s ^ 2 * sn 2 c) =
        C / N ^ 2 := by
      rw [hC]
      ring
    rw [e] at h
    refine (Real.sqrt_le_sqrt h).trans (le_of_eq ?_)
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hN0.le]
  refine squeeze_zero' (Eventually.of_forall fun _ => Real.sqrt_nonneg _) hb ?_
  exact tendsto_const_div_atTop_nhds_zero_nat _

/-- **The passive `H¹` commutator**, at a fixed time. -/
theorem abs_pairS_adv_le {s : Field} {c : Mode → ℂ} (hs : Adm 2 s) (hs3 : InH 3 s)
    (hsl : PiS s = s) (hcR : ∀ k, c (-k) = conj (c k)) (hcs : ∀ k, k 2 ≠ 0 → c k = 0)
    (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2)
    {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D) (hstr : StrainBd s q D)
    (hDΛ : D ^ q ≤ Λ ^ (q - 1)) :
    |pairS 1 c (advC s c)| ≤ 2 * Λ * sn 1 c + 10 * Real.sqrt (sn 1 c) * Real.sqrt (sn 2 c) := by
  set φ : Mode → ℂ := fun k => (absSq k : ℂ) * (conj (c k) * advC s c k) with hφ
  have hd := summable_advC_sq hs.inH hc1
  have hsum : Summable φ := summable_pair_term hc2 hd
  have hslow : ∀ k, k 2 ≠ 0 → φ k = 0 := fun k hk => by simp [hφ, hcs k hk]
  have hT1 := (tendsto_sum_slowBox hsum hslow).comp (tendsto_id.const_mul_atTop' two_pos :
    Tendsto (fun N : ℕ => 2 * id N) atTop atTop)
  have hT2 : Tendsto (fun N : ℕ => ‖∑ k ∈ slowBox (2 * N), φ k‖) atTop (𝓝 ‖∑' k, φ k‖) :=
    hT1.norm
  set R := 2 * Λ * sn 1 c + 10 * Real.sqrt (sn 1 c) * Real.sqrt (sn 2 c) with hR
  have hE := tendsto_sqrt_nn2_errP hs hs3 hsl hc1 hc2 hcs
  have hT3 : Tendsto (fun N : ℕ => R + Real.sqrt (nn2 (errP (slowBox (2 * N)) s c)) *
      Real.sqrt (sn 2 c)) atTop (𝓝 R) := by
    simpa using tendsto_const_nhds.add (hE.mul_const (Real.sqrt (sn 2 c)))
  have hle : ‖∑' k, φ k‖ ≤ R := le_of_tendsto_of_tendsto hT2 hT3 (by
    filter_upwards [hstr] with N hN
    exact norm_sum_box_le hs.sol hcR hc1 hc2 hq hΛ hD hDΛ (2 * N) hN)
  rw [pairS_one_eq hc2 hd]
  exact (Complex.abs_re_le_norm _).trans hle

/-! ### Fatou along the boxes -/

/-- A slow mode is eventually in the boxes. -/
private lemma eventually_mem_box {k : Mode} (hk : k 2 = 0) :
    ∀ᶠ N : ℕ in atTop, k ∈ slowBox (2 * N) := by
  filter_upwards [eventually_ge_atTop ((k 0).natAbs + (k 1).natAbs)] with N hN
  refine mem_slowBox.2 ⟨hk, ?_, ?_⟩ <;> rw [Int.abs_eq_natAbs] <;> omega

private lemma eventually_tr_eq {a : Mode → ℂ} (ha : ∀ k, k 2 ≠ 0 → a k = 0) (p : Mode) :
    ∀ᶠ N : ℕ in atTop, tr (slowBox (2 * N)) a p = a p := by
  by_cases hp : p 2 = 0
  · filter_upwards [eventually_mem_box hp] with N hN
    simp [tr, hN]
  · exact Eventually.of_forall fun N => by simp [tr, ha p hp]

/-- **Fatou along the boxes**: `GN.cv_fatou`, for slow sequences and a bound on large boxes. -/
private lemma cv_fatou_box {a b : Mode → ℂ} {B : ℝ}
    (hab : ∀ m, Summable fun p => ‖a p‖ * ‖b (m - p)‖)
    (has : ∀ k, k 2 ≠ 0 → a k = 0) (hbs : ∀ k, k 2 ≠ 0 → b k = 0)
    (hle : ∀ᶠ N : ℕ in atTop,
      ∫ x, ‖tp (slowBox (2 * N)) a x‖ ^ 2 * ‖tp (slowBox (2 * N)) b x‖ ^ 2 ∂μT ≤ B) :
    Summable (fun m => ‖cv a b m‖ ^ 2) ∧ ∑' m, ‖cv a b m‖ ^ 2 ≤ B := by
  have hpt : ∀ m, Tendsto (fun N : ℕ => cv (tr (slowBox (2 * N)) a) (tr (slowBox (2 * N)) b) m)
      atTop (𝓝 (cv a b m)) := by
    intro m
    refine tendsto_tsum_of_dominated_convergence (hab m) (fun p => ?_) (Eventually.of_forall ?_)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_tr_eq has p, eventually_tr_eq hbs (m - p)] with N h1 h2
      rw [h1, h2]
    · intro N p
      rw [norm_mul]
      refine mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _)
      · simp only [tr]
        split_ifs <;> simp
      · simp only [tr]
        split_ifs <;> simp
  have key : ∀ K : Finset Mode, ∑ m ∈ K, ‖cv a b m‖ ^ 2 ≤ B := fun K => by
    have h1 : Tendsto (fun N : ℕ =>
        ∑ m ∈ K, ‖cv (tr (slowBox (2 * N)) a) (tr (slowBox (2 * N)) b) m‖ ^ 2) atTop
        (𝓝 (∑ m ∈ K, ‖cv a b m‖ ^ 2)) :=
      tendsto_finsetSum _ fun m _ => ((hpt m).norm).pow 2
    refine le_of_tendsto h1 ?_
    filter_upwards [hle] with N hN
    exact (sum_le_hasSum K (fun m _ => by positivity) (hasSum_cv _ _ a b)).trans hN
  have h0 : 0 ≤ fun m => ‖cv a b m‖ ^ 2 := fun m => by positivity
  exact ⟨summable_of_sum_le h0 key, Real.tsum_le_of_sum_le h0 key⟩

/-- The level split for `A²`, at the exponent `4q`. -/
private lemma integral_split_sq {A g : Pol} {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ)
    (hD : 0 ≤ D) (hA : mP (2 * q) A ≤ D ^ (2 * (2 * q))) (hDΛ : D ^ q ≤ Λ ^ (q - 1)) :
    ∫ x, ‖ev A x‖ ^ 2 * ‖ev g x‖ ^ 2 ∂μT ≤ Λ ^ 2 * nn2 g + Real.sqrt (nn4 g) := by
  have h1 : mP q (A ^ 2) ≤ (D ^ 2) ^ (2 * q) := by
    have e : mP q (A ^ 2) = mP (2 * q) A := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [map_pow, ContinuousMap.coe_pow, Pi.pow_apply, norm_pow]
      ring
    rw [e, ← pow_mul]
    exact hA
  have h2 : (D ^ 2) ^ q ≤ (Λ ^ 2) ^ (q - 1) := by
    rw [pow_right_comm, pow_right_comm Λ]
    exact pow_le_pow_left₀ (by positivity) hDΛ 2
  have h3 := integral_split (A := A ^ 2) (g := g) hq (by positivity) (by positivity) h1 h2
  refine le_trans (le_of_eq ?_) h3
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_pow, ContinuousMap.coe_pow, Pi.pow_apply, norm_pow]

private lemma dC_slow {c : Mode → ℂ} (hcs : ∀ k, k 2 ≠ 0 → c k = 0) (l : Fin 3) (k : Mode)
    (hk : k 2 ≠ 0) : dC l c k = 0 := by
  simp [dC, hcs k hk]

/-- One term of the strain against the gradient. -/
private lemma tsum_cv_sq_le {s : Field} {c : Mode → ℂ} (hs : Adm 2 s) (hsl : PiS s = s)
    (hcs : ∀ k, k 2 ≠ 0 → c k = 0) (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2)
    {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D) (hstr : StrainBd s (2 * q) D)
    (hDΛ : D ^ q ≤ Λ ^ (q - 1)) {l i : Fin 3} (hl : l ≠ 2) (hi : i ≠ 2) :
    Summable (fun m => ‖cv (dC l (GN.cmp s i)) (dC i c) m‖ ^ 2) ∧
      ∑' m, ‖cv (dC l (GN.cmp s i)) (dC i c) m‖ ^ 2 ≤
        Λ ^ 2 * sn 1 c + 5 * Real.sqrt (sn 1 c) * Real.sqrt (sn 2 c) := by
  have ha : Summable fun k => ‖dC l (GN.cmp s i) k‖ ^ 2 :=
    summable_dC_sq (hs.inH.mono (by norm_num)) l i
  refine cv_fatou_box (summable_mul_of_l2 ha (summable_dC_sq' i hc1))
    (dC_slow (cmp_slow hsl i) l) (dC_slow hcs i) ?_
  filter_upwards [hstr] with N hN
  set A := slowBox (2 * N) with hA
  set P := polyOf A c with hP
  have e1 : tp A (dC l (GN.cmp s i)) = ev (Slow.D l (polyOf A (GN.cmp s i))) := by
    rw [← ev_polyOf]
    exact (congrArg ev (mult_polyOf _ _ _)).symm
  have e2 : tp A (dC i c) = ev (Slow.D i P) := by
    rw [← ev_polyOf]
    exact (congrArg ev (mult_polyOf _ _ _)).symm
  rw [e1, e2]
  refine (integral_split_sq hq hΛ hD (hN l i hl hi) hDΛ).trans ?_
  have hP1 : IsSlowP P := isSlowP_polyOf (fun _ hk => (mem_slowBox.1 hk).1) c
  have h1 : nn2 (Slow.D i P) ≤ sn 1 c := by
    refine le_trans ?_ (grad2_polyOf_le (A := A) hc1)
    exact Finset.single_le_sum (f := fun i => nn2 (Slow.D i P)) (fun _ _ => nn2_nonneg _)
      (Finset.mem_univ i)
  have h2 : grad2 (Slow.D i P) ≤ sn 2 c := by
    refine le_trans ?_ (sum_grad2_D_polyOf_le (A := A) hc2)
    exact Finset.single_le_sum (f := fun i => grad2 (Slow.D i P)) (fun _ _ => grad2_nonneg _)
      (Finset.mem_univ i)
  have h3 := sqrt_nn4_le (hP1.D i) (mean_D i P)
  have h4 := mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ Λ ^ 2)]

private lemma cmp_dF (l i : Fin 3) (s : Field) : GN.cmp (dF l s) i = dC l (GN.cmp s i) := by
  funext k
  simp [GN.cmp, dF, dC]

private lemma dC_two_eq_zero {c : Mode → ℂ} (hcs : ∀ k, k 2 ≠ 0 → c k = 0) :
    dC 2 c = fun _ => 0 := by
  funext k
  by_cases hk : k 2 = 0
  · simp [dC, hk]
  · simp [dC, hcs k hk]

/-- The transport by `∂_l s` of a slow sequence, on its two terms. -/
private lemma advC_dF_eq {s : Field} {c : Mode → ℂ} (hcs : ∀ k, k 2 ≠ 0 → c k = 0) (l : Fin 3)
    (m : Mode) :
    advC (dF l s) c m =
      cv (dC l (GN.cmp s 0)) (dC 0 c) m + cv (dC l (GN.cmp s 1)) (dC 1 c) m := by
  simp [advC, Fin.sum_univ_three, cmp_dF, dC_two_eq_zero hcs, cv]

/-- **The strain against the gradient in `L²`**: `‖∂_l s·∇c‖₂² ≤ 4(Λ² ‖c‖₁² + 5 ‖c‖₁‖c‖₂)`. -/
theorem sn_zero_advC_dF_le {s : Field} {c : Mode → ℂ} (hs : Adm 2 s) (hs3 : InH 3 s)
    (hsl : PiS s = s) (hcR : ∀ k, c (-k) = conj (c k)) (hcs : ∀ k, k 2 ≠ 0 → c k = 0)
    (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2)
    {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D) (hstr : StrainBd s (2 * q) D)
    (hDΛ : D ^ q ≤ Λ ^ (q - 1)) {l : Fin 3} (hl : l ≠ 2) :
    (Summable fun k => ‖advC (dF l s) c k‖ ^ 2) ∧
      sn 0 (advC (dF l s) c) ≤
        4 * (Λ ^ 2 * sn 1 c + 5 * Real.sqrt (sn 1 c) * Real.sqrt (sn 2 c)) := by
  have _ := hcR
  have _ := hs3
  obtain ⟨h0s, h0t⟩ := tsum_cv_sq_le hs hsl hcs hc1 hc2 hq hΛ hD hstr hDΛ hl
    (by decide : (0 : Fin 3) ≠ 2)
  obtain ⟨h1s, h1t⟩ := tsum_cv_sq_le hs hsl hcs hc1 hc2 hq hΛ hD hstr hDΛ hl
    (by decide : (1 : Fin 3) ≠ 2)
  have hle : ∀ m, ‖advC (dF l s) c m‖ ^ 2 ≤ 2 * (‖cv (dC l (GN.cmp s 0)) (dC 0 c) m‖ ^ 2 +
      ‖cv (dC l (GN.cmp s 1)) (dC 1 c) m‖ ^ 2) := fun m => by
    rw [advC_dF_eq hcs]
    have h := norm_add_le (cv (dC l (GN.cmp s 0)) (dC 0 c) m) (cv (dC l (GN.cmp s 1)) (dC 1 c) m)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖cv (dC l (GN.cmp s 0)) (dC 0 c) m‖ -
      ‖cv (dC l (GN.cmp s 1)) (dC 1 c) m‖)]
  have hsum := (h0s.add h1s).mul_left 2
  have hS : Summable fun k => ‖advC (dF l s) c k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle hsum
  refine ⟨hS, ?_⟩
  rw [sn_zero]
  refine (hS.tsum_le_tsum hle hsum).trans ?_
  rw [tsum_mul_left, h0s.tsum_add h1s]
  linarith

/-! ### The next level: Leibniz on the series -/

private lemma summable_level {c : Mode → ℂ} {j : ℕ}
    (hc : Summable fun k => absSq k ^ (j + 1) * ‖c k‖ ^ 2) (l : Fin 3) :
    Summable fun k => absSq k ^ j * ‖dC l c k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (absSq_nonneg k) _) (by positivity)) (fun k => ?_) hc
  rw [pow_succ (absSq k) j, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_dC_sq_le l c k) (pow_nonneg (absSq_nonneg k) _)

private lemma summable_mul_l1_l2 {a b : Mode → ℂ} (ha : Summable fun k => ‖a k‖)
    (hb : Summable fun k => ‖b k‖ ^ 2) (m : Mode) : Summable fun p => a p * b (m - p) :=
  Summable.of_norm (by
    simpa only [norm_mul] using (young_l1_l2 (a := fun k => ‖a k‖) (b := fun k => ‖b k‖)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) ha hb).1 m)

private lemma summable_mul_l2_l2 {a b : Mode → ℂ} (ha : Summable fun k => ‖a k‖ ^ 2)
    (hb : Summable fun k => ‖b k‖ ^ 2) (m : Mode) : Summable fun p => a p * b (m - p) :=
  Summable.of_norm (by simpa only [norm_mul] using summable_mul_of_l2 ha hb m)

/-- Leibniz for the convolution. -/
private lemma dC_cv (l : Fin 3) {a b : Mode → ℂ} {m : Mode}
    (h1 : Summable fun p => a p * dC l b (m - p)) (h2 : Summable fun p => dC l a p * b (m - p)) :
    dC l (cv a b) m = cv a (dC l b) m + cv (dC l a) b m := by
  rw [cv, cv, ← h1.tsum_add h2]
  change Complex.I * (m l : ℂ) * ∑' p, a p * b (m - p) = _
  rw [← tsum_mul_left]
  refine tsum_congr fun p => ?_
  simp only [dC, Pi.sub_apply, Int.cast_sub]
  ring

private lemma dC_comm (l i : Fin 3) (c : Mode → ℂ) : dC i (dC l c) = dC l (dC i c) := by
  funext k
  simp only [dC]
  ring

/-- **Leibniz for the transport**: `∂_l (s·∇c) = s·∇(∂_l c) + (∂_l s)·∇c`. -/
private lemma dC_advC {s : Field} {c : Mode → ℂ} (hs : InH 2 s)
    (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2) (l : Fin 3) (m : Mode) :
    dC l (advC s c) m = advC s (dC l c) m + advC (dF l s) c m := by
  have hterm : ∀ i, dC l (cv (GN.cmp s i) (dC i c)) m =
      cv (GN.cmp s i) (dC i (dC l c)) m + cv (GN.cmp (dF l s) i) (dC i c) m := fun i => by
    rw [cmp_dF, dC_comm]
    refine dC_cv l ?_ ?_
    · exact summable_mul_l1_l2 (summable_cmp (summable_wiener hs) i)
        (summable_dC_sq' l (summable_level (j := 1) hc2 i)) m
    · exact summable_mul_l2_l2 (summable_dC_sq (hs.mono (by norm_num)) l i)
        (summable_dC_sq' i hc1) m
  have e : dC l (advC s c) m = ∑ i, dC l (cv (GN.cmp s i) (dC i c)) m := by
    simp only [dC, advC, Finset.mul_sum]
  rw [e, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
  rfl

private lemma dC_conj {c : Mode → ℂ} (hcR : ∀ k, c (-k) = conj (c k)) (l : Fin 3) (k : Mode) :
    dC l c (-k) = conj (dC l c k) := by
  simp only [dC, hcR, Pi.neg_apply, Int.cast_neg, map_mul, Complex.conj_I, map_intCast]
  ring

private lemma absSq_slow' {k : Mode} (hk : k 2 = 0) : absSq k = (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 := by
  simp [absSq, Fin.sum_univ_three, hk]

/-- The levels of the horizontal derivatives add up. -/
private lemma sn_dC_add {c : Mode → ℂ} (hcs : ∀ k, k 2 ≠ 0 → c k = 0) {j : ℕ}
    (hc : Summable fun k => absSq k ^ (j + 1) * ‖c k‖ ^ 2) :
    sn j (dC 0 c) + sn j (dC 1 c) = sn (j + 1) c := by
  rw [sn, sn, sn, ← (summable_level hc 0).tsum_add (summable_level hc 1)]
  refine tsum_congr fun k => ?_
  by_cases hk : k 2 = 0
  · rw [normSq_dC, normSq_dC, pow_succ, absSq_slow' hk]
    ring
  · simp [dC, hcs k hk]

/-- `pairS 2` is the sum of the `pairS 1` of the horizontal derivatives. -/
private lemma pairS_two_eq {c d : Mode → ℂ} (hcs : ∀ k, k 2 ≠ 0 → c k = 0)
    (h0 : Summable fun k => absSq k ^ 1 * (conj (dC 0 c k) * dC 0 d k).re)
    (h1 : Summable fun k => absSq k ^ 1 * (conj (dC 1 c k) * dC 1 d k).re) :
    pairS 2 c d = pairS 1 (dC 0 c) (dC 0 d) + pairS 1 (dC 1 c) (dC 1 d) := by
  rw [pairS, pairS, pairS, ← h0.tsum_add h1]
  refine tsum_congr fun k => ?_
  by_cases hk : k 2 = 0
  · have e : ∀ l : Fin 3, conj (dC l c k) * dC l d k =
        (((k l : ℝ) ^ 2 : ℝ) : ℂ) * (conj (c k) * d k) := fun l => by
      simp only [dC, map_mul, Complex.conj_I, map_intCast]
      push_cast
      linear_combination (-(k l : ℂ) ^ 2 * conj (c k) * d k) * Complex.I_mul_I
    rw [e 0, e 1, Complex.re_ofReal_mul, Complex.re_ofReal_mul, absSq_slow' hk]
    ring
  · simp [dC, hcs k hk]

private lemma summable_pair_re {a b : Mode → ℂ}
    (ha : Summable fun k => absSq k ^ 2 * ‖a k‖ ^ 2) (hb : Summable fun k => ‖b k‖ ^ 2) :
    Summable fun k => absSq k ^ 1 * (conj (a k) * b k).re := by
  refine (Complex.reCLM.summable (summable_pair_term ha hb)).congr fun k => ?_
  rw [pow_one]
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul]

private lemma pairS_one_add {a x y : Mode → ℂ}
    (ha : Summable fun k => absSq k ^ 2 * ‖a k‖ ^ 2) (hx : Summable fun k => ‖x k‖ ^ 2)
    (hy : Summable fun k => ‖y k‖ ^ 2) :
    pairS 1 a (fun k => x k + y k) = pairS 1 a x + pairS 1 a y := by
  rw [pairS, pairS, pairS, ← (summable_pair_re ha hx).tsum_add (summable_pair_re ha hy)]
  refine tsum_congr fun k => ?_
  rw [mul_add, Complex.add_re, mul_add]

/-- Cauchy–Schwarz for `pairS 1`. -/
private lemma abs_pairS_one_le {a b : Mode → ℂ} (ha : Summable fun k => absSq k ^ 2 * ‖a k‖ ^ 2)
    (hb : Summable fun k => ‖b k‖ ^ 2) :
    |pairS 1 a b| ≤ Real.sqrt (sn 2 a) * Real.sqrt (sn 0 b) := by
  have hf : Summable fun k => (absSq k * ‖a k‖) ^ 2 := ha.congr fun k => by ring
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (f := fun k => absSq k * ‖a k‖) (g := fun k => ‖b k‖)
    (fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _)) (fun _ => norm_nonneg _)
    (by simpa only [Real.rpow_two] using hf) (by simpa only [Real.rpow_two] using hb)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  have e1 : ∑' k, (absSq k * ‖a k‖) ^ 2 = sn 2 a := tsum_congr fun k => by ring
  have e2 : ∑' k, ‖b k‖ ^ 2 = sn 0 b := (sn_zero b).symm
  rw [e1, e2] at h
  rw [pairS_one_eq ha hb]
  refine (Complex.abs_re_le_norm _).trans ?_
  have hn : ∀ k, ‖(absSq k : ℂ) * (conj (a k) * b k)‖ = absSq k * ‖a k‖ * ‖b k‖ := fun k => by
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (absSq_nonneg k)]
    ring
  refine (tsum_of_norm_bounded h.1.hasSum fun k => (hn k).le).trans h.2

/-- One horizontal derivative of the `H²` commutator. -/
private lemma abs_pairS_dC_le {s : Field} {c : Mode → ℂ} (hs : Adm 2 s) (hs3 : InH 3 s)
    (hsl : PiS s = s) (hcR : ∀ k, c (-k) = conj (c k)) (hcs : ∀ k, k 2 ≠ 0 → c k = 0)
    (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2)
    (hc3 : Summable fun k => absSq k ^ 3 * ‖c k‖ ^ 2)
    {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D) (hstr : StrainBd s q D)
    (hstr2 : StrainBd s (2 * q) D) (hDΛ : D ^ q ≤ Λ ^ (q - 1)) {l : Fin 3} (hl : l ≠ 2) :
    (Summable fun k => absSq k ^ 1 * (conj (dC l c k) * dC l (advC s c) k).re) ∧
      |pairS 1 (dC l c) (dC l (advC s c))| ≤ 2 * Λ * sn 1 (dC l c) +
        10 * Real.sqrt (sn 1 (dC l c)) * Real.sqrt (sn 2 (dC l c)) +
        2 * Real.sqrt (sn 2 (dC l c)) *
          Real.sqrt (Λ ^ 2 * sn 1 c + 5 * Real.sqrt (sn 1 c) * Real.sqrt (sn 2 c)) := by
  set E := Λ ^ 2 * sn 1 c + 5 * Real.sqrt (sn 1 c) * Real.sqrt (sn 2 c) with hE
  have hE0 : 0 ≤ E := by
    have := sn_nonneg 1 c
    positivity
  set g := dC l c with hg
  have hg1 : Summable fun k => absSq k ^ 1 * ‖g k‖ ^ 2 := summable_level hc2 l
  have hg2 : Summable fun k => absSq k ^ 2 * ‖g k‖ ^ 2 := summable_level hc3 l
  have hgR : ∀ k, g (-k) = conj (g k) := dC_conj hcR l
  have hA := abs_pairS_adv_le hs hs3 hsl hgR (dC_slow hcs l) hg1 hg2 hq hΛ hD hstr hDΛ
  obtain ⟨heS, heB⟩ := sn_zero_advC_dF_le hs hs3 hsl hcR hcs hc1 hc2 hq hΛ hD hstr2 hDΛ hl
  have hx : Summable fun k => ‖advC s g k‖ ^ 2 := summable_advC_sq hs.inH hg1
  have hd : dC l (advC s c) = fun k => advC s g k + advC (dF l s) c k :=
    funext fun k => dC_advC hs.inH hc1 hc2 l k
  have hs4 : Summable fun k => ‖dC l (advC s c) k‖ ^ 2 := by
    rw [hd]
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
      ((hx.add heS).mul_left 2)
    have h := norm_add_le (advC s g k) (advC (dF l s) c k)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖advC s g k‖ - ‖advC (dF l s) c k‖)]
  refine ⟨summable_pair_re hg2 hs4, ?_⟩
  rw [hd, pairS_one_add hg2 hx heS]
  have hB := abs_pairS_one_le hg2 heS
  have hsq : Real.sqrt (sn 0 (advC (dF l s) c)) ≤ 2 * Real.sqrt E := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hE0]
    linarith
  have h5 := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg (sn 2 g))
  have h6 := abs_add_le (pairS 1 g (advC s g)) (pairS 1 g (advC (dF l s) c))
  nlinarith

/-- **The passive `H²` commutator**, at a fixed time. -/
theorem abs_pairS_two_adv_le {s : Field} {c : Mode → ℂ} (hs : Adm 2 s) (hs3 : InH 3 s)
    (hsl : PiS s = s) (hcR : ∀ k, c (-k) = conj (c k)) (hcs : ∀ k, k 2 ≠ 0 → c k = 0)
    (hc0 : c 0 = 0) (hc1 : Summable fun k => absSq k ^ 1 * ‖c k‖ ^ 2)
    (hc2 : Summable fun k => absSq k ^ 2 * ‖c k‖ ^ 2)
    (hc3 : Summable fun k => absSq k ^ 3 * ‖c k‖ ^ 2)
    {q : ℕ} (hq : 1 ≤ q) {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D) (hstr : StrainBd s q D)
    (hstr2 : StrainBd s (2 * q) D) (hDΛ : D ^ q ≤ Λ ^ (q - 1)) :
    |pairS 2 c (advC s c)| ≤ 2 * Λ * sn 2 c + 10 * Real.sqrt (sn 2 c) * Real.sqrt (sn 3 c) +
      3 * Real.sqrt (sn 3 c) *
        Real.sqrt (Λ ^ 2 * sn 1 c + 5 * Real.sqrt (sn 1 c) * Real.sqrt (sn 2 c)) := by
  have _ := hc0
  set E := Λ ^ 2 * sn 1 c + 5 * Real.sqrt (sn 1 c) * Real.sqrt (sn 2 c) with hE
  have hE0 : 0 ≤ E := by
    have := sn_nonneg 1 c
    positivity
  have key : ∀ l : Fin 3, l ≠ 2 →
      (Summable fun k => absSq k ^ 1 * (conj (dC l c k) * dC l (advC s c) k).re) ∧
      |pairS 1 (dC l c) (dC l (advC s c))| ≤ 2 * Λ * sn 1 (dC l c) +
        10 * Real.sqrt (sn 1 (dC l c)) * Real.sqrt (sn 2 (dC l c)) +
        2 * Real.sqrt (sn 2 (dC l c)) * Real.sqrt E := fun l hl =>
    abs_pairS_dC_le hs hs3 hsl hcR hcs hc1 hc2 hc3 hq hΛ hD hstr hstr2 hDΛ hl
  have h0 := key 0 (by decide)
  have h1 := key 1 (by decide)
  rw [pairS_two_eq hcs h0.1 h1.1]
  have hA := sn_dC_add hcs (j := 1) hc2
  have hB := sn_dC_add hcs (j := 2) hc3
  simp only [one_add_one_eq_two] at hA
  rw [show 2 + 1 = 3 from rfl] at hB
  have hA0 := sn_nonneg 1 (dC 0 c)
  have hA1 := sn_nonneg 1 (dC 1 c)
  have hB0 := sn_nonneg 2 (dC 0 c)
  have hB1 := sn_nonneg 2 (dC 1 c)
  have hC := sqrt_cauchy hA0 hA1 hB0 hB1
  rw [hA, hB] at hC
  have hC2 := sqrt_cauchy (zero_le_one' ℝ) (zero_le_one' ℝ) hB0 hB1
  rw [hB, Real.sqrt_one, one_mul, one_mul, one_add_one_eq_two] at hC2
  have h2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hs3' := Real.sqrt_nonneg (sn 3 c)
  have hsE := Real.sqrt_nonneg E
  have hC3 : 2 * (Real.sqrt (sn 2 (dC 0 c)) + Real.sqrt (sn 2 (dC 1 c))) * Real.sqrt E ≤
      3 * Real.sqrt (sn 3 c) * Real.sqrt E := by
    refine mul_le_mul_of_nonneg_right ?_ hsE
    nlinarith [mul_le_mul_of_nonneg_right h2 hs3']
  have h3 := abs_add_le (pairS 1 (dC 0 c) (dC 0 (advC s c))) (pairS 1 (dC 1 c) (dC 1 (advC s c)))
  have h4 : 2 * Λ * sn 1 (dC 0 c) + 2 * Λ * sn 1 (dC 1 c) = 2 * Λ * sn 2 c := by
    rw [← hA]
    ring
  nlinarith [h0.2, h1.2]

/-! ### Bridges to the fields -/

private lemma sobWeight_natCast {k : Mode} (hk : k ≠ 0) (j : ℕ) :
    sobWeight (j : ℝ) k = absSq k ^ j := by
  simp only [sobWeight, hk, ↓reduceIte]
  have e : (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) := by
    push_cast
    ring
  rw [e, Real.rpow_natCast, pow_mul, absk_sq]

private lemma norm_PiV_sq {z : Field} (hz' : PiS z = z) (k : Mode) :
    ‖PiV z k‖ ^ 2 = ‖GN.cmp z 2 k‖ ^ 2 := by
  by_cases hk : k 2 = 0
  · simp only [PiV, hk, ↓reduceIte]
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three, GN.cmp]
  · simp [PiV, hk, cmp_slow hz' 2 k hk]

private lemma norm_PiH_sq {z : Field} {k : Mode} (hk : k 2 = 0) :
    ‖PiH z k‖ ^ 2 = ‖z k 0‖ ^ 2 + ‖z k 1‖ ^ 2 := by
  simp only [PiH, hk, ↓reduceIte]
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]

/-- The Lagrange identity, for a pair orthogonal to `(x, y)`. -/
private lemma lagrange_norm {x y : ℝ} {v w : ℂ} (h : (x : ℂ) * v + (y : ℂ) * w = 0) :
    ‖(x : ℂ) * w - (y : ℂ) * v‖ ^ 2 = (x ^ 2 + y ^ 2) * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.add_im, Complex.im_ofReal_mul,
    Complex.zero_re, Complex.zero_im] at hre him
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  linear_combination (-(x * v.re + y * w.re)) * hre + (-(x * v.im + y * w.im)) * him

/-- The Lagrange identity, polarized. -/
private lemma lagrange_inner {x y : ℝ} {v₀ v₁ w₀ w₁ : ℂ} (h : (x : ℂ) * v₀ + (y : ℂ) * v₁ = 0) :
    ((x ^ 2 + y ^ 2 : ℝ) : ℂ) * (conj v₀ * w₀ + conj v₁ * w₁) =
      conj ((x : ℂ) * v₁ - (y : ℂ) * v₀) * ((x : ℂ) * w₁ - (y : ℂ) * w₀) := by
  have h' : (x : ℂ) * conj v₀ + (y : ℂ) * conj v₁ = 0 := by
    simpa using congrArg conj h
  simp only [map_sub, map_mul, Complex.conj_ofReal]
  push_cast
  linear_combination ((x : ℂ) * w₀ + (y : ℂ) * w₁) * h'

/-- The orthogonality of a slow solenoidal coefficient to its mode. -/
private lemma dot_slow {z : Field} (hz : IsSolenoidal z) {k : Mode} (hk : k 2 = 0) :
    (((k 0 : ℤ) : ℝ) : ℂ) * z k 0 + (((k 1 : ℤ) : ℝ) : ℂ) * z k 1 = 0 := by
  have h := hz k
  simp only [dotM, Fin.sum_univ_three, hk, Int.cast_zero, mul_zero, add_zero] at h
  push_cast
  linear_combination h

private lemma norm_wC_sq {z : Field} (hz : IsSolenoidal z) (hz' : PiS z = z) (k : Mode) :
    ‖wC z k‖ ^ 2 = absSq k * ‖PiH z k‖ ^ 2 := by
  by_cases hk : k 2 = 0
  · rw [norm_PiH_sq hk, wC, curlL_apply, norm_mul, Complex.norm_I, one_mul, absSq_slow' hk]
    have h := lagrange_norm (dot_slow hz hk)
    push_cast at h
    exact h
  · simp [wC, PiH, hk, slow_zero' hz' hk, curlL_apply]

lemma sn_cmp_two {z : Field} (hz' : PiS z = z) (h0 : z 0 = 0) (j : ℕ) :
    sn j (GN.cmp z 2) = hnorm j (PiV z) ^ 2 := by
  rw [hnorm, Real.sq_sqrt (tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg _ _) (sq_nonneg _))]
  refine tsum_congr fun k => ?_
  rw [norm_PiV_sq hz']
  by_cases hk : k = 0
  · subst hk
    simp [sobWeight, GN.cmp, h0]
  · rw [sobWeight_natCast hk]

lemma sn_wC {z : Field} (hz : Adm 2 z) (hz' : PiS z = z) (j : ℕ) :
    sn j (wC z) = hnorm ((j : ℝ) + 1) (PiH z) ^ 2 := by
  rw [hnorm, Real.sq_sqrt (tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg _ _) (sq_nonneg _))]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [sobWeight, wC, curlL_apply]
  · have e : (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by push_cast; rfl
    rw [e, sobWeight_natCast hk, norm_wC_sq hz.sol hz', pow_succ (absSq k) j]
    ring

private lemma inner_PiV {z F : Field} (hz' : PiS z = z) (k : Mode) :
    inner ℂ (PiV z k) (F k) = conj (GN.cmp z 2 k) * GN.cmp F 2 k := by
  by_cases hk : k 2 = 0
  · simp only [PiV, hk, ↓reduceIte, PiLp.inner_apply, Fin.sum_univ_three]
    simp [GN.cmp, mul_comm]
  · simp [PiV, hk, cmp_slow hz' 2 k hk]

private lemma inner_PiH {z F : Field} {k : Mode} (hk : k 2 = 0) :
    inner ℂ (PiH z k) (F k) = conj (z k 0) * F k 0 + conj (z k 1) * F k 1 := by
  simp only [PiH, hk, ↓reduceIte, PiLp.inner_apply, Fin.sum_univ_three]
  simp [mul_comm]

theorem pair_one_PiV {z : Field} (hz : Adm 2 z) (hz' : PiS z = z) :
    pair 1 (PiV z) (Bsym z z) = pairS 1 (GN.cmp z 2) (advC z (GN.cmp z 2)) := by
  rw [pair, pairS]
  refine tsum_congr fun k => ?_
  rw [sobWeight_one, inner_PiV hz', cmp_Bsym_two hz hz', pow_one]

theorem pair_two_PiV {z : Field} (hz : Adm 2 z) (hz' : PiS z = z) :
    pair 2 (PiV z) (Bsym z z) = pairS 2 (GN.cmp z 2) (advC z (GN.cmp z 2)) := by
  rw [pair, pairS]
  refine tsum_congr fun k => ?_
  rw [sobWeight_two, inner_PiV hz', cmp_Bsym_two hz hz']

theorem pair_two_PiH {z : Field} (hz : Adm 2 z) (hz' : PiS z = z) :
    pair 2 (PiH z) (Bsym z z) = pairS 1 (wC z) (advC z (wC z)) := by
  rw [pair, pairS]
  refine tsum_congr fun k => ?_
  rw [sobWeight_two, ← wC_Bsym hz hz' k, pow_one]
  by_cases hk : k 2 = 0
  · rw [inner_PiH hk, wC, wC, curlL_apply, curlL_apply]
    have h := lagrange_inner (w₀ := Bsym z z k 0) (w₁ := Bsym z z k 1) (dot_slow hz.sol hk)
    push_cast at h
    have e : conj (Complex.I * ((k 0 : ℂ) * z k 1 - (k 1 : ℂ) * z k 0)) *
        (Complex.I * ((k 0 : ℂ) * Bsym z z k 1 - (k 1 : ℂ) * Bsym z z k 0)) =
        (((absSq k : ℝ) : ℂ)) * (conj (z k 0) * Bsym z z k 0 + conj (z k 1) * Bsym z z k 1) := by
      rw [absSq_slow' hk, map_mul, Complex.conj_I]
      push_cast
      rw [h]
      linear_combination (-conj ((k 0 : ℂ) * z k 1 - (k 1 : ℂ) * z k 0) *
        ((k 0 : ℂ) * Bsym z z k 1 - (k 1 : ℂ) * Bsym z z k 0)) * Complex.I_mul_I
    rw [e, Complex.re_ofReal_mul]
    ring
  · simp [PiH, hk, wC, slow_zero' hz' hk, curlL_apply]

end OVNS.Quant.Slow
