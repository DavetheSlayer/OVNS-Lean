import OddViscousNS.Quant.Joint.Slow.H1
import OddViscousNS.Quant.Joint.Slow.Riesz

/-!
# E7-P: from the vorticity to the strain, and Moser on the truncations of a passive scalar

* `strain_eq_zero`, `strain_eq_one`: `∂_i z₀ = R_i R₁ ω`, `∂_i z₁ = −R_i R₀ ω` on box truncations of
  a slow solenoidal field: Biot–Savart.
* `strainBd_of_poly`: the `L^{2q}` bound of the truncated vorticity gives `StrainBd`.
* `Passive.moser_eventually`: `moser` on the truncations, for all large boxes.
* `Passive.propagate_eventually`: propagation from a start at a time `a` (true zero), for all large
  boxes.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.Slow

open GN

/-- The Riesz constant of the strain. -/
def rK (q : ℕ) : ℝ := (4 * (4 * (q : ℝ) + 1)) ^ 2

lemma one_le_rK (q : ℕ) : 1 ≤ rK q := by
  have h : (1 : ℝ) ≤ 4 * (4 * (q : ℝ) + 1) := by
    have : (0 : ℝ) ≤ q := by positivity
    linarith
  exact one_le_pow₀ h

lemma mP_neg (q : ℕ) (P : Pol) : mP q (-P) = mP q P := by
  simp [mP]

lemma absSq_slow {k : Mode} (hk : k 2 = 0) : absSq k = (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 := by
  simp [absSq, Fin.sum_univ_three, hk]

lemma ne_zero_absk_sq {k : Mode} (hk : k ≠ 0) : ((absk k : ℝ) : ℂ) ^ 2 ≠ 0 := by
  have h := one_le_absSq hk
  have h2 : absk k ^ 2 = absSq k := absk_sq k
  have h3 : absk k ^ 2 ≠ 0 := by rw [h2]; linarith
  exact_mod_cast h3

/-- Biot–Savart on a mode, the first component. -/
lemma strain_alg_zero {I' ρ k0 k1 ki z0 z1 : ℂ} (hI : I' * I' = -1) (hρ : ρ ^ 2 = k0 ^ 2 + k1 ^ 2)
    (hρ0 : ρ ≠ 0) (hsol : z0 * k0 + z1 * k1 = 0) :
    I' * ki * z0 = (I' * (ki / ρ)) * ((I' * (k1 / ρ)) * (I' * (k0 * z1 - k1 * z0))) := by
  have h2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ0
  have e : (I' * (ki / ρ)) * ((I' * (k1 / ρ)) * (I' * (k0 * z1 - k1 * z0))) =
      (I' * I') * I' * ki * k1 * (k0 * z1 - k1 * z0) / ρ ^ 2 := by
    field_simp
  rw [e, hI, eq_div_iff h2, hρ]
  linear_combination (I' * ki * k0) * hsol

/-- Biot–Savart on a mode, the second component. -/
lemma strain_alg_one {I' ρ k0 k1 ki z0 z1 : ℂ} (hI : I' * I' = -1) (hρ : ρ ^ 2 = k0 ^ 2 + k1 ^ 2)
    (hρ0 : ρ ≠ 0) (hsol : z0 * k0 + z1 * k1 = 0) :
    I' * ki * z1 = -((I' * (ki / ρ)) * ((I' * (k0 / ρ)) * (I' * (k0 * z1 - k1 * z0)))) := by
  have h2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ0
  have e : (I' * (ki / ρ)) * ((I' * (k0 / ρ)) * (I' * (k0 * z1 - k1 * z0))) =
      (I' * I') * I' * ki * k0 * (k0 * z1 - k1 * z0) / ρ ^ 2 := by
    field_simp
  rw [e, hI, ← neg_div, eq_div_iff h2, hρ]
  linear_combination (I' * ki * k1) * hsol

lemma absk_ne_zero' {k : Mode} (hk : k ≠ 0) : ((absk k : ℝ) : ℂ) ≠ 0 := by
  intro h
  exact ne_zero_absk_sq hk (by rw [h]; ring)

lemma absk_sq_complex {k : Mode} (hk : k 2 = 0) :
    ((absk k : ℝ) : ℂ) ^ 2 = (k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 := by
  have h := absk_sq k
  rw [absSq_slow hk] at h
  have h2 : (((absk k ^ 2 : ℝ)) : ℂ) = (((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 : ℝ) : ℂ) := by rw [h]
  push_cast at h2
  exact h2

lemma sol_slow {z : Field} (hsol : IsSolenoidal z) {k : Mode} (hk : k 2 = 0) :
    z k 0 * (k 0 : ℂ) + z k 1 * (k 1 : ℂ) = 0 := by
  have h := hsol k
  simpa [dotM, Fin.sum_univ_three, hk] using h

/-- `∂_i z₀ = R_i R₁ ω` on box truncations. -/
lemma strain_eq_zero {z : Field} (hsol : IsSolenoidal z) (N : ℕ) (i : Fin 3) :
    D i (polyOf (slowBox N) (GN.cmp z 0)) =
      riesz i (riesz 1 (polyOf (slowBox N) (wC z))) := by
  ext k
  simp only [D, riesz, coeff_mult, coeff_polyOf, tr]
  split_ifs with hk
  · have hk2 := (mem_slowBox.1 hk).1
    by_cases hk0 : k = 0
    · subst hk0
      simp [dSym, rieszSym]
    · simp only [rieszSym, hk0, ↓reduceIte, wC, curlL_apply, dSym]
      push_cast
      exact strain_alg_zero Complex.I_mul_I (absk_sq_complex hk2) (absk_ne_zero' hk0)
        (sol_slow hsol hk2)
  · simp

/-- `∂_i z₁ = −R_i R₀ ω` on box truncations. -/
lemma strain_eq_one {z : Field} (hsol : IsSolenoidal z) (N : ℕ) (i : Fin 3) :
    D i (polyOf (slowBox N) (GN.cmp z 1)) =
      -riesz i (riesz 0 (polyOf (slowBox N) (wC z))) := by
  ext k
  simp only [D, riesz, coeff_mult, coeff_polyOf, tr, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]
  split_ifs with hk
  · have hk2 := (mem_slowBox.1 hk).1
    by_cases hk0 : k = 0
    · subst hk0
      simp [dSym, rieszSym]
    · simp only [rieszSym, hk0, ↓reduceIte, wC, curlL_apply, dSym]
      push_cast
      exact strain_alg_one Complex.I_mul_I (absk_sq_complex hk2) (absk_ne_zero' hk0)
        (sol_slow hsol hk2)
  · simp

lemma wC_neg {z : Field} (hz : IsReal z) (k : Mode) : wC z (-k) = conj (wC z k) := by
  rw [wC, wC, curlL_apply, curlL_apply, hz k]
  simp only [conjV, Pi.neg_apply, Int.cast_neg, map_mul, map_sub, Complex.conj_I, map_intCast]
  ring

lemma wC_zero (z : Field) : wC z 0 = 0 := by
  simp [wC, curlL_apply]

lemma realC_polyOf_box {a : Mode → ℂ} (ha : ∀ k, a (-k) = conj (a k)) (N : ℕ) :
    RealC (polyOf (slowBox N) a) := fun k => by
  rw [coeff_polyOf, coeff_polyOf]
  exact tr_neg_conj (fun _ => neg_mem_slowBox) ha k

lemma slow_polyOf_box (a : Mode → ℂ) (N : ℕ) : IsSlowP (polyOf (slowBox N) a) :=
  isSlowP_polyOf (fun _ hk => (mem_slowBox.1 hk).1) a

lemma mP_double_riesz_le {f : Pol} (hR : RealC f) (hs : IsSlowP f) (h0 : mean f = 0) {q : ℕ}
    (hq : 1 ≤ q) {i j : Fin 3} (hi : i = 0 ∨ i = 1) (hj : j = 0 ∨ j = 1) :
    mP q (riesz i (riesz j f)) ≤ rK q ^ (2 * q) * mP q f := by
  have h1 := mP_riesz_le hR hs h0 hj q hq
  have h2 := mP_riesz_le (hR.riesz j) (hs.riesz j) (mean_riesz j f) hi q hq
  have e : rK q ^ (2 * q) =
      (4 * (4 * (q : ℝ) + 1)) ^ (2 * q) * (4 * (4 * (q : ℝ) + 1)) ^ (2 * q) := by
    rw [rK, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [e, mul_assoc]
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))

/-- **Biot–Savart and Riesz on truncations**. -/
lemma mP_strain_le {z : Field} (hz : Adm 2 z) {q : ℕ} (hq : 1 ≤ q) (N : ℕ) {i j : Fin 3}
    (hi : i ≠ 2) (hj : j ≠ 2) :
    mP q (D i (polyOf (slowBox N) (GN.cmp z j))) ≤
      rK q ^ (2 * q) * mP q (polyOf (slowBox N) (wC z)) := by
  have hR : RealC (polyOf (slowBox N) (wC z)) := realC_polyOf_box (wC_neg hz.real) N
  have hs := slow_polyOf_box (wC z) N
  have h0 : mean (polyOf (slowBox N) (wC z)) = 0 := by
    simp only [mean, coeff_polyOf, tr]
    split_ifs
    · exact wC_zero z
    · rfl
  have hi' : i = 0 ∨ i = 1 := by omega
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · rw [strain_eq_zero hz.sol]
    exact mP_double_riesz_le hR hs h0 hq hi' (Or.inr rfl)
  · rw [strain_eq_one hz.sol, mP_neg]
    exact mP_double_riesz_le hR hs h0 hq hi' (Or.inl rfl)

/-- **The strain from the truncated vorticity.** -/
theorem strainBd_of_poly {z : Field} (hz : Adm 2 z) {q : ℕ} (hq : 1 ≤ q) {Y : ℝ} (hY : 0 ≤ Y)
    (h : ∀ᶠ N : ℕ in atTop, mP q (polyOf (slowBox (2 * N)) (wC z)) ≤ Y ^ q) :
    StrainBd z q (rK q * Real.sqrt Y) := by
  filter_upwards [h] with N hN i j hi hj
  have hK : 0 ≤ rK q ^ (2 * q) := by
    have := one_le_rK q
    positivity
  have e : (rK q * Real.sqrt Y) ^ (2 * q) = rK q ^ (2 * q) * Y ^ q := by
    rw [mul_pow, pow_mul (Real.sqrt Y), Real.sq_sqrt hY]
  rw [e]
  exact (mP_strain_le hz hq _ hi hj).trans (mul_le_mul_of_nonneg_left hN hK)

/-! ### Moser on the truncations of a passive scalar -/

variable {a b : ℝ} {s : ℝ → Field} {c f : ℝ → Mode → ℂ}

/-- The hypotheses of the source bound at almost every time. -/
def SrcAe (a b : ℝ) (s : ℝ → Field) (c f : ℝ → Mode → ℂ) (G E : ℝ → ℝ) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Icc a b)), MZ 3 (s t) ∧ MZ 2 (s t) ∧
    (∀ k, k 2 ≠ 0 → s t k = 0) ∧ (∀ k, k 2 ≠ 0 → c t k = 0) ∧
    (Summable fun k => absSq k ^ 1 * ‖c t k‖ ^ 2) ∧
    (Summable fun k => absSq k ^ 2 * ‖c t k‖ ^ 2) ∧ (Summable fun k => ‖f t k‖ ^ 2) ∧
    sn 0 (f t) ≤ G t ∧ hnorm 3 (s t) ^ 2 * sn 1 (c t) + hnorm 2 (s t) ^ 2 * sn 2 (c t) ≤ E t

/-- For all large boxes, the integrated source of the truncation is `≤ Y`. -/
lemma Passive.eventually_src (h : Passive a b s c f) {Y : ℝ} (hY : 0 < Y) {G E : ℝ → ℝ}
    (hG : IntervalIntegrable G volume a b) (hE : IntervalIntegrable E volume a b)
    (hae : SrcAe a b s c f G E) (hG2 : 4 * (∫ t in a..b, G t) ≤ Y) :
    ∀ᶠ N : ℕ in atTop, ∫ t in a..b,
      nn2 (srcP (slowBox (2 * N)) c (rhsP s c f) (fun t i => GN.cmp (s t) i) t) ≤ Y := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (72 * c4 ^ 2 * |∫ t in a..b, E t| / Y)
  filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN
  have hN1 : 1 ≤ N := by omega
  have h1 := h.integral_src_le hN1 hG hE hae
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN2 : (N₀ : ℝ) ≤ N := by exact_mod_cast (by omega : N₀ ≤ N)
  have h2 : 36 * c4 ^ 2 / N ^ 2 * (∫ t in a..b, E t) ≤ Y / 2 := by
    have h3 : 72 * c4 ^ 2 * |∫ t in a..b, E t| ≤ Y * N := by
      have := hN₀.trans hN2
      rw [div_le_iff₀ hY] at this
      linarith
    have h4 : (∫ t in a..b, E t) ≤ |∫ t in a..b, E t| := le_abs_self _
    have hN3 : (N : ℝ) ≤ N ^ 2 := by nlinarith
    have h5 : 72 * c4 ^ 2 * (∫ t in a..b, E t) ≤ Y * N ^ 2 := by
      have hc := sq_nonneg c4
      nlinarith [mul_le_mul_of_nonneg_left hN3 hY.le]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  linarith

/-- **Moser for a passive scalar, for all large boxes.** -/
theorem Passive.moser_eventually (h : Passive a b s c f) {T Y : ℝ} (hT : b - a ≤ T) (hT0 : 0 ≤ T)
    (hY : 0 < Y) {G E : ℝ → ℝ} (hG : IntervalIntegrable G volume a b)
    (hE : IntervalIntegrable E volume a b) (hae : SrcAe a b s c f G E)
    (hG2 : 4 * (∫ t in a..b, G t) ≤ Y) (h0 : ∀ t ∈ Icc a b, Summable fun k => ‖c t k‖ ^ 2)
    (h1 : ∀ t ∈ Icc a b, sn 0 (c t) ≤ Y) (n : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (a + 1 - 1 / 2 ^ n) b,
      mP (2 ^ n) (polyOf (slowBox (2 * N)) (c t)) ≤ (piM T n * Y) ^ (2 ^ n) := by
  filter_upwards [h.eventually_src hY hG hE hae hG2] with N hN
  exact (h.polyPath (2 * N)).moser hT hT0 hY
    (fun t ht => (mP_one_polyOf_le (h0 t ht)).trans (h1 t ht)) hN n

/-- **Propagation for a passive scalar, for all large boxes**, from a start at `a`. -/
theorem Passive.propagate_eventually (h : Passive a b s c f) {T Y Y₀ : ℝ} (hT : b - a ≤ T)
    (hY : 0 < Y) (hY₀ : 0 < Y₀) {G E : ℝ → ℝ} (hG : IntervalIntegrable G volume a b)
    (hE : IntervalIntegrable E volume a b) (hae : SrcAe a b s c f G E)
    (hG2 : 4 * (∫ t in a..b, G t) ≤ Y) {n : ℕ}
    (hst : ∀ᶠ N : ℕ in atTop, mP (2 ^ n) (polyOf (slowBox (2 * N)) (c a)) ≤ Y₀ ^ (2 ^ n)) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc a b, mP (2 ^ n) (polyOf (slowBox (2 * N)) (c t)) ≤
      (Real.exp T * (2 * Y₀ + 201 * (2 : ℝ) ^ n * Y)) ^ (2 ^ n) := by
  filter_upwards [h.eventually_src hY hG hE hae hG2, hst] with N hN hN' t ht
  have hp := h.polyPath (2 * N)
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hb := hp.propagate hq le_rfl ht.1 ht.2 hY₀ hN'
  refine hb.trans (pow_le_pow_left₀ ?_ ?_ _)
  · have : 0 ≤ ∫ u in a..t, nn2 (srcP (slowBox (2 * N)) c (rhsP s c f)
        (fun t i => GN.cmp (s t) i) u) :=
      intervalIntegral.integral_nonneg ht.1 fun _ _ => nn2_nonneg _
    positivity
  · have hint : (∫ u in a..t, nn2 (srcP (slowBox (2 * N)) c (rhsP s c f)
        (fun t i => GN.cmp (s t) i) u)) ≤ Y := by
      refine (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Eventually.of_forall fun _ => nn2_nonneg _)
        (hp.continuousOn_srcNorm.intervalIntegrable_of_Icc hp.hab)).trans hN
    have hint0 : 0 ≤ ∫ u in a..t, nn2 (srcP (slowBox (2 * N)) c (rhsP s c f)
        (fun t i => GN.cmp (s t) i) u) :=
      intervalIntegral.integral_nonneg ht.1 fun _ _ => nn2_nonneg _
    have hexp : Real.exp ((t - a) / ((2 ^ n : ℕ) : ℝ)) ≤ Real.exp T := by
      refine Real.exp_le_exp.2 ?_
      have h3 : t - a ≤ T := by linarith [ht.2]
      have h4 : 0 ≤ t - a := by linarith [ht.1]
      have h5 : (1 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hq
      exact (div_le_self h4 h5).trans h3
    refine mul_le_mul hexp ?_ (by positivity) (Real.exp_pos _).le
    push_cast
    have : (0 : ℝ) ≤ 201 * 2 ^ n := by positivity
    nlinarith

end OVNS.Quant.Slow
