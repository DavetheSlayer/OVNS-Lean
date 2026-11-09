import OddViscousNS.Quant.Arith.Weighted.Conic
import OddViscousNS.Quant.Arith.Gamma

/-!
# `Y² − P` and the fixed-height quartic (Section C)

* `sq_or_absIrred`: over `ℚ`, `Y² − P(s)` is absolutely irreducible unless `P = c R²`.
* `Psi_t4`: the `t⁴` coefficient of `Ψ(t, w₀, k)` is `Δ²(n₃ + 2w₀)²`.
* `fixed_w_count`: at fixed height `w = k₃` the active points number `≤ C N^{1/4+η} + 2`
  (`PlaneCurveCount`, `d = 4`, `𝔗 ≥ B⁴`; the `+2` covers the square case with ≤ 2 real zeros).
* `height_count`: on a shell `T ≤ t < 2T` with `gcd(v, t) = g` there are at most `8gz/T`
  eligible heights (with the added hypothesis `0 ≤ z`, needed since only `z²` is constrained).
* `Wg_bound` (eq. quant-fixed-height): `W_g(n) ≤ C_η N^{1/4+η} g`.
-/

namespace OVNS.Quant

open Polynomial in
/-- Two monic polynomials with equal squares are equal. -/
private theorem monic_sq_unique {K : Type*} [_root_.Field K] [CharZero K] {R₁ R₂ : K[X]}
    (h1 : R₁.Monic) (h2 : R₂.Monic) (h : R₁ ^ 2 = R₂ ^ 2) : R₁ = R₂ := by
  have hd : R₁.natDegree = R₂.natDegree := by
    have := congrArg natDegree h
    rw [h1.natDegree_pow, h2.natDegree_pow] at this
    omega
  have hm : (R₁ - R₂) * (R₁ + R₂) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hm with h' | h'
  · exact sub_eq_zero.mp h'
  · exfalso
    have := congrArg (fun p => p.coeff R₁.natDegree) h'
    simp only [coeff_add, coeff_zero] at this
    rw [h1.coeff_natDegree, hd, h2.coeff_natDegree] at this
    norm_num at this

open Polynomial in
/-- C3: over `ℚ`, `Y² − P(s)` is absolutely irreducible or `P = c R²`. -/
theorem sq_or_absIrred (P : Polynomial ℚ) (hP : 0 < P.natDegree) :
    Irreducible ((Polynomial.X : Polynomial (Polynomial (AlgebraicClosure ℚ))) ^ 2 -
        Polynomial.C (P.map (algebraMap ℚ (AlgebraicClosure ℚ)))) ∨
      ∃ (c : ℚ) (R : Polynomial ℚ), P = Polynomial.C c * R ^ 2 := by
  by_cases hirr : Irreducible ((Polynomial.X : Polynomial (Polynomial (AlgebraicClosure ℚ))) ^ 2 -
        Polynomial.C (P.map (algebraMap ℚ (AlgebraicClosure ℚ))))
  · exact Or.inl hirr
  right
  set K := AlgebraicClosure ℚ
  set f := algebraMap ℚ K
  set Pb := P.map f with hPb
  have hmon : ((X : (K[X])[X]) ^ 2 - C Pb).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hdeg : ((X : (K[X])[X]) ^ 2 - C Pb).natDegree = 2 := natDegree_X_pow_sub_C _
  have hroots : ((X : (K[X])[X]) ^ 2 - C Pb).roots ≠ 0 := fun h =>
    hirr ((hmon.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr h)
  obtain ⟨A, hA⟩ := Multiset.exists_mem_of_ne_zero hroots
  have hA2 : A ^ 2 = Pb := by
    have := (mem_roots hmon.ne_zero).mp hA
    simpa [sub_eq_zero] using this
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  set c := P.leadingCoeff
  have hc : c ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  have hPb0 : Pb ≠ 0 := (Polynomial.map_ne_zero_iff f.injective).mpr hP0
  have hA0 : A ≠ 0 := by rintro rfl; simp at hA2; exact hPb0 hA2.symm
  set a := A.leadingCoeff
  have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr hA0
  have hac : a ^ 2 = f c := by
    have := congrArg leadingCoeff hA2
    rw [leadingCoeff_pow, hPb, leadingCoeff_map_of_injective f.injective] at this
    exact this
  set R₀ := C a⁻¹ * A
  have hR₀ : R₀.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ ha)
  set Q := C c⁻¹ * P
  have hR₀Q : R₀ ^ 2 = Q.map f := by
    simp only [R₀, Q, Polynomial.map_mul, map_C, mul_pow, ← C_pow, hA2, inv_pow, hac, map_inv₀, hPb]
  have hfix : ∀ σ : Gal(K/ℚ), R₀.map (σ : K →+* K) = R₀ := by
    intro σ
    apply monic_sq_unique (hR₀.map _) hR₀
    rw [← Polynomial.map_pow, hR₀Q, Polynomial.map_map]
    congr 1
    ext x
    simp [f]
  have hlift : R₀ ∈ lifts f := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    have := congrArg (fun p => p.coeff i) (hfix σ)
    simpa [coeff_map] using this
  obtain ⟨R, hR⟩ := (mem_lifts _).mp hlift
  refine ⟨c, R, Polynomial.map_injective f f.injective ?_⟩
  rw [Polynomial.map_mul, Polynomial.map_pow, hR, map_C, hR₀Q, ← hPb]
  simp only [Q, Polynomial.map_mul, map_C, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc,
    map_one, one_mul, hPb]

open Polynomial in
/-- `2 n₃ L` as a polynomial in `t` at fixed height `w`. -/
private noncomputable def Lp (Δ z n3 s3 w : ℤ) : ℤ[X] :=
  -(C (Δ * n3)) * (X + C (s3 * z)) ^ 2 - 2 * (C (n3 ^ 2) + C Δ * X ^ 2) * C w

open Polynomial in
/-- `n₃ x` as a polynomial in `t` at fixed height `w`. -/
private noncomputable def NXp (z n3 s3 w : ℤ) : ℤ[X] := C n3 * (X + C (s3 * z)) + X * C w

open Polynomial in
/-- The quartic `P_w(t)` with `|n_h|² Ψ = (2n₃|n_h|²k_i − n_i·2n₃L)² − P_w`. -/
private noncomputable def Pp (Δ z n3 ni nj s3 w : ℤ) : ℤ[X] :=
  -(C (nj ^ 2)) * (Lp Δ z n3 s3 w ^ 2 + C (4 * (ni ^ 2 + nj ^ 2) * n3 ^ 2 * w ^ 2) -
    C (4 * (ni ^ 2 + nj ^ 2) * Δ) * NXp z n3 s3 w ^ 2)

open Polynomial in
/-- Expanded form of `P_w`. -/
private theorem Pp_eq (Δ z n3 ni nj s3 w : ℤ) : Pp Δ z n3 ni nj s3 w =
    C (-nj ^ 2 * (Δ * (n3 + 2 * w)) ^ 2) * X ^ 4 +
    C (-nj ^ 2 * (2 * (Δ * (n3 + 2 * w)) * (2 * Δ * n3 * (s3 * z)))) * X ^ 3 +
    C (-nj ^ 2 * ((2 * Δ * n3 * (s3 * z)) ^ 2 +
      2 * (Δ * (n3 + 2 * w)) * (Δ * n3 * (s3 * z) ^ 2 + 2 * n3 ^ 2 * w) -
      4 * (ni ^ 2 + nj ^ 2) * Δ * (n3 + w) ^ 2)) * X ^ 2 +
    C (-nj ^ 2 * (2 * (2 * Δ * n3 * (s3 * z)) * (Δ * n3 * (s3 * z) ^ 2 + 2 * n3 ^ 2 * w) -
      8 * (ni ^ 2 + nj ^ 2) * Δ * (n3 + w) * n3 * (s3 * z))) * X +
    C (-nj ^ 2 * ((Δ * n3 * (s3 * z) ^ 2 + 2 * n3 ^ 2 * w) ^ 2 +
      4 * (ni ^ 2 + nj ^ 2) * n3 ^ 2 * w ^ 2 -
      4 * (ni ^ 2 + nj ^ 2) * Δ * n3 ^ 2 * (s3 * z) ^ 2)) := by
  simp only [Pp, Lp, NXp, map_mul, map_add, map_sub, map_neg, map_pow, map_ofNat]
  ring

open Polynomial in
/-- `P_w` has degree 4 with leading coefficient `-n_j²Δ²(n₃+2w)²`. -/
private theorem Pp_natDegree (Δ z n3 ni nj s3 w : ℤ) (hΔ : Δ ≠ 0) (hnj : nj ≠ 0)
    (hw : n3 + 2 * w ≠ 0) :
    (Pp Δ z n3 ni nj s3 w).natDegree = 4 ∧
    (Pp Δ z n3 ni nj s3 w).coeff 4 = -nj ^ 2 * (Δ * (n3 + 2 * w)) ^ 2 := by
  have hc : (Pp Δ z n3 ni nj s3 w).coeff 4 = -nj ^ 2 * (Δ * (n3 + 2 * w)) ^ 2 := by
    rw [Pp_eq]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    norm_num
  refine ⟨natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_, hc⟩
  · rw [Pp_eq]; compute_degree
  · rw [hc]; simp [hΔ, hnj, hw]

open MvPolynomial in
/-- `2 n₃ L` in `ℤ[t, k]`. -/
private noncomputable def Lm (Δ z n3 s3 w : ℤ) : MvPolynomial (Fin 2) ℤ :=
  -(C (Δ * n3)) * (X 0 + C (s3 * z)) ^ 2 - 2 * (C (n3 ^ 2) + C Δ * X 0 ^ 2) * C w

open MvPolynomial in
/-- `n₃ x` in `ℤ[t, k]`. -/
private noncomputable def NXm (z n3 s3 w : ℤ) : MvPolynomial (Fin 2) ℤ :=
  C n3 * (X 0 + C (s3 * z)) + X 0 * C w

open MvPolynomial in
/-- The fixed-height plane curve `Ψ(t, w, k_i) ∈ ℤ[t, k_i]`. -/
private noncomputable def wCurve (Δ z n3 ni nj s3 w : ℤ) : MvPolynomial (Fin 2) ℤ :=
  C (4 * n3 ^ 2 * nj ^ 2) * X 1 ^ 2 + (Lm Δ z n3 s3 w - C (2 * n3 * ni) * X 1) ^ 2 +
    C (4 * n3 ^ 2 * nj ^ 2 * w ^ 2) - C (4 * nj ^ 2 * Δ) * NXm z n3 s3 w ^ 2

open MvPolynomial in
/-- The completed-square identity `|n_h|² F = Y² − P_w(t)`. -/
private theorem wCurve_eval (Δ z n3 ni nj s3 w : ℤ) (x : Fin 2 → ℤ) :
    (ni ^ 2 + nj ^ 2) * eval x (wCurve Δ z n3 ni nj s3 w) =
      (2 * n3 * (ni ^ 2 + nj ^ 2) * x 1 - ni * (Lp Δ z n3 s3 w).eval (x 0)) ^ 2 -
        (Pp Δ z n3 ni nj s3 w).eval (x 0) := by
  simp only [wCurve, Lm, NXm, Pp, Lp, NXp, map_add, map_sub, map_mul, map_neg, map_pow,
    eval_C, eval_X, map_ofNat, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat]
  ring

open MvPolynomial in
/-- The fixed-height curve has total degree `≤ 4`. -/
private theorem wCurve_totalDegree_le (Δ z n3 ni nj s3 w : ℤ) :
    (wCurve Δ z n3 ni nj s3 w).totalDegree ≤ 4 := by
  have hX0 : (X 0 : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 1 := (totalDegree_X _).le
  have hX1 : (X 1 : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 1 := (totalDegree_X _).le
  have hC : ∀ a : ℤ, (C a : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 0 := fun a => (totalDegree_C a).le
  have hadd : ∀ (p q : MvPolynomial (Fin 2) ℤ) (m : ℕ), p.totalDegree ≤ m →
      q.totalDegree ≤ m → (p + q).totalDegree ≤ m :=
    fun p q m hp hq => (totalDegree_add p q).trans (max_le hp hq)
  have hsub : ∀ (p q : MvPolynomial (Fin 2) ℤ) (m : ℕ), p.totalDegree ≤ m →
      q.totalDegree ≤ m → (p - q).totalDegree ≤ m :=
    fun p q m hp hq => (totalDegree_sub p q).trans (max_le hp hq)
  have hmul : ∀ (p q : MvPolynomial (Fin 2) ℤ) (a b m : ℕ), p.totalDegree ≤ a →
      q.totalDegree ≤ b → a + b ≤ m → (p * q).totalDegree ≤ m :=
    fun p q a b m hp hq hm => (totalDegree_mul p q).trans (by omega)
  have hpow : ∀ (p : MvPolynomial (Fin 2) ℤ) (a k m : ℕ), p.totalDegree ≤ a →
      k * a ≤ m → (p ^ k).totalDegree ≤ m :=
    fun p a k m hp hm => (totalDegree_pow p k).trans (le_trans (Nat.mul_le_mul_left _ hp) hm)
  have hneg : ∀ (p : MvPolynomial (Fin 2) ℤ) (m : ℕ), p.totalDegree ≤ m →
      (-p).totalDegree ≤ m := fun p m hp => by rwa [totalDegree_neg]
  have h2 : (2 : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 0 := by
    rw [show (2 : MvPolynomial (Fin 2) ℤ) = C 2 by simp]; exact hC 2
  have hL : (Lm Δ z n3 s3 w).totalDegree ≤ 2 := by
    unfold Lm
    refine hsub _ _ _ (hmul _ _ 0 2 _ (hneg _ _ (hC _))
      (hpow _ 1 _ _ (hadd _ _ _ hX0 (hC _ |>.trans (by omega))) (by omega)) (by omega))
      (hmul _ _ 2 0 _ (hmul _ _ 0 2 _ h2 (hadd _ _ _ (hC _ |>.trans (by omega))
        (hmul _ _ 0 2 _ (hC _) (hpow _ 1 _ _ hX0 (by omega)) (by omega))) (by omega))
        (hC _) (by omega))
  have hN : (NXm z n3 s3 w).totalDegree ≤ 1 := by
    unfold NXm
    exact hadd _ _ _ (hmul _ _ 0 1 _ (hC _) (hadd _ _ _ hX0 (hC _ |>.trans (by omega)))
      (by omega)) (hmul _ _ 1 0 _ hX0 (hC _) (by omega))
  unfold wCurve
  refine hsub _ _ _ (hadd _ _ _ (hadd _ _ _ ?_ ?_) (hC _ |>.trans (by omega))) ?_
  · exact hmul _ _ 0 2 _ (hC _) (hpow _ 1 _ _ hX1 (by omega)) (by omega)
  · exact hpow _ 2 _ _ (hsub _ _ _ hL (hmul _ _ 0 1 _ (hC _) (hX1.trans (by omega))
      (by omega))) (by omega)
  · exact hmul _ _ 0 2 _ (hC _) (hpow _ 1 _ _ hN (by omega)) (by omega)

open MvPolynomial in
/-- Keep the pure-`t` part of a polynomial in `ℤ[t, k]`. -/
private noncomputable def tPart2 : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] Polynomial ℤ :=
  aeval fun i => if i = 0 then Polynomial.X else 0

open MvPolynomial in
/-- `tPart2` reads off the pure-`t` coefficients. -/
private theorem coeff_tPart2 (p : MvPolynomial (Fin 2) ℤ) (a : ℕ) :
    (tPart2 p).coeff a = p.coeff (Finsupp.single 0 a) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
    simp only [tPart2, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_two, coeff_monomial]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
    by_cases h : m = Finsupp.single 0 a
    · subst h; simp
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
      have hm : ¬ (m 0 = a ∧ m 1 = 0) := by
        rintro ⟨h0, h1⟩
        apply h
        ext i
        fin_cases i <;> simp [h0, h1]
      by_cases h1 : m 1 = 0
      · rw [h1]
        rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Polynomial.coeff_C_mul, pow_zero, mul_one, Polynomial.coeff_X_pow]
        simp [show a ≠ m 0 from fun h' => hm ⟨h'.symm, h1⟩]
      · rw [zero_pow h1]; simp
  | add p q hp hq => simp [hp, hq]

open MvPolynomial in
/-- The `t⁴` coefficient of the fixed-height curve. -/
private theorem wCurve_coeff (Δ z n3 ni nj s3 w : ℤ) :
    (wCurve Δ z n3 ni nj s3 w).coeff (Finsupp.single 0 4) = (Δ * (n3 + 2 * w)) ^ 2 := by
  rw [← coeff_tPart2]
  set u := s3 * z
  set a := -Δ * (n3 + 2 * w)
  set b := -2 * Δ * n3 * u
  set c := -Δ * n3 * u ^ 2 - 2 * n3 ^ 2 * w
  have key : tPart2 (wCurve Δ z n3 ni nj s3 w) =
      Polynomial.C (a ^ 2) * Polynomial.X ^ 4 + Polynomial.C (2 * a * b) * Polynomial.X ^ 3 +
      Polynomial.C (b ^ 2 + 2 * a * c - 4 * nj ^ 2 * Δ * (n3 + w) ^ 2) * Polynomial.X ^ 2 +
      Polynomial.C (2 * b * c - 8 * nj ^ 2 * Δ * (n3 + w) * n3 * u) * Polynomial.X +
      Polynomial.C (c ^ 2 + 4 * n3 ^ 2 * nj ^ 2 * w ^ 2 - 4 * nj ^ 2 * Δ * n3 ^ 2 * u ^ 2) := by
    simp only [wCurve, Lm, NXm, tPart2, map_add, map_sub, map_mul, map_pow, map_neg, aeval_C,
      aeval_X, map_ofNat, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Fin.isValue, ↓reduceIte, one_ne_zero, a, b, c, u]
    ring
  rw [key]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C]
  norm_num
  simp only [a]
  ring

open MvPolynomial in
/-- The fixed-height curve has total degree exactly 4 off `n₃ + 2w = 0`. -/
private theorem wCurve_totalDegree (Δ z n3 ni nj s3 w : ℤ) (hΔ : Δ ≠ 0)
    (hw : n3 + 2 * w ≠ 0) :
    (wCurve Δ z n3 ni nj s3 w).totalDegree = 4 := by
  refine le_antisymm (wCurve_totalDegree_le _ _ _ _ _ _ _) ?_
  have hmem : Finsupp.single 0 4 ∈ (wCurve Δ z n3 ni nj s3 w).support := by
    rw [mem_support_iff, wCurve_coeff]; exact pow_ne_zero 2 (mul_ne_zero hΔ hw)
  have := le_totalDegree hmem
  simpa using this

/-- `𝔗 ≥ B⁴` for the square box of side `B`. -/
private theorem wCurve_boxSize (Δ z n3 ni nj s3 w : ℤ) (hΔ : Δ ≠ 0) (hw : n3 + 2 * w ≠ 0)
    (B : ℝ) : B ^ 4 ≤ boxSize (wCurve Δ z n3 ni nj s3 w) (fun _ => B) := by
  have hmem : Finsupp.single 0 4 ∈ (wCurve Δ z n3 ni nj s3 w).support := by
    rw [MvPolynomial.mem_support_iff, wCurve_coeff]; exact pow_ne_zero 2 (mul_ne_zero hΔ hw)
  unfold boxSize
  refine le_csSup ((Set.Finite.image _ (Finset.finite_toSet _)).bddAbove) ⟨_, hmem, ?_⟩
  simp [Fin.prod_univ_two]

open Polynomial in
/-- Irreducibility transfers along the triangular change `k ↦ α(Y + φ(t))`. -/
private theorem irred_of_shear {K : Type*} [_root_.Field K] (α : K) (hα : α ≠ 0) (φ : K[X])
    (G : MvPolynomial (Fin 2) K)
    (h : Irreducible (MvPolynomial.eval₂Hom (C.comp C) (![C X, C (C α) * (X + C φ)]) G)) :
    Irreducible G := by
  set Φ : MvPolynomial (Fin 2) K →+* K[X][X] :=
    MvPolynomial.eval₂Hom (C.comp C) (![C X, C (C α) * (X + C φ)]) with hΦ
  set ψ0 : K[X] →+* MvPolynomial (Fin 2) K :=
    Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0) with hψ0
  set Ψ : K[X][X] →+* MvPolynomial (Fin 2) K :=
    Polynomial.eval₂RingHom ψ0 (MvPolynomial.C α⁻¹ * MvPolynomial.X 1 - ψ0 φ) with hΨ
  have hΦψ0 : ∀ p : K[X], Φ (ψ0 p) = C p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | monomial n a => simp [ψ0, Φ, ← C_mul_X_pow_eq_monomial]
  have h1 : Φ.comp Ψ = RingHom.id _ := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a; simp [Ψ, Φ, ψ0]
      · simp [Ψ, Φ, ψ0]
    · simp only [RingHom.comp_apply, Ψ, coe_eval₂RingHom, eval₂_X, map_sub, map_mul, hΦψ0,
        RingHom.id_apply]
      simp only [Φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
        RingHom.comp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hα, map_one, map_one, one_mul]
      ring
  have h2 : Ψ.comp Φ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [Ψ, Φ, ψ0]
    · intro i
      fin_cases i
      · simp [Ψ, Φ, ψ0]
      · simp only [RingHom.comp_apply, Φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, map_mul,
          map_add, RingHom.id_apply, Ψ, coe_eval₂RingHom, eval₂_C, eval₂_X]
        have : ψ0 (C α) = MvPolynomial.C α := by simp [ψ0]
        rw [this, sub_add_cancel, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
  exact (MulEquiv.irreducible_iff (RingEquiv.ofRingHom Φ Ψ h1 h2)).mp h

open Polynomial in
/-- If `Y² − P_w` is irreducible over `ℚ̄[t]`, the fixed-height curve is absolutely
irreducible. -/
private theorem wCurve_absIrred (Δ z n3 ni nj s3 w : ℤ) (hn3 : n3 ≠ 0) (hnj : nj ≠ 0)
    (h : Irreducible ((X : (AlgebraicClosure ℚ)[X][X]) ^ 2 - C (((Pp Δ z n3 ni nj s3 w).map
      (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))))) :
    AbsIrred (wCurve Δ z n3 ni nj s3 w) := by
  set K := AlgebraicClosure ℚ
  set ι := Int.castRingHom K
  have hmap : ((Pp Δ z n3 ni nj s3 w).map (Int.castRingHom ℚ)).map (algebraMap ℚ K) =
      (Pp Δ z n3 ni nj s3 w).map ι := by
    rw [Polynomial.map_map]; congr 1
  rw [hmap] at h
  have hh : ((ni ^ 2 + nj ^ 2 : ℤ) : K) ≠ 0 := by
    have : ni ^ 2 + nj ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  have hc1 : ((2 * n3 * (ni ^ 2 + nj ^ 2) : ℤ) : K) ≠ 0 := by
    have : 2 * n3 * (ni ^ 2 + nj ^ 2) ≠ 0 := by positivity
    exact_mod_cast this
  set α : K := ((2 * n3 * (ni ^ 2 + nj ^ 2) : ℤ) : K)⁻¹
  set ℓ : K[X] := (Lp Δ z n3 s3 w).map ι
  set ν : K[X] := (NXp z n3 s3 w).map ι
  set Φ : MvPolynomial (Fin 2) K →+* K[X][X] :=
    MvPolynomial.eval₂Hom (C.comp C) (![C X, C (C α) * (X + C (C (ι ni) * ℓ))])
  have hL : Φ (MvPolynomial.map ι (Lm Δ z n3 s3 w)) = C ℓ := by
    simp only [Φ, ℓ, Lm, Lp, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
      MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_X, RingHom.comp_apply, Matrix.cons_val_zero, Polynomial.map_mul,
      Polynomial.map_add, Polynomial.map_sub, Polynomial.map_neg, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat]
  have hN : Φ (MvPolynomial.map ι (NXm z n3 s3 w)) = C ν := by
    simp only [Φ, ν, NXm, NXp, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, RingHom.comp_apply,
      Matrix.cons_val_zero, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
      Polynomial.map_X]
  have hA : C (C α) * C (C (ι (2 * n3 * (ni ^ 2 + nj ^ 2)))) = (1 : K[X][X]) := by
    rw [← map_mul, ← map_mul, eq_intCast, inv_mul_cancel₀ hc1, map_one, map_one]
  have key : Φ (MvPolynomial.map ι (wCurve Δ z n3 ni nj s3 w)) *
      C (C (ι (ni ^ 2 + nj ^ 2))) = X ^ 2 - C ((Pp Δ z n3 ni nj s3 w).map ι) := by
    simp only [wCurve, map_add, map_sub, map_mul, map_pow, hL, hN]
    simp only [Φ, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, RingHom.comp_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, Pp, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_neg, Polynomial.map_pow, Polynomial.map_C]
    rw [show (Lp Δ z n3 s3 w).map ι = ℓ from rfl, show (NXp z n3 s3 w).map ι = ν from rfl]
    simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_neg] at hA ⊢
    linear_combination (X + C (C (ι ni)) * C ℓ) *
      (C (C α) * (2 * C (C (ι n3)) * (C (C (ι ni)) ^ 2 + C (C (ι nj)) ^ 2)) *
        (X + C (C (ι ni)) * C ℓ) - C (C (ι ni)) * C ℓ + X) * hA
  have hu : IsUnit (C (C (ι (ni ^ 2 + nj ^ 2))) : K[X][X]) :=
    isUnit_C.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by simpa using hh)))
  rw [← key] at h
  exact irred_of_shear α (inv_ne_zero hc1) (C (ι ni) * ℓ) _ ((irreducible_mul_isUnit hu).mp h)

open Polynomial in
/-- In the square case `P_w = cR²` (`c < 0`) the curve has at most two integer zeros. -/
private theorem wCurve_sq_count (Δ z n3 ni nj s3 w : ℤ) (hΔ : Δ ≠ 0) (hn3 : n3 ≠ 0)
    (hnj : nj ≠ 0) (hw : n3 + 2 * w ≠ 0) (c : ℚ) (R : ℚ[X])
    (hcR : (Pp Δ z n3 ni nj s3 w).map (Int.castRingHom ℚ) = C c * R ^ 2) (B : Fin 2 → ℝ) :
    (boxZeros (wCurve Δ z n3 ni nj s3 w) B).card ≤ 2 := by
  classical
  obtain ⟨hdeg, hcoef⟩ := Pp_natDegree Δ z n3 ni nj s3 w hΔ hnj hw
  set Pq := (Pp Δ z n3 ni nj s3 w).map (Int.castRingHom ℚ) with hPq
  have hdegq : Pq.natDegree = 4 := by
    rw [hPq, natDegree_map_eq_of_injective (RingHom.injective_int _), hdeg]
  have hcoefq : Pq.coeff 4 < 0 := by
    rw [hPq, coeff_map, hcoef]
    have hne := mul_ne_zero (pow_ne_zero 2 (mul_ne_zero hΔ hw)) (pow_ne_zero 2 hnj)
    have : 0 < (Δ * (n3 + 2 * w)) ^ 2 * nj ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hne)
    have : -nj ^ 2 * (Δ * (n3 + 2 * w)) ^ 2 < 0 := by linarith
    simpa using (Int.cast_lt (R := ℚ)).mpr this
  have hc0 : c ≠ 0 := by rintro rfl; rw [hcR] at hdegq; simp at hdegq
  have hR0 : R ≠ 0 := by rintro rfl; rw [hcR] at hdegq; simp at hdegq
  have hRdeg : R.natDegree = 2 := by
    rw [hcR, natDegree_C_mul hc0, natDegree_pow] at hdegq; omega
  have hc : c < 0 := by
    rw [hcR, coeff_C_mul, show 4 = (R ^ 2).natDegree by rw [natDegree_pow, hRdeg],
      coeff_natDegree, leadingCoeff_pow] at hcoefq
    have : 0 < R.leadingCoeff ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hR0)))
    nlinarith
  have hpt : ∀ x ∈ boxZeros (wCurve Δ z n3 ni nj s3 w) B,
      2 * n3 * (ni ^ 2 + nj ^ 2) * x 1 - ni * (Lp Δ z n3 s3 w).eval (x 0) = 0 ∧
        R.eval ((x 0 : ℤ) : ℚ) = 0 := by
    intro x hx
    simp only [boxZeros, Finset.mem_filter] at hx
    have h1 := wCurve_eval Δ z n3 ni nj s3 w x
    rw [hx.2, mul_zero] at h1
    set Y := 2 * n3 * (ni ^ 2 + nj ^ 2) * x 1 - ni * (Lp Δ z n3 s3 w).eval (x 0)
    have h2 : ((Y : ℤ) : ℚ) ^ 2 = c * (R.eval ((x 0 : ℤ) : ℚ)) ^ 2 := by
      have h3 : ((Y ^ 2 : ℤ) : ℚ) = (((Pp Δ z n3 ni nj s3 w).eval (x 0) : ℤ) : ℚ) := by
        congr 1; linarith
      have h4 := eval_intCast_map (Int.castRingHom ℚ) (Pp Δ z n3 ni nj s3 w) (x 0)
      simp only [eq_intCast, Int.cast_id] at h4
      rw [← h4, ← hPq, hcR] at h3
      simpa [eval_mul, eval_pow] using h3
    have hY : ((Y : ℤ) : ℚ) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((Y : ℤ) : ℚ), sq_nonneg (R.eval ((x 0 : ℤ) : ℚ))]
    have hR : c * (R.eval ((x 0 : ℤ) : ℚ)) ^ 2 = 0 := by rw [← h2, hY]
    have hY0 : ((Y : ℤ) : ℚ) = 0 := (pow_eq_zero_iff two_ne_zero).mp hY
    refine ⟨by exact_mod_cast hY0, ?_⟩
    rcases mul_eq_zero.mp hR with h | h
    · exact absurd h hc0
    · exact (pow_eq_zero_iff two_ne_zero).mp h
  have hmaps : ∀ x ∈ boxZeros (wCurve Δ z n3 ni nj s3 w) B,
      ((x 0 : ℤ) : ℚ) ∈ R.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hR0]
    exact (hpt x hx).2
  have hinj : Set.InjOn (fun x : Fin 2 → ℤ => ((x 0 : ℤ) : ℚ))
      (boxZeros (wCurve Δ z n3 ni nj s3 w) B) := by
    intro x hx y hy hxy
    have h0 : x 0 = y 0 := by simpa using hxy
    have hx1 := (hpt x hx).1
    have hy1 := (hpt y hy).1
    rw [h0] at hx1
    have hne : 2 * n3 * (ni ^ 2 + nj ^ 2) ≠ 0 := by positivity
    have h1 : x 1 = y 1 := by
      have : 2 * n3 * (ni ^ 2 + nj ^ 2) * (x 1 - y 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hne
      · linarith
    funext i; fin_cases i
    · exact h0
    · exact h1
  calc (boxZeros (wCurve Δ z n3 ni nj s3 w) B).card ≤ R.roots.toFinset.card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ Multiset.card R.roots := Multiset.toFinset_card_le _
    _ ≤ R.natDegree := card_roots' R
    _ = 2 := hRdeg

/-- The fixed-height plane curve has `≤ C B^{1/4+η} + 2` zeros in the square box of side `B`. -/
private theorem curve_count (hP : PlaneCurveCount) (η : ℝ) (hη : 0 < η) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Δ z n3 ni nj s3 w : ℤ), Δ ≠ 0 → n3 ≠ 0 → nj ≠ 0 → n3 + 2 * w ≠ 0 → ∀ B : ℝ, 2 ≤ B →
      ((boxZeros (wCurve Δ z n3 ni nj s3 w) (fun _ => B)).card : ℝ) ≤
        C * B ^ ((1 : ℝ) / 4 + η) + 2 := by
  obtain ⟨C4, hC4⟩ := hP 4 η (by norm_num) hη
  refine ⟨max C4 0, le_max_right _ _, ?_⟩
  intro Δ z n3 ni nj s3 w hΔ hn3 hnj hw B hB
  have hBpos : 0 < B := by linarith
  have hpos : 0 ≤ max C4 0 * B ^ ((1 : ℝ) / 4 + η) :=
    mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hBpos.le _)
  obtain ⟨hdeg, -⟩ := Pp_natDegree Δ z n3 ni nj s3 w hΔ hnj hw
  have hdq : 0 < ((Pp Δ z n3 ni nj s3 w).map (Int.castRingHom ℚ)).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _), hdeg]; norm_num
  rcases sq_or_absIrred _ hdq with hirr | ⟨c, R, hcR⟩
  · have habs := wCurve_absIrred Δ z n3 ni nj s3 w hn3 hnj hirr
    have h := hC4 _ (wCurve_totalDegree Δ z n3 ni nj s3 w hΔ hw) habs (fun _ => B) hB le_rfl
    have hT := wCurve_boxSize Δ z n3 ni nj s3 w hΔ hw B
    have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
    have hB4 : 0 < B ^ 4 := by positivity
    have hlogT : 4 * Real.log B ≤ Real.log (boxSize (wCurve Δ z n3 ni nj s3 w) fun _ => B) := by
      have := Real.log_le_log hB4 hT
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    have hexp : Real.exp (Real.log B * Real.log B /
        Real.log (boxSize (wCurve Δ z n3 ni nj s3 w) fun _ => B)) ≤ B ^ ((1 : ℝ) / 4) := by
      rw [Real.rpow_def_of_pos hBpos]
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hBη : 0 ≤ B ^ η := Real.rpow_nonneg hBpos.le _
    calc ((boxZeros (wCurve Δ z n3 ni nj s3 w) (fun _ => B)).card : ℝ)
        ≤ C4 * B ^ η * Real.exp (Real.log B * Real.log B /
            Real.log (boxSize (wCurve Δ z n3 ni nj s3 w) fun _ => B)) := h
      _ ≤ max C4 0 * B ^ η * B ^ ((1 : ℝ) / 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hBη) hexp
          (Real.exp_pos _).le (mul_nonneg (le_max_right _ _) hBη)
      _ = max C4 0 * B ^ ((1 : ℝ) / 4 + η) := by
        rw [mul_assoc, ← Real.rpow_add hBpos, add_comm η]
      _ ≤ _ := by linarith
  · have := wCurve_sq_count Δ z n3 ni nj s3 w hΔ hn3 hnj hw c R hcR (fun _ => B)
    have h2 : ((boxZeros (wCurve Δ z n3 ni nj s3 w) (fun _ => B)).card : ℝ) ≤ 2 := by
      exact_mod_cast this
    linarith

open MvPolynomial

/-- Keep the pure-`t` part: `t ↦ X`, other variables `↦ 0`. -/
private noncomputable def tPart : MvPolynomial (Fin 3) ℤ →ₐ[ℤ] Polynomial ℤ :=
  aeval fun i => if i = 0 then Polynomial.X else 0

/-- `tPart` reads off the pure-`t` coefficients. -/
private theorem coeff_tPart (p : MvPolynomial (Fin 3) ℤ) (a : ℕ) :
    (tPart p).coeff a = p.coeff (Finsupp.single 0 a) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
    simp only [tPart, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_three, coeff_monomial]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, Fin.reduceEq]
    by_cases h : m = Finsupp.single 0 a
    · subst h; simp
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
      have hm : ¬ (m 0 = a ∧ m 1 = 0 ∧ m 2 = 0) := by
        rintro ⟨h0, h1, h2⟩
        apply h
        ext i
        fin_cases i <;> simp [h0, h1, h2]
      by_cases h12 : m 1 = 0 ∧ m 2 = 0
      · rw [h12.1, h12.2]
        rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Polynomial.coeff_C_mul, pow_zero, mul_one, mul_one, Polynomial.coeff_X_pow]
        simp [show a ≠ m 0 from fun h' => hm ⟨h'.symm, h12⟩]
      · rcases not_and_or.mp h12 with h1 | h2
        · rw [zero_pow h1]; simp
        · rw [zero_pow h2]; simp
  | add p q hp hq => simp [hp, hq]

/-- C1: `t⁴` coefficient of `Ψ(t, w₀, k)`. -/
theorem Psi_t4 (Δ z n3 ni nj s3 w0 : ℤ) :
    ((Psi Δ z n3 ni nj s3).eval₂ C (fun i => if i = 1 then C w0 else X i)).coeff
      (Finsupp.single 0 4) =
      Δ ^ 2 * (n3 + 2 * w0) ^ 2 := by
  rw [← coeff_tPart]
  set u := s3 * z
  set a := -Δ * (n3 + 2 * w0)
  set b := -2 * Δ * n3 * u
  set c := -Δ * n3 * u ^ 2 - 2 * n3 ^ 2 * w0
  have key : tPart ((Psi Δ z n3 ni nj s3).eval₂ C (fun i => if i = 1 then C w0 else X i)) =
      Polynomial.C (a ^ 2) * Polynomial.X ^ 4 + Polynomial.C (2 * a * b) * Polynomial.X ^ 3 +
      Polynomial.C (b ^ 2 + 2 * a * c - 4 * nj ^ 2 * Δ * (n3 + w0) ^ 2) * Polynomial.X ^ 2 +
      Polynomial.C (2 * b * c - 8 * nj ^ 2 * Δ * (n3 + w0) * n3 * u) * Polynomial.X +
      Polynomial.C (c ^ 2 + 4 * n3 ^ 2 * nj ^ 2 * w0 ^ 2 - 4 * nj ^ 2 * Δ * n3 ^ 2 * u ^ 2) := by
    simp only [Psi, tPart, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_neg, eval₂_C,
      eval₂_X, eval₂_ofNat, map_add, map_sub, map_mul, map_pow, map_neg, aeval_C, aeval_X,
      map_ofNat, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Fin.isValue, Fin.reduceEq, ↓reduceIte, a, b, c, u]
    ring
  rw [key]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C]
  norm_num
  simp only [a]
  ring

/-- Unpacking membership in the sorted fibre. -/
private theorem mem_sortedFibre' {n m k : Mode} (hp : (m, k) ∈ sortedFibre n) :
    m + k + n = 0 ∧ nsqZ m ≤ nsqZ k ∧ nsqZ k ≤ nsqZ n ∧ m 2 ≠ 0 ∧ k 2 ≠ 0 ∧ n 2 ≠ 0 := by
  classical
  simp only [sortedFibre, Finset.mem_filter] at hp
  convert hp.2

/-- Uniqueness of the squarefree part. -/
private theorem sqfree_unique {a b x y : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hx : x ≠ 0) (hy : y ≠ 0) (h : a * x ^ 2 = b * y ^ 2) : a = b := by
  have ha0 := ha.ne_zero
  have hb0 := hb.ne_zero
  apply Nat.eq_of_factorization_eq ha0 hb0
  intro p
  have := congrArg (fun m => m.factorization p) h
  simp only [Nat.factorization_mul ha0 (pow_ne_zero 2 hx),
    Nat.factorization_mul hb0 (pow_ne_zero 2 hy), Nat.factorization_pow, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul] at this
  have h1 := (Nat.squarefree_iff_factorization_le_one ha0).mp ha p
  have h2 := (Nat.squarefree_iff_factorization_le_one hb0).mp hb p
  omega

/-- `xOf` recovers `x` from `|k|² = Δ x²`. -/
private theorem xOf_eq {Δ x : ℕ} {k : Mode} (hΔ : 0 < Δ) (h : nsqZ k = Δ * x ^ 2) :
    xOf Δ k = x := by
  simp only [xOf, h]
  rw [show ((Δ : ℤ) * (x : ℤ) ^ 2) = ((Δ * x ^ 2 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast,
    Nat.mul_div_cancel_left _ hΔ, Nat.sqrt_eq']

/-- A mode with nonzero vertical component has positive squared norm. -/
private theorem nsqZ_pos {l : Mode} (hl : l 2 ≠ 0) : 0 < nsqZ l := by
  simp only [nsqZ, Fin.sum_univ_three]
  nlinarith [sq_nonneg (l 0), sq_nonneg (l 1), pow_pos (abs_pos.mpr hl) 2, sq_abs (l 2)]

/-- Integer coordinates of an active point, normalized to the given `Δ` and `|z|`. -/
private theorem coords_of_active {n k : Mode} {s2 s3 : ℤ} {Δ : ℕ} {z : ℤ} (hΔ : Squarefree Δ)
    (hn : nsqZ n = Δ * z ^ 2) (hk : k ∈ activePts n s2 s3) :
    ∃ c : Coords n k, c.Δ = Δ ∧ c.z = |z| ∧ c.s2 = s2 ∧ c.s3 = s3 ∧ c.t = tOf Δ s2 n k ∧
      ∃ a b e : Sgn, sgZ a * sgZ b = s2 ∧ sgZ e * sgZ b = s3 ∧
        phase3 a b e (-k - n) k n = 0 ∧ gammaCoef a b e (-k - n) k n ≠ 0 := by
  classical
  simp only [activePts, Finset.mem_filter] at hk
  obtain ⟨_, hsf, a, b, e, hs2, hs3, hph, hγ⟩ := hk
  obtain ⟨_, _, _, hm3, hk3, hn3⟩ := mem_sortedFibre' hsf
  obtain ⟨Δ', x, y, z', hΔ', hkx, hmy, hnz, hy, hyx, hxz, hres⟩ := exists_coords hsf hph
  have hpos := nsqZ_pos hn3
  have hz' : z' ≠ 0 := by rintro rfl; rw [hnz] at hpos; simp at hpos
  have hz0 : z.natAbs ≠ 0 := by
    intro h0; rw [Int.natAbs_eq_zero.mp h0] at hn; rw [hn] at hpos; simp at hpos
  have hEq : Δ' * z' ^ 2 = Δ * z.natAbs ^ 2 := by
    have : ((Δ' * z' ^ 2 : ℕ) : ℤ) = ((Δ * z.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [sq_abs, ← hn, hnz]
    exact_mod_cast this
  have hΔΔ : Δ' = Δ := sqfree_unique hΔ' hΔ hz' hz0 hEq
  subst hΔΔ
  have hzz : z' = z.natAbs := by
    have h2 : z' ^ 2 = z.natAbs ^ 2 := Nat.eq_of_mul_eq_mul_left hΔ.ne_zero.bot_lt hEq
    exact Nat.pow_left_injective (by norm_num) h2
  have hΔ0 : 0 < Δ' := hΔ.ne_zero.bot_lt
  let hc : Coords n k :=
    { Δ := Δ', x := x, y := y, z := z', s2 := s2, s3 := s3
      hΔ := (by exact_mod_cast hΔ0)
      hy := (by exact_mod_cast hy)
      hyx := (by exact_mod_cast hyx)
      hxz := (by exact_mod_cast hxz)
      hs2 := (by subst hs2; cases a <;> cases b <;> simp [sgZ])
      hs3 := (by subst hs3; cases e <;> cases b <;> simp [sgZ])
      hk := hkx
      hm := hmy
      hn := hnz
      hres := (by rw [← hs2, ← hs3]; exact hres)
      hk3 := hk3
      hm3 := hm3
      hn3 := hn3 }
  refine ⟨hc, rfl, ?_, rfl, rfl, ?_, a, b, e, hs2, hs3, hph, hγ⟩
  · show ((z' : ℕ) : ℤ) = |z|
    rw [hzz, Int.natCast_natAbs]
  · simp only [Coords.t, tOf, xOf_eq hΔ0 hkx, xOf_eq hΔ0 hmy]
    rfl

/-- Evaluation of the fixed-height curve at an actual point vanishes. -/
private theorem wCurve_eval_zero (Δ z n3 ni nj s3 w t ki kj L x : ℤ)
    (hL : 2 * n3 * L = -Δ * n3 * (t + s3 * z) ^ 2 - 2 * (n3 ^ 2 + Δ * t ^ 2) * w)
    (hx : n3 * x = n3 * (t + s3 * z) + t * w) (hLk : L = ni * ki + nj * kj)
    (hk : ki ^ 2 + kj ^ 2 + w ^ 2 = Δ * x ^ 2) :
    eval ![t, ki] (wCurve Δ z n3 ni nj s3 w) = 0 := by
  simp only [wCurve, Lm, NXm, map_add, map_sub, map_mul, map_neg, map_pow, eval_C, eval_X,
    map_ofNat, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (-((-Δ * n3 * (t + s3 * z) ^ 2 - 2 * (n3 ^ 2 + Δ * t ^ 2) * w) +
      2 * n3 * L - 2 * (2 * n3 * ni * ki))) * hL +
    4 * nj ^ 2 * Δ * (n3 * x + (n3 * (t + s3 * z) + t * w)) * hx +
    2 * n3 * (2 * n3 * L - 2 * n3 * ni * ki + 2 * n3 * nj * kj) * hLk +
    4 * n3 ^ 2 * nj ^ 2 * hk

/-- An equilateral triad has `γ = 0`. -/
private theorem gamma_eq_zero_of_eq {a b e : Sgn} {m k n : Mode} (h1 : absk m = absk k)
    (h2 : absk k = absk n) : gammaCoef a b e m k n = 0 := by
  simp only [gammaCoef]
  rw [h1, h2]
  cases a <;> cases b <;> cases e <;> simp [sg]

/-- Facts on an active point: `t > 0`, `n₃ + 2w ≠ 0` (A8), `n_h ≠ 0` (A1). -/
private theorem active_facts {n k : Mode} (c : Coords n k) {a b e : Sgn}
    (hsf : (-k - n, k) ∈ sortedFibre n) (hph : phase3 a b e (-k - n) k n = 0)
    (hγ : gammaCoef a b e (-k - n) k n ≠ 0) :
    0 < c.t ∧ n 2 + 2 * k 2 ≠ 0 ∧ (n 0 ≠ 0 ∨ n 1 ≠ 0) := by
  have heq : c.t ≠ 0 := by
    intro h0
    obtain ⟨hxy, hyz⟩ := c.t_eq_zero h0
    apply hγ
    apply gamma_eq_zero_of_eq
    · rw [absk_eq_sqrt_nsqZ, absk_eq_sqrt_nsqZ, c.hm, c.hk, hxy]
    · rw [absk_eq_sqrt_nsqZ, absk_eq_sqrt_nsqZ, c.hk, c.hn, hxy, hyz]
  refine ⟨lt_of_le_of_ne c.t_nonneg (Ne.symm heq), ?_, ?_⟩
  · intro hw
    have hx := c.x_id
    simp only [Coords.w] at hx
    have h2 : n 2 * (2 * c.x) = n 2 * (c.t + 2 * c.s3 * c.z) := by
      linear_combination 2 * hx + c.t * hw
    have h3 : 2 * c.x = c.t + 2 * c.s3 * c.z := mul_left_cancel₀ c.hn3 h2
    have := c.hy; have := c.hyx; have := c.hxz; have := c.t_lt; have := c.t_nonneg
    rcases c.hs3 with h | h <;> rw [h] at h3
    · exact heq (by linarith)
    · linarith
  · by_contra hcon
    obtain ⟨h0, h1⟩ := not_or.mp hcon
    exact hγ (vertical_output_null (not_not.mp h0) (not_not.mp h1) hsf hph)

/-- An integer of absolute value `≤ B` lies in `[-⌊B⌋, ⌊B⌋]`. -/
private theorem mem_Icc_floor {a : ℤ} {B : ℝ} (h : |(a : ℝ)| ≤ B) :
    a ∈ Finset.Icc (-⌊B⌋) ⌊B⌋ := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  refine Finset.mem_Icc.mpr ⟨?_, Int.le_floor.mpr h2⟩
  have : -a ≤ ⌊B⌋ := Int.le_floor.mpr (by push_cast; linarith)
  omega

/-- The point `(t, k_i)` of an active `k` lies in the box of side `max 2 (2|n|)`. -/
private theorem pt_mem_box {n k : Mode} {Δ z : ℕ} (hn : nsqZ n = Δ * z ^ 2) (hΔ : 0 < Δ)
    {t : ℤ} (ht0 : 0 ≤ t) (htz : t < 2 * z) (i : Fin 3) (hkn : nsqZ k ≤ nsqZ n) :
    ![t, k i] ∈ boxPts 2 (fun _ => max 2 (2 * absk n)) := by
  have hz : (z : ℝ) ≤ absk n := by
    rw [absk_eq_sqrt_nsqZ, hn]
    apply Real.le_sqrt_of_sq_le
    push_cast
    have : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    nlinarith [sq_nonneg (z : ℝ)]
  have hki : |((k i : ℤ) : ℝ)| ≤ absk n := by
    rw [absk_eq_sqrt_nsqZ]
    apply Real.abs_le_sqrt
    have : k i ^ 2 ≤ nsqZ k := by
      simp only [nsqZ, Fin.sum_univ_three]
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2)]
    exact_mod_cast this.trans hkn
  simp only [boxPts, Fintype.mem_piFinset]
  intro j
  fin_cases j
  · apply mem_Icc_floor
    rw [abs_of_nonneg (by exact_mod_cast ht0)]
    have : (t : ℝ) ≤ 2 * z := by exact_mod_cast htz.le
    exact this.trans ((by linarith : (2 : ℝ) * z ≤ 2 * absk n).trans (le_max_right _ _))
  · apply mem_Icc_floor
    exact hki.trans ((by linarith [absk_nonneg n] : absk n ≤ 2 * absk n).trans (le_max_right _ _))

/-- A choice of horizontal indices `(i, j)` with `n_j ≠ 0`. -/
private theorem exists_ij {n : Mode} (hnh : n 0 ≠ 0 ∨ n 1 ≠ 0) :
    ∃ i0 j0 : Fin 3, n j0 ≠ 0 ∧
      (∀ k : Mode, n 0 * k 0 + n 1 * k 1 = n i0 * k i0 + n j0 * k j0 ∧
        k 0 ^ 2 + k 1 ^ 2 = k i0 ^ 2 + k j0 ^ 2) ∧
      ∀ k k' : Mode, k i0 = k' i0 → k j0 = k' j0 → k 2 = k' 2 → k = k' := by
  by_cases h1 : n 1 ≠ 0
  · refine ⟨0, 1, h1, fun k => ⟨rfl, rfl⟩, fun k k' h0 h1 h2 => ?_⟩
    funext i; fin_cases i <;> assumption
  · have h0 : n 0 ≠ 0 := hnh.resolve_right h1
    refine ⟨1, 0, h0, fun k => ⟨by ring, by ring⟩, fun k k' h1 h0 h2 => ?_⟩
    funext i; fin_cases i <;> assumption

/-- C5: fixed height `w = k₃`. -/
theorem fixed_w_count (hP : PlaneCurveCount) : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (w s2 s3 : ℤ),
      (((activePts n s2 s3).filter fun k => k 2 = w).card : ℝ) ≤
        C * max 2 (2 * absk n) ^ ((1 : ℝ) / 4 + η) + 2 := by
  intro η hη
  obtain ⟨C, hC0, hC⟩ := curve_count hP η hη
  refine ⟨C, hC0, ?_⟩
  intro n w s2 s3
  classical
  set B := max 2 (2 * absk n) with hBdef
  have hB : 2 ≤ B := le_max_left _ _
  have hpos : 0 ≤ C * B ^ ((1 : ℝ) / 4 + η) := mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _)
  set A := (activePts n s2 s3).filter fun k => k 2 = w with hAdef
  rcases A.eq_empty_or_nonempty with hA | ⟨k₀, hk₀⟩
  · rw [hA, Finset.card_empty, Nat.cast_zero]; linarith
  have hk₀' := (Finset.mem_filter.mp hk₀).1
  obtain ⟨Δ, z, hΔ, hn⟩ : ∃ Δ z : ℕ, Squarefree Δ ∧ nsqZ n = Δ * z ^ 2 := by
    simp only [activePts, Finset.mem_filter] at hk₀'
    obtain ⟨_, hsf, a, b, e, -, -, hph, -⟩ := hk₀'
    obtain ⟨Δ, x, y, z, hΔ, -, -, hn, -⟩ := exists_coords hsf hph
    exact ⟨Δ, z, hΔ, hn⟩
  have hΔ0 : 0 < Δ := hΔ.ne_zero.bot_lt
  have hsf : ∀ k ∈ (activePts n s2 s3), (-k - n, k) ∈ sortedFibre n := by
    intro k hk
    simp only [activePts, Finset.mem_filter] at hk
    exact hk.2.1
  obtain ⟨c₀, -, -, -, -, -, a, b, e, -, -, hph, hγ⟩ := coords_of_active hΔ hn hk₀'
  obtain ⟨-, hw0, hnh⟩ := active_facts c₀ (hsf _ hk₀') hph hγ
  have hw : n 2 + 2 * w ≠ 0 := by rw [← (Finset.mem_filter.mp hk₀).2]; exact hw0
  obtain ⟨i0, j0, hnj, hLk, hinj⟩ := exists_ij hnh
  have hn3 : n 2 ≠ 0 := c₀.hn3
  -- data of each point
  have hdata : ∀ k ∈ A, ∃ L x : ℤ,
      2 * n 2 * L = -Δ * n 2 * (tOf Δ s2 n k + s3 * z) ^ 2 -
        2 * (n 2 ^ 2 + Δ * tOf Δ s2 n k ^ 2) * w ∧
      n 2 * x = n 2 * (tOf Δ s2 n k + s3 * z) + tOf Δ s2 n k * w ∧
      L = n i0 * k i0 + n j0 * k j0 ∧ k i0 ^ 2 + k j0 ^ 2 + w ^ 2 = Δ * x ^ 2 ∧
      0 ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k < 2 * z ∧ nsqZ k ≤ nsqZ n := by
    intro k hk
    obtain ⟨hk, hkw⟩ := Finset.mem_filter.mp hk
    obtain ⟨c, hcΔ, hcz, -, hcs3, hct, -⟩ := coords_of_active hΔ hn hk
    rw [abs_of_nonneg (Int.natCast_nonneg z)] at hcz
    have hcw : c.w = w := hkw
    refine ⟨c.L, c.x, ?_, ?_, ?_, ?_, ?_, ?_, (mem_sortedFibre' (hsf k hk)).2.2.1⟩
    · have := c.L_id; rwa [hcΔ, hcz, hcs3, hct, hcw] at this
    · have := c.x_id; rwa [hcz, hcs3, hct, hcw] at this
    · rw [← (hLk k).1]; rfl
    · have := c.hk
      simp only [nsqZ, Fin.sum_univ_three] at this
      rw [← (hLk k).2, ← hkw, ← hcΔ]; linarith
    · rw [← hct]; exact c.t_nonneg
    · rw [← hct, ← hcz]; exact c.t_lt
  have hmaps : ∀ k ∈ A, ![tOf Δ s2 n k, k i0] ∈
      boxZeros (wCurve Δ z (n 2) (n i0) (n j0) s3 w) (fun _ => B) := by
    intro k hk
    obtain ⟨L, x, hL, hx, hLk', hk2, ht0, htz, hkn⟩ := hdata k hk
    simp only [boxZeros, Finset.mem_filter]
    exact ⟨pt_mem_box hn hΔ0 ht0 htz i0 hkn,
      wCurve_eval_zero _ _ _ _ _ _ _ _ _ _ L x hL hx hLk' hk2⟩
  have hinjOn : Set.InjOn (fun k : Mode => ![tOf Δ s2 n k, k i0]) A := by
    intro k hk k' hk' heq
    have ht : tOf Δ s2 n k = tOf Δ s2 n k' := by simpa using congrFun heq 0
    have hi : k i0 = k' i0 := by simpa using congrFun heq 1
    obtain ⟨L, x, hL, -, hLk', -⟩ := hdata k hk
    obtain ⟨L', x', hL', -, hLk'', -⟩ := hdata k' hk'
    rw [ht] at hL
    have hLL : L = L' := by
      have : 2 * n 2 * (L - L') = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · linarith
    have hj : k j0 = k' j0 := by
      have : n j0 * (k j0 - k' j0) = 0 := by rw [← hi] at hLk''; linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hnj
      · linarith
    exact hinj k k' hi hj (by rw [(Finset.mem_filter.mp hk).2, (Finset.mem_filter.mp hk').2])
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinjOn
  have hbound := hC Δ z (n 2) (n i0) (n j0) s3 w (by exact_mod_cast hΔ0.ne') hn3 hnj hw B hB
  calc (A.card : ℝ) ≤ (boxZeros (wCurve Δ z (n 2) (n i0) (n j0) s3 w) (fun _ => B)).card := by
        exact_mod_cast hcard
    _ ≤ _ := hbound

/-- C6: eligible heights on a shell `T ≤ t < 2T` with `gcd(v,t) = g`: at most `8gz/T`.
(Corrected: needs `0 ≤ z`; for `z < 0` the right side is `≤ 0`.) -/
theorem height_count (n : Mode) (Δ : ℕ) (z s2 s3 T : ℤ) (g : ℕ) (hT : 0 < T)
    (hΔ : Squarefree Δ) (hn : nsqZ n = Δ * z ^ 2) (hz : 0 ≤ z) :
    ((((activePts n s2 s3).filter fun k => T ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k < 2 * T ∧
        Nat.gcd (n 2).natAbs (tOf Δ s2 n k).natAbs = g).image fun k => k 2).card : ℝ) ≤
      8 * g * z / T := by
  classical
  set S := ((activePts n s2 s3).filter fun k => T ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k < 2 * T ∧
        Nat.gcd (n 2).natAbs (tOf Δ s2 n k).natAbs = g).image fun k => k 2 with hSdef
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.card_empty, Nat.cast_zero]; positivity
  have key : ∀ w ∈ S, w ≠ 0 ∧ (((n 2).natAbs / g : ℕ) : ℤ) ∣ w ∧
      T * |w| ≤ ((n 2).natAbs : ℤ) * (T + 2 * z) ∧ T < 2 * z ∧ 0 < g ∧ g ∣ (n 2).natAbs ∧
      n 2 ≠ 0 := by
    intro w hw
    rw [hSdef, Finset.mem_image] at hw
    obtain ⟨k, hk, rfl⟩ := hw
    rw [Finset.mem_filter] at hk
    obtain ⟨hk, hT1, _, hg⟩ := hk
    obtain ⟨c, hcΔ, hcz, hcs2, hcs3, hct, -⟩ := coords_of_active hΔ hn hk
    rw [abs_of_nonneg hz] at hcz
    have hcg : c.g = g := by simp only [Coords.g, hct, hg]
    have hTt : T ≤ c.t := hct ▸ hT1
    refine ⟨c.hk3, ?_, ?_, ?_, ?_, ?_, c.hn3⟩
    · have := c.vg_dvd_w; rwa [hcg] at this
    · have := c.w_shell hT hTt; rwa [hcz] at this
    · have := c.t_lt; rw [hcz] at this; omega
    · rw [← hcg]; exact Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr c.hn3)
    · rw [← hcg]; exact Nat.gcd_dvd_left _ _
  obtain ⟨w₀, hw₀⟩ := hS
  obtain ⟨-, -, -, hTz, hg0, hgv, hn3⟩ := key w₀ hw₀
  set v := (n 2).natAbs
  set d := v / g
  have hvd : (v : ℤ) = d * g := by
    have : d * g = v := Nat.div_mul_cancel hgv
    exact_mod_cast this.symm
  have hd0 : 0 < d := Nat.div_pos (Nat.le_of_dvd (Int.natAbs_pos.mpr hn3) hgv) hg0
  have hd0' : (0 : ℤ) < d := by exact_mod_cast hd0
  set K := (g : ℤ) * (T + 2 * z) / T
  have hmaps : ∀ w ∈ S, w / (d : ℤ) ∈ (Finset.Icc (-K) K).erase 0 := by
    intro w hw
    obtain ⟨hw0, hdw, hsh, -, -, -⟩ := key w hw
    obtain ⟨j, rfl⟩ := hdw
    rw [Int.mul_ediv_cancel_left _ hd0'.ne']
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_Icc.mpr ?_⟩
    · rintro rfl; simp at hw0
    · have h1 : T * |j| ≤ g * (T + 2 * z) := by
        rw [abs_mul, abs_of_pos hd0', hvd] at hsh
        have : d * (T * |j|) ≤ d * (g * (T + 2 * z)) := by linarith
        exact le_of_mul_le_mul_left this hd0'
      have h2 : |j| ≤ K := (Int.le_ediv_iff_mul_le hT).mpr (by linarith)
      exact abs_le.mp h2
  have hinj : Set.InjOn (fun w => w / (d : ℤ)) S := by
    intro w1 hw1 w2 hw2 h
    obtain ⟨j1, rfl⟩ := (key w1 hw1).2.1
    obtain ⟨j2, rfl⟩ := (key w2 hw2).2.1
    simp only [Int.mul_ediv_cancel_left _ hd0'.ne'] at h
    rw [h]
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  have hK0 : 0 ≤ K := Int.ediv_nonneg (by positivity) hT.le
  have hcardK : ((Finset.Icc (-K) K).erase 0).card = 2 * K.toNat := by
    rw [Finset.card_erase_of_mem (by simp; omega), Int.card_Icc]; omega
  have hKT : K * T ≤ g * (T + 2 * z) := Int.ediv_mul_le _ hT.ne'
  rw [le_div_iff₀ hTr]
  have hSK : (S.card : ℤ) ≤ 2 * K := by rw [hcardK] at hcard; omega
  have hg0' : (0 : ℤ) ≤ g := by positivity
  have : (S.card : ℤ) * T ≤ 8 * g * z := by
    nlinarith [mul_le_mul_of_nonneg_right hSK hT.le, mul_le_mul_of_nonneg_left hTz.le hg0']
  exact_mod_cast this

/-- `∑_{a ∈ S} min(4, 36 g²/a²) ≤ 36 g` over positive integers. -/
private theorem sum_min_le (g : ℕ) (hg : 0 < g) (S : Finset ℕ) (h0 : 0 ∉ S) :
    ∑ a ∈ S, min (4 : ℝ) (36 * (g : ℝ) ^ 2 / (a : ℝ) ^ 2) ≤ 36 * g := by
  classical
  set G := 6 * g
  rw [← Finset.sum_filter_add_sum_filter_not S (fun a => a ≤ G)]
  have h1 : ∑ a ∈ S.filter (fun a => a ≤ G), min (4 : ℝ) (36 * (g : ℝ) ^ 2 / (a : ℝ) ^ 2) ≤
      4 * G := by
    have hsub : S.filter (fun a => a ≤ G) ⊆ Finset.Icc 1 G := by
      intro a ha
      obtain ⟨haS, haG⟩ := Finset.mem_filter.mp ha
      have : a ≠ 0 := fun h => h0 (h ▸ haS)
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr this, haG⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hc
    calc _ ≤ ∑ a ∈ S.filter (fun a => a ≤ G), (4 : ℝ) :=
          Finset.sum_le_sum fun a _ => min_le_left _ _
      _ = 4 * (S.filter (fun a => a ≤ G)).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 4 * G := by gcongr
  have h2 : ∑ a ∈ S.filter (fun a => ¬ a ≤ G), min (4 : ℝ) (36 * (g : ℝ) ^ 2 / (a : ℝ) ^ 2) ≤
      36 * (g : ℝ) ^ 2 * (2 / (G + 1)) := by
    set N := S.sup id + 1
    have hsub : S.filter (fun a => ¬ a ≤ G) ⊆ Finset.Ioo G N := by
      intro a ha
      obtain ⟨haS, haG⟩ := Finset.mem_filter.mp ha
      have : a ≤ S.sup id := Finset.le_sup (f := id) haS
      exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
    calc _ ≤ ∑ a ∈ S.filter (fun a => ¬ a ≤ G), 36 * (g : ℝ) ^ 2 * ((a : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum fun a _ => (min_le_right _ _).trans (le_of_eq (by ring))
      _ ≤ ∑ a ∈ Finset.Ioo G N, 36 * (g : ℝ) ^ 2 * ((a : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 36 * (g : ℝ) ^ 2 * ∑ a ∈ Finset.Ioo G N, ((a : ℝ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ 36 * (g : ℝ) ^ 2 * (2 / (G + 1)) := by
          gcongr; exact sum_Ioo_inv_sq_le G N
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hG : ((G : ℕ) : ℝ) = 6 * g := by simp [G]
  have h3 : 36 * (g : ℝ) ^ 2 * (2 / ((G : ℝ) + 1)) ≤ 12 * g := by
    rw [hG, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  calc _ ≤ (4 * G : ℝ) + 36 * (g : ℝ) ^ 2 * (2 / (G + 1)) := add_le_add h1 h2
    _ ≤ 4 * (6 * g) + 12 * g := by rw [← hG]; linarith
    _ = 36 * g := by ring

/-- Lagrange's identity. -/
private theorem lagrange' (m k : Mode) :
    nsqZ m * nsqZ k - dotZ m k ^ 2 =
      (m 1 * k 2 - m 2 * k 1) ^ 2 + (m 2 * k 0 - m 0 * k 2) ^ 2 + (m 0 * k 1 - m 1 * k 0) ^ 2 := by
  simp only [nsqZ, dotZ, Fin.sum_univ_three]
  ring

/-- The triangle inequality `z ≤ x + y` in integer coordinates. -/
private theorem Coords.z_le {n k : Mode} (c : Coords n k) : c.z ≤ c.x + c.y := by
  have := c.hy; have := c.hyx; have := c.hxz
  have hΔ := c.hΔ
  have hlag := lagrange' (-k - n) k
  have hcs : dotZ (-k - n) k ^ 2 ≤ (c.Δ * c.x * c.y) ^ 2 := by
    have : nsqZ (-k - n) * nsqZ k = (c.Δ * c.x * c.y) ^ 2 := by rw [c.hm, c.hk]; ring
    nlinarith [sq_nonneg ((-k - n) 1 * k 2 - (-k - n) 2 * k 1),
      sq_nonneg ((-k - n) 2 * k 0 - (-k - n) 0 * k 2),
      sq_nonneg ((-k - n) 0 * k 1 - (-k - n) 1 * k 0)]
  have hpos : 0 ≤ c.Δ * c.x * c.y := mul_nonneg (mul_nonneg hΔ.le (by linarith)) (by linarith)
  have hD : dotZ (-k - n) k ≤ c.Δ * c.x * c.y := by nlinarith
  have hN : nsqZ n = nsqZ (-k - n) + nsqZ k + 2 * dotZ (-k - n) k := by
    simp only [nsqZ, dotZ, Fin.sum_univ_three, Pi.sub_apply, Pi.neg_apply]
    ring
  rw [c.hn, c.hm, c.hk] at hN
  have hsq : c.Δ * c.z ^ 2 ≤ c.Δ * (c.x + c.y) ^ 2 := by nlinarith
  have hsq' : c.z ^ 2 ≤ (c.x + c.y) ^ 2 := le_of_mul_le_mul_left hsq hΔ
  nlinarith

/-- `|l| = √Δ u` from `|l|² = Δ u²`, `u ≥ 0`. -/
private theorem absk_eq_of {l : Mode} {Δ u : ℤ} (hΔ : 0 < Δ) (hu : 0 ≤ u)
    (h : nsqZ l = Δ * u ^ 2) : absk l = Real.sqrt Δ * u := by
  rw [absk_eq_sqrt_nsqZ, h]
  push_cast
  rw [Real.sqrt_mul (by exact_mod_cast hΔ.le), Real.sqrt_sq (by exact_mod_cast hu)]

set_option maxHeartbeats 400000 in
/-- The weight of an active point: `γ² ≤ 4` and `γ² w² ≤ 36 v²`. -/
private theorem gamma_weight {n k : Mode} (c : Coords n k) {a b e : Sgn}
    (hs2 : c.s2 = sgZ a * sgZ b) (hγ : gammaCoef a b e (-k - n) k n ≠ 0) :
    gammaCoef a b e (-k - n) k n ^ 2 ≤ 4 ∧
      gammaCoef a b e (-k - n) k n ^ 2 * ((k 2 : ℤ) : ℝ) ^ 2 ≤ 36 * ((n 2 : ℤ) : ℝ) ^ 2 := by
  have := c.hy; have := c.hyx; have := c.hxz
  set sΔ := Real.sqrt c.Δ with hsΔ
  have hsΔ0 : 0 < sΔ := Real.sqrt_pos.mpr (by exact_mod_cast c.hΔ)
  have hX := absk_eq_of c.hΔ (by linarith) c.hm
  have hY := absk_eq_of c.hΔ (by linarith) c.hk
  have hZ := absk_eq_of c.hΔ (by linarith) c.hn
  rw [← hsΔ] at hX hY hZ
  set X := absk (-k - n)
  set Y := absk k
  set Z := absk n
  set D := crossAbs (-k - n) k
  have hy1 : (1 : ℝ) ≤ c.y := by exact_mod_cast c.hy
  have hyx : (c.y : ℝ) ≤ c.x := by exact_mod_cast c.hyx
  have hxz : (c.x : ℝ) ≤ c.z := by exact_mod_cast c.hxz
  have hzxy : (c.z : ℝ) ≤ c.x + c.y := by exact_mod_cast c.z_le
  have hX0 : 0 < X := by rw [hX]; positivity
  have hXY : X ≤ Y := by rw [hX, hY]; gcongr
  have hYZ : Y ≤ Z := by rw [hY, hZ]; gcongr
  have hZXY : Z ≤ X + Y := by rw [hX, hY, hZ]; nlinarith
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hD : D ≤ X * Y := by
    simp only [D, X, Y, absk_eq_sqrt_nsqZ]
    rw [← Real.sqrt_mul (by exact_mod_cast (nsqZ_pos c.hm3).le)]
    apply Real.sqrt_le_sqrt
    push_cast
    nlinarith [sq_nonneg ((dotZ (-k - n) k : ℤ) : ℝ)]
  have hsg : ∀ s : Sgn, |sg s| = 1 := by intro s; cases s <;> simp [sg]
  have hQ : 0 < (X * Y * Z) ^ 2 := pow_pos (mul_pos (mul_pos hX0 (by linarith)) (by linarith)) 2
  have h12 : 0 < 12 * Real.sqrt 2 * (X * Y * Z) ^ 2 := by positivity
  have hs2' : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  set P := (sg a * X + sg b * Y + sg e * Z) * (sg a * X - sg b * Y) * (sg b * Y - sg e * Z) *
    (sg e * Z - sg a * X)
  have hγdef : gammaCoef a b e (-k - n) k n = D * |P| / (12 * Real.sqrt 2 * (X * Y * Z) ^ 2) :=
    rfl
  set γ := gammaCoef a b e (-k - n) k n
  have hγ0 : 0 ≤ γ := by rw [hγdef]; positivity
  -- the uniform bound
  have hb := gamma_bound (x := sg a * X) (y := sg b * Y) (z := sg e * Z) hX0 hXY hYZ hZXY hD0
    hD (by rw [abs_mul, hsg, one_mul, abs_of_pos hX0])
    (by rw [abs_mul, hsg, one_mul, abs_of_pos (by linarith)])
    (by rw [abs_mul, hsg, one_mul, abs_of_pos (by linarith)])
  have hs43 : (4 / 3 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hγ4 : γ ≤ 2 := by
    rw [hγdef, div_le_iff₀ h12]
    nlinarith [mul_le_mul_of_nonneg_right hs43 hQ.le]
  have hγsq : γ ^ 2 ≤ 4 := by nlinarith
  refine ⟨hγsq, ?_⟩
  have hZ0 : 0 < Z := by linarith
  have ht0 : 0 < c.t := by
    refine lt_of_le_of_ne c.t_nonneg (fun h0 => hγ ?_)
    obtain ⟨hxy, hyz⟩ := c.t_eq_zero h0.symm
    apply gamma_eq_zero_of_eq
    · show X = Y; rw [hX, hY, hxy]
    · show Y = Z; rw [hY, hZ, hxy, hyz]
  have hsh := c.w_shell ht0 le_rfl
  simp only [Coords.w, Coords.v, Int.natCast_natAbs] at hsh
  have hz0 : (0 : ℝ) < c.z := by linarith
  have hw2 : ((k 2 : ℤ) : ℝ) ^ 2 = ((|k 2| : ℤ) : ℝ) ^ 2 := by push_cast; exact (sq_abs _).symm
  have hn2 : ((n 2 : ℤ) : ℝ) ^ 2 = ((|n 2| : ℤ) : ℝ) ^ 2 := by push_cast; exact (sq_abs _).symm
  have hwa : (0 : ℝ) ≤ ((|k 2| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  have hva : (0 : ℝ) ≤ ((|n 2| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  rw [hw2, hn2]
  rcases c.hs2 with h1 | h1
  · -- same-sign inner pair: `t < z` and `γ z ≤ t`
    have htz : c.t ≠ c.z := by
      intro htz
      have h0 := c.t_eq_z htz
      apply hγ
      have : D = 0 := by simp only [D, crossAbs, h0, sub_self, Int.cast_zero, Real.sqrt_zero]
      rw [hγdef, this, zero_mul, zero_div]
    have htlt : c.t < c.z := (c.s2_branch htz).mpr h1
    have hab : sg a = sg b := by
      rw [h1] at hs2; cases a <;> cases b <;> simp [sgZ, sg] at hs2 ⊢
    have h8 : D * |P| ≤ 8 * ((Y - X) / Z) * (X * Y * Z) ^ 2 := by
      have hP : |P| = |(Y + X + sg a * sg e * Z) * (Y - X) * (X - sg a * sg e * Z) *
          (sg a * sg e * Z - Y)| := by
        rw [← abs_neg]
        congr 1
        simp only [P, ← hab]
        cases a <;> simp only [sg, Bool.false_eq_true, ↓reduceIte] <;> ring
      rw [hP, show (X * Y * Z) ^ 2 = (Y * X * Z) ^ 2 by ring]
      exact gamma_small_difference hX0 hXY hYZ (by linarith) hD0 (by linarith)
        (by rw [abs_mul, abs_mul, hsg, hsg, one_mul, one_mul, abs_of_pos hZ0])
    have hγZ : γ * Z ≤ Y - X := by
      have h8' : D * |P| * Z ≤ 8 * (Y - X) * (X * Y * Z) ^ 2 := by
        calc D * |P| * Z ≤ 8 * ((Y - X) / Z) * (X * Y * Z) ^ 2 * Z :=
              mul_le_mul_of_nonneg_right h8 hZ0.le
          _ = 8 * (Y - X) * (X * Y * Z) ^ 2 := by field_simp
      rw [hγdef, div_mul_eq_mul_div, div_le_iff₀ h12]
      nlinarith [mul_le_mul_of_nonneg_right hs2' (mul_nonneg (by linarith : (0 : ℝ) ≤ Y - X) hQ.le)]
    have hγz : γ * c.z ≤ c.t := by
      have : γ * Z ≤ Y - X := hγZ
      rw [hX, hY, hZ] at this
      have h' : sΔ * (γ * c.z) ≤ sΔ * ((c.x : ℝ) - c.y) := by linarith
      have := le_of_mul_le_mul_left h' hsΔ0
      simp only [Coords.t, h1, one_mul]; push_cast; linarith
    have hsh' : (c.t : ℝ) * ((|k 2| : ℤ) : ℝ) ≤ 3 * ((|n 2| : ℤ) : ℝ) * c.z := by
      have : c.t * |k 2| ≤ 3 * |n 2| * c.z := by nlinarith [abs_nonneg (n 2)]
      exact_mod_cast this
    have hfin : γ * ((|k 2| : ℤ) : ℝ) ≤ 3 * ((|n 2| : ℤ) : ℝ) := by
      have : γ * ((|k 2| : ℤ) : ℝ) * c.z ≤ 3 * ((|n 2| : ℤ) : ℝ) * c.z := by
        nlinarith [mul_le_mul_of_nonneg_right hγz hwa]
      exact le_of_mul_le_mul_right this hz0
    calc γ ^ 2 * ((|k 2| : ℤ) : ℝ) ^ 2 = (γ * ((|k 2| : ℤ) : ℝ)) ^ 2 := by ring
      _ ≤ (3 * ((|n 2| : ℤ) : ℝ)) ^ 2 := pow_le_pow_left₀ (mul_nonneg hγ0 hwa) hfin 2
      _ = 9 * ((|n 2| : ℤ) : ℝ) ^ 2 := by ring
      _ ≤ 36 * ((|n 2| : ℤ) : ℝ) ^ 2 := by linarith [sq_nonneg ((|n 2| : ℤ) : ℝ)]
  · -- opposite signs: `t ≥ z`, so `|w| ≤ 3v`
    have htz : c.z ≤ c.t := by
      by_contra hlt
      have hlt : c.t < c.z := lt_of_not_ge hlt
      have := (c.s2_branch hlt.ne).mp hlt
      rw [h1] at this; norm_num at this
    have hw3 : |k 2| ≤ 3 * |n 2| := by
      have : c.t * |k 2| ≤ c.t * (3 * |n 2|) := by nlinarith [abs_nonneg (n 2)]
      exact le_of_mul_le_mul_left this ht0
    have hw3' : ((|k 2| : ℤ) : ℝ) ≤ 3 * ((|n 2| : ℤ) : ℝ) := by exact_mod_cast hw3
    have h9 : ((|k 2| : ℤ) : ℝ) ^ 2 ≤ 9 * ((|n 2| : ℤ) : ℝ) ^ 2 := by
      nlinarith [pow_le_pow_left₀ hwa hw3' 2]
    calc γ ^ 2 * ((|k 2| : ℤ) : ℝ) ^ 2 ≤ 4 * (9 * ((|n 2| : ℤ) : ℝ) ^ 2) :=
          mul_le_mul hγsq h9 (sq_nonneg _) (by norm_num)
      _ = 36 * ((|n 2| : ℤ) : ℝ) ^ 2 := by ring

/-- Weighted count of the active points with `gcd(v, t) = g` for one helicity pattern. -/
private theorem act_sum_le {n : Mode} {Δ : ℕ} {z : ℤ} (hΔ : Squarefree Δ)
    (hn : nsqZ n = Δ * z ^ 2) (s2 s3 : ℤ) (g : ℕ) (a b e : Sgn) (hs2 : sgZ a * sgZ b = s2)
    (M : ℝ) (hM : ∀ w : ℤ, (((activePts n s2 s3).filter fun k => k 2 = w).card : ℝ) ≤ M) :
    ∑ k ∈ (activePts n s2 s3).filter
        (fun k => Nat.gcd (n 2).natAbs (tOf Δ s2 n k).natAbs = g),
      gammaCoef a b e (-k - n) k n ^ 2 ≤ 72 * M * g := by
  classical
  set Act := (activePts n s2 s3).filter
    (fun k => Nat.gcd (n 2).natAbs (tOf Δ s2 n k).natAbs = g) with hAct
  have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans (hM 0)
  rcases Act.eq_empty_or_nonempty with hA | ⟨k₀, hk₀⟩
  · rw [hA, Finset.sum_empty]; positivity
  -- per-point facts
  have hpt : ∀ k ∈ Act, ∃ c : Coords n k, c.s2 = s2 ∧ c.g = g := by
    intro k hk
    obtain ⟨hk, hg⟩ := Finset.mem_filter.mp hk
    obtain ⟨c, -, -, hcs2, -, hct, -⟩ := coords_of_active hΔ hn hk
    exact ⟨c, hcs2, by simp only [Coords.g, hct, hg]⟩
  obtain ⟨c₀, -, hc₀g⟩ := hpt k₀ hk₀
  have hv0 : 0 < (n 2).natAbs := Int.natAbs_pos.mpr c₀.hn3
  have hg0 : 0 < g := hc₀g ▸ Nat.gcd_pos_of_pos_left _ hv0
  have hgv : g ∣ (n 2).natAbs := hc₀g ▸ Nat.gcd_dvd_left _ _
  set d := (n 2).natAbs / g with hd
  have hvd : (n 2).natAbs = d * g := (Nat.div_mul_cancel hgv).symm
  have hd0 : 0 < d := Nat.div_pos (Nat.le_of_dvd hv0 hgv) hg0
  set h : ℕ → ℝ := fun A => min (4 : ℝ) (36 * (g : ℝ) ^ 2 / (A : ℝ) ^ 2)
  set φ : Mode → ℕ := fun k => (k 2).natAbs / d
  have hdiv : ∀ k ∈ Act, (k 2).natAbs = d * φ k ∧ 0 < φ k := by
    intro k hk
    obtain ⟨c, -, hcg⟩ := hpt k hk
    have h1 : ((c.v / c.g : ℕ) : ℤ) ∣ c.w := c.vg_dvd_w
    rw [hcg] at h1
    have h2 : d ∣ (k 2).natAbs := Int.natCast_dvd.mp h1
    refine ⟨(Nat.mul_div_cancel' h2).symm, Nat.div_pos (Nat.le_of_dvd ?_ h2) hd0⟩
    exact Int.natAbs_pos.mpr c.hk3
  have hweight : ∀ k ∈ Act, gammaCoef a b e (-k - n) k n ^ 2 ≤ h (φ k) := by
    intro k hk
    by_cases hγ : gammaCoef a b e (-k - n) k n = 0
    · rw [hγ, sq, mul_zero]; exact le_min (by norm_num) (by positivity)
    obtain ⟨c, hcs2, -⟩ := hpt k hk
    obtain ⟨h4, h36⟩ := gamma_weight c (hcs2.trans hs2.symm) hγ
    obtain ⟨hkd, hφ⟩ := hdiv k hk
    refine le_min h4 ?_
    have hk2 : ((k 2 : ℤ) : ℝ) ^ 2 = ((d : ℝ) * (φ k : ℝ)) ^ 2 := by
      have h' := Int.natAbs_sq (k 2)
      rw [hkd] at h'
      rw [← Int.cast_pow, ← h']; push_cast; ring
    have hn2 : ((n 2 : ℤ) : ℝ) ^ 2 = ((d : ℝ) * (g : ℝ)) ^ 2 := by
      have h' := Int.natAbs_sq (n 2)
      rw [hvd] at h'
      rw [← Int.cast_pow, ← h']; push_cast; ring
    rw [hk2, hn2] at h36
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
    have hφ' : (0 : ℝ) < φ k := by exact_mod_cast hφ
    rw [le_div_iff₀ (by positivity)]
    have : (d : ℝ) ^ 2 * (gammaCoef a b e (-k - n) k n ^ 2 * (φ k : ℝ) ^ 2) ≤
        (d : ℝ) ^ 2 * (36 * (g : ℝ) ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hfib : ∀ A ∈ Act.image φ, ((Act.filter fun k => φ k = A).card : ℝ) ≤ 2 * M := by
    intro A _
    have hsub : Act.filter (fun k => φ k = A) ⊆
        ((activePts n s2 s3).filter fun k => k 2 = ((d * A : ℕ) : ℤ)) ∪
          ((activePts n s2 s3).filter fun k => k 2 = -((d * A : ℕ) : ℤ)) := by
      intro k hk
      obtain ⟨hkA, hφA⟩ := Finset.mem_filter.mp hk
      have hkact := (Finset.mem_filter.mp hkA).1
      have habs : (k 2).natAbs = d * A := by rw [(hdiv k hkA).1, hφA]
      rcases Int.natAbs_eq (k 2) with h' | h'
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hkact, by rw [h', habs]⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hkact, by rw [h', habs]⟩)
    calc ((Act.filter fun k => φ k = A).card : ℝ)
        ≤ (((activePts n s2 s3).filter fun k => k 2 = ((d * A : ℕ) : ℤ)) ∪
          ((activePts n s2 s3).filter fun k => k 2 = -((d * A : ℕ) : ℤ))).card := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (((activePts n s2 s3).filter fun k => k 2 = ((d * A : ℕ) : ℤ)).card : ℝ) +
          ((activePts n s2 s3).filter fun k => k 2 = -((d * A : ℕ) : ℤ)).card := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ M + M := add_le_add (hM _) (hM _)
      _ = 2 * M := by ring
  have h0 : 0 ∉ Act.image φ := by
    intro h0
    obtain ⟨k, hk, hk0⟩ := Finset.mem_image.mp h0
    exact absurd hk0 (hdiv k hk).2.ne'
  calc ∑ k ∈ Act, gammaCoef a b e (-k - n) k n ^ 2 ≤ ∑ k ∈ Act, h (φ k) :=
        Finset.sum_le_sum hweight
    _ = ∑ A ∈ Act.image φ, ∑ k ∈ Act with φ k = A, h A :=
        (Finset.sum_fiberwise_of_maps_to' (fun k hk => Finset.mem_image_of_mem φ hk) h).symm
    _ = ∑ A ∈ Act.image φ, ((Act.filter fun k => φ k = A).card : ℝ) * h A := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ A ∈ Act.image φ, 2 * M * h A := by
        refine Finset.sum_le_sum fun A hA => ?_
        exact mul_le_mul_of_nonneg_right (hfib A hA) (by simp only [h]; positivity)
    _ = 2 * M * ∑ A ∈ Act.image φ, h A := by rw [Finset.mul_sum]
    _ ≤ 2 * M * (36 * g) := by
        gcongr
        exact sum_min_le g hg0 _ h0
    _ = 72 * M * g := by ring

/-- `W_g` is dominated by the sum over patterns of the weighted active counts. -/
private theorem Wg_le_sum (Δ : ℕ) (n : Mode) (g : ℕ) :
    Wg Δ n g ≤ ∑ s : Sgn × Sgn × Sgn,
      ∑ k ∈ (activePts n (sgZ s.1 * sgZ s.2.1) (sgZ s.2.2 * sgZ s.2.1)).filter
        (fun k => Nat.gcd (n 2).natAbs (tOf Δ (sgZ s.1 * sgZ s.2.1) n k).natAbs = g),
        gammaCoef s.1 s.2.1 s.2.2 (-k - n) k n ^ 2 := by
  classical
  unfold Wg
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun s _ => ?_
  set Act := (activePts n (sgZ s.1 * sgZ s.2.1) (sgZ s.2.2 * sgZ s.2.1)).filter
    (fun k => Nat.gcd (n 2).natAbs (tOf Δ (sgZ s.1 * sgZ s.2.1) n k).natAbs = g)
  set G : Mode → ℝ := fun k => if k ∈ Act then gammaCoef s.1 s.2.1 s.2.2 (-k - n) k n ^ 2 else 0
  have hp1 : ∀ p ∈ sortedFibre n, p.1 = -p.2 - n := by
    intro p hp
    have := (mem_sortedFibre' (m := p.1) (k := p.2) hp).1
    funext i
    have hi := congrFun this i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    simp only [Pi.sub_apply, Pi.neg_apply]
    linarith
  have hstep : ∀ p ∈ sortedFibre n,
      (if phase3 s.1 s.2.1 s.2.2 p.1 p.2 n = 0 ∧
          Nat.gcd (n 2).natAbs (tOf Δ (sgZ s.1 * sgZ s.2.1) n p.2).natAbs = g
        then gammaCoef s.1 s.2.1 s.2.2 p.1 p.2 n ^ 2 else 0) ≤ G p.2 := by
    intro p hp
    have hG0 : 0 ≤ G p.2 := by simp only [G]; split_ifs <;> positivity
    split_ifs with hc
    · by_cases hγ : gammaCoef s.1 s.2.1 s.2.2 p.1 p.2 n = 0
      · rw [hγ, sq, mul_zero]; exact hG0
      have hmem : p.2 ∈ Act := by
        have hbox : p.2 ∈ modeBox (Nat.sqrt (nsqZ n).toNat) := by
          simp only [sortedFibre, Finset.mem_filter, Finset.mem_product] at hp
          exact hp.1.2
        have hp' : (-p.2 - n, p.2) ∈ sortedFibre n := by
          rw [← hp1 p hp]; exact hp
        rw [hp1 p hp] at hc hγ
        refine Finset.mem_filter.mpr ⟨?_, hc.2⟩
        simp only [activePts, Finset.mem_filter]
        exact ⟨hbox, hp', s.1, s.2.1, s.2.2, rfl, rfl, hc.1, hγ⟩
      simp only [G, hmem, ↓reduceIte, hp1 p hp, le_refl]
    · exact hG0
  calc _ ≤ ∑ p ∈ sortedFibre n, G p.2 := Finset.sum_le_sum hstep
    _ = ∑ k ∈ (sortedFibre n).image Prod.snd, G k := by
        rw [Finset.sum_image]
        intro p hp q hq hpq
        exact Prod.ext (by rw [hp1 p hp, hp1 q hq, hpq]) hpq
    _ = ∑ k ∈ ((sortedFibre n).image Prod.snd).filter (· ∈ Act),
          gammaCoef s.1 s.2.1 s.2.2 (-k - n) k n ^ 2 := by
        rw [Finset.sum_filter]
    _ ≤ ∑ k ∈ Act, gammaCoef s.1 s.2.1 s.2.2 (-k - n) k n ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.mp hk).2)
          (fun _ _ _ => sq_nonneg _)

/-- C7 (eq. quant-fixed-height): `W_g(n) ≤ C N^{1/4+η} g`. -/
theorem Wg_bound (hP : PlaneCurveCount) : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ : ℕ) (z : ℤ) (g : ℕ), Squarefree Δ → nsqZ n = Δ * z ^ 2 →
      Wg Δ n g ≤ C * max 2 (absk n) ^ ((1 : ℝ) / 4 + η) * g := by
  intro η hη
  obtain ⟨C₁, hC₁0, hC₁⟩ := fixed_w_count hP η hη
  set α : ℝ := (1 : ℝ) / 4 + η with hα
  have hα0 : 0 ≤ α := by positivity
  refine ⟨576 * (C₁ * 2 ^ α + 2), by positivity, ?_⟩
  intro n Δ z g hΔ hn
  set N := max 2 (absk n)
  have hN1 : 1 ≤ N ^ α := Real.one_le_rpow (le_trans (by norm_num) (le_max_left _ _)) hα0
  set M := C₁ * max 2 (2 * absk n) ^ α + 2
  have hMb : M ≤ (C₁ * 2 ^ α + 2) * N ^ α := by
    have h1 : max 2 (2 * absk n) ≤ 2 * N :=
      max_le (by linarith [le_max_left 2 (absk n)]) (by linarith [le_max_right 2 (absk n)])
    have h2 : max 2 (2 * absk n) ^ α ≤ 2 ^ α * N ^ α := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) h1 hα0
    have h3 : C₁ * max 2 (2 * absk n) ^ α ≤ C₁ * (2 ^ α * N ^ α) :=
      mul_le_mul_of_nonneg_left h2 hC₁0
    simp only [M]
    nlinarith
  have hsum := Wg_le_sum Δ n g
  have hB : ∀ s : Sgn × Sgn × Sgn,
      ∑ k ∈ (activePts n (sgZ s.1 * sgZ s.2.1) (sgZ s.2.2 * sgZ s.2.1)).filter
        (fun k => Nat.gcd (n 2).natAbs (tOf Δ (sgZ s.1 * sgZ s.2.1) n k).natAbs = g),
        gammaCoef s.1 s.2.1 s.2.2 (-k - n) k n ^ 2 ≤ 72 * M * g := fun s =>
    act_sum_le hΔ hn _ _ g s.1 s.2.1 s.2.2 rfl M (fun w => hC₁ n w _ _)
  have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  calc Wg Δ n g ≤ ∑ _s : Sgn × Sgn × Sgn, 72 * M * g :=
        hsum.trans (Finset.sum_le_sum fun s _ => hB s)
    _ = 8 * (72 * M * g) := by simp
    _ ≤ 8 * (72 * ((C₁ * 2 ^ α + 2) * N ^ α) * g) := by gcongr
    _ = 576 * (C₁ * 2 ^ α + 2) * N ^ α * g := by ring

end OVNS.Quant
