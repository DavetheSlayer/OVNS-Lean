import OddViscousNS.Quant.Arith.Weighted.Quartic

/-!
# The joint surface and the gcd seam (Section D)

The surface `F(X₁,X₂,X₃) = 4g²n_j²(|k|² − Δx²)` (at `t = gX₁`, `w = n₃X₂/g`, `X₃ = k_i`) has total
degree 6 with the unique top monomial `X₁⁴X₂²` (coefficient `4Δ²g⁴`) and is absolutely
irreducible.  `resultant_projection` replaces the manuscript's "components + projection +
d²-descent": for `G` not divisible by `F` over `ℚ`, the resultant in `X₃` is a nonzero plane
polynomial of degree `≤ (2 + deg G) max(deg F, deg G)` vanishing on the common zeros.
`kappa_bound` is the covering-exponent inequality `κ ≤ p*/2 + O(1/log N)` with the explicit
constant 4.
-/

open MvPolynomial

namespace OVNS.Quant

/-- Total degree bound for a sum. -/
private lemma td_add {p q : MvPolynomial (Fin 3) ℤ} {n : ℕ} (hp : p.totalDegree ≤ n)
    (hq : q.totalDegree ≤ n) : (p + q).totalDegree ≤ n :=
  (totalDegree_add p q).trans (max_le hp hq)

/-- Total degree bound for a difference. -/
private lemma td_sub {p q : MvPolynomial (Fin 3) ℤ} {n : ℕ} (hp : p.totalDegree ≤ n)
    (hq : q.totalDegree ≤ n) : (p - q).totalDegree ≤ n :=
  (totalDegree_sub p q).trans (max_le hp hq)

/-- Total degree bound for a product. -/
private lemma td_mul {p q : MvPolynomial (Fin 3) ℤ} {a b n : ℕ} (hp : p.totalDegree ≤ a)
    (hq : q.totalDegree ≤ b) (h : a + b ≤ n) : (p * q).totalDegree ≤ n :=
  (totalDegree_mul p q).trans ((add_le_add hp hq).trans h)

/-- Total degree bound for a square. -/
private lemma td_sq {p : MvPolynomial (Fin 3) ℤ} {a n : ℕ} (hp : p.totalDegree ≤ a)
    (h : 2 * a ≤ n) : (p ^ 2).totalDegree ≤ n :=
  (totalDegree_pow p 2).trans ((Nat.mul_le_mul_left 2 hp).trans h)

/-- Constants have total degree `0`. -/
private lemma td_C (r : ℤ) (n : ℕ) : (C r : MvPolynomial (Fin 3) ℤ).totalDegree ≤ n := by
  rw [totalDegree_C]; exact Nat.zero_le _

/-- Variables have total degree `1`. -/
private lemma td_X (i : Fin 3) {n : ℕ} (h : 1 ≤ n) :
    (X i : MvPolynomial (Fin 3) ℤ).totalDegree ≤ n := by
  rw [totalDegree_X]; exact h

/-- Total degree bound for a negation. -/
private lemma td_neg {p : MvPolynomial (Fin 3) ℤ} {n : ℕ} (hp : p.totalDegree ≤ n) :
    (-p).totalDegree ≤ n := by
  rwa [totalDegree_neg]

/-- Each summand of the surface has total degree at most `6`. -/
private lemma surface_totalDegree_le (Δ z n3 ni nj s3 g : ℤ) :
    (surfacePoly Δ z n3 ni nj s3 g).totalDegree ≤ 6 := by
  simp only [surfacePoly]
  have hL : (-C (2 * Δ * g ^ 2) * X 0 ^ 2 * X 1 - C (Δ * g ^ 3) * X 0 ^ 2
      - C (2 * Δ * g ^ 2 * s3 * z) * X 0 - C (Δ * g * z ^ 2) - C (2 * n3 ^ 2) * X 1
      - C (2 * g * ni) * X 2 : MvPolynomial (Fin 3) ℤ).totalDegree ≤ 3 := by
    refine td_sub (td_sub (td_sub (td_sub (td_sub ?_ ?_) ?_) (td_C _ _)) ?_) ?_
    · exact td_mul (td_mul (td_neg (td_C _ 0)) (td_sq (td_X 0 le_rfl) le_rfl) le_rfl)
        (td_X 1 le_rfl) le_rfl
    · exact td_mul (td_C _ 0) (td_sq (td_X 0 le_rfl) le_rfl) (by norm_num)
    · exact td_mul (td_C _ 0) (td_X 0 le_rfl) (by norm_num)
    · exact td_mul (td_C _ 0) (td_X 1 le_rfl) (by norm_num)
    · exact td_mul (td_C _ 0) (td_X 2 le_rfl) (by norm_num)
  have hx : (C g * X 0 + C (s3 * z) + X 0 * X 1 : MvPolynomial (Fin 3) ℤ).totalDegree ≤ 2 := by
    refine td_add (td_add ?_ (td_C _ _)) (td_mul (td_X 0 le_rfl) (td_X 1 le_rfl) le_rfl)
    exact td_mul (td_C _ 0) (td_X 0 le_rfl) (by norm_num)
  refine td_sub (td_add (td_add ?_ (td_sq hL le_rfl)) ?_) ?_
  · exact td_mul (td_C _ 0) (td_sq (td_X 2 le_rfl) le_rfl) (by norm_num)
  · exact td_mul (td_C _ 0) (td_sq (td_X 1 le_rfl) le_rfl) (by norm_num)
  · exact td_mul (td_C _ 0) (td_sq hx le_rfl) (by norm_num)

/-- Additivity of coefficients. -/
private lemma coeff_add' (m : Fin 3 →₀ ℕ) (p q : MvPolynomial (Fin 3) ℤ) :
    (p + q).coeff m = p.coeff m + q.coeff m := by
  simp

/-- The coefficient of `X₁⁴X₂²` in the surface is `4Δ²g⁴`. -/
theorem surface_coeff_X14X22 (Δ z n3 ni nj s3 g : ℤ) :
    (surfacePoly Δ z n3 ni nj s3 g).coeff (Finsupp.single 0 4 + Finsupp.single 1 2) =
      4 * Δ ^ 2 * g ^ 4 := by
  simp only [surfacePoly, X, C_apply, sq, mul_add, add_mul, sub_mul, mul_sub, neg_mul, mul_neg,
    monomial_mul_monomial, coeff_add', coeff_sub, coeff_neg,
    coeff_monomial]
  simp only [Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply]
  norm_num [Fin.ext_iff]
  ring

/-- The surface has total degree `6`. -/
theorem surface_totalDegree (Δ z n3 ni nj s3 g : ℤ) (hΔ : Δ ≠ 0) (hg : g ≠ 0) :
    (surfacePoly Δ z n3 ni nj s3 g).totalDegree = 6 := by
  refine le_antisymm (surface_totalDegree_le _ _ _ _ _ _ _) ?_
  have hmem : (Finsupp.single 0 4 + Finsupp.single 1 2 : Fin 3 →₀ ℕ) ∈
      (surfacePoly Δ z n3 ni nj s3 g).support := by
    rw [mem_support_iff, surface_coeff_X14X22]
    positivity
  have := le_totalDegree hmem
  rwa [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl), Finsupp.sum_single_index rfl,
    Finsupp.sum_single_index rfl] at this

/-- A quadratic which is a square has zero discriminant. -/
private lemma disc_eq_zero_of_sq {K : Type} [_root_.Field K] (a b c : K) (u : Polynomial K)
    (h : Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c =
      u ^ 2) : b ^ 2 = 4 * a * c := by
  have hdeg : u.natDegree ≤ 1 := by
    have h1 := Polynomial.natDegree_quadratic_le (a := a) (b := b) (c := c)
    rw [h, Polynomial.natDegree_pow] at h1
    omega
  set u1 := u.coeff 1
  set u0 := u.coeff 0
  have h' : Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c =
      Polynomial.C (u1 ^ 2) * Polynomial.X ^ 2 + Polynomial.C (2 * u1 * u0) * Polynomial.X +
        Polynomial.C (u0 ^ 2) := by
    rw [h, Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
    simp only [map_mul, map_pow, map_ofNat]
    ring
  have h0 := congrArg (fun p : Polynomial K ↦ p.coeff 0) h'
  have h1 := congrArg (fun p : Polynomial K ↦ p.coeff 1) h'
  have h2 := congrArg (fun p : Polynomial K ↦ p.coeff 2) h'
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C] at h0 h1 h2
  norm_num at h0 h1 h2
  rw [h0, h1, h2]; ring

/-- The polynomial `2gL` in the two plane variables. -/
private noncomputable def sT (Δ z n3 s3 g : ℤ) : MvPolynomial (Fin 2) ℤ :=
  -C (2 * Δ * g ^ 2) * X 0 ^ 2 * X 1 - C (Δ * g ^ 3) * X 0 ^ 2 - C (2 * Δ * g ^ 2 * s3 * z) * X 0
    - C (Δ * g * z ^ 2) - C (2 * n3 ^ 2) * X 1

/-- The polynomial `x` in the two plane variables. -/
private noncomputable def sX (z s3 g : ℤ) : MvPolynomial (Fin 2) ℤ :=
  C g * X 0 + C (s3 * z) + X 0 * X 1

/-- The `X₃`-linear coefficient of the surface. -/
private noncomputable def sF1 (Δ z n3 ni s3 g : ℤ) : MvPolynomial (Fin 2) ℤ :=
  -C (4 * g * ni) * sT Δ z n3 s3 g

/-- The `X₃`-constant coefficient of the surface. -/
private noncomputable def sF0 (Δ z n3 nj s3 g : ℤ) : MvPolynomial (Fin 2) ℤ :=
  sT Δ z n3 s3 g ^ 2 + C (4 * nj ^ 2 * n3 ^ 2) * X 1 ^ 2
    - C (4 * g ^ 2 * nj ^ 2 * Δ) * sX z s3 g ^ 2

/-- The reduced discriminant of the surface in `X₃`. -/
private noncomputable def sP (Δ z n3 ni nj s3 g : ℤ) : MvPolynomial (Fin 2) ℤ :=
  C (4 * (ni ^ 2 + nj ^ 2) * g ^ 2 * Δ) * sX z s3 g ^ 2
    - C (4 * (ni ^ 2 + nj ^ 2) * n3 ^ 2) * X 1 ^ 2
    - sT Δ z n3 s3 g ^ 2

/-- The surface as a quadratic in `X₃`. -/
private lemma surface_decomp (Δ z n3 ni nj s3 g : ℤ) :
    surfacePoly Δ z n3 ni nj s3 g = C (4 * g ^ 2 * (ni ^ 2 + nj ^ 2)) * X 2 ^ 2
      + rename Fin.castSucc (sF1 Δ z n3 ni s3 g) * X 2
      + rename Fin.castSucc (sF0 Δ z n3 nj s3 g) := by
  simp only [surfacePoly, sF1, sF0, sT, sX, map_add, map_sub, map_mul, map_neg, map_pow,
    rename_C, rename_X, map_ofNat]
  have e0 : (Fin.castSucc (0 : Fin 2) : Fin 3) = 0 := rfl
  have e1 : (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 := rfl
  simp only [e0, e1]
  ring

/-- The `X₃`-discriminant of the surface is `(4gn_j)²` times `sP`. -/
private lemma disc_identity (Δ z n3 ni nj s3 g : ℤ) :
    sF1 Δ z n3 ni s3 g ^ 2 - 4 * C (4 * g ^ 2 * (ni ^ 2 + nj ^ 2)) * sF0 Δ z n3 nj s3 g =
      C (4 * g * nj) ^ 2 * sP Δ z n3 ni nj s3 g := by
  simp only [sF1, sF0, sP, map_add, map_mul, map_pow, map_ofNat]
  ring

/-- The reduced discriminant specialized at `X₁ = 0`. -/
private lemma sP_special (K : Type) [CommRing K] (Δ z n3 ni nj s3 g : ℤ) :
    eval₂Hom Polynomial.C ![0, Polynomial.X]
        (MvPolynomial.map (Int.castRingHom K) (sP Δ z n3 ni nj s3 g)) =
      Polynomial.C ((-4 * (ni ^ 2 + nj ^ 2) * n3 ^ 2 - 4 * n3 ^ 4 : ℤ) : K) * Polynomial.X ^ 2
        + Polynomial.C ((-4 * Δ * g * z ^ 2 * n3 ^ 2 : ℤ) : K) * Polynomial.X
        + Polynomial.C ((4 * (ni ^ 2 + nj ^ 2) * Δ * g ^ 2 * s3 ^ 2 * z ^ 2
            - Δ ^ 2 * g ^ 2 * z ^ 4 : ℤ) : K) := by
  rw [coe_eval₂Hom, eval₂_map, RingHom.ext_int (Polynomial.C.comp (Int.castRingHom K))
    (Int.castRingHom (Polynomial K))]
  simp only [sP, sT, sX, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_neg, eval₂_C, eval₂_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [eq_intCast, map_add, map_mul, map_pow, map_ofNat,
    Polynomial.C_eq_intCast]
  push_cast
  ring


/-- `MvPolynomial (Fin 3) R` as polynomials in `X 2` over `MvPolynomial (Fin 2) R`. -/
private noncomputable def lastEquiv (R : Type) [CommRing R] :
    MvPolynomial (Fin 3) R ≃ₐ[R] Polynomial (MvPolynomial (Fin 2) R) :=
  (renameEquiv R (finRotate 3)).trans (finSuccEquiv R 2)

/-- `lastEquiv` on `X 0`. -/
private lemma lastEquiv_X0 (R : Type) [CommRing R] :
    lastEquiv R (X 0) = Polynomial.C (X 0) := by
  simp only [lastEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X]
  exact finSuccEquiv_X_succ (j := 0)

/-- `lastEquiv` on `X 1`. -/
private lemma lastEquiv_X1 (R : Type) [CommRing R] :
    lastEquiv R (X 1) = Polynomial.C (X 1) := by
  simp only [lastEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X]
  exact finSuccEquiv_X_succ (j := 1)

/-- `lastEquiv` on `X 2`. -/
private lemma lastEquiv_X2 (R : Type) [CommRing R] :
    lastEquiv R (X 2) = Polynomial.X := by
  simp only [lastEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X]
  exact finSuccEquiv_X_zero

/-- `lastEquiv` on constants. -/
private lemma lastEquiv_C (R : Type) [CommRing R] (a : R) :
    lastEquiv R (C a) = Polynomial.C (C a) := by
  simp only [lastEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_C, finSuccEquiv_apply,
    eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]

/-- `lastEquiv` on polynomials in the first two variables. -/
private lemma lastEquiv_rename (R : Type) [CommRing R] (P : MvPolynomial (Fin 2) R) :
    lastEquiv R (rename Fin.castSucc P) = Polynomial.C P := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [rename_C, lastEquiv_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.C_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, rename_X, Polynomial.C_mul]
    congr 1
    fin_cases i
    · exact lastEquiv_X0 R
    · exact lastEquiv_X1 R

/-- The surface is absolutely irreducible. -/
theorem surface_absIrred (Δ z n3 ni nj s3 g : ℤ) (hΔ : 0 < Δ) (hz : 0 < z) (hn3 : n3 ≠ 0)
    (hnj : nj ≠ 0) (hg : g ≠ 0) (hs3 : s3 = 1 ∨ s3 = -1)
    (hnorm : ni ^ 2 + nj ^ 2 + n3 ^ 2 = Δ * z ^ 2) :
    AbsIrred (surfacePoly Δ z n3 ni nj s3 g) := by
  unfold AbsIrred
  have hN : 0 < ni ^ 2 + nj ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg ni) (lt_of_le_of_ne (sq_nonneg nj)
      (Ne.symm (pow_ne_zero 2 hnj)))
  have hc0 : (4 * g ^ 2 * (ni ^ 2 + nj ^ 2) : ℤ) ≠ 0 := by positivity
  have hc : ((4 * g ^ 2 * (ni ^ 2 + nj ^ 2) : ℤ) : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast hc0
  set cK : AlgebraicClosure ℚ := ((4 * g ^ 2 * (ni ^ 2 + nj ^ 2) : ℤ) : AlgebraicClosure ℚ)
    with hcK
  set F1 := MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ)) (sF1 Δ z n3 ni s3 g)
  set F0 := MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ)) (sF0 Δ z n3 nj s3 g)
  set P := MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ)) (sP Δ z n3 ni nj s3 g)
  have hdec : MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ))
      (surfacePoly Δ z n3 ni nj s3 g) =
      C cK * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 + rename Fin.castSucc F0 := by
    rw [surface_decomp]
    have hm := map_mul (MvPolynomial.map (σ := Fin 3) (Int.castRingHom (AlgebraicClosure ℚ)))
    have ha := map_add (MvPolynomial.map (σ := Fin 3) (Int.castRingHom (AlgebraicClosure ℚ)))
    rw [ha, ha, hm, hm, map_pow, map_rename, map_rename, MvPolynomial.map_C, MvPolynomial.map_X]
    rfl
  rw [← MulEquiv.irreducible_iff (lastEquiv (AlgebraicClosure ℚ)), hdec]
  simp only [map_add, map_mul, map_pow, lastEquiv_rename]
  rw [lastEquiv_C, lastEquiv_X2]
  have hinv : C cK * C cK⁻¹ = (1 : MvPolynomial (Fin 2) (AlgebraicClosure ℚ)) := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have hinv' : Polynomial.C (C cK) * Polynomial.C (C cK⁻¹) =
      (1 : Polynomial (MvPolynomial (Fin 2) (AlgebraicClosure ℚ))) := by
    rw [← Polynomial.C_mul, hinv, map_one]
  have hfac : Polynomial.C (C cK) * Polynomial.X ^ 2 + Polynomial.C F1 * Polynomial.X +
      Polynomial.C F0 = Polynomial.C (C cK) * (Polynomial.C 1 * Polynomial.X ^ 2 +
        Polynomial.C (C cK⁻¹ * F1) * Polynomial.X + Polynomial.C (C cK⁻¹ * F0)) := by
    simp only [Polynomial.C_mul, map_one]
    linear_combination (-(Polynomial.C F1 * Polynomial.X + Polynomial.C F0)) * hinv'
  have hu : IsUnit (Polynomial.C (C cK) : Polynomial (MvPolynomial (Fin 2) (AlgebraicClosure ℚ))) :=
    ((Ne.isUnit hc).map C).map Polynomial.C
  rw [hfac, irreducible_isUnit_mul hu]
  have hqm : (Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C (C cK⁻¹ * F1) * Polynomial.X +
      Polynomial.C (C cK⁻¹ * F0) : Polynomial (MvPolynomial (Fin 2) (AlgebraicClosure ℚ))).Monic :=
    Polynomial.leadingCoeff_quadratic one_ne_zero
  have hqd := Polynomial.natDegree_quadratic (R := MvPolynomial (Fin 2) (AlgebraicClosure ℚ))
    (b := C cK⁻¹ * F1) (c := C cK⁻¹ * F0) one_ne_zero
  rw [hqm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  by_contra hroots
  obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hroots
  have hr' := (Polynomial.mem_roots hqm.ne_zero).mp hr
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at hr'
  have hroot : C cK * r ^ 2 + F1 * r + F0 = 0 := by
    linear_combination (C cK) * hr' - (F1 * r + F0) * hinv
  have hdisc : F1 ^ 2 - 4 * C cK * F0 = C ((4 * g * nj : ℤ) : AlgebraicClosure ℚ) ^ 2 * P := by
    have := congrArg (MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ)))
      (disc_identity Δ z n3 ni nj s3 g)
    have hm := map_mul (MvPolynomial.map (σ := Fin 2) (Int.castRingHom (AlgebraicClosure ℚ)))
    rw [map_sub, hm, hm, hm, map_pow, map_pow, map_ofNat, MvPolynomial.map_C,
      MvPolynomial.map_C] at this
    exact this
  have hd0 : ((4 * g * nj : ℤ) : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast (show (4 * g * nj : ℤ) ≠ 0 by positivity)
  have hdi : C ((4 * g * nj : ℤ) : AlgebraicClosure ℚ)⁻¹ * C ((4 * g * nj : ℤ) : AlgebraicClosure ℚ)
      = (1 : MvPolynomial (Fin 2) (AlgebraicClosure ℚ)) := by
    rw [← map_mul, inv_mul_cancel₀ hd0, map_one]
  have hsq : P = (C ((4 * g * nj : ℤ) : AlgebraicClosure ℚ)⁻¹ * (2 * C cK * r + F1)) ^ 2 := by
    linear_combination (-(C ((4 * g * nj : ℤ) : AlgebraicClosure ℚ)⁻¹ *
      C ((4 * g * nj : ℤ) : AlgebraicClosure ℚ) + 1) * P) * hdi
      + (-(C ((4 * g * nj : ℤ) : AlgebraicClosure ℚ)⁻¹) ^ 2) * hdisc
      + (-4 * C cK * C ((4 * g * nj : ℤ) : AlgebraicClosure ℚ)⁻¹ ^ 2) * hroot
  have hsp := congrArg (eval₂Hom Polynomial.C ![0, Polynomial.X]) hsq
  rw [sP_special, map_pow] at hsp
  have h := disc_eq_zero_of_sq _ _ _ _ hsp
  have hZ : (-4 * Δ * g * z ^ 2 * n3 ^ 2) ^ 2 = 4 * (-4 * (ni ^ 2 + nj ^ 2) * n3 ^ 2 - 4 * n3 ^ 4)
      * (4 * (ni ^ 2 + nj ^ 2) * Δ * g ^ 2 * s3 ^ 2 * z ^ 2 - Δ ^ 2 * g ^ 2 * z ^ 4) := by
    exact_mod_cast h
  have hs : s3 ^ 2 = 1 := by rcases hs3 with rfl | rfl <;> norm_num
  have key : (-4 * Δ * g * z ^ 2 * n3 ^ 2) ^ 2 - 4 * (-4 * (ni ^ 2 + nj ^ 2) * n3 ^ 2 - 4 * n3 ^ 4)
      * (4 * (ni ^ 2 + nj ^ 2) * Δ * g ^ 2 * s3 ^ 2 * z ^ 2 - Δ ^ 2 * g ^ 2 * z ^ 4) =
      48 * Δ ^ 2 * g ^ 2 * z ^ 4 * n3 ^ 2 * (ni ^ 2 + nj ^ 2) := by
    linear_combination (64 * Δ * g ^ 2 * z ^ 2 * n3 ^ 2 * (ni ^ 2 + nj ^ 2)) * hnorm
      + (64 * n3 ^ 2 * (ni ^ 2 + nj ^ 2 + n3 ^ 2) * (ni ^ 2 + nj ^ 2) * Δ * g ^ 2 * z ^ 2) * hs
  have hpos : 48 * Δ ^ 2 * g ^ 2 * z ^ 4 * n3 ^ 2 * (ni ^ 2 + nj ^ 2) ≠ 0 := by positivity
  exact hpos (by rw [← key, hZ, sub_self])

/-- Evaluation through `lastEquiv`. -/
private lemma eval_eq_lastEquiv (x : Fin 3 → ℤ) (P : MvPolynomial (Fin 3) ℤ) :
    eval x P = Polynomial.eval₂ (eval fun i ↦ x (Fin.castSucc i)) (x 2) (lastEquiv ℤ P) := by
  have h : eval x = (Polynomial.eval₂RingHom (eval fun i ↦ x (Fin.castSucc i)) (x 2)).comp
      (lastEquiv ℤ).toRingEquiv.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp
    · fin_cases i
      · simp [lastEquiv_X0]
      · simp [lastEquiv_X1]
      · simp [lastEquiv_X2]
  exact RingHom.congr_fun h P

/-- `lastEquiv` commutes with the coefficient map `ℤ → ℚ`. -/
private lemma map_lastEquiv (P : MvPolynomial (Fin 3) ℤ) :
    (lastEquiv ℤ P).map (MvPolynomial.map (Int.castRingHom ℚ)) =
      lastEquiv ℚ (MvPolynomial.map (Int.castRingHom ℚ) P) := by
  have h : (Polynomial.mapRingHom (MvPolynomial.map (Int.castRingHom ℚ))).comp
      (lastEquiv ℤ).toRingEquiv.toRingHom =
      (lastEquiv ℚ).toRingEquiv.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℚ)) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp
    · fin_cases i
      · simp [lastEquiv_X0]
      · simp [lastEquiv_X1]
      · simp [lastEquiv_X2]
  exact RingHom.congr_fun h P

/-- Coefficients in `X₃` have total degree at most that of the polynomial. -/
private lemma totalDegree_coeff_lastEquiv_le (P : MvPolynomial (Fin 3) ℤ) (k : ℕ) :
    ((lastEquiv ℤ P).coeff k).totalDegree ≤ P.totalDegree := by
  by_cases hk : (lastEquiv ℤ P).coeff k = 0
  · rw [hk, totalDegree_zero]; exact Nat.zero_le _
  · have := totalDegree_coeff_finSuccEquiv_add_le (renameEquiv ℤ (finRotate 3) P) k hk
    rw [totalDegree_renameEquiv] at this
    exact le_trans (Nat.le_add_right _ _) this

/-- The `X₃`-degree is at most the total degree. -/
private lemma natDegree_lastEquiv_le (P : MvPolynomial (Fin 3) ℤ) :
    (lastEquiv ℤ P).natDegree ≤ P.totalDegree := by
  by_cases hP : lastEquiv ℤ P = 0
  · rw [hP, Polynomial.natDegree_zero]; exact Nat.zero_le _
  · have hk : (lastEquiv ℤ P).coeff (lastEquiv ℤ P).natDegree ≠ 0 := by
      rwa [Polynomial.coeff_natDegree, Ne, Polynomial.leadingCoeff_eq_zero]
    have := totalDegree_coeff_finSuccEquiv_add_le (renameEquiv ℤ (finRotate 3) P) _ hk
    rw [totalDegree_renameEquiv] at this
    exact le_trans (Nat.le_add_left _ _) this

/-- Total degree bound for a determinant. -/
private lemma totalDegree_det_le {n D : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2) ℤ))
    (hM : ∀ i j, (M i j).totalDegree ≤ D) : M.det.totalDegree ≤ n * D := by
  rw [Matrix.det_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ ↦ ?_)
  refine (totalDegree_smul_le _ _).trans ((totalDegree_finsetProd _ _).trans ?_)
  calc ∑ i, (M (σ i) i).totalDegree ≤ ∑ _i : Fin n, D := Finset.sum_le_sum fun i _ ↦ hM _ _
    _ = n * D := by simp

/-- Entries of the Sylvester matrix have bounded total degree. -/
private lemma totalDegree_sylvester_le {D m n : ℕ} (f g : Polynomial (MvPolynomial (Fin 2) ℤ))
    (hf : ∀ k, (f.coeff k).totalDegree ≤ D) (hg : ∀ k, (g.coeff k).totalDegree ≤ D)
    (i j : Fin (m + n)) : (Polynomial.sylvester f g m n i j).totalDegree ≤ D := by
  unfold Polynomial.sylvester
  rw [Matrix.of_apply]
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · rw [Fin.addCases_left]
    split_ifs
    · exact hg _
    · rw [totalDegree_zero]; exact Nat.zero_le _
  · rw [Fin.addCases_right]
    split_ifs
    · exact hf _
    · rw [totalDegree_zero]; exact Nat.zero_le _

/-- The `X₃`-resultant does not vanish. -/
private lemma resultant_ne_zero_aux (F G : MvPolynomial (Fin 3) ℤ)
    (hf2 : (lastEquiv ℤ F).natDegree = 2)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) F))
    (hFG : ¬ MvPolynomial.map (Int.castRingHom ℚ) F ∣ MvPolynomial.map (Int.castRingHom ℚ) G) :
    Polynomial.resultant (lastEquiv ℤ F) (lastEquiv ℤ G) 2 (lastEquiv ℤ G).natDegree ≠ 0 := by
  intro h0
  set ι : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ) with hιdef
  set κ := algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
  have hι : Function.Injective ι := map_injective _ (Int.castRingHom ℚ).injective_int
  have hκ : Function.Injective κ := IsFractionRing.injective _ _
  have hf' := map_lastEquiv F
  have hg' := map_lastEquiv G
  have e1 : (((lastEquiv ℤ F).map ι).map κ).natDegree = 2 := by
    rw [Polynomial.natDegree_map_eq_of_injective hκ, Polynomial.natDegree_map_eq_of_injective hι,
      hf2]
  have e2 : (((lastEquiv ℤ G).map ι).map κ).natDegree = (lastEquiv ℤ G).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hκ, Polynomial.natDegree_map_eq_of_injective hι]
  have hres : Polynomial.resultant (((lastEquiv ℤ F).map ι).map κ)
      (((lastEquiv ℤ G).map ι).map κ) = 0 := by
    rw [e1, e2, Polynomial.resultant_map_map, Polynomial.resultant_map_map, h0, map_zero,
      map_zero]
  obtain ⟨-, hnc⟩ := Polynomial.resultant_eq_zero_iff.mp hres
  have hirr' : Irreducible ((lastEquiv ℤ F).map ι) := by
    rw [hf']; exact (MulEquiv.irreducible_iff (lastEquiv ℚ)).mpr hirr
  have hprim : ((lastEquiv ℤ F).map ι).IsPrimitive :=
    hirr'.isPrimitive (by rw [Polynomial.natDegree_map_eq_of_injective hι, hf2]; norm_num)
  have hirrK := (hprim.irreducible_iff_irreducible_map_fraction_map
    (K := FractionRing (MvPolynomial (Fin 2) ℚ))).mp hirr'
  have hdvd : ((lastEquiv ℤ F).map ι).map κ ∣ ((lastEquiv ℤ G).map ι).map κ := by
    by_contra hd
    exact hnc (hirrK.coprime_iff_not_dvd.mpr hd)
  have h := hprim.dvd_of_fraction_map_dvd_fraction_map hdvd
  rw [hf', hg'] at h
  apply hFG
  simpa using map_dvd (lastEquiv ℚ).symm h

/-- D5: resultant projection. -/
theorem resultant_projection (F G : MvPolynomial (Fin 3) ℤ) (c : ℤ) (hc : c ≠ 0)
    (F1 F0 : MvPolynomial (Fin 2) ℤ)
    (hF : F = C c * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 + rename Fin.castSucc F0)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) F))
    (hFG : ¬ MvPolynomial.map (Int.castRingHom ℚ) F ∣ MvPolynomial.map (Int.castRingHom ℚ) G) :
    ∃ R : MvPolynomial (Fin 2) ℤ, R ≠ 0 ∧
      R.totalDegree ≤ (2 + G.totalDegree) * max F.totalDegree G.totalDegree ∧
      ∀ x : Fin 3 → ℤ, eval x F = 0 → eval x G = 0 → eval (fun i => x (Fin.castSucc i)) R = 0 := by
  set f := lastEquiv ℤ F with hfdef
  set g := lastEquiv ℤ G with hgdef
  have hf : f = Polynomial.C (C c) * Polynomial.X ^ 2 + Polynomial.C F1 * Polynomial.X +
      Polynomial.C F0 := by
    rw [hfdef, hF]
    simp only [map_add, map_mul, map_pow, lastEquiv_rename]
    rw [lastEquiv_C, lastEquiv_X2]
  have hCc : (C c : MvPolynomial (Fin 2) ℤ) ≠ 0 := by simpa using hc
  have hf2 : f.natDegree = 2 := by rw [hf]; exact Polynomial.natDegree_quadratic hCc
  refine ⟨Polynomial.resultant f g 2 g.natDegree, ?_, ?_, ?_⟩
  · exact resultant_ne_zero_aux F G hf2 hirr hFG
  · refine (totalDegree_det_le _ fun i j ↦ totalDegree_sylvester_le f g
      (fun k ↦ (totalDegree_coeff_lastEquiv_le F k).trans (le_max_left _ _))
      (fun k ↦ (totalDegree_coeff_lastEquiv_le G k).trans (le_max_right _ _)) i j).trans ?_
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_left (natDegree_lastEquiv_le G) 2)
  · intro x hFx hGx
    obtain ⟨p, q, -, -, e⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g hf2.le le_rfl
      (Or.inl two_ne_zero)
    have := congrArg (Polynomial.eval₂ (eval fun i ↦ x (Fin.castSucc i)) (x 2)) e
    rw [Polynomial.eval₂_C, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul,
      ← eval_eq_lastEquiv, ← eval_eq_lastEquiv, hFx, hGx] at this
    rw [← this]; ring

/-- D4: the covering exponent. -/
theorem kappa_bound {lam U : ℝ} (hlam : Real.log 2 ≤ lam) (hU1 : pStar * lam < U)
    (hU2 : U ≤ (5 / 4 - pStar) * lam + Real.log 2) :
    Real.sqrt ((Real.log 2 + U) * (Real.log 4 + lam - U) * lam /
        (Real.log 256 + 2 * U + 2 * lam)) ≤ pStar / 2 * lam + 4 := by
  have _ := hU2
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  rw [h4, h256]
  set L := Real.log 2 with hL
  have hL0 : 0.6931471803 < L := Real.log_two_gt_d9
  have hL1 : L < 0.6931471808 := Real.log_two_lt_d9
  obtain ⟨hp1, hp2, -⟩ := pStar_bounds
  set p := pStar with hp
  have hpe : p ^ 2 + 3 * p - 2 = 0 := pStar_eq
  have hlam0 : 0 < lam := by linarith
  have hU0 : 0 < U := by nlinarith
  have hden : 0 < 8 * L + 2 * U + 2 * lam := by linarith
  have hR : 0 ≤ p / 2 * lam + 4 := by nlinarith
  rw [Real.sqrt_le_iff, div_le_iff₀ hden]
  refine ⟨hR, ?_⟩
  have hid : p ^ 2 / 4 * lam ^ 2 * (2 * U + 2 * lam) - lam * U * (lam - U) =
      lam * (U - p * lam) * (U - p * lam / 2) := by
    linear_combination (lam ^ 2 * U / 2) * hpe
  have h1 : 0 ≤ lam * (U - p * lam) * (U - p * lam / 2) := by
    apply mul_nonneg (mul_nonneg hlam0.le (by linarith)) (by nlinarith)
  have h2 : lam * L * (U + lam) ≤ 8 * p * lam * (U + lam) := by
    have : 0 ≤ lam * (U + lam) := by positivity
    nlinarith
  have h3 : lam * L * (2 * L) ≤ 32 * lam := by
    have : L * (2 * L) ≤ 32 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hlam0.le]
  have h5 : 0 ≤ 8 * L * (p / 2 * lam + 4) ^ 2 := by positivity
  nlinarith

end OVNS.Quant
