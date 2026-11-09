import OddViscousNS.Quant.Arith.Weighted.Defs

/-!
# Plane Bézout (weak form) and the few-points lemma for non-absolutely-irreducible curves

* `plane_bezout`: over a field `K`, two relatively prime plane polynomials (no common non-unit
  factor, `IsRelPrime`) have at most `deg P · deg Q` common zeros.  Proved by a dimension count
  on the spaces `V_t` of polynomials of total degree `≤ t`: with `t = m + n + |S|` the map
  `(A, B) ↦ AP + BQ : V_{t−m} × V_{t−n} → V_t` has kernel `{(CQ, −CP)}` (relative primality),
  its image vanishes on `S`, and Lagrange products make evaluation on `S` surjective; the identity
  `N(t) − N(t−m) − N(t−n) + N(t−m−n) = mn` closes the count.
* `fewPointsNotAbsIrred : FewPointsNotAbsIrred`: a `ℚ`-irreducible plane curve `H` (integer
  coefficients) that is not absolutely irreducible has at most `(deg H)²` integer points.  Galois
  descent (`InfiniteGalois.mem_range_algebraMap_iff_fixed`): the `ℚ̄`-irreducible factors of `H`
  are permuted by `Gal(ℚ̄/ℚ)`; if every automorphism sent a factor `F` to an associate, a
  coefficient-normalized `F` and its cofactor would be rational, contradicting irreducibility over
  `ℚ`; hence `H` has two distinct conjugate factors, both vanishing at every rational zero, so
  every rational zero is a singular point of `H`.  Then `plane_bezout` over `ℚ` for `(H, ∂ᵢH)`
  with `∂ᵢH ≠ 0` (char 0, `H` non-constant) gives `≤ d(d − 1) ≤ d²`.

Route: `OddViscousNS_data/reports/t12_algebra_route.md`.  (The earlier named input
`PlaneBezoutWeak` with Mathlib's `IsCoprime` is vacuous — `IsCoprime` excludes common zeros —
and is superseded by `plane_bezout`.)
-/

open MvPolynomial

namespace OVNS.Quant

/-- Twice the number of lattice points `(a, b)` with `a + b ≤ t` is `(t + 1)(t + 2)`. -/
lemma two_mul_card_lowSet (t : ℕ) :
    2 * ((Finset.range (t + 1) ×ˢ Finset.range (t + 1)).filter
      (fun p : ℕ × ℕ ↦ p.1 + p.2 ≤ t)).card = (t + 1) * (t + 2) := by
  have h : ((Finset.range (t + 1) ×ˢ Finset.range (t + 1)).filter
      (fun p : ℕ × ℕ ↦ p.1 + p.2 ≤ t)) =
      (Finset.range (t + 1)).biUnion (fun k ↦ Finset.HasAntidiagonal.antidiagonal k) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_biUnion,
      Finset.HasAntidiagonal.mem_antidiagonal]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨a + b, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [h, Finset.card_biUnion]
  · simp only [Finset.Nat.card_antidiagonal]
    clear h
    induction t with
    | zero => simp
    | succ t ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  · intro i _ j _ hij
    exact Finset.disjoint_left.2 fun p hi hj ↦
      hij ((Finset.HasAntidiagonal.mem_antidiagonal.1 hi).symm.trans
        (Finset.HasAntidiagonal.mem_antidiagonal.1 hj))

/-- `2 · dim V_t = (t + 1)(t + 2)` for the space `V_t` of plane polynomials of degree `≤ t`. -/
lemma two_mul_finrank_restrictTotalDegree (K : Type*) [_root_.Field K] (t : ℕ) :
    2 * Module.finrank K (restrictTotalDegree (Fin 2) K t) = (t + 1) * (t + 2) := by
  rw [restrictTotalDegree, Module.finrank_eq_nat_card_basis (basisRestrictSupport K _),
    ← two_mul_card_lowSet t, ← Nat.card_eq_finsetCard]
  congr 1
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Finsupp.equivFunOnFinite.trans (piFinTwoEquiv fun _ ↦ ℕ)) ?_
  intro e
  rw [Set.mem_ofPred_eq, Finsupp.sum_fintype e (fun _ e ↦ e) (fun _ ↦ rfl), Fin.sum_univ_two]
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Equiv.trans_apply, Finsupp.equivFunOnFinite_apply, piFinTwoEquiv_apply]
  omega

section Helpers

variable {K : Type*} [_root_.Field K]

/-- The map `(A, B) ↦ AP + BQ : V_a × V_b → V_t`. -/
noncomputable def bezoutMap (P Q : MvPolynomial (Fin 2) K) (a b t : ℕ)
    (ha : a + P.totalDegree ≤ t) (hb : b + Q.totalDegree ≤ t) :
    (restrictTotalDegree (Fin 2) K a × restrictTotalDegree (Fin 2) K b) →ₗ[K]
      restrictTotalDegree (Fin 2) K t :=
  LinearMap.codRestrict _
    ((LinearMap.mulRight K P ∘ₗ (Submodule.subtype _) ∘ₗ LinearMap.fst K _ _) +
      (LinearMap.mulRight K Q ∘ₗ (Submodule.subtype _) ∘ₗ LinearMap.snd K _ _))
    (fun x ↦ by
      rw [mem_restrictTotalDegree]
      have h1 := (mem_restrictTotalDegree _ _ _).1 x.1.2
      have h2 := (mem_restrictTotalDegree _ _ _).1 x.2.2
      change ((x.1 : MvPolynomial (Fin 2) K) * P + (x.2 : MvPolynomial (Fin 2) K) * Q).totalDegree
        ≤ t
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_mul _ _).trans (by omega)
      · exact (totalDegree_mul _ _).trans (by omega))

/-- The syzygy map `C ↦ (CQ, -CP) : V_c → V_a × V_b`. -/
noncomputable def syzMap (P Q : MvPolynomial (Fin 2) K) (a b c : ℕ)
    (ha : c + Q.totalDegree ≤ a) (hb : c + P.totalDegree ≤ b) :
    restrictTotalDegree (Fin 2) K c →ₗ[K]
      (restrictTotalDegree (Fin 2) K a × restrictTotalDegree (Fin 2) K b) :=
  LinearMap.prod
    (LinearMap.codRestrict _ (LinearMap.mulRight K Q ∘ₗ Submodule.subtype _) (fun x ↦ by
      rw [mem_restrictTotalDegree]
      have h1 := (mem_restrictTotalDegree _ _ _).1 x.2
      change ((x : MvPolynomial (Fin 2) K) * Q).totalDegree ≤ a
      exact (totalDegree_mul _ _).trans (by omega)))
    (LinearMap.codRestrict _ (-(LinearMap.mulRight K P ∘ₗ Submodule.subtype _)) (fun x ↦ by
      rw [mem_restrictTotalDegree]
      have h1 := (mem_restrictTotalDegree _ _ _).1 x.2
      change (-((x : MvPolynomial (Fin 2) K) * P)).totalDegree ≤ b
      rw [totalDegree_neg]
      exact (totalDegree_mul _ _).trans (by omega)))

/-- Evaluation on a finite set of points `V_t → K^S`. -/
noncomputable def evalOn (S : Finset (Fin 2 → K)) (t : ℕ) :
    restrictTotalDegree (Fin 2) K t →ₗ[K] (S → K) where
  toFun f x := eval (x : Fin 2 → K) (f : MvPolynomial (Fin 2) K)
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp


/-- The kernel of `(A, B) ↦ AP + BQ` consists of syzygies `(CQ, -CP)` when `P, Q` are
relatively prime. -/
lemma ker_bezoutMap_le (P Q : MvPolynomial (Fin 2) K) (hPQ : IsRelPrime P Q) (hQ : Q ≠ 0)
    (c : ℕ) :
    LinearMap.ker (bezoutMap P Q (c + Q.totalDegree) (c + P.totalDegree)
        (c + P.totalDegree + Q.totalDegree) (by omega) (by omega)) ≤
      LinearMap.range (syzMap P Q (c + Q.totalDegree) (c + P.totalDegree) c le_rfl le_rfl) := by
  rintro ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ hx
  have h0 : A * P + B * Q = 0 := congrArg Subtype.val hx
  have hdvd : Q ∣ A * P := ⟨-B, by linear_combination h0⟩
  obtain ⟨D, rfl⟩ := hPQ.symm.dvd_of_dvd_mul_right hdvd
  have hB' : B = -(D * P) := by
    have : Q * (D * P + B) = 0 := by linear_combination h0
    linear_combination (mul_eq_zero.1 this).resolve_left hQ
  have hD : D ∈ restrictTotalDegree (Fin 2) K c := by
    rw [mem_restrictTotalDegree]
    rcases eq_or_ne D 0 with h | h
    · simp [h]
    · have := (mem_restrictTotalDegree _ _ _).1 hA
      rw [totalDegree_mul_of_isDomain hQ h] at this
      omega
  refine ⟨⟨D, hD⟩, ?_⟩
  subst hB'
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact mul_comm D Q
  · rfl

open scoped Classical in
/-- A coordinate in which two distinct points of `K²` differ. -/
noncomputable def diffCoord (x y : Fin 2 → K) : Fin 2 := if x 0 = y 0 then 1 else 0

omit [_root_.Field K] in
/-- Distinct points differ at `diffCoord`. -/
lemma ne_at_diffCoord {x y : Fin 2 → K} (h : y ≠ x) :
    x (diffCoord x y) ≠ y (diffCoord x y) := by
  unfold diffCoord
  split_ifs with h0
  · intro h1
    apply h
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
  · exact h0

open scoped Classical in
/-- The Lagrange-type product vanishing on `S \ {x}` but not at `x`. -/
noncomputable def lagrangeProd (S : Finset (Fin 2 → K)) (x : Fin 2 → K) :
    MvPolynomial (Fin 2) K :=
  ∏ y ∈ S.erase x, (X (diffCoord x y) - C (y (diffCoord x y)))

/-- The Lagrange product has degree at most `|S|`. -/
lemma totalDegree_lagrangeProd (S : Finset (Fin 2 → K)) (x : Fin 2 → K) :
    (lagrangeProd S x).totalDegree ≤ S.card := by
  classical
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun y _ ↦ ?_).trans ?_
  · exact (totalDegree_sub_C_le _ _).trans (totalDegree_X _).le
  · simpa using Finset.card_erase_le

/-- The Lagrange product does not vanish at its own point. -/
lemma eval_lagrangeProd_self (S : Finset (Fin 2 → K)) (x : Fin 2 → K) :
    eval x (lagrangeProd S x) ≠ 0 := by
  classical
  rw [lagrangeProd, map_prod]
  refine Finset.prod_ne_zero_iff.2 fun y hy ↦ ?_
  simp only [map_sub, eval_X, eval_C]
  exact sub_ne_zero.2 (ne_at_diffCoord (Finset.ne_of_mem_erase hy))

/-- The Lagrange product vanishes at the other points of `S`. -/
lemma eval_lagrangeProd_of_ne (S : Finset (Fin 2 → K)) {x y : Fin 2 → K} (hy : y ∈ S)
    (hxy : y ≠ x) : eval y (lagrangeProd S x) = 0 := by
  classical
  rw [lagrangeProd, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hxy, hy⟩) (by simp)

/-- Evaluation `V_t → K^S` is surjective once `|S| ≤ t`. -/
lemma evalOn_surjective (S : Finset (Fin 2 → K)) (t : ℕ) (ht : S.card ≤ t) :
    Function.Surjective (evalOn S t) := by
  intro g
  have hmem : ∑ x ∈ S.attach, (g x / eval (x : Fin 2 → K) (lagrangeProd S x)) •
      lagrangeProd S x ∈ restrictTotalDegree (Fin 2) K t :=
    Submodule.sum_mem _ fun x _ ↦ Submodule.smul_mem _ _
      ((mem_restrictTotalDegree _ _ _).2 ((totalDegree_lagrangeProd S x).trans ht))
  refine ⟨⟨_, hmem⟩, ?_⟩
  funext y
  change eval (y : Fin 2 → K) (∑ x ∈ S.attach, _) = g y
  rw [map_sum, Finset.sum_eq_single y]
  · rw [smul_eval]
    exact div_mul_cancel₀ _ (eval_lagrangeProd_self S y)
  · intro x _ hxy
    rw [smul_eval, eval_lagrangeProd_of_ne S y.2 (fun h ↦ hxy (Subtype.ext h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_attach _ _) h

end Helpers

/-- **Weak plane Bézout.** Relatively prime `P, Q ∈ K[X, Y]` have at most `deg P · deg Q`
common zeros. -/
theorem plane_bezout {K : Type*} [_root_.Field K] (P Q : MvPolynomial (Fin 2) K)
    (hPQ : IsRelPrime P Q) (hP : P ≠ 0) (hQ : Q ≠ 0) (S : Finset (Fin 2 → K))
    (hS : ∀ x ∈ S, eval x P = 0 ∧ eval x Q = 0) :
    S.card ≤ P.totalDegree * Q.totalDegree := by
  have _ := hP
  set m := P.totalDegree with hm
  set n := Q.totalDegree with hn
  set s := S.card with hs
  set Φ := bezoutMap P Q (s + n) (s + m) (s + m + n) (by omega) (by omega)
  set ev := evalOn S (s + m + n)
  have hrange : LinearMap.range Φ ≤ LinearMap.ker ev := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    funext y
    change eval (y : Fin 2 → K) (x.1.1 * P + x.2.1 * Q) = 0
    simp [(hS y y.2).1, (hS y y.2).2]
  have hker : Module.finrank K (LinearMap.ker Φ) ≤
      Module.finrank K (restrictTotalDegree (Fin 2) K s) :=
    (Submodule.finrank_mono (ker_bezoutMap_le P Q hPQ hQ s)).trans (LinearMap.finrank_range_le _)
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  have h2 := LinearMap.finrank_range_add_finrank_ker ev
  rw [LinearMap.range_eq_top.2 (evalOn_surjective S _ (by omega)), finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
  rw [Module.finrank_prod] at h1
  have h3 := Submodule.finrank_mono hrange
  have e1 := two_mul_finrank_restrictTotalDegree K (s + m + n)
  have e2 := two_mul_finrank_restrictTotalDegree K (s + n)
  have e3 := two_mul_finrank_restrictTotalDegree K (s + m)
  have e4 := two_mul_finrank_restrictTotalDegree K s
  have key : (s + m + n + 1) * (s + m + n + 2) + (s + 1) * (s + 2) =
      (s + n + 1) * (s + n + 2) + (s + m + 1) * (s + m + 2) + 2 * (m * n) := by ring
  omega

/-- Evaluation commutes with a coefficient ring homomorphism. -/
lemma eval_map_comp {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : Fin 2 → R)
    (q : MvPolynomial (Fin 2) R) : eval (fun i ↦ f (p i)) (map f q) = f (eval p q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add a b ha hb => simp [ha, hb]
  | mul_X a i ha => simp [ha]

/-- A Galois automorphism commutes with evaluation at a rational point. -/
lemma eval_map_galois (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (F : MvPolynomial (Fin 2) (AlgebraicClosure ℚ)) (p : Fin 2 → ℚ) :
    eval (fun i ↦ algebraMap ℚ (AlgebraicClosure ℚ) (p i))
        (map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) F) =
      σ (eval (fun i ↦ algebraMap ℚ (AlgebraicClosure ℚ) (p i)) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a i ha => simp only [map_mul, map_X, eval_X, ha, AlgEquiv.commutes]

/-- A Galois-fixed polynomial over `ℚ̄` has rational coefficients. -/
lemma exists_rat_of_fixed (W : MvPolynomial (Fin 2) (AlgebraicClosure ℚ))
    (h : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) W = W) :
    ∃ W' : MvPolynomial (Fin 2) ℚ, map (algebraMap ℚ (AlgebraicClosure ℚ)) W' = W := by
  have : W ∈ Set.range (map (algebraMap ℚ (AlgebraicClosure ℚ)) :
      MvPolynomial (Fin 2) ℚ → _) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    have := congrArg (fun q ↦ q.coeff m) (h σ)
    rwa [coeff_map] at this
  exact this

/-- Mapping `ℤ → ℚ̄` factors through `ℚ`. -/
lemma map_int_eq_map_rat (H : MvPolynomial (Fin 2) ℤ) :
    map (Int.castRingHom (AlgebraicClosure ℚ)) H =
      map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) H) := by
  rw [map_map, RingHom.ext_int ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ))
    (Int.castRingHom (AlgebraicClosure ℚ))]

/-- Galois automorphisms fix polynomials with integer coefficients. -/
lemma map_galois_map_int (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (H : MvPolynomial (Fin 2) ℤ) :
    map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
      (map (Int.castRingHom (AlgebraicClosure ℚ)) H) =
      map (Int.castRingHom (AlgebraicClosure ℚ)) H := by
  rw [map_map, RingHom.ext_int ((σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
    (Int.castRingHom (AlgebraicClosure ℚ))) (Int.castRingHom (AlgebraicClosure ℚ))]

/-- Galois automorphisms preserve irreducibility. -/
lemma irreducible_map_galois (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {F : MvPolynomial (Fin 2) (AlgebraicClosure ℚ)} (hF : Irreducible F) :
    Irreducible (map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) F) :=
  (MulEquiv.irreducible_iff (mapAlgEquiv (Fin 2) σ).toMulEquiv).mpr hF

/-- **Galois descent.** An irreducible factor over `ℚ̄` of a `ℚ`-irreducible, not absolutely
irreducible `H` is moved to a non-associate by some Galois automorphism. -/
lemma exists_galois_not_associated (H : MvPolynomial (Fin 2) ℤ)
    (hq : Irreducible (map (Int.castRingHom ℚ) H))
    (hb : ¬ Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) H))
    (F : MvPolynomial (Fin 2) (AlgebraicClosure ℚ)) (hF : Irreducible F)
    (hFH : F ∣ map (Int.castRingHom (AlgebraicClosure ℚ)) H) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ¬ Associated (map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) F) F := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m₀, hm₀⟩ : F.support.Nonempty := Finset.nonempty_iff_ne_empty.2
    (by rw [Ne, MvPolynomial.support_eq_empty]; exact hF.ne_zero)
  have hc : F.coeff m₀ ≠ 0 := mem_support_iff.1 hm₀
  set F₀ := C (F.coeff m₀)⁻¹ * F with hF₀def
  have hFF₀ : Associated F₀ F :=
    associated_unit_mul_left _ _ ((isUnit_iff_ne_zero.2 (inv_ne_zero hc)).map C)
  have hcoeff : F₀.coeff m₀ = 1 := by rw [hF₀def, coeff_C_mul, inv_mul_cancel₀ hc]
  have hF₀0 : F₀ ≠ 0 := fun h ↦ by simp [h] at hcoeff
  have hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) F₀ = F₀ := by
    intro σ
    have ha : Associated (map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) F₀) F₀ :=
      ((hFF₀.map (map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))).trans
        (hcon σ)).trans hFF₀.symm
    obtain ⟨u, hu⟩ := ha
    obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
    have h1 := congrArg (fun q ↦ q.coeff m₀) hu
    rw [hr, mul_comm, coeff_C_mul, coeff_map, hcoeff, map_one, mul_one] at h1
    calc _ = map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) F₀ * (u : _) := by
          rw [hr, h1, C_1, mul_one]
      _ = F₀ := hu
  obtain ⟨G, hG⟩ := exists_rat_of_fixed F₀ hfix
  obtain ⟨W, hW⟩ := hFF₀.dvd.trans hFH
  have hWfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) W = W := by
    intro σ
    have h1 := map_galois_map_int σ H
    rw [hW, map_mul, hfix σ] at h1
    exact mul_left_cancel₀ hF₀0 h1
  obtain ⟨W', hW'⟩ := exists_rat_of_fixed W hWfix
  have hsplit : map (Int.castRingHom ℚ) H = G * W' := by
    apply map_injective _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    rw [← map_int_eq_map_rat, hW, map_mul, hG, hW']
  rcases hq.isUnit_or_isUnit hsplit with hGu | hWu
  · exact hF.not_isUnit (hFF₀.isUnit (hG ▸ hGu.map _))
  · have hWu' : IsUnit W := hW' ▸ hWu.map _
    apply hb
    rw [hW]
    exact (hFF₀.symm.trans (associated_mul_unit_right F₀ W hWu')).irreducible hF


/-- **Rational zeros are singular.** Every rational zero of a `ℚ`-irreducible, not absolutely
irreducible `H` is a zero of all partial derivatives of `H`. -/
lemma singular_of_rat_zero (H : MvPolynomial (Fin 2) ℤ)
    (hq : Irreducible (map (Int.castRingHom ℚ) H))
    (hb : ¬ Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) H))
    (p : Fin 2 → ℚ) (hp : eval p (map (Int.castRingHom ℚ) H) = 0) (i : Fin 2) :
    eval p (pderiv i (map (Int.castRingHom ℚ) H)) = 0 := by
  set Hb := map (Int.castRingHom (AlgebraicClosure ℚ)) H with hHbdef
  have hHb : Hb = map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) H) :=
    map_int_eq_map_rat H
  set p' : Fin 2 → AlgebraicClosure ℚ := fun j ↦ algebraMap ℚ (AlgebraicClosure ℚ) (p j)
    with hp'def
  have hp' : eval p' Hb = 0 := by rw [hHb, hp'def, eval_map_comp, hp, map_zero]
  have hHb0 : Hb ≠ 0 := by
    rw [hHb]
    intro h
    apply hq.ne_zero
    apply map_injective _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    rw [h, map_zero]
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hHb0
  have hprod : eval p' (UniqueFactorizationMonoid.factors Hb).prod = 0 := by
    have h1 := congrArg (eval p') hu
    rw [map_mul, hp'] at h1
    exact (mul_eq_zero.1 h1).resolve_right (u.isUnit.map (eval p')).ne_zero
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
  obtain ⟨F, hFmem, hFp⟩ := hprod
  have hF := UniqueFactorizationMonoid.irreducible_of_factor F hFmem
  have hFdvd := UniqueFactorizationMonoid.dvd_of_mem_factors hFmem
  obtain ⟨σ, hσ⟩ := exists_galois_not_associated H hq hb F hF hFdvd
  set F' := map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) F with hF'def
  have hF' : Irreducible F' := irreducible_map_galois σ hF
  have hF'dvd : F' ∣ Hb := by
    have := map_dvd (map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) hFdvd
    rwa [map_galois_map_int] at this
  have hF'p : eval p' F' = 0 := by rw [hF'def, hp'def, eval_map_galois, ← hp'def, hFp, map_zero]
  have hrel : IsRelPrime F F' := by
    rw [hF.isRelPrime_iff_not_dvd]
    intro hd
    exact hσ (hF.associated_of_dvd hF' hd).symm
  obtain ⟨R, hR⟩ := hrel.mul_dvd hFdvd hF'dvd
  have hsing : eval p' (pderiv i Hb) = 0 := by
    rw [hR]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hFp, hF'p, zero_mul,
      mul_zero, add_zero]
  rw [hHb, pderiv_map, hp'def, eval_map_comp] at hsing
  exact (map_eq_zero _).1 hsing

/-- A nonzero partial derivative has strictly smaller total degree. -/
lemma totalDegree_pderiv_lt {R : Type*} [CommRing R] (i : Fin 2) (p : MvPolynomial (Fin 2) R)
    (h : pderiv i p ≠ 0) : (pderiv i p).totalDegree + 1 ≤ p.totalDegree := by
  have key : ∀ m ∈ (pderiv i p).support, (m.sum fun _ e ↦ e) + 1 ≤ p.totalDegree := by
    intro m hm
    have hm' : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
      intro h0
      apply mem_support_iff.1 hm
      rw [coeff_pderiv, h0, zero_mul]
    have := le_totalDegree (mem_support_iff.2 hm')
    rwa [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
      Finsupp.sum_single_index rfl] at this
  have hne : (pderiv i p).support.Nonempty := Finset.nonempty_iff_ne_empty.2
    (by rw [Ne, MvPolynomial.support_eq_empty]; exact h)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup _ hne (fun m ↦ m.sum fun _ e ↦ e)
  rw [totalDegree, hmax]
  exact key m hm

/-- Over `ℚ`, a polynomial all of whose partial derivatives vanish is constant. -/
lemma eq_C_of_pderiv_eq_zero (p : MvPolynomial (Fin 2) ℚ) (h : ∀ i, pderiv i p = 0) :
    p = C (p.coeff 0) := by
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [hm]
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hm (Finsupp.ext fun i ↦ (hc i).symm)
    have h1 : (pderiv i p).coeff (m - Finsupp.single i 1) = 0 := by rw [h i]; rfl
    rw [coeff_pderiv] at h1
    have hmm : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
      ext j
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply]
      split_ifs with hij
      · subst hij
        omega
      · omega
    rw [hmm] at h1
    exact (mul_eq_zero.1 h1).resolve_right (by positivity)

/-- An irreducible polynomial is relatively prime to each nonzero partial derivative. -/
lemma isRelPrime_pderiv {p : MvPolynomial (Fin 2) ℚ} (hp : Irreducible p) (i : Fin 2)
    (hi : pderiv i p ≠ 0) : IsRelPrime p (pderiv i p) := by
  rw [hp.isRelPrime_iff_not_dvd]
  intro hd
  have h1 := totalDegree_le_of_dvd_of_isDomain hd hi
  have h2 := totalDegree_pderiv_lt i p hi
  omega

/-- The counting core of `fewPointsNotAbsIrred`: any finite set of integer zeros of `H` has at
most `(deg H)²` points. -/
lemma card_le_of_zeros (H : MvPolynomial (Fin 2) ℤ)
    (hq : Irreducible (map (Int.castRingHom ℚ) H))
    (hb : ¬ Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) H))
    (T : Finset (Fin 2 → ℤ)) (hT : ∀ x ∈ T, eval x H = 0) :
    T.card ≤ H.totalDegree ^ 2 := by
  set Hq := map (Int.castRingHom ℚ) H with hHq
  obtain ⟨i, hi⟩ : ∃ i, pderiv i Hq ≠ 0 := by
    by_contra hc
    push Not at hc
    have hC := eq_C_of_pderiv_eq_zero Hq hc
    apply hq.not_isUnit
    have h0 : Hq.coeff 0 ≠ 0 := fun h0 ↦ hq.ne_zero (by rw [hC, h0, C_0])
    rw [hC]
    exact (isUnit_iff_ne_zero.2 h0).map C
  have hdeg : Hq.totalDegree = H.totalDegree := by
    rw [hHq, totalDegree, totalDegree, support_map_of_injective _ (RingHom.injective_int _)]
  set S := T.image (fun x j ↦ ((x j : ℤ) : ℚ)) with hSdef
  have hcard : S.card = T.card := Finset.card_image_of_injective _
    (fun x y h ↦ funext fun j ↦ by exact_mod_cast congrFun h j)
  have hS : ∀ y ∈ S, eval y Hq = 0 ∧ eval y (pderiv i Hq) = 0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have h0 : eval (fun j ↦ ((x j : ℤ) : ℚ)) Hq = 0 := by
      have := eval_map_comp (Int.castRingHom ℚ) x H
      simp only [eq_intCast] at this
      rw [hHq, this, hT x hx, Int.cast_zero]
    exact ⟨h0, singular_of_rat_zero H hq hb _ h0 i⟩
  have hB := plane_bezout Hq (pderiv i Hq) (isRelPrime_pderiv hq i hi) hq.ne_zero hi S hS
  have h2 := totalDegree_pderiv_lt i Hq hi
  rw [← hcard]
  calc S.card ≤ Hq.totalDegree * (pderiv i Hq).totalDegree := hB
    _ ≤ Hq.totalDegree * Hq.totalDegree := Nat.mul_le_mul_left _ (by omega)
    _ = H.totalDegree ^ 2 := by rw [hdeg, sq]

/-- **Few points on a `ℚ`-irreducible, not absolutely irreducible, plane curve.** -/
theorem fewPointsNotAbsIrred : FewPointsNotAbsIrred := by
  intro H hq hb B
  have h := card_le_of_zeros H hq hb (boxZeros H B) fun x hx ↦ by
    unfold boxZeros at hx
    exact (Finset.mem_filter.1 hx).2
  exact_mod_cast h

end OVNS.Quant
