import OddViscousNS.Quant.Arith.Algebra.FewPoints
import OddViscousNS.Quant.Arith.Weighted.SurfaceCover

/-!
# `PlaneCurveCount` is a theorem

Formal proof of `OVNS.PlaneCurveCount`, by the single-prime `p`-adic determinant method in the
plane (Heath-Brown, *The density of rational points on curves and surfaces*, Ann. of Math. 155
(2002): Lemma 4 for the primes, Lemma 5 for the Hensel family, Theorem 4 for the height; the
exponent `log B₀ log B₁ / log 𝔗` is obtained from an L-shaped exponent set adapted to the box, as
in Heath-Brown, LNM 1891, Theorem 15).

Inputs: Mathlib's Bertrand postulate, Siegel lemma, `Matrix.det_vandermonde`, Schwartz–Zippel, and
the repository's `plane_bezout`.  Not used: absolute irreducibility modulo `p`, Noether forms,
Lang–Weil, Chebyshev bounds, Hilbert functions.  For `d ≥ 2` only irreducibility over `ℚ` is used.
Route and sources: `OddViscousNS_data/reports/t12_plane_route.md`.
-/

namespace OVNS.Quant.PlaneCount
/-! ## the determinant core (Vandermonde divisibility, Leibniz bound) -/

section DeterminantCore
open Polynomial Matrix

/-- The Vandermonde product divides `det (hⱼ(tᵢ))` for ANY polynomials `hⱼ`. -/
theorem vandermonde_dvd_det_eval {R : Type*} [CommRing R] [Nontrivial R] {s : ℕ} (t : Fin s → R)
    (h : Fin s → R[X]) :
    ∏ i, ∏ j ∈ Finset.Ioi i, (t j - t i) ∣ (Matrix.of fun i j => (h j).eval (t i)).det := by
  classical
  set P : R[X] := ∏ i, (X - C (t i)) with hP
  have hmon : P.Monic := monic_prod_X_sub_C _ _
  have hdeg : P.natDegree = s := by
    rw [hP, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp
  have hroot : ∀ i, P.eval (t i) = 0 := by
    intro i
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  set r : Fin s → R[X] := fun j => h j %ₘ P with hr
  have hrd : ∀ j, s ≠ 0 → (r j).natDegree < s := by
    intro j hs
    have h1 : P ≠ 1 := by
      intro h1
      rw [h1, natDegree_one] at hdeg
      omega
    have := natDegree_modByMonic_lt (h j) hmon h1
    simpa [hr, hdeg] using this
  have hev : ∀ i j, (h j).eval (t i) = (r j).eval (t i) := by
    intro i j
    have := modByMonic_add_div (h j) P
    conv_lhs => rw [← this]
    simp [hroot i, hr]
  have hmat : (Matrix.of fun i j => (h j).eval (t i)) =
      Matrix.vandermonde t * Matrix.of (fun (l j : Fin s) => (r j).coeff l) := by
    ext i j
    have hs : s ≠ 0 := fun h0 => by subst h0; exact Fin.elim0 i
    rw [Matrix.of_apply, Matrix.mul_apply, hev]
    simp only [Matrix.vandermonde_apply, Matrix.of_apply]
    rw [eval_eq_sum_range' (hrd j hs),
      Fin.sum_univ_eq_sum_range (fun l => t i ^ l * (r j).coeff l) s]
    exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
  rw [hmat, Matrix.det_mul, Matrix.det_vandermonde]
  exact Dvd.intro _ rfl

/-- Number of ordered pairs in `Fin s`. -/
theorem sum_card_Ioi (s : ℕ) : ∑ i : Fin s, (Finset.Ioi i).card = s * (s - 1) / 2 := by
  have h1 : ∑ i : Fin s, (Finset.Ioi i).card = ∑ i ∈ Finset.range s, (s - 1 - i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => s - 1 - i) s]
    exact Finset.sum_congr rfl (fun i _ => by simp)
  rw [h1, Finset.sum_range_reflect (fun i => i) s, Finset.sum_range_id]

/-- If all `tᵢ` are congruent mod `p`, then `p^{s(s-1)/2} ∣ det (hⱼ(tᵢ))`. -/
theorem pow_dvd_det_eval {s : ℕ} (p : ℤ) (t : Fin s → ℤ) (ht : ∀ i j, p ∣ t j - t i)
    (h : Fin s → ℤ[X]) :
    p ^ (s * (s - 1) / 2) ∣ (Matrix.of fun i j => (h j).eval (t i)).det := by
  refine dvd_trans ?_ (vandermonde_dvd_det_eval t h)
  rw [← sum_card_Ioi, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ?_
  rw [← Finset.prod_const]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun j _ => ht i j

/-- Entrywise congruence passes to determinants. -/
theorem dvd_det_sub_det {n : Type*} [Fintype n] [DecidableEq n] (m : ℤ)
    (A B : Matrix n n ℤ) (h : ∀ i j, m ∣ A i j - B i j) : m ∣ A.det - B.det := by
  have key : (Ideal.Quotient.mk (Ideal.span {m})).mapMatrix A =
      (Ideal.Quotient.mk (Ideal.span {m})).mapMatrix B := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (h i j))
  have := congrArg Matrix.det key
  rw [← RingHom.map_det, ← RingHom.map_det] at this
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp this)

/-- Leibniz bound with column bounds. -/
theorem abs_det_le_prod {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) (c : Fin s → ℝ)
    (h : ∀ i j, |(A i j : ℝ)| ≤ c j) :
    |(A.det : ℝ)| ≤ s.factorial * ∏ j, c j := by
  have hc : ∀ j, 0 ≤ c j := fun j => by
    by_cases hs : s = 0
    · subst hs; exact Fin.elim0 j
    · exact (abs_nonneg _).trans (h ⟨0, by omega⟩ j)
  rw [Matrix.det_apply]
  push_cast
  calc |∑ σ : Equiv.Perm (Fin s), ((Equiv.Perm.sign σ • ∏ i, A (σ i) i : ℤ) : ℝ)|
      ≤ ∑ σ : Equiv.Perm (Fin s), |((Equiv.Perm.sign σ • ∏ i, A (σ i) i : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin s), ∏ j, c j := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have : |((Equiv.Perm.sign σ • ∏ i, A (σ i) i : ℤ) : ℝ)| = ∏ i, |(A (σ i) i : ℝ)| := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;>
            simp [h1, Finset.abs_prod]
        rw [this]
        exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => h _ j)
    _ = s.factorial * ∏ j, c j := by
        simp [Finset.card_univ, Fintype.card_perm]

end DeterminantCore

/-! ## the polynomial Hensel family -/

section HenselFamily
open MvPolynomial

/-- Second-order Taylor expansion in the second variable. -/
theorem taylor_Y (F : MvPolynomial (Fin 2) ℤ) (x w δ : ℤ) :
    ∃ r : ℤ, eval ![x, w + δ] F =
      eval ![x, w] F + eval ![x, w] (pderiv 1 F) * δ + r * δ ^ 2 := by
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add p q hp hq =>
    obtain ⟨r1, h1⟩ := hp
    obtain ⟨r2, h2⟩ := hq
    exact ⟨r1 + r2, by simp only [map_add, h1, h2]; ring⟩
  | mul_X p i hp =>
    obtain ⟨r, h⟩ := hp
    fin_cases i
    · refine ⟨r * x, ?_⟩
      simp [pderiv_X, h]
      ring
    · refine ⟨r * (w + δ) + eval ![x, w] (pderiv 1 p), ?_⟩
      simp [pderiv_X, h]
      ring

/-- Evaluation is compatible with congruences. -/
theorem eval_congr_mod (G : MvPolynomial (Fin 2) ℤ) (m : ℤ) {a b a' b' : ℤ}
    (ha : m ∣ a - a') (hb : m ∣ b - b') : m ∣ eval ![a, b] G - eval ![a', b'] G := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    simp only [map_add]
    have := dvd_add hp hq
    convert this using 1
    ring
  | mul_X p i hp =>
    fin_cases i
    · simp only [map_mul, eval_X]
      have h : eval ![a, b] p * a - eval ![a', b'] p * a' =
          (eval ![a, b] p - eval ![a', b'] p) * a + eval ![a', b'] p * (a - a') := by ring
      simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [h]
      exact dvd_add (Dvd.dvd.mul_right hp _) (Dvd.dvd.mul_left ha _)
    · simp only [map_mul, eval_X]
      have h : eval ![a, b] p * b - eval ![a', b'] p * b' =
          (eval ![a, b] p - eval ![a', b'] p) * b + eval ![a', b'] p * (b - b') := by ring
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h]
      exact dvd_add (Dvd.dvd.mul_right hp _) (Dvd.dvd.mul_left hb _)

/-- `F(x₀ + t, g(t)) ∈ ℤ[t]`. -/
noncomputable def Phi (F : MvPolynomial (Fin 2) ℤ) (x₀ : ℤ) (g : Polynomial ℤ) : Polynomial ℤ :=
  MvPolynomial.aeval ![Polynomial.C x₀ + Polynomial.X, g] F

theorem eval_aeval (v : Fin 2 → Polynomial ℤ) (t : ℤ) (F : MvPolynomial (Fin 2) ℤ) :
    (MvPolynomial.aeval v F).eval t = eval (fun i => (v i).eval t) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, Polynomial.eval_mul, hp, aeval_X, eval_X]

theorem eval_Phi (F : MvPolynomial (Fin 2) ℤ) (x₀ t : ℤ) (g : Polynomial ℤ) :
    (Phi F x₀ g).eval t = eval ![x₀ + t, g.eval t] F := by
  unfold Phi
  rw [eval_aeval]
  congr 2
  funext i
  fin_cases i <;> simp

/-- The Hensel polynomials `g_{k+1} = g_k - c·F(x₀ + t, g_k)`. -/
noncomputable def gK (F : MvPolynomial (Fin 2) ℤ) (x₀ y₀ c : ℤ) : ℕ → Polynomial ℤ
  | 0 => Polynomial.C y₀
  | k + 1 => gK F x₀ y₀ c k - Polynomial.C c * Phi F x₀ (gK F x₀ y₀ c k)

/-- **Hensel family**: all integer zeros `(x, y)` in the residue class of `(x₀, y₀)` obey
`y ≡ g_k(x - x₀) mod p^{k+1}`, with one polynomial `g_k ∈ ℤ[t]`. -/
theorem hensel_family (F : MvPolynomial (Fin 2) ℤ) (p x₀ y₀ c : ℤ)
    (hc : p ∣ 1 - c * eval ![x₀, y₀] (pderiv 1 F)) (x y : ℤ) (hF : eval ![x, y] F = 0)
    (hx : p ∣ x - x₀) (hy : p ∣ y - y₀) (k : ℕ) :
    p ^ (k + 1) ∣ y - (gK F x₀ y₀ c k).eval (x - x₀) := by
  induction k with
  | zero => simpa [gK] using hy
  | succ k ih =>
    set w := (gK F x₀ y₀ c k).eval (x - x₀) with hw
    obtain ⟨δ', hδ'⟩ := ih
    set δ := y - w with hδ
    have hy' : y = w + δ := by rw [hδ]; ring
    obtain ⟨r, hr⟩ := taylor_Y F x w δ
    rw [← hy', hF] at hr
    have hstep : (gK F x₀ y₀ c (k + 1)).eval (x - x₀) = w - c * eval ![x, w] F := by
      have : x₀ + (x - x₀) = x := by ring
      simp [gK, eval_Phi, ← hw, this]
    rw [hstep]
    have hwy : p ∣ w - y₀ := by
      have h1 : p ∣ δ := by
        rw [hδ']
        exact Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero k)) _
      have : w - y₀ = (y - y₀) - δ := by rw [hδ]; ring
      rw [this]
      exact dvd_sub hy h1
    have hd : p ∣ eval ![x, w] (pderiv 1 F) - eval ![x₀, y₀] (pderiv 1 F) :=
      eval_congr_mod _ p hx hwy
    have hu : p ∣ 1 - c * eval ![x, w] (pderiv 1 F) := by
      have : 1 - c * eval ![x, w] (pderiv 1 F) = (1 - c * eval ![x₀, y₀] (pderiv 1 F)) -
          c * (eval ![x, w] (pderiv 1 F) - eval ![x₀, y₀] (pderiv 1 F)) := by ring
      rw [this]
      exact dvd_sub hc (Dvd.dvd.mul_left hd _)
    obtain ⟨u, hu⟩ := hu
    have key : y - (w - c * eval ![x, w] F) = δ * (1 - c * eval ![x, w] (pderiv 1 F)) -
        c * r * δ ^ 2 := by
      have : eval ![x, w] F = - (eval ![x, w] (pderiv 1 F) * δ + r * δ ^ 2) := by linarith
      rw [this, hδ]
      ring
    rw [key, hu, hδ']
    refine ⟨δ' * u - c * r * δ' ^ 2 * p ^ k, ?_⟩
    ring

/-- A Bézout inverse of a unit mod `p`. -/
theorem exists_inv_mod {p : ℕ} (hp : p.Prime) {m : ℤ} (hm : ¬ (p : ℤ) ∣ m) :
    ∃ c : ℤ, (p : ℤ) ∣ 1 - c * m := by
  have h : IsCoprime (p : ℤ) m :=
    ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).mpr hm
  obtain ⟨u, v, huv⟩ := h
  exact ⟨v, u, by linarith⟩

/-- The polynomial attached to the monomial `X^a Y^b` on the class. -/
noncomputable def hMon (F : MvPolynomial (Fin 2) ℤ) (x₀ y₀ c : ℤ) (k a b : ℕ) : Polynomial ℤ :=
  (Polynomial.C x₀ + Polynomial.X) ^ a * (gK F x₀ y₀ c k) ^ b

theorem hMon_congr (F : MvPolynomial (Fin 2) ℤ) (p x₀ y₀ c : ℤ)
    (hc : p ∣ 1 - c * eval ![x₀, y₀] (pderiv 1 F)) (x y : ℤ) (hF : eval ![x, y] F = 0)
    (hx : p ∣ x - x₀) (hy : p ∣ y - y₀) (k a b : ℕ) :
    p ^ (k + 1) ∣ x ^ a * y ^ b - (hMon F x₀ y₀ c k a b).eval (x - x₀) := by
  have h := hensel_family F p x₀ y₀ c hc x y hF hx hy k
  have e : (hMon F x₀ y₀ c k a b).eval (x - x₀) =
      x ^ a * ((gK F x₀ y₀ c k).eval (x - x₀)) ^ b := by
    simp [hMon]
  rw [e, ← mul_sub]
  exact Dvd.dvd.mul_left (h.trans (sub_dvd_pow_sub_pow _ _ _)) _

end HenselFamily

/-! ## the determinant on a nonsingular residue class -/

section ClassDeterminant
open MvPolynomial

/-- Pointwise form: a point of `Fin 2 → ℤ` is `![ξ 0, ξ 1]`. -/
theorem pt_eta {R : Type*} (ξ : Fin 2 → R) : ![ξ 0, ξ 1] = ξ := by
  funext i
  fin_cases i <;> rfl

/-- **Key determinant bound.**  On a residue class mod `p` of integer zeros of `F`, at a point where
`∂F/∂Y` is a unit, the monomial determinant is divisible by `p^{s(s-1)/2}`. -/
theorem pow_dvd_det_monomial {s : ℕ} (F : MvPolynomial (Fin 2) ℤ) {p : ℕ} (hp : p.Prime)
    (x₀ y₀ : ℤ) (hd : ¬ (p : ℤ) ∣ eval ![x₀, y₀] (pderiv 1 F))
    (ξ : Fin s → Fin 2 → ℤ) (hz : ∀ i, eval (ξ i) F = 0)
    (hx : ∀ i, (p : ℤ) ∣ ξ i 0 - x₀) (hy : ∀ i, (p : ℤ) ∣ ξ i 1 - y₀)
    (μ : Fin s → ℕ × ℕ) :
    (p : ℤ) ^ (s * (s - 1) / 2) ∣
      (Matrix.of fun i j => ξ i 0 ^ (μ j).1 * ξ i 1 ^ (μ j).2).det := by
  obtain ⟨c, hc⟩ := exists_inv_mod hp hd
  set k := s * (s - 1) / 2 with hk
  set A : Matrix (Fin s) (Fin s) ℤ := Matrix.of fun i j => ξ i 0 ^ (μ j).1 * ξ i 1 ^ (μ j).2
  set N : Matrix (Fin s) (Fin s) ℤ := Matrix.of fun i j =>
    (hMon F x₀ y₀ c k (μ j).1 (μ j).2).eval (ξ i 0 - x₀) with hN
  have h1 : (p : ℤ) ^ (k + 1) ∣ A.det - N.det := by
    refine dvd_det_sub_det _ A N fun i j => ?_
    have hzi : eval ![ξ i 0, ξ i 1] F = 0 := by rw [pt_eta]; exact hz i
    exact hMon_congr F p x₀ y₀ c hc _ _ hzi (hx i) (hy i) k _ _
  have h2 : (p : ℤ) ^ k ∣ N.det := by
    refine pow_dvd_det_eval (p : ℤ) (fun i => ξ i 0 - x₀) (fun i j => ?_) _
    have : ξ j 0 - x₀ - (ξ i 0 - x₀) = (ξ j 0 - x₀) - (ξ i 0 - x₀) := rfl
    exact dvd_sub (hx j) (hx i)
  have h3 : (p : ℤ) ^ k ∣ A.det - N.det := (pow_dvd_pow _ (Nat.le_succ k)).trans h1
  have := dvd_add h3 h2
  simpa using this

/-- Size + divisibility: the determinant vanishes. -/
theorem det_monomial_eq_zero {s : ℕ} (F : MvPolynomial (Fin 2) ℤ) {p : ℕ} (hp : p.Prime)
    (x₀ y₀ : ℤ) (hd : ¬ (p : ℤ) ∣ eval ![x₀, y₀] (pderiv 1 F))
    (ξ : Fin s → Fin 2 → ℤ) (hz : ∀ i, eval (ξ i) F = 0)
    (hx : ∀ i, (p : ℤ) ∣ ξ i 0 - x₀) (hy : ∀ i, (p : ℤ) ∣ ξ i 1 - y₀)
    (μ : Fin s → ℕ × ℕ) (B₀ B₁ : ℝ) (hB₀ : ∀ i, |(ξ i 0 : ℝ)| ≤ B₀) (hB₁ : ∀ i, |(ξ i 1 : ℝ)| ≤ B₁)
    (hsize : (s.factorial : ℝ) * ∏ j, (B₀ ^ (μ j).1 * B₁ ^ (μ j).2) <
      (p : ℝ) ^ (s * (s - 1) / 2)) :
    (Matrix.of fun i j => ξ i 0 ^ (μ j).1 * ξ i 1 ^ (μ j).2).det = 0 := by
  set A : Matrix (Fin s) (Fin s) ℤ := Matrix.of fun i j => ξ i 0 ^ (μ j).1 * ξ i 1 ^ (μ j).2 with hA
  have hdvd := pow_dvd_det_monomial F hp x₀ y₀ hd ξ hz hx hy μ
  by_contra hne
  have hle := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
  have hbound := abs_det_le_prod A (fun j => B₀ ^ (μ j).1 * B₁ ^ (μ j).2) (fun i j => by
    simp only [hA, Matrix.of_apply]
    push_cast
    rw [abs_mul, abs_pow, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hB₀ i) _)
      (pow_le_pow_left₀ (abs_nonneg _) (hB₁ i) _) (by positivity)
      (pow_nonneg ((abs_nonneg _).trans (hB₀ i)) _))
  have hle' : ((p : ℝ) ^ (s * (s - 1) / 2)) ≤ |(A.det : ℝ)| := by
    exact_mod_cast hle
  linarith

end ClassDeterminant

/-! ## vanishing minors give a linear relation -/

section VanishingMinors

/-- The row of a point. -/
noncomputable def row {s : ℕ} (μ : Fin s → ℕ × ℕ) (ξ : Fin 2 → ℤ) : Fin s → ℚ :=
  fun j => (ξ 0 : ℚ) ^ (μ j).1 * (ξ 1 : ℚ) ^ (μ j).2

theorem exists_vanishing_combination {s : ℕ} (A : Finset (Fin 2 → ℤ)) (μ : Fin s → ℕ × ℕ)
    (hdet : ∀ ξ : Fin s → Fin 2 → ℤ, (∀ i, ξ i ∈ A) →
      (Matrix.of fun i j => ξ i 0 ^ (μ j).1 * ξ i 1 ^ (μ j).2).det = 0) :
    ∃ c : Fin s → ℚ, c ≠ 0 ∧ ∀ ξ ∈ A, ∑ j, c j * row μ ξ j = 0 := by
  classical
  set T : Set (Fin s → ℚ) := row μ '' (A : Set (Fin 2 → ℤ)) with hT
  set W := Submodule.span ℚ T with hW
  by_cases htop : W = ⊤
  · exfalso
    obtain ⟨b, hbT, hbspan, hbli⟩ := exists_linearIndependent ℚ T
    have hb_top : Submodule.span ℚ b = ⊤ := hbspan.trans htop
    let _ : Fintype b := by
      have : Finite b := hbli.finite
      exact Fintype.ofFinite _
    have hcard : Fintype.card b = s := by
      have h1 := finrank_span_eq_card hbli
      have h2 : Submodule.span ℚ (Set.range ((↑) : b → (Fin s → ℚ))) = ⊤ := by
        simpa using hb_top
      rw [h2, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
      exact h1.symm
    let e : Fin s ≃ b := (Fintype.equivFinOfCardEq hcard).symm
    have hch : ∀ i : Fin s, ∃ ξ ∈ A, row μ ξ = (e i : Fin s → ℚ) := by
      intro i
      obtain ⟨ξ, hξ, h⟩ := hbT (e i).2
      exact ⟨ξ, hξ, h⟩
    choose ξ hξA hξ using hch
    have hd := hdet ξ hξA
    set Mz : Matrix (Fin s) (Fin s) ℤ :=
      Matrix.of fun i j => ξ i 0 ^ (μ j).1 * ξ i 1 ^ (μ j).2 with hMz
    set Mq : Matrix (Fin s) (Fin s) ℚ := Matrix.of fun i => (e i : Fin s → ℚ) with hMq
    have hcast : (Int.castRingHom ℚ).mapMatrix Mz = Mq := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hMz, hMq, Matrix.of_apply]
      rw [← hξ i]
      simp [row]
    have hdetq : Mq.det = 0 := by
      rw [← hcast, ← RingHom.map_det, hd]
      simp
    have hli : LinearIndependent ℚ Mq.row := by
      have : LinearIndependent ℚ (fun i : Fin s => (e i : Fin s → ℚ)) :=
        hbli.comp _ e.injective
      exact this
    have hunit := Matrix.linearIndependent_row_iff_isUnit.mp hli
    have := (Matrix.isUnit_iff_isUnit_det Mq).mp hunit
    rw [hdetq] at this
    exact not_isUnit_zero this
  · obtain ⟨f, hf0, hfW⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr htop)
    refine ⟨fun j => f (Pi.single j 1), ?_, ?_⟩
    · intro h
      apply hf0
      ext j
      have := congrFun h j
      simpa using this
    · intro ξ hξ
      have hmem : row μ ξ ∈ W := Submodule.subset_span ⟨ξ, hξ, rfl⟩
      have h0 : f (row μ ξ) = 0 := hfW hmem
      rw [← h0]
      have : row μ ξ = ∑ j, row μ ξ j • (Pi.single j 1 : Fin s → ℚ) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [this]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]

end VanishingMinors

/-! ## the leading-monomial argument -/

section TopMonomial
open MvPolynomial

/-- The weight. -/
noncomputable def wt (a b : ℝ) (m : Fin 2 →₀ ℕ) : ℝ := (m 0 : ℝ) * a + (m 1 : ℝ) * b

theorem wt_add (a b : ℝ) (m n : Fin 2 →₀ ℕ) : wt a b (m + n) = wt a b m + wt a b n := by
  simp only [wt, Finsupp.add_apply]; push_cast; ring

/-- `e` is the lexicographic top of `S` for the key `(wt, m 0)`. -/
def IsTop (a b : ℝ) (S : Finset (Fin 2 →₀ ℕ)) (e : Fin 2 →₀ ℕ) : Prop :=
  e ∈ S ∧ ∀ m ∈ S, wt a b m ≤ wt a b e ∧ (wt a b m = wt a b e → m 0 ≤ e 0)

theorem exists_isTop (a b : ℝ) (S : Finset (Fin 2 →₀ ℕ)) (hS : S.Nonempty) :
    ∃ e, IsTop a b S e := by
  classical
  obtain ⟨e, he, hmax⟩ := S.exists_max_image (fun m => toLex (wt a b m, m 0)) hS
  refine ⟨e, he, fun m hm => ?_⟩
  have := hmax m hm
  rw [Prod.Lex.toLex_le_toLex] at this
  rcases this with h | ⟨h1, h2⟩
  · exact ⟨h.le, fun h' => absurd h' h.ne⟩
  · exact ⟨h1.le, fun _ => h2⟩

/-- If `F ∣ G ≠ 0`, some monomial of `G` is divisible by the top monomial of `F`. -/
theorem exists_support_ge_of_dvd {F G : MvPolynomial (Fin 2) ℚ} {a b : ℝ} (hb : 0 < b)
    {e : Fin 2 →₀ ℕ} (he : IsTop a b F.support e) (hG : G ≠ 0) (hdvd : F ∣ G) :
    ∃ m ∈ G.support, e 0 ≤ m 0 ∧ e 1 ≤ m 1 := by
  classical
  obtain ⟨Q, rfl⟩ := hdvd
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hG
  obtain ⟨f, hf⟩ := exists_isTop a b Q.support (support_nonempty.mpr hQ)
  refine ⟨e + f, ?_, by simp, by simp⟩
  rw [mem_support_iff, coeff_mul]
  rw [Finset.sum_eq_single (e, f)]
  · exact mul_ne_zero (mem_support_iff.mp he.1) (mem_support_iff.mp hf.1)
  · rintro ⟨u, v⟩ huv hne
    by_contra hprod
    have hu : u ∈ F.support := mem_support_iff.mpr (left_ne_zero_of_mul hprod)
    have hv : v ∈ Q.support := mem_support_iff.mpr (right_ne_zero_of_mul hprod)
    have hsum : u + v = e + f := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    have hw := congrArg (wt a b) hsum
    rw [wt_add, wt_add] at hw
    obtain ⟨h1, h2⟩ := he.2 u hu
    obtain ⟨h3, h4⟩ := hf.2 v hv
    have h5 : wt a b u = wt a b e := by linarith
    have h6 : wt a b v = wt a b f := by linarith
    have h7 := h2 h5
    have h8 := h4 h6
    have h00 := DFunLike.congr_fun hsum 0
    have h11 := DFunLike.congr_fun hsum 1
    simp only [Finsupp.add_apply] at h00 h11
    have hu0 : u 0 = e 0 := by omega
    have hu1 : u 1 = e 1 := by
      have : (u 1 : ℝ) * b = (e 1 : ℝ) * b := by
        have h9 := h5
        simp only [wt, hu0] at h9
        linarith
      have := mul_right_cancel₀ hb.ne' this
      exact_mod_cast this
    have hue : u = e := by
      ext i
      fin_cases i
      · exact hu0
      · exact hu1
    have hvf : v = f := by
      rw [hue] at hsum
      exact add_left_cancel hsum
    exact hne (by rw [hue, hvf])
  · intro h
    exact absurd (by simp : (e, f) ∈ Finset.HasAntidiagonal.antidiagonal (e + f)) h

end TopMonomial

/-! ## the per-class bound -/

section ClassBound
open MvPolynomial

/-- The exponent `X^a Y^b`. -/
noncomputable def ex (m : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 m.1 + Finsupp.single 1 m.2

@[simp] theorem ex_zero (m : ℕ × ℕ) : ex m 0 = m.1 := by simp [ex]
@[simp] theorem ex_one (m : ℕ × ℕ) : ex m 1 = m.2 := by simp [ex]

theorem ex_injective : Function.Injective ex := by
  intro m n h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  simp only [ex_zero, ex_one] at h0 h1
  exact Prod.ext h0 h1

theorem ex_sum (m : ℕ × ℕ) : ((ex m).sum fun _ e => e) = m.1 + m.2 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two, ex_zero, ex_one]

/-- A polynomial with prescribed monomials. -/
noncomputable def polyOf {s : ℕ} (μ : Fin s → ℕ × ℕ) (c : Fin s → ℚ) : MvPolynomial (Fin 2) ℚ :=
  ∑ j, monomial (ex (μ j)) (c j)

theorem coeff_polyOf {s : ℕ} {μ : Fin s → ℕ × ℕ} (hμ : Function.Injective μ) (c : Fin s → ℚ)
    (j : Fin s) : (polyOf μ c).coeff (ex (μ j)) = c j := by
  classical
  unfold polyOf
  rw [coeff_sum, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [coeff_monomial, ite_eq_right_iff]
    exact fun h => absurd (hμ (ex_injective h)) hk
  · simp

theorem support_polyOf {s : ℕ} (μ : Fin s → ℕ × ℕ) (c : Fin s → ℚ) {m : Fin 2 →₀ ℕ}
    (hm : m ∈ (polyOf μ c).support) : ∃ j, m = ex (μ j) := by
  classical
  by_contra h
  push Not at h
  apply mem_support_iff.mp hm
  unfold polyOf
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_monomial, ite_eq_right_iff]
  exact fun h' => absurd h'.symm (h j)

theorem totalDegree_polyOf_le {s : ℕ} (μ : Fin s → ℕ × ℕ) (c : Fin s → ℚ) {D : ℕ}
    (hD : ∀ j, (μ j).1 + (μ j).2 ≤ D) : (polyOf μ c).totalDegree ≤ D := by
  unfold polyOf
  refine (totalDegree_finsetSum_le fun j _ => ?_)
  refine (totalDegree_monomial_le _ _).trans ?_
  have h1 : ((ex (μ j)).sum fun _ => id) = (μ j).1 + (μ j).2 := ex_sum (μ j)
  rw [h1]
  exact hD j

theorem eval_polyOf {s : ℕ} (μ : Fin s → ℕ × ℕ) (c : Fin s → ℚ) (ξ : Fin 2 → ℤ) :
    eval (fun i => (ξ i : ℚ)) (polyOf μ c) = ∑ j, c j * row μ ξ j := by
  unfold polyOf
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp [row]

/-- **Per-class bound.** -/
theorem class_card_le {F : MvPolynomial (Fin 2) ℤ}
    (hirr : Irreducible (map (Int.castRingHom ℚ) F)) {a b : ℝ} (hb : 0 < b) {e : Fin 2 →₀ ℕ}
    (he : IsTop a b (map (Int.castRingHom ℚ) F).support e) {p : ℕ} (hp : p.Prime) (x₀ y₀ : ℤ)
    (hd : ¬ (p : ℤ) ∣ eval ![x₀, y₀] (pderiv 1 F)) (A : Finset (Fin 2 → ℤ))
    (hz : ∀ ξ ∈ A, eval ξ F = 0) (hx : ∀ ξ ∈ A, (p : ℤ) ∣ ξ 0 - x₀)
    (hy : ∀ ξ ∈ A, (p : ℤ) ∣ ξ 1 - y₀) (B₀ B₁ : ℝ)
    (hB₀ : ∀ ξ ∈ A, |(ξ 0 : ℝ)| ≤ B₀) (hB₁ : ∀ ξ ∈ A, |(ξ 1 : ℝ)| ≤ B₁)
    (E : Finset (ℕ × ℕ)) (D : ℕ) (hE : ∀ m ∈ E, ¬ (e 0 ≤ m.1 ∧ e 1 ≤ m.2))
    (hED : ∀ m ∈ E, m.1 + m.2 ≤ D)
    (hsize : ((E.card).factorial : ℝ) * ∏ m ∈ E, (B₀ ^ m.1 * B₁ ^ m.2) <
      (p : ℝ) ^ (E.card * (E.card - 1) / 2)) :
    A.card ≤ (map (Int.castRingHom ℚ) F).totalDegree * D := by
  classical
  set s := E.card with hs
  let en : Fin s ≃ E := E.equivFin.symm
  set μ : Fin s → ℕ × ℕ := fun j => (en j : ℕ × ℕ) with hμ
  have hμinj : Function.Injective μ := fun i j h => en.injective (Subtype.ext h)
  have hμE : ∀ j, μ j ∈ E := fun j => (en j).2
  have hprod : ∏ j, (B₀ ^ (μ j).1 * B₁ ^ (μ j).2) = ∏ m ∈ E, (B₀ ^ m.1 * B₁ ^ m.2) := by
    rw [← Finset.prod_coe_sort E]
    exact Equiv.prod_comp en (fun m : E => B₀ ^ (m : ℕ × ℕ).1 * B₁ ^ (m : ℕ × ℕ).2)
  obtain ⟨c, hc0, hc⟩ := exists_vanishing_combination A μ (fun ξ hξ =>
    det_monomial_eq_zero F hp x₀ y₀ hd ξ (fun i => hz _ (hξ i)) (fun i => hx _ (hξ i))
      (fun i => hy _ (hξ i)) μ B₀ B₁ (fun i => hB₀ _ (hξ i)) (fun i => hB₁ _ (hξ i))
      (by rw [hprod]; exact hsize))
  set G := polyOf μ c with hG
  have hG0 : G ≠ 0 := by
    intro h0
    apply hc0
    funext j
    have := coeff_polyOf hμinj c j
    rw [← hG, h0] at this
    simpa using this.symm
  set Fq := map (Int.castRingHom ℚ) F with hFq
  have hnd : ¬ Fq ∣ G := by
    intro hdvd
    obtain ⟨m, hm, h0, h1⟩ := exists_support_ge_of_dvd hb he hG0 hdvd
    obtain ⟨j, rfl⟩ := support_polyOf μ c hm
    simp only [ex_zero, ex_one] at h0 h1
    exact hE _ (hμE j) ⟨h0, h1⟩
  have hrel : IsRelPrime Fq G := hirr.isRelPrime_iff_not_dvd.mpr hnd
  have hinj : Function.Injective (fun (ξ : Fin 2 → ℤ) (i : Fin 2) => (ξ i : ℚ)) := by
    intro ξ ξ' h
    funext i
    simpa using congrFun h i
  have hbz := OVNS.Quant.plane_bezout Fq G hrel hirr.ne_zero hG0
    (A.image fun (ξ : Fin 2 → ℤ) (i : Fin 2) => (ξ i : ℚ)) (by
      intro q hq
      obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hq
      constructor
      · have := OVNS.Quant.eval_map_comp (Int.castRingHom ℚ) ξ F
        simp only [eq_intCast] at this
        rw [hFq, this, hz ξ hξ]
        simp
      · rw [hG, eval_polyOf]
        exact hc ξ hξ)
  rw [Finset.card_image_of_injective _ hinj] at hbz
  exact hbz.trans (Nat.mul_le_mul_left _ (totalDegree_polyOf_le μ c fun j => hED _ (hμE j)))

end ClassBound

/-! ## primes, residue classes, the count for one prime -/

section OnePrime
open MvPolynomial

/-- `K` distinct primes in `(n, 2^K n]`, by iterating Bertrand. -/
theorem exists_primes (K n : ℕ) (hn : n ≠ 0) :
    ∃ ps : Finset ℕ, ps.card = K ∧ ∀ p ∈ ps, p.Prime ∧ n < p ∧ p ≤ 2 ^ K * n := by
  induction K with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ K ih =>
    obtain ⟨ps, hc, hp⟩ := ih
    obtain ⟨q, hq, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ K * n) (by positivity)
    have hnq : q ∉ ps := by
      intro hmem
      have := (hp q hmem).2.2
      omega
    refine ⟨insert q ps, by rw [Finset.card_insert_of_notMem hnq, hc], fun p hpm => ?_⟩
    have hle : n ≤ 2 ^ K * n := Nat.le_mul_of_pos_left _ (by positivity)
    have hpow : 2 ^ (K + 1) * n = 2 * (2 ^ K * n) := by ring
    rcases Finset.mem_insert.mp hpm with rfl | h
    · exact ⟨hq, by omega, by omega⟩
    · obtain ⟨a, b, c⟩ := hp p h
      exact ⟨a, b, by omega⟩

/-- A nonzero integer of size `< n^K` is not divisible by all of `K` primes `≥ n`. -/
theorem exists_prime_not_dvd (ps : Finset ℕ) (hp : ∀ p ∈ ps, p.Prime) (n : ℕ)
    (hn : ∀ p ∈ ps, n ≤ p) (m : ℤ) (hm : m ≠ 0) (hsize : m.natAbs < n ^ ps.card) :
    ∃ p ∈ ps, ¬ (p : ℤ) ∣ m := by
  by_contra hall
  push Not at hall
  have hdvd : ∏ p ∈ ps, p ∣ m.natAbs :=
    Finset.prod_primes_dvd _ (fun p hps => (hp p hps).prime)
      (fun p hps => Int.natCast_dvd.mp (hall p hps))
  have hle : ∏ p ∈ ps, p ≤ m.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hm) hdvd
  have hge : n ^ ps.card ≤ ∏ p ∈ ps, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod hn
  omega

/-- The number of `𝔽_p`-points of a nonzero curve of degree `≤ d` is at most `d p`
(Schwartz–Zippel; no Lang–Weil). -/
theorem card_points_le {p : ℕ} [Fact p.Prime] {G : MvPolynomial (Fin 2) (ZMod p)} (hG : G ≠ 0)
    {d : ℕ} (hd : G.totalDegree ≤ d) (I : Finset (ZMod p × ZMod p))
    (hI : ∀ q ∈ I, eval ![q.1, q.2] G = 0) : I.card ≤ d * p := by
  classical
  have hsz := schwartz_zippel_totalDegree hG (Finset.univ : Finset (ZMod p))
  simp only [Finset.card_univ, ZMod.card] at hsz
  set Z := (Fintype.piFinset fun _ : Fin 2 => (Finset.univ : Finset (ZMod p))).filter
    fun f => eval f G = 0 with hZ
  have hp0 : (0 : ℚ≥0) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hZle : (Z.card : ℚ≥0) ≤ G.totalDegree * p := by
    have h1 : (Z.card : ℚ≥0) / (p : ℚ≥0) ^ 2 ≤ G.totalDegree / p := hsz
    rw [div_le_div_iff₀ (by positivity) hp0] at h1
    have h2 : (Z.card : ℚ≥0) * p ≤ (G.totalDegree * p) * p := by
      calc (Z.card : ℚ≥0) * p ≤ G.totalDegree * p ^ 2 := h1
        _ = (G.totalDegree * p) * p := by ring
    exact le_of_mul_le_mul_right h2 hp0
  have hZn : Z.card ≤ G.totalDegree * p := by exact_mod_cast hZle
  have hinj : Set.InjOn (fun q : ZMod p × ZMod p => (![q.1, q.2] : Fin 2 → ZMod p)) I := by
    intro q _ q' _ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext h0 h1
  have hle : I.card ≤ Z.card := by
    refine Finset.card_le_card_of_injOn _ (fun q hq => ?_) hinj
    simp [hZ, hI q hq]
  exact hle.trans (hZn.trans (Nat.mul_le_mul_right _ hd))

/-- If `p ∤ ∂F(ξ)` for some `ξ`, then `F` is nonzero mod `p`. -/
theorem map_ne_zero_of_not_dvd {F : MvPolynomial (Fin 2) ℤ} {p : ℕ} {ξ : Fin 2 → ℤ}
    (h : ¬ (p : ℤ) ∣ eval ξ (pderiv 1 F)) : map (Int.castRingHom (ZMod p)) F ≠ 0 := by
  intro h0
  obtain ⟨Q, rfl⟩ := (C_dvd_iff_zmod p F).mpr h0
  apply h
  simp

/-- Reduction of `eval` modulo `p`. -/
theorem eval_map_zmod (F : MvPolynomial (Fin 2) ℤ) (p : ℕ) (ξ : Fin 2 → ℤ) :
    eval ![(ξ 0 : ZMod p), (ξ 1 : ZMod p)] (map (Int.castRingHom (ZMod p)) F) =
      ((eval ξ F : ℤ) : ZMod p) := by
  have := OVNS.Quant.eval_map_comp (Int.castRingHom (ZMod p)) ξ F
  simp only [eq_intCast] at this
  rw [← this]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- **The count for one prime**: integer zeros nonsingular mod `p` number at most
`(d·p)(d·D)`. -/
theorem nonsing_card_le {F : MvPolynomial (Fin 2) ℤ}
    (hirr : Irreducible (map (Int.castRingHom ℚ) F)) {a b : ℝ} (hb : 0 < b) {e : Fin 2 →₀ ℕ}
    (he : IsTop a b (map (Int.castRingHom ℚ) F).support e) {p : ℕ} (hp : p.Prime)
    (S : Finset (Fin 2 → ℤ)) (hz : ∀ ξ ∈ S, eval ξ F = 0) (B₀ B₁ : ℝ)
    (hB₀ : ∀ ξ ∈ S, |(ξ 0 : ℝ)| ≤ B₀) (hB₁ : ∀ ξ ∈ S, |(ξ 1 : ℝ)| ≤ B₁)
    (E : Finset (ℕ × ℕ)) (D d : ℕ) (hE : ∀ m ∈ E, ¬ (e 0 ≤ m.1 ∧ e 1 ≤ m.2))
    (hED : ∀ m ∈ E, m.1 + m.2 ≤ D) (hd : F.totalDegree ≤ d)
    (hdq : (map (Int.castRingHom ℚ) F).totalDegree ≤ d)
    (hsize : ((E.card).factorial : ℝ) * ∏ m ∈ E, (B₀ ^ m.1 * B₁ ^ m.2) <
      (p : ℝ) ^ (E.card * (E.card - 1) / 2)) :
    (S.filter fun ξ => ¬ (p : ℤ) ∣ eval ξ (pderiv 1 F)).card ≤ (d * D) * (d * p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set S' := S.filter fun ξ => ¬ (p : ℤ) ∣ eval ξ (pderiv 1 F) with hS'
  rcases S'.eq_empty_or_nonempty with h0 | ⟨ξ₀, hξ₀⟩
  · rw [h0]; simp
  have hne : map (Int.castRingHom (ZMod p)) F ≠ 0 :=
    map_ne_zero_of_not_dvd (Finset.mem_filter.mp hξ₀).2
  let π : (Fin 2 → ℤ) → ZMod p × ZMod p := fun ξ => ((ξ 0 : ZMod p), (ξ 1 : ZMod p))
  have hfib : ∀ q ∈ S'.image π, (S'.filter fun ξ => π ξ = q).card ≤ d * D := by
    intro q hq
    obtain ⟨ξ₁, hξ₁, rfl⟩ := Finset.mem_image.mp hq
    have hξ₁' := Finset.mem_filter.mp hξ₁
    have hdz : ¬ (p : ℤ) ∣ eval ![ξ₁ 0, ξ₁ 1] (pderiv 1 F) := by
      rw [pt_eta]; exact hξ₁'.2
    have hsub : ∀ ξ ∈ S'.filter (fun ξ => π ξ = π ξ₁), ξ ∈ S ∧ π ξ = π ξ₁ := fun ξ hξ => by
      have := Finset.mem_filter.mp hξ
      exact ⟨(Finset.mem_filter.mp this.1).1, this.2⟩
    have hmod : ∀ ξ ∈ S'.filter (fun ξ => π ξ = π ξ₁),
        (p : ℤ) ∣ ξ 0 - ξ₁ 0 ∧ (p : ℤ) ∣ ξ 1 - ξ₁ 1 := fun ξ hξ => by
      have h := (hsub ξ hξ).2
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp only [π] at h0 h1
      exact ⟨by
        have := (ZMod.intCast_eq_intCast_iff_dvd_sub (ξ₁ 0) (ξ 0) p).mp h0.symm
        exact this, by
        have := (ZMod.intCast_eq_intCast_iff_dvd_sub (ξ₁ 1) (ξ 1) p).mp h1.symm
        exact this⟩
    have := class_card_le hirr hb he hp (ξ₁ 0) (ξ₁ 1) hdz (S'.filter fun ξ => π ξ = π ξ₁)
      (fun ξ hξ => hz ξ (hsub ξ hξ).1) (fun ξ hξ => (hmod ξ hξ).1) (fun ξ hξ => (hmod ξ hξ).2)
      B₀ B₁ (fun ξ hξ => hB₀ ξ (hsub ξ hξ).1) (fun ξ hξ => hB₁ ξ (hsub ξ hξ).1) E D hE hED hsize
    exact this.trans (Nat.mul_le_mul_right _ hdq)
  have himg : (S'.image π).card ≤ d * p := by
    have hdeg : (map (Int.castRingHom (ZMod p)) F).totalDegree ≤ d :=
      (Finset.sup_mono (support_map_subset _ _)).trans hd
    refine card_points_le hne hdeg _ fun q hq => ?_
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hq
    have := eval_map_zmod F p ξ
    simp only [π]
    rw [this, hz ξ (Finset.mem_filter.mp hξ).1]
    simp
  exact (Finset.card_le_mul_card_image S' _ hfib).trans (Nat.mul_le_mul_left _ himg)

end OnePrime

/-! ## height reduction -/

section HeightReduction
open MvPolynomial
attribute [local instance] Matrix.seminormedAddCommGroup

/-- Exponents of degree `≤ d`. -/
def lowMon (d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (d + 1) ×ˢ Finset.range (d + 1)).filter fun m => m.1 + m.2 ≤ d

theorem mem_lowMon {d : ℕ} {m : ℕ × ℕ} : m ∈ lowMon d ↔ m.1 + m.2 ≤ d := by
  simp only [lowMon, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem card_lowMon_le (d : ℕ) : (lowMon d).card ≤ (d + 1) ^ 2 := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp [sq]

/-- Exponent of a degree-`≤ d` monomial of `H`. -/
theorem exists_low_of_mem {R : Type*} [CommRing R] {H : MvPolynomial (Fin 2) R} {d : ℕ}
    (hd : H.totalDegree ≤ d) {m : Fin 2 →₀ ℕ} (hm : m ∈ H.support) :
    ∃ m' ∈ lowMon d, ex m' = m := by
  refine ⟨(m 0, m 1), mem_lowMon.mpr ?_, ?_⟩
  · have h := le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h
    exact h.trans hd
  · ext i
    fin_cases i <;> simp

/-- Expansion of a polynomial of degree `≤ d` along `lowMon d`. -/
theorem eval_eq_sum_low {R : Type*} [CommRing R] {H : MvPolynomial (Fin 2) R} {d : ℕ}
    (hd : H.totalDegree ≤ d) (x : Fin 2 → R) :
    eval x H = ∑ m ∈ lowMon d, H.coeff (ex m) * (x 0 ^ m.1 * x 1 ^ m.2) := by
  classical
  rw [eval_eq']
  have himg : Finset.sum (lowMon d) (fun m => H.coeff (ex m) * (x 0 ^ m.1 * x 1 ^ m.2)) =
      Finset.sum ((lowMon d).image ex)
        (fun m => H.coeff m * ∏ i, x i ^ m i) := by
    rw [Finset.sum_image (fun a _ b _ h => ex_injective h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [Fin.prod_univ_two]
  rw [himg]
  refine Finset.sum_subset (fun m hm => ?_) (fun m _ hm => ?_)
  · obtain ⟨m', hm', rfl⟩ := exists_low_of_mem hd hm
    exact Finset.mem_image_of_mem _ hm'
  · rw [notMem_support_iff.mp hm, zero_mul]

variable {d : ℕ}

/-- The integer row. -/
def rowZ (d : ℕ) (ξ : Fin 2 → ℤ) : lowMon d → ℤ := fun m => ξ 0 ^ m.1.1 * ξ 1 ^ m.1.2

/-- The functional `r ↦ ∑ r m * v m`. -/
noncomputable def pair (v : lowMon d → ℚ) : (lowMon d → ℚ) →ₗ[ℚ] ℚ :=
  ∑ m, v m • LinearMap.proj m

theorem pair_apply (v r : lowMon d → ℚ) : pair v r = ∑ m, r m * v m := by
  simp [pair, LinearMap.sum_apply, mul_comm]

theorem pair_single (v : lowMon d → ℚ) (m : lowMon d) : pair v (Pi.single m 1) = v m := by
  classical
  rw [pair_apply, Finset.sum_eq_single m]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem pair_ne_zero {v : lowMon d → ℚ} (hv : v ≠ 0) : pair v ≠ 0 := by
  intro h
  apply hv
  funext m
  have := pair_single v m
  rw [h] at this
  simpa using this.symm

/-- The integer polynomial attached to an integer vector. -/
noncomputable def polyZ (t : lowMon d → ℤ) : MvPolynomial (Fin 2) ℤ :=
  ∑ m : lowMon d, monomial (ex m.1) (t m)

theorem coeff_polyZ (t : lowMon d → ℤ) (m : lowMon d) : (polyZ t).coeff (ex m.1) = t m := by
  classical
  unfold polyZ
  rw [coeff_sum, Finset.sum_eq_single m]
  · simp
  · intro k _ hk
    rw [coeff_monomial, ite_eq_right_iff]
    exact fun h => absurd (Subtype.ext (ex_injective h)) hk
  · simp

theorem coeff_polyZ_of_ne (t : lowMon d → ℤ) (m' : Fin 2 →₀ ℕ) (h : ∀ m : lowMon d, ex m.1 ≠ m') :
    (polyZ t).coeff m' = 0 := by
  classical
  unfold polyZ
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [coeff_monomial, ite_eq_right_iff]
  exact fun h' => absurd h' (h m)

theorem eval_polyZ (t : lowMon d → ℤ) (ξ : Fin 2 → ℤ) :
    eval ξ (polyZ t) = ∑ m, rowZ d ξ m * t m := by
  unfold polyZ
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp [rowZ]
  ring

theorem totalDegree_polyZ_le (t : lowMon d → ℤ) : (polyZ t).totalDegree ≤ d := by
  unfold polyZ
  refine totalDegree_finsetSum_le fun m _ => (totalDegree_monomial_le _ _).trans ?_
  have h1 : ((ex m.1).sum fun _ => id) = m.1.1 + m.1.2 := ex_sum m.1
  rw [h1]
  exact mem_lowMon.mp m.2

/-- **Height reduction.** -/
theorem height_reduction {F : MvPolynomial (Fin 2) ℤ}
    (hirr : Irreducible (map (Int.castRingHom ℚ) F))
    (hd : (map (Int.castRingHom ℚ) F).totalDegree = d) (S : Finset (Fin 2 → ℤ))
    (hz : ∀ ξ ∈ S, eval ξ F = 0) (B : ℝ) (hB : 1 ≤ B) (hbox : ∀ ξ ∈ S, ∀ i, |(ξ i : ℝ)| ≤ B)
    (hcard : d ^ 2 < S.card) :
    ∃ (F' : MvPolynomial (Fin 2) ℤ) (q : ℚ), q ≠ 0 ∧
      map (Int.castRingHom ℚ) F' = C q * map (Int.castRingHom ℚ) F ∧
      ∀ m, |(F'.coeff m : ℝ)| ≤ ((((d + 1) ^ 2 : ℕ) : ℝ) * B ^ d) ^ ((d + 1) ^ 2) := by
  classical
  set Fq := map (Int.castRingHom ℚ) F with hFq
  set rowQ : (Fin 2 → ℤ) → (lowMon d → ℚ) := fun ξ m => (rowZ d ξ m : ℚ) with hrowQ
  have hcast : ∀ ξ : Fin 2 → ℤ, eval (fun i => (ξ i : ℚ)) Fq = (eval ξ F : ℚ) := fun ξ => by
    have := OVNS.Quant.eval_map_comp (Int.castRingHom ℚ) ξ F
    simp only [eq_intCast] at this
    exact this
  -- the coefficient vector of `F`
  set c : lowMon d → ℚ := fun m => Fq.coeff (ex m.1) with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hirr.ne_zero
    ext m'
    by_cases hm : m' ∈ Fq.support
    · obtain ⟨m, hm', rfl⟩ := exists_low_of_mem hd.le hm
      simpa [hc] using congrFun h ⟨m, hm'⟩
    · simpa using notMem_support_iff.mp hm
  set T : Set (lowMon d → ℚ) := rowQ '' (S : Set (Fin 2 → ℤ)) with hT
  have hTc : Submodule.span ℚ T ≤ LinearMap.ker (pair c) := by
    rw [Submodule.span_le]
    rintro _ ⟨ξ, hξ, rfl⟩
    have h1 := eval_eq_sum_low hd.le (fun i => (ξ i : ℚ))
    rw [hcast, hz ξ hξ] at h1
    simp only [SetLike.mem_coe, LinearMap.mem_ker, pair_apply]
    rw [← Finset.sum_coe_sort (lowMon d)] at h1
    simp only [Int.cast_zero] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [hrowQ, rowZ, hc, mul_comm]
  obtain ⟨b, hbT, hbspan, hbli⟩ := exists_linearIndependent ℚ T
  have hfin : Finite b := hbli.finite
  let _ : Fintype b := Fintype.ofFinite _
  have hcardb : Fintype.card b < Fintype.card (lowMon d) := by
    have h1 := finrank_span_eq_card hbli
    have h2 : Submodule.span ℚ (Set.range ((↑) : b → (lowMon d → ℚ))) ≠ ⊤ := by
      intro htop
      apply pair_ne_zero hc0
      have h3 : (⊤ : Submodule ℚ (lowMon d → ℚ)) ≤ LinearMap.ker (pair c) := by
        rw [← htop, Subtype.range_coe, hbspan]
        exact hTc
      exact LinearMap.ker_eq_top.mp (top_le_iff.mp h3)
    have h3 := Submodule.finrank_lt h2
    rw [Module.finrank_fintype_fun_eq_card, h1] at h3
    convert h3
  -- nonempty
  obtain ⟨ξ₀, hξ₀⟩ : S.Nonempty := by
    rw [← Finset.card_pos]; omega
  have hmem0 : ((0, 0) : ℕ × ℕ) ∈ lowMon d := mem_lowMon.mpr (by simp)
  have hrow0 : rowQ ξ₀ ≠ 0 := by
    intro h
    have := congrFun h ⟨(0, 0), hmem0⟩
    simp [hrowQ, rowZ] at this
  have hbpos : 0 < Fintype.card b := by
    by_contra h0
    have hemp : IsEmpty b := Fintype.card_eq_zero_iff.mp (by omega)
    have hb0 : b = ∅ := Set.isEmpty_coe_sort.mp hemp
    have : rowQ ξ₀ ∈ Submodule.span ℚ T := Submodule.subset_span ⟨ξ₀, hξ₀, rfl⟩
    rw [← hbspan, hb0, Submodule.span_empty, Submodule.mem_bot] at this
    exact hrow0 this
  -- integer rows for the elements of `b`
  have hch : ∀ v : b, ∃ ξ ∈ S, rowQ ξ = (v : lowMon d → ℚ) := fun v => by
    obtain ⟨ξ, hξ, h⟩ := hbT v.2
    exact ⟨ξ, hξ, h⟩
  choose ξv hξvS hξv using hch
  let A : Matrix b (lowMon d) ℤ := Matrix.of fun v m => rowZ d (ξv v) m
  obtain ⟨t, ht0, hAt, htn⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A hcardb hbpos
  -- `t` kills all rows
  have htq0 : (fun m => (t m : ℚ)) ≠ 0 := fun h => ht0 (by
    funext m
    have := congrFun h m
    simpa using this)
  have hkill : ∀ ξ ∈ S, eval ξ (polyZ t) = 0 := by
    intro ξ hξ
    have hle : Submodule.span ℚ b ≤ LinearMap.ker (pair fun m => (t m : ℚ)) := by
      rw [Submodule.span_le]
      intro v hv
      have h1 := congrFun hAt ⟨v, hv⟩
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
      simp only [SetLike.mem_coe, LinearMap.mem_ker, pair_apply]
      have e : v = rowQ (ξv ⟨v, hv⟩) := (hξv ⟨v, hv⟩).symm
      rw [e]
      have h2 : (∑ m, rowQ (ξv ⟨v, hv⟩) m * (t m : ℚ)) =
          ((∑ m, A ⟨v, hv⟩ m * t m : ℤ) : ℚ) := by
        push_cast
        rfl
      rw [h2, h1]
      simp
    have hmem : rowQ ξ ∈ Submodule.span ℚ b := by
      rw [hbspan]; exact Submodule.subset_span ⟨ξ, hξ, rfl⟩
    have h3 := hle hmem
    simp only [LinearMap.mem_ker, pair_apply] at h3
    rw [eval_polyZ]
    have h4 : ((∑ m, rowZ d ξ m * t m : ℤ) : ℚ) = 0 := by
      push_cast
      exact h3
    exact_mod_cast h4
  set G := polyZ t with hG
  set Gq := map (Int.castRingHom ℚ) G with hGq
  have hGne : Gq ≠ 0 := by
    intro h0
    apply ht0
    funext m
    have h1 := coeff_polyZ t m
    have h2 : (Gq.coeff (ex m.1)) = ((G.coeff (ex m.1) : ℤ) : ℚ) := by
      rw [hGq, coeff_map]; simp
    rw [h0, coeff_polyZ t m] at h2
    simpa using h2.symm
  have hGdeg : Gq.totalDegree ≤ d :=
    (Finset.sup_mono (support_map_subset _ _)).trans (totalDegree_polyZ_le t)
  -- divisibility, by Bézout
  have hdvd : Fq ∣ Gq := by
    by_contra hnd
    have hrel : IsRelPrime Fq Gq := hirr.isRelPrime_iff_not_dvd.mpr hnd
    have hinj : Function.Injective (fun (ξ : Fin 2 → ℤ) (i : Fin 2) => (ξ i : ℚ)) := by
      intro ξ ξ' h
      funext i
      simpa using congrFun h i
    have hbz := OVNS.Quant.plane_bezout Fq Gq hrel hirr.ne_zero hGne
      (S.image fun (ξ : Fin 2 → ℤ) (i : Fin 2) => (ξ i : ℚ)) (by
        intro x hx
        obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hx
        constructor
        · rw [hcast, hz ξ hξ]; simp
        · have := OVNS.Quant.eval_map_comp (Int.castRingHom ℚ) ξ G
          simp only [eq_intCast] at this
          rw [hGq, this, hkill ξ hξ]
          simp)
    rw [Finset.card_image_of_injective _ hinj, hd] at hbz
    have : d * Gq.totalDegree ≤ d * d := Nat.mul_le_mul_left _ hGdeg
    nlinarith
  obtain ⟨Q, hQ⟩ := hdvd
  have hQ0 : Q ≠ 0 := right_ne_zero_of_mul (hQ ▸ hGne)
  have hdeg := totalDegree_mul_of_isDomain hirr.ne_zero hQ0
  rw [← hQ, hd] at hdeg
  have hQdeg : Q.totalDegree = 0 := by omega
  have hq' : Q = C (Q.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hQdeg
  set q := Q.coeff 0 with hqdef
  have hqne : q ≠ 0 := by
    intro h0
    apply hQ0
    rw [hq', h0]; simp
  refine ⟨G, q, hqne, ?_, ?_⟩
  · rw [← hGq, hQ, hq', mul_comm]
  · intro m'
    set n := Fintype.card (lowMon d) with hn
    have hnle : n ≤ (d + 1) ^ 2 := by
      rw [hn, Fintype.card_coe]
      exact card_lowMon_le d
    have hnpos : 0 < n := by omega
    have hBd : (1 : ℝ) ≤ B ^ d := one_le_pow₀ hB
    have hAle : ‖A‖ ≤ B ^ d := by
      rw [Matrix.norm_le_iff (by positivity)]
      intro v m
      simp only [A, Matrix.of_apply, rowZ, Int.norm_eq_abs]
      push_cast
      rw [abs_mul, abs_pow, abs_pow]
      have h1 := hbox _ (hξvS v) 0
      have h2 := hbox _ (hξvS v) 1
      have h3 : m.1.1 + m.1.2 ≤ d := mem_lowMon.mp m.2
      calc |((ξv v 0 : ℤ) : ℝ)| ^ m.1.1 * |((ξv v 1 : ℤ) : ℝ)| ^ m.1.2
          ≤ B ^ m.1.1 * B ^ m.1.2 :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 _)
              (pow_le_pow_left₀ (abs_nonneg _) h2 _) (by positivity) (by positivity)
        _ = B ^ (m.1.1 + m.1.2) := (pow_add _ _ _).symm
        _ ≤ B ^ d := pow_le_pow_right₀ hB h3
    have hbase : (1 : ℝ) ≤ (n : ℝ) * max 1 ‖A‖ := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have h2 : (1 : ℝ) ≤ max 1 ‖A‖ := le_max_left _ _
      nlinarith
    have hmax : max 1 ‖A‖ ≤ B ^ d := max_le hBd hAle
    have hexp : ((Fintype.card b : ℝ) / ((n : ℝ) - Fintype.card b)) ≤ ((d + 1) ^ 2 : ℕ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) - Fintype.card b := by
        have : (Fintype.card b : ℝ) + 1 ≤ n := by exact_mod_cast hcardb
        linarith
      have h2 : (Fintype.card b : ℝ) ≤ n := by exact_mod_cast hcardb.le
      have h3 : (n : ℝ) ≤ ((d + 1) ^ 2 : ℕ) := by exact_mod_cast hnle
      calc (Fintype.card b : ℝ) / ((n : ℝ) - Fintype.card b) ≤ Fintype.card b :=
            div_le_self (by positivity) h1
        _ ≤ _ := h2.trans h3
    have hnorm : ‖t‖ ≤ (((d + 1) ^ 2 : ℕ) * B ^ d) ^ ((d + 1) ^ 2) := by
      calc ‖t‖ ≤ ((n : ℝ) * max 1 ‖A‖) ^ ((Fintype.card b : ℝ) / ((n : ℝ) - Fintype.card b)) := htn
        _ ≤ ((n : ℝ) * max 1 ‖A‖) ^ (((d + 1) ^ 2 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hbase hexp
        _ = ((n : ℝ) * max 1 ‖A‖) ^ ((d + 1) ^ 2) := Real.rpow_natCast _ _
        _ ≤ (((d + 1) ^ 2 : ℕ) * B ^ d) ^ ((d + 1) ^ 2) := by
            refine pow_le_pow_left₀ (by positivity) ?_ _
            exact mul_le_mul (by exact_mod_cast hnle) hmax (by positivity) (by positivity)
    by_cases hm : ∃ m : lowMon d, ex m.1 = m'
    · obtain ⟨m, rfl⟩ := hm
      rw [hG, coeff_polyZ]
      have := norm_le_pi_norm t m
      simp only [Int.norm_eq_abs] at this
      exact this.trans hnorm
    · push Not at hm
      rw [hG, coeff_polyZ_of_ne t m' hm]
      simp only [Int.cast_zero, abs_zero]
      positivity

end HeightReduction

/-! ## the L-shaped exponent set and the size inequality -/

section LShape
open Finset

/-- The L-shape: `e0` columns of height `u` and `e1` rows of length `v`. -/
def lShape (e0 e1 u v : ℕ) : Finset (ℕ × ℕ) :=
  (range e0 ×ˢ range u) ∪ (Ico e0 (e0 + v) ×ˢ range e1)

theorem lShape_disjoint (e0 e1 u v : ℕ) :
    Disjoint (range e0 ×ˢ range u) (Ico e0 (e0 + v) ×ˢ range e1) := by
  rw [Finset.disjoint_left]
  rintro ⟨i, j⟩ h1 h2
  simp only [mem_product, mem_range, mem_Ico] at h1 h2
  omega

theorem card_lShape (e0 e1 u v : ℕ) : (lShape e0 e1 u v).card = e0 * u + e1 * v := by
  rw [lShape, card_union_of_disjoint (lShape_disjoint e0 e1 u v), card_product, card_product]
  simp only [card_range, Nat.card_Ico, add_tsub_cancel_left]
  ring

theorem lShape_avoid {e0 e1 u v : ℕ} {m : ℕ × ℕ} (hm : m ∈ lShape e0 e1 u v) :
    ¬ (e0 ≤ m.1 ∧ e1 ≤ m.2) := by
  simp only [lShape, mem_union, mem_product, mem_range, mem_Ico] at hm
  omega

theorem lShape_deg {e0 e1 u v : ℕ} {m : ℕ × ℕ} (hm : m ∈ lShape e0 e1 u v) :
    m.1 + m.2 ≤ e0 + e1 + u + v := by
  simp only [lShape, mem_union, mem_product, mem_range, mem_Ico] at hm
  omega

theorem gauss (n : ℕ) : ∑ i ∈ range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Closed form of the total weight. -/
theorem sum_lShape (a b : ℝ) (e0 e1 u v : ℕ) :
    ∑ m ∈ lShape e0 e1 u v, ((m.1 : ℝ) * a + (m.2 : ℝ) * b) =
      a * u * (e0 * (e0 - 1) / 2) + b * e0 * (u * (u - 1) / 2) +
        a * e1 * (e0 * v + v * (v - 1) / 2) + b * v * (e1 * (e1 - 1) / 2) := by
  rw [lShape, sum_union (lShape_disjoint e0 e1 u v), sum_product, sum_product]
  have h1 : ∑ i ∈ range e0, ∑ j ∈ range u, ((i : ℝ) * a + (j : ℝ) * b) =
      a * u * (e0 * (e0 - 1) / 2) + b * e0 * (u * (u - 1) / 2) := by
    have : ∀ i ∈ range e0, ∑ j ∈ range u, ((i : ℝ) * a + (j : ℝ) * b) =
        (a * u) * (i : ℝ) + b * (u * (u - 1) / 2) := by
      intro i _
      rw [sum_add_distrib, sum_const, ← sum_mul, gauss]
      simp only [card_range, nsmul_eq_mul]
      ring
    rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, gauss, sum_const]
    simp only [card_range, nsmul_eq_mul]
    ring
  have h2 : ∑ i ∈ Ico e0 (e0 + v), ∑ j ∈ range e1, ((i : ℝ) * a + (j : ℝ) * b) =
      a * e1 * (e0 * v + v * (v - 1) / 2) + b * v * (e1 * (e1 - 1) / 2) := by
    rw [sum_Ico_eq_sum_range]
    simp only [add_tsub_cancel_left]
    have : ∀ k ∈ range v, ∑ j ∈ range e1, (((e0 + k : ℕ) : ℝ) * a + (j : ℝ) * b) =
        (a * e1 * e0 + b * (e1 * (e1 - 1) / 2)) + (a * e1) * (k : ℝ) := by
      intro k _
      rw [sum_add_distrib, sum_const, ← sum_mul, gauss]
      simp only [card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, gauss, sum_const]
    simp only [card_range, nsmul_eq_mul]
    ring
  simp only at h1 h2 ⊢
  rw [h1, h2]
  ring

/-- **Main size inequality**: `2W ≤ (ab/τ) s² + 3 d b s`. -/
theorem two_W_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {e0 e1 u v d : ℕ} (hd : e0 + e1 ≤ d)
    (he : 1 ≤ e0 + e1) (hs : 1 ≤ e0 * u + e1 * v) (h1 : 0 ≤ a * v - b * u)
    (h2 : a * v - b * u ≤ a) :
    2 * ∑ m ∈ lShape e0 e1 u v, ((m.1 : ℝ) * a + (m.2 : ℝ) * b) ≤
      a * b / (e0 * a + e1 * b) * ((e0 * u + e1 * v : ℕ) : ℝ) ^ 2 +
        3 * d * b * ((e0 * u + e1 * v : ℕ) : ℝ) := by
  rw [sum_lShape]
  push_cast
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set E0 : ℝ := (e0 : ℝ) with hE0
  set E1 : ℝ := (e1 : ℝ) with hE1
  set U : ℝ := (u : ℝ) with hU
  set V : ℝ := (v : ℝ) with hV
  set D : ℝ := (d : ℝ) with hD
  have hE0n : 0 ≤ E0 := Nat.cast_nonneg _
  have hE1n : 0 ≤ E1 := Nat.cast_nonneg _
  have hUn : 0 ≤ U := Nat.cast_nonneg _
  have hVn : 0 ≤ V := Nat.cast_nonneg _
  have hdE : E0 + E1 ≤ D := by rw [hE0, hE1, hD]; exact_mod_cast hd
  have heE : 1 ≤ E0 + E1 := by rw [hE0, hE1]; exact_mod_cast he
  set s : ℝ := E0 * U + E1 * V with hsdef
  have hs1 : 1 ≤ s := by
    have : ((e0 * u + e1 * v : ℕ) : ℝ) = s := by push_cast; rfl
    rw [← this]
    exact_mod_cast hs
  set τ : ℝ := E0 * a + E1 * b with hτ
  have hτge : a ≤ τ := by
    have : a * (E0 + E1) ≤ τ := by
      have := mul_nonneg hE1n (sub_nonneg.mpr hab)
      nlinarith
    nlinarith
  have hτpos : 0 < τ := lt_of_lt_of_le ha hτge
  -- the cross-term identity
  have hid : (b * E0 * U ^ 2 + a * E1 * V ^ 2) * τ =
      a * b * s ^ 2 + E0 * E1 * (b * U - a * V) ^ 2 := by
    rw [hτ, hsdef]; ring
  have hsq : (b * U - a * V) ^ 2 ≤ a ^ 2 := by
    have : (a * V - b * U) ^ 2 ≤ a ^ 2 := by
      have := mul_nonneg h1 (sub_nonneg.mpr h2)
      nlinarith
    nlinarith
  have hE0le : E0 ≤ D := by linarith
  have hE1le : E1 ≤ D := by linarith
  -- the remainder
  set R : ℝ := a * U * E0 ^ 2 + 2 * a * E0 * E1 * V + b * V * E1 ^ 2 with hR
  have hR2 : R ≤ 2 * D * b * s := by
    have h3 : a * U * E0 ^ 2 ≤ b * U * E0 * D := by
      have h4 : a * U * E0 ≤ b * U * E0 := by
        have := mul_nonneg hUn hE0n
        nlinarith
      have h5 := mul_le_mul h4 hE0le hE0n (by positivity)
      nlinarith
    have h6 : 2 * a * E0 * E1 * V + b * V * E1 ^ 2 ≤ 2 * b * V * E1 * D := by
      have h7 : 2 * a * E0 * E1 * V ≤ 2 * b * E0 * E1 * V := by
        have := mul_nonneg (mul_nonneg hE0n hE1n) hVn
        nlinarith
      have h8 : 2 * b * E0 * E1 * V + b * V * E1 ^ 2 = b * V * E1 * (2 * E0 + E1) := by ring
      have h9 : b * V * E1 * (2 * E0 + E1) ≤ b * V * E1 * (2 * D) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have h10 : 0 ≤ b * U * E0 * D := by
      have : 0 ≤ D := by linarith
      positivity
    have h11 : 2 * D * b * s = 2 * (b * U * E0 * D) + 2 * b * V * E1 * D := by
      rw [hsdef]; ring
    linarith
  have hW : 2 * (a * U * (E0 * (E0 - 1) / 2) + b * E0 * (U * (U - 1) / 2) +
        a * E1 * (E0 * V + V * (V - 1) / 2) + b * V * (E1 * (E1 - 1) / 2)) ≤
      (b * E0 * U ^ 2 + a * E1 * V ^ 2) + R := by
    have h3 : 0 ≤ a * U * E0 := by positivity
    have h4 : 0 ≤ b * E0 * U := by positivity
    have h5 : 0 ≤ a * E1 * V := by positivity
    have h6 : 0 ≤ b * V * E1 := by positivity
    have : 2 * (a * U * (E0 * (E0 - 1) / 2) + b * E0 * (U * (U - 1) / 2) +
        a * E1 * (E0 * V + V * (V - 1) / 2) + b * V * (E1 * (E1 - 1) / 2)) =
      (b * E0 * U ^ 2 + a * E1 * V ^ 2) + R - a * U * E0 - b * E0 * U - a * E1 * V - b * V * E1 := by
      rw [hR]; ring
    linarith
  have hcross : E0 * E1 * (b * U - a * V) ^ 2 ≤ τ * (D * b * s) := by
    have h3 : E0 * E1 * (b * U - a * V) ^ 2 ≤ E0 * E1 * a ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h4 : E0 * a ≤ τ := by
      have : 0 ≤ E1 * b := by positivity
      linarith
    have h5 : E1 * a ≤ D * b * s := by
      have h6 : E1 * a ≤ D * b := mul_le_mul hE1le hab ha.le (by linarith)
      have h7 : 0 ≤ D * b := by
        have : 0 ≤ D := by linarith
        positivity
      exact h6.trans (le_mul_of_one_le_right h7 hs1)
    calc E0 * E1 * (b * U - a * V) ^ 2 ≤ E0 * E1 * a ^ 2 := h3
      _ = (E0 * a) * (E1 * a) := by ring
      _ ≤ τ * (D * b * s) := mul_le_mul h4 h5 (by positivity) hτpos.le
  rw [show a * b / τ * s ^ 2 = (a * b * s ^ 2) / τ by ring]
  have hmain : ((b * E0 * U ^ 2 + a * E1 * V ^ 2) + R) ≤
      (a * b * s ^ 2) / τ + 3 * D * b * s := by
    have h3 : (b * E0 * U ^ 2 + a * E1 * V ^ 2) ≤ (a * b * s ^ 2) / τ + D * b * s := by
      rw [← mul_le_mul_iff_left₀ hτpos, hid, add_mul, div_mul_cancel₀ _ hτpos.ne']
      have e : τ * (D * b * s) = D * b * s * τ := by ring
      linarith
    linarith
  exact hW.trans hmain

/-- The size hypothesis of the determinant lemma, from the logarithmic inequality. -/
theorem hsize_of_good {a b η : ℝ} (ha : Real.log 2 ≤ a) (hab : a ≤ b)
    {e0 e1 u v d : ℕ} (hd : e0 + e1 ≤ d) (he : 1 ≤ e0 + e1)
    (h1 : 0 ≤ a * v - b * u) (h2 : a * v - b * u ≤ a)
    (hs2 : 2 ≤ e0 * u + e1 * v)
    (hgood : 2 * Real.log ((e0 * u + e1 * v : ℕ) : ℝ) + (3 * d + 1) * Real.log 2 ≤
      (((e0 * u + e1 * v : ℕ) : ℝ) - 1) * η * Real.log 2)
    {p : ℕ} (hp : Real.exp (a * b / (e0 * a + e1 * b) + η * b) < p) :
    (((lShape e0 e1 u v).card.factorial : ℕ) : ℝ) *
        ∏ m ∈ lShape e0 e1 u v, (Real.exp a ^ m.1 * Real.exp b ^ m.2) <
      (p : ℝ) ^ ((lShape e0 e1 u v).card * ((lShape e0 e1 u v).card - 1) / 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le hl2 ha
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  rw [card_lShape]
  set s := e0 * u + e1 * v with hs
  set W := ∑ m ∈ lShape e0 e1 u v, ((m.1 : ℝ) * a + (m.2 : ℝ) * b) with hW
  have hprod : ∏ m ∈ lShape e0 e1 u v, (Real.exp a ^ m.1 * Real.exp b ^ m.2) = Real.exp W := by
    rw [hW, Real.exp_sum]
    refine prod_congr rfl fun m _ => ?_
    rw [Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  rw [hprod]
  set τ : ℝ := e0 * a + e1 * b with hτ
  set L : ℝ := a * b / τ + η * b with hL
  have hW2 := two_W_le ha0 hab hd he (by omega) h1 h2
  rw [← hs, ← hW, ← hτ] at hW2
  set S : ℝ := (s : ℝ) with hS
  have hS2 : (2 : ℝ) ≤ S := by rw [hS]; exact_mod_cast hs2
  have hk : (((s * (s - 1) / 2 : ℕ)) : ℝ) = S * (S - 1) / 2 := by
    have heven : 2 ∣ s * (s - 1) := by
      have := Nat.even_mul_pred_self s
      exact this.two_dvd
    rw [Nat.cast_div heven (by norm_num)]
    push_cast [Nat.cast_sub (show 1 ≤ s by omega)]
    rfl
  set k := s * (s - 1) / 2 with hkdef
  have hkpos : 0 < k := by
    have : 0 < (k : ℝ) := by
      rw [hk]
      nlinarith
    exact_mod_cast this
  have hτge : a ≤ τ := by
    have h3 : (1 : ℝ) ≤ (e0 : ℝ) + e1 := by exact_mod_cast he
    have h4 : 0 ≤ (e1 : ℝ) * (b - a) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hab)
    have h5 : τ = (e0 + e1 : ℝ) * a + e1 * (b - a) := by rw [hτ]; ring
    nlinarith
  have hτ0 : 0 < τ := lt_of_lt_of_le ha0 hτge
  have habτ : a * b / τ ≤ b := by
    rw [div_le_iff₀ hτ0]
    nlinarith
  have habτ0 : 0 ≤ a * b / τ := by positivity
  -- the logarithmic inequality
  have hlog : 2 * Real.log S + (3 * d + 1) * b + a * b / τ ≤ (S - 1) * η * b + a * b / τ := by
    set r := b / Real.log 2 with hr
    have hr1 : 1 ≤ r := by
      rw [hr, le_div_iff₀ hl2]
      linarith
    have hrb : r * Real.log 2 = b := by
      rw [hr]; field_simp
    have hlogS : 0 ≤ Real.log S := Real.log_nonneg (by linarith)
    have h3 : 2 * Real.log S ≤ r * (2 * Real.log S) := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left hgood (by linarith : (0 : ℝ) ≤ r)
    have h5 : r * ((S - 1) * η * Real.log 2) = (S - 1) * η * b := by
      rw [← hrb]; ring
    have h6 : r * ((3 * d + 1) * Real.log 2) = (3 * d + 1) * b := by
      rw [← hrb]; ring
    rw [mul_add, h5, h6] at h4
    linarith
  have hkey : S * Real.log S + W ≤ (k : ℝ) * L := by
    rw [hk, hL]
    have h3 : 2 * W ≤ a * b / τ * S ^ 2 + 3 * d * b * S := hW2
    have h4 : 2 * Real.log S + 3 * d * b + b ≤ (S - 1) * η * b := by
      have : (3 * (d : ℝ) + 1) * b = 3 * d * b + b := by ring
      linarith
    have h5 : S * (2 * Real.log S + 3 * d * b + a * b / τ) ≤ S * ((S - 1) * η * b) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      linarith
    set A := a * b / τ with hA
    have e1 : S * (S - 1) / 2 * (A + η * b) = (A * S ^ 2 - S * A + S * ((S - 1) * η * b)) / 2 := by
      ring
    have e2 : S * (2 * Real.log S + 3 * d * b + A) =
        2 * (S * Real.log S) + 3 * d * b * S + S * A := by ring
    rw [e1]
    rw [e2] at h5
    linarith
  have hfac : ((s.factorial : ℕ) : ℝ) ≤ Real.exp (S * Real.log S) := by
    have h3 : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := by exact_mod_cast Nat.factorial_le_pow s
    have h4 : (0 : ℝ) < S := by linarith
    rw [mul_comm, Real.exp_mul, Real.exp_log h4, Real.rpow_natCast]
    exact h3
  calc ((s.factorial : ℕ) : ℝ) * Real.exp W ≤ Real.exp (S * Real.log S) * Real.exp W :=
        mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le
    _ = Real.exp (S * Real.log S + W) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((k : ℝ) * L) := Real.exp_le_exp.mpr hkey
    _ = Real.exp L ^ k := by rw [Real.exp_nat_mul]
    _ < (p : ℝ) ^ k := pow_lt_pow_left₀ hp (Real.exp_pos _).le hkpos.ne'

end LShape

/-! ## lines, the case without Y, the size of the derivative -/

section Auxiliary
open MvPolynomial

/-- On a vertical line an irreducible curve of degree `d ≥ 2` has `≤ d` points. -/
theorem line_card_le {Fq : MvPolynomial (Fin 2) ℚ} (hirr : Irreducible Fq) {d : ℕ}
    (hd : Fq.totalDegree = d) (hd2 : 2 ≤ d) (c : ℚ) (A : Finset (Fin 2 → ℚ))
    (hA : ∀ x ∈ A, eval x Fq = 0 ∧ x 0 = c) : A.card ≤ d := by
  set L : MvPolynomial (Fin 2) ℚ := X 0 - C c with hL
  have hL0 : L ≠ 0 := by
    intro h
    have := congrArg (eval ![c + 1, 0]) h
    simp [hL] at this
  have hLd : L.totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans (max_le (by simp) (by simp))
  have hnd : ¬ Fq ∣ L := by
    intro h
    have := totalDegree_le_of_dvd_of_isDomain h hL0
    omega
  have hbz := OVNS.Quant.plane_bezout Fq L (hirr.isRelPrime_iff_not_dvd.mpr hnd) hirr.ne_zero hL0 A
    (fun x hx => ⟨(hA x hx).1, by simp [hL, (hA x hx).2]⟩)
  calc A.card ≤ Fq.totalDegree * L.totalDegree := hbz
    _ ≤ d * 1 := Nat.mul_le_mul hd.le hLd
    _ = d := mul_one d

theorem int_pts_inj : Function.Injective (fun (ξ : Fin 2 → ℤ) (i : Fin 2) => (ξ i : ℚ)) := by
  intro ξ ξ' h
  funext i
  simpa using congrFun h i

/-- The cast of an integer zero is a rational zero. -/
theorem eval_cast {F : MvPolynomial (Fin 2) ℤ} (ξ : Fin 2 → ℤ) :
    eval (fun i => (ξ i : ℚ)) (map (Int.castRingHom ℚ) F) = (eval ξ F : ℚ) := by
  have := OVNS.Quant.eval_map_comp (Int.castRingHom ℚ) ξ F
  simp only [eq_intCast] at this
  exact this

/-- The trivial bound: `#S ≤ d (2 B₀ + 1)`. -/
theorem trivial_count {F : MvPolynomial (Fin 2) ℤ}
    (hirr : Irreducible (map (Int.castRingHom ℚ) F)) {d : ℕ}
    (hd : (map (Int.castRingHom ℚ) F).totalDegree = d) (hd2 : 2 ≤ d) (S : Finset (Fin 2 → ℤ))
    (hz : ∀ ξ ∈ S, eval ξ F = 0) (B₀ : ℝ) (hB₀ : 2 ≤ B₀) (hS₀ : ∀ ξ ∈ S, |(ξ 0 : ℝ)| ≤ B₀) :
    (S.card : ℝ) ≤ 3 * d * B₀ := by
  classical
  have hfib : ∀ c ∈ S.image (fun ξ => ξ 0), (S.filter fun ξ => ξ 0 = c).card ≤ d := by
    intro c _
    have h := line_card_le hirr hd hd2 (c : ℚ)
      ((S.filter fun ξ => ξ 0 = c).image fun (ξ : Fin 2 → ℤ) (i : Fin 2) => (ξ i : ℚ)) (by
        intro x hx
        obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hx
        have hξ' := Finset.mem_filter.mp hξ
        constructor
        · rw [eval_cast, hz ξ hξ'.1]; simp
        · simp [hξ'.2])
    rwa [Finset.card_image_of_injective _ int_pts_inj] at h
  have h1 := Finset.card_le_mul_card_image S d hfib
  have h2 : (S.image fun ξ => ξ 0).card ≤ (Finset.Icc (-⌊B₀⌋) ⌊B₀⌋).card := by
    refine Finset.card_le_card fun c hc => ?_
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hc
    have := abs_le.mp (hS₀ ξ hξ)
    rw [Finset.mem_Icc]
    constructor
    · have h3 := Int.le_floor.mpr (show (((-ξ 0 : ℤ)) : ℝ) ≤ B₀ by push_cast; linarith)
      omega
    · exact Int.le_floor.mpr this.2
  have hfl : (0 : ℤ) ≤ ⌊B₀⌋ := Int.floor_nonneg.mpr (by linarith)
  have h3 : (((Finset.Icc (-⌊B₀⌋) ⌊B₀⌋).card : ℕ) : ℝ) = 2 * (⌊B₀⌋ : ℝ) + 1 := by
    rw [Int.card_Icc]
    have e : ⌊B₀⌋ + 1 - -⌊B₀⌋ = 2 * ⌊B₀⌋ + 1 := by ring
    rw [e]
    have h4 := Int.toNat_of_nonneg (show (0 : ℤ) ≤ 2 * ⌊B₀⌋ + 1 by omega)
    have h5 : (((2 * ⌊B₀⌋ + 1).toNat : ℤ) : ℝ) = ((2 * ⌊B₀⌋ + 1 : ℤ) : ℝ) := by rw [h4]
    rw [Int.cast_natCast] at h5
    rw [h5]
    push_cast
    ring
  have h6 : (S.card : ℝ) ≤ d * ((Finset.Icc (-⌊B₀⌋) ⌊B₀⌋).card : ℕ) := by
    exact_mod_cast h1.trans (Nat.mul_le_mul_left _ h2)
  rw [h3] at h6
  have h7 : (⌊B₀⌋ : ℝ) ≤ B₀ := Int.floor_le _
  have h8 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith

/-- If `∂_Y P = 0`, then `P` does not see `Y`. -/
theorem eval_eq_of_pderiv_eq_zero {P : MvPolynomial (Fin 2) ℚ} (h : pderiv 1 P = 0)
    (x y y' : ℚ) : eval ![x, y] P = eval ![x, y'] P := by
  have hm : ∀ m ∈ P.support, m 1 = 0 := by
    intro m hm
    by_contra hne
    apply mem_support_iff.mp hm
    have h1 : (pderiv 1 P).coeff (m - Finsupp.single 1 1) = 0 := by rw [h]; rfl
    rw [coeff_pderiv] at h1
    have hmm : m - Finsupp.single 1 1 + Finsupp.single 1 1 = m := by
      ext j
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply]
      split_ifs with hij
      · subst hij
        omega
      · omega
    rw [hmm] at h1
    exact (mul_eq_zero.1 h1).resolve_right (by positivity)
  rw [eval_eq', eval_eq']
  refine Finset.sum_congr rfl fun m hmem => ?_
  simp [Fin.prod_univ_two, hm m hmem]

/-- A curve of degree `≥ 2` without `Y` has no integer zero. -/
theorem no_zero_of_pderiv_eq_zero {Fq : MvPolynomial (Fin 2) ℚ} (hirr : Irreducible Fq) {d : ℕ}
    (hd : Fq.totalDegree = d) (hd2 : 2 ≤ d) (h : pderiv 1 Fq = 0) (x y : ℚ)
    (hz : eval ![x, y] Fq = 0) : False := by
  classical
  have hinj : Function.Injective (fun i : ℕ => (![x, (i : ℚ)] : Fin 2 → ℚ)) := by
    intro i j hij
    have := congrFun hij 1
    simpa using this
  have hc := line_card_le hirr hd hd2 x
    ((Finset.range (d + 1)).image fun i : ℕ => (![x, (i : ℚ)] : Fin 2 → ℚ)) (by
      intro p hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨by rw [eval_eq_of_pderiv_eq_zero h x (i : ℚ) y, hz], by simp⟩)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at hc
  omega

/-- Size of `∂_Y F` on the box. -/
theorem abs_eval_pderiv_le {F : MvPolynomial (Fin 2) ℤ} {d : ℕ} (hdeg : F.totalDegree ≤ d)
    (H : ℝ) (hH : ∀ m, |(F.coeff m : ℝ)| ≤ H) (B : ℝ) (hB : 1 ≤ B) (ξ : Fin 2 → ℤ)
    (hξ : ∀ i, |(ξ i : ℝ)| ≤ B) :
    |((eval ξ (pderiv 1 F) : ℤ) : ℝ)| ≤ ((d + 1 : ℕ) : ℝ) ^ 3 * H * B ^ d := by
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
  have hdeg' : (pderiv 1 F).totalDegree ≤ d := by
    by_cases h0 : pderiv 1 F = 0
    · rw [h0]; simp
    · have := OVNS.Quant.totalDegree_pderiv_lt 1 F h0
      omega
  rw [eval_eq_sum_low hdeg']
  push_cast
  have hterm : ∀ m ∈ lowMon d, |(((pderiv 1 F).coeff (ex m) : ℤ) : ℝ) *
      ((ξ 0 : ℝ) ^ m.1 * (ξ 1 : ℝ) ^ m.2)| ≤ ((d + 1 : ℕ) : ℝ) * H * B ^ d := by
    intro m hm
    have hm' := mem_lowMon.mp hm
    rw [coeff_pderiv]
    push_cast
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow]
    have h1 := hH (ex m + Finsupp.single 1 1)
    have h2 : |((ex m 1 : ℕ) : ℝ) + 1| ≤ ((d + 1 : ℕ) : ℝ) := by
      rw [ex_one]
      rw [abs_of_nonneg (by positivity)]
      push_cast
      have : (m.2 : ℝ) ≤ d := by exact_mod_cast (by omega : m.2 ≤ d)
      linarith
    have h3 : |(ξ 0 : ℝ)| ^ m.1 * |(ξ 1 : ℝ)| ^ m.2 ≤ B ^ d := by
      calc |(ξ 0 : ℝ)| ^ m.1 * |(ξ 1 : ℝ)| ^ m.2 ≤ B ^ m.1 * B ^ m.2 :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hξ 0) _)
              (pow_le_pow_left₀ (abs_nonneg _) (hξ 1) _) (by positivity) (by positivity)
        _ = B ^ (m.1 + m.2) := (pow_add _ _ _).symm
        _ ≤ B ^ d := pow_le_pow_right₀ hB hm'
    have h4 : |(((F.coeff (ex m + Finsupp.single 1 1)) : ℤ) : ℝ)| * |((ex m 1 : ℕ) : ℝ) + 1| ≤
        H * ((d + 1 : ℕ) : ℝ) := mul_le_mul h1 h2 (abs_nonneg _) hH0
    calc _ ≤ (H * ((d + 1 : ℕ) : ℝ)) * B ^ d :=
          mul_le_mul h4 h3 (by positivity) (by positivity)
      _ = _ := by push_cast; ring
  calc |∑ m ∈ lowMon d, (((pderiv 1 F).coeff (ex m) : ℤ) : ℝ) *
        ((ξ 0 : ℝ) ^ m.1 * (ξ 1 : ℝ) ^ m.2)|
      ≤ ∑ m ∈ lowMon d, |(((pderiv 1 F).coeff (ex m) : ℤ) : ℝ) *
        ((ξ 0 : ℝ) ^ m.1 * (ξ 1 : ℝ) ^ m.2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ lowMon d, ((d + 1 : ℕ) : ℝ) * H * B ^ d := Finset.sum_le_sum hterm
    _ = ((lowMon d).card : ℝ) * (((d + 1 : ℕ) : ℝ) * H * B ^ d) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((d + 1 : ℕ) : ℝ) ^ 2) * (((d + 1 : ℕ) : ℝ) * H * B ^ d) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_lowMon_le d
    _ = _ := by push_cast; ring

/-- The logarithmic condition holds for all large `s`. -/
theorem exists_good (η : ℝ) (hη : 0 < η) (d : ℕ) : ∃ N₀ : ℕ, ∀ s : ℕ, N₀ ≤ s →
    2 ≤ s ∧ 2 * Real.log (s : ℝ) + (3 * d + 1) * Real.log 2 ≤ ((s : ℝ) - 1) * η * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := η * Real.log 2 / 4 with hc
  have hc0 : 0 < c := by positivity
  have hlo := Real.isLittleO_log_id_atTop.def (show 0 < c / 2 by positivity)
  have hlo' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlo
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hlo'
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (((3 * d + 1) * Real.log 2 + 4 * c) / (3 * c))
  refine ⟨N₁ + N₂ + 2, fun s hs => ⟨by omega, ?_⟩⟩
  have h1 := hN₁ s (by omega)
  simp only [id, Real.norm_eq_abs] at h1
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  rw [abs_of_nonneg hs0] at h1
  have h2 : Real.log (s : ℝ) ≤ c / 2 * s := (le_abs_self _).trans h1
  have h3 : ((N₂ : ℕ) : ℝ) ≤ s := by exact_mod_cast (by omega : N₂ ≤ s)
  have h4 : ((3 * d + 1) * Real.log 2 + 4 * c) ≤ 3 * c * s := by
    have := (div_le_iff₀ (by positivity : 0 < 3 * c)).mp (hN₂.trans h3)
    linarith
  have h5 : ((s : ℝ) - 1) * η * Real.log 2 = 4 * c * ((s : ℝ) - 1) := by
    rw [hc]; ring
  rw [h5]
  nlinarith

end Auxiliary

/-! ## the balanced regime -/

section Balanced
open MvPolynomial

/-- Elementary size bound `(d+1)³ H B^d ≤ B^{c₁}`. -/
theorem size_le_pow {B : ℝ} (hB : 2 ≤ B) (d : ℕ) :
    ((d + 1 : ℕ) : ℝ) ^ 3 * ((((d + 1) ^ 2 : ℕ) : ℝ) * B ^ d) ^ ((d + 1) ^ 2) * B ^ d ≤
      B ^ (4 * d + 3 * d * (d + 1) ^ 2) := by
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hd1 : ((d + 1 : ℕ) : ℝ) ≤ B ^ d := by
    have h1 : ((d + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ d := by
      exact_mod_cast Nat.lt_two_pow_self (n := d)
    exact h1.trans (pow_le_pow_left₀ (by norm_num) hB d)
  have hd0 : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (((d + 1) ^ 2 : ℕ) : ℝ) * B ^ d ≤ B ^ (3 * d) := by
    have e : (((d + 1) ^ 2 : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
    rw [e]
    calc ((d + 1 : ℕ) : ℝ) ^ 2 * B ^ d ≤ (B ^ d) ^ 2 * B ^ d :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd0 hd1 2) (by positivity)
      _ = B ^ (3 * d) := by ring
  have h3 : ((((d + 1) ^ 2 : ℕ) : ℝ) * B ^ d) ^ ((d + 1) ^ 2) ≤ B ^ (3 * d * (d + 1) ^ 2) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) h2 _
  have h4 : ((d + 1 : ℕ) : ℝ) ^ 3 ≤ B ^ (3 * d) := by
    calc ((d + 1 : ℕ) : ℝ) ^ 3 ≤ (B ^ d) ^ 3 := pow_le_pow_left₀ hd0 hd1 3
      _ = B ^ (3 * d) := by ring
  calc ((d + 1 : ℕ) : ℝ) ^ 3 * ((((d + 1) ^ 2 : ℕ) : ℝ) * B ^ d) ^ ((d + 1) ^ 2) * B ^ d
      ≤ B ^ (3 * d) * B ^ (3 * d * (d + 1) ^ 2) * B ^ d :=
        mul_le_mul_of_nonneg_right (mul_le_mul h4 h3 (by positivity) (by positivity))
          (by positivity)
    _ = B ^ (4 * d + 3 * d * (d + 1) ^ 2) := by ring

theorem balanced_count (d : ℕ) (hd2 : 2 ≤ d) (η : ℝ) (hη : 0 < η) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ F : MvPolynomial (Fin 2) ℤ, Irreducible (map (Int.castRingHom ℚ) F) →
      (map (Int.castRingHom ℚ) F).totalDegree = d →
      ∀ B₀ B₁ : ℝ, 2 ≤ B₀ → B₀ ≤ B₁ → η * Real.log B₁ < Real.log B₀ →
      ∀ e : Fin 2 →₀ ℕ, IsTop (Real.log B₀) (Real.log B₁) (map (Int.castRingHom ℚ) F).support e →
      ∀ S : Finset (Fin 2 → ℤ), (∀ ξ ∈ S, eval ξ F = 0) →
        (∀ ξ ∈ S, |(ξ 0 : ℝ)| ≤ B₀) → (∀ ξ ∈ S, |(ξ 1 : ℝ)| ≤ B₁) →
        (S.card : ℝ) ≤ C * B₁ ^ η * Real.exp (Real.log B₀ * Real.log B₁ /
          ((e 0 : ℝ) * Real.log B₀ + (e 1 : ℝ) * Real.log B₁)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_good η hη d
  set N := N₀ + 2 with hN
  set c₁ : ℕ := 4 * d + 3 * d * (d + 1) ^ 2 with hc₁
  set K : ℕ := ⌈((c₁ : ℝ) + 1) / η⌉₊ with hK
  set D : ℕ := d + N + ⌈(N : ℝ) / η⌉₊ with hD
  refine ⟨(d : ℝ) ^ 2 + K * (d * D) * d * 2 ^ (K + 1), by positivity, ?_⟩
  intro F hirr hdeg B₀ B₁ hB₀ hB₀₁ hbal e he S hz hS₀ hS₁
  set a := Real.log B₀ with ha
  set b := Real.log B₁ with hb
  have hB₁ : 2 ≤ B₁ := hB₀.trans hB₀₁
  have hB₀p : 0 < B₀ := by linarith
  have hB₁p : 0 < B₁ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha2 : Real.log 2 ≤ a := Real.log_le_log (by norm_num) hB₀
  have hab : a ≤ b := Real.log_le_log hB₀p hB₀₁
  have ha0 : 0 < a := lt_of_lt_of_le hl2 ha2
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hedeg : e 0 + e 1 ≤ d := by
    have h := le_totalDegree he.1
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two, hdeg] at h
    exact h
  have hepos : 1 ≤ e 0 + e 1 := by
    by_contra hcon
    have h0 : e 0 = 0 := by omega
    have h1 : e 1 = 0 := by omega
    have hne : (map (Int.castRingHom ℚ) F).support.Nonempty := support_nonempty.mpr hirr.ne_zero
    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup _ hne (fun m => m.sum fun _ x => x)
    have hmd : m.sum (fun _ x => x) = d := by
      rw [← hmax]; exact hdeg
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hmd
    have hw := (he.2 m hm).1
    simp only [wt, h0, h1, Nat.cast_zero, zero_mul, add_zero] at hw
    have h3 : (0 : ℝ) ≤ m 0 := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ m 1 := Nat.cast_nonneg _
    have h5 : ((m 0 : ℝ)) + m 1 = d := by exact_mod_cast hmd
    have h6 : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have h7 : a * (m 0 + m 1) ≤ (m 0 : ℝ) * a + (m 1 : ℝ) * b := by
      have := mul_le_mul_of_nonneg_left hab h4
      nlinarith
    nlinarith
  set τ : ℝ := (e 0 : ℝ) * a + (e 1 : ℝ) * b with hτ
  have hτge : a ≤ τ := by
    have h3 : (1 : ℝ) ≤ (e 0 : ℝ) + e 1 := by exact_mod_cast hepos
    have h4 : 0 ≤ (e 1 : ℝ) * (b - a) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hab)
    have h5 : τ = ((e 0 : ℝ) + e 1) * a + e 1 * (b - a) := by rw [hτ]; ring
    nlinarith
  have hτ0 : 0 < τ := lt_of_lt_of_le ha0 hτge
  set A : ℝ := a * b / τ with hA
  have hA0 : 0 ≤ A := by positivity
  set L : ℝ := A + η * b with hL
  set Y : ℝ := B₁ ^ η * Real.exp A with hY
  have hrpow : B₁ ^ η = Real.exp (η * b) := by
    rw [Real.rpow_def_of_pos hB₁p, mul_comm]
  have hexpL : Real.exp L = Y := by
    rw [hL, Real.exp_add, hY, hrpow, mul_comm]
  have hY1 : 1 ≤ Y := by
    rw [← hexpL]
    exact Real.one_le_exp (by positivity)
  have hgoal : ∀ x : ℝ, x ≤ ((d : ℝ) ^ 2 + K * (d * D) * d * 2 ^ (K + 1)) * Y →
      x ≤ ((d : ℝ) ^ 2 + K * (d * D) * d * 2 ^ (K + 1)) * B₁ ^ η * Real.exp A := fun x hx => by
    rw [mul_assoc]; exact hx
  apply hgoal
  by_cases hsmall : S.card ≤ d ^ 2
  · have h1 : (S.card : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast hsmall
    have h2 : (0 : ℝ) ≤ K * (d * D) * d * 2 ^ (K + 1) := by positivity
    nlinarith
  push Not at hsmall
  have hbox : ∀ ξ ∈ S, ∀ i, |(ξ i : ℝ)| ≤ B₁ := by
    intro ξ hξ i
    fin_cases i
    · exact (hS₀ ξ hξ).trans hB₀₁
    · exact hS₁ ξ hξ
  obtain ⟨F', q, hq, hmap, hcoef⟩ := height_reduction hirr hdeg S hz B₁ (by linarith) hbox hsmall
  have hirr' : Irreducible (map (Int.castRingHom ℚ) F') := by
    rw [hmap]
    exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr hq).map C)).mpr hirr
  have hsupp : (map (Int.castRingHom ℚ) F').support = (map (Int.castRingHom ℚ) F).support := by
    rw [hmap, C_mul', support_smul_eq hq]
  have hdeg' : (map (Int.castRingHom ℚ) F').totalDegree = d := by
    rw [totalDegree, hsupp]; exact hdeg
  have hdegZ : F'.totalDegree ≤ d := by
    rw [← hdeg', totalDegree, totalDegree,
      support_map_of_injective F' (RingHom.injective_int (Int.castRingHom ℚ))]
  have he' : IsTop a b (map (Int.castRingHom ℚ) F').support e := by
    rw [hsupp]; exact he
  have hz' : ∀ ξ ∈ S, eval ξ F' = 0 := by
    intro ξ hξ
    have h1 := eval_cast (F := F') ξ
    rw [hmap, map_mul, eval_C, eval_cast, hz ξ hξ] at h1
    have h2 : ((eval ξ F' : ℤ) : ℚ) = 0 := by rw [← h1]; simp
    exact_mod_cast h2
  set Fq' := map (Int.castRingHom ℚ) F' with hFq'
  set dF := pderiv 1 F' with hdF
  have hderiv : pderiv 1 Fq' ≠ 0 := by
    intro h0
    obtain ⟨ξ, hξ⟩ : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    refine no_zero_of_pderiv_eq_zero hirr' hdeg' hd2 h0 (ξ 0) (ξ 1) ?_
    have := pt_eta (fun i => (ξ i : ℚ))
    rw [this, eval_cast, hz' ξ hξ]
    simp
  have hmapd : pderiv 1 Fq' = map (Int.castRingHom ℚ) dF := by
    rw [hFq', pderiv_map]
  set Z := S.filter fun ξ => eval ξ dF = 0 with hZdef
  have hZ : Z.card ≤ d * d := by
    have hbz := OVNS.Quant.plane_bezout Fq' (pderiv 1 Fq')
      (OVNS.Quant.isRelPrime_pderiv hirr' 1 hderiv) hirr'.ne_zero hderiv
      (Z.image fun (ξ : Fin 2 → ℤ) (i : Fin 2) => (ξ i : ℚ)) (by
        intro x hx
        obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hx
        have hξ' := Finset.mem_filter.mp hξ
        constructor
        · rw [eval_cast, hz' ξ hξ'.1]; simp
        · rw [hmapd, eval_cast, hξ'.2]; simp)
    rw [Finset.card_image_of_injective _ int_pts_inj, hdeg'] at hbz
    have h2 := OVNS.Quant.totalDegree_pderiv_lt 1 Fq' hderiv
    refine hbz.trans (Nat.mul_le_mul_left _ ?_)
    omega
  -- primes
  have hexpL0 : 0 < Real.exp L := Real.exp_pos _
  set n : ℕ := ⌈Real.exp L⌉₊ with hn
  have hnL : Real.exp L ≤ n := Nat.le_ceil _
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hnL
    simp only [Nat.cast_zero] at hnL
    linarith
  obtain ⟨ps, hpsc, hps⟩ := exists_primes K n hn0
  -- the L-shape
  set v : ℕ := ⌈(N : ℝ) * b / a⌉₊ with hv
  have hv1 : (N : ℝ) * b / a ≤ v := Nat.le_ceil _
  have hv2 : (v : ℝ) < (N : ℝ) * b / a + 1 := Nat.ceil_lt_add_one (by positivity)
  have hva1 : 0 ≤ a * v - b * N := by
    have h1 := mul_le_mul_of_nonneg_left hv1 ha0.le
    have h2 : a * ((N : ℝ) * b / a) = b * N := by field_simp
    linarith
  have hva2 : a * v - b * N ≤ a := by
    have h1 := mul_le_mul_of_nonneg_left hv2.le ha0.le
    have h2 : a * ((N : ℝ) * b / a + 1) = b * N + a := by field_simp
    linarith
  have hvN : N ≤ v := by
    have h1 : (N : ℝ) ≤ (N : ℝ) * b / a := by
      rw [le_div_iff₀ ha0]
      exact mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg _)
    exact_mod_cast h1.trans hv1
  have hvD : v ≤ ⌈(N : ℝ) / η⌉₊ := by
    refine Nat.ceil_mono ?_
    rw [div_le_div_iff₀ ha0 hη]
    have : (N : ℝ) * (b * η) ≤ (N : ℝ) * a := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      linarith
    linarith
  set s : ℕ := e 0 * N + e 1 * v with hs
  have hsN : N ≤ s := by
    rcases Nat.eq_zero_or_pos (e 0) with h0 | h0
    · have h1 : 0 < e 1 := by omega
      have : v ≤ e 1 * v := Nat.le_mul_of_pos_left _ h1
      omega
    · have : N ≤ e 0 * N := Nat.le_mul_of_pos_left _ h0
      omega
  obtain ⟨hs2, hgood⟩ := hN₀ s (by omega)
  set E := lShape (e 0) (e 1) N v with hE
  have hsize : ∀ p ∈ ps, ((E.card).factorial : ℝ) * ∏ m ∈ E, (B₀ ^ m.1 * B₁ ^ m.2) <
      (p : ℝ) ^ (E.card * (E.card - 1) / 2) := by
    intro p hp
    have hpL : Real.exp (a * b / ((e 0 : ℝ) * a + (e 1 : ℝ) * b) + η * b) < p :=
      lt_of_le_of_lt hnL (by exact_mod_cast (hps p hp).2.1)
    have := hsize_of_good ha2 hab hedeg hepos hva1 hva2 hs2 hgood hpL
    rw [Real.exp_log hB₀p, Real.exp_log hB₁p] at this
    exact this
  have hfilter : ∀ p ∈ ps, (S.filter fun ξ => ¬ (p : ℤ) ∣ eval ξ dF).card ≤
      (d * D) * (d * (2 ^ K * n)) := by
    intro p hp
    have h1 := nonsing_card_le hirr' hb0 he' (hps p hp).1 S hz' B₀ B₁ hS₀ hS₁ E D d
      (fun m hm => lShape_avoid hm) (fun m hm => (lShape_deg hm).trans (by omega)) hdegZ
      hdeg'.le (hsize p hp)
    refine h1.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hps p hp).2.2))
  -- the size of `∂F`
  have hdFsize : ∀ ξ ∈ S, (eval ξ dF).natAbs < n ^ ps.card := by
    intro ξ hξ
    have h1 := abs_eval_pderiv_le hdegZ _ hcoef B₁ (by linarith) ξ (hbox ξ hξ)
    have h2 := size_le_pow hB₁ d
    have h3 : B₁ ^ (c₁ + 1) ≤ (n : ℝ) ^ K := by
      have h4 : ((c₁ : ℝ) + 1) ≤ K * η := by
        have := Nat.le_ceil (((c₁ : ℝ) + 1) / η)
        rwa [div_le_iff₀ hη] at this
      have h5 : ((c₁ + 1 : ℕ) : ℝ) * b ≤ K * L := by
        have : (K : ℝ) * (η * b) ≤ K * L := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rw [hL]
          linarith
        push_cast
        calc ((c₁ : ℝ) + 1) * b ≤ (K * η) * b := mul_le_mul_of_nonneg_right h4 hb0.le
          _ = K * (η * b) := by ring
          _ ≤ K * L := this
      calc B₁ ^ (c₁ + 1) = Real.exp (((c₁ + 1 : ℕ) : ℝ) * b) := by
            rw [Real.exp_nat_mul, hb, Real.exp_log hB₁p]
        _ ≤ Real.exp ((K : ℝ) * L) := Real.exp_le_exp.mpr h5
        _ = Real.exp L ^ K := Real.exp_nat_mul _ _
        _ ≤ (n : ℝ) ^ K := pow_le_pow_left₀ hexpL0.le hnL K
    have h4 : B₁ ^ c₁ < B₁ ^ (c₁ + 1) := pow_lt_pow_right₀ (by linarith) (Nat.lt_succ_self _)
    have h5 : ((eval ξ dF).natAbs : ℝ) < (n : ℝ) ^ K := by
      rw [Nat.cast_natAbs]
      push_cast
      linarith
    rw [hpsc]
    exact_mod_cast h5
  -- the covering
  have hcover : S ⊆ Z ∪ ps.biUnion fun p => S.filter fun ξ => ¬ (p : ℤ) ∣ eval ξ dF := by
    intro ξ hξ
    by_cases h0 : eval ξ dF = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hξ, h0⟩)
    · obtain ⟨p, hp, hnd⟩ := exists_prime_not_dvd ps (fun p hp => (hps p hp).1) n
        (fun p hp => (hps p hp).2.1.le) _ h0 (hdFsize ξ hξ)
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩)
      exact Finset.mem_filter.mpr ⟨hξ, hnd⟩
  have hcard : S.card ≤ d * d + K * ((d * D) * (d * (2 ^ K * n))) := by
    calc S.card ≤ _ := Finset.card_le_card hcover
      _ ≤ Z.card + (ps.biUnion fun p => S.filter fun ξ => ¬ (p : ℤ) ∣ eval ξ dF).card :=
        Finset.card_union_le _ _
      _ ≤ d * d + ps.card * ((d * D) * (d * (2 ^ K * n))) :=
        add_le_add hZ (Finset.card_biUnion_le_card_mul _ _ _ hfilter)
      _ = _ := by rw [hpsc]
  have hnle : (n : ℝ) ≤ 2 * Y := by
    have h1 : (n : ℝ) < Real.exp L + 1 := Nat.ceil_lt_add_one hexpL0.le
    rw [hexpL] at h1
    linarith
  have hcardR : (S.card : ℝ) ≤ (d : ℝ) ^ 2 + K * (d * D) * d * 2 ^ K * n := by
    have h1 : (S.card : ℝ) ≤ ((d * d + K * ((d * D) * (d * (2 ^ K * n))) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    refine h1.trans (le_of_eq ?_)
    push_cast
    ring
  have h6 : (0 : ℝ) ≤ K * (d * D) * d * 2 ^ K := by positivity
  have h7 := mul_le_mul_of_nonneg_left hnle h6
  have h8 : (d : ℝ) ^ 2 * 1 ≤ (d : ℝ) ^ 2 * Y := mul_le_mul_of_nonneg_left hY1 (by positivity)
  calc (S.card : ℝ) ≤ (d : ℝ) ^ 2 + K * (d * D) * d * 2 ^ K * n := hcardR
    _ ≤ (d : ℝ) ^ 2 * Y + K * (d * D) * d * 2 ^ K * (2 * Y) := by linarith
    _ = _ := by ring

end Balanced

/-! ## degree one (`plane_d_one`, from the statement audit) -/

section DegreeOne

open OVNS MvPolynomial

noncomputable section

private abbrev e0 : Fin 2 →₀ ℕ := Finsupp.single 0 1
private abbrev e1 : Fin 2 →₀ ℕ := Finsupp.single 1 1

private lemma deg_eq (d : Fin 2 →₀ ℕ) : (d.sum fun _ e => e) = d 0 + d 1 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]

private lemma mem_three {d : Fin 2 →₀ ℕ} (h : d 0 + d 1 ≤ 1) : d = 0 ∨ d = e0 ∨ d = e1 := by
  have h0 : d 0 = 0 ∨ d 0 = 1 := by omega
  have h1 : d 1 = 0 ∨ d 1 = 1 := by omega
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · left; ext i; fin_cases i <;> simp [h0, h1]
  · right; right; ext i; fin_cases i <;> simp [e1, h0, h1]
  · right; left; ext i; fin_cases i <;> simp [e0, h0, h1]
  · omega

private lemma e0_ne_zero : e0 ≠ 0 := by simp [e0]
private lemma e1_ne_zero : e1 ≠ 0 := by simp [e1]
private lemma e0_ne_e1 : e0 ≠ e1 := by
  intro h
  have := DFunLike.congr_fun h 0
  simp [e0, e1] at this

private lemma support_sub {F : MvPolynomial (Fin 2) ℤ} (hF : F.totalDegree ≤ 1) :
    F.support ⊆ {0, e0, e1} := by
  intro d hd
  have h := MvPolynomial.le_totalDegree hd
  rw [deg_eq] at h
  have := mem_three (h.trans hF)
  simpa using this

private lemma eval_lin {F : MvPolynomial (Fin 2) ℤ} (hF : F.totalDegree ≤ 1) (x : Fin 2 → ℤ) :
    eval x F = F.coeff e0 * x 0 + F.coeff e1 * x 1 + F.coeff 0 := by
  classical
  rw [MvPolynomial.eval_eq', Finset.sum_subset (support_sub hF)
    (fun d _ hd => by simp [MvPolynomial.notMem_support_iff.1 hd])]
  rw [Finset.sum_insert (by simp [e0_ne_zero.symm, e1_ne_zero.symm]),
    Finset.sum_insert (by simpa using e0_ne_e1), Finset.sum_singleton]
  simp [Fin.prod_univ_two, e0, e1]
  ring

private lemma card_le {F : MvPolynomial (Fin 2) ℤ} {B : Fin 2 → ℝ} (i : Fin 2) (hB : 2 ≤ B i)
    (hinj : ∀ x ∈ boxZeros F B, ∀ y ∈ boxZeros F B, x i = y i → x = y) :
    ((boxZeros F B).card : ℝ) ≤ 3 * B i := by
  classical
  have hc : (boxZeros F B).card ≤ (Finset.Icc (-⌊B i⌋) ⌊B i⌋).card := by
    refine Finset.card_le_card_of_injOn (fun x => x i) (fun x hx => ?_) (fun x hx y hy h => hinj x hx y hy h)
    have hx' : x ∈ boxPts 2 B := by
      unfold boxZeros at hx
      exact (Finset.mem_filter.1 hx).1
    exact (Fintype.mem_piFinset.1 hx') i
  have hfl : (0:ℤ) ≤ ⌊B i⌋ := Int.floor_nonneg.2 (by linarith)
  have h2 : ((Finset.Icc (-⌊B i⌋) ⌊B i⌋).card : ℝ) = 2 * (⌊B i⌋ : ℝ) + 1 := by
    rw [Int.card_Icc]
    have : (⌊B i⌋ + 1 - -⌊B i⌋) = 2 * ⌊B i⌋ + 1 := by ring
    rw [this]
    have h3 : (0:ℤ) ≤ 2 * ⌊B i⌋ + 1 := by omega
    have h4 := Int.toNat_of_nonneg h3
    have h5 : (((2 * ⌊B i⌋ + 1).toNat : ℤ) : ℝ) = ((2 * ⌊B i⌋ + 1 : ℤ) : ℝ) := by rw [h4]
    rw [Int.cast_natCast] at h5
    rw [h5]
    push_cast
    ring
  have h6 : ((boxZeros F B).card : ℝ) ≤ ((Finset.Icc (-⌊B i⌋) ⌊B i⌋).card : ℝ) := by
    exact_mod_cast hc
  have h7 : (⌊B i⌋ : ℝ) ≤ B i := Int.floor_le _
  rw [h2] at h6
  linarith

private lemma mem_zero {F : MvPolynomial (Fin 2) ℤ} {B : Fin 2 → ℝ} {x : Fin 2 → ℤ}
    (hx : x ∈ boxZeros F B) : eval x F = 0 := by
  unfold boxZeros at hx
  exact (Finset.mem_filter.1 hx).2

private lemma boxSize_eq {F : MvPolynomial (Fin 2) ℤ} {B : Fin 2 → ℝ}
    {i : Fin 2} {ei : Fin 2 →₀ ℕ} (hei : ei ∈ F.support)
    (hval : ∏ j, B j ^ ei j = B i)
    (hup : ∀ d ∈ F.support, ∏ j, B j ^ d j ≤ B i) : boxSize F B = B i := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ei, hei, rfl⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact hup d hd
  · have hbdd : BddAbove ((fun e : Fin 2 →₀ ℕ => ∏ i, B i ^ (e i)) ''
        (F.support : Set (Fin 2 →₀ ℕ))) := (F.support.finite_toSet.image _).bddAbove
    rw [← hval]
    exact le_csSup hbdd ⟨ei, hei, rfl⟩

theorem plane_d_one (η : ℝ) (hη : 0 < η) : ∃ C : ℝ, ∀ F : MvPolynomial (Fin 2) ℤ,
    F.totalDegree = 1 → AbsIrred F → ∀ B : Fin 2 → ℝ, 2 ≤ B 0 → B 0 ≤ B 1 →
      ((boxZeros F B).card : ℝ) ≤
        C * B 1 ^ η * Real.exp (Real.log (B 0) * Real.log (B 1) / Real.log (boxSize F B)) := by
  classical
  refine ⟨3, fun F hF _ B hB0 hB1 => ?_⟩
  have hF' : F.totalDegree ≤ 1 := hF.le
  have hpos0 : 0 < B 0 := by linarith
  have hpos1 : 0 < B 1 := by linarith
  have hlog0 : 0 < Real.log (B 0) := Real.log_pos (by linarith)
  have hlog1 : 0 < Real.log (B 1) := Real.log_pos (by linarith)
  have hrpow : (1:ℝ) ≤ B 1 ^ η := Real.one_le_rpow (by linarith) hη.le
  have hsup := support_sub hF'
  by_cases hb : F.coeff e1 = 0
  · -- `F = aX + c`, `T = B₀`, exponent `log B₁`, count `≤ 3 B₁`.
    have ha : F.coeff e0 ≠ 0 := by
      intro ha
      have hlt : (0:ℕ) < F.support.sup (fun s => s.sum fun _ e => e) := by
        have : F.totalDegree = 1 := hF
        unfold MvPolynomial.totalDegree at this
        omega
      obtain ⟨d, hd, hd2⟩ := (Finset.lt_sup_iff).1 hlt
      have hd3 := hsup hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd3
      rcases hd3 with rfl | rfl | rfl
      · simp at hd2
      · exact (MvPolynomial.mem_support_iff.1 hd) ha
      · exact (MvPolynomial.mem_support_iff.1 hd) hb
    have hT : boxSize F B = B 0 := by
      refine boxSize_eq (i := 0) (ei := e0) (MvPolynomial.mem_support_iff.2 ha)
        (by simp [Fin.prod_univ_two, e0]) (fun d hd => ?_)
      have hd3 := hsup hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd3
      rcases hd3 with rfl | rfl | rfl
      · simpa [Fin.prod_univ_two] using (by linarith : (1:ℝ) ≤ B 0)
      · simp [Fin.prod_univ_two, e0]
      · exact absurd hb (MvPolynomial.mem_support_iff.1 hd)
    have hcard := card_le (F := F) (B := B) 1 (by linarith) (fun x hx y hy hxy => by
      have h1 := mem_zero hx
      have h2 := mem_zero hy
      rw [eval_lin hF', hb] at h1 h2
      have h3 : F.coeff e0 * (x 0 - y 0) = 0 := by linear_combination h1 - h2
      have h4 : x 0 = y 0 := by
        have := (mul_eq_zero.1 h3).resolve_left ha
        omega
      funext i
      fin_cases i
      · exact h4
      · exact hxy)
    have hexp : Real.exp (Real.log (B 0) * Real.log (B 1) / Real.log (boxSize F B)) = B 1 := by
      rw [hT, mul_comm, mul_div_assoc, div_self hlog0.ne', mul_one, Real.exp_log hpos1]
    rw [hexp]
    nlinarith
  · -- `b ≠ 0`, `T = B₁`, exponent `log B₀`, count `≤ 3 B₀`.
    have hT : boxSize F B = B 1 := by
      refine boxSize_eq (i := 1) (ei := e1) (MvPolynomial.mem_support_iff.2 hb)
        (by simp [Fin.prod_univ_two, e1]) (fun d hd => ?_)
      have hd3 := hsup hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd3
      rcases hd3 with rfl | rfl | rfl
      · simpa [Fin.prod_univ_two] using (by linarith : (1:ℝ) ≤ B 1)
      · simpa [Fin.prod_univ_two, e0] using hB1
      · simp [Fin.prod_univ_two, e1]
    have hcard := card_le (F := F) (B := B) 0 hB0 (fun x hx y hy hxy => by
      have h1 := mem_zero hx
      have h2 := mem_zero hy
      rw [eval_lin hF'] at h1 h2
      have h3 : F.coeff e1 * (x 1 - y 1) = 0 := by
        rw [hxy] at h1
        linear_combination h1 - h2
      have h4 : x 1 = y 1 := by
        have := (mul_eq_zero.1 h3).resolve_left hb
        omega
      funext i
      fin_cases i
      · exact hxy
      · exact h4)
    have hexp : Real.exp (Real.log (B 0) * Real.log (B 1) / Real.log (boxSize F B)) = B 0 := by
      rw [hT, mul_div_assoc, div_self hlog1.ne', mul_one, Real.exp_log hpos0]
    rw [hexp]
    nlinarith

end

end DegreeOne

/-! ## the theorem -/

section Final

open MvPolynomial

theorem log_boxSize {F : MvPolynomial (Fin 2) ℤ} {B : Fin 2 → ℝ} (h0 : 0 < B 0) (h1 : 0 < B 1)
    {e : Fin 2 →₀ ℕ}
    (he : IsTop (Real.log (B 0)) (Real.log (B 1)) (map (Int.castRingHom ℚ) F).support e) :
    Real.log (OVNS.boxSize F B) = (e 0 : ℝ) * Real.log (B 0) + (e 1 : ℝ) * Real.log (B 1) := by
  have hsupp : (map (Int.castRingHom ℚ) F).support = F.support :=
    support_map_of_injective _ (RingHom.injective_int _)
  have hval : ∀ m : Fin 2 →₀ ℕ,
      ∏ i, B i ^ (m i) = Real.exp (wt (Real.log (B 0)) (Real.log (B 1)) m) := by
    intro m
    rw [Fin.prod_univ_two, wt, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log h0,
      Real.exp_log h1]
  have hgr : IsGreatest ((fun e : Fin 2 →₀ ℕ => ∏ i, B i ^ (e i)) ''
      (F.support : Set (Fin 2 →₀ ℕ))) (Real.exp (wt (Real.log (B 0)) (Real.log (B 1)) e)) := by
    constructor
    · refine ⟨e, ?_, hval e⟩
      have := he.1
      rw [hsupp] at this
      exact this
    · rintro _ ⟨m, hm, rfl⟩
      simp only [hval]
      exact Real.exp_le_exp.mpr (he.2 m (by rw [hsupp]; exact hm)).1
  unfold OVNS.boxSize
  rw [hgr.csSup_eq, Real.log_exp]
  rfl

theorem mem_box {F : MvPolynomial (Fin 2) ℤ} {B : Fin 2 → ℝ} {ξ : Fin 2 → ℤ}
    (hξ : ξ ∈ OVNS.boxZeros F B) (i : Fin 2) : |(ξ i : ℝ)| ≤ B i := by
  unfold OVNS.boxZeros at hξ
  have h1 := (Finset.mem_filter.mp hξ).1
  have h2 := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp h1 i)
  have h3 : (⌊B i⌋ : ℝ) ≤ B i := Int.floor_le _
  have h4 : (ξ i : ℝ) ≤ (⌊B i⌋ : ℝ) := by exact_mod_cast h2.2
  have h5 : (-(⌊B i⌋ : ℝ)) ≤ (ξ i : ℝ) := by exact_mod_cast h2.1
  rw [abs_le]
  constructor <;> linarith

theorem zero_box {F : MvPolynomial (Fin 2) ℤ} {B : Fin 2 → ℝ} {ξ : Fin 2 → ℤ}
    (hξ : ξ ∈ OVNS.boxZeros F B) : eval ξ F = 0 := by
  unfold OVNS.boxZeros at hξ
  exact (Finset.mem_filter.mp hξ).2

theorem plane_count_ge_two (d : ℕ) (hd2 : 2 ≤ d) (η : ℝ) (hη : 0 < η) : ∃ C : ℝ,
    ∀ F : MvPolynomial (Fin 2) ℤ, F.totalDegree = d →
      Irreducible (map (Int.castRingHom ℚ) F) → ∀ B : Fin 2 → ℝ, 2 ≤ B 0 → B 0 ≤ B 1 →
        ((OVNS.boxZeros F B).card : ℝ) ≤ C * B 1 ^ η *
          Real.exp (Real.log (B 0) * Real.log (B 1) / Real.log (OVNS.boxSize F B)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := balanced_count d hd2 η hη
  refine ⟨C₁ + 3 * d, fun F hF hirr B hB0 hB01 => ?_⟩
  have hdeg : (map (Int.castRingHom ℚ) F).totalDegree = d := by
    rw [totalDegree, support_map_of_injective F (RingHom.injective_int (Int.castRingHom ℚ))]
    exact hF
  have hB1 : 2 ≤ B 1 := hB0.trans hB01
  have h0 : 0 < B 0 := by linarith
  have h1 : 0 < B 1 := by linarith
  set a := Real.log (B 0) with ha
  set b := Real.log (B 1) with hb
  have ha0 : 0 < a := Real.log_pos (by linarith)
  have hb0 : 0 < b := Real.log_pos (by linarith)
  obtain ⟨e, he⟩ := exists_isTop a b (map (Int.castRingHom ℚ) F).support
    (support_nonempty.mpr hirr.ne_zero)
  have hlogT := log_boxSize h0 h1 he
  rw [← ha, ← hb] at hlogT
  rw [hlogT]
  set A := a * b / ((e 0 : ℝ) * a + (e 1 : ℝ) * b) with hA
  have hA0 : 0 ≤ A := by positivity
  have hE1 : 1 ≤ Real.exp A := Real.one_le_exp hA0
  have hrp : 1 ≤ B 1 ^ η := Real.one_le_rpow (by linarith) hη.le
  set S := OVNS.boxZeros F B with hS
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  by_cases hbal : η * b < a
  · have := hC₁ F hirr hdeg (B 0) (B 1) hB0 hB01 hbal e he S (fun ξ hξ => zero_box hξ)
      (fun ξ hξ => mem_box hξ 0) (fun ξ hξ => mem_box hξ 1)
    refine this.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith
  · push Not at hbal
    have h2 := trivial_count hirr hdeg hd2 S (fun ξ hξ => zero_box hξ) (B 0) hB0
      (fun ξ hξ => mem_box hξ 0)
    have h3 : B 0 ≤ B 1 ^ η := by
      rw [Real.rpow_def_of_pos h1, ← hb]
      calc B 0 = Real.exp a := (Real.exp_log h0).symm
        _ ≤ Real.exp (b * η) := Real.exp_le_exp.mpr (by linarith)
    have h4 : (S.card : ℝ) ≤ 3 * d * B 1 ^ η := h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    have h5 : (3 * (d : ℝ)) * B 1 ^ η ≤ (C₁ + 3 * d) * B 1 ^ η := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith
    have h6 : (C₁ + 3 * d) * B 1 ^ η * 1 ≤ (C₁ + 3 * d) * B 1 ^ η * Real.exp A :=
      mul_le_mul_of_nonneg_left hE1 (by positivity)
    linarith

/-- **`PlaneCurveCount` is a theorem.** -/
theorem planeCurveCount : OVNS.PlaneCurveCount := by
  intro d η hd hη
  rcases Nat.lt_or_ge d 2 with h | h
  · obtain rfl : d = 1 := by omega
    exact plane_d_one η hη
  · obtain ⟨C, hC⟩ := plane_count_ge_two d h η hη
    exact ⟨C, fun F hF hA B h0 h1 => hC F hF (OVNS.Quant.surface_irreducible_rat F hA) B h0 h1⟩

end Final

end OVNS.Quant.PlaneCount
