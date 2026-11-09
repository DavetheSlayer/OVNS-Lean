import OddViscousNS.Helical

/-! # Algebraic counting of resonances (`Lemma lem:count`) -/

noncomputable section
namespace OVNS

/-- The lattice point `(a, b, c)`. -/
def mk3 (a b c : ℤ) : Mode := ![a, b, c]

open Polynomial in
/-- The degree-six resonance polynomial `X² - 4GA²`, with `X = A² + G - B²` written as an explicit
cubic, for `A² = x⁴ + q x²` and `B² = (x + c)⁴ + p (x + c)²`. -/
private def resPoly (p q c G : ℤ) : ℤ[X] :=
  (C (-4 * c) * X ^ 3 + C (q - p - 6 * c ^ 2) * X ^ 2 + C (-4 * c ^ 3 - 2 * p * c) * X
    + C (G - c ^ 4 - p * c ^ 2)) ^ 2 - C (4 * G) * (X ^ 4 + C q * X ^ 2)

/-- The resonance polynomial has degree six, with leading coefficient `16 c²`. -/
private lemma natDegree_resPoly (p q G : ℤ) {c : ℤ} (hc : c ≠ 0) :
    (resPoly p q c G).natDegree = 6 := by
  unfold resPoly
  compute_degree!

/-- The evaluation of the resonance polynomial, in terms of `A²`, `B²` and `G`. -/
private lemma eval_resPoly (p q c G x : ℤ) :
    (resPoly p q c G).eval x =
      ((x ^ 4 + q * x ^ 2) + G - ((x + c) ^ 4 + p * (x + c) ^ 2)) ^ 2
        - 4 * G * (x ^ 4 + q * x ^ 2) := by
  simp only [resPoly, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- A signed zero sum of three reals forces the vanishing of `(A + G - B)² - 4GA`. -/
private lemma resonance_identity {A B G a b g : ℝ} (h : a + b + g = 0) (ha : a ^ 2 = A)
    (hb : b ^ 2 = B) (hg : g ^ 2 = G) : (A + G - B) ^ 2 - 4 * G * A = 0 := by
  obtain rfl : b = -a - g := by linarith
  subst ha hb hg
  ring

private lemma sg_sq (a : Sgn) : sg a ^ 2 = 1 := by
  cases a <;> simp [sg]

/-- Every resonant `x` is an integer root of the resonance polynomial. -/
private lemma resonant_isRoot (n : Mode) (a b x : ℤ) (σ₁ σ₂ σ₃ : Sgn)
    (h : sg σ₁ * (x : ℝ) * absk (mk3 a b x)
        + sg σ₂ * ((-mk3 a b x - n) 2 : ℤ) * absk (-mk3 a b x - n)
        + sg σ₃ * (n 2 : ℝ) * absk n = 0) :
    (resPoly ((a + n 0) ^ 2 + (b + n 1) ^ 2) (a ^ 2 + b ^ 2) (n 2)
      (n 2 ^ 2 * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2))).eval x = 0 := by
  have hk : absk (mk3 a b x) ^ 2 = (a : ℝ) ^ 2 + b ^ 2 + x ^ 2 := by
    rw [absk_sq]
    simp [absSq, Fin.sum_univ_three, mk3]
  have hm : absk (-mk3 a b x - n) ^ 2 =
      ((a : ℝ) + n 0) ^ 2 + (b + n 1) ^ 2 + (x + n 2) ^ 2 := by
    rw [absk_sq]
    simp only [absSq, Fin.sum_univ_three, mk3, Pi.sub_apply, Pi.neg_apply]
    simp
    ring
  have hn : absk n ^ 2 = (n 0 : ℝ) ^ 2 + n 1 ^ 2 + n 2 ^ 2 := by
    rw [absk_sq]
    simp [absSq, Fin.sum_univ_three]
  have hm2 : (((-mk3 a b x - n) 2 : ℤ) : ℝ) = -(x : ℝ) - n 2 := by
    simp [mk3]
  have key := resonance_identity (A := (x : ℝ) ^ 4 + (a ^ 2 + b ^ 2) * x ^ 2)
    (B := ((x : ℝ) + n 2) ^ 4 + (((a : ℝ) + n 0) ^ 2 + (b + n 1) ^ 2) * (x + n 2) ^ 2)
    (G := (n 2 : ℝ) ^ 2 * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2)) h
    (by rw [mul_pow, mul_pow, sg_sq, hk]; ring)
    (by rw [mul_pow, mul_pow, sg_sq, hm, hm2]; ring)
    (by rw [mul_pow, mul_pow, sg_sq, hn]; ring)
  rw [eval_resPoly]
  exact_mod_cast key

/-- For fixed `n` with `n₃ ≠ 0` and fixed `k'`, at most six vertical components `k₃` admit a
resonance `σ₁k₃|k| + σ₂m₃|m| + σ₃n₃|n| = 0` with `m = -k-n`. -/
theorem card_resonant_vertical (n : Mode) (hn : n 2 ≠ 0) (a b : ℤ) :
    {x : ℤ | ∃ σ₁ σ₂ σ₃ : Sgn,
      sg σ₁ * (x : ℝ) * absk (mk3 a b x) + sg σ₂ * ((-mk3 a b x - n) 2 : ℤ) * absk (-mk3 a b x - n)
        + sg σ₃ * (n 2 : ℝ) * absk n = 0}.encard ≤ 6 := by
  set P := resPoly ((a + n 0) ^ 2 + (b + n 1) ^ 2) (a ^ 2 + b ^ 2) (n 2)
    (n 2 ^ 2 * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2)) with hP
  have hdeg : P.natDegree = 6 := natDegree_resPoly _ _ _ hn
  have hP0 : P ≠ 0 := by
    intro h0
    simp [h0] at hdeg
  have hsub : {x : ℤ | ∃ σ₁ σ₂ σ₃ : Sgn,
      sg σ₁ * (x : ℝ) * absk (mk3 a b x) + sg σ₂ * ((-mk3 a b x - n) 2 : ℤ) * absk (-mk3 a b x - n)
        + sg σ₃ * (n 2 : ℝ) * absk n = 0} ⊆ (P.roots.toFinset : Set ℤ) := by
    rintro x ⟨σ₁, σ₂, σ₃, h⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hP0).2 (resonant_isRoot n a b x σ₁ σ₂ σ₃ h)
  refine (Set.encard_le_encard hsub).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  have hcard : P.roots.toFinset.card ≤ 6 :=
    (Multiset.toFinset_card_le _).trans (hdeg ▸ Polynomial.card_roots' P)
  exact_mod_cast hcard

end OVNS
