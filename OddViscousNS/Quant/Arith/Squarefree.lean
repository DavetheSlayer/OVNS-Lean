import Mathlib

/-!
# Squarefree rigidity of a vanishing three-term radical sum

If `α√A + β√B + χ√C = 0` with positive naturals `A, B, C` and nonzero integers `α, β, χ`, then
`A, B, C` have a common squarefree part: `A = Δx²`, `B = Δy²`, `C = Δz²` (isolate one radical and
square: `√(AB) ∈ ℚ`, so `AB` is a perfect square and `A, B` have equal squarefree parts; likewise
for `C`).  Also the exponent facts used by the weighted resonance count.
-/

namespace OVNS.Quant

/-- Squarefree parts are unique. -/
private lemma sqf_eq_of_mul_sq {a b m n : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hm : m ≠ 0) (hn : n ≠ 0) (h : a * m ^ 2 = b * n ^ 2) : a = b := by
  refine Nat.eq_of_factorization_eq ha.ne_zero hb.ne_zero fun p ↦ ?_
  have h1 := ha.natFactorization_le_one p
  have h2 := hb.natFactorization_le_one p
  have := congrArg (fun k : ℕ ↦ k.factorization p) h
  rw [Nat.factorization_mul ha.ne_zero (pow_ne_zero 2 hm),
    Nat.factorization_mul hb.ne_zero (pow_ne_zero 2 hn), Nat.factorization_pow,
    Nat.factorization_pow] at this
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at this
  omega

/-- Two positive naturals whose product is a perfect square have the same squarefree part. -/
theorem same_squarefree_part_of_mul_sq {A B : ℕ} (hA : 0 < A) (hB : 0 < B) {r : ℕ}
    (h : A * B = r ^ 2) : ∃ Δ x y : ℕ, Squarefree Δ ∧ A = Δ * x ^ 2 ∧ B = Δ * y ^ 2 := by
  obtain ⟨a, x, _, hx, rfl, ha⟩ := Nat.sq_mul_squarefree_of_pos hA
  obtain ⟨b, y, _, hy, rfl, hb⟩ := Nat.sq_mul_squarefree_of_pos hB
  have hr : r ≠ 0 := by
    rintro rfl
    have : x ^ 2 * a * (y ^ 2 * b) ≠ 0 := by positivity
    simp_all
  have hab : a = b := by
    refine sqf_eq_of_mul_sq ha hb (m := b * x * y) (n := r) (by positivity) hr ?_
    calc a * (b * x * y) ^ 2 = b * (x ^ 2 * a * (y ^ 2 * b)) := by ring
      _ = b * r ^ 2 := by rw [h]
  subst hab
  exact ⟨a, x, y, ha, by ring, by ring⟩

/-- A vanishing three-term radical sum forces `AB` to be a square. -/
private lemma isSquare_mul_of_radical {A B C : ℕ} {α β χ : ℤ}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : (α : ℝ) * Real.sqrt A + β * Real.sqrt B + χ * Real.sqrt C = 0) :
    IsSquare (A * B) := by
  by_contra hns
  have hirr : Irrational (Real.sqrt ((A * B : ℕ) : ℝ)) := irrational_sqrt_natCast_iff.mpr hns
  apply hirr
  refine ⟨((χ ^ 2 * C - α ^ 2 * A - β ^ 2 * B : ℚ) / (2 * α * β)), ?_⟩
  have hC : (χ : ℝ) * Real.sqrt C = -((α : ℝ) * Real.sqrt A + β * Real.sqrt B) := by linarith
  have hsq : ((χ : ℝ) * Real.sqrt C) ^ 2 = ((α : ℝ) * Real.sqrt A + β * Real.sqrt B) ^ 2 := by
    rw [hC]; ring
  have hAB : Real.sqrt ((A * B : ℕ) : ℝ) = Real.sqrt A * Real.sqrt B := by
    push_cast
    exact Real.sqrt_mul (Nat.cast_nonneg _) _
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
  have e1 : Real.sqrt (A : ℝ) ^ 2 = A := Real.sq_sqrt (Nat.cast_nonneg _)
  have e2 : Real.sqrt (B : ℝ) ^ 2 = B := Real.sq_sqrt (Nat.cast_nonneg _)
  have h2 : (2 * α * β : ℝ) ≠ 0 := by
    have : (α : ℝ) ≠ 0 := by exact_mod_cast hα
    have : (β : ℝ) ≠ 0 := by exact_mod_cast hβ
    positivity
  rw [hAB]
  push_cast
  rw [div_eq_iff h2]
  nlinarith [e1, e2, hsq]

/-- Squarefree rigidity. -/
theorem squarefree_rigidity {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) {α β χ : ℤ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hχ : χ ≠ 0)
    (h : (α : ℝ) * Real.sqrt A + β * Real.sqrt B + χ * Real.sqrt C = 0) :
    ∃ Δ x y z : ℕ, Squarefree Δ ∧ A = Δ * x ^ 2 ∧ B = Δ * y ^ 2 ∧ C = Δ * z ^ 2 := by
  obtain ⟨r, hr⟩ := isSquare_mul_of_radical hα hβ h
  obtain ⟨s, hs⟩ := isSquare_mul_of_radical (A := A) (B := C) (C := B) (χ := β) hα hχ
    (by linarith)
  obtain ⟨Δ, x, y, hΔ, hAx, hBy⟩ := 
    same_squarefree_part_of_mul_sq hA hB (r := r) (by rw [hr]; ring)
  obtain ⟨Δ', x', z, hΔ', hAx', hCz⟩ :=
    same_squarefree_part_of_mul_sq hA hC (r := s) (by rw [hs]; ring)
  have hx : x ≠ 0 := by rintro rfl; simp at hAx; omega
  have hx' : x' ≠ 0 := by rintro rfl; simp at hAx'; omega
  have : Δ = Δ' := sqf_eq_of_mul_sq hΔ hΔ' hx hx' (hAx.symm.trans hAx')
  subst this
  exact ⟨Δ, x, y, z, hΔ, hAx, hBy, hCz⟩

/-- `p* = (√17 − 3)/2` solves `p² + 3p − 2 = 0`. -/
noncomputable def pStar : ℝ := (Real.sqrt 17 - 3) / 2

/-- `p*` is a root of `p² + 3p − 2`. -/
theorem pStar_eq : pStar ^ 2 + 3 * pStar - 2 = 0 := by
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  unfold pStar
  nlinarith

/-- Numerical bounds on `p*`. -/
theorem pStar_bounds : 1 / 2 < pStar ∧ pStar < 281 / 500 ∧ pStar < 7 / 10 := by
  have h1 : (4 : ℝ) < Real.sqrt 17 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 17 < (4124 / 1000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold pStar
  refine ⟨by linarith, by linarith, by linarith⟩

/-- `f(u) = u(1−u)/(2+2u)` satisfies `4 f(p*) = p*²` and is antitone on `[√2 − 1, 1]`. -/
theorem covering_exponent_identity : 4 * (pStar * (1 - pStar) / (2 + 2 * pStar)) = pStar ^ 2 := by
  have h := pStar_eq
  have hp := pStar_bounds.1
  have hd : (2 + 2 * pStar) ≠ 0 := by linarith
  field_simp
  linear_combination (-2) * h

/-- Antitonicity of `u(1−u)/(2+2u)` on `[√2 − 1, 1]`. -/
theorem covering_exponent_antitone {u v : ℝ} (hu : Real.sqrt 2 - 1 ≤ u) (huv : u ≤ v)
    (_hv : v ≤ 1) :
    v * (1 - v) / (2 + 2 * v) ≤ u * (1 - u) / (2 + 2 * u) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  have hu0 : 0 < u := by
    have : (1 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  have hsq : 2 ≤ (u + 1) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr huv) (by nlinarith : (0:ℝ) ≤ u + v + u * v - 1)]

end OVNS.Quant
