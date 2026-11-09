import OddViscousNS.Quant.Arith.Weighted.Surface

/-!
# The resultant with a linear degree bound (route L11)

`resultant_projection_lin`: for `F = c X₃² + F₁ X₃ + F₀` of total degree `≤ 6` and `G` not divisible by
`F` over `ℚ`, the `X₃`-resultant `R` is a nonzero plane polynomial with `deg R ≤ 8 deg G`, vanishing on
the projections of the common integer zeros.  The bound is obtained column by column in the Sylvester
matrix: two columns of coefficients of `G`, `deg_{X₃} G` columns of coefficients of `F`.
-/

open MvPolynomial

namespace OVNS.Quant.Surf

open private lastEquiv lastEquiv_C lastEquiv_X2 lastEquiv_rename eval_eq_lastEquiv
  totalDegree_coeff_lastEquiv_le natDegree_lastEquiv_le resultant_ne_zero_aux
  from OddViscousNS.Quant.Arith.Weighted.Surface

/-- Total degree bound for a determinant, column by column. -/
lemma totalDegree_det_le_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2) ℤ))
    (w : Fin n → ℕ) (hM : ∀ i j, (M i j).totalDegree ≤ w j) :
    M.det.totalDegree ≤ ∑ j, w j := by
  rw [Matrix.det_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ ↦ ?_)
  refine (totalDegree_smul_le _ _).trans ((totalDegree_finsetProd _ _).trans ?_)
  exact Finset.sum_le_sum fun i _ ↦ hM _ _

/-- Column bounds for the Sylvester matrix. -/
lemma totalDegree_sylvester_col {D E m n : ℕ} (f g : Polynomial (MvPolynomial (Fin 2) ℤ))
    (hf : ∀ k, (f.coeff k).totalDegree ≤ E) (hg : ∀ k, (g.coeff k).totalDegree ≤ D)
    (i j : Fin (m + n)) : (Polynomial.sylvester f g m n i j).totalDegree ≤
      Fin.addCases (fun _ => D) (fun _ => E) j := by
  unfold Polynomial.sylvester
  rw [Matrix.of_apply]
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · rw [Fin.addCases_left, Fin.addCases_left]
    split_ifs
    · exact hg _
    · rw [totalDegree_zero]; exact Nat.zero_le _
  · rw [Fin.addCases_right, Fin.addCases_right]
    split_ifs
    · exact hf _
    · rw [totalDegree_zero]; exact Nat.zero_le _

/-- **L11.** The resultant with `deg R ≤ 8 deg G`. -/
theorem resultant_projection_lin (F G : MvPolynomial (Fin 3) ℤ) (c : ℤ) (hc : c ≠ 0)
    (F1 F0 : MvPolynomial (Fin 2) ℤ)
    (hF : F = C c * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 + rename Fin.castSucc F0)
    (hF6 : F.totalDegree ≤ 6)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) F))
    (hFG : ¬ MvPolynomial.map (Int.castRingHom ℚ) F ∣ MvPolynomial.map (Int.castRingHom ℚ) G) :
    ∃ R : MvPolynomial (Fin 2) ℤ, R ≠ 0 ∧ R.totalDegree ≤ 8 * G.totalDegree ∧
      ∀ x : Fin 3 → ℤ, eval x F = 0 → eval x G = 0 →
        eval (fun i => x (Fin.castSucc i)) R = 0 := by
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
  · have hdeg := totalDegree_det_le_sum (Polynomial.sylvester f g 2 g.natDegree)
      (Fin.addCases (fun _ => G.totalDegree) (fun _ => 6))
      (fun i j ↦ totalDegree_sylvester_col f g
        (fun k ↦ (totalDegree_coeff_lastEquiv_le F k).trans hF6)
        (fun k ↦ totalDegree_coeff_lastEquiv_le G k) i j)
    have hs : ∑ j : Fin (2 + g.natDegree), (Fin.addCases (fun _ => G.totalDegree) (fun _ => 6) j : ℕ)
        = 2 * G.totalDegree + 6 * g.natDegree := by
      rw [Fin.sum_univ_add]
      simp [mul_comm]
    have hd : g.natDegree ≤ G.totalDegree := natDegree_lastEquiv_le G
    have h1 : (Polynomial.resultant f g 2 g.natDegree).totalDegree ≤
        2 * G.totalDegree + 6 * g.natDegree := by
      rw [← hs]
      exact hdeg
    omega
  · intro x hFx hGx
    obtain ⟨p, q, -, -, e⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g hf2.le le_rfl
      (Or.inl two_ne_zero)
    have := congrArg (Polynomial.eval₂ (eval fun i ↦ x (Fin.castSucc i)) (x 2)) e
    rw [Polynomial.eval₂_C, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul,
      ← eval_eq_lastEquiv, ← eval_eq_lastEquiv, hFx, hGx] at this
    rw [← this]; ring

end OVNS.Quant.Surf
