import OddViscousNS.Quant.Arith.Weighted.SurfacePoints

/-!
# Facts about an intermediate shell

Notation: `N = |n|`, `U = log(T/g)`, `λ = log N`, `F = surfacePoly Δ z n₃ n_i n_j s₃ g`, and the
shell box `B = (2T/g, 4gN/T, max 2 N)`.

* `shellBox_ge_two`: all sides are `≥ 2` (`T/g > N^{p*} ≥ 1`; `T ≤ 2z ≤ 2N ≤ 2gN`).
* `surface_X3_form`: `F = 4g²(n_i² + n_j²) X₃² + F₁(X₁,X₂) X₃ + F₀(X₁,X₂)` (the shape required by
  `resultant_projection`; the only `X₃²` terms come from `4g²n_j²X₃²` and `(2gL − 2g n_i X₃)²`).
* `surface_irreducible_rat`: absolute irreducibility gives irreducibility over `ℚ` (a factorization
  over `ℚ` into non-units stays one over `ℚ̄`).
* `boxSize_ge`: `X₁⁴X₂²` is in the support (`surface_coeff_X14X22`, coefficient `4Δ²g⁴ ≠ 0`), so
  `𝔗 ≥ B₀⁴B₁²`.
-/

open MvPolynomial

noncomputable section

namespace OVNS.Quant

/-- Elementary consequences of the shell hypotheses. -/
private lemma shell_facts {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T) :
    1 ≤ Δ ∧ (z : ℝ) ≤ absk n ∧ (1 : ℝ) ≤ g ∧ 2 ≤ absk n ∧ (T : ℝ) ≤ 2 * absk n ∧
      1 < (T : ℝ) / g ∧ 1 ≤ z := by
  obtain ⟨hsq, hn, -, hT1, hT2, hgN, hTg⟩ := hH
  have hΔ : 1 ≤ Δ := Nat.one_le_iff_ne_zero.mpr fun h => by
    subst h; exact not_squarefree_zero hsq
  have hzN : (z : ℝ) ≤ absk n := by
    rw [absk_eq_sqrt_nsqZ, hn]
    apply Real.le_sqrt_of_sq_le
    have : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    push_cast
    nlinarith [sq_nonneg (z : ℝ)]
  have hz1 : 1 ≤ z := by omega
  have hN1 : (1 : ℝ) ≤ absk n := le_trans (by exact_mod_cast hz1) hzN
  have hp := pStar_bounds
  have h1 : (1 : ℝ) ≤ absk n ^ (pStar - 1 / 4) := Real.one_le_rpow hN1 (by linarith)
  have h2 : (1 : ℝ) ≤ absk n ^ pStar := Real.one_le_rpow hN1 (by linarith)
  have hg2 : 2 ≤ g := by
    have : (1 : ℝ) < g := lt_of_le_of_lt h1 hgN
    exact_mod_cast this
  have hg0 : (0 : ℝ) < g := by positivity
  have hTg' : (g : ℝ) < T := by
    have := lt_of_le_of_lt h2 hTg
    rwa [one_lt_div hg0] at this
  have hT3 : g < T := by exact_mod_cast hTg'
  have hz2 : 2 ≤ z := by omega
  refine ⟨hΔ, hzN, by exact_mod_cast (by omega : 1 ≤ g), ?_, ?_, lt_of_le_of_lt h2 hTg, hz1⟩
  · exact le_trans (by exact_mod_cast hz2) hzN
  · have : (T : ℝ) ≤ 2 * z := by exact_mod_cast hT2
    linarith

theorem shellBox_ge_two {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T) :
    ∀ i, 2 ≤ shellBox g T (absk n) i := by
  obtain ⟨-, -, hg1, hN2, hTN, hTg, -⟩ := shell_facts hH
  have hg0 : (0 : ℝ) < g := by linarith
  have hT0 : (0 : ℝ) < T := by
    have := (one_lt_div hg0).mp hTg
    linarith
  intro i
  fin_cases i
  · simp only [shellBox, Fin.zero_eta, Matrix.cons_val_zero]
    rw [mul_div_assoc]
    linarith
  · simp only [shellBox, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [le_div_iff₀ hT0]
    nlinarith
  · simp only [shellBox, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons]
    exact le_max_left _ _

theorem surface_X3_form (Δ z n3 ni nj s3 g : ℤ) :
    ∃ F1 F0 : MvPolynomial (Fin 2) ℤ, surfacePoly Δ z n3 ni nj s3 g =
      C (4 * g ^ 2 * (ni ^ 2 + nj ^ 2)) * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 +
        rename Fin.castSucc F0 := by
  set L : MvPolynomial (Fin 2) ℤ := -C (2 * Δ * g ^ 2) * X 0 ^ 2 * X 1 - C (Δ * g ^ 3) * X 0 ^ 2
    - C (2 * Δ * g ^ 2 * s3 * z) * X 0 - C (Δ * g * z ^ 2) - C (2 * n3 ^ 2) * X 1 with hL
  set xs : MvPolynomial (Fin 2) ℤ := C g * X 0 + C (s3 * z) + X 0 * X 1 with hxs
  refine ⟨-C (4 * g * ni) * L, L ^ 2 + C (4 * nj ^ 2 * n3 ^ 2) * X 1 ^ 2
    - C (4 * g ^ 2 * nj ^ 2 * Δ) * xs ^ 2, ?_⟩
  simp only [surfacePoly, hL, hxs, map_add, map_sub, map_mul, map_neg, map_pow,
    rename_C, rename_X]
  have e0 : (Fin.castSucc (0 : Fin 2) : Fin 3) = 0 := rfl
  have e1 : (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 := rfl
  simp only [e0, e1, map_ofNat]
  ring

/-- An injective map of coefficient fields reflects units of multivariate polynomials. -/
private lemma isUnit_of_isUnit_map {σ K L : Type*} [_root_.Field K] [_root_.Field L]
    (f : K →+* L) {A : MvPolynomial σ K} (h : IsUnit (MvPolynomial.map f A)) : IsUnit A := by
  rw [isUnit_iff_totalDegree_of_isReduced] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [coeff_map] at h1
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, map_zero] at h1
    exact not_isUnit_zero h1
  · rwa [totalDegree, support_map_of_injective _ f.injective] at h2

theorem surface_irreducible_rat {m : ℕ} (F : MvPolynomial (Fin m) ℤ) (hF : AbsIrred F) :
    Irreducible (MvPolynomial.map (Int.castRingHom ℚ) F) := by
  unfold AbsIrred at hF
  have hcomp : Int.castRingHom (AlgebraicClosure ℚ) =
      (algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
  rw [hcomp, ← MvPolynomial.map_map] at hF
  refine ⟨fun hu => hF.not_isUnit (hu.map _), fun A B hAB => ?_⟩
  rw [hAB, map_mul] at hF
  rcases hF.isUnit_or_isUnit rfl with h | h
  · exact Or.inl (isUnit_of_isUnit_map _ h)
  · exact Or.inr (isUnit_of_isUnit_map _ h)

theorem boxSize_ge (Δ z n3 ni nj s3 g : ℤ) (hΔ : Δ ≠ 0) (hg : g ≠ 0) (B : Fin 3 → ℝ)
    (hB : ∀ i, 0 ≤ B i) :
    B 0 ^ 4 * B 1 ^ 2 ≤ boxSize (surfacePoly Δ z n3 ni nj s3 g) B := by
  have _ := hB
  have hmem : (Finsupp.single 0 4 + Finsupp.single 1 2 : Fin 3 →₀ ℕ) ∈
      (surfacePoly Δ z n3 ni nj s3 g).support := by
    rw [mem_support_iff, surface_coeff_X14X22]
    positivity
  have hbdd : BddAbove ((fun e : Fin 3 →₀ ℕ => ∏ i, B i ^ (e i)) ''
      ((surfacePoly Δ z n3 ni nj s3 g).support : Set (Fin 3 →₀ ℕ))) :=
    ((Finset.finite_toSet _).image _).bddAbove
  have := le_csSup hbdd ⟨_, hmem, rfl⟩
  refine le_trans (le_of_eq ?_) this
  simp [Fin.prod_univ_three, Finsupp.single_apply]

/-- Upper bound for the shell box sides: all are at most `4N`. -/
private lemma shellBox_le {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T) :
    ∀ l, shellBox g T (absk n) l ≤ 4 * absk n := by
  obtain ⟨-, -, hg1, hN, hTN, hTg, -⟩ := shell_facts hH
  have hg0 : (0 : ℝ) < g := by linarith
  have hgT : (g : ℝ) < T := (one_lt_div hg0).mp hTg
  have hT0 : (0 : ℝ) < T := by linarith
  intro l
  fin_cases l
  · simp only [shellBox, Fin.zero_eta, Matrix.cons_val_zero]
    rw [div_le_iff₀ hg0]
    nlinarith
  · simp only [shellBox, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [div_le_iff₀ hT0]
    nlinarith
  · change max 2 (absk n) ≤ 4 * absk n
    rw [max_eq_right hN]
    linarith

/-- Lower bound for the shell box sides: all are at least `N^{p*−1/4}`. -/
private lemma shellBox_ge_rpow {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T) :
    ∀ l, absk n ^ (pStar - 1 / 4) ≤ shellBox g T (absk n) l := by
  obtain ⟨-, -, hg1, hN, hTN, hTg, -⟩ := shell_facts hH
  obtain ⟨-, -, -, -, -, hgN, hTgN⟩ := hH
  have hp := pStar_bounds
  have hg0 : (0 : ℝ) < g := by linarith
  have hgT : (g : ℝ) < T := (one_lt_div hg0).mp hTg
  have hT0 : (0 : ℝ) < T := by linarith
  have hN1 : (1 : ℝ) ≤ absk n := by linarith
  intro l
  fin_cases l
  · simp only [shellBox, Fin.zero_eta, Matrix.cons_val_zero]
    have h1 : absk n ^ (pStar - 1 / 4) ≤ absk n ^ pStar :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h2 : (T : ℝ) / g ≤ 2 * T / g := by
      rw [mul_div_assoc]
      have : 0 ≤ (T : ℝ) / g := by positivity
      linarith
    linarith
  · simp only [shellBox, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [le_div_iff₀ hT0]
    have h1 : (g : ℝ) * T ≤ 4 * g * absk n := by nlinarith
    have h2 : absk n ^ (pStar - 1 / 4) * T ≤ g * T := by nlinarith
    linarith
  · change absk n ^ (pStar - 1 / 4) ≤ max 2 (absk n)
    rw [max_eq_right hN]
    calc absk n ^ (pStar - 1 / 4) ≤ absk n ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = absk n := Real.rpow_one _

/-- The degree ratio `log B_max / log B_min ≤ 6` on a shell. -/
private lemma shell_cover_ratio {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T)
    (hN : 2 ≤ absk n) :
    Real.log (max (shellBox g T (absk n) 0) (max (shellBox g T (absk n) 1)
        (shellBox g T (absk n) 2))) ≤
      6 * Real.log (min (shellBox g T (absk n) 0) (min (shellBox g T (absk n) 1)
        (shellBox g T (absk n) 2))) ∧
    0 ≤ Real.log (max (shellBox g T (absk n) 0) (max (shellBox g T (absk n) 1)
        (shellBox g T (absk n) 2))) ∧
    0 < Real.log (min (shellBox g T (absk n) 0) (min (shellBox g T (absk n) 1)
        (shellBox g T (absk n) 2))) := by
  have hp := pStar_bounds
  have hge := shellBox_ge_two hH
  have hle := shellBox_le hH
  have hlo := shellBox_ge_rpow hH
  have hN0 : 0 < absk n := by linarith
  have hN1 : 1 ≤ absk n := by linarith
  have hBmax_le : max (shellBox g T (absk n) 0) (max (shellBox g T (absk n) 1)
      (shellBox g T (absk n) 2)) ≤ 4 * absk n := max_le (hle 0) (max_le (hle 1) (hle 2))
  have hBmax2 : 2 ≤ max (shellBox g T (absk n) 0) (max (shellBox g T (absk n) 1)
      (shellBox g T (absk n) 2)) := le_trans (hge 0) (le_max_left _ _)
  have hBmin2 : 2 ≤ min (shellBox g T (absk n) 0) (min (shellBox g T (absk n) 1)
      (shellBox g T (absk n) 2)) := le_min (hge 0) (le_min (hge 1) (hge 2))
  have hBminN : absk n ^ (pStar - 1 / 4) ≤ min (shellBox g T (absk n) 0)
      (min (shellBox g T (absk n) 1) (shellBox g T (absk n) 2)) :=
    le_min (hlo 0) (le_min (hlo 1) (hlo 2))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlmin2 := Real.log_le_log (by norm_num) hBmin2
  have hlN0 : 0 ≤ Real.log (absk n) := Real.log_nonneg hN1
  have hlminN := (Real.log_le_log (by positivity) hBminN)
  rw [Real.log_rpow hN0] at hlminN
  have hlmax := Real.log_le_log (by linarith) hBmax_le
  rw [Real.log_mul (by norm_num) hN0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    at hlmax
  push_cast at hlmax
  have hq : (1 / 4) * Real.log (absk n) ≤ (pStar - 1 / 4) * Real.log (absk n) :=
    mul_le_mul_of_nonneg_right (by linarith) hlN0
  refine ⟨by linarith, Real.log_nonneg (by linarith), by linarith⟩

end OVNS.Quant

end
