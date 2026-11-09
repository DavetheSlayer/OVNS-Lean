import OddViscousNS.Quant.Defs

/-!
# Covering the integer zeros of a plane polynomial by `ℚ`-irreducible factors

`resultant_factor_cover`: a nonzero `R ∈ ℤ[X₁,X₂]` factors over the UFD `ℚ[X₁,X₂]` as
`R = c ∏ Pᵢ^{eᵢ}` with `Pᵢ` irreducible and nonconstant; clearing denominators
`Hᵢ = dᵢPᵢ ∈ ℤ[X₁,X₂]`
(`dᵢ ∈ ℤ∖{0}`, a unit of `ℚ`) keeps `Hᵢ` irreducible over `ℚ` with `deg Hᵢ = deg Pᵢ ≤ deg R`, and
the number of distinct factors is at most `∑ deg Pᵢ ≤ deg R`.  An integer zero of `R` is a zero of
some `Pᵢ`, hence of `Hᵢ`.  (A constant `R ≠ 0` has no zeros: take the empty list.)
-/

open MvPolynomial

namespace OVNS.Quant

/-- Casting an integer evaluation to `ℚ` is evaluation of the mapped polynomial. -/
private lemma cast_eval_eq (x : Fin 2 → ℤ) (p : MvPolynomial (Fin 2) ℤ) :
    ((eval x p : ℤ) : ℚ) = eval (fun i ↦ (x i : ℚ)) (map (Int.castRingHom ℚ) p) := by
  induction p using MvPolynomial.induction_on <;> simp_all

/-- Mapping `ℤ → ℚ` preserves total degree. -/
private lemma totalDegree_map_int (p : MvPolynomial (Fin 2) ℤ) :
    (map (Int.castRingHom ℚ) p).totalDegree = p.totalDegree := by
  simp only [totalDegree, support_map_of_injective _ (f := Int.castRingHom ℚ) Int.cast_injective]

/-- Clearing denominators of a rational polynomial. -/
private lemma clear_denom (F : MvPolynomial (Fin 2) ℚ) :
    ∃ H : MvPolynomial (Fin 2) ℤ, ∃ d : ℤ, d ≠ 0 ∧
      map (Int.castRingHom ℚ) H = C (d : ℚ) * F := by
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨monomial u a.num, a.den, by exact_mod_cast a.den_ne_zero, ?_⟩
    rw [map_monomial, C_mul_monomial]
    congr 1
    simp [Rat.den_mul_eq_num]
  | add p q hp hq =>
    obtain ⟨H₁, d₁, hd₁, h₁⟩ := hp
    obtain ⟨H₂, d₂, hd₂, h₂⟩ := hq
    refine ⟨C d₂ * H₁ + C d₁ * H₂, d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    simp only [map_add, map_mul, map_C, h₁, h₂, Int.coe_castRingHom, Int.cast_mul]
    ring

/-- The cover statement for a nonzero rational polynomial, by irreducible induction. -/
private lemma cover_aux (p : MvPolynomial (Fin 2) ℚ) : p ≠ 0 →
    ∃ L : List (MvPolynomial (Fin 2) ℤ), L.length ≤ p.totalDegree ∧
      (∀ H ∈ L, Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H) ∧
        H.totalDegree ≤ p.totalDegree) ∧
      ∀ x : Fin 2 → ℤ, eval (fun i ↦ (x i : ℚ)) p = 0 → ∃ H ∈ L, eval x H = 0 := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => intro h; exact absurd rfl h
  | unit u hu =>
    intro _
    refine ⟨[], by simp, by simp, fun x hx ↦ ?_⟩
    exact absurd hx ((hu.map (eval fun i ↦ (x i : ℚ))).ne_zero)
  | mul a i ha hi ih =>
    intro _
    obtain ⟨L, hL1, hL2, hL3⟩ := ih ha
    obtain ⟨H, d, hd, hH⟩ := clear_denom i
    have hi0 : i ≠ 0 := hi.ne_zero
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    have hCd : C (d : ℚ) ≠ (0 : MvPolynomial (Fin 2) ℚ) := by simpa using hdq
    have hdeg : (i * a).totalDegree = i.totalDegree + a.totalDegree :=
      totalDegree_mul_of_isDomain hi0 ha
    have hi1 : 1 ≤ i.totalDegree := by
      by_contra hc
      have h0 : i.totalDegree = 0 := by omega
      have hc := totalDegree_eq_zero_iff_eq_C.mp h0
      have hc0 : i.coeff 0 ≠ 0 := by intro h0'; exact hi0 (by rw [hc, h0', C_0])
      exact hi.not_isUnit (hc ▸ (Ne.isUnit hc0).map C)
    have hHdeg : H.totalDegree = i.totalDegree := by
      rw [← totalDegree_map_int, hH, totalDegree_mul_of_isDomain hCd hi0, totalDegree_C,
        zero_add]
    refine ⟨H :: L, ?_, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro G hG
      rcases List.mem_cons.mp hG with rfl | hG
      · refine ⟨?_, by omega⟩
        rw [hH, irreducible_isUnit_mul ((Ne.isUnit hdq).map C)]
        exact hi
      · obtain ⟨h1, h2⟩ := hL2 G hG
        exact ⟨h1, by omega⟩
    · intro x hx
      rw [map_mul] at hx
      rcases mul_eq_zero.mp hx with h | h
      · refine ⟨H, List.mem_cons_self .., ?_⟩
        have : ((eval x H : ℤ) : ℚ) = 0 := by
          rw [cast_eval_eq, hH, map_mul, eval_C, h, mul_zero]
        exact_mod_cast this
      · obtain ⟨G, hG, hG0⟩ := hL3 x h
        exact ⟨G, List.mem_cons_of_mem _ hG, hG0⟩

/-- Integer zeros of `R ≠ 0` are covered by at most `deg R` `ℚ`-irreducible integer factors. -/
theorem resultant_factor_cover (R : MvPolynomial (Fin 2) ℤ) (hR : R ≠ 0) :
    ∃ L : List (MvPolynomial (Fin 2) ℤ), L.length ≤ R.totalDegree ∧
      (∀ H ∈ L, Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H) ∧
        H.totalDegree ≤ R.totalDegree) ∧
      ∀ x : Fin 2 → ℤ, eval x R = 0 → ∃ H ∈ L, eval x H = 0 := by
  have hRq : map (Int.castRingHom ℚ) R ≠ 0 := by
    intro h
    apply hR
    exact map_injective _ (RingHom.injective_int _) (by rw [h, map_zero])
  obtain ⟨L, h1, h2, h3⟩ := cover_aux _ hRq
  rw [totalDegree_map_int] at h1 h2
  refine ⟨L, h1, h2, fun x hx ↦ h3 x ?_⟩
  rw [← cast_eval_eq, hx, Int.cast_zero]

end OVNS.Quant
