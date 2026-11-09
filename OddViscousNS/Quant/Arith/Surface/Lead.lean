import OddViscousNS.Quant.Arith.Weighted.Surface

/-!
# The lex leading monomial of the surface (route L9)

The lexicographic leading monomial of `surfacePoly` (with `X₀ > X₁ > X₂`) is `X₀⁴X₁²`, with coefficient
`4Δ²g⁴`.  So a nonzero `G` all of whose monomials have `e₀ < 4` or `e₁ < 2` is not divisible by the
surface over `ℚ` (`not_dvd_of_support`).
-/

open MvPolynomial MonomialOrder

namespace OVNS.Quant.Surf

/-- The lexicographic order with `X₀ > X₁ > X₂`. -/
noncomputable abbrev lx : MonomialOrder (Fin 3) := MonomialOrder.lex

/-- The monomial exponent `(i, j, k)`. -/
noncomputable def ex3 (i j k : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 k

@[simp] lemma ex3_zero (i j k : ℕ) : ex3 i j k 0 = i := by simp [ex3]
@[simp] lemma ex3_one (i j k : ℕ) : ex3 i j k 1 = j := by simp [ex3]
@[simp] lemma ex3_two (i j k : ℕ) : ex3 i j k 2 = k := by simp [ex3]

/-- Every monomial of `f` is at most `(i, j, k)` for the lexicographic order. -/
def Dle (f : MvPolynomial (Fin 3) ℤ) (i j k : ℕ) : Prop :=
  ∀ c ∈ f.support, c ≼[lx] ex3 i j k

lemma lex_le_of {c d : Fin 3 →₀ ℕ}
    (h : c 0 < d 0 ∨ (c 0 = d 0 ∧ c 1 < d 1) ∨ (c 0 = d 0 ∧ c 1 = d 1 ∧ c 2 ≤ d 2)) :
    c ≼[lx] d := by
  rw [MonomialOrder.lex_le_iff]
  rcases h with h | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
  · exact (show toLex c < toLex d from ⟨0, fun j hj => absurd hj (Fin.not_lt_zero _), h⟩).le
  · refine (show toLex c < toLex d from ⟨1, fun j hj => ?_, h1⟩).le
    have : j = 0 := by omega
    subst this
    exact h0
  · rcases h2.lt_or_eq with h3 | h3
    · refine (show toLex c < toLex d from ⟨2, fun j hj => ?_, h3⟩).le
      fin_cases j
      · exact h0
      · exact h1
      · exact absurd hj (lt_irrefl _)
    · have : c = d := by
        ext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h3
      rw [this]

lemma Dle.mono {f : MvPolynomial (Fin 3) ℤ} {i j k i' j' k' : ℕ} (h : Dle f i j k)
    (hl : i < i' ∨ (i = i' ∧ j < j') ∨ (i = i' ∧ j = j' ∧ k ≤ k')) : Dle f i' j' k' := by
  intro c hc
  refine le_trans (h c hc) (lex_le_of ?_)
  simpa using hl

lemma Dle.add {f g : MvPolynomial (Fin 3) ℤ} {i j k : ℕ} (hf : Dle f i j k) (hg : Dle g i j k) :
    Dle (f + g) i j k := by
  classical
  intro c hc
  rcases Finset.mem_union.1 (support_add hc) with h | h
  · exact hf c h
  · exact hg c h

lemma Dle.neg {f : MvPolynomial (Fin 3) ℤ} {i j k : ℕ} (hf : Dle f i j k) : Dle (-f) i j k := by
  intro c hc
  rw [support_neg] at hc
  exact hf c hc

lemma Dle.sub {f g : MvPolynomial (Fin 3) ℤ} {i j k : ℕ} (hf : Dle f i j k) (hg : Dle g i j k) :
    Dle (f - g) i j k := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

lemma Dle.mul {f g : MvPolynomial (Fin 3) ℤ} {i j k i' j' k' : ℕ} (hf : Dle f i j k)
    (hg : Dle g i' j' k') : Dle (f * g) (i + i') (j + j') (k + k') := by
  classical
  intro c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul f g hc)
  have e : ex3 (i + i') (j + j') (k + k') = ex3 i j k + ex3 i' j' k' := by
    ext l
    fin_cases l <;> simp
  rw [e]
  show lx.toSyn (a + b) ≤ lx.toSyn (ex3 i j k + ex3 i' j' k')
  rw [map_add, map_add]
  exact add_le_add (hf a ha) (hg b hb)

lemma Dle.mul' {f g : MvPolynomial (Fin 3) ℤ} {i j k i' j' k' a b d : ℕ} (hf : Dle f i j k)
    (hg : Dle g i' j' k') (h1 : i + i' = a) (h2 : j + j' = b) (h3 : k + k' = d) :
    Dle (f * g) a b d := by
  subst h1 h2 h3
  exact hf.mul hg

lemma Dle_C (r : ℤ) : Dle (C r) 0 0 0 := by
  classical
  intro c hc
  rw [support_C] at hc
  split_ifs at hc with h
  · simp at hc
  · rw [Finset.mem_singleton] at hc
    subst hc
    simp

lemma Dle_X (i : Fin 3) : Dle (X i) (if i = 0 then 1 else 0) (if i = 1 then 1 else 0)
    (if i = 2 then 1 else 0) := by
  classical
  intro c hc
  rw [support_X, Finset.mem_singleton] at hc
  subst hc
  refine lex_le_of ?_
  fin_cases i <;> simp

lemma Dle_X0 : Dle (X 0) 1 0 0 := by simpa using Dle_X 0
lemma Dle_X1 : Dle (X 1) 0 1 0 := by simpa using Dle_X 1
lemma Dle_X2 : Dle (X 2) 0 0 1 := by simpa using Dle_X 2

lemma Dle_sq {f : MvPolynomial (Fin 3) ℤ} {i j k a b d : ℕ} (hf : Dle f i j k)
    (h1 : 2 * i = a) (h2 : 2 * j = b) (h3 : 2 * k = d) : Dle (f ^ 2) a b d := by
  subst h1 h2 h3
  rw [sq, two_mul, two_mul, two_mul]
  exact hf.mul hf

/-- The surface has lex degree at most `(4, 2, 0)`. -/
lemma surface_Dle (Δ z n3 ni nj s3 g : ℤ) : Dle (surfacePoly Δ z n3 ni nj s3 g) 4 2 0 := by
  have h2 : ∀ r, Dle (C r * X 2 ^ 2) 0 0 2 := fun r =>
    (Dle_C r).mul' (Dle_sq Dle_X2 rfl rfl rfl) rfl rfl rfl
  have h1 : ∀ r, Dle (C r * X 1 ^ 2) 0 2 0 := fun r =>
    (Dle_C r).mul' (Dle_sq Dle_X1 rfl rfl rfl) rfl rfl rfl
  have h0 : ∀ r, Dle (C r * X 0 ^ 2) 2 0 0 := fun r =>
    (Dle_C r).mul' (Dle_sq Dle_X0 rfl rfl rfl) rfl rfl rfl
  have g0 : ∀ r, Dle (C r * X 0) 1 0 0 := fun r => (Dle_C r).mul' Dle_X0 rfl rfl rfl
  have g1 : ∀ r, Dle (C r * X 1) 0 1 0 := fun r => (Dle_C r).mul' Dle_X1 rfl rfl rfl
  have g2 : ∀ r, Dle (C r * X 2) 0 0 1 := fun r => (Dle_C r).mul' Dle_X2 rfl rfl rfl
  have tL : Dle (-C (2 * Δ * g ^ 2) * X 0 ^ 2 * X 1 - C (Δ * g ^ 3) * X 0 ^ 2
      - C (2 * Δ * g ^ 2 * s3 * z) * X 0 - C (Δ * g * z ^ 2) - C (2 * n3 ^ 2) * X 1
      - C (2 * g * ni) * X 2) 2 1 0 := by
    have a1 : Dle (-C (2 * Δ * g ^ 2) * X 0 ^ 2 * X 1) 2 1 0 :=
      ((Dle_C (2 * Δ * g ^ 2)).neg.mul' (Dle_sq Dle_X0 rfl rfl rfl) rfl rfl rfl).mul' Dle_X1
        rfl rfl rfl
    have a2 : Dle (C (Δ * g ^ 3) * X 0 ^ 2) 2 1 0 := (h0 _).mono (by norm_num)
    have a3 : Dle (C (2 * Δ * g ^ 2 * s3 * z) * X 0) 2 1 0 := (g0 _).mono (by norm_num)
    have a4 : Dle (C (Δ * g * z ^ 2)) 2 1 0 := (Dle_C _).mono (by norm_num)
    have a5 : Dle (C (2 * n3 ^ 2) * X 1) 2 1 0 := (g1 _).mono (by norm_num)
    have a6 : Dle (C (2 * g * ni) * X 2) 2 1 0 := (g2 _).mono (by norm_num)
    exact ((((a1.sub a2).sub a3).sub a4).sub a5).sub a6
  have txs : Dle (C g * X 0 + C (s3 * z) + X 0 * X 1) 1 1 0 := by
    have a1 : Dle (C g * X 0) 1 1 0 := (g0 _).mono (by norm_num)
    have a2 : Dle (C (s3 * z)) 1 1 0 := (Dle_C _).mono (by norm_num)
    have a3 : Dle (X 0 * X 1) 1 1 0 := Dle_X0.mul' Dle_X1 rfl rfl rfl
    exact (a1.add a2).add a3
  have a1 : Dle (C (4 * g ^ 2 * nj ^ 2) * X 2 ^ 2) 4 2 0 := (h2 _).mono (by norm_num)
  have a2 := Dle_sq (a := 4) (b := 2) (d := 0) tL rfl rfl rfl
  have a3 : Dle (C (4 * nj ^ 2 * n3 ^ 2) * X 1 ^ 2) 4 2 0 := (h1 _).mono (by norm_num)
  have a4' : Dle (C (4 * g ^ 2 * nj ^ 2 * Δ) * (C g * X 0 + C (s3 * z) + X 0 * X 1) ^ 2) 2 2 0 :=
    (Dle_C _).mul' (Dle_sq txs rfl rfl rfl) rfl rfl rfl
  have a4 := a4'.mono (i' := 4) (j' := 2) (k' := 0) (by norm_num)
  exact ((a1.add a2).add a3).sub a4

/-- The lex degree of the surface over `ℚ`. -/
lemma surface_degree (Δ z n3 ni nj s3 g : ℤ) (hΔ : Δ ≠ 0) (hg : g ≠ 0) :
    lx.degree (MvPolynomial.map (Int.castRingHom ℚ) (surfacePoly Δ z n3 ni nj s3 g)) =
      ex3 4 2 0 := by
  classical
  set F := surfacePoly Δ z n3 ni nj s3 g with hF
  have hsupp : (MvPolynomial.map (Int.castRingHom ℚ) F).support = F.support :=
    support_map_of_injective _ (RingHom.injective_int _)
  have hmem : ex3 4 2 0 ∈ F.support := by
    rw [mem_support_iff]
    have e : ex3 4 2 0 = Finsupp.single 0 4 + Finsupp.single 1 2 := by
      ext l
      fin_cases l <;> simp [ex3]
    rw [e, hF, surface_coeff_X14X22]
    positivity
  refine lx.toSyn.injective (le_antisymm ?_ ?_)
  · have := (degree_le_iff (m := lx) (f := MvPolynomial.map (Int.castRingHom ℚ) F)
      (d := ex3 4 2 0)).2 fun c hc => surface_Dle Δ z n3 ni nj s3 g c (hsupp ▸ hc)
    exact this
  · exact le_degree (m := lx) (by rw [hsupp]; exact hmem)

/-- **Non-divisibility.** A nonzero polynomial all of whose monomials have `e₀ < 4` or `e₁ < 2`
is not divisible by the surface over `ℚ`. -/
theorem not_dvd_of_support (Δ z n3 ni nj s3 g : ℤ) (hΔ : Δ ≠ 0) (hg : g ≠ 0)
    (G : MvPolynomial (Fin 3) ℤ) (hG0 : G ≠ 0) (hG : ∀ d ∈ G.support, d 0 < 4 ∨ d 1 < 2) :
    ¬ MvPolynomial.map (Int.castRingHom ℚ) (surfacePoly Δ z n3 ni nj s3 g) ∣
      MvPolynomial.map (Int.castRingHom ℚ) G := by
  classical
  rintro ⟨H, hH⟩
  have hinj := MvPolynomial.map_injective (σ := Fin 3) _ (RingHom.injective_int (Int.castRingHom ℚ))
  set F := surfacePoly Δ z n3 ni nj s3 g with hF
  have hG' : MvPolynomial.map (Int.castRingHom ℚ) G ≠ 0 := fun h =>
    hG0 (hinj (by rw [h, map_zero]))
  have hF' : MvPolynomial.map (Int.castRingHom ℚ) F ≠ 0 := by
    intro h
    rw [h, zero_mul] at hH
    exact hG' hH
  have hH0 : H ≠ 0 := by
    intro h
    rw [h, mul_zero] at hH
    exact hG' hH
  have hdeg := degree_mul (m := lx) hF' hH0
  rw [← hH, surface_degree Δ z n3 ni nj s3 g hΔ hg] at hdeg
  have hmem : lx.degree (MvPolynomial.map (Int.castRingHom ℚ) G) ∈ G.support := by
    have := degree_mem_support (m := lx) hG'
    rwa [support_map_of_injective _ (RingHom.injective_int _)] at this
  have h := hG _ hmem
  rw [hdeg] at h
  simp only [Finsupp.add_apply, ex3_zero, ex3_one] at h
  omega

end OVNS.Quant.Surf
