import OddViscousNS.Quant.Arith.Surface.Hensel
import OddViscousNS.Quant.Arith.Surface.Convex
import OddViscousNS.Quant.Arith.Surface.Exponents

/-!
# The determinant at a node: arithmetic input (route L4, L5, first half of L10)

* `prime_val`: at a prime `p` with `#{F = 0 in 𝔽_p³} ≤ p² + 18p` the monomial determinant of zeros of `F`
  is divisible by `p^n` with `n ≥ (2√2/3) E_p^{3/2}/√(p²+18p) − 2E_p`, where `E_p` counts the rows with
  `p ∤ m`.  Rows with `p ∣ m` are discarded (they are singletons of the class decomposition).
* `q_val`: all rows congruent `(q^a, q^a, q)`, `q ∤ m`: `(q^a)^{V(E)}` divides the determinant.
* `abs_det_le_fact_mul`, `log_abs_det_le`: the Leibniz bound.
* `sum_log_le_log_abs`: prime powers dividing `D ≠ 0`.
-/

open Finset MvPolynomial

namespace OVNS.Quant.Surf

lemma Vs_zero : Vs 0 = 0 := by simp [Vs]

lemma eval_map_cast {R : Type*} [CommRing R] (x : Fin 3 → ℤ) (P : MvPolynomial (Fin 3) ℤ) :
    eval (fun i => (x i : R)) (MvPolynomial.map (Int.castRingHom R) P) = ((eval x P : ℤ) : R) := by
  induction P using MvPolynomial.induction_on <;> simp_all

/-- The divisibility at one prime, with the rows `p ∣ m` discarded. -/
theorem prime_val {J : Type*} [Fintype J] [DecidableEq J]
    (c : ℤ) (F1 F0 : MvPolynomial (Fin 2) ℤ) (F : MvPolynomial (Fin 3) ℤ)
    (hF : F = C c * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 + rename Fin.castSucc F0)
    (p : ℕ) [Fact p.Prime] (pts : J → Fin 3 → ℤ) (es : J → Fin 3 → ℕ)
    (hz : ∀ j, eval (pts j) F = 0)
    (hcount : ((univ.filter fun ξ : Fin 3 → ZMod p =>
      eval ξ (MvPolynomial.map (Int.castRingHom (ZMod p)) F) = 0).card : ℕ) ≤ p ^ 2 + 18 * p) :
    ∃ n : ℕ, (p : ℤ) ^ n ∣ (monoMat pts es).det ∧
      2 * Real.sqrt 2 / 3 *
          (((univ.filter fun j => ¬ (p : ℤ) ∣ mVal c F1 (pts j)).card : ℕ) : ℝ) ^ ((3 : ℝ) / 2) /
            Real.sqrt ((p : ℝ) ^ 2 + 18 * p)
        - 2 * (((univ.filter fun j => ¬ (p : ℤ) ∣ mVal c F1 (pts j)).card : ℕ) : ℝ) ≤ n := by
  classical
  have hp : p.Prime := Fact.out
  rcases isEmpty_or_nonempty J with hJ | hJ
  · refine ⟨0, by simp, ?_⟩
    have : (univ.filter fun j : J => ¬ (p : ℤ) ∣ mVal c F1 (pts j)) = ∅ := by
      ext j; exact (hJ.false j).elim
    rw [this]
    simp [Real.zero_rpow]
  set κ : J → (Fin 3 → ZMod p) := fun j i => (pts j i : ZMod p) with hκ
  set good : Finset J := univ.filter fun j => ¬ (p : ℤ) ∣ mVal c F1 (pts j) with hgood
  set g := Function.invFunOn κ (good : Set J) with hg
  have hgmem : ∀ j ∈ good, g (κ j) ∈ good := fun j hj =>
    Function.invFunOn_mem ⟨j, hj, rfl⟩
  have hgeq : ∀ j ∈ good, κ (g (κ j)) = κ j := fun j hj =>
    Function.invFunOn_eq ⟨j, hj, rfl⟩
  set rep : J → J := fun j => if j ∈ good then g (κ j) else j with hrep
  have hrep_good : ∀ j ∈ good, rep j = g (κ j) := fun j hj => by simp only [hrep, hj, ite_true]
  have hrep_bad : ∀ j, j ∉ good → rep j = j := fun j hj => by simp only [hrep, hj, ite_false]
  have h1 : ∀ j, rep j = j ∨ ¬ (p : ℤ) ∣ mVal c F1 (pts (rep j)) := by
    intro j
    by_cases hj : j ∈ good
    · right
      rw [hrep_good j hj]
      exact (mem_filter.1 (hgmem j hj)).2
    · exact Or.inl (hrep_bad j hj)
  have hcl : ∀ j, rep j ≠ j → ∀ i, (p : ℤ) ∣ pts j i - pts (rep j) i := by
    intro j hne i
    have hj : j ∈ good := by
      by_contra h
      exact hne (hrep_bad j h)
    have := congrFun (hgeq j hj) i
    rw [← hrep_good j hj] at this
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 this
  have hdvd := pow_dvd_det c F1 F0 F hF p 1 hp le_rfl pts es hz rep h1 (fun j hj => by
    have := hcl j hj
    simpa using ⟨this 0, this 1, this 2⟩)
  rw [pow_one] at hdvd
  refine ⟨∑ ξ, Vs (univ.filter fun j => rep j = ξ).card, hdvd, ?_⟩
  set Ξ := good.image rep with hΞ
  have hΞgood : ∀ ξ ∈ Ξ, ξ ∈ good := by
    intro ξ hξ
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hξ
    rw [hrep_good j hj]
    exact hgmem j hj
  set s : J → ℕ := fun ξ => (univ.filter fun j => rep j = ξ).card with hs
  have hsum : ∑ ξ ∈ Ξ, s ξ = good.card := by
    rw [card_eq_sum_card_image rep good]
    refine sum_congr rfl fun ξ hξ => ?_
    simp only [hs]
    congr 1
    ext j
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    by_contra hj
    have : j = ξ := by rw [← h, hrep_bad j hj]
    exact hj (this ▸ hΞgood ξ hξ)
  have hcardΞ : (Ξ.card : ℝ) ≤ (p : ℝ) ^ 2 + 18 * p := by
    have hle : Ξ.card ≤ (univ.filter fun ξ : Fin 3 → ZMod p =>
        eval ξ (MvPolynomial.map (Int.castRingHom (ZMod p)) F) = 0).card := by
      refine card_le_card_of_injOn κ (fun ξ _ => ?_) ?_
      · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, hκ]
        rw [eval_map_cast, hz ξ]
        simp
      · intro ξ hξ ξ' hξ' he
        obtain ⟨j, hj, rfl⟩ := mem_image.1 (mem_coe.1 hξ)
        obtain ⟨j', hj', rfl⟩ := mem_image.1 (mem_coe.1 hξ')
        rw [hrep_good j hj, hrep_good j' hj', hgeq j hj, hgeq j' hj'] at he
        rw [hrep_good j hj, hrep_good j' hj', he]
    have := hle.trans hcount
    exact_mod_cast this
  have hpos : (0 : ℝ) < (p : ℝ) ^ 2 + 18 * p := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  have hjen := sum_Vs_ge Ξ s ((p : ℝ) ^ 2 + 18 * p) hpos hcardΞ
  rw [hsum] at hjen
  refine hjen.trans ?_
  have : ∑ ξ ∈ Ξ, Vs (s ξ) ≤ ∑ ξ, Vs (s ξ) :=
    sum_le_sum_of_subset (subset_univ _)
  exact_mod_cast this

/-- All rows congruent: the full power. -/
theorem q_val {J : Type*} [Fintype J] [DecidableEq J]
    (c : ℤ) (F1 F0 : MvPolynomial (Fin 2) ℤ) (F : MvPolynomial (Fin 3) ℤ)
    (hF : F = C c * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 + rename Fin.castSucc F0)
    (q a : ℕ) (hq : q.Prime) (ha : 1 ≤ a) (pts : J → Fin 3 → ℤ) (es : J → Fin 3 → ℕ)
    (hz : ∀ j, eval (pts j) F = 0) (hm : ∀ j, ¬ (q : ℤ) ∣ mVal c F1 (pts j))
    (hcong : ∀ j j', ((q : ℤ) ^ a ∣ pts j 0 - pts j' 0) ∧ ((q : ℤ) ^ a ∣ pts j 1 - pts j' 1) ∧
      ((q : ℤ) ∣ pts j 2 - pts j' 2)) :
    (q : ℤ) ^ (a * Vs (Fintype.card J)) ∣ (monoMat pts es).det := by
  classical
  rcases isEmpty_or_nonempty J with hJ | ⟨⟨j₀⟩⟩
  · have : Fintype.card J = 0 := Fintype.card_eq_zero
    simp [Vs_zero]
  have h := pow_dvd_det c F1 F0 F hF q a hq ha pts es hz (fun _ => j₀)
    (fun j => Or.inr (hm j₀)) (fun j _ => hcong j j₀)
  have e : ∑ ξ, Vs (univ.filter fun j : J => j₀ = ξ).card = Vs (Fintype.card J) := by
    rw [Finset.sum_eq_single j₀]
    · simp [Finset.card_univ]
    · intro ξ _ hξ
      have : (univ.filter fun j : J => j₀ = ξ) = ∅ := by
        ext j
        simp [hξ.symm]
      rw [this, card_empty, Vs_zero]
    · intro h
      exact (h (mem_univ _)).elim
  rw [e, ← pow_mul] at h
  exact h

/-- Leibniz bound for a general index type, with column bounds. -/
theorem abs_det_le_fact_mul {J : Type*} [Fintype J] [DecidableEq J] (A : Matrix J J ℤ) (c : J → ℝ)
    (h : ∀ i j, |(A i j : ℝ)| ≤ c j) :
    |(A.det : ℝ)| ≤ (Fintype.card J).factorial * ∏ j, c j := by
  rw [Matrix.det_apply]
  push_cast
  calc |∑ σ : Equiv.Perm J, ((Equiv.Perm.sign σ • ∏ i, A (σ i) i : ℤ) : ℝ)|
      ≤ ∑ σ : Equiv.Perm J, |((Equiv.Perm.sign σ • ∏ i, A (σ i) i : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm J, ∏ j, c j := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have : |((Equiv.Perm.sign σ • ∏ i, A (σ i) i : ℤ) : ℝ)| = ∏ i, |(A (σ i) i : ℝ)| := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;>
            simp [h1, Finset.abs_prod]
        rw [this]
        exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => h _ j)
    _ = (Fintype.card J).factorial * ∏ j, c j := by
        simp [Finset.card_univ, Fintype.card_perm]

/-- Upper bound for the logarithm of a nonzero monomial determinant. -/
theorem log_abs_det_le {J : Type*} [Fintype J] [DecidableEq J]
    (pts : J → Fin 3 → ℤ) (es : J → Fin 3 → ℕ) (B : Fin 3 → ℝ) (hB : ∀ i, 1 ≤ B i)
    (hpts : ∀ j i, |(pts j i : ℝ)| ≤ B i) (hdet : (monoMat pts es).det ≠ 0) :
    Real.log |((monoMat pts es).det : ℝ)| ≤ Real.log (Fintype.card J).factorial +
      ∑ j, wt (fun i => Real.log (B i)) (es j) := by
  have hB0 : ∀ i, 0 < B i := fun i => by linarith [hB i]
  set l : Fin 3 → ℝ := fun i => Real.log (B i) with hl
  have hrow : ∀ j i', |((monoMat pts es j i' : ℤ) : ℝ)| ≤ Real.exp (wt l (es i')) := by
    intro j i'
    simp only [monoMat, Matrix.of_apply]
    push_cast
    rw [Finset.abs_prod]
    have e : Real.exp (wt l (es i')) = ∏ k, B k ^ es i' k := by
      simp only [wt, Real.exp_sum]
      refine prod_congr rfl fun k _ => ?_
      rw [mul_comm, Real.exp_mul, hl, Real.exp_log (hB0 k), Real.rpow_natCast]
    rw [e]
    refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun k _ => ?_
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hpts j k) _
  have hle := abs_det_le_fact_mul (monoMat pts es) (fun i' => Real.exp (wt l (es i'))) hrow
  have hprod : ∏ j, Real.exp (wt l (es j)) = Real.exp (∑ j, wt l (es j)) :=
    (Real.exp_sum _ _).symm
  rw [hprod] at hle
  have hpos : 0 < |((monoMat pts es).det : ℝ)| := by
    rw [abs_pos]; exact_mod_cast hdet
  have h2 := Real.log_le_log hpos hle
  have hfac : (0 : ℝ) < (Fintype.card J).factorial := by exact_mod_cast Nat.factorial_pos _
  rwa [Real.log_mul hfac.ne' (Real.exp_pos _).ne', Real.log_exp] at h2

/-- Prime powers dividing a nonzero integer. -/
theorem sum_log_le_log_abs (D : ℤ) (hD : D ≠ 0) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (n : ℕ → ℕ) (h : ∀ p ∈ S, (p : ℤ) ^ n p ∣ D) :
    ∑ p ∈ S, (n p : ℝ) * Real.log p ≤ Real.log |(D : ℝ)| := by
  classical
  have hcop : (S : Set ℕ).Pairwise (Function.onFun IsCoprime fun p : ℕ => (p : ℤ) ^ n p) := by
    intro p hp p' hp' hne
    have h1 : IsCoprime (p : ℤ) (p' : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (hS p hp) (hS p' hp')).2 hne)
    exact IsCoprime.pow h1
  have hdvd : ∏ p ∈ S, (p : ℤ) ^ n p ∣ D := Finset.prod_dvd_of_coprime hcop h
  have hle : |∏ p ∈ S, (p : ℤ) ^ n p| ≤ |D| :=
    abs_dvd_abs _ _ |>.2 hdvd |> Int.le_of_dvd (abs_pos.2 hD)
  have hpos : ∀ p ∈ S, (0 : ℝ) < (p : ℝ) ^ n p := fun p hp => by
    have : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    positivity
  have hle' : ∏ p ∈ S, (p : ℝ) ^ n p ≤ |(D : ℝ)| := by
    have : ((|∏ p ∈ S, (p : ℤ) ^ n p| : ℤ) : ℝ) ≤ ((|D| : ℤ) : ℝ) := by exact_mod_cast hle
    push_cast at this
    rwa [abs_of_nonneg (Finset.prod_nonneg fun p hp => (hpos p hp).le)] at this
  have hlog := Real.log_le_log (Finset.prod_pos hpos) hle'
  rw [Real.log_prod fun p hp => (hpos p hp).ne'] at hlog
  refine le_trans (le_of_eq ?_) hlog
  refine sum_congr rfl fun p _ => ?_
  rw [Real.log_pow]

end OVNS.Quant.Surf
