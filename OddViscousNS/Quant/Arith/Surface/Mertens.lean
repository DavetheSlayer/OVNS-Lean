import Mathlib

/-!
# Mertens in a window (route L6)

`∑_{P<p≤x} log p/p ≥ log(x/P) − C`, from `log n! = ∑ v_p(n!) log p` and `θ(n) ≤ n log 4`.
-/

open Finset

namespace OVNS.Quant.Surf

section M
open Real


/-- primes `≤ n`. -/
def PL (n : ℕ) : Finset ℕ := (range (n + 1)).filter Nat.Prime

lemma mem_PL {n p : ℕ} : p ∈ PL n ↔ p ≤ n ∧ p.Prime := by
  simp [PL]

/-- `log n! = ∑_{p ≤ n} v_p(n!) log p`. -/
lemma log_factorial_eq (n : ℕ) : Real.log (n.factorial : ℝ) =
    ∑ p ∈ PL n, (n.factorial.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    refine mem_PL.2 ⟨?_, hpp⟩
    exact (Nat.Prime.dvd_factorial hpp).1 (Nat.dvd_of_mem_primeFactors (by simpa using hp))
  · intro p _ hp'
    have hz : n.factorial.factorization p = 0 := Finsupp.notMem_support_iff.1 hp'
    simp [hz]

/-- `v_p(n!) ≤ n/(p-1)`. -/
lemma fact_le (n p : ℕ) (hp : p.Prime) :
    (n.factorial.factorization p : ℝ) ≤ n / (p - 1) := by
  have h := hp.sub_one_mul_multiplicity_factorial (n := n)
  rw [Nat.multiplicity_eq_factorization hp] at h
  have hle : (p - 1) * n.factorial.factorization p ≤ n := by omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [le_div_iff₀ (by linarith)]
  have : ((p - 1 : ℕ) : ℝ) = p - 1 := by
    rw [Nat.cast_sub hp.one_lt.le]; simp
  have h2 : (((p - 1) * n.factorial.factorization p : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
  push_cast at h2
  rw [this] at h2
  linarith

/-- `n/p - 1 ≤ v_p(n!)`. -/
lemma le_fact (n p : ℕ) (hp : p.Prime) :
    (n : ℝ) / p - 1 ≤ (n.factorial.factorization p : ℝ) := by
  have h := Nat.factorization_factorial hp (n := n) (b := Nat.log p n + 2) (by omega)
  have h2 : n / p ≤ n.factorial.factorization p := by
    rw [h]
    have hm : 1 ∈ Ico 1 (Nat.log p n + 2) := by simp
    have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) hm
    simpa using this
  have h3 : (n : ℝ) / p ≤ (n / p : ℕ) + 1 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [div_le_iff₀ hp0]
    have := Nat.lt_div_mul_add (a := n) hp.pos
    have h4 : n ≤ n / p * p + p := by omega
    have : (n : ℝ) ≤ ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast h4
    linarith
  have h5 : ((n / p : ℕ) : ℝ) ≤ n.factorial.factorization p := by exact_mod_cast h2
  linarith

/-- `θ(n) ≤ n log 4`. -/
lemma theta_PL (n : ℕ) : ∑ p ∈ PL n, Real.log p ≤ n * Real.log 4 := by
  have h := Chebyshev.theta_le_log4_mul_x (x := n) (by positivity)
  have e : Chebyshev.theta n = ∑ p ∈ PL n, Real.log p := by
    rw [Chebyshev.theta_eq_sum_Icc]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Nat.floor_natCast, mem_filter, mem_Icc, mem_PL]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨Nat.zero_le _, h1⟩, h2⟩
  rw [e] at h
  linarith

lemma log_nonneg_prime {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log p :=
  Real.log_nonneg (by exact_mod_cast hp.one_le)

/-- Upper bound: `∑_{p ≤ n} log p / p ≤ log n + log 4`. -/
lemma S_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ PL n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    have : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) this
    rwa [Real.log_pow] at h
  have h2 : ∑ p ∈ PL n, ((n : ℝ) / p - 1) * Real.log p ≤ Real.log (n.factorial : ℝ) := by
    rw [log_factorial_eq]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp := (mem_PL.1 hp).2
    exact mul_le_mul_of_nonneg_right (le_fact n p hpp) (log_nonneg_prime hpp)
  have h3 : ∑ p ∈ PL n, ((n : ℝ) / p - 1) * Real.log p =
      n * ∑ p ∈ PL n, Real.log p / p - ∑ p ∈ PL n, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have h4 := theta_PL n
  rw [h3] at h2
  have h5 : n * ∑ p ∈ PL n, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    rw [mul_add]; linarith
  exact le_of_mul_le_mul_left h5 hn0

/-- The tail constant. -/
noncomputable def C0 : ℝ := ∑' m : ℕ, 4 * ((m : ℝ) ^ ((3 : ℝ) / 2))⁻¹

lemma summable_C0 : Summable fun m : ℕ => 4 * ((m : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
  (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 4

lemma tail_term (p : ℕ) (hp : p.Prime) :
    Real.log p / (p * (p - 1)) ≤ 4 * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : Real.log p ≤ 2 * (p : ℝ) ^ ((1 : ℝ) / 2) := by
    have := Real.log_le_rpow_div (x := p) hp0.le (ε := 1 / 2) (by norm_num)
    linarith
  have hs : (p : ℝ) ^ ((3 : ℝ) / 2) = p ^ 2 / (p : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [eq_div_iff (by positivity), ← Real.rpow_add hp0, ← Real.rpow_natCast]
    norm_num
  rw [hs, inv_div, div_le_iff₀ (by nlinarith)]
  have h3 : (p : ℝ) ^ 2 ≤ 2 * (p * (p - 1)) := by nlinarith
  have h4 : 0 < (p : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  calc Real.log p ≤ 2 * (p : ℝ) ^ ((1 : ℝ) / 2) := hlog
    _ = 2 * (p : ℝ) ^ ((1 : ℝ) / 2) * ((p : ℝ) ^ 2 / (p : ℝ) ^ 2) := by
        rw [div_self (by positivity)]; ring
    _ ≤ _ := by
      rw [show 2 * (p : ℝ) ^ ((1 : ℝ) / 2) * ((p : ℝ) ^ 2 / (p : ℝ) ^ 2) =
        2 * (p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ 2 * (p : ℝ) ^ 2 by ring]
      have h5 : 0 ≤ 2 * (p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left h3 h5
      refine this.trans (le_of_eq ?_)
      field_simp
      ring

lemma tail_sum (n : ℕ) : ∑ p ∈ PL n, Real.log p / (p * (p - 1)) ≤ C0 := by
  have h1 : ∑ p ∈ PL n, Real.log p / (p * (p - 1)) ≤
      ∑ p ∈ PL n, 4 * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
    Finset.sum_le_sum fun p hp => tail_term p (mem_PL.1 hp).2
  exact h1.trans (summable_C0.sum_le_tsum _ fun i _ => by positivity)

/-- Lower bound: `∑_{p ≤ n} log p / p ≥ log n - 1 - C0`. -/
lemma le_S (n : ℕ) (hn : 1 ≤ n) :
    Real.log n - 1 - C0 ≤ ∑ p ∈ PL n, Real.log p / p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : n * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (n : ℝ) hn0.le n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have h2 := Real.log_le_log (by positivity) h
    rw [Real.log_div (by positivity) hf.ne', Real.log_pow, Real.log_exp] at h2
    linarith
  have h2 : Real.log (n.factorial : ℝ) ≤ ∑ p ∈ PL n, ((n : ℝ) / (p - 1)) * Real.log p := by
    rw [log_factorial_eq]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp := (mem_PL.1 hp).2
    exact mul_le_mul_of_nonneg_right (fact_le n p hpp) (log_nonneg_prime hpp)
  have h3 : ∑ p ∈ PL n, ((n : ℝ) / (p - 1)) * Real.log p =
      n * (∑ p ∈ PL n, Real.log p / p + ∑ p ∈ PL n, Real.log p / (p * (p - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_PL.1 hp).2.one_lt
    have h' : (p : ℝ) - 1 ≠ 0 := by linarith
    have h'' : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [h3] at h2
  have h4 := tail_sum n
  have h5 : n * (Real.log n - 1) ≤ n * (∑ p ∈ PL n, Real.log p / p + C0) := by
    calc n * (Real.log n - 1) = n * Real.log n - n := by ring
      _ ≤ _ := h1.trans h2
      _ ≤ _ := by gcongr
  have := le_of_mul_le_mul_left h5 hn0
  linarith

/-- **Mertens in a window.** -/
theorem mertens_window : ∃ C : ℝ, 0 ≤ C ∧ ∀ P x : ℕ, 1 ≤ P → P ≤ x →
    Real.log x - Real.log P - C ≤ ∑ p ∈ (Ioc P x).filter Nat.Prime, Real.log p / p := by
  have hC0 : 0 ≤ C0 := tsum_nonneg fun m => by positivity
  refine ⟨1 + C0 + Real.log 4, by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith,
    fun P x hP hx => ?_⟩
  have hsplit : PL x = PL P ∪ (Ioc P x).filter Nat.Prime := by
    ext p
    simp only [mem_PL, mem_union, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : p ≤ P
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨⟨by omega, h1⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨h2, h3⟩
  have hdisj : Disjoint (PL P) ((Ioc P x).filter Nat.Prime) := by
    refine disjoint_left.2 fun p h1 h2 => ?_
    have := (mem_PL.1 h1).1
    have := (mem_Ioc.1 (mem_filter.1 h2).1).1
    omega
  have hsum : ∑ p ∈ PL x, Real.log p / p = ∑ p ∈ PL P, Real.log p / p +
      ∑ p ∈ (Ioc P x).filter Nat.Prime, Real.log p / p := by
    rw [hsplit, Finset.sum_union hdisj]
  have h1 := le_S x (by omega)
  have h2 := S_le P hP
  linarith


end M

end OVNS.Quant.Surf
