import Mathlib

/-!
# The uniform divisor bound `τ(n) ≤ C_δ n^δ`

For every `δ > 0` there is `C` with `(n.divisors.card : ℝ) ≤ C n^δ` for all `n ≥ 1`.
Proof: `τ` is multiplicative, `τ(p^a) = a + 1`; for primes `p ≥ 2^{1/δ}` one has
`(a+1) ≤ p^{aδ}`; the finitely many primes `p < 2^{1/δ}` contribute a factor
`max_a (a+1)/p^{aδ} ≤ C_p`; take `C = ∏_{p < 2^{1/δ}} C_p`.  Also the elementary
`τ(n) ≤ 2 √n` and the gcd sum `∑_{1 ≤ t < T} gcd(t, v) ≤ T τ(v)`.
-/

namespace OVNS.Quant

open Finset

/-- `τ(n) ≤ 2 √n`. -/
theorem card_divisors_le_two_sqrt (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card : ℝ) ≤ 2 * Real.sqrt n := by
  set S := n.divisors.filter (fun d ↦ d * d ≤ n) with hS
  have hsub : n.divisors ⊆ S ∪ S.image (fun d ↦ n / d) := by
    intro d hd
    have hdn := Nat.mem_divisors.1 hd
    by_cases h : d * d ≤ n
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hd, h⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨n / d, ?_, ?_⟩)
      · obtain ⟨e, he⟩ := hdn.1
        have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
        have hed : n / d = e := by rw [he, Nat.mul_div_cancel_left _ hd0]
        rw [hed]
        have hlt : e < d := by
          by_contra hc
          push Not at hc
          exact h (he ▸ Nat.mul_le_mul_left d hc)
        refine Finset.mem_filter.2
          ⟨Nat.mem_divisors.2 ⟨⟨d, by rw [he, mul_comm]⟩, by omega⟩, ?_⟩
        rw [he]; exact Nat.mul_le_mul_right e hlt.le
      · exact Nat.div_div_self hdn.1 (by omega)
  have hScard : S.card ≤ Nat.sqrt n := by
    calc S.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
          refine Finset.card_le_card fun d hd ↦ ?_
          obtain ⟨hd1, hd2⟩ := Finset.mem_filter.1 hd
          have := Nat.pos_of_mem_divisors hd1
          exact Finset.mem_Icc.2 ⟨this, Nat.le_sqrt.2 hd2⟩
      _ = Nat.sqrt n := by simp
  have hcard : n.divisors.card ≤ 2 * Nat.sqrt n := by
    calc n.divisors.card ≤ (S ∪ S.image (fun d ↦ n / d)).card := Finset.card_le_card hsub
      _ ≤ S.card + (S.image (fun d ↦ n / d)).card := Finset.card_union_le _ _
      _ ≤ S.card + S.card := Nat.add_le_add_left Finset.card_image_le _
      _ ≤ 2 * Nat.sqrt n := by omega
  calc (n.divisors.card : ℝ) ≤ ((2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = 2 * (Nat.sqrt n : ℝ) := by push_cast; ring
    _ ≤ 2 * Real.sqrt n := by
      have := Real.nat_sqrt_le_real_sqrt (a := n)
      linarith

/-- Bernoulli: `1 + a (x - 1) ≤ x ^ a` for `x ≥ 1`. -/
private lemma bernoulli_nat (x : ℝ) (hx : 1 ≤ x) (a : ℕ) :
    1 + (a : ℝ) * (x - 1) ≤ x ^ a := by
  have := one_add_mul_le_pow (a := x - 1) (by linarith) a
  simpa using this

/-- The uniform divisor bound. -/
theorem divisor_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  set q : ℝ := (2 : ℝ) ^ δ with hq
  have hq1 : 1 < q := Real.one_lt_rpow (by norm_num) hδ
  set K : ℝ := 1 + 1 / (q - 1) with hK
  have hK1 : 1 ≤ K := by
    have : 0 < 1 / (q - 1) := by apply div_pos one_pos; linarith
    linarith
  -- threshold N with p ≥ N → p ^ δ ≥ 2
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ p : ℕ, N ≤ p → (2 : ℝ) ≤ (p : ℝ) ^ δ := by
    obtain ⟨N, hN⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / δ))
    refine ⟨N, fun p hp ↦ ?_⟩
    have h1 : (2 : ℝ) ^ (1 / δ) ≤ p := hN.trans (by exact_mod_cast hp)
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / δ)) ^ δ := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one]
      _ ≤ (p : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) h1 hδ.le
  let c : ℕ → ℝ := fun p ↦ if p < N then K else 1
  -- per-prime bound
  have hloc : ∀ p : ℕ, p.Prime → ∀ a : ℕ,
      ((a : ℝ) + 1) ≤ c p * ((p : ℝ) ^ δ) ^ a := by
    intro p hp a
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpq : q ≤ (p : ℝ) ^ δ := Real.rpow_le_rpow (by norm_num) hp2 hδ.le
    by_cases h : p < N
    · have hcp : c p = K := by simp [c, h]
      rw [hcp]
      have hb := bernoulli_nat ((p : ℝ) ^ δ) (by linarith) a
      have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have hq0 : 0 < q - 1 := by linarith
      have hmul : (a : ℝ) * (q - 1) ≤ (a : ℝ) * ((p : ℝ) ^ δ - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) ha
      have : (a : ℝ) + 1 ≤ K * (1 + a * (q - 1)) := by
        rw [hK]
        have e : (1 + 1 / (q - 1)) * (1 + a * (q - 1)) =
            1 + 1 / (q - 1) + a * (q - 1) + a := by
          field_simp; ring
        rw [e]
        have : 0 < 1 / (q - 1) := by apply div_pos one_pos; linarith
        nlinarith
      calc (a : ℝ) + 1 ≤ K * (1 + a * (q - 1)) := this
        _ ≤ K * ((p : ℝ) ^ δ) ^ a := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith
    · have hcp : c p = 1 := by simp [c, h]
      rw [hcp, one_mul]
      have h2 := hN p (by omega)
      have hb := bernoulli_nat ((p : ℝ) ^ δ) (by linarith) a
      have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have : (a : ℝ) ≤ a * ((p : ℝ) ^ δ - 1) := by nlinarith
      linarith
  refine ⟨K ^ N, by positivity, fun n hn ↦ ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hnδ : (n : ℝ) ^ δ =
      ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) := by
    have hnp := Nat.prod_primeFactors_pow_factorization hn0
    have hcast : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by
      have := congrArg (Nat.cast : ℕ → ℝ) hnp
      push_cast at this
      exact this
    rw [hcast, ← Real.finsetProd_rpow _ _ (fun p _ ↦ by positivity)]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity), mul_comm]
  have hc : ∏ p ∈ n.primeFactors, c p ≤ K ^ N := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    refine pow_le_pow_right₀ hK1 ?_
    calc #{p ∈ n.primeFactors | p < N} ≤ #(Finset.range N) := by
          refine Finset.card_le_card fun p hp ↦ ?_
          simp only [Finset.mem_filter] at hp
          exact Finset.mem_range.2 hp.2
      _ = N := Finset.card_range N
  rw [Nat.card_divisors hn0, Nat.cast_prod, hnδ]
  calc ∏ p ∈ n.primeFactors, (((n.factorization p + 1 : ℕ)) : ℝ)
      ≤ ∏ p ∈ n.primeFactors, (c p * ((p : ℝ) ^ δ) ^ (n.factorization p)) := by
        refine Finset.prod_le_prod₀ (fun p _ ↦ by positivity) (fun p hp ↦ ?_)
        push_cast
        exact hloc p (Nat.prime_of_mem_primeFactors hp) _
    _ = (∏ p ∈ n.primeFactors, c p) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) :=
        Finset.prod_mul_distrib
    _ ≤ K ^ N * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) :=
        mul_le_mul_of_nonneg_right hc (Finset.prod_nonneg fun p _ ↦ by positivity)

/-- `∑_{1 ≤ t < T} gcd(t, v) ≤ T · τ(v)`. -/
theorem gcd_sum_le (T v : ℕ) (hv : 1 ≤ v) :
    ∑ t ∈ Finset.Ico 1 T, Nat.gcd t v ≤ T * v.divisors.card := by
  have hmaps : ∀ t ∈ Finset.Ico 1 T, Nat.gcd t v ∈ v.divisors := fun t _ ↦
    Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right t v, by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ d ∈ v.divisors, ∑ t ∈ Finset.Ico 1 T with Nat.gcd t v = d, Nat.gcd t v
      ≤ ∑ d ∈ v.divisors, T := by
        refine Finset.sum_le_sum fun d _ ↦ ?_
        rw [Finset.sum_congr rfl fun t ht ↦ (Finset.mem_filter.1 ht).2, Finset.sum_const,
          smul_eq_mul]
        calc #{t ∈ Finset.Ico 1 T | Nat.gcd t v = d} * d
            ≤ (T / d) * d := by
              refine Nat.mul_le_mul_right _ ?_
              rw [← Nat.Ioc_filter_dvd_card_eq_div]
              refine Finset.card_le_card fun t ht ↦ ?_
              simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc] at ht ⊢
              exact ⟨⟨by omega, by omega⟩, ht.2 ▸ Nat.gcd_dvd_left t v⟩
          _ ≤ T := Nat.div_mul_le_self T d
    _ = T * v.divisors.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end OVNS.Quant
