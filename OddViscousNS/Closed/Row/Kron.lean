import Mathlib

/-!
# Kronecker substitution: digits of packed sums

`Dig X N i` is the `i`-th base-`X` digit of `N`.  The central fact, `dig_fiber`: if `N` is a sum of
`u i · X^(idx i)` and the total weight of every fiber of `idx` is below `X`, the digits of `N` are the
fiber sums.  This covers products (index the sum by pairs), triple products and prefix sums.
`slot_lt` is the Cauchy-Schwarz bound on a slot of a product when the index maps are injective.
-/

open Finset

namespace OVNS
namespace Row

/-- The base-`X` digit of `N` at position `i`. -/
def Dig (X N i : ℕ) : ℕ := N / X ^ i % X

lemma dig_zero (X N : ℕ) : Dig X N 0 = N % X := by simp [Dig]

lemma dig_add_mul {X : ℕ} (hX : 0 < X) (a M i : ℕ) (ha : a < X) :
    Dig X (a + X * M) (i + 1) = Dig X M i := by
  unfold Dig
  rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hX, Nat.div_eq_of_lt ha,
    zero_add]

lemma dig_add_mul_zero {X : ℕ} (a M : ℕ) (ha : a < X) : Dig X (a + X * M) 0 = a := by
  rw [dig_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

/-- Digits of an explicit base-`X` expansion. -/
lemma dig_sum_range {X : ℕ} (hX : 0 < X) (n : ℕ) (d : ℕ → ℕ) (hd : ∀ i < n, d i < X) (j : ℕ)
    (hj : j < n) : Dig X (∑ i ∈ range n, d i * X ^ i) j = d j := by
  induction n generalizing d j with
  | zero => omega
  | succ n ih =>
    have e : ∑ i ∈ range (n + 1), d i * X ^ i = d 0 + X * ∑ i ∈ range n, d (i + 1) * X ^ i := by
      rw [sum_range_succ', mul_sum, add_comm]
      simp only [pow_zero, mul_one]
      congr 1
      exact sum_congr rfl fun i _ => by ring
    rw [e]
    cases j with
    | zero => exact dig_add_mul_zero _ _ (hd 0 (by omega))
    | succ j =>
      rw [dig_add_mul hX _ _ _ (hd 0 (by omega))]
      exact ih (fun i => d (i + 1)) (fun i hi => hd _ (by omega)) j (by omega)

/-- **Digits of a packed sum are fiber sums.** -/
theorem dig_fiber {ι : Type*} [DecidableEq ι] {X M : ℕ} (hX : 0 < X) (I : Finset ι) (u : ι → ℕ)
    (idx : ι → ℕ) (hM : ∀ i ∈ I, idx i < M)
    (hslot : ∀ s < M, ∑ i ∈ I.filter (fun i => idx i = s), u i < X) (s : ℕ) (hs : s < M) :
    Dig X (∑ i ∈ I, u i * X ^ idx i) s = ∑ i ∈ I.filter (fun i => idx i = s), u i := by
  have e : ∑ i ∈ I, u i * X ^ idx i =
      ∑ t ∈ range M, (∑ i ∈ I.filter (fun i => idx i = t), u i) * X ^ t := by
    rw [← sum_fiberwise_of_maps_to (g := idx) (t := range M) (fun i hi => mem_range.2 (hM i hi))]
    refine sum_congr rfl fun t _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [(mem_filter.1 hi).2]
  rw [e]
  exact dig_sum_range hX M _ hslot s hs

/-- The product of two packed sums, as a packed sum over pairs. -/
lemma pack_mul {ι κ : Type*} (I : Finset ι) (J : Finset κ) (u : ι → ℕ) (v : κ → ℕ) (idx : ι → ℕ)
    (jdx : κ → ℕ) (X : ℕ) :
    (∑ i ∈ I, u i * X ^ idx i) * (∑ j ∈ J, v j * X ^ jdx j) =
      ∑ q ∈ I ×ˢ J, (u q.1 * v q.2) * X ^ (idx q.1 + jdx q.2) := by
  rw [sum_mul_sum, sum_product]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [pow_add]; ring

/-- Cauchy-Schwarz on a slot of a product, for injective index maps. -/
theorem slot_sq_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (I : Finset ι) (J : Finset κ)
    (u : ι → ℕ) (v : κ → ℕ) (idx : ι → ℕ) (jdx : κ → ℕ)
    (hi : Set.InjOn idx I) (hj : Set.InjOn jdx J) (s : ℕ) :
    (∑ q ∈ (I ×ˢ J).filter (fun q => idx q.1 + jdx q.2 = s), u q.1 * v q.2) ^ 2 ≤
      (∑ i ∈ I, u i ^ 2) * (∑ j ∈ J, v j ^ 2) := by
  classical
  set P := (I ×ˢ J).filter (fun q => idx q.1 + jdx q.2 = s) with hP
  -- for each `i` at most one `j` is matched
  have huniq : ∀ q ∈ P, ∀ q' ∈ P, q.1 = q'.1 → q = q' := by
    intro q hq q' hq' h1
    have h2 := (mem_filter.1 hq).2
    have h3 := (mem_filter.1 hq').2
    have hjq := (mem_product.1 (mem_filter.1 hq).1).2
    have hjq' := (mem_product.1 (mem_filter.1 hq').1).2
    have h4 : jdx q.2 = jdx q'.2 := by rw [← h1] at h3; omega
    exact Prod.ext h1 (hj hjq hjq' h4)
  have h1 : (∑ q ∈ P, u q.1 * v q.2) ^ 2 ≤ (∑ q ∈ P, u q.1 ^ 2) * ∑ q ∈ P, v q.2 ^ 2 :=
    sum_mul_sq_le_sq_mul_sq P _ _
  have hI : ∑ q ∈ P, u q.1 ^ 2 ≤ ∑ i ∈ I, u i ^ 2 := by
    have : ∑ q ∈ P, u q.1 ^ 2 = ∑ i ∈ P.image Prod.fst, u i ^ 2 := by
      rw [sum_image]
      exact fun q hq q' hq' h => huniq q hq q' hq' h
    rw [this]
    refine sum_le_sum_of_subset ?_
    intro i hi
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hi
    exact (mem_product.1 (mem_filter.1 hq).1).1
  have hJ : ∑ q ∈ P, v q.2 ^ 2 ≤ ∑ j ∈ J, v j ^ 2 := by
    have huniq' : ∀ q ∈ P, ∀ q' ∈ P, q.2 = q'.2 → q = q' := by
      intro q hq q' hq' h1
      have h2 := (mem_filter.1 hq).2
      have h3 := (mem_filter.1 hq').2
      have hiq := (mem_product.1 (mem_filter.1 hq).1).1
      have hiq' := (mem_product.1 (mem_filter.1 hq').1).1
      have h4 : idx q.1 = idx q'.1 := by rw [← h1] at h3; omega
      exact Prod.ext (hi hiq hiq' h4) h1
    have : ∑ q ∈ P, v q.2 ^ 2 = ∑ j ∈ P.image Prod.snd, v j ^ 2 := by
      rw [sum_image]
      exact fun q hq q' hq' h => huniq' q hq q' hq' h
    rw [this]
    refine sum_le_sum_of_subset ?_
    intro j hj'
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hj'
    exact (mem_product.1 (mem_filter.1 hq).1).2
  exact h1.trans (Nat.mul_le_mul hI hJ)

/-- A slot of a product is below `X` when the norms of the factors are small. -/
theorem slot_lt {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (I : Finset ι) (J : Finset κ)
    (u : ι → ℕ) (v : κ → ℕ) (idx : ι → ℕ) (jdx : κ → ℕ) {X : ℕ}
    (hi : Set.InjOn idx I) (hj : Set.InjOn jdx J)
    (hX : (∑ i ∈ I, u i ^ 2) * (∑ j ∈ J, v j ^ 2) < X ^ 2) (s : ℕ) :
    ∑ q ∈ (I ×ˢ J).filter (fun q => idx q.1 + jdx q.2 = s), u q.1 * v q.2 < X := by
  have := slot_sq_le I J u v idx jdx hi hj s
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (this.trans_lt hX)

/-- **Digits of a product of packed sums.** -/
theorem dig_mul {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {X M : ℕ} (hX0 : 0 < X)
    (I : Finset ι) (J : Finset κ) (u : ι → ℕ) (v : κ → ℕ) (idx : ι → ℕ) (jdx : κ → ℕ)
    (hi : Set.InjOn idx I) (hj : Set.InjOn jdx J)
    (hM : ∀ q ∈ I ×ˢ J, idx q.1 + jdx q.2 < M)
    (hX : (∑ i ∈ I, u i ^ 2) * (∑ j ∈ J, v j ^ 2) < X ^ 2) (s : ℕ) (hs : s < M) :
    Dig X ((∑ i ∈ I, u i * X ^ idx i) * (∑ j ∈ J, v j * X ^ jdx j)) s =
      ∑ q ∈ (I ×ˢ J).filter (fun q => idx q.1 + jdx q.2 = s), u q.1 * v q.2 := by
  rw [pack_mul]
  exact dig_fiber hX0 (I ×ˢ J) (fun q => u q.1 * v q.2) (fun q => idx q.1 + jdx q.2) hM
    (fun t _ => slot_lt I J u v idx jdx hi hj hX t) s hs

/-- `N % X^n` has the digits of `N` below `n`. -/
lemma dig_mod {X : ℕ} (N n i : ℕ) (hi : i < n) :
    Dig X (N % X ^ n) i = Dig X N i := by
  unfold Dig
  obtain ⟨m, rfl⟩ : ∃ m, n = i + 1 + m := ⟨n - (i + 1), by omega⟩
  rw [pow_add, pow_add, pow_one, mul_assoc, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

/-- `N / X^s` has the digits of `N` shifted by `s`. -/
lemma dig_div {X : ℕ} (N s i : ℕ) : Dig X (N / X ^ s) i = Dig X N (s + i) := by
  unfold Dig
  rw [Nat.div_div_eq_div_mul, pow_add]

/-- A window of `N`. -/
lemma dig_window {X : ℕ} (N s n i : ℕ) (hi : i < n) :
    Dig X (N / X ^ s % X ^ n) i = Dig X N (s + i) := by
  rw [dig_mod _ _ _ hi, dig_div]

end Row
end OVNS
