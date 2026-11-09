import Mathlib

/-!
# Block divisibility of determinants (route L1, L2)

`Vs s = ∑_{t ≥ 1} (s - t(t+1)/2)₊`, the layer-cake bound `Vs_le_sum_deg` and `det_dvd_of_blocks`.
-/

open Finset

namespace OVNS.Quant.Surf

section O


/-- `V(s) = ∑_{t ≥ 1} (s - t(t+1)/2)₊`, the sum of the `s` smallest values of `a+b` on `ℕ²`. -/
def Vs (s : ℕ) : ℕ := ∑ t ∈ Icc 1 s, (s - t * (t + 1) / 2)

/-- exponents of degree `< t`. -/
def low (t : ℕ) : Finset (ℕ × ℕ) := (range t ×ˢ range t).filter fun d => d.1 + d.2 < t

lemma two_mul_card_low (t : ℕ) : 2 * (low t).card = t * (t + 1) := by
  induction t with
  | zero => simp [low]
  | succ t ih =>
    have h : low (t + 1) = low t ∪ (Finset.HasAntidiagonal.antidiagonal t) := by
      ext ⟨a, b⟩
      simp only [low, mem_filter, mem_product, mem_range, mem_union,
        Finset.HasAntidiagonal.mem_antidiagonal]
      omega
    have hd : Disjoint (low t) (Finset.HasAntidiagonal.antidiagonal t) := by
      refine disjoint_left.2 fun ⟨a, b⟩ h1 h2 => ?_
      simp only [low, mem_filter, mem_product, mem_range,
        Finset.HasAntidiagonal.mem_antidiagonal] at h1 h2
      omega
    rw [h, card_union_of_disjoint hd, Finset.Nat.card_antidiagonal, mul_add, ih]
    ring

lemma card_low (t : ℕ) : (low t).card = t * (t + 1) / 2 := by
  have := two_mul_card_low t
  omega

/-- The layer-cake lower bound: an injective assignment of exponents has total degree `≥ V(s)`. -/
lemma Vs_le_sum_deg {J : Type*} [DecidableEq J] (S : Finset J) (μ : J → ℕ × ℕ)
    (hμ : Set.InjOn μ S) : Vs S.card ≤ ∑ j ∈ S, ((μ j).1 + (μ j).2) := by
  classical
  set s := S.card with hs
  -- each degree dominates its layer count
  have h1 : ∀ j ∈ S, ∑ t ∈ Icc 1 s, (if t ≤ (μ j).1 + (μ j).2 then 1 else 0) ≤
      (μ j).1 + (μ j).2 := by
    intro j _
    rw [← card_filter]
    calc ((Icc 1 s).filter fun t => t ≤ (μ j).1 + (μ j).2).card
        ≤ (Icc 1 ((μ j).1 + (μ j).2)).card := by
          refine card_le_card fun t ht => ?_
          simp only [mem_filter, mem_Icc] at ht ⊢
          omega
      _ = _ := by simp
  have h2 : ∀ t ∈ Icc 1 s, s - t * (t + 1) / 2 ≤
      ∑ j ∈ S, (if t ≤ (μ j).1 + (μ j).2 then 1 else 0) := by
    intro t _
    rw [← card_filter]
    have hle : (S.filter fun j => (μ j).1 + (μ j).2 < t).card ≤ (low t).card := by
      refine card_le_card_of_injOn μ (fun j hj => ?_) (hμ.mono ?_)
      · simp only [coe_filter, Set.mem_ofPred_eq] at hj
        simp only [low, coe_filter, mem_product, mem_range, Set.mem_ofPred_eq]
        omega
      · intro j hj
        simp only [coe_filter, Set.mem_ofPred_eq] at hj
        exact hj.1
    have hadd := card_filter_add_card_filter_not (s := S) (fun j => t ≤ (μ j).1 + (μ j).2)
    have hsplit : (S.filter fun j => ¬ t ≤ (μ j).1 + (μ j).2) =
        S.filter fun j => (μ j).1 + (μ j).2 < t := by
      refine filter_congr fun j _ => ?_
      omega
    rw [hsplit] at hadd
    rw [card_low] at hle
    omega
  calc Vs s ≤ ∑ t ∈ Icc 1 s, ∑ j ∈ S, (if t ≤ (μ j).1 + (μ j).2 then 1 else 0) :=
        sum_le_sum h2
    _ = ∑ j ∈ S, ∑ t ∈ Icc 1 s, (if t ≤ (μ j).1 + (μ j).2 then 1 else 0) := sum_comm
    _ ≤ _ := sum_le_sum h1


end O


section B



open MvPolynomial in
/-- **Block divisibility.** If each row `j` of `M` is the value at `(U j, V j)`, with `ϖ ∣ U j, V j`,
of a polynomial vector depending only on the class `cls j`, then `ϖ^{∑_ξ V(s_ξ)}` divides `det M`. -/
theorem det_dvd_of_blocks {R : Type*} [CommRing R] {J κ : Type*} [Fintype J] [DecidableEq J]
    [Fintype κ] [DecidableEq κ] (M : Matrix J J R) (cls : J → κ) (ϖ : R) (U V : J → R)
    (hU : ∀ j, ϖ ∣ U j) (hV : ∀ j, ϖ ∣ V j)
    (Q : κ → J → MvPolynomial (Fin 2) R)
    (hM : ∀ j e, M j e = eval ![U j, V j] (Q (cls j) e)) :
    ϖ ^ (∑ ξ, Vs (univ.filter fun j => cls j = ξ).card) ∣ M.det := by
  classical
  -- all exponents occurring
  set Λ : Finset (Fin 2 →₀ ℕ) := univ.biUnion fun ξ => univ.biUnion fun e => (Q ξ e).support
    with hΛ
  set mon : J → (Fin 2 →₀ ℕ) → R := fun j d => U j ^ d 0 * V j ^ d 1 with hmon
  set c : J → (Fin 2 →₀ ℕ) → J → R := fun j d e => (Q (cls j) e).coeff d with hc
  -- rows expand over `Λ`
  have hrow : ∀ j, M j = ∑ d ∈ Λ, mon j d • c j d := by
    intro j
    funext e
    rw [hM, Finset.sum_apply]
    have hsub : (Q (cls j) e).support ⊆ Λ := by
      intro d hd
      simp only [hΛ, mem_biUnion, mem_univ, true_and]
      exact ⟨cls j, e, hd⟩
    rw [eval_eq', Finset.sum_subset hsub (f := fun d => (Q (cls j) e).coeff d *
      ∏ i, (![U j, V j] i) ^ d i) (fun d _ hd => by simp [notMem_support_iff.1 hd])]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [hmon, hc, Fin.prod_univ_two, mul_comm]
  -- multilinear expansion of the determinant
  have hdet : M.det = ∑ r ∈ Fintype.piFinset (fun _ : J => Λ),
      (∏ j, mon j (r j)) • (Matrix.of fun j => c j (r j)).det := by
    have e1 : M = Matrix.of fun j => ∑ d ∈ Λ, mon j d • c j d := by
      ext j e; rw [hrow j]; rfl
    conv_lhs => rw [e1]
    have := (Matrix.detRowAlternating (n := J) (R := R)).toMultilinearMap.map_sum_finset
      (fun j d => mon j d • c j d) (fun _ => Λ)
    change Matrix.detRowAlternating (fun j => ∑ d ∈ Λ, mon j d • c j d) = _
    change (Matrix.detRowAlternating (n := J) (R := R)).toMultilinearMap
      (fun j => ∑ d ∈ Λ, mon j d • c j d) = _
    rw [this]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h2 := (Matrix.detRowAlternating (n := J) (R := R)).toMultilinearMap.map_smul_univ
      (fun j => mon j (r j)) (fun j => c j (r j))
    rw [h2]
    rfl
  rw [hdet]
  refine Finset.dvd_sum fun r _ => ?_
  by_cases hinj : ∃ j j', j ≠ j' ∧ cls j = cls j' ∧ r j = r j'
  · obtain ⟨j, j', hne, hcl, hr⟩ := hinj
    have : (Matrix.of fun j => c j (r j)).det = 0 := by
      refine Matrix.det_zero_of_row_eq hne ?_
      funext e
      show (Q (cls j) e).coeff (r j) = (Q (cls j') e).coeff (r j'); rw [hcl, hr]
    rw [this, smul_zero]
    exact dvd_zero _
  · push Not at hinj
    -- total degree of the assignment
    have hsum : ∑ ξ, Vs (univ.filter fun j => cls j = ξ).card ≤ ∑ j, (r j 0 + r j 1) := by
      have h3 : ∑ j, (r j 0 + r j 1) =
          ∑ ξ, ∑ j ∈ univ.filter (fun j => cls j = ξ), (r j 0 + r j 1) := by
        rw [Finset.sum_fiberwise]
      rw [h3]
      refine Finset.sum_le_sum fun ξ _ => ?_
      refine Vs_le_sum_deg _ (fun j => (r j 0, r j 1)) ?_
      intro j hj j' hj' he
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hj hj'
      by_contra hne
      refine hinj j j' hne (hj.trans hj'.symm) ?_
      ext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    have hp : ϖ ^ (∑ j, (r j 0 + r j 1)) ∣ ∏ j, mon j (r j) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_dvd_prod_of_dvd _ _ fun j _ => ?_
      rw [pow_add]
      exact mul_dvd_mul (pow_dvd_pow_of_dvd (hU j) _) (pow_dvd_pow_of_dvd (hV j) _)
    exact Dvd.dvd.trans (pow_dvd_pow _ hsum) (hp.trans (by
      rw [smul_eq_mul]; exact dvd_mul_right _ _))


end B

end OVNS.Quant.Surf
