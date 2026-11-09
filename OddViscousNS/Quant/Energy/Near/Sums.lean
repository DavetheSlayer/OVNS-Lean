import OddViscousNS.Quant.Energy.Near.Defs

/-!
# E9: elementary summation lemmas for the near moments

Two real-analysis inputs of the Lorentzian-layer summation (route report §2.1 step 3, §2.2):

* **Layer cake / rearrangement** (`sum_inv_le_of_card_le`): if a finite family has counting
  function `#{s : d(s) ≤ t} ≤ L t` (`t ≥ 1`) and `1 ≤ d ≤ D`, then
  `Σ_s 1/d(s) ≤ L Σ_{t=1}^{D} 1/t ≤ L (1 + log D)` (Abel summation against the linear sublevel
  count; `harmonic_le_one_add_log`).  This replaces the report's dyadic `d`-layers.
* **The lattice sum** `Σ_{0 < ‖p‖_∞ ≤ R} |p|^{−2} ≤ 26 R` (`lattice_sum_le`; Body 18:
  "`Σ_{0<|p|≤K} |p|^{−2} ≤ 26K`"): the sup-norm shell `‖p‖_∞ = n` has `(2n+1)³ − (2n−1)³ = 24n² + 2`
  points, each with `|p|² ≥ n²`.
-/

noncomputable section

namespace OVNS.Quant

open Finset

/-! ### Harmonic sums -/

theorem sum_Icc_inv_eq_harmonic (D : ℕ) :
    ∑ t ∈ Finset.Icc 1 D, ((t : ℝ))⁻¹ = (harmonic D : ℝ) := by
  induction D with
  | zero => simp [harmonic]
  | succ D ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
    push_cast
    ring

/-- `Σ_{t=1}^{D} 1/t ≤ 1 + log D`. -/
theorem sum_Icc_inv_le_log (D : ℕ) : ∑ t ∈ Finset.Icc 1 D, ((t : ℝ))⁻¹ ≤ 1 + Real.log D := by
  rw [sum_Icc_inv_eq_harmonic]
  exact harmonic_le_one_add_log D

/-- Telescoping: `Σ_{t=a}^{D} (1/t − 1/(t+1)) = 1/a − 1/(D+1)` for `1 ≤ a ≤ D + 1`. -/
theorem sum_Icc_inv_sub_inv_succ (a D : ℕ) (ha : 1 ≤ a) (haD : a ≤ D + 1) :
    ∑ t ∈ Finset.Icc a D, (((t : ℝ))⁻¹ - ((t : ℝ) + 1)⁻¹) = ((a : ℝ))⁻¹ - ((D : ℝ) + 1)⁻¹ := by
  induction D with
  | zero =>
    obtain rfl : a = 1 := by omega
    simp
  | succ D ih =>
    rcases Nat.lt_or_ge a (D + 2) with h | h
    · rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
      push_cast
      ring
    · obtain rfl : a = D + 2 := by omega
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      push_cast
      ring

/-- The algebraic identity behind the Abel summation:
`Σ_{t=1}^{D} (1/t − 1/(t+1)) t + D/(D+1) = Σ_{t=1}^{D} 1/t`. -/
theorem sum_Icc_abel_identity (D : ℕ) :
    ∑ t ∈ Finset.Icc 1 D, (((t : ℝ))⁻¹ - ((t : ℝ) + 1)⁻¹) * t + (D : ℝ) * ((D : ℝ) + 1)⁻¹ =
      ∑ t ∈ Finset.Icc 1 D, ((t : ℝ))⁻¹ := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ← ih]
    push_cast
    have h1 : ((D : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((D : ℝ) + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- **Layer cake (rearrangement) against a linear count.**  If `1 ≤ d s ≤ D` on `S` and
`#{s ∈ S : d s ≤ t} ≤ L t` for every `t ≥ 1`, then `Σ_{s ∈ S} 1/d(s) ≤ L Σ_{t=1}^{D} 1/t`
(route report §2.1 step 3: "layer-cake in `d` against the linear sublevel count"). -/
theorem sum_inv_le_of_card_le {α : Type*} (S : Finset α) (d : α → ℕ) (D : ℕ) (L : ℝ)
    (hd : ∀ s ∈ S, 1 ≤ d s ∧ d s ≤ D)
    (hcount : ∀ t : ℕ, 1 ≤ t → ((S.filter fun s => d s ≤ t).card : ℝ) ≤ L * t) :
    ∑ s ∈ S, ((d s : ℕ) : ℝ)⁻¹ ≤ L * ∑ t ∈ Finset.Icc 1 D, ((t : ℝ))⁻¹ := by
  classical
  rcases Nat.eq_zero_or_pos D with hD | hD
  · have hS : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro s hs
      have := hd s hs
      omega
    subst hD
    simp [hS]
  set g : ℕ → ℝ := fun t => ((t : ℝ))⁻¹ - ((t : ℝ) + 1)⁻¹ with hg
  have hg0 : ∀ t : ℕ, 1 ≤ t → 0 ≤ g t := by
    intro t ht
    have : (0 : ℝ) < t := by exact_mod_cast ht
    simp only [hg]
    rw [sub_nonneg]
    exact inv_anti₀ this (by linarith)
  -- Step A: `1/d(s) = Σ_{t ∈ Icc 1 D} [d s ≤ t] g t + 1/(D+1)`.
  have hA : ∀ s ∈ S, ((d s : ℕ) : ℝ)⁻¹ =
      ∑ t ∈ Finset.Icc 1 D, (if d s ≤ t then g t else 0) + ((D : ℝ) + 1)⁻¹ := by
    intro s hs
    obtain ⟨h1, h2⟩ := hd s hs
    rw [← Finset.sum_filter]
    have e : (Finset.Icc 1 D).filter (fun t => d s ≤ t) = Finset.Icc (d s) D := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [e, sum_Icc_inv_sub_inv_succ (d s) D h1 (by omega)]
    ring
  -- Step B: sum over `s` and swap.
  have hB : ∑ s ∈ S, ((d s : ℕ) : ℝ)⁻¹ =
      ∑ t ∈ Finset.Icc 1 D, g t * ((S.filter fun s => d s ≤ t).card : ℝ) +
        (S.card : ℝ) * ((D : ℝ) + 1)⁻¹ := by
    rw [Finset.sum_congr rfl hA, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Step C: bound the counting function.
  have hSD : (S.card : ℝ) ≤ L * D := by
    have : S.filter (fun s => d s ≤ D) = S := by
      rw [Finset.filter_eq_self]
      exact fun s hs => (hd s hs).2
    have h := hcount D hD
    rwa [this] at h
  rw [hB]
  calc ∑ t ∈ Finset.Icc 1 D, g t * ((S.filter fun s => d s ≤ t).card : ℝ) +
        (S.card : ℝ) * ((D : ℝ) + 1)⁻¹
      ≤ ∑ t ∈ Finset.Icc 1 D, g t * (L * t) + (L * D) * ((D : ℝ) + 1)⁻¹ := by
        gcongr with t ht
        · exact hg0 t (Finset.mem_Icc.1 ht).1
        · exact hcount t (Finset.mem_Icc.1 ht).1
    _ = L * (∑ t ∈ Finset.Icc 1 D, g t * t + (D : ℝ) * ((D : ℝ) + 1)⁻¹) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun t _ => by ring
        · ring
    _ = L * ∑ t ∈ Finset.Icc 1 D, ((t : ℝ))⁻¹ := by rw [sum_Icc_abel_identity]

/-! ### The sup-norm shells of the lattice -/

/-- The sup norm `‖p‖_∞ = max_i |p_i|`. -/
def supNorm (p : Mode) : ℕ := Finset.univ.sup fun i => (p i).natAbs

theorem mem_modeBox_iff_supNorm_le {R : ℕ} {p : Mode} : p ∈ modeBox R ↔ supNorm p ≤ R := by
  rw [mem_modeBox, supNorm, Finset.sup_le_iff]
  constructor
  · intro h i _
    have := h i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  · intro h i
    have := h i (Finset.mem_univ i)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this

theorem one_le_supNorm {p : Mode} (hp : p ≠ 0) : 1 ≤ supNorm p := by
  by_contra h
  apply hp
  funext i
  have h1 : (p i).natAbs ≤ supNorm p := Finset.le_sup (f := fun i => (p i).natAbs) (mem_univ i)
  have h2 : (p i).natAbs = 0 := by omega
  simpa using h2

/-- `‖p‖_∞² ≤ |p|²`. -/
theorem sq_supNorm_le_absSq (p : Mode) : ((supNorm p : ℕ) : ℝ) ^ 2 ≤ absSq p := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3)) univ_nonempty
      (fun i => (p i).natAbs)
  rw [supNorm, hi]
  have e : (((p i).natAbs : ℕ) : ℝ) ^ 2 = ((p i : ℤ) : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [e]
  exact Finset.single_le_sum (f := fun j => ((p j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- The shell `‖p‖_∞ = n` (`n ≥ 1`) has at most `24n² + 2 = (2n+1)³ − (2n−1)³` points. -/
theorem card_shell_le {R n : ℕ} (hn : 1 ≤ n) :
    ((modeBox R).filter fun p => supNorm p = n).card ≤ 24 * n ^ 2 + 2 := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsub : ((modeBox R).filter fun p => supNorm p = m + 1) ∪ modeBox m ⊆ modeBox (m + 1) := by
    intro p hp
    simp only [Finset.mem_union, Finset.mem_filter, mem_modeBox_iff_supNorm_le] at hp
    rw [mem_modeBox_iff_supNorm_le]
    rcases hp with ⟨-, h⟩ | h <;> omega
  have hdisj : Disjoint ((modeBox R).filter fun p => supNorm p = m + 1) (modeBox m) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_filter] at hp
    rw [mem_modeBox_iff_supNorm_le] at hp'
    omega
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, card_modeBox, card_modeBox] at h1
  have h2 : (2 * (m + 1) + 1) ^ 3 = (2 * m + 1) ^ 3 + (24 * (m + 1) ^ 2 + 2) := by ring
  omega

/-- **The lattice sum** `Σ_{p ≠ 0, ‖p‖_∞ ≤ R} |p|^{−2} ≤ 26 R` (Body 18, `26K`). -/
theorem lattice_sum_le (R : ℕ) : ∑ p ∈ (modeBox R).erase 0, (absSq p)⁻¹ ≤ 26 * R := by
  classical
  have hmaps : ∀ p ∈ (modeBox R).erase 0, supNorm p ∈ Finset.Icc 1 R := by
    intro p hp
    rw [Finset.mem_erase, mem_modeBox_iff_supNorm_le] at hp
    exact Finset.mem_Icc.2 ⟨one_le_supNorm hp.1, hp.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hterm : ∀ n ∈ Finset.Icc 1 R,
      ∑ p ∈ ((modeBox R).erase 0).filter (fun p => supNorm p = n), (absSq p)⁻¹ ≤ 26 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hnR : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hcard : (((modeBox R).erase 0).filter (fun p => supNorm p = n)).card ≤ 24 * n ^ 2 + 2 := by
      refine le_trans (Finset.card_le_card ?_) (card_shell_le (R := R) hn1)
      intro p hp
      rw [Finset.mem_filter, Finset.mem_erase] at hp
      exact Finset.mem_filter.2 ⟨hp.1.2, hp.2⟩
    calc ∑ p ∈ ((modeBox R).erase 0).filter (fun p => supNorm p = n), (absSq p)⁻¹
        ≤ ∑ p ∈ ((modeBox R).erase 0).filter (fun p => supNorm p = n), (((n : ℝ)) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp' := (Finset.mem_filter.1 hp).2
          have := sq_supNorm_le_absSq p
          rw [hp'] at this
          exact inv_anti₀ hnR this
      _ = ((((modeBox R).erase 0).filter (fun p => supNorm p = n)).card : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((24 * n ^ 2 + 2 : ℕ) : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
          gcongr
      _ = 24 + 2 * ((n : ℝ) ^ 2)⁻¹ := by
          push_cast
          rw [add_mul, mul_assoc, mul_inv_cancel₀ hnR.ne', mul_one]
      _ ≤ 26 := by
          have : ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
            rw [inv_le_one_iff₀]
            right
            exact_mod_cast Nat.one_le_pow 2 n hn1
          linarith
  calc ∑ n ∈ Finset.Icc 1 R, ∑ p ∈ ((modeBox R).erase 0).filter (fun p => supNorm p = n),
        (absSq p)⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 R, (26 : ℝ) := Finset.sum_le_sum hterm
    _ = 26 * R := by simp [Finset.sum_const, Nat.card_Icc, mul_comm]

end OVNS.Quant

end
