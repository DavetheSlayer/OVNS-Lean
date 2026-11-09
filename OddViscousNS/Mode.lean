import OddViscousNS.Defs

/-! # Elementary facts on the lattice and on the Hilbert structure of coefficient spaces -/

noncomputable section
namespace OVNS

lemma absSq_nonneg (k : Mode) : 0 ≤ absSq k := by
  unfold absSq
  positivity

lemma absk_nonneg (k : Mode) : 0 ≤ absk k := Real.sqrt_nonneg _

lemma absk_sq (k : Mode) : absk k ^ 2 = absSq k := Real.sq_sqrt (absSq_nonneg k)

/-- The squared length vanishes only at the origin. -/
private lemma absSq_eq_zero {k : Mode} : absSq k = 0 ↔ k = 0 := by
  unfold absSq
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg _]
  constructor
  · intro h
    funext i
    have hi := h i (Finset.mem_univ i)
    simpa using hi
  · rintro rfl i _
    simp

lemma absk_eq_zero {k : Mode} : absk k = 0 ↔ k = 0 := by
  unfold absk
  rw [Real.sqrt_eq_zero (absSq_nonneg k), absSq_eq_zero]

lemma one_le_absSq {k : Mode} (hk : k ≠ 0) : 1 ≤ absSq k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    exact hk (funext fun i ↦ by_contra fun hi ↦ h ⟨i, hi⟩)
  have h1 : (1 : ℤ) ≤ k i ^ 2 := by
    have := sq_nonneg (k i)
    have h0 : k i ^ 2 ≠ 0 := pow_ne_zero 2 hi
    omega
  have h2 : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by exact_mod_cast h1
  calc (1 : ℝ) ≤ (k i : ℝ) ^ 2 := h2
    _ ≤ absSq k := Finset.single_le_sum (f := fun j ↦ (k j : ℝ) ^ 2)
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)

lemma one_le_absk {k : Mode} (hk : k ≠ 0) : 1 ≤ absk k := by
  unfold absk
  exact Real.one_le_sqrt.mpr (one_le_absSq hk)

lemma absSq_neg (k : Mode) : absSq (-k) = absSq k := by
  simp [absSq]

lemma absk_neg (k : Mode) : absk (-k) = absk k := by
  unfold absk
  rw [absSq_neg]

/-- Embedding of the lattice in Euclidean space. -/
private def embed (k : Mode) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 fun i ↦ (k i : ℝ)

private lemma norm_embed (k : Mode) : ‖embed k‖ = absk k := by
  rw [EuclideanSpace.norm_eq]
  simp [absk, absSq, embed]

private lemma embed_add (p q : Mode) : embed (p + q) = embed p + embed q := by
  ext i
  simp [embed]

lemma absk_add_le (p q : Mode) : absk (p + q) ≤ absk p + absk q := by
  simp only [← norm_embed, embed_add]
  exact norm_add_le _ _

lemma absk_sub_le (p q : Mode) : absk (p - q) ≤ absk p + absk q := by
  rw [sub_eq_add_neg, ← absk_neg q]
  exact absk_add_le p (-q)

/-- Each coordinate is bounded by the length. -/
lemma abs_coord_le_absk (k : Mode) (i : Fin 3) : |(k i : ℝ)| ≤ absk k := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt <| Finset.single_le_sum (f := fun j ↦ (k j : ℝ) ^ 2)
    (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)

/-- `|v·k| ≤ ‖v‖ |k|`. -/
lemma norm_dotM_le (v : V3) (k : Mode) : ‖dotM v k‖ ≤ ‖v‖ * absk k := by
  calc ‖dotM v k‖ ≤ ∑ i, ‖v i‖ * |(k i : ℝ)| := by
        unfold dotM
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [norm_mul, Complex.norm_intCast]
    _ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) * Real.sqrt (∑ i, |(k i : ℝ)| ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖v‖ * absk k := by
        rw [EuclideanSpace.norm_eq]
        simp [absk, absSq]

/-- Finiteness of balls, with the crude cube count. -/
lemma finite_ball (R : ℝ) : {k : Mode | absk k ≤ R}.Finite := by
  refine (Set.finite_Icc (fun _ ↦ -⌈R⌉) (fun _ ↦ ⌈R⌉) :
    (Set.Icc _ _ : Set Mode).Finite).subset ?_
  intro k hk
  have hk' : absk k ≤ R := hk
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;>
  · have h := (abs_coord_le_absk k i).trans (hk'.trans (Int.le_ceil R))
    have h' : |k i| ≤ ⌈R⌉ := by exact_mod_cast h
    have := abs_le.mp h'
    first
      | exact this.1
      | exact this.2

lemma card_ball_le (N : ℕ) : (finite_ball N).toFinset.card ≤ (2 * N + 1) ^ 3 := by
  have hsub : (finite_ball N).toFinset ⊆
      Finset.Icc (fun _ ↦ -(N : ℤ)) (fun _ ↦ (N : ℤ)) := by
    intro k hk
    have hk' : absk k ≤ N := by simpa using hk
    rw [Finset.mem_Icc]
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;>
    · have h := (abs_coord_le_absk k i).trans hk'
      have h' : |k i| ≤ (N : ℤ) := by exact_mod_cast h
      have := abs_le.mp h'
      first
        | exact this.1
        | exact this.2
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Pi.card_Icc]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- `sobWeight` monotonicity: on the lattice `|k|^{2s} ≤ |k|^{2s'}` for `s ≤ s'`. -/
lemma sobWeight_mono {s s' : ℝ} (h : s ≤ s') (k : Mode) : sobWeight s k ≤ sobWeight s' k := by
  unfold sobWeight
  split_ifs with hk
  · exact le_rfl
  · exact Real.rpow_le_rpow_of_exponent_le (one_le_absk hk) (by linarith)

lemma sobWeight_nonneg (s : ℝ) (k : Mode) : 0 ≤ sobWeight s k := by
  unfold sobWeight
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (absk_nonneg k) _

lemma sobWeight_neg (s : ℝ) (k : Mode) : sobWeight s (-k) = sobWeight s k := by
  simp [sobWeight, absk_neg]

/-- `|k|² ` is integer valued. -/
lemma absSq_eq_int (k : Mode) : ∃ n : ℤ, absSq k = n :=
  ⟨∑ i, k i ^ 2, by simp [absSq]⟩

end OVNS
