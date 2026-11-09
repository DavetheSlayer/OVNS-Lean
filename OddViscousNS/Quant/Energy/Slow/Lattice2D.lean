import OddViscousNS.Mode

/-!
# T1: the 2D lattice sum on the slow modes (slow-cap route E7-F)

`S(λ) := ∑_{k ∈ ℤ²∖{0}} (λ + |k|²)⁻²`, realized on the slow modes `k₃ = 0` of `Mode = ℤ³`
(`slowResW`).  The route report `OddViscousNS_data/reports/t12_slow_fourier_route.md` §2.1 (T1)
asks for `S(λ) ≤ (127/3)/λ`, the manuscript's disc-plus-dyadic-shells count (`forced.tex`,
Lemma fg:lem:lady).  We prove the sharper

  `S(λ) ≤ 25/(4λ + 1)`  for every `λ ≥ 0`

by summing over the square shells `max(|k₁|, |k₂|) = n` (exactly `8n` points, each term
`≤ (λ + n²)⁻²` since `|k|² ≥ n²`) and telescoping

  `8n/(λ + n²)² ≤ (25/16) [4/(λ + (n − ½)²) − 4/(λ + (n + ½)²)]`,

which is the polynomial inequality `16 (λ + (n−½)²)(λ + (n+½)²) ≤ 25 (λ + n²)²` for `λ ≥ 0`,
`n ≥ 1`.  Numerically `λ S(λ) → π` as `λ → ∞`, so the constant `25/4` is within a factor `2`
of optimal; the report's `127/3` follows a fortiori (`slow_lattice_sum_le_report`).
-/

noncomputable section
namespace OVNS

open Classical in
/-- The 2D resolvent weight `(λ + |k|²)⁻¹` on the nonzero slow modes `k₃ = 0`, zero elsewhere. -/
def slowResW (t : ℝ) (k : Mode) : ℝ := if k 2 = 0 ∧ k ≠ 0 then (t + absSq k)⁻¹ else 0

variable {t : ℝ} {k : Mode}

lemma slowResW_of_slow (hk2 : k 2 = 0) (hk : k ≠ 0) : slowResW t k = (t + absSq k)⁻¹ := by
  simp [slowResW, hk2, hk]

lemma slowResW_of_fast (hk2 : k 2 ≠ 0) : slowResW t k = 0 := by
  simp [slowResW, hk2]

lemma slowResW_zero (t : ℝ) : slowResW t 0 = 0 := by
  simp [slowResW]

lemma slowResW_nonneg (ht : 0 ≤ t) (k : Mode) : 0 ≤ slowResW t k := by
  unfold slowResW
  split_ifs
  · exact inv_nonneg.2 (add_nonneg ht (absSq_nonneg k))
  · exact le_rfl

/-- `r_λ(k) (λ + |k|²) = 1` on the nonzero slow modes. -/
lemma slowResW_mul_cancel (ht : 0 ≤ t) (hk2 : k 2 = 0) (hk : k ≠ 0) :
    slowResW t k * (t + absSq k) = 1 := by
  rw [slowResW_of_slow hk2 hk]
  have h := one_le_absSq hk
  exact inv_mul_cancel₀ (by linarith)

/-- `√(r_λ(k)) √(λ + |k|²) = 1` on the nonzero slow modes. -/
lemma sqrt_slowResW_mul (ht : 0 ≤ t) (hk2 : k 2 = 0) (hk : k ≠ 0) :
    Real.sqrt (slowResW t k) * Real.sqrt (t + absSq k) = 1 := by
  rw [← Real.sqrt_mul (slowResW_nonneg ht k), slowResW_mul_cancel ht hk2 hk, Real.sqrt_one]

/-! ### Square shells -/

/-- The slow square `{k₃ = 0, |k₁| ≤ n, |k₂| ≤ n}`. -/
def slowBox (n : ℕ) : Finset Mode :=
  Finset.Icc (fun i => if i = 2 then 0 else -(n : ℤ)) (fun i => if i = 2 then 0 else (n : ℤ))

lemma mem_slowBox {n : ℕ} : k ∈ slowBox n ↔ k 2 = 0 ∧ |k 0| ≤ n ∧ |k 1| ≤ n := by
  simp only [slowBox, Finset.mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩
    have a0 := h1 0
    have b0 := h2 0
    have a1 := h1 1
    have b1 := h2 1
    have a2 := h1 2
    have b2 := h2 2
    simp only [Fin.isValue, Fin.reduceEq, ite_false, ite_true] at a0 b0 a1 b1 a2 b2
    exact ⟨le_antisymm b2 a2, abs_le.2 ⟨a0, b0⟩, abs_le.2 ⟨a1, b1⟩⟩
  · rintro ⟨h2, h0, h1⟩
    obtain ⟨h0a, h0b⟩ := abs_le.1 h0
    obtain ⟨h1a, h1b⟩ := abs_le.1 h1
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp [h2] <;> assumption

lemma slowBox_mono {m n : ℕ} (h : m ≤ n) : slowBox m ⊆ slowBox n := by
  intro k hk
  rw [mem_slowBox] at hk ⊢
  have h' : (m : ℤ) ≤ n := by exact_mod_cast h
  exact ⟨hk.1, hk.2.1.trans h', hk.2.2.trans h'⟩

lemma card_slowBox (n : ℕ) : (slowBox n).card = (2 * n + 1) ^ 2 := by
  rw [slowBox, Pi.card_Icc, Fin.prod_univ_three]
  simp only [Fin.isValue, Fin.reduceEq, ite_false, ite_true, Int.card_Icc]
  have h : ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by omega
  have h0 : ((0 : ℤ) + 1 - 0).toNat = 1 := by norm_num
  rw [h, h0]
  ring

/-- The shell `slowBox (n+1) \ slowBox n` has `8(n+1)` points. -/
lemma card_shell (n : ℕ) : (slowBox (n + 1) \ slowBox n).card = 8 * (n + 1) := by
  rw [Finset.card_sdiff_of_subset (slowBox_mono (Nat.le_succ n)), card_slowBox, card_slowBox]
  have h : (2 * n + 1) ^ 2 ≤ (2 * (n + 1) + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  zify [h]
  ring

/-- On the shell, `|k|² ≥ (n+1)²` and `k` is a nonzero slow mode. -/
lemma shell_spec {n : ℕ} (hk : k ∈ slowBox (n + 1) \ slowBox n) :
    k 2 = 0 ∧ k ≠ 0 ∧ ((n : ℝ) + 1) ^ 2 ≤ absSq k := by
  rw [Finset.mem_sdiff, mem_slowBox, mem_slowBox] at hk
  obtain ⟨⟨h2, -, -⟩, hn⟩ := hk
  have hor : (n : ℤ) + 1 ≤ |k 0| ∨ (n : ℤ) + 1 ≤ |k 1| := by
    by_cases h0 : (n : ℤ) + 1 ≤ |k 0|
    · exact Or.inl h0
    · refine Or.inr ?_
      by_contra h1
      exact hn ⟨h2, by omega, by omega⟩
  have hsq : ∀ i : Fin 3, (k i : ℝ) ^ 2 ≤ absSq k := fun i =>
    Finset.single_le_sum (f := fun j => (k j : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have key : ∀ i : Fin 3, (n : ℤ) + 1 ≤ |k i| → ((n : ℝ) + 1) ^ 2 ≤ absSq k := by
    intro i hi
    have h1 : ((n : ℝ) + 1) ≤ |(k i : ℝ)| := by
      have : (((n : ℤ) + 1 : ℤ) : ℝ) ≤ ((|k i| : ℤ) : ℝ) := by exact_mod_cast hi
      simpa using this
    have h2' : ((n : ℝ) + 1) ^ 2 ≤ |(k i : ℝ)| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [sq_abs] at h2'
    exact h2'.trans (hsq i)
  have hne : k ≠ 0 := by
    rintro rfl
    rcases hor with h | h <;> simp at h <;> omega
  rcases hor with h | h
  · exact ⟨h2, hne, key 0 h⟩
  · exact ⟨h2, hne, key 1 h⟩

/-- Every term of the shell is at most `(λ + (n+1)²)⁻²`. -/
lemma shell_term_le (ht : 0 ≤ t) {n : ℕ} (hk : k ∈ slowBox (n + 1) \ slowBox n) :
    slowResW t k ^ 2 ≤ ((t + ((n : ℝ) + 1) ^ 2) ^ 2)⁻¹ := by
  obtain ⟨h2, hne, hsq⟩ := shell_spec hk
  rw [slowResW_of_slow h2 hne, inv_pow]
  have hpos : 0 < t + ((n : ℝ) + 1) ^ 2 := by positivity
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le (by linarith) 2)

/-! ### The telescoping bound -/

/-- `16 (λ + (m−½)²)(λ + (m+½)²) ≤ 25 (λ + m²)²` for `λ ≥ 0`, `m ≥ 1`. -/
lemma shell_poly (ht : 0 ≤ t) {m : ℝ} (hm : 1 ≤ m) :
    16 * ((t + (m - 1 / 2) ^ 2) * (t + (m + 1 / 2) ^ 2)) ≤ 25 * (t + m ^ 2) ^ 2 := by
  have hu : 1 ≤ t + m ^ 2 := by nlinarith
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 9 * (t + m ^ 2) + 1)
    (by linarith : 0 ≤ t + m ^ 2 - 1), sq_nonneg m]

/-- The shell term telescopes: `8m/(λ+m²)² ≤ (25/4)/(λ+(m−½)²) − (25/4)/(λ+(m+½)²)`. -/
lemma shell_telescope (ht : 0 ≤ t) {m : ℝ} (hm : 1 ≤ m) :
    8 * m * ((t + m ^ 2) ^ 2)⁻¹ ≤
      25 / 4 / (t + (m - 1 / 2) ^ 2) - 25 / 4 / (t + (m + 1 / 2) ^ 2) := by
  have hA : 0 < t + (m - 1 / 2) ^ 2 := by nlinarith
  have hB : 0 < t + (m + 1 / 2) ^ 2 := by nlinarith
  have hU : 0 < (t + m ^ 2) ^ 2 := by positivity
  have hP := shell_poly ht hm
  rw [div_sub_div _ _ hA.ne' hB.ne', ← div_eq_mul_inv, div_le_div_iff₀ hU (mul_pos hA hB)]
  nlinarith [mul_le_mul_of_nonneg_left hP (by linarith : (0 : ℝ) ≤ m)]

/-- Partial sums over the slow squares: `∑_{slowBox n} r_λ² ≤ 25/(4λ+1) − (25/4)/(λ+(n+½)²)`. -/
lemma sum_slowBox_le (ht : 0 ≤ t) (n : ℕ) :
    ∑ k ∈ slowBox n, slowResW t k ^ 2 ≤
      25 / (4 * t + 1) - 25 / 4 / (t + ((n : ℝ) + 1 / 2) ^ 2) := by
  induction n with
  | zero =>
    have h0 : ∑ k ∈ slowBox 0, slowResW t k ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [mem_slowBox] at hk
      have hk0 : k = 0 := by
        funext i
        fin_cases i
        · simpa using abs_nonpos_iff.1 (by simpa using hk.2.1)
        · simpa using abs_nonpos_iff.1 (by simpa using hk.2.2)
        · simpa using hk.1
      simp [hk0, slowResW_zero]
    rw [h0]
    have h1 : (0 : ℝ) < 4 * t + 1 := by linarith
    have e : (25 : ℝ) / 4 / (t + ((0 : ℕ) + 1 / 2 : ℝ) ^ 2) = 25 / (4 * t + 1) := by
      field_simp
      ring
    rw [e, sub_self]
  | succ n ih =>
    rw [← Finset.sum_sdiff (slowBox_mono (Nat.le_succ n))]
    have hsh : ∑ k ∈ slowBox (n + 1) \ slowBox n, slowResW t k ^ 2 ≤
        8 * ((n : ℝ) + 1) * ((t + ((n : ℝ) + 1) ^ 2) ^ 2)⁻¹ := by
      have h := Finset.sum_le_card_nsmul (slowBox (n + 1) \ slowBox n) (fun k => slowResW t k ^ 2)
        (((t + ((n : ℝ) + 1) ^ 2) ^ 2)⁻¹) (fun k hk => shell_term_le ht hk)
      rw [card_shell, nsmul_eq_mul] at h
      refine h.trans (le_of_eq ?_)
      push_cast
      ring
    have htel := shell_telescope ht (m := (n : ℝ) + 1)
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have e1 : (n : ℝ) + 1 - 1 / 2 = (n : ℝ) + 1 / 2 := by ring
    have e2 : (n : ℝ) + 1 + 1 / 2 = ((n + 1 : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
    rw [e1, e2] at htel
    linarith

/-- **T1.** The 2D lattice sum `S(λ) = ∑_{k∈ℤ²∖0} (λ + |k|²)⁻²` on the slow modes converges and
`S(λ) ≤ 25/(4λ + 1)` for every `λ ≥ 0`. -/
theorem slow_lattice_sum_le (ht : 0 ≤ t) :
    Summable (fun k => slowResW t k ^ 2) ∧ ∑' k, slowResW t k ^ 2 ≤ 25 / (4 * t + 1) := by
  have h0 : 0 ≤ fun k => slowResW t k ^ 2 := fun k => sq_nonneg _
  have key : ∀ s : Finset Mode, ∑ k ∈ s, slowResW t k ^ 2 ≤ 25 / (4 * t + 1) := by
    intro s
    obtain ⟨M, hM⟩ := (s.image fun k : Mode => |k 0| ⊔ |k 1|).exists_le
    set n : ℕ := M.toNat with hn
    have hsub : s.filter (fun k : Mode => k 2 = 0) ⊆ slowBox n := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have h := hM _ (Finset.mem_image_of_mem (fun k : Mode => |k 0| ⊔ |k 1|) hk.1)
      have hMn : M ≤ (n : ℤ) := Int.self_le_toNat M
      rw [mem_slowBox]
      exact ⟨hk.2, (le_sup_left.trans h).trans hMn, (le_sup_right.trans h).trans hMn⟩
    have hfilt : ∑ k ∈ s.filter (fun k : Mode => k 2 = 0), slowResW t k ^ 2 =
        ∑ k ∈ s, slowResW t k ^ 2 := by
      refine Finset.sum_filter_of_ne fun k _ hk => ?_
      by_contra h2
      exact hk (by rw [slowResW_of_fast h2]; ring)
    rw [← hfilt]
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => sq_nonneg _).trans ?_
    refine (sum_slowBox_le ht n).trans ?_
    have : 0 ≤ 25 / 4 / (t + ((n : ℝ) + 1 / 2) ^ 2) := by positivity
    linarith
  exact ⟨summable_of_sum_le h0 key, Real.tsum_le_of_sum_le h0 key⟩

lemma summable_slowResW_sq (ht : 0 ≤ t) : Summable (fun k => slowResW t k ^ 2) :=
  (slow_lattice_sum_le ht).1

/-- `S(λ) ≤ (25/4)/λ` for `λ > 0`. -/
theorem slow_lattice_sum_le_div (ht : 0 < t) : ∑' k, slowResW t k ^ 2 ≤ 25 / 4 / t := by
  refine (slow_lattice_sum_le ht.le).2.trans ?_
  rw [div_le_div_iff₀ (by linarith) ht]
  nlinarith

/-- The constant of the route report (`forced.tex` Lemma fg:lem:lady): `S(λ) ≤ (127/3)/λ`. -/
theorem slow_lattice_sum_le_report (ht : 0 < t) : ∑' k, slowResW t k ^ 2 ≤ 127 / 3 / t := by
  refine (slow_lattice_sum_le_div ht).trans ?_
  exact div_le_div_of_nonneg_right (by norm_num) ht.le

/-- Translation invariance of the lattice sum. -/
lemma tsum_slowResW_sub (t : ℝ) (k : Mode) :
    ∑' p, slowResW t (k - p) ^ 2 = ∑' p, slowResW t p ^ 2 :=
  (Equiv.subLeft k).tsum_eq fun p => slowResW t p ^ 2

end OVNS
