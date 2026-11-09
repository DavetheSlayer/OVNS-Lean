import OddViscousNS.Sobolev

/-! # Lattice sums and Wiener-algebra bounds (`Lemma fg:lem:interp` and the constant `c₄`) -/

noncomputable section
namespace OVNS

/-- `c₄² = ∑_{k≠0} |k|⁻⁴`. -/
def c4 : ℝ := Real.sqrt (∑' k : Mode, if k = 0 then 0 else (absSq k)⁻¹ ^ 2)

/-! ### Dyadic counting -/

/-- The lattice ball `{|k| ≤ R}` as a finset. -/
private def ballF (R : ℝ) : Finset Mode := (finite_ball R).toFinset

private lemma mem_ballF {R : ℝ} {k : Mode} : k ∈ ballF R ↔ absk k ≤ R := by
  simp [ballF]

private lemma ballF_mono {r R : ℝ} (h : r ≤ R) : ballF r ⊆ ballF R := fun _ hk =>
  mem_ballF.2 ((mem_ballF.1 hk).trans h)

private lemma card_ballF_le {R : ℝ} (hR : 1 ≤ R) : ((ballF R).card : ℝ) ≤ 343 * R ^ 3 := by
  have h1 : ballF R ⊆ ballF (⌈R⌉₊ : ℝ) := ballF_mono (Nat.le_ceil R)
  have h2 : (ballF R).card ≤ (2 * ⌈R⌉₊ + 1) ^ 3 := (Finset.card_le_card h1).trans (card_ball_le _)
  have h3 : ((⌈R⌉₊ : ℕ) : ℝ) < R + 1 := Nat.ceil_lt_add_one (by linarith)
  have h4 : ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ≤ 7 * R := by
    push_cast
    linarith
  calc ((ballF R).card : ℝ) ≤ ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast h2
    _ ≤ (7 * R) ^ 3 := pow_le_pow_left₀ (by positivity) h4 3
    _ = 343 * R ^ 3 := by ring

/-- A shell `r < |k| ≤ 2r` has at most `2744 r³` points. -/
private lemma shell_sum_le (ψ : Mode → ℝ) {r B : ℝ} (hr : 1 ≤ r) (hB : 0 ≤ B)
    (hψ : ∀ k, r < absk k → ψ k ≤ B) :
    ∑ k ∈ ballF (2 * r) \ ballF r, ψ k ≤ 2744 * r ^ 3 * B := by
  have h1 : ∀ k ∈ ballF (2 * r) \ ballF r, ψ k ≤ B := fun k hk =>
    hψ k (not_le.1 fun h => (Finset.mem_sdiff.1 hk).2 (mem_ballF.2 h))
  have h2 := Finset.sum_le_card_nsmul _ _ _ h1
  have h3 : ((ballF (2 * r) \ ballF r).card : ℝ) ≤ 2744 * r ^ 3 := by
    have h4 := card_ballF_le (R := 2 * r) (by linarith)
    have h5 : ((ballF (2 * r) \ ballF r).card : ℝ) ≤ (ballF (2 * r)).card := by
      exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have e : 343 * (2 * r) ^ 3 = 2744 * r ^ 3 := by ring
    linarith
  rw [nsmul_eq_mul] at h2
  exact h2.trans (mul_le_mul_of_nonneg_right h3 hB)

private lemma inv_absSq_le {r : ℝ} {k : Mode} (hr : 0 < r) (h : r < absk k) :
    (absSq k)⁻¹ ≤ (r ^ 2)⁻¹ := by
  rw [← absk_sq]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hr.le h.le 2)

private lemma inv_absSq_sq_le {r : ℝ} {k : Mode} (hr : 0 < r) (h : r < absk k) :
    (absSq k)⁻¹ ^ 2 ≤ (r ^ 4)⁻¹ := by
  have h1 := pow_le_pow_left₀ (inv_nonneg.2 (absSq_nonneg k)) (inv_absSq_le hr h) 2
  have e : ((r ^ 2)⁻¹) ^ 2 = (r ^ 4)⁻¹ := by
    rw [inv_pow]
    ring_nf
  rwa [e] at h1

/-- Dyadic summation of the `|k|⁻⁴` tail, from radius `R` up to `2ⁿR`. -/
private lemma dyadic_tail {ψ : Mode → ℝ} (hψ : ∀ k, ψ k ≤ (absSq k)⁻¹ ^ 2) {R : ℝ} (hR : 1 ≤ R)
    (n : ℕ) :
    ∑ k ∈ ballF (2 ^ n * R), ψ k ≤ ∑ k ∈ ballF R, ψ k + 5488 / R * (1 - (1 / 2) ^ n) := by
  have hR0 : 0 < R := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hr1 : 1 ≤ (2 : ℝ) ^ n * R :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hR
    have hr0 : 0 < (2 : ℝ) ^ n * R := by linarith
    have e : (2 : ℝ) ^ (n + 1) * R = 2 * (2 ^ n * R) := by ring
    rw [e, ← Finset.sum_sdiff (ballF_mono (show 2 ^ n * R ≤ 2 * (2 ^ n * R) by linarith))]
    have hsh := shell_sum_le ψ hr1 (B := (((2 : ℝ) ^ n * R) ^ 4)⁻¹) (by positivity)
      (fun k hk => (hψ k).trans (inv_absSq_sq_le hr0 hk))
    have e2 : 2744 * ((2 : ℝ) ^ n * R) ^ 3 * (((2 : ℝ) ^ n * R) ^ 4)⁻¹
        = 2744 / R * (1 / 2) ^ n := by
      have : ((1 : ℝ) / 2) ^ n = ((2 : ℝ) ^ n)⁻¹ := by simp
      rw [this]
      field_simp
    have e3 : 5488 / R * (1 - ((1 : ℝ) / 2) ^ (n + 1))
        = 5488 / R * (1 - (1 / 2) ^ n) + 2744 / R * (1 / 2) ^ n := by
      rw [pow_succ]
      ring
    rw [e3]
    rw [e2] at hsh
    linarith

/-- Summability with the tail bound `∑_{|k|>R} |k|⁻⁴ ≤ 5488/R`. -/
private lemma summable_tail {ψ : Mode → ℝ} (h0 : ∀ k, 0 ≤ ψ k)
    (hψ : ∀ k, ψ k ≤ (absSq k)⁻¹ ^ 2) {R : ℝ} (hR : 1 ≤ R) :
    Summable ψ ∧ ∑' k, ψ k ≤ ∑ k ∈ ballF R, ψ k + 5488 / R := by
  have hR0 : 0 < R := by linarith
  have key : ∀ s : Finset Mode, ∑ k ∈ s, ψ k ≤ ∑ k ∈ ballF R, ψ k + 5488 / R := by
    intro s
    obtain ⟨M, hM⟩ := (s.image absk).exists_le
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (one_lt_two : (1 : ℝ) < 2)
    have hsub : s ⊆ ballF (2 ^ n * R) := fun k hk => mem_ballF.2 (by
      have h1 := hM _ (Finset.mem_image_of_mem absk hk)
      have h2 : (2 : ℝ) ^ n ≤ 2 ^ n * R := le_mul_of_one_le_right (by positivity) hR
      linarith)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => h0 k).trans ?_
    refine (dyadic_tail hψ hR n).trans ?_
    have h3 : (0 : ℝ) ≤ 5488 / R * (1 / 2) ^ n := by positivity
    have e : 5488 / R * (1 - ((1 : ℝ) / 2) ^ n) = 5488 / R - 5488 / R * (1 / 2) ^ n := by ring
    linarith
  exact ⟨summable_of_sum_le h0 key, Real.tsum_le_of_sum_le h0 key⟩

lemma summable_inv4 : Summable fun k : Mode => if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2 := by
  refine (summable_tail (R := 1) (fun k => ?_) (fun k => ?_) le_rfl).1
  · split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  · split_ifs
    · exact sq_nonneg _
    · exact le_rfl

lemma c4_pos : 0 < c4 := by
  have hk : (fun _ => 1 : Mode) ≠ 0 := fun h => by simpa using congrFun h 0
  refine Real.sqrt_pos.2 (summable_inv4.tsum_pos (fun k => ?_) (fun _ => 1) ?_)
  · split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  · rw [ite_eq_right hk]
    have := one_le_absSq hk
    positivity

/-- The weight `|k|⁻²`, zero at `k = 0`. -/
private def w4 (k : Mode) : ℝ := if k = 0 then 0 else (absSq k)⁻¹

private lemma w4_nonneg (k : Mode) : 0 ≤ w4 k := by
  unfold w4
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.2 (absSq_nonneg k)

private lemma w4_le (k : Mode) : w4 k ≤ (absSq k)⁻¹ := by
  unfold w4
  split_ifs
  · exact inv_nonneg.2 (absSq_nonneg k)
  · exact le_rfl

private lemma w4_sq (k : Mode) : w4 k ^ 2 = if k = 0 then 0 else (absSq k)⁻¹ ^ 2 := by
  unfold w4
  split_ifs <;> simp

/-- `∑_{0<|k|≤2ⁿ} |k|⁻² ≤ 2744·2ⁿ`. -/
private lemma low_dyadic (n : ℕ) : ∑ k ∈ ballF (2 ^ n), w4 k ≤ 2744 * 2 ^ n := by
  induction n with
  | zero =>
    have h1 : ∀ k ∈ ballF ((2 : ℝ) ^ 0), w4 k ≤ 1 := fun k _ => by
      by_cases hk : k = 0
      · simp [w4, hk]
      · simpa [w4, hk] using inv_le_one_of_one_le₀ (one_le_absSq hk)
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    have h3 := card_ballF_le (R := (2 : ℝ) ^ 0) (by simp)
    rw [nsmul_eq_mul] at h2
    norm_num at h2 h3 ⊢
    have h4 : ((ballF 1).card : ℝ) ≤ 343 := by exact_mod_cast h3
    linarith
  | succ n ih =>
    have hr1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    have hr0 : (0 : ℝ) < 2 ^ n := by positivity
    have e : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [e, ← Finset.sum_sdiff (ballF_mono (show (2 : ℝ) ^ n ≤ 2 * 2 ^ n by linarith))]
    have hsh := shell_sum_le w4 hr1 (B := (((2 : ℝ) ^ n) ^ 2)⁻¹) (by positivity)
      (fun k hk => (w4_le k).trans (inv_absSq_le hr0 hk))
    have e2 : 2744 * ((2 : ℝ) ^ n) ^ 3 * (((2 : ℝ) ^ n) ^ 2)⁻¹ = 2744 * 2 ^ n := by
      field_simp
    rw [e2] at hsh
    linarith

/-- `∑_{0<|k|≤R} |k|⁻² ≤ 5488 R`. -/
private lemma low_sum {R : ℝ} (hR : 1 ≤ R) : ∑ k ∈ ballF R, w4 k ≤ 5488 * R := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near hR (one_lt_two : (1 : ℝ) < 2)
  refine (Finset.sum_le_sum_of_subset_of_nonneg (ballF_mono h2.le)
    fun k _ _ => w4_nonneg k).trans ?_
  refine (low_dyadic (n + 1)).trans ?_
  rw [pow_succ]
  linarith

/-! ### Cauchy–Schwarz against the Sobolev norms -/

private lemma cs_tsum {f g : Mode → ℝ} (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k)
    (hf2 : Summable fun k => f k ^ 2) (hg2 : Summable fun k => g k ^ 2) :
    (Summable fun k => f k * g k) ∧
      ∑' k, f k * g k ≤ Real.sqrt (∑' k, f k ^ 2) * Real.sqrt (∑' k, g k ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have key := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg
    (by simpa using hf2) (by simpa using hg2)
  simpa [Real.sqrt_eq_rpow] using key

private lemma weighted_cs {s : ℝ} {f : Field} {w a : Mode → ℝ} (hf : InH s f)
    (hw : ∀ k, 0 ≤ w k) (hw2 : Summable fun k => w k ^ 2)
    (ha : ∀ k, a k = w k * (Real.sqrt (sobWeight s k) * ‖f k‖)) :
    Summable a ∧ ∑' k, a k ≤ Real.sqrt (∑' k, w k ^ 2) * hnorm s f := by
  have e : ∀ k, (Real.sqrt (sobWeight s k) * ‖f k‖) ^ 2 = sobWeight s k * ‖f k‖ ^ 2 := fun k => by
    rw [mul_pow, Real.sq_sqrt (sobWeight_nonneg s k)]
  have hf' : Summable fun k => (Real.sqrt (sobWeight s k) * ‖f k‖) ^ 2 := by
    simp only [e]
    exact hf
  obtain rfl : a = _ := funext ha
  have h := cs_tsum hw (fun k => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hw2 hf'
  simp only [e] at h
  exact h

private lemma sqrt_sob {s : ℝ} {n : ℕ} (hs : s = n) {k : Mode} (hk : k ≠ 0) :
    Real.sqrt (sobWeight s k) = absk k ^ n := by
  have h : (2 * s : ℝ) = ((2 * n : ℕ) : ℝ) := by
    push_cast
    rw [hs]
  rw [sobWeight, ite_eq_right hk, h, Real.rpow_natCast, pow_mul',
    Real.sqrt_sq (pow_nonneg (absk_nonneg k) n)]

private lemma w4_mul_ne (m : ℕ) {s : ℝ} (hs : s = ((m + 2 : ℕ) : ℝ)) (f : Field) {k : Mode}
    (hk : k ≠ 0) :
    absk k ^ m * ‖f k‖ = w4 k * (Real.sqrt (sobWeight s k) * ‖f k‖) := by
  have h : absSq k ≠ 0 := (zero_lt_one.trans_le (one_le_absSq hk)).ne'
  rw [w4, ite_eq_right hk, sqrt_sob hs hk, pow_add, absk_sq]
  field_simp

private lemma w4_mul (m : ℕ) {s : ℝ} (hs : s = ((m + 2 : ℕ) : ℝ)) {f : Field} (hf : f 0 = 0)
    (k : Mode) : absk k ^ m * ‖f k‖ = w4 k * (Real.sqrt (sobWeight s k) * ‖f k‖) := by
  by_cases hk : k = 0
  · subst hk
    simp [w4, hf]
  · exact w4_mul_ne m hs f hk

private lemma w4_cs {s : ℝ} {f : Field} {a : Mode → ℝ} (hf : InH s f)
    (ha : ∀ k, a k = w4 k * (Real.sqrt (sobWeight s k) * ‖f k‖)) :
    Summable a ∧ ∑' k, a k ≤ c4 * hnorm s f := by
  have h := weighted_cs hf w4_nonneg (w := w4) (by simpa only [w4_sq] using summable_inv4) ha
  simp only [w4_sq] at h
  exact h

/-! ### Low and high frequency weights -/

/-- The weight `|k|⁻¹` on `0 < |k| ≤ R`. -/
private def wLo (R : ℝ) (k : Mode) : ℝ := if absk k ≤ R ∧ k ≠ 0 then (absk k)⁻¹ else 0

/-- The weight `|k|⁻²` on `|k| > R`. -/
private def wHi (R : ℝ) (k : Mode) : ℝ := if absk k ≤ R then 0 else (absSq k)⁻¹

private lemma wLo_nonneg (R : ℝ) (k : Mode) : 0 ≤ wLo R k := by
  unfold wLo
  split_ifs
  · exact inv_nonneg.2 (absk_nonneg k)
  · exact le_rfl

private lemma wHi_nonneg (R : ℝ) (k : Mode) : 0 ≤ wHi R k := by
  unfold wHi
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.2 (absSq_nonneg k)

private lemma wLo_sq_le (R : ℝ) (k : Mode) : wLo R k ^ 2 ≤ w4 k := by
  unfold wLo
  split_ifs with h
  · rw [w4, ite_eq_right h.2, inv_pow, absk_sq]
  · simpa using w4_nonneg k

private lemma wLo_sum {R : ℝ} (hR : 1 ≤ R) :
    (Summable fun k => wLo R k ^ 2) ∧ ∑' k, wLo R k ^ 2 ≤ 5488 * R := by
  have h0 : ∀ k ∉ ballF R, wLo R k ^ 2 = 0 := fun k hk => by
    have h : ¬ (absk k ≤ R ∧ k ≠ 0) := fun h => hk (mem_ballF.2 h.1)
    simp [wLo, h]
  refine ⟨summable_of_ne_finset_zero h0, ?_⟩
  rw [tsum_eq_sum h0]
  exact (Finset.sum_le_sum fun k _ => wLo_sq_le R k).trans (low_sum hR)

private lemma wHi_sum {R : ℝ} (hR : 1 ≤ R) :
    (Summable fun k => wHi R k ^ 2) ∧ ∑' k, wHi R k ^ 2 ≤ 5488 / R := by
  have h := summable_tail (ψ := fun k => wHi R k ^ 2) (fun k => sq_nonneg _) (fun k => by
    unfold wHi
    split_ifs
    · simpa using sq_nonneg (absSq k)⁻¹
    · exact le_rfl) hR
  have h0 : ∑ k ∈ ballF R, wHi R k ^ 2 = 0 := Finset.sum_eq_zero fun k hk => by
    simp [wHi, mem_ballF.1 hk]
  rw [h0, zero_add] at h
  exact h

private lemma ne_zero_of_lt {R : ℝ} (hR : 1 ≤ R) {k : Mode} (h : ¬ absk k ≤ R) : k ≠ 0 := by
  rintro rfl
  exact h (by rw [absk_eq_zero.2 rfl]; linarith)

/-- The high-frequency part is controlled by `(5488/R)^{1/2} ‖f‖₂`. -/
private lemma high_part {f : Field} (hf : InH 2 f) {R : ℝ} (hR : 1 ≤ R) :
    (Summable fun k => if absk k ≤ R then 0 else ‖f k‖) ∧
      ∑' k, (if absk k ≤ R then 0 else ‖f k‖) ≤ Real.sqrt (5488 / R) * hnorm 2 f := by
  have hw := wHi_sum hR
  have h := weighted_cs (w := wHi R) (a := fun k => if absk k ≤ R then 0 else ‖f k‖) hf
    (wHi_nonneg R) hw.1 (fun k => by
      by_cases hk : absk k ≤ R
      · simp [hk, wHi]
      · have hk0 := ne_zero_of_lt hR hk
        have h1 := w4_mul_ne 0 (s := 2) (by norm_num) f hk0
        simp only [pow_zero, one_mul, w4, ite_eq_right hk0] at h1
        simpa [hk, wHi] using h1)
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hw.2)
    (hnorm_nonneg 2 f))⟩

/-- The low-frequency part is controlled by `(5488 R)^{1/2} ‖f‖₁`. -/
private lemma low_part {f : Field} (hf : InH 1 f) (hf0 : f 0 = 0) {R : ℝ} (hR : 1 ≤ R) :
    (Summable fun k => if absk k ≤ R then ‖f k‖ else 0) ∧
      ∑' k, (if absk k ≤ R then ‖f k‖ else 0) ≤ Real.sqrt (5488 * R) * hnorm 1 f := by
  have hw := wLo_sum hR
  have h := weighted_cs (w := wLo R) (a := fun k => if absk k ≤ R then ‖f k‖ else 0) hf
    (wLo_nonneg R) hw.1 (fun k => by
      by_cases hk0 : k = 0
      · subst hk0
        simp [hf0]
      by_cases hk : absk k ≤ R
      · have h1 : absk k ≠ 0 := fun h => hk0 (absk_eq_zero.1 h)
        rw [ite_eq_left hk, wLo, ite_eq_left ⟨hk, hk0⟩, sqrt_sob (n := 1) (by norm_num) hk0,
          pow_one]
        field_simp
      · simp [hk, wLo])
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hw.2)
    (hnorm_nonneg 1 f))⟩

/-- Splitting at frequency `R ≥ 1`. -/
private lemma wiener_split {u : Field} (hu : MZ 2 u) {R : ℝ} (hR : 1 ≤ R) :
    wiener u ≤ Real.sqrt (5488 * R) * hnorm 1 u + Real.sqrt (5488 / R) * hnorm 2 u := by
  have hL := low_part (hu.inH.mono (by norm_num)) hu.mean hR
  have hH := high_part hu.inH hR
  have e : wiener u = ∑' k, (if absk k ≤ R then ‖u k‖ else 0) +
      ∑' k, (if absk k ≤ R then 0 else ‖u k‖) := by
    rw [← hL.1.tsum_add hH.1, wiener]
    refine tsum_congr fun k => ?_
    split_ifs <;> simp
  rw [e]
  exact add_le_add hL.2 hH.2

variable {u : Field}

lemma summable_wiener (hu : InH 2 u) : Summable fun k => ‖u k‖ := by
  have h1 := (w4_cs (a := fun k => if k = 0 then 0 else ‖u k‖) hu (fun k => by
    by_cases hk : k = 0
    · simp [hk, w4]
    · simpa [hk] using w4_mul_ne 0 (s := 2) (by norm_num) u hk)).1
  have h2 : Summable fun k : Mode => if k = 0 then ‖u 0‖ else 0 :=
    (hasSum_ite_eq (0 : Mode) ‖u 0‖).summable
  refine (h1.add h2).congr fun k => ?_
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk]

lemma wiener_nonneg (u : Field) : 0 ≤ wiener u := tsum_nonneg fun _ => norm_nonneg _

/-- `𝒜(u) ≤ c₄ ‖u‖₂`. -/
lemma wiener_le (hu : MZ 2 u) : wiener u ≤ c4 * hnorm 2 u :=
  (w4_cs (a := fun k => ‖u k‖) hu.inH fun k => by
    simpa using w4_mul 0 (s := 2) (by norm_num) hu.mean k).2

/-- `𝒜(∇u) ≤ c₄ ‖u‖₃`. -/
lemma wiener_grad_le (hu : MZ 3 u) :
    Summable (fun k => absk k * ‖u k‖) ∧ ∑' k, absk k * ‖u k‖ ≤ c4 * hnorm 3 u :=
  w4_cs hu.inH fun k => by
    simpa using w4_mul 1 (s := 3) (by norm_num) hu.mean k

/-- Wiener interpolation: `𝒜(u) ≤ c_I ‖u‖₁^{1/2} ‖u‖₂^{1/2}`. -/
theorem exists_wiener_interp :
    ∃ cI : ℝ, 0 < cI ∧ ∀ u : Field, MZ 2 u →
      wiener u ≤ cI * Real.sqrt (hnorm 1 u * hnorm 2 u) := by
  refine ⟨2 * Real.sqrt 5488, by positivity, fun u hu => ?_⟩
  have hu1 : InH 1 u := hu.inH.mono (by norm_num)
  have hA0 := hnorm_nonneg 1 u
  have hAB : hnorm 1 u ≤ hnorm 2 u := hnorm_mono (by norm_num) hu.inH
  rcases hA0.eq_or_lt with hA | hA
  · have h0 : u = 0 := eq_zero_of_hnorm_eq_zero hu1 hu.mean hA.symm
    subst h0
    simp only [wiener, Pi.zero_apply, norm_zero, tsum_zero]
    positivity
  have hB : 0 < hnorm 2 u := hA.trans_le hAB
  have hR : 1 ≤ hnorm 2 u / hnorm 1 u := (one_le_div hA).2 hAB
  refine (wiener_split hu hR).trans (le_of_eq ?_)
  have e1 : (5488 : ℝ) * (hnorm 2 u / hnorm 1 u) * hnorm 1 u ^ 2
      = 5488 * (hnorm 1 u * hnorm 2 u) := by
    field_simp
  have e2 : (5488 : ℝ) / (hnorm 2 u / hnorm 1 u) * hnorm 2 u ^ 2
      = 5488 * (hnorm 1 u * hnorm 2 u) := by
    field_simp
  have h1 : Real.sqrt (5488 * (hnorm 2 u / hnorm 1 u)) * hnorm 1 u
      = Real.sqrt (5488 * (hnorm 1 u * hnorm 2 u)) := by
    rw [← e1, Real.sqrt_mul (mul_nonneg (by norm_num) (div_pos hB hA).le) (_ ^ 2), Real.sqrt_sq hA0]
  have h2 : Real.sqrt (5488 / (hnorm 2 u / hnorm 1 u)) * hnorm 2 u
      = Real.sqrt (5488 * (hnorm 1 u * hnorm 2 u)) := by
    rw [← e2, Real.sqrt_mul (div_pos (by norm_num) (div_pos hB hA)).le (_ ^ 2),
      Real.sqrt_sq hB.le]
  rw [h1, h2, Real.sqrt_mul (by norm_num)]
  ring

/-- High-frequency Wiener tail: `∑_{|k|>N} |k|⁻⁴ ≤ c_b/N`. -/
theorem exists_wiener_tail :
    ∃ cb : ℝ, 0 < cb ∧ ∀ (N : ℕ) (u : Field), 1 ≤ N → MZ 2 u → (∀ k, absk k ≤ N → u k = 0) →
      wiener u ≤ Real.sqrt (cb / N) * hnorm 2 u := by
  refine ⟨5488, by norm_num, fun N u hN hu hlow => ?_⟩
  have h := (high_part hu.inH (R := N) (by exact_mod_cast hN)).2
  refine le_of_eq_of_le (tsum_congr fun k => ?_) h
  by_cases hk : absk k ≤ N
  · simp [hk, hlow k hk]
  · simp [hk]

lemma wiener_add_le (hu : Summable fun k => ‖u k‖) {v : Field} (hv : Summable fun k => ‖v k‖) :
    wiener (u + v) ≤ wiener u + wiener v := by
  have h : Summable fun k => ‖(u + v) k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_add_le (u k) (v k)) (hu.add hv)
  unfold wiener
  rw [← hu.tsum_add hv]
  exact h.tsum_le_tsum (fun k => norm_add_le (u k) (v k)) (hu.add hv)

end OVNS
