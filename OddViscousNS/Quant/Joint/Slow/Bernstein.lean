import OddViscousNS.Quant.Joint.Slow.Smoothing

/-!
# E7-P: Bernstein on the slow boxes

* `norm_ev_pow_le`: Nikolskii at even exponent, `‖P‖_∞^{2q} ≤ (2qN+1)² ∫ |P|^{2q}` when the spectrum
  of `P` lies in `slowBox N`: `P^q` has its spectrum in `slowBox (qN)`, then `ℓ¹ ≤ √card ℓ²`.
* `tsum_tail_le`: the tail of a slow `H²` field above `slowBox N` is `≲ ‖u‖₂/N`.
* `wiener_log_le`: the 2D logarithmic Wiener bound (Brezis–Gallouët form),
  `𝒜(u) ≲ √(1 + log N) ‖u‖₁ + ‖u‖₂/N`.

Both lattice sums run over the square shells of `Energy/Slow/Lattice2D.lean`: `8n` points with
`|k|² ≥ n²`, whence `∑_{0<|k|_∞≤N} |k|⁻² ≤ 8 H_N` and `∑_{|k|_∞>N} |k|⁻⁴ ≤ 4/(N+½)²`.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.Slow

open GN

/-! ### Nikolskii at even exponent -/

lemma add_mem_slowBox {a b : Mode} {m n : ℕ} (ha : a ∈ slowBox m) (hb : b ∈ slowBox n) :
    a + b ∈ slowBox (m + n) := by
  rw [mem_slowBox] at ha hb ⊢
  obtain ⟨a2, a0, a1⟩ := ha
  obtain ⟨b2, b0, b1⟩ := hb
  push_cast
  exact ⟨by simp [a2, b2], (abs_add_le _ _).trans (add_le_add a0 b0),
    (abs_add_le _ _).trans (add_le_add a1 b1)⟩

lemma zero_mem_slowBox (n : ℕ) : (0 : Mode) ∈ slowBox n := by
  rw [mem_slowBox]
  simp

private lemma eq_zero_of_mem_slowBox_zero {k : Mode} (hk : k ∈ slowBox 0) : k = 0 := by
  rw [mem_slowBox] at hk
  funext i
  fin_cases i
  · simpa using abs_nonpos_iff.1 (by simpa using hk.2.1)
  · simpa using abs_nonpos_iff.1 (by simpa using hk.2.2)
  · simpa using hk.1

/-- The spectrum of `P^q`. -/
lemma pow_mem_slowBox {P : Pol} {N : ℕ} (hP : ∀ k, P.coeff k ≠ 0 → k ∈ slowBox N) (q : ℕ) :
    ∀ k, (P ^ q).coeff k ≠ 0 → k ∈ slowBox (q * N) := by
  classical
  induction q with
  | zero =>
    intro k hk
    rw [pow_zero, AddMonoidAlgebra.one_def] at hk
    have : k = 0 := by
      by_contra h0
      apply hk
      simp [AddMonoidAlgebra.coeff_single, Ne.symm h0]
    simpa [this] using zero_mem_slowBox _
  | succ q ih =>
    intro k hk
    rw [pow_succ] at hk
    have h := AddMonoidAlgebra.support_coeff_mul_subset (P ^ q) P (Finsupp.mem_support_iff.2 hk)
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 h
    have h2 := add_mem_slowBox (ih a (Finsupp.mem_support_iff.1 ha))
      (hP b (Finsupp.mem_support_iff.1 hb))
    rwa [show q * N + N = (q + 1) * N by ring] at h2

/-- `ℓ¹ ≤ √card ℓ²` for the value of a polynomial. -/
private lemma norm_ev_sq_le (Q : Pol) (x : T3) :
    ‖ev Q x‖ ^ 2 ≤ Q.coeff.support.card * nn2 Q := by
  have h1 : ‖ev Q x‖ ≤ ∑ k ∈ Q.coeff.support, ‖Q.coeff k‖ := by
    rw [ev_eq_tp, tp_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_mFourier_le k x)
  have h2 : (∑ k ∈ Q.coeff.support, ‖Q.coeff k‖) ^ 2 ≤
      Q.coeff.support.card * ∑ k ∈ Q.coeff.support, ‖Q.coeff k‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [nn2, integral_norm_sq_ev]
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- **Nikolskii at even exponent on slow boxes.** -/
theorem norm_ev_pow_le {P : Pol} {N : ℕ} (hP : ∀ k, P.coeff k ≠ 0 → k ∈ slowBox N) {q : ℕ}
    (hq : 1 ≤ q) (x : T3) :
    ‖ev P x‖ ^ (2 * q) ≤ (2 * (q : ℝ) * N + 1) ^ 2 * mP q P := by
  have _ := hq
  have hsub : (P ^ q).coeff.support ⊆ slowBox (q * N) := fun k hk =>
    pow_mem_slowBox hP q k (Finsupp.mem_support_iff.1 hk)
  have hcard : ((P ^ q).coeff.support.card : ℝ) ≤ (2 * (q : ℝ) * N + 1) ^ 2 := by
    have h := Finset.card_le_card hsub
    rw [card_slowBox] at h
    have h' : ((P ^ q).coeff.support.card : ℝ) ≤ (((2 * (q * N) + 1) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h
    refine h'.trans_eq ?_
    push_cast
    ring
  have e : ‖ev P x‖ ^ (2 * q) = ‖ev (P ^ q) x‖ ^ 2 := by
    simp only [map_pow, ContinuousMap.coe_pow, Pi.pow_apply, norm_pow]
    ring
  rw [e, mP_eq_nn2]
  exact (norm_ev_sq_le _ x).trans (mul_le_mul_of_nonneg_right hcard (nn2_nonneg _))

/-! ### The shell sums -/

private lemma sum_shell_le {f : Mode → ℝ} {n : ℕ} {B : ℝ}
    (hf : ∀ k ∈ slowBox (n + 1) \ slowBox n, f k ≤ B) :
    ∑ k ∈ slowBox (n + 1) \ slowBox n, f k ≤ 8 * ((n : ℝ) + 1) * B := by
  have h := Finset.sum_le_card_nsmul _ f B hf
  rw [card_shell, nsmul_eq_mul] at h
  refine h.trans_eq ?_
  push_cast
  ring

private lemma inv_absSq_le_shell {n : ℕ} {k : Mode} (hk : k ∈ slowBox (n + 1) \ slowBox n) :
    (absSq k)⁻¹ ≤ (((n : ℝ) + 1) ^ 2)⁻¹ :=
  inv_anti₀ (by positivity) (shell_spec hk).2.2

/-- `∑_{0<|k|_∞≤N} |k|⁻² ≤ 8 H_N`, the point `k = 0` contributing `0⁻¹ = 0`. -/
lemma sum_inv_absSq_le (N : ℕ) :
    ∑ k ∈ slowBox N, (absSq k)⁻¹ ≤ 8 * ∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹ := by
  induction N with
  | zero =>
    have h : ∑ k ∈ slowBox 0, (absSq k)⁻¹ = 0 := Finset.sum_eq_zero fun k hk => by
      simp [eq_zero_of_mem_slowBox_zero hk, absSq]
    simp [h]
  | succ N ih =>
    rw [← Finset.sum_sdiff (slowBox_mono (Nat.le_succ N)), Finset.sum_range_succ, mul_add]
    have h := sum_shell_le (n := N) (f := fun k => (absSq k)⁻¹) fun k hk => inv_absSq_le_shell hk
    have e : 8 * ((N : ℝ) + 1) * (((N : ℝ) + 1) ^ 2)⁻¹ = 8 * ((N : ℝ) + 1)⁻¹ := by
      field_simp
    linarith

private lemma sum_inv_le_log (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have e : ((harmonic N : ℚ) : ℝ) = ∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹ := by
    simp [harmonic, Rat.cast_sum]
  rwa [e] at h

/-- The cubic telescoping: `8m/m⁴ ≤ 4/(m−½)² − 4/(m+½)²`, for `m = n + 1`. -/
private lemma shell_cube_le (n : ℕ) :
    8 * ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ 4)⁻¹ ≤
      4 / ((n : ℝ) + 1 / 2) ^ 2 - 4 / ((n : ℝ) + 3 / 2) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hA : 0 < ((n : ℝ) + 1 / 2) ^ 2 := by positivity
  have hB : 0 < ((n : ℝ) + 3 / 2) ^ 2 := by positivity
  have hU : 0 < ((n : ℝ) + 1) ^ 4 := by positivity
  rw [div_sub_div _ _ hA.ne' hB.ne', ← div_eq_mul_inv, div_le_div_iff₀ hU (mul_pos hA hB)]
  set m : ℝ := (n : ℝ) + 1 with hm
  have hm1 : 1 ≤ m := by linarith
  have e1 : (n : ℝ) + 1 / 2 = m - 1 / 2 := by rw [hm]; ring
  have e2 : (n : ℝ) + 3 / 2 = m + 1 / 2 := by rw [hm]; ring
  rw [e1, e2]
  have key : (m - 1 / 2) ^ 2 * (m + 1 / 2) ^ 2 ≤ m ^ 4 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key (by linarith : (0 : ℝ) ≤ 8 * m)]

/-- The weight `|k|⁻²` on the slow modes off `slowBox N`. -/
private def wHi (N : ℕ) (k : Mode) : ℝ := if k ∉ slowBox N ∧ k 2 = 0 then (absSq k)⁻¹ else 0

private lemma wHi_nonneg (N : ℕ) (k : Mode) : 0 ≤ wHi N k := by
  unfold wHi
  split_ifs
  · exact inv_nonneg.2 (absSq_nonneg k)
  · exact le_rfl

private lemma wHi_sq_le_shell (N : ℕ) {n : ℕ} {k : Mode} (hk : k ∈ slowBox (n + 1) \ slowBox n) :
    wHi N k ^ 2 ≤ (((n : ℝ) + 1) ^ 4)⁻¹ := by
  have h1 : wHi N k ≤ (((n : ℝ) + 1) ^ 2)⁻¹ := by
    unfold wHi
    split_ifs
    · exact inv_absSq_le_shell hk
    · positivity
  have h2 := pow_le_pow_left₀ (wHi_nonneg N k) h1 2
  refine h2.trans_eq ?_
  rw [inv_pow]
  ring_nf

/-- The partial sums of the tail. -/
private lemma sum_wHi_le (N M : ℕ) :
    ∑ k ∈ slowBox (N + M), wHi N k ^ 2 ≤
      4 / ((N : ℝ) + 1 / 2) ^ 2 - 4 / (((N + M : ℕ) : ℝ) + 1 / 2) ^ 2 := by
  induction M with
  | zero =>
    have h : ∑ k ∈ slowBox N, wHi N k ^ 2 = 0 := Finset.sum_eq_zero fun k hk => by
      simp [wHi, hk]
    simp [h]
  | succ M ih =>
    rw [← add_assoc, ← Finset.sum_sdiff (slowBox_mono (Nat.le_succ (N + M)))]
    have h := sum_shell_le (n := N + M) (f := fun k => wHi N k ^ 2) fun k hk => wHi_sq_le_shell N hk
    have h' := shell_cube_le (N + M)
    have e : (((N + M : ℕ) : ℝ) + 3 / 2) = (((N + M + 1 : ℕ) : ℝ) + 1 / 2) := by
      push_cast
      ring
    rw [e] at h'
    linarith

/-- A finite set of slow modes lies in a box. -/
private lemma exists_slowBox (s : Finset Mode) :
    ∃ n : ℕ, s.filter (fun k : Mode => k 2 = 0) ⊆ slowBox n := by
  obtain ⟨M, hM⟩ := (s.image fun k : Mode => |k 0| ⊔ |k 1|).exists_le
  refine ⟨M.toNat, fun k hk => ?_⟩
  rw [Finset.mem_filter] at hk
  have h := hM _ (Finset.mem_image_of_mem (fun k : Mode => |k 0| ⊔ |k 1|) hk.1)
  have hMn : M ≤ (M.toNat : ℤ) := Int.self_le_toNat M
  rw [mem_slowBox]
  exact ⟨hk.2, (le_sup_left.trans h).trans hMn, (le_sup_right.trans h).trans hMn⟩

/-- `∑_{|k|_∞>N} |k|⁻⁴ ≤ 4/N²` on the slow modes. -/
private lemma wHi_sum (N : ℕ) (hN : 1 ≤ N) :
    (Summable fun k => wHi N k ^ 2) ∧ ∑' k, wHi N k ^ 2 ≤ 4 / (N : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : 0 ≤ fun k => wHi N k ^ 2 := fun k => sq_nonneg _
  have key : ∀ s : Finset Mode, ∑ k ∈ s, wHi N k ^ 2 ≤ 4 / (N : ℝ) ^ 2 := by
    intro s
    obtain ⟨M, hM⟩ := exists_slowBox s
    have hfilt : ∑ k ∈ s.filter (fun k : Mode => k 2 = 0), wHi N k ^ 2 =
        ∑ k ∈ s, wHi N k ^ 2 := by
      refine Finset.sum_filter_of_ne fun k _ hk => ?_
      by_contra h2
      exact hk (by simp [wHi, h2])
    rw [← hfilt]
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (hM.trans (slowBox_mono (Nat.le_add_left M N))) fun k _ _ => sq_nonneg _).trans ?_
    refine (sum_wHi_le N M).trans ?_
    have h1 : 0 ≤ 4 / (((N + M : ℕ) : ℝ) + 1 / 2) ^ 2 := by positivity
    have h2 : 4 / ((N : ℝ) + 1 / 2) ^ 2 ≤ 4 / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ hN0.le (by linarith) 2)
    linarith
  exact ⟨summable_of_sum_le h0 key, Real.tsum_le_of_sum_le h0 key⟩

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

private lemma sqrt_sobWeight_one {k : Mode} (hk : k ≠ 0) : Real.sqrt (sobWeight 1 k) = absk k := by
  have h : (2 * 1 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [sobWeight, ite_eq_right hk, h, Real.rpow_natCast, Real.sqrt_sq (absk_nonneg k)]

private lemma sqrt_sobWeight_two {k : Mode} (hk : k ≠ 0) :
    Real.sqrt (sobWeight 2 k) = absSq k := by
  have h : (2 * 2 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  have e : absk k ^ 4 = (absSq k) ^ 2 := by
    rw [← absk_sq]
    ring
  rw [sobWeight, ite_eq_right hk, h, Real.rpow_natCast, e, Real.sqrt_sq (absSq_nonneg k)]

/-! ### The tail and the logarithmic Wiener bound -/

/-- The tail above `slowBox N`, with the sharper constant `2`. -/
private lemma tail_part {u : Field} (hu : InH 2 u) (hs : ∀ k, k 2 ≠ 0 → u k = 0) {N : ℕ}
    (hN : 1 ≤ N) :
    (Summable fun k => if k ∈ slowBox N then 0 else ‖u k‖) ∧
      ∑' k, (if k ∈ slowBox N then 0 else ‖u k‖) ≤ 2 * hnorm 2 u / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := wHi_sum N hN
  have h := weighted_cs (w := wHi N) (a := fun k => if k ∈ slowBox N then 0 else ‖u k‖) hu
    (wHi_nonneg N) hw.1 (fun k => by
      by_cases hk : k ∈ slowBox N
      · simp [hk, wHi]
      by_cases h2 : k 2 = 0
      · have hk0 : k ≠ 0 := fun h => hk (h ▸ zero_mem_slowBox N)
        have hne : absSq k ≠ 0 := (zero_lt_one.trans_le (one_le_absSq hk0)).ne'
        simp only [hk, ite_false, wHi, not_false_eq_true, h2, and_self, ite_true,
          sqrt_sobWeight_two hk0]
        field_simp
      · simp [hk, wHi, h2, hs k h2])
  refine ⟨h.1, h.2.trans ?_⟩
  have e : Real.sqrt (4 / (N : ℝ) ^ 2) = 2 / N := by
    rw [show (4 : ℝ) / (N : ℝ) ^ 2 = (2 / N) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h3 := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hw.2) (hnorm_nonneg 2 u)
  rw [e] at h3
  exact h3.trans_eq (by ring)

/-- The weight `|k|⁻¹` on `slowBox N`, the point `k = 0` contributing `0⁻¹ = 0`. -/
private def wLo (N : ℕ) (k : Mode) : ℝ := if k ∈ slowBox N then (absk k)⁻¹ else 0

private lemma wLo_nonneg (N : ℕ) (k : Mode) : 0 ≤ wLo N k := by
  unfold wLo
  split_ifs
  · exact inv_nonneg.2 (absk_nonneg k)
  · exact le_rfl

private lemma wLo_sum (N : ℕ) :
    (Summable fun k => wLo N k ^ 2) ∧ ∑' k, wLo N k ^ 2 ≤ 8 * (1 + Real.log N) := by
  have h0 : ∀ k ∉ slowBox N, wLo N k ^ 2 = 0 := fun k hk => by simp [wLo, hk]
  refine ⟨summable_of_ne_finset_zero h0, ?_⟩
  rw [tsum_eq_sum h0]
  have e : ∑ k ∈ slowBox N, wLo N k ^ 2 = ∑ k ∈ slowBox N, (absSq k)⁻¹ :=
    Finset.sum_congr rfl fun k hk => by rw [wLo, ite_eq_left hk, inv_pow, absk_sq]
  rw [e]
  exact (sum_inv_absSq_le N).trans (mul_le_mul_of_nonneg_left (sum_inv_le_log N) (by norm_num))

/-- The part in `slowBox N`, with the sharper constant `3`. -/
private lemma low_part {u : Field} (hu : InH 1 u) (h0 : u 0 = 0) (N : ℕ) :
    (Summable fun k => if k ∈ slowBox N then ‖u k‖ else 0) ∧
      ∑' k, (if k ∈ slowBox N then ‖u k‖ else 0) ≤
        3 * Real.sqrt (1 + Real.log N) * hnorm 1 u := by
  have hw := wLo_sum N
  have h := weighted_cs (w := wLo N) (a := fun k => if k ∈ slowBox N then ‖u k‖ else 0) hu
    (wLo_nonneg N) hw.1 (fun k => by
      by_cases hk0 : k = 0
      · subst hk0
        simp [h0]
      by_cases hk : k ∈ slowBox N
      · have h1 : absk k ≠ 0 := fun h => hk0 (absk_eq_zero.1 h)
        rw [ite_eq_left hk, wLo, ite_eq_left hk, sqrt_sobWeight_one hk0]
        field_simp
      · simp [hk, wLo])
  refine ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right ?_ (hnorm_nonneg 1 u))⟩
  refine (Real.sqrt_le_sqrt hw.2).trans ?_
  rw [Real.sqrt_mul (by norm_num)]
  have h8 : Real.sqrt 8 ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  exact mul_le_mul_of_nonneg_right h8 (Real.sqrt_nonneg _)

/-- **Tail of a slow field above a box, in `H²`.** -/
theorem tsum_tail_le {u : Field} (hu : InH 2 u) (hs : ∀ k, k 2 ≠ 0 → u k = 0) (h0 : u 0 = 0)
    {N : ℕ} (hN : 1 ≤ N) :
    ∑' k, (if k ∈ slowBox N then 0 else ‖u k‖) ≤ 4 * hnorm 2 u / N := by
  have _ := h0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine (tail_part hu hs hN).2.trans ?_
  exact div_le_div_of_nonneg_right (by linarith [hnorm_nonneg 2 u]) hN0.le

/-- **The 2D logarithmic Wiener bound (Brezis–Gallouët form).** -/
theorem wiener_log_le {u : Field} (hu : InH 2 u) (hs : ∀ k, k 2 ≠ 0 → u k = 0) (h0 : u 0 = 0)
    {N : ℕ} (hN : 1 ≤ N) :
    wiener u ≤ 4 * Real.sqrt (1 + Real.log N) * hnorm 1 u + 4 * hnorm 2 u / N := by
  have hL := low_part (hu.mono (by norm_num)) h0 N
  have hH := tail_part hu hs hN
  have e : wiener u = ∑' k, (if k ∈ slowBox N then ‖u k‖ else 0) +
      ∑' k, (if k ∈ slowBox N then 0 else ‖u k‖) := by
    rw [← hL.1.tsum_add hH.1, wiener]
    refine tsum_congr fun k => ?_
    split_ifs <;> simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 3 * Real.sqrt (1 + Real.log N) * hnorm 1 u ≤
      4 * Real.sqrt (1 + Real.log N) * hnorm 1 u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))
      (hnorm_nonneg 1 u)
  have h2 : 2 * hnorm 2 u / N ≤ 4 * hnorm 2 u / N :=
    div_le_div_of_nonneg_right (by linarith [hnorm_nonneg 2 u]) hN0.le
  rw [e]
  linarith [hL.2, hH.2]

end OVNS.Quant.Slow
