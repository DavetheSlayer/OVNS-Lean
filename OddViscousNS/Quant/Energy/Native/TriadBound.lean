import OddViscousNS.Quant.Energy.Native.Triad

/-!
# Theorem 1.2, fixed force — E5/E8 native layer: the pointwise bound on a triad term

On a nondegenerate triad `(p, q, −(p+q))` the triad term `nearTriadTerm` is, helicity by
helicity, the phase `e^{iτΦ}` times the cyclic sum `cyc3` of the three rootings weighted by
`f_j(|out|²)` (`nearTriadTerm_eq`; the near mask, the phase and `Φ` are common to the three
rootings by `nearT_cyc`, `Phi_cyc`).  The cyclic sum is bounded by `triad_cyclic_le` after
sorting the legs, which gives (`abs_nearTriadTerm_le`)
`|T(p,q)| ≤ Σ_{a,b,c} 𝟏_{near} · 13 m K^{2j}/√(K⁴ + r²Φ²) · ‖G_p‖ ‖F_q‖ ‖F_{−(p+q)}‖`
for any `m` above the shortest leg and `K` above the longest one.
-/

noncomputable section

namespace OVNS.Quant

open scoped Classical

/-! ### The cyclic sum of a triad and its permutation invariance -/

/-- The three rootings of the triad `(ℓ₀, ℓ₁, ℓ₂)` with helical amplitudes
`A_i = hel s_i ℓ_i v_i`, weighted by `f_j(|out|²)` (the expression of `triad_cyclic_le`). -/
def cyc3 (j : ℕ) (ε z : ℝ) (ℓ0 ℓ1 ℓ2 : Mode) (s0 s1 s2 : Sgn) (v0 v1 v2 : V3) : ℂ :=
  tau ℓ0 ℓ1 (hel s0 ℓ0 v0) (hel s1 ℓ1 v1) (hel s2 ℓ2 v2) * fres j ε z (absSq ℓ2) +
    tau ℓ1 ℓ2 (hel s1 ℓ1 v1) (hel s2 ℓ2 v2) (hel s0 ℓ0 v0) * fres j ε z (absSq ℓ0) +
    tau ℓ2 ℓ0 (hel s2 ℓ2 v2) (hel s0 ℓ0 v0) (hel s1 ℓ1 v1) * fres j ε z (absSq ℓ1)

private lemma cyc3_rot (j : ℕ) (ε z : ℝ) (ℓ0 ℓ1 ℓ2 : Mode) (s0 s1 s2 : Sgn) (v0 v1 v2 : V3) :
    cyc3 j ε z ℓ1 ℓ2 ℓ0 s1 s2 s0 v1 v2 v0 = cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 := by
  unfold cyc3
  ring

private lemma cyc3_swap (j : ℕ) (ε z : ℝ) (ℓ0 ℓ1 ℓ2 : Mode) (s0 s1 s2 : Sgn) (v0 v1 v2 : V3) :
    cyc3 j ε z ℓ1 ℓ0 ℓ2 s1 s0 s2 v1 v0 v2 = cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 := by
  unfold cyc3
  rw [tau_comm ℓ1 ℓ0, tau_comm ℓ0 ℓ2, tau_comm ℓ2 ℓ1]
  ring

/-- The kernel `13 m K^{2j}/√(K⁴ + z²)` of `triad_cyclic_le`. -/
def kerB (j : ℕ) (z m K : ℝ) : ℝ := 13 * m * K ^ (2 * j) / Real.sqrt (K ^ 4 + z ^ 2)

theorem kerB_nonneg (j : ℕ) (z : ℝ) {m K : ℝ} (hm : 0 ≤ m) (hK : 0 ≤ K) : 0 ≤ kerB j z m K := by
  unfold kerB
  positivity

private lemma pow_ratio_mono {j : ℕ} (hj : 1 ≤ j) (z : ℝ) {K M : ℝ} (hK : 0 < K) (hKM : K ≤ M) :
    K ^ (2 * j) / Real.sqrt (K ^ 4 + z ^ 2) ≤ M ^ (2 * j) / Real.sqrt (M ^ 4 + z ^ 2) := by
  have hM : 0 < M := hK.trans_le hKM
  have hA : 0 < Real.sqrt (K ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hB : 0 < Real.sqrt (M ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [div_le_div_iff₀ hA hB]
  have e : ∀ x : ℝ, x ^ (2 * j) = x ^ (2 * j - 2) * x ^ 2 := fun x => by
    rw [← pow_add]
    congr 1
    omega
  have h1 : (K ^ (2 * j - 2)) ^ 2 ≤ (M ^ (2 * j - 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hK.le hKM _) 2
  have h2 : K ^ 4 ≤ M ^ 4 := pow_le_pow_left₀ hK.le hKM 4
  have hsq : (K ^ (2 * j) * Real.sqrt (M ^ 4 + z ^ 2)) ^ 2 ≤
      (M ^ (2 * j) * Real.sqrt (K ^ 4 + z ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), e K, e M]
    have h3 : (K ^ (2 * j - 2)) ^ 2 * K ^ 4 * M ^ 4 ≤ (M ^ (2 * j - 2)) ^ 2 * K ^ 4 * M ^ 4 := by
      gcongr
    have h4 : (K ^ (2 * j - 2)) ^ 2 * K ^ 4 * z ^ 2 ≤ (M ^ (2 * j - 2)) ^ 2 * M ^ 4 * z ^ 2 := by
      gcongr
    nlinarith [h3, h4]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq

theorem kerB_mono {j : ℕ} (hj : 1 ≤ j) (z : ℝ) {m mn K mx : ℝ} (hm : 0 ≤ m) (hmn : m ≤ mn)
    (hK : 0 < K) (hKx : K ≤ mx) : kerB j z m K ≤ kerB j z mn mx := by
  have h := pow_ratio_mono hj z hK hKx
  have h0 : 0 ≤ K ^ (2 * j) / Real.sqrt (K ^ 4 + z ^ 2) := by positivity
  have e : ∀ a b : ℝ, kerB j z a b = 13 * a * (b ^ (2 * j) / Real.sqrt (b ^ 4 + z ^ 2)) :=
    fun a b => by unfold kerB; ring
  rw [e, e]
  exact mul_le_mul (by linarith) h h0 (by linarith)

private lemma cyc3_le_sorted {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (z : ℝ)
    {ℓ0 ℓ1 ℓ2 : Mode} (hsum : ℓ0 + ℓ1 + ℓ2 = 0) (h0 : ℓ0 ≠ 0) (h1 : ℓ1 ≠ 0) (h2 : ℓ2 ≠ 0)
    (h01 : absk ℓ0 ≤ absk ℓ1) (h12 : absk ℓ1 ≤ absk ℓ2) (s0 s1 s2 : Sgn) (v0 v1 v2 : V3) :
    ‖cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2‖ ≤
      kerB j z (absk ℓ0) (absk ℓ2) * (‖v0‖ * ‖v1‖ * ‖v2‖) := by
  have h := triad_cyclic_le hj hε z ![ℓ0, ℓ1, ℓ2] (by simp [Fin.sum_univ_three, hsum])
    (fun i => by fin_cases i <;> simpa) (by simpa) (by simpa) ![s0, s1, s2] ![v0, v1, v2]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  have hP : ‖hel s0 ℓ0 v0‖ * ‖hel s1 ℓ1 v1‖ * ‖hel s2 ℓ2 v2‖ ≤ ‖v0‖ * ‖v1‖ * ‖v2‖ := by
    gcongr <;> exact norm_hel_le _ _ _
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left hP (kerB_nonneg j z (absk_nonneg _) (absk_nonneg _))

/-- The cyclic sum of an arbitrary (unsorted) nondegenerate triad: bounded by the kernel at any
`m` above the shortest leg and any `K` above the longest leg. -/
theorem cyc3_le {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (z : ℝ)
    {ℓ0 ℓ1 ℓ2 : Mode} (hsum : ℓ0 + ℓ1 + ℓ2 = 0) (h0 : ℓ0 ≠ 0) (h1 : ℓ1 ≠ 0) (h2 : ℓ2 ≠ 0)
    (s0 s1 s2 : Sgn) (v0 v1 v2 : V3) {mn mx : ℝ}
    (hmn : absk ℓ0 ≤ mn ∨ absk ℓ1 ≤ mn ∨ absk ℓ2 ≤ mn)
    (hmx : absk ℓ0 ≤ mx ∧ absk ℓ1 ≤ mx ∧ absk ℓ2 ≤ mx) :
    ‖cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2‖ ≤ kerB j z mn mx * (‖v0‖ * ‖v1‖ * ‖v2‖) := by
  have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> norm_num
  have p0 := lt_of_lt_of_le one_pos (one_le_absk h0)
  have p1 := lt_of_lt_of_le one_pos (one_le_absk h1)
  have p2 := lt_of_lt_of_le one_pos (one_le_absk h2)
  obtain ⟨hx0, hx1, hx2⟩ := hmx
  have hP0 : 0 ≤ ‖v0‖ * ‖v1‖ * ‖v2‖ := by positivity
  -- conclude from a sorted relabelling with smallest leg `a` and largest leg `c`
  have fin : ∀ {a c : Mode} {P : ℝ}, P = ‖v0‖ * ‖v1‖ * ‖v2‖ →
      ‖cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2‖ ≤ kerB j z (absk a) (absk c) * P →
      absk a ≤ mn → 0 < absk c → absk c ≤ mx →
      ‖cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2‖ ≤ kerB j z mn mx * (‖v0‖ * ‖v1‖ * ‖v2‖) := by
    intro a c P hP hle ha hc hcx
    rw [hP] at hle
    exact hle.trans (mul_le_mul_of_nonneg_right
      (kerB_mono hj1 z (absk_nonneg a) ha hc hcx) hP0)
  rcases le_total (absk ℓ0) (absk ℓ1) with h01 | h01 <;>
    rcases le_total (absk ℓ1) (absk ℓ2) with h12 | h12 <;>
    rcases le_total (absk ℓ0) (absk ℓ2) with h02 | h02
  · exact fin rfl (cyc3_le_sorted hj hε z hsum h0 h1 h2 h01 h12 _ _ _ _ _ _)
      (by rcases hmn with h | h | h <;> linarith) p2 hx2
  · exact fin rfl (cyc3_le_sorted hj hε z hsum h0 h1 h2 h01 h12 _ _ _ _ _ _)
      (by rcases hmn with h | h | h <;> linarith) p2 hx2
  · -- order ℓ0 ≤ ℓ2 ≤ ℓ1
    have hs : ℓ0 + ℓ2 + ℓ1 = 0 := by rw [← hsum]; abel
    have e : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 = cyc3 j ε z ℓ0 ℓ2 ℓ1 s0 s2 s1 v0 v2 v1 :=
      ((cyc3_rot j ε z ℓ1 ℓ0 ℓ2 s1 s0 s2 v1 v0 v2).trans
        (cyc3_swap j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2)).symm
    refine fin (a := ℓ0) (c := ℓ1) (P := ‖v0‖ * ‖v2‖ * ‖v1‖) (by ring) ?_
      (by rcases hmn with h | h | h <;> linarith) p1 hx1
    rw [e]
    exact cyc3_le_sorted hj hε z hs h0 h2 h1 h02 h12 _ _ _ _ _ _
  · -- order ℓ2 ≤ ℓ0 ≤ ℓ1
    have hs : ℓ2 + ℓ0 + ℓ1 = 0 := by rw [← hsum]; abel
    have e : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 = cyc3 j ε z ℓ2 ℓ0 ℓ1 s2 s0 s1 v2 v0 v1 :=
      cyc3_rot j ε z ℓ2 ℓ0 ℓ1 s2 s0 s1 v2 v0 v1
    refine fin (a := ℓ2) (c := ℓ1) (P := ‖v2‖ * ‖v0‖ * ‖v1‖) (by ring) ?_
      (by rcases hmn with h | h | h <;> linarith) p1 hx1
    rw [e]
    exact cyc3_le_sorted hj hε z hs h2 h0 h1 h02 h01 _ _ _ _ _ _
  · -- order ℓ1 ≤ ℓ0 ≤ ℓ2
    have hs : ℓ1 + ℓ0 + ℓ2 = 0 := by rw [← hsum]; abel
    have e : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 = cyc3 j ε z ℓ1 ℓ0 ℓ2 s1 s0 s2 v1 v0 v2 :=
      (cyc3_swap j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2).symm
    refine fin (a := ℓ1) (c := ℓ2) (P := ‖v1‖ * ‖v0‖ * ‖v2‖) (by ring) ?_
      (by rcases hmn with h | h | h <;> linarith) p2 hx2
    rw [e]
    exact cyc3_le_sorted hj hε z hs h1 h0 h2 h01 h02 _ _ _ _ _ _
  · -- order ℓ1 ≤ ℓ2 ≤ ℓ0
    have hs : ℓ1 + ℓ2 + ℓ0 = 0 := by rw [← hsum]; abel
    have e : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 = cyc3 j ε z ℓ1 ℓ2 ℓ0 s1 s2 s0 v1 v2 v0 :=
      (cyc3_rot j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2).symm
    refine fin (a := ℓ1) (c := ℓ0) (P := ‖v1‖ * ‖v2‖ * ‖v0‖) (by ring) ?_
      (by rcases hmn with h | h | h <;> linarith) p0 hx0
    rw [e]
    exact cyc3_le_sorted hj hε z hs h1 h2 h0 h12 h02 _ _ _ _ _ _
  all_goals
    -- order ℓ2 ≤ ℓ1 ≤ ℓ0
    have hs : ℓ2 + ℓ1 + ℓ0 = 0 := by rw [← hsum]; abel
    have e : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 = cyc3 j ε z ℓ2 ℓ1 ℓ0 s2 s1 s0 v2 v1 v0 :=
      ((cyc3_swap j ε z ℓ1 ℓ2 ℓ0 s1 s2 s0 v1 v2 v0).trans
        (cyc3_rot j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2)).symm
    refine fin (a := ℓ2) (c := ℓ0) (P := ‖v2‖ * ‖v1‖ * ‖v0‖) (by ring) ?_
      (by rcases hmn with h | h | h <;> linarith) p0 hx0
    rw [e]
    exact cyc3_le_sorted hj hε z hs h2 h1 h0 h12 h01 _ _ _ _ _ _

/-! ### The triad term as a sum of cyclic sums -/

private lemma sobWeight_eq_pow {j : ℕ} {k : Mode} (hk : k ≠ 0) :
    sobWeight j k = absSq k ^ j := by
  have hw : sobWeight j k = absk k ^ (2 * (j : ℝ)) := by simp [sobWeight, hk]
  have e : (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) := by push_cast; ring
  rw [hw, e, Real.rpow_natCast, ← absk_sq, pow_mul]

/-- The weighted multiplier of one rooting is the near mask times the phase times `f_j`. -/
private lemma rooting_coef (j : ℕ) (ε r τ : ℝ) (a b c : Sgn) {p q : Mode} (hk : p + q ≠ 0) :
    (sobWeight j (p + q) : ℂ) * nearCorrM ε r τ a b c p q =
      if NearT a b c p q then
        phaseM τ a b c p q * fres j ε (r * Phi a b c p q) (absSq (p + q)) else 0 := by
  rw [sobWeight_eq_pow hk]
  unfold nearCorrM fres corrSym
  split_ifs
  · push_cast
    ring
  · simp

private lemma phaseM_congr {τ : ℝ} {a b c a' b' c' : Sgn} {p q p' q' : Mode}
    (h : Phi a b c p q = Phi a' b' c' p' q') :
    phaseM τ a b c p q = phaseM τ a' b' c' p' q' := by
  simp only [phaseM, h]

/-- **The triad term on a nondegenerate triad**: the near mask, the phase and `Φ` are common to
the three rootings, which collect into the cyclic sum `cyc3`. -/
theorem nearTriadTerm_eq (j : ℕ) (ε r τ : ℝ) (F G : Field) {p q : Mode} (hp : p ≠ 0)
    (hq : q ≠ 0) (hk : p + q ≠ 0) :
    nearTriadTerm j ε r τ F G (p, q) = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      if NearT a b c p q then
        phaseM τ a b c p q * cyc3 j ε (r * Phi a b c p q) p q (-(p + q)) a b c
          (G p) (F q) (F (-(p + q))) else 0 := by
  set s := -(p + q) with hs
  have e1 : -(q + s) = p := by rw [hs]; abel
  have e2 : -(s + p) = q := by rw [hs]; abel
  have e3 : q + s = -p := by rw [hs]; abel
  have e4 : s + p = -q := by rw [hs]; abel
  have hrho : rho (p, q) = (q, s) := rfl
  have hrho2 : rho (q, s) = (s, p) := Prod.ext rfl e1
  have hm1 : (-p : Mode) ≠ 0 := neg_ne_zero.2 hp
  have hm2 : (-q : Mode) ≠ 0 := neg_ne_zero.2 hq
  have T1 : nearTri j ε r τ G F F (p, q) = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      (if NearT a b c p q then
        phaseM τ a b c p q * fres j ε (r * Phi a b c p q) (absSq s) else 0) *
        tau p q (hel a p (G p)) (hel b q (F q)) (hel c s (F s)) := by
    simp only [nearTri, tripT, Finset.mul_sum, ← mul_assoc, rooting_coef j ε r τ _ _ _ hk, hs]
    simp only [absSq_neg]
  have T2 : nearTri j ε r τ F G F (s, p) = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      (if NearT c a b s p then
        phaseM τ c a b s p * fres j ε (r * Phi c a b s p) (absSq q) else 0) *
        tau s p (hel c s (F s)) (hel a p (G p)) (hel b q (F q)) := by
    have h4 : s + p ≠ 0 := by rw [e4]; exact hm2
    rw [← sum3_rot' fun a b c => (if NearT a b c s p then
        phaseM τ a b c s p * fres j ε (r * Phi a b c s p) (absSq q) else 0) *
        tau s p (hel a s (F s)) (hel b p (G p)) (hel c q (F q))]
    simp only [nearTri, tripT, Finset.mul_sum, ← mul_assoc, rooting_coef j ε r τ _ _ _ h4, e2]
    simp only [e4, absSq_neg]
  have T3 : nearTri j ε r τ F F G (q, s) = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      (if NearT b c a q s then
        phaseM τ b c a q s * fres j ε (r * Phi b c a q s) (absSq p) else 0) *
        tau q s (hel b q (F q)) (hel c s (F s)) (hel a p (G p)) := by
    have h3 : q + s ≠ 0 := by rw [e3]; exact hm1
    rw [← sum3_rot fun a b c => (if NearT a b c q s then
        phaseM τ a b c q s * fres j ε (r * Phi a b c q s) (absSq p) else 0) *
        tau q s (hel a q (F q)) (hel b s (F s)) (hel c p (G p))]
    simp only [nearTri, tripT, Finset.mul_sum, ← mul_assoc, rooting_coef j ε r τ _ _ _ h3, e1]
    simp only [e3, absSq_neg]
  unfold nearTriadTerm
  rw [hrho, hrho2, T1, T2, T3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hP2 : Phi a b c p q = Phi b c a q s := Phi_cyc a b c p q
  have hP3 : Phi b c a q s = Phi c a b s p := by
    have := Phi_cyc b c a q s
    rwa [e1] at this
  have hN2 : NearT a b c p q ↔ NearT b c a q s := nearT_cyc hp hk a b c
  have hN3 : NearT b c a q s ↔ NearT c a b s p := by
    have := nearT_cyc hq (by rw [e3]; exact hm1 : q + s ≠ 0) b c a
    rwa [e1] at this
  have hph2 : phaseM τ a b c p q = phaseM τ b c a q s := phaseM_congr hP2
  have hph3 : phaseM τ b c a q s = phaseM τ c a b s p := phaseM_congr hP3
  rw [← hP3, ← hP2, ← hph3, ← hph2]
  by_cases hN : NearT a b c p q
  · rw [ite_eq_left hN, ite_eq_left (hN3.1 (hN2.1 hN)), ite_eq_left (hN2.1 hN), ite_eq_left hN]
    unfold cyc3
    ring
  · rw [ite_eq_right hN, ite_eq_right fun h => hN (hN2.2 (hN3.2 h)),
      ite_eq_right fun h => hN (hN2.2 h), ite_eq_right hN]
    ring

private lemma nearTriadTerm_degen (j : ℕ) (ε r τ : ℝ) (F G : Field) {p q : Mode}
    (h : p = 0 ∨ q = 0 ∨ p + q = 0) : nearTriadTerm j ε r τ F G (p, q) = 0 := by
  have e : rho (rho (p, q)) = (-(p + q), p) := Prod.ext rfl (by
    change -(q + -(p + q)) = p
    abel)
  have hz : ∀ (X Y Z : Field) (x : Mode × Mode), (x.1 = 0 ∨ x.2 = 0 ∨ x.1 + x.2 = 0) →
      nearTri j ε r τ X Y Z x = 0 := by
    intro X Y Z x hx
    obtain ⟨u, v⟩ := x
    simp only at hx
    have ht : ∀ a b c, tau u v (hel a u (X u)) (hel b v (Y v))
        (hel c (-(u + v)) (Z (-(u + v)))) = 0 := by
      intro a b c
      rcases hx with rfl | rfl | hx
      · rw [hel_zero_mode, tau_zero_left]
      · rw [hel_zero_mode, tau_zero_mid]
      · rw [hx, neg_zero, hel_zero_mode, tau_zero_right]
    simp only [nearTri, tripT, ht, mul_zero, Finset.sum_const_zero]
  unfold nearTriadTerm
  rw [e, hz G F F (p, q) h]
  have h1 : (-(p + q) = 0 ∨ p = 0 ∨ -(p + q) + p = 0) := by
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · right; right
      rw [h]
      abel
    · left
      rw [h, neg_zero]
  have h2 : (q = 0 ∨ -(p + q) = 0 ∨ q + -(p + q) = 0) := by
    rcases h with h | h | h
    · right; right
      rw [h]
      abel
    · exact Or.inl h
    · right; left
      rw [h, neg_zero]
  rw [hz F G F _ h1, show rho (p, q) = (q, -(p + q)) from rfl, hz F F G _ h2]
  simp

/-- **The pointwise triad bound** (report §2 Step 2 summed over helicities): for `mn` above the
shortest leg and `mx` above the longest one,
`|T(p,q)| ≤ Σ_{a,b,c} 𝟏_{near} 13 mn mx^{2j}/√(mx⁴ + r²Φ²) · ‖G_p‖ ‖F_q‖ ‖F_{−(p+q)}‖`. -/
theorem abs_nearTriadTerm_le {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (r τ : ℝ) (F G : Field) (p q : Mode) {mn mx : ℝ}
    (hmn : absk p ≤ mn ∨ absk q ≤ mn ∨ absk (p + q) ≤ mn)
    (hmx : absk p ≤ mx ∧ absk q ≤ mx ∧ absk (p + q) ≤ mx) :
    ‖nearTriadTerm j ε r τ F G (p, q)‖ ≤
      (∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
        if NearT a b c p q then kerB j (r * Phi a b c p q) mn mx else 0) *
        (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖) := by
  have hmn0 : 0 ≤ mn := by
    rcases hmn with h | h | h <;> exact (absk_nonneg _).trans h
  have hmx0 : 0 ≤ mx := (absk_nonneg p).trans hmx.1
  have hP : 0 ≤ ‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖ := by positivity
  have hker : ∀ a b c, 0 ≤ if NearT a b c p q then kerB j (r * Phi a b c p q) mn mx else 0 := by
    intro a b c
    split_ifs
    · exact kerB_nonneg _ _ hmn0 hmx0
    · exact le_rfl
  by_cases hd : p = 0 ∨ q = 0 ∨ p + q = 0
  · rw [nearTriadTerm_degen j ε r τ F G hd, norm_zero]
    exact mul_nonneg (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      Finset.sum_nonneg fun c _ => hker a b c) hP
  simp only [not_or] at hd
  obtain ⟨hp, hq, hk⟩ := hd
  rw [nearTriadTerm_eq j ε r τ F G hp hq hk, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun a _ => ?_
  rw [Finset.sum_mul]
  refine norm_sum_le_of_le _ fun b _ => ?_
  rw [Finset.sum_mul]
  refine norm_sum_le_of_le _ fun c _ => ?_
  split_ifs
  · rw [norm_mul, show ‖phaseM τ a b c p q‖ = 1 from by
      rw [phaseM, mul_comm, Complex.norm_exp_ofReal_mul_I], one_mul]
    refine cyc3_le hj hε _ (by abel) hp hq (neg_ne_zero.2 hk) _ _ _ _ _ _ ?_ ?_
    · rwa [absk_neg]
    · rwa [absk_neg]
  · simp

end OVNS.Quant

end
