import OddViscousNS.Closed.GTable

/-!
# Closed form of the row quadratic form

For real `c ⊥ k`, with `A = |p|²`, `B = |k-p|²`, `C = |k|²`, `c'' = k × c`:

`Wk² gramQ p (k-p) k c / (A h_A B h_B) = w1 k p (p·c'')² + w2 k p (p·c)²`,

with `w1 = W² (B d₁² + A d₂²) / (A²B²h_Ah_B)` and `w2 = W² (L*² + A B d₃²) / (A²B²h_Ah_B)`.  A complex
`c = a + i b` splits into `a` and `b`.  All reports' normalizations are checked here against the
definition: there is no factor `36` in `gramQ`.
-/

open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS
namespace Row

/-- Real 3-vectors. -/
abbrev R3 := Fin 3 → ℝ

/-- `p · v` for a lattice vector `p` and a real vector `v`. -/
def dR (p : Mode) (v : R3) : ℝ := ∑ i, (p i : ℝ) * v i

/-- `|v|²` for a real vector. -/
def nR (v : R3) : ℝ := ∑ i, v i ^ 2

/-- `p · k` for lattice vectors. -/
def dZ (p k : Mode) : ℝ := ∑ i, (p i : ℝ) * (k i : ℝ)

/-- `k × v` for a lattice vector `k` and a real vector `v`. -/
def crR (k : Mode) (v : R3) : R3 :=
  ![(k 1 : ℝ) * v 2 - (k 2 : ℝ) * v 1, (k 2 : ℝ) * v 0 - (k 0 : ℝ) * v 2,
    (k 0 : ℝ) * v 1 - (k 1 : ℝ) * v 0]

/-- The coefficient of `(p·c'')²`. -/
def w1 (k p : Mode) : ℝ :=
  Wk lamW k p ^ 2 * (absSq (k - p) * (hm k - hm (k - p)) ^ 2 + absSq p * (hm p - hm k) ^ 2) /
    (absSq p ^ 2 * absSq (k - p) ^ 2 * hm p * hm (k - p))

/-- `L* = A d₁ + B d₂ + C d₃`. -/
def Lst (k p : Mode) : ℝ :=
  absSq p * (hm k - hm (k - p)) + absSq (k - p) * (hm p - hm k) + absSq k * (hm (k - p) - hm p)

/-- The coefficient of `(p·c)²`. -/
def w2 (k p : Mode) : ℝ :=
  Wk lamW k p ^ 2 * (Lst k p ^ 2 + absSq p * absSq (k - p) * (hm (k - p) - hm p) ^ 2) /
    (absSq p ^ 2 * absSq (k - p) ^ 2 * hm p * hm (k - p))

/-- The summand of the row form for real `c`. -/
def pterm (k : Mode) (c : R3) (p : Mode) : ℝ :=
  w1 k p * dR p (crR k c) ^ 2 + w2 k p * dR p c ^ 2

/-- The real row form. -/
def rowR (k : Mode) (c : R3) : ℝ≥0∞ := ∑' p, ENNReal.ofReal (pterm k c p)

lemma absSq_nonneg' (k : Mode) : 0 ≤ absSq k := by
  unfold absSq; positivity

lemma hm_nonneg (k : Mode) : 0 ≤ hm k := by
  unfold hm hmet
  split_ifs
  · exact le_rfl
  · positivity
  · positivity

lemma w1_nonneg (k p : Mode) : 0 ≤ w1 k p := by
  have h1 := absSq_nonneg' p
  have h2 := absSq_nonneg' (k - p)
  have h3 := hm_nonneg p
  have h4 := hm_nonneg (k - p)
  unfold w1; positivity

lemma w2_nonneg (k p : Mode) : 0 ≤ w2 k p := by
  have h1 := absSq_nonneg' p
  have h2 := absSq_nonneg' (k - p)
  have h3 := hm_nonneg p
  have h4 := hm_nonneg (k - p)
  unfold w2; positivity

lemma pterm_nonneg (k : Mode) (c : R3) (p : Mode) : 0 ≤ pterm k c p :=
  add_nonneg (mul_nonneg (w1_nonneg k p) (sq_nonneg _)) (mul_nonneg (w2_nonneg k p) (sq_nonneg _))

/-- `absSq p ≠ 0` for `p ≠ 0`. -/
lemma absSq_ne_zero {p : Mode} (hp : p ≠ 0) : absSq p ≠ 0 := by
  have := one_le_absSq hp
  linarith

lemma absSq_zero : absSq (0 : Mode) = 0 := by simp [absSq]

private lemma dotV_cross (p k : Mode) (c : V3) :
    dotV (cross (modeVec p) (modeVec k)) c =
      ((dR p (crR k fun i => (c i).re) : ℝ) : ℂ)
        + ((dR p (crR k fun i => (c i).im) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
  simp [dotV, cross, modeVec, dR, crR, Fin.sum_univ_three] <;> ring

private lemma dotV_N (p k : Mode) (c : V3) (hc : dotM c k = 0) :
    dotV (cross (modeVec k) (cross (modeVec p) (modeVec k))) c =
      ((absSq k : ℝ) : ℂ) * (((dR p fun i => (c i).re : ℝ) : ℂ)
        + ((dR p fun i => (c i).im : ℝ) : ℂ) * Complex.I) := by
  have hre : (dotM c k).re = 0 := by rw [hc]; rfl
  have him : (dotM c k).im = 0 := by rw [hc]; rfl
  simp [dotM, Fin.sum_univ_three] at hre him
  have hC : ((absSq k : ℝ) : ℂ) = (k 0 : ℂ) * k 0 + (k 1 : ℂ) * k 1 + (k 2 : ℂ) * k 2 := by
    simp [absSq, Fin.sum_univ_three]; ring
  rw [hC]
  apply Complex.ext
  · simp [dotV, cross, modeVec, dR, Fin.sum_univ_three]
    linear_combination (-(p 0 : ℝ) * k 0 - (p 1 : ℝ) * k 1 - (p 2 : ℝ) * k 2) * hre
  · simp [dotV, cross, modeVec, dR, Fin.sum_univ_three]
    linear_combination (-(p 0 : ℝ) * k 0 - (p 1 : ℝ) * k 1 - (p 2 : ℝ) * k 2) * him

private lemma normsq_ri (x y : ℝ) :
    ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- The summand of `rowQ` splits over the real and imaginary parts of `c`. -/
theorem rowQ_term (k p : Mode) (hk : k ≠ 0) (c : V3) (hc : dotM c k = 0) :
    Wk lamW k p ^ 2 * gramQ p (k - p) k c / (absSq p * hm p * absSq (k - p) * hm (k - p)) =
      pterm k (fun i => (c i).re) p + pterm k (fun i => (c i).im) p := by
  by_cases hp : p = 0
  · subst hp
    simp [gramQ, pterm, w1, w2, absSq_zero]
  by_cases hl : k - p = 0
  · simp [gramQ, pterm, w1, w2, absSq_zero, hl, hp]
  have hA := absSq_ne_zero hp
  have hB := absSq_ne_zero hl
  have hC := absSq_ne_zero hk
  have hnot : ¬ (p = 0 ∨ k - p = 0 ∨ k = 0) := by simp [hp, hk, hl]
  set a : R3 := fun i => (c i).re with ha
  set b : R3 := fun i => (c i).im with hb
  have e1 : ‖dotV (cross (modeVec p) (modeVec k)) c‖ ^ 2 =
      dR p (crR k a) ^ 2 + dR p (crR k b) ^ 2 := by
    rw [dotV_cross]; exact normsq_ri _ _
  have e2 : ‖dotV (cross (modeVec k) (cross (modeVec p) (modeVec k))) c‖ ^ 2 =
      absSq k ^ 2 * (dR p a ^ 2 + dR p b ^ 2) := by
    rw [dotV_N p k c hc, norm_mul, mul_pow, normsq_ri]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (absSq_nonneg' k), a, b]
  unfold gramQ
  simp only [hnot, ↓reduceIte, e1, e2]
  simp only [pterm, w1, w2, Lst]
  rcases eq_or_ne (hm p) 0 with h0 | h0
  · simp [h0]
  rcases eq_or_ne (hm (k - p)) 0 with h1 | h1
  · simp [h1]
  field_simp
  ring

/-- `rowQ` splits over the real and imaginary parts of `c`. -/
theorem rowQ_eq (k : Mode) (hk : k ≠ 0) (c : V3) (hc : dotM c k = 0) :
    rowQ k c = rowR k (fun i => (c i).re) + rowR k (fun i => (c i).im) := by
  unfold rowQ rowR
  rw [← tsum_add]
  refine tsum_congr fun p => ?_
  rw [rowQ_term k p hk c hc, ENNReal.ofReal_add (pterm_nonneg _ _ _) (pterm_nonneg _ _ _)]

/-- `‖c‖² = |re c|² + |im c|²`. -/
lemma norm_sq_split (c : V3) :
    ‖c‖ ^ 2 = nR (fun i => (c i).re) + nR (fun i => (c i).im) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [nR, Complex.sq_norm, Complex.normSq_apply, Fin.sum_univ_three]
  ring

/-- The real parts of `c ⊥ k` are orthogonal to `k`. -/
lemma dR_re (k : Mode) (c : V3) (hc : dotM c k = 0) : dR k (fun i => (c i).re) = 0 := by
  have hre : (dotM c k).re = 0 := by rw [hc]; rfl
  simp [dotM, Fin.sum_univ_three] at hre
  simp [dR, Fin.sum_univ_three]
  linarith

lemma dR_im (k : Mode) (c : V3) (hc : dotM c k = 0) : dR k (fun i => (c i).im) = 0 := by
  have him : (dotM c k).im = 0 := by rw [hc]; rfl
  simp [dotM, Fin.sum_univ_three] at him
  simp [dR, Fin.sum_univ_three]
  linarith

/-- The real form of `RowBound`. -/
def RealRow (g : ℕ → ℝ) : Prop :=
  ∀ k : Mode, k ≠ 0 → ∀ c : R3, dR k c = 0 →
    rowR k c ≤ ENNReal.ofReal (36 * g (nsq k) * hm k * nR c)

lemma nR_nonneg (c : R3) : 0 ≤ nR c := by unfold nR; positivity

/-- The complex statement follows from the real one. -/
theorem rowBound_of_real {g : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j) (h : RealRow g) : RowBound g := by
  intro k hk c hc
  rw [rowQ_eq k hk c hc, norm_sq_split]
  refine (add_le_add (h k hk _ (dR_re k c hc)) (h k hk _ (dR_im k c hc))).trans_eq ?_
  have h0 : 0 ≤ 36 * g (nsq k) * hm k := by
    have := hg (nsq k); have := hm_nonneg k; positivity
  rw [← ENNReal.ofReal_add (mul_nonneg h0 (nR_nonneg _)) (mul_nonneg h0 (nR_nonneg _))]
  congr 1
  ring

/-! ### Elementary vector identities -/

lemma dR_add (p q : Mode) (v : R3) : dR (p + q) v = dR p v + dR q v := by
  simp only [dR, Fin.sum_univ_three, Pi.add_apply, Int.cast_add]; ring

lemma dR_sub (p q : Mode) (v : R3) : dR (p - q) v = dR p v - dR q v := by
  simp only [dR, Fin.sum_univ_three, Pi.sub_apply, Int.cast_sub]; ring

lemma dR_neg (p : Mode) (v : R3) : dR (-p) v = - dR p v := by
  simp only [dR, Fin.sum_univ_three, Pi.neg_apply, Int.cast_neg]; ring

/-- `|k × c|² = |k|²|c|²` for `c ⊥ k`. -/
lemma nR_crR (k : Mode) (c : R3) (hc : dR k c = 0) : nR (crR k c) = absSq k * nR c := by
  simp only [dR, Fin.sum_univ_three] at hc
  simp [nR, crR, absSq, Fin.sum_univ_three]
  linear_combination (-(k 0 : ℝ) * c 0 - (k 1 : ℝ) * c 1 - (k 2 : ℝ) * c 2) * hc

/-- `k ⊥ k × c`. -/
lemma dR_crR_self (k : Mode) (c : R3) : dR k (crR k c) = 0 := by
  simp [dR, crR, Fin.sum_univ_three]; ring

/-- Parseval in the orthogonal frame `k, c, k × c`. -/
lemma parseval (p k : Mode) (c : R3) (hc : dR k c = 0) :
    dR p (crR k c) ^ 2 + absSq k * dR p c ^ 2 + dZ p k ^ 2 * nR c = absSq p * absSq k * nR c := by
  simp only [dR, Fin.sum_univ_three] at hc
  simp [dR, dZ, nR, crR, absSq, Fin.sum_univ_three]
  linear_combination (2 * (((p 0 : ℝ) * k 0 + (p 1 : ℝ) * k 1 + (p 2 : ℝ) * k 2) *
      ((p 0 : ℝ) * c 0 + (p 1 : ℝ) * c 1 + (p 2 : ℝ) * c 2))
      - ((p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2 + (p 2 : ℝ) ^ 2) * ((k 0 : ℝ) * c 0 + (k 1 : ℝ) * c 1 + (k 2 : ℝ) * c 2)) * hc

/-- `dZ` in terms of squared norms. -/
lemma absSq_sub (k p : Mode) : absSq (k - p) = absSq k - 2 * dZ p k + absSq p := by
  simp only [absSq, dZ, Fin.sum_univ_three, Pi.sub_apply, Int.cast_sub]; ring

lemma sub_sub_self' (k p : Mode) : k - (k - p) = p := by simp

lemma Wk_symm (k p : Mode) : Wk lamW k (k - p) = Wk lamW k p := by
  unfold Wk
  rw [sub_sub_self']
  congr 1
  ring

lemma w1_symm (k p : Mode) : w1 k (k - p) = w1 k p := by
  unfold w1
  rw [Wk_symm, sub_sub_self']
  congr 1
  · ring
  · ring

lemma w2_symm (k p : Mode) : w2 k (k - p) = w2 k p := by
  unfold w2 Lst
  rw [Wk_symm, sub_sub_self']
  congr 1
  · ring
  · ring

/-- The pair symmetry `p ↔ k - p`. -/
lemma pterm_symm (k p : Mode) (c : R3) (hc : dR k c = 0) :
    pterm k c (k - p) = pterm k c p := by
  unfold pterm
  rw [w1_symm, w2_symm, dR_sub, dR_sub, dR_crR_self, hc]
  ring

/-- `(l·v)² = (p·v)²` for `v ⊥ k`. -/
lemma dR_symm_sq (k p : Mode) (v : R3) (hv : dR k v = 0) : dR (k - p) v ^ 2 = dR p v ^ 2 := by
  rw [dR_sub, hv]; ring

end Row
end OVNS
