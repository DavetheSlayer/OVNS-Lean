import OddViscousNS.Closed.Row.Moment
import OddViscousNS.Closed.Row.Pair

/-!
# The pointwise steps of the tail lemma

Off the lens both legs are high, so `W = ω_C`, the metric is affine, and with `e = h_C - b`,
`δ = h_C - a C - b`, one has `G₁ ≤ a²(A³+B³)` (if `0 ≤ e ≤ 2a min(A,B)`) and
`G₂ = (A-B)²(δ² + a² A B)`.  This gives `pterm_off`.  `mul_four_le` is the AM-GM plus Bessel step
`4 (p·k)² (p·c)² ≤ A ((p·k)² |c|² + C (p·c)²)` for `c ⊥ k`.
-/

open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

/-- `ω_C = 3λ_C/(2+λ_C)`. -/
def om (C : ℕ) : ℝ := 3 * lamW C / (2 + lamW C)

lemma Wk_high (k p : Mode) (hA : 120 < nsq p) (hB : 120 < nsq (k - p)) :
    Wk lamW k p = om (nsq k) := by
  rw [Wk, lamW_gt hA, lamW_gt hB, om]
  congr 1
  ring

/-- `(p·c'')²/A³`. -/
def t1 (k : Mode) (c : R3) (p : Mode) : ℝ := dR p (crR k c) ^ 2 * (absSq p)⁻¹ ^ 3

/-- `(A-B)²(p·c)²/A⁴`. -/
def t2 (k : Mode) (c : R3) (p : Mode) : ℝ :=
  (absSq p - absSq (k - p)) ^ 2 * dR p c ^ 2 * (absSq p)⁻¹ ^ 4

lemma t1_nonneg (k c p) : 0 ≤ t1 k c p := by
  have := absSq_nonneg' p
  unfold t1; positivity

lemma t2_nonneg (k c p) : 0 ≤ t2 k c p := by
  have := absSq_nonneg' p
  unfold t2; positivity

/-- The real-variable bound behind `pterm_off`. -/
lemma off_real (a b A B e δ ε hC W T P L : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hA : 0 < A) (hB : 0 < B)
    (he0 : 0 ≤ e) (he1 : e ≤ 2 * a * A) (he2 : e ≤ 2 * a * B) (hε : 0 ≤ ε)
    (hδ : δ ^ 2 ≤ ε * a ^ 2 * (A * B)) (hT : 0 ≤ T) (hP : 0 ≤ P)
    (hL : L = (A - B) * δ) (hh : hC = e + b) :
    W ^ 2 * (B * (hC - (a * B + b)) ^ 2 + A * ((a * A + b) - hC) ^ 2) /
        (A ^ 2 * B ^ 2 * (a * A + b) * (a * B + b)) * T
      + W ^ 2 * (L ^ 2 + A * B * ((a * B + b) - (a * A + b)) ^ 2) /
        (A ^ 2 * B ^ 2 * (a * A + b) * (a * B + b)) * P ≤
    W ^ 2 * (T * A⁻¹ ^ 3 + T * B⁻¹ ^ 3 + (1 + ε) / 2 *
      ((A - B) ^ 2 * P * A⁻¹ ^ 4 + (A - B) ^ 2 * P * B⁻¹ ^ 4)) := by
  have hha : a * A ≤ a * A + b := by linarith
  have hhb : a * B ≤ a * B + b := by linarith
  have hprod : a ^ 2 * (A * B) ≤ (a * A + b) * (a * B + b) := by
    have := mul_le_mul hha hhb (by positivity) (by positivity)
    linarith
  have hdpos : 0 < A ^ 2 * B ^ 2 * (a * A + b) * (a * B + b) := by positivity
  -- the first coefficient
  have hG1 : B * (hC - (a * B + b)) ^ 2 + A * ((a * A + b) - hC) ^ 2 ≤ a ^ 2 * (A ^ 3 + B ^ 3) := by
    subst hh
    have h1 : 0 ≤ e * (A * (2 * a * A - e) + B * (2 * a * B - e)) := by
      have := sub_nonneg.2 he1
      have := sub_nonneg.2 he2
      positivity
    nlinarith
  have h1 : (B * (hC - (a * B + b)) ^ 2 + A * ((a * A + b) - hC) ^ 2) /
      (A ^ 2 * B ^ 2 * (a * A + b) * (a * B + b)) ≤ A⁻¹ ^ 3 + B⁻¹ ^ 3 := by
    rw [div_le_iff₀ hdpos]
    have e1 : (A⁻¹ ^ 3 + B⁻¹ ^ 3) * (A ^ 2 * B ^ 2 * (a * A + b) * (a * B + b)) =
        (A ^ 3 + B ^ 3) * ((a * A + b) * (a * B + b)) / (A * B) := by
      field_simp
      ring
    rw [e1, le_div_iff₀ (by positivity)]
    have h2 : (B * (hC - (a * B + b)) ^ 2 + A * ((a * A + b) - hC) ^ 2) * (A * B) ≤
        a ^ 2 * (A ^ 3 + B ^ 3) * (A * B) := mul_le_mul_of_nonneg_right hG1 (by positivity)
    have h3 : (A ^ 3 + B ^ 3) * (a ^ 2 * (A * B)) ≤ (A ^ 3 + B ^ 3) * ((a * A + b) * (a * B + b)) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    linarith
  -- the second coefficient
  have hG2 : L ^ 2 + A * B * ((a * B + b) - (a * A + b)) ^ 2 ≤
      (1 + ε) * (A - B) ^ 2 * (a ^ 2 * (A * B)) := by
    subst hL
    have e2 : ((A - B) * δ) ^ 2 + A * B * ((a * B + b) - (a * A + b)) ^ 2 =
        (A - B) ^ 2 * (δ ^ 2 + a ^ 2 * (A * B)) := by ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left hδ (sq_nonneg (A - B))
    nlinarith
  have h2 : (L ^ 2 + A * B * ((a * B + b) - (a * A + b)) ^ 2) /
      (A ^ 2 * B ^ 2 * (a * A + b) * (a * B + b)) ≤ (1 + ε) * (A - B) ^ 2 * (A⁻¹ ^ 2 * B⁻¹ ^ 2) := by
    rw [div_le_iff₀ hdpos]
    have e1 : (1 + ε) * (A - B) ^ 2 * (A⁻¹ ^ 2 * B⁻¹ ^ 2) *
        (A ^ 2 * B ^ 2 * (a * A + b) * (a * B + b)) =
        (1 + ε) * (A - B) ^ 2 * ((a * A + b) * (a * B + b)) := by
      field_simp
    rw [e1]
    exact hG2.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
  have h3 : A⁻¹ ^ 2 * B⁻¹ ^ 2 ≤ (A⁻¹ ^ 4 + B⁻¹ ^ 4) / 2 := by
    nlinarith [sq_nonneg (A⁻¹ ^ 2 - B⁻¹ ^ 2)]
  have hW := sq_nonneg W
  calc W ^ 2 * (B * (hC - (a * B + b)) ^ 2 + A * ((a * A + b) - hC) ^ 2) /
        (A ^ 2 * B ^ 2 * (a * A + b) * (a * B + b)) * T
      + W ^ 2 * (L ^ 2 + A * B * ((a * B + b) - (a * A + b)) ^ 2) /
        (A ^ 2 * B ^ 2 * (a * A + b) * (a * B + b)) * P
      = W ^ 2 * ((B * (hC - (a * B + b)) ^ 2 + A * ((a * A + b) - hC) ^ 2) /
        (A ^ 2 * B ^ 2 * (a * A + b) * (a * B + b)) * T
      + (L ^ 2 + A * B * ((a * B + b) - (a * A + b)) ^ 2) /
        (A ^ 2 * B ^ 2 * (a * A + b) * (a * B + b)) * P) := by ring
    _ ≤ W ^ 2 * ((A⁻¹ ^ 3 + B⁻¹ ^ 3) * T
        + ((1 + ε) * (A - B) ^ 2 * ((A⁻¹ ^ 4 + B⁻¹ ^ 4) / 2)) * P) := by
          refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right h1 hT)
            (mul_le_mul_of_nonneg_right (h2.trans ?_) hP)) hW
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-- The pointwise bound off the lens. -/
theorem pterm_off (k p : Mode) (c : R3) (hc : dR k c = 0) (ε : ℝ)
    (hA : 120 < nsq p) (hB : 120 < nsq (k - p))
    (he0 : 0 ≤ hm k - 117 / 500)
    (he1 : hm k - 117 / 500 ≤ 2 * (29 / 100) * absSq p)
    (he2 : hm k - 117 / 500 ≤ 2 * (29 / 100) * absSq (k - p)) (hε : 0 ≤ ε)
    (hδ : (hm k - 29 / 100 * absSq k - 117 / 500) ^ 2 ≤
      ε * (29 / 100) ^ 2 * (absSq p * absSq (k - p))) :
    pterm k c p ≤ om (nsq k) ^ 2 * (t1 k c p + t1 k c (k - p) +
      (1 + ε) / 2 * (t2 k c p + t2 k c (k - p))) := by
  have hAe : (nsq p : ℝ) = absSq p := nsq_cast p
  have hBe : (nsq (k - p) : ℝ) = absSq (k - p) := nsq_cast (k - p)
  have hA0 : 0 < absSq p := by
    rw [← hAe]; exact_mod_cast (show 0 < nsq p by omega)
  have hB0 : 0 < absSq (k - p) := by
    rw [← hBe]; exact_mod_cast (show 0 < nsq (k - p) by omega)
  have hhA : hm p = 29 / 100 * absSq p + 117 / 500 := by
    rw [hm, hmet_affine (by omega), hAe]; ring
  have hhB : hm (k - p) = 29 / 100 * absSq (k - p) + 117 / 500 := by
    rw [hm, hmet_affine (by omega), hBe]; ring
  have hL : Lst k p = (absSq p - absSq (k - p)) * (hm k - 29 / 100 * absSq k - 117 / 500) := by
    simp only [Lst, hhA, hhB]; ring
  have := off_real (29 / 100) (117 / 500) (absSq p) (absSq (k - p)) (hm k - 117 / 500)
    (hm k - 29 / 100 * absSq k - 117 / 500) ε (hm k) (om (nsq k)) (dR p (crR k c) ^ 2)
    (dR p c ^ 2) (Lst k p) (by norm_num) (by norm_num) hA0 hB0 he0 he1 he2 hε hδ (sq_nonneg _)
    (sq_nonneg _) hL (by ring)
  have hpterm : pterm k c p = om (nsq k) ^ 2 * (absSq (k - p) * (hm k - (29 / 100 * absSq (k - p)
        + 117 / 500)) ^ 2 + absSq p * ((29 / 100 * absSq p + 117 / 500) - hm k) ^ 2) /
        (absSq p ^ 2 * absSq (k - p) ^ 2 * (29 / 100 * absSq p + 117 / 500)
          * (29 / 100 * absSq (k - p) + 117 / 500)) * dR p (crR k c) ^ 2
      + om (nsq k) ^ 2 * (Lst k p ^ 2 + absSq p * absSq (k - p) *
        ((29 / 100 * absSq (k - p) + 117 / 500) - (29 / 100 * absSq p + 117 / 500)) ^ 2) /
        (absSq p ^ 2 * absSq (k - p) ^ 2 * (29 / 100 * absSq p + 117 / 500)
          * (29 / 100 * absSq (k - p) + 117 / 500)) * dR p c ^ 2 := by
    rw [pterm, w1, w2, Wk_high k p hA hB, hhA, hhB]
  rw [hpterm]
  refine this.trans (le_of_eq ?_)
  have e1 : t1 k c (k - p) = dR p (crR k c) ^ 2 * (absSq (k - p))⁻¹ ^ 3 := by
    rw [t1, dR_symm_sq k p _ (dR_crR_self k c)]
  have e2 : t2 k c (k - p) = (absSq p - absSq (k - p)) ^ 2 * dR p c ^ 2 * (absSq (k - p))⁻¹ ^ 4 := by
    rw [t2, dR_symm_sq k p _ hc, sub_sub_self']; ring
  rw [e1, e2, t1, t2]

/-- AM-GM plus Bessel. -/
theorem mul_four_le (k p : Mode) (hk : k ≠ 0) (c : R3) (hc : dR k c = 0) :
    4 * dZ p k ^ 2 * dR p c ^ 2 ≤ absSq p * (dZ p k ^ 2 * nR c + absSq k * dR p c ^ 2) := by
  have hC : 0 < absSq k := lt_of_lt_of_le one_pos (one_le_absSq hk)
  have hpar := parseval p k c hc
  have hn := nR_nonneg c
  rcases hn.eq_or_lt with h0 | h0
  · -- `c = 0`
    have hc0 : ∀ i, c i = 0 := by
      intro i
      have : c i ^ 2 ≤ nR c := by
        unfold nR
        exact Finset.single_le_sum (f := fun j => c j ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)
      rw [← h0] at this
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg _))
    have : dR p c = 0 := by simp [dR, hc0]
    rw [this]; simp only [← h0]; norm_num
  · have hT := sq_nonneg (dR p (crR k c))
    set y2 := dZ p k ^ 2
    set P := dR p c ^ 2
    set A := absSq p
    set C := absSq k
    set n := nR c
    have hy : 0 ≤ y2 := sq_nonneg _
    have hPp : 0 ≤ P := sq_nonneg _
    have hA : 0 ≤ A := absSq_nonneg' p
    have hZ : y2 * n + C * P ≤ A * C * n := by linarith
    have hZ0 : 0 ≤ y2 * n + C * P := by positivity
    have h1 : 4 * (y2 * n) * (C * P) ≤ (y2 * n + C * P) ^ 2 := by
      nlinarith [sq_nonneg (y2 * n - C * P)]
    have h2 : (y2 * n + C * P) ^ 2 ≤ (y2 * n + C * P) * (A * C * n) := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hZ hZ0
    have h3 : (C * n) * (4 * y2 * P) ≤ (C * n) * (A * (y2 * n + C * P)) := by
      calc (C * n) * (4 * y2 * P) = 4 * (y2 * n) * (C * P) := by ring
        _ ≤ (y2 * n + C * P) * (A * C * n) := h1.trans h2
        _ = _ := by ring
    exact le_of_mul_le_mul_left h3 (by positivity)

end Row
end OVNS
