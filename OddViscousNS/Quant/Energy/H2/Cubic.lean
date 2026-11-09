import OddViscousNS.Quant.Energy.H2.Identity

/-!
# E8: the proper remainders of the weight-two cubic (roles 16, 17)

`cubicE_two_static_le_proved`, `cubicHeat2_le_proved`: the two bounds which `Bounds.lean` uses, for
real fast `F`,
* `|E⁰₂| ≤ cStat2 (P(q) + q^{−1/2}) ‖F‖₂³` (`F ∈ H²`),
* `|E₂_heat| ≤ cHeat2 (P(q) + q^{−1/2}) ‖F‖₂ ‖F‖₃²` (`F ∈ H³`).

## The route
Split `corrM = nearCorrM + farCorrM` on the series of `pair 2 F (Qm corrM X Y)`.

*Near.*  On `0 < |Φ| < 1` the absolute value is not enough at weight two (the output on the longest
leg costs `K/m`), so the three rootings are collected.  `E⁰₂` is `⅓` of the triad sum of
`nearTriadTerm 2` (`rho`), and `triad_cyclic_le` at `j = 2` gives `13 m K⁴/D_K`, the same input as
role 31.  The heat is `(Σ − x_c) f₂(x_c) = Σ f₂(x_c) − f₃(x_c)` at each rooting (`Σ` the sum of the
three `|ℓ|²`), which is `Σ · nearTriadTerm 2 − nearTriadTerm 3`.  Section A is `triad_cyclic_le` at
`j = 3`, which `Native/Kernel.lean` does not cover: `26 m K⁶/D_K`.
With the slots `(H², H², H²)`, resp. `H³` on the two large legs and `H²` on the small one, the
kernel left is `≤ c/(m D_K)`, the proper kernel `propKer = K nearKerSum` whose squared moment is
`momP` (`kerB_le_nearKerSum`, `moment_cauchy`).

*Far.*  On `|Φ| ≥ 1`: `|k| ‖m‖ ≤ q^{−1/2}`, no cancellation (Section F).

## Provenance
The slots are those of the coordinator's note and of the static and heat statements of
`H1/Bounds.lean` (Table quant-fixed "Complete proper static/heats, FAR and one-zero: `3v`").  The
box sums and the regions (Sections B, C) are copies of the private lemmas of `H1/Cubic.lean`, which
is owned by another agent and is not imported.  Sections A and D–G are new.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.H2

/-! ### A. The cyclic kernel at `j = 3` -/

/-- `f₃(s) − f₃(t) = (s − t)[εst(s + t) + iz(s² + st + t²)]/[(εs + iz)(εt + iz)]` (the identity
of `fres_two_sub` one degree up). -/
theorem fres_three_sub {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) (z : ℝ) :
    fres 3 ε z s - fres 3 ε z t =
      (((s : ℂ) - t) * (((ε * s * t * (s + t) : ℝ) : ℂ) +
        ((z * (s ^ 2 + s * t + t ^ 2) : ℝ) : ℂ) * Complex.I)) / (den ε z s * den ε z t) := by
  rw [fres_eq_div, fres_eq_div, div_sub_div _ _ (den_ne_zero hε hs z) (den_ne_zero hε ht z)]
  congr 1
  simp only [den]
  push_cast
  ring

private lemma norm_ofReal_sub' {s t : ℝ} (hst : s ≤ t) : ‖(s : ℂ) - t‖ = t - s := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith),
    neg_sub]

/-- `|f₃(s) − f₃(t)| ≤ 5t²(t − s)/√(t² + z²)` for `0 < s ≤ t`. -/
theorem norm_fres_three_sub_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (z : ℝ) :
    ‖fres 3 ε z s - fres 3 ε z t‖ ≤ 5 * t ^ 2 * (t - s) / Real.sqrt (t ^ 2 + z ^ 2) := by
  have ht : 0 < t := hs.trans_le hst
  have hA : 0 < Real.sqrt (s ^ 2 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hB : 0 < Real.sqrt (t ^ 2 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsA : s ≤ Real.sqrt (s ^ 2 + z ^ 2) := by
    rw [Real.le_sqrt hs.le (by positivity)]
    nlinarith [sq_nonneg z]
  have hzA : |z| ≤ Real.sqrt (s ^ 2 + z ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])
  set w := s ^ 2 + s * t + t ^ 2 with hw
  have hw0 : 0 ≤ w := by positivity
  set A := Real.sqrt (s ^ 2 + z ^ 2) with hAdef
  have hnum : ‖((ε * s * t * (s + t) : ℝ) : ℂ) + ((z * w : ℝ) : ℂ) * Complex.I‖ ≤
      5 * A * t ^ 2 := by
    rw [Complex.norm_add_mul_I]
    have h1 : (ε * s * t * (s + t)) ^ 2 = (s * t * (s + t)) ^ 2 := by
      rcases hε with rfl | rfl <;> ring
    rw [h1]
    have hz2 : |z| ^ 2 * w ^ 2 = z ^ 2 * w ^ 2 := by rw [sq_abs]
    have hprod : 0 ≤ s * t * (s + t) * (|z| * w) := by positivity
    calc Real.sqrt ((s * t * (s + t)) ^ 2 + (z * w) ^ 2) ≤ s * t * (s + t) + |z| * w := by
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith [hz2, hprod]
      _ ≤ A * t * (s + t) + A * w := by gcongr
      _ = A * (t * (s + t) + w) := by ring
      _ ≤ A * (5 * t ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hA.le
          rw [hw]
          nlinarith [mul_le_mul_of_nonneg_left hst ht.le, mul_le_mul_of_nonneg_left hst hs.le]
      _ = 5 * A * t ^ 2 := by ring
  rw [fres_three_sub hε hs.ne' ht.ne', norm_div, norm_mul, norm_mul, norm_den hε, norm_den hε,
    norm_ofReal_sub' hst]
  have hts : 0 ≤ t - s := by linarith
  rw [div_le_div_iff₀ (by positivity) hB]
  nlinarith [mul_le_mul_of_nonneg_right hnum (mul_nonneg hts hB.le)]

/-- Small/middle legs, `j = 3`: `|f₃(m²) − f₃(B²)| D_K ≤ 20K⁶`. -/
theorem diff_small_three {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B)
    (hBK : B ≤ K) (htri : K ≤ B + m) :
    ‖fres 3 ε z (m ^ 2) - fres 3 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2) ≤ 20 * K ^ 6 := by
  have hB : 0 < B := hm.trans_le hmB
  have h1 := norm_fres_three_sub_le hε (s := m ^ 2) (t := B ^ 2) (by positivity)
    (pow_le_pow_left₀ hm.le hmB 2) z
  have h2 := sqrt_quartic_le (B := B) (K := K) (by linarith) (by linarith) z
  have e : (B ^ 2) ^ 2 = B ^ 4 := by ring
  rw [e] at h1
  have hpos : 0 < Real.sqrt (B ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hmB2 : m ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hm.le hmB 2
  have hB6 : B ^ 6 ≤ K ^ 6 := pow_le_pow_left₀ hB.le hBK 6
  have hd : 0 ≤ 5 * B ^ 4 * (B ^ 2 - m ^ 2) := mul_nonneg (by positivity) (by linarith)
  calc ‖fres 3 ε z (m ^ 2) - fres 3 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2)
      ≤ 5 * B ^ 4 * (B ^ 2 - m ^ 2) / Real.sqrt (B ^ 4 + z ^ 2) *
          (4 * Real.sqrt (B ^ 4 + z ^ 2)) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (div_nonneg hd hpos.le)
    _ = 20 * (B ^ 4 * (B ^ 2 - m ^ 2)) := by field_simp; ring
    _ ≤ 20 * K ^ 6 := by
        have : B ^ 4 * (B ^ 2 - m ^ 2) ≤ B ^ 4 * B ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg m]) (by positivity)
        nlinarith [hB6]

/-- Large/middle legs, `j = 3`: `|f₃(K²) − f₃(B²)| D_K ≤ 10mK⁵`. -/
theorem diff_large_three {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B)
    (hBK : B ≤ K) (htri : K ≤ B + m) :
    ‖fres 3 ε z (K ^ 2) - fres 3 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2) ≤ 10 * m * K ^ 5 := by
  have hB : 0 < B := hm.trans_le hmB
  have h1 := norm_fres_three_sub_le hε (s := B ^ 2) (t := K ^ 2) (by positivity)
    (pow_le_pow_left₀ hB.le hBK 2) z
  have e : (K ^ 2) ^ 2 = K ^ 4 := by ring
  rw [e, ← norm_sub_rev] at h1
  have hK : 0 < K := hB.trans_le hBK
  have hpos : 0 < Real.sqrt (K ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hKB : K ^ 2 - B ^ 2 ≤ 2 * m * K := by nlinarith
  calc ‖fres 3 ε z (K ^ 2) - fres 3 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2)
      ≤ 5 * K ^ 4 * (K ^ 2 - B ^ 2) / Real.sqrt (K ^ 4 + z ^ 2) * Real.sqrt (K ^ 4 + z ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hpos.le
    _ = 5 * K ^ 4 * (K ^ 2 - B ^ 2) := by field_simp
    _ ≤ 5 * K ^ 4 * (2 * m * K) := mul_le_mul_of_nonneg_left hKB (by positivity)
    _ = 10 * m * K ^ 5 := by ring

private lemma sqrt_two_ge : (1.4 : ℝ) ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

private lemma abs_cz_le' {m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B) (hBK : B ≤ K) (sx sy : Sgn) :
    |(sg sx * m - sg sy * B) / 2| ≤ K := by
  rw [abs_le]
  cases sx <;> cases sy <;> simp only [sg, ↓reduceIte, Bool.false_eq_true] <;>
    constructor <;> linarith

private lemma abs_cx_same' {m B K : ℝ} (hBK : B ≤ K) (htri : K ≤ B + m) (s : Sgn) :
    |(sg s * B - sg s * K) / 2| ≤ m / 2 := by
  rw [abs_le]
  cases s <;> simp only [sg, ↓reduceIte, Bool.false_eq_true] <;> constructor <;> linarith

private lemma abs_cx_opp' {m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B) (hBK : B ≤ K) (s : Sgn) :
    |(sg s * B - (-sg s) * K) / 2| ≤ K := by
  rw [abs_le]
  cases s <;> simp only [sg, ↓reduceIte, Bool.false_eq_true] <;> constructor <;> linarith

private lemma abs_sum_opp' {m B K : ℝ} (hm : 0 < m) (hBK : B ≤ K) (htri : K ≤ B + m)
    (sx s : Sgn) : |sg sx * m + sg s * B + (-sg s) * K| ≤ 2 * m := by
  rw [abs_le]
  cases sx <;> cases s <;> simp only [sg, ↓reduceIte, Bool.false_eq_true] <;>
    constructor <;> linarith

private lemma sg_of_ne' {a b : Sgn} (h : ¬ a = b) : sg b = -sg a := by
  cases a <;> cases b <;> simp_all [sg]

/-- **The cyclic kernel bound, `j = 3`** (`cyclic_sum_two` one degree up): the same hypotheses,
`|g Σ c_i f₃(l_i²)| ≤ 26 m K⁶/√(K⁴ + z²)`. -/
theorem cyclic_sum_three {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (z : ℝ) {m B K : ℝ} (hm : 0 < m)
    (hmB : m ≤ B) (hBK : B ≤ K) (htri : K ≤ B + m) (sx sy sz : Sgn) (g : ℂ) (hg1 : ‖g‖ ≤ 1)
    (hgW : ‖g‖ * (2 * Real.sqrt 2 * K) ≤ |sg sx * m + sg sy * B + sg sz * K|) :
    ‖g * ((((sg sy * B - sg sz * K) / 2 : ℝ) : ℂ) * fres 3 ε z (m ^ 2) +
        (((sg sz * K - sg sx * m) / 2 : ℝ) : ℂ) * fres 3 ε z (B ^ 2) +
        (((sg sx * m - sg sy * B) / 2 : ℝ) : ℂ) * fres 3 ε z (K ^ 2))‖ ≤
      26 * m * K ^ 6 / Real.sqrt (K ^ 4 + z ^ 2) := by
  have hB : 0 < B := hm.trans_le hmB
  have hK : 0 < K := hB.trans_le hBK
  have hD : 0 < Real.sqrt (K ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have h1 := cyclic_split ((sg sy * B - sg sz * K) / 2) ((sg sz * K - sg sx * m) / 2)
    ((sg sx * m - sg sy * B) / 2) (by ring) g (fres 3 ε z (m ^ 2)) (fres 3 ε z (B ^ 2))
    (fres 3 ε z (K ^ 2))
  have hd1 := diff_small_three hε (z := z) hm hmB hBK htri
  have hd2 := diff_large_three hε (z := z) hm hmB hBK htri
  have hcz := abs_cz_le' hm hmB hBK sx sy
  rw [le_div_iff₀ hD]
  refine (mul_le_mul_of_nonneg_right h1 hD.le).trans ?_
  have e : ‖g‖ * (|(sg sy * B - sg sz * K) / 2| * ‖fres 3 ε z (m ^ 2) - fres 3 ε z (B ^ 2)‖ +
      |(sg sx * m - sg sy * B) / 2| * ‖fres 3 ε z (K ^ 2) - fres 3 ε z (B ^ 2)‖) *
        Real.sqrt (K ^ 4 + z ^ 2) =
      ‖g‖ * (|(sg sy * B - sg sz * K) / 2| *
        (‖fres 3 ε z (m ^ 2) - fres 3 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2)) +
        |(sg sx * m - sg sy * B) / 2| *
        (‖fres 3 ε z (K ^ 2) - fres 3 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2))) := by ring
  rw [e]
  have hK6 : 0 < K ^ 6 := by positivity
  by_cases hs : sy = sz
  · subst hs
    have hcx := abs_cx_same' hBK htri sy
    calc _ ≤ 1 * (m / 2 * (20 * K ^ 6) + K * (10 * m * K ^ 5)) := by gcongr
      _ ≤ 26 * m * K ^ 6 := by nlinarith [mul_pos hm hK6]
  · have hsz := sg_of_ne' hs
    rw [hsz] at hgW ⊢
    have hcx := abs_cx_opp' hm hmB hBK sy
    have hXYZ := abs_sum_opp' hm hBK htri sx sy
    have hgK : ‖g‖ * K * 1.4 ≤ m := by
      have h2 := sqrt_two_ge
      have h3 : ‖g‖ * K * Real.sqrt 2 ≤ m := by nlinarith
      nlinarith [norm_nonneg g, mul_nonneg (norm_nonneg g) hK.le]
    have h5 : ‖g‖ * K * m * K ^ 5 ≤ ‖g‖ * K * K * K ^ 5 := by
      have := mul_nonneg (norm_nonneg g) hK.le
      gcongr
      linarith
    calc _ ≤ ‖g‖ * (K * (20 * K ^ 6) + K * (10 * m * K ^ 5)) := by gcongr
      _ ≤ 26 * m * K ^ 6 := by
          nlinarith [mul_le_mul_of_nonneg_right hgK hK6.le, mul_pos hm hK6,
            mul_nonneg (mul_nonneg (norm_nonneg g) hK.le) hK6.le]

/-- **The triad-level kernel bound at `j = 3`**: `triad_cyclic_le` one degree up, with `26`. -/
theorem triad_cyclic_three {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (z : ℝ)
    (ℓ : Fin 3 → Mode) (hsum : ∑ i, ℓ i = 0) (hne : ∀ i, ℓ i ≠ 0)
    (h01 : absk (ℓ 0) ≤ absk (ℓ 1)) (h12 : absk (ℓ 1) ≤ absk (ℓ 2))
    (s : Fin 3 → Sgn) (v : Fin 3 → V3) :
    let A := fun i => hel (s i) (ℓ i) (v i)
    ‖tau (ℓ 0) (ℓ 1) (A 0) (A 1) (A 2) * fres 3 ε z (absSq (ℓ 2)) +
        tau (ℓ 1) (ℓ 2) (A 1) (A 2) (A 0) * fres 3 ε z (absSq (ℓ 0)) +
        tau (ℓ 2) (ℓ 0) (A 2) (A 0) (A 1) * fres 3 ε z (absSq (ℓ 1))‖ ≤
      26 * absk (ℓ 0) * absk (ℓ 2) ^ 6 / Real.sqrt (absk (ℓ 2) ^ 4 + z ^ 2) *
        ∏ i, ‖A i‖ := by
  intro A
  rw [triad_rootings_eq 3 ε z ℓ hsum hne s v]
  have hm : 0 < absk (ℓ 0) := lt_of_lt_of_le one_pos (one_le_absk (hne 0))
  have htri : absk (ℓ 2) ≤ absk (ℓ 1) + absk (ℓ 0) := by
    rw [Fin.sum_univ_three] at hsum
    have e : ℓ 2 = -(ℓ 0 + ℓ 1) := by linear_combination hsum
    rw [e, absk_neg, add_comm (absk (ℓ 1))]
    exact absk_add_le _ _
  have hP : 0 ≤ ∏ i, ‖A i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hW := waleffe_le ℓ hsum hne s v
  have hT := norm_trip_le (A 0) (A 1) (A 2)
  have hP3 : ∏ i, ‖A i‖ = ‖A 0‖ * ‖A 1‖ * ‖A 2‖ := Fin.prod_univ_three _
  rcases hP.eq_or_lt with hP0 | hP0
  · have h0 : trip (A 0) (A 1) (A 2) = 0 := by
      rw [hP3] at hP0
      exact norm_le_zero_iff.mp (hT.trans_eq hP0.symm)
    rw [h0, zero_mul, norm_zero, ← hP0, mul_zero]
  · set P := ∏ i, ‖A i‖
    set g : ℂ := trip (A 0) (A 1) (A 2) / (P : ℂ) with hg
    have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP0.ne'
    have hgP : trip (A 0) (A 1) (A 2) = (P : ℂ) * g := by
      rw [hg, mul_div_cancel₀ _ hPc]
    have hg1 : ‖g‖ ≤ 1 := by
      rw [hg, norm_div, Complex.norm_real, Real.norm_of_nonneg hP0.le, div_le_one hP0, hP3]
      exact hT
    have hgW : ‖g‖ * (2 * Real.sqrt 2 * absk (ℓ 2)) ≤
        |sg (s 0) * absk (ℓ 0) + sg (s 1) * absk (ℓ 1) + sg (s 2) * absk (ℓ 2)| := by
      rw [hg, norm_div, Complex.norm_real, Real.norm_of_nonneg hP0.le]
      have := hW
      simp only [sl] at this
      rw [div_mul_eq_mul_div, div_le_iff₀ hP0]
      linarith
    have key : ∀ (f : ℝ → ℂ),
        ‖(P : ℂ) * g * ((((sl ℓ s 1 - sl ℓ s 2) / 2 : ℝ) : ℂ) * f (absSq (ℓ 0)) +
          (((sl ℓ s 2 - sl ℓ s 0) / 2 : ℝ) : ℂ) * f (absSq (ℓ 1)) +
          (((sl ℓ s 0 - sl ℓ s 1) / 2 : ℝ) : ℂ) * f (absSq (ℓ 2)))‖ =
        P * ‖g * ((((sg (s 1) * absk (ℓ 1) - sg (s 2) * absk (ℓ 2)) / 2 : ℝ) : ℂ) *
          f (absk (ℓ 0) ^ 2) +
          (((sg (s 2) * absk (ℓ 2) - sg (s 0) * absk (ℓ 0)) / 2 : ℝ) : ℂ) * f (absk (ℓ 1) ^ 2) +
          (((sg (s 0) * absk (ℓ 0) - sg (s 1) * absk (ℓ 1)) / 2 : ℝ) : ℂ) *
          f (absk (ℓ 2) ^ 2))‖ := by
      intro f
      rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hP0.le]
      simp only [sl, absk_sq]
    rw [hgP, key (fres 3 ε z), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hP0.le
    exact cyclic_sum_three hε z hm h01 h12 htri (s 0) (s 1) (s 2) g hg1 hgW

private lemma cyc3_rot' (j : ℕ) (ε z : ℝ) (ℓ0 ℓ1 ℓ2 : Mode) (s0 s1 s2 : Sgn) (v0 v1 v2 : V3) :
    cyc3 j ε z ℓ1 ℓ2 ℓ0 s1 s2 s0 v1 v2 v0 = cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 := by
  unfold cyc3
  ring

private lemma cyc3_swap' (j : ℕ) (ε z : ℝ) (ℓ0 ℓ1 ℓ2 : Mode) (s0 s1 s2 : Sgn) (v0 v1 v2 : V3) :
    cyc3 j ε z ℓ1 ℓ0 ℓ2 s1 s0 s2 v1 v0 v2 = cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 := by
  unfold cyc3
  rw [tau_comm ℓ1 ℓ0, tau_comm ℓ0 ℓ2, tau_comm ℓ2 ℓ1]
  ring

private lemma cyc3_three_sorted {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (z : ℝ)
    {ℓ0 ℓ1 ℓ2 : Mode} (hsum : ℓ0 + ℓ1 + ℓ2 = 0) (h0 : ℓ0 ≠ 0) (h1 : ℓ1 ≠ 0) (h2 : ℓ2 ≠ 0)
    (h01 : absk ℓ0 ≤ absk ℓ1) (h12 : absk ℓ1 ≤ absk ℓ2) (s0 s1 s2 : Sgn) (v0 v1 v2 : V3) :
    ‖cyc3 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2‖ ≤
      2 * absk ℓ2 ^ 2 * kerB 2 z (absk ℓ0) (absk ℓ2) * (‖v0‖ * ‖v1‖ * ‖v2‖) := by
  have h := triad_cyclic_three hε z ![ℓ0, ℓ1, ℓ2] (by simp [Fin.sum_univ_three, hsum])
    (fun i => by fin_cases i <;> simpa) (by simpa) (by simpa) ![s0, s1, s2] ![v0, v1, v2]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  have hP : ‖hel s0 ℓ0 v0‖ * ‖hel s1 ℓ1 v1‖ * ‖hel s2 ℓ2 v2‖ ≤ ‖v0‖ * ‖v1‖ * ‖v2‖ := by
    gcongr <;> exact norm_hel_le _ _ _
  refine h.trans ?_
  have e : 26 * absk ℓ0 * absk ℓ2 ^ 6 / Real.sqrt (absk ℓ2 ^ 4 + z ^ 2) =
      2 * absk ℓ2 ^ 2 * kerB 2 z (absk ℓ0) (absk ℓ2) := by
    unfold kerB
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left hP ?_
  exact mul_nonneg (by positivity) (kerB_nonneg 2 z (absk_nonneg _) (absk_nonneg _))

/-- **The cyclic sum of an unsorted nondegenerate triad at `j = 3`** (`cyc3_le`): at any `mn` above
the shortest leg and any `mx` above the longest one, with the kernel `2 mx² kerB₂`. -/
theorem cyc3_three_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (z : ℝ)
    {ℓ0 ℓ1 ℓ2 : Mode} (hsum : ℓ0 + ℓ1 + ℓ2 = 0) (h0 : ℓ0 ≠ 0) (h1 : ℓ1 ≠ 0) (h2 : ℓ2 ≠ 0)
    (s0 s1 s2 : Sgn) (v0 v1 v2 : V3) {mn mx : ℝ}
    (hmn : absk ℓ0 ≤ mn ∨ absk ℓ1 ≤ mn ∨ absk ℓ2 ≤ mn)
    (hmx : absk ℓ0 ≤ mx ∧ absk ℓ1 ≤ mx ∧ absk ℓ2 ≤ mx) :
    ‖cyc3 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2‖ ≤
      2 * mx ^ 2 * kerB 2 z mn mx * (‖v0‖ * ‖v1‖ * ‖v2‖) := by
  have p0 := lt_of_lt_of_le one_pos (one_le_absk h0)
  have p1 := lt_of_lt_of_le one_pos (one_le_absk h1)
  have p2 := lt_of_lt_of_le one_pos (one_le_absk h2)
  obtain ⟨hx0, hx1, hx2⟩ := hmx
  have hP0 : 0 ≤ ‖v0‖ * ‖v1‖ * ‖v2‖ := by positivity
  have hmn0 : 0 ≤ mn := by
    rcases hmn with h | h | h <;> linarith
  have fin : ∀ {a c : Mode} {P : ℝ}, P = ‖v0‖ * ‖v1‖ * ‖v2‖ →
      ‖cyc3 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2‖ ≤
        2 * absk c ^ 2 * kerB 2 z (absk a) (absk c) * P →
      absk a ≤ mn → 0 < absk c → absk c ≤ mx →
      ‖cyc3 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2‖ ≤
        2 * mx ^ 2 * kerB 2 z mn mx * (‖v0‖ * ‖v1‖ * ‖v2‖) := by
    intro a c P hP hle ha hc hcx
    rw [hP] at hle
    refine hle.trans (mul_le_mul_of_nonneg_right ?_ hP0)
    have hK := kerB_mono (j := 2) (by norm_num) z (absk_nonneg a) ha hc hcx
    have hK0 := kerB_nonneg 2 z (absk_nonneg a) hc.le
    have h2' : absk c ^ 2 ≤ mx ^ 2 := pow_le_pow_left₀ hc.le hcx 2
    exact mul_le_mul (by linarith) hK hK0 (by positivity)
  rcases le_total (absk ℓ0) (absk ℓ1) with h01 | h01 <;>
    rcases le_total (absk ℓ1) (absk ℓ2) with h12 | h12 <;>
    rcases le_total (absk ℓ0) (absk ℓ2) with h02 | h02
  · exact fin rfl (cyc3_three_sorted hε z hsum h0 h1 h2 h01 h12 _ _ _ _ _ _)
      (by rcases hmn with h | h | h <;> linarith) p2 hx2
  · exact fin rfl (cyc3_three_sorted hε z hsum h0 h1 h2 h01 h12 _ _ _ _ _ _)
      (by rcases hmn with h | h | h <;> linarith) p2 hx2
  · have hs : ℓ0 + ℓ2 + ℓ1 = 0 := by rw [← hsum]; abel
    have e : cyc3 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 = cyc3 3 ε z ℓ0 ℓ2 ℓ1 s0 s2 s1 v0 v2 v1 :=
      ((cyc3_rot' 3 ε z ℓ1 ℓ0 ℓ2 s1 s0 s2 v1 v0 v2).trans
        (cyc3_swap' 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2)).symm
    refine fin (a := ℓ0) (c := ℓ1) (P := ‖v0‖ * ‖v2‖ * ‖v1‖) (by ring) ?_
      (by rcases hmn with h | h | h <;> linarith) p1 hx1
    rw [e]
    exact cyc3_three_sorted hε z hs h0 h2 h1 h02 h12 _ _ _ _ _ _
  · have hs : ℓ2 + ℓ0 + ℓ1 = 0 := by rw [← hsum]; abel
    have e : cyc3 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 = cyc3 3 ε z ℓ2 ℓ0 ℓ1 s2 s0 s1 v2 v0 v1 :=
      cyc3_rot' 3 ε z ℓ2 ℓ0 ℓ1 s2 s0 s1 v2 v0 v1
    refine fin (a := ℓ2) (c := ℓ1) (P := ‖v2‖ * ‖v0‖ * ‖v1‖) (by ring) ?_
      (by rcases hmn with h | h | h <;> linarith) p1 hx1
    rw [e]
    exact cyc3_three_sorted hε z hs h2 h0 h1 h02 h01 _ _ _ _ _ _
  · have hs : ℓ1 + ℓ0 + ℓ2 = 0 := by rw [← hsum]; abel
    have e : cyc3 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 = cyc3 3 ε z ℓ1 ℓ0 ℓ2 s1 s0 s2 v1 v0 v2 :=
      (cyc3_swap' 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2).symm
    refine fin (a := ℓ1) (c := ℓ2) (P := ‖v1‖ * ‖v0‖ * ‖v2‖) (by ring) ?_
      (by rcases hmn with h | h | h <;> linarith) p2 hx2
    rw [e]
    exact cyc3_three_sorted hε z hs h1 h0 h2 h01 h02 _ _ _ _ _ _
  · have hs : ℓ1 + ℓ2 + ℓ0 = 0 := by rw [← hsum]; abel
    have e : cyc3 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 = cyc3 3 ε z ℓ1 ℓ2 ℓ0 s1 s2 s0 v1 v2 v0 :=
      (cyc3_rot' 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2).symm
    refine fin (a := ℓ1) (c := ℓ0) (P := ‖v1‖ * ‖v2‖ * ‖v0‖) (by ring) ?_
      (by rcases hmn with h | h | h <;> linarith) p0 hx0
    rw [e]
    exact cyc3_three_sorted hε z hs h1 h2 h0 h12 h02 _ _ _ _ _ _
  all_goals
    have hs : ℓ2 + ℓ1 + ℓ0 = 0 := by rw [← hsum]; abel
    have e : cyc3 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2 = cyc3 3 ε z ℓ2 ℓ1 ℓ0 s2 s1 s0 v2 v1 v0 :=
      ((cyc3_swap' 3 ε z ℓ1 ℓ2 ℓ0 s1 s2 s0 v1 v2 v0).trans
        (cyc3_rot' 3 ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 v2)).symm
    refine fin (a := ℓ2) (c := ℓ0) (P := ‖v2‖ * ‖v1‖ * ‖v0‖) (by ring) ?_
      (by rcases hmn with h | h | h <;> linarith) p0 hx0
    rw [e]
    exact cyc3_three_sorted hε z hs h2 h1 h0 h12 h01 _ _ _ _ _ _

open scoped Classical in
/-- **The triad term at `j = 3`** on a nondegenerate triad (`abs_nearTriadTerm_le`): the kernel
`2 mx² kerB₂` at each near helicity. -/
theorem norm_nearTriadTerm_three_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) (F G : Field)
    {p q : Mode} (hp : p ≠ 0) (hq : q ≠ 0) (hk : p + q ≠ 0) {mn mx : ℝ}
    (hmn : absk p ≤ mn ∨ absk q ≤ mn ∨ absk (p + q) ≤ mn)
    (hmx : absk p ≤ mx ∧ absk q ≤ mx ∧ absk (p + q) ≤ mx) :
    ‖nearTriadTerm 3 ε r τ F G (p, q)‖ ≤
      2 * mx ^ 2 * (∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
        if NearT a b c p q then kerB 2 (r * Phi a b c p q) mn mx else 0) *
        (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖) := by
  rw [nearTriadTerm_eq 3 ε r τ F G hp hq hk, Finset.mul_sum, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun c _ => ?_
  split_ifs
  · rw [norm_mul, show ‖phaseM τ a b c p q‖ = 1 from by
      rw [phaseM, mul_comm, Complex.norm_exp_ofReal_mul_I], one_mul]
    refine cyc3_three_le hε _ (by abel) hp hq (neg_ne_zero.2 hk) _ _ _ _ _ _ ?_ ?_
    · rwa [absk_neg]
    · rwa [absk_neg]
  · simp

/-! ### B. The proper near kernel and the box sums (`H1/Cubic.lean`, private there) -/

/-- The proper near kernel `|L| κ_N(L, u)`: its squared moment over `nearBox L` is `momP`. -/
def propKer (q : ℝ) (L u : Mode) : ℝ := absk L * nearKerSum q L u

lemma propKer_nonneg (q : ℝ) (L u : Mode) : 0 ≤ propKer q L u :=
  mul_nonneg (absk_nonneg L) (nearKerSum_nonneg q L u)

/-- The moment of the proper near kernel is `momP`. -/
lemma sum_propKer_sq (q : ℝ) (L : Mode) : ∑ u ∈ nearBox L, propKer q L u ^ 2 ≤ MomP q := by
  refine le_trans (le_of_eq ?_) (momP_le_MomP q L)
  simp only [propKer, mul_pow, ← Finset.mul_sum, sum_nearKerSum_sq, momP]

/-- The summand `U_L κ(L, u) V_u W_{L−u}` of a box sum, on `u ∈ nearBox L`. -/
def boxK (κ : Mode → Mode → ℝ) (U V W : Mode → ℝ) (y : Mode × Mode) : ℝ :=
  if y.2 ∈ nearBox y.1 then U y.1 * (κ y.1 y.2 * (V y.2 * W (y.1 - y.2))) else 0

lemma boxK_of_mem {κ : Mode → Mode → ℝ} {U V W : Mode → ℝ} {k u : Mode} (hu : u ∈ nearBox k) :
    boxK κ U V W (k, u) = U k * (κ k u * (V u * W (k - u))) :=
  ite_eq_left hu

lemma boxK_nonneg {κ : Mode → Mode → ℝ} (hκ : ∀ k p, 0 ≤ κ k p) {U V W : Mode → ℝ}
    (hU : ∀ k, 0 ≤ U k) (hV : ∀ k, 0 ≤ V k) (hW : ∀ k, 0 ≤ W k) (y : Mode × Mode) :
    0 ≤ boxK κ U V W y := by
  unfold boxK
  split_ifs
  · exact mul_nonneg (hU _) (mul_nonneg (hκ _ _) (mul_nonneg (hV _) (hW _)))
  · exact le_rfl

/-- The box sum over the lattice square, by `moment_cauchy`. -/
lemma boxK_tsum_le {κ : Mode → Mode → ℝ} {M : ℝ} (hκ : ∀ k p, 0 ≤ κ k p)
    (hM : ∀ k, ∑ p ∈ nearBox k, κ k p ^ 2 ≤ M) {U V W : Mode → ℝ} (hU : ∀ k, 0 ≤ U k)
    (hV : ∀ k, 0 ≤ V k) (hW : ∀ k, 0 ≤ W k) (hU2 : Summable fun k => U k ^ 2)
    (hV2 : Summable fun k => V k ^ 2) (hW2 : Summable fun k => W k ^ 2) :
    Summable (boxK κ U V W) ∧ ∑' y, boxK κ U V W y ≤
      Real.sqrt M *
        (Real.sqrt (∑' k, U k ^ 2) * Real.sqrt (∑' k, V k ^ 2) * Real.sqrt (∑' k, W k ^ 2)) := by
  obtain ⟨hs, hle⟩ := moment_cauchy hκ hM hU hV hW hU2 hV2 hW2
  have h0 : ∀ k, ∀ u ∉ nearBox k, boxK κ U V W (k, u) = 0 := fun k u hu => ite_eq_right hu
  have hfib : ∀ k, Summable fun u => boxK κ U V W (k, u) := fun k =>
    summable_of_ne_finset_zero (h0 k)
  have hval : ∀ k, ∑' u, boxK κ U V W (k, u) =
      U k * ∑ p ∈ nearBox k, κ k p * (V p * W (k - p)) := fun k => by
    rw [tsum_eq_sum (h0 k), Finset.mul_sum]
    exact Finset.sum_congr rfl fun u hu => boxK_of_mem hu
  have hsum : Summable (boxK κ U V W) :=
    (summable_prod_of_nonneg (boxK_nonneg hκ hU hV hW)).2
      ⟨hfib, by simpa only [Function.comp_def, hval] using hs⟩
  refine ⟨hsum, ?_⟩
  rw [hsum.tsum_prod]
  simpa only [hval] using hle

/-! ### C. The regions: the longest leg of a fast triad -/

/-- `(p, q) ↦ (−p, q)`: the longest leg `p`. -/
def eA : Equiv.Perm (Mode × Mode) :=
  Function.Involutive.toPerm (fun x => (-x.1, x.2)) fun x => Prod.ext (by simp) rfl

/-- `(p, q) ↦ (−q, p)`: the longest leg `q`. -/
def eB : Equiv.Perm (Mode × Mode) where
  toFun x := (-x.2, x.1)
  invFun x := (x.2, -x.1)
  left_inv x := Prod.ext rfl (by simp)
  right_inv x := Prod.ext (by simp) rfl

/-- `(p, q) ↦ (p + q, p)`: the longest leg `−(p + q)`. -/
def eC : Equiv.Perm (Mode × Mode) where
  toFun x := (x.1 + x.2, x.1)
  invFun x := (x.2, x.1 - x.2)
  left_inv x := Prod.ext rfl (by simp)
  right_inv x := Prod.ext (by simp) rfl

/-- The box terms of the three regions. -/
def triB (κ : Mode → Mode → ℝ) (U V W : Mode → ℝ) (x : Mode × Mode) : ℝ :=
  boxK κ U V W (eA x) + boxK κ U V W (eB x) + boxK κ U V W (eC x)

lemma triB_nonneg {κ : Mode → Mode → ℝ} (hκ : ∀ k p, 0 ≤ κ k p) {U V W : Mode → ℝ}
    (hU : ∀ k, 0 ≤ U k) (hV : ∀ k, 0 ≤ V k) (hW : ∀ k, 0 ≤ W k) (x : Mode × Mode) :
    0 ≤ triB κ U V W x :=
  add_nonneg (add_nonneg (boxK_nonneg hκ hU hV hW _) (boxK_nonneg hκ hU hV hW _))
    (boxK_nonneg hκ hU hV hW _)

/-- Each box term is below the sum of the three. -/
lemma boxK_le_triB {κ : Mode → Mode → ℝ} (hκ : ∀ k p, 0 ≤ κ k p) {U V W : Mode → ℝ}
    (hU : ∀ k, 0 ≤ U k) (hV : ∀ k, 0 ≤ V k) (hW : ∀ k, 0 ≤ W k) {e : Equiv.Perm (Mode × Mode)}
    (he : e = eA ∨ e = eB ∨ e = eC) (x : Mode × Mode) :
    boxK κ U V W (e x) ≤ triB κ U V W x := by
  have h1 := boxK_nonneg hκ hU hV hW (eA x)
  have h2 := boxK_nonneg hκ hU hV hW (eB x)
  have h3 := boxK_nonneg hκ hU hV hW (eC x)
  unfold triB
  rcases he with rfl | rfl | rfl <;> linarith

/-- `Equiv.summable_iff` on an abstract `b`: at a concrete `boxK` the unifier times out. -/
lemma perm_summable {b : Mode × Mode → ℝ} (e : Equiv.Perm (Mode × Mode)) (h : Summable b) :
    Summable fun x => b (e x) :=
  e.summable_iff.mpr h

/-- `Equiv.tsum_eq` on an abstract `b`. -/
lemma perm_tsum {b : Mode × Mode → ℝ} (e : Equiv.Perm (Mode × Mode)) :
    ∑' x, b (e x) = ∑' x, b x :=
  e.tsum_eq b

/-- The sum of the three regions, `3 √M ‖U‖ ‖V‖ ‖W‖`. -/
lemma triB_facts {κ : Mode → Mode → ℝ} {M : ℝ} (hκ : ∀ k p, 0 ≤ κ k p)
    (hM : ∀ k, ∑ p ∈ nearBox k, κ k p ^ 2 ≤ M) {U V W : Mode → ℝ} (hU : ∀ k, 0 ≤ U k)
    (hV : ∀ k, 0 ≤ V k) (hW : ∀ k, 0 ≤ W k) (hU2 : Summable fun k => U k ^ 2)
    (hV2 : Summable fun k => V k ^ 2) (hW2 : Summable fun k => W k ^ 2) :
    Summable (triB κ U V W) ∧ ∑' x, triB κ U V W x ≤
      3 * (Real.sqrt M *
        (Real.sqrt (∑' k, U k ^ 2) * Real.sqrt (∑' k, V k ^ 2) * Real.sqrt (∑' k, W k ^ 2))) := by
  obtain ⟨s, b⟩ := boxK_tsum_le hκ hM hU hV hW hU2 hV2 hW2
  set R := Real.sqrt M *
    (Real.sqrt (∑' k, U k ^ 2) * Real.sqrt (∑' k, V k ^ 2) * Real.sqrt (∑' k, W k ^ 2))
  have s1 := perm_summable eA s
  have s2 := perm_summable eB s
  have s3 := perm_summable eC s
  have hs : Summable (triB κ U V W) := (s1.add s2).add s3
  refine ⟨hs, ?_⟩
  have e : ∑' x, triB κ U V W x = ∑' x, boxK κ U V W (eA x) + ∑' x, boxK κ U V W (eB x) +
      ∑' x, boxK κ U V W (eC x) := by
    rw [← s1.tsum_add s2, ← (s1.add s2).tsum_add s3]
    exact tsum_congr fun x => rfl
  rw [e, perm_tsum eA, perm_tsum eB, perm_tsum eC]
  set A := ∑' x, boxK κ U V W x
  linarith

/-- At least one leg of a triad is the longest. -/
lemma regions' (p q : Mode) :
    (absk q ≤ absk p ∧ absk (p + q) ≤ absk p) ∨ (absk p ≤ absk q ∧ absk (p + q) ≤ absk q) ∨
      (absk p ≤ absk (p + q) ∧ absk q ≤ absk (p + q)) := by
  rcases le_total (absk p) (absk q) with h1 | h1 <;>
    rcases le_total (absk q) (absk (p + q)) with h2 | h2 <;>
    rcases le_total (absk p) (absk (p + q)) with h3 | h3
  · exact Or.inr (Or.inr ⟨h3, h2⟩)
  · exact Or.inr (Or.inr ⟨h1.trans h2, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h3, h2⟩)
  · exact Or.inl ⟨h1, h3⟩
  · exact Or.inl ⟨h1, h2.trans h1⟩
  · exact Or.inl ⟨h1, h3⟩

/-- Every helicity pattern of a triad is, up to sign, one of the near phases `nearPhi` (from
`H1/Cubic.lean`). -/
lemma exists_pat' (α β γ : Sgn) (u k : Mode) :
    ∃ s₁ s₂, |lam α u + lam β (k - u) + lam γ (-k)| = |nearPhi s₁ s₂ u k| := by
  cases γ
  · refine ⟨!α, !β, ?_⟩
    have e : lam false k = -lam true k := by simpa using lam_not true k
    simp only [nearPhi, lam_not, lam_neg, e]
    rw [← abs_neg]
    congr 1
    ring
  · refine ⟨α, β, ?_⟩
    simp only [nearPhi, lam_neg]
    congr 1

private lemma sub_A' (p q : Mode) : -p - q = -(p + q) := by abel

private lemma sub_B' (p q : Mode) : -q - p = -(p + q) := by abel

private lemma regA {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0) (hr3 : (-(p + q)) 2 ≠ 0)
    (h1 : absk q ≤ absk p) (h2 : absk (p + q) ≤ absk p) :
    q ∈ nearBox (-p) ∧ minLeg q (-p) = min (absk q) (absk (p + q)) ∧
      ∀ a b c, ∃ s₁ s₂, |Phi a b c p q| = |nearPhi s₁ s₂ q (-p)| := by
  refine ⟨mem_nearBox.2 ⟨by simpa using hp3, hq3, by rw [sub_A']; exact hr3, by rwa [absk_neg],
    by rw [sub_A', absk_neg, absk_neg]; exact h2⟩, by rw [minLeg, sub_A', absk_neg], ?_⟩
  intro a b c
  obtain ⟨s₁, s₂, h⟩ := exists_pat' b c a q (-p)
  refine ⟨s₁, s₂, ?_⟩
  rw [← h, sub_A', neg_neg, lam_neg, Phi]
  congr 1
  ring

private lemma regB {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0) (hr3 : (-(p + q)) 2 ≠ 0)
    (h1 : absk p ≤ absk q) (h2 : absk (p + q) ≤ absk q) :
    p ∈ nearBox (-q) ∧ minLeg p (-q) = min (absk p) (absk (p + q)) ∧
      ∀ a b c, ∃ s₁ s₂, |Phi a b c p q| = |nearPhi s₁ s₂ p (-q)| := by
  refine ⟨mem_nearBox.2 ⟨by simpa using hq3, hp3, by rw [sub_B']; exact hr3, by rwa [absk_neg],
    by rw [sub_B', absk_neg, absk_neg]; exact h2⟩, by rw [minLeg, sub_B', absk_neg], ?_⟩
  intro a b c
  obtain ⟨s₁, s₂, h⟩ := exists_pat' a c b p (-q)
  refine ⟨s₁, s₂, ?_⟩
  rw [← h, sub_B', neg_neg, lam_neg, Phi]
  congr 1
  ring

private lemma regC {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0) (hr3 : (-(p + q)) 2 ≠ 0)
    (h1 : absk p ≤ absk (p + q)) (h2 : absk q ≤ absk (p + q)) :
    p ∈ nearBox (p + q) ∧ minLeg p (p + q) = min (absk p) (absk q) ∧
      ∀ a b c, ∃ s₁ s₂, |Phi a b c p q| = |nearPhi s₁ s₂ p (p + q)| := by
  have e : p + q - p = q := by abel
  have hk3 : (p + q) 2 ≠ 0 := fun h => hr3 (by simp only [Pi.neg_apply, h, neg_zero])
  refine ⟨mem_nearBox.2 ⟨hk3, hp3, by rw [e]; exact hq3, h1, by rw [e]; exact h2⟩,
    by rw [minLeg, e], ?_⟩
  intro a b c
  obtain ⟨s₁, s₂, h⟩ := exists_pat' a b c p (p + q)
  refine ⟨s₁, s₂, ?_⟩
  rw [← h, e, lam_neg, Phi]
  congr 1

/-- A real field has the same amplitude at `k` and `−k`. -/
lemma norm_real_neg {F : Field} (hF : IsReal F) (k : Mode) : ‖F (-k)‖ = ‖F k‖ := by
  rw [hF k, norm_conjV]

/-- **The region of a fast triad** of a real field: the longest leg gives the output `L` of a box
term, `e (p, q) = (L, u)`, with the legs `{L, u, L − u}` and the same amplitudes. -/
lemma exists_region {F : Field} (hFr : IsReal F) {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0)
    (hr3 : (-(p + q)) 2 ≠ 0) :
    ∃ (e : Equiv.Perm (Mode × Mode)) (L u : Mode), (e = eA ∨ e = eB ∨ e = eC) ∧
      e (p, q) = (L, u) ∧ u ∈ nearBox L ∧
      (∀ a b c, ∃ s₁ s₂, |Phi a b c p q| = |nearPhi s₁ s₂ u L|) ∧
      ‖F L‖ * ‖F u‖ * ‖F (L - u)‖ = ‖F p‖ * ‖F q‖ * ‖F (-(p + q))‖ ∧
      (absk p ≤ absk L ∧ absk q ≤ absk L ∧ absk (p + q) ≤ absk L) ∧
      (absk p ≤ minLeg u L ∨ absk q ≤ minLeg u L ∨ absk (p + q) ≤ minLeg u L) := by
  rcases regions' p q with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨hu, hm, hpat⟩ := regA hp3 hq3 hr3 h1 h2
    refine ⟨eA, -p, q, Or.inl rfl, rfl, hu, hpat, ?_, ?_, ?_⟩
    · rw [sub_A', norm_real_neg hFr]
    · rw [absk_neg]
      exact ⟨le_rfl, h1, h2⟩
    · rw [hm]
      rcases min_choice (absk q) (absk (p + q)) with h | h <;> rw [h]
      · exact Or.inr (Or.inl le_rfl)
      · exact Or.inr (Or.inr le_rfl)
  · obtain ⟨hu, hm, hpat⟩ := regB hp3 hq3 hr3 h1 h2
    refine ⟨eB, -q, p, Or.inr (Or.inl rfl), rfl, hu, hpat, ?_, ?_, ?_⟩
    · rw [sub_B', norm_real_neg hFr]
      ring
    · rw [absk_neg]
      exact ⟨h1, le_rfl, h2⟩
    · rw [hm]
      rcases min_choice (absk p) (absk (p + q)) with h | h <;> rw [h]
      · exact Or.inl le_rfl
      · exact Or.inr (Or.inr le_rfl)
  · obtain ⟨hu, hm, hpat⟩ := regC hp3 hq3 hr3 h1 h2
    refine ⟨eC, p + q, p, Or.inr (Or.inr rfl), rfl, hu, hpat, ?_, ⟨h1, h2, le_rfl⟩, ?_⟩
    · rw [add_sub_cancel_left, ← norm_real_neg hFr (p + q)]
      ring
    · rw [hm]
      rcases min_choice (absk p) (absk q) with h | h <;> rw [h]
      · exact Or.inl le_rfl
      · exact Or.inr (Or.inl le_rfl)

/-! ### D. The pointwise bounds at a triad -/

open scoped Classical in
/-- The near helicity sum of `kerB₂` against the proper kernel (`kerB_le_nearKerSum`). -/
lemma near_sum_le (r : ℝ) {p q L u : Mode} (hu : u ∈ nearBox L)
    (hpat : ∀ a b c, ∃ s₁ s₂, |Phi a b c p q| = |nearPhi s₁ s₂ u L|) :
    (∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
        if NearT a b c p q then kerB 2 (r * Phi a b c p q) (minLeg u L) (absk L) else 0) ≤
      104 * minLeg u L ^ 2 * absk L ^ 4 * propKer |r| L u := by
  have hK := absk_nonneg L
  set A := 13 * minLeg u L ^ 2 * absk L ^ 4 * propKer |r| L u with hA
  have hA0 : 0 ≤ A := by
    have := propKer_nonneg |r| L u
    positivity
  have hterm : ∀ a b c, (if NearT a b c p q then
      kerB 2 (r * Phi a b c p q) (minLeg u L) (absk L) else 0) ≤ A := by
    intro a b c
    split_ifs with hN
    · obtain ⟨s₁, s₂, hs⟩ := hpat a b c
      refine (kerB_le_nearKerSum 2 r _ hu hs hN.2.1 hN.2.2).trans (le_of_eq ?_)
      rw [hA]
      unfold propKer
      ring
    · exact hA0
  calc _ ≤ ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, A :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ =>
          hterm a b c
    _ = 8 * A := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
    _ = _ := by
        rw [hA]
        ring

/-- `tripT` vanishes with its first amplitude. -/
lemma tripT_zero_left (m : Mult) {X : Field} (Y Z : Field) {p : Mode} (h : X p = 0) (q : Mode) :
    tripT m X Y Z p q = 0 := by
  simp [tripT, h, hel_zero_right, tau_zero_left]

/-- `tripT` vanishes with its second amplitude. -/
lemma tripT_zero_mid (m : Mult) (X : Field) {Y : Field} (Z : Field) (p : Mode) {q : Mode}
    (h : Y q = 0) : tripT m X Y Z p q = 0 := by
  simp [tripT, h, hel_zero_right, tau_zero_mid]

/-- `tripT` vanishes with its third amplitude. -/
lemma tripT_zero_right (m : Mult) (X Y : Field) {Z : Field} {p q : Mode}
    (h : Z (-(p + q)) = 0) : tripT m X Y Z p q = 0 := by
  simp only [tripT, h, hel_zero_right, tau_zero_right, mul_zero, Finset.sum_const_zero]

/-- The triad term vanishes with one of its amplitudes. -/
lemma nearTriadTerm_amp_zero (j : ℕ) (ε r τ : ℝ) {F : Field} {p q : Mode}
    (h : F p = 0 ∨ F q = 0 ∨ F (-(p + q)) = 0) : nearTriadTerm j ε r τ F F (p, q) = 0 := by
  set s := -(p + q) with hs
  have e1 : -(q + s) = p := by rw [hs]; abel
  have e2 : -(s + p) = q := by rw [hs]; abel
  have hrho : rho (p, q) = (q, s) := rfl
  have hrho2 : rho (q, s) = (s, p) := Prod.ext rfl e1
  have t1 : tripT (nearCorrM ε r τ) F F F p q = 0 := by
    rcases h with h | h | h
    · exact tripT_zero_left _ _ _ h _
    · exact tripT_zero_mid _ _ _ _ h
    · exact tripT_zero_right _ _ _ h
  have t2 : tripT (nearCorrM ε r τ) F F F s p = 0 := by
    rcases h with h | h | h
    · exact tripT_zero_mid _ _ _ _ h
    · exact tripT_zero_right _ _ _ (by rw [e2]; exact h)
    · exact tripT_zero_left _ _ _ h _
  have t3 : tripT (nearCorrM ε r τ) F F F q s = 0 := by
    rcases h with h | h | h
    · exact tripT_zero_right _ _ _ (by rw [e1]; exact h)
    · exact tripT_zero_left _ _ _ h _
    · exact tripT_zero_mid _ _ _ _ h
  unfold nearTriadTerm
  rw [hrho, hrho2]
  simp only [nearTri, t1, t2, t3, mul_zero, add_zero]

/-- Not a fast triad: one amplitude vanishes. -/
lemma amp_zero_of_not_fast {F : Field} (hF : PiF F = F) {p q : Mode}
    (h : ¬(p 2 ≠ 0 ∧ q 2 ≠ 0 ∧ (-(p + q)) 2 ≠ 0)) :
    F p = 0 ∨ F q = 0 ∨ F (-(p + q)) = 0 := by
  by_cases h1 : p 2 = 0
  · exact Or.inl (fast_zero hF h1)
  by_cases h2 : q 2 = 0
  · exact Or.inr (Or.inl (fast_zero hF h2))
  have h3 : (-(p + q)) 2 = 0 := by
    by_contra h3
    exact h ⟨h1, h2, h3⟩
  exact Or.inr (Or.inr (fast_zero hF h3))

/-- The nondegeneracy of a fast triad. -/
lemma fast_ne {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0) (hr3 : (-(p + q)) 2 ≠ 0) :
    p ≠ 0 ∧ q ≠ 0 ∧ p + q ≠ 0 :=
  ⟨fun h => hp3 (by simp [h]), fun h => hq3 (by simp [h]), fun h => hr3 (by simp [h])⟩

/-- The legs of a box point. -/
lemma box_legs {L u : Mode} (hu : u ∈ nearBox L) :
    0 < absk L ∧ 0 < absk u ∧ 0 < absk (L - u) ∧ absk L ≤ absk u + absk (L - u) ∧
      absk u ≤ absk L ∧ absk (L - u) ≤ absk L := by
  obtain ⟨h1, h2, h3⟩ := one_le_absk_of_mem_nearBox hu
  obtain ⟨-, -, -, h4, h5⟩ := mem_nearBox.1 hu
  have h6 := absk_add_le u (L - u)
  rw [add_sub_cancel] at h6
  exact ⟨by linarith, by linarith, by linarith, h6, h4, h5⟩

/-- **The pointwise domination of the static near sum**, slots `(H², H², H²)`:
`m²K⁴ ≤ 4 K² y² ℓ²`, `y, ℓ` the two other legs. -/
lemma static_point (r τ : ℝ) {F : Field} (hFr : IsReal F) (hF' : PiF F = F) (x : Mode × Mode) :
    ‖nearTriadTerm 2 (-1) r τ F F x‖ ≤
      416 * triB (propKer |r|) (wtd 2 F) (wtd 2 F) (wtd 2 F) x := by
  obtain ⟨p, q⟩ := x
  have hκ := propKer_nonneg |r|
  have hW := wtd_nonneg 2 F
  by_cases hfast : p 2 ≠ 0 ∧ q 2 ≠ 0 ∧ (-(p + q)) 2 ≠ 0
  swap
  · rw [nearTriadTerm_amp_zero 2 _ _ _ (amp_zero_of_not_fast hF' hfast), norm_zero]
    exact mul_nonneg (by norm_num) (triB_nonneg hκ hW hW hW _)
  obtain ⟨hp3, hq3, hr3⟩ := hfast
  obtain ⟨e, L, u, he, hex, hu, hpat, hamp, hmx, hmn⟩ := exists_region hFr hp3 hq3 hr3
  have h1 := abs_nearTriadTerm_le (j := 2) (Or.inr rfl) (Or.inr rfl) r τ F F p q hmn hmx
  have h2 := near_sum_le r hu hpat
  have hle := boxK_le_triB hκ hW hW hW he (p, q)
  rw [hex, boxK_of_mem hu] at hle
  obtain ⟨hK, hy, hl, htri, hyK, hlK⟩ := box_legs hu
  set P := ‖F p‖ * ‖F q‖ * ‖F (-(p + q))‖ with hP
  have hP0 : 0 ≤ P := by positivity
  set κ := propKer |r| L u with hκdef
  have hκ0 : 0 ≤ κ := hκ _ _
  simp only [wtd] at hle
  have hbox : absk L ^ 2 * ‖F L‖ * (κ * (absk u ^ 2 * ‖F u‖ * (absk (L - u) ^ 2 * ‖F (L - u)‖))) =
      absk L ^ 2 * absk u ^ 2 * absk (L - u) ^ 2 * κ * P := by
    rw [← hamp]
    ring
  rw [hbox] at hle
  have hw : minLeg u L ^ 2 * absk L ^ 4 ≤ 4 * (absk L ^ 2 * absk u ^ 2 * absk (L - u) ^ 2) := by
    unfold minLeg
    set K := absk L
    set y := absk u
    set l := absk (L - u)
    rcases le_total y l with h | h
    · rw [min_eq_left h]
      have h3 : K ^ 2 ≤ 4 * l ^ 2 := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ y ^ 2 * K ^ 2)
      nlinarith
    · rw [min_eq_right h]
      have h3 : K ^ 2 ≤ 4 * y ^ 2 := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ l ^ 2 * K ^ 2)
      nlinarith
  calc ‖nearTriadTerm 2 (-1) r τ F F (p, q)‖
      ≤ (104 * minLeg u L ^ 2 * absk L ^ 4 * κ) * P :=
        h1.trans (mul_le_mul_of_nonneg_right h2 hP0)
    _ = 104 * (minLeg u L ^ 2 * absk L ^ 4) * (κ * P) := by ring
    _ ≤ 104 * (4 * (absk L ^ 2 * absk u ^ 2 * absk (L - u) ^ 2)) * (κ * P) := by gcongr
    _ = 416 * (absk L ^ 2 * absk u ^ 2 * absk (L - u) ^ 2 * κ * P) := by ring
    _ ≤ _ := by linarith

/-- `Σ = |p|² + |q|² + |p+q|²`, the sum of the three heats of a triad. -/
def sigK (x : Mode × Mode) : ℝ := absSq x.1 + absSq x.2 + absSq (x.1 + x.2)

/-- `Σ` is common to the three rootings of a triad. -/
lemma sigK_rho (x : Mode × Mode) : sigK (rho x) = sigK x := by
  have e : x.2 + -(x.1 + x.2) = -x.1 := by abel
  change absSq x.2 + absSq (-(x.1 + x.2)) + absSq (x.2 + -(x.1 + x.2)) = _
  rw [e, absSq_neg, absSq_neg]
  unfold sigK
  ring

open scoped Classical in
/-- **The pointwise domination of the heat near sum**, slots `H³` on the two large legs and `H²`
on the small one: `Σ ≤ 3K²`, `‖T₂‖ ≤ S P`, `‖T₃‖ ≤ 2K² S P`, `S ≤ 104 m²K⁴ κ`, and
`m²K⁶ ≤ 8 m²B³K³`. -/
lemma heat_point (r τ : ℝ) {F : Field} (hFr : IsReal F) (hF' : PiF F = F) (x : Mode × Mode) :
    ‖(sigK x : ℂ) * nearTriadTerm 2 (-1) r τ F F x - nearTriadTerm 3 (-1) r τ F F x‖ ≤
      4160 * (triB (propKer |r|) (wtd 3 F) (wtd 2 F) (wtd 3 F) x +
        triB (propKer |r|) (wtd 3 F) (wtd 3 F) (wtd 2 F) x) := by
  obtain ⟨p, q⟩ := x
  have hκ := propKer_nonneg |r|
  have hW2 := wtd_nonneg 2 F
  have hW3 := wtd_nonneg 3 F
  have hT1 := triB_nonneg hκ hW3 hW2 hW3 (p, q)
  have hT2 := triB_nonneg hκ hW3 hW3 hW2 (p, q)
  by_cases hfast : p 2 ≠ 0 ∧ q 2 ≠ 0 ∧ (-(p + q)) 2 ≠ 0
  swap
  · have h0 := amp_zero_of_not_fast hF' hfast
    rw [nearTriadTerm_amp_zero 2 _ _ _ h0, nearTriadTerm_amp_zero 3 _ _ _ h0]
    simp only [mul_zero, sub_zero, norm_zero]
    positivity
  obtain ⟨hp3, hq3, hr3⟩ := hfast
  obtain ⟨hp, hq, hk⟩ := fast_ne hp3 hq3 hr3
  obtain ⟨e, L, u, he, hex, hu, hpat, hamp, hmx, hmn⟩ := exists_region hFr hp3 hq3 hr3
  have h1 := abs_nearTriadTerm_le (j := 2) (Or.inr rfl) (Or.inr rfl) r τ F F p q hmn hmx
  have h3 := norm_nearTriadTerm_three_le (Or.inr rfl) r τ F F hp hq hk hmn hmx
  have h2 := near_sum_le r hu hpat
  have hle1 := boxK_le_triB hκ hW3 hW2 hW3 he (p, q)
  have hle2 := boxK_le_triB hκ hW3 hW3 hW2 he (p, q)
  rw [hex, boxK_of_mem hu] at hle1 hle2
  obtain ⟨hK, hy, hl, htri, hyK, hlK⟩ := box_legs hu
  set P := ‖F p‖ * ‖F q‖ * ‖F (-(p + q))‖ with hP
  have hP0 : 0 ≤ P := by positivity
  set κ := propKer |r| L u with hκdef
  have hκ0 : 0 ≤ κ := hκ _ _
  set S := ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
    if NearT a b c p q then kerB 2 (r * Phi a b c p q) (minLeg u L) (absk L) else 0 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun c _ => by
      split_ifs
      · exact kerB_nonneg _ _ (minLeg_pos hu).le hK.le
      · exact le_rfl
  have hsig0 : 0 ≤ sigK (p, q) := by
    unfold sigK
    have := absSq_nonneg p
    have := absSq_nonneg q
    have := absSq_nonneg (p + q)
    simp only
    linarith
  have hsig : sigK (p, q) ≤ 3 * absk L ^ 2 := by
    obtain ⟨m1, m2, m3⟩ := hmx
    have s1 : absSq p ≤ absk L ^ 2 := by
      rw [← absk_sq]
      exact pow_le_pow_left₀ (absk_nonneg _) m1 2
    have s2 : absSq q ≤ absk L ^ 2 := by
      rw [← absk_sq]
      exact pow_le_pow_left₀ (absk_nonneg _) m2 2
    have s3 : absSq (p + q) ≤ absk L ^ 2 := by
      rw [← absk_sq]
      exact pow_le_pow_left₀ (absk_nonneg _) m3 2
    unfold sigK
    simp only
    linarith
  have hmain : ‖(sigK (p, q) : ℂ) * nearTriadTerm 2 (-1) r τ F F (p, q) -
      nearTriadTerm 3 (-1) r τ F F (p, q)‖ ≤ 520 * (minLeg u L ^ 2 * absk L ^ 6 * κ * P) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hsig0]
    have a1 : sigK (p, q) * ‖nearTriadTerm 2 (-1) r τ F F (p, q)‖ ≤
        3 * absk L ^ 2 * (S * P) := mul_le_mul hsig h1 (norm_nonneg _) (by positivity)
    have a2 : S * P ≤ 104 * minLeg u L ^ 2 * absk L ^ 4 * κ * P :=
      mul_le_mul_of_nonneg_right h2 hP0
    have a3 := mul_le_mul_of_nonneg_left a2 (by positivity : 0 ≤ 5 * absk L ^ 2)
    have e3 : 2 * absk L ^ 2 * S * P = 2 * absk L ^ 2 * (S * P) := by ring
    rw [e3] at h3
    calc _ ≤ 3 * absk L ^ 2 * (S * P) + 2 * absk L ^ 2 * (S * P) := add_le_add a1 h3
      _ = 5 * absk L ^ 2 * (S * P) := by ring
      _ ≤ _ := by
          refine a3.trans (le_of_eq ?_)
          ring
  refine hmain.trans ?_
  have hK3 : (0 : ℝ) ≤ absk L ^ 3 := by positivity
  simp only [wtd] at hle1 hle2
  unfold minLeg
  rcases le_total (absk u) (absk (L - u)) with h | h
  · rw [min_eq_left h]
    have hb : absk L ^ 3 * ‖F L‖ * (κ * (absk u ^ 2 * ‖F u‖ * (absk (L - u) ^ 3 * ‖F (L - u)‖))) =
        absk L ^ 3 * absk u ^ 2 * absk (L - u) ^ 3 * κ * P := by
      rw [← hamp]
      ring
    rw [hb] at hle1
    have h4 : absk L ^ 3 ≤ 8 * absk (L - u) ^ 3 := by
      have := pow_le_pow_left₀ hK.le (by linarith : absk L ≤ 2 * absk (L - u)) 3
      nlinarith
    have h5 := mul_le_mul_of_nonneg_left h4
      (by positivity : 0 ≤ absk u ^ 2 * absk L ^ 3 * (κ * P))
    calc 520 * (absk u ^ 2 * absk L ^ 6 * κ * P)
        = 520 * (absk u ^ 2 * absk L ^ 3 * (κ * P) * absk L ^ 3) := by ring
      _ ≤ 520 * (absk u ^ 2 * absk L ^ 3 * (κ * P) * (8 * absk (L - u) ^ 3)) := by gcongr
      _ = 4160 * (absk L ^ 3 * absk u ^ 2 * absk (L - u) ^ 3 * κ * P) := by ring
      _ ≤ 4160 * (triB (propKer |r|) (wtd 3 F) (wtd 2 F) (wtd 3 F) (p, q) +
            triB (propKer |r|) (wtd 3 F) (wtd 3 F) (wtd 2 F) (p, q)) := by linarith
  · rw [min_eq_right h]
    have hb : absk L ^ 3 * ‖F L‖ * (κ * (absk u ^ 3 * ‖F u‖ * (absk (L - u) ^ 2 * ‖F (L - u)‖))) =
        absk L ^ 3 * absk u ^ 3 * absk (L - u) ^ 2 * κ * P := by
      rw [← hamp]
      ring
    rw [hb] at hle2
    have h4 : absk L ^ 3 ≤ 8 * absk u ^ 3 := by
      have := pow_le_pow_left₀ hK.le (by linarith : absk L ≤ 2 * absk u) 3
      nlinarith
    have h5 := mul_le_mul_of_nonneg_left h4
      (by positivity : 0 ≤ absk (L - u) ^ 2 * absk L ^ 3 * (κ * P))
    calc 520 * (absk (L - u) ^ 2 * absk L ^ 6 * κ * P)
        = 520 * (absk (L - u) ^ 2 * absk L ^ 3 * (κ * P) * absk L ^ 3) := by ring
      _ ≤ 520 * (absk (L - u) ^ 2 * absk L ^ 3 * (κ * P) * (8 * absk u ^ 3)) := by gcongr
      _ = 4160 * (absk L ^ 3 * absk u ^ 3 * absk (L - u) ^ 2 * κ * P) := by ring
      _ ≤ 4160 * (triB (propKer |r|) (wtd 3 F) (wtd 2 F) (wtd 3 F) (p, q) +
            triB (propKer |r|) (wtd 3 F) (wtd 3 F) (wtd 2 F) (p, q)) := by linarith

/-! ### E. The near series -/

/-- The cyclic average of a summable family on triads (`rho`). -/
lemma tsum_cyc3 {b : Mode × Mode → ℂ} (h : Summable b) :
    Summable (fun x => b x + b (rho (rho x)) + b (rho x)) ∧
      ∑' x, (b x + b (rho (rho x)) + b (rho x)) = 3 * ∑' x, b x := by
  have s1 : Summable fun x => b (rho x) := rho.summable_iff.mpr h
  have s2 : Summable fun x => b (rho (rho x)) :=
    (rho.summable_iff (f := fun y => b (rho y))).mpr s1
  refine ⟨(h.add s2).add s1, ?_⟩
  have e1 : ∑' x, b (rho x) = ∑' x, b x := rho.tsum_eq b
  have e2 : ∑' x, b (rho (rho x)) = ∑' x, b x := by
    rw [rho.tsum_eq (fun y => b (rho y)), e1]
  rw [(h.add s2).tsum_add s1, h.tsum_add s2, e1, e2]
  ring

/-- **The near static series**: `‖Σ t‖ ≤ 416 √𝔐_P ‖F‖₂³` for `t = nearTri 2`, by `⅓` of the triad
sum. -/
theorem near_static_series (r τ : ℝ) {F : Field} (hF : MZ 2 F) (hFr : IsReal F)
    (hF' : PiF F = F) :
    Summable (nearTri 2 (-1) r τ F F F) ∧
      ‖∑' x, nearTri 2 (-1) r τ F F F x‖ ≤ 416 * (Real.sqrt (MomP |r|) * hnorm 2 F ^ 3) := by
  have hs : Summable (nearTri 2 (-1) r τ F F F) :=
    Summable.of_norm_bounded ((summable_nearMaj_two hF hF hF).mul_left 8)
      (norm_nearTri_le (by norm_num) (Or.inr rfl) r τ F F F)
  refine ⟨hs, ?_⟩
  obtain ⟨-, eT⟩ := tsum_cyc3 hs
  obtain ⟨l2, n2⟩ := wtd_l2_two hF
  have hW := wtd_nonneg 2 F
  obtain ⟨sB, bB⟩ := triB_facts (propKer_nonneg |r|) (sum_propKer_sq |r|) hW hW hW l2 l2 l2
  rw [n2] at bB
  have hN : ∀ x, ‖nearTri 2 (-1) r τ F F F x + nearTri 2 (-1) r τ F F F (rho (rho x)) +
      nearTri 2 (-1) r τ F F F (rho x)‖ ≤
      416 * triB (propKer |r|) (wtd 2 F) (wtd 2 F) (wtd 2 F) x :=
    fun x => static_point r τ hFr hF' x
  have h3 := tsum_of_norm_bounded (sB.hasSum.mul_left 416) hN
  rw [eT, norm_mul] at h3
  have e3 : ‖(3 : ℂ)‖ = 3 := by norm_num
  rw [e3] at h3
  have e4 : hnorm 2 F ^ 3 = hnorm 2 F * hnorm 2 F * hnorm 2 F := by ring
  rw [e4]
  linarith

/-- The gain of the near multiplier. -/
lemma nearCorrM_gain' (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    ‖nearCorrM (-1) r τ a b c p q‖ ≤ 1 / absSq (p + q) := by
  unfold nearCorrM
  split_ifs with h
  · exact norm_corrSym_le (Or.inr rfl) r τ a b c h.1
  · simpa using absSq_nonneg (p + q)

/-- The gain of the far multiplier. -/
lemma farCorrM_gain' (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    ‖farCorrM (-1) r τ a b c p q‖ ≤ 1 / absSq (p + q) := by
  unfold farCorrM
  split_ifs with h
  · exact norm_corrSym_le (Or.inr rfl) r τ a b c h.1
  · simpa using absSq_nonneg (p + q)

/-- The two heat slots of a gain multiplier are summable at `F ∈ H³`. -/
lemma heat_slots_summable {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    {F : Field} (hF : MZ 3 F) :
    (Summable fun x : Mode × Mode => tripT m (lapF F) F (lapF (lapF F)) x.1 x.2) ∧
      Summable fun x : Mode × Mode => tripT m F (lapF F) (lapF (lapF F)) x.1 x.2 := by
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  obtain ⟨l2, -⟩ := wtd_l2 hF (n := 2) (by norm_num)
  obtain ⟨l3, -⟩ := wtd_l2 hF (n := 3) (by norm_num)
  have l1 := (summable_wtd_one hF).1
  have ln : Summable fun k => ‖F k‖ := summable_wiener hF2.inH
  have n0 : ∀ k, 0 ≤ ‖F k‖ := fun k => norm_nonneg _
  have w1 := wtd_nonneg 1 F
  have w2 := wtd_nonneg 2 F
  have w3 := wtd_nonneg 3 F
  obtain ⟨s1, -⟩ := summable_tri_second w3 n0 w2 l3 l2 ln
  obtain ⟨s2, -⟩ := summable_tri_second w2 w1 w2 l2 l2 l1
  obtain ⟨s3, -⟩ := summable_tri_first w1 w2 w2 l1 l2 l2
  obtain ⟨s4, -⟩ := summable_tri_first n0 w3 w2 ln l3 l2
  constructor
  · refine Summable.of_norm_bounded ((s1.add s2).mul_left 8) fun x => ?_
    obtain ⟨p, q⟩ := x
    refine (norm_tripT_gain_lap hm (lapF F) F (lapF F) p q).trans (le_of_eq ?_)
    simp only [norm_lapF, wtd, ← absk_sq]
    ring
  · refine Summable.of_norm_bounded ((s3.add s4).mul_left 8) fun x => ?_
    obtain ⟨p, q⟩ := x
    refine (norm_tripT_gain_lap hm F (lapF F) (lapF F) p q).trans (le_of_eq ?_)
    simp only [norm_lapF, wtd, ← absk_sq]
    ring

/-- The near heat at a triad: both input heats of one rooting. -/
def heatN (r τ : ℝ) (F : Field) (x : Mode × Mode) : ℂ :=
  tripT (nearCorrM (-1) r τ) (lapF F) F (lapF (lapF F)) x.1 x.2 +
    tripT (nearCorrM (-1) r τ) F (lapF F) (lapF (lapF F)) x.1 x.2

/-- `(x_a + x_b) f₂(x_c) = Σ f₂(x_c) − f₃(x_c)`, at a rooting. -/
lemma heatN_eq (r τ : ℝ) (F : Field) (x : Mode × Mode) :
    heatN r τ F x = (sigK x : ℂ) * nearTri 2 (-1) r τ F F F x - nearTri 3 (-1) r τ F F F x := by
  simp only [heatN, nearTri, sigK, tripT_lapF_left, tripT_lapF_mid, tripT_lapF_right,
    Nat.cast_ofNat, sobWeight_two, sobWeight_three]
  push_cast
  ring

/-- The cyclic sum of the near heat. -/
lemma heatN_cyc (r τ : ℝ) (F : Field) (x : Mode × Mode) :
    heatN r τ F x + heatN r τ F (rho (rho x)) + heatN r τ F (rho x) =
      (sigK x : ℂ) * nearTriadTerm 2 (-1) r τ F F x - nearTriadTerm 3 (-1) r τ F F x := by
  rw [heatN_eq, heatN_eq, heatN_eq, sigK_rho, sigK_rho]
  unfold nearTriadTerm
  ring

/-- **The near heat series**: `‖Σ heatN‖ ≤ 8320 √𝔐_P ‖F‖₂ ‖F‖₃²`. -/
theorem near_heat_series (r τ : ℝ) {F : Field} (hF : MZ 3 F) (hFr : IsReal F)
    (hF' : PiF F = F) :
    Summable (heatN r τ F) ∧
      ‖∑' x, heatN r τ F x‖ ≤ 8320 * (Real.sqrt (MomP |r|) * (hnorm 2 F * hnorm 3 F ^ 2)) := by
  obtain ⟨h1, h2⟩ := heat_slots_summable (nearCorrM_gain' r τ) hF
  have hs : Summable (heatN r τ F) := h1.add h2
  refine ⟨hs, ?_⟩
  obtain ⟨-, eT⟩ := tsum_cyc3 hs
  obtain ⟨l2, n2⟩ := wtd_l2 hF (n := 2) (by norm_num)
  obtain ⟨l3, n3⟩ := wtd_l2 hF (n := 3) (by norm_num)
  push_cast at n2 n3
  have w2 := wtd_nonneg 2 F
  have w3 := wtd_nonneg 3 F
  obtain ⟨s1, b1⟩ := triB_facts (propKer_nonneg |r|) (sum_propKer_sq |r|) w3 w2 w3 l3 l2 l3
  obtain ⟨s2, b2⟩ := triB_facts (propKer_nonneg |r|) (sum_propKer_sq |r|) w3 w3 w2 l3 l3 l2
  rw [n2, n3] at b1 b2
  have hN : ∀ x, ‖heatN r τ F x + heatN r τ F (rho (rho x)) + heatN r τ F (rho x)‖ ≤
      4160 * (triB (propKer |r|) (wtd 3 F) (wtd 2 F) (wtd 3 F) x +
        triB (propKer |r|) (wtd 3 F) (wtd 3 F) (wtd 2 F) x) := fun x => by
    rw [heatN_cyc]
    exact heat_point r τ hFr hF' x
  have h3 := tsum_of_norm_bounded ((s1.hasSum.add s2.hasSum).mul_left 4160) hN
  rw [eT, norm_mul] at h3
  have e3 : ‖(3 : ℂ)‖ = 3 := by norm_num
  rw [e3] at h3
  have e4 : hnorm 2 F * hnorm 3 F ^ 2 = hnorm 3 F * hnorm 2 F * hnorm 3 F := by ring
  have e5 : hnorm 3 F * hnorm 3 F * hnorm 2 F = hnorm 3 F * hnorm 2 F * hnorm 3 F := by ring
  rw [e5] at b2
  rw [e4]
  linarith

/-! ### F. The far series -/

/-- `|k| ‖m‖ ≤ q^{−1/2}` on the far set: `√(K⁴ + q²) ≥ K √q`. -/
lemma norm_farCorrM_root {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (a b c : Sgn) {p q : Mode}
    (hk : p + q ≠ 0) :
    ‖farCorrM (-1) r τ a b c p q‖ ≤ |r| ^ (-(1 / 2) : ℝ) / absk (p + q) := by
  have hq : 0 < |r| := abs_pos.mpr hr
  have hK : 0 < absk (p + q) := lt_of_lt_of_le one_pos (one_le_absk hk)
  have hθ : 0 < |r| ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hq _
  unfold farCorrM
  split_ifs with h
  · rw [norm_corrSym (Or.inr rfl)]
    set s := Real.sqrt |r| with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hq
    have hs2 : s ^ 2 = |r| := Real.sq_sqrt hq.le
    have e : |r| ^ (-(1 / 2) : ℝ) = 1 / s := by
      rw [Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow, one_div]
    set K := absk (p + q) with hKdef
    have hA : absSq (p + q) = K ^ 2 := (absk_sq _).symm
    have hΦ : |r| ≤ |r * Phi a b c p q| := by
      rw [abs_mul]
      nlinarith [h.2]
    have hz : |r| ^ 2 ≤ (r * Phi a b c p q) ^ 2 := by
      rw [← sq_abs (r * Phi a b c p q)]
      exact pow_le_pow_left₀ hq.le hΦ 2
    have hle : K * s ≤ Real.sqrt (absSq (p + q) ^ 2 + (r * Phi a b c p q) ^ 2) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [hA, mul_pow, hs2]
      nlinarith [sq_nonneg (K ^ 2 - |r|), sq_nonneg (K ^ 2), mul_pos (pow_pos hK 2) hq]
    rw [e, div_div, mul_comm s K]
    exact one_div_le_one_div_of_le (by positivity) hle
  · simpa using by positivity

/-- A far rooting at the test `A²Z`: `|k|⁴ ‖m‖ ≤ q^{−1/2} |k|³`. -/
lemma far_tri_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (X Y Z : Field) (p q : Mode) :
    ‖tripT (farCorrM (-1) r τ) X Y (lapF (lapF Z)) p q‖ ≤
      8 * |r| ^ (-(1 / 2) : ℝ) * ((absk p + absk q) * absk (-(p + q)) ^ 3 *
        (‖X p‖ * ‖Y q‖ * ‖Z (-(p + q))‖)) := by
  have hq : 0 < |r| := abs_pos.mpr hr
  have hθ : 0 < |r| ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hq _
  have hP := absk_nonneg p
  have hQ := absk_nonneg q
  have hK0 := absk_nonneg (-(p + q))
  by_cases hk : p + q = 0
  · rw [tripT_zero_of_add_eq_zero _ _ _ _ hk, norm_zero]
    positivity
  have hK : 0 < absk (p + q) := lt_of_lt_of_le one_pos (one_le_absk hk)
  have h := norm_tripT_le_of_le (κ := |r| ^ (-(1 / 2) : ℝ) / absk (p + q)) (by positivity)
    (fun a b c => norm_farCorrM_root hr τ a b c hk) X Y (lapF (lapF Z))
  refine h.trans (le_of_eq ?_)
  have e : ‖lapF (lapF Z) (-(p + q))‖ = absk (p + q) ^ 4 * ‖Z (-(p + q))‖ := by
    rw [norm_lapF, norm_lapF, absSq_neg, ← absk_sq]
    ring
  rw [e, absk_neg]
  field_simp

/-- **The far static series**: `‖Σ‖ ≤ 32 c₄ q^{−1/2} ‖F‖₂³`. -/
theorem far_static_series {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {F : Field} (hF : MZ 2 F) :
    (Summable fun x : Mode × Mode =>
      tripT (farCorrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2) ∧
      ‖∑' x : Mode × Mode, tripT (farCorrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2‖ ≤
        32 * c4 * |r| ^ (-(1 / 2) : ℝ) * hnorm 2 F ^ 3 := by
  have hq : 0 < |r| := abs_pos.mpr hr
  set θ := |r| ^ (-(1 / 2) : ℝ) with hθdef
  have hθ : 0 ≤ θ := Real.rpow_nonneg hq.le _
  obtain ⟨l2, n2⟩ := wtd_l2_two hF
  have ln : Summable fun k => ‖F k‖ := summable_wiener hF.inH
  have n0 : ∀ k, 0 ≤ ‖F k‖ := fun k => norm_nonneg _
  have w2 := wtd_nonneg 2 F
  obtain ⟨s1, b1⟩ := summable_tri_second w2 n0 w2 l2 l2 ln
  obtain ⟨s2, b2⟩ := summable_tri_first n0 w2 w2 ln l2 l2
  rw [n2] at b1 b2
  have hB : ∀ x : Mode × Mode, ‖tripT (farCorrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2‖ ≤
      16 * θ * (wtd 2 F x.1 * ‖F x.2‖ * wtd 2 F (-(x.1 + x.2)) +
        ‖F x.1‖ * wtd 2 F x.2 * wtd 2 F (-(x.1 + x.2))) := by
    rintro ⟨p, q⟩
    refine (far_tri_le hr τ F F F p q).trans ?_
    simp only [wtd]
    set P := absk p
    set Q := absk q
    set K := absk (-(p + q))
    have hP : 0 ≤ P := absk_nonneg _
    have hQ : 0 ≤ Q := absk_nonneg _
    have hK : 0 ≤ K := absk_nonneg _
    have hKle : K ≤ P + Q := by
      rw [show K = absk (-(p + q)) from rfl, absk_neg]
      exact absk_add_le p q
    set A := ‖F p‖ * ‖F q‖ * ‖F (-(p + q))‖ with hA
    have hA0 : 0 ≤ A := by positivity
    have h1 : (P + Q) * K ^ 3 ≤ 2 * (P ^ 2 + Q ^ 2) * K ^ 2 := by
      have h2 : (P + Q) * K ≤ 2 * (P ^ 2 + Q ^ 2) := by nlinarith [sq_nonneg (P - Q)]
      have := mul_le_mul_of_nonneg_right h2 (sq_nonneg K)
      calc (P + Q) * K ^ 3 = (P + Q) * K * K ^ 2 := by ring
        _ ≤ _ := this
    calc 8 * θ * ((P + Q) * K ^ 3 * A) ≤ 8 * θ * (2 * (P ^ 2 + Q ^ 2) * K ^ 2 * A) := by gcongr
      _ = _ := by
          rw [hA]
          ring
  have hG := (s1.add s2).mul_left (16 * θ)
  have hS := Summable.of_norm_bounded hG hB
  refine ⟨hS, ?_⟩
  refine (tsum_of_norm_bounded hG.hasSum hB).trans ?_
  rw [tsum_mul_left, s1.tsum_add s2]
  have hw := wiener_le hF
  have hb := hnorm_nonneg 2 F
  change 16 * θ * (∑' x : Mode × Mode, wtd 2 F x.1 * ‖F x.2‖ * wtd 2 F (-(x.1 + x.2)) +
    ∑' x : Mode × Mode, ‖F x.1‖ * wtd 2 F x.2 * wtd 2 F (-(x.1 + x.2))) ≤ _
  have h3 : wiener F * (hnorm 2 F * hnorm 2 F) ≤ c4 * hnorm 2 F * (hnorm 2 F * hnorm 2 F) :=
    mul_le_mul_of_nonneg_right hw (by positivity)
  have b1' : ∑' x : Mode × Mode, wtd 2 F x.1 * ‖F x.2‖ * wtd 2 F (-(x.1 + x.2)) ≤
      wiener F * (hnorm 2 F * hnorm 2 F) := b1
  have b2' : ∑' x : Mode × Mode, ‖F x.1‖ * wtd 2 F x.2 * wtd 2 F (-(x.1 + x.2)) ≤
      wiener F * (hnorm 2 F * hnorm 2 F) := b2
  have h4 := add_le_add (b1'.trans h3) (b2'.trans h3)
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 16 * θ)
  refine h5.trans (le_of_eq ?_)
  ring

/-- The far heat at a triad. -/
def heatB (r τ : ℝ) (F : Field) (x : Mode × Mode) : ℂ :=
  tripT (farCorrM (-1) r τ) (lapF F) F (lapF (lapF F)) x.1 x.2 +
    tripT (farCorrM (-1) r τ) F (lapF F) (lapF (lapF F)) x.1 x.2

/-- **The far heat series**: `‖Σ heatB‖ ≤ 32 c₄ q^{−1/2} ‖F‖₂ ‖F‖₃²`. -/
theorem far_heat_series {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {F : Field} (hF : MZ 3 F) :
    Summable (heatB r τ F) ∧
      ‖∑' x, heatB r τ F x‖ ≤ 32 * c4 * |r| ^ (-(1 / 2) : ℝ) * (hnorm 2 F * hnorm 3 F ^ 2) := by
  have hq : 0 < |r| := abs_pos.mpr hr
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  set θ := |r| ^ (-(1 / 2) : ℝ) with hθdef
  have hθ : 0 ≤ θ := Real.rpow_nonneg hq.le _
  obtain ⟨hS1, hS2⟩ := heat_slots_summable (farCorrM_gain' r τ) hF
  refine ⟨hS1.add hS2, ?_⟩
  obtain ⟨l2, n2⟩ := wtd_l2 hF (n := 2) (by norm_num)
  obtain ⟨l3, n3⟩ := wtd_l2 hF (n := 3) (by norm_num)
  push_cast at n2 n3
  obtain ⟨l1, b0⟩ := summable_wtd_one hF
  have ln : Summable fun k => ‖F k‖ := summable_wiener hF2.inH
  have n0 : ∀ k, 0 ≤ ‖F k‖ := fun k => norm_nonneg _
  have w1 := wtd_nonneg 1 F
  have w2 := wtd_nonneg 2 F
  have w3 := wtd_nonneg 3 F
  obtain ⟨s1, b1⟩ := summable_tri_second w3 n0 w3 l3 l3 ln
  obtain ⟨s2, b2⟩ := summable_tri_second w2 w1 w3 l2 l3 l1
  obtain ⟨s3, b3⟩ := summable_tri_first w1 w2 w3 l1 l2 l3
  obtain ⟨s4, b4⟩ := summable_tri_first n0 w3 w3 ln l3 l3
  rw [n3] at b1 b4
  rw [n2, n3] at b2 b3
  have hL : ∀ x : Mode × Mode, ‖tripT (farCorrM (-1) r τ) (lapF F) F (lapF (lapF F)) x.1 x.2‖ ≤
      8 * θ * (wtd 3 F x.1 * ‖F x.2‖ * wtd 3 F (-(x.1 + x.2)) +
        wtd 2 F x.1 * wtd 1 F x.2 * wtd 3 F (-(x.1 + x.2))) := by
    rintro ⟨p, q⟩
    refine (far_tri_le hr τ (lapF F) F F p q).trans (le_of_eq ?_)
    simp only [norm_lapF, wtd, ← absk_sq]
    ring
  have hR : ∀ x : Mode × Mode, ‖tripT (farCorrM (-1) r τ) F (lapF F) (lapF (lapF F)) x.1 x.2‖ ≤
      8 * θ * (wtd 1 F x.1 * wtd 2 F x.2 * wtd 3 F (-(x.1 + x.2)) +
        ‖F x.1‖ * wtd 3 F x.2 * wtd 3 F (-(x.1 + x.2))) := by
    rintro ⟨p, q⟩
    refine (far_tri_le hr τ F (lapF F) F p q).trans (le_of_eq ?_)
    simp only [norm_lapF, wtd, ← absk_sq]
    ring
  have hG := ((((s1.add s2).mul_left (8 * θ))).add ((s3.add s4).mul_left (8 * θ)))
  have hN : ∀ x, ‖heatB r τ F x‖ ≤ _ := fun x => (norm_add_le _ _).trans (add_le_add (hL x) (hR x))
  refine (tsum_of_norm_bounded hG.hasSum hN).trans ?_
  rw [((s1.add s2).mul_left (8 * θ)).tsum_add ((s3.add s4).mul_left (8 * θ)), tsum_mul_left,
    tsum_mul_left, s1.tsum_add s2, s3.tsum_add s4]
  set b := hnorm 2 F with hb
  set c := hnorm 3 F with hc
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have hc0 : 0 ≤ c := hnorm_nonneg _ _
  have hw : (∑' k, ‖F k‖) ≤ c4 * b := wiener_le hF2
  have hc4 := c4_pos
  have t1 : (∑' k, ‖F k‖) * (c * c) ≤ c4 * b * (c * c) :=
    mul_le_mul_of_nonneg_right hw (by positivity)
  have t2 : (∑' k, wtd 1 F k) * (b * c) ≤ c4 * c * (b * c) :=
    mul_le_mul_of_nonneg_right b0 (by positivity)
  have hsum := add_le_add (add_le_add b1 b2) (add_le_add b3 b4)
  have h5 : (∑' k, ‖F k‖) * (c * c) + (∑' k, wtd 1 F k) * (b * c) +
      ((∑' k, wtd 1 F k) * (b * c) + (∑' k, ‖F k‖) * (c * c)) ≤ 4 * c4 * (b * c ^ 2) := by
    nlinarith [t1, t2]
  have h6 := mul_le_mul_of_nonneg_left (hsum.trans h5) (by positivity : 0 ≤ 8 * θ)
  calc _ = 8 * θ * ((∑' x : Mode × Mode, wtd 3 F x.1 * ‖F x.2‖ * wtd 3 F (-(x.1 + x.2))) +
          (∑' x : Mode × Mode, wtd 2 F x.1 * wtd 1 F x.2 * wtd 3 F (-(x.1 + x.2))) +
          ((∑' x : Mode × Mode, wtd 1 F x.1 * wtd 2 F x.2 * wtd 3 F (-(x.1 + x.2))) +
            (∑' x : Mode × Mode, ‖F x.1‖ * wtd 3 F x.2 * wtd 3 F (-(x.1 + x.2))))) := by ring
    _ ≤ _ := h6
    _ = _ := by ring

/-! ### G. The two proper remainders -/

/-- The near/far split at a rooting. -/
lemma tripT_corrM_split (r τ : ℝ) (X Y Z : Field) (p q : Mode) :
    tripT (corrM (-1) r τ) X Y Z p q =
      tripT (nearCorrM (-1) r τ) X Y Z p q + tripT (farCorrM (-1) r τ) X Y Z p q := by
  simp only [tripT, corrM_eq_add, add_mul, Finset.sum_add_distrib]

/-- The test `A²F` of a near rooting is the weight of `nearTri 2`. -/
lemma tripT_near_lap_lap (r τ : ℝ) (F : Field) (x : Mode × Mode) :
    tripT (nearCorrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2 = nearTri 2 (-1) r τ F F F x := by
  simp only [nearTri, tripT_lapF_right, Nat.cast_ofNat, sobWeight_two]
  push_cast
  ring

/-- **The static remainder of the weight-two cubic** (role 16, "E2 proper static 1/128"; TeX
"static coercivity … separate estimates"): for real fast `F ∈ H²`,
`|E⁰₂| ≤ cStat2 (P(q) + q^{−1/2}) ‖F‖₂³`. -/
theorem cubicE_two_static_le_proved {r : ℝ} (hr : 1 ≤ |r|) (τ : ℝ) {F : Field} (hF : MZ 2 F)
    (hFr : IsReal F) (hF' : PiF F = F) :
    |cubicE 2 (-1) r τ F| ≤ cStat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) * hnorm 2 F ^ 3 := by
  have hq : 0 < |r| := by linarith
  have hr0 : r ≠ 0 := abs_pos.mp hq
  have hF1 : MZ 1 F := hF.mono' (by norm_num)
  obtain ⟨sN, bN⟩ := near_static_series r τ hF hFr hF'
  obtain ⟨sB, bB⟩ := far_static_series hr0 τ hF
  have eN : (fun x : Mode × Mode => tripT (nearCorrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2) =
      nearTri 2 (-1) r τ F F F := funext (tripT_near_lap_lap r τ F)
  have sN' : Summable fun x : Mode × Mode =>
      tripT (nearCorrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2 := by
    rw [eN]
    exact sN
  have hsplit : ∀ x : Mode × Mode, tripT (corrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2 =
      tripT (nearCorrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2 +
        tripT (farCorrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2 :=
    fun x => tripT_corrM_split r τ _ _ _ _ _
  have hs : Summable fun x : Mode × Mode =>
      tripT (corrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2 := by
    rw [funext hsplit]
    exact sN'.add sB
  have hl2 : Summable fun p => ‖F p‖ ^ 2 := summable_norm_sq_of_inH (hF.inH.mono (by norm_num))
  have hgr : Summable fun p => (absk p * ‖F p‖) ^ 2 :=
    hF1.inH.congr fun p => by rw [sobWeight_one, mul_pow, absk_sq]
  have hE : cubicE 2 (-1) r τ F = (∑' x : Mode × Mode,
      tripT (corrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2).re := by
    unfold cubicE corr
    rw [Nat.cast_ofNat]
    exact pair_two_eq_re_tsum_gain (corrM_gain (-1) r τ (Or.inr rfl)) hFr hl2 hl2 (Or.inl hgr) hs
  have ht : (∑' x : Mode × Mode, tripT (corrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2) =
      (∑' x, nearTri 2 (-1) r τ F F F x) + ∑' x : Mode × Mode,
        tripT (farCorrM (-1) r τ) F F (lapF (lapF F)) x.1 x.2 := by
    rw [tsum_congr hsplit, sN'.tsum_add sB, eN]
  rw [hE, ht]
  refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
  set S := Real.sqrt (MomP |r|) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set θ := |r| ^ (-(1 / 2) : ℝ) with hθdef
  have hθ : 0 ≤ θ := Real.rpow_nonneg hq.le _
  set w := |r| ^ (-(3 : ℝ) / 4) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hq.le _
  have hc4 := c4_pos
  have hb3 : 0 ≤ hnorm 2 F ^ 3 := pow_nonneg (hnorm_nonneg _ _) 3
  have hconst : 416 * S + 32 * c4 * θ ≤ cStat2 * (nearP |r| + θ) := by
    unfold cStat2 nearP
    rw [← hS, ← hw]
    nlinarith [mul_nonneg hc4.le hS0, mul_nonneg hc4.le hw0, mul_nonneg hc4.le hθ]
  calc _ ≤ 416 * (S * hnorm 2 F ^ 3) + 32 * c4 * θ * hnorm 2 F ^ 3 := add_le_add bN bB
    _ = (416 * S + 32 * c4 * θ) * hnorm 2 F ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst hb3

/-- The heat as the near and far series. -/
lemma cubicHeat2_eq (r τ : ℝ) {F : Field} (hF : MZ 3 F) (hFr : IsReal F)
    (sN : Summable (heatN r τ F)) (sB : Summable (heatB r τ F)) :
    cubicHeat2 r τ F = ((∑' x, heatN r τ F x) + ∑' x, heatB r τ F x).re := by
  have hF1 : MZ 1 F := hF.mono' (by norm_num)
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  obtain ⟨hs1, hs2⟩ := heat_slots_summable (corrM_gain (-1) r τ (Or.inr rfl)) hF
  have hl2 : Summable fun p => ‖F p‖ ^ 2 := summable_norm_sq_of_inH (hF.inH.mono (by norm_num))
  have hgr : Summable fun p => (absk p * ‖F p‖) ^ 2 :=
    hF1.inH.congr fun p => by rw [sobWeight_one, mul_pow, absk_sq]
  have hal := (lapF_l2 hF2.inH).1
  have e1 := pair_two_eq_re_tsum_gain (corrM_gain (-1) r τ (Or.inr rfl)) hFr hal hl2
    (Or.inr hgr) hs1
  have e2 := pair_two_eq_re_tsum_gain (corrM_gain (-1) r τ (Or.inr rfl)) hFr hl2 hal
    (Or.inl hgr) hs2
  have hsplit : ∀ x : Mode × Mode, tripT (corrM (-1) r τ) (lapF F) F (lapF (lapF F)) x.1 x.2 +
      tripT (corrM (-1) r τ) F (lapF F) (lapF (lapF F)) x.1 x.2 =
      heatN r τ F x + heatB r τ F x := fun x => by
    rw [tripT_corrM_split, tripT_corrM_split]
    unfold heatN heatB
    ring
  have ht := hs1.tsum_add hs2
  rw [tsum_congr hsplit, sN.tsum_add sB] at ht
  rw [ht]
  unfold cubicHeat2 corr
  rw [e1, e2, Complex.add_re]

/-- **Both input heats of the weight-two cubic** (role 17, "E2 BOTH input heats"; slots `H²` on
the small leg and `H³` on the two others): for real fast `F ∈ H³`,
`|E₂_heat| ≤ cHeat2 (P(q) + q^{−1/2}) ‖F‖₂ ‖F‖₃²`. -/
theorem cubicHeat2_le_proved {r : ℝ} (hr : 1 ≤ |r|) (τ : ℝ) {F : Field} (hF : MZ 3 F)
    (hFr : IsReal F) (hF' : PiF F = F) :
    |cubicHeat2 r τ F| ≤
      cHeat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) * hnorm 2 F * hnorm 3 F ^ 2 := by
  have hq : 0 < |r| := by linarith
  have hr0 : r ≠ 0 := abs_pos.mp hq
  obtain ⟨sN, bN⟩ := near_heat_series r τ hF hFr hF'
  obtain ⟨sB, bB⟩ := far_heat_series hr0 τ hF
  rw [cubicHeat2_eq r τ hF hFr sN sB]
  refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
  set S := Real.sqrt (MomP |r|) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set θ := |r| ^ (-(1 / 2) : ℝ) with hθdef
  have hθ : 0 ≤ θ := Real.rpow_nonneg hq.le _
  set w := |r| ^ (-(3 : ℝ) / 4) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hq.le _
  have hc4 := c4_pos
  have hbc : 0 ≤ hnorm 2 F * hnorm 3 F ^ 2 :=
    mul_nonneg (hnorm_nonneg _ _) (pow_nonneg (hnorm_nonneg _ _) 2)
  have hconst : 8320 * S + 32 * c4 * θ ≤ cHeat2 * (nearP |r| + θ) := by
    unfold cHeat2 nearP
    rw [← hS, ← hw]
    nlinarith [mul_nonneg hc4.le hS0, mul_nonneg hc4.le hw0, mul_nonneg hc4.le hθ]
  calc _ ≤ 8320 * (S * (hnorm 2 F * hnorm 3 F ^ 2)) +
        32 * c4 * θ * (hnorm 2 F * hnorm 3 F ^ 2) := add_le_add bN bB
    _ = (8320 * S + 32 * c4 * θ) * (hnorm 2 F * hnorm 3 F ^ 2) := by ring
    _ ≤ cHeat2 * (nearP |r| + θ) * (hnorm 2 F * hnorm 3 F ^ 2) :=
        mul_le_mul_of_nonneg_right hconst hbc
    _ = _ := by ring

end OVNS.Quant.H2

end
