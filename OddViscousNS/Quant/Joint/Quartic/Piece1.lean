import OddViscousNS.Quant.Joint.Quartic.Piece2

/-!
# `C_{4,1}` on a joint piece (step J5, node N11)

J3-v2 §5, with `ε = min(1/64, 1/(8 + ln R))` (`epsR`), fixed before the evolution.

`quartic_one_piece`: on a prefix with the caps, the near share `P(q) ≤ Q^{−1/3}`, and the threshold
`qOneFull A ≤ q`, `A = 2²⁶ e⁵/η²`:
* `|C_{4,1}| ≤ η a²`;
* `|Rem| ≤ η b² + η h b`, `h = ‖H_ψ‖₁`: "the nonlinear debit" and "the extra genuine debit".

`q^{−1+ε}` is handled by J6's `rpow_eps_le`, `q^{−1+ε} ≤ e⁵ (1/q + R⁻⁵)`.  That needs the threshold
`T = A thrOne` to lie below `R⁵` (J3-v2: "at a sufficiently large absolute `R₀` it lies in
`[R³, R⁵]`"), which holds on scaled caps, but `H1EnergyJoint` quantifies over all caps.  So
`qOneFull` has one more term, `extraOne T R = T²` when `T > R⁵`, `0` otherwise: for `q ≥ T²`,
`q^{−1+ε} ≤ 1/T`.  On scaled caps at large `R` the term is `0` (`thrOne_le_pow5`), and
`qOneFull_below` is `JointBelow`.  So `ε` costs nothing.

**The slow direction `N_S` in `H¹`** uses `hSrc`, of size `W B ≍ R^{7/2}`; J3-v2 has `R³` through
`M_∞ b_S`.  This row, `2 ‖N_S‖₁ L`, has degree `(1, 7/2)` against the top `(1, 4)` of `m₁`: no loss.
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {X R r η R₀ : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps} {s t : ℝ}

/-- J3-v2's `ε`. -/
def epsR (R : ℝ) : ℝ := min (1 / 64) (1 / (8 + Real.log R))

lemma epsR_pos (hR : 1 ≤ R) : 0 < epsR R := by
  have := Real.log_nonneg hR
  unfold epsR
  exact lt_min (by norm_num) (by positivity)

lemma epsR_le (R : ℝ) : epsR R ≤ 1 := (min_le_left _ _).trans (by norm_num)

lemma epsR_mul (hR : 1 ≤ R) : epsR R * (8 + Real.log R) ≤ 1 := by
  have h := Real.log_nonneg hR
  have h1 : epsR R ≤ 1 / (8 + Real.log R) := min_le_right _ _
  have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ 8 + Real.log R)
  have e : 1 / (8 + Real.log R) * (8 + Real.log R) = 1 := by field_simp
  linarith

lemma sqrt_epsR_le (hR : 1 ≤ R) : Real.sqrt (9 + 4 / epsR R) ≤ logE R := by
  have h := Real.log_nonneg hR
  have hε := epsR_pos hR
  have h1 : 1 / epsR R ≤ 72 + Real.log R := by
    unfold epsR
    rcases min_choice ((1 : ℝ) / 64) (1 / (8 + Real.log R)) with e | e <;> rw [e]
    · norm_num
      linarith
    · rw [one_div_one_div]
      linarith
  have h2 : 4 / epsR R = 4 * (1 / epsR R) := by ring
  unfold logE
  rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by positivity), h2]
  nlinarith only [h1, h]

/-- The extra term of the threshold: only off the scaled caps. -/
def extraOne (T R : ℝ) : ℝ := if T ≤ R ^ 5 then 0 else T ^ 2

/-- **The whole threshold of `C_{4,1}`.** -/
def qOneFull (A X R : ℝ) (caps : Caps) : ℝ :=
  A * thrOne X R caps + extraOne (A * thrOne X R caps) R + flrTwo R caps

lemma extraOne_nonneg (T R : ℝ) : 0 ≤ extraOne T R := by
  unfold extraOne
  split_ifs
  · exact le_rfl
  · positivity

/-- On scaled caps the threshold is below `R⁵`. -/
theorem thrOne_le_pow5 {A : ℝ} (hA : 0 ≤ A) {K c : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c) :
    ∃ R₁ : ℝ, ∀ X R : ℝ, JDom R₁ X R → ∀ caps : Caps, CapsScaledJ K c X R caps →
      A * thrOne X R caps ≤ R ^ 5 := by
  obtain ⟨C, c', R₂, hC, hm⟩ := (deg_thrOne.const_mul hA) K c hK hc
  set C₁ := max C 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  set E₁ := max c' 0 with hE₁
  have hE₁0 : 0 ≤ E₁ := le_max_right _ _
  refine ⟨max R₂ (max (C₁ ^ (4 : ℝ)) (Real.exp (Real.exp (4 * E₁)))), fun X R hdom caps hcaps => ?_⟩
  have h1 : R₂ ≤ R := (le_max_left _ _).trans hdom.R₀_le
  have h2 : C₁ ^ (4 : ℝ) ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans hdom.R₀_le
  have h3 : Real.exp (Real.exp (4 * E₁)) ≤ R :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hdom.R₀_le
  have hd2 : JDom R₂ X R := hdom.mono (le_max_left _ _)
  obtain ⟨-, hle⟩ := hm X R hd2 caps hcaps
  have hR1 := hdom.one_lt_R
  have hR0 := hdom.R_pos
  have hl := hdom.loglog_pos
  have hlog : Real.exp (4 * E₁) ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos _) h3
    rwa [Real.log_exp] at this
  have hlog2 : 4 * E₁ ≤ Real.log (Real.log R) := by
    have := Real.log_le_log (Real.exp_pos _) hlog
    rwa [Real.log_exp] at this
  have hEx : Ex c' R ≤ R ^ ((1 : ℝ) / 4) := by
    refine Ex_le_rpow hR1 hl ?_
    have : c' ≤ E₁ := le_max_left _ _
    linarith
  have hC' : C ≤ R ^ ((1 : ℝ) / 4) := by
    refine (le_max_left C 1).trans (le_rpow_of_large (by linarith) (by norm_num) ?_)
    have e : (1 : ℝ) / (1 / 4) = 4 := by norm_num
    rw [e]
    exact h2
  have ht := hdom.trial_le (C := C) (E := Ex c' R) (Ex_pos _ _).le hC' hEx
  have e1 : C * (jointU X ^ (1 : ℝ) * R ^ (3 : ℝ)) * Ex c' R = C * jointQ X R * Ex c' R := by
    rw [Real.rpow_one, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rfl
  rw [e1] at hle
  have h4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR1.le (by norm_num)
  exact hle.trans (ht.trans h4)

/-- **The row of `C_{4,1}` with its extra term is `JointBelow`.** -/
theorem qOneFull_below {A : ℝ} (hA : 0 ≤ A) : JointBelow fun X R caps ↦ qOneFull A X R caps := by
  intro K c hK hc
  obtain ⟨C, C₀, R₂, hb⟩ := qOne_below hA K c hK hc
  obtain ⟨R₁, h5⟩ := thrOne_le_pow5 hA hK hc
  refine ⟨C, C₀, max R₂ R₁, fun X R hdom caps hcaps => ?_⟩
  have h1 := hb X R (hdom.mono (le_max_left _ _)) caps hcaps
  have h2 := h5 X R (hdom.mono (le_max_right _ _)) caps hcaps
  have e : extraOne (A * thrOne X R caps) R = 0 := ite_eq_left h2
  simp only [qOneFull, e, add_zero]
  exact h1

/-- **The near share at weight one**: `κ₁ T₀ ≤ η/4`. -/
lemma kap1_key {Z T₀ ε A T : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hq1 : 1 ≤ |r|) (hR : 1 ≤ R)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (hε : ε * (8 + Real.log R) ≤ 1) (hZ : 0 ≤ Z)
    (hP : nearP |r| ≤ Z) (hT₀ : 0 ≤ T₀) (hA : A = 2 ^ 26 * Real.exp 5 / η ^ 2)
    (hT : A * (T₀ * Z) ≤ T) (h2 : T ≤ |r|) (h3 : T ≤ R ^ 5 ∨ T ^ 2 ≤ |r|) :
    kap1 r ε * T₀ ≤ η / 4 := by
  have hq : 0 < |r| := by linarith
  have he := Real.exp_pos 5
  have hA0 : 0 < A := by rw [hA]; positivity
  have hR5 : 0 < R ^ 5 := by positivity
  have e1 : (2 : ℝ) ^ 13 / |r| ^ (1 - ε) = 2 ^ 13 * |r| ^ (-1 + ε) := by
    have : (-1 + ε) = -(1 - ε) := by ring
    rw [this, Real.rpow_neg hq.le]
    rfl
  have h4 := (three_sqrt_le hq.le).trans (div_le_div_of_nonneg_right hP (by norm_num : (0 : ℝ) ≤ 6))
  set Y := T₀ * Z with hY
  have hY0 : 0 ≤ Y := by positivity
  have hAY : A * Y ≤ |r| := hT.trans h2
  have h60 : 0 ≤ 3 * Real.sqrt (MomP |r|) := by positivity
  have hsmall : η ^ 2 / (6 * 2 ^ 12) ≤ η / 4 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith only [hη, hη1]
  by_cases hcase : A * Y ≤ R ^ 5
  · have hrp := rpow_eps_le hR hq1 h0 (by linarith) hε
    have h5 : kap1 r ε ≤ 2 ^ 13 * (Real.exp 5 * (1 / |r| + 1 / R ^ 5)) * (Z / 6) := by
      unfold kap1
      rw [e1]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hrp (by norm_num)) h4 h60 (by positivity)
    have t1 : Y / |r| ≤ 1 / A := by
      rw [div_le_div_iff₀ hq hA0]
      linarith
    have t2 : Y / R ^ 5 ≤ 1 / A := by
      rw [div_le_div_iff₀ hR5 hA0]
      linarith
    have h6 : kap1 r ε * T₀ ≤ 2 ^ 13 * (Real.exp 5 * (1 / |r| + 1 / R ^ 5)) * (Z / 6) * T₀ :=
      mul_le_mul_of_nonneg_right h5 hT₀
    have e2 : 2 ^ 13 * (Real.exp 5 * (1 / |r| + 1 / R ^ 5)) * (Z / 6) * T₀ =
        2 ^ 13 * Real.exp 5 / 6 * (Y / |r| + Y / R ^ 5) := by
      simp only [hY]
      ring
    rw [e2] at h6
    have h7 : Y / |r| + Y / R ^ 5 ≤ 2 / A := by
      have : 2 / A = 1 / A + 1 / A := by ring
      linarith
    have h8 := mul_le_mul_of_nonneg_left h7 (by positivity : 0 ≤ 2 ^ 13 * Real.exp 5 / 6)
    have e3 : 2 ^ 13 * Real.exp 5 / 6 * (2 / A) = η ^ 2 / (6 * 2 ^ 12) := by
      rw [hA]
      field_simp
    rw [e3] at h8
    linarith
  · -- the threshold is above `R⁵`, off the scaled caps
    have hT5 : R ^ 5 < T := lt_of_lt_of_le (not_le.1 hcase) hT
    have hq2 : T ^ 2 ≤ |r| := h3.resolve_left (not_le.2 hT5)
    have hT1 : 1 ≤ T := by
      have : (1 : ℝ) ≤ R ^ 5 := one_le_pow₀ hR
      linarith
    have hT0 : 0 < T := by linarith
    have h5 : |r| ^ (-1 + ε) ≤ 1 / T := by
      have h6 : |r| ^ (-1 + ε) ≤ (T ^ 2) ^ (-1 + ε) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hq2 (by linarith)
      have h7 : (T ^ 2) ^ (-1 + ε) = T ^ (2 * (-1 + ε)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
        norm_num
      have h8 : T ^ (2 * (-1 + ε)) ≤ T ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      rw [h7] at h6
      rw [Real.rpow_neg_one] at h8
      rw [one_div]
      exact h6.trans h8
    have h6 : kap1 r ε * T₀ ≤ 2 ^ 13 * (1 / T) * (Z / 6) * T₀ := by
      refine mul_le_mul_of_nonneg_right ?_ hT₀
      unfold kap1
      rw [e1]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h5 (by norm_num)) h4 h60 (by positivity)
    have h7 : 2 ^ 13 * (1 / T) * (Z / 6) * T₀ = 2 ^ 13 / 6 * (Y / T) := by
      simp only [hY]
      ring
    rw [h7] at h6
    have h8 : Y / T ≤ 1 / A := by
      rw [div_le_div_iff₀ hT0 hA0]
      linarith
    have h9 := mul_le_mul_of_nonneg_left h8 (by positivity : (0 : ℝ) ≤ 2 ^ 13 / 6)
    have e3 : (2 : ℝ) ^ 13 / 6 * (1 / A) = η ^ 2 / (6 * 2 ^ 13 * Real.exp 5) := by
      rw [hA]
      field_simp
    rw [e3] at h9
    have h10 : η ^ 2 / (6 * 2 ^ 13 * Real.exp 5) ≤ η ^ 2 / (6 * 2 ^ 12) := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      have := Real.add_one_le_exp (5 : ℝ)
      nlinarith only [this]
    linarith

/-- **`C_{4,1}` on a prefix** (J3-v2 §5): the static bound and the two debits. -/
theorem quartic_one_piece (hdom : JDom R₀ X R) (h : ActualSol X (R - X) r g y Ty) (hr : r ≠ 0)
    (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hon : OnPrefix caps r g y s t) (hη : 0 < η)
    (hη1 : η ≤ 1)
    (hthr : qOneFull (2 ^ 26 * Real.exp 5 / η ^ 2) X R caps ≤ |r|)
    (hP : nearP |r| ≤ zq X R) :
    ∀ u ∈ Set.Icc s t, |C4 1 r g y u| ≤ η * fastNorm 1 r g y u ^ 2 ∧
      |Rem4 1 r g y u| ≤ η * fastNorm 2 r g y u ^ 2 +
        η * hnorm 1 (Hpsi r g y u) * fastNorm 2 r g y u := by
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  have hc4 := c4_pos
  have he := Real.exp_pos 5
  set Amp : ℝ := 2 ^ 26 * Real.exp 5 / η ^ 2 with hAmp
  have hAmp0 : 0 < Amp := by positivity
  set c := co1 X R caps with hcd
  set Z := zq X R with hZd
  have hZ : 0 ≤ Z := by
    have := Real.rpow_nonneg hdom.Q_pos.le ((1 : ℝ) / 3)
    simp only [hZd, zq]
    positivity
  have hL0 : 0 ≤ c.L := fibL_nonneg hR0 caps
  have hP0 : 0 ≤ c.P := cp_nonneg _
  have hA0 : 0 ≤ c.A := cp_nonneg _
  have hB0 : 0 ≤ c.B := cp_nonneg _
  have hLe0 : 0 ≤ c.Le := by
    simp only [hcd, co1, logE]
    positivity
  have hNb0 : 0 ≤ c.Nb := by
    have h1 := cp_nonneg caps.WS
    have h2 := cp_nonneg caps.BS
    have h3 := cp_nonneg caps.yF
    simp only [hcd, co1]
    positivity
  have hφ0 : 0 ≤ R - X := (hnorm_nonneg 2 g).trans h.force_le
  have hφR : R - X ≤ R := by linarith [hdom.one_lt_X]
  have hNs0 : 0 ≤ c.Ns := by
    have h1 := cp_nonneg caps.WS
    have h2 := cp_nonneg caps.BS
    have h3 := cp_nonneg caps.yF
    simp only [hcd, co1, hSrc]
    positivity
  have hm0 : 0 ≤ c.m₁ := by
    simp only [Co1.m₁]
    positivity
  have hy0 : 0 ≤ c.y₁ := by
    simp only [Co1.y₁]
    positivity
  have t1 : 0 ≤ tM₁ X R caps := mul_nonneg hm0 hZ
  have t2 : 0 ≤ tY₁ X R caps := mul_nonneg hy0 hZ
  have t3 : 0 ≤ tA₁ X R caps := by
    have h1 := cp_nonneg caps.AS
    have h2 := cp_nonneg caps.BS
    simp only [tA₁]
    positivity
  have hfl : 0 ≤ flrTwo R caps := by
    have := cp_nonneg caps.yF
    unfold flrTwo
    positivity
  have hq3 : R ^ 3 ≤ |r| := by
    have h1 : 0 ≤ 2 ^ 11 * c4 * cp caps.yF := by
      have := cp_nonneg caps.yF
      positivity
    have h2 : 0 ≤ Amp * thrOne X R caps := by
      have : 0 ≤ thrOne X R caps := add_nonneg (add_nonneg t1 t2) t3
      positivity
    have h3 := extraOne_nonneg (Amp * thrOne X R caps) R
    simp only [qOneFull, flrTwo] at hthr
    linarith
  have hext := extraOne_nonneg (Amp * thrOne X R caps) R
  have hthr' : Amp * thrOne X R caps ≤ |r| := by
    simp only [qOneFull] at hthr
    linarith
  have hext' : Amp * thrOne X R caps ≤ R ^ 5 ∨ (Amp * thrOne X R caps) ^ 2 ≤ |r| := by
    by_cases hc : Amp * thrOne X R caps ≤ R ^ 5
    · exact Or.inl hc
    · right
      have e : extraOne (Amp * thrOne X R caps) R = (Amp * thrOne X R caps) ^ 2 := ite_eq_right hc
      simp only [qOneFull, e] at hthr
      have h1 : 0 ≤ Amp * thrOne X R caps := by
        have : 0 ≤ thrOne X R caps := add_nonneg (add_nonneg t1 t2) t3
        positivity
      linarith
  have hq1 : 1 ≤ |r| := by
    have : (1 : ℝ) ≤ R ^ 3 := one_le_pow₀ hR1
    linarith
  have hε0 := epsR_pos hR1
  have hε1 := epsR_le R
  have hε2 : epsR R ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hε := epsR_mul hR1
  have hk : ∀ T₀ : ℝ, 0 ≤ T₀ → T₀ * Z ≤ thrOne X R caps → kap1 r (epsR R) * T₀ ≤ η / 4 :=
    fun T₀ h0 hle => kap1_key hη hη1 hq1 hR1 hε0.le hε2 hε hZ hP h0 hAmp
      (mul_le_mul_of_nonneg_left hle hAmp0.le) hthr' hext'
  have km : kap1 r (epsR R) * c.m₁ ≤ η / 4 := hk _ hm0 (by
    have : c.m₁ * Z = tM₁ X R caps := rfl
    rw [this, thrOne]
    linarith)
  have ky : kap1 r (epsR R) * c.y₁ ≤ η / 4 := hk _ hy0 (by
    have : c.y₁ * Z = tY₁ X R caps := rfl
    rw [this, thrOne]
    linarith)
  intro u hu
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  obtain ⟨c1, c2, c3, c4', c5⟩ := hon.1 u hu
  have hF := Fp_adm h hu0 huT
  have hS := Sp_adm h hu0 huT
  have ha' := c1.trans (le_cp _)
  have hb' := c2.trans (le_cp _)
  have hA' := c3.trans (le_cp _)
  have hB' := c4'.trans (le_cp _)
  have hW' := c5.trans (le_cp _)
  have hL := lhB_fibL (R := R) (caps := caps) hF.inH (PiF_Fp r g y u) hR1 ha' hb'
  have hq : 0 < |r| := by linarith
  constructor
  · -- the static bound
    have hv := val_one_le hr h hu0 huT hL
    have h1 : |C4 1 r g y u| ≤ 2 * ‖val4 1 r g y u‖ := by
      simp only [C4, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    have hsq : 0 < Real.sqrt |r| := Real.sqrt_pos.2 hq
    set S32 := hnorm (3 / 2) (Sp r g y u) with hS32
    have hS320 : 0 ≤ S32 := hnorm_nonneg _ _
    have hin : S32 ^ 2 ≤ cp caps.AS * cp caps.BS := by
      have := hnorm_interp (σ := 1) (by norm_num) le_rfl hS.inH
      have e : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
      rw [e] at this
      norm_num at this
      refine this.trans ?_
      exact mul_le_mul hA' hB' (hnorm_nonneg _ _) (cp_nonneg _)
    set a := hnorm 1 (Fp r g y u) with had
    have ha0 : 0 ≤ a := hnorm_nonneg _ _
    set W₀ := Z * S32 * fibL R caps with hW₀
    have hW₀0 : 0 ≤ W₀ := by
      have := fibL_nonneg hR0 caps
      positivity
    have hW2 : W₀ ^ 2 ≤ tA₁ X R caps := by
      have h2 := mul_le_mul_of_nonneg_left hin
        (by positivity : 0 ≤ Z ^ 2 * fibL R caps ^ 2)
      simp only [hW₀, tA₁]
      nlinarith only [h2]
    have hlast : 2 ^ 13 / 6 * W₀ ≤ η * Real.sqrt |r| := by
      have h3 : tA₁ X R caps ≤ |r| / Amp := by
        rw [le_div_iff₀ hAmp0]
        have : tA₁ X R caps ≤ thrOne X R caps := by
          rw [thrOne]
          linarith
        nlinarith only [mul_le_mul_of_nonneg_left this hAmp0.le, hthr']
      have h4 : (2 ^ 13 / 6 * W₀) ^ 2 ≤ (η * Real.sqrt |r|) ^ 2 := by
        have e5 : (η * Real.sqrt |r|) ^ 2 = η ^ 2 * |r| := by rw [mul_pow, Real.sq_sqrt hq.le]
        rw [e5, mul_pow]
        have h5 := mul_le_mul_of_nonneg_left (hW2.trans h3)
          (by positivity : 0 ≤ ((2 : ℝ) ^ 13 / 6) ^ 2)
        refine h5.trans ?_
        have e : ((2 : ℝ) ^ 13 / 6) ^ 2 * (|r| / Amp) = η ^ 2 * |r| / (36 * Real.exp 5) := by
          simp only [hAmp]
          field_simp
          ring
        rw [e, div_le_iff₀ (by positivity)]
        have h6 : (1 : ℝ) ≤ 36 * Real.exp 5 := by
          have := Real.add_one_le_exp (5 : ℝ)
          linarith
        have h7 : 0 ≤ η ^ 2 * |r| := by positivity
        nlinarith only [h6, h7]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h4
    have h3 : 3 * Real.sqrt (MomP |r|) ≤ Z / 6 :=
      (three_sqrt_le hq.le).trans (div_le_div_of_nonneg_right hP (by norm_num))
    have e1 : fastNorm 1 r g y u = a := rfl
    rw [e1]
    have h4 : 2 * (2 ^ 12 / Real.sqrt |r| * (3 * (Real.sqrt (MomP |r|) *
        (S32 * fibL R caps * a * a)))) ≤ η * a ^ 2 := by
      have hN0 : 0 ≤ S32 * fibL R caps * a * a := by
        have := fibL_nonneg hR0 caps
        positivity
      have h5 : 3 * (Real.sqrt (MomP |r|) * (S32 * fibL R caps * a * a)) ≤
          Z / 6 * (S32 * fibL R caps * a * a) := by
        have := mul_le_mul_of_nonneg_right h3 hN0
        linarith only [this]
      have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 2 ^ 12 / Real.sqrt |r|)
      have e2 : 2 ^ 12 / Real.sqrt |r| * (Z / 6 * (S32 * fibL R caps * a * a)) =
          (2 ^ 13 / 6 * W₀) * a ^ 2 / (2 * Real.sqrt |r|) := by
        simp only [hW₀]
        field_simp
      rw [e2] at h6
      have h7 := mul_le_mul_of_nonneg_right hlast (sq_nonneg a)
      have h8 : (2 ^ 13 / 6 * W₀) * a ^ 2 / (2 * Real.sqrt |r|) ≤
          (η * Real.sqrt |r|) * a ^ 2 / (2 * Real.sqrt |r|) :=
        div_le_div_of_nonneg_right h7 (by positivity)
      have e3 : (η * Real.sqrt |r|) * a ^ 2 / (2 * Real.sqrt |r|) = η * a ^ 2 / 2 := by
        field_simp
      rw [e3] at h8
      linarith only [h6, h8]
    linarith only [h1, hv, h4]
  · -- the two debits
    have hψ : hnorm 2 (psi r 0 g u) ≤ 1 := by
      refine (psi_le h hr hu0).trans ?_
      rw [div_le_one hq]
      have h3 : 2 * R ≤ R ^ 3 := by
        have := hdom.three_le_X
        have hXR := hdom.X_le_R
        nlinarith only [this, hXR, hR0, sq_nonneg (R - 1)]
      linarith
    obtain ⟨hNsM, hNs⟩ := H2.slowNL_one_le' h hon hu hs huT hψ
    obtain ⟨hI1, -⟩ := hnorm_PiF_Qphase_le (r * u) (h.sol.adm u hu0 huT)
    have hN1 : InH 1 (fastNL r g y u) := InH.neg hI1
    have hNF := fastNL_one_caps h hr hu0 huT hW' hB' hb'
    have hb := rem_one_caps hr h hu0 huT hε0 hε1 c hN1 hNsM.inH hL ha' hA' hB' hNs hNb0 hNF
      (sqrt_epsR_le hR1)
    have h1 : |Rem4 1 r g y u| ≤ 2 * ‖rem4 1 r g y u‖ := by
      simp only [Rem4, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    set b := hnorm 2 (Fp r g y u) with hbd
    set hh := hnorm 1 (Hpsi r g y u) with hhd
    have hb0 : 0 ≤ b := hnorm_nonneg _ _
    have hh0 : 0 ≤ hh := hnorm_nonneg _ _
    have e1 : fastNorm 2 r g y u = b := rfl
    rw [e1]
    have h2 := mul_le_mul_of_nonneg_right km (sq_nonneg b)
    have h3 := mul_le_mul_of_nonneg_right ky (mul_nonneg hh0 hb0)
    have h4 : 0 ≤ η * b ^ 2 := by positivity
    have h5 : 0 ≤ η * hh * b := by positivity
    nlinarith only [h1, hb, h2, h3, h4, h5]

end OVNS.Quant.Quartic

end
