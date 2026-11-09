import OddViscousNS.Quant.Joint.Metric.Thresh2

/-!
# The degrees of the thresholds (nodes N14, N15)

`q1_below`, `q2_below`: `JointBelow`, one line per monomial, with the calculus of `Assembly/Degree.lean`.

| monomial | degree | |
|---|---|---|
| `Q11`, the group of `E₁` | `(0, 3)` | `q⁻¹ R³`, up to logs |
| `√Q12` | `(0, 11/4)` | `q⁻² R^{11/2}` |
| `Q14^{1/4}` | `(1/2, 3)` | `q⁻⁴ R¹²`, `q⁻⁴ R¹⁰ U²` |
| `N1 Λ`, `N1L Λ` | `(1, 3)` | the row `q⁻¹ R⁴/λ_*`, tied at `Q` |
| `√(N2 Λ)` | `(3/4, 3)` | `q⁻² (D R⁵ + R⁷)/λ_*`, `U^{1/2} R³` |
| `√(Ky S)` | `(1/2, 5/2)` | `q⁻² W b √(P_S/λ_*)` |
| `(N3 Λ)^{1/3}` | `(1/3, 17/6)` | `q⁻³ D² W b²/λ_*` |
| `(N4 Λ)^{1/4}` | `(1/2, 9/4)` | `q⁻⁴ R¹⁰/λ_*`, `q⁻⁴ W² b² y²/λ_*` |
-/

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic OVNS.Quant.NearFar JDeg
open OVNS.Quant.H2 (cBil cBil_nonneg)

variable {C e : ℝ}

/-! ### Logarithms -/

theorem deg_Zs (n : ℕ) : JDeg 0 0 fun _ R (_ : Caps) ↦ Zs (R ^ n) := by
  refine (logR.const_mul (k := 9 + 8 * n) (by positivity)).of_le fun R₀ X R hdom _ ↦ ?_
  have hl : 0 ≤ Real.log R := Real.log_nonneg hdom.one_lt_R.le
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [Zs, Real.log_pow]
  constructor
  · positivity
  · nlinarith only [hl, hn, mul_nonneg hl hn]

theorem deg_Z4s (n : ℕ) : JDeg 0 0 fun _ R (_ : Caps) ↦ Z4s (R ^ n) := by
  refine (logR.const_mul (k := 33 + 8 * n) (by positivity)).of_le fun R₀ X R hdom _ ↦ ?_
  have hR := hdom.R_pos
  have hl : 0 ≤ Real.log R := Real.log_nonneg hdom.one_lt_R.le
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have e : Real.log (4 * R ^ n) = Real.log 4 + n * Real.log R := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  simp only [Z4s, e]
  constructor
  · positivity
  · nlinarith only [hl, hn, mul_nonneg hl hn, h4]

theorem deg_sqrtZs (n : ℕ) : JDeg 0 0 fun _ R (_ : Caps) ↦ Real.sqrt (Zs (R ^ n)) :=
  (deg_Zs n).sqrt.up 0 0

theorem deg_sqrtZ4s (n : ℕ) : JDeg 0 0 fun _ R (_ : Caps) ↦ Real.sqrt (Z4s (R ^ n)) :=
  (deg_Z4s n).sqrt.up 0 0

theorem deg_T0 (n : ℕ) : JDeg 0 0 fun _ R (_ : Caps) ↦ T0 (R ^ n) := by
  have hc := c4_pos
  have h1 := (deg_sqrtZs n).const_mul (k := 6) (by norm_num)
  have h2 := (deg_sqrtZs n).const_mul (k := 2 * c4) (by positivity)
  have h3 : JDeg 0 0 fun _ _ (_ : Caps) ↦ 2 * c4 := const (by positivity)
  have h4 := (((deg_sqrtZ4s n).const_mul (k := Real.sqrt 17) (Real.sqrt_nonneg _)).mul
    ((const (k := 1) zero_le_one).add (deg_sqrtZs n))).up 0 0
  exact deg_congr (((h1.add h2).add h3).add h4) fun X R caps => by simp only [T0]

/-! ### The caps -/

theorem deg_Kc : JDeg 0 5 fun _ _ caps ↦ Kc caps := by
  have hc := c4_pos
  have h1 := ((WS.mul WS).mul WS).up 0 5
  have h2 := ((BS.mul WS).mul WS).up 0 5
  have h3 := ((WS.mul BS).mul WS).up 0 5
  have h4 := ((WS.mul WS).mul BS).up 0 5
  have h5 := (h1.add (((h2.add h3).add h4).const_mul hc.le)).const_mul
    (k := 2 ^ 37) (by norm_num)
  exact deg_congr h5 fun X R caps => by simp only [Kc, clsS]

theorem deg_Xic : JDeg (1 / 2) 2 fun _ _ caps ↦ Xic caps := by
  have hc := c4_pos
  have h1 := WS.up (1 / 2) 2
  have h2 := (BS.const_mul hc.le).up (1 / 2) 2
  have h3 := (yF.const_mul hc.le).up (1 / 2) 2
  have h4 := ((h1.add h2).add h3).const_mul (k := 8) (by norm_num)
  exact deg_congr h4 fun X R caps => by simp only [Xic]

theorem deg_fB (hC : 0 ≤ C) : JDeg 0 3 fun _ R caps ↦ 41 * Mi C e R * cp caps.BS :=
  (((Minf (e := e) hC).const_mul (k := 41) (by norm_num)).mul BS).up 0 3

theorem deg_Om (hC : 0 ≤ C) : JDeg 0 5 fun _ R caps ↦ Om (Mi C e R) caps := by
  have hc := c4_pos
  have hf := deg_fB (e := e) hC
  have t1 := ((hf.const_mul hc.le).mul WS).up 0 5
  have t2 := ((hf.mul WS).up 0 5).add ((((hf.const_mul hc.le).mul BS)).up 0 5)
  have t3 := (hf.mul BS).up 0 5
  have t4 := (t1.add (t2.const_mul (k := 2 * c4) (by positivity))).add
    (t3.const_mul (k := c4 ^ 2) (by positivity))
  have t5 := t4.const_mul (k := 2 ^ 22) (by norm_num)
  have u1 := (hf.mul AS).up 0 5
  have u2 := (hf.mul WS).up 0 5
  have u3 := (hf.mul BS).up 0 5
  have u4 := ((u1.const_mul (k := 30) (by norm_num)).add (u2.const_mul hc.le)).add
    (u3.const_mul (Real.sqrt_nonneg (34 * (9 + 4 / 1))))
  have u5 := u4.const_mul (k := 2 ^ 15) (by norm_num)
  exact deg_congr (t5.add u5) fun X R caps => by simp only [Om, cls2]

/-! ### The first energy -/

theorem deg_I1 (hC : 0 ≤ C) : JDeg 0 2 fun _ R (_ : Caps) ↦ 8 * (C * Ex e R * R ^ 2) :=
  ((((ex e).const_mul hC).mul (R.pow 2)).const_mul (k := 8) (by norm_num)).up 0 2

theorem deg_I2 (hC : 0 ≤ C) : JDeg 0 5 fun _ R (_ : Caps) ↦ 4 * slowPrice C (Ex e R) R 1 := by
  have h1 : JDeg 0 5 fun _ R (_ : Caps) ↦ R ^ 4 + 1 * R ^ 5 :=
    (((R.pow 4).up 0 5).add ((by simpa using R.pow 5 : JDeg 0 5 fun _ R (_ : Caps) ↦ 1 * R ^ 5)))
  have h2 := (((ex e).const_mul hC).mul h1).const_mul (k := 4) (by norm_num)
  exact deg_congr (h2.up 0 5) fun X R caps => by simp only [slowPrice]

theorem deg_A11 (hC : 0 ≤ C) : JDeg 0 1 fun _ R caps ↦ A11 R (Mi C e R) (R ^ 4) (cp caps.BS) := by
  have hc := cL_nonneg
  have hM := Minf (e := e) hC
  have h1 := (hM.const_mul (k := 2 ^ 18 * (cL + 1)) (by positivity)).mul
    ((const (k := 1) zero_le_one).add ((deg_Zs 4).const_mul (k := 2) (by norm_num)))
  have h2 := (BS.mul (deg_div_pow (k := 1) zero_le_one 1)).const_mul (k := Cm3) Cm3_pos.le
  have h3 := (h1.up 0 1).add (h2.up 0 1)
  refine h3.of_le fun R₀ X R hdom caps ↦ ?_
  have hR1 := hdom.one_lt_R
  have hR0 := hdom.R_pos
  have hEx := Ex_pos e R
  have hB := cp_nonneg caps.BS
  have hC3 := Cm3_pos
  have hlog : 0 ≤ Real.log (R ^ 4) := Real.log_nonneg (one_le_pow₀ hR1.le)
  have hZ : 0 ≤ Zs (R ^ 4) := by unfold Zs; positivity
  have hcL1 : 0 ≤ cL + 1 := by linarith
  constructor
  · unfold A11 Mi
    positivity
  · unfold A11
    have h4 : 1 / (2 * R ^ 4) + 1 / (2 * R) ≤ 1 / R ^ 1 := by
      have h5 : 1 / (2 * R ^ 4) ≤ 1 / (2 * R) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : R ≤ R ^ 4 := by
          calc R = R ^ 1 := (pow_one R).symm
            _ ≤ R ^ 4 := pow_le_pow_right₀ hR1.le (by norm_num)
        linarith
      have e1 : 1 / R ^ 1 = 1 / (2 * R) + 1 / (2 * R) := by
        field_simp
        norm_num
      linarith
    have h6 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hC3.le hB)
    have e2 : Cm3 * (cp caps.BS * (1 / R ^ 1)) = Cm3 * cp caps.BS * (1 / R ^ 1) := by ring
    rw [e2]
    linarith

theorem deg_A12 : JDeg 0 (-2) fun _ R caps ↦ A12 (R ^ 4) (cp caps.BS) := by
  have h := (BS.mul (deg_div_pow (k := Cm3 / 2) (by have := Cm3_pos; positivity) 4)).up 0 (-2)
  exact deg_congr h fun X R caps => by
    simp only [A12]
    ring

theorem deg_A13 : JDeg 0 3 fun _ R caps ↦ A13 R (R ^ 4) (cp caps.BS) := by
  have hC3 := Cm3_pos
  have h1 := ((BS.pow 3).mul (deg_div_pow (k := 5 * Cm3) (by positivity) 4)).up 0 3
  have h2 := ((BS.mul R).const_mul (k := Cm3 / 2) (by positivity)).up 0 3
  exact deg_congr (h1.add h2) fun X R caps => by
    simp only [A13]
    ring

theorem deg_Q11 (hC : 0 ≤ C) : JDeg 0 3 fun _ R caps ↦ Q11 R (Mi C e R) (R ^ 4) C (Ex e R) caps := by
  have h1 := ((deg_A11 (e := e) hC).mul (deg_I1 (e := e) hC)).up 0 3
  have h2 := (deg_A12.mul (deg_I2 (e := e) hC)).up 0 3
  have h3 := deg_A13.const_mul (k := 4) (by norm_num)
  exact deg_congr ((h1.add h2).add h3) fun X R caps => by simp only [Q11]

theorem deg_B11 : JDeg 0 (7 / 2) fun X R caps ↦ B11 (R - X) (R ^ 4) caps := by
  have hc := c4_pos
  have h1 := ((deg_Z4s 4).const_mul (k := 2 ^ 27 * 5) (by norm_num)).mul BS
  have h2 := (((deg_Z4s 4).const_mul (k := 2 ^ 21) (by norm_num)).mul (deg_sqrtZs 4)).mul BS
  have h3 := ((h1.up 0 (7 / 2)).add (h2.up 0 (7 / 2)))
  have h4 := ((WS.pow 2).up 0 (7 / 2)).add
    (((BS.mul WS).const_mul (k := 3 * c4) (by positivity)).up 0 (7 / 2))
  have h5 := h4.const_mul (k := 2 ^ 40) (by norm_num)
  have h6 := ((deg_hSrc.mul (deg_T0 4)).const_mul (k := 2 ^ 36) (by norm_num)).up 0 (7 / 2)
  exact deg_congr ((h3.add h5).add h6) fun X R caps => by simp only [B11, B11g]

theorem deg_B13 (hC : 0 ≤ C) :
    JDeg 0 (9 / 2) fun _ R caps ↦ B13 (Mi C e R) (R ^ 4) (cp caps.AS) (cp caps.BS) := by
  have h1 := (Minf (e := e) hC).const_mul (k := 2 ^ 22) (by norm_num)
  have h2 := (((deg_Zs 4).const_mul (k := 2) (by norm_num)).mul (h1.mul (AS.mul BS))).up 0 (9 / 2)
  exact deg_congr h2 fun X R caps => by simp only [B13]

theorem deg_Q12 (hC : 0 ≤ C) :
    JDeg 0 (11 / 2) fun X R caps ↦ Q12 (R - X) R (Mi C e R) (R ^ 4) C (Ex e R) caps := by
  have h1 := (deg_B11.mul (deg_I1 (e := e) hC)).up 0 (11 / 2)
  have h2 := ((deg_B13 (e := e) hC).const_mul (k := 4) (by norm_num)).up 0 (11 / 2)
  exact deg_congr (h1.add h2) fun X R caps => by simp only [Q12]

theorem deg_Q14 (hC : 0 ≤ C) : JDeg 2 12 fun _ R caps ↦ Q14 R C (Ex e R) caps := by
  have hc := c4_pos
  have h1 := (deg_I1 (e := e) hC).up 2 2
  have h2 := ((PF.pow 2).const_mul (k := 4) (by norm_num)).up 2 2
  have h3 := ((deg_Kc.pow 2).const_mul (k := 2 ^ 10 * c4 ^ 2) (by positivity)).mul (h1.add h2)
  exact deg_congr (h3.up 2 12) fun X R caps => by simp only [Q14]

theorem deg_n11 (hC : 0 ≤ C) : JDeg 0 3 fun _ R caps ↦ n11 (Mi C e R) (R ^ 4) caps := by
  have hc := cL_nonneg
  have h1 := deg_div_pow (k := 5) (by norm_num) 4
  have h2 := ((((h1.pow 2).const_mul (k := 2) (by norm_num)).mul
    (((Minf (e := e) hC).const_mul (k := 2 ^ 18 * (cL + 1)) (by positivity)).mul (AS.pow 2)))).up 0 3
  exact deg_congr h2 fun X R caps => by simp only [n11]

theorem deg_n12 (hC : 0 ≤ C) : JDeg 0 3 fun _ R caps ↦ n12 (Mi C e R) (R ^ 4) caps := by
  have h1 := deg_div_pow (k := 5) (by norm_num) 4
  have h2 := ((((h1.pow 2).const_mul (k := 2) (by norm_num)).mul
    (((Minf (e := e) hC).const_mul (k := 2 ^ 22) (by norm_num)).mul (AS.mul BS)))).up 0 3
  exact deg_congr h2 fun X R caps => by simp only [n12]

theorem deg_kapA (hC : 0 ≤ C) : JDeg 0 3 fun _ R caps ↦ kapA R (Mi C e R) caps := by
  have hc := c4_pos
  have hL : JDeg 0 0 fun _ R (_ : Caps) ↦ 1 + Real.sqrt (1 + Real.log R) :=
    (const zero_le_one).add (logR.sqrt.up 0 0)
  have hB2 : JDeg 0 3 fun _ R caps ↦ cp caps.BS ^ 2 / R := by
    refine (((BS.pow 2).mul (Rpow (-1))).up 0 3).congr' fun _ X R hdom _ ↦ ?_
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  have h1 := (BS.const_mul (k := 2 ^ 8 * (1 + c4)) (by positivity)).up 0 3
  have hS := (((hL.mul (AS.pow 2)).up 0 3).add
    (((AS.mul WS).const_mul (by norm_num : (0 : ℝ) ≤ 2)).up 0 3)).add hB2
  have h2 := (hS.const_mul Cst_nonneg).up 0 3
  have h3 := (((Minf (e := e) hC).const_mul CZ_nonneg).mul BS).up 0 3
  exact deg_congr ((h1.add h2).add h3) fun X R caps => by simp only [kapA, Mi]

theorem deg_kapB : JDeg 0 (9 / 2) fun _ R caps ↦ kapB R caps :=
  ((R.mul (AS.mul BS)).const_mul Cst_nonneg).up 0 (9 / 2)

/-- **The shares of `Thr1`.** -/
theorem qS1_below (hC : 0 ≤ C) : JointBelow fun X R caps ↦ qS1 C e X R caps := by
  have h1 := ((deg_Q11 (e := e) hC).const_mul (k := 64) (by norm_num)).toQ
  have h2 := (((deg_Q12 (e := e) hC).const_mul (k := 64) (by norm_num)).root (1 / 2)).toQ
  have h3 := (((deg_Q14 (e := e) hC).const_mul (k := 64) (by norm_num)).root (1 / 4)).toQ
  have h4 := ((deg_n11 (e := e) hC).const_mul (k := 128) (by norm_num)).toQ
  have h5 := (((deg_n12 (e := e) hC).const_mul (k := 128) (by norm_num)).root (1 / 2)).toQ
  have h6 := ((deg_Kc.const_mul (k := 2 ^ 24) (by norm_num)).root (1 / 2)).toQ
  have h7 := ((deg_kapA (e := e) hC).const_mul (k := 2 ^ 23) (by norm_num)).toQ
  have h8 := ((deg_kapB.const_mul (k := 2 ^ 23) (by norm_num)).root (1 / 2)).toQ
  exact h1.sup (h2.sup (h3.sup (h4.sup (h5.sup (h6.sup (h7.sup h8))))))

lemma etaQ_nonneg : 0 ≤ etaQ := zero_le_one.trans one_le_etaQ

lemma etaQ2_nonneg : 0 ≤ etaQ2 := zero_le_one.trans one_le_etaQ2

lemma amp1_nonneg : 0 ≤ amp1 := by
  have := Real.exp_pos 5
  unfold amp1 eta41
  positivity

/-- **The threshold of the first energy is below `Q`.** -/
theorem q1_below (hC : 0 ≤ C) : JointBelow fun X R caps ↦ q1 C e X R caps := by
  have h1 := jointSlowFloor_below
  have h2 := force1Q_below (C := C) (e := e) hC
  have h3 := (staticQ_below (C := C) (e := e) hC).const_mul etaQ_nonneg
  have h4 := qOneFull_below amp1_nonneg
  have h5 := qNF₁_below (η := 1 / 256) (by norm_num)
  have h6 := (deg_force0Y.const_mul (k := 2 ^ 5) (by norm_num)).toQ
  have h7 := qS1_below (C := C) (e := e) hC
  exact h1.sup (h2.sup (h3.sup (h4.sup (h5.sup (h6.sup h7)))))

/-! ### The logarithm of a threshold -/

/-- **The logarithm of a monomial is a polylog of `R`.** -/
theorem log_one {a b : ℝ} {m : ℝ → ℝ → Caps → ℝ} (h : JDeg a b m) :
    JDeg 0 0 fun X R caps ↦ 1 + Real.log (max 1 (m X R caps)) := by
  intro K c hK hc
  obtain ⟨C₁, c₁, R₁, hC₁, hm⟩ := h K c hK hc
  obtain ⟨C₂, c₂, R₂, hC₂, hL⟩ := logR K c hK hc
  set κ := 1 + |Real.log (C₁ + 1)| + |a| + |b| + |c₁| with hκ
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨κ * C₂, c₂, max R₁ R₂, mul_nonneg hκ0 hC₂, fun X R hdom caps hcaps ↦ ?_⟩
  obtain ⟨h0, h1⟩ := hm X R (hdom.mono (le_max_left _ _)) caps hcaps
  obtain ⟨-, h2⟩ := hL X R (hdom.mono (le_max_right _ _)) caps hcaps
  simp only [Real.rpow_zero, mul_one] at h2 ⊢
  have hR1 := hdom.one_lt_R
  have hR0 := hdom.R_pos
  have hl : 0 ≤ Real.log R := Real.log_nonneg hR1.le
  have hU1 := hdom.one_lt_U
  have hU0 : 0 < jointU X := by linarith
  have hlU0 : 0 ≤ Real.log (jointU X) := Real.log_nonneg hU1.le
  have hlU : Real.log (jointU X) ≤ Real.log R := Real.log_le_log hU0 hdom.U_le_self
  have hll := hdom.one_le_loglog
  have hM1 : 0 ≤ Real.log (max 1 (m X R caps)) := Real.log_nonneg (le_max_left _ _)
  have key : Real.log (max 1 (m X R caps)) ≤ |Real.log (C₁ + 1)| + (|a| + |b| + |c₁|) * Real.log R := by
    rcases le_total (m X R caps) 1 with hle | hle
    · rw [max_eq_left hle, Real.log_one]
      positivity
    · rw [max_eq_right hle]
      have hmp : 0 < m X R caps := by linarith
      have hB : m X R caps ≤ (C₁ + 1) * (jointU X ^ a * R ^ b) * Ex c₁ R := by
        refine h1.trans ?_
        have : 0 ≤ jointU X ^ a * R ^ b * Ex c₁ R := by
          have := Ex_pos c₁ R
          have := Real.rpow_nonneg hU0.le a
          have := Real.rpow_nonneg hR0.le b
          positivity
        nlinarith only [this]
      have hC0 : 0 < C₁ + 1 := by linarith
      have hUa := Real.rpow_pos_of_pos hU0 a
      have hRb := Real.rpow_pos_of_pos hR0 b
      have hEx := Ex_pos c₁ R
      have s1 := Real.log_le_log hmp hB
      rw [Real.log_mul (by positivity) hEx.ne', Real.log_mul hC0.ne' (by positivity),
        Real.log_mul hUa.ne' hRb.ne', Real.log_rpow hU0, Real.log_rpow hR0, Ex, Real.log_exp] at s1
      have s2 : Real.log (C₁ + 1) ≤ |Real.log (C₁ + 1)| := le_abs_self _
      have s3 : a * Real.log (jointU X) ≤ |a| * Real.log R := by
        calc a * Real.log (jointU X) ≤ |a| * Real.log (jointU X) :=
              mul_le_mul_of_nonneg_right (le_abs_self a) hlU0
          _ ≤ |a| * Real.log R := mul_le_mul_of_nonneg_left hlU (abs_nonneg a)
      have s4 : b * Real.log R ≤ |b| * Real.log R := mul_le_mul_of_nonneg_right (le_abs_self b) hl
      have s5 : c₁ * Real.log R / Real.log (Real.log R) ≤ |c₁| * Real.log R := by
        have hll0 : 0 < Real.log (Real.log R) := by linarith
        rw [div_le_iff₀ hll0]
        have h6 : c₁ * Real.log R ≤ |c₁| * Real.log R := mul_le_mul_of_nonneg_right (le_abs_self c₁) hl
        have h7 : 0 ≤ |c₁| * Real.log R := by positivity
        nlinarith only [h6, h7, hll]
      linarith only [s1, s2, s3, s4, s5]
  refine ⟨by linarith, ?_⟩
  have h3 : 1 + Real.log (max 1 (m X R caps)) ≤ κ * (1 + Real.log R) := by
    have h4 : 0 ≤ |Real.log (C₁ + 1)| * Real.log R := by positivity
    have h5 : 0 ≤ (|a| + |b| + |c₁|) := by positivity
    simp only [hκ]
    nlinarith only [key, h4, h5, hl]
  calc _ ≤ κ * (1 + Real.log R) := h3
    _ ≤ κ * (C₂ * Ex c₂ R) := mul_le_mul_of_nonneg_left h2 hκ0
    _ = _ := by ring

/-- `qL` of a monomial of degree `(1, 3)` keeps it. -/
theorem deg_qL {m : ℝ → ℝ → Caps → ℝ} (h : JDeg 1 3 m) : JDeg 1 3 fun X R caps ↦ qL (m X R caps) := by
  have h1 : JDeg 1 3 fun X R caps ↦ max 1 (m X R caps) := by
    intro K c hK hc
    obtain ⟨C, c', R₀, hC, hm⟩ := ((const (k := 1) zero_le_one).up 1 3).add h K c hK hc
    obtain ⟨C', c'', R₁, -, hm'⟩ := h K c hK hc
    refine ⟨C, c', max R₀ R₁, hC, fun X R hdom caps hcaps ↦ ?_⟩
    obtain ⟨h0, -⟩ := hm' X R (hdom.mono (le_max_right _ _)) caps hcaps
    obtain ⟨-, h2⟩ := hm X R (hdom.mono (le_max_left _ _)) caps hcaps
    refine ⟨zero_le_one.trans (le_max_left _ _), le_trans ?_ h2⟩
    exact max_le (by linarith) (by linarith)
  have h2 := ((h1.const_mul (k := 4) (by norm_num)).mul (log_one h)).up 1 3
  exact deg_congr h2 fun X R caps => by simp only [qL]

/-! ### The second energy -/

theorem deg_N1 (hC : 0 ≤ C) : JDeg 0 4 fun _ R caps ↦ N1 (R ^ 2) (Mi C e R) caps := by
  have hC1 := CLow_nonneg 1
  have hZ := CZh_pos
  have hM := Minf (e := e) hC
  have c1 := hM.const_mul (k := 2 * CLow 1) (by positivity)
  have t1 := ((WS.pow 2).const_mul (k := 2 ^ 28) (by norm_num)).up 0 3
  have t2 := (((deg_Zs 2).mul (AS.pow 2)).const_mul (k := 2 ^ 18) (by norm_num)).up 0 3
  have t3 := ((((const (k := 1) zero_le_one).up 0 1).add hM).const_mul hZ.le).mul BS
  have t4 := (((t1.add t2).add (t3.up 0 3)).mul c1).up 0 4
  have t5 := (((hM.const_mul (k := 3) (by norm_num)).mul AS).mul WS)
  have t6 := ((t5.const_mul (Real.sqrt_nonneg 33)).const_mul (k := 2 ^ 30 + 2 ^ 16)
    (by norm_num)).up 0 4
  exact deg_congr (t4.add t6) fun X R caps => by simp only [N1]

theorem deg_N1L (hC : 0 ≤ C) : JDeg 0 4 fun _ R caps ↦ N1L (Mi C e R) caps := by
  have hC1 := CLow_nonneg 1
  have hZ := CZh_pos
  have hM := Minf (e := e) hC
  have c1 := hM.const_mul (k := 2 * CLow 1) (by positivity)
  exact (((hM.const_mul hZ.le).mul BS).mul c1).up 0 4

theorem deg_Ky : JDeg 0 (7 / 2) fun _ _ caps ↦ Ky caps := by
  have hc := c4_pos
  exact ((BS.mul WS).const_mul (k := 2 ^ 37 * c4 ^ 2) (by positivity)).up 0 (7 / 2)

theorem deg_cls2 : JDeg 0 4 fun _ _ caps ↦ cls2 (cp caps.WS) (cp caps.WS) (cp caps.BS) (cp caps.BS) := by
  have hc := c4_pos
  have h1 := (WS.mul WS).up 0 4
  have h2 := ((((BS.mul WS).up 0 4).add ((WS.mul BS).up 0 4)).const_mul (k := 2 * c4) (by positivity))
  have h3 := ((BS.mul BS).const_mul (k := c4 ^ 2) (by positivity)).up 0 4
  exact deg_congr ((h1.add h2).add h3) fun X R caps => by simp only [cls2]

theorem deg_N2 (hC : 0 ≤ C) :
    JDeg (1 / 2) 7 fun X R caps ↦ N2 (R - X) (R ^ 2) (Mi C e R) caps := by
  have hc := c4_pos
  have hC1 := CLow_nonneg 1
  have hM := Minf (e := e) hC
  have c1 := hM.const_mul (k := 2 * CLow 1) (by positivity)
  have hD : JDeg 0 2 fun _ R (_ : Caps) ↦ R ^ 2 := (R.pow 2).up 0 2
  have t1 := ((((hD.const_mul (k := 2 ^ 19) (by norm_num)).mul deg_cls2).mul c1)).up (1 / 2) 7
  have t2a := ((((deg_sqrtZs 2).const_mul (k := 2 * c4) (by positivity)).mul
    ((BS.pow 2).mul WS))).up (1 / 2) 7
  have t2b := (((deg_sqrtZs 2).const_mul (k := c4 ^ 2) (by positivity)).mul (BS.pow 3)).up (1 / 2) 7
  have t2 := (t2a.add t2b).const_mul (k := 2 ^ 36) (by norm_num)
  have t3 := (((hD.const_mul (k := 2 ^ 22) (by norm_num)).mul
    (((BS.const_mul (k := Real.sqrt 17) (Real.sqrt_nonneg _)).mul (AS.mul (deg_sqrtZ4s 2))).mul
      WS))).up (1 / 2) 7
  have t4 := (((hD.const_mul (k := 2 ^ 18) (by norm_num)).mul
    (((((hM.const_mul (k := 41) (by norm_num)).mul BS).mul BS)).const_mul
      (k := c4 ^ 2) (by positivity)))).up (1 / 2) 7
  have t5 := ((deg_Kc.const_mul (k := 2) (by norm_num)).mul deg_Xic).up (1 / 2) 7
  have t6 := (((deg_hSrc.mul (deg_T0 2)).mul (((WS.pow 2).up 0 3).add ((AS.pow 2).up 0 3))).const_mul
    (k := 2 ^ 36) (by norm_num)).up (1 / 2) 7
  refine deg_congr (((((t1.add t2).add t3).add t4).add t5).add t6) fun X R caps => ?_
  simp only [N2, mul_comm, mul_left_comm, mul_assoc]

theorem deg_N3 : JDeg 0 (19 / 2) fun _ R caps ↦ N3 (R ^ 2) caps := by
  have hc := c4_pos
  have hD : JDeg 0 4 fun _ R (_ : Caps) ↦ (R ^ 2) ^ 2 := ((R.pow 2).pow 2).up 0 4
  have h := ((hD.const_mul (k := 2 ^ 23) (by norm_num)).mul
    (((BS.pow 2).mul WS).const_mul (k := c4 ^ 2) (by positivity))).up 0 (19 / 2)
  exact deg_congr h fun X R caps => by simp only [N3]

theorem deg_N4 (hC : 0 ≤ C) : JDeg 1 10 fun _ R caps ↦ N4 (Mi C e R) caps := by
  have h1 := (((((deg_Ky.mul (const (k := 1 / 128) (by norm_num))).pow 2).const_mul (k := 16)
    (by norm_num)).mul (yF.pow 2))).up 1 10
  have h2 := (((deg_Om (e := e) hC).pow 2).const_mul (k := 16) (by norm_num)).up 1 10
  refine deg_congr (h1.add h2) fun X R caps => ?_
  simp only [N4]
  ring

theorem deg_lI : JDeg 1 (-1) fun X R caps ↦ lamI X R caps := invLam

theorem deg_Spr (hC : 0 ≤ C) : JDeg 1 (3 / 2) fun X R caps ↦ Spr C e X R caps := by
  have h := ((deg_lI.mul ((price (e := e) hC).const_mul (k := 4) (by norm_num))).sqrt).up 1 (3 / 2)
  exact h

/-- **The shares of `Thr2`.** -/
theorem qS2_below (hC : 0 ≤ C) : JointBelow fun X R caps ↦ qS2 C e X R caps := by
  have hc := c4_pos
  have hl := deg_lI
  have h1 := (((deg_N1 (e := e) hC).mul hl).up 1 3).const_mul (k := 2 ^ 9) (by norm_num)
  have h2 := deg_qL ((((deg_N1L (e := e) hC).mul hl).up 1 3).const_mul (k := 2 ^ 9) (by norm_num))
  have h3a := ((deg_N2 (e := e) hC).mul hl).up (3 / 2) 6
  have h3b := (deg_Ky.mul (deg_Spr (e := e) hC)).up (3 / 2) 6
  have h3 := (((h3a.add h3b).const_mul (k := 2 ^ 9) (by norm_num)).root (1 / 2)).toQ
  have h4 := (((deg_N3.mul hl).const_mul (k := 2 ^ 9) (by norm_num)).root (1 / 3)).toQ
  have h5 := ((((deg_N4 (e := e) hC).mul hl).const_mul (k := 2 ^ 9) (by norm_num)).root (1 / 4)).toQ
  have h6 := WS.toQ
  have h7 := (yF.const_mul (k := 2 ^ 11 * c4) (by positivity)).toQ
  have h8 := ((deg_Kc.const_mul (k := 2 ^ 8) (by norm_num)).root (1 / 2)).toQ
  have h9 := (BS.const_mul (k := 2 ^ 8 * cBil) (by have := cBil_nonneg; positivity)).toQ
  have h10 := ((deg_kapA (e := e) hC).const_mul (k := 2 ^ 9) (by norm_num)).toQ
  have h11 := ((deg_kapB.const_mul (k := 2 ^ 9) (by norm_num)).root (1 / 2)).toQ
  exact h1.toQ.sup (h2.toQ.sup (h3.sup (h4.sup (h5.sup (h6.sup (h7.sup (h8.sup (h9.sup
    (h10.sup h11)))))))))

/-- **The threshold of the second energy is below `Q`.** -/
theorem q2_below (hC : 0 ≤ C) : JointBelow fun X R caps ↦ q2 C e X R caps := by
  have h1 := qTot₂_below (CS := C) (cS := e) hC (η := eta2) (by norm_num [eta2])
  have h2 := force2Q_below (C := C) (e := e) hC
  have h3 := force1Q_below (C := C) (e := e) hC
  have h4 := (staticQ_below (C := C) (e := e) hC).const_mul etaQ2_nonneg
  have h5 := (deg_force0Y.const_mul (k := 2 ^ 5) (by norm_num)).toQ
  have h6 := qS2_below (C := C) (e := e) hC
  exact h1.sup (h2.sup (h3.sup (h4.sup (h5.sup h6))))

end OVNS.Quant.Metric

end
