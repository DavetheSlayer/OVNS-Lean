import OddViscousNS.Quant.Joint.Force.Source
import OddViscousNS.Quant.Joint.Assembly.Roles
import OddViscousNS.Quant.Joint.Assembly.Package

/-!
# The degree table of the force (step J5, node N12)

One `JDeg` line per monomial of `force2Q`, `force1Q`, `force0Q`, `role18J`, at `φ = R − X`,
`M = C Ex(e, R) R`, `D = jointD R = R²` for `H²`, and `D = R` for `H¹`.  A line reads
`JDeg a b` for `m ≲ U^a R^b Ex`; the exit is `b ≤ 3`, `(a − 1)/8 + b ≤ 3`.

| # | pair | linear | quadratic | printed |
|---|---|---|---|---|
| 1 | direct + native | `(1, 5/2)` | `(1/2, 1)` | the same |
| 2 | comparable `X₁` | `(0, 3)` | `(0, 8/5)` | the same |
| 3 | separated `X₁` | `(0, 11/4)` | `(0, 3/2)` | `(0, 3)`, `(0, 5/3)`: lower here |
| 4 | low `X₂`, ordinary | `(0, 11/4)` | `(0, 5/3)` | the same |
| 5 | low `X₂`, heat | `(0, 17/6)` | `(0, 2)` | the same |
| 6 | `Z` | `(0, 44/15)` | `(0, 40/23)` | `(0, 11/4)`, `(0, 5/3)`: higher here |
| 7 | high `X₂` | `(0, 11/4)` | `(0, 3/2)` | the same |

Row 3 is lower because `C_hist ≲ R^{5/2}` in Lean (`deg_E3c`, against `R³ L` of `JOINT_METRIC`, H3).
Row 6 is higher because the logarithm of `Z` is paid by `q^{1/8}`: `q^{15/8}`, `q^{23/8}` in place
of `q²`, `q³`.  Both stay `≤ 3`, so `Z` is not tied.  The only tied rows are 2 and the operator
norm of the metric (`deg_forceK`), both at `R³`; the companion `P_F (1 + B_S) H₀` is tied at `U R³`.

`H¹`: `forceK` at `D = R`: `2¹⁰ B` `(0, 2)`, static `(0, 3)`, heat root `(0, 9/4)`, `Z` `(0, 3)`;
source `h_L` `(0, 5/2)`, `√h_Q` `(0, 1)`; tested `P_F² h_L` `(2, 5/2)`, `√(P_F² h_Q)` `(1, 1)`.

The tested prices are those of roles 11–12, `U² R^{5/2}`, `U R`.  `force2Q_below`, `force1Q_below`,
`force0Q_below`, `role18J_below`: all are `JointBelow`, with no hypothesis but `0 ≤ C`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace OVNS.Quant

namespace JDeg

variable {a b : ℝ} {m m' : ℝ → ℝ → Caps → ℝ}

/-- **Comparison on the domain.** -/
theorem of_le (h : JDeg a b m)
    (hle : ∀ R₀ X R : ℝ, JDom R₀ X R → ∀ caps, 0 ≤ m' X R caps ∧ m' X R caps ≤ m X R caps) :
    JDeg a b m' := by
  intro K c hK hc
  obtain ⟨C, c', R₀, hC, hm⟩ := h K c hK hc
  refine ⟨C, c', R₀, hC, fun X R hdom caps hcaps ↦ ?_⟩
  obtain ⟨h0, h1⟩ := hle _ _ _ hdom caps
  exact ⟨h0, h1.trans (hm X R hdom caps hcaps).2⟩

/-- Equality on the domain. -/
theorem congr' (h : JDeg a b m)
    (he : ∀ R₀ X R : ℝ, JDom R₀ X R → ∀ caps, m' X R caps = m X R caps) : JDeg a b m' := by
  intro K c hK hc
  obtain ⟨C, c', R₀, hC, hm⟩ := h K c hK hc
  exact ⟨C, c', R₀, hC, fun X R hdom caps hcaps ↦ by
    rw [he _ _ _ hdom]
    exact hm X R hdom caps hcaps⟩

end JDeg

/-- `JointBelow` is stable under sums. -/
theorem JointBelow.add' {q q' : ℝ → ℝ → Caps → ℝ} (h : JointBelow q) (h' : JointBelow q') :
    JointBelow fun X R caps ↦ q X R caps + q' X R caps := by
  intro K c hK hc
  obtain ⟨C, C₀, R₀, hb⟩ := (h.sup h').const_mul (a := 2) (by norm_num) K c hK hc
  refine ⟨C, C₀, R₀, fun X R hdom caps hcaps ↦ le_trans ?_ (hb X R hdom caps hcaps)⟩
  have h1 := le_max_left (q X R caps) (q' X R caps)
  have h2 := le_max_right (q X R caps) (q' X R caps)
  linarith

namespace Metric

open JDeg

variable {C e : ℝ}

private lemma c4_nn (k : ℝ) (hk : 0 ≤ k) : 0 ≤ k * c4 := mul_nonneg hk c4_pos.le

/-! ### The force -/

/-- `h_L ≲ R^{5/2}`: `J_F ≤ R³` on the sector. -/
theorem deg_hLc : JDeg 0 (5 / 2) fun X R caps ↦ hLc (R - X) caps :=
  ((phi.const_mul (c4_nn 32 (by norm_num))).mul (JS.add (JF.up 0 3)).sqrt).up 0 (5 / 2)

/-- `h_Q ≲ R²`. -/
theorem deg_hQc : JDeg 0 2 fun X R _ ↦ hQc (R - X) :=
  ((phi.pow 2).const_mul (c4_nn 64 (by norm_num))).up 0 2

/-- `j_L ≲ R³`. -/
theorem deg_jLc : JDeg 0 3 fun X R caps ↦ jLc (R - X) caps :=
  ((phi.const_mul (c4_nn 32 (by norm_num))).mul (BS.add (yF.up 0 2))).up 0 3

/-- `j_Q ≲ R²`. -/
theorem deg_jQc : JDeg 0 2 fun X R _ ↦ jQc (R - X) :=
  ((phi.pow 2).const_mul (c4_nn 32 (by norm_num))).up 0 2

/-! ### The coefficients -/

theorem deg_E1c : JDeg 1 0 fun _ _ caps ↦ E1c caps :=
  ((const zero_le_one).up 1 0).add (PF.const_mul (c4_nn 48 (by norm_num)))

theorem deg_E2c : JDeg 0 2 fun _ _ caps ↦ E2c caps :=
  BS.const_mul (by positivity)

private theorem hy1 : JDeg (1 / 2) (1 / 2) fun _ _ caps ↦ cp caps.yF + 1 :=
  yF.add ((const zero_le_one).up (1 / 2) (1 / 2))

private theorem hbudW : JDeg 0 (3 / 2) fun _ _ caps ↦ budW caps :=
  (WS.add ((yF.const_mul c4_pos.le).up 0 (3 / 2))).add
    ((const (c4_nn 3 (by norm_num))).up 0 (3 / 2))

/-- `J_{3,pre} ≲ U R⁴`. -/
theorem deg_J3pre : JDeg 1 4 fun _ _ caps ↦ J3pre 4 caps := by
  have h1 := (yF.pow 2).up 1 4
  have h2 := ((hbudW.pow 2).const_mul (by norm_num : (0 : ℝ) ≤ 4)).up 0 3
  have h3 := (JS.const_mul (sq_nonneg c4)).up 0 3
  have h4 := ((hy1.pow 2).const_mul (by norm_num : (0 : ℝ) ≤ 128)).mul (h2.add h3)
  exact h1.add (h4.up 1 4)

/-- `P_S(1) ≲ R⁵`. -/
theorem deg_price1 (hC : 0 ≤ C) : JDeg 0 5 fun _ R _ ↦ slowPrice C (Ex e R) R 1 := by
  have h1 := ((R.pow 4).up 0 5).add (((const zero_le_one).mul (R.pow 5)).up 0 5)
  exact (((ex e).const_mul hC).mul h1).up 0 5

/-- `C_hist² ≲ R⁵`. -/
theorem deg_chist (hC : 0 ≤ C) : JDeg 0 5 fun _ R caps ↦ chistSq C (Ex e R) R caps := by
  have h1 := (deg_price1 (e := e) hC).const_mul (by norm_num : (0 : ℝ) ≤ 8)
  have h2 := (deg_J3pre.up 0 5).const_mul (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 13)
  refine (h1.add h2).congr' fun _ X R _ caps ↦ ?_
  unfold chistSq
  ring

/-- `C_hist ≲ R^{5/2}`. -/
theorem deg_E3c (hC : 0 ≤ C) : JDeg 0 (5 / 2) fun _ R caps ↦ E3c C (Ex e R) R caps :=
  ((deg_chist (e := e) hC).sqrt.const_mul (c4_nn (2 ^ 11) (by norm_num))).up 0 (5 / 2)

private theorem hlogD : JDeg 0 0 fun _ R _ ↦ 9 + 8 * Real.log (jointD R) := by
  have h := logR.const_mul (by norm_num : (0 : ℝ) ≤ 16)
  refine h.of_le fun _ X R hdom _ ↦ ?_
  have e1 : Real.log (jointD R) = 2 * Real.log R := by
    unfold jointD
    rw [Real.log_pow]
    norm_num
  have h1 : 0 ≤ Real.log R := Real.log_nonneg hdom.one_lt_R.le
  rw [e1]
  constructor <;> linarith

theorem deg_E4c : JDeg 0 3 fun _ R caps ↦ E4c (jointD R) caps := by
  have h1 := ((WS.pow 2).const_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 29)).up 0 3
  have h2 := ((hlogD.const_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 19)).mul (AS.pow 2)).up 0 3
  exact h1.add h2

private theorem hcls : JDeg 0 4 fun _ _ caps ↦
    cls2 (cp caps.WS) (cp caps.WS) (cp caps.BS) (cp caps.BS) := by
  have h1 := (WS.mul WS).up 0 4
  have h2 := (((BS.mul WS).up 0 4).add ((WS.mul BS).up 0 4)).const_mul
    (by have := c4_pos; positivity : (0 : ℝ) ≤ 2 * c4)
  have h3 := ((BS.mul BS).up 0 4).const_mul (sq_nonneg c4)
  exact (h1.add h2).add h3

private theorem hD2 : JDeg 0 2 fun _ R _ ↦ jointD R := (R.pow 2).up 0 2

theorem deg_E5c : JDeg 0 6 fun _ R caps ↦ E5c (jointD R) caps :=
  ((hD2.const_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 20)).mul hcls).up 0 6

theorem deg_E6c (hC : 0 ≤ C) : JDeg 0 3 fun _ R caps ↦ E6c (C * Ex e R * R) caps := by
  have h1 := ((const zero_le_one).up 0 1).add (Minf (e := e) hC)
  have hZ : (0 : ℝ) ≤ 18 * CZh := by
    have := CZh_pos
    positivity
  exact ((h1.const_mul hZ).mul BS).up 0 3

theorem deg_E7c (hC : 0 ≤ C) :
    JDeg 0 (5 / 2) fun _ R caps ↦ E7c C (Ex e R) R (jointD R) caps := by
  have h0 : JDeg 0 (1 / 2) fun _ R _ ↦ Real.sqrt (slowPrice C (Ex e R) R 1) / jointD R := by
    refine (((deg_price1 (e := e) hC).sqrt.mul (Rpow (-2))).up 0 (1 / 2)).congr'
      fun _ X R hdom _ ↦ ?_
    rw [jointD, Real.rpow_neg hdom.R_pos.le, Real.rpow_two, div_eq_mul_inv]
  have h1 := h0.add ((const delta0_pos.le).up 0 (1 / 2))
  have hZ : (0 : ℝ) ≤ 4 * Cm2 := by
    have := Cm2_pos
    positivity
  exact ((BS.const_mul hZ).mul h1).up 0 (5 / 2)

/-! ### The seven pairs -/

/-- One root of the table. -/
private theorem row {a b a' b' : ℝ} {E m : ℝ → ℝ → Caps → ℝ} (hE : JDeg a b E) (hm : JDeg a' b' m)
    (x : ℝ) (hx : 0 < x) :
    JDeg ((a + a') * (1 / x)) ((b + b') * (1 / x)) fun X R caps ↦
      rootQ x (2 ^ 12 * (E X R caps * m X R caps)) :=
  ((hE.mul hm).const_mul (by norm_num)).root (1 / x) (by positivity)

/-- **Role 29**, line by line. -/
theorem deg_role29J (hC : 0 ≤ C) : JDeg 1 3 fun X R caps ↦
    role29J (R - X) (jointD R) (C * Ex e R * R) C (Ex e R) R caps := by
  have h1 := (row deg_E1c deg_hLc (0 + 1) (by norm_num)).up 1 (5 / 2)
  have h2 := (row deg_E2c deg_hLc (1 / 2 + 1) (by norm_num)).up 0 3
  have h3 := (row (deg_E3c (e := e) hC) deg_jLc (1 + 1) (by norm_num)).up 0 (11 / 4)
  have h4 := (row deg_E4c deg_hLc (1 + 1) (by norm_num)).up 0 (11 / 4)
  have h5 := (row deg_E5c deg_hLc (2 + 1) (by norm_num)).up 0 (17 / 6)
  have h6 := (row (deg_E6c (e := e) hC) deg_hLc (7 / 8 + 1) (by norm_num)).up 0 (44 / 15)
  have h7 := (row (deg_E7c (e := e) hC) deg_jLc (1 + 1) (by norm_num)).up 0 (11 / 4)
  exact ((((((h1.up 1 3).add (h2.up 1 3)).add (h3.up 1 3)).add (h4.up 1 3)).add (h5.up 1 3)).add
    (h6.up 1 3)).add (h7.up 1 3)

/-- **Role 30**, line by line. -/
theorem deg_role30J (hC : 0 ≤ C) : JDeg 1 3 fun X R caps ↦
    role30J (R - X) (jointD R) (C * Ex e R * R) C (Ex e R) R caps := by
  have h1 := (row deg_E1c deg_hQc (0 + 2) (by norm_num)).up (1 / 2) 1
  have h2 := (row deg_E2c deg_hQc (1 / 2 + 2) (by norm_num)).up 0 (8 / 5)
  have h3 := (row (deg_E3c (e := e) hC) deg_jQc (1 + 2) (by norm_num)).up 0 (3 / 2)
  have h4 := (row deg_E4c deg_hQc (1 + 2) (by norm_num)).up 0 (5 / 3)
  have h5 := (row deg_E5c deg_hQc (2 + 2) (by norm_num)).up 0 2
  have h6 := (row (deg_E6c (e := e) hC) deg_hQc (7 / 8 + 2) (by norm_num)).up 0 (40 / 23)
  have h7 := (row (deg_E7c (e := e) hC) deg_jQc (1 + 2) (by norm_num)).up 0 (3 / 2)
  exact ((((((h1.up 1 3).add (h2.up 1 3)).add (h3.up 1 3)).add (h4.up 1 3)).add (h5.up 1 3)).add
    (h6.up 1 3)).add (h7.up 1 3)

/-- **The `H²` threshold of the force is below `Q`.** -/
theorem force2Q_below (hC : 0 ≤ C) : JointBelow fun X R caps ↦
    force2Q (R - X) (jointD R) (C * Ex e R * R) C (Ex e R) R caps :=
  (jointBudget_below.add' (deg_role29J (e := e) hC).toQ).add' (deg_role30J (e := e) hC).toQ

/-! ### Weight one -/

/-- The operator norm of the metric at `D = R`: `(0, 2)`, `(0, 3)`, `(0, 9/4)`, `(0, 3)`. -/
theorem deg_forceK (hC : 0 ≤ C) : JDeg 0 3 fun _ R caps ↦ forceK R (C * Ex e R * R) caps := by
  have hL : JDeg 0 0 fun _ R _ ↦ 1 + Real.sqrt (1 + Real.log R) :=
    (const zero_le_one).add (logR.sqrt.up 0 0)
  have hB2 : JDeg 0 3 fun _ R caps ↦ cp caps.BS ^ 2 / R := by
    refine (((BS.pow 2).mul (Rpow (-1))).up 0 3).congr' fun _ X R hdom _ ↦ ?_
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  have h1 := (BS.const_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 10)).up 0 3
  have hS := (((hL.mul (AS.pow 2)).up 0 3).add
    (((AS.mul WS).const_mul (by norm_num : (0 : ℝ) ≤ 2)).up 0 3)).add hB2
  have h2 := ((hS.const_mul Cst_nonneg).const_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 4))
  have h3 := (((R.mul (AS.mul BS)).const_mul Cst_nonneg).const_mul
    (by norm_num : (0 : ℝ) ≤ 2 ^ 4)).root (1 / 2)
  have h4 := ((((Minf (e := e) hC).const_mul CZ_nonneg).mul BS).const_mul
    (by norm_num : (0 : ℝ) ≤ 8))
  exact ((h1.add (h2.up 0 3)).add (h3.up 0 (9 / 4) |>.up 0 3)).add (h4.up 0 3)

/-- **The `H¹` threshold of the force is below `Q`**: operator norm, source, tested. -/
theorem force1Q_below (hC : 0 ≤ C) : JointBelow fun X R caps ↦
    force1Q (R - X) R (C * Ex e R * R) caps := by
  have hc : (0 : ℝ) ≤ 2 ^ 8 * c4 := c4_nn _ (by norm_num)
  have h1 := (deg_forceK (e := e) hC).toQ
  have h2 := (deg_hLc.const_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 3)).toQ
  have h3 := ((deg_hQc.const_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 3)).root (1 / 2)).toQ
  have h4 := (((PF.pow 2).const_mul hc).mul deg_hLc).toQ
  have h5 := ((((PF.pow 2).const_mul hc).mul deg_hQc).root (1 / 2)).toQ
  exact (((((jointBudget_below.add' h1).add' h2).add' h3).add' h4).add' h5)

/-! ### The companions, and role 18 -/

/-- `H₀ ≲ R`. -/
theorem deg_H0c : JDeg 0 1 fun X R caps ↦ H0c (R - X) caps := by
  have h1 := (phi.const_mul (by norm_num : (0 : ℝ) ≤ 4)).up 0 1
  have h2 := ((yF.mul JF.sqrt).const_mul (c4_nn 16 (by norm_num))).up 0 1
  exact (h1.add h2).add ((const (by norm_num : (0 : ℝ) ≤ 2)).up 0 1)

/-- The companions: tied at `U R³`. -/
theorem deg_force0Q : JDeg 1 3 fun X R caps ↦ force0Q (R - X) caps :=
  ((((const zero_le_one).up 1 0).add PF).mul (((const zero_le_one).up 0 2).add BS)).mul deg_H0c
    |>.up 1 3

theorem force0Q_below : JointBelow fun X R caps ↦ force0Q (R - X) caps := deg_force0Q.toQ

/-- Role 18: `(0, 3)`, `(0, 1)`. -/
theorem deg_role18J : JDeg 0 3 fun X R caps ↦ role18J (R - X) caps :=
  (deg_jLc.const_mul (by norm_num : (0 : ℝ) ≤ 4)).add
    (((deg_jQc.const_mul (by norm_num : (0 : ℝ) ≤ 4)).root (1 / 2)).up 0 3)

theorem role18J_below : JointBelow fun X R caps ↦ role18J (R - X) caps := deg_role18J.toQ

end Metric

end OVNS.Quant

end
