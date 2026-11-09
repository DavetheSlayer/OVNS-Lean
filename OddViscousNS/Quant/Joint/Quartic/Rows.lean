import OddViscousNS.Quant.Joint.Quartic.Price1
import OddViscousNS.Quant.Joint.Assembly.Roles

/-!
# The true monomials of `C_{4,1}`, `C_{4,2}` against `JointBelow` (step J5, node N11)

The coefficients of `Price2.lean`, `Price1.lean` at the caps, and their degrees in the calculus
`JDeg` of J6 (`Assembly/Degree.lean`).  As in `rowQuarticNear`, `P(q)` is paid by the floor
`Q^{1/3}` of `jointLP`: a coefficient `Z` of `q⁻¹ P(q)` is the threshold `Z/Q^{1/3}` (`zq`).  So "the squared
Young numerators and the nonlinear debit keep their different powers of `q`": the Young terms are
thresholds at the square root of the numerator, `(κ Cy)² P_S ≲ T²`, the debit is a threshold at `Z`.

`fibL` is the cap of `L_h(F)`, from `lhB_log` at `D = R`.

The true monomials (`U^a R^b`, with `L ≍ U`, `y ≍ (UR)^{1/2}`, `B ≍ R²`, `A, W ≍ R^{3/2}`, `M ≍ R`):

| term | monomial | degree before `zq` | after |
|---|---|---:|---:|
| `tS` | static `B L` | `(1, 2)` | `(2/3, 1)` |
| `tM` | clip mass `L B²/λ_*` | `(2, 3)` | `(5/3, 2)` |
| `tC` | `c_F²`: `B y M` | `(1/2, 7/2)` | `(1/6, 5/2)` |
| | `B L M` | `(1, 3)` | `(2/3, 2)` |
| | `B L²` | `(2, 2)` | `(5/3, 1)` |
| | `L y W` | `(3/2, 2)` | `(7/6, 1)` |
| `tY` | short: `B L² √P_S/T` | `(2, 7/2)` | `(5/3, 5/2)` |
| | `L y W √P_S/T` | `(3/2, 7/2)` | `(7/6, 5/2)` |
| `tG` | genuine: `L y R √(1/λ_*)/T` | `(3/2, 1/2)` | `(7/6, −1/2)` |
| `m₁` | `H¹` debit: `B L N_F` | `(1, 4)` | `(2/3, 3)` |
| | `N_S L`, `A P N_F`, `A L N_F` | `(1, 7/2)` | `(2/3, 5/2)` |
| `y₁` | `H¹` genuine debit: `B L` | `(1, 2)` | `(2/3, 1)` |
| `tA` | `H¹` static, squared: `Q^{−2/3} A B L²` | | `(4/3, 3/2)` |

The lemmas below keep only envelopes: `deg_Cc` is `(4/3, 4)`, so `deg_tC` is `(1, 3)`.
-/

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

/-- `5 √(1 + ln R)`. -/
def logL (R : ℝ) : ℝ := 5 * Real.sqrt (1 + Real.log R)

/-- **The cap of `L_h(F)`** (`lhB_log` at `D = R`). -/
def fibL (R : ℝ) (caps : Caps) : ℝ := logL R * cp caps.PF + 5 / R * cp caps.yF

/-- `16 c_I √(P y)`. -/
def capCp (caps : Caps) : ℝ := 16 * cI * Real.sqrt (cp caps.PF * cp caps.yF)

/-- **The parameters of the weight-two prices at the caps**, with `D = R²` and, for `q ≥ R³`,
`φ/q ≤ R⁻²` (J3-v2 §4). -/
def co2 (CS cS R : ℝ) (caps : Caps) : Co where
  L := fibL R caps
  y := cp caps.yF
  B := cp caps.BS
  W := cp caps.WS
  D := R ^ 2
  Lg := logL R
  P₀ := 2 * CLow 2 * (CS * Ex cS R * R) + capCp caps
  Cp := capCp caps
  E := 64 * c4 / R ^ 2
  G := 64 * c4 / R ^ 4
  φ := R

/-- `U⁻¹ R⁻¹`: `1/T²`. -/
def uInv (X R : ℝ) : ℝ := jointU X ^ (-1 : ℝ) * R ^ (-1 : ℝ)

/-- `Q^{−1/3}`: the price of `P(q)`. -/
def zq (X R : ℝ) : ℝ := (jointQ X R ^ ((1 : ℝ) / 3))⁻¹

/-- The clip length. -/
def lamI (X R : ℝ) (caps : Caps) : ℝ := 1 / jointLam X R caps

/-- The slow price of a clip. -/
def priceS (CS cS X R : ℝ) (caps : Caps) : ℝ := slowPrice CS (Ex cS R) R (lamI X R caps)

section

variable (CS cS X R : ℝ) (caps : Caps)

/-- The static term of `C_{4,2}`. -/
def tS : ℝ := (co2 CS cS R caps).B * (co2 CS cS R caps).L * zq X R

/-- The clip mass of `C_{4,2}`. -/
def tM : ℝ := (co2 CS cS R caps).Mm * lamI X R caps * zq X R

/-- The coefficient of `c_F²`. -/
def tC : ℝ := (co2 CS cS R caps).Cc * zq X R

/-- The short term. -/
def tY : ℝ :=
  Real.sqrt ((co2 CS cS R caps).Cy ^ 2 * priceS CS cS X R caps * uInv X R) * zq X R

/-- The genuine term. -/
def tG : ℝ := Real.sqrt ((co2 CS cS R caps).Ga ^ 2 * lamI X R caps * uInv X R) * zq X R

/-- **The threshold of `C_{4,2}`**: the sum of the five terms. -/
def thrTwo : ℝ := tS CS cS X R caps + tM CS cS X R caps + tC CS cS X R caps +
  tY CS cS X R caps + tG CS cS X R caps

/-- The floors of `C_{4,2}`. -/
def flrTwo : ℝ := R ^ 3 + 2 ^ 11 * c4 * cp caps.yF + 1

/-- `18 √(1 + ln R)`: `√(9 + 4/ε)` at J3-v2's `ε = min(1/64, 1/(8 + ln R))`. -/
def logE (R : ℝ) : ℝ := 18 * Real.sqrt (1 + Real.log R)

/-- **The parameters of the weight-one prices at the caps.** -/
def co1 (X R : ℝ) (caps : Caps) : Co1 where
  L := fibL R caps
  P := cp caps.PF
  A := cp caps.AS
  B := cp caps.BS
  Ns := hSrc (R - X) caps
  Nb := 8 * (cp caps.WS + c4 * cp caps.BS + c4 * cp caps.yF)
  Le := logE R

/-- The nonlinear debit of `C_{4,1}`. -/
def tM₁ : ℝ := (co1 X R caps).m₁ * zq X R

/-- The genuine debit of `C_{4,1}`. -/
def tY₁ : ℝ := (co1 X R caps).y₁ * zq X R

/-- The static term of `C_{4,1}`, squared: `q ≥ (Q^{−1/3} √(a b) L)²`. -/
def tA₁ : ℝ := zq X R ^ 2 * (cp caps.AS * cp caps.BS) * fibL R caps ^ 2

/-- **The threshold of `C_{4,1}`.** -/
def thrOne : ℝ := tM₁ X R caps + tY₁ X R caps + tA₁ X R caps

end

section Degrees

open JDeg

variable {CS cS : ℝ}

/-- A function equal to one of degree `(a, b)`. -/
theorem deg_congr {a b : ℝ} {m m' : ℝ → ℝ → Caps → ℝ} (h : JDeg a b m)
    (e : ∀ X R caps, m X R caps = m' X R caps) : JDeg a b m' := by
  have : m = m' := funext fun X => funext fun R => funext fun caps => e X R caps
  rwa [← this]

/-- `k/Rⁿ`. -/
theorem deg_div_pow {k : ℝ} (hk : 0 ≤ k) (n : ℕ) :
    JDeg 0 (-(n : ℝ)) fun _ R (_ : Caps) ↦ k / R ^ n := fun _ _ _ _ ↦
  ⟨k, 0, 0, hk, fun X R hdom _ _ ↦ by
    have hR := hdom.R_pos
    refine ⟨by positivity, ?_⟩
    rw [Real.rpow_zero, Ex_zero, Real.rpow_neg hR.le, Real.rpow_natCast]
    simp only [one_mul, mul_one]
    exact le_of_eq (div_eq_mul_inv _ _)⟩

theorem deg_uInv : JDeg (-1) (-1) fun X R (_ : Caps) ↦ uInv X R := fun _ _ _ _ ↦
  ⟨1, 0, 0, zero_le_one, fun X R hdom _ _ ↦ by
    have hU0 : 0 < jointU X := by linarith [hdom.one_lt_U]
    refine ⟨mul_nonneg (Real.rpow_nonneg hU0.le _) (Real.rpow_nonneg hdom.R_pos.le _), ?_⟩
    simp [uInv, Ex_zero]⟩

theorem deg_zq : JDeg (-(1 / 3)) (-1) fun X R (_ : Caps) ↦ zq X R := invQ

theorem deg_logL : JDeg 0 0 fun _ R (_ : Caps) ↦ logL R := by
  have h := logR.sqrt.const_mul (k := 5) (by norm_num)
  simpa [logL] using h

theorem deg_logE : JDeg 0 0 fun _ R (_ : Caps) ↦ logE R := by
  have h := logR.sqrt.const_mul (k := 18) (by norm_num)
  simpa [logE] using h

theorem deg_fibL : JDeg 1 0 fun _ R caps ↦ fibL R caps := by
  have h1 := (deg_logL.mul PF).up 1 0
  have h2 := ((deg_div_pow (k := 5) (by norm_num) 1).mul yF).up 1 0
  exact deg_congr (h1.add h2) fun X R caps => by simp [fibL]

theorem deg_Cp : JDeg (3 / 4) (1 / 4) fun _ _ caps ↦ capCp caps :=
  ((PF.mul yF).sqrt.const_mul (k := 16 * cI) (by have := cI_pos; positivity)).up (3 / 4) (1 / 4)

theorem deg_P₀ (hCS : 0 ≤ CS) :
    JDeg 0 1 fun _ R caps ↦ (co2 CS cS R caps).P₀ := by
  have hc : 0 ≤ 2 * CLow 2 := mul_nonneg (by norm_num) (CLow_nonneg 2)
  exact ((Minf (e := cS) hCS).const_mul hc).add (deg_Cp.up 0 1)

theorem deg_E : JDeg 0 (-2) fun _ R caps ↦ (co2 CS cS R caps).E :=
  (deg_div_pow (k := 64 * c4) (by have := c4_pos; positivity) 2).up 0 (-2)

theorem deg_G : JDeg 0 (-4) fun _ R caps ↦ (co2 CS cS R caps).G :=
  (deg_div_pow (k := 64 * c4) (by have := c4_pos; positivity) 4).up 0 (-4)

theorem deg_A₁ : JDeg 1 0 fun _ R caps ↦ (co2 CS cS R caps).A₁ :=
  (deg_fibL.const_mul (k := 20) (by norm_num)).add (deg_E.up 1 0)

theorem deg_A₂ : JDeg 1 (-2) fun _ R caps ↦ (co2 CS cS R caps).A₂ := by
  have h1 := ((deg_fibL.mul (deg_div_pow (k := 100) (by norm_num) 2)).up 1 (-2))
  have h2 := (deg_E (CS := CS) (cS := cS)).const_mul (k := 5) (by norm_num) |>.up 1 (-2)
  refine deg_congr (h1.add h2) fun X R caps => ?_
  simp only [Co.A₂, co2]
  ring

theorem deg_A₃ : JDeg 0 (3 / 2) fun _ R caps ↦ (co2 CS cS R caps).A₃ :=
  (WS.const_mul (k := 16) (by norm_num)).add (deg_E.up 0 (3 / 2))

theorem deg_P₁ (hCS : 0 ≤ CS) : JDeg 0 1 fun _ R caps ↦ (co2 CS cS R caps).P₁ :=
  (deg_P₀ hCS).add (deg_E.up 0 1)

theorem deg_Mm : JDeg 1 4 fun _ R caps ↦ (co2 CS cS R caps).Mm :=
  (((deg_fibL.const_mul (k := 20) (by norm_num)).mul deg_logL).mul (BS.pow 2)).up 1 4

theorem deg_Cc (hCS : 0 ≤ CS) : JDeg (4 / 3) 4 fun _ R caps ↦ (co2 CS cS R caps).Cc := by
  have a := (deg_A₃ (CS := CS) (cS := cS)).add (deg_Cp.up 0 (3 / 2)) |>.add
    ((deg_E (CS := CS) (cS := cS)).up 0 (3 / 2))
  have t1 := ((deg_fibL.mul yF).mul a).up (4 / 3) 4
  have b := ((deg_A₂ (CS := CS) (cS := cS)).up 0 1).add
    ((deg_P₁ (cS := cS) hCS).const_mul (k := 5) (by norm_num))
  have t2 := ((BS.mul yF).mul b).up (4 / 3) 4
  have c := ((deg_A₁ (CS := CS) (cS := cS)).up 0 1).add (deg_P₁ (cS := cS) hCS)
  have t3 := (((BS.const_mul (k := 2) (by norm_num)).mul deg_fibL).mul c).up (4 / 3) 4
  exact (t1.add t2).add t3

theorem deg_Cy : JDeg 2 2 fun _ R caps ↦ (co2 CS cS R caps).Cy := by
  have t1 := ((deg_fibL.mul yF).mul (deg_A₃ (CS := CS) (cS := cS))).up 2 2
  have t2 := ((BS.mul yF).mul (deg_A₂ (CS := CS) (cS := cS))).up 2 2
  have t3 := (((BS.const_mul (k := 2) (by norm_num)).mul deg_fibL).mul
    (deg_A₁ (CS := CS) (cS := cS))).up 2 2
  exact (t1.add t2).add t3

theorem deg_Ga : JDeg (3 / 2) (3 / 2) fun _ R caps ↦ (co2 CS cS R caps).Ga := by
  have a := ((deg_G (CS := CS) (cS := cS)).up 0 1).add (JDeg.R)
  have t1 := ((deg_fibL.mul yF).mul a).up (3 / 2) (3 / 2)
  have t2 := (((BS.const_mul (k := 5) (by norm_num)).mul yF).mul
    (deg_G (CS := CS) (cS := cS))).up (3 / 2) (3 / 2)
  have t3 := (((BS.const_mul (k := 2) (by norm_num)).mul deg_fibL).mul
    (deg_G (CS := CS) (cS := cS))).up (3 / 2) (3 / 2)
  exact (t1.add t2).add t3

/-- `tS`: `(2/3, 1)`. -/
theorem deg_tS : JDeg (2 / 3) 1 fun X R caps ↦ tS CS cS X R caps :=
  ((BS.mul deg_fibL).mul deg_zq).up (2 / 3) 1

/-- `tM`: `(5/3, 2)`, the added mass. -/
theorem deg_tM : JDeg (5 / 3) 2 fun X R caps ↦ tM CS cS X R caps :=
  (((deg_Mm (CS := CS) (cS := cS)).mul invLam).mul deg_zq).up (5 / 3) 2

/-- `tC`: at most `(1, 3)`. -/
theorem deg_tC (hCS : 0 ≤ CS) : JDeg 1 3 fun X R caps ↦ tC CS cS X R caps :=
  ((deg_Cc (cS := cS) hCS).mul deg_zq).up 1 3

/-- `tY`: `(5/3, 5/2)`, the short term. -/
theorem deg_tY (hCS : 0 ≤ CS) : JDeg (5 / 3) (5 / 2) fun X R caps ↦ tY CS cS X R caps := by
  have hP := price (e := cS) hCS
  have h := (((deg_Cy (CS := CS) (cS := cS)).pow 2).mul hP).mul deg_uInv
  exact (h.sqrt.mul deg_zq).up (5 / 3) (5 / 2)

/-- `tG`: `(7/6, −1/2)`, the genuine term. -/
theorem deg_tG : JDeg (7 / 6) (-1 / 2) fun X R caps ↦ tG CS cS X R caps := by
  have h := (((deg_Ga (CS := CS) (cS := cS)).pow 2).mul invLam).mul deg_uInv
  exact (h.sqrt.mul deg_zq).up (7 / 6) (-1 / 2)

/-- **The threshold of `C_{4,2}` has degree at most `(1, 3)`.** -/
theorem deg_thrTwo (hCS : 0 ≤ CS) : JDeg 1 3 fun X R caps ↦ thrTwo CS cS X R caps :=
  (((((deg_tS (CS := CS) (cS := cS)).up 1 3).add ((deg_tM (CS := CS) (cS := cS)).up 1 3)).add
    (deg_tC hCS)).add ((deg_tY hCS).up 1 3)).add ((deg_tG (CS := CS) (cS := cS)).up 1 3)

theorem deg_flrTwo : JDeg 1 3 fun _ R caps ↦ flrTwo R caps :=
  ((((JDeg.R.pow 3).up 1 3).add ((yF.const_mul (k := 2 ^ 11 * c4)
    (by have := c4_pos; positivity)).up 1 3)).add ((const (k := 1) zero_le_one).up 1 3))

/-- **The row of `C_{4,2}` is `JointBelow`**, for any fixed factor `A`. -/
theorem qTwo_below (hCS : 0 ≤ CS) {A : ℝ} (hA : 0 ≤ A) :
    JointBelow fun X R caps ↦ A * thrTwo CS cS X R caps + flrTwo R caps :=
  (((deg_thrTwo (cS := cS) hCS).const_mul hA).add deg_flrTwo).toQ

theorem deg_hSrc : JDeg 0 (7 / 2) fun X R caps ↦ hSrc (R - X) caps := by
  have c4n : 0 ≤ c4 := c4_pos.le
  have a := (WS.add ((yF.const_mul c4n).up 0 (3 / 2))).add ((const c4n).up 0 (3 / 2))
  have b := (BS.add (yF.up 0 2)).add ((const (k := 1) zero_le_one).up 0 2)
  have h := ((a.mul b).const_mul (k := 8) (by norm_num)).up 0 (7 / 2)
  exact deg_congr (h.add (phi.up 0 (7 / 2))) fun X R caps => by simp only [hSrc]; ring

theorem deg_Nb : JDeg 0 2 fun X R caps ↦ (co1 X R caps).Nb := by
  have c4n : 0 ≤ c4 := c4_pos.le
  exact (((WS.up 0 2).add (BS.const_mul c4n)).add ((yF.const_mul c4n).up 0 2)).const_mul
    (k := 8) (by norm_num)

theorem deg_m₁ : JDeg 1 4 fun X R caps ↦ (co1 X R caps).m₁ := by
  have t1 := (((deg_hSrc.const_mul (k := 2) (by norm_num))).mul deg_fibL).up 1 4
  have t2 := ((((AS.const_mul (k := 2) (by norm_num)).mul deg_logE).mul PF).mul deg_Nb).up 1 4
  have t3 := (((BS.const_mul (k := 2) (by norm_num)).mul deg_fibL).mul deg_Nb).up 1 4
  have t4 := (((AS.const_mul (k := 2) (by norm_num)).mul deg_fibL).mul deg_Nb).up 1 4
  exact ((t1.add t2).add t3).add t4

theorem deg_y₁ : JDeg 1 2 fun X R caps ↦ (co1 X R caps).y₁ := by
  have t2 := ((AS.const_mul (k := 2) (by norm_num)).mul deg_logE |>.mul PF).up 1 2
  have t3 := ((BS.const_mul (k := 2) (by norm_num)).mul deg_fibL).up 1 2
  have t4 := ((AS.const_mul (k := 2) (by norm_num)).mul deg_fibL).up 1 2
  exact (t2.add t3).add t4

/-- `tM₁`: `(2/3, 3)`: "`U^{−1/3}` at trial". -/
theorem deg_tM₁ : JDeg (2 / 3) 3 fun X R caps ↦ tM₁ X R caps :=
  (deg_m₁.mul deg_zq).up (2 / 3) 3

/-- `tY₁`: `(2/3, 1)`. -/
theorem deg_tY₁ : JDeg (2 / 3) 1 fun X R caps ↦ tY₁ X R caps :=
  (deg_y₁.mul deg_zq).up (2 / 3) 1

/-- `tA₁`: `(4/3, 3/2)`. -/
theorem deg_tA₁ : JDeg (4 / 3) (3 / 2) fun X R caps ↦ tA₁ X R caps :=
  (((deg_zq.pow 2).mul (AS.mul BS)).mul (deg_fibL.pow 2)).up (4 / 3) (3 / 2)

/-- **The threshold of `C_{4,1}` has degree at most `(1, 3)`**, with the debit at `(2/3, 3)`. -/
theorem deg_thrOne : JDeg 1 3 fun X R caps ↦ thrOne X R caps :=
  ((deg_tM₁.up 1 3).add (deg_tY₁.up 1 3)).add (deg_tA₁.up 1 3)

/-- **The row of `C_{4,1}` is `JointBelow`.** -/
theorem qOne_below {A : ℝ} (hA : 0 ≤ A) :
    JointBelow fun X R caps ↦ A * thrOne X R caps + flrTwo R caps :=
  ((deg_thrOne.const_mul hA).add deg_flrTwo).toQ

end Degrees

end OVNS.Quant.Quartic

end
