import OddViscousNS.Quant.Joint.Assembly.Degree

/-!
# J6: the printed role table against `JointBelow`

`q₁Env`, `q₂Env`: the envelopes of the roles of E5-J and E8-J, as functions of the caps, from
Tables quant-metric and the table of the joint proof (`quantitative_regimes.tex`), Bodies 40–43, 47
and report `t12_joint_documents.md` §3.  `q₁Env_below`, `q₂Env_below`: both are `JointBelow`.

This is a check of arithmetic, not a proof of the energies: it says that the monomials the sources
print are paid at the Lean caps `CapsScaledJ`, at the Lean normalizations (`B_* = T/P_F`, `D = R²`,
`M_∞ = C_S Ex(c_S, R) R`, `P_S = slowPrice`), and that no monomial needs a lower bound on a slow
cap.  It is also the shape of `q₁`, `q₂` for J5: a threshold bounded by a constant times these
envelopes (plus `jointSlowFloor`, `Assembly/Package.lean`) is `JointBelow`, and a monomial which is
not listed takes one line of `JDeg`.

Every inverse printed by the TeX is reproduced exactly: each degree below is the one of its
`JDeg` statement, read by `norm_num` from the base degrees.  Notation: `P, y, a, b, W, J_S` are `cp`
of `PF, yF, AS, BS, WS, JS`, `M = C_S Ex(c_S, R) R`, `Λ = 1/λ_*`, `L = 1 + log R`, `φ = R − X`,
`P_S = slowPrice … Λ`, `D = R²` (the timed cutoff), `H₀ = φ + y √J_F` (the `L²H¹` size of `h₀`).
-/

noncomputable section

namespace OVNS.Quant

namespace JDeg

variable {a b : ℝ} {m : ℝ → ℝ → Caps → ℝ}

/-- `mono`, with the side conditions discharged by `norm_num`. -/
theorem up (h : JDeg a b m) (a' b' : ℝ) (hb : b ≤ b' := by norm_num)
    (hab : (a - a') / 8 + b ≤ b' := by norm_num) : JDeg a' b' m := h.mono hb hab

/-- `below`, with the side conditions discharged by `norm_num`. -/
theorem toQ (h : JDeg a b m) (hb : b ≤ 3 := by norm_num)
    (hab : (a - 1) / 8 + b ≤ 3 := by norm_num) : JointBelow m := h.below hb hab

/-- Powers of `R`. -/
theorem Rpow (x : ℝ) : JDeg 0 x fun _ R _ ↦ R ^ x := fun _ _ _ _ ↦
  ⟨1, 0, 0, zero_le_one, fun X R hdom _ _ ↦
    ⟨Real.rpow_nonneg hdom.R_pos.le _, by simp [Ex_zero]⟩⟩

/-- `X` is below `R`. -/
theorem X : JDeg 0 1 fun X _ _ ↦ X := fun _ _ _ _ ↦
  ⟨1, 0, 0, zero_le_one, fun X R hdom _ _ ↦
    ⟨by linarith [hdom.one_lt_X], by simpa [Ex_zero] using hdom.X_le_R⟩⟩

/-- `m^e`, with the side condition by `norm_num`. -/
theorem root (h : JDeg a b m) (e : ℝ) (he : 0 ≤ e := by norm_num) :
    JDeg (a * e) (b * e) fun X R caps ↦ m X R caps ^ e := h.rpow he

/-- `Q^{−1/3}`: the price of `P(q)` through the floor of `jointLP`. -/
theorem invQ : JDeg (-(1 / 3)) (-1) fun X R _ ↦ (jointQ X R ^ ((1 : ℝ) / 3))⁻¹ := by
  intro _ _ _ _
  refine ⟨1, 0, 0, zero_le_one, fun X R hdom _ _ ↦ ?_⟩
  have hU0 : 0 < jointU X := by linarith [hdom.one_lt_U]
  have hR0 := hdom.R_pos
  have e : (jointQ X R ^ ((1 : ℝ) / 3))⁻¹ = jointU X ^ (-(1 / 3) : ℝ) * R ^ (-1 : ℝ) := by
    rw [hdom.Q_rpow_third, Real.rpow_neg hU0.le, Real.rpow_neg_one, mul_inv]
  beta_reduce
  rw [e]
  refine ⟨mul_nonneg (Real.rpow_nonneg hU0.le _) (Real.rpow_nonneg hR0.le _), ?_⟩
  simp [Ex_zero]

/-- The total `H²` cap `Y`. -/
theorem totalY : JDeg 0 2 fun X _ caps ↦ OVNS.Quant.totalY X caps := by
  have h1 : JDeg 0 2 fun X _ caps ↦ 1 + X + cp caps.yF + cp caps.BS :=
    ((((const zero_le_one).up 0 2).add (X.up 0 2)).add (yF.up 0 2)).add BS
  exact h1.const_mul (by norm_num)

end JDeg

section Rows

variable (CS cS X R : ℝ) (caps : Caps)

/-- The clip length `Λ = 1/λ_*`. -/
local notation "Λ" => 1 / jointLam X R caps
/-- The logarithm. -/
local notation "L" => 1 + Real.log R
/-- The physical maximum. -/
local notation "M" => CS * Ex cS R * R
/-- The fast `H¹` cap. -/
local notation "P" => cp caps.PF
/-- The fast `H²` cap. -/
local notation "Y" => cp caps.yF
/-- The slow `H¹` cap. -/
local notation "A" => cp caps.AS
/-- The slow `H²` cap. -/
local notation "B" => cp caps.BS
/-- The slow Wiener cap. -/
local notation "W" => cp caps.WS
/-- The slow clip price. -/
local notation "PS" => slowPrice CS (Ex cS R) R (1 / jointLam X R caps)
/-- The `L²H¹` size of `h₀`. -/
local notation "H₀" => R - X + cp caps.yF * Real.sqrt (cp caps.JF)
/-- `‖S‖_{5/4} ≤ a^{3/4} b^{1/4}`. -/
local notation "A₊" => cp caps.AS ^ ((3 : ℝ) / 4) * cp caps.BS ^ ((1 : ℝ) / 4)
/-- The force size `h_L = φ √J_S` (LOCAL363). -/
local notation "hL" => (R - X) * Real.sqrt (cp caps.JS)
/-- The force size `h_Q = φ²` (LOCAL363). -/
local notation "hQ" => (R - X) ^ 2
/-- `C_y/D + 1`, with `C_y² ≍ P_S(1)`: the high tail of the force pair. -/
local notation "Ty" => Real.sqrt (CS * Ex cS R * (R ^ 4 + R ^ 5)) * R ^ (-2 : ℝ) + 1

/-- **Row 1 of Table quant-metric**, tied: `Λ M (W² + L a² + a W + L M b)`, with the true forms of
Body 42 (`M[W² + (1 + ln D) a²]`, `(1 + ln q) M² b`, `M a W`). -/
def rowComparable : ℝ := Λ * M * (W ^ 2 + L * A ^ 2 + A * W + L * M * B)

/-- **Row 4**: `q⁻² (D M b² + D (W a b + W² b) + W² b²) Λ`, inverse `U^{1/2} R³`. -/
def rowHeat : ℝ :=
  Real.sqrt (Λ * (R ^ 2 * M * B ^ 2 + R ^ 2 * (W * A * B + W ^ 2 * B) + W ^ 2 * B ^ 2))

/-- **Row 5**: `q⁻² √L (W² + W a₊ + a W + a a₊) H₀ √Λ`, inverse `U^{1/4} R^{29/16}`. -/
def rowSource : ℝ :=
  Real.sqrt (Real.sqrt L * (W ^ 2 + W * A₊ + A * W + A * A₊) * H₀ * Real.sqrt Λ)

/-- **Row 6**: `q⁻⁴ (M b²)² Λ`, inverse `U^{1/4} R^{9/4}`. -/
def rowYoung : ℝ := (M ^ 2 * B ^ 4 * Λ) ^ ((1 : ℝ) / 4)

/-- **Rows 7–10**, in this order, the separated high-last primitive: the inverses
`U^{1/2} R^{5/2}`, `U^{1/2} R^{5/2}`, `U^{1/3} R^{17/6}`, `U^{1/2} R^{7/4}`. -/
def rowSeparated : ℝ :=
  Real.sqrt (W * B * Real.sqrt (PS * Λ)) + Real.sqrt ((B ^ 2 * W + B ^ 3) * Λ) +
    ((R ^ 2) ^ 2 * W * B ^ 2 * Λ) ^ ((1 : ℝ) / 3) + (W ^ 2 * B ^ 2 * Y ^ 2 * Λ) ^ ((1 : ℝ) / 4)

/-- **The quartic `Q₄`** (Body 47): static `(U b)^{3/4}`, pointwise `R^{11/4}`, added mass
`(U b² Λ)^{3/4}`, and the three short terms in the order of Body 47, and `U √P_S`. -/
def rowQuartic : ℝ :=
  (P * B * L) ^ ((3 : ℝ) / 4) + R ^ ((11 : ℝ) / 4) + (P * B ^ 2 * Λ) ^ ((3 : ℝ) / 4) +
    (PS * P ^ 2) ^ ((3 : ℝ) / 8) +
    (PS * P ^ 4 * R ^ 4 * (jointU X ^ (-1 : ℝ) * R ^ (-1 : ℝ))) ^ ((3 : ℝ) / 8) +
    (PS * P ^ 2 * R ^ 2) ^ ((3 : ℝ) / 8) + P * Real.sqrt PS

/-- **The quartics through `jointLP`**: the coefficients of `q⁻¹ P(q)` in `Q₄`, `Q₄,₁`, in the
order static, pointwise, added mass, the three short roots, and the `H¹` debit `U b²`, with `P(q)`
paid by the floor `Q^{1/3}` of `LP`.  This is the Lean route: no `q^{−4/3}` and no moving exponent
(`rpow_eps_le`).  The last term has degree `(2/3, 3)`: the debit `U^{−1/3}` of the TeX. -/
def rowQuarticNear : ℝ :=
  (P * B * L + R ^ 3 * Y + P * B ^ 2 * Λ + Real.sqrt (PS * P ^ 2) +
    Real.sqrt (PS * P ^ 4 * R ^ 4 * (jointU X ^ (-1 : ℝ) * R ^ (-1 : ℝ))) +
    Real.sqrt (PS * P ^ 2 * R ^ 2) + P * B ^ 2) * (jointQ X R ^ ((1 : ℝ) / 3))⁻¹

/-- **The static metric** at its own `D = R` (Lemma quant-static), with the full metric–`Q`
insertion, tied: `P (L a² + a W + b²/R) + P M b`, the heat term `(P R a b)^{1/2}`, and `q ≥ B_S`. -/
def rowStatic : ℝ :=
  P * (L * A ^ 2 + A * W + B ^ 2 * R ^ (-1 : ℝ)) + P * M * B + Real.sqrt (P * R * A * B) + B

/-- **The native and ordinary FAR**: `√P y^{3/2} + M y + P b`, `y^{14/5} + P^{3/2}`, and the
purefast `P y³`, proper `y³` of roles 13–17, which Lean pays through `LN`, `LP`. -/
def rowFar : ℝ :=
  Real.sqrt P * Y ^ ((3 : ℝ) / 2) + M * Y + P * B + Y ^ ((14 : ℝ) / 5) + P ^ ((3 : ℝ) / 2) +
    P * Y ^ 3 + Y ^ 3

/-- **The first three force roots** of rows 29, 30, 32: `U R^{5/2}, R³, R³` and
`U^{1/2} R, R^{8/5}, R^{5/3}`, as printed. -/
def rowForceRoots : ℝ :=
  P * R ^ ((5 : ℝ) / 2) + R ^ (3 : ℝ) + Real.sqrt P * R + R ^ ((8 : ℝ) / 5) + R ^ ((5 : ℝ) / 3)

/-- **The `Z` force pair** (Body 40): the powers `11/4`, `5/3`. -/
def rowForceZ : ℝ :=
  Real.sqrt (M * B * L * hL) + (M * B * L * hQ) ^ ((1 : ℝ) / 3)

/-- **The low `X₂` force pair** (Body 41): the powers `11/4`, `5/3`, `17/6`, `2`. -/
def rowForceLow : ℝ :=
  Real.sqrt ((W ^ 2 + L * A ^ 2) * hL) + ((W ^ 2 + L * A ^ 2) * hQ) ^ ((1 : ℝ) / 3) +
    (R ^ 2 * B ^ 2 * hL) ^ ((1 : ℝ) / 3) + (R ^ 2 * B ^ 2 * hQ) ^ ((1 : ℝ) / 4)

/-- **The high `X₂` force pair** (Body 41), at the total cap `Y`: the powers `11/4`, `3/2`. -/
def rowForceHigh : ℝ :=
  Real.sqrt (B * Ty * (R - X) * totalY X caps) + (B * Ty * hQ) ^ ((1 : ℝ) / 3)

/-- **The envelope of the `H²` roles**, but the rows 2, 3 (`highAnc`). -/
def q₂Env : ℝ :=
  rowComparable CS cS X R caps + rowHeat CS cS X R caps + rowSource X R caps +
    rowYoung CS cS X R caps + rowSeparated CS cS X R caps + rowQuartic CS cS X R caps +
    rowStatic CS cS R caps + rowFar CS cS R caps + rowForceRoots R caps +
    rowForceZ CS cS X R caps + rowForceLow X R caps + rowForceHigh CS cS X R caps

/-- **The timed `H¹` mass** (Bodies 37, 38): `M ∫ G²`, with `∫ G² ≲ C_S ex R²` on units (the slot
`kin` of `SlowOut`), and the root `R³` of `q⁻² R⁶`. -/
def rowTimed : ℝ := L * M * (CS * Ex cS R * R ^ 2) + R ^ 3

/-- **The quartic `Q₄,₁`** (Bodies 35, 47) and `Q₃,₁`: the static `q^{−5/6} U √(a b) L`, the
derivative `q^{−1} P(q) U b²` paid with `P b²` at exponent `3/4`, and the static `q⁻² W³`. -/
def rowQuartic₁ : ℝ :=
  (P * L * Real.sqrt (A * B)) ^ ((6 : ℝ) / 5) + (P * B ^ 2) ^ ((3 : ℝ) / 4) +
    W ^ ((3 : ℝ) / 2)

/-- **The genuine `H¹` and tested roles**: role 9 `√P y^{3/2} + W y + b √(P y) + 1`, the tested
`P² h_L`, `P φ`, the genuine `P (1 + R²) H₀`, and the literal role 18 `Y φ`. -/
def rowGenuine : ℝ :=
  Real.sqrt P * Y ^ ((3 : ℝ) / 2) + W * Y + B * Real.sqrt (P * Y) + 1 + P ^ 2 * hL + P * (R - X) +
    P * (1 + R ^ 2) * H₀ + totalY X caps * (R - X)

/-- **The envelope of the `H¹` roles.** -/
def q₁Env : ℝ :=
  rowTimed CS cS R + rowQuartic₁ R caps + rowStatic CS cS R caps + rowFar CS cS R caps +
    rowGenuine X R caps + rowForceRoots R caps + rowForceZ CS cS X R caps +
    rowForceLow X R caps + rowForceHigh CS cS X R caps

/-- **The floors and the printed slow rows** of the table of the joint proof, for the record: J2
and J4 do not read them, since `jointBudget` is below (J4 §3).  `R^{5/2}`, `U T`, `U T/R`; rows 7,
19: `(y/R)(y + R² P + P^{3/2} y^{1/2} + √J_S + 1)`; row 20: `(y/R)(R² y + √P y^{3/2} + R² + y + 1)`;
row 21: `R y²`, `y²/√R`; rows 33, 34: `R² y² + R³ + y²`; row 35: `φ √J_S + φ`. -/
def rowSlowPrinted : ℝ :=
  R ^ ((5 : ℝ) / 2) + P * Y + P * Y * R ^ (-1 : ℝ) +
    Y * R ^ (-1 : ℝ) *
      (Y + R ^ 2 * P + P ^ ((3 : ℝ) / 2) * Real.sqrt Y + Real.sqrt (cp caps.JS) + 1) +
    Y * R ^ (-1 : ℝ) * (R ^ 2 * Y + Real.sqrt P * Y ^ ((3 : ℝ) / 2) + R ^ 2 + Y + 1) +
    R * Y ^ 2 + Y ^ 2 * R ^ (-(1 : ℝ) / 2) + R ^ 2 * Y ^ 2 + R ^ 3 + Y ^ 2 + hL + (R - X)

end Rows

section Degrees

open JDeg

variable {CS cS : ℝ}

private theorem hAplus :
    JDeg 0 (13 / 8) fun _ _ caps ↦ cp caps.AS ^ ((3 : ℝ) / 4) * cp caps.BS ^ ((1 : ℝ) / 4) :=
  ((AS.root (3 / 4)).mul (BS.root (1 / 4))).up 0 (13 / 8)

private theorem hH₀ : JDeg 0 1 fun X R caps ↦ R - X + cp caps.yF * Real.sqrt (cp caps.JF) :=
  phi.add ((yF.mul JF.sqrt).up 0 1)

private theorem hhL : JDeg 0 (5 / 2) fun X R caps ↦ (R - X) * Real.sqrt (cp caps.JS) :=
  (phi.mul JS.sqrt).up 0 (5 / 2)

private theorem hhQ : JDeg 0 2 fun X R _ ↦ (R - X) ^ 2 := (phi.pow 2).up 0 2

private theorem hUm : JDeg (-1) (-1) fun X R _ ↦ jointU X ^ (-1 : ℝ) * R ^ (-1 : ℝ) := by
  have hU : JDeg (-1) 0 fun X _ _ ↦ jointU X ^ (-1 : ℝ) := by
    intro _ _ _ _
    refine ⟨1, 0, 0, zero_le_one, fun X R hdom _ _ ↦ ⟨?_, by simp [Ex_zero]⟩⟩
    exact Real.rpow_nonneg (by linarith [hdom.one_lt_U]) _
  simpa using hU.mul (Rpow (-1))

private theorem hG : JDeg 0 3 fun _ R caps ↦
    cp caps.WS ^ 2 + (1 + Real.log R) * cp caps.AS ^ 2 :=
  ((WS.pow 2).up 0 3).add ((logR.mul (AS.pow 2)).up 0 3)

/-- Row 1: exactly `(1, 3)`, tied for every `U`. -/
theorem deg_rowComparable (hCS : 0 ≤ CS) :
    JDeg 1 3 fun X R caps ↦ rowComparable CS cS X R caps := by
  have hM := Minf (e := cS) hCS
  have h := (invLam.mul hM).mul ((hG.add ((AS.mul WS).up 0 3)).add
    (((logR.mul hM).mul BS).up 0 3))
  exact h.up 1 3

/-- Row 4: exactly `(1/2, 3)`. -/
theorem deg_rowHeat (hCS : 0 ≤ CS) : JDeg (1 / 2) 3 fun X R caps ↦ rowHeat CS cS X R caps := by
  have hM := Minf (e := cS) hCS
  have hR2 := R.pow 2
  have h1 := (((hR2.mul hM).mul (BS.pow 2)).up 0 7).add
    (((hR2.mul ((((WS.mul AS).mul BS).up 0 5).add (((WS.pow 2).mul BS).up 0 5))).up 0 7))
  have h2 := h1.add (((WS.pow 2).mul (BS.pow 2)).up 0 7)
  exact (invLam.mul h2).sqrt.up (1 / 2) 3

/-- Row 5: exactly `(1/4, 29/16)`. -/
theorem deg_rowSource : JDeg (1 / 4) (29 / 16) fun X R caps ↦ rowSource X R caps := by
  have h1 := (((WS.pow 2).up 0 (25 / 8)).add ((WS.mul hAplus).up 0 (25 / 8))).add
    ((AS.mul WS).up 0 (25 / 8))
  have h2 := h1.add ((AS.mul hAplus).up 0 (25 / 8))
  exact (((logR.sqrt.mul h2).mul hH₀).mul invLam.sqrt).sqrt.up (1 / 4) (29 / 16)

/-- Row 6: exactly `(1/4, 9/4)`. -/
theorem deg_rowYoung (hCS : 0 ≤ CS) : JDeg (1 / 4) (9 / 4) fun X R caps ↦ rowYoung CS cS X R caps :=
  ((((Minf (e := cS) hCS).pow 2).mul (BS.pow 4)).mul invLam).root (1 / 4) |>.up (1 / 4) (9 / 4)

/-- Rows 7–10: `(1/2, 5/2)`, `(1/2, 5/2)`, `(1/3, 17/6)`, `(1/2, 7/4)`. -/
theorem deg_rowSeparated (hCS : 0 ≤ CS) :
    JDeg 1 3 fun X R caps ↦ rowSeparated CS cS X R caps := by
  have hP := price (e := cS) hCS
  have h7 := ((WS.mul BS).mul (hP.mul invLam).sqrt).sqrt.up (1 / 2) (5 / 2)
  have h8 := ((((BS.pow 2).mul WS).up 0 6).add (BS.pow 3 |>.up 0 6)).mul invLam |>.sqrt
  have h8' := h8.up (1 / 2) (5 / 2)
  have h9 := ((((R.pow 2).pow 2).mul WS).mul (BS.pow 2)).mul invLam |>.root (1 / 3)
  have h9' := h9.up (1 / 3) (17 / 6)
  have h10 := (((WS.pow 2).mul (BS.pow 2)).mul (yF.pow 2)).mul invLam |>.root (1 / 4)
  have h10' := h10.up (1 / 2) (7 / 4)
  exact (((h7.up 1 3).add (h8'.up 1 3)).add (h9'.up 1 3)).add (h10'.up 1 3)

/-- `Q₄`: `(3/4, 3/2)`, `(0, 11/4)`, `(3/2, 9/4)`, `(9/8, 3/2)`, `(3/2, 21/8)`, `(9/8, 9/4)`,
`(3/2, 2)`. -/
theorem deg_rowQuartic (hCS : 0 ≤ CS) :
    JDeg 1 3 fun X R caps ↦ rowQuartic CS cS X R caps := by
  have hP := price (e := cS) hCS
  have h1 := ((PF.mul BS).mul logR).root (3 / 4) |>.up (3 / 4) (3 / 2)
  have h2 := (Rpow (11 / 4)).up 0 (11 / 4)
  have h3 := ((PF.mul (BS.pow 2)).mul invLam).root (3 / 4) |>.up (3 / 2) (9 / 4)
  have h4 := (hP.mul (PF.pow 2)).root (3 / 8) |>.up (9 / 8) (3 / 2)
  have h5 := ((hP.mul (PF.pow 4)).mul (R.pow 4)).mul hUm |>.root (3 / 8) |>.up (3 / 2) (21 / 8)
  have h6 := ((hP.mul (PF.pow 2)).mul (R.pow 2)).root (3 / 8) |>.up (9 / 8) (9 / 4)
  have h7 := PF.mul hP.sqrt |>.up (3 / 2) 2
  exact ((((((h1.up 1 3).add (h2.up 1 3)).add (h3.up 1 3)).add (h4.up 1 3)).add
    (h5.up 1 3)).add (h6.up 1 3)).add (h7.up 1 3)

/-- The coefficients of `q⁻¹ P(q)`, over `Q^{1/3}`: all below `Q`, the `H¹` one by `U^{−1/3}`. -/
theorem deg_rowQuarticNear (hCS : 0 ≤ CS) :
    JDeg 1 3 fun X R caps ↦ rowQuarticNear CS cS X R caps := by
  have hP := price (e := cS) hCS
  have h1 := (PF.mul BS).mul logR |>.up 1 2
  have h2 := (R.pow 3).mul yF |>.up (1 / 2) (7 / 2)
  have h3 := (PF.mul (BS.pow 2)).mul invLam |>.up 2 3
  have h4 := (hP.mul (PF.pow 2)).sqrt.up (3 / 2) 2
  have h5 := (((hP.mul (PF.pow 4)).mul (R.pow 4)).mul hUm).sqrt.up 2 (7 / 2)
  have h6 := ((hP.mul (PF.pow 2)).mul (R.pow 2)).sqrt.up (3 / 2) 3
  have h7 := PF.mul (BS.pow 2) |>.up 1 4
  have h := h1.up (4 / 3) 4 |>.add (h2.up (4 / 3) 4) |>.add (h3.up (4 / 3) 4) |>.add
    (h4.up (4 / 3) 4) |>.add (h5.up (4 / 3) 4) |>.add (h6.up (4 / 3) 4) |>.add (h7.up (4 / 3) 4)
  exact (h.mul invQ).up 1 3

/-- The static metric: `(1, 3)`, tied; the heat term `(1/2, 9/4)`; `q ≥ B_S`. -/
theorem deg_rowStatic (hCS : 0 ≤ CS) :
    JDeg 1 3 fun _ R caps ↦ rowStatic CS cS R caps := by
  have hM := Minf (e := cS) hCS
  have h1 := PF.mul (((((logR.mul (AS.pow 2)).up 0 3).add ((AS.mul WS).up 0 3))).add
    (((BS.pow 2).mul (Rpow (-1))).up 0 3))
  have h2 := (PF.mul hM).mul BS
  have h3 := (((PF.mul R).mul AS).mul BS).sqrt.up (1 / 2) (9 / 4)
  exact (((h1.up 1 3).add (h2.up 1 3)).add (h3.up 1 3)).add (BS.up 1 3)

/-- The FAR: `(5/4, 3/4)`, `(1/2, 3/2)`, `(1, 2)`, `(7/5, 7/5)`, `(3/2, 0)`; purefast `(5/2, 3/2)`,
proper `(3/2, 3/2)`. -/
theorem deg_rowFar (hCS : 0 ≤ CS) : JDeg 1 3 fun _ R caps ↦ rowFar CS cS R caps := by
  have hM := Minf (e := cS) hCS
  have h1 := PF.sqrt.mul (yF.root (3 / 2)) |>.up (5 / 4) (3 / 4)
  have h2 := hM.mul yF |>.up (1 / 2) (3 / 2)
  have h3 := PF.mul BS |>.up 1 2
  have h4 := yF.root (14 / 5) |>.up (7 / 5) (7 / 5)
  have h5 := PF.root (3 / 2) |>.up (3 / 2) 0
  have h6 := PF.mul (yF.pow 3) |>.up (5 / 2) (3 / 2)
  have h7 := yF.pow 3 |>.up (3 / 2) (3 / 2)
  exact h1.up 1 3 |>.add (h2.up 1 3) |>.add (h3.up 1 3) |>.add (h4.up 1 3) |>.add (h5.up 1 3)
    |>.add (h6.up 1 3) |>.add (h7.up 1 3)

/-- The first three force roots, as printed. -/
theorem deg_rowForceRoots : JDeg 1 3 fun _ R caps ↦ rowForceRoots R caps := by
  have h1 := PF.mul (Rpow (5 / 2)) |>.up 1 (5 / 2)
  have h2 := PF.sqrt.mul R |>.up (1 / 2) 1
  exact (((((h1.up 1 3).add ((Rpow 3).up 1 3)).add (h2.up 1 3)).add ((Rpow (8 / 5)).up 1 3))).add
    ((Rpow (5 / 3)).up 1 3)

/-- The `Z` pair: exactly the powers `11/4`, `5/3`. -/
theorem deg_rowForceZ (hCS : 0 ≤ CS) : JDeg 1 3 fun X R caps ↦ rowForceZ CS cS X R caps := by
  have hM := Minf (e := cS) hCS
  have h1 := (((hM.mul BS).mul logR).mul hhL).sqrt.up 0 (11 / 4)
  have h2 := ((hM.mul BS).mul logR).mul hhQ |>.root (1 / 3) |>.up 0 (5 / 3)
  exact (h1.up 1 3).add (h2.up 1 3)

/-- The low `X₂` pair: exactly the powers `11/4`, `5/3`, `17/6`, `2`. -/
theorem deg_rowForceLow : JDeg 1 3 fun X R caps ↦ rowForceLow X R caps := by
  have h1 := (hG.mul hhL).sqrt.up 0 (11 / 4)
  have h2 := hG.mul hhQ |>.root (1 / 3) |>.up 0 (5 / 3)
  have h3 := ((R.pow 2).mul (BS.pow 2)).mul hhL |>.root (1 / 3) |>.up 0 (17 / 6)
  have h4 := ((R.pow 2).mul (BS.pow 2)).mul hhQ |>.root (1 / 4) |>.up 0 2
  exact (((h1.up 1 3).add (h2.up 1 3)).add (h3.up 1 3)).add (h4.up 1 3)

/-- The high `X₂` pair: exactly the powers `11/4`, `3/2`. -/
theorem deg_rowForceHigh (hCS : 0 ≤ CS) :
    JDeg 1 3 fun X R caps ↦ rowForceHigh CS cS X R caps := by
  have hC : JDeg 0 5 fun _ R _ ↦ CS * Ex cS R * (R ^ 4 + R ^ 5) := by
    have h0 := ((ex cS).const_mul hCS).mul (((R.pow 4).up 0 5).add ((R.pow 5).up 0 5))
    exact h0.up 0 5
  have hTy : JDeg 0 (1 / 2) fun _ R _ ↦
      Real.sqrt (CS * Ex cS R * (R ^ 4 + R ^ 5)) * R ^ (-2 : ℝ) + 1 :=
    ((hC.sqrt.mul (Rpow (-2))).up 0 (1 / 2)).add ((const zero_le_one).up 0 (1 / 2))
  have h1 := (((BS.mul hTy).mul phi).mul JDeg.totalY).sqrt.up 0 (11 / 4)
  have h2 := (BS.mul hTy).mul hhQ |>.root (1 / 3) |>.up 0 (3 / 2)
  exact (h1.up 1 3).add (h2.up 1 3)

/-- The timed mass: `(0, 3)`, tied at `U ≍ 1`. -/
theorem deg_rowTimed (hCS : 0 ≤ CS) : JDeg 1 3 fun _ R _ ↦ rowTimed CS cS R := by
  have hM := Minf (e := cS) hCS
  have h1 := (logR.mul hM).mul (((ex cS).const_mul hCS).mul (R.pow 2))
  exact (h1.up 1 3).add ((R.pow 3).up 1 3)

/-- `Q₄,₁`, `Q₃,₁`: `(6/5, 21/10)`, `(3/4, 3)`, `(0, 9/4)`. -/
theorem deg_rowQuartic₁ : JDeg 1 3 fun _ R caps ↦ rowQuartic₁ R caps := by
  have h1 := ((PF.mul logR).mul (AS.mul BS).sqrt).root (6 / 5) |>.up (6 / 5) (21 / 10)
  have h2 := (PF.mul (BS.pow 2)).root (3 / 4) |>.up (3 / 4) 3
  have h3 := WS.root (3 / 2) |>.up 0 (9 / 4)
  exact ((h1.up 1 3).add (h2.up 1 3)).add (h3.up 1 3)

/-- The genuine and tested roles: `(5/4, 3/4)`, `(1/2, 2)`, `(3/4, 9/4)`, `(2, 5/2)`, `(1, 1)`,
`(1, 3)`, `(0, 3)`. -/
theorem deg_rowGenuine : JDeg 1 3 fun X R caps ↦ rowGenuine X R caps := by
  have h1 := PF.sqrt.mul (yF.root (3 / 2)) |>.up (5 / 4) (3 / 4)
  have h2 := WS.mul yF |>.up (1 / 2) 2
  have h3 := BS.mul (PF.mul yF).sqrt |>.up (3 / 4) (9 / 4)
  have h4 := (PF.pow 2).mul hhL |>.up 2 (5 / 2)
  have h5 := PF.mul phi |>.up 1 1
  have h6 := (PF.mul (((const zero_le_one).up 0 2).add ((R.pow 2).up 0 2))).mul hH₀ |>.up 1 3
  have h7 := JDeg.totalY.mul phi |>.up 0 3
  exact (((((((h1.up 1 3).add (h2.up 1 3)).add (h3.up 1 3)).add
    ((const zero_le_one).up 1 3)).add (h4.up 1 3)).add (h5.up 1 3)).add h6).add (h7.up 1 3)

/-- The printed slow rows and floors: the tied `R² y²` and `R³`. -/
theorem deg_rowSlowPrinted : JDeg 1 3 fun X R caps ↦ rowSlowPrinted X R caps := by
  have hRm := Rpow (-1)
  have hy := yF.mul hRm
  have h1 := PF.mul yF |>.up (3 / 2) (1 / 2)
  have h2 := (PF.mul yF).mul hRm |>.up (3 / 2) (-(1 / 2))
  have h3 := yF.up 1 2 |>.add ((((R.pow 2).mul PF)).up 1 2) |>.add
    (((PF.root (3 / 2)).mul yF.sqrt).up 1 2) |>.add (JS.sqrt.up 1 2) |>.add
    ((const zero_le_one).up 1 2)
  have h4 := ((R.pow 2).mul yF).up (1 / 2) (5 / 2) |>.add
    ((PF.sqrt.mul (yF.root (3 / 2))).up (1 / 2) (5 / 2)) |>.add
    ((R.pow 2).up (1 / 2) (5 / 2)) |>.add (yF.up (1 / 2) (5 / 2)) |>.add
    ((const zero_le_one).up (1 / 2) (5 / 2))
  have h5 := (hy.mul h3).up 1 3
  have h6 := (hy.mul h4).up 1 3
  have h7 := R.mul (yF.pow 2) |>.up 1 2
  have h8 := (yF.pow 2).mul (Rpow (-(1 : ℝ) / 2)) |>.up 1 (1 / 2)
  have h9 := (R.pow 2).mul (yF.pow 2) |>.up 1 3
  exact ((Rpow (5 / 2)).up 1 3) |>.add (h1.up 1 3) |>.add (h2.up 1 3) |>.add h5 |>.add h6 |>.add
    (h7.up 1 3) |>.add (h8.up 1 3) |>.add h9 |>.add ((R.pow 3).up 1 3) |>.add
    ((yF.pow 2).up 1 3) |>.add (hhL.up 1 3) |>.add (phi.up 1 3)

/-- **The `H²` envelope is `JointBelow`**: every row printed by the TeX, at the Lean caps. -/
theorem q₂Env_below (hCS : 0 ≤ CS) : JointBelow (q₂Env CS cS) := by
  have d1 := deg_rowComparable (cS := cS) hCS
  have d2 := (deg_rowHeat (cS := cS) hCS).up 1 3
  have d3 := (deg_rowYoung (cS := cS) hCS).up 1 3
  have d4 := deg_rowSeparated (cS := cS) hCS
  have d5 := deg_rowQuartic (cS := cS) hCS
  have d6 := deg_rowStatic (cS := cS) hCS
  have d7 := deg_rowFar (cS := cS) hCS
  have d8 := deg_rowForceZ (cS := cS) hCS
  have d9 := deg_rowForceHigh (cS := cS) hCS
  have h := d1.add d2 |>.add (deg_rowSource.up 1 3) |>.add d3 |>.add d4 |>.add d5 |>.add d6 |>.add
    d7 |>.add deg_rowForceRoots |>.add d8 |>.add deg_rowForceLow |>.add d9
  exact h.toQ

/-- **The `H¹` envelope is `JointBelow`.** -/
theorem q₁Env_below (hCS : 0 ≤ CS) : JointBelow (q₁Env CS cS) := by
  have d1 := deg_rowTimed (cS := cS) hCS
  have d6 := deg_rowStatic (cS := cS) hCS
  have d7 := deg_rowFar (cS := cS) hCS
  have d8 := deg_rowForceZ (cS := cS) hCS
  have d9 := deg_rowForceHigh (cS := cS) hCS
  have h := d1.add deg_rowQuartic₁ |>.add d6 |>.add d7 |>.add deg_rowGenuine |>.add
    deg_rowForceRoots |>.add d8 |>.add deg_rowForceLow |>.add d9
  exact h.toQ

/-- The quartic coefficients through `jointLP` are `JointBelow`. -/
theorem rowQuarticNear_below (hCS : 0 ≤ CS) :
    JointBelow fun X R caps ↦ rowQuarticNear CS cS X R caps :=
  (deg_rowQuarticNear hCS).toQ

/-- The printed slow rows are `JointBelow`, as J4 has them with a gap. -/
theorem rowSlowPrinted_below : JointBelow fun X R caps ↦ rowSlowPrinted X R caps :=
  deg_rowSlowPrinted.toQ

end Degrees

end OVNS.Quant

end
