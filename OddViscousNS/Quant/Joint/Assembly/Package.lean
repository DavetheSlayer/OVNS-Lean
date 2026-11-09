import OddViscousNS.Quant.Joint.Assembly.Near
import OddViscousNS.Quant.Joint.Regimes
import OddViscousNS.Quant.Joint.Sources.Below
import OddViscousNS.Quant.Joint.Kinetic.Main
import OddViscousNS.Quant.Energy.NearJ.Main

/-!
# J6: the concrete package and the joint theorem from the energies

`EnergyData` is the list of what is still free in `JointData`: the parameters of E5-J and E8-J.
`EnergyData.data` is the concrete package: every other field is fixed here, from the proved layers
(J1, J2, J3, J4).

| field | value | owner |
|---|---|---|
| `R₀` | `Slow.R₁ E.R₀` | J2, enlarged by the energies |
| `Tp` | `4` | J2 |
| `q₀` | `kinJ0 C_S c_S` | J3 |
| `qS` | `jointBudget (R − X)` | J4 |
| `L`, `CS`, `cS`, `Sl` | `slowL`, `slowC`, `36`, `True` | J2 |
| `N`, `P` | `nearN`, `nearP` | J1 |
| `LN`, `LP` | `jointLN`, `jointLP` (`Assembly/Near.lean`) | J6 |
| `Nbar`, `piTol` | `C_N X`, `C_π X` | J6: the only use is `fast_budget` |
| `q₁`, `q₂`, `Cs`, `CG`, `m₀`, `Cm` | open | J5 |

**The target of J5** is `JointH1Input E`, `JointH2Input E`, `JointBelow E.q₁`, `JointBelow E.q₂`,
for one `E` with `E.Ranges`, chosen after the resonant constants:
`quantitative_joint_of_energies` is then the conclusion of `quantitative_joint_force`, verbatim.

**Monotonicity.**  `H1Output` is monotone in `N̄, π` on nonnegative values, so fixing
`N̄ = C_N X`, `π = C_π X` loses nothing against the fields `Nbar_le`, `piTol_le`
(`H1Output.mono`).  The fields `Nbar_nonneg`, `piTol_nonneg`, `Nbar_le`, `piTol_le` are therefore
theorems here, and are not part of the target.
-/

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace OVNS.Quant

/-! ### Monotonicity in the tolerances -/

/-- `H1Output` is monotone in `N̄`, `π`, on nonnegative values. -/
theorem H1Output.mono {σ Cs N N' p p' r : ℝ} {g : Field} {y : ℝ → Field} {s t : ℝ} (hN0 : 0 ≤ N)
    (hN : N ≤ N') (hp0 : 0 ≤ p) (hp : p ≤ p') (h : H1Output σ Cs N p r g y s t) :
    H1Output σ Cs N' p' r g y s t := by
  obtain ⟨E, Nf, ff, m, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨E, Nf, ff, m, h1, h2, h3, h4, h5, h6, h7.trans (pow_le_pow_left₀ hN0 hN 2),
    h8.trans (pow_le_pow_left₀ hp0 hp 2), h9⟩

/-- `H1EnergyJoint` is monotone in `N̄`, `π`, on nonnegative values: an energy proved at some
`N̄ ≤ C_N X`, `π ≤ C_π X` is the input `JointH1Input` at `C_N`, `C_π`. -/
theorem H1EnergyJoint.mono {σ Cs μ φ Tp N N' p p' Minf : ℝ} {q₁ : Caps → ℝ}
    {near : Caps → ℝ → Prop} {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} (hN0 : 0 ≤ N)
    (hN : N ≤ N') (hp0 : 0 ≤ p) (hp : p ≤ p') (h : H1EnergyJoint σ Cs μ φ Tp N p Minf q₁ near Sl) :
    H1EnergyJoint σ Cs μ φ Tp N' p' Minf q₁ near Sl :=
  fun r g y Ty caps s t hsol hP ↦ (h r g y Ty caps s t hsol hP).mono hN0 hN hp0 hp

/-! ### The package -/

/-- **What is open in the joint package**: the parameters of E5-J and E8-J. -/
structure EnergyData where
  /-- The domain of the energies (it is enlarged by the one of E7-P, see `EnergyData.data`). -/
  R₀ : ℝ
  /-- The `H¹` threshold. -/
  q₁ : ℝ → ℝ → Caps → ℝ
  /-- The `H²` threshold, apart from the rows 2, 3 of Table quant-metric. -/
  q₂ : ℝ → ℝ → Caps → ℝ
  /-- The (enlarged) resonant constant of the `H¹` energy. -/
  Cs : ℝ
  /-- The (enlarged) resonant constant of the `H²` energy. -/
  CG : ℝ
  /-- The clip multiplier mass. -/
  m₀ : ℝ
  /-- The kernel constant of the rows 2, 3 of Table quant-metric. -/
  Cm : ℝ
  /-- `N̄ = C_N X`. -/
  CN : ℝ
  /-- `π = C_π X`. -/
  Cp : ℝ
  /-- The normalization of the native near role. -/
  KN : ℝ
  /-- The normalization of the proper near role. -/
  KP : ℝ

/-- The sign and range conditions on the open constants. -/
structure EnergyData.Ranges (E : EnergyData) : Prop where
  /-- `C_s ≥ 0`. -/
  Cs_nonneg : 0 ≤ E.Cs
  /-- `C_G ≥ 0`. -/
  CG_nonneg : 0 ≤ E.CG
  /-- `0 ≤ m₀ ≤ 1/4`. -/
  m₀_mem : 0 ≤ E.m₀ ∧ E.m₀ ≤ 1 / 4
  /-- `C_m ≥ 0`. -/
  Cm_nonneg : 0 ≤ E.Cm
  /-- `C_N ≥ 0`. -/
  CN_nonneg : 0 ≤ E.CN
  /-- `C_π ≥ 0`. -/
  Cp_nonneg : 0 ≤ E.Cp
  /-- `K_N ≥ 0`. -/
  KN_nonneg : 0 ≤ E.KN
  /-- `K_P ≥ 0`. -/
  KP_nonneg : 0 ≤ E.KP

/-- **The concrete joint package.**  Everything but the fields of `EnergyData` is fixed. -/
def EnergyData.data (E : EnergyData) : JointData where
  R₀ := Slow.R₁ E.R₀
  Tp := fun _ _ ↦ 4
  q₀ := kinJ0 Slow.slowC 36
  q₁ := E.q₁
  q₂ := E.q₂
  qS := fun X R caps ↦ jointBudget (R - X) caps
  Nbar := fun X _ ↦ E.CN * X
  piTol := fun X _ ↦ E.Cp * X
  LN := jointLN E.KN Slow.slowC 36
  LP := jointLP E.KP
  N := nearN
  P := nearP
  Sl := fun _ _ _ _ _ _ _ ↦ True
  Cs := E.Cs
  CG := E.CG
  m₀ := E.m₀
  Cm := E.Cm
  L := Slow.slowL
  CS := Slow.slowC
  cS := 36

/-- **E5-J, the first input**: `H1EnergyJoint` at the package.  Unfolded, `Tp = 4`,
`M_∞ = slowC Ex(36, R) R`, `N̄ = C_N X`, `π = C_π X`, `near = NearPaid (jointLN …) (jointLP …) nearN
nearP`, `Sl = SlowOut slowC (Ex 36 R) R (fun _ _ _ _ _ ↦ True)`. -/
def JointH1Input (E : EnergyData) : Prop :=
  ∀ X R : ℝ, JDom E.data.R₀ X R →
    H1EnergyJoint ((281 : ℝ) / 1000) E.Cs X (R - X) 4 (E.CN * X) (E.Cp * X) (E.data.Minf R)
      (E.q₁ X R) (E.data.near X R) (E.data.slowOut X R)

/-- **E8-J, the second input**: `H2EnergyInterfaceB` at the package, at `B_* = T/P_F`, with the
threshold `q₂Full = max(q₂, C_m highAnc)`. -/
def JointH2Input (E : EnergyData) : Prop :=
  ∀ X R : ℝ, JDom E.data.R₀ X R →
    H2EnergyInterfaceB ((281 : ℝ) / 1000) E.CG X (R - X) 4 E.m₀ (E.data.Minf R) (jointBs X R)
      (E.data.q₂Full X R) (E.data.near X R) (E.data.slowOut X R)

/-- `JointH1Input`, fully unfolded: the statement for J5, with no reference to `JointData`. -/
theorem jointH1Input_iff (E : EnergyData) : JointH1Input E ↔ ∀ X R : ℝ, JDom (Slow.R₁ E.R₀) X R →
    H1EnergyJoint ((281 : ℝ) / 1000) E.Cs X (R - X) 4 (E.CN * X) (E.Cp * X)
      (Slow.slowC * Ex 36 R * R) (E.q₁ X R)
      (NearPaid (jointLN E.KN Slow.slowC 36 X R) (jointLP E.KP X R) nearN nearP)
      (SlowOut Slow.slowC (Ex 36 R) R fun _ _ _ _ _ ↦ True) := Iff.rfl

/-- `JointH2Input`, fully unfolded: the statement for J5, with no reference to `JointData`. -/
theorem jointH2Input_iff (E : EnergyData) : JointH2Input E ↔ ∀ X R : ℝ, JDom (Slow.R₁ E.R₀) X R →
    H2EnergyInterfaceB ((281 : ℝ) / 1000) E.CG X (R - X) 4 E.m₀ (Slow.slowC * Ex 36 R * R)
      (jointBs X R)
      (fun caps ↦ max (E.q₂ X R caps) (E.Cm * highAnc Slow.slowC (Ex 36 R) X R caps))
      (NearPaid (jointLN E.KN Slow.slowC 36 X R) (jointLP E.KP X R) nearN nearP)
      (SlowOut Slow.slowC (Ex 36 R) R fun _ _ _ _ _ ↦ True) := Iff.rfl

/-- **The whole target of J5.** -/
structure EnergyData.Closes (E : EnergyData) : Prop where
  /-- The ranges of the constants. -/
  ranges : E.Ranges
  /-- E5-J. -/
  h1 : JointH1Input E
  /-- E8-J. -/
  h2 : JointH2Input E
  /-- The `H¹` roles. -/
  below₁ : JointBelow E.q₁
  /-- The `H²` roles but the rows 2, 3. -/
  below₂ : JointBelow E.q₂

/-! ### The fields that are proved -/

section Fields

variable (E : EnergyData)

theorem EnergyData.minf_eq (R : ℝ) : E.data.Minf R = Slow.slowC * Ex 36 R * R := rfl

theorem EnergyData.near_iff {X R q : ℝ} {caps : Caps} :
    E.data.near X R caps q ↔ jointLN E.KN Slow.slowC 36 X R caps * nearN q ≤ 1 ∧
      jointLP E.KP X R caps * nearP q ≤ 1 := Iff.rfl

theorem EnergyData.dom_mono {X R : ℝ} (h : JDom E.data.R₀ X R) : JDom E.R₀ X R :=
  h.mono (le_max_left _ _)

theorem EnergyData.L_ge : ∀ i, 1 ≤ E.data.L i := by
  intro i
  fin_cases i <;> norm_num [EnergyData.data, Slow.slowL]

theorem EnergyData.CS_ge : 1 ≤ E.data.CS := Slow.one_le_slowC

theorem slowC_nonneg : 0 ≤ Slow.slowC := zero_le_one.trans Slow.one_le_slowC

theorem EnergyData.slow :
    SlowCapsJoint E.data.R₀ E.data.Tp E.data.qSFull E.data.L E.data.CS E.data.cS E.data.Sl :=
  (E.data.slow_fields (R₀ := E.R₀) rfl rfl rfl rfl rfl rfl rfl).1

theorem EnergyData.belowS : JointBelow E.data.qS :=
  (E.data.slow_fields (R₀ := E.R₀) rfl rfl rfl rfl rfl rfl rfl).2

theorem EnergyData.kinetic (X R : ℝ) :
    KineticJoint X (R - X) (E.data.Minf R) (E.data.q₀ X R) :=
  kineticJoint_data Slow.slowC 36 X R

theorem EnergyData.below₀ : JointBelow E.data.q₀ :=
  kinJ0_below slowC_nonneg (by norm_num)

end Fields

/-- **The slow threshold of the package**, which reads no open parameter.  J5 may add it to `q₁`,
`q₂`: it contains the floors `2²⁰(1 + c₄) y²`, `2⁵ c₄ Y φ` (role 18), `16 q₀` and the budget of J4,
none of which `JointPiece` hands to the energies otherwise, since E5-J, E8-J only see their own
threshold. -/
def jointSlowFloor (X R : ℝ) (caps : Caps) : ℝ :=
  max (jointBudget (R - X) caps) (64 * Q0Prime X (R - X) (kinJ0 Slow.slowC 36 X R caps) caps)

theorem EnergyData.qSFull_eq (E : EnergyData) : E.data.qSFull = jointSlowFloor := rfl

/-- `jointSlowFloor` is below `Q`, with no hypothesis. -/
theorem jointSlowFloor_below : JointBelow jointSlowFloor :=
  jointBudget_below.sup (JointBelow.const_mul (rootFloor_below.sup
    ((kinJ0_below slowC_nonneg (by norm_num)).const_mul (by norm_num : (0 : ℝ) ≤ 16)))
    (by norm_num))

private lemma nearP_nonneg' {q : ℝ} (hq : 0 ≤ q) : 0 ≤ nearP q := by
  unfold nearP
  have := Real.sqrt_nonneg (MomP q)
  have := Real.rpow_nonneg hq (-(3 : ℝ) / 4)
  positivity

/-- **The near shares on a joint piece**: the hypothesis `nearPaid` of `JointPiece`, summand by
summand: low mixed, purefast and floor; quartic, static and heat coefficient `y`, and floor. -/
theorem EnergyData.near_shares {E : EnergyData} (hr : E.Ranges) {X R r : ℝ} {caps : Caps}
    (hdom : JDom E.data.R₀ X R) (h : E.data.near X R caps |r|) :
    (E.KN * Ex 1 R * (Slow.slowC * Ex 36 R * R * cp caps.yF) * nearN |r| ≤ 1 ∧
      E.KN * Ex 1 R * (Real.sqrt (cp caps.PF) * cp caps.yF ^ ((3 : ℝ) / 2)) * nearN |r| ≤ 1 ∧
      E.KN * Ex 1 R * jointQ X R ^ ((1 : ℝ) / 2) * nearN |r| ≤ 1) ∧
    (E.KP * Ex 1 R * (jointU X ^ ((1 : ℝ) / 4) * Real.sqrt (cp caps.BS)) * nearP |r| ≤ 1 ∧
      E.KP * Ex 1 R * cp caps.yF * nearP |r| ≤ 1 ∧
      E.KP * Ex 1 R * jointQ X R ^ ((1 : ℝ) / 3) * nearP |r| ≤ 1) :=
  ⟨native_shares hr.KN_nonneg slowC_nonneg hdom (nearN_nonneg _) h.1,
    proper_shares hr.KP_nonneg hdom (nearP_nonneg' (abs_nonneg _)) h.2⟩

/-- **`JointInterfaces` from the energies.** -/
theorem EnergyData.Closes.interfaces {E : EnergyData} (h : E.Closes) :
    JointInterfaces E.data where
  Cs_nonneg := h.ranges.Cs_nonneg
  CG_nonneg := h.ranges.CG_nonneg
  m₀_mem := h.ranges.m₀_mem
  L_ge := E.L_ge
  CS_ge := E.CS_ge
  cS_nonneg := by norm_num [EnergyData.data]
  Cm_nonneg := h.ranges.Cm_nonneg
  Tp_ge := fun _ _ _ ↦ by norm_num [EnergyData.data]
  Tp_le := ⟨4, 0, le_rfl, fun X R _ ↦ by simp [EnergyData.data, Ex_zero]⟩
  kinetic := fun X R _ ↦ E.kinetic X R
  h1 := h.h1
  h2 := h.h2
  slow := E.slow
  profiles := jointProfiles
  below₀ := E.below₀
  below₁ := h.below₁
  below₂ := h.below₂
  belowS := E.belowS
  leadN := leadN_jointLN h.ranges.KN_nonneg slowC_nonneg (by norm_num)
  leadP := leadP_jointLP h.ranges.KP_nonneg
  Nbar_nonneg := fun X R hdom ↦ mul_nonneg h.ranges.CN_nonneg (by linarith [hdom.one_lt_X])
  piTol_nonneg := fun X R hdom ↦ mul_nonneg h.ranges.Cp_nonneg (by linarith [hdom.one_lt_X])
  Nbar_le := ⟨E.CN, fun _ _ _ ↦ le_rfl⟩
  piTol_le := ⟨E.Cp, fun _ _ _ ↦ le_rfl⟩

/-- The form of the open hypothesis of `quantitative_joint_of_interfaces`. -/
theorem EnergyData.Closes.exists_interfaces {E : EnergyData} (h : E.Closes) :
    ∃ D : JointData, JointInterfaces D := ⟨E.data, h.interfaces⟩

/-- **Theorem 1.2, joint large force, from the energies.**  The conclusion is verbatim that of
`quantitative_joint_force`.  The hypothesis is the target of J5, for each pair of valid resonant
constants: E5-J (`JointH1Input`), E8-J (`JointH2Input`), and the two role tables. -/
theorem quantitative_joint_of_energies
    (hE : ∀ Cs CH : ℝ, 0 ≤ Cs → 0 < CH → ResH1 ((281 : ℝ) / 1000) Cs →
      ResH2 ((281 : ℝ) / 1000) CH → ∃ E : EnergyData, E.Closes) :
    ∃ C C₀ R₀ : ℝ, 0 < C ∧ 0 < C₀ ∧ 0 < R₀ ∧ ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F →
        let X := Real.exp (Real.exp 1) + M / ν
        let R := X + F / ν ^ 2
        let U := X ^ ((1719 : ℝ) / 719)
        max R₀ (X ^ (24 : ℝ)) ≤ R →
        C * U * R ^ 3 * Real.exp (C₀ * Real.log R / Real.log (Real.log R)) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) :=
  quantitative_joint_of_interfaces fun Cs CH h₀ hC h₁ h₂ ↦ by
    obtain ⟨E, hE'⟩ := hE Cs CH h₀ hC h₁ h₂
    exact hE'.exists_interfaces

end OVNS.Quant

end
