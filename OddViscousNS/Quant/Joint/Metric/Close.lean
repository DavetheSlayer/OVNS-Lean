import OddViscousNS.Quant.Joint.Metric.Degrees

/-!
# The energies close: the target of J5

`energyData`: the open parameters of the joint package; `energyData_closes`: `E.Closes`, for each pair
of valid resonant constants.  With `quantitative_joint_of_energies` this is the conclusion of
`quantitative_joint_force`.

| field | value | |
|---|---|---|
| `R₀` | `0` | `JDom` alone is enough |
| `q₁`, `q₂` | `q1`, `q2` | at `C = slowC`, `c = 36` |
| `Cs`, `CG` | `Cs`, `CH` | the resonant constants are not enlarged |
| `m₀` | `1/4` | the mass per clip is `≤ 0.073` |
| `Cm` | `2³⁶ Chigh (2 C_low(1))` | rows 2, 3 |
| `CN`, `Cp` | `3`, `2` | `N_f = 6 hBd`, `f_f = 48 c₄ P_F² hBd` |
| `KN`, `KP` | `2¹¹ kN`, `2¹¹ kP` | absolute |

No value depends on the cap scale `K`.
-/

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.NearFar

/-- **The open parameters of the joint package.** -/
def energyData (Cs CH : ℝ) : EnergyData where
  R₀ := 0
  q₁ := fun X R caps ↦ q1 Slow.slowC 36 X R caps
  q₂ := fun X R caps ↦ q2 Slow.slowC 36 X R caps
  Cs := Cs
  CG := CH
  m₀ := 1 / 4
  Cm := 2 ^ 36 * Chigh (2 * CLow 1)
  CN := 3
  Cp := 2
  KN := 2 ^ 11 * kN
  KP := 2 ^ 11 * kP

lemma Cm_le : 0 ≤ (2 : ℝ) ^ 36 * Chigh (2 * CLow 1) :=
  mul_nonneg (by norm_num) (Chigh_nonneg (mul_nonneg (by norm_num) (CLow_nonneg 1)))

/-- **The ranges.** -/
theorem energyData_ranges {Cs CH : ℝ} (h0 : 0 ≤ Cs) (hC : 0 < CH) : (energyData Cs CH).Ranges where
  Cs_nonneg := h0
  CG_nonneg := hC.le
  m₀_mem := by norm_num [energyData]
  Cm_nonneg := Cm_le
  CN_nonneg := by norm_num [energyData]
  Cp_nonneg := by norm_num [energyData]
  KN_nonneg := by
    have := kN_pos
    simp only [energyData]
    positivity
  KP_nonneg := by
    have := kP_pos
    simp only [energyData]
    positivity

lemma kN_le₁ : 256 * kN ≤ 2 ^ 11 * kN := by
  have := kN_pos
  nlinarith only [this]

lemma kP_le₁ : 256 * kP ≤ 2 ^ 11 * kP := by
  have := kP_pos
  nlinarith only [this]

lemma kN_le₂ : kN / eta2 ≤ 2 ^ 11 * kN := by
  have e : kN / eta2 = 2 ^ 11 * kN := by
    simp only [eta2]
    field_simp
  exact e.le

lemma kP_le₂ : kP / eta2 ≤ 2 ^ 11 * kP := by
  have e : kP / eta2 = 2 ^ 11 * kP := by
    simp only [eta2]
    field_simp
  exact e.le

lemma one_le_KP' : 1 ≤ (2 : ℝ) ^ 11 * kP :=
  one_le_KP (η := eta2) (by norm_num [eta2]) (by norm_num [eta2]) kP_le₂

/-- **E5-J.** -/
theorem energyData_h1 {Cs CH : ℝ} (hres : ResH1 ((281 : ℝ) / 1000) Cs) :
    JointH1Input (energyData Cs CH) := by
  intro X R hdom r g y Ty caps s t hsol hP
  have hCS : 0 ≤ Slow.slowC := slowC_nonneg
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hq : q1 Slow.slowC 36 X R caps ≤ |r| := hP.thr
  have hT := Thr1_of hdom hCS hq
  exact h1_output (CN := 3) (Cp := 2) hres hdom hCS kN_le₁ kP_le₁ one_le_KP' (one_le_pow₀ hR1)
    (by norm_num) (by norm_num) hsol hP hT

/-- **E8-J.** -/
theorem energyData_h2 {Cs CH : ℝ} (hres : ResH2 ((281 : ℝ) / 1000) CH) :
    JointH2Input (energyData Cs CH) := by
  intro X R hdom r g y Ty caps s t hsol hP hG
  have hCS : 0 ≤ Slow.slowC := slowC_nonneg
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hq : q2 Slow.slowC 36 X R caps ≤ |r| := (le_max_left _ _).trans hP.thr
  have hT := Thr2_of hdom hCS hq
  have hfl : jointSlowFloor X R caps ≤ |r| :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hT.q)
  obtain ⟨-, -, -, -, hr⟩ := floor_setup hdom hfl
  have hK : 0 ≤ 2 * CLow 1 := mul_nonneg (by norm_num) (CLow_nonneg 1)
  obtain ⟨-, -, -, hrow⟩ := row23_piece (energyData Cs CH).data (K := 2 * CLow 1) hr hR1 hK hCS
    le_rfl hsol hP
  exact h2_output hres hdom hCS kN_le₂ kP_le₂ hsol hP hT hG hrow

/-- **The target of J5.** -/
theorem energyData_closes {Cs CH : ℝ} (h0 : 0 ≤ Cs) (hC : 0 < CH)
    (h₁ : ResH1 ((281 : ℝ) / 1000) Cs) (h₂ : ResH2 ((281 : ℝ) / 1000) CH) :
    (energyData Cs CH).Closes where
  ranges := energyData_ranges h0 hC
  h1 := energyData_h1 h₁
  h2 := energyData_h2 h₂
  below₁ := q1_below slowC_nonneg
  below₂ := q2_below slowC_nonneg

/-- **The hypothesis of `quantitative_joint_of_energies`.** -/
theorem energies_close (Cs CH : ℝ) (h0 : 0 ≤ Cs) (hC : 0 < CH)
    (h₁ : ResH1 ((281 : ℝ) / 1000) Cs) (h₂ : ResH2 ((281 : ℝ) / 1000) CH) :
    ∃ E : EnergyData, E.Closes :=
  ⟨energyData Cs CH, energyData_closes h0 hC h₁ h₂⟩

end OVNS.Quant.Metric

end
