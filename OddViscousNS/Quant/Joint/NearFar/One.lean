import OddViscousNS.Quant.Joint.NearFar.Base

/-!
# The near and far differentials at weight one

`nearD₁(F; N_rest)`, `farD₁(F; N_F)`, the proper heat and the static remainder, at a time and on a
joint piece.  Roles 13, 14, 15; JOINT_ASSEMBLY_V4 §5, rows 9, 13–17.

* `hnorm_one_fastRest`: `‖N_rest‖₁ ≤ (2 C_low M + c_Q √(ab)) b + ‖H_ψ‖₁`.
* The native differential costs `C₀ N(q) ‖N_rest‖₁ b²` (`nearD1_le`): the low mixed monomial
  `N M y`, the purefast `N √P y^{3/2}` and the floor `N`, one summand of `jointLN` each.
* FAR costs `2¹⁴ q⁻¹ ‖N_F‖₁ b²` (`farD1_le`): the threshold `2¹⁴ (N_b y + 1)/η`.
* The heat and the static remainder cost `P(q) y` (`cubicHeat_le`, `cubicE_static_le`).

`‖H_ψ‖₁ ≤ 1/2` (role 18) comes from `jointSlowFloor`, so at weight one nothing is charged to `N_f`,
`f_f`, `m`: each of the four terms is `η b²` or `η a²`.
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.NearFar

open OVNS.Quant.Metric OVNS.Quant.Quartic

variable {μ φ r η KN KP M : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ} {caps : Caps}

/-- **`N_rest` in `H¹`**: the low mixed, purefast and filter directions. -/
theorem hnorm_one_fastRest (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hM : slowSup r g y u ≤ M) :
    InH 1 (fastRest r g y u) ∧ hnorm 1 (fastRest r g y u) ≤
      (2 * CLow 1 * M + cQone * Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u))) *
          hnorm 2 (Fp r g y u) + hnorm 1 (Hpsi r g y u) := by
  have hS := Sp_adm h hu huT
  have hF := Fp_adm h hu huT
  have hF2 : MZ 2 (Fp r g y u) := hF.mz
  have hSup : GN.SupBd (Sp r g y u) M := GN.supBd_slowSup hS.inH hM
  obtain ⟨iL, bL⟩ := hnorm_Qlo_le (r * u) hS (Fam.PiS_Sp r g y u) hSup hF 1
    (by norm_num; exact hF.inH)
  have iL' : InH 1 (Qlo (r * u) (Sp r g y u) (Fp r g y u)) := by simpa using iL
  have bL' : hnorm 1 (Qlo (r * u) (Sp r g y u) (Fp r g y u)) ≤ CLow 1 * M *
      hnorm 2 (Fp r g y u) := by
    have e : (((1 + 1 : ℕ)) : ℝ) = 2 := by norm_num
    have e2 : (((1 : ℕ)) : ℝ) = 1 := by norm_num
    rw [e, e2] at bL
    exact bL
  obtain ⟨iQ, -⟩ := hnorm_Qm_le (phaseM_bdd (r * u)) (σ := 2) (by norm_num) hF2 hF2 hF2 hF2
  have e1 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [e1] at iQ
  have bQ := hnorm_one_Qphase_le (r * u) hF2
  obtain ⟨iH, -⟩ := hnorm_one_Hpsi_le h hr hu huT
  have e : fastRest r g y u = -(Qlo (r * u) (Sp r g y u) (Fp r g y u) +
      Qlo (r * u) (Sp r g y u) (Fp r g y u)) + (-PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u)) +
      -PiF (Hpsi r g y u)) := by
    simp only [fastRest]
    abel
  have i1 := (iL'.add iL').neg
  have i2 : InH 1 (-PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u))) := iQ.PiF.neg
  have i3 := iH.PiF.neg
  refine ⟨by rw [e]; exact i1.add (i2.add i3), ?_⟩
  rw [e]
  refine (hnorm_add_le i1 (i2.add i3)).trans ?_
  have t1 := hnorm_add_le iL' iL'
  have t2 := hnorm_add_le i2 i3
  rw [hnorm_neg]
  have t4 := hnorm_PiF_le iH
  have a2 : hnorm 1 (-PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u))) =
      hnorm 1 (PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u))) := hnorm_neg
  have a3 : hnorm 1 (-PiF (Hpsi r g y u)) = hnorm 1 (PiF (Hpsi r g y u)) := hnorm_neg
  rw [a2, a3] at t2
  have e3 : cQone * Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) *
      hnorm 2 (Fp r g y u) = 16 * Real.sqrt 5488 *
      Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) * hnorm 2 (Fp r g y u) := rfl
  nlinarith only [t1, t2, t4, bL', bQ, e3]

/-- `N_F` in the near and far bounds. -/
lemma mz_fastNL_one (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    MZ 1 (fastNL r g y u) := by
  obtain ⟨hI1, -⟩ := hnorm_PiF_Qphase_le (r * u) (h.sol.adm u hu huT)
  exact ⟨InH.neg hI1, fastNL_zero u⟩

/-- **The near differential in the direction `N_rest`, weight one.** -/
theorem near_one_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hη : 0 < η) (hK : kN / η ≤ KN) (hM0 : 0 ≤ M)
    (ha : fastNorm 1 r g y u ≤ caps.PF) (hb : fastNorm 2 r g y u ≤ caps.yF)
    (hM : slowSup r g y u ≤ M) (hf : hnorm 1 (Hpsi r g y u) ≤ 1 / 2)
    (hS : Shares KN KP M |r| caps) :
    |nearD 1 (-1) r (r * u) (Fp r g y u) (fastRest r g y u)| ≤
      η * fastNorm 2 r g y u ^ 2 := by
  obtain ⟨i, bd⟩ := hnorm_one_fastRest h hr hu huT hM
  have hF := Fp_adm h hu huT
  have hrest : MZ 1 (fastRest r g y u) := ⟨i, fastRest_zero h hu huT⟩
  have h1 := nearD1_le (Or.inr rfl) r (r * u) hF.mz hF.real (PiF_Fp r g y u) hrest
    (isReal_fastRest h hu huT)
  have e0 : fastNorm 2 r g y u = hnorm 2 (Fp r g y u) := rfl
  have ha0 := hnorm_nonneg 1 (Fp r g y u)
  have hb0 := hnorm_nonneg 2 (Fp r g y u)
  have ha' : hnorm 1 (Fp r g y u) ≤ cp caps.PF := ha.trans (le_cp _)
  have hb' : hnorm 2 (Fp r g y u) ≤ cp caps.yF := hb.trans (le_cp _)
  rw [e0]
  set a := hnorm 1 (Fp r g y u)
  set b := hnorm 2 (Fp r g y u)
  set N := nearN |r| with hN
  have hN0 : 0 ≤ N := nearN_nonneg _
  have hC0 := nearC₀_pos
  have hCL1 := CLow_nonneg 1
  have hCL2 := CLow_nonneg 2
  have hcQ := cQone_nonneg
  have hcI := cI_pos
  have hKpos : 0 < KN := lt_of_lt_of_le (div_pos kN_pos hη) hK
  have hroot := sqrt_mul_le_leading ha0 hb0 ha' hb'
  have hMb : M * b ≤ M * cp caps.yF := mul_le_mul_of_nonneg_left hb' hM0
  have hρ : hnorm 1 (fastRest r g y u) ≤ 2 * CLow 1 * (M * cp caps.yF) +
      cQone * (Real.sqrt (cp caps.PF) * cp caps.yF ^ ((3 : ℝ) / 2)) + 1 / 2 := by
    have t1 := mul_le_mul_of_nonneg_left hMb (by positivity : 0 ≤ 2 * CLow 1)
    have t2 := mul_le_mul_of_nonneg_left hroot hcQ
    nlinarith only [bd, t1, t2, hf]
  have hs := share_sum (K := KN) (η := η) (c := kN) (a₁ := nearC₀ * (2 * CLow 1))
    (a₂ := nearC₀ * cQone) (a₃ := nearC₀ * (1 / 2)) hKpos hη hS.low hS.pure hS.flr
    (by positivity) (by positivity) (by positivity)
    (by unfold kN; nlinarith only [hC0, hCL1, hCL2, hcQ, hcI]) hK
  have h2 : nearC₀ * N * hnorm 1 (fastRest r g y u) ≤ η := by
    have := mul_le_mul_of_nonneg_left hρ (by positivity : 0 ≤ nearC₀ * N)
    nlinarith only [this, hs]
  have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg b)
  have e : nearC₀ * nearN |r| * hnorm 1 (fastRest r g y u) * (b * b) =
      nearC₀ * N * hnorm 1 (fastRest r g y u) * b ^ 2 := by
    rw [hN]
    ring
  rw [e] at h1
  exact h1.trans h3

/-- `N_b`: `‖N_F‖₁ ≤ N_b b + ‖H_ψ‖₁` (`fastNL_one_caps`). -/
def nbF (caps : Caps) : ℝ := 8 * (cp caps.WS + c4 * cp caps.BS + c4 * cp caps.yF)

lemma nbF_nonneg (caps : Caps) : 0 ≤ nbF caps := by
  have h1 := cp_nonneg caps.WS
  have h2 := cp_nonneg caps.BS
  have h3 := cp_nonneg caps.yF
  have h4 := c4_pos
  unfold nbF
  positivity

/-- **The native FAR at weight one**, in the full direction `N_F`. -/
theorem far_one_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hη : 0 < η) (hW : wiener (Sp r g y u) ≤ cp caps.WS)
    (hB : hnorm 2 (Sp r g y u) ≤ cp caps.BS) (hb : hnorm 2 (Fp r g y u) ≤ cp caps.yF)
    (hf : hnorm 1 (Hpsi r g y u) ≤ 1 / 2)
    (hq : 2 ^ 14 / η * (nbF caps * cp caps.yF + 1) ≤ |r|) :
    |farD 1 (-1) r (r * u) (Fp r g y u) (fastNL r g y u)| ≤ η * fastNorm 2 r g y u ^ 2 := by
  have hF := Fp_adm h hu huT
  have hN := mz_fastNL_one h hu huT
  have h1 := farD1_le (Or.inr rfl) hr (r * u) hF.mz (PiF_Fp r g y u) hN
  have h2 := fastNL_one_caps h hr hu huT hW hB hb
  have e0 : fastNorm 2 r g y u = hnorm 2 (Fp r g y u) := rfl
  have hb0 := hnorm_nonneg 2 (Fp r g y u)
  rw [e0]
  set b := hnorm 2 (Fp r g y u)
  have hq0 : 0 < |r| := abs_pos.2 hr
  have hnb := nbF_nonneg caps
  have hn0 := hnorm_nonneg 1 (fastNL r g y u)
  have h3 : hnorm 1 (fastNL r g y u) ≤ nbF caps * cp caps.yF + 1 := by
    have t := mul_le_mul_of_nonneg_left hb hnb
    have e : 8 * (cp caps.WS + c4 * cp caps.BS + c4 * cp caps.yF) * b = nbF caps * b := rfl
    rw [e] at h2
    linarith
  have h4 : 2 ^ 14 / |r| * (nbF caps * cp caps.yF + 1) ≤ η := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hq0]
    rw [div_mul_eq_mul_div, div_le_iff₀ hη] at hq
    linarith
  have h5 : 2 ^ 14 / |r| * hnorm 1 (fastNL r g y u) ≤ η :=
    (mul_le_mul_of_nonneg_left h3 (by positivity)).trans h4
  exact h1.trans (mul_le_mul_of_nonneg_right h5 (sq_nonneg b))

lemma cStat_le_kP : cStat ≤ kP := by
  have hc := c4_pos
  unfold cStat kP H2.cHeat2
  nlinarith only [hc]

lemma cHeat_le_kP : cHeat ≤ kP := by
  have hc := c4_pos
  unfold cHeat kP H2.cHeat2
  nlinarith only [hc]

/-- **The static remainder at weight one**: `|E⁰| ≤ cStat P(q) a² b`, paid by `P(q) y`. -/
theorem static_one_le (h : ActualSol μ φ r g y Ty) (hr : 1 ≤ |r|) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hη : 0 < η) (hK : kP / η ≤ KP)
    (hb : fastNorm 2 r g y u ≤ caps.yF) (hS : Shares KN KP M |r| caps) :
    |cubicE 1 (-1) r (r * u) (Fp r g y u)| ≤ η * fastNorm 1 r g y u ^ 2 := by
  have hF := Fp_adm h hu huT
  have h1 := cubicE_static_le hr (r * u) hF.mz (PiF_Fp r g y u)
  have e0 : fastNorm 1 r g y u = hnorm 1 (Fp r g y u) := rfl
  have hb' : hnorm 2 (Fp r g y u) ≤ cp caps.yF := hb.trans (le_cp _)
  have hP0 : 0 ≤ nearP |r| := nearP_nonneg (abs_nonneg _)
  have hy := cp_nonneg caps.yF
  have h2 := share_one hη hK cStat_le_kP (mul_nonneg hP0 hy) hS.stat
  have hc0 : 0 ≤ cStat := by
    unfold cStat
    norm_num
  rw [e0]
  have h3 : cStat * nearP |r| * hnorm 2 (Fp r g y u) ≤ η :=
    (mul_le_mul_of_nonneg_left hb' (mul_nonneg hc0 hP0)).trans (by nlinarith only [h2])
  have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg (hnorm 1 (Fp r g y u)))
  nlinarith only [h1, h4]

/-- **Both input heats at weight one**: `|E_heat| ≤ cHeat P(q) b³`, paid by `P(q) y`. -/
theorem heat_one_le (h : ActualSol μ φ r g y Ty) (hr : 1 ≤ |r|) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hη : 0 < η) (hK : kP / η ≤ KP)
    (hb : fastNorm 2 r g y u ≤ caps.yF) (hS : Shares KN KP M |r| caps) :
    |cubicHeat r (r * u) (Fp r g y u)| ≤ η * fastNorm 2 r g y u ^ 2 := by
  have hF := Fp_adm h hu huT
  have h1 := cubicHeat_le hr (r * u) hF.mz hF.real (PiF_Fp r g y u)
  have e0 : fastNorm 2 r g y u = hnorm 2 (Fp r g y u) := rfl
  have hb' : hnorm 2 (Fp r g y u) ≤ cp caps.yF := hb.trans (le_cp _)
  have hP0 : 0 ≤ nearP |r| := nearP_nonneg (abs_nonneg _)
  have hy := cp_nonneg caps.yF
  have h2 := share_one hη hK cHeat_le_kP (mul_nonneg hP0 hy) hS.stat
  have hc0 : 0 ≤ cHeat := by
    unfold cHeat
    norm_num
  rw [e0]
  have h3 : cHeat * nearP |r| * hnorm 2 (Fp r g y u) ≤ η :=
    (mul_le_mul_of_nonneg_left hb' (mul_nonneg hc0 hP0)).trans (by nlinarith only [h2])
  have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg (hnorm 2 (Fp r g y u)))
  nlinarith only [h1, h4]

end OVNS.Quant.NearFar

end
