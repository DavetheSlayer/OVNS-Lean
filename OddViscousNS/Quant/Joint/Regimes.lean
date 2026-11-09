import OddViscousNS.Quant.Joint.Arith
import OddViscousNS.Quant.Joint.Continuation
import OddViscousNS.Quant.Regimes.FixedForce
import OddViscousNS.Quant.Arith.Main

/-!
# Theorem 1.2, joint large force: the regimes layer against the joint interfaces (step J0)

`quantitative_joint_of_interfaces`: the conclusion of `quantitative_joint_force`, verbatim, from
the two published counting inputs and the package `JointInterfaces` (`Joint/Interfaces.lean`).
There is no compact range: `R ≥ max(R₀, X²⁴)` makes everything large (TeX, joint proof).

Reused by import: `young_cubic`, `barrier_cap`, `peakSq`, `dissipSq`, `first_exit`,
`pieces_induction`, `norms_continuous`, `actual_mz`, `ae_inH3_fast`, `interp_fast`, and the glue of
`Regimes/{Scalar,FixedForce}.lean` (`peak_le`, `dissip_le`, `BarrierProp`, `energy_step`, ...),
parameter-only statements with no dependence on the regime.

Proof structure (all proved):
* (a) E6 and E10 from the *local* outputs `H1Output`, `H2Output`: `scalar_peak_of_output`,
  `scalar_dissipation_of_output`, `fast_H2_of_output`.  The library lemmas take the global
  `H1EnergyInterface`, which the joint interfaces do not imply (`JointPiece` has extra hypotheses);
  the proofs are those of `Regimes/Scalar.lean`, `Regimes/FixedForce.lean`.
* (b) the joint caps `capsJ`, `capsJImp`, `capsJStart`, `capsJoint`: `P_F = K_P U`, `y = K_Y T`,
  `J_F = K_J U²`, with `K_P = Z^{β/2}` (`jointZ`: the E6 fixed point, `Z ≍ Tp`), and the slow caps
  at the exponents `slowExpHA`; `capsJoint_scaled`, `fast_budget`.
* (c) `thresholds_paid_joint`: one trial `C Q Ex(C₀, R)` pays the four thresholds, among them the
  true rows 2, 3 of Table quant-metric and the raised floor (`Joint/Arith.lean`), and the near roles
  (`near_pay`), for every larger `q`.
* (d) `strictOn_joint`: strict improvement along a solution, in the chronology of the TeX: slow
  first (E7-P), kinetic (E4-J), `H¹` peak and dissipation (E5-J, E6), `H²` barrier (E8-J, E10).
  The start predicate is the backward-unit history: `slowHistory_zero` at the datum,
  `slowHistory_regained` on the last unit of a piece, with no analysis.
* (e) `joint_normalized`, `joint_of_data`, `quantitative_joint_of_interfaces`.
-/

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace OVNS.Quant

/-! ### (a) E6 and E10 from the local outputs -/

section Local

variable {r : ℝ} {g : Field} {y : ℝ → Field} {s t : ℝ}

/-- **E6, peak, from the output of the `H¹` energy on `[s, t]`** (the proof of
`scalar_peak_on_piece`): `a_F² ≤ peakSq` given the cap `a_F ≤ P_F`, the kinetic integral
`∫ a_F² ≤ I_a`, the incoming trace `a_F(s) ≤ M_f` and Young's constant at `λ`. -/
theorem scalar_peak_of_output {σ Cs Nbar piTol PF Ia Mf cy lam : ℝ} (hσ : 0 < σ ∧ σ < 1)
    (hst : s ≤ t) (hout : H1Output σ Cs Nbar piTol r g y s t)
    (hPF : ∀ u ∈ Icc s t, fastNorm 1 r g y u ≤ PF) (hlam : 0 < lam ∧ lam < 3 / 4) (hcy0 : 0 ≤ cy)
    (hcy : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Cs * a ^ (3 - σ) * b ^ σ ≤ lam * b ^ 2 + cy * a ^ (4 - 2 / betaOf σ))
    (hkin : (∫ u in s..t, fastNorm 1 r g y u ^ 2) ≤ Ia) (hin : fastNorm 1 r g y s ≤ Mf)
    (hc1 : ContinuousOn (fastNorm 1 r g y) (Icc s t))
    (hc2 : ContinuousOn (fastNorm 2 r g y) (Icc s t)) :
    ∀ v ∈ Icc s t, fastNorm 1 r g y v ^ 2 ≤ peakSq σ cy lam Mf PF Ia Nbar piTol := by
  obtain ⟨E, Nf, ff, m, hco, hint, hfm, hNi, hfi, hmi, hNb, hfb, hmb⟩ := hout
  have hn : 0 < 3 / 4 - lam := by linarith
  have ha0 : ∀ u, 0 ≤ fastNorm 1 r g y u := fun u => hnorm_nonneg _ _
  have hb0 : ∀ u, 0 ≤ fastNorm 2 r g y u := fun u => hnorm_nonneg _ _
  have hℓ : 0 < ell1 := by norm_num [ell1]
  have hβ := one_lt_betaOf hσ
  have hp1 : 1 / betaOf σ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hEq : ∀ u ∈ uIcc s t, |ff u| = ff u ∧ |m u| = m u := fun u hu => by
    rw [uIcc_of_le hst] at hu
    exact ⟨abs_of_nonneg (hfm u hu).1, abs_of_nonneg (hfm u hu).2⟩
  have hfint : (∫ u in s..t, |ff u|) = ∫ u in s..t, ff u :=
    intervalIntegral.integral_congr fun u hu => (hEq u hu).1
  have hmint : (∫ u in s..t, |m u|) = ∫ u in s..t, m u :=
    intervalIntegral.integral_congr fun u hu => (hEq u hu).2
  have hIa : 0 ≤ Ia := (intervalIntegral.integral_nonneg hst fun u _ => sq_nonneg _).trans hkin
  have hcore := peak_bound_core (Φ := fun u => fastNorm 1 r g y u ^ 2) (E := E)
    (β := fun u => Nf u ^ 2 / (4 * (3 / 4 - lam)) + |ff u|) (m := fun u => |m u|)
    (c := cy) (p := 1 / betaOf σ) (M := PF ^ 2) (I := Ia)
    (S := Nbar ^ 2 / (4 * (3 / 4 - lam)) + piTol ^ 2) hst hℓ hp1 hcy0 (sq_nonneg _) hIa
    (by positivity) (hc1.pow 2) (fun u => sq_nonneg _)
    (fun u hu => pow_le_pow_left₀ (ha0 u) (hPF u hu) 2) hkin
    (fun u hu => (hco u hu).1) ((hNi.div_const _).add hfi.abs)
    (fun u => by have := abs_nonneg (ff u); positivity)
    (by
      rw [intervalIntegral.integral_add (hNi.div_const _) hfi.abs, intervalIntegral.integral_div,
        hfint]
      have := div_le_div_of_nonneg_right hNb (by positivity : (0 : ℝ) ≤ 4 * (3 / 4 - lam))
      linarith)
    hmi.abs (fun u => abs_nonneg _) (by rw [hmint]; exact hmb)
    (fun v hv => by
      have h := energy_step (ε := 3 / 4 - lam) hσ hn hlam.1.le hcy0 le_rfl hv.1 hv.2 hc1 hc2
        ha0 hb0 hcy hfm hNi hfi hmi (hint s v le_rfl hv.1 hv.2)
      have e : lam + (3 / 4 - lam) = 3 / 4 := by ring
      rw [e] at h
      linarith)
  intro v hv
  have h := hcore v hv
  have hEs : E s ≤ u1 * Mf ^ 2 / 2 := by
    have h1 := (hco s ⟨le_rfl, hst⟩).2
    have h2 : fastNorm 1 r g y s ^ 2 ≤ Mf ^ 2 := pow_le_pow_left₀ (ha0 s) hin 2
    have : 0 < u1 := by norm_num [u1]
    nlinarith
  unfold peakSq
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  linarith

/-- **E6, dissipation, from the output of the `H¹` energy on `[s, t]`** (the proof of
`scalar_dissipation_on_piece`): `∫ b_F² ≤ dissipSq`. -/
theorem scalar_dissipation_of_output {σ Cs Nbar piTol PF Ia Mf cy lam : ℝ} (hσ : 0 < σ ∧ σ < 1)
    (hst : s ≤ t) (hout : H1Output σ Cs Nbar piTol r g y s t)
    (hPF : ∀ u ∈ Icc s t, fastNorm 1 r g y u ≤ PF) (hlam : 0 < lam ∧ lam < 3 / 4) (hcy0 : 0 ≤ cy)
    (hcy : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Cs * a ^ (3 - σ) * b ^ σ ≤ lam * b ^ 2 + cy * a ^ (4 - 2 / betaOf σ))
    (hkin : (∫ u in s..t, fastNorm 1 r g y u ^ 2) ≤ Ia) (hin : fastNorm 1 r g y s ≤ Mf)
    (hc1 : ContinuousOn (fastNorm 1 r g y) (Icc s t))
    (hc2 : ContinuousOn (fastNorm 2 r g y) (Icc s t)) :
    (∫ u in s..t, fastNorm 2 r g y u ^ 2) ≤ dissipSq σ cy lam Mf PF Ia Nbar piTol := by
  unfold dissipSq
  have hpeak := scalar_peak_of_output hσ hst hout hPF hlam hcy0 hcy hkin hin hc1 hc2
  obtain ⟨E, Nf, ff, m, hco, hint, hfm, hNi, hfi, hmi, hNb, hfb, hmb⟩ := hout
  have hn : 0 < 3 / 4 - lam := by linarith
  have ha0 : ∀ u, 0 ≤ fastNorm 1 r g y u := fun u => hnorm_nonneg _ _
  have hb0 : ∀ u, 0 ≤ fastNorm 2 r g y u := fun u => hnorm_nonneg _ _
  have hℓ : 0 < ell1 := by norm_num [ell1]
  have hu1 : 0 < u1 := by norm_num [u1]
  have hβ := one_lt_betaOf hσ
  have hp1 : 1 / betaOf σ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  set P := peakSq σ cy lam Mf PF Ia Nbar piTol with hP
  set X := (PF ^ 2) ^ (1 - 1 / betaOf σ) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg (sq_nonneg _) _
  have hP0 : 0 ≤ P := (sq_nonneg _).trans (hpeak s ⟨le_rfl, hst⟩)
  have hIa : 0 ≤ Ia := (intervalIntegral.integral_nonneg hst fun u _ => sq_nonneg _).trans hkin
  have hEq : ∀ u ∈ uIcc s t, |ff u| = ff u ∧ |m u| = m u := fun u hu => by
    rw [uIcc_of_le hst] at hu
    exact ⟨abs_of_nonneg (hfm u hu).1, abs_of_nonneg (hfm u hu).2⟩
  have hfint : (∫ u in s..t, |ff u|) = ∫ u in s..t, ff u :=
    intervalIntegral.integral_congr fun u hu => (hEq u hu).1
  have hmint : (∫ u in s..t, |m u|) = ∫ u in s..t, m u :=
    intervalIntegral.integral_congr fun u hu => (hEq u hu).2
  have hEt : 0 ≤ E t := by
    have := (hco t ⟨hst, le_rfl⟩).1
    have := mul_nonneg hℓ.le (sq_nonneg (fastNorm 1 r g y t))
    linarith
  have hEs : E s ≤ u1 * Mf ^ 2 / 2 := by
    have h1 := (hco s ⟨le_rfl, hst⟩).2
    have h2 : fastNorm 1 r g y s ^ 2 ≤ Mf ^ 2 := pow_le_pow_left₀ (ha0 s) hin 2
    nlinarith
  have hm2 : (∫ u in s..t, m u) ≤ ell1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_one hℓ] at hmb
    linarith
  have hc1' : ContinuousOn (fastNorm 1 r g y) (uIcc s t) := by
    rw [uIcc_of_le hst]
    exact hc1
  have hai : IntervalIntegrable (fun u => fastNorm 1 r g y u ^ 2) volume s t :=
    (hc1'.pow 2).intervalIntegrable
  set B := u1 * Mf ^ 2 / 2 + cy * X * Ia + piTol ^ 2 + ell1 / 2 * P with hB
  have hB0 : 0 ≤ B := by positivity
  have key : ∀ ε > 0, (3 / 4 - lam) * (∫ u in s..t, fastNorm 2 r g y u ^ 2) ≤
      B + ε * (∫ u in s..t, fastNorm 2 r g y u ^ 2) + Nbar ^ 2 / (4 * ε) := by
    intro ε hε
    have h := energy_step (ε := ε) hσ hε hlam.1.le hcy0 le_rfl hst le_rfl hc1 hc2 ha0 hb0 hcy
      hfm hNi hfi hmi (hint s t le_rfl hst le_rfl)
    have hKi : IntervalIntegrable (fun u => cy * (fastNorm 1 r g y u ^ 2) ^ (2 - 1 / betaOf σ) +
        (Nf u ^ 2 / (4 * ε) + |ff u|) + |m u| * fastNorm 1 r g y u ^ 2) volume s t :=
      ((((hc1'.pow 2).rpow_const fun _ _ => Or.inr (by linarith)).intervalIntegrable.const_mul
        cy).add ((hNi.div_const _).add hfi.abs)).add (hmi.abs.mul_continuousOn (hc1'.pow 2))
    have hK'i : IntervalIntegrable (fun u => cy * X * fastNorm 1 r g y u ^ 2 +
        Nf u ^ 2 / (4 * ε) + |ff u| + P * |m u|) volume s t :=
      (((hai.const_mul _).add (hNi.div_const _)).add hfi.abs).add (hmi.abs.const_mul _)
    have hKK := intervalIntegral.integral_mono_on hst hKi hK'i fun u hu => by
      have hΦ := hpeak u hu
      have hpow : (fastNorm 1 r g y u ^ 2) ^ (2 - 1 / betaOf σ) ≤
          X * fastNorm 1 r g y u ^ 2 := by
        rw [show (2 - 1 / betaOf σ : ℝ) = (1 - 1 / betaOf σ) + 1 by ring,
          Real.rpow_add' (sq_nonneg _) (by linarith), Real.rpow_one]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (sq_nonneg _)
          (pow_le_pow_left₀ (ha0 u) (hPF u hu) 2) (by linarith)) (sq_nonneg _)
      have h1 := mul_le_mul_of_nonneg_left hpow hcy0
      have h2 := mul_le_mul_of_nonneg_left hΦ (abs_nonneg (m u))
      linarith
    rw [intervalIntegral.integral_add (((hai.const_mul _).add (hNi.div_const _)).add hfi.abs)
      (hmi.abs.const_mul _), intervalIntegral.integral_add ((hai.const_mul _).add
      (hNi.div_const _)) hfi.abs, intervalIntegral.integral_add (hai.const_mul _)
      (hNi.div_const _), intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, hfint, hmint] at hKK
    have h3 := mul_le_mul_of_nonneg_left hkin (mul_nonneg hcy0 hX0)
    have h4 := div_le_div_of_nonneg_right hNb (by positivity : (0 : ℝ) ≤ 4 * ε)
    have h5 := mul_le_mul_of_nonneg_left hm2 hP0
    linarith
  have hJ0 : 0 ≤ ∫ u in s..t, fastNorm 2 r g y u ^ 2 :=
    intervalIntegral.integral_nonneg hst fun u _ => sq_nonneg _
  have hroot := dissipation_root hn hB0 (abs_nonneg Nbar) hJ0 (sqrt_bound hB0 hJ0 key)
  rwa [sq_abs] at hroot

/-- **E10 on a piece, from the output of the `H²` energy** (the proof of `fast_H2_on_piece`): the
fast `H²` cap improves to `(19/20) y`, and after the first unit (`1/λ_* ≤ 1`, from `B ≥ 1`) it is
back below `(4/5) y`.  `barrier_cap` is applied at the coefficient `B` of the output, with the
clipped `c̃_F = max(c_F, b_F²/A)`. -/
theorem fast_H2_of_output {μ φ A B m₀ Cb yF : ℝ} {Ty : ℝ≥0∞}
    (hout : H2Output A B m₀ r g y s t) (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4) (hCb : 0 ≤ Cb)
    (hbar : BarrierProp m₀ Cb) (hsol : ActualSol μ φ r g y Ty) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) (ha : ∀ u ∈ Icc s t, fastNorm 1 r g y u ≤ A)
    (hbY : ∀ u ∈ Icc s t, fastNorm 2 r g y u ≤ yF) (hA : 0 < A) (hB : 1 ≤ B) (hyF : 0 ≤ yF)
    (hCW : Cb * WStar 1 A B ≤ yF ^ 2 / 100) (hin : fastNorm 2 r g y s ≤ 4 / 5 * yF) :
    (∀ v ∈ Icc s t, fastNorm 2 r g y v ≤ 19 / 20 * yF) ∧
      ∀ v ∈ Icc (s + 1) t, fastNorm 2 r g y v ≤ 4 / 5 * yF := by
  obtain ⟨W, G, H, hco, hc3, hineq, hGH, hGi, hHi, hclip⟩ := hout
  obtain ⟨-, c2, -, -, -⟩ := norms_continuous hsol (b := t) (hs.trans hst) ht
  have c2' := c2.mono (Icc_subset_Icc hs le_rfl)
  set bF := fastNorm 2 r g y with hbF
  set c3 := fastNorm 3 r g y with hc3def
  set cF : ℝ → ℝ := fun u ↦ max (c3 u) (bF u ^ 2 / A) with hcF
  have hb0 : ∀ u, 0 ≤ bF u := fun u ↦ hnorm_nonneg _ _
  have hint : ∀ u ∈ Icc s t, bF u ^ 2 ≤ A * cF u := fun u _ ↦ by
    have : bF u ^ 2 / A ≤ cF u := le_max_right _ _
    rw [div_le_iff₀ hA] at this
    linarith
  -- `cF = c₃` almost everywhere on `[s, t]`
  have hae : ∀ᵐ u, u ∈ Icc s t → cF u = c3 u := by
    have h := (ae_restrict_iff' measurableSet_Icc).1 (ae_inH3_fast hsol (hs.trans hst) ht)
    filter_upwards [h] with u hu hmem
    have h3 := hu ⟨hs.trans hmem.1, hmem.2⟩
    have hip := interp_fast h3
    have haF := ha u hmem
    have hc0 : 0 ≤ c3 u := hnorm_nonneg _ _
    have : bF u ^ 2 / A ≤ c3 u := by
      rw [div_le_iff₀ hA]
      calc bF u ^ 2 ≤ fastNorm 1 r g y u * c3 u := hip
        _ ≤ A * c3 u := mul_le_mul_of_nonneg_right haF hc0
        _ = c3 u * A := by ring
    exact max_eq_left this
  have haeI : ∀ {a b : ℝ}, s ≤ a → a ≤ b → b ≤ t → ∀ᵐ u, u ∈ uIoc a b → cF u = c3 u := by
    intro a b ha' hab hb
    filter_upwards [hae] with u hu hmem
    rw [uIoc_of_le hab] at hmem
    exact hu ⟨ha'.trans hmem.1.le, hmem.2.trans hb⟩
  have hcFi : IntervalIntegrable (fun u ↦ cF u ^ 2) volume s t := by
    refine hc3.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [haeI le_rfl hst le_rfl] with u hu hmem
    rw [hu hmem]
  have hineq' : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      W u₂ - W u₁ ≤ ∫ u in u₁..u₂,
        (-2 * dZero * cF u ^ 2 + 2 * B * bF u * cF u + G u * W u + H u) := by
    intro u₁ u₂ h1 h2 h3
    refine (hineq u₁ u₂ h1 h2 h3).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [haeI h1 h2 h3] with u hu hmem
    rw [hu hmem]
  have hBpos : 0 < B := by linarith
  have hbarv := hbar hA hBpos hst c2' hb0 hco hint hcFi hineq' hGH hGi hHi hclip
  obtain ⟨he0, he1⟩ := exp_bounds hm₀
  have hWst0 : 0 ≤ WStar 1 A B := by unfold WStar; positivity
  have hCW0 : 0 ≤ Cb * WStar 1 A B := mul_nonneg hCb hWst0
  have hlam : 1 / lamStar 1 A B ≤ 1 := inv_lamStar_le hA hB
  have hfull : ∀ v ∈ Icc s t, 1 / lamStar 1 A B ≤ v - s → bF v ≤ 4 / 5 * yF := by
    intro v hv hle
    exact full_clip_arith (hb0 v) hyF (hco v hv).1 ((hbarv v hv).2 hle yF hbY) he1 hCW
  refine ⟨fun v hv ↦ ?_, fun v hv ↦ hfull v ⟨by linarith [hv.1], hv.2⟩ (by linarith [hv.1])⟩
  rcases le_total (v - s) (1 / lamStar 1 A B) with hle | hle
  · have hWs : W s ≤ 33 / 32 * (4 / 5 * yF) ^ 2 := by
      have h1 := (hco s ⟨le_rfl, hst⟩).2
      have h2 : bF s ^ 2 ≤ (4 / 5 * yF) ^ 2 := pow_le_pow_left₀ (hb0 s) hin 2
      linarith
    exact first_clip_arith (hb0 v) hyF (hco v hv).1 ((hbarv v hv).1 hle) he0
      (Real.exp_pos _).le hWs hCW0 hCW
  · linarith [hfull v hv hle]

end Local

/-! ### (b) The joint caps -/

/-- **The joint caps** from their fast sizes and the slow constant `CS` (polylog included):
`A_S, W_S = 2 CS R^{3/2}`, `B_S, B_H = 2 CS R²`, `J_S = 2 CS R³`, `E_S, A_H = 2 CS R`. -/
def capsJ (PF yF JF CS R : ℝ) : Caps :=
  ⟨PF, yF, 2 * CS * R ^ slowExpHA.eA, 2 * CS * R ^ slowExpHA.eB, 2 * CS * R ^ slowExpHA.eW, JF,
    2 * CS * R ^ slowExpHA.eJ, 2 * CS * R, 2 * CS * R, 2 * CS * R ^ 2⟩

/-- The improved caps: `P_F/2`, `(19/20) y`, `J_F/2` and half of every slow cap. -/
def capsJImp (PF yF JF CS R : ℝ) : Caps :=
  ⟨PF / 2, 19 / 20 * yF, CS * R ^ slowExpHA.eA, CS * R ^ slowExpHA.eB, CS * R ^ slowExpHA.eW,
    JF / 2, CS * R ^ slowExpHA.eJ, CS * R, CS * R, CS * R ^ 2⟩

/-- The start levels of a good point: the improved fast `H¹` cap, the post-clip fast `H²` level
`(4/5) y`, and the slow start levels `L'` (`levelsJ` of `SlowCapsJoint`). -/
def capsJStart (PF yF JF CS R : ℝ) (L' : Fin 5 → ℝ) : Caps :=
  ⟨PF / 2, 4 / 5 * yF, L' 3 * R ^ slowExpHA.eA, L' 4 * R ^ slowExpHA.eB, CS * R ^ slowExpHA.eW,
    JF / 2, CS * R ^ slowExpHA.eJ, L' 0 * R, L' 1 * R, L' 2 * R ^ 2⟩

/-- The improved caps lie strictly below the caps. -/
theorem capsJImp_below {PF yF JF CS R : ℝ} (hPF : 0 < PF) (hyF : 0 < yF) (hJF : 0 < JF)
    (hCS : 0 < CS) (hR : 0 < R) : (capsJImp PF yF JF CS R).Below (capsJ PF yF JF CS R) := by
  have hA := mul_pos hCS (Real.rpow_pos_of_pos hR slowExpHA.eA)
  have hB := mul_pos hCS (Real.rpow_pos_of_pos hR slowExpHA.eB)
  have hW := mul_pos hCS (Real.rpow_pos_of_pos hR slowExpHA.eW)
  have hJ := mul_pos hCS (Real.rpow_pos_of_pos hR slowExpHA.eJ)
  have h1 := mul_pos hCS hR
  have h2 := mul_pos hCS (pow_pos hR 2)
  simp only [Caps.Below, capsJImp, capsJ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The E6 fixed point: `Z = 48(4 + C_N² + C_π²) + 48 c_y (Tp + 5) + 1`. -/
def jointZ (CN Cp cy Tp : ℝ) : ℝ := 48 * (4 + CN ^ 2 + Cp ^ 2) + 48 * cy * (Tp + 5) + 1

/-- `K_P = Z^{β/2}`: at fixed `Tp` this is the constant of `A ≍ U`. -/
def jointKP (CN Cp cy Tp : ℝ) : ℝ := jointZ CN Cp cy Tp ^ (betaOf ((281 : ℝ) / 1000) / 2)

/-- `K_J = 8 C_N² + 4 K_P² + 2`. -/
def jointKJ (CN Cp cy Tp : ℝ) : ℝ := 2 * (4 * CN ^ 2 + 2 * jointKP CN Cp cy Tp ^ 2) + 2

/-- **The joint caps** `P_F = K_P U`, `y = 20 (C_b + 1) T`, `J_F = K_J U²`, slow constant
`CS Ex(c, R)`.  So `A B_* = T`-normalized: `W_* ≍ T²`, `y ≍ T`, `λ_* ≍ T²/P_F²`. -/
def capsJoint (CN Cp cy Cb CS c Tp X R : ℝ) : Caps :=
  capsJ (jointKP CN Cp cy Tp * jointU X) (20 * (Cb + 1) * jointT X R)
    (jointKJ CN Cp cy Tp * jointU X ^ 2) (CS * Ex c R) R

/-- `β = 1719/719`. -/
theorem betaOf_281 : betaOf ((281 : ℝ) / 1000) = 1719 / 719 := by norm_num [betaOf]

section Budget

variable {CN Cp cy Tp : ℝ}

theorem jointZ_ge (hcy : 0 ≤ cy) (hTp : 0 ≤ Tp) : 49 ≤ jointZ CN Cp cy Tp := by
  have h : 0 ≤ cy * (Tp + 5) := mul_nonneg hcy (by linarith)
  have e : 48 * cy * (Tp + 5) = 48 * (cy * (Tp + 5)) := by ring
  unfold jointZ
  rw [e]
  linarith only [sq_nonneg CN, sq_nonneg Cp, h]

/-- `K_P ≥ 49`. -/
theorem jointKP_ge (hcy : 0 ≤ cy) (hTp : 0 ≤ Tp) : 49 ≤ jointKP CN Cp cy Tp := by
  have hZ := jointZ_ge (CN := CN) (Cp := Cp) hcy hTp
  have hβ : (1 : ℝ) ≤ betaOf ((281 : ℝ) / 1000) / 2 := by rw [betaOf_281]; norm_num
  calc (49 : ℝ) ≤ jointZ CN Cp cy Tp := hZ
    _ = jointZ CN Cp cy Tp ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ jointKP CN Cp cy Tp :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hβ

theorem jointKJ_ge : 1 ≤ jointKJ CN Cp cy Tp := by
  unfold jointKJ
  nlinarith [sq_nonneg CN, sq_nonneg (jointKP CN Cp cy Tp)]

/-- **The E6 budget at the joint caps** (`peak_le`, `dissip_le`): with `N̄ ≤ C_N X`, `π ≤ C_π X`,
the incoming trace `2X` and the kinetic integral `Tp/8 + 5X²`, the peak is `≤ (P_F/2)²` and the
dissipation `≤ J_F/2`, at `P_F = K_P U`, `J_F = K_J U²`. -/
theorem fast_budget {X Nb pt : ℝ} (hX : 1 ≤ X) (hcy : 0 ≤ cy) (hTp : 0 ≤ Tp) (hNb0 : 0 ≤ Nb)
    (hNb : Nb ≤ CN * X) (hpt0 : 0 ≤ pt) (hpt : pt ≤ Cp * X) :
    peakSq ((281 : ℝ) / 1000) cy (1 / 4) (2 * X) (jointKP CN Cp cy Tp * jointU X)
        (Tp / 8 + 5 * X ^ 2) Nb pt ≤ (jointKP CN Cp cy Tp * jointU X / 2) ^ 2 ∧
      dissipSq ((281 : ℝ) / 1000) cy (1 / 4) (2 * X) (jointKP CN Cp cy Tp * jointU X)
        (Tp / 8 + 5 * X ^ 2) Nb pt ≤ jointKJ CN Cp cy Tp * jointU X ^ 2 / 2 := by
  have hσ : (0 : ℝ) < 281 / 1000 ∧ (281 : ℝ) / 1000 < 1 := by norm_num
  have hX0 : 0 < X := by linarith
  have hU : jointU X = X ^ betaOf ((281 : ℝ) / 1000) := by rw [betaOf_281]; rfl
  have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX
  have hIa : Tp / 8 + 5 * X ^ 2 ≤ (Tp + 5) * X ^ 2 := by
    have := mul_le_mul_of_nonneg_left hX2 hTp
    linarith only [this, hTp]
  have hIa0 : 0 ≤ Tp / 8 + 5 * X ^ 2 := by positivity
  have hpeak := peak_le (σ := (281 : ℝ) / 1000) (CN := CN) (Cp := Cp) (Z := jointZ CN Cp cy Tp)
    (Tp := Tp) hσ hX hcy hTp le_rfl hNb0 hNb hpt0 hpt hIa0 hIa
  rw [← hU] at hpeak
  have hd := dissip_le (σ := (281 : ℝ) / 1000) (Mf := 2 * X)
    (PF := jointKP CN Cp cy Tp * jointU X) (Nb := Nb) (pt := pt) (Ia := Tp / 8 + 5 * X ^ 2) hcy hIa0
  have hN2 : Nb ^ 2 ≤ CN ^ 2 * X ^ 2 := by
    have := pow_le_pow_left₀ hNb0 hNb 2
    rwa [mul_pow] at this
  have hXU : X ≤ jointU X := by
    have h : X ^ (1 : ℝ) ≤ X ^ ((1719 : ℝ) / 719) :=
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    rwa [Real.rpow_one] at h
  exact ⟨hpeak, dis_bound hd hpeak hN2 (pow_le_pow_left₀ hX0.le hXU 2)⟩

/-- The growth of `Z` from that of `Tp`. -/
theorem jointZ_le {CT E : ℝ} (hcy : 0 ≤ cy) (hE : 1 ≤ E) (hTp : Tp ≤ CT * E) :
    jointZ CN Cp cy Tp ≤ jointZ CN Cp cy CT * E := by
  have h1 : Tp + 5 ≤ (CT + 5) * E := by
    have e : (CT + 5) * E = CT * E + 5 * E := by ring
    rw [e]
    linarith
  have h2 : 48 * cy * (Tp + 5) ≤ 48 * cy * ((CT + 5) * E) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 0 ≤ 48 * (4 + CN ^ 2 + Cp ^ 2) := by positivity
  unfold jointZ
  nlinarith

end Budget

/-- The cap-scaling constant of the joint caps. -/
def jointK (CN Cp cy Cb CS CT : ℝ) : ℝ :=
  max (max (jointKP CN Cp cy CT) (20 * (Cb + 1)))
    (max (8 * CN ^ 2 + 4 * jointKP CN Cp cy CT ^ 2 + 2) (2 * CS))

/-- **The joint caps are scaled** (uniformly in `φ`): `CapsScaledJ K c` with `K = jointK …`, and
`c = c_S + c_T β` accounting for the slow polylog and the growth of `Tp`. -/
theorem capsJoint_scaled {R₀ X R CN Cp cy Cb CS cS Tp CT cT : ℝ} (hD : JDom R₀ X R) (hcy : 0 ≤ cy)
    (hCb : 0 ≤ Cb) (hcS : 0 ≤ cS) (hcT : 0 ≤ cT) (hCT : 0 ≤ CT) (hTp0 : 0 ≤ Tp)
    (hTp : Tp ≤ CT * Ex cT R) :
    CapsScaledJ (jointK CN Cp cy Cb CS CT) (cS + cT * betaOf ((281 : ℝ) / 1000)) X R
      (capsJoint CN Cp cy Cb CS cS Tp X R) := by
  set β := betaOf ((281 : ℝ) / 1000) with hβ
  have hβ0 : 0 < β := by rw [hβ, betaOf_281]; norm_num
  set K := jointK CN Cp cy Cb CS CT with hK
  set c := cS + cT * β with hc
  set KP := jointKP CN Cp cy Tp with hKP
  set K₁ := jointKP CN Cp cy CT with hK₁
  have hK₁K : K₁ ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hYK : 20 * (Cb + 1) ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hJK : 8 * CN ^ 2 + 4 * K₁ ^ 2 + 2 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hSK : 2 * CS ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hK1 : 49 ≤ K₁ := jointKP_ge hcy hCT
  have hKP1 : 49 ≤ KP := jointKP_ge hcy hTp0
  have hK0 : 1 ≤ K := by linarith
  have hE := hD.one_le_Ex hcT
  -- the two subpowers of `K_P`
  have hZ := jointZ_le (CN := CN) (Cp := Cp) hcy hE hTp
  have hKPle : KP ≤ K₁ * Ex (cT * (β / 2)) R := by
    have h0 : 0 ≤ jointZ CN Cp cy Tp := by linarith [jointZ_ge (CN := CN) (Cp := Cp) hcy hTp0]
    have h1 : 0 ≤ jointZ CN Cp cy CT := by linarith [jointZ_ge (CN := CN) (Cp := Cp) hcy hCT]
    calc KP ≤ (jointZ CN Cp cy CT * Ex cT R) ^ (β / 2) :=
          Real.rpow_le_rpow h0 hZ (by positivity)
      _ = K₁ * Ex (cT * (β / 2)) R := by
          rw [Real.mul_rpow h1 (Ex_pos _ _).le, Ex_rpow]
          rfl
  have hE₁ : Ex (cT * (β / 2)) R ≤ Ex c R := hD.Ex_le_Ex (by rw [hc]; nlinarith)
  have hE₂ : Ex (cT * β) R ≤ Ex c R := hD.Ex_le_Ex (by rw [hc]; linarith)
  have hE₃ : Ex cS R ≤ Ex c R := hD.Ex_le_Ex (by rw [hc]; nlinarith)
  have hEc : 1 ≤ Ex c R := hD.one_le_Ex (by rw [hc]; positivity)
  have hKP2 : KP ^ 2 ≤ K₁ ^ 2 * Ex (cT * β) R := by
    have h1 : 0 ≤ Ex (cT * (β / 2)) R := (Ex_pos _ _).le
    have h2 : Ex (cT * (β / 2)) R ^ 2 = Ex (cT * β) R := by
      rw [sq, ← Ex_add]
      congr 1
      ring
    calc KP ^ 2 ≤ (K₁ * Ex (cT * (β / 2)) R) ^ 2 := pow_le_pow_left₀ (by linarith) hKPle 2
      _ = K₁ ^ 2 * Ex (cT * β) R := by rw [mul_pow, h2]
  have hKJ : jointKJ CN Cp cy Tp ≤ K * Ex c R := by
    have h1 : 1 ≤ Ex (cT * β) R := hD.one_le_Ex (by positivity)
    have h2 : jointKJ CN Cp cy Tp ≤ (8 * CN ^ 2 + 4 * K₁ ^ 2 + 2) * Ex (cT * β) R := by
      unfold jointKJ
      nlinarith [sq_nonneg CN, sq_nonneg K₁]
    calc jointKJ CN Cp cy Tp ≤ (8 * CN ^ 2 + 4 * K₁ ^ 2 + 2) * Ex (cT * β) R := h2
      _ ≤ K * Ex c R := mul_le_mul hJK hE₂ (Ex_pos _ _).le (by linarith)
  have hKPK : KP ≤ K * Ex c R :=
    hKPle.trans (mul_le_mul hK₁K hE₁ (Ex_pos _ _).le (by linarith))
  have hKJ1 := jointKJ_ge (CN := CN) (Cp := Cp) (cy := cy) (Tp := Tp)
  have hU0 : 0 < jointU X := by linarith [hD.one_lt_U]
  have hT0 := hD.T_pos
  have hK00 : 0 < K := by linarith
  have hCSEx : ∀ x : ℝ, 2 * (CS * Ex cS R) * R ^ x ≤ K * Ex c R * R ^ x := fun x ↦ by
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hD.R_pos.le _)
    calc 2 * (CS * Ex cS R) = 2 * CS * Ex cS R := by ring
      _ ≤ K * Ex c R := mul_le_mul hSK hE₃ (Ex_pos _ _).le (by linarith)
  have hCS1 : 2 * (CS * Ex cS R) * R ≤ K * Ex c R * R := by
    simpa [Real.rpow_one] using hCSEx 1
  have hCS2 : 2 * (CS * Ex cS R) * R ^ 2 ≤ K * Ex c R * R ^ 2 := by
    simpa [Real.rpow_two] using hCSEx 2
  have hdiv : ∀ {a v : ℝ}, 0 < v → 1 ≤ a → v / K ≤ a * v := fun {a v} hv ha ↦ by
    rw [div_le_iff₀ hK00]
    have h1 : 1 ≤ a * K := one_le_mul_of_one_le_of_one_le ha hK0
    nlinarith
  refine ⟨⟨hdiv hU0 (by linarith), ?_⟩, ⟨hdiv hT0 (by linarith), ?_⟩,
    ⟨hdiv (by positivity) hKJ1, ?_⟩, hCSEx _, hCSEx _, hCSEx _, hCSEx _, hCS1, hCS1, hCS2⟩
  · exact mul_le_mul_of_nonneg_right hKPK hU0.le
  · refine mul_le_mul_of_nonneg_right ?_ hT0.le
    calc 20 * (Cb + 1) ≤ K := hYK
      _ ≤ K * Ex c R := le_mul_of_one_le_right hK00.le hEc
  · exact mul_le_mul_of_nonneg_right hKJ (by positivity)

/-! ### (c) All thresholds paid -/

/-- **All thresholds paid** (R1 at the joint scale; `thresholds_paid` of the fixed force): for every
cap-scaling constant there are absolute `C, C₀, R₀` such that the trial `C Q Ex(C₀, R)` pays, for
every larger `q`, the four thresholds (`JointBelow`, with the rows 2, 3 of Table quant-metric and
the raised floor paid by `JointInterfaces.below₂Full`, `belowSFull`) and the near roles (`near_pay`,
from `JointProfiles` and `LeadBelow`).  Here is the origin of `Ex`: at the tie the near moment
forces `C₀ ≥ 2(c' + 4 c_n)`. -/
theorem thresholds_paid_joint {D : JointData} (hD : JointInterfaces D) {K c : ℝ} (hK : 1 ≤ K)
    (hc : 0 ≤ c) :
    ∃ C C₀ R₀ : ℝ, 1 ≤ C ∧ 1 ≤ C₀ ∧ 0 < R₀ ∧ ∀ X R : ℝ, JDom R₀ X R → ∀ caps : Caps,
      CapsScaledJ K c X R caps → ∀ q : ℝ, C * jointQ X R * Ex C₀ R ≤ q →
        D.q₀ X R caps ≤ q ∧ D.q₁ X R caps ≤ q ∧ D.q₂Full X R caps ≤ q ∧ D.qSFull X R caps ≤ q ∧
          D.near X R caps q := by
  obtain ⟨C0, B0, R0, h0⟩ := hD.below₀ K c hK hc
  obtain ⟨C1, B1, R1, h1⟩ := hD.below₁ K c hK hc
  obtain ⟨C2, B2, R2, h2⟩ := hD.below₂Full K c hK hc
  obtain ⟨C3, B3, R3, h3⟩ := hD.belowSFull K c hK hc
  obtain ⟨Cl, bl, Rl, hl⟩ := hD.leadN K c hK hc
  obtain ⟨Cm, bm, Rm, hm⟩ := hD.leadP K c hK hc
  obtain ⟨cn, Cn, qn, hcn, hCn, hprof⟩ := hD.profiles
  set Cl' := max Cl 0 with hCl'
  set Cm' := max Cm 0 with hCm'
  have hCl0 : 0 ≤ Cl' := le_max_right _ _
  have hCm0 : 0 ≤ Cm' := le_max_right _ _
  set C : ℝ := 1 + (max C0 0 + max C1 0 + max C2 0 + max C3 0) + (Cl' * Cn) ^ 2 +
    (Cm' * Cn) ^ 3 with hC
  have hn0 : 0 ≤ max C0 0 := le_max_right _ _
  have hn1 : 0 ≤ max C1 0 := le_max_right _ _
  have hn2 : 0 ≤ max C2 0 := le_max_right _ _
  have hn3 : 0 ≤ max C3 0 := le_max_right _ _
  have hn4 : 0 ≤ (Cl' * Cn) ^ 2 := sq_nonneg _
  have hn5 : 0 ≤ (Cm' * Cn) ^ 3 := pow_nonneg (mul_nonneg hCm0 hCn) 3
  have hC1 : 1 ≤ C := by rw [hC]; linarith
  have hC0' : 0 < C := by linarith
  set C₀ : ℝ := 1 + (|B0| + |B1| + |B2| + |B3|) + 2 * (|bl| + 4 * cn) + 3 * (|bm| + 4 * cn)
    with hC₀
  have ha0 := abs_nonneg B0
  have ha1 := abs_nonneg B1
  have ha2 := abs_nonneg B2
  have ha3 := abs_nonneg B3
  have ha4 := abs_nonneg bl
  have ha5 := abs_nonneg bm
  have hC₀1 : 1 ≤ C₀ := by rw [hC₀]; linarith
  set B : ℝ := 3 * cn + 4 * C₀ with hB
  set R₀ : ℝ := 1 + (|R0| + |R1| + |R2| + |R3| + |Rl| + |Rm| + |qn|) + C ^ (4 : ℝ) +
    Real.exp (Real.exp B) with hR₀
  have hb0 := abs_nonneg R0
  have hb1 := abs_nonneg R1
  have hb2 := abs_nonneg R2
  have hb3 := abs_nonneg R3
  have hb4 := abs_nonneg Rl
  have hb5 := abs_nonneg Rm
  have hb6 := abs_nonneg qn
  have hb7 : 0 ≤ C ^ (4 : ℝ) := Real.rpow_nonneg hC0'.le _
  have hb8 := Real.exp_pos (Real.exp B)
  refine ⟨C, C₀, R₀, hC1, hC₀1, by rw [hR₀]; linarith, ?_⟩
  intro X R hdom caps hcaps q hq
  have hRR : R₀ ≤ R := hdom.R₀_le
  have hd : ∀ {x : ℝ}, x ≤ |x| → |x| ≤ R₀ → JDom x X R := fun hx hx' ↦
    hdom.mono (hx.trans hx')
  have hE (a : ℝ) : 0 ≤ Ex a R := (Ex_pos _ _).le
  have hQ0 := (hdom.Q_pos).le
  have hll : B ≤ Real.log (Real.log R) := le_loglog (by rw [hR₀] at hRR; linarith)
  have hcn3 : 3 * cn ≤ Real.log (Real.log R) := by rw [hB] at hll; linarith
  have hC₀4 : 4 * C₀ ≤ Real.log (Real.log R) := by rw [hB] at hll; linarith
  have hExC₀1 : 1 ≤ Ex C₀ R := hdom.one_le_Ex (by linarith)
  -- paying one `JointBelow` threshold
  have pay : ∀ {C' B' x : ℝ}, max C' 0 ≤ C → |B'| ≤ C₀ → x ≤ C' * jointQ X R * Ex B' R → x ≤ q := by
    intro C' B' x hC' hB' hx
    refine hx.trans (le_trans ?_ hq)
    calc C' * jointQ X R * Ex B' R ≤ C * jointQ X R * Ex B' R :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hC') hQ0)
            (hE _)
      _ ≤ C * jointQ X R * Ex C₀ R :=
          mul_le_mul_of_nonneg_left (hdom.Ex_le_Ex ((le_abs_self _).trans hB')) (by positivity)
  have hp0 := h0 X R (hd (le_abs_self _) (by rw [hR₀]; linarith)) caps hcaps
  have hp1 := h1 X R (hd (le_abs_self _) (by rw [hR₀]; linarith)) caps hcaps
  have hp2 := h2 X R (hd (le_abs_self _) (by rw [hR₀]; linarith)) caps hcaps
  have hp3 := h3 X R (hd (le_abs_self _) (by rw [hR₀]; linarith)) caps hcaps
  obtain ⟨hlo, hlu⟩ := hl X R (hd (le_abs_self _) (by rw [hR₀]; linarith)) caps hcaps
  obtain ⟨hmo, hmu⟩ := hm X R (hd (le_abs_self _) (by rw [hR₀]; linarith)) caps hcaps
  -- the near payment
  have hR1 := hdom.one_lt_R
  have hlR := hdom.one_lt_log
  have hTrl : R ≤ C * jointQ X R * Ex C₀ R := by
    have h1 : 1 ≤ C * Ex C₀ R := one_le_mul_of_one_le_of_one_le hC1 hExC₀1
    calc R ≤ jointQ X R := hdom.R_le_Q
      _ ≤ (C * Ex C₀ R) * jointQ X R := le_mul_of_one_le_left hQ0 h1
      _ = C * jointQ X R * Ex C₀ R := by ring
  have hTru : C * jointQ X R * Ex C₀ R ≤ R ^ 4 := by
    refine hdom.trial_le (hE _) ?_ (Ex_le_rpow hR1 hdom.loglog_pos (by linarith))
    refine le_rpow_of_large (by linarith) (by norm_num) ?_
    have e : (1 : ℝ) / (1 / 4) = 4 := by norm_num
    rw [e]
    rw [hR₀] at hRR
    linarith
  have hqn : qn ≤ q := by
    have h1 : qn ≤ R := (le_abs_self qn).trans (by rw [hR₀] at hRR; linarith)
    exact h1.trans (hTrl.trans hq)
  obtain ⟨hN, hP⟩ := hprof q hqn
  have hN' : D.N q ≤ Cn * q ^ (-((1 : ℝ) / 2)) * Ex cn q := by
    have e : (-(1 : ℝ) / 2) = -(1 / 2) := by ring
    rwa [e] at hN
  have hP' : D.P q ≤ Cn * q ^ (-((1 : ℝ) / 3)) * Ex cn q := by
    have e : (-(1 : ℝ) / 3) = -(1 / 3) := by ring
    rwa [e] at hP
  have hCa2 : Cl' * Cn ≤ C ^ ((1 : ℝ) / 2) := by
    have h := le_rpow_of_pow_le (A := Cl' * Cn) (C := C) (n := 2) (by norm_num)
      (mul_nonneg hCl0 hCn) (by rw [hC]; linarith)
    simpa using h
  have hCa3 : Cm' * Cn ≤ C ^ ((1 : ℝ) / 3) := by
    have h := le_rpow_of_pow_le (A := Cm' * Cn) (C := C) (n := 3) (by norm_num)
      (mul_nonneg hCm0 hCn) (by rw [hC]; linarith)
    simpa using h
  have hl' : D.LN X R caps ≤ Cl' * jointQ X R ^ ((1 : ℝ) / 2) * Ex bl R :=
    hlu.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hQ0 _)) (hE _))
  have hm' : D.LP X R caps ≤ Cm' * jointQ X R ^ ((1 : ℝ) / 3) * Ex bm R :=
    hmu.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hQ0 _)) (hE _))
  have hbl := le_abs_self bl
  have hbm := le_abs_self bm
  refine ⟨pay (by rw [hC]; linarith) (by rw [hC₀]; linarith) hp0,
    pay (by rw [hC]; linarith) (by rw [hC₀]; linarith) hp1,
    pay (by rw [hC]; linarith) (by rw [hC₀]; linarith) hp2,
    pay (by rw [hC]; linarith) (by rw [hC₀]; linarith) hp3, ?_, ?_⟩
  · exact near_pay (a := 1 / 2) (by norm_num) hCl0 hCn hcn hC0' hdom.Q_pos hR1 hlR
      (by linarith) hTrl hTru hCa2 (by rw [hC₀]; linarith) hq hlo hl' hN'
  · exact near_pay (a := 1 / 3) (by norm_num) hCm0 hCn hcn hC0' hdom.Q_pos hR1 hlR
      (by linarith) hTrl hTru hCa3 (by rw [hC₀]; linarith) hq hmo hm' hP'

/-! ### (d) Strict improvement -/

/-- `OnPrefix` restricts to any sub-interval. -/
theorem onPrefix_restrict {caps : Caps} {r : ℝ} {g : Field} {y : ℝ → Field} {s t a b : ℝ}
    (h : OnPrefix caps r g y s t) (hsa : s ≤ a) (hab : a ≤ b) (hbt : b ≤ t)
    (hf : ContinuousOn (fastNorm 2 r g y) (Icc s t))
    (hS : ContinuousOn (slowNorm 2 r g y) (Icc s t)) : OnPrefix caps r g y a b := by
  have hst : s ≤ t := hsa.trans (hab.trans hbt)
  have hsub : ∀ {u : ℝ}, u ∈ Icc a b → u ∈ Icc s t := fun hu ↦ ⟨hsa.trans hu.1, hu.2.trans hbt⟩
  refine ⟨fun u hu ↦ h.1 u (hsub hu), ?_, ?_, fun u hu ↦ h.2.2.2 u (hsub hu)⟩
  · refine le_trans ?_ h.2.1
    exact intervalIntegral.integral_mono_interval hsa hab hbt
      (Filter.Eventually.of_forall fun u ↦ sq_nonneg _) ((hf.pow 2).intervalIntegrable_of_Icc hst)
  · refine le_trans ?_ h.2.2.1
    exact intervalIntegral.integral_mono_interval hsa hab hbt
      (Filter.Eventually.of_forall fun u ↦ sq_nonneg _) ((hS.pow 2).intervalIntegrable_of_Icc hst)

/-- **The history is regained on the last unit, with no analysis**: `Tp ≥ 3` puts `[v − 1, v]`
inside `[s + 1, t]`, where the caps hold by restriction and the levels by the last clause of
E7-P. -/
theorem slowHistory_regained {caps : Caps} {L' : Fin 5 → ℝ} {R Tp : ℝ} {r : ℝ} {g : Field}
    {y : ℝ → Field} {s t v : ℝ} (hs : 0 ≤ s) (hTp : 3 ≤ Tp) (hon : OnPrefix caps r g y s t)
    (hf : ContinuousOn (fastNorm 2 r g y) (Icc s t))
    (hS : ContinuousOn (slowNorm 2 r g y) (Icc s t))
    (hL : ∀ u ∈ Icc (s + 1) t, SlowLevel L' R slowExpHA r g y u)
    (hv : v ∈ Icc (s + Tp - 1) t) : SlowHistory caps L' R r g y v := by
  have hv1 : 1 ≤ v := by linarith [hv.1]
  have e : max 0 (v - 1) = v - 1 := max_eq_right (by linarith)
  refine ⟨?_, fun u hu ↦ hL u ?_⟩
  · rw [e]
    exact onPrefix_restrict hon (by linarith [hv.1]) (by linarith) hv.2 hf hS
  · rw [e] at hu
    exact ⟨by linarith [hu.1, hv.1], hu.2.trans hv.2⟩

/-- The history at the true zero: the datum is a good point, and the clipped backward unit is the
point `0`. -/
theorem slowHistory_zero {Mf : ℝ} {caps ci : Caps} {PF yF JF CS R : ℝ} {L' : Fin 5 → ℝ} {r : ℝ}
    {g : Field} {y : ℝ → Field} (hlt : ci.Below caps)
    (hgood : GoodPoint Mf (capsJStart PF yF JF CS R L') ci r g y 0) :
    SlowHistory caps L' R r g y 0 := by
  have e : max 0 ((0 : ℝ) - 1) = 0 := max_eq_left (by norm_num)
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := hlt
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hgood.pointCaps
  have hpc : PointCaps caps r g y 0 := ⟨a1.trans p1.le, a2.trans p2.le, a3.trans p3.le,
    a4.trans p4.le, a5.trans p5.le, a6.trans p10.le, a7.trans p11.le, a8.trans p12.le⟩
  obtain ⟨-, -, b3, b4, -, b6, b7, b8⟩ := hgood.start
  refine ⟨?_, fun u hu ↦ ?_⟩
  · rw [e]
    exact onPrefix_point hpc (p8.trans p6.le) (p9.trans p7.le)
  · rw [e] at hu
    rw [show u = 0 from le_antisymm hu.2 hu.1]
    exact ⟨b6, b7, b8, b3, b4⟩

/-- The start levels are at least one. -/
theorem one_le_levelsJ {L : Fin 5 → ℝ} {e : ℝ} (hL : ∀ i, 1 ≤ L i) (he : 1 ≤ e) (i : Fin 5) :
    1 ≤ levelsJ L e i := by
  unfold levelsJ
  split_ifs
  · exact hL i
  · exact one_le_mul_of_one_le_of_one_le (hL i) he

/-- **Strict improvement along a solution** (E7-P + E4 + E5-J + E6 + E8-J + E10), in the chronology
of the TeX: the slow caps first (`hSl`), which also feed `M_∞` and `Sl` forward; the kinetic budget
`I_a = Tp/8 + 5X²` (`hW0`, along the functional of E4-J); the `H¹` peak and dissipation; the guard
and the `H²` barrier.  The start predicate is the backward-unit history (`SlowHistory`), regained by
`slowHistory_regained`. -/
theorem strictOn_joint {σ Cs CG m₀ Tp X φ cy Cb Nb pt Minf CSl Thr PF yF JF CS R : ℝ}
    {L' : Fin 5 → ℝ} {q₀ q₁ q₂ qS Bs : Caps → ℝ} {near : Caps → ℝ → Prop}
    {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} (hσ : 0 < σ ∧ σ < 1)
    (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4) (hCG : 0 ≤ CG)
    (hE1 : H1EnergyJoint σ Cs X φ Tp Nb pt Minf q₁ near Sl)
    (hE2 : H2EnergyInterfaceB σ CG X φ Tp m₀ Minf Bs q₂ near Sl)
    {r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} (hsol : ActualSol X φ r g y Ty) {W0 : ℝ → ℝ}
    (hW0 : KinFunOn X q₀ (fun u ↦ slowSup r g y u ≤ Minf) r g y Ty W0)
    (hSl : ∀ s t : ℝ, PieceHyp Tp qS r g y Ty (capsJ PF yF JF CS R) s t →
      SlowHistory (capsJ PF yF JF CS R) L' R r g y s →
      (∀ u ∈ Icc s t, SlowLevel (fun _ ↦ CSl) R slowExpHA r g y u ∧
        slowWiener r g y u ≤ CSl * R ^ slowExpHA.eW ∧ slowSup r g y u ≤ Minf) ∧
      (∫ u in s..t, slowNorm 2 r g y u ^ 2) ≤ CSl * R ^ slowExpHA.eJ ∧
      Sl r g y s t ∧ ∀ v ∈ Icc (s + 1) t, SlowLevel L' R slowExpHA r g y v)
    (hCSl : CSl ≤ CS) (hR : 0 < R) (hcy0 : 0 ≤ cy)
    (hcy : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Cs * a ^ (3 - σ) * b ^ σ ≤ 1 / 4 * b ^ 2 + cy * a ^ (4 - 2 / betaOf σ))
    (hCb : 0 ≤ Cb) (hbar : BarrierProp m₀ Cb) (hTp : 3 ≤ Tp) (hPF : 0 < PF) (hyF : 0 ≤ yF)
    (hpeak : peakSq σ cy (1 / 4) (2 * X) PF (Tp / 8 + 5 * X ^ 2) Nb pt ≤ (PF / 2) ^ 2)
    (hdis : dissipSq σ cy (1 / 4) (2 * X) PF (Tp / 8 + 5 * X ^ 2) Nb pt ≤ JF / 2)
    (hB : 1 ≤ Bs (capsJ PF yF JF CS R)) (hguard : CG * PF ≤ Bs (capsJ PF yF JF CS R))
    (hCW : Cb * WStar 1 PF (Bs (capsJ PF yF JF CS R)) ≤ yF ^ 2 / 100)
    (hthr : ∀ q : ℝ, Thr ≤ q → q₀ (capsJ PF yF JF CS R) ≤ q ∧ q₁ (capsJ PF yF JF CS R) ≤ q ∧
      q₂ (capsJ PF yF JF CS R) ≤ q ∧ qS (capsJ PF yF JF CS R) ≤ q ∧
      near (capsJ PF yF JF CS R) q) :
    StrictOn (2 * X) Tp (fun _ ↦ Thr) (capsJ PF yF JF CS R) (capsJImp PF yF JF CS R)
      (capsJStart PF yF JF CS R L') (SlowHistory (capsJ PF yF JF CS R) L' R r g y)
      (fun u ↦ slowSup r g y u ≤ Minf) r g y Ty := by
  intro s t hgood hLev hpiece
  set caps := capsJ PF yF JF CS R with hcaps
  have hs := hpiece.hs
  have hst := hpiece.hst
  have ht := hpiece.ht
  have hon := hpiece.onPrefix
  obtain ⟨h0, h1, h2, h3, hnear⟩ := hthr |r| hpiece.thr
  have mk : ∀ {q : Caps → ℝ}, q caps ≤ |r| → PieceHyp Tp q r g y Ty caps s t :=
    fun h ↦ ⟨⟨hs, hst, ht, h, hon⟩, hpiece.len⟩
  obtain ⟨c1, c2, -, c4', -⟩ := norms_continuous hsol (b := t) (hs.trans hst) ht
  have hsub : Icc s t ⊆ Icc 0 t := Icc_subset_Icc hs le_rfl
  -- the slow caps first
  obtain ⟨hsl, hslJ, hslO, hslP⟩ := hSl s t (mk h3) hLev
  have mkJ : ∀ {q : Caps → ℝ}, q caps ≤ |r| → JointPiece Tp Minf q near Sl r g y Ty caps s t :=
    fun h ↦ ⟨mk h, fun u hu ↦ (hsl u hu).2.2, hslO, hnear⟩
  -- kinetic budget, on the prefix where E7-P has just bounded `M_∞`
  obtain ⟨k1, -, k3, -⟩ := hW0 caps s t ⟨hs, hst, ht, h0, hon⟩ fun u hu ↦ (hsl u hu).2.2
  have hsT : ENNReal.ofReal s < Ty := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) ht
  have ha0 : fastNorm 0 r g y s ≤ fastNorm 1 r g y s :=
    hnorm_mono (by norm_num) (((actual_mz hsol hs hsT).inH.mono (by norm_num)).PiF)
  have hWs : W0 s ≤ 5 * X ^ 2 := by
    have h := (k1 s ⟨le_rfl, hst⟩).2
    have h' : fastNorm 0 r g y s ^ 2 ≤ (2 * X) ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg _ _) (ha0.trans hgood.fastH1) 2
    nlinarith
  have hWt : 0 ≤ W0 t := le_trans (by positivity) (k1 t ⟨hst, le_rfl⟩).1
  have hkin : (∫ u in s..t, fastNorm 1 r g y u ^ 2) ≤ Tp / 8 + 5 * X ^ 2 := by
    have := hpiece.len
    linarith
  -- the `H¹` energy
  have hcapF : ∀ u ∈ Icc s t, fastNorm 1 r g y u ≤ PF := fun u hu ↦ (hon.1 u hu).1
  have hout1 := hE1 r g y Ty caps s t hsol (mkJ h1)
  have hpk := scalar_peak_of_output hσ hst hout1 hcapF ⟨by norm_num, by norm_num⟩ hcy0 hcy
    hkin hgood.fastH1 (c1.mono hsub) (c2.mono hsub)
  have hds := scalar_dissipation_of_output hσ hst hout1 hcapF ⟨by norm_num, by norm_num⟩ hcy0 hcy
    hkin hgood.fastH1 (c1.mono hsub) (c2.mono hsub)
  -- the guard and the `H²` energy
  have hg : ∀ u ∈ Icc s t, CG * fastNorm σ r g y u ≤ Bs caps := fun u hu ↦ by
    have hu0 : 0 ≤ u := hs.trans hu.1
    have huT : ENNReal.ofReal u < Ty := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) ht
    have h' : fastNorm σ r g y u ≤ fastNorm 1 r g y u :=
      hnorm_mono hσ.2.le (((actual_mz hsol hu0 huT).inH.mono (by norm_num)).PiF)
    exact (mul_le_mul_of_nonneg_left (h'.trans (hcapF u hu)) hCG).trans hguard
  have hout2 := hE2 r g y Ty caps s t hsol (mkJ h2) hg
  obtain ⟨hb1, hb2⟩ := fast_H2_of_output hout2 hm₀ hCb hbar hsol hs hst ht hcapF
    (fun u hu ↦ (hon.1 u hu).2.1) hPF hB hyF hCW hgood.start.2.1
  have hC : ∀ x : ℝ, CSl * R ^ x ≤ CS * R ^ x := fun x ↦
    mul_le_mul_of_nonneg_right hCSl (Real.rpow_nonneg hR.le _)
  have hC1 : CSl * R ≤ CS * R := mul_le_mul_of_nonneg_right hCSl hR.le
  have hC2 : CSl * R ^ 2 ≤ CS * R ^ 2 := mul_le_mul_of_nonneg_right hCSl (sq_nonneg _)
  have haF : ∀ u ∈ Icc s t, fastNorm 1 r g y u ≤ PF / 2 := fun u hu ↦ by
    have h := (hpk u hu).trans hpeak
    exact (pow_le_pow_iff_left₀ (hnorm_nonneg _ _) (by positivity) (by norm_num)).1 h
  refine ⟨⟨fun u hu ↦ ⟨haF u hu, hb1 u hu, (hsl u hu).1.2.2.2.1.trans (hC _),
    (hsl u hu).1.2.2.2.2.trans (hC _), (hsl u hu).2.1.trans (hC _)⟩, hds.trans hdis,
    hslJ.trans (hC _), fun u hu ↦ ⟨(hsl u hu).1.1.trans hC1, (hsl u hu).1.2.1.trans hC1,
    (hsl u hu).1.2.2.1.trans hC2⟩⟩, fun u hu ↦ (hsl u hu).2.2, fun v hv ↦ ?_⟩
  have hv1 : v ∈ Icc (s + 1) t := ⟨by linarith [hv.1], hv.2⟩
  have hv' : v ∈ Icc s t := ⟨by linarith [hv.1], hv.2⟩
  obtain ⟨p0, p1, p2, p3, p4⟩ := hslP v hv1
  exact ⟨⟨haF v hv', hb2 v hv1, p3, p4, (hsl v hv').2.1.trans (hC _), p0, p1, p2⟩,
    slowHistory_regained hs hTp hon (c2.mono hsub) (c4'.mono hsub) hslP hv⟩

/-- **The start of the bootstrap**: the datum in the `X`-ball is a good point (`ψ(0) = 0`). -/
theorem goodPoint_zero {r X R PF yF JF CS : ℝ} {L' : Fin 5 → ℝ} {g v₀ : Field} {y : ℝ → Field}
    (hy0 : y 0 = v₀) (hv : Adm 2 v₀) (hvX : hnorm 2 v₀ ≤ X) (hX : 0 ≤ X) (hXR : X ≤ R)
    (hR : 1 ≤ R) (hPF : 2 * X ≤ PF / 2) (hyF : 2 * X ≤ 4 / 5 * yF) (hCS : c4 ≤ CS)
    (hCS1 : 1 ≤ CS) (hL : ∀ i, 1 ≤ L' i) :
    GoodPoint (2 * X) (capsJStart PF yF JF CS R L') (capsJImp PF yF JF CS R) r g y 0 := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := norms_at_zero (r := r) (g := g) hy0 hv hvX
  have hR0 : 0 < R := by linarith
  have hpow : ∀ x : ℝ, 1 ≤ x → X ≤ R ^ x := fun x hx ↦ by
    calc X ≤ R := hXR
      _ = R ^ (1 : ℝ) := (Real.rpow_one R).symm
      _ ≤ R ^ x := Real.rpow_le_rpow_of_exponent_le hR hx
  have hsq : X ≤ R ^ 2 := hXR.trans (le_self_pow₀ hR (by norm_num))
  have hL' : ∀ (i) (B : ℝ), X ≤ B → 0 ≤ B → X ≤ L' i * B := fun i B hB hB0 ↦
    hB.trans (le_mul_of_one_le_left hB0 (hL i))
  have hC' : ∀ B : ℝ, X ≤ B → 0 ≤ B → X ≤ CS * B := fun B hB hB0 ↦
    hB.trans (le_mul_of_one_le_left hB0 hCS1)
  have hP : ∀ x : ℝ, 0 ≤ R ^ x := fun x ↦ Real.rpow_nonneg hR0.le x
  have hc4 : c4 * X ≤ CS * R ^ slowExpHA.eW := by
    calc c4 * X ≤ CS * X := mul_le_mul_of_nonneg_right hCS hX
      _ ≤ CS * R ^ slowExpHA.eW :=
        mul_le_mul_of_nonneg_left (hpow _ (by norm_num [slowExpHA])) (by linarith)
  refine ⟨le_rfl, by linarith, ?_, ?_⟩
  · simp only [PointCaps, capsJStart]
    exact ⟨z1.trans (by linarith), z2.trans (by linarith),
      z3.trans (hL' 3 _ (hpow _ (by norm_num [slowExpHA])) (hP _)),
      z4.trans (hL' 4 _ (hpow _ (by norm_num [slowExpHA])) (hP _)), z5.trans hc4,
      z6.trans (hL' 0 _ hXR hR0.le), z7.trans (hL' 1 _ hXR hR0.le),
      z8.trans (hL' 2 _ hsq (sq_nonneg _))⟩
  · simp only [PointCaps, capsJImp]
    exact ⟨z1.trans (by linarith), z2.trans (by linarith),
      z3.trans (hC' _ (hpow _ (by norm_num [slowExpHA])) (hP _)),
      z4.trans (hC' _ (hpow _ (by norm_num [slowExpHA])) (hP _)), z5.trans hc4,
      z6.trans (hC' _ hXR hR0.le), z7.trans (hC' _ hXR hR0.le),
      z8.trans (hC' _ hsq (sq_nonneg _))⟩

/-! ### (e) The joint theorem -/

/-- `C_b W_* ≤ y²/100` at `y = 20 (C_b + 1) T`, `B_* = T/P_F`. -/
theorem cw_joint {Cb T PF : ℝ} (hCb : 0 ≤ Cb) (hPF : PF ≠ 0) :
    Cb * WStar 1 PF (T / PF) ≤ (20 * (Cb + 1) * T) ^ 2 / 100 := by
  rw [WStar_jointBs hPF]
  have h : Cb * (297 / 128) ≤ 4 * (Cb + 1) ^ 2 := by nlinarith [sq_nonneg Cb]
  calc Cb * (297 / 128 * T ^ 2) = Cb * (297 / 128) * T ^ 2 := by ring
    _ ≤ 4 * (Cb + 1) ^ 2 * T ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg T)
    _ = (20 * (Cb + 1) * T) ^ 2 / 100 := by ring

/-- **The bootstrap at one radius pair**, the constants being given: the caps `capsJoint` close
(`fast_budget`, `cw_joint`, the guards), `strictOn_joint` holds along every solution, and
`global_of_strictOn` applies. -/
theorem joint_at {D : JointData} (hD : JointInterfaces D) {CN Cp cy Cb CS₁ Thr X R : ℝ}
    (hcy0 : 0 ≤ cy) (hcy : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      D.Cs * a ^ (3 - (281 : ℝ) / 1000) * b ^ ((281 : ℝ) / 1000) ≤
        1 / 4 * b ^ 2 + cy * a ^ (4 - 2 / betaOf ((281 : ℝ) / 1000)))
    (hCb0 : 0 ≤ Cb) (hbar : BarrierProp D.m₀ Cb) (hCS₁ : D.CS ≤ CS₁) (hc4₁ : c4 ≤ CS₁)
    (hdom : JDom D.R₀ X R) (hNb : D.Nbar X R ≤ CN * X) (hpt : D.piTol X R ≤ Cp * X)
    (hguards : D.CG * (jointKP CN Cp cy (D.Tp X R) * jointU X) ≤
        jointT X R / (jointKP CN Cp cy (D.Tp X R) * jointU X) ∧
      jointKP CN Cp cy (D.Tp X R) * jointU X ≤ jointT X R)
    (hthr : ∀ q : ℝ, Thr ≤ q → D.q₀ X R (capsJoint CN Cp cy Cb CS₁ D.cS (D.Tp X R) X R) ≤ q ∧
      D.q₁ X R (capsJoint CN Cp cy Cb CS₁ D.cS (D.Tp X R) X R) ≤ q ∧
      D.q₂Full X R (capsJoint CN Cp cy Cb CS₁ D.cS (D.Tp X R) X R) ≤ q ∧
      D.qSFull X R (capsJoint CN Cp cy Cb CS₁ D.cS (D.Tp X R) X R) ≤ q ∧
      D.near X R (capsJoint CN Cp cy Cb CS₁ D.cS (D.Tp X R) X R) q)
    {r : ℝ} {g v₀ : Field} (hg : Adm 2 g) (hgφ : hnorm 2 g ≤ R - X) (hv : Adm 2 v₀)
    (hvX : hnorm 2 v₀ ≤ X) (hr : Thr ≤ |r|) :
    ∃ y : ℝ → Field, IsHeatSol (filtN r 0) (filtG r 0 g) ⊤ y ∧ y 0 = v₀ ∧
      ∀ t, 0 ≤ t → hnorm 2 (y t) ≤ (capsJoint CN Cp cy Cb CS₁ D.cS (D.Tp X R) X R).yF +
        (capsJoint CN Cp cy Cb CS₁ D.cS (D.Tp X R) X R).BS + 4 * (R - X) := by
  have hσ : (0 : ℝ) < 281 / 1000 ∧ (281 : ℝ) / 1000 < 1 := by norm_num
  have hTp3 : 3 ≤ D.Tp X R := hD.Tp_ge X R hdom
  have hTp2 : 2 ≤ D.Tp X R := by linarith
  have hX1 : 1 ≤ X := hdom.one_lt_X.le
  have hX0 : 0 < X := by linarith
  have hR0 := hdom.R_pos
  set Tp := D.Tp X R with hTpd
  set KP := jointKP CN Cp cy Tp with hKP
  set PF := KP * jointU X with hPFd
  set yF := 20 * (Cb + 1) * jointT X R with hyFd
  set JF := jointKJ CN Cp cy Tp * jointU X ^ 2 with hJFd
  set CS := CS₁ * Ex D.cS R with hCSd
  have hKP49 : 49 ≤ KP := jointKP_ge hcy0 (by linarith)
  have hU1 := hdom.one_lt_U
  have hPF0 : 0 < PF := mul_pos (by linarith) (by linarith)
  have hT0 := hdom.T_pos
  have hyF0 : 0 < yF := mul_pos (by linarith) hT0
  have hKJ1 := jointKJ_ge (CN := CN) (Cp := Cp) (cy := cy) (Tp := Tp)
  have hJF0 : 0 < JF := mul_pos (by linarith) (by positivity)
  have hEx1 : 1 ≤ Ex D.cS R := hdom.one_le_Ex hD.cS_nonneg
  have hCS1 : 1 ≤ CS₁ := hD.CS_ge.trans hCS₁
  have hCS0 : 1 ≤ CS := one_le_mul_of_one_le_of_one_le hCS1 hEx1
  obtain ⟨hpeak, hdis⟩ := fast_budget (CN := CN) (Cp := Cp) (Tp := Tp) (Nb := D.Nbar X R)
    (pt := D.piTol X R) hX1 hcy0 (by linarith) (hD.Nbar_nonneg X R hdom) hNb
    (hD.piTol_nonneg X R hdom) hpt
  have hBs : jointBs X R (capsJ PF yF JF CS R) = jointT X R / PF := rfl
  have hCW : Cb * WStar 1 PF (jointBs X R (capsJ PF yF JF CS R)) ≤ yF ^ 2 / 100 := by
    rw [hBs]
    exact cw_joint hCb0 hPF0.ne'
  have hB1 : 1 ≤ jointBs X R (capsJ PF yF JF CS R) := by
    rw [hBs, one_le_div hPF0]
    exact hguards.2
  have hCSl : D.CS * Ex D.cS R ≤ CS := mul_le_mul_of_nonneg_right hCS₁ (Ex_pos _ _).le
  set L' := levelsJ D.L (Ex (D.cS / 3) R) with hL'd
  have hL' : ∀ i, 1 ≤ L' i :=
    one_le_levelsJ hD.L_ge (hdom.one_le_Ex (div_nonneg hD.cS_nonneg (by norm_num)))
  have hc4 : c4 ≤ CS := hc4₁.trans (le_mul_of_one_le_right (by linarith) hEx1)
  have hXU := hdom.X_le_U
  have hXT := hdom.X_le_T
  have h2P : 2 * X ≤ PF / 2 := by
    have : 49 * X ≤ PF := mul_le_mul hKP49 hXU hX0.le (by linarith)
    linarith
  have h2y : 2 * X ≤ 4 / 5 * yF := by
    have : 20 * X ≤ yF := mul_le_mul (by linarith) hXT hX0.le (by linarith)
    linarith
  have hlt := capsJImp_below hPF0 hyF0 hJF0 (by linarith : 0 < CS) hR0
  have hgood0 : ∀ {r : ℝ} {g : Field} {y : ℝ → Field}, Adm 2 (y 0) → hnorm 2 (y 0) ≤ X →
      GoodPoint (2 * X) (capsJStart PF yF JF CS R L') (capsJImp PF yF JF CS R) r g y 0 :=
    fun hv' hvX' ↦
      goodPoint_zero rfl hv' hvX' hX0.le hdom.X_le_R hdom.one_lt_R.le h2P h2y hc4 hCS0 hL'
  have himp : ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞), ActualSol X (R - X) r g y Ty →
      ∃ (Lev Bd : ℝ → Prop) (W0 : ℝ → ℝ), Lev 0 ∧ StrictOn (2 * X) Tp (fun _ ↦ Thr)
        (capsJ PF yF JF CS R) (capsJImp PF yF JF CS R)
        (capsJStart PF yF JF CS R L') Lev Bd r g y Ty ∧
        KinFunOn X (D.q₀ X R) Bd r g y Ty W0 := by
    intro r g y Ty hsol
    obtain ⟨W0, hW0⟩ := hD.kinetic X R hdom r g y Ty hsol
    have hadm0 : Adm 2 (y 0) := hsol.sol.adm 0 le_rfl (by simpa using hsol.pos)
    exact ⟨SlowHistory (capsJ PF yF JF CS R) L' R r g y, fun u ↦ slowSup r g y u ≤ D.Minf R, W0,
      slowHistory_zero hlt (hgood0 hadm0 hsol.init_le),
      strictOn_joint (CSl := D.CS * Ex D.cS R) hσ hD.m₀_mem hD.CG_nonneg (hD.h1 X R hdom)
        (hD.h2 X R hdom) hsol hW0 (fun s t hp hLv ↦ hD.slow X R hdom r g y Ty hsol _ s t hp hLv)
        hCSl hR0 hcy0 hcy hCb0 hbar hTp3 hPF0 hyF0.le hpeak hdis hB1 hguards.1 hCW hthr, hW0⟩
  exact global_of_strictOn hX1 hTp2 hlt himp hg hgφ hv hvX hr (hthr |r| hr).1
    fun y hy0 ↦ goodPoint_zero hy0 hv hvX hX0.le hdom.X_le_R hdom.one_lt_R.le h2P h2y hc4 hCS0 hL'

/-- **The normalized joint theorem** (R1 + R3): for `X, R` in the joint domain, data in the balls
`(X, R − X)` and `C Q Ex(C₀, R) ≤ |r|`, the maximal filtered solution is global with a uniform
`H²` bound.  There is no compact range. -/
theorem joint_normalized {D : JointData} (hD : JointInterfaces D) :
    ∃ (C C₀ R₀ : ℝ) (S : ℝ → ℝ → ℝ), 0 < C ∧ 0 < C₀ ∧ 0 < R₀ ∧
      ∀ (X R r : ℝ) (g v₀ : Field), JDom R₀ X R → Adm 2 g → hnorm 2 g ≤ R - X → Adm 2 v₀ →
        hnorm 2 v₀ ≤ X → C * jointQ X R * Ex C₀ R ≤ |r| →
        ∃ y : ℝ → Field, IsHeatSol (filtN r 0) (filtG r 0 g) ⊤ y ∧ y 0 = v₀ ∧
          ∀ t, 0 ≤ t → hnorm 2 (y t) ≤ S X R := by
  have hσ : (0 : ℝ) < 281 / 1000 ∧ (281 : ℝ) / 1000 < 1 := by norm_num
  obtain ⟨CT₀, cT, hcT, hTpLe⟩ := hD.Tp_le
  obtain ⟨CN₀, hCN⟩ := hD.Nbar_le
  obtain ⟨Cp₀, hCp⟩ := hD.piTol_le
  obtain ⟨cy, hcy0, hcy⟩ := young_cubic hσ hD.Cs_nonneg (lam := 1 / 4) (by norm_num)
  obtain ⟨Cb, hCb0, hbar⟩ := barrier_cap hD.m₀_mem.1 (by linarith [hD.m₀_mem.2])
  have hbar' : BarrierProp D.m₀ Cb := hbar
  set CT := max CT₀ 0 with hCT
  set CN := max CN₀ 0 with hCNd
  set Cp := max Cp₀ 0 with hCpd
  have hCT0 : 0 ≤ CT := le_max_right _ _
  set CS₁ := max D.CS c4 with hCS₁
  set K := jointK CN Cp cy Cb CS₁ CT with hK
  set c := D.cS + cT * betaOf ((281 : ℝ) / 1000) with hc
  have hβ0 : 0 < betaOf ((281 : ℝ) / 1000) := by rw [betaOf_281]; norm_num
  have hK1 : 1 ≤ K :=
    (by linarith [jointKP_ge (CN := CN) (Cp := Cp) hcy0 hCT0] :
      (1 : ℝ) ≤ jointKP CN Cp cy CT).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hc0 : 0 ≤ c := by
    have := hD.cS_nonneg
    positivity
  obtain ⟨Cth, Bth, Rth, hCth, hBth, hRth, hpay⟩ := thresholds_paid_joint hD hK1 hc0
  set R₀ : ℝ := 1 + |D.R₀| + |Rth| + K ^ (32 : ℝ) + D.CG ^ (8 : ℝ) +
    Real.exp (Real.exp (32 * c)) with hR₀
  have hb1 := abs_nonneg D.R₀
  have hb2 := abs_nonneg Rth
  have hb3 : 0 ≤ K ^ (32 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hb4 : 0 ≤ D.CG ^ (8 : ℝ) := Real.rpow_nonneg hD.CG_nonneg _
  have hb5 := Real.exp_pos (Real.exp (32 * c))
  refine ⟨Cth, Bth, R₀, fun X R ↦ (capsJoint CN Cp cy Cb CS₁ D.cS (D.Tp X R) X R).yF +
    (capsJoint CN Cp cy Cb CS₁ D.cS (D.Tp X R) X R).BS + 4 * (R - X), by linarith, by linarith,
    by rw [hR₀]; linarith, ?_⟩
  intro X R r g v₀ hdom hg hgφ hv hvX hr
  have hRR : R₀ ≤ R := hdom.R₀_le
  rw [hR₀] at hRR
  have hdom₁ : JDom D.R₀ X R := hdom.mono ((le_abs_self _).trans (by rw [hR₀]; linarith))
  have hdom₂ : JDom Rth X R := hdom.mono ((le_abs_self _).trans (by rw [hR₀]; linarith))
  have hTp2 : 3 ≤ D.Tp X R := hD.Tp_ge X R hdom₁
  have hTpC : D.Tp X R ≤ CT * Ex cT R := (hTpLe X R hdom₁).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Ex_pos _ _).le)
  have hX0 : 0 < X := by linarith [hdom.one_lt_X]
  have hscaled : CapsScaledJ K c X R (capsJoint CN Cp cy Cb CS₁ D.cS (D.Tp X R) X R) :=
    capsJoint_scaled hdom hcy0 hCb0 hD.cS_nonneg hcT hCT0 (by linarith) hTpC
  -- the guards
  have hPF0 : 0 < jointKP CN Cp cy (D.Tp X R) * jointU X :=
    mul_pos (by linarith [jointKP_ge (CN := CN) (Cp := Cp) hcy0 (by linarith : 0 ≤ D.Tp X R)])
      (by linarith [hdom.one_lt_U])
  have hRlarge₁ : K ≤ R ^ ((1 : ℝ) / 32) := by
    refine le_rpow_of_large (by linarith) (by norm_num) ?_
    have e : (1 : ℝ) / (1 / 32) = 32 := by norm_num
    rw [e]
    linarith
  have hRlarge₂ : D.CG ≤ R ^ ((1 : ℝ) / 8) := by
    refine le_rpow_of_large hD.CG_nonneg (by norm_num) ?_
    have e : (1 : ℝ) / (1 / 8) = 8 := by norm_num
    rw [e]
    linarith
  have hRlarge₃ : Ex c R ≤ R ^ ((1 : ℝ) / 32) := by
    refine Ex_le_rpow hdom.one_lt_R hdom.loglog_pos ?_
    have := le_loglog (B := 32 * c) (R := R) (by linarith)
    linarith
  exact joint_at hD hcy0 hcy hCb0 hbar' (le_max_left _ _) (le_max_right _ _) hdom₁
    ((hCN X R hdom₁).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0.le))
    ((hCp X R hdom₁).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0.le))
    (hdom.guards hPF0 (Ex_pos _ _).le hscaled.1.2 hRlarge₁ hRlarge₃ hRlarge₂)
    (fun q hq ↦ hpay X R hdom₂ _ hscaled q hq) hg hgφ hv hvX hr

/-- The bound of the joint conclusion: `S` from `joint_normalized`, and the sliding `L²H³` bound. -/
def jointBd (S : ℝ → ℝ → ℝ) (μ φ : ℝ) : ℝ :=
  max (S (Real.exp (Real.exp 1) + μ) (Real.exp (Real.exp 1) + μ + φ))
    (S (Real.exp (Real.exp 1) + μ) (Real.exp (Real.exp 1) + μ + φ) ^ 2 + 128 * c4 ^ 2 *
      S (Real.exp (Real.exp 1) + μ) (Real.exp (Real.exp 1) + μ + φ) ^ 4 + 2 * φ ^ 2)

/-- **The joint theorem from the interfaces**, for one parameter set `D`: the conclusion of
`quantitative_joint_force`, by the scaling of `global_regularity` (`joint_normalized` at
`μ = M/ν`, `φ = F/ν²`, `r = α/ν`, in the balls `(X, R − X)`) and `exists_physical_of_normalized`. -/
theorem joint_of_data {D : JointData} (hD : JointInterfaces D) :
    ∃ C C₀ R₀ : ℝ, 0 < C ∧ 0 < C₀ ∧ 0 < R₀ ∧ ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F →
        let X := Real.exp (Real.exp 1) + M / ν
        let R := X + F / ν ^ 2
        let U := X ^ ((1719 : ℝ) / 719)
        max R₀ (X ^ (24 : ℝ)) ≤ R →
        C * U * R ^ 3 * Real.exp (C₀ * Real.log R / Real.log (Real.log R)) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  obtain ⟨C, C₀, R₀, S, hC, hC₀, hR₀, H⟩ := joint_normalized hD
  refine ⟨C, C₀, R₀, hC, hC₀, hR₀, jointBd S, ?_⟩
  intro ν M F α u₀ f hν hM hF hu₀ hf hu₀M hfF X R U hdom hthr
  have hν2 : 0 < ν ^ 2 := pow_pos hν 2
  have hc : ((ν : ℂ) ^ 2)⁻¹ = (((ν ^ 2)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hc' : (ν⁻¹ : ℂ) = ((ν⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hg : Adm 2 (((ν : ℂ) ^ 2)⁻¹ • f) := by
    rw [hc]
    exact adm_smul_real _ hf
  have hv : Adm 2 ((ν⁻¹ : ℂ) • u₀) := by
    rw [hc']
    exact adm_smul_real _ hu₀
  have hgn : hnorm 2 (((ν : ℂ) ^ 2)⁻¹ • f) ≤ F / ν ^ 2 := by
    rw [hc, hnorm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hν2).le,
      div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hfF (inv_pos.2 hν2).le
  have hvn : hnorm 2 ((ν⁻¹ : ℂ) • u₀) ≤ M / ν := by
    rw [hc', hnorm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hν).le,
      div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hu₀M (inv_pos.2 hν).le
  have hμ : 0 ≤ M / ν := div_nonneg hM hν.le
  have hRX : R - X = F / ν ^ 2 := by
    change X + F / ν ^ 2 - X = F / ν ^ 2
    ring
  have hdom' : JDom R₀ X R := ⟨le_add_of_nonneg_right hμ, hdom⟩
  have hgX : hnorm 2 (((ν : ℂ) ^ 2)⁻¹ • f) ≤ R - X := by rw [hRX]; exact hgn
  have hvX : hnorm 2 ((ν⁻¹ : ℂ) • u₀) ≤ X :=
    hvn.trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hthr' : C * jointQ X R * Ex C₀ R ≤ |α / ν| := by
    rw [abs_div, abs_of_pos hν]
    refine le_trans (le_of_eq ?_) hthr
    unfold jointQ jointU Ex
    ring
  obtain ⟨y, hy, h0, hS2⟩ := H X R (α / ν) _ _ hdom' hg hgX hv hvX hthr'
  have hG : GoodForce (filtG (α / ν) 0 (((ν : ℂ) ^ 2)⁻¹ • f)) (R - X) :=
    goodForce_mono (goodForce_filtG _ 0 hg) ((hnorm_mono (by norm_num) hg.inH).trans hgX)
  have hBd : jointBd S (M / ν) (F / ν ^ 2) =
      max (S X R) (S X R ^ 2 + 128 * c4 ^ 2 * S X R ^ 4 + 2 * (R - X) ^ 2) := by
    rw [hRX]
    rfl
  rw [hBd]
  exact exists_physical_of_normalized hν hg hy h0
    (fun t ht ↦ ⟨((hnorm_mono (by norm_num) (hy.adm t ht ENNReal.ofReal_lt_top).inH).trans
      (hS2 t ht)).trans (le_max_left _ _), (hS2 t ht).trans (le_max_left _ _)⟩)
    fun t ht ↦ (sliding_h3' (majorized_filtN _ 0) hG hy hS2 ht).trans (le_max_right _ _)

/-- **Theorem 1.2, joint large force, from the interfaces.**  The conclusion is verbatim that of
`quantitative_joint_force` (`OddViscousNS/Quant.lean`), under the two published counting inputs and
the package `JointInterfaces`, for parameters which may depend on the resonant constants.  What is
open is exactly the list of `Joint/Interfaces.lean`: E4-J, E5-J, E7-P, E8-J, E9-J and the role
table; the regimes layer (R1, R3, E6, E10) is proved. -/
theorem quantitative_joint_of_interfaces
    (hI : ∀ Cs CH : ℝ, 0 ≤ Cs → 0 < CH → ResH1 ((281 : ℝ) / 1000) Cs →
      ResH2 ((281 : ℝ) / 1000) CH → ∃ D : JointData, JointInterfaces D) :
    ∃ C C₀ R₀ : ℝ, 0 < C ∧ 0 < C₀ ∧ 0 < R₀ ∧ ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F →
        let X := Real.exp (Real.exp 1) + M / ν
        let R := X + F / ν ^ 2
        let U := X ^ ((1719 : ℝ) / 719)
        max R₀ (X ^ (24 : ℝ)) ≤ R →
        C * U * R ^ 3 * Real.exp (C₀ * Real.log R / Real.log (Real.log R)) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  obtain ⟨Cs, hCs, h1⟩ := resonant_H1_of_counts
  obtain ⟨CH, -, h2⟩ := resonant_H2_of_counts
  have h2' : ResH2 ((281 : ℝ) / 1000) (max CH 1) := fun F hF hPF ↦ (h2 F hF hPF).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (hnorm_nonneg _ _)) (hnorm_nonneg _ _)) (hnorm_nonneg _ _))
  obtain ⟨D, hD⟩ := hI Cs (max CH 1) hCs (lt_of_lt_of_le one_pos (le_max_right _ _)) h1 h2'
  exact joint_of_data hD

end OVNS.Quant

end
