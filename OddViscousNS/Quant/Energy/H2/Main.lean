import OddViscousNS.Quant.Energy.H2.Bounds

/-!
# E8: the `H²` energy interface (assembly)

`h2EnergyInterface`: `H2EnergyInterface (281/1000) CH μ φ 2 K₂ m₀ q₂ nearN` with `K₂ = h2K₂`,
`m₀ = 1/4` absolute, and `DegreeBelow (281/1000) (9876/719) slowExpF q₂`, on the pieces of length
`Tp = 2` and at the exponents `slowExpF = (2, 3, 4, 5/2)` of the slow layer.  Every clause of the
interface is proved (`#print axioms h2EnergyInterface`: `propext`, `Classical.choice`,
`Quot.sound`); the status of each statement is in `t12_h2_scaffold.md`.

* `h2Energy_coercive`: `31/32 b_F² ≤ W ≤ 33/32 b_F²` (`metBil2_le`, role 28; `cubicE_two_static_le`,
  role 16).
* `h2_pointwise`: the integrand of `W'` against `−2d₀ c_F² + 2B b_F c_F + G W + H`, from
  `h2RHS_budget`.
* `h2Energy_integrated`: the inequality on subintervals, with all integrands integrable (`W` is
  continuous as a primitive).
* `clip_G`, `clip_H`: the masses.  `∫ G ≤ 1/4` and `∫ H ≤ W_*/32` hold on the whole piece; the
  clip length `1/λ_*` is not used, only `t − s ≤ 2`.  `H` is the only place where `CH` enters
  (`W_*(CH) ≥ W_*(CH₀)` for `CH ≥ CH₀`).
* `h2EnergyInterface_of_lower`: the interface for every `CH ≥ CH₀ > 0`, with the threshold at `CH₀`.
* `h2_degree`: the degree lemma (worst role `31price`, degree `≤ 27/2`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace OVNS.Quant.H2

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### A. Coercivity -/

/-- **Coercivity** (TeX `ℓ b_F² ≤ W ≤ u b_F²`, `(ℓ, u) = (31/32, 33/32)`). -/
theorem h2Energy_coercive (h : ActualSol μ φ r g y Ty) (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) {θ CH₀ : ℝ}
    {caps : Caps} {s t : ℝ} (hP : PieceHyp 2 (h2Threshold θ CH₀ μ φ) r g y Ty caps s t) {u : ℝ}
    (hu : u ∈ Icc s t) :
    31 / 32 * fastNorm 2 r g y u ^ 2 ≤ h2Energy r g y u ∧
      h2Energy r g y u ≤ 33 / 32 * fastNorm 2 r g y u ^ 2 := by
  obtain ⟨hr, -, -, -, -, r16, -, -, -, -, -, r28, -, -⟩ := thr_pieces hμ hφ caps hP.thr
  have hr0' : 0 < |r| := by linarith
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr0'; exact lt_irrefl _ hr0'
  have hu0 : 0 ≤ u := hP.hs.trans hu.1
  have huT := lt_lifespan hu.2 hP.ht
  have hx := actual_adm h hu0 huT
  set F := PiF (actual r g y u) with hFdef
  set S := PiS (actual r g y u) with hSdef
  have hF : Adm 2 F := hx.PiF
  have hS : Adm 2 S := hx.PiS
  have hF' : PiF F = F := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hFdef, PiF, hk]
  have hS' : PiS S = S := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hSdef, PiS, hk]
  obtain ⟨-, cF2, -, cS2, -⟩ := hP.onPrefix.1 u hu
  set b := fastNorm 2 r g y u with hb
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have hbY : b ≤ cp caps.yF := cF2.trans (le_cp _)
  have hY := cp_nonneg caps.yF
  have hB := cp_nonneg caps.BS
  have hbil := cBil_nonneg
  have hLc := h2Lc_nonneg caps
  have hLy := h2Ly_nonneg caps
  have hL0 := h2L0_nonneg hφ caps
  have hPr := h2Price_nonneg (φ := φ) hμ caps
  -- the metric
  have hm : |metricCorr2 r g y u| ≤ 1 / 64 * b ^ 2 := by
    have h1 := metBil2_le hr0 (r * u) hS.mz hS' hF.mz hF' hF.real hF.mz hF.real
    have e : metricCorr2 r g y u = metBil2 r (r * u) S F F := metForm2_eq_bil _ _ _ _
    rw [e]
    refine h1.trans ?_
    have h2 : hnorm 2 S ≤ cp caps.BS := cS2.trans (le_cp _)
    have h3 : 2 ^ 6 * cBil * cp caps.BS ≤ |r| := by
      unfold role28 at r28
      have n1 : 0 ≤ 2 ^ 6 * cBil * cp caps.BS * h2Lc caps := by positivity
      have n2 : 0 ≤ 2 ^ 8 * cBil * cp caps.BS * h2L0 φ caps := by positivity
      have n3 : 0 ≤ 2 ^ 8 * cBil * cp caps.BS * (h2Ly caps * h2Price μ φ caps) := by positivity
      nlinarith
    have h4 : cBil * hnorm 2 S / |r| ≤ 1 / 64 := by
      rw [div_le_div_iff₀ hr0' (by norm_num)]
      have := mul_le_mul_of_nonneg_left h2 hbil
      nlinarith
    have e2 : cBil * hnorm 2 S * hnorm 2 F * hnorm 2 F / |r| = cBil * hnorm 2 S / |r| * b ^ 2 := by
      rw [hb]
      unfold fastNorm
      ring
    rw [e2]
    exact mul_le_mul_of_nonneg_right h4 (sq_nonneg b)
  -- the cubic
  have hc : |2 * cubicCorr2 r g y u| ≤ 1 / 64 * b ^ 2 := by
    have h1 := cubicE_two_static_le hr (r * u) hF.mz hF.real hF'
    have hPz : cStat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) * cp caps.yF ≤ 1 / 128 := by
      have hSt := cStat2_pos
      have hPC := profC_pos
      have n1 : 0 ≤ (2 ^ 8 * cStat2 * profC * cp caps.yF) ^ (100 / 29 : ℝ) := by positivity
      have n2 : 0 ≤ (2 ^ 8 * cStat2 * cp caps.yF) ^ 2 := by positivity
      unfold role16 at r16
      exact pz_le hSt.le hY hr (by linarith) (by linarith)
    have hPz0 : 0 ≤ cStat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) := by
      have := cStat2_pos
      have h3 : 0 ≤ nearP |r| := by
        unfold nearP
        positivity
      have h4 : 0 ≤ |r| ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hr0'.le _
      positivity
    have h2 : cStat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) * b ≤ 1 / 128 :=
      (mul_le_mul_of_nonneg_left hbY hPz0).trans hPz
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have e : cubicCorr2 r g y u = cubicE 2 (-1) r (r * u) F := rfl
    rw [e]
    have h3 : |cubicE 2 (-1) r (r * u) F| ≤
        cStat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) * b * b ^ 2 := by
      refine h1.trans (le_of_eq ?_)
      rw [hb]
      unfold fastNorm
      ring
    have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg b)
    linarith
  have hm' := abs_le.mp hm
  have hc' := abs_le.mp hc
  unfold h2Energy
  constructor <;> nlinarith [sq_nonneg b]

/-! ### B. The integrated inequality -/

/-- A nonnegative function with an integrable square is integrable (`c_F`, from `∫ c_F² < ∞` of
`fast_h2_law`, for the term `2B b_F c_F`). -/
lemma intervalIntegrable_of_sq {f : ℝ → ℝ} {a b : ℝ} (hf0 : ∀ u, 0 ≤ f u)
    (h : IntervalIntegrable (fun u => f u ^ 2) volume a b) : IntervalIntegrable f volume a b := by
  have hm : AEStronglyMeasurable f (volume.restrict (uIoc a b)) := by
    have h1 := (intervalIntegrable_iff.1 h).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun u => Real.sqrt (f u ^ 2))
        (volume.restrict (uIoc a b)) := Real.continuous_sqrt.comp_aestronglyMeasurable h1
    refine h2.congr (.of_forall fun u => ?_)
    exact Real.sqrt_sq (hf0 u)
  refine ((intervalIntegrable_const (c := (1 : ℝ))).add h).mono_fun hm ?_
  refine .of_forall fun u => ?_
  have h1 := hf0 u
  have h2 : ‖f u‖ = f u := Real.norm_of_nonneg h1
  show ‖f u‖ ≤ ‖(1 : ℝ) + f u ^ 2‖
  rw [h2, Real.norm_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (f u - 1)]

/-- `W` is continuous on a piece: it is a primitive (`h2Energy_identity`). -/
theorem h2Energy_continuousOn (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    ContinuousOn (h2Energy r g y) (Icc s t) := by
  set f : ℝ → ℝ := fun u => 2 * h2RHS r g y u - 2 * fastNorm 3 r g y u ^ 2 with hf
  have hI : IntervalIntegrable f volume s t :=
    ((h2Energy_identity h hr hs hst ht).1.const_mul 2).sub
      ((fast_h2_law h hs hst ht).1.const_mul 2)
  have hP : ContinuousOn (fun v => ∫ u in s..v, f u) (Icc s t) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := f) (a := s)
      (b := t) (by
        rw [uIcc_of_le hst]
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le hst).1 hI)
    rwa [uIcc_of_le hst] at this
  have hC : ContinuousOn (fun v => h2Energy r g y s + ∫ u in s..v, f u) (Icc s t) :=
    continuousOn_const.add hP
  refine hC.congr fun v hv => ?_
  have hv' := lt_lifespan hv.2 ht
  obtain ⟨hI1, hE⟩ := h2Energy_identity h hr hs hv.1 hv'
  have hI2 := (fast_h2_law h hs hv.1 hv').1
  have e : ∫ u in s..v, f u = 2 * (∫ u in s..v, h2RHS r g y u) -
      2 * ∫ u in s..v, fastNorm 3 r g y u ^ 2 := by
    simp only [hf]
    rw [intervalIntegral.integral_sub (hI1.const_mul 2) (hI2.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only
  rw [e]
  linarith

/-- The pointwise form of the inequality, at almost every time. -/
theorem h2_pointwise (h : ActualSol μ φ r g y Ty) (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) {θ CH₀ CH : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hres : ResH2 θ CH) (hCH : 0 ≤ CH) {caps : Caps} {s t : ℝ}
    (hP : PieceHyp 2 (h2Threshold θ CH₀ μ φ) r g y Ty caps s t)
    (hK : h2K₂ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * nearN |r| ≤ 1) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)),
      2 * h2RHS r g y u - 2 * fastNorm 3 r g y u ^ 2 ≤
        -2 * dZero * fastNorm 3 r g y u ^ 2 +
          2 * resCoeff θ CH μ φ caps * fastNorm 2 r g y u * fastNorm 3 r g y u +
          h2G φ caps r g y u * h2Energy r g y u + h2H φ caps r := by
  filter_upwards [h2RHS_budget h hμ hφ hθ0 hθ1 hres hCH hP hK,
    ae_restrict_mem measurableSet_Icc] with u hb hu
  obtain ⟨hco, -⟩ := h2Energy_coercive h hμ hφ hP hu
  have hG0 := h2G0_nonneg hφ caps r
  have hG1 := h2G1_nonneg caps r
  set Gp := h2G0 φ caps r + h2G1 caps r * hnorm 3 (corrSlow r g y u) ^ 2 with hGp
  have hGp0 : 0 ≤ Gp := by positivity
  set b := fastNorm 2 r g y u
  set c := fastNorm 3 r g y u
  have h1 : 2 * (Gp * b ^ 2) ≤ h2G φ caps r g y u * h2Energy r g y u := by
    have e : h2G φ caps r g y u = 3 * Gp := rfl
    rw [e]
    have := mul_le_mul_of_nonneg_left hco (by positivity : 0 ≤ 3 * Gp)
    nlinarith [mul_nonneg hGp0 (sq_nonneg b)]
  have e2 : h2H φ caps r = 2 * h2H1 φ caps r := rfl
  rw [e2]
  have hd : -2 * dZero = -(4 / 3) := by
    unfold dZero
    norm_num
  rw [hd]
  nlinarith [sq_nonneg c]

/-- **The integrated inequality on subintervals** (TeX eq. quant-metric at `s = 2` plus the budget:
`W' ≤ −2d₀ c_F² + 2B b_F c_F + G W + H`, integrated). -/
theorem h2Energy_integrated (h : ActualSol μ φ r g y Ty) (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) {θ CH₀ CH : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hres : ResH2 θ CH) (hCH : 0 ≤ CH) {caps : Caps} {s t : ℝ}
    (hP : PieceHyp 2 (h2Threshold θ CH₀ μ φ) r g y Ty caps s t)
    (hK : h2K₂ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * nearN |r| ≤ 1) {u₁ u₂ : ℝ}
    (h1 : s ≤ u₁) (h2 : u₁ ≤ u₂) (h3 : u₂ ≤ t) :
    h2Energy r g y u₂ - h2Energy r g y u₁ ≤ ∫ u in u₁..u₂, (-2 * dZero * fastNorm 3 r g y u ^ 2 +
      2 * resCoeff θ CH μ φ caps * fastNorm 2 r g y u * fastNorm 3 r g y u +
      h2G φ caps r g y u * h2Energy r g y u + h2H φ caps r) := by
  obtain ⟨hr, hbudget, hsm, -, -, -, -, -, -, -, -, -, -, -⟩ := thr_pieces hμ hφ caps hP.thr
  have hr0' : 0 < |r| := by linarith
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr0'; exact lt_irrefl _ hr0'
  have hs := hP.hs
  have hu₁ : 0 ≤ u₁ := hs.trans h1
  have hu₂ : ENNReal.ofReal u₂ < Ty := lt_lifespan h3 hP.ht
  have ht₂ : 0 ≤ u₂ := hu₁.trans h2
  obtain ⟨hI, hE⟩ := h2Energy_identity h hr0 hu₁ h2 hu₂
  have hc2 := (fast_h2_law h hu₁ h2 hu₂).1
  have hc1 : IntervalIntegrable (fastNorm 3 r g y) volume u₁ u₂ :=
    intervalIntegrable_of_sq (fun _ => hnorm_nonneg _ _) hc2
  have hb : ContinuousOn (fastNorm 2 r g y) (uIcc u₁ u₂) := by
    rw [uIcc_of_le h2]
    exact (norms_continuous h ht₂ hu₂).2.1.mono (Icc_subset_Icc_left hu₁)
  have hbc : IntervalIntegrable
      (fun u => 2 * resCoeff θ CH μ φ caps * fastNorm 2 r g y u * fastNorm 3 r g y u)
      volume u₁ u₂ := by
    have := (hc1.continuousOn_mul hb).const_mul (2 * resCoeff θ CH μ φ caps)
    refine this.congr (fun u _ => ?_)
    ring
  have hW : ContinuousOn (h2Energy r g y) (uIcc u₁ u₂) := by
    rw [uIcc_of_le h2]
    exact h2Energy_continuousOn h hr0 hu₁ h2 hu₂
  have hcy2 : IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume u₁ u₂ := by
    have hPy := (heatPair_corrSlow h hr0 (σ := 2) (Or.inr (Or.inr rfl)) ht₂ hu₂).mono hu₁ le_rfl
    have := hPy.intervalIntegrable_dissipation h2
    rwa [show (2 : ℝ) + 1 = 3 by norm_num] at this
  have hGi : IntervalIntegrable (h2G φ caps r g y) volume u₁ u₂ := by
    have := ((intervalIntegrable_const (c := h2G0 φ caps r)).add
      (hcy2.const_mul (h2G1 caps r))).const_mul 3
    exact this
  have hGW : IntervalIntegrable (fun u => h2G φ caps r g y u * h2Energy r g y u) volume u₁ u₂ :=
    hGi.mul_continuousOn hW
  have hRi : IntervalIntegrable (fun u => -2 * dZero * fastNorm 3 r g y u ^ 2 +
      2 * resCoeff θ CH μ φ caps * fastNorm 2 r g y u * fastNorm 3 r g y u +
      h2G φ caps r g y u * h2Energy r g y u + h2H φ caps r) volume u₁ u₂ :=
    (((hc2.const_mul _).add hbc).add hGW).add intervalIntegrable_const
  have hLi : IntervalIntegrable (fun u => 2 * h2RHS r g y u - 2 * fastNorm 3 r g y u ^ 2)
      volume u₁ u₂ := (hI.const_mul 2).sub (hc2.const_mul 2)
  have e : h2Energy r g y u₂ - h2Energy r g y u₁ =
      ∫ u in u₁..u₂, (2 * h2RHS r g y u - 2 * fastNorm 3 r g y u ^ 2) := by
    rw [intervalIntegral.integral_sub (hI.const_mul 2) (hc2.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    linarith
  rw [e]
  have hpt := h2_pointwise h hμ hφ hθ0 hθ1 hres hCH hP hK
  have hpt' : ∀ᵐ u ∂(volume.restrict (Icc u₁ u₂)),
      2 * h2RHS r g y u - 2 * fastNorm 3 r g y u ^ 2 ≤
        -2 * dZero * fastNorm 3 r g y u ^ 2 +
          2 * resCoeff θ CH μ φ caps * fastNorm 2 r g y u * fastNorm 3 r g y u +
          h2G φ caps r g y u * h2Energy r g y u + h2H φ caps r :=
    ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc h1 h3) hpt
  exact intervalIntegral.integral_mono_ae_restrict h2 hLi hRi hpt'

/-! ### C. The clip masses -/

/-- The smallness of the multiplier and of the residual, from the thresholds (TeX, the virtual
barrier paragraph: the clips carry `∫ G ≤ m₀ ≤ 1/4`, `∫ H ≤ W_*/32`; roles 28, 31, 32). -/
theorem h2_small {θ CH₀ q : ℝ} (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) {caps : Caps} {r' : ℝ}
    (hq : q = |r'|) (hthr : h2Threshold θ CH₀ μ φ caps ≤ q) :
    h2G0 φ caps r' ≤ 7 / 512 ∧ h2G1 caps r' * h2Price μ φ caps ≤ 3 / 512 ∧
      h2H1 φ caps r' ≤ h2Hn φ caps / |r'| := by
  subst hq
  obtain ⟨hr, -, -, -, -, -, -, -, -, rpsi, rpr, r28, rsrc, -⟩ := thr_pieces hμ hφ caps hthr
  have hr0 : 0 < |r'| := by linarith
  have hL0 := h2L0_nonneg hφ caps
  have hLc := h2Lc_nonneg caps
  have hLy := h2Ly_nonneg caps
  have hPr := h2Price_nonneg (φ := φ) hμ caps
  have hB := cp_nonneg caps.BS
  have hbil := cBil_nonneg
  have hM := nM_nonneg r'
  have hκ := kap_nonneg caps r'
  have hsS := hSrc_nonneg hφ caps
  have hcS := cSrc_nonneg
  have m1 : nM r' * h2L0 φ caps ≤ 1 / 64 := nM_mul_le hr hL0 rpsi
  have m2 : nM r' * (h2Ly caps * Real.sqrt (h2Price μ φ caps)) ≤ 1 / 64 :=
    nM_mul_le hr (mul_nonneg hLy (Real.sqrt_nonneg _)) rpr
  have hsplit : 0 ≤ 2 ^ 6 * cBil * cp caps.BS ∧ 0 ≤ 2 ^ 6 * cBil * cp caps.BS * h2Lc caps ∧
      0 ≤ 2 ^ 8 * cBil * cp caps.BS * h2L0 φ caps ∧
      0 ≤ 2 ^ 8 * cBil * cp caps.BS * (h2Ly caps * h2Price μ φ caps) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> positivity
  obtain ⟨n0, n1, n2, n3⟩ := hsplit
  unfold role28 at r28
  have k1 : kap caps r' * h2Lc caps ≤ 1 / 64 := by
    have e : kap caps r' * h2Lc caps = cBil * cp caps.BS * h2Lc caps / |r'| := by
      unfold kap
      ring
    rw [e, div_le_div_iff₀ hr0 (by norm_num)]
    nlinarith
  have k2 : kap caps r' * h2L0 φ caps ≤ 1 / 256 := by
    have e : kap caps r' * h2L0 φ caps = cBil * cp caps.BS * h2L0 φ caps / |r'| := by
      unfold kap
      ring
    rw [e, div_le_div_iff₀ hr0 (by norm_num)]
    nlinarith
  have k3 : kap caps r' * (h2Ly caps * h2Price μ φ caps) ≤ 1 / 256 := by
    have e : kap caps r' * (h2Ly caps * h2Price μ φ caps) =
        cBil * cp caps.BS * (h2Ly caps * h2Price μ φ caps) / |r'| := by
      unfold kap
      ring
    rw [e, div_le_div_iff₀ hr0 (by norm_num)]
    nlinarith
  have a1 : cSrc * hSrc φ caps / |r'| ≤ 1 / 128 := by
    unfold role28src2 at rsrc
    rw [div_le_div_iff₀ hr0 (by norm_num)]
    nlinarith
  have a0 : 0 ≤ cSrc * hSrc φ caps / |r'| := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold h2G0
    have s1 : (nM r' * h2L0 φ caps) ^ 2 ≤ (1 / 64) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hM hL0) m1 2
    have s2 : (kap caps r' * h2Lc caps) ^ 2 ≤ (1 / 64) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hκ hLc) k1 2
    have s3 : (cSrc * hSrc φ caps / |r'|) ^ 2 ≤ (1 / 128) ^ 2 := pow_le_pow_left₀ a0 a1 2
    norm_num at s1 s2 s3 ⊢
    linarith
  · unfold h2G1
    have e : (nM r' * h2Ly caps) ^ 2 * h2Price μ φ caps =
        (nM r' * (h2Ly caps * Real.sqrt (h2Price μ φ caps))) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hPr]
      ring
    have s1 : (nM r' * (h2Ly caps * Real.sqrt (h2Price μ φ caps))) ^ 2 ≤ (1 / 64) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hM (mul_nonneg hLy (Real.sqrt_nonneg _))) m2 2
    have e2 : (16 * (nM r' * h2Ly caps) ^ 2 + kap caps r' * h2Ly caps / 2) * h2Price μ φ caps =
        16 * ((nM r' * h2Ly caps) ^ 2 * h2Price μ φ caps) +
          kap caps r' * (h2Ly caps * h2Price μ φ caps) / 2 := by ring
    rw [e2, e]
    norm_num at s1 ⊢
    linarith
  · have hT : 0 ≤ cp caps.BS + cp caps.yF + cp caps.WS + 1 := by
      have := cp_nonneg caps.yF
      have := cp_nonneg caps.WS
      positivity
    unfold h2H1 h2Hn hPsiC kap
    set n1' := 32 * (1 + c4) * φ * (cp caps.BS + cp caps.yF + cp caps.WS + 1) with hn1
    have hsq : 16 * (n1' / |r'|) ^ 2 ≤ 16 * n1' ^ 2 / |r'| := by
      rw [div_pow, ← mul_div_assoc]
      refine div_le_div_of_nonneg_left (by positivity) hr0 ?_
      nlinarith
    have e : (16 * n1' ^ 2 + cBil * cp caps.BS * (h2Ly caps + h2L0 φ caps)) / |r'| =
        16 * n1' ^ 2 / |r'| + cBil * cp caps.BS / |r'| * h2Ly caps +
          cBil * cp caps.BS / |r'| * h2L0 φ caps := by ring
    rw [e]
    have hκ' : 0 ≤ cBil * cp caps.BS / |r'| := by positivity
    have h1 := mul_nonneg hκ' hLy
    have h2 := mul_nonneg hκ' hL0
    linarith

/-- **The multiplier mass** on every subinterval of a piece of length `≤ 2` (interface clause
`∫ G ≤ m₀`, here `m₀ = 1/4`): `2 G₀' + G₁' P_y`, by `slow_price` and `h2_small`.  The clip length
`1/λ_*` of the TeX is not needed. -/
theorem clip_G (h : ActualSol μ φ r g y Ty) (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) {θ CH₀ : ℝ} {caps : Caps}
    {s t : ℝ} (hP : PieceHyp 2 (h2Threshold θ CH₀ μ φ) r g y Ty caps s t) {u₁ u₂ : ℝ}
    (h1 : s ≤ u₁) (h2 : u₁ ≤ u₂) (h3 : u₂ ≤ t) : ∫ u in u₁..u₂, h2G φ caps r g y u ≤ 1 / 4 := by
  obtain ⟨hr, hbudget, hsm, -, -, -, -, -, -, -, -, -, -, -⟩ := thr_pieces hμ hφ caps hP.thr
  have hr0' : 0 < |r| := by linarith
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr0'; exact lt_irrefl _ hr0'
  obtain ⟨hIy, hPr⟩ := slow_price h hr hμ hP.hs hP.hst hP.ht hP.len hP.onPrefix hbudget hsm
  obtain ⟨s0, s1, -⟩ := h2_small (r' := r) hμ hφ rfl hP.thr
  have hG0 := h2G0_nonneg hφ caps r
  have hG1 := h2G1_nonneg caps r
  have hst := hP.hst
  have hsub : ∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2 ≤
      ∫ u in s..t, hnorm 3 (corrSlow r g y u) ^ 2 :=
    intervalIntegral.integral_mono_interval h1 h2 h3
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) hIy
  have hIy' : IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume u₁ u₂ :=
    hIy.mono_set (by
      rw [uIcc_of_le h2, uIcc_of_le hst]
      exact Icc_subset_Icc h1 h3)
  have e : ∫ u in u₁..u₂, h2G φ caps r g y u =
      3 * ((u₂ - u₁) * h2G0 φ caps r +
        h2G1 caps r * ∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2) := by
    have : ∀ u, h2G φ caps r g y u =
        3 * (h2G0 φ caps r + h2G1 caps r * hnorm 3 (corrSlow r g y u) ^ 2) := fun _ => rfl
    simp only [this]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const (hIy'.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [e]
  have hlen : u₂ - u₁ ≤ 2 := by
    have := hP.len
    linarith
  have t1 : (u₂ - u₁) * h2G0 φ caps r ≤ 2 * (7 / 512) :=
    mul_le_mul hlen s0 hG0 (by norm_num)
  have t2 : h2G1 caps r * ∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2 ≤ 3 / 512 :=
    (mul_le_mul_of_nonneg_left (hsub.trans hPr) hG1).trans s1
  linarith

/-- `W_*` is monotone in the resonant coefficient (`Interfaces.lean`, `bStar`, `WStar`), which is
how the threshold at `CH₀` serves every `CH ≥ CH₀`. -/
lemma WStar_mono {A B B' : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hBB : B ≤ B') :
    WStar 1 A B ≤ WStar 1 A B' := by
  unfold WStar bStar dZero
  have h1 : 0 ≤ 1 * A * B / (2 / 3) := by positivity
  have h2 : 1 * A * B / (2 / 3) ≤ 1 * A * B' / (2 / 3) := by
    gcongr
  have := pow_le_pow_left₀ h1 h2 2
  linarith

/-- **The residual mass** on a piece with `P_F > 0`: `∫ H ≤ W_*/32`.  This is the only place
where `CH` enters the thresholds. -/
theorem clip_H {θ CH₀ CH : ℝ} (hCH₀ : 0 < CH₀) (hCH : CH₀ ≤ CH) (hμ : 0 ≤ μ)
    (hφ : 0 ≤ φ) {caps : Caps} (hPF : 0 < caps.PF)
    (hthr : h2Threshold θ CH₀ μ φ caps ≤ |r|) {ℓ : ℝ} (hℓ : ℓ ≤ 2) :
    ℓ * h2H φ caps r ≤ WStar 1 caps.PF (resCoeff θ CH μ φ caps) / 32 := by
  obtain ⟨hr, -, -, -, -, -, -, -, -, -, -, -, -, r32⟩ := thr_pieces hμ hφ caps hthr
  have hr0 : 0 < |r| := by linarith
  obtain ⟨-, -, s2⟩ := h2_small (r' := r) hμ hφ rfl hthr
  have hρ : 0 < rhoOf μ φ := by
    unfold rhoOf
    linarith
  have hB0 : 0 < resCoeff θ CH₀ μ φ caps := by
    unfold resCoeff
    have := Real.rpow_pos_of_pos hρ (1 - θ)
    have := Real.rpow_pos_of_pos hPF θ
    positivity
  have hBB : resCoeff θ CH₀ μ φ caps ≤ resCoeff θ CH μ φ caps := by
    unfold resCoeff
    have h1 := Real.rpow_pos_of_pos hρ (1 - θ)
    have h2 := Real.rpow_pos_of_pos hPF θ
    gcongr
  have hW0 : 0 < WStar 1 caps.PF (resCoeff θ CH₀ μ φ caps) := by
    unfold WStar bStar dZero
    positivity
  have hWm := WStar_mono hPF.le hB0.le hBB
  have hH := h2H1_nonneg hφ caps r
  have e : h2H φ caps r = 2 * h2H1 φ caps r := rfl
  have h1 : h2Hn φ caps / |r| ≤ WStar 1 caps.PF (resCoeff θ CH₀ μ φ caps) / 128 := by
    unfold role32 at r32
    rw [div_le_iff₀ hW0] at r32
    rw [div_le_div_iff₀ hr0 (by norm_num)]
    linarith
  rw [e]
  have h2 : ℓ * (2 * h2H1 φ caps r) ≤ 2 * (2 * h2H1 φ caps r) :=
    mul_le_mul_of_nonneg_right hℓ (by positivity)
  linarith

/-! ### D. The interface -/

/-- **E8: the interface, at a lower bound of the resonant constant**: for every `CH ≥ CH₀ > 0`
with `ResH2 θ CH`, the interface holds with `K₂ = h2K₂`, `m₀ = 1/4` and the threshold
`h2Threshold θ CH₀`, independent of `CH` otherwise. -/
theorem h2EnergyInterface_of_lower {θ CH₀ CH : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hCH₀ : 0 < CH₀)
    (hCH : CH₀ ≤ CH) (hres : ResH2 θ CH) {μ φ : ℝ} (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) :
    H2EnergyInterface θ CH μ φ 2 h2K₂ h2m₀ (h2Threshold θ CH₀ μ φ) nearN := by
  intro r g y Ty caps s t hsol hP hK A B
  have hCH0 : 0 ≤ CH := hCH₀.le.trans hCH
  have hs := hP.hs
  have hst := hP.hst
  have ht := hP.ht
  obtain ⟨hr, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := thr_pieces hμ hφ caps hP.thr
  have hr0' : 0 < |r| := by linarith
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr0'; exact lt_irrefl _ hr0'
  have ht0 : 0 ≤ t := hs.trans hst
  have hPF0 : 0 ≤ caps.PF := (hnorm_nonneg 1 _).trans (hP.onPrefix.1 s ⟨le_rfl, hst⟩).1
  refine ⟨h2Energy r g y, h2G φ caps r g y, fun _ => h2H φ caps r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun u hu => h2Energy_coercive hsol hμ hφ hP hu
  · exact (fast_h2_law hsol hs hst ht).1
  · exact fun u₁ u₂ h1 h2 h3 =>
      h2Energy_integrated hsol hμ hφ hθ0 hθ1 hres hCH0 hP hK h1 h2 h3
  · refine fun u _ => ⟨?_, ?_⟩
    · have h1 := h2G0_nonneg hφ caps r
      have h2 := h2G1_nonneg caps r
      unfold h2G
      positivity
    · have h1 := h2H1_nonneg hφ caps r
      unfold h2H
      positivity
  · have hPy := (heatPair_corrSlow hsol hr0 (σ := 2) (Or.inr (Or.inr rfl)) ht0 ht).mono hs le_rfl
    have hcy := hPy.intervalIntegrable_dissipation hst
    rw [show (2 : ℝ) + 1 = 3 by norm_num] at hcy
    exact ((intervalIntegrable_const (c := h2G0 φ caps r)).add
      (hcy.const_mul (h2G1 caps r))).const_mul 3
  · exact intervalIntegrable_const
  · intro u₁ u₂ h1 h2 h3 hclip
    refine ⟨?_, ?_⟩
    · exact (clip_G hsol hμ hφ hP h1 h2 h3).trans (le_of_eq rfl)
    · rw [intervalIntegral.integral_const, smul_eq_mul]
      have hℓ : u₂ - u₁ ≤ 2 := by
        have := hP.len
        linarith
      rcases hPF0.eq_or_lt with hz | hpos
      · -- `P_F = 0`: `λ_* = 0`, `1/λ_* = 0`, the clip is a point
        have hA : A = 0 := hz.symm
        have hl : 1 / lamStar 1 A B = 0 := by
          unfold lamStar bStar
          rw [hA]
          simp
        rw [hl] at hclip
        have heq : u₂ - u₁ = 0 := le_antisymm hclip (by linarith)
        rw [heq, zero_mul]
        have : 0 ≤ WStar 1 A B := by
          unfold WStar
          positivity
        positivity
      · exact clip_H hCH₀ hCH hμ hφ hpos hP.thr hℓ

/-! ### E. The degree lemma

`DgB δ K f κ` is the bound `0 ≤ f ≤ C μ^κ` on the `δ`-scaled caps, closed under the operations by
which the thresholds are built (`DgB.add`, `DgB.mul`, `DgB.rpow`, …).  The lemmas `dg_*` give the
degree of each role at `σ = 281/1000`, `e = slowExpF`, the technique of `Kinetic/Degree.lean` and of
`slow_degree`. -/

/-- `f` is nonnegative and `≤ C μ^κ` on the `δ`-scaled caps with constant `K`, at `σ = 281/1000`
and the slow exponents `slowExpF`. -/
def DgB (δ K : ℝ) (f : ℝ → Caps → ℝ) (κ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ, 1 ≤ μ → ∀ caps : Caps,
    CapsScaled ((281 : ℝ) / 1000) δ K μ slowExpF caps → 0 ≤ f μ caps ∧ f μ caps ≤ C * μ ^ κ

section DgB

variable {δ K κ κ' : ℝ} {f g : ℝ → Caps → ℝ}

lemma DgB.mono (hf : DgB δ K f κ) (h : κ ≤ κ') : DgB δ K f κ' := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨C, hC, fun μ hμ c hc => ⟨(hb μ hμ c hc).1, (hb μ hμ c hc).2.trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hμ h) hC

lemma DgB.congr (hf : DgB δ K f κ) (e : ∀ μ c, g μ c = f μ c) : DgB δ K g κ := by
  obtain ⟨C, hC, hb⟩ := hf
  exact ⟨C, hC, fun μ hμ c hc => by rw [e]; exact hb μ hμ c hc⟩

lemma DgB.add (hf : DgB δ K f κ) (hg : DgB δ K g κ) : DgB δ K (fun μ c => f μ c + g μ c) κ := by
  obtain ⟨C, hC, hb⟩ := hf
  obtain ⟨C', hC', hb'⟩ := hg
  refine ⟨C + C', add_nonneg hC hC', fun μ hμ c hc => ?_⟩
  obtain ⟨h1, h2⟩ := hb μ hμ c hc
  obtain ⟨h3, h4⟩ := hb' μ hμ c hc
  refine ⟨add_nonneg h1 h3, ?_⟩
  rw [add_mul]
  exact add_le_add h2 h4

lemma DgB.mul (hf : DgB δ K f κ) (hg : DgB δ K g κ') :
    DgB δ K (fun μ c => f μ c * g μ c) (κ + κ') := by
  obtain ⟨C, hC, hb⟩ := hf
  obtain ⟨C', hC', hb'⟩ := hg
  refine ⟨C * C', mul_nonneg hC hC', fun μ hμ c hc => ?_⟩
  obtain ⟨h1, h2⟩ := hb μ hμ c hc
  obtain ⟨h3, h4⟩ := hb' μ hμ c hc
  refine ⟨mul_nonneg h1 h3, ?_⟩
  have hμ0 : 0 < μ := by linarith
  rw [Real.rpow_add hμ0]
  calc f μ c * g μ c ≤ (C * μ ^ κ) * (C' * μ ^ κ') :=
        mul_le_mul h2 h4 h3 (h1.trans h2)
    _ = _ := by ring

lemma DgB.const {x : ℝ} (hx : 0 ≤ x) (hκ : 0 ≤ κ) : DgB δ K (fun _ _ => x) κ := by
  refine ⟨x, hx, fun μ hμ _ _ => ⟨hx, ?_⟩⟩
  have := Real.one_le_rpow hμ hκ
  nlinarith

lemma DgB.cmul {x : ℝ} (hx : 0 ≤ x) (hf : DgB δ K f κ) : DgB δ K (fun μ c => x * f μ c) κ := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨x * C, mul_nonneg hx hC, fun μ hμ c hc => ?_⟩
  obtain ⟨h1, h2⟩ := hb μ hμ c hc
  refine ⟨mul_nonneg hx h1, ?_⟩
  calc x * f μ c ≤ x * (C * μ ^ κ) := mul_le_mul_of_nonneg_left h2 hx
    _ = _ := by ring

lemma DgB.rpow (hf : DgB δ K f κ) {E : ℝ} (hE : 0 ≤ E) :
    DgB δ K (fun μ c => f μ c ^ E) (κ * E) := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨C ^ E, Real.rpow_nonneg hC E, fun μ hμ c hc => ?_⟩
  obtain ⟨h1, h2⟩ := hb μ hμ c hc
  have hμ0 : 0 < μ := by linarith
  refine ⟨Real.rpow_nonneg h1 E, ?_⟩
  have h3 := Real.rpow_le_rpow h1 h2 hE
  rwa [Real.mul_rpow hC (Real.rpow_nonneg hμ0.le κ), ← Real.rpow_mul hμ0.le] at h3

lemma DgB.sqrt (hf : DgB δ K f κ) : DgB δ K (fun μ c => Real.sqrt (f μ c)) (κ / 2) := by
  have h := hf.rpow (E := 1 / 2) (by norm_num)
  have e : κ * (1 / 2) = κ / 2 := by ring
  rw [e] at h
  exact h.congr fun _ _ => Real.sqrt_eq_rpow _

lemma DgB.pow2 (hf : DgB δ K f κ) : DgB δ K (fun μ c => f μ c ^ 2) (κ + κ) :=
  (hf.mul hf).congr fun _ _ => sq _

lemma DgB.pow4 (hf : DgB δ K f κ) : DgB δ K (fun μ c => f μ c ^ 4) (κ + κ + (κ + κ)) :=
  (hf.pow2.mul hf.pow2).congr fun _ _ => by ring

lemma DgB.add' {κ'' : ℝ} (hf : DgB δ K f κ) (hg : DgB δ K g κ') (h : κ ≤ κ'') (h' : κ' ≤ κ'') :
    DgB δ K (fun μ c => f μ c + g μ c) κ'' := (hf.mono h).add (hg.mono h')

/-- The atom `μ^κ`. -/
lemma dg_mu : DgB δ K (fun μ _ => μ ^ κ) κ := by
  refine ⟨1, zero_le_one, fun μ hμ _ _ => ⟨Real.rpow_nonneg (by linarith) _, ?_⟩⟩
  rw [one_mul]

end DgB

/-- The atoms of the scaled caps, with the fixed exponents `β, v, 2.01, 3.01, 2.51, 4.01, 1.01,
2.01` (`δ ≤ 1/100`). -/
structure DgAtoms (δ K : ℝ) : Prop where
  hP : DgB δ K (fun _ c => cp c.PF) (1719 / 719)
  hY : DgB δ K (fun _ c => cp c.yF) (2719 / 719)
  hA : DgB δ K (fun _ c => cp c.AS) (201 / 100)
  hB : DgB δ K (fun _ c => cp c.BS) (301 / 100)
  hW : DgB δ K (fun _ c => cp c.WS) (251 / 100)
  hJ : DgB δ K (fun _ c => cp c.JS) (401 / 100)
  hAh : DgB δ K (fun _ c => cp c.AH) (101 / 100)
  hBh : DgB δ K (fun _ c => cp c.BH) (201 / 100)

lemma beta_281 : betaOf ((281 : ℝ) / 1000) = 1719 / 719 := by
  unfold betaOf
  norm_num

lemma v_281 : vOf ((281 : ℝ) / 1000) = 2719 / 719 := by
  unfold vOf
  rw [beta_281]
  norm_num

/-- The atoms hold on the `δ`-scaled caps, `0 < δ ≤ 1/100`. -/
lemma dg_atoms {δ K : ℝ} (hδ : δ ≤ 1 / 100) (hK : 1 ≤ K) : DgAtoms δ K := by
  have hK0 : 0 ≤ K := by linarith
  have key : ∀ (e κ : ℝ) (X : Caps → ℝ), e ≤ κ →
      (∀ μ c, 1 ≤ μ → CapsScaled ((281 : ℝ) / 1000) δ K μ slowExpF c → X c ≤ K * μ ^ e) →
      DgB δ K (fun _ c => cp (X c)) κ := by
    intro e κ X hle hX
    refine ⟨K, hK0, fun μ hμ c hc => ⟨cp_nonneg _, ?_⟩⟩
    have hμ0 : 0 < μ := by linarith
    refine cp_le (by positivity) ((hX μ c hμ hc).trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hμ hle) hK0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact key (1719 / 719) _ _ le_rfl fun μ c _ hc => by
      have := hc.1.2
      rwa [beta_281] at this
  · exact key (2719 / 719) _ _ le_rfl fun μ c _ hc => by
      have := hc.2.1.2
      rwa [v_281] at this
  · refine key (2 + δ) _ _ (by linarith) fun μ c _ hc => hc.2.2.2.1
  · refine key (3 + δ) _ _ (by linarith) fun μ c _ hc => hc.2.2.2.2.1
  · refine key (5 / 2 + δ) _ _ (by linarith) fun μ c _ hc => hc.2.2.2.2.2.2.1
  · refine key (4 + δ) _ _ (by linarith) fun μ c _ hc => hc.2.2.2.2.2.1
  · refine key (1 + δ) _ _ (by linarith) fun μ c _ hc => hc.2.2.2.2.2.2.2.2.1
  · refine key (2 + δ) _ _ (by linarith) fun μ c _ hc => hc.2.2.2.2.2.2.2.2.2

section Roles

variable {δ K φ : ℝ}

lemma dg_wy (h : DgAtoms δ K) : DgB δ K (fun _ c => wyCap c) (2719 / 719) := by
  have hc4 := c4_pos.le
  exact (h.hW.add' (h.hY.cmul hc4) (by norm_num) le_rfl).add' (DgB.const hc4 (by norm_num)) le_rfl
    le_rfl

lemma dg_root (h : DgAtoms δ K) : DgB δ K (fun _ c => h2Root c) (2219 / 719) :=
  (h.hP.mul h.hY).sqrt.mono (by norm_num)

lemma dg_lead (h : DgAtoms δ K) : DgB δ K (fun _ c => h2Lead c) (4938 / 719) :=
  (h.hP.sqrt.mul (h.hY.rpow (E := 3 / 2) (by norm_num))).mono (by norm_num)

lemma dg_L0 (h : DgAtoms δ K) (hφ : 0 ≤ φ) : DgB δ K (fun _ c => h2L0 φ c) (2719 / 719) := by
  have hc4 := c4_pos.le
  have h1 : DgB δ K (fun _ c => c4 + 2 * wyCap c) (2719 / 719) :=
    (DgB.const hc4 (by norm_num)).add' ((dg_wy h).cmul (by norm_num)) le_rfl le_rfl
  exact h1.cmul (by positivity)

lemma dg_Lc (h : DgAtoms δ K) : DgB δ K (fun _ c => h2Lc c) (2219 / 719) := by
  have hc4 := c4_pos.le
  have hcI := cI_pos.le
  have hcQ := cQ2_nonneg
  exact (((dg_root h).cmul (by positivity)).add' (h.hW.cmul (by norm_num)) le_rfl
    (by norm_num)).add' (DgB.const (by positivity) (by norm_num)) le_rfl le_rfl

lemma dg_Ly (h : DgAtoms δ K) : DgB δ K (fun _ c => h2Ly c) (2219 / 719) := by
  have hc4 := c4_pos.le
  have hcI := cI_pos.le
  exact ((dg_root h).cmul (by positivity)).add' (DgB.const (by positivity) (by norm_num)) le_rfl
    le_rfl

lemma dg_one_add {f : ℝ → Caps → ℝ} {κ : ℝ} (hf : DgB δ K f κ) (hκ : 0 ≤ κ) :
    DgB δ K (fun μ c => f μ c + 1) κ :=
  hf.add' (DgB.const zero_le_one hκ) le_rfl le_rfl

lemma dg_A3 (h : DgAtoms δ K) : DgB δ K (fun μ c => h2A3 μ c) (151 / 100) :=
  (dg_one_add h.hAh (by norm_num)).add' (dg_mu (κ := 3 / 2)) (by norm_num) (by norm_num)

lemma dg_invA3 : DgB δ K (fun μ c => (h2A3 μ c ^ 4)⁻¹) (-6) := by
  refine ⟨1, zero_le_one, fun μ hμ c _ => ?_⟩
  have hμ0 : 0 < μ := by linarith
  have h1 : μ ^ (3 / 2 : ℝ) ≤ h2A3 μ c := by
    unfold h2A3
    have := cp_nonneg c.AH
    linarith
  have h0 : 0 < μ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hμ0 _
  have h2 : 0 < h2A3 μ c := by linarith
  refine ⟨by positivity, ?_⟩
  have h3 : μ ^ (6 : ℝ) ≤ h2A3 μ c ^ 4 := by
    have e : μ ^ (6 : ℝ) = (μ ^ (3 / 2 : ℝ)) ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hμ0.le]
      norm_num
    rw [e]
    exact pow_le_pow_left₀ h0.le h1 4
  rw [one_mul, Real.rpow_neg hμ0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hμ0 _) h3

lemma dg_Price (h : DgAtoms δ K) : DgB δ K (fun μ c => h2Price μ φ c) (703 / 100) := by
  have Bh1 := dg_one_add h.hBh (by norm_num)
  have Ah1 := dg_one_add h.hAh (by norm_num)
  have B1 := dg_one_add h.hB (by norm_num)
  have A1 := dg_one_add h.hA (by norm_num)
  have J1 := dg_one_add (h.hJ.cmul (x := 2) (by norm_num)) (by norm_num)
  have A3 := dg_A3 h
  have t1 : DgB δ K (fun _ c => (cp c.BH + 1) ^ 2) (703 / 100) := Bh1.pow2.mono (by norm_num)
  have t2 : DgB δ K (fun _ c => 900 * (cp c.AH + 1) ^ 2 * (cp c.BH + 1) ^ 2) (703 / 100) :=
    ((Ah1.pow2.cmul (by norm_num)).mul Bh1.pow2).mono (by norm_num)
  have t3 : DgB δ K (fun _ c => (cp c.BS + 1) ^ 2) (703 / 100) := B1.pow2.mono (by norm_num)
  have t4 : DgB δ K (fun μ c => 226 * h2A3 μ c ^ 2 * (2 * cp c.JS + 1)) (703 / 100) :=
    ((A3.pow2.cmul (by norm_num)).mul J1).mono (by norm_num)
  have t5 : DgB δ K (fun μ c => 26 * (cp c.BH + 1) ^ 4 * (cp c.AS + 1) ^ 2 / h2A3 μ c ^ 4)
      (703 / 100) :=
    ((((Bh1.pow4.cmul (x := 26) (by norm_num)).mul A1.pow2).mul dg_invA3).mono
      (by norm_num)).congr fun _ _ => div_eq_mul_inv _ _
  have t6 : DgB δ K (fun _ _ => 6 * (4 * φ ^ 2 + 4)) (703 / 100) :=
    DgB.const (by positivity) (by norm_num)
  exact ((((t1.add t2).add t3).add t4).add t5).add t6

/-- The polynomial `budgetPoly` of the slow layer has degree `2.01 + 3v`, the worst monomial being
`A_S y Γ` (`slow_degree` of `Slow/Main.lean` says the same at `δ ≤ 1/16`, for the threshold
`qS`). -/
lemma dg_budget (h : DgAtoms δ K) (hφ : 0 ≤ φ) :
    DgB δ K (fun _ c => budgetPoly φ c) (27 / 2) := by
  have hφc : DgB δ K (fun _ _ => φ) 0 := DgB.const hφ le_rfl
  have hc4 := c4_pos.le
  have Ga : DgB δ K (fun _ c => cp c.yF + (cp c.WS + cp c.yF + φ) * (cp c.BS + cp c.yF + φ))
      (5438 / 719) := by
    have a1 := (h.hW.add' h.hY (by norm_num) le_rfl).add' hφc le_rfl (by norm_num)
    have a2 := (h.hB.add' h.hY (by norm_num) le_rfl).add' hφc le_rfl (by norm_num)
    exact h.hY.add' (a1.mul a2) (by norm_num) (by norm_num)
  have t1 : DgB δ K (fun _ _ => (1 : ℝ)) (27 / 2) := DgB.const zero_le_one (by norm_num)
  have t2 := h.hY.pow2.mono (κ' := 27 / 2) (by norm_num)
  have t3 := (h.hY.mul Ga).mono (κ' := 27 / 2) (by norm_num)
  have t4 := (((h.hA.mul h.hY).add' (h.hW.mul h.hP) le_rfl (by norm_num)).mul Ga).mono
    (κ' := 27 / 2) (by norm_num)
  have t5 : DgB δ K (fun _ c => cp c.yF ^ 3) (27 / 2) :=
    ((h.hY.pow2.mul h.hY).mono (by norm_num)).congr fun _ _ => by ring
  have a3 : DgB δ K (fun _ c => cp c.AS + cp c.PF + cp c.WS + cp c.yF + φ) (2719 / 719) :=
    (((h.hA.add' h.hP (by norm_num) (by norm_num)).add' h.hW le_rfl (by norm_num)).add'
      h.hY le_rfl (by norm_num)).add' hφc le_rfl (by norm_num)
  have t6 := ((a3.cmul hφ).mul Ga).mono (κ' := 27 / 2) (by norm_num)
  have a4 : DgB δ K (fun _ c => cp c.WS + cp c.yF + cp c.BS + φ) (2719 / 719) :=
    ((h.hW.add' h.hY (by norm_num) le_rfl).add' h.hB le_rfl (by norm_num)).add'
      hφc le_rfl (by norm_num)
  have t7 := (a4.cmul hφ).mono (κ' := 27 / 2) (by norm_num)
  have a5 : DgB δ K (fun _ c => cp c.WS + cp c.BS + 1) (301 / 100) :=
    dg_one_add (h.hW.add' h.hB (by norm_num) le_rfl) (by norm_num)
  have t8 := (h.hY.pow2.mul a5).mono (κ' := 27 / 2) (by norm_num)
  have hsum := ((((((t1.add t2).add t3).add t4).add t5).add t6).add t7).add t8
  exact (hsum.cmul (x := 2 ^ 11 * (1 + c4) ^ 2) (by positivity)).congr fun _ _ => rfl

lemma dg_hSrc (h : DgAtoms δ K) (hφ : 0 ≤ φ) : DgB δ K (fun _ c => hSrc φ c) (27 / 2) := by
  have hc4 := c4_pos.le
  have a1 := (h.hW.add' (h.hY.cmul hc4) (by norm_num) le_rfl).add'
    (DgB.const hc4 (by norm_num)) le_rfl le_rfl
  have a2 : DgB δ K (fun _ c => cp c.BS + cp c.yF + 1) (2719 / 719) :=
    dg_one_add (h.hB.add' h.hY (by norm_num) le_rfl) (by norm_num)
  exact ((a1.cmul (x := 8) (by norm_num)).mul a2).add' (DgB.const hφ (by norm_num))
    (by norm_num) le_rfl

lemma dg_Hn (h : DgAtoms δ K) (hφ : 0 ≤ φ) : DgB δ K (fun _ c => h2Hn φ c) 8 := by
  have hc4 := c4_pos.le
  have hb := cBil_nonneg
  have a1 := (dg_one_add ((h.hB.add' h.hY (by norm_num) le_rfl).add' h.hW le_rfl (by norm_num))
    (by norm_num)).cmul (x := 32 * (1 + c4) * φ) (by positivity)
  have t1 := (a1.pow2.cmul (x := 16) (by norm_num)).mono (κ' := 8) (by norm_num)
  have a2 := (dg_Ly h).add' (dg_L0 h hφ) (by norm_num) le_rfl
  have t2 := ((h.hB.cmul hb).mul a2).mono (κ' := 8) (by norm_num)
  exact t1.add t2

/-- The barrier level is at least of degree `4`: `W_*⁻¹ ≲ μ⁻⁴` on scaled caps, from the lower
bound `P_F ≥ μ^β/K` of `CapsScaled` (the true degree is `2(β(1+σ) + 1 − σ) = 2v`, which is the same
as that of `H_n`; it is not needed: `role32 ≲ μ⁴` is far below `d`). -/
lemma dg_invW {CH₀ : ℝ} (hCH₀ : 0 < CH₀) (hK : 1 ≤ K) (hφ : 0 ≤ φ) :
    DgB δ K (fun μ c => (WStar 1 c.PF (resCoeff (281 / 1000) CH₀ μ φ c))⁻¹) (-4) := by
  have hK0 : 0 < K := by linarith
  set e : ℝ := CH₀ * (1 / K) ^ ((281 : ℝ) / 1000) / K with he
  have he0 : 0 < e := by positivity
  refine ⟨(e ^ 2)⁻¹, by positivity, fun μ hμ c hc => ?_⟩
  have hμ0 : 0 < μ := by linarith
  have hlow : μ ^ betaOf ((281 : ℝ) / 1000) / K ≤ c.PF := hc.1.1
  rw [beta_281] at hlow
  have hμ2 : μ ^ 2 ≤ μ ^ ((1719 : ℝ) / 719) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hμ (by norm_num)
  have h1 : μ ^ 2 / K ≤ c.PF := (div_le_div_of_nonneg_right hμ2 hK0.le).trans hlow
  have hμ21 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ
  have h2 : 1 / K ≤ c.PF := (div_le_div_of_nonneg_right hμ21 hK0.le).trans h1
  have hA0 : 0 < c.PF := lt_of_lt_of_le (by positivity) h2
  have hρ : 1 ≤ rhoOf μ φ := by
    unfold rhoOf
    linarith
  have hρ' : 1 ≤ rhoOf μ φ ^ (1 - (281 : ℝ) / 1000) := Real.one_le_rpow hρ (by norm_num)
  have hAθ : (1 / K) ^ ((281 : ℝ) / 1000) ≤ c.PF ^ ((281 : ℝ) / 1000) :=
    Real.rpow_le_rpow (by positivity) h2 (by norm_num)
  have hK' : 0 < (1 / K) ^ ((281 : ℝ) / 1000) := by positivity
  set B := resCoeff (281 / 1000) CH₀ μ φ c with hB
  have hB1 : CH₀ * (1 / K) ^ ((281 : ℝ) / 1000) ≤ B := by
    rw [hB]
    unfold resCoeff
    calc CH₀ * (1 / K) ^ ((281 : ℝ) / 1000)
        ≤ CH₀ * 1 * c.PF ^ ((281 : ℝ) / 1000) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hAθ hCH₀.le
      _ ≤ _ := by gcongr
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB1
  have hAB : e * μ ^ 2 ≤ c.PF * B := by
    have := mul_le_mul h1 hB1 (by positivity) hA0.le
    calc e * μ ^ 2 = μ ^ 2 / K * (CH₀ * (1 / K) ^ ((281 : ℝ) / 1000)) := by
          rw [he]
          ring
      _ ≤ _ := this
  have hW : e ^ 2 * μ ^ 4 ≤ WStar 1 c.PF B := by
    unfold WStar bStar dZero
    have h3 : (e * μ ^ 2) ^ 2 ≤ (c.PF * B) ^ 2 := pow_le_pow_left₀ (by positivity) hAB 2
    have e2 : 33 / 32 * (1 * c.PF * B / (2 / 3)) ^ 2 = 297 / 128 * (c.PF * B) ^ 2 := by ring
    rw [e2]
    have h4 : (e * μ ^ 2) ^ 2 = e ^ 2 * μ ^ 4 := by ring
    rw [h4] at h3
    have h5 : 0 ≤ (c.PF * B) ^ 2 := sq_nonneg _
    linarith
  have hpos : 0 < e ^ 2 * μ ^ 4 := by positivity
  have hWpos : 0 < WStar 1 c.PF B := lt_of_lt_of_le hpos hW
  refine ⟨hWpos.le.trans' (le_refl _) |> fun _ => inv_nonneg.2 hWpos.le, ?_⟩
  have e3 : (e ^ 2)⁻¹ * μ ^ (-4 : ℝ) = (e ^ 2 * μ ^ 4)⁻¹ := by
    rw [Real.rpow_neg hμ0.le, mul_inv]
    congr 2
    exact_mod_cast Real.rpow_natCast μ 4
  rw [e3]
  exact inv_anti₀ hpos hW

lemma dg_role32 {CH₀ : ℝ} (h : DgAtoms δ K) (hCH₀ : 0 < CH₀) (hK : 1 ≤ K) (hφ : 0 ≤ φ) :
    DgB δ K (fun μ c => role32 (281 / 1000) CH₀ μ φ c) (27 / 2) := by
  have h1 := ((dg_Hn h hφ).cmul (x := 128) (by norm_num)).mul (dg_invW (δ := δ) hCH₀ hK hφ)
  exact (h1.mono (by norm_num)).congr fun _ _ => div_eq_mul_inv _ _

/-- The threshold has degree `27/2` on `δ`-scaled caps, `δ ≤ 1/100`.  The worst role is `31price`,
`(100/49)((β + v)/2 + 7.03/2) ≈ 13.47`; the next ones are `budgetPoly` (`≈ 13.36`), `role28`
(`≈ 13.13`), `role16/17` (`(100/29) v ≈ 13.04`), `role31mix` (`≈ 12.84`). -/
theorem dg_threshold {CH₀ : ℝ} (h : DgAtoms δ K) (hCH₀ : 0 < CH₀) (hK : 1 ≤ K) (hφ : 0 ≤ φ) :
    DgB δ K (fun μ c => h2Threshold (281 / 1000) CH₀ μ φ c) (27 / 2) := by
  have hc4 := c4_pos.le
  have hcI := cI_pos.le
  have hcQ := cQ2_nonneg
  have hSt := cStat2_pos.le
  have hHe := cHeat2_pos.le
  have hPC := profC_pos.le
  have hFar := cFar_nonneg
  have hMc := h2Mc_nonneg
  have hBil := cBil_nonneg
  have hSr := cSrc_nonneg
  have t0 : DgB δ K (fun _ _ => (1 : ℝ)) (27 / 2) := DgB.const zero_le_one (by norm_num)
  have t1 := dg_budget h hφ
  have t2 : DgB δ K (fun _ c => 32 * c4 * cp c.yF ^ 2) (27 / 2) :=
    (h.hY.pow2.cmul (by positivity)).mono (by norm_num)
  have t3 : DgB δ K (fun _ _ => 2 * φ) (27 / 2) := DgB.const (by positivity) (by norm_num)
  have t4 : DgB δ K (fun _ c => 16 * c4 * cp c.yF) (27 / 2) :=
    (h.hY.cmul (by positivity)).mono (by norm_num)
  have rr : ∀ x : ℝ, 0 ≤ x → DgB δ K (fun _ c => (x * profC * cp c.yF) ^ (100 / 29 : ℝ) +
      (x * cp c.yF) ^ 2) (27 / 2) := fun x hx =>
    (((h.hY.cmul (x := x * profC) (by positivity)).rpow (E := 100 / 29) (by norm_num)).add'
      (h.hY.cmul hx).pow2 (by norm_num) (by norm_num))
  have t5 : DgB δ K (fun _ c => role16 c) (27 / 2) := rr (2 ^ 8 * cStat2) (by positivity)
  have t6 : DgB δ K (fun _ c => role17 c) (27 / 2) := rr (2 ^ 8 * cHeat2) (by positivity)
  have t7 : DgB δ K (fun _ c => role31far c) (27 / 2) :=
    ((dg_lead h).cmul (by positivity)).mono (by norm_num)
  have m1 : DgB δ K (fun _ c => cp c.yF * (16 * cp c.WS + 32 * c4)) (2719 / 719 + 251 / 100) :=
    h.hY.mul ((h.hW.cmul (by norm_num)).add' (DgB.const (by positivity) (by norm_num))
      le_rfl le_rfl)
  have t8 : DgB δ K (fun _ c => role31mix c) (27 / 2) :=
    ((m1.cmul (x := 2 ^ 6 * h2Mc) (by positivity)).rpow (E := 100 / 49) (by norm_num)).mono
      (by norm_num)
  have t9 : DgB δ K (fun _ c => role31psi φ c) (27 / 2) :=
    (((dg_L0 h hφ).cmul (x := 2 ^ 6 * h2Mc) (by positivity)).rpow (E := 100 / 49)
      (by norm_num)).mono (by norm_num)
  have hPr : DgB δ K (fun μ c => h2Price μ φ c) (703 / 100) := dg_Price h
  have m2 : DgB δ K (fun μ c => h2Ly c * Real.sqrt (h2Price μ φ c)) (2219 / 719 + 703 / 100 / 2) :=
    (dg_Ly h).mul hPr.sqrt
  have t10 : DgB δ K (fun μ c => role31price μ φ c) (27 / 2) :=
    ((m2.cmul (x := 2 ^ 6 * h2Mc) (by positivity)).rpow (E := 100 / 49) (by norm_num)).mono
      (by norm_num)
  have m3 : DgB δ K (fun _ c => 1 + h2Lc c) (2219 / 719) :=
    (DgB.const (κ := 0) zero_le_one le_rfl).add' (dg_Lc h) (by norm_num) le_rfl
  have r1 := ((h.hB.cmul (x := 2 ^ 6 * cBil) (by positivity)).mul m3).mono (κ' := 27 / 2)
    (by norm_num)
  have r2 := ((h.hB.cmul (x := 2 ^ 8 * cBil) (by positivity)).mul (dg_L0 h hφ)).mono
    (κ' := 27 / 2) (by norm_num)
  have r3 := ((h.hB.cmul (x := 2 ^ 8 * cBil) (by positivity)).mul ((dg_Ly h).mul hPr)).mono
    (κ' := 27 / 2) (by norm_num)
  have t11 : DgB δ K (fun μ c => role28 μ φ c) (27 / 2) := (r1.add r2).add r3
  have t12 : DgB δ K (fun _ c => role28src2 φ c) (27 / 2) :=
    (dg_hSrc h hφ).cmul (x := 2 ^ 7 * cSrc) (by positivity)
  have t13 := dg_role32 h hCH₀ hK hφ
  exact ((((((((((((t0.add t1).add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add
    t10).add t11).add t12).add t13

end Roles

/-- **The degree lemma**: the threshold has fixed-force degree `27/2 < d = 9876/719 ≈ 13.74` at
the exponents `slowExpF` of the slow layer. -/
theorem h2_degree {CH₀ : ℝ} (hCH₀ : 0 < CH₀) :
    DegreeBelow (281 / 1000) (9876 / 719) slowExpF (h2Threshold (281 / 1000) CH₀) := by
  intro φ hφ
  refine ⟨1 / 100, by norm_num, fun δ K _ hδ hK => ?_⟩
  obtain ⟨C, -, hb⟩ := dg_threshold (dg_atoms hδ hK) hCH₀ hK hφ
  exact ⟨C, 27 / 2, by norm_num, fun μ hμ c hc => (hb μ hμ c hc).2⟩

/-! ### F. The target -/

/-- **E8** (spec §1.2): the `H²` energy interface of the fixed-force proof, at `σ = 281/1000`, on
pieces of length `Tp = 2`, at the exponents `slowExpF`.  Here `K₂ = h2K₂` and `m₀ = 1/4` are
absolute; the threshold is `h2Threshold (281/1000) CH`.  See `h2EnergyInterface_uniform` for the
version with a threshold uniform over `CH ≥ 1`. -/
theorem h2EnergyInterface : ∀ CH : ℝ, 0 < CH → ResH2 (281 / 1000) CH →
    ∃ (K₂ m₀ : ℝ) (q₂ : ℝ → ℝ → Caps → ℝ), 0 ≤ K₂ ∧ 0 ≤ m₀ ∧ m₀ ≤ 1 / 4 ∧
      (∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
        H2EnergyInterface (281 / 1000) CH μ φ 2 K₂ m₀ (q₂ μ φ) nearN) ∧
      DegreeBelow (281 / 1000) (9876 / 719) slowExpF q₂ := by
  intro CH hCH hres
  refine ⟨h2K₂, h2m₀, h2Threshold (281 / 1000) CH, h2K₂_nonneg, by unfold h2m₀; norm_num,
    by unfold h2m₀; norm_num, fun μ φ hμ hφ => ?_, h2_degree hCH⟩
  exact h2EnergyInterface_of_lower (by norm_num) (by norm_num) hCH le_rfl hres hμ hφ

/-- **E8, uniform form**: `K₂`, `m₀` and `q₂` are chosen before `CH`, for all resonant constants
`CH ≥ 1` (the form the assembly quantifies; it passes `max CH 1`).  The threshold is
`h2Threshold (281/1000) 1`.  The restriction `1 ≤ CH` is forced: `q₂` has to pay
`H_n/q ≤ W_*/128` and `W_* ∝ CH²`, so no threshold is uniform as `CH → 0`. -/
theorem h2EnergyInterface_uniform :
    ∃ (K₂ m₀ : ℝ) (q₂ : ℝ → ℝ → Caps → ℝ), 0 ≤ K₂ ∧ 0 ≤ m₀ ∧ m₀ ≤ 1 / 4 ∧
      (∀ CH : ℝ, 1 ≤ CH → ResH2 (281 / 1000) CH → ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
        H2EnergyInterface (281 / 1000) CH μ φ 2 K₂ m₀ (q₂ μ φ) nearN) ∧
      DegreeBelow (281 / 1000) (9876 / 719) slowExpF q₂ := by
  refine ⟨h2K₂, h2m₀, h2Threshold (281 / 1000) 1, h2K₂_nonneg, by unfold h2m₀; norm_num,
    by unfold h2m₀; norm_num, fun CH hCH hres μ φ hμ hφ => ?_, h2_degree one_pos⟩
  exact h2EnergyInterface_of_lower (by norm_num) (by norm_num) one_pos hCH hres hμ hφ

end OVNS.Quant.H2

end
