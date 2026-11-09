import OddViscousNS.Quant.Joint.Sources.Below
import OddViscousNS.Quant.Energy.H2.Identity

/-!
# J4: the histories handed to E5-J and E8-J

These are the source constants of the TeX joint proof ("the independent source constants satisfy
`C_hist ≲ R³`, `C_y ≲ R^{5/2}`, with both actual time pieces and genuine partners"), consumed by the
force pairs of LOCAL363, LOCAL479.  Nothing here is used by E7-P.

* Role 19, `hnorm_three_slowCorr_le`, `slow_three_le`: `‖R_S‖₃ ≤ (16 c₄ y/q) c_F`, whence the
  transform `c_S ≤ c_y + c_F/128`.  The threshold pays it (`two11_le_jointBudget`);
* `C_y`, `SlowOut.cy_piece_le`: `∫ c_y² ≤ 4 P_S(1)` on a piece of length `≤ 4`, from the slot `clip`
  on four units.  So `C_y ≲ R^{5/2}`;
* `C_hist`, `slow_three_sq_le`: `∫ c_S² ≤ 2 ∫ c_y² + J_{3,pre}/2¹³`.  So `C_hist² ≲ R⁵ + U R⁴`, that
  is `C_hist ≲ R^{5/2}` up to the subpower, below the `R³` of the TeX (`chistSq_le`).

The filter force is in `Sources/Filter.lean`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace OVNS.Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### Role 19 -/

/-- `‖R_S‖₃ ≤ (16 c₄ ‖F‖₂/q) ‖F‖₃`, at a time with `F ∈ H³`. -/
theorem hnorm_three_slowCorr_le (hr : r ≠ 0) (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (PiF (actual r g y u))) :
    InH 3 (slowCorr r g y u) ∧
      hnorm 3 (slowCorr r g y u) ≤ 16 * c4 * fastNorm 2 r g y u / |r| * fastNorm 3 r g y u := by
  have hF := (actual_adm h hu huT).PiF
  have hmz : MZ 3 (PiF (actual r g y u)) := ⟨hF3, hF.mean⟩
  have hF1 := summable_wiener hF.inH
  obtain ⟨hI, hle⟩ := hnorm_kinN_le_of_one_le (τ := r * u) hr (by norm_num : (1 : ℝ) ≤ 3) hmz hmz
    hF1 hF1
  have hr' : 0 < |r| := abs_pos.mpr hr
  have e8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
  rw [e8] at hle
  refine ⟨hI, hle.trans ?_⟩
  have hw := wiener_le hF.mz
  have n3 := hnorm_nonneg 3 (PiF (actual r g y u))
  have e : 16 * c4 * fastNorm 2 r g y u / |r| * fastNorm 3 r g y u =
      8 / |r| * (2 * (c4 * hnorm 2 (PiF (actual r g y u)) * hnorm 3 (PiF (actual r g y u)))) := by
    unfold fastNorm
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := mul_le_mul_of_nonneg_right hw n3
  linarith

/-- The threshold pays role 19. -/
lemma two11_le_jointBudget (hφ : 0 ≤ φ) (caps : Caps) :
    2 ^ 11 * c4 * cp caps.yF ≤ jointBudget φ caps := by
  have hc := c4_pos
  have hY := cp_nonneg caps.yF
  have hW := cp_nonneg caps.WS
  have hj := capJ_nonneg caps
  unfold jointBudget
  rw [← sub_nonneg]
  ring_nf
  positivity

/-- **Role 19**: the transform `c_S ≤ c_y + c_F/128`, at a time with `F, y_S ∈ H³`. -/
theorem slow_three_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (PiF (actual r g y u)))
    (hz : InH 3 (corrSlow r g y u)) {Y : ℝ} (hY : fastNorm 2 r g y u ≤ Y)
    (hq : 2 ^ 11 * c4 * Y ≤ |r|) :
    slowNorm 3 r g y u ≤ hnorm 3 (corrSlow r g y u) + fastNorm 3 r g y u / 128 := by
  have hr' : 0 < |r| := abs_pos.mpr hr
  have hc := c4_pos
  obtain ⟨hI, hle⟩ := hnorm_three_slowCorr_le hr h hu huT hF3
  have e : PiS (actual r g y u) = corrSlow r g y u - slowCorr r g y u := by simp [corrSlow]
  have h1 : slowNorm 3 r g y u ≤ hnorm 3 (corrSlow r g y u) + hnorm 3 (slowCorr r g y u) := by
    unfold slowNorm
    rw [e]
    exact hnorm_sub_le hz hI
  have n2 : 0 ≤ fastNorm 2 r g y u := hnorm_nonneg _ _
  have n3 : 0 ≤ fastNorm 3 r g y u := hnorm_nonneg _ _
  have h2 : 16 * c4 * fastNorm 2 r g y u / |r| * fastNorm 3 r g y u ≤ fastNorm 3 r g y u / 128 := by
    have h3 : 16 * c4 * fastNorm 2 r g y u / |r| ≤ 1 / 128 := by
      rw [div_le_iff₀ hr']
      have := mul_le_mul_of_nonneg_left hY (by positivity : 0 ≤ 2 ^ 11 * c4)
      linarith
    have := mul_le_mul_of_nonneg_right h3 n3
    linarith
  linarith

/-! ### `C_y`: the unit clips on a piece -/

lemma slowPrice_mono {C ex R ℓ ℓ' : ℝ} (h0 : 0 ≤ C * ex) (hR : 0 ≤ R) (h : ℓ ≤ ℓ') :
    slowPrice C ex R ℓ ≤ slowPrice C ex R ℓ' := by
  unfold slowPrice
  have hR5 : 0 ≤ R ^ 5 := by positivity
  have := mul_le_mul_of_nonneg_right h hR5
  have h2 : R ^ 4 + ℓ * R ^ 5 ≤ R ^ 4 + ℓ' * R ^ 5 := by linarith
  have := mul_le_mul_of_nonneg_left h2 h0
  linarith

/-- **`C_y`**: `∫ c_y² ≤ 4 P_S(1)` on a piece of length at most four, from the slot `clip`. -/
theorem SlowOut.cy_piece_le {C ex R : ℝ} {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} {s t : ℝ}
    (hO : SlowOut C ex R Sl r g y s t) (h0 : 0 ≤ C * ex) (hR : 0 ≤ R) (hst : s ≤ t)
    (hlen : t - s ≤ 4) :
    ∫ u in s..t, hnorm 3 (corrSlow r g y u) ^ 2 ≤ 4 * slowPrice C ex R 1 := by
  set d := (t - s) / 4 with hd
  have hd0 : 0 ≤ d := by simp only [hd]; linarith
  have hd1 : d ≤ 1 := by simp only [hd]; linarith
  set f := fun u => hnorm 3 (corrSlow r g y u) ^ 2 with hf
  have hI : IntervalIntegrable f volume s t := hO.cy_int
  have sub : ∀ a b : ℝ, s ≤ a → a ≤ b → b ≤ t → IntervalIntegrable f volume a b :=
    fun a b ha hab hb => hI.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le hst]
      exact Icc_subset_Icc ha hb)
  have piece : ∀ a b : ℝ, s ≤ a → a ≤ b → b ≤ t → b - a ≤ d →
      ∫ u in a..b, f u ≤ slowPrice C ex R 1 := fun a b ha hab hb hl =>
    (hO.clip a b ha hab hb (hl.trans hd1)).trans (slowPrice_mono h0 hR (hl.trans hd1))
  have h1 : s ≤ s + d := by linarith
  have h2 : s + d ≤ s + 2 * d := by linarith
  have h3 : s + 2 * d ≤ s + 3 * d := by linarith
  have h4 : s + 3 * d ≤ t := by simp only [hd]; linarith
  have i1 := sub s (s + d) le_rfl h1 (by linarith)
  have i2 := sub (s + d) (s + 2 * d) h1 h2 (by linarith)
  have i3 := sub (s + 2 * d) (s + 3 * d) (by linarith) h3 h4
  have i4 := sub (s + 3 * d) t (by linarith) h4 le_rfl
  have e : ∫ u in s..t, f u = (∫ u in s..(s + d), f u) + (∫ u in (s + d)..(s + 2 * d), f u) +
      (∫ u in (s + 2 * d)..(s + 3 * d), f u) + ∫ u in (s + 3 * d)..t, f u := by
    rw [intervalIntegral.integral_add_adjacent_intervals i1 i2,
      intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3,
      intervalIntegral.integral_add_adjacent_intervals ((i1.trans i2).trans i3) i4]
  have p1 := piece s (s + d) le_rfl h1 (by linarith) (by linarith)
  have p2 := piece (s + d) (s + 2 * d) h1 h2 (by linarith) (by linarith)
  have p3 := piece (s + 2 * d) (s + 3 * d) (by linarith) h3 h4 (by linarith)
  have p4 := piece (s + 3 * d) t (by linarith) h4 le_rfl (by simp only [hd]; linarith)
  show ∫ u in s..t, f u ≤ _
  rw [e]
  linarith

/-! ### `C_hist` -/

/-- **`C_hist`**, squared (LOCAL363: `‖c_S‖_{L²} ≤ C_y + √(2 J_{3,pre})/128`): on an interval of
length at most `ℓ` where the caps hold, at the threshold,
`∫ c_S² ≤ 2 ∫ c_y² + J_{3,pre}(ℓ)/2¹³`. -/
theorem slow_three_sq_le (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t ℓ : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ ℓ)
    (hthr : jointBudget φ caps ≤ |r|) (hP : OnPrefix caps r g y s t) :
    ∫ u in s..t, slowNorm 3 r g y u ^ 2 ≤
      2 * (∫ u in s..t, hnorm 3 (corrSlow r g y u) ^ 2) + J3pre ℓ caps / 2 ^ 13 := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  obtain ⟨hf1, hf2, -⟩ := jointBudget_floors hφ caps
  have hq : 1 ≤ |r| := hf1.trans hthr
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hq; linarith
  have ht0 := hs.trans hst
  have hJ := fast_three_le h hr0 hs hst ht hlen (hf2.trans hthr) hP
  have hq19 := (two11_le_jointBudget hφ caps).trans hthr
  have hPy := (heatPair_corrSlow h hr0 (σ := 2) (Or.inr (Or.inr rfl)) ht0 ht).mono hs le_rfl
  have hz3 := hPy.ae_inH hst
  have hzI := hPy.intervalIntegrable_dissipation hst
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at hz3 hzI
  have hS : IntervalIntegrable (fun u => slowNorm 3 r g y u ^ 2) volume s t :=
    H2.slow_c3_integrable h hs hst ht
  have hF := intervalIntegrable_fast_three h hs hst ht
  have hae : ∀ᵐ u ∂(volume.restrict (Icc s t)), slowNorm 3 r g y u ^ 2 ≤
      2 * hnorm 3 (corrSlow r g y u) ^ 2 + 1 / 2 ^ 13 * fastNorm 3 r g y u ^ 2 := by
    filter_upwards [ae_fast_three h hs hst ht, hz3, ae_restrict_mem measurableSet_Icc]
      with u hF3 hz hu
    have hb := slow_three_le h hr0 (hs.trans hu.1) (lt_lifespan hu.2 ht) hF3 hz
      (((hP.1 u hu).2.1).trans (le_cp _)) hq19
    have n0 : 0 ≤ slowNorm 3 r g y u := hnorm_nonneg _ _
    have h1 := pow_le_pow_left₀ n0 hb 2
    nlinarith [sq_nonneg (hnorm 3 (corrSlow r g y u) - fastNorm 3 r g y u / 128)]
  have hm := intervalIntegral.integral_mono_ae_restrict hst hS
    ((hzI.const_mul 2).add (hF.const_mul (1 / 2 ^ 13))) hae
  have hval : ∫ u in s..t, (2 * hnorm 3 (corrSlow r g y u) ^ 2 +
      1 / 2 ^ 13 * fastNorm 3 r g y u ^ 2) =
      2 * (∫ u in s..t, hnorm 3 (corrSlow r g y u) ^ 2) +
        1 / 2 ^ 13 * ∫ u in s..t, fastNorm 3 r g y u ^ 2 := by
    rw [intervalIntegral.integral_add (hzI.const_mul 2) (hF.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hval] at hm
  have h2 : 1 / 2 ^ 13 * (∫ u in s..t, fastNorm 3 r g y u ^ 2) ≤ 1 / 2 ^ 13 * J3pre ℓ caps :=
    mul_le_mul_of_nonneg_left hJ (by norm_num)
  linarith

/-- **`C_hist²`** on a piece of length at most four: `8 P_S(1) + J_{3,pre}(4)/2¹³`. -/
def chistSq (C ex R : ℝ) (caps : Caps) : ℝ := 8 * slowPrice C ex R 1 + J3pre 4 caps / 2 ^ 13

/-- **`‖c_S‖_{L²}` on a piece** (LOCAL363, slot `C_hist`), from the slot `clip` of `SlowOut` and the
fast `H³` dissipation of the same piece; neither `J_post` nor a later energy is used. -/
theorem slow_three_piece_le (h : ActualSol μ φ r g y Ty) {C ex R : ℝ}
    {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} {caps : Caps} {s t : ℝ}
    (hO : SlowOut C ex R Sl r g y s t) (h0 : 0 ≤ C * ex) (hR : 0 ≤ R) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 4) (hthr : jointBudget φ caps ≤ |r|)
    (hP : OnPrefix caps r g y s t) :
    ∫ u in s..t, slowNorm 3 r g y u ^ 2 ≤ chistSq C ex R caps := by
  have h1 := slow_three_sq_le h hs hst ht hlen hthr hP
  have h2 := hO.cy_piece_le h0 hR hst hlen
  unfold chistSq
  linarith

/-- `J_{3,pre}(4) ≲ U R⁴ ≤ R⁵` on the scaled caps. -/
theorem J3pre_four_le {K c R₀ X R : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c) (hdom : JDom R₀ X R) {caps : Caps}
    (hcaps : CapsScaledJ K c X R caps) :
    J3pre 4 caps ≤ 2 ^ 18 * (1 + c4) ^ 2 * (K * Ex c R) ^ 4 * (jointU X * R ^ 4) := by
  obtain ⟨-, ⟨-, hY⟩, -, -, -, hJ, hW, -, -, -⟩ := hcaps
  have hR1 := hdom.one_lt_R
  have hR0 := hdom.R_pos
  have hU1 := hdom.one_lt_U
  have hT0 := hdom.T_pos
  have hT2 := hdom.T_sq
  have hEc : 1 ≤ Ex c R := hdom.one_le_Ex hc
  have hc4 := c4_pos
  set E := K * Ex c R with hE
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le hK hEc
  have hE0 : 0 ≤ E := by linarith
  set ρ := R ^ ((3 : ℝ) / 2) with hρ
  have hρ2 : ρ ^ 2 = R ^ 3 := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le, ← Real.rpow_natCast]
    norm_num
  have hRρ : R ≤ ρ := by
    calc R = R ^ (1 : ℝ) := (Real.rpow_one R).symm
      _ ≤ ρ := Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num)
  have h1ρ : 1 ≤ ρ := hR1.le.trans hRρ
  have hU : jointU X ≤ R := by
    refine hdom.U_le.trans ?_
    calc R ^ ((1 : ℝ) / 8) ≤ R ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num)
      _ = R := Real.rpow_one R
  have hT : jointT X R ≤ R := by
    have h1 : jointT X R ≤ Real.sqrt (R * R) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hU hR0.le)
    rwa [Real.sqrt_mul_self hR0.le] at h1
  have hT1 : 1 ≤ jointT X R := by
    have h1 : 1 ≤ jointT X R ^ 2 := by
      rw [hT2]
      exact one_le_mul_of_one_le_of_one_le hU1.le hR1.le
    nlinarith
  have hY0 := cp_nonneg caps.yF
  have hW0 := cp_nonneg caps.WS
  have hJ0 := cp_nonneg caps.JS
  have hY' : cp caps.yF ≤ E * jointT X R := cp_le (by positivity) hY
  have hW' : cp caps.WS ≤ E * ρ := cp_le (by positivity) (by simpa [slowExpHA] using hW)
  have hJ' : cp caps.JS ≤ E * ρ ^ 2 := by
    rw [hρ2]
    refine cp_le (by positivity) ?_
    have e3 : R ^ slowExpHA.eJ = R ^ 3 := by
      simp only [slowExpHA]
      exact_mod_cast Real.rpow_natCast R 3
    rw [← e3]
    exact hJ
  have hET : 1 ≤ E * jointT X R := one_le_mul_of_one_le_of_one_le hE1 hT1
  have hEρ : 1 ≤ E * ρ := one_le_mul_of_one_le_of_one_le hE1 h1ρ
  have hYρ : cp caps.yF ≤ E * ρ :=
    hY'.trans (mul_le_mul_of_nonneg_left (hT.trans hRρ) hE0)
  have hv : cp caps.yF + 1 ≤ 2 * (E * jointT X R) := by linarith
  have hv2 : (cp caps.yF + 1) ^ 2 ≤ 4 * (E ^ 2 * (jointU X * R)) := by
    have := pow_le_pow_left₀ (by linarith) hv 2
    rwa [mul_pow, mul_pow, hT2, show (2 : ℝ) ^ 2 = 4 by norm_num] at this
  have hY2 : cp caps.yF ^ 2 ≤ E ^ 2 * (jointU X * R) := by
    have := pow_le_pow_left₀ hY0 hY' 2
    rwa [mul_pow, hT2] at this
  have hbW : budW caps ≤ (1 + 4 * c4) * (E * ρ) := by
    unfold budW
    nlinarith only [hW', hYρ, hEρ, hc4]
  have hbW0 : 0 ≤ budW caps := by unfold budW; positivity
  have hbW2 : budW caps ^ 2 ≤ (1 + 4 * c4) ^ 2 * (E ^ 2 * ρ ^ 2) := by
    have := pow_le_pow_left₀ hbW0 hbW 2
    rwa [mul_pow, mul_pow] at this
  set Z := E ^ 2 * ρ ^ 2 with hZ
  have hZ1 : 1 ≤ Z := by
    have : 1 ≤ (E * ρ) ^ 2 := one_le_pow₀ hEρ
    rwa [mul_pow] at this
  have hJZ : cp caps.JS ≤ Z := by
    refine hJ'.trans ?_
    rw [hZ]
    have h2 : E ≤ E ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hW4 : 4 * budW caps ^ 2 + c4 ^ 2 * cp caps.JS ≤ 2 ^ 8 * (1 + c4) ^ 2 * Z := by
    have h3 : (1 + 4 * c4) ^ 2 ≤ 16 * (1 + c4) ^ 2 := by nlinarith
    have h4 : (1 + 4 * c4) ^ 2 * Z ≤ 16 * (1 + c4) ^ 2 * Z :=
      mul_le_mul_of_nonneg_right h3 (by linarith)
    have h5 : c4 ^ 2 * cp caps.JS ≤ c4 ^ 2 * Z := mul_le_mul_of_nonneg_left hJZ (by positivity)
    have h6 : c4 ^ 2 * Z ≤ (1 + c4) ^ 2 * Z :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    nlinarith only [hbW2, h4, h5, h6, hZ1, mul_nonneg (sq_nonneg (1 + c4)) (by linarith : 0 ≤ Z)]
  set W₁ := jointU X * R with hW₁
  have hW10 : 0 ≤ W₁ := by positivity
  have hprod : (cp caps.yF + 1) ^ 2 * (4 * budW caps ^ 2 + c4 ^ 2 * cp caps.JS) ≤
      (4 * (E ^ 2 * W₁)) * (2 ^ 8 * (1 + c4) ^ 2 * Z) :=
    mul_le_mul hv2 hW4 (by positivity) (by positivity)
  have e1 : jointU X * R ^ 4 = W₁ * ρ ^ 2 := by
    rw [hW₁, hρ2]
    ring
  have hE2 : 1 ≤ E ^ 2 := one_le_pow₀ hE1
  have hY3 : cp caps.yF ^ 2 ≤ (1 + c4) ^ 2 * (E ^ 4 * (W₁ * ρ ^ 2)) := by
    refine hY2.trans ?_
    have h7 : 1 ≤ ρ ^ 2 := one_le_pow₀ h1ρ
    have h8 : (1 : ℝ) ≤ (1 + c4) ^ 2 := one_le_pow₀ (by linarith)
    have h9 : E ^ 2 * W₁ * 1 ≤ E ^ 2 * W₁ * ρ ^ 2 :=
      mul_le_mul_of_nonneg_left h7 (by positivity)
    have h10 : E ^ 2 * W₁ * ρ ^ 2 ≤ E ^ 4 * (W₁ * ρ ^ 2) := by
      have e : E ^ 4 * (W₁ * ρ ^ 2) = E ^ 2 * (E ^ 2 * W₁ * ρ ^ 2) := by ring
      rw [e]
      exact le_mul_of_one_le_left (by positivity) hE2
    have h11 := le_mul_of_one_le_left (by positivity : 0 ≤ E ^ 4 * (W₁ * ρ ^ 2)) h8
    linarith
  unfold J3pre
  rw [e1]
  have e2 : (4 * (E ^ 2 * W₁)) * (2 ^ 8 * (1 + c4) ^ 2 * Z) =
      2 ^ 10 * (1 + c4) ^ 2 * (E ^ 4 * (W₁ * ρ ^ 2)) := by
    rw [hZ]
    ring
  rw [e2] at hprod
  have hm := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 128)
  have hn : 0 ≤ (1 + c4) ^ 2 * (E ^ 4 * (W₁ * ρ ^ 2)) := by positivity
  nlinarith only [hm, hY3, hn]

/-- **`C_hist ≲ R^{5/2}` up to the subpower** on the scaled caps, below the `R³` of the TeX. -/
theorem chistSq_le {K c R₀ X R C ex : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c) (hdom : JDom R₀ X R)
    (h0 : 0 ≤ C * ex) {caps : Caps} (hcaps : CapsScaledJ K c X R caps) :
    chistSq C ex R caps ≤
      (16 * (C * ex) + 32 * (1 + c4) ^ 2 * K ^ 4 * Ex (4 * c) R) * R ^ 5 := by
  have hR1 := hdom.one_lt_R
  have hR0 := hdom.R_pos
  have hc4 := c4_pos
  have hJ := J3pre_four_le hK hc hdom hcaps
  have hU : jointU X ≤ R := by
    refine hdom.U_le.trans ?_
    calc R ^ ((1 : ℝ) / 8) ≤ R ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num)
      _ = R := Real.rpow_one R
  have hEx : (K * Ex c R) ^ 4 = K ^ 4 * Ex (4 * c) R := by
    rw [show 4 * c = c + (c + (c + c)) by ring, Ex_add, Ex_add, Ex_add]
    ring
  rw [hEx] at hJ
  have hK0 : 0 ≤ K := by linarith
  have hE0 := (Ex_pos (4 * c) R).le
  have hC0 : 0 ≤ (1 + c4) ^ 2 * K ^ 4 * Ex (4 * c) R := by positivity
  have hUR : jointU X * R ^ 4 ≤ R ^ 5 := by
    have e : R ^ 5 = R * R ^ 4 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hU (by positivity)
  have h1 : J3pre 4 caps / 2 ^ 13 ≤ 32 * ((1 + c4) ^ 2 * K ^ 4 * Ex (4 * c) R) * R ^ 5 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 13)]
    have h2 := mul_le_mul_of_nonneg_left hUR hC0
    have e2 : 2 ^ 18 * (1 + c4) ^ 2 * (K ^ 4 * Ex (4 * c) R) * (jointU X * R ^ 4) =
        2 ^ 18 * ((1 + c4) ^ 2 * K ^ 4 * Ex (4 * c) R * (jointU X * R ^ 4)) := by ring
    rw [e2] at hJ
    nlinarith only [hJ, h2]
  have h3 : slowPrice C ex R 1 ≤ 2 * (C * ex) * R ^ 5 := by
    unfold slowPrice
    have h4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR1.le (by norm_num)
    have h5 := mul_le_mul_of_nonneg_left h4 h0
    nlinarith only [h5]
  unfold chistSq
  nlinarith only [h1, h3]

end OVNS.Quant

end
