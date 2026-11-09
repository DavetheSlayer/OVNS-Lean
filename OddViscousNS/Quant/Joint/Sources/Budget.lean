import OddViscousNS.Quant.Joint.Sources.Fast
import OddViscousNS.Quant.Joint.Slow.Main

/-!
# J4: the slow budget at the joint scale

`SlowBudget` is the only property of the slow threshold that E7-P needs beyond the floors
(`slowCapsJoint_of_budget`).  The fixed-force `corrRes_budget` pays it at `budgetPoly`, which is
above `Q = UR³` at the joint caps.  Two changes bring it below `Q`:

1. **Sectors** (`Sources/Fast.lean`): `‖Π_F Q(y,y)‖₁ ≤ 8 Ξ`, with no slow–slow term.  This removes
   the monomial `y W_S B_S ≍ T R^{7/2}`, in both places where `budgetPoly` has it: the fast `H²` law
   and the corrector derivative.
2. **`L²` in time.**  The budget is an `L²_t H¹` bound, so `b_S` may stay in the time integral,
   paid by the cap `∫ b_S² ≤ J_S` of the same interval.  The pointwise cap `B_S` then occurs in no
   monomial, and the source's tied `B_S y² = R²T² = Q` becomes `√J_S y² = U R^{5/2}`.

The threshold is `jointBudget`; it reads `y, W_S, J_S, φ` and no other cap.  Everything is on the
interval `[s, t]` where the caps hold: nothing is taken from a later energy, so there is no
circularity.  See `corrRes_budget_J`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace OVNS.Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### The threshold -/

/-- `√J_S`: the `L²_t` size of `b_S` at the cap. -/
def capJ (caps : Caps) : ℝ := Real.sqrt (cp caps.JS)

lemma capJ_nonneg (caps : Caps) : 0 ≤ capJ caps := Real.sqrt_nonneg _

lemma capJ_sq (caps : Caps) : capJ caps ^ 2 = cp caps.JS := Real.sq_sqrt (cp_nonneg _)

/-- **The joint slow threshold**: `2¹²(1 + c₄)³ ((y + 1)² + φ)(W_S + y + √J_S + 1)`. -/
def jointBudget (φ : ℝ) (caps : Caps) : ℝ :=
  2 ^ 12 * (1 + c4) ^ 3 *
    (((cp caps.yF + 1) ^ 2 + φ) * (cp caps.WS + cp caps.yF + capJ caps + 1))

/-- `W' = W + c₄ Y + 3c₄`: `Ξ ≤ (Y + 1)(W' + c₄ b_S)` (`fastXi_le`). -/
def budW (caps : Caps) : ℝ := cp caps.WS + c4 * cp caps.yF + 3 * c4

/-- The constant part of the `1/q` terms of the `H¹` residual. -/
private def bud0 (φ : ℝ) (caps : Caps) : ℝ :=
  56 * c4 * cp caps.yF * (cp caps.yF + 1) * budW caps +
    16 * φ * (cp caps.WS + 2 * c4 * cp caps.yF + c4) +
    64 * c4 * cp caps.yF ^ 2 * (cp caps.WS + c4)

/-- The coefficient of `b_S` in the `1/q` terms of the `H¹` residual. -/
private def bud1 (φ : ℝ) (caps : Caps) : ℝ :=
  56 * c4 ^ 2 * cp caps.yF * (cp caps.yF + 1) + 16 * c4 * φ + 64 * c4 ^ 2 * cp caps.yF ^ 2

/-- The coefficient of `c_F` in the `1/q` terms of the `H¹` residual. -/
private def bud2 (caps : Caps) : ℝ := 24 * c4 * cp caps.yF

/-- All the coefficients of the budget are dominated monomial by monomial. -/
private lemma budget_alg {c Y W j φ : ℝ} (hc : 0 ≤ c) (hY : 0 ≤ Y) (hW : 0 ≤ W) (hj : 0 ≤ j)
    (hφ : 0 ≤ φ) :
    2 * (2 * (56 * c * Y * (Y + 1) * (W + c * Y + 3 * c) + 16 * φ * (W + 2 * c * Y + c) +
        64 * c * Y ^ 2 * (W + c)) +
      (56 * c ^ 2 * Y * (Y + 1) + 16 * c * φ + 64 * c ^ 2 * Y ^ 2) * j +
      24 * c * Y * Y + 16 * (24 * c * Y) * (Y + 1) * (W + c * Y + 3 * c) +
      12 * (24 * c * Y) * (Y + 1) * c * j) ≤
      2 ^ 12 * (1 + c) ^ 3 * (((Y + 1) ^ 2 + φ) * (W + Y + j + 1)) := by
  rw [← sub_nonneg]
  ring_nf
  positivity

/-- The floors of the threshold. -/
private lemma budget_floors {c Y W j φ : ℝ} (hc : 0 ≤ c) (hY : 0 ≤ Y) (hW : 0 ≤ W) (hj : 0 ≤ j)
    (hφ : 0 ≤ φ) :
    1 ≤ 2 ^ 12 * (1 + c) ^ 3 * (((Y + 1) ^ 2 + φ) * (W + Y + j + 1)) ∧
      2 * φ ≤ 2 ^ 12 * (1 + c) ^ 3 * (((Y + 1) ^ 2 + φ) * (W + Y + j + 1)) ∧
      8 * c * Y ^ 2 ≤ 2 ^ 12 * (1 + c) ^ 3 * (((Y + 1) ^ 2 + φ) * (W + Y + j + 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [← sub_nonneg]
    ring_nf
    positivity

/-- The threshold pays its floors. -/
lemma jointBudget_floors (hφ : 0 ≤ φ) (caps : Caps) :
    1 ≤ jointBudget φ caps ∧ 2 * φ ≤ jointBudget φ caps ∧
      8 * c4 * cp caps.yF ^ 2 ≤ jointBudget φ caps :=
  budget_floors c4_pos.le (cp_nonneg _) (cp_nonneg _) (capJ_nonneg caps) hφ

/-! ### The sizes on the caps -/

/-- `‖ψ‖₂ ≤ 2φ/q`. -/
lemma psi_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    hnorm 2 (psi r 0 g u) ≤ 2 * φ / |r| := by
  have hrpos : 0 < |r| := abs_pos.2 hr
  have hg1 : hnorm 1 g ≤ φ := (hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le
  refine (psi_bound (t₀ := 0) hr h.force_adm u hu).2.trans ?_
  rw [div_le_div_iff_of_pos_right hrpos]
  linarith

/-- The size of the fast output on the caps, where the filter is at most one in `H²`. -/
lemma fastXi_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hq : 2 * φ ≤ |r|) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) {Y W : ℝ} (hY : fastNorm 2 r g y u ≤ Y)
    (hW : slowWiener r g y u ≤ W) :
    fastXi (y u) ≤ (Y + 1) * (W + c4 * Y + 3 * c4 + c4 * slowNorm 2 r g y u) := by
  have hrpos : 0 < |r| := abs_pos.2 hr
  have hc := c4_pos
  have hx := actual_adm h hu huT
  have hψ := psi_adm (r := r) (t₀ := 0) h.force_adm u hu
  have hw := h.sol.adm u hu huT
  have hψ1 : hnorm 2 (psi r 0 g u) ≤ 1 := by
    refine (psi_le h hr hu).trans ?_
    rw [div_le_one hrpos]
    exact hq
  have e : y u = actual r g y u + psi r 0 g u := by simp [actual]
  have eS : PiS (y u) = PiS (actual r g y u) + PiS (psi r 0 g u) := by rw [e, PiS_add']
  have eF : PiF (y u) = PiF (actual r g y u) + PiF (psi r 0 g u) := by
    rw [e]
    funext k
    by_cases hk : k 2 = 0 <;> simp [PiF, hk]
  have hS2 : hnorm 2 (PiS (y u)) ≤ slowNorm 2 r g y u + 1 := by
    rw [eS]
    refine (hnorm_add_le hx.inH.PiS hψ.inH.PiS).trans (add_le_add le_rfl ?_)
    exact (hnorm_PiS_le hψ.inH).trans hψ1
  have hG2 : hnorm 2 (PiF (y u)) ≤ Y + 1 := by
    rw [eF]
    refine (hnorm_add_le hx.inH.PiF hψ.inH.PiF).trans (add_le_add hY ?_)
    exact (hnorm_PiF_le hψ.inH).trans hψ1
  have hSW : wiener (PiS (y u)) ≤ W + c4 := by
    rw [eS]
    refine (wiener_add_le (summable_wiener hx.PiS.inH) (summable_wiener hψ.PiS.inH)).trans
      (add_le_add hW ?_)
    have h1 := wiener_le hψ.PiS.mz
    have h2 := (hnorm_PiS_le hψ.inH).trans hψ1
    nlinarith
  have hGW : wiener (PiF (y u)) ≤ c4 * (Y + 1) :=
    (wiener_le hw.PiF.mz).trans (mul_le_mul_of_nonneg_left hG2 hc.le)
  have n1 := wiener_nonneg (PiS (y u))
  have n2 := wiener_nonneg (PiF (y u))
  have n3 := hnorm_nonneg 2 (PiS (y u))
  have n4 := hnorm_nonneg 2 (PiF (y u))
  have n5 : 0 ≤ slowNorm 2 r g y u := hnorm_nonneg _ _
  have hY0 : 0 ≤ Y + 1 := by linarith
  have p1 : wiener (PiS (y u)) * hnorm 2 (PiF (y u)) ≤ (W + c4) * (Y + 1) :=
    mul_le_mul hSW hG2 n4 (n1.trans hSW)
  have p2 : hnorm 2 (PiS (y u)) * wiener (PiF (y u)) ≤
      (slowNorm 2 r g y u + 1) * (c4 * (Y + 1)) :=
    mul_le_mul hS2 hGW n2 (by positivity)
  have p3 : wiener (PiF (y u)) * hnorm 2 (PiF (y u)) ≤ c4 * (Y + 1) * (Y + 1) :=
    mul_le_mul hGW hG2 n4 (by positivity)
  unfold fastXi
  nlinarith

/-- The other sizes along the solution under the caps. -/
private lemma sizes (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {caps : Caps} {s t : ℝ}
    (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hP : OnPrefix caps r g y s t) {u : ℝ}
    (hu : u ∈ Icc s t) :
    wiener (actual r g y u) ≤ cp caps.WS + c4 * cp caps.yF ∧
      hnorm 2 (actual r g y u) ≤ slowNorm 2 r g y u + cp caps.yF ∧
      hnorm 2 (slowCorr r g y u) ≤ 8 * c4 * cp caps.yF ^ 2 / |r| := by
  have hrpos : 0 < |r| := abs_pos.2 hr
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hc4 := c4_pos
  obtain ⟨-, hbF, -, -, hWS⟩ := hP.1 u hu
  have hY : fastNorm 2 r g y u ≤ cp caps.yF := hbF.trans (le_cp _)
  have hW : slowWiener r g y u ≤ cp caps.WS := hWS.trans (le_cp _)
  refine ⟨(wiener_actual_le h hu0 huT).trans
      (add_le_add hW (mul_le_mul_of_nonneg_left hY hc4.le)),
    (hnorm_two_actual_le h hu0 huT).trans (add_le_add le_rfl hY), ?_⟩
  refine (hnorm_slowCorr_le h hr hu0 huT).2.trans ?_
  have hsq : fastNorm 2 r g y u ^ 2 ≤ cp caps.yF ^ 2 :=
    pow_le_pow_left₀ (hnorm_nonneg _ _) hY 2
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (by nlinarith) hrpos.le

/-- **The budget form of the pointwise `H¹` bound**:
`‖corrRes‖₁ ≤ φ + (a₀ + a₁ b_S + e c_F)/q`. -/
private lemma hnorm_one_corrRes_caps_J (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {caps : Caps}
    {s t : ℝ} (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hP : OnPrefix caps r g y s t)
    (hq2 : 2 * φ ≤ |r|) (hρ : 8 * c4 * cp caps.yF ^ 2 ≤ |r|) {u : ℝ} (hu : u ∈ Icc s t)
    (hF3 : InH 3 (PiF (actual r g y u))) :
    hnorm 1 (corrRes r g y u) ≤ φ + (bud0 φ caps + bud1 φ caps * slowNorm 2 r g y u +
      bud2 caps * fastNorm 3 r g y u) / |r| := by
  have hrpos : 0 < |r| := abs_pos.2 hr
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hc4 := c4_pos
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  obtain ⟨hwx, hnx, hR⟩ := sizes h hr hs ht hP hu
  obtain ⟨-, hbF, -, -, hWS⟩ := hP.1 u hu
  have hY : fastNorm 2 r g y u ≤ cp caps.yF := hbF.trans (le_cp _)
  have hW : slowWiener r g y u ≤ cp caps.WS := hWS.trans (le_cp _)
  have hXi := fastXi_le h hr hq2 hu0 huT hY hW
  have hg1 : hnorm 1 g ≤ φ := (hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le
  have hψ2 := psi_le h hr hu0
  have hψ1 : hnorm 2 (psi r 0 g u) ≤ 1 := by
    refine hψ2.trans ?_
    rw [div_le_one hrpos]
    exact hq2
  have hR1 : hnorm 2 (slowCorr r g y u) ≤ 1 := by
    refine hR.trans ?_
    rw [div_le_one hrpos]
    exact hρ
  have hY0 := cp_nonneg caps.yF
  have hW0 := cp_nonneg caps.WS
  have n1 : 0 ≤ fastNorm 2 r g y u := hnorm_nonneg _ _
  have n2 : 0 ≤ fastNorm 3 r g y u := hnorm_nonneg _ _
  have n3 := fastXi_nonneg (y u)
  have n5 := hnorm_nonneg 2 (psi r 0 g u)
  have n6 := hnorm_nonneg 2 (slowCorr r g y u)
  have n7 := wiener_nonneg (actual r g y u)
  have n8 : 0 ≤ slowWiener r g y u := wiener_nonneg _
  have n9 := hnorm_nonneg 2 (actual r g y u)
  have n10 : 0 ≤ slowNorm 2 r g y u := hnorm_nonneg _ _
  refine (hnorm_one_corrRes_J h hr hu0 huT hF3).2.trans ?_
  have hmain : hnorm 1 g + c4 * fastNorm 2 r g y u / |r| *
      (24 * fastNorm 3 r g y u + 56 * fastXi (y u)) +
      8 * hnorm 2 (psi r 0 g u) * (wiener (actual r g y u) + c4 * hnorm 2 (actual r g y u) +
        c4 * hnorm 2 (psi r 0 g u)) +
      8 * hnorm 2 (slowCorr r g y u) * (slowWiener r g y u + c4 * slowNorm 2 r g y u +
        c4 * hnorm 2 (slowCorr r g y u)) ≤
      φ + c4 * cp caps.yF / |r| * (24 * fastNorm 3 r g y u +
        56 * ((cp caps.yF + 1) * (cp caps.WS + c4 * cp caps.yF + 3 * c4 +
          c4 * slowNorm 2 r g y u))) +
      8 * (2 * φ / |r|) * (cp caps.WS + c4 * cp caps.yF +
        c4 * (slowNorm 2 r g y u + cp caps.yF) + c4 * 1) +
      8 * (8 * c4 * cp caps.yF ^ 2 / |r|) * (cp caps.WS + c4 * slowNorm 2 r g y u + c4 * 1) := by
    gcongr
  refine hmain.trans (le_of_eq ?_)
  simp only [bud0, bud1, bud2, budW]
  ring

/-! ### The fast `H³` dissipation of the interval: `J_{3,pre}` -/

/-- **`J_{3,pre}` at the caps, on an interval of length `ℓ`**: `y² + 128 (y + 1)²(ℓ W'² + c₄² J_S)`,
where the TeX has `y² + Θ²`.  The bracket is `Θ² ≍ y² (W_S² + J_S)`: of the two alternatives
`B_S √J_F`, `y √J_S` of `Θ`, it is the second. -/
def J3pre (ℓ : ℝ) (caps : Caps) : ℝ :=
  cp caps.yF ^ 2 + 128 * (cp caps.yF + 1) ^ 2 * (ℓ * budW caps ^ 2 + c4 ^ 2 * cp caps.JS)

lemma continuousOn_slow_two (h : ActualSol μ φ r g y Ty) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) : ContinuousOn (slowNorm 2 r g y) (uIcc s t) := by
  rw [uIcc_of_le hst]
  exact (norms_continuous h (hs.trans hst) ht).2.2.2.1.mono (Icc_subset_Icc_left hs)

lemma intervalIntegrable_slow_sq (h : ActualSol μ φ r g y Ty) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (fun u => slowNorm 2 r g y u ^ 2) volume s t :=
  ((continuousOn_slow_two h hs hst ht).pow 2).intervalIntegrable

/-- **The fast `H³` dissipation under the caps of the same interval** (Body 13: "`∫ c_F² ≤ b_F(s)² +
‖h_F‖²_{L²H¹}`"): the true left trace and the sector bound, no later pulse. -/
theorem fast_three_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {caps : Caps} {s t ℓ : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ ℓ)
    (hq2 : 2 * φ ≤ |r|) (hP : OnPrefix caps r g y s t) :
    ∫ u in s..t, fastNorm 3 r g y u ^ 2 ≤ J3pre ℓ caps := by
  have hc := c4_pos
  have hY0 := cp_nonneg caps.yF
  have hW0 : 0 ≤ budW caps := by
    have := cp_nonneg caps.WS
    unfold budW
    positivity
  set Y := cp caps.yF with hYdef
  set W' := budW caps with hW'def
  set v := Y + 1 with hv
  have hv0 : 0 ≤ v := by positivity
  have hcont := continuousOn_slow_two h hs hst ht
  have hb := intervalIntegrable_slow_sq h hs hst ht
  have hDi : IntervalIntegrable (fun u => (8 * (v * (W' + c4 * slowNorm 2 r g y u))) ^ 2)
      volume s t :=
    ((continuousOn_const.mul (continuousOn_const.mul
      (continuousOn_const.add (continuousOn_const.mul hcont)))).pow 2).intervalIntegrable
  have hd := fast_dissipation_J (D := fun u => 8 * (v * (W' + c4 * slowNorm 2 r g y u)))
    h hs hst ht hDi fun u hu => by
      have hu0 : 0 ≤ u := hs.trans hu.1
      have huT := lt_lifespan hu.2 ht
      obtain ⟨-, hbF, -, -, hWS⟩ := hP.1 u hu
      have hXi := fastXi_le h hr hq2 hu0 huT (hbF.trans (le_cp _)) (hWS.trans (le_cp _))
      have h1 := (hnorm_PiF_Qphase_le (r * u) (h.sol.adm u hu0 huT)).2
      have h2 : fastXi (y u) ≤ v * (W' + c4 * slowNorm 2 r g y u) := by
        simpa only [hW'def, budW, hv] using hXi
      linarith
  -- the time integral of the bound
  have hI : ∫ u in s..t, (8 * (v * (W' + c4 * slowNorm 2 r g y u))) ^ 2 ≤
      128 * v ^ 2 * (ℓ * W' ^ 2 + c4 ^ 2 * cp caps.JS) := by
    have hle : ∀ u ∈ Icc s t, (8 * (v * (W' + c4 * slowNorm 2 r g y u))) ^ 2 ≤
        128 * v ^ 2 * W' ^ 2 + 128 * v ^ 2 * c4 ^ 2 * slowNorm 2 r g y u ^ 2 := fun u _ => by
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) (sq_nonneg v))
        (sq_nonneg (W' - c4 * slowNorm 2 r g y u))]
    have hg := (intervalIntegrable_const (c := 128 * v ^ 2 * W' ^ 2) (μ := volume) (a := s)
      (b := t)).add (hb.const_mul (128 * v ^ 2 * c4 ^ 2))
    have hm := intervalIntegral.integral_mono_on hst hDi hg hle
    have hval : ∫ u in s..t, (128 * v ^ 2 * W' ^ 2 +
        128 * v ^ 2 * c4 ^ 2 * slowNorm 2 r g y u ^ 2) = (t - s) * (128 * v ^ 2 * W' ^ 2) +
        128 * v ^ 2 * c4 ^ 2 * ∫ u in s..t, slowNorm 2 r g y u ^ 2 := by
      rw [intervalIntegral.integral_add intervalIntegrable_const (hb.const_mul _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
    have hJ : ∫ u in s..t, slowNorm 2 r g y u ^ 2 ≤ cp caps.JS := hP.2.2.1.trans (le_cp _)
    have h1 : (t - s) * (128 * v ^ 2 * W' ^ 2) ≤ ℓ * (128 * v ^ 2 * W' ^ 2) :=
      mul_le_mul_of_nonneg_right hlen (by positivity)
    have h2 : 128 * v ^ 2 * c4 ^ 2 * ∫ u in s..t, slowNorm 2 r g y u ^ 2 ≤
        128 * v ^ 2 * c4 ^ 2 * cp caps.JS := mul_le_mul_of_nonneg_left hJ (by positivity)
    nlinarith
  have hF : fastNorm 2 r g y s ≤ Y := (hP.1 s ⟨le_rfl, hst⟩).2.1.trans (le_cp _)
  have hF2 : fastNorm 2 r g y s ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) hF 2
  unfold J3pre
  linarith

/-! ### The budget -/

/-- The arithmetic of the budget. -/
private lemma budget_arith {a b e Y v W c j q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e)
    (hY : 0 ≤ Y) (hv : 0 ≤ v) (hW : 0 ≤ W) (hc : 0 ≤ c) (hj : 0 ≤ j)
    (hK : 2 * (2 * a + b * j + e * Y + 16 * e * v * W + 12 * e * v * c * j) ≤ |q|) :
    6 * (2 * a ^ 2 + b ^ 2 * j ^ 2 + e ^ 2 * (Y ^ 2 + 128 * v ^ 2 * (2 * W ^ 2 + c ^ 2 * j ^ 2))) ≤
      4 * q ^ 2 := by
  set E := 2 * a + b * j + e * Y + 16 * e * v * W + 12 * e * v * c * j with hE
  have hE0 : 0 ≤ E := by positivity
  have h2 := pow_le_pow_left₀ (by positivity) hK 2
  rw [sq_abs] at h2
  have hsq : 2 * a ^ 2 + b ^ 2 * j ^ 2 +
      e ^ 2 * (Y ^ 2 + 128 * v ^ 2 * (2 * W ^ 2 + c ^ 2 * j ^ 2)) ≤ E ^ 2 := by
    rw [hE, ← sub_nonneg]
    ring_nf
    positivity
  nlinarith [sq_nonneg E]

/-- **The `L²_t H¹` residual budget at the joint scale** on an interval of length `≤ 2` where the
caps hold: `∫ₛᵗ ‖corrRes‖₁² ≤ 4φ² + 4` once `jointBudget φ caps ≤ q`.  `‖Π_S g‖₁ ≤ φ` gives `4φ²`,
the `1/q` terms give at most `4`. -/
theorem corrRes_budget_J (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 2)
    (hthr : jointBudget φ caps ≤ |r|) (hP : OnPrefix caps r g y s t) :
    (∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 4 * φ ^ 2 + 4 := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  obtain ⟨hf1, hf2, hf3⟩ := jointBudget_floors hφ caps
  have hq : 1 ≤ |r| := hf1.trans hthr
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hq; linarith
  have hq2 := hf2.trans hthr
  have hρ := hf3.trans hthr
  have hY0 := cp_nonneg caps.yF
  have hW0 := cp_nonneg caps.WS
  have hj0 := capJ_nonneg caps
  have hc4 := c4_pos
  have hW'0 : 0 ≤ budW caps := by unfold budW; positivity
  have ha0 : 0 ≤ bud0 φ caps := by unfold bud0; positivity
  have ha1 : 0 ≤ bud1 φ caps := by unfold bud1; positivity
  have he0 : 0 ≤ bud2 caps := by unfold bud2; positivity
  have hJ3 := fast_three_le (ℓ := 2) h hr0 hs hst ht hlen hq2 hP
  have hJb : ∫ u in s..t, slowNorm 2 r g y u ^ 2 ≤ cp caps.JS := hP.2.2.1.trans (le_cp _)
  have hK : 2 * (2 * bud0 φ caps + bud1 φ caps * capJ caps + bud2 caps * cp caps.yF +
      16 * bud2 caps * (cp caps.yF + 1) * budW caps +
      12 * bud2 caps * (cp caps.yF + 1) * c4 * capJ caps) ≤ |r| := by
    have := budget_alg hc4.le hY0 hW0 hj0 hφ
    refine le_trans ?_ hthr
    unfold jointBudget
    refine le_trans (le_of_eq ?_) this
    simp only [bud0, bud1, bud2, budW]
  have hK2 := budget_arith ha0 ha1 he0 hY0 (by positivity) hW'0 hc4.le hj0 hK
  rw [capJ_sq] at hK2
  set a := bud0 φ caps
  set b := bud1 φ caps
  set e := bud2 caps
  have hr2 : 0 < r ^ 2 := by positivity
  -- the bound at almost every time
  have hae : ∀ᵐ u ∂(volume.restrict (Icc s t)), hnorm 1 (corrRes r g y u) ^ 2 ≤
      2 * φ ^ 2 + 6 * a ^ 2 / r ^ 2 + 6 * b ^ 2 / r ^ 2 * slowNorm 2 r g y u ^ 2 +
        6 * e ^ 2 / r ^ 2 * fastNorm 3 r g y u ^ 2 := by
    filter_upwards [ae_fast_three h hs hst ht, ae_restrict_mem measurableSet_Icc] with u hF3 hu
    have hbd := hnorm_one_corrRes_caps_J h hr0 hs ht hP hq2 hρ hu hF3
    set S2 := slowNorm 2 r g y u
    set C3 := fastNorm 3 r g y u
    have h1 : hnorm 1 (corrRes r g y u) ^ 2 ≤ (φ + (a + b * S2 + e * C3) / |r|) ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg _ _) hbd 2
    have e1 : (a + b * S2 + e * C3) ^ 2 / r ^ 2 = ((a + b * S2 + e * C3) / |r|) ^ 2 := by
      rw [div_pow, sq_abs]
    have h2 : (a + b * S2 + e * C3) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 * S2 ^ 2 + e ^ 2 * C3 ^ 2) := by
      nlinarith [sq_nonneg (a - b * S2), sq_nonneg (a - e * C3), sq_nonneg (b * S2 - e * C3)]
    have h3 : (φ + (a + b * S2 + e * C3) / |r|) ^ 2 ≤
        2 * φ ^ 2 + 2 * ((a + b * S2 + e * C3) ^ 2 / r ^ 2) := by
      rw [e1]
      nlinarith [sq_nonneg (φ - (a + b * S2 + e * C3) / |r|)]
    have h4 : (a + b * S2 + e * C3) ^ 2 / r ^ 2 ≤
        3 * (a ^ 2 + b ^ 2 * S2 ^ 2 + e ^ 2 * C3 ^ 2) / r ^ 2 :=
      div_le_div_of_nonneg_right h2 hr2.le
    have e2 : 2 * (3 * (a ^ 2 + b ^ 2 * S2 ^ 2 + e ^ 2 * C3 ^ 2) / r ^ 2) =
        6 * a ^ 2 / r ^ 2 + 6 * b ^ 2 / r ^ 2 * S2 ^ 2 + 6 * e ^ 2 / r ^ 2 * C3 ^ 2 := by ring
    linarith
  -- integration
  have hI1 := intervalIntegrable_corrRes_sq h hr0 hs hst ht
  have hIb := (intervalIntegrable_slow_sq h hs hst ht).const_mul (6 * b ^ 2 / r ^ 2)
  have hIc := (intervalIntegrable_fast_three h hs hst ht).const_mul (6 * e ^ 2 / r ^ 2)
  have hI2 := ((intervalIntegrable_const (c := 2 * φ ^ 2 + 6 * a ^ 2 / r ^ 2) (μ := volume)
    (a := s) (b := t)).add hIb).add hIc
  have hmono := intervalIntegral.integral_mono_ae_restrict hst hI1 hI2 hae
  have hval : ∫ u in s..t, (2 * φ ^ 2 + 6 * a ^ 2 / r ^ 2 +
      6 * b ^ 2 / r ^ 2 * slowNorm 2 r g y u ^ 2 + 6 * e ^ 2 / r ^ 2 * fastNorm 3 r g y u ^ 2) =
      (t - s) * (2 * φ ^ 2 + 6 * a ^ 2 / r ^ 2) +
      6 * b ^ 2 / r ^ 2 * (∫ u in s..t, slowNorm 2 r g y u ^ 2) +
      6 * e ^ 2 / r ^ 2 * ∫ u in s..t, fastNorm 3 r g y u ^ 2 := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const.add hIb) hIc,
      intervalIntegral.integral_add intervalIntegrable_const hIb,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [hval] at hmono
  have h7 : (t - s) * (2 * φ ^ 2 + 6 * a ^ 2 / r ^ 2) ≤ 2 * (2 * φ ^ 2 + 6 * a ^ 2 / r ^ 2) :=
    mul_le_mul_of_nonneg_right hlen (by positivity)
  have h8 : 6 * b ^ 2 / r ^ 2 * (∫ u in s..t, slowNorm 2 r g y u ^ 2) ≤
      6 * b ^ 2 / r ^ 2 * cp caps.JS := mul_le_mul_of_nonneg_left hJb (by positivity)
  have h9 : 6 * e ^ 2 / r ^ 2 * (∫ u in s..t, fastNorm 3 r g y u ^ 2) ≤
      6 * e ^ 2 / r ^ 2 * J3pre 2 caps := mul_le_mul_of_nonneg_left hJ3 (by positivity)
  have h10 : 6 * (2 * a ^ 2 + b ^ 2 * cp caps.JS + e ^ 2 * J3pre 2 caps) / r ^ 2 ≤ 4 := by
    rw [div_le_iff₀ hr2]
    unfold J3pre
    exact hK2
  have e3 : 2 * (2 * φ ^ 2 + 6 * a ^ 2 / r ^ 2) + 6 * b ^ 2 / r ^ 2 * cp caps.JS +
      6 * e ^ 2 / r ^ 2 * J3pre 2 caps =
      4 * φ ^ 2 + 6 * (2 * a ^ 2 + b ^ 2 * cp caps.JS + e ^ 2 * J3pre 2 caps) / r ^ 2 := by ring
  linarith

/-- **`SlowBudget` at the joint threshold.** -/
theorem slowBudget_jointBudget (R₀ : ℝ) :
    Slow.SlowBudget R₀ fun X R caps ↦ jointBudget (R - X) caps :=
  fun _ _ _ _ _ _ _ h _ _ _ hs hst ht hlen hthr hP ↦ corrRes_budget_J h hs hst ht hlen hthr hP

end OVNS.Quant

end
