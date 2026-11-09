import OddViscousNS.Quant.Joint.Sources.Below
import OddViscousNS.Quant.Energy.H2.Identity

/-!
# J4: the filter force

The sources of the force filter, in the forms of the TeX and LOCAL363.  `hnorm_one_Hpsi_le`:
`‖H_ψ‖₁ ≤ (32 c₄ φ/q)(b_S + b_F) + 32 c₄ φ²/q²`, the bound `‖h‖₁ ≤ C[(φ/q)(‖S‖₂ + ‖F‖₂) + (φ/q)²]`.
Its two norms: `j_L/q + j_Q/q²` in `L^∞_t` (`hnorm_one_Hpsi_sup`), `h_L/q + h_Q/q²` in `L²_t`
(`filter_sq_le`).  Role 18, the literal pointwise `‖H_ψ‖₁ ≤ 1/2`, is paid by the raised floor
(`role18`).  None of these is used by E7-P, where the filter is in `corrRes_budget_J`.

In `H²` (LOCAL479): `‖ψ‖₃ ≤ 2φ/q` (`psi_three_div_le`), whence
`‖H_ψ‖₂ ≤ (64 c₄ φ/q)(c_F + c_S) + 64 c₄ φ²/q²` (`hnorm_two_Hpsi_J`).  The fixed-force
`H2.psi_three_le` is `‖ψ‖₃ ≤ 4φ`, with no `1/q`, and `H2.Hpsi_two_le` has the additive
`h2L0 ≍ φ(W_S + y)`: at the joint scale these do not give the form the quartic `Q₄` uses (Body 34).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

open private term_le from OddViscousNS.Corrector

noncomputable section

namespace OVNS.Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- **The filter force in `H¹`** (TeX; LOCAL363): `‖H_ψ‖₁ ≤ (32c₄φ/q)(b_S + b_F) + 32c₄φ²/q²`. -/
theorem hnorm_one_Hpsi_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    InH 1 (Hpsi r g y u) ∧ hnorm 1 (Hpsi r g y u) ≤
      32 * c4 * φ / |r| * (slowNorm 2 r g y u + fastNorm 2 r g y u) + 32 * c4 * φ ^ 2 / r ^ 2 := by
  have hrp : 0 < |r| := abs_pos.mpr hr
  have hc := c4_pos
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hx := actual_adm h hu huT
  have hψ := psi_adm (r := r) (t₀ := 0) h.force_adm u hu
  obtain ⟨i3, b3⟩ := hnorm_Qm_three_bound (phaseM_bdd (r * u)) hx.mz hψ.mz
  have e3 : Hpsi r g y u = Qm (phaseM (r * u)) (actual r g y u) (psi r 0 g u) +
      Qm (phaseM (r * u)) (psi r 0 g u) (actual r g y u) +
      Qm (phaseM (r * u)) (psi r 0 g u) (psi r 0 g u) := Hpsi_eq h hu huT
  rw [← e3] at i3 b3
  refine ⟨i3, b3.trans ?_⟩
  have hψ2 := psi_le h hr hu
  have hwx := wiener_le hx.mz
  have hx2 := hnorm_two_actual_le h hu huT
  have n1 := hnorm_nonneg 2 (actual r g y u)
  have n2 := hnorm_nonneg 2 (psi r 0 g u)
  have n3 := wiener_nonneg (actual r g y u)
  have hmain : 8 * hnorm 2 (psi r 0 g u) * (wiener (actual r g y u) +
      c4 * hnorm 2 (actual r g y u) + c4 * hnorm 2 (psi r 0 g u)) ≤
      8 * (2 * φ / |r|) * (c4 * (slowNorm 2 r g y u + fastNorm 2 r g y u) +
        c4 * (slowNorm 2 r g y u + fastNorm 2 r g y u) + c4 * (2 * φ / |r|)) := by
    have hb : wiener (actual r g y u) ≤ c4 * (slowNorm 2 r g y u + fastNorm 2 r g y u) :=
      hwx.trans (mul_le_mul_of_nonneg_left hx2 hc.le)
    gcongr
  refine hmain.trans (le_of_eq ?_)
  rw [← sq_abs r]
  field_simp
  ring

/-- `‖H_ψ‖_{L^∞_t H¹} ≤ j_L/q + j_Q/q²`, `j_L = 32 c₄ φ (B_S + y)`, `j_Q = 32 c₄ φ²`. -/
theorem hnorm_one_Hpsi_sup (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {caps : Caps} {s t : ℝ}
    (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hP : OnPrefix caps r g y s t) {u : ℝ}
    (hu : u ∈ Icc s t) :
    hnorm 1 (Hpsi r g y u) ≤ 32 * c4 * φ * (cp caps.BS + cp caps.yF) / |r| +
      32 * c4 * φ ^ 2 / r ^ 2 := by
  have hrp : 0 < |r| := abs_pos.mpr hr
  have hc := c4_pos
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  refine (hnorm_one_Hpsi_le h hr (hs.trans hu.1) (lt_lifespan hu.2 ht)).2.trans ?_
  obtain ⟨-, hbF, -, hbS, -⟩ := hP.1 u hu
  have h1 : slowNorm 2 r g y u + fastNorm 2 r g y u ≤ cp caps.BS + cp caps.yF :=
    add_le_add (hbS.trans (le_cp _)) (hbF.trans (le_cp _))
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 32 * c4 * φ / |r|)
  have e : 32 * c4 * φ * (cp caps.BS + cp caps.yF) / |r| =
      32 * c4 * φ / |r| * (cp caps.BS + cp caps.yF) := by ring
  rw [e]
  linarith

/-- The `L²_t` size of the bound of `hnorm_one_Hpsi_le` on an interval of length `≤ ℓ`:
`≤ 3(h_L/q)² + 3(h_Q/q²)²`, with `h_L² = (32 c₄ φ)²(J_S + J_F)`, `h_Q² = (32 c₄ φ²)² ℓ`. -/
theorem filter_sq_le (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t ℓ : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ ℓ)
    (hP : OnPrefix caps r g y s t) :
    ∫ u in s..t, (32 * c4 * φ / |r| * (slowNorm 2 r g y u + fastNorm 2 r g y u) +
        32 * c4 * φ ^ 2 / r ^ 2) ^ 2 ≤
      3 * ((32 * c4 * φ / |r|) ^ 2 * (cp caps.JS + cp caps.JF)) +
        3 * ((32 * c4 * φ ^ 2 / r ^ 2) ^ 2 * ℓ) := by
  have ht0 := hs.trans hst
  set A := 32 * c4 * φ / |r|
  set B := 32 * c4 * φ ^ 2 / r ^ 2
  have hS := continuousOn_slow_two h hs hst ht
  have hF : ContinuousOn (fastNorm 2 r g y) (uIcc s t) := by
    rw [uIcc_of_le hst]
    exact (norms_continuous h ht0 ht).2.1.mono (Icc_subset_Icc_left hs)
  have hb := intervalIntegrable_slow_sq h hs hst ht
  have hf : IntervalIntegrable (fun u => fastNorm 2 r g y u ^ 2) volume s t :=
    (hF.pow 2).intervalIntegrable
  have hI : IntervalIntegrable (fun u => (A * (slowNorm 2 r g y u + fastNorm 2 r g y u) + B) ^ 2)
      volume s t :=
    (((continuousOn_const.mul (hS.add hF)).add continuousOn_const).pow 2).intervalIntegrable
  have hg := (intervalIntegrable_const (c := 3 * B ^ 2) (μ := volume) (a := s) (b := t)).add
    ((hb.const_mul (3 * A ^ 2)).add (hf.const_mul (3 * A ^ 2)))
  have hle : ∀ u ∈ Icc s t, (A * (slowNorm 2 r g y u + fastNorm 2 r g y u) + B) ^ 2 ≤
      3 * B ^ 2 + (3 * A ^ 2 * slowNorm 2 r g y u ^ 2 + 3 * A ^ 2 * fastNorm 2 r g y u ^ 2) :=
    fun u _ => by
      set a := A * slowNorm 2 r g y u
      set b := A * fastNorm 2 r g y u
      have e : (A * (slowNorm 2 r g y u + fastNorm 2 r g y u) + B) ^ 2 = (a + b + B) ^ 2 := by
        simp only [a, b]
        ring
      rw [e]
      have e2 : 3 * B ^ 2 + (3 * A ^ 2 * slowNorm 2 r g y u ^ 2 +
          3 * A ^ 2 * fastNorm 2 r g y u ^ 2) = 3 * (a ^ 2 + b ^ 2 + B ^ 2) := by
        simp only [a, b]
        ring
      rw [e2]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - B), sq_nonneg (b - B)]
  have hm := intervalIntegral.integral_mono_on hst hI hg hle
  have hval : ∫ u in s..t, (3 * B ^ 2 + (3 * A ^ 2 * slowNorm 2 r g y u ^ 2 +
      3 * A ^ 2 * fastNorm 2 r g y u ^ 2)) = (t - s) * (3 * B ^ 2) +
      (3 * A ^ 2 * (∫ u in s..t, slowNorm 2 r g y u ^ 2) +
        3 * A ^ 2 * ∫ u in s..t, fastNorm 2 r g y u ^ 2) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
        ((hb.const_mul _).add (hf.const_mul _)),
      intervalIntegral.integral_add (hb.const_mul _) (hf.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [hval] at hm
  have hJS : ∫ u in s..t, slowNorm 2 r g y u ^ 2 ≤ cp caps.JS := hP.2.2.1.trans (le_cp _)
  have hJF : ∫ u in s..t, fastNorm 2 r g y u ^ 2 ≤ cp caps.JF := hP.2.1.trans (le_cp _)
  have h1 : (t - s) * (3 * B ^ 2) ≤ ℓ * (3 * B ^ 2) :=
    mul_le_mul_of_nonneg_right hlen (by positivity)
  have h2 := mul_le_mul_of_nonneg_left hJS (by positivity : 0 ≤ 3 * A ^ 2)
  have h3 := mul_le_mul_of_nonneg_left hJF (by positivity : 0 ≤ 3 * A ^ 2)
  nlinarith

/-- **Role 18**, the literal pointwise filter certificate, at the raised floor: `‖H_ψ‖₁ ≤ 1/2` on a
prefix.  It is `q ≥ 2⁵ c₄ Y φ`, `Y = totalY ∋ B_S`, of degree `(0, 3)` (`rootFloor_below`), so
unlike the budget it does read the pointwise cap `B_S`. -/
theorem role18 {X R q₀ : ℝ} {caps : Caps} {s t : ℝ} (h : ActualSol X (R - X) r g y Ty)
    (hX : 0 ≤ X) (hthr : 64 * Q0Prime X (R - X) q₀ caps ≤ |r|) (hs : 0 ≤ s)
    (ht : ENNReal.ofReal t < Ty) (hP : OnPrefix caps r g y s t) {u : ℝ} (hu : u ∈ Icc s t) :
    hnorm 1 (Hpsi r g y u) ≤ 1 / 2 := by
  have hφ : 0 ≤ R - X := (hnorm_nonneg 2 g).trans h.force_le
  set φ := R - X with hφdef
  have hc := c4_pos
  have hy := cp_nonneg caps.yF
  have hB := cp_nonneg caps.BS
  set Y := totalY X caps with hY
  have hY2 : 2 ≤ Y := by
    have : Y = 2 * (1 + X + cp caps.yF + cp caps.BS) := rfl
    linarith
  have hYB : 2 * (cp caps.BS + cp caps.yF) ≤ Y := by
    have : Y = 2 * (1 + X + cp caps.yF + cp caps.BS) := rfl
    linarith
  have hfl : rootFloor X φ caps ≤ |r| / 64 := by
    have : rootFloor X φ caps ≤ Q0Prime X φ q₀ caps := le_max_left _ _
    linarith
  have hYφ : 0 ≤ 2 ^ 5 * c4 * Y * φ := by positivity
  have h20 : 0 ≤ 2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 := by positivity
  have hq1 : 2 ^ 5 * c4 * Y * φ * 64 ≤ |r| := by
    unfold rootFloor at hfl
    linarith only [hfl, hφ, hYφ, h20, hY2]
  have hq2 : 2 ^ 9 * φ * 64 ≤ |r| := by
    unfold rootFloor at hfl
    linarith only [hfl, hφ, hYφ, h20, hY2]
  have hq3 : 2 * 64 ≤ |r| := by
    unfold rootFloor at hfl
    linarith only [hfl, hφ, hYφ, h20, hY2]
  have hrp : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hrp
  refine (hnorm_one_Hpsi_sup h hr hs ht hP hu).trans ?_
  have t1 : 32 * c4 * φ * (cp caps.BS + cp caps.yF) / |r| ≤ 1 / 4 := by
    rw [div_le_iff₀ hrp]
    have h3 : 32 * c4 * φ * (2 * (cp caps.BS + cp caps.yF)) ≤ 32 * c4 * φ * Y :=
      mul_le_mul_of_nonneg_left hYB (by positivity)
    nlinarith only [h3, hq1, hrp]
  have t2 : 32 * c4 * φ ^ 2 / r ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs r, div_le_iff₀ (by positivity)]
    have h4 : 32 * c4 * φ * 2 ≤ 32 * c4 * φ * Y :=
      mul_le_mul_of_nonneg_left hY2 (by positivity)
    have h5 : 2 ^ 12 * (c4 * φ) ≤ |r| := by nlinarith only [h4, hq1]
    have h6 : 2 ^ 15 * φ ≤ |r| := by linarith only [hq2]
    have h7 := mul_le_mul h5 h6 (by positivity) hrp.le
    nlinarith only [h7, hrp, sq_nonneg (r : ℝ)]
  linarith

/-! ### The filter in `H²` -/

private lemma sobWeight_three_eq (k : Mode) : sobWeight 3 k = absSq k * sobWeight 2 k := by
  by_cases hk : k = 0
  · simp [sobWeight, hk]
  · rw [sobWeight_two]
    simp only [sobWeight, hk, ↓reduceIte]
    rw [show ((2 : ℝ) * 3) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← absk_sq]
    ring

private lemma sobWeight_two_eq (k : Mode) : sobWeight 2 k = absSq k * sobWeight 1 k := by
  rw [sobWeight_two, sobWeight_one]
  ring

/-- **`‖ψ‖₃ ≤ 2φ/q`**: the TeX's `‖ψ‖_j ≤ φ/q`, `0 ≤ j ≤ 3`.  The rotation gains one derivative and
the factor `1/q` (`term_le`), with the force in `H²`. -/
theorem psi_three_div_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    InH 3 (psi r 0 g u) ∧ hnorm 3 (psi r 0 g u) ≤ 2 * φ / |r| := by
  have hrp : 0 < |r| := abs_pos.mpr hr
  have hI := inH3_psi (r := r) h.force_adm hu
  refine ⟨hI, ?_⟩
  have hle : ∀ k, sobWeight 3 k * ‖psi r 0 g u k‖ ^ 2 ≤
      (2 / |r|) ^ 2 * (sobWeight 2 k * ‖g k‖ ^ 2) := fun k => by
    have h1 := term_le (t₀ := 0) (g := g) hr k hu
    have h2 := mul_le_mul_of_nonneg_left h1 (absSq_nonneg k)
    rw [sobWeight_three_eq, sobWeight_two_eq k]
    rw [sobWeight_two_eq k] at h2
    linarith
  have hsum : ∑' k, sobWeight 3 k * ‖psi r 0 g u k‖ ^ 2 ≤
      (2 / |r|) ^ 2 * ∑' k, sobWeight 2 k * ‖g k‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact hI.tsum_le_tsum hle (h.force_adm.inH.mul_left _)
  have h4 : hnorm 3 (psi r 0 g u) ≤ 2 / |r| * hnorm 2 g := by
    unfold hnorm
    refine (Real.sqrt_le_sqrt hsum).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  refine h4.trans ?_
  have := mul_le_mul_of_nonneg_left h.force_le (by positivity : 0 ≤ 2 / |r|)
  calc 2 / |r| * hnorm 2 g ≤ 2 / |r| * φ := this
    _ = 2 * φ / |r| := by ring

/-- **The filter in `H²`** (LOCAL479), at a time with `S, F ∈ H³`:
`‖H_ψ‖₂ ≤ (64 c₄ φ/q)(c_F + c_S) + 64 c₄ φ²/q²`. -/
theorem hnorm_two_Hpsi_J (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (PiF (actual r g y u)))
    (hS3 : InH 3 (PiS (actual r g y u))) :
    InH 2 (Hpsi r g y u) ∧ hnorm 2 (Hpsi r g y u) ≤
      64 * c4 * φ / |r| * (fastNorm 3 r g y u + slowNorm 3 r g y u) +
        64 * c4 * φ ^ 2 / r ^ 2 := by
  have hrp : 0 < |r| := abs_pos.mpr hr
  have hc := c4_pos
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hx := actual_adm h hu huT
  have hψa := psi_adm (r := r) (t₀ := 0) h.force_adm u hu
  obtain ⟨hψ3, hψ3le⟩ := psi_three_div_le h hr hu
  have hxSF := PiS_add_PiF (actual r g y u)
  have hx3I : InH 3 (actual r g y u) := by
    rw [← hxSF]
    exact hS3.add hF3
  have hx3 : MZ 3 (actual r g y u) := ⟨hx3I, hx.mean⟩
  have hψm : MZ 3 (psi r 0 g u) := ⟨hψ3, hψa.mean⟩
  have hxn : hnorm 3 (actual r g y u) ≤ fastNorm 3 r g y u + slowNorm 3 r g y u := by
    conv_lhs => rw [← hxSF]
    refine (hnorm_add_le hS3 hF3).trans (le_of_eq ?_)
    unfold fastNorm slowNorm
    ring
  obtain ⟨i1, b1⟩ := H2.Qm_two_le (phaseM_bdd (r * u)) hx3 hψm
  obtain ⟨i2, b2⟩ := H2.Qm_two_le (phaseM_bdd (r * u)) hψm hx3
  obtain ⟨i3, b3⟩ := H2.Qm_two_le (phaseM_bdd (r * u)) hψm hψm
  have e : Hpsi r g y u = Qm (phaseM (r * u)) (actual r g y u) (psi r 0 g u) +
      Qm (phaseM (r * u)) (psi r 0 g u) (actual r g y u) +
      Qm (phaseM (r * u)) (psi r 0 g u) (psi r 0 g u) := Hpsi_eq h hu huT
  refine ⟨by rw [e]; exact (i1.add i2).add i3, ?_⟩
  rw [e]
  have hsum := add_le_add ((hnorm_add_le i1 i2).trans (add_le_add b1 b2)) b3
  refine (hnorm_add_le (i1.add i2) i3).trans (hsum.trans ?_)
  set P := hnorm 3 (psi r 0 g u) with hP
  set X3 := hnorm 3 (actual r g y u) with hX3
  have hP0 : 0 ≤ P := hnorm_nonneg _ _
  have hX0 : 0 ≤ X3 := hnorm_nonneg _ _
  have ax : wiener (actual r g y u) ≤ c4 * X3 :=
    (wiener_le hx.mz).trans (mul_le_mul_of_nonneg_left
      (hnorm_mono (by norm_num) hx3I) hc.le)
  have aψ : wiener (psi r 0 g u) ≤ c4 * P :=
    (wiener_le hψa.mz).trans (mul_le_mul_of_nonneg_left
      (hnorm_mono (by norm_num) hψ3) hc.le)
  have t1 := mul_le_mul_of_nonneg_right ax hP0
  have t2 := mul_le_mul_of_nonneg_left aψ hX0
  have t3 := mul_le_mul_of_nonneg_right aψ hX0
  have t4 := mul_le_mul_of_nonneg_left ax hP0
  have t5 := mul_le_mul_of_nonneg_right aψ hP0
  have t6 := mul_le_mul_of_nonneg_left aψ hP0
  set E := 2 * φ / |r| with hE
  have hE0 : 0 ≤ E := by positivity
  set C := fastNorm 3 r g y u + slowNorm 3 r g y u with hC
  have m1 : X3 * P ≤ C * E := mul_le_mul hxn hψ3le hP0 (hX0.trans hxn)
  have m2 : P * P ≤ E * E := mul_le_mul hψ3le hψ3le hP0 hE0
  have m1' := mul_le_mul_of_nonneg_left m1 (by positivity : 0 ≤ c4)
  have m2' := mul_le_mul_of_nonneg_left m2 (by positivity : 0 ≤ c4)
  have e2 : 64 * c4 * φ / |r| * C + 64 * c4 * φ ^ 2 / r ^ 2 =
      32 * (c4 * (C * E)) + 16 * (c4 * (E * E)) := by
    rw [hE, ← sq_abs r]
    field_simp
    ring
  rw [e2]
  nlinarith only [t1, t2, t3, t4, t5, t6, m1', m2']

end OVNS.Quant

end
