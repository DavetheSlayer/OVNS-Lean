import OddViscousNS.Quant.Energy.Kinetic.Identity
import OddViscousNS.Quant.Energy.Kinetic.Degree

/-!
# E4: the kinetic interface

Assembly of `KineticInterface μ φ q₀` (TeX eq. quant-kinetic; spec §2.1 E4) with the explicit
threshold `q₀ = kinThreshold μ φ` (`Defs.lean`), and the degree bookkeeping
`DegreeBelow σ (dOf σ) e kinThreshold` (Table quant-fixed: the kinetic rows are "other …
raised-domain … roles `< 13`"; here degree `5β − 3/2 < d = 7β − 3`).

* `gronwall_decay_max`: the sharp form of `gronwall_decay`, `y' + λy ≤ β ⇒ y ≤ max (y a) (β/λ)`
  (TeX: "`W₀' + 4W₀/5 ≤ 1/8`", hence `W₀ ≤ max(W₀(s), 5/32)`).
* `abs_kinCorr_le`, `W0_coercive`: `|2⟨N(F,F),S⟩| ≤ (4/q) W_S ‖F‖₀² ≤ ¼‖F‖₀²` once
  `16 W_S ≤ q` (paid inside `kinThreshold`, `wiener_cap_le_kinThreshold`), i.e.
  `¾‖F‖₀² ≤ W₀ ≤ ⁵⁄₄‖F‖₀²` — the fixed-slow-output Cauchy bound of `Symbol.lean`.
* `W0_zero_le`: the true-zero bound `W₀(0) ≤ ⁵⁄₄ μ² ≤ ⁵⁄₄(μ + ¼)²` (`ψ(0) = 0`, so
  `F(0) = Π_F y(0)`;
  the TeX's `+¼` is the stationary filter's `‖ψ(0)‖ ≤ φ/q ≤ ¼`, role 23).
* `W0_diff_ineq` (**E4.5, the error budget**): the integrated
  `W₀' + a_F² ≤ 1/8` on every subinterval of a prefix where the caps hold and `kinThreshold ≤ q`.
* `kineticInterface_of_threshold`: `KineticInterface μ φ (kinThreshold μ φ)` from the above and
  `gronwall_decay_max`; with `kinetic_degree` (`Degree.lean`), `kineticInterface` is the
  consumable statement for `fixed_force_of_interfaces`.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ENNReal

noncomputable section

namespace OVNS

/-- Sharp form of `gronwall_decay`: from `y t + λ∫ₛᵗ y ≤ y s + β(t − s)` on all subintervals,
`y b ≤ max (y a) (β/λ)` (Duhamel with the exact `∫ e^{−λ(b−u)} β du = (β/λ)(1 − e^{−λ(b−a)})`). -/
theorem gronwall_decay_max {y : ℝ → ℝ} {a b lam β : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hβ : 0 ≤ β) (hy : ContinuousOn y (Icc a b))
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b → y t + lam * ∫ u in s..t, y u ≤ y s + β * (t - s)) :
    y b ≤ max (y a) (β / lam) := by
  have hyi : ∀ s t', a ≤ s → s ≤ t' → t' ≤ b → IntervalIntegrable y volume s t' :=
    fun s t' hs hst ht ↦ ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le hst]
      exact hy.mono (Icc_subset_Icc hs ht))
  have h1 := gronwall_integrated (y := y) (κ := fun _ ↦ -lam) (β := fun _ ↦ β) hab hy
    intervalIntegrable_const intervalIntegrable_const (fun s t' hs hst ht ↦ by
      have h0 := h s t' hs hst ht
      rw [intervalIntegral.integral_add ((hyi s t' hs hst ht).const_mul _)
        intervalIntegrable_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul]
      linarith) a b le_rfl hab le_rfl
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h1
  have h2 : ∫ u in a..b, Real.exp ((b - u) * -lam) * β =
      β / lam - β / lam * Real.exp ((b - a) * -lam) := by
    have hF : ∀ u ∈ uIcc a b, HasDerivAt (fun u ↦ β / lam * Real.exp ((b - u) * -lam))
        (Real.exp ((b - u) * -lam) * β) u := fun u _ ↦ by
      have h3 : HasDerivAt (fun u ↦ (b - u) * -lam) lam u := by
        simpa using ((hasDerivAt_id u).const_sub b).mul_const (-lam)
      refine (h3.exp.const_mul (β / lam)).congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp
  rw [h2] at h1
  set E := Real.exp ((b - a) * -lam) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hβl : 0 ≤ β / lam := div_nonneg hβ hlam.le
  rcases le_total (β / lam) (y a) with hc | hc
  · calc y b ≤ E * y a + (β / lam - β / lam * E) := h1
      _ = y a - (1 - E) * (y a - β / lam) := by ring
      _ ≤ y a := by nlinarith
      _ ≤ max (y a) (β / lam) := le_max_left _ _
  · calc y b ≤ E * y a + (β / lam - β / lam * E) := h1
      _ = β / lam - E * (β / lam - y a) := by ring
      _ ≤ β / lam := by nlinarith
      _ ≤ max (y a) (β / lam) := le_max_right _ _

namespace Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### Coercivity and the true-zero bound -/

/-- `|⟨N(F,F), S⟩| ≤ (2/q) W_S ‖F‖₀²` along the actual solution (`abs_pair_kinN_le`). -/
theorem abs_kinCorr_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) :
    |kinCorr r g y t| ≤ 2 / |r| * (slowWiener r g y t * fastNorm 0 r g y t ^ 2) := by
  have hx := actual_adm h ht htT
  have hF : Adm 2 (PiF (actual r g y t)) := hx.PiF
  have hS : Adm 2 (PiS (actual r g y t)) := hx.PiS
  have hF2 : Summable fun k => ‖PiF (actual r g y t) k‖ ^ 2 :=
    summable_norm_sq_of_inH (hF.inH.mono (by norm_num))
  have hS1 : Summable fun k => ‖PiS (actual r g y t) k‖ := summable_wiener hS.inH
  have := abs_pair_kinN_le (τ := r * t) hr hS1 hF2 hF2
  rw [← hnorm_zero_eq hF.mean] at this
  unfold kinCorr slowWiener fastNorm
  refine this.trans (le_of_eq ?_)
  ring

/-- `|r| ≥ 1` once the threshold is paid (role 22). -/
lemma one_le_abs_of_prefix (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) {caps : Caps} {s t : ℝ}
    (hP : PrefixHyp (kinThreshold μ φ) r g y Ty caps s t) : 1 ≤ |r| :=
  (one_le_kinThreshold hμ hφ caps).trans hP.thr

/-- **Coercivity** (TeX eq. quant-kinetic, first clause): on a prefix where the caps hold and the
kinetic floors are paid, `¾‖F‖₀² ≤ W₀ ≤ ⁵⁄₄‖F‖₀²` — from `|2⟨N(F,F),S⟩| ≤ (4/q) W_S ‖F‖₀²` and
`16 W_S ≤ 16 WS ≤ q₀ ≤ q`. -/
theorem W0_coercive (h : ActualSol μ φ r g y Ty) (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) {caps : Caps}
    {s t : ℝ} (hP : PrefixHyp (kinThreshold μ φ) r g y Ty caps s t) {u : ℝ} (hu : u ∈ Icc s t) :
    3 / 4 * fastNorm 0 r g y u ^ 2 ≤ W0 r g y u ∧ W0 r g y u ≤ 5 / 4 * fastNorm 0 r g y u ^ 2 := by
  have hr1 := one_le_abs_of_prefix hμ hφ hP
  have hr : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr1; linarith
  have hu0 : 0 ≤ u := hP.hs.trans hu.1
  have huT := lt_lifespan hu.2 hP.ht
  have hK := abs_kinCorr_le h hr hu0 huT
  have hW : slowWiener r g y u ≤ cp caps.WS := (hP.onPrefix.1 u hu).2.2.2.2.trans (le_cp _)
  have hW0 : 0 ≤ slowWiener r g y u := wiener_nonneg _
  have h16 : 16 * slowWiener r g y u ≤ |r| := by
    have := wiener_cap_le_kinThreshold hμ hφ caps
    linarith [hP.thr]
  have hA := sq_nonneg (fastNorm 0 r g y u)
  have hbound : 2 / |r| * (slowWiener r g y u * fastNorm 0 r g y u ^ 2) ≤
      1 / 8 * fastNorm 0 r g y u ^ 2 := by
    have hrpos : 0 < |r| := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hrpos]
    nlinarith [mul_le_mul_of_nonneg_left h16 hA]
  have := abs_le.1 (hK.trans hbound)
  unfold W0
  constructor <;> linarith

/-- **The true-zero bound** (TeX: `B₀ = max{⁵⁄₄(μ + ¼)², 5/32}`): `W₀(0) ≤ ⁵⁄₄(μ + ¼)²`, since
`ψ(0) = 0` gives `‖F(0)‖₀ ≤ ‖y(0)‖₂ ≤ μ`. -/
theorem W0_zero_le (h : ActualSol μ φ r g y Ty) (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) {caps : Caps} {t : ℝ}
    (hP : PrefixHyp (kinThreshold μ φ) r g y Ty caps 0 t) :
    W0 r g y 0 ≤ 5 / 4 * (μ + 1 / 4) ^ 2 := by
  have hc := (W0_coercive h hμ hφ hP (u := 0) ⟨le_rfl, hP.hst⟩).2
  have hy0 := h.sol.adm 0 le_rfl h.pos
  have e : actual r g y 0 = y 0 := by simp [actual, psi_zero]
  have h1 : fastNorm 0 r g y 0 ≤ μ := by
    unfold fastNorm
    rw [e]
    calc hnorm 0 (PiF (y 0)) ≤ hnorm 0 (y 0) := hnorm_PiF_le (hy0.inH.mono (by norm_num))
      _ ≤ hnorm 2 (y 0) := hnorm_mono (by norm_num) hy0.inH
      _ ≤ μ := h.init_le
  have h0 := hnorm_nonneg 0 (PiF (actual r g y 0))
  have h2 : fastNorm 0 r g y 0 ^ 2 ≤ (μ + 1 / 4) ^ 2 := by
    unfold fastNorm at h1 ⊢
    nlinarith
  linarith

/-! ### E4.5: the error budget -/

/-- The real-number bookkeeping of the E4.5 budget: the three remainders of `W₀'` carry a factor
`1/q` and are paid by `2²⁰(1 + c₄)⁴(1 + φ)⁴ · fourierFloor ≤ q`. -/
private lemma budget_alg {c φ q P Y A B W a f0 ε ψ1 wψ aS bF bS gn ax wx ay wy Qy h0 s' wF n0 fd
    wS X1 X2 X3 : ℝ}
    (hc : 0 < c) (hφ : 0 ≤ φ) (hq : 1 ≤ q) (hY : 0 ≤ Y) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hW : 0 ≤ W) (ha : 0 ≤ a) (haP : a ≤ P) (hf0 : 0 ≤ f0) (hf0a : f0 ≤ a) (hε : 0 ≤ ε)
    (hqε : q * ε ≤ 2 * φ) (hψ1 : ψ1 ≤ ε) (hwψ : wψ ≤ c * ε)
    (haS : aS ≤ A) (hbF : bF ≤ Y) (hbS : bS ≤ B) (hgn : gn ≤ φ)
    (hax0 : 0 ≤ ax) (hax : ax ≤ aS + a) (hwx0 : 0 ≤ wx) (hwx : wx ≤ wS + wF)
    (hay0 : 0 ≤ ay) (hay : ay ≤ ax + ψ1) (hwy0 : 0 ≤ wy) (hwy : wy ≤ wx + wψ)
    (hQy : Qy ≤ ay * wy + wy * ay)
    (hh0 : h0 ≤ ψ1 * wy + wψ * ay + ax * wψ + wx * ψ1) (h1 : |X1| ≤ a * h0)
    (hs0 : 0 ≤ s') (hs : s' ≤ bS + Qy + gn) (hwF0 : 0 ≤ wF) (hwF : wF ≤ c * bF)
    (hn0 : n0 ≤ 2 / q * (wF * f0)) (h2 : |X2| ≤ s' * n0)
    (hfd0 : 0 ≤ fd) (hfd : fd ≤ bF + Qy) (hwS : wS ≤ W)
    (h3 : |X3| ≤ 2 / q * (wS * (fd * f0)))
    (hthr : 2 ^ 20 * (1 + c) ^ 4 * (1 + φ) ^ 4 * (W + B * Y + Y * (A + P + 1) * (W + Y + 1) +
      W * (A + P + 1) * (W + Y + 1) + W * Y + (A + P + W + Y) + 1) ≤ q) :
    -2 * a ^ 2 - 2 * X1 - 2 * X2 - 4 * X3 + a ^ 2 ≤ 1 / 8 := by
  have hq0 : 0 < q := by linarith
  have hP : 0 ≤ P := ha.trans haP
  obtain ⟨M, hM⟩ : ∃ M, M = (1 + c) * (1 + φ) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = A + P + 1 := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = W + Y + 1 := ⟨_, rfl⟩
  have hU1 : 1 ≤ U := by rw [hU]; linarith
  have hV1 : 1 ≤ V := by rw [hV]; linarith
  have hc1 : 1 ≤ 1 + c := by linarith
  have hφ1 : 1 ≤ 1 + φ := by linarith
  have hM1 : 1 ≤ M := hM ▸ one_le_mul_of_one_le_of_one_le hc1 hφ1
  have hcM' : 1 + c ≤ M := hM ▸ le_mul_of_one_le_right (by linarith) hφ1
  have hφM' : 1 + φ ≤ M := hM ▸ le_mul_of_one_le_left (by linarith) hc1
  have hcM : c ≤ M := by linarith
  have hφM : φ ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hUV : 1 ≤ U * V := one_le_mul_of_one_le_of_one_le hU1 hV1
  have hεφ : ε ≤ 2 * φ := (le_mul_of_one_le_left hε hq).trans hqε
  -- the atoms
  have hay' : ay ≤ 2 * M * U := by
    have h1 : ay ≤ U + 2 * φ := by linarith only [hay, hax, haS, haP, hψ1, hεφ, hU]
    have h2 : φ ≤ φ * U := le_mul_of_one_le_right hφ hU1
    have h4 : (1 + φ) * U ≤ M * U := mul_le_mul_of_nonneg_right hφM' (by linarith)
    nlinarith only [h1, h2, h4, hU1]
  have hcε : c * ε ≤ 2 * (c * φ) := by nlinarith only [hεφ, hc]
  have hcbF : c * bF ≤ c * Y := mul_le_mul_of_nonneg_left hbF hc.le
  have hwy' : wy ≤ 2 * M * V := by
    have h1 : wy ≤ W + c * Y + 2 * (c * φ) := by
      linarith only [hwy, hwx, hwS, hwF, hcbF, hwψ, hcε]
    have h2 : W + c * Y ≤ (1 + c) * V := by
      rw [hV]; nlinarith only [mul_nonneg hc.le hW, hY, hc]
    have h3 : c * φ ≤ (1 + c) * φ * V := by
      have : c * φ ≤ (1 + c) * φ := by nlinarith only [hφ]
      exact this.trans (le_mul_of_one_le_right (by positivity) hV1)
    have h5 : 0 ≤ (1 + c) * V := by positivity
    rw [hM]
    nlinarith only [h1, h2, h3, h5]
  have hax' : ax ≤ U := by linarith
  have hwx' : wx ≤ M * V := by
    have h1 : wx ≤ W + c * Y := by linarith
    have : W + c * Y ≤ (1 + c) * V := by
      rw [hV]; nlinarith only [mul_nonneg hc.le hW, hY, hc]
    exact h1.trans (this.trans (mul_le_mul_of_nonneg_right hcM' (by linarith)))
  have hQ' : Qy ≤ 8 * M ^ 2 * (U * V) := by
    have := mul_le_mul hay' hwy' hwy0 (by positivity)
    nlinarith only [this, hQy]
  -- term (a)–(b): the filter
  have hG0 : 0 ≤ wy + c * ay + c * ax + wx := by positivity
  have hG : q * h0 ≤ 2 * φ * (wy + c * ay + c * ax + wx) := by
    have h4 : h0 ≤ ε * (wy + c * ay + c * ax + wx) := by
      have e1 : ψ1 * wy ≤ ε * wy := mul_le_mul_of_nonneg_right hψ1 hwy0
      have e2 : wψ * ay ≤ c * ε * ay := mul_le_mul_of_nonneg_right hwψ hay0
      have e3 : ax * wψ ≤ ax * (c * ε) := mul_le_mul_of_nonneg_left hwψ hax0
      have e4 : wx * ψ1 ≤ wx * ε := mul_le_mul_of_nonneg_left hψ1 hwx0
      nlinarith only [hh0, e1, e2, e3, e4]
    calc q * h0 ≤ q * (ε * (wy + c * ay + c * ax + wx)) := mul_le_mul_of_nonneg_left h4 hq0.le
      _ = (q * ε) * (wy + c * ay + c * ax + wx) := by ring
      _ ≤ 2 * φ * (wy + c * ay + c * ax + wx) := mul_le_mul_of_nonneg_right hqε hG0
  have hG' : wy + c * ay + c * ax + wx ≤ 6 * M ^ 2 * (U * V) := by
    have e1 : c * ay ≤ M * (2 * M * U) := mul_le_mul hcM hay' hay0 hM0
    have e2 : c * ax ≤ M * U := mul_le_mul hcM hax' hax0 hM0
    have e3 : M * V ≤ M ^ 2 * (U * V) := by
      have h0 : V ≤ U * V := le_mul_of_one_le_left (by linarith) hU1
      have : V ≤ M * (U * V) := by nlinarith only [mul_le_mul hM1 h0 (by linarith) hM0]
      calc M * V ≤ M * (M * (U * V)) := mul_le_mul_of_nonneg_left this hM0
        _ = _ := by ring
    have e4 : M * U ≤ M ^ 2 * (U * V) := by
      have h0 : U ≤ U * V := le_mul_of_one_le_right (by linarith) hV1
      have : U ≤ M * (U * V) := by nlinarith only [mul_le_mul hM1 h0 (by linarith) hM0]
      calc M * U ≤ M * (M * (U * V)) := mul_le_mul_of_nonneg_left this hM0
        _ = _ := by ring
    have e5 : M * (2 * M * U) = 2 * (M ^ 2 * U) := by ring
    have e6 : M ^ 2 * U ≤ M ^ 2 * (U * V) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by linarith) hV1) (by positivity)
    nlinarith only [hwy', hwx', e1, e2, e3, e4, e5, e6]
  have hUV0 : 0 ≤ U * V := by linarith
  have hT1 : q * |X1| ≤ a * (12 * M ^ 3 * (U * V)) := by
    calc q * |X1| ≤ q * (a * h0) := mul_le_mul_of_nonneg_left h1 hq0.le
      _ = a * (q * h0) := by ring
      _ ≤ a * (2 * φ * (wy + c * ay + c * ax + wx)) := mul_le_mul_of_nonneg_left hG ha
      _ ≤ a * (2 * M * (6 * M ^ 2 * (U * V))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (by linarith) hG' hG0 (by positivity)) ha
      _ = a * (12 * M ^ 3 * (U * V)) := by ring
  have hqn : q * n0 ≤ 2 * (wF * f0) := by
    have := mul_le_mul_of_nonneg_left hn0 hq0.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hq0.ne'] at this
  have hY' : Y ≤ U * V := by
    have : Y ≤ V := by linarith
    exact this.trans (le_mul_of_one_le_left (by linarith) hU1)
  have hT2 : q * |X2| ≤ a * (2 * M ^ 3 * (B * Y + 8 * (Y * (U * V)) + U * V)) := by
    have hs' : s' ≤ B + 8 * M ^ 2 * (U * V) + φ := by linarith
    have hwf : wF * f0 ≤ c * Y * a := mul_le_mul (hwF.trans hcbF) hf0a hf0 (by positivity)
    have k1 : q * |X2| ≤ (B + 8 * M ^ 2 * (U * V) + φ) * (2 * (c * Y * a)) := by
      calc q * |X2| ≤ q * (s' * n0) := mul_le_mul_of_nonneg_left h2 hq0.le
        _ = s' * (q * n0) := by ring
        _ ≤ s' * (2 * (wF * f0)) := mul_le_mul_of_nonneg_left hqn hs0
        _ ≤ (B + 8 * M ^ 2 * (U * V) + φ) * (2 * (c * Y * a)) :=
            mul_le_mul hs' (by linarith) (by positivity) (by positivity)
    have hcY : c * Y ≤ M * Y := mul_le_mul_of_nonneg_right hcM hY
    have hM2 : M ≤ M ^ 2 := by nlinarith only [hM1]
    have hM3 : M ^ 2 ≤ M ^ 3 := by nlinarith only [hM1, hM0]
    have p1 : B * (c * Y) ≤ M ^ 3 * (B * Y) := by
      have : B * (c * Y) ≤ B * (M * Y) := mul_le_mul_of_nonneg_left hcY hB
      nlinarith only [this, mul_le_mul_of_nonneg_right (hM2.trans hM3) (mul_nonneg hB hY)]
    have p2 : 8 * M ^ 2 * (U * V) * (c * Y) ≤ M ^ 3 * (8 * (Y * (U * V))) := by
      have : (c * Y) ≤ M * Y := hcY
      have h8 : 0 ≤ 8 * M ^ 2 * (U * V) := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left this h8]
    have p3 : φ * (c * Y) ≤ M ^ 3 * (U * V) := by
      have : φ * (c * Y) ≤ M * (M * (U * V)) :=
        mul_le_mul hφM ((hcY).trans (mul_le_mul_of_nonneg_left hY' hM0)) (by positivity) hM0
      nlinarith only [this, mul_le_mul_of_nonneg_right hM3 hUV0]
    have : (B + 8 * M ^ 2 * (U * V) + φ) * (2 * (c * Y * a)) =
        2 * a * (B * (c * Y) + 8 * M ^ 2 * (U * V) * (c * Y) + φ * (c * Y)) := by ring
    rw [this] at k1
    refine k1.trans ?_
    have := add_le_add (add_le_add p1 p2) p3
    nlinarith only [mul_le_mul_of_nonneg_left this (by linarith : 0 ≤ 2 * a)]
  have hT3 : q * |X3| ≤ a * (2 * M ^ 3 * (W * Y + 8 * (W * (U * V)))) := by
    have hqX : q * |X3| ≤ 2 * (wS * (fd * f0)) := by
      have := mul_le_mul_of_nonneg_left h3 hq0.le
      rwa [← mul_assoc, mul_div_cancel₀ _ hq0.ne'] at this
    have hfd' : fd ≤ Y + 8 * M ^ 2 * (U * V) := by linarith
    have k1 : wS * (fd * f0) ≤ W * ((Y + 8 * M ^ 2 * (U * V)) * a) :=
      mul_le_mul hwS (mul_le_mul hfd' hf0a hf0 (by positivity)) (by positivity) hW
    have hM3 : 1 ≤ M ^ 3 := one_le_pow₀ hM1
    have hM23 : M ^ 2 ≤ M ^ 3 := by nlinarith only [hM1, hM0]
    have p1 : W * Y ≤ M ^ 3 * (W * Y) := le_mul_of_one_le_left (by positivity) hM3
    have p2 : M ^ 2 * (W * (U * V)) ≤ M ^ 3 * (W * (U * V)) :=
      mul_le_mul_of_nonneg_right hM23 (by positivity)
    have e : W * ((Y + 8 * M ^ 2 * (U * V)) * a) = a * (W * Y + 8 * (M ^ 2 * (W * (U * V)))) := by
      ring
    rw [e] at k1
    have : a * (W * Y + 8 * (M ^ 2 * (W * (U * V)))) ≤ a * (M ^ 3 * (W * Y + 8 * (W * (U * V)))) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [p1, p2]) ha
    nlinarith only [hqX, k1, this]
  -- the threshold
  set FF := W + B * Y + Y * (A + P + 1) * (W + Y + 1) + W * (A + P + 1) * (W + Y + 1) + W * Y +
    (A + P + W + Y) + 1 with hFF
  have hFF1 : B * Y + Y * (U * V) + W * (U * V) + W * Y ≤ FF := by
    rw [hFF, hU, hV]; nlinarith only [hW, hA, hP, hY]
  have hFF2 : U * V ≤ FF := by
    have : U ≤ U * V := le_mul_of_one_le_right (by linarith) hV1
    rw [hFF]; rw [hU, hV] at this ⊢
    nlinarith only [this, hW, hA, hP, hY, mul_nonneg hB hY, mul_nonneg hW hY,
      mul_le_mul_of_nonneg_left this (by linarith : 0 ≤ W + Y)]
  have hM4 : (1 + c) ^ 4 * (1 + φ) ^ 4 = M ^ 4 := by rw [hM]; ring
  have hq' : 2 ^ 20 * M ^ 4 * FF ≤ q := by
    rw [← hM4]; linarith only [hthr]
  have hFF0 : 0 ≤ FF := le_trans (by positivity) hFF2
  have hkey : q * (2 * |X1| + 2 * |X2| + 4 * |X3|) ≤ a * (q / 2) := by
    have hsum : q * (2 * |X1| + 2 * |X2| + 4 * |X3|) ≤ a * (M ^ 3 * (92 * FF)) := by
      have h3 : 0 ≤ a * M ^ 3 := mul_nonneg ha (pow_nonneg hM0 3)
      have hp : 28 * (U * V) + 4 * (B * Y) + 32 * (Y * (U * V)) + 8 * (W * Y) +
          64 * (W * (U * V)) ≤ 92 * FF := by
        nlinarith only [hFF1, hFF2, mul_nonneg hB hY, mul_nonneg hY hUV0, mul_nonneg hW hY]
      nlinarith only [hT1, hT2, hT3, mul_le_mul_of_nonneg_left hp h3]
    refine hsum.trans (mul_le_mul_of_nonneg_left ?_ ha)
    have : M ^ 3 ≤ M ^ 4 := pow_le_pow_right₀ hM1 (by norm_num)
    nlinarith only [hq', mul_le_mul_of_nonneg_right this hFF0, hFF0, pow_nonneg hM0 3]
  have hT : 2 * |X1| + 2 * |X2| + 4 * |X3| ≤ a / 2 := by
    have : q * (2 * |X1| + 2 * |X2| + 4 * |X3|) ≤ q * (a / 2) := by linarith only [hkey]
    exact le_of_mul_le_mul_left this hq0
  nlinarith only [hT, neg_abs_le X1, neg_abs_le X2, neg_abs_le X3, sq_nonneg (a - 1 / 4)]

/-- `ℓ²` Cauchy–Schwarz for the `σ = 0` pairing. -/
private lemma abs_pair_zero_le_l2 {c F : Field} (hc : Summable fun k => ‖c k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) :
    |pair 0 c F| ≤ Real.sqrt (∑' k, ‖c k‖ ^ 2) * Real.sqrt (∑' k, ‖F k‖ ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hc' : Summable fun k => ‖c k‖ ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hc
  have hF' : Summable fun k => ‖F k‖ ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hF
  have key : Summable (fun k => ‖c k‖ * ‖F k‖) ∧ ∑' k, ‖c k‖ * ‖F k‖ ≤
      Real.sqrt (∑' k, ‖c k‖ ^ 2) * Real.sqrt (∑' k, ‖F k‖ ^ 2) := by
    have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq
      (fun k => norm_nonneg (c k)) (fun k => norm_nonneg (F k)) hc' hF'
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using h
  rw [pair, ← Real.norm_eq_abs]
  refine (tsum_of_norm_bounded key.1.hasSum fun k => ?_).trans key.2
  have h1 : sobWeight 0 k ≤ 1 := by
    unfold sobWeight
    split_ifs <;> simp
  refine (norm_pair_term_le' 0 c F k).trans ?_
  rw [mul_assoc]
  exact mul_le_of_le_one_left (by positivity) h1

/-- The filter force splits as `H_ψ = Q(ψ, y) + Q(x, ψ)`. -/
private lemma Hpsi_eq (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    Hpsi r g y u = Qphase (r * u) (psi r 0 g u) (y u) +
      Qphase (r * u) (actual r g y u) (psi r 0 g u) := by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  have e1 := (majorized_Qphase (r * u)).sub_left 0 (y u) (actual r g y u) (y u) hy.mz hx.mz hy.mz
  have e2 := (majorized_Qphase (r * u)).sub_right 0 (actual r g y u) (y u) (actual r g y u)
    hx.mz hy.mz hx.mz
  have hyx : y u - actual r g y u = psi r 0 g u := by simp [actual]
  simp only [hyx] at e1 e2
  rw [Hpsi, e1, e2]
  abel

/-- The pointwise E4.5 budget: `W₀' + a_F² ≤ 1/8` on a prefix where the caps hold. -/
private lemma W0RHS_budget (h : ActualSol μ φ r g y Ty) (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) {caps : Caps}
    {s t : ℝ} (hP : PrefixHyp (kinThreshold μ φ) r g y Ty caps s t) {u : ℝ} (hu : u ∈ Icc s t) :
    W0RHS r g y u + fastNorm 1 r g y u ^ 2 ≤ 1 / 8 := by
  have hr1 := (one_le_kinThreshold hμ hφ caps).trans hP.thr
  have hr : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr1; linarith
  have hu0 : 0 ≤ u := hP.hs.trans hu.1
  have huT := lt_lifespan hu.2 hP.ht
  have hx := actual_adm h hu0 huT
  have hy := h.sol.adm u hu0 huT
  have hF := hx.PiF
  have hS := hx.PiS
  have hψ : Adm 2 (psi r 0 g u) := psi_adm h.force_adm u hu0
  have hψb := (psi_bound (t₀ := 0) hr h.force_adm u hu0).2
  obtain ⟨cF1, cF2, cS1, cS2, cW⟩ := hP.onPrefix.1 u hu
  have hF2 : Summable fun k => ‖PiF (actual r g y u) k‖ ^ 2 :=
    summable_norm_sq_of_inH (hF.inH.mono (by norm_num))
  have hQyy := hnorm_Qm_zero_le (phaseM_bdd (r * u)) hy.mz hy.mz
  have hQ1 := hnorm_Qm_zero_le (phaseM_bdd (r * u)) hψ.mz hy.mz
  have hQ2 := hnorm_Qm_zero_le (phaseM_bdd (r * u)) hx.mz hψ.mz
  have hH0 : InH 0 (Hpsi r g y u) := by
    rw [Hpsi_eq h hu0 huT]; exact hQ1.1.add hQ2.1
  have hh0 : hnorm 0 (Hpsi r g y u) ≤ hnorm 1 (psi r 0 g u) * wiener (y u) +
      wiener (psi r 0 g u) * hnorm 1 (y u) + hnorm 1 (actual r g y u) * wiener (psi r 0 g u) +
      wiener (actual r g y u) * hnorm 1 (psi r 0 g u) := by
    rw [Hpsi_eq h hu0 huT]
    refine (hnorm_add_le hQ1.1 hQ2.1).trans ?_
    linarith [hQ1.2, hQ2.2]
  have h1 : |pair 0 (PiF (actual r g y u)) (Hpsi r g y u)| ≤
      hnorm 1 (PiF (actual r g y u)) * hnorm 0 (Hpsi r g y u) := by
    have := (pair_le (σ := 0) (hF.inH.mono (by norm_num)) (hH0.mono (by norm_num))).2
    rw [zero_add] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (hnorm_nonneg _ _))
    exact hnorm_mono (by norm_num) hH0
  obtain ⟨hNs, hNle⟩ := hnorm_kinN_le (τ := r * u) hr (summable_wiener hF.inH) hF2
  obtain ⟨hSd, hSdle⟩ := slowRHS_l2 h hu0 huT
  obtain ⟨hFd, hFdle⟩ := fastRHS_l2 h hu0 huT
  have h2 := abs_pair_zero_le_l2 hSd (summable_norm_sq_of_inH hNs)
  rw [← hnorm_zero_eq (kinN_zero_mode _ _)] at h2
  have h3 := abs_pair_kinN_le (τ := r * u) hr (summable_wiener hS.inH) hFd hF2
  have hf0 : Real.sqrt (∑' k, ‖PiF (actual r g y u) k‖ ^ 2) ≤ hnorm 1 (PiF (actual r g y u)) := by
    rw [← hnorm_zero_eq hF.mean]; exact hnorm_mono (by norm_num) (hF.inH.mono (by norm_num))
  have hyx : y u = actual r g y u + psi r 0 g u := by simp [actual]
  have hay : hnorm 1 (y u) ≤ hnorm 1 (actual r g y u) + hnorm 1 (psi r 0 g u) := by
    rw [hyx]; exact hnorm_add_le (hx.inH.mono (by norm_num)) (hψ.inH.mono (by norm_num))
  have hwy : wiener (y u) ≤ wiener (actual r g y u) + wiener (psi r 0 g u) := by
    rw [hyx]; exact wiener_add_le (summable_wiener hx.inH) (summable_wiener hψ.inH)
  have hxSF := PiS_add_PiF (actual r g y u)
  have hax : hnorm 1 (actual r g y u) ≤
      hnorm 1 (PiS (actual r g y u)) + hnorm 1 (PiF (actual r g y u)) := by
    conv_lhs => rw [← hxSF]
    exact hnorm_add_le (hS.inH.mono (by norm_num)) (hF.inH.mono (by norm_num))
  have hwx : wiener (actual r g y u) ≤
      wiener (PiS (actual r g y u)) + wiener (PiF (actual r g y u)) := by
    conv_lhs => rw [← hxSF]
    exact wiener_add_le (summable_wiener hS.inH) (summable_wiener hF.inH)
  have hqε : |r| * hnorm 2 (psi r 0 g u) ≤ 2 * φ := by
    have hr0 : 0 < |r| := by linarith
    have hg12 : hnorm 1 g ≤ hnorm 2 g := hnorm_mono (by norm_num) h.force_adm.inH
    have := (le_div_iff₀ hr0).1 hψb
    nlinarith [h.force_le]
  have hthr : 2 ^ 20 * (1 + c4) ^ 4 * (1 + φ) ^ 4 * fourierFloor caps ≤ |r| := by
    refine le_trans ?_ hP.thr
    have h5 : 0 ≤ role22 + role23 φ + role24 caps + role25 caps + role26 φ + role27 φ caps := by
      have := cp_nonneg caps.yF
      have := cp_nonneg caps.BS
      have := c4_pos
      unfold role22 role23 role24 role25 role26 role27
      positivity
    have := role36_nonneg hμ hφ caps
    have := kineticFloor_nonneg hμ hφ caps
    have hC : 0 ≤ kinC φ := (zero_le_one).trans (one_le_kinC φ hφ)
    unfold kinThreshold
    have e : 2 ^ 20 * (1 + c4) ^ 4 * (1 + φ) ^ 4 = kinC φ := rfl
    rw [e]
    nlinarith
  unfold fourierFloor at hthr
  simp only [W0RHS, fastNorm]
  exact budget_alg c4_pos hφ hr1 (cp_nonneg _) (cp_nonneg _) (cp_nonneg _) (cp_nonneg _)
    (hnorm_nonneg _ _) (cF1.trans (le_cp _)) (Real.sqrt_nonneg _) hf0 (hnorm_nonneg _ _) hqε
    (hnorm_mono (by norm_num) hψ.inH) (wiener_le hψ.mz) (cS1.trans (le_cp _))
    (cF2.trans (le_cp _)) (cS2.trans (le_cp _)) h.force_le (hnorm_nonneg _ _) hax
    (wiener_nonneg _) hwx (hnorm_nonneg _ _) hay (wiener_nonneg _) hwy hQyy.2 hh0 h1
    (Real.sqrt_nonneg _) hSdle (wiener_nonneg _) (wiener_le hF.mz) hNle h2 (Real.sqrt_nonneg _)
    hFdle (cW.trans (le_cp _)) h3 hthr

/-- **E4.5, the kinetic error budget** (TeX eq. quant-kinetic, `W₀' + a_F² ≤ 1/8`, integrated on
every subinterval of a prefix where the caps hold and `kinThreshold μ φ caps ≤ q`).

Proof plan (survey §2.1 (b)): by `W0_identity`, `W₀(t') − W₀(s') = ∫ (−2a_F² − 2⟨F,H_ψ⟩ −
2⟨S',N(F,F)⟩ − 4⟨S,N(F',F)⟩)`, so it suffices to bound the three remainders pointwise by
`a_F² + 1/8` on `[s,t]`:
* `|2⟨F, H_ψ⟩| ≤ 2‖F‖₀(2‖Q(x,ψ)‖₀ + ‖Q(ψ,ψ)‖₀)`, `‖Q(x,ψ)‖₀ ≤ ‖x‖₁𝒜(ψ) + 𝒜(x)‖ψ‖₁`
  (`hnorm_Qm_zero_le`), `‖ψ‖₂ ≤ 2‖g‖₁/q` (`psi_bound`), `𝒜(ψ) ≤ c₄‖ψ‖₂` — terms (a), (b);
* `|2⟨S', N(F,F)⟩| ≤ 2‖S'‖₀ ‖N(F,F)‖₀`, `‖N(F,F)‖₀ ≤ (2/q)𝒜(F)‖F‖₀` (`hnorm_kinN_le`),
  `‖S'‖₀ ≤ b_S + ‖Q(y,y)‖₀ + φ` — terms (c), (d), (e);
* `|4⟨S, N(F',F)⟩| ≤ (8/q) W_S ‖F'‖₀‖F‖₀` (`abs_pair_kinN_le`, the fixed-slow-output Cauchy),
  `‖F'‖₀ ≤ b_F + ‖Q(y,y)‖₀` — terms (f), (g);
with `𝒜(F) ≤ c₄ b_F`, `‖F‖₀ ≤ a_F`, the caps `a_F ≤ P_F`, `b_F ≤ y`, `a_S ≤ A_S`, `b_S ≤ B_S`,
`W_S ≤ WS` (`OnPrefix`) and `‖y‖₁ ≤ a_S + a_F + ‖ψ‖₁`, `𝒜(y) ≤ W_S + c₄ b_F + c₄‖ψ‖₂`.  Each
product `(poly/q)·a_F` is split by Young into `a_F²/8 + 2·poly²/q²`; the seven absorbed pieces
total `≤ a_F²`, and `q ≥ kinThreshold` (whose `fourierFloor` carries exactly these monomials,
`kinC` the constants) makes the seven constants total `≤ 1/8`.  Then integrate
(`intervalIntegral.integral_mono_on`, with the integrability from `W0_identity`'s right-hand
side and `intervalIntegrable_fast`). -/
theorem W0_diff_ineq (h : ActualSol μ φ r g y Ty) (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) {caps : Caps}
    {s t : ℝ} (hP : PrefixHyp (kinThreshold μ φ) r g y Ty caps s t) :
    ∀ s' t' : ℝ, s ≤ s' → s' ≤ t' → t' ≤ t →
      W0 r g y t' - W0 r g y s' + (∫ u in s'..t', fastNorm 1 r g y u ^ 2) ≤ (t' - s') / 8 := by
  intro s' t' hs' hst' ht'
  have hr1 := (one_le_kinThreshold hμ hφ caps).trans hP.thr
  have hr : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr1; linarith
  have hs0 : 0 ≤ s' := hP.hs.trans hs'
  have ht'T := lt_lifespan ht' hP.ht
  obtain ⟨hI1, hI2⟩ := intervalIntegrable_fast h hs0 hst' ht'T
  have hI3 := (kinCorr_identity h hr hs0 hst' ht'T).1
  have hI : IntervalIntegrable (W0RHS r g y) volume s' t' := by
    refine (((hI1.const_mul (-2)).add (hI2.const_mul 2)).sub (hI3.const_mul 2)).congr
      fun u hu => ?_
    rw [uIoc_of_le hst'] at hu
    have hu0 : 0 ≤ u := hs0.trans hu.1.le
    have huT := lt_lifespan hu.2 ht'T
    simp only [W0RHS, kinCorrRHS]
    rw [pair_fast_force_eq h hu0 huT]
    ring
  rw [W0_identity h hr hs0 hst' ht'T]
  have hmono : ∫ u in s'..t', W0RHS r g y u ≤ ∫ u in s'..t', (1 / 8 - fastNorm 1 r g y u ^ 2) := by
    refine intervalIntegral.integral_mono_on hst' hI (intervalIntegrable_const.sub hI1)
      fun u hu => ?_
    have := W0RHS_budget h hμ hφ hP ⟨hs'.trans hu.1, hu.2.trans ht'⟩
    linarith
  rw [intervalIntegral.integral_sub intervalIntegrable_const hI1, intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  linarith

/-! ### Assembly -/

/-- `W₀` is continuous on `[0,b]` (from the kinetic law and `kinCorr_identity`). -/
theorem continuousOn_W0 (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) : ContinuousOn (W0 r g y) (Icc 0 b) := by
  have h1 := continuousOn_fastNorm_sq h (σ := 0) (Or.inl rfl) hb hbT
  have h2 : ContinuousOn (kinCorr r g y) (Icc 0 b) := by
    have hI := (kinCorr_identity h hr le_rfl hb hbT).1
    have hc : ContinuousOn (fun t => kinCorr r g y 0 + ∫ u in (0 : ℝ)..t, kinCorrRHS r g y u)
        (Icc 0 b) := by
      have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
        (f := kinCorrRHS r g y) (a := 0) (b := b)
        (by rwa [uIcc_of_le hb, ← intervalIntegrable_iff_integrableOn_Icc_of_le hb])
      rw [uIcc_of_le hb] at this
      exact continuousOn_const.add this
    refine hc.congr fun t ht => ?_
    have := (kinCorr_identity h hr le_rfl ht.1 (lt_lifespan ht.2 hbT)).2
    linarith
  show ContinuousOn (fun t => fastNorm 0 r g y t ^ 2 - 2 * kinCorr r g y t) (Icc 0 b)
  exact h1.sub (continuousOn_const.mul h2)

/-- **E4 output with the explicit threshold**: `KineticInterface μ φ (kinThreshold μ φ)`, from the
coercivity, the true-zero bound, the error budget `W0_diff_ineq` and `gronwall_decay_max`
(`λ = 4/5`, `β = 1/8`; `(4/5)W₀ ≤ a_F²` by coercivity and `‖F‖₀ ≤ a_F`). -/
theorem kineticInterface_of_threshold (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) :
    KineticInterface μ φ (kinThreshold μ φ) := by
  intro r g y Ty h
  refine ⟨W0 r g y, fun caps s t hP => ?_⟩
  have hr1 := one_le_abs_of_prefix hμ hφ hP
  have hr : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr1; linarith
  have hcoer : ∀ u ∈ Icc s t, 3 / 4 * fastNorm 0 r g y u ^ 2 ≤ W0 r g y u ∧
      W0 r g y u ≤ 5 / 4 * fastNorm 0 r g y u ^ 2 := fun u hu => W0_coercive h hμ hφ hP hu
  have hdiff := W0_diff_ineq h hμ hφ hP
  refine ⟨hcoer, fun hs0 => ?_, hdiff s t le_rfl hP.hst le_rfl, ?_⟩
  · subst hs0
    exact W0_zero_le h hμ hφ hP
  · have ht0 : 0 ≤ t := hP.hs.trans hP.hst
    have hW := (continuousOn_W0 h hr ht0 hP.ht).mono (Icc_subset_Icc_left hP.hs)
    have ha := (continuousOn_fastNorm_sq h (σ := 1) (Or.inr rfl) ht0 hP.ht).mono
      (Icc_subset_Icc_left hP.hs)
    have key : ∀ s' t', s ≤ s' → s' ≤ t' → t' ≤ t →
        W0 r g y t' + 4 / 5 * ∫ u in s'..t', W0 r g y u ≤ W0 r g y s' + 1 / 8 * (t' - s') := by
      intro s' t' hs' hst' ht'
      have hsub : Icc s' t' ⊆ Icc s t := Icc_subset_Icc hs' ht'
      have hWI : IntervalIntegrable (W0 r g y) volume s' t' :=
        (hW.mono hsub).intervalIntegrable_of_Icc hst'
      have haI : IntervalIntegrable (fun u => fastNorm 1 r g y u ^ 2) volume s' t' :=
        (ha.mono hsub).intervalIntegrable_of_Icc hst'
      have hmono : ∫ u in s'..t', 4 / 5 * W0 r g y u ≤ ∫ u in s'..t', fastNorm 1 r g y u ^ 2 := by
        refine intervalIntegral.integral_mono_on hst' (hWI.const_mul _) haI fun u hu => ?_
        have hu' := hsub hu
        have h1 := (hcoer u hu').2
        have hx := actual_adm h (hP.hs.trans hu'.1) (lt_lifespan hu'.2 hP.ht)
        have h2 : fastNorm 0 r g y u ≤ fastNorm 1 r g y u :=
          hnorm_mono (by norm_num) (hx.PiF.inH.mono (by norm_num))
        have h3 := hnorm_nonneg 0 (PiF (actual r g y u))
        have h4 : fastNorm 0 r g y u ^ 2 ≤ fastNorm 1 r g y u ^ 2 := by
          unfold fastNorm at h2 h3 ⊢
          nlinarith
        linarith
      rw [intervalIntegral.integral_const_mul] at hmono
      have := hdiff s' t' hs' hst' ht'
      linarith
    have := gronwall_decay_max hP.hst (by norm_num : (0 : ℝ) < 4 / 5)
      (by norm_num : (0 : ℝ) ≤ 1 / 8) hW key
    have e : (1 : ℝ) / 8 / (4 / 5) = 5 / 32 := by norm_num
    rw [e] at this
    exact this

/-- **E4 (final form, as `fixed_force_of_interfaces` consumes it)**: an explicit kinetic role
threshold `q₀ = kinThreshold` with `KineticInterface μ φ (q₀ μ φ)` for all `μ, φ ≥ 0` and the R1
degree duty `DegreeBelow σ (dOf σ) e q₀` for every `σ ∈ [0,1)` and slow exponents with
`eA ≤ 2`, `eB ≤ 4`, `eW ≤ 5/2` (covering `slowExpHA`, `slowExpEl` and the Fourier-side slow route
`eW = 5/2`).  Fully proved (no open step). -/
theorem kineticInterface (e : SlowExp) (heA : e.eA ≤ 2) (heB : e.eB ≤ 4) (heW : e.eW ≤ 5 / 2) :
    ∃ q₀ : ℝ → ℝ → Caps → ℝ,
      (∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ → KineticInterface μ φ (q₀ μ φ)) ∧
      ∀ σ : ℝ, 0 ≤ σ → σ < 1 → DegreeBelow σ (dOf σ) e q₀ :=
  ⟨kinThreshold, fun _ _ hμ hφ => kineticInterface_of_threshold hμ hφ,
    fun _ h0 h1 => kinetic_degree h0 h1 e heA heB heW⟩

end Quant

end OVNS

end
