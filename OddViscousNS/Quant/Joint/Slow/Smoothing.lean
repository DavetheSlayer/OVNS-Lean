import OddViscousNS.Quant.Joint.Slow.Poly
import OddViscousNS.Quant.Energy.Slow.Energy

/-!
# E7-P: even-power laws and drift-uniform smoothing on polynomial paths

Steps 2–4 of `Joint/Slow/Plan.lean`.  A *polynomial path* is `w(t) = ∑_{k ∈ A} c_k(t) e_k`, real,
slow, with `C¹` coefficients, and any divergence-free polynomial drift `U(t)`; its source is
*defined* by `F = ∂_t w − Δw + U·∇w`.  All statements are uniform in `U` and in `A`.

* fixed time: `mP q P = ∫ |P|^{2q}`; Ladyzhenskaya `mP_double_le`; the absorption of an `L²` source
  `nn2_pow_odd_le`, whence (`energy_ineq`) the law `m_q' + d_q ≤ y^q + 201 q² ‖F‖₂² y^{q−1}`, for
  any `y > 0` with `m_q ≤ y^q`;
* `propagate`: `‖w(t)‖²_{2q} ≤ e^{(t−τ)/q} (2 ‖w(τ)‖²_{2q} + 201 q ∫ ‖F‖₂²)`, additive in the
  source;
* `moser`: `L² → L^{2·2ⁿ}` in a unit, by good times;
* `smoothing_four`: `L² → L⁴`, its first step `n = 1`, from the energy.

No propagator, no adjoint, no Nash, no regularization of the drift.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.Slow

open GN

/-! ### Fixed time: the norms of powers -/

/-- `m_q(P) = ∫ |P|^{2q}`. -/
def mP (q : ℕ) (P : Pol) : ℝ := ∫ x, ‖ev P x‖ ^ (2 * q) ∂μT

lemma mP_nonneg (q : ℕ) (P : Pol) : 0 ≤ mP q P := integral_nonneg fun _ => by positivity

lemma mP_eq_nn2 (q : ℕ) (P : Pol) : mP q P = nn2 (P ^ q) := by
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_pow, ContinuousMap.coe_pow, Pi.pow_apply, norm_pow]
  ring

lemma mP_two_mul (q : ℕ) (P : Pol) : mP (2 * q) P = nn4 (P ^ q) := by
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_pow, ContinuousMap.coe_pow, Pi.pow_apply, norm_pow]
  ring

/-- Ladyzhenskaya for `P^q`. -/
lemma mP_double_le {P : Pol} (hs : IsSlowP P) (q : ℕ) :
    mP (2 * q) P ≤ 200 * mP q P * (mP q P + grad2 (P ^ q)) := by
  rw [mP_two_mul, mP_eq_nn2]
  exact lady_poly (hs.pow q)

lemma integrable_norm_pow (P : Pol) (n : ℕ) : Integrable (fun x => ‖ev P x‖ ^ n) μT :=
  integrable_of_continuous ((ev P).continuous.norm.pow n)

/-- **The absorption of the source, the pointwise split**: for `τ = |P|²`,
`τ^{2q−1} ≤ τ^{2q}/y + y^{2q−1}`. -/
lemma nn2_pow_odd_le_aux {y : ℝ} (hy : 0 < y) {q : ℕ} (hq : 1 ≤ q) (P : Pol) :
    nn2 (P ^ (2 * q - 1)) ≤ mP (2 * q) P / y + y ^ (2 * q - 1) := by
  have hpt : ∀ x, ‖ev (P ^ (2 * q - 1)) x‖ ^ 2 ≤
      ‖ev P x‖ ^ (2 * (2 * q)) / y + y ^ (2 * q - 1) := fun x => by
    set τ := ‖ev P x‖ ^ 2 with hτ
    have hτ0 : 0 ≤ τ := by positivity
    have e1 : ‖ev (P ^ (2 * q - 1)) x‖ ^ 2 = τ ^ (2 * q - 1) := by
      simp only [map_pow, ContinuousMap.coe_pow, Pi.pow_apply, norm_pow, hτ]
      ring
    have e2 : ‖ev P x‖ ^ (2 * (2 * q)) = τ ^ (2 * q) := by
      simp only [hτ]
      ring
    rw [e1, e2]
    obtain ⟨m, hm⟩ : ∃ m, 2 * q = m + 1 := ⟨2 * q - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    rcases le_total τ y with h | h
    · have h1 : τ ^ m ≤ y ^ m := pow_le_pow_left₀ hτ0 h m
      have h2 : 0 ≤ τ ^ (m + 1) / y := by positivity
      linarith
    · have h1 : τ ^ m * y ≤ τ ^ (m + 1) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_left h (by positivity)
      have h2 : τ ^ m ≤ τ ^ (m + 1) / y := by
        rwa [le_div_iff₀ hy]
      have h3 : 0 ≤ y ^ m := by positivity
      linarith
  have hi2 : Integrable (fun x => ‖ev P x‖ ^ (2 * (2 * q)) / y + y ^ (2 * q - 1)) μT :=
    ((integrable_norm_pow P _).div_const y).add (integrable_const _)
  have h := integral_mono (integrable_norm_pow (P ^ (2 * q - 1)) 2) hi2 hpt
  simp only [integral_add ((integrable_norm_pow P _).div_const y) (integrable_const _),
    integral_div, integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  exact h

/-- **The absorption of the source**: for `y > 0`, `m_q ≤ y^q`,
`‖P^{2q−1}‖₂² ≤ 201 y^{q−1} (y^q + d_q)`. -/
lemma nn2_pow_odd_le {y : ℝ} (hy : 0 < y) {q : ℕ} (hq : 1 ≤ q) {P : Pol} (hs : IsSlowP P)
    (hm : mP q P ≤ y ^ q) :
    nn2 (P ^ (2 * q - 1)) ≤ 201 * y ^ (q - 1) * (y ^ q + grad2 (P ^ q)) := by
  have h1 := nn2_pow_odd_le_aux hy hq P
  have h2 := mP_double_le hs q
  have hd := grad2_nonneg (P ^ q)
  have hm0 := mP_nonneg q P
  have hyq : y ^ q = y * y ^ (q - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hq]
  have hy1 : 0 < y ^ (q - 1) := by positivity
  have hyq0 : 0 < y ^ q := by positivity
  have e : y ^ (2 * q - 1) = y ^ (q - 1) * y ^ q := by
    rw [← pow_add]
    congr 1
    omega
  have h3 : mP q P * (mP q P + grad2 (P ^ q)) ≤ y ^ q * (y ^ q + grad2 (P ^ q)) :=
    mul_le_mul hm (add_le_add hm le_rfl) (by positivity) (by positivity)
  have h4 : mP (2 * q) P / y ≤ 200 * y ^ (q - 1) * (y ^ q + grad2 (P ^ q)) := by
    rw [div_le_iff₀ hy]
    calc mP (2 * q) P ≤ 200 * (mP q P * (mP q P + grad2 (P ^ q))) := by linarith
      _ ≤ 200 * (y ^ q * (y ^ q + grad2 (P ^ q))) := by linarith
      _ = 200 * y ^ (q - 1) * (y ^ q + grad2 (P ^ q)) * y := by rw [hyq]; ring
  rw [e] at h1
  have h5 : 0 ≤ y ^ (q - 1) * grad2 (P ^ q) := by positivity
  nlinarith

/-! ### Fixed time: the dissipation and the law -/

/-- Pointwise real polynomials. -/
def PtReal (Q : Pol) : Prop := ∀ x, conj (ev Q x) = ev Q x

lemma RealC.ptReal {P : Pol} (hP : RealC P) : PtReal P := hP.conj_ev

lemma PtReal.mul {P Q : Pol} (hP : PtReal P) (hQ : PtReal Q) : PtReal (P * Q) := fun x => by
  simp only [map_mul, ContinuousMap.mul_apply, hP x, hQ x]

lemma PtReal.pow {P : Pol} (hP : PtReal P) (n : ℕ) : PtReal (P ^ n) := fun x => by
  simp only [map_pow, ContinuousMap.coe_pow, Pi.pow_apply, hP x]

lemma PtReal.ev_sq {Q : Pol} (hQ : PtReal Q) (x : T3) :
    ev Q x ^ 2 = ((‖ev Q x‖ ^ 2 : ℝ) : ℂ) := by
  have h : ev Q x = ((ev Q x).re : ℂ) :=
    Complex.ext rfl (by simp [Complex.conj_eq_iff_im.1 (hQ x)])
  set a := (ev Q x).re
  rw [h, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  push_cast
  ring

/-- `∫ Q² = ‖Q‖₂²` for real `Q`. -/
lemma PtReal.mean_sq {Q : Pol} (hQ : PtReal Q) : mean (Q ^ 2) = (nn2 Q : ℂ) := by
  rw [← J_ev, J_apply, nn2, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_pow, ContinuousMap.coe_pow, Pi.pow_apply]
  exact hQ.ev_sq x

lemma nn2_smul (c : ℂ) (Q : Pol) : nn2 (c • Q) = ‖c‖ ^ 2 * nn2 Q := by
  rw [nn2, nn2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_smul, ContinuousMap.smul_apply, smul_eq_mul, norm_mul, mul_pow]

/-- The dissipation of the even-power law, for real `P`. -/
lemma mean_pow_lap_eq {P : Pol} (hP : RealC P) (p : ℕ) :
    mean (P ^ (2 * p + 1) * lap P) * (((p + 1 : ℕ) : ℂ) ^ 2) =
      -((2 * p + 1 : ℕ) : ℂ) * (grad2 (P ^ (p + 1)) : ℝ) := by
  have h := mean_pow_lap P (2 * p)
  have e : ∀ i, mean (P ^ (2 * p) * D i P ^ 2) = (nn2 (P ^ p * D i P) : ℂ) := fun i => by
    have hQ : PtReal (P ^ p * D i P) := (hP.ptReal.pow p).mul (hP.D i).ptReal
    have e0 : P ^ (2 * p) * D i P ^ 2 = (P ^ p * D i P) ^ 2 := by ring
    rw [e0, hQ.mean_sq]
  have e2 : ∀ i, nn2 (D i (P ^ (p + 1))) =
      (((p + 1 : ℕ) : ℝ)) ^ 2 * nn2 (P ^ p * D i P) := fun i => by
    have h1 := D_pow i P p
    have h2 := nn2_smul ((p + 1 : ℕ) : ℂ) (P ^ p * D i P)
    rw [h1, h2]
    congr 2
    exact Complex.norm_natCast _
  have e3 : ((grad2 (P ^ (p + 1)) : ℝ) : ℂ) =
      (((p + 1 : ℕ) : ℂ)) ^ 2 * ∑ i, (nn2 (P ^ p * D i P) : ℂ) := by
    rw [grad2, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2]
    push_cast
    ring
  rw [e3, h]
  simp only [e]
  ring

lemma norm_mean_mul_le (Q F : Pol) :
    ‖mean (Q * F)‖ ≤ Real.sqrt (nn2 Q) * Real.sqrt (nn2 F) := by
  rw [← J_ev, map_mul]
  have h1 : ‖J (ev Q * ev F)‖ ≤ ∫ x, ‖ev Q x‖ * ‖ev F x‖ ∂μT :=
    norm_J_le ((ev Q).continuous.norm.mul (ev F).continuous.norm) fun x => by
      simp
  refine h1.trans ?_
  have h := integral_mul_le_sqrt (f := fun x => ‖ev Q x‖) (g := fun x => ‖ev F x‖)
    (ev Q).continuous.norm (ev F).continuous.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact h

/-- The arithmetic of `law_ineq`. -/
private lemma law_arith {Q d n f y Lr Sr : ℝ} {p : ℕ} (hQ1 : 1 ≤ Q) (hd0 : 0 ≤ d) (hn0 : 0 ≤ n)
    (hf0 : 0 ≤ f) (hy : 0 < y) (hLre : Lr * Q ^ 2 = -(2 * Q - 1) * d)
    (hS : Sr ≤ Real.sqrt n * Real.sqrt f) (hn : n ≤ 201 * y ^ p * (y ^ (p + 1) + d)) :
    2 * Q * (Lr + Sr) + d ≤ y ^ (p + 1) + 201 * Q ^ 2 * f * y ^ p := by
  -- `2 Q L.re ≤ −2 d`
  have hLle : 2 * Q * Lr ≤ -(2 * d) := by
    have h1 : Lr = -(2 * Q - 1) * d / Q ^ 2 := by
      field_simp
      linarith
    rw [h1]
    have : 2 * Q * (-(2 * Q - 1) * d / Q ^ 2) = -(2 * (2 * Q - 1) / Q) * d := by
      field_simp
    rw [this]
    have h3 : 2 ≤ 2 * (2 * Q - 1) / Q := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    nlinarith
  set A := Real.sqrt n with hA
  set B := Real.sqrt f with hB
  have hA2 : A ^ 2 = n := Real.sq_sqrt hn0
  have hB2 : B ^ 2 = f := Real.sq_sqrt hf0
  set c : ℝ := 201 * y ^ p with hc
  have hc0 : 0 < c := by positivity
  have hY : 2 * Q * (A * B) ≤ A ^ 2 / c + c * Q ^ 2 * B ^ 2 := by
    have h1 : 2 * Q * (A * B) * c ≤ A ^ 2 + (c * Q * B) ^ 2 := by
      nlinarith [sq_nonneg (A - c * Q * B)]
    have h2 : A ^ 2 / c + c * Q ^ 2 * B ^ 2 = (A ^ 2 + (c * Q * B) ^ 2) / c := by
      field_simp
    rw [h2, le_div_iff₀ hc0]
    exact h1
  have hn' : A ^ 2 / c ≤ y ^ (p + 1) + d := by
    rw [hA2, div_le_iff₀ hc0]
    linarith
  have hfin : c * Q ^ 2 * B ^ 2 = 201 * Q ^ 2 * f * y ^ p := by
    rw [hB2, hc]
    ring
  nlinarith

/-- **The even-power law at a fixed time**: `Ṗ = ΔP − U·∇P + F` gives
`m_q' + d_q ≤ y^q + 201 q² ‖F‖₂² y^{q−1}`, for `y > 0`, `m_q ≤ y^q`, uniformly in `U`. -/
theorem law_ineq {P F Pd : Pol} {U : Fin 3 → Pol} (hP : RealC P) (hs : IsSlowP P) (hU : DivFree U)
    (hPd : Pd = lap P - trans U P + F) {q : ℕ} (hq : 1 ≤ q) {y : ℝ} (hy : 0 < y)
    (hm : mP q P ≤ y ^ q) :
    2 * (q : ℝ) * (mean (P ^ (2 * q - 1) * Pd)).re + grad2 (P ^ q) ≤
      y ^ q + 201 * (q : ℝ) ^ 2 * nn2 F * y ^ (q - 1) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have e1 : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
  simp only [Nat.add_sub_cancel]
  rw [e1] at *
  set d := grad2 (P ^ (p + 1)) with hd
  have hd0 : 0 ≤ d := grad2_nonneg _
  have hn := nn2_pow_odd_le (q := p + 1) hy (by omega) hs hm
  rw [show 2 * (p + 1) - 1 = 2 * p + 1 by omega] at hn
  simp only [Nat.add_sub_cancel] at hn
  set n := nn2 (P ^ (2 * p + 1)) with hndef
  have hn0 : 0 ≤ n := nn2_nonneg _
  have hf0 : 0 ≤ nn2 F := nn2_nonneg _
  have htr : mean (P ^ (2 * p + 1) * trans U P) = 0 := mean_pow_trans hU P _
  have hsplit : mean (P ^ (2 * p + 1) * Pd) =
      mean (P ^ (2 * p + 1) * lap P) + mean (P ^ (2 * p + 1) * F) := by
    have e : P ^ (2 * p + 1) * Pd = P ^ (2 * p + 1) * lap P - P ^ (2 * p + 1) * trans U P +
        P ^ (2 * p + 1) * F := by rw [hPd]; ring
    have e' : mean (P ^ (2 * p + 1) * lap P - P ^ (2 * p + 1) * trans U P +
        P ^ (2 * p + 1) * F) = mean (P ^ (2 * p + 1) * lap P) -
        mean (P ^ (2 * p + 1) * trans U P) + mean (P ^ (2 * p + 1) * F) := by
      simp [mean, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub]
    rw [e, e', htr, sub_zero]
  have hL := mean_pow_lap_eq hP p
  set L := mean (P ^ (2 * p + 1) * lap P) with hLdef
  have hq0 : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by positivity
  have hLre : L.re * ((p + 1 : ℕ) : ℝ) ^ 2 = -((2 * p + 1 : ℕ) : ℝ) * d := by
    have h := congrArg Complex.re hL
    have e3 : (((p + 1 : ℕ) : ℂ)) ^ 2 = ((((p + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    have e4 : -(((2 * p + 1 : ℕ) : ℂ)) * (d : ℂ) = ((-((2 * p + 1 : ℕ) : ℝ) * d : ℝ) : ℂ) := by
      push_cast; rfl
    rw [e3, e4, Complex.re_mul_ofReal, Complex.ofReal_re] at h
    exact h
  have hS : (mean (P ^ (2 * p + 1) * F)).re ≤ Real.sqrt n * Real.sqrt (nn2 F) :=
    (Complex.re_le_norm _).trans (norm_mean_mul_le _ _)
  rw [hsplit, Complex.add_re]
  have hQ1 : (1 : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by simp
  have h2p : ((2 * p + 1 : ℕ) : ℝ) = 2 * ((p + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  rw [h2p] at hLre
  exact law_arith hQ1 hd0 hn0 hf0 hy hLre hS hn

/-! ### Scalar comparison lemmas -/

/-- Integrated form of a differential inequality, for a function with a derivative everywhere. -/
theorem integrated_le {φ φ' h g : ℝ → ℝ} {τ t : ℝ} (hτ : τ ≤ t)
    (hd : ∀ u ∈ Icc τ t, HasDerivWithinAt φ (φ' u) (Icc τ t) u)
    (hh : ContinuousOn h (Icc τ t)) (hg : ContinuousOn g (Icc τ t))
    (hle : ∀ u ∈ Icc τ t, φ' u + h u ≤ g u) :
    φ t + (∫ u in τ..t, h u) ≤ φ τ + ∫ u in τ..t, g u := by
  set w : ℝ → ℝ := fun u => h u - g u with hw
  have hwc : ContinuousOn w (Icc τ t) := hh.sub hg
  have hwi : IntervalIntegrable w volume τ t := hwc.intervalIntegrable_of_Icc hτ
  set G : ℝ → ℝ := fun u => ∫ v in τ..u, w v with hG
  have hGc : ContinuousOn G (Icc τ t) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := τ) (b := t)
      (f := w) (by rw [uIcc_of_le hτ]; exact hwc.integrableOn_Icc)
    rwa [uIcc_of_le hτ] at this
  have hφc : ContinuousOn φ (Icc τ t) := fun u hu => (hd u hu).continuousWithinAt
  have hanti : AntitoneOn (fun u => φ u + G u) (Icc τ t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc τ t) (hφc.add hGc) ?_ ?_
    · intro u hu
      rw [interior_Icc] at hu
      have huI : u ∈ Icc τ t := Ioo_subset_Icc_self hu
      have h1 : HasDerivAt φ (φ' u) u := (hd u huI).hasDerivAt (Icc_mem_nhds hu.1 hu.2)
      have h2 : HasDerivAt G (w u) u := by
        refine intervalIntegral.integral_hasDerivAt_right
          (hwc.mono (Icc_subset_Icc_right hu.2.le) |>.intervalIntegrable_of_Icc hu.1.le)
          ((hwc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc u).filter_mono ?_)
          (hwc.continuousAt (Icc_mem_nhds hu.1 hu.2))
        rw [nhdsWithin_eq_nhds.2 (Icc_mem_nhds hu.1 hu.2)]
      exact (h1.add h2).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have huI : u ∈ Icc τ t := Ioo_subset_Icc_self hu
      have h1 : HasDerivAt φ (φ' u) u := (hd u huI).hasDerivAt (Icc_mem_nhds hu.1 hu.2)
      have h2 : HasDerivAt G (w u) u := by
        refine intervalIntegral.integral_hasDerivAt_right
          (hwc.mono (Icc_subset_Icc_right hu.2.le) |>.intervalIntegrable_of_Icc hu.1.le)
          ((hwc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc u).filter_mono ?_)
          (hwc.continuousAt (Icc_mem_nhds hu.1 hu.2))
        rw [nhdsWithin_eq_nhds.2 (Icc_mem_nhds hu.1 hu.2)]
      have h3 := (h1.add h2).deriv
      have e : deriv (fun u => φ u + G u) u = φ' u + w u := h3
      rw [e]
      have := hle u huI
      simp only [hw]
      linarith
  have hmain := hanti (left_mem_Icc.2 hτ) (right_mem_Icc.2 hτ) hτ
  have hG0 : G τ = 0 := intervalIntegral.integral_same
  simp only [hG0, add_zero] at hmain
  have e : G t = (∫ u in τ..t, h u) - ∫ u in τ..t, g u :=
    intervalIntegral.integral_sub (hh.intervalIntegrable_of_Icc hτ)
      (hg.intervalIntegrable_of_Icc hτ)
  rw [e] at hmain
  linarith

/-- Gronwall with an additive source, in the form with no exponential on the source. -/
theorem gronwall_src {φ φ' g : ℝ → ℝ} {τ t κ : ℝ} (hτ : τ ≤ t) (hκ : 0 ≤ κ)
    (hd : ∀ u ∈ Icc τ t, HasDerivWithinAt φ (φ' u) (Icc τ t) u)
    (hg : ContinuousOn g (Icc τ t)) (hg0 : ∀ u ∈ Icc τ t, 0 ≤ g u)
    (hle : ∀ u ∈ Icc τ t, φ' u ≤ κ * φ u + g u) :
    φ t ≤ Real.exp (κ * (t - τ)) * (φ τ + ∫ u in τ..t, g u) := by
  set E : ℝ → ℝ := fun u => Real.exp (-κ * (u - τ)) with hE
  have hE' : ∀ u, HasDerivAt E (-κ * E u) u := fun u => by
    have h1 : HasDerivAt (fun u => -κ * (u - τ)) (-κ) u := by
      simpa using ((hasDerivAt_id u).sub_const τ).const_mul (-κ)
    have := h1.exp
    simpa [hE, mul_comm] using this
  have hmain := integrated_le (φ := fun u => E u * φ u)
    (φ' := fun u => -κ * E u * φ u + E u * φ' u) (h := fun _ => 0) (g := g) hτ
    (fun u hu => by
      have h1 := ((hE' u).hasDerivWithinAt (s := Icc τ t)).mul (hd u hu)
      exact h1)
    continuousOn_const hg (fun u hu => by
      have hE0 : 0 < E u := Real.exp_pos _
      have hE1 : E u ≤ 1 := by
        refine Real.exp_le_one_iff.2 ?_
        nlinarith [hu.1]
      have h1 := hle u hu
      have h2 := hg0 u hu
      have h3 : E u * φ' u ≤ E u * (κ * φ u + g u) := mul_le_mul_of_nonneg_left h1 hE0.le
      have h4 : E u * g u ≤ g u := by nlinarith
      nlinarith)
  simp only [intervalIntegral.integral_zero, add_zero] at hmain
  have hEτ : E τ = 1 := by simp [hE]
  rw [hEτ, one_mul] at hmain
  have hEt : Real.exp (κ * (t - τ)) * E t = 1 := by
    simp only [hE]
    rw [← Real.exp_add]
    ring_nf
    simp
  calc φ t = Real.exp (κ * (t - τ)) * (E t * φ t) := by
        rw [← mul_assoc, hEt, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le

/-! ### Polynomial paths -/

/-- The mean as a continuous linear functional. -/
def Jc : C(T3, ℂ) →L[ℂ] ℂ :=
  J.mkContinuous 1 fun h => by
    have h1 : ‖J h‖ ≤ ∫ _, ‖h‖ ∂μT := norm_J_le continuous_const fun x =>
      ContinuousMap.norm_coe_le_norm h x
    simpa using h1

@[simp] lemma Jc_apply (h : C(T3, ℂ)) : Jc h = J h := rfl

/-- The functional `Re ∫`. -/
def reJ : C(T3, ℂ) →L[ℝ] ℝ := Complex.reCLM.comp (Jc.restrictScalars ℝ)

@[simp] lemma reJ_apply (h : C(T3, ℂ)) : reJ h = (J h).re := rfl

lemma nnC_eq (h : C(T3, ℂ)) : ∫ x, ‖h x‖ ^ 2 ∂μT = reJ (h * star h) := by
  have e : J (h * star h) = ((∫ x, ‖h x‖ ^ 2 ∂μT : ℝ) : ℂ) := by
    rw [J_apply, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [reJ_apply, e, Complex.ofReal_re]

lemma mP_eq_reJ {P : Pol} (hR : PtReal P) (q : ℕ) : mP q P = reJ (ev P ^ (2 * q)) := by
  have e : J (ev P ^ (2 * q)) = ((mP q P : ℝ) : ℂ) := by
    rw [J_apply, mP, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ContinuousMap.coe_pow, Pi.pow_apply, pow_mul]
    rw [hR.ev_sq x]
    push_cast
    rfl
  rw [reJ_apply, e, Complex.ofReal_re]

lemma continuous_nnC : Continuous fun h : C(T3, ℂ) => ∫ x, ‖h x‖ ^ 2 ∂μT := by
  simp only [nnC_eq]
  exact reJ.continuous.comp (continuous_id.mul continuous_star)

lemma continuousOn_nn2 {Q : ℝ → Pol} {S : Set ℝ} (hQ : ContinuousOn (fun t => ev (Q t)) S) :
    ContinuousOn (fun t => nn2 (Q t)) S :=
  continuous_nnC.comp_continuousOn hQ

lemma mult_polyOf (m : Mode → ℂ) (A : Finset Mode) (a : Mode → ℂ) :
    mult m (polyOf A a) = polyOf A fun k => m k * a k := by
  ext k
  simp only [coeff_mult, coeff_polyOf, tr]
  split_ifs <;> simp

lemma continuousOn_ev_polyOf {A : Finset Mode} {a : ℝ → Mode → ℂ} {S : Set ℝ}
    (h : ∀ k ∈ A, ContinuousOn (fun t => a t k) S) :
    ContinuousOn (fun t => ev (polyOf A (a t))) S := by
  simp only [ev_polyOf, tp]
  exact continuousOn_finsetSum _ fun k hk => (h k hk).smul continuousOn_const

lemma continuousOn_ev_mult {A : Finset Mode} {a : ℝ → Mode → ℂ} {S : Set ℝ}
    (h : ∀ k ∈ A, ContinuousOn (fun t => a t k) S) (m : Mode → ℂ) :
    ContinuousOn (fun t => ev (mult m (polyOf A (a t)))) S := by
  simp only [mult_polyOf]
  exact continuousOn_ev_polyOf fun k hk => continuousOn_const.mul (h k hk)

/-- The data of a polynomial path: real, slow, `C¹` coefficients on `A`, divergence-free drift. -/
structure PolyPath (a b : ℝ) (A : Finset Mode) (c c' : ℝ → Mode → ℂ)
    (U : ℝ → Fin 3 → Mode → ℂ) : Prop where
  hab : a ≤ b
  slow : ∀ k ∈ A, k 2 = 0
  real : ∀ t ∈ Icc a b, RealC (polyOf A (c t))
  deriv : ∀ k ∈ A, ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => c s k) (c' t k) (Icc a b) t
  cont' : ∀ k ∈ A, ContinuousOn (fun t => c' t k) (Icc a b)
  contU : ∀ i, ∀ k ∈ A, ContinuousOn (fun t => U t i k) (Icc a b)
  div : ∀ t ∈ Icc a b, DivFree fun i => polyOf A (U t i)

/-- The source of a polynomial path: `F = ∂_t w − Δw + U·∇w`, the *definition*. -/
def srcP (A : Finset Mode) (c c' : ℝ → Mode → ℂ) (U : ℝ → Fin 3 → Mode → ℂ) (t : ℝ) : Pol :=
  polyOf A (c' t) - lap (polyOf A (c t)) + trans (fun i => polyOf A (U t i)) (polyOf A (c t))

lemma isSlowP_polyOf {A : Finset Mode} (hA : ∀ k ∈ A, k 2 = 0) (a : Mode → ℂ) :
    IsSlowP (polyOf A a) := fun k hk => by
  rw [coeff_polyOf] at hk
  by_contra h
  refine hk ?_
  simp only [tr]
  exact ite_eq_right_iff.2 fun hk' => absurd (hA k hk') h

section Path

variable {a b : ℝ} {A : Finset Mode} {c c' : ℝ → Mode → ℂ} {U : ℝ → Fin 3 → Mode → ℂ}

namespace PolyPath

variable (h : PolyPath a b A c c' U)
include h

lemma contC {k : Mode} (hk : k ∈ A) : ContinuousOn (fun t => c t k) (Icc a b) :=
  fun t ht => (h.deriv k hk t ht).continuousWithinAt

lemma continuousOn_ev : ContinuousOn (fun t => ev (polyOf A (c t))) (Icc a b) :=
  continuousOn_ev_polyOf fun _ hk => h.contC hk

lemma continuousOn_ev_D (i : Fin 3) : ContinuousOn (fun t => ev (D i (polyOf A (c t)))) (Icc a b) :=
  continuousOn_ev_mult (fun _ hk => h.contC hk) _

lemma continuousOn_ev_src : ContinuousOn (fun t => ev (srcP A c c' U t)) (Icc a b) := by
  simp only [srcP, map_add, map_sub, trans, map_sum, map_mul]
  refine ((continuousOn_ev_polyOf h.cont').sub ?_).add ?_
  · exact continuousOn_ev_mult (fun _ hk => h.contC hk) _
  · exact continuousOn_finsetSum _ fun i _ =>
      (continuousOn_ev_polyOf (h.contU i)).mul (h.continuousOn_ev_D i)

lemma continuousOn_srcNorm : ContinuousOn (fun t => nn2 (srcP A c c' U t)) (Icc a b) :=
  continuousOn_nn2 h.continuousOn_ev_src

lemma continuousOn_mP (q : ℕ) : ContinuousOn (fun t => mP q (polyOf A (c t))) (Icc a b) := by
  simp only [mP_eq_nn2]
  refine continuousOn_nn2 ?_
  simp only [map_pow]
  exact h.continuousOn_ev.pow q

lemma continuousOn_diss (q : ℕ) :
    ContinuousOn (fun t => grad2 (polyOf A (c t) ^ q)) (Icc a b) := by
  simp only [grad2]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_nn2 ?_
  cases q with
  | zero =>
    have : ∀ t, D i (polyOf A (c t) ^ 0) = 0 := fun t => by
      ext k
      simp [D, dSym, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      intro hk
      simp [← hk]
    simp only [this, map_zero]
    exact continuousOn_const
  | succ q =>
    simp only [D_pow, map_smul, map_mul, map_pow]
    exact ((h.continuousOn_ev.pow q).mul (h.continuousOn_ev_D i)).const_smul ((q + 1 : ℕ) : ℂ)

/-- The time derivative of `m_q`. -/
theorem hasDeriv_mP {q : ℕ} {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => mP q (polyOf A (c s)))
      (2 * (q : ℝ) * (mean (polyOf A (c t) ^ (2 * q - 1) * polyOf A (c' t))).re) (Icc a b) t := by
  have hE : HasDerivWithinAt (fun s => ev (polyOf A (c s))) (ev (polyOf A (c' t))) (Icc a b) t := by
    simp only [ev_polyOf, tp]
    refine HasDerivWithinAt.fun_sum fun k hk => ?_
    exact ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℝ] ℂ)
      (mFourier k : C(T3, ℂ))).hasFDerivAt.comp_hasDerivWithinAt t (h.deriv k hk t ht))
  have hP := (hE.fun_pow (2 * q))
  have hL := reJ.hasFDerivAt.comp_hasDerivWithinAt t hP
  have e1 : ∀ s ∈ Icc a b, mP q (polyOf A (c s)) = reJ (ev (polyOf A (c s)) ^ (2 * q)) :=
    fun s hs => mP_eq_reJ (h.real s hs).ptReal q
  have e2 : reJ (((2 * q : ℕ) : C(T3, ℂ)) * ev (polyOf A (c t)) ^ (2 * q - 1) *
      ev (polyOf A (c' t))) =
      2 * (q : ℝ) * (mean (polyOf A (c t) ^ (2 * q - 1) * polyOf A (c' t))).re := by
    rw [mul_assoc, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ← map_pow, ← map_mul, reJ_apply, J_ev]
    push_cast
    rfl
  have hL' : HasDerivWithinAt (fun s => reJ (ev (polyOf A (c s)) ^ (2 * q)))
      (2 * (q : ℝ) * (mean (polyOf A (c t) ^ (2 * q - 1) * polyOf A (c' t))).re) (Icc a b) t := by
    rw [← e2]
    exact hL
  exact hL'.congr (fun s hs => e1 s hs) (e1 t ht)

/-- The law along a path. -/
theorem energy_ineq {q : ℕ} (hq : 1 ≤ q) {t y : ℝ} (ht : t ∈ Icc a b) (hy : 0 < y)
    (hm : mP q (polyOf A (c t)) ≤ y ^ q) :
    2 * (q : ℝ) * (mean (polyOf A (c t) ^ (2 * q - 1) * polyOf A (c' t))).re +
        grad2 (polyOf A (c t) ^ q) ≤
      y ^ q + 201 * (q : ℝ) ^ 2 * nn2 (srcP A c c' U t) * y ^ (q - 1) :=
  law_ineq (h.real t ht) (isSlowP_polyOf h.slow _) (h.div t ht) (by simp [srcP]) hq hy hm

/-- The differential inequality of `(m_q + ε)^{1/q}`. -/
private theorem deriv_root_le {q : ℕ} (hq : 1 ≤ q) {u ε : ℝ} (huI : u ∈ Icc a b) (hε0 : 0 < ε) :
    2 * (q : ℝ) * (mean (polyOf A (c u) ^ (2 * q - 1) * polyOf A (c' u))).re * (q : ℝ)⁻¹ *
        (mP q (polyOf A (c u)) + ε) ^ ((q : ℝ)⁻¹ - 1) ≤
      (q : ℝ)⁻¹ * (mP q (polyOf A (c u)) + ε) ^ (q : ℝ)⁻¹ +
        201 * q * nn2 (srcP A c c' U u) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqne : q ≠ 0 := by omega
  set M : ℝ := mP q (polyOf A (c u)) + ε with hM
  have hM0 : 0 < M := add_pos_of_nonneg_of_pos (mP_nonneg _ _) hε0
  set r : ℝ := (q : ℝ)⁻¹ with hr
  set m' : ℝ := 2 * (q : ℝ) * (mean (polyOf A (c u) ^ (2 * q - 1) * polyOf A (c' u))).re with hm'
  set y : ℝ := M ^ r with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hM0 _
  have hyq : y ^ q = M := Real.rpow_inv_natCast_pow hM0.le hqne
  have hmle : mP q (polyOf A (c u)) ≤ y ^ q := by
    rw [hyq]
    simp only [hM]
    linarith
  have hlaw := h.energy_ineq hq huI hy0 hmle
  have hd0 := grad2_nonneg (polyOf A (c u) ^ q)
  have hm1 : m' ≤ y ^ q + 201 * (q : ℝ) ^ 2 * nn2 (srcP A c c' U u) * y ^ (q - 1) := by
    simp only [hm']
    linarith
  have hp : M ^ (r - 1) = y / y ^ q := by
    rw [Real.rpow_sub_one hM0.ne', hyq]
  have hyq' : y ^ q = y * y ^ (q - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hq]
  have hy1 : 0 < y ^ (q - 1) := by positivity
  rw [hp]
  have hr0 : 0 < r := by positivity
  have hmul : r * (y / y ^ q) = r / y ^ (q - 1) := by
    rw [hyq']
    field_simp
  calc m' * r * (y / y ^ q) = m' * (r / y ^ (q - 1)) := by rw [mul_assoc, hmul]
    _ ≤ (y ^ q + 201 * (q : ℝ) ^ 2 * nn2 (srcP A c c' U u) * y ^ (q - 1)) *
          (r / y ^ (q - 1)) := mul_le_mul_of_nonneg_right hm1 (by positivity)
    _ = r * y + 201 * q * nn2 (srcP A c c' U u) := by
        rw [hyq']
        simp only [hr]
        field_simp

/-- **Propagation of `L^{2q}`**, additive in the source:
`‖w(t)‖²_{2q} ≤ e^{(t−τ)/q} (2Y + 201 q ∫ ‖F‖₂²)` if `‖w(τ)‖²_{2q} ≤ Y`.  The factor `2` avoids a
limit in the regularization of `m^{1/q}` at `m = 0`. -/
theorem propagate {q : ℕ} (hq : 1 ≤ q) {τ t Y : ℝ} (hτa : a ≤ τ) (hτt : τ ≤ t) (ht : t ≤ b)
    (hY : 0 < Y) (hm : mP q (polyOf A (c τ)) ≤ Y ^ q) :
    mP q (polyOf A (c t)) ≤ (Real.exp ((t - τ) / q) *
      (2 * Y + 201 * q * ∫ u in τ..t, nn2 (srcP A c c' U u))) ^ q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqne : q ≠ 0 := by omega
  have hsub : Icc τ t ⊆ Icc a b := Icc_subset_Icc hτa ht
  have h2 : (2 : ℝ) ≤ 2 ^ q := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  set ε : ℝ := (2 ^ q - 1) * Y ^ q with hε
  have hε0 : 0 < ε := mul_pos (by linarith) (by positivity)
  set M : ℝ → ℝ := fun u => mP q (polyOf A (c u)) + ε with hM
  have hM0 : ∀ u, 0 < M u := fun u => add_pos_of_nonneg_of_pos (mP_nonneg _ _) hε0
  set r : ℝ := (q : ℝ)⁻¹ with hr
  set φ : ℝ → ℝ := fun u => M u ^ r with hφ
  set m' : ℝ → ℝ := fun u =>
    2 * (q : ℝ) * (mean (polyOf A (c u) ^ (2 * q - 1) * polyOf A (c' u))).re with hm'
  have hφ0 : ∀ u, 0 < φ u := fun u => Real.rpow_pos_of_pos (hM0 u) _
  have hφq : ∀ u, φ u ^ q = M u := fun u => Real.rpow_inv_natCast_pow (hM0 u).le hqne
  have hd : ∀ u ∈ Icc τ t, HasDerivWithinAt φ (m' u * r * M u ^ (r - 1)) (Icc τ t) u :=
      fun u hu => by
    have h1 := ((h.hasDeriv_mP (q := q) (hsub hu)).add_const ε).mono hsub
    exact h1.rpow_const (Or.inl (hM0 u).ne')
  have hg : ContinuousOn (fun u => 201 * (q : ℝ) * nn2 (srcP A c c' U u)) (Icc τ t) :=
    (h.continuousOn_srcNorm.mono hsub).const_mul _
  have hkey := gronwall_src (κ := r) (φ' := fun u => m' u * r * M u ^ (r - 1)) hτt
    (by positivity) hd hg (fun _ _ => mul_nonneg (by positivity) (nn2_nonneg _)) ?_
  · have e1 : ∫ u in τ..t, 201 * (q : ℝ) * nn2 (srcP A c c' U u) =
        201 * q * ∫ u in τ..t, nn2 (srcP A c c' U u) := intervalIntegral.integral_const_mul _ _
    rw [e1] at hkey
    have hτ2 : φ τ ≤ 2 * Y := by
      have h3 : M τ ≤ (2 * Y) ^ q := by
        simp only [hM, hε, mul_pow]
        linarith
      calc φ τ ≤ ((2 * Y) ^ q) ^ r := Real.rpow_le_rpow (hM0 τ).le h3 (by positivity)
        _ = 2 * Y := Real.pow_rpow_inv_natCast (by positivity) hqne
    have hint0 : 0 ≤ ∫ u in τ..t, nn2 (srcP A c c' U u) :=
      intervalIntegral.integral_nonneg hτt fun _ _ => nn2_nonneg _
    have e2 : r * (t - τ) = (t - τ) / q := by
      simp only [hr]
      field_simp
    rw [e2] at hkey
    have h4 : φ t ≤ Real.exp ((t - τ) / q) *
        (2 * Y + 201 * q * ∫ u in τ..t, nn2 (srcP A c c' U u)) :=
      hkey.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)
    calc mP q (polyOf A (c t)) ≤ M t := by simp only [hM]; linarith
      _ = φ t ^ q := (hφq t).symm
      _ ≤ _ := pow_le_pow_left₀ (hφ0 t).le h4 q
  · intro u hu
    exact h.deriv_root_le hq (hsub hu) hε0

/-- The integrated dissipation at level `q`. -/
theorem diss_le {q : ℕ} (hq : 1 ≤ q) {τ t y : ℝ} (hτa : a ≤ τ) (hτt : τ ≤ t) (ht : t ≤ b)
    (hy : 0 < y) (hm : ∀ u ∈ Icc τ t, mP q (polyOf A (c u)) ≤ y ^ q) :
    ∫ u in τ..t, grad2 (polyOf A (c u) ^ q) ≤ mP q (polyOf A (c τ)) + (t - τ) * y ^ q +
      201 * (q : ℝ) ^ 2 * (∫ u in τ..t, nn2 (srcP A c c' U u)) * y ^ (q - 1) := by
  have hsub : Icc τ t ⊆ Icc a b := Icc_subset_Icc hτa ht
  have hf := (h.continuousOn_srcNorm.mono hsub)
  have hg : ContinuousOn (fun u => y ^ q + 201 * (q : ℝ) ^ 2 * nn2 (srcP A c c' U u) * y ^ (q - 1))
      (Icc τ t) := continuousOn_const.add ((hf.const_mul _).mul continuousOn_const)
  have hkey := integrated_le
    (φ' := fun u => 2 * (q : ℝ) * (mean (polyOf A (c u) ^ (2 * q - 1) * polyOf A (c' u))).re) hτt
    (fun u hu => (h.hasDeriv_mP (hsub hu)).mono hsub) ((h.continuousOn_diss q).mono hsub) hg
    fun u hu => h.energy_ineq hq (hsub hu) hy (hm u hu)
  have e : ∫ u in τ..t, (y ^ q + 201 * (q : ℝ) ^ 2 * nn2 (srcP A c c' U u) * y ^ (q - 1)) =
      (t - τ) * y ^ q + 201 * (q : ℝ) ^ 2 * (∫ u in τ..t, nn2 (srcP A c c' U u)) * y ^ (q - 1) := by
    have hi : IntervalIntegrable
        (fun u => 201 * (q : ℝ) ^ 2 * nn2 (srcP A c c' U u) * y ^ (q - 1)) volume τ t :=
      ((hf.const_mul _).mul continuousOn_const).intervalIntegrable_of_Icc hτt
    rw [intervalIntegral.integral_add intervalIntegrable_const hi,
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [e] at hkey
  have h0 := mP_nonneg q (polyOf A (c t))
  linarith

end PolyPath

/-- The Moser constants: `piM T (n + 1) = e^T 2¹⁸ 8ⁿ piM T n`. -/
def piM (T : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => Real.exp T * 2 ^ 18 * 8 ^ n * piM T n

lemma one_le_piM {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : 1 ≤ piM T n := by
  induction n with
  | zero => simp [piM]
  | succ n ih =>
    simp only [piM]
    have h1 : 1 ≤ Real.exp T := Real.one_le_exp hT
    have h2 : (1 : ℝ) ≤ 8 ^ n := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ Real.exp T * 2 ^ 18 := by nlinarith
    have h4 : (1 : ℝ) ≤ Real.exp T * 2 ^ 18 * 8 ^ n := by nlinarith
    nlinarith

lemma moser_arith {q Y I : ℝ} (hq : 1 ≤ q) (hY : 0 < Y) (hI : I ≤ Y) (hI0 : 0 ≤ I) :
    2 * (2 * q * (200 * (3 + 201 * q ^ 2)) * Y) + 201 * (2 * q) * I ≤ 2 ^ 18 * q ^ 3 * Y := by
  have h1 : q ≤ q ^ 3 := by
    calc q = q ^ 1 := (pow_one _).symm
      _ ≤ q ^ 3 := pow_le_pow_right₀ hq (by norm_num)
  have h2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
  have h3 : q * (3 + 201 * q ^ 2) ≤ 204 * q ^ 3 := by nlinarith
  have h4 : q * I ≤ q ^ 3 * Y := mul_le_mul h1 hI hI0 (by positivity)
  have h5 : q * (3 + 201 * q ^ 2) * Y ≤ 204 * q ^ 3 * Y := mul_le_mul_of_nonneg_right h3 hY.le
  have h6 : 0 ≤ q ^ 3 * Y := by positivity
  have e : 2 * (2 * q * (200 * (3 + 201 * q ^ 2)) * Y) + 201 * (2 * q) * I =
      800 * (q * (3 + 201 * q ^ 2) * Y) + 402 * (q * I) := by ring
  rw [e]
  have e2 : 204 * q ^ 3 * Y = 204 * (q ^ 3 * Y) := by ring
  have e3 : (2 : ℝ) ^ 18 * q ^ 3 * Y = 262144 * (q ^ 3 * Y) := by ring
  rw [e3]
  linarith

/-- The integral of `m_{2q}` on a window of length at most one, from the dissipation and
Ladyzhenskaya. -/
theorem PolyPath.integral_double_le (h : PolyPath a b A c c' U) {q : ℕ} (hq1 : 1 ≤ q) {α δ Y : ℝ}
    (hα : a ≤ α) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hb : α + δ ≤ b) (hY : 0 < Y)
    (hm : ∀ u ∈ Icc α (α + δ), mP q (polyOf A (c u)) ≤ Y ^ q)
    (hF : (∫ u in α..(α + δ), nn2 (srcP A c c' U u)) ≤ Y) :
    ∫ u in α..(α + δ), mP (2 * q) (polyOf A (c u)) ≤
      200 * (3 + 201 * (q : ℝ) ^ 2) * Y ^ q * Y ^ q := by
  have hle : α ≤ α + δ := by linarith
  have hsub : Icc α (α + δ) ⊆ Icc a b := Icc_subset_Icc hα hb
  have hdiss := h.diss_le hq1 hα hle hb hY hm
  set Id := ∫ u in α..(α + δ), grad2 (polyOf A (c u) ^ q) with hId
  set Iq := ∫ u in α..(α + δ), nn2 (srcP A c c' U u) with hIq
  have hq' : Y ^ q = Y * Y ^ (q - 1) := by rw [← pow_succ', Nat.sub_add_cancel hq1]
  have hY0' : 0 < Y ^ (q - 1) := by positivity
  have hYq0 : 0 < Y ^ q := by positivity
  have hIdle : Id ≤ (2 + 201 * (q : ℝ) ^ 2) * Y ^ q := by
    have h3 : mP q (polyOf A (c α)) ≤ Y ^ q := hm α (left_mem_Icc.2 hle)
    have h4 : (α + δ - α) * Y ^ q ≤ Y ^ q := by
      have : α + δ - α = δ := by ring
      rw [this]
      nlinarith
    have h5 : 201 * (q : ℝ) ^ 2 * Iq * Y ^ (q - 1) ≤ 201 * (q : ℝ) ^ 2 * Y ^ q := by
      rw [hq']
      have : Iq * Y ^ (q - 1) ≤ Y * Y ^ (q - 1) := mul_le_mul_of_nonneg_right hF hY0'.le
      have h6 : (0 : ℝ) ≤ 201 * (q : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  have hc2 : ContinuousOn (fun u => mP (2 * q) (polyOf A (c u))) (Icc α (α + δ)) :=
    (h.continuousOn_mP _).mono hsub
  have hdc : ContinuousOn (fun u => grad2 (polyOf A (c u) ^ q)) (Icc α (α + δ)) :=
    (h.continuousOn_diss q).mono hsub
  have hrhs : IntervalIntegrable
      (fun u => 200 * Y ^ q * (Y ^ q + grad2 (polyOf A (c u) ^ q))) volume α (α + δ) :=
    ((continuousOn_const.add hdc).const_mul _).intervalIntegrable_of_Icc hle
  have h3 := intervalIntegral.integral_mono_on hle (hc2.intervalIntegrable_of_Icc hle)
    hrhs fun u hu => by
      have h4 := mP_double_le (isSlowP_polyOf h.slow (c u)) q
      have h5 := hm u hu
      have h6 := mP_nonneg q (polyOf A (c u))
      have h7 := grad2_nonneg (polyOf A (c u) ^ q)
      calc mP (2 * q) (polyOf A (c u)) ≤ 200 * mP q (polyOf A (c u)) *
            (mP q (polyOf A (c u)) + grad2 (polyOf A (c u) ^ q)) := h4
        _ ≤ 200 * Y ^ q * (Y ^ q + grad2 (polyOf A (c u) ^ q)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h5 (by norm_num))
              (add_le_add h5 le_rfl) (by positivity) (by positivity)
  have e : ∫ u in α..(α + δ), 200 * Y ^ q * (Y ^ q + grad2 (polyOf A (c u) ^ q)) =
      200 * Y ^ q * (δ * Y ^ q + Id) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      intervalIntegrable_const (hdc.intervalIntegrable_of_Icc hle),
      intervalIntegral.integral_const, smul_eq_mul]
    congr 2
    ring
  rw [e] at h3
  refine h3.trans ?_
  have h8 : δ * Y ^ q ≤ Y ^ q := by nlinarith
  have h9 : 200 * Y ^ q * (δ * Y ^ q + Id) ≤ 200 * Y ^ q * ((3 + 201 * (q : ℝ) ^ 2) * Y ^ q) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  calc _ ≤ _ := h9
    _ = _ := by ring

/-- A good time at level `2q`, in a window of length `1/(2q)`. -/
theorem PolyPath.good_time (h : PolyPath a b A c c' U) {q : ℕ} (hq1 : 1 ≤ q) {α δ Y : ℝ}
    (hα : a ≤ α) (hδ0 : 0 < δ) (hδe : δ * (2 * q) = 1) (hb : α + δ ≤ b) (hY : 0 < Y)
    (hm : ∀ u ∈ Icc α (α + δ), mP q (polyOf A (c u)) ≤ Y ^ q)
    (hF : (∫ u in α..(α + δ), nn2 (srcP A c c' U u)) ≤ Y) :
    ∃ τ ∈ Icc α (α + δ), mP (2 * q) (polyOf A (c τ)) ≤
      (2 * q * (200 * (3 + 201 * (q : ℝ) ^ 2)) * Y) ^ (2 * q) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hδ1 : δ ≤ 1 := by nlinarith
  have hI := h.integral_double_le hq1 hα hδ0.le hδ1 hb hY hm hF
  have hc2 : ContinuousOn (fun u => mP (2 * q) (polyOf A (c u))) (Icc α (α + δ)) :=
    (h.continuousOn_mP _).mono (Icc_subset_Icc hα hb)
  obtain ⟨τ, hτ, hgood⟩ := exists_le_average (by linarith : α < α + δ) hc2
  have e0 : α + δ - α = δ := by ring
  rw [e0] at hgood
  refine ⟨τ, hτ, ?_⟩
  set Λ : ℝ := 2 * q * (200 * (3 + 201 * (q : ℝ) ^ 2)) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    have : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hqR
    simp only [hΛ]
    nlinarith
  have h3 : mP (2 * q) (polyOf A (c τ)) ≤ Λ * Y ^ q * Y ^ q := by
    have h4 : mP (2 * q) (polyOf A (c τ)) = mP (2 * q) (polyOf A (c τ)) * δ * (2 * q) := by
      rw [mul_assoc, hδe, mul_one]
    rw [h4]
    calc _ ≤ 200 * (3 + 201 * (q : ℝ) ^ 2) * Y ^ q * Y ^ q * (2 * q) :=
          mul_le_mul_of_nonneg_right (hgood.trans hI) (by positivity)
      _ = _ := by simp only [hΛ]; ring
  refine h3.trans ?_
  have e1 : Y ^ q * Y ^ q = Y ^ (2 * q) := by rw [two_mul, pow_add]
  have h5 : Λ ≤ Λ ^ (2 * q) := by
    calc Λ = Λ ^ 1 := (pow_one _).symm
      _ ≤ Λ ^ (2 * q) := pow_le_pow_right₀ hΛ1 (by omega)
  have e3 : (Λ * Y) ^ (2 * q) = Λ ^ (2 * q) * Y ^ (2 * q) := mul_pow _ _ _
  rw [mul_assoc, e1, e3]
  exact mul_le_mul_of_nonneg_right h5 (by positivity)

/-- From a good time to the later times. -/
theorem PolyPath.of_good_time (h : PolyPath a b A c c' U) {q : ℕ} (hq1 : 1 ≤ q) {T Y τ t : ℝ}
    (hT : b - a ≤ T) (hY : 0 < Y) (hτ : a ≤ τ) (hτt : τ ≤ t) (ht : t ≤ b)
    (hF : (∫ u in τ..t, nn2 (srcP A c c' U u)) ≤ Y)
    (hm : mP (2 * q) (polyOf A (c τ)) ≤
      (2 * q * (200 * (3 + 201 * (q : ℝ) ^ 2)) * Y) ^ (2 * q)) :
    mP (2 * q) (polyOf A (c t)) ≤
      (Real.exp T * (2 ^ 18 * (q : ℝ) ^ 3 * Y)) ^ (2 * q) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hbound := h.propagate (q := 2 * q) (by omega) hτ hτt ht
    (by positivity : 0 < 2 * q * (200 * (3 + 201 * (q : ℝ) ^ 2)) * Y) hm
  have hint0 : 0 ≤ ∫ u in τ..t, nn2 (srcP A c c' U u) :=
    intervalIntegral.integral_nonneg hτt fun _ _ => nn2_nonneg _
  refine hbound.trans (pow_le_pow_left₀ ?_ ?_ _)
  · positivity
  · have hexp : Real.exp ((t - τ) / ((2 * q : ℕ) : ℝ)) ≤ Real.exp T := by
      refine Real.exp_le_exp.2 ?_
      have h3 : t - τ ≤ T := by linarith
      have h4 : 0 ≤ t - τ := by linarith
      have h5 : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by
        push_cast
        linarith
      exact (div_le_self h4 h5).trans h3
    have hsum : 2 * (2 * q * (200 * (3 + 201 * (q : ℝ) ^ 2)) * Y) + 201 * ((2 * q : ℕ) : ℝ) *
        (∫ u in τ..t, nn2 (srcP A c c' U u)) ≤ 2 ^ 18 * (q : ℝ) ^ 3 * Y := by
      push_cast
      exact moser_arith hqR hY hF hint0
    exact mul_le_mul hexp hsum (by positivity) (Real.exp_pos _).le

/-- **Moser iteration in time, on polynomial paths**, uniform in the drift and in `A`: for
`t ≥ a + 1` (`a_n = a + 1 − 2⁻ⁿ`), `‖w(t)‖²_{2·2ⁿ} ≤ piM T n · Y`, if `‖w‖₂² ≤ Y` on `[a, b]`,
`∫ ‖F‖₂² ≤ Y`, `b − a ≤ T`.  At each level: the dissipation and Ladyzhenskaya bound `∫ m_{2q}`,
on a window of length `2^{−n−1}`, a good time carries `m_{2q}`, and `propagate` extends it. -/
theorem PolyPath.moser (h : PolyPath a b A c c' U) {T Y : ℝ} (hT : b - a ≤ T) (hT0 : 0 ≤ T)
    (hY : 0 < Y) (h1 : ∀ t ∈ Icc a b, mP 1 (polyOf A (c t)) ≤ Y)
    (hF : (∫ u in a..b, nn2 (srcP A c c' U u)) ≤ Y) (n : ℕ) :
    ∀ t ∈ Icc (a + 1 - 1 / 2 ^ n) b, mP (2 ^ n) (polyOf A (c t)) ≤ (piM T n * Y) ^ (2 ^ n) := by
  have hfi : IntervalIntegrable (fun u => nn2 (srcP A c c' U u)) volume a b :=
    h.continuousOn_srcNorm.intervalIntegrable_of_Icc h.hab
  have hfmono : ∀ {u v : ℝ}, a ≤ u → u ≤ v → v ≤ b →
      (∫ w in u..v, nn2 (srcP A c c' U w)) ≤ Y := fun hu huv hv =>
    (intervalIntegral.integral_mono_interval hu huv hv
      (Eventually.of_forall fun _ => nn2_nonneg _) hfi).trans hF
  induction n with
  | zero =>
    intro t ht
    have ht' : t ∈ Icc a b := ⟨by simpa using ht.1, ht.2⟩
    simpa [piM] using h1 t ht'
  | succ n ih =>
    intro t ht
    set q : ℕ := 2 ^ n with hq
    have hq1 : 1 ≤ q := Nat.one_le_two_pow
    set Yn : ℝ := piM T n * Y with hYn
    have hPi := one_le_piM hT0 n
    have hYn0 : 0 < Yn := by positivity
    have hYle : Y ≤ Yn := by nlinarith
    set an : ℝ := a + 1 - 1 / 2 ^ n with han
    set δ : ℝ := 1 / 2 ^ (n + 1) with hδ
    have hδ0 : 0 < δ := by positivity
    have hδe : δ * (2 * q) = 1 := by
      simp only [hδ, hq]
      push_cast
      field_simp
      ring
    have hanδ : a + 1 - 1 / 2 ^ (n + 1) = an + δ := by
      simp only [han, hδ, pow_succ]
      field_simp
      ring
    rw [hanδ] at ht
    have h2n : (1 : ℝ) / 2 ^ n ≤ 1 := by
      have : (2 : ℝ) ^ n ≥ 1 := one_le_pow₀ (by norm_num)
      rw [div_le_one (by positivity)]
      exact this
    have haan : a ≤ an := by simp only [han]; linarith
    have hanle : an ≤ an + δ := by linarith
    have han1b : an + δ ≤ b := ht.1.trans ht.2
    have hmY : ∀ u ∈ Icc an (an + δ), mP q (polyOf A (c u)) ≤ Yn ^ q := fun u hu =>
      ih u (Icc_subset_Icc_right han1b hu)
    obtain ⟨τ, hτ, hmτ⟩ := h.good_time hq1 haan hδ0 hδe han1b hYn0 hmY
      ((hfmono haan hanle han1b).trans hYle)
    have hτab : a ≤ τ := haan.trans hτ.1
    have hτt : τ ≤ t := hτ.2.trans ht.1
    have hgood := h.of_good_time hq1 hT hYn0 hτab hτt ht.2
      ((hfmono hτab hτt ht.2).trans hYle) hmτ
    have e2 : 2 ^ (n + 1) = 2 * q := by rw [hq, pow_succ']
    have h8 : (8 : ℝ) ^ n = (q : ℝ) ^ 3 := by
      simp only [hq]
      push_cast
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have e3 : piM T (n + 1) * Y = Real.exp T * (2 ^ 18 * (q : ℝ) ^ 3 * Yn) := by
      simp only [piM, hYn, h8]
      ring
    rw [e2, e3]
    exact hgood

/-- **Smoothing at `p = 4`**, drift-uniform: the first step of `moser`.  From the energy on
`[a, b]`, with any divergence-free drift, `‖w(t)‖₄² ≤ e^T 2¹⁸ Y` after the time `a + 1/2`.  This is
Step J2's first target on polynomial paths; `Slow.vert_moser_box` is its form for the box
truncation of the vertical velocity, at every `n`. -/
theorem PolyPath.smoothing_four (h : PolyPath a b A c c' U) {T Y : ℝ} (hT : b - a ≤ T)
    (hT0 : 0 ≤ T) (hY : 0 < Y) (h1 : ∀ t ∈ Icc a b, mP 1 (polyOf A (c t)) ≤ Y)
    (hF : (∫ u in a..b, nn2 (srcP A c c' U u)) ≤ Y) :
    ∀ t ∈ Icc (a + 1 / 2) b, mP 2 (polyOf A (c t)) ≤ (Real.exp T * 2 ^ 18 * Y) ^ 2 := by
  intro t ht
  have h2 := h.moser hT hT0 hY h1 hF 1 t ⟨by
    have := ht.1
    norm_num at this ⊢
    linarith, ht.2⟩
  simpa [piM] using h2

end Path

end OVNS.Quant.Slow
