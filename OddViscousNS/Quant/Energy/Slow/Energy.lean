import OddViscousNS.Quant.Energy.Slow.Equation
import OddViscousNS.Gronwall

/-!
# E7-F, the slow energy laws: `L²`, horizontal enstrophy, vertical `H¹` (F0–F2)

Route `t12_slow_fourier_route.md` §2.2, steps F0–F2, along the corrected slow field
`y_S = S + R_S` (`corrSlow`, `Equation.lean`), with `h = Π_H y_S`, `ζ = Π_V y_S` and the
pointwise residual size `Φ ≥ ‖corrRes‖₀` on the piece (`Φ = φ + 1` once the slow-correction
roles are paid, `hnorm_corrRes_le`):

* F0 `corr_l2_law`: `‖y_S(t)‖₀² + ∫ ‖y_S‖₁² ≤ ‖y_S(s)‖₀² + Φ²(t−s)` — the transport
  cancellation `⟨B(y_S,y_S), y_S⟩ = 0` (`pair_slow_cyc`), the residual by Young;
  `corr_l2_bounds`: exponential contraction of `‖y_S‖₀²` to the level `Φ²` and the dissipation
  budget `∫ ‖y_S‖₁² ≤ ‖y_S(s)‖₀² + Φ²(t−s)` (this is the `∫ a_ζ² ≲ μ²` of F2).
* F1 `corr_horiz_law`, `corr_horiz_bounds`: the same for the horizontal enstrophy `a_h²` with
  dissipation `∫ b_h²` (2D enstrophy conservation `pair_slow_horizontal`).
* F2 `corr_vert_law`: `(a_ζ²)' + ½ b_ζ² ≤ 25 a_h² a_ζ² + 2Φ²` (T3a `pair_slow_vertical_lady`,
  `c_L = 5`); `corr_vert_bounds`: **window averaging, no exponential Gronwall** —
  `a_ζ(u)² ≤ a_ζ(τ)² + 25 A_h² ∫ a_ζ² + 2Φ²(t−s)` from any `τ ≤ u`, with `τ` a time of the first
  unit window where `a_ζ² ≤ ∫ a_ζ² ≤ I` (`exists_le_average`), hence `a_ζ² ≲ (1 + A_h²) I`
  on `[s+1, t]` and `∫ b_ζ² ≤ 2(a_ζ(s)² + 25 A_h² I + 2Φ²(t−s))`.

Scalar tools: `exists_le_average` (a continuous function takes a value at most its mean) and
the library's `gronwall_decay`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace OVNS

/-! ### Scalar lemmas -/

/-- A continuous function on `[a, b]`, `a < b`, takes a value at most its average. -/
theorem exists_le_average {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b)) :
    ∃ τ ∈ Icc a b, f τ * (b - a) ≤ ∫ u in a..b, f u := by
  obtain ⟨τ, hτ, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab.le) hf
  refine ⟨τ, hτ, ?_⟩
  have h1 : ∫ _ in a..b, f τ ≤ ∫ u in a..b, f u :=
    intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
      (hf.intervalIntegrable_of_Icc hab.le) fun u hu => hmin hu
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  linarith

namespace Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### Regularity of the residual and the pairing splitting -/

/-- `corrRes ∈ H⁰` along the solution. -/
theorem corrRes_inH0 (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) : InH 0 (corrRes r g y u) := by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  have hR := slowCorr_adm h hr hu huT
  have hz := corrSlow_adm h hr hu huT
  have hF : Adm 2 (PiF (actual r g y u)) := hx.PiF
  -- `A R_S ∈ H⁰`
  have hAR : InH 0 (fun k => (absSq k : ℂ) • slowCorr r g y u k) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg 0 k) (sq_nonneg _))
      (fun k => ?_) hR.inH
    by_cases hk : k = 0
    · simp [hk, sobWeight]
    · have h0 : sobWeight 0 k = 1 := by simp [sobWeight, hk]
      rw [h0, one_mul, norm_smul, mul_pow, sobWeight_two, Complex.norm_real,
        Real.norm_of_nonneg (absSq_nonneg k)]
  -- the pieces of `slowRes`
  have hg0 : InH 0 (PiS g) := (h.force_adm.inH.mono (by norm_num)).PiS
  have hH : InH 0 (PiS (Hpsi r g y u)) := by
    have h1 := (hnorm_Qm_zero_le (phaseM_bdd (r * u)) hy.mz hy.mz).1
    have h2 := (hnorm_Qm_zero_le (phaseM_bdd (r * u)) hx.mz hx.mz).1
    exact (h1.sub h2).PiS
  have hN : InH 0 ((2 : ℂ) • kinN r (r * u) (fastRHS r g y u) (PiF (actual r g y u))) := by
    rw [kinN_comm]
    exact ((hnorm_kinN_le hr (summable_wiener hF.inH) (fastRHS_l2 h hu huT).1).1).smul _
  have hone : Mult.Bdd (fun _ _ _ _ _ => (1 : ℂ)) := fun _ _ _ _ _ => by simp
  have hBz : InH 0 (Bsym (corrSlow r g y u) (corrSlow r g y u)) := by
    rw [← Qm_one hz hz]
    exact (hnorm_Qm_zero_le hone hz.mz hz.mz).1
  have hBS : InH 0 (Bsym (PiS (actual r g y u)) (PiS (actual r g y u))) := by
    rw [← Qm_one hx.PiS hx.PiS]
    exact (hnorm_Qm_zero_le hone hx.PiS.mz hx.PiS.mz).1
  have hres : InH 0 (slowRes r g y u) := ((hg0.sub hH).add hN).add (hBz.sub hBS)
  exact hAR.add hres

/-- `B(y_S, y_S) ∈ H⁰` along the solution. -/
theorem Bsym_corrSlow_inH0 (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) : InH 0 (Bsym (corrSlow r g y u) (corrSlow r g y u)) := by
  have hz := corrSlow_adm h hr hu huT
  have hone : Mult.Bdd (fun _ _ _ _ _ => (1 : ℂ)) := fun _ _ _ _ _ => by simp
  rw [← Qm_one hz hz]
  exact (hnorm_Qm_zero_le hone hz.mz hz.mz).1

/-- `⟨Z, Λ^{2σ} corrForce⟩ = ⟨Z, Λ^{2σ} corrRes⟩ − ⟨Z, Λ^{2σ} B(y_S,y_S)⟩` for `σ ≤ 1`. -/
theorem pair_corrForce (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) {σ : ℝ} (hσ : σ ≤ 1) {Z : Field} (hZ : InH (σ + 1) Z) :
    pair σ Z (corrForce r g y u) =
      pair σ Z (corrRes r g y u) - pair σ Z (Bsym (corrSlow r g y u) (corrSlow r g y u)) := by
  have h1 : InH (σ - 1) (corrRes r g y u) := (corrRes_inH0 h hr hu huT).mono (by linarith)
  have h2 : InH (σ - 1) (Bsym (corrSlow r g y u) (corrSlow r g y u)) :=
    (Bsym_corrSlow_inH0 h hr hu huT).mono (by linarith)
  exact pair_sub hZ h1 h2

/-! ### Continuity of the norms along the corrected field -/

theorem continuousOn_corr_sq (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {σ b : ℝ}
    (hσ : σ = 0 ∨ σ = 1 ∨ σ = 2) (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    ContinuousOn (fun u => hnorm σ (corrSlow r g y u) ^ 2) (Icc 0 b) :=
  (heatPair_corrSlow h hr hσ hb hbT).continuousOn_hnorm_sq hb

theorem continuousOn_corrH_sq (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {σ b : ℝ}
    (hσ : σ = 0 ∨ σ = 1 ∨ σ = 2) (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    ContinuousOn (fun u => hnorm σ (PiH (corrSlow r g y u)) ^ 2) (Icc 0 b) :=
  (heatPair_corrH h hr hσ hb hbT).continuousOn_hnorm_sq hb

theorem continuousOn_corrV_sq (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {σ b : ℝ}
    (hσ : σ = 0 ∨ σ = 1 ∨ σ = 2) (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    ContinuousOn (fun u => hnorm σ (PiV (corrSlow r g y u)) ^ 2) (Icc 0 b) :=
  (heatPair_corrV h hr hσ hb hbT).continuousOn_hnorm_sq hb

/-- `t ↦ hnorm σ (·)` is continuous when its square is (`Real.sqrt` of the square). -/
lemma continuousOn_of_sq {f : ℝ → ℝ} {S : Set ℝ} (hf0 : ∀ u, 0 ≤ f u)
    (hf : ContinuousOn (fun u => f u ^ 2) S) : ContinuousOn f S := by
  have : f = fun u => Real.sqrt (f u ^ 2) := by
    funext u; rw [Real.sqrt_sq (hf0 u)]
  rw [this]
  exact hf.sqrt

/-! ### F0: the slow `L²` law -/

/-- **F0** (route §2.2): `‖y_S(t)‖₀² + ∫ₛᵗ ‖y_S‖₁² ≤ ‖y_S(s)‖₀² + Φ²(t − s)` whenever
`‖corrRes‖₀ ≤ Φ` on `[s, t]`. -/
theorem corr_l2_law (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {Φ : ℝ}
    (hres : ∀ u ∈ Icc s t, hnorm 0 (corrRes r g y u) ≤ Φ) :
    hnorm 0 (corrSlow r g y t) ^ 2 + ∫ u in s..t, hnorm 1 (corrSlow r g y u) ^ 2 ≤
      hnorm 0 (corrSlow r g y s) ^ 2 + Φ ^ 2 * (t - s) := by
  have hp : HeatPair 0 s t (corrSlow r g y) (corrForce r g y) :=
    (heatPair_corrSlow h hr (Or.inl rfl) (hs.trans hst) ht).mono hs le_rfl
  have key := hp.energy_le (τ := 1) (θ := 1) (R := fun _ => Φ ^ 2) (by norm_num) hst
    intervalIntegrable_const ?_
  · rw [intervalIntegral.integral_const, smul_eq_mul] at key
    linarith
  refine ae_restrict_of_forall_mem measurableSet_Icc fun u hu => ?_
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hz := corrSlow_adm h hr hu0 huT
  have hz1 : InH ((0 : ℝ) + 1) (corrSlow r g y u) := by
    rw [zero_add]; exact hz.inH.mono (by norm_num)
  rw [pair_corrForce h hr hu0 huT (by norm_num) hz1,
    pair_slow_cyc hz hz (fun _ _ => rfl), sub_zero]
  have hle := (pair_le hz1 ((corrRes_inH0 h hr hu0 huT).mono (by norm_num : (0 : ℝ) - 1 ≤ 0))).2
  rw [zero_add] at hle
  have h1 : hnorm ((0 : ℝ) - 1) (corrRes r g y u) ≤ Φ :=
    (hnorm_mono (by norm_num) (corrRes_inH0 h hr hu0 huT)).trans (hres u hu)
  have h2 := le_abs_self (pair 0 (corrSlow r g y u) (corrRes r g y u))
  have h3 := hnorm_nonneg 1 (corrSlow r g y u)
  have h4 := hnorm_nonneg ((0 : ℝ) - 1) (corrRes r g y u)
  nlinarith [sq_nonneg (hnorm 1 (corrSlow r g y u) - hnorm ((0 : ℝ) - 1) (corrRes r g y u)),
    mul_le_mul_of_nonneg_left h1 h3]

/-- **F0, consequences**: exponential contraction of `‖y_S‖₀²` to the level `Φ²` and the
dissipation budget. -/
theorem corr_l2_bounds (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {Φ : ℝ}
    (hres : ∀ u ∈ Icc s t, hnorm 0 (corrRes r g y u) ≤ Φ) :
    (∀ u ∈ Icc s t, hnorm 0 (corrSlow r g y u) ^ 2 ≤
      Real.exp (-(u - s)) * hnorm 0 (corrSlow r g y s) ^ 2 + Φ ^ 2) ∧
    (∫ u in s..t, hnorm 1 (corrSlow r g y u) ^ 2) ≤
      hnorm 0 (corrSlow r g y s) ^ 2 + Φ ^ 2 * (t - s) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hp : HeatPair 0 s t (corrSlow r g y) (corrForce r g y) :=
    (heatPair_corrSlow h hr (Or.inl rfl) ht0 ht).mono hs le_rfl
  have hc0 : ContinuousOn (fun u => hnorm 0 (corrSlow r g y u) ^ 2) (Icc s t) :=
    (continuousOn_corr_sq h hr (Or.inl rfl) ht0 ht).mono (Icc_subset_Icc_left hs)
  refine ⟨fun u hu => ?_, ?_⟩
  · have key := gronwall_decay (y := fun u => hnorm 0 (corrSlow r g y u) ^ 2) (lam := 1)
      (β := Φ ^ 2) hst one_pos (sq_nonneg Φ) hc0 (fun s' t' hs' hst' ht' => ?_) u hu.1 hu.2
    · simpa only [neg_one_mul, div_one] using key
    have hlaw := corr_l2_law h hr (hs.trans hs') hst' (lt_lifespan ht' ht)
      fun v hv => hres v ⟨hs'.trans hv.1, hv.2.trans ht'⟩
    have hsub : Icc s' t' ⊆ Icc s t := Icc_subset_Icc hs' ht'
    have hD : IntervalIntegrable (fun u => hnorm 1 (corrSlow r g y u) ^ 2) volume s' t' := by
      have := (hp.mono hs' ht').intervalIntegrable_dissipation hst'
      rwa [zero_add] at this
    have hmono : ∫ u in s'..t', hnorm 0 (corrSlow r g y u) ^ 2 ≤
        ∫ u in s'..t', hnorm 1 (corrSlow r g y u) ^ 2 := by
      refine intervalIntegral.integral_mono_on hst' ((hc0.mono hsub).intervalIntegrable_of_Icc hst')
        hD fun v hv => ?_
      have hz := (corrSlow_adm h hr (hs.trans (hs'.trans hv.1))
        (lt_lifespan (hv.2.trans ht') ht)).inH.mono (by norm_num : (1 : ℝ) ≤ 2)
      exact pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_mono (by norm_num) hz) 2
    rw [one_mul]
    linarith
  · exact le_trans (by linarith [sq_nonneg (hnorm 0 (corrSlow r g y t))])
      (corr_l2_law h hr hs hst ht hres)

/-! ### F1: the horizontal enstrophy law -/

/-- **F1** (route §2.2, `fg:prop:h`): `a_h(t)² + ∫ₛᵗ b_h² ≤ a_h(s)² + Φ²(t − s)`. -/
theorem corr_horiz_law (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {Φ : ℝ}
    (hres : ∀ u ∈ Icc s t, hnorm 0 (corrRes r g y u) ≤ Φ) :
    hnorm 1 (PiH (corrSlow r g y t)) ^ 2 + ∫ u in s..t, hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤
      hnorm 1 (PiH (corrSlow r g y s)) ^ 2 + Φ ^ 2 * (t - s) := by
  have hp : HeatPair 1 s t (fun u => PiH (corrSlow r g y u)) (fun u => PiH (corrForce r g y u)) :=
    (heatPair_corrH h hr (Or.inr (Or.inl rfl)) (hs.trans hst) ht).mono hs le_rfl
  have key := hp.energy_le (τ := 2) (θ := 1) (R := fun _ => Φ ^ 2) (by norm_num) hst
    intervalIntegrable_const ?_
  · rw [intervalIntegral.integral_const, smul_eq_mul] at key
    linarith
  refine ae_restrict_of_forall_mem measurableSet_Icc fun u hu => ?_
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hz := corrSlow_adm h hr hu0 huT
  have hz' := PiS_corrSlow r g y u
  have hH : InH ((1 : ℝ) + 1) (PiH (corrSlow r g y u)) := by
    rw [one_add_one_eq_two]; exact hz.inH.PiH
  show 2 * pair 1 (PiH (corrSlow r g y u)) (PiH (corrForce r g y u)) ≤
    1 * hnorm 2 (PiH (corrSlow r g y u)) ^ 2 + Φ ^ 2
  have h0 : pair 1 (PiH (corrSlow r g y u)) (Bsym (corrSlow r g y u) (corrSlow r g y u)) = 0 := by
    rw [← pair_PiH]
    exact pair_slow_horizontal hz hz' (Or.inr rfl)
  rw [pair_PiH, pair_corrForce h hr hu0 huT le_rfl hH, h0, sub_zero]
  have hle := (pair_le hH ((corrRes_inH0 h hr hu0 huT).mono (by norm_num : (1 : ℝ) - 1 ≤ 0))).2
  rw [one_add_one_eq_two] at hle
  have h1 : hnorm ((1 : ℝ) - 1) (corrRes r g y u) ≤ Φ :=
    (hnorm_mono (by norm_num) (corrRes_inH0 h hr hu0 huT)).trans (hres u hu)
  have h2 := le_abs_self (pair 1 (PiH (corrSlow r g y u)) (corrRes r g y u))
  have h3 := hnorm_nonneg 2 (PiH (corrSlow r g y u))
  have h4 := hnorm_nonneg ((1 : ℝ) - 1) (corrRes r g y u)
  nlinarith [sq_nonneg (hnorm 2 (PiH (corrSlow r g y u)) - hnorm ((1 : ℝ) - 1) (corrRes r g y u)),
    mul_le_mul_of_nonneg_left h1 h3]

/-- **F1, consequences**: exponential contraction of `a_h²` to the level `Φ²`, and the
dissipation budget `∫ b_h²`. -/
theorem corr_horiz_bounds (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {Φ : ℝ}
    (hres : ∀ u ∈ Icc s t, hnorm 0 (corrRes r g y u) ≤ Φ) :
    (∀ u ∈ Icc s t, hnorm 1 (PiH (corrSlow r g y u)) ^ 2 ≤
      Real.exp (-(u - s)) * hnorm 1 (PiH (corrSlow r g y s)) ^ 2 + Φ ^ 2) ∧
    (∫ u in s..t, hnorm 2 (PiH (corrSlow r g y u)) ^ 2) ≤
      hnorm 1 (PiH (corrSlow r g y s)) ^ 2 + Φ ^ 2 * (t - s) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hp : HeatPair 1 s t (fun u => PiH (corrSlow r g y u)) (fun u => PiH (corrForce r g y u)) :=
    (heatPair_corrH h hr (Or.inr (Or.inl rfl)) ht0 ht).mono hs le_rfl
  have hc1 : ContinuousOn (fun u => hnorm 1 (PiH (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrH_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  refine ⟨fun u hu => ?_, ?_⟩
  · have key := gronwall_decay (y := fun u => hnorm 1 (PiH (corrSlow r g y u)) ^ 2) (lam := 1)
      (β := Φ ^ 2) hst one_pos (sq_nonneg Φ) hc1 (fun s' t' hs' hst' ht' => ?_) u hu.1 hu.2
    · simpa only [neg_one_mul, div_one] using key
    have hlaw := corr_horiz_law h hr (hs.trans hs') hst' (lt_lifespan ht' ht)
      fun v hv => hres v ⟨hs'.trans hv.1, hv.2.trans ht'⟩
    have hsub : Icc s' t' ⊆ Icc s t := Icc_subset_Icc hs' ht'
    have hD : IntervalIntegrable (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) volume s' t' := by
      have := (hp.mono hs' ht').intervalIntegrable_dissipation hst'
      rwa [one_add_one_eq_two] at this
    have hmono : ∫ u in s'..t', hnorm 1 (PiH (corrSlow r g y u)) ^ 2 ≤
        ∫ u in s'..t', hnorm 2 (PiH (corrSlow r g y u)) ^ 2 := by
      refine intervalIntegral.integral_mono_on hst' ((hc1.mono hsub).intervalIntegrable_of_Icc hst')
        hD fun v hv => ?_
      have hz := (corrSlow_adm h hr (hs.trans (hs'.trans hv.1))
        (lt_lifespan (hv.2.trans ht') ht)).inH.PiH
      exact pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_mono (by norm_num) hz) 2
    rw [one_mul]
    linarith
  · exact le_trans (by linarith [sq_nonneg (hnorm 1 (PiH (corrSlow r g y t)))])
      (corr_horiz_law h hr hs hst ht hres)

/-! ### F2: the vertical `H¹` law and window averaging -/

/-- **F2, the law** (route §2.2, with T3a at `c_L = 5`):
`a_ζ(t)² + ½∫ₛᵗ b_ζ² ≤ a_ζ(s)² + ∫ₛᵗ (25 a_h² a_ζ² + 2Φ²)`. -/
theorem corr_vert_law (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {Φ : ℝ}
    (hres : ∀ u ∈ Icc s t, hnorm 0 (corrRes r g y u) ≤ Φ) :
    hnorm 1 (PiV (corrSlow r g y t)) ^ 2 +
        1 / 2 * ∫ u in s..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤
      hnorm 1 (PiV (corrSlow r g y s)) ^ 2 + ∫ u in s..t,
        (25 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 * hnorm 1 (PiV (corrSlow r g y u)) ^ 2 +
          2 * Φ ^ 2) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hp : HeatPair 1 s t (fun u => PiV (corrSlow r g y u)) (fun u => PiV (corrForce r g y u)) :=
    (heatPair_corrV h hr (Or.inr (Or.inl rfl)) ht0 ht).mono hs le_rfl
  have hcH : ContinuousOn (fun u => hnorm 1 (PiH (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrH_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hcV : ContinuousOn (fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hR : IntervalIntegrable (fun u => 25 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 *
      hnorm 1 (PiV (corrSlow r g y u)) ^ 2 + 2 * Φ ^ 2) volume s t :=
    (((continuousOn_const.mul hcH).mul hcV).add continuousOn_const).intervalIntegrable_of_Icc hst
  have key := hp.energy_le (τ := 2) (θ := 3 / 2) (by norm_num) hst hR ?_
  · have e : (2 : ℝ) - 3 / 2 = 1 / 2 := by norm_num
    rw [e] at key
    exact key
  refine ae_restrict_of_forall_mem measurableSet_Icc fun u hu => ?_
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hz := corrSlow_adm h hr hu0 huT
  have hz' := PiS_corrSlow r g y u
  have hV : InH ((1 : ℝ) + 1) (PiV (corrSlow r g y u)) := by
    rw [one_add_one_eq_two]; exact hz.inH.PiV
  show 2 * pair 1 (PiV (corrSlow r g y u)) (PiV (corrForce r g y u)) ≤
    3 / 2 * hnorm 2 (PiV (corrSlow r g y u)) ^ 2 +
      (25 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 * hnorm 1 (PiV (corrSlow r g y u)) ^ 2 +
        2 * Φ ^ 2)
  rw [pair_PiV, pair_corrForce h hr hu0 huT le_rfl hV]
  have hT3 := pair_slow_vertical_lady hz hz'
  rw [pair_PiV] at hT3
  have hle := (pair_le hV ((corrRes_inH0 h hr hu0 huT).mono (by norm_num : (1 : ℝ) - 1 ≤ 0))).2
  rw [one_add_one_eq_two] at hle
  have h1 : hnorm ((1 : ℝ) - 1) (corrRes r g y u) ≤ Φ :=
    (hnorm_mono (by norm_num) (corrRes_inH0 h hr hu0 huT)).trans (hres u hu)
  have h2 := le_abs_self (pair 1 (PiV (corrSlow r g y u)) (corrRes r g y u))
  have h2' := neg_abs_le (pair 1 (PiV (corrSlow r g y u)) (Bsym (corrSlow r g y u)
    (corrSlow r g y u)))
  have h3 := hnorm_nonneg 2 (PiV (corrSlow r g y u))
  have h4 := hnorm_nonneg ((1 : ℝ) - 1) (corrRes r g y u)
  have h5 := hnorm_nonneg 1 (PiH (corrSlow r g y u))
  have h6 := hnorm_nonneg 1 (PiV (corrSlow r g y u))
  have hprod : 0 ≤ hnorm 1 (PiH (corrSlow r g y u)) * hnorm 1 (PiV (corrSlow r g y u)) :=
    mul_nonneg h5 h6
  nlinarith [sq_nonneg (hnorm 2 (PiV (corrSlow r g y u)) - 2 * hnorm ((1 : ℝ) - 1) (corrRes r g y u)),
    sq_nonneg (hnorm 2 (PiV (corrSlow r g y u)) -
      5 * (hnorm 1 (PiH (corrSlow r g y u)) * hnorm 1 (PiV (corrSlow r g y u)))),
    mul_le_mul_of_nonneg_left h1 h3]

/-- **F2, window averaging** (route §2.2: "average `τ` over the first unit window; the `L²`
dissipation `∫ a_ζ² ≲ μ²` removes the exponential").  With `a_h ≤ A_h` on the piece and
`∫ₛᵗ ‖y_S‖₁² ≤ I`: `a_ζ(u)² ≤ a_ζ(s)² + 25A_h² I + 2Φ²(t−s)` on `[s, t]`,
`a_ζ(u)² ≤ (1 + 25A_h²) I + 2Φ²(t−s)` on `[s+1, t]`, and
`∫ₛᵗ b_ζ² ≤ 2(a_ζ(s)² + 25A_h² I + 2Φ²(t−s))`. -/
theorem corr_vert_bounds (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {Φ Ah I : ℝ}
    (hres : ∀ u ∈ Icc s t, hnorm 0 (corrRes r g y u) ≤ Φ)
    (hah : ∀ u ∈ Icc s t, hnorm 1 (PiH (corrSlow r g y u)) ≤ Ah)
    (hI : (∫ u in s..t, hnorm 1 (corrSlow r g y u) ^ 2) ≤ I) :
    (∀ u ∈ Icc s t, hnorm 1 (PiV (corrSlow r g y u)) ^ 2 ≤
      hnorm 1 (PiV (corrSlow r g y s)) ^ 2 + 25 * Ah ^ 2 * I + 2 * Φ ^ 2 * (t - s)) ∧
    (∀ u ∈ Icc (s + 1) t, hnorm 1 (PiV (corrSlow r g y u)) ^ 2 ≤
      I + 25 * Ah ^ 2 * I + 2 * Φ ^ 2 * (t - s)) ∧
    (∫ u in s..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2) ≤
      2 * (hnorm 1 (PiV (corrSlow r g y s)) ^ 2 + 25 * Ah ^ 2 * I + 2 * Φ ^ 2 * (t - s)) := by
  have ht0 : 0 ≤ t := hs.trans hst
  set f : ℝ → ℝ := fun u => hnorm 1 (PiV (corrSlow r g y u)) ^ 2 with hf
  have hcV : ContinuousOn f (Icc s t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hcH : ContinuousOn (fun u => hnorm 1 (PiH (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrH_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hc1 : ContinuousOn (fun u => hnorm 1 (corrSlow r g y u) ^ 2) (Icc s t) :=
    (continuousOn_corr_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hf0 : ∀ u, 0 ≤ f u := fun u => sq_nonneg _
  have hAh0 : 0 ≤ Ah := (hnorm_nonneg _ _).trans (hah s ⟨le_rfl, hst⟩)
  -- `∫ f ≤ ∫ ‖y_S‖₁² ≤ I` on every subinterval
  have hfle : ∀ u ∈ Icc s t, f u ≤ hnorm 1 (corrSlow r g y u) ^ 2 := fun u hu => by
    have hz := (corrSlow_adm h hr (hs.trans hu.1) (lt_lifespan hu.2 ht)).inH.mono
      (by norm_num : (1 : ℝ) ≤ 2)
    exact pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_PiV_le' hz) 2
  have hint : ∀ s' t', s ≤ s' → s' ≤ t' → t' ≤ t → ∫ u in s'..t', f u ≤ I := by
    intro s' t' hs' hst' ht'
    have hsub : Icc s' t' ⊆ Icc s t := Icc_subset_Icc hs' ht'
    calc ∫ u in s'..t', f u ≤ ∫ u in s..t, f u :=
          intervalIntegral.integral_mono_interval hs' hst' ht'
            (Filter.Eventually.of_forall hf0) (hcV.intervalIntegrable_of_Icc hst)
      _ ≤ ∫ u in s..t, hnorm 1 (corrSlow r g y u) ^ 2 :=
          intervalIntegral.integral_mono_on hst (hcV.intervalIntegrable_of_Icc hst)
            (hc1.intervalIntegrable_of_Icc hst) hfle
      _ ≤ I := hI
  -- the law with constants: `f t' + ½ ∫ b_ζ² ≤ f s' + 25 A_h² I + 2Φ²(t' − s')`
  have hlaw : ∀ s' t', s ≤ s' → s' ≤ t' → t' ≤ t →
      f t' + 1 / 2 * (∫ u in s'..t', hnorm 2 (PiV (corrSlow r g y u)) ^ 2) ≤
        f s' + 25 * Ah ^ 2 * I + 2 * Φ ^ 2 * (t' - s') := by
    intro s' t' hs' hst' ht'
    have hsub : Icc s' t' ⊆ Icc s t := Icc_subset_Icc hs' ht'
    have h1 := corr_vert_law h hr (hs.trans hs') hst' (lt_lifespan ht' ht)
      fun v hv => hres v (hsub hv)
    have hRi : IntervalIntegrable (fun u => 25 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 *
        hnorm 1 (PiV (corrSlow r g y u)) ^ 2 + 2 * Φ ^ 2) volume s' t' :=
      ((((continuousOn_const.mul hcH).mul hcV).add continuousOn_const).mono hsub
        ).intervalIntegrable_of_Icc hst'
    have h2 : ∫ u in s'..t', (25 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 *
        hnorm 1 (PiV (corrSlow r g y u)) ^ 2 + 2 * Φ ^ 2) ≤
        ∫ u in s'..t', (25 * Ah ^ 2 * f u + 2 * Φ ^ 2) := by
      refine intervalIntegral.integral_mono_on hst' hRi
        (((hcV.mono hsub).const_mul _ |>.add continuousOn_const).intervalIntegrable_of_Icc hst')
        fun v hv => ?_
      have hv' := hsub hv
      have ha := hah v hv'
      have ha0 := hnorm_nonneg 1 (PiH (corrSlow r g y v))
      have hsq : hnorm 1 (PiH (corrSlow r g y v)) ^ 2 ≤ Ah ^ 2 :=
        pow_le_pow_left₀ ha0 ha 2
      have := mul_le_mul_of_nonneg_right hsq (hf0 v)
      simp only [hf]
      nlinarith
    rw [intervalIntegral.integral_add ((hcV.mono hsub).intervalIntegrable_of_Icc hst' |>.const_mul _)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul] at h2
    have h3 := hint s' t' hs' hst' ht'
    have hA : 0 ≤ 25 * Ah ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h3 hA
    simp only [hf] at h1 h2 ⊢
    linarith
  refine ⟨fun u hu => ?_, fun u hu => ?_, ?_⟩
  · have h1 := hlaw s u le_rfl hu.1 hu.2
    have h2 : 0 ≤ ∫ v in s..u, hnorm 2 (PiV (corrSlow r g y v)) ^ 2 :=
      intervalIntegral.integral_nonneg hu.1 fun _ _ => sq_nonneg _
    have h3 : 2 * Φ ^ 2 * (u - s) ≤ 2 * Φ ^ 2 * (t - s) :=
      mul_le_mul_of_nonneg_left (by linarith [hu.2]) (by positivity)
    simp only [hf] at h1 ⊢
    linarith
  · -- window averaging: a good time `τ ∈ [s, s+1]`
    have hs1 : s + 1 ≤ t := hu.1.trans hu.2
    obtain ⟨τ, hτ, hfτ⟩ := exists_le_average (f := f) (a := s) (b := s + 1) (by linarith)
      (hcV.mono (Icc_subset_Icc_right hs1))
    have hτI : f τ ≤ I := by
      have := hint s (s + 1) le_rfl (by linarith) hs1
      simp only [add_sub_cancel_left, mul_one] at hfτ
      linarith
    have h1 := hlaw τ u hτ.1 (hτ.2.trans hu.1) hu.2
    have h2 : 0 ≤ ∫ v in τ..u, hnorm 2 (PiV (corrSlow r g y v)) ^ 2 :=
      intervalIntegral.integral_nonneg (hτ.2.trans hu.1) fun _ _ => sq_nonneg _
    have h3 : 2 * Φ ^ 2 * (u - τ) ≤ 2 * Φ ^ 2 * (t - s) :=
      mul_le_mul_of_nonneg_left (by linarith [hu.2, hτ.1]) (by positivity)
    simp only [hf] at h1 hτI ⊢
    linarith
  · have h1 := hlaw s t le_rfl hst le_rfl
    have h2 := hf0 t
    simp only [hf] at h1 h2 ⊢
    linarith

end Quant

end OVNS

end
