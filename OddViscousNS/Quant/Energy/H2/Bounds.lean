import OddViscousNS.Quant.Energy.H2.Cubic

/-!
# E8 — the term-by-term bounds of the `H²` energy identity

The right-hand side `h2RHS` of `h2Energy_identity` (`Identity.lean`) is bounded at almost every time
of a piece by `(9/64) c_F² + B b_F c_F + G' b_F² + H'` (`h2RHS_budget`), once the role thresholds
`h2Threshold` are paid and the leading role 31 is paid through `K₂ √P_F y^{3/2} N(q) ≤ 1`.

* **A, B.** The two facts behind `B = C_H ρ^{1−θ} P_F^θ` (spec §2.3 (b), open point (b) of the
  brief): the Hölder interpolation `hnorm_frac_le` (new) and the cap-free `‖F‖₀ ≤ ρ`
  (`fast_zero_le_rho`, from the plain `L²` balance and Poincaré; no extra interface hypothesis).
* **C, D.** The metric at weight two (TeX eq. quant-metric at `s = 2`, Body 12 §6): the Hermitian
  numerator `num2` cancels the factor of `Φ` and leaves `1/q`.  The eight helicities are bounded one
  by one, not by the paired Schur lemma of Body 12 §2: `metBil2_le`, `pair_X1op_slow_le`.
* **E.** The native differential: near by `nearD2_le` (`role31_bound`), far by (M4) and
  `|corrSym| ≤ 1/q`: `cubicD_two_le`.
* **F.** The proper remainders, roles 16, 17 (`Cubic.lean`).
* **G.** The norms on a piece, among them the mixed source `2Π_F Q_τ(S, F)` (open point (a) of the
  brief): `fastNL_two_le` and `slow_three_le` turn `‖S‖₃` into `‖y_S‖₃ + (16c₄ b_F/q) c_F`.
* **H.** The slow `H³` price (TeX eq. quant-short-slow): `slow_price`, degree `7` on the whole
  piece, with the free parameter `A₃ = a_h + μ^{3/2}`.
* **I, J.** The budget: `budget_core`, `thr_pieces`, `h2RHS_terms`, `h2RHS_budget`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.H2

/-! ### A. The fractional interpolation (spec §2.3 (b): "a fractional Hölder interpolation lemma,
new") -/

/-- **Fractional interpolation** `‖F‖_θ ≤ ‖F‖₀^{1−θ} ‖F‖₁^θ`, `0 < θ < 1`. -/
theorem hnorm_frac_le {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) {F : Field} (hF : InH 1 F) :
    hnorm θ F ≤ hnorm 0 F ^ (1 - θ) * hnorm 1 F ^ θ := by
  set α : ℝ := 1 - θ with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  have hαβ : α + θ = 1 := by rw [hα]; ring
  have hpq : (1 / α).HolderConjugate (1 / θ) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, by simpa only [one_div, inv_inv] using hαβ⟩
    rw [lt_one_div one_pos hα0, one_div_one]
    linarith
  have hX : ∀ k, 0 ≤ ‖F k‖ ^ 2 := fun k => sq_nonneg _
  have hw : ∀ s k, 0 ≤ sobWeight s k * ‖F k‖ ^ 2 := fun s k =>
    mul_nonneg (sobWeight_nonneg s k) (hX k)
  have hpow : ∀ (t : ℝ) (_ : 0 < t) (s : ℝ) (k : Mode),
      ((sobWeight s k * ‖F k‖ ^ 2) ^ t) ^ (1 / t) = sobWeight s k * ‖F k‖ ^ 2 := fun t ht s k => by
    rw [← Real.rpow_mul (hw s k), mul_one_div_cancel ht.ne', Real.rpow_one]
  have hterm : ∀ k, sobWeight θ k * ‖F k‖ ^ 2 =
      (sobWeight 0 k * ‖F k‖ ^ 2) ^ α * (sobWeight 1 k * ‖F k‖ ^ 2) ^ θ := fun k => by
    simp only [sobWeight]
    split_ifs with hk
    · simp [Real.zero_rpow hα0.ne']
    have hk0 : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
    rw [Real.mul_rpow (Real.rpow_nonneg hk0.le _) (hX k),
      Real.mul_rpow (Real.rpow_nonneg hk0.le _) (hX k), ← Real.rpow_mul hk0.le,
      ← Real.rpow_mul hk0.le]
    calc absk k ^ (2 * θ) * ‖F k‖ ^ 2
        = absk k ^ (2 * 0 * α + 2 * 1 * θ) * (‖F k‖ ^ 2) ^ (α + θ) := by
          rw [hαβ, Real.rpow_one]
          congr 2
          ring
      _ = _ := by
          rw [Real.rpow_add hk0, Real.rpow_add' (hX k) (by rw [hαβ]; exact one_ne_zero)]
          ring
  have hI0 : InH 0 F := hF.mono (by norm_num)
  have hIθ : InH θ F := hF.mono h1.le
  have hS1 : Summable fun k => ((sobWeight 0 k * ‖F k‖ ^ 2) ^ α) ^ (1 / α) := by
    simp only [hpow α hα0]
    exact hI0
  have hS2 : Summable fun k => ((sobWeight 1 k * ‖F k‖ ^ 2) ^ θ) ^ (1 / θ) := by
    simp only [hpow θ h0]
    exact hF
  have hH := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq (fun k => Real.rpow_nonneg (hw 0 k) α)
    (fun k => Real.rpow_nonneg (hw 1 k) θ) hS1 hS2
  simp only [hpow α hα0, hpow θ h0, one_div_one_div, ← hterm] at hH
  have e1 : ∀ (s t : ℝ), (hnorm s F ^ 2) ^ t = (hnorm s F ^ t) ^ 2 := fun s t => by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (hnorm_nonneg s F),
      ← Real.rpow_mul (hnorm_nonneg s F), mul_comm]
  rw [← hnorm_sq hIθ, ← hnorm_sq hI0, ← hnorm_sq hF, e1, e1, ← mul_pow] at hH
  exact (pow_le_pow_iff_left₀ (hnorm_nonneg _ _)
    (mul_nonneg (Real.rpow_nonneg (hnorm_nonneg _ _) _) (Real.rpow_nonneg (hnorm_nonneg _ _) _))
    two_ne_zero).mp hH


variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### B. The cap-free `L²` bound (`‖F‖₀ ≤ ρ`, open point (b) of the brief) -/

/-- The integrated `L²` energy inequality of the filtered solution: `Q_τ` conserves energy
(`pair_Qphase_self`), `R(τ)` is an isometry (`hnorm_rotF`). -/
private lemma y_energy_step (h : ActualSol μ φ r g y Ty) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) :
    hnorm 0 (y t) ^ 2 + ∫ u in s..t, hnorm 1 (y u) ^ 2 ≤ hnorm 0 (y s) ^ 2 + φ ^ 2 * (t - s) := by
  have hP := IsHeatSol.heatPair_low (majorized_filtN r 0) (goodForce_filtG r 0 h.force_adm) h.sol
    (σ := 0) (Or.inl rfl) (hs.trans hst) ht
  have hp := hP.mono hs le_rfl
  have hid := hp.energy_identity le_rfl hst le_rfl
  have hD := hp.intervalIntegrable_dissipation hst
  have hPr := hp.intervalIntegrable_pair hst
  rw [zero_add] at hid hD
  have hG0 : ∀ u, hnorm 0 (filtG r 0 g u) ≤ φ := fun u => by
    unfold filtG
    rw [hnorm_rotF _ h.force_adm.sol]
    exact (hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le
  have hbound : ∀ u ∈ Icc s t, 2 * pair 0 (y u) (filtG r 0 g u -
      filtN r 0 u (y u) (y u)) ≤ hnorm 1 (y u) ^ 2 + φ ^ 2 := by
    intro u hu
    have hu0 := hs.trans hu.1
    have huT := lt_lifespan hu.2 ht
    have hy := h.sol.adm u hu0 huT
    have hc : InH (0 + 1) (y u) := hy.inH.mono (by norm_num)
    have hGa := (goodForce_filtG r 0 h.force_adm).adm u
    have hG : InH (0 - 1) (filtG r 0 g u) := hGa.inH.mono (by norm_num)
    have hN : InH (0 - 1) (filtN r 0 u (y u) (y u)) :=
      ((hnorm_Qm_zero_le (phaseM_bdd _) hy.mz hy.mz).1).mono (by norm_num)
    rw [pair_sub hc hG hN]
    have h0 : pair 0 (y u) (filtN r 0 u (y u) (y u)) = 0 := pair_Qphase_self _ hy
    rw [h0, sub_zero]
    have h1 := (pair_le hc hG).2
    rw [show (0 : ℝ) + 1 = 1 by norm_num] at h1
    have h2 : hnorm (0 - 1) (filtG r 0 g u) ≤ φ :=
      (hnorm_mono (by norm_num) (hGa.inH.mono (by norm_num))).trans (hG0 u)
    have h3 := hnorm_nonneg 1 (y u)
    have h4 : pair 0 (y u) (filtG r 0 g u) ≤ hnorm 1 (y u) * φ :=
      (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_left h2 h3))
    nlinarith [sq_nonneg (hnorm 1 (y u) - φ)]
  have hint : 2 * (∫ u in s..t, pair 0 (y u) (filtG r 0 g u - filtN r 0 u (y u) (y u))) ≤
      (∫ u in s..t, hnorm 1 (y u) ^ 2) + φ ^ 2 * (t - s) := by
    rw [← intervalIntegral.integral_const_mul]
    have e : (∫ u in s..t, hnorm 1 (y u) ^ 2) + φ ^ 2 * (t - s) =
        ∫ u in s..t, (hnorm 1 (y u) ^ 2 + φ ^ 2) := by
      rw [intervalIntegral.integral_add hD intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [e]
    exact intervalIntegral.integral_mono_on hst (hPr.const_mul 2)
      (hD.add intervalIntegrable_const) hbound
  linarith

/-- **`‖y(t)‖₀ ≤ μ + φ` for every time of the lifespan, without any cap**: the plain energy
inequality with Poincaré (`‖y‖₀ ≤ ‖y‖₁`) and `gronwall_decay`. -/
theorem hnorm_zero_y_le (h : ActualSol μ φ r g y Ty) (hφ : 0 ≤ φ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t < Ty) : hnorm 0 (y t) ≤ μ + φ := by
  have hP := IsHeatSol.heatPair_low (majorized_filtN r 0) (goodForce_filtG r 0 h.force_adm) h.sol
    (σ := 0) (Or.inl rfl) ht0 ht
  have hc := hP.continuousOn_hnorm_sq ht0
  have hD0 : ∀ s t', 0 ≤ s → s ≤ t' → t' ≤ t →
      IntervalIntegrable (fun u => hnorm 0 (y u) ^ 2) volume s t' := fun s t' hs hst' ht' =>
    ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le hst']
      exact hc.mono (Icc_subset_Icc hs ht'))
  have key := gronwall_decay (y := fun u => hnorm 0 (y u) ^ 2) (lam := 1) (β := φ ^ 2) ht0
    one_pos (sq_nonneg φ) hc (fun s t' h1 h2 h3 => ?_) t ht0 le_rfl
  · have hμ : 0 ≤ μ := (hnorm_nonneg 2 (y 0)).trans h.init_le
    have hy0 : hnorm 0 (y 0) ≤ μ :=
      (hnorm_mono (by norm_num) (h.sol.adm 0 le_rfl (lt_of_le_of_lt
        (ENNReal.ofReal_le_ofReal ht0) ht)).inH).trans h.init_le
    simp only [div_one] at key
    have he : Real.exp (-1 * (t - 0)) * hnorm 0 (y 0) ^ 2 ≤ hnorm 0 (y 0) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (Real.exp_le_one_iff.2 (by linarith))
    have h2 := pow_le_pow_left₀ (hnorm_nonneg 0 (y 0)) hy0 2
    have h3 : hnorm 0 (y t) ^ 2 ≤ (μ + φ) ^ 2 := by nlinarith [mul_nonneg hμ hφ]
    exact (pow_le_pow_iff_left₀ (hnorm_nonneg _ _) (add_nonneg hμ hφ) two_ne_zero).mp h3
  · have htT := lt_lifespan h3 ht
    have hs' := y_energy_step h h1 h2 htT
    have hsub : Icc s t' ⊆ Icc 0 t := Icc_subset_Icc h1 h3
    have hmono : ∫ u in s..t', hnorm 0 (y u) ^ 2 ≤ ∫ u in s..t', hnorm 1 (y u) ^ 2 := by
      have hp := IsHeatSol.heatPair_low (majorized_filtN r 0)
        (goodForce_filtG r 0 h.force_adm) h.sol (σ := 0) (Or.inl rfl) (h1.trans h2) htT
      have i1 := (hp.mono h1 le_rfl).intervalIntegrable_dissipation h2
      rw [zero_add] at i1
      refine intervalIntegral.integral_mono_on h2 (hD0 s t' h1 h2 h3) i1 fun u hu => ?_
      have hi : InH 1 (y u) := InH.mono (by norm_num)
        (h.sol.adm u (h1.trans hu.1) (lt_lifespan hu.2 htT)).inH
      exact pow_le_pow_left₀ (hnorm_nonneg _ _) (hnorm_mono (by norm_num) hi) 2
    simp only [one_mul]
    linarith

/-- `‖ψ‖₂ ≤ 2φ/q` at every time. -/
lemma psi_two_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    InH 2 (psi r 0 g u) ∧ hnorm 2 (psi r 0 g u) ≤ 2 * φ / |r| := by
  obtain ⟨hI, hb⟩ := psi_bound (t₀ := 0) hr h.force_adm u hu
  have hg1 : hnorm 1 g ≤ φ := (hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le
  have hr0 : 0 < |r| := abs_pos.mpr hr
  refine ⟨hI, hb.trans ?_⟩
  gcongr

/-- **`‖F‖₀ ≤ ρ` on the whole lifespan, from nothing but the equation** (resolves open point (b)
of the brief: no extra hypothesis of `H2EnergyInterface` is needed).  The survey's derivation
through `W₀` (E4) uses a cap-dependent functional on `[0, t]`; the total energy needs no cap:
`‖F‖₀ ≤ ‖x‖₀ ≤ ‖y‖₀ + ‖ψ‖₀ ≤ μ + φ + 2φ/q ≤ ρ`. -/
theorem fast_zero_le_rho (h : ActualSol μ φ r g y Ty) (hφ : 0 ≤ φ) (hr : 1 ≤ |r|) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < Ty) : fastNorm 0 r g y t ≤ rhoOf μ φ := by
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr; linarith
  have hx := actual_adm h ht0 ht
  have hy := h.sol.adm t ht0 ht
  obtain ⟨hψI, hψ⟩ := psi_two_le h hr0 ht0
  have h1 : hnorm 0 (actual r g y t) ≤ hnorm 0 (y t) + hnorm 0 (psi r 0 g t) :=
    hnorm_sub_le (hy.inH.mono (by norm_num)) (hψI.mono (by norm_num))
  have h2 := hnorm_zero_y_le h hφ ht0 ht
  have h3 : hnorm 0 (psi r 0 g t) ≤ 2 * φ := by
    refine (hnorm_mono (by norm_num) hψI).trans (hψ.trans ?_)
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h4 : fastNorm 0 r g y t ≤ hnorm 0 (actual r g y t) :=
    hnorm_PiF_le (hx.inH.mono (by norm_num))
  unfold rhoOf
  linarith

/-- `‖F‖_θ ≤ ρ^{1−θ} P_F^θ` where `a_F ≤ P_F`. -/
theorem fast_theta_le (h : ActualSol μ φ r g y Ty) (hφ : 0 ≤ φ) (hr : 1 ≤ |r|) {θ : ℝ}
    (h0 : 0 < θ) (h1 : θ < 1) {t PF : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < Ty)
    (ha : fastNorm 1 r g y t ≤ PF) :
    hnorm θ (PiF (actual r g y t)) ≤ rhoOf μ φ ^ (1 - θ) * PF ^ θ := by
  have hx := actual_adm h ht0 ht
  have hF1 : InH 1 (PiF (actual r g y t)) := hx.PiF.inH.mono (by norm_num)
  refine (hnorm_frac_le h0 h1 hF1).trans ?_
  have hρ := fast_zero_le_rho h hφ hr ht0 ht
  have e1 := Real.rpow_le_rpow (hnorm_nonneg 0 _) hρ (by linarith : (0 : ℝ) ≤ 1 - θ)
  have e2 := Real.rpow_le_rpow (hnorm_nonneg 1 _) ha h0.le
  exact mul_le_mul e1 e2 (Real.rpow_nonneg (hnorm_nonneg _ _) _)
    (Real.rpow_nonneg ((hnorm_nonneg 0 _).trans hρ) _)


/-! ### C. The metric at weight two: the numerator and the termwise bounds

Body 12 §6 proves `‖X_{1,s}‖ ≤ 44√104 B_S/q` with the paired Schur lemma.  Paying the eight helicity
patterns by absolute values needs no Schur lemma: on a slow–fast triad `(p, q, r = −(p+q))` the two
rootings of the weighted form collect into the TeX numerator (`tau_pair_two`), whose factor `v − u`
cancels the phase `Φ = q₃(u − v)` of the denominator (`norm_metSym_mul_le`). -/

/-- The Hermitian energy numerator at `s = 2` (TeX eq. quant-metric):
`l(v+u)(v²+u²) − uv(v²+uv+u²)`, with `u, v` the signed fast lengths. -/
def num2 (L u v : ℝ) : ℝ := L * (v + u) * (v ^ 2 + u ^ 2) - u * v * (v ^ 2 + u * v + u ^ 2)

/-- The size of `num2`. -/
def wb (P Q K : ℝ) : ℝ := P * (K + Q) * (K ^ 2 + Q ^ 2) + K * Q * (K ^ 2 + K * Q + Q ^ 2)

lemma wb_nonneg {P Q K : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hK : 0 ≤ K) : 0 ≤ wb P Q K := by
  unfold wb
  positivity

lemma abs_num2_le {L u v P Q K : ℝ} (hL : |L| = P) (hu : |u| = Q) (hv : |v| = K) :
    |num2 L u v| ≤ wb P Q K := by
  have hP : 0 ≤ P := hL ▸ abs_nonneg _
  have hQ : 0 ≤ Q := hu ▸ abs_nonneg _
  have hK : 0 ≤ K := hv ▸ abs_nonneg _
  have hu2 : u ^ 2 = Q ^ 2 := by rw [← hu, sq_abs]
  have hv2 : v ^ 2 = K ^ 2 := by rw [← hv, sq_abs]
  have h1 : |L * (v + u) * (v ^ 2 + u ^ 2)| ≤ P * (K + Q) * (K ^ 2 + Q ^ 2) := by
    rw [abs_mul, abs_mul, hL, hu2, hv2, abs_of_nonneg (by positivity : 0 ≤ K ^ 2 + Q ^ 2)]
    have : |v + u| ≤ K + Q := by rw [← hu, ← hv]; exact abs_add_le _ _
    gcongr
  have h2 : |u * v * (v ^ 2 + u * v + u ^ 2)| ≤ K * Q * (K ^ 2 + K * Q + Q ^ 2) := by
    rw [abs_mul, abs_mul, hu, hv, hu2, hv2]
    have h3 : |K ^ 2 + u * v + Q ^ 2| ≤ K ^ 2 + K * Q + Q ^ 2 := by
      refine (abs_add_three _ _ _).trans ?_
      rw [abs_mul, hu, hv, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg hQ hK)
    nlinarith
  unfold num2 wb
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- `wb ≤ 11 K²Q² + 4P²(K²+Q²)` on a triangle. -/
lemma wb_le_two {P Q K : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (h2 : K ≤ P + Q) (h3 : Q ≤ P + K) :
    wb P Q K ≤ 11 * (Q ^ 2 * K ^ 2) + 4 * P ^ 2 * (K ^ 2 + Q ^ 2) := by
  set s := K ^ 2 with hs
  set t := Q ^ 2 with ht
  set w := P ^ 2 with hw
  have hs0 : 0 ≤ s := sq_nonneg _
  have ht0 : 0 ≤ t := sq_nonneg _
  have hw0 : 0 ≤ w := sq_nonneg _
  have a1 : P * (K + Q) ≤ w / 2 + s + t := by
    nlinarith [sq_nonneg (P - (K + Q)), sq_nonneg (K - Q)]
  have a2 : K * Q ≤ (s + t) / 2 := by nlinarith [sq_nonneg (K - Q)]
  have a3 : s ≤ 2 * t + 2 * w := by nlinarith [sq_nonneg (P - Q)]
  have a4 : t ≤ 2 * s + 2 * w := by nlinarith [sq_nonneg (P - K)]
  have hst : 0 ≤ s + t := by positivity
  have b1 : P * (K + Q) * (s + t) ≤ (w / 2 + s + t) * (s + t) := mul_le_mul_of_nonneg_right a1 hst
  have b2 : K * Q * (s + K * Q + t) ≤ (s + t) / 2 * (s + (s + t) / 2 + t) := by
    have h0 : 0 ≤ K * Q := mul_nonneg hK hQ
    exact mul_le_mul a2 (by linarith) (by positivity) (by positivity)
  have b3 : s * s ≤ s * (2 * t + 2 * w) := mul_le_mul_of_nonneg_left a3 hs0
  have b4 : t * t ≤ t * (2 * s + 2 * w) := mul_le_mul_of_nonneg_left a4 ht0
  have hst0 : 0 ≤ s * t := mul_nonneg hs0 ht0
  unfold wb
  nlinarith

/-- `wb ≤ 8 P(K³+Q³) + 11 K²Q²(K+Q)/P` on a triangle with `P > 0` (the two orientations of Body 12
§4, §6, without the comparable/separated case split). -/
lemma wb_le_one {P Q K : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hK : 0 ≤ K) (h1 : P ≤ K + Q)
    (h2 : K ≤ P + Q) (h3 : Q ≤ P + K) :
    wb P Q K ≤ 8 * P * (K ^ 3 + Q ^ 3) + 11 * (K ^ 2 * Q ^ 2 * (K + Q)) / P := by
  refine (wb_le_two hP.le hQ hK h2 h3).trans ?_
  have e1 : 4 * P ^ 2 * (K ^ 2 + Q ^ 2) ≤ 8 * P * (K ^ 3 + Q ^ 3) := by
    have h4 : P * (K ^ 2 + Q ^ 2) ≤ (K + Q) * (K ^ 2 + Q ^ 2) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h5 : (K + Q) * (K ^ 2 + Q ^ 2) ≤ 2 * (K ^ 3 + Q ^ 3) := by
      nlinarith [mul_nonneg (add_nonneg hK hQ) (sq_nonneg (K - Q))]
    nlinarith
  have e2 : 11 * (Q ^ 2 * K ^ 2) ≤ 11 * (K ^ 2 * Q ^ 2 * (K + Q)) / P := by
    rw [le_div_iff₀ hP]
    have h6 : 0 ≤ K ^ 2 * Q ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h6]
  linarith

private lemma sg_sq (a : Sgn) : sg a ^ 2 = 1 := by cases a <;> simp [sg]

private lemma abs_sg_mul (a : Sgn) (x : ℝ) (hx : 0 ≤ x) : |sg a * x| = x := by
  rw [abs_mul, abs_of_nonneg hx]
  cases a <;> simp [sg]

/-- The triple product is alternating in its last two slots. -/
lemma trip_swap (A B C : V3) : trip A C B = -trip A B C := by
  simp only [trip, bd, cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

private lemma add_neg_add_self (p q : Mode) : p + -(p + q) = -q := by abel

lemma Phi_swap_met (a b c : Sgn) (p q : Mode) : Phi a c b p (-(p + q)) = Phi a b c p q := by
  simp only [Phi, add_neg_add_self, lam_neg]
  ring

lemma triHeat_swap (p q : Mode) : triHeat p (-(p + q)) = triHeat p q := by
  simp only [triHeat, add_neg_add_self, absSq_neg]
  ring

/-- The `X₁` multiplier takes the same value on the two rootings of a slow–fast triad. -/
lemma metM_swap (r τ : ℝ) (a b c : Sgn) {p q : Mode} :
    metM r τ a c b p (-(p + q)) = metM r τ a b c p q := by
  have hS : SlowFast a c b p (-(p + q)) ↔ SlowFast a b c p q := by
    unfold SlowFast
    rw [Phi_swap_met]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun h0 => h2 ?_, h3⟩
      simp [h1, h0]
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, h3⟩
      simpa [h1] using h2
  unfold metM
  by_cases h : SlowFast a b c p q
  · rw [ite_eq_left h, ite_eq_left (hS.2 h)]
    simp only [metSym, phaseM, Phi_swap_met, triHeat_swap]
  · rw [ite_eq_right h, ite_eq_right fun h' => h (hS.1 h')]

/-- **The numerator on a slow–fast triad** (TeX eq. quant-metric, `s = 2`): the two rootings of the
weighted form, with `L = α|p|`, `u = β|q|`, `v = γ|p+q|`, collect into
`½ (v − u) [L(v+u)(v²+u²) − uv(v²+uv+u²)] · [A, B, C]`. -/
lemma tau_pair_two (a b c : Sgn) {p q : Mode} (hk : p + q ≠ 0) (hq : q ≠ 0) (v0 v1 v2 : V3) :
    ((absSq (p + q) * absSq (p + q) : ℝ) : ℂ) *
        tau p q (hel a p v0) (hel b q v1) (hel c (-(p + q)) v2) +
      ((absSq q * absSq q : ℝ) : ℂ) *
        tau p (-(p + q)) (hel a p v0) (hel c (-(p + q)) v2) (hel b q v1) =
      ((1 / 2 * (sg c * absk (p + q) - sg b * absk q) *
        num2 (sg a * absk p) (sg b * absk q) (sg c * absk (p + q)) : ℝ) : ℂ) *
        trip (hel a p v0) (hel b q v1) (hel c (-(p + q)) v2) := by
  have hC : dotM (hel c (-(p + q)) v2) (p + q) = 0 := dotM_hel_neg c (p + q) v2
  have hB : dotM (hel b q v1) (p + -(p + q)) = 0 := by
    rw [add_neg_add_self, dotM_neg_mode, dotM_hel, neg_zero]
  have hk' : p + -(p + q) ≠ 0 := by
    rw [add_neg_add_self]
    exact neg_ne_zero.2 hq
  rw [tau_hel_eq_trip a b hk v0 v1 hC, tau_hel_eq_trip a c hk' v0 v2 hB, trip_swap, absk_neg]
  have e1 : absSq (p + q) = (sg c * absk (p + q)) ^ 2 := by
    rw [mul_pow, sg_sq, one_mul, absk_sq]
  have e2 : absSq q = (sg b * absk q) ^ 2 := by
    rw [mul_pow, sg_sq, one_mul, absk_sq]
  rw [e1, e2]
  simp only [num2]
  push_cast
  ring

/-- **The cancellation of the phase**: `|metSym| |v − u| ≤ 1/q` on a slow–fast triad (the phase is
`Φ = q₃ (u − v)`, Body 12 §3, `δ = n(u − v)`; `|q₃| ≥ 1`). -/
lemma norm_metSym_mul_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (a b c : Sgn) {p q : Mode} (hp : p 2 = 0)
    (hq : q 2 ≠ 0) (hΦ : Phi a b c p q ≠ 0) :
    ‖metSym r τ a b c p q‖ * |sg c * absk (p + q) - sg b * absk q| ≤ 1 / |r| := by
  set u := sg b * absk q with hu
  set v := sg c * absk (p + q) with hv
  have hphase : Phi a b c p q = (q 2 : ℝ) * (u - v) := by
    have e : (((p + q) 2 : ℤ) : ℝ) = (q 2 : ℝ) := by simp [hp]
    rw [Phi, lam_slow hp, lam, lam, e, hu, hv]
    ring
  have hr0 : 0 < |r| := abs_pos.mpr hr
  have hn : (1 : ℝ) ≤ |(q 2 : ℝ)| := by
    have : (1 : ℤ) ≤ |q 2| := Int.one_le_abs hq
    exact_mod_cast this
  have huv : u - v ≠ 0 := fun h0 => hΦ (by rw [hphase, h0, mul_zero])
  have hab : 0 < |u - v| := abs_pos.mpr huv
  have hz : |r| * |u - v| ≤ Real.sqrt (triHeat p q ^ 2 + (r * Phi a b c p q) ^ 2) := by
    have h1 : |r * Phi a b c p q| ≤ Real.sqrt (triHeat p q ^ 2 + (r * Phi a b c p q) ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (triHeat p q)])
    refine le_trans ?_ h1
    rw [hphase, abs_mul, abs_mul]
    nlinarith [mul_pos hr0 hab]
  have hS : 0 < |r| * |u - v| := mul_pos hr0 hab
  rw [metSym, norm_mul, show ‖phaseM τ a b c p q‖ = 1 by
    rw [phaseM, mul_comm, Complex.norm_exp_ofReal_mul_I], one_mul,
    Quant.norm_resolv_sgn (Or.inr rfl), abs_sub_comm v u, div_mul_eq_mul_div, one_mul,
    div_le_div_iff₀ (lt_of_lt_of_le hS hz) hr0]
  nlinarith

lemma hel_lapF_lapF (c : Sgn) (k : Mode) (Z : Field) :
    hel c k (lapF (lapF Z) k) = ((absSq k * absSq k : ℝ) : ℂ) • hel c k (Z k) := by
  simp only [lapF, hel_smul, smul_smul]
  push_cast
  rfl

/-- **The triad bound of the polarized metric**: the rootings `(p, q)` of `⟨A²G, X₁F⟩` and
`(p, −(p+q))` of `⟨A²F, X₁G⟩`, summed, are at most `(4/q) ‖S_p‖‖F_q‖‖G_r‖ wb(|p|,|q|,|k|)`. -/
theorem metric_triad_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S F G : Field} (hS : PiS S = S)
    (hF : PiF F = F) (p q : Mode) :
    ‖tripT (metM r τ) S F (lapF (lapF G)) p q +
        tripT (metM r τ) S G (lapF (lapF F)) p (-(p + q))‖ ≤
      4 / |r| * (‖S p‖ * ‖F q‖ * ‖G (-(p + q))‖ * wb (absk p) (absk q) (absk (p + q))) := by
  have hr0 : 0 < |r| := abs_pos.mpr hr
  have hw0 : 0 ≤ wb (absk p) (absk q) (absk (p + q)) :=
    wb_nonneg (absk_nonneg _) (absk_nonneg _) (absk_nonneg _)
  have hR0 : 0 ≤ 4 / |r| * (‖S p‖ * ‖F q‖ * ‖G (-(p + q))‖ * wb (absk p) (absk q) (absk (p + q))) :=
    by positivity
  have hsub : -(p + -(p + q)) = q := by abel
  by_cases hp : p 2 = 0
  swap
  · rw [tripT_zero_left _ _ _ (slow_zero hS hp), tripT_zero_left _ _ _ (slow_zero hS hp),
      add_zero, norm_zero]
    exact hR0
  by_cases hq : q 2 = 0
  · have h1 : lapF (lapF F) (-(p + -(p + q))) = 0 := by
      rw [hsub]
      simp [lapF, fast_zero hF hq]
    rw [tripT_zero_mid _ _ _ _ (fast_zero hF hq), tripT_zero_right _ _ _ h1, add_zero, norm_zero]
    exact hR0
  have hq0 : q ≠ 0 := fun h0 => hq (by simp [h0])
  have hk : p + q ≠ 0 := fun h0 => hq (by
    have := congrFun h0 2
    simpa [hp] using this)
  set R := -(p + q) with hR
  have hsubR : -(p + R) = q := hsub
  have e2 : tripT (metM r τ) S G (lapF (lapF F)) p R =
      ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, metM r τ a c b p R *
        tau p R (hel a p (S p)) (hel c R (G R)) (hel b q (lapF (lapF F) q)) := by
    simp only [tripT, hsubR]
    exact sum3_swap fun a b c => metM r τ a b c p R *
      tau p R (hel a p (S p)) (hel b R (G R)) (hel c q (lapF (lapF F) q))
  rw [e2, tripT, ← hR]
  simp only [← Finset.sum_add_distrib]
  set E := 1 / (2 * |r|) * (‖S p‖ * ‖F q‖ * ‖G R‖ * wb (absk p) (absk q) (absk (p + q))) with hE
  have hE0 : 0 ≤ E := by positivity
  have hterm : ∀ a b c, ‖metM r τ a b c p q *
      tau p q (hel a p (S p)) (hel b q (F q)) (hel c R (lapF (lapF G) R)) +
      metM r τ a c b p R *
        tau p R (hel a p (S p)) (hel c R (G R)) (hel b q (lapF (lapF F) q))‖ ≤ E := by
    intro a b c
    rw [hR, metM_swap, ← hR, hel_lapF_lapF, hel_lapF_lapF, tau_smul_right, tau_smul_right,
      ← mul_add]
    have e3 : ((absSq R * absSq R : ℝ) : ℂ) = ((absSq (p + q) * absSq (p + q) : ℝ) : ℂ) := by
      rw [hR, absSq_neg]
    rw [e3, hR, tau_pair_two a b c hk hq0, ← hR]
    unfold metM
    by_cases hsf : SlowFast a b c p q
    · rw [ite_eq_left hsf, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_mul]
      have h1 := norm_metSym_mul_le hr τ a b c hp hq hsf.2.2
      have h2 := abs_num2_le (abs_sg_mul a _ (absk_nonneg p)) (abs_sg_mul b _ (absk_nonneg q))
        (abs_sg_mul c _ (absk_nonneg (p + q)))
      have h3 : ‖trip (hel a p (S p)) (hel b q (F q)) (hel c R (G R))‖ ≤
          ‖S p‖ * ‖F q‖ * ‖G R‖ :=
        (norm_trip_le _ _ _).trans (by
          have h4 := norm_hel_le a p (S p)
          have h5 := norm_hel_le b q (F q)
          have h6 := norm_hel_le c R (G R)
          gcongr)
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      set M := ‖metSym r τ a b c p q‖
      set D := |sg c * absk (p + q) - sg b * absk q|
      set N := |num2 (sg a * absk p) (sg b * absk q) (sg c * absk (p + q))|
      set W := wb (absk p) (absk q) (absk (p + q))
      set Tn := ‖trip (hel a p (S p)) (hel b q (F q)) (hel c R (G R))‖
      set Pn := ‖S p‖ * ‖F q‖ * ‖G R‖
      have hM0 : 0 ≤ M := norm_nonneg _
      have hD0 : 0 ≤ D := abs_nonneg _
      have hN0 : 0 ≤ N := abs_nonneg _
      have hT0 : 0 ≤ Tn := norm_nonneg _
      have hP0 : 0 ≤ Pn := by positivity
      calc M * (1 / 2 * D * N * Tn) = (M * D) * (N * Tn) / 2 := by ring
        _ ≤ (1 / |r|) * (W * Pn) / 2 := by
            have h7 : N * Tn ≤ W * Pn := mul_le_mul h2 h3 hT0 hw0
            have h8 : (M * D) * (N * Tn) ≤ (1 / |r|) * (W * Pn) :=
              mul_le_mul h1 h7 (by positivity) (by positivity)
            linarith
        _ = E := by rw [hE]; field_simp
    · rw [ite_eq_right hsf, zero_mul, norm_zero]
      exact hE0
  refine (norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
    norm_sum_le_of_le _ fun c _ => hterm a b c).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, hE]
  push_cast
  field_simp
  ring

/-- The polarized pairing is bounded by the sum of the triad bounds. -/
theorem abs_pair_metM_add_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S F G : Field} (hS : PiS S = S)
    (hF : PiF F = F)
    (hs1 : Summable fun x : Mode × Mode => tripT (metM r τ) S F (lapF (lapF G)) x.1 x.2)
    (hs2 : Summable fun x : Mode × Mode => tripT (metM r τ) S G (lapF (lapF F)) x.1 x.2)
    (hb : Summable fun x : Mode × Mode =>
      ‖S x.1‖ * ‖F x.2‖ * ‖G (-(x.1 + x.2))‖ * wb (absk x.1) (absk x.2) (absk (x.1 + x.2)))
    (hp1 : pair 2 G (X1op r τ S F) =
      (∑' x : Mode × Mode, tripT (metM r τ) S F (lapF (lapF G)) x.1 x.2).re)
    (hp2 : pair 2 F (X1op r τ S G) =
      (∑' x : Mode × Mode, tripT (metM r τ) S G (lapF (lapF F)) x.1 x.2).re) :
    |pair 2 G (X1op r τ S F) + pair 2 F (X1op r τ S G)| ≤
      4 / |r| * ∑' x : Mode × Mode,
        ‖S x.1‖ * ‖F x.2‖ * ‖G (-(x.1 + x.2))‖ * wb (absk x.1) (absk x.2) (absk (x.1 + x.2)) := by
  have hr0 : 0 < |r| := abs_pos.mpr hr
  set U : Mode × Mode → ℂ := fun x => tripT (metM r τ) S G (lapF (lapF F)) x.1 x.2 with hU
  have hsi : Summable fun x => U (iota x) := iota.summable_iff.mpr hs2
  have e : ∑' x, U x = ∑' x, U (iota x) := (iota.tsum_eq U).symm
  have hsum : Summable fun x : Mode × Mode =>
      tripT (metM r τ) S F (lapF (lapF G)) x.1 x.2 + U (iota x) := hs1.add hsi
  have hre : pair 2 G (X1op r τ S F) + pair 2 F (X1op r τ S G) =
      (∑' x : Mode × Mode, (tripT (metM r τ) S F (lapF (lapF G)) x.1 x.2 + U (iota x))).re := by
    rw [hp1, hp2, ← Complex.add_re, hs1.tsum_add hsi, ← e]
  rw [hre]
  have hle : ∀ x : Mode × Mode, ‖tripT (metM r τ) S F (lapF (lapF G)) x.1 x.2 + U (iota x)‖ ≤
      4 / |r| * (‖S x.1‖ * ‖F x.2‖ * ‖G (-(x.1 + x.2))‖ *
        wb (absk x.1) (absk x.2) (absk (x.1 + x.2))) := fun x =>
    metric_triad_le hr τ hS hF x.1 x.2
  have hbs := hb.mul_left (4 / |r|)
  have hn : Summable fun x : Mode × Mode =>
      ‖tripT (metM r τ) S F (lapF (lapF G)) x.1 x.2 + U (iota x)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hbs
  calc _ ≤ ‖∑' x : Mode × Mode, (tripT (metM r τ) S F (lapF (lapF G)) x.1 x.2 + U (iota x))‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑' x : Mode × Mode, ‖tripT (metM r τ) S F (lapF (lapF G)) x.1 x.2 + U (iota x)‖ :=
        norm_tsum_le_tsum_norm hn
    _ ≤ ∑' x : Mode × Mode, 4 / |r| * (‖S x.1‖ * ‖F x.2‖ * ‖G (-(x.1 + x.2))‖ *
        wb (absk x.1) (absk x.2) (absk (x.1 + x.2))) := hn.tsum_le_tsum hle hbs
    _ = _ := tsum_mul_left

/-! ### D. The two metric bounds at weight two -/

/-- `∑ |h_k|/|k| ≤ c₄ ‖h‖₁`: `𝒜(Λ⁻¹h) ≤ c₄ ‖Λ⁻¹h‖₂`. -/
lemma summable_wtd_inv {h : Field} (hh : MZ 1 h) :
    (Summable fun k => ‖h k‖ / absk k) ∧ ∑' k, ‖h k‖ / absk k ≤ c4 * hnorm 1 h := by
  set G : Field := fun k => ((absk k)⁻¹ : ℂ) • h k with hG
  have hn : ∀ k, ‖G k‖ = ‖h k‖ / absk k := fun k => by
    simp only [hG, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (absk_nonneg k)]
    rw [div_eq_inv_mul]
  have hw : ∀ k, sobWeight 2 k * ‖G k‖ ^ 2 = sobWeight 1 k * ‖h k‖ ^ 2 := fun k => by
    by_cases hk : k = 0
    · subst hk
      simp [hG, hh.mean, sobWeight]
    have h0 : absk k ≠ 0 := (lt_of_lt_of_le one_pos (one_le_absk hk)).ne'
    rw [hn, sobWeight_two, sobWeight_one, ← absk_sq]
    field_simp
  have hI : InH 2 G := hh.inH.congr fun k => (hw k).symm
  have hG0 : G 0 = 0 := by simp [hG, hh.mean]
  have hN : hnorm 2 G = hnorm 1 h := by
    unfold hnorm
    exact congrArg _ (tsum_congr hw)
  have hs := summable_wiener hI
  have hle := wiener_le ⟨hI, hG0⟩
  refine ⟨hs.congr hn, ?_⟩
  have e : wiener G = ∑' k, ‖h k‖ / absk k := tsum_congr hn
  rwa [e, hN] at hle

private lemma absk_triangle (p q : Mode) :
    absk p ≤ absk (p + q) + absk q ∧ absk (p + q) ≤ absk p + absk q ∧
      absk q ≤ absk p + absk (p + q) := by
  refine ⟨?_, absk_add_le p q, ?_⟩
  · have := absk_sub_le (p + q) q
    rwa [add_sub_cancel_right] at this
  · have := absk_sub_le (p + q) p
    rw [add_sub_cancel_left] at this
    linarith

/-- **The polarized `X₁` bound at weight two** (Body 12 §6 eq. (12); TeX "`‖X₁‖ ≤ C B_S/q`", at
both metric weights): for slow `S ∈ H²`, real fast `F, G ∈ H²`,
`|⟨z_F, X₁ z_G⟩| ≤ c_bil ‖S‖₂ ‖F‖₂ ‖G‖₂/q`.  PROVED termwise (`metric_triad_le`). -/
theorem metBil2_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S F G : Field} (hS : MZ 2 S) (hS' : PiS S = S)
    (hF : MZ 2 F) (hF' : PiF F = F) (hFr : IsReal F) (hG : MZ 2 G) (hGr : IsReal G) :
    |metBil2 r τ S F G| ≤ cBil * hnorm 2 S * hnorm 2 F * hnorm 2 G / |r| := by
  have hr0 : 0 < |r| := abs_pos.mpr hr
  have hgain : ∀ a b c p q, ‖metM r τ a b c p q‖ ≤ 1 / absSq (p + q) :=
    fun a b c p q => norm_metM_le_absSq r τ a b c p q
  have hdat : ∀ {V : Field}, MZ 2 V → (Summable fun k => ‖V k‖) ∧
      (Summable fun k => ‖V k‖ ^ 2) ∧ Summable fun k => (absk k * ‖V k‖) ^ 2 := fun {V} hV =>
    ⟨summable_wiener hV.inH, summable_norm_sq_of_inH (hV.inH.mono (by norm_num)),
      summable_grad_sq hV⟩
  obtain ⟨s1, s2, s3⟩ := hdat hS
  obtain ⟨f1, f2, f3⟩ := hdat hF
  obtain ⟨g1, g2, g3⟩ := hdat hG
  have hs : ∀ {X Y : Field}, MZ 2 X → MZ 2 Y → Summable fun x : Mode × Mode =>
      tripT (metM r τ) S X (lapF (lapF Y)) x.1 x.2 := fun {X Y} hX hY => by
    obtain ⟨x1, -, x3⟩ := hdat hX
    have hb := (gradTri_bound (fun k => norm_nonneg (S k)) (fun k => norm_nonneg (X k))
      (fun k => norm_nonneg (lapF Y k)) s1 s3 x1 x3 (lapF_l2 hY.inH).1).1
    exact Summable.of_norm_bounded (hb.mul_left 8) fun x =>
      norm_tripT_gain_lap hgain S X (lapF Y) x.1 x.2
  have e1 := pair_two_eq_re_tsum_gain hgain hGr s2 f2 (Or.inl s3) (hs hF hG)
  have e2 := pair_two_eq_re_tsum_gain hgain hFr s2 g2 (Or.inl s3) (hs hG hF)
  obtain ⟨sS, nS⟩ := wtd_l2_two hS
  obtain ⟨sF, nF⟩ := wtd_l2_two hF
  obtain ⟨sG, nG⟩ := wtd_l2_two hG
  obtain ⟨t1, b1⟩ := summable_tri_first (b := fun k => ‖S k‖) (a := wtd 2 F) (c := wtd 2 G)
    (fun _ => norm_nonneg _) (wtd_nonneg 2 F) (wtd_nonneg 2 G) s1 sF sG
  obtain ⟨t2, b2⟩ := summable_tri_second (a := wtd 2 S) (c := wtd 2 G) (b := fun k => ‖F k‖)
    (wtd_nonneg 2 S) (fun _ => norm_nonneg _) (wtd_nonneg 2 G) sS sG f1
  obtain ⟨t3, b3⟩ := summable_tri_third (a := wtd 2 S) (c := wtd 2 F) (b := fun k => ‖G k‖)
    (wtd_nonneg 2 S) (fun _ => norm_nonneg _) (wtd_nonneg 2 F) sS sF g1
  rw [nF, nG] at b1
  rw [nS, nG] at b2
  rw [nS, nF] at b3
  have hle : ∀ x : Mode × Mode,
      ‖S x.1‖ * ‖F x.2‖ * ‖G (-(x.1 + x.2))‖ * wb (absk x.1) (absk x.2) (absk (x.1 + x.2)) ≤
        11 * (‖S x.1‖ * wtd 2 F x.2 * wtd 2 G (-(x.1 + x.2))) +
        4 * (wtd 2 S x.1 * ‖F x.2‖ * wtd 2 G (-(x.1 + x.2))) +
        4 * (wtd 2 S x.1 * wtd 2 F x.2 * ‖G (-(x.1 + x.2))‖) := fun x => by
    obtain ⟨h1, h2, h3⟩ := absk_triangle x.1 x.2
    have hw := wb_le_two (P := absk x.1) (Q := absk x.2) (K := absk (x.1 + x.2))
      (absk_nonneg _) (absk_nonneg _) (absk_nonneg _) h2 h3
    have hP : 0 ≤ ‖S x.1‖ * ‖F x.2‖ * ‖G (-(x.1 + x.2))‖ := by positivity
    have := mul_le_mul_of_nonneg_left hw hP
    refine this.trans (le_of_eq ?_)
    simp only [wtd, absk_neg]
    ring
  have hG' := ((t1.mul_left 11).add (t2.mul_left 4)).add (t3.mul_left 4)
  have hnn : ∀ x : Mode × Mode, 0 ≤ ‖S x.1‖ * ‖F x.2‖ * ‖G (-(x.1 + x.2))‖ *
      wb (absk x.1) (absk x.2) (absk (x.1 + x.2)) := fun x =>
    mul_nonneg (by positivity) (wb_nonneg (absk_nonneg _) (absk_nonneg _) (absk_nonneg _))
  have hbs := Summable.of_nonneg_of_le hnn hle hG'
  have key := abs_pair_metM_add_le hr τ hS' hF' (hs hF hG) (hs hG hF) hbs e1 e2
  have hsum := hbs.tsum_le_tsum hle hG'
  rw [((t1.mul_left 11).add (t2.mul_left 4)).tsum_add (t3.mul_left 4),
    (t1.mul_left 11).tsum_add (t2.mul_left 4), tsum_mul_left, tsum_mul_left, tsum_mul_left]
    at hsum
  have hc := c4_pos
  have aS : ∑' k, ‖S k‖ ≤ c4 * hnorm 2 S := wiener_le hS
  have aF : ∑' k, ‖F k‖ ≤ c4 * hnorm 2 F := wiener_le hF
  have aG : ∑' k, ‖G k‖ ≤ c4 * hnorm 2 G := wiener_le hG
  have nS0 := hnorm_nonneg 2 S
  have nF0 := hnorm_nonneg 2 F
  have nG0 := hnorm_nonneg 2 G
  have c1 : (∑' k, ‖S k‖) * (hnorm 2 F * hnorm 2 G) ≤
      c4 * hnorm 2 S * (hnorm 2 F * hnorm 2 G) :=
    mul_le_mul_of_nonneg_right aS (mul_nonneg nF0 nG0)
  have c2 : (∑' k, ‖F k‖) * (hnorm 2 S * hnorm 2 G) ≤
      c4 * hnorm 2 F * (hnorm 2 S * hnorm 2 G) :=
    mul_le_mul_of_nonneg_right aF (mul_nonneg nS0 nG0)
  have c3 : (∑' k, ‖G k‖) * (hnorm 2 S * hnorm 2 F) ≤
      c4 * hnorm 2 G * (hnorm 2 S * hnorm 2 F) :=
    mul_le_mul_of_nonneg_right aG (mul_nonneg nS0 nF0)
  set N := hnorm 2 S * hnorm 2 F * hnorm 2 G with hN
  have hN0 : 0 ≤ N := by positivity
  have hsum' : ∑' x : Mode × Mode, ‖S x.1‖ * ‖F x.2‖ * ‖G (-(x.1 + x.2))‖ *
      wb (absk x.1) (absk x.2) (absk (x.1 + x.2)) ≤ 19 * c4 * N := by
    have e3 : 19 * c4 * N = 11 * (c4 * hnorm 2 S * (hnorm 2 F * hnorm 2 G)) +
        4 * (c4 * hnorm 2 F * (hnorm 2 S * hnorm 2 G)) +
        4 * (c4 * hnorm 2 G * (hnorm 2 S * hnorm 2 F)) := by rw [hN]; ring
    rw [e3]
    linarith
  unfold metBil2 cBil
  have e4 : 2 * pair 2 G (X1op r τ S F) + 2 * pair 2 F (X1op r τ S G) =
      2 * (pair 2 G (X1op r τ S F) + pair 2 F (X1op r τ S G)) := by ring
  rw [e4, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h4 := key.trans (mul_le_mul_of_nonneg_left hsum' (by positivity : 0 ≤ 4 / |r|))
  have e5 : 2 ^ 8 * c4 * hnorm 2 S * hnorm 2 F * hnorm 2 G / |r| = 2 ^ 8 * c4 * N / |r| := by
    rw [hN]; ring
  rw [e5]
  have e6 : 2 * (4 / |r| * (19 * c4 * N)) = 152 * c4 * N / |r| := by ring
  have h5 : 152 * c4 * N / |r| ≤ 2 ^ 8 * c4 * N / |r| := by
    gcongr
    norm_num
  linarith

/-- **The genuine `H¹`-direction form at weight two** (Body 12 §6 eq. (14):
`|⟨z_s, X₁[h] z_s⟩| ≲ ‖h‖₁ F_s G_s/q` at both weights): for a slow real `h ∈ H¹` and a real fast
`F ∈ H³`, `|⟨A²F, X₁(h)F⟩| ≤ c_src ‖h‖₁ ‖F‖₂ ‖F‖₃/q`.  PROVED termwise (`metric_triad_le`,
`wb_le_one`: the two orientations without a case split). -/
theorem pair_X1op_slow_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {h F : Field} (hh : MZ 1 h)
    (hh' : PiS h = h) (hF : MZ 3 F) (hF' : PiF F = F) (hFr : IsReal F) :
    |pair 2 F (X1op r τ h F)| ≤ cSrc * hnorm 1 h * hnorm 2 F * hnorm 3 F / |r| := by
  have hr0 : 0 < |r| := abs_pos.mpr hr
  have hgain : ∀ a b c p q, ‖metM r τ a b c p q‖ ≤ 1 / absSq (p + q) :=
    fun a b c p q => norm_metM_le_absSq r τ a b c p q
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  have hh2 : Summable fun k => ‖h k‖ ^ 2 := summable_norm_sq_of_inH (hh.inH.mono (by norm_num))
  have f2 : Summable fun k => ‖F k‖ ^ 2 := summable_norm_sq_of_inH (hF.inH.mono (by norm_num))
  have f3 : Summable fun k => (absk k * ‖F k‖) ^ 2 := summable_grad_sq hF2
  have f1 : Summable fun k => ‖F k‖ := summable_wiener hF2.inH
  have hs : Summable fun x : Mode × Mode => tripT (metM r τ) h F (lapF (lapF F)) x.1 x.2 :=
    (slotX_sum hgain hh2 hF hF).1.of_norm
  have e1 := pair_two_eq_re_tsum_gain hgain hFr hh2 f2 (Or.inr f3) hs
  have hh1' : InH ((1 : ℕ) : ℝ) h := by simpa using hh.inH
  have s1 : Summable fun k => wtd 1 h k ^ 2 := summable_wtd_sq 1 hh1' hh.mean
  have n1 : Real.sqrt (∑' k, wtd 1 h k ^ 2) = hnorm 1 h := by
    have := sqrt_tsum_wtd_sq (u := h) 1 hh.mean
    simpa using this
  obtain ⟨sF2, nF2⟩ := wtd_l2 hF (n := 2) (by norm_num)
  obtain ⟨sF3, nF3⟩ := wtd_l2 hF (n := 3) (by norm_num)
  obtain ⟨hi1, hi2⟩ := summable_wtd_inv hh
  have hid0 : ∀ k, 0 ≤ ‖h k‖ / absk k := fun k => div_nonneg (norm_nonneg _) (absk_nonneg k)
  obtain ⟨t1, b1⟩ := summable_tri_second (a := wtd 1 h) (c := wtd 3 F) (b := fun k => ‖F k‖)
    (wtd_nonneg 1 h) (fun _ => norm_nonneg _) (wtd_nonneg 3 F) s1 sF3 f1
  obtain ⟨t2, b2⟩ := summable_tri_third (a := wtd 1 h) (c := wtd 3 F) (b := fun k => ‖F k‖)
    (wtd_nonneg 1 h) (fun _ => norm_nonneg _) (wtd_nonneg 3 F) s1 sF3 f1
  obtain ⟨t3, b3⟩ := summable_tri_first (b := fun k => ‖h k‖ / absk k) (a := wtd 2 F)
    (c := wtd 3 F) hid0 (wtd_nonneg 2 F) (wtd_nonneg 3 F) hi1 sF2 sF3
  obtain ⟨t4, b4⟩ := summable_tri_first (b := fun k => ‖h k‖ / absk k) (a := wtd 3 F)
    (c := wtd 2 F) hid0 (wtd_nonneg 3 F) (wtd_nonneg 2 F) hi1 sF3 sF2
  rw [n1, nF3] at b1 b2
  rw [nF2, nF3] at b3 b4
  push_cast at b1 b2 b3 b4
  have hle : ∀ x : Mode × Mode,
      ‖h x.1‖ * ‖F x.2‖ * ‖F (-(x.1 + x.2))‖ * wb (absk x.1) (absk x.2) (absk (x.1 + x.2)) ≤
        8 * (wtd 1 h x.1 * ‖F x.2‖ * wtd 3 F (-(x.1 + x.2))) +
        8 * (wtd 1 h x.1 * wtd 3 F x.2 * ‖F (-(x.1 + x.2))‖) +
        11 * (‖h x.1‖ / absk x.1 * wtd 2 F x.2 * wtd 3 F (-(x.1 + x.2))) +
        11 * (‖h x.1‖ / absk x.1 * wtd 3 F x.2 * wtd 2 F (-(x.1 + x.2))) := fun x => by
    by_cases hp0 : x.1 = 0
    · have e : h x.1 = 0 := by rw [hp0]; exact hh.mean
      simp only [e, norm_zero, zero_mul, zero_div, wtd, mul_zero, add_zero]
      exact le_rfl
    obtain ⟨h1, h2, h3⟩ := absk_triangle x.1 x.2
    have hP : 0 < absk x.1 := lt_of_lt_of_le one_pos (one_le_absk hp0)
    have hw := wb_le_one (P := absk x.1) (Q := absk x.2) (K := absk (x.1 + x.2)) hP
      (absk_nonneg _) (absk_nonneg _) (by linarith) h2 h3
    have hN : 0 ≤ ‖h x.1‖ * ‖F x.2‖ * ‖F (-(x.1 + x.2))‖ := by positivity
    have := mul_le_mul_of_nonneg_left hw hN
    refine this.trans (le_of_eq ?_)
    simp only [wtd, absk_neg]
    field_simp
    ring
  have hG' := (((t1.mul_left 8).add (t2.mul_left 8)).add (t3.mul_left 11)).add (t4.mul_left 11)
  have hnn : ∀ x : Mode × Mode, 0 ≤ ‖h x.1‖ * ‖F x.2‖ * ‖F (-(x.1 + x.2))‖ *
      wb (absk x.1) (absk x.2) (absk (x.1 + x.2)) := fun x =>
    mul_nonneg (by positivity) (wb_nonneg (absk_nonneg _) (absk_nonneg _) (absk_nonneg _))
  have hbs := Summable.of_nonneg_of_le hnn hle hG'
  have key := abs_pair_metM_add_le hr τ hh' hF' hs hs hbs e1 e1
  have hsum := hbs.tsum_le_tsum hle hG'
  rw [(((t1.mul_left 8).add (t2.mul_left 8)).add (t3.mul_left 11)).tsum_add (t4.mul_left 11),
    ((t1.mul_left 8).add (t2.mul_left 8)).tsum_add (t3.mul_left 11),
    (t1.mul_left 8).tsum_add (t2.mul_left 8), tsum_mul_left, tsum_mul_left, tsum_mul_left,
    tsum_mul_left] at hsum
  have hc := c4_pos
  have aF : ∑' k, ‖F k‖ ≤ c4 * hnorm 2 F := wiener_le hF2
  set a1 := hnorm 1 h with ha1
  set b := hnorm 2 F with hb
  set c := hnorm 3 F with hc'
  have ha0 : 0 ≤ a1 := hnorm_nonneg _ _
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have hc0 : 0 ≤ c := hnorm_nonneg _ _
  have c1 : (∑' k, ‖F k‖) * (a1 * c) ≤ c4 * b * (a1 * c) :=
    mul_le_mul_of_nonneg_right aF (mul_nonneg ha0 hc0)
  have c2 : (∑' k, ‖h k‖ / absk k) * (b * c) ≤ c4 * a1 * (b * c) :=
    mul_le_mul_of_nonneg_right hi2 (mul_nonneg hb0 hc0)
  have c3 : (∑' k, ‖h k‖ / absk k) * (c * b) ≤ c4 * a1 * (c * b) :=
    mul_le_mul_of_nonneg_right hi2 (mul_nonneg hc0 hb0)
  have hsum' : ∑' x : Mode × Mode, ‖h x.1‖ * ‖F x.2‖ * ‖F (-(x.1 + x.2))‖ *
      wb (absk x.1) (absk x.2) (absk (x.1 + x.2)) ≤ 38 * c4 * (a1 * b * c) := by
    have e3 : 38 * c4 * (a1 * b * c) = 8 * (c4 * b * (a1 * c)) + 8 * (c4 * b * (a1 * c)) +
        11 * (c4 * a1 * (b * c)) + 11 * (c4 * a1 * (c * b)) := by ring
    rw [e3]
    linarith
  have e4 : pair 2 F (X1op r τ h F) + pair 2 F (X1op r τ h F) = 2 * pair 2 F (X1op r τ h F) := by
    ring
  rw [e4, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at key
  have h4 := key.trans (mul_le_mul_of_nonneg_left hsum' (by positivity : 0 ≤ 4 / |r|))
  have hABC : 0 ≤ a1 * b * c := by positivity
  unfold cSrc
  have e5 : 2 ^ 7 * c4 * a1 * b * c / |r| = 2 ^ 7 * c4 * (a1 * b * c) / |r| := by ring
  rw [e5]
  have h5 : 2 * (2 ^ 7 * c4 * (a1 * b * c) / |r|) = 4 / |r| * (64 * c4 * (a1 * b * c)) := by ring
  have h6 : 4 / |r| * (38 * c4 * (a1 * b * c)) ≤ 4 / |r| * (64 * c4 * (a1 * b * c)) := by
    gcongr
    norm_num
  linarith

/-- Cauchy–Schwarz at the top weight: `|⟨c, A²F⟩| ≤ ‖c‖₂ ‖F‖₂` (`pair_le` loses a derivative). -/
lemma abs_pair_two_le {c F : Field} (hc : MZ 2 c) (hF : MZ 2 F) :
    (Summable fun k => sobWeight 2 k * (inner ℂ (c k) (F k)).re) ∧
      |pair 2 c F| ≤ hnorm 2 c * hnorm 2 F := by
  obtain ⟨sc, nc⟩ := wtd_l2_two hc
  obtain ⟨sF, nF⟩ := wtd_l2_two hF
  obtain ⟨hs, hb⟩ := Quant.cs_tsum_nonneg' (wtd_nonneg 2 c) (wtd_nonneg 2 F) sc sF
  rw [nc, nF] at hb
  have hle : ∀ k, ‖sobWeight 2 k * (inner ℂ (c k) (F k)).re‖ ≤ wtd 2 c k * wtd 2 F k := fun k => by
    refine (norm_pair_term_le' 2 c F k).trans (le_of_eq ?_)
    simp only [wtd, sobWeight_two, ← absk_sq]
    ring
  have hsum := Summable.of_norm_bounded hs hle
  refine ⟨hsum, ?_⟩
  have hn : Summable fun k => ‖sobWeight 2 k * (inner ℂ (c k) (F k)).re‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs
  calc |pair 2 c F| = ‖∑' k, sobWeight 2 k * (inner ℂ (c k) (F k)).re‖ := rfl
    _ ≤ ∑' k, ‖sobWeight 2 k * (inner ℂ (c k) (F k)).re‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k, wtd 2 c k * wtd 2 F k := hn.tsum_le_tsum hle hs
    _ ≤ _ := hb

/-- Additivity of the pairing at the top weight. -/
lemma pair_add_two {c F F' : Field} (hc : MZ 2 c) (hF : MZ 2 F) (hF' : MZ 2 F') :
    pair 2 c (F + F') = pair 2 c F + pair 2 c F' := by
  simp only [pair]
  rw [← (abs_pair_two_le hc hF).1.tsum_add (abs_pair_two_le hc hF').1]
  refine tsum_congr fun k => ?_
  rw [Pi.add_apply, inner_add_right, Complex.add_re, mul_add]

/-- `Q^♯_m(f,g)` has no zero mode. -/
lemma Qm_zero_mode (m : Mult) (f g : Field) : Qm m f g 0 = 0 := by
  simp [Qm, hel_zero_mode]

/-! ### E. The native differential at weight two: the near/far split and FAR -/

/-- **The near/far split of `D₂` for an `H²` direction** (`cubicD_eq_near_add_far` of
`Native/Bound.lean` needs `h ∈ H³`; the actual source is `H²` at almost every time). -/
theorem cubicD_two_eq_near_add_far {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) {F h : Field}
    (hF : MZ 3 F) (hh : MZ 2 h) :
    cubicD 2 ε r τ F h = nearD 2 ε r τ F h + farD 2 ε r τ F h := by
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  have hG : MZ 2 (PiF h) := hh.PiF'
  have hF1 : InH (2 + 1) F := by
    rw [show (2 : ℝ) + 1 = 3 by norm_num]
    exact hF.inH
  have hN : ∀ {f g : Field}, MZ 2 f → MZ 2 g → InH (2 - 1) (nearCorr ε r τ f g) := fun hf hg => by
    rw [show (2 : ℝ) - 1 = 1 by norm_num]
    exact (Qm_one_le (nearCorrM_bdd hε r τ) hf hg).1
  have hB : ∀ {f g : Field}, MZ 2 f → MZ 2 g → InH (2 - 1) (farCorr ε r τ f g) := fun hf hg => by
    rw [show (2 : ℝ) - 1 = 1 by norm_num]
    exact (Qm_one_le (farCorrM_bdd hε r τ) hf hg).1
  have hNF : MZ 2 (nearCorr ε r τ F F) :=
    ⟨(Qm_two_le (nearCorrM_bdd hε r τ) hF hF).1, Qm_zero_mode _ _ _⟩
  have hBF : MZ 2 (farCorr ε r τ F F) :=
    ⟨(Qm_two_le (farCorrM_bdd hε r τ) hF hF).1, Qm_zero_mode _ _ _⟩
  unfold cubicD nearD farD
  rw [Nat.cast_ofNat, corr_eq_near_add_far hε r τ hG hF2, corr_eq_near_add_far hε r τ hF2 hG,
    corr_eq_near_add_far hε r τ hF2 hF2, pair_add hF1 (hN hG hF2) (hB hG hF2),
    pair_add hF1 (hN hF2 hG) (hB hF2 hG), pair_add_two hG hNF hBF]
  ring

/-- `|corrSym| ≤ 1/q` on the far set. -/
lemma norm_farCorrM_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (a b c : Sgn)
    (p q : Mode) : ‖farCorrM ε r τ a b c p q‖ ≤ 1 / |r| := by
  have hr0 : 0 < |r| := abs_pos.mpr hr
  unfold farCorrM
  split_ifs with h
  · rw [norm_corrSym hε]
    refine one_div_le_one_div_of_le hr0 ?_
    have h1 : |r * Phi a b c p q| ≤ Real.sqrt (absSq (p + q) ^ 2 + (r * Phi a b c p q) ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (absSq (p + q))])
    refine le_trans ?_ h1
    rw [abs_mul]
    nlinarith [h.2]
  · simp [hr0.le]

/-- The far multiplier times `q`. -/
def farScaled (ε r τ : ℝ) : Mult := fun a b c p q => ((|r| : ℝ) : ℂ) * farCorrM ε r τ a b c p q

lemma farScaled_bdd {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) :
    (farScaled ε r τ).Bdd := fun a b c p q => by
  have hr0 : 0 < |r| := abs_pos.mpr hr
  have h := norm_farCorrM_le hε hr τ a b c p q
  rw [farScaled, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  calc |r| * ‖farCorrM ε r τ a b c p q‖ ≤ |r| * (1 / |r|) := mul_le_mul_of_nonneg_left h hr0.le
    _ = 1 := by field_simp

lemma farCorr_eq_smul {ε r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) :
    farCorr ε r τ f g = (((|r| : ℝ) : ℂ)⁻¹) • Qm (farScaled ε r τ) f g := by
  have hr0 : ((|r| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (abs_pos.mpr hr).ne'
  funext k
  rw [Pi.smul_apply]
  unfold farCorr Qm
  rw [← tsum_const_smul'']
  refine tsum_congr fun p => ?_
  simp only [Finset.smul_sum, smul_smul, farScaled]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [inv_mul_cancel_left₀ hr0]

/-- `‖farCorr f g‖₁ ≤ (4/q)(𝒜(f)‖g‖₂ + ‖f‖₂𝒜(g))`. -/
lemma farCorr_one_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {f g : Field}
    (hf : MZ 2 f) (hg : MZ 2 g) :
    hnorm 1 (farCorr ε r τ f g) ≤ 4 / |r| * (wiener f * hnorm 2 g + hnorm 2 f * wiener g) := by
  have hr0 : 0 < |r| := abs_pos.mpr hr
  rw [farCorr_eq_smul hr, hnorm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have h := (Qm_one_le (farScaled_bdd hε hr τ) hf hg).2
  have h0 : 0 ≤ |r|⁻¹ := by positivity
  refine (mul_le_mul_of_nonneg_left h h0).trans (le_of_eq ?_)
  field_simp

/-- `‖farCorr f g‖₂ ≤ (8/q)(𝒜(f)‖g‖₃ + ‖f‖₃𝒜(g))`. -/
lemma farCorr_two_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {f g : Field}
    (hf : MZ 3 f) (hg : MZ 3 g) :
    hnorm 2 (farCorr ε r τ f g) ≤ 8 / |r| * (wiener f * hnorm 3 g + hnorm 3 f * wiener g) := by
  have hr0 : 0 < |r| := abs_pos.mpr hr
  rw [farCorr_eq_smul hr, hnorm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have h := (Qm_two_le (farScaled_bdd hε hr τ) hf hg).2
  have h0 : 0 ≤ |r|⁻¹ := by positivity
  refine (mul_le_mul_of_nonneg_left h h0).trans (le_of_eq ?_)
  field_simp

/-- **The FAR native differential at weight two** (Body 18 §2 has the kernel `32/(mKq)`; at `H²`
the cyclic cancellation is not needed): `|D₂^B(F; h)| ≤ (c_far/q) ‖h‖₂ ‖F‖₂ ‖F‖₃` by (M4) and
`|corrSym| ≤ 1/q` on `|Φ| ≥ 1`.  PROVED. -/
theorem farD_two_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {F h : Field}
    (hF : MZ 3 F) (hh : MZ 2 h) :
    |farD 2 ε r τ F h| ≤ cFar / |r| * hnorm 2 h * (hnorm 2 F * hnorm 3 F) := by
  have hr0 : 0 < |r| := abs_pos.mpr hr
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  have hG : MZ 2 (PiF h) := hh.PiF'
  have hF1 : InH (2 + 1) F := by
    rw [show (2 : ℝ) + 1 = 3 by norm_num]
    exact hF.inH
  have hc := c4_pos
  set g2 := hnorm 2 (PiF h) with hg2
  set b := hnorm 2 F with hb
  set c := hnorm 3 F with hcd
  have hg0 : 0 ≤ g2 := hnorm_nonneg _ _
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have hc0 : 0 ≤ c := hnorm_nonneg _ _
  have aF : wiener F ≤ c4 * b := wiener_le hF2
  have aG : wiener (PiF h) ≤ c4 * g2 := wiener_le hG
  have aF0 := wiener_nonneg F
  have aG0 := wiener_nonneg (PiF h)
  have hN : ∀ {X : Field}, InH 1 X → |pair 2 F X| ≤ c * hnorm 1 X := fun {X} hX => by
    have hX' : InH (2 - 1) X := by
      rw [show (2 : ℝ) - 1 = 1 by norm_num]
      exact hX
    have := (pair_le hF1 hX').2
    rwa [show (2 : ℝ) + 1 = 3 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num] at this
  have hI1 : InH 1 (farCorr ε r τ (PiF h) F) := (Qm_one_le (farCorrM_bdd hε r τ) hG hF2).1
  have hI2 : InH 1 (farCorr ε r τ F (PiF h)) := (Qm_one_le (farCorrM_bdd hε r τ) hF2 hG).1
  have t1 : |pair 2 F (farCorr ε r τ (PiF h) F)| ≤ c * (8 * c4 * g2 * b / |r|) := by
    refine (hN hI1).trans (mul_le_mul_of_nonneg_left ?_ hc0)
    refine (farCorr_one_le hε hr τ hG hF2).trans ?_
    have h1 : wiener (PiF h) * b ≤ c4 * g2 * b := mul_le_mul_of_nonneg_right aG hb0
    have h2 : g2 * wiener F ≤ g2 * (c4 * b) := mul_le_mul_of_nonneg_left aF hg0
    calc 4 / |r| * (wiener (PiF h) * b + g2 * wiener F)
        ≤ 4 / |r| * (c4 * g2 * b + g2 * (c4 * b)) := by gcongr
      _ = _ := by ring
  have t2 : |pair 2 F (farCorr ε r τ F (PiF h))| ≤ c * (8 * c4 * g2 * b / |r|) := by
    refine (hN hI2).trans (mul_le_mul_of_nonneg_left ?_ hc0)
    refine (farCorr_one_le hε hr τ hF2 hG).trans ?_
    have h1 : wiener F * g2 ≤ c4 * b * g2 := mul_le_mul_of_nonneg_right aF hg0
    have h2 : b * wiener (PiF h) ≤ b * (c4 * g2) := mul_le_mul_of_nonneg_left aG hb0
    calc 4 / |r| * (wiener F * g2 + b * wiener (PiF h))
        ≤ 4 / |r| * (c4 * b * g2 + b * (c4 * g2)) := by gcongr
      _ = _ := by ring
  have hFF : MZ 2 (farCorr ε r τ F F) :=
    ⟨(Qm_two_le (farCorrM_bdd hε r τ) hF hF).1, Qm_zero_mode _ _ _⟩
  have t3 : |pair 2 (PiF h) (farCorr ε r τ F F)| ≤ g2 * (16 * c4 * b * c / |r|) := by
    refine (abs_pair_two_le hG hFF).2.trans (mul_le_mul_of_nonneg_left ?_ hg0)
    refine (farCorr_two_le hε hr τ hF hF).trans ?_
    have h1 : wiener F * c ≤ c4 * b * c := mul_le_mul_of_nonneg_right aF hc0
    calc 8 / |r| * (wiener F * c + c * wiener F) ≤ 8 / |r| * (c4 * b * c + c * (c4 * b)) := by
          have h2 : c * wiener F ≤ c * (c4 * b) := mul_le_mul_of_nonneg_left aF hc0
          gcongr
      _ = _ := by ring
  have hgh : g2 ≤ hnorm 2 h := hnorm_PiF_le hh.inH
  unfold farD
  rw [Nat.cast_ofNat]
  have hsum := (abs_add_three _ _ _).trans (add_le_add (add_le_add t1 t2) t3)
  refine hsum.trans ?_
  have e : c * (8 * c4 * g2 * b / |r|) + c * (8 * c4 * g2 * b / |r|) + g2 * (16 * c4 * b * c / |r|)
      = 32 * c4 / |r| * g2 * (b * c) := by ring
  rw [e]
  have hbc : 0 ≤ b * c := mul_nonneg hb0 hc0
  unfold cFar
  have h3 : 32 * c4 / |r| * g2 * (b * c) ≤ 2 ^ 6 * c4 / |r| * hnorm 2 h * (b * c) := by
    have h4 : 32 * c4 / |r| ≤ 2 ^ 6 * c4 / |r| := by
      gcongr
      norm_num
    exact mul_le_mul_of_nonneg_right (mul_le_mul h4 hgh hg0 (by positivity)) hbc
  exact h3

/-- **The native differential at weight two**: near part through `N(q)` (`nearD2_le`), far part
through `c_far/q`: `|D₂(F; h)| ≤ M ‖h‖₂ ‖F‖₂ ‖F‖₃`, `M = C₀ N(q) + c_far/q`. -/
theorem cubicD_two_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {F h : Field} (hF : MZ 3 F) (hFr : IsReal F)
    (hF' : PiF F = F) (hh : MZ 2 h) (hhr : IsReal h) :
    |cubicD 2 (-1) r τ F h| ≤ nM r * hnorm 2 h * (hnorm 2 F * hnorm 3 F) := by
  rw [cubicD_two_eq_near_add_far (Or.inr rfl) r τ hF hh]
  have h1 := nearD2_le (Or.inr rfl) r τ hF hFr hF' hh hhr
  have h2 := farD_two_le (Or.inr rfl) hr τ hF hh
  refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  unfold nM
  ring

/-! ### F. The proper remainders (roles 16, 17) -/

/-- **The static remainder of the weight-two cubic** (role 16, "E2 proper static 1/128"; TeX
"static coercivity … separate estimates"; Table quant-fixed "`3v`"): for real fast `F ∈ H²`,
`|E⁰₂| ≤ cStat2 (P(q) + q^{−1/2}) ‖F‖₂³`.  PROVED in `Cubic.lean`: `E⁰₂` is `⅓` of the triad sum
near (`triad_cyclic_le`, `j = 2`, `13 m K⁴/D_K`; the weights `(H², H², H²)` are `m²B²K² ≥ m²K⁴/4`
and leave `1/(m D_K) = K κ_N`, whose squared near moment is `momP`); far, `|k| |corrSym| ≤ q^{−1/2}`
and (M4), no cancellation, whence the `q^{−1/2}` (`nearP` carries only `2⁷q^{−3/4}`, which needs
`Σ_{|p|≤K}|p|⁻²`). -/
theorem cubicE_two_static_le {r : ℝ} (hr : 1 ≤ |r|) (τ : ℝ) {F : Field} (hF : MZ 2 F)
    (hFr : IsReal F) (hF' : PiF F = F) :
    |cubicE 2 (-1) r τ F| ≤
      cStat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) * hnorm 2 F ^ 3 :=
  cubicE_two_static_le_proved hr τ hF hFr hF'

/-- **Both input heats of the weight-two cubic** (role 17, "E2 both input heats 1/32"; TeX "the
two proper heat directions … are separate estimates"): for real fast `F ∈ H³`,
`|E₂_heat| ≤ cHeat2 (P(q) + q^{−1/2}) ‖F‖₂ ‖F‖₃²`.  PROVED in `Cubic.lean`: the rootings of
`E₂_heat` carry `(x_a + x_b) f₂(x_c) = Σ f₂(x_c) − f₃(x_c)` with `Σ = x_a + x_b + x_c` common to
the triad, so the cyclic cancellation applies to `f₂` and `f₃`, kernel `≲ m K⁶/D_K`; the slots
`(H², H³, H³)` with `H²` on the shortest leg are `m²K⁶`, which leaves the proper kernel
`1/(m D_K)`. -/
theorem cubicHeat2_le {r : ℝ} (hr : 1 ≤ |r|) (τ : ℝ) {F : Field} (hF : MZ 3 F)
    (hFr : IsReal F) (hF' : PiF F = F) :
    |cubicHeat2 r τ F| ≤
      cHeat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) * hnorm 2 F * hnorm 3 F ^ 2 :=
  cubicHeat2_le_proved hr τ hF hFr hF'

/-! ### G. Norms on the piece -/

/-- The helical coefficient of the corrector is at most `2/L` (`Regimes/Continuation.lean` has it
privately). -/
private lemma norm_coef_le_div' (x y z L t : ℝ) (hL : 1 ≤ L) (ht : 0 ≤ t) :
    ‖(Complex.exp (-(Complex.I * (x : ℂ))) -
        Complex.exp (-((L * t : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (y : ℂ)))) /
      ((L : ℂ) - Complex.I * (z : ℂ))‖ ≤ 2 / L := by
  rw [norm_div]
  have hden : L ≤ ‖(L : ℂ) - Complex.I * (z : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (Complex.re_le_norm _)
    simp
  have he1 : ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have he2 : ‖Complex.exp (-(Complex.I * (y : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have he3 : ‖Complex.exp (-((L * t : ℝ) : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hnum : ‖Complex.exp (-(Complex.I * (x : ℂ))) -
      Complex.exp (-((L * t : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (y : ℂ)))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, he1, he2]
    linarith
  exact div_le_div₀ (by norm_num) hnum (by linarith) hden

/-- Mode-wise smoothing of the corrector: `‖ψ(t)_k‖ ≤ 4 ‖g_k‖ / |k|²`. -/
private lemma norm_psi_le_div' (r : ℝ) (g : Field) {t : ℝ} (ht : 0 ≤ t) {k : Mode}
    (hk0 : k ≠ 0) : ‖psi r 0 g t k‖ ≤ 4 * ‖g k‖ / absSq k := by
  have h1 : (1 : ℝ) ≤ absSq k := one_le_absSq hk0
  unfold psi
  split_ifs with hk
  · rw [norm_zero]
    positivity
  · refine (norm_sum_le _ _).trans ?_
    rw [Fintype.sum_bool]
    have hterm : ∀ a : Sgn, ‖((Complex.exp (-(Complex.I * (r * (t + 0) * lam a k : ℝ))) -
        Complex.exp (-(absSq k * t : ℝ)) * Complex.exp (-(Complex.I * (r * 0 * lam a k : ℝ)))) /
          ((absSq k : ℂ) - Complex.I * (r * lam a k : ℝ))) • hel a k (g k)‖ ≤
          2 / absSq k * ‖g k‖ := by
      intro a
      rw [norm_smul]
      exact mul_le_mul (norm_coef_le_div' _ _ _ _ _ h1 ht) (norm_hel_le a k (g k))
        (norm_nonneg _) (by positivity)
    have e : 4 * ‖g k‖ / absSq k = 2 / absSq k * ‖g k‖ + 2 / absSq k * ‖g k‖ := by ring
    rw [e]
    linarith [hterm true, hterm false]

/-- `‖ψ‖₃ ≤ 4φ` at every time (parabolic smoothing of the explicit modes). -/
theorem psi_three_le (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) :
    InH 3 (psi r 0 g u) ∧ hnorm 3 (psi r 0 g u) ≤ 4 * φ := by
  have hI := inH3_psi (r := r) h.force_adm hu
  refine ⟨hI, ?_⟩
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hle : ∀ k, sobWeight 3 k * ‖psi r 0 g u k‖ ^ 2 ≤ 16 * (sobWeight 2 k * ‖g k‖ ^ 2) := by
    intro k
    by_cases hk : k = 0
    · simp [sobWeight, hk]
    have h1 : (1 : ℝ) ≤ absSq k := one_le_absSq hk
    rw [sobWeight_two, sobWeight_three]
    have hp := norm_psi_le_div' r g hu hk
    have hp2 : ‖psi r 0 g u k‖ ^ 2 ≤ (4 * ‖g k‖ / absSq k) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hp 2
    have hA : 0 < absSq k := by linarith
    calc absSq k ^ 3 * ‖psi r 0 g u k‖ ^ 2 ≤ absSq k ^ 3 * (4 * ‖g k‖ / absSq k) ^ 2 :=
          mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ = 16 * (absSq k * ‖g k‖ ^ 2) := by field_simp; ring
      _ ≤ 16 * (absSq k ^ 2 * ‖g k‖ ^ 2) := by
          gcongr
          nlinarith
  have hsum : ∑' k, sobWeight 3 k * ‖psi r 0 g u k‖ ^ 2 ≤ 16 * ∑' k, sobWeight 2 k * ‖g k‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact hI.tsum_le_tsum hle (h.force_adm.inH.mul_left 16)
  have h4 : hnorm 3 (psi r 0 g u) ≤ 4 * hnorm 2 g := by
    unfold hnorm
    refine (Real.sqrt_le_sqrt hsum).trans (le_of_eq ?_)
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  linarith [h.force_le]

/-- The total fields at a time of the piece, from the caps and `‖ψ‖₂ ≤ 1`. -/
lemma piece_caps (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t : ℝ}
    (hon : OnPrefix caps r g y s t) {u : ℝ} (hu : u ∈ Icc s t) (hs : 0 ≤ s)
    (huT : ENNReal.ofReal u < Ty) (hε : hnorm 2 (psi r 0 g u) ≤ 1) :
    hnorm 2 (actual r g y u) ≤ cp caps.BS + cp caps.yF ∧
      wiener (actual r g y u) ≤ cp caps.WS + c4 * cp caps.yF ∧
      hnorm 2 (y u) ≤ cp caps.BS + cp caps.yF + 1 ∧ wiener (y u) ≤ wyCap caps := by
  have hu0 : 0 ≤ u := hs.trans hu.1
  have hx := actual_adm h hu0 huT
  have hψ := psi_adm (r := r) (t₀ := 0) h.force_adm u hu0
  obtain ⟨-, cF2, -, cS2, cW⟩ := hon.1 u hu
  have hc4 := c4_pos
  have hxSF := PiS_add_PiF (actual r g y u)
  have hyx : y u = actual r g y u + psi r 0 g u := by simp [actual]
  have hx2 : hnorm 2 (actual r g y u) ≤ cp caps.BS + cp caps.yF := by
    conv_lhs => rw [← hxSF]
    refine (hnorm_add_le hx.PiS.inH hx.PiF.inH).trans ?_
    exact add_le_add (cS2.trans (le_cp _)) (cF2.trans (le_cp _))
  have hxw : wiener (actual r g y u) ≤ cp caps.WS + c4 * cp caps.yF := by
    refine (wiener_actual_le h hu0 huT).trans ?_
    exact add_le_add (cW.trans (le_cp _))
      (mul_le_mul_of_nonneg_left (cF2.trans (le_cp _)) hc4.le)
  refine ⟨hx2, hxw, ?_, ?_⟩
  · rw [hyx]
    exact (hnorm_add_le hx.inH hψ.inH).trans (add_le_add hx2 hε)
  · rw [hyx]
    refine (wiener_add_le (summable_wiener hx.inH) (summable_wiener hψ.inH)).trans ?_
    have h1 : wiener (psi r 0 g u) ≤ c4 :=
      (wiener_le hψ.mz).trans ((mul_le_mul_of_nonneg_left hε hc4.le).trans_eq (mul_one c4))
    unfold wyCap
    linarith

/-- `H_ψ ∈ H¹`, `‖H_ψ‖₁ ≤ h₁ = 32(1+c₄) φ (B_S + y + W_S + 1)/q` on the piece, for `2φ ≤ q`
((M4), `H_ψ = Q(x,ψ) + Q(ψ,x) + Q(ψ,ψ)`). -/
theorem Hpsi_one_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {caps : Caps} {s t : ℝ}
    (hon : OnPrefix caps r g y s t) {u : ℝ} (hu : u ∈ Icc s t) (hs : 0 ≤ s)
    (huT : ENNReal.ofReal u < Ty) (hq : 2 * φ ≤ |r|) :
    InH 1 (Hpsi r g y u) ∧ hnorm 1 (Hpsi r g y u) ≤ hPsiC φ caps r := by
  have hu0 : 0 ≤ u := hs.trans hu.1
  have hr0 : 0 < |r| := abs_pos.mpr hr
  have hx := actual_adm h hu0 huT
  have hψ := psi_adm (r := r) (t₀ := 0) h.force_adm u hu0
  obtain ⟨-, hψle⟩ := psi_two_le h hr hu0
  have hε : hnorm 2 (psi r 0 g u) ≤ 1 :=
    hψle.trans ((div_le_one hr0).2 hq)
  obtain ⟨hx2, hxw, -, -⟩ := piece_caps h hon hu hs huT hε
  obtain ⟨i1, b1⟩ := Qm_one_le (phaseM_bdd (r * u)) hx.mz hψ.mz
  obtain ⟨i2, b2⟩ := Qm_one_le (phaseM_bdd (r * u)) hψ.mz hx.mz
  obtain ⟨i3, b3⟩ := Qm_one_le (phaseM_bdd (r * u)) hψ.mz hψ.mz
  have e := Hpsi_eq h hu0 huT
  have hI12 : InH 1 (Qphase (r * u) (actual r g y u) (psi r 0 g u) +
      Qphase (r * u) (psi r 0 g u) (actual r g y u)) := i1.add i2
  refine ⟨by rw [e]; exact hI12.add i3, ?_⟩
  rw [e]
  refine (hnorm_add_le hI12 i3).trans ?_
  have hsum := add_le_add ((hnorm_add_le i1 i2).trans (add_le_add b1 b2)) b3
  refine hsum.trans ?_
  have hc := c4_pos
  set E := hnorm 2 (psi r 0 g u) with hE
  have hE0 : 0 ≤ E := hnorm_nonneg _ _
  have aψ : wiener (psi r 0 g u) ≤ c4 * E := wiener_le hψ.mz
  have aψ0 := wiener_nonneg (psi r 0 g u)
  set W := cp caps.WS
  set Y := cp caps.yF
  set B := cp caps.BS
  have hW : 0 ≤ W := cp_nonneg _
  have hY : 0 ≤ Y := cp_nonneg _
  have hB : 0 ≤ B := cp_nonneg _
  have t1 : wiener (actual r g y u) * E ≤ (W + c4 * Y) * E := mul_le_mul_of_nonneg_right hxw hE0
  have t2 : hnorm 2 (actual r g y u) * wiener (psi r 0 g u) ≤ (B + Y) * (c4 * E) :=
    mul_le_mul hx2 aψ aψ0 (by positivity)
  have t3 : E * wiener (actual r g y u) ≤ E * (W + c4 * Y) := mul_le_mul_of_nonneg_left hxw hE0
  have t4 : wiener (psi r 0 g u) * hnorm 2 (actual r g y u) ≤ c4 * E * (B + Y) :=
    mul_le_mul aψ hx2 (hnorm_nonneg _ _) (by positivity)
  have t5 : wiener (psi r 0 g u) * E ≤ c4 * E * E := mul_le_mul_of_nonneg_right aψ hE0
  have t6 : E * wiener (psi r 0 g u) ≤ E * (c4 * E) := mul_le_mul_of_nonneg_left aψ hE0
  have t7 : c4 * E * E ≤ c4 * E := by
    have := mul_le_mul_of_nonneg_left hε (mul_nonneg hc.le hE0)
    linarith
  have hT : 0 ≤ B + Y + W + 1 := by positivity
  have hm : 4 * (wiener (actual r g y u) * E + hnorm 2 (actual r g y u) * wiener (psi r 0 g u)) +
      4 * (wiener (psi r 0 g u) * hnorm 2 (actual r g y u) + E * wiener (actual r g y u)) +
      4 * (wiener (psi r 0 g u) * E + E * wiener (psi r 0 g u)) ≤
      16 * (1 + c4) * E * (B + Y + W + 1) := by
    have e2 : 16 * (1 + c4) * E * (B + Y + W + 1) =
        4 * ((W + c4 * Y) * E + (B + Y) * (c4 * E)) +
        4 * (c4 * E * (B + Y) + E * (W + c4 * Y)) + 4 * (c4 * E + c4 * E) +
        (16 * E * B + 16 * E * Y + 8 * E * W + 16 * E + 8 * c4 * E * B + 16 * c4 * E * W +
          8 * c4 * E) := by ring
    have hrest : 0 ≤ 16 * E * B + 16 * E * Y + 8 * E * W + 16 * E + 8 * c4 * E * B +
        16 * c4 * E * W + 8 * c4 * E := by positivity
    rw [e2]
    linarith
  refine hm.trans ?_
  unfold hPsiC
  have e3 : 32 * (1 + c4) * φ * (B + Y + W + 1) / |r| =
      16 * (1 + c4) * (2 * φ / |r|) * (B + Y + W + 1) := by ring
  rw [e3]
  have h4 : 0 ≤ 16 * (1 + c4) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hψle h4) hT

/-- The slow source on the piece: `slowNL ∈ H¹` (mean zero, slow), `‖slowNL‖₁ ≤ hSrc`. -/
theorem slowNL_one_le' (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t : ℝ}
    (hon : OnPrefix caps r g y s t) {u : ℝ} (hu : u ∈ Icc s t) (hs : 0 ≤ s)
    (huT : ENNReal.ofReal u < Ty) (hε : hnorm 2 (psi r 0 g u) ≤ 1) :
    MZ 1 (slowNL r g y u) ∧ hnorm 1 (slowNL r g y u) ≤ hSrc φ caps := by
  have hu0 : 0 ≤ u := hs.trans hu.1
  have hy := h.sol.adm u hu0 huT
  obtain ⟨hJ, hR⟩ := Qm_one_le (phaseM_bdd (r * u)) hy.mz hy.mz
  have hg1 : InH 1 g := h.force_adm.inH.mono (by norm_num)
  have hI : InH 1 (slowNL r g y u) := hJ.PiS.neg.add hg1.PiS
  have hQ0 : Qphase (r * u) (y u) (y u) 0 = 0 := Qm_zero_mode _ _ _
  refine ⟨⟨hI, by simp [slowNL, PiS, h.force_adm.mean, hQ0]⟩, ?_⟩
  obtain ⟨-, -, hy2, hyw⟩ := piece_caps h hon hu hs huT hε
  have hg : hnorm 1 (PiS g) ≤ φ :=
    (hnorm_PiS_le hg1).trans ((hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le)
  have h2 : wiener (y u) * hnorm 2 (y u) ≤ wyCap caps * (cp caps.BS + cp caps.yF + 1) :=
    mul_le_mul hyw hy2 (hnorm_nonneg _ _) (wyCap_nonneg caps)
  have h1 : hnorm 1 (PiS (Qm (phaseM (r * u)) (y u) (y u))) ≤
      8 * (wiener (y u) * hnorm 2 (y u)) :=
    (hnorm_PiS_le hJ).trans (hR.trans (le_of_eq (by ring)))
  have e : hSrc φ caps = 8 * (wyCap caps * (cp caps.BS + cp caps.yF + 1)) + φ := by
    unfold hSrc wyCap
    ring
  rw [e]
  unfold slowNL
  refine (hnorm_add_le hJ.PiS.neg hg1.PiS).trans ?_
  rw [hnorm_neg]
  have h3 : hnorm 1 (PiS (Qphase (r * u) (y u) (y u))) ≤ 8 * (wiener (y u) * hnorm 2 (y u)) := h1
  linarith

/-- `H_ψ ∈ H²` at a time when `S, F ∈ H³`:
`‖H_ψ‖₂ ≤ 16 c₄ e (c_F + c_S) + h2L0` with `e = ‖ψ‖₂ ≤ 1`, `‖ψ‖₃ ≤ 4φ`. -/
theorem Hpsi_two_le (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t : ℝ}
    (hon : OnPrefix caps r g y s t) {u : ℝ} (hu : u ∈ Icc s t) (hs : 0 ≤ s)
    (huT : ENNReal.ofReal u < Ty) (hε : hnorm 2 (psi r 0 g u) ≤ 1)
    (hF3 : InH 3 (PiF (actual r g y u))) (hS3 : InH 3 (PiS (actual r g y u))) :
    InH 2 (Hpsi r g y u) ∧ hnorm 2 (Hpsi r g y u) ≤
      16 * c4 * hnorm 2 (psi r 0 g u) * (fastNorm 3 r g y u + hnorm 3 (PiS (actual r g y u))) +
        h2L0 φ caps := by
  have hu0 : 0 ≤ u := hs.trans hu.1
  have hx := actual_adm h hu0 huT
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  obtain ⟨hψ3, hψ3le⟩ := psi_three_le h hu0
  have hψa := psi_adm (r := r) (t₀ := 0) h.force_adm u hu0
  have hxSF := PiS_add_PiF (actual r g y u)
  have hx3I : InH 3 (actual r g y u) := by
    rw [← hxSF]
    exact hS3.add hF3
  have hx3 : MZ 3 (actual r g y u) := ⟨hx3I, hx.mean⟩
  have hψm : MZ 3 (psi r 0 g u) := ⟨hψ3, hψa.mean⟩
  have hxn : hnorm 3 (actual r g y u) ≤ fastNorm 3 r g y u + hnorm 3 (PiS (actual r g y u)) := by
    conv_lhs => rw [← hxSF]
    refine (hnorm_add_le hS3 hF3).trans (le_of_eq ?_)
    unfold fastNorm
    ring
  obtain ⟨i1, b1⟩ := Qm_two_le (phaseM_bdd (r * u)) hx3 hψm
  obtain ⟨i2, b2⟩ := Qm_two_le (phaseM_bdd (r * u)) hψm hx3
  obtain ⟨i3, b3⟩ := Qm_two_le (phaseM_bdd (r * u)) hψm hψm
  have e := Hpsi_eq h hu0 huT
  have hI12 : InH 2 (Qphase (r * u) (actual r g y u) (psi r 0 g u) +
      Qphase (r * u) (psi r 0 g u) (actual r g y u)) := i1.add i2
  refine ⟨by rw [e]; exact hI12.add i3, ?_⟩
  rw [e]
  refine (hnorm_add_le hI12 i3).trans ?_
  have hsum := add_le_add ((hnorm_add_le i1 i2).trans (add_le_add b1 b2)) b3
  refine hsum.trans ?_
  obtain ⟨-, hxw, -, -⟩ := piece_caps h hon hu hs huT hε
  have hc := c4_pos
  set E := hnorm 2 (psi r 0 g u) with hE
  set P3 := hnorm 3 (psi r 0 g u) with hP3
  set X3 := hnorm 3 (actual r g y u) with hX3
  set C := fastNorm 3 r g y u + hnorm 3 (PiS (actual r g y u)) with hC
  have hE0 : 0 ≤ E := hnorm_nonneg _ _
  have hP30 : 0 ≤ P3 := hnorm_nonneg _ _
  have hX30 : 0 ≤ X3 := hnorm_nonneg _ _
  have aψ : wiener (psi r 0 g u) ≤ c4 * E := wiener_le hψa.mz
  have aψ0 := wiener_nonneg (psi r 0 g u)
  have aX0 := wiener_nonneg (actual r g y u)
  set Wx := cp caps.WS + c4 * cp caps.yF with hWx
  have hWx0 : 0 ≤ Wx := aX0.trans hxw
  have t1 : wiener (actual r g y u) * P3 ≤ Wx * P3 := mul_le_mul_of_nonneg_right hxw hP30
  have t2 : X3 * wiener (psi r 0 g u) ≤ C * (c4 * E) :=
    mul_le_mul hxn aψ aψ0 (hX30.trans hxn)
  have t3 : wiener (psi r 0 g u) * X3 ≤ c4 * E * C :=
    mul_le_mul aψ hxn hX30 (by positivity)
  have t4 : P3 * wiener (actual r g y u) ≤ P3 * Wx := mul_le_mul_of_nonneg_left hxw hP30
  have t5 : wiener (psi r 0 g u) * P3 ≤ c4 * E * P3 := mul_le_mul_of_nonneg_right aψ hP30
  have t6 : P3 * wiener (psi r 0 g u) ≤ P3 * (c4 * E) := mul_le_mul_of_nonneg_left aψ hP30
  have hsum2 : 8 * (wiener (actual r g y u) * P3 + X3 * wiener (psi r 0 g u)) +
      8 * (wiener (psi r 0 g u) * X3 + P3 * wiener (actual r g y u)) +
      8 * (wiener (psi r 0 g u) * P3 + P3 * wiener (psi r 0 g u)) ≤
      16 * c4 * E * C + 16 * P3 * (Wx + c4 * E) := by
    have e2 : 16 * c4 * E * C + 16 * P3 * (Wx + c4 * E) =
        8 * (Wx * P3 + C * (c4 * E)) + 8 * (c4 * E * C + P3 * Wx) +
        8 * (c4 * E * P3 + P3 * (c4 * E)) := by ring
    rw [e2]
    linarith
  refine hsum2.trans ?_
  have hL : 16 * P3 * (Wx + c4 * E) ≤ h2L0 φ caps := by
    have h1 : Wx + c4 * E ≤ wyCap caps := by
      have : c4 * E ≤ c4 := (mul_le_mul_of_nonneg_left hε hc.le).trans_eq (mul_one c4)
      rw [hWx]
      unfold wyCap
      linarith
    have hW0 := wyCap_nonneg caps
    have h2 : 16 * P3 * (Wx + c4 * E) ≤ 16 * (4 * φ) * wyCap caps :=
      mul_le_mul (mul_le_mul_of_nonneg_left hψ3le (by norm_num)) h1 (by positivity) (by positivity)
    unfold h2L0
    nlinarith [mul_nonneg hφ hc.le, mul_nonneg hφ hW0]
  linarith

/-- **The `H²` norm of the fast source at a time when `S, F ∈ H³`** (TeX `‖Q(S+F,S+F)‖₂`, spec
"the mixed source"): `Π_F Q(y,y) = 2Π_F Q(S,F) + Π_F Q(F,F) + Π_F H_ψ`, (M4) at `σ = 3` for the
mixed product `‖Q(S,F)‖₂ ≤ 8(𝒜(S) c_F + c_S 𝒜(F))`: the high mixed term carries the actual slow
`H³` norm (TeX "its actual `H³` slow time slot"). -/
theorem fastNL_two_le (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t : ℝ}
    (hon : OnPrefix caps r g y s t) {u : ℝ} (hu : u ∈ Icc s t) (hs : 0 ≤ s)
    (huT : ENNReal.ofReal u < Ty) (hε : hnorm 2 (psi r 0 g u) ≤ 1)
    (hF3 : InH 3 (PiF (actual r g y u))) (hS3 : InH 3 (PiS (actual r g y u))) :
    MZ 2 (fastNL r g y u) ∧ hnorm 2 (fastNL r g y u) ≤
      cQ2 * Real.sqrt (fastNorm 1 r g y u * fastNorm 2 r g y u) * fastNorm 3 r g y u +
      16 * (cp caps.WS * fastNorm 3 r g y u + cI *
        Real.sqrt (fastNorm 1 r g y u * fastNorm 2 r g y u) * hnorm 3 (PiS (actual r g y u))) +
      (16 * c4 * hnorm 2 (psi r 0 g u) *
        (fastNorm 3 r g y u + hnorm 3 (PiS (actual r g y u))) + h2L0 φ caps) := by
  have hu0 : 0 ≤ u := hs.trans hu.1
  have hx := actual_adm h hu0 huT
  have hy := h.sol.adm u hu0 huT
  obtain ⟨cF1, cF2, cS1, cS2, cW⟩ := hon.1 u hu
  set S := PiS (actual r g y u) with hSdef
  set F := PiF (actual r g y u) with hFdef
  have hS : Adm 2 S := hx.PiS
  have hF : Adm 2 F := hx.PiF
  have hSm3 : MZ 3 S := ⟨hS3, hS.mean⟩
  have hFm3 : MZ 3 F := ⟨hF3, hF.mean⟩
  have hS' : PiS S = S := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hSdef, PiS, hk]
  have hF' : PiF F = F := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hFdef, PiF, hk]
  have hM := majorized_Qphase (r * u)
  have hx' : actual r g y u = S + F := (PiS_add_PiF _).symm
  have hsum : MZ 2 (S + F) := by rw [← hx']; exact hx.mz
  have hcomm : Qphase (r * u) F S = Qphase (r * u) S F :=
    Qm_comm_of_symm (phaseM_symm _) hF.mz hS.mz
  have hsplit : Qphase (r * u) (actual r g y u) (actual r g y u) =
      Qphase (r * u) S S + Qphase (r * u) S F + Qphase (r * u) S F + Qphase (r * u) F F := by
    conv_lhs => rw [hx']
    rw [hM.add_left 0 _ _ _ hS.mz hF.mz hsum, hM.add_right 0 _ _ _ hS.mz hS.mz hF.mz,
      hM.add_right 0 _ _ _ hF.mz hS.mz hF.mz, hcomm]
    abel
  have hyy : Qphase (r * u) (y u) (y u) =
      Qphase (r * u) (actual r g y u) (actual r g y u) + Hpsi r g y u := by simp [Hpsi]
  obtain ⟨hJSF, hRSF⟩ := Qm_two_le (phaseM_bdd (r * u)) hSm3 hFm3
  obtain ⟨hJFF, -⟩ := Qm_two_le (phaseM_bdd (r * u)) hFm3 hFm3
  obtain ⟨hJH, hRH⟩ := Hpsi_two_le h hon hu hs huT hε hF3 hS3
  have hSS0 : PiF (Qphase (r * u) S S) = 0 := by
    funext k
    by_cases hk : k 2 = 0
    · simp [PiF, hk]
    · simp only [PiF, hk, ite_false, Pi.zero_apply]
      exact Qphase_slow_slow (r * u) hS' hk
  have ePiF : PiF (Qphase (r * u) (y u) (y u)) = PiF (Qphase (r * u) S F) +
      PiF (Qphase (r * u) S F) + PiF (Qphase (r * u) F F) + PiF (Hpsi r g y u) := by
    rw [hyy, hsplit]
    have e : ∀ A B : Field, PiF (A + B) = PiF A + PiF B := fun A B => by
      funext k; by_cases hk : k 2 = 0 <;> simp [PiF, hk]
    rw [e, e, e, e, hSS0, zero_add]
  have hI1 : InH 2 (PiF (Qphase (r * u) S F)) := hJSF.PiF
  have hI2 : InH 2 (PiF (Qphase (r * u) F F)) := hJFF.PiF
  have hI3 : InH 2 (PiF (Hpsi r g y u)) := hJH.PiF
  have hIall : InH 2 (PiF (Qphase (r * u) (y u) (y u))) := by
    rw [ePiF]
    exact ((hI1.add hI1).add hI2).add hI3
  refine ⟨⟨hIall.neg, by simp [fastNL, PiF]⟩, ?_⟩
  set a := fastNorm 1 r g y u with hadef
  set b := fastNorm 2 r g y u with hbdef
  set c := fastNorm 3 r g y u with hcdef
  have eab : a * b = hnorm 1 F * hnorm 2 F := rfl
  have hmix : hnorm 2 (PiF (Qphase (r * u) S F)) ≤
      8 * (cp caps.WS * c + cI * Real.sqrt (a * b) * hnorm 3 S) := by
    refine (hnorm_PiF_le hJSF).trans (hRSF.trans ?_)
    have h1 : wiener S ≤ cp caps.WS := cW.trans (le_cp _)
    have h3 := wiener_le_cI hF.mz
    have hc0 : 0 ≤ c := hnorm_nonneg _ _
    have hS30 : 0 ≤ hnorm 3 S := hnorm_nonneg _ _
    have t1 : wiener S * hnorm 3 F ≤ cp caps.WS * c := mul_le_mul_of_nonneg_right h1 hc0
    have t2 : hnorm 3 S * wiener F ≤ hnorm 3 S * (cI * Real.sqrt (hnorm 1 F * hnorm 2 F)) :=
      mul_le_mul_of_nonneg_left h3 hS30
    rw [eab]
    nlinarith
  have hff : hnorm 2 (PiF (Qphase (r * u) F F)) ≤ cQ2 * Real.sqrt (a * b) * c :=
    hnorm_two_Qphase_le (r * u) hFm3
  have hH2 : hnorm 2 (PiF (Hpsi r g y u)) ≤ hnorm 2 (Hpsi r g y u) := hnorm_PiF_le hJH
  have h12 := hnorm_add_le hI1 hI1
  have h123 := hnorm_add_le (hI1.add hI1) hI2
  have h1234 := hnorm_add_le ((hI1.add hI1).add hI2) hI3
  unfold fastNL
  rw [hnorm_neg, ePiF]
  have hRH' : hnorm 2 (Hpsi r g y u) ≤ 16 * c4 * hnorm 2 (psi r 0 g u) * (c + hnorm 3 S) +
      h2L0 φ caps := hRH
  linarith

/-- The transform of the TeX: `c_S ≤ c_y + (16 c₄ b_F/q) c_F`
(`‖R_S‖₃ ≤ (16/q) 𝒜(F) c_F`, `hnorm_kinN_le_of_one_le`; TeX "`c_S ≤ c_y + c_F/128`"). -/
theorem slow_three_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (PiF (actual r g y u)))
    (hy3 : InH 3 (corrSlow r g y u)) :
    hnorm 3 (PiS (actual r g y u)) ≤ hnorm 3 (corrSlow r g y u) +
      16 * c4 / |r| * fastNorm 2 r g y u * fastNorm 3 r g y u := by
  have hx := actual_adm h hu huT
  set F := PiF (actual r g y u) with hFdef
  have hF : Adm 2 F := hx.PiF
  have hFm3 : MZ 3 F := ⟨hF3, hF.mean⟩
  have hF1 : Summable fun k => ‖F k‖ := summable_wiener hF.inH
  obtain ⟨hI, hle⟩ := hnorm_kinN_le_of_one_le (τ := r * u) hr (σ := 3) (by norm_num) hFm3 hFm3
    hF1 hF1
  have e8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [e8] at hle
  have e : PiS (actual r g y u) = corrSlow r g y u - slowCorr r g y u := by
    simp [corrSlow]
  have hr0 : 0 < |r| := abs_pos.mpr hr
  have hw : wiener F ≤ c4 * hnorm 2 F := wiener_le hF.mz
  have hc := hnorm_nonneg 3 F
  rw [e]
  refine (hnorm_sub_le hy3 hI).trans ?_
  refine add_le_add le_rfl (hle.trans ?_)
  have e2 : 8 / |r| * (wiener F * hnorm 3 F + hnorm 3 F * wiener F) =
      16 / |r| * (wiener F * hnorm 3 F) := by ring
  rw [e2]
  have e3 : 16 * c4 / |r| * fastNorm 2 r g y u * fastNorm 3 r g y u =
      16 / |r| * (c4 * hnorm 2 F * hnorm 3 F) := by
    unfold fastNorm
    ring
  rw [e3]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hc) (by positivity)

/-! ### H. The slow `H³` price (TeX eq. quant-short-slow) -/

/-- **The slow `H³` price on a piece of length `≤ 2`** (TeX eq. quant-short-slow, "integration from
its true `H²` left trace gives the independent slow `H³` price"): `∫ₛᵗ ‖y_S‖₃² ≤ h2Price`.  From the
laws `corr_horiz_h2_law`, `corr_vert_h2_law` of `Slow/Barrier.lean` (T3b, T3c: the commutator
estimates, whence no `W_S² B_S²` term) and the residual budget `corrRes_budget`.  The free parameter
`A₃ = A_h + μ^{3/2}` of the vertical law balances `A₃² ∫ b_ζ²` (degree `7`) against
`B_h⁴ A_ζ²/A₃⁴` (degree `6`). -/
theorem slow_price (h : ActualSol μ φ r g y Ty) (hr : 1 ≤ |r|) (hμ : 0 ≤ μ) {caps : Caps} {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 2)
    (hon : OnPrefix caps r g y s t) (hB : budgetPoly φ caps ≤ |r|)
    (hsm : 32 * c4 * cp caps.yF ^ 2 ≤ |r|) :
    IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume s t ∧
      ∫ u in s..t, hnorm 3 (corrSlow r g y u) ^ 2 ≤ h2Price μ φ caps := by
  have hr0' : 0 < |r| := by linarith
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr0'; exact lt_irrefl _ hr0'
  have ht0 : 0 ≤ t := hs.trans hst
  have hmem : ∀ u ∈ Icc s t, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hs.trans hu.1, lt_lifespan hu.2 ht⟩
  have hc4 := c4_pos
  have hρ : ∀ u ∈ Icc s t, hnorm 2 (slowCorr r g y u) ≤ 1 / 4 := by
    intro u hu
    refine ((hnorm_slowCorr_le h hr0 (hmem u hu).1 (hmem u hu).2).2).trans ?_
    have hb : fastNorm 2 r g y u ≤ cp caps.yF := ((hon.1 u hu).2.1).trans (le_cp _)
    have hb0 : 0 ≤ fastNorm 2 r g y u := hnorm_nonneg _ _
    have h2 := pow_le_pow_left₀ hb0 hb 2
    rw [div_mul_eq_mul_div, div_le_iff₀ hr0']
    nlinarith
  set Aq := cp caps.AH + 1 with hAq
  set Bq := cp caps.BH + 1 with hBq
  set Zq := cp caps.AS + 1 with hZq
  set Bz := cp caps.BS + 1 with hBz
  set A3 := h2A3 μ caps with hA3
  have hAq0 : 0 < Aq := by have := cp_nonneg caps.AH; rw [hAq]; linarith
  have hBq0 : 0 < Bq := by have := cp_nonneg caps.BH; rw [hBq]; linarith
  have hZq0 : 0 < Zq := by have := cp_nonneg caps.AS; rw [hZq]; linarith
  have hBz0 : 0 < Bz := by have := cp_nonneg caps.BS; rw [hBz]; linarith
  have hA30 : 0 < A3 := h2A3_pos hμ caps
  have hAqA3 : Aq ≤ A3 := by
    have := Real.rpow_nonneg hμ (3 / 2 : ℝ)
    rw [hAq, hA3]
    unfold h2A3
    linarith
  have haH : ∀ u ∈ Icc s t, hnorm 1 (PiH (corrSlow r g y u)) ≤ Aq := fun u hu => by
    have h1 := (horizNorm_le_corr h hr0 (hmem u hu).1 (hmem u hu).2 (σ := 1) (by norm_num)).2
    have h2 := (hon.2.2.2 u hu).2.1.trans (le_cp _)
    have h3 := hρ u hu
    rw [hAq]
    linarith
  have hbH : ∀ u ∈ Icc s t, hnorm 2 (PiH (corrSlow r g y u)) ≤ Bq := fun u hu => by
    have h1 := (horizNorm_le_corr h hr0 (hmem u hu).1 (hmem u hu).2 (σ := 2) le_rfl).2
    have h2 := (hon.2.2.2 u hu).2.2.trans (le_cp _)
    have h3 := hρ u hu
    rw [hBq]
    linarith
  have haZ : ∀ u ∈ Icc s t, hnorm 1 (PiV (corrSlow r g y u)) ≤ Zq := fun u hu => by
    have hz := corrSlow_adm h hr0 (hmem u hu).1 (hmem u hu).2
    have h0 : hnorm 1 (PiV (corrSlow r g y u)) ≤ hnorm 1 (corrSlow r g y u) :=
      hnorm_PiV_le' (hz.inH.mono (by norm_num))
    have h1 := (slowNorm_le_corr h hr0 (hmem u hu).1 (hmem u hu).2 (σ := 1) (by norm_num)).2
    have h2 := (hon.1 u hu).2.2.1.trans (le_cp _)
    have h3 := hρ u hu
    rw [hZq]
    linarith
  have hbZ : ∀ u ∈ Icc s t, hnorm 2 (PiV (corrSlow r g y u)) ≤
      slowNorm 2 r g y u + 1 / 4 := fun u hu => by
    have hz := corrSlow_adm h hr0 (hmem u hu).1 (hmem u hu).2
    have h0 : hnorm 2 (PiV (corrSlow r g y u)) ≤ hnorm 2 (corrSlow r g y u) :=
      hnorm_PiV_le' hz.inH
    have h1 := (slowNorm_le_corr h hr0 (hmem u hu).1 (hmem u hu).2 (σ := 2) le_rfl).2
    have h3 := hρ u hu
    linarith
  have hE := corrRes_budget h hs hst ht hlen hB hon
  have hresI := intervalIntegrable_corrRes_sq h hr0 hs hst ht
  -- the two laws
  have lawH := corr_horiz_h2_law h hr0 hs hst ht
  have lawV := corr_vert_h2_law h hr0 hs hst ht (Ah := A3) (Bh := Bq) (Aζ := Zq) hA30 hBq0
    hZq0.le (fun u hu => (haH u hu).trans hAqA3) hbH haZ
  -- the heat pairs and the integrability
  have hPy := (heatPair_corrSlow h hr0 (σ := 2) (Or.inr (Or.inr rfl)) ht0 ht).mono hs le_rfl
  have hPH := (heatPair_corrH h hr0 (σ := 2) (Or.inr (Or.inr rfl)) ht0 ht).mono hs le_rfl
  have hPV := (heatPair_corrV h hr0 (σ := 2) (Or.inr (Or.inr rfl)) ht0 ht).mono hs le_rfl
  have hIy := hPy.intervalIntegrable_dissipation hst
  have hIH := hPH.intervalIntegrable_dissipation hst
  have hIV := hPV.intervalIntegrable_dissipation hst
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at hIy hIH hIV
  refine ⟨hIy, ?_⟩
  -- horizontal
  have hc1 : ContinuousOn (fun u => hnorm 1 (PiH (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrH_sq h hr0 (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hc2 : ContinuousOn (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrH_sq h hr0 (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hc3 : ContinuousOn (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrV_sq h hr0 (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  set E2 := 4 * φ ^ 2 + 4 with hE2
  have hlen0 : 0 ≤ t - s := by linarith
  have i1 : IntervalIntegrable (fun u => 450 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 *
      hnorm 2 (PiH (corrSlow r g y u)) ^ 2) volume s t :=
    ((continuousOn_const.mul hc1).mul hc2).intervalIntegrable_of_Icc hst
  have i1c : ∫ u in s..t, 450 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 *
      hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤ 900 * Aq ^ 2 * Bq ^ 2 := by
    have h0 : ∫ u in s..t, 450 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 *
        hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤ ∫ _ in s..t, 450 * Aq ^ 2 * Bq ^ 2 := by
      refine intervalIntegral.integral_mono_on hst i1 intervalIntegrable_const fun u hu => ?_
      have h1 := pow_le_pow_left₀ (hnorm_nonneg _ _) (haH u hu) 2
      have h2 := pow_le_pow_left₀ (hnorm_nonneg _ _) (hbH u hu) 2
      have h3 : hnorm 1 (PiH (corrSlow r g y u)) ^ 2 * hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤
          Aq ^ 2 * Bq ^ 2 := mul_le_mul h1 h2 (by positivity) (by positivity)
      nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at h0
    have h4 : 0 ≤ 450 * Aq ^ 2 * Bq ^ 2 := by positivity
    have h5 := mul_le_mul_of_nonneg_right hlen h4
    linarith
  have hHle : ∫ u in s..t, hnorm 3 (PiH (corrSlow r g y u)) ^ 2 ≤
      Bq ^ 2 + 900 * Aq ^ 2 * Bq ^ 2 + 2 * E2 := by
    rw [intervalIntegral.integral_add i1 (hresI.const_mul 2),
      intervalIntegral.integral_const_mul] at lawH
    have h1 := pow_le_pow_left₀ (hnorm_nonneg _ _) (hbH s ⟨le_rfl, hst⟩) 2
    have h2 := sq_nonneg (hnorm 2 (PiH (corrSlow r g y t)))
    linarith
  -- vertical
  have iZ : IntervalIntegrable (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2) volume s t :=
    hc3.intervalIntegrable_of_Icc hst
  have hcS : ContinuousOn (fun u => slowNorm 2 r g y u ^ 2) (Icc s t) :=
    (((norms_continuous h ht0 ht).2.2.2.1).mono (Icc_subset_Icc_left hs)).pow 2
  have iS : IntervalIntegrable (fun u => slowNorm 2 r g y u ^ 2) volume s t :=
    hcS.intervalIntegrable_of_Icc hst
  have hZint : ∫ u in s..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤ 2 * cp caps.JS + 1 := by
    have h0 : ∫ u in s..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤
        ∫ u in s..t, (2 * slowNorm 2 r g y u ^ 2 + 1 / 8) := by
      refine intervalIntegral.integral_mono_on hst iZ
        ((iS.const_mul 2).add intervalIntegrable_const) fun u hu => ?_
      have h1 := hbZ u hu
      have h2 : 0 ≤ slowNorm 2 r g y u := hnorm_nonneg _ _
      have h3 := pow_le_pow_left₀ (hnorm_nonneg _ _) h1 2
      nlinarith [sq_nonneg (slowNorm 2 r g y u - 1 / 4)]
    rw [intervalIntegral.integral_add (iS.const_mul 2) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at h0
    have h1 := hon.2.2.1.trans (le_cp _)
    linarith
  have hVle : ∫ u in s..t, hnorm 3 (PiV (corrSlow r g y u)) ^ 2 ≤
      Bz ^ 2 + 226 * A3 ^ 2 * (2 * cp caps.JS + 1) + 26 * Bq ^ 4 * Zq ^ 2 / A3 ^ 4 + 4 * E2 := by
    have i2 : IntervalIntegrable (fun u => 226 * A3 ^ 2 * hnorm 2 (PiV (corrSlow r g y u)) ^ 2)
        volume s t := iZ.const_mul _
    rw [intervalIntegral.integral_add (i2.add intervalIntegrable_const) (hresI.const_mul 4),
      intervalIntegral.integral_add i2 intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul] at lawV
    have h1 : hnorm 2 (PiV (corrSlow r g y s)) ≤ Bz := by
      have h2 := hbZ s ⟨le_rfl, hst⟩
      have h3 := (hon.1 s ⟨le_rfl, hst⟩).2.2.2.1.trans (le_cp _)
      rw [hBz]
      linarith
    have h4 := pow_le_pow_left₀ (hnorm_nonneg _ _) h1 2
    have h5 := sq_nonneg (hnorm 2 (PiV (corrSlow r g y t)))
    have h6 : 226 * A3 ^ 2 * ∫ u in s..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤
        226 * A3 ^ 2 * (2 * cp caps.JS + 1) := mul_le_mul_of_nonneg_left hZint (by positivity)
    have h7 : (t - s) * (13 * Bq ^ 4 * Zq ^ 2 / A3 ^ 4) ≤ 26 * Bq ^ 4 * Zq ^ 2 / A3 ^ 4 := by
      have h8 : 0 ≤ 13 * Bq ^ 4 * Zq ^ 2 / A3 ^ 4 := by positivity
      have e : 26 * Bq ^ 4 * Zq ^ 2 / A3 ^ 4 = 2 * (13 * Bq ^ 4 * Zq ^ 2 / A3 ^ 4) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hlen h8
    linarith
  have hsplit : ∫ u in s..t, hnorm 3 (corrSlow r g y u) ^ 2 =
      ∫ u in s..t,
        (hnorm 3 (PiH (corrSlow r g y u)) ^ 2 + hnorm 3 (PiV (corrSlow r g y u)) ^ 2) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hst]
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 (ae_inH3_corr h hr0 hs hst ht)]
      with u hu hm
    have h3 := hnorm_sq_split_slow (hu (Ioc_subset_Icc_self hm))
    rwa [PiS_corrSlow] at h3
  rw [hsplit, intervalIntegral.integral_add hIH hIV]
  unfold h2Price
  rw [← hAq, ← hBq, ← hZq, ← hBz, ← hA3]
  have e : 6 * (4 * φ ^ 2 + 4) = 2 * E2 + 4 * E2 := by rw [hE2]; ring
  rw [e]
  linarith

/-! ### I. The budget -/

/-- `x y ≤ x²/64 + 16 y²`. -/
private lemma young64 (x y : ℝ) : x * y ≤ 1 / 64 * x ^ 2 + 16 * y ^ 2 := by
  nlinarith [sq_nonneg (x / 8 - 4 * y)]

/-- **The pointwise budget** (pure algebra): the six terms of `h2RHS`, with
`N₂ = ‖fastNL‖₂ ≤ X c + L_y c_y + L₀`, are at most `(9/64) c² + B b c + (G₀ + G₁ c_y²) b² + H`. -/
theorem budget_core {b c cy B M κ Lc Ly L0 X h1 α T1 T2 T3 T4 T5 T6 N2 : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hM : 0 ≤ M) (hκ : 0 ≤ κ) (hLy : 0 ≤ Ly) (hL0 : 0 ≤ L0)
    (t1 : T1 ≤ B * b * c) (t2 : T2 ≤ h1 * c) (t3 : T3 ≤ 2 * α * b * c) (t4 : T4 ≤ κ * b * N2)
    (t5 : T5 ≤ 1 / 64 * c ^ 2) (t6 : T6 ≤ M * N2 * (b * c))
    (hN2 : N2 ≤ X * c + Ly * cy + L0) (hX : X ≤ Lc) (hXb : M * X * b ≤ 3 / 64) :
    T1 + T2 + T3 + T4 + T5 + T6 ≤ 9 / 64 * c ^ 2 + B * b * c +
      (16 * (M * L0) ^ 2 + 16 * (κ * Lc) ^ 2 + κ * L0 / 2 + 64 * α ^ 2 +
        (16 * (M * Ly) ^ 2 + κ * Ly / 2) * cy ^ 2) * b ^ 2 +
      (16 * h1 ^ 2 + κ * Ly / 2 + κ * L0 / 2) := by
  have hbc : 0 ≤ b * c := mul_nonneg hb hc
  have s6 : T6 ≤ M * X * b * c ^ 2 + M * Ly * b * c * cy + M * L0 * b * c := by
    have h1' : M * N2 * (b * c) ≤ M * (X * c + Ly * cy + L0) * (b * c) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN2 hM) hbc
    calc T6 ≤ _ := t6
      _ ≤ _ := h1'
      _ = _ := by ring
  have s6a : M * X * b * c ^ 2 ≤ 3 / 64 * c ^ 2 := mul_le_mul_of_nonneg_right hXb (sq_nonneg c)
  have s6b : M * Ly * b * c * cy ≤ 1 / 64 * c ^ 2 + 16 * (M * Ly) ^ 2 * cy ^ 2 * b ^ 2 := by
    have := young64 c (M * Ly * b * cy)
    calc M * Ly * b * c * cy = c * (M * Ly * b * cy) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have s6c : M * L0 * b * c ≤ 1 / 64 * c ^ 2 + 16 * (M * L0) ^ 2 * b ^ 2 := by
    have := young64 c (M * L0 * b)
    calc M * L0 * b * c = c * (M * L0 * b) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have hκb : 0 ≤ κ * b := mul_nonneg hκ hb
  have s4 : T4 ≤ κ * Lc * b * c + κ * Ly * b * cy + κ * L0 * b := by
    have h2' : N2 ≤ Lc * c + Ly * cy + L0 := by
      have := mul_le_mul_of_nonneg_right hX hc
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2' hκb
    calc T4 ≤ _ := t4
      _ ≤ _ := h3
      _ = _ := by ring
  have s4a : κ * Lc * b * c ≤ 1 / 64 * c ^ 2 + 16 * (κ * Lc) ^ 2 * b ^ 2 := by
    have := young64 c (κ * Lc * b)
    calc κ * Lc * b * c = c * (κ * Lc * b) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have s4b : κ * Ly * b * cy ≤ κ * Ly / 2 * cy ^ 2 * b ^ 2 + κ * Ly / 2 := by
    have h4 : 0 ≤ κ * Ly / 2 := by positivity
    have h5 : b * cy ≤ (cy ^ 2 * b ^ 2 + 1) / 2 := by nlinarith [sq_nonneg (b * cy - 1)]
    have := mul_le_mul_of_nonneg_left h5 h4
    nlinarith
  have s4c : κ * L0 * b ≤ κ * L0 / 2 * b ^ 2 + κ * L0 / 2 := by
    have h4 : 0 ≤ κ * L0 / 2 := by positivity
    have h5 : b ≤ (b ^ 2 + 1) / 2 := by nlinarith [sq_nonneg (b - 1)]
    have := mul_le_mul_of_nonneg_left h5 h4
    nlinarith
  have s2 : T2 ≤ 1 / 64 * c ^ 2 + 16 * h1 ^ 2 := by
    have := young64 c h1
    linarith [show h1 * c = c * h1 by ring]
  have s3 : T3 ≤ 1 / 64 * c ^ 2 + 64 * α ^ 2 * b ^ 2 := by
    have := young64 c (2 * α * b)
    have e : (2 * α * b) ^ 2 = 4 * α ^ 2 * b ^ 2 := by ring
    rw [e] at this
    linarith [show 2 * α * b * c = c * (2 * α * b) by ring]
  have e : 9 / 64 * c ^ 2 + B * b * c +
      (16 * (M * L0) ^ 2 + 16 * (κ * Lc) ^ 2 + κ * L0 / 2 + 64 * α ^ 2 +
        (16 * (M * Ly) ^ 2 + κ * Ly / 2) * cy ^ 2) * b ^ 2 +
      (16 * h1 ^ 2 + κ * Ly / 2 + κ * L0 / 2) =
      B * b * c + (1 / 64 * c ^ 2 + 16 * h1 ^ 2) + (1 / 64 * c ^ 2 + 64 * α ^ 2 * b ^ 2) +
      ((1 / 64 * c ^ 2 + 16 * (κ * Lc) ^ 2 * b ^ 2) + (κ * Ly / 2 * cy ^ 2 * b ^ 2 + κ * Ly / 2) +
        (κ * L0 / 2 * b ^ 2 + κ * L0 / 2)) + 1 / 64 * c ^ 2 +
      (3 / 64 * c ^ 2 + (1 / 64 * c ^ 2 + 16 * (M * Ly) ^ 2 * cy ^ 2 * b ^ 2) +
        (1 / 64 * c ^ 2 + 16 * (M * L0) ^ 2 * b ^ 2)) := by ring
  rw [e]
  linarith

/-! ### J. The thresholds -/

/-- All the terms of the threshold are nonnegative and paid. -/
theorem thr_pieces {θ CH₀ μ φ q : ℝ} (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) (caps : Caps)
    (hq : h2Threshold θ CH₀ μ φ caps ≤ q) :
    1 ≤ q ∧ budgetPoly φ caps ≤ q ∧ 32 * c4 * cp caps.yF ^ 2 ≤ q ∧ 2 * φ ≤ q ∧
      16 * c4 * cp caps.yF ≤ q ∧ role16 caps ≤ q ∧ role17 caps ≤ q ∧ role31far caps ≤ q ∧
      role31mix caps ≤ q ∧ role31psi φ caps ≤ q ∧ role31price μ φ caps ≤ q ∧
      role28 μ φ caps ≤ q ∧ role28src2 φ caps ≤ q ∧ role32 θ CH₀ μ φ caps ≤ q := by
  have hc := c4_pos
  have hY := cp_nonneg caps.yF
  have hB := cp_nonneg caps.BS
  have hbil := cBil_nonneg
  have hL0 := h2L0_nonneg hφ caps
  have hLc := h2Lc_nonneg caps
  have hLy := h2Ly_nonneg caps
  have hPr := h2Price_nonneg (φ := φ) hμ caps
  have hSt := cStat2_pos
  have hHe := cHeat2_pos
  have hPc := profC_pos
  have hMc := h2Mc_nonneg
  have n1 : 0 ≤ budgetPoly φ caps := zero_le_one.trans (one_le_budgetPoly hφ caps)
  have n2 : 0 ≤ 32 * c4 * cp caps.yF ^ 2 := by positivity
  have n4 : 0 ≤ 16 * c4 * cp caps.yF := by positivity
  have n5 : 0 ≤ role16 caps := by unfold role16; positivity
  have n6 : 0 ≤ role17 caps := by unfold role17; positivity
  have n7 : 0 ≤ role31far caps := by
    have := h2Lead_nonneg caps
    have := cQ2_nonneg
    have := cI_pos
    have := cFar_nonneg
    unfold role31far
    positivity
  have n8 : 0 ≤ role31mix caps := by
    have := cp_nonneg caps.WS
    unfold role31mix
    positivity
  have n9 : 0 ≤ role31psi φ caps := by unfold role31psi; positivity
  have n10 : 0 ≤ role31price μ φ caps := by unfold role31price; positivity
  have n11 : 0 ≤ role28 μ φ caps := by unfold role28; positivity
  have n12 : 0 ≤ role28src2 φ caps := by
    have := hSrc_nonneg hφ caps
    have := cSrc_nonneg
    unfold role28src2
    positivity
  have n13 : 0 ≤ role32 θ CH₀ μ φ caps := by
    have := h2Hn_nonneg hφ caps
    unfold role32 WStar
    positivity
  unfold h2Threshold at hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- A threshold `(c X)^E ≤ q` (`E e = 1`, `q ≥ 1`) pays `c X q^{−e} ≤ 1`. -/
lemma rpow_paid {X q c e E : ℝ} (hX : 0 ≤ X) (hc : 0 ≤ c) (he : 0 < e) (hE : E * e = 1)
    (hq1 : 1 ≤ q) (hq : (c * X) ^ E ≤ q) : c * X * q ^ (-e) ≤ 1 := by
  have hq0 : 0 < q := by linarith
  have hcX : 0 ≤ c * X := mul_nonneg hc hX
  have h1 : c * X ≤ q ^ e := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hcX _) hq he.le
    rwa [← Real.rpow_mul hcX, hE, Real.rpow_one] at this
  rw [Real.rpow_neg hq0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hq0 e)]
  exact h1

/-- `M = C₀ N(q) + c_far/q ≤ Mc q^{−49/100}`. -/
lemma nM_le {r : ℝ} (hq : 1 ≤ |r|) : nM r ≤ h2Mc * |r| ^ (-(49 / 100 : ℝ)) := by
  have hq0 : 0 < |r| := by linarith
  have h1 := nearN_le_profC hq
  have h2 : 1 / |r| ≤ |r| ^ (-(49 / 100 : ℝ)) := by
    have := Real.rpow_le_rpow_of_exponent_le hq (by norm_num : (-1 : ℝ) ≤ -(49 / 100))
    rwa [Real.rpow_neg_one, ← one_div] at this
  have h3 := nearC₀_pos
  have h4 := cFar_nonneg
  unfold nM h2Mc
  have e1 : nearC₀ * nearN |r| ≤ nearC₀ * (profC * |r| ^ (-(49 / 100 : ℝ))) :=
    mul_le_mul_of_nonneg_left h1 h3.le
  have e2 : cFar / |r| ≤ cFar * |r| ^ (-(49 / 100 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left h2 h4
    rwa [mul_one_div] at this
  nlinarith

/-- `(2⁶ Mc X)^{100/49} ≤ q ⟹ M X ≤ 1/64`. -/
lemma nM_mul_le {r X : ℝ} (hq : 1 ≤ |r|) (hX : 0 ≤ X)
    (h : (2 ^ 6 * h2Mc * X) ^ (100 / 49 : ℝ) ≤ |r|) : nM r * X ≤ 1 / 64 := by
  have hMc := h2Mc_nonneg
  have hp := rpow_paid (c := 2 ^ 6 * h2Mc) (e := 49 / 100) (E := 100 / 49) hX (by positivity)
    (by norm_num) (by norm_num) hq h
  have h1 := mul_le_mul_of_nonneg_right (nM_le hq) hX
  have e : h2Mc * |r| ^ (-(49 / 100 : ℝ)) * X =
      1 / 64 * (2 ^ 6 * h2Mc * X * |r| ^ (-(49 / 100 : ℝ))) := by ring
  rw [e] at h1
  linarith

/-- The proper profile paid: `C (P(q) + q^{−1/2}) Y ≤ 1/128`. -/
lemma pz_le {C Y q : ℝ} (hC : 0 ≤ C) (hY : 0 ≤ Y) (hq : 1 ≤ q)
    (h1 : (2 ^ 8 * C * profC * Y) ^ (100 / 29 : ℝ) ≤ q) (h2 : (2 ^ 8 * C * Y) ^ 2 ≤ q) :
    C * (nearP q + q ^ (-(1 / 2) : ℝ)) * Y ≤ 1 / 128 := by
  have hPc := profC_pos
  have hp1 := rpow_paid (c := 2 ^ 8 * C * profC) (e := 29 / 100) (E := 100 / 29) hY
    (by positivity) (by norm_num) (by norm_num) hq h1
  have h2' : (2 ^ 8 * C * Y) ^ (2 : ℝ) ≤ q := by
    rw [Real.rpow_two]
    exact h2
  have hp2 := rpow_paid (c := 2 ^ 8 * C) (e := 1 / 2) (E := 2) hY (by positivity) (by norm_num)
    (by norm_num) hq h2'
  have hP := nearP_le_profC hq
  have hCY : 0 ≤ C * Y := mul_nonneg hC hY
  have h3 := mul_le_mul_of_nonneg_left hP hCY
  have e1 : C * Y * (profC * q ^ (-(29 / 100 : ℝ))) =
      1 / 2 ^ 8 * (2 ^ 8 * C * profC * Y * q ^ (-(29 / 100 : ℝ))) := by ring
  rw [e1] at h3
  have e2 : C * (nearP q + q ^ (-(1 / 2) : ℝ)) * Y =
      C * Y * nearP q + 1 / 2 ^ 8 * (2 ^ 8 * C * Y * q ^ (-(1 / 2) : ℝ)) := by ring
  rw [e2]
  norm_num at hp1 hp2 h3 ⊢
  linarith

/-- `√(ab) b ≤ √P y^{3/2}`. -/
lemma sqrt_mul_mul_le {a b P Y : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ P) (hb : b ≤ Y) :
    Real.sqrt (a * b) * b ≤ Real.sqrt P * Y ^ (3 / 2 : ℝ) := by
  have hY0 : 0 ≤ Y := hb0.trans hb
  have e : Y ^ (3 / 2 : ℝ) = Real.sqrt Y * Y := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.rpow_add' hY0 (by norm_num), Real.rpow_one]
  rw [e, Real.sqrt_mul ha0]
  have h1 : Real.sqrt a ≤ Real.sqrt P := Real.sqrt_le_sqrt ha
  have h2 : Real.sqrt b ≤ Real.sqrt Y := Real.sqrt_le_sqrt hb
  have h4 := Real.sqrt_nonneg b
  have h5 := Real.sqrt_nonneg P
  have h6 := Real.sqrt_nonneg Y
  have h7 : Real.sqrt a * Real.sqrt b ≤ Real.sqrt P * Real.sqrt Y := mul_le_mul h1 h2 h4 h5
  calc Real.sqrt a * Real.sqrt b * b ≤ Real.sqrt P * Real.sqrt Y * Y :=
        mul_le_mul h7 hb hb0 (mul_nonneg h5 h6)
    _ = _ := by ring

/-- **The leading share** (role 31, fast–fast near term and the leading part of the high mixed
term): `M (c_Q + 16 c_I) √P_F y^{3/2} ≤ 2/64` from `K₂ √P_F y^{3/2} N(q) ≤ 1` and the FAR role. -/
lemma leading_share {caps : Caps} {r : ℝ} (hP0 : 0 ≤ caps.PF) (hy0 : 0 ≤ caps.yF)
    (hK : h2K₂ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * nearN |r| ≤ 1)
    (hfar : role31far caps ≤ |r|) (hr : 1 ≤ |r|) :
    nM r * ((cQ2 + 16 * cI) * h2Lead caps) ≤ 2 / 64 := by
  have hr0 : 0 < |r| := by linarith
  have ePF : cp caps.PF = caps.PF := max_eq_left hP0
  have ey : cp caps.yF = caps.yF := max_eq_left hy0
  have hL0 := h2Lead_nonneg caps
  have hc := cQ2_nonneg
  have hI := cI_pos
  have hX : 0 ≤ (cQ2 + 16 * cI) * h2Lead caps := by positivity
  set Lead := h2Lead caps with hLead
  have e1 : Lead = Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) := by
    rw [hLead]
    unfold h2Lead
    rw [ePF, ey]
  have h1 : nearC₀ * nearN |r| * ((cQ2 + 16 * cI) * Lead) ≤ 1 / 64 := by
    have e : nearC₀ * nearN |r| * ((cQ2 + 16 * cI) * Lead) =
        1 / 64 * (h2K₂ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * nearN |r|) := by
      rw [e1]
      unfold h2K₂
      ring
    rw [e]
    linarith
  have h2 : cFar / |r| * ((cQ2 + 16 * cI) * Lead) ≤ 1 / 2 ^ 10 := by
    have e : cFar / |r| * ((cQ2 + 16 * cI) * Lead) = role31far caps / 2 ^ 10 / |r| := by
      unfold role31far
      rw [← hLead]
      field_simp
    rw [e, div_le_div_iff₀ hr0 (by norm_num)]
    have : role31far caps * 2 ^ 10 / 2 ^ 10 ≤ |r| := by
      rw [mul_div_assoc, div_self (by norm_num), mul_one]
      exact hfar
    field_simp
    linarith
  unfold nM
  rw [add_mul]
  norm_num at h1 h2 ⊢
  linarith

/-- The source bound with the transform inserted: at a time when `F, S, y_S ∈ H³`,
`‖fastNL‖₂ ≤ X c_F + Λ̄_y c_y + Λ̄₀`, `X = (c_Q + 16 c_I) √(ab) + 16 W_S + 32 c₄`. -/
theorem fastNL_bound (h : ActualSol μ φ r g y Ty) (hr : 1 ≤ |r|) {caps : Caps} {s t : ℝ}
    (hon : OnPrefix caps r g y s t) {u : ℝ} (hu : u ∈ Icc s t) (hs : 0 ≤ s)
    (huT : ENNReal.ofReal u < Ty) (hq2 : 2 * φ ≤ |r|) (hq3 : 16 * c4 * cp caps.yF ≤ |r|)
    (hF3 : InH 3 (PiF (actual r g y u))) (hS3 : InH 3 (PiS (actual r g y u)))
    (hy3 : InH 3 (corrSlow r g y u)) :
    MZ 2 (fastNL r g y u) ∧ hnorm 2 (fastNL r g y u) ≤
      ((cQ2 + 16 * cI) * Real.sqrt (fastNorm 1 r g y u * fastNorm 2 r g y u) +
        16 * cp caps.WS + 32 * c4) * fastNorm 3 r g y u +
      h2Ly caps * hnorm 3 (corrSlow r g y u) + h2L0 φ caps := by
  have hr0' : 0 < |r| := by linarith
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr0'; exact lt_irrefl _ hr0'
  have hu0 : 0 ≤ u := hs.trans hu.1
  obtain ⟨-, hψle⟩ := psi_two_le h hr0 hu0
  have hε : hnorm 2 (psi r 0 g u) ≤ 1 := hψle.trans ((div_le_one hr0').2 hq2)
  obtain ⟨hMZ, hN⟩ := fastNL_two_le h hon hu hs huT hε hF3 hS3
  refine ⟨hMZ, hN.trans ?_⟩
  have hT := slow_three_le h hr0 hu0 huT hF3 hy3
  obtain ⟨cF1, cF2, -, -, -⟩ := hon.1 u hu
  set a := fastNorm 1 r g y u with ha
  set b := fastNorm 2 r g y u with hb
  set c := fastNorm 3 r g y u with hc'
  set cS := hnorm 3 (PiS (actual r g y u)) with hcS
  set cy := hnorm 3 (corrSlow r g y u) with hcy
  set E := hnorm 2 (psi r 0 g u) with hE
  set A2 := Real.sqrt (a * b) with hA2
  have ha0 : 0 ≤ a := hnorm_nonneg _ _
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have hc0 : 0 ≤ c := hnorm_nonneg _ _
  have hcS0 : 0 ≤ cS := hnorm_nonneg _ _
  have hcy0 : 0 ≤ cy := hnorm_nonneg _ _
  have hE0 : 0 ≤ E := hnorm_nonneg _ _
  have hA0 : 0 ≤ A2 := Real.sqrt_nonneg _
  have hc4 := c4_pos
  have hcI := cI_pos
  have hρ : 16 * c4 / |r| * b ≤ 1 := by
    have h1 : b ≤ cp caps.yF := cF2.trans (le_cp _)
    rw [div_mul_eq_mul_div, div_le_one hr0']
    calc 16 * c4 * b ≤ 16 * c4 * cp caps.yF := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ |r| := hq3
  have hcS1 : cS ≤ cy + c := by
    have h1 : 16 * c4 / |r| * b * c ≤ 1 * c := mul_le_mul_of_nonneg_right hρ hc0
    linarith
  have hroot : A2 ≤ h2Root caps := by
    refine Real.sqrt_le_sqrt ?_
    exact mul_le_mul (cF1.trans (le_cp _)) (cF2.trans (le_cp _)) hb0 (cp_nonneg _)
  have t1 : 16 * cI * A2 * cS ≤ 16 * cI * A2 * (cy + c) :=
    mul_le_mul_of_nonneg_left hcS1 (by positivity)
  have t2 : 16 * c4 * E * (c + cS) ≤ 16 * c4 * 1 * (c + (cy + c)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hε (by positivity)) (by linarith) (by positivity)
      (by positivity)
  have t3 : (16 * cI * A2 + 16 * c4) * cy ≤ h2Ly caps * cy := by
    refine mul_le_mul_of_nonneg_right ?_ hcy0
    unfold h2Ly
    have := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 16 * cI)
    linarith
  have e : ((cQ2 + 16 * cI) * A2 + 16 * cp caps.WS + 32 * c4) * c + (16 * cI * A2 + 16 * c4) * cy =
      cQ2 * A2 * c + 16 * (cp caps.WS * c) + 16 * cI * A2 * (cy + c) +
        16 * c4 * 1 * (c + (cy + c)) := by ring
  have e2 : cQ2 * A2 * c + 16 * (cp caps.WS * c + cI * A2 * cS) + (16 * c4 * E * (c + cS) +
      h2L0 φ caps) = cQ2 * A2 * c + 16 * (cp caps.WS * c) + 16 * cI * A2 * cS +
        16 * c4 * E * (c + cS) + h2L0 φ caps := by ring
  rw [e2]
  linarith

/-- The six term bounds of `h2RHS` at a time when `F, S, y_S ∈ H³`. -/
theorem h2RHS_terms (h : ActualSol μ φ r g y Ty) (hφ : 0 ≤ φ) {θ CH : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hres : ResH2 θ CH) (hCH : 0 ≤ CH) {caps : Caps} {s t : ℝ}
    (hon : OnPrefix caps r g y s t) (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hr : 1 ≤ |r|)
    (hq2 : 2 * φ ≤ |r|) {u : ℝ} (hu : u ∈ Icc s t) (hF3 : InH 3 (PiF (actual r g y u)))
    (hNL : MZ 2 (fastNL r g y u)) (hPz : cHeat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) *
      cp caps.yF ≤ 1 / 128) :
    -pair 2 (PiF (actual r g y u)) (Qres (PiF (actual r g y u)) (PiF (actual r g y u))) ≤
        resCoeff θ CH μ φ caps * fastNorm 2 r g y u * fastNorm 3 r g y u ∧
      -pair 2 (PiF (actual r g y u)) (Hpsi r g y u) ≤ hPsiC φ caps r * fastNorm 3 r g y u ∧
      2 * pair 2 (PiF (actual r g y u))
        (X1op r (r * u) (slowNL r g y u) (PiF (actual r g y u))) ≤
        2 * (cSrc * hSrc φ caps / |r|) * fastNorm 2 r g y u * fastNorm 3 r g y u ∧
      metBil2 r (r * u) (PiS (actual r g y u)) (PiF (actual r g y u)) (fastNL r g y u) ≤
        kap caps r * fastNorm 2 r g y u * hnorm 2 (fastNL r g y u) ∧
      -cubicHeat2 r (r * u) (PiF (actual r g y u)) ≤ 1 / 64 * fastNorm 3 r g y u ^ 2 ∧
      cubicD 2 (-1) r (r * u) (PiF (actual r g y u)) (fastNL r g y u) ≤
        nM r * hnorm 2 (fastNL r g y u) * (fastNorm 2 r g y u * fastNorm 3 r g y u) := by
  have hr0' : 0 < |r| := by linarith
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr0'; exact lt_irrefl _ hr0'
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hx := actual_adm h hu0 huT
  set F := PiF (actual r g y u) with hFdef
  set S := PiS (actual r g y u) with hSdef
  have hF : Adm 2 F := hx.PiF
  have hS : Adm 2 S := hx.PiS
  have hFa3 : Adm 3 F := ⟨hF3, hF.real, hF.sol, hF.mean⟩
  have hFm3 : MZ 3 F := hFa3.mz
  have hF' : PiF F = F := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hFdef, PiF, hk]
  have hS' : PiS S = S := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hSdef, PiS, hk]
  obtain ⟨cF1, cF2, -, cS2, -⟩ := hon.1 u hu
  have hb0 : 0 ≤ hnorm 2 F := hnorm_nonneg _ _
  have hc0 : 0 ≤ hnorm 3 F := hnorm_nonneg _ _
  obtain ⟨hHI, hHle⟩ := Hpsi_one_le h hr0 hon hu hs huT hq2
  obtain ⟨-, hψle⟩ := psi_two_le h hr0 hu0
  have hε : hnorm 2 (psi r 0 g u) ≤ 1 := hψle.trans ((div_le_one hr0').2 hq2)
  obtain ⟨hslow, hslowle⟩ := slowNL_one_le' h hon hu hs huT hε
  obtain ⟨hNr, -, -⟩ := fastNL_l2 h hu0 huT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := hres F hFa3 hF'
    have h2 := fast_theta_le h hφ hr hθ0 hθ1 hu0 huT cF1
    have hρ : hnorm θ F ≤ rhoOf μ φ ^ (1 - θ) * caps.PF ^ θ := h2
    refine (neg_le_abs _).trans (h1.trans ?_)
    have hbc : 0 ≤ hnorm 2 F * hnorm 3 F := mul_nonneg hb0 hc0
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ hCH) hbc
    unfold resCoeff
    calc CH * hnorm θ F * hnorm 2 F * hnorm 3 F = CH * hnorm θ F * (hnorm 2 F * hnorm 3 F) := by
          ring
      _ ≤ CH * (rhoOf μ φ ^ (1 - θ) * caps.PF ^ θ) * (hnorm 2 F * hnorm 3 F) := this
      _ = _ := by unfold fastNorm; ring
  · have hF1 : InH (2 + 1) F := by
      rw [show (2 : ℝ) + 1 = 3 by norm_num]
      exact hF3
    have hH : InH (2 - 1) (Hpsi r g y u) := by
      rw [show (2 : ℝ) - 1 = 1 by norm_num]
      exact hHI
    have h1 := (pair_le hF1 hH).2
    rw [show (2 : ℝ) + 1 = 3 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num] at h1
    refine (neg_le_abs _).trans (h1.trans ?_)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hHle hc0
  · have h1 := pair_X1op_slow_le hr0 (r * u) hslow (PiS_slowNL u) hFm3 hF' hFa3.real
    have h2 := (le_abs_self _).trans h1
    have hS0 := hSrc_nonneg hφ caps
    have hc := cSrc_nonneg
    have h3 : cSrc * hnorm 1 (slowNL r g y u) * hnorm 2 F * hnorm 3 F / |r| ≤
        cSrc * hSrc φ caps * hnorm 2 F * hnorm 3 F / |r| := by
      gcongr
    have e : 2 * (cSrc * hSrc φ caps / |r|) * fastNorm 2 r g y u * fastNorm 3 r g y u =
        2 * (cSrc * hSrc φ caps * hnorm 2 F * hnorm 3 F / |r|) := by
      unfold fastNorm
      ring
    rw [e]
    linarith
  · have h1 := metBil2_le hr0 (r * u) hS.mz hS' hF.mz hF' hF.real hNL hNr
    refine (le_abs_self _).trans (h1.trans ?_)
    have hbS := hnorm_nonneg 2 S
    have hS2 : hnorm 2 S ≤ cp caps.BS := cS2.trans (le_cp _)
    have hG0 := hnorm_nonneg 2 (fastNL r g y u)
    have hb := cBil_nonneg
    unfold kap fastNorm
    calc cBil * hnorm 2 S * hnorm 2 F * hnorm 2 (fastNL r g y u) / |r|
        ≤ cBil * cp caps.BS * hnorm 2 F * hnorm 2 (fastNL r g y u) / |r| := by gcongr
      _ = _ := by ring
  · have h1 := cubicHeat2_le hr (r * u) hFm3 hFa3.real hF'
    refine (neg_le_abs _).trans (h1.trans ?_)
    have hb : hnorm 2 F ≤ cp caps.yF := cF2.trans (le_cp _)
    set Pz := nearP |r| + |r| ^ (-(1 / 2) : ℝ) with hPzdef
    have hPz0 : 0 ≤ cHeat2 * Pz := by
      have := cHeat2_pos
      have h3 : 0 ≤ nearP |r| := by
        unfold nearP
        positivity
      have h4 : 0 ≤ |r| ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hr0'.le _
      positivity
    have h2 : cHeat2 * Pz * hnorm 2 F ≤ 1 / 64 :=
      (mul_le_mul_of_nonneg_left hb hPz0).trans (hPz.trans (by norm_num))
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  · exact (le_abs_self _).trans (cubicD_two_le hr0 (r * u) hFm3 hFa3.real hF' hNL hNr)

/-- **E8, the pointwise budget**: at almost every time of a piece, once the thresholds are paid
and `K₂ √P_F y^{3/2} N(q) ≤ 1`,
`h2RHS ≤ (9/64) c_F² + B b_F c_F + (G₀' + G₁' c_y²) b_F² + H'`. -/
theorem h2RHS_budget (h : ActualSol μ φ r g y Ty) (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) {θ CH₀ CH : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hres : ResH2 θ CH) (hCH : 0 ≤ CH) {caps : Caps} {s t : ℝ}
    (hP : PieceHyp 2 (h2Threshold θ CH₀ μ φ) r g y Ty caps s t)
    (hK : h2K₂ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * nearN |r| ≤ 1) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), h2RHS r g y u ≤
      9 / 64 * fastNorm 3 r g y u ^ 2 +
        resCoeff θ CH μ φ caps * fastNorm 2 r g y u * fastNorm 3 r g y u +
        (h2G0 φ caps r + h2G1 caps r * hnorm 3 (corrSlow r g y u) ^ 2) *
          fastNorm 2 r g y u ^ 2 + h2H1 φ caps r := by
  obtain ⟨hr, -, -, hq2, hq3, -, r17, hfar, hmix, -, -, -, -, -⟩ :=
    thr_pieces hμ hφ caps hP.thr
  have hr0' : 0 < |r| := by linarith
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr0'; exact lt_irrefl _ hr0'
  have hs := hP.hs
  have hst := hP.hst
  have ht := hP.ht
  have hon := hP.onPrefix
  have hPc0 : 0 ≤ caps.PF := (hnorm_nonneg 1 _).trans (hon.1 s ⟨le_rfl, hst⟩).1
  have hy0 : 0 ≤ caps.yF := (hnorm_nonneg 2 _).trans (hon.1 s ⟨le_rfl, hst⟩).2.1
  have hlead := leading_share hPc0 hy0 hK hfar hr
  have hYc := cp_nonneg caps.yF
  have hPzh : cHeat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) * cp caps.yF ≤ 1 / 128 := by
    have hHe := cHeat2_pos
    have hPC := profC_pos
    have n1 : 0 ≤ (2 ^ 8 * cHeat2 * profC * cp caps.yF) ^ (100 / 29 : ℝ) := by positivity
    have n2 : 0 ≤ (2 ^ 8 * cHeat2 * cp caps.yF) ^ 2 := by positivity
    unfold role17 at r17
    exact pz_le hHe.le hYc hr (by linarith) (by linarith)
  have hWm : nM r * (cp caps.yF * (16 * cp caps.WS + 32 * c4)) ≤ 1 / 64 :=
    nM_mul_le hr (by have := cp_nonneg caps.WS; have := c4_pos; positivity) hmix
  filter_upwards [ae_inH3_split h hs hst ht, ae_inH3_corr h hr0 hs hst ht,
    ae_restrict_mem measurableSet_Icc] with u hu3 hy3 hu
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  obtain ⟨hNL, hN2⟩ := fastNL_bound h hr hon hu hs huT hq2 hq3 hu3.1 hu3.2 hy3
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := h2RHS_terms (μ := μ) h hφ hθ0 hθ1 hres hCH hon hs ht hr hq2 hu
    hu3.1 hNL hPzh
  obtain ⟨cF1, cF2, -, -, -⟩ := hon.1 u hu
  set a := fastNorm 1 r g y u with ha
  set b := fastNorm 2 r g y u with hb
  set c := fastNorm 3 r g y u with hc'
  set cy := hnorm 3 (corrSlow r g y u) with hcy
  set A2 := Real.sqrt (a * b) with hA2
  have ha0 : 0 ≤ a := hnorm_nonneg _ _
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have hc0 : 0 ≤ c := hnorm_nonneg _ _
  have hA0 : 0 ≤ A2 := Real.sqrt_nonneg _
  have hM := nM_nonneg r
  have hc4 := c4_pos
  have hcI := cI_pos
  have hcQ := cQ2_nonneg
  have hW := cp_nonneg caps.WS
  have hbY : b ≤ cp caps.yF := cF2.trans (le_cp _)
  have hroot : A2 ≤ h2Root caps :=
    Real.sqrt_le_sqrt (mul_le_mul (cF1.trans (le_cp _)) hbY hb0 (cp_nonneg _))
  have hX : (cQ2 + 16 * cI) * A2 + 16 * cp caps.WS + 32 * c4 ≤ h2Lc caps := by
    unfold h2Lc
    have := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ cQ2 + 16 * cI)
    linarith
  have hXb : nM r * ((cQ2 + 16 * cI) * A2 + 16 * cp caps.WS + 32 * c4) * b ≤ 3 / 64 := by
    have h1 : A2 * b ≤ h2Lead caps := by
      have := sqrt_mul_mul_le ha0 hb0 (cF1.trans (le_cp _)) hbY
      exact this
    have h2 : nM r * ((cQ2 + 16 * cI) * (A2 * b)) ≤ 2 / 64 :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) hM).trans hlead
    have h3 : nM r * (b * (16 * cp caps.WS + 32 * c4)) ≤ 1 / 64 :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbY (by positivity)) hM).trans hWm
    have e : nM r * ((cQ2 + 16 * cI) * A2 + 16 * cp caps.WS + 32 * c4) * b =
        nM r * ((cQ2 + 16 * cI) * (A2 * b)) + nM r * (b * (16 * cp caps.WS + 32 * c4)) := by ring
    rw [e]
    norm_num at h2 h3 ⊢
    linarith
  have key := budget_core (b := b) (c := c) (cy := cy) (B := resCoeff θ CH μ φ caps) (M := nM r)
    (κ := kap caps r) (Lc := h2Lc caps) (Ly := h2Ly caps) (L0 := h2L0 φ caps)
    (X := (cQ2 + 16 * cI) * A2 + 16 * cp caps.WS + 32 * c4) (h1 := hPsiC φ caps r)
    (α := cSrc * hSrc φ caps / |r|) hb0 hc0 hM (kap_nonneg caps r) (h2Ly_nonneg caps)
    (h2L0_nonneg hφ caps) t1 t2 t3 t4 t5 t6 hN2 hX hXb
  have e : h2RHS r g y u = -pair 2 (PiF (actual r g y u))
        (Qres (PiF (actual r g y u)) (PiF (actual r g y u))) +
      -pair 2 (PiF (actual r g y u)) (Hpsi r g y u) +
      2 * pair 2 (PiF (actual r g y u)) (X1op r (r * u) (slowNL r g y u) (PiF (actual r g y u))) +
      metBil2 r (r * u) (PiS (actual r g y u)) (PiF (actual r g y u)) (fastNL r g y u) +
      -cubicHeat2 r (r * u) (PiF (actual r g y u)) +
      cubicD 2 (-1) r (r * u) (PiF (actual r g y u)) (fastNL r g y u) := by
    unfold h2RHS metBil2
    ring
  rw [e]
  refine key.trans (le_of_eq ?_)
  unfold h2G0 h2G1 h2H1
  ring

end OVNS.Quant.H2

end
