import OddViscousNS.Quant.Regimes.Algebra
import OddViscousNS.Quant.Regimes.Scalar
import OddViscousNS.Quant.Regimes.Barrier
import OddViscousNS.Quant.Regimes.Continuation
import OddViscousNS.Quant.Defs
import OddViscousNS.Closed.Conclusion
import OddViscousNS.Quant.Arith.Resonant.Main
import OddViscousNS.Physical

/-!
# Theorem 1.2, fixed force: the regimes layer against the energy interfaces (glue)

Assembly of `OddViscousNS_data/reports/t12_energy_spec.md` §2.1 over the node files
`Regimes/Algebra.lean` (proved), `Regimes/Scalar.lean` (E6), `Regimes/Barrier.lean` (E10),
`Regimes/Continuation.lean` (R3); see `OddViscousNS_data/reports/t12_regimes_decomposition.md`.

* `fixed_force_normalized` (locked): the normalized fixed-force statement — for `φ, ε` there are
  `C` and `Bd` such that `C (1+μ)^{d+ε} ≤ |r|` gives a global filtered solution with the
  `normalized_main`-shaped bounds.  Its proof is the R1 choice of caps (`CapsScaled` at
  `K = K(φ, δ)`), the two Algebra lemmas paying every threshold (`DegreeBelow.exists_le_rpow`,
  `NearProfiles.leading_paid'`), the strict improvement of the caps on a piece (E6:
  `scalar_peak_on_piece`, `scalar_dissipation_on_piece`; E10: `barrier_cap` with `interp_fast`;
  E7: `SlowCapsInterface`) packaged as `StrictImprovement`, the lookahead bootstrap on the
  maximal solution of `exists_maximal` (`piece_step`, `pieces_induction`), the sliding `H³`
  bound from the `H²` cap (as `sliding_h3` in Induction.lean), and `normalized_main μ₀ φ` for
  the compact range `μ ≤ μ₀`.
* `fixed_force_of_interfaces` (proved from it): the physical statement, by the scaling of
  `global_regularity` and `exists_physical_of_normalized`.
* `quantitative_fixed_force_of_interfaces` (proved from it): `σ = θ = 281/1000`,
  `d = 9876/719` (`dOf_281`); the conclusion is literally that of `quantitative_fixed_force`.

Amendments: D1 (piece length `Tp`), D2 (general degree `d ≥ dOf σ`), D3 (slow exponents `e`);
`0 ≤ K₁, K₂` (leading pair).  Second round (needed by the glue, all three statements):
* `0 < σ` (E6 `scalar_peak_on_piece`/`young_cubic` need it), `0 ≤ C_s` (`young_cubic`);
* `0 < C_H` (`barrier_cap` needs `B = C_H ρ^{1−σ} P_F^σ > 0`; also `B ≥ C_H μ ≥ 1`, i.e.
  `1/λ_* ≤ 1`, for `μ ≥ μ₀ = max 1 (1/C_H)`);
* `m₀ ≤ 1/4` (was `1/2`): the post-clip level `Y₀² ≈ (33/31)e^{m₀−1} y²` must survive the next
  first clip, `(33/31)² e^{2m₀−1} < 1`;
* `1 ≤ e.eA, e.eB, e.eW` (the datum `‖v₀‖₂ ≤ μ` must sit below the slow caps at `t = 0`);
* `0 ≤ N̄(μ, φ)`, `0 ≤ π(μ, φ)` (only `N̄ ≤ Cμ`, `π ≤ Cμ` are assumed; the E6 peak uses `N̄², π²`);
* D4: the slow sub-caps `E_S, A_H, B_H` (`Caps`, `OnPrefix`, `CapsScaled`) and
  `SlowCapsInterface` in the strict-improvement form (start levels `L`), carried by the start
  caps `capsStart` of `GoodPoint`;
* D5: `hN : NativeProfile N` (the native clause `N ≤ C q^{−1/2+δ}`) instead of `NearProfiles N P`.
`ResH1`, `ResH2` are consumed inside the energy interfaces; `fixed_force_normalized` keeps them
(as `_h1`, `_h2`) for the shape of the statement.
Proof structure (all proved): (a) `capsOf`/`capsImp`/`capsOf_scaled`, (b) `thresholds_paid`,
(c) `strict_improvement_of_interfaces` (with `fast_H2_on_piece`, the clipped `c̃_F` trick and
`ae_inH3_fast`), (d) `global_of_strict` (amended `piece_step` + `pieces_induction`),
(e) `sliding_h3'`, (f) `large_regime` + `normalized_main μ₀ φ`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS.Quant

/-- `ResH1 (281/1000)` is the `H¹` conclusion of Proposition quant-resonant (`resonant_H1`),
conditional on the weighted count. -/
theorem resH1_of_weightedCount (hW : WeightedCount) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ResH1 ((281 : ℝ) / 1000) Cs :=
  resonant_H1 hW

/-- `ResH2 (281/1000)` is the `H²` conclusion of Proposition quant-resonant (`resonant_H2`),
conditional on the weighted count. -/
theorem resH2_of_weightedCount (hW : WeightedCount) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ResH2 ((281 : ℝ) / 1000) CH :=
  resonant_H2 hW

/-- A good force stays good for a larger bound (as the private `GoodForce.mono_bound` of
Induction.lean). -/
lemma goodForce_mono {G : ℝ → Field} {Γ Γ' : ℝ} (h : GoodForce G Γ) (hΓ : Γ ≤ Γ') :
    GoodForce G Γ' :=
  ⟨h.adm, fun t ↦ (h.bd t).trans hΓ, h.cont⟩

/-- **(e) The sliding `L²H³` bound** from a uniform `H²` bound (reproof of the private
`sliding_h3` of Induction.lean from `h2_ineq`). -/
lemma sliding_h3' {N : ℝ → Field → Field → Field} {G : ℝ → Field} {φ S : ℝ}
    {y : ℝ → Field} (hN : Majorized N) (hG : GoodForce G φ) (hy : IsHeatSol N G ⊤ y)
    (hS : ∀ t, 0 ≤ t → hnorm 2 (y t) ≤ S) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in t..(t + 1), hnorm 3 (y s) ^ 2 ≤ S ^ 2 + 128 * c4 ^ 2 * S ^ 4 + 2 * φ ^ 2 := by
  have h := h2_ineq hN hG hy ht (by linarith : t ≤ t + 1) ENNReal.ofReal_lt_top
  have hS0 : 0 ≤ S := (hnorm_nonneg 2 _).trans (hS t ht)
  have hbd : ‖∫ u in t..(t + 1), (128 * wiener (y u) ^ 2 * hnorm 2 (y u) ^ 2 + 2 * φ ^ 2)‖ ≤
      (128 * c4 ^ 2 * S ^ 4 + 2 * φ ^ 2) * |t + 1 - t| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu ↦ ?_
    rw [uIoc_of_le (by linarith)] at hu
    have hu0 : 0 ≤ u := ht.trans hu.1.le
    have hadm := hy.adm u hu0 ENNReal.ofReal_lt_top
    have hH := hS u hu0
    have hW : wiener (y u) ≤ c4 * S := (wiener_le ⟨hadm.inH, hadm.mean⟩).trans
      (mul_le_mul_of_nonneg_left hH c4_pos.le)
    have hW0 := wiener_nonneg (y u)
    have hH0 := hnorm_nonneg 2 (y u)
    have h1 : wiener (y u) ^ 2 ≤ (c4 * S) ^ 2 := pow_le_pow_left₀ hW0 hW 2
    have h2 : hnorm 2 (y u) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hH0 hH 2
    have h3 : wiener (y u) ^ 2 * hnorm 2 (y u) ^ 2 ≤ (c4 * S) ^ 2 * S ^ 2 :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith
  have e : |t + 1 - t| = 1 := by simp
  rw [e, mul_one] at hbd
  have hbd' := (le_abs_self _).trans hbd
  have h0 := pow_le_pow_left₀ (hnorm_nonneg 2 _) (hS t ht) 2
  nlinarith [sq_nonneg (hnorm 2 (y (t + 1)))]

/-- One `C (1+μ)^{d+ε} ≤ q` pays a `≤ C' μ^d` threshold once `C' ≤ C`. -/
private lemma pay_one {C C' μ d ε q : ℝ} (hC' : 0 ≤ C') (hCC : C' ≤ C) (hμ : 1 ≤ μ)
    (hd : 0 ≤ d) (hε : 0 ≤ ε) (hq : C * (1 + μ) ^ (d + ε) ≤ q) {x : ℝ} (hx : x ≤ C' * μ ^ d) :
    x ≤ q :=
  hx.trans ((rpow_le_one_add_rpow hC' hμ hd hε).trans ((mul_le_mul_of_nonneg_right hCC
    (Real.rpow_nonneg (by linarith) _)).trans hq))

/-- **(b) All thresholds paid** (R1, spec §3.2): for every cap-scaling constant `K ≥ 1` there is
`δ₀ > 0` such that for `δ ∈ (0, δ₀]` one constant `C ≥ 0` makes `C (1 + μ)^{d+ε} ≤ q` pay the
four non-leading thresholds `q₀, q₁, q₂, q_S` (`DegreeBelow.exists_le_rpow`,
`rpow_le_one_add_rpow`) and both leading conditions (roles 15, 31:
`NearProfiles.leading_paid'`) on every `δ`-scaled cap set, `μ ≥ 1`. -/
private theorem thresholds_paid {σ d K₁ K₂ : ℝ} {e : SlowExp}
    {q₀ q₁ q₂ qS : ℝ → ℝ → Caps → ℝ} {N P : ℝ → ℝ}
    (hσ : 0 ≤ σ ∧ σ < 1) (hd : dOf σ ≤ d) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hN : NearProfiles N P) (hq₀ : DegreeBelow σ d e q₀) (hq₁ : DegreeBelow σ d e q₁)
    (hq₂ : DegreeBelow σ d e q₂) (hqS : DegreeBelow σ d e qS) {φ ε K : ℝ} (hφ : 0 ≤ φ)
    (hε : 0 < ε) (hK : 1 ≤ K) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ μ : ℝ, 1 ≤ μ → ∀ caps : Caps, CapsScaled σ δ K μ e caps → ∀ q : ℝ,
        C * (1 + μ) ^ (d + ε) ≤ q →
        q₀ μ φ caps ≤ q ∧ q₁ μ φ caps ≤ q ∧ q₂ μ φ caps ≤ q ∧ qS μ φ caps ≤ q ∧
        K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * N q ≤ 1 ∧
        K₂ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * N q ≤ 1 := by
  have hd0 : 0 ≤ d := (dOf_pos hσ.1 hσ.2).le.trans hd
  obtain ⟨a₀, ha₀, A₀⟩ := hq₀.exists_le_rpow hφ
  obtain ⟨a₁, ha₁, A₁⟩ := hq₁.exists_le_rpow hφ
  obtain ⟨a₂, ha₂, A₂⟩ := hq₂.exists_le_rpow hφ
  obtain ⟨a₃, ha₃, A₃⟩ := hqS.exists_le_rpow hφ
  obtain ⟨b₁, hb₁, B₁⟩ := hN.leading_paid' e hσ hK₁ hK hε hd
  obtain ⟨b₂, hb₂, B₂⟩ := hN.leading_paid' e hσ hK₂ hK hε hd
  refine ⟨min (min (min a₀ a₁) (min a₂ a₃)) (min b₁ b₂), by positivity, fun δ hδ hδ' => ?_⟩
  simp only [le_min_iff] at hδ'
  obtain ⟨⟨⟨h₀, h₁⟩, h₂, h₃⟩, h₄, h₅⟩ := hδ'
  obtain ⟨C₀, hC₀, D₀⟩ := A₀ δ K hδ h₀ hK
  obtain ⟨C₁, hC₁, D₁⟩ := A₁ δ K hδ h₁ hK
  obtain ⟨C₂, hC₂, D₂⟩ := A₂ δ K hδ h₂ hK
  obtain ⟨C₃, hC₃, D₃⟩ := A₃ δ K hδ h₃ hK
  obtain ⟨L₁, hL₁, E₁⟩ := B₁ δ hδ h₄
  obtain ⟨L₂, hL₂, E₂⟩ := B₂ δ hδ h₅
  refine ⟨C₀ + C₁ + C₂ + C₃ + L₁ + L₂, by positivity, fun μ hμ caps hcaps q hq => ?_⟩
  have hμ0 : 0 < μ := by linarith
  have hlead : ∀ L : ℝ, 0 ≤ L → L ≤ C₀ + C₁ + C₂ + C₃ + L₁ + L₂ → L * μ ^ (d + ε) ≤ q :=
    fun L hL hLC => (mul_le_mul hLC (Real.rpow_le_rpow hμ0.le (by linarith) (by linarith))
      (Real.rpow_nonneg hμ0.le _) (by positivity)).trans hq
  refine ⟨pay_one hC₀ (by linarith) hμ hd0 hε.le hq (D₀ μ hμ caps hcaps),
    pay_one hC₁ (by linarith) hμ hd0 hε.le hq (D₁ μ hμ caps hcaps),
    pay_one hC₂ (by linarith) hμ hd0 hε.le hq (D₂ μ hμ caps hcaps),
    pay_one hC₃ (by linarith) hμ hd0 hε.le hq (D₃ μ hμ caps hcaps),
    E₁ μ hμ caps hcaps q (hlead L₁ (by linarith) (by linarith)),
    E₂ μ hμ caps hcaps q (hlead L₂ (by linarith) (by linarith))⟩

/-! ### Arithmetic for the R1 caps -/

/-- The exponential factors of the barrier for `0 ≤ m₀ ≤ 1/4`. -/
lemma exp_bounds {m₀ : ℝ} (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4) :
    Real.exp m₀ ≤ 13 / 10 ∧ Real.exp (m₀ - 1) ≤ 1 / 2 := by
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have h4 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h34 : Real.exp (3 / 4) ^ 4 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have hp1 := Real.exp_pos (1 / 4)
  have hp3 := Real.exp_pos (3 / 4)
  have hb1 : Real.exp (1 / 4) ≤ 13 / 10 := by
    by_contra h
    push Not at h
    have : (13 / 10 : ℝ) ^ 4 < Real.exp (1 / 4) ^ 4 :=
      pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    nlinarith
  have hb3 : 2 ≤ Real.exp (3 / 4) := by
    by_contra h
    push Not at h
    have : Real.exp (3 / 4) ^ 4 < 2 ^ 4 := pow_lt_pow_left₀ h hp3.le (by norm_num)
    have h3 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 := pow_lt_pow_left₀ he' (by norm_num)
      (by norm_num)
    nlinarith
  refine ⟨(Real.exp_le_exp.2 hm₀.2).trans hb1, ?_⟩
  have h1 : Real.exp (m₀ - 1) ≤ Real.exp (-(3 / 4)) := Real.exp_le_exp.2 (by linarith)
  rw [Real.exp_neg] at h1
  refine h1.trans ?_
  rw [inv_le_comm₀ hp3 (by norm_num)]
  linarith

/-- `β = betaOf σ ≥ 2` and `vOf σ = 1 + 2(β − 1)`. -/
private lemma vOf_eq (σ : ℝ) : vOf σ = 1 + 2 * (betaOf σ - 1) := by
  unfold vOf
  ring

/-- `1 − σ + βσ = β − 1`. -/
private lemma beta_identity {σ : ℝ} (hσ : σ < 1) : 1 - σ + betaOf σ * σ = betaOf σ - 1 := by
  unfold betaOf
  have h : (1 - σ) ≠ 0 := by linarith
  field_simp
  ring

/-- The power `p = μ^{β−1}` and the cap monomials in terms of it. -/
private lemma rpow_facts {σ μ : ℝ} (hσ : 0 < σ ∧ σ < 1) (hμ : 1 ≤ μ) :
    μ ^ betaOf σ = μ * μ ^ (betaOf σ - 1) ∧ μ ^ vOf σ = μ * (μ ^ (betaOf σ - 1)) ^ 2 ∧
      μ ^ (2 * betaOf σ) = (μ * μ ^ (betaOf σ - 1)) ^ 2 ∧
      μ ^ (1 - σ) * (μ * μ ^ (betaOf σ - 1)) ^ σ = μ ^ (betaOf σ - 1) ∧
      μ ≤ μ ^ (betaOf σ - 1) := by
  have hμ0 : 0 < μ := by linarith
  have hβ := two_le_betaOf hσ.1.le hσ.2
  have h1 : μ ^ betaOf σ = μ * μ ^ (betaOf σ - 1) := by
    conv_lhs => rw [show betaOf σ = 1 + (betaOf σ - 1) by ring]
    rw [Real.rpow_add hμ0, Real.rpow_one]
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · rw [vOf_eq, Real.rpow_add hμ0, Real.rpow_one, mul_comm 2 (betaOf σ - 1),
      Real.rpow_mul hμ0.le, Real.rpow_two]
  · rw [← h1, mul_comm 2 (betaOf σ), Real.rpow_mul hμ0.le, Real.rpow_two]
  · rw [← h1, ← Real.rpow_mul hμ0.le, ← Real.rpow_add hμ0, beta_identity hσ.2]
  · calc μ = μ ^ (1 : ℝ) := (Real.rpow_one μ).symm
      _ ≤ μ ^ (betaOf σ - 1) := Real.rpow_le_rpow_of_exponent_le hμ (by linarith)

/-- `((Z^{β/2} μ p)²)^{1 − 1/β} = Z^{β−1} p²` and `(Z^{β/2})² = Z · Z^{β−1}`. -/
private lemma peak_rpow {σ μ Z : ℝ} (hσ : 0 < σ ∧ σ < 1) (hμ : 1 ≤ μ) (hZ : 1 ≤ Z) :
    ((Z ^ (betaOf σ / 2) * μ ^ betaOf σ) ^ 2) ^ (1 - 1 / betaOf σ) =
        Z ^ (betaOf σ - 1) * (μ ^ (betaOf σ - 1)) ^ 2 ∧
      (Z ^ (betaOf σ / 2)) ^ 2 = Z * Z ^ (betaOf σ - 1) := by
  have hμ0 : 0 < μ := by linarith
  have hZ0 : 0 < Z := by linarith
  have hβ := two_le_betaOf hσ.1.le hσ.2
  have hb0 : betaOf σ ≠ 0 := by linarith
  have hsq : (Z ^ (betaOf σ / 2)) ^ 2 = Z ^ betaOf σ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hZ0.le]
    ring_nf
  refine ⟨?_, ?_⟩
  · rw [mul_pow, hsq, ← Real.rpow_two (μ ^ betaOf σ), ← Real.rpow_mul hμ0.le,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hZ0.le,
      ← Real.rpow_mul hμ0.le, ← Real.rpow_two (μ ^ (betaOf σ - 1)), ← Real.rpow_mul hμ0.le]
    congr 2
    · field_simp
    · field_simp
  · rw [hsq]
    conv_lhs => rw [show betaOf σ = 1 + (betaOf σ - 1) by ring]
    rw [Real.rpow_add hZ0, Real.rpow_one]

/-- `e (2/ℓ₁) ≤ 6`, `1 ≤ e (2/ℓ₁)`, `u₁ ≤ 2`, `0 < ℓ₁ ≤ 1`. -/
private lemma consts_bounds :
    Real.exp 1 * (2 / ell1) ≤ 6 ∧ 1 ≤ Real.exp 1 * (2 / ell1) ∧ u1 ≤ 2 ∧ 0 < ell1 ∧
      ell1 ≤ 1 := by
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have hl : (99 : ℝ) / 100 ≤ ell1 := by unfold ell1; norm_num
  have hl1 : ell1 ≤ 1 := by unfold ell1; norm_num
  have hl0 : 0 < ell1 := by linarith
  refine ⟨?_, ?_, by unfold u1; norm_num, hl0, hl1⟩
  · rw [mul_div_assoc', div_le_iff₀ hl0]
    nlinarith
  · rw [mul_div_assoc', le_div_iff₀ hl0]
    nlinarith

/-- **E6 peak arithmetic**: with `P_F = Z^{β/2} μ^β`, `M_f = 2μ`, `λ = 1/4`, `I_a ≤ (Tp+5)μ²`,
`N̄ ≤ C_N μ`, `π ≤ C_π μ` and `Z ≥ 48(4 + C_N² + C_π²) + 48 c_y (Tp + 5) + 1`, the E6 peak is
`≤ (P_F/2)²`. -/
lemma peak_le {σ μ cy CN Cp Tp Z Nb pt Ia : ℝ} (hσ : 0 < σ ∧ σ < 1) (hμ : 1 ≤ μ)
    (hcy : 0 ≤ cy) (hTp : 0 ≤ Tp)
    (hZ : 48 * (4 + CN ^ 2 + Cp ^ 2) + 48 * cy * (Tp + 5) + 1 ≤ Z)
    (hNb0 : 0 ≤ Nb) (hNb : Nb ≤ CN * μ) (hpt0 : 0 ≤ pt) (hpt : pt ≤ Cp * μ) (hIa0 : 0 ≤ Ia)
    (hIa : Ia ≤ (Tp + 5) * μ ^ 2) :
    peakSq σ cy (1 / 4) (2 * μ) (Z ^ (betaOf σ / 2) * μ ^ betaOf σ) Ia Nb pt ≤
      (Z ^ (betaOf σ / 2) * μ ^ betaOf σ / 2) ^ 2 := by
  have hZ1 : 1 ≤ Z := by
    have : 0 ≤ cy * (Tp + 5) := mul_nonneg hcy (by linarith)
    have e3 : 48 * cy * (Tp + 5) = 48 * (cy * (Tp + 5)) := by ring
    rw [e3] at hZ
    linarith only [hZ, this, sq_nonneg CN, sq_nonneg Cp]
  have hZ0 : 0 < Z := by linarith
  obtain ⟨hpr, hsq⟩ := peak_rpow hσ hμ hZ1
  obtain ⟨h1, -, -, -, hμp⟩ := rpow_facts hσ hμ
  obtain ⟨hE, -, hu, -, -⟩ := consts_bounds
  have hβ := two_le_betaOf hσ.1.le hσ.2
  set p := μ ^ (betaOf σ - 1) with hp
  set Q := Z ^ (betaOf σ - 1) with hQ
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hZ1 (by linarith)
  have hp1 : 1 ≤ p := hμ.trans hμp
  have hX : μ ^ 2 ≤ Q * p ^ 2 * μ ^ 2 := by
    have : 1 ≤ Q * p ^ 2 := one_le_mul_of_one_le_of_one_le hQ1 (one_le_pow₀ hp1)
    have := mul_le_mul_of_nonneg_right this (sq_nonneg μ)
    linarith only [this]
  have hNb2 : Nb ^ 2 ≤ CN ^ 2 * μ ^ 2 := by
    have := pow_le_pow_left₀ hNb0 hNb 2
    nlinarith
  have hpt2 : pt ^ 2 ≤ Cp ^ 2 * μ ^ 2 := by
    have := pow_le_pow_left₀ hpt0 hpt 2
    nlinarith
  have hcyI : cy * (Q * p ^ 2) * Ia ≤ cy * (Tp + 5) * (Q * p ^ 2 * μ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hIa (mul_nonneg hcy (by positivity : 0 ≤ Q * p ^ 2))
    nlinarith
  have hinner : u1 * (2 * μ) ^ 2 / 2 + cy * (Q * p ^ 2) * Ia + Nb ^ 2 / (4 * (3 / 4 - 1 / 4)) +
      pt ^ 2 ≤ (4 + CN ^ 2 + Cp ^ 2 + cy * (Tp + 5)) * (Q * p ^ 2 * μ ^ 2) := by
    have hu0 : 0 ≤ u1 := by unfold u1; norm_num
    have hu' : u1 * (2 * μ) ^ 2 / 2 ≤ 4 * μ ^ 2 := by
      have : u1 * (2 * μ) ^ 2 / 2 = u1 * (2 * μ ^ 2) := by ring
      rw [this]
      have : 0 ≤ 2 * μ ^ 2 := by positivity
      nlinarith
    have e : Nb ^ 2 / (4 * (3 / 4 - 1 / 4)) = Nb ^ 2 / 2 := by norm_num
    rw [e]
    have hN2 : 0 ≤ Nb ^ 2 := sq_nonneg _
    have hc1 := mul_le_mul_of_nonneg_left hX (sq_nonneg CN)
    have hc2 := mul_le_mul_of_nonneg_left hX (sq_nonneg Cp)
    have hc3 := mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 4)
    have e2 : (4 + CN ^ 2 + Cp ^ 2 + cy * (Tp + 5)) * (Q * p ^ 2 * μ ^ 2) =
        4 * (Q * p ^ 2 * μ ^ 2) + CN ^ 2 * (Q * p ^ 2 * μ ^ 2) + Cp ^ 2 * (Q * p ^ 2 * μ ^ 2) +
          cy * (Tp + 5) * (Q * p ^ 2 * μ ^ 2) := by ring
    rw [e2]
    linarith
  have hin0 : 0 ≤ u1 * (2 * μ) ^ 2 / 2 + cy * (Q * p ^ 2) * Ia +
      Nb ^ 2 / (4 * (3 / 4 - 1 / 4)) + pt ^ 2 := by
    have hu0 : 0 ≤ u1 := by unfold u1; norm_num
    positivity
  unfold peakSq
  rw [hpr, h1]
  have hR : (Z ^ (betaOf σ / 2) * (μ * p) / 2) ^ 2 = Z * (Q * p ^ 2 * μ ^ 2) / 4 := by
    rw [div_pow, mul_pow, hsq]
    ring
  rw [hR]
  have hXp : 0 ≤ Q * p ^ 2 * μ ^ 2 := by positivity
  calc Real.exp 1 * (2 / ell1) * (u1 * (2 * μ) ^ 2 / 2 + cy * (Q * p ^ 2) * Ia +
        Nb ^ 2 / (4 * (3 / 4 - 1 / 4)) + pt ^ 2)
      ≤ 6 * ((4 + CN ^ 2 + Cp ^ 2 + cy * (Tp + 5)) * (Q * p ^ 2 * μ ^ 2)) :=
        mul_le_mul hE hinner hin0 (by norm_num)
    _ ≤ Z * (Q * p ^ 2 * μ ^ 2) / 4 := by
        have hc : 0 ≤ cy * (Tp + 5) := mul_nonneg hcy (by linarith)
        have h24 : 24 * (4 + CN ^ 2 + Cp ^ 2 + cy * (Tp + 5)) ≤ Z := by
          have e3 : 48 * cy * (Tp + 5) = 48 * (cy * (Tp + 5)) := by ring
          rw [e3] at hZ
          linarith only [hZ, hc, sq_nonneg CN, sq_nonneg Cp]
        have := mul_le_mul_of_nonneg_right h24 hXp
        linarith only [this]

/-- **E6 dissipation arithmetic** (`λ = 1/4`): `dissipSq ≤ 4 N̄² + 8 peakSq`. -/
lemma dissip_le {σ cy Mf PF Ia Nb pt : ℝ} (hcy : 0 ≤ cy) (hIa : 0 ≤ Ia) :
    dissipSq σ cy (1 / 4) Mf PF Ia Nb pt ≤ 4 * Nb ^ 2 + 8 * peakSq σ cy (1 / 4) Mf PF Ia Nb pt := by
  obtain ⟨-, hE1, -, hl0, hl1⟩ := consts_bounds
  have hu0 : 0 ≤ u1 := by unfold u1; norm_num
  set R := (PF ^ 2) ^ (1 - 1 / betaOf σ) with hR
  have hR0 : 0 ≤ R := Real.rpow_nonneg (sq_nonneg _) _
  set T := u1 * Mf ^ 2 / 2 + cy * R * Ia + Nb ^ 2 / (4 * (3 / 4 - 1 / 4)) + pt ^ 2 with hT
  have hT0 : 0 ≤ T := by positivity
  have hP : peakSq σ cy (1 / 4) Mf PF Ia Nb pt = Real.exp 1 * (2 / ell1) * T := rfl
  have hPT : T ≤ peakSq σ cy (1 / 4) Mf PF Ia Nb pt := by
    rw [hP]
    nlinarith
  set P := peakSq σ cy (1 / 4) Mf PF Ia Nb pt with hPdef
  set X := u1 * Mf ^ 2 / 2 + cy * R * Ia + pt ^ 2 + ell1 / 2 * P with hX
  have hP0 : 0 ≤ P := hT0.trans hPT
  have hX0 : 0 ≤ X := by positivity
  have hX2 : X ≤ 2 * P := by
    have : u1 * Mf ^ 2 / 2 + cy * R * Ia + pt ^ 2 ≤ T := by
      rw [hT]
      have : 0 ≤ Nb ^ 2 / (4 * (3 / 4 - 1 / 4)) := by positivity
      linarith
    nlinarith
  have hD : dissipSq σ cy (1 / 4) Mf PF Ia Nb pt =
      (|Nb| + Real.sqrt (Nb ^ 2 + 2 * X)) ^ 2 := by
    unfold dissipSq
    rw [← hR, ← hPdef, ← hX]
    norm_num
  rw [hD]
  have hs := Real.sq_sqrt (by positivity : 0 ≤ Nb ^ 2 + 2 * X)
  have ha : |Nb| ^ 2 = Nb ^ 2 := sq_abs Nb
  nlinarith [sq_nonneg (|Nb| - Real.sqrt (Nb ^ 2 + 2 * X))]

/-! ### (a) The R1 caps -/

/-- **(a) The R1 caps** at datum radius `μ` (spec §1.2, §3.1): `P_F = K_P μ^β`, `y = K_Y μ^v`,
`J_F = K_J μ^{2β}`, the slow caps `2 C_{S1} μ^{e}` and the slow sub-caps `2 C_{S1} μ`,
`2 C_{S1} μ`, `2 C_{S1} μ²` (D4). -/
private noncomputable def capsOf (σ KP KY KJ Cs1 μ : ℝ) (e : SlowExp) : Caps :=
  ⟨KP * μ ^ betaOf σ, KY * μ ^ vOf σ, 2 * Cs1 * μ ^ e.eA, 2 * Cs1 * μ ^ e.eB,
    2 * Cs1 * μ ^ e.eW, KJ * μ ^ (2 * betaOf σ), 2 * Cs1 * μ ^ e.eJ, 2 * Cs1 * μ, 2 * Cs1 * μ,
    2 * Cs1 * μ ^ 2⟩

/-- The improved caps: `P_F/2`, `(19/20) y`, `J_F/2` and half of every slow cap. -/
private noncomputable def capsImp (σ KP KY KJ Cs1 μ : ℝ) (e : SlowExp) : Caps :=
  ⟨KP * μ ^ betaOf σ / 2, 19 / 20 * (KY * μ ^ vOf σ), Cs1 * μ ^ e.eA, Cs1 * μ ^ e.eB,
    Cs1 * μ ^ e.eW, KJ * μ ^ (2 * betaOf σ) / 2, Cs1 * μ ^ e.eJ, Cs1 * μ, Cs1 * μ, Cs1 * μ ^ 2⟩

/-- The start levels `c0` of a good point: the improved fast `H¹` cap, the post-clip fast `H²`
level `(4/5) y`, and the slow start levels `L` of `SlowCapsInterface`. -/
private noncomputable def capsStart (σ KP KY KJ Cs1 μ : ℝ) (e : SlowExp) (L : Fin 5 → ℝ) :
    Caps :=
  ⟨KP * μ ^ betaOf σ / 2, 4 / 5 * (KY * μ ^ vOf σ), L 3 * μ ^ e.eA, L 4 * μ ^ e.eB,
    Cs1 * μ ^ e.eW, KJ * μ ^ (2 * betaOf σ) / 2, Cs1 * μ ^ e.eJ, L 0 * μ, L 1 * μ, L 2 * μ ^ 2⟩

/-- The improved caps lie strictly below the caps. -/
private lemma capsImp_below {σ KP KY KJ Cs1 μ : ℝ} {e : SlowExp} (hKP : 0 < KP) (hKY : 0 < KY)
    (hKJ : 0 < KJ) (hC : 0 < Cs1) (hμ : 0 < μ) :
    (capsImp σ KP KY KJ Cs1 μ e).Below (capsOf σ KP KY KJ Cs1 μ e) := by
  have h1 := Real.rpow_pos_of_pos hμ (betaOf σ)
  have h2 := Real.rpow_pos_of_pos hμ (vOf σ)
  have h3 := Real.rpow_pos_of_pos hμ (2 * betaOf σ)
  have hA := Real.rpow_pos_of_pos hμ e.eA
  have hB := Real.rpow_pos_of_pos hμ e.eB
  have hW := Real.rpow_pos_of_pos hμ e.eW
  have hJ := Real.rpow_pos_of_pos hμ e.eJ
  have hμ2 : 0 < μ ^ 2 := by positivity
  simp only [Caps.Below, capsImp, capsOf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_pos hKP h1,
    mul_pos hKY h2, mul_pos hKJ h3, mul_pos hC hA, mul_pos hC hB, mul_pos hC hW, mul_pos hC hJ,
    mul_pos hC hμ, mul_pos hC hμ2]

/-- A coefficient below `K` with exponent `≤` the scaled one. -/
private lemma le_K_rpow {c K μ a b : ℝ} (hcK : c ≤ K) (hc : 0 ≤ c) (hμ : 1 ≤ μ) (hab : a ≤ b) :
    c * μ ^ a ≤ K * μ ^ b :=
  mul_le_mul hcK (Real.rpow_le_rpow_of_exponent_le hμ hab) (Real.rpow_nonneg (by linarith) _)
    (hc.trans hcK)

/-- `μ^a / K ≤ c μ^a` for `K, c ≥ 1`. -/
private lemma div_K_le {c K μ a : ℝ} (hc : 1 ≤ c) (hK : 1 ≤ K) (hμ : 0 < μ) :
    μ ^ a / K ≤ c * μ ^ a := by
  have h := Real.rpow_pos_of_pos hμ a
  rw [div_le_iff₀ (by linarith)]
  have h1 : 1 ≤ c * K := one_le_mul_of_one_le_of_one_le hc hK
  nlinarith [mul_le_mul_of_nonneg_left h1 h.le]

/-- The caps are `CapsScaled` with any `K` dominating the coefficients. -/
private lemma capsOf_scaled {σ δ K KP KY KJ Cs1 μ : ℝ} {e : SlowExp} (hδ : 0 ≤ δ) (hμ : 1 ≤ μ)
    (hKP : 1 ≤ KP) (hKY : 1 ≤ KY) (hKJ : 1 ≤ KJ) (hC : 0 ≤ Cs1) (hK1 : KP ≤ K) (hK2 : KY ≤ K)
    (hK3 : KJ ≤ K) (hK4 : 2 * Cs1 ≤ K) :
    CapsScaled σ δ K μ e (capsOf σ KP KY KJ Cs1 μ e) := by
  have hμ0 : 0 < μ := by linarith
  have hK : 1 ≤ K := hKP.trans hK1
  have hC2 : 0 ≤ 2 * Cs1 := by linarith
  refine ⟨⟨div_K_le hKP hK hμ0, le_K_rpow hK1 (by linarith) hμ le_rfl⟩,
    ⟨div_K_le hKY hK hμ0, le_K_rpow hK2 (by linarith) hμ le_rfl⟩,
    ⟨div_K_le hKJ hK hμ0, le_K_rpow hK3 (by linarith) hμ le_rfl⟩,
    le_K_rpow hK4 hC2 hμ (by linarith), le_K_rpow hK4 hC2 hμ (by linarith),
    le_K_rpow hK4 hC2 hμ (by linarith), le_K_rpow hK4 hC2 hμ (by linarith), ?_, ?_, ?_⟩
  all_goals simp only [capsOf]
  · have h := le_K_rpow (a := 1) hK4 hC2 hμ (by linarith : (1 : ℝ) ≤ 1 + δ)
    rwa [Real.rpow_one] at h
  · have h := le_K_rpow (a := 1) hK4 hC2 hμ (by linarith : (1 : ℝ) ≤ 1 + δ)
    rwa [Real.rpow_one] at h
  · have h := le_K_rpow (a := 2) hK4 hC2 hμ (by linarith : (2 : ℝ) ≤ 2 + δ)
    rwa [Real.rpow_two] at h

/-- Bounds on the resonant coefficient `B = C_H ρ^{1−σ} P_F^σ` at `P_F = K_P μ^β`:
`C_H μ ≤ B ≤ C_H (6 + 4φ) K_P μ^{β−1}`. -/
private lemma resCoeff_bounds {σ CH μ φ KP : ℝ} {c : Caps} (hσ : 0 < σ ∧ σ < 1) (hCH : 0 ≤ CH)
    (hμ : 1 ≤ μ) (hφ : 0 ≤ φ) (hKP : 1 ≤ KP) (hPF : c.PF = KP * μ ^ betaOf σ) :
    CH * μ ≤ resCoeff σ CH μ φ c ∧
      resCoeff σ CH μ φ c ≤ CH * (6 + 4 * φ) * KP * μ ^ (betaOf σ - 1) := by
  obtain ⟨h1, -, -, h5, hμp⟩ := rpow_facts hσ hμ
  have hμ0 : 0 < μ := by linarith
  have hρ : μ ≤ rhoOf μ φ := by unfold rhoOf; linarith
  have hρ' : rhoOf μ φ ≤ (6 + 4 * φ) * μ := by unfold rhoOf; nlinarith
  have hs1 : 0 ≤ 1 - σ := by linarith
  set p := μ ^ (betaOf σ - 1)
  have hmp0 : 0 ≤ μ * p := by positivity
  unfold resCoeff
  rw [hPF, h1]
  have hPσ : (μ * p) ^ σ ≤ (KP * (μ * p)) ^ σ :=
    Real.rpow_le_rpow hmp0 (le_mul_of_one_le_left hmp0 hKP) hσ.1.le
  have hPσ' : (KP * (μ * p)) ^ σ ≤ KP * (μ * p) ^ σ := by
    rw [Real.mul_rpow (by linarith) hmp0]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hmp0 _)
    calc KP ^ σ ≤ KP ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hKP hσ.2.le
      _ = KP := Real.rpow_one KP
  have hρσ : μ ^ (1 - σ) ≤ rhoOf μ φ ^ (1 - σ) := Real.rpow_le_rpow hμ0.le hρ hs1
  have hρσ' : rhoOf μ φ ^ (1 - σ) ≤ (6 + 4 * φ) * μ ^ (1 - σ) := by
    calc rhoOf μ φ ^ (1 - σ) ≤ ((6 + 4 * φ) * μ) ^ (1 - σ) :=
          Real.rpow_le_rpow (by unfold rhoOf; linarith) hρ' hs1
      _ = (6 + 4 * φ) ^ (1 - σ) * μ ^ (1 - σ) := Real.mul_rpow (by linarith) hμ0.le
      _ ≤ (6 + 4 * φ) ^ (1 : ℝ) * μ ^ (1 - σ) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith)
            (by linarith)) (Real.rpow_nonneg hμ0.le _)
      _ = (6 + 4 * φ) * μ ^ (1 - σ) := by rw [Real.rpow_one]
  have hA0 : 0 ≤ μ ^ (1 - σ) := Real.rpow_nonneg hμ0.le _
  have hB0 : 0 ≤ (μ * p) ^ σ := Real.rpow_nonneg hmp0 _
  constructor
  · calc CH * μ ≤ CH * p := mul_le_mul_of_nonneg_left hμp hCH
      _ = CH * (μ ^ (1 - σ) * (μ * p) ^ σ) := by rw [h5]
      _ ≤ CH * (rhoOf μ φ ^ (1 - σ) * (KP * (μ * p)) ^ σ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hρσ hPσ hB0 (hA0.trans hρσ)) hCH
      _ = CH * rhoOf μ φ ^ (1 - σ) * (KP * (μ * p)) ^ σ := by ring
  · calc CH * rhoOf μ φ ^ (1 - σ) * (KP * (μ * p)) ^ σ
        = CH * (rhoOf μ φ ^ (1 - σ) * (KP * (μ * p)) ^ σ) := by ring
      _ ≤ CH * (((6 + 4 * φ) * μ ^ (1 - σ)) * (KP * (μ * p) ^ σ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hρσ' hPσ' (Real.rpow_nonneg (by positivity) _)
            (by positivity)) hCH
      _ = CH * (6 + 4 * φ) * KP * (μ ^ (1 - σ) * (μ * p) ^ σ) := by ring
      _ = CH * (6 + 4 * φ) * KP * p := by rw [h5]

/-- `λ_* = (16/11) B²` for `A > 0`; hence `1/λ_* ≤ 1` once `B ≥ 1`. -/
lemma inv_lamStar_le {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B) : 1 / lamStar 1 A B ≤ 1 := by
  have e : lamStar 1 A B = 16 / 11 * B ^ 2 := by
    unfold lamStar bStar dZero
    field_simp
    ring
  rw [e, div_le_one (by positivity)]
  nlinarith

/-- `W_* ≤ 3 A² B²`. -/
lemma WStar_le (A B : ℝ) : WStar 1 A B ≤ 3 * (A * B) ^ 2 := by
  unfold WStar bStar dZero
  have : 0 ≤ (A * B) ^ 2 := sq_nonneg _
  have e : 33 / 32 * (1 * A * B / (2 / 3)) ^ 2 = 297 / 128 * (A * B) ^ 2 := by ring
  rw [e]
  linarith

/-- **E10 arithmetic, first clip**: from the incoming trace `b_F(s) ≤ Y₀ = (4/5) y`. -/
lemma first_clip_arith {b W Ws Wst Cb e₀ yF : ℝ} (hb : 0 ≤ b) (hyF : 0 ≤ yF)
    (hbW : 31 / 32 * b ^ 2 ≤ W) (hW : W ≤ e₀ * (Ws + Cb * Wst)) (he : e₀ ≤ 13 / 10)
    (he0 : 0 ≤ e₀) (hWs : Ws ≤ 33 / 32 * (4 / 5 * yF) ^ 2) (hCW0 : 0 ≤ Cb * Wst)
    (hCW : Cb * Wst ≤ yF ^ 2 / 100) : b ≤ 19 / 20 * yF := by
  have h1 : Ws + Cb * Wst ≤ 33 / 32 * (4 / 5 * yF) ^ 2 + yF ^ 2 / 100 := by linarith
  have h2 : e₀ * (Ws + Cb * Wst) ≤ 13 / 10 * (33 / 32 * (4 / 5 * yF) ^ 2 + yF ^ 2 / 100) := by
    have hY : 0 ≤ 33 / 32 * (4 / 5 * yF) ^ 2 + yF ^ 2 / 100 := by positivity
    rcases le_total 0 (Ws + Cb * Wst) with hWs0 | hWs0
    · exact mul_le_mul he h1 hWs0 (by norm_num)
    · nlinarith
  have h3 : b ^ 2 ≤ (19 / 20 * yF) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ hb (by positivity) (by norm_num)).1 h3

/-- **E10 arithmetic, after a full clip**: back below `Y₀ = (4/5) y`. -/
lemma full_clip_arith {b W Wst Cb e₁ yF : ℝ} (hb : 0 ≤ b) (hyF : 0 ≤ yF)
    (hbW : 31 / 32 * b ^ 2 ≤ W) (hW : W ≤ e₁ * (33 / 32) * yF ^ 2 + Cb * Wst)
    (he : e₁ ≤ 1 / 2) (hCW : Cb * Wst ≤ yF ^ 2 / 100) : b ≤ 4 / 5 * yF := by
  have h1 : e₁ * (33 / 32) * yF ^ 2 ≤ 1 / 2 * (33 / 32) * yF ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h3 : b ^ 2 ≤ (4 / 5 * yF) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ hb (by positivity) (by norm_num)).1 h3

/-! ### (c) Strict improvement on a piece -/

/-- The conclusion of `barrier_cap` for a fixed constant `Cb`. -/
def BarrierProp (m₀ Cb : ℝ) : Prop :=
  ∀ {A B s t : ℝ} {W G H bF cF : ℝ → ℝ}, 0 < A → 0 < B → s ≤ t →
    ContinuousOn bF (Icc s t) → (∀ u, 0 ≤ bF u) →
    (∀ u ∈ Icc s t, 31 / 32 * bF u ^ 2 ≤ W u ∧ W u ≤ 33 / 32 * bF u ^ 2) →
    (∀ u ∈ Icc s t, bF u ^ 2 ≤ A * cF u) →
    IntervalIntegrable (fun u => cF u ^ 2) volume s t →
    (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      W u₂ - W u₁ ≤ ∫ u in u₁..u₂,
        (-2 * dZero * cF u ^ 2 + 2 * B * bF u * cF u + G u * W u + H u)) →
    (∀ u ∈ Icc s t, 0 ≤ G u ∧ 0 ≤ H u) →
    IntervalIntegrable G volume s t → IntervalIntegrable H volume s t →
    (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ 1 / lamStar 1 A B →
      (∫ u in u₁..u₂, G u) ≤ m₀ ∧ (∫ u in u₁..u₂, H u) ≤ WStar 1 A B / 32) →
    ∀ v ∈ Icc s t,
      (v - s ≤ 1 / lamStar 1 A B → W v ≤ Real.exp m₀ * (W s + Cb * WStar 1 A B)) ∧
      (1 / lamStar 1 A B ≤ v - s → ∀ Y : ℝ, (∀ u ∈ Icc s t, bF u ≤ Y) →
        W v ≤ Real.exp (m₀ - 1) * (33 / 32) * Y ^ 2 + Cb * WStar 1 A B)

/-- **E10 on a piece**: the fast `H²` cap improves to `(19/20) y`, and after the first unit
(`1/λ_* ≤ 1`) it is back below `Y₀ = (4/5) y`.  `barrier_cap` is applied with the clipped
`c̃_F = max(c_F, b_F²/P_F)`, which equals `c_F` at almost every time (`ae_inH3_fast`,
`interp_fast`), so that the interpolation `b_F² ≤ P_F c̃_F` holds at every time. -/
private lemma fast_H2_on_piece {σ CH μ φ Tp K₂ m₀ Cb : ℝ} {q₂ : Caps → ℝ} {N : ℝ → ℝ}
    (hE2 : H2EnergyInterface σ CH μ φ Tp K₂ m₀ q₂ N) (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4)
    (hCb : 0 ≤ Cb) (hbar : BarrierProp m₀ Cb)
    {r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps} {s t : ℝ}
    (hsol : ActualSol μ φ r g y Ty) (hpiece : PieceHyp Tp q₂ r g y Ty caps s t)
    (hlead : K₂ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * N |r| ≤ 1)
    (hA : 0 < caps.PF) (hB : 1 ≤ resCoeff σ CH μ φ caps) (hyF : 0 ≤ caps.yF)
    (hCW : Cb * WStar 1 caps.PF (resCoeff σ CH μ φ caps) ≤ caps.yF ^ 2 / 100)
    (hin : fastNorm 2 r g y s ≤ 4 / 5 * caps.yF) :
    (∀ v ∈ Icc s t, fastNorm 2 r g y v ≤ 19 / 20 * caps.yF) ∧
      ∀ v ∈ Icc (s + 1) t, fastNorm 2 r g y v ≤ 4 / 5 * caps.yF := by
  have hs := hpiece.hs
  have hst := hpiece.hst
  have ht := hpiece.ht
  have hon := hpiece.onPrefix
  obtain ⟨W, G, H, hco, hc3, hineq, hGH, hGi, hHi, hclip⟩ := hE2 r g y Ty caps s t hsol hpiece hlead
  set A := caps.PF with hAdef
  set B := resCoeff σ CH μ φ caps with hBdef
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
    have haF := (hon.1 u hmem).1
    have hc0 : 0 ≤ c3 u := hnorm_nonneg _ _
    have : bF u ^ 2 / A ≤ c3 u := by
      rw [div_le_iff₀ hA]
      calc bF u ^ 2 ≤ fastNorm 1 r g y u * c3 u := hip
        _ ≤ A * c3 u := mul_le_mul_of_nonneg_right haF hc0
        _ = c3 u * A := by ring
    exact max_eq_left this
  have haeI : ∀ {a b : ℝ}, s ≤ a → a ≤ b → b ≤ t → ∀ᵐ u, u ∈ uIoc a b → cF u = c3 u := by
    intro a b ha hab hb
    filter_upwards [hae] with u hu hmem
    rw [uIoc_of_le hab] at hmem
    exact hu ⟨ha.trans hmem.1.le, hmem.2.trans hb⟩
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
  have hYb : ∀ u ∈ Icc s t, bF u ≤ caps.yF := fun u hu ↦ (hon.1 u hu).2.1
  have hfull : ∀ v ∈ Icc s t, 1 / lamStar 1 A B ≤ v - s → bF v ≤ 4 / 5 * caps.yF := by
    intro v hv hle
    exact full_clip_arith (hb0 v) hyF (hco v hv).1 ((hbarv v hv).2 hle caps.yF hYb) he1 hCW
  refine ⟨fun v hv ↦ ?_, fun v hv ↦ hfull v ⟨by linarith [hv.1], hv.2⟩ (by linarith [hv.1])⟩
  rcases le_total (v - s) (1 / lamStar 1 A B) with hle | hle
  · have hWs : W s ≤ 33 / 32 * (4 / 5 * caps.yF) ^ 2 := by
      have h1 := (hco s ⟨le_rfl, hst⟩).2
      have h2 : bF s ^ 2 ≤ (4 / 5 * caps.yF) ^ 2 := pow_le_pow_left₀ (hb0 s) hin 2
      linarith
    exact first_clip_arith (hb0 v) hyF (hco v hv).1 ((hbarv v hv).1 hle) he0
      (Real.exp_pos _).le hWs hCW0 hCW
  · linarith [hfull v hv hle]

/-- **(c) Strict improvement from the interfaces** (E6 + E10 + E7): on the R1 caps
`capsOf …`, every piece from a good point (`M_f = 2μ`, `Y₀ = (4/5) y`) with the threshold
`Thr ≤ |r|` paid improves to `capsImp …`, and the fast `H²` trace is back below `Y₀` after the
first unit.  E6: `scalar_peak_on_piece`, `scalar_dissipation_on_piece` with `λ = 1/4` and the
kinetic budget `I_a = Tp/8 + 5μ²` (`KineticInterface`); E10: `fast_H2_on_piece`; E7: the slow
caps. -/
private theorem strict_improvement_of_interfaces {σ Cs CH K₁ K₂ m₀ Tp μ φ cy Cb CSl KP KY KJ Cs1
    Thr : ℝ} {e : SlowExp} {L : Fin 5 → ℝ} {q₀ q₁ q₂ qS : ℝ → ℝ → Caps → ℝ} {Nbar piTol : ℝ → ℝ → ℝ}
    {N : ℝ → ℝ} (hσ : 0 < σ ∧ σ < 1) (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4) (hμ : 1 ≤ μ)
    (hK : KineticInterface μ φ (q₀ μ φ))
    (hE1 : H1EnergyInterface σ Cs μ φ Tp (Nbar μ φ) (piTol μ φ) K₁ (q₁ μ φ) N)
    (hE2 : H2EnergyInterface σ CH μ φ Tp K₂ m₀ (q₂ μ φ) N)
    (hSl : ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞) (caps : Caps) (s t : ℝ),
      ActualSol μ φ r g y Ty → PieceHyp Tp (qS μ φ) r g y Ty caps s t →
      SlowLevel L μ e r g y s →
      (∀ u ∈ Icc s t, SlowLevel (fun _ ↦ CSl) μ e r g y u ∧ slowWiener r g y u ≤ CSl * μ ^ e.eW) ∧
      (∫ u in s..t, slowNorm 2 r g y u ^ 2) ≤ CSl * μ ^ e.eJ ∧
      ∀ u ∈ Icc (s + 1) t, SlowLevel L μ e r g y u)
    (hCSl : CSl ≤ Cs1) (hcy0 : 0 ≤ cy) (hcy : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Cs * a ^ (3 - σ) * b ^ σ ≤ 1 / 4 * b ^ 2 + cy * a ^ (4 - 2 / betaOf σ))
    (hCb : 0 ≤ Cb) (hbar : BarrierProp m₀ Cb) (hKP : 0 < KP) (hKY : 0 ≤ KY)
    (hpeak : peakSq σ cy (1 / 4) (2 * μ) (KP * μ ^ betaOf σ) (Tp / 8 + 5 * μ ^ 2) (Nbar μ φ)
      (piTol μ φ) ≤ (KP * μ ^ betaOf σ / 2) ^ 2)
    (hdis : dissipSq σ cy (1 / 4) (2 * μ) (KP * μ ^ betaOf σ) (Tp / 8 + 5 * μ ^ 2) (Nbar μ φ)
      (piTol μ φ) ≤ KJ * μ ^ (2 * betaOf σ) / 2)
    (hB : 1 ≤ resCoeff σ CH μ φ (capsOf σ KP KY KJ Cs1 μ e))
    (hCW : Cb * WStar 1 (KP * μ ^ betaOf σ) (resCoeff σ CH μ φ (capsOf σ KP KY KJ Cs1 μ e)) ≤
      (KY * μ ^ vOf σ) ^ 2 / 100)
    (hthr : ∀ q : ℝ, Thr ≤ q →
      q₀ μ φ (capsOf σ KP KY KJ Cs1 μ e) ≤ q ∧ q₁ μ φ (capsOf σ KP KY KJ Cs1 μ e) ≤ q ∧
      q₂ μ φ (capsOf σ KP KY KJ Cs1 μ e) ≤ q ∧ qS μ φ (capsOf σ KP KY KJ Cs1 μ e) ≤ q ∧
      K₁ * Real.sqrt (capsOf σ KP KY KJ Cs1 μ e).PF *
        (capsOf σ KP KY KJ Cs1 μ e).yF ^ (3 / 2 : ℝ) * N q ≤ 1 ∧
      K₂ * Real.sqrt (capsOf σ KP KY KJ Cs1 μ e).PF *
        (capsOf σ KP KY KJ Cs1 μ e).yF ^ (3 / 2 : ℝ) * N q ≤ 1) :
    StrictImprovement (2 * μ) Tp μ φ (fun _ ↦ Thr) (capsOf σ KP KY KJ Cs1 μ e)
      (capsImp σ KP KY KJ Cs1 μ e) (capsStart σ KP KY KJ Cs1 μ e L) := by
  intro r g y Ty hsol s t hgood hpiece
  set caps := capsOf σ KP KY KJ Cs1 μ e with hcaps
  have hμ0 : 0 < μ := by linarith
  have hs := hpiece.hs
  have hst := hpiece.hst
  have ht := hpiece.ht
  have hon := hpiece.onPrefix
  obtain ⟨h0, h1, h2, h3, hl1, hl2⟩ := hthr |r| hpiece.thr
  have mk : ∀ {q : Caps → ℝ}, q caps ≤ |r| → PieceHyp Tp q r g y Ty caps s t :=
    fun h ↦ ⟨⟨hs, hst, ht, h, hon⟩, hpiece.len⟩
  obtain ⟨c1, c2, -, -, -⟩ := norms_continuous hsol (b := t) (hs.trans hst) ht
  have hsub : Icc s t ⊆ Icc 0 t := Icc_subset_Icc hs le_rfl
  -- kinetic budget
  obtain ⟨W0, hW0⟩ := hK r g y Ty hsol
  obtain ⟨k1, -, k3, -⟩ := hW0 caps s t ⟨hs, hst, ht, h0, hon⟩
  have hsT : ENNReal.ofReal s < Ty := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) ht
  have ha0 : fastNorm 0 r g y s ≤ fastNorm 1 r g y s :=
    hnorm_mono (by norm_num) (((actual_mz hsol hs hsT).inH.mono (by norm_num)).PiF)
  have hWs : W0 s ≤ 5 * μ ^ 2 := by
    have h := (k1 s ⟨le_rfl, hst⟩).2
    have h' : fastNorm 0 r g y s ^ 2 ≤ (2 * μ) ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg _ _) (ha0.trans hgood.fastH1) 2
    nlinarith
  have hWt : 0 ≤ W0 t := le_trans (by positivity) (k1 t ⟨hst, le_rfl⟩).1
  have hkin : (∫ u in s..t, fastNorm 1 r g y u ^ 2) ≤ Tp / 8 + 5 * μ ^ 2 := by
    have := hpiece.len
    linarith
  have hpk := scalar_peak_on_piece hσ hE1 hsol (mk h1) hl1 ⟨by norm_num, by norm_num⟩ hcy0 hcy
    hkin hgood.fastH1 (c1.mono hsub) (c2.mono hsub)
  have hds := scalar_dissipation_on_piece hσ hE1 hsol (mk h1) hl1 ⟨by norm_num, by norm_num⟩
    hcy0 hcy hkin hgood.fastH1 (c1.mono hsub) (c2.mono hsub)
  obtain ⟨-, -, a3, a4, -, a6, a7, a8⟩ := hgood.start
  obtain ⟨hsl, hslJ, hslP⟩ := hSl r g y Ty caps s t hsol (mk h3) ⟨a6, a7, a8, a3, a4⟩
  have hPF : 0 < caps.PF := mul_pos hKP (Real.rpow_pos_of_pos hμ0 _)
  have hyF : 0 ≤ caps.yF := mul_nonneg hKY (Real.rpow_nonneg hμ0.le _)
  obtain ⟨hb1, hb2⟩ := fast_H2_on_piece hE2 hm₀ hCb hbar hsol (mk h2) hl2 hPF hB hyF hCW
    hgood.start.2.1
  have hC : ∀ x : ℝ, CSl * μ ^ x ≤ Cs1 * μ ^ x := fun x ↦
    mul_le_mul_of_nonneg_right hCSl (Real.rpow_nonneg hμ0.le _)
  have hC1 : CSl * μ ≤ Cs1 * μ := mul_le_mul_of_nonneg_right hCSl hμ0.le
  have hC2 : CSl * μ ^ 2 ≤ Cs1 * μ ^ 2 := mul_le_mul_of_nonneg_right hCSl (sq_nonneg _)
  have haF : ∀ u ∈ Icc s t, fastNorm 1 r g y u ≤ KP * μ ^ betaOf σ / 2 := fun u hu ↦ by
    have h := (hpk u hu).trans hpeak
    exact (pow_le_pow_iff_left₀ (hnorm_nonneg _ _) (by positivity) (by norm_num)).1 h
  refine ⟨⟨fun u hu ↦ ⟨haF u hu, hb1 u hu, (hsl u hu).1.2.2.2.1.trans (hC _),
    (hsl u hu).1.2.2.2.2.trans (hC _), (hsl u hu).2.trans (hC _)⟩, hds.trans hdis,
    hslJ.trans (hC _), fun u hu ↦ ⟨(hsl u hu).1.1.trans hC1, (hsl u hu).1.2.1.trans hC1,
    (hsl u hu).1.2.2.1.trans hC2⟩⟩, fun v hv ↦ ?_⟩
  have hv' : v ∈ Icc s t := ⟨by linarith [hv.1], hv.2⟩
  obtain ⟨p0, p1, p2, p3, p4⟩ := hslP v hv
  exact ⟨haF v hv', hb2 v hv, p3, p4, (hsl v hv').2.trans (hC _), p0, p1, p2⟩

/-- `C_b W_* ≤ y²/100` once `A B ≤ X μ^v` and `K_Y = 20 (C_b + 1)(X + 1)`. -/
private lemma cw_bound {Cb X KY A B v : ℝ} (hCb0 : 0 ≤ Cb) (hX0 : 0 ≤ X)
    (hKY : KY = 20 * (Cb + 1) * (X + 1)) (hAB0 : 0 ≤ A * B) (hAB : A * B ≤ X * v) :
    Cb * WStar 1 A B ≤ (KY * v) ^ 2 / 100 := by
  have hW := WStar_le A B
  have hAB2 := pow_le_pow_left₀ hAB0 hAB 2
  have ha : Cb ≤ (Cb + 1) ^ 2 := by nlinarith
  have hb : X ^ 2 ≤ (X + 1) ^ 2 := by nlinarith
  have hab : Cb * X ^ 2 ≤ (Cb + 1) ^ 2 * (X + 1) ^ 2 :=
    mul_le_mul ha hb (sq_nonneg _) (sq_nonneg _)
  have hKYX : 300 * (Cb * X ^ 2) ≤ KY ^ 2 := by
    have e : KY ^ 2 = 400 * ((Cb + 1) ^ 2 * (X + 1) ^ 2) := by rw [hKY]; ring
    rw [e]
    nlinarith [mul_nonneg hCb0 (sq_nonneg X)]
  calc Cb * WStar 1 A B ≤ Cb * (3 * (A * B) ^ 2) := mul_le_mul_of_nonneg_left hW hCb0
    _ ≤ Cb * (3 * (X * v) ^ 2) := by gcongr
    _ = 3 * (Cb * X ^ 2) * v ^ 2 := by ring
    _ ≤ KY ^ 2 / 100 * v ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = (KY * v) ^ 2 / 100 := by ring

/-- The dissipation budget arithmetic: `D ≤ 4 N̄² + 8 P`, `P ≤ (K_P M/2)²`, `N̄² ≤ C_N² m`,
`m ≤ M²` give `D ≤ K_J M²/2` with `K_J = 2(4 C_N² + 2 K_P²) + 2`. -/
lemma dis_bound {D P N2 CN KP m M : ℝ} (hd : D ≤ 4 * N2 + 8 * P)
    (hP : P ≤ (KP * M / 2) ^ 2) (hN2 : N2 ≤ CN ^ 2 * m) (hm : m ≤ M ^ 2) :
    D ≤ (2 * (4 * CN ^ 2 + 2 * KP ^ 2) + 2) * M ^ 2 / 2 := by
  have h3 : CN ^ 2 * m ≤ CN ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hm (sq_nonneg _)
  have e1 : (KP * M / 2) ^ 2 = KP ^ 2 * M ^ 2 / 4 := by ring
  rw [e1] at hP
  nlinarith [sq_nonneg M, sq_nonneg KP]

/-- `‖Π_H f‖_s ≤ ‖f‖_s`. -/
private lemma hnorm_PiH_le_self {s : ℝ} {f : Field} (hf : InH s f) :
    hnorm s (PiH f) ≤ hnorm s f := by
  have h := hnorm_sq_split_slow hf
  have h1 : hnorm s (PiH f) ≤ hnorm s (PiS f) :=
    (pow_le_pow_iff_left₀ (hnorm_nonneg _ _) (hnorm_nonneg _ _) (by norm_num : (2 : ℕ) ≠ 0)).1
      (by nlinarith [sq_nonneg (hnorm s (PiV f))])
  exact h1.trans (hnorm_PiS_le hf)

/-- Norms of the actual field at time `0` (`ψ(0) = 0`, `x(0) = v₀`). -/
lemma norms_at_zero {r μ : ℝ} {g v₀ : Field} {y : ℝ → Field} (hy0 : y 0 = v₀)
    (hv : Adm 2 v₀) (hvμ : hnorm 2 v₀ ≤ μ) :
    fastNorm 1 r g y 0 ≤ μ ∧ fastNorm 2 r g y 0 ≤ μ ∧ slowNorm 1 r g y 0 ≤ μ ∧
      slowNorm 2 r g y 0 ≤ μ ∧ slowWiener r g y 0 ≤ c4 * μ ∧ slowNorm 0 r g y 0 ≤ μ ∧
      horizNorm 1 r g y 0 ≤ μ ∧ horizNorm 2 r g y 0 ≤ μ := by
  have ha : actual r g y 0 = v₀ := by simp [actual, hy0, psi_zero]
  have h12 : hnorm 1 v₀ ≤ μ := (hnorm_mono (by norm_num) hv.inH).trans hvμ
  have h02 : hnorm 0 v₀ ≤ μ := (hnorm_mono (by norm_num) hv.inH).trans hvμ
  have hv1 : InH 1 v₀ := hv.inH.mono (by norm_num)
  have hv0 : InH 0 v₀ := hv.inH.mono (by norm_num)
  simp only [fastNorm, slowNorm, slowWiener, horizNorm, ha]
  refine ⟨(hnorm_PiF_le hv1).trans h12, (hnorm_PiF_le hv.inH).trans hvμ,
    (hnorm_PiS_le hv1).trans h12, (hnorm_PiS_le hv.inH).trans hvμ, ?_,
    (hnorm_PiS_le hv0).trans h02, (hnorm_PiH_le_self hv1).trans h12,
    (hnorm_PiH_le_self hv.inH).trans hvμ⟩
  exact (wiener_le ⟨hv.inH.PiS, by simp [PiS, hv.mean]⟩).trans
    (mul_le_mul_of_nonneg_left ((hnorm_PiS_le hv.inH).trans hvμ) c4_pos.le)

/-- **(d) Global from strict improvement**: on the maximal solution of `exists_maximal`, the
good points (`GoodPoint` and kinetic level `W₀ ≤ 2μ²`) propagate by `piece_step`, so
`pieces_induction` gives a global solution with `‖y‖₂ ≤ y + B_S + 4φ`. -/
private theorem global_of_strict {μ φ Tp Thr : ℝ} {q₀ : Caps → ℝ} {caps ci c0 : Caps}
    (hμ : 1 ≤ μ) (hTp : 2 ≤ Tp) (hlt : ci.Below caps)
    (himp : StrictImprovement (2 * μ) Tp μ φ (fun _ ↦ Thr) caps ci c0)
    (hK : KineticInterface μ φ q₀) {r : ℝ} {g v₀ : Field} (hg : Adm 2 g) (hgφ : hnorm 2 g ≤ φ)
    (hv : Adm 2 v₀) (hvμ : hnorm 2 v₀ ≤ μ) (hthr : Thr ≤ |r|) (hthr₀ : q₀ caps ≤ |r|)
    (hbase : ∀ y : ℝ → Field, y 0 = v₀ → GoodPoint (2 * μ) c0 ci r g y 0) :
    ∃ y : ℝ → Field, IsHeatSol (filtN r 0) (filtG r 0 g) ⊤ y ∧ y 0 = v₀ ∧
      ∀ t, 0 ≤ t → hnorm 2 (y t) ≤ caps.yF + caps.BS + 4 * φ := by
  obtain ⟨Ty, y, hTy0, hy, hy0, hbl⟩ :=
    exists_maximal (majorized_filtN r 0) (goodForce_filtG r 0 hg) hv
  have hsol : ActualSol μ φ r g y Ty := ⟨hg, hgφ, hTy0, hy, hy0 ▸ hvμ⟩
  obtain ⟨W0, hW0⟩ := hK r g y Ty hsol
  have hW0' : KinFun μ q₀ r g y Ty W0 := hW0
  have hb := hbase y hy0
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := hlt
  have hJ : 0 ≤ caps.JF ∧ 0 ≤ caps.JS := ⟨p8.trans p6.le, p9.trans p7.le⟩
  have hpc : PointCaps caps r g y 0 := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hb.pointCaps
    exact ⟨a1.trans p1.le, a2.trans p2.le, a3.trans p3.le, a4.trans p4.le, a5.trans p5.le,
      a6.trans p10.le, a7.trans p11.le, a8.trans p12.le⟩
  have hlt : ci.Below caps := ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩
  have hW00 : W0 0 ≤ 2 * μ ^ 2 := by
    have h := (hW0' caps 0 0 ⟨le_rfl, le_rfl, by simpa using hTy0, hthr₀,
      onPrefix_point hpc hJ.1 hJ.2⟩).2.1 rfl
    nlinarith
  have hstep : ∀ τ : ℝ, 0 ≤ τ → ENNReal.ofReal τ < Ty →
      (GoodPoint (2 * μ) c0 ci r g y τ ∧ W0 τ ≤ 2 * μ ^ 2) →
      ∃ τ' : ℝ, τ + 1 ≤ τ' ∧ ENNReal.ofReal τ' < Ty ∧
        (GoodPoint (2 * μ) c0 ci r g y τ' ∧ W0 τ' ≤ 2 * μ ^ 2) ∧
        ∀ u ∈ Icc τ τ', hnorm 2 (y u) ≤ caps.yF + caps.BS + 4 * φ := by
    rintro τ hτ0 hτT ⟨hgood, hWτ⟩
    obtain ⟨s', h1, -, h3, h4, h5, h6⟩ := piece_step hlt hTp himp hsol hbl hthr hthr₀ hW0'
      (by linarith) (by nlinarith) (by nlinarith) hgood hWτ hτT
    refine ⟨s', by linarith, h3, ⟨h4, h5⟩, fun u hu ↦ ?_⟩
    have hu0 : 0 ≤ u := hτ0.trans hu.1
    have huT : ENNReal.ofReal u < Ty := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) h3
    have hc := h6.1 u hu
    have := hnorm_y_le hsol hu0 huT
    linarith [hc.2.1, hc.2.2.2.1]
  obtain ⟨hTop, hB⟩ := pieces_induction le_rfl hstep hTy0 ⟨hb, hW00⟩
  subst hTop
  exact ⟨y, hy, hy0, hB⟩

/-- **The large-data regime `μ ≥ μ₀` (R1 + R3 bootstrap).**  Under the hypotheses of
`fixed_force_normalized`, for `C (1 + μ)^{d+ε} ≤ |r|`, `μ ≥ μ₀ = max 1 (1/C_H)`, the maximal
filtered solution is global with a uniform `H²` bound `S μ`: the caps `capsOf` (a), the
thresholds (`thresholds_paid`, b), the strict improvement (c) and `global_of_strict` (d). -/
private theorem large_regime {σ d Cs CH K₁ K₂ m₀ Tp : ℝ} {e : SlowExp}
    {q₀ q₁ q₂ qS : ℝ → ℝ → Caps → ℝ} {Nbar piTol : ℝ → ℝ → ℝ} {N : ℝ → ℝ}
    (hσ : 0 < σ ∧ σ < 1) (hd : dOf σ ≤ d) (hTp : 2 ≤ Tp) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4) (hCs : 0 ≤ Cs) (hCH : 0 < CH)
    (he : 1 ≤ e.eA ∧ 1 ≤ e.eB ∧ 1 ≤ e.eW)
    (hK : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ → KineticInterface μ φ (q₀ μ φ))
    (hE1 : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H1EnergyInterface σ Cs μ φ Tp (Nbar μ φ) (piTol μ φ) K₁ (q₁ μ φ) N)
    (hE2 : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ → H2EnergyInterface σ CH μ φ Tp K₂ m₀ (q₂ μ φ) N)
    (hS : SlowCapsInterface Tp e qS) (hN : NativeProfile N)
    (hq₀ : DegreeBelow σ d e q₀) (hq₁ : DegreeBelow σ d e q₁)
    (hq₂ : DegreeBelow σ d e q₂) (hqS : DegreeBelow σ d e qS)
    (hNbar : AtMostLinear Nbar) (hpi : AtMostLinear piTol)
    (hNbar0 : ∀ μ φ : ℝ, 0 ≤ Nbar μ φ) (hpi0 : ∀ μ φ : ℝ, 0 ≤ piTol μ φ) :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ μ₀ C : ℝ, ∃ S : ℝ → ℝ, 1 ≤ μ₀ ∧ 0 ≤ C ∧
      ∀ (μ r : ℝ) (g v₀ : Field), μ₀ ≤ μ → Adm 2 g → hnorm 2 g ≤ φ → Adm 2 v₀ →
        hnorm 2 v₀ ≤ μ → C * (1 + μ) ^ (d + ε) ≤ |r| →
        ∃ y : ℝ → Field, IsHeatSol (filtN r 0) (filtG r 0 g) ⊤ y ∧ y 0 = v₀ ∧
          ∀ t, 0 ≤ t → hnorm 2 (y t) ≤ S μ := by
  intro φ ε hφ hε
  have hσ' : 0 ≤ σ ∧ σ < 1 := ⟨hσ.1.le, hσ.2⟩
  have hβ := two_le_betaOf hσ'.1 hσ'.2
  obtain ⟨CN, hCN⟩ := hNbar φ hφ
  obtain ⟨Cp, hCp⟩ := hpi φ hφ
  obtain ⟨L, CSl, hL, hCSl⟩ := hS φ hφ
  obtain ⟨cy, hcy0, hcy⟩ := young_cubic hσ hCs (lam := 1 / 4) (by norm_num)
  obtain ⟨Cb, hCb0, hbar⟩ := barrier_cap hm₀.1 (by linarith [hm₀.2])
  have hbar' : BarrierProp m₀ Cb := hbar
  set CN' := max CN 0 with hCN'
  set Cp' := max Cp 0 with hCp'
  set Z : ℝ := 48 * (4 + CN' ^ 2 + Cp' ^ 2) + 48 * cy * (Tp + 5) + 1 with hZ
  have hcyT : 0 ≤ cy * (Tp + 5) := mul_nonneg hcy0 (by linarith)
  have hZ49 : 49 ≤ Z := by
    have e3 : 48 * cy * (Tp + 5) = 48 * (cy * (Tp + 5)) := by ring
    rw [hZ, e3]
    linarith only [sq_nonneg CN', sq_nonneg Cp', hcyT]
  have hZ1 : 1 ≤ Z := by linarith
  set KP : ℝ := Z ^ (betaOf σ / 2) with hKPdef
  have hKPZ : Z ≤ KP := by
    calc Z = Z ^ (1 : ℝ) := (Real.rpow_one Z).symm
      _ ≤ Z ^ (betaOf σ / 2) := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hKP1 : 1 ≤ KP := hZ1.trans hKPZ
  set KJ : ℝ := 2 * (4 * CN' ^ 2 + 2 * KP ^ 2) + 2 with hKJ
  have hKJ1 : 1 ≤ KJ := by
    rw [hKJ]
    linarith only [sq_nonneg CN', sq_nonneg KP]
  set X : ℝ := CH * (6 + 4 * φ) * KP ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  set KY : ℝ := 20 * (Cb + 1) * (X + 1) with hKY
  have hKY20 : 20 ≤ KY := by
    have h : 1 ≤ (Cb + 1) * (X + 1) := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    rw [hKY]
    linarith only [h]
  set Cs1 : ℝ := max (max CSl c4) 1 with hCs1
  have hCs11 : 1 ≤ Cs1 := le_max_right _ _
  set K : ℝ := max (max KP KY) (max KJ (2 * Cs1)) with hKdef
  have hK1 : 1 ≤ K := hKP1.trans ((le_max_left _ _).trans (le_max_left _ _))
  obtain ⟨δ₀, hδ₀, hT⟩ :=
    thresholds_paid hσ' hd hK₁ hK₂ hN.nearProfiles_zero hq₀ hq₁ hq₂ hqS hφ hε hK1
  obtain ⟨Cthr, hCthr0, hTC⟩ := hT δ₀ hδ₀ le_rfl
  refine ⟨max 1 (1 / CH), Cthr, fun μ ↦ KY * μ ^ vOf σ + 2 * Cs1 * μ ^ e.eB + 4 * φ,
    le_max_left _ _, hCthr0, ?_⟩
  intro μ r g v₀ hμ hg hgφ hv hvμ hr
  have hμ1 : 1 ≤ μ := (le_max_left _ _).trans hμ
  have hμ0 : 0 < μ := by linarith
  have hCHμ : 1 ≤ CH * μ := by
    have h := (le_max_right _ _).trans hμ
    rw [div_le_iff₀ hCH] at h
    linarith
  obtain ⟨hf1, hf2, hf3, -, hμp⟩ := rpow_facts hσ hμ1
  set p := μ ^ (betaOf σ - 1) with hp
  have hp1 : 1 ≤ p := hμ1.trans hμp
  have hscaled : CapsScaled σ δ₀ K μ e (capsOf σ KP KY KJ Cs1 μ e) :=
    capsOf_scaled hδ₀.le hμ1 hKP1 (by linarith) hKJ1 (by linarith)
      ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
      ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
  have hthr := fun q (hq : Cthr * (1 + μ) ^ (d + ε) ≤ q) ↦ hTC μ hμ1 _ hscaled q hq
  obtain ⟨hBlo, hBhi⟩ := resCoeff_bounds (c := capsOf σ KP KY KJ Cs1 μ e) hσ hCH.le hμ1 hφ
    hKP1 rfl
  set B := resCoeff σ CH μ φ (capsOf σ KP KY KJ Cs1 μ e) with hBdef
  have hB : 1 ≤ B := hCHμ.trans hBlo
  have hCW : Cb * WStar 1 (KP * μ ^ betaOf σ) B ≤ (KY * μ ^ vOf σ) ^ 2 / 100 := by
    refine cw_bound hCb0 hX0 hKY
      (mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hμ0.le _)) (by linarith)) ?_
    rw [hf1, hf2]
    calc KP * (μ * p) * B ≤ KP * (μ * p) * (CH * (6 + 4 * φ) * KP * p) :=
          mul_le_mul_of_nonneg_left hBhi (by positivity)
      _ = X * (μ * p ^ 2) := by rw [hX]; ring
  have hNb : Nbar μ φ ≤ CN' * μ :=
    (hCN μ hμ1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hμ0.le)
  have hpt : piTol μ φ ≤ Cp' * μ :=
    (hCp μ hμ1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hμ0.le)
  have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ1
  have hIa : Tp / 8 + 5 * μ ^ 2 ≤ (Tp + 5) * μ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hμ2 (by linarith : (0 : ℝ) ≤ Tp)
    linarith only [this, hTp]
  have hpeak := peak_le (σ := σ) (CN := CN') (Cp := Cp') (Z := Z) hσ hμ1 hcy0 (by linarith)
    le_rfl (hNbar0 μ φ) hNb (hpi0 μ φ) hpt (by positivity) hIa
  have hμβ : μ ≤ μ ^ betaOf σ := by rw [hf1]; exact le_mul_of_one_le_right hμ0.le hp1
  have hdis : dissipSq σ cy (1 / 4) (2 * μ) (KP * μ ^ betaOf σ) (Tp / 8 + 5 * μ ^ 2) (Nbar μ φ)
      (piTol μ φ) ≤ KJ * μ ^ (2 * betaOf σ) / 2 := by
    have hd := dissip_le (σ := σ) (Mf := 2 * μ) (PF := KP * μ ^ betaOf σ) (Nb := Nbar μ φ)
      (pt := piTol μ φ) (Ia := Tp / 8 + 5 * μ ^ 2) hcy0 (by positivity)
    have hN2 : Nbar μ φ ^ 2 ≤ CN' ^ 2 * μ ^ 2 := by
      have := pow_le_pow_left₀ (hNbar0 μ φ) hNb 2
      rwa [mul_pow] at this
    have hμ2' : μ ^ 2 ≤ (μ ^ betaOf σ) ^ 2 := pow_le_pow_left₀ hμ0.le hμβ 2
    have e0 : μ ^ (2 * betaOf σ) = (μ ^ betaOf σ) ^ 2 := by rw [hf3, hf1]
    rw [e0, hKJ]
    exact dis_bound hd hpeak hN2 hμ2'
  have hCSl1 : CSl ≤ Cs1 := (le_max_left _ _).trans (le_max_left _ _)
  have himp := strict_improvement_of_interfaces (Thr := Cthr * (1 + μ) ^ (d + ε)) hσ hm₀ hμ1
    (hK μ φ hμ0.le hφ) (hE1 μ φ hμ0.le hφ) (hE2 μ φ hμ0.le hφ) (hCSl μ hμ1) hCSl1 hcy0 hcy hCb0
    hbar' (by linarith) (by linarith) hpeak hdis hB hCW hthr
  have hlt := capsImp_below (σ := σ) (e := e) (Cs1 := Cs1) (by linarith : 0 < KP)
    (by linarith : 0 < KY) (by linarith : 0 < KJ) (by linarith) hμ0
  have hpow1 : ∀ x : ℝ, 1 ≤ x → μ ≤ μ ^ x := fun x hx ↦ by
    calc μ = μ ^ (1 : ℝ) := (Real.rpow_one μ).symm
      _ ≤ μ ^ x := Real.rpow_le_rpow_of_exponent_le hμ1 hx
  have hμv : μ ≤ μ ^ vOf σ := hpow1 _ (by linarith [three_le_vOf hσ'.1 hσ'.2])
  have hCmono : ∀ x : ℝ, 1 ≤ x → μ ≤ Cs1 * μ ^ x := fun x hx ↦
    (hpow1 x hx).trans (le_mul_of_one_le_left (Real.rpow_nonneg hμ0.le _) hCs11)
  have hc4 : c4 ≤ Cs1 := (le_max_right _ _).trans (le_max_left _ _)
  have hμ2 : μ ≤ μ ^ 2 := le_self_pow₀ hμ1 (by norm_num)
  have hLμ : ∀ i, μ ≤ L i * μ := fun i ↦ le_mul_of_one_le_left hμ0.le (hL i)
  have hLx : ∀ i (x : ℝ), 1 ≤ x → μ ≤ L i * μ ^ x := fun i x hx ↦
    (hpow1 x hx).trans (le_mul_of_one_le_left (Real.rpow_nonneg hμ0.le _) (hL i))
  have hbase : ∀ y : ℝ → Field, y 0 = v₀ →
      GoodPoint (2 * μ) (capsStart σ KP KY KJ Cs1 μ e L) (capsImp σ KP KY KJ Cs1 μ e) r g y 0 := by
    intro y hy0
    obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := norms_at_zero (r := r) (g := g) hy0 hv hvμ
    have h20 : 20 * μ ≤ KY * μ ^ vOf σ := mul_le_mul hKY20 hμv hμ0.le (by linarith)
    have h2P : 2 * μ ≤ KP * μ ^ betaOf σ := mul_le_mul (by linarith) hμβ hμ0.le (by linarith)
    have hW : c4 * μ ≤ Cs1 * μ ^ e.eW :=
      calc c4 * μ ≤ Cs1 * μ := mul_le_mul_of_nonneg_right hc4 hμ0.le
        _ ≤ Cs1 * μ ^ e.eW := mul_le_mul_of_nonneg_left (hpow1 _ he.2.2) (by linarith)
    have hC1 : μ ≤ Cs1 * μ := le_mul_of_one_le_left hμ0.le hCs11
    have hC2 : μ ≤ Cs1 * μ ^ 2 := hμ2.trans (le_mul_of_one_le_left (sq_nonneg _) hCs11)
    have hL2 : μ ≤ L 2 * μ ^ 2 := hμ2.trans (le_mul_of_one_le_left (sq_nonneg _) (hL 2))
    refine ⟨le_rfl, by linarith, ?_, ?_⟩
    · simp only [PointCaps, capsStart]
      exact ⟨z1.trans (by linarith only [h2P]), z2.trans (by linarith only [h20, hμ0]),
        z3.trans (hLx 3 _ he.1), z4.trans (hLx 4 _ he.2.1), z5.trans hW, z6.trans (hLμ 0),
        z7.trans (hLμ 1), z8.trans hL2⟩
    · simp only [PointCaps, capsImp]
      exact ⟨z1.trans (by linarith only [h2P]), z2.trans (by linarith only [h20, hμ0]),
        z3.trans (hCmono _ he.1), z4.trans (hCmono _ he.2.1), z5.trans hW, z6.trans hC1,
        z7.trans hC1, z8.trans hC2⟩
  exact global_of_strict hμ1 hTp hlt himp (hK μ φ hμ0.le hφ) hg hgφ hv hvμ hr (hthr |r| hr).1
    hbase

/-- **The normalized fixed-force assembly (R1 + R3)** (locked; amended hypotheses): for each
`φ ≥ 0`, `ε > 0` there are `C ≥ 0` and `Bd : ℝ → ℝ` such that every normalized datum/force pair
in the balls `(μ, φ)` with `C (1 + μ)^{d+ε} ≤ |r|` has a global filtered solution with the
`normalized_main`-shaped `H¹, H², L²H³` bounds `Bd μ`.  Hypotheses: the interfaces at
`σ = θ ∈ (0, 1)`, piece length `Tp ≥ 2`, slow exponents `e` with `e.eA, e.eB, e.eW ≥ 1`, a
degree `d ≥ dOf σ` (D2) with the R1 bookkeeping `DegreeBelow σ d e` for the four thresholds,
nonnegative `O(μ)` tolerances `N̄, π`, nonnegative leading normalizations, `C_s ≥ 0`,
`C_H > 0` and a clip mass `m₀ ≤ 1/4`.  `ResH1`/`ResH2` are consumed inside the energy
interfaces and are kept only for the shape of the statement.  Proof: `large_regime` for
`μ ≥ μ₀`, `normalized_main μ₀ φ` for `μ ≤ μ₀`, `sliding_h3'` for `L²H³`. -/
theorem fixed_force_normalized {σ d Cs CH K₁ K₂ m₀ Tp : ℝ} {e : SlowExp}
    {q₀ q₁ q₂ qS : ℝ → ℝ → Caps → ℝ} {Nbar piTol : ℝ → ℝ → ℝ} {N : ℝ → ℝ}
    (hσ : 0 < σ ∧ σ < 1) (hd : dOf σ ≤ d) (hTp : 2 ≤ Tp) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4) (hCs : 0 ≤ Cs) (hCH : 0 < CH)
    (he : 1 ≤ e.eA ∧ 1 ≤ e.eB ∧ 1 ≤ e.eW) (_h1 : ResH1 σ Cs) (_h2 : ResH2 σ CH)
    (hK : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ → KineticInterface μ φ (q₀ μ φ))
    (hE1 : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H1EnergyInterface σ Cs μ φ Tp (Nbar μ φ) (piTol μ φ) K₁ (q₁ μ φ) N)
    (hE2 : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ → H2EnergyInterface σ CH μ φ Tp K₂ m₀ (q₂ μ φ) N)
    (hS : SlowCapsInterface Tp e qS) (hN : NativeProfile N)
    (hq₀ : DegreeBelow σ d e q₀) (hq₁ : DegreeBelow σ d e q₁)
    (hq₂ : DegreeBelow σ d e q₂) (hqS : DegreeBelow σ d e qS)
    (hNbar : AtMostLinear Nbar) (hpi : AtMostLinear piTol)
    (hNbar0 : ∀ μ φ : ℝ, 0 ≤ Nbar μ φ) (hpi0 : ∀ μ φ : ℝ, 0 ≤ piTol μ φ) :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ C : ℝ, ∃ Bd : ℝ → ℝ, 0 ≤ C ∧
      ∀ (μ r : ℝ) (g v₀ : Field), 0 ≤ μ → Adm 2 g → hnorm 2 g ≤ φ → Adm 2 v₀ →
        hnorm 2 v₀ ≤ μ → C * (1 + μ) ^ (d + ε) ≤ |r| →
        ∃ y : ℝ → Field, IsHeatSol (filtN r 0) (filtG r 0 g) ⊤ y ∧ y 0 = v₀ ∧
          (∀ t, 0 ≤ t → hnorm 1 (y t) ≤ Bd μ ∧ hnorm 2 (y t) ≤ Bd μ) ∧
          (∀ t, 0 ≤ t → ∫ s in t..(t + 1), hnorm 3 (y s) ^ 2 ≤ Bd μ) := by
  intro φ ε hφ hε
  obtain ⟨μ₀, CL, SL, hμ₀, hCL, HL⟩ := large_regime hσ hd hTp hK₁ hK₂ hm₀ hCs hCH he hK
    hE1 hE2 hS hN hq₀ hq₁ hq₂ hqS hNbar hpi hNbar0 hpi0 φ ε hφ hε
  obtain ⟨R₀, B₀, hR₀, -, H₀⟩ := normalized_main μ₀ φ (by linarith) hφ
  have hdε : 0 ≤ d + ε := by linarith [dOf_pos hσ.1.le hσ.2]
  refine ⟨max CL R₀, fun μ ↦ max B₀ (max (SL μ) (SL μ ^ 2 + 128 * c4 ^ 2 * SL μ ^ 4 +
    2 * φ ^ 2)), le_max_of_le_left hCL, ?_⟩
  intro μ r g v₀ hμ hg hgφ hv₀ hv₀μ hthr
  have hpow : 1 ≤ (1 + μ) ^ (d + ε) := Real.one_le_rpow (by linarith) hdε
  have hC0 : 0 ≤ max CL R₀ := le_max_of_le_left hCL
  rcases le_total μ μ₀ with hμ1 | hμ1
  · have hR : R₀ ≤ |r| := by
      calc R₀ ≤ max CL R₀ := le_max_right _ _
        _ ≤ max CL R₀ * (1 + μ) ^ (d + ε) := le_mul_of_one_le_right hC0 hpow
        _ ≤ |r| := hthr
    obtain ⟨y, hy, hy0, hB, hW⟩ := H₀ r g v₀ hg hgφ hv₀ (hv₀μ.trans hμ1) hR
    exact ⟨y, hy, hy0, fun t ht ↦ ⟨(hB t ht).1.trans (le_max_left _ _),
      (hB t ht).2.trans (le_max_left _ _)⟩, fun t ht ↦ (hW t ht).trans (le_max_left _ _)⟩
  · have hthr' : CL * (1 + μ) ^ (d + ε) ≤ |r| :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)).trans hthr
    obtain ⟨y, hy, hy0, hS2⟩ := HL μ r g v₀ hμ1 hg hgφ hv₀ hv₀μ hthr'
    have hG : GoodForce (filtG r 0 g) φ := goodForce_mono (goodForce_filtG r 0 hg)
      ((hnorm_mono (by norm_num) hg.inH).trans hgφ)
    refine ⟨y, hy, hy0, fun t ht ↦ ⟨?_, ?_⟩, fun t ht ↦ ?_⟩
    · exact ((hnorm_mono (by norm_num) (hy.adm t ht ENNReal.ofReal_lt_top).inH).trans
        (hS2 t ht)).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hS2 t ht).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (sliding_h3' (majorized_filtN r 0) hG hy hS2 ht).trans
        ((le_max_right _ _).trans (le_max_right _ _))

/-- **Assembly theorem (R1 + R3)** (spec §2.1 `fixed_force_of_interfaces`; amendments D1–D5):
the fixed-force statement of Theorem 1.2 with exponent `d + ε` for any `d ≥ dOf σ = 7β − 3`,
`β = (2 − σ)/(1 − σ)`, conditional on the analytic interfaces at a common `σ = θ ∈ (0,1)`.

Hypotheses: the arithmetic inputs `ResH1 σ Cs`, `ResH2 σ CH`; the energy interfaces
`KineticInterface` (E4), `H1EnergyInterface` (E5), `H2EnergyInterface` (E8) for every `(μ, φ)`
on pieces of length `≤ Tp`, `SlowCapsInterface Tp e` (E7, slow exponents `e`) and
the native near profile `NativeProfile N` (E9, D5: the only clause used; implied by both
`NearProfiles` and `NearProfilesEl`) with their abstract constants (`K₁, K₂ ≥ 0` the role-15/31
normalizations, `m₀ ≤ 1/4` the clip multiplier mass, `C_s ≥ 0`, `C_H > 0`, `N` the native near
moment); `e.eA, e.eB, e.eW ≥ 1`; the R1 degree bookkeeping `DegreeBelow σ d e` of every
non-leading threshold (Table quant-fixed, spec §3.2) and the nonnegative `O(μ)` growth of `N̄`,
`π` (E6).  The compact range `μ ≤ μ₀` is covered by `normalized_main` (R0) inside
`fixed_force_normalized`.

Conclusion: in the shape of `quantitative_fixed_force` — for each `φ ≥ 0`, `ε > 0` there are `C`
and `Bd` such that on the force ball `F/ν² ≤ φ`, `C (1 + M/ν)^{d+ε} ≤ |α|/ν` implies
`GlobalConclusion'` with bound `Bd (M/ν) (F/ν²)`.  Proved from `fixed_force_normalized` by the
scaling of `global_regularity` and `exists_physical_of_normalized`. -/
theorem fixed_force_of_interfaces {σ d Cs CH K₁ K₂ m₀ Tp : ℝ} {e : SlowExp}
    {q₀ q₁ q₂ qS : ℝ → ℝ → Caps → ℝ} {Nbar piTol : ℝ → ℝ → ℝ} {N : ℝ → ℝ}
    (hσ : 0 < σ ∧ σ < 1) (hd : dOf σ ≤ d) (hTp : 2 ≤ Tp) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4) (hCs : 0 ≤ Cs) (hCH : 0 < CH)
    (he : 1 ≤ e.eA ∧ 1 ≤ e.eB ∧ 1 ≤ e.eW) (h1 : ResH1 σ Cs) (h2 : ResH2 σ CH)
    (hK : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ → KineticInterface μ φ (q₀ μ φ))
    (hE1 : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H1EnergyInterface σ Cs μ φ Tp (Nbar μ φ) (piTol μ φ) K₁ (q₁ μ φ) N)
    (hE2 : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ → H2EnergyInterface σ CH μ φ Tp K₂ m₀ (q₂ μ φ) N)
    (hS : SlowCapsInterface Tp e qS) (hN : NativeProfile N)
    (hq₀ : DegreeBelow σ d e q₀) (hq₁ : DegreeBelow σ d e q₁)
    (hq₂ : DegreeBelow σ d e q₂) (hqS : DegreeBelow σ d e qS)
    (hNbar : AtMostLinear Nbar) (hpi : AtMostLinear piTol)
    (hNbar0 : ∀ μ φ : ℝ, 0 ≤ Nbar μ φ) (hpi0 : ∀ μ φ : ℝ, 0 ≤ piTol μ φ) :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ C : ℝ, ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F → F / ν ^ 2 ≤ φ →
        C * (1 + M / ν) ^ (d + ε) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  intro φ ε hφ hε
  obtain ⟨C, Bd, -, H⟩ := fixed_force_normalized hσ hd hTp hK₁ hK₂ hm₀ hCs hCH he h1 h2 hK hE1
    hE2 hS hN hq₀ hq₁ hq₂ hqS hNbar hpi hNbar0 hpi0 φ ε hφ hε
  refine ⟨C, fun μ _ => Bd μ, fun ν M F α u₀ f hν hM _hF hu₀ hf hu₀M hfF hFφ hthr => ?_⟩
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
  have hthr' : C * (1 + M / ν) ^ (d + ε) ≤ |α / ν| := by
    rwa [abs_div, abs_of_pos hν]
  obtain ⟨y, hy, h0, hB, hW⟩ :=
    H (M / ν) (α / ν) _ _ (div_nonneg hM hν.le) hg (hgn.trans hFφ) hv hvn hthr'
  exact exists_physical_of_normalized hν hg hy h0 hB hW

/-- **Corollary**: `fixed_force_of_interfaces` at `σ = θ = 281/1000` and `d = 9876/719 = dOf σ`
(`dOf_281`; `resonant_H1_of_counts`, `resonant_H2_of_counts` supply `ResH1`, `ResH2`).  Its conclusion is literally that of
`quantitative_fixed_force` (`OddViscousNS/Quant.lean`): exponent `9876/719 + ε`. -/
theorem quantitative_fixed_force_of_interfaces {Cs CH K₁ K₂ m₀ Tp : ℝ} {e : SlowExp}
    {q₀ q₁ q₂ qS : ℝ → ℝ → Caps → ℝ} {Nbar piTol : ℝ → ℝ → ℝ} {N : ℝ → ℝ}
    (hTp : 2 ≤ Tp) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4)
    (hCs : 0 ≤ Cs) (hCH : 0 < CH) (he : 1 ≤ e.eA ∧ 1 ≤ e.eB ∧ 1 ≤ e.eW)
    (h1 : ResH1 ((281 : ℝ) / 1000) Cs) (h2 : ResH2 ((281 : ℝ) / 1000) CH)
    (hK : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ → KineticInterface μ φ (q₀ μ φ))
    (hE1 : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H1EnergyInterface ((281 : ℝ) / 1000) Cs μ φ Tp (Nbar μ φ) (piTol μ φ) K₁ (q₁ μ φ) N)
    (hE2 : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H2EnergyInterface ((281 : ℝ) / 1000) CH μ φ Tp K₂ m₀ (q₂ μ φ) N)
    (hS : SlowCapsInterface Tp e qS) (hN : NativeProfile N)
    (hq₀ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e q₀)
    (hq₁ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e q₁)
    (hq₂ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e q₂)
    (hqS : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e qS)
    (hNbar : AtMostLinear Nbar) (hpi : AtMostLinear piTol)
    (hNbar0 : ∀ μ φ : ℝ, 0 ≤ Nbar μ φ) (hpi0 : ∀ μ φ : ℝ, 0 ≤ piTol μ φ) :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ C : ℝ, ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F → F / ν ^ 2 ≤ φ →
        C * (1 + M / ν) ^ ((9876 : ℝ) / 719 + ε) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) :=
  fixed_force_of_interfaces (by norm_num) dOf_281.le hTp hK₁ hK₂ hm₀ hCs hCH he h1 h2 hK hE1 hE2
    hS hN hq₀ hq₁ hq₂ hqS hNbar hpi hNbar0 hpi0

end OVNS.Quant
