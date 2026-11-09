import OddViscousNS.Quant.Energy.Slow.Energy

/-!
# E7-F, the slow `H²` barriers: `h` and `ζ` (F3–F4)

Route `t12_slow_fourier_route.md` §2.2, steps F3–F4, along the corrected slow field
`y_S = S + R_S` with `h = Π_H y_S`, `ζ = Π_V y_S`, and the `L²_t H¹` residual budget
`E₂ ≥ ∫ ‖corrRes‖₁²` on the piece (`E₂ = 4φ² + 4` once the roles are paid, `corrRes_budget`).

* `barrier_sup`: the **sup barrier with an `L¹` forcing** — a continuous `Z` with
  `Z(t) ≤ Z(s) + ∫ₛᵗ (D(Z) + ε)`, `D ≤ 0` above the level `Z_*`, `ε ≥ 0`, `∫ ε ≤ E`, satisfies
  `Z ≤ max(Z(a), Z_*) + E`: past the last time at or below `max(Z(a), Z_*)` the drift is
  nonpositive and only the forcing can raise `Z`.
* `corr_horiz_h2_law` (F3): `(b_h²)' + c_h² ≤ 450 a_h² b_h² + 2‖corrRes‖₁²` (T3b
  `pair_slow_horizontal_h2`, `15 a_h b_h c_h`, Young), a.e. in time (`y_S ∈ H³`, `corrRes ∈ H¹`
  a.e., from the `σ = 2` heat pair); with the interpolation `b_h² ≤ a_h c_h` this is the Riccati
  drift `−Z²/A_h² + 450 A_h² Z`, nonpositive above `Z_* = 450 A_h⁴` — `corr_horiz_h2`:
  `b_h(u)² ≤ max(b_h(τ)², 450 A_h⁴) + 2E₂` from any start `τ` (so `b_h ≲ a_h² ≈ μ²`).
* `corr_vert_h2_law` (F4): `(b_ζ²)' + c_ζ² ≤ 226 A_h² b_ζ² + 13 B_h⁴ A_ζ²/A_h⁴ + 4‖corrRes‖₁²`
  (T3c `pair_slow_vertical_h2`, `10 a_h b_ζ c_ζ + 5 b_h b_ζ √(a_ζ c_ζ)`; the mixed term by
  `√(a_ζ c_ζ) ≤ ½(θ a_ζ + c_ζ/θ)` with `θ = B_h/A_h`, so that only `h` enters the coefficient:
  `vert_h2_young`); drift `−Z²/A_ζ² + 226 A_h² Z + 13 B_h⁴A_ζ²/A_h⁴`, nonpositive above
  `Z_* = max(452 A_h² A_ζ², 6 B_h² A_ζ²/A_h²)` (`vert_drift_nonpos`) — `corr_vert_h2`:
  `b_ζ(u)² ≤ max(b_ζ(τ)², Z_*) + 4E₂` (so `b_ζ ≲ max(a_h a_ζ, b_h a_ζ/a_h) ≈ μ³`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace OVNS

/-! ### The sup barrier with an `L¹` forcing -/

/-- **Sup barrier.**  `Z` continuous on `[a, b]` with `Z(t) ≤ Z(s) + ∫ₛᵗ (D(Z(u)) + ε(u))` on
all subintervals, `D` continuous and `≤ 0` on `[Z_*, ∞)`, `ε ≥ 0` integrable with
`∫ₐᵇ ε ≤ E`.  Then `Z ≤ max(Z(a), Z_*) + E` on `[a, b]`. -/
theorem barrier_sup {Z D ε : ℝ → ℝ} {a b Zs E : ℝ} (hab : a ≤ b)
    (hZ : ContinuousOn Z (Icc a b)) (hD : Continuous D) (hDneg : ∀ x, Zs ≤ x → D x ≤ 0)
    (hε : IntervalIntegrable ε volume a b) (hε0 : ∀ u ∈ Icc a b, 0 ≤ ε u)
    (hE : (∫ u in a..b, ε u) ≤ E)
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b → Z t ≤ Z s + ∫ u in s..t, (D (Z u) + ε u)) :
    ∀ u ∈ Icc a b, Z u ≤ max (Z a) Zs + E := by
  intro u₁ hu₁
  by_contra hpos
  push Not at hpos
  set M := max (Z a) Zs with hM
  have hE0 : 0 ≤ E := le_trans (intervalIntegral.integral_nonneg hab hε0) hE
  have hclosed : IsClosed (Icc a u₁ ∩ Z ⁻¹' Iic M) :=
    (hZ.mono (Icc_subset_Icc_right hu₁.2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  obtain ⟨u₀, ⟨hu₀, hZu₀⟩, hmax⟩ :=
    (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).exists_isGreatest
      ⟨a, left_mem_Icc.2 hu₁.1, (le_max_left (Z a) Zs : Z a ≤ M)⟩
  have hZu₀' : Z u₀ ≤ M := hZu₀
  have hu₀₁ : u₀ < u₁ := lt_of_le_of_ne hu₀.2 (by rintro rfl; linarith)
  have hZgt : ∀ u, u₀ < u → u ≤ u₁ → Zs < Z u := by
    intro u h1 h2
    by_contra hn
    push Not at hn
    have hmem : u ∈ Icc a u₁ ∩ Z ⁻¹' Iic M :=
      ⟨⟨hu₀.1.trans h1.le, h2⟩, hn.trans (le_max_right _ _)⟩
    have := hmax hmem
    linarith
  have hlaw := h u₀ u₁ hu₀.1 hu₀₁.le hu₁.2
  have hsub : Icc u₀ u₁ ⊆ Icc a b := Icc_subset_Icc hu₀.1 hu₁.2
  have hDZ : IntervalIntegrable (fun u => D (Z u)) volume u₀ u₁ :=
    (hD.comp_continuousOn (hZ.mono hsub)).intervalIntegrable_of_Icc hu₀₁.le
  have hεi : IntervalIntegrable ε volume u₀ u₁ := hε.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le hu₀₁.le]
    exact hsub)
  have h1 : ∫ u in u₀..u₁, (D (Z u) + ε u) ≤ ∫ u in u₀..u₁, ε u := by
    rw [intervalIntegral.integral_add hDZ hεi]
    have h0 : ∫ u in u₀..u₁, D (Z u) ≤ ∫ _ in u₀..u₁, (0 : ℝ) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hu₀₁.le hDZ intervalIntegrable_const
        fun u hu => hDneg _ (hZgt u hu.1 hu.2.le).le
    simp only [intervalIntegral.integral_zero] at h0
    linarith
  have h2 : ∫ u in u₀..u₁, ε u ≤ ∫ u in a..b, ε u :=
    intervalIntegral.integral_mono_interval hu₀.1 hu₀₁.le hu₁.2
      (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => hε0 u (Ioc_subset_Icc_self hu)) hε
  linarith

/-! ### Elementary inequalities of the barriers -/

/-- The horizontal drift `−x²/A² + 450 A² x` is nonpositive above `450 A⁴`. -/
lemma horiz_drift_nonpos {A x : ℝ} (hA : 0 < A) (hx : 450 * A ^ 4 ≤ x) :
    -(x ^ 2 / A ^ 2) + 450 * A ^ 2 * x ≤ 0 := by
  have hA2 : 0 < A ^ 2 := by positivity
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have : 450 * A ^ 2 * x ≤ x ^ 2 / A ^ 2 := by
    rw [le_div_iff₀ hA2]
    nlinarith
  linarith

/-- The vertical drift `−x²/A_ζ² + 226 A_h² x + 13 B_h⁴ A_ζ²/A_h⁴` is nonpositive above
`max(452 A_h² A_ζ², 6 B_h² A_ζ²/A_h²)`. -/
lemma vert_drift_nonpos {Ah Aζ Bh x : ℝ} (hAh : 0 < Ah) (hAζ : 0 < Aζ) (_hBh : 0 ≤ Bh)
    (hx : max (452 * Ah ^ 2 * Aζ ^ 2) (6 * Bh ^ 2 * Aζ ^ 2 / Ah ^ 2) ≤ x) :
    -(x ^ 2 / Aζ ^ 2) + 226 * Ah ^ 2 * x + 13 * Bh ^ 4 * Aζ ^ 2 / Ah ^ 4 ≤ 0 := by
  have hAζ2 : 0 < Aζ ^ 2 := by positivity
  have hAh2 : 0 < Ah ^ 2 := by positivity
  have hAh4 : 0 < Ah ^ 4 := by positivity
  have hx1 : 452 * Ah ^ 2 * Aζ ^ 2 ≤ x := (le_max_left _ _).trans hx
  have hx2 : 6 * Bh ^ 2 * Aζ ^ 2 / Ah ^ 2 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 ≤ x := le_trans (by positivity) hx1
  have hx2' : 6 * Bh ^ 2 * Aζ ^ 2 ≤ x * Ah ^ 2 := by
    rwa [div_le_iff₀ hAh2] at hx2
  -- `226 A_h² x ≤ x²/(2A_ζ²)`
  have h1 : 226 * Ah ^ 2 * x ≤ x ^ 2 / (2 * Aζ ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- `13 B_h⁴ A_ζ²/A_h⁴ ≤ x²/(2A_ζ²)`
  have h2 : 13 * Bh ^ 4 * Aζ ^ 2 / Ah ^ 4 ≤ x ^ 2 / (2 * Aζ ^ 2) := by
    rw [div_le_div_iff₀ hAh4 (by positivity)]
    have h3 : (6 * Bh ^ 2 * Aζ ^ 2) ^ 2 ≤ (x * Ah ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hx2' 2
    nlinarith [sq_nonneg (Bh ^ 2 * Aζ ^ 2), mul_nonneg (sq_nonneg (Bh ^ 2 * Aζ ^ 2)) hAζ2.le]
  have h3 : x ^ 2 / (2 * Aζ ^ 2) + x ^ 2 / (2 * Aζ ^ 2) = x ^ 2 / Aζ ^ 2 := by
    field_simp
    ring
  linarith

/-- **The Young step of the vertical `H²` law**: with `a_h ≤ A_h`, `b_h ≤ B_h`, `a_ζ ≤ A_ζ`,
`2 c ρ + 2(10 a_h b c + 5 b_h b √(a_ζ c)) ≤ c² + 226 A_h² b² + 13 B_h⁴ A_ζ²/A_h⁴ + 4ρ²`
(`√(a_ζ c) ≤ ½(θ a_ζ + c/θ)`, `θ = B_h/A_h`). -/
lemma vert_h2_young {a bh aζ b c ρ Ah Bh Aζ : ℝ} (hAh : 0 < Ah) (hBh : 0 < Bh) (hAζ : 0 ≤ Aζ)
    (_ha0 : 0 ≤ a) (hbh0 : 0 ≤ bh) (haζ0 : 0 ≤ aζ) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (_hρ0 : 0 ≤ ρ)
    (ha : a ≤ Ah) (hbh : bh ≤ Bh) (haζ : aζ ≤ Aζ) :
    2 * (c * ρ) + 2 * (10 * a * b * c + 5 * bh * b * Real.sqrt (aζ * c)) ≤
      c ^ 2 + 226 * Ah ^ 2 * b ^ 2 + 13 * Bh ^ 4 * Aζ ^ 2 / Ah ^ 4 + 4 * ρ ^ 2 := by
  set θ := Bh / Ah with hθ
  have hθ0 : 0 < θ := div_pos hBh hAh
  have hθA : θ * Ah = Bh := by rw [hθ]; field_simp
  -- `√(a_ζ c) ≤ (θ a_ζ + c/θ)/2`
  have hS : Real.sqrt (aζ * c) ≤ (θ * aζ + c / θ) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : c = θ * (c / θ) := by field_simp
    nlinarith [sq_nonneg (θ * aζ - c / θ), mul_nonneg hθ0.le haζ0,
      div_nonneg hc0 hθ0.le]
  have hS0 : 0 ≤ Real.sqrt (aζ * c) := Real.sqrt_nonneg _
  -- the forcing: `2cρ ≤ c²/4 + 4ρ²`
  have h1 : 2 * (c * ρ) ≤ c ^ 2 / 4 + 4 * ρ ^ 2 := by nlinarith [sq_nonneg (c / 2 - 2 * ρ)]
  -- `20 a b c ≤ c²/2 + 200 A_h² b²`
  have h2 : 20 * a * b * c ≤ c ^ 2 / 2 + 200 * Ah ^ 2 * b ^ 2 := by
    have : a * b * c ≤ Ah * b * c := by
      have := mul_nonneg hb0 hc0
      nlinarith
    nlinarith [sq_nonneg (c - 20 * Ah * b)]
  -- the mixed term
  have h3 : 10 * bh * b * Real.sqrt (aζ * c) ≤
      5 * bh * b * (θ * aζ) + 5 * bh * b * (c / θ) := by
    have := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 10 * bh * b)
    linarith
  -- `5 b_h b c/θ ≤ 5 A_h b c ≤ c²/4 + 25 A_h² b²`
  have h4 : 5 * bh * b * (c / θ) ≤ c ^ 2 / 4 + 25 * Ah ^ 2 * b ^ 2 := by
    have hbhθ : bh / θ ≤ Ah := by
      rw [div_le_iff₀ hθ0, mul_comm]; linarith
    have e : 5 * bh * b * (c / θ) = 5 * (bh / θ) * b * c := by field_simp
    rw [e]
    have : 5 * (bh / θ) * b * c ≤ 5 * Ah * b * c := by
      have := mul_nonneg hb0 hc0
      have := div_nonneg hbh0 hθ0.le
      nlinarith
    nlinarith [sq_nonneg (c - 10 * Ah * b)]
  -- `5 b_h b θ a_ζ ≤ 5 K b ≤ A_h² b²/2 + 25 K²/(2A_h²)`, `K = B_h θ A_ζ`
  set K := Bh * θ * Aζ with hK
  have hK0 : 0 ≤ K := by positivity
  have h5 : 5 * bh * b * (θ * aζ) ≤ 5 * K * b := by
    have : bh * (θ * aζ) ≤ Bh * (θ * Aζ) :=
      mul_le_mul hbh (mul_le_mul_of_nonneg_left haζ hθ0.le) (by positivity) hBh.le
    have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 5 * b)
    rw [hK]; nlinarith
  have h6 : 5 * K * b ≤ Ah ^ 2 * b ^ 2 / 2 + 25 * K ^ 2 / (2 * Ah ^ 2) := by
    have hA2 : 0 < Ah ^ 2 := by positivity
    rw [div_add_div _ _ two_ne_zero (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Ah ^ 2 * b - 5 * K)]
  have h7 : 25 * K ^ 2 / (2 * Ah ^ 2) = 25 * Bh ^ 4 * Aζ ^ 2 / (2 * Ah ^ 4) := by
    rw [hK, hθ]
    field_simp
  have h8 : 25 * Bh ^ 4 * Aζ ^ 2 / (2 * Ah ^ 4) ≤ 13 * Bh ^ 4 * Aζ ^ 2 / Ah ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg hBh.le 4, pow_nonneg hAh.le 4, sq_nonneg Aζ,
      mul_nonneg (mul_nonneg (pow_nonneg hBh.le 4) (sq_nonneg Aζ)) (pow_nonneg hAh.le 4)]
  nlinarith

namespace Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### Almost-everywhere regularity along the piece -/

/-- `y_S ∈ H³` at almost every time of a piece (dissipation of the `σ = 2` heat pair). -/
theorem ae_inH3_corr (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), InH 3 (corrSlow r g y u) := by
  have hp := (heatPair_corrSlow h hr (Or.inr (Or.inr rfl)) (hs.trans hst) ht).mono hs le_rfl
  filter_upwards [hp.ae_inH hst] with u hu
  have e : (2 : ℝ) + 1 = 3 := by norm_num
  rwa [e] at hu

/-- `corrForce ∈ H¹` at almost every time of a piece (`L²_t H¹` of the force of the `σ = 2`
heat pair). -/
theorem ae_inH1_corrForce (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), InH 1 (corrForce r g y u) := by
  have hp := (heatPair_corrSlow h hr (Or.inr (Or.inr rfl)) (hs.trans hst) ht).mono hs le_rfl
  have hl := hp.force_l2
  have hm : AEMeasurable (fun u => hsE ((2 : ℝ) - 1) (corrForce r g y u))
      (volume.restrict (Icc s t)) := by
    refine AEMeasurable.tsum fun k => ?_
    have : ContinuousOn (fun u => sobWeight ((2 : ℝ) - 1) k * ‖corrForce r g y u k‖ ^ 2)
        (Icc s t) := continuousOn_const.mul ((hp.force_cont k).norm.pow 2)
    exact (ENNReal.continuous_ofReal.comp_continuousOn this).aemeasurable measurableSet_Icc
  filter_upwards [ae_lt_top' hm hl.ne] with u hu
  have := inH_iff_hsE_lt_top.2 hu
  have e : (2 : ℝ) - 1 = 1 := by norm_num
  rwa [e] at this

/-- `B(y_S, y_S) ∈ H¹` along the solution. -/
theorem Bsym_corrSlow_inH1 (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) : InH 1 (Bsym (corrSlow r g y u) (corrSlow r g y u)) := by
  have hz := corrSlow_adm h hr hu huT
  have hone : Mult.Bdd (fun _ _ _ _ _ => (1 : ℂ)) := fun _ _ _ _ _ => by simp
  rw [← Qm_one hz hz]
  have := (hnorm_Qm_le hone (by norm_num : (1 : ℝ) ≤ 2) hz.mz hz.mz hz.mz hz.mz).1
  have e : (2 : ℝ) - 1 = 1 := by norm_num
  rwa [e] at this

/-- `corrRes = corrForce + B(y_S,y_S) ∈ H¹` at almost every time of a piece. -/
theorem ae_inH1_corrRes (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), InH 1 (corrRes r g y u) := by
  filter_upwards [ae_inH1_corrForce h hr hs hst ht, ae_restrict_mem measurableSet_Icc] with u hu hmem
  have e : corrRes r g y u = corrForce r g y u + Bsym (corrSlow r g y u) (corrSlow r g y u) := by
    simp [corrForce]
  rw [e]
  exact hu.add (Bsym_corrSlow_inH1 h hr (hs.trans hmem.1) (lt_lifespan hmem.2 ht))

/-! ### F3: the horizontal `H²` law and barrier -/

/-- **F3, the law** (route §2.2, T3b at `c_L = 5`):
`b_h(t)² + ∫ₛᵗ c_h² ≤ b_h(s)² + ∫ₛᵗ (450 a_h² b_h² + 2‖corrRes‖₁²)`. -/
theorem corr_horiz_h2_law (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    hnorm 2 (PiH (corrSlow r g y t)) ^ 2 + ∫ u in s..t, hnorm 3 (PiH (corrSlow r g y u)) ^ 2 ≤
      hnorm 2 (PiH (corrSlow r g y s)) ^ 2 + ∫ u in s..t,
        (450 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 * hnorm 2 (PiH (corrSlow r g y u)) ^ 2 +
          2 * hnorm 1 (corrRes r g y u) ^ 2) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hp : HeatPair 2 s t (fun u => PiH (corrSlow r g y u)) (fun u => PiH (corrForce r g y u)) :=
    (heatPair_corrH h hr (Or.inr (Or.inr rfl)) ht0 ht).mono hs le_rfl
  have hc1 : ContinuousOn (fun u => hnorm 1 (PiH (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrH_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hc2 : ContinuousOn (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrH_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hR : IntervalIntegrable (fun u => 450 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 *
      hnorm 2 (PiH (corrSlow r g y u)) ^ 2 + 2 * hnorm 1 (corrRes r g y u) ^ 2) volume s t :=
    (((continuousOn_const.mul hc1).mul hc2).intervalIntegrable_of_Icc hst).add
      ((intervalIntegrable_corrRes_sq h hr hs hst ht).const_mul 2)
  have key := hp.energy_le (τ := 3) (θ := 1) (by norm_num) hst hR ?_
  · linarith
  filter_upwards [ae_inH3_corr h hr hs hst ht, ae_inH1_corrRes h hr hs hst ht,
    ae_restrict_mem measurableSet_Icc] with u hz3 hres1 hu
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hz := corrSlow_adm h hr hu0 huT
  have hz' := PiS_corrSlow r g y u
  have hH3 : InH ((2 : ℝ) + 1) (PiH (corrSlow r g y u)) := by
    have e : (2 : ℝ) + 1 = 3 := by norm_num
    rw [e]; exact hz3.PiH
  have hres1' : InH ((2 : ℝ) - 1) (corrRes r g y u) := by
    have e : (2 : ℝ) - 1 = 1 := by norm_num
    rw [e]; exact hres1
  have hB1 : InH ((2 : ℝ) - 1) (Bsym (corrSlow r g y u) (corrSlow r g y u)) := by
    have e : (2 : ℝ) - 1 = 1 := by norm_num
    rw [e]; exact Bsym_corrSlow_inH1 h hr hu0 huT
  show 2 * pair 2 (PiH (corrSlow r g y u)) (PiH (corrForce r g y u)) ≤
    1 * hnorm 3 (PiH (corrSlow r g y u)) ^ 2 +
      (450 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 * hnorm 2 (PiH (corrSlow r g y u)) ^ 2 +
        2 * hnorm 1 (corrRes r g y u) ^ 2)
  rw [pair_PiH, corrForce, pair_sub hH3 hres1' hB1]
  have hT3 := pair_slow_horizontal_h2 hz hz3 hz'
  rw [pair_PiH] at hT3
  have hle := (pair_le hH3 hres1').2
  have e3 : (2 : ℝ) + 1 = 3 := by norm_num
  have e1 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [e3, e1] at hle
  have h2 := le_abs_self (pair 2 (PiH (corrSlow r g y u)) (corrRes r g y u))
  have h2' := neg_abs_le (pair 2 (PiH (corrSlow r g y u))
    (Bsym (corrSlow r g y u) (corrSlow r g y u)))
  have h3 := hnorm_nonneg 3 (PiH (corrSlow r g y u))
  have h4 := hnorm_nonneg 1 (corrRes r g y u)
  have h5 := hnorm_nonneg 1 (PiH (corrSlow r g y u))
  have h6 := hnorm_nonneg 2 (PiH (corrSlow r g y u))
  have hprod : 0 ≤ hnorm 1 (PiH (corrSlow r g y u)) * hnorm 2 (PiH (corrSlow r g y u)) :=
    mul_nonneg h5 h6
  have hY1 : 2 * (hnorm 3 (PiH (corrSlow r g y u)) * hnorm 1 (corrRes r g y u)) ≤
      hnorm 3 (PiH (corrSlow r g y u)) ^ 2 / 2 + 2 * hnorm 1 (corrRes r g y u) ^ 2 := by
    nlinarith [sq_nonneg (hnorm 3 (PiH (corrSlow r g y u)) - 2 * hnorm 1 (corrRes r g y u))]
  have hY2 : 30 * ((hnorm 1 (PiH (corrSlow r g y u)) * hnorm 2 (PiH (corrSlow r g y u))) *
      hnorm 3 (PiH (corrSlow r g y u))) ≤ hnorm 3 (PiH (corrSlow r g y u)) ^ 2 / 2 +
        450 * (hnorm 1 (PiH (corrSlow r g y u)) * hnorm 2 (PiH (corrSlow r g y u))) ^ 2 := by
    nlinarith [sq_nonneg (hnorm 3 (PiH (corrSlow r g y u)) -
      30 * (hnorm 1 (PiH (corrSlow r g y u)) * hnorm 2 (PiH (corrSlow r g y u))))]
  nlinarith

/-- **F3, the barrier**: with `a_h ≤ A_h` on the piece and `∫ₛᵗ ‖corrRes‖₁² ≤ E₂`,
`b_h(u)² ≤ max(b_h(τ)², 450 A_h⁴) + 2E₂` for all `τ ≤ u` in the piece. -/
theorem corr_horiz_h2 (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {Ah E₂ : ℝ} (hAh : 0 < Ah)
    (hah : ∀ u ∈ Icc s t, hnorm 1 (PiH (corrSlow r g y u)) ≤ Ah)
    (hE : (∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ E₂) :
    ∀ τ ∈ Icc s t, ∀ u ∈ Icc τ t, hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤
      max (hnorm 2 (PiH (corrSlow r g y τ)) ^ 2) (450 * Ah ^ 4) + 2 * E₂ := by
  intro τ hτ
  have ht0 : 0 ≤ t := hs.trans hst
  have hτ0 : 0 ≤ τ := hs.trans hτ.1
  set Z : ℝ → ℝ := fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2 with hZ
  have hZc : ContinuousOn Z (Icc τ t) :=
    (continuousOn_corrH_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hτ0)
  have hεi : IntervalIntegrable (fun u => 2 * hnorm 1 (corrRes r g y u) ^ 2) volume τ t :=
    (intervalIntegrable_corrRes_sq h hr hτ0 hτ.2 (lt_lifespan le_rfl ht)).const_mul 2
  have hεE : (∫ u in τ..t, 2 * hnorm 1 (corrRes r g y u) ^ 2) ≤ 2 * E₂ := by
    rw [intervalIntegral.integral_const_mul]
    have : (∫ u in τ..t, hnorm 1 (corrRes r g y u) ^ 2) ≤
        ∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2 :=
      intervalIntegral.integral_mono_interval hτ.1 hτ.2 le_rfl
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (intervalIntegrable_corrRes_sq h hr hs hst ht)
    linarith
  refine barrier_sup (D := fun x => -(x ^ 2 / Ah ^ 2) + 450 * Ah ^ 2 * x) hτ.2 hZc
    (by fun_prop) (fun x hx => horiz_drift_nonpos hAh hx) hεi (fun _ _ => by positivity) hεE ?_
  intro s' t' hs' hst' ht'
  have hs'0 : 0 ≤ s' := hτ0.trans hs'
  have ht'T := lt_lifespan ht' ht
  have hlaw := corr_horiz_h2_law h hr hs'0 hst' ht'T
  have hsub : Icc s' t' ⊆ Icc s t := Icc_subset_Icc (hτ.1.trans hs') ht'
  have hp : HeatPair 2 s' t' (fun u => PiH (corrSlow r g y u)) (fun u => PiH (corrForce r g y u)) :=
    (heatPair_corrH h hr (Or.inr (Or.inr rfl)) ht0 ht).mono hs'0 ht'
  have hD : IntervalIntegrable (fun u => hnorm 3 (PiH (corrSlow r g y u)) ^ 2) volume s' t' := by
    have := hp.intervalIntegrable_dissipation hst'
    have e : (2 : ℝ) + 1 = 3 := by norm_num
    rwa [e] at this
  have hZc' : ContinuousOn Z (Icc s' t') := hZc.mono (Icc_subset_Icc hs' ht')
  -- the dissipation dominates the Riccati term: `Z²/A_h² ≤ c_h²` a.e.
  have hdiss : ∫ u in s'..t', Z u ^ 2 / Ah ^ 2 ≤ ∫ u in s'..t', hnorm 3 (PiH (corrSlow r g y u)) ^ 2 := by
    refine intervalIntegral.integral_mono_ae_restrict hst'
      (((hZc'.pow 2).div_const _).intervalIntegrable_of_Icc hst') hD ?_
    filter_upwards [ae_inH3_corr h hr hs'0 hst' ht'T, ae_restrict_mem measurableSet_Icc] with u hz3 hu
    have hH3 : InH ((2 : ℝ) + 1) (PiH (corrSlow r g y u)) := by
      have e : (2 : ℝ) + 1 = 3 := by norm_num
      rw [e]; exact hz3.PiH
    have hint := hnorm_sq_le_mul hH3
    have e3 : (2 : ℝ) + 1 = 3 := by norm_num
    have e1 : (2 : ℝ) - 1 = 1 := by norm_num
    rw [e3, e1] at hint
    have ha := hah u (hsub hu)
    have h1 := hnorm_nonneg 1 (PiH (corrSlow r g y u))
    have h3 := hnorm_nonneg 3 (PiH (corrSlow r g y u))
    have h2 := hnorm_nonneg 2 (PiH (corrSlow r g y u))
    simp only [hZ]
    rw [div_le_iff₀ (by positivity)]
    have h4 : hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤ Ah * hnorm 3 (PiH (corrSlow r g y u)) :=
      hint.trans (mul_le_mul_of_nonneg_right ha h3)
    calc (hnorm 2 (PiH (corrSlow r g y u)) ^ 2) ^ 2
        ≤ (Ah * hnorm 3 (PiH (corrSlow r g y u))) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
      _ = hnorm 3 (PiH (corrSlow r g y u)) ^ 2 * Ah ^ 2 := by ring
  -- the quadratic term is at most `450 A_h² Z`
  have hquad : ∫ u in s'..t', (450 * hnorm 1 (PiH (corrSlow r g y u)) ^ 2 *
      hnorm 2 (PiH (corrSlow r g y u)) ^ 2 + 2 * hnorm 1 (corrRes r g y u) ^ 2) ≤
      ∫ u in s'..t', (450 * Ah ^ 2 * Z u + 2 * hnorm 1 (corrRes r g y u) ^ 2) := by
    have hc1 : ContinuousOn (fun u => hnorm 1 (PiH (corrSlow r g y u)) ^ 2) (Icc s' t') :=
      (continuousOn_corrH_sq h hr (Or.inr (Or.inl rfl)) ht0 ht).mono (Icc_subset_Icc hs'0 ht')
    have hεi' : IntervalIntegrable (fun u => 2 * hnorm 1 (corrRes r g y u) ^ 2) volume s' t' :=
      (intervalIntegrable_corrRes_sq h hr hs'0 hst' ht'T).const_mul 2
    refine intervalIntegral.integral_mono_on hst'
      ((((continuousOn_const.mul hc1).mul hZc').intervalIntegrable_of_Icc hst').add hεi')
      (((continuousOn_const.mul hZc').intervalIntegrable_of_Icc hst').add hεi') fun u hu => ?_
    have ha := hah u (hsub hu)
    have h1 := hnorm_nonneg 1 (PiH (corrSlow r g y u))
    have hsq : hnorm 1 (PiH (corrSlow r g y u)) ^ 2 ≤ Ah ^ 2 := pow_le_pow_left₀ h1 ha 2
    have := mul_le_mul_of_nonneg_right hsq (sq_nonneg (hnorm 2 (PiH (corrSlow r g y u))))
    simp only [hZ]
    nlinarith
  have hDi : IntervalIntegrable (fun u => Z u ^ 2 / Ah ^ 2) volume s' t' :=
    ((hZc'.pow 2).div_const _).intervalIntegrable_of_Icc hst'
  have hZi : IntervalIntegrable (fun u => 450 * Ah ^ 2 * Z u) volume s' t' :=
    (continuousOn_const.mul hZc').intervalIntegrable_of_Icc hst'
  have hεi' : IntervalIntegrable (fun u => 2 * hnorm 1 (corrRes r g y u) ^ 2) volume s' t' :=
    (intervalIntegrable_corrRes_sq h hr hs'0 hst' ht'T).const_mul 2
  have e : ∫ u in s'..t', (-(Z u ^ 2 / Ah ^ 2) + 450 * Ah ^ 2 * Z u +
      2 * hnorm 1 (corrRes r g y u) ^ 2) =
      -(∫ u in s'..t', Z u ^ 2 / Ah ^ 2) + ∫ u in s'..t',
        (450 * Ah ^ 2 * Z u + 2 * hnorm 1 (corrRes r g y u) ^ 2) := by
    have h0 := intervalIntegral.integral_add hDi.neg (hZi.add hεi')
    simp only [Pi.neg_apply] at h0
    rw [intervalIntegral.integral_neg] at h0
    rw [← h0]
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring
  show Z t' ≤ Z s' + ∫ u in s'..t', (-(Z u ^ 2 / Ah ^ 2) + 450 * Ah ^ 2 * Z u +
    2 * hnorm 1 (corrRes r g y u) ^ 2)
  rw [e]
  simp only [hZ] at hlaw ⊢
  linarith

/-! ### F4: the vertical `H²` law and barrier -/

/-- **F4, the law** (route §2.2, T3c at `c_L = 5`, with the mixed term split by
`θ = B_h/A_h`): with `a_h ≤ A_h`, `b_h ≤ B_h`, `a_ζ ≤ A_ζ` on the piece,
`b_ζ(t)² + ∫ₛᵗ c_ζ² ≤ b_ζ(s)² + ∫ₛᵗ (226 A_h² b_ζ² + 13 B_h⁴A_ζ²/A_h⁴ + 4‖corrRes‖₁²)`. -/
theorem corr_vert_h2_law (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {Ah Bh Aζ : ℝ} (hAh : 0 < Ah) (hBh : 0 < Bh)
    (hAζ : 0 ≤ Aζ)
    (hah : ∀ u ∈ Icc s t, hnorm 1 (PiH (corrSlow r g y u)) ≤ Ah)
    (hbh : ∀ u ∈ Icc s t, hnorm 2 (PiH (corrSlow r g y u)) ≤ Bh)
    (haζ : ∀ u ∈ Icc s t, hnorm 1 (PiV (corrSlow r g y u)) ≤ Aζ) :
    hnorm 2 (PiV (corrSlow r g y t)) ^ 2 + ∫ u in s..t, hnorm 3 (PiV (corrSlow r g y u)) ^ 2 ≤
      hnorm 2 (PiV (corrSlow r g y s)) ^ 2 + ∫ u in s..t,
        (226 * Ah ^ 2 * hnorm 2 (PiV (corrSlow r g y u)) ^ 2 + 13 * Bh ^ 4 * Aζ ^ 2 / Ah ^ 4 +
          4 * hnorm 1 (corrRes r g y u) ^ 2) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hp : HeatPair 2 s t (fun u => PiV (corrSlow r g y u)) (fun u => PiV (corrForce r g y u)) :=
    (heatPair_corrV h hr (Or.inr (Or.inr rfl)) ht0 ht).mono hs le_rfl
  have hc2 : ContinuousOn (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2) (Icc s t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
  have hR : IntervalIntegrable (fun u => 226 * Ah ^ 2 * hnorm 2 (PiV (corrSlow r g y u)) ^ 2 +
      13 * Bh ^ 4 * Aζ ^ 2 / Ah ^ 4 + 4 * hnorm 1 (corrRes r g y u) ^ 2) volume s t :=
    (((continuousOn_const.mul hc2).add continuousOn_const).intervalIntegrable_of_Icc hst).add
      ((intervalIntegrable_corrRes_sq h hr hs hst ht).const_mul 4)
  have key := hp.energy_le (τ := 3) (θ := 1) (by norm_num) hst hR ?_
  · linarith
  filter_upwards [ae_inH3_corr h hr hs hst ht, ae_inH1_corrRes h hr hs hst ht,
    ae_restrict_mem measurableSet_Icc] with u hz3 hres1 hu
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hz := corrSlow_adm h hr hu0 huT
  have hz' := PiS_corrSlow r g y u
  have hV3 : InH ((2 : ℝ) + 1) (PiV (corrSlow r g y u)) := by
    have e : (2 : ℝ) + 1 = 3 := by norm_num
    rw [e]; exact hz3.PiV
  have hres1' : InH ((2 : ℝ) - 1) (corrRes r g y u) := by
    have e : (2 : ℝ) - 1 = 1 := by norm_num
    rw [e]; exact hres1
  have hB1 : InH ((2 : ℝ) - 1) (Bsym (corrSlow r g y u) (corrSlow r g y u)) := by
    have e : (2 : ℝ) - 1 = 1 := by norm_num
    rw [e]; exact Bsym_corrSlow_inH1 h hr hu0 huT
  show 2 * pair 2 (PiV (corrSlow r g y u)) (PiV (corrForce r g y u)) ≤
    1 * hnorm 3 (PiV (corrSlow r g y u)) ^ 2 +
      (226 * Ah ^ 2 * hnorm 2 (PiV (corrSlow r g y u)) ^ 2 + 13 * Bh ^ 4 * Aζ ^ 2 / Ah ^ 4 +
        4 * hnorm 1 (corrRes r g y u) ^ 2)
  rw [pair_PiV, corrForce, pair_sub hV3 hres1' hB1]
  have hT3 := pair_slow_vertical_h2 hz hz3 hz'
  rw [pair_PiV] at hT3
  have hle := (pair_le hV3 hres1').2
  have e3 : (2 : ℝ) + 1 = 3 := by norm_num
  have e1 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [e3, e1] at hle
  have h2 := le_abs_self (pair 2 (PiV (corrSlow r g y u)) (corrRes r g y u))
  have h2' := neg_abs_le (pair 2 (PiV (corrSlow r g y u))
    (Bsym (corrSlow r g y u) (corrSlow r g y u)))
  have hY := vert_h2_young hAh hBh hAζ (hnorm_nonneg 1 (PiH (corrSlow r g y u)))
    (hnorm_nonneg 2 (PiH (corrSlow r g y u))) (hnorm_nonneg 1 (PiV (corrSlow r g y u)))
    (hnorm_nonneg 2 (PiV (corrSlow r g y u))) (hnorm_nonneg 3 (PiV (corrSlow r g y u)))
    (hnorm_nonneg 1 (corrRes r g y u)) (hah u hu) (hbh u hu) (haζ u hu)
  linarith

/-- **F4, the barrier**: with `a_h ≤ A_h`, `b_h ≤ B_h`, `a_ζ ≤ A_ζ` on the piece and
`∫ₛᵗ ‖corrRes‖₁² ≤ E₂`,
`b_ζ(u)² ≤ max(b_ζ(τ)², max(452 A_h² A_ζ², 6 B_h² A_ζ²/A_h²)) + 4E₂` for all `τ ≤ u` in the
piece. -/
theorem corr_vert_h2 (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) {Ah Bh Aζ E₂ : ℝ} (hAh : 0 < Ah) (hBh : 0 < Bh)
    (hAζ : 0 < Aζ)
    (hah : ∀ u ∈ Icc s t, hnorm 1 (PiH (corrSlow r g y u)) ≤ Ah)
    (hbh : ∀ u ∈ Icc s t, hnorm 2 (PiH (corrSlow r g y u)) ≤ Bh)
    (haζ : ∀ u ∈ Icc s t, hnorm 1 (PiV (corrSlow r g y u)) ≤ Aζ)
    (hE : (∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ E₂) :
    ∀ τ ∈ Icc s t, ∀ u ∈ Icc τ t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤
      max (hnorm 2 (PiV (corrSlow r g y τ)) ^ 2)
        (max (452 * Ah ^ 2 * Aζ ^ 2) (6 * Bh ^ 2 * Aζ ^ 2 / Ah ^ 2)) + 4 * E₂ := by
  intro τ hτ
  have ht0 : 0 ≤ t := hs.trans hst
  have hτ0 : 0 ≤ τ := hs.trans hτ.1
  set Z : ℝ → ℝ := fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2 with hZ
  set c₀ : ℝ := 13 * Bh ^ 4 * Aζ ^ 2 / Ah ^ 4 with hc₀
  have hZc : ContinuousOn Z (Icc τ t) :=
    (continuousOn_corrV_sq h hr (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hτ0)
  have hεi : IntervalIntegrable (fun u => 4 * hnorm 1 (corrRes r g y u) ^ 2) volume τ t :=
    (intervalIntegrable_corrRes_sq h hr hτ0 hτ.2 (lt_lifespan le_rfl ht)).const_mul 4
  have hεE : (∫ u in τ..t, 4 * hnorm 1 (corrRes r g y u) ^ 2) ≤ 4 * E₂ := by
    rw [intervalIntegral.integral_const_mul]
    have : (∫ u in τ..t, hnorm 1 (corrRes r g y u) ^ 2) ≤
        ∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2 :=
      intervalIntegral.integral_mono_interval hτ.1 hτ.2 le_rfl
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (intervalIntegrable_corrRes_sq h hr hs hst ht)
    linarith
  refine barrier_sup (D := fun x => -(x ^ 2 / Aζ ^ 2) + 226 * Ah ^ 2 * x + c₀) hτ.2 hZc
    (by fun_prop) (fun x hx => vert_drift_nonpos hAh hAζ hBh.le hx) hεi
    (fun _ _ => by positivity) hεE ?_
  intro s' t' hs' hst' ht'
  have hs'0 : 0 ≤ s' := hτ0.trans hs'
  have ht'T := lt_lifespan ht' ht
  have hsub : Icc s' t' ⊆ Icc s t := Icc_subset_Icc (hτ.1.trans hs') ht'
  have hlaw := corr_vert_h2_law h hr hs'0 hst' ht'T hAh hBh hAζ.le
    (fun u hu => hah u (hsub hu)) (fun u hu => hbh u (hsub hu)) (fun u hu => haζ u (hsub hu))
  have hp : HeatPair 2 s' t' (fun u => PiV (corrSlow r g y u)) (fun u => PiV (corrForce r g y u)) :=
    (heatPair_corrV h hr (Or.inr (Or.inr rfl)) ht0 ht).mono hs'0 ht'
  have hD : IntervalIntegrable (fun u => hnorm 3 (PiV (corrSlow r g y u)) ^ 2) volume s' t' := by
    have := hp.intervalIntegrable_dissipation hst'
    have e : (2 : ℝ) + 1 = 3 := by norm_num
    rwa [e] at this
  have hZc' : ContinuousOn Z (Icc s' t') := hZc.mono (Icc_subset_Icc hs' ht')
  -- the dissipation dominates the Riccati term: `Z²/A_ζ² ≤ c_ζ²` a.e.
  have hdiss : ∫ u in s'..t', Z u ^ 2 / Aζ ^ 2 ≤
      ∫ u in s'..t', hnorm 3 (PiV (corrSlow r g y u)) ^ 2 := by
    refine intervalIntegral.integral_mono_ae_restrict hst'
      (((hZc'.pow 2).div_const _).intervalIntegrable_of_Icc hst') hD ?_
    filter_upwards [ae_inH3_corr h hr hs'0 hst' ht'T, ae_restrict_mem measurableSet_Icc] with u hz3 hu
    have hV3 : InH ((2 : ℝ) + 1) (PiV (corrSlow r g y u)) := by
      have e : (2 : ℝ) + 1 = 3 := by norm_num
      rw [e]; exact hz3.PiV
    have hint := hnorm_sq_le_mul hV3
    have e3 : (2 : ℝ) + 1 = 3 := by norm_num
    have e1 : (2 : ℝ) - 1 = 1 := by norm_num
    rw [e3, e1] at hint
    have ha := haζ u (hsub hu)
    have h3 := hnorm_nonneg 3 (PiV (corrSlow r g y u))
    simp only [hZ]
    rw [div_le_iff₀ (by positivity)]
    have h4 : hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤ Aζ * hnorm 3 (PiV (corrSlow r g y u)) :=
      hint.trans (mul_le_mul_of_nonneg_right ha h3)
    calc (hnorm 2 (PiV (corrSlow r g y u)) ^ 2) ^ 2
        ≤ (Aζ * hnorm 3 (PiV (corrSlow r g y u))) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
      _ = hnorm 3 (PiV (corrSlow r g y u)) ^ 2 * Aζ ^ 2 := by ring
  have hDi : IntervalIntegrable (fun u => Z u ^ 2 / Aζ ^ 2) volume s' t' :=
    ((hZc'.pow 2).div_const _).intervalIntegrable_of_Icc hst'
  have hZi : IntervalIntegrable (fun u => 226 * Ah ^ 2 * Z u + c₀) volume s' t' :=
    ((continuousOn_const.mul hZc').add continuousOn_const).intervalIntegrable_of_Icc hst'
  have hεi' : IntervalIntegrable (fun u => 4 * hnorm 1 (corrRes r g y u) ^ 2) volume s' t' :=
    (intervalIntegrable_corrRes_sq h hr hs'0 hst' ht'T).const_mul 4
  have e : ∫ u in s'..t', (-(Z u ^ 2 / Aζ ^ 2) + 226 * Ah ^ 2 * Z u + c₀ +
      4 * hnorm 1 (corrRes r g y u) ^ 2) =
      -(∫ u in s'..t', Z u ^ 2 / Aζ ^ 2) + ∫ u in s'..t',
        (226 * Ah ^ 2 * Z u + c₀ + 4 * hnorm 1 (corrRes r g y u) ^ 2) := by
    have h0 := intervalIntegral.integral_add hDi.neg (hZi.add hεi')
    simp only [Pi.neg_apply] at h0
    rw [intervalIntegral.integral_neg] at h0
    rw [← h0]
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring
  show Z t' ≤ Z s' + ∫ u in s'..t', (-(Z u ^ 2 / Aζ ^ 2) + 226 * Ah ^ 2 * Z u + c₀ +
    4 * hnorm 1 (corrRes r g y u) ^ 2)
  rw [e]
  simp only [hZ, hc₀] at hlaw ⊢
  linarith

end Quant

end OVNS

end
