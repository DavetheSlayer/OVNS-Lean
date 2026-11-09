import OddViscousNS.Quant.Energy.Kinetic.Defs

/-!
# E4: degree bookkeeping of the kinetic threshold (Table quant-fixed)

`kinetic_degree`: `DegreeBelow σ (dOf σ) e kinThreshold` — the R1 duty of the kinetic roles
22–27 and 36 (TeX Table quant-fixed: "other quadratic, tested, trace, raised-domain and zero
roles `< 13`").  With the fixed-force scaling `P_F ≍ μ^β`, `y ≍ μ^v`, `A_S ≲ μ^{eA+δ}`,
`B_S ≲ μ^{eB+δ}`, `W_S ≲ μ^{eW+δ}` (`CapsScaled`) and slow exponents `eA ≤ 2`, `eB ≤ 4`,
`eW ≤ 5/2` (`slowExpHA = (3/2, 2, 3, 3/2)`, `slowExpEl = (2, 4, 4, 2)` and the Fourier-side route
`(2, 3, 4, 5/2)`), every monomial of
`kinThreshold` has degree `≤ 5β − 3/2 < d = 7β − 3`; the worst is `y(A_S + P_F)(W_S + y)` of
`fourierFloor`, degree `2v + max(eA + δ, β) ≤ 5β − 3/2` (the survey's hand count `≈ 8.2` at
`σ = 281/1000` versus `d ≈ 13.74`; here `5β − 3/2 ≈ 10.45`).  With `W_S ≲ μ^{eW+δ} ≤ μ³`
(`eW ≤ 5/2`, `δ ≤ 1/2`) the `W_S`-monomials have degree `≤ max(6, 2β + 2, 3β + 5/2) ≤ 5β − 3/2`
since `β ≥ 2` (e.g. `W_S(A_S + P_F + 1)(W_S + y + 1)`: `3 + (β + 1/2) + (2β − 1)`).
-/

open scoped ENNReal

noncomputable section

namespace OVNS.Quant

/-! ### Degree bookkeeping (Table quant-fixed) -/

/-- Degree helper: a product of three nonnegative atoms bounded by `Lᵢ μ^{eᵢ}` is bounded by
`L₁L₂L₃ μ^κ` once `e₁ + e₂ + e₃ ≤ κ` (`μ ≥ 1`). -/
lemma prod3_le_rpow {μ L₁ L₂ L₃ x₁ x₂ x₃ e₁ e₂ e₃ κ : ℝ} (hμ : 1 ≤ μ) (hL₁ : 0 ≤ L₁)
    (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃) (h₂ : 0 ≤ x₂) (h₃ : 0 ≤ x₃)
    (hx₁ : x₁ ≤ L₁ * μ ^ e₁) (hx₂ : x₂ ≤ L₂ * μ ^ e₂) (hx₃ : x₃ ≤ L₃ * μ ^ e₃)
    (he : e₁ + e₂ + e₃ ≤ κ) : x₁ * x₂ * x₃ ≤ L₁ * L₂ * L₃ * μ ^ κ := by
  have hμ0 : 0 < μ := by linarith
  have h1 : x₁ * x₂ * x₃ ≤ (L₁ * μ ^ e₁) * (L₂ * μ ^ e₂) * (L₃ * μ ^ e₃) := by
    have := mul_le_mul hx₁ hx₂ h₂ (by positivity)
    exact mul_le_mul this hx₃ h₃ (by positivity)
  have h2 : (L₁ * μ ^ e₁) * (L₂ * μ ^ e₂) * (L₃ * μ ^ e₃) =
      L₁ * L₂ * L₃ * μ ^ (e₁ + e₂ + e₃) := by
    rw [Real.rpow_add hμ0, Real.rpow_add hμ0]
    ring
  have h3 : μ ^ (e₁ + e₂ + e₃) ≤ μ ^ κ := Real.rpow_le_rpow_of_exponent_le hμ he
  calc x₁ * x₂ * x₃ ≤ L₁ * L₂ * L₃ * μ ^ (e₁ + e₂ + e₃) := h1.trans_eq h2
    _ ≤ L₁ * L₂ * L₃ * μ ^ κ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- `β(σ) ≥ 2` on `[0,1)`. -/
lemma two_le_betaOf {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ < 1) : 2 ≤ betaOf σ := by
  unfold betaOf
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **R1 duty of the kinetic roles** (Table quant-fixed): `kinThreshold` has fixed-force degree
`5β − 3/2 < d = 7β − 3` for slow exponents `eA ≤ 2`, `eB ≤ 4`, `eW ≤ 5/2` (`slowExpHA`,
`slowExpEl` and the Fourier-side `eW = 5/2`) and polylog exponents `δ ≤ 1/2`.  The worst monomial is `y (A_S + P_F)(W_S + y)` of
`fourierFloor`, degree `2v + max(eA + δ, β) ≤ 5β − 3/2`. -/
theorem kinetic_degree {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (e : SlowExp) (heA : e.eA ≤ 2)
    (heB : e.eB ≤ 4) (heW : e.eW ≤ 5 / 2) : DegreeBelow σ (dOf σ) e kinThreshold := by
  intro φ hφ
  refine ⟨1 / 2, by norm_num, fun δ K hδ hδ' hK => ?_⟩
  have hβ : 2 ≤ betaOf σ := two_le_betaOf hσ0 hσ1
  set β := betaOf σ with hβdef
  have hv : vOf σ = 2 * β - 1 := rfl
  set L := K * (6 + 4 * φ) with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hc4 := c4_pos
  set Ctot : ℝ := 1 + 4 * φ + 2 ^ 13 + 2 ^ 20 + 2 ^ 9 * φ + 2 ^ 6 * c4 * φ + 64 * (6 + φ) + 9 + 28
    with hCtot
  refine ⟨kinC φ * L ^ 3 * Ctot, 5 * β - 3 / 2, by unfold dOf; linarith,
    fun μ hμ caps hc => ?_⟩
  obtain ⟨⟨-, hPF⟩, ⟨-, hyF⟩, -, hAS, hBS, -, hWS, -, -, -⟩ := hc
  have hμ0 : 0 < μ := by linarith
  have hKL : K ≤ L := by rw [hLdef]; nlinarith
  have hpow : ∀ a b : ℝ, a ≤ b → μ ^ a ≤ μ ^ b := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_le hμ hab
  have hKL' : ∀ a : ℝ, K * μ ^ a ≤ L * μ ^ a := fun a =>
    mul_le_mul_of_nonneg_right hKL (by positivity)
  -- atom bounds
  have hP : cp caps.PF ≤ L * μ ^ β := cp_le (by positivity) (hPF.trans (hKL' _))
  have hY : cp caps.yF ≤ L * μ ^ (2 * β - 1) := by
    rw [← hv]; exact cp_le (by positivity) (hyF.trans (hKL' _))
  have hA : cp caps.AS ≤ L * μ ^ (5 / 2 : ℝ) := cp_le (by positivity) (hAS.trans
    ((mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) (by linarith)).trans (hKL' _)))
  have hB : cp caps.BS ≤ L * μ ^ (9 / 2 : ℝ) := cp_le (by positivity) (hBS.trans
    ((mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) (by linarith)).trans (hKL' _)))
  have hW : cp caps.WS ≤ L * μ ^ (3 : ℝ) := cp_le (by positivity) (hWS.trans
    ((mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) (by linarith)).trans (hKL' _)))
  have hρ0 : 0 ≤ rhoOf μ φ := by unfold rhoOf; linarith
  have hρ1 : 1 ≤ rhoOf μ φ := by unfold rhoOf; linarith
  have hρ : rhoOf μ φ ≤ L * μ ^ (1 : ℝ) := by
    rw [Real.rpow_one, hLdef]
    unfold rhoOf
    nlinarith
  have hone : (1 : ℝ) ≤ L * μ ^ (0 : ℝ) := by rw [Real.rpow_zero, mul_one]; exact hL1
  have hP0 := cp_nonneg caps.PF
  have hY0 := cp_nonneg caps.yF
  have hA0 := cp_nonneg caps.AS
  have hB0 := cp_nonneg caps.BS
  have hW0 := cp_nonneg caps.WS
  -- composite atoms
  have hAP1 : cp caps.AS + cp caps.PF + 1 ≤ 3 * L * μ ^ (β + 1 / 2) := by
    have h1 : cp caps.AS ≤ L * μ ^ (β + 1 / 2) :=
      hA.trans (mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) hL0)
    have h2 : cp caps.PF ≤ L * μ ^ (β + 1 / 2) :=
      hP.trans (mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) hL0)
    have h3 : (1 : ℝ) ≤ L * μ ^ (β + 1 / 2) :=
      hone.trans (mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) hL0)
    linarith
  have hWY1 : cp caps.WS + cp caps.yF + 1 ≤ 3 * L * μ ^ (2 * β - 1) := by
    have h1 : cp caps.WS ≤ L * μ ^ (2 * β - 1) :=
      hW.trans (mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) hL0)
    have h3 : (1 : ℝ) ≤ L * μ ^ (2 * β - 1) :=
      hone.trans (mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) hL0)
    linarith
  have hsqρ : Real.sqrt (rhoOf μ φ) ≤ rhoOf μ φ := by
    rw [Real.sqrt_le_left hρ0, sq]
    exact le_mul_of_one_le_left hρ0 hρ1
  have hsqρB : Real.sqrt (rhoOf μ φ * (cp caps.BS + 1)) ≤ rhoOf μ φ + cp caps.BS + 1 := by
    rw [Real.sqrt_le_left (by positivity), sq]
    have h1 : rhoOf μ φ * (cp caps.BS + 1) ≤ (rhoOf μ φ + cp caps.BS + 1) * (cp caps.BS + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : (rhoOf μ φ + cp caps.BS + 1) * (cp caps.BS + 1) ≤
        (rhoOf μ φ + cp caps.BS + 1) * (rhoOf μ φ + cp caps.BS + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact h1.trans h2
  set κ := 5 * β - 3 / 2 with hκ
  set M := L ^ 3 * μ ^ κ with hM
  have hM0 : 0 ≤ M := by positivity
  have hL3 : L ^ 3 = L * L * L := by ring
  -- one-, two- and three-factor monomials, all `≤ M`
  have m1 : ∀ {x e : ℝ}, x ≤ L * μ ^ e → e ≤ κ → x ≤ M := fun {x e} hxe he => by
    have := prod3_le_rpow (κ := κ) hμ hL0 hL0 hL0 zero_le_one zero_le_one hxe hone hone
      (by linarith)
    rw [mul_one, mul_one] at this
    rw [hM, hL3]; exact this
  have m2 : ∀ {x y e f : ℝ}, 0 ≤ y → x ≤ L * μ ^ e → y ≤ L * μ ^ f → e + f ≤ κ → x * y ≤ M :=
    fun {x y e f} hy hxe hyf hef => by
      have := prod3_le_rpow (κ := κ) hμ hL0 hL0 hL0 hy zero_le_one hxe hyf hone (by linarith)
      rw [mul_one] at this
      rw [hM, hL3]; exact this
  have m3 : ∀ {x y z e f g' : ℝ}, 0 ≤ y → 0 ≤ z → x ≤ L * μ ^ e → y ≤ L * μ ^ f →
      z ≤ L * μ ^ g' → e + f + g' ≤ κ → x * y * z ≤ M :=
    fun {x y z e f g'} hy hz hxe hyf hzg hs => by
      have := prod3_le_rpow (κ := κ) hμ hL0 hL0 hL0 hy hz hxe hyf hzg hs
      rw [hM, hL3]; exact this
  have hκ0 : (0 : ℝ) ≤ κ := by rw [hκ]; linarith
  have h1M : (1 : ℝ) ≤ M := m1 hone hκ0
  -- atoms below `M`
  have hYM : cp caps.yF ≤ M := m1 hY (by rw [hκ]; linarith)
  have hBM : cp caps.BS ≤ M := m1 hB (by rw [hκ]; linarith)
  have hWM : cp caps.WS ≤ M := m1 hW (by rw [hκ]; linarith)
  have hAM : cp caps.AS ≤ M := m1 hA (by rw [hκ]; linarith)
  have hPM : cp caps.PF ≤ M := m1 hP (by rw [hκ]; linarith)
  have hYY : cp caps.yF ^ 2 ≤ M := by rw [sq]; exact m2 hY0 hY hY (by rw [hκ]; linarith)
  -- roles 22–27
  have r22 : role22 ≤ M := h1M
  have r23 : role23 φ ≤ 4 * φ * M := by
    unfold role23
    have := mul_le_mul_of_nonneg_left h1M (by positivity : (0 : ℝ) ≤ 4 * φ)
    linarith
  have r24 : role24 caps ≤ 2 ^ 13 * M := by unfold role24; linarith
  have r25 : role25 caps ≤ 2 ^ 20 * M := by unfold role25; linarith
  have r26 : role26 φ ≤ 2 ^ 9 * φ * M := by
    unfold role26
    have := mul_le_mul_of_nonneg_left h1M (by positivity : (0 : ℝ) ≤ 2 ^ 9 * φ)
    linarith
  have r27 : role27 φ caps ≤ 2 ^ 6 * c4 * φ * M := by
    unfold role27
    have h1 : cp caps.yF + cp caps.BS ≤ 2 * M := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 ^ 5 * c4)
    have h3 := mul_le_mul_of_nonneg_right h2 hφ
    linarith
  -- row 36
  have hBρ : cp caps.BS * rhoOf μ φ ≤ M := m2 hρ0 hB hρ (by rw [hκ]; linarith)
  have hBρρ : cp caps.BS * (rhoOf μ φ * Real.sqrt (rhoOf μ φ)) ≤ M := by
    have h1 : cp caps.BS * (rhoOf μ φ * Real.sqrt (rhoOf μ φ)) ≤
        cp caps.BS * rhoOf μ φ * rhoOf μ φ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqρ hρ0) hB0
    exact h1.trans (m3 hρ0 hρ0 hB hρ hρ (by rw [hκ]; linarith))
  have hBY : cp caps.BS * cp caps.yF ≤ M := m2 hY0 hB hY (by rw [hκ]; linarith)
  have hρA : rhoOf μ φ * cp caps.AS ≤ M := m2 hA0 hρ hA (by rw [hκ]; linarith)
  have hYφ : cp caps.yF * φ ≤ φ * M := by
    have := mul_le_mul_of_nonneg_left hYM hφ
    linarith
  have r36 : role36 μ φ caps ≤ 64 * (6 + φ) * M := by
    have e : role36 μ φ caps = 64 * (cp caps.yF ^ 2 + cp caps.yF * φ + cp caps.yF +
        (cp caps.BS * rhoOf μ φ + cp caps.BS * (rhoOf μ φ * Real.sqrt (rhoOf μ φ)) +
          cp caps.BS * cp caps.yF) + rhoOf μ φ * cp caps.AS) := by
      simp only [role36]
      ring
    rw [e]
    linarith
  -- eq. quant-kinetic-floor
  have hWW : cp caps.WS * cp caps.WS ≤ M := m2 hW0 hW hW (by rw [hκ]; linarith)
  have hWρ : cp caps.WS * rhoOf μ φ ≤ M := m2 hρ0 hW hρ (by rw [hκ]; linarith)
  have hWB : cp caps.WS * cp caps.BS ≤ M := m2 hB0 hW hB (by rw [hκ]; linarith)
  have hWY : cp caps.WS * cp caps.yF ≤ M := m2 hY0 hW hY (by rw [hκ]; linarith)
  have hWA : cp caps.WS * cp caps.AS ≤ M := m2 hA0 hW hA (by rw [hκ]; linarith)
  have hWsq : cp caps.WS * Real.sqrt (rhoOf μ φ * (cp caps.BS + 1)) ≤ 3 * M := by
    have h1 := mul_le_mul_of_nonneg_left hsqρB hW0
    have h2 : cp caps.WS * (rhoOf μ φ + cp caps.BS + 1) =
        cp caps.WS * rhoOf μ φ + cp caps.WS * cp caps.BS + cp caps.WS := by ring
    linarith
  have rKF : kineticFloor μ φ caps ≤ 9 * M := by
    have e : kineticFloor μ φ caps = cp caps.WS * cp caps.WS + cp caps.WS * rhoOf μ φ +
        cp caps.WS * Real.sqrt (rhoOf μ φ * (cp caps.BS + 1)) + cp caps.WS +
        cp caps.WS * cp caps.yF + cp caps.WS * cp caps.AS + cp caps.yF ^ 2 := by
      simp only [kineticFloor]
      ring
    rw [e]
    linarith
  -- the Lean error budget
  have hYAPWY : cp caps.yF * (cp caps.AS + cp caps.PF + 1) * (cp caps.WS + cp caps.yF + 1) ≤
      9 * M := by
    have := prod3_le_rpow hμ hL0 (by positivity : (0 : ℝ) ≤ 3 * L)
      (by positivity : (0 : ℝ) ≤ 3 * L) (by positivity) (by positivity) hY hAP1 hWY1 (κ := κ)
      (by rw [hκ]; linarith)
    rw [hM, hL3]; linarith
  have hWAPWY : cp caps.WS * (cp caps.AS + cp caps.PF + 1) * (cp caps.WS + cp caps.yF + 1) ≤
      9 * M := by
    have := prod3_le_rpow hμ hL0 (by positivity : (0 : ℝ) ≤ 3 * L)
      (by positivity : (0 : ℝ) ≤ 3 * L) (by positivity) (by positivity) hW hAP1 hWY1 (κ := κ)
      (by rw [hκ]; linarith)
    rw [hM, hL3]; linarith
  have rFF : fourierFloor caps ≤ 28 * M := by
    simp only [fourierFloor]
    linarith
  -- sum up
  have hkC : 0 ≤ kinC φ := by unfold kinC; positivity
  have hsum : role22 + role23 φ + role24 caps + role25 caps + role26 φ + role27 φ caps +
      role36 μ φ caps + kineticFloor μ φ caps + fourierFloor caps ≤ Ctot * M := by
    rw [hCtot]
    linarith
  unfold kinThreshold
  calc kinC φ * (role22 + role23 φ + role24 caps + role25 caps + role26 φ + role27 φ caps +
      role36 μ φ caps + kineticFloor μ φ caps + fourierFloor caps)
      ≤ kinC φ * (Ctot * M) := mul_le_mul_of_nonneg_left hsum hkC
    _ = kinC φ * L ^ 3 * Ctot * μ ^ κ := by rw [hM]; ring

/-- The degree lemma for the harmonic-analysis slow exponents `slowExpHA = (3/2, 2, 3, 3/2)`. -/
theorem kinetic_degree_HA {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    DegreeBelow σ (dOf σ) slowExpHA kinThreshold :=
  kinetic_degree hσ0 hσ1 slowExpHA (by norm_num [slowExpHA]) (by norm_num [slowExpHA])
    (by norm_num [slowExpHA])

/-- The degree lemma for the elementary slow exponents `slowExpEl = (2, 4, 4, 2)`. -/
theorem kinetic_degree_el {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    DegreeBelow σ (dOf σ) slowExpEl kinThreshold :=
  kinetic_degree hσ0 hσ1 slowExpEl (by norm_num [slowExpEl]) (by norm_num [slowExpEl])
    (by norm_num [slowExpEl])

end OVNS.Quant

end
