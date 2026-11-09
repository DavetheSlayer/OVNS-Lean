import OddViscousNS.Quant.Energy.Interfaces

/-!
# Regimes layer, node 1: algebra and degree bookkeeping (all proved)

Pure algebra of the fixed-force regimes layer (`OddViscousNS_data/reports/t12_energy_spec.md`
§2.2 E10, §3.1–3.2; `t12_regimes_decomposition.md` node 1):
* E10 damping (TeX eq. quant-virtual): `virtual_damping`;
* the degree identities `β, v, d` (`two_le_betaOf`, `betaOf_le_betaOf`, `dOf_eq`, `half_dOf`,
  `dOf_pos`, `degree_at_281`, `dOf_281`);
* the small-`δ` arithmetic behind the `+ε` (`div_one_sub_le`, `scaling_exponent_le`);
* the R1 threshold arithmetic: a `DegreeBelow σ d` threshold is `≤ C μ^d`
  (`DegreeBelow.exists_le_rpow`, monotone in `d`: `DegreeBelow.mono`), hence paid by
  `q ≥ C (1+μ)^{d+ε}` (`rpow_le_one_add_rpow`), and `NearProfiles` pays the leading role-15/31
  condition `K √P_F y^{3/2} N(q) ≤ 1` at `q ≥ C μ^{d+ε}` for every `d ≥ dOf σ`
  (`NearProfiles.leading_paid`, `NearProfiles.leading_paid'`).
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS.Quant

/-! ### E10: virtual damping (TeX eq. quant-virtual) -/

/-- **E10, virtual damping** (TeX eq. quant-virtual; spec §2.2 E10).  Above the barrier
`W > W_*`, with the interpolation `c_F ≥ b_F²/A`, `b_F ≥ b_*`, and the coercivity `W ≤ u b_F²`
(`u = 33/32`), the quadratic `−2d₀ c_F² + 2B b_F c_F` is at most `−λ_*(W − W_*)`.  (The TeX
hypotheses `B ≤ d₀ b_*/A = v_* B` and `W > W_*` are not needed: the first is automatic for
`v_* ≥ 1`, `B ≥ 0`, and the inequality holds for every `W ≤ u b_F²`.) -/
theorem virtual_damping {vStar A B W bF cF : ℝ} (hv : 1 ≤ vStar) (hA : 0 < A) (hB : 0 ≤ B)
    (hWu : W ≤ 33 / 32 * bF ^ 2) (hc : bF ^ 2 / A ≤ cF) (hb : bStar vStar A B ≤ bF) :
    -2 * dZero * cF ^ 2 + 2 * B * bF * cF ≤ -lamStar vStar A B * (W - WStar vStar A B) := by
  obtain ⟨b, hb_eq⟩ : ∃ b, b = bStar vStar A B := ⟨_, rfl⟩
  rw [← hb_eq] at hb
  have hb0 : 0 ≤ b := by
    rw [hb_eq]
    unfold bStar dZero
    positivity
  have hbF0 : 0 ≤ bF := hb0.trans hb
  have hAB : A * B ≤ 2 / 3 * b := by
    have e : 2 / 3 * b = vStar * A * B := by
      rw [hb_eq]
      unfold bStar dZero
      ring
    rw [e]
    nlinarith [mul_nonneg hA.le hB]
  have hcA : bF ^ 2 ≤ A * cF := by
    have := (div_le_iff₀ hA).1 hc
    linarith
  have hcF0 : 0 ≤ cF := le_trans (div_nonneg (sq_nonneg _) hA.le) hc
  -- Step 1: the quadratic in `c_F` decreases on the eligible half-line `c_F ≥ b_F²/A`.
  have h1 : A ^ 2 * (-2 * dZero * cF ^ 2 + 2 * B * bF * cF) ≤
      -(4 / 3) * bF ^ 4 + 2 * A * B * bF ^ 3 := by
    unfold dZero
    have h2 : 2 * A * B * bF ≤ 4 / 3 * (A * cF + bF ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hAB hbF0, hcA, mul_nonneg hb0 hbF0]
    nlinarith [mul_nonneg (sub_nonneg.2 hcA) (sub_nonneg.2 h2)]
  -- Step 2: `2AB ≤ (4/3) b_*`.
  have h3 : 2 * A * B * bF ^ 3 ≤ 4 / 3 * b * bF ^ 3 := by
    have := mul_le_mul_of_nonneg_right hAB (pow_nonneg hbF0 3)
    linarith
  -- Step 3: the tangent bound `2 b_F³ ≥ b_*² (b_F + b_*)`.
  have h4 : b ^ 2 * (bF + b) ≤ 2 * bF ^ 3 := by
    nlinarith [mul_nonneg hb0 hbF0, mul_nonneg (mul_nonneg hb0 hb0) (sub_nonneg.2 hb),
      mul_nonneg (mul_nonneg hbF0 hbF0) (sub_nonneg.2 hb)]
  have hlam : lamStar vStar A B = 2 / 3 * b ^ 2 / (33 / 32 * A ^ 2) := by
    rw [hb_eq]
    unfold lamStar dZero
    ring
  have hWs : WStar vStar A B = 33 / 32 * b ^ 2 := by
    rw [hb_eq]
    unfold WStar
    ring
  rw [hlam, hWs]
  have hA2 : 0 < 33 / 32 * A ^ 2 := by positivity
  rw [show -(2 / 3 * b ^ 2 / (33 / 32 * A ^ 2)) * (W - 33 / 32 * b ^ 2) =
      (-(2 / 3) * b ^ 2 * (W - 33 / 32 * b ^ 2)) / (33 / 32 * A ^ 2) by ring,
    le_div_iff₀ hA2]
  unfold dZero at h1 ⊢
  nlinarith [h1, h3, mul_nonneg (sub_nonneg.2 hb) (sub_nonneg.2 h4),
    mul_le_mul_of_nonneg_left hWu (sq_nonneg b)]

/-! ### Degree identities (spec §3.1) -/

/-- `β ≥ 2` on `[0, 1)`. -/
theorem two_le_betaOf {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ < 1) : 2 ≤ betaOf σ := by
  unfold betaOf
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `β` is monotone on `[0, 1)`. -/
theorem betaOf_le_betaOf {σ σ' : ℝ} (hle : σ ≤ σ') (h1 : σ' < 1) :
    betaOf σ ≤ betaOf σ' := by
  unfold betaOf
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `d = β + 3v`. -/
theorem dOf_eq (σ : ℝ) : dOf σ = betaOf σ + 3 * vOf σ := by
  unfold dOf vOf
  ring

/-- The leading cap monomial `√P_F y^{3/2}` has degree `β/2 + 3v/2 = d/2`. -/
theorem half_dOf (σ : ℝ) : betaOf σ / 2 + 3 * vOf σ / 2 = dOf σ / 2 := by
  unfold dOf vOf
  ring

/-- `v ≥ 3` on `[0, 1)`. -/
theorem three_le_vOf {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ < 1) : 3 ≤ vOf σ := by
  unfold vOf
  linarith [two_le_betaOf h0 h1]

/-- `d > 0` on `[0, 1)` (in fact `d ≥ 11`). -/
theorem dOf_pos {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ < 1) : 0 < dOf σ := by
  unfold dOf
  linarith [two_le_betaOf h0 h1]

/-- The degree at `σ = 281/1000`: `7β − 3 = 7 · 1719/719 − 3 = 9876/719` (spec §3.1). -/
theorem degree_at_281 :
    7 * ((2 - (281 : ℝ) / 1000) / (1 - 281 / 1000)) - 3 = 9876 / 719 := by
  norm_num

/-- `dOf (281/1000) = 9876/719`. -/
theorem dOf_281 : dOf ((281 : ℝ) / 1000) = 9876 / 719 := by
  unfold dOf betaOf
  exact degree_at_281

/-! ### The small-`δ` arithmetic behind the `+ε` (spec §3.1: `+ε` absorbs the subpower) -/

/-- `δ ≤ ε/(2(d+ε))` gives `d/(1 − 2δ) ≤ d + ε`. -/
theorem div_one_sub_le {d ε δ : ℝ} (hd : 0 < d) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ' : δ ≤ ε / (2 * (d + ε))) : d / (1 - 2 * δ) ≤ d + ε := by
  have hδε : δ * (2 * (d + ε)) ≤ ε := (le_div_iff₀ (by positivity)).1 hδ'
  have h2δ : 2 * δ < 1 := by
    by_contra h
    push Not at h
    have h1 : ε ≤ 2 * δ * ε := le_mul_of_one_le_left hε.le h
    nlinarith [mul_pos hδ hd]
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- Equivalently `(d + ε)(1/2 − δ) ≥ d/2`: the cap monomial `μ^{d/2}` is paid by `q^{1/2−δ}` at
`q ≥ μ^{d+ε}`. -/
theorem scaling_exponent_le {d ε δ : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hδ' : δ ≤ ε / (2 * (d + ε))) : d / 2 ≤ (d + ε) * (1 / 2 - δ) := by
  have hδε : δ * (2 * (d + ε)) ≤ ε := (le_div_iff₀ (by positivity)).1 hδ'
  nlinarith

/-! ### R1 threshold arithmetic (spec §2.1 caveat, §3.2) -/

/-- Monotonicity of the degree bound in `d` (amendment D2). -/
theorem DegreeBelow.mono {σ d d' : ℝ} {e : SlowExp} {q : ℝ → ℝ → Caps → ℝ}
    (hq : DegreeBelow σ d e q) (hdd : d ≤ d') : DegreeBelow σ d' e q := by
  intro φ hφ
  obtain ⟨δ₀, hδ₀, h⟩ := hq φ hφ
  refine ⟨δ₀, hδ₀, fun δ K hδ hδδ hK => ?_⟩
  obtain ⟨C, κ, hκ, hC⟩ := h δ K hδ hδδ hK
  exact ⟨C, κ, lt_of_lt_of_le hκ hdd, hC⟩

/-- A `DegreeBelow σ d` threshold is `≤ C μ^d` on scaled caps, with `C ≥ 0`. -/
theorem DegreeBelow.exists_le_rpow {σ d : ℝ} {e : SlowExp} {q : ℝ → ℝ → Caps → ℝ}
    (hq : DegreeBelow σ d e q) {φ : ℝ} (hφ : 0 ≤ φ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ K : ℝ, 0 < δ → δ ≤ δ₀ → 1 ≤ K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ μ : ℝ, 1 ≤ μ → ∀ caps : Caps, CapsScaled σ δ K μ e caps → q μ φ caps ≤ C * μ ^ d := by
  obtain ⟨δ₀, hδ₀, h⟩ := hq φ hφ
  refine ⟨δ₀, hδ₀, fun δ K hδ hδδ hK => ?_⟩
  obtain ⟨C, κ, hκ, hC⟩ := h δ K hδ hδδ hK
  refine ⟨max C 0, le_max_right _ _, fun μ hμ caps hcaps => ?_⟩
  calc q μ φ caps ≤ C * μ ^ κ := hC μ hμ caps hcaps
    _ ≤ max C 0 * μ ^ κ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * μ ^ d :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hμ hκ.le) (le_max_right _ _)

/-- `C μ^d ≤ C (1 + μ)^{d+ε}`: the threshold `C (1+μ)^{d+ε} ≤ q` pays every `≤ C μ^d` price. -/
theorem rpow_le_one_add_rpow {C μ d ε : ℝ} (hC : 0 ≤ C) (hμ : 1 ≤ μ) (hd : 0 ≤ d) (hε : 0 ≤ ε) :
    C * μ ^ d ≤ C * (1 + μ) ^ (d + ε) := by
  apply mul_le_mul_of_nonneg_left _ hC
  calc μ ^ d ≤ (1 + μ) ^ d := Real.rpow_le_rpow (by linarith) (by linarith) hd
    _ ≤ (1 + μ) ^ (d + ε) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- **The leading pair (roles 15, 31) is paid at degree `d + ε`** (spec §0.1, §3.1): with
`N(q) ≤ C_δ q^{−1/2+δ}` and the cap scaling `√P_F y^{3/2} ≤ K² μ^{d/2}`, for `δ ≤ ε/(2(d+ε))`
there is `C ≥ 1` such that `q ≥ C μ^{d+ε}` gives `K₁ √P_F y^{3/2} N(q) ≤ 1`. -/
theorem NearProfiles.leading_paid {N P : ℝ → ℝ} (hN : NearProfiles N P) {σ K₁ K ε : ℝ}
    (e : SlowExp) (hσ : 0 ≤ σ ∧ σ < 1) (hK₁ : 0 ≤ K₁) (hK : 1 ≤ K) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ C : ℝ, 1 ≤ C ∧
      ∀ μ : ℝ, 1 ≤ μ → ∀ caps : Caps, CapsScaled σ δ K μ e caps → ∀ q : ℝ,
        C * μ ^ (dOf σ + ε) ≤ q → K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * N q ≤ 1 := by
  have hd0 : 0 < dOf σ := dOf_pos hσ.1 hσ.2
  refine ⟨ε / (2 * (dOf σ + ε)), by positivity, fun δ hδ hδ' => ?_⟩
  obtain ⟨C₀, hC₀⟩ := hN δ hδ
  have ha : 0 < 1 / 2 - δ := by
    have hδε : δ * (2 * (dOf σ + ε)) ≤ ε := (le_div_iff₀ (by positivity)).1 hδ'
    by_contra h
    push Not at h
    have h1 : ε ≤ 2 * δ * ε := le_mul_of_one_le_left hε.le (by linarith)
    nlinarith [mul_pos hδ hd0]
  have hexp := scaling_exponent_le hd0 hε hδ'
  set C' : ℝ := max C₀ 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set a : ℝ := 1 / 2 - δ with ha_def
  set C : ℝ := max 1 ((K₁ * K ^ 2 * C') ^ (1 / a)) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := by linarith
  refine ⟨C, hC1, fun μ hμ caps hcaps q hq => ?_⟩
  have hμ0 : 0 < μ := by linarith
  have hK0 : 0 < K := by linarith
  obtain ⟨⟨hPFlo, hPFhi⟩, ⟨hyFlo, hyFhi⟩, -, -, -, -, -⟩ := hcaps
  have hPF0 : 0 ≤ caps.PF := le_trans (by positivity) hPFlo
  have hyF0 : 0 ≤ caps.yF := le_trans (by positivity) hyFlo
  have hμd : 1 ≤ μ ^ (dOf σ + ε) := Real.one_le_rpow hμ (by linarith)
  have hq1 : 1 ≤ q := le_trans (one_le_mul_of_one_le_of_one_le hC1 hμd) hq
  have hqpos : 0 < q := by linarith
  -- the native profile at `q`
  have hNq : N q ≤ C' * q ^ (-a) := by
    have h := (hC₀ q hq1).1
    have e : (-1 / 2 + δ : ℝ) = -a := by
      rw [ha_def]
      ring
    rw [e] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hqpos.le _))
  -- the cap monomial `√P_F y^{3/2} ≤ K² μ^{d/2}`
  have hsqrt : Real.sqrt caps.PF ≤ K ^ (1 / 2 : ℝ) * μ ^ (betaOf σ / 2) := by
    calc Real.sqrt caps.PF ≤ Real.sqrt (K * μ ^ betaOf σ) := Real.sqrt_le_sqrt hPFhi
      _ = K ^ (1 / 2 : ℝ) * μ ^ (betaOf σ / 2) := by
        rw [Real.sqrt_eq_rpow, Real.mul_rpow hK0.le (Real.rpow_nonneg hμ0.le _),
          ← Real.rpow_mul hμ0.le]
        congr 2
        ring
  have hyF : caps.yF ^ (3 / 2 : ℝ) ≤ K ^ (3 / 2 : ℝ) * μ ^ (3 * vOf σ / 2) := by
    calc caps.yF ^ (3 / 2 : ℝ) ≤ (K * μ ^ vOf σ) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow hyF0 hyFhi (by norm_num)
      _ = K ^ (3 / 2 : ℝ) * μ ^ (3 * vOf σ / 2) := by
        rw [Real.mul_rpow hK0.le (Real.rpow_nonneg hμ0.le _), ← Real.rpow_mul hμ0.le]
        congr 2
        ring
  have hmono : Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) ≤ K ^ 2 * μ ^ (dOf σ / 2) := by
    calc Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ)
        ≤ (K ^ (1 / 2 : ℝ) * μ ^ (betaOf σ / 2)) * (K ^ (3 / 2 : ℝ) * μ ^ (3 * vOf σ / 2)) :=
          mul_le_mul hsqrt hyF (Real.rpow_nonneg hyF0 _)
            (mul_nonneg (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg hμ0.le _))
      _ = (K ^ (1 / 2 : ℝ) * K ^ (3 / 2 : ℝ)) * (μ ^ (betaOf σ / 2) * μ ^ (3 * vOf σ / 2)) := by
          ring
      _ = K ^ 2 * μ ^ (dOf σ / 2) := by
          rw [← Real.rpow_add hK0, ← Real.rpow_add hμ0, half_dOf,
            show (1 / 2 + 3 / 2 : ℝ) = 2 by norm_num, Real.rpow_two]
  -- `q^{-a} ≤ (C μ^{d+ε})^{-a} = C^{-a} μ^{-(d+ε)a}`
  have hbase : 0 < C * μ ^ (dOf σ + ε) := mul_pos hCpos (Real.rpow_pos_of_pos hμ0 _)
  have hqa : q ^ (-a) ≤ (C * μ ^ (dOf σ + ε)) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos hbase hq (by linarith)
  have hsplit : (C * μ ^ (dOf σ + ε)) ^ (-a) = C ^ (-a) * μ ^ (-((dOf σ + ε) * a)) := by
    rw [Real.mul_rpow hCpos.le (Real.rpow_nonneg hμ0.le _), ← Real.rpow_mul hμ0.le]
    congr 2
    ring
  -- the constants: `K₁ K² C' C^{-a} ≤ 1`
  have hpos0 : 0 ≤ K₁ * K ^ 2 * C' := mul_nonneg (mul_nonneg hK₁ (sq_nonneg K)) hC'0
  have hCa : K₁ * K ^ 2 * C' ≤ C ^ a := by
    have h1 : (K₁ * K ^ 2 * C') ^ (1 / a) ≤ C := le_max_right _ _
    calc K₁ * K ^ 2 * C' = ((K₁ * K ^ 2 * C') ^ (1 / a)) ^ a := by
          rw [one_div, Real.rpow_inv_rpow hpos0 ha.ne']
      _ ≤ C ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hpos0 _) h1 ha.le
  have hCa' : K₁ * K ^ 2 * C' * C ^ (-a) ≤ 1 := by
    rw [Real.rpow_neg hCpos.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hCpos a)]
    exact hCa
  -- the powers of `μ`: `μ^{d/2} μ^{-(d+ε)a} ≤ 1`
  have hμle : μ ^ (dOf σ / 2) * μ ^ (-((dOf σ + ε) * a)) ≤ 1 := by
    rw [← Real.rpow_add hμ0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hμ (by linarith)
  -- assemble
  have hpre0 : 0 ≤ K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg hK₁ (Real.sqrt_nonneg _)) (Real.rpow_nonneg hyF0 _)
  have hq' : C' * q ^ (-a) ≤ C' * (C ^ (-a) * μ ^ (-((dOf σ + ε) * a))) := by
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_left hqa hC'0
  have hm : K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) ≤ K₁ * (K ^ 2 * μ ^ (dOf σ / 2)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmono hK₁
  calc K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * N q
      ≤ K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * (C' * q ^ (-a)) :=
        mul_le_mul_of_nonneg_left hNq hpre0
    _ ≤ K₁ * (K ^ 2 * μ ^ (dOf σ / 2)) * (C' * (C ^ (-a) * μ ^ (-((dOf σ + ε) * a)))) :=
        mul_le_mul hm hq' (mul_nonneg hC'0 (Real.rpow_nonneg hqpos.le _))
          (mul_nonneg hK₁ (mul_nonneg (sq_nonneg K) (Real.rpow_nonneg hμ0.le _)))
    _ = (K₁ * K ^ 2 * C' * C ^ (-a)) * (μ ^ (dOf σ / 2) * μ ^ (-((dOf σ + ε) * a))) := by ring
    _ ≤ 1 * 1 := mul_le_mul hCa' hμle
        (mul_nonneg (Real.rpow_nonneg hμ0.le _) (Real.rpow_nonneg hμ0.le _)) zero_le_one
    _ = 1 := by ring

/-- The leading pair at any degree `d ≥ dOf σ` (amendment D2): `q ≥ C μ^{d+ε}` also pays it. -/
theorem NearProfiles.leading_paid' {N P : ℝ → ℝ} (hN : NearProfiles N P) {σ K₁ K ε d : ℝ}
    (e : SlowExp) (hσ : 0 ≤ σ ∧ σ < 1) (hK₁ : 0 ≤ K₁) (hK : 1 ≤ K) (hε : 0 < ε)
    (hd : dOf σ ≤ d) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ C : ℝ, 1 ≤ C ∧
      ∀ μ : ℝ, 1 ≤ μ → ∀ caps : Caps, CapsScaled σ δ K μ e caps → ∀ q : ℝ,
        C * μ ^ (d + ε) ≤ q → K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * N q ≤ 1 := by
  obtain ⟨δ₀, hδ₀, h⟩ := hN.leading_paid e hσ hK₁ hK hε (K := K)
  refine ⟨δ₀, hδ₀, fun δ hδ hδ' => ?_⟩
  obtain ⟨C, hC1, hC⟩ := h δ hδ hδ'
  refine ⟨C, hC1, fun μ hμ caps hcaps q hq => hC μ hμ caps hcaps q (le_trans ?_ hq)⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hμ (by linarith))
    (by linarith)

end OVNS.Quant
