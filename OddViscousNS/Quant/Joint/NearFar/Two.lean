import OddViscousNS.Quant.Joint.NearFar.One

/-!
# The near and far differentials at weight two, at a time

Roles 16, 17, 31; JOINT_ASSEMBLY_V4 §5.  At an `H³` time, with `b = ‖F‖₂`, `c = ‖F‖₃`,
`c_y = ‖y_S‖₃`, `E = 64 c₄ φ/q`, `G = 64 c₄ φ²/q²`, `P' = 2 C_low M + 16 c_I √(ab)`:

* `rest_le`: `‖N_rest‖₂ ≤ (P' + 2E) c + E c_y + G`, by `hnorm_two_fastRest` and
  `c_S ≤ c_y + c/128`;
* `fastNL_le`: `‖N_F‖₂ ≤ (P' + 2E + L) c + (E + 20 L) c_y + G`, by `hnorm_two_fastNL`: the high
  mixed direction is in the FAR, and it is the old partner `q⁻¹ U √P_S` of role 31;
* `alg_nf`: `ν ρ b c ≤ η c² + (1/η)(ν E₂)² c_y² b²`, for `ν` either coefficient.  So the only
  charge outside the dissipation is the multiplier `(1/η)(ν E₂)² c_y²` of `b²`.

The constant term `G` needs no Young step: `b c ≤ c²`.
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.NearFar

open OVNS.Quant.Metric OVNS.Quant.Quartic

variable {μ φ r η KN KP M X L cy : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ} {caps : Caps}

/-- **The algebra of the two differentials.** -/
lemma alg_nf {ν ρ b c cy P₂ E₂ G₂ : ℝ} (hη : 0 < η) (hν : 0 ≤ ν) (hb0 : 0 ≤ b) (hbc : b ≤ c)
    (hρ : ρ ≤ P₂ * c + E₂ * cy + G₂) (h1 : ν * P₂ * b ≤ η / 2) (h2 : ν * G₂ ≤ η / 4) :
    ν * ρ * (b * c) ≤ η * c ^ 2 + 1 / η * (ν * E₂) ^ 2 * cy ^ 2 * b ^ 2 := by
  have hc0 : 0 ≤ c := hb0.trans hbc
  have hbc0 : 0 ≤ b * c := mul_nonneg hb0 hc0
  have t0 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ hν) hbc0
  have t1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg c)
  have t2 := mul_le_mul_of_nonneg_right h2 hbc0
  have t3 : η / 4 * (b * c) ≤ η / 4 * c ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith only [hbc, hc0]
  set x := ν * E₂ * cy * b with hx
  have t4 : x * c ≤ η / 4 * c ^ 2 + 1 / η * x ^ 2 := by
    have h3 : 0 ≤ 1 / η * (η / 2 * c - x) ^ 2 := by positivity
    have e : 1 / η * (η / 2 * c - x) ^ 2 = η / 4 * c ^ 2 + 1 / η * x ^ 2 - x * c := by
      field_simp
      ring
    linarith
  have e1 : ν * (P₂ * c + E₂ * cy + G₂) * (b * c) = ν * P₂ * b * c ^ 2 + x * c +
      ν * G₂ * (b * c) := by
    rw [hx]
    ring
  have e2 : 1 / η * x ^ 2 = 1 / η * (ν * E₂) ^ 2 * cy ^ 2 * b ^ 2 := by
    rw [hx]
    ring
  rw [e1] at t0
  rw [e2] at t4
  nlinarith only [t0, t1, t2, t3, t4]

/-- `E = 64 c₄ φ/q`. -/
def Eq₂ (φ r : ℝ) : ℝ := 64 * c4 * φ / |r|

/-- `G = 64 c₄ φ²/q²`. -/
def Gq₂ (φ r : ℝ) : ℝ := 64 * c4 * φ ^ 2 / r ^ 2

/-- `2 C_low M y + 16 c_I √P y^{3/2}`: the low mixed and the purefast coefficient, weight two. -/
def lead₂ (M : ℝ) (caps : Caps) : ℝ :=
  2 * CLow 2 * (M * cp caps.yF) +
    16 * cI * (Real.sqrt (cp caps.PF) * cp caps.yF ^ ((3 : ℝ) / 2))

lemma lead₂_nonneg (hM : 0 ≤ M) (caps : Caps) : 0 ≤ lead₂ M caps := by
  have h1 := CLow_nonneg 2
  have h2 := cI_pos
  have h3 := cp_nonneg caps.yF
  have h4 : 0 ≤ cp caps.yF ^ ((3 : ℝ) / 2) := Real.rpow_nonneg h3 _
  unfold lead₂
  positivity

lemma Eq_nonneg (h : ActualSol μ φ r g y Ty) : 0 ≤ Eq₂ φ r := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hc := c4_pos
  unfold Eq₂
  positivity

/-- The hypotheses at a time of the weight-two bounds. -/
structure T2 (X φ M cy r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) (caps : Caps) : Prop where
  /-- `F ∈ H³`. -/
  hF3 : InH 3 (Fp r g y u)
  /-- `S ∈ H³`. -/
  hS3 : InH 3 (Sp r g y u)
  /-- The `H¹` cap. -/
  ha : fastNorm 1 r g y u ≤ caps.PF
  /-- The `H²` cap. -/
  hb : fastNorm 2 r g y u ≤ caps.yF
  /-- The sup cap. -/
  hM : slowSup r g y u ≤ M
  /-- `M ≥ 0`. -/
  hM0 : 0 ≤ M
  /-- `c_y ≥ 0`. -/
  hcy : 0 ≤ cy
  /-- `c_S ≤ c_y + c/128`. -/
  hc : slowNorm 3 r g y u ≤ cy + fastNorm 3 r g y u / 128
  /-- The floor. -/
  hfl : Floor X φ |r| caps
  /-- `X ≥ 0`. -/
  hX : 0 ≤ X

section

variable (T : T2 X φ M cy r g y u caps)
include T

lemma T2.r_ne : r ≠ 0 := abs_pos.1 T.hfl.q_pos

lemma T2.b_le_c : hnorm 2 (Fp r g y u) ≤ hnorm 3 (Fp r g y u) :=
  hnorm_mono (by norm_num) T.hF3

/-- `‖N_rest‖₂`. -/
theorem T2.rest_le (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    MZ 2 (fastRest r g y u) ∧ hnorm 2 (fastRest r g y u) ≤
      (2 * CLow 2 * M + 16 * cI * Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) +
        2 * Eq₂ φ r) * hnorm 3 (Fp r g y u) + Eq₂ φ r * cy + Gq₂ φ r := by
  obtain ⟨i, bd⟩ := hnorm_two_fastRest h T.r_ne hu huT T.hF3 T.hS3 T.hM
  refine ⟨⟨i, fastRest_zero h hu huT⟩, bd.trans ?_⟩
  have hE := Eq_nonneg (r := r) h
  have hc0 := hnorm_nonneg 3 (Fp r g y u)
  have hS := T.hc
  have e1 : slowNorm 3 r g y u = hnorm 3 (Sp r g y u) := rfl
  have e2 : fastNorm 3 r g y u = hnorm 3 (Fp r g y u) := rfl
  rw [e1, e2] at hS
  have h1 : hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u) ≤ 2 * hnorm 3 (Fp r g y u) + cy := by
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hE
  change _ + Eq₂ φ r * (hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) + Gq₂ φ r ≤ _
  nlinarith only [h2]

/-- `‖N_F‖₂`, with the fibre norm `L` of `F`. -/
theorem T2.fastNL_le (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty)
    (hL : LhB (nrm (Fp r g y u)) L) (hL0 : 0 ≤ L) :
    MZ 2 (fastNL r g y u) ∧ hnorm 2 (fastNL r g y u) ≤
      (2 * CLow 2 * M + 16 * cI * Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) +
        2 * Eq₂ φ r + L) * hnorm 3 (Fp r g y u) + (Eq₂ φ r + 20 * L) * cy + Gq₂ φ r := by
  obtain ⟨⟨iR, -⟩, bR⟩ := T.rest_le h hu huT
  obtain ⟨i, bd⟩ := hnorm_two_fastNL h hu huT iR T.hS3 hL
  refine ⟨⟨i, fastNL_zero u⟩, bd.trans ?_⟩
  have hc0 := hnorm_nonneg 3 (Fp r g y u)
  have hS := T.hc
  have e1 : slowNorm 3 r g y u = hnorm 3 (Sp r g y u) := rfl
  have e2 : fastNorm 3 r g y u = hnorm 3 (Fp r g y u) := rfl
  rw [e1, e2] at hS
  have h1 := mul_le_mul_of_nonneg_right hS hL0
  have h2 : L * hnorm 3 (Fp r g y u) / 128 * 20 ≤ L * hnorm 3 (Fp r g y u) := by
    have : 0 ≤ L * hnorm 3 (Fp r g y u) := mul_nonneg hL0 hc0
    linarith
  nlinarith only [bR, h1, h2]

/-- `P' b ≤ lead₂`, `2 E b ≤ 1/32`. -/
lemma T2.lead_le (h : ActualSol μ φ r g y Ty) :
    (2 * CLow 2 * M + 16 * cI * Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) +
        2 * Eq₂ φ r) * hnorm 2 (Fp r g y u) ≤ lead₂ M caps + 1 / 32 := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have ha0 := hnorm_nonneg 1 (Fp r g y u)
  have hb0 := hnorm_nonneg 2 (Fp r g y u)
  have ha' : hnorm 1 (Fp r g y u) ≤ cp caps.PF := T.ha.trans (le_cp _)
  have hb' : hnorm 2 (Fp r g y u) ≤ cp caps.yF := T.hb.trans (le_cp _)
  have hroot := sqrt_mul_le_leading ha0 hb0 ha' hb'
  have hCL := CLow_nonneg 2
  have hcI := cI_pos
  have hE := Eq_nonneg (r := r) h
  have hM0 := T.hM0
  have t1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb' hM0)
    (by positivity : 0 ≤ 2 * CLow 2)
  have t2 := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 16 * cI)
  have t3 : Eq₂ φ r * hnorm 2 (Fp r g y u) ≤ 1 / 64 :=
    (mul_le_mul_of_nonneg_left hb' hE).trans (T.hfl.Eq_y_le T.hX hφ)
  unfold lead₂
  nlinarith only [t1, t2, t3]

/-- **The near differential in the direction `N_rest`, weight two.** -/
theorem T2.near_le (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty)
    (hη : 0 < η) (hK : kN / η ≤ KN) (hS : Shares KN KP M |r| caps) :
    |nearD 2 (-1) r (r * u) (Fp r g y u) (fastRest r g y u)| ≤
      η * fastNorm 3 r g y u ^ 2 + 1 / η * (nearC₀ * nearN |r| * Eq₂ φ r) ^ 2 * cy ^ 2 *
        fastNorm 2 r g y u ^ 2 := by
  have hF := Fp_adm h hu huT
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hF3m : MZ 3 (Fp r g y u) := ⟨T.hF3, hF.mean⟩
  obtain ⟨hm, bρ⟩ := T.rest_le h hu huT
  have h1 := nearD2_le (Or.inr rfl) r (r * u) hF3m hF.real (PiF_Fp r g y u) hm
    (isReal_fastRest h hu huT)
  have hN0 := nearN_nonneg |r|
  have hC0 := nearC₀_pos
  have hCL1 := CLow_nonneg 1
  have hCL2 := CLow_nonneg 2
  have hcQ := cQone_nonneg
  have hcI := cI_pos
  have hKpos : 0 < KN := lt_of_lt_of_le (div_pos kN_pos hη) hK
  have hlead := T.lead_le h
  have hs := share_sum (K := KN) (η := η / 2) (c := kN / 2) (a₁ := nearC₀ * (2 * CLow 2))
    (a₂ := nearC₀ * (16 * cI)) (a₃ := nearC₀ * (1 / 32)) hKpos (by positivity) hS.low hS.pure
    hS.flr (by positivity) (by positivity) (by positivity)
    (by unfold kN; nlinarith only [hC0, hCL1, hCL2, hcQ, hcI])
    (by rw [show kN / 2 / (η / 2) = kN / η by field_simp]; exact hK)
  have hb2 : nearC₀ * nearN |r| * (2 * CLow 2 * M + 16 * cI *
      Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) + 2 * Eq₂ φ r) *
      hnorm 2 (Fp r g y u) ≤ η / 2 := by
    have t := mul_le_mul_of_nonneg_left hlead (by positivity : 0 ≤ nearC₀ * nearN |r|)
    unfold lead₂ at t
    nlinarith only [t, hs]
  have hG : nearC₀ * nearN |r| * Gq₂ φ r ≤ η / 4 := by
    have t1 : nearC₀ * nearN |r| ≤ η := share_one hη hK
      (by unfold kN; nlinarith only [hC0, hCL1, hCL2, hcQ, hcI]) hN0 hS.flr
    have t2 : Gq₂ φ r ≤ 1 / 64 := T.hfl.Gq_le T.hX hφ
    have t3 := mul_le_mul_of_nonneg_left t2 (by positivity : 0 ≤ nearC₀ * nearN |r|)
    nlinarith only [t1, t3, hη]
  exact h1.trans (alg_nf hη (by positivity) (hnorm_nonneg _ _) T.b_le_c bρ hb2 hG)

/-- **The native FAR in the full direction `N_F`, weight two.** -/
theorem T2.far_le (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty)
    (hη : 0 < η) (hL : LhB (nrm (Fp r g y u)) L) (hL0 : 0 ≤ L)
    (hq : 2 * H2.cFar / η * (lead₂ M caps + 1 + L * cp caps.yF) ≤ |r|) :
    |farD 2 (-1) r (r * u) (Fp r g y u) (fastNL r g y u)| ≤
      η * fastNorm 3 r g y u ^ 2 + 1 / η * (H2.cFar / |r| * (Eq₂ φ r + 20 * L)) ^ 2 * cy ^ 2 *
        fastNorm 2 r g y u ^ 2 := by
  have hF := Fp_adm h hu huT
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hF3m : MZ 3 (Fp r g y u) := ⟨T.hF3, hF.mean⟩
  obtain ⟨hm, bρ⟩ := T.fastNL_le h hu huT hL hL0
  have h1 := H2.farD_two_le (Or.inr rfl) T.r_ne (r * u) hF3m hm
  have hq0 := T.hfl.q_pos
  have hc := c4_pos
  have hcF : 0 < H2.cFar := by
    unfold H2.cFar
    positivity
  have hν : 0 ≤ H2.cFar / |r| := by positivity
  have hlead0 := lead₂_nonneg T.hM0 caps
  have hy := cp_nonneg caps.yF
  have hLy : 0 ≤ L * cp caps.yF := mul_nonneg hL0 hy
  have hq' : 2 * H2.cFar * (lead₂ M caps + 1 + L * cp caps.yF) ≤ η * |r| := by
    have e : 2 * H2.cFar / η * (lead₂ M caps + 1 + L * cp caps.yF) =
        2 * H2.cFar * (lead₂ M caps + 1 + L * cp caps.yF) / η := by ring
    rw [e, div_le_iff₀ hη] at hq
    linarith
  have hνb : H2.cFar / |r| * (lead₂ M caps + 1 + L * cp caps.yF) ≤ η / 2 := by
    have e : H2.cFar / |r| * (lead₂ M caps + 1 + L * cp caps.yF) =
        H2.cFar * (lead₂ M caps + 1 + L * cp caps.yF) / |r| := by ring
    rw [e, div_le_iff₀ hq0]
    linarith
  have hlead := T.lead_le h
  have hb' : hnorm 2 (Fp r g y u) ≤ cp caps.yF := T.hb.trans (le_cp _)
  have hb2 : H2.cFar / |r| * (2 * CLow 2 * M + 16 * cI *
      Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) + 2 * Eq₂ φ r + L) *
      hnorm 2 (Fp r g y u) ≤ η / 2 := by
    have t1 := mul_le_mul_of_nonneg_left hb' hL0
    have t2 : (2 * CLow 2 * M + 16 * cI *
        Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) + 2 * Eq₂ φ r + L) *
        hnorm 2 (Fp r g y u) ≤ lead₂ M caps + 1 + L * cp caps.yF := by
      nlinarith only [t1, hlead]
    have t3 := mul_le_mul_of_nonneg_left t2 hν
    nlinarith only [t3, hνb]
  have hG : H2.cFar / |r| * Gq₂ φ r ≤ η / 4 := by
    have t2 : Gq₂ φ r ≤ 1 / 64 := T.hfl.Gq_le T.hX hφ
    have t3 := mul_le_mul_of_nonneg_left t2 hν
    have t4 : H2.cFar / |r| ≤ H2.cFar / |r| * (lead₂ M caps + 1 + L * cp caps.yF) := by
      have : 0 ≤ H2.cFar / |r| * (lead₂ M caps + L * cp caps.yF) := by positivity
      nlinarith only [this]
    nlinarith only [t3, t4, hνb, hη]
  exact h1.trans (alg_nf hη hν (hnorm_nonneg _ _) T.b_le_c bρ hb2 hG)

end

/-- `q^{−1/2} w ≤ 1` from `w² ≤ q`. -/
lemma rpow_half_mul_le {q w : ℝ} (hq : 0 < q) (h : w ^ 2 ≤ q) : q ^ (-(1 / 2) : ℝ) * w ≤ 1 := by
  rw [Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow]
  have h1 : w ≤ Real.sqrt q := Real.le_sqrt_of_sq_le h
  have h2 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  rw [inv_mul_le_iff₀ h2]
  linarith

/-- **The coefficient of the proper terms at weight two**: the proper profile and FAR `q^{−1/2}`. -/
lemma heat_coef_le {b : ℝ} (hη : 0 < η) (hr : 1 ≤ |r|) (hK : kP / η ≤ KP)
    (hb : b ≤ cp caps.yF) (hS : Shares KN KP M |r| caps)
    (hq : (2 * H2.cHeat2 * cp caps.yF / η) ^ 2 ≤ |r|) :
    H2.cHeat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) * b ≤ η := by
  have hq0 : 0 < |r| := by linarith
  have hH := H2.cHeat2_pos
  have hP0 : 0 ≤ nearP |r| := nearP_nonneg hq0.le
  have hy := cp_nonneg caps.yF
  have hz : 0 ≤ |r| ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hq0.le _
  have h1 : kP * (nearP |r| * cp caps.yF) ≤ η :=
    share_one hη hK le_rfl (mul_nonneg hP0 hy) hS.stat
  have h2 := rpow_half_mul_le hq0 hq
  have h3 : |r| ^ (-(1 / 2) : ℝ) * (2 * H2.cHeat2 * cp caps.yF) ≤ η := by
    have e : |r| ^ (-(1 / 2) : ℝ) * (2 * H2.cHeat2 * cp caps.yF / η) * η =
        |r| ^ (-(1 / 2) : ℝ) * (2 * H2.cHeat2 * cp caps.yF) := by
      field_simp
    have := mul_le_mul_of_nonneg_right h2 hη.le
    rw [e] at this
    linarith
  have h4 := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ H2.cHeat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)))
  have e : kP = 2 * H2.cHeat2 := rfl
  rw [e] at h1
  nlinarith only [h1, h3, h4]

/-- **The static remainder at weight two.** -/
theorem static_two_le (h : ActualSol μ φ r g y Ty) (hr : 1 ≤ |r|) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hη : 0 < η) (hK : kP / η ≤ KP)
    (hb : fastNorm 2 r g y u ≤ caps.yF) (hS : Shares KN KP M |r| caps)
    (hq : (2 * H2.cHeat2 * cp caps.yF / η) ^ 2 ≤ |r|) :
    |cubicE 2 (-1) r (r * u) (Fp r g y u)| ≤ η * fastNorm 2 r g y u ^ 2 := by
  have hF := Fp_adm h hu huT
  have h1 := H2.cubicE_two_static_le hr (r * u) hF.mz hF.real (PiF_Fp r g y u)
  have e0 : fastNorm 2 r g y u = hnorm 2 (Fp r g y u) := rfl
  have hb' : hnorm 2 (Fp r g y u) ≤ cp caps.yF := hb.trans (le_cp _)
  have hb0 := hnorm_nonneg 2 (Fp r g y u)
  rw [e0]
  have h2 := heat_coef_le hη hr hK hb' hS hq
  have hq0 : 0 < |r| := by linarith
  have hP0 : 0 ≤ nearP |r| := nearP_nonneg hq0.le
  have hz : 0 ≤ |r| ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hq0.le _
  have hc4 := c4_pos
  have h3 : H2.cStat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) * hnorm 2 (Fp r g y u) ≤
      H2.cHeat2 * (nearP |r| + |r| ^ (-(1 / 2) : ℝ)) * hnorm 2 (Fp r g y u) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hb0
    unfold H2.cStat2 H2.cHeat2
    nlinarith only [hc4]
  have h4 := mul_le_mul_of_nonneg_right (h3.trans h2) (sq_nonneg (hnorm 2 (Fp r g y u)))
  nlinarith only [h1, h4]

/-- **Both input heats at weight two.** -/
theorem heat_two_le (h : ActualSol μ φ r g y Ty) (hr : 1 ≤ |r|) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hη : 0 < η) (hK : kP / η ≤ KP)
    (hF3 : InH 3 (Fp r g y u)) (hb : fastNorm 2 r g y u ≤ caps.yF)
    (hS : Shares KN KP M |r| caps) (hq : (2 * H2.cHeat2 * cp caps.yF / η) ^ 2 ≤ |r|) :
    |H2.cubicHeat2 r (r * u) (Fp r g y u)| ≤ η * fastNorm 3 r g y u ^ 2 := by
  have hF := Fp_adm h hu huT
  have hF3m : MZ 3 (Fp r g y u) := ⟨hF3, hF.mean⟩
  have h1 := H2.cubicHeat2_le hr (r * u) hF3m hF.real (PiF_Fp r g y u)
  have e0 : fastNorm 3 r g y u = hnorm 3 (Fp r g y u) := rfl
  have hb' : hnorm 2 (Fp r g y u) ≤ cp caps.yF := hb.trans (le_cp _)
  have hb0 := hnorm_nonneg 2 (Fp r g y u)
  rw [e0]
  have h2 := heat_coef_le hη hr hK hb' hS hq
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (hnorm 3 (Fp r g y u)))
  nlinarith only [h1, h4]

end OVNS.Quant.NearFar

end
