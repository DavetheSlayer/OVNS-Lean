import OddViscousNS.Quant.Energy.Slow.Barrier

/-!
# E7-F: the slow-cap interface (assembly)

`slowCapsInterface`: there are a piece length `Tp = 2` and a role threshold `qS` with
`SlowCapsInterface 2 slowExpF qS` and `DegreeBelow (281/1000) (9876/719) slowExpF qS`, the
Fourier-side route E7-F (`t12_slow_fourier_route.md`) with exponents
`slowExpF = (eA, eB, eJ, eW) = (2, 3, 4, 5/2)`.

## The threshold
`qS μ φ caps = 1 + 32 c₄ Y² + resPoly φ caps + budgetPoly φ caps` (`Y = cp caps.yF`; the
slow-correction roles 18–21): it pays `‖R_S‖₂ ≤ 8c₄ b_F²/q ≤ 1/4` (role 25-like, `Y²`), the
pointwise `H⁰` residual `‖corrRes‖₀ ≤ φ + resPoly/q ≤ φ + 1` and the `L²_t H¹` residual budget
`∫ ‖corrRes‖₁² ≤ 4φ² + 4` (`budgetPoly ≤ q`).  Degree (`slow_degree`): every monomial has
fixed-force degree `≤ 2 + 3v + δ`, the worst being the slack monomial
`(A_S y + W_S P_F)(y + (W_S + y)(B_S + y))` of `budgetPoly` (the monomials the proof of
`corrRes_budget` actually pays have degree `≤ 3v`), i.e. `≤ 2 + 3v + 1/8 < d = β + 3v`
at `σ = 281/1000` (`β − 2 = 281/719 > 1/8`).

## The levels (`t12_slow_fourier_route.md` §2.2, chosen triangularly)
With `q = 1 + φ` (`Φ = φ + 1` the pointwise residual size): `L₀ = L₁ = 16 q` (contraction of
`‖y_S‖₀`, `a_h` by `e^{−1} ≤ 3/8` after one unit); `a_h ≤ 18 q μ`, `∫ ‖y_S‖₁² ≤ 292 q² μ²` on the
piece; window averaging gives `a_ζ² ≲ μ⁴` with the regained level `L₃`; the `h`-barrier
`450 A_h⁴` gives `L₂`, the `ζ`-barrier `max(452 A_h² A_ζ², 6 B_h² A_ζ²/A_h²)` gives `L₄`.  The
piece-wide constant `C` collects the pointwise caps, the Wiener cap
`W_S ≤ c_I √(a_S b_S) + c₄/4 ≲ μ^{5/2}` (`exists_wiener_interp`) and the budget `∫ b_S² ≲ μ⁴`.
Transfer `S ↔ y_S` costs `‖R_S‖₂ ≤ 1/4` on every norm (`slowNorm_le_corr`, `horizNorm_le_corr`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace OVNS.Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### The threshold -/

/-- **The slow-correction role threshold** `qS(μ, φ, caps)`:
`1 + 32c₄ Y² + resPoly + budgetPoly` (roles 18–21 and the corrector size). -/
def qS (_μ φ : ℝ) (caps : Caps) : ℝ :=
  1 + 32 * c4 * cp caps.yF ^ 2 + resPoly φ caps + budgetPoly φ caps

lemma one_le_qS {μ φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) : 1 ≤ qS μ φ caps := by
  have h1 := resPoly_nonneg hφ caps
  have h2 := one_le_budgetPoly hφ caps
  have h3 := cp_nonneg caps.yF
  have h4 := c4_pos
  unfold qS
  nlinarith [mul_nonneg h4.le (sq_nonneg (cp caps.yF))]

/-- The threshold pays the corrector size, the pointwise residual and the residual budget. -/
theorem slow_small (h : ActualSol μ φ r g y Ty) (hφ : 0 ≤ φ) {caps : Caps} {s t : ℝ}
    (hP : PieceHyp 2 (qS μ φ) r g y Ty caps s t) :
    1 ≤ |r| ∧ (∀ u ∈ Icc s t, hnorm 2 (slowCorr r g y u) ≤ 1 / 4) ∧
      (∀ u ∈ Icc s t, hnorm 0 (corrRes r g y u) ≤ φ + 1) ∧
      (∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 4 * φ ^ 2 + 4 := by
  have hq := hP.thr
  have h1 : 1 ≤ |r| := (one_le_qS hφ caps).trans hq
  have hr : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at h1; linarith
  have hrpos : 0 < |r| := by linarith
  have hY := cp_nonneg caps.yF
  have hc4 := c4_pos
  have hres := resPoly_nonneg hφ caps
  have hbud := one_le_budgetPoly hφ caps
  have hq' : 32 * c4 * cp caps.yF ^ 2 ≤ |r| := by unfold qS at hq; linarith
  have hq'' : resPoly φ caps ≤ |r| := by unfold qS at hq; nlinarith
  have hq''' : budgetPoly φ caps ≤ |r| := by unfold qS at hq; nlinarith
  have hρ : ∀ u ∈ Icc s t, hnorm 2 (slowCorr r g y u) ≤ 1 / 4 := by
    intro u hu
    have hu0 : 0 ≤ u := hP.hs.trans hu.1
    have huT := lt_lifespan hu.2 hP.ht
    have hb := (hnorm_slowCorr_le h hr hu0 huT).2
    have hbF : fastNorm 2 r g y u ≤ cp caps.yF := (hP.onPrefix.1 u hu).2.1.trans (le_cp _)
    have hbF0 := hnorm_nonneg 2 (PiF (actual r g y u))
    have hsq : fastNorm 2 r g y u ^ 2 ≤ cp caps.yF ^ 2 := pow_le_pow_left₀ hbF0 hbF 2
    calc hnorm 2 (slowCorr r g y u) ≤ 8 * c4 / |r| * fastNorm 2 r g y u ^ 2 := hb
      _ ≤ 8 * c4 / |r| * cp caps.yF ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ 1 / 4 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hrpos]
          linarith
  refine ⟨h1, hρ, fun u hu => ?_, ?_⟩
  · have := hnorm_corrRes_le h h1 hP.hs hP.ht hP.onPrefix hu ((hρ u hu).trans (by norm_num))
    have h2 : resPoly φ caps / |r| ≤ 1 := by
      rw [div_le_one hrpos]; exact hq''
    linarith
  · exact corrRes_budget h hP.hs hP.hst hP.ht hP.len hq''' hP.onPrefix

/-! ### Arithmetic helpers -/

lemma exp_neg_one_le : Real.exp (-1) ≤ 3 / 8 :=
  (Real.exp_neg_one_lt_d9).le.trans (by norm_num)

/-- The contraction step: `x² ≤ e^{−1}(16q+1)²μ² + q²` gives `x + 1/4 ≤ 16 q μ`
(`q ≥ 1`, `μ ≥ 1`). -/
lemma regain_arith {x μ q : ℝ} (hx : 0 ≤ x) (hμ : 1 ≤ μ) (hq : 1 ≤ q)
    (h : x ^ 2 ≤ Real.exp (-1) * (16 * q + 1) ^ 2 * μ ^ 2 + q ^ 2) : x + 1 / 4 ≤ 16 * q * μ := by
  have he := exp_neg_one_le
  have he0 := (Real.exp_pos (-1)).le
  have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ
  have h1 : Real.exp (-1) * (16 * q + 1) ^ 2 * μ ^ 2 ≤ 3 / 8 * (16 * q + 1) ^ 2 * μ ^ 2 := by
    have := mul_le_mul_of_nonneg_right he (by positivity : (0 : ℝ) ≤ (16 * q + 1) ^ 2 * μ ^ 2)
    linarith [this]
  have h2 : (x + 1 / 4) ^ 2 ≤ (16 * q * μ) ^ 2 := by
    nlinarith [sq_nonneg (x - 1 / 4), mul_le_mul_of_nonneg_left hμ2 (sq_nonneg q)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h2

/-- `x² ≤ A m²` gives `x ≤ √A m`. -/
lemma le_sqrt_mul {x A m : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hm : 0 ≤ m) (h : x ^ 2 ≤ A * m ^ 2) :
    x ≤ Real.sqrt A * m := by
  have : x ^ 2 ≤ (Real.sqrt A * m) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hA]; exact h
  exact (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).1 this

/-- `x² ≤ A m²` with `m ≥ 1` gives `x + 1/4 ≤ √(2A + 1) m`. -/
lemma add_quarter_le_sqrt {x A m : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hm : 1 ≤ m)
    (h : x ^ 2 ≤ A * m ^ 2) : x + 1 / 4 ≤ Real.sqrt (2 * A + 1) * m := by
  refine le_sqrt_mul (by positivity) (by positivity) (by linarith) ?_
  have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm
  nlinarith [sq_nonneg (x - 1 / 4)]

lemma rpow_three (μ : ℝ) : μ ^ (3 : ℝ) = μ ^ 3 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma rpow_four (μ : ℝ) : μ ^ (4 : ℝ) = μ ^ 4 := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma rpow_five_half {μ : ℝ} (hμ : 0 ≤ μ) : μ ^ (5 / 2 : ℝ) = Real.sqrt (μ ^ 5) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hμ]
  norm_num

/-- `SlowLevel` at the Fourier-side exponents, with natural powers. -/
lemma slowLevel_F_iff (L : Fin 5 → ℝ) (μ r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    SlowLevel L μ slowExpF r g y u ↔
      slowNorm 0 r g y u ≤ L 0 * μ ∧ horizNorm 1 r g y u ≤ L 1 * μ ∧
        horizNorm 2 r g y u ≤ L 2 * μ ^ 2 ∧ slowNorm 1 r g y u ≤ L 3 * μ ^ 2 ∧
        slowNorm 2 r g y u ≤ L 4 * μ ^ 3 := by
  simp only [SlowLevel, slowExpF, Real.rpow_two, rpow_three]

/-! ### The levels -/

/-- `L₀ = L₁ = 16(1 + φ)`. -/
def L01 (φ : ℝ) : ℝ := 16 * (1 + φ)

/-- The piece-wide bound of `a_h` (and of `‖y_S‖₀`): `18(1 + φ) μ`. -/
def cA (φ : ℝ) : ℝ := 18 * (1 + φ)

/-- The dissipation budgets `∫ ‖y_S‖₁²`, `∫ b_h² ≤ 292 (1 + φ)² μ²`. -/
def slowCI (φ : ℝ) : ℝ := 292 * (1 + φ) ^ 2

/-- The residual budget `E₂ = 4φ² + 4 ≤ 4(1 + φ)²`. -/
def E2 (φ : ℝ) : ℝ := 4 * (1 + φ) ^ 2

/-- The regained `a_ζ²/μ⁴` (window averaging): `(1 + 25 A_h²) I + 2Φ²·2`. -/
def cZ' (φ : ℝ) : ℝ := slowCI φ + 25 * cA φ ^ 2 * slowCI φ + 4 * (1 + φ) ^ 2

/-- `L₃`: the regained slow `H¹` level. -/
def L3c (φ : ℝ) : ℝ := Real.sqrt (2 * (cA φ ^ 2 + cZ' φ) + 1)

/-- The piece-wide `a_ζ²/μ⁴`. -/
def cZeta (φ : ℝ) : ℝ := (L3c φ + 1) ^ 2 + 25 * cA φ ^ 2 * slowCI φ + 4 * (1 + φ) ^ 2

/-- The regained `b_h²/μ⁴` (the `h`-barrier from the good time of the first unit, where
`b_h² ≤ ∫ b_h² ≤ slowCI μ²`). -/
def cB' (φ : ℝ) : ℝ := slowCI φ + 450 * cA φ ^ 4 + 2 * E2 φ

/-- `L₂`: the regained horizontal `H²` level. -/
def L2c (φ : ℝ) : ℝ := Real.sqrt (2 * cB' φ + 1)

/-- The piece-wide `b_h²/μ⁴`. -/
def cB (φ : ℝ) : ℝ := (L2c φ + 1) ^ 2 + 450 * cA φ ^ 4 + 2 * E2 φ

/-- The `ζ`-barrier level `Z_*/μ⁶`. -/
def cZ (φ : ℝ) : ℝ := 452 * cA φ ^ 2 * cZeta φ + 6 * cB φ * cZeta φ

/-- The regained `b_ζ²/μ⁶`. -/
def cBz' (φ : ℝ) : ℝ := 2 * cZeta φ + cZ φ + 4 * E2 φ

/-- `L₄`: the regained slow `H²` level. -/
def L4c (φ : ℝ) : ℝ := Real.sqrt (2 * (cB' φ + cBz' φ) + 1)

/-- The piece-wide `b_ζ²/μ⁶`. -/
def cBz (φ : ℝ) : ℝ := (L4c φ + 1) ^ 2 + cZ φ + 4 * E2 φ

/-- The budget `∫ b_S²/μ⁴`: `2(∫ b_h² + ∫ b_ζ²) + (t−s)/8 ≤ (2 slowCI + 4 cZeta + 1) μ⁴`. -/
def cJ (φ : ℝ) : ℝ := 2 * slowCI φ + 4 * cZeta φ + 1

/-- The start levels `L = (L₀, L₁, L₂, L₃, L₄)`. -/
def Lvec (φ : ℝ) : Fin 5 → ℝ := ![L01 φ, L01 φ, L2c φ, L3c φ, L4c φ]

/-- The piece-wide constant `C` (pointwise caps, Wiener cap with the interpolation constant
`cW`, and the `∫ b_S²` budget). -/
def Cfin (φ cW : ℝ) : ℝ :=
  (cA φ + 1) + (cA φ + 1) + (Real.sqrt (cB φ) + 1) + (Real.sqrt (cA φ ^ 2 + cZeta φ) + 1) +
    (Real.sqrt (cB φ + cBz φ) + 1) +
    (cW * Real.sqrt (Real.sqrt (cA φ ^ 2 + cZeta φ) * Real.sqrt (cB φ + cBz φ)) + c4) + cJ φ

section constants

variable (hφ : 0 ≤ φ)
include hφ

lemma one_le_q : 1 ≤ 1 + φ := by linarith
lemma L01_nonneg : 0 ≤ L01 φ := by unfold L01; linarith
lemma one_le_L01 : 1 ≤ L01 φ := by unfold L01; linarith
lemma cA_nonneg : 0 ≤ cA φ := by unfold cA; linarith
lemma one_le_cA : 1 ≤ cA φ := by unfold cA; linarith
lemma slowCI_nonneg : 0 ≤ slowCI φ := by unfold slowCI; positivity
lemma E2_nonneg : 0 ≤ E2 φ := by unfold E2; positivity
lemma budget_le_E2 : 4 * φ ^ 2 + 4 ≤ E2 φ := by unfold E2; nlinarith
lemma cZ'_nonneg : 0 ≤ cZ' φ := by
  have := slowCI_nonneg hφ; have := cA_nonneg hφ; unfold cZ'; positivity
lemma one_le_L3c : 1 ≤ L3c φ := by
  unfold L3c
  have := cZ'_nonneg hφ
  have := cA_nonneg hφ
  rw [Real.one_le_sqrt]; nlinarith [sq_nonneg (cA φ)]
lemma cZeta_nonneg : 0 ≤ cZeta φ := by
  have := slowCI_nonneg hφ; have := cA_nonneg hφ; unfold cZeta; positivity
lemma cB'_nonneg : 0 ≤ cB' φ := by
  have := cA_nonneg hφ; have := E2_nonneg hφ; have := slowCI_nonneg hφ; unfold cB'; positivity
lemma one_le_L2c : 1 ≤ L2c φ := by
  unfold L2c
  have := cB'_nonneg hφ
  rw [Real.one_le_sqrt]; linarith
lemma cB_nonneg : 0 ≤ cB φ := by
  have := cA_nonneg hφ; have := E2_nonneg hφ; unfold cB; positivity
lemma cZ_nonneg : 0 ≤ cZ φ := by
  have := cA_nonneg hφ; have := cZeta_nonneg hφ; have := cB_nonneg hφ; unfold cZ; positivity
lemma cBz'_nonneg : 0 ≤ cBz' φ := by
  have := cZeta_nonneg hφ; have := cZ_nonneg hφ; have := E2_nonneg hφ; unfold cBz'; positivity
lemma one_le_L4c : 1 ≤ L4c φ := by
  unfold L4c
  have := cB'_nonneg hφ; have := cBz'_nonneg hφ
  rw [Real.one_le_sqrt]; linarith
lemma cBz_nonneg : 0 ≤ cBz φ := by
  have := cZ_nonneg hφ; have := E2_nonneg hφ; unfold cBz; positivity
lemma cJ_nonneg : 0 ≤ cJ φ := by
  have := cZeta_nonneg hφ; have := slowCI_nonneg hφ; unfold cJ; positivity

lemma one_le_Lvec : ∀ i, 1 ≤ Lvec φ i := by
  intro i
  fin_cases i
  · exact one_le_L01 hφ
  · exact one_le_L01 hφ
  · exact one_le_L2c hφ
  · exact one_le_L3c hφ
  · exact one_le_L4c hφ

end constants

/-! ### The chain: the `σ ≤ 1` laws -/

/-- The contraction arithmetic of F0/F1 on the piece: from `X(s) ≤ (16q+1)μ` and
`X(u)² ≤ e^{−(u−s)} X(s)² + q²`, `X ≤ 18 q μ` on the piece and `X + 1/4 ≤ 16 q μ` after one
unit. -/
lemma contraction_step {X : ℝ → ℝ} {s t μ φ : ℝ} (hμ : 1 ≤ μ) (hφ : 0 ≤ φ)
    (hX0 : ∀ u, 0 ≤ X u) (hXs : X s ≤ (L01 φ + 1) * μ)
    (hXd : ∀ u ∈ Icc s t, X u ^ 2 ≤ Real.exp (-(u - s)) * X s ^ 2 + (φ + 1) ^ 2) :
    (∀ u ∈ Icc s t, X u ≤ cA φ * μ) ∧ (∀ u ∈ Icc (s + 1) t, X u + 1 / 4 ≤ L01 φ * μ) := by
  have hq : 1 ≤ 1 + φ := by linarith
  have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ
  have hXs2 : X s ^ 2 ≤ ((16 * (1 + φ) + 1) * μ) ^ 2 := by
    have := pow_le_pow_left₀ (hX0 s) hXs 2
    unfold L01 at this
    exact this
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have hd := hXd u hu
    have he : Real.exp (-(u - s)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hu.1])
    have h1 : Real.exp (-(u - s)) * X s ^ 2 ≤ ((16 * (1 + φ) + 1) * μ) ^ 2 := by
      calc Real.exp (-(u - s)) * X s ^ 2 ≤ 1 * X s ^ 2 :=
            mul_le_mul_of_nonneg_right he (sq_nonneg _)
        _ ≤ ((16 * (1 + φ) + 1) * μ) ^ 2 := by rw [one_mul]; exact hXs2
    have h68 : 0 ≤ 68 * (1 + φ) ^ 2 - 32 * (1 + φ) - 1 := by nlinarith
    have hb : X u ^ 2 ≤ (cA φ * μ) ^ 2 := by
      unfold cA
      nlinarith [mul_le_mul_of_nonneg_left hμ2 h68,
        mul_le_mul_of_nonneg_left hμ2 (sq_nonneg (1 + φ))]
    exact (pow_le_pow_iff_left₀ (hX0 u) (by have := cA_nonneg hφ; positivity) two_ne_zero).1 hb
  · have hu' : u ∈ Icc s t := ⟨by linarith [hu.1], hu.2⟩
    have hd := hXd u hu'
    have he : Real.exp (-(u - s)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith [hu.1])
    have h1 : Real.exp (-(u - s)) * X s ^ 2 ≤ Real.exp (-1) * ((16 * (1 + φ) + 1) * μ) ^ 2 :=
      mul_le_mul he hXs2 (sq_nonneg _) (Real.exp_pos _).le
    have hb : X u ^ 2 ≤ Real.exp (-1) * (16 * (1 + φ) + 1) ^ 2 * μ ^ 2 + (1 + φ) ^ 2 := by
      have e : Real.exp (-1) * ((16 * (1 + φ) + 1) * μ) ^ 2 =
          Real.exp (-1) * (16 * (1 + φ) + 1) ^ 2 * μ ^ 2 := by ring
      have e2 : (φ + 1) ^ 2 = (1 + φ) ^ 2 := by ring
      rw [e] at h1
      rw [e2] at hd
      linarith
    have := regain_arith (hX0 u) hμ hq hb
    unfold L01
    linarith

/-- The dissipation budget constant: `(L₀+1)² μ² + 2(φ+1)² ≤ slowCI μ²`. -/
lemma cI_bound (hφ : 0 ≤ φ) (hμ : 1 ≤ μ) :
    (L01 φ + 1) ^ 2 * μ ^ 2 + (φ + 1) ^ 2 * 2 ≤ slowCI φ * μ ^ 2 := by
  have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ
  have hq : 1 ≤ 1 + φ := by linarith
  have h36 : 0 ≤ 36 * (1 + φ) ^ 2 - 32 * (1 + φ) - 1 := by nlinarith
  have h34 : 0 ≤ 34 * (1 + φ) ^ 2 - 32 * (1 + φ) - 1 := by nlinarith
  have := mul_nonneg h36 (by linarith : (0 : ℝ) ≤ μ ^ 2 - 1)
  unfold L01 slowCI
  nlinarith

/-- `a_h² ≤ cA² μ² ≤ cA² μ⁴`-type monotonicity in `μ`. -/
lemma mu_pow_mono {μ : ℝ} (hμ : 1 ≤ μ) {m n : ℕ} (hmn : m ≤ n) : μ ^ m ≤ μ ^ n :=
  pow_le_pow_right₀ hμ hmn

set_option maxHeartbeats 1000000 in
/-- **The `σ ≤ 1` part of the chain** (F0–F2) along the corrected field, from the start levels of
`S`: piece-wide bounds `‖y_S‖₀, a_h ≤ 18(1+φ)μ`, `a_ζ² ≤ cZeta μ⁴`, the dissipation budgets, and
the regained bounds after one unit. -/
theorem chain_low (hφ : 0 ≤ φ) (hμ : 1 ≤ μ) (h : ActualSol μ φ r g y Ty) (hr : 1 ≤ |r|)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 2)
    (hρ : ∀ u ∈ Icc s t, hnorm 2 (slowCorr r g y u) ≤ 1 / 4)
    (hres : ∀ u ∈ Icc s t, hnorm 0 (corrRes r g y u) ≤ φ + 1)
    (h0 : slowNorm 0 r g y s ≤ L01 φ * μ) (h1 : horizNorm 1 r g y s ≤ L01 φ * μ)
    (h3 : slowNorm 1 r g y s ≤ L3c φ * μ ^ 2) :
    (∀ u ∈ Icc s t, hnorm 0 (corrSlow r g y u) ≤ cA φ * μ) ∧
    (∀ u ∈ Icc (s + 1) t, hnorm 0 (corrSlow r g y u) + 1 / 4 ≤ L01 φ * μ) ∧
    (∀ u ∈ Icc s t, hnorm 1 (PiH (corrSlow r g y u)) ≤ cA φ * μ) ∧
    (∀ u ∈ Icc (s + 1) t, hnorm 1 (PiH (corrSlow r g y u)) + 1 / 4 ≤ L01 φ * μ) ∧
    (∫ u in s..t, hnorm 2 (PiH (corrSlow r g y u)) ^ 2) ≤ slowCI φ * μ ^ 2 ∧
    (s + 1 ≤ t → (∫ u in s..(s + 1), hnorm 2 (PiH (corrSlow r g y u)) ^ 2) ≤ slowCI φ * μ ^ 2) ∧
    (∀ u ∈ Icc s t, hnorm 1 (PiV (corrSlow r g y u)) ^ 2 ≤ cZeta φ * μ ^ 4) ∧
    (∀ u ∈ Icc (s + 1) t, hnorm 1 (PiV (corrSlow r g y u)) ^ 2 ≤ cZ' φ * μ ^ 4) ∧
    (∫ u in s..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2) ≤ 2 * cZeta φ * μ ^ 4 := by
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr; linarith
  have hμ0 : 0 ≤ μ := by linarith
  have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ
  have hμ4 : μ ^ 2 ≤ μ ^ 4 := mu_pow_mono hμ (by norm_num)
  have hμ4' : (1 : ℝ) ≤ μ ^ 4 := hμ2.trans hμ4
  have hsT := lt_lifespan hst ht
  have hρs := hρ s ⟨le_rfl, hst⟩
  have hcI := cI_bound hφ hμ
  have hcI0 := slowCI_nonneg hφ
  -- start values of the corrected field
  have hz0 : hnorm 0 (corrSlow r g y s) ≤ (L01 φ + 1) * μ := by
    have := (slowNorm_le_corr h hr0 hs hsT (by norm_num : (0 : ℝ) ≤ 2)).2
    have e : (L01 φ + 1) * μ = L01 φ * μ + μ := by ring
    rw [e]; linarith
  have hh0 : hnorm 1 (PiH (corrSlow r g y s)) ≤ (L01 φ + 1) * μ := by
    have := (horizNorm_le_corr h hr0 hs hsT (by norm_num : (1 : ℝ) ≤ 2)).2
    have e : (L01 φ + 1) * μ = L01 φ * μ + μ := by ring
    rw [e]; linarith
  have hζ0 : hnorm 1 (PiV (corrSlow r g y s)) ≤ (L3c φ + 1) * μ ^ 2 := by
    have hz := (corrSlow_adm h hr0 hs hsT).inH.mono (by norm_num : (1 : ℝ) ≤ 2)
    have h1' := hnorm_PiV_le' hz
    have := (slowNorm_le_corr h hr0 hs hsT (by norm_num : (1 : ℝ) ≤ 2)).2
    have e : (L3c φ + 1) * μ ^ 2 = L3c φ * μ ^ 2 + μ ^ 2 := by ring
    rw [e]; linarith
  -- F0, F1
  obtain ⟨hdec0, hI0⟩ := corr_l2_bounds h hr0 hs hst ht hres
  obtain ⟨hdec1, hI1⟩ := corr_horiz_bounds h hr0 hs hst ht hres
  obtain ⟨hE, hEr⟩ := contraction_step (X := fun u => hnorm 0 (corrSlow r g y u)) hμ hφ
    (fun u => hnorm_nonneg 0 _) hz0 hdec0
  obtain ⟨hA, hAr⟩ := contraction_step (X := fun u => hnorm 1 (PiH (corrSlow r g y u))) hμ hφ
    (fun u => hnorm_nonneg 1 _) hh0 hdec1
  -- the dissipation budgets
  have hz0sq : hnorm 0 (corrSlow r g y s) ^ 2 ≤ (L01 φ + 1) ^ 2 * μ ^ 2 := by
    have := pow_le_pow_left₀ (hnorm_nonneg _ _) hz0 2
    rw [mul_pow] at this; exact this
  have hh0sq : hnorm 1 (PiH (corrSlow r g y s)) ^ 2 ≤ (L01 φ + 1) ^ 2 * μ ^ 2 := by
    have := pow_le_pow_left₀ (hnorm_nonneg _ _) hh0 2
    rw [mul_pow] at this; exact this
  have hlen2 : (φ + 1) ^ 2 * (t - s) ≤ (φ + 1) ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hlen (sq_nonneg _)
  have hI0' : (∫ u in s..t, hnorm 1 (corrSlow r g y u) ^ 2) ≤ slowCI φ * μ ^ 2 := by linarith
  have hI1' : (∫ u in s..t, hnorm 2 (PiH (corrSlow r g y u)) ^ 2) ≤ slowCI φ * μ ^ 2 := by linarith
  have hI1w : s + 1 ≤ t →
      (∫ u in s..(s + 1), hnorm 2 (PiH (corrSlow r g y u)) ^ 2) ≤ slowCI φ * μ ^ 2 := by
    intro hs1
    have hw := (corr_horiz_bounds h hr0 hs (by linarith) (lt_lifespan hs1 ht)
      fun u hu => hres u ⟨hu.1, hu.2.trans hs1⟩).2
    simp only [add_sub_cancel_left, mul_one] at hw
    have : (φ + 1) ^ 2 ≤ (φ + 1) ^ 2 * 2 := by nlinarith [sq_nonneg (φ + 1)]
    linarith
  -- F2 with `A_h = cA μ`, `I = slowCI μ²`
  obtain ⟨hζ, hζr, hJζ⟩ := corr_vert_bounds h hr0 hs hst ht (Ah := cA φ * μ) (I := slowCI φ * μ ^ 2)
    hres hA hI0'
  have hlen' : 2 * (φ + 1) ^ 2 * (t - s) ≤ 4 * (1 + φ) ^ 2 * μ ^ 4 := by
    have h1' := mul_le_mul_of_nonneg_left hlen (by positivity : (0 : ℝ) ≤ 2 * (φ + 1) ^ 2)
    have h2' := mul_le_mul_of_nonneg_left hμ4' (by positivity : (0 : ℝ) ≤ 4 * (1 + φ) ^ 2)
    have e : (φ + 1) ^ 2 = (1 + φ) ^ 2 := by ring
    rw [e] at h1'
    linarith
  have hmid : 25 * (cA φ * μ) ^ 2 * (slowCI φ * μ ^ 2) = 25 * cA φ ^ 2 * slowCI φ * μ ^ 4 := by ring
  have hζs2 : hnorm 1 (PiV (corrSlow r g y s)) ^ 2 ≤ (L3c φ + 1) ^ 2 * μ ^ 4 := by
    have := pow_le_pow_left₀ (hnorm_nonneg _ _) hζ0 2
    rw [mul_pow, ← pow_mul] at this
    norm_num at this
    exact this
  have hcIμ : slowCI φ * μ ^ 2 ≤ slowCI φ * μ ^ 4 := mul_le_mul_of_nonneg_left hμ4 hcI0
  have eζ : cZeta φ * μ ^ 4 = (L3c φ + 1) ^ 2 * μ ^ 4 + 25 * cA φ ^ 2 * slowCI φ * μ ^ 4 +
      4 * (1 + φ) ^ 2 * μ ^ 4 := by unfold cZeta; ring
  have eζ' : cZ' φ * μ ^ 4 = slowCI φ * μ ^ 4 + 25 * cA φ ^ 2 * slowCI φ * μ ^ 4 +
      4 * (1 + φ) ^ 2 * μ ^ 4 := by unfold cZ'; ring
  refine ⟨hE, hEr, hA, hAr, hI1', hI1w, fun u hu => ?_, fun u hu => ?_, ?_⟩
  · have := hζ u hu
    rw [hmid] at this
    rw [eζ]
    linarith
  · have := hζr u hu
    rw [hmid] at this
    rw [eζ']
    linarith
  · rw [hmid] at hJζ
    have e : 2 * cZeta φ * μ ^ 4 = 2 * (cZeta φ * μ ^ 4) := by ring
    rw [e, eζ]
    linarith

/-! ### The chain: the `σ = 2` barriers -/

/-- The `ζ`-barrier level: `max(452 A_h² A_ζ², 6 B_h² A_ζ²/A_h²) ≤ cZ μ⁶` with `A_h = cA μ`,
`A_ζ = √cZeta μ²`, `B_h = √cB μ²`. -/
lemma zeta_level_le (hφ : 0 ≤ φ) (hμ : 1 ≤ μ) :
    max (452 * (cA φ * μ) ^ 2 * (Real.sqrt (cZeta φ) * μ ^ 2) ^ 2)
      (6 * (Real.sqrt (cB φ) * μ ^ 2) ^ 2 * (Real.sqrt (cZeta φ) * μ ^ 2) ^ 2 / (cA φ * μ) ^ 2) ≤
      cZ φ * μ ^ 6 := by
  have hμ0 : 0 ≤ μ := by linarith
  have hcA := one_le_cA hφ
  have hcB := cB_nonneg hφ
  have hcZeta := cZeta_nonneg hφ
  have hcAμ : 0 < cA φ * μ := by positivity
  have e1 : 452 * (cA φ * μ) ^ 2 * (Real.sqrt (cZeta φ) * μ ^ 2) ^ 2 =
      452 * cA φ ^ 2 * cZeta φ * μ ^ 6 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hcZeta]; ring
  have hnum : 6 * (Real.sqrt (cB φ) * μ ^ 2) ^ 2 * (Real.sqrt (cZeta φ) * μ ^ 2) ^ 2 =
      6 * cB φ * cZeta φ * μ ^ 6 * μ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hcB, Real.sq_sqrt hcZeta]; ring
  have hc : μ ^ 2 ≤ (cA φ * μ) ^ 2 := by
    rw [mul_pow]
    have := one_le_pow₀ (n := 2) hcA
    have := sq_nonneg μ
    nlinarith
  have e2 : 6 * (Real.sqrt (cB φ) * μ ^ 2) ^ 2 * (Real.sqrt (cZeta φ) * μ ^ 2) ^ 2 /
      (cA φ * μ) ^ 2 ≤ 6 * cB φ * cZeta φ * μ ^ 6 := by
    rw [hnum, div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have e3 : cZ φ * μ ^ 6 = 452 * cA φ ^ 2 * cZeta φ * μ ^ 6 + 6 * cB φ * cZeta φ * μ ^ 6 := by
    unfold cZ; ring
  have n1 : 0 ≤ 452 * cA φ ^ 2 * cZeta φ * μ ^ 6 := by positivity
  have n2 : 0 ≤ 6 * cB φ * cZeta φ * μ ^ 6 := by positivity
  rw [e1, e3]
  exact max_le (by linarith) (by linarith)

lemma cB_pos (hφ : 0 ≤ φ) : 0 < cB φ := by
  unfold cB
  have := one_le_L2c hφ
  have := cA_nonneg hφ
  have := E2_nonneg hφ
  nlinarith [pow_nonneg (cA_nonneg hφ) 4]

lemma cZeta_pos (hφ : 0 ≤ φ) : 0 < cZeta φ := by
  unfold cZeta
  have := one_le_L3c hφ
  have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 25) (sq_nonneg (cA φ))) (slowCI_nonneg hφ)
  nlinarith [sq_nonneg (1 + φ)]

/-- **The `σ = 2` part of the chain** (F3–F4): piece-wide `b_h² ≤ cB μ⁴`, `b_ζ² ≤ cBz μ⁶` and
the regained `b_h² ≤ cB' μ⁴`, `b_ζ² ≤ cBz' μ⁶` after one unit. -/
theorem chain_high (hφ : 0 ≤ φ) (hμ : 1 ≤ μ) (h : ActualSol μ φ r g y Ty) (hr : 1 ≤ |r|)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty)
    (hρ : ∀ u ∈ Icc s t, hnorm 2 (slowCorr r g y u) ≤ 1 / 4)
    (hE : (∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 4 * φ ^ 2 + 4)
    (hA : ∀ u ∈ Icc s t, hnorm 1 (PiH (corrSlow r g y u)) ≤ cA φ * μ)
    (hI1w : s + 1 ≤ t → (∫ u in s..(s + 1), hnorm 2 (PiH (corrSlow r g y u)) ^ 2) ≤ slowCI φ * μ ^ 2)
    (hζ : ∀ u ∈ Icc s t, hnorm 1 (PiV (corrSlow r g y u)) ^ 2 ≤ cZeta φ * μ ^ 4)
    (hJζ : (∫ u in s..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2) ≤ 2 * cZeta φ * μ ^ 4)
    (h2 : horizNorm 2 r g y s ≤ L2c φ * μ ^ 2) (h4 : slowNorm 2 r g y s ≤ L4c φ * μ ^ 3) :
    (∀ u ∈ Icc s t, hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤ cB φ * μ ^ 4) ∧
    (∀ u ∈ Icc (s + 1) t, hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤ cB' φ * μ ^ 4) ∧
    (∀ u ∈ Icc s t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤ cBz φ * μ ^ 6) ∧
    (∀ u ∈ Icc (s + 1) t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤ cBz' φ * μ ^ 6) := by
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr; linarith
  have hμ0 : 0 ≤ μ := by linarith
  have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ
  have hμ3 : 1 ≤ μ ^ 3 := one_le_pow₀ hμ
  have hμ4 : μ ^ 2 ≤ μ ^ 4 := mu_pow_mono hμ (by norm_num)
  have hμ6 : μ ^ 4 ≤ μ ^ 6 := mu_pow_mono hμ (by norm_num)
  have hμ4' : (1 : ℝ) ≤ μ ^ 4 := hμ2.trans hμ4
  have hμ6' : (1 : ℝ) ≤ μ ^ 6 := hμ4'.trans hμ6
  have hsT := lt_lifespan hst ht
  have hρs := hρ s ⟨le_rfl, hst⟩
  have hE2 := budget_le_E2 hφ
  have hcA := one_le_cA hφ
  have hcAμ : 0 < cA φ * μ := by positivity
  have hcB := cB_nonneg hφ
  have hcZeta := cZeta_nonneg hφ
  have hE2' : 0 ≤ E2 φ := E2_nonneg hφ
  have hcZ := cZ_nonneg hφ
  have hcI0 := slowCI_nonneg hφ
  have hE2μ4 : 2 * (4 * φ ^ 2 + 4) ≤ 2 * E2 φ * μ ^ 4 := by
    have := mul_le_mul_of_nonneg_left hμ4' hE2'
    linarith
  have hE2μ6 : 4 * (4 * φ ^ 2 + 4) ≤ 4 * E2 φ * μ ^ 6 := by
    have := mul_le_mul_of_nonneg_left hμ6' hE2'
    linarith
  -- the start values of the corrected field
  have hh0 : hnorm 2 (PiH (corrSlow r g y s)) ≤ (L2c φ + 1) * μ ^ 2 := by
    have := (horizNorm_le_corr h hr0 hs hsT (le_refl (2 : ℝ))).2
    have e : (L2c φ + 1) * μ ^ 2 = L2c φ * μ ^ 2 + μ ^ 2 := by ring
    rw [e]; linarith
  have hζ0 : hnorm 2 (PiV (corrSlow r g y s)) ≤ (L4c φ + 1) * μ ^ 3 := by
    have hz := (corrSlow_adm h hr0 hs hsT).inH
    have h1' := hnorm_PiV_le' hz
    have := (slowNorm_le_corr h hr0 hs hsT (le_refl (2 : ℝ))).2
    have e : (L4c φ + 1) * μ ^ 3 = L4c φ * μ ^ 3 + μ ^ 3 := by ring
    rw [e]; linarith
  have hh0sq : hnorm 2 (PiH (corrSlow r g y s)) ^ 2 ≤ (L2c φ + 1) ^ 2 * μ ^ 4 := by
    have := pow_le_pow_left₀ (hnorm_nonneg _ _) hh0 2
    rw [mul_pow, ← pow_mul] at this
    norm_num at this
    exact this
  have hζ0sq : hnorm 2 (PiV (corrSlow r g y s)) ^ 2 ≤ (L4c φ + 1) ^ 2 * μ ^ 6 := by
    have := pow_le_pow_left₀ (hnorm_nonneg _ _) hζ0 2
    rw [mul_pow, ← pow_mul] at this
    norm_num at this
    exact this
  have hAh4 : 450 * (cA φ * μ) ^ 4 = 450 * cA φ ^ 4 * μ ^ 4 := by ring
  have hAh4n : 0 ≤ 450 * cA φ ^ 4 * μ ^ 4 := by positivity
  have eB : cB φ * μ ^ 4 = (L2c φ + 1) ^ 2 * μ ^ 4 + 450 * cA φ ^ 4 * μ ^ 4 +
      2 * E2 φ * μ ^ 4 := by unfold cB; ring
  have eB' : cB' φ * μ ^ 4 = slowCI φ * μ ^ 4 + 450 * cA φ ^ 4 * μ ^ 4 + 2 * E2 φ * μ ^ 4 := by
    unfold cB'; ring
  -- F3 from the start
  have hBh := corr_horiz_h2 h hr0 hs hst ht hcAμ hA hE s ⟨le_rfl, hst⟩
  have hcBpiece : ∀ u ∈ Icc s t, hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤ cB φ * μ ^ 4 := by
    intro u hu
    have h1' := hBh u hu
    rw [hAh4] at h1'
    have hn : 0 ≤ (L2c φ + 1) ^ 2 * μ ^ 4 := by positivity
    have hmax : max (hnorm 2 (PiH (corrSlow r g y s)) ^ 2) (450 * cA φ ^ 4 * μ ^ 4) ≤
        (L2c φ + 1) ^ 2 * μ ^ 4 + 450 * cA φ ^ 4 * μ ^ 4 :=
      max_le (by linarith) (by linarith)
    rw [eB]
    linarith
  -- F3 regained: the good time of the first unit
  have hcBregain : ∀ u ∈ Icc (s + 1) t,
      hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤ cB' φ * μ ^ 4 := by
    intro u hu
    have hs1 : s + 1 ≤ t := hu.1.trans hu.2
    have hc : ContinuousOn (fun v => hnorm 2 (PiH (corrSlow r g y v)) ^ 2) (Icc s (s + 1)) :=
      (continuousOn_corrH_sq h hr0 (Or.inr (Or.inr rfl)) (hs.trans hst) ht).mono
        (Icc_subset_Icc hs hs1)
    obtain ⟨τ, hτ, hτle⟩ := exists_le_average (by linarith : s < s + 1) hc
    simp only [add_sub_cancel_left, mul_one] at hτle
    have hτt : τ ∈ Icc s t := ⟨hτ.1, hτ.2.trans hs1⟩
    have hb := corr_horiz_h2 h hr0 hs hst ht hcAμ hA hE τ hτt u ⟨hτ.2.trans hu.1, hu.2⟩
    rw [hAh4] at hb
    have hτI := hτle.trans (hI1w hs1)
    have hcIμ : slowCI φ * μ ^ 2 ≤ slowCI φ * μ ^ 4 := mul_le_mul_of_nonneg_left hμ4 hcI0
    have hn : 0 ≤ slowCI φ * μ ^ 4 := by positivity
    have hmax : max (hnorm 2 (PiH (corrSlow r g y τ)) ^ 2) (450 * cA φ ^ 4 * μ ^ 4) ≤
        slowCI φ * μ ^ 4 + 450 * cA φ ^ 4 * μ ^ 4 :=
      max_le (by linarith) (by linarith)
    rw [eB']
    linarith
  -- the piece-wide bounds feeding the `ζ`-barrier
  have hBh' : ∀ u ∈ Icc s t, hnorm 2 (PiH (corrSlow r g y u)) ≤ Real.sqrt (cB φ) * μ ^ 2 := by
    intro u hu
    refine le_sqrt_mul (hnorm_nonneg _ _) hcB (by positivity) ?_
    have := hcBpiece u hu
    rw [← pow_mul]
    norm_num
    exact this
  have hAζ : ∀ u ∈ Icc s t, hnorm 1 (PiV (corrSlow r g y u)) ≤ Real.sqrt (cZeta φ) * μ ^ 2 := by
    intro u hu
    refine le_sqrt_mul (hnorm_nonneg _ _) hcZeta (by positivity) ?_
    have := hζ u hu
    rw [← pow_mul]
    norm_num
    exact this
  have hcB1 : 0 < Real.sqrt (cB φ) * μ ^ 2 := by
    have := cB_pos hφ
    positivity
  have hcZeta1 : 0 < Real.sqrt (cZeta φ) * μ ^ 2 := by
    have := cZeta_pos hφ
    positivity
  have hZs := zeta_level_le hφ hμ
  have hcZμ : 0 ≤ cZ φ * μ ^ 6 := by positivity
  have eBz : cBz φ * μ ^ 6 = (L4c φ + 1) ^ 2 * μ ^ 6 + cZ φ * μ ^ 6 + 4 * E2 φ * μ ^ 6 := by
    unfold cBz; ring
  have eBz' : cBz' φ * μ ^ 6 = 2 * cZeta φ * μ ^ 6 + cZ φ * μ ^ 6 + 4 * E2 φ * μ ^ 6 := by
    unfold cBz'; ring
  -- F4 from the start
  have hBζ := corr_vert_h2 h hr0 hs hst ht hcAμ hcB1 hcZeta1 hA hBh' hAζ hE s ⟨le_rfl, hst⟩
  have hcBzpiece : ∀ u ∈ Icc s t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤ cBz φ * μ ^ 6 := by
    intro u hu
    have h1' := hBζ u hu
    have hmax := max_le_max (le_refl (hnorm 2 (PiV (corrSlow r g y s)) ^ 2)) hZs
    have hn : 0 ≤ (L4c φ + 1) ^ 2 * μ ^ 6 := by positivity
    have hmax' : max (hnorm 2 (PiV (corrSlow r g y s)) ^ 2) (cZ φ * μ ^ 6) ≤
        (L4c φ + 1) ^ 2 * μ ^ 6 + cZ φ * μ ^ 6 :=
      max_le (by linarith) (by linarith)
    rw [eBz]
    linarith
  -- F4 regained
  have hcBzregain : ∀ u ∈ Icc (s + 1) t,
      hnorm 2 (PiV (corrSlow r g y u)) ^ 2 ≤ cBz' φ * μ ^ 6 := by
    intro u hu
    have hs1 : s + 1 ≤ t := hu.1.trans hu.2
    have hc : ContinuousOn (fun v => hnorm 2 (PiV (corrSlow r g y v)) ^ 2) (Icc s (s + 1)) :=
      (continuousOn_corrV_sq h hr0 (Or.inr (Or.inr rfl)) (hs.trans hst) ht).mono
        (Icc_subset_Icc hs hs1)
    obtain ⟨τ, hτ, hτle⟩ := exists_le_average (by linarith : s < s + 1) hc
    simp only [add_sub_cancel_left, mul_one] at hτle
    have hτt : τ ∈ Icc s t := ⟨hτ.1, hτ.2.trans hs1⟩
    have hb := corr_vert_h2 h hr0 hs hst ht hcAμ hcB1 hcZeta1 hA hBh' hAζ hE τ hτt u
      ⟨hτ.2.trans hu.1, hu.2⟩
    have hwin : (∫ v in s..(s + 1), hnorm 2 (PiV (corrSlow r g y v)) ^ 2) ≤
        ∫ v in s..t, hnorm 2 (PiV (corrSlow r g y v)) ^ 2 := by
      have hp : HeatPair 1 s t (fun u => PiV (corrSlow r g y u))
          (fun u => PiV (corrForce r g y u)) :=
        (heatPair_corrV h hr0 (Or.inr (Or.inl rfl)) (hs.trans hst) ht).mono hs le_rfl
      have hD := hp.intervalIntegrable_dissipation hst
      rw [one_add_one_eq_two] at hD
      exact intervalIntegral.integral_mono_interval le_rfl (by linarith) hs1
        (Filter.Eventually.of_forall fun _ => sq_nonneg _) hD
    have hτJ := hτle.trans (hwin.trans hJζ)
    have hζμ : 2 * cZeta φ * μ ^ 4 ≤ 2 * cZeta φ * μ ^ 6 :=
      mul_le_mul_of_nonneg_left hμ6 (by positivity)
    have hmax := max_le_max (le_refl (hnorm 2 (PiV (corrSlow r g y τ)) ^ 2)) hZs
    have hn : 0 ≤ 2 * cZeta φ * μ ^ 6 := by positivity
    have hmax' : max (hnorm 2 (PiV (corrSlow r g y τ)) ^ 2) (cZ φ * μ ^ 6) ≤
        2 * cZeta φ * μ ^ 6 + cZ φ * μ ^ 6 :=
      max_le (by linarith) (by linarith)
    rw [eBz']
    linarith
  exact ⟨hcBpiece, hcBregain, hcBzpiece, hcBzregain⟩

/-! ### The interface -/

/-- The pieces of `Cfin` dominate each individual constant. -/
lemma Cfin_pieces (hφ : 0 ≤ φ) {cW : ℝ} (hcW : 0 ≤ cW) :
    cA φ + 1 ≤ Cfin φ cW ∧ Real.sqrt (cB φ) + 1 ≤ Cfin φ cW ∧
      Real.sqrt (cA φ ^ 2 + cZeta φ) + 1 ≤ Cfin φ cW ∧
      Real.sqrt (cB φ + cBz φ) + 1 ≤ Cfin φ cW ∧
      cW * Real.sqrt (Real.sqrt (cA φ ^ 2 + cZeta φ) * Real.sqrt (cB φ + cBz φ)) + c4 ≤
        Cfin φ cW ∧
      cJ φ ≤ Cfin φ cW := by
  have h1 := cA_nonneg hφ
  have h2 := Real.sqrt_nonneg (cB φ)
  have h3 := Real.sqrt_nonneg (cA φ ^ 2 + cZeta φ)
  have h4 := Real.sqrt_nonneg (cB φ + cBz φ)
  have h5 := Real.sqrt_nonneg (Real.sqrt (cA φ ^ 2 + cZeta φ) * Real.sqrt (cB φ + cBz φ))
  have h6 := mul_nonneg hcW h5
  have h7 := cJ_nonneg hφ
  have h8 := c4_pos
  unfold Cfin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The pointwise slow caps on the piece, from the chain outputs. -/
lemma cap_pointwise (hφ : 0 ≤ φ) (hμ : 1 ≤ μ) (h : ActualSol μ φ r g y Ty) (hr0 : r ≠ 0)
    {u : ℝ} (hu0 : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) {cW : ℝ} (hcW : 0 ≤ cW)
    (hρu : hnorm 2 (slowCorr r g y u) ≤ 1 / 4)
    (hE0 : hnorm 0 (corrSlow r g y u) ≤ cA φ * μ)
    (hA : hnorm 1 (PiH (corrSlow r g y u)) ≤ cA φ * μ)
    (hB : hnorm 2 (PiH (corrSlow r g y u)) ^ 2 ≤ cB φ * μ ^ 4)
    (hz1 : hnorm 1 (corrSlow r g y u) ≤ Real.sqrt (cA φ ^ 2 + cZeta φ) * μ ^ 2)
    (hz2 : hnorm 2 (corrSlow r g y u) ≤ Real.sqrt (cB φ + cBz φ) * μ ^ 3) :
    SlowLevel (fun _ => Cfin φ cW) μ slowExpF r g y u := by
  obtain ⟨hC1, hC3, hC4, hC5, -, -⟩ := Cfin_pieces hφ hcW
  have hμ0 : 0 ≤ μ := by linarith
  have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ
  have hμ3 : 1 ≤ μ ^ 3 := one_le_pow₀ hμ
  have hcB := cB_nonneg hφ
  rw [slowLevel_F_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := (slowNorm_le_corr h hr0 hu0 huT (by norm_num : (0 : ℝ) ≤ 2)).1
    calc slowNorm 0 r g y u ≤ cA φ * μ + 1 / 4 := by linarith
      _ ≤ (cA φ + 1) * μ := by nlinarith
      _ ≤ Cfin φ cW * μ := mul_le_mul_of_nonneg_right hC1 hμ0
  · have := (horizNorm_le_corr h hr0 hu0 huT (by norm_num : (1 : ℝ) ≤ 2)).1
    calc horizNorm 1 r g y u ≤ cA φ * μ + 1 / 4 := by linarith
      _ ≤ (cA φ + 1) * μ := by nlinarith
      _ ≤ Cfin φ cW * μ := mul_le_mul_of_nonneg_right hC1 hμ0
  · have := (horizNorm_le_corr h hr0 hu0 huT (le_refl (2 : ℝ))).1
    have hb : hnorm 2 (PiH (corrSlow r g y u)) ≤ Real.sqrt (cB φ) * μ ^ 2 :=
      le_sqrt_mul (hnorm_nonneg _ _) hcB (by positivity) (by rw [← pow_mul]; norm_num; exact hB)
    calc horizNorm 2 r g y u ≤ Real.sqrt (cB φ) * μ ^ 2 + 1 / 4 := by linarith
      _ ≤ (Real.sqrt (cB φ) + 1) * μ ^ 2 := by nlinarith
      _ ≤ Cfin φ cW * μ ^ 2 := mul_le_mul_of_nonneg_right hC3 (by positivity)
  · have := (slowNorm_le_corr h hr0 hu0 huT (by norm_num : (1 : ℝ) ≤ 2)).1
    calc slowNorm 1 r g y u ≤ Real.sqrt (cA φ ^ 2 + cZeta φ) * μ ^ 2 + 1 / 4 := by linarith
      _ ≤ (Real.sqrt (cA φ ^ 2 + cZeta φ) + 1) * μ ^ 2 := by nlinarith
      _ ≤ Cfin φ cW * μ ^ 2 := mul_le_mul_of_nonneg_right hC4 (by positivity)
  · have := (slowNorm_le_corr h hr0 hu0 huT (le_refl (2 : ℝ))).1
    calc slowNorm 2 r g y u ≤ Real.sqrt (cB φ + cBz φ) * μ ^ 3 + 1 / 4 := by linarith
      _ ≤ (Real.sqrt (cB φ + cBz φ) + 1) * μ ^ 3 := by nlinarith
      _ ≤ Cfin φ cW * μ ^ 3 := mul_le_mul_of_nonneg_right hC5 (by positivity)

/-- The Wiener cap `W_S ≤ C μ^{5/2}` on the piece. -/
lemma cap_wiener (hφ : 0 ≤ φ) (hμ : 1 ≤ μ) (h : ActualSol μ φ r g y Ty) (hr0 : r ≠ 0)
    {u : ℝ} (hu0 : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) {cW : ℝ} (hcW : 0 ≤ cW)
    (hW : ∀ v : Field, MZ 2 v → wiener v ≤ cW * Real.sqrt (hnorm 1 v * hnorm 2 v))
    (hρu : hnorm 2 (slowCorr r g y u) ≤ 1 / 4)
    (hz1 : hnorm 1 (corrSlow r g y u) ≤ Real.sqrt (cA φ ^ 2 + cZeta φ) * μ ^ 2)
    (hz2 : hnorm 2 (corrSlow r g y u) ≤ Real.sqrt (cB φ + cBz φ) * μ ^ 3) :
    slowWiener r g y u ≤ Cfin φ cW * μ ^ slowExpF.eW := by
  obtain ⟨-, -, -, -, hC6, -⟩ := Cfin_pieces hφ hcW
  have hμ0 : 0 ≤ μ := by linarith
  have hz := corrSlow_adm h hr0 hu0 huT
  have hR := slowCorr_adm h hr0 hu0 huT
  have e : PiS (actual r g y u) = corrSlow r g y u + (-slowCorr r g y u) := by
    simp [corrSlow]
  have hWS : wiener (PiS (actual r g y u)) ≤
      wiener (corrSlow r g y u) + wiener (slowCorr r g y u) := by
    rw [e]
    have := wiener_add_le (summable_wiener hz.inH) (summable_wiener hR.inH.neg)
    have e2 : wiener (-slowCorr r g y u) = wiener (slowCorr r g y u) := by
      simp [wiener]
    linarith
  have hWz := hW _ hz.mz
  have hWR : wiener (slowCorr r g y u) ≤ c4 / 4 := by
    have := wiener_le hR.mz
    have := c4_pos
    nlinarith
  have hprod : hnorm 1 (corrSlow r g y u) * hnorm 2 (corrSlow r g y u) ≤
      Real.sqrt (cA φ ^ 2 + cZeta φ) * Real.sqrt (cB φ + cBz φ) * μ ^ 5 := by
    have := mul_le_mul hz1 hz2 (hnorm_nonneg _ _) (by positivity)
    calc hnorm 1 (corrSlow r g y u) * hnorm 2 (corrSlow r g y u)
        ≤ Real.sqrt (cA φ ^ 2 + cZeta φ) * μ ^ 2 * (Real.sqrt (cB φ + cBz φ) * μ ^ 3) := this
      _ = Real.sqrt (cA φ ^ 2 + cZeta φ) * Real.sqrt (cB φ + cBz φ) * μ ^ 5 := by ring
  have hsq : Real.sqrt (hnorm 1 (corrSlow r g y u) * hnorm 2 (corrSlow r g y u)) ≤
      Real.sqrt (Real.sqrt (cA φ ^ 2 + cZeta φ) * Real.sqrt (cB φ + cBz φ)) *
        Real.sqrt (μ ^ 5) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hprod
  have hμ5 : 1 ≤ Real.sqrt (μ ^ 5) := by
    rw [Real.one_le_sqrt]; exact one_le_pow₀ hμ
  have heW : μ ^ slowExpF.eW = Real.sqrt (μ ^ 5) := rpow_five_half hμ0
  have hS0 := Real.sqrt_nonneg (Real.sqrt (cA φ ^ 2 + cZeta φ) * Real.sqrt (cB φ + cBz φ))
  have hc4 := c4_pos
  have h1 := mul_le_mul_of_nonneg_left hsq hcW
  have h2 : c4 / 4 ≤ c4 * Real.sqrt (μ ^ 5) := by nlinarith
  show wiener (PiS (actual r g y u)) ≤ Cfin φ cW * μ ^ slowExpF.eW
  rw [heW]
  calc wiener (PiS (actual r g y u))
      ≤ cW * Real.sqrt (hnorm 1 (corrSlow r g y u) * hnorm 2 (corrSlow r g y u)) + c4 / 4 := by
        linarith
    _ ≤ (cW * Real.sqrt (Real.sqrt (cA φ ^ 2 + cZeta φ) * Real.sqrt (cB φ + cBz φ)) + c4) *
        Real.sqrt (μ ^ 5) := by nlinarith
    _ ≤ Cfin φ cW * Real.sqrt (μ ^ 5) := mul_le_mul_of_nonneg_right hC6 (by positivity)

/-- **`SlowCapsInterface 2 slowExpF qS`** (E7-F): the chain `chain_low`, `chain_high`, the
transfer `S ↔ y_S` by `‖R_S‖₂ ≤ 1/4`, the Wiener interpolation and the `∫ b_S²` budget. -/
theorem slowCapsInterface_of_threshold : SlowCapsInterface 2 slowExpF qS := by
  intro φ hφ
  obtain ⟨cW, hcW0, hcW⟩ := exists_wiener_interp
  refine ⟨Lvec φ, Cfin φ cW, one_le_Lvec hφ, ?_⟩
  intro μ hμ r g y Ty caps s t h hP hlev
  obtain ⟨hr, hρ, hres, hE⟩ := slow_small h hφ hP
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr; linarith
  have hs := hP.hs
  have hst := hP.hst
  have ht := hP.ht
  have hlen := hP.len
  have ht0 : 0 ≤ t := hs.trans hst
  have hμ0 : 0 ≤ μ := by linarith
  have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ
  have hμ3 : 1 ≤ μ ^ 3 := one_le_pow₀ hμ
  have hμ4 : μ ^ 2 ≤ μ ^ 4 := pow_le_pow_right₀ hμ (by norm_num)
  have hμ46 : μ ^ 4 ≤ μ ^ 6 := pow_le_pow_right₀ hμ (by norm_num)
  have hμ4' : (1 : ℝ) ≤ μ ^ 4 := hμ2.trans hμ4
  rw [slowLevel_F_iff] at hlev
  obtain ⟨h0, h1, h2, h3, h4⟩ := hlev
  simp only [Lvec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2 h3 h4
  obtain ⟨hE0, hEr, hA, hAr, hI1, hI1w, hζ, hζr, hJζ⟩ :=
    chain_low hφ hμ h hr hs hst ht hlen hρ hres h0 h1 h3
  obtain ⟨hB, hBr, hBz, hBzr⟩ :=
    chain_high hφ hμ h hr hs hst ht hρ hE hA hI1w hζ hJζ h2 h4
  have hcA := cA_nonneg hφ
  have hcB := cB_nonneg hφ
  have hcZeta := cZeta_nonneg hφ
  have hcBz := cBz_nonneg hφ
  obtain ⟨-, -, -, -, -, hC7⟩ := Cfin_pieces hφ hcW0.le
  -- pointwise bounds on the full corrected field
  have hz1 : ∀ u ∈ Icc s t,
      hnorm 1 (corrSlow r g y u) ≤ Real.sqrt (cA φ ^ 2 + cZeta φ) * μ ^ 2 := by
    intro u hu
    have hz := (corrSlow_adm h hr0 (hs.trans hu.1) (lt_lifespan hu.2 ht)).inH.mono
      (by norm_num : (1 : ℝ) ≤ 2)
    have hsplit := hnorm_sq_split_slow hz
    rw [PiS_corrSlow] at hsplit
    have ha2 : hnorm 1 (PiH (corrSlow r g y u)) ^ 2 ≤ cA φ ^ 2 * μ ^ 2 := by
      have := pow_le_pow_left₀ (hnorm_nonneg _ _) (hA u hu) 2
      rw [mul_pow] at this; exact this
    have hζu := hζ u hu
    refine le_sqrt_mul (hnorm_nonneg _ _) (by positivity) (by positivity) ?_
    rw [← pow_mul]
    norm_num
    have : cA φ ^ 2 * μ ^ 2 ≤ cA φ ^ 2 * μ ^ 4 := mul_le_mul_of_nonneg_left hμ4 (by positivity)
    linarith
  have hz2 : ∀ u ∈ Icc s t, hnorm 2 (corrSlow r g y u) ≤ Real.sqrt (cB φ + cBz φ) * μ ^ 3 := by
    intro u hu
    have hz := (corrSlow_adm h hr0 (hs.trans hu.1) (lt_lifespan hu.2 ht)).inH
    have hsplit := hnorm_sq_split_slow hz
    rw [PiS_corrSlow] at hsplit
    have hb := hB u hu
    have hbz := hBz u hu
    refine le_sqrt_mul (hnorm_nonneg _ _) (by positivity) (by positivity) ?_
    rw [← pow_mul]
    norm_num
    have : cB φ * μ ^ 4 ≤ cB φ * μ ^ 6 := mul_le_mul_of_nonneg_left hμ46 hcB
    linarith
  refine ⟨fun u hu => ⟨?_, ?_⟩, ?_, fun u hu => ?_⟩
  · exact cap_pointwise hφ hμ h hr0 (hs.trans hu.1) (lt_lifespan hu.2 ht) hcW0.le (hρ u hu)
      (hE0 u hu) (hA u hu) (hB u hu) (hz1 u hu) (hz2 u hu)
  · exact cap_wiener hφ hμ h hr0 (hs.trans hu.1) (lt_lifespan hu.2 ht) hcW0.le hcW (hρ u hu)
      (hz1 u hu) (hz2 u hu)
  · -- the `∫ b_S²` budget
    have heJ : μ ^ slowExpF.eJ = μ ^ 4 := rpow_four μ
    show (∫ u in s..t, slowNorm 2 r g y u ^ 2) ≤ Cfin φ cW * μ ^ slowExpF.eJ
    rw [heJ]
    have hcS : ContinuousOn (fun u => slowNorm 2 r g y u ^ 2) (Icc s t) :=
      ((norms_continuous h ht0 ht).2.2.2.1.mono (Icc_subset_Icc_left hs)).pow 2
    have hcz : ContinuousOn (fun u => hnorm 2 (corrSlow r g y u) ^ 2) (Icc s t) :=
      (continuousOn_corr_sq h hr0 (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
    have hpt : ∀ u ∈ Icc s t,
        slowNorm 2 r g y u ^ 2 ≤ 2 * hnorm 2 (corrSlow r g y u) ^ 2 + 1 / 8 := by
      intro u hu
      have hu0 : 0 ≤ u := hs.trans hu.1
      have huT := lt_lifespan hu.2 ht
      have h1' := (slowNorm_le_corr h hr0 hu0 huT (le_refl (2 : ℝ))).1
      have h2' := hρ u hu
      have hb0 : 0 ≤ slowNorm 2 r g y u := hnorm_nonneg _ _
      nlinarith [sq_nonneg (hnorm 2 (corrSlow r g y u) - 1 / 4)]
    have hint : (∫ u in s..t, slowNorm 2 r g y u ^ 2) ≤
        ∫ u in s..t, (2 * hnorm 2 (corrSlow r g y u) ^ 2 + 1 / 8) :=
      intervalIntegral.integral_mono_on hst (hcS.intervalIntegrable_of_Icc hst)
        (((continuousOn_const.mul hcz).add continuousOn_const).intervalIntegrable_of_Icc hst) hpt
    rw [intervalIntegral.integral_add ((hcz.intervalIntegrable_of_Icc hst).const_mul _)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul] at hint
    -- `∫ ‖y_S‖₂² = ∫ b_h² + ∫ b_ζ²`
    have hcH : ContinuousOn (fun u => hnorm 2 (PiH (corrSlow r g y u)) ^ 2) (Icc s t) :=
      (continuousOn_corrH_sq h hr0 (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
    have hcV : ContinuousOn (fun u => hnorm 2 (PiV (corrSlow r g y u)) ^ 2) (Icc s t) :=
      (continuousOn_corrV_sq h hr0 (Or.inr (Or.inr rfl)) ht0 ht).mono (Icc_subset_Icc_left hs)
    have hsplit : (∫ u in s..t, hnorm 2 (corrSlow r g y u) ^ 2) =
        (∫ u in s..t, hnorm 2 (PiH (corrSlow r g y u)) ^ 2) +
          ∫ u in s..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2 := by
      rw [← intervalIntegral.integral_add (hcH.intervalIntegrable_of_Icc hst)
        (hcV.intervalIntegrable_of_Icc hst)]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hst] at hu
      have hz := (corrSlow_adm h hr0 (hs.trans hu.1) (lt_lifespan hu.2 ht)).inH
      have := hnorm_sq_split_slow hz
      rw [PiS_corrSlow] at this
      exact this
    have hcIμ : slowCI φ * μ ^ 2 ≤ slowCI φ * μ ^ 4 := mul_le_mul_of_nonneg_left hμ4 (slowCI_nonneg hφ)
    have hlen8 : (t - s) * (1 / 8) ≤ μ ^ 4 := by nlinarith
    have hcJ : 2 * (slowCI φ * μ ^ 4 + 2 * cZeta φ * μ ^ 4) + μ ^ 4 ≤ cJ φ * μ ^ 4 := by
      unfold cJ
      exact le_of_eq (by ring)
    calc (∫ u in s..t, slowNorm 2 r g y u ^ 2)
        ≤ 2 * ((∫ u in s..t, hnorm 2 (PiH (corrSlow r g y u)) ^ 2) +
            ∫ u in s..t, hnorm 2 (PiV (corrSlow r g y u)) ^ 2) + (t - s) * (1 / 8) := by
          rw [← hsplit]; exact hint
      _ ≤ 2 * (slowCI φ * μ ^ 4 + 2 * cZeta φ * μ ^ 4) + μ ^ 4 := by linarith
      _ ≤ cJ φ * μ ^ 4 := hcJ
      _ ≤ Cfin φ cW * μ ^ 4 := mul_le_mul_of_nonneg_right hC7 (by positivity)
  · -- the regained levels after one unit
    have hut : u ∈ Icc s t := ⟨by linarith [hu.1], hu.2⟩
    have hu0 : 0 ≤ u := hs.trans hut.1
    have huT := lt_lifespan hu.2 ht
    rw [slowLevel_F_iff]
    simp only [Lvec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := (slowNorm_le_corr h hr0 hu0 huT (by norm_num : (0 : ℝ) ≤ 2)).1
      have := hEr u hu
      have := hρ u hut
      linarith
    · have := (horizNorm_le_corr h hr0 hu0 huT (by norm_num : (1 : ℝ) ≤ 2)).1
      have := hAr u hu
      have := hρ u hut
      linarith
    · have := (horizNorm_le_corr h hr0 hu0 huT (le_refl (2 : ℝ))).1
      have hb := hBr u hu
      have := hρ u hut
      have := add_quarter_le_sqrt (hnorm_nonneg 2 (PiH (corrSlow r g y u))) (cB'_nonneg hφ) hμ2
        (by rw [← pow_mul]; norm_num; exact hb)
      unfold L2c
      linarith
    · have := (slowNorm_le_corr h hr0 hu0 huT (by norm_num : (1 : ℝ) ≤ 2)).1
      have := hρ u hut
      have hz := (corrSlow_adm h hr0 hu0 huT).inH.mono (by norm_num : (1 : ℝ) ≤ 2)
      have hsplit := hnorm_sq_split_slow hz
      rw [PiS_corrSlow] at hsplit
      have ha2 : hnorm 1 (PiH (corrSlow r g y u)) ^ 2 ≤ cA φ ^ 2 * μ ^ 2 := by
        have := pow_le_pow_left₀ (hnorm_nonneg _ _) (hA u hut) 2
        rw [mul_pow] at this; exact this
      have hζu := hζr u hu
      have hz1' : hnorm 1 (corrSlow r g y u) ^ 2 ≤ (cA φ ^ 2 + cZ' φ) * (μ ^ 2) ^ 2 := by
        have : cA φ ^ 2 * μ ^ 2 ≤ cA φ ^ 2 * μ ^ 4 :=
          mul_le_mul_of_nonneg_left hμ4 (by positivity)
        rw [← pow_mul]
        norm_num
        have e : (cA φ ^ 2 + cZ' φ) * μ ^ 4 = cA φ ^ 2 * μ ^ 4 + cZ' φ * μ ^ 4 := by ring
        rw [e]
        linarith
      have := add_quarter_le_sqrt (hnorm_nonneg 1 (corrSlow r g y u))
        (by have := cZ'_nonneg hφ; positivity) hμ2 hz1'
      unfold L3c
      linarith
    · have := (slowNorm_le_corr h hr0 hu0 huT (le_refl (2 : ℝ))).1
      have := hρ u hut
      have hz := (corrSlow_adm h hr0 hu0 huT).inH
      have hsplit := hnorm_sq_split_slow hz
      rw [PiS_corrSlow] at hsplit
      have hb := hBr u hu
      have hbz := hBzr u hu
      have hz2' : hnorm 2 (corrSlow r g y u) ^ 2 ≤ (cB' φ + cBz' φ) * (μ ^ 3) ^ 2 := by
        have : cB' φ * μ ^ 4 ≤ cB' φ * μ ^ 6 := mul_le_mul_of_nonneg_left hμ46 (cB'_nonneg hφ)
        rw [← pow_mul]
        norm_num
        have e : (cB' φ + cBz' φ) * μ ^ 6 = cB' φ * μ ^ 6 + cBz' φ * μ ^ 6 := by ring
        rw [e]
        linarith
      have := add_quarter_le_sqrt (hnorm_nonneg 2 (corrSlow r g y u))
        (by have := cB'_nonneg hφ; have := cBz'_nonneg hφ; positivity) hμ3 hz2'
      unfold L4c
      linarith

/-! ### Degree bookkeeping (Table quant-fixed, roles 18–21) -/

/-- The threshold with every cap replaced by the common bound `N = K μ^v` and the pair
`A_S y + W_S P_F` by `X₂ = 2K² μ^{2+δ+v}` (same syntactic shape as `qS`, for `gcongr`). -/
def qBound (φ N X₂ : ℝ) : ℝ :=
  1 + 32 * c4 * N ^ 2 +
    (8 * c4 * N ^ 2 + 4 * φ * (c4 * (N + N) + N + c4 * N) + 8 * c4 * φ ^ 2 +
      4 * c4 * N * (N + 2 * (N + N + 2 * φ) * (N + c4 * N + 2 * c4 * φ)) +
      16 * c4 * N ^ 2 * (c4 * N + N + c4)) +
    2 ^ 11 * (1 + c4) ^ 2 * (1 + N ^ 2 + N * (N + (N + N + φ) * (N + N + φ)) +
      X₂ * (N + (N + N + φ) * (N + N + φ)) +
      N ^ 3 + φ * (N + N + N + N + φ) * (N + (N + N + φ) * (N + N + φ)) +
      φ * (N + N + N + φ) + N ^ 2 * (N + N + 1))

/-- The coefficient of `N³` in the residual part of `qBound` (padding by `N ≥ 1`). -/
def Q1a (φ : ℝ) : ℝ :=
  1 + 32 * c4 + 8 * c4 + (12 * c4 * φ + 4 * φ) + 8 * c4 * φ ^ 2 +
    (16 * c4 * (1 + c4) + 4 * c4 + (48 * c4 ^ 2 * φ + 16 * c4 * φ) + 32 * c4 ^ 2 * φ ^ 2) +
    (16 * c4 * (1 + c4) + 16 * c4 ^ 2)

/-- The coefficient of `N³` in the budget part of `qBound` (padding by `N ≥ 1`). -/
def Q1b (φ : ℝ) : ℝ :=
  1 + 1 + (1 + 4 + 4 * φ + φ ^ 2) + 1 + (16 * φ + 4 * φ + 20 * φ ^ 2 + φ ^ 2 + 8 * φ ^ 3 + φ ^ 4) +
    (3 * φ + φ ^ 2) + (2 + 1)

/-- The coefficient of `X₂ N²` in the budget part of `qBound`. -/
def Q2b (φ : ℝ) : ℝ := 1 + 4 + 4 * φ + φ ^ 2

/-- The coefficient of `N³` after padding every lower monomial by `N ≥ 1`. -/
def Q1 (φ : ℝ) : ℝ := Q1a φ + 2 ^ 11 * (1 + c4) ^ 2 * Q1b φ

/-- The coefficient of `X₂ N²`. -/
def Q2 (φ : ℝ) : ℝ := 2 ^ 11 * (1 + c4) ^ 2 * Q2b φ

/-- `qS ≤ qBound` once every cap is below `N` and `A_S y + W_S P_F ≤ X₂` (monotonicity). -/
lemma qS_le_qBound {φ N X₂ : ℝ} (hφ : 0 ≤ φ) (hN : 0 ≤ N) (hX₂ : 0 ≤ X₂) (caps : Caps)
    (hP : cp caps.PF ≤ N) (hY : cp caps.yF ≤ N) (hA : cp caps.AS ≤ N) (hB : cp caps.BS ≤ N)
    (hW : cp caps.WS ≤ N) (hAY : cp caps.AS * cp caps.yF + cp caps.WS * cp caps.PF ≤ X₂)
    (μ : ℝ) : qS μ φ caps ≤ qBound φ N X₂ := by
  have h1 := cp_nonneg caps.PF
  have h2 := cp_nonneg caps.yF
  have h3 := cp_nonneg caps.AS
  have h4 := cp_nonneg caps.BS
  have h5 := cp_nonneg caps.WS
  have hc := c4_pos.le
  simp only [qS, resPoly, budgetPoly, qBound]
  gcongr

/-- `qBound ≤ Q1 N³ + Q2 X₂ N²` for `N ≥ 1`, `X₂ ≥ 0` (padding by powers of `N`). -/
lemma qBound_le {φ N X₂ : ℝ} (hφ : 0 ≤ φ) (hN : 1 ≤ N) (hX₂ : 0 ≤ X₂) :
    qBound φ N X₂ ≤ Q1 φ * N ^ 3 + Q2 φ * (X₂ * N ^ 2) := by
  have hc := c4_pos.le
  have hN0 : 0 ≤ N := by linarith
  have hT1 : 0 ≤ N ^ 3 - 1 := by nlinarith [one_le_pow₀ (n := 3) hN]
  have hT2 : 0 ≤ N ^ 3 - N := by nlinarith [one_le_pow₀ (n := 2) hN]
  have hT3 : 0 ≤ N ^ 3 - N ^ 2 := by nlinarith [sq_nonneg N]
  have hU1 : 0 ≤ X₂ * N ^ 2 - X₂ := by nlinarith [one_le_pow₀ (n := 2) hN]
  have hU2 : 0 ≤ X₂ * N ^ 2 - X₂ * N := by nlinarith
  have hφ2 : 0 ≤ φ ^ 2 := sq_nonneg φ
  have hφ3 : 0 ≤ φ ^ 3 := pow_nonneg hφ 3
  have hφ4 : 0 ≤ φ ^ 4 := pow_nonneg hφ 4
  have hc2 : 0 ≤ c4 ^ 2 := sq_nonneg c4
  have hA : 1 + 32 * c4 * N ^ 2 +
      (8 * c4 * N ^ 2 + 4 * φ * (c4 * (N + N) + N + c4 * N) + 8 * c4 * φ ^ 2 +
        4 * c4 * N * (N + 2 * (N + N + 2 * φ) * (N + c4 * N + 2 * c4 * φ)) +
        16 * c4 * N ^ 2 * (c4 * N + N + c4)) ≤ Q1a φ * N ^ 3 := by
    unfold Q1a
    nlinarith [mul_nonneg hc hT3, mul_nonneg (mul_nonneg hc hφ) hT2, mul_nonneg hφ hT2,
      mul_nonneg (mul_nonneg hc hφ2) hT1, mul_nonneg (mul_nonneg hc2 hφ) hT3,
      mul_nonneg (mul_nonneg hc2 hφ2) hT2, mul_nonneg hc2 hT3, hT1, hT2, hT3]
  have hB : 1 + N ^ 2 + N * (N + (N + N + φ) * (N + N + φ)) +
      X₂ * (N + (N + N + φ) * (N + N + φ)) +
      N ^ 3 + φ * (N + N + N + N + φ) * (N + (N + N + φ) * (N + N + φ)) +
      φ * (N + N + N + φ) + N ^ 2 * (N + N + 1) ≤ Q1b φ * N ^ 3 + Q2b φ * (X₂ * N ^ 2) := by
    unfold Q1b Q2b
    nlinarith [mul_nonneg hφ hT3, mul_nonneg hφ2 hT2, mul_nonneg hφ2 hT3, mul_nonneg hφ3 hT2,
      mul_nonneg hφ4 hT1, mul_nonneg hφ hT2, mul_nonneg hφ hU2, mul_nonneg hφ2 hU1, hT1, hT2, hT3,
      hU1, hU2]
  have hκ : (0 : ℝ) ≤ 2 ^ 11 * (1 + c4) ^ 2 := by positivity
  have hB' := mul_le_mul_of_nonneg_left hB hκ
  unfold qBound Q1 Q2
  nlinarith only [hA, hB']

/-- **R1 duty of the slow-correction roles**: `DegreeBelow (281/1000) (9876/719) slowExpF qS`.
With `β = 1719/719`, `v = 2719/719` every cap is `≤ K μ^v`, the pair `A_S y + W_S P_F` is
`≤ 2K² μ^{2+δ+v}` (`5/2 + δ + β ≤ 2 + δ + v`), so `qS ≤ Q1 K³ μ^{3v} + 2 Q2 K⁴ μ^{2+δ+3v}
≤ C μ^κ` with `κ = 2 + 3v + 1/8 < d = β + 3v` (`β − 2 = 281/719 > 1/8`), for `δ ≤ 1/16`. -/
theorem slow_degree : DegreeBelow (281 / 1000) (9876 / 719) slowExpF qS := by
  intro φ hφ
  refine ⟨1 / 16, by norm_num, fun δ K hδ hδ' hK => ?_⟩
  have hβ : betaOf (281 / 1000) = 1719 / 719 := by unfold betaOf; norm_num
  have hv : vOf (281 / 1000) = 2719 / 719 := by unfold vOf; rw [hβ]; norm_num
  refine ⟨Q1 φ * K ^ 3 + 2 * Q2 φ * K ^ 4, 2 + 3 * (2719 / 719) + 1 / 8, by norm_num,
    fun μ hμ caps hc => ?_⟩
  obtain ⟨⟨-, hP⟩, ⟨-, hY⟩, -, hA, hB, -, hW, -, -, -⟩ := hc
  rw [hβ] at hP
  rw [hv] at hY
  simp only [slowExpF] at hA hB hW
  have hμ0 : 0 < μ := by linarith
  have hK0 : 0 ≤ K := by linarith
  set v : ℝ := 2719 / 719 with hvdef
  set N := K * μ ^ v with hNdef
  have hμv : 1 ≤ μ ^ v := Real.one_le_rpow hμ (by norm_num)
  have hN1 : 1 ≤ N := by rw [hNdef]; nlinarith
  have hN0 : 0 ≤ N := by linarith
  have hpow : ∀ a : ℝ, a ≤ v → K * μ ^ a ≤ N := fun a ha =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hμ ha) hK0
  have hPN : cp caps.PF ≤ N := cp_le hN0 (hP.trans (hpow _ (by norm_num)))
  have hYN : cp caps.yF ≤ N := cp_le hN0 hY
  have hAN : cp caps.AS ≤ N := cp_le hN0 (hA.trans (hpow _ (by rw [hvdef]; linarith)))
  have hBN : cp caps.BS ≤ N := cp_le hN0 (hB.trans (hpow _ (by rw [hvdef]; linarith)))
  have hWN : cp caps.WS ≤ N := cp_le hN0 (hW.trans (hpow _ (by rw [hvdef]; linarith)))
  -- the pair `A_S y + W_S P_F ≤ X₂`
  set X₂ := 2 * K ^ 2 * μ ^ (2 + δ + v) with hX₂def
  have hX₂0 : 0 ≤ X₂ := by positivity
  have hAY : cp caps.AS * cp caps.yF ≤ K ^ 2 * μ ^ (2 + δ + v) := by
    have h1 : cp caps.AS ≤ K * μ ^ (2 + δ) := cp_le (by positivity) hA
    have h2 : cp caps.yF ≤ K * μ ^ v := cp_le (by positivity) hY
    calc cp caps.AS * cp caps.yF ≤ (K * μ ^ (2 + δ)) * (K * μ ^ v) :=
          mul_le_mul h1 h2 (cp_nonneg _) (by positivity)
      _ = K ^ 2 * μ ^ (2 + δ + v) := by rw [Real.rpow_add hμ0 (2 + δ) v]; ring
  have hWP : cp caps.WS * cp caps.PF ≤ K ^ 2 * μ ^ (2 + δ + v) := by
    have h1 : cp caps.WS ≤ K * μ ^ (5 / 2 + δ) := cp_le (by positivity) hW
    have h2 : cp caps.PF ≤ K * μ ^ (1719 / 719 : ℝ) := cp_le (by positivity) hP
    have h3 : μ ^ (5 / 2 + δ + 1719 / 719 : ℝ) ≤ μ ^ (2 + δ + v) :=
      Real.rpow_le_rpow_of_exponent_le hμ (by rw [hvdef]; linarith)
    calc cp caps.WS * cp caps.PF ≤ (K * μ ^ (5 / 2 + δ)) * (K * μ ^ (1719 / 719 : ℝ)) :=
          mul_le_mul h1 h2 (cp_nonneg _) (by positivity)
      _ = K ^ 2 * μ ^ (5 / 2 + δ + 1719 / 719 : ℝ) := by
          rw [Real.rpow_add hμ0 (5 / 2 + δ) (1719 / 719)]; ring
      _ ≤ K ^ 2 * μ ^ (2 + δ + v) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hX₂ : cp caps.AS * cp caps.yF + cp caps.WS * cp caps.PF ≤ X₂ := by
    rw [hX₂def]; linarith
  -- the two bounds
  have hmono := qS_le_qBound hφ hN0 hX₂0 caps hPN hYN hAN hBN hWN hX₂ μ
  have hpoly := qBound_le hφ hN1 hX₂0
  -- the powers
  have hpow3 : (μ ^ v) ^ 3 = μ ^ (3 * v) := by
    rw [← Real.rpow_natCast (μ ^ v) 3, ← Real.rpow_mul hμ0.le]
    simp only [Nat.cast_ofNat]
    ring_nf
  have hpow2 : (μ ^ v) ^ 2 = μ ^ (2 * v) := by
    rw [← Real.rpow_natCast (μ ^ v) 2, ← Real.rpow_mul hμ0.le]
    simp only [Nat.cast_ofNat]
    ring_nf
  have hN3 : N ^ 3 = K ^ 3 * μ ^ (3 * v) := by rw [hNdef, mul_pow, hpow3]
  have hX₂N : X₂ * N ^ 2 = 2 * K ^ 4 * μ ^ (2 + δ + 3 * v) := by
    rw [hX₂def, hNdef, mul_pow, hpow2]
    have e : (2 : ℝ) + δ + 3 * v = (2 + δ + v) + 2 * v := by ring
    rw [e, Real.rpow_add hμ0 (2 + δ + v) (2 * v)]
    ring
  have hκ1 : μ ^ (3 * v) ≤ μ ^ (2 + 3 * (2719 / 719 : ℝ) + 1 / 8) :=
    Real.rpow_le_rpow_of_exponent_le hμ (by rw [hvdef]; norm_num)
  have hκ2 : μ ^ (2 + δ + 3 * v) ≤ μ ^ (2 + 3 * (2719 / 719 : ℝ) + 1 / 8) :=
    Real.rpow_le_rpow_of_exponent_le hμ (by rw [hvdef]; linarith)
  have hQ1 : 0 ≤ Q1 φ := by
    have := c4_pos.le
    unfold Q1 Q1a Q1b; positivity
  have hQ2 : 0 ≤ Q2 φ := by
    have := c4_pos.le
    unfold Q2 Q2b; positivity
  calc qS μ φ caps ≤ Q1 φ * N ^ 3 + Q2 φ * (X₂ * N ^ 2) := hmono.trans hpoly
    _ = Q1 φ * K ^ 3 * μ ^ (3 * v) + 2 * Q2 φ * K ^ 4 * μ ^ (2 + δ + 3 * v) := by
        rw [hN3, hX₂N]; ring
    _ ≤ Q1 φ * K ^ 3 * μ ^ (2 + 3 * (2719 / 719 : ℝ) + 1 / 8) +
        2 * Q2 φ * K ^ 4 * μ ^ (2 + 3 * (2719 / 719 : ℝ) + 1 / 8) := by
        gcongr
    _ = (Q1 φ * K ^ 3 + 2 * Q2 φ * K ^ 4) * μ ^ (2 + 3 * (2719 / 719 : ℝ) + 1 / 8) := by ring

/-! ### The final statement -/

/-- **E7 (route E7-F), final form**: a piece length `Tp = 2` and a slow-correction role threshold
`qS` with the slow-cap interface at the exponents `slowExpF = (2, 3, 4, 5/2)` and the degree duty
`DegreeBelow (281/1000) (9876/719)`. -/
theorem slowCapsInterface :
    ∃ (Tp : ℝ) (qS : ℝ → ℝ → Caps → ℝ), 2 ≤ Tp ∧ SlowCapsInterface Tp slowExpF qS ∧
      DegreeBelow (281 / 1000) (9876 / 719) slowExpF qS :=
  ⟨2, qS, le_rfl, slowCapsInterface_of_threshold, slow_degree⟩

end OVNS.Quant

end
