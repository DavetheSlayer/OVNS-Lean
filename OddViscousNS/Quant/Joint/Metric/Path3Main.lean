import OddViscousNS.Quant.Joint.Metric.Path3

/-!
# The energy identity on the actual path: three leaves, the sum (step J5, node N13, part 2)

`Fam3.identity`: for a family of three-leaf blocks with the size `Bd`, the form on the actual path is
absolutely continuous, with the integrand (source + five insertions) in `L¹`, at `s = 1, 2`.
`ρ₃ = (L + P₁ + P₂ + P₃)/Σ` absorbs the derivative of the insertions, as in `PathForm.lean`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (integral_tsum_deriv_ae slow_c3_integrable fast_h2_law ae_inH3_split)

noncomputable section

namespace OVNS.Quant.Metric

/-- The ratio of a block. -/
def rho₃ (x : I4) : ℝ := (absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2) / Hx₃ x

lemma Hx₃_pos {x : I4} (hx : Act₃ x) : 0 < Hx₃ x := by
  have hj : inJ x ≠ 0 := fun h => hx.2.2.2 (by rw [h]; rfl)
  have h1 := one_le_absSq hj
  have h2 := absSq_nonneg x.1
  have h3 := absSq_nonneg x.2.1
  have h4 := absSq_nonneg x.2.2.1
  have h5 := absSq_nonneg x.2.2.2
  simp only [Hx₃]
  linarith

lemma rho₃_nonneg (x : I4) : 0 ≤ rho₃ x := by
  have h1 := absk_nonneg x.1
  have h2 := absk_nonneg x.2.1
  have h3 := absk_nonneg x.2.2.1
  have h4 := absk_nonneg x.2.2.2
  have h5 : 0 ≤ Hx₃ x := by
    have := absSq_nonneg x.1
    have := absSq_nonneg (inJ x)
    have := absSq_nonneg x.2.1
    have := absSq_nonneg x.2.2.1
    have := absSq_nonneg x.2.2.2
    simp only [Hx₃]
    linarith
  unfold rho₃
  positivity

/-- `L + P₁ + P₂ + P₃ ≤ Σ` and the square bound. -/
lemma sum_facts (x : I4) :
    (absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2) ≤ Hx₃ x ∧
      (absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2) ^ 2 ≤ 4 * Hx₃ x := by
  have h1 := absk_le_absSq x.1
  have h2 := absk_le_absSq x.2.1
  have h3 := absk_le_absSq x.2.2.1
  have h4 := absk_le_absSq x.2.2.2
  have h5 := absSq_nonneg (inJ x)
  constructor
  · simp only [Hx₃]
    linarith
  · simp only [Hx₃, ← absk_sq x.1, ← absk_sq x.2.1, ← absk_sq x.2.2.1, ← absk_sq x.2.2.2]
    set a := absk x.1
    set b := absk x.2.1
    set c := absk x.2.2.1
    set d := absk x.2.2.2
    nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
      sq_nonneg (b - d), sq_nonneg (c - d), h5]

/-- The lengths against the ratio. -/
lemma len_rho {x : I4} (hx : Act₃ x) {Y : ℝ}
    (hY : Y ≤ absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2) : Y * rho₃ x ≤ 4 := by
  have hH := Hx₃_pos hx
  obtain ⟨-, h2⟩ := sum_facts x
  unfold rho₃
  rw [mul_div_assoc', div_le_iff₀ hH]
  have h3 := rho₃_nonneg x
  have h4 := add_nonneg (add_nonneg (add_nonneg (absk_nonneg x.1) (absk_nonneg x.2.1))
    (absk_nonneg x.2.2.1)) (absk_nonneg x.2.2.2)
  have := mul_le_mul_of_nonneg_right hY h4
  nlinarith only [this, h2]

lemma inJ_le (x : I4) : absk (inJ x) ≤ absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2 := by
  have h1 := absk_sub_le x.1 x.2.1
  have h2 := absk_sub_le (x.1 - x.2.1) x.2.2.1
  have h3 := absk_sub_le (x.1 - x.2.1 - x.2.2.1) x.2.2.2
  simp only [inJ]
  linarith

namespace Fam3

variable {𝔉 : Fam3} {r : ℝ} {K : ℝ} {x : I4} {G F t v w : V3} {τ : ℝ}

lemma norm_T_le (hB : 𝔉.Bd K) (hx : Act₃ x) :
    ‖𝔉.T r x G F t v w τ‖ ≤
      4 * K * (‖G‖ * ‖F‖ * (‖t‖ * ‖v‖ * ‖w‖) * rho₃ x * E3 x) := by
  have hH := Hx₃_pos hx
  refine (norm_inner_apply_le _ _ _).trans ?_
  have h1 := norm_outerInv_le hH r x.1 (inJ x) (𝔉.Sr x τ t v w)
  have h2 := hB.source x hx τ t v w
  have hK := hB.K0
  have hE := E3_nonneg x
  calc _ ≤ ‖G‖ * ‖F‖ * (4 / Hx₃ x * (K * (absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2) *
        (‖t‖ * ‖v‖ * ‖w‖) * E3 x)) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by
        simp only [rho₃]
        ring

lemma norm_srcT_le (hB : 𝔉.Bd K) (hx : Act₃ x) :
    ‖𝔉.srcT x G F t v w τ‖ ≤ K * (‖G‖ * ‖F‖ * (‖t‖ * ‖v‖ * ‖w‖) *
      (absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2) * E3 x) := by
  refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
  have h1 := hB.source x hx τ t v w
  have h2 := norm_leray_le x.1 (𝔉.Sr x τ t v w (leray (inJ x) F))
  have h3 : ‖𝔉.Sr x τ t v w (leray (inJ x) F)‖ ≤ ‖𝔉.Sr x τ t v w‖ * ‖F‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_leray_le _ _) (norm_nonneg _))
  have h4 := h3.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg F))
  calc _ ≤ ‖G‖ * (K * (absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2) *
        (‖t‖ * ‖v‖ * ‖w‖) * E3 x * ‖F‖) := mul_le_mul_of_nonneg_left (h2.trans h4) (norm_nonneg _)
    _ = _ := by ring

/-- The derivative family. -/
def rhsT (𝔉 : Fam3) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) (x : I4) : ℂ :=
  𝔉.srcT x (zp s r g y u x.1) (zp s r g y u (inJ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2.1)
      (Sp r g y u x.2.2.2) (r * u) +
    𝔉.T r x (Nzp s r g y u x.1) (zp s r g y u (inJ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2.1)
      (Sp r g y u x.2.2.2) (r * u) +
    𝔉.T r x (zp s r g y u x.1) (Nzp s r g y u (inJ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2.1)
      (Sp r g y u x.2.2.2) (r * u) +
    𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ x)) (slowNL r g y u x.2.1) (Sp r g y u x.2.2.1)
      (Sp r g y u x.2.2.2) (r * u) +
    𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ x)) (Sp r g y u x.2.1) (slowNL r g y u x.2.2.1)
      (Sp r g y u x.2.2.2) (r * u) +
    𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2.1)
      (slowNL r g y u x.2.2.2) (r * u)

/-- The derivative. -/
def rhs (𝔉 : Fam3) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  𝔉.src (r * u) (Sp r g y u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (Sp r g y u) (Nzp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (Nzp s r g y u) +
    𝔉.form r (r * u) (slowNL r g y u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (slowNL r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (slowNL r g y u) (zp s r g y u) (zp s r g y u)

/-- The value along the solution. -/
def val (𝔉 : Fam3) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u)

/-- The majorant of the derivative family. -/
def maj (K : ℝ) (z N Ns S : Field) (x : I4) : ℝ :=
  K * (Phi₃ (gr z) (nrm z) (nrm S) (nrm S) (nrm S) x * E3 x +
      Phi₃ (nrm z) (nrm z) (gr S) (nrm S) (nrm S) x * E3 x +
      Phi₃ (nrm z) (nrm z) (nrm S) (gr S) (nrm S) x * E3 x +
      Phi₃ (nrm z) (nrm z) (nrm S) (nrm S) (gr S) x * E3 x) +
    16 * K * (Phi₃ (gr N) (nrm z) (nrm S) (nrm S) (nrm S) x * E3 x +
      Phi₃ (nrm z) (gr N) (nrm S) (nrm S) (nrm S) x * E3 x +
      Phi₃ (nrm z) (nrm z) (dv Ns) (nrm S) (nrm S) x * E3 x +
      Phi₃ (nrm z) (nrm z) (nrm S) (dv Ns) (nrm S) x * E3 x +
      Phi₃ (nrm z) (nrm z) (nrm S) (nrm S) (dv Ns) x * E3 x)

/-- `SB` of the majorant. -/
lemma sb_maj {z N Ns S : Field} (hK : 0 ≤ K) (hz : Summable fun k => ‖z k‖ ^ 2) (hz1 : InH 1 z)
    (hN : InH 1 N) (hNs : InH 1 Ns) (hS : MZ 3 S) :
    SB (maj K z N Ns S) (K * (hnorm 1 z * l2n z * cls3 (wiener S) (wiener S) (wiener S)
          (hnorm 2 S) (hnorm 2 S) (hnorm 2 S) +
        l2n z * l2n z * cls3 (c4 * hnorm 3 S) (wiener S) (wiener S) (hnorm 3 S) (hnorm 2 S)
          (hnorm 2 S) +
        l2n z * l2n z * cls3 (wiener S) (c4 * hnorm 3 S) (wiener S) (hnorm 2 S) (hnorm 3 S)
          (hnorm 2 S) +
        l2n z * l2n z * cls3 (wiener S) (wiener S) (c4 * hnorm 3 S) (hnorm 2 S) (hnorm 2 S)
          (hnorm 3 S)) +
      16 * K * (hnorm 1 N * l2n z * cls3 (wiener S) (wiener S) (wiener S) (hnorm 2 S) (hnorm 2 S)
          (hnorm 2 S) +
        l2n z * hnorm 1 N * cls3 (wiener S) (wiener S) (wiener S) (hnorm 2 S) (hnorm 2 S)
          (hnorm 2 S) +
        l2n z * l2n z * cls3 (c4 * hnorm 1 Ns) (wiener S) (wiener S) (hnorm 1 Ns) (hnorm 2 S)
          (hnorm 2 S) +
        l2n z * l2n z * cls3 (wiener S) (c4 * hnorm 1 Ns) (wiener S) (hnorm 2 S) (hnorm 1 Ns)
          (hnorm 2 S) +
        l2n z * l2n z * cls3 (wiener S) (wiener S) (c4 * hnorm 1 Ns) (hnorm 2 S) (hnorm 2 S)
          (hnorm 1 Ns))) := by
  have hS2 : MZ 2 S := hS.mono' (by norm_num)
  have α := l2B_nrm hz
  have α1 := l2B_gr hz1
  have N1 := l2B_gr hN
  have W := l1B_nrm hS2.inH
  have U := l2B_up hS2.inH
  have W1 := l1B_gr hS
  have U1 := l2B_up_gr hS
  have D1 := l1B_dv hNs
  have D2 := l2B_up_dv hNs
  have t1 := pos3_E3 α1 α W W W U U U
  have t2 := pos3_E3 α α W1 W W U1 U U
  have t3 := pos3_E3 α α W W1 W U U1 U
  have t4 := pos3_E3 α α W W W1 U U U1
  have t5 := pos3_E3 N1 α W W W U U U
  have t6 := pos3_E3 α N1 W W W U U U
  have t7 := pos3_E3 α α D1 W W D2 U U
  have t8 := pos3_E3 α α W D1 W U D2 U
  have t9 := pos3_E3 α α W W D1 U U D2
  exact ((((t1.add t2).add t3).add t4).const_mul hK).add
    ((((((t5.add t6).add t7).add t8).add t9)).const_mul (by positivity))

variable {f₀ g₀ h₀ G₀ F₀ : Field}

/-- A term vanishes off the active labels. -/
lemma T_form_le (hf : PiS f₀ = f₀) (hg : PiS g₀ = g₀) (hh : PiS h₀ = h₀) (hF : PiF F₀ = F₀)
    {B : I4 → ℝ} (hB0 : ∀ x, 0 ≤ B x)
    (h : ∀ x, Act₃ x →
      ‖𝔉.T r x (G₀ x.1) (F₀ (inJ x)) (f₀ x.2.1) (g₀ x.2.2.1) (h₀ x.2.2.2) τ‖ ≤ B x) (x : I4) :
    ‖𝔉.T r x (G₀ x.1) (F₀ (inJ x)) (f₀ x.2.1) (g₀ x.2.2.1) (h₀ x.2.2.2) τ‖ ≤ B x := by
  by_cases h1 : x.2.1 2 = 0
  · by_cases h2 : x.2.2.1 2 = 0
    · by_cases h3 : x.2.2.2 2 = 0
      · by_cases hj : inJ x 2 = 0
        · rw [fast_zero hF hj, T_zero_F, norm_zero]
          exact hB0 x
        · exact h x ⟨h1, h2, h3, hj⟩
      · rw [slow_zero hh h3, T_zero₃, norm_zero]
        exact hB0 x
    · rw [slow_zero hg h2, T_zero₂, norm_zero]
      exact hB0 x
  · rw [slow_zero hf h1, T_zero₁, norm_zero]
    exact hB0 x

/-- A source term vanishes off the active labels. -/
lemma srcT_form_le (hf : PiS f₀ = f₀) (hg : PiS g₀ = g₀) (hh : PiS h₀ = h₀) (hF : PiF F₀ = F₀)
    {B : I4 → ℝ} (hB0 : ∀ x, 0 ≤ B x)
    (h : ∀ x, Act₃ x →
      ‖𝔉.srcT x (G₀ x.1) (F₀ (inJ x)) (f₀ x.2.1) (g₀ x.2.2.1) (h₀ x.2.2.2) τ‖ ≤ B x) (x : I4) :
    ‖𝔉.srcT x (G₀ x.1) (F₀ (inJ x)) (f₀ x.2.1) (g₀ x.2.2.1) (h₀ x.2.2.2) τ‖ ≤ B x := by
  by_cases h1 : x.2.1 2 = 0
  · by_cases h2 : x.2.2.1 2 = 0
    · by_cases h3 : x.2.2.2 2 = 0
      · by_cases hj : inJ x 2 = 0
        · rw [fast_zero hF hj, srcT_zero_F, norm_zero]
          exact hB0 x
        · exact h x ⟨h1, h2, h3, hj⟩
      · rw [slow_zero hh h3, srcT_zero₃, norm_zero]
        exact hB0 x
    · rw [slow_zero hg h2, srcT_zero₂, norm_zero]
      exact hB0 x
  · rw [slow_zero hf h1, srcT_zero₁, norm_zero]
    exact hB0 x

lemma Phi₃_E3_nonneg {α β f₁ f₂ f₃ : Mode → ℝ} (hα : ∀ k, 0 ≤ α k) (hβ : ∀ k, 0 ≤ β k)
    (h1 : ∀ k, 0 ≤ f₁ k) (h2 : ∀ k, 0 ≤ f₂ k) (h3 : ∀ k, 0 ≤ f₃ k) (x : I4) :
    0 ≤ Phi₃ α β f₁ f₂ f₃ x * E3 x :=
  mul_nonneg (Phi₃_nonneg hα hβ h1 h2 h3 x) (E3_nonneg x)

variable {μ φ : ℝ} {g : Field} {y : ℝ → Field}

/-- **The six terms of the derivative family are dominated** at a time. -/
lemma terms_le (hB : 𝔉.Bd K) {s : ℕ} (hs : s = 1 ∨ s = 2) (u : ℝ)
    (hNs0 : slowNL r g y u 0 = 0) (x : I4) :
    ‖𝔉.srcT x (zp s r g y u x.1) (zp s r g y u (inJ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2.1)
        (Sp r g y u x.2.2.2) (r * u)‖ ≤ maj K (zp s r g y u) (fastNL r g y u) (slowNL r g y u)
          (Sp r g y u) x ∧
    ‖𝔉.T r x (Nzp s r g y u x.1) (zp s r g y u (inJ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2.1)
        (Sp r g y u x.2.2.2) (r * u)‖ ≤ maj K (zp s r g y u) (fastNL r g y u) (slowNL r g y u)
          (Sp r g y u) x ∧
    ‖𝔉.T r x (zp s r g y u x.1) (Nzp s r g y u (inJ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2.1)
        (Sp r g y u x.2.2.2) (r * u)‖ ≤ maj K (zp s r g y u) (fastNL r g y u) (slowNL r g y u)
          (Sp r g y u) x ∧
    ‖𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ x)) (slowNL r g y u x.2.1) (Sp r g y u x.2.2.1)
        (Sp r g y u x.2.2.2) (r * u)‖ ≤ maj K (zp s r g y u) (fastNL r g y u) (slowNL r g y u)
          (Sp r g y u) x ∧
    ‖𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ x)) (Sp r g y u x.2.1) (slowNL r g y u x.2.2.1)
        (Sp r g y u x.2.2.2) (r * u)‖ ≤ maj K (zp s r g y u) (fastNL r g y u) (slowNL r g y u)
          (Sp r g y u) x ∧
    ‖𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2.1)
        (slowNL r g y u x.2.2.2) (r * u)‖ ≤ maj K (zp s r g y u) (fastNL r g y u) (slowNL r g y u)
          (Sp r g y u) x := by
  set z := zp s r g y u with hz
  set N := fastNL r g y u with hN
  set Ns := slowNL r g y u with hNs
  set S := Sp r g y u with hS
  have hSs : PiS S = S := Fam.PiS_Sp r g y u
  have hNss : PiS Ns = Ns := PiS_slowNL u
  have hzf : PiF z = z := Fam.PiF_zp s r g y u
  have hNz : PiF (Nzp s r g y u) = Nzp s r g y u := Fam.PiF_Nzp s r g y u
  have hK := hB.K0
  have nz : ∀ k, 0 ≤ nrm z k := fun _ => norm_nonneg _
  have nS : ∀ k, 0 ≤ nrm S k := fun _ => norm_nonneg _
  have gz := gr_nonneg z
  have gS := gr_nonneg S
  have gN := gr_nonneg N
  have dN := dv_nonneg Ns
  have hrho : ∀ x, Act₃ x → ∀ {Y : ℝ},
      Y ≤ absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2 → Y * (rho₃ x / 2) ≤ 2 :=
    fun x hx Y h1 => by
      have := len_rho hx h1
      linarith
  have hrho2 : ∀ x, Act₃ x → rho₃ x / 2 ≤ 2 := fun x hx => by
    have hj : inJ x ≠ 0 := fun h => hx.2.2.2 (by rw [h]; rfl)
    have h1 := one_le_absk hj
    have h2 := len_rho hx (inJ_le x)
    have h3 := rho₃_nonneg x
    nlinarith only [h1, h2, h3]
  have sum0 : ∀ x : I4, 0 ≤ absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2 := fun x => by
    have h1 := absk_nonneg x.1
    have h2 := absk_nonneg x.2.1
    have h3 := absk_nonneg x.2.2.1
    have h4 := absk_nonneg x.2.2.2
    positivity
  have lenL : ∀ x : I4, absk x.1 ≤ absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2 := fun x => by
    have h2 := absk_nonneg x.2.1
    have h3 := absk_nonneg x.2.2.1
    have h4 := absk_nonneg x.2.2.2
    linarith
  have lenA : ∀ x : I4, absk x.2.1 ≤ absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2 :=
    fun x => by
    have h2 := absk_nonneg x.1
    have h3 := absk_nonneg x.2.2.1
    have h4 := absk_nonneg x.2.2.2
    linarith
  have lenB : ∀ x : I4, absk x.2.2.1 ≤ absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2 :=
    fun x => by
    have h2 := absk_nonneg x.1
    have h3 := absk_nonneg x.2.1
    have h4 := absk_nonneg x.2.2.2
    linarith
  have lenC : ∀ x : I4, absk x.2.2.2 ≤ absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2 :=
    fun x => by
    have h2 := absk_nonneg x.1
    have h3 := absk_nonneg x.2.1
    have h4 := absk_nonneg x.2.2.1
    linarith
  have t1 : ‖𝔉.srcT x (z x.1) (z (inJ x)) (S x.2.1) (S x.2.2.1) (S x.2.2.2) (r * u)‖ ≤
      K * (Phi₃ (gr z) (nrm z) (nrm S) (nrm S) (nrm S) x * E3 x +
        Phi₃ (nrm z) (nrm z) (gr S) (nrm S) (nrm S) x * E3 x +
        Phi₃ (nrm z) (nrm z) (nrm S) (gr S) (nrm S) x * E3 x +
        Phi₃ (nrm z) (nrm z) (nrm S) (nrm S) (gr S) x * E3 x) := by
    refine srcT_form_le hSs hSs hSs hzf (fun x => mul_nonneg hK (add_nonneg (add_nonneg (add_nonneg
      (Phi₃_E3_nonneg gz nz nS nS nS x) (Phi₃_E3_nonneg nz nz gS nS nS x))
      (Phi₃_E3_nonneg nz nz nS gS nS x)) (Phi₃_E3_nonneg nz nz nS nS gS x))) (fun x hx => ?_) x
    refine (norm_srcT_le hB hx).trans (le_of_eq ?_)
    simp only [Phi₃, nrm, gr]
    ring
  have t2 : ‖𝔉.T r x (Nzp s r g y u x.1) (z (inJ x)) (S x.2.1) (S x.2.2.1) (S x.2.2.2) (r * u)‖ ≤ 16 * K * (Phi₃ (gr N) (nrm z) (nrm S) (nrm S) (nrm S) x * E3 x) := by
    refine T_form_le hSs hSs hSs hzf (fun x => mul_nonneg (by positivity) (Phi₃_E3_nonneg gN nz nS nS nS x)) (fun x hx => ?_) x
    refine (norm_T_le hB hx).trans ?_
    have h1 := zOf_ratio hs N x.1 (hrho2 x hx) (hrho x hx (lenL x))
    have hE := E3_nonneg x
    have hR : 0 ≤ (‖z (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖)) * E3 x := by positivity
    have e1 : 4 * K * (‖Nzp s r g y u x.1‖ * ‖z (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖) * rho₃ x * E3 x) = 8 * K * (‖Nzp s r g y u x.1‖ * (rho₃ x / 2) * ((‖z (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖)) * E3 x)) := by
      ring
    have e2 : 16 * K * (Phi₃ (gr N) (nrm z) (nrm S) (nrm S) (nrm S) x * E3 x) = 8 * K * ((2 * gr N x.1) * ((‖z (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖)) * E3 x)) := by
      simp only [Phi₃, nrm]
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hR) (by positivity)
  have t3 : ‖𝔉.T r x (z x.1) (Nzp s r g y u (inJ x)) (S x.2.1) (S x.2.2.1) (S x.2.2.2) (r * u)‖ ≤ 16 * K * (Phi₃ (nrm z) (gr N) (nrm S) (nrm S) (nrm S) x * E3 x) := by
    refine T_form_le hSs hSs hSs hNz (fun x => mul_nonneg (by positivity) (Phi₃_E3_nonneg nz gN nS nS nS x)) (fun x hx => ?_) x
    refine (norm_T_le hB hx).trans ?_
    have h1 := zOf_ratio hs N (inJ x) (hrho2 x hx) (hrho x hx (inJ_le x))
    have hE := E3_nonneg x
    have hR : 0 ≤ (‖z x.1‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖)) * E3 x := by positivity
    have e1 : 4 * K * (‖z x.1‖ * ‖Nzp s r g y u (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖) * rho₃ x * E3 x) = 8 * K * (‖Nzp s r g y u (inJ x)‖ * (rho₃ x / 2) * ((‖z x.1‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖)) * E3 x)) := by
      ring
    have e2 : 16 * K * (Phi₃ (nrm z) (gr N) (nrm S) (nrm S) (nrm S) x * E3 x) = 8 * K * ((2 * gr N (inJ x)) * ((‖z x.1‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖)) * E3 x)) := by
      simp only [Phi₃, nrm]
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hR) (by positivity)
  have t4 : ‖𝔉.T r x (z x.1) (z (inJ x)) (Ns x.2.1) (S x.2.2.1) (S x.2.2.2) (r * u)‖ ≤ 16 * K * (Phi₃ (nrm z) (nrm z) (dv Ns) (nrm S) (nrm S) x * E3 x) := by
    refine T_form_le hNss hSs hSs hzf (fun x => mul_nonneg (by positivity) (Phi₃_E3_nonneg nz nz dN nS nS x)) (fun x hx => ?_) x
    refine (norm_T_le hB hx).trans ?_
    have h1 := dv_ratio hNs0 x.2.1 (hrho x hx (lenA x))
    have hE := E3_nonneg x
    have hR : 0 ≤ (‖z x.1‖ * ‖z (inJ x)‖ * (‖S x.2.2.1‖ * ‖S x.2.2.2‖)) * E3 x := by positivity
    have e1 : 4 * K * (‖z x.1‖ * ‖z (inJ x)‖ * (‖Ns x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖) * rho₃ x * E3 x) = 8 * K * (‖Ns x.2.1‖ * (rho₃ x / 2) * ((‖z x.1‖ * ‖z (inJ x)‖ * (‖S x.2.2.1‖ * ‖S x.2.2.2‖)) * E3 x)) := by
      ring
    have e2 : 16 * K * (Phi₃ (nrm z) (nrm z) (dv Ns) (nrm S) (nrm S) x * E3 x) = 8 * K * ((2 * dv Ns x.2.1) * ((‖z x.1‖ * ‖z (inJ x)‖ * (‖S x.2.2.1‖ * ‖S x.2.2.2‖)) * E3 x)) := by
      simp only [Phi₃, nrm]
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hR) (by positivity)
  have t5 : ‖𝔉.T r x (z x.1) (z (inJ x)) (S x.2.1) (Ns x.2.2.1) (S x.2.2.2) (r * u)‖ ≤ 16 * K * (Phi₃ (nrm z) (nrm z) (nrm S) (dv Ns) (nrm S) x * E3 x) := by
    refine T_form_le hSs hNss hSs hzf (fun x => mul_nonneg (by positivity) (Phi₃_E3_nonneg nz nz nS dN nS x)) (fun x hx => ?_) x
    refine (norm_T_le hB hx).trans ?_
    have h1 := dv_ratio hNs0 x.2.2.1 (hrho x hx (lenB x))
    have hE := E3_nonneg x
    have hR : 0 ≤ (‖z x.1‖ * ‖z (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.2‖)) * E3 x := by positivity
    have e1 : 4 * K * (‖z x.1‖ * ‖z (inJ x)‖ * (‖S x.2.1‖ * ‖Ns x.2.2.1‖ * ‖S x.2.2.2‖) * rho₃ x * E3 x) = 8 * K * (‖Ns x.2.2.1‖ * (rho₃ x / 2) * ((‖z x.1‖ * ‖z (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.2‖)) * E3 x)) := by
      ring
    have e2 : 16 * K * (Phi₃ (nrm z) (nrm z) (nrm S) (dv Ns) (nrm S) x * E3 x) = 8 * K * ((2 * dv Ns x.2.2.1) * ((‖z x.1‖ * ‖z (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.2‖)) * E3 x)) := by
      simp only [Phi₃, nrm]
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hR) (by positivity)
  have t6 : ‖𝔉.T r x (z x.1) (z (inJ x)) (S x.2.1) (S x.2.2.1) (Ns x.2.2.2) (r * u)‖ ≤ 16 * K * (Phi₃ (nrm z) (nrm z) (nrm S) (nrm S) (dv Ns) x * E3 x) := by
    refine T_form_le hSs hSs hNss hzf (fun x => mul_nonneg (by positivity) (Phi₃_E3_nonneg nz nz nS nS dN x)) (fun x hx => ?_) x
    refine (norm_T_le hB hx).trans ?_
    have h1 := dv_ratio hNs0 x.2.2.2 (hrho x hx (lenC x))
    have hE := E3_nonneg x
    have hR : 0 ≤ (‖z x.1‖ * ‖z (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖)) * E3 x := by positivity
    have e1 : 4 * K * (‖z x.1‖ * ‖z (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖Ns x.2.2.2‖) * rho₃ x * E3 x) = 8 * K * (‖Ns x.2.2.2‖ * (rho₃ x / 2) * ((‖z x.1‖ * ‖z (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖)) * E3 x)) := by
      ring
    have e2 : 16 * K * (Phi₃ (nrm z) (nrm z) (nrm S) (nrm S) (dv Ns) x * E3 x) = 8 * K * ((2 * dv Ns x.2.2.2) * ((‖z x.1‖ * ‖z (inJ x)‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖)) * E3 x)) := by
      simp only [Phi₃, nrm]
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hR) (by positivity)
  have p1 := Phi₃_E3_nonneg gz nz nS nS nS x
  have p2 := Phi₃_E3_nonneg nz nz gS nS nS x
  have p3 := Phi₃_E3_nonneg nz nz nS gS nS x
  have p4 := Phi₃_E3_nonneg nz nz nS nS gS x
  have p5 := Phi₃_E3_nonneg gN nz nS nS nS x
  have p6 := Phi₃_E3_nonneg nz gN nS nS nS x
  have p7 := Phi₃_E3_nonneg nz nz dN nS nS x
  have p8 := Phi₃_E3_nonneg nz nz nS dN nS x
  have p9 := Phi₃_E3_nonneg nz nz nS nS dN x
  have q1 := mul_nonneg hK (add_nonneg (add_nonneg (add_nonneg p1 p2) p3) p4)
  have h16 : 0 ≤ 16 * K := by positivity
  have q5 := mul_nonneg h16 p5
  have q6 := mul_nonneg h16 p6
  have q7 := mul_nonneg h16 p7
  have q8 := mul_nonneg h16 p8
  have q9 := mul_nonneg h16 p9
  simp only [maj]
  rw [mul_add (16 * K), mul_add (16 * K), mul_add (16 * K), mul_add (16 * K)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine t1.trans ?_
    linarith only [q5, q6, q7, q8, q9]
  · refine t2.trans ?_
    linarith only [q1, q6, q7, q8, q9]
  · refine t3.trans ?_
    linarith only [q1, q5, q7, q8, q9]
  · refine t4.trans ?_
    linarith only [q1, q5, q6, q8, q9]
  · refine t5.trans ?_
    linarith only [q1, q5, q6, q7, q9]
  · refine t6.trans ?_
    linarith only [q1, q5, q6, q7, q8]

end Fam3

end OVNS.Quant.Metric

end
