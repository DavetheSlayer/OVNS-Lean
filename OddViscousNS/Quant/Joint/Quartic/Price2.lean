import OddViscousNS.Quant.Joint.Quartic.Scalar

/-!
# The prices of `C_{4,2}` (step J5, node N11)

J3-v2 §4.  With `κ = kap2 r = 3·2¹⁴ √𝔐_P(q)/q`, `b = ‖F‖₂`, `c_F = ‖F‖₃`:

* `val_two_le`: `|Q₄| ≤ κ B L b²`;
* `rem_two_le`: `|Rem| ≤ κ (‖N_S‖₂ L b² + B L_h(N_F) b² + 2 B L ‖N_F‖₂ b)`;
* `Co`: the coefficients, `Co.Mm`, `Co.Cc`, `Co.Cy`, `Co.Ga`: the multiplier of `b²`, the coefficient of
  `c_F²`, of `c_y c_F`, and the genuine coefficient of `c_F`, the four items of J3-v2 §4;
* `rem_alg`, `rem_two_caps`: `|Rem| ≤ κ (Mm b² + Cc c_F² + Cy c_y c_F + Ga c_F)`.

The three summands of `Cy` are, in the order of J3-v2, `B y A₂` (`U R² D⁻¹ y`, inner fast), `2 B L A₁`
(`U² R²`, exterior fast), `L y A₃` (`U W y`, slow; `U R y` there: see `Source.lean`).
-/

open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- `‖F‖₂ ≤ ‖F‖₃`, for mean-zero `F`. -/
lemma hnorm_mono_fast {F : Field} (hF3 : InH 3 F) (_hF : Adm 2 F) : hnorm 2 F ≤ hnorm 3 F :=
  hnorm_mono (by norm_num) hF3

/-- `κ = C P(q)/q`, with the literal constant. -/
def kap2 (r : ℝ) : ℝ := 2 ^ 14 / |r| * (3 * Real.sqrt (MomP |r|))

lemma kap2_nonneg (r : ℝ) : 0 ≤ kap2 r := by
  unfold kap2
  positivity

/-- **The static bound of the quartic**, weight two. -/
theorem val_two_le (hr : r ≠ 0) (h : ActualSol μ φ r g y Ty) {u L : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hL : LhB (nrm (Fp r g y u)) L) :
    ‖val4 2 r g y u‖ ≤ kap2 r *
      (hnorm 2 (Sp r g y u) * L * hnorm 2 (Fp r g y u) ^ 2) := by
  have hF := Fp_adm h hu huT
  have hS := Sp_adm h hu huT
  refine (norm_Q4F_two_le hr (slots_val r g y u) hS.inH hL hF.inH hF.inH (r * u)).trans
    (le_of_eq ?_)
  simp only [kap2]
  ring

/-- **The four insertions**, weight two. -/
theorem rem_two_le (hr : r ≠ 0) (h : ActualSol μ φ r g y Ty) {u L Ln : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hNF : InH 2 (fastNL r g y u)) (hNS : InH 2 (slowNL r g y u))
    (hL : LhB (nrm (Fp r g y u)) L) (hLn : LhB (nrm (fastNL r g y u)) Ln) :
    ‖rem4 2 r g y u‖ ≤ kap2 r *
      (hnorm 2 (slowNL r g y u) * L * hnorm 2 (Fp r g y u) ^ 2 +
        hnorm 2 (Sp r g y u) * Ln * hnorm 2 (Fp r g y u) ^ 2 +
        2 * (hnorm 2 (Sp r g y u) * L * hnorm 2 (fastNL r g y u) * hnorm 2 (Fp r g y u))) := by
  have hF := Fp_adm h hu huT
  have hS := Sp_adm h hu huT
  have t1 := norm_Q4F_two_le hr (slots_S r g y u) hNS hL hF.inH hF.inH (r * u)
  have t2 := norm_Q4F_two_le hr (slots_W r g y u) hS.inH hLn hF.inH hF.inH (r * u)
  have t3 := norm_Q4F_two_le hr (slots_U r g y u) hS.inH hL hNF hF.inH (r * u)
  have t4 := norm_Q4F_two_le hr (slots_V r g y u) hS.inH hL hF.inH hNF (r * u)
  unfold rem4
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4) |>.trans (le_of_eq ?_)
  simp only [kap2]
  ring

/-- The parameters of the weight-two prices. -/
structure Co where
  /-- The fibre norm of `F`. -/
  L : ℝ
  /-- `b_F ≤ y`. -/
  y : ℝ
  /-- `b_S ≤ B`. -/
  B : ℝ
  /-- `𝒜(S) ≤ W`. -/
  W : ℝ
  /-- The height of the slow split. -/
  D : ℝ
  /-- `√(9 + 8 ln D)`. -/
  Lg : ℝ
  /-- The coefficient of `c_F` in the low and purefast pieces. -/
  P₀ : ℝ
  /-- `16 c_I √(ab)`. -/
  Cp : ℝ
  /-- `64 c₄ φ/q`. -/
  E : ℝ
  /-- `64 c₄ φ²/q²`. -/
  G : ℝ
  /-- The force. -/
  φ : ℝ

namespace Co

/-- All the parameters are nonnegative, and `D > 0`. -/
structure Nn (c : Co) : Prop where
  L : 0 ≤ c.L
  y : 0 ≤ c.y
  B : 0 ≤ c.B
  W : 0 ≤ c.W
  D : 0 < c.D
  Lg : 0 ≤ c.Lg
  P₀ : 0 ≤ c.P₀
  Cp : 0 ≤ c.Cp
  E : 0 ≤ c.E
  G : 0 ≤ c.G
  φ : 0 ≤ c.φ

variable (c : Co)

/-- The coefficient of `c_S` in `‖N_F‖₂`. -/
def A₁ : ℝ := 20 * c.L + c.E

/-- The coefficient of `c_S` in `L_h(N_F)`. -/
def A₂ : ℝ := 100 * c.L / c.D + 5 * c.E

/-- The coefficient of `c_S` in `‖N_S‖₂`. -/
def A₃ : ℝ := 16 * c.W + c.E

/-- The coefficient of `c_F` in the rest. -/
def P₁ : ℝ := c.P₀ + c.E

/-- **The multiplier of `b²`**: `20 L Lg B²`, J3-v2's `U R⁴ L(R)`. -/
def Mm : ℝ := 20 * c.L * c.Lg * c.B ^ 2

/-- **The coefficient of `c_F²`**: J3-v2's `R³(U + y) L(R)`. -/
def Cc : ℝ := c.L * c.y * (c.A₃ + c.Cp + c.E) + c.B * c.y * (c.A₂ + 5 * c.P₁) +
  2 * c.B * c.L * (c.A₁ + c.P₁)

/-- **The coefficient of `c_y c_F`**: slow, inner fast, exterior fast. -/
def Cy : ℝ := c.L * c.y * c.A₃ + c.B * c.y * c.A₂ + 2 * c.B * c.L * c.A₁

/-- **The genuine coefficient of `c_F`.** -/
def Ga : ℝ := c.L * c.y * (c.G + c.φ) + 5 * c.B * c.y * c.G + 2 * c.B * c.L * c.G

end Co

/-- **The algebra of the weight-two remainder.** -/
theorem rem_alg (c : Co) (hc : c.Nn) {b cF cy cS nS nF ρ W₁ B₀ : ℝ} (hb0 : 0 ≤ b) (hbF : b ≤ cF)
    (hby : b ≤ c.y) (hcy : 0 ≤ cy) (hcS : cS ≤ cy + cF / 128) (hBc : B₀ ≤ c.B) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ c.P₀ * cF + c.E * (cF + cS) + c.G) (hnS0 : 0 ≤ nS)
    (hnS : nS ≤ 16 * c.W * cS + c.Cp * cF + (c.E * (cF + cS) + c.G) + c.φ) (hnF0 : 0 ≤ nF)
    (hnF : nF ≤ 20 * (cS * c.L) + ρ) (hW₁0 : 0 ≤ W₁) (hW₁ : W₁ ≤ c.Lg * c.B + 5 / c.D * cS) :
    nS * c.L * b ^ 2 + B₀ * (20 * (W₁ * c.L) + Real.sqrt 17 * ρ) * b ^ 2 +
        2 * (B₀ * c.L * nF * b) ≤
      c.Mm * b ^ 2 + c.Cc * cF ^ 2 + c.Cy * cy * cF + c.Ga * cF := by
  have hL := hc.L
  have hE := hc.E
  have hD := hc.D
  have hG := hc.G
  have hφ := hc.φ
  have hP₀ := hc.P₀
  have hCp := hc.Cp
  have hW := hc.W
  have hF0 : 0 ≤ cF := hb0.trans hbF
  have hb2 : b ^ 2 ≤ c.y * cF := by
    rw [sq]
    exact mul_le_mul hby hbF hb0 hc.y
  have hcS' : cS ≤ cy + cF := by linarith
  have hA₁ : 0 ≤ c.A₁ := by unfold Co.A₁; positivity
  have hA₂ : 0 ≤ c.A₂ := by unfold Co.A₂; positivity
  have hA₃ : 0 ≤ c.A₃ := by unfold Co.A₃; positivity
  have hP₁ : 0 ≤ c.P₁ := by unfold Co.P₁; positivity
  -- the three directions
  have h1 : nS ≤ c.A₃ * cy + (c.A₃ + c.Cp + c.E) * cF + c.G + c.φ := by
    have := mul_le_mul_of_nonneg_left hcS' hA₃
    simp only [Co.A₃] at this ⊢
    nlinarith only [this, hnS]
  have h3 : nF ≤ c.A₁ * cy + (c.A₁ + c.P₁) * cF + c.G := by
    have := mul_le_mul_of_nonneg_left hcS' hA₁
    simp only [Co.A₁, Co.P₁] at this ⊢
    nlinarith only [this, hnF, hρ]
  have hs17 : Real.sqrt 17 ≤ 5 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h2 : 20 * (W₁ * c.L) + Real.sqrt 17 * ρ ≤ 20 * c.L * c.Lg * c.B + (c.A₂ * cy +
      (c.A₂ + 5 * c.P₁) * cF + 5 * c.G) := by
    have a1 : W₁ * c.L ≤ (c.Lg * c.B + 5 / c.D * cS) * c.L := mul_le_mul_of_nonneg_right hW₁ hL
    have a2 : Real.sqrt 17 * ρ ≤ 5 * ρ := mul_le_mul_of_nonneg_right hs17 hρ0
    have a3 := mul_le_mul_of_nonneg_left hcS' hA₂
    have e : c.A₂ * cS = 100 * (5 / c.D * cS * c.L) / 5 + 5 * c.E * cS := by
      simp only [Co.A₂]
      field_simp
    simp only [Co.P₁]
    nlinarith only [a1, a2, a3, e, hρ]
  set X₁ := c.A₃ * cy + (c.A₃ + c.Cp + c.E) * cF + c.G + c.φ with hX₁
  set X₂ := c.A₂ * cy + (c.A₂ + 5 * c.P₁) * cF + 5 * c.G with hX₂
  set X₃ := c.A₁ * cy + (c.A₁ + c.P₁) * cF + c.G with hX₃
  have hX₁0 : 0 ≤ X₁ := hnS0.trans h1
  have hX₃0 : 0 ≤ X₃ := hnF0.trans h3
  have hX₂0 : 0 ≤ X₂ := by
    simp only [hX₂]
    positivity
  have t1 : nS * c.L * b ^ 2 ≤ X₁ * c.L * (c.y * cF) :=
    mul_le_mul (mul_le_mul_of_nonneg_right h1 hL) hb2 (sq_nonneg b) (by positivity)
  have hLn0 : 0 ≤ 20 * (W₁ * c.L) + Real.sqrt 17 * ρ := by positivity
  have t2 : B₀ * (20 * (W₁ * c.L) + Real.sqrt 17 * ρ) * b ^ 2 ≤
      c.B * (20 * c.L * c.Lg * c.B + X₂) * b ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul hBc h2 hLn0 hc.B) (sq_nonneg b)
  have t2' : c.B * X₂ * b ^ 2 ≤ c.B * X₂ * (c.y * cF) :=
    mul_le_mul_of_nonneg_left hb2 (mul_nonneg hc.B hX₂0)
  have t3 : 2 * (B₀ * c.L * nF * b) ≤ 2 * (c.B * c.L * X₃ * cF) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hBc hL) h3 hnF0
      (mul_nonneg hc.B hL)) hbF hb0 (mul_nonneg (mul_nonneg hc.B hL) hX₃0)
  have e : c.Mm * b ^ 2 + c.Cc * cF ^ 2 + c.Cy * cy * cF + c.Ga * cF =
      X₁ * c.L * (c.y * cF) + (c.B * (20 * c.L * c.Lg * c.B) * b ^ 2 + c.B * X₂ * (c.y * cF)) +
        2 * (c.B * c.L * X₃ * cF) := by
    simp only [Co.Mm, Co.Cc, Co.Cy, Co.Ga, hX₁, hX₂, hX₃]
    ring
  rw [e]
  have e2 : c.B * (20 * c.L * c.Lg * c.B + X₂) * b ^ 2 =
      c.B * (20 * c.L * c.Lg * c.B) * b ^ 2 + c.B * X₂ * b ^ 2 := by ring
  linarith

/-- The bounds of one time. -/
structure At2 (c : Co) (r : ℝ) (g : Field) (y : ℝ → Field) (u cy M φ' : ℝ) : Prop where
  hL : LhB (nrm (Fp r g y u)) c.L
  hB : hnorm 2 (Sp r g y u) ≤ c.B
  hb : hnorm 2 (Fp r g y u) ≤ c.y
  hW : wiener (Sp r g y u) ≤ c.W
  hsup : slowSup r g y u ≤ M
  hCp : 16 * cI * Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) ≤ c.Cp
  hP₀ : 2 * CLow 2 * M + c.Cp ≤ c.P₀
  hE : 64 * c4 * φ' / |r| ≤ c.E
  hG : 64 * c4 * φ' ^ 2 / r ^ 2 ≤ c.G
  hφ : φ' ≤ c.φ
  hD : 1 ≤ c.D
  hLg : Real.sqrt (9 + 8 * Real.log c.D) ≤ c.Lg
  hcy : 0 ≤ cy
  hcS : hnorm 3 (Sp r g y u) ≤ cy + hnorm 3 (Fp r g y u) / 128

/-- **The remainder of `C_{4,2}` at an `H³` time**, J3-v2 §4: the four items. -/
theorem rem_two_caps (hr : r ≠ 0) (h : ActualSol μ φ r g y Ty) {u cy M : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u)) {c : Co}
    (hc : c.Nn) (hA : At2 c r g y u cy M φ) :
    ‖rem4 2 r g y u‖ ≤ kap2 r * (c.Mm * hnorm 2 (Fp r g y u) ^ 2 +
      c.Cc * hnorm 3 (Fp r g y u) ^ 2 + c.Cy * cy * hnorm 3 (Fp r g y u) +
      c.Ga * hnorm 3 (Fp r g y u)) := by
  have hS := Sp_adm h hu huT
  have hF := Fp_adm h hu huT
  have hS3m : MZ 3 (Sp r g y u) := ⟨hS3, hS.mean⟩
  obtain ⟨iR, bR⟩ := hnorm_two_fastRest h hr hu huT hF3 hS3 hA.hsup
  obtain ⟨iNF, bNF⟩ := hnorm_two_fastNL h hu huT iR hS3 hA.hL
  obtain ⟨iNS, bNS⟩ := hnorm_two_slowNL h hr hu huT hF3 hS3
  have hW₁ := l1B_gr_log hA.hD hS3m (Fam.PiS_Sp r g y u)
  have hLn := lhB_fastNL h hu huT iR hW₁ hA.hL
  have hb := rem_two_le hr h hu huT iNF iNS hA.hL hLn
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ (kap2_nonneg r))
  have hbF : hnorm 2 (Fp r g y u) ≤ hnorm 3 (Fp r g y u) := hnorm_mono_fast hF3 hF
  have hF30 := hnorm_nonneg 3 (Fp r g y u)
  have hS30 := hnorm_nonneg 3 (Sp r g y u)
  have hS20 := hnorm_nonneg 2 (Sp r g y u)
  have hsq := hc.Lg
  have hSq0 := Real.sqrt_nonneg (9 + 8 * Real.log c.D)
  have hcF : 0 ≤ c.Cp := hc.Cp
  have hW0 := wiener_nonneg (Sp r g y u)
  have ρle : hnorm 2 (fastRest r g y u) ≤ c.P₀ * hnorm 3 (Fp r g y u) +
      c.E * (hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) + c.G := by
    refine bR.trans ?_
    have h1 : 2 * CLow 2 * M + 16 * cI * Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) ≤
        c.P₀ := (by linarith [hA.hCp, hA.hP₀])
    have h2 := mul_le_mul_of_nonneg_right h1 hF30
    have h3 := mul_le_mul_of_nonneg_right hA.hE (by positivity : 0 ≤ hnorm 3 (Fp r g y u) +
      hnorm 3 (Sp r g y u))
    linarith [hA.hG]
  have hnS : hnorm 2 (slowNL r g y u) ≤ 16 * c.W * hnorm 3 (Sp r g y u) +
      c.Cp * hnorm 3 (Fp r g y u) + (c.E * (hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) + c.G) +
      c.φ := by
    refine bNS.trans ?_
    have h1 := mul_le_mul_of_nonneg_right hA.hW hS30
    have h2 := mul_le_mul_of_nonneg_right hA.hCp hF30
    have h3 := mul_le_mul_of_nonneg_right hA.hE (by positivity : 0 ≤ hnorm 3 (Fp r g y u) +
      hnorm 3 (Sp r g y u))
    linarith [hA.hG, hA.hφ]
  have hW₁le : Real.sqrt (9 + 8 * Real.log c.D) * hnorm 2 (Sp r g y u) +
      5 / c.D * hnorm 3 (Sp r g y u) ≤ c.Lg * c.B + 5 / c.D * hnorm 3 (Sp r g y u) := by
    have := mul_le_mul hA.hLg hA.hB hS20 hc.Lg
    linarith
  have hnFle : hnorm 2 (fastNL r g y u) ≤ 20 * (hnorm 3 (Sp r g y u) * c.L) +
      hnorm 2 (fastRest r g y u) := bNF
  have hWn : 0 ≤ Real.sqrt (9 + 8 * Real.log c.D) * hnorm 2 (Sp r g y u) +
      5 / c.D * hnorm 3 (Sp r g y u) := by
    have := hc.D
    positivity
  exact rem_alg c hc (hnorm_nonneg _ _) hbF hA.hb hA.hcy hA.hcS hA.hB
    (hnorm_nonneg _ _) ρle (hnorm_nonneg _ _) hnS (hnorm_nonneg _ _) hnFle hWn hW₁le

end OVNS.Quant.Quartic

end
