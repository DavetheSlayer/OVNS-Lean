import OddViscousNS.Quant.Joint.Quartic.Price2

/-!
# The prices of `C_{4,1}` (step J5, node N11)

J3-v2 §5.  With `κ₁ = kap1 r ε = 3·2¹³ √𝔐_P(q)/q^{1−ε}`, `a = ‖F‖₁`, `b = ‖F‖₂`:

* `val_one_le`: `|Q₄,₁| ≤ 2¹² q^{−1/2} 3√𝔐 ‖S‖_{3/2} L a²`;
* `rem_one_le`: `|Rem| ≤ κ₁ (2 ‖N_S‖₁ L a b + 2 a_S L_ε ‖N_F‖₁ a b + 2 b_S L ‖N_F‖₁ a + 2 a_S L ‖N_F‖₁ b)`,
  `L_ε = √(9 + 4/ε)`: "the four remainders";
* `Co1`, `rem_one_caps`: with `‖N_F‖₁ ≤ N b + h`: `|Rem| ≤ κ₁ (m₁ b² + y₁ h b)`, "the nonlinear debit",
  `m₁ ≍ U R⁴`, and "the extra genuine debit", `y₁ ≍ U R²`.
-/

open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- `κ₁ = C P(q) q^{−1+ε}`, with the literal constant, `ε^{−1/2}` apart. -/
def kap1 (r ε : ℝ) : ℝ := 2 ^ 13 / |r| ^ (1 - ε) * (3 * Real.sqrt (MomP |r|))

lemma kap1_nonneg (r ε : ℝ) : 0 ≤ kap1 r ε := by
  have : 0 ≤ |r| ^ (1 - ε) := Real.rpow_nonneg (abs_nonneg r) _
  unfold kap1
  positivity

/-- **The static bound of the quartic**, weight one. -/
theorem val_one_le (hr : r ≠ 0) (h : ActualSol μ φ r g y Ty) {u L : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hL : LhB (nrm (Fp r g y u)) L) :
    ‖val4 1 r g y u‖ ≤ 2 ^ 12 / Real.sqrt |r| * (3 * (Real.sqrt (MomP |r|) *
      (hnorm (3 / 2) (Sp r g y u) * L * hnorm 1 (Fp r g y u) * hnorm 1 (Fp r g y u)))) := by
  have hF := Fp_adm h hu huT
  have hS := Sp_adm h hu huT
  have hF1 : InH 1 (Fp r g y u) := hF.inH.mono (by norm_num)
  have hs := Q1_static_sb hr (slots_val r g y u) (hS.inH.mono (by norm_num)) hL hF1 hF1 (r * u)
  exact (norm_tsum_le_tsum_norm hs.1).trans hs.2

/-- The weighted fibre of `F` is below its fibre. -/
lemma lhB_weight {F : Field} {L ε : ℝ} (hL : LhB (nrm F) L) (hε : 0 ≤ ε) (hF0 : F 0 = 0) :
    LhB (fun k => (absk k)⁻¹ ^ ε * ‖F k‖) L := by
  refine hL.of_le (fun k => mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 (absk_nonneg k)) _)
    (norm_nonneg _)) fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [hF0, nrm]
  · have h1 := inv_rpow_le_one (one_le_absk hk) hε
    exact mul_le_of_le_one_left (norm_nonneg _) h1

/-- **The four insertions**, weight one. -/
theorem rem_one_le (hr : r ≠ 0) (h : ActualSol μ φ r g y Ty) {u L ε : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hN1 : InH 1 (fastNL r g y u))
    (hNs1 : InH 1 (slowNL r g y u)) (hL : LhB (nrm (Fp r g y u)) L) :
    ‖rem4 1 r g y u‖ ≤ kap1 r ε *
      (2 * (hnorm 1 (slowNL r g y u) * L * hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) +
        2 * (hnorm 1 (Sp r g y u) * Real.sqrt (9 + 4 / ε) * hnorm 1 (fastNL r g y u) *
          hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) +
        2 * (hnorm 2 (Sp r g y u) * L * hnorm 1 (fastNL r g y u) * hnorm 1 (Fp r g y u)) +
        2 * (hnorm 1 (Sp r g y u) * L * hnorm 1 (fastNL r g y u) * hnorm 2 (Fp r g y u))) := by
  have hF := Fp_adm h hu huT
  have hS := Sp_adm h hu huT
  have hF1 : InH 1 (Fp r g y u) := hF.inH.mono (by norm_num)
  have hS1 : InH 1 (Sp r g y u) := hS.inH.mono (by norm_num)
  have hW := lhB_weight hL hε0.le hF.mean
  have hLN := lhB_eps hε0 hN1 (PiF_fastNL u)
  have s1 := Q1_in_sb hr hε0.le hε1 (slots_S r g y u) hNs1 hW hF.inH hF.inH (r * u)
  have s2 := Q1_in_sb hr hε0.le hε1 (slots_W r g y u) hS1 hLN hF.inH hF.inH (r * u)
  have s3 := Q1_q_sb hr hε0.le hε1 (slots_U r g y u) hS.inH hL hN1 hF.inH (r * u)
  have s4 := Q1_e_sb hr hε0.le hε1 (slots_V r g y u) hS.inH hL hF.inH hN1 (r * u)
  have t1 := (norm_tsum_le_tsum_norm s1.1).trans s1.2
  have t2 := (norm_tsum_le_tsum_norm s2.1).trans s2.2
  have t3 := (norm_tsum_le_tsum_norm s3.1).trans s3.2
  have t4 := (norm_tsum_le_tsum_norm s4.1).trans s4.2
  unfold rem4
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4) |>.trans (le_of_eq ?_)
  simp only [kap1]
  ring

/-- The parameters of the weight-one prices. -/
structure Co1 where
  /-- The fibre norm of `F`. -/
  L : ℝ
  /-- `a_F ≤ P`. -/
  P : ℝ
  /-- `a_S ≤ A`. -/
  A : ℝ
  /-- `b_S ≤ B`. -/
  B : ℝ
  /-- `‖N_S‖₁ ≤ Ns`. -/
  Ns : ℝ
  /-- `‖N_F‖₁ ≤ Nb b + h`. -/
  Nb : ℝ
  /-- `√(9 + 4/ε)`. -/
  Le : ℝ

namespace Co1

variable (c : Co1)

/-- **The nonlinear debit**: J3-v2's `U R⁴ L(R)`. -/
def m₁ : ℝ := 2 * c.Ns * c.L + 2 * c.A * c.Le * c.P * c.Nb + 2 * c.B * c.L * c.Nb +
  2 * c.A * c.L * c.Nb

/-- **The extra genuine debit**: J3-v2's `U R² L(R)`. -/
def y₁ : ℝ := 2 * c.A * c.Le * c.P + 2 * c.B * c.L + 2 * c.A * c.L

end Co1

/-- **The algebra of the weight-one remainder.** -/
theorem rem_alg₁ (c : Co1) (hL : 0 ≤ c.L) (hA : 0 ≤ c.A) (hB : 0 ≤ c.B)
    (hNs : 0 ≤ c.Ns) (hNb : 0 ≤ c.Nb) (hLe : 0 ≤ c.Le) {a b nS nF a₀ B₀ h₀ : ℝ} (ha0 : 0 ≤ a)
    (hab : a ≤ b) (haP : a ≤ c.P) (hnS : nS ≤ c.Ns) (hnF0 : 0 ≤ nF)
    (hnF : nF ≤ c.Nb * b + h₀) (ha₀ : a₀ ≤ c.A) (hB₀ : B₀ ≤ c.B) (hh0 : 0 ≤ h₀) :
    2 * (nS * c.L * a * b) + 2 * (a₀ * c.Le * nF * a * b) + 2 * (B₀ * c.L * nF * a) +
        2 * (a₀ * c.L * nF * b) ≤ c.m₁ * b ^ 2 + c.y₁ * h₀ * b := by
  have hb0 : 0 ≤ b := ha0.trans hab
  have hN0 : 0 ≤ c.Nb * b + h₀ := by positivity
  have t1 : nS * c.L * a * b ≤ c.Ns * c.L * b * b :=
    mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right hnS hL) hab ha0
      (mul_nonneg hNs hL)) hb0
  have t2 : a₀ * c.Le * nF * a * b ≤ c.A * c.Le * (c.Nb * b + h₀) * c.P * b :=
    mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right ha₀ hLe) hnF
      hnF0 (mul_nonneg hA hLe)) haP ha0 (mul_nonneg (mul_nonneg hA hLe) hN0)) hb0
  have t3 : B₀ * c.L * nF * a ≤ c.B * c.L * (c.Nb * b + h₀) * b :=
    mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hB₀ hL) hnF hnF0 (mul_nonneg hB hL)) hab
      ha0 (mul_nonneg (mul_nonneg hB hL) hN0)
  have t4 : a₀ * c.L * nF * b ≤ c.A * c.L * (c.Nb * b + h₀) * b :=
    mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right ha₀ hL) hnF hnF0
      (mul_nonneg hA hL)) hb0
  have e : c.m₁ * b ^ 2 + c.y₁ * h₀ * b = 2 * (c.Ns * c.L * b * b) +
      2 * (c.A * c.Le * (c.Nb * b + h₀) * c.P * b) + 2 * (c.B * c.L * (c.Nb * b + h₀) * b) +
      2 * (c.A * c.L * (c.Nb * b + h₀) * b) := by
    simp only [Co1.m₁, Co1.y₁]
    ring
  rw [e]
  linarith

/-- **`N_F` in `H¹`, against the caps**: `‖N_F‖₁ ≤ 8 (W + c₄ B + c₄ y) b + h`. -/
theorem fastNL_one_caps (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u W B Y : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hW : wiener (Sp r g y u) ≤ W) (hB : hnorm 2 (Sp r g y u) ≤ B)
    (hY : hnorm 2 (Fp r g y u) ≤ Y) :
    hnorm 1 (fastNL r g y u) ≤ 8 * (W + c4 * B + c4 * Y) * hnorm 2 (Fp r g y u) +
      hnorm 1 (Hpsi r g y u) := by
  have hF := Fp_adm h hu huT
  have hc := c4_pos
  refine (hnorm_one_fastNL_le h hr hu huT).trans (add_le_add_left ?_ _)
  have hw : wiener (Fp r g y u) ≤ c4 * hnorm 2 (Fp r g y u) := wiener_le hF.mz
  have hb0 := hnorm_nonneg 2 (Fp r g y u)
  have hB0 := hnorm_nonneg 2 (Sp r g y u)
  have hw0 := wiener_nonneg (Fp r g y u)
  have e : fastXi (actual r g y u) = wiener (Sp r g y u) * hnorm 2 (Fp r g y u) +
      hnorm 2 (Sp r g y u) * wiener (Fp r g y u) +
      wiener (Fp r g y u) * hnorm 2 (Fp r g y u) := rfl
  rw [e]
  have t1 := mul_le_mul_of_nonneg_right hW hb0
  have t2 : hnorm 2 (Sp r g y u) * wiener (Fp r g y u) ≤ B * (c4 * hnorm 2 (Fp r g y u)) :=
    mul_le_mul hB hw hw0 (hB0.trans hB)
  have t3 : wiener (Fp r g y u) * hnorm 2 (Fp r g y u) ≤
      c4 * Y * hnorm 2 (Fp r g y u) := by
    have : wiener (Fp r g y u) ≤ c4 * Y := hw.trans (mul_le_mul_of_nonneg_left hY hc.le)
    exact mul_le_mul_of_nonneg_right this hb0
  nlinarith only [t1, t2, t3]

/-- **The remainder of `C_{4,1}`**, J3-v2 §5: the nonlinear and the genuine debit. -/
theorem rem_one_caps (hr : r ≠ 0) (h : ActualSol μ φ r g y Ty) {u ε : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (c : Co1)
    (hN1 : InH 1 (fastNL r g y u)) (hNs1 : InH 1 (slowNL r g y u))
    (hL : LhB (nrm (Fp r g y u)) c.L) (hP : hnorm 1 (Fp r g y u) ≤ c.P)
    (hA : hnorm 1 (Sp r g y u) ≤ c.A) (hB : hnorm 2 (Sp r g y u) ≤ c.B)
    (hNs : hnorm 1 (slowNL r g y u) ≤ c.Ns) (hNb0 : 0 ≤ c.Nb)
    (hNF : hnorm 1 (fastNL r g y u) ≤ c.Nb * hnorm 2 (Fp r g y u) + hnorm 1 (Hpsi r g y u))
    (hLe : Real.sqrt (9 + 4 / ε) ≤ c.Le) :
    ‖rem4 1 r g y u‖ ≤ kap1 r ε * (c.m₁ * hnorm 2 (Fp r g y u) ^ 2 +
      c.y₁ * hnorm 1 (Hpsi r g y u) * hnorm 2 (Fp r g y u)) := by
  have hF := Fp_adm h hu huT
  have hb := rem_one_le hr h hu huT hε0 hε1 hN1 hNs1 hL
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ (kap1_nonneg r ε))
  have hL0 := hL.bd_nonneg
  have ha0 := hnorm_nonneg 1 (Fp r g y u)
  have hab : hnorm 1 (Fp r g y u) ≤ hnorm 2 (Fp r g y u) := hnorm_mono (by norm_num) hF.inH
  have hA0 := hnorm_nonneg 1 (Sp r g y u)
  have hB0 := hnorm_nonneg 2 (Sp r g y u)
  have hLe0 := Real.sqrt_nonneg (9 + 4 / ε)
  have key := rem_alg₁ c hL0 (hA0.trans hA) (hB0.trans hB)
    ((hnorm_nonneg _ _).trans hNs) hNb0 (hLe0.trans hLe) ha0 hab hP hNs
    (hnorm_nonneg _ _) hNF hA hB (hnorm_nonneg _ _)
  refine le_trans ?_ key
  have h1 : hnorm 1 (Sp r g y u) * Real.sqrt (9 + 4 / ε) ≤ hnorm 1 (Sp r g y u) * c.Le :=
    mul_le_mul_of_nonneg_left hLe hA0
  have h2 : 0 ≤ hnorm 1 (fastNL r g y u) * hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u) :=
    mul_nonneg (mul_nonneg (hnorm_nonneg _ _) ha0) (hnorm_nonneg _ _)
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  nlinarith only [h3]

end OVNS.Quant.Quartic

end
