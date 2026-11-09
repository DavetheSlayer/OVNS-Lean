import OddViscousNS.Quant.Joint.Metric.EnergyId

/-!
# The bracket at weight one, at one time (node N14)

`TIMED_METRIC_PROOF_V2.md` §8.  The sum of the group of the last edge and of `D_S Y[B]` is a coefficient
of `a_F²` and a small coefficient of `b_F²`: the fibre length is `L = Z a_F + 5 b_F/D`, the mixed term
`e W · a L` is split, and `L² ≤ 2 Z² a_F² + 2 (5/D)² b_F²`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic
open GN (SupBd)

/-- `2 (C₀ + C₁)`: the two low-pass constants. -/
def cL : ℝ := 2 * (CLow 0 + CLow 1)

lemma cL_nonneg : 0 ≤ cL := by
  have := CLow_nonneg 0
  have := CLow_nonneg 1
  unfold cL
  positivity

/-- The first half of the group. -/
lemma halfB_le {a W e e₁ L L₁ K : ℝ} (ha : 0 ≤ a) (hW : 0 ≤ W) (he : 0 ≤ e) (hL : 0 ≤ L)
    (hK : 0 ≤ K) (h1 : e₁ ≤ K * e) (h2 : L₁ ≤ K * L) :
    halfB a W e₁ e L₁ L ≤ 3 * K * (e ^ 2 * W ^ 2 + a ^ 2 * L ^ 2) := by
  have s1 : e₁ * e * (W * W) ≤ K * e * e * (W * W) := by gcongr
  have s2 : 2 * (e * L₁ * a * W) ≤ 2 * (e * (K * L) * a * W) := by gcongr
  have s3 : 2 * (e₁ * L * a * W) ≤ 2 * (K * e * L * a * W) := by gcongr
  have s4 : a * L₁ * (a * L) ≤ a * (K * L) * (a * L) := by gcongr
  have hm : 0 ≤ K * (e * W - a * L) ^ 2 := by positivity
  have hp : 0 ≤ K * (e ^ 2 * W ^ 2) := by positivity
  have hq : 0 ≤ K * (a ^ 2 * L ^ 2) := by positivity
  simp only [halfB]
  nlinarith only [s1, s2, s3, s4, hm, hp, hq]

/-- The derivative in a direction, at the actual `B`. -/
lemma diff1B_le {q c₁ c₂ M a b W e L : ℝ} (hq : 0 < q) (hc₁ : 0 ≤ c₁) (hM : 0 ≤ M) :
    diff1B q c₁ c₂ (3 * M * a) (41 * M * b) W a e L ≤
      3 * c₁ * M / q * (e ^ 2 * W ^ 2 + a ^ 2 * L ^ 2) + 82 * c₂ * M * (a * b) / q ^ 2 * L ^ 2 := by
  have h0 : 0 ≤ 3 * c₁ * M / q * (e * W - a * L) ^ 2 := by positivity
  have e1 : diff1B q c₁ c₂ (3 * M * a) (41 * M * b) W a e L =
      3 * c₁ * M / q * (2 * (e * W) * (a * L)) + 82 * c₂ * M * (a * b) / q ^ 2 * L ^ 2 := by
    simp only [diff1B]
    field_simp
    ring
  have e2 : 3 * c₁ * M / q * (e * W - a * L) ^ 2 = 3 * c₁ * M / q * (e ^ 2 * W ^ 2 + a ^ 2 * L ^ 2) -
      3 * c₁ * M / q * (2 * (e * W) * (a * L)) := by ring
  rw [e1]
  linarith

/-- The coefficient of `a_F²` of the group and of `D_S Y[B]`. -/
def X11 (q D M a W b tW tB : ℝ) : ℝ :=
  2 ^ 18 * (cL + 1) * M / q * (W ^ 2 + 2 * (9 + 8 * Real.log D) * a ^ 2) +
    2 * (9 + 8 * Real.log D) * (2 ^ 22 * M * (a * b) / q ^ 2) +
    Cm3 / q * (tW * b ^ 2 + W * b * tB) +
    2 ^ 28 / q ^ 2 * (5 * ((9 + 8 * Real.log (4 * D)) * (a * b * W))) +
    2 ^ 21 / q ^ 2 * (a ^ 2 * (9 + 8 * Real.log (4 * D)) * (Real.sqrt (9 + 8 * Real.log D) * b))

/-- The coefficient of `b_F²`. -/
def X12 (q D M a b : ℝ) : ℝ :=
  2 * (5 / D) ^ 2 * (2 ^ 18 * (cL + 1) * M / q * a ^ 2 + 2 ^ 22 * M * (a * b) / q ^ 2)

/-- **The group and `D_S Y[B]` at weight one.** -/
theorem G1_BY1_le {r D M e d : ℝ} (hq : 0 < |r|) (hD : 1 ≤ D) (hM : 0 ≤ M) {S : Field}
    (he : 0 ≤ e) (hd : 0 ≤ d) :
    G₁ r D M S e d + 1 / 2 * BY1 |r| D M (hnorm 1 S) (wiener S) (hnorm 2 S) e d ≤
      X11 |r| D M (hnorm 1 S) (wiener S) (hnorm 2 S) (tailW D S) (tailB D S) * e ^ 2 +
        X12 |r| D M (hnorm 1 S) (hnorm 2 S) * d ^ 2 := by
  have hD0 : 0 < D := by linarith
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  have hZq : 0 ≤ 9 + 8 * Real.log D := by positivity
  set a := hnorm 1 S with ha
  set W := wiener S with hWd
  set b := hnorm 2 S with hb
  set Z := Real.sqrt (9 + 8 * Real.log D) with hZ
  have ha0 : 0 ≤ a := hnorm_nonneg _ _
  have hW0 : 0 ≤ W := wiener_nonneg S
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have hZ0 : 0 ≤ Z := Real.sqrt_nonneg _
  have hZZ : Z ^ 2 = 9 + 8 * Real.log D := Real.sq_sqrt hZq
  have hC0 := CLow_nonneg 0
  have hC1 := CLow_nonneg 1
  set δ := 5 / D with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set L := Z * e + δ * d with hL
  have hL0 : 0 ≤ L := by positivity
  have hK : 0 ≤ cL * M := mul_nonneg cL_nonneg hM
  have h1 : 2 * CLow 0 * M * e ≤ cL * M * e := by
    have : 0 ≤ 2 * CLow 1 * M * e := by positivity
    simp only [cL]
    nlinarith only [this]
  have h2 : Z * (2 * CLow 0 * M * e) + δ * (2 * CLow 1 * M * d) ≤ cL * M * L := by
    have t1 : 0 ≤ 2 * CLow 1 * M * (Z * e) := by positivity
    have t2 : 0 ≤ 2 * CLow 0 * M * (δ * d) := by positivity
    simp only [cL, hL]
    nlinarith only [t1, t2]
  have h3 := halfB_le ha0 hW0 he hL0 hK h1 h2
  have h4 := diff1B_le (c₁ := 2 ^ 15) (c₂ := 2 ^ 15) (M := M) (a := a) (b := b) (W := W) (e := e)
    (L := L) hq (by norm_num) hM
  have h5 := diff1B_le (c₁ := 2 ^ 11) (c₂ := 0) (M := M) (a := a) (b := b) (W := W) (e := e)
    (L := L) hq (by norm_num) hM
  have hLL : L ^ 2 ≤ 2 * (9 + 8 * Real.log D) * e ^ 2 + 2 * δ ^ 2 * d ^ 2 := by
    rw [← hZZ, hL]
    nlinarith only [sq_nonneg (Z * e - δ * d)]
  set P := e ^ 2 * W ^ 2 + a ^ 2 * L ^ 2 with hP
  have hP0 : 0 ≤ P := by positivity
  have hP1 : P ≤ (W ^ 2 + 2 * (9 + 8 * Real.log D) * a ^ 2) * e ^ 2 + a ^ 2 * (2 * δ ^ 2 * d ^ 2) := by
    have := mul_le_mul_of_nonneg_left hLL (sq_nonneg a)
    simp only [hP]
    nlinarith only [this]
  have hQ : 0 ≤ 1 / |r| := by positivity
  have hQ2 : 0 ≤ 1 / |r| ^ 2 := by positivity
  have hab : 0 ≤ a * b := by positivity
  have hMQ : 0 ≤ M / |r| := by positivity
  have hMQ2 : 0 ≤ M * (a * b) / |r| ^ 2 := by positivity
  -- the two families of terms
  have s1 : 2 * (2 ^ 14 / |r| * (3 * (cL * M) * P)) + 3 * 2 ^ 15 * M / |r| * P +
      3 * 2 ^ 11 * M / |r| * P ≤ 2 ^ 18 * (cL + 1) * M / |r| * P := by
    have h0 : 0 ≤ M / |r| * P := by positivity
    have hc := cL_nonneg
    have e1 : 2 * (2 ^ 14 / |r| * (3 * (cL * M) * P)) = 3 * 2 ^ 15 * (cL * (M / |r| * P)) := by ring
    have e2 : 3 * 2 ^ 15 * M / |r| * P = 3 * 2 ^ 15 * (M / |r| * P) := by ring
    have e3 : 3 * 2 ^ 11 * M / |r| * P = 3 * 2 ^ 11 * (M / |r| * P) := by ring
    have e4 : 2 ^ 18 * (cL + 1) * M / |r| * P =
        2 ^ 18 * (cL * (M / |r| * P)) + 2 ^ 18 * (M / |r| * P) := by ring
    rw [e1, e2, e3, e4]
    have h1 := mul_nonneg hc h0
    linarith only [h0, h1]
  have s2 : 82 * 2 ^ 15 * M * (a * b) / |r| ^ 2 * L ^ 2 ≤ 2 ^ 22 * M * (a * b) / |r| ^ 2 * L ^ 2 := by
    have h0 : 0 ≤ M * (a * b) / |r| ^ 2 * L ^ 2 := by positivity
    have e1 : 82 * 2 ^ 15 * M * (a * b) / |r| ^ 2 * L ^ 2 =
        82 * 2 ^ 15 * (M * (a * b) / |r| ^ 2 * L ^ 2) := by ring
    have e2 : 2 ^ 22 * M * (a * b) / |r| ^ 2 * L ^ 2 =
        2 ^ 22 * (M * (a * b) / |r| ^ 2 * L ^ 2) := by ring
    rw [e1, e2]
    linarith only [h0]
  have hcL1 : 0 ≤ cL + 1 := by linarith only [cL_nonneg]
  have s3 := mul_le_mul_of_nonneg_left hP1
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcL1) hM) hq.le :
      0 ≤ 2 ^ 18 * (cL + 1) * M / |r|)
  have s4 := mul_le_mul_of_nonneg_left hLL
    (by positivity : 0 ≤ 2 ^ 22 * M * (a * b) / |r| ^ 2)
  have s5 : 2 * (2 ^ 14 / |r| * halfB a W (2 * CLow 0 * M * e) e
      (Z * (2 * CLow 0 * M * e) + δ * (2 * CLow 1 * M * d)) L) ≤
      2 * (2 ^ 14 / |r| * (3 * (cL * M) * P)) := by gcongr
  have e0 : 1 / 2 * BY1 |r| D M a W b e d =
      diff1B |r| (2 ^ 15) (2 ^ 15) (3 * M * a) (41 * M * b) W a e L +
        diff1B |r| (2 ^ 11) 0 (3 * M * a) (41 * M * b) W a e L := by
    simp only [BY1]
    ring
  have e3 : G₁ r D M S e d = 2 * (2 ^ 14 / |r| * halfB a W (2 * CLow 0 * M * e) e
      (Z * (2 * CLow 0 * M * e) + δ * (2 * CLow 1 * M * d)) L) +
      Cm3 / |r| * (tailW D S * hnorm 2 S ^ 2 + wiener S * hnorm 2 S * tailB D S) * e ^ 2 +
      2 ^ 28 / |r| ^ 2 * (e ^ 2 * sep1B D S) +
      2 ^ 21 / |r| ^ 2 * (e ^ 2 * (hnorm 1 S ^ 2 * (9 + 8 * Real.log (4 * D)) *
        (Z * hnorm 2 S))) := rfl
  rw [e0, e3]
  simp only [X11, X12, sep1B]
  rw [← ha, ← hb, ← hWd]
  have h4' : 3 * 2 ^ 15 * M / |r| * P + 82 * 2 ^ 15 * M * (a * b) / |r| ^ 2 * L ^ 2 ≥
      diff1B |r| (2 ^ 15) (2 ^ 15) (3 * M * a) (41 * M * b) W a e L := h4
  have h5' : 3 * 2 ^ 11 * M / |r| * P ≥
      diff1B |r| (2 ^ 11) 0 (3 * M * a) (41 * M * b) W a e L := by
    refine h5.trans (le_of_eq ?_)
    ring
  have e4 : 2 ^ 18 * (cL + 1) * M / |r| * ((W ^ 2 + 2 * (9 + 8 * Real.log D) * a ^ 2) * e ^ 2 +
      a ^ 2 * (2 * δ ^ 2 * d ^ 2)) + 2 ^ 22 * M * (a * b) / |r| ^ 2 *
      (2 * (9 + 8 * Real.log D) * e ^ 2 + 2 * δ ^ 2 * d ^ 2) =
      (2 ^ 18 * (cL + 1) * M / |r| * (W ^ 2 + 2 * (9 + 8 * Real.log D) * a ^ 2) +
        2 * (9 + 8 * Real.log D) * (2 ^ 22 * M * (a * b) / |r| ^ 2)) * e ^ 2 +
      2 * δ ^ 2 * (2 ^ 18 * (cL + 1) * M / |r| * a ^ 2 + 2 ^ 22 * M * (a * b) / |r| ^ 2) * d ^ 2 := by
    ring
  have key : 2 * (2 ^ 14 / |r| * halfB a W (2 * CLow 0 * M * e) e
      (Z * (2 * CLow 0 * M * e) + δ * (2 * CLow 1 * M * d)) L) +
      (diff1B |r| (2 ^ 15) (2 ^ 15) (3 * M * a) (41 * M * b) W a e L +
        diff1B |r| (2 ^ 11) 0 (3 * M * a) (41 * M * b) W a e L) ≤
      (2 ^ 18 * (cL + 1) * M / |r| * (W ^ 2 + 2 * (9 + 8 * Real.log D) * a ^ 2) +
        2 * (9 + 8 * Real.log D) * (2 ^ 22 * M * (a * b) / |r| ^ 2)) * e ^ 2 +
      2 * δ ^ 2 * (2 ^ 18 * (cL + 1) * M / |r| * a ^ 2 + 2 ^ 22 * M * (a * b) / |r| ^ 2) * d ^ 2 := by
    rw [← e4]
    linarith only [s1, s2, s3, s4, s5, h4', h5']
  have e5 : (2 ^ 18 * (cL + 1) * M / |r| * (W ^ 2 + 2 * (9 + 8 * Real.log D) * a ^ 2) +
        2 * (9 + 8 * Real.log D) * (2 ^ 22 * M * (a * b) / |r| ^ 2) +
        Cm3 / |r| * (tailW D S * b ^ 2 + W * b * tailB D S) +
        2 ^ 28 / |r| ^ 2 * (5 * ((9 + 8 * Real.log (4 * D)) * (a * b * W))) +
        2 ^ 21 / |r| ^ 2 * (a ^ 2 * (9 + 8 * Real.log (4 * D)) * (Z * b))) * e ^ 2 =
      (2 ^ 18 * (cL + 1) * M / |r| * (W ^ 2 + 2 * (9 + 8 * Real.log D) * a ^ 2) +
        2 * (9 + 8 * Real.log D) * (2 ^ 22 * M * (a * b) / |r| ^ 2)) * e ^ 2 +
      Cm3 / |r| * (tailW D S * b ^ 2 + W * b * tailB D S) * e ^ 2 +
      2 ^ 28 / |r| ^ 2 * (e ^ 2 * (5 * ((9 + 8 * Real.log (4 * D)) * (a * b * W)))) +
      2 ^ 21 / |r| ^ 2 * (e ^ 2 * (a ^ 2 * (9 + 8 * Real.log (4 * D)) * (Z * b))) := by
    ring
  rw [e5]
  linarith only [key]

/-! ### The direction `N_F` in `L²` -/

section Path

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}

/-- The product in `L²`, by (M4) at `σ = 1`. -/
lemma Qphase_l2 (τ : ℝ) {f f' : Field} (hf : MZ 2 f) (hf' : MZ 2 f') :
    InH 0 (Qphase τ f f') ∧ hnorm 0 (Qphase τ f f') ≤
      2 * (wiener f * hnorm 1 f' + hnorm 1 f * wiener f') := by
  have h := hnorm_Qm_le (phaseM_bdd τ) (σ := 1) le_rfl (hf.mono' (by norm_num))
    (hf'.mono' (by norm_num)) hf hf'
  rw [show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_one] at h
  exact h

/-- **`‖N_F‖₀`**: no norm of `S` above `H¹`. -/
theorem fastNL_l2_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    (Summable fun k => ‖fastNL r g y u k‖ ^ 2) ∧ l2n (fastNL r g y u) ≤
      4 * (wiener (Sp r g y u) * hnorm 1 (Fp r g y u) +
        hnorm 1 (Sp r g y u) * wiener (Fp r g y u)) +
        4 * (wiener (Fp r g y u) * hnorm 1 (Fp r g y u)) + hnorm 1 (Hf r g y u) := by
  have hx := actual_adm h hu huT
  have hS : Adm 2 (Sp r g y u) := hx.PiS
  have hF : Adm 2 (Fp r g y u) := hx.PiF
  obtain ⟨q1, b1⟩ := Qphase_l2 (r * u) hS.mz hF.mz
  obtain ⟨q2, b2⟩ := Qphase_l2 (r * u) hF.mz hF.mz
  obtain ⟨hH, bH⟩ := Hf_one h hr hu huT
  have e1 := PiF_Qphase_eq (r * u) hx
  have e2 : fastNL r g y u = fastQ r g y u - Hf r g y u := by
    rw [fastQ_eq]
    abel
  have e3 : fastNL r g y u = -(Qphase (r * u) (Sp r g y u) (Fp r g y u) +
      Qphase (r * u) (Sp r g y u) (Fp r g y u) + PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u))) -
      Hf r g y u := by
    rw [e2, fastQ, e1]
    rfl
  have hH0 : InH 0 (Hf r g y u) := hH.inH.mono (by norm_num)
  have i1 := q1.add q1
  have i2 := i1.add q2.PiF
  have hin : InH 0 (fastNL r g y u) := by
    rw [e3]
    exact i2.neg.sub hH0
  have hm : fastNL r g y u 0 = 0 := by simp [fastNL, PiF]
  have hs : Summable fun k => ‖fastNL r g y u k‖ ^ 2 := mz_l2 le_rfl ⟨hin, hm⟩
  refine ⟨hs, ?_⟩
  rw [l2n_eq_hnorm0 hm, e3]
  refine (hnorm_sub_le i2.neg hH0).trans ?_
  rw [hnorm_neg]
  have t1 := hnorm_add_le i1 q2.PiF
  have t2 := hnorm_add_le q1 q1
  have t3 := hnorm_PiF_le q2
  have t4 : hnorm 0 (Hf r g y u) ≤ hnorm 1 (Hf r g y u) := hnorm_mono (by norm_num) hH.inH
  have b3 : wiener (Fp r g y u) * hnorm 1 (Fp r g y u) + hnorm 1 (Fp r g y u) * wiener (Fp r g y u) =
      2 * (wiener (Fp r g y u) * hnorm 1 (Fp r g y u)) := by ring
  rw [b3] at b2
  linarith

end Path

end OVNS.Quant.Metric

end
