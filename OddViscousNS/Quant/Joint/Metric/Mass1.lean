import OddViscousNS.Quant.Joint.Metric.Bound1

/-!
# The multiplier of the first energy (node N14)

`TIMED_METRIC_PROOF_V2.md` (8.11).  `m₁ = κ₁ (W² + a²) + κ₂ c_y² + κ₃` at every `H³` time of `y_S`, with
constants at the caps.  On a piece, `∫ (W² + a²) ≲ R²`, by the slot `kin` of `SlowOut`, `∫ c_y² ≲ R⁵`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic
open GN (SupBd)

/-- The logarithm of the band. -/
abbrev Zs (D : ℝ) : ℝ := 9 + 8 * Real.log D

/-- The logarithm of the band `4 D`. -/
abbrev Z4s (D : ℝ) : ℝ := 9 + 8 * Real.log (4 * D)

/-- The coefficient of `W² + a²` in the slots of `O`. -/
def T0 (D : ℝ) : ℝ :=
  6 * Real.sqrt (Zs D) + 2 * c4 * Real.sqrt (Zs D) + 2 * c4 +
    Real.sqrt 17 * Real.sqrt (Z4s D) * (1 + Real.sqrt (Zs D))

lemma T0_nonneg (D : ℝ) : 0 ≤ T0 D := by
  have := c4_pos
  unfold T0
  positivity

/-- The slots of `O` against `W² + a²`. -/
lemma T3_le {D a W : ℝ} : T3 D a W ≤ T0 D * (W ^ 2 + a ^ 2) := by
  set Z := Real.sqrt (Zs D) with hZ
  set Z₄ := Real.sqrt (Z4s D) with hZ₄
  have hZ0 : 0 ≤ Z := Real.sqrt_nonneg _
  have hZ40 : 0 ≤ Z₄ := Real.sqrt_nonneg _
  have hc := c4_pos
  have h17 : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
  have haW : 2 * (a * W) ≤ W ^ 2 + a ^ 2 := by nlinarith only [sq_nonneg (a - W)]
  have ha2 := sq_nonneg a
  have hW2 := sq_nonneg W
  have e : T3 D a W = 6 * (Z * W ^ 2) + 2 * c4 * Z * (2 * (a * W)) + 2 * c4 * W ^ 2 +
      Real.sqrt 17 * Z₄ * (2 * (a * W) + Z * a ^ 2) := by
    simp only [T3, hZ, hZ₄, Zs, Z4s]
    ring
  have e2 : T0 D * (W ^ 2 + a ^ 2) = (6 * Z) * (W ^ 2 + a ^ 2) + (2 * c4 * Z) * (W ^ 2 + a ^ 2) +
      (2 * c4) * (W ^ 2 + a ^ 2) + (Real.sqrt 17 * Z₄) * ((1 + Z) * (W ^ 2 + a ^ 2)) := by
    simp only [T0, hZ, hZ₄]
    ring
  rw [e, e2]
  have s1 : 6 * Z * W ^ 2 ≤ 6 * Z * (W ^ 2 + a ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have s2 : 2 * c4 * Z * (2 * (a * W)) ≤ 2 * c4 * Z * (W ^ 2 + a ^ 2) :=
    mul_le_mul_of_nonneg_left haW (by positivity)
  have s3 : 2 * c4 * W ^ 2 ≤ 2 * c4 * (W ^ 2 + a ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have s4 : 2 * (a * W) + Z * a ^ 2 ≤ (1 + Z) * (W ^ 2 + a ^ 2) := by
    have := mul_le_mul_of_nonneg_left (by linarith : a ^ 2 ≤ W ^ 2 + a ^ 2) hZ0
    nlinarith only [this, haW]
  have s5 := mul_le_mul_of_nonneg_left s4 (by positivity : 0 ≤ Real.sqrt 17 * Z₄)
  have e3 : 6 * (Z * W ^ 2) = 6 * Z * W ^ 2 := by ring
  rw [e3]
  linarith only [s1, s2, s3, s5]

/-- The `q⁻¹` coefficient of `W² + a²`. -/
def A11 (R M D B : ℝ) : ℝ :=
  2 ^ 18 * (cL + 1) * M * (1 + 2 * Zs D) + Cm3 * B * (1 / (2 * D) + 1 / (2 * R))

/-- The part of the `q⁻²` coefficient of `W² + a²` in the group. -/
def B11g (D B : ℝ) : ℝ :=
  2 ^ 27 * 5 * Z4s D * B + 2 ^ 21 * Z4s D * Real.sqrt (Zs D) * B

/-- The `q⁻¹` coefficient of `c_y²`. -/
def A12 (D B : ℝ) : ℝ := Cm3 * B / (2 * D)

/-- The `q⁻¹` constant. -/
def A13 (R D B : ℝ) : ℝ := 5 * Cm3 * B ^ 3 / D + Cm3 * B * R / 2

/-- The `q⁻²` constant. -/
def B13 (M D A B : ℝ) : ℝ := 2 * Zs D * (2 ^ 22 * M * (A * B))

lemma delta0_le_one : delta0 ≤ 1 := by norm_num [delta0]

/-- **`X11`, by the kinetic density, `c_y²` and constants.** -/
theorem X11_le {q D R M a W b tW tB A B cy : ℝ} (hq : 0 < q) (hD : 1 ≤ D) (hR : 0 < R) (hM : 0 ≤ M)
    (ha : 0 ≤ a) (hW : 0 ≤ W) (hb : 0 ≤ b) (hcy : 0 ≤ cy) (haA : a ≤ A) (hbB : b ≤ B)
    (htW : tW ≤ 5 / D * B) (htB : tB ≤ cy / D + delta0) (htB0 : 0 ≤ tB) :
    X11 q D M a W b tW tB ≤ (A11 R M D B / q + B11g D B / q ^ 2) * (W ^ 2 + a ^ 2) +
      A12 D B / q * cy ^ 2 + (A13 R D B / q + B13 M D A B / q ^ 2) := by
  have hD0 : 0 < D := by linarith
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  have hZq : 0 ≤ Zs D := by unfold Zs; positivity
  have hlog4 : 0 ≤ Real.log (4 * D) := Real.log_nonneg (by linarith)
  have hZ4 : 0 ≤ Z4s D := by unfold Z4s; positivity
  have hZ0 : 0 ≤ Real.sqrt (Zs D) := Real.sqrt_nonneg _
  have hB : 0 ≤ B := hb.trans hbB
  have hA : 0 ≤ A := ha.trans haA
  have hC := Cm3_pos
  have hcL := cL_nonneg
  have hd := delta0_pos
  have hK := add_nonneg (sq_nonneg W) (sq_nonneg a)
  have haW : a * W ≤ (W ^ 2 + a ^ 2) / 2 := by nlinarith only [sq_nonneg (a - W)]
  have hab : a * b ≤ A * B := mul_le_mul haA hbB hb hA
  have hWK : W ^ 2 ≤ W ^ 2 + a ^ 2 := by linarith only [sq_nonneg a]
  have haK : a ^ 2 ≤ W ^ 2 + a ^ 2 := by linarith only [sq_nonneg W]
  -- first term
  have t1 : 2 ^ 18 * (cL + 1) * M / q * (W ^ 2 + 2 * Zs D * a ^ 2) ≤
      2 ^ 18 * (cL + 1) * M * (1 + 2 * Zs D) / q * (W ^ 2 + a ^ 2) := by
    have h0 : 0 ≤ 2 ^ 18 * (cL + 1) * M / q := by positivity
    have h1 : W ^ 2 + 2 * Zs D * a ^ 2 ≤ (1 + 2 * Zs D) * (W ^ 2 + a ^ 2) := by
      nlinarith only [mul_nonneg hZq (sq_nonneg W)]
    have := mul_le_mul_of_nonneg_left h1 h0
    refine this.trans (le_of_eq ?_)
    ring
  -- second term
  have t2 : 2 * Zs D * (2 ^ 22 * M * (a * b) / q ^ 2) ≤ B13 M D A B / q ^ 2 := by
    have h0 : 2 ^ 22 * M * (a * b) ≤ 2 ^ 22 * M * (A * B) :=
      mul_le_mul_of_nonneg_left hab (by positivity)
    have h1 := div_le_div_of_nonneg_right h0 (by positivity : 0 ≤ q ^ 2)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * Zs D)
    refine h2.trans (le_of_eq ?_)
    simp only [B13]
    ring
  -- the high ancestors
  have t3 : Cm3 / q * (tW * b ^ 2 + W * b * tB) ≤
      5 * Cm3 * B ^ 3 / D / q + Cm3 * B * R / 2 / q +
        Cm3 * B * (1 / (2 * D) + 1 / (2 * R)) / q * (W ^ 2 + a ^ 2) +
        A12 D B / q * cy ^ 2 := by
    have s1 : tW * b ^ 2 ≤ 5 / D * B * B ^ 2 :=
      mul_le_mul htW (pow_le_pow_left₀ hb hbB 2) (sq_nonneg b) (by positivity)
    have s2 : W * b * tB ≤ W * B * (cy / D + delta0) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hbB hW) htB htB0 (by positivity)
    have s3 : W * cy ≤ (W ^ 2 + cy ^ 2) / 2 := by nlinarith only [sq_nonneg (W - cy)]
    have s4 : W * delta0 ≤ (W ^ 2 / R + R) / 2 := by
      have h1 : W * delta0 ≤ W := mul_le_of_le_one_right hW delta0_le_one
      have h2 : W ≤ (W ^ 2 / R + R) / 2 := by
        have h3 : 0 ≤ (W - R) ^ 2 / R := by positivity
        have e : (W - R) ^ 2 / R = W ^ 2 / R - 2 * W + R := by
          field_simp
          ring
        linarith
      linarith
    have s5 : W * B * (cy / D + delta0) ≤
        B / D * ((W ^ 2 + cy ^ 2) / 2) + B * ((W ^ 2 / R + R) / 2) := by
      have e : W * B * (cy / D + delta0) = B / D * (W * cy) + B * (W * delta0) := by
        field_simp
      rw [e]
      exact add_le_add (mul_le_mul_of_nonneg_left s3 (by positivity))
        (mul_le_mul_of_nonneg_left s4 hB)
    have s6 : tW * b ^ 2 + W * b * tB ≤ 5 / D * B * B ^ 2 + (B / D * ((W ^ 2 + cy ^ 2) / 2) +
        B * ((W ^ 2 / R + R) / 2)) := add_le_add s1 (s2.trans s5)
    have s7 := mul_le_mul_of_nonneg_left s6 (by positivity : 0 ≤ Cm3 / q)
    have s8 : Cm3 / q * (B / D * (W ^ 2 / 2)) ≤ Cm3 / q * (B / D * ((W ^ 2 + a ^ 2) / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
        (by positivity)
    have s9 : Cm3 / q * (B * (W ^ 2 / R / 2)) ≤ Cm3 / q * (B * ((W ^ 2 + a ^ 2) / R / 2)) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hB) (by positivity)
      have := div_le_div_of_nonneg_right hWK hR.le
      linarith
    have e1 : Cm3 / q * (5 / D * B * B ^ 2 + (B / D * ((W ^ 2 + cy ^ 2) / 2) +
        B * ((W ^ 2 / R + R) / 2))) = 5 * Cm3 * B ^ 3 / D / q + Cm3 * B * R / 2 / q +
        Cm3 / q * (B / D * (W ^ 2 / 2)) + Cm3 / q * (B * (W ^ 2 / R / 2)) +
        A12 D B / q * cy ^ 2 := by
      simp only [A12]
      field_simp
      ring
    have e2 : Cm3 * B * (1 / (2 * D) + 1 / (2 * R)) / q * (W ^ 2 + a ^ 2) =
        Cm3 / q * (B / D * ((W ^ 2 + a ^ 2) / 2)) + Cm3 / q * (B * ((W ^ 2 + a ^ 2) / R / 2)) := by
      field_simp
    rw [e1] at s7
    rw [e2]
    linarith only [s7, s8, s9]
  -- the separated terms
  have t4 : 2 ^ 28 / q ^ 2 * (5 * (Z4s D * (a * b * W))) ≤
      2 ^ 27 * 5 * Z4s D * B / q ^ 2 * (W ^ 2 + a ^ 2) := by
    have s1 : a * b * W ≤ B * ((W ^ 2 + a ^ 2) / 2) := by
      calc a * b * W = b * (a * W) := by ring
        _ ≤ B * ((W ^ 2 + a ^ 2) / 2) := mul_le_mul hbB haW (by positivity) hB
    have s2 := mul_le_mul_of_nonneg_left s1 (by positivity : 0 ≤ 2 ^ 28 / q ^ 2 * (5 * Z4s D))
    calc 2 ^ 28 / q ^ 2 * (5 * (Z4s D * (a * b * W))) =
        2 ^ 28 / q ^ 2 * (5 * Z4s D) * (a * b * W) := by ring
      _ ≤ _ := s2
      _ = _ := by ring
  have t5 : 2 ^ 21 / q ^ 2 * (a ^ 2 * Z4s D * (Real.sqrt (Zs D) * b)) ≤
      2 ^ 21 * Z4s D * Real.sqrt (Zs D) * B / q ^ 2 * (W ^ 2 + a ^ 2) := by
    have s1 : a ^ 2 * b ≤ (W ^ 2 + a ^ 2) * B := mul_le_mul haK hbB hb hK
    have s2 := mul_le_mul_of_nonneg_left s1
      (by positivity : 0 ≤ 2 ^ 21 / q ^ 2 * (Z4s D * Real.sqrt (Zs D)))
    calc 2 ^ 21 / q ^ 2 * (a ^ 2 * Z4s D * (Real.sqrt (Zs D) * b)) =
        2 ^ 21 / q ^ 2 * (Z4s D * Real.sqrt (Zs D)) * (a ^ 2 * b) := by ring
      _ ≤ _ := s2
      _ = _ := by ring
  have e : (A11 R M D B / q + B11g D B / q ^ 2) * (W ^ 2 + a ^ 2) + A12 D B / q * cy ^ 2 +
      (A13 R D B / q + B13 M D A B / q ^ 2) =
      2 ^ 18 * (cL + 1) * M * (1 + 2 * Zs D) / q * (W ^ 2 + a ^ 2) + B13 M D A B / q ^ 2 +
      (5 * Cm3 * B ^ 3 / D / q + Cm3 * B * R / 2 / q +
        Cm3 * B * (1 / (2 * D) + 1 / (2 * R)) / q * (W ^ 2 + a ^ 2) + A12 D B / q * cy ^ 2) +
      2 ^ 27 * 5 * Z4s D * B / q ^ 2 * (W ^ 2 + a ^ 2) +
      2 ^ 21 * Z4s D * Real.sqrt (Zs D) * B / q ^ 2 * (W ^ 2 + a ^ 2) := by
    simp only [A11, B11g, A13]
    ring
  rw [e]
  simp only [X11]
  linarith only [t1, t2, t3, t4, t5]

/-! ### The kinetic integrals on a piece -/

section Piece

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- The kinetic density `W² + a²` of the slow field. -/
def kinD (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  slowWiener r g y u ^ 2 + slowNorm 1 r g y u ^ 2

lemma kinD_nonneg (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : 0 ≤ kinD r g y u := by
  unfold kinD
  positivity

/-- `kinD` is continuous on the lifespan. -/
lemma kinD_cont (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    ContinuousOn (kinD r g y) (Icc 0 b) := by
  obtain ⟨-, -, c1, -, c3, -, -, -⟩ := norms_continuous h hb hbT
  exact (c3.pow 2).add (c1.pow 2)

/-- **The kinetic density on a piece of length at most four.** -/
theorem kinD_piece_le (h : ActualSol μ φ r g y Ty) {C ex R : ℝ}
    {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} {s t : ℝ}
    (hO : SlowOut C ex R Sl r g y s t) (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty)
    (hlen : t - s ≤ 4) :
    IntervalIntegrable (kinD r g y) volume s t ∧
      ∫ u in s..t, kinD r g y u ≤ 8 * (C * ex * R ^ 2) := by
  have ht0 := hs.trans hst
  have hc := kinD_cont h ht0 ht
  have sub : ∀ a b : ℝ, s ≤ a → a ≤ b → b ≤ t → IntervalIntegrable (kinD r g y) volume a b := by
    intro a b ha hab hb
    refine (hc.mono ?_).intervalIntegrable
    rw [uIcc_of_le hab]
    exact Icc_subset_Icc (hs.trans ha) hb
  refine ⟨sub s t le_rfl hst le_rfl, ?_⟩
  obtain ⟨-, -, c1, -, c3, -, -, -⟩ := norms_continuous h ht0 ht
  have unit : ∀ a b : ℝ, s ≤ a → a ≤ b → b ≤ t → b - a ≤ 1 →
      ∫ u in a..b, kinD r g y u ≤ 2 * (C * ex * R ^ 2) := by
    intro a b ha hab hb hl
    obtain ⟨k1, k2⟩ := hO.kin a b ha hab hb hl
    have hsub : uIcc a b ⊆ Icc 0 t := by
      rw [uIcc_of_le hab]
      exact Icc_subset_Icc (hs.trans ha) hb
    have i1 : IntervalIntegrable (fun u => slowWiener r g y u ^ 2) volume a b :=
      ((c3.mono hsub).pow 2).intervalIntegrable
    have i2 : IntervalIntegrable (fun u => slowNorm 1 r g y u ^ 2) volume a b :=
      ((c1.mono hsub).pow 2).intervalIntegrable
    have e : ∫ u in a..b, kinD r g y u = (∫ u in a..b, slowWiener r g y u ^ 2) +
        ∫ u in a..b, slowNorm 1 r g y u ^ 2 := by
      simp only [kinD]
      exact intervalIntegral.integral_add i1 i2
    rw [e]
    linarith
  set d := (t - s) / 4 with hd
  have hd0 : 0 ≤ d := by simp only [hd]; linarith
  have hd1 : d ≤ 1 := by simp only [hd]; linarith
  have e1 : s + 4 * d = t := by simp only [hd]; ring
  have p1 := sub s (s + d) le_rfl (by linarith) (by linarith)
  have p2 := sub (s + d) (s + 2 * d) (by linarith) (by linarith) (by linarith)
  have p3 := sub (s + 2 * d) (s + 3 * d) (by linarith) (by linarith) (by linarith)
  have p4 := sub (s + 3 * d) t (by linarith) (by linarith) le_rfl
  have u1 := unit s (s + d) le_rfl (by linarith) (by linarith) (by linarith)
  have u2 := unit (s + d) (s + 2 * d) (by linarith) (by linarith) (by linarith) (by linarith)
  have u3 := unit (s + 2 * d) (s + 3 * d) (by linarith) (by linarith) (by linarith) (by linarith)
  have u4 := unit (s + 3 * d) t (by linarith) (by linarith) le_rfl (by linarith)
  have s1 := intervalIntegral.integral_add_adjacent_intervals p1 p2
  have s2 := intervalIntegral.integral_add_adjacent_intervals (p1.trans p2) p3
  have s3 := intervalIntegral.integral_add_adjacent_intervals ((p1.trans p2).trans p3) p4
  linarith

end Piece

end OVNS.Quant.Metric

end
