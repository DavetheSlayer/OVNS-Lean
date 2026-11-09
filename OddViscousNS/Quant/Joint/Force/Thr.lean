import OddViscousNS.Quant.Joint.Force.Piece

/-!
# Roles 29, 30, 32: the thresholds of the force pairs (step J5, node N12)

Seven pairs (linear, quadratic) of monomials, in the order of LOCAL363, Body 40, Body 41:

| # | pair | linear `X ≤ q^e` | quadratic |
|---|---|---|---|
| 1 | direct + native (`1 + 48 c₄ P_F`) | `E₁ h_L ≤ q` | `E₁ h_Q ≤ q²` |
| 2 | comparable `X₁` | `E₂ h_L ≤ q^{3/2}` | `E₂ h_Q ≤ q^{5/2}` |
| 3 | separated `X₁` | `E₃ j_L ≤ q²` | `E₃ j_Q ≤ q³` |
| 4 | low `X₂`, ordinary | `E₄ h_L ≤ q²` | `E₄ h_Q ≤ q³` |
| 5 | low `X₂`, heat | `E₅ h_L ≤ q³` | `E₅ h_Q ≤ q⁴` |
| 6 | `Z` | `E₆ h_L ≤ q^{15/8}` | `E₆ h_Q ≤ q^{23/8}` |
| 7 | high `X₂` | `E₇ j_L ≤ q²` | `E₇ j_Q ≤ q³` |

Pairs 4, 5 are one low `X₂` (Body 41's "four low terms"), pairs 1–3 the five groups' first three of
LOCAL363.  The first column is role 29, the second role 30; role 32, the native filter, is the
first row: "a combined source is charged once".  `role29J`, `role30J` are the sums of the roots.

`budG_le`: at `q ≥ role29J + role30J`, `∫ GF ≤ 2⁻¹²`, that is `‖g‖_{L²} ≤ 1/64`, LOCAL363's
tolerance.  The logarithm of `Z` is paid by `1 + ln q ≤ 9 q^{1/8}`: `q^{15/8}` in place of `q²`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### Roots -/

/-- The least `q` with `X ≤ q^e`. -/
def rootQ (e X : ℝ) : ℝ := X ^ (1 / e)

lemma rootQ_nonneg (e : ℝ) {X : ℝ} (hX : 0 ≤ X) : 0 ≤ rootQ e X := Real.rpow_nonneg hX _

lemma le_rpow_of_rootQ {e X q : ℝ} (he : 0 < e) (hX : 0 ≤ X) (h : rootQ e X ≤ q) : X ≤ q ^ e := by
  have h1 := Real.rpow_le_rpow (rootQ_nonneg e hX) h he.le
  rwa [rootQ, ← Real.rpow_mul hX, one_div, inv_mul_cancel₀ he.ne', Real.rpow_one] at h1

/-- One monomial is paid. -/
lemma mono_paid {E m q a b : ℝ} (hq : 0 < q) (hE : 0 ≤ E) (hm : 0 ≤ m)
    (h : rootQ (a + b) (2 ^ 12 * (E * m)) ≤ q) (hab : 0 < a + b) :
    E / q ^ a * (m / q ^ b) ≤ 1 / 2 ^ 12 := by
  have h1 := le_rpow_of_rootQ hab (by positivity) h
  rw [Real.rpow_add hq] at h1
  have ha := Real.rpow_pos_of_pos hq a
  have hb := Real.rpow_pos_of_pos hq b
  have e1 : E / q ^ a * (m / q ^ b) = (E * m) / (q ^ a * q ^ b) := by
    field_simp
  rw [e1, div_le_iff₀ (by positivity)]
  linarith

/-! ### The monomials -/

/-- The `Z` pair: the logarithm is paid by the power `q^{1/8}`. -/
def E6c (M : ℝ) (caps : Caps) : ℝ := 18 * CZh * (1 + M) * cp caps.BS

/-- The high `X₂` pair: `C B (C_y/D + δ₀)`, `C_y = 2 √P_S(1)`. -/
def E7c (C ex R D : ℝ) (caps : Caps) : ℝ :=
  4 * Cm2 * cp caps.BS * (Real.sqrt (slowPrice C ex R 1) / D + delta0)

/-- **Role 29**: the linear monomials. -/
def role29J (φ D M C ex R : ℝ) (caps : Caps) : ℝ :=
  rootQ (0 + 1) (2 ^ 12 * (E1c caps * hLc φ caps)) +
    rootQ (1 / 2 + 1) (2 ^ 12 * (E2c caps * hLc φ caps)) +
    rootQ (1 + 1) (2 ^ 12 * (E3c C ex R caps * jLc φ caps)) +
    rootQ (1 + 1) (2 ^ 12 * (E4c D caps * hLc φ caps)) +
    rootQ (2 + 1) (2 ^ 12 * (E5c D caps * hLc φ caps)) +
    rootQ (7 / 8 + 1) (2 ^ 12 * (E6c M caps * hLc φ caps)) +
    rootQ (1 + 1) (2 ^ 12 * (E7c C ex R D caps * jLc φ caps))

/-- **Role 30**: the quadratic monomials. -/
def role30J (φ D M C ex R : ℝ) (caps : Caps) : ℝ :=
  rootQ (0 + 2) (2 ^ 12 * (E1c caps * hQc φ)) +
    rootQ (1 / 2 + 2) (2 ^ 12 * (E2c caps * hQc φ)) +
    rootQ (1 + 2) (2 ^ 12 * (E3c C ex R caps * jQc φ)) +
    rootQ (1 + 2) (2 ^ 12 * (E4c D caps * hQc φ)) +
    rootQ (2 + 2) (2 ^ 12 * (E5c D caps * hQc φ)) +
    rootQ (7 / 8 + 2) (2 ^ 12 * (E6c M caps * hQc φ)) +
    rootQ (1 + 2) (2 ^ 12 * (E7c C ex R D caps * jQc φ))

variable {φ D M C ex R r : ℝ} {caps : Caps}

lemma hLc_nonneg (hφ : 0 ≤ φ) (caps : Caps) : 0 ≤ hLc φ caps := by
  have := c4_pos
  unfold hLc
  positivity

lemma hQc_nonneg (φ : ℝ) : 0 ≤ hQc φ := by
  have := c4_pos
  unfold hQc
  positivity

lemma jLc_nonneg (hφ : 0 ≤ φ) (caps : Caps) : 0 ≤ jLc φ caps := by
  have := c4_pos
  have := cp_nonneg caps.BS
  have := cp_nonneg caps.yF
  unfold jLc
  positivity

lemma jQc_nonneg (φ : ℝ) : 0 ≤ jQc φ := by
  have := c4_pos
  unfold jQc
  positivity

lemma E3c_nonneg (C ex R : ℝ) (caps : Caps) : 0 ≤ E3c C ex R caps := by
  have := c4_pos
  have := Real.sqrt_nonneg (chistSq C ex R caps)
  unfold E3c
  positivity

lemma E6c_nonneg (hM : 0 ≤ M) (caps : Caps) : 0 ≤ E6c M caps := by
  have := CZh_pos
  have := cp_nonneg caps.BS
  unfold E6c
  positivity

lemma E7c_nonneg (hD : 0 ≤ D) (C ex R : ℝ) (caps : Caps) : 0 ≤ E7c C ex R D caps := by
  have := Cm2_pos
  have := cp_nonneg caps.BS
  have := delta0_pos
  have := Real.sqrt_nonneg (slowPrice C ex R 1)
  unfold E7c
  positivity

/-- The logarithm against a power. -/
lemma one_add_log_le {q : ℝ} (hq : 1 ≤ q) : 1 + Real.log q ≤ 9 * q ^ ((1 : ℝ) / 8) := by
  have h1 := Real.log_le_rpow_div (by linarith : 0 ≤ q) (by norm_num : (0 : ℝ) < 1 / 8)
  have h2 : (1 : ℝ) ≤ q ^ ((1 : ℝ) / 8) := Real.one_le_rpow hq (by norm_num)
  have e : q ^ ((1 : ℝ) / 8) / (1 / 8) = 8 * q ^ ((1 : ℝ) / 8) := by ring
  rw [e] at h1
  linarith

/-- The `Z` coefficient against its power. -/
lemma Zt_le (hq : 1 ≤ |r|) (hM : 0 ≤ M) (caps : Caps) :
    2 * (CZh / |r| * (1 + M * (1 + Real.log |r|)) * cp caps.BS) ≤
      E6c M caps / |r| ^ ((7 : ℝ) / 8) := by
  have hq0 : 0 < |r| := by linarith
  have hL := Real.log_nonneg hq
  have hB := cp_nonneg caps.BS
  have hZ := CZh_pos
  have h1 : 1 + M * (1 + Real.log |r|) ≤ (1 + M) * (1 + Real.log |r|) := by nlinarith only [hL, hM]
  have h2 := one_add_log_le hq
  have h3 : (1 + M) * (1 + Real.log |r|) ≤ (1 + M) * (9 * |r| ^ ((1 : ℝ) / 8)) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have hp : |r| ^ ((7 : ℝ) / 8) * |r| ^ ((1 : ℝ) / 8) = |r| := by
    rw [← Real.rpow_add hq0]
    norm_num
  have hp0 := Real.rpow_pos_of_pos hq0 ((7 : ℝ) / 8)
  have hp1 := Real.rpow_pos_of_pos hq0 ((1 : ℝ) / 8)
  have key : ∀ a b : ℝ, 0 < a → 0 < b → E6c M caps / a =
      2 * (CZh / (a * b) * ((1 + M) * (9 * b)) * cp caps.BS) := fun a b ha hb => by
    unfold E6c
    field_simp
    ring
  have e := key _ _ hp0 hp1
  rw [hp] at e
  rw [e]
  have h5 := h1.trans h3
  gcongr

/-! ### The payment -/

/-- The coefficient as a sum of the five powers. -/
lemma gA_le (hq : 1 ≤ |r|) (hM : 0 ≤ M) (D : ℝ) (caps : Caps) :
    gA D M r caps ≤ E1c caps / |r| ^ (0 : ℝ) + E2c caps / |r| ^ ((1 : ℝ) / 2) +
      E4c D caps / |r| ^ (1 : ℝ) + E5c D caps / |r| ^ (2 : ℝ) +
      E6c M caps / |r| ^ ((7 : ℝ) / 8) := by
  have h := Zt_le hq hM caps
  rw [Real.rpow_zero, div_one, ← Real.sqrt_eq_rpow, Real.rpow_one, Real.rpow_two]
  unfold gA
  linarith

private lemma seven_le {a1 a2 a3 a4 a5 a6 a7 q : ℝ} (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3)
    (h4 : 0 ≤ a4) (h5 : 0 ≤ a5) (h6 : 0 ≤ a6) (h7 : 0 ≤ a7)
    (h : a1 + a2 + a3 + a4 + a5 + a6 + a7 ≤ q) :
    a1 ≤ q ∧ a2 ≤ q ∧ a3 ≤ q ∧ a4 ≤ q ∧ a5 ≤ q ∧ a6 ≤ q ∧ a7 ≤ q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The arithmetic of the payment. -/
private lemma pay_arith {a x y b c d f A2 A3 : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hA1 : a * (x + y) ≤ 10 / 2 ^ 12) (h2 : 0 ≤ A2) (h3 : 0 ≤ A3)
    (hb : b * (c + d + f) ≤ A2 ^ 2 + A3 ^ 2) (hA2 : A2 ≤ 2 / 2 ^ 12) (hA3 : A3 ≤ 2 / 2 ^ 12) :
    4 * (a ^ 2 * (3 * x ^ 2 + 3 * y ^ 2) + b * (c + d + f)) ≤ 1 / 2 ^ 12 := by
  have h0 : 0 ≤ a * (x + y) := by positivity
  have h1 : (a * (x + y)) ^ 2 ≤ (10 / 2 ^ 12) ^ 2 := pow_le_pow_left₀ h0 hA1 2
  have h4 : a ^ 2 * (3 * x ^ 2 + 3 * y ^ 2) ≤ 3 * (a * (x + y)) ^ 2 := by
    have : 0 ≤ a ^ 2 * (x * y) := by positivity
    nlinarith only [this]
  have h5 : A2 ^ 2 ≤ (2 / 2 ^ 12) ^ 2 := pow_le_pow_left₀ h2 hA2 2
  have h6 : A3 ^ 2 ≤ (2 / 2 ^ 12) ^ 2 := pow_le_pow_left₀ h3 hA3 2
  norm_num at h1 h5 h6 ⊢
  linarith

/-- **Roles 29, 30 pay the force**: `∫ GF ≤ 2⁻¹²`, i.e. `‖g‖_{L²} ≤ 1/64`. -/
theorem budG_le (hφ : 0 ≤ φ) (h0 : 0 ≤ C * ex) (hR : 0 ≤ R) (hD : 1 ≤ D) (hM : 0 ≤ M)
    (hq1 : 1 ≤ |r|) (h29 : role29J φ D M C ex R caps ≤ |r|)
    (h30 : role30J φ D M C ex R caps ≤ |r|) :
    budG φ D M r C ex R caps ≤ 1 / 2 ^ 12 := by
  have hq : 0 < |r| := by linarith
  have hD0 : 0 < D := by linarith
  have hE1 := E1c_nonneg caps
  have hE2 := E2c_nonneg caps
  have hE3 := E3c_nonneg C ex R caps
  have hE4 := E4c_nonneg hD caps
  have hE5 := E5c_nonneg hD caps
  have hE6 := E6c_nonneg hM caps
  have hE7 := E7c_nonneg hD0.le C ex R caps
  have hhL := hLc_nonneg hφ caps
  have hhQ := hQc_nonneg φ
  have hjL := jLc_nonneg hφ caps
  have hjQ := jQc_nonneg φ
  have r0 : ∀ {e X : ℝ}, 0 ≤ X → 0 ≤ rootQ e X := fun hX => rootQ_nonneg _ hX
  have n : ∀ {E m : ℝ}, 0 ≤ E → 0 ≤ m → 0 ≤ 2 ^ 12 * (E * m) := fun hE hm => by positivity
  -- the fourteen roots
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ : rootQ (0 + 1) (2 ^ 12 * (E1c caps * hLc φ caps)) ≤ |r| ∧
      rootQ (1 / 2 + 1) (2 ^ 12 * (E2c caps * hLc φ caps)) ≤ |r| ∧
      rootQ (1 + 1) (2 ^ 12 * (E3c C ex R caps * jLc φ caps)) ≤ |r| ∧
      rootQ (1 + 1) (2 ^ 12 * (E4c D caps * hLc φ caps)) ≤ |r| ∧
      rootQ (2 + 1) (2 ^ 12 * (E5c D caps * hLc φ caps)) ≤ |r| ∧
      rootQ (7 / 8 + 1) (2 ^ 12 * (E6c M caps * hLc φ caps)) ≤ |r| ∧
      rootQ (1 + 1) (2 ^ 12 * (E7c C ex R D caps * jLc φ caps)) ≤ |r| := by
    exact seven_le (r0 (n hE1 hhL)) (r0 (n hE2 hhL)) (r0 (n hE3 hjL)) (r0 (n hE4 hhL))
      (r0 (n hE5 hhL)) (r0 (n hE6 hhL)) (r0 (n hE7 hjL)) h29
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ : rootQ (0 + 2) (2 ^ 12 * (E1c caps * hQc φ)) ≤ |r| ∧
      rootQ (1 / 2 + 2) (2 ^ 12 * (E2c caps * hQc φ)) ≤ |r| ∧
      rootQ (1 + 2) (2 ^ 12 * (E3c C ex R caps * jQc φ)) ≤ |r| ∧
      rootQ (1 + 2) (2 ^ 12 * (E4c D caps * hQc φ)) ≤ |r| ∧
      rootQ (2 + 2) (2 ^ 12 * (E5c D caps * hQc φ)) ≤ |r| ∧
      rootQ (7 / 8 + 2) (2 ^ 12 * (E6c M caps * hQc φ)) ≤ |r| ∧
      rootQ (1 + 2) (2 ^ 12 * (E7c C ex R D caps * jQc φ)) ≤ |r| := by
    exact seven_le (r0 (n hE1 hhQ)) (r0 (n hE2 hhQ)) (r0 (n hE3 hjQ)) (r0 (n hE4 hhQ))
      (r0 (n hE5 hhQ)) (r0 (n hE6 hhQ)) (r0 (n hE7 hjQ)) h30
  -- the monomials
  set x := hLc φ caps / |r| ^ (1 : ℝ) with hx
  set y := hQc φ / |r| ^ (2 : ℝ) with hy
  set ε : ℝ := 1 / 2 ^ 12 with hε
  have m1 := mono_paid hq hE1 hhL l1 (by norm_num)
  have m2 := mono_paid hq hE2 hhL l2 (by norm_num)
  have m4 := mono_paid hq hE4 hhL l4 (by norm_num)
  have m5 := mono_paid hq hE5 hhL l5 (by norm_num)
  have m6 := mono_paid hq hE6 hhL l6 (by norm_num)
  have n1 := mono_paid hq hE1 hhQ k1 (by norm_num)
  have n2 := mono_paid hq hE2 hhQ k2 (by norm_num)
  have n4 := mono_paid hq hE4 hhQ k4 (by norm_num)
  have n5 := mono_paid hq hE5 hhQ k5 (by norm_num)
  have n6 := mono_paid hq hE6 hhQ k6 (by norm_num)
  have m3 := mono_paid hq hE3 hjL l3 (by norm_num)
  have n3 := mono_paid hq hE3 hjQ k3 (by norm_num)
  have m7 := mono_paid hq hE7 hjL l7 (by norm_num)
  have n7 := mono_paid hq hE7 hjQ k7 (by norm_num)
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hg := gA_le hq1 hM D caps
  have hg0 := gA_nonneg hD hM hq1 caps
  set G := E1c caps / |r| ^ (0 : ℝ) + E2c caps / |r| ^ ((1 : ℝ) / 2) +
      E4c D caps / |r| ^ (1 : ℝ) + E5c D caps / |r| ^ (2 : ℝ) +
      E6c M caps / |r| ^ ((7 : ℝ) / 8) with hG
  have hA1 : gA D M r caps * (x + y) ≤ 10 / 2 ^ 12 := by
    have h1 := mul_le_mul_of_nonneg_right hg (add_nonneg hx0 hy0)
    refine h1.trans ?_
    have e : G * (x + y) = E1c caps / |r| ^ (0 : ℝ) * x + E1c caps / |r| ^ (0 : ℝ) * y +
        (E2c caps / |r| ^ ((1 : ℝ) / 2) * x + E2c caps / |r| ^ ((1 : ℝ) / 2) * y) +
        (E4c D caps / |r| ^ (1 : ℝ) * x + E4c D caps / |r| ^ (1 : ℝ) * y) +
        (E5c D caps / |r| ^ (2 : ℝ) * x + E5c D caps / |r| ^ (2 : ℝ) * y) +
        (E6c M caps / |r| ^ ((7 : ℝ) / 8) * x + E6c M caps / |r| ^ ((7 : ℝ) / 8) * y) := by
      rw [hG]
      ring
    rw [e]
    have e10 : (10 : ℝ) / 2 ^ 12 = 10 * ε := by rw [hε]; ring
    rw [e10]
    linarith
  -- the two norms
  have hSh : Shc φ r caps = jLc φ caps / |r| ^ (1 : ℝ) + jQc φ / |r| ^ (2 : ℝ) := by
    rw [Real.rpow_one, Real.rpow_two]
    rfl
  set A2 := E3c C ex R caps / |r| ^ (1 : ℝ) * Shc φ r caps with hA2d
  set A3 := E7c C ex R D caps / |r| ^ (1 : ℝ) * Shc φ r caps with hA3d
  have hS0 := Shc_nonneg hφ r caps
  have hA20 : 0 ≤ A2 := by positivity
  have hA30 : 0 ≤ A3 := by positivity
  have hA2 : A2 ≤ 2 / 2 ^ 12 := by
    rw [hA2d, hSh, mul_add]
    have e : (2 : ℝ) / 2 ^ 12 = ε + ε := by rw [hε]; ring
    rw [e]
    exact add_le_add m3 n3
  have hA3 : A3 ≤ 2 / 2 ^ 12 := by
    rw [hA3d, hSh, mul_add]
    have e : (2 : ℝ) / 2 ^ 12 = ε + ε := by rw [hε]; ring
    rw [e]
    exact add_le_add m7 n7
  -- the slow constants
  have hPy : 0 ≤ slowPrice C ex R 1 := by
    have h1 : 0 ≤ R ^ 4 + 1 * R ^ 5 := by positivity
    exact mul_nonneg h0 h1
  have hCh : 0 ≤ chistSq C ex R caps := by
    have h1 : 0 ≤ J3pre 4 caps := by
      have := cp_nonneg caps.yF
      have := cp_nonneg caps.JS
      unfold J3pre
      positivity
    unfold chistSq
    positivity
  have hxe : x = hLc φ caps / |r| := by rw [hx, Real.rpow_one]
  have hye : y = hQc φ / |r| ^ 2 := by rw [hy, Real.rpow_two]
  have hbud : Shc φ r caps ^ 2 * ((2 ^ 11 * c4 / |r|) ^ 2 * chistSq C ex R caps +
      (2 * Cm2 / |r| * cp caps.BS / D) ^ 2 * (4 * slowPrice C ex R 1) +
      4 * (2 * Cm2 / |r| * cp caps.BS * delta0) ^ 2) ≤ A2 ^ 2 + A3 ^ 2 := by
    set Py := slowPrice C ex R 1
    have e1 : A2 ^ 2 = Shc φ r caps ^ 2 * ((2 ^ 11 * c4 / |r|) ^ 2 * chistSq C ex R caps) := by
      rw [hA2d, Real.rpow_one, mul_pow, div_pow, E3c, mul_pow, Real.sq_sqrt hCh]
      field_simp
    have hs : Real.sqrt Py ^ 2 = Py := Real.sq_sqrt hPy
    have e2 : A3 ^ 2 = Shc φ r caps ^ 2 * ((4 * Cm2 * cp caps.BS / |r|) ^ 2 *
        (Real.sqrt Py / D + delta0) ^ 2) := by
      rw [hA3d, Real.rpow_one, E7c]
      ring
    have e3 : (2 * Cm2 / |r| * cp caps.BS / D) ^ 2 * (4 * Py) +
        4 * (2 * Cm2 / |r| * cp caps.BS * delta0) ^ 2 =
        (4 * Cm2 * cp caps.BS / |r|) ^ 2 * ((Real.sqrt Py / D) ^ 2 + delta0 ^ 2) := by
      rw [div_pow (Real.sqrt Py) D, hs]
      ring
    have h4 : (Real.sqrt Py / D) ^ 2 + delta0 ^ 2 ≤ (Real.sqrt Py / D + delta0) ^ 2 := by
      have : 0 ≤ Real.sqrt Py / D * delta0 := by
        have := delta0_pos
        have := Real.sqrt_nonneg Py
        positivity
      nlinarith only [this]
    have h5 := mul_le_mul_of_nonneg_left h4
      (sq_nonneg (4 * Cm2 * cp caps.BS / |r|))
    have h6 := mul_le_mul_of_nonneg_left h5 (sq_nonneg (Shc φ r caps))
    rw [e1, e2]
    have e4 : Shc φ r caps ^ 2 * ((2 ^ 11 * c4 / |r|) ^ 2 * chistSq C ex R caps +
        (2 * Cm2 / |r| * cp caps.BS / D) ^ 2 * (4 * Py) +
        4 * (2 * Cm2 / |r| * cp caps.BS * delta0) ^ 2) =
        Shc φ r caps ^ 2 * ((2 ^ 11 * c4 / |r|) ^ 2 * chistSq C ex R caps) +
        Shc φ r caps ^ 2 * ((2 * Cm2 / |r| * cp caps.BS / D) ^ 2 * (4 * Py) +
          4 * (2 * Cm2 / |r| * cp caps.BS * delta0) ^ 2) := by ring
    rw [e4, e3]
    linarith
  unfold budG
  rw [← hxe, ← hye]
  exact pay_arith hg0 hx0 hy0 hA1 hA20 hA30 hbud hA2 hA3

/-! ### The force in the `H²` energy -/

lemma role29J_nonneg (hφ : 0 ≤ φ) (hD : 1 ≤ D) (hM : 0 ≤ M) (C ex R : ℝ) (caps : Caps) :
    0 ≤ role29J φ D M C ex R caps := by
  have hD0 : 0 ≤ D := by linarith
  have hE1 := E1c_nonneg caps
  have hE2 := E2c_nonneg caps
  have hE3 := E3c_nonneg C ex R caps
  have hE4 := E4c_nonneg hD caps
  have hE5 := E5c_nonneg hD caps
  have hE6 := E6c_nonneg hM caps
  have hE7 := E7c_nonneg hD0 C ex R caps
  have hhL := hLc_nonneg hφ caps
  have hjL := jLc_nonneg hφ caps
  unfold role29J
  have r0 : ∀ {e X : ℝ}, 0 ≤ X → 0 ≤ rootQ e X := fun hX => rootQ_nonneg _ hX
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_)
    ?_) ?_ <;> exact r0 (by positivity)

lemma role30J_nonneg (hD : 1 ≤ D) (hM : 0 ≤ M) (C ex R : ℝ) (caps : Caps) :
    0 ≤ role30J φ D M C ex R caps := by
  have hD0 : 0 ≤ D := by linarith
  have hE1 := E1c_nonneg caps
  have hE2 := E2c_nonneg caps
  have hE3 := E3c_nonneg C ex R caps
  have hE4 := E4c_nonneg hD caps
  have hE5 := E5c_nonneg hD caps
  have hE6 := E6c_nonneg hM caps
  have hE7 := E7c_nonneg hD0 C ex R caps
  have hhQ := hQc_nonneg φ
  have hjQ := jQc_nonneg φ
  unfold role30J
  have r0 : ∀ {e X : ℝ}, 0 ≤ X → 0 ≤ rootQ e X := fun hX => rootQ_nonneg _ hX
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_)
    ?_) ?_ <;> exact r0 (by positivity)

/-- **The force threshold of the `H²` energy**: J4's budget (for the histories) and roles 29, 30.
J5's `q₂` must dominate it. -/
def force2Q (φ D M C ex R : ℝ) (caps : Caps) : ℝ :=
  jointBudget φ caps + role29J φ D M C ex R caps + role30J φ D M C ex R caps

variable {μ : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- **The force in the `H²` energy** (LOCAL363, Bodies 40, 41): on a piece, at almost every time,
`force2 ≤ c_F²/64 + 16 GF`, with `∫ GF ≤ 2⁻¹²` on every sub-interval: "the same `c_F²/64` Young slot
and the additive `16 g²`", `‖g‖_{L²} ≤ 1/64`. -/
theorem force2_final (h : ActualSol μ φ r g y Ty)
    {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} {s t : ℝ}
    (hO : SlowOut C ex R Sl r g y s t) (h0 : 0 ≤ C * ex) (hR : 0 ≤ R) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 4) (hP : OnPrefix caps r g y s t)
    (hsup : ∀ u ∈ Icc s t, slowSup r g y u ≤ M) (hD : 1 ≤ D)
    (hq : force2Q φ D M C ex R caps ≤ |r|) :
    IntervalIntegrable (GF φ D M r g y caps) volume s t ∧
      (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → ∫ u in u₁..u₂, GF φ D M r g y caps u ≤ 1 / 2 ^ 12) ∧
      ∀ᵐ u ∂(volume.restrict (Icc s t)),
        force2 r g y u ≤ 1 / 64 * fastNorm 3 r g y u ^ 2 + 16 * GF φ D M r g y caps u := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hM : 0 ≤ M := slowSup_nonneg.trans (hsup s ⟨le_rfl, hst⟩)
  have h29 := role29J_nonneg hφ hD hM C ex R caps
  have h30 := role30J_nonneg (φ := φ) hD hM C ex R caps
  have hB : 0 ≤ jointBudget φ caps := zero_le_one.trans (jointBudget_floors hφ caps).1
  have hthr : jointBudget φ caps ≤ |r| := by
    unfold force2Q at hq
    linarith
  have hq1 : 1 ≤ |r| := (jointBudget_floors hφ caps).1.trans hthr
  obtain ⟨hI, hV, hf⟩ := force2_piece h hO h0 hR hs hst ht hlen hthr hP hsup hD
  have hbud := budG_le hφ h0 hR hD hM hq1 (R := R) (C := C) (ex := ex) (caps := caps)
    (by unfold force2Q at hq; linarith) (by unfold force2Q at hq; linarith)
  refine ⟨hI, fun u₁ u₂ h1 h2 h3 => (hV u₁ u₂ h1 h2 h3).trans hbud, ?_⟩
  filter_upwards [hf] with u hu
  have h2 := gF_sq_le φ D M r g y caps u
  set x := gF φ D M r g y caps u
  set c := fastNorm 3 r g y u
  nlinarith only [hu, h2, sq_nonneg (c / 8 - 4 * x)]

end OVNS.Quant.Metric

end
