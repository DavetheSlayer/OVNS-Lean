import OddViscousNS.Quant.Energy.Native.Defs

/-!
# Theorem 1.2, fixed force — E5/E8 native layer: the pointwise kernel (LOCAL210 §1, (1.2))

The **cyclic kernel bound** behind `Z1 = 32/(mK√(K⁴ + q²Φ²))`, reconstructed in
`OddViscousNS_data/reports/t12_leading_coeff.md` §2 (Steps 1–2) with the constant `13` in place
of LOCAL210's `4` (the constants are irrelevant in the fixed-`δ` form).

* **A. Exact differences** (LOCAL210 §1, both signs `ε`): with `f_j(s) = s^j/(εs + iz)`,
  `f₁(s) − f₁(t) = iz(s − t)/[(εs + iz)(εt + iz)]` (`fres_one_sub`) and
  `f₂(s) − f₂(t) = (s − t)[εst + iz(s + t)]/[(εs + iz)(εt + iz)]` (`fres_two_sub`), and the four
  bounds at sorted legs `m ≤ B ≤ K ≤ B + m` (so `B ≥ K/2`, `K − B ≤ m`), `D_K = √(K⁴ + z²)`:
  `|f₁(m²) − f₁(B²)| D_K ≤ 4K²`, `|f₂(m²) − f₂(B²)| D_K ≤ 12K⁴`,
  `|f₁(K²) − f₁(B²)| D_K ≤ 2mK`, `|f₂(K²) − f₂(B²)| D_K ≤ 6mK³` (`diff_*`; report §2 Step 2).
* **B. The cyclic sum** (report §2 Step 1–2): the three rootings of a triad at the same `z = rΦ`
  carry the coefficients `c_x = (Y − Z)/2`, `c_y = (Z − X)/2`, `c_z = (X − Y)/2` (signed lengths
  `X = s_x m`, `Y = s_y B`, `Z = s_z K`), which sum to zero, so
  `S_j = g Σ c_i f_j(l_i²) = g [c_x (f_j(m²) − f_j(B²)) + c_z (f_j(K²) − f_j(B²))]`.  With the two
  bounds on the common triple product `g` — `|g| ≤ 1` and the Waleffe bound
  `|g| 2√2 K ≤ |X + Y + Z|` — the two helicity cases of the large pair give
  `|S_j| ≤ 13 m K^{2j}/D_K` (`cyclic_sum_one`, `cyclic_sum_two`; same helicity: `4`, `12`;
  opposite: `6/√2`, `18/√2`).
* **C. The Waleffe triple-product identity** for the library's helical projectors
  (`waleffe`): for a zero-sum triad of nonzero modes and helical amplitudes
  `A_j = hel (s j) (ℓ j) (v j)`,
  `|[A₀, A₁, A₂]| · 2√2 |ℓ₀||ℓ₁||ℓ₂| = |x₀ + x₁ + x₂| · |ℓ₀ × ℓ₁| · ∏ ‖A_j‖`
  (`[A, B, C] = (A × B)·C` bilinear, `trip`).  Proof: each `A_j` is a multiple of the frame
  vector `|ℓ_j|² n + i x_j ℓ_j × n`, `n = ℓ₀ × ℓ₁` (the eigenvector decomposition of
  `Resonant/Orbit.lean`, replicated here), and the triple product of the three frame vectors is
  the polynomial `−|n|⁴ x₀x₁x₂(x₀ + x₁ + x₂)` (`trip_wv`); collinear triads give `0` on both
  sides.  Consequences: `|[A₀,A₁,A₂]| ≤ ∏ ‖A_j‖` (`norm_trip_le`, Lagrange) and
  `|[A₀,A₁,A₂]| 2√2 |ℓ₂| ≤ |Σ x_j| ∏ ‖A_j‖` (`waleffe_le`, from `|ℓ₀ × ℓ₁| ≤ |ℓ₀||ℓ₁|`).
* **D. The vertex as a triple product** (`tau_hel_eq_trip`): on helical amplitudes the library's
  vertex form `tau` is `((α|p| − β|q|)/2) · [A, B, C]` (from `vert_hel`), which is LOCAL210's
  `C_{pv}^k = (α|p| − β|v|) g/2`; the three rootings share `g` (`trip_cyc`).
* **E. The triad-level kernel bound** (`triad_cyclic_le`): for a sorted fast triad the cyclic sum
  of the three rootings weighted by `f_j(|out|²)` is at most `13 m K^{2j}/D_K · ∏ ‖A_j‖`, and the
  **native domination** (`native_dominated_E1/E2`): dividing by the native slot weights
  (`wgtE1`, `wgtE2`) gives `≤ (13/4) · Z1 · weight · ∏ ‖A_j‖` at each of the three positions of
  `h` (LOCAL210 (1.2) with `32` replaced by `104 = 8 · 13`; report §2 Step 2).

## Reading choices
* The report's two helicity cases are encoded by the two hypotheses on `g` (`|g| ≤ 1`, the
  Waleffe bound), which is exactly what `norm_trip_le` and `waleffe_le` supply.
* `z = rΦ` is an arbitrary real: `D_K = √(K⁴ + (rΦ)²) = √(K⁴ + |r|²Φ²)` (`sqrt_lorentz_eq`).
-/

noncomputable section

namespace OVNS.Quant

open scoped ComplexConjugate

/-! ### A. The exact differences of the cyclic scalars -/

/-- The denominator `εs + iz` of `f_j`. -/
def den (ε z s : ℝ) : ℂ := ((ε * s : ℝ) : ℂ) + (z : ℝ) * Complex.I

theorem fres_eq_div (j : ℕ) (ε z s : ℝ) : fres j ε z s = (s : ℂ) ^ j / den ε z s := by
  rw [fres, resolv, den, mul_one_div]

theorem den_ne_zero {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {s : ℝ} (hs : s ≠ 0) (z : ℝ) :
    den ε z s ≠ 0 :=
  resolv_den_ne_zero hε hs z

theorem norm_den {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (z s : ℝ) :
    ‖den ε z s‖ = Real.sqrt (s ^ 2 + z ^ 2) := by
  rw [den, Complex.norm_add_mul_I]
  rcases hε with rfl | rfl <;> ring_nf

/-- LOCAL210 §1: `f₁(s) − f₁(t) = iz(s − t)/[(εs + iz)(εt + iz)]`. -/
theorem fres_one_sub {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0)
    (z : ℝ) :
    fres 1 ε z s - fres 1 ε z t =
      ((z : ℂ) * Complex.I * ((s : ℂ) - t)) / (den ε z s * den ε z t) := by
  rw [fres_eq_div, fres_eq_div, div_sub_div _ _ (den_ne_zero hε hs z) (den_ne_zero hε ht z)]
  congr 1
  simp only [den, pow_one]
  push_cast
  ring

/-- LOCAL210 §1: `f₂(s) − f₂(t) = (s − t)[εst + iz(s + t)]/[(εs + iz)(εt + iz)]`. -/
theorem fres_two_sub {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0)
    (z : ℝ) :
    fres 2 ε z s - fres 2 ε z t =
      (((s : ℂ) - t) * (((ε * s * t : ℝ) : ℂ) + ((z * (s + t) : ℝ) : ℂ) * Complex.I)) /
        (den ε z s * den ε z t) := by
  rw [fres_eq_div, fres_eq_div, div_sub_div _ _ (den_ne_zero hε hs z) (den_ne_zero hε ht z)]
  congr 1
  simp only [den]
  push_cast
  ring

private lemma norm_ofReal_sub {s t : ℝ} (hst : s ≤ t) : ‖(s : ℂ) - t‖ = t - s := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith),
    neg_sub]

private lemma abs_le_sqrt_add {s z : ℝ} : |z| ≤ Real.sqrt (s ^ 2 + z ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])

private lemma le_sqrt_add {s z : ℝ} (hs : 0 ≤ s) : s ≤ Real.sqrt (s ^ 2 + z ^ 2) := by
  rw [Real.le_sqrt hs (by positivity)]
  nlinarith [sq_nonneg z]

/-- `|f₁(s) − f₁(t)| ≤ (t − s)/√(t² + z²)` for `0 < s ≤ t` (`|z| ≤ √(s² + z²)`). -/
theorem norm_fres_one_sub_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (z : ℝ) :
    ‖fres 1 ε z s - fres 1 ε z t‖ ≤ (t - s) / Real.sqrt (t ^ 2 + z ^ 2) := by
  have ht : 0 < t := hs.trans_le hst
  rw [fres_one_sub hε hs.ne' ht.ne', norm_div, norm_mul, norm_mul, norm_mul, norm_den hε,
    norm_den hε, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    norm_ofReal_sub hst]
  have hA : 0 < Real.sqrt (s ^ 2 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hB : 0 < Real.sqrt (t ^ 2 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hz : |z| ≤ Real.sqrt (s ^ 2 + z ^ 2) := abs_le_sqrt_add
  have hts : 0 ≤ t - s := by linarith
  rw [div_le_div_iff₀ (by positivity) hB]
  nlinarith [mul_le_mul_of_nonneg_right hz (mul_nonneg hts hB.le)]

/-- `|f₂(s) − f₂(t)| ≤ 3t(t − s)/√(t² + z²)` for `0 < s ≤ t`. -/
theorem norm_fres_two_sub_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (z : ℝ) :
    ‖fres 2 ε z s - fres 2 ε z t‖ ≤ 3 * t * (t - s) / Real.sqrt (t ^ 2 + z ^ 2) := by
  have ht : 0 < t := hs.trans_le hst
  have hA : 0 < Real.sqrt (s ^ 2 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hB : 0 < Real.sqrt (t ^ 2 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsA : s ≤ Real.sqrt (s ^ 2 + z ^ 2) := le_sqrt_add hs.le
  have hzA : |z| ≤ Real.sqrt (s ^ 2 + z ^ 2) := abs_le_sqrt_add
  have hnum : ‖((ε * s * t : ℝ) : ℂ) + ((z * (s + t) : ℝ) : ℂ) * Complex.I‖ ≤
      3 * Real.sqrt (s ^ 2 + z ^ 2) * t := by
    rw [Complex.norm_add_mul_I]
    have h1 : (ε * s * t) ^ 2 = (s * t) ^ 2 := by rcases hε with rfl | rfl <;> ring
    rw [h1]
    have h0 : 0 ≤ s + t := by linarith
    have hz2 : |z| ^ 2 * (s + t) ^ 2 = z ^ 2 * (s + t) ^ 2 := by rw [sq_abs]
    have hprod : 0 ≤ s * t * (|z| * (s + t)) :=
      mul_nonneg (mul_nonneg hs.le ht.le) (mul_nonneg (abs_nonneg z) h0)
    calc Real.sqrt ((s * t) ^ 2 + (z * (s + t)) ^ 2) ≤ s * t + |z| * (s + t) := by
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith [hz2, hprod]
      _ ≤ Real.sqrt (s ^ 2 + z ^ 2) * t + Real.sqrt (s ^ 2 + z ^ 2) * (s + t) := by gcongr
      _ ≤ 3 * Real.sqrt (s ^ 2 + z ^ 2) * t := by nlinarith
  rw [fres_two_sub hε hs.ne' ht.ne', norm_div, norm_mul, norm_mul, norm_den hε, norm_den hε,
    norm_ofReal_sub hst]
  have hts : 0 ≤ t - s := by linarith
  rw [div_le_div_iff₀ (by positivity) hB]
  nlinarith [mul_le_mul_of_nonneg_right hnum (mul_nonneg hts hB.le)]

/-- `K ≤ 2B` gives `√(K⁴ + z²) ≤ 4√(B⁴ + z²)` (LOCAL210 §1: `B₀ ≥ K/2`). -/
theorem sqrt_quartic_le {B K : ℝ} (hK : 0 ≤ K) (hKB : K ≤ 2 * B) (z : ℝ) :
    Real.sqrt (K ^ 4 + z ^ 2) ≤ 4 * Real.sqrt (B ^ 4 + z ^ 2) := by
  have h4 : K ^ 4 ≤ 16 * B ^ 4 := by
    have := pow_le_pow_left₀ hK hKB 4
    nlinarith [this]
  calc Real.sqrt (K ^ 4 + z ^ 2) ≤ Real.sqrt (16 * (B ^ 4 + z ^ 2)) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg z])
    _ = 4 * Real.sqrt (B ^ 4 + z ^ 2) := by
        rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]

/-- Small/middle legs, `j = 1`: `|f₁(m²) − f₁(B²)| D_K ≤ 4K²`. -/
theorem diff_small_one {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B)
    (hBK : B ≤ K) (htri : K ≤ B + m) :
    ‖fres 1 ε z (m ^ 2) - fres 1 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2) ≤ 4 * K ^ 2 := by
  have hB : 0 < B := hm.trans_le hmB
  have h1 := norm_fres_one_sub_le hε (s := m ^ 2) (t := B ^ 2) (by positivity)
    (pow_le_pow_left₀ hm.le hmB 2) z
  have h2 := sqrt_quartic_le (B := B) (K := K) (by linarith) (by linarith) z
  have e : (B ^ 2) ^ 2 = B ^ 4 := by ring
  rw [e] at h1
  have hpos : 0 < Real.sqrt (B ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hmB2 : m ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hm.le hmB 2
  calc ‖fres 1 ε z (m ^ 2) - fres 1 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2)
      ≤ (B ^ 2 - m ^ 2) / Real.sqrt (B ^ 4 + z ^ 2) * (4 * Real.sqrt (B ^ 4 + z ^ 2)) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (div_nonneg (by linarith) hpos.le)
    _ = 4 * (B ^ 2 - m ^ 2) := by field_simp
    _ ≤ 4 * K ^ 2 := by nlinarith [pow_le_pow_left₀ hB.le hBK 2]

/-- Small/middle legs, `j = 2`: `|f₂(m²) − f₂(B²)| D_K ≤ 12K⁴`. -/
theorem diff_small_two {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B)
    (hBK : B ≤ K) (htri : K ≤ B + m) :
    ‖fres 2 ε z (m ^ 2) - fres 2 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2) ≤ 12 * K ^ 4 := by
  have hB : 0 < B := hm.trans_le hmB
  have h1 := norm_fres_two_sub_le hε (s := m ^ 2) (t := B ^ 2) (by positivity)
    (pow_le_pow_left₀ hm.le hmB 2) z
  have h2 := sqrt_quartic_le (B := B) (K := K) (by linarith) (by linarith) z
  have e : (B ^ 2) ^ 2 = B ^ 4 := by ring
  rw [e] at h1
  have hpos : 0 < Real.sqrt (B ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hmB2 : m ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hm.le hmB 2
  have hBK4 : B ^ 4 ≤ K ^ 4 := pow_le_pow_left₀ hB.le hBK 4
  calc ‖fres 2 ε z (m ^ 2) - fres 2 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2)
      ≤ 3 * B ^ 2 * (B ^ 2 - m ^ 2) / Real.sqrt (B ^ 4 + z ^ 2) *
          (4 * Real.sqrt (B ^ 4 + z ^ 2)) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (div_nonneg (by nlinarith) hpos.le)
    _ = 12 * (B ^ 2 * (B ^ 2 - m ^ 2)) := by field_simp; ring
    _ ≤ 12 * K ^ 4 := by nlinarith [sq_nonneg m, sq_nonneg B]

/-- Large/middle legs, `j = 1`: `|f₁(K²) − f₁(B²)| D_K ≤ 2mK` (`K − B ≤ m`). -/
theorem diff_large_one {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B)
    (hBK : B ≤ K) (htri : K ≤ B + m) :
    ‖fres 1 ε z (K ^ 2) - fres 1 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2) ≤ 2 * m * K := by
  have hB : 0 < B := hm.trans_le hmB
  have h1 := norm_fres_one_sub_le hε (s := B ^ 2) (t := K ^ 2) (by positivity)
    (pow_le_pow_left₀ hB.le hBK 2) z
  have e : (K ^ 2) ^ 2 = K ^ 4 := by ring
  rw [e, ← norm_sub_rev] at h1
  have hK : 0 < K := hB.trans_le hBK
  have hpos : 0 < Real.sqrt (K ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  calc ‖fres 1 ε z (K ^ 2) - fres 1 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2)
      ≤ (K ^ 2 - B ^ 2) / Real.sqrt (K ^ 4 + z ^ 2) * Real.sqrt (K ^ 4 + z ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hpos.le
    _ = K ^ 2 - B ^ 2 := by field_simp
    _ ≤ 2 * m * K := by nlinarith

/-- Large/middle legs, `j = 2`: `|f₂(K²) − f₂(B²)| D_K ≤ 6mK³`. -/
theorem diff_large_two {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B)
    (hBK : B ≤ K) (htri : K ≤ B + m) :
    ‖fres 2 ε z (K ^ 2) - fres 2 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2) ≤ 6 * m * K ^ 3 := by
  have hB : 0 < B := hm.trans_le hmB
  have h1 := norm_fres_two_sub_le hε (s := B ^ 2) (t := K ^ 2) (by positivity)
    (pow_le_pow_left₀ hB.le hBK 2) z
  have e : (K ^ 2) ^ 2 = K ^ 4 := by ring
  rw [e, ← norm_sub_rev] at h1
  have hK : 0 < K := hB.trans_le hBK
  have hpos : 0 < Real.sqrt (K ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hKB : K ^ 2 - B ^ 2 ≤ 2 * m * K := by nlinarith
  calc ‖fres 2 ε z (K ^ 2) - fres 2 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2)
      ≤ 3 * K ^ 2 * (K ^ 2 - B ^ 2) / Real.sqrt (K ^ 4 + z ^ 2) * Real.sqrt (K ^ 4 + z ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hpos.le
    _ = 3 * K ^ 2 * (K ^ 2 - B ^ 2) := by field_simp
    _ ≤ 3 * K ^ 2 * (2 * m * K) := mul_le_mul_of_nonneg_left hKB (by positivity)
    _ = 6 * m * K ^ 3 := by ring

/-! ### B. The cyclic sum of the three rootings -/

/-- The cyclic collection (report §2 Step 1): with `c_x + c_y + c_z = 0`,
`|g(c_x f₁ + c_y f₂ + c_z f₃)| ≤ |g| (|c_x| |f₁ − f₂| + |c_z| |f₃ − f₂|)` ("subtract the
middle-root value with the same `z`", LOCAL210 §1). -/
theorem cyclic_split (cx cy cz : ℝ) (hsum : cx + cy + cz = 0) (g f₁ f₂ f₃ : ℂ) :
    ‖g * ((cx : ℂ) * f₁ + (cy : ℂ) * f₂ + (cz : ℂ) * f₃)‖ ≤
      ‖g‖ * (|cx| * ‖f₁ - f₂‖ + |cz| * ‖f₃ - f₂‖) := by
  have hcy : (cy : ℂ) = -cx - cz := by
    have : cy = -cx - cz := by linarith
    rw [this]
    push_cast
    ring
  have e : (cx : ℂ) * f₁ + (cy : ℂ) * f₂ + (cz : ℂ) * f₃ =
      (cx : ℂ) * (f₁ - f₂) + (cz : ℂ) * (f₃ - f₂) := by
    rw [hcy]
    ring
  rw [e, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

private lemma sqrt_two_bounds : (1.4 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 1.5 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [Real.sqrt_le_left (by norm_num)]
    norm_num

/-- `|c_z| = |X − Y|/2 ≤ (m + B)/2 ≤ K` for any signs. -/
private lemma abs_cz_le {m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B) (hBK : B ≤ K) (sx sy : Sgn) :
    |(sg sx * m - sg sy * B) / 2| ≤ K := by
  rw [abs_le]
  cases sx <;> cases sy <;> simp only [sg, ↓reduceIte, Bool.false_eq_true] <;>
    constructor <;> linarith

/-- Same helicity on the two large legs: `|c_x| = (K − B)/2 ≤ m/2`. -/
private lemma abs_cx_same {m B K : ℝ} (hBK : B ≤ K) (htri : K ≤ B + m) (s : Sgn) :
    |(sg s * B - sg s * K) / 2| ≤ m / 2 := by
  rw [abs_le]
  cases s <;> simp only [sg, ↓reduceIte, Bool.false_eq_true] <;> constructor <;> linarith

/-- Opposite helicity on the two large legs: `|c_x| = (B + K)/2 ≤ K`. -/
private lemma abs_cx_opp {m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B) (hBK : B ≤ K) (s : Sgn) :
    |(sg s * B - (-sg s) * K) / 2| ≤ K := by
  rw [abs_le]
  cases s <;> simp only [sg, ↓reduceIte, Bool.false_eq_true] <;> constructor <;> linarith

/-- Opposite helicity on the two large legs: `|X + Y + Z| ≤ m + (K − B) ≤ 2m`. -/
private lemma abs_sum_opp {m B K : ℝ} (hm : 0 < m) (hBK : B ≤ K) (htri : K ≤ B + m)
    (sx s : Sgn) : |sg sx * m + sg s * B + (-sg s) * K| ≤ 2 * m := by
  rw [abs_le]
  cases sx <;> cases s <;> simp only [sg, ↓reduceIte, Bool.false_eq_true] <;>
    constructor <;> linarith

private lemma sg_of_ne {a b : Sgn} (h : ¬ a = b) : sg b = -sg a := by
  cases a <;> cases b <;> simp_all [sg]

/-- **The cyclic kernel bound, `j = 1`** (report §2 Step 2; LOCAL210 §1 `|S₁| ≤ 4mK²/D_K` with
`4` replaced by `13`).  Sorted legs `0 < m ≤ B ≤ K ≤ B + m` with helicities `s_x, s_y, s_z`
(signed lengths `X = s_x m`, `Y = s_y B`, `Z = s_z K`), the common triple product `g` with
`|g| ≤ 1` and the Waleffe bound `|g| 2√2 K ≤ |X + Y + Z|`, and the cyclic coefficients
`c_x = (Y − Z)/2` on the rooting with output `m`, `c_y = (Z − X)/2` on output `B`,
`c_z = (X − Y)/2` on output `K`: `|g Σ c_i f₁(l_i²)| ≤ 13 m K²/√(K⁴ + z²)`. -/
theorem cyclic_sum_one {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (z : ℝ) {m B K : ℝ} (hm : 0 < m)
    (hmB : m ≤ B) (hBK : B ≤ K) (htri : K ≤ B + m) (sx sy sz : Sgn) (g : ℂ) (hg1 : ‖g‖ ≤ 1)
    (hgW : ‖g‖ * (2 * Real.sqrt 2 * K) ≤ |sg sx * m + sg sy * B + sg sz * K|) :
    ‖g * ((((sg sy * B - sg sz * K) / 2 : ℝ) : ℂ) * fres 1 ε z (m ^ 2) +
        (((sg sz * K - sg sx * m) / 2 : ℝ) : ℂ) * fres 1 ε z (B ^ 2) +
        (((sg sx * m - sg sy * B) / 2 : ℝ) : ℂ) * fres 1 ε z (K ^ 2))‖ ≤
      13 * m * K ^ 2 / Real.sqrt (K ^ 4 + z ^ 2) := by
  have hB : 0 < B := hm.trans_le hmB
  have hK : 0 < K := hB.trans_le hBK
  have hD : 0 < Real.sqrt (K ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have h1 := cyclic_split ((sg sy * B - sg sz * K) / 2) ((sg sz * K - sg sx * m) / 2)
    ((sg sx * m - sg sy * B) / 2) (by ring) g (fres 1 ε z (m ^ 2)) (fres 1 ε z (B ^ 2))
    (fres 1 ε z (K ^ 2))
  have hd1 := diff_small_one hε (z := z) hm hmB hBK htri
  have hd2 := diff_large_one hε (z := z) hm hmB hBK htri
  have hcz := abs_cz_le hm hmB hBK sx sy
  rw [le_div_iff₀ hD]
  refine (mul_le_mul_of_nonneg_right h1 hD.le).trans ?_
  have e : ‖g‖ * (|(sg sy * B - sg sz * K) / 2| * ‖fres 1 ε z (m ^ 2) - fres 1 ε z (B ^ 2)‖ +
      |(sg sx * m - sg sy * B) / 2| * ‖fres 1 ε z (K ^ 2) - fres 1 ε z (B ^ 2)‖) *
        Real.sqrt (K ^ 4 + z ^ 2) =
      ‖g‖ * (|(sg sy * B - sg sz * K) / 2| *
        (‖fres 1 ε z (m ^ 2) - fres 1 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2)) +
        |(sg sx * m - sg sy * B) / 2| *
        (‖fres 1 ε z (K ^ 2) - fres 1 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2))) := by ring
  rw [e]
  by_cases hs : sy = sz
  · subst hs
    have hcx := abs_cx_same hBK htri sy
    calc _ ≤ 1 * (m / 2 * (4 * K ^ 2) + K * (2 * m * K)) := by gcongr
      _ ≤ 13 * m * K ^ 2 := by nlinarith [mul_pos hm hK]
  · have hsz := sg_of_ne hs
    rw [hsz] at hgW ⊢
    have hcx := abs_cx_opp hm hmB hBK sy
    have hXYZ := abs_sum_opp hm hBK htri sx sy
    have hgK : ‖g‖ * K * 1.4 ≤ m := by
      have h2 := sqrt_two_bounds.1
      have h3 : ‖g‖ * K * Real.sqrt 2 ≤ m := by nlinarith
      nlinarith [norm_nonneg g]
    calc _ ≤ ‖g‖ * (K * (4 * K ^ 2) + K * (2 * m * K)) := by gcongr
      _ ≤ 13 * m * K ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_right hgK (sq_nonneg K),
            mul_nonneg (mul_nonneg (norm_nonneg g) hK.le) (mul_nonneg hK.le hK.le),
            mul_le_mul_of_nonneg_left hmB (mul_nonneg (norm_nonneg g) hK.le)]

/-- **The cyclic kernel bound, `j = 2`** (LOCAL210 §1 `|S₂| ≤ 4mK⁴/D_K` with `13`): the same
hypotheses as `cyclic_sum_one`, `|g Σ c_i f₂(l_i²)| ≤ 13 m K⁴/√(K⁴ + z²)`. -/
theorem cyclic_sum_two {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (z : ℝ) {m B K : ℝ} (hm : 0 < m)
    (hmB : m ≤ B) (hBK : B ≤ K) (htri : K ≤ B + m) (sx sy sz : Sgn) (g : ℂ) (hg1 : ‖g‖ ≤ 1)
    (hgW : ‖g‖ * (2 * Real.sqrt 2 * K) ≤ |sg sx * m + sg sy * B + sg sz * K|) :
    ‖g * ((((sg sy * B - sg sz * K) / 2 : ℝ) : ℂ) * fres 2 ε z (m ^ 2) +
        (((sg sz * K - sg sx * m) / 2 : ℝ) : ℂ) * fres 2 ε z (B ^ 2) +
        (((sg sx * m - sg sy * B) / 2 : ℝ) : ℂ) * fres 2 ε z (K ^ 2))‖ ≤
      13 * m * K ^ 4 / Real.sqrt (K ^ 4 + z ^ 2) := by
  have hB : 0 < B := hm.trans_le hmB
  have hK : 0 < K := hB.trans_le hBK
  have hD : 0 < Real.sqrt (K ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have h1 := cyclic_split ((sg sy * B - sg sz * K) / 2) ((sg sz * K - sg sx * m) / 2)
    ((sg sx * m - sg sy * B) / 2) (by ring) g (fres 2 ε z (m ^ 2)) (fres 2 ε z (B ^ 2))
    (fres 2 ε z (K ^ 2))
  have hd1 := diff_small_two hε (z := z) hm hmB hBK htri
  have hd2 := diff_large_two hε (z := z) hm hmB hBK htri
  have hcz := abs_cz_le hm hmB hBK sx sy
  rw [le_div_iff₀ hD]
  refine (mul_le_mul_of_nonneg_right h1 hD.le).trans ?_
  have e : ‖g‖ * (|(sg sy * B - sg sz * K) / 2| * ‖fres 2 ε z (m ^ 2) - fres 2 ε z (B ^ 2)‖ +
      |(sg sx * m - sg sy * B) / 2| * ‖fres 2 ε z (K ^ 2) - fres 2 ε z (B ^ 2)‖) *
        Real.sqrt (K ^ 4 + z ^ 2) =
      ‖g‖ * (|(sg sy * B - sg sz * K) / 2| *
        (‖fres 2 ε z (m ^ 2) - fres 2 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2)) +
        |(sg sx * m - sg sy * B) / 2| *
        (‖fres 2 ε z (K ^ 2) - fres 2 ε z (B ^ 2)‖ * Real.sqrt (K ^ 4 + z ^ 2))) := by ring
  rw [e]
  have hK4 : 0 < K ^ 4 := by positivity
  by_cases hs : sy = sz
  · subst hs
    have hcx := abs_cx_same hBK htri sy
    calc _ ≤ 1 * (m / 2 * (12 * K ^ 4) + K * (6 * m * K ^ 3)) := by gcongr
      _ ≤ 13 * m * K ^ 4 := by nlinarith [mul_pos hm hK4]
  · have hsz := sg_of_ne hs
    rw [hsz] at hgW ⊢
    have hcx := abs_cx_opp hm hmB hBK sy
    have hXYZ := abs_sum_opp hm hBK htri sx sy
    have hgK : ‖g‖ * K * 1.4 ≤ m := by
      have h2 := sqrt_two_bounds.1
      have h3 : ‖g‖ * K * Real.sqrt 2 ≤ m := by nlinarith
      nlinarith [norm_nonneg g]
    calc _ ≤ ‖g‖ * (K * (12 * K ^ 4) + K * (6 * m * K ^ 3)) := by gcongr
      _ ≤ 13 * m * K ^ 4 := by
          nlinarith [mul_le_mul_of_nonneg_right hgK hK4.le,
            mul_nonneg (mul_nonneg (norm_nonneg g) hK.le) hK4.le,
            mul_le_mul_of_nonneg_left hmB (mul_nonneg (mul_nonneg (norm_nonneg g) hK.le)
              (pow_nonneg hK.le 3))]

/-! ### C. The Waleffe triple-product identity -/

/-- The bilinear scalar triple product `[A, B, C] = (A × B)·C` of `ℂ³` (LOCAL210 §1
`g = (h_α(p) × h_β(v))·conj h_γ(k)`, with `conj h(k) = h(−k)` in the all-incoming convention). -/
def trip (A B C : V3) : ℂ := bd (cross A B) C

theorem trip_smul (a b c : ℂ) (A B C : V3) :
    trip (a • A) (b • B) (c • C) = a * b * c * trip A B C := by
  simp only [trip, bd, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.smul_apply,
    smul_eq_mul]
  ring

/-- Cyclic invariance of the triple product. -/
theorem trip_cyc (A B C : V3) : trip B C A = trip A B C := by
  simp only [trip, bd, cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

/-- `‖bd a b‖ ≤ ‖a‖ ‖b‖` is `norm_bd_le`; this is Lagrange's identity in inequality form,
`‖A × B‖ ≤ ‖A‖ ‖B‖`, for the bilinear cross product of `ℂ³`. -/
theorem norm_cross_le (A B : V3) : ‖cross A B‖ ≤ ‖A‖ * ‖B‖ := by
  have key : ‖cross A B‖ ^ 2 ≤ (‖A‖ * ‖B‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, cross_apply_zero, cross_apply_one, cross_apply_two,
      Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im]
    nlinarith [sq_nonneg ((A 0).re * (B 0).re + (A 0).im * (B 0).im + (A 1).re * (B 1).re +
        (A 1).im * (B 1).im + (A 2).re * (B 2).re + (A 2).im * (B 2).im),
      sq_nonneg ((A 0).re * (B 0).im - (A 0).im * (B 0).re + (A 1).re * (B 1).im -
        (A 1).im * (B 1).re + (A 2).re * (B 2).im - (A 2).im * (B 2).re)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp key

/-- `|[A, B, C]| ≤ ‖A‖ ‖B‖ ‖C‖`: the trivial bound `|g| ≤ 1` on unit helical vectors. -/
theorem norm_trip_le (A B C : V3) : ‖trip A B C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ :=
  (norm_bd_le _ _).trans (mul_le_mul_of_nonneg_right (norm_cross_le A B) (norm_nonneg _))

private lemma crossZ_zero (p q : Mode) : crossZ p q 0 = p 1 * q 2 - p 2 * q 1 := by
  simp [crossZ]

private lemma crossZ_one (p q : Mode) : crossZ p q 1 = p 2 * q 0 - p 0 * q 2 := by
  simp [crossZ]

private lemma crossZ_two (p q : Mode) : crossZ p q 2 = p 0 * q 1 - p 1 * q 0 := by
  simp [crossZ]

/-- Lagrange for the lattice: `|p × q|² = |p|²|q|² − (p·q)²`. -/
theorem absSq_crossZ (p q : Mode) :
    absSq (crossZ p q) = absSq p * absSq q - (∑ i, (p i : ℝ) * q i) ^ 2 := by
  simp only [absSq, Fin.sum_univ_three, crossZ_zero, crossZ_one, crossZ_two, Int.cast_sub,
    Int.cast_mul]
  ring

/-- `|p × q| ≤ |p| |q|`. -/
theorem areaM_le (p q : Mode) : areaM p q ≤ absk p * absk q := by
  unfold areaM absk
  rw [← Real.sqrt_mul (absSq_nonneg p)]
  exact Real.sqrt_le_sqrt (by rw [absSq_crossZ]; nlinarith [sq_nonneg (∑ i, (p i : ℝ) * q i)])

/-! #### The helical frame (replicated from `Resonant/Orbit.lean`, where it is private) -/

/-- Unnormalised helical frame vector `|k|² n + i x (k × n)`. -/
private def wv (k n : Mode) (x : ℝ) : V3 :=
  (absSq k : ℂ) • modeVec n + (Complex.I * x) • cross (modeVec k) (modeVec n)

private lemma wv_apply (k n : Mode) (x : ℝ) (i : Fin 3) :
    wv k n x i =
      (absSq k : ℂ) * (n i : ℂ) + Complex.I * x * cross (modeVec k) (modeVec n) i := by
  simp [wv, modeVec_apply]

/-- A helical eigenvector orthogonal to `k` is a multiple of the frame vector. -/
private lemma eig_decomp {k n : Mode} {x : ℝ} {A : V3}
    (hkn : (k 0 : ℂ) * n 0 + (k 1 : ℂ) * n 1 + (k 2 : ℂ) * n 2 = 0)
    (hA : dotM A k = 0) (he : Complex.I • cross (modeVec k) A = (x : ℂ) • A) :
    ((absSq k : ℂ) * absSq n) • A = dotM A n • wv k n x := by
  have e0 := congrArg (fun v : V3 => v 0) he
  have e1 := congrArg (fun v : V3 => v 1) he
  have e2 := congrArg (fun v : V3 => v 2) he
  simp only [PiLp.smul_apply, smul_eq_mul, cross_apply_zero, cross_apply_one, cross_apply_two,
    modeVec_apply] at e0 e1 e2
  rw [dotM_eq] at hA
  have hc : Complex.I * ((n 0 : ℂ) * (Complex.I * ((k 1 : ℂ) * A 2 - (k 2 : ℂ) * A 1)) +
      (n 1 : ℂ) * (Complex.I * ((k 2 : ℂ) * A 0 - (k 0 : ℂ) * A 2)) +
      (n 2 : ℂ) * (Complex.I * ((k 0 : ℂ) * A 1 - (k 1 : ℂ) * A 0))) =
      Complex.I * ((n 0 : ℂ) * (x * A 0) + (n 1 : ℂ) * (x * A 1) + (n 2 : ℂ) * (x * A 2)) := by
    rw [e0, e1, e2]
  rw [dotM_eq]
  apply v3_ext <;>
  simp only [PiLp.smul_apply, smul_eq_mul, wv_apply, absSq_cast, cross_apply_zero,
    cross_apply_one, cross_apply_two, modeVec_apply]
  · linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
      (((k 0 : ℂ) * (n 0 : ℂ) + (k 1 : ℂ) * (n 1 : ℂ) + (k 2 : ℂ) * (n 2 : ℂ)) * A 0 -
      (A 0 * (n 0 : ℂ) + A 1 * (n 1 : ℂ) + A 2 * (n 2 : ℂ)) * (k 0 : ℂ)) * hkn -
      (((k 2 : ℂ) * (n 0 : ℂ) - (k 0 : ℂ) * (n 2 : ℂ)) * (n 2 : ℂ) -
      ((k 0 : ℂ) * (n 1 : ℂ) - (k 1 : ℂ) * (n 0 : ℂ)) * (n 1 : ℂ)) * hA +
      ((k 1 : ℂ) * (n 2 : ℂ) - (k 2 : ℂ) * (n 1 : ℂ)) * hc
  · linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
      (((k 0 : ℂ) * (n 0 : ℂ) + (k 1 : ℂ) * (n 1 : ℂ) + (k 2 : ℂ) * (n 2 : ℂ)) * A 1 -
      (A 0 * (n 0 : ℂ) + A 1 * (n 1 : ℂ) + A 2 * (n 2 : ℂ)) * (k 1 : ℂ)) * hkn -
      (((k 0 : ℂ) * (n 1 : ℂ) - (k 1 : ℂ) * (n 0 : ℂ)) * (n 0 : ℂ) -
      ((k 1 : ℂ) * (n 2 : ℂ) - (k 2 : ℂ) * (n 1 : ℂ)) * (n 2 : ℂ)) * hA +
      ((k 2 : ℂ) * (n 0 : ℂ) - (k 0 : ℂ) * (n 2 : ℂ)) * hc
  · linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
      (((k 0 : ℂ) * (n 0 : ℂ) + (k 1 : ℂ) * (n 1 : ℂ) + (k 2 : ℂ) * (n 2 : ℂ)) * A 2 -
      (A 0 * (n 0 : ℂ) + A 1 * (n 1 : ℂ) + A 2 * (n 2 : ℂ)) * (k 2 : ℂ)) * hkn -
      (((k 1 : ℂ) * (n 2 : ℂ) - (k 2 : ℂ) * (n 1 : ℂ)) * (n 1 : ℂ) -
      ((k 2 : ℂ) * (n 0 : ℂ) - (k 0 : ℂ) * (n 2 : ℂ)) * (n 0 : ℂ)) * hA +
      ((k 0 : ℂ) * (n 1 : ℂ) - (k 1 : ℂ) * (n 0 : ℂ)) * hc

private lemma norm_wv_sq {k n : Mode} (x : ℝ)
    (hkn : (k 0 : ℝ) * n 0 + (k 1 : ℝ) * n 1 + (k 2 : ℝ) * n 2 = 0) :
    ‖wv k n x‖ ^ 2 = absSq k ^ 2 * absSq n + x ^ 2 * (absSq k * absSq n) := by
  have hi : ∀ i, wv k n x i = ((absSq k * n i : ℝ) : ℂ) +
      ((x * ((crossZ k n i : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I := by
    intro i
    rw [wv_apply]
    fin_cases i <;>
    simp [cross_apply_zero, cross_apply_one, cross_apply_two, modeVec_apply, crossZ] <;> ring
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, hi, hi, hi]
  simp only [Complex.sq_norm, Complex.normSq_add_mul_I]
  simp only [absSq, Fin.sum_univ_three, crossZ]
  simp
  linear_combination (-(x ^ 2) * ((k 0 : ℝ) * n 0 + (k 1 : ℝ) * n 1 + (k 2 : ℝ) * n 2)) * hkn

private lemma kn_p (p q : Mode) :
    p 0 * crossZ p q 0 + p 1 * crossZ p q 1 + p 2 * crossZ p q 2 = 0 := by
  simp only [crossZ_zero, crossZ_one, crossZ_two]; ring

private lemma kn_q (p q : Mode) :
    q 0 * crossZ p q 0 + q 1 * crossZ p q 1 + q 2 * crossZ p q 2 = 0 := by
  simp only [crossZ_zero, crossZ_one, crossZ_two]; ring

private lemma kn_r (p q : Mode) :
    (-(p + q)) 0 * crossZ p q 0 + (-(p + q)) 1 * crossZ p q 1 +
      (-(p + q)) 2 * crossZ p q 2 = 0 := by
  simp only [crossZ_zero, crossZ_one, crossZ_two, Pi.neg_apply, Pi.add_apply]; ring

/-- The coordinates of the frame vector, with the integer cross product. -/
private lemma wv_coord (k n : Mode) (x : ℝ) (i : Fin 3) :
    wv k n x i = ((absSq k * (n i : ℤ) : ℝ) : ℂ) +
      ((x * ((crossZ k n i : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I := by
  rw [wv_apply]
  fin_cases i <;>
  simp [cross_apply_zero, cross_apply_one, cross_apply_two, modeVec_apply, crossZ] <;> ring

/-- The triple product in coordinates. -/
private lemma trip_coord (A B C : V3) :
    trip A B C = (A 1 * B 2 - A 2 * B 1) * C 0 + (A 2 * B 0 - A 0 * B 2) * C 1 +
      (A 0 * B 1 - A 1 * B 0) * C 2 := by
  unfold trip bd
  rw [cross_apply_zero, cross_apply_one, cross_apply_two]

set_option maxRecDepth 8192 in
/-- The triple product of the three frame vectors of the triad `(p, q, −(p + q))`, normal
`n = p × q`: `−|n|⁴ (|p|² y w + x |q|² w + x y |r|²)` (which is `−|n|⁴ xyw(x + y + w)` once
`x² = |p|²`, `y² = |q|²`, `w² = |r|²`).  A polynomial identity in the lattice coordinates; it is
the algebraic core of the Waleffe identity. -/
private lemma trip_wv (p q : Mode) (x y w : ℝ) :
    trip (wv p (crossZ p q) x) (wv q (crossZ p q) y) (wv (-(p + q)) (crossZ p q) w) =
      -((absSq (crossZ p q) ^ 2 * (absSq p * y * w + x * absSq q * w +
        x * y * absSq (-(p + q))) : ℝ) : ℂ) := by
  rw [trip_coord]
  simp only [wv_coord]
  simp only [absSq, Fin.sum_univ_three, crossZ_zero, crossZ_one, crossZ_two, Pi.neg_apply,
    Pi.add_apply]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

private lemma kn_leg (ℓ : Fin 3 → Mode) (hr : ℓ 2 = -(ℓ 0 + ℓ 1)) (j : Fin 3) :
    ℓ j 0 * crossZ (ℓ 0) (ℓ 1) 0 + ℓ j 1 * crossZ (ℓ 0) (ℓ 1) 1 +
      ℓ j 2 * crossZ (ℓ 0) (ℓ 1) 2 = 0 := by
  fin_cases j
  · exact kn_p _ _
  · exact kn_q _ _
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [hr]; exact kn_r _ _

private lemma hel_decomp (ℓ : Fin 3 → Mode) (hr : ℓ 2 = -(ℓ 0 + ℓ 1)) (hne : ∀ j, ℓ j ≠ 0)
    (s : Fin 3 → Sgn) (v : Fin 3 → V3) (hG : absSq (crossZ (ℓ 0) (ℓ 1)) ≠ 0) (j : Fin 3) :
    hel (s j) (ℓ j) (v j) = (dotM (hel (s j) (ℓ j) (v j)) (crossZ (ℓ 0) (ℓ 1)) /
      ((absSq (ℓ j) : ℂ) * absSq (crossZ (ℓ 0) (ℓ 1)))) •
        wv (ℓ j) (crossZ (ℓ 0) (ℓ 1)) (sl ℓ s j) := by
  have h := eig_decomp (x := sl ℓ s j) (by exact_mod_cast kn_leg ℓ hr j)
    (dotM_hel (s j) (ℓ j) (v j)) (cross_hel (s j) (ℓ j) (v j))
  have hc : ((absSq (ℓ j) : ℂ) * absSq (crossZ (ℓ 0) (ℓ 1))) ≠ 0 :=
    mul_ne_zero (absSq_cast_ne (hne j)) (by exact_mod_cast hG)
  rw [div_eq_inv_mul, ← smul_smul, ← h, smul_smul, inv_mul_cancel₀ hc, one_smul]

private lemma sg_sq' (a : Sgn) : sg a ^ 2 = 1 := by cases a <;> simp [sg]

private lemma abs_sg (a : Sgn) : |sg a| = 1 := by cases a <;> simp [sg]

private lemma sl_sq (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) (j : Fin 3) :
    sl ℓ s j ^ 2 = absSq (ℓ j) := by
  rw [sl, mul_pow, sg_sq', one_mul, absk_sq]

private lemma abs_sl (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) (j : Fin 3) :
    |sl ℓ s j| = absk (ℓ j) := by
  rw [sl, abs_mul, abs_sg, one_mul, abs_of_nonneg (absk_nonneg _)]

private lemma norm_wv_leg (ℓ : Fin 3 → Mode) (hr : ℓ 2 = -(ℓ 0 + ℓ 1)) (s : Fin 3 → Sgn)
    (j : Fin 3) :
    ‖wv (ℓ j) (crossZ (ℓ 0) (ℓ 1)) (sl ℓ s j)‖ =
      Real.sqrt 2 * absSq (ℓ j) * Real.sqrt (absSq (crossZ (ℓ 0) (ℓ 1))) := by
  have h := norm_wv_sq (sl ℓ s j) (by exact_mod_cast kn_leg ℓ hr j)
  rw [sl_sq] at h
  have hG := absSq_nonneg (crossZ (ℓ 0) (ℓ 1))
  have hP := absSq_nonneg (ℓ j)
  rw [← pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero, h, mul_pow, mul_pow,
    Real.sq_sqrt (by norm_num), Real.sq_sqrt hG]
  ring

private lemma crossZ_leg_zero (ℓ : Fin 3 → Mode) (hr : ℓ 2 = -(ℓ 0 + ℓ 1))
    (h : crossZ (ℓ 0) (ℓ 1) = 0) (a b : Fin 3) : crossZ (ℓ a) (ℓ b) = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [crossZ_zero, crossZ_one, crossZ_two, Pi.zero_apply] at h0 h1 h2
  funext i
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp only [Fin.reduceFinMk, Fin.isValue, hr, crossZ_zero, crossZ_one, crossZ_two,
      Pi.zero_apply, Pi.neg_apply, Pi.add_apply] <;>
    first
    | ring1
    | linear_combination h0
    | linear_combination -h0
    | linear_combination h1
    | linear_combination -h1
    | linear_combination h2
    | linear_combination -h2

private lemma dot_collinear {k l : Mode} {A : V3} (hk : k ≠ 0) (hc : crossZ k l = 0)
    (hA : dotM A k = 0) : dotM A l = 0 := by
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp only [crossZ_zero, crossZ_one, crossZ_two, Pi.zero_apply] at h0 h1 h2
  have c0 : (k 1 : ℂ) * l 2 - (k 2 : ℂ) * l 1 = 0 := by exact_mod_cast h0
  have c1 : (k 2 : ℂ) * l 0 - (k 0 : ℂ) * l 2 = 0 := by exact_mod_cast h1
  have c2 : (k 0 : ℂ) * l 1 - (k 1 : ℂ) * l 0 = 0 := by exact_mod_cast h2
  rw [dotM_eq] at hA ⊢
  have key : (absSq k : ℂ) * (A 0 * l 0 + A 1 * l 1 + A 2 * l 2) = 0 := by
    rw [absSq_cast]
    linear_combination ((k 0 : ℂ) * l 0 + (k 1 : ℂ) * l 1 + (k 2 : ℂ) * l 2) * hA -
      (A 0 * ((k 1 : ℂ) * c2 - (k 2 : ℂ) * c1) + A 1 * ((k 2 : ℂ) * c0 - (k 0 : ℂ) * c2) +
        A 2 * ((k 0 : ℂ) * c1 - (k 1 : ℂ) * c0))
  exact (mul_eq_zero.mp key).resolve_left (absSq_cast_ne hk)

/-- The expansion `[A, B, C] u = (A·u)(B × C) + (B·u)(C × A) + (C·u)(A × B)`, componentwise. -/
private lemma trip_mul_coord (A B C : V3) (u : Mode) (i : Fin 3) :
    trip A B C * (u i : ℂ) =
      dotM A u * cross B C i + dotM B u * cross C A i + dotM C u * cross A B i := by
  fin_cases i <;>
    simp only [trip, bd, dotM_eq, cross_apply_zero, cross_apply_one, cross_apply_two,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    ring

/-- Three vectors orthogonal to a nonzero lattice vector have zero triple product. -/
private lemma trip_eq_zero_of_perp {u : Mode} (hu : u ≠ 0) {A B C : V3} (hA : dotM A u = 0)
    (hB : dotM B u = 0) (hC : dotM C u = 0) : trip A B C = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    exact hu (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  have h := trip_mul_coord A B C u i
  rw [hA, hB, hC, zero_mul, zero_mul, zero_mul, add_zero, add_zero] at h
  have hi' : (u i : ℂ) ≠ 0 := by exact_mod_cast hi
  exact (mul_eq_zero.mp h).resolve_right hi'

/-- **The Waleffe triple-product identity** for the library's helical projectors (report §2
Step 2 (ii), checked there numerically on 20 000 triads; here proved): for a zero-sum triad of
nonzero modes with helical amplitudes `A_j = hel (s j) (ℓ j) (v j)` and signed lengths
`x_j = s_j |ℓ_j|` (`sl`),
`|[A₀, A₁, A₂]| · 2√2 |ℓ₀||ℓ₁||ℓ₂| = |x₀ + x₁ + x₂| · |ℓ₀ × ℓ₁| · ‖A₀‖‖A₁‖‖A₂‖`. -/
theorem waleffe (ℓ : Fin 3 → Mode) (hsum : ∑ j, ℓ j = 0) (hne : ∀ j, ℓ j ≠ 0)
    (s : Fin 3 → Sgn) (v : Fin 3 → V3) :
    ‖trip (hel (s 0) (ℓ 0) (v 0)) (hel (s 1) (ℓ 1) (v 1)) (hel (s 2) (ℓ 2) (v 2))‖ *
        (2 * Real.sqrt 2 * (absk (ℓ 0) * absk (ℓ 1) * absk (ℓ 2))) =
      |sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2| * areaM (ℓ 0) (ℓ 1) *
        ∏ j, ‖hel (s j) (ℓ j) (v j)‖ := by
  have hr : ℓ 2 = -(ℓ 0 + ℓ 1) := by
    rw [Fin.sum_univ_three] at hsum
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hsum
  set n := crossZ (ℓ 0) (ℓ 1) with hn
  by_cases hG : absSq n = 0
  · have hn0 : n = 0 := absk_eq_zero.mp (by rw [absk, hG, Real.sqrt_zero])
    have hd : ∀ a, dotM (hel (s a) (ℓ a) (v a)) (ℓ 0) = 0 := fun a =>
      dot_collinear (hne a) (crossZ_leg_zero ℓ hr hn0 a 0) (dotM_hel _ _ _)
    have h0 : trip (hel (s 0) (ℓ 0) (v 0)) (hel (s 1) (ℓ 1) (v 1)) (hel (s 2) (ℓ 2) (v 2)) = 0 :=
      trip_eq_zero_of_perp (hne 0) (hd 0) (hd 1) (hd 2)
    have hA : areaM (ℓ 0) (ℓ 1) = 0 := by
      rw [areaM, ← hn, absk, hG, Real.sqrt_zero]
    rw [h0, hA]
    simp
  · set α : Fin 3 → ℂ := fun j => dotM (hel (s j) (ℓ j) (v j)) n /
      ((absSq (ℓ j) : ℂ) * absSq n) with hα
    have hdec : ∀ j, hel (s j) (ℓ j) (v j) = α j • wv (ℓ j) n (sl ℓ s j) :=
      fun j => hel_decomp ℓ hr hne s v hG j
    have hnorm : ∀ j, ‖hel (s j) (ℓ j) (v j)‖ =
        ‖α j‖ * (Real.sqrt 2 * absSq (ℓ j) * Real.sqrt (absSq n)) := by
      intro j
      rw [hdec j, norm_smul, norm_wv_leg ℓ hr s j]
    have htrip : trip (hel (s 0) (ℓ 0) (v 0)) (hel (s 1) (ℓ 1) (v 1)) (hel (s 2) (ℓ 2) (v 2)) =
        α 0 * α 1 * α 2 * -((absSq n ^ 2 * (sl ℓ s 0 * sl ℓ s 1 * sl ℓ s 2 *
          (sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2)) : ℝ) : ℂ) := by
      rw [hdec 0, hdec 1, hdec 2, trip_smul]
      congr 1
      have e2 : wv (ℓ 2) n (sl ℓ s 2) = wv (-(ℓ 0 + ℓ 1)) n (sl ℓ s 2) := by rw [hr]
      rw [e2, hn, trip_wv, ← hr]
      congr 2
      rw [← sl_sq ℓ s 0, ← sl_sq ℓ s 1, ← sl_sq ℓ s 2]
      ring
    rw [htrip, Fin.prod_univ_three, hnorm, hnorm, hnorm, areaM, ← hn]
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_sl]
    have hg : absk n = Real.sqrt (absSq n) := rfl
    have hG2 : absSq n ^ 2 = Real.sqrt (absSq n) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (absSq_nonneg n)]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ absSq n ^ 2), hg, ← absk_sq (ℓ 0),
      ← absk_sq (ℓ 1), ← absk_sq (ℓ 2), hG2]
    set g := Real.sqrt (absSq n)
    set T := |sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2|
    linear_combination (-(‖α 0‖ * ‖α 1‖ * ‖α 2‖ * g ^ 4 *
      (absk (ℓ 0) * absk (ℓ 1) * absk (ℓ 2)) ^ 2 * T * Real.sqrt 2)) * h2

/-- The Waleffe bound used in the kernel estimate (report §2 Step 2 (ii)): with
`|ℓ₀ × ℓ₁| ≤ |ℓ₀||ℓ₁|`, `|[A₀, A₁, A₂]| · 2√2 |ℓ₂| ≤ |x₀ + x₁ + x₂| ∏ ‖A_j‖`. -/
theorem waleffe_le (ℓ : Fin 3 → Mode) (hsum : ∑ j, ℓ j = 0) (hne : ∀ j, ℓ j ≠ 0)
    (s : Fin 3 → Sgn) (v : Fin 3 → V3) :
    ‖trip (hel (s 0) (ℓ 0) (v 0)) (hel (s 1) (ℓ 1) (v 1)) (hel (s 2) (ℓ 2) (v 2))‖ *
        (2 * Real.sqrt 2 * absk (ℓ 2)) ≤
      |sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2| * ∏ j, ‖hel (s j) (ℓ j) (v j)‖ := by
  have h := waleffe ℓ hsum hne s v
  have h0 : 0 < absk (ℓ 0) := lt_of_lt_of_le one_pos (one_le_absk (hne 0))
  have h1 : 0 < absk (ℓ 1) := lt_of_lt_of_le one_pos (one_le_absk (hne 1))
  have hA := areaM_le (ℓ 0) (ℓ 1)
  have hT : 0 ≤ |sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2| * ∏ j, ‖hel (s j) (ℓ j) (v j)‖ := by
    positivity
  have key : ‖trip (hel (s 0) (ℓ 0) (v 0)) (hel (s 1) (ℓ 1) (v 1)) (hel (s 2) (ℓ 2) (v 2))‖ *
      (2 * Real.sqrt 2 * absk (ℓ 2)) * (absk (ℓ 0) * absk (ℓ 1)) ≤
      |sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2| * (∏ j, ‖hel (s j) (ℓ j) (v j)‖) *
        (absk (ℓ 0) * absk (ℓ 1)) := by
    calc _ = |sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2| * areaM (ℓ 0) (ℓ 1) *
          ∏ j, ‖hel (s j) (ℓ j) (v j)‖ := by rw [← h]; ring
      _ ≤ _ := by
          rw [mul_right_comm]
          exact mul_le_mul_of_nonneg_left hA hT
  exact le_of_mul_le_mul_right key (by positivity)

/-! ### D. The vertex as a triple product -/

private lemma bd_smul_right (C : V3) (c : ℂ) (V : V3) : bd C (c • V) = c * bd C V := by
  simp only [bd, PiLp.smul_apply, smul_eq_mul]
  ring

/-- LOCAL210 §1 `C_{pv}^k = (α|p| − β|v|) g/2`: on helical amplitudes the vertex form `tau`
against a transverse test vector is the signed-length difference times the triple product
(from `vert_hel`). -/
theorem tau_hel_eq_trip (a b : Sgn) {p q : Mode} (hk : p + q ≠ 0) (v w : V3) {C : V3}
    (hC : dotM C (p + q) = 0) :
    tau p q (hel a p v) (hel b q w) C =
      (((sg a * absk p - sg b * absk q) / 2 : ℝ) : ℂ) * trip (hel a p v) (hel b q w) C := by
  rw [← bd_vert hC (fun h => absurd h hk), vert_hel, bd_smul_right, bd_leray hk hC, trip,
    bd_comm]

/-! ### E. The triad-level kernel bound and the native domination -/

/-- `√(K⁴ + (rΦ)²) = √(K⁴ + |r|²Φ²)`: the `z = rΦ` of the cyclic bound is the `q = |r|`
Lorentzian of `Z1`. -/
theorem sqrt_lorentz_eq (K r Φ : ℝ) :
    Real.sqrt (K ^ 4 + (r * Φ) ^ 2) = Real.sqrt (K ^ 4 + |r| ^ 2 * Φ ^ 2) := by
  rw [mul_pow, sq_abs]

/-- The three rootings of a zero-sum triad of nonzero modes with helical amplitudes, weighted by
`f_j(|out|²)` (output `−ℓ_c` for the rooting with inputs `ℓ_a, ℓ_b`), collect into the common
triple product times the cyclic scalar sum (report §2 Step 1). -/
theorem triad_rootings_eq (j : ℕ) (ε z : ℝ) (ℓ : Fin 3 → Mode) (hsum : ∑ i, ℓ i = 0)
    (hne : ∀ i, ℓ i ≠ 0) (s : Fin 3 → Sgn) (v : Fin 3 → V3) :
    let A := fun i => hel (s i) (ℓ i) (v i)
    tau (ℓ 0) (ℓ 1) (A 0) (A 1) (A 2) * fres j ε z (absSq (ℓ 2)) +
      tau (ℓ 1) (ℓ 2) (A 1) (A 2) (A 0) * fres j ε z (absSq (ℓ 0)) +
      tau (ℓ 2) (ℓ 0) (A 2) (A 0) (A 1) * fres j ε z (absSq (ℓ 1)) =
    trip (A 0) (A 1) (A 2) *
      ((((sl ℓ s 1 - sl ℓ s 2) / 2 : ℝ) : ℂ) * fres j ε z (absSq (ℓ 0)) +
        (((sl ℓ s 2 - sl ℓ s 0) / 2 : ℝ) : ℂ) * fres j ε z (absSq (ℓ 1)) +
        (((sl ℓ s 0 - sl ℓ s 1) / 2 : ℝ) : ℂ) * fres j ε z (absSq (ℓ 2))) := by
  intro A
  simp only [A]
  rw [Fin.sum_univ_three] at hsum
  have h01 : ℓ 0 + ℓ 1 ≠ 0 := by
    intro h
    exact hne 2 (by linear_combination hsum - h)
  have h12 : ℓ 1 + ℓ 2 ≠ 0 := by
    intro h
    exact hne 0 (by linear_combination hsum - h)
  have h20 : ℓ 2 + ℓ 0 ≠ 0 := by
    intro h
    exact hne 1 (by linear_combination hsum - h)
  have hC2 : dotM (hel (s 2) (ℓ 2) (v 2)) (ℓ 0 + ℓ 1) = 0 := by
    have e : ℓ 0 + ℓ 1 = -ℓ 2 := by linear_combination hsum
    rw [e, dotM_neg_mode, dotM_hel, neg_zero]
  have hC0 : dotM (hel (s 0) (ℓ 0) (v 0)) (ℓ 1 + ℓ 2) = 0 := by
    have e : ℓ 1 + ℓ 2 = -ℓ 0 := by linear_combination hsum
    rw [e, dotM_neg_mode, dotM_hel, neg_zero]
  have hC1 : dotM (hel (s 1) (ℓ 1) (v 1)) (ℓ 2 + ℓ 0) = 0 := by
    have e : ℓ 2 + ℓ 0 = -ℓ 1 := by linear_combination hsum
    rw [e, dotM_neg_mode, dotM_hel, neg_zero]
  rw [tau_hel_eq_trip _ _ h01 _ _ hC2, tau_hel_eq_trip _ _ h12 _ _ hC0,
    tau_hel_eq_trip _ _ h20 _ _ hC1,
    trip_cyc (hel (s 1) (ℓ 1) (v 1)) (hel (s 2) (ℓ 2) (v 2)) (hel (s 0) (ℓ 0) (v 0)),
    trip_cyc (hel (s 0) (ℓ 0) (v 0)) (hel (s 1) (ℓ 1) (v 1)) (hel (s 2) (ℓ 2) (v 2))]
  simp only [sl]
  push_cast
  ring

/-- **The triad-level kernel bound** (LOCAL210 §1, report §2 Steps 1–2 with the constant `13`):
for a sorted fast triad `|ℓ₀| = m ≤ |ℓ₁| = B ≤ |ℓ₂| = K` of nonzero zero-sum modes, the cyclic
sum of the three rootings weighted by `f_j(|out|²)`, `j ∈ {1, 2}`, is at most
`13 m K^{2j}/√(K⁴ + z²) · ∏ ‖A_i‖`. -/
theorem triad_cyclic_le {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (z : ℝ)
    (ℓ : Fin 3 → Mode) (hsum : ∑ i, ℓ i = 0) (hne : ∀ i, ℓ i ≠ 0)
    (h01 : absk (ℓ 0) ≤ absk (ℓ 1)) (h12 : absk (ℓ 1) ≤ absk (ℓ 2))
    (s : Fin 3 → Sgn) (v : Fin 3 → V3) :
    let A := fun i => hel (s i) (ℓ i) (v i)
    ‖tau (ℓ 0) (ℓ 1) (A 0) (A 1) (A 2) * fres j ε z (absSq (ℓ 2)) +
        tau (ℓ 1) (ℓ 2) (A 1) (A 2) (A 0) * fres j ε z (absSq (ℓ 0)) +
        tau (ℓ 2) (ℓ 0) (A 2) (A 0) (A 1) * fres j ε z (absSq (ℓ 1))‖ ≤
      13 * absk (ℓ 0) * absk (ℓ 2) ^ (2 * j) / Real.sqrt (absk (ℓ 2) ^ 4 + z ^ 2) *
        ∏ i, ‖A i‖ := by
  intro A
  rw [triad_rootings_eq j ε z ℓ hsum hne s v]
  have hm : 0 < absk (ℓ 0) := lt_of_lt_of_le one_pos (one_le_absk (hne 0))
  have htri : absk (ℓ 2) ≤ absk (ℓ 1) + absk (ℓ 0) := by
    rw [Fin.sum_univ_three] at hsum
    have e : ℓ 2 = -(ℓ 0 + ℓ 1) := by linear_combination hsum
    rw [e, absk_neg, add_comm (absk (ℓ 1))]
    exact absk_add_le _ _
  have hP : 0 ≤ ∏ i, ‖A i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hD : 0 ≤ 13 * absk (ℓ 0) * absk (ℓ 2) ^ (2 * j) / Real.sqrt (absk (ℓ 2) ^ 4 + z ^ 2) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (absk_nonneg _))
      (pow_nonneg (absk_nonneg _) _)) (Real.sqrt_nonneg _)
  have hW := waleffe_le ℓ hsum hne s v
  have hT := norm_trip_le (A 0) (A 1) (A 2)
  have hP3 : ∏ i, ‖A i‖ = ‖A 0‖ * ‖A 1‖ * ‖A 2‖ := Fin.prod_univ_three _
  rcases hP.eq_or_lt with hP0 | hP0
  · -- a vanishing amplitude: the triple product vanishes
    have h0 : trip (A 0) (A 1) (A 2) = 0 := by
      rw [hP3] at hP0
      exact norm_le_zero_iff.mp (hT.trans_eq hP0.symm)
    rw [h0, zero_mul, norm_zero, ← hP0, mul_zero]
  · -- normalise the triple product
    set P := ∏ i, ‖A i‖
    set g : ℂ := trip (A 0) (A 1) (A 2) / (P : ℂ) with hg
    have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP0.ne'
    have hgP : trip (A 0) (A 1) (A 2) = (P : ℂ) * g := by
      rw [hg, mul_div_cancel₀ _ hPc]
    have hg1 : ‖g‖ ≤ 1 := by
      rw [hg, norm_div, Complex.norm_real, Real.norm_of_nonneg hP0.le, div_le_one hP0, hP3]
      exact hT
    have hgW : ‖g‖ * (2 * Real.sqrt 2 * absk (ℓ 2)) ≤
        |sg (s 0) * absk (ℓ 0) + sg (s 1) * absk (ℓ 1) + sg (s 2) * absk (ℓ 2)| := by
      rw [hg, norm_div, Complex.norm_real, Real.norm_of_nonneg hP0.le]
      have := hW
      simp only [sl] at this
      rw [div_mul_eq_mul_div, div_le_iff₀ hP0]
      linarith
    have key : ∀ (f : ℝ → ℂ),
        ‖(P : ℂ) * g * ((((sl ℓ s 1 - sl ℓ s 2) / 2 : ℝ) : ℂ) * f (absSq (ℓ 0)) +
          (((sl ℓ s 2 - sl ℓ s 0) / 2 : ℝ) : ℂ) * f (absSq (ℓ 1)) +
          (((sl ℓ s 0 - sl ℓ s 1) / 2 : ℝ) : ℂ) * f (absSq (ℓ 2)))‖ =
        P * ‖g * ((((sg (s 1) * absk (ℓ 1) - sg (s 2) * absk (ℓ 2)) / 2 : ℝ) : ℂ) *
          f (absk (ℓ 0) ^ 2) +
          (((sg (s 2) * absk (ℓ 2) - sg (s 0) * absk (ℓ 0)) / 2 : ℝ) : ℂ) * f (absk (ℓ 1) ^ 2) +
          (((sg (s 0) * absk (ℓ 0) - sg (s 1) * absk (ℓ 1)) / 2 : ℝ) : ℂ) *
          f (absk (ℓ 2) ^ 2))‖ := by
      intro f
      rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hP0.le]
      simp only [sl, absk_sq]
    rw [hgP, key (fres j ε z), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hP0.le
    rcases hj with rfl | rfl
    · simpa using cyclic_sum_one hε z hm h01 h12 htri (s 0) (s 1) (s 2) g hg1 hgW
    · simpa using cyclic_sum_two hε z hm h01 h12 htri (s 0) (s 1) (s 2) g hg1 hgW

/-- The six native normalisations, `E1` (LOCAL210 §1 "E1's h-small/middle/large coefficients
are bounded by `4/(B₀²D_K), 4/(mB₀D_K), 4K/(mB₀²D_K)`, all `≤ 32/(mKD_K)`"; here with `13`
and `104`): `13 m K² · mK ≤ 104 · (native weight)` at each position. -/
theorem wgtE1_dom {m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B) (hBK : B ≤ K) (htri : K ≤ B + m)
    (i : Fin 3) : 13 * m * K ^ 2 * (m * K) ≤ 104 * wgtE1 m B K i := by
  have hB : 0 < B := hm.trans_le hmB
  have hK : 0 < K := hB.trans_le hBK
  have hK2B : K ≤ 2 * B := by linarith
  have hKB2 : K ^ 2 ≤ 4 * B ^ 2 := by nlinarith
  have hmK : m * K ≤ K ^ 2 := by nlinarith
  fin_cases i <;> simp only [wgtE1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · nlinarith [mul_pos hm hK, mul_pos (mul_pos hm hK) hK]
  · nlinarith [mul_pos hm hm, mul_pos (mul_pos hm hm) hK, mul_pos (mul_pos (mul_pos hm hm) hK) hK]
  · nlinarith [mul_pos hm hm, mul_pos (mul_pos hm hm) hK]

/-- The six native normalisations, `E2` (LOCAL210 §1 "E2's are bounded by `4K/(mB₀²D_K),
4K/(mB₀²D_K), 4K²/(mB₀³D_K)`"): `13 m K⁴ · mK ≤ 104 · (native weight)` at each position. -/
theorem wgtE2_dom {m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B) (hBK : B ≤ K) (htri : K ≤ B + m)
    (i : Fin 3) : 13 * m * K ^ 4 * (m * K) ≤ 104 * wgtE2 m B K i := by
  have hB : 0 < B := hm.trans_le hmB
  have hK : 0 < K := hB.trans_le hBK
  have hK2B : K ≤ 2 * B := by linarith
  have hKB2 : K ^ 2 ≤ 4 * B ^ 2 := by nlinarith
  have hKB3 : K ^ 3 ≤ 8 * B ^ 3 := by
    have := pow_le_pow_left₀ hK.le hK2B 3
    nlinarith [this]
  have hm2K3 : 0 < m ^ 2 * K ^ 3 := by positivity
  have hm2K2 : 0 < m ^ 2 * K ^ 2 := by positivity
  fin_cases i <;> simp only [wgtE2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · nlinarith [mul_le_mul_of_nonneg_left hKB2 hm2K3.le]
  · nlinarith [mul_le_mul_of_nonneg_left hKB2 hm2K3.le]
  · nlinarith [mul_le_mul_of_nonneg_left hKB3 hm2K2.le]

/-- `13 m K^{2j}/D_K ≤ (13/4) · Z1 · (native weight)` at every position, `E1`. -/
theorem kernel_le_Z1_E1 {m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B) (hBK : B ≤ K) (htri : K ≤ B + m)
    (r Φ : ℝ) (i : Fin 3) :
    13 * m * K ^ 2 / Real.sqrt (K ^ 4 + (r * Φ) ^ 2) ≤
      13 / 4 * Z1 |r| m K Φ * wgtE1 m B K i := by
  have hB : 0 < B := hm.trans_le hmB
  have hK : 0 < K := hB.trans_le hBK
  have hD : 0 < Real.sqrt (K ^ 4 + |r| ^ 2 * Φ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hw := wgtE1_dom hm hmB hBK htri i
  rw [sqrt_lorentz_eq, Z1, div_le_iff₀ hD]
  have e : 13 / 4 * (32 / (m * K * Real.sqrt (K ^ 4 + |r| ^ 2 * Φ ^ 2))) * wgtE1 m B K i *
      Real.sqrt (K ^ 4 + |r| ^ 2 * Φ ^ 2) = 104 * wgtE1 m B K i / (m * K) := by
    field_simp
    ring
  rw [e, le_div_iff₀ (by positivity)]
  linarith

/-- `13 m K^{2j}/D_K ≤ (13/4) · Z1 · (native weight)` at every position, `E2`. -/
theorem kernel_le_Z1_E2 {m B K : ℝ} (hm : 0 < m) (hmB : m ≤ B) (hBK : B ≤ K) (htri : K ≤ B + m)
    (r Φ : ℝ) (i : Fin 3) :
    13 * m * K ^ 4 / Real.sqrt (K ^ 4 + (r * Φ) ^ 2) ≤
      13 / 4 * Z1 |r| m K Φ * wgtE2 m B K i := by
  have hB : 0 < B := hm.trans_le hmB
  have hK : 0 < K := hB.trans_le hBK
  have hD : 0 < Real.sqrt (K ^ 4 + |r| ^ 2 * Φ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hw := wgtE2_dom hm hmB hBK htri i
  rw [sqrt_lorentz_eq, Z1, div_le_iff₀ hD]
  have e : 13 / 4 * (32 / (m * K * Real.sqrt (K ^ 4 + |r| ^ 2 * Φ ^ 2))) * wgtE2 m B K i *
      Real.sqrt (K ^ 4 + |r| ^ 2 * Φ ^ 2) = 104 * wgtE2 m B K i / (m * K) := by
    field_simp
    ring
  rw [e, le_div_iff₀ (by positivity)]
  linarith

/-- **Native domination, `E1`** (LOCAL210 (1.2) with `32` replaced by `104 = 8·13`, report §2
Step 2): for a sorted fast triad with `z = rΦ`, the cyclic sum of the three rootings is at most
`(13/4) · Z1(|r|, m, K, Φ) · (native E1 weight at the position of h) · ∏ ‖A_i‖`, at each of the
three positions. -/
theorem native_dominated_E1 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r Φ : ℝ) (ℓ : Fin 3 → Mode)
    (hsum : ∑ i, ℓ i = 0) (hne : ∀ i, ℓ i ≠ 0) (h01 : absk (ℓ 0) ≤ absk (ℓ 1))
    (h12 : absk (ℓ 1) ≤ absk (ℓ 2)) (s : Fin 3 → Sgn) (v : Fin 3 → V3) (i : Fin 3) :
    let A := fun i => hel (s i) (ℓ i) (v i)
    ‖tau (ℓ 0) (ℓ 1) (A 0) (A 1) (A 2) * fres 1 ε (r * Φ) (absSq (ℓ 2)) +
        tau (ℓ 1) (ℓ 2) (A 1) (A 2) (A 0) * fres 1 ε (r * Φ) (absSq (ℓ 0)) +
        tau (ℓ 2) (ℓ 0) (A 2) (A 0) (A 1) * fres 1 ε (r * Φ) (absSq (ℓ 1))‖ ≤
      13 / 4 * Z1 |r| (absk (ℓ 0)) (absk (ℓ 2)) Φ * wgtE1 (absk (ℓ 0)) (absk (ℓ 1)) (absk (ℓ 2)) i *
        ∏ i, ‖A i‖ := by
  intro A
  have h := triad_cyclic_le (Or.inl rfl) hε (r * Φ) ℓ hsum hne h01 h12 s v
  have hm : 0 < absk (ℓ 0) := lt_of_lt_of_le one_pos (one_le_absk (hne 0))
  have htri : absk (ℓ 2) ≤ absk (ℓ 1) + absk (ℓ 0) := by
    rw [Fin.sum_univ_three] at hsum
    have e : ℓ 2 = -(ℓ 0 + ℓ 1) := by linear_combination hsum
    rw [e, absk_neg, add_comm (absk (ℓ 1))]
    exact absk_add_le _ _
  have hk := kernel_le_Z1_E1 hm h01 h12 htri r Φ i
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _))
  simpa using hk

/-- **Native domination, `E2`**: the same with the `E2` weights `(H²(h), H²(F), H³(F))`. -/
theorem native_dominated_E2 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r Φ : ℝ) (ℓ : Fin 3 → Mode)
    (hsum : ∑ i, ℓ i = 0) (hne : ∀ i, ℓ i ≠ 0) (h01 : absk (ℓ 0) ≤ absk (ℓ 1))
    (h12 : absk (ℓ 1) ≤ absk (ℓ 2)) (s : Fin 3 → Sgn) (v : Fin 3 → V3) (i : Fin 3) :
    let A := fun i => hel (s i) (ℓ i) (v i)
    ‖tau (ℓ 0) (ℓ 1) (A 0) (A 1) (A 2) * fres 2 ε (r * Φ) (absSq (ℓ 2)) +
        tau (ℓ 1) (ℓ 2) (A 1) (A 2) (A 0) * fres 2 ε (r * Φ) (absSq (ℓ 0)) +
        tau (ℓ 2) (ℓ 0) (A 2) (A 0) (A 1) * fres 2 ε (r * Φ) (absSq (ℓ 1))‖ ≤
      13 / 4 * Z1 |r| (absk (ℓ 0)) (absk (ℓ 2)) Φ * wgtE2 (absk (ℓ 0)) (absk (ℓ 1)) (absk (ℓ 2)) i *
        ∏ i, ‖A i‖ := by
  intro A
  have h := triad_cyclic_le (Or.inr rfl) hε (r * Φ) ℓ hsum hne h01 h12 s v
  have hm : 0 < absk (ℓ 0) := lt_of_lt_of_le one_pos (one_le_absk (hne 0))
  have htri : absk (ℓ 2) ≤ absk (ℓ 1) + absk (ℓ 0) := by
    rw [Fin.sum_univ_three] at hsum
    have e : ℓ 2 = -(ℓ 0 + ℓ 1) := by linear_combination hsum
    rw [e, absk_neg, add_comm (absk (ℓ 1))]
    exact absk_add_le _ _
  have hk := kernel_le_Z1_E2 hm h01 h12 htri r Φ i
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _))
  simpa using hk

end OVNS.Quant

end
