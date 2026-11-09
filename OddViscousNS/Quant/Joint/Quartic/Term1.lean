import OddViscousNS.Quant.Joint.Quartic.Term

/-!
# The fourth correction at weight one: one label (step J5, node N11)

Body 35 (LOCAL496), Body 43 for `ε`.  With `P = ‖t‖‖w‖‖u‖‖v‖`, `k = p + q`, `K = mxL`:

* `termQ_one_static`: `√q ‖Q₄,₁‖ ≤ 2¹² kT (|s|^{3/2}‖t‖) ‖w‖ (|q|‖u‖) (|k|‖v‖)`.  "Use this `K` to
  replace the original largest `H²` norm factor by `H¹` pointwise".
* `term1_eps`: `q^{1−ε} ‖Q₄,₁‖ ≤ 2¹² |s|^{−ε} K |p||q||k| kT P`, before the placements.
* The placements of Body 35 need only the triangle inequality for the largest leg, `K ≤` the sum of
  any two legs (`mxL_tri`): the cases "an exterior of length `≥ K/2`", "`≥ K/4`", "`h ≥ 3K/4`" are
  not needed.
  - `termQ_one_in`, for a slow or inner fast derivative: `K ≤ |q| + |k|`, so `H²` is on an exterior;
    `|s|^{−ε} ≤ |l|^{−ε}` stays on the inner slot.
  - `termQ_one_q`, for a derivative at `q`: `K ≤ |p| + |k|`: `H²` on `h` or on the unchanged exterior.
  - `termQ_one_e`, for a derivative at `e`: `K ≤ |p| + |q|`.
* `srcQ_one_le`: the source.
-/

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {r : ℝ} {x : L4} {d a b c : Sgn} {t w u v : V3} {τ : ℝ}

/-- **One label of `Q₄,₁`**, the static bound. -/
theorem termQ_one_static (hr : r ≠ 0) (hx : Act x) (τ : ℝ) (t w u v : V3) :
    Real.sqrt |r| * ‖termQ 1 r x τ t w u v‖ ≤ 2 ^ 12 * kT |r| (x.1, x.2.1) *
      ((absk x.2.2 * Real.sqrt (absk x.2.2) * ‖t‖) * ‖w‖ * (absk x.2.1 * ‖u‖) *
        (absk (x.1 + x.2.1) * ‖v‖)) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hsq : 0 < Real.sqrt |r| := Real.sqrt_pos.2 hq
  have hk := kT_nonneg |r| (x.1, x.2.1)
  have hA := amp_nonneg t w u v
  set Y := absk x.2.1 * absk (x.1 + x.2.1) * kT |r| (x.1, x.2.1) * amp t w u v with hY
  have hY0 : 0 ≤ Y := by
    have := absk_nonneg x.2.1
    have := absk_nonneg (x.1 + x.2.1)
    positivity
  have hs0 := absk_nonneg x.2.2
  have hW : 0 ≤ absk x.2.2 * Real.sqrt (absk x.2.2) * Y := by positivity
  have hB : 0 ≤ 235 * (absk x.2.2 * Real.sqrt (absk x.2.2) * Y) / Real.sqrt |r| := by positivity
  have hmain := termQ_le (j := 1) (r := r) (x := x) (t := t) (w := w) (u := u) (v := v) (τ := τ)
    hB fun d a b c hN => ?_
  · have h1 := mul_le_mul_of_nonneg_left hmain hsq.le
    refine h1.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_right
      (by norm_num : (16 * 235 : ℝ) ≤ 2 ^ 12) hW)) |>.trans (le_of_eq ?_)
    · field_simp
    · simp only [hY, amp]
      ring
  · have hc := coreQ_one_le hx r d a b c t w u v
    have hR := Rq_nonneg r d b c x
    by_cases hμ : hiMu x.2.2 (inL x) = 0
    · rw [hμ] at hc
      have h0 : ‖coreQ 1 r x d a b c t w u v‖ ≤ 0 := by simpa using hc
      exact (mul_le_mul_of_nonneg_left h0 hR).trans (by simpa using hB)
    have hS := sep_of hμ
    have hs := Sep.s_pos hS hx
    have hs1 : 0 < absk x.2.2 := by linarith
    have hmx0 : 0 ≤ mxL x.1 x.2.1 := (absk_nonneg _).trans (le_mxL _ _).1
    have h1 := R_static (d := d) hr hx hS hN
    rw [Real.sqrt_mul hq.le] at h1
    have hp := Sep.p_le hS
    have hp0 := absk_nonneg x.1
    have hp2 : absk x.1 ^ 2 ≤ (17 / 16 * absk x.2.2) ^ 2 := pow_le_pow_left₀ hp0 hp 2
    have hμ1 := hiMu_le_one x.2.2 (inL x)
    have hμ0 := hiMu_nonneg x.2.2 (inL x)
    set ρ := Rq r d b c x * mxL x.1 x.2.1 with hρ
    have hρ0 : 0 ≤ ρ := mul_nonneg hR hmx0
    set S2 := Real.sqrt (absk x.2.2) with hS2
    have hS20 : 0 ≤ S2 := Real.sqrt_nonneg _
    have hSS : S2 * S2 = absk x.2.2 := Real.mul_self_sqrt hs0
    rw [le_div_iff₀ hsq]
    have e : Rq r d b c x * (104 * hiMu x.2.2 (inL x) * (mxL x.1 x.2.1 * absk x.1 ^ 2 * absk x.2.1 *
        absk (x.1 + x.2.1)) * kT |r| (x.1, x.2.1) * amp t w u v) * Real.sqrt |r| =
        104 * (hiMu x.2.2 (inL x) * (ρ * Real.sqrt |r| * absk x.1 ^ 2 * Y)) := by
      simp only [hρ, hY]
      ring
    have h2 := mul_le_mul_of_nonneg_left hc hR
    have h3 := mul_le_mul_of_nonneg_right h2 hsq.le
    rw [e] at h3
    refine h3.trans ?_
    have h4 : ρ * Real.sqrt |r| * absk x.1 ^ 2 ≤ 2 * (289 / 256) * (absk x.2.2 * S2) := by
      have e1 : (17 / 16 * absk x.2.2) ^ 2 = (289 / 256) * (absk x.2.2 * S2) * S2 := by
        have : absk x.2.2 ^ 2 = absk x.2.2 * (S2 * S2) := by rw [hSS]; ring
        calc (17 / 16 * absk x.2.2) ^ 2 = 289 / 256 * absk x.2.2 ^ 2 := by ring
          _ = _ := by rw [this]; ring
      have h5 : ρ * Real.sqrt |r| * absk x.1 ^ 2 ≤ ρ * Real.sqrt |r| *
          ((289 / 256) * (absk x.2.2 * S2) * S2) := by
        rw [← e1]
        exact mul_le_mul_of_nonneg_left hp2 (by positivity)
      have e2 : ρ * Real.sqrt |r| * ((289 / 256) * (absk x.2.2 * S2) * S2) =
          (ρ * (Real.sqrt |r| * S2)) * ((289 / 256) * (absk x.2.2 * S2)) := by ring
      rw [e2] at h5
      have h6 := mul_le_mul_of_nonneg_right h1 (by positivity :
        0 ≤ (289 / 256 : ℝ) * (absk x.2.2 * S2))
      linarith only [h5, h6]
    have h7 : ρ * Real.sqrt |r| * absk x.1 ^ 2 * Y ≤ 2 * (289 / 256) * (absk x.2.2 * S2) * Y :=
      mul_le_mul_of_nonneg_right h4 hY0
    have h8 : 0 ≤ ρ * Real.sqrt |r| * absk x.1 ^ 2 * Y := by positivity
    have h9 : hiMu x.2.2 (inL x) * (ρ * Real.sqrt |r| * absk x.1 ^ 2 * Y) ≤
        ρ * Real.sqrt |r| * absk x.1 ^ 2 * Y := by nlinarith only [h8, hμ1]
    have h10 : 0 ≤ absk x.2.2 * S2 * Y := by positivity
    nlinarith only [h7, h9, h10]

/-- **One label of `Q₄,₁`**, the interpolated denominator, before the placements. -/
theorem term1_eps (hr : r ≠ 0) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hx : Act x) {B : ℝ} (hB : 0 ≤ B)
    (h : Sep x → 2 ^ 12 * (absk x.2.2)⁻¹ ^ ε *
      (mxL x.1 x.2.1 * absk x.1 * absk x.2.1 * absk (x.1 + x.2.1)) * kT |r| (x.1, x.2.1) *
        amp t w u v ≤ B) :
    |r| ^ (1 - ε) * ‖termQ 1 r x τ t w u v‖ ≤ B := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hqe : 0 < |r| ^ (1 - ε) := Real.rpow_pos_of_pos hq _
  have hB' : 0 ≤ B / 16 / |r| ^ (1 - ε) := by positivity
  have hmain := termQ_le (j := 1) (r := r) (x := x) (t := t) (w := w) (u := u) (v := v) (τ := τ)
    hB' fun d a b c hN => ?_
  · have h2 := mul_le_mul_of_nonneg_left hmain hqe.le
    refine h2.trans (le_of_eq ?_)
    field_simp
  · have hc := coreQ_one_le hx r d a b c t w u v
    have hR := Rq_nonneg r d b c x
    by_cases hμ : hiMu x.2.2 (inL x) = 0
    · rw [hμ] at hc
      have h3 : ‖coreQ 1 r x d a b c t w u v‖ ≤ 0 := by simpa using hc
      exact (mul_le_mul_of_nonneg_left h3 hR).trans (by simpa using hB')
    have hS := sep_of hμ
    have hs := Sep.s_pos hS hx
    have hs1 : 0 < absk x.2.2 := by linarith
    have hmx0 : 0 ≤ mxL x.1 x.2.1 := (absk_nonneg _).trans (le_mxL _ _).1
    have hk := kT_nonneg |r| (x.1, x.2.1)
    have hA := amp_nonneg t w u v
    have hl0 := absk_nonneg x.2.1
    have hk0 := absk_nonneg (x.1 + x.2.1)
    have hp0 := absk_nonneg x.1
    have hp := Sep.p_le hS
    have hμ1 := hiMu_le_one x.2.2 (inL x)
    have hμ0 := hiMu_nonneg x.2.2 (inL x)
    have h3 := R_eps (d := d) hr hx hS hN h0 h1
    set Se := (absk x.2.2)⁻¹ ^ ε with hSe
    have hSe0 : 0 < Se := Real.rpow_pos_of_pos (inv_pos.2 hs1) _
    have e1 : absk x.2.2 ^ (1 + ε) * Se = absk x.2.2 := by
      rw [hSe, Real.inv_rpow hs1.le, Real.rpow_add hs1, Real.rpow_one]
      field_simp
    set Rr := Rq r d b c x with hRr
    set qe := |r| ^ (1 - ε) with hqedef
    -- `Rr qe ≤ 2 Se / |s|`
    have h4 : Rr * qe * absk x.2.2 ≤ 2 * Se := by
      have := mul_le_mul_of_nonneg_right h3 hSe0.le
      have e4 : Rr * (qe * absk x.2.2 ^ (1 + ε)) * Se =
          Rr * qe * (absk x.2.2 ^ (1 + ε) * Se) := by ring
      rw [e4, e1] at this
      exact this
    have h5 : absk x.1 ^ 2 ≤ 17 / 16 * absk x.2.2 * absk x.1 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hp hp0
    set Y := mxL x.1 x.2.1 * absk x.2.1 * absk (x.1 + x.2.1) * kT |r| (x.1, x.2.1) * amp t w u v
      with hY
    have hY0 : 0 ≤ Y := by positivity
    have h6 : Rr * qe * absk x.1 ^ 2 ≤ 17 / 8 * Se * absk x.1 := by
      have h7 : Rr * qe * absk x.1 ^ 2 ≤ Rr * qe * (17 / 16 * absk x.2.2 * absk x.1) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
      have e2 : Rr * qe * (17 / 16 * absk x.2.2 * absk x.1) =
          (Rr * qe * absk x.2.2) * (17 / 16 * absk x.1) := by ring
      rw [e2] at h7
      have h8 := mul_le_mul_of_nonneg_right h4 (by positivity : 0 ≤ 17 / 16 * absk x.1)
      linarith only [h7, h8]
    have hle : Rr * ‖coreQ 1 r x d a b c t w u v‖ * qe ≤ 221 * (Se * absk x.1 * Y) := by
      have h7 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hR) hqe.le
      refine h7.trans ?_
      have e2 : Rr * (104 * hiMu x.2.2 (inL x) * (mxL x.1 x.2.1 * absk x.1 ^ 2 * absk x.2.1 *
          absk (x.1 + x.2.1)) * kT |r| (x.1, x.2.1) * amp t w u v) * qe =
          104 * hiMu x.2.2 (inL x) * ((Rr * qe * absk x.1 ^ 2) * Y) := by
        simp only [hY]
        ring
      rw [e2]
      have h8 := mul_le_mul_of_nonneg_right h6 hY0
      have h9 : 0 ≤ (Rr * qe * absk x.1 ^ 2) * Y := by positivity
      have h10 : hiMu x.2.2 (inL x) * ((Rr * qe * absk x.1 ^ 2) * Y) ≤
          (Rr * qe * absk x.1 ^ 2) * Y := by nlinarith only [h9, hμ1]
      have h11 : 0 ≤ Se * absk x.1 * Y := by positivity
      nlinarith only [h8, h10, h11]
    have h12 := h hS
    have e3 : 2 ^ 12 * Se * (mxL x.1 x.2.1 * absk x.1 * absk x.2.1 * absk (x.1 + x.2.1)) *
        kT |r| (x.1, x.2.1) * amp t w u v = 2 ^ 12 * (Se * absk x.1 * Y) := by
      simp only [hY]
      ring
    rw [e3] at h12
    rw [div_div, le_div_iff₀ (by positivity : 0 < 16 * qe)]
    have h13 : 0 ≤ Se * absk x.1 * Y := by positivity
    nlinarith only [hle, h12, h13]

/-! ### The placements -/

/-- `(|s|⁻¹)^ε ≤ 1` for `|s| ≥ 1`. -/
lemma inv_rpow_le_one {y ε : ℝ} (hy : 1 ≤ y) (h0 : 0 ≤ ε) : y⁻¹ ^ ε ≤ 1 :=
  Real.rpow_le_one (by positivity) (inv_le_one_of_one_le₀ hy) h0

/-- **A slow or inner fast derivative** (Body 35): the first two placements. -/
theorem termQ_one_in (hr : r ≠ 0) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hx : Act x) (τ : ℝ)
    (t w u v : V3) :
    |r| ^ (1 - ε) * ‖termQ 1 r x τ t w u v‖ ≤ 2 ^ 13 * kT |r| (x.1, x.2.1) *
      ((absk x.2.2 * ‖t‖) * ((absk (inL x))⁻¹ ^ ε * ‖w‖) * (absk x.2.1 ^ 2 * ‖u‖) *
          (absk (x.1 + x.2.1) * ‖v‖) +
        (absk x.2.2 * ‖t‖) * ((absk (inL x))⁻¹ ^ ε * ‖w‖) * (absk x.2.1 * ‖u‖) *
          (absk (x.1 + x.2.1) ^ 2 * ‖v‖)) := by
  have hk := kT_nonneg |r| (x.1, x.2.1)
  have hl1 := absk_nonneg (inL x)
  have hLe : 0 ≤ (absk (inL x))⁻¹ ^ ε := by positivity
  have hs0 := absk_nonneg x.2.2
  have hq0 := absk_nonneg x.2.1
  have hk0 := absk_nonneg (x.1 + x.2.1)
  have hB : 0 ≤ 2 ^ 13 * kT |r| (x.1, x.2.1) *
      ((absk x.2.2 * ‖t‖) * ((absk (inL x))⁻¹ ^ ε * ‖w‖) * (absk x.2.1 ^ 2 * ‖u‖) *
          (absk (x.1 + x.2.1) * ‖v‖) +
        (absk x.2.2 * ‖t‖) * ((absk (inL x))⁻¹ ^ ε * ‖w‖) * (absk x.2.1 * ‖u‖) *
          (absk (x.1 + x.2.1) ^ 2 * ‖v‖)) := by positivity
  refine term1_eps hr h0 h1 hx hB fun hS => ?_
  have hl := Sep.l_ge hx
  have hle : absk (inL x) ≤ absk x.2.2 := Sep.l_le hS
  have hSe : (absk x.2.2)⁻¹ ^ ε ≤ (absk (inL x))⁻¹ ^ ε :=
    Real.rpow_le_rpow (by positivity) (inv_anti₀ (by linarith) hle) h0
  have hSe0 : 0 ≤ (absk x.2.2)⁻¹ ^ ε := by positivity
  have hmx := (mxL_tri x.1 x.2.1).1
  have hmx0 : 0 ≤ mxL x.1 x.2.1 := (absk_nonneg _).trans (le_mxL _ _).1
  have hp := Sep.p_le hS
  have hp0 := absk_nonneg x.1
  set Le := (absk (inL x))⁻¹ ^ ε
  set Se := (absk x.2.2)⁻¹ ^ ε
  set m := mxL x.1 x.2.1
  set P := absk x.1
  set s := absk x.2.2
  set q := absk x.2.1
  set k := absk (x.1 + x.2.1)
  have h2 : m * P ≤ (q + k) * (17 / 16 * s) := mul_le_mul hmx hp hp0 (by positivity)
  have h3 : Se * (m * P) ≤ Le * ((q + k) * (17 / 16 * s)) :=
    mul_le_mul hSe h2 (by positivity) hLe
  have hA := amp_nonneg t w u v
  have hQ : 0 ≤ q * k * kT |r| (x.1, x.2.1) * amp t w u v := by positivity
  have h4 := mul_le_mul_of_nonneg_right h3 hQ
  have e1 : 2 ^ 12 * Se * (m * P * q * k) * kT |r| (x.1, x.2.1) * amp t w u v =
      2 ^ 12 * (Se * (m * P) * (q * k * kT |r| (x.1, x.2.1) * amp t w u v)) := by ring
  have e2 : 2 ^ 13 * kT |r| (x.1, x.2.1) * ((s * ‖t‖) * (Le * ‖w‖) * (q ^ 2 * ‖u‖) * (k * ‖v‖) +
      (s * ‖t‖) * (Le * ‖w‖) * (q * ‖u‖) * (k ^ 2 * ‖v‖)) =
      2 ^ 12 * (2 * (Le * ((q + k) * s) * (q * k * kT |r| (x.1, x.2.1) * amp t w u v))) := by
    simp only [amp]
    ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine h4.trans ?_
  have h5 : 0 ≤ Le * ((q + k) * s) * (q * k * kT |r| (x.1, x.2.1) * amp t w u v) := by positivity
  have e3 : Le * ((q + k) * (17 / 16 * s)) * (q * k * kT |r| (x.1, x.2.1) * amp t w u v) =
      17 / 16 * (Le * ((q + k) * s) * (q * k * kT |r| (x.1, x.2.1) * amp t w u v)) := by ring
  rw [e3]
  linarith only [h5]

/-- **A derivative at the outer leg `q`** (Body 35): the last two placements. -/
theorem termQ_one_q (hr : r ≠ 0) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hx : Act x) (τ : ℝ)
    (t w u v : V3) :
    |r| ^ (1 - ε) * ‖termQ 1 r x τ t w u v‖ ≤ 2 ^ 13 * kT |r| (x.1, x.2.1) *
      ((absk x.2.2 ^ 2 * ‖t‖) * ‖w‖ * (absk x.2.1 * ‖u‖) * (absk (x.1 + x.2.1) * ‖v‖) +
        (absk x.2.2 * ‖t‖) * ‖w‖ * (absk x.2.1 * ‖u‖) * (absk (x.1 + x.2.1) ^ 2 * ‖v‖)) := by
  have hk := kT_nonneg |r| (x.1, x.2.1)
  have hs0 := absk_nonneg x.2.2
  have hq0 := absk_nonneg x.2.1
  have hk0 := absk_nonneg (x.1 + x.2.1)
  have hB : 0 ≤ 2 ^ 13 * kT |r| (x.1, x.2.1) *
      ((absk x.2.2 ^ 2 * ‖t‖) * ‖w‖ * (absk x.2.1 * ‖u‖) * (absk (x.1 + x.2.1) * ‖v‖) +
        (absk x.2.2 * ‖t‖) * ‖w‖ * (absk x.2.1 * ‖u‖) * (absk (x.1 + x.2.1) ^ 2 * ‖v‖)) := by
    positivity
  refine term1_eps hr h0 h1 hx hB fun hS => ?_
  have hs1 : 1 ≤ absk x.2.2 := by
    have := Sep.s_pos hS hx
    linarith
  have hSe := inv_rpow_le_one hs1 h0
  have hSe0 : 0 ≤ (absk x.2.2)⁻¹ ^ ε := by positivity
  have hmx := (mxL_tri x.1 x.2.1).2.1
  have hmx0 : 0 ≤ mxL x.1 x.2.1 := (absk_nonneg _).trans (le_mxL _ _).1
  have hp := Sep.p_le hS
  have hp0 := absk_nonneg x.1
  set Se := (absk x.2.2)⁻¹ ^ ε
  set m := mxL x.1 x.2.1
  set P := absk x.1
  set s := absk x.2.2
  set q := absk x.2.1
  set k := absk (x.1 + x.2.1)
  have h2 : m * P ≤ (17 / 16 * s + k) * (17 / 16 * s) :=
    mul_le_mul (hmx.trans (by linarith)) hp hp0 (by positivity)
  have h3 : Se * (m * P) ≤ 1 * ((17 / 16 * s + k) * (17 / 16 * s)) :=
    mul_le_mul hSe h2 (by positivity) (by norm_num)
  have hA := amp_nonneg t w u v
  have hQ : 0 ≤ q * k * kT |r| (x.1, x.2.1) * amp t w u v := by positivity
  have h4 := mul_le_mul_of_nonneg_right h3 hQ
  have e1 : 2 ^ 12 * Se * (m * P * q * k) * kT |r| (x.1, x.2.1) * amp t w u v =
      2 ^ 12 * (Se * (m * P) * (q * k * kT |r| (x.1, x.2.1) * amp t w u v)) := by ring
  have e2 : 2 ^ 13 * kT |r| (x.1, x.2.1) * ((s ^ 2 * ‖t‖) * ‖w‖ * (q * ‖u‖) * (k * ‖v‖) +
      (s * ‖t‖) * ‖w‖ * (q * ‖u‖) * (k ^ 2 * ‖v‖)) =
      2 ^ 12 * (2 * ((s + k) * s * (q * k * kT |r| (x.1, x.2.1) * amp t w u v))) := by
    simp only [amp]
    ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine h4.trans ?_
  set Q := q * k * kT |r| (x.1, x.2.1) * amp t w u v
  have h5 : 0 ≤ s ^ 2 * Q := by positivity
  have h6 : 0 ≤ s * k * Q := by positivity
  nlinarith only [h5, h6]

/-- **A derivative at the outer leg `e`** (Body 35). -/
theorem termQ_one_e (hr : r ≠ 0) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hx : Act x) (τ : ℝ)
    (t w u v : V3) :
    |r| ^ (1 - ε) * ‖termQ 1 r x τ t w u v‖ ≤ 2 ^ 13 * kT |r| (x.1, x.2.1) *
      ((absk x.2.2 ^ 2 * ‖t‖) * ‖w‖ * (absk x.2.1 * ‖u‖) * (absk (x.1 + x.2.1) * ‖v‖) +
        (absk x.2.2 * ‖t‖) * ‖w‖ * (absk x.2.1 ^ 2 * ‖u‖) * (absk (x.1 + x.2.1) * ‖v‖)) := by
  have hk := kT_nonneg |r| (x.1, x.2.1)
  have hs0 := absk_nonneg x.2.2
  have hq0 := absk_nonneg x.2.1
  have hk0 := absk_nonneg (x.1 + x.2.1)
  have hB : 0 ≤ 2 ^ 13 * kT |r| (x.1, x.2.1) *
      ((absk x.2.2 ^ 2 * ‖t‖) * ‖w‖ * (absk x.2.1 * ‖u‖) * (absk (x.1 + x.2.1) * ‖v‖) +
        (absk x.2.2 * ‖t‖) * ‖w‖ * (absk x.2.1 ^ 2 * ‖u‖) * (absk (x.1 + x.2.1) * ‖v‖)) := by
    positivity
  refine term1_eps hr h0 h1 hx hB fun hS => ?_
  have hs1 : 1 ≤ absk x.2.2 := by
    have := Sep.s_pos hS hx
    linarith
  have hSe := inv_rpow_le_one hs1 h0
  have hSe0 : 0 ≤ (absk x.2.2)⁻¹ ^ ε := by positivity
  have hmx := (mxL_tri x.1 x.2.1).2.2
  have hmx0 : 0 ≤ mxL x.1 x.2.1 := (absk_nonneg _).trans (le_mxL _ _).1
  have hp := Sep.p_le hS
  have hp0 := absk_nonneg x.1
  set Se := (absk x.2.2)⁻¹ ^ ε
  set m := mxL x.1 x.2.1
  set P := absk x.1
  set s := absk x.2.2
  set q := absk x.2.1
  set k := absk (x.1 + x.2.1)
  have h2 : m * P ≤ (17 / 16 * s + q) * (17 / 16 * s) :=
    mul_le_mul (hmx.trans (by linarith)) hp hp0 (by positivity)
  have h3 : Se * (m * P) ≤ 1 * ((17 / 16 * s + q) * (17 / 16 * s)) :=
    mul_le_mul hSe h2 (by positivity) (by norm_num)
  have hA := amp_nonneg t w u v
  have hQ : 0 ≤ q * k * kT |r| (x.1, x.2.1) * amp t w u v := by positivity
  have h4 := mul_le_mul_of_nonneg_right h3 hQ
  have e1 : 2 ^ 12 * Se * (m * P * q * k) * kT |r| (x.1, x.2.1) * amp t w u v =
      2 ^ 12 * (Se * (m * P) * (q * k * kT |r| (x.1, x.2.1) * amp t w u v)) := by ring
  have e2 : 2 ^ 13 * kT |r| (x.1, x.2.1) * ((s ^ 2 * ‖t‖) * ‖w‖ * (q * ‖u‖) * (k * ‖v‖) +
      (s * ‖t‖) * ‖w‖ * (q ^ 2 * ‖u‖) * (k * ‖v‖)) =
      2 ^ 12 * (2 * ((s + q) * s * (q * k * kT |r| (x.1, x.2.1) * amp t w u v))) := by
    simp only [amp]
    ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine h4.trans ?_
  set Q := q * k * kT |r| (x.1, x.2.1) * amp t w u v
  have h5 : 0 ≤ s ^ 2 * Q := by positivity
  have h6 : 0 ≤ s * q * Q := by positivity
  nlinarith only [h5, h6]

/-- **One label of the source**, weight one: `H²` on an exterior, `H¹` on the other two legs. -/
theorem srcQ_one_le (hx : Act x) (r τ : ℝ) (t w u v : V3) :
    ‖srcQ 1 r x τ t w u v‖ ≤ 2 ^ 13 * kT |r| (x.1, x.2.1) *
      ((absk x.2.2 ^ 2 * ‖t‖) * ‖w‖ * (absk x.2.1 ^ 2 * ‖u‖) * (absk (x.1 + x.2.1) * ‖v‖) +
        (absk x.2.2 ^ 2 * ‖t‖) * ‖w‖ * (absk x.2.1 * ‖u‖) * (absk (x.1 + x.2.1) ^ 2 * ‖v‖)) := by
  have hk := kT_nonneg |r| (x.1, x.2.1)
  have hA := amp_nonneg t w u v
  have hs0 := absk_nonneg x.2.2
  have hq0 := absk_nonneg x.2.1
  have hk0 := absk_nonneg (x.1 + x.2.1)
  set B : ℝ := 2 ^ 9 * kT |r| (x.1, x.2.1) *
      ((absk x.2.2 ^ 2 * ‖t‖) * ‖w‖ * (absk x.2.1 ^ 2 * ‖u‖) * (absk (x.1 + x.2.1) * ‖v‖) +
        (absk x.2.2 ^ 2 * ‖t‖) * ‖w‖ * (absk x.2.1 * ‖u‖) * (absk (x.1 + x.2.1) ^ 2 * ‖v‖)) with hBd
  have hB : 0 ≤ B := by positivity
  have hmain := srcQ_le (j := 1) (r := r) (x := x) (t := t) (w := w) (u := u) (v := v) (τ := τ)
    hB fun d a b c hN => ?_
  · refine hmain.trans (le_of_eq ?_)
    simp only [hBd]
    ring
  · have hc := coreQ_one_le hx r d a b c t w u v
    by_cases hμ : hiMu x.2.2 (inL x) = 0
    · rw [hμ] at hc
      have h0 : ‖coreQ 1 r x d a b c t w u v‖ ≤ 0 := by simpa using hc
      exact h0.trans hB
    have hS := sep_of hμ
    have hp := Sep.p_le hS
    have hp0 := absk_nonneg x.1
    have hp2 : absk x.1 ^ 2 ≤ (17 / 16 * absk x.2.2) ^ 2 := pow_le_pow_left₀ hp0 hp 2
    have hμ1 := hiMu_le_one x.2.2 (inL x)
    have hμ0 := hiMu_nonneg x.2.2 (inL x)
    have hmx := (mxL_tri x.1 x.2.1).1
    have hmx0 : 0 ≤ mxL x.1 x.2.1 := (absk_nonneg _).trans (le_mxL _ _).1
    refine hc.trans ?_
    set m := mxL x.1 x.2.1
    set s := absk x.2.2
    set q := absk x.2.1
    set k := absk (x.1 + x.2.1)
    set Q := q * k * kT |r| (x.1, x.2.1) * amp t w u v with hQd
    have hQ : 0 ≤ Q := by positivity
    have e1 : 104 * hiMu x.2.2 (inL x) * (m * absk x.1 ^ 2 * q * k) * kT |r| (x.1, x.2.1) *
        amp t w u v = 104 * (hiMu x.2.2 (inL x) * (m * absk x.1 ^ 2 * Q)) := by
      simp only [hQd]
      ring
    have e2 : B = 2 ^ 9 * ((q + k) * s ^ 2 * Q) := by
      simp only [hBd, hQd, amp]
      ring
    rw [e1, e2]
    have h1 : m * absk x.1 ^ 2 ≤ (q + k) * (17 / 16 * s) ^ 2 :=
      mul_le_mul hmx hp2 (by positivity) (by positivity)
    have h2 := mul_le_mul_of_nonneg_right h1 hQ
    have h3 : 0 ≤ m * absk x.1 ^ 2 * Q := by positivity
    have h4 : hiMu x.2.2 (inL x) * (m * absk x.1 ^ 2 * Q) ≤ m * absk x.1 ^ 2 * Q := by
      nlinarith only [h3, hμ1]
    have h5 : 0 ≤ (q + k) * s ^ 2 * Q := by positivity
    have e3 : (q + k) * (17 / 16 * s) ^ 2 * Q = (17 / 16) ^ 2 * ((q + k) * s ^ 2 * Q) := by ring
    rw [e3] at h2
    nlinarith only [h2, h4, h5]

end OVNS.Quant.Quartic

end
