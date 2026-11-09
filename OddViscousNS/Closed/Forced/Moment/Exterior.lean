import OddViscousNS.Closed.Forced.Moment.PairSound

/-!
# The exterior-`W` bound and the row-price convexity bound

With `r = C_l/J ∈ [0,1]`, prices `0 ≤ g ≤ M₀` and weights `u ≥ 1`:
`raw(W) ≤ (M₀/2)(1 + W/(W + 4a))` (`psi_bound`, convexity in `r`, maximum at `r ∈ {0,1}`).
`F(W) = (M₀/2)(1 + W/(W + 4a)) − λ(W − 1)` is concave; tangent-line bounds give
`F(W) ≤ F(w_lo)` for `0 < W ≤ w_lo` when `F'(w_lo) ≥ 0`, and `F(W) ≤ F(w_hi)` for `W ≥ w_hi` when
`F'(w_hi) ≤ 0` (`F'(W) = 2aM₀/(W + 4a)² − λ`).  Hence `exterior_bound`.
`convex_r_bound`: for fixed `W, L, H`, `r ↦ L W/(W + 4ar) + H W/(W + 4a(1 − r))` is bounded on
`[r₀, r₁] ⊆ [0,1]` by its values at the endpoints.
-/

open Set

namespace OVNS

namespace Forced

namespace Mom

private lemma M₀_nonneg : 0 ≤ M₀ := by norm_num [M₀]

private lemma sum_le_aux {a W r : ℝ} (ha : 0 < a) (hW : 0 < W) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    W / (W + 4 * a * r) + W / (W + 4 * a * (1 - r)) ≤ 1 + W / (W + 4 * a) := by
  have hA : 0 < W + 4 * a * r := by positivity
  have hB : 0 < W + 4 * a * (1 - r) := by nlinarith
  have hC : 0 < W + 4 * a := by positivity
  rw [div_add_div _ _ hA.ne' hB.ne', one_add_div hC.ne', div_le_div_iff₀ (mul_pos hA hB) hC]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha.le ha.le) (mul_nonneg hr0 (sub_nonneg.2 hr1)))
    (add_pos hC hW).le]

private lemma tangent_aux {a W w : ℝ} (ha : 0 < a) (hW : 0 < W) (hw : 0 < w) :
    W / (W + 4 * a) ≤ w / (w + 4 * a) + 4 * a / (w + 4 * a) ^ 2 * (W - w) := by
  have hA : 0 < W + 4 * a := by positivity
  have hB : 0 < w + 4 * a := by positivity
  have key : W / (W + 4 * a) - (w / (w + 4 * a) + 4 * a / (w + 4 * a) ^ 2 * (W - w)) =
      -(4 * a * (W - w) ^ 2) / ((W + 4 * a) * (w + 4 * a) ^ 2) := by
    field_simp
    ring
  have : -(4 * a * (W - w) ^ 2) / ((W + 4 * a) * (w + 4 * a) ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (W - w)]) (by positivity)
  linarith

private lemma convex_aux {c d r r0 r1 : ℝ} (hr : r ∈ Icc r0 r1) (h01 : r0 < r1)
    (hx0 : 0 < c + d * r0) (hx1 : 0 < c + d * r1) (hx : 0 < c + d * r) :
    (r1 - r0) * (1 / (c + d * r)) ≤ (r1 - r) * (1 / (c + d * r0)) +
      (r - r0) * (1 / (c + d * r1)) := by
  have hp : 0 ≤ r1 - r := sub_nonneg.2 hr.2
  have hq : 0 ≤ r - r0 := sub_nonneg.2 hr.1
  rw [mul_one_div, mul_one_div, mul_one_div, div_add_div _ _ hx0.ne' hx1.ne',
    div_le_div_iff₀ hx (mul_pos hx0 hx1)]
  nlinarith [mul_nonneg (mul_nonneg hp hq) (mul_nonneg (sq_nonneg d) (sub_nonneg.2 h01.le))]

/-- `raw ≤ (M₀/2)(1 + W/(W+4a))` for `r ∈ [0,1]`, prices `≤ M₀`, weights `≥ 1`. -/
theorem psi_bound {a W r gl gh ul uh : ℝ} (ha : 0 < a) (hW : 0 < W) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hgl0 : 0 ≤ gl) (hgl : gl ≤ M₀) (hgh0 : 0 ≤ gh) (hgh : gh ≤ M₀) (hul : 1 ≤ ul)
    (huh : 1 ≤ uh) :
    (gl * W / (ul * W + 4 * a * r) + gh * W / (uh * W + 4 * a * (1 - r))) / 2 ≤
      M₀ / 2 * (1 + W / (W + 4 * a)) := by
  have _h := And.intro hgl0 hgh0
  have hM := M₀_nonneg
  have hA : 0 < W + 4 * a * r := by positivity
  have hB : 0 < W + 4 * a * (1 - r) := by nlinarith
  have h1 : gl * W / (ul * W + 4 * a * r) ≤ M₀ * W / (W + 4 * a * r) :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hgl hW.le) hA (by nlinarith)
  have h2 : gh * W / (uh * W + 4 * a * (1 - r)) ≤ M₀ * W / (W + 4 * a * (1 - r)) :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hgh hW.le) hB (by nlinarith)
  have h3 := mul_le_mul_of_nonneg_left (sum_le_aux ha hW hr0 hr1) hM
  simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
  linarith

/-- The exterior bound: outside `[w_lo, w_hi]`, with the four rational endpoint checks. -/
theorem exterior_bound {a lam K wlo whi : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) (hwlo : 0 < wlo)
    (hlohi : wlo ≤ whi)
    (hFlo : M₀ / 2 * (1 + wlo / (wlo + 4 * a)) - lam * (wlo - 1) ≤ K)
    (hFhi : M₀ / 2 * (1 + whi / (whi + 4 * a)) - lam * (whi - 1) ≤ K)
    (hdlo : lam ≤ M₀ * (2 * a) / (wlo + 4 * a) ^ 2)
    (hdhi : M₀ * (2 * a) / (whi + 4 * a) ^ 2 ≤ lam)
    {W : ℝ} (hW : 0 < W) (hout : W < wlo ∨ whi < W) {r gl gh ul uh : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hgl0 : 0 ≤ gl) (hgl : gl ≤ M₀) (hgh0 : 0 ≤ gh) (hgh : gh ≤ M₀) (hul : 1 ≤ ul)
    (huh : 1 ≤ uh) :
    (gl * W / (ul * W + 4 * a * r) + gh * W / (uh * W + 4 * a * (1 - r))) / 2 - lam * (W - 1)
      ≤ K := by
  have _h := hlam
  have hM := M₀_nonneg
  have hpsi := psi_bound ha hW hr0 hr1 hgl0 hgl hgh0 hgh hul huh
  have tang : ∀ w : ℝ, 0 < w → M₀ / 2 * (1 + W / (W + 4 * a)) - lam * (W - 1) ≤
      M₀ / 2 * (1 + w / (w + 4 * a)) - lam * (w - 1) +
        (M₀ * (2 * a) / (w + 4 * a) ^ 2 - lam) * (W - w) := by
    intro w hw
    have t := mul_le_mul_of_nonneg_left (tangent_aux ha hW hw) (by positivity : 0 ≤ M₀ / 2)
    have e : M₀ * (2 * a) / (w + 4 * a) ^ 2 = M₀ / 2 * (4 * a / (w + 4 * a) ^ 2) := by ring
    rw [e]
    nlinarith
  rcases hout with h | h
  · have t := tang wlo hwlo
    have : (M₀ * (2 * a) / (wlo + 4 * a) ^ 2 - lam) * (W - wlo) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  · have t := tang whi (by linarith)
    have : (M₀ * (2 * a) / (whi + 4 * a) ^ 2 - lam) * (W - whi) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith

/-- Convexity in `r`: endpoint bound on `[r₀, r₁] ⊆ [0,1]`. -/
theorem convex_r_bound {a W L H r r0 r1 : ℝ} (ha : 0 < a) (hW : 0 < W) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hr0 : 0 ≤ r0) (hr1 : r1 ≤ 1) (hr : r ∈ Icc r0 r1) :
    (L * W / (W + 4 * a * r) + H * W / (W + 4 * a * (1 - r))) / 2 ≤
      max ((L * W / (W + 4 * a * r0) + H * W / (W + 4 * a * (1 - r0))) / 2)
        ((L * W / (W + 4 * a * r1) + H * W / (W + 4 * a * (1 - r1))) / 2) := by
  obtain ⟨hr0r, hrr1⟩ := hr
  rcases eq_or_lt_of_le (hr0r.trans hrr1) with h01 | h01
  · have : r = r0 := le_antisymm (h01 ▸ hrr1) hr0r
    subst this
    exact le_max_left _ _
  have hD : 0 < r1 - r0 := sub_pos.2 h01
  have hx0 : 0 < W + 4 * a * r0 := by positivity
  have hx1 : 0 < W + 4 * a * r1 := by nlinarith
  have hx : 0 < W + 4 * a * r := by nlinarith
  have hy0 : 0 < W + 4 * a * (1 - r0) := by nlinarith
  have hy1 : 0 < W + 4 * a * (1 - r1) := by nlinarith
  have hy : 0 < W + 4 * a * (1 - r) := by nlinarith
  have e : ∀ s : ℝ, W + 4 * a * (1 - s) = (W + 4 * a) + (-(4 * a)) * s := fun s ↦ by ring
  have c1 := convex_aux (c := W) (d := 4 * a) ⟨hr0r, hrr1⟩ h01 hx0 hx1 hx
  have c2 := convex_aux (c := W + 4 * a) (d := -(4 * a)) ⟨hr0r, hrr1⟩ h01
    (by rw [← e]; exact hy0) (by rw [← e]; exact hy1) (by rw [← e]; exact hy)
  rw [← e, ← e, ← e] at c2
  have d1 := mul_le_mul_of_nonneg_left c1 (mul_nonneg hL hW.le)
  have d2 := mul_le_mul_of_nonneg_left c2 (mul_nonneg hH hW.le)
  set m := max ((L * W / (W + 4 * a * r0) + H * W / (W + 4 * a * (1 - r0))) / 2)
    ((L * W / (W + 4 * a * r1) + H * W / (W + 4 * a * (1 - r1))) / 2) with hm
  have m0 := le_max_left ((L * W / (W + 4 * a * r0) + H * W / (W + 4 * a * (1 - r0))) / 2)
    ((L * W / (W + 4 * a * r1) + H * W / (W + 4 * a * (1 - r1))) / 2)
  have m1 := le_max_right ((L * W / (W + 4 * a * r0) + H * W / (W + 4 * a * (1 - r0))) / 2)
    ((L * W / (W + 4 * a * r1) + H * W / (W + 4 * a * (1 - r1))) / 2)
  rw [← hm] at m0 m1
  refine le_of_mul_le_mul_left ?_ hD
  have p0 := mul_le_mul_of_nonneg_left m0 (sub_nonneg.2 hrr1)
  have p1 := mul_le_mul_of_nonneg_left m1 (sub_nonneg.2 hr0r)
  simp only [div_eq_mul_inv, one_mul] at d1 d2 p0 p1 ⊢
  linarith

/-- Monotonicity of the row-price value in the prices. -/
theorem rawRr_mono_prices {a W r L H L' H' : ℝ} (ha : 0 ≤ a) (hW : 0 ≤ W) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hL : L ≤ L') (hH : H ≤ H') : rawRr a L H r W ≤ rawRr a L' H' r W := by
  unfold rawRr
  have hA : 0 ≤ W + 4 * a * r := by positivity
  have hB : 0 ≤ W + 4 * a * (1 - r) := by nlinarith
  have h1 : L * W / (W + 4 * a * r) ≤ L' * W / (W + 4 * a * r) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hL hW) hA
  have h2 : H * W / (W + 4 * a * (1 - r)) ≤ H' * W / (W + 4 * a * (1 - r)) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hH hW) hB
  linarith

end Mom

end Forced

end OVNS
