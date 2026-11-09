import OddViscousNS.Quant.Joint.Metric.Block
import OddViscousNS.Quant.Joint.Metric.Product

/-!
# Rows 2 and 3 of Table quant-metric: the high ancestors (step J5, pilot)

`rowM2`, `rowM3` of `Joint/Interfaces.lean` as theorems on the actual Fourier-side forms.

## The estimates at a fixed time
With `W = ‖Ŝ‖_{ℓ¹}`, `b = ‖S‖₂`, `W_>, b_>` the tails at `D`, `q = |r|`, `z` the fast energy vector:
* `YLForm_high_le`: the undifferentiated group `X₂𝓛 + 𝓛*X₂ + Z𝓛 + 𝓛*Z` with at least one ancestor at
  `|p| > D` costs `C q⁻¹ (W_> b² + W b b_>) ‖z‖²` (LOCAL440 step 1, LOCAL441), for every multiplier
  of modulus at most one on that sector ("multiplying only by a scalar between zero and one",
  Body 42): this is what the high-last complement of Body 42 needs.
* `X2Half_high_le`: `‖A^{1/2} X_{2,hi}‖ ≤ C q⁻¹ b b_>` (Body 41, LOCAL655), whence the companion
  `q⁻¹ M_∞ b b_>` of the low-last `X₂`, by pairing with `A^{−1/2} 𝓛_lo z`.
* `DSX2_high_le`: the high-intermediate sector `M > D`, `M ≥ 4 max(L, J)` of `D_S X₂[h]` costs
  `C q⁻¹ ‖h‖₁ b_{>D/2} ‖z‖²` (Bodies 33, 42), the companion `q⁻¹ f₁ b_{>cD}`.
* `tailW_le`: `W_> ≤ 5 D⁻¹ b`, the inverse-fourth tail of the slow lattice.
* `tailB_le_of_split`: `b_> ≤ D⁻¹ ‖y‖₃ + ‖R‖₂` for `S = y − R`, `y ∈ H³`.

## Proof of the first estimate, from the blocks
`norm_YLb_le` is the kernel: on three slow leaves and a fast input, `(C/q) f_a f_b f_c E_2^z`.
`hiMask₃` enlarges to one restricted leaf in each of the three slots (`mask₃_le`), overlaps
included.  `pos3_E3` is the convolution with one restricted leaf.  The arithmetic is `cls3_tail`.

## The conclusion
`row23_piece`: on a joint piece, with the hypotheses of `H2EnergyInterfaceB`, the multiplier `rowG`
is nonnegative and integrable, dominates the three high-ancestor forms at a.e. time, and has clip
mass at most `2⁻³⁵` on every clip of length `1/λ_*`, from `q₂Full`.  The clip is `highG_clip_le`:
`∫_clip highG ≤ Ch (rowM2 + rowM3)`.  Everything here is proved.  One input stays outside: the
low-last vector `v`, with `‖v‖ ≤ K M_∞ ‖z‖`, is universally quantified in `row23_piece`.  It is
`A^{−1/2} 𝓛_lo z` of the last-edge node (NEW382), which will supply it.

## `H³` times
`hnorm 3` is `0` where the series diverges, so `tailB_le_of_split` needs `InH 3 y`: a real
hypothesis, and the source's: "On true almost-everywhere `H³` times" (Body 41).  `ae_inH3_corr`
supplies it, which is why the clip theorem below is a statement a.e. in time.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. From fields to sequences -/

/-- The modulus sequence of a field. -/
def nrm (u : Field) (k : Mode) : ℝ := ‖u k‖

/-- `‖z‖_{ℓ²}`, the norm of an energy vector. -/
def l2n (z : Field) : ℝ := Real.sqrt (∑' k, ‖z k‖ ^ 2)

lemma l2n_nonneg (z : Field) : 0 ≤ l2n z := Real.sqrt_nonneg _

lemma l2B_nrm {z : Field} (hz : Summable fun k => ‖z k‖ ^ 2) : L2B (nrm z) (l2n z) :=
  ⟨fun _ => norm_nonneg _, hz, le_rfl⟩

lemma l1B_nrm {S : Field} (hS : InH 2 S) : L1B (nrm S) (wiener S) :=
  ⟨fun _ => norm_nonneg _, summable_wiener hS, le_rfl⟩

/-- `|p|² ‖S_p‖` is `ℓ²` with norm `‖S‖₂`. -/
lemma l2B_up {S : Field} (hS : InH 2 S) : L2B (up (nrm S)) (hnorm 2 S) := by
  have e : ∀ k, up (nrm S) k ^ 2 = sobWeight 2 k * ‖S k‖ ^ 2 := fun k => by
    rw [sobWeight_two, up, nrm, mul_pow]
  refine ⟨fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _), ?_, ?_⟩
  · simp only [e]
    exact hS
  · simp only [e, hnorm]
    exact le_rfl

/-- `hiP` is a mode-wise truncation. -/
lemma norm_hiP_le (D : ℝ) (u : Field) (k : Mode) : ‖hiP D u k‖ ≤ ‖u k‖ := by
  unfold hiP
  split_ifs
  · exact le_rfl
  · simp

lemma hiP_of_lt {D : ℝ} (u : Field) {k : Mode} (h : D < absk k) : hiP D u k = u k := by
  simp [hiP, h]

lemma hiP_of_le {D : ℝ} (u : Field) {k : Mode} (h : ¬ D < absk k) : hiP D u k = 0 := by
  simp [hiP, h]

lemma inH_hiP {s D : ℝ} {u : Field} (hu : InH s u) : InH s (hiP D u) :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_hiP_le D u k) 2)
      (sobWeight_nonneg s k)) hu

lemma mz_hiP {s D : ℝ} {u : Field} (hu : MZ s u) : MZ s (hiP D u) := by
  refine ⟨inH_hiP hu.inH, ?_⟩
  unfold hiP
  split_ifs
  · exact hu.mean
  · rfl

lemma piS_hiP {D : ℝ} {u : Field} (hu : PiS u = u) : PiS (hiP D u) = hiP D u := by
  funext k
  by_cases hk : k 2 = 0
  · simp [PiS, hk]
  · have h0 : u k = 0 := by rw [← hu]; simp [PiS, hk]
    simp [PiS, hiP, hk, h0]

lemma tailB_nonneg (D : ℝ) (u : Field) : 0 ≤ tailB D u := hnorm_nonneg _ _

lemma tailW_nonneg (D : ℝ) (u : Field) : 0 ≤ tailW D u := tsum_nonneg fun _ => norm_nonneg _

/-- `b_> ≤ b`. -/
lemma tailB_le_hnorm {D : ℝ} {u : Field} (hu : InH 2 u) : tailB D u ≤ hnorm 2 u := by
  refine Real.sqrt_le_sqrt ?_
  refine Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_hiP_le D u k) 2) (sobWeight_nonneg 2 k)) ?_ hu
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg 2 k) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_hiP_le D u k) 2) (sobWeight_nonneg 2 k)) hu

/-- `W_> ≤ c₄ b_>`: the Wiener tail against the `H²` tail. -/
lemma tailW_le_c4 {D : ℝ} {u : Field} (hu : MZ 2 u) : tailW D u ≤ c4 * tailB D u :=
  wiener_le (mz_hiP hu)

/-- **The inverse-fourth tail** (LOCAL440 step 1: "the exact inverse fourth tail on the slow
lattice"): `W_> ≤ 5 D⁻¹ b`.  On `|p| > D`: `|p|⁻² ≤ 2 (D² + |p|²)⁻¹`, and T1
(`slow_lattice_sum_le`) has `∑ (D² + |p|²)⁻² ≤ 25/(4D² + 1)`.  The report's numerical constant is
`√π` at infinity, `1.80` at worst. -/
theorem tailW_le {D : ℝ} (hD : 0 < D) {S : Field} (hS : MZ 2 S) (hS' : PiS S = S) :
    tailW D S ≤ 5 / D * hnorm 2 S := by
  set ρ : Mode → ℝ := fun k => 2 * slowResW (D ^ 2) k with hρ
  have hρ0 : ∀ k, 0 ≤ ρ k := fun k => by
    have := slowResW_nonneg (sq_nonneg D) k
    simp only [hρ]
    positivity
  obtain ⟨hs2, hle2⟩ := slow_lattice_sum_le (sq_nonneg D)
  have hρ2 : Summable fun k => ρ k ^ 2 := by
    have := hs2.mul_left 4
    refine this.congr fun k => ?_
    simp only [hρ]
    ring
  have hρt : ∑' k, ρ k ^ 2 = 4 * ∑' k, slowResW (D ^ 2) k ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by simp only [hρ]; ring
  have hρs : Real.sqrt (∑' k, ρ k ^ 2) ≤ 5 / D := by
    rw [Real.sqrt_le_left (by positivity), hρt]
    have hD2 : 0 < D ^ 2 := by positivity
    have h1 : 25 / (4 * D ^ 2 + 1) ≤ 25 / (4 * D ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    calc 4 * ∑' k, slowResW (D ^ 2) k ^ 2 ≤ 4 * (25 / (4 * D ^ 2)) := by linarith
      _ = (5 / D) ^ 2 := by
          field_simp
          ring
  have hU := l2B_up (mz_hiP (D := D) hS).inH
  obtain ⟨hs3, hle3⟩ := cs_tsum_nonneg' hU.nn hρ0 hU.s hρ2
  have hpt : ∀ k, ‖hiP D S k‖ ≤ up (nrm (hiP D S)) k * ρ k := fun k => by
    by_cases hk : D < absk k
    · have hk0 : k ≠ 0 := fun h => by
        rw [h, show absk 0 = 0 from absk_eq_zero.2 rfl] at hk
        linarith
      by_cases h2 : k 2 = 0
      · have hA : 0 < absSq k := by linarith [one_le_absSq hk0]
        have hsq : D ^ 2 ≤ absSq k := by
          rw [← absk_sq k]
          exact pow_le_pow_left₀ hD.le hk.le 2
        simp only [up, nrm, hρ, slowResW_of_slow h2 hk0]
        have hpos : 0 < D ^ 2 + absSq k := by positivity
        have e : absSq k * ‖hiP D S k‖ * (2 * (D ^ 2 + absSq k)⁻¹) =
            ‖hiP D S k‖ * (2 * absSq k / (D ^ 2 + absSq k)) := by
          field_simp
        rw [e]
        have h1 : 1 ≤ 2 * absSq k / (D ^ 2 + absSq k) := by
          rw [one_le_div hpos]
          linarith
        exact le_mul_of_one_le_right (norm_nonneg _) h1
      · have h0 : S k = 0 := by rw [← hS']; simp [PiS, h2]
        simp [hiP_of_lt S hk, h0, up, nrm]
    · rw [hiP_of_le S hk, norm_zero]
      simp [up, nrm, hiP_of_le S hk]
  have hW : Summable fun k => ‖hiP D S k‖ := summable_wiener (mz_hiP hS).inH
  calc tailW D S = ∑' k, ‖hiP D S k‖ := rfl
    _ ≤ ∑' k, up (nrm (hiP D S)) k * ρ k := hW.tsum_le_tsum hpt hs3
    _ ≤ Real.sqrt (∑' k, up (nrm (hiP D S)) k ^ 2) * Real.sqrt (∑' k, ρ k ^ 2) := hle3
    _ ≤ hnorm 2 (hiP D S) * (5 / D) :=
        mul_le_mul hU.le hρs (Real.sqrt_nonneg _) (hnorm_nonneg _ _)
    _ ≤ hnorm 2 S * (5 / D) :=
        mul_le_mul_of_nonneg_right (tailB_le_hnorm hS.inH) (by positivity)
    _ = 5 / D * hnorm 2 S := mul_comm _ _

/-- `‖P_{>D} y‖₂ ≤ D⁻¹ ‖y‖₃`. -/
lemma tail_two_le {D : ℝ} (hD : 0 < D) {y : Field} (hy : InH 3 y) :
    hnorm 2 (hiP D y) ≤ hnorm 3 y / D := by
  have hpt : ∀ k, sobWeight 2 k * ‖hiP D y k‖ ^ 2 ≤
      (1 / D ^ 2) * (sobWeight 3 k * ‖y k‖ ^ 2) := fun k => by
    rw [sobWeight_two, H2.sobWeight_three]
    by_cases hk : D < absk k
    · rw [hiP_of_lt y hk]
      have hsq : D ^ 2 ≤ absSq k := by
        rw [← absk_sq k]
        exact pow_le_pow_left₀ hD.le hk.le 2
      have hA := absSq_nonneg k
      have hD2 : 0 < D ^ 2 := by positivity
      have h1 : absSq k ^ 2 ≤ 1 / D ^ 2 * absSq k ^ 3 := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hD2]
        nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (absSq k))]
      calc absSq k ^ 2 * ‖y k‖ ^ 2 ≤ 1 / D ^ 2 * absSq k ^ 3 * ‖y k‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = _ := by ring
    · rw [hiP_of_le y hk, norm_zero]
      have : 0 ≤ absSq k ^ 3 * ‖y k‖ ^ 2 := by
        have := absSq_nonneg k
        positivity
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
  have hs : Summable fun k => (1 / D ^ 2) * (sobWeight 3 k * ‖y k‖ ^ 2) := hy.mul_left _
  have hs2 : Summable fun k => sobWeight 2 k * ‖hiP D y k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg 2 k) (sq_nonneg _)) hpt hs
  have hle := hs2.tsum_le_tsum hpt hs
  rw [tsum_mul_left, ← hnorm_sq hy] at hle
  have h3 := hnorm_nonneg 3 y
  change Real.sqrt (∑' k, sobWeight 2 k * ‖hiP D y k‖ ^ 2) ≤ hnorm 3 y / D
  rw [Real.sqrt_le_left (by positivity), div_pow]
  rwa [mul_comm, ← div_eq_mul_one_div] at hle

/-- **The weighted tail** (LOCAL440 step 1, LOCAL441): `b_> ≤ D⁻¹ ‖y‖₃ + ‖R‖₂` for `y = S + R` at an
`H³` time of `y`.  With `y = y_S`, `R = R_S`: "`S = y_S − R_S`"; it "uses only the independently
paid `H²` trace of `R_S` and corrected slow `H³`". -/
theorem tailB_le_of_split {D : ℝ} (hD : 0 < D) {S y R : Field} (hy : InH 3 y) (hR : InH 2 R)
    (e : y = S + R) : tailB D S ≤ hnorm 3 y / D + hnorm 2 R := by
  have hmod : ∀ k, S k = y k - R k := fun k => by rw [e]; simp
  have e1 : hiP D S = hiP D y - hiP D R := by
    funext k
    by_cases hk : D < absk k
    · simp only [Pi.sub_apply, hiP_of_lt _ hk, hmod k]
    · simp only [Pi.sub_apply, hiP_of_le _ hk, sub_zero]
  have hy2 : InH 2 y := hy.mono (by norm_num)
  have h1 := hnorm_sub_le (inH_hiP (D := D) hy2) (inH_hiP (D := D) hR)
  have h2 : hnorm 2 (hiP D R) ≤ hnorm 2 R := tailB_le_hnorm hR
  have h3 := tail_two_le hD hy
  rw [← e1] at h1
  exact h1.trans (add_le_add h3 h2)

/-! ### B. Vanishing leaves -/

lemma blk_zero_leaf (m : Mult) (p k j : Mode) : blk m p k j 0 = 0 := by
  ext1 w
  simp [blk_apply, hel_zero_right, vert_zero_left]

private lemma conjV_zero' : conjV 0 = 0 := by
  ext i
  simp [conjV]

lemma Lb_zero_leaf (s : ℕ) (τ : ℝ) (p k j : Mode) : Lb s τ p k j 0 = 0 := by
  ext1 w
  simp only [Lb, blk_zero_leaf, smul_apply, zero_apply, smul_zero]

lemma Lad_zero_leaf (s : ℕ) (τ : ℝ) (p k j : Mode) : Lad s τ p k j 0 = 0 := by
  rw [Lad, conjV_zero', Lb_zero_leaf, map_zero]

lemma X1b_zero_leaf (s : ℕ) (r τ : ℝ) (p k j : Mode) : X1b s r τ p k j 0 = 0 := by
  have e : ∀ c : ℂ, c • (0 : V3 →L[ℂ] V3) = 0 := fun c => by
    ext1 w
    simp only [smul_apply, zero_apply, smul_zero]
  rw [X1b, conjV_zero', blk_zero_leaf, blk_zero_leaf, e, e, map_zero, add_zero]

lemma outerInv_zero (r H : ℝ) (l j : Mode) : outerInv r H l j 0 = 0 := by
  ext1 w
  simp [outerInv, smul_apply]

lemma X2b_eq_zero {s : ℕ} {r τ : ℝ} {f g : Field} {l a b : Mode} (h : f a = 0 ∨ g b = 0) :
    X2b s r τ f g l a b = 0 := by
  have ht : twoRoot s r τ f g l a b = 0 := by
    rcases h with h | h <;> simp [twoRoot, h, Lb_zero_leaf, Lad_zero_leaf, X1b_zero_leaf]
  rw [X2b, ht, outerInv_zero]

lemma slowV_eq_zero {a b : Mode} {v w : V3} (h : v = 0 ∨ w = 0) : slowV a b v w = 0 := by
  rcases h with rfl | rfl
  · simp [slowV, blk_zero_leaf]
  · simp [slowV]

lemma Zb_eq_zero {s : ℕ} {r τ : ℝ} {f g : Field} {l a b : Mode} (h : f a = 0 ∨ g b = 0) :
    Zb s r τ f g l a b = 0 := by
  rw [Zb, slowV_eq_zero h, X1b_zero_leaf, outerInv_zero]

lemma YLb_eq_zero {s : ℕ} {r τ : ℝ} {f g h : Field} {x : I4}
    (hx : f x.2.1 = 0 ∨ g x.2.2.1 = 0 ∨ h x.2.2.2 = 0) : YLb s r τ f g h x = 0 := by
  rcases hx with hx | hx | hx
  · simp [YLb, X2b_eq_zero (Or.inl hx), Zb_eq_zero (Or.inl hx)]
  · simp [YLb, X2b_eq_zero (Or.inr hx), Zb_eq_zero (Or.inr hx)]
  · simp [YLb, hx, Lb_zero_leaf]

/-! ### C. The summands -/

lemma form_le {ι : Type*} {T : ι → ℂ} {Ψ : ι → ℝ} {B : ℝ} (hb : SB Ψ B) (h : ∀ x, ‖T x‖ ≤ Ψ x) :
    Summable T ∧ ‖∑' x, T x‖ ≤ B :=
  ⟨Summable.of_norm_bounded hb.1 h, (tsum_of_norm_bounded hb.1.hasSum h).trans hb.2⟩

lemma norm_inner_apply_le (G w : V3) (T : V3 →L[ℂ] V3) :
    ‖inner ℂ G (T w)‖ ≤ ‖G‖ * ‖w‖ * ‖T‖ := by
  refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
  have := T.le_opNorm w
  calc ‖G‖ * ‖T w‖ ≤ ‖G‖ * (‖T‖ * ‖w‖) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := by ring

/-- The summand of the cubic form, against the kernel of `norm_YLb_le`. -/
lemma norm_YL_summand_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {f g h G F : Field} (hf : PiS f = f)
    (hg : PiS g = g) (hh : PiS h = h) (hF : PiF F = F) (μ : ℂ) (x : I4) :
    ‖μ * inner ℂ (G x.1) (YLb 2 r τ f g h x (F (inJ x)))‖ ≤
      2 ^ 21 / |r| * (‖μ‖ * (‖G x.1‖ * ‖F (inJ x)‖ * (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖)) *
        E3 x) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hE := E3_nonneg x
  have hR : 0 ≤ 2 ^ 21 / |r| * (‖μ‖ * (‖G x.1‖ * ‖F (inJ x)‖ *
      (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖)) * E3 x) := by positivity
  have hzero : ∀ (hb0 : YLb 2 r τ f g h x = 0), ‖μ * inner ℂ (G x.1)
      (YLb 2 r τ f g h x (F (inJ x)))‖ ≤ 2 ^ 21 / |r| * (‖μ‖ * (‖G x.1‖ * ‖F (inJ x)‖ *
        (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖)) * E3 x) := fun hb0 => by
    simpa [hb0] using hR
  by_cases ha : x.2.1 2 = 0
  swap
  · exact hzero (YLb_eq_zero (Or.inl (slow_zero hf ha)))
  by_cases hb : x.2.2.1 2 = 0
  swap
  · exact hzero (YLb_eq_zero (Or.inr (Or.inl (slow_zero hg hb))))
  by_cases hc : x.2.2.2 2 = 0
  swap
  · exact hzero (YLb_eq_zero (Or.inr (Or.inr (slow_zero hh hc))))
  by_cases hj : inJ x 2 = 0
  · have : F (inJ x) = 0 := fast_zero hF hj
    simp [this]
  have hK := norm_YLb_le hr τ f g h ha hb hc hj
  rw [norm_mul]
  calc ‖μ‖ * ‖inner ℂ (G x.1) (YLb 2 r τ f g h x (F (inJ x)))‖
      ≤ ‖μ‖ * (‖G x.1‖ * ‖F (inJ x)‖ * ‖YLb 2 r τ f g h x‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_apply_le _ _ _) (norm_nonneg _)
    _ ≤ ‖μ‖ * (‖G x.1‖ * ‖F (inJ x)‖ * (2 ^ 21 / |r| *
        (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) * E3 x)) := by gcongr
    _ = _ := by ring

/-- The union bound of the mask: one restricted leaf per slot, overlaps included ("split its index
among the three actual slots", LOCAL440 step 1). -/
lemma mask₃_le (D : ℝ) (S : Field) (x : I4) :
    ‖hiMask₃ D x‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖) ≤
      ‖hiP D S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖ + ‖S x.2.1‖ * ‖hiP D S x.2.2.1‖ * ‖S x.2.2.2‖ +
        ‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖hiP D S x.2.2.2‖ := by
  have h1 : 0 ≤ ‖hiP D S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖ := by positivity
  have h2 : 0 ≤ ‖S x.2.1‖ * ‖hiP D S x.2.2.1‖ * ‖S x.2.2.2‖ := by positivity
  have h3 : 0 ≤ ‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖hiP D S x.2.2.2‖ := by positivity
  unfold hiMask₃
  split_ifs with h
  · rw [norm_one, one_mul]
    rcases h with h | h | h
    · rw [hiP_of_lt S h] at h1 ⊢
      linarith
    · rw [hiP_of_lt S h] at h2 ⊢
      linarith
    · rw [hiP_of_lt S h] at h3 ⊢
      linarith
  · simp only [norm_zero, zero_mul]
    linarith

/-- The arithmetic of the three-leaf classes with one restricted leaf. -/
lemma cls3_tail {W b W' b' : ℝ} (hW : 0 ≤ W) (hb : 0 ≤ b) (hW' : 0 ≤ W') (hb' : 0 ≤ b')
    (h : W ≤ c4 * b) :
    cls3 W' W W b' b b ≤ 6 * c4 ^ 2 * (W' * b ^ 2) + 4 * c4 ^ 2 * (W * b * b') := by
  have hc := c4_pos
  have h1 : W * W ≤ c4 * b * (c4 * b) := mul_le_mul h h hW (by positivity)
  have h2 : W' * (W * W) ≤ W' * (c4 * b * (c4 * b)) := mul_le_mul_of_nonneg_left h1 hW'
  have h3 : 2 * c4 * (b' * W * W) ≤ 2 * c4 * (b' * W * (c4 * b)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by positivity)) (by positivity)
  have h4 : 4 * c4 * (W' * b * W) ≤ 4 * c4 * (W' * b * (c4 * b)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by positivity)) (by positivity)
  simp only [cls3]
  nlinarith only [h2, h3, h4]

/-- The constant of the undifferentiated high ancestors. -/
def Cm3 : ℝ := 2 ^ 21 * 18 * c4 ^ 2

lemma Cm3_pos : 0 < Cm3 := by
  have := c4_pos
  unfold Cm3
  positivity

/-- **Rows 2, 3, undifferentiated** (LOCAL440 step 1, LOCAL441; NEW378's `E₂^z` with one restricted
leaf): at each time, for every multiplier of modulus at most one on the sector "at least one
ancestor at `|p| > D`", `|⟨G, μ (X₂ + Z) 𝓛 F⟩| ≤ (C/q) (W_> b² + W b b_>) ‖G‖ ‖F‖`.  With
`G = F = z` this is the mass of the source; the literal adjoints are the conjugate form. -/
theorem YLForm_high_le {r : ℝ} (hr : r ≠ 0) (τ D : ℝ) {S G F : Field} (hS : MZ 2 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) {μ : I4 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ ‖hiMask₃ D x‖) :
    ‖YLForm μ 2 r τ S S S G F‖ ≤ Cm3 / |r| *
      (tailW D S * hnorm 2 S ^ 2 + wiener S * hnorm 2 S * tailB D S) * (l2n G * l2n F) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hc := c4_pos
  set b := hnorm 2 S with hb
  set W := wiener S with hWd
  set W' := tailW D S with hW'd
  set b' := tailB D S with hb'd
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have hb'0 : 0 ≤ b' := tailB_nonneg _ _
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => norm_nonneg _
  have hW'0 : 0 ≤ W' := tailW_nonneg _ _
  have hWb : W ≤ c4 * b := wiener_le hS
  have ha := l2B_nrm hG
  have hβ := l2B_nrm hF
  have W1 : L1B (nrm S) W := l1B_nrm hS.inH
  have U1 : L2B (up (nrm S)) b := l2B_up hS.inH
  have W2 : L1B (nrm (hiP D S)) W' := l1B_nrm (inH_hiP hS.inH)
  have U2 : L2B (up (nrm (hiP D S))) b' := l2B_up (inH_hiP hS.inH)
  have p1 := pos3_E3 ha hβ W2 W1 W1 U2 U1 U1
  have p2 := pos3_E3 ha hβ W1 W2 W1 U1 U2 U1
  have p3 := pos3_E3 ha hβ W1 W1 W2 U1 U1 U2
  have hK : (0 : ℝ) ≤ 2 ^ 21 / |r| := by positivity
  have hΨ := ((p1.add p2).add p3).const_mul hK
  have hpt : ∀ x : I4, ‖μ x * inner ℂ (G x.1) (YLb 2 r τ S S S x (F (inJ x)))‖ ≤
      2 ^ 21 / |r| * (Phi₃ (nrm G) (nrm F) (nrm (hiP D S)) (nrm S) (nrm S) x * E3 x +
        Phi₃ (nrm G) (nrm F) (nrm S) (nrm (hiP D S)) (nrm S) x * E3 x +
        Phi₃ (nrm G) (nrm F) (nrm S) (nrm S) (nrm (hiP D S)) x * E3 x) := fun x => by
    refine (norm_YL_summand_le hr τ hS' hS' hS' hF' (μ x) x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK
    have hE := E3_nonneg x
    have h1 : ‖μ x‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖) ≤
        ‖hiMask₃ D x‖ * (‖S x.2.1‖ * ‖S x.2.2.1‖ * ‖S x.2.2.2‖) :=
      mul_le_mul_of_nonneg_right (hμ x) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left (h1.trans (mask₃_le D S x))
      (by positivity : 0 ≤ ‖G x.1‖ * ‖F (inJ x)‖ * E3 x)
    simp only [Phi₃, nrm]
    nlinarith only [h2]
  obtain ⟨-, hle⟩ := form_le hΨ hpt
  refine hle.trans ?_
  have c1 := cls3_tail hW0 hb0 hW'0 hb'0 hWb
  have e2 : cls3 W W' W b b' b = cls3 W' W W b' b b := by simp only [cls3]; ring
  have e3 : cls3 W W W' b b b' = cls3 W' W W b' b b := by simp only [cls3]; ring
  have hL := mul_nonneg (l2n_nonneg G) (l2n_nonneg F)
  have hT1 : 0 ≤ c4 ^ 2 * (W' * b ^ 2) := by positivity
  have hT2 : 0 ≤ c4 ^ 2 * (W * b * b') := by positivity
  have htot : l2n G * l2n F * cls3 W' W W b' b b + l2n G * l2n F * cls3 W W' W b b' b +
      l2n G * l2n F * cls3 W W W' b b b' ≤
      l2n G * l2n F * (18 * c4 ^ 2 * (W' * b ^ 2 + W * b * b')) := by
    rw [e2, e3]
    have := mul_le_mul_of_nonneg_left c1 hL
    nlinarith only [this, mul_nonneg hL hT1, mul_nonneg hL hT2]
  calc 2 ^ 21 / |r| * (l2n G * l2n F * cls3 W' W W b' b b + l2n G * l2n F * cls3 W W' W b b' b +
        l2n G * l2n F * cls3 W W W' b b b')
      ≤ 2 ^ 21 / |r| * (l2n G * l2n F * (18 * c4 ^ 2 * (W' * b ^ 2 + W * b * b'))) :=
        mul_le_mul_of_nonneg_left htot hK
    _ = _ := by
        simp only [Cm3]
        ring

/-! ### D. The two-leaf companions -/

/-- The summand of an `X₂` form, against a block bound on the actual support. -/
lemma norm_X2_summand_le {r τ : ℝ} {f g G F : Field} (hf : PiS f = f) (hg : PiS g = g)
    (hF : PiF F = F) {B : I3 → ℝ} (hB0 : ∀ x, 0 ≤ B x)
    (hB : ∀ x : I3, x.2.1 2 = 0 → x.2.2 2 = 0 → inJ₂ x 2 ≠ 0 →
      ‖X2b 2 r τ f g x.1 x.2.1 x.2.2‖ ≤ B x) (c : ℂ) (x : I3) :
    ‖c * inner ℂ (G x.1) (X2b 2 r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))‖ ≤
      ‖c‖ * (‖G x.1‖ * ‖F (inJ₂ x)‖ * B x) := by
  have hR : 0 ≤ ‖c‖ * (‖G x.1‖ * ‖F (inJ₂ x)‖ * B x) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (by positivity) (hB0 x))
  have hzero : ∀ (hb0 : X2b 2 r τ f g x.1 x.2.1 x.2.2 = 0),
      ‖c * inner ℂ (G x.1) (X2b 2 r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))‖ ≤
        ‖c‖ * (‖G x.1‖ * ‖F (inJ₂ x)‖ * B x) := fun hb0 => by
    simpa [hb0] using hR
  by_cases ha : x.2.1 2 = 0
  swap
  · exact hzero (X2b_eq_zero (Or.inl (slow_zero hf ha)))
  by_cases hb : x.2.2 2 = 0
  swap
  · exact hzero (X2b_eq_zero (Or.inr (slow_zero hg hb)))
  by_cases hj : inJ₂ x 2 = 0
  · have : F (inJ₂ x) = 0 := fast_zero hF hj
    have h0 : F (x.1 - x.2.1 - x.2.2) = 0 := this
    simpa [h0, map_zero] using hR
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_inner_apply_le _ _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (hB x ha hb hj) (by positivity)

/-- The union bound of the two-leaf mask. -/
lemma mask₂_le (D : ℝ) (S : Field) (x : I3) :
    ‖hiMask₂ D x‖ * (‖S x.2.1‖ * ‖S x.2.2‖) ≤
      ‖hiP D S x.2.1‖ * ‖S x.2.2‖ + ‖S x.2.1‖ * ‖hiP D S x.2.2‖ := by
  have h1 : 0 ≤ ‖hiP D S x.2.1‖ * ‖S x.2.2‖ := by positivity
  have h2 : 0 ≤ ‖S x.2.1‖ * ‖hiP D S x.2.2‖ := by positivity
  unfold hiMask₂
  split_ifs with h
  · rw [norm_one, one_mul]
    rcases h with h | h
    · rw [hiP_of_lt S h] at h1 ⊢
      linarith
    · rw [hiP_of_lt S h] at h2 ⊢
      linarith
  · simp only [norm_zero, zero_mul]
    linarith

/-- The arithmetic of the two-leaf classes with one restricted leaf. -/
lemma cls2_tail {W b W' b' : ℝ} (hW0 : 0 ≤ W) (hb : 0 ≤ b) (hb' : 0 ≤ b') (hW : W ≤ c4 * b)
    (h' : W' ≤ c4 * b') : cls2 W' W b' b ≤ 6 * c4 ^ 2 * (b * b') := by
  have hc := c4_pos
  have h1 : W' * W ≤ c4 * b' * (c4 * b) := mul_le_mul h' hW hW0 (by positivity)
  have h2 : 2 * c4 * (b' * W) ≤ 2 * c4 * (b' * (c4 * b)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW hb') (by positivity)
  have h3 : 2 * c4 * (W' * b) ≤ 2 * c4 * (c4 * b' * b) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h' hb) (by positivity)
  simp only [cls2]
  nlinarith only [h1, h2, h3]

/-- The constant of the two-leaf companions. -/
def Cm2 : ℝ := 2 * 39424 * 12 * c4 ^ 2

lemma Cm2_pos : 0 < Cm2 := by
  have := c4_pos
  unfold Cm2
  positivity

/-- **The output half of the high ancestor** (Body 41, LOCAL655:
"`‖A^{1/2}X_{2,hi}‖ ≤ C q⁻¹ b b_>`", LOCAL577's output-half price `1758`, up to the constant):
`|⟨G, A^{1/2} μ X₂ F⟩| ≤ (C/q) b b_> ‖G‖ ‖F‖` for every multiplier of modulus at most one on "at
least one ancestor at `|p| > D`". -/
theorem X2Half_high_le {r : ℝ} (hr : r ≠ 0) (τ D : ℝ) {S G F : Field} (hS : MZ 2 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ ‖hiMask₂ D x‖) :
    ‖X2HalfForm μ 2 r τ S S G F‖ ≤ Cm2 / |r| * (hnorm 2 S * tailB D S) * (l2n G * l2n F) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hc := c4_pos
  set b := hnorm 2 S with hb
  set W := wiener S with hWd
  set W' := tailW D S with hW'd
  set b' := tailB D S with hb'd
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have hb'0 : 0 ≤ b' := tailB_nonneg _ _
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => norm_nonneg _
  have hW'0 : 0 ≤ W' := tailW_nonneg _ _
  have hWb : W ≤ c4 * b := wiener_le hS
  have hWb' : W' ≤ c4 * b' := tailW_le_c4 hS
  have ha := l2B_nrm hG
  have hβ := l2B_nrm hF
  have W1 : L1B (nrm S) W := l1B_nrm hS.inH
  have U1 : L2B (up (nrm S)) b := l2B_up hS.inH
  have W2 : L1B (nrm (hiP D S)) W' := l1B_nrm (inH_hiP hS.inH)
  have U2 : L2B (up (nrm (hiP D S))) b' := l2B_up (inH_hiP hS.inH)
  have p1 := pos2_E2 ha hβ W2 W1 U2 U1
  have p2 := pos2_E2 ha hβ W1 W2 U1 U2
  have hK : (0 : ℝ) ≤ 2 * 39424 / |r| := by positivity
  have hΨ := (p1.add p2).const_mul hK
  have hB0 : ∀ x : I3, 0 ≤ 39424 / |r| * (absk (x.1 - x.2.1) /
      heat4 x.1 (x.1 - x.2.1 - x.2.2) x.2.1 x.2.2) * (‖S x.2.1‖ * ‖S x.2.2‖) * E2 x := fun x => by
    have h1 : 0 ≤ heat4 x.1 (x.1 - x.2.1 - x.2.2) x.2.1 x.2.2 := by
      have := absSq_nonneg x.1
      have := absSq_nonneg x.2.1
      have := absSq_nonneg x.2.2
      have := absSq_nonneg (x.1 - x.2.1 - x.2.2)
      unfold heat4
      linarith
    have := E2_nonneg x
    have := absk_nonneg (x.1 - x.2.1)
    positivity
  have hpt : ∀ x : I3, ‖μ x * ((absk x.1 : ℝ) : ℂ) * inner ℂ (G x.1)
      (X2b 2 r τ S S x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))‖ ≤
      2 * 39424 / |r| * (Phi₂ (nrm G) (nrm F) (nrm (hiP D S)) (nrm S) x * E2 x +
        Phi₂ (nrm G) (nrm F) (nrm S) (nrm (hiP D S)) x * E2 x) := fun x => by
    refine (norm_X2_summand_le hS' hS' hF' hB0 (fun x ha hb hj => ?_) _ x).trans ?_
    · have h1 := norm_X2b_E2_le hr τ S S (l := x.1) ha hb hj
      refine h1.trans (le_of_eq ?_)
      ring
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (absk_nonneg _)]
      have hE := E2_nonneg x
      have hR := half_ratio_le x.1 x.2.1 x.2.2
      set R := absk x.1 * (absk (x.1 - x.2.1) / heat4 x.1 (x.1 - x.2.1 - x.2.2) x.2.1 x.2.2)
        with hRd
      have hR0 : 0 ≤ R := by
        have h1 := hB0 x
        have h2 : 0 ≤ heat4 x.1 (x.1 - x.2.1 - x.2.2) x.2.1 x.2.2 := by
          have := absSq_nonneg x.1
          have := absSq_nonneg x.2.1
          have := absSq_nonneg x.2.2
          have := absSq_nonneg (x.1 - x.2.1 - x.2.2)
          unfold heat4
          linarith
        have := absk_nonneg x.1
        have := absk_nonneg (x.1 - x.2.1)
        positivity
      have h1 : ‖μ x‖ * (‖S x.2.1‖ * ‖S x.2.2‖) ≤
          ‖hiP D S x.2.1‖ * ‖S x.2.2‖ + ‖S x.2.1‖ * ‖hiP D S x.2.2‖ :=
        (mul_le_mul_of_nonneg_right (hμ x) (by positivity)).trans (mask₂_le D S x)
      have hY : 0 ≤ ‖μ x‖ * (‖S x.2.1‖ * ‖S x.2.2‖) := by positivity
      have h2 : R * (‖μ x‖ * (‖S x.2.1‖ * ‖S x.2.2‖)) ≤
          2 * (‖hiP D S x.2.1‖ * ‖S x.2.2‖ + ‖S x.2.1‖ * ‖hiP D S x.2.2‖) :=
        mul_le_mul hR h1 hY (by norm_num)
      have h3 := mul_le_mul_of_nonneg_left h2
        (by positivity : 0 ≤ 39424 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * E2 x))
      simp only [Phi₂, nrm]
      rw [hRd] at h3
      calc _ = 39424 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * E2 x) * (absk x.1 * (absk (x.1 - x.2.1) /
            heat4 x.1 (x.1 - x.2.1 - x.2.2) x.2.1 x.2.2) *
              (‖μ x‖ * (‖S x.2.1‖ * ‖S x.2.2‖))) := by ring
        _ ≤ _ := h3
        _ = _ := by ring
  obtain ⟨-, hle⟩ := form_le hΨ hpt
  refine hle.trans ?_
  have c1 := cls2_tail hW0 hb0 hb'0 hWb hWb'
  have e2 : cls2 W W' b b' = cls2 W' W b' b := by simp only [cls2]; ring
  have hL := mul_nonneg (l2n_nonneg G) (l2n_nonneg F)
  have htot : l2n G * l2n F * cls2 W' W b' b + l2n G * l2n F * cls2 W W' b b' ≤
      l2n G * l2n F * (12 * c4 ^ 2 * (b * b')) := by
    rw [e2]
    have := mul_le_mul_of_nonneg_left c1 hL
    nlinarith only [this]
  calc 2 * 39424 / |r| * (l2n G * l2n F * cls2 W' W b' b + l2n G * l2n F * cls2 W W' b b')
      ≤ 2 * 39424 / |r| * (l2n G * l2n F * (12 * c4 ^ 2 * (b * b'))) :=
        mul_le_mul_of_nonneg_left htot hK
    _ = _ := by
        simp only [Cm2]
        ring

/-- The gradient sequence `|a| ‖h_a‖`. -/
def gr (h : Field) (a : Mode) : ℝ := absk a * ‖h a‖

/-- The sequence `‖h_a‖/|a|` of a genuine `H¹` direction (LOCAL577: "the adjusted slow direction
sequence `|h|/R` has the same class estimates as `f` with `B` replaced by `‖h‖₁`"). -/
def dv (h : Field) : Mode → ℝ := in2 (gr h)

lemma l2B_gr {h : Field} (hh : InH 1 h) : L2B (gr h) (hnorm 1 h) := by
  have e : ∀ k, gr h k ^ 2 = sobWeight 1 k * ‖h k‖ ^ 2 := fun k => by
    rw [sobWeight_one, gr, mul_pow, absk_sq]
  refine ⟨fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _), ?_, ?_⟩
  · simp only [e]
    exact hh
  · simp only [e, hnorm]
    exact le_rfl

lemma dv_nonneg (h : Field) (a : Mode) : 0 ≤ dv h a :=
  div_nonneg (mul_nonneg (absk_nonneg a) (norm_nonneg _)) (absSq_nonneg a)

lemma dv_apply (h : Field) (a : Mode) : dv h a = ‖h a‖ / absk a := by
  by_cases ha : a = 0
  · subst ha
    simp [dv, in2, gr, absSq, absk]
  · have h1 : absk a ≠ 0 := absk_eq_zero.not.2 ha
    simp only [dv, in2, gr, ← absk_sq]
    field_simp

lemma up_dv (h : Field) : up (dv h) = gr h := by
  funext a
  by_cases ha : a = 0
  · subst ha
    simp [up, gr, absSq, absk]
  · have h1 : absSq a ≠ 0 := by linarith [one_le_absSq ha]
    simp only [up, dv, in2]
    field_simp

/-- `X₂` with the genuine direction in the first slot (Body 12 §7: "`M/(Σ H) ≤ 1/R`"; here without
the extra exterior derivative): the replaced leaf is `‖h_a‖/|a|`. -/
theorem norm_X2b_left_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {h S : Field} (hh0 : h 0 = 0) {l a b : Mode}
    (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖X2b 2 r τ h S l a b‖ ≤ 39424 / |r| * (dv h a * ‖S b‖) * E2 (l, a, b) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hE := E2_nonneg (l, a, b)
  have hd := dv_nonneg h a
  by_cases ha0 : a = 0
  · rw [X2b_eq_zero (Or.inl (by rw [ha0, hh0])), norm_zero]
    positivity
  have hP : 0 < absk a := lt_of_lt_of_le one_pos (one_le_absk ha0)
  obtain ⟨-, -, hj0⟩ := fast_labels ha hb hj
  have hR := leaf_ratio_left_le (l := l) (a := a) (b := b) hj0
  refine (norm_X2b_E2_le hr τ h S ha hb hj).trans ?_
  set R := absk (l - a) / heat4 l (l - a - b) a b with hRd
  have h1 : R * ‖h a‖ ≤ dv h a := by
    rw [dv_apply, le_div_iff₀ hP]
    calc R * ‖h a‖ * absk a = (absk a * R) * ‖h a‖ := by ring
      _ ≤ 1 * ‖h a‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)
      _ = ‖h a‖ := one_mul _
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 39424 / |r| * ‖S b‖ * E2 (l, a, b))
  calc 39424 / |r| * R * (‖h a‖ * ‖S b‖) * E2 (l, a, b)
      = 39424 / |r| * ‖S b‖ * E2 (l, a, b) * (R * ‖h a‖) := by ring
    _ ≤ 39424 / |r| * ‖S b‖ * E2 (l, a, b) * dv h a := h2
    _ = _ := by ring

/-- `X₂` with the genuine direction in the second slot. -/
theorem norm_X2b_right_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {h S : Field} (hh0 : h 0 = 0) {l a b : Mode}
    (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖X2b 2 r τ S h l a b‖ ≤ 39424 / |r| * (‖S a‖ * dv h b) * E2 (l, a, b) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hE := E2_nonneg (l, a, b)
  have hd := dv_nonneg h b
  by_cases hb0 : b = 0
  · rw [X2b_eq_zero (Or.inr (by rw [hb0, hh0])), norm_zero]
    positivity
  have hP : 0 < absk b := lt_of_lt_of_le one_pos (one_le_absk hb0)
  obtain ⟨-, -, hj0⟩ := fast_labels ha hb hj
  have hR := leaf_ratio_right_le (l := l) (a := a) (b := b) hj0
  refine (norm_X2b_E2_le hr τ S h ha hb hj).trans ?_
  set R := absk (l - a) / heat4 l (l - a - b) a b with hRd
  have h1 : R * ‖h b‖ ≤ dv h b := by
    rw [dv_apply, le_div_iff₀ hP]
    calc R * ‖h b‖ * absk b = (absk b * R) * ‖h b‖ := by ring
      _ ≤ 1 * ‖h b‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)
      _ = ‖h b‖ := one_mul _
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 39424 / |r| * ‖S a‖ * E2 (l, a, b))
  calc 39424 / |r| * R * (‖S a‖ * ‖h b‖) * E2 (l, a, b)
      = 39424 / |r| * ‖S a‖ * E2 (l, a, b) * (R * ‖h b‖) := by ring
    _ ≤ 39424 / |r| * ‖S a‖ * E2 (l, a, b) * dv h b := h2
    _ = _ := by ring

/-- On the high-intermediate sector both leaves are long (Body 33: "If `M > D` in the
high-intermediate sector, both old slow lengths exceed `D/2`"; in fact `3D/4`). -/
lemma hiInt_leaves {D : ℝ} (hD : 0 ≤ D) {x : I3} (hx : hiIntMask D x ≠ 0) :
    D / 2 < absk x.2.1 ∧ D / 2 < absk x.2.2 := by
  by_contra hcon
  apply hx
  unfold hiIntMask
  refine ite_eq_right fun ⟨h1, h2, h3⟩ => hcon ?_
  have t1 := absk_sub_le x.1 x.2.1
  have t2 := absk_add_le (x.1 - x.2.1 - x.2.2) x.2.2
  rw [sub_add_cancel] at t2
  constructor <;> linarith

lemma mask_int_le {D : ℝ} (hD : 0 ≤ D) {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ ‖hiIntMask D x‖)
    (S : Field) (x : I3) :
    ‖μ x‖ * ‖S x.2.1‖ ≤ ‖hiP (D / 2) S x.2.1‖ ∧ ‖μ x‖ * ‖S x.2.2‖ ≤ ‖hiP (D / 2) S x.2.2‖ := by
  by_cases hx : hiIntMask D x = 0
  · have h0 : ‖μ x‖ = 0 := le_antisymm (by simpa [hx] using hμ x) (norm_nonneg _)
    simp [h0]
  have hle : ‖μ x‖ ≤ 1 := by
    refine (hμ x).trans ?_
    unfold hiIntMask
    split_ifs <;> simp
  obtain ⟨h1, h2⟩ := hiInt_leaves hD hx
  rw [hiP_of_lt S h1, hiP_of_lt S h2]
  exact ⟨mul_le_of_le_one_left (norm_nonneg _) hle, mul_le_of_le_one_left (norm_nonneg _) hle⟩

/-- **The differentiated companion** (Bodies 33, 42: "`C q⁻¹ ‖h‖_{H¹} b_>`", the "complete old
`q⁻¹ f₁ b_{>cD}` form"; LOCAL577's derivative price): on the high-intermediate sector, for every
multiplier of modulus at most one, `|⟨G, μ D_S X₂[h] F⟩| ≤ (C/q) ‖h‖₁ b_{>D/2} ‖G‖ ‖F‖`, with both
slots of `X₂` and both rootings.  The restricted leaf is the unreplaced one, `S`, not `h`: no `H²`
norm of `h` is used. -/
theorem DSX2_high_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 0 ≤ D) {h S G F : Field}
    (hh : MZ 1 h) (hh' : PiS h = h) (hS : MZ 2 S) (hS' : PiS S = S)
    (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F)
    {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ ‖hiIntMask D x‖) :
    ‖DSX2Form μ 2 r τ h S G F‖ ≤
      Cm2 / |r| * (hnorm 1 h * tailB (D / 2) S) * (l2n G * l2n F) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hc := c4_pos
  set f₁ := hnorm 1 h with hf₁
  set W' := tailW (D / 2) S with hW'd
  set b' := tailB (D / 2) S with hb'd
  have hf0 : 0 ≤ f₁ := hnorm_nonneg _ _
  have hb'0 : 0 ≤ b' := tailB_nonneg _ _
  have hW'0 : 0 ≤ W' := tailW_nonneg _ _
  have hWb' : W' ≤ c4 * b' := tailW_le_c4 hS
  have ha := l2B_nrm hG
  have hβ := l2B_nrm hF
  have hg := l2B_gr hh.inH
  have W1 : L1B (dv h) (c4 * f₁) := hg.in2
  have U1 : L2B (up (dv h)) f₁ := by rw [up_dv]; exact hg
  have W2 : L1B (nrm (hiP (D / 2) S)) W' := l1B_nrm (inH_hiP hS.inH)
  have U2 : L2B (up (nrm (hiP (D / 2) S))) b' := l2B_up (inH_hiP hS.inH)
  have hK : (0 : ℝ) ≤ 39424 / |r| := by positivity
  have p1 := (pos2_E2 ha hβ W1 W2 U1 U2).const_mul hK
  have p2 := (pos2_E2 ha hβ W2 W1 U2 U1).const_mul hK
  have hB1 : ∀ x : I3, 0 ≤ 39424 / |r| * (dv h x.2.1 * ‖S x.2.2‖) * E2 x := fun x => by
    have := E2_nonneg x
    have := dv_nonneg h x.2.1
    positivity
  have hB2 : ∀ x : I3, 0 ≤ 39424 / |r| * (‖S x.2.1‖ * dv h x.2.2) * E2 x := fun x => by
    have := E2_nonneg x
    have := dv_nonneg h x.2.2
    positivity
  have hpt1 : ∀ x : I3, ‖μ x * inner ℂ (G x.1)
      (X2b 2 r τ h S x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))‖ ≤
      39424 / |r| * (Phi₂ (nrm G) (nrm F) (dv h) (nrm (hiP (D / 2) S)) x * E2 x) := fun x => by
    refine (norm_X2_summand_le hh' hS' hF' hB1
      (fun x ha hb hj => norm_X2b_left_le hr τ hh.mean ha hb hj) _ x).trans ?_
    have h1 := (mask_int_le hD hμ S x).2
    have hE := E2_nonneg x
    have hd := dv_nonneg h x.2.1
    have h2 := mul_le_mul_of_nonneg_left h1
      (by positivity : 0 ≤ 39424 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * dv h x.2.1 * E2 x))
    simp only [Phi₂, nrm]
    calc _ = 39424 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * dv h x.2.1 * E2 x) *
          (‖μ x‖ * ‖S x.2.2‖) := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  have hpt2 : ∀ x : I3, ‖μ x * inner ℂ (G x.1)
      (X2b 2 r τ S h x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))‖ ≤
      39424 / |r| * (Phi₂ (nrm G) (nrm F) (nrm (hiP (D / 2) S)) (dv h) x * E2 x) := fun x => by
    refine (norm_X2_summand_le hS' hh' hF' hB2
      (fun x ha hb hj => norm_X2b_right_le hr τ hh.mean ha hb hj) _ x).trans ?_
    have h1 := (mask_int_le hD hμ S x).1
    have hE := E2_nonneg x
    have hd := dv_nonneg h x.2.2
    have h2 := mul_le_mul_of_nonneg_left h1
      (by positivity : 0 ≤ 39424 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * dv h x.2.2 * E2 x))
    simp only [Phi₂, nrm]
    calc _ = 39424 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * dv h x.2.2 * E2 x) *
          (‖μ x‖ * ‖S x.2.1‖) := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  have hL := mul_nonneg (l2n_nonneg G) (l2n_nonneg F)
  have c1 : cls2 W' (c4 * f₁) b' f₁ ≤ 6 * c4 ^ 2 * (f₁ * b') :=
    cls2_tail (by positivity) hf0 hb'0 le_rfl hWb'
  have e2 : cls2 (c4 * f₁) W' f₁ b' = cls2 W' (c4 * f₁) b' f₁ := by simp only [cls2]; ring
  have h1 := (form_le p1 hpt1).2.trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (e2.le.trans c1) hL) hK)
  have h2 := (form_le p2 hpt2).2.trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c1 hL) hK)
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  have hT : 0 ≤ l2n G * l2n F * (c4 ^ 2 * (f₁ * b')) := by positivity
  have hq : 0 ≤ 1 / |r| := by positivity
  have e3 : Cm2 / |r| * (f₁ * b') * (l2n G * l2n F) -
      (39424 / |r| * (l2n G * l2n F * (6 * c4 ^ 2 * (f₁ * b'))) +
        39424 / |r| * (l2n G * l2n F * (6 * c4 ^ 2 * (f₁ * b')))) =
      39424 * 12 * (1 / |r| * (l2n G * l2n F * (c4 ^ 2 * (f₁ * b')))) := by
    simp only [Cm2]
    ring
  have := mul_nonneg hq hT
  linarith

/-! ### E. The source of the differentiated group -/

/-- On a slow field `B_slow` is the convection `B(S, S)`. -/
lemma Bslow_eq {S : Field} (hS : Adm 2 S) (hS' : PiS S = S) : Bslow S = Bsym S S := by
  have h := PiS_Qres hS
  rwa [hS'] at h

/-- The slow source is admissible in `H¹`, slow, and `f₁ = ‖B_slow(S,S)‖₁ ≤ 41 M_∞ b` (Body 30). -/
theorem Bslow_facts {S : Field} (hS : Adm 2 S) (hS' : PiS S = S) {M : ℝ} (hM : GN.SupBd S M) :
    MZ 1 (Bslow S) ∧ PiS (Bslow S) = Bslow S ∧ hnorm 1 (Bslow S) ≤ 41 * M * hnorm 2 S := by
  obtain ⟨h1, h2⟩ := GN.hnorm_one_Bsym_le hS.inH hM
  have e := Bslow_eq hS hS'
  refine ⟨⟨by rw [e]; exact h1, ?_⟩, ?_, by rw [e]; exact h2⟩
  · simp [Bslow, PiS, H2.Qm_zero_mode, Qres]
  · funext k
    by_cases hk : k 2 = 0 <;> simp [Bslow, PiS, hk]

/-! ### F. The multiplier of rows 2 and 3 -/

/-- **The multiplier of rows 2, 3** at a time where `c_y = cy`, with the caps `B ≥ b`, `Wc ≥ W`,
`Minf ≥ M_∞`.  `D⁻¹B³` is `W_> b²`; `(Wc + Minf) B (D⁻¹ cy + δ₀)` is `(W + M_∞) b b_>`. -/
def highG (Ch D B Wc Minf cy : ℝ) : ℝ := Ch * (B ^ 3 / D + (Wc + Minf) * B * (cy / D + delta0))

lemma delta0_pos : 0 < delta0 := by norm_num [delta0]

/-- The state of the slow field at one `H³` time. -/
structure SlowAt (B Wc Minf : ℝ) (S y R : Field) : Prop where
  adm : Adm 2 S
  slow : PiS S = S
  y3 : InH 3 y
  R2 : InH 2 R
  split : y = S + R
  trace : hnorm 2 R ≤ delta0
  b_le : hnorm 2 S ≤ B
  W_le : wiener S ≤ Wc
  sup : GN.SupBd S Minf

/-- The constant of rows 2, 3: `K` is the constant of the low-last edge. -/
def Chigh (K : ℝ) : ℝ := 5 * Cm3 + Cm2 * K + 82 * Cm2

lemma SlowAt.tail_le {B Wc Minf : ℝ} {S y R : Field} (h : SlowAt B Wc Minf S y R) {D : ℝ}
    (hD : 0 < D) : tailB D S ≤ hnorm 3 y / D + delta0 :=
  (tailB_le_of_split hD h.y3 h.R2 h.split).trans (by linarith [h.trace])

/-- **The undifferentiated group against the multiplier.** -/
theorem YLForm_highG_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D B Wc Minf : ℝ} (hD : 0 < D)
    {S y R z : Field} (h : SlowAt B Wc Minf S y R) (hz : Summable fun k => ‖z k‖ ^ 2)
    (hz' : PiF z = z) {μ : I4 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ ‖hiMask₃ D x‖) :
    ‖YLForm μ 2 r τ S S S z z‖ ≤
      highG (5 * Cm3) D B Wc Minf (hnorm 3 y) / |r| * l2n z ^ 2 := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hM0 : 0 ≤ Minf := (norm_nonneg _).trans (h.sup 0)
  have hb0 := hnorm_nonneg 2 S
  have hB0 : 0 ≤ B := hb0.trans h.b_le
  have hW0 : 0 ≤ wiener S := tsum_nonneg fun _ => norm_nonneg _
  have hWc0 : 0 ≤ Wc := hW0.trans h.W_le
  have hmz : MZ 2 S := ⟨h.adm.inH, h.adm.mean⟩
  refine (YLForm_high_le hr τ D hmz h.slow hz hz hz' hμ).trans ?_
  have h1 : tailW D S ≤ 5 / D * B :=
    (tailW_le hD hmz h.slow).trans (mul_le_mul_of_nonneg_left h.b_le (by positivity))
  have h2 := h.tail_le hD
  have hc0 : 0 ≤ hnorm 3 y / D + delta0 := by
    have := hnorm_nonneg 3 y
    have := delta0_pos
    positivity
  have hb2 : hnorm 2 S ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hb0 h.b_le 2
  have ht1 : tailW D S * hnorm 2 S ^ 2 ≤ 5 * (B ^ 3 / D) := by
    calc tailW D S * hnorm 2 S ^ 2 ≤ 5 / D * B * B ^ 2 :=
          mul_le_mul h1 hb2 (by positivity) (by positivity)
      _ = _ := by ring
  have ht2 : wiener S * hnorm 2 S * tailB D S ≤ Wc * B * (hnorm 3 y / D + delta0) :=
    mul_le_mul (mul_le_mul h.W_le h.b_le hb0 hWc0) h2 (tailB_nonneg _ _) (by positivity)
  have ht3 : Wc * B * (hnorm 3 y / D + delta0) ≤
      5 * ((Wc + Minf) * B * (hnorm 3 y / D + delta0)) := by
    have : 0 ≤ Wc * B * (hnorm 3 y / D + delta0) := by positivity
    have h4 : 0 ≤ Minf * B * (hnorm 3 y / D + delta0) := by positivity
    nlinarith only [this, h4]
  have hC := Cm3_pos
  have hl : l2n z * l2n z = l2n z ^ 2 := by ring
  rw [hl]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [highG, div_eq_mul_inv, div_eq_mul_inv]
  have hinv : 0 ≤ (|r|)⁻¹ := by positivity
  calc Cm3 * (|r|)⁻¹ * (tailW D S * hnorm 2 S ^ 2 + wiener S * hnorm 2 S * tailB D S)
      ≤ Cm3 * (|r|)⁻¹ * (5 * (B ^ 3 / D) + 5 * ((Wc + Minf) * B * (hnorm 3 y / D + delta0))) :=
        mul_le_mul_of_nonneg_left (add_le_add ht1 (ht2.trans ht3)) (by positivity)
    _ = _ := by rw [div_eq_mul_inv (B ^ 3) D, div_eq_mul_inv (hnorm 3 y) D]; ring

/-- **The low-last companion against the multiplier**: `q⁻¹ M_∞ b b_>` (Body 42), by pairing the
output half of `X_{2,hi}` with `v = A^{−1/2} 𝓛_lo z`, `‖v‖ ≤ K M_∞ ‖z‖` (the physical low-pass
estimate of NEW382, Body 27, which belongs to the last-edge node of J5 and is an input here). -/
theorem X2Half_highG_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D B Wc Minf K : ℝ} (hD : 0 < D) (hK : 0 ≤ K)
    {S y R z v : Field} (h : SlowAt B Wc Minf S y R) (hz : Summable fun k => ‖z k‖ ^ 2)
    (hz' : PiF z = z) (hv : Summable fun k => ‖v k‖ ^ 2) (hvz : l2n v ≤ K * Minf * l2n z)
    (hWc : 0 ≤ Wc) {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ ‖hiMask₂ D x‖) :
    ‖X2HalfForm μ 2 r τ S S v z‖ ≤
      highG (Cm2 * K) D B Wc Minf (hnorm 3 y) / |r| * l2n z ^ 2 := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hM0 : 0 ≤ Minf := (norm_nonneg _).trans (h.sup 0)
  have hb0 := hnorm_nonneg 2 S
  have hB0 : 0 ≤ B := hb0.trans h.b_le
  have hmz : MZ 2 S := ⟨h.adm.inH, h.adm.mean⟩
  refine (X2Half_high_le hr τ D hmz h.slow hv hz hz' hμ).trans ?_
  have h2 := h.tail_le hD
  have hc0 : 0 ≤ hnorm 3 y / D + delta0 := by
    have := hnorm_nonneg 3 y
    have := delta0_pos
    positivity
  have hC := Cm2_pos
  have hzn := l2n_nonneg z
  have hvn := l2n_nonneg v
  have ht : hnorm 2 S * tailB D S ≤ B * (hnorm 3 y / D + delta0) :=
    mul_le_mul h.b_le h2 (tailB_nonneg _ _) hB0
  have hq : l2n v * l2n z ≤ K * Minf * l2n z ^ 2 := by
    calc l2n v * l2n z ≤ K * Minf * l2n z * l2n z := mul_le_mul_of_nonneg_right hvz hzn
      _ = _ := by ring
  have hX : 0 ≤ B * (hnorm 3 y / D + delta0) := by positivity
  have hf : (hnorm 2 S * tailB D S) * (l2n v * l2n z) ≤
      (B * (hnorm 3 y / D + delta0)) * (K * Minf * l2n z ^ 2) :=
    mul_le_mul ht hq (mul_nonneg hvn hzn) hX
  have hrest : 0 ≤ Cm2 * K * (B ^ 3 / D) + Cm2 * K * (Wc * B * (hnorm 3 y / D + delta0)) := by
    positivity
  have e : highG (Cm2 * K) D B Wc Minf (hnorm 3 y) =
      Cm2 * K * (Minf * B * (hnorm 3 y / D + delta0)) +
        (Cm2 * K * (B ^ 3 / D) + Cm2 * K * (Wc * B * (hnorm 3 y / D + delta0))) := by
    simp only [highG]
    ring
  rw [e, add_div, add_mul]
  have h5 : Cm2 / |r| * (hnorm 2 S * tailB D S) * (l2n v * l2n z) ≤
      Cm2 * K * (Minf * B * (hnorm 3 y / D + delta0)) / |r| * l2n z ^ 2 := by
    calc _ ≤ Cm2 / |r| * ((B * (hnorm 3 y / D + delta0)) * (K * Minf * l2n z ^ 2)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hf (by positivity)
      _ = _ := by ring
  have h6 : 0 ≤ (Cm2 * K * (B ^ 3 / D) + Cm2 * K * (Wc * B * (hnorm 3 y / D + delta0))) / |r| *
      l2n z ^ 2 := by positivity
  linarith

/-- **The differentiated companion against the multiplier**: `q⁻¹ f₁ b_{>D/2}`, with
`f₁ ≤ 41 M_∞ b` and `b_{>D/2} ≤ 2 D⁻¹ c_y + δ₀`. -/
theorem DSX2_highG_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D B Wc Minf : ℝ} (hD : 0 < D)
    {S y R z : Field} (h : SlowAt B Wc Minf S y R) (hz : Summable fun k => ‖z k‖ ^ 2)
    (hz' : PiF z = z) (hWc : 0 ≤ Wc) {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ ‖hiIntMask D x‖) :
    ‖DSX2Form μ 2 r τ (Bslow S) S z z‖ ≤
      highG (82 * Cm2) D B Wc Minf (hnorm 3 y) / |r| * l2n z ^ 2 := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hM0 : 0 ≤ Minf := (norm_nonneg _).trans (h.sup 0)
  have hb0 := hnorm_nonneg 2 S
  have hB0 : 0 ≤ B := hb0.trans h.b_le
  have hmz : MZ 2 S := ⟨h.adm.inH, h.adm.mean⟩
  obtain ⟨hf1, hf2, hf3⟩ := Bslow_facts h.adm h.slow h.sup
  refine (DSX2_high_le hr τ hD.le hf1 hf2 hmz h.slow hz hz hz' hμ).trans ?_
  have h2 := h.tail_le (D := D / 2) (by positivity)
  have hc3 := hnorm_nonneg 3 y
  have hd := delta0_pos
  have e2 : hnorm 3 y / (D / 2) = 2 * (hnorm 3 y / D) := by
    field_simp
  rw [e2] at h2
  have hc0 : 0 ≤ hnorm 3 y / D + delta0 := by positivity
  have h3 : tailB (D / 2) S ≤ 2 * (hnorm 3 y / D + delta0) := by linarith
  have hf : hnorm 1 (Bslow S) * tailB (D / 2) S ≤
      (41 * Minf * B) * (2 * (hnorm 3 y / D + delta0)) :=
    mul_le_mul (hf3.trans (mul_le_mul_of_nonneg_left h.b_le (by positivity))) h3
      (tailB_nonneg _ _) (by positivity)
  have hC := Cm2_pos
  have hl : l2n z * l2n z = l2n z ^ 2 := by ring
  rw [hl]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have e : highG (82 * Cm2) D B Wc Minf (hnorm 3 y) =
      82 * Cm2 * (Minf * B * (hnorm 3 y / D + delta0)) +
        (82 * Cm2 * (B ^ 3 / D) + 82 * Cm2 * (Wc * B * (hnorm 3 y / D + delta0))) := by
    simp only [highG]
    ring
  rw [e, add_div]
  have hrest : 0 ≤ (82 * Cm2 * (B ^ 3 / D) + 82 * Cm2 * (Wc * B * (hnorm 3 y / D + delta0))) /
      |r| := by positivity
  have h5 : Cm2 / |r| * (hnorm 1 (Bslow S) * tailB (D / 2) S) ≤
      82 * Cm2 * (Minf * B * (hnorm 3 y / D + delta0)) / |r| := by
    calc _ ≤ Cm2 / |r| * ((41 * Minf * B) * (2 * (hnorm 3 y / D + delta0))) :=
          mul_le_mul_of_nonneg_left hf (by positivity)
      _ = _ := by ring
  linarith

/-! ### G. The clip: `rowM2`, `rowM3` -/

/-- Cauchy–Schwarz on a clip: `∫ c ≤ √(ℓ P)`, from `∫ c² ≤ P` ("the high weighted term uses `R⁻¹ (∫
c_y²)^{1/2}` times the square root of the clip length", LOCAL440). -/
lemma clip_cauchy {c : ℝ → ℝ} {u₁ u₂ P : ℝ} (h12 : u₁ ≤ u₂) (hc : ∀ u, 0 ≤ c u)
    (hi : IntervalIntegrable (fun u => c u ^ 2) volume u₁ u₂)
    (hP : ∫ u in u₁..u₂, c u ^ 2 ≤ P) :
    IntervalIntegrable c volume u₁ u₂ ∧ ∫ u in u₁..u₂, c u ≤ Real.sqrt ((u₂ - u₁) * P) := by
  set μ := volume.restrict (Ioc u₁ u₂) with hμ
  have hI : Integrable (fun u => c u ^ 2) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h12).1 hi
  have hm : AEStronglyMeasurable c μ := by
    have h1 := hI.aestronglyMeasurable.aemeasurable
    have h2 : AEMeasurable (fun u => Real.sqrt (c u ^ 2)) μ :=
      Real.continuous_sqrt.measurable.comp_aemeasurable h1
    have e : (fun u => Real.sqrt (c u ^ 2)) = c := funext fun u => Real.sqrt_sq (hc u)
    rw [e] at h2
    exact h2.aestronglyMeasurable
  have hL : MemLp c 2 μ := (memLp_two_iff_integrable_sq hm).2 hI
  have hc1 : Integrable c μ := hL.integrable (by norm_num)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le h12).2 hc1, ?_⟩
  have h0 : (0 : ℝ) ≤ ∫ u in u₁..u₂, c u ^ 2 :=
    intervalIntegral.integral_nonneg h12 fun u _ => sq_nonneg _
  have hP0 : 0 ≤ P := h0.trans hP
  have h3 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (f := c) (g := fun _ => (1 : ℝ))
    Real.HolderConjugate.two_two (Filter.Eventually.of_forall hc)
    (Filter.Eventually.of_forall fun _ => zero_le_one)
    (by simpa using hL) (by simpa using memLp_const (μ := μ) (p := 2) (1 : ℝ))
  simp only [mul_one, Real.rpow_two, one_pow, ← Real.sqrt_eq_rpow, integral_const] at h3
  rw [intervalIntegral.integral_of_le h12]
  rw [intervalIntegral.integral_of_le h12] at hP
  refine h3.trans ?_
  have hvol : μ.real univ = u₂ - u₁ := by
    simp [hμ, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal, sub_nonneg.2 h12]
  simp only [smul_eq_mul, mul_one, hvol]
  rw [← Real.sqrt_mul' _ (sub_nonneg.2 h12), mul_comm]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hP (sub_nonneg.2 h12))

/-- **The clip mass of the multiplier**: `∫_clip highG ≤ Ch (rowM2 + rowM3)`, on a clip of length at
most `1/λ` with `∫_clip c² ≤ P`.  This is the Table's "up to fixed log factors" with no log: rows 2,
3 are clean. -/
theorem highG_clip_le {Ch D B Wc Minf lam P : ℝ} (hCh : 0 ≤ Ch) (hD : 0 < D) (hB : 0 ≤ B)
    (hWM : 0 ≤ Wc + Minf) (hlam : 0 < lam) {c : ℝ → ℝ} {u₁ u₂ : ℝ} (h12 : u₁ ≤ u₂)
    (hlen : u₂ - u₁ ≤ 1 / lam) (hc : ∀ u, 0 ≤ c u)
    (hi : IntervalIntegrable (fun u => c u ^ 2) volume u₁ u₂)
    (hP : ∫ u in u₁..u₂, c u ^ 2 ≤ P) :
    ∫ u in u₁..u₂, highG Ch D B Wc Minf (c u) ≤
      Ch * (rowM2 D lam B + rowM3 D lam P Wc Minf B) := by
  obtain ⟨hc1, hc2⟩ := clip_cauchy h12 hc hi hP
  have hP0 : 0 ≤ P :=
    (intervalIntegral.integral_nonneg h12 fun u _ => sq_nonneg _).trans hP
  have hd := delta0_pos
  set α := Ch * (B ^ 3 / D + (Wc + Minf) * B * delta0) with hα
  set β := Ch * (Wc + Minf) * B / D with hβ
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  have e : ∀ u, highG Ch D B Wc Minf (c u) = α + β * c u := fun u => by
    simp only [highG, hα, hβ]
    field_simp
    ring
  have hint : ∫ u in u₁..u₂, (α + β * c u) = (u₂ - u₁) * α + β * ∫ u in u₁..u₂, c u := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hc1.const_mul β),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul β, smul_eq_mul]
  simp only [e]
  rw [hint]
  have h1 : (u₂ - u₁) * α ≤ 1 / lam * α := mul_le_mul_of_nonneg_right hlen hα0
  have h2 : Real.sqrt ((u₂ - u₁) * P) ≤ Real.sqrt (P / lam) := by
    refine Real.sqrt_le_sqrt ?_
    calc (u₂ - u₁) * P ≤ 1 / lam * P := mul_le_mul_of_nonneg_right hlen hP0
      _ = P / lam := by ring
  have h3 := mul_le_mul_of_nonneg_left (hc2.trans h2) hβ0
  refine (add_le_add h1 h3).trans (le_of_eq ?_)
  simp only [rowM2, rowM3, hα, hβ]
  field_simp
  ring

/-- Covering a long clip by unit clips. -/
lemma clip_cover {c : ℝ → ℝ} {s t U : ℝ} (hU : 0 ≤ U)
    (hi : IntervalIntegrable c volume s t)
    (h1 : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ 1 → ∫ u in u₁..u₂, c u ≤ U) (n : ℕ) :
    ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ (n : ℝ) + 1 →
      ∫ u in u₁..u₂, c u ≤ ((n : ℝ) + 1) * U := by
  induction n with
  | zero =>
    intro u₁ u₂ a b c' d
    simpa using h1 u₁ u₂ a b c' (by simpa using d)
  | succ n ih =>
    intro u₁ u₂ a b c' d
    push_cast at d ⊢
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    by_cases hshort : u₂ - u₁ ≤ 1
    · refine (h1 u₁ u₂ a b c' hshort).trans ?_
      nlinarith
    rw [not_le] at hshort
    have hv : u₁ + 1 ≤ u₂ := by linarith
    have hsub : ∀ x y : ℝ, s ≤ x → x ≤ y → y ≤ t → IntervalIntegrable c volume x y :=
      fun x y hx hxy hy => hi.mono_set (by
        rw [Set.uIcc_of_le hxy, Set.uIcc_of_le (hx.trans (hxy.trans hy))]
        exact Icc_subset_Icc hx hy)
    have hA : s ≤ u₁ + 1 := by linarith
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hsub u₁ (u₁ + 1) a (by linarith) (by linarith)) (hsub (u₁ + 1) u₂ hA hv c')
    have h2 := h1 u₁ (u₁ + 1) a (by linarith) (by linarith) (by linarith)
    have h3 := ih (u₁ + 1) u₂ hA hv c' (by linarith)
    rw [← hsplit]
    nlinarith

/-- **The slow price on every clip**, from the slot `clip` of `SlowOut`: `∫_clip c_y² ≤ 4 P_S(L)` on
a clip of length at most `L`, with no restriction `L ≤ 1`.  The interface `H2Output` asks for the
clips of `1/λ_*` at all caps, and `SlowOut` has clips of length at most one: on `L ≥ 1` the unit
cover costs `(L + 1) C ex (R⁴ + R⁵) ≤ 4 C ex L R⁵`. -/
lemma slowOut_clip_le {C ex R : ℝ} {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} {r : ℝ} {g : Field}
    {y : ℝ → Field} {s t : ℝ} (hO : SlowOut C ex R Sl r g y s t) (hC : 0 ≤ C * ex) (hR : 1 ≤ R)
    {u₁ u₂ L : ℝ} (h1 : s ≤ u₁) (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ t) (hL : u₂ - u₁ ≤ L) :
    ∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2 ≤ 4 * slowPrice C ex R L := by
  have hR5 : 0 ≤ R ^ 5 := by positivity
  have hR4 : 0 ≤ R ^ 4 := by positivity
  have hRR : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR (by norm_num)
  have hL0 : 0 ≤ L := (sub_nonneg.2 h12).trans hL
  have hP0 : ∀ ℓ, 0 ≤ ℓ → 0 ≤ slowPrice C ex R ℓ := fun ℓ hℓ => by
    simp only [slowPrice]
    positivity
  have hmono : ∀ {a b : ℝ}, a ≤ b → slowPrice C ex R a ≤ slowPrice C ex R b := fun {a b} hab => by
    simp only [slowPrice]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have := mul_le_mul_of_nonneg_right hab hR5
    linarith
  have hunit : ∀ a b : ℝ, s ≤ a → a ≤ b → b ≤ t → b - a ≤ 1 →
      ∫ u in a..b, hnorm 3 (corrSlow r g y u) ^ 2 ≤ slowPrice C ex R 1 :=
    fun a b ha hab hb hl => (hO.clip a b ha hab hb hl).trans (hmono hl)
  by_cases hshort : u₂ - u₁ ≤ 1
  · have := (hO.clip u₁ u₂ h1 h12 h2 hshort).trans (hmono hL)
    linarith [hP0 L hL0]
  rw [not_le] at hshort
  set n : ℕ := ⌊u₂ - u₁⌋₊ with hn
  have hn1 : u₂ - u₁ ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hn2 : (n : ℝ) ≤ u₂ - u₁ := Nat.floor_le (sub_nonneg.2 h12)
  have hcov := clip_cover (hP0 1 zero_le_one) hO.cy_int hunit n u₁ u₂ h1 h12 h2 hn1
  have hL1 : 1 < L := hshort.trans_le hL
  have hb : ((n : ℝ) + 1) * slowPrice C ex R 1 ≤ 2 * L * slowPrice C ex R 1 :=
    mul_le_mul_of_nonneg_right (by linarith) (hP0 1 zero_le_one)
  refine hcov.trans (hb.trans ?_)
  simp only [slowPrice]
  have h3 : 2 * L * (C * ex * (R ^ 4 + 1 * R ^ 5)) ≤ 4 * (C * ex * (L * R ^ 5)) := by
    have h4 : R ^ 4 + 1 * R ^ 5 ≤ 2 * R ^ 5 := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hC hL0)
    nlinarith only [h5]
  have h6 : 0 ≤ C * ex * R ^ 4 := by positivity
  nlinarith only [h3, h6]

/-- `H²` energy coordinates are `A F`. -/
lemma zOf_two (F : Field) : zOf 2 F = lapF F := by
  funext k
  simp only [zOf, lapF, absk_sq]

/-- **The multiplier of rows 2, 3 on a joint piece**: `G(u) = highG/q`, at `D = R²`, the caps and
the `M_∞` of the interface. -/
def rowG (Ch : ℝ) (D : JointData) (R : ℝ) (caps : Caps) (r : ℝ) (g : Field) (y : ℝ → Field)
    (u : ℝ) : ℝ :=
  highG Ch (jointD R) (cp caps.BS) (cp caps.WS) (D.Minf R) (hnorm 3 (corrSlow r g y u)) / |r|

/-- **Rows 2 and 3 of Table quant-metric, on a joint piece, in the form `H2EnergyInterfaceB`
consumes.**  The hypotheses are those of the interface, with `D = R²`.  Then `G = rowG` is a
nonnegative integrable multiplier such that:
* at a.e. time of the piece (the `H³` times of `y_S`), the high-ancestor parts of the actual cubic
  group are at most `G(u) b_F(u)²`: the undifferentiated `X₂𝓛 + Z𝓛` and adjoints on `|p| > D`
  (LOCAL440 step 1), its low-last companion (Bodies 41, 42), the differentiated companion on the
  high-intermediate sector (Bodies 33, 42);
* on every clip of length at most `1/λ_*`, which is literally the clause of `H2Output`,
  `∫ G ≤ 2⁻³⁵`, the budget of Body 47: this is `q⁻¹ (rowM2 + rowM3) ≤ 2⁻³⁵` from `JointData.q₂Full`.

So `G` can be added to the `G` of `H2Output`.  `K` is the constant of the physical low-pass estimate
`‖A^{−1/2} 𝓛_lo z‖ ≤ K M_∞ ‖z‖` (NEW382, Body 42), an input of the last-edge node.  The hypothesis
on `D.Cm` fixes that field of `JointData`; `r ≠ 0` is role 16 of the threshold `q₂`. -/
theorem row23_piece (D : JointData) {X R r K : ℝ} {g : Field} {y : ℝ → Field} {Ty : ENNReal}
    {caps : Caps} {s t : ℝ} (hr : r ≠ 0) (hR : 1 ≤ R) (hK : 0 ≤ K) (hCS : 0 ≤ D.CS)
    (hCm : 2 ^ 36 * Chigh K ≤ D.Cm) (hsol : ActualSol X (R - X) r g y Ty)
    (hP : JointPiece (D.Tp X R) (D.Minf R) (D.q₂Full X R) (D.near X R) (D.slowOut X R) r g y Ty
      caps s t) :
    (∀ u, 0 ≤ rowG (Chigh K) D R caps r g y u) ∧
    IntervalIntegrable (rowG (Chigh K) D R caps r g y) volume s t ∧
    (∀ᵐ u ∂(volume.restrict (Icc s t)), ∀ (μ₃ : I4 → ℂ) (μ₂ μᵢ : I3 → ℂ) (v : Field),
      (∀ x, ‖μ₃ x‖ ≤ ‖hiMask₃ (jointD R) x‖) → (∀ x, ‖μ₂ x‖ ≤ ‖hiMask₂ (jointD R) x‖) →
      (∀ x, ‖μᵢ x‖ ≤ ‖hiIntMask (jointD R) x‖) → (Summable fun k => ‖v k‖ ^ 2) →
      l2n v ≤ K * D.Minf R * fastNorm 2 r g y u →
      ‖YLForm μ₃ 2 r (r * u) (PiS (actual r g y u)) (PiS (actual r g y u))
          (PiS (actual r g y u)) (zOf 2 (PiF (actual r g y u))) (zOf 2 (PiF (actual r g y u)))‖ +
        ‖X2HalfForm μ₂ 2 r (r * u) (PiS (actual r g y u)) (PiS (actual r g y u)) v
          (zOf 2 (PiF (actual r g y u)))‖ +
        ‖DSX2Form μᵢ 2 r (r * u) (Bslow (PiS (actual r g y u))) (PiS (actual r g y u))
          (zOf 2 (PiF (actual r g y u))) (zOf 2 (PiF (actual r g y u)))‖ ≤
        rowG (Chigh K) D R caps r g y u * fastNorm 2 r g y u ^ 2) ∧
    ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ 1 / lamStar 1 caps.PF (jointBs X R caps) →
      ∫ u in u₁..u₂, rowG (Chigh K) D R caps r g y u ≤ 1 / 2 ^ 35 := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hR0 : 0 < R := by linarith
  have hD0 : 0 < jointD R := by unfold jointD; positivity
  have hBc := cp_nonneg caps.BS
  have hWc := cp_nonneg caps.WS
  have hd := delta0_pos
  have hex : 0 < Ex D.cS R := Real.exp_pos _
  have hMinf : 0 ≤ D.Minf R := by
    unfold JointData.Minf
    positivity
  have hCex : 0 ≤ D.CS * Ex D.cS R := by positivity
  have hC0 : 0 ≤ Chigh K := by
    have := Cm3_pos
    have := Cm2_pos
    unfold Chigh
    positivity
  have hcy : ∀ u, 0 ≤ hnorm 3 (corrSlow r g y u) := fun u => hnorm_nonneg _ _
  have hO : SlowOut D.CS (Ex D.cS R) R (D.Sl X R) r g y s t := hP.slow
  refine ⟨fun u => ?_, ?_, ?_, ?_⟩
  · have := hcy u
    simp only [rowG, highG]
    positivity
  · have h1 := (clip_cauchy hP.hst hcy hO.cy_int le_rfl).1
    have h2 : IntervalIntegrable (fun u => (Chigh K * (cp caps.BS ^ 3 / jointD R +
        (cp caps.WS + D.Minf R) * cp caps.BS * delta0) +
        Chigh K * (cp caps.WS + D.Minf R) * cp caps.BS / jointD R *
          hnorm 3 (corrSlow r g y u)) / |r|) volume s t :=
      (intervalIntegrable_const.add (h1.const_mul _)).div_const _
    refine h2.congr fun u _ => ?_
    simp only [rowG, highG]
    field_simp
    ring
  · filter_upwards [ae_inH3_corr hsol hr hP.hs hP.hst hP.ht, ae_restrict_mem measurableSet_Icc]
      with u hu3 hu μ₃ μ₂ μᵢ v h3 h2 hi hv hvz
    have hu0 : 0 ≤ u := hP.hs.trans hu.1
    have huT := lt_lifespan hu.2 hP.ht
    have hA := actual_adm hsol hu0 huT
    have hRS := slowCorr_adm hsol hr hu0 huT
    have hon := hP.onPrefix.1 u hu
    have hS : SlowAt (cp caps.BS) (cp caps.WS) (D.Minf R) (PiS (actual r g y u))
        (corrSlow r g y u) (slowCorr r g y u) :=
      ⟨hA.PiS, PiS_PiS_eq _, hu3, hRS.inH, rfl, hO.trace u hu, hon.2.2.2.1.trans (le_cp _),
        hon.2.2.2.2.trans (le_cp _), GN.supBd_slowSup hA.PiS.inH (hP.sup u hu)⟩
    have hF := hA.PiF
    obtain ⟨hz1, hz2⟩ := lapF_l2 hF.inH
    have hzn : l2n (zOf 2 (PiF (actual r g y u))) = fastNorm 2 r g y u := by
      rw [zOf_two]
      exact hz2
    have hzs : Summable fun k => ‖zOf 2 (PiF (actual r g y u)) k‖ ^ 2 := by
      rw [zOf_two]
      exact hz1
    have hzf : PiF (zOf 2 (PiF (actual r g y u))) = zOf 2 (PiF (actual r g y u)) := by
      rw [zOf_two, PiF_lapF, PiF_PiF_eq]
    have e1 := YLForm_highG_le hr (r * u) hD0 hS hzs hzf h3
    have e2 := X2Half_highG_le hr (r * u) hD0 hK hS hzs hzf hv (by rwa [hzn]) hWc h2
    have e3 := DSX2_highG_le hr (r * u) hD0 hS hzs hzf hWc hi
    rw [hzn] at e1 e2 e3
    refine (add_le_add (add_le_add e1 e2) e3).trans (le_of_eq ?_)
    simp only [rowG, highG, Chigh]
    ring
  · intro u₁ u₂ h1 h12 h2 hl
    set lam := lamStar 1 caps.PF (jointBs X R caps) with hlamd
    have hlam0 : 0 ≤ lam := by
      simp only [hlamd, lamStar, dZero]
      positivity
    rcases hlam0.eq_or_lt with hlam | hlam
    · have h0 : u₂ - u₁ ≤ 0 := by simpa [← hlam] using hl
      have e : u₁ = u₂ := le_antisymm h12 (by linarith)
      rw [e, intervalIntegral.integral_same]
      positivity
    have hsub : Set.uIcc u₁ u₂ ⊆ Set.uIcc s t := by
      rw [uIcc_of_le h12, uIcc_of_le hP.hst]
      exact Icc_subset_Icc h1 h2
    have hi : IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume u₁ u₂ :=
      hO.cy_int.mono_set hsub
    set P₀ := slowPrice D.CS (Ex D.cS R) R (1 / lam) with hP₀
    have hP₀0 : 0 ≤ P₀ := by
      simp only [hP₀, slowPrice]
      positivity
    have hPr : (∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2) ≤ 4 * P₀ :=
      slowOut_clip_le hO hCex hR h1 h12 h2 hl
    have hclip := highG_clip_le (Ch := Chigh K) (D := jointD R) (B := cp caps.BS)
      (Wc := cp caps.WS) (Minf := D.Minf R) hC0 hD0 hBc (by positivity) hlam h12 hl hcy hi hPr
    have hint : ∫ u in u₁..u₂, rowG (Chigh K) D R caps r g y u =
        (∫ u in u₁..u₂, highG (Chigh K) (jointD R) (cp caps.BS) (cp caps.WS) (D.Minf R)
          (hnorm 3 (corrSlow r g y u))) / |r| := by
      simp only [rowG]
      rw [intervalIntegral.integral_div]
    have hM3 : rowM3 (jointD R) lam (4 * P₀) (cp caps.WS) (D.Minf R) (cp caps.BS) ≤
        2 * rowM3 (jointD R) lam P₀ (cp caps.WS) (D.Minf R) (cp caps.BS) := by
      simp only [rowM3]
      have e4 : Real.sqrt (4 * P₀ / lam) = 2 * Real.sqrt (P₀ / lam) := by
        rw [show 4 * P₀ / lam = 2 ^ 2 * (P₀ / lam) by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]
      rw [e4]
      have h9 : 0 ≤ (cp caps.WS + D.Minf R) * cp caps.BS * (delta0 / lam) := by positivity
      have h10 : 0 ≤ (cp caps.WS + D.Minf R) * cp caps.BS * (Real.sqrt (P₀ / lam) / jointD R) := by
        positivity
      have e5 : (cp caps.WS + D.Minf R) * cp caps.BS * (2 * Real.sqrt (P₀ / lam) / jointD R +
          delta0 / lam) = 2 * ((cp caps.WS + D.Minf R) * cp caps.BS *
            (Real.sqrt (P₀ / lam) / jointD R)) +
            (cp caps.WS + D.Minf R) * cp caps.BS * (delta0 / lam) := by ring
      rw [e5]
      have e6 : 2 * ((cp caps.WS + D.Minf R) * cp caps.BS * (Real.sqrt (P₀ / lam) / jointD R +
          delta0 / lam)) = 2 * ((cp caps.WS + D.Minf R) * cp caps.BS *
            (Real.sqrt (P₀ / lam) / jointD R)) +
            2 * ((cp caps.WS + D.Minf R) * cp caps.BS * (delta0 / lam)) := by ring
      rw [e6]
      linarith
    have hM2 : 0 ≤ rowM2 (jointD R) lam (cp caps.BS) := by
      simp only [rowM2]
      positivity
    have hM30 : 0 ≤ rowM3 (jointD R) lam P₀ (cp caps.WS) (D.Minf R) (cp caps.BS) := by
      simp only [rowM3]
      positivity
    have hA : highAnc D.CS (Ex D.cS R) X R caps = rowM2 (jointD R) lam (cp caps.BS) +
        rowM3 (jointD R) lam P₀ (cp caps.WS) (D.Minf R) (cp caps.BS) := rfl
    have hA0 : 0 ≤ highAnc D.CS (Ex D.cS R) X R caps := by
      rw [hA]
      positivity
    have hclip' : (∫ u in u₁..u₂, highG (Chigh K) (jointD R) (cp caps.BS) (cp caps.WS) (D.Minf R)
        (hnorm 3 (corrSlow r g y u))) ≤ 2 * Chigh K * highAnc D.CS (Ex D.cS R) X R caps := by
      refine hclip.trans ?_
      rw [hA]
      have := mul_le_mul_of_nonneg_left hM3 hC0
      nlinarith only [this, mul_nonneg hC0 hM2]
    have hq : D.Cm * highAnc D.CS (Ex D.cS R) X R caps ≤ |r| :=
      (le_max_right _ _).trans hP.thr
    have h5 : 2 ^ 35 * (2 * Chigh K * highAnc D.CS (Ex D.cS R) X R caps) ≤ |r| := by
      calc _ = (2 ^ 36 * Chigh K) * highAnc D.CS (Ex D.cS R) X R caps := by ring
        _ ≤ D.Cm * highAnc D.CS (Ex D.cS R) X R caps := mul_le_mul_of_nonneg_right hCm hA0
        _ ≤ |r| := hq
    rw [hint, div_le_iff₀ hr0]
    calc _ ≤ 2 * Chigh K * highAnc D.CS (Ex D.cS R) X R caps := hclip'
      _ ≤ 1 / 2 ^ 35 * |r| := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
          linarith

end OVNS.Quant.Metric

end
