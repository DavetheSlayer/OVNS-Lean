import OddViscousNS.Quant.Joint.Metric.HalfX2
import OddViscousNS.Quant.Joint.Sources.History
import OddViscousNS.Quant.Joint.Sources.Filter

/-!
# The output half of `X₁`: the elementary facts (step J5, node N12)

LOCAL363 (`checkpoints/FAST_SLOW_METRIC_FORCE_PAIRING_363_LOCAL_CANDIDATE.md`): on comparable fast
lengths `K, J`, `K |X₁|_{kj} ≲ f_p √(P/q)`, and on separated lengths the old bound `P³/min(K, J)²`.

The source splits by helicity, with a physical argument for opposite helicities: "the transverse
projected advection matrix and reverse adjoint cancel at unweighted level".  On the block form
`inner_X1b` this argument is one fact about the helical basis (`cross_small`, `elt_opp_le`): if
`b ≠ c`, then `h_c(k)` and `h_b(j)` are, after the conjugation in the triple product, in the same
helical line up to the angle between `k` and `j`, so their cross product has size `P/K`.  Then:
* every channel has `|numerator| ≤ 16 |v − u|` (`num_cmp_le`), `v − u` being the phase;
* equal helicities: `|v − u| = |K − J| ≤ P`, and the heat or the phase pays (`chan_eq_le`);
* opposite helicities: `|v − u| = K + J`, and `elt` carries `P/K` (`chan_opp_le`).
-/

open scoped ComplexConjugate

open OVNS.Quant.H2 (norm_metSym_mul_le)

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. Two helical vectors of the same sign at close directions -/

/-- `x × (n × y) = (x·y) n − (x·n) y`, for the bilinear pairing. -/
private lemma cross_cross_bd (x n y : V3) :
    cross x (cross n y) = bd x y • n - bd x n • y := by
  apply v3_ext <;>
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, bd, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul] <;> ring

private lemma bd_cross_cyc (m x y : V3) : bd (cross m x) y = bd m (cross x y) := by
  simp only [bd, cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

private lemma bd_cross_mid (n x y : V3) : bd x (cross n y) = -bd n (cross x y) := by
  simp only [bd, cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

private lemma bd_smul_left' (c : ℂ) (a b : V3) : bd (c • a) b = c * bd a b := by
  simp only [bd, PiLp.smul_apply, smul_eq_mul]
  ring

private lemma bd_sub_right' (a b c : V3) : bd a (b - c) = bd a b - bd a c := by
  simp only [bd, PiLp.sub_apply]
  ring

private lemma cross_smul_right' (a b : V3) (c : ℂ) : cross a (c • b) = c • cross a b := by
  apply v3_ext <;>
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.smul_apply, smul_eq_mul] <;>
    ring

/-- **Two helical vectors of the same sign**: `‖x × y‖ ≤ (3/2) ‖n − m‖ ‖x‖ ‖y‖` for the unit
directions `m, n`, where `i m × x = σ x`, `i n × y = σ y`, `σ² = 1`, `x·m = 0`. -/
theorem cross_small {x y m n : V3} {σ : ℂ} (hσ : σ * σ = 1) (hσn : ‖σ‖ = 1)
    (hm : Complex.I • cross m x = σ • x) (hn : Complex.I • cross n y = σ • y) (hxm : bd x m = 0)
    (hn1 : ‖n‖ ≤ 1) : ‖cross x y‖ ≤ 3 / 2 * ‖n - m‖ * ‖x‖ * ‖y‖ := by
  set c : ℂ := σ * Complex.I with hc
  have hcn : ‖c‖ = 1 := by simp [hc, hσn]
  have hxe : x = c • cross m x := by
    rw [hc, mul_smul, hm, smul_smul, hσ, one_smul]
  have hye : y = c • cross n y := by
    rw [hc, mul_smul, hn, smul_smul, hσ, one_smul]
  set W := cross x y with hW
  have hWn : ‖W‖ ≤ ‖x‖ * ‖y‖ := norm_cross_le x y
  have h1 : bd x y = c * bd m W := by
    conv_lhs => rw [hxe]
    rw [bd_smul_left', bd_cross_cyc]
  have h2 : bd x y = -(c * bd n W) := by
    conv_lhs => rw [hye]
    rw [bd_smul_right, bd_cross_mid]
    ring
  have h3 : (2 : ℂ) * bd x y = -(c * bd (n - m) W) := by
    have e : bd (n - m) W = bd n W - bd m W := by
      rw [bd_comm, bd_sub_right', bd_comm W n, bd_comm W m]
    rw [e, two_mul]
    nth_rewrite 1 [h1]
    rw [h2]
    ring
  have h4 : ‖bd x y‖ ≤ 1 / 2 * (‖n - m‖ * (‖x‖ * ‖y‖)) := by
    have h5 : 2 * ‖bd x y‖ = ‖bd (n - m) W‖ := by
      have := congrArg norm h3
      simpa [hcn] using this
    have h6 := norm_bd_le (n - m) W
    have h7 := mul_le_mul_of_nonneg_left hWn (norm_nonneg (n - m))
    linarith
  have h5 : bd x n = bd x (n - m) := by rw [bd_sub_right', hxm, sub_zero]
  have h6 : ‖bd x n‖ ≤ ‖x‖ * ‖n - m‖ := by
    rw [h5]
    exact norm_bd_le _ _
  have h7 : W = c • (bd x y • n - bd x n • y) := by
    rw [← cross_cross_bd, ← cross_smul_right', ← hye]
  have h8 : ‖W‖ ≤ ‖bd x y‖ * ‖n‖ + ‖bd x n‖ * ‖y‖ := by
    rw [h7, norm_smul, hcn, one_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul]
  have h9 : ‖bd x y‖ * ‖n‖ ≤ ‖bd x y‖ * 1 := mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)
  have h10 := mul_le_mul_of_nonneg_right h6 (norm_nonneg y)
  nlinarith only [h8, h9, h10, h4]

/-! ### B. The triple product at opposite helicities -/

private lemma cross_smul_left' (c : ℂ) (a b : V3) : cross (c • a) b = c • cross a b := by
  apply v3_ext <;>
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.smul_apply, smul_eq_mul] <;>
    ring

private lemma cross_neg_mode (k : Mode) (v : V3) :
    cross (modeVec (-k)) v = -cross (modeVec k) v := by
  apply v3_ext <;>
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, modeVec_apply, PiLp.neg_apply,
      Pi.neg_apply, Int.cast_neg] <;> ring

/-- `‖k‖ = |k|` for the complex wave vector. -/
lemma norm_modeVec (k : Mode) : ‖modeVec k‖ = absk k := by
  rw [EuclideanSpace.norm_eq, absk, absSq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [modeVec_apply]
  rw [Complex.norm_intCast]
  simp

private lemma modeVec_add' (p j : Mode) : modeVec (p + j) = modeVec p + modeVec j := by
  ext i
  simp [modeVec_apply]

/-- The angle between `k` and `j`: `‖k/|k| − j/|j|‖ ≤ 2 P/|k|`, with `k = p + j`. -/
lemma norm_dir_le {p k j : Mode} (hk : p + j = k) (hk0 : k ≠ 0) (hj0 : j ≠ 0) :
    ‖((absk k)⁻¹ : ℂ) • modeVec k - ((absk j)⁻¹ : ℂ) • modeVec j‖ ≤ 2 * absk p / absk k := by
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk0)
  have hJ : 0 < absk j := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have e : ((absk k)⁻¹ : ℂ) • modeVec k - ((absk j)⁻¹ : ℂ) • modeVec j =
      ((absk k)⁻¹ : ℂ) • modeVec p + (((absk k : ℂ))⁻¹ - ((absk j : ℂ))⁻¹) • modeVec j := by
    have e0 : modeVec k = modeVec p + modeVec j := by rw [← hk, modeVec_add']
    rw [e0, smul_add, sub_smul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have n1 : ‖((absk k)⁻¹ : ℂ) • modeVec p‖ = absk p / absk k := by
    rw [norm_smul, norm_modeVec, norm_inv, Complex.norm_real, Real.norm_of_nonneg hK.le]
    field_simp
  have n2 : ‖(((absk k : ℂ))⁻¹ - ((absk j : ℂ))⁻¹) • modeVec j‖ ≤ absk p / absk k := by
    have e2 : ((absk k : ℂ))⁻¹ - ((absk j : ℂ))⁻¹ = (((absk k)⁻¹ - (absk j)⁻¹ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [norm_smul, norm_modeVec, e2, Complex.norm_real, Real.norm_eq_abs]
    have e3 : (absk k)⁻¹ - (absk j)⁻¹ = (absk j - absk k) / (absk k * absk j) := by
      field_simp
    rw [e3, abs_div, abs_of_pos (by positivity : 0 < absk k * absk j)]
    have h1 : |absk j - absk k| ≤ absk p := by
      have a1 := absk_add_le p j
      have a2 := absk_sub_le k j
      rw [hk] at a1
      rw [show k - j = p by rw [← hk]; abel] at a2
      have a3 := absk_add_le k (-p)
      rw [show k + -p = j by rw [← hk]; abel, absk_neg] at a3
      exact abs_le.2 ⟨by linarith, by linarith⟩
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hK]
    nlinarith only [mul_le_mul_of_nonneg_right h1 (mul_nonneg hK.le hJ.le), mul_pos hK hJ]
  rw [n1]
  have e4 : 2 * absk p / absk k = absk p / absk k + absk p / absk k := by ring
  rw [e4]
  linarith

/-- **The triple product at opposite helicities**: for `b ≠ c` the two fast legs lie in one helical
line up to the angle, so `|elt| ≤ 3 (P/K) ‖v‖ ‖w‖ ‖Z‖`.  This is LOCAL363's cancellation of the
unweighted transport. -/
theorem elt_opp_le {a b c : Sgn} (hbc : b ≠ c) {p k j : Mode} (hk : p + j = k) (hk0 : k ≠ 0)
    (hj0 : j ≠ 0) (v w Z : V3) :
    ‖elt a b c p k j v w Z‖ ≤ 3 * (absk p / absk k) * (‖v‖ * ‖w‖ * ‖Z‖) := by
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk0)
  have hJ : 0 < absk j := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hKc : (absk k : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have hJc : (absk j : ℂ) ≠ 0 := by exact_mod_cast hJ.ne'
  set x := hel b j w with hx
  set y := conjV (hel c k Z) with hy
  set m : V3 := ((absk j)⁻¹ : ℂ) • modeVec j with hm
  set n : V3 := ((absk k)⁻¹ : ℂ) • modeVec k with hn
  have hsb : sg c = -sg b := by
    cases b <;> cases c <;> simp_all [sg]
  have hσ : (sg b : ℂ) * sg b = 1 := by
    cases b <;> simp [sg]
  have hσn : ‖(sg b : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    cases b <;> simp [sg]
  have hm1 : Complex.I • cross m x = (sg b : ℂ) • x := by
    have h1 := cross_hel b j w
    rw [← hx] at h1
    rw [hm, cross_smul_left', smul_comm, h1, smul_smul]
    congr 1
    push_cast
    field_simp
  have hn1 : Complex.I • cross n y = (sg b : ℂ) • y := by
    have e0 : y = hel c (-k) (conjV Z) := conjV_hel c k Z
    have h1 := cross_hel c (-k) (conjV Z)
    rw [← e0, absk_neg, cross_neg_mode] at h1
    rw [hn, cross_smul_left', smul_comm, smul_neg] at *
    have h2 : Complex.I • cross (modeVec k) y = -(((sg c * absk k : ℝ) : ℂ) • y) := by
      rw [← h1, neg_neg]
    rw [h2, smul_neg, smul_smul, ← neg_smul]
    congr 1
    rw [hsb]
    push_cast
    field_simp
  have hxm : bd x m = 0 := by
    have h1 : dotM x j = 0 := dotM_hel b j w
    have h2 : bd x (modeVec j) = dotM x j := by
      simp only [bd, dotM_eq, modeVec_apply]
    rw [hm, bd_smul_right, h2, h1, mul_zero]
  have hnn : ‖n‖ ≤ 1 := by
    rw [hn, norm_smul, norm_modeVec, norm_inv, Complex.norm_real, Real.norm_of_nonneg hK.le]
    rw [inv_mul_cancel₀ hK.ne']
  have hc := cross_small hσ hσn hm1 hn1 hxm hnn
  have hdir : ‖n - m‖ ≤ 2 * absk p / absk k := norm_dir_le hk hk0 hj0
  have hxw : ‖x‖ ≤ ‖w‖ := norm_hel_le _ _ _
  have hyZ : ‖y‖ ≤ ‖Z‖ := by
    rw [hy, norm_conjV]
    exact norm_hel_le _ _ _
  have hB : ‖hel a p v‖ ≤ ‖v‖ := norm_hel_le _ _ _
  have e : elt a b c p k j v w Z = bd (hel a p v) (cross x y) := by
    unfold elt
    rw [bd_comm, bd_cross_cyc]
  rw [e]
  refine (norm_bd_le _ _).trans ?_
  have hdn := norm_nonneg (n - m)
  have hx0 := norm_nonneg x
  have hy0 := norm_nonneg y
  have hP : 0 ≤ absk p / absk k := div_nonneg (absk_nonneg p) hK.le
  have h1 : ‖cross x y‖ ≤ 3 * (absk p / absk k) * (‖w‖ * ‖Z‖) := by
    refine hc.trans ?_
    have h2 : 3 / 2 * ‖n - m‖ ≤ 3 * (absk p / absk k) := by
      have e2 : 2 * absk p / absk k = 2 * (absk p / absk k) := by ring
      rw [e2] at hdir
      linarith
    have h3 : ‖x‖ * ‖y‖ ≤ ‖w‖ * ‖Z‖ := mul_le_mul hxw hyZ hy0 (norm_nonneg _)
    calc 3 / 2 * ‖n - m‖ * ‖x‖ * ‖y‖ = 3 / 2 * ‖n - m‖ * (‖x‖ * ‖y‖) := by ring
      _ ≤ 3 * (absk p / absk k) * (‖w‖ * ‖Z‖) := mul_le_mul h2 h3 (by positivity) (by positivity)
  calc ‖hel a p v‖ * ‖cross x y‖ ≤ ‖v‖ * (3 * (absk p / absk k) * (‖w‖ * ‖Z‖)) :=
        mul_le_mul hB h1 (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

/-! ### C. The numerator on comparable lengths -/

/-- The two weighted lengths. -/
private lemma AB_bounds {s : ℕ} (hs : s = 1 ∨ s = 2) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : x ≤ 2 * y) (h2 : y ≤ 2 * x) :
    |(x / y) ^ s * y - (y / x) ^ s * x| ≤ 4 * |x - y| ∧
      (x / y) ^ s * y + (y / x) ^ s * x ≤ 4 * (x + y) := by
  have hxy : 0 < x * y := by positivity
  have hQ := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
  have hP : 2 * (x ^ 2 + y ^ 2) ≤ 5 * (x * y) := by nlinarith only [hQ]
  rcases hs with rfl | rfl
  · have e1 : (x / y) ^ 1 * y = x := by field_simp
    have e2 : (y / x) ^ 1 * x = y := by field_simp
    rw [e1, e2]
    constructor
    · have := abs_nonneg (x - y)
      linarith
    · linarith
  · have e1 : (x / y) ^ 2 * y = x ^ 2 / y := by field_simp
    have e2 : (y / x) ^ 2 * x = y ^ 2 / x := by field_simp
    rw [e1, e2]
    constructor
    · have e3 : x ^ 2 / y - y ^ 2 / x = (x - y) * ((x ^ 2 + x * y + y ^ 2) / (x * y)) := by
        field_simp
        ring
      have h3 : (x ^ 2 + x * y + y ^ 2) / (x * y) ≤ 4 := by
        rw [div_le_iff₀ hxy]
        linarith
      rw [e3, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (x ^ 2 + x * y + y ^ 2) / (x * y)),
        mul_comm]
      exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
    · have e3 : x ^ 2 / y + y ^ 2 / x = (x + y) * ((x ^ 2 - x * y + y ^ 2) / (x * y)) := by
        field_simp
        ring
      have h3 : (x ^ 2 - x * y + y ^ 2) / (x * y) ≤ 4 := by
        rw [div_le_iff₀ hxy]
        nlinarith only [hP, hxy]
      rw [e3, mul_comm]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)

/-- The difference of the two weights. -/
private lemma wt_diff_le {s : ℕ} (hs : s = 1 ∨ s = 2) {x y P : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : x ≤ 2 * y) (h2 : y ≤ 2 * x) (hP : P ≤ x + y) :
    P * |(x / y) ^ s - (y / x) ^ s| ≤ 12 * |x - y| := by
  have hxy : 0 < x * y := by positivity
  have hQ := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
  have hP2 : 2 * (x ^ 2 + y ^ 2) ≤ 5 * (x * y) := by nlinarith only [hQ]
  have hS : 2 * (x + y) ^ 2 ≤ 9 * (x * y) := by nlinarith only [hP2]
  have hPS : P * (x + y) ≤ (x + y) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hP (by positivity : 0 ≤ x + y)
    nlinarith only [this]
  have hA := abs_nonneg (x - y)
  rcases hs with rfl | rfl
  · have e : (x / y) ^ 1 - (y / x) ^ 1 = (x - y) * ((x + y) / (x * y)) := by
      field_simp
      ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (x + y) / (x * y))]
    have h3 : P * ((x + y) / (x * y)) ≤ 12 := by
      rw [mul_div_assoc', div_le_iff₀ hxy]
      nlinarith only [hPS, hS, hxy]
    calc P * (|x - y| * ((x + y) / (x * y))) = P * ((x + y) / (x * y)) * |x - y| := by ring
      _ ≤ 12 * |x - y| := mul_le_mul_of_nonneg_right h3 hA
  · have e : (x / y) ^ 2 - (y / x) ^ 2 =
        (x - y) * ((x + y) * (x ^ 2 + y ^ 2) / (x * y) ^ 2) := by
      field_simp
      ring
    rw [e, abs_mul, abs_of_nonneg (by positivity :
      0 ≤ (x + y) * (x ^ 2 + y ^ 2) / (x * y) ^ 2)]
    have h3 : P * ((x + y) * (x ^ 2 + y ^ 2) / (x * y) ^ 2) ≤ 12 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have h4 : P * (x + y) * (2 * (x ^ 2 + y ^ 2)) ≤
          ((x + y) ^ 2) * (5 * (x * y)) := mul_le_mul hPS hP2 (by positivity) (by positivity)
      have h5 : ((x + y) ^ 2) * (5 * (x * y)) ≤ (9 / 2 * (x * y)) * (5 * (x * y)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith only [h4, h5, sq_nonneg (x * y)]
    calc P * (|x - y| * ((x + y) * (x ^ 2 + y ^ 2) / (x * y) ^ 2)) =
        P * ((x + y) * (x ^ 2 + y ^ 2) / (x * y) ^ 2) * |x - y| := by ring
      _ ≤ 12 * |x - y| := mul_le_mul_of_nonneg_right h3 hA

/-- **The numerator of a channel on comparable lengths**: it is at most `16` times the phase. -/
lemma num_cmp_le {s : ℕ} (hs : s = 1 ∨ s = 2) {x y P l u v : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : x ≤ 2 * y) (h2 : y ≤ 2 * x) (hP : P ≤ x + y) (hl : |l| = P)
    (hu : u = y ∨ u = -y) (hv : v = x ∨ v = -x) :
    |(x / y) ^ s * (l - u) - (y / x) ^ s * (l - v)| ≤ 16 * |v - u| := by
  obtain ⟨hA, hB⟩ := AB_bounds hs hx hy h1 h2
  have hW := wt_diff_le hs hx hy h1 h2 hP
  set w₁ := (x / y) ^ s
  set w₂ := (y / x) ^ s
  have hxyd : |x - y| ≤ |v - u| := by
    have hxy0 : 0 < x + y := by positivity
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
    · rw [show -x - y = -(x + y) by ring, abs_neg, abs_of_pos hxy0, abs_le]
      constructor <;> linarith
    · rw [show x - -y = x + y by ring, abs_of_pos hxy0, abs_le]
      constructor <;> linarith
    · rw [show -x - -y = -(x - y) by ring, abs_neg]
  have hR : |w₁ * u - w₂ * v| ≤ 4 * |v - u| := by
    have hxy0 : 0 < x + y := by positivity
    have hw0 : 0 ≤ w₁ * y + w₂ * x := by positivity
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
    · exact hA
    · rw [show w₁ * y - w₂ * -x = w₁ * y + w₂ * x by ring, abs_of_nonneg hw0,
        show -x - y = -(x + y) by ring, abs_neg, abs_of_pos hxy0]
      exact hB
    · rw [show w₁ * -y - w₂ * x = -(w₁ * y + w₂ * x) by ring, abs_neg, abs_of_nonneg hw0,
        show x - -y = x + y by ring, abs_of_pos hxy0]
      exact hB
    · rw [show w₁ * -y - w₂ * -x = -(w₁ * y - w₂ * x) by ring, abs_neg,
        show -x - -y = -(x - y) by ring, abs_neg]
      exact hA
  have e : w₁ * (l - u) - w₂ * (l - v) = l * (w₁ - w₂) - (w₁ * u - w₂ * v) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, hl]
  linarith

end OVNS.Quant.Metric

end
