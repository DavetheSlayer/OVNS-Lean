import OddViscousNS.Quant.Joint.Metric.Positive

/-!
# The block bounds of the signed metric at weight two (step J5, pilot)

The entry bounds behind every kernel of the signed metric: the physical edge `|L_uv| ≤ C U^{s+1}
V^{−s} f` and the first correction `|X₁_uv(h)| ≤ (C/q) |h_p| [(U/V)^s + (V/U)^s]` of LOCAL95 §1, eq.
(L), (X); the heat ratio; the kernels (A), (B) of LOCAL95 §3 and eq. (15) of Body 12.

## The Hermitian numerator on a block
`inner_X1b` is the block form of the Hermitian pairing, at every weight: on the helical channel
`(a, b, c)`, with `l = aP`, `u = bQ`, `v = cK`, the two edges of `X₁` carry the same triple product
`T`, with the coefficient `(K/Q)^s (l − u) − (Q/K)^s (l − v)`.  At `s = 2` this is
`(v − u) [l(v+u)(v²+u²) − uv(v²+uv+u²)]/(K²Q²)`, the TeX numerator, and `v − u` is absorbed by the
resolvent at the price `1/q` (`X1b_coeff_le`).  The eight channels are paid one by one, as in
`H1/Metric.lean`, `H2/Bounds.lean`, so the paired Schur lemma of Body 12 §2 is not used: it costs a
constant factor.  `H2/Bounds.lean` has the same numerator on a triad of fields (`metric_triad_le`);
here it is an operator bound on `V3`, which is what the composition `X₁ 𝓛` needs.

## The kernels
`norm_X2b_two_le`: both rootings with their outer heat, `(C/q) (M/Σ) f_a g_b [L²/J² + 2M⁴/(L²J²) +
J²/L²]`, the bracket of Body 12 (15).  `norm_Zb_two_le`: the merged leaf.  The envelope lemmas
`kerA_le`, `kerB_le`, `bracket₂_le`, `heat_*` are elementary (LOCAL95 §§3–4; Body 12 §7; NEW378).
-/

open scoped ComplexConjugate

open OVNS.Quant.H2 (num2 wb wb_nonneg abs_num2_le norm_metSym_mul_le)

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. Operator norms of the edges -/

lemma norm_helL_le (a : Sgn) (k : Mode) : ‖helL a k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using norm_hel_le a k v

/-- The edge of a bounded multiplier: `‖blk m p k j v‖ ≤ 8 |k| ‖v‖` ("each physical transport term
is bounded by `U |S_p| |F_v|`", LOCAL95 §2: the vertex sees the output frequency on transverse
inputs). -/
lemma norm_blk_le {m : Mult} (hm : m.Bdd) {p k j : Mode} (hk : p + j = k) (v : V3) :
    ‖blk m p k j v‖ ≤ 8 * absk k * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := absk_nonneg k; positivity) fun w => ?_
  rw [blk_apply]
  set E := absk k * ‖v‖ * ‖w‖ with hE
  have hterm : ∀ a b c, ‖m a b c p j • hel c k (vert p j (hel a p v) (hel b j w))‖ ≤ E := by
    intro a b c
    rw [norm_smul]
    have h1 : ‖hel c k (vert p j (hel a p v) (hel b j w))‖ ≤
        absk (p + j) * (‖hel a p v‖ * ‖hel b j w‖) :=
      (norm_hel_le _ _ _).trans (norm_vert_le₂ p j (dotM_hel a p v) (dotM_hel b j w))
    have h2 : ‖hel a p v‖ * ‖hel b j w‖ ≤ ‖v‖ * ‖w‖ :=
      mul_le_mul (norm_hel_le _ _ _) (norm_hel_le _ _ _) (norm_nonneg _) (norm_nonneg _)
    rw [hk] at h1
    calc ‖m a b c p j‖ * ‖hel c k (vert p j (hel a p v) (hel b j w))‖
        ≤ 1 * ‖hel c k (vert p j (hel a p v) (hel b j w))‖ :=
          mul_le_mul_of_nonneg_right (hm a b c p j) (norm_nonneg _)
      _ ≤ absk k * (‖v‖ * ‖w‖) := by
          rw [one_mul]
          exact h1.trans (mul_le_mul_of_nonneg_left h2 (absk_nonneg k))
      _ = E := by rw [hE]; ring
  refine (norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
    norm_sum_le_of_le _ fun c _ => hterm a b c).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, hE]
  push_cast
  ring

lemma wt_nonneg (s : ℕ) (k j : Mode) : 0 ≤ wt s k j :=
  pow_nonneg (div_nonneg (absk_nonneg _) (absk_nonneg _)) _

/-- `(K/J)² = K²/J²`. -/
lemma wt_two (k j : Mode) : wt 2 k j = absSq k / absSq j := by
  rw [wt, div_pow, absk_sq, absk_sq]

/-- **The physical edge** (LOCAL95 eq. (L)): `‖𝓛_s‖_{kj} ≤ 16 (K/J)^s K ‖v‖`. -/
lemma norm_Lb_le (s : ℕ) (τ : ℝ) {p k j : Mode} (hk : p + j = k) (v : V3) :
    ‖Lb s τ p k j v‖ ≤ 16 * wt s k j * absk k * ‖v‖ := by
  have hw := wt_nonneg s k j
  rw [Lb, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc 2 * wt s k j * ‖blk (phaseM τ) p k j v‖
      ≤ 2 * wt s k j * (8 * absk k * ‖v‖) :=
        mul_le_mul_of_nonneg_left (norm_blk_le (phaseM_bdd τ) hk v) (by positivity)
    _ = _ := by ring

/-- The adjoint edge. -/
lemma norm_Lad_le (s : ℕ) (τ : ℝ) {p k j : Mode} (hk : p + j = k) (v : V3) :
    ‖Lad s τ p k j v‖ ≤ 16 * wt s j k * absk j * ‖v‖ := by
  have e : -p + k = j := by rw [← hk]; abel
  rw [Lad, LinearIsometryEquiv.norm_map]
  simpa only [norm_conjV] using norm_Lb_le s τ e (conjV v)

/-! ### B. The Hermitian numerator -/

/-- Conjugation of a triple product. -/
private lemma conj_bd_cross (x y z : V3) :
    conj (bd (conjV x) (cross (conjV y) z)) = bd x (cross y (conjV z)) := by
  simp only [bd, cross_apply_zero, cross_apply_one, cross_apply_two, conjV_apply, map_add, map_sub,
    map_mul, Complex.conj_conj]

/-- Antisymmetry of the triple product in its outer slots. -/
private lemma bd_cross_swap (x y z : V3) : bd x (cross y z) = -bd z (cross y x) := by
  simp only [bd, cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

/-- The vertex against an arbitrary test vector, on helical inputs. -/
private lemma inner_hel_vert (Z X Y : V3) (a b c : Sgn) {p q k : Mode} (hk : p + q = k)
    (hk0 : k ≠ 0) :
    inner ℂ Z (hel c k (vert p q (hel a p X) (hel b q Y))) =
      (((sg a * absk p - sg b * absk q) / 2 : ℝ) : ℂ) *
        bd (conjV (hel c k Z)) (cross (hel a p X) (hel b q Y)) := by
  subst hk
  have hC : dotM (conjV (hel c (p + q) Z)) (p + q) = 0 := by
    rw [conjV_hel]
    exact dotM_hel_neg c _ _
  rw [inner_hel_right, inner_eq_bd, vert_hel, bd_smul_right, bd_leray hk0 hC]

/-- The triple product of the channel `(a, b, c)`. -/
def elt (a b c : Sgn) (p k j : Mode) (v w Z : V3) : ℂ :=
  bd (conjV (hel c k Z)) (cross (hel a p v) (hel b j w))

lemma norm_elt_le (a b c : Sgn) (p k j : Mode) (v w Z : V3) :
    ‖elt a b c p k j v w Z‖ ≤ ‖v‖ * ‖w‖ * ‖Z‖ := by
  unfold elt
  refine (norm_bd_le _ _).trans ?_
  rw [norm_conjV]
  calc ‖hel c k Z‖ * ‖cross (hel a p v) (hel b j w)‖
      ≤ ‖Z‖ * (‖v‖ * ‖w‖) :=
        mul_le_mul (norm_hel_le _ _ _) ((norm_cross_le _ _).trans (mul_le_mul (norm_hel_le _ _ _)
          (norm_hel_le _ _ _) (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

/-- The reverse edge `k → j` through `conj v`, conjugated: the same triple product. -/
private lemma conj_inner_rev (w Z v : V3) (a b c : Sgn) {p j k : Mode} (hk : p + j = k)
    (hj : j ≠ 0) :
    conj (inner ℂ w (hel b j (vert (-p) k (hel a (-p) (conjV v)) (hel c k Z)))) =
      -(((sg a * absk p - sg c * absk k) / 2 : ℝ) : ℂ) * elt a b c p k j v w Z := by
  have e : -p + k = j := by rw [← hk]; abel
  have h := inner_hel_vert w (conjV v) Z a c b e hj
  rw [absk_neg, ← conjV_hel] at h
  rw [← conjV_hel, h, map_mul, Complex.conj_ofReal, conj_bd_cross, bd_cross_swap]
  unfold elt
  ring

/-- The reversed edge has the opposite phase. -/
private lemma Phi_flip (a b c : Sgn) {p : Mode} (hp : p 2 = 0) (q : Mode) :
    Phi a c b (-p) (p + q) = -Phi a b c p q := by
  have e : -p + (p + q) = q := by abel
  simp only [Phi, e, lam_neg, lam_slow hp]
  ring

/-- The reversed edge has the same three-leg heat. -/
private lemma triHeat_flip (p q : Mode) : triHeat (-p) (p + q) = triHeat p q := by
  have e : -p + (p + q) = q := by abel
  simp only [triHeat, e, absSq_neg]
  ring

/-- The reversed edge has the same mask. -/
private lemma slowFast_flip (a b c : Sgn) (p q : Mode) :
    SlowFast a c b (-p) (p + q) ↔ SlowFast a b c p q := by
  unfold SlowFast
  by_cases hp : p 2 = 0
  · rw [Phi_flip a b c hp q, neg_ne_zero]
    simp [hp]
  · simp [hp]

/-- `m(-δ) = conj m(δ)` for the `X₁` symbol, on a slow leg. -/
private lemma metSym_flip (r τ : ℝ) (a b c : Sgn) {p : Mode} (hp : p 2 = 0) (q : Mode) :
    conj (metSym r τ a c b (-p) (p + q)) = metSym r τ a b c p q := by
  have hph : conj (phaseM τ a c b (-p) (p + q)) = phaseM τ a b c p q := by
    simp only [phaseM, Phi_flip a b c hp q]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [metSym, map_mul, hph, Quant.conj_resolv, triHeat_flip, Phi_flip a b c hp, mul_neg, neg_neg,
    metSym]

/-- The two edges of a triad carry the same multiplier, up to conjugation. -/
private lemma conj_metM_flip (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    conj (metM r τ a c b (-p) (p + q)) = metM r τ a b c p q := by
  unfold metM
  by_cases h : SlowFast a b c p q
  · rw [ite_eq_left ((slowFast_flip a b c p q).2 h), ite_eq_left h]
    exact metSym_flip r τ a b c h.1 q
  · rw [ite_eq_right (fun h' => h ((slowFast_flip a b c p q).1 h')), ite_eq_right h, map_zero]

/-- **The Hermitian pairing on a block**, at every weight: the two edges of `X₁` collect, on each
channel, into one triple product with the coefficient `(K/Q)^s (l − u) − (Q/K)^s (l − v)`. -/
theorem inner_X1b (s : ℕ) (r τ : ℝ) {p k j : Mode} (hk : p + j = k) (hj : j ≠ 0) (hk0 : k ≠ 0)
    (v w Z : V3) :
    inner ℂ Z (X1b s r τ p k j v w) = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, metM r τ a b c p j *
      (((wt s k j * (sg a * absk p - sg b * absk j) -
        wt s j k * (sg a * absk p - sg c * absk k) : ℝ) : ℂ) * elt a b c p k j v w Z) := by
  have e1 : inner ℂ Z (blk (metM r τ) p k j v w) = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      metM r τ a b c p j * ((((sg a * absk p - sg b * absk j) / 2 : ℝ) : ℂ) *
        elt a b c p k j v w Z) := by
    rw [blk_apply]
    simp only [inner_sum, inner_smul_right]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    rw [inner_hel_vert _ _ _ _ _ _ hk hk0]
    rfl
  have e2 : inner ℂ (blk (metM r τ) (-p) j k (conjV v) Z) w = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      metM r τ a b c p j * (-(((sg a * absk p - sg c * absk k) / 2 : ℝ) : ℂ) *
        elt a b c p k j v w Z) := by
    rw [← inner_conj_symm, blk_apply]
    simp only [inner_sum, inner_smul_right, map_sum, map_mul]
    rw [sum3_swap]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    subst hk
    rw [conj_metM_flip, conj_inner_rev _ _ _ _ _ _ rfl hj]
  simp only [X1b, add_apply, inner_add_right, ContinuousLinearMap.adjoint_inner_right, smul_apply,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, e1, e2, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  push_cast
  ring

/-- `wb ≤ (11/2)(K⁴ + Q⁴)` on a triangle: this is `H ≤ (11/2)(R² + R⁻²)` of Body 12 §6. -/
lemma wb_le_four {P Q K : ℝ} (hQ : 0 ≤ Q) (hK : 0 ≤ K) (h : P ≤ K + Q) :
    wb P Q K ≤ 11 / 2 * (K ^ 4 + Q ^ 4) := by
  set s := K ^ 2 + Q ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have h1 : P * (K + Q) ≤ 2 * s := by nlinarith [sq_nonneg (K - Q)]
  have h2 : K * Q ≤ s / 2 := by nlinarith [sq_nonneg (K - Q)]
  have h3 : K ^ 2 + K * Q + Q ^ 2 ≤ 3 / 2 * s := by linarith
  have h4 : P * (K + Q) * s ≤ 2 * s * s := mul_le_mul_of_nonneg_right h1 hs0
  have h5 : K * Q * (K ^ 2 + K * Q + Q ^ 2) ≤ s / 2 * (3 / 2 * s) :=
    mul_le_mul h2 h3 (by positivity) (by positivity)
  have h6 : s * s ≤ 2 * (K ^ 4 + Q ^ 4) := by nlinarith [sq_nonneg (K ^ 2 - Q ^ 2)]
  unfold wb
  rw [← hs]
  nlinarith

/-- **The cancellation at `s = 2`** (TeX eq. quant-metric): the coefficient of the channel
`(a, b, c)` in `inner_X1b` is `(v − u)` times the numerator over `K²Q²`, and `v − u` is absorbed by
the resolvent. -/
theorem X1b_coeff_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (a b c : Sgn) {p k j : Mode} (hk : p + j = k)
    (hp : p 2 = 0) (hj : j 2 ≠ 0) :
    ‖metM r τ a b c p j‖ * |wt 2 k j * (sg a * absk p - sg b * absk j) -
        wt 2 j k * (sg a * absk p - sg c * absk k)| ≤
      11 / 2 / |r| * (absSq k / absSq j + absSq j / absSq k) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hj0 : j ≠ 0 := fun h => hj (by simp [h])
  have hk2 : k 2 = j 2 := by rw [← hk]; simp [hp]
  have hk0 : k ≠ 0 := fun h => hj (by rw [← hk2, h]; rfl)
  have hJ : 0 < absSq j := by linarith [one_le_absSq hj0]
  have hK : 0 < absSq k := by linarith [one_le_absSq hk0]
  have hR : 0 ≤ 11 / 2 / |r| * (absSq k / absSq j + absSq j / absSq k) := by positivity
  unfold metM
  split_ifs with h
  swap
  · rw [norm_zero, zero_mul]
    exact hR
  rw [wt_two, wt_two]
  set l := sg a * absk p with hl
  set u := sg b * absk j with hu
  set v := sg c * absk k with hv
  have hu2 : u ^ 2 = absSq j := by
    rw [hu, mul_pow, show sg b ^ 2 = 1 by cases b <;> simp [sg], one_mul, absk_sq]
  have hv2 : v ^ 2 = absSq k := by
    rw [hv, mul_pow, show sg c ^ 2 = 1 by cases c <;> simp [sg], one_mul, absk_sq]
  have hsg : ∀ (e : Sgn) (x : ℝ), 0 ≤ x → |sg e * x| = x := fun e x hx => by
    rw [abs_mul, abs_of_nonneg hx]
    cases e <;> simp [sg]
  have hnum : absSq k / absSq j * (l - u) - absSq j / absSq k * (l - v) =
      (v - u) * num2 l u v / (absSq k * absSq j) := by
    rw [← hu2, ← hv2]
    have hu0 : u ≠ 0 := fun h0 => by
      rw [h0] at hu2
      simp at hu2
      exact hJ.ne hu2
    have hv0 : v ≠ 0 := fun h0 => by
      rw [h0] at hv2
      simp at hv2
      exact hK.ne hv2
    simp only [num2]
    field_simp
    ring
  have hP : absk p ≤ absk k + absk j := by
    have := absk_sub_le k j
    rwa [show k - j = p by rw [← hk]; abel] at this
  have hw := wb_le_four (absk_nonneg j) (absk_nonneg k) hP
  have hn := abs_num2_le (hsg a _ (absk_nonneg p)) (hsg b _ (absk_nonneg j))
    (hsg c _ (absk_nonneg k))
  have hm := norm_metSym_mul_le hr τ a b c hp hj h.2.2
  rw [hk] at hm
  have hprod : wb (absk p) (absk j) (absk k) / (absSq k * absSq j) ≤
      11 / 2 * (absSq k / absSq j + absSq j / absSq k) := by
    rw [div_le_iff₀ (by positivity)]
    have e1 : 11 / 2 * (absSq k / absSq j + absSq j / absSq k) * (absSq k * absSq j) =
        11 / 2 * (absSq k ^ 2 + absSq j ^ 2) := by
      field_simp
    rw [e1, ← absk_sq k, ← absk_sq j]
    calc _ ≤ _ := hw
      _ = _ := by ring
  rw [hnum, abs_div, abs_mul, abs_of_pos (by positivity : 0 < absSq k * absSq j)]
  set m := ‖metSym r τ a b c p j‖
  have hm0 : 0 ≤ m := norm_nonneg _
  calc m * (|v - u| * |num2 l u v| / (absSq k * absSq j))
      = (m * |v - u|) * (|num2 l u v| / (absSq k * absSq j)) := by ring
    _ ≤ (1 / |r|) * (wb (absk p) (absk j) (absk k) / (absSq k * absSq j)) :=
        mul_le_mul hm (div_le_div_of_nonneg_right hn (by positivity)) (by positivity)
          (by positivity)
    _ ≤ (1 / |r|) * (11 / 2 * (absSq k / absSq j + absSq j / absSq k)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

/-- From test vectors to the norm. -/
lemma norm_le_of_inner {x : V3} {B : ℝ} (hB : 0 ≤ B) (h : ∀ Z : V3, ‖inner ℂ Z x‖ ≤ B * ‖Z‖) :
    ‖x‖ ≤ B := by
  by_cases hx : x = 0
  · simpa [hx] using hB
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h1 := h x
  have h2 : ‖inner ℂ x x‖ = ‖x‖ * ‖x‖ := by
    rw [inner_self_eq_norm_sq_to_K, sq]
    simp
  rw [h2] at h1
  exact le_of_mul_le_mul_right h1 hpos

/-- **The first correction at weight two** (LOCAL95 eq. (X), Body 12 (11); the constant is `44`
against `11/2` because the eight channels are paid separately):
`‖X₁(v)_{kj}‖ ≤ (44/q) ‖v‖ [K²/J² + J²/K²]`, on a slow leaf and a fast input. -/
theorem norm_X1b_two_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {p k j : Mode} (hk : p + j = k)
    (hp : p 2 = 0) (hj : j 2 ≠ 0) (v : V3) :
    ‖X1b 2 r τ p k j v‖ ≤ 44 / |r| * ‖v‖ * (absSq k / absSq j + absSq j / absSq k) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hj0 : j ≠ 0 := fun h => hj (by simp [h])
  have hk2 : k 2 = j 2 := by rw [← hk]; simp [hp]
  have hk0 : k ≠ 0 := fun h => hj (by rw [← hk2, h]; rfl)
  have hJ : 0 ≤ absSq j := absSq_nonneg j
  have hK : 0 ≤ absSq k := absSq_nonneg k
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  refine norm_le_of_inner (by positivity) fun Z => ?_
  rw [inner_X1b 2 r τ hk hj0 hk0]
  set E := 11 / 2 / |r| * (absSq k / absSq j + absSq j / absSq k) * (‖v‖ * ‖w‖ * ‖Z‖) with hE
  have hterm : ∀ a b c, ‖metM r τ a b c p j *
      (((wt 2 k j * (sg a * absk p - sg b * absk j) -
        wt 2 j k * (sg a * absk p - sg c * absk k) : ℝ) : ℂ) * elt a b c p k j v w Z)‖ ≤ E := by
    intro a b c
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
    exact mul_le_mul (X1b_coeff_le hr τ a b c hk hp hj) (norm_elt_le _ _ _ _ _ _ _ _ _)
      (norm_nonneg _) (by positivity)
  refine (norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
    norm_sum_le_of_le _ fun c _ => hterm a b c).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, hE]
  push_cast
  ring

/-! ### C. The outer inverse and both rootings -/

/-- `‖H⁻¹ T‖ ≤ (4/H) ‖T‖`: "taking a norm majorant inside the exact heat integral yields `1/Σ`"
(Body 12 §7).  The four exterior channels are paid separately. -/
lemma norm_outerInv_le {H : ℝ} (hH : 0 < H) (r : ℝ) (l j : Mode) (T : V3 →L[ℂ] V3) :
    ‖outerInv r H l j T‖ ≤ 4 / H * ‖T‖ := by
  have hterm : ∀ c e, ‖resolv (-1) H (r * outerPhi c e l j) • (helL c l ∘L T ∘L helL e j)‖ ≤
      1 / H * ‖T‖ := by
    intro c e
    rw [norm_smul]
    have h1 : ‖helL c l ∘L T ∘L helL e j‖ ≤ ‖T‖ := by
      calc _ ≤ ‖helL c l‖ * ‖T ∘L helL e j‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * (‖T‖ * 1) := by
            refine mul_le_mul (norm_helL_le _ _) ?_ (norm_nonneg _) zero_le_one
            exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_left (norm_helL_le _ _) (norm_nonneg _))
        _ = ‖T‖ := by ring
    exact mul_le_mul (norm_resolv_le (Or.inr rfl) hH _) h1 (norm_nonneg _) (by positivity)
  refine (norm_sum_le_of_le _ fun c _ => norm_sum_le_of_le _ fun e _ => hterm c e).trans
    (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

/-- The bracket of Body 12 (15) at weight two, in the squared lengths. -/
def Br (L M J : ℝ) : ℝ := L / J + 2 * M ^ 2 / (L * J) + J / L

lemma heat4_pos {l j : Mode} (hj : j ≠ 0) (a b : Mode) : 0 < heat4 l j a b := by
  have := one_le_absSq hj
  have := absSq_nonneg l
  have := absSq_nonneg a
  have := absSq_nonneg b
  unfold heat4
  linarith

/-- The three fast labels of a two-leaf block. -/
lemma fast_labels {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    l ≠ 0 ∧ l - a ≠ 0 ∧ l - a - b ≠ 0 := by
  have h1 : (l - a - b) 2 = (l - a) 2 := by simp [hb]
  have h2 : (l - a) 2 = l 2 := by simp [ha]
  refine ⟨fun h => hj ?_, fun h => hj ?_, fun h => hj ?_⟩
  · rw [h1, h2, h]; rfl
  · rw [h1, h]; rfl
  · rw [h]; rfl

/-- **Both rootings**, with their outer heat (Body 12 (15), before enlarging `M/Σ`):
`‖X₂(f,g)_{lj}‖ ≤ (2816/q) (M/Σ) ‖f_a‖ ‖g_b‖ [L²/J² + 2M⁴/(L²J²) + J²/L²]`. -/
theorem norm_X2b_two_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖X2b 2 r τ f g l a b‖ ≤ 2816 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) *
      (‖f a‖ * ‖g b‖) * Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hm2 : (l - a) 2 ≠ 0 := fun h => hj (by simp only [Pi.sub_apply] at h ⊢; simpa [hb] using h)
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absSq l := by linarith [one_le_absSq hl0]
  have hM : 0 < absSq (l - a) := by linarith [one_le_absSq hm0]
  have hJ : 0 < absSq (l - a - b) := by linarith [one_le_absSq hj0]
  have hH := heat4_pos (l := l) hj0 a b
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  have h1 := norm_X1b_two_le hr τ e1 ha hm2 (f a)
  have h2 := norm_Lb_le 2 τ e2 (g b)
  have h3 := norm_Lad_le 2 τ e1 (f a)
  have h4 := norm_X1b_two_le hr τ e2 hb hj (g b)
  rw [wt_two] at h2 h3
  set L := absSq l
  set M := absSq (l - a)
  set J := absSq (l - a - b)
  set M₁ := absk (l - a) with hM₁
  have hM₁0 : 0 ≤ M₁ := absk_nonneg _
  have ha0 := norm_nonneg (f a)
  have hb0 := norm_nonneg (g b)
  have hT : ‖twoRoot 2 r τ f g l a b‖ ≤ 704 / |r| * M₁ * (‖f a‖ * ‖g b‖) * Br L M J := by
    have ht1 : ‖X1b 2 r τ a l (l - a) (f a) ∘L Lb 2 τ b (l - a) (l - a - b) (g b)‖ ≤
        44 / |r| * ‖f a‖ * (L / M + M / L) * (16 * (M / J) * M₁ * ‖g b‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
    have ht2 : ‖Lad 2 τ a l (l - a) (f a) ∘L X1b 2 r τ b (l - a) (l - a - b) (g b)‖ ≤
        16 * (M / L) * M₁ * ‖f a‖ * (44 / |r| * ‖g b‖ * (M / J + J / M)) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul h3 h4 (norm_nonneg _) (by positivity))
    refine (norm_add_le _ _).trans ((add_le_add ht1 ht2).trans (le_of_eq ?_))
    simp only [Br]
    field_simp
    ring
  have hB : 0 ≤ Br L M J := by simp only [Br]; positivity
  calc ‖X2b 2 r τ f g l a b‖ ≤ 4 / heat4 l (l - a - b) a b * ‖twoRoot 2 r τ f g l a b‖ :=
        norm_outerInv_le hH r l _ _
    _ ≤ 4 / heat4 l (l - a - b) a b * (704 / |r| * M₁ * (‖f a‖ * ‖g b‖) * Br L M J) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = _ := by ring

/-- The slow product edge: `|B_p| ≤ C |p| f_a f_b`, the merged output derivative (LOCAL95 §6 (V)).
-/
lemma norm_slowV_le (a b : Mode) (v w : V3) :
    ‖slowV a b v w‖ ≤ 8 * absk (a + b) * ‖v‖ * ‖w‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_blk_le resM_bdd rfl v) (norm_nonneg _))

/-- **The merged block**: `‖Z(f,g)_{lk}‖ ≤ (1408/q) (P/Σ) ‖f_a‖ ‖g_b‖ [L²/K² + K²/L²]`, with
`P = |a + b|` from the merged output, and the outer heat of the two ancestors (LOCAL95 §6). -/
theorem norm_Zb_two_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖Zb 2 r τ f g l a b‖ ≤ 1408 / |r| * (absk (a + b) / heat4 l (l - a - b) a b) *
      (‖f a‖ * ‖g b‖) * (absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 ≤ absSq l := absSq_nonneg l
  have hJ : 0 ≤ absSq (l - a - b) := absSq_nonneg _
  have hH := heat4_pos (l := l) hj0 a b
  have e1 : (a + b) + (l - a - b) = l := by abel
  have hab : (a + b) 2 = 0 := by simp [ha, hb]
  have h1 := norm_X1b_two_le hr τ e1 hab hj (slowV a b (f a) (g b))
  have h2 := norm_slowV_le a b (f a) (g b)
  have hP := absk_nonneg (a + b)
  have hab0 := norm_nonneg (f a)
  have hb0 := norm_nonneg (g b)
  set R := absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l with hR
  have hR0 : 0 ≤ R := by positivity
  calc ‖Zb 2 r τ f g l a b‖
      ≤ 4 / heat4 l (l - a - b) a b * ‖X1b 2 r τ (a + b) l (l - a - b) (slowV a b (f a) (g b))‖ :=
        norm_outerInv_le hH r l _ _
    _ ≤ 4 / heat4 l (l - a - b) a b * (44 / |r| * (8 * absk (a + b) * ‖f a‖ * ‖g b‖) * R) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
        gcongr
    _ = _ := by ring

/-! ### D. The triangle envelopes -/

lemma absSq_le₂ {k u v : Mode} (h : k = u + v) : absSq k ≤ 2 * (absSq u + absSq v) := by
  have hi : ∀ i, (k i : ℝ) ^ 2 ≤ 2 * ((u i : ℝ) ^ 2 + (v i : ℝ) ^ 2) := fun i => by
    subst h
    simp only [Pi.add_apply, Int.cast_add]
    nlinarith [sq_nonneg ((u i : ℝ) - v i)]
  calc absSq k ≤ ∑ i, 2 * ((u i : ℝ) ^ 2 + (v i : ℝ) ^ 2) := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp only [absSq, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma absSq_le₃ {k u v w : Mode} (h : k = u + v + w) :
    absSq k ≤ 3 * (absSq u + absSq v + absSq w) := by
  have hi : ∀ i, (k i : ℝ) ^ 2 ≤ 3 * ((u i : ℝ) ^ 2 + (v i : ℝ) ^ 2 + (w i : ℝ) ^ 2) := fun i => by
    subst h
    simp only [Pi.add_apply, Int.cast_add]
    nlinarith [sq_nonneg ((u i : ℝ) - v i), sq_nonneg ((u i : ℝ) - w i),
      sq_nonneg ((v i : ℝ) - w i)]
  calc absSq k ≤ ∑ i, 3 * ((u i : ℝ) ^ 2 + (v i : ℝ) ^ 2 + (w i : ℝ) ^ 2) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp only [absSq, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma absSq_le₄ {k u v w t : Mode} (h : k = u + v + w + t) :
    absSq k ≤ 4 * (absSq u + absSq v + absSq w + absSq t) := by
  have hi : ∀ i, (k i : ℝ) ^ 2 ≤
      4 * ((u i : ℝ) ^ 2 + (v i : ℝ) ^ 2 + (w i : ℝ) ^ 2 + (t i : ℝ) ^ 2) := fun i => by
    subst h
    simp only [Pi.add_apply, Int.cast_add]
    nlinarith [sq_nonneg ((u i : ℝ) - v i), sq_nonneg ((u i : ℝ) - w i),
      sq_nonneg ((u i : ℝ) - t i), sq_nonneg ((v i : ℝ) - w i), sq_nonneg ((v i : ℝ) - t i),
      sq_nonneg ((w i : ℝ) - t i)]
  calc absSq k ≤ ∑ i, 4 * ((u i : ℝ) ^ 2 + (v i : ℝ) ^ 2 + (w i : ℝ) ^ 2 + (t i : ℝ) ^ 2) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp only [absSq, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- `xy ≤ (x² + y²)/2` for the lengths of two modes. -/
lemma absk_mul_absk_le (u v : Mode) : absk u * absk v ≤ (absSq u + absSq v) / 2 := by
  rw [← absk_sq u, ← absk_sq v]
  nlinarith [sq_nonneg (absk u - absk v)]

/-- `E_2^z` as a polynomial over `L²J²`. -/
lemma E3_eq {L J A B C : ℝ} (hL : 0 < L) (hJ : 0 < J) :
    1 + (A + B + C) / L + (A + B + C) / J + (A * B + A * C + B * C) / (L * J) =
      (L * J + (A + B + C) * (L + J) + (A * B + A * C + B * C)) / (L * J) := by
  field_simp
  ring

/-- **The scalar domination** of the fast-chain and `ZL` brackets by `E_2^z`, with only distinct
ancestral slots (LOCAL95 §4; NEW378): `L²/J² ≤ 4E`, `M⁴/(L²J²) ≤ 6E`, `K⁴/(L²J²) ≤ 6E`, from the
triangles along the path `l → m → k → j`. -/
lemma kerA_le {L M K J A B C : ℝ} (hL : 0 < L) (hJ : 0 < J) (hM : 0 ≤ M) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (h1 : L ≤ 4 * (J + A + B + C)) (h2 : M ≤ 2 * (L + A))
    (h3 : M ≤ 3 * (J + B + C)) (h4 : K ≤ 3 * (L + A + B)) (h5 : K ≤ 2 * (J + C)) :
    L / J + 2 * M ^ 2 / (L * J) + K ^ 2 / (L * J) ≤
      22 * (1 + (A + B + C) / L + (A + B + C) / J + (A * B + A * C + B * C) / (L * J)) := by
  rw [E3_eq hL hJ]
  set P := L * J + (A + B + C) * (L + J) + (A * B + A * C + B * C) with hP
  have hLJ : 0 < L * J := mul_pos hL hJ
  have e : L / J + 2 * M ^ 2 / (L * J) + K ^ 2 / (L * J) =
      (L ^ 2 + 2 * M ^ 2 + K ^ 2) / (L * J) := by
    field_simp
  rw [e, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hLJ.le
  have a1 : L ^ 2 ≤ 4 * P := by
    have := mul_le_mul_of_nonneg_left h1 hL.le
    nlinarith [mul_nonneg hA hJ.le, mul_nonneg hB hJ.le, mul_nonneg hC hJ.le, mul_nonneg hA hB,
      mul_nonneg hA hC, mul_nonneg hB hC]
  have a2 : M ^ 2 ≤ 6 * P := by
    have := mul_le_mul h2 h3 hM (by positivity)
    nlinarith [mul_nonneg hA hL.le, mul_nonneg hA hJ.le, mul_nonneg hB hL.le, mul_nonneg hB hJ.le,
      mul_nonneg hC hL.le, mul_nonneg hC hJ.le, mul_nonneg hA hB, mul_nonneg hA hC,
      mul_nonneg hB hC]
  have a3 : K ^ 2 ≤ 6 * P := by
    have := mul_le_mul h4 h5 hK (by positivity)
    nlinarith [mul_nonneg hA hL.le, mul_nonneg hA hJ.le, mul_nonneg hB hL.le, mul_nonneg hB hJ.le,
      mul_nonneg hC hL.le, mul_nonneg hC hJ.le, mul_nonneg hA hB, mul_nonneg hA hC,
      mul_nonneg hB hC]
  linarith

/-- The `ZL` bracket (LOCAL95 §6). -/
lemma kerB_le {L K J A B C : ℝ} (hL : 0 < L) (hJ : 0 < J) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (h1 : L ≤ 4 * (J + A + B + C)) (h4 : K ≤ 3 * (L + A + B))
    (h5 : K ≤ 2 * (J + C)) :
    L / J + K ^ 2 / (L * J) ≤
      10 * (1 + (A + B + C) / L + (A + B + C) / J + (A * B + A * C + B * C) / (L * J)) := by
  rw [E3_eq hL hJ]
  set P := L * J + (A + B + C) * (L + J) + (A * B + A * C + B * C) with hP
  have hLJ : 0 < L * J := mul_pos hL hJ
  have e : L / J + K ^ 2 / (L * J) = (L ^ 2 + K ^ 2) / (L * J) := by
    field_simp
  rw [e, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hLJ.le
  have a1 : L ^ 2 ≤ 4 * P := by
    have := mul_le_mul_of_nonneg_left h1 hL.le
    nlinarith [mul_nonneg hA hJ.le, mul_nonneg hB hJ.le, mul_nonneg hC hJ.le, mul_nonneg hA hB,
      mul_nonneg hA hC, mul_nonneg hB hC]
  have a3 : K ^ 2 ≤ 6 * P := by
    have := mul_le_mul h4 h5 hK (by positivity)
    nlinarith [mul_nonneg hA hL.le, mul_nonneg hA hJ.le, mul_nonneg hB hL.le, mul_nonneg hB hJ.le,
      mul_nonneg hC hL.le, mul_nonneg hC hJ.le, mul_nonneg hA hB, mul_nonneg hA hC,
      mul_nonneg hB hC]
  linarith

/-- The bracket of Body 12 (15) against `E₂`: `≤ 14 E₂` (Body 12 §7: "the bracket at `s2` is
`≤ 14 E₂`"). -/
lemma bracket₂_le {L M J A B : ℝ} (hL : 0 < L) (hJ : 0 < J) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : L ≤ 3 * (J + A + B)) (h2 : J ≤ 3 * (L + A + B)) (h3 : M ≤ 2 * (L + A))
    (h4 : M ≤ 2 * (J + B)) :
    Br L M J ≤ 14 * (1 + (A + B) / L + (A + B) / J + A * B / (L * J)) := by
  have e1 : 1 + (A + B) / L + (A + B) / J + A * B / (L * J) =
      (L * J + (A + B) * (L + J) + A * B) / (L * J) := by
    field_simp
    ring
  have e2 : Br L M J = (L ^ 2 + 2 * M ^ 2 + J ^ 2) / (L * J) := by
    simp only [Br]
    field_simp
  rw [e1, e2, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (mul_pos hL hJ).le
  set P := L * J + (A + B) * (L + J) + A * B with hP
  have a1 : L ^ 2 ≤ 3 * P := by
    have := mul_le_mul_of_nonneg_left h1 hL.le
    nlinarith [mul_nonneg hA hJ.le, mul_nonneg hB hJ.le, mul_nonneg hA hB]
  have a2 : J ^ 2 ≤ 3 * P := by
    have := mul_le_mul_of_nonneg_left h2 hJ.le
    nlinarith [mul_nonneg hA hL.le, mul_nonneg hB hL.le, mul_nonneg hA hB]
  have a3 : M ^ 2 ≤ 4 * P := by
    have := mul_le_mul h3 h4 hM (by positivity)
    nlinarith [mul_nonneg hA hL.le, mul_nonneg hA hJ.le, mul_nonneg hB hL.le, mul_nonneg hB hJ.le,
      mul_nonneg hA hB]
  linarith

/-- The triangles of two leaves. -/
lemma two_leaf_triangles (l a b : Mode) :
    absSq l ≤ 3 * (absSq (l - a - b) + absSq a + absSq b) ∧
      absSq (l - a - b) ≤ 3 * (absSq l + absSq a + absSq b) ∧
      absSq (l - a) ≤ 2 * (absSq l + absSq a) ∧
      absSq (l - a) ≤ 2 * (absSq (l - a - b) + absSq b) := by
  refine ⟨absSq_le₃ (by abel), ?_, ?_, absSq_le₂ (by abel)⟩
  · have := absSq_le₃ (k := l - a - b) (u := l) (v := -a) (w := -b) (by abel)
    rwa [absSq_neg, absSq_neg] at this
  · have := absSq_le₂ (k := l - a) (u := l) (v := -a) (by abel)
    rwa [absSq_neg] at this

/-- `E₂` is nonnegative. -/
lemma E2_nonneg (x : I3) : 0 ≤ E2 x := by
  have h1 := absSq_nonneg x.1
  have h2 := absSq_nonneg x.2.1
  have h3 := absSq_nonneg x.2.2
  have h4 := absSq_nonneg (inJ₂ x)
  unfold E2
  positivity

/-- `E_2^z` is nonnegative. -/
lemma E3_nonneg (x : I4) : 0 ≤ E3 x := by
  have h1 := absSq_nonneg x.1
  have h2 := absSq_nonneg x.2.1
  have h3 := absSq_nonneg x.2.2.1
  have h5 := absSq_nonneg x.2.2.2
  have h4 := absSq_nonneg (inJ x)
  unfold E3
  positivity

/-- **The two-leaf kernel**: `‖X₂(f,g)_{lj}‖ ≤ (C/q) (M/Σ) f_a g_b E₂`. -/
theorem norm_X2b_E2_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖X2b 2 r τ f g l a b‖ ≤ 39424 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) *
      (‖f a‖ * ‖g b‖) * E2 (l, a, b) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hL : 0 < absSq l := by linarith [one_le_absSq hl0]
  have hJ : 0 < absSq (l - a - b) := by linarith [one_le_absSq hj0]
  obtain ⟨t1, t2, t3, t4⟩ := two_leaf_triangles l a b
  have hBr := bracket₂_le hL hJ (absSq_nonneg (l - a)) (absSq_nonneg a) (absSq_nonneg b) t1 t2 t3 t4
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hH := heat4_pos (l := l) hj0 a b
  have hM := absk_nonneg (l - a)
  have hfg : 0 ≤ ‖f a‖ * ‖g b‖ := by positivity
  refine (norm_X2b_two_le hr τ f g ha hb hj).trans ?_
  calc 2816 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) * (‖f a‖ * ‖g b‖) *
        Br (absSq l) (absSq (l - a)) (absSq (l - a - b))
      ≤ 2816 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) * (‖f a‖ * ‖g b‖) *
        (14 * E2 (l, a, b)) := mul_le_mul_of_nonneg_left hBr (by positivity)
    _ = _ := by ring

/-- `(M/Σ) L ≤ 2`: the output half (Body 12 §7: `LM/Σ ≤ 5/4`). -/
lemma half_ratio_le (l a b : Mode) :
    absk l * (absk (l - a) / heat4 l (l - a - b) a b) ≤ 2 := by
  have hH0 : 0 ≤ heat4 l (l - a - b) a b := by
    have := absSq_nonneg l
    have := absSq_nonneg a
    have := absSq_nonneg b
    have := absSq_nonneg (l - a - b)
    unfold heat4
    linarith
  rcases hH0.eq_or_lt with hH | hH
  · rw [← hH]
    simp
  rw [← mul_div_assoc, div_le_iff₀ hH]
  have h1 := absk_mul_absk_le l (l - a)
  have h2 := (two_leaf_triangles l a b).2.2.1
  have h3 := absSq_nonneg (l - a - b)
  have h4 := absSq_nonneg b
  have h5 := absSq_nonneg l
  have h6 := absSq_nonneg a
  unfold heat4
  linarith

/-- `(M/Σ) U ≤ 1`, `U = |a|`: the replaced leaf of `D_S X₂` in the first slot (Body 12 §7:
"`R M ≤ Σ`"). -/
lemma leaf_ratio_left_le {l a b : Mode} (hj : l - a - b ≠ 0) :
    absk a * (absk (l - a) / heat4 l (l - a - b) a b) ≤ 1 := by
  have hH := heat4_pos (l := l) hj a b
  rw [← mul_div_assoc, div_le_iff₀ hH]
  have h1 := absk_mul_absk_le a (l - a)
  have h2 := (two_leaf_triangles l a b).2.2.2
  have h3 := absSq_nonneg (l - a - b)
  have h4 := absSq_nonneg b
  have h5 := absSq_nonneg l
  have h6 := absSq_nonneg a
  unfold heat4
  linarith

/-- `(M/Σ) V ≤ 1`, `V = |b|`: the replaced leaf in the second slot. -/
lemma leaf_ratio_right_le {l a b : Mode} (hj : l - a - b ≠ 0) :
    absk b * (absk (l - a) / heat4 l (l - a - b) a b) ≤ 1 := by
  have hH := heat4_pos (l := l) hj a b
  rw [← mul_div_assoc, div_le_iff₀ hH]
  have h1 := absk_mul_absk_le b (l - a)
  have h2 := (two_leaf_triangles l a b).2.2.1
  have h3 := absSq_nonneg (l - a - b)
  have h4 := absSq_nonneg b
  have h5 := absSq_nonneg l
  have h6 := absSq_nonneg a
  unfold heat4
  linarith

/-- The intermediate of the last edge, against the heat: `M K ≤ Σ` (LOCAL95 §2: "the heat ratio is
bounded by one"). -/
lemma chain_ratio_le {l a b : Mode} (hj : l - a - b ≠ 0) :
    absk (l - a) * absk (l - a - b) ≤ heat4 l (l - a - b) a b := by
  have h1 := absk_mul_absk_le (l - a) (l - a - b)
  have h2 := (two_leaf_triangles l a b).2.2.1
  have h3 := absSq_nonneg (l - a - b)
  have h4 := absSq_nonneg b
  have h5 := absSq_nonneg l
  have h6 := absSq_nonneg a
  have _ := hj
  unfold heat4
  linarith

/-- The merged leaf, against the heat: `P K ≤ Σ` (LOCAL95 §6). -/
lemma merged_ratio_le (l a b : Mode) :
    absk (a + b) * absk (l - a - b) ≤ heat4 l (l - a - b) a b := by
  have h1 := absk_mul_absk_le (a + b) (l - a - b)
  have h2 := absSq_le₂ (k := a + b) rfl
  have h3 := absSq_nonneg (l - a - b)
  have h5 := absSq_nonneg l
  unfold heat4
  linarith

/-- **The cubic kernel** (LOCAL95 §§3–6, NEW378): on three slow leaves and a fast input, the block
of `(X₂ + Z) 𝓛` at weight two is `≤ (C/q) f_a g_b h_c E_2^z`.  This is the whole undifferentiated
part, both rootings, the merged `Z` and the last physical edge, resonant edges included. -/
theorem norm_YLb_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g h : Field) {x : I4} (ha : x.2.1 2 = 0)
    (hb : x.2.2.1 2 = 0) (hc : x.2.2.2 2 = 0) (hj : inJ x 2 ≠ 0) :
    ‖YLb 2 r τ f g h x‖ ≤
      2 ^ 21 / |r| * (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) * E3 x := by
  obtain ⟨l, a, b, c⟩ := x
  simp only at ha hb hc ⊢
  have hjj : (l - a - b - c) 2 ≠ 0 := hj
  have hk : (l - a - b) 2 ≠ 0 := fun h0 => hjj (by simp only [Pi.sub_apply] at h0 ⊢; simp [hc, h0])
  obtain ⟨hl0, hm0, hk0⟩ := fast_labels ha hb hk
  have hj0 : l - a - b - c ≠ 0 := fun h0 => hjj (by rw [h0]; rfl)
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absSq l := by linarith [one_le_absSq hl0]
  have hJ : 0 < absSq (l - a - b - c) := by linarith [one_le_absSq hj0]
  have hK : 0 < absSq (l - a - b) := by linarith [one_le_absSq hk0]
  have hH := heat4_pos (l := l) hk0 a b
  have e1 : c + (l - a - b - c) = l - a - b := by abel
  have h1 := norm_X2b_two_le hr τ f g ha hb hk
  have h2 := norm_Zb_two_le hr τ f g ha hb hk
  have h3 := norm_Lb_le 2 τ e1 (h c)
  rw [wt_two] at h3
  set A := absSq a
  set B := absSq b
  set C := absSq c
  set L2 := absSq l
  set M2 := absSq (l - a)
  set K2 := absSq (l - a - b)
  set J2 := absSq (l - a - b - c)
  set S4 := heat4 l (l - a - b) a b
  set M₁ := absk (l - a)
  set K₁ := absk (l - a - b)
  set P₁ := absk (a + b)
  have hA : 0 ≤ A := absSq_nonneg _
  have hB : 0 ≤ B := absSq_nonneg _
  have hC : 0 ≤ C := absSq_nonneg _
  have hM2 : 0 ≤ M2 := absSq_nonneg _
  have hM₁ : 0 ≤ M₁ := absk_nonneg _
  have hK₁ : 0 ≤ K₁ := absk_nonneg _
  have hP₁ : 0 ≤ P₁ := absk_nonneg _
  have t1 : L2 ≤ 4 * (J2 + A + B + C) := absSq_le₄ (by abel)
  have t2 : M2 ≤ 2 * (L2 + A) := (two_leaf_triangles l a b).2.2.1
  have t3 : M2 ≤ 3 * (J2 + B + C) := absSq_le₃ (by abel)
  have t4 : K2 ≤ 3 * (L2 + A + B) := by
    have := absSq_le₃ (k := l - a - b) (u := l) (v := -a) (w := -b) (by abel)
    rwa [absSq_neg, absSq_neg] at this
  have t5 : K2 ≤ 2 * (J2 + C) := absSq_le₂ (by abel)
  have hE : E3 (l, a, b, c) =
      1 + (A + B + C) / L2 + (A + B + C) / J2 + (A * B + A * C + B * C) / (L2 * J2) := rfl
  rw [hE]
  set E := 1 + (A + B + C) / L2 + (A + B + C) / J2 + (A * B + A * C + B * C) / (L2 * J2) with hEd
  have hE0 : 0 ≤ E := by positivity
  have hk1 := kerA_le hL hJ hM2 hK.le hA hB hC t1 t2 t3 t4 t5
  have hk2 := kerB_le hL hJ hK.le hA hB hC t1 t4 t5
  rw [← hEd] at hk1 hk2
  have hr1 : M₁ * K₁ / S4 ≤ 1 := (div_le_one hH).2 (chain_ratio_le hk0)
  have hr2 : P₁ * K₁ / S4 ≤ 1 := (div_le_one hH).2 (merged_ratio_le l a b)
  have hf0 := norm_nonneg (f a)
  have hg0 := norm_nonneg (g b)
  have hh0 := norm_nonneg (h c)
  have eK : Br L2 M2 K2 * (K2 / J2) = L2 / J2 + 2 * M2 ^ 2 / (L2 * J2) + K2 ^ 2 / (L2 * J2) := by
    simp only [Br]
    field_simp
  have eZ : (L2 / K2 + K2 / L2) * (K2 / J2) = L2 / J2 + K2 ^ 2 / (L2 * J2) := by
    field_simp
  have hBK : 0 ≤ Br L2 M2 K2 := by simp only [Br]; positivity
  have hRZ : 0 ≤ L2 / K2 + K2 / L2 := by positivity
  have hX : ‖X2b 2 r τ f g l a b‖ * ‖Lb 2 τ c (l - a - b) (l - a - b - c) (h c)‖ ≤
      2 ^ 16 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (22 * E) := by
    calc _ ≤ (2816 / |r| * (M₁ / S4) * (‖f a‖ * ‖g b‖) * Br L2 M2 K2) *
          (16 * (K2 / J2) * K₁ * ‖h c‖) := mul_le_mul h1 h3 (norm_nonneg _) (by positivity)
      _ = 45056 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (M₁ * K₁ / S4) *
            (Br L2 M2 K2 * (K2 / J2)) := by ring
      _ ≤ 45056 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * 1 * (22 * E) := by
          rw [eK]
          have hnn : 0 ≤ L2 / J2 + 2 * M2 ^ 2 / (L2 * J2) + K2 ^ 2 / (L2 * J2) := by positivity
          gcongr
      _ ≤ _ := by
          rw [mul_one]
          gcongr
          norm_num
  have hZ : ‖Zb 2 r τ f g l a b‖ * ‖Lb 2 τ c (l - a - b) (l - a - b - c) (h c)‖ ≤
      2 ^ 15 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (10 * E) := by
    calc _ ≤ (1408 / |r| * (P₁ / S4) * (‖f a‖ * ‖g b‖) * (L2 / K2 + K2 / L2)) *
          (16 * (K2 / J2) * K₁ * ‖h c‖) := mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
      _ = 22528 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (P₁ * K₁ / S4) *
            ((L2 / K2 + K2 / L2) * (K2 / J2)) := by ring
      _ ≤ 22528 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * 1 * (10 * E) := by
          rw [eZ]
          have hnn : 0 ≤ L2 / J2 + K2 ^ 2 / (L2 * J2) := by positivity
          gcongr
      _ ≤ _ := by
          rw [mul_one]
          gcongr
          norm_num
  have hcomp : ‖YLb 2 r τ f g h (l, a, b, c)‖ ≤
      (‖X2b 2 r τ f g l a b‖ + ‖Zb 2 r τ f g l a b‖) *
        ‖Lb 2 τ c (l - a - b) (l - a - b - c) (h c)‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
  refine hcomp.trans ?_
  rw [add_mul]
  refine (add_le_add hX hZ).trans ?_
  have hT : 0 ≤ (‖f a‖ * ‖g b‖ * ‖h c‖) * E / |r| := by positivity
  have e : 2 ^ 21 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * E -
      (2 ^ 16 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (22 * E) +
        2 ^ 15 / |r| * (‖f a‖ * ‖g b‖ * ‖h c‖) * (10 * E)) =
      (2 ^ 21 - 2 ^ 16 * 22 - 2 ^ 15 * 10) * ((‖f a‖ * ‖g b‖ * ‖h c‖) * E / |r|) := by
    ring
  have h9 : (0 : ℝ) ≤ 2 ^ 21 - 2 ^ 16 * 22 - 2 ^ 15 * 10 := by norm_num
  have := mul_nonneg h9 hT
  linarith

end OVNS.Quant.Metric

end
