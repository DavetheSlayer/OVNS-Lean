import OddViscousNS.Quant.Joint.Metric.Phase

/-!
# The intermediate-helicity channels of `X₂` (step J5, node N2)

The signed step of Bodies 33, 36, 41 and LOCAL457: in `X₂` the two rootings carry the same product
`L[f]*_{lm} L[g]_{mj}`, with the two inner denominators, and `1/d_lm + 1/d_mj` gains on the old
kernel at a large intermediate.  All of it is **at a fixed block**: no cancellation is claimed
between different slow leaves or different exteriors, so the output of this file is an upper bound
on the operator norm of one block, `norm_X2b_signed_le`.

## The method
On a slow leaf the helicity of the leaf does not enter the denominator of `X₁`: the phase is
`λ_b(j) − λ_c(k)`, since `λ_a(p) = 0`.  So on a fast channel `(c, b)`, **an edge of `X₁` is the
edge of `𝓛` times a scalar** (`chan_Xf`), and its reverse edge is the edge of `𝓛*` times the same
scalar (`chan_Xr`).  The sum over the eight leaf helicities is not opened.  Then the four products
of the two rootings collect, on the channel `(c, e, d)`, as
`(1/d_lm + 1/d_mj) 𝓛*𝓛 + (1/d_lm) 𝓛𝓛 + (1/d_mj) 𝓛*𝓛*` (`twoRoot_split`),
which is the displayed formula of LOCAL457 at every weight `s`.  The scalars add, by
`1/d₁ + 1/d₂ = (d₁ + d₂)/(d₁ d₂)` (`resolv_add`), and in `d₁ + d₂ = −(Σ_lm + Σ_mj) + irδ_lj`
**the intermediate helicity has cancelled**.

The bound at a large intermediate is `SignedBlock.lean`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. An edge of `X₁` is an edge of `𝓛` times a scalar -/

/-- The forward edge of `X₁`, `(L/d)` of Body 12 §6. -/
def Xf (s : ℕ) (r τ : ℝ) (p k j : Mode) (v : V3) : V3 →L[ℂ] V3 :=
  ((2 * wt s k j : ℝ) : ℂ) • blk (metM r τ) p k j v

/-- The reverse edge of `X₁`, `(L*/d)`. -/
def Xr (s : ℕ) (r τ : ℝ) (p k j : Mode) (v : V3) : V3 →L[ℂ] V3 :=
  ContinuousLinearMap.adjoint (Xf s r τ (-p) j k (conjV v))

lemma X1b_eq_add (s : ℕ) (r τ : ℝ) (p k j : Mode) (v : V3) :
    X1b s r τ p k j v = Xf s r τ p k j v + Xr s r τ p k j v := rfl

/-- The inverse denominator `1/d` of the fast channel `(c, b)`, with
`d = −H + i r (λ_b(j) − λ_c(k))`: "its OWN denominator" (Body 12 §6), which does not see the
helicity of the slow leaf. -/
def chR (r H : ℝ) (c b : Sgn) (k j : Mode) : ℂ := resolv (-1) H (r * (lam b j - lam c k))

lemma metM_eq {r τ : ℝ} {a b c : Sgn} {p q : Mode} (hp : p 2 = 0) (hq : q 2 ≠ 0)
    (hne : lam b q ≠ lam c (p + q)) :
    metM r τ a b c p q = phaseM τ a b c p q * chR r (triHeat p q) c b (p + q) q := by
  have hΦ : Phi a b c p q = lam b q - lam c (p + q) := by simp [Phi, lam_slow hp]
  unfold metM
  rw [ite_eq_left ⟨hp, hq, by rw [hΦ]; exact sub_ne_zero.2 hne⟩]
  simp only [metSym, chR]
  rw [hΦ]

/-- The channel of an edge: only the leaf helicity remains. -/
lemma hel_blk_hel (m : Mult) (p k j : Mode) (v w : V3) (b c : Sgn) :
    hel c k (blk m p k j v (hel b j w)) =
      ∑ a : Sgn, m a b c p j • hel c k (vert p j (hel a p v) (hel b j w)) := by
  rw [blk_apply, hel_sum_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hel_sum_distrib, Fintype.sum_eq_single b (fun b' hb' => ?_)]
  · rw [hel_sum_distrib, Fintype.sum_eq_single c (fun c' hc' => ?_)]
    · rw [hel_smul, hel_idem, hel_idem]
    · rw [hel_smul, hel_orth (Ne.symm hc'), smul_zero]
  · refine (hel_sum_distrib _ _ _ _).trans (Finset.sum_eq_zero fun c' _ => ?_)
    rw [hel_orth hb', hel_smul]
    have h0 : vert p j (hel a p v) (0 : V3) = 0 := map_zero (vertR p j (hel a p v))
    rw [h0, hel_zero_right, hel_zero_right, smul_zero]

/-- **The forward edge of `X₁`, on a fast channel, is the edge of `𝓛` times `1/d`.** -/
theorem chan_Xf (s : ℕ) (r τ : ℝ) {p k j : Mode} {b c : Sgn} (hp : p 2 = 0) (hj : j 2 ≠ 0)
    (hk : p + j = k) (hne : lam b j ≠ lam c k) (v w : V3) :
    hel c k (Xf s r τ p k j v (hel b j w)) =
      chR r (triHeat p j) c b k j • hel c k (Lb s τ p k j v (hel b j w)) := by
  subst hk
  simp only [Xf, Lb, smul_apply, hel_smul]
  rw [hel_blk_hel, hel_blk_hel, smul_comm (chR r (triHeat p j) c b (p + j) j)]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [metM_eq hp hj hne, mul_comm, mul_smul]

private lemma triHeat_flip' (p q : Mode) : triHeat (-p) (p + q) = triHeat p q := by
  have e : -p + (p + q) = q := by abel
  simp only [triHeat, e, absSq_neg]
  ring

/-- **The reverse edge of `X₁`, on a fast channel, is the edge of `𝓛*` times the same `1/d`.** -/
theorem chan_Xr (s : ℕ) (r τ : ℝ) {p k j : Mode} {b c : Sgn} (hp : p 2 = 0) (hk2 : k 2 ≠ 0)
    (hk : p + j = k) (hne : lam b j ≠ lam c k) (v w : V3) :
    hel c k (Xr s r τ p k j v (hel b j w)) =
      chR r (triHeat p j) c b k j • hel c k (Lad s τ p k j v (hel b j w)) := by
  have hp' : (-p) 2 = 0 := by simp [hp]
  have e : -p + k = j := by rw [← hk]; abel
  refine ext_inner_left ℂ fun x => ?_
  rw [inner_smul_right, inner_hel_right, inner_hel_right]
  simp only [Xr, Lad, ContinuousLinearMap.adjoint_inner_right]
  rw [inner_hel_right, inner_hel_right]
  have h1 := chan_Xf s r τ (b := c) (c := b) hp' hk2 e hne.symm (conjV v) x
  rw [h1, inner_smul_left]
  congr 1
  simp only [chR]
  rw [Quant.conj_resolv, ← hk, triHeat_flip']
  congr 1
  ring

/-! ### B. The two rootings on a channel -/

/-- A vector with a transverse output is the sum of its channels. -/
lemma sum_hel_Lb (s : ℕ) (τ : ℝ) (p k j : Mode) (v w : V3) :
    ∑ e : Sgn, hel e k (Lb s τ p k j v w) = Lb s τ p k j v w := by
  have h := Pi_Lb s τ p k j v w
  rw [rotL_apply] at h
  simpa using h

/-- `𝓛*` sees only the transverse part of its input. -/
lemma Lad_sum (s : ℕ) (τ : ℝ) (p k j : Mode) (v u : V3) :
    Lad s τ p k j v u = ∑ e : Sgn, Lad s τ p k j v (hel e j u) := by
  rw [← map_sum, ← Lad_Pi s τ p k j v u, rotL_apply]
  simp

/-- **The two rootings on a channel** (LOCAL457, "Exact common product of the two inner rootings";
Body 33; Body 36): at the exterior helicities `(c, d)`, the sum over the intermediate helicity `e`
of `(1/d_lm + 1/d_mj) 𝓛*𝓛 + (1/d_lm) 𝓛𝓛 + (1/d_mj) 𝓛*𝓛*`.  At every weight, and an exact identity;
the hypotheses are the masks of the two inner `X₁`. -/
theorem twoRoot_split (s : ℕ) (r τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) (h1 : ∀ e c, lam e (l - a) ≠ lam c l)
    (h2 : ∀ d e, lam d (l - a - b) ≠ lam e (l - a)) (c d : Sgn) (w : V3) :
    hel c l (twoRoot s r τ f g l a b (hel d (l - a - b) w)) = ∑ e : Sgn,
      ((chR r (triHeat a (l - a)) c e l (l - a) +
          chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)) •
          hel c l (Lad s τ a l (l - a) (f a)
            (hel e (l - a) (Lb s τ b (l - a) (l - a - b) (g b) (hel d (l - a - b) w)))) +
        chR r (triHeat a (l - a)) c e l (l - a) •
          hel c l (Lb s τ a l (l - a) (f a)
            (hel e (l - a) (Lb s τ b (l - a) (l - a - b) (g b) (hel d (l - a - b) w)))) +
        chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b) •
          hel c l (Lad s τ a l (l - a) (f a)
            (hel e (l - a) (Lad s τ b (l - a) (l - a - b) (g b) (hel d (l - a - b) w))))) := by
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  have hm2 : (l - a) 2 ≠ 0 := fun h => hj (by simp only [Pi.sub_apply] at h ⊢; simpa [hb] using h)
  have hl2 : l 2 ≠ 0 := fun h => hm2 (by simp [ha, h])
  have r1 : hel c l (X1b s r τ a l (l - a) (f a)
      (Lb s τ b (l - a) (l - a - b) (g b) (hel d (l - a - b) w))) = ∑ e : Sgn,
      (chR r (triHeat a (l - a)) c e l (l - a) • hel c l (Lb s τ a l (l - a) (f a)
          (hel e (l - a) (Lb s τ b (l - a) (l - a - b) (g b) (hel d (l - a - b) w)))) +
        chR r (triHeat a (l - a)) c e l (l - a) • hel c l (Lad s τ a l (l - a) (f a)
          (hel e (l - a) (Lb s τ b (l - a) (l - a - b) (g b) (hel d (l - a - b) w))))) := by
    conv_lhs => rw [← sum_hel_Lb s τ b (l - a) (l - a - b) (g b) (hel d (l - a - b) w)]
    rw [map_sum, hel_sum_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [X1b_eq_add, add_apply, hel_add, chan_Xf s r τ ha hm2 e1 (h1 e c),
      chan_Xr s r τ ha hl2 e1 (h1 e c)]
  have r2 : hel c l (Lad s τ a l (l - a) (f a)
      (X1b s r τ b (l - a) (l - a - b) (g b) (hel d (l - a - b) w))) = ∑ e : Sgn,
      (chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b) • hel c l (Lad s τ a l (l - a) (f a)
          (hel e (l - a) (Lb s τ b (l - a) (l - a - b) (g b) (hel d (l - a - b) w)))) +
        chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b) • hel c l (Lad s τ a l (l - a) (f a)
          (hel e (l - a) (Lad s τ b (l - a) (l - a - b) (g b) (hel d (l - a - b) w))))) := by
    rw [Lad_sum, hel_sum_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [X1b_eq_add, add_apply, hel_add, chan_Xf s r τ hb hj e2 (h2 d e),
      chan_Xr s r τ hb hm2 e2 (h2 d e), map_add, map_smul, map_smul, hel_add, hel_smul, hel_smul]
  simp only [twoRoot, add_apply, ContinuousLinearMap.comp_apply]
  rw [hel_add, r1, r2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [add_smul]
  abel

/-! ### C. The two inverse denominators -/

/-- `1/d₁ + 1/d₂ = (d₁ + d₂)/(d₁ d₂)`, with `d = −H + iz`: "its exact multiplier" (LOCAL457). -/
theorem resolv_add {H₁ H₂ : ℝ} (h1 : H₁ ≠ 0) (h2 : H₂ ≠ 0) (z₁ z₂ : ℝ) :
    resolv (-1) H₁ z₁ + resolv (-1) H₂ z₂ =
      (((-(H₁ + H₂) : ℝ) : ℂ) + ((z₁ + z₂ : ℝ) : ℂ) * Complex.I) *
        (resolv (-1) H₁ z₁ * resolv (-1) H₂ z₂) := by
  have n1 := Quant.resolv_den_ne_zero (ε := -1) (Or.inr rfl) h1 z₁
  have n2 := Quant.resolv_den_ne_zero (ε := -1) (Or.inr rfl) h2 z₂
  simp only [Quant.resolv]
  have e : ((-(H₁ + H₂) : ℝ) : ℂ) + ((z₁ + z₂ : ℝ) : ℂ) * Complex.I =
      (((-1 * H₁ : ℝ) : ℂ) + (z₁ : ℂ) * Complex.I) +
        (((-1 * H₂ : ℝ) : ℂ) + (z₂ : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [e]
  generalize ((-1 * H₁ : ℝ) : ℂ) + (z₁ : ℂ) * Complex.I = d₁ at n1 ⊢
  generalize ((-1 * H₂ : ℝ) : ℂ) + (z₂ : ℂ) * Complex.I = d₂ at n2 ⊢
  field_simp
  ring

/-- `|1/d| ≤ 1/|z|`. -/
lemma norm_resolv_le_abs (H : ℝ) {z : ℝ} (hz : z ≠ 0) : ‖resolv (-1) H z‖ ≤ 1 / |z| := by
  rw [Quant.norm_resolv_sgn (Or.inr rfl)]
  refine one_div_le_one_div_of_le (abs_pos.2 hz) ?_
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg H])

/-- The sum of the two inverse denominators: the signed gain. -/
theorem norm_resolv_add_le {H₁ H₂ z₁ z₂ : ℝ} (h1 : 0 < H₁) (h2 : 0 < H₂) (hz₁ : z₁ ≠ 0)
    (hz₂ : z₂ ≠ 0) :
    ‖resolv (-1) H₁ z₁ + resolv (-1) H₂ z₂‖ ≤ (H₁ + H₂ + |z₁ + z₂|) / (|z₁| * |z₂|) := by
  rw [resolv_add h1.ne' h2.ne', norm_mul, norm_mul]
  have hn : ‖((-(H₁ + H₂) : ℝ) : ℂ) + ((z₁ + z₂ : ℝ) : ℂ) * Complex.I‖ ≤ H₁ + H₂ + |z₁ + z₂| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith)]
  have h3 := norm_resolv_le_abs H₁ hz₁
  have h4 := norm_resolv_le_abs H₂ hz₂
  calc _ ≤ (H₁ + H₂ + |z₁ + z₂|) * (1 / |z₁| * (1 / |z₂|)) :=
        mul_le_mul hn (mul_le_mul h3 h4 (norm_nonneg _) (by positivity)) (by positivity)
          (by positivity)
    _ = _ := by
        rw [div_mul_div_comm, mul_one, mul_one_div]

end OVNS.Quant.Metric

end
