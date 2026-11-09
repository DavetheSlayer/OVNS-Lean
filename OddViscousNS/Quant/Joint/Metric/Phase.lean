import OddViscousNS.Quant.Joint.Metric.Block

/-!
# The homological identity of the signed metric, at one coefficient (step J5, pilot)

The check of the definitions of `Defs.lean` against Body 12 §§7–8 and LOCAL83.  All the blocks are
**covariant under the filter**: `O(τ + σ)_{kj} = R(−σ)_k O(τ)_{kj} R(σ)_j`, with
`R(σ)_k = ∑_c e^{iσλ_c(k)} H_c(k)` (`rotL`), on slow leaves, since `λ_a(p) = 0` there.  This is
the statement that the intermediate helicity cancels: in `X₁ 𝓛` the factors `R(σ)_m R(−σ)_m` at the
intermediate label `m` collapse (`Pi_*`), so the only phase of `X₂` and `Z` is the exterior one
`δ_lj = λ_e(j) − λ_c(l)`.  If the two rootings had been wired wrongly, this would fail.

Consequences, for `s = 1, 2` alike:
* `X2b_homological`: `(∂_t − Σ) X₂ = X₁𝓛 + 𝓛*X₁` on each exterior channel: LOCAL83's `H₂X₂ = X₁L +
  L*X₁`; `Zb_homological`: `(∂_t − Σ) Z = X₁(B)`, the "PLUS sign".
* `X2b_heat`: the coefficient of `−∫₀^∞ E_u [X₁𝓛 + 𝓛*X₁](τ + ru) E_u du` is `X2b` (Body 12 §7: "the
  negative integral is the actual outer `1/[−Sigma + ir delta_lj]`"; "phases advance once inside the
  integrand").
* `adjoint_X2b`, `adjoint_Zb`: `X₂`, `Z` are Hermitian on real slow data, path reversed.  With
  `adjoint_twoRoot` this tests the wiring of the second rooting; and it is what makes the literal
  adjoints `𝓛*X₂`, `𝓛*Z` the conjugate form of `YLForm`, as the docstring of `YLForm` says.

Nothing here is an estimate.  These are the algebraic inputs of the energy identity of E8-J.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. The filter at one mode -/

/-- The filter at the mode `k`, on the transverse part: `∑_c e^{iσλ_c(k)} H_c(k)`. -/
def rotL (σ : ℝ) (k : Mode) : V3 →L[ℂ] V3 :=
  ∑ c : Sgn, Complex.exp (Complex.I * (σ * lam c k : ℝ)) • helL c k

lemma rotL_apply (σ : ℝ) (k : Mode) (v : V3) :
    rotL σ k v = ∑ c : Sgn, Complex.exp (Complex.I * (σ * lam c k : ℝ)) • hel c k v := by
  simp [rotL]

lemma hel_sum_distrib (e : Sgn) (k : Mode) {ι : Type*} (s : Finset ι) (x : ι → V3) :
    hel e k (∑ i ∈ s, x i) = ∑ i ∈ s, hel e k (x i) := by
  have h : helL e k (∑ i ∈ s, x i) = ∑ i ∈ s, helL e k (x i) := map_sum (helL e k) x s
  simpa only [helL_apply] using h

/-- `H_c R(σ) = e^{iσλ_c} H_c`. -/
lemma hel_rotL (σ : ℝ) (c : Sgn) (k : Mode) (v : V3) :
    hel c k (rotL σ k v) = Complex.exp (Complex.I * (σ * lam c k : ℝ)) • hel c k v := by
  rw [rotL_apply, hel_sum_distrib, Fintype.sum_eq_single c]
  · rw [hel_smul, hel_idem]
  · intro d hd
    rw [hel_smul, hel_orth (Ne.symm hd), smul_zero]

/-- `R(σ) H_c = e^{iσλ_c} H_c`. -/
lemma rotL_hel (σ : ℝ) (c : Sgn) (k : Mode) (v : V3) :
    rotL σ k (hel c k v) = Complex.exp (Complex.I * (σ * lam c k : ℝ)) • hel c k v := by
  rw [rotL_apply, Fintype.sum_eq_single c]
  · rw [hel_idem]
  · intro d hd
    rw [hel_orth hd, smul_zero]

/-- `R(σ) R(σ') = R(σ + σ')`. -/
lemma rotL_rotL (σ σ' : ℝ) (k : Mode) (v : V3) :
    rotL σ k (rotL σ' k v) = rotL (σ + σ') k v := by
  rw [rotL_apply σ k, rotL_apply (σ + σ') k]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hel_rotL, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `R(σ)` moves across the inner product as `R(−σ)`. -/
lemma inner_rotL (σ : ℝ) (k : Mode) (x y : V3) :
    inner ℂ (rotL σ k x) y = inner ℂ x (rotL (-σ) k y) := by
  rw [rotL_apply, rotL_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_hel_right]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-! ### B. Covariance of the edges -/

/-- A family of multipliers advances by the phase. -/
def Cov (σ : ℝ) (m m' : Mult) : Prop :=
  ∀ a b c p q, m' a b c p q = Complex.exp (Complex.I * (σ * Phi a b c p q : ℝ)) * m a b c p q

lemma phaseM_cov (τ σ : ℝ) : Cov σ (phaseM τ) (phaseM (τ + σ)) := fun a b c p q => by
  simp only [phaseM]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma metM_cov (r τ σ : ℝ) : Cov σ (metM r τ) (metM r (τ + σ)) := fun a b c p q => by
  unfold metM
  split_ifs
  · simp only [metSym]
    rw [phaseM_cov τ σ a b c p q]
    ring
  · simp

/-- **Covariance of an edge through a slow leaf**: `λ_a(p) = 0`, so the phase of a triad is the
phase of its two fast legs. -/
lemma blk_cov {σ : ℝ} {m m' : Mult} (hm : Cov σ m m') {p k j : Mode} (hp : p 2 = 0)
    (hk : p + j = k) (v w : V3) :
    blk m' p k j v w = rotL (-σ) k (blk m p k j v (rotL σ j w)) := by
  subst hk
  rw [blk_apply, blk_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hv : ∀ (e : ℂ) (B : V3), vert p j (hel a p v) (e • B) = e • vert p j (hel a p v) B :=
    fun e B => (vertR p j (hel a p v)).map_smul e B
  rw [hm a b c p j, hel_rotL, hv, hel_smul, map_smul, map_smul, rotL_hel, smul_smul, smul_smul]
  congr 1
  simp only [Phi, lam_slow hp, zero_add]
  rw [mul_comm _ (m a b c p j), mul_assoc, ← Complex.exp_add]
  congr 3
  push_cast
  ring

/-- The output of an edge is transverse: `R(0) O = O`. -/
lemma Pi_blk (m : Mult) (p k j : Mode) (v w : V3) :
    rotL 0 k (blk m p k j v w) = blk m p k j v w := by
  rw [blk_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, rotL_hel]
  simp

lemma Pi_Lb (s : ℕ) (τ : ℝ) (p k j : Mode) (v w : V3) :
    rotL 0 k (Lb s τ p k j v w) = Lb s τ p k j v w := by
  simp only [Lb, smul_apply, map_smul, Pi_blk]

/-- The adjoint of an operator with transverse output has transverse input. -/
lemma adjoint_Pi {T : V3 →L[ℂ] V3} {k : Mode} (h : ∀ w, rotL 0 k (T w) = T w) (w : V3) :
    ContinuousLinearMap.adjoint T (rotL 0 k w) = ContinuousLinearMap.adjoint T w := by
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  calc inner ℂ (T x) (rotL 0 k w) = inner ℂ (rotL 0 k (T x)) w := by
        rw [inner_rotL, neg_zero]
    _ = inner ℂ (T x) w := by rw [h x]

/-- The adjoint of a covariant operator is covariant. -/
lemma adjoint_cov {T T' : V3 →L[ℂ] V3} {k j : Mode} {σ : ℝ}
    (h : ∀ w, T' w = rotL (-σ) j (T (rotL σ k w))) (w : V3) :
    ContinuousLinearMap.adjoint T' w =
      rotL (-σ) k (ContinuousLinearMap.adjoint T (rotL σ j w)) := by
  refine ext_inner_left ℂ fun x => ?_
  have e : inner ℂ x (rotL (-σ) k (ContinuousLinearMap.adjoint T (rotL σ j w))) =
      inner ℂ (rotL σ k x) (ContinuousLinearMap.adjoint T (rotL σ j w)) := (inner_rotL σ k _ _).symm
  rw [e, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right, h,
    inner_rotL, neg_neg]

lemma Lb_cov (s : ℕ) (τ σ : ℝ) {p k j : Mode} (hp : p 2 = 0) (hk : p + j = k) (v w : V3) :
    Lb s (τ + σ) p k j v w = rotL (-σ) k (Lb s τ p k j v (rotL σ j w)) := by
  simp only [Lb, smul_apply, map_smul]
  rw [blk_cov (phaseM_cov τ σ) hp hk]

lemma Lad_cov (s : ℕ) (τ σ : ℝ) {p k j : Mode} (hp : p 2 = 0) (hk : p + j = k) (v w : V3) :
    Lad s (τ + σ) p k j v w = rotL (-σ) k (Lad s τ p k j v (rotL σ j w)) := by
  have hp' : (-p) 2 = 0 := by simp [hp]
  have e : -p + k = j := by rw [← hk]; abel
  exact adjoint_cov (fun w => Lb_cov s τ σ hp' e (conjV v) w) w

lemma X1b_cov (s : ℕ) (r τ σ : ℝ) {p k j : Mode} (hp : p 2 = 0) (hk : p + j = k) (v w : V3) :
    X1b s r (τ + σ) p k j v w = rotL (-σ) k (X1b s r τ p k j v (rotL σ j w)) := by
  have hp' : (-p) 2 = 0 := by simp [hp]
  have e : -p + k = j := by rw [← hk]; abel
  have h2 := adjoint_cov (T := ((2 * wt s j k : ℝ) : ℂ) • blk (metM r τ) (-p) j k (conjV v))
    (T' := ((2 * wt s j k : ℝ) : ℂ) • blk (metM r (τ + σ)) (-p) j k (conjV v)) (σ := σ)
    (fun w => by
      simp only [smul_apply, map_smul]
      rw [blk_cov (metM_cov r τ σ) hp' e]) w
  simp only [X1b, add_apply, map_add, smul_apply, map_smul]
  rw [blk_cov (metM_cov r τ σ) hp hk, h2]

/-- `𝓛*` has transverse input. -/
lemma Lad_Pi (s : ℕ) (τ : ℝ) (p k j : Mode) (v w : V3) :
    Lad s τ p k j v (rotL 0 j w) = Lad s τ p k j v w :=
  adjoint_Pi (fun w => Pi_Lb s τ (-p) j k (conjV v) w) w

/-- `X₁` applied to a transverse vector of the intermediate label: covariant composition with `𝓛`
needs only `Pi_Lb`.  For `𝓛* X₁`, `Lad_Pi`. -/
lemma twoRoot_cov (s : ℕ) (r τ σ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (w : V3) :
    twoRoot s r (τ + σ) f g l a b w =
      rotL (-σ) l (twoRoot s r τ f g l a b (rotL σ (l - a - b) w)) := by
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  simp only [twoRoot, add_apply, map_add, ContinuousLinearMap.comp_apply]
  congr 1
  · rw [Lb_cov s τ σ hb e2, X1b_cov s r τ σ ha e1, rotL_rotL, add_neg_cancel, Pi_Lb]
  · rw [X1b_cov s r τ σ hb e2, Lad_cov s τ σ ha e1, rotL_rotL, add_neg_cancel, Lad_Pi]

/-! ### C. The outer inverse -/

/-- On one exterior channel, `outerInv` is the resolvent. -/
lemma hel_outerInv (r H : ℝ) (l j : Mode) (T : V3 →L[ℂ] V3) (c e : Sgn) (w : V3) :
    hel c l (outerInv r H l j T (hel e j w)) =
      resolv (-1) H (r * outerPhi c e l j) • hel c l (T (hel e j w)) := by
  simp only [outerInv, sum_apply, smul_apply, ContinuousLinearMap.comp_apply, helL_apply]
  rw [hel_sum_distrib, Fintype.sum_eq_single c (fun c' hc' => ?_)]
  · rw [hel_sum_distrib, Fintype.sum_eq_single e (fun e' he' => ?_)]
    · rw [hel_smul, hel_idem, hel_idem]
    · rw [hel_smul, hel_idem, hel_orth he', map_zero, hel_zero_right, smul_zero]
  · rw [hel_sum_distrib]
    refine Finset.sum_eq_zero fun e' _ => ?_
    rw [hel_smul, hel_orth (Ne.symm hc'), smul_zero]

/-- The exterior channel of a covariant block moves by the exterior phase alone. -/
lemma chan_cov {T T' : V3 →L[ℂ] V3} {l j : Mode} {σ : ℝ}
    (h : ∀ w, T' w = rotL (-σ) l (T (rotL σ j w))) (c e : Sgn) (w : V3) :
    hel c l (T' (hel e j w)) = Complex.exp (Complex.I * (σ * outerPhi c e l j : ℝ)) •
      hel c l (T (hel e j w)) := by
  rw [h, hel_rotL, rotL_hel, map_smul, hel_smul, smul_smul, ← Complex.exp_add]
  congr 2
  simp only [outerPhi]
  push_cast
  ring

/-! ### D. The homological identities -/

/-- **The channel of both rootings moves by the exterior phase**: the intermediate helicity has
cancelled. -/
theorem twoRoot_chan (s : ℕ) (r τ σ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (c e : Sgn) (w : V3) :
    hel c l (twoRoot s r (τ + σ) f g l a b (hel e (l - a - b) w)) =
      Complex.exp (Complex.I * (σ * outerPhi c e l (l - a - b) : ℝ)) •
        hel c l (twoRoot s r τ f g l a b (hel e (l - a - b) w)) :=
  chan_cov (fun w => twoRoot_cov s r τ σ f g ha hb w) c e w

/-- The `Z` source: `X₁(B)` is covariant at the merged slow leaf. -/
theorem X1Z_chan (s : ℕ) (r τ σ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (c e : Sgn) (w : V3) :
    hel c l (X1b s r (τ + σ) (a + b) l (l - a - b) (slowV a b (f a) (g b)) (hel e (l - a - b) w)) =
      Complex.exp (Complex.I * (σ * outerPhi c e l (l - a - b) : ℝ)) •
        hel c l (X1b s r τ (a + b) l (l - a - b) (slowV a b (f a) (g b))
          (hel e (l - a - b) w)) := by
  have hab : (a + b) 2 = 0 := by simp [ha, hb]
  have e1 : (a + b) + (l - a - b) = l := by abel
  exact chan_cov (fun w => X1b_cov s r τ σ hab e1 _ w) c e w

/-- The channel of `H⁻¹ T` against the channel of `T`: `(−Σ + irδ) H⁻¹ T = T`. -/
lemma outer_mul {r H : ℝ} (hH : 0 < H) (l j : Mode) (T : V3 →L[ℂ] V3) (c e : Sgn) (w : V3) :
    (((-H : ℝ) : ℂ) + ((r * outerPhi c e l j : ℝ) : ℂ) * Complex.I) •
        hel c l (outerInv r H l j T (hel e j w)) = hel c l (T (hel e j w)) := by
  have h0 := resolv_den_ne_zero (ε := -1) (Or.inr rfl) hH.ne' (r * outerPhi c e l j)
  have e1 : (((-1 : ℝ) * H : ℝ) : ℂ) = ((-H : ℝ) : ℂ) := by push_cast; ring
  rw [e1] at h0
  rw [hel_outerInv, smul_smul, resolv, e1, mul_div_cancel₀ _ h0, one_smul]

/-- `(∂_t − Σ)` on a channel: if the channel moves by the phase `Φ` at rate `r`, its time derivative
is `irΦ`, and `irΦ = Σ + (−Σ + irΦ)`. -/
lemma chan_hasDerivAt {r Φ t₀ : ℝ} {V : ℝ → V3}
    (h : ∀ t, V t = Complex.exp (Complex.I * ((r * (t - t₀)) * Φ : ℝ)) • V t₀) :
    HasDerivAt V ((((r * Φ : ℝ) : ℂ) * Complex.I) • V t₀) t₀ := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * ((r * (t - t₀)) * Φ : ℝ)))
      (((r * Φ : ℝ) : ℂ) * Complex.I) t₀ := by
    have h1 : HasDerivAt (fun t : ℝ => Complex.I * (((r * (t - t₀)) * Φ : ℝ) : ℂ))
        (((r * Φ : ℝ) : ℂ) * Complex.I) t₀ := by
      have h2 : HasDerivAt (fun t : ℝ => ((r * (t - t₀)) * Φ : ℝ)) (r * Φ) t₀ := by
        have := ((hasDerivAt_id t₀).sub_const t₀).const_mul r |>.mul_const Φ
        simpa using this
      have h3 := (h2.ofReal_comp).const_mul Complex.I
      simpa [mul_comm] using h3
    have h4 := h1.cexp
    simpa using h4
  have hV : V = fun t => Complex.exp (Complex.I * ((r * (t - t₀)) * Φ : ℝ)) • V t₀ := funext h
  rw [hV]
  have := hE.smul_const (V t₀)
  simpa using this

/-- **`H₂ X₂ = X₁𝓛 + 𝓛*X₁` on one exterior channel, at every weight** (LOCAL83: "`H₂Y₂ − X₁L − L*X₁
− D_SX₁[BSS] = 0`"): along `τ = r t`, frozen amplitudes,
`∂_t X₂ = Σ X₂ + (X₁𝓛 + 𝓛*X₁)`, that is `(∂_t − Σ) X₂ = X₁𝓛 + 𝓛*X₁`, with `Σ` the two exterior and
the two ancestor heats.  This is the homological equation of the metric. -/
theorem X2b_homological (s : ℕ) (r t₀ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : l - a - b ≠ 0) (c e : Sgn) (w : V3) :
    HasDerivAt (fun t : ℝ => hel c l (X2b s r (r * t) f g l a b (hel e (l - a - b) w)))
      (((heat4 l (l - a - b) a b : ℝ) : ℂ) •
          hel c l (X2b s r (r * t₀) f g l a b (hel e (l - a - b) w)) +
        hel c l (twoRoot s r (r * t₀) f g l a b (hel e (l - a - b) w))) t₀ := by
  set H := heat4 l (l - a - b) a b with hH
  have hH0 : 0 < H := heat4_pos hj a b
  set Φ := outerPhi c e l (l - a - b) with hΦ
  have hchan : ∀ t, hel c l (X2b s r (r * t) f g l a b (hel e (l - a - b) w)) =
      Complex.exp (Complex.I * ((r * (t - t₀)) * Φ : ℝ)) •
        hel c l (X2b s r (r * t₀) f g l a b (hel e (l - a - b) w)) := fun t => by
    simp only [X2b]
    rw [hel_outerInv, hel_outerInv]
    have e1 : r * t = r * t₀ + r * (t - t₀) := by ring
    rw [e1, twoRoot_chan s r (r * t₀) _ f g ha hb, smul_comm]
  have hD := chan_hasDerivAt (V := fun t => hel c l (X2b s r (r * t) f g l a b
    (hel e (l - a - b) w))) (t₀ := t₀) (r := r) (Φ := Φ) hchan
  have hO := outer_mul (r := r) hH0 l (l - a - b) (twoRoot s r (r * t₀) f g l a b) c e w
  have hval : (((r * Φ : ℝ) : ℂ) * Complex.I) •
      hel c l (X2b s r (r * t₀) f g l a b (hel e (l - a - b) w)) =
      ((H : ℝ) : ℂ) • hel c l (X2b s r (r * t₀) f g l a b (hel e (l - a - b) w)) +
        hel c l (twoRoot s r (r * t₀) f g l a b (hel e (l - a - b) w)) := by
    rw [← hO]
    simp only [X2b, ← hH]
    rw [← add_smul]
    congr 1
    push_cast
    ring
  rw [← hval]
  exact hD

/-- **`H₂ Z = X₁(B)` on one exterior channel, at every weight**: "the PLUS sign" (LOCAL83). -/
theorem Zb_homological (s : ℕ) (r t₀ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : l - a - b ≠ 0) (c e : Sgn) (w : V3) :
    HasDerivAt (fun t : ℝ => hel c l (Zb s r (r * t) f g l a b (hel e (l - a - b) w)))
      (((heat4 l (l - a - b) a b : ℝ) : ℂ) •
          hel c l (Zb s r (r * t₀) f g l a b (hel e (l - a - b) w)) +
        hel c l (X1b s r (r * t₀) (a + b) l (l - a - b) (slowV a b (f a) (g b))
          (hel e (l - a - b) w))) t₀ := by
  set H := heat4 l (l - a - b) a b with hH
  have hH0 : 0 < H := heat4_pos hj a b
  set Φ := outerPhi c e l (l - a - b) with hΦ
  have hchan : ∀ t, hel c l (Zb s r (r * t) f g l a b (hel e (l - a - b) w)) =
      Complex.exp (Complex.I * ((r * (t - t₀)) * Φ : ℝ)) •
        hel c l (Zb s r (r * t₀) f g l a b (hel e (l - a - b) w)) := fun t => by
    simp only [Zb]
    rw [hel_outerInv, hel_outerInv]
    have e1 : r * t = r * t₀ + r * (t - t₀) := by ring
    rw [e1, X1Z_chan s r (r * t₀) _ f g ha hb, smul_comm]
  have hD := chan_hasDerivAt (V := fun t => hel c l (Zb s r (r * t) f g l a b
    (hel e (l - a - b) w))) (t₀ := t₀) (r := r) (Φ := Φ) hchan
  have hO := outer_mul (r := r) hH0 l (l - a - b)
    (X1b s r (r * t₀) (a + b) l (l - a - b) (slowV a b (f a) (g b))) c e w
  have hval : (((r * Φ : ℝ) : ℂ) * Complex.I) •
      hel c l (Zb s r (r * t₀) f g l a b (hel e (l - a - b) w)) =
      ((H : ℝ) : ℂ) • hel c l (Zb s r (r * t₀) f g l a b (hel e (l - a - b) w)) +
        hel c l (X1b s r (r * t₀) (a + b) l (l - a - b) (slowV a b (f a) (g b))
          (hel e (l - a - b) w)) := by
    rw [← hO]
    simp only [Zb, ← hH]
    rw [← add_smul]
    congr 1
    push_cast
    ring
  rw [← hval]
  exact hD

/-- **The heat formula of `X₂`** (Body 12 §7), on one exterior channel: `X₂` is `−∫₀^∞` of
`e^{−uΣ}` times both rootings at the advanced phase `τ + r u`.  The factor `e^{−uΣ}` is the two
exterior `E_u` and the two heated leaves `S_u`; the phase advances once. -/
theorem X2b_heat (s : ℕ) (r τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : l - a - b ≠ 0) (c e : Sgn) (w : V3) :
    hel c l (X2b s r τ f g l a b (hel e (l - a - b) w)) =
      -∫ u in Ioi (0 : ℝ), (Real.exp (-(u * heat4 l (l - a - b) a b)) : ℂ) •
        hel c l (twoRoot s r (τ + r * u) f g l a b (hel e (l - a - b) w)) := by
  set H := heat4 l (l - a - b) a b with hH
  have hH0 : 0 < H := heat4_pos hj a b
  set Φ := outerPhi c e l (l - a - b) with hΦ
  set V := hel c l (twoRoot s r τ f g l a b (hel e (l - a - b) w)) with hV
  have hint : ∀ u : ℝ, (Real.exp (-(u * H)) : ℂ) •
      hel c l (twoRoot s r (τ + r * u) f g l a b (hel e (l - a - b) w)) =
      Complex.exp (((-H : ℝ) + ((r * Φ : ℝ) : ℂ) * Complex.I) * u) • V := fun u => by
    rw [twoRoot_chan s r τ (r * u) f g ha hb, smul_smul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp only [hint]
  rw [integral_smul_const, ← neg_smul, outer_heat_integral hH0 (r * Φ), X2b, hel_outerInv]

/-! ### E. Hermiticity of the blocks -/

private lemma conjV_conjV' (v : V3) : conjV (conjV v) = v := by
  ext i
  simp [conjV]

/-- `X₁` is Hermitian as a block, by construction. -/
lemma adjoint_X1b (s : ℕ) (r τ : ℝ) (p k j : Mode) (v : V3) :
    ContinuousLinearMap.adjoint (X1b s r τ p k j v) = X1b s r τ (-p) j k (conjV v) := by
  simp only [X1b, map_add, ContinuousLinearMap.adjoint_adjoint, neg_neg, conjV_conjV']
  exact add_comm _ _

lemma adjoint_Lb (s : ℕ) (τ : ℝ) (p k j : Mode) (v : V3) :
    ContinuousLinearMap.adjoint (Lb s τ p k j v) = Lad s τ (-p) j k (conjV v) := by
  simp only [Lad, neg_neg, conjV_conjV']

lemma adjoint_Lad (s : ℕ) (τ : ℝ) (p k j : Mode) (v : V3) :
    ContinuousLinearMap.adjoint (Lad s τ p k j v) = Lb s τ (-p) j k (conjV v) := by
  simp only [Lad, ContinuousLinearMap.adjoint_adjoint]

/-- The outer inverse commutes with the adjoint: the exterior phase changes sign with the two
exteriors, and `conj (1/(−Σ + irδ)) = 1/(−Σ − irδ)`. -/
lemma adjoint_outerInv (r H : ℝ) (l j : Mode) (T : V3 →L[ℂ] V3) :
    ContinuousLinearMap.adjoint (outerInv r H l j T) =
      outerInv r H j l (ContinuousLinearMap.adjoint T) := by
  refine ContinuousLinearMap.ext fun w => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [outerInv, sum_apply, smul_apply, ContinuousLinearMap.comp_apply, helL_apply, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
  have e1 : outerPhi e c j l = -outerPhi c e l j := by
    simp only [outerPhi]
    ring
  rw [Quant.conj_resolv, e1, mul_neg, inner_hel_right, ContinuousLinearMap.adjoint_inner_right,
    inner_hel_right]

/-- **Both rootings are the adjoint of each other**: on real slow data the adjoint of `X₁𝓛 + 𝓛*X₁`
at `(l, a, b)` is the same operator at the reversed path `(j, −b, −a)`.  If the second rooting were
wired wrongly, this would fail. -/
theorem adjoint_twoRoot (s : ℕ) (r τ : ℝ) {f g : Field} (hf : IsReal f) (hg : IsReal g)
    (l a b : Mode) :
    ContinuousLinearMap.adjoint (twoRoot s r τ f g l a b) =
      twoRoot s r τ g f (l - a - b) (-b) (-a) := by
  have e1 : l - a - b - -b = l - a := by abel
  have e2 : l - a - -a = l := by abel
  simp only [twoRoot, map_add, ContinuousLinearMap.adjoint_comp, adjoint_X1b, adjoint_Lb,
    adjoint_Lad, e1, e2, hf a, hg b]
  exact add_comm _ _

/-- **`X₂` is Hermitian** (Body 12 §7: "Hermiticity/reality follow from the integrand and real
heat"): `(X₂)_{lj}† = (X₂)_{jl}`, with the path reversed. -/
theorem adjoint_X2b (s : ℕ) (r τ : ℝ) {f g : Field} (hf : IsReal f) (hg : IsReal g)
    (l a b : Mode) :
    ContinuousLinearMap.adjoint (X2b s r τ f g l a b) =
      X2b s r τ g f (l - a - b) (-b) (-a) := by
  have e1 : l - a - b - -b = l - a := by abel
  have e2 : l - a - -a = l := by abel
  have hH : heat4 (l - a - b) l (-b) (-a) = heat4 l (l - a - b) a b := by
    simp only [heat4, absSq_neg]
    ring
  simp only [X2b, adjoint_outerInv, adjoint_twoRoot s r τ hf hg, sub_neg_eq_add]
  have e3 : l - a - b + b + a = l := by abel
  rw [e3]
  have e4 : heat4 (l - a - b) l (-b) (-a) = heat4 l (l - a - b) a b := hH
  rw [e4]

/-- Conjugation is additive. -/
private lemma conjV_add'' (a b : V3) : conjV (a + b) = conjV a + conjV b := by
  ext i
  simp [conjV]

private lemma conjV_smul'' (c : ℂ) (a : V3) : conjV (c • a) = conj c • conjV a := by
  ext i
  simp [conjV]

private lemma dotM_conjV' (v : V3) (k : Mode) : dotM (conjV v) (-k) = -conj (dotM v k) := by
  simp [dotM, conjV, Finset.sum_neg_distrib]

/-- The vertex respects reality. -/
private lemma conjV_vert' (p q : Mode) (A B : V3) :
    conjV (vert p q A B) = vert (-p) (-q) (conjV A) (conjV B) := by
  have h2 : conj (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, Complex.conj_ofNat]
  simp only [vert, conjV_smul'', conjV_leray, conjV_add'', h2, map_mul, Complex.conj_I, dotM_conjV',
    neg_add]
  simp only [mul_neg, neg_mul]

private lemma conjV_fin_sum {ι : Type*} (s : Finset ι) (x : ι → V3) :
    conjV (∑ i ∈ s, x i) = ∑ i ∈ s, conjV (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext i
      simp [conjV]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, conjV_add'', ih]

/-- The slow product edge respects reality. -/
lemma conjV_slowV (a b : Mode) (v w : V3) :
    conjV (slowV a b v w) = slowV (-a) (-b) (conjV v) (conjV w) := by
  have h1 : -a + -b = -(a + b) := by abel
  simp only [slowV, blk_apply, h1, conjV_fin_sum]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ =>
    Finset.sum_congr rfl fun c' _ => ?_
  rw [conjV_smul'', conjV_hel, conjV_vert', conjV_hel, conjV_hel, resM_real a' b' c' a b]

/-- **`Z` is Hermitian** (Body 12 §8: "Real `Bslow`, `X1` and heat prove Hermiticity/reality"). -/
theorem adjoint_Zb (s : ℕ) (r τ : ℝ) {f g : Field} (hf : IsReal f) (hg : IsReal g)
    (l a b : Mode) :
    ContinuousLinearMap.adjoint (Zb s r τ f g l a b) =
      Zb s r τ f g (l - a - b) (-a) (-b) := by
  have e1 : l - a - b - -a - -b = l := by abel
  have hH : heat4 (l - a - b) l (-a) (-b) = heat4 l (l - a - b) a b := by
    simp only [heat4, absSq_neg]
    ring
  have e2 : -(a + b) = -a + -b := by abel
  simp only [Zb, adjoint_outerInv, adjoint_X1b, e1, hH, conjV_slowV, hf a, hg b, e2]

end OVNS.Quant.Metric

end
