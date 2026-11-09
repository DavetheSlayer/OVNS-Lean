import OddViscousNS.Quant.Joint.Quartic.Tri

/-!
# The fourth correction: definition (step J5, node N11)

Bodies 34, 35 (LOCAL488, LOCAL496).  The high mixed source `Q_hi(S, F)` of the near differential
`D_j^N(F; h)` is removed by a quartic with the actual ancestors `s, l, q, e`:

`x = (p, q, s)`, `l = p − s` (`inL`), `e = −(p + q)` (`outE`).  The triad `(p, q, e)` is the outer
near triad, with `p = h = s + l` the intermediate of Body 34.

* `hiMu s l = 1 − lowM s l` is the exact complement of the low last edge of `LowPass.lean`
  (`Qlo`), so `Qphase = Qlo + Qhi`.  It is in `[0, 1]`, and its support is in `|s| > 16 |l|`
  (`hi_sep`): `H₀ = 16`.
* `coreQ`: the literal cyclic coefficient `cyc3 j` of the outer triad at its outer phase `Φ` and near
  mask, with the source edge at `τ = 0` in the first slot.  This is the coefficient `C` of Body 34:
  "the literal signed cyclic static coefficient, with its original old denominators, original
  projections, and actual `0 < |Φ| < 1` mask".
* `psiQ d b c x = λ_d(l) + λ_b(q) + λ_c(e)`: the total phase `Ψ`; "the intermediate phase canceled and
  the slow dispersion zero".  `heatQ x = |s|² + |l|² + |q|² + |e|²`: "the four actual ancestral heat
  lengths.  It has no intermediate `h` heat".
* `srcQ`, `termQ`: one label of the source and of the quartic.  `J4F`, `Q4F`: the forms on fields.

**Directed form.**  As for `Q₃`, nothing Hermitian is written.  The energy term is `Re (Q4F …)`:
the sum runs over all labels and both orientations are in it, so the conjugate term of Body 34 is the
reflected label.  Since `d/dt` acts on `Q4F` itself, a real part is only taken at the very end.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

/-! ### A. The labels and the mask -/

/-- The labels `(p, q, s)`. -/
abbrev L4 := Mode × Mode × Mode

/-- The inner fast ancestor `l = p − s`. -/
def inL (x : L4) : Mode := x.1 - x.2.2

/-- The third outer leg `e = −(p + q)`. -/
def outE (x : L4) : Mode := -(x.1 + x.2.1)

/-- The total phase `Ψ = λ_d(l) + λ_b(q) + λ_c(e)`. -/
def psiQ (d b c : Sgn) (x : L4) : ℝ := lam d (inL x) + lam b x.2.1 + lam c (outE x)

/-- The four ancestral heats. -/
def heatQ (x : L4) : ℝ := absSq x.2.2 + absSq (inL x) + absSq x.2.1 + absSq (outE x)

/-- The high complement of the low last edge. -/
def hiMu (s l : Mode) : ℝ := 1 - lowM s l

lemma hiMu_nonneg (s l : Mode) : 0 ≤ hiMu s l := by
  have := lowM_le_one s l
  unfold hiMu
  linarith

lemma hiMu_le_one (s l : Mode) : hiMu s l ≤ 1 := by
  have := lowM_nonneg s l
  unfold hiMu
  linarith

lemma hiMu_neg (s l : Mode) : hiMu (-s) (-l) = hiMu s l := by
  simp only [hiMu, lowM, bnd_neg, chiM_neg]

/-- **The support of the high complement**: `|s| > 16 |l|`. -/
lemma hi_sep {s l : Mode} (h : hiMu s l ≠ 0) : 16 * absk l < absk s := by
  have h1 : ¬ absk s ≤ 2 ^ (bnd l + 5) := fun hle => h (by
    unfold hiMu lowM
    rw [chiM_one hle, sub_self])
  have h2 := lt_two_pow_bnd l
  have h3 : (2 : ℝ) ^ (bnd l + 5) = 16 * 2 ^ (bnd l + 1) := by ring
  rw [h3] at h1
  linarith [not_le.1 h1]

/-- The multiplier of `Q_hi`. -/
def hiM (τ : ℝ) : Mult := fun a b c p q => ((hiMu p q : ℝ) : ℂ) * phaseM τ a b c p q

lemma hiM_bdd (τ : ℝ) : (hiM τ).Bdd := fun a b c p q => by
  rw [hiM, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hiMu_nonneg p q)]
  exact (mul_le_mul (hiMu_le_one p q) (phaseM_bdd τ a b c p q) (norm_nonneg _)
    zero_le_one).trans_eq (one_mul 1)

lemma hiM_real (τ : ℝ) : (hiM τ).Real := fun a b c p q => by
  simp only [hiM, hiMu_neg, map_mul, Complex.conj_ofReal, phaseM_real τ a b c p q]

/-- **The high mixed source** `Q_hi(S, F)`. -/
def Qhi (τ : ℝ) (S F : Field) : Field := Qm (hiM τ) S F

/-- An edge of the high source. -/
lemma blk_hiM (τ : ℝ) (s p l : Mode) (v : V3) :
    blk (hiM τ) s p l v = ((hiMu s l : ℝ) : ℂ) • blk (phaseM τ) s p l v := by
  refine ContinuousLinearMap.ext fun w => ?_
  simp only [smul_apply, blk_apply, Finset.smul_sum, hiM, smul_smul]

/-- The size of an edge. -/
lemma norm_blk_hiM (τ : ℝ) {s p l : Mode} (hk : s + l = p) (v : V3) :
    ‖blk (hiM τ) s p l v‖ ≤ hiMu s l * (8 * absk p * ‖v‖) := by
  rw [blk_hiM, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hiMu_nonneg s l)]
  exact mul_le_mul_of_nonneg_left (norm_blk_le (phaseM_bdd τ) hk v) (hiMu_nonneg s l)

/-! ### B. The trilinear algebra -/

section Algebra

variable {p q : Mode}

lemma bd_add_left (a a' b : V3) : bd (a + a') b = bd a b + bd a' b := by
  simp only [bd, PiLp.add_apply]
  ring

lemma bd_smul_left (c : ℂ) (a b : V3) : bd (c • a) b = c * bd a b := by
  simp only [bd, PiLp.smul_apply, smul_eq_mul]
  ring

lemma bd_add_right (a b b' : V3) : bd a (b + b') = bd a b + bd a b' := by
  simp only [bd, PiLp.add_apply]
  ring

lemma bd_smul_right (c : ℂ) (a b : V3) : bd a (c • b) = c * bd a b := by
  simp only [bd, PiLp.smul_apply, smul_eq_mul]
  ring

lemma bd_isBil : IsBil bd := ⟨bd_add_left, bd_smul_left, bd_add_right, bd_smul_right⟩

/-- The pairing with a mode, as an operator. -/
def dotL (k : Mode) : V3 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => dotM a k
      map_add' := fun a b => dotM_add a b k
      map_smul' := fun c a => dotM_smul c a k }

@[simp] lemma dotL_apply (k : Mode) (a : V3) : dotL k a = dotM a k := rfl

lemma tau_add₁ (A A' B C : V3) : tau p q (A + A') B C = tau p q A B C + tau p q A' B C := by
  simp only [tau, dotM_add, bd_add_left]
  ring

lemma tau_smul₁ (c : ℂ) (A B C : V3) : tau p q (c • A) B C = c * tau p q A B C := by
  simp only [tau, dotM_smul, bd_smul_left]
  ring

lemma tau_add₂ (A B B' C : V3) : tau p q A (B + B') C = tau p q A B C + tau p q A B' C := by
  simp only [tau, dotM_add, bd_add_left]
  ring

lemma tau_smul₂ (c : ℂ) (A B C : V3) : tau p q A (c • B) C = c * tau p q A B C := by
  simp only [tau, dotM_smul, bd_smul_left]
  ring

lemma tau_add₃ (A B C C' : V3) : tau p q A B (C + C') = tau p q A B C + tau p q A B C' := by
  simp only [tau, bd_add_right]
  ring

lemma tau_smul₃ (c : ℂ) (A B C : V3) : tau p q A B (c • C) = c * tau p q A B C := by
  simp only [tau, bd_smul_right]
  ring

/-- The bilinear form `bd`, as an operator. -/
def bdB : V3 →L[ℂ] V3 →L[ℂ] ℂ := bilCLM bd_isBil

@[simp] lemma bdB_apply (a b : V3) : bdB a b = bd a b := rfl

/-- `tau` along a path. -/
lemma tau_hasDeriv {A B C : ℝ → V3} {A' B' C' : V3} {s : Set ℝ} {y : ℝ}
    (hA : HasDerivWithinAt A A' s y) (hB : HasDerivWithinAt B B' s y)
    (hC : HasDerivWithinAt C C' s y) :
    HasDerivWithinAt (fun u => tau p q (A u) (B u) (C u))
      (tau p q A' (B y) (C y) + tau p q (A y) B' (C y) + tau p q (A y) (B y) C') s y := by
  have d1 : HasDerivWithinAt (fun u => dotL q (A u)) (dotL q A') s y := hasDeriv_clm _ hA
  have d2 : HasDerivWithinAt (fun u => dotL p (B u)) (dotL p B') s y := hasDeriv_clm _ hB
  have b1 : HasDerivWithinAt (fun u => bdB (B u) (C u)) (bdB B' (C y) + bdB (B y) C') s y :=
    hasDeriv_bil bdB hB hC
  have b2 : HasDerivWithinAt (fun u => bdB (A u) (C u)) (bdB A' (C y) + bdB (A y) C') s y :=
    hasDeriv_bil bdB hA hC
  have h := ((d1.mul b1).add (d2.mul b2)).const_mul ((1 / 2) * Complex.I)
  refine h.congr_deriv ?_
  simp only [tau, bdB_apply, dotL_apply]
  ring

/-- A continuous bilinear operator of continuous paths. -/
lemma bil_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {B C : ℝ → V3}
    {s : Set ℝ} (hB : ContinuousOn B s) (hC : ContinuousOn C s) (B0 : V3 →L[ℂ] V3 →L[ℂ] E) :
    ContinuousOn (fun u => B0 (B u) (C u)) s :=
  B0.continuous₂.comp_continuousOn (hB.prodMk hC)

/-- `tau` is continuous. -/
lemma tau_continuousOn {A B C : ℝ → V3} {s : Set ℝ} (hA : ContinuousOn A s)
    (hB : ContinuousOn B s) (hC : ContinuousOn C s) :
    ContinuousOn (fun u => tau p q (A u) (B u) (C u)) s := by
  have d1 : ContinuousOn (fun u => dotL q (A u)) s := (dotL q).continuous.comp_continuousOn hA
  have d2 : ContinuousOn (fun u => dotL p (B u)) s := (dotL p).continuous.comp_continuousOn hB
  have b1 := bil_continuousOn hB hC bdB
  have b2 := bil_continuousOn hA hC bdB
  have e : (fun u => tau p q (A u) (B u) (C u)) = fun u =>
      (1 / 2) * Complex.I * (dotL q (A u) * bdB (B u) (C u) + dotL p (B u) * bdB (A u) (C u)) :=
    funext fun u => by simp only [tau, bdB_apply, dotL_apply]
  rw [e]
  exact ((d1.mul b1).add (d2.mul b2)).const_mul ((1 / 2) * Complex.I)

variable {j : ℕ} {ε z : ℝ} {ℓ0 ℓ1 ℓ2 : Mode} {s0 s1 s2 : Sgn}

lemma cyc3_add₀ (a a' v1 v2 : V3) : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 (a + a') v1 v2 =
    cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 a v1 v2 + cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 a' v1 v2 := by
  simp only [cyc3, hel_add, tau_add₁, tau_add₂, tau_add₃]
  ring

lemma cyc3_smul₀ (c : ℂ) (a v1 v2 : V3) : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 (c • a) v1 v2 =
    c * cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 a v1 v2 := by
  simp only [cyc3, hel_smul, tau_smul₁, tau_smul₂, tau_smul₃]
  ring

lemma cyc3_add₁ (v0 a a' v2 : V3) : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 (a + a') v2 =
    cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 a v2 + cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 a' v2 := by
  simp only [cyc3, hel_add, tau_add₁, tau_add₂, tau_add₃]
  ring

lemma cyc3_smul₁ (c : ℂ) (v0 a v2 : V3) : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 (c • a) v2 =
    c * cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 a v2 := by
  simp only [cyc3, hel_smul, tau_smul₁, tau_smul₂, tau_smul₃]
  ring

lemma cyc3_add₂ (v0 v1 a a' : V3) : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 (a + a') =
    cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 a + cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 a' := by
  simp only [cyc3, hel_add, tau_add₁, tau_add₂, tau_add₃]
  ring

lemma cyc3_smul₂ (c : ℂ) (v0 v1 a : V3) : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 (c • a) =
    c * cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 a := by
  simp only [cyc3, hel_smul, tau_smul₁, tau_smul₂, tau_smul₃]
  ring

/-- The cyclic sum along a path. -/
lemma cyc3_hasDeriv {a b c : ℝ → V3} {a' b' c' : V3} {s : Set ℝ} {y : ℝ}
    (ha : HasDerivWithinAt a a' s y) (hb : HasDerivWithinAt b b' s y)
    (hc : HasDerivWithinAt c c' s y) :
    HasDerivWithinAt (fun u => cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 (a u) (b u) (c u))
      (cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 a' (b y) (c y) +
        cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 (a y) b' (c y) +
        cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 (a y) (b y) c') s y := by
  have h0 : HasDerivWithinAt (fun u => hel s0 ℓ0 (a u)) (hel s0 ℓ0 a') s y :=
    hasDeriv_clm (helL s0 ℓ0) ha
  have h1 : HasDerivWithinAt (fun u => hel s1 ℓ1 (b u)) (hel s1 ℓ1 b') s y :=
    hasDeriv_clm (helL s1 ℓ1) hb
  have h2 : HasDerivWithinAt (fun u => hel s2 ℓ2 (c u)) (hel s2 ℓ2 c') s y :=
    hasDeriv_clm (helL s2 ℓ2) hc
  have t1 := (tau_hasDeriv (p := ℓ0) (q := ℓ1) h0 h1 h2).mul_const (fres j ε z (absSq ℓ2))
  have t2 := (tau_hasDeriv (p := ℓ1) (q := ℓ2) h1 h2 h0).mul_const (fres j ε z (absSq ℓ0))
  have t3 := (tau_hasDeriv (p := ℓ2) (q := ℓ0) h2 h0 h1).mul_const (fres j ε z (absSq ℓ1))
  refine ((t1.add t2).add t3).congr_deriv ?_
  simp only [cyc3]
  ring

/-- The cyclic sum is continuous. -/
lemma cyc3_continuousOn {a b c : ℝ → V3} {s : Set ℝ} (ha : ContinuousOn a s) (hb : ContinuousOn b s)
    (hc : ContinuousOn c s) :
    ContinuousOn (fun u => cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 (a u) (b u) (c u)) s := by
  have h0 : ContinuousOn (fun u => hel s0 ℓ0 (a u)) s :=
    (helL s0 ℓ0).continuous.comp_continuousOn ha
  have h1 : ContinuousOn (fun u => hel s1 ℓ1 (b u)) s :=
    (helL s1 ℓ1).continuous.comp_continuousOn hb
  have h2 : ContinuousOn (fun u => hel s2 ℓ2 (c u)) s :=
    (helL s2 ℓ2).continuous.comp_continuousOn hc
  have t1 : ContinuousOn (fun u => tau ℓ0 ℓ1 (hel s0 ℓ0 (a u)) (hel s1 ℓ1 (b u))
      (hel s2 ℓ2 (c u)) * fres j ε z (absSq ℓ2)) s :=
    (tau_continuousOn h0 h1 h2).mul continuousOn_const
  have t2 : ContinuousOn (fun u => tau ℓ1 ℓ2 (hel s1 ℓ1 (b u)) (hel s2 ℓ2 (c u))
      (hel s0 ℓ0 (a u)) * fres j ε z (absSq ℓ0)) s :=
    (tau_continuousOn h1 h2 h0).mul continuousOn_const
  have t3 : ContinuousOn (fun u => tau ℓ2 ℓ0 (hel s2 ℓ2 (c u)) (hel s0 ℓ0 (a u))
      (hel s1 ℓ1 (b u)) * fres j ε z (absSq ℓ1)) s :=
    (tau_continuousOn h2 h0 h1).mul continuousOn_const
  exact (t1.add t2).add t3

/-- The cyclic sum vanishes with one of its vectors. -/
lemma cyc3_zero₀ (v1 v2 : V3) : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 0 v1 v2 = 0 := by
  have := cyc3_smul₀ (j := j) (ε := ε) (z := z) (ℓ0 := ℓ0) (ℓ1 := ℓ1) (ℓ2 := ℓ2) (s0 := s0)
    (s1 := s1) (s2 := s2) 0 0 v1 v2
  simpa using this

lemma cyc3_zero₁ (v0 v2 : V3) : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 0 v2 = 0 := by
  have := cyc3_smul₁ (j := j) (ε := ε) (z := z) (ℓ0 := ℓ0) (ℓ1 := ℓ1) (ℓ2 := ℓ2) (s0 := s0)
    (s1 := s1) (s2 := s2) 0 v0 0 v2
  simpa using this

lemma cyc3_zero₂ (v0 v1 : V3) : cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v0 v1 0 = 0 := by
  have := cyc3_smul₂ (j := j) (ε := ε) (z := z) (ℓ0 := ℓ0) (ℓ1 := ℓ1) (ℓ2 := ℓ2) (s0 := s0)
    (s1 := s1) (s2 := s2) 0 v0 v1 0
  simpa using this

end Algebra

/-! ### C. The coefficient -/

/-- The source edge at `τ = 0`, helicity `d` at the inner fast ancestor. -/
def edgeQ (x : L4) (d : Sgn) (t w : V3) : V3 :=
  blk (hiM 0) x.2.2 x.1 (inL x) t (hel d (inL x) w)

lemma edgeQ_isBil (x : L4) (d : Sgn) : IsBil (edgeQ x d) where
  add_l v v' w := by simp only [edgeQ, blk_add_leaf, add_apply]
  smul_l c v w := by simp only [edgeQ, blk_smul_leaf, smul_apply]
  add_r v w w' := by simp only [edgeQ, hel_add, map_add]
  smul_r c v w := by simp only [edgeQ, hel_smul, map_smul]

/-- The edge as an operator. -/
def edgeB (x : L4) (d : Sgn) : V3 →L[ℂ] V3 →L[ℂ] V3 := bilCLM (edgeQ_isBil x d)

@[simp] lemma edgeB_apply (x : L4) (d : Sgn) (t w : V3) : edgeB x d t w = edgeQ x d t w := rfl

lemma edgeQ_zero_l (x : L4) (d : Sgn) (w : V3) : edgeQ x d 0 w = 0 := by
  have := (edgeQ_isBil x d).smul_l 0 0 w
  simpa using this

lemma edgeQ_zero_r (x : L4) (d : Sgn) (t : V3) : edgeQ x d t 0 = 0 := by
  have := (edgeQ_isBil x d).smul_r 0 t 0
  simpa using this

open Classical in
/-- **The coefficient** of the near differential at the labels `x`, helicities `(d, a, b, c)`, at
weight `j`: the cyclic sum of the outer triad on its near mask, the source edge in the first slot. -/
def coreQ (j : ℕ) (r : ℝ) (x : L4) (d a b c : Sgn) (t w u v : V3) : ℂ :=
  if NearT a b c x.1 x.2.1 then
    cyc3 j (-1) (r * Phi a b c x.1 x.2.1) x.1 x.2.1 (outE x) a b c (edgeQ x d t w) u v
  else 0

/-- The phase of a channel. -/
def chQ (τ : ℝ) (d b c : Sgn) (x : L4) : ℂ := Complex.exp (Complex.I * (τ * psiQ d b c x : ℝ))

lemma norm_chQ (τ : ℝ) (d b c : Sgn) (x : L4) : ‖chQ τ d b c x‖ = 1 := by
  rw [chQ, mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- One label of the source. -/
def srcQ (j : ℕ) (r : ℝ) (x : L4) (τ : ℝ) (t w u v : V3) : ℂ :=
  ∑ d : Sgn, ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, chQ τ d b c x * coreQ j r x d a b c t w u v

/-- One label of the quartic: "`−C/[−Σ₄ + i r Ψ]`", without the sign of the source. -/
def termQ (j : ℕ) (r : ℝ) (x : L4) (τ : ℝ) (t w u v : V3) : ℂ :=
  ∑ d : Sgn, ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
    resolv (-1) (heatQ x) (r * psiQ d b c x) * (chQ τ d b c x * coreQ j r x d a b c t w u v)

/-- **The source form** on fields. -/
def J4F (j : ℕ) (r τ : ℝ) (T W U V : Field) : ℂ :=
  ∑' x : L4, srcQ j r x τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))

/-- **The quartic form** on fields, `T` in the slow slot, `W` in the inner fast slot, `U, V` in the
two outer slots. -/
def Q4F (j : ℕ) (r τ : ℝ) (T W U V : Field) : ℂ :=
  ∑' x : L4, termQ j r x τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))

section Core

variable {j : ℕ} {r : ℝ} {x : L4} {d a b c : Sgn}

lemma coreQ_heat₁ (g : ℂ) (t N w u v : V3) : coreQ j r x d a b c (g • t + N) w u v =
    g * coreQ j r x d a b c t w u v + coreQ j r x d a b c N w u v := by
  have h := edgeQ_isBil x d
  unfold coreQ
  split_ifs
  · rw [h.add_l, h.smul_l, cyc3_add₀, cyc3_smul₀]
  · simp

lemma coreQ_heat₂ (g : ℂ) (t w N u v : V3) : coreQ j r x d a b c t (g • w + N) u v =
    g * coreQ j r x d a b c t w u v + coreQ j r x d a b c t N u v := by
  have h := edgeQ_isBil x d
  unfold coreQ
  split_ifs
  · rw [h.add_r, h.smul_r, cyc3_add₀, cyc3_smul₀]
  · simp

lemma coreQ_heat₃ (g : ℂ) (t w u N v : V3) : coreQ j r x d a b c t w (g • u + N) v =
    g * coreQ j r x d a b c t w u v + coreQ j r x d a b c t w N v := by
  unfold coreQ
  split_ifs
  · rw [cyc3_add₁, cyc3_smul₁]
  · simp

lemma coreQ_heat₄ (g : ℂ) (t w u v N : V3) : coreQ j r x d a b c t w u (g • v + N) =
    g * coreQ j r x d a b c t w u v + coreQ j r x d a b c t w u N := by
  unfold coreQ
  split_ifs
  · rw [cyc3_add₂, cyc3_smul₂]
  · simp

lemma coreQ_zero₁ (w u v : V3) : coreQ j r x d a b c 0 w u v = 0 := by
  unfold coreQ
  split_ifs
  · rw [edgeQ_zero_l, cyc3_zero₀]
  · rfl

lemma coreQ_zero₂ (t u v : V3) : coreQ j r x d a b c t 0 u v = 0 := by
  unfold coreQ
  split_ifs
  · rw [edgeQ_zero_r, cyc3_zero₀]
  · rfl

lemma coreQ_zero₃ (t w v : V3) : coreQ j r x d a b c t w 0 v = 0 := by
  unfold coreQ
  split_ifs
  · rw [cyc3_zero₁]
  · rfl

lemma coreQ_zero₄ (t w u : V3) : coreQ j r x d a b c t w u 0 = 0 := by
  unfold coreQ
  split_ifs
  · rw [cyc3_zero₂]
  · rfl

/-- The coefficient along a path. -/
lemma coreQ_hasDeriv {t w u v : ℝ → V3} {t' w' u' v' : V3} {A : Set ℝ} {y : ℝ}
    (ht : HasDerivWithinAt t t' A y) (hw : HasDerivWithinAt w w' A y)
    (hu : HasDerivWithinAt u u' A y) (hv : HasDerivWithinAt v v' A y) :
    HasDerivWithinAt (fun τ => coreQ j r x d a b c (t τ) (w τ) (u τ) (v τ))
      (coreQ j r x d a b c t' (w y) (u y) (v y) + coreQ j r x d a b c (t y) w' (u y) (v y) +
        coreQ j r x d a b c (t y) (w y) u' (v y) + coreQ j r x d a b c (t y) (w y) (u y) v')
      A y := by
  by_cases hN : NearT a b c x.1 x.2.1
  · have hE : HasDerivWithinAt (fun τ => edgeB x d (t τ) (w τ))
        (edgeB x d t' (w y) + edgeB x d (t y) w') A y := hasDeriv_bil (edgeB x d) ht hw
    have h := cyc3_hasDeriv (j := j) (ε := -1) (z := r * Phi a b c x.1 x.2.1) (ℓ0 := x.1)
      (ℓ1 := x.2.1) (ℓ2 := outE x) (s0 := a) (s1 := b) (s2 := c) hE hu hv
    simp only [coreQ, hN, ite_true]
    simp only [edgeB_apply, cyc3_add₀] at h
    exact h
  · simp only [coreQ, hN, ite_false, add_zero]
    exact hasDerivWithinAt_const _ _ _

/-- The coefficient along continuous paths. -/
lemma coreQ_continuousOn {t w u v : ℝ → V3} {A : Set ℝ} (ht : ContinuousOn t A)
    (hw : ContinuousOn w A) (hu : ContinuousOn u A) (hv : ContinuousOn v A) :
    ContinuousOn (fun τ => coreQ j r x d a b c (t τ) (w τ) (u τ) (v τ)) A := by
  by_cases hN : NearT a b c x.1 x.2.1
  · simp only [coreQ, hN, ite_true]
    have hE : ContinuousOn (fun τ => edgeB x d (t τ) (w τ)) A := bil_continuousOn ht hw (edgeB x d)
    simp only [edgeB_apply] at hE
    exact cyc3_continuousOn hE hu hv
  · simp only [coreQ, hN, ite_false]
    exact continuousOn_const

end Core

/-- `(−H + i z) · 1/(−H + i z) = 1`. -/
lemma resolv_mul {H z : ℝ} (hH : 0 < H) :
    resolv (-1) H z * (((-H : ℝ) : ℂ) + (z : ℂ) * Complex.I) = 1 := by
  have hne := Quant.resolv_den_ne_zero (ε := -1) (Or.inr rfl) hH.ne' z
  have e2 : (((-1 : ℝ) * H : ℝ) : ℂ) = ((-H : ℝ) : ℂ) := by push_cast; ring
  rw [e2] at hne
  rw [Quant.resolv, e2, one_div, inv_mul_cancel₀ hne]

lemma chQ_eq (r u : ℝ) (d b c : Sgn) (x : L4) : chQ (r * u) d b c x = chP r u (psiQ d b c x) := rfl

/-- **One label of the identity**: the heat of the four ancestors and the total phase cancel the
denominator, and the four insertions remain. -/
theorem termQ_hasDeriv {j : ℕ} {r : ℝ} {x : L4} {t w u v : ℝ → V3} {Nt Nw Nu Nv : V3} {A : Set ℝ}
    {y : ℝ} (ht : HasDerivWithinAt t (((-absSq x.2.2 : ℝ) : ℂ) • t y + Nt) A y)
    (hw : HasDerivWithinAt w (((-absSq (inL x) : ℝ) : ℂ) • w y + Nw) A y)
    (hu : HasDerivWithinAt u (((-absSq x.2.1 : ℝ) : ℂ) • u y + Nu) A y)
    (hv : HasDerivWithinAt v (((-absSq (outE x) : ℝ) : ℂ) • v y + Nv) A y) :
    HasDerivWithinAt (fun τ => termQ j r x (r * τ) (t τ) (w τ) (u τ) (v τ))
      (srcQ j r x (r * y) (t y) (w y) (u y) (v y) + termQ j r x (r * y) Nt (w y) (u y) (v y) +
        termQ j r x (r * y) (t y) Nw (u y) (v y) + termQ j r x (r * y) (t y) (w y) Nu (v y) +
        termQ j r x (r * y) (t y) (w y) (u y) Nv) A y := by
  simp only [termQ, srcQ, ← Finset.sum_add_distrib]
  refine HasDerivWithinAt.fun_sum (u := Finset.univ) fun d _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun b _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun c _ => ?_
  by_cases hN : NearT a b c x.1 x.2.1
  · have hH : 0 < heatQ x := by
      have hk : outE x ≠ 0 := neg_ne_zero.2 hN.1
      have h1 := one_le_absSq hk
      have h2 := absSq_nonneg x.2.2
      have h3 := absSq_nonneg (inL x)
      have h4 := absSq_nonneg x.2.1
      unfold heatQ
      linarith
    have hc := coreQ_hasDeriv (j := j) (r := r) (x := x) (d := d) (a := a) (b := b) (c := c)
      ht hw hu hv
    have hP := chP_hasDeriv r (psiQ d b c x) (A := A) y
    have hm := (hP.mul hc).const_mul (resolv (-1) (heatQ x) (r * psiQ d b c x))
    refine hm.congr_deriv ?_
    simp only [coreQ_heat₁, coreQ_heat₂, coreQ_heat₃, coreQ_heat₄, chQ_eq]
    have e1 := resolv_mul (z := r * psiQ d b c x) hH
    set R := resolv (-1) (heatQ x) (r * psiQ d b c x)
    set P := chP r y (psiQ d b c x)
    set c0 := coreQ j r x d a b c (t y) (w y) (u y) (v y)
    have e2 : ((heatQ x : ℝ) : ℂ) = ((absSq x.2.2 : ℝ) : ℂ) + ((absSq (inL x) : ℝ) : ℂ) +
        ((absSq x.2.1 : ℝ) : ℂ) + ((absSq (outE x) : ℝ) : ℂ) := by
      simp only [heatQ]
      push_cast
      ring
    push_cast at e1 ⊢
    rw [e2] at e1
    linear_combination (P * c0) * e1
  · simp only [coreQ, hN, ite_false, mul_zero, add_zero]
    exact hasDerivWithinAt_const _ _ _

end OVNS.Quant.Quartic

end
