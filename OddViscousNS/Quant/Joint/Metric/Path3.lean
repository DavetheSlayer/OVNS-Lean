import OddViscousNS.Quant.Joint.Metric.HalfX2

/-!
# The energy identity on the actual path: three leaves (step J5, node N13, part 2)

The same as `PathTerm.lean`, `PathForm.lean`, for a family with three slow leaves and the outer heat
`L² + J² + P₁² + P₂² + P₃²` (`Q₃`: Body 33, "the exact third denominator").  `block_hasDeriv` is the
derivative of one term along a path of blocks, with any number of leaves inside the block.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

section Block

variable {r H : ℝ} {l j : Mode}

/-- One channel of a block. -/
def chC (B : Blk) (l j : Mode) (c e : Sgn) (G F : V3) : ℂ := inner ℂ G (hel c l (B (hel e j F)))

lemma chC_hasDeriv (c e : Sgn) {G F : ℝ → V3} {B : ℝ → Blk} {G' F' : V3} {B' : Blk} {A : Set ℝ}
    {x : ℝ} (hG : HasDerivWithinAt G G' A x) (hF : HasDerivWithinAt F F' A x)
    (hB : HasDerivWithinAt B B' A x) :
    HasDerivWithinAt (fun u => chC (B u) l j c e (G u) (F u))
      (chC (B x) l j c e G' (F x) + chC (B x) l j c e (G x) F' + chC B' l j c e (G x) (F x)) A x := by
  have h2 : HasDerivWithinAt (fun u => helL e j (F u)) (helL e j F') A x := hasDeriv_clm _ hF
  have h3 := hasDeriv_bil (ContinuousLinearMap.id ℂ Blk) hB h2
  have h4 := hasDeriv_clm (helL c l) h3
  have h5 := HasDerivWithinAt.inner ℂ hG h4
  refine h5.congr_deriv ?_
  simp only [ContinuousLinearMap.id_apply, map_add, inner_add_right, helL_apply, chC]
  ring

variable {L2 J2 K : ℝ}

/-- **One term, along a path of blocks.** -/
theorem block_hasDeriv (hH : H = L2 + J2 + K) (hH0 : 0 < H) {G F : ℝ → V3} {B : ℝ → Blk}
    {NG NF : V3} {NB : Blk} {A : Set ℝ} {x : ℝ}
    (hG : HasDerivWithinAt G (((-L2 : ℝ) : ℂ) • G x + NG) A x)
    (hF : HasDerivWithinAt F (((-J2 : ℝ) : ℂ) • F x + NF) A x)
    (hB : HasDerivWithinAt B (((-K : ℝ) : ℂ) • B x + NB) A x) :
    HasDerivWithinAt (fun u => ∑ c : Sgn, ∑ e : Sgn, resolv (-1) H (r * outerPhi c e l j) *
        (chP r u (outerPhi c e l j) * chC (B u) l j c e (G u) (F u)))
      (∑ c : Sgn, ∑ e : Sgn, (chP r x (outerPhi c e l j) * chC (B x) l j c e (G x) (F x) +
        resolv (-1) H (r * outerPhi c e l j) * (chP r x (outerPhi c e l j) *
          (chC (B x) l j c e NG (F x) + chC (B x) l j c e (G x) NF +
            chC NB l j c e (G x) (F x))))) A x := by
  refine HasDerivWithinAt.fun_sum (u := Finset.univ) fun c _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun e _ => ?_
  have h1 := (chP_hasDeriv r (outerPhi c e l j) (A := A) x).mul
    (chC_hasDeriv (l := l) (j := j) c e hG hF hB)
  have h2 := h1.const_mul (resolv (-1) H (r * outerPhi c e l j))
  refine h2.congr_deriv ?_
  have hne := Quant.resolv_den_ne_zero (ε := -1) (Or.inr rfl) hH0.ne' (r * outerPhi c e l j)
  have e1 : resolv (-1) H (r * outerPhi c e l j) *
      (((-H : ℝ) : ℂ) + ((r * outerPhi c e l j : ℝ) : ℂ) * Complex.I) = 1 := by
    have e2 : (((-1 : ℝ) * H : ℝ) : ℂ) = ((-H : ℝ) : ℂ) := by push_cast; ring
    rw [e2] at hne
    rw [Quant.resolv, e2, one_div, inv_mul_cancel₀ hne]
  simp only [chC, map_add, map_smul, add_apply, smul_apply, hel_add, hel_smul, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  simp only [hH] at e1 ⊢
  set R := resolv (-1) (L2 + J2 + K) (r * outerPhi c e l j)
  set P := chP r x (outerPhi c e l j)
  push_cast at e1 ⊢
  linear_combination (P * inner ℂ (G x) (hel c l (B x (hel e j (F x))))) * e1

end Block

/-! ### The family -/

/-- The labels on which a block of three leaves can be nonzero. -/
def Act₃ (x : I4) : Prop := x.2.1 2 = 0 ∧ x.2.2.1 2 = 0 ∧ x.2.2.2 2 = 0 ∧ inJ x 2 ≠ 0

/-- The outer heat of three leaves. -/
def Hx₃ (x : I4) : ℝ :=
  absSq x.1 + absSq (inJ x) + absSq x.2.1 + absSq x.2.2.1 + absSq x.2.2.2

/-- A family of blocks with three slow leaves. -/
structure Fam3 where
  /-- The source. -/
  Sr : I4 → ℝ → V3 → V3 → V3 → Blk
  /-- The source at `τ = 0`: the two-leaf factor. -/
  A0 : I4 → V3 →L[ℂ] V3 →L[ℂ] Blk
  /-- The source at `τ = 0`: the last edge. -/
  E0 : I4 → V3 →L[ℂ] Blk
  /-- Covariance on the slow labels. -/
  cov : ∀ x : I4, x.2.1 2 = 0 → x.2.2.1 2 = 0 → x.2.2.2 2 = 0 →
    ∀ (τ : ℝ) (t v w : V3) (c e : Sgn) (y : V3),
    hel c x.1 (Sr x τ t v w (hel e (inJ x) y)) =
      Complex.exp (Complex.I * (τ * outerPhi c e x.1 (inJ x) : ℝ)) •
        hel c x.1 ((A0 x t v ∘L E0 x w) (hel e (inJ x) y))
  zero₁ : ∀ x τ v w, Sr x τ 0 v w = 0
  zero₂ : ∀ x τ t w, Sr x τ t 0 w = 0
  zero₃ : ∀ x τ t v, Sr x τ t v 0 = 0

namespace Fam3

variable (𝔉 : Fam3)

/-- A term of the form. -/
def T (r : ℝ) (x : I4) (G F t v w : V3) (τ : ℝ) : ℂ :=
  inner ℂ G (outerInv r (Hx₃ x) x.1 (inJ x) (𝔉.Sr x τ t v w) F)

/-- The form `⟨G, O(f, g, h) F⟩`. -/
def form (r τ : ℝ) (f g h G F : Field) : ℂ :=
  ∑' x : I4, 𝔉.T r x (G x.1) (F (inJ x)) (f x.2.1) (g x.2.2.1) (h x.2.2.2) τ

/-- A term of the source form. -/
def srcT (x : I4) (G F t v w : V3) (τ : ℝ) : ℂ :=
  inner ℂ G (leray x.1 (𝔉.Sr x τ t v w (leray (inJ x) F)))

/-- The source form. -/
def src (τ : ℝ) (f g h G F : Field) : ℂ :=
  ∑' x : I4, 𝔉.srcT x (G x.1) (F (inJ x)) (f x.2.1) (g x.2.2.1) (h x.2.2.2) τ

/-- The analysis of a family: the size of the source. -/
structure Bd (K : ℝ) : Prop where
  K0 : 0 ≤ K
  source : ∀ x, Act₃ x → ∀ (τ : ℝ) (t v w : V3), ‖𝔉.Sr x τ t v w‖ ≤
    K * (absk x.1 + absk x.2.1 + absk x.2.2.1 + absk x.2.2.2) * (‖t‖ * ‖v‖ * ‖w‖) * E3 x

variable {𝔉} {r : ℝ} {x : I4} {G F t v w : V3} {τ : ℝ}

lemma T_zero₁ (r : ℝ) (x : I4) (G F v w : V3) (τ : ℝ) : 𝔉.T r x G F 0 v w τ = 0 := by
  simp [T, 𝔉.zero₁, outerInv_zero]

lemma T_zero₂ (r : ℝ) (x : I4) (G F t w : V3) (τ : ℝ) : 𝔉.T r x G F t 0 w τ = 0 := by
  simp [T, 𝔉.zero₂, outerInv_zero]

lemma T_zero₃ (r : ℝ) (x : I4) (G F t v : V3) (τ : ℝ) : 𝔉.T r x G F t v 0 τ = 0 := by
  simp [T, 𝔉.zero₃, outerInv_zero]

lemma T_zero_F (r : ℝ) (x : I4) (G t v w : V3) (τ : ℝ) : 𝔉.T r x G 0 t v w τ = 0 := by
  simp [T]

private lemma leray_zero (k : Mode) : leray k (0 : V3) = 0 := by
  simpa using leray_smul k 0 (0 : V3)

lemma srcT_zero₁ (x : I4) (G F v w : V3) (τ : ℝ) : 𝔉.srcT x G F 0 v w τ = 0 := by
  simp [srcT, 𝔉.zero₁, leray_zero]

lemma srcT_zero₂ (x : I4) (G F t w : V3) (τ : ℝ) : 𝔉.srcT x G F t 0 w τ = 0 := by
  simp [srcT, 𝔉.zero₂, leray_zero]

lemma srcT_zero₃ (x : I4) (G F t v : V3) (τ : ℝ) : 𝔉.srcT x G F t v 0 τ = 0 := by
  simp [srcT, 𝔉.zero₃, leray_zero]

lemma srcT_zero_F (x : I4) (G t v w : V3) (τ : ℝ) : 𝔉.srcT x G 0 t v w τ = 0 := by
  simp [srcT, leray_zero]

/-! ### The expansion in channels -/

/-- The channel core at `τ = 0`. -/
def core₃ (𝔉 : Fam3) (x : I4) (c e : Sgn) (G F t v w : V3) : ℂ :=
  chC (𝔉.A0 x t v ∘L 𝔉.E0 x w) x.1 (inJ x) c e G F

lemma T_eq (hc : x.2.1 2 = 0 ∧ x.2.2.1 2 = 0 ∧ x.2.2.2 2 = 0) (G F t v w : V3) (u : ℝ) :
    𝔉.T r x G F t v w (r * u) = ∑ c : Sgn, ∑ e : Sgn,
      resolv (-1) (Hx₃ x) (r * outerPhi c e x.1 (inJ x)) * (chP r u (outerPhi c e x.1 (inJ x)) *
        core₃ 𝔉 x c e G F t v w) := by
  rw [T, inner_outerInv]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  rw [𝔉.cov x hc.1 hc.2.1 hc.2.2, inner_smul_right]
  rfl

lemma srcT_eq₃ (hc : x.2.1 2 = 0 ∧ x.2.2.1 2 = 0 ∧ x.2.2.2 2 = 0) (G F t v w : V3) (u : ℝ) :
    𝔉.srcT x G F t v w (r * u) = ∑ c : Sgn, ∑ e : Sgn,
      chP r u (outerPhi c e x.1 (inJ x)) * core₃ 𝔉 x c e G F t v w := by
  rw [srcT, inner_leray_leray]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  rw [𝔉.cov x hc.1 hc.2.1 hc.2.2, inner_smul_right]
  rfl

/-- **One term of the identity**, three leaves. -/
theorem term_hasDeriv₃ (hH0 : 0 < Hx₃ x) (hc : x.2.1 2 = 0 ∧ x.2.2.1 2 = 0 ∧ x.2.2.2 2 = 0)
    {G F t v w : ℝ → V3} {NG NF Nt Nv Nw : V3} {A : Set ℝ} {y : ℝ}
    (hG : HasDerivWithinAt G (((-absSq x.1 : ℝ) : ℂ) • G y + NG) A y)
    (hF : HasDerivWithinAt F (((-absSq (inJ x) : ℝ) : ℂ) • F y + NF) A y)
    (ht : HasDerivWithinAt t (((-absSq x.2.1 : ℝ) : ℂ) • t y + Nt) A y)
    (hv : HasDerivWithinAt v (((-absSq x.2.2.1 : ℝ) : ℂ) • v y + Nv) A y)
    (hw : HasDerivWithinAt w (((-absSq x.2.2.2 : ℝ) : ℂ) • w y + Nw) A y) :
    HasDerivWithinAt (fun u => 𝔉.T r x (G u) (F u) (t u) (v u) (w u) (r * u))
      (𝔉.srcT x (G y) (F y) (t y) (v y) (w y) (r * y) +
        𝔉.T r x NG (F y) (t y) (v y) (w y) (r * y) + 𝔉.T r x (G y) NF (t y) (v y) (w y) (r * y) +
        𝔉.T r x (G y) (F y) Nt (v y) (w y) (r * y) + 𝔉.T r x (G y) (F y) (t y) Nv (w y) (r * y) +
        𝔉.T r x (G y) (F y) (t y) (v y) Nw (r * y)) A y := by
  have h1 := hasDeriv_bil (𝔉.A0 x) ht hv
  have h2 : HasDerivWithinAt (fun u => 𝔉.E0 x (w u))
      (𝔉.E0 x (((-absSq x.2.2.2 : ℝ) : ℂ) • w y + Nw)) A y := hasDeriv_clm (𝔉.E0 x) hw
  have h3 := hasDeriv_bil (ContinuousLinearMap.compL ℂ V3 V3 V3) h1 h2
  have hB : HasDerivWithinAt (fun u => 𝔉.A0 x (t u) (v u) ∘L 𝔉.E0 x (w u))
      (((-(absSq x.2.1 + absSq x.2.2.1 + absSq x.2.2.2) : ℝ) : ℂ) •
          (𝔉.A0 x (t y) (v y) ∘L 𝔉.E0 x (w y)) +
        (𝔉.A0 x Nt (v y) ∘L 𝔉.E0 x (w y) + 𝔉.A0 x (t y) Nv ∘L 𝔉.E0 x (w y) +
          𝔉.A0 x (t y) (v y) ∘L 𝔉.E0 x Nw)) A y := by
    refine h3.congr_deriv ?_
    ext1 q
    simp only [ContinuousLinearMap.compL_apply, map_add, map_smul, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply]
    push_cast
    module
  have hH : Hx₃ x = absSq x.1 + absSq (inJ x) +
      (absSq x.2.1 + absSq x.2.2.1 + absSq x.2.2.2) := by
    unfold Hx₃
    ring
  have hmain := block_hasDeriv (r := r) (l := x.1) (j := inJ x) hH hH0 hG hF hB
  have hexp : (fun u => 𝔉.T r x (G u) (F u) (t u) (v u) (w u) (r * u)) = fun u =>
      ∑ c : Sgn, ∑ e : Sgn, resolv (-1) (Hx₃ x) (r * outerPhi c e x.1 (inJ x)) *
        (chP r u (outerPhi c e x.1 (inJ x)) *
          chC (𝔉.A0 x (t u) (v u) ∘L 𝔉.E0 x (w u)) x.1 (inJ x) c e (G u) (F u)) :=
    funext fun u => T_eq hc _ _ _ _ _ u
  rw [hexp]
  refine hmain.congr_deriv ?_
  simp only [T_eq hc, srcT_eq₃ hc, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  simp only [core₃, chC, add_apply, hel_add, inner_add_right]
  ring

end Fam3

end OVNS.Quant.Metric

end
