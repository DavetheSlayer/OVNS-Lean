import OddViscousNS.Quant.Joint.Metric.Channel

/-!
# The blocks are multilinear in their slow leaves (step J5, node N13)

The energy identity on the actual path differentiates a form in its slow leaves, so the blocks of
`Defs.lean` have to be multilinear maps of the leaf vectors, not functions of a `Field`.  Everything
here is finite-dimensional algebra: an edge is `ℂ`-linear in its leaf (`blk_add_leaf`, `blk_smul_leaf`),
including the reverse edges, where the two conjugations of `adjoint` and `conjV` cancel.

* `tR`, `zR`: the two sources `X₁𝓛 + 𝓛*X₁`, `X₁(B)` as functions of the two leaf vectors.
* `IsBil`, `bilCLM`: a bilinear map of leaf vectors as a continuous bilinear map.
* `hasDeriv_bil`: the product rule for a `ℂ`-bilinear map along a real path.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-- The block space. -/
abbrev Blk := V3 →L[ℂ] V3

/-! ### A. An edge is linear in its leaf -/

private lemma vert_add_left' (p q : Mode) (A A' B : V3) :
    vert p q (A + A') B = vert p q A B + vert p q A' B := by
  simp only [vert, dotM_add, mul_add, add_smul, smul_add, leray_add]
  abel

private lemma vert_smul_left' (p q : Mode) (c : ℂ) (A B : V3) :
    vert p q (c • A) B = c • vert p q A B := by
  have h : (Complex.I * dotM (c • A) q) • B + (Complex.I * dotM B p) • (c • A) =
      c • ((Complex.I * dotM A q) • B + (Complex.I * dotM B p) • A) := by
    rw [dotM_smul]
    module
  rw [vert, vert, h, leray_smul, smul_comm]

lemma blk_add_leaf (m : Mult) (p k j : Mode) (v v' : V3) :
    blk m p k j (v + v') = blk m p k j v + blk m p k j v' := by
  refine ContinuousLinearMap.ext fun w => ?_
  simp only [add_apply, blk_apply, hel_add, vert_add_left', smul_add, Finset.sum_add_distrib]

lemma blk_smul_leaf (m : Mult) (p k j : Mode) (c : ℂ) (v : V3) :
    blk m p k j (c • v) = c • blk m p k j v := by
  refine ContinuousLinearMap.ext fun w => ?_
  simp only [smul_apply, blk_apply, hel_smul, vert_smul_left', Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c' _ => ?_
  rw [smul_comm]

private lemma conjV_add₁ (a b : V3) : conjV (a + b) = conjV a + conjV b := by
  ext i
  simp [conjV]

private lemma conjV_smul₁ (c : ℂ) (a : V3) : conjV (c • a) = conj c • conjV a := by
  ext i
  simp [conjV]

lemma Lb_add_leaf (s : ℕ) (τ : ℝ) (p k j : Mode) (v v' : V3) :
    Lb s τ p k j (v + v') = Lb s τ p k j v + Lb s τ p k j v' := by
  simp only [Lb, blk_add_leaf, smul_add]

lemma Lb_smul_leaf (s : ℕ) (τ : ℝ) (p k j : Mode) (c : ℂ) (v : V3) :
    Lb s τ p k j (c • v) = c • Lb s τ p k j v := by
  simp only [Lb, blk_smul_leaf, smul_comm _ c]

lemma Lad_add_leaf (s : ℕ) (τ : ℝ) (p k j : Mode) (v v' : V3) :
    Lad s τ p k j (v + v') = Lad s τ p k j v + Lad s τ p k j v' := by
  simp only [Lad, conjV_add₁, Lb_add_leaf, map_add]

lemma Lad_smul_leaf (s : ℕ) (τ : ℝ) (p k j : Mode) (c : ℂ) (v : V3) :
    Lad s τ p k j (c • v) = c • Lad s τ p k j v := by
  simp only [Lad, conjV_smul₁, Lb_smul_leaf, map_smulₛₗ, Complex.conj_conj]

lemma X1b_add_leaf (s : ℕ) (r τ : ℝ) (p k j : Mode) (v v' : V3) :
    X1b s r τ p k j (v + v') = X1b s r τ p k j v + X1b s r τ p k j v' := by
  simp only [X1b, conjV_add₁, blk_add_leaf, smul_add, map_add]
  abel

lemma X1b_smul_leaf (s : ℕ) (r τ : ℝ) (p k j : Mode) (c : ℂ) (v : V3) :
    X1b s r τ p k j (c • v) = c • X1b s r τ p k j v := by
  simp only [X1b, conjV_smul₁, blk_smul_leaf, smul_add, smul_comm _ c, map_smulₛₗ,
    Complex.conj_conj]

/-! ### B. The two sources -/

/-- `X₁𝓛 + 𝓛*X₁` at `(l, a, b)` on the leaf vectors. -/
def tR (s : ℕ) (r τ : ℝ) (l a b : Mode) (v w : V3) : Blk :=
  X1b s r τ a l (l - a) v ∘L Lb s τ b (l - a) (l - a - b) w +
    Lad s τ a l (l - a) v ∘L X1b s r τ b (l - a) (l - a - b) w

lemma twoRoot_eq_tR (s : ℕ) (r τ : ℝ) (f g : Field) (l a b : Mode) :
    twoRoot s r τ f g l a b = tR s r τ l a b (f a) (g b) := rfl

/-- `X₁(B)` at `(l, a, b)` on the leaf vectors: the merged leaf. -/
def zR (s : ℕ) (r τ : ℝ) (l a b : Mode) (v w : V3) : Blk :=
  X1b s r τ (a + b) l (l - a - b) (slowV a b v w)

lemma slowV_add_left (a b : Mode) (v v' w : V3) :
    slowV a b (v + v') w = slowV a b v w + slowV a b v' w := by
  simp only [slowV, blk_add_leaf, add_apply]

lemma slowV_smul_left (a b : Mode) (c : ℂ) (v w : V3) :
    slowV a b (c • v) w = c • slowV a b v w := by
  simp only [slowV, blk_smul_leaf, smul_apply]

lemma slowV_add_right (a b : Mode) (v w w' : V3) :
    slowV a b v (w + w') = slowV a b v w + slowV a b v w' := by
  simp only [slowV, map_add]

lemma slowV_smul_right (a b : Mode) (c : ℂ) (v w : V3) :
    slowV a b v (c • w) = c • slowV a b v w := by
  simp only [slowV, map_smul]

/-- A map of two leaf vectors that is `ℂ`-bilinear. -/
structure IsBil {E : Type*} [AddCommGroup E] [Module ℂ E] (f : V3 → V3 → E) : Prop where
  add_l : ∀ v v' w, f (v + v') w = f v w + f v' w
  smul_l : ∀ (c : ℂ) v w, f (c • v) w = c • f v w
  add_r : ∀ v w w', f v (w + w') = f v w + f v w'
  smul_r : ∀ (c : ℂ) v w, f v (c • w) = c • f v w

lemma tR_isBil (s : ℕ) (r τ : ℝ) (l a b : Mode) : IsBil (tR s r τ l a b) where
  add_l v v' w := by
    simp only [tR, X1b_add_leaf, Lad_add_leaf, ContinuousLinearMap.add_comp]
    abel
  smul_l c v w := by
    simp only [tR, X1b_smul_leaf, Lad_smul_leaf, ContinuousLinearMap.smul_comp, smul_add]
  add_r v w w' := by
    simp only [tR, X1b_add_leaf, Lb_add_leaf, ContinuousLinearMap.comp_add]
    abel
  smul_r c v w := by
    simp only [tR, X1b_smul_leaf, Lb_smul_leaf, ContinuousLinearMap.comp_smul, smul_add]

lemma zR_isBil (s : ℕ) (r τ : ℝ) (l a b : Mode) : IsBil (zR s r τ l a b) where
  add_l v v' w := by simp only [zR, slowV_add_left, X1b_add_leaf]
  smul_l c v w := by simp only [zR, slowV_smul_left, X1b_smul_leaf]
  add_r v w w' := by simp only [zR, slowV_add_right, X1b_add_leaf]
  smul_r c v w := by simp only [zR, slowV_smul_right, X1b_smul_leaf]

section Bil

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A bilinear map of leaf vectors is a continuous bilinear map: `V3` is finite dimensional. -/
def bilCLM {f : V3 → V3 → E} (h : IsBil f) : V3 →L[ℂ] V3 →L[ℂ] E :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V3 →ₗ[ℂ] E) ≃ₗ[ℂ] V3 →L[ℂ] E).toLinearMap ∘ₗ
      LinearMap.mk₂ ℂ f h.add_l h.smul_l h.add_r h.smul_r)

@[simp] lemma bilCLM_apply {f : V3 → V3 → E} (h : IsBil f) (v w : V3) : bilCLM h v w = f v w := rfl

end Bil

/-- **The product rule** for a `ℂ`-bilinear map, along a real path. -/
lemma hasDeriv_bil {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (B : E →L[ℂ] F →L[ℂ] G) {u : ℝ → E} {v : ℝ → F} {u' : E} {v' : F} {A : Set ℝ} {x : ℝ}
    (hu : HasDerivWithinAt u u' A x) (hv : HasDerivWithinAt v v' A x) :
    HasDerivWithinAt (fun y => B (u y) (v y)) (B u' (v x) + B (u x) v') A x := by
  have h := (B.bilinearRestrictScalars ℝ).hasDerivWithinAt_of_bilinear hu hv
  simpa [add_comm] using h

/-- A continuous `ℂ`-linear map of a real path. -/
lemma hasDeriv_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (B : E →L[ℂ] F) {u : ℝ → E} {u' : E} {A : Set ℝ}
    {x : ℝ} (hu : HasDerivWithinAt u u' A x) :
    HasDerivWithinAt (fun y => B (u y)) (B u') A x :=
  (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt x hu

end OVNS.Quant.Metric

end
