import OddViscousNS.Quant.Joint.Metric.HeatSplit

/-!
# The third correction: definition (step J5, node N8)

Body 33 (LOCAL474), Body 42 (LOCAL659), LOCAL466.  On the labels `(l, a, b, c)`, `k = l − a − b`,
`j = k − c`:

* `muQ D`: the high-last complement `1 − χ` times "all three ancestors `≤ D`" times "`L, K` comparable
  up to two".  Then `P₃ ≥ 16 J`, so `L > 4 J` (Body 42): the total phase is separated.
* `Yq`: the two-leaf factor, `H⁻¹` of `tQ + zR`, with `tQ = tR` on the ordinary sector and
  `tQ = tR − tH` at a large intermediate: the heat sum stays out (Body 33: "Leave the
  high-intermediate heat-sum estimate in the preceding independent `q⁻²` group").
* `famQ`: the family with source `muQ • (Yq ∘ 𝓛)`, whose outer heat is `L² + J² + P₁² + P₂² + P₃²`:
  "the exact third denominator".

The form of the family is the directed operator; the energy has `Re⟨z, O z⟩`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open Classical in
/-- The two rootings as they enter `Q₃`. -/
def tQ (s : ℕ) (r τ : ℝ) (l a b : Mode) (v w : V3) : Blk :=
  if 4 * absk l ≤ absk (l - a) ∧ 4 * absk (l - a - b) ≤ absk (l - a) then
    tR s r τ l a b v w - tH s r τ l a b v w else tR s r τ l a b v w

/-- The two-leaf factor of `Q₃`. -/
def Yq (s : ℕ) (r τ : ℝ) (l a b : Mode) (v w : V3) : Blk :=
  outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (tQ s r τ l a b v w + zR s r τ l a b v w)

/-- The heat block is bilinear. -/
lemma tH_isBil (s : ℕ) (r τ : ℝ) (l a b : Mode) : IsBil (tH s r τ l a b) where
  add_l v v' w := by
    simp only [tH, Lad_add_leaf, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
      smul_add, Finset.sum_add_distrib]
  smul_l c v w := by
    simp only [tH, Lad_smul_leaf, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      Finset.smul_sum, smul_comm c]
  add_r v w w' := by
    simp only [tH, Lb_add_leaf, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
      smul_add, Finset.sum_add_distrib]
  smul_r c v w := by
    simp only [tH, Lb_smul_leaf, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      Finset.smul_sum, smul_comm c]

lemma tQ_isBil (s : ℕ) (r τ : ℝ) (l a b : Mode) : IsBil (tQ s r τ l a b) := by
  have h1 := tR_isBil s r τ l a b
  have h2 := tH_isBil s r τ l a b
  by_cases h : 4 * absk l ≤ absk (l - a) ∧ 4 * absk (l - a - b) ≤ absk (l - a)
  · have e : tQ s r τ l a b = fun v w => tR s r τ l a b v w - tH s r τ l a b v w := by
      funext v w
      simp only [tQ, h, and_self, ite_true]
    rw [e]
    refine ⟨fun v v' w => ?_, fun c v w => ?_, fun v w w' => ?_, fun c v w => ?_⟩
    · rw [h1.add_l, h2.add_l]
      abel
    · rw [h1.smul_l, h2.smul_l, smul_sub]
    · rw [h1.add_r, h2.add_r]
      abel
    · rw [h1.smul_r, h2.smul_r, smul_sub]
  · have e : tQ s r τ l a b = tR s r τ l a b := by
      funext v w
      simp only [tQ, h, ite_false]
    rw [e]
    exact h1

/-- `outerInv` is linear. -/
lemma outerInv_add (r H : ℝ) (l j : Mode) (T T' : Blk) :
    outerInv r H l j (T + T') = outerInv r H l j T + outerInv r H l j T' := by
  simp only [outerInv, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, smul_add,
    Finset.sum_add_distrib]

lemma outerInv_smul (r H : ℝ) (l j : Mode) (c : ℂ) (T : Blk) :
    outerInv r H l j (c • T) = c • outerInv r H l j T := by
  simp only [outerInv, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    Finset.smul_sum, smul_comm c]

lemma Yq_isBil (s : ℕ) (r τ : ℝ) (l a b : Mode) : IsBil (Yq s r τ l a b) := by
  have h1 := tQ_isBil s r τ l a b
  have h2 := zR_isBil s r τ l a b
  refine ⟨fun v v' w => ?_, fun c v w => ?_, fun v w w' => ?_, fun c v w => ?_⟩
  · simp only [Yq, h1.add_l, h2.add_l]
    rw [← outerInv_add]
    congr 1
    abel
  · simp only [Yq, h1.smul_l, h2.smul_l, ← smul_add, outerInv_smul]
  · simp only [Yq, h1.add_r, h2.add_r]
    rw [← outerInv_add]
    congr 1
    abel
  · simp only [Yq, h1.smul_r, h2.smul_r, ← smul_add, outerInv_smul]

/-- The heat block moves by the exterior phase. -/
lemma tH_chan (s : ℕ) (r τ σ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (v w y : V3)
    (c d : Sgn) :
    hel c l (tH s r (τ + σ) l a b v w (hel d (l - a - b) y)) =
      Complex.exp (Complex.I * (σ * outerPhi c d l (l - a - b) : ℝ)) •
        hel c l (tH s r τ l a b v w (hel d (l - a - b) y)) := by
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  rw [chan_tH, chan_tH, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [smul_comm]
  congr 1
  set m := l - a
  set k := l - a - b
  rw [Lb_cov s τ σ hb e2, rotL_hel, map_smul, Lad_cov s τ σ ha e1, hel_rotL]
  simp only [hel_smul, map_smul, rotL_hel, smul_smul, hel_rotL]
  congr 1
  simp only [← Complex.exp_add]
  congr 1
  simp only [outerPhi]
  push_cast
  ring

/-- The two rootings of `Q₃` move by the exterior phase. -/
lemma tQ_chan (s : ℕ) (r τ σ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (v w y : V3)
    (c d : Sgn) :
    hel c l ((tQ s r (τ + σ) l a b v w + zR s r (τ + σ) l a b v w) (hel d (l - a - b) y)) =
      Complex.exp (Complex.I * (σ * outerPhi c d l (l - a - b) : ℝ)) •
        hel c l ((tQ s r τ l a b v w + zR s r τ l a b v w) (hel d (l - a - b) y)) := by
  have hR := twoRoot_chan s r τ σ (fun _ => v) (fun _ => w) (l := l) ha hb c d y
  have hZ := X1Z_chan s r τ σ (fun _ => v) (fun _ => w) (l := l) ha hb c d y
  have hH := tH_chan s r τ σ (l := l) ha hb v w y c d
  have eR : ∀ τ', twoRoot s r τ' (fun _ => v) (fun _ => w) l a b = tR s r τ' l a b v w := fun _ => rfl
  rw [eR, eR] at hR
  have eZ : ∀ τ', X1b s r τ' (a + b) l (l - a - b) (slowV a b v w) = zR s r τ' l a b v w :=
    fun _ => rfl
  have hZ' : hel c l (zR s r (τ + σ) l a b v w (hel d (l - a - b) y)) =
      Complex.exp (Complex.I * (σ * outerPhi c d l (l - a - b) : ℝ)) •
        hel c l (zR s r τ l a b v w (hel d (l - a - b) y)) := hZ
  by_cases h : 4 * absk l ≤ absk (l - a) ∧ 4 * absk (l - a - b) ≤ absk (l - a)
  · simp only [tQ, h, and_self, ite_true, add_apply, sub_apply, hel_add, hel_sub, smul_add,
      smul_sub, hR, hH, hZ']
  · simp only [tQ, h, ite_false, add_apply, hel_add, smul_add, hR, hZ']

/-- The two-leaf factor moves by the exterior phase. -/
lemma Yq_chan (s : ℕ) (r τ σ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (v w y : V3)
    (c d : Sgn) :
    hel c l (Yq s r (τ + σ) l a b v w (hel d (l - a - b) y)) =
      Complex.exp (Complex.I * (σ * outerPhi c d l (l - a - b) : ℝ)) •
        hel c l (Yq s r τ l a b v w (hel d (l - a - b) y)) := by
  simp only [Yq]
  rw [hel_outerInv, hel_outerInv, tQ_chan s r τ σ ha hb, smul_comm]

/-- An edge moves by its exterior phase. -/
lemma Lb_chan (s : ℕ) (τ σ : ℝ) {p k j : Mode} (hp : p 2 = 0) (hk : p + j = k) (v y : V3)
    (c e : Sgn) :
    hel c k (Lb s (τ + σ) p k j v (hel e j y)) =
      Complex.exp (Complex.I * (σ * outerPhi c e k j : ℝ)) • hel c k (Lb s τ p k j v (hel e j y)) :=
  chan_cov (fun w => Lb_cov s τ σ hp hk v w) c e y

/-- A block times an edge moves by the total exterior phase: the helicity at `k` has cancelled. -/
lemma comp_chan {A E : ℝ → Blk} {l k j : Mode}
    (hA : ∀ τ c d y, hel c l (A τ (hel d k y)) =
      Complex.exp (Complex.I * (τ * outerPhi c d l k : ℝ)) • hel c l (A 0 (hel d k y)))
    (hE : ∀ τ d e y, hel d k (E τ (hel e j y)) =
      Complex.exp (Complex.I * (τ * outerPhi d e k j : ℝ)) • hel d k (E 0 (hel e j y)))
    (hS : ∀ τ z, ∑ d : Sgn, hel d k (E τ z) = E τ z) (τ : ℝ) (c e : Sgn) (y : V3) :
    hel c l (A τ (E τ (hel e j y))) =
      Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) • hel c l (A 0 (E 0 (hel e j y))) := by
  have h1 : ∀ σ, hel c l (A σ (E σ (hel e j y))) =
      ∑ d : Sgn, hel c l (A σ (hel d k (E σ (hel e j y)))) := fun σ => by
    conv_lhs => rw [← hS σ (hel e j y)]
    rw [map_sum, hel_sum_distrib]
  rw [h1 τ, h1 0, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hA, hE, map_smul, hel_smul, smul_smul, ← Complex.exp_add]
  congr 2
  simp only [outerPhi]
  push_cast
  ring

/-- The last edge as a linear map of its leaf. -/
def LbCL (s : ℕ) (τ : ℝ) (p k j : Mode) : V3 →L[ℂ] Blk :=
  LinearMap.toContinuousLinearMap
    { toFun := Lb s τ p k j
      map_add' := Lb_add_leaf s τ p k j
      map_smul' := fun c v => Lb_smul_leaf s τ p k j c v }

@[simp] lemma LbCL_apply (s : ℕ) (τ : ℝ) (p k j : Mode) (v : V3) :
    LbCL s τ p k j v = Lb s τ p k j v := rfl

open Classical in
/-- The mask of `Q₃`. -/
def muQ (D : ℝ) (x : I4) : ℝ :=
  (1 - lowM x.2.2.2 (inJ x)) *
    if absk x.2.1 ≤ D ∧ absk x.2.2.1 ≤ D ∧ absk x.2.2.2 ≤ D ∧
      absk x.1 ≤ 2 * absk (x.1 - x.2.1 - x.2.2.1) ∧ absk (x.1 - x.2.1 - x.2.2.1) ≤ 2 * absk x.1
    then 1 else 0

lemma muQ_nonneg (D : ℝ) (x : I4) : 0 ≤ muQ D x := by
  have h := lowM_le_one x.2.2.2 (inJ x)
  unfold muQ
  split_ifs <;> linarith

lemma muQ_le_one (D : ℝ) (x : I4) : muQ D x ≤ 1 := by
  have h := lowM_nonneg x.2.2.2 (inJ x)
  have h1 := lowM_le_one x.2.2.2 (inJ x)
  unfold muQ
  split_ifs <;> linarith

lemma IsBil.zero_l' {f : V3 → V3 → Blk} (h : IsBil f) (w : V3) : f 0 w = 0 := by
  have := h.smul_l 0 0 w
  rw [zero_smul] at this
  have h0 : (0 : ℂ) • f 0 w = 0 := by
    ext1 y
    simp only [smul_apply, zero_apply, zero_smul]
  rw [h0] at this
  exact this

lemma IsBil.zero_r' {f : V3 → V3 → Blk} (h : IsBil f) (v : V3) : f v 0 = 0 := by
  have := h.smul_r 0 v 0
  rw [zero_smul] at this
  have h0 : (0 : ℂ) • f v 0 = 0 := by
    ext1 y
    simp only [smul_apply, zero_apply, zero_smul]
  rw [h0] at this
  exact this

/-- **The family of `Q₃`.** -/
def famQ (s : ℕ) (r D : ℝ) : Fam3 where
  Sr x τ t v w := ((muQ D x : ℝ) : ℂ) • (Yq s r τ x.1 x.2.1 x.2.2.1 t v ∘L
    Lb s τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x) w)
  A0 x := ((muQ D x : ℝ) : ℂ) • bilCLM (Yq_isBil s r 0 x.1 x.2.1 x.2.2.1)
  E0 x := LbCL s 0 x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x)
  cov x ha hb hc τ t v w c e y := by
    have ek : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
      simp only [inJ]
      abel
    have h := comp_chan (A := fun τ => Yq s r τ x.1 x.2.1 x.2.2.1 t v)
      (E := fun τ => Lb s τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x) w) (l := x.1)
      (k := x.1 - x.2.1 - x.2.2.1) (j := inJ x)
      (fun τ c d y => by
        have := Yq_chan s r 0 τ (l := x.1) ha hb t v y c d
        rwa [zero_add] at this)
      (fun τ d e y => by
        have := Lb_chan s 0 τ hc ek w y d e
        rwa [zero_add] at this)
      (fun τ z => sum_hel_Lb s τ _ _ _ w z) τ c e y
    simp only [ContinuousLinearMap.comp_apply, smul_apply, hel_smul, LbCL_apply, bilCLM_apply]
    rw [h, smul_comm]
  zero₁ x τ v w := by
    have := (Yq_isBil s r τ x.1 x.2.1 x.2.2.1).zero_l' v
    simp only [this, ContinuousLinearMap.zero_comp]
    ext1 y
    simp only [smul_apply, zero_apply, smul_zero]
  zero₂ x τ t w := by
    have := (Yq_isBil s r τ x.1 x.2.1 x.2.2.1).zero_r' t
    simp only [this, ContinuousLinearMap.zero_comp]
    ext1 y
    simp only [smul_apply, zero_apply, smul_zero]
  zero₃ x τ t v := by
    simp only [Lb_zero_leaf, ContinuousLinearMap.comp_zero]
    ext1 y
    simp only [smul_apply, zero_apply, smul_zero]

end OVNS.Quant.Metric

end
