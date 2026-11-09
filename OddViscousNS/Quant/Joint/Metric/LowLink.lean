import OddViscousNS.Quant.Joint.Metric.SepForm

/-!
# The last edge of the cubic group, split (step J5, nodes N6, N7)

Body 42: "Split it into a smooth low multiplier and exact complement before any absolute kernel
estimate."  On the fast labels `𝓛 = QLF + QHF`, with `QLF = 2 Π_F Q_lo` the low last edge of
`LowPass.lean`.  In the energy coordinates (`zOf_QLF`, `zOf_QHF`) these are the sums over the last
leaf with the multipliers `lowM`, `1 − lowM`.

* `form_fubini`: the form of a two-leaf block on a sum of edges is the four-label form;
* `X2Form_herm`, `ZForm_herm`: `X₂`, `Z` are Hermitian as forms, with no summability hypothesis.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-- The low last edge, on the fast labels. -/
def QLF (τ : ℝ) (S F : Field) : Field := (2 : ℂ) • PiF (Qlo τ S F)

/-- The high last edge, on the fast labels. -/
def QHF (τ : ℝ) (S F : Field) : Field := Lop τ S F - QLF τ S F

variable {S F G w : Field} {s : ℕ} {τ : ℝ}

/-- The summand of the low edge against the energy coordinates. -/
lemma Lb_zOf (s : ℕ) (τ : ℝ) {F : Field} (hF0 : F 0 = 0) (k p : Mode) (v : V3) :
    Lb s τ p k (k - p) v (zOf s F (k - p)) =
      ((2 * absk k ^ s : ℝ) : ℂ) • blk (phaseM τ) p k (k - p) v (F (k - p)) := by
  by_cases hj : k - p = 0
  · simp [hj, hF0, zOf]
  have hJ : absk (k - p) ≠ 0 := absk_eq_zero.not.2 hj
  simp only [Lb, wt, smul_apply, zOf, map_smul, smul_smul]
  congr 1
  push_cast
  rw [div_pow]
  have hJ' : (absk (k - p) : ℂ) ≠ 0 := by exact_mod_cast hJ
  field_simp

lemma Lb_summable (s : ℕ) (τ : ℝ) {S F : Field} (hF0 : F 0 = 0)
    (hS2 : Summable fun k => ‖S k‖ ^ 2) (hF2 : Summable fun k => ‖F k‖ ^ 2) (k : Mode) :
    Summable fun p => Lb s τ p k (k - p) (S p) (zOf s F (k - p)) := by
  simp only [Lb_zOf s τ hF0]
  exact (blk_summable (phaseM_bdd τ) hS2 hF2 k).const_smul _

/-- **The low edge on the energy coordinates**, at a fast output. -/
lemma zOf_QLF (s : ℕ) (τ : ℝ) {S F : Field} (hF0 : F 0 = 0) {k : Mode} (hk : k 2 ≠ 0) :
    zOf s (QLF τ S F) k =
      ∑' p, ((lowM p (k - p) : ℝ) : ℂ) • Lb s τ p k (k - p) (S p) (zOf s F (k - p)) := by
  have hL : QLF τ S F k = (2 : ℂ) • Qlo τ S F k := by simp [QLF, PiF, hk]
  set t : Mode → V3 := fun p => ((lowM p (k - p) : ℝ) : ℂ) •
    blk (phaseM τ) p k (k - p) (S p) (F (k - p)) with ht
  have e0 : Qlo τ S F k = ∑' p, t p := rfl
  have h1 : zOf s (QLF τ S F) k = ((2 * absk k ^ s : ℝ) : ℂ) • ∑' p, t p := by
    rw [← e0]
    simp only [zOf, hL, smul_smul]
    congr 1
    push_cast
    ring
  rw [h1, ← tsum_const_smul'']
  refine tsum_congr fun p => ?_
  rw [Lb_zOf s τ hF0, smul_comm]

/-- **The high edge on the energy coordinates**, at a fast output. -/
lemma zOf_QHF (s : ℕ) (τ : ℝ) {S F : Field} (hF0 : F 0 = 0) (hS2 : Summable fun k => ‖S k‖ ^ 2)
    (hF2 : Summable fun k => ‖F k‖ ^ 2) {k : Mode} (hk : k 2 ≠ 0) :
    HasSum (fun p => ((1 - lowM p (k - p) : ℝ) : ℂ) • Lb s τ p k (k - p) (S p) (zOf s F (k - p)))
      (zOf s (QHF τ S F) k) := by
  have hs := Lb_summable s τ hF0 hS2 hF2 k
  have hl : Summable fun p => ((lowM p (k - p) : ℝ) : ℂ) • Lb s τ p k (k - p) (S p)
      (zOf s F (k - p)) := by
    refine Summable.of_norm_bounded (summable_norm_iff.2 hs) fun p => ?_
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (lowM_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (lowM_le_one _ _)
  have e : zOf s (QHF τ S F) k = zOf s (Lop τ S F) k - zOf s (QLF τ S F) k := by
    simp only [zOf, QHF, Pi.sub_apply, smul_sub]
  rw [e, zOf_Lop s τ hF0 hk, zOf_QLF s τ hF0 hk]
  have h := hs.hasSum.sub hl.hasSum
  convert h using 1
  funext p
  rw [Complex.ofReal_sub, sub_smul, Complex.ofReal_one, one_smul]

/-! ### The four-label form -/

/-- A two-leaf block `Y` on a sum of edges. -/
theorem form_fubini {Y : I3 → Blk} {G : Field} {w : Field} {E : I4 → V3}
    (hE : ∀ y : I3, y.2.1 2 = 0 → y.2.2 2 = 0 → (y.1 - y.2.1 - y.2.2) 2 ≠ 0 →
      HasSum (fun c => E (y.1, y.2.1, y.2.2, c)) (w (y.1 - y.2.1 - y.2.2)))
    (h0 : ∀ y : I3, ¬ (y.2.1 2 = 0 ∧ y.2.2 2 = 0 ∧ (y.1 - y.2.1 - y.2.2) 2 ≠ 0) →
      inner ℂ (G y.1) (Y y (w (y.1 - y.2.1 - y.2.2))) = 0 ∧
        ∀ c, inner ℂ (G y.1) (Y y (E (y.1, y.2.1, y.2.2, c))) = 0)
    (hT : Summable fun x : I4 => inner ℂ (G x.1) (Y (x.1, x.2.1, x.2.2.1) (E x))) :
    ∑' y : I3, inner ℂ (G y.1) (Y y (w (y.1 - y.2.1 - y.2.2))) =
      ∑' x : I4, inner ℂ (G x.1) (Y (x.1, x.2.1, x.2.2.1) (E x)) := by
  set e : I3 × Mode ≃ I4 :=
    { toFun := fun p => (p.1.1, p.1.2.1, p.1.2.2, p.2)
      invFun := fun x => ((x.1, x.2.1, x.2.2.1), x.2.2.2)
      left_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl } with he
  rw [← e.tsum_eq]
  have hT' : Summable fun p : I3 × Mode => inner ℂ (G (e p).1)
      (Y ((e p).1, (e p).2.1, (e p).2.2.1) (E (e p))) := e.summable_iff.2 hT
  rw [hT'.tsum_prod]
  refine tsum_congr fun y => ?_
  by_cases hA : y.2.1 2 = 0 ∧ y.2.2 2 = 0 ∧ (y.1 - y.2.1 - y.2.2) 2 ≠ 0
  · have h1 := hE y hA.1 hA.2.1 hA.2.2
    have h2 : HasSum (fun c => inner ℂ (G y.1) (Y y (E (y.1, y.2.1, y.2.2, c))))
        (inner ℂ (G y.1) (Y y (w (y.1 - y.2.1 - y.2.2)))) :=
      (innerSL ℂ (G y.1) ∘L Y y).hasSum h1
    exact h2.tsum_eq.symm
  · obtain ⟨h1, h2⟩ := h0 y hA
    rw [h1]
    have : ∀ c, inner ℂ (G (e (y, c)).1) (Y ((e (y, c)).1, (e (y, c)).2.1, (e (y, c)).2.2.1)
        (E (e (y, c)))) = 0 := h2
    simp only [this, tsum_zero]

/-! ### Hermiticity of the forms -/

/-- The path reversal, for `Z`. -/
def revZb : I3 ≃ I3 where
  toFun x := (inJ₂ x, -x.2.1, -x.2.2)
  invFun x := (inJ₂ x, -x.2.1, -x.2.2)
  left_inv := fun ⟨l, a, b⟩ => Prod.ext (show l - a - b - -a - -b = l by abel)
    (Prod.ext (neg_neg a) (neg_neg b))
  right_inv := fun ⟨l, a, b⟩ => Prod.ext (show l - a - b - -a - -b = l by abel)
    (Prod.ext (neg_neg a) (neg_neg b))

/-- **`X₂` is Hermitian as a form.** -/
theorem X2Form_herm (s : ℕ) (r τ : ℝ) {f g : Field} (hf : IsReal f) (hg : IsReal g)
    (G w : Field) :
    X2Form (fun _ => 1) s r τ f g G w = conj (X2Form (fun _ => 1) s r τ g f w G) := by
  simp only [X2Form, one_mul]
  rw [Complex.conj_tsum, ← revE.tsum_eq]
  refine tsum_congr fun x => ?_
  have e1 : (revE x).1 = inJ₂ x := rfl
  have e2 : (revE x).2.1 = -x.2.2 := rfl
  have e3 : (revE x).2.2 = -x.2.1 := rfl
  rw [e1, e2, e3, inner_conj_symm]
  have e4 : inJ₂ x - -x.2.2 - -x.2.1 = x.1 := by
    simp only [inJ₂]
    abel
  rw [e4]
  have e5 : inJ₂ x = x.1 - x.2.1 - x.2.2 := rfl
  rw [e5, ← adjoint_X2b s r τ hg hf, ContinuousLinearMap.adjoint_inner_right]

/-- **`Z` is Hermitian as a form.** -/
theorem ZForm_herm (s : ℕ) (r τ : ℝ) {f g : Field} (hf : IsReal f) (hg : IsReal g)
    (G w : Field) :
    ZForm (fun _ => 1) s r τ f g G w = conj (ZForm (fun _ => 1) s r τ f g w G) := by
  simp only [ZForm, one_mul]
  rw [Complex.conj_tsum, ← revZb.tsum_eq]
  refine tsum_congr fun x => ?_
  have e1 : (revZb x).1 = inJ₂ x := rfl
  have e2 : (revZb x).2.1 = -x.2.1 := rfl
  have e3 : (revZb x).2.2 = -x.2.2 := rfl
  rw [e1, e2, e3, inner_conj_symm]
  have e4 : inJ₂ x - -x.2.1 - -x.2.2 = x.1 := by
    simp only [inJ₂]
    abel
  rw [e4]
  have e5 : inJ₂ x = x.1 - x.2.1 - x.2.2 := rfl
  rw [e5, ← adjoint_Zb s r τ hf hg, ContinuousLinearMap.adjoint_inner_right]

/-- The output half is the form on `zOf 1 G`. -/
lemma X2Half_eq (μ : I3 → ℂ) (s : ℕ) (r τ : ℝ) (f g G F : Field) :
    X2HalfForm μ s r τ f g G F = X2Form μ s r τ f g (zOf 1 G) F := by
  simp only [X2HalfForm, X2Form]
  refine tsum_congr fun x => ?_
  simp only [zOf, pow_one]
  rw [inner_smul_left, Complex.conj_ofReal]
  ring

end OVNS.Quant.Metric

end
