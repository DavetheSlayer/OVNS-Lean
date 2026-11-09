import OddViscousNS.Quant.Joint.Quartic.Form

/-!
# The identity of the quartic on the actual path (step J5, node N11)

The derivative of `Q₄` along the actual solution: the source plus the four insertions, at both
weights.  This is the part of N13 for four fields, one slow and three fast.

* `T_hasDeriv`: one label, from `termQ_hasDeriv`;
* `identity_of_dom`: the sum over the labels, from a dominating `L¹` function;
* `rhsT`, `rhs4`, `val4`: the derivative family, the derivative, the value.

There is nothing to differentiate in the masks: `coreQ` does not depend on time.  Body 34: "There is
no time derivative of a cutoff, cap, old scalar bound, or force."
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (integral_tsum_deriv_ae slow_c3_integrable fast_h2_law ae_inH3_split)

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

lemma Fp_hasDeriv (h : ActualSol μ φ r g y Ty) (k : Mode) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    HasDerivWithinAt (fun v => Fp r g y v k)
      (((-absSq k : ℝ) : ℂ) • Fp r g y u k + fastNL r g y u k) (Ici 0) u := by
  refine (fast_mode h k hu huT).congr_deriv ?_
  rw [fastRHS_eq_lap]
  simp only [Fp, Pi.add_apply, Pi.neg_apply, lapF, Complex.ofReal_neg, neg_smul]

/-- The value along the solution. -/
def val4 (j : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  Q4F j r (r * u) (Sp r g y u) (Fp r g y u) (Fp r g y u) (Fp r g y u)

/-- The source along the solution: the coefficient of the near differential. -/
def src4 (j : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  J4F j r (r * u) (Sp r g y u) (Fp r g y u) (Fp r g y u) (Fp r g y u)

/-- The four insertions: `Rem` of Bodies 34, 35, 46. -/
def rem4 (j : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  Q4F j r (r * u) (slowNL r g y u) (Fp r g y u) (Fp r g y u) (Fp r g y u) +
    Q4F j r (r * u) (Sp r g y u) (fastNL r g y u) (Fp r g y u) (Fp r g y u) +
    Q4F j r (r * u) (Sp r g y u) (Fp r g y u) (fastNL r g y u) (Fp r g y u) +
    Q4F j r (r * u) (Sp r g y u) (Fp r g y u) (Fp r g y u) (fastNL r g y u)

/-- The derivative family. -/
def rhsT (j : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) (x : L4) : ℂ :=
  srcQ j r x (r * u) (Sp r g y u x.2.2) (Fp r g y u (inL x)) (Fp r g y u x.2.1)
      (Fp r g y u (outE x)) +
    termQ j r x (r * u) (slowNL r g y u x.2.2) (Fp r g y u (inL x)) (Fp r g y u x.2.1)
      (Fp r g y u (outE x)) +
    termQ j r x (r * u) (Sp r g y u x.2.2) (fastNL r g y u (inL x)) (Fp r g y u x.2.1)
      (Fp r g y u (outE x)) +
    termQ j r x (r * u) (Sp r g y u x.2.2) (Fp r g y u (inL x)) (fastNL r g y u x.2.1)
      (Fp r g y u (outE x)) +
    termQ j r x (r * u) (Sp r g y u x.2.2) (Fp r g y u (inL x)) (Fp r g y u x.2.1)
      (fastNL r g y u (outE x))

/-- One label of the actual path has the derivative of the family. -/
lemma T_hasDeriv (h : ActualSol μ φ r g y Ty) (j : ℕ) (x : L4) {a b : ℝ} (ha : 0 ≤ a)
    (hb : ENNReal.ofReal b < Ty) {u : ℝ} (hu : u ∈ Icc a b) :
    HasDerivWithinAt (fun v => termQ j r x (r * v) (Sp r g y v x.2.2) (Fp r g y v (inL x))
      (Fp r g y v x.2.1) (Fp r g y v (outE x))) (rhsT j r g y u x) (Icc a b) u := by
  have hu0 : 0 ≤ u := ha.trans hu.1
  have huT := lt_lifespan hu.2 hb
  have hsub : Icc a b ⊆ Ici 0 := fun v hv => ha.trans hv.1
  exact termQ_hasDeriv ((Sp_hasDeriv h _ hu0 huT).mono hsub) ((Fp_hasDeriv h _ hu0 huT).mono hsub)
    ((Fp_hasDeriv h _ hu0 huT).mono hsub) ((Fp_hasDeriv h _ hu0 huT).mono hsub)

lemma chQ_continuous (r : ℝ) (d b c : Sgn) (x : L4) :
    Continuous fun u : ℝ => chQ (r * u) d b c x := by
  unfold chQ
  fun_prop

/-- A label of the quartic along continuous paths. -/
lemma termQ_continuousOn {j : ℕ} {x : L4} {t w u v : ℝ → V3} {A : Set ℝ} (ht : ContinuousOn t A)
    (hw : ContinuousOn w A) (hu : ContinuousOn u A) (hv : ContinuousOn v A) :
    ContinuousOn (fun τ => termQ j r x (r * τ) (t τ) (w τ) (u τ) (v τ)) A := by
  unfold termQ
  refine continuousOn_finsetSum _ fun d _ => continuousOn_finsetSum _ fun a _ =>
    continuousOn_finsetSum _ fun b _ => continuousOn_finsetSum _ fun c _ => ?_
  exact continuousOn_const.mul ((chQ_continuous r d b c x).continuousOn.mul
    (coreQ_continuousOn ht hw hu hv))

/-- A label of the source along continuous paths. -/
lemma srcQ_continuousOn {j : ℕ} {x : L4} {t w u v : ℝ → V3} {A : Set ℝ} (ht : ContinuousOn t A)
    (hw : ContinuousOn w A) (hu : ContinuousOn u A) (hv : ContinuousOn v A) :
    ContinuousOn (fun τ => srcQ j r x (r * τ) (t τ) (w τ) (u τ) (v τ)) A := by
  unfold srcQ
  refine continuousOn_finsetSum _ fun d _ => continuousOn_finsetSum _ fun a _ =>
    continuousOn_finsetSum _ fun b _ => continuousOn_finsetSum _ fun c _ => ?_
  exact (chQ_continuous r d b c x).continuousOn.mul (coreQ_continuousOn ht hw hu hv)

/-- The derivative family is continuous in time. -/
lemma rhsT_continuousOn (h : ActualSol μ φ r g y Ty) (j : ℕ) (x : L4) {a b : ℝ} (ha : 0 ≤ a)
    (hb : ENNReal.ofReal b < Ty) (hab : a ≤ b) :
    ContinuousOn (fun u => rhsT j r g y u x) (Icc a b) := by
  have hb0 := ha.trans hab
  have hsub : Icc a b ⊆ Icc 0 b := Icc_subset_Icc_left ha
  have hmem : ∀ u ∈ Icc a b, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨ha.trans hu.1, lt_lifespan hu.2 hb⟩
  have hI : Icc a b ⊆ Ici 0 := fun v hv => ha.trans hv.1
  have cF : ∀ k, ContinuousOn (fun u => Fp r g y u k) (Icc a b) := fun k u hu =>
    ((Fp_hasDeriv h k (hmem u hu).1 (hmem u hu).2).mono hI).continuousWithinAt
  have cS : ∀ k, ContinuousOn (fun u => Sp r g y u k) (Icc a b) := fun k u hu =>
    ((Sp_hasDeriv h k (hmem u hu).1 (hmem u hu).2).mono hI).continuousWithinAt
  have cN : ∀ k, ContinuousOn (fun u => fastNL r g y u k) (Icc a b) := fun k =>
    (fastNL_mode_continuousOn h hb0 hb k).mono hsub
  have cNs : ∀ k, ContinuousOn (fun u => slowNL r g y u k) (Icc a b) := fun k =>
    (slowNL_mode_continuousOn h hb0 hb k).mono hsub
  exact (((((srcQ_continuousOn (r := r) (cS _) (cF _) (cF _) (cF _)).add
    (termQ_continuousOn (cNs _) (cF _) (cF _) (cF _))).add
    (termQ_continuousOn (cS _) (cN _) (cF _) (cF _))).add
    (termQ_continuousOn (cS _) (cF _) (cN _) (cF _))).add
    (termQ_continuousOn (cS _) (cF _) (cF _) (cN _)))

/-- A dominated family has the identity. -/
theorem identity_of_dom (h : ActualSol μ φ r g y Ty) (j : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : ENNReal.ofReal b < Ty) {gf : ℝ → ℝ} (hgi : IntervalIntegrable gf volume a b)
    (hdom : ∀ᵐ u ∂(volume.restrict (Icc a b)), ∃ c₀ c₁ c₂ c₃ c₄ : ℝ,
      SB (fun x : L4 => ‖srcQ j r x (r * u) (Sp r g y u x.2.2) (Fp r g y u (inL x))
        (Fp r g y u x.2.1) (Fp r g y u (outE x))‖) c₀ ∧
      SB (fun x : L4 => ‖termQ j r x (r * u) (slowNL r g y u x.2.2) (Fp r g y u (inL x))
        (Fp r g y u x.2.1) (Fp r g y u (outE x))‖) c₁ ∧
      SB (fun x : L4 => ‖termQ j r x (r * u) (Sp r g y u x.2.2) (fastNL r g y u (inL x))
        (Fp r g y u x.2.1) (Fp r g y u (outE x))‖) c₂ ∧
      SB (fun x : L4 => ‖termQ j r x (r * u) (Sp r g y u x.2.2) (Fp r g y u (inL x))
        (fastNL r g y u x.2.1) (Fp r g y u (outE x))‖) c₃ ∧
      SB (fun x : L4 => ‖termQ j r x (r * u) (Sp r g y u x.2.2) (Fp r g y u (inL x))
        (Fp r g y u x.2.1) (fastNL r g y u (outE x))‖) c₄ ∧
      c₀ + c₁ + c₂ + c₃ + c₄ ≤ gf u)
    (hend : ∀ c ∈ Icc a b, Summable fun x : L4 => termQ j r x (r * c) (Sp r g y c x.2.2)
      (Fp r g y c (inL x)) (Fp r g y c x.2.1) (Fp r g y c (outE x))) :
    IntervalIntegrable (fun u => src4 j r g y u + rem4 j r g y u) volume a b ∧
      val4 j r g y b - val4 j r g y a = ∫ u in a..b, (src4 j r g y u + rem4 j r g y u) := by
  have hdom' : ∀ᵐ u ∂(volume.restrict (Icc a b)),
      Summable (fun x => ‖rhsT j r g y u x‖) ∧ ∑' x, ‖rhsT j r g y u x‖ ≤ gf u := by
    filter_upwards [hdom] with u hu
    obtain ⟨c₀, c₁, c₂, c₃, c₄, s0, s1, s2, s3, s4, hle⟩ := hu
    have hsum := ((((s0.add s1).add s2).add s3).add s4).of_le (F := fun x => ‖rhsT j r g y u x‖)
      (fun x => norm_nonneg _) (fun x => by
        unfold rhsT
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _)
    exact ⟨hsum.1, hsum.2.trans hle⟩
  obtain ⟨hI, key⟩ := integral_tsum_deriv_ae (T := fun u x => termQ j r x (r * u) (Sp r g y u x.2.2)
    (Fp r g y u (inL x)) (Fp r g y u x.2.1) (Fp r g y u (outE x)))
    (T' := fun u x => rhsT j r g y u x) hab
    (fun x u hu => T_hasDeriv h j x ha hb hu) (fun x => rhsT_continuousOn h j x ha hb hab)
    (hend a ⟨le_rfl, hab⟩) (hend b ⟨hab, le_rfl⟩) hgi hdom'
  have hsplit : ∀ᵐ u, u ∈ uIoc a b → ∑' x, rhsT j r g y u x = src4 j r g y u + rem4 j r g y u := by
    rw [uIoc_of_le hab]
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hdom] with u hu3 hmem
    obtain ⟨c₀, c₁, c₂, c₃, c₄, s0, s1, s2, s3, s4, -⟩ := hu3 (Ioc_subset_Icc_self hmem)
    have t0 := s0.1.of_norm
    have t1 := s1.1.of_norm
    have t2 := s2.1.of_norm
    have t3 := s3.1.of_norm
    have t4 := s4.1.of_norm
    simp only [src4, rem4, J4F, Q4F]
    rw [← t1.tsum_add t2, ← (t1.add t2).tsum_add t3, ← ((t1.add t2).add t3).tsum_add t4,
      ← t0.tsum_add ((((t1.add t2).add t3).add t4))]
    refine tsum_congr fun x => ?_
    simp only [rhsT]
    ring
  refine ⟨?_, ?_⟩
  · refine hI.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hsplit
  · have e : ∫ u in a..b, ∑' x, rhsT j r g y u x =
        ∫ u in a..b, (src4 j r g y u + rem4 j r g y u) :=
      intervalIntegral.integral_congr_ae hsplit
    rw [← e, ← key]
    rfl

end OVNS.Quant.Quartic

end
