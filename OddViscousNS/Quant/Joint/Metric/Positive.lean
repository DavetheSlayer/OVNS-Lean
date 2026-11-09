import OddViscousNS.Quant.Joint.Metric.Defs

/-!
# The positive convolution classes of the metric (step J5, pilot)

The convolution estimates behind every bound of the signed metric: the **seven classes** of Body 12
§7 and LOCAL577 (two slow leaves `E₂`), the **thirteen classes** of LOCAL83, LOCAL95 and NEW378
(three slow leaves `E_s^z`,
`checkpoints/COMPLETE_FORCED_UNWEIGHTED_CUBIC_HISTORY_378_CANDIDATE.md`), stated multilinearly in
the leaves, so that a restricted leaf is just another sequence.  This is LOCAL440 step 1: "the same
horizontal convolution as NEW378 with one restricted leaf".

## The classes
For the exteriors `α, β ∈ ℓ²` and the leaves `f_i`, with `u_i = |p|² f_i`:
* base `1`: `α, β ∈ ℓ²`, `f_i ∈ ℓ¹`;
* single `P_i²/L²`: `α/L² ∈ ℓ¹`, `β ∈ ℓ²`, `u_i ∈ ℓ²`, the other leaves `∈ ℓ¹`, and its transpose;
* pair `P_i² P_j²/(L²J²)`, `i ≠ j`: `α/L², β/J² ∈ ℓ¹`, `u_i, u_j ∈ ℓ²`, the last leaf `∈ ℓ¹`.
No same-slot `P_i⁴` occurs (LOCAL95 §4), and none is needed.

## The method
Every class is one chain of Young steps `β ↦ φ ⋆ β`, on the abstract bounds `L1B`, `L2B`: the sum
over the leaves is a convolution (`hasSum_Phi₃`, `hasSum_Phi₂`), one pairing ends it.  The lattice
constant is `c₄` on `ℤ³`, not the two-dimensional fibre constants of LOCAL577: "constants may be
loose", and the fibre argument is not needed, because `z/|k|²` is already `ℓ¹` on `ℤ³`.  So the
vertical sum needs no separate treatment.
-/

open Finset

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. Abstract `ℓ¹` and `ℓ²` bounds -/

/-- A nonnegative sequence of `ℓ¹` norm at most `B`. -/
structure L1B (f : Mode → ℝ) (B : ℝ) : Prop where
  nn : ∀ k, 0 ≤ f k
  s : Summable f
  le : ∑' k, f k ≤ B

/-- A nonnegative sequence of `ℓ²` norm at most `B`. -/
structure L2B (f : Mode → ℝ) (B : ℝ) : Prop where
  nn : ∀ k, 0 ≤ f k
  s : Summable fun k => f k ^ 2
  le : Real.sqrt (∑' k, f k ^ 2) ≤ B

variable {f g α β γ : Mode → ℝ} {A B C : ℝ}

lemma L1B.bd_nonneg (h : L1B f A) : 0 ≤ A := (tsum_nonneg h.nn).trans h.le

lemma L2B.bd_nonneg (h : L2B f A) : 0 ≤ A := (Real.sqrt_nonneg _).trans h.le

lemma L1B.mono (h : L1B f A) (hAB : A ≤ B) : L1B f B := ⟨h.nn, h.s, h.le.trans hAB⟩

lemma L2B.mono (h : L2B f A) (hAB : A ≤ B) : L2B f B := ⟨h.nn, h.s, h.le.trans hAB⟩

/-- The sharp `ℓ¹` bound. -/
lemma l1B_tsum (h0 : ∀ k, 0 ≤ f k) (hs : Summable f) : L1B f (∑' k, f k) := ⟨h0, hs, le_rfl⟩

/-- The sharp `ℓ²` bound. -/
lemma l2B_tsum (h0 : ∀ k, 0 ≤ f k) (hs : Summable fun k => f k ^ 2) :
    L2B f (Real.sqrt (∑' k, f k ^ 2)) := ⟨h0, hs, le_rfl⟩

lemma convR_nonneg (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k) (k : Mode) : 0 ≤ convR f g k :=
  tsum_nonneg fun p => mul_nonneg (hf p) (hg _)

/-- Tonelli for `hasSum`, on a nonnegative family over a product. -/
lemma hasSum_prod_nonneg {ι κ : Type*} {F : ι × κ → ℝ} (h0 : ∀ x, 0 ≤ F x) {S : ι → ℝ} {T : ℝ}
    (h1 : ∀ i, HasSum (fun k => F (i, k)) (S i)) (h2 : HasSum S T) : HasSum F T := by
  have hs : Summable F :=
    (summable_prod_of_nonneg h0).2 ⟨fun i => (h1 i).summable, h2.summable.congr fun i =>
      (h1 i).tsum_eq.symm⟩
  have h3 := hs.hasSum.prod_fiberwise h1
  rw [h2.unique h3]
  exact hs.hasSum

/-- `ℓ¹ ⋆ ℓ² ⊂ ℓ²`. -/
lemma L1B.conv_l2 (hf : L1B f A) (hg : L2B g B) :
    (∀ k, Summable fun p => f p * g (k - p)) ∧ L2B (convR f g) (A * B) := by
  obtain ⟨h1, h2, h3⟩ := young_l1_l2 hf.nn hg.nn hf.s hg.s
  refine ⟨h1, convR_nonneg hf.nn hg.nn, h2, ?_⟩
  have hA := hf.bd_nonneg
  have hB := hg.bd_nonneg
  have hT0 : 0 ≤ ∑' k, f k := tsum_nonneg hf.nn
  have hG0 : 0 ≤ ∑' k, g k ^ 2 := tsum_nonneg fun k => sq_nonneg _
  calc Real.sqrt (∑' k, convR f g k ^ 2)
      ≤ Real.sqrt ((∑' k, f k) ^ 2 * ∑' k, g k ^ 2) := Real.sqrt_le_sqrt h3
    _ = (∑' k, f k) * Real.sqrt (∑' k, g k ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hT0]
    _ ≤ A * B := mul_le_mul hf.le hg.le (Real.sqrt_nonneg _) hA

/-- `ℓ² ⋆ ℓ¹ ⊂ ℓ²`. -/
lemma L2B.conv_l1 (hf : L2B f A) (hg : L1B g B) :
    (∀ k, Summable fun p => f p * g (k - p)) ∧ L2B (convR f g) (A * B) := by
  obtain ⟨h1, h2⟩ := hg.conv_l2 hf
  have e : convR f g = convR g f := funext (convR_comm f g)
  refine ⟨fun k => ?_, by rw [e, mul_comm]; exact h2⟩
  have := (Equiv.subLeft k).summable_iff.mpr (h1 k)
  refine this.congr fun p => ?_
  simp [mul_comm]

/-- `ℓ¹ ⋆ ℓ¹ ⊂ ℓ¹`. -/
lemma L1B.conv_l1 (hf : L1B f A) (hg : L1B g B) :
    (∀ k, Summable fun p => f p * g (k - p)) ∧ L1B (convR f g) (A * B) := by
  have hG : Summable fun z : Mode × Mode => f z.1 * g z.2 := hf.s.mul_of_nonneg hg.s hf.nn hg.nn
  let sh : Mode × Mode ≃ Mode × Mode :=
    { toFun := fun z => (z.2, z.1 - z.2), invFun := fun z => (z.1 + z.2, z.1),
      left_inv := fun z => by simp, right_inv := fun z => by simp }
  have hF : Summable fun z : Mode × Mode => f z.2 * g (z.1 - z.2) := sh.summable_iff.2 hG
  have hin : ∀ k, Summable fun p => f p * g (k - p) := fun k => hF.prod_factor k
  have ht : ∑' k, convR f g k = (∑' k, f k) * ∑' k, g k := by
    rw [hf.s.tsum_mul_tsum hg.s hG, ← sh.tsum_eq (fun z : Mode × Mode => f z.1 * g z.2)]
    exact (hF.tsum_prod).symm
  refine ⟨hin, convR_nonneg hf.nn hg.nn, hF.prod, ?_⟩
  rw [ht]
  exact mul_le_mul hf.le hg.le (tsum_nonneg hg.nn) hf.bd_nonneg

/-- `ℓ² ⋆ ℓ² ⊂ ℓ^∞`. -/
lemma L2B.conv_sup (hf : L2B f A) (hg : L2B g B) (k : Mode) :
    Summable (fun p => f p * g (k - p)) ∧ convR f g k ≤ A * B := by
  obtain ⟨h1, h2⟩ := convR_le_of_l2 hf.nn hg.nn hf.s hg.s k
  exact ⟨h1, h2.trans (mul_le_mul hf.le hg.le (Real.sqrt_nonneg _) hf.bd_nonneg)⟩

/-- The pairing `ℓ² × ℓ²`. -/
lemma L2B.pair (hf : L2B f A) (hg : L2B g B) :
    Summable (fun k => f k * g k) ∧ ∑' k, f k * g k ≤ A * B := by
  obtain ⟨h1, h2⟩ := cs_tsum_nonneg' hf.nn hg.nn hf.s hg.s
  exact ⟨h1, h2.trans (mul_le_mul hf.le hg.le (Real.sqrt_nonneg _) hf.bd_nonneg)⟩

/-- The pairing `ℓ¹ × ℓ^∞`. -/
lemma L1B.pair_sup (hf : L1B f A) (h0 : ∀ k, 0 ≤ g k) (hg : ∀ k, g k ≤ B) (hB : 0 ≤ B) :
    Summable (fun k => f k * g k) ∧ ∑' k, f k * g k ≤ A * B := by
  have hs : Summable (fun k => f k * g k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hf.nn k) (h0 k))
      (fun k => mul_le_mul_of_nonneg_left (hg k) (hf.nn k)) (hf.s.mul_right B)
  refine ⟨hs, ?_⟩
  calc ∑' k, f k * g k ≤ ∑' k, f k * B :=
        hs.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hg k) (hf.nn k)) (hf.s.mul_right B)
    _ = (∑' k, f k) * B := tsum_mul_right
    _ ≤ A * B := mul_le_mul_of_nonneg_right hf.le hB

/-! ### B. The inverse weights and the two lattice bounds -/

/-- `α/|k|²`, the exterior weight of a class. -/
def in2 (α : Mode → ℝ) (k : Mode) : ℝ := α k / absSq k

/-- `|p|² f`, the leaf weight of a class. -/
def up (f : Mode → ℝ) (p : Mode) : ℝ := absSq p * f p

/-- `‖α/|k|²‖_{ℓ¹} ≤ c₄ ‖α‖_{ℓ²}` (Body 12 §4: "`‖z/Q²‖_{ℓ¹} ≤ √104 ‖z‖₂`"). -/
lemma L2B.in2 (h : L2B α A) : L1B (in2 α) (c4 * A) := by
  classical
  set w : Mode → ℝ := fun k => if k = 0 then 0 else (absSq k)⁻¹ with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by
    simp only [hw]
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.2 (absSq_nonneg k)
  have hw2 : (fun k => w k ^ 2) = fun k : Mode => if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2 := by
    funext k
    simp only [hw]
    split_ifs <;> simp
  have hw3 : Real.sqrt (∑' k, w k ^ 2) = c4 := by rw [hw2]; rfl
  obtain ⟨hs, hle⟩ := cs_tsum_nonneg' h.nn hw0 h.s (by rw [hw2]; exact summable_inv4)
  have e : ∀ k, α k * w k = OVNS.Quant.Metric.in2 α k := fun k => by
    simp only [hw, Metric.in2]
    split_ifs with hk
    · simp [hk, absSq]
    · rw [div_eq_mul_inv]
  simp only [e] at hs hle
  refine ⟨fun k => div_nonneg (h.nn k) (absSq_nonneg k), hs, hle.trans ?_⟩
  rw [hw3, mul_comm]
  exact mul_le_mul_of_nonneg_left h.le c4_pos.le

/-! ### C. Three leaves: `Φ₃`, the thirteen classes of `E_s^z` -/

/-- The positive form of three leaves. -/
def Phi₃ (α β f₁ f₂ f₃ : Mode → ℝ) (x : I4) : ℝ :=
  α x.1 * β (inJ x) * (f₁ x.2.1 * f₂ x.2.2.1 * f₃ x.2.2.2)

variable {f₁ f₂ f₃ : Mode → ℝ}

lemma Phi₃_nonneg (hα : ∀ k, 0 ≤ α k) (hβ : ∀ k, 0 ≤ β k) (h1 : ∀ k, 0 ≤ f₁ k)
    (h2 : ∀ k, 0 ≤ f₂ k) (h3 : ∀ k, 0 ≤ f₃ k) (x : I4) : 0 ≤ Phi₃ α β f₁ f₂ f₃ x :=
  mul_nonneg (mul_nonneg (hα _) (hβ _)) (mul_nonneg (mul_nonneg (h1 _) (h2 _)) (h3 _))

/-- **The sum over the leaves is an iterated convolution.** -/
lemma hasSum_Phi₃ (hα : ∀ k, 0 ≤ α k) (hβ : ∀ k, 0 ≤ β k) (h1 : ∀ k, 0 ≤ f₁ k)
    (h2 : ∀ k, 0 ≤ f₂ k) (h3 : ∀ k, 0 ≤ f₃ k)
    (s3 : ∀ t, Summable fun c => f₃ c * β (t - c))
    (s2 : ∀ t, Summable fun b => f₂ b * convR f₃ β (t - b))
    (s1 : ∀ t, Summable fun a => f₁ a * convR f₂ (convR f₃ β) (t - a))
    (s0 : Summable fun l => α l * convR f₁ (convR f₂ (convR f₃ β)) l) :
    HasSum (Phi₃ α β f₁ f₂ f₃) (∑' l, α l * convR f₁ (convR f₂ (convR f₃ β)) l) := by
  have hF := Phi₃_nonneg hα hβ h1 h2 h3
  have hc : ∀ l a b, HasSum (fun c => Phi₃ α β f₁ f₂ f₃ (l, a, b, c))
      (α l * f₁ a * f₂ b * convR f₃ β (l - a - b)) := fun l a b => by
    have e : (fun c => Phi₃ α β f₁ f₂ f₃ (l, a, b, c)) =
        fun c => α l * f₁ a * f₂ b * (f₃ c * β (l - a - b - c)) := by
      funext c
      simp only [Phi₃, inJ]
      ring
    rw [e]
    exact (s3 (l - a - b)).hasSum.mul_left _
  have hb : ∀ l a, HasSum (fun y : Mode × Mode => Phi₃ α β f₁ f₂ f₃ (l, a, y))
      (α l * f₁ a * convR f₂ (convR f₃ β) (l - a)) := fun l a => by
    refine hasSum_prod_nonneg (fun y => hF _) (fun b => hc l a b) ?_
    have e : (fun b => α l * f₁ a * f₂ b * convR f₃ β (l - a - b)) =
        fun b => α l * f₁ a * (f₂ b * convR f₃ β (l - a - b)) := by
      funext b
      ring
    rw [e]
    exact (s2 (l - a)).hasSum.mul_left _
  have ha : ∀ l, HasSum (fun y : Mode × Mode × Mode => Phi₃ α β f₁ f₂ f₃ (l, y))
      (α l * convR f₁ (convR f₂ (convR f₃ β)) l) := fun l => by
    refine hasSum_prod_nonneg (fun y => hF _) (fun a => hb l a) ?_
    have e : (fun a => α l * f₁ a * convR f₂ (convR f₃ β) (l - a)) =
        fun a => α l * (f₁ a * convR f₂ (convR f₃ β) (l - a)) := by
      funext a
      ring
    rw [e]
    exact (s1 l).hasSum.mul_left _
  exact hasSum_prod_nonneg hF ha s0.hasSum

/-- The base class. -/
lemma pos3_I {C₁ C₂ C₃ : ℝ} (hα : L2B α A) (hβ : L2B β B) (h1 : L1B f₁ C₁) (h2 : L1B f₂ C₂)
    (h3 : L1B f₃ C₃) :
    Summable (Phi₃ α β f₁ f₂ f₃) ∧ ∑' x, Phi₃ α β f₁ f₂ f₃ x ≤ A * B * (C₁ * C₂ * C₃) := by
  obtain ⟨s3, b1⟩ := h3.conv_l2 hβ
  obtain ⟨s2, b2⟩ := h2.conv_l2 b1
  obtain ⟨s1, b3⟩ := h1.conv_l2 b2
  obtain ⟨s0, hle⟩ := hα.pair b3
  have hS := hasSum_Phi₃ hα.nn hβ.nn h1.nn h2.nn h3.nn s3 s2 s1 s0
  refine ⟨hS.summable, ?_⟩
  rw [hS.tsum_eq]
  exact hle.trans (le_of_eq (by ring))

/-- A single class, with the weighted leaf in the first slot and the exterior weight on the output:
`ℓ² ⋆ ℓ²` is bounded, and pairs with the `ℓ¹` output. -/
lemma pos3_II {C₁ C₂ C₃ : ℝ} (hα : L1B α A) (hβ : L2B β B) (h1 : L2B f₁ C₁) (h2 : L1B f₂ C₂)
    (h3 : L1B f₃ C₃) :
    Summable (Phi₃ α β f₁ f₂ f₃) ∧ ∑' x, Phi₃ α β f₁ f₂ f₃ x ≤ A * B * (C₁ * C₂ * C₃) := by
  obtain ⟨s3, b1⟩ := h3.conv_l2 hβ
  obtain ⟨s2, b2⟩ := h2.conv_l2 b1
  have hsup := h1.conv_sup b2
  have hB : 0 ≤ C₁ * (C₂ * (C₃ * B)) := mul_nonneg h1.bd_nonneg b2.bd_nonneg
  obtain ⟨s0, hle⟩ := hα.pair_sup (convR_nonneg h1.nn b2.nn) (fun k => (hsup k).2) hB
  have hS := hasSum_Phi₃ hα.nn hβ.nn h1.nn h2.nn h3.nn s3 s2 (fun t => (hsup t).1) s0
  refine ⟨hS.summable, ?_⟩
  rw [hS.tsum_eq]
  exact hle.trans (le_of_eq (by ring))

/-- A single class, with the exterior weight on the input: the transpose of `pos3_II`. -/
lemma pos3_II' {C₁ C₂ C₃ : ℝ} (hα : L2B α A) (hβ : L1B β B) (h1 : L2B f₁ C₁) (h2 : L1B f₂ C₂)
    (h3 : L1B f₃ C₃) :
    Summable (Phi₃ α β f₁ f₂ f₃) ∧ ∑' x, Phi₃ α β f₁ f₂ f₃ x ≤ A * B * (C₁ * C₂ * C₃) := by
  obtain ⟨s3, b1⟩ := h3.conv_l1 hβ
  obtain ⟨s2, b2⟩ := h2.conv_l1 b1
  obtain ⟨s1, b3⟩ := h1.conv_l1 b2
  obtain ⟨s0, hle⟩ := hα.pair b3
  have hS := hasSum_Phi₃ hα.nn hβ.nn h1.nn h2.nn h3.nn s3 s2 s1 s0
  refine ⟨hS.summable, ?_⟩
  rw [hS.tsum_eq]
  exact hle.trans (le_of_eq (by ring))

/-- A distinct pair: two weighted leaves in `ℓ²`, both exterior weights. -/
lemma pos3_III {C₁ C₂ C₃ : ℝ} (hα : L1B α A) (hβ : L1B β B) (h1 : L2B f₁ C₁) (h2 : L2B f₂ C₂)
    (h3 : L1B f₃ C₃) :
    Summable (Phi₃ α β f₁ f₂ f₃) ∧ ∑' x, Phi₃ α β f₁ f₂ f₃ x ≤ A * B * (C₁ * C₂ * C₃) := by
  obtain ⟨s3, b1⟩ := h3.conv_l1 hβ
  obtain ⟨s2, b2⟩ := h2.conv_l1 b1
  have hsup := h1.conv_sup b2
  have hB : 0 ≤ C₁ * (C₂ * (C₃ * B)) := mul_nonneg h1.bd_nonneg b2.bd_nonneg
  obtain ⟨s0, hle⟩ := hα.pair_sup (convR_nonneg h1.nn b2.nn) (fun k => (hsup k).2) hB
  have hS := hasSum_Phi₃ hα.nn hβ.nn h1.nn h2.nn h3.nn s3 s2 (fun t => (hsup t).1) s0
  refine ⟨hS.summable, ?_⟩
  rw [hS.tsum_eq]
  exact hle.trans (le_of_eq (by ring))

/-- A summable family with a bound on its sum. -/
def SB {ι : Type*} (F : ι → ℝ) (B : ℝ) : Prop := Summable F ∧ ∑' x, F x ≤ B

lemma SB.add {ι : Type*} {F G : ι → ℝ} {A B : ℝ} (hF : SB F A) (hG : SB G B) :
    SB (fun x => F x + G x) (A + B) :=
  ⟨hF.1.add hG.1, by rw [hF.1.tsum_add hG.1]; exact add_le_add hF.2 hG.2⟩

lemma SB.const_mul {ι : Type*} {F : ι → ℝ} {A : ℝ} (hF : SB F A) {c : ℝ} (hc : 0 ≤ c) :
    SB (fun x => c * F x) (c * A) :=
  ⟨hF.1.mul_left c, by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hF.2 hc⟩

lemma SB.mono_bd {ι : Type*} {F : ι → ℝ} {A B : ℝ} (hF : SB F A) (h : A ≤ B) : SB F B :=
  ⟨hF.1, hF.2.trans h⟩

/-- A family dominated by a family with a bound. -/
lemma SB.of_le {ι : Type*} {F G : ι → ℝ} {A : ℝ} (hG : SB G A) (h0 : ∀ x, 0 ≤ F x)
    (h : ∀ x, F x ≤ G x) : SB F A := by
  have hs := Summable.of_nonneg_of_le h0 h hG.1
  exact ⟨hs, (hs.tsum_le_tsum h hG.1).trans hG.2⟩

/-- Reindexing. -/
lemma SB.equiv {ι : Type*} {F G : ι → ℝ} {A : ℝ} (e : ι ≃ ι) (hF : SB F A)
    (h : ∀ x, G x = F (e x)) : SB G A := by
  have hG : G = fun x => F (e x) := funext h
  rw [hG]
  exact ⟨e.summable_iff.2 hF.1, (e.tsum_eq F).le.trans hF.2⟩

/-- The exchange of the first two leaves. -/
def swap12 : I4 ≃ I4 :=
  Function.Involutive.toPerm (fun x => (x.1, x.2.2.1, x.2.1, x.2.2.2)) fun _ => rfl

/-- The exchange of the last two leaves. -/
def swap23 : I4 ≃ I4 :=
  Function.Involutive.toPerm (fun x => (x.1, x.2.1, x.2.2.2, x.2.2.1)) fun _ => rfl

lemma swap12_apply (x : I4) : swap12 x = (x.1, x.2.2.1, x.2.1, x.2.2.2) := rfl

lemma swap23_apply (x : I4) : swap23 x = (x.1, x.2.1, x.2.2.2, x.2.2.1) := rfl

lemma inJ_swap12 (x : I4) : inJ (swap12 x) = inJ x := by
  rw [swap12_apply]
  simp only [inJ]
  abel

lemma inJ_swap23 (x : I4) : inJ (swap23 x) = inJ x := by
  rw [swap23_apply]
  simp only [inJ]
  abel

lemma Phi₃_swap12 (α β f₁ f₂ f₃ : Mode → ℝ) (x : I4) :
    Phi₃ α β f₁ f₂ f₃ x = Phi₃ α β f₂ f₁ f₃ (swap12 x) := by
  simp only [Phi₃, inJ_swap12]
  rw [swap12_apply]
  ring

lemma Phi₃_swap23 (α β f₁ f₂ f₃ : Mode → ℝ) (x : I4) :
    Phi₃ α β f₁ f₂ f₃ x = Phi₃ α β f₁ f₃ f₂ (swap23 x) := by
  simp only [Phi₃, inJ_swap23]
  rw [swap23_apply]
  ring

/-- **The envelope `E_2^z`** of NEW378, at the labels `x = (l, a, b, c)`: base, six singles and the
distinct pairs (each unordered pair once; LOCAL95 §4 has `E` with the pairs ordered).  There is no
`P_i⁴`.  With `A = |a|²`, …, `L = |l|²`, `J = |j|²`. -/
def E3 (x : I4) : ℝ :=
  1 + (absSq x.2.1 + absSq x.2.2.1 + absSq x.2.2.2) / absSq x.1 +
    (absSq x.2.1 + absSq x.2.2.1 + absSq x.2.2.2) / absSq (inJ x) +
    (absSq x.2.1 * absSq x.2.2.1 + absSq x.2.1 * absSq x.2.2.2 +
      absSq x.2.2.1 * absSq x.2.2.2) / (absSq x.1 * absSq (inJ x))

/-- The value of the thirteen classes, with `W_i` the `ℓ¹` bounds of the leaves and `U_i` the `ℓ²`
bounds of `|p|² f_i`. -/
def cls3 (W₁ W₂ W₃ U₁ U₂ U₃ : ℝ) : ℝ :=
  W₁ * W₂ * W₃ + 2 * c4 * (U₁ * W₂ * W₃ + W₁ * U₂ * W₃ + W₁ * W₂ * U₃) +
    c4 ^ 2 * (U₁ * U₂ * W₃ + U₁ * W₂ * U₃ + W₁ * U₂ * U₃)

/-- **The thirteen classes** (LOCAL95 §5, NEW378 "Full H2 multiplier"), multilinear in the leaves:
`∑ |α_l| |β_j| f₁(a) f₂(b) f₃(c) E ≤ ‖α‖ ‖β‖ cls₃`. -/
theorem pos3_E3 {W₁ W₂ W₃ U₁ U₂ U₃ : ℝ} (hα : L2B α A) (hβ : L2B β B) (h1 : L1B f₁ W₁)
    (h2 : L1B f₂ W₂) (h3 : L1B f₃ W₃) (u1 : L2B (up f₁) U₁) (u2 : L2B (up f₂) U₂)
    (u3 : L2B (up f₃) U₃) :
    SB (fun x => Phi₃ α β f₁ f₂ f₃ x * E3 x) (A * B * cls3 W₁ W₂ W₃ U₁ U₂ U₃) := by
  have ha := hα.in2
  have hb := hβ.in2
  have t0 : SB (Phi₃ α β f₁ f₂ f₃) (A * B * (W₁ * W₂ * W₃)) := pos3_I hα hβ h1 h2 h3
  have t1 : SB (Phi₃ (in2 α) β (up f₁) f₂ f₃) (c4 * A * B * (U₁ * W₂ * W₃)) :=
    pos3_II ha hβ u1 h2 h3
  have t2 : SB (Phi₃ (in2 α) β f₁ (up f₂) f₃) (c4 * A * B * (U₂ * W₁ * W₃)) :=
    SB.equiv swap12 (pos3_II ha hβ u2 h1 h3) (Phi₃_swap12 _ _ _ _ _)
  have t3 : SB (Phi₃ (in2 α) β f₁ f₂ (up f₃)) (c4 * A * B * (U₃ * W₁ * W₂)) :=
    SB.equiv swap23 (SB.equiv swap12 (pos3_II ha hβ u3 h1 h2) (Phi₃_swap12 _ _ _ _ _))
      (Phi₃_swap23 _ _ _ _ _)
  have t4 : SB (Phi₃ α (in2 β) (up f₁) f₂ f₃) (A * (c4 * B) * (U₁ * W₂ * W₃)) :=
    pos3_II' hα hb u1 h2 h3
  have t5 : SB (Phi₃ α (in2 β) f₁ (up f₂) f₃) (A * (c4 * B) * (U₂ * W₁ * W₃)) :=
    SB.equiv swap12 (pos3_II' hα hb u2 h1 h3) (Phi₃_swap12 _ _ _ _ _)
  have t6 : SB (Phi₃ α (in2 β) f₁ f₂ (up f₃)) (A * (c4 * B) * (U₃ * W₁ * W₂)) :=
    SB.equiv swap23 (SB.equiv swap12 (pos3_II' hα hb u3 h1 h2) (Phi₃_swap12 _ _ _ _ _))
      (Phi₃_swap23 _ _ _ _ _)
  have t7 : SB (Phi₃ (in2 α) (in2 β) (up f₁) (up f₂) f₃) (c4 * A * (c4 * B) * (U₁ * U₂ * W₃)) :=
    pos3_III ha hb u1 u2 h3
  have t8 : SB (Phi₃ (in2 α) (in2 β) (up f₁) f₂ (up f₃)) (c4 * A * (c4 * B) * (U₁ * U₃ * W₂)) :=
    SB.equiv swap23 (pos3_III ha hb u1 u3 h2) (Phi₃_swap23 _ _ _ _ _)
  have t9 : SB (Phi₃ (in2 α) (in2 β) f₁ (up f₂) (up f₃)) (c4 * A * (c4 * B) * (U₂ * U₃ * W₁)) :=
    SB.equiv swap12 (SB.equiv swap23 (pos3_III ha hb u2 u3 h1) (Phi₃_swap23 _ _ _ _ _))
      (Phi₃_swap12 _ _ _ _ _)
  have h := ((((((((((t0.add t1).add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9))
  have e : (fun x => Phi₃ α β f₁ f₂ f₃ x * E3 x) = fun x =>
      Phi₃ α β f₁ f₂ f₃ x + Phi₃ (in2 α) β (up f₁) f₂ f₃ x + Phi₃ (in2 α) β f₁ (up f₂) f₃ x +
        Phi₃ (in2 α) β f₁ f₂ (up f₃) x + Phi₃ α (in2 β) (up f₁) f₂ f₃ x +
        Phi₃ α (in2 β) f₁ (up f₂) f₃ x + Phi₃ α (in2 β) f₁ f₂ (up f₃) x +
        Phi₃ (in2 α) (in2 β) (up f₁) (up f₂) f₃ x + Phi₃ (in2 α) (in2 β) (up f₁) f₂ (up f₃) x +
        Phi₃ (in2 α) (in2 β) f₁ (up f₂) (up f₃) x := by
    funext x
    simp only [Phi₃, E3, in2, up]
    ring
  rw [e]
  refine h.mono_bd (le_of_eq ?_)
  simp only [cls3]
  ring

/-! ### D. Two leaves: `Φ₂`, the seven classes of `E₂` -/

/-- The input label `j = l − a − b` of `x = (l, a, b)`. -/
def inJ₂ (x : I3) : Mode := x.1 - x.2.1 - x.2.2

/-- The positive form of two leaves. -/
def Phi₂ (α β f₁ f₂ : Mode → ℝ) (x : I3) : ℝ := α x.1 * β (inJ₂ x) * (f₁ x.2.1 * f₂ x.2.2)

lemma Phi₂_nonneg (hα : ∀ k, 0 ≤ α k) (hβ : ∀ k, 0 ≤ β k) (h1 : ∀ k, 0 ≤ f₁ k)
    (h2 : ∀ k, 0 ≤ f₂ k) (x : I3) : 0 ≤ Phi₂ α β f₁ f₂ x :=
  mul_nonneg (mul_nonneg (hα _) (hβ _)) (mul_nonneg (h1 _) (h2 _))

lemma hasSum_Phi₂ (hα : ∀ k, 0 ≤ α k) (hβ : ∀ k, 0 ≤ β k) (h1 : ∀ k, 0 ≤ f₁ k)
    (h2 : ∀ k, 0 ≤ f₂ k) (s2 : ∀ t, Summable fun b => f₂ b * β (t - b))
    (s1 : ∀ t, Summable fun a => f₁ a * convR f₂ β (t - a))
    (s0 : Summable fun l => α l * convR f₁ (convR f₂ β) l) :
    HasSum (Phi₂ α β f₁ f₂) (∑' l, α l * convR f₁ (convR f₂ β) l) := by
  have hF := Phi₂_nonneg hα hβ h1 h2
  have hb : ∀ l a, HasSum (fun b => Phi₂ α β f₁ f₂ (l, a, b))
      (α l * f₁ a * convR f₂ β (l - a)) := fun l a => by
    have e : (fun b => Phi₂ α β f₁ f₂ (l, a, b)) =
        fun b => α l * f₁ a * (f₂ b * β (l - a - b)) := by
      funext b
      simp only [Phi₂, inJ₂]
      ring
    rw [e]
    exact (s2 (l - a)).hasSum.mul_left _
  have ha : ∀ l, HasSum (fun y : Mode × Mode => Phi₂ α β f₁ f₂ (l, y))
      (α l * convR f₁ (convR f₂ β) l) := fun l => by
    refine hasSum_prod_nonneg (fun y => hF _) (fun a => hb l a) ?_
    have e : (fun a => α l * f₁ a * convR f₂ β (l - a)) =
        fun a => α l * (f₁ a * convR f₂ β (l - a)) := by
      funext a
      ring
    rw [e]
    exact (s1 l).hasSum.mul_left _
  exact hasSum_prod_nonneg hF ha s0.hasSum

lemma pos2_I {C₁ C₂ : ℝ} (hα : L2B α A) (hβ : L2B β B) (h1 : L1B f₁ C₁) (h2 : L1B f₂ C₂) :
    SB (Phi₂ α β f₁ f₂) (A * B * (C₁ * C₂)) := by
  obtain ⟨s2, b1⟩ := h2.conv_l2 hβ
  obtain ⟨s1, b2⟩ := h1.conv_l2 b1
  obtain ⟨s0, hle⟩ := hα.pair b2
  have hS := hasSum_Phi₂ hα.nn hβ.nn h1.nn h2.nn s2 s1 s0
  refine ⟨hS.summable, ?_⟩
  rw [hS.tsum_eq]
  exact hle.trans (le_of_eq (by ring))

lemma pos2_II {C₁ C₂ : ℝ} (hα : L1B α A) (hβ : L2B β B) (h1 : L2B f₁ C₁) (h2 : L1B f₂ C₂) :
    SB (Phi₂ α β f₁ f₂) (A * B * (C₁ * C₂)) := by
  obtain ⟨s2, b1⟩ := h2.conv_l2 hβ
  have hsup := h1.conv_sup b1
  have hB : 0 ≤ C₁ * (C₂ * B) := mul_nonneg h1.bd_nonneg b1.bd_nonneg
  obtain ⟨s0, hle⟩ := hα.pair_sup (convR_nonneg h1.nn b1.nn) (fun k => (hsup k).2) hB
  have hS := hasSum_Phi₂ hα.nn hβ.nn h1.nn h2.nn s2 (fun t => (hsup t).1) s0
  refine ⟨hS.summable, ?_⟩
  rw [hS.tsum_eq]
  exact hle.trans (le_of_eq (by ring))

lemma pos2_II' {C₁ C₂ : ℝ} (hα : L2B α A) (hβ : L1B β B) (h1 : L2B f₁ C₁) (h2 : L1B f₂ C₂) :
    SB (Phi₂ α β f₁ f₂) (A * B * (C₁ * C₂)) := by
  obtain ⟨s2, b1⟩ := h2.conv_l1 hβ
  obtain ⟨s1, b2⟩ := h1.conv_l1 b1
  obtain ⟨s0, hle⟩ := hα.pair b2
  have hS := hasSum_Phi₂ hα.nn hβ.nn h1.nn h2.nn s2 s1 s0
  refine ⟨hS.summable, ?_⟩
  rw [hS.tsum_eq]
  exact hle.trans (le_of_eq (by ring))

lemma pos2_III {C₁ C₂ : ℝ} (hα : L1B α A) (hβ : L1B β B) (h1 : L2B f₁ C₁) (h2 : L2B f₂ C₂) :
    SB (Phi₂ α β f₁ f₂) (A * B * (C₁ * C₂)) := by
  obtain ⟨s2, b1⟩ := h2.conv_l1 hβ
  have hsup := h1.conv_sup b1
  have hB : 0 ≤ C₁ * (C₂ * B) := mul_nonneg h1.bd_nonneg b1.bd_nonneg
  obtain ⟨s0, hle⟩ := hα.pair_sup (convR_nonneg h1.nn b1.nn) (fun k => (hsup k).2) hB
  have hS := hasSum_Phi₂ hα.nn hβ.nn h1.nn h2.nn s2 (fun t => (hsup t).1) s0
  refine ⟨hS.summable, ?_⟩
  rw [hS.tsum_eq]
  exact hle.trans (le_of_eq (by ring))

/-- The exchange of the two leaves. -/
def swapL : I3 ≃ I3 := Function.Involutive.toPerm (fun x => (x.1, x.2.2, x.2.1)) fun _ => rfl

lemma swapL_apply (x : I3) : swapL x = (x.1, x.2.2, x.2.1) := rfl

lemma inJ₂_swapL (x : I3) : inJ₂ (swapL x) = inJ₂ x := by
  rw [swapL_apply]
  simp only [inJ₂]
  abel

lemma Phi₂_swapL (α β f₁ f₂ : Mode → ℝ) (x : I3) :
    Phi₂ α β f₁ f₂ x = Phi₂ α β f₂ f₁ (swapL x) := by
  simp only [Phi₂, inJ₂_swapL]
  rw [swapL_apply]
  ring

/-- **The envelope `E₂`** of Body 12 §7 at `(l, a, b)`: base, four singles, the distinct pair. -/
def E2 (x : I3) : ℝ :=
  1 + (absSq x.2.1 + absSq x.2.2) / absSq x.1 + (absSq x.2.1 + absSq x.2.2) / absSq (inJ₂ x) +
    absSq x.2.1 * absSq x.2.2 / (absSq x.1 * absSq (inJ₂ x))

/-- The value of the seven classes. -/
def cls2 (W₁ W₂ U₁ U₂ : ℝ) : ℝ :=
  W₁ * W₂ + 2 * c4 * (U₁ * W₂ + W₁ * U₂) + c4 ^ 2 * (U₁ * U₂)

/-- **The seven classes** (Body 12 §7; LOCAL577 "Common fast fibre and seven classes"), multilinear
in the two leaves. -/
theorem pos2_E2 {W₁ W₂ U₁ U₂ : ℝ} (hα : L2B α A) (hβ : L2B β B) (h1 : L1B f₁ W₁) (h2 : L1B f₂ W₂)
    (u1 : L2B (up f₁) U₁) (u2 : L2B (up f₂) U₂) :
    SB (fun x => Phi₂ α β f₁ f₂ x * E2 x) (A * B * cls2 W₁ W₂ U₁ U₂) := by
  have ha := hα.in2
  have hb := hβ.in2
  have t0 : SB (Phi₂ α β f₁ f₂) (A * B * (W₁ * W₂)) := pos2_I hα hβ h1 h2
  have t1 : SB (Phi₂ (in2 α) β (up f₁) f₂) (c4 * A * B * (U₁ * W₂)) := pos2_II ha hβ u1 h2
  have t2 : SB (Phi₂ (in2 α) β f₁ (up f₂)) (c4 * A * B * (U₂ * W₁)) :=
    SB.equiv swapL (pos2_II ha hβ u2 h1) (Phi₂_swapL _ _ _ _)
  have t3 : SB (Phi₂ α (in2 β) (up f₁) f₂) (A * (c4 * B) * (U₁ * W₂)) := pos2_II' hα hb u1 h2
  have t4 : SB (Phi₂ α (in2 β) f₁ (up f₂)) (A * (c4 * B) * (U₂ * W₁)) :=
    SB.equiv swapL (pos2_II' hα hb u2 h1) (Phi₂_swapL _ _ _ _)
  have t5 : SB (Phi₂ (in2 α) (in2 β) (up f₁) (up f₂)) (c4 * A * (c4 * B) * (U₁ * U₂)) :=
    pos2_III ha hb u1 u2
  have h := ((((t0.add t1).add t2).add t3).add t4).add t5
  have e : (fun x => Phi₂ α β f₁ f₂ x * E2 x) = fun x =>
      Phi₂ α β f₁ f₂ x + Phi₂ (in2 α) β (up f₁) f₂ x + Phi₂ (in2 α) β f₁ (up f₂) x +
        Phi₂ α (in2 β) (up f₁) f₂ x + Phi₂ α (in2 β) f₁ (up f₂) x +
        Phi₂ (in2 α) (in2 β) (up f₁) (up f₂) x := by
    funext x
    simp only [Phi₂, E2, in2, up]
    ring
  rw [e]
  refine h.mono_bd (le_of_eq ?_)
  simp only [cls2]
  ring

end OVNS.Quant.Metric

end
