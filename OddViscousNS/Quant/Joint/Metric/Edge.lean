import OddViscousNS.Quant.Joint.Metric.Heat
import OddViscousNS.Quant.Joint.Metric.StaticForm

/-!
# The mixed form of `X₁` with an `H¹` leaf (step J5, node N5)

Body 40: `|⟨z, X₁[h] w⟩| ≤ C q⁻¹ ‖h‖₁ (‖z‖₀ ‖A^{1/2} w‖₀ + ‖A^{1/2} z‖₀ ‖w‖₀)`.

Body 40 polarizes the signed diagonal form.  Here the bound is proved directly, termwise: the block
bound `|X₁| ≤ C q⁻¹ ‖h_p‖ (K²/J² + J²/K²)` (`norm_X1b_two_le`, `norm_X1b_one_le`) is all that is
needed, with three sectors (`edge_mixed`):
* `J ≤ 2K`, `K ≤ 2J`: the kernel is bounded.  Put the derivative on the output and use
  `∑_p |j + p|⁻² |p|⁻² ≤ 17`, on the plane through `j`;
* `J > 2K`: then `P ≥ J/2`, so `J²/K² ≤ 2 P J / K²`, and `∑_k K⁻⁴ = c₄²`;
* `K > 2J`: the same with `G, F` exchanged.
So no polarization is needed, and no reality of `G, F`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {α β γ : Mode → ℝ} {A₀ A₁ B₀ B₁ U : ℝ}

/-- A product of two sums. -/
lemma SB.pairing {ι κ : Type*} {f : ι → ℝ} {g : κ → ℝ} {A B : ℝ} (hf : SB f A) (hg : SB g B)
    (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ k, 0 ≤ g k) :
    SB (fun x : ι × κ => f x.1 * g x.2) (A * B) := by
  have hB : 0 ≤ B := (tsum_nonneg hg0).trans hg.2
  have hc : SB (fun i => f i * B) (A * B) := by
    refine ⟨hf.1.mul_right B, ?_⟩
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right hf.2 hB
  exact SB.prod (fun y => mul_nonneg (hf0 _) (hg0 _)) (fun i => hg.const_mul (hf0 i)) hc

/-- The edge relabelling `(k, p) ↦ (k − p, p)`. -/
def edgeE : Mode × Mode ≃ Mode × Mode where
  toFun x := (x.1 - x.2, x.2)
  invFun y := (y.1 + y.2, y.2)
  left_inv := fun ⟨k, p⟩ => Prod.ext (show k - p + p = k by abel) rfl
  right_inv := fun ⟨j, p⟩ => Prod.ext (show j + p - p = j by abel) rfl

/-- The sum of `K⁻⁴`. -/
lemma sb_inv4 : SB (fun k : Mode => if k = 0 then (0 : ℝ) else (absk k)⁻¹ ^ 4) (c4 ^ 2) := by
  have e : ∀ k : Mode, (if k = 0 then (0 : ℝ) else (absk k)⁻¹ ^ 4) =
      if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2 := fun k => by
    split_ifs
    · rfl
    · rw [← absk_sq k]
      simp only [inv_pow]
      rw [← pow_mul]
  simp only [e]
  refine ⟨summable_inv4, ?_⟩
  rw [c4, Real.sq_sqrt (tsum_nonneg fun k => by split_ifs <;> positivity)]

/-- `∑_p |j + p|⁻² |p|⁻² ≤ 17` on the plane. -/
lemma sb_plane (j : Mode) :
    SB (fun p : Mode => (absk (j + p))⁻¹ ^ 2 * (absk p)⁻¹ ^ 2 * if p 2 = 0 then 1 else 0) 17 := by
  have h1 := fib_w4.add j
  have h2 := fib_w4.add 0
  have h3 := (h1.add h2).const_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have e : (1 / 2 : ℝ) * (17 + 17) = 17 := by norm_num
  rw [e] at h3
  refine h3.of_le (fun p => ?_) fun p => ?_
  · have := inv_nonneg.2 (absk_nonneg (j + p))
    have := inv_nonneg.2 (absk_nonneg p)
    split_ifs <;> positivity
  · by_cases hp : p 2 = 0
    · simp only [hp, ite_true, zero_add, w4, mul_one]
      set x := (absk (j + p))⁻¹
      set y := (absk p)⁻¹
      nlinarith only [sq_nonneg (x ^ 2 - y ^ 2)]
    · simp [hp]

lemma plane_nonneg (i k : Mode) :
    0 ≤ (absk (i + k))⁻¹ ^ 2 * (absk k)⁻¹ ^ 2 * if k 2 = 0 then (1 : ℝ) else 0 := by
  have := inv_nonneg.2 (absk_nonneg (i + k))
  have := inv_nonneg.2 (absk_nonneg k)
  split_ifs <;> positivity

/-- The first sector: both exteriors comparable. -/
lemma sb_edgeA (hα1 : L2B (fun k => absk k * α k) A₁) (hβ : L2B β B₀) (hγ : SlowH1 γ U) :
    SB (fun x : Mode × Mode => (absk x.1 * α x.1 * (absk x.2 * γ x.2)) *
      (β (x.1 - x.2) * ((absk x.1)⁻¹ * (absk x.2)⁻¹ * if x.2 2 = 0 then 1 else 0)))
      (A₁ * U * (Real.sqrt 17 * B₀)) := by
  have hA := hα1.bd_nonneg
  have hU := hγ.grad.bd_nonneg
  have hB := hβ.bd_nonneg
  refine SB.cs (fun x => mul_nonneg (hα1.nn _) (hγ.grad.nn _)) (fun x => mul_nonneg (hβ.nn _) ?_)
    (by positivity) (by positivity) ?_ ?_
  · have := inv_nonneg.2 (absk_nonneg x.1)
    have := inv_nonneg.2 (absk_nonneg x.2)
    split_ifs <;> positivity
  · have h := SB.pairing hα1.sq hγ.grad.sq (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    have e : (A₁ * U) ^ 2 = A₁ ^ 2 * U ^ 2 := by ring
    rw [e]
    simpa only [mul_pow] using h
  · have e : (Real.sqrt 17 * B₀) ^ 2 = B₀ ^ 2 * 17 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      ring
    rw [e]
    have ht := SB.prod_mul (a := fun j => β j ^ 2) (K := fun j p =>
      (absk (j + p))⁻¹ ^ 2 * (absk p)⁻¹ ^ 2 * if p 2 = 0 then 1 else 0) hβ.sq
      (fun _ => sq_nonneg _) (fun i k => plane_nonneg i k) sb_plane (by norm_num)
    refine SB.equiv' edgeE ht fun x => ?_
    have e1 : x.1 - x.2 + x.2 = x.1 := by abel
    simp only [edgeE, Equiv.coe_fn_mk, e1]
    by_cases h : x.2 2 = 0
    · simp only [h, ↓reduceIte]
      ring
    · simp only [h, ↓reduceIte]
      ring

/-- The second sector: `J > 2K`. -/
lemma sb_edgeB {b g : Mode → ℝ} (hα : L2B α A₀) (hb : L2B b B₁) (hg : L2B g U) :
    SB (fun x : Mode × Mode => (α x.1 * b (x.1 - x.2)) *
      (g x.2 * if x.1 = 0 then 0 else (absk x.1)⁻¹ ^ 2)) (A₀ * B₁ * (U * c4)) := by
  have hA := hα.bd_nonneg
  have hU := hg.bd_nonneg
  have hB := hb.bd_nonneg
  have hc := c4_pos
  refine SB.cs (fun x => mul_nonneg (hα.nn _) (hb.nn _)) (fun x => mul_nonneg (hg.nn _) ?_)
    (by positivity) (by positivity) ?_ ?_
  · have := inv_nonneg.2 (absk_nonneg x.1)
    split_ifs <;> positivity
  · have hs : ∀ k, SB (fun p => b (k - p) ^ 2) (B₁ ^ 2) := fun k =>
      SB.equiv' (Equiv.subLeft k) hb.sq fun p => rfl
    have h := SB.prod_mul hα.sq (fun _ => sq_nonneg _) (fun i k => sq_nonneg _) hs (sq_nonneg _)
    have e : (A₀ * B₁) ^ 2 = A₀ ^ 2 * B₁ ^ 2 := by ring
    rw [e]
    simpa only [mul_pow] using h
  · have h := SB.pairing sb_inv4 hg.sq (fun k => by split_ifs <;> positivity)
      (fun _ => sq_nonneg _)
    have e : (U * c4) ^ 2 = c4 ^ 2 * U ^ 2 := by ring
    rw [e]
    refine h.of_le (fun x => sq_nonneg _) fun x => le_of_eq ?_
    split_ifs
    · simp
    · rw [mul_pow, ← pow_mul]
      ring

/-- The third sector: `K > 2J`. -/
lemma sb_edgeC {a g : Mode → ℝ} (hα1 : L2B a A₁) (hβ : L2B β B₀) (hg : L2B g U) :
    SB (fun x : Mode × Mode => (β (x.1 - x.2) * a x.1) *
      (g x.2 * if x.1 - x.2 = 0 then 0 else (absk (x.1 - x.2))⁻¹ ^ 2))
      (B₀ * A₁ * (U * c4)) := by
  have hA := hα1.bd_nonneg
  have hU := hg.bd_nonneg
  have hB := hβ.bd_nonneg
  have hc := c4_pos
  refine SB.cs (fun x => mul_nonneg (hβ.nn _) (hα1.nn _)) (fun x => mul_nonneg (hg.nn _) ?_)
    (by positivity) (by positivity) ?_ ?_
  · have := inv_nonneg.2 (absk_nonneg (x.1 - x.2))
    split_ifs <;> positivity
  · have hs : ∀ j, SB (fun p => a (j + p) ^ 2) (A₁ ^ 2) := fun j =>
      SB.equiv' (Equiv.addLeft j) hα1.sq fun p => rfl
    have h := SB.prod_mul hβ.sq (fun _ => sq_nonneg _) (fun i k => sq_nonneg _) hs (sq_nonneg _)
    have e : (B₀ * A₁) ^ 2 = B₀ ^ 2 * A₁ ^ 2 := by ring
    rw [e]
    refine SB.equiv' edgeE h fun x => ?_
    have e1 : x.1 - x.2 + x.2 = x.1 := by abel
    simp only [edgeE, Equiv.coe_fn_mk, e1, mul_pow]
  · have h := SB.pairing sb_inv4 hg.sq (fun k => by split_ifs <;> positivity)
      (fun _ => sq_nonneg _)
    have e : (U * c4) ^ 2 = c4 ^ 2 * U ^ 2 := by ring
    rw [e]
    refine SB.equiv' edgeE h fun x => ?_
    simp only [edgeE, Equiv.coe_fn_mk]
    by_cases h' : x.1 - x.2 = 0
    · simp only [h', ↓reduceIte]
      ring
    · simp only [h', ↓reduceIte]
      rw [mul_pow (g x.2), ← pow_mul]
      ring

/-- The constant of the mixed form. -/
def Ce : ℝ := 8 * Real.sqrt 17 + 3 * c4

lemma Ce_pos : 0 < Ce := by
  have := c4_pos
  have : 0 < Real.sqrt 17 := Real.sqrt_pos.2 (by norm_num)
  unfold Ce
  positivity

/-- The pointwise comparison of the three sectors. -/
lemma sector_le {a b c x y z : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (h1 : b ≤ a + c)
    (h2 : a ≤ b + c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * y * z * (a ^ 2 / b ^ 2 + b ^ 2 / a ^ 2) ≤
      8 * ((a * x * (c * y)) * (z * (a⁻¹ * c⁻¹))) + 3 * ((x * (b * z)) * (c * y * a⁻¹ ^ 2)) +
        3 * ((z * (a * x)) * (c * y * b⁻¹ ^ 2)) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hT : 0 ≤ x * y * z := by positivity
  have e1 : (a * x * (c * y)) * (z * (a⁻¹ * c⁻¹)) = x * y * z := by
    field_simp
  have e2 : (x * (b * z)) * (c * y * a⁻¹ ^ 2) = x * y * z * (b * c / a ^ 2) := by
    field_simp
  have e3 : (z * (a * x)) * (c * y * b⁻¹ ^ 2) = x * y * z * (a * c / b ^ 2) := by
    field_simp
  rw [e1, e2, e3]
  have hp2 : 0 ≤ x * y * z * (b * c / a ^ 2) := by positivity
  have hp3 : 0 ≤ x * y * z * (a * c / b ^ 2) := by positivity
  by_cases hA : b ≤ 2 * a
  · by_cases hB : a ≤ 2 * b
    · have k1 : a ^ 2 / b ^ 2 ≤ 4 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [hB, ha0, hb0]
      have k2 : b ^ 2 / a ^ 2 ≤ 4 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [hA, ha0, hb0]
      have := mul_le_mul_of_nonneg_left (add_le_add k1 k2) hT
      nlinarith only [this, hp2, hp3, hT]
    · rw [not_le] at hB
      have hc2 : a ≤ 2 * c := by linarith
      have k1 : a ^ 2 / b ^ 2 ≤ a * c / b ^ 2 * 2 := by
        rw [div_mul_eq_mul_div]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith only [hc2, ha0]
      have k2 : b ^ 2 / a ^ 2 ≤ a * c / b ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 : b ^ 4 ≤ a ^ 3 * c := by
          have h4 : b ≤ a := by linarith
          have h5 : b ≤ c := by linarith
          have h6 : b ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hb0.le h4 3
          calc b ^ 4 = b ^ 3 * b := by ring
            _ ≤ a ^ 3 * c := mul_le_mul h6 h5 hb0.le (by positivity)
        nlinarith only [h3]
      have := mul_le_mul_of_nonneg_left (add_le_add k1 k2) hT
      nlinarith only [this, hp2, hp3, hT]
  · rw [not_le] at hA
    have hc2 : b ≤ 2 * c := by linarith
    have k1 : b ^ 2 / a ^ 2 ≤ b * c / a ^ 2 * 2 := by
      rw [div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      nlinarith only [hc2, hb0]
    have k2 : a ^ 2 / b ^ 2 ≤ b * c / a ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : a ^ 4 ≤ b ^ 3 * c := by
        have h4 : a ≤ b := by linarith
        have h5 : a ≤ c := by linarith
        have h6 : a ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ ha0.le h4 3
        calc a ^ 4 = a ^ 3 * a := by ring
          _ ≤ b ^ 3 * c := mul_le_mul h6 h5 ha0.le (by positivity)
      nlinarith only [h3]
    have := mul_le_mul_of_nonneg_left (add_le_add k1 k2) hT
    nlinarith only [this, hp2, hp3, hT]

/-- **The mixed edge**: the positive form of `X₁` with an `H¹` leaf. -/
theorem edge_mixed (hα : L2B α A₀) (hα1 : L2B (fun k => absk k * α k) A₁) (hβ : L2B β B₀)
    (hβ1 : L2B (fun k => absk k * β k) B₁) (hγ : SlowH1 γ U) (hα0 : ∀ k, k 2 = 0 → α k = 0)
    (hβ0 : ∀ k, k 2 = 0 → β k = 0) :
    SB (fun x : Mode × Mode => α x.1 * γ x.2 * β (x.1 - x.2) *
      (absSq x.1 / absSq (x.1 - x.2) + absSq (x.1 - x.2) / absSq x.1))
      (Ce * U * (A₁ * B₀ + A₀ * B₁)) := by
  have hA := sb_edgeA hα1 hβ hγ
  have hB := sb_edgeB hα hβ1 hγ.grad
  have hC := sb_edgeC hα1 hβ hγ.grad
  have hs := ((hA.const_mul (by norm_num : (0 : ℝ) ≤ 8)).add
    (hB.const_mul (by norm_num : (0 : ℝ) ≤ 3))).add (hC.const_mul (by norm_num : (0 : ℝ) ≤ 3))
  have hA0 := hα1.bd_nonneg
  have hA00 := hα.bd_nonneg
  have hB0 := hβ.bd_nonneg
  have hB1 := hβ1.bd_nonneg
  have hU := hγ.grad.bd_nonneg
  have hc := c4_pos
  have ht : 8 * (A₁ * U * (Real.sqrt 17 * B₀)) + 3 * (A₀ * B₁ * (U * c4)) +
      3 * (B₀ * A₁ * (U * c4)) ≤ Ce * U * (A₁ * B₀ + A₀ * B₁) := by
    have h17 : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
    have : 0 ≤ A₀ * B₁ * (U * Real.sqrt 17) := by positivity
    simp only [Ce]
    nlinarith only [this]
  refine (hs.mono_bd ht).of_le (fun x => ?_) fun x => ?_
  · have h1 := hα.nn x.1
    have h2 := hγ.nn x.2
    have h3 := hβ.nn (x.1 - x.2)
    have h4 := absSq_nonneg x.1
    have h5 := absSq_nonneg (x.1 - x.2)
    positivity
  · obtain ⟨k, p⟩ := x
    simp only
    by_cases hk : k 2 = 0
    · simp [hα0 k hk]
    by_cases hj : (k - p) 2 = 0
    · simp [hβ0 _ hj]
    by_cases hp : p 2 = 0
    swap
    · simp [hγ.slow p hp]
    by_cases hp0 : p = 0
    · subst hp0
      simp [hγ.mean]
    have hk0 : k ≠ 0 := fun h => hk (by rw [h]; rfl)
    have hj0 : k - p ≠ 0 := fun h => hj (by rw [h]; rfl)
    simp only [hk0, hj0, hp, ite_false, ite_true, mul_one]
    have := sector_le (a := absk k) (b := absk (k - p)) (c := absk p) (x := α k) (y := γ p)
      (z := β (k - p)) (one_le_absk hk0) (one_le_absk hj0) (one_le_absk hp0)
      (by simpa using absk_sub_le k p) (by
        have := absk_add_le (k - p) p
        rwa [sub_add_cancel] at this) (hα.nn _) (hγ.nn _) (hβ.nn _)
    rw [absk_sq, absk_sq] at this
    exact this

/-- The comparison of the sectors, in the phase-free form. -/
lemma sector_free {a b c x y z : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (h1 : b ≤ a + c)
    (h2 : a ≤ b + c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * y * z * (1 + a ^ 2 / b ^ 2 + b ^ 2 / a ^ 2) ≤
      9 * (x * (y * z)) + 8 * ((x * z) * (c ^ 2 * y * a⁻¹ ^ 2)) +
        8 * ((z * x) * (c ^ 2 * y * b⁻¹ ^ 2)) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hT : 0 ≤ x * y * z := by positivity
  have e2 : (x * z) * (c ^ 2 * y * a⁻¹ ^ 2) = x * y * z * (c ^ 2 / a ^ 2) := by
    field_simp
  have e3 : (z * x) * (c ^ 2 * y * b⁻¹ ^ 2) = x * y * z * (c ^ 2 / b ^ 2) := by
    field_simp
  rw [e2, e3]
  have hp2 : 0 ≤ x * y * z * (c ^ 2 / a ^ 2) := by positivity
  have hp3 : 0 ≤ x * y * z * (c ^ 2 / b ^ 2) := by positivity
  have hcalc : x * y * z * (1 + a ^ 2 / b ^ 2 + b ^ 2 / a ^ 2) ≤ x * y * z *
      (9 + 8 * (c ^ 2 / a ^ 2) + 8 * (c ^ 2 / b ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hT
    have hq2 : 0 ≤ c ^ 2 / a ^ 2 := by positivity
    have hq3 : 0 ≤ c ^ 2 / b ^ 2 := by positivity
    have hr1 : 0 ≤ a ^ 2 / b ^ 2 := by positivity
    have hr2 : 0 ≤ b ^ 2 / a ^ 2 := by positivity
    by_cases hA : b ≤ 2 * a
    · by_cases hB : a ≤ 2 * b
      · have k1 : a ^ 2 / b ^ 2 ≤ 4 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith only [hB, ha0, hb0]
        have k2 : b ^ 2 / a ^ 2 ≤ 4 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith only [hA, ha0, hb0]
        linarith
      · rw [not_le] at hB
        have hc2 : a ≤ 2 * c := by linarith
        have k1 : a ^ 2 / b ^ 2 ≤ 4 * (c ^ 2 / b ^ 2) := by
          rw [← mul_div_assoc]
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          nlinarith only [hc2, ha0]
        have k2 : b ^ 2 / a ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith only [hB, ha0, hb0]
        linarith
    · rw [not_le] at hA
      have hc2 : b ≤ 2 * c := by linarith
      have k1 : b ^ 2 / a ^ 2 ≤ 4 * (c ^ 2 / a ^ 2) := by
        rw [← mul_div_assoc]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith only [hc2, hb0]
      have k2 : a ^ 2 / b ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith only [hA, ha0, hb0]
      linarith
  refine hcalc.trans (le_of_eq ?_)
  have e0 : x * (y * z) = x * y * z := by ring
  rw [e0]
  ring

/-- **The phase-free edge.** -/
theorem edge_free (hα : L2B α A₀) (hβ : L2B β B₀) (hγ1 : L1B γ U) (hγ2 : L2B (up γ) B₁)
    (hγm : γ 0 = 0) (hα0 : ∀ k, k 2 = 0 → α k = 0) (hβ0 : ∀ k, k 2 = 0 → β k = 0) :
    SB (fun x : Mode × Mode => α x.1 * γ x.2 * β (x.1 - x.2) *
      (1 + absSq x.1 / absSq (x.1 - x.2) + absSq (x.1 - x.2) / absSq x.1))
      ((9 * U + 16 * c4 * B₁) * (A₀ * B₀)) := by
  obtain ⟨c1, d1⟩ := hγ1.conv_l2 hβ
  have hA : SB (fun x : Mode × Mode => α x.1 * (γ x.2 * β (x.1 - x.2))) (A₀ * (U * B₀)) := by
    have hc : SB (fun k => α k * convR γ β k) (A₀ * (U * B₀)) := hα.pair d1
    have hin : ∀ k, SB (fun p => α k * (γ p * β (k - p))) (α k * convR γ β k) := fun k => by
      refine ⟨(c1 k).mul_left _, ?_⟩
      rw [tsum_mul_left]
      exact le_rfl
    exact SB.prod (H := fun x : Mode × Mode => α x.1 * (γ x.2 * β (x.1 - x.2)))
      (fun x => mul_nonneg (hα.nn _) (mul_nonneg (hγ1.nn _) (hβ.nn _))) hin hc
  have hB := sb_edgeB hα hβ hγ2
  have hC := sb_edgeC hα hβ hγ2
  have hs := ((hA.const_mul (by norm_num : (0 : ℝ) ≤ 9)).add
    (hB.const_mul (by norm_num : (0 : ℝ) ≤ 8))).add (hC.const_mul (by norm_num : (0 : ℝ) ≤ 8))
  have ht : 9 * (A₀ * (U * B₀)) + 8 * (A₀ * B₀ * (B₁ * c4)) + 8 * (B₀ * A₀ * (B₁ * c4)) =
      (9 * U + 16 * c4 * B₁) * (A₀ * B₀) := by ring
  refine (hs.mono_bd ht.le).of_le (fun x => ?_) fun x => ?_
  · have h1 := hα.nn x.1
    have h2 := hγ1.nn x.2
    have h3 := hβ.nn (x.1 - x.2)
    have h4 := absSq_nonneg x.1
    have h5 := absSq_nonneg (x.1 - x.2)
    positivity
  · obtain ⟨k, p⟩ := x
    simp only
    by_cases hk : k 2 = 0
    · simp [hα0 k hk]
    by_cases hj : (k - p) 2 = 0
    · simp [hβ0 _ hj]
    by_cases hp0 : p = 0
    · subst hp0
      simp [hγm, up]
    have hk0 : k ≠ 0 := fun h => hk (by rw [h]; rfl)
    have hj0 : k - p ≠ 0 := fun h => hj (by rw [h]; rfl)
    simp only [hk0, hj0, ite_false]
    have := sector_free (a := absk k) (b := absk (k - p)) (c := absk p) (x := α k) (y := γ p)
      (z := β (k - p)) (one_le_absk hk0) (one_le_absk hj0) (one_le_absk hp0)
      (by simpa using absk_sub_le k p) (by
        have := absk_add_le (k - p) p
        rwa [sub_add_cancel] at this) (hα.nn _) (hγ1.nn _) (hβ.nn _)
    rw [absk_sq, absk_sq, absk_sq] at this
    simpa only [up] using this

end OVNS.Quant.Metric

end
