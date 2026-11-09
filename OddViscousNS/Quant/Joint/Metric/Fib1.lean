import OddViscousNS.Quant.Joint.Metric.DiffZ
import OddViscousNS.Quant.Joint.Quartic.FibreBd

/-!
# Inverse-first-power exteriors through the fibre norm (step J5, node N10)

`z/J` is `F` at weight one, and N11's `lhB_log` has `L_h(F) ≤ √(9 + 8 ln D) a_F + (5/D) b_F`, so the
horizontal `ℓ¹` of an inverse-first-power exterior, (3.5) of the unit, is `LhB`.  This replaces both
the subcritical rule (3.4) and the fractional dissipation of (3.5) at weight one: only logarithms
and a term `b_F/D` remain, and `D` is free.

* `sb_fib`: `∑ α_l β_j u_a v_b ≤ ‖α‖ L_h(β) ‖u‖₂ ‖v‖₁`;
* `sb_fib₂`: `∑ β₁_l β₂_j u_a v_b ≤ L_h(β₁) L_h(β₂) ‖u‖₂ ‖v‖₂`;
* `pos3_band2`: two band exteriors and three leaves.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic

variable {α β β₁ β₂ u v : Mode → ℝ} {A B U V L L₁ L₂ : ℝ}

/-- The translate of an `ℓ²` sequence. -/
lemma L2B.shift (h : L2B α A) (c : Mode) : L2B (fun k => α (k - c)) A := by
  have e : ∀ s : Mode → ℝ, ∑' k, s (k - c) = ∑' k, s k := fun s => (Equiv.subRight c).tsum_eq s
  refine ⟨fun k => h.nn _, (Equiv.subRight c).summable_iff.2 h.s, ?_⟩
  rw [e fun k => α k ^ 2]
  exact h.le

/-- **The fibre rule, one fibre.** -/
theorem sb_fib (hα : L2B α A) (hβ : LhB β L) (hu : L2B u U) (hus : ∀ p, p 2 ≠ 0 → u p = 0)
    (hv : L1B v V) : SB (Phi₂ α β u v) (A * L * U * V) := by
  obtain ⟨hc, hγ⟩ := LhB.conv hu hus hβ
  have hA := hα.bd_nonneg
  have hU := hu.bd_nonneg
  have hL := hβ.bd_nonneg
  have hin : ∀ b : Mode, SB (fun y : Mode × Mode => v b * (α y.1 * (u y.2 * β (y.1 - y.2 - b))))
      (v b * (A * (U * L))) := fun b => by
    refine SB.const_mul ?_ (hv.nn b)
    have hp := (hα.pair (hγ.shift b))
    refine SB.prod (c := fun l => α l * cvS u β (l - b))
      (fun y => mul_nonneg (hα.nn _) (mul_nonneg (hu.nn _) (hβ.nn _))) (fun l => ?_) ⟨hp.1, hp.2⟩
    refine SB.const_mul ?_ (hα.nn l)
    have e : ∀ a, u a * β (l - a - b) = u a * β (l - b - a) := fun a => by
      rw [show l - a - b = l - b - a by abel]
    simp only [e]
    exact ⟨hc (l - b), le_rfl⟩
  have hp0 : 0 ≤ A * (U * L) := by positivity
  have hsum : SB (fun b => v b * (A * (U * L))) (A * L * U * V) := by
    refine ⟨hv.s.mul_right _, ?_⟩
    rw [tsum_mul_right]
    calc _ ≤ V * (A * (U * L)) := mul_le_mul_of_nonneg_right hv.le hp0
      _ = _ := by ring
  have hprod := SB.prod (H := fun y : Mode × (Mode × Mode) => v y.1 * (α y.2.1 * (u y.2.2 *
      β (y.2.1 - y.2.2 - y.1))))
    (fun y => mul_nonneg (hv.nn _) (mul_nonneg (hα.nn _) (mul_nonneg (hu.nn _) (hβ.nn _))))
    hin hsum
  set e : I3 ≃ Mode × (Mode × Mode) :=
    { toFun := fun x => (x.2.2, x.1, x.2.1)
      invFun := fun y => (y.2.1, y.2.2, y.1)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl } with he
  refine SB.equiv' e hprod fun x => ?_
  simp only [Phi₂, he, Equiv.coe_fn_mk, inJ₂]
  ring

/-- The relabelling around the intermediate. -/
def midE : I3 ≃ Mode × (Mode × Mode) where
  toFun x := (x.1 - x.2.1, x.2.1, x.2.2)
  invFun y := (y.1 + y.2.1, y.2.1, y.2.2)
  left_inv := fun ⟨l, a, b⟩ => Prod.ext (show l - a + a = l by abel) rfl
  right_inv := fun ⟨m, a, b⟩ => Prod.ext (show m + a - a = m by abel) rfl

lemma midE_phi (x : I3) (u v b₁ b₂ : Mode → ℝ) : Phi₂ b₁ b₂ u v x =
    (u (midE x).2.1 * b₁ ((midE x).1 + (midE x).2.1)) *
      (v (midE x).2.2 * b₂ ((midE x).1 - (midE x).2.2)) := by
  have e1 : (midE x).1 = x.1 - x.2.1 := rfl
  have e2 : (midE x).2.1 = x.2.1 := rfl
  have e3 : (midE x).2.2 = x.2.2 := rfl
  rw [e1, e2, e3, sub_add_cancel]
  simp only [Phi₂, inJ₂]
  ring

/-- **The fibre rule, two fibres.** -/
theorem sb_fib₂ (hβ₁ : LhB β₁ L₁) (hβ₂ : LhB β₂ L₂) (hu : L2B u U) (hus : ∀ p, p 2 ≠ 0 → u p = 0)
    (hv : L2B v V) (hvs : ∀ p, p 2 ≠ 0 → v p = 0) :
    SB (Phi₂ β₁ β₂ u v) ((U * L₁) * (V * L₂)) := by
  have hus' : ∀ p : Mode, p 2 ≠ 0 → Metric.refl u p = 0 := fun p hp => hus _ (by simpa using hp)
  obtain ⟨hc1, hγ1⟩ := LhB.conv hu.refl hus' hβ₁
  obtain ⟨hc2, hγ2⟩ := LhB.conv hv hvs hβ₂
  have hp := hγ1.pair hγ2
  have h1 : ∀ m : Mode, SB (fun a : Mode => u a * β₁ (m + a)) (cvS (Metric.refl u) β₁ m) := fun m => by
    have hs : SB (fun s : Mode => Metric.refl u s * β₁ (m - s)) (cvS (Metric.refl u) β₁ m) :=
      ⟨hc1 m, le_rfl⟩
    refine SB.equiv' (Equiv.neg Mode) hs fun a => ?_
    simp only [Equiv.neg_apply, Metric.refl, neg_neg, sub_neg_eq_add]
  have h2 : ∀ m : Mode, SB (fun b : Mode => v b * β₂ (m - b)) (cvS v β₂ m) := fun m =>
    ⟨hc2 m, le_rfl⟩
  have hin : ∀ m : Mode, SB (fun y : Mode × Mode => (u y.1 * β₁ (m + y.1)) * (v y.2 * β₂ (m - y.2)))
      (cvS (Metric.refl u) β₁ m * cvS v β₂ m) := fun m => by
    have h3 := SB.mul_prod (h1 m) (h2 m) (fun a => mul_nonneg (hu.nn _) (hβ₁.nn _))
      (fun b => mul_nonneg (hv.nn _) (hβ₂.nn _))
    exact h3
  have hs : SB (fun m => cvS (Metric.refl u) β₁ m * cvS v β₂ m) ((U * L₁) * (V * L₂)) :=
    ⟨hp.1, hp.2⟩
  have hprod : SB (fun y : Mode × (Mode × Mode) => (u y.2.1 * β₁ (y.1 + y.2.1)) *
      (v y.2.2 * β₂ (y.1 - y.2.2))) ((U * L₁) * (V * L₂)) :=
    SB.prod (c := fun m => cvS (Metric.refl u) β₁ m * cvS v β₂ m)
      (fun y => mul_nonneg (mul_nonneg (hu.nn _) (hβ₁.nn _)) (mul_nonneg (hv.nn _) (hβ₂.nn _)))
      hin hs
  exact SB.equiv' midE hprod fun x => midE_phi x u v β₁ β₂

/-- **Two band exteriors and three leaves.** -/
theorem pos3_band2 {w : Mode → ℝ} {D W : ℝ} (hD : 1 ≤ D) (hα : L2B α A) (hβ : L2B β B)
    (hu : L2B u U) (hv : L2B v V) (hw : L1B w W) (hus : ∀ p, p 2 ≠ 0 → u p = 0)
    (hvs : ∀ p, p 2 ≠ 0 → v p = 0) :
    SB (fun x : I4 => α x.1 * bandW D x.1 * (β (inJ x) * bandW D (inJ x)) *
      (u x.2.1 * v x.2.2.1 * w x.2.2.2))
      (A * U * Real.sqrt (9 + 8 * Real.log D) * (B * V * Real.sqrt (9 + 8 * Real.log D)) * W) := by
  have hlog : 0 ≤ 9 + 8 * Real.log D := by
    have := Real.log_nonneg hD
    linarith
  have hA := hα.bd_nonneg
  have hB := hβ.bd_nonneg
  have hU := hu.bd_nonneg
  have hV := hv.bd_nonneg
  have hF := fib_band hD
  set Z := Real.sqrt (9 + 8 * Real.log D) with hZ
  have hin : ∀ c : Mode, SB (fun y : I3 => w c * ((α y.1 * u y.2.1 *
      (if y.2.2 2 = 0 then bandW D (inJ₂ y - c) else 0)) * (β (inJ₂ y - c) * v y.2.2 *
      (if y.2.1 2 = 0 then bandW D y.1 else 0))))
      (w c * ((A * U * Z) * (B * V * Z))) := fun c => by
    have hβc := hβ.shift c
    set κ₁ : I3 → ℝ := fun y => if y.2.2 2 = 0 then bandW D (inJ₂ y - c) else 0 with hκ₁
    set κ₂ : I3 → ℝ := fun y => if y.2.1 2 = 0 then bandW D y.1 else 0 with hκ₂
    have h10 : ∀ y, 0 ≤ κ₁ y := fun y => by
      have := bandW_nonneg D (inJ₂ y - c)
      simp only [hκ₁]
      split_ifs <;> positivity
    have h20 : ∀ y, 0 ≤ κ₂ y := fun y => by
      have := bandW_nonneg D y.1
      simp only [hκ₂]
      split_ifs <;> positivity
    have c1 : ∀ l a, SB (fun b => κ₁ (l, a, b) ^ 2) (9 + 8 * Real.log D) := fun l a => by
      refine (hF (l - a - c)).of_le (fun b => sq_nonneg _) fun b => le_of_eq ?_
      have e : l - a - b - c = l - a - c - b := by abel
      by_cases hb : b 2 = 0
      · simp only [hκ₁, inJ₂, hb, ↓reduceIte, e]
      · simp only [hκ₁, hb, ↓reduceIte]
        ring
    have c2 : ∀ j b, SB (fun a => κ₂ (j + b + a, a, b) ^ 2) (9 + 8 * Real.log D) := fun j b => by
      refine (hF.add (j + b)).of_le (fun a => sq_nonneg _) fun a => le_of_eq ?_
      by_cases ha : a 2 = 0
      · simp only [hκ₂, ha, ↓reduceIte]
      · simp only [hκ₂, ha, ↓reduceIte]
        ring
    have hc := cs_mid h10 h20 c1 c2 hlog hlog hα hβc hu hv
    exact hc.const_mul (hw.nn c)
  have hZ0 : 0 ≤ Z := Real.sqrt_nonneg _
  have hp : 0 ≤ (A * U * Z) * (B * V * Z) := by positivity
  have hsum : SB (fun c => w c * ((A * U * Z) * (B * V * Z))) (A * U * Z * (B * V * Z) * W) := by
    refine ⟨hw.s.mul_right _, ?_⟩
    rw [tsum_mul_right, mul_comm]
    exact mul_le_mul_of_nonneg_left hw.le hp
  have hprod := SB.prod (H := fun y : Mode × I3 => w y.1 * ((α y.2.1 * u y.2.2.1 *
      (if y.2.2.2 2 = 0 then bandW D (inJ₂ y.2 - y.1) else 0)) *
      (β (inJ₂ y.2 - y.1) * v y.2.2.2 *
      (if y.2.2.1 2 = 0 then bandW D y.2.1 else 0))))
    (fun y => by
      have h1 := hw.nn y.1
      have h2 := hα.nn y.2.1
      have h3 := hu.nn y.2.2.1
      have h4 := hβ.nn (inJ₂ y.2 - y.1)
      have h5 := hv.nn y.2.2.2
      have h6 := bandW_nonneg D (inJ₂ y.2 - y.1)
      have h7 := bandW_nonneg D y.2.1
      split_ifs <;> positivity) hin hsum
  refine SB.equiv' leafE.symm hprod fun x => ?_
  have e : inJ₂ (leafE.symm x).2 - (leafE.symm x).1 = inJ x := rfl
  simp only [e]
  have e1 : (leafE.symm x).2.1 = x.1 := rfl
  have e2 : (leafE.symm x).2.2.1 = x.2.1 := rfl
  have e3 : (leafE.symm x).2.2.2 = x.2.2.1 := rfl
  have e4 : (leafE.symm x).1 = x.2.2.2 := rfl
  simp only [e1, e2, e3, e4]
  by_cases ha : x.2.1 2 = 0
  · by_cases hb : x.2.2.1 2 = 0
    · simp only [ha, hb, ↓reduceIte]
      ring
    · simp [hvs _ hb]
  · simp [hus _ ha]

end OVNS.Quant.Metric

end
