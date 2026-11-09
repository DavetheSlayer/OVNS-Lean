import OddViscousNS.Quant.Joint.Metric.Fibre

/-!
# The fibered positive layer: the forms (step J5, node N1)

The two groupings of `Fibre.lean` and the rules of the sources they replace.
* `cs_out`, `cs_mid`: weighted Cauchy–Schwarz, output against the rest, and around the intermediate.
* `pos2_base`, `pos2_base'`: `ℓ^{6/5} ⋆ ℓ^{6/5} ⋆ ℓ^{6/5} ⊂ ℓ²` of Bodies 33, 36, 39 and LOCAL457,
  with the kernel `kernel_base`.
* `pos2_band`, `pos2_band'`: the two `H¹` leaves in `ℓ²` and the band `|j| ≤ D`.
-/

open Finset

noncomputable section

namespace OVNS.Quant.Metric

variable {α β u v f₁ f₂ : Mode → ℝ} {A B U V U₁ U₂ Z Z₁ Z₂ : ℝ}

/-! ### D. The two groupings -/

/-- The index shift `(l, a, b) ↦ (j, a, b)`. -/
def shE : I3 ≃ I3 where
  toFun x := (inJ₂ x, x.2.1, x.2.2)
  invFun y := (y.1 + y.2.1 + y.2.2, y.2.1, y.2.2)
  left_inv := fun ⟨l, a, b⟩ => Prod.ext (show l - a - b + a + b = l by abel) rfl
  right_inv := fun ⟨j, a, b⟩ => Prod.ext (show j + a + b - a - b = j by abel) rfl

/-- The index shift `(l, a, b) ↦ (j, b, a)`. -/
def miE : I3 ≃ I3 where
  toFun x := (inJ₂ x, x.2.2, x.2.1)
  invFun y := (y.1 + y.2.2 + y.2.1, y.2.2, y.2.1)
  left_inv := fun ⟨l, a, b⟩ => Prod.ext (show l - a - b + a + b = l by abel) rfl
  right_inv := fun ⟨j, b, a⟩ => Prod.ext (show j + a + b - a - b = j by abel) rfl

/-- **Output against the rest**: `∑ α_l p(l,a,b) u_a v_b β_j ≤ √Z ‖α‖ ‖u‖ ‖v‖ ‖β‖`, as soon as
`∑_{a,b} p(l,a,b)² ≤ Z` for every `l`. -/
theorem cs_out {p : I3 → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp : ∀ l, SB (fun y : Mode × Mode => p (l, y) ^ 2) Z) (hZ : 0 ≤ Z) (hα : L2B α A)
    (hβ : L2B β B) (hu : L2B u U) (hv : L2B v V) :
    SB (fun x : I3 => α x.1 * p x * (u x.2.1 * v x.2.2 * β (inJ₂ x)))
      (A * Real.sqrt Z * (U * V * B)) := by
  have hA := hα.bd_nonneg
  have hB := hβ.bd_nonneg
  have hU := hu.bd_nonneg
  have hV := hv.bd_nonneg
  refine SB.cs (fun x => mul_nonneg (hα.nn _) (hp0 _))
    (fun x => mul_nonneg (mul_nonneg (hu.nn _) (hv.nn _)) (hβ.nn _)) (by positivity) (by positivity)
    ?_ ?_
  · have hs : SB (fun l => α l ^ 2 * Z) (A ^ 2 * Z) := by
      refine ⟨hα.sq.1.mul_right Z, ?_⟩
      rw [tsum_mul_right]
      exact mul_le_mul_of_nonneg_right hα.sq.2 hZ
    have e : (A * Real.sqrt Z) ^ 2 = A ^ 2 * Z := by rw [mul_pow, Real.sq_sqrt hZ]
    rw [e]
    refine SB.prod (c := fun l => α l ^ 2 * Z) (fun x => sq_nonneg _) (fun l => ?_) hs
    simp only [mul_pow]
    exact (hp l).const_mul (sq_nonneg _)
  · have ht := SB.tri (Z := V ^ 2) hβ.sq hu.sq (fun k => sq_nonneg _) (fun k => sq_nonneg _)
      (K := fun x => v x.2.2 ^ 2) (fun x => sq_nonneg _) fun _ _ => hv.sq
    have e : (U * V * B) ^ 2 = B ^ 2 * U ^ 2 * V ^ 2 := by ring
    rw [e]
    refine SB.equiv' shE ht fun x => ?_
    simp only [shE, Equiv.coe_fn_mk]
    ring

/-- **Around the intermediate label**: `(α_l, u_a)` against `(β_j, v_b)`:
`∑ α_l u_a κ₁(x) β_j v_b κ₂(x) ≤ √Z₁ √Z₂ ‖α‖ ‖u‖ ‖β‖ ‖v‖`, with `∑_b κ₁² ≤ Z₁` at fixed `(l, a)`
and `∑_a κ₂² ≤ Z₂` at fixed `(j, b)`. -/
theorem cs_mid {κ₁ κ₂ : I3 → ℝ} (h10 : ∀ x, 0 ≤ κ₁ x) (h20 : ∀ x, 0 ≤ κ₂ x)
    (h1 : ∀ l a, SB (fun b => κ₁ (l, a, b) ^ 2) Z₁)
    (h2 : ∀ j b, SB (fun a => κ₂ (j + b + a, a, b) ^ 2) Z₂) (hZ₁ : 0 ≤ Z₁) (hZ₂ : 0 ≤ Z₂)
    (hα : L2B α A) (hβ : L2B β B) (hu : L2B u U) (hv : L2B v V) :
    SB (fun x : I3 => (α x.1 * u x.2.1 * κ₁ x) * (β (inJ₂ x) * v x.2.2 * κ₂ x))
      ((A * U * Real.sqrt Z₁) * (B * V * Real.sqrt Z₂)) := by
  have hA := hα.bd_nonneg
  have hB := hβ.bd_nonneg
  have hU := hu.bd_nonneg
  have hV := hv.bd_nonneg
  refine SB.cs (fun x => mul_nonneg (mul_nonneg (hα.nn _) (hu.nn _)) (h10 _))
    (fun x => mul_nonneg (mul_nonneg (hβ.nn _) (hv.nn _)) (h20 _)) (by positivity) (by positivity)
    ?_ ?_
  · have ht := SB.tri hα.sq hu.sq (fun k => sq_nonneg _) (fun k => sq_nonneg _)
      (K := fun x => κ₁ x ^ 2) (fun x => sq_nonneg _) h1
    have e : (A * U * Real.sqrt Z₁) ^ 2 = A ^ 2 * U ^ 2 * Z₁ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hZ₁]
    rw [e]
    refine ht.of_le (fun x => sq_nonneg _) fun x => le_of_eq ?_
    ring
  · have ht := SB.tri hβ.sq hv.sq (fun k => sq_nonneg _) (fun k => sq_nonneg _)
      (K := fun y => κ₂ (y.1 + y.2.1 + y.2.2, y.2.2, y.2.1) ^ 2) (fun x => sq_nonneg _) h2
    have e : (B * V * Real.sqrt Z₂) ^ 2 = B ^ 2 * V ^ 2 * Z₂ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hZ₂]
    rw [e]
    refine SB.equiv' miE ht fun x => ?_
    have e1 : inJ₂ x + x.2.2 + x.2.1 = x.1 := by
      simp only [inJ₂]
      abel
    simp only [miE, Equiv.coe_fn_mk, e1]
    ring

/-! ### E. Slow sequences -/

/-- A nonnegative slow mean-zero sequence of `H¹` norm at most `U`. -/
structure SlowH1 (f : Mode → ℝ) (U : ℝ) : Prop where
  nn : ∀ p, 0 ≤ f p
  slow : ∀ p, p 2 ≠ 0 → f p = 0
  mean : f 0 = 0
  grad : L2B (fun p => absk p * f p) U

/-- The reflection of a sequence. -/
def refl (f : Mode → ℝ) (p : Mode) : ℝ := f (-p)

lemma L2B.refl (h : L2B f₁ A) : L2B (Metric.refl f₁) A := by
  have e : ∀ s : Mode → ℝ, ∑' k, s (-k) = ∑' k, s k := fun s => (Equiv.neg Mode).tsum_eq s
  refine ⟨fun k => h.nn _, (Equiv.neg Mode).summable_iff.2 h.s, ?_⟩
  simp only [Metric.refl]
  rw [e fun k => f₁ k ^ 2]
  exact h.le

lemma SlowH1.refl (h : SlowH1 f₁ U) : SlowH1 (Metric.refl f₁) U := by
  refine ⟨fun p => h.nn _, fun p hp => h.slow _ ?_, ?_, ?_⟩
  · simpa using hp
  · simpa [Metric.refl] using h.mean
  · have := h.grad.refl
    refine L2B.mono (A := U) ?_ le_rfl
    convert this using 2 with p
    simp only [Metric.refl, absk_neg]

/-- The exchange of the two ends of a path: `(l, a, b) ↦ (j, −b, −a)`. -/
def revE : I3 ≃ I3 where
  toFun x := (inJ₂ x, -x.2.2, -x.2.1)
  invFun x := (inJ₂ x, -x.2.2, -x.2.1)
  left_inv := fun ⟨l, a, b⟩ => Prod.ext (show l - a - b - -b - -a = l by abel)
    (Prod.ext (neg_neg a) (neg_neg b))
  right_inv := fun ⟨l, a, b⟩ => Prod.ext (show l - a - b - -b - -a = l by abel)
    (Prod.ext (neg_neg a) (neg_neg b))

lemma Phi₂_rev (α β f₁ f₂ : Mode → ℝ) (x : I3) :
    Phi₂ α β f₁ f₂ x = Phi₂ β α (refl f₂) (refl f₁) (revE x) := by
  obtain ⟨l, a, b⟩ := x
  have e : l - a - b - -b - -a = l := by abel
  change α l * β (l - a - b) * (f₁ a * f₂ b) =
    β (l - a - b) * α (l - a - b - -b - -a) * (f₂ (- -b) * f₁ (- -a))
  rw [e, neg_neg, neg_neg]
  ring

/-- `α/|k|`, the inverse-first-power exterior. -/
def in1 (α : Mode → ℝ) (k : Mode) : ℝ := α k / absk k

/-- `α/|k|` on the ball of radius `D`. -/
def band (D : ℝ) (α : Mode → ℝ) (k : Mode) : ℝ := bandW D k * α k

/-- The slow part of a weight. -/
def sl (w : Mode → ℝ) (b : Mode) : ℝ := if b 2 = 0 then w b else 0

lemma sl_nonneg {w : Mode → ℝ} (h : ∀ k, 0 ≤ w k) (b : Mode) : 0 ≤ sl w b := by
  unfold sl
  split_ifs
  · exact h b
  · exact le_rfl

/-- The slow sum of an even weight of bounded fibres. -/
lemma Fib.slow {w : Mode → ℝ} (h : Fib w Z) (hw : ∀ k, w (-k) = w k) : SB (sl w) Z := by
  have e : (fun b : Mode => if b 2 = 0 then w (0 - b) else 0) = sl w := by
    funext b
    simp only [zero_sub, hw, sl]
  exact e ▸ h 0

/-- `(xyz)² ≤ (xy)³ + (xz)³ + (yz)³`: **the largest length can be discarded**. -/
lemma three_cube_le {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x * y * z) ^ 2 ≤ x ^ 3 * y ^ 3 + x ^ 3 * z ^ 3 + y ^ 3 * z ^ 3 := by
  have key : ∀ {a b c : ℝ}, 0 ≤ a → 0 ≤ b → 0 ≤ c → c ≤ a → c ≤ b →
      (a * b * c) ^ 2 ≤ a ^ 3 * b ^ 3 := fun {a b c} ha hb hc hca hcb => by
    have h : c ^ 2 ≤ a * b := by nlinarith
    calc (a * b * c) ^ 2 = (a * b) ^ 2 * c ^ 2 := by ring
      _ ≤ (a * b) ^ 2 * (a * b) := by gcongr
      _ = a ^ 3 * b ^ 3 := by ring
  have h1 : 0 ≤ x ^ 3 * y ^ 3 := by positivity
  have h2 : 0 ≤ x ^ 3 * z ^ 3 := by positivity
  have h3 : 0 ≤ y ^ 3 * z ^ 3 := by positivity
  rcases le_total x y with hxy | hxy <;> rcases le_total x z with hxz | hxz <;>
    rcases le_total y z with hyz | hyz
  all_goals first
    | (have := key hy hz hx hxy hxz
       have e : (x * y * z) ^ 2 = (y * z * x) ^ 2 := by ring
       linarith)
    | (have := key hx hz hy hxy hyz
       have e : (x * y * z) ^ 2 = (x * z * y) ^ 2 := by ring
       linarith)
    | (have := key hx hy hz hxz hyz
       linarith)
    | (have := key hx hy hz (hyz.trans hxy) hyz
       linarith)
    | (have := key hx hy hz hxz (hxz.trans hxy)
       linarith)

/-- The inverse length, on the slow modes. -/
def sinv (a : Mode) : ℝ := sl (fun k => (absk k)⁻¹) a

lemma sinv_nonneg (a : Mode) : 0 ≤ sinv a := sl_nonneg (fun k => inv_nonneg.2 (absk_nonneg k)) a

lemma SlowH1.sinv_mul (h : SlowH1 f₁ U) (a : Mode) : sinv a * (absk a * f₁ a) = f₁ a := by
  by_cases h2 : a 2 = 0
  · by_cases h0 : a = 0
    · simp [h0, h.mean]
    · have h1 : absk a ≠ 0 := absk_eq_zero.not.2 h0
      simp only [sinv, sl, h2, ite_true]
      field_simp
  · simp [h.slow a h2]

/-- The kernel of `pos2_base`: `∑_{a,b} |a|⁻²|b|⁻²|j|⁻² ≤ 3 · 17²`, for every output. -/
lemma kernel_base (l : Mode) :
    SB (fun y : Mode × Mode => (sinv y.1 * sinv y.2 * (absk (l - y.1 - y.2))⁻¹) ^ 2) 867 := by
  have hS := fib_w3.slow w3_neg
  have hS0 := sl_nonneg w3_nonneg
  have hF : ∀ t b, 0 ≤ (if b 2 = 0 then w3 (t - b) else 0 : ℝ) := fun t b => by
    split_ifs
    · exact w3_nonneg _
    · exact le_rfl
  have t1 : SB (fun y : Mode × Mode => sl w3 y.1 * sl w3 y.2) (17 * 17) :=
    SB.prod_mul (K := fun _ => sl w3) hS hS0 (fun _ k => hS0 k) (fun _ => hS) (by norm_num)
  have t2 : ∀ l : Mode, SB (fun y : Mode × Mode =>
      sl w3 y.1 * (if y.2 2 = 0 then w3 (l - y.1 - y.2) else 0)) (17 * 17) := fun l =>
    SB.prod_mul (K := fun a b => if b 2 = 0 then w3 (l - a - b) else 0) hS hS0
      (fun i k => hF _ k) (fun i => fib_w3 (l - i)) (by norm_num)
  have t3 : SB (fun y : Mode × Mode =>
      sl w3 y.2 * (if y.1 2 = 0 then w3 (l - y.1 - y.2) else 0)) (17 * 17) :=
    SB.equiv' (Equiv.prodComm Mode Mode) (t2 l) fun y => by
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, sub_right_comm]
  have h := ((t1.add (t2 l)).add t3).mono_bd (show _ ≤ (867 : ℝ) by norm_num)
  refine h.of_le (fun y => sq_nonneg _) fun y => ?_
  obtain ⟨a, b⟩ := y
  have hx := inv_nonneg.2 (absk_nonneg a)
  have hy := inv_nonneg.2 (absk_nonneg b)
  have hz := inv_nonneg.2 (absk_nonneg (l - a - b))
  have hkey := three_cube_le hx hy hz
  have hw : ∀ k, (absk k)⁻¹ ^ 3 = w3 k := fun k => rfl
  rw [hw, hw, hw] at hkey
  simp only [sinv, sl]
  by_cases ha : a 2 = 0 <;> by_cases hb : b 2 = 0
  · simp only [ha, hb, ite_true]
    linarith
  · simp [hb]
  · simp [ha]
  · simp [ha]

/-- **The inverse-first-power base** (Body 36: `S ∈ ℓ^{6/5}` twice, `z/J ∈ ℓ^{6/5}`; LOCAL457): two
`H¹` leaves, one `ℓ²` exterior and one inverse first power cost `30 ‖α‖ ‖β‖ U₁ U₂`, with no
`ℓ¹` norm and no log.  Weighted Cauchy–Schwarz, `kernel_base`. -/
theorem pos2_base (hα : L2B α A) (hβ : L2B β B) (h1 : SlowH1 f₁ U₁) (h2 : SlowH1 f₂ U₂) :
    SB (Phi₂ α (in1 β) f₁ f₂) (30 * (A * B * (U₁ * U₂))) := by
  set p : I3 → ℝ := fun x => sinv x.2.1 * sinv x.2.2 * (absk (inJ₂ x))⁻¹ with hp
  have hp0 : ∀ x, 0 ≤ p x := fun x => mul_nonneg (mul_nonneg (sinv_nonneg _) (sinv_nonneg _))
    (inv_nonneg.2 (absk_nonneg _))
  have h := cs_out hp0 (fun l => kernel_base l) (by norm_num) hα hβ h1.grad h2.grad
  have hs : Real.sqrt 867 ≤ 30 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hA := hα.bd_nonneg
  have hB := hβ.bd_nonneg
  have hU1 := h1.grad.bd_nonneg
  have hU2 := h2.grad.bd_nonneg
  have e : Phi₂ α (in1 β) f₁ f₂ = fun x : I3 =>
      α x.1 * p x * (absk x.2.1 * f₁ x.2.1 * (absk x.2.2 * f₂ x.2.2) * β (inJ₂ x)) := by
    funext x
    have e1 := h1.sinv_mul x.2.1
    have e2 := h2.sinv_mul x.2.2
    simp only [Phi₂, in1, hp]
    rw [div_eq_mul_inv]
    calc _ = α x.1 * (β (inJ₂ x) * (absk (inJ₂ x))⁻¹) *
          ((sinv x.2.1 * (absk x.2.1 * f₁ x.2.1)) * (sinv x.2.2 * (absk x.2.2 * f₂ x.2.2))) := by
          rw [e1, e2]
      _ = _ := by ring
  rw [e]
  refine h.mono_bd ?_
  calc A * Real.sqrt 867 * (U₁ * U₂ * B) = Real.sqrt 867 * (A * B * (U₁ * U₂)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (by positivity)

/-- The transpose of `pos2_base`. -/
theorem pos2_base' (hα : L2B α A) (hβ : L2B β B) (h1 : SlowH1 f₁ U₁) (h2 : SlowH1 f₂ U₂) :
    SB (Phi₂ (in1 α) β f₁ f₂) (30 * (A * B * (U₁ * U₂))) := by
  refine SB.equiv' revE (pos2_base hβ hα h2.refl h1.refl) (fun x => ?_) |>.mono_bd (le_of_eq ?_)
  · exact Phi₂_rev _ _ _ _ x
  · ring

lemma in2_eq (α : Mode → ℝ) (k : Mode) : in2 α k = (absk k)⁻¹ ^ 2 * α k := by
  simp only [in2, ← absk_sq k, inv_pow, div_eq_mul_inv]
  ring

/-- **The band** (Body 36, high intermediate at `M ≤ D`; Bodies 33, 41): the two `H¹` leaves in
`ℓ²`, the inverse-square exterior uniformly, the inverse-first-power exterior with `√(1 + ln D)`. -/
theorem pos2_band {D : ℝ} (hD : 1 ≤ D) (hα : L2B α A) (hβ : L2B β B) (hu : L2B u U) (hv : L2B v V)
    (hus : ∀ p, p 2 ≠ 0 → u p = 0) (hvs : ∀ p, p 2 ≠ 0 → v p = 0) :
    SB (Phi₂ (in2 α) (band D β) u v) (5 * Real.sqrt (9 + 8 * Real.log D) * (A * B * (U * V))) := by
  have hlog : 0 ≤ 9 + 8 * Real.log D := by
    have := Real.log_nonneg hD
    linarith
  set κ₁ : I3 → ℝ := fun x => if x.2.2 2 = 0 then bandW D (inJ₂ x) else 0 with hκ₁
  set κ₂ : I3 → ℝ := fun x => if x.2.1 2 = 0 then (absk x.1)⁻¹ ^ 2 else 0 with hκ₂
  have h10 : ∀ x, 0 ≤ κ₁ x := fun x => by
    simp only [hκ₁]
    split_ifs
    · exact bandW_nonneg _ _
    · exact le_rfl
  have h20 : ∀ x, 0 ≤ κ₂ x := fun x => by
    simp only [hκ₂]
    split_ifs
    · positivity
    · exact le_rfl
  have h1 : ∀ l a, SB (fun b => κ₁ (l, a, b) ^ 2) (9 + 8 * Real.log D) := fun l a => by
    refine (fib_band hD (l - a)).of_le (fun b => sq_nonneg _) fun b => le_of_eq ?_
    simp only [hκ₁, inJ₂]
    split_ifs <;> simp
  have h2 : ∀ j b, SB (fun a => κ₂ (j + b + a, a, b) ^ 2) 17 := fun j b => by
    refine (fib_w4.add (j + b)).of_le (fun a => sq_nonneg _) fun a => le_of_eq ?_
    simp only [hκ₂, w4]
    split_ifs
    · ring
    · simp
  have h := cs_mid h10 h20 h1 h2 hlog (by norm_num) hα hβ hu hv
  have hA := hα.bd_nonneg
  have hB := hβ.bd_nonneg
  have hU := hu.bd_nonneg
  have hV := hv.bd_nonneg
  have hs : Real.sqrt 17 ≤ 5 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hl0 := Real.sqrt_nonneg (9 + 8 * Real.log D)
  have e : Phi₂ (in2 α) (band D β) u v = fun x : I3 =>
      (α x.1 * u x.2.1 * κ₁ x) * (β (inJ₂ x) * v x.2.2 * κ₂ x) := by
    funext x
    simp only [Phi₂, band, in2_eq, hκ₁, hκ₂]
    by_cases ha : x.2.1 2 = 0
    · by_cases hb : x.2.2 2 = 0
      · simp only [ha, hb, ite_true]
        ring
      · simp [hvs _ hb]
    · simp [hus _ ha]
  rw [e]
  refine h.mono_bd ?_
  calc A * U * Real.sqrt (9 + 8 * Real.log D) * (B * V * Real.sqrt 17)
      = Real.sqrt 17 * Real.sqrt (9 + 8 * Real.log D) * (A * B * (U * V)) := by ring
    _ ≤ _ := by gcongr

/-- The transpose of `pos2_band`. -/
theorem pos2_band' {D : ℝ} (hD : 1 ≤ D) (hα : L2B α A) (hβ : L2B β B) (hu : L2B u U)
    (hv : L2B v V) (hus : ∀ p, p 2 ≠ 0 → u p = 0) (hvs : ∀ p, p 2 ≠ 0 → v p = 0) :
    SB (Phi₂ (band D α) (in2 β) u v) (5 * Real.sqrt (9 + 8 * Real.log D) * (A * B * (U * V))) := by
  refine SB.equiv' revE (pos2_band hD hβ hα hv.refl hu.refl (fun p hp => hvs _ ?_)
    (fun p hp => hus _ ?_)) (fun x => ?_) |>.mono_bd (le_of_eq ?_)
  · simpa using hp
  · simpa using hp
  · exact Phi₂_rev _ _ _ _ x
  · ring

end OVNS.Quant.Metric

end
