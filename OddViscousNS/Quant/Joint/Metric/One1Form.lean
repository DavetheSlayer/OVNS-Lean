import OddViscousNS.Quant.Joint.Metric.One1
import OddViscousNS.Quant.Joint.Metric.Fib1

/-!
# Weight one: the forms (step J5, node N10)

Unit: `TIMED_METRIC_PROOF_V2.md` §8.1, §8.4.  With `L_h(β)` the fibre norm, `z = A^{1/2} F`:
* `X2_half_one`, `Z_half_one`: (8.1): `‖A^{1/2} X₂‖`, `‖A^{1/2} Z‖ ≲ q⁻¹ [W² + W a (L_h + L_h') + a² L_h L_h']`;
* `X2_diff_one`, `Z_diff_one`: (8.9), both slots, for any direction `v ∈ H¹`.

The sources' `G = W + a_ε` and fractional dissipation do not occur: `L_h(F)` costs one
`√(1 + ln D)` and a term `b_F/D`, `lhB_log`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic

variable {α β β₁ β₂ u v : Mode → ℝ} {A B U V L L₁ L₂ : ℝ}

lemma L1B.refl (h : L1B v V) : L1B (Metric.refl v) V := by
  refine ⟨fun k => h.nn _, (Equiv.neg Mode).summable_iff.2 h.s, ?_⟩
  have e : ∑' k, Metric.refl v k = ∑' k, v k := (Equiv.neg Mode).tsum_eq v
  rw [e]
  exact h.le

/-- The fibre on the output label. -/
theorem sb_fib_l (hα : L2B α A) (hβ : LhB β L) (hu : L2B u U) (hus : ∀ p, p 2 ≠ 0 → u p = 0)
    (hv : L1B v V) : SB (Phi₂ β α u v) (A * L * U * V) := by
  have hus' : ∀ p : Mode, p 2 ≠ 0 → Metric.refl u p = 0 := fun p hp => hus _ (by simpa using hp)
  have h1 := sb_fib hα hβ hu.refl hus' hv.refl
  have h2 : SB (Phi₂ α β (Metric.refl v) (Metric.refl u)) (A * L * U * V) :=
    SB.equiv swapL h1 fun x => Phi₂_swapL _ _ _ _ _
  exact SB.equiv revE h2 fun x => Phi₂_rev _ _ _ _ _

/-- The fibre rule, the `ℓ²` leaf second. -/
theorem sb_fib' (hα : L2B α A) (hβ : LhB β L) (hu : L2B u U) (hus : ∀ p, p 2 ≠ 0 → u p = 0)
    (hv : L1B v V) : SB (Phi₂ α β v u) (A * L * U * V) :=
  SB.equiv swapL (sb_fib hα hβ hu hus hv) fun _ => Phi₂_swapL _ _ _ _ _

/-- The fibre on the output label, the `ℓ²` leaf second. -/
theorem sb_fib_l' (hα : L2B α A) (hβ : LhB β L) (hu : L2B u U) (hus : ∀ p, p 2 ≠ 0 → u p = 0)
    (hv : L1B v V) : SB (Phi₂ β α v u) (A * L * U * V) :=
  SB.equiv swapL (sb_fib_l hα hβ hu hus hv) fun _ => Phi₂_swapL _ _ _ _ _

lemma gr_slow {S : Field} (hS' : PiS S = S) (p : Mode) (hp : p 2 ≠ 0) : gr S p = 0 := by
  simp [gr, slow_zero hS' hp]

lemma nrm_slow {S : Field} (hS' : PiS S = S) (p : Mode) (hp : p 2 ≠ 0) : nrm S p = 0 := by
  simp [nrm, slow_zero hS' hp]

/-! ### The output half -/

/-- The majorant of the output half. -/
def PsiHalf (G z F S : Mode → ℝ) (gS : Mode → ℝ) (x : I3) : ℝ :=
  Phi₂ G z S S x + Phi₂ (in1 G) z gS S x + Phi₂ (in1 G) z S gS x +
    Phi₂ G F gS S x + Phi₂ G F S gS x + Phi₂ (in1 G) F gS gS x

/-- The bound of the output half. -/
def halfB (a W e₁ e₂ L₁ L₂ : ℝ) : ℝ :=
  e₁ * e₂ * (W * W) + 2 * (e₂ * L₁ * a * W) + 2 * (e₁ * L₂ * a * W) + a * L₁ * (a * L₂)

/-- **The sum of the output half.** -/
theorem sb_PsiH {S G z F : Field} {e₁ e₂ : ℝ} (hS : MZ 2 S) (hS' : PiS S = S)
    (hG : L2B (nrm G) e₁) (hz : L2B (nrm z) e₂) (hLG : LhB (in1 (nrm G)) L₁)
    (hLF : LhB (nrm F) L₂) :
    SB (PsiHalf (nrm G) (nrm z) (nrm F) (nrm S) (gr S))
      (halfB (hnorm 1 S) (wiener S) e₁ e₂ L₁ L₂) := by
  have wS := l1B_nrm hS.inH
  have aS := l2B_gr (hS.inH.mono (by norm_num) : InH 1 S)
  have gs := gr_slow hS'
  have t1 := pos2_I hG hz wS wS
  have t2 := sb_fib_l hz hLG aS gs wS
  have t3 := sb_fib_l' hz hLG aS gs wS
  have t4 := sb_fib hG hLF aS gs wS
  have t5 := sb_fib' hG hLF aS gs wS
  have t6 := sb_fib₂ hLG hLF aS gs aS gs
  refine (((((t1.add t2).add t3).add t4).add t5).add t6).mono_bd (le_of_eq ?_)
  simp only [halfB]
  ring

lemma nrm_zOf_one (F : Field) (k : Mode) : nrm (zOf 1 F) k = absk k * ‖F k‖ := by
  simp only [nrm, zOf, pow_one, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (absk_nonneg k)]

/-- The majorant on a label. -/
lemma PsiHalf_eq {G F S : Field} {x : I3} (hl : x.1 ≠ 0) (hj : inJ₂ x ≠ 0) :
    PsiHalf (nrm G) (nrm (zOf 1 F)) (nrm F) (nrm S) (gr S) x =
      E1k x * ((‖G x.1‖ * ‖zOf 1 F (inJ₂ x)‖) * (‖S x.2.1‖ * ‖S x.2.2‖)) := by
  have hL : absk x.1 ≠ 0 := absk_eq_zero.not.2 hl
  have hJ : absk (inJ₂ x) ≠ 0 := absk_eq_zero.not.2 hj
  have e : ‖zOf 1 F (inJ₂ x)‖ = absk (inJ₂ x) * ‖F (inJ₂ x)‖ := nrm_zOf_one F _
  simp only [PsiHalf, Phi₂, in1, gr, nrm, E1k, e]
  field_simp
  ring

lemma PsiHalf_nonneg {G F S : Field} (x : I3) :
    0 ≤ PsiHalf (nrm G) (nrm (zOf 1 F)) (nrm F) (nrm S) (gr S) x := by
  have n1 : ∀ u : Field, ∀ k, 0 ≤ nrm u k := fun u k => norm_nonneg _
  have n5 : ∀ u : Field, ∀ k, 0 ≤ in1 (nrm u) k := fun u k =>
    div_nonneg (norm_nonneg _) (absk_nonneg k)
  have n4 := gr_nonneg
  have t := fun (α β f₁ f₂ : Mode → ℝ) (a b c d) =>
    Phi₂_nonneg (α := α) (β := β) (f₁ := f₁) (f₂ := f₂) a b c d x
  have h1 := t _ _ _ _ (n1 G) (n1 (zOf 1 F)) (n1 S) (n1 S)
  have h2 := t _ _ _ _ (n5 G) (n1 (zOf 1 F)) (n4 S) (n1 S)
  have h3 := t _ _ _ _ (n5 G) (n1 (zOf 1 F)) (n1 S) (n4 S)
  have h4 := t _ _ _ _ (n1 G) (n1 F) (n4 S) (n1 S)
  have h5 := t _ _ _ _ (n1 G) (n1 F) (n1 S) (n4 S)
  have h6 := t _ _ _ _ (n5 G) (n1 F) (n4 S) (n4 S)
  unfold PsiHalf
  positivity

/-- A term of the output half, for a block of the size of `norm_Y_half_one`. -/
lemma half_term {r : ℝ} {S G F : Field} (hq : 0 < |r|) (hS' : PiS S = S) (hF' : PiF F = F)
    {Y : I3 → Blk} (hY0 : ∀ x : I3, S x.2.1 = 0 ∨ S x.2.2 = 0 → Y x = 0)
    (hY : ∀ x : I3, x.2.1 2 = 0 → x.2.2 2 = 0 → (x.1 - x.2.1 - x.2.2) 2 ≠ 0 →
      absk x.1 * ‖Y x‖ ≤ 2 ^ 14 / |r| * E1k x * (‖S x.2.1‖ * ‖S x.2.2‖)) (x : I3) :
    ‖inner ℂ (zOf 1 G x.1) (Y x (zOf 1 F (x.1 - x.2.1 - x.2.2)))‖ ≤
      2 ^ 14 / |r| * PsiHalf (nrm G) (nrm (zOf 1 F)) (nrm F) (nrm S) (gr S) x := by
  have e0 : x.1 - x.2.1 - x.2.2 = inJ₂ x := rfl
  rw [e0]
  have hR : 0 ≤ 2 ^ 14 / |r| * PsiHalf (nrm G) (nrm (zOf 1 F)) (nrm F) (nrm S) (gr S) x :=
    mul_nonneg (by positivity) (PsiHalf_nonneg x)
  by_cases ha : x.2.1 2 = 0
  swap
  · rw [hY0 x (Or.inl (slow_zero hS' ha))]
    simpa using hR
  by_cases hb : x.2.2 2 = 0
  swap
  · rw [hY0 x (Or.inr (slow_zero hS' hb))]
    simpa using hR
  by_cases hj : inJ₂ x 2 = 0
  · have : zOf 1 F (inJ₂ x) = 0 := by
      simp [zOf, fast_zero hF' hj]
    rw [this, map_zero, inner_zero_right, norm_zero]
    exact hR
  have hj' : (x.1 - x.2.1 - x.2.2) 2 ≠ 0 := hj
  obtain ⟨hl0, -, hj0⟩ := fast_labels ha hb hj'
  have h1 := norm_inner_apply_le (zOf 1 G x.1) (zOf 1 F (inJ₂ x)) (Y x)
  have e1 : ‖zOf 1 G x.1‖ = absk x.1 * ‖G x.1‖ := nrm_zOf_one G _
  have hB := hY x ha hb hj'
  rw [PsiHalf_eq hl0 hj0]
  refine h1.trans ?_
  rw [e1]
  calc _ = ‖G x.1‖ * ‖zOf 1 F (inJ₂ x)‖ * (absk x.1 * ‖Y x‖) := by ring
    _ ≤ ‖G x.1‖ * ‖zOf 1 F (inJ₂ x)‖ * (2 ^ 14 / |r| * E1k x * (‖S x.2.1‖ * ‖S x.2.2‖)) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = _ := by ring

/-- **The output half of `X₂` at weight one** (8.1). -/
theorem X2_half_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S G F : Field} {e₁ e₂ : ℝ} (hS : MZ 2 S)
    (hS' : PiS S = S) (hF' : PiF F = F) (hG : L2B (nrm G) e₁) (hz : L2B (nrm (zOf 1 F)) e₂)
    (hLG : LhB (in1 (nrm G)) L₁) (hLF : LhB (nrm F) L₂) :
    (Summable fun x : I3 => inner ℂ (zOf 1 G x.1)
      (X2b 1 r τ S S x.1 x.2.1 x.2.2 (zOf 1 F (x.1 - x.2.1 - x.2.2)))) ∧
    ‖X2Form 1 1 r τ S S (zOf 1 G) (zOf 1 F)‖ ≤
      2 ^ 14 / |r| * halfB (hnorm 1 S) (wiener S) e₁ e₂ L₁ L₂ := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hs := (sb_PsiH hS hS' hG hz hLG hLF).const_mul (by positivity : 0 ≤ 2 ^ 14 / |r|)
  have hT := form_le hs (half_term (Y := fun x => X2b 1 r τ S S x.1 x.2.1 x.2.2) hq hS' hF'
    (fun x h0 => X2b_eq_zero h0) fun x ha hb hj => (norm_Y_half_one hr τ S S ha hb hj).1)
  refine ⟨hT.1, ?_⟩
  have e : X2Form 1 1 r τ S S (zOf 1 G) (zOf 1 F) = ∑' x : I3, inner ℂ (zOf 1 G x.1)
      (X2b 1 r τ S S x.1 x.2.1 x.2.2 (zOf 1 F (x.1 - x.2.1 - x.2.2))) := by
    simp only [X2Form, Pi.one_apply, one_mul]
  rw [e]
  exact hT.2

/-- **The output half of `Z` at weight one** (8.1). -/
theorem Z_half_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S G F : Field} {e₁ e₂ : ℝ} (hS : MZ 2 S)
    (hS' : PiS S = S) (hF' : PiF F = F) (hG : L2B (nrm G) e₁) (hz : L2B (nrm (zOf 1 F)) e₂)
    (hLG : LhB (in1 (nrm G)) L₁) (hLF : LhB (nrm F) L₂) :
    (Summable fun x : I3 => inner ℂ (zOf 1 G x.1)
      (Zb 1 r τ S S x.1 x.2.1 x.2.2 (zOf 1 F (x.1 - x.2.1 - x.2.2)))) ∧
    ‖ZForm 1 1 r τ S S (zOf 1 G) (zOf 1 F)‖ ≤
      2 ^ 14 / |r| * halfB (hnorm 1 S) (wiener S) e₁ e₂ L₁ L₂ := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hs := (sb_PsiH hS hS' hG hz hLG hLF).const_mul (by positivity : 0 ≤ 2 ^ 14 / |r|)
  have hT := form_le hs (half_term (Y := fun x => Zb 1 r τ S S x.1 x.2.1 x.2.2) hq hS' hF'
    (fun x h0 => Zb_eq_zero h0) fun x ha hb hj => (norm_Y_half_one hr τ S S ha hb hj).2)
  refine ⟨hT.1, ?_⟩
  have e : ZForm 1 1 r τ S S (zOf 1 G) (zOf 1 F) = ∑' x : I3, inner ℂ (zOf 1 G x.1)
      (Zb 1 r τ S S x.1 x.2.1 x.2.2 (zOf 1 F (x.1 - x.2.1 - x.2.2))) := by
    simp only [ZForm, Pi.one_apply, one_mul]
  rw [e]
  exact hT.2

/-! ### The direction of a slow source -/

/-- The majorant of a direction at weight one. -/
def PsiD (q c₁ c₂ : ℝ) (z F f g gf gg : Mode → ℝ) (x : I3) : ℝ :=
  c₁ / q * (Phi₂ F z f g x + Phi₂ z F f g x) + 2 * c₂ / q ^ 2 * Phi₂ F F gf gg x

/-- The bound of a direction at weight one. -/
def diff1B (q c₁ c₂ f₀ f₁ W a e L : ℝ) : ℝ :=
  c₁ / q * (2 * (e * L * f₀ * W)) + 2 * c₂ / q ^ 2 * ((f₁ * L) * (a * L))

lemma PsiD_nonneg {q c₁ c₂ : ℝ} (hq : 0 < q) (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) (F f g : Field)
    (x : I3) : 0 ≤ PsiD q c₁ c₂ (nrm (zOf 1 F)) (nrm F) (nrm f) (nrm g) (gr f) (gr g) x := by
  have n1 : ∀ u : Field, ∀ k, 0 ≤ nrm u k := fun u k => norm_nonneg _
  have n4 := gr_nonneg
  have t := fun (α β f₁ f₂ : Mode → ℝ) (a b c d) =>
    Phi₂_nonneg (α := α) (β := β) (f₁ := f₁) (f₂ := f₂) a b c d x
  have h3 := t _ _ _ _ (n1 F) (n1 (zOf 1 F)) (n1 f) (n1 g)
  have h4 := t _ _ _ _ (n1 (zOf 1 F)) (n1 F) (n1 f) (n1 g)
  have h5 := t _ _ _ _ (n1 F) (n1 F) (n4 f) (n4 g)
  unfold PsiD
  positivity

/-- A term of a direction at weight one. -/
lemma diff_one_term {r : ℝ} (hq : 0 < |r|) {c₁ c₂ : ℝ} (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) {f g F : Field}
    (hf' : PiS f = f) (hg' : PiS g = g) (hF' : PiF F = F) {μ : I3 → ℂ} (hμ1 : ∀ x, ‖μ x‖ ≤ 1)
    {Y : I3 → Blk} (hY0 : ∀ x : I3, f x.2.1 = 0 ∨ g x.2.2 = 0 → Y x = 0)
    (hY : ∀ x : I3, x.2.1 2 = 0 → x.2.2 2 = 0 → (x.1 - x.2.1 - x.2.2) 2 ≠ 0 →
      ‖Y x‖ ≤ (c₁ / |r| * ((absk x.1)⁻¹ + (absk (x.1 - x.2.1 - x.2.2))⁻¹) +
        c₂ / |r| ^ 2 * hiK x.1 x.2.1 x.2.2) * (‖f x.2.1‖ * ‖g x.2.2‖)) (x : I3) :
    ‖μ x * inner ℂ (zOf 1 F x.1) (Y x (zOf 1 F (x.1 - x.2.1 - x.2.2)))‖ ≤
      PsiD |r| c₁ c₂ (nrm (zOf 1 F)) (nrm F) (nrm f) (nrm g) (gr f) (gr g) x := by
  have e0 : x.1 - x.2.1 - x.2.2 = inJ₂ x := rfl
  rw [e0]
  have hR := PsiD_nonneg hq h1 h2 F f g x
  by_cases ha : x.2.1 2 = 0
  swap
  · rw [hY0 x (Or.inl (slow_zero hf' ha))]
    simpa using hR
  by_cases hb : x.2.2 2 = 0
  swap
  · rw [hY0 x (Or.inr (slow_zero hg' hb))]
    simpa using hR
  by_cases hj : inJ₂ x 2 = 0
  · have : zOf 1 F (inJ₂ x) = 0 := by
      simp [zOf, fast_zero hF' hj]
    rw [this, map_zero, inner_zero_right, mul_zero, norm_zero]
    exact hR
  have hj' : (x.1 - x.2.1 - x.2.2) 2 ≠ 0 := hj
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj'
  have hL : 0 < absk x.1 := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hJ : 0 < absk (inJ₂ x) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have h3 := norm_inner_apply_le (zOf 1 F x.1) (zOf 1 F (inJ₂ x)) (Y x)
  have e1 : ‖zOf 1 F x.1‖ = absk x.1 * ‖F x.1‖ := nrm_zOf_one F _
  have e2 : ‖zOf 1 F (inJ₂ x)‖ = absk (inJ₂ x) * ‖F (inJ₂ x)‖ := nrm_zOf_one F _
  have hB := hY x ha hb hj'
  have hFF : 0 ≤ ‖F x.1‖ * ‖F (inJ₂ x)‖ := by positivity
  have hfg : 0 ≤ ‖f x.2.1‖ * ‖g x.2.2‖ := by positivity
  have hkey : absk x.1 * absk (inJ₂ x) * hiK x.1 x.2.1 x.2.2 ≤ 2 * (absk x.2.1 * absk x.2.2) := by
    obtain ⟨q1, q2, -, -⟩ := two_leaf_paths x.1 x.2.1 x.2.2
    by_cases hhi : 4 * absk x.1 ≤ absk (x.1 - x.2.1) ∧
        4 * absk (x.1 - x.2.1 - x.2.2) ≤ absk (x.1 - x.2.1)
    · have e : hiK x.1 x.2.1 x.2.2 = absk (x.1 - x.2.1) ^ 2 /
          (absk x.1 * absk (x.1 - x.2.1 - x.2.2)) := by
        simp only [hiK, hhi.1, hhi.2, and_self, ite_true]
      rw [e]
      have e3 : absk (inJ₂ x) = absk (x.1 - x.2.1 - x.2.2) := rfl
      rw [e3] at hJ ⊢
      have e4 : absk x.1 * absk (x.1 - x.2.1 - x.2.2) * (absk (x.1 - x.2.1) ^ 2 /
          (absk x.1 * absk (x.1 - x.2.1 - x.2.2))) = absk (x.1 - x.2.1) ^ 2 := by
        field_simp
      rw [e4]
      have m1 : absk (x.1 - x.2.1) ≤ 4 / 3 * absk x.2.1 := by linarith [hhi.1]
      have m2 : absk (x.1 - x.2.1) ≤ 4 / 3 * absk x.2.2 := by linarith [hhi.2]
      have hM := absk_nonneg (x.1 - x.2.1)
      have hA := absk_nonneg x.2.1
      have hB' := absk_nonneg x.2.2
      have : absk (x.1 - x.2.1) ^ 2 ≤ 4 / 3 * absk x.2.1 * (4 / 3 * absk x.2.2) := by
        rw [sq]
        exact mul_le_mul m1 m2 hM (by positivity)
      nlinarith only [this, mul_nonneg hA hB']
    · have e : hiK x.1 x.2.1 x.2.2 = 0 := by simp [hiK, hhi]
      rw [e, mul_zero]
      have hA := absk_nonneg x.2.1
      have hB' := absk_nonneg x.2.2
      positivity
  rw [norm_mul]
  have e5 : absk (x.1 - x.2.1 - x.2.2) = absk (inJ₂ x) := rfl
  rw [e5] at hB
  calc _ ≤ 1 * (‖zOf 1 F x.1‖ * ‖zOf 1 F (inJ₂ x)‖ * ‖Y x‖) :=
        mul_le_mul (hμ1 x) h3 (norm_nonneg _) zero_le_one
    _ = absk x.1 * ‖F x.1‖ * (absk (inJ₂ x) * ‖F (inJ₂ x)‖) * ‖Y x‖ := by
        rw [e1, e2, one_mul]
    _ ≤ absk x.1 * ‖F x.1‖ * (absk (inJ₂ x) * ‖F (inJ₂ x)‖) * ((c₁ / |r| * ((absk x.1)⁻¹ +
        (absk (inJ₂ x))⁻¹) + c₂ / |r| ^ 2 * hiK x.1 x.2.1 x.2.2) * (‖f x.2.1‖ * ‖g x.2.2‖)) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = c₁ / |r| * ((‖F x.1‖ * (absk (inJ₂ x) * ‖F (inJ₂ x)‖) +
        absk x.1 * ‖F x.1‖ * ‖F (inJ₂ x)‖) * (‖f x.2.1‖ * ‖g x.2.2‖)) +
        c₂ / |r| ^ 2 * ((absk x.1 * absk (inJ₂ x) * hiK x.1 x.2.1 x.2.2) *
          ((‖F x.1‖ * ‖F (inJ₂ x)‖) * (‖f x.2.1‖ * ‖g x.2.2‖))) := by
        field_simp
    _ ≤ c₁ / |r| * ((‖F x.1‖ * (absk (inJ₂ x) * ‖F (inJ₂ x)‖) +
        absk x.1 * ‖F x.1‖ * ‖F (inJ₂ x)‖) * (‖f x.2.1‖ * ‖g x.2.2‖)) +
        c₂ / |r| ^ 2 * ((2 * (absk x.2.1 * absk x.2.2)) *
          ((‖F x.1‖ * ‖F (inJ₂ x)‖) * (‖f x.2.1‖ * ‖g x.2.2‖))) := by
        gcongr
    _ = _ := by
        simp only [PsiD, Phi₂, gr, nrm, e1, e2]
        ring

/-- The sum of a direction, the `ℓ²` leaf first. -/
lemma sb_PsiD₁ {q c₁ c₂ e : ℝ} (hq : 0 < q) (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) {v S F : Field}
    (hv2 : Summable fun k => ‖v k‖ ^ 2) (hv : InH 1 v) (hv' : PiS v = v) (hS : MZ 2 S)
    (hS' : PiS S = S) (hz : L2B (nrm (zOf 1 F)) e) (hLF : LhB (nrm F) L) :
    SB (PsiD q c₁ c₂ (nrm (zOf 1 F)) (nrm F) (nrm v) (nrm S) (gr v) (gr S))
      (diff1B q c₁ c₂ (l2n v) (hnorm 1 v) (wiener S) (hnorm 1 S) e L) := by
  have wS := l1B_nrm hS.inH
  have aS := l2B_gr (hS.inH.mono (by norm_num) : InH 1 S)
  have uv := l2B_nrm hv2
  have av := l2B_gr hv
  have t1 := sb_fib_l hz hLF uv (nrm_slow hv') wS
  have t2 := sb_fib hz hLF uv (nrm_slow hv') wS
  have t3 := sb_fib₂ hLF hLF av (gr_slow hv') aS (gr_slow hS')
  have h3 := (t1.add t2).const_mul (by positivity : 0 ≤ c₁ / q)
  have h4 := t3.const_mul (by positivity : 0 ≤ 2 * c₂ / q ^ 2)
  refine (h3.add h4).mono_bd (le_of_eq ?_)
  simp only [diff1B]
  ring

/-- The sum of a direction, the `ℓ²` leaf second. -/
lemma sb_PsiD₂ {q c₁ c₂ e : ℝ} (hq : 0 < q) (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) {v S F : Field}
    (hv2 : Summable fun k => ‖v k‖ ^ 2) (hv : InH 1 v) (hv' : PiS v = v) (hS : MZ 2 S)
    (hS' : PiS S = S) (hz : L2B (nrm (zOf 1 F)) e) (hLF : LhB (nrm F) L) :
    SB (PsiD q c₁ c₂ (nrm (zOf 1 F)) (nrm F) (nrm S) (nrm v) (gr S) (gr v))
      (diff1B q c₁ c₂ (l2n v) (hnorm 1 v) (wiener S) (hnorm 1 S) e L) := by
  have wS := l1B_nrm hS.inH
  have aS := l2B_gr (hS.inH.mono (by norm_num) : InH 1 S)
  have uv := l2B_nrm hv2
  have av := l2B_gr hv
  have t1 := sb_fib_l' hz hLF uv (nrm_slow hv') wS
  have t2 := sb_fib' hz hLF uv (nrm_slow hv') wS
  have t3 := sb_fib₂ hLF hLF aS (gr_slow hS') av (gr_slow hv')
  have h3 := (t1.add t2).const_mul (by positivity : 0 ≤ c₁ / q)
  have h4 := t3.const_mul (by positivity : 0 ≤ 2 * c₂ / q ^ 2)
  refine (h3.add h4).mono_bd (le_of_eq ?_)
  simp only [diff1B]
  ring

/-- `Z` in the shape of the common term. -/
lemma Z_shape {r τ : ℝ} (hr : r ≠ 0) (f g : Field) (x : I3) (ha : x.2.1 2 = 0) (hb : x.2.2 2 = 0)
    (hj : (x.1 - x.2.1 - x.2.2) 2 ≠ 0) :
    ‖Zb 1 r τ f g x.1 x.2.1 x.2.2‖ ≤ (2 ^ 11 / |r| * ((absk x.1)⁻¹ +
      (absk (x.1 - x.2.1 - x.2.2))⁻¹) + 0 / |r| ^ 2 * hiK x.1 x.2.1 x.2.2) *
        (‖f x.2.1‖ * ‖g x.2.2‖) := by
  simpa using norm_Z_one hr τ f g ha hb hj

/-- **A slow direction at weight one** (8.9): the four slots of `X₂`, `Z`, for every multiplier. -/
theorem Y_diff_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {v S F : Field} {e : ℝ}
    (hv2 : Summable fun k => ‖v k‖ ^ 2) (hv : InH 1 v) (hv' : PiS v = v) (hS : MZ 2 S)
    (hS' : PiS S = S) (hF' : PiF F = F) (hz : L2B (nrm (zOf 1 F)) e) (hLF : LhB (nrm F) L)
    {μ : I3 → ℂ} (hμ1 : ∀ x, ‖μ x‖ ≤ 1) :
    ‖X2Form μ 1 r τ v S (zOf 1 F) (zOf 1 F)‖ ≤
        diff1B |r| (2 ^ 15) (2 ^ 15) (l2n v) (hnorm 1 v) (wiener S) (hnorm 1 S) e L ∧
      ‖X2Form μ 1 r τ S v (zOf 1 F) (zOf 1 F)‖ ≤
        diff1B |r| (2 ^ 15) (2 ^ 15) (l2n v) (hnorm 1 v) (wiener S) (hnorm 1 S) e L ∧
      ‖ZForm μ 1 r τ v S (zOf 1 F) (zOf 1 F)‖ ≤
        diff1B |r| (2 ^ 11) 0 (l2n v) (hnorm 1 v) (wiener S) (hnorm 1 S) e L ∧
      ‖ZForm μ 1 r τ S v (zOf 1 F) (zOf 1 F)‖ ≤
        diff1B |r| (2 ^ 11) 0 (l2n v) (hnorm 1 v) (wiener S) (hnorm 1 S) e L := by
  have hq : 0 < |r| := abs_pos.2 hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs := sb_PsiD₁ hq (by norm_num : (0 : ℝ) ≤ 2 ^ 15) (by norm_num : (0 : ℝ) ≤ 2 ^ 15) hv2 hv
      hv' hS hS' hz hLF
    refine (form_le hs fun x => ?_).2
    exact diff_one_term hq (by norm_num) (by norm_num) hv' hS' hF' hμ1
      (Y := fun x => X2b 1 r τ v S x.1 x.2.1 x.2.2) (fun x h0 => X2b_eq_zero h0)
      (fun x ha hb hj => norm_X2_one hr τ v S ha hb hj) x
  · have hs := sb_PsiD₂ hq (by norm_num : (0 : ℝ) ≤ 2 ^ 15) (by norm_num : (0 : ℝ) ≤ 2 ^ 15) hv2 hv
      hv' hS hS' hz hLF
    refine (form_le hs fun x => ?_).2
    exact diff_one_term hq (by norm_num) (by norm_num) hS' hv' hF' hμ1
      (Y := fun x => X2b 1 r τ S v x.1 x.2.1 x.2.2) (fun x h0 => X2b_eq_zero h0)
      (fun x ha hb hj => norm_X2_one hr τ S v ha hb hj) x
  · have hs := sb_PsiD₁ hq (by norm_num : (0 : ℝ) ≤ 2 ^ 11) le_rfl hv2 hv hv' hS hS' hz hLF
    refine (form_le hs fun x => ?_).2
    exact diff_one_term hq (by norm_num) le_rfl hv' hS' hF' hμ1
      (Y := fun x => Zb 1 r τ v S x.1 x.2.1 x.2.2) (fun x h0 => Zb_eq_zero h0)
      (fun x ha hb hj => Z_shape (τ := τ) hr v S x ha hb hj) x
  · have hs := sb_PsiD₂ hq (by norm_num : (0 : ℝ) ≤ 2 ^ 11) le_rfl hv2 hv hv' hS hS' hz hLF
    refine (form_le hs fun x => ?_).2
    exact diff_one_term hq (by norm_num) le_rfl hS' hv' hF' hμ1
      (Y := fun x => Zb 1 r τ S v x.1 x.2.1 x.2.2) (fun x h0 => Zb_eq_zero h0)
      (fun x ha hb hj => Z_shape (τ := τ) hr S v x ha hb hj) x

end OVNS.Quant.Metric

end
