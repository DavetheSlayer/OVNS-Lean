import OddViscousNS.Quant.Joint.Metric.DiffBlock

/-!
# The differentiated group: positive forms (step J5, nodes N5, N7)

`fib_cnt`: the two-dimensional band count of Body 42 ("One exterior `ℓ¹` norm costs `C F₀` against
its `ℓ²` norm by the two-dimensional band count").  `sb_kap₁`, `sb_kap₂`: the class
`q⁻¹ f₀ W`: `∑ α_l β_j u_a w_b κ(l, j) ≲ ‖α‖ ‖β‖ ‖u‖₂ ‖w‖₁`, with `κ = 1/J` on comparable exteriors.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {α β u w : Mode → ℝ} {A B U W : ℝ}

/-- The number of naturals below `T`, times `T`. -/
lemma sum_le_sq {T : ℝ} (hT : 0 ≤ T) (N : ℕ) :
    ∑ n ∈ Finset.range N, (if (n : ℝ) + 1 ≤ T then (n : ℝ) + 1 else 0) ≤ T ^ 2 := by
  classical
  have e : ∑ n ∈ Finset.range N, (if (n : ℝ) + 1 ≤ T then (n : ℝ) + 1 else 0) =
      ∑ n ∈ (Finset.range N).filter (fun n : ℕ => (n : ℝ) + 1 ≤ T), ((n : ℝ) + 1) :=
    (Finset.sum_filter _ _).symm
  rw [e]
  set s := (Finset.range N).filter (fun n : ℕ => (n : ℝ) + 1 ≤ T) with hs
  have h1 : ∀ n ∈ s, (n : ℝ) + 1 ≤ T := fun n hn => (Finset.mem_filter.1 hn).2
  have h2 : s ⊆ Finset.range ⌊T⌋₊ := fun n hn => by
    rw [Finset.mem_range]
    have := h1 n hn
    rw [Nat.lt_iff_add_one_le, Nat.le_floor_iff hT]
    push_cast
    exact this
  have h3 : (s.card : ℝ) ≤ T := by
    have h4 : s.card ≤ ⌊T⌋₊ := by simpa using Finset.card_le_card h2
    exact (Nat.cast_le.2 h4).trans (Nat.floor_le hT)
  calc ∑ n ∈ s, ((n : ℝ) + 1) ≤ ∑ _n ∈ s, T := Finset.sum_le_sum h1
    _ = s.card * T := by simp
    _ ≤ T * T := by gcongr
    _ = _ := by ring

/-- **The two-dimensional band count**, uniform in `J`. -/
theorem fib_cnt {J : ℝ} (hJ : 1 ≤ J) :
    Fib (fun k => if absk k ≤ 2 * J then J⁻¹ ^ 2 else 0) 33 := by
  have hJ0 : 0 < J := by linarith
  have hi : 0 ≤ J⁻¹ ^ 2 := by positivity
  have hi1 : J⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.2 hJ0.le) (inv_le_one_of_one_le₀ hJ)
  refine fib_of_shell (ψ₀ := 1) (ψ := fun n => if (n : ℝ) + 1 ≤ 2 * J then J⁻¹ ^ 2 else 0)
    (fun k => ?_) (fun k => ?_) (fun n k h => ?_) fun N => ?_
  · split_ifs
    · exact hi
    · exact le_rfl
  · split_ifs
    · exact hi1
    · norm_num
  · have hnJ : (n : ℝ) + 1 ≤ absk k := by
      rw [← absk_sq] at h
      exact (pow_le_pow_iff_left₀ (by positivity) (absk_nonneg k) (by norm_num)).1 h
    by_cases hk : absk k ≤ 2 * J
    · have : (n : ℝ) + 1 ≤ 2 * J := hnJ.trans hk
      simp [hk, this]
    · simp only [hk, ite_false]
      split_ifs
      · exact hi
      · exact le_rfl
  · have h1 := sum_le_sq (T := 2 * J) (by linarith) N
    have e : ∑ n ∈ Finset.range N, 8 * ((n : ℝ) + 1) *
        (if (n : ℝ) + 1 ≤ 2 * J then J⁻¹ ^ 2 else 0) =
        8 * J⁻¹ ^ 2 * ∑ n ∈ Finset.range N, (if (n : ℝ) + 1 ≤ 2 * J then (n : ℝ) + 1 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    rw [e]
    have h2 : 8 * J⁻¹ ^ 2 * (2 * J) ^ 2 = 32 := by
      field_simp
      norm_num
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 8 * J⁻¹ ^ 2)
    rw [h2] at h3
    linarith

/-- The fibre sum of `kapC`. -/
lemma kap_fib (j t : Mode) :
    SB (fun a : Mode => if a 2 = 0 then kapC (t + a) j ^ 2 else 0) 33 := by
  by_cases hj : j = 0
  · have h0 : ∀ a : Mode, (if a 2 = 0 then kapC (t + a) j ^ 2 else 0) = (0 : ℝ) := fun a => by
      have : kapC (t + a) j = 0 := by
        simp [kapC, hj, absk, absSq]
      simp [this]
    simp only [h0]
    exact ⟨summable_zero, by simp⟩
  have hJ := one_le_absk hj
  refine (fib_cnt hJ |>.add t).of_le (fun a => ?_) fun a => ?_
  · split_ifs <;> simp [sq_nonneg]
  · by_cases ha : a 2 = 0
    · simp only [ha, ite_true, kapC]
      by_cases h1 : absk (t + a) ≤ 2 * absk j ∧ absk j ≤ 2 * absk (t + a)
      · simp [h1]
      · simp only [h1, ite_false]
        have : (0 : ℝ) ≤ (absk j)⁻¹ ^ 2 := by positivity
        split_ifs
        · simpa using this
        · simp
    · simp [ha]

/-- **The class `f₀ W`**, the `ℓ²` leaf first. -/
theorem sb_kap₁ (hα : L2B α A) (hβ : L2B β B) (hu : L2B u U) (hw : L1B w W)
    (hus : ∀ p, p 2 ≠ 0 → u p = 0) :
    SB (fun x : I3 => Phi₂ α β u w x * kapC x.1 (inJ₂ x)) (Real.sqrt 33 * (A * B * (U * W))) := by
  have hW : 0 ≤ W := hw.bd_nonneg
  set v : Mode → ℝ := fun b => Real.sqrt (w b) with hv
  have hv2 : L2B v (Real.sqrt W) := by
    have e : ∀ b, v b ^ 2 = w b := fun b => Real.sq_sqrt (hw.nn b)
    refine ⟨fun b => Real.sqrt_nonneg _, ?_, ?_⟩
    · simp only [e]
      exact hw.s
    · simp only [e]
      exact Real.sqrt_le_sqrt hw.le
  set κ₁ : I3 → ℝ := fun x => v x.2.2 with hκ₁
  set κ₂ : I3 → ℝ := fun x => if x.2.1 2 = 0 then kapC x.1 (inJ₂ x) else 0 with hκ₂
  have h10 : ∀ x, 0 ≤ κ₁ x := fun x => Real.sqrt_nonneg _
  have h20 : ∀ x, 0 ≤ κ₂ x := fun x => by
    have := kapC_nonneg x.1 (inJ₂ x)
    simp only [hκ₂]
    split_ifs <;> simp [this]
  have h1 : ∀ l a, SB (fun b => κ₁ (l, a, b) ^ 2) W := fun l a => by
    have e : ∀ b, κ₁ (l, a, b) ^ 2 = w b := fun b => Real.sq_sqrt (hw.nn b)
    simp only [e]
    exact ⟨hw.s, hw.le⟩
  have h2 : ∀ j b, SB (fun a => κ₂ (j + b + a, a, b) ^ 2) 33 := fun j b => by
    refine (kap_fib j (j + b)).of_le (fun a => sq_nonneg _) fun a => le_of_eq ?_
    have e : inJ₂ (j + b + a, a, b) = j := by
      simp only [inJ₂]
      abel
    simp only [hκ₂, e]
    split_ifs <;> simp
  have h := cs_mid h10 h20 h1 h2 hW (by norm_num) hα hβ hu hv2
  have e : (fun x : I3 => Phi₂ α β u w x * kapC x.1 (inJ₂ x)) = fun x : I3 =>
      (α x.1 * u x.2.1 * κ₁ x) * (β (inJ₂ x) * v x.2.2 * κ₂ x) := by
    funext x
    have e1 : v x.2.2 * v x.2.2 = w x.2.2 := Real.mul_self_sqrt (hw.nn _)
    simp only [Phi₂, hκ₁, hκ₂]
    by_cases ha : x.2.1 2 = 0
    · simp only [ha, ite_true]
      calc _ = α x.1 * β (inJ₂ x) * (u x.2.1 * (v x.2.2 * v x.2.2)) * kapC x.1 (inJ₂ x) := by
            rw [e1]
        _ = _ := by ring
    · simp [hus _ ha]
  rw [e]
  refine h.mono_bd (le_of_eq ?_)
  have e2 : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hW
  calc A * U * Real.sqrt W * (B * Real.sqrt W * Real.sqrt 33)
      = Real.sqrt 33 * (A * B * (U * (Real.sqrt W * Real.sqrt W))) := by ring
    _ = _ := by rw [e2]

/-- **The class `f₀ W`**, the `ℓ²` leaf second. -/
theorem sb_kap₂ (hα : L2B α A) (hβ : L2B β B) (hu : L2B u U) (hw : L1B w W)
    (hus : ∀ p, p 2 ≠ 0 → u p = 0) :
    SB (fun x : I3 => Phi₂ α β w u x * kapC x.1 (inJ₂ x)) (Real.sqrt 33 * (A * B * (U * W))) := by
  refine SB.equiv swapL (sb_kap₁ hα hβ hu hw hus) fun x => ?_
  rw [Phi₂_swapL, inJ₂_swapL]
  rfl

/-! ### The form of `X₂` -/

variable {D : ℝ}

/-- The majorant of `D_S X₂`, the direction `h` in the first slot. -/
def PsiX (D q : ℝ) (G F h S : Field) (x : I3) : ℝ :=
  2 ^ 30 / q * (Phi₂ (nrm G) (nrm F) (nrm h) (nrm S) x * kapC x.1 (inJ₂ x)) +
  2 ^ 21 / q ^ 2 * (Phi₂ (gr G) (nrm F) (dv h) (nrm S) x * E2 x +
    Phi₂ (nrm G) (gr F) (dv h) (nrm S) x * E2 x) +
  2 ^ 18 * D / q ^ 2 * Phi₂ (in2 (nrm G)) (in2 (nrm F)) (gr h) (up (nrm S)) x

/-- The bound of the form. -/
def diffB (D q f₀ f₁ W b A B A₁ B₁ : ℝ) : ℝ :=
  2 ^ 30 / q * (Real.sqrt 33 * (A * B * (f₀ * W))) +
  2 ^ 21 / q ^ 2 * ((A₁ * B + A * B₁) * cls2 (c4 * f₁) W f₁ b) +
  2 ^ 18 * D / q ^ 2 * (c4 * A * (c4 * B) * (f₁ * b))

lemma PsiX_nonneg {q : ℝ} (hq : 0 < q) (hD : 0 ≤ D) (G F h S : Field) (x : I3) :
    0 ≤ PsiX D q G F h S x := by
  have n1 : ∀ u : Field, ∀ k, 0 ≤ nrm u k := fun u k => norm_nonneg _
  have n2 : ∀ u : Field, ∀ k, 0 ≤ up (nrm u) k := fun u k => up_nrm_nonneg u k
  have n3 : ∀ u : Field, ∀ k, 0 ≤ in2 (nrm u) k := fun u k =>
    div_nonneg (norm_nonneg _) (absSq_nonneg k)
  have n4 := gr_nonneg
  have t := fun (α β f₁ f₂ : Mode → ℝ) (a b c d) =>
    Phi₂_nonneg (α := α) (β := β) (f₁ := f₁) (f₂ := f₂) a b c d x
  have h1 := t _ _ _ _ (n1 G) (n1 F) (n1 h) (n1 S)
  have h2 := t _ _ _ _ (n4 G) (n1 F) (dv_nonneg h) (n1 S)
  have h3 := t _ _ _ _ (n1 G) (n4 F) (dv_nonneg h) (n1 S)
  have h4 := t _ _ _ _ (n3 G) (n3 F) (n4 h) (n2 S)
  have h5 := kapC_nonneg x.1 (inJ₂ x)
  have h6 := E2_nonneg x
  unfold PsiX
  positivity

/-- **The sum of the differentiated majorant.** -/
lemma sb_PsiX {q : ℝ} (hq : 0 < q) (hD : 0 ≤ D) {G F h S : Field}
    (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF1 : Summable fun k => ‖zOf 1 F k‖ ^ 2)
    (hh0 : Summable fun k => ‖h k‖ ^ 2) (hh : InH 1 h) (hh' : PiS h = h) (hS : MZ 2 S) :
    SB (PsiX D q G F h S) (diffB D q (l2n h) (hnorm 1 h) (wiener S) (hnorm 2 S) (l2n G) (l2n F)
      (l2n (zOf 1 G)) (l2n (zOf 1 F))) := by
  have hα := l2B_nrm hG
  have hβ := l2B_nrm hF
  have gα := l2B_half hG1
  have gβ := l2B_half hF1
  have wS := l1B_nrm hS.inH
  have uS := l2B_up hS.inH
  have t1 := sb_kap₁ hα hβ (l2B_nrm hh0) wS fun p hp => by
    simp [nrm, slow_zero hh' hp]
  have t2 := pos2_E2 gα hβ (l1B_dv hh) wS (l2B_up_dv hh) uS
  have t3 := pos2_E2 hα gβ (l1B_dv hh) wS (l2B_up_dv hh) uS
  have t4 := pos2_III hα.in2 hβ.in2 (l2B_gr hh) uS
  have h1 := t1.const_mul (by positivity : 0 ≤ 2 ^ 30 / q)
  have h2 := (t2.add t3).const_mul (by positivity : 0 ≤ 2 ^ 21 / q ^ 2)
  have h3 := t4.const_mul (by positivity : 0 ≤ 2 ^ 18 * D / q ^ 2)
  refine ((h1.add h2).add h3).mono_bd (le_of_eq ?_)
  simp only [diffB]
  ring

/-- A term of `D_S X₂`, the direction in the first slot. -/
lemma X2diff_term {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hD : 0 ≤ D) {h S G F : Field} (hh' : PiS h = h)
    (hh0 : h 0 = 0) (hS' : PiS S = S) (hF' : PiF F = F) {μ : I3 → ℂ} (hμ1 : ∀ x, ‖μ x‖ ≤ 1)
    (hμ0 : ∀ x : I3, D < absk (x.1 - x.2.1) → 4 * absk x.1 ≤ absk (x.1 - x.2.1) →
      4 * absk (x.1 - x.2.1 - x.2.2) ≤ absk (x.1 - x.2.1) → μ x = 0) (x : I3) :
    ‖μ x * inner ℂ (G x.1) (X2b 2 r τ h S x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))‖ ≤
      PsiX D |r| G F h S x := by
  have e0 : x.1 - x.2.1 - x.2.2 = inJ₂ x := rfl
  rw [e0]
  have hq : 0 < |r| := abs_pos.2 hr
  have hR := PsiX_nonneg (D := D) hq hD G F h S x
  by_cases hm : μ x = 0
  · simpa [hm] using hR
  by_cases ha : x.2.1 2 = 0
  swap
  · rw [X2b_eq_zero (Or.inl (slow_zero hh' ha))]
    simpa using hR
  by_cases hb : x.2.2 2 = 0
  swap
  · rw [X2b_eq_zero (Or.inr (slow_zero hS' hb))]
    simpa using hR
  by_cases hj : inJ₂ x 2 = 0
  · rw [fast_zero hF' hj, map_zero, inner_zero_right, mul_zero, norm_zero]
    exact hR
  by_cases ha0 : x.2.1 = 0
  · rw [X2b_eq_zero (Or.inl (by rw [ha0]; exact hh0))]
    simpa using hR
  have hA1 := one_le_absk ha0
  have hA : 0 < absk x.2.1 := by linarith
  have hB0 := absk_nonneg x.2.2
  have hj' : (x.1 - x.2.1 - x.2.2) 2 ≠ 0 := hj
  obtain ⟨hl0, -, hj0⟩ := fast_labels ha hb hj'
  have hL : 0 < absk x.1 := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (x.1 - x.2.1 - x.2.2) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  obtain ⟨q1, q2, -, -⟩ := two_leaf_paths x.1 x.2.1 x.2.2
  have hPa : absk x.2.1 ≤ absk (x.1 - x.2.1) + absk x.1 + absk (x.1 - x.2.1 - x.2.2) := by
    have h1 := absk_sub_le x.1 (x.1 - x.2.1)
    rw [show x.1 - (x.1 - x.2.1) = x.2.1 by abel] at h1
    linarith
  have hT0 : 0 ≤ 4 * D * absk x.2.1 * absk x.2.2 ^ 2 := by positivity
  have hT : absk (x.1 - x.2.1) ≤ D → 4 * absk x.1 ≤ absk (x.1 - x.2.1) →
      4 * absk (x.1 - x.2.1 - x.2.2) ≤ absk (x.1 - x.2.1) →
      absk (x.1 - x.2.1) ^ 4 ≤ 4 * D * absk x.2.1 * absk x.2.2 ^ 2 := fun h1 h2 h3 => by
    have m1 : absk (x.1 - x.2.1) ≤ 4 / 3 * absk x.2.1 := by linarith
    have m2 : absk (x.1 - x.2.1) ≤ 4 / 3 * absk x.2.2 := by linarith
    have hM0 := absk_nonneg (x.1 - x.2.1)
    have hX : 0 ≤ D * absk x.2.1 * absk x.2.2 ^ 2 := by positivity
    calc absk (x.1 - x.2.1) ^ 4 = absk (x.1 - x.2.1) * absk (x.1 - x.2.1) *
          absk (x.1 - x.2.1) * absk (x.1 - x.2.1) := by ring
      _ ≤ D * (4 / 3 * absk x.2.1) * (4 / 3 * absk x.2.2) * (4 / 3 * absk x.2.2) := by gcongr
      _ = 64 / 27 * (D * absk x.2.1 * absk x.2.2 ^ 2) := by ring
      _ ≤ _ := by nlinarith only [hX]
  have hmask : ¬ (D < absk (x.1 - x.2.1) ∧ 4 * absk x.1 ≤ absk (x.1 - x.2.1) ∧
      4 * absk (x.1 - x.2.1 - x.2.2) ≤ absk (x.1 - x.2.1)) := fun h1 =>
    hm (hμ0 x h1.1 h1.2.1 h1.2.2)
  have hB := norm_X2_diff hr τ h S ha hb hj' hA hT0 hPa hT hmask
  have h1 := norm_inner_apply_le (G x.1) (F (inJ₂ x)) (X2b 2 r τ h S x.1 x.2.1 x.2.2)
  have hP0 : 0 ≤ ‖G x.1‖ * ‖F (inJ₂ x)‖ := by positivity
  rw [norm_mul]
  refine (mul_le_mul (hμ1 x) (h1.trans (mul_le_mul_of_nonneg_left hB hP0))
    (norm_nonneg _) zero_le_one).trans (le_of_eq ?_)
  simp only [PsiX, Phi₂, in2, up, dv_apply, E2, gr, nrm, inJ₂, ← absk_sq]
  field_simp
  ring

/-- **`D_S X₂` off the high tail**, the direction in the first slot. -/
theorem X2diff_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hD : 0 ≤ D) {h S G F : Field}
    (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF1 : Summable fun k => ‖zOf 1 F k‖ ^ 2)
    (hh2 : Summable fun k => ‖h k‖ ^ 2) (hh : InH 1 h) (hh' : PiS h = h) (hh0 : h 0 = 0)
    (hS : MZ 2 S) (hS' : PiS S = S) (hF' : PiF F = F) {μ : I3 → ℂ} (hμ1 : ∀ x, ‖μ x‖ ≤ 1)
    (hμ0 : ∀ x : I3, D < absk (x.1 - x.2.1) → 4 * absk x.1 ≤ absk (x.1 - x.2.1) →
      4 * absk (x.1 - x.2.1 - x.2.2) ≤ absk (x.1 - x.2.1) → μ x = 0) :
    ‖X2Form μ 2 r τ h S G F‖ ≤ diffB D |r| (l2n h) (hnorm 1 h) (wiener S) (hnorm 2 S) (l2n G)
      (l2n F) (l2n (zOf 1 G)) (l2n (zOf 1 F)) := by
  have hs := sb_PsiX (D := D) (abs_pos.2 hr) hD hG hG1 hF hF1 hh2 hh hh' hS
  refine (form_le hs fun x => ?_).2
  exact X2diff_term hr τ hD hh' hh0 hS' hF' hμ1 hμ0 x

end OVNS.Quant.Metric

end
