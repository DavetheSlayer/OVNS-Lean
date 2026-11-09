import OddViscousNS.Quant.Joint.Force.X1Form

/-!
# The native differential in the genuine force (step J5, node N12)

Body 16 (F219, eq. (N)): "`|D₂(F;h)| ≤ 384 a c_F ‖Π_F h‖₁` … the two input terms cost `128 a c_F
‖h‖₁`, while the test term costs `16√208 b²‖h‖₁ ≤ 256 a c_F ‖h‖₁`, using `b² ≤ a c_F`", from
`‖R(u,v)‖₁ ≤ 64 ‖u‖₁‖v‖₁` and `‖R(F,F)‖₃ ≲ b²`.  At weight one the same three terms give
`|D₁(F;h)| ≲ a_F² ‖h‖₁`: this is the tested force `q_force = 64 P_F² h` of Bodies 15, 45.

Neither bound uses a phase or a pointwise bound on `h`; the constants are `c₄`, not `64`.
The library's `cubicD_one_le`, `cubicD_two_le` have the factor `N(q)`, but need a pointwise `H¹`,
resp. an `H²` norm of the force, which is the wrong regularity for this slot (Body 16).

* `conv_H1`: `H¹ ⋆ H¹ ⊂ ℓ²`, `‖a ⋆ b‖_{ℓ²} ≤ c₄ ‖a‖₁ ‖b‖₁`;
* `hnorm_one_gain_le`, `hnorm_three_gain_le`: `R : H¹ × H¹ → H¹`, `R : H² × H² → H³`;
* **`cubicD_tame_one`, `cubicD_tame_two`.**
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. `H¹ ⋆ H¹` -/

/-- The inverse length, zero at the origin. -/
private def wI (k : Mode) : ℝ := if k = 0 then 0 else (absk k)⁻¹

private lemma wI_nonneg (k : Mode) : 0 ≤ wI k := by
  unfold wI
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.2 (absk_nonneg k)

private lemma wI_fourth (k : Mode) :
    wI k ^ 4 = if k = 0 then (0 : ℝ) else (absk k)⁻¹ ^ 4 := by
  unfold wI
  split_ifs <;> simp

/-- `∑_p |p|⁻²|k − p|⁻² ≤ c₄²`. -/
private lemma sb_wI (k : Mode) : SB (fun p => (wI p * wI (k - p)) ^ 2) (c4 ^ 2) := by
  have h1 : SB (fun p : Mode => wI p ^ 4) (c4 ^ 2) := by
    simpa only [wI_fourth] using sb_inv4
  have h2 : SB (fun p : Mode => wI (k - p) ^ 4) (c4 ^ 2) :=
    SB.equiv' (Equiv.subLeft k) h1 fun p => rfl
  have h3 := (h1.add h2).const_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have e : (1 / 2 : ℝ) * (c4 ^ 2 + c4 ^ 2) = c4 ^ 2 := by ring
  rw [e] at h3
  refine h3.of_le (fun p => sq_nonneg _) fun p => ?_
  nlinarith only [sq_nonneg (wI p ^ 2 - wI (k - p) ^ 2)]

/-- **`H¹ ⋆ H¹ ⊂ ℓ²`**: for nonnegative mean-zero sequences. -/
theorem conv_H1 {a b : Mode → ℝ} {A B : ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (ha0 : a 0 = 0)
    (hb0 : b 0 = 0) (hA : L2B (fun k => absk k * a k) A) (hB : L2B (fun k => absk k * b k) B) :
    (∀ k, Summable fun p => a p * b (k - p)) ∧ L2B (convR a b) (c4 * (A * B)) := by
  have hA0 := hA.bd_nonneg
  have hB0 := hB.bd_nonneg
  set a' : Mode → ℝ := fun k => absk k * a k with ha'
  set b' : Mode → ℝ := fun k => absk k * b k with hb'
  have e0 : ∀ {c : Mode → ℝ}, c 0 = 0 → ∀ p, c p = absk p * c p * wI p := fun {c} hc p => by
    by_cases hp : p = 0
    · subst hp
      simp [hc]
    · have hP : absk p ≠ 0 := (lt_of_lt_of_le one_pos (one_le_absk hp)).ne'
      simp only [wI, hp, ↓reduceIte]
      field_simp
  set t : Mode → ℝ := fun k => ∑' p, (a' p * b' (k - p)) ^ 2 with ht
  have hsq : SB (fun x : Mode × Mode => (a' x.1 * b' x.2) ^ 2) (A ^ 2 * B ^ 2) := by
    have := SB.pairing hA.sq hB.sq (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    simpa only [mul_pow] using this
  let sh : Mode × Mode ≃ Mode × Mode :=
    { toFun := fun z => (z.2, z.1 - z.2), invFun := fun z => (z.1 + z.2, z.1),
      left_inv := fun z => by simp, right_inv := fun z => by simp }
  have hsq2 : SB (fun x : Mode × Mode => (a' x.2 * b' (x.1 - x.2)) ^ 2) (A ^ 2 * B ^ 2) :=
    SB.equiv' sh hsq fun _ => rfl
  have hin : ∀ k, Summable fun p => (a' p * b' (k - p)) ^ 2 := fun k => hsq2.1.prod_factor k
  have ht1 : SB t (A ^ 2 * B ^ 2) := ⟨hsq2.1.prod, by
    rw [← hsq2.1.tsum_prod]
    exact hsq2.2⟩
  have hpt : ∀ k, SB (fun p => (a' p * b' (k - p)) * (wI p * wI (k - p)))
      (Real.sqrt (t k) * c4) := fun k => by
    have hc4 := c4_pos.le
    have h0 : 0 ≤ t k := tsum_nonneg fun _ => sq_nonneg _
    refine SB.cs (fun p => mul_nonneg (hA.nn _) (hB.nn _))
      (fun p => mul_nonneg (wI_nonneg _) (wI_nonneg _)) (Real.sqrt_nonneg _) hc4 ?_ (sb_wI k)
    rw [Real.sq_sqrt h0]
    exact ⟨hin k, le_rfl⟩
  have e1 : ∀ k p, a p * b (k - p) = (a' p * b' (k - p)) * (wI p * wI (k - p)) := fun k p => by
    conv_lhs => rw [e0 ha0 p, e0 hb0 (k - p)]
    simp only [ha', hb']
    ring
  have hs : ∀ k, Summable fun p => a p * b (k - p) := fun k => by
    simp only [e1]
    exact (hpt k).1
  have hc : ∀ k, convR a b k ≤ Real.sqrt (t k) * c4 := fun k => by
    unfold convR
    simp only [e1]
    exact (hpt k).2
  have hc0 := convR_nonneg ha hb
  have hc2 : ∀ k, convR a b k ^ 2 ≤ c4 ^ 2 * t k := fun k => by
    have h0 : 0 ≤ t k := tsum_nonneg fun _ => sq_nonneg _
    have h1 := pow_le_pow_left₀ (hc0 k) (hc k) 2
    rw [mul_pow, Real.sq_sqrt h0] at h1
    linarith
  have hS : SB (fun k => c4 ^ 2 * t k) (c4 ^ 2 * (A ^ 2 * B ^ 2)) := ht1.const_mul (sq_nonneg _)
  have hS2 := hS.of_le (fun k => sq_nonneg (convR a b k)) hc2
  refine ⟨hs, hc0, hS2.1, ?_⟩
  have e2 : c4 ^ 2 * (A ^ 2 * B ^ 2) = (c4 * (A * B)) ^ 2 := by ring
  rw [e2] at hS2
  exact Real.sqrt_le_iff.2 ⟨by have := c4_pos; positivity, hS2.2⟩

/-- The triangle inequality in `ℓ²`. -/
lemma L2B.add {a b : Mode → ℝ} {A B : ℝ} (ha : L2B a A) (hb : L2B b B) :
    L2B (fun k => a k + b k) (A + B) := by
  have hA := ha.bd_nonneg
  have hB := hb.bd_nonneg
  have h1 := ha.sq
  have h2 := hb.sq
  have h3 : SB (fun k => a k * b k) (A * B) := ha.pair hb
  have h4 : SB (fun k => (a k + b k) ^ 2) (A ^ 2 + 2 * (A * B) + B ^ 2) := by
    refine ((h1.add (SB.const_mul h3 (by norm_num : (0 : ℝ) ≤ 2))).add h2).of_le
      (fun _ => sq_nonneg _) fun k => le_of_eq ?_
    ring
  refine ⟨fun k => add_nonneg (ha.nn k) (hb.nn k), h4.1, Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩⟩
  refine h4.2.trans (le_of_eq ?_)
  ring

/-! ### B. The gain multipliers -/

variable {m : Mult} {f g : Field}

/-- The gain bound: `|k| ‖Q^♯_m(f, g)_k‖ ≤ 8 ∑_p ‖f_p‖ ‖g_{k−p}‖`. -/
lemma mul_norm_gain_le (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q)) {k : Mode}
    (hk : k ≠ 0) (hs : Summable fun p => ‖f p‖ * ‖g (k - p)‖) :
    absk k * ‖Qm m f g k‖ ≤ 8 * ∑' p, ‖f p‖ * ‖g (k - p)‖ := by
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
  have hb : ∀ p, ‖blk m p k (k - p) (f p) (g (k - p))‖ ≤ 8 / absk k * (‖f p‖ * ‖g (k - p)‖) :=
    fun p => by
      have ekj : p + (k - p) = k := by abel
      have hm' : ∀ a b c, ‖m a b c p (k - p)‖ ≤ 1 / absSq k := fun a b c => by
        have := hm a b c p (k - p)
        rwa [ekj] at this
      have h1 := norm_blk_le_of (m := m) (by have := absSq_nonneg k; positivity) hm' ekj (f p)
      have h2 := (ContinuousLinearMap.le_opNorm (blk m p k (k - p) (f p)) (g (k - p))).trans
        (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
      refine h2.trans (le_of_eq ?_)
      rw [← absk_sq k]
      field_simp
  have hs2 : Summable fun p => ‖blk m p k (k - p) (f p) (g (k - p))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hs.mul_left _)
  rw [Qm_eq_tsum_blk]
  calc absk k * ‖∑' p, blk m p k (k - p) (f p) (g (k - p))‖
      ≤ absk k * ∑' p, 8 / absk k * (‖f p‖ * ‖g (k - p)‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hK.le
        exact (norm_tsum_le_tsum_norm hs2).trans (hs2.tsum_le_tsum hb (hs.mul_left _))
    _ = _ := by
        rw [tsum_mul_left]
        field_simp

/-- The norm from a weighted bound. -/
lemma hnorm_le_of_L2B {n : ℕ} {c : Field} {a : Mode → ℝ} {B : ℝ} (ha : L2B a B)
    (h : ∀ k, k ≠ 0 → absk k ^ n * ‖c k‖ ≤ a k) (hc0 : c 0 = 0) :
    InH n c ∧ hnorm n c ≤ B := by
  have hle : ∀ k, sobWeight n k * ‖c k‖ ^ 2 ≤ a k ^ 2 := fun k => by
    by_cases hk : k = 0
    · subst hk
      simp only [hc0, norm_zero]
      have := sq_nonneg (a 0)
      simpa using this
    have hw : sobWeight (n : ℝ) k = (absk k ^ n) ^ 2 := by
      rw [sobWeight_nat n hk]
      ring
    rw [hw, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (pow_nonneg (absk_nonneg k) n) (norm_nonneg _)) (h k hk) 2
  have hI : InH n c :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg _ k) (sq_nonneg _)) hle ha.s
  refine ⟨hI, ?_⟩
  exact (Real.sqrt_le_sqrt (hI.tsum_le_tsum hle ha.s)).trans ha.le

lemma l2B_nrm_grad {F : Field} (hF : InH 1 F) : L2B (fun k => absk k * nrm F k) (hnorm 1 F) := by
  have := l2B_gr hF
  exact this

lemma Qm_zero_mode' (m : Mult) (f g : Field) : Qm m f g 0 = 0 :=
  OVNS.Quant.H2.Qm_zero_mode m f g

/-- **`R : H¹ × H¹ → H¹`** (Body 12 §1: "`R₋ : H¹ × H¹ → H¹` with constant 64"). -/
theorem hnorm_one_gain_le (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q)) (hf : MZ 1 f)
    (hg : MZ 1 g) : InH 1 (Qm m f g) ∧ hnorm 1 (Qm m f g) ≤ 8 * c4 * (hnorm 1 f * hnorm 1 g) := by
  obtain ⟨hs, hL⟩ := conv_H1 (fun k => norm_nonneg (f k)) (fun k => norm_nonneg (g k))
    (by simp [hf.mean]) (by simp [hg.mean]) (l2B_nrm_grad hf.inH) (l2B_nrm_grad hg.inH)
  have hL8 : L2B (fun k => 8 * convR (fun k => ‖f k‖) (fun k => ‖g k‖) k)
      (8 * (c4 * (hnorm 1 f * hnorm 1 g))) := by
    refine ⟨fun k => mul_nonneg (by norm_num) (hL.nn k), ?_, ?_⟩
    · simp only [mul_pow]
      exact hL.s.mul_left _
    · simp only [mul_pow]
      rw [tsum_mul_left, Real.sqrt_mul (by norm_num), show (8 : ℝ) ^ 2 = 8 * 8 by norm_num,
        Real.sqrt_mul_self (by norm_num)]
      exact mul_le_mul_of_nonneg_left hL.le (by norm_num)
  have h := hnorm_le_of_L2B (n := 1) (c := Qm m f g) hL8 (fun k hk => by
    rw [pow_one]
    exact mul_norm_gain_le hm hk (hs k)) (Qm_zero_mode' m f g)
  simp only [Nat.cast_one] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  ring

/-- **`R : H² × H² → H³`**, with the product norm (Body 12 §1 `‖R(F,F)‖₃ ≤ 16√208 b²`). -/
theorem hnorm_three_gain_le (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q)) (hf : MZ 2 f)
    (hg : MZ 2 g) : InH 3 (Qm m f g) ∧
      hnorm 3 (Qm m f g) ≤ 16 * (hnorm 2 f * wiener g + wiener f * hnorm 2 g) := by
  obtain ⟨c1, d1⟩ := (l2B_up hf.inH).conv_l1 (l1B_nrm hg.inH)
  obtain ⟨c2, d2⟩ := (l1B_nrm hf.inH).conv_l2 (l2B_up hg.inH)
  set a : Mode → ℝ := fun k => 16 * (convR (up (nrm f)) (nrm g) k + convR (nrm f) (up (nrm g)) k)
    with ha
  have hL : L2B a (16 * (hnorm 2 f * wiener g + wiener f * hnorm 2 g)) := by
    have h0 : ∀ k, 0 ≤ convR (up (nrm f)) (nrm g) k + convR (nrm f) (up (nrm g)) k := fun k =>
      add_nonneg (d1.nn k) (d2.nn k)
    have hsum : L2B (fun k => convR (up (nrm f)) (nrm g) k + convR (nrm f) (up (nrm g)) k)
        (hnorm 2 f * wiener g + wiener f * hnorm 2 g) := L2B.add d1 d2
    refine ⟨fun k => mul_nonneg (by norm_num) (h0 k), ?_, ?_⟩
    · simp only [ha, mul_pow]
      exact hsum.s.mul_left _
    · simp only [ha, mul_pow]
      rw [tsum_mul_left, Real.sqrt_mul (by norm_num), show (16 : ℝ) ^ 2 = 16 * 16 by norm_num,
        Real.sqrt_mul_self (by norm_num)]
      exact mul_le_mul_of_nonneg_left hsum.le (by norm_num)
  refine hnorm_le_of_L2B (n := 3) hL (fun k hk => ?_) (Qm_zero_mode' m f g)
  have hl1 : L1B (nrm f) (wiener f) := l1B_nrm hf.inH
  have hle : ∀ p, ‖f p‖ * ‖g (k - p)‖ ≤ absSq p * ‖f p‖ * ‖g (k - p)‖ +
      ‖f p‖ * (absSq (k - p) * ‖g (k - p)‖) := fun p => by
    by_cases hp : p = 0
    · subst hp
      simp only [hf.mean, norm_zero, zero_mul, mul_zero, add_zero, le_refl]
    · have h1 := one_le_absSq hp
      have h2 := mul_nonneg (norm_nonneg (f p)) (norm_nonneg (g (k - p)))
      have h3 : 0 ≤ ‖f p‖ * (absSq (k - p) * ‖g (k - p)‖) :=
        mul_nonneg (norm_nonneg _) (mul_nonneg (absSq_nonneg _) (norm_nonneg _))
      nlinarith only [h1, h2, h3]
  have hsum0 : Summable fun p => ‖f p‖ * ‖g (k - p)‖ :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hle
      ((c1 k).add (c2 k))
  have hK := absk_nonneg k
  have h1 := mul_norm_gain_le hm hk hsum0
  have hKK : absk k ^ 2 * ∑' p, ‖f p‖ * ‖g (k - p)‖ ≤
      2 * (convR (up (nrm f)) (nrm g) k + convR (nrm f) (up (nrm g)) k) := by
    rw [← tsum_mul_left]
    have hsS := ((c1 k).add (c2 k)).mul_left 2
    have e2 : convR (up (nrm f)) (nrm g) k + convR (nrm f) (up (nrm g)) k =
        ∑' p, (up (nrm f) p * nrm g (k - p) + nrm f p * up (nrm g) (k - p)) := by
      rw [(c1 k).tsum_add (c2 k)]
      rfl
    rw [e2, ← tsum_mul_left]
    refine (hsum0.mul_left _).tsum_le_tsum (fun p => ?_) hsS
    have ekj : k = p + (k - p) := by abel
    have h2 : absk k ^ 2 ≤ 2 * (absSq p + absSq (k - p)) := by
      rw [absk_sq]
      exact absSq_le₂ ekj
    have h3 := mul_le_mul_of_nonneg_right h2
      (mul_nonneg (norm_nonneg (f p)) (norm_nonneg (g (k - p))))
    refine h3.trans (le_of_eq ?_)
    simp only [up, nrm]
    ring
  calc absk k ^ 3 * ‖Qm m f g k‖ = absk k ^ 2 * (absk k * ‖Qm m f g k‖) := by ring
    _ ≤ absk k ^ 2 * (8 * ∑' p, ‖f p‖ * ‖g (k - p)‖) := by gcongr
    _ = 8 * (absk k ^ 2 * ∑' p, ‖f p‖ * ‖g (k - p)‖) := by ring
    _ ≤ 8 * (2 * (convR (up (nrm f)) (nrm g) k + convR (nrm f) (up (nrm g)) k)) := by gcongr
    _ = a k := by simp only [ha]; ring

/-! ### C. The pairing -/

/-- The pairing is symmetric. -/
lemma pair_comm' (σ : ℝ) (c F : Field) : pair σ c F = pair σ F c := by
  unfold pair
  refine tsum_congr fun k => ?_
  have := inner_re_symm (𝕜 := ℂ) (c k) (F k)
  simp only [RCLike.re_to_complex] at this
  rw [this]

/-- `|⟨c, F⟩_σ| ≤ ‖c‖_σ ‖F‖_σ`. -/
lemma abs_pair_symm_le {σ : ℝ} {c F : Field} (hc : InH σ c) (hF : InH σ F) :
    |pair σ c F| ≤ hnorm σ c * hnorm σ F := by
  set A : Mode → ℝ := fun k => Real.sqrt (sobWeight σ k) * ‖c k‖ with hA
  set B : Mode → ℝ := fun k => Real.sqrt (sobWeight σ k) * ‖F k‖ with hB
  have e : ∀ {u : Field} k, (Real.sqrt (sobWeight σ k) * ‖u k‖) ^ 2 = sobWeight σ k * ‖u k‖ ^ 2 :=
    fun {u} k => by rw [mul_pow, Real.sq_sqrt (sobWeight_nonneg σ k)]
  have hA2 : L2B A (hnorm σ c) := by
    refine ⟨fun k => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _), ?_, ?_⟩
    · simp only [hA, e]
      exact hc
    · simp only [hA, e, hnorm]
      exact le_rfl
  have hB2 : L2B B (hnorm σ F) := by
    refine ⟨fun k => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _), ?_, ?_⟩
    · simp only [hB, e]
      exact hF
    · simp only [hB, e, hnorm]
      exact le_rfl
  have hp : SB (fun k => A k * B k) (hnorm σ c * hnorm σ F) := hA2.pair hB2
  have hle : ∀ k, ‖sobWeight σ k * (inner ℂ (c k) (F k)).re‖ ≤ A k * B k := fun k => by
    refine (norm_pair_term_le' σ c F k).trans (le_of_eq ?_)
    have := Real.mul_self_sqrt (sobWeight_nonneg σ k)
    simp only [hA, hB]
    calc sobWeight σ k * ‖c k‖ * ‖F k‖
        = (Real.sqrt (sobWeight σ k) * Real.sqrt (sobWeight σ k)) * ‖c k‖ * ‖F k‖ := by rw [this]
      _ = _ := by ring
  have hn : Summable fun k => ‖sobWeight σ k * (inner ℂ (c k) (F k)).re‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hp.1
  calc |pair σ c F| = ‖∑' k, sobWeight σ k * (inner ℂ (c k) (F k)).re‖ := rfl
    _ ≤ ∑' k, ‖sobWeight σ k * (inner ℂ (c k) (F k)).re‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k, A k * B k := hn.tsum_le_tsum hle hp.1
    _ ≤ _ := hp.2

/-! ### D. The tame native differential -/

variable {ε r τ : ℝ} {F h : Field}

/-- **The native differential tested at weight one**: `|D₁(F; h)| ≤ 24 c₄ a_F² ‖h‖₁`, the tested
force of Bodies 15, 45, with no phase and no pointwise bound on `h`. -/
theorem cubicD_tame_one (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) (hF : MZ 1 F) (hh : MZ 1 h) :
    |cubicD 1 ε r τ F h| ≤ 24 * c4 * hnorm 1 h * hnorm 1 F ^ 2 := by
  have hG : MZ 1 (PiF h) := hh.PiF'
  have hm := corrM_gain ε r τ hε
  have hc := c4_pos
  set a := hnorm 1 F with ha
  set g := hnorm 1 (PiF h) with hg
  have ha0 : 0 ≤ a := hnorm_nonneg _ _
  have hg0 : 0 ≤ g := hnorm_nonneg _ _
  have hgh : g ≤ hnorm 1 h := hnorm_PiF_le hh.inH
  obtain ⟨i1, b1⟩ := hnorm_one_gain_le hm hG hF
  obtain ⟨i2, b2⟩ := hnorm_one_gain_le hm hF hG
  obtain ⟨i3, b3⟩ := hnorm_one_gain_le hm hF hF
  have t1 := abs_pair_symm_le hF.inH i1
  have t2 := abs_pair_symm_le hF.inH i2
  have t3 := abs_pair_symm_le hG.inH i3
  unfold cubicD corr
  rw [Nat.cast_one]
  refine (abs_add_three _ _ _).trans ?_
  have m1 := mul_le_mul_of_nonneg_left b1 ha0
  have m2 := mul_le_mul_of_nonneg_left b2 ha0
  have m3 := mul_le_mul_of_nonneg_left b3 hg0
  have h4 : 24 * c4 * g * a ^ 2 ≤ 24 * c4 * hnorm 1 h * a ^ 2 := by gcongr
  nlinarith only [t1, t2, t3, m1, m2, m3, h4]

/-- **The native differential tested at weight two** (Body 16 (N)):
`|D₂(F; h)| ≤ 48 c₄ a_F c_F ‖h‖₁`, for a genuine `H¹` direction. -/
theorem cubicD_tame_two (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) (hF : MZ 3 F) (hh : MZ 1 h) :
    |cubicD 2 ε r τ F h| ≤ 48 * c4 * hnorm 1 h * (hnorm 1 F * hnorm 3 F) := by
  have hG : MZ 1 (PiF h) := hh.PiF'
  have hF1 : MZ 1 F := hF.mono' (by norm_num)
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  have hm := corrM_gain ε r τ hε
  have hc := c4_pos
  set a := hnorm 1 F with ha
  set b := hnorm 2 F with hb
  set d := hnorm 3 F with hd
  set g := hnorm 1 (PiF h) with hg
  have ha0 : 0 ≤ a := hnorm_nonneg _ _
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have hd0 : 0 ≤ d := hnorm_nonneg _ _
  have hg0 : 0 ≤ g := hnorm_nonneg _ _
  have hgh : g ≤ hnorm 1 h := hnorm_PiF_le hh.inH
  have hF3 : InH (2 + 1) F := by
    rw [show (2 : ℝ) + 1 = 3 by norm_num]
    exact hF.inH
  have hX : ∀ {X : Field}, InH 1 X → |pair 2 F X| ≤ d * hnorm 1 X := fun {X} hX => by
    have hX' : InH (2 - 1) X := by
      rw [show (2 : ℝ) - 1 = 1 by norm_num]
      exact hX
    have := (pair_le hF3 hX').2
    rwa [show (2 : ℝ) + 1 = 3 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num] at this
  obtain ⟨i1, b1⟩ := hnorm_one_gain_le hm hG hF1
  obtain ⟨i2, b2⟩ := hnorm_one_gain_le hm hF1 hG
  obtain ⟨i3, b3⟩ := hnorm_three_gain_le hm hF2 hF2
  have t1 := hX i1
  have t2 := hX i2
  have t3 : |pair 2 (PiF h) (Qm (corrM ε r τ) F F)| ≤ hnorm 3 (Qm (corrM ε r τ) F F) * g := by
    rw [pair_comm']
    have hI : InH (2 + 1) (Qm (corrM ε r τ) F F) := by
      rw [show (2 : ℝ) + 1 = 3 by norm_num]
      exact i3
    have hG' : InH (2 - 1) (PiF h) := by
      rw [show (2 : ℝ) - 1 = 1 by norm_num]
      exact hG.inH
    have := (pair_le hI hG').2
    rwa [show (2 : ℝ) + 1 = 3 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num] at this
  have hw : wiener F ≤ c4 * b := wiener_le hF2
  have hbs : b ^ 2 ≤ a * d := by
    have := hnorm_sq_le_mul (s := 2) (f := F) hF3
    rwa [show (2 : ℝ) - 1 = 1 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num] at this
  have h3 : hnorm 3 (Qm (corrM ε r τ) F F) ≤ 32 * c4 * (a * d) := by
    refine b3.trans ?_
    have h4 : b * wiener F ≤ b * (c4 * b) := mul_le_mul_of_nonneg_left hw hb0
    have h5 : c4 * b ^ 2 ≤ c4 * (a * d) := mul_le_mul_of_nonneg_left hbs hc.le
    nlinarith only [h4, h5]
  unfold cubicD corr
  rw [Nat.cast_ofNat]
  refine (abs_add_three _ _ _).trans ?_
  have m1 := mul_le_mul_of_nonneg_left b1 hd0
  have m2 := mul_le_mul_of_nonneg_left b2 hd0
  have m3 := mul_le_mul_of_nonneg_right h3 hg0
  have h4 : 48 * c4 * g * (a * d) ≤ 48 * c4 * hnorm 1 h * (a * d) := by
    have : 0 ≤ a * d := by positivity
    gcongr
  nlinarith only [t1, t2, t3, m1, m2, m3, h4]

end OVNS.Quant.Metric

end
