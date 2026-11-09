import OddViscousNS.Lattice

/-! # Discrete Young and product inequalities on `ℤ³` (`Lemma lem:product`) -/

noncomputable section
namespace OVNS

/-- Real convolution on the lattice. -/
def convR (a b : Mode → ℝ) (k : Mode) : ℝ := ∑' p, a p * b (k - p)

variable {a b : Mode → ℝ}

/-- Cauchy-Schwarz for nonnegative `ℓ²` sequences, with Euclidean exponents. -/
private lemma cauchy_schwarz_tsum {f g : Mode → ℝ} (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfs : Summable fun i => f i ^ 2) (hgs : Summable fun i => g i ^ 2) :
    Summable (fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2) := by
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    hf hg (by simpa only [Real.rpow_two] using hfs) (by simpa only [Real.rpow_two] using hgs)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h

/-- Minkowski in `ℓ²` for nonnegative sequences, with Euclidean exponents. -/
private lemma minkowski_tsum {f g : Mode → ℝ} (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfs : Summable fun i => f i ^ 2) (hgs : Summable fun i => g i ^ 2) :
    Summable (fun i => (f i + g i) ^ 2) ∧
      Real.sqrt (∑' i, (f i + g i) ^ 2) ≤
        Real.sqrt (∑' i, f i ^ 2) + Real.sqrt (∑' i, g i ^ 2) := by
  have h := Real.Lp_add_le_tsum_of_nonneg (p := 2) one_le_two
    hf hg (by simpa only [Real.rpow_two] using hfs) (by simpa only [Real.rpow_two] using hgs)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h

/-- The shear `(k, p) ↦ (p, k - p)` of the lattice square. -/
private def shear : Mode × Mode ≃ Mode × Mode where
  toFun z := (z.2, z.1 - z.2)
  invFun z := (z.1 + z.2, z.1)
  left_inv z := by simp
  right_inv z := by simp

/-- Tonelli for a convolution of two nonnegative summable sequences. -/
private lemma tonelli_conv {a c : Mode → ℝ} (ha0 : ∀ k, 0 ≤ a k) (hc0 : ∀ k, 0 ≤ c k)
    (ha : Summable a) (hc : Summable c) :
    Summable (fun k => ∑' p, a p * c (k - p)) ∧
      ∑' k, ∑' p, a p * c (k - p) = (∑' k, a k) * ∑' k, c k := by
  have hG : Summable fun z : Mode × Mode => a z.1 * c z.2 := ha.mul_of_nonneg hc ha0 hc0
  have hF : Summable fun z : Mode × Mode => a z.2 * c (z.1 - z.2) :=
    shear.summable_iff.2 hG
  refine ⟨hF.prod, ?_⟩
  rw [ha.tsum_mul_tsum hc hG, ← shear.tsum_eq (fun z : Mode × Mode => a z.1 * c z.2)]
  exact (hF.tsum_prod).symm

/-- Young `ℓ¹ * ℓ² ⊂ ℓ²`. -/
theorem young_l1_l2 (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k) (ha : Summable a)
    (hb : Summable fun k => b k ^ 2) :
    (∀ k, Summable fun p => a p * b (k - p)) ∧ Summable (fun k => convR a b k ^ 2) ∧
      ∑' k, convR a b k ^ 2 ≤ (∑' k, a k) ^ 2 * ∑' k, b k ^ 2 := by
  have hA0 : 0 ≤ ∑' k, a k := tsum_nonneg ha0
  have hS0 : 0 ≤ ∑' k, b k ^ 2 := tsum_nonneg fun k => sq_nonneg _
  have hbd : ∀ q, b q ^ 2 ≤ ∑' k, b k ^ 2 := fun q =>
    hb.le_tsum q fun j _ => sq_nonneg _
  have hT : ∀ k, Summable fun p => a p * b (k - p) ^ 2 := fun k =>
    Summable.of_nonneg_of_le (fun p => mul_nonneg (ha0 p) (sq_nonneg _))
      (fun p => mul_le_mul_of_nonneg_left (hbd _) (ha0 p)) (ha.mul_right _)
  have hcs : ∀ k, Summable (fun p => a p * b (k - p)) ∧
      convR a b k ^ 2 ≤ (∑' k, a k) * ∑' p, a p * b (k - p) ^ 2 := by
    intro k
    have hs : ∀ p, Real.sqrt (a p) ^ 2 = a p := fun p => Real.sq_sqrt (ha0 p)
    have h := cauchy_schwarz_tsum (f := fun p => Real.sqrt (a p))
      (g := fun p => Real.sqrt (a p) * b (k - p)) (fun p => Real.sqrt_nonneg _)
      (fun p => mul_nonneg (Real.sqrt_nonneg _) (hb0 _))
      (by simpa only [hs] using ha) (by simpa only [mul_pow, hs] using hT k)
    have he : ∀ p, Real.sqrt (a p) * (Real.sqrt (a p) * b (k - p)) = a p * b (k - p) := by
      intro p
      rw [← mul_assoc, Real.mul_self_sqrt (ha0 p)]
    simp only [he, mul_pow, hs] at h
    refine ⟨h.1, ?_⟩
    have hc0 : 0 ≤ convR a b k := tsum_nonneg fun p => mul_nonneg (ha0 p) (hb0 _)
    have hT0 : 0 ≤ ∑' p, a p * b (k - p) ^ 2 :=
      tsum_nonneg fun p => mul_nonneg (ha0 p) (sq_nonneg _)
    calc convR a b k ^ 2
        ≤ (Real.sqrt (∑' k, a k) * Real.sqrt (∑' p, a p * b (k - p) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ hc0 h.2 2
      _ = (∑' k, a k) * ∑' p, a p * b (k - p) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hT0]
  obtain ⟨hTs, hTe⟩ := tonelli_conv (c := fun k => b k ^ 2) ha0 (fun k => sq_nonneg _) ha hb
  have hsum : Summable fun k => (∑' k, a k) * ∑' p, a p * b (k - p) ^ 2 := hTs.mul_left _
  refine ⟨fun k => (hcs k).1, Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (fun k => (hcs k).2) hsum, ?_⟩
  calc ∑' k, convR a b k ^ 2
      ≤ ∑' k, (∑' k, a k) * ∑' p, a p * b (k - p) ^ 2 :=
        (Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => (hcs k).2) hsum).tsum_le_tsum
          (fun k => (hcs k).2) hsum
    _ = (∑' k, a k) ^ 2 * ∑' k, b k ^ 2 := by
        rw [tsum_mul_left, hTe, sq, mul_assoc]

/-- Pointwise commutation of the convolution. -/
lemma convR_comm (a b : Mode → ℝ) (k : Mode) : convR a b k = convR b a k := by
  unfold convR
  rw [← (Equiv.subLeft k).tsum_eq]
  refine tsum_congr fun p => ?_
  simp [mul_comm]

/-- Pointwise bound on a coefficient: `∑ₚ a_p b_{k-p} ≤ ‖a‖₂ ‖b‖₂`. -/
lemma convR_le_of_l2 (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k)
    (ha : Summable fun k => a k ^ 2) (hb : Summable fun k => b k ^ 2) (k : Mode) :
    Summable (fun p => a p * b (k - p)) ∧
      convR a b k ≤ Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, b k ^ 2) := by
  have hb' : Summable fun p => b (k - p) ^ 2 :=
    (Equiv.subLeft k).summable_iff.2 hb
  have ht : ∑' p, b (k - p) ^ 2 = ∑' p, b p ^ 2 :=
    (Equiv.subLeft k).tsum_eq fun p => b p ^ 2
  have h := cauchy_schwarz_tsum ha0 (fun p => hb0 (k - p)) ha hb'
  rw [ht] at h
  exact h

/-- `|k|^σ ≤ 2^{σ-1}(|p|^σ + |q|^σ)` for `σ ≥ 1`, `k = p + q`. -/
lemma rpow_absk_add_le {σ : ℝ} (hσ : 1 ≤ σ) (p q : Mode) :
    absk (p + q) ^ σ ≤ 2 ^ (σ - 1) * (absk p ^ σ + absk q ^ σ) := by
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow ⟨absk p, absk_nonneg p⟩ ⟨absk q, absk_nonneg q⟩ hσ
  have h' : (absk p + absk q) ^ σ ≤ 2 ^ (σ - 1) * (absk p ^ σ + absk q ^ σ) := by
    exact_mod_cast h
  exact (Real.rpow_le_rpow (absk_nonneg _) (absk_add_le p q) (by linarith)).trans h'

/-- The square of the weighted coefficient is the summand of the homogeneous Sobolev norm. -/
private lemma weight_sq {σ : ℝ} {x : Field} (hx : MZ σ x) (k : Mode) :
    (absk k ^ σ * ‖x k‖) ^ 2 = sobWeight σ k * ‖x k‖ ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    simp [sobWeight, hx.mean]
  · have : (absk k ^ σ) ^ 2 = absk k ^ (2 * σ) := by
      rw [mul_comm, Real.rpow_mul (absk_nonneg k), Real.rpow_two]
    have hs : sobWeight σ k = absk k ^ (2 * σ) := by simp [sobWeight, hk]
    rw [hs, mul_pow, this]

/-- Young with the roles of the two factors swapped: `ℓ² * ℓ¹ ⊂ ℓ²`. -/
private lemma young_l2_l1 (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k)
    (ha : Summable fun k => a k ^ 2) (hb : Summable b) :
    (∀ k, Summable fun p => a p * b (k - p)) ∧ Summable (fun k => convR a b k ^ 2) ∧
      ∑' k, convR a b k ^ 2 ≤ (∑' k, b k) ^ 2 * ∑' k, a k ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := young_l1_l2 hb0 ha0 hb ha
  have hc : convR a b = convR b a := funext (convR_comm a b)
  refine ⟨fun k => ?_, by rwa [hc], by rwa [hc]⟩
  have := (Equiv.subLeft k).summable_iff.2 (h1 k)
  refine this.congr fun p => ?_
  simp [mul_comm]

/-- `√(∑ (conv)²) ≤ ‖b‖₁ ‖a‖₂` from the squared form of Young. -/
private lemma sqrt_young_le {c a : Mode → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∑' k, c k ^ 2 ≤ B ^ 2 * ∑' k, a k ^ 2) :
    Real.sqrt (∑' k, c k ^ 2) ≤ B * Real.sqrt (∑' k, a k ^ 2) := by
  calc Real.sqrt (∑' k, c k ^ 2) ≤ Real.sqrt (B ^ 2 * ∑' k, a k ^ 2) := Real.sqrt_le_sqrt h
    _ = B * Real.sqrt (∑' k, a k ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]

/-- The termwise convexity split behind the weighted product estimate. -/
private lemma weighted_conv_le {σ : ℝ} (hσ : 1 ≤ σ) {A B : Mode → ℝ} (hA0 : ∀ k, 0 ≤ A k)
    (hB0 : ∀ k, 0 ≤ B k)
    (hAB : ∀ k, Summable fun p => A p * B (k - p))
    (hXB : ∀ k, Summable fun p => (absk p ^ σ * A p) * B (k - p))
    (hAY : ∀ k, Summable fun p => A p * (absk (k - p) ^ σ * B (k - p))) (k : Mode) :
    absk k ^ σ * convR A B k ≤
      2 ^ (σ - 1) * (convR (fun p => absk p ^ σ * A p) B k +
        convR A (fun p => absk p ^ σ * B p) k) := by
  unfold convR
  rw [← (hXB k).tsum_add (hAY k), ← tsum_mul_left, ← tsum_mul_left]
  refine (((hAB k).mul_left _).tsum_le_tsum (fun p => ?_) ?_)
  · have hw := rpow_absk_add_le hσ p (k - p)
    rw [add_sub_cancel] at hw
    have hn : 0 ≤ A p * B (k - p) := mul_nonneg (hA0 p) (hB0 _)
    calc absk k ^ σ * (A p * B (k - p))
        ≤ 2 ^ (σ - 1) * (absk p ^ σ + absk (k - p) ^ σ) * (A p * B (k - p)) :=
          mul_le_mul_of_nonneg_right hw hn
      _ = _ := by ring
  · exact ((hXB k).add (hAY k)).mul_left _

/-- The weighted product estimate, in the form used by the majorants: for `σ ≥ 1`,
`‖ |k|^σ (x*y) ‖₂ ≤ 2^{σ-1}(‖x‖₁ ‖|k|^σ y‖₂ + ‖|k|^σ x‖₂ ‖y‖₁)`. -/
theorem product_estimate {σ : ℝ} (hσ : 1 ≤ σ) {x y : Field} (hx : MZ σ x) (hy : MZ σ y)
    (hx1 : Summable fun k => ‖x k‖) (hy1 : Summable fun k => ‖y k‖) :
    Summable (fun k => absk k ^ (2 * σ) * (∑' p, ‖x p‖ * ‖y (k - p)‖) ^ 2) ∧
    Real.sqrt (∑' k, absk k ^ (2 * σ) * (∑' p, ‖x p‖ * ‖y (k - p)‖) ^ 2) ≤
      2 ^ (σ - 1) * (wiener x * hnorm σ y + hnorm σ x * wiener y) := by
  set A : Mode → ℝ := fun k => ‖x k‖ with hA
  set B : Mode → ℝ := fun k => ‖y k‖ with hB
  set X : Mode → ℝ := fun k => absk k ^ σ * A k with hX
  set Y : Mode → ℝ := fun k => absk k ^ σ * B k with hY
  have hA0 : ∀ k, 0 ≤ A k := fun k => norm_nonneg _
  have hB0 : ∀ k, 0 ≤ B k := fun k => norm_nonneg _
  have hX0 : ∀ k, 0 ≤ X k := fun k =>
    mul_nonneg (Real.rpow_nonneg (absk_nonneg k) σ) (hA0 k)
  have hY0 : ∀ k, 0 ≤ Y k := fun k =>
    mul_nonneg (Real.rpow_nonneg (absk_nonneg k) σ) (hB0 k)
  have hXs : (fun k => X k ^ 2) = fun k => sobWeight σ k * ‖x k‖ ^ 2 :=
    funext (weight_sq hx)
  have hYs : (fun k => Y k ^ 2) = fun k => sobWeight σ k * ‖y k‖ ^ 2 :=
    funext (weight_sq hy)
  have hX2 : Summable fun k => X k ^ 2 := hXs ▸ hx.inH
  have hY2 : Summable fun k => Y k ^ 2 := hYs ▸ hy.inH
  have hNX : Real.sqrt (∑' k, X k ^ 2) = hnorm σ x := by rw [hXs, hnorm]
  have hNY : Real.sqrt (∑' k, Y k ^ 2) = hnorm σ y := by rw [hYs, hnorm]
  obtain ⟨hU1, hU2, hU3⟩ := young_l2_l1 hX0 hB0 hX2 hy1
  obtain ⟨hV1, hV2, hV3⟩ := young_l1_l2 hA0 hY0 hx1 hY2
  have hAB : ∀ k, Summable fun p => A p * B (k - p) := fun k =>
    Summable.of_nonneg_of_le (fun p => mul_nonneg (hA0 _) (hB0 _))
      (fun p => mul_le_mul_of_nonneg_left (hy1.le_tsum _ fun j _ => hB0 j) (hA0 p))
      (hx1.mul_right (∑' k, B k))
  have hpt := weighted_conv_le hσ hA0 hB0 hAB hU1 hV1
  have hU0 : ∀ k, 0 ≤ convR X B k := fun k =>
    tsum_nonneg fun p => mul_nonneg (hX0 p) (hB0 _)
  have hV0 : ∀ k, 0 ≤ convR A Y k := fun k =>
    tsum_nonneg fun p => mul_nonneg (hA0 p) (hY0 _)
  have hC0 : ∀ k, 0 ≤ convR A B k := fun k =>
    tsum_nonneg fun p => mul_nonneg (hA0 p) (hB0 _)
  have hc0 : (0 : ℝ) ≤ 2 ^ (σ - 1) := by positivity
  have hZ : ∀ k, absk k ^ (2 * σ) * convR A B k ^ 2 ≤
      (2 ^ (σ - 1)) ^ 2 * (convR X B k + convR A Y k) ^ 2 := by
    intro k
    have h2 : absk k ^ (2 * σ) = (absk k ^ σ) ^ 2 := by
      rw [mul_comm, Real.rpow_mul (absk_nonneg k), Real.rpow_two]
    rw [h2, ← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀
      (mul_nonneg (Real.rpow_nonneg (absk_nonneg k) σ) (hC0 k)) (hpt k) 2
  obtain ⟨hM1, hM2⟩ := minkowski_tsum hU0 hV0 hU2 hV2
  have hsum : Summable fun k => (2 ^ (σ - 1)) ^ 2 * (convR X B k + convR A Y k) ^ 2 :=
    hM1.mul_left _
  have hL0 : ∀ k, 0 ≤ absk k ^ (2 * σ) * convR A B k ^ 2 := fun k =>
    mul_nonneg (Real.rpow_nonneg (absk_nonneg k) _) (sq_nonneg _)
  have hLs := Summable.of_nonneg_of_le hL0 hZ hsum
  refine ⟨hLs, ?_⟩
  have hb1 := sqrt_young_le (tsum_nonneg hB0) hU3
  have hb2 := sqrt_young_le (tsum_nonneg hA0) hV3
  rw [hNX] at hb1
  rw [hNY] at hb2
  have hstep : Real.sqrt (∑' k, absk k ^ (2 * σ) * convR A B k ^ 2) ≤
      2 ^ (σ - 1) * Real.sqrt (∑' k, (convR X B k + convR A Y k) ^ 2) := by
    calc Real.sqrt (∑' k, absk k ^ (2 * σ) * convR A B k ^ 2)
        ≤ Real.sqrt (∑' k, (2 ^ (σ - 1)) ^ 2 * (convR X B k + convR A Y k) ^ 2) :=
          Real.sqrt_le_sqrt (hLs.tsum_le_tsum hZ hsum)
      _ = 2 ^ (σ - 1) * Real.sqrt (∑' k, (convR X B k + convR A Y k) ^ 2) := by
          rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc0]
  have hfin : Real.sqrt (∑' k, (convR X B k + convR A Y k) ^ 2) ≤
      wiener x * hnorm σ y + hnorm σ x * wiener y := by
    have hw1 : (∑' k, B k) * hnorm σ x = hnorm σ x * wiener y := mul_comm _ _
    have hw2 : (∑' k, A k) * hnorm σ y = wiener x * hnorm σ y := rfl
    linarith
  exact hstep.trans (mul_le_mul_of_nonneg_left hfin hc0)

end OVNS
