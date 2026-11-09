import OddViscousNS.Quant.Energy.Slow.Equation

/-!
# J4: the fast source of the slow budget, by sectors

The fixed-force budget `budgetPoly` (`Energy/Slow/Equation.lean`) bounds the nonlinearity of
`F' = −AF − Π_F Q(y,y)` by `‖Q(y,y)‖₁ ≲ 𝒜(y)‖y‖₂`.  At the joint caps this is `W_S B_S ≍ R^{7/2}`,
which is the slow–slow interaction, and it does not occur in the fast equation at all: a slow–slow
triad has a slow output, `Π_F Q(S,S) = 0`.  With `w = y(u)`, `S = Π_S w`, `G = Π_F w`, the true size
is `Ξ(w) = 𝒜(S)‖G‖₂ + ‖S‖₂𝒜(G) + 𝒜(G)‖G‖₂` (`fastXi`), the bracket `Θ_pt` of the TeX
(`quantitative_energies.tex`, "the full physical product bound on `F_τ + AF`"; Body 13).

* `hnorm_PiF_Qphase_le`: `‖Π_F Q(w,w)‖₁ ≤ 8 Ξ(w)`;
* `norm_PiF_Qphase_le`, `fastMaj`: the same as a pointwise majorant with one lost derivative;
* `hnorm_one_kinN_fastRHS_J`: `‖N(F',F)‖₁ ≤ (c₄‖F‖₂/q)(4‖F‖₃ + 28 Ξ)`, in place of
  `hnorm_one_kinN_fastRHS_le`, whose second term is `26 𝒜(y)‖y‖₂`;
* `fast_dissipation_J`: `∫ ‖F‖₃² ≤ ‖F s‖₂² + ∫ D²` for `‖Π_F Q(y,y)‖₁ ≤ D(u)`, in place of
  `fast_dissipation_le`, with a time-dependent `D` (the `L²_t` budget uses `∫ b_S² ≤ J_S`);
* `hnorm_one_corrRes_J`: the pointwise `H¹` bound of the residual, in place of
  `hnorm_one_corrRes_le`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace OVNS.Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### Sequences -/

/-- Minkowski in `ℓ²` for nonnegative sequences. -/
private lemma minkowski {f g : Mode → ℝ} (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfs : Summable fun i => f i ^ 2) (hgs : Summable fun i => g i ^ 2) :
    Summable (fun i => (f i + g i) ^ 2) ∧
      Real.sqrt (∑' i, (f i + g i) ^ 2) ≤
        Real.sqrt (∑' i, f i ^ 2) + Real.sqrt (∑' i, g i ^ 2) := by
  have h := Real.Lp_add_le_tsum_of_nonneg (p := 2) one_le_two
    hf hg (by simpa only [Real.rpow_two] using hfs) (by simpa only [Real.rpow_two] using hgs)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h

/-- The shear `(k, p) ↦ (p, k − p)` of the lattice square. -/
private def shearJ : Mode × Mode ≃ Mode × Mode where
  toFun z := (z.2, z.1 - z.2)
  invFun z := (z.1 + z.2, z.1)
  left_inv z := by simp
  right_inv z := by simp

/-- Young `ℓ¹ * ℓ¹ ⊂ ℓ¹`. -/
private lemma tonelli {a c : Mode → ℝ} (ha0 : ∀ k, 0 ≤ a k) (hc0 : ∀ k, 0 ≤ c k)
    (ha : Summable a) (hc : Summable c) :
    Summable (fun k => ∑' p, a p * c (k - p)) ∧
      ∑' k, ∑' p, a p * c (k - p) = (∑' k, a k) * ∑' k, c k := by
  have hG : Summable fun z : Mode × Mode => a z.1 * c z.2 := ha.mul_of_nonneg hc ha0 hc0
  have hF : Summable fun z : Mode × Mode => a z.2 * c (z.1 - z.2) :=
    shearJ.summable_iff.2 hG
  refine ⟨hF.prod, ?_⟩
  rw [ha.tsum_mul_tsum hc hG, ← shearJ.tsum_eq (fun z : Mode × Mode => a z.1 * c z.2)]
  exact (hF.tsum_prod).symm

/-- `|k|^{2·2} = |k|⁴`, as a square of `|k|²`. -/
private lemma absk_rpow_four (k : Mode) : absk k ^ ((2 : ℝ) * 2) = absSq k ^ 2 := by
  rw [show ((2 : ℝ) * 2) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← absk_sq]
  ring

/-! ### The sectors of the convection -/

/-- `Q(w,w) = Q(S,S) + 2 Q(S,G) + Q(G,G)`, `S = Π_S w`, `G = Π_F w`. -/
lemma Qphase_sectors (τ : ℝ) {w : Field} (hw : Adm 2 w) :
    Qphase τ w w = Qphase τ (PiS w) (PiS w) + Qphase τ (PiS w) (PiF w) +
      Qphase τ (PiS w) (PiF w) + Qphase τ (PiF w) (PiF w) := by
  have hS : Adm 2 (PiS w) := hw.PiS
  have hF : Adm 2 (PiF w) := hw.PiF
  have hM := majorized_Qphase τ
  have hw' : w = PiS w + PiF w := (PiS_add_PiF w).symm
  have hsum : MZ 2 (PiS w + PiF w) := by rw [← hw']; exact hw.mz
  have hcomm : Qphase τ (PiF w) (PiS w) = Qphase τ (PiS w) (PiF w) :=
    Qm_comm_of_symm (phaseM_symm τ) hF.mz hS.mz
  conv_lhs => rw [hw']
  rw [hM.add_left 0 _ _ _ hS.mz hF.mz hsum, hM.add_right 0 _ _ _ hS.mz hS.mz hF.mz,
    hM.add_right 0 _ _ _ hF.mz hS.mz hF.mz, hcomm]
  abel

/-- **The fast output has no slow–slow term.** -/
lemma PiF_Qphase_eq (τ : ℝ) {w : Field} (hw : Adm 2 w) :
    PiF (Qphase τ w w) = Qphase τ (PiS w) (PiF w) + Qphase τ (PiS w) (PiF w) +
      PiF (Qphase τ (PiF w) (PiF w)) := by
  funext k
  rw [Qphase_sectors τ hw]
  by_cases hk : k 2 = 0
  · simp only [Pi.add_apply, PiF_apply_slow _ hk,
      Qphase_slow_fast τ (PiS_PiS_eq w) (PiF_PiF_eq w) hk]
    simp
  · simp only [Pi.add_apply, PiF_apply_fast _ hk]
    rw [Qphase_slow_slow τ (PiS_PiS_eq w) hk]
    abel

/-- **The size of the fast output**: `Ξ(w) = 𝒜(S)‖G‖₂ + ‖S‖₂𝒜(G) + 𝒜(G)‖G‖₂`. -/
def fastXi (w : Field) : ℝ :=
  wiener (PiS w) * hnorm 2 (PiF w) + hnorm 2 (PiS w) * wiener (PiF w) +
    wiener (PiF w) * hnorm 2 (PiF w)

lemma fastXi_nonneg (w : Field) : 0 ≤ fastXi w := by
  have := wiener_nonneg (PiS w)
  have := wiener_nonneg (PiF w)
  have := hnorm_nonneg 2 (PiS w)
  have := hnorm_nonneg 2 (PiF w)
  unfold fastXi
  positivity

/-- `‖Π_F Q(w,w)‖₁ ≤ 8 Ξ(w)`. -/
theorem hnorm_PiF_Qphase_le (τ : ℝ) {w : Field} (hw : Adm 2 w) :
    InH 1 (PiF (Qphase τ w w)) ∧ hnorm 1 (PiF (Qphase τ w w)) ≤ 8 * fastXi w := by
  have hS : Adm 2 (PiS w) := hw.PiS
  have hG : Adm 2 (PiF w) := hw.PiF
  have q1 : InH 1 (Qphase τ (PiS w) (PiF w)) ∧ hnorm 1 (Qphase τ (PiS w) (PiF w)) ≤
      4 * (wiener (PiS w) * hnorm 2 (PiF w) + hnorm 2 (PiS w) * wiener (PiF w)) :=
    hnorm_Qm_one_bound (phaseM_bdd τ) hS.mz hG.mz
  have q2 : InH 1 (Qphase τ (PiF w) (PiF w)) ∧ hnorm 1 (Qphase τ (PiF w) (PiF w)) ≤
      4 * (wiener (PiF w) * hnorm 2 (PiF w) + hnorm 2 (PiF w) * wiener (PiF w)) :=
    hnorm_Qm_one_bound (phaseM_bdd τ) hG.mz hG.mz
  rw [PiF_Qphase_eq τ hw]
  have h3 := hnorm_PiF_le q2.1
  have i12 := q1.1.add q1.1
  refine ⟨i12.add q2.1.PiF, ?_⟩
  have t1 := hnorm_add_le i12 q2.1.PiF
  have t2 := hnorm_add_le q1.1 q1.1
  unfold fastXi
  linarith [q1.2, q2.2, mul_comm (wiener (PiF w)) (hnorm 2 (PiF w))]

/-! ### The majorant with one lost derivative -/

/-- The convolution majorant `C_k = 2 (|S| * |G|)_k + (|G| * |G|)_k` of the fast output. -/
def fastMaj (w : Field) (k : Mode) : ℝ :=
  2 * (∑' q, ‖PiS w q‖ * ‖PiF w (k - q)‖) + ∑' q, ‖PiF w q‖ * ‖PiF w (k - q)‖

lemma fastMaj_nonneg (w : Field) (k : Mode) : 0 ≤ fastMaj w k :=
  add_nonneg (mul_nonneg (by norm_num)
    (tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- `‖Π_F Q(w,w)_p‖ ≤ |p| · 2 C_p`. -/
lemma norm_PiF_Qphase_le (τ : ℝ) {w : Field} (hw : Adm 2 w) (p : Mode) :
    ‖PiF (Qphase τ w w) p‖ ≤ absk p * (2 * fastMaj w p) := by
  have hS : Adm 2 (PiS w) := hw.PiS
  have hG : Adm 2 (PiF w) := hw.PiF
  have h1 : ‖Qphase τ (PiS w) (PiF w) p‖ ≤
      2 * absk p * ∑' q, ‖PiS w q‖ * ‖PiF w (p - q)‖ :=
    norm_Qm_le₂ (phaseM_bdd τ) hS.mz hG.mz p
  have h2 : ‖Qphase τ (PiF w) (PiF w) p‖ ≤
      2 * absk p * ∑' q, ‖PiF w q‖ * ‖PiF w (p - q)‖ :=
    norm_Qm_le₂ (phaseM_bdd τ) hG.mz hG.mz p
  have h3 : ‖PiF (Qphase τ (PiF w) (PiF w)) p‖ ≤ ‖Qphase τ (PiF w) (PiF w) p‖ := by
    by_cases hp : p 2 = 0
    · rw [PiF_apply_slow _ hp, norm_zero]
      exact norm_nonneg _
    · rw [PiF_apply_fast _ hp]
  rw [PiF_Qphase_eq τ hw]
  simp only [Pi.add_apply]
  have t1 := norm_add_le (Qphase τ (PiS w) (PiF w) p + Qphase τ (PiS w) (PiF w) p)
    (PiF (Qphase τ (PiF w) (PiF w)) p)
  have t2 := norm_add_le (Qphase τ (PiS w) (PiF w) p) (Qphase τ (PiS w) (PiF w) p)
  have e : absk p * (2 * fastMaj w p) =
      2 * (2 * absk p * ∑' q, ‖PiS w q‖ * ‖PiF w (p - q)‖) +
        2 * absk p * ∑' q, ‖PiF w q‖ * ‖PiF w (p - q)‖ := by
    unfold fastMaj
    ring
  rw [e]
  linarith

/-- `C ∈ ℓ¹`, with `∑ C ≤ 2 c₄ Ξ`. -/
lemma fastMaj_sum {w : Field} (hw : Adm 2 w) :
    Summable (fastMaj w) ∧ ∑' k, fastMaj w k ≤ 2 * c4 * fastXi w := by
  have hS : Adm 2 (PiS w) := hw.PiS
  have hG : Adm 2 (PiF w) := hw.PiF
  have hS1 : Summable fun k => ‖PiS w k‖ := summable_wiener hS.inH
  have hG1 : Summable fun k => ‖PiF w k‖ := summable_wiener hG.inH
  obtain ⟨s1, e1⟩ := tonelli (a := fun k => ‖PiS w k‖) (c := fun k => ‖PiF w k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hS1 hG1
  obtain ⟨s2, e2⟩ := tonelli (a := fun k => ‖PiF w k‖) (c := fun k => ‖PiF w k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hG1 hG1
  have hs : Summable (fastMaj w) := (s1.mul_left 2).add s2
  refine ⟨hs, ?_⟩
  have e : ∑' k, fastMaj w k = 2 * (wiener (PiS w) * wiener (PiF w)) +
      wiener (PiF w) * wiener (PiF w) := by
    have h := (s1.mul_left 2).tsum_add s2
    rw [tsum_mul_left, e1, e2] at h
    exact h
  rw [e]
  have hw2 := wiener_le hG.mz
  have n1 := wiener_nonneg (PiS w)
  have n2 := wiener_nonneg (PiF w)
  have n3 := hnorm_nonneg 2 (PiS w)
  have n4 := hnorm_nonneg 2 (PiF w)
  have hc := c4_pos
  have p1 : wiener (PiS w) * wiener (PiF w) ≤ wiener (PiS w) * (c4 * hnorm 2 (PiF w)) :=
    mul_le_mul_of_nonneg_left hw2 n1
  have p2 : wiener (PiF w) * wiener (PiF w) ≤ wiener (PiF w) * (c4 * hnorm 2 (PiF w)) :=
    mul_le_mul_of_nonneg_left hw2 n2
  have p3 : 0 ≤ c4 * (hnorm 2 (PiS w) * wiener (PiF w)) := by positivity
  have p4 : 0 ≤ c4 * (wiener (PiF w) * hnorm 2 (PiF w)) := by positivity
  unfold fastXi
  nlinarith

/-- `|·|²C ∈ ℓ²`, with `‖|·|²C‖ ≤ 4 Ξ`. -/
lemma fastMaj_weight {w : Field} (hw : Adm 2 w) :
    Summable (fun k => (absSq k * fastMaj w k) ^ 2) ∧
      Real.sqrt (∑' k, (absSq k * fastMaj w k) ^ 2) ≤ 4 * fastXi w := by
  have hS : Adm 2 (PiS w) := hw.PiS
  have hG : Adm 2 (PiF w) := hw.PiF
  have hS1 : Summable fun k => ‖PiS w k‖ := summable_wiener hS.inH
  have hG1 : Summable fun k => ‖PiF w k‖ := summable_wiener hG.inH
  obtain ⟨hP1, hP2⟩ := product_estimate (σ := 2) (by norm_num) hS.mz hG.mz hS1 hG1
  obtain ⟨hR1, hR2⟩ := product_estimate (σ := 2) (by norm_num) hG.mz hG.mz hG1 hG1
  simp only [absk_rpow_four] at hP1 hP2 hR1 hR2
  have e2 : (2 : ℝ) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  rw [e2] at hP2 hR2
  set A : Mode → ℝ := fun k => 2 * (absSq k * ∑' q, ‖PiS w q‖ * ‖PiF w (k - q)‖) with hA
  set B : Mode → ℝ := fun k => absSq k * ∑' q, ‖PiF w q‖ * ‖PiF w (k - q)‖ with hB
  have hA0 : ∀ k, 0 ≤ A k := fun k => mul_nonneg (by norm_num)
    (mul_nonneg (absSq_nonneg k)
      (tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hB0 : ∀ k, 0 ≤ B k := fun k => mul_nonneg (absSq_nonneg k)
    (tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hAe : ∀ k, A k ^ 2 = 4 * (absSq k ^ 2 * (∑' q, ‖PiS w q‖ * ‖PiF w (k - q)‖) ^ 2) :=
    fun k => by simp only [hA]; ring
  have hBe : ∀ k, B k ^ 2 = absSq k ^ 2 * (∑' q, ‖PiF w q‖ * ‖PiF w (k - q)‖) ^ 2 :=
    fun k => by simp only [hB]; ring
  have hA2 : Summable fun k => A k ^ 2 := by
    simp only [hAe]
    exact hP1.mul_left 4
  have hB2 : Summable fun k => B k ^ 2 := by
    simp only [hBe]
    exact hR1
  obtain ⟨hM1, hM2⟩ := minkowski hA0 hB0 hA2 hB2
  have hsum : ∀ k, absSq k * fastMaj w k = A k + B k := fun k => by
    simp only [hA, hB, fastMaj]
    ring
  simp only [hsum]
  refine ⟨hM1, hM2.trans ?_⟩
  have hAn : Real.sqrt (∑' k, A k ^ 2) ≤
      4 * (wiener (PiS w) * hnorm 2 (PiF w) + hnorm 2 (PiS w) * wiener (PiF w)) := by
    have e : ∑' k, A k ^ 2 = 4 * ∑' k, absSq k ^ 2 * (∑' q, ‖PiS w q‖ * ‖PiF w (k - q)‖) ^ 2 := by
      simp only [hAe]
      exact tsum_mul_left
    rw [e, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    linarith
  have hBn : Real.sqrt (∑' k, B k ^ 2) ≤
      2 * (wiener (PiF w) * hnorm 2 (PiF w) + hnorm 2 (PiF w) * wiener (PiF w)) := by
    simp only [hBe]
    exact hR2
  have e3 := mul_comm (wiener (PiF w)) (hnorm 2 (PiF w))
  unfold fastXi
  linarith

/-! ### The corrector derivative -/

/-- `F' = −AF − Π_F Q(y,y)` loses one derivative over `|·|F + 2 C`. -/
private lemma norm_fastRHS_le_J (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (p : Mode) :
    ‖fastRHS r g y u p‖ ≤ absk p * (absk p * ‖PiF (actual r g y u) p‖ +
      2 * fastMaj (y u) p) := by
  have h1 := norm_PiF_Qphase_le (r * u) (h.sol.adm u hu huT) p
  have h3 : ‖(-(absSq p : ℝ) : ℂ) • PiF (actual r g y u) p‖ =
      absk p * (absk p * ‖PiF (actual r g y u) p‖) := by
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (absSq_nonneg p), ← absk_sq]
    ring
  have h4 : ‖fastRHS r g y u p‖ ≤ ‖(-(absSq p : ℝ) : ℂ) • PiF (actual r g y u) p‖ +
      ‖PiF (Qphase (r * u) (y u) (y u)) p‖ := norm_sub_le _ _
  rw [h3] at h4
  rw [mul_add]
  linarith

/-- **The corrector derivative in `H¹`, by sectors**, at a time with `F ∈ H³`:
`‖N(F',F)‖₁ ≤ (c₄‖F‖₂/q)(4‖F‖₃ + 28 Ξ(y))`. -/
theorem hnorm_one_kinN_fastRHS_J (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (τ : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (PiF (actual r g y u))) :
    InH 1 (kinN r τ (fastRHS r g y u) (PiF (actual r g y u))) ∧
      hnorm 1 (kinN r τ (fastRHS r g y u) (PiF (actual r g y u))) ≤
        c4 * hnorm 2 (PiF (actual r g y u)) / |r| *
          (4 * hnorm 3 (PiF (actual r g y u)) + 28 * fastXi (y u)) := by
  have hrp : 0 < |r| := abs_pos.mpr hr
  have hc := c4_pos
  have hx := actual_adm h hu huT
  have hF := hx.PiF
  have hy := h.sol.adm u hu huT
  set F := PiF (actual r g y u) with hFdef
  have hF3' : MZ 3 F := ⟨hF3, hF.mean⟩
  obtain ⟨hgrad, hgradle⟩ := wiener_grad_le hF3'
  obtain ⟨hC1, hCs⟩ := fastMaj_sum hy
  obtain ⟨hCw, hCn⟩ := fastMaj_weight hy
  set C : Mode → ℝ := fastMaj (y u) with hC
  have hC0 : ∀ k, 0 ≤ C k := fastMaj_nonneg (y u)
  set a : Mode → ℝ := fun k => absSq k * (absk k * ‖F k‖) with ha
  set d : Mode → ℝ := fun k => 2 * (absSq k * C k) with hd
  have ha0 : ∀ k, 0 ≤ a k := fun k =>
    mul_nonneg (absSq_nonneg k) (mul_nonneg (absk_nonneg k) (norm_nonneg _))
  have hd0 : ∀ k, 0 ≤ d k := fun k =>
    mul_nonneg (by norm_num) (mul_nonneg (absSq_nonneg k) (hC0 k))
  have hae : ∀ k, a k ^ 2 = sobWeight 3 k * ‖F k‖ ^ 2 := fun k => by
    have e : sobWeight 3 k = absk k ^ 6 := by
      unfold sobWeight
      split_ifs with hk
      · subst hk
        simp [absk, absSq]
      · rw [show ((2 : ℝ) * 3) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    show (absSq k * (absk k * ‖F k‖)) ^ 2 = _
    rw [e, ← absk_sq]
    ring
  have hde : ∀ k, d k ^ 2 = 4 * (absSq k * C k) ^ 2 := fun k => by
    show (2 * (absSq k * C k)) ^ 2 = _
    ring
  have ha2 : Summable fun k => a k ^ 2 := by
    simp only [hae]
    exact hF3
  have hd2 : Summable fun k => d k ^ 2 := by
    simp only [hde]
    exact hCw.mul_left 4
  obtain ⟨hM1, hM2⟩ := minkowski ha0 hd0 ha2 hd2
  have han : Real.sqrt (∑' k, a k ^ 2) = hnorm 3 F := by
    unfold hnorm
    exact congrArg Real.sqrt (tsum_congr hae)
  have hdn : Real.sqrt (∑' k, d k ^ 2) ≤ 8 * fastXi (y u) := by
    have e : ∑' k, d k ^ 2 = 4 * ∑' k, (absSq k * C k) ^ 2 := by
      simp only [hde]
      exact tsum_mul_left
    rw [e, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    linarith
  -- the majorant
  set B : Mode → ℝ := fun k => absk k * ‖F k‖ + 2 * C k with hBdef
  have hB0 : ∀ k, 0 ≤ B k := fun k =>
    add_nonneg (mul_nonneg (absk_nonneg k) (norm_nonneg _)) (mul_nonneg (by norm_num) (hC0 k))
  have hB1 : Summable B := hgrad.add (hC1.mul_left 2)
  have hBe : ∀ k, absSq k * B k = a k + d k := fun k => by
    simp only [hBdef, ha, hd]
    ring
  have hB2 : Summable fun k => (absSq k * B k) ^ 2 := by
    simp only [hBe]
    exact hM1
  have hBs : ∑' k, B k ≤ c4 * hnorm 3 F + 4 * c4 * fastXi (y u) := by
    have e : ∑' k, B k = ∑' k, absk k * ‖F k‖ + 2 * ∑' k, C k := by
      rw [← tsum_mul_left]
      exact hgrad.tsum_add (hC1.mul_left 2)
    rw [e]
    linarith
  have hBn : Real.sqrt (∑' k, (absSq k * B k) ^ 2) ≤ hnorm 3 F + 8 * fastXi (y u) := by
    simp only [hBe]
    rw [← han]
    exact hM2.trans (add_le_add le_rfl hdn)
  obtain ⟨hI, hle⟩ := hnorm_one_kinN_of_loss_le (τ := τ) hr (f := fastRHS r g y u) (g := F) hB0
    hB1 hB2 (fun p => norm_fastRHS_le_J h hu huT p) (fastRHS_l2 h hu huT).1 hF.mz
  refine ⟨hI, hle.trans ?_⟩
  -- the arithmetic
  have hwF : wiener F ≤ c4 * hnorm 2 F := wiener_le hF.mz
  have n1 := hnorm_nonneg 2 F
  have n2 := hnorm_nonneg 3 F
  have n3 := fastXi_nonneg (y u)
  have s1 : wiener F * Real.sqrt (∑' k, (absSq k * B k) ^ 2) ≤
      c4 * hnorm 2 F * (hnorm 3 F + 8 * fastXi (y u)) :=
    mul_le_mul hwF hBn (Real.sqrt_nonneg _) (by positivity)
  have s2 : (∑' k, B k) * hnorm 2 F ≤ (c4 * hnorm 3 F + 4 * c4 * fastXi (y u)) * hnorm 2 F :=
    mul_le_mul_of_nonneg_right hBs n1
  have e : c4 * hnorm 2 F / |r| * (4 * hnorm 3 F + 28 * fastXi (y u)) =
      1 / |r| * (3 * (c4 * hnorm 2 F * (hnorm 3 F + 8 * fastXi (y u))) +
        (c4 * hnorm 3 F + 4 * c4 * fastXi (y u)) * hnorm 2 F) := by
    field_simp
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-! ### The fast `H²` law -/

/-- **The fast `H²` law, by sectors**: `∫ₛᵗ ‖F‖₃² ≤ ‖F s‖₂² + ∫ₛᵗ D²` as soon as
`‖Π_F Q(y,y)‖₁ ≤ D(u)`.  The true left trace is the only input from the past: this is `J_{3,pre}`
(Body 13: "`∫c_F² ≤ b_F(s)² + ‖h_F‖²_{L²H¹}`"), and no later pulse is used. -/
theorem fast_dissipation_J (h : ActualSol μ φ r g y Ty) {s t : ℝ} {D : ℝ → ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty)
    (hDi : IntervalIntegrable (fun u => D u ^ 2) volume s t)
    (hD : ∀ u ∈ Icc s t, hnorm 1 (PiF (Qphase (r * u) (y u) (y u))) ≤ D u) :
    ∫ u in s..t, fastNorm 3 r g y u ^ 2 ≤ fastNorm 2 r g y s ^ 2 + ∫ u in s..t, D u ^ 2 := by
  have hP := (heatPair_fast_level_two h (hs.trans hst) ht).mono hs le_rfl
  have hu0 : ∀ u ∈ Icc s t, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hs.trans hu.1, lt_lifespan hu.2 ht⟩
  have hp : ∀ᵐ u ∂(volume.restrict (Icc s t)),
      2 * pair 2 (PiF (actual r g y u)) (-PiF (Qphase (r * u) (y u) (y u))) ≤
        1 * hnorm 3 (PiF (actual r g y u)) ^ 2 + D u ^ 2 := by
    filter_upwards [ae_fast_three h hs hst ht, ae_restrict_mem measurableSet_Icc] with u hF3 hu
    have hy := h.sol.adm u (hu0 u hu).1 (hu0 u hu).2
    have hI := (hnorm_PiF_Qphase_le (r * u) hy).1
    have hI' : InH 1 (-PiF (Qphase (r * u) (y u) (y u))) := hI.neg
    have e1 : (2 : ℝ) + 1 = 3 := by norm_num
    have e2 : (2 : ℝ) - 1 = 1 := by norm_num
    have hl := (pair_le (σ := 2) (c := PiF (actual r g y u))
      (F := -PiF (Qphase (r * u) (y u) (y u))) (by rw [e1]; exact hF3) (by rw [e2]; exact hI')).2
    rw [e1, e2, hnorm_neg] at hl
    have hb1 := hD u hu
    have hb2 := hnorm_nonneg 1 (PiF (Qphase (r * u) (y u) (y u)))
    have hb3 := hnorm_nonneg 3 (PiF (actual r g y u))
    have := le_abs_self (pair 2 (PiF (actual r g y u)) (-PiF (Qphase (r * u) (y u) (y u))))
    nlinarith [sq_nonneg (hnorm 3 (PiF (actual r g y u)) -
      hnorm 1 (PiF (Qphase (r * u) (y u) (y u)))),
      pow_le_pow_left₀ hb2 hb1 2]
  have hE := hP.energy_le (τ := 3) (θ := 1) (by norm_num) hst hDi hp
  have hF := hnorm_nonneg 2 (PiF (actual r g y t))
  simp only [fastNorm]
  nlinarith [sq_nonneg (hnorm 2 (PiF (actual r g y t)))]

/-! ### The residual in `H¹` -/

/-- **The pointwise `H¹` bound of the residual, by sectors**, at a time with `F ∈ H³`: the bound of
`hnorm_one_corrRes_le` with `Ξ(y)` in place of `𝒜(y)‖y‖₂`.  Terms: `A R_S`, `Π_S g`, the force
filter `Π_S H_ψ`, the corrector derivative `2N(F',F)`, and the corrector in the nonlinearity. -/
theorem hnorm_one_corrRes_J (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (PiF (actual r g y u))) :
    InH 1 (corrRes r g y u) ∧
      hnorm 1 (corrRes r g y u) ≤ hnorm 1 g +
        c4 * fastNorm 2 r g y u / |r| * (24 * fastNorm 3 r g y u + 56 * fastXi (y u)) +
        8 * hnorm 2 (psi r 0 g u) * (wiener (actual r g y u) + c4 * hnorm 2 (actual r g y u) +
          c4 * hnorm 2 (psi r 0 g u)) +
        8 * hnorm 2 (slowCorr r g y u) * (slowWiener r g y u + c4 * slowNorm 2 r g y u +
          c4 * hnorm 2 (slowCorr r g y u)) := by
  have hx := actual_adm h hu huT
  have hψ := psi_adm (r := r) (t₀ := 0) h.force_adm u hu
  have hR := slowCorr_adm h hr hu huT
  have hz : Adm 2 (PiS (actual r g y u) + slowCorr r g y u) := corrSlow_adm h hr hu huT
  have hS := hx.PiS
  have hg1 : InH 1 g := h.force_adm.inH.mono (by norm_num)
  -- (1) `A R_S`
  obtain ⟨i1, b1⟩ := hnorm_one_A_slowCorr_le h hr hu huT hF3
  -- (2) the genuine force
  have i2 : InH 1 (PiS g) := hg1.PiS
  have b2 := hnorm_PiS_le hg1
  -- (3) the force filter
  obtain ⟨i3, b3⟩ := hnorm_Qm_three_bound (phaseM_bdd (r * u)) hx.mz hψ.mz
  have e3 : Hpsi r g y u = Qm (phaseM (r * u)) (actual r g y u) (psi r 0 g u) +
      Qm (phaseM (r * u)) (psi r 0 g u) (actual r g y u) +
      Qm (phaseM (r * u)) (psi r 0 g u) (psi r 0 g u) := Hpsi_eq h hu huT
  rw [← e3] at i3 b3
  have b3' := hnorm_PiS_le i3
  -- (4) the corrector derivative
  obtain ⟨i4, b4⟩ := hnorm_one_kinN_fastRHS_J h hr (r * u) hu huT hF3
  have i4' := i4.smul (2 : ℂ)
  have b4' : hnorm 1 ((2 : ℂ) • kinN r (r * u) (fastRHS r g y u) (PiF (actual r g y u))) ≤
      2 * (c4 * fastNorm 2 r g y u / |r| *
        (4 * fastNorm 3 r g y u + 28 * fastXi (y u))) := by
    rw [hnorm_smul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left b4 (by norm_num)
  -- (5) the nonlinear difference
  obtain ⟨i5, b5⟩ := hnorm_Qm_three_bound one_mult_bdd hS.mz hR.mz
  have e5 : Bsym (corrSlow r g y u) (corrSlow r g y u) -
      Bsym (PiS (actual r g y u)) (PiS (actual r g y u)) =
      Qm (fun _ _ _ _ _ => (1 : ℂ)) (PiS (actual r g y u)) (slowCorr r g y u) +
        Qm (fun _ _ _ _ _ => (1 : ℂ)) (slowCorr r g y u) (PiS (actual r g y u)) +
        Qm (fun _ _ _ _ _ => (1 : ℂ)) (slowCorr r g y u) (slowCorr r g y u) :=
    Bsym_add_sub hS hR hz
  rw [← e5] at i5 b5
  -- assembly
  have e : corrRes r g y u = (fun k => (absSq k : ℂ) • slowCorr r g y u k) + slowRes r g y u := by
    funext k; rfl
  have hres : InH 1 (slowRes r g y u) := ((i2.sub i3.PiS).add i4').add i5
  have t1 := hnorm_add_le i1 hres
  unfold slowRes at t1
  have t2 := hnorm_add_le ((i2.sub i3.PiS).add i4') i5
  have t3 := hnorm_add_le (i2.sub i3.PiS) i4'
  have t4 := hnorm_sub_le i2 i3.PiS
  refine ⟨by rw [e]; exact i1.add hres, ?_⟩
  have ealg : c4 * fastNorm 2 r g y u / |r| * (24 * fastNorm 3 r g y u + 56 * fastXi (y u)) =
      16 * c4 * fastNorm 2 r g y u / |r| * fastNorm 3 r g y u +
        2 * (c4 * fastNorm 2 r g y u / |r| *
          (4 * fastNorm 3 r g y u + 28 * fastXi (y u))) := by
    ring
  rw [ealg, e]
  unfold slowRes
  simp only [slowWiener, slowNorm] at *
  linarith only [t1, t2, t3, t4, b1, b2, b3, b3', b4', b5]

end OVNS.Quant

end
