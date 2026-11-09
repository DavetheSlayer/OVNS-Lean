import OddViscousNS.Quant.Energy.Kinetic.Bounds
import OddViscousNS.Quant.Regimes.Continuation

/-!
# E7-F, continuity along the actual solution

The continuity facts behind the heat pair of the corrected slow field (`Equation.lean`): the
`H²`-continuity of the corrector `ψ` and of the split field `x = y − ψ` (dominated convergence
over the modes, as in `Regimes/Continuation.lean`, whose versions are private), the
mode-continuity of a `Majorized` bilinear family along `H²`-continuous paths
(`continuousOn_majorized_mode`: the increment is bounded by `‖f − f₀‖₂‖g‖₂`-type terms through
(M3) and the multiplier is continuous for frozen fields), the `H⁰`-continuity of the phased
convection along the solution (`tendsto_hnorm0_Qphase_actual`) and the `ℓ²`-continuity of the
fast right-hand side `F' = fastRHS` (`tendsto_fastRHS_l2`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace OVNS

/-! ### Mode-wise facts -/

/-- A coefficient is dominated by the `H⁰` norm. -/
lemma norm_apply_le_hnorm_zero {f : Field} (hf : InH 0 f) (h0 : f 0 = 0) (k : Mode) :
    ‖f k‖ ≤ hnorm 0 f := by
  by_cases hk : k = 0
  · subst hk; rw [h0, norm_zero]; exact hnorm_nonneg _ _
  · have h := sobWeight_mul_norm_le hf k
    have hw : sobWeight 0 k = 1 := by simp [sobWeight, hk]
    rw [hw, one_mul] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hnorm_nonneg _ _) two_ne_zero).1 h

/-- Dominated convergence for the `H^s` distance along a filter. -/
lemma tendsto_hnorm_sub {F : ℝ → Field} {l : Filter ℝ} {t₀ s : ℝ} {B : Mode → ℝ}
    (hB : Summable B) (hdom : ∀ᶠ t in l, ∀ k, sobWeight s k * ‖F t k - F t₀ k‖ ^ 2 ≤ B k)
    (hpt : ∀ k, Tendsto (fun t => F t k) l (𝓝 (F t₀ k))) :
    Tendsto (fun t => hnorm s (F t - F t₀)) l (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := l) (f := fun t k => sobWeight s k *
      ‖F t k - F t₀ k‖ ^ 2) (g := fun _ => (0 : ℝ)) hB (fun k => ?_) ?_
  · have h2 := (Real.continuous_sqrt.tendsto _).comp h
    simpa [hnorm, Function.comp_def] using h2
  · have : Tendsto (fun t => F t k - F t₀ k) l (𝓝 0) := by
      simpa using (hpt k).sub_const (F t₀ k)
    have h3 := ((this.norm).pow 2).const_mul (sobWeight s k)
    simpa using h3
  · filter_upwards [hdom] with t ht k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _))]
    exact ht k

/-! ### The corrector is `H²`-continuous -/

/-- The helical coefficient of the corrector is at most `2/L ≤ 2`. -/
private lemma norm_coef_le (x y z L t : ℝ) (hL : 1 ≤ L) (ht : 0 ≤ t) :
    ‖(Complex.exp (-(Complex.I * (x : ℂ))) -
        Complex.exp (-((L * t : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (y : ℂ)))) /
      ((L : ℂ) - Complex.I * (z : ℂ))‖ ≤ 2 := by
  rw [norm_div]
  have hden : L ≤ ‖(L : ℂ) - Complex.I * (z : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (Complex.re_le_norm _)
    simp
  have he1 : ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have he2 : ‖Complex.exp (-(Complex.I * (y : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have he3 : ‖Complex.exp (-((L * t : ℝ) : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hnum : ‖Complex.exp (-(Complex.I * (x : ℂ))) -
      Complex.exp (-((L * t : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (y : ℂ)))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, he1, he2]
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (Complex.exp (-(Complex.I * (x : ℂ))) -
      Complex.exp (-((L * t : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (y : ℂ))))]

/-- Mode-wise size of the corrector at nonnegative times: `‖ψ(t)_k‖ ≤ 4 ‖g_k‖`. -/
lemma norm_psi_le (r : ℝ) (g : Field) {t : ℝ} (ht : 0 ≤ t) (k : Mode) :
    ‖psi r 0 g t k‖ ≤ 4 * ‖g k‖ := by
  unfold psi
  split_ifs with hk
  · rw [norm_zero]
    positivity
  · have hk0 : k ≠ 0 := by
      rintro rfl
      exact hk rfl
    have h1 : (1 : ℝ) ≤ absSq k := one_le_absSq hk0
    refine (norm_sum_le _ _).trans ?_
    rw [Fintype.sum_bool]
    have hterm : ∀ a : Sgn, ‖((Complex.exp (-(Complex.I * (r * (t + 0) * lam a k : ℝ))) -
        Complex.exp (-(absSq k * t : ℝ)) * Complex.exp (-(Complex.I * (r * 0 * lam a k : ℝ)))) /
          ((absSq k : ℂ) - Complex.I * (r * lam a k : ℝ))) • hel a k (g k)‖ ≤ 2 * ‖g k‖ := by
      intro a
      rw [norm_smul]
      exact mul_le_mul (norm_coef_le _ _ _ _ _ h1 ht) (norm_hel_le a k (g k)) (norm_nonneg _)
        (by norm_num)
    linarith [hterm true, hterm false]

/-- The corrector is continuous in `H²` on `[0, ∞)`. -/
theorem psi_cont {r : ℝ} {g : Field} (hg : Adm 2 g) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    Tendsto (fun t => hnorm 2 (psi r 0 g t - psi r 0 g t₀)) (𝓝[Ici 0] t₀) (𝓝 0) := by
  refine tendsto_hnorm_sub (B := fun k => 64 * (sobWeight 2 k * ‖g k‖ ^ 2))
    (hg.inH.mul_left 64) ?_ fun k =>
      ((psi_mode (r := r) (t₀ := 0) hg k t₀).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht k
  have h1 := norm_psi_le r g (mem_Ici.mp ht) k
  have h2 := norm_psi_le r g ht₀ k
  have h3 : ‖psi r 0 g t k - psi r 0 g t₀ k‖ ≤ 8 * ‖g k‖ :=
    (norm_sub_le _ _).trans (by linarith)
  have h4 : ‖psi r 0 g t k - psi r 0 g t₀ k‖ ^ 2 ≤ 64 * ‖g k‖ ^ 2 := by
    nlinarith [norm_nonneg (psi r 0 g t k - psi r 0 g t₀ k)]
  nlinarith [sobWeight_nonneg 2 k]

namespace Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- The split field `x = y − ψ` is `H²`-continuous on `[0, b]` inside the lifespan. -/
theorem actual_cont (h : ActualSol μ φ r g y Ty) {b : ℝ} (hbT : ENNReal.ofReal b < Ty) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 b) :
    Tendsto (fun t => hnorm 2 (actual r g y t - actual r g y t₀)) (𝓝[Icc 0 b] t₀) (𝓝 0) := by
  have hlife : ∀ t ∈ Icc (0 : ℝ) b, ENNReal.ofReal t < Ty := fun t ht =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) hbT
  have hsub : Icc (0 : ℝ) b ⊆ Ici 0 := fun t ht => ht.1
  have hy := (h.sol.cont t₀ ht₀.1 (hlife t₀ ht₀)).mono_left (nhdsWithin_mono _ hsub)
  have hp := (psi_cont (r := r) h.force_adm t₀ ht₀.1).mono_left (nhdsWithin_mono _ hsub)
  refine squeeze_zero' (Eventually.of_forall fun _ => hnorm_nonneg _ _) ?_
    (by simpa using hy.add hp)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have e : actual r g y t - actual r g y t₀ =
      (y t - y t₀) - (psi r 0 g t - psi r 0 g t₀) := by
    simp only [actual]
    abel
  rw [e]
  exact hnorm_sub_le (((h.sol.adm t ht.1 (hlife t ht)).inH).sub
      (h.sol.adm t₀ ht₀.1 (hlife t₀ ht₀)).inH)
    ((psi_adm h.force_adm t ht.1).inH.sub (psi_adm h.force_adm t₀ ht₀.1).inH)

/-- `y` is `H²`-continuous on `[0, b]` inside the lifespan (restriction of `IsHeatSol.cont`). -/
theorem y_cont (h : ActualSol μ φ r g y Ty) {b : ℝ} (hbT : ENNReal.ofReal b < Ty) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 b) :
    Tendsto (fun t => hnorm 2 (y t - y t₀)) (𝓝[Icc 0 b] t₀) (𝓝 0) :=
  (h.sol.cont t₀ ht₀.1 (lt_lifespan ht₀.2 hbT)).mono_left
    (nhdsWithin_mono _ fun t (ht : t ∈ Icc (0 : ℝ) b) => ht.1)

lemma PiF_sub' (u v : Field) : PiF (u - v) = PiF u - PiF v := by
  funext k
  simp only [PiF, Pi.sub_apply]
  split_ifs <;> simp

lemma PiS_sub' (u v : Field) : PiS (u - v) = PiS u - PiS v := by
  funext k
  simp only [PiS, Pi.sub_apply]
  split_ifs <;> simp

/-- The fast part `F = Π_F x` is `H²`-continuous on `[0, b]`. -/
theorem fast_cont (h : ActualSol μ φ r g y Ty) {b : ℝ} (hbT : ENNReal.ofReal b < Ty) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 b) :
    Tendsto (fun t => hnorm 2 (PiF (actual r g y t) - PiF (actual r g y t₀))) (𝓝[Icc 0 b] t₀)
      (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => hnorm_nonneg _ _) ?_ (actual_cont h hbT ht₀)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [← PiF_sub']
  exact hnorm_PiF_le ((actual_adm h ht.1 (lt_lifespan ht.2 hbT)).inH.sub
    (actual_adm h ht₀.1 (lt_lifespan ht₀.2 hbT)).inH)

/-- The slow part `S = Π_S x` is `H²`-continuous on `[0, b]`. -/
theorem slow_cont (h : ActualSol μ φ r g y Ty) {b : ℝ} (hbT : ENNReal.ofReal b < Ty) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 b) :
    Tendsto (fun t => hnorm 2 (PiS (actual r g y t) - PiS (actual r g y t₀))) (𝓝[Icc 0 b] t₀)
      (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => hnorm_nonneg _ _) ?_ (actual_cont h hbT ht₀)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [← PiS_sub']
  exact hnorm_PiS_le ((actual_adm h ht.1 (lt_lifespan ht.2 hbT)).inH.sub
    (actual_adm h ht₀.1 (lt_lifespan ht₀.2 hbT)).inH)

end Quant

/-! ### Mode-continuity of a `Majorized` family along `H²`-continuous paths -/

/-- `‖N t f g‖₀ ≤ 2 c₄ ‖f‖₂ ‖g‖₂` for a `Majorized` family ((M3) with `‖·‖₁ ≤ ‖·‖₂`,
`𝒜 ≤ c₄‖·‖₂`). -/
lemma Majorized.hnorm_zero_le' {N : ℝ → Field → Field → Field} (hN : Majorized N) (t : ℝ)
    {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) :
    hnorm 0 (N t f g) ≤ 2 * c4 * (hnorm 2 f * hnorm 2 g) := by
  have h := (hN.hnorm_zero_le t hf hg).2
  have h1 := hnorm_mono (by norm_num : (1 : ℝ) ≤ 2) hf.inH
  have h2 := hnorm_mono (by norm_num : (1 : ℝ) ≤ 2) hg.inH
  have h3 := wiener_le hf
  have h4 := wiener_le hg
  have hc := c4_pos
  have n1 := hnorm_nonneg 1 f
  have n2 := hnorm_nonneg 1 g
  have n3 := wiener_nonneg f
  have n4 := wiener_nonneg g
  have n5 := hnorm_nonneg 2 f
  have n6 := hnorm_nonneg 2 g
  nlinarith [mul_le_mul h1 h4 n4 n5, mul_le_mul h3 h2 n2 (by positivity)]

/-- A mode of `N t f g` is dominated by `2 c₄ ‖f‖₂ ‖g‖₂`. -/
lemma Majorized.norm_apply_le {N : ℝ → Field → Field → Field} (hN : Majorized N) (t : ℝ)
    {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    ‖N t f g k‖ ≤ 2 * c4 * (hnorm 2 f * hnorm 2 g) :=
  (norm_apply_le_hnorm_zero (hN.hnorm_zero_le t hf hg).1 (hN.mean t f g hf hg) k).trans
    (hN.hnorm_zero_le' t hf hg)

/-- **Mode-continuity of a `Majorized` family along `H²`-continuous, `H²`-bounded paths.** -/
theorem continuousOn_majorized_mode {N : ℝ → Field → Field → Field} (hN : Majorized N)
    {f g : ℝ → Field} {b : ℝ} (hf : ∀ u ∈ Icc 0 b, MZ 2 (f u)) (hg : ∀ u ∈ Icc 0 b, MZ 2 (g u))
    (hfc : ∀ u₀ ∈ Icc 0 b, Tendsto (fun u => hnorm 2 (f u - f u₀)) (𝓝[Icc 0 b] u₀) (𝓝 0))
    (hgc : ∀ u₀ ∈ Icc 0 b, Tendsto (fun u => hnorm 2 (g u - g u₀)) (𝓝[Icc 0 b] u₀) (𝓝 0))
    {M : ℝ} (hM : ∀ u ∈ Icc 0 b, hnorm 2 (f u) ≤ M ∧ hnorm 2 (g u) ≤ M) (k : Mode) :
    ContinuousOn (fun u => N u (f u) (g u) k) (Icc 0 b) := by
  intro u₀ hu₀
  have hM0 : 0 ≤ M := (hnorm_nonneg _ _).trans (hM u₀ hu₀).1
  have hc := c4_pos
  -- the frozen-field term is continuous in the multiplier
  have h3 : Tendsto (fun u => N u (f u₀) (g u₀) k - N u₀ (f u₀) (g u₀) k) (𝓝[Icc 0 b] u₀)
      (𝓝 0) := by
    have := ((hN.cont (f u₀) (g u₀) k (hf u₀ hu₀) (hg u₀ hu₀)).tendsto u₀).sub_const
      (N u₀ (f u₀) (g u₀) k)
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- the increment of the fields
  have hfg : Tendsto (fun u => 2 * c4 * (hnorm 2 (f u - f u₀) * M) +
      2 * c4 * (M * hnorm 2 (g u - g u₀))) (𝓝[Icc 0 b] u₀) (𝓝 0) := by
    have h1 := ((hfc u₀ hu₀).mul_const M).const_mul (2 * c4)
    have h2 := ((hgc u₀ hu₀).const_mul M).const_mul (2 * c4)
    simpa using h1.add h2
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using hfg.add h3.norm)
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hfu := hf u hu
  have hgu := hg u hu
  have hf0 := hf u₀ hu₀
  have hg0 := hg u₀ hu₀
  have hd1 : MZ 2 (f u - f u₀) := ⟨hfu.inH.sub hf0.inH, by simp [hfu.mean, hf0.mean]⟩
  have hd2 : MZ 2 (g u - g u₀) := ⟨hgu.inH.sub hg0.inH, by simp [hgu.mean, hg0.mean]⟩
  -- `N u (f u) (g u) − N u (f u₀) (g u₀) = N u (f u − f u₀) (g u) + N u (f u₀) (g u − g u₀)`
  have e1 := hN.sub_left u (f u) (f u₀) (g u) hfu hf0 hgu
  have e2 := hN.sub_right u (f u₀) (g u) (g u₀) hf0 hgu hg0
  have esplitF : N u (f u) (g u) - N u₀ (f u₀) (g u₀) =
      N u (f u - f u₀) (g u) + N u (f u₀) (g u - g u₀) +
        (N u (f u₀) (g u₀) - N u₀ (f u₀) (g u₀)) := by
    rw [e1, e2]; abel
  have esplit : N u (f u) (g u) k - N u₀ (f u₀) (g u₀) k =
      N u (f u - f u₀) (g u) k + N u (f u₀) (g u - g u₀) k +
        (N u (f u₀) (g u₀) k - N u₀ (f u₀) (g u₀) k) := by
    have := congrFun esplitF k
    simpa only [Pi.sub_apply, Pi.add_apply] using this
  have b1 := hN.norm_apply_le u hd1 hgu k
  have b2 := hN.norm_apply_le u hf0 hd2 k
  have hgM := (hM u hu).2
  have hfM := (hM u₀ hu₀).1
  have n1 := hnorm_nonneg 2 (f u - f u₀)
  have n2 := hnorm_nonneg 2 (g u - g u₀)
  calc ‖N u (f u) (g u) k - N u₀ (f u₀) (g u₀) k‖
      ≤ ‖N u (f u - f u₀) (g u) k‖ + ‖N u (f u₀) (g u - g u₀) k‖ +
        ‖N u (f u₀) (g u₀) k - N u₀ (f u₀) (g u₀) k‖ := by
        rw [esplit]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2 * c4 * (hnorm 2 (f u - f u₀) * M) + 2 * c4 * (M * hnorm 2 (g u - g u₀)) +
        ‖N u (f u₀) (g u₀) k - N u₀ (f u₀) (g u₀) k‖ := by
        gcongr
        · exact b1.trans (by gcongr)
        · exact b2.trans (by gcongr)

/-- `H⁰`-continuity of a `Majorized` family along `H²`-continuous, `H²`-bounded paths: the
frozen-field multiplier continuity by dominated convergence with the `ℓ²` majorant of (M3). -/
theorem tendsto_hnorm0_majorized {N : ℝ → Field → Field → Field} (hN : Majorized N)
    {f g : ℝ → Field} {b : ℝ} (hf : ∀ u ∈ Icc 0 b, MZ 2 (f u)) (hg : ∀ u ∈ Icc 0 b, MZ 2 (g u))
    (hfc : ∀ u₀ ∈ Icc 0 b, Tendsto (fun u => hnorm 2 (f u - f u₀)) (𝓝[Icc 0 b] u₀) (𝓝 0))
    (hgc : ∀ u₀ ∈ Icc 0 b, Tendsto (fun u => hnorm 2 (g u - g u₀)) (𝓝[Icc 0 b] u₀) (𝓝 0))
    {M : ℝ} (hM : ∀ u ∈ Icc 0 b, hnorm 2 (f u) ≤ M ∧ hnorm 2 (g u) ≤ M) {u₀ : ℝ}
    (hu₀ : u₀ ∈ Icc 0 b) :
    Tendsto (fun u => hnorm 0 (N u (f u) (g u) - N u₀ (f u₀) (g u₀))) (𝓝[Icc 0 b] u₀) (𝓝 0) := by
  have hM0 : 0 ≤ M := (hnorm_nonneg _ _).trans (hM u₀ hu₀).1
  have hc := c4_pos
  have hf0 := hf u₀ hu₀
  have hg0 := hg u₀ hu₀
  -- the frozen-field term: dominated convergence over the modes
  have h3 : Tendsto (fun u => hnorm 0 (N u (f u₀) (g u₀) - N u₀ (f u₀) (g u₀))) (𝓝[Icc 0 b] u₀)
      (𝓝 0) := by
    -- the majorant `maj₁` is in `ℓ²`
    obtain ⟨-, hc1, -⟩ := young_l1_l2 (a := fun p => ‖f u₀ p‖) (b := fun q => absk q * ‖g u₀ q‖)
      (fun _ => norm_nonneg _) (fun q => mul_nonneg (absk_nonneg q) (norm_nonneg _))
      (summable_wiener hf0.inH) (summable_grad_sq hg0)
    obtain ⟨-, hc2, -⟩ := young_l1_l2 (a := fun q => ‖g u₀ q‖) (b := fun p => absk p * ‖f u₀ p‖)
      (fun _ => norm_nonneg _) (fun p => mul_nonneg (absk_nonneg p) (norm_nonneg _))
      (summable_wiener hg0.inH) (summable_grad_sq hf0)
    set maj : Mode → ℝ := fun k => ∑' p, (absk p + absk (k - p)) * ‖f u₀ p‖ * ‖g u₀ (k - p)‖
      with hmaj
    have hmaj_eq : ∀ k, maj k = convR (fun q => ‖g u₀ q‖) (fun p => absk p * ‖f u₀ p‖) k +
        convR (fun p => ‖f u₀ p‖) (fun q => absk q * ‖g u₀ q‖) k := by
      intro k
      rw [convR_comm (fun q => ‖g u₀ q‖) (fun p => absk p * ‖f u₀ p‖)]
      simp only [hmaj, convR]
      have s1 := (convR_le_of_l2 (a := fun p => absk p * ‖f u₀ p‖) (b := fun q => ‖g u₀ q‖)
        (fun p => mul_nonneg (absk_nonneg p) (norm_nonneg _)) (fun _ => norm_nonneg _)
        (summable_grad_sq hf0) (summable_sq hg0) k).1
      have s2 := (convR_le_of_l2 (a := fun p => ‖f u₀ p‖) (b := fun q => absk q * ‖g u₀ q‖)
        (fun _ => norm_nonneg _) (fun q => mul_nonneg (absk_nonneg q) (norm_nonneg _))
        (summable_sq hf0) (summable_grad_sq hg0) k).1
      rw [← s1.tsum_add s2]
      refine tsum_congr fun p => ?_
      ring
    have hmaj2 : Summable fun k => 8 * maj k ^ 2 := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
        ((hc2.add hc1).mul_left 16)
      rw [hmaj_eq]
      nlinarith [sq_nonneg (convR (fun q => ‖g u₀ q‖) (fun p => absk p * ‖f u₀ p‖) k -
        convR (fun p => ‖f u₀ p‖) (fun q => absk q * ‖g u₀ q‖) k)]
    refine tendsto_hnorm_sub (F := fun u => N u (f u₀) (g u₀)) (s := 0) (B := fun k => 8 * maj k ^ 2)
      hmaj2 ?_ fun k => ?_
    · refine Eventually.of_forall fun u k => ?_
      have hw : sobWeight 0 k ≤ 1 := by unfold sobWeight; split_ifs <;> simp
      have m1 := hN.maj₁ u (f u₀) (g u₀) k hf0 hg0
      have m2 := hN.maj₁ u₀ (f u₀) (g u₀) k hf0 hg0
      have hd : ‖N u (f u₀) (g u₀) k - N u₀ (f u₀) (g u₀) k‖ ≤ 2 * maj k :=
        (norm_sub_le _ _).trans (by simp only [hmaj]; linarith)
      have hd2 : ‖N u (f u₀) (g u₀) k - N u₀ (f u₀) (g u₀) k‖ ^ 2 ≤ 4 * maj k ^ 2 := by
        nlinarith [norm_nonneg (N u (f u₀) (g u₀) k - N u₀ (f u₀) (g u₀) k)]
      have hmk : 0 ≤ maj k := by
        simp only [hmaj]
        exact tsum_nonneg fun p => mul_nonneg (mul_nonneg (add_nonneg (absk_nonneg _)
          (absk_nonneg _)) (norm_nonneg _)) (norm_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_right hw
        (sq_nonneg ‖N u (f u₀) (g u₀) k - N u₀ (f u₀) (g u₀) k‖)]
    · exact ((hN.cont (f u₀) (g u₀) k hf0 hg0).tendsto u₀).mono_left nhdsWithin_le_nhds
  have hfg : Tendsto (fun u => 2 * c4 * (hnorm 2 (f u - f u₀) * M) +
      2 * c4 * (M * hnorm 2 (g u - g u₀))) (𝓝[Icc 0 b] u₀) (𝓝 0) := by
    have h1 := ((hfc u₀ hu₀).mul_const M).const_mul (2 * c4)
    have h2 := ((hgc u₀ hu₀).const_mul M).const_mul (2 * c4)
    simpa using h1.add h2
  refine squeeze_zero' (Eventually.of_forall fun _ => hnorm_nonneg _ _) ?_ (by simpa using hfg.add h3)
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hfu := hf u hu
  have hgu := hg u hu
  have hd1 : MZ 2 (f u - f u₀) := ⟨hfu.inH.sub hf0.inH, by simp [hfu.mean, hf0.mean]⟩
  have hd2 : MZ 2 (g u - g u₀) := ⟨hgu.inH.sub hg0.inH, by simp [hgu.mean, hg0.mean]⟩
  have e1 := hN.sub_left u (f u) (f u₀) (g u) hfu hf0 hgu
  have e2 := hN.sub_right u (f u₀) (g u) (g u₀) hf0 hgu hg0
  have esplit : N u (f u) (g u) - N u₀ (f u₀) (g u₀) =
      N u (f u - f u₀) (g u) + N u (f u₀) (g u - g u₀) +
        (N u (f u₀) (g u₀) - N u₀ (f u₀) (g u₀)) := by
    rw [e1, e2]; abel
  have i1 := (hN.hnorm_zero_le u hd1 hgu).1
  have i2 := (hN.hnorm_zero_le u hf0 hd2).1
  have i3 := (hN.hnorm_zero_le u hf0 hg0).1.sub (hN.hnorm_zero_le u₀ hf0 hg0).1
  have b1 := hN.hnorm_zero_le' u hd1 hgu
  have b2 := hN.hnorm_zero_le' u hf0 hd2
  have hgM := (hM u hu).2
  have hfM := (hM u₀ hu₀).1
  have n1 := hnorm_nonneg 2 (f u - f u₀)
  have n2 := hnorm_nonneg 2 (g u - g u₀)
  rw [esplit]
  calc hnorm 0 (N u (f u - f u₀) (g u) + N u (f u₀) (g u - g u₀) +
        (N u (f u₀) (g u₀) - N u₀ (f u₀) (g u₀)))
      ≤ hnorm 0 (N u (f u - f u₀) (g u)) + hnorm 0 (N u (f u₀) (g u - g u₀)) +
        hnorm 0 (N u (f u₀) (g u₀) - N u₀ (f u₀) (g u₀)) :=
        (hnorm_add_le (i1.add i2) i3).trans (add_le_add (hnorm_add_le i1 i2) le_rfl)
    _ ≤ 2 * c4 * (hnorm 2 (f u - f u₀) * M) + 2 * c4 * (M * hnorm 2 (g u - g u₀)) +
        hnorm 0 (N u (f u₀) (g u₀) - N u₀ (f u₀) (g u₀)) := by
        gcongr
        · exact b1.trans (by gcongr)
        · exact b2.trans (by gcongr)

namespace Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- The phased convection along `x` or `F`: `Qphase (r u) = filtN r 0 u`. -/
lemma filtN_eq (r u : ℝ) : filtN r 0 u = Qphase (r * u) := by
  simp [filtN]

/-- `u ↦ Q_{ru}(f u, g u)_k` is continuous along `H²`-continuous bounded paths. -/
theorem continuousOn_Qphase_mode_of_paths {f g' : ℝ → Field} {b : ℝ}
    (hf : ∀ u ∈ Icc 0 b, MZ 2 (f u)) (hg : ∀ u ∈ Icc 0 b, MZ 2 (g' u))
    (hfc : ∀ u₀ ∈ Icc 0 b, Tendsto (fun u => hnorm 2 (f u - f u₀)) (𝓝[Icc 0 b] u₀) (𝓝 0))
    (hgc : ∀ u₀ ∈ Icc 0 b, Tendsto (fun u => hnorm 2 (g' u - g' u₀)) (𝓝[Icc 0 b] u₀) (𝓝 0))
    {M : ℝ} (hM : ∀ u ∈ Icc 0 b, hnorm 2 (f u) ≤ M ∧ hnorm 2 (g' u) ≤ M) (k : Mode) :
    ContinuousOn (fun u => Qphase (r * u) (f u) (g' u) k) (Icc 0 b) := by
  have := continuousOn_majorized_mode (majorized_filtN r 0) hf hg hfc hgc hM k
  simpa only [filtN_eq] using this

/-- The sup bound of `‖x‖₂` on `[0,b]`, with the fast part. -/
lemma exists_actual_bound' (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc 0 b, hnorm 2 (actual r g y u) ≤ M ∧
      hnorm 2 (PiF (actual r g y u)) ≤ M ∧ hnorm 2 (PiS (actual r g y u)) ≤ M ∧
      hnorm 2 (y u) ≤ M := by
  obtain ⟨Mx, hMx0, hMx⟩ := exists_actual_bound h hr hbT
  obtain ⟨My, hMy⟩ := h.sol.exists_bound hbT
  refine ⟨max Mx My, le_trans hMx0 (le_max_left _ _), fun u hu => ?_⟩
  have hx := (actual_adm h hu.1 (lt_lifespan hu.2 hbT)).inH
  exact ⟨(hMx u hu).trans (le_max_left _ _),
    (hnorm_PiF_le hx).trans ((hMx u hu).trans (le_max_left _ _)),
    (hnorm_PiS_le hx).trans ((hMx u hu).trans (le_max_left _ _)),
    (hMy u hu).trans (le_max_right _ _)⟩

/-- `u ↦ Q_{ru}(F u, F u)_k` is continuous on `[0, b]`. -/
theorem continuousOn_Qphase_fast_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => Qphase (r * u) (PiF (actual r g y u)) (PiF (actual r g y u)) k)
      (Icc 0 b) := by
  obtain ⟨M, -, hM⟩ := exists_actual_bound' h hr hbT
  exact continuousOn_Qphase_mode_of_paths
    (fun u hu => (actual_adm h hu.1 (lt_lifespan hu.2 hbT)).PiF.mz)
    (fun u hu => (actual_adm h hu.1 (lt_lifespan hu.2 hbT)).PiF.mz)
    (fun u₀ hu₀ => fast_cont h hbT hu₀) (fun u₀ hu₀ => fast_cont h hbT hu₀)
    (fun u hu => ⟨(hM u hu).2.1, (hM u hu).2.1⟩) k

/-- `u ↦ Q_{ru}(x u, x u)_k` is continuous on `[0, b]`. -/
theorem continuousOn_Qphase_actual_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => Qphase (r * u) (actual r g y u) (actual r g y u) k) (Icc 0 b) := by
  obtain ⟨M, -, hM⟩ := exists_actual_bound' h hr hbT
  exact continuousOn_Qphase_mode_of_paths
    (fun u hu => actual_mz h hu.1 (lt_lifespan hu.2 hbT))
    (fun u hu => actual_mz h hu.1 (lt_lifespan hu.2 hbT))
    (fun u₀ hu₀ => actual_cont h hbT hu₀) (fun u₀ hu₀ => actual_cont h hbT hu₀)
    (fun u hu => ⟨(hM u hu).1, (hM u hu).1⟩) k

/-- The force filter `H_ψ` is mode-continuous on `[0, b]`. -/
theorem continuousOn_Hpsi_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => Hpsi r g y u k) (Icc 0 b) := by
  have h1 := continuousOn_Qphase_mode h hb hbT k
  have h2 := continuousOn_Qphase_actual_mode h hr hbT k
  exact h1.sub h2

/-- `H⁰`-continuity of `u ↦ Q_{ru}(y u, y u)` on `[0, b]`. -/
theorem tendsto_hnorm0_Qphase_y (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) {u₀ : ℝ} (hu₀ : u₀ ∈ Icc 0 b) :
    Tendsto (fun u => hnorm 0 (Qphase (r * u) (y u) (y u) - Qphase (r * u₀) (y u₀) (y u₀)))
      (𝓝[Icc 0 b] u₀) (𝓝 0) := by
  obtain ⟨M, -, hM⟩ := exists_actual_bound' h hr hbT
  have := tendsto_hnorm0_majorized (majorized_filtN r 0) (f := y) (g := y)
    (fun u hu => (h.sol.adm u hu.1 (lt_lifespan hu.2 hbT)).mz)
    (fun u hu => (h.sol.adm u hu.1 (lt_lifespan hu.2 hbT)).mz)
    (fun u₀ hu₀ => y_cont h hbT hu₀) (fun u₀ hu₀ => y_cont h hbT hu₀)
    (fun u hu => ⟨(hM u hu).2.2.2, (hM u hu).2.2.2⟩) hu₀
  simpa only [filtN_eq] using this

/-- The `ℓ²` norm of a mean-zero field is its `H⁰` norm (restated). -/
lemma sqrt_tsum_sq_eq {f : Field} (hf : f 0 = 0) :
    Real.sqrt (∑' k, ‖f k‖ ^ 2) = hnorm 0 f := (hnorm_zero_eq hf).symm

/-- **`ℓ²`-continuity of `F' = fastRHS`** on `[0, b]`:
`‖F' u − F' u₀‖_{ℓ²} ≤ ‖F u − F u₀‖₂ + ‖Q_{ru}(y u,y u) − Q_{ru₀}(y u₀, y u₀)‖₀`. -/
theorem tendsto_fastRHS_l2 (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) {u₀ : ℝ} (hu₀ : u₀ ∈ Icc 0 b) :
    Tendsto (fun u => hnorm 0 (fastRHS r g y u - fastRHS r g y u₀)) (𝓝[Icc 0 b] u₀) (𝓝 0) := by
  have h1 := fast_cont h hbT hu₀
  have h2 := tendsto_hnorm0_Qphase_y h hr hbT hu₀
  refine squeeze_zero' (Eventually.of_forall fun _ => hnorm_nonneg _ _) ?_ (by simpa using h1.add h2)
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hx := actual_adm h hu.1 (lt_lifespan hu.2 hbT)
  have hx0 := actual_adm h hu₀.1 (lt_lifespan hu₀.2 hbT)
  have hy := h.sol.adm u hu.1 (lt_lifespan hu.2 hbT)
  have hy0 := h.sol.adm u₀ hu₀.1 (lt_lifespan hu₀.2 hbT)
  have hQ : InH 0 (Qphase (r * u) (y u) (y u)) := (hnorm_Qm_zero_le (phaseM_bdd _) hy.mz hy.mz).1
  have hQ0 : InH 0 (Qphase (r * u₀) (y u₀) (y u₀)) :=
    (hnorm_Qm_zero_le (phaseM_bdd _) hy0.mz hy0.mz).1
  set D := PiF (actual r g y u) - PiF (actual r g y u₀) with hD
  have hD2 : InH 2 D := hx.PiF.inH.sub hx0.PiF.inH
  -- `F' u − F' u₀ = −A D − Π_F (Q u − Q u₀)`
  have e : fastRHS r g y u - fastRHS r g y u₀ =
      (fun k => (-(absSq k : ℝ) : ℂ) • D k) - PiF (Qphase (r * u) (y u) (y u) -
        Qphase (r * u₀) (y u₀) (y u₀)) := by
    funext k
    simp only [fastRHS, hD, Pi.sub_apply, PiF_sub', smul_sub]
    abel
  have hA : InH 0 (fun k => (-(absSq k : ℝ) : ℂ) • D k) := by
    obtain ⟨hs, -⟩ := tsum_norm_sq_absSq_smul hD2
    exact inH_zero_of_summable hs
  have hAn : hnorm 0 (fun k => (-(absSq k : ℝ) : ℂ) • D k) = hnorm 2 D := by
    obtain ⟨-, he⟩ := tsum_norm_sq_absSq_smul hD2
    rw [← he, hnorm_zero_eq]
    simp [hD, hx.PiF.mean, hx0.PiF.mean]
  rw [e]
  refine (hnorm_sub_le hA (hQ.sub hQ0).PiF).trans ?_
  rw [hAn]
  exact add_le_add le_rfl (hnorm_PiF_le (hQ.sub hQ0))

end Quant

end OVNS

end
