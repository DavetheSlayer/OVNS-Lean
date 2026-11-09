import OddViscousNS.Quant.Energy.Kinetic.Multiplier

/-!
# E4.4 for the kinetic functional: bounds along the actual solution

The analytic inputs of `kinCorr_identity` (`Identity.lean`):
* reality and `ℓ²` bookkeeping of the right-hand sides `F' = fastRHS`, `S' = slowRHS`
  (`slowRHS_real`, `fastRHS_l2`, `slowRHS_l2`: `‖F'‖_{ℓ²} ≤ ‖F‖₂ + ‖Q(y,y)‖₀`,
  `‖S'‖_{ℓ²} ≤ ‖S‖₂ + ‖Q(y,y)‖₀ + ‖g‖₂`);
* the sup bounds along the solution (`exists_actual_bound`: `‖x‖₂ ≤ ‖y‖₂ + 2‖g‖₁/q`);
* **the summability control** `tripD_summable_bound` for the four-slot derivative family of the
  kinetic triad sum: `∑_{(p,q)} ‖tripD‖ ≤ 16 𝒜(S)‖F‖₁‖F‖₀ + (2/q)(2𝒜(F)‖F'‖₀‖S‖₀ + 𝒜(F)‖F‖₀‖S'‖₀)`
  (TeX (N3)/(N4) with the fixed-slow-output Cauchy pattern; survey §2.1 (c), spec risk R5);
* the continuity of the derivative family (`continuousOn_tripDPath`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS

variable {r : ℝ}

/-! ### Reality and `ℓ²` bookkeeping for the right-hand sides -/

private lemma conjV_add (a b : V3) : conjV (a + b) = conjV a + conjV b := by
  ext i; simp [conjV]

private lemma conjV_sub (a b : V3) : conjV (a - b) = conjV a - conjV b := by
  ext i; simp [conjV]

private lemma conjV_smul (c : ℂ) (a : V3) : conjV (c • a) = conj c • conjV a := by
  ext i; simp [conjV]

lemma IsReal.PiS' {W : Field} (h : IsReal W) : IsReal (PiS W) := fun k => by
  by_cases hk : k 2 = 0
  · have hk' : (-k) 2 = 0 := by simp [hk]
    rw [PiS_apply_slow _ hk', PiS_apply_slow _ hk, h k]
  · have hk' : (-k) 2 ≠ 0 := by rw [Pi.neg_apply, neg_ne_zero]; exact hk
    rw [PiS_apply_fast _ hk', PiS_apply_fast _ hk]
    ext i; simp [conjV]

lemma IsReal.PiF' {W : Field} (h : IsReal W) : IsReal (PiF W) := fun k => by
  by_cases hk : k 2 = 0
  · have hk' : (-k) 2 = 0 := by simp [hk]
    rw [PiF_apply_slow _ hk', PiF_apply_slow _ hk]
    ext i; simp [conjV]
  · have hk' : (-k) 2 ≠ 0 := by rw [Pi.neg_apply, neg_ne_zero]; exact hk
    rw [PiF_apply_fast _ hk', PiF_apply_fast _ hk, h k]

/-- `‖f‖² ≤ 2‖a‖² + 2‖b‖²` summability: a field dominated by a sum of two `ℓ²` fields is `ℓ²`. -/
lemma summable_norm_sq_of_le {f a b : Field} (h : ∀ k, ‖f k‖ ≤ ‖a k‖ + ‖b k‖)
    (ha : Summable fun k => ‖a k‖ ^ 2) (hb : Summable fun k => ‖b k‖ ^ 2) :
    Summable fun k => ‖f k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) ((ha.add hb).mul_left 2)
  have h1 := h k
  have h2 := norm_nonneg (f k)
  nlinarith [sq_nonneg (‖a k‖ - ‖b k‖), norm_nonneg (a k), norm_nonneg (b k)]

/-- The `ℓ²` norm of `A f = |k|² f` is `‖f‖₂`. -/
lemma tsum_norm_sq_absSq_smul {f : Field} (hf : InH 2 f) :
    (Summable fun k => ‖(-(absSq k : ℝ) : ℂ) • f k‖ ^ 2) ∧
      Real.sqrt (∑' k, ‖(-(absSq k : ℝ) : ℂ) • f k‖ ^ 2) = hnorm 2 f := by
  have e : ∀ k, ‖(-(absSq k : ℝ) : ℂ) • f k‖ ^ 2 = sobWeight 2 k * ‖f k‖ ^ 2 := fun k => by
    rw [norm_smul, mul_pow, sobWeight_two]
    congr 1
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg (absSq_nonneg k)]
  refine ⟨?_, ?_⟩
  · simp only [e]; exact hf
  · rw [hnorm]; congr 1; exact tsum_congr e

namespace Quant

variable {μ φ : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- `S'` is real. -/
lemma slowRHS_real (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    IsReal (slowRHS r g y u) := fun k => by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  have hQ : IsReal (Qphase (r * u) (y u) (y u)) :=
    (majorized_Qphase (r * u)).real 0 (y u) (y u) hy hy
  simp only [slowRHS]
  rw [absSq_neg, hx.PiS.real k, hQ.PiS' k, h.force_adm.PiS.real k, conjV_add, conjV_sub,
    conjV_smul]
  simp

/-- The `ℓ²` size of `F' = −AF − Π_F Q(y,y)`: `‖F'‖_{ℓ²} ≤ ‖F‖₂ + ‖Q(y,y)‖₀`. -/
lemma fastRHS_l2 (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    (Summable fun k => ‖fastRHS r g y u k‖ ^ 2) ∧
      Real.sqrt (∑' k, ‖fastRHS r g y u k‖ ^ 2) ≤
        hnorm 2 (PiF (actual r g y u)) + hnorm 0 (Qphase (r * u) (y u) (y u)) := by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  have hF := hx.PiF
  have hQ : InH 0 (Qphase (r * u) (y u) (y u)) := (hnorm_Qm_zero_le (phaseM_bdd _) hy.mz hy.mz).1
  obtain ⟨hA2, hAn⟩ := tsum_norm_sq_absSq_smul hF.inH
  have hQ2 : Summable fun k => ‖PiF (Qphase (r * u) (y u) (y u)) k‖ ^ 2 :=
    summable_norm_sq_of_inH hQ.PiF
  have hle : ∀ k, ‖fastRHS r g y u k‖ ≤ ‖(-(absSq k : ℝ) : ℂ) • PiF (actual r g y u) k‖ +
      ‖PiF (Qphase (r * u) (y u) (y u)) k‖ := fun k => norm_sub_le _ _
  have hs := summable_norm_sq_of_le hle hA2 hQ2
  refine ⟨hs, ?_⟩
  -- triangle inequality in `ℓ²`, through `hnorm 0`
  have h0 : fastRHS r g y u 0 = 0 := by simp [fastRHS, PiF]
  have hA0 : (fun k => (-(absSq k : ℝ) : ℂ) • PiF (actual r g y u) k) 0 = 0 := by
    simp [hF.mean]
  rw [← hnorm_zero_eq h0]
  have e : fastRHS r g y u = (fun k => (-(absSq k : ℝ) : ℂ) • PiF (actual r g y u) k) +
      (-PiF (Qphase (r * u) (y u) (y u))) := by
    funext k; simp [fastRHS, sub_eq_add_neg]
  rw [e]
  refine (hnorm_add_le (inH_zero_of_summable hA2) hQ.PiF.neg).trans ?_
  rw [hnorm_zero_eq hA0, hAn, hnorm_neg]
  exact add_le_add le_rfl (hnorm_PiF_le hQ)

/-- The `ℓ²` size of `S' = −AS − Π_S Q(y,y) + Π_S g`: `‖S'‖_{ℓ²} ≤ ‖S‖₂ + ‖Q(y,y)‖₀ + ‖g‖₂`. -/
lemma slowRHS_l2 (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    (Summable fun k => ‖slowRHS r g y u k‖ ^ 2) ∧
      Real.sqrt (∑' k, ‖slowRHS r g y u k‖ ^ 2) ≤
        hnorm 2 (PiS (actual r g y u)) + hnorm 0 (Qphase (r * u) (y u) (y u)) + hnorm 2 g := by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  have hS := hx.PiS
  have hQ : InH 0 (Qphase (r * u) (y u) (y u)) := (hnorm_Qm_zero_le (phaseM_bdd _) hy.mz hy.mz).1
  obtain ⟨hA2, hAn⟩ := tsum_norm_sq_absSq_smul hS.inH
  have hg0 : InH 0 g := h.force_adm.inH.mono (by norm_num)
  have hQ2 : Summable fun k => ‖(-PiS (Qphase (r * u) (y u) (y u)) + PiS g) k‖ ^ 2 :=
    summable_norm_sq_of_inH (hQ.PiS.neg.add hg0.PiS)
  have hle : ∀ k, ‖slowRHS r g y u k‖ ≤ ‖(-(absSq k : ℝ) : ℂ) • PiS (actual r g y u) k‖ +
      ‖(-PiS (Qphase (r * u) (y u) (y u)) + PiS g) k‖ := fun k => by
    have : slowRHS r g y u k = (-(absSq k : ℝ) : ℂ) • PiS (actual r g y u) k +
        (-PiS (Qphase (r * u) (y u) (y u)) + PiS g) k := by
      simp [slowRHS, sub_eq_add_neg, add_assoc]
    rw [this]; exact norm_add_le _ _
  have hs := summable_norm_sq_of_le hle hA2 hQ2
  refine ⟨hs, ?_⟩
  have hQ0 : Qphase (r * u) (y u) (y u) 0 = 0 := by simp [Qphase, Qm, hel_zero_mode]
  have ha0 : absSq (0 : Mode) = 0 := by simp [absSq]
  have h0 : slowRHS r g y u 0 = 0 := by
    simp [slowRHS, PiS, h.force_adm.mean, hx.mean, hQ0, ha0]
  have hA0 : (fun k => (-(absSq k : ℝ) : ℂ) • PiS (actual r g y u) k) 0 = 0 := by
    simp [hS.mean]
  rw [← hnorm_zero_eq h0]
  have e : slowRHS r g y u = (fun k => (-(absSq k : ℝ) : ℂ) • PiS (actual r g y u) k) +
      (-PiS (Qphase (r * u) (y u) (y u)) + PiS g) := by
    funext k; simp [slowRHS, sub_eq_add_neg, add_assoc]
  rw [e]
  refine (hnorm_add_le (inH_zero_of_summable hA2) (hQ.PiS.neg.add hg0.PiS)).trans ?_
  rw [hnorm_zero_eq hA0, hAn, add_assoc]
  refine add_le_add le_rfl ((hnorm_add_le hQ.PiS.neg hg0.PiS).trans ?_)
  rw [hnorm_neg]
  exact add_le_add (hnorm_PiS_le hQ)
    ((hnorm_PiS_le hg0).trans (hnorm_mono (by norm_num) h.force_adm.inH))


variable {μ φ : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- Uniform bound of `‖x‖₂` on `[0,b]`: `‖y‖₂ + ‖ψ‖₂ ≤ M + 2‖g‖₁/q`. -/
lemma exists_actual_bound (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) :
    ∃ Mx : ℝ, 0 ≤ Mx ∧ ∀ u ∈ Icc 0 b, hnorm 2 (actual r g y u) ≤ Mx := by
  obtain ⟨M, hM⟩ := h.sol.exists_bound hbT
  have hg1 := hnorm_nonneg 1 g
  refine ⟨max M 0 + 2 * hnorm 1 g / |r|, add_nonneg (le_max_right _ _) (by positivity),
    fun u hu => ?_⟩
  have hy := h.sol.adm u hu.1 (lt_lifespan hu.2 hbT)
  obtain ⟨hψ, hψle⟩ := psi_bound (t₀ := 0) hr h.force_adm u hu.1
  unfold actual
  exact (hnorm_sub_le hy.inH hψ).trans (add_le_add ((hM u hu).trans (le_max_left _ _)) hψle)

/-- `√∑ (|k| ‖f_k‖)² = ‖f‖₁` for a mean-zero field. -/
lemma sqrt_tsum_grad_sq (f : Field) :
    Real.sqrt (∑' k, (absk k * ‖f k‖) ^ 2) = hnorm 1 f := by
  unfold hnorm
  congr 1
  refine tsum_congr fun k => ?_
  rw [sobWeight_one, mul_pow, absk_sq]

/-- **The summability control for the kinetic derivative family** (fields at a fixed time): the
four slots of `tripD (kinM) (kinDM) F F' F F' S S'` are absolutely summable over `(p,q)` with
`∑ ≤ 16 𝒜(S) ‖F‖₁‖F‖₀ + (2/q)(2 𝒜(F)‖F'‖₀‖S‖₀ + 𝒜(F)‖F‖₀‖S'‖₀)` (`norm_tripT_le` for the
`e^{iτΦ}` slot through `tripT_kinDM_eq`, `norm_tripT_kinM_le` for the three `N` slots, and the
`ℓ¹ℓ²ℓ²` triple bounds). -/
lemma tripD_summable_bound (hr : r ≠ 0) (τ : ℝ) {F F' S S' : Field} (hF : PiF F = F)
    (hS : PiS S = S) (hF1 : Summable fun k => ‖F k‖) (hF2 : Summable fun k => ‖F k‖ ^ 2)
    (hFg : Summable fun k => (absk k * ‖F k‖) ^ 2) (hF'2 : Summable fun k => ‖F' k‖ ^ 2)
    (hS1 : Summable fun k => ‖S k‖) (hS2 : Summable fun k => ‖S k‖ ^ 2)
    (hS'2 : Summable fun k => ‖S' k‖ ^ 2) :
    (Summable fun x : Mode × Mode => ‖tripD (kinM r τ) (kinDM τ) F F' F F' S S' x.1 x.2‖) ∧
    ∑' x : Mode × Mode, ‖tripD (kinM r τ) (kinDM τ) F F' F F' S S' x.1 x.2‖ ≤
      16 * ((∑' k, ‖S k‖) *
          (Real.sqrt (∑' k, (absk k * ‖F k‖) ^ 2) * Real.sqrt (∑' k, ‖F k‖ ^ 2))) +
      2 / |r| * (2 * ((∑' k, ‖F k‖) *
          (Real.sqrt (∑' k, ‖F' k‖ ^ 2) * Real.sqrt (∑' k, ‖S k‖ ^ 2))) +
        (∑' k, ‖F k‖) * (Real.sqrt (∑' k, ‖F k‖ ^ 2) * Real.sqrt (∑' k, ‖S' k‖ ^ 2))) := by
  have hr' : 0 < |r| := abs_pos.mpr hr
  have hn : ∀ (W : Field) (k : Mode), 0 ≤ ‖W k‖ := fun W k => norm_nonneg _
  have hg : ∀ k, 0 ≤ absk k * ‖F k‖ := fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _)
  obtain ⟨s1, b1⟩ := summable_tri_third (a := fun k => absk k * ‖F k‖) (c := fun k => ‖F k‖)
    (b := fun k => ‖S k‖) hg (hn S) (hn F) hFg hF2 hS1
  obtain ⟨s2, b2⟩ := summable_tri_third (a := fun k => ‖F k‖) (c := fun k => absk k * ‖F k‖)
    (b := fun k => ‖S k‖) (hn F) (hn S) hg hF2 hFg hS1
  obtain ⟨s3, b3⟩ := summable_tri_second (a := fun k => ‖F' k‖) (b := fun k => ‖F k‖)
    (c := fun k => ‖S k‖) (hn F') (hn F) (hn S) hF'2 hS2 hF1
  obtain ⟨s4, b4⟩ := summable_tri_first (b := fun k => ‖F k‖) (a := fun k => ‖F' k‖)
    (c := fun k => ‖S k‖) (hn F) (hn F') (hn S) hF1 hF'2 hS2
  obtain ⟨s5, b5⟩ := summable_tri_first (b := fun k => ‖F k‖) (a := fun k => ‖F k‖)
    (c := fun k => ‖S' k‖) (hn F) (hn F) (hn S') hF1 hF2 hS'2
  set G : Mode × Mode → ℝ := fun x =>
    8 * (absk x.1 * ‖F x.1‖ * ‖F x.2‖ * ‖S (-(x.1 + x.2))‖) +
      8 * (‖F x.1‖ * (absk x.2 * ‖F x.2‖) * ‖S (-(x.1 + x.2))‖) +
      2 / |r| * (‖F' x.1‖ * ‖F x.2‖ * ‖S (-(x.1 + x.2))‖) +
      2 / |r| * (‖F x.1‖ * ‖F' x.2‖ * ‖S (-(x.1 + x.2))‖) +
      2 / |r| * (‖F x.1‖ * ‖F x.2‖ * ‖S' (-(x.1 + x.2))‖) with hG
  have hGs : Summable G :=
    (((((s1.mul_left 8).add (s2.mul_left 8)).add (s3.mul_left _)).add (s4.mul_left _)).add
      (s5.mul_left _))
  have hpt : ∀ x, ‖tripD (kinM r τ) (kinDM τ) F F' F F' S S' x.1 x.2‖ ≤ G x := fun x => by
    have h1 : ‖tripT (kinDM τ) F F S x.1 x.2‖ ≤
        8 * (absk x.1 * ‖F x.1‖ * ‖F x.2‖ * ‖S (-(x.1 + x.2))‖) +
          8 * (‖F x.1‖ * (absk x.2 * ‖F x.2‖) * ‖S (-(x.1 + x.2))‖) := by
      rw [tripT_kinDM_eq τ hF hS]
      refine (norm_tripT_le (phaseM_bdd τ) F F S x.1 x.2).trans (le_of_eq ?_)
      ring
    have h2 := norm_tripT_kinM_le (τ := τ) hr F' F S x.1 x.2
    have h3 := norm_tripT_kinM_le (τ := τ) hr F F' S x.1 x.2
    have h4 := norm_tripT_kinM_le (τ := τ) hr F F S' x.1 x.2
    have h5 : ‖tripD (kinM r τ) (kinDM τ) F F' F F' S S' x.1 x.2‖ ≤
        ‖tripT (kinDM τ) F F S x.1 x.2‖ + ‖tripT (kinM r τ) F' F S x.1 x.2‖ +
          ‖tripT (kinM r τ) F F' S x.1 x.2‖ + ‖tripT (kinM r τ) F F S' x.1 x.2‖ :=
      (norm_add_le _ _).trans (add_le_add norm_add₃_le le_rfl)
    rw [hG]
    linarith
  have hS0 : Summable fun x : Mode × Mode =>
      ‖tripD (kinM r τ) (kinDM τ) F F' F F' S S' x.1 x.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hGs
  refine ⟨hS0, (hS0.tsum_le_tsum hpt hGs).trans ?_⟩
  have eG : ∑' x, G x =
      8 * ∑' x : Mode × Mode, (absk x.1 * ‖F x.1‖ * ‖F x.2‖ * ‖S (-(x.1 + x.2))‖) +
      8 * ∑' x : Mode × Mode, (‖F x.1‖ * (absk x.2 * ‖F x.2‖) * ‖S (-(x.1 + x.2))‖) +
      2 / |r| * ∑' x : Mode × Mode, (‖F' x.1‖ * ‖F x.2‖ * ‖S (-(x.1 + x.2))‖) +
      2 / |r| * ∑' x : Mode × Mode, (‖F x.1‖ * ‖F' x.2‖ * ‖S (-(x.1 + x.2))‖) +
      2 / |r| * ∑' x : Mode × Mode, (‖F x.1‖ * ‖F x.2‖ * ‖S' (-(x.1 + x.2))‖) := by
    rw [hG,
      ((((s1.mul_left 8).add (s2.mul_left 8)).add (s3.mul_left _)).add (s4.mul_left _)).tsum_add
        (s5.mul_left _), (((s1.mul_left 8).add (s2.mul_left 8)).add (s3.mul_left _)).tsum_add
      (s4.mul_left _), ((s1.mul_left 8).add (s2.mul_left 8)).tsum_add (s3.mul_left _),
      (s1.mul_left 8).tsum_add (s2.mul_left 8), tsum_mul_left, tsum_mul_left, tsum_mul_left,
      tsum_mul_left, tsum_mul_left]
  rw [eG]
  have c1 := mul_le_mul_of_nonneg_left b1 (by norm_num : (0 : ℝ) ≤ 8)
  have c2 := mul_le_mul_of_nonneg_left b2 (by norm_num : (0 : ℝ) ≤ 8)
  have c3 := mul_le_mul_of_nonneg_left b3 (by positivity : (0 : ℝ) ≤ 2 / |r|)
  have c4 := mul_le_mul_of_nonneg_left b4 (by positivity : (0 : ℝ) ≤ 2 / |r|)
  have c5 := mul_le_mul_of_nonneg_left b5 (by positivity : (0 : ℝ) ≤ 2 / |r|)
  linarith

/-- Continuity of the derivative family along continuous paths. -/
lemma continuousOn_tripDPath {m m' : ℝ → Mult} {X X' Y Y' Z Z' : ℝ → Field} {s : Set ℝ}
    (x : Mode × Mode)
    (hm : ∀ a b c, ContinuousOn (fun u => m u a b c x.1 x.2) s)
    (hm' : ∀ a b c, ContinuousOn (fun u => m' u a b c x.1 x.2) s)
    (hX : ContinuousOn (fun u => X u x.1) s) (hX' : ContinuousOn (fun u => X' u x.1) s)
    (hY : ContinuousOn (fun u => Y u x.2) s) (hY' : ContinuousOn (fun u => Y' u x.2) s)
    (hZ : ContinuousOn (fun u => Z u (-(x.1 + x.2))) s)
    (hZ' : ContinuousOn (fun u => Z' u (-(x.1 + x.2))) s) :
    ContinuousOn (fun u => tripDPath m m' X X' Y Y' Z Z' u x) s := by
  have h1 := continuousOn_tripT x.1 x.2 hm' hX hY hZ
  have h2 := continuousOn_tripT x.1 x.2 hm hX' hY hZ
  have h3 := continuousOn_tripT x.1 x.2 hm hX hY' hZ
  have h4 := continuousOn_tripT x.1 x.2 hm hX hY hZ'
  have h5 := ((h1.add h2).add h3).add h4
  exact h5

end Quant

end OVNS

end
