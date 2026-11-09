import OddViscousNS.Majorant
import OddViscousNS.EnergyMode
import OddViscousNS.Gronwall

/-! # Filtered system: shifts, `HeatPair` instances, time-continuity of the nonlinearity -/

open scoped ENNReal Topology
open MeasureTheory Set Filter
noncomputable section
namespace OVNS

variable {N : ℝ → Field → Field → Field} {G : ℝ → Field} {Γ : ℝ}

/-- For a mean-zero field, the `H⁰` weight is trivial on every mode. -/
private lemma sobWeight_zero_mul {f : Field} (h0 : f 0 = 0) (k : Mode) :
    sobWeight 0 k * ‖f k‖ ^ 2 = ‖f k‖ ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    simp [h0]
  · simp [sobWeight, hk]

/-- Mean-zero `H²` coefficients are square-summable. -/
private lemma summable_norm_sq {f : Field} (hf : MZ 2 f) : Summable fun k => ‖f k‖ ^ 2 := by
  have h : InH 0 f := InH.mono (by norm_num) hf.inH
  unfold InH at h
  simpa only [sobWeight_zero_mul hf.mean] using h

/-- The `ℓ²` norm of the coefficients is bounded by the `H²` norm. -/
private lemma sqrt_tsum_norm_sq_le {f : Field} (hf : MZ 2 f) :
    Real.sqrt (∑' k, ‖f k‖ ^ 2) ≤ hnorm 2 f := by
  have e : hnorm 0 f = Real.sqrt (∑' k, ‖f k‖ ^ 2) := by
    simp only [hnorm, sobWeight_zero_mul hf.mean]
  rw [← e]
  exact hnorm_mono (by norm_num) hf.inH

/-- Each coefficient of a mean-zero `H^s` field, `s ≥ 0`, is bounded by the `H^s` norm. -/
private lemma norm_le_hnorm {s : ℝ} {f : Field} (hs : 0 ≤ s) (hf : InH s f) (h0 : f 0 = 0)
    (k : Mode) : ‖f k‖ ≤ hnorm s f := by
  have h := sobWeight_mul_norm_le (InH.mono hs hf) k
  rw [sobWeight_zero_mul h0] at h
  exact ((sq_le_sq₀ (norm_nonneg _) (hnorm_nonneg _ _)).1 h).trans (hnorm_mono hs hf)

/-- A difference of mean-zero `H²` fields is a mean-zero `H²` field. -/
private lemma MZ.sub' {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) : MZ 2 (f - g) :=
  ⟨hf.inH.sub hg.inH, by simp [hf.mean, hg.mean]⟩

/-- Pointwise bound of a majorized bilinear form by `H²` norms. -/
private lemma Majorized.norm_apply_le (hN : Majorized N) (t : ℝ) {f g : Field} (hf : MZ 2 f)
    (hg : MZ 2 g) (k : Mode) : ‖N t f g k‖ ≤ 2 * absk k * (hnorm 2 f * hnorm 2 g) := by
  have h := (convR_le_of_l2 (a := fun k => ‖f k‖) (b := fun k => ‖g k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (summable_norm_sq hf)
    (summable_norm_sq hg) k).2
  have h' : ∑' p, ‖f p‖ * ‖g (k - p)‖ ≤ hnorm 2 f * hnorm 2 g :=
    h.trans (mul_le_mul (sqrt_tsum_norm_sq_le hf) (sqrt_tsum_norm_sq_le hg)
      (Real.sqrt_nonneg _) (hnorm_nonneg _ _))
  exact (hN.maj₂ t f g k hf hg).trans
    (mul_le_mul_of_nonneg_left h' (mul_nonneg zero_le_two (absk_nonneg k)))

/-- Lipschitz bound of the quadratic map `f ↦ N t f f` on each mode. -/
private lemma Majorized.norm_sub_apply_le (hN : Majorized N) (t : ℝ) {f f₀ : Field}
    (hf : MZ 2 f) (hf₀ : MZ 2 f₀) (k : Mode) :
    ‖N t f f k - N t f₀ f₀ k‖ ≤ 2 * absk k * (hnorm 2 (f - f₀) * (hnorm 2 f + hnorm 2 f₀)) := by
  have hd := MZ.sub' hf hf₀
  have e : N t f f k - N t f₀ f₀ k = N t (f - f₀) f k + N t f₀ (f - f₀) k := by
    rw [hN.sub_left t f f₀ f hf hf₀ hf, hN.sub_right t f₀ f f₀ hf₀ hf hf₀]
    simp only [Pi.sub_apply]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := hN.norm_apply_le t hd hf k
  have h2 := hN.norm_apply_le t hf₀ hd k
  nlinarith [h1, h2]

/-- Every mode of a good force is continuous in time. -/
private lemma GoodForce.continuous_mode (hG : GoodForce G Γ) (k : Mode) :
    Continuous fun t => G t k := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) (hG.cont t₀)
  exact norm_le_hnorm zero_le_one ((hG.adm t).inH.sub (hG.adm t₀).inH)
    (by simp [(hG.adm t).mean, (hG.adm t₀).mean]) k

/-- Times of `[0,b]` lie in the lifespan when `b` does. -/
private lemma ofReal_lt_of_mem {T : ℝ≥0∞} {t b : ℝ} (ht : t ∈ Icc 0 b)
    (hbT : ENNReal.ofReal b < T) : ENNReal.ofReal t < T :=
  (ENNReal.ofReal_le_ofReal ht.2).trans_lt hbT

/-- The shifted time stays in the lifespan. -/
private lemma ofReal_add_lt {T : ℝ≥0∞} {t t₀ : ℝ} (ht : 0 ≤ t) (ht₀ : 0 ≤ t₀)
    (h : ENNReal.ofReal t < T - ENNReal.ofReal t₀) : ENNReal.ofReal (t + t₀) < T := by
  rw [ENNReal.ofReal_add ht ht₀]
  exact lt_tsub_iff_right.1 h

/-- Time translation of solutions. -/
theorem IsHeatSol.shift {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) (_ht₀' : ENNReal.ofReal t₀ < T) :
    IsHeatSol (fun t => N (t + t₀)) (fun t => G (t + t₀)) (T - ENNReal.ofReal t₀)
      (fun t => y (t + t₀)) := by
  refine ⟨fun t ht h => hy.adm _ (add_nonneg ht ht₀) (ofReal_add_lt ht ht₀ h), ?_, ?_⟩
  · intro t ht h
    have hm : Tendsto (fun s => s + t₀) (𝓝[Ici 0] t) (𝓝[Ici 0] (t + t₀)) :=
      (continuous_id.add continuous_const).continuousWithinAt.tendsto_nhdsWithin
        fun s hs => add_nonneg hs ht₀
    exact (hy.cont _ (add_nonneg ht ht₀) (ofReal_add_lt ht ht₀ h)).comp hm
  · intro k t ht h
    have hd := hy.mode k (t + t₀) (add_nonneg ht ht₀) (ofReal_add_lt ht ht₀ h)
    have hs : HasDerivWithinAt (fun s : ℝ => s + t₀) (1 : ℝ) (Ici 0) t :=
      (hasDerivWithinAt_id t _).add_const t₀
    have h' := hd.scomp t hs (fun s (hs : (0 : ℝ) ≤ s) => add_nonneg hs ht₀)
    rw [one_smul] at h'
    exact h'

/-- Time translation of a majorized family. -/
theorem Majorized.shift (hN : Majorized N) (t₀ : ℝ) : Majorized (fun t => N (t + t₀)) where
  add_left t := hN.add_left (t + t₀)
  sub_left t := hN.sub_left (t + t₀)
  add_right t := hN.add_right (t + t₀)
  sub_right t := hN.sub_right (t + t₀)
  maj₁ t := hN.maj₁ (t + t₀)
  maj₂ t := hN.maj₂ (t + t₀)
  real t := hN.real (t + t₀)
  sol t := hN.sol (t + t₀)
  mean t := hN.mean (t + t₀)
  cont f g k hf hg := (hN.cont f g k hf hg).comp (continuous_id.add continuous_const)

/-- Time translation of a good force. -/
theorem GoodForce.shift (hG : GoodForce G Γ) (t₀ : ℝ) :
    GoodForce (fun t => G (t + t₀)) Γ where
  adm t := hG.adm (t + t₀)
  bd t := hG.bd (t + t₀)
  cont t := (hG.cont (t + t₀)).comp (continuous_id.add continuous_const).continuousAt

/-- `t ↦ ‖y t‖₂` is continuous on compact subintervals of the lifespan. -/
private lemma IsHeatSol.continuousOn_hnorm_aux {T : ℝ≥0∞} {y : ℝ → Field}
    (hy : IsHeatSol N G T y) {b : ℝ} (hbT : ENNReal.ofReal b < T) :
    ContinuousOn (fun t => hnorm 2 (y t)) (Icc 0 b) := by
  intro t₀ ht₀
  have hc : Tendsto (fun t => hnorm 2 (y t - y t₀)) (𝓝[Icc 0 b] t₀) (𝓝 0) :=
    (hy.cont t₀ ht₀.1 (ofReal_lt_of_mem ht₀ hbT)).mono_left
      (nhdsWithin_mono t₀ Icc_subset_Ici_self)
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hc
  filter_upwards [self_mem_nhdsWithin] with t ht
  have it := (hy.adm t ht.1 (ofReal_lt_of_mem ht hbT)).inH
  have it₀ := (hy.adm t₀ ht₀.1 (ofReal_lt_of_mem ht₀ hbT)).inH
  have h1 : hnorm 2 (y t) ≤ hnorm 2 (y t - y t₀) + hnorm 2 (y t₀) := by
    simpa using hnorm_add_le (it.sub it₀) it₀
  have h2 : hnorm 2 (y t₀) ≤ hnorm 2 (y t₀ - y t) + hnorm 2 (y t) := by
    simpa using hnorm_add_le (it₀.sub it) it
  rw [hnorm_sub_comm (f := y t₀) (g := y t)] at h2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- `‖y t‖₂` is bounded on compact subintervals of the lifespan. -/
private lemma IsHeatSol.exists_bound_aux {T : ℝ≥0∞} {y : ℝ → Field}
    (hy : IsHeatSol N G T y) {b : ℝ} (hbT : ENNReal.ofReal b < T) :
    ∃ C : ℝ, ∀ t ∈ Icc 0 b, hnorm 2 (y t) ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hy.continuousOn_hnorm_aux hbT)
  exact ⟨C, fun t ht => (le_abs_self _).trans (hC t ht)⟩

/-- Every mode of the nonlinearity along a solution is continuous in time. -/
private lemma IsHeatSol.continuousOn_nonlinear (hN : Majorized N) {T : ℝ≥0∞} {y : ℝ → Field}
    (hy : IsHeatSol N G T y) {b : ℝ} (hbT : ENNReal.ofReal b < T) (k : Mode) :
    ContinuousOn (fun t => N t (y t) (y t) k) (Icc 0 b) := by
  obtain ⟨C, hC⟩ := hy.exists_bound_aux hbT
  intro t₀ ht₀
  have hmz₀ : MZ 2 (y t₀) := (hy.adm t₀ ht₀.1 (ofReal_lt_of_mem ht₀ hbT)).mz
  have hc : Tendsto (fun t => hnorm 2 (y t - y t₀)) (𝓝[Icc 0 b] t₀) (𝓝 0) :=
    (hy.cont t₀ ht₀.1 (ofReal_lt_of_mem ht₀ hbT)).mono_left
      (nhdsWithin_mono t₀ Icc_subset_Ici_self)
  have hc2 : Tendsto (fun t => N t (y t₀) (y t₀) k) (𝓝[Icc 0 b] t₀)
      (𝓝 (N t₀ (y t₀) (y t₀) k)) := (hN.cont _ _ k hmz₀ hmz₀).continuousWithinAt
  have hbound : Tendsto (fun t => 2 * absk k * (hnorm 2 (y t - y t₀) * (C + C)) +
      ‖N t (y t₀) (y t₀) k - N t₀ (y t₀) (y t₀) k‖) (𝓝[Icc 0 b] t₀) (𝓝 0) := by
    simpa using ((hc.mul_const (C + C)).const_mul (2 * absk k)).add
      (tendsto_iff_norm_sub_tendsto_zero.1 hc2)
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hmz : MZ 2 (y t) := (hy.adm t ht.1 (ofReal_lt_of_mem ht hbT)).mz
  have h1 := hN.norm_sub_apply_le t hmz hmz₀ k
  have h2 : hnorm 2 (y t - y t₀) * (hnorm 2 (y t) + hnorm 2 (y t₀)) ≤
      hnorm 2 (y t - y t₀) * (C + C) :=
    mul_le_mul_of_nonneg_left (add_le_add (hC t ht) (hC t₀ ht₀)) (hnorm_nonneg _ _)
  have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg zero_le_two (absk_nonneg k))
  calc ‖N t (y t) (y t) k - N t₀ (y t₀) (y t₀) k‖
      ≤ ‖N t (y t) (y t) k - N t (y t₀) (y t₀) k‖ +
          ‖N t (y t₀) (y t₀) k - N t₀ (y t₀) (y t₀) k‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add_left (h1.trans h3) _

/-- The force lies in `H¹`, uniformly on compact subintervals of the lifespan. -/
private lemma IsHeatSol.exists_force_bound (hN : Majorized N) (hG : GoodForce G Γ) {T : ℝ≥0∞}
    {y : ℝ → Field} (hy : IsHeatSol N G T y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) :
    ∃ D : ℝ, ∀ t ∈ Icc 0 b, InH 1 (G t - N t (y t) (y t)) ∧
      hnorm 1 (G t - N t (y t) (y t)) ≤ D := by
  obtain ⟨C, hC⟩ := hy.exists_bound_aux hbT
  have hC0 : 0 ≤ C := (hnorm_nonneg 2 _).trans (hC 0 ⟨le_rfl, hb⟩)
  refine ⟨Γ + 2 ^ (2 : ℝ) * (c4 * C * C + C * (c4 * C)), fun t ht => ?_⟩
  have hmz : MZ 2 (y t) := (hy.adm t ht.1 (ofReal_lt_of_mem ht hbT)).mz
  have h := hN.hnorm_le t (σ := 2) (by norm_num) hmz hmz hmz hmz
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at h
  have hw : wiener (y t) ≤ c4 * C :=
    (wiener_le hmz).trans (mul_le_mul_of_nonneg_left (hC t ht) c4_pos.le)
  have hw0 := wiener_nonneg (y t)
  have hc4C : 0 ≤ c4 * C := mul_nonneg c4_pos.le hC0
  have hn0 := hnorm_nonneg 2 (y t)
  have hbd : wiener (y t) * hnorm 2 (y t) + hnorm 2 (y t) * wiener (y t) ≤
      c4 * C * C + C * (c4 * C) :=
    add_le_add (mul_le_mul hw (hC t ht) hn0 hc4C) (mul_le_mul (hC t ht) hw hw0 hC0)
  refine ⟨(hG.adm t).inH.sub h.1, (hnorm_sub_le (hG.adm t).inH h.1).trans ?_⟩
  exact add_le_add (hG.bd t) (h.2.trans (mul_le_mul_of_nonneg_left hbd (by positivity)))

/-- A solution gives a `HeatPair` at every level `σ ≤ 2`. -/
private lemma IsHeatSol.heatPair_aux (hN : Majorized N) (hG : GoodForce G Γ) {T : ℝ≥0∞}
    {y : ℝ → Field} (hy : IsHeatSol N G T y) {σ b : ℝ} (hσ : σ ≤ 2) (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) :
    HeatPair σ 0 b y (fun t => G t - N t (y t) (y t)) := by
  refine ⟨fun t ht => InH.mono hσ (hy.adm t ht.1 (ofReal_lt_of_mem ht hbT)).inH,
    fun k t ht => ?_, fun k => ?_, ?_⟩
  · have hd := (hy.mode k t ht.1 (ofReal_lt_of_mem ht hbT)).mono
      (Icc_subset_Ici_self : Icc (0 : ℝ) b ⊆ Ici 0)
    have e : (-(absSq k : ℝ) : ℂ) • y t k - N t (y t) (y t) k + G t k =
        (-(absSq k : ℝ) : ℂ) • y t k + (G t - N t (y t) (y t)) k := by
      simp only [Pi.sub_apply]
      abel
    rwa [e] at hd
  · exact (hG.continuous_mode k).continuousOn.sub (hy.continuousOn_nonlinear hN hbT k)
  · obtain ⟨D, hD⟩ := hy.exists_force_bound hN hG hb hbT
    have hle : σ - 1 ≤ 1 := by linarith
    calc ∫⁻ t in Icc 0 b, hsE (σ - 1) (G t - N t (y t) (y t))
        ≤ ∫⁻ _ in Icc 0 b, ENNReal.ofReal (D ^ 2) := by
          refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
          obtain ⟨hi, hn⟩ := hD t ht
          rw [hsE_eq_ofReal (InH.mono hle hi)]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hnorm_nonneg _ _)
            ((hnorm_mono hle hi).trans hn) 2)
      _ < ∞ := by
          rw [setLIntegral_const, Real.volume_Icc]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- A solution gives a `HeatPair` at level `σ = 2`, with force `-N(y,y) + G`, on compact
subintervals of its lifespan. -/
theorem IsHeatSol.heatPair (hN : Majorized N) (hG : GoodForce G Γ) {T : ℝ≥0∞} {y : ℝ → Field}
    (hy : IsHeatSol N G T y) {b : ℝ} (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    HeatPair 2 0 b y (fun t => G t - N t (y t) (y t)) :=
  hy.heatPair_aux hN hG le_rfl hb hbT

/-- Same at level `σ = 1` and `σ = 0`. -/
theorem IsHeatSol.heatPair_low (hN : Majorized N) (hG : GoodForce G Γ) {T : ℝ≥0∞} {y : ℝ → Field}
    (hy : IsHeatSol N G T y) {σ b : ℝ} (hσ : σ = 0 ∨ σ = 1) (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) :
    HeatPair σ 0 b y (fun t => G t - N t (y t) (y t)) := by
  refine hy.heatPair_aux hN hG ?_ hb hbT
  rcases hσ with rfl | rfl <;> norm_num

/-- `t ↦ ‖y t‖₂` is continuous on compact subintervals of the lifespan. -/
theorem IsHeatSol.continuousOn_hnorm2 {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y) {b : ℝ}
    (hbT : ENNReal.ofReal b < T) : ContinuousOn (fun t => hnorm 2 (y t)) (Icc 0 b) :=
  hy.continuousOn_hnorm_aux hbT

/-- `‖y t‖₂` is bounded on compact subintervals of the lifespan. -/
theorem IsHeatSol.exists_bound {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y) {b : ℝ}
    (hbT : ENNReal.ofReal b < T) : ∃ C : ℝ, ∀ t ∈ Icc 0 b, hnorm 2 (y t) ≤ C :=
  hy.exists_bound_aux hbT

end OVNS
