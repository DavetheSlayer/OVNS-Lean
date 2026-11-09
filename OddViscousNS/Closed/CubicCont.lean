import OddViscousNS.Closed.Gram
import OddViscousNS.Majorant

/-!
# Continuity of the cubic on `H²`

`cubic u = ∑_k h_k Re⟨u_k, B(u,u)_k⟩` is a trilinear form; with `h_k ≤ |k|²`,
`|cubic a − cubic b| ≤ ‖a − b‖₁ ‖B(a,a)‖₁ + ‖b‖₁ ‖B(a,a) − B(b,b)‖₁` and the product estimates of
`OddViscousNS/Majorant.lean` (`hnorm_Qm_le`), so `cubic` is Lipschitz on `H²`-balls, and the cubic
along an `H²`-continuous curve is continuous in time.
-/

open scoped ENNReal
open Set Filter Topology

namespace OVNS

/-- The multiplier identically equal to one. -/
private def oneM : Mult := fun _ _ _ _ _ => 1

private lemma oneM_bdd : oneM.Bdd := fun _ _ _ _ _ => by simp [oneM]

private lemma oneM_real : oneM.Real := fun _ _ _ _ _ => by simp [oneM]

private lemma majorized_oneM : Majorized (fun _ => Qm oneM) :=
  majorized_Qm (fun _ => oneM) (fun _ => oneM_bdd) (fun _ => oneM_real)
    fun _ _ _ _ _ => continuous_const

private lemma convec_eq_Qm {u : Field} (hu : Adm 2 u) : convec u = Qm oneM u u := by
  rw [← Bsym_self hu.mz, ← Qm_one hu hu]
  rfl

private lemma hm_nonneg (k : Mode) : 0 ≤ hm k := by
  unfold hm
  by_cases h : nsq k = 0
  · rw [h]; simp [hmet]
  · exact (hmet_pos (Nat.one_le_iff_ne_zero.2 h)).le

private lemma hm_le (k : Mode) : hm k ≤ absSq k := by
  rw [← nsq_cast]
  exact hmet_upper _

private lemma MZ.sub'' {s : ℝ} {x y : Field} (hx : MZ s x) (hy : MZ s y) : MZ s (x - y) :=
  ⟨hx.inH.sub hy.inH, by simp [hx.mean, hy.mean]⟩

/-- Cauchy-Schwarz for nonnegative real series. -/
private lemma cs_tsum' {a b : Mode → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (ha2 : Summable fun k => a k ^ 2) (hb2 : Summable fun k => b k ^ 2) :
    Summable (fun k => a k * b k) ∧
      ∑' k, a k * b k ≤ Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, b k ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have ha2' : Summable fun k => a k ^ (2 : ℝ) := by simpa only [Real.rpow_two] using ha2
  have hb2' : Summable fun k => b k ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hb2
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq ha hb ha2' hb2'
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using h

private lemma sobWeight_two_eq {k : Mode} (hk : k ≠ 0) : sobWeight 2 k = absSq k ^ 2 := by
  simp only [sobWeight, hk, ↓reduceIte]
  rw [absk, show (2 : ℝ) * 2 = (4 : ℕ) by norm_num, Real.rpow_natCast,
    show 4 = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (absSq_nonneg k)]

/-- `∑ |k|² |x_k| |F_k| ≤ ‖x‖₂ ‖F‖₀`. -/
private lemma cs_absSq {x F : Field} (hx : MZ 2 x) (hF : MZ 0 F) :
    Summable (fun k => absSq k * ‖x k‖ * ‖F k‖) ∧
      ∑' k, absSq k * ‖x k‖ * ‖F k‖ ≤ hnorm 2 x * hnorm 0 F := by
  have ea : ∀ k, (absSq k * ‖x k‖) ^ 2 = sobWeight 2 k * ‖x k‖ ^ 2 := fun k => by
    by_cases hk : k = 0
    · subst hk; simp [hx.mean]
    · rw [sobWeight_two_eq hk]; ring
  have eb : ∀ k, ‖F k‖ ^ 2 = sobWeight 0 k * ‖F k‖ ^ 2 := fun k => by
    by_cases hk : k = 0
    · subst hk; simp [hF.mean]
    · simp [sobWeight, hk]
  have ha2 : Summable fun k => (absSq k * ‖x k‖) ^ 2 := by
    rw [funext ea]; exact hx.inH
  have hb2 : Summable fun k => ‖F k‖ ^ 2 := by
    rw [show (fun k => ‖F k‖ ^ 2) = fun k => sobWeight 0 k * ‖F k‖ ^ 2 from funext eb]
    exact hF.inH
  have h := cs_tsum' (a := fun k => absSq k * ‖x k‖) (b := fun k => ‖F k‖)
    (fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _)) (fun k => norm_nonneg _) ha2 hb2
  rw [funext ea, show (∑' k, ‖F k‖ ^ 2) = ∑' k, sobWeight 0 k * ‖F k‖ ^ 2 from
    tsum_congr eb] at h
  exact h

private lemma inH0_Qm {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) : MZ 0 (Qm oneM f g) :=
  ⟨(hnorm_Qm_zero_le oneM_bdd hf hg).1, majorized_oneM.mean 0 f g hf hg⟩

private lemma hnorm0_Qm_le {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) :
    hnorm 0 (Qm oneM f g) ≤ 2 * c4 * hnorm 2 f * hnorm 2 g := by
  have h := (hnorm_Qm_zero_le oneM_bdd hf hg).2
  have h1f := hnorm_mono (show (1 : ℝ) ≤ 2 by norm_num) hf.inH
  have h1g := hnorm_mono (show (1 : ℝ) ≤ 2 by norm_num) hg.inH
  have wf := wiener_le hf
  have wg := wiener_le hg
  have := hnorm_nonneg 1 f
  have := hnorm_nonneg 1 g
  have := hnorm_nonneg 2 f
  have := hnorm_nonneg 2 g
  have := wiener_nonneg f
  have := wiener_nonneg g
  have hc := c4_pos.le
  calc hnorm 0 (Qm oneM f g) ≤ hnorm 1 f * wiener g + wiener f * hnorm 1 g := h
    _ ≤ hnorm 2 f * (c4 * hnorm 2 g) + (c4 * hnorm 2 f) * hnorm 2 g := by
        gcongr
    _ = 2 * c4 * hnorm 2 f * hnorm 2 g := by ring

private lemma norm_term_le (x F : V3) (k : Mode) :
    ‖hm k * (inner ℂ x F).re‖ ≤ absSq k * ‖x‖ * ‖F‖ := by
  rw [norm_mul, Real.norm_of_nonneg (hm_nonneg k), mul_assoc]
  exact mul_le_mul (hm_le k)
    ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _))
    (norm_nonneg _) (absSq_nonneg k)

private lemma summable_term {u : Field} (hu : MZ 2 u) :
    Summable fun k => hm k * (inner ℂ (u k) (Qm oneM u u k)).re :=
  Summable.of_norm_bounded (cs_absSq hu (inH0_Qm hu hu)).1
    fun k => norm_term_le (u k) (Qm oneM u u k) k

/-- A locally Lipschitz difference estimate for the cubic on admissible `H²` fields. -/
theorem cubic_sub_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ {a b : Field}, Adm 2 a → Adm 2 b →
    |cubic a - cubic b| ≤ K * (hnorm 2 a + hnorm 2 b) ^ 2 * hnorm 2 (a - b) := by
  refine ⟨2 * c4, by linarith [c4_pos], fun {a b} ha hb => ?_⟩
  have ma := ha.mz
  have mb := hb.mz
  have md : MZ 2 (a - b) := ma.sub'' mb
  have hdiff : Qm oneM a a - Qm oneM b b = Qm oneM (a - b) a + Qm oneM b (a - b) := by
    rw [majorized_oneM.sub_left 0 a b a ma mb ma, majorized_oneM.sub_right 0 b a b mb ma mb]
    abel
  have hpt : ∀ k, hm k * (inner ℂ (a k) (Qm oneM a a k)).re -
      hm k * (inner ℂ (b k) (Qm oneM b b k)).re =
      hm k * (inner ℂ ((a - b) k) (Qm oneM a a k)).re +
        hm k * (inner ℂ (b k) (Qm oneM (a - b) a k)).re +
        hm k * (inner ℂ (b k) (Qm oneM b (a - b) k)).re := fun k => by
    have e : Qm oneM b b k = Qm oneM a a k - (Qm oneM (a - b) a k + Qm oneM b (a - b) k) := by
      rw [← Pi.add_apply, ← hdiff]; simp
    rw [e, Pi.sub_apply, inner_sub_left, inner_sub_right, inner_add_right]
    simp only [Complex.sub_re, Complex.add_re]
    ring
  obtain ⟨s1, l1⟩ := cs_absSq md (inH0_Qm ma ma)
  obtain ⟨s2, l2⟩ := cs_absSq mb (inH0_Qm md ma)
  obtain ⟨s3, l3⟩ := cs_absSq mb (inH0_Qm mb md)
  have hsum := (s1.add s2).add s3
  have hcub : cubic a - cubic b = ∑' k, (hm k * (inner ℂ (a k) (Qm oneM a a k)).re -
      hm k * (inner ℂ (b k) (Qm oneM b b k)).re) := by
    rw [cubic, cubic, convec_eq_Qm ha, convec_eq_Qm hb,
      (summable_term ma).tsum_sub (summable_term mb)]
  have hbd : |cubic a - cubic b| ≤ ∑' k, (absSq k * ‖(a - b) k‖ * ‖Qm oneM a a k‖ +
      absSq k * ‖b k‖ * ‖Qm oneM (a - b) a k‖ +
        absSq k * ‖b k‖ * ‖Qm oneM b (a - b) k‖) := by
    rw [hcub, ← Real.norm_eq_abs]
    refine tsum_of_norm_bounded hsum.hasSum fun k => ?_
    rw [hpt k]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (norm_term_le _ _ k) (norm_term_le _ _ k))) (norm_term_le _ _ k))
  rw [(s1.add s2).tsum_add s3, s1.tsum_add s2] at hbd
  have q1 := hnorm0_Qm_le ma ma
  have q2 := hnorm0_Qm_le md ma
  have q3 := hnorm0_Qm_le mb md
  have := hnorm_nonneg 2 a
  have := hnorm_nonneg 2 b
  have := hnorm_nonneg 2 (a - b)
  have hc := c4_pos.le
  have h0 := hnorm_nonneg 0 (Qm oneM a a)
  calc |cubic a - cubic b|
      ≤ hnorm 2 (a - b) * hnorm 0 (Qm oneM a a) + hnorm 2 b * hnorm 0 (Qm oneM (a - b) a) +
        hnorm 2 b * hnorm 0 (Qm oneM b (a - b)) := by linarith
    _ ≤ hnorm 2 (a - b) * (2 * c4 * hnorm 2 a * hnorm 2 a) +
        hnorm 2 b * (2 * c4 * hnorm 2 (a - b) * hnorm 2 a) +
        hnorm 2 b * (2 * c4 * hnorm 2 b * hnorm 2 (a - b)) := by gcongr
    _ ≤ 2 * c4 * (hnorm 2 a + hnorm 2 b) ^ 2 * hnorm 2 (a - b) := by
        have : 0 ≤ 2 * c4 * hnorm 2 (a - b) * (hnorm 2 a * hnorm 2 b) := by positivity
        nlinarith

private lemma sol_sub' {x z : Field} (hx : IsSolenoidal x) (hz : IsSolenoidal z) :
    IsSolenoidal (x - z) := fun k => by
  have h1 := hx k
  have h2 := hz k
  simp only [dotM, Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib] at h1 h2 ⊢
  rw [h1, h2, sub_zero]

/-- The cubic of the filtered field along an `H²`-continuous admissible curve is continuous. -/
theorem continuousOn_cubic_rotF {r : ℝ} {y : ℝ → Field} {b : ℝ}
    (hadm : ∀ t ∈ Icc 0 b, Adm 2 (y t))
    (hcont : ∀ t₀ ∈ Icc 0 b, Tendsto (fun t => hnorm 2 (y t - y t₀)) (𝓝[Icc 0 b] t₀) (𝓝 0)) :
    ContinuousOn (fun t => cubic (rotF (r * t) (y t))) (Icc 0 b) := by
  obtain ⟨K, hK, hKb⟩ := cubic_sub_le
  intro t₀ ht₀
  set A : ℝ → Field := fun t => rotF (r * t) (y t) with hA
  set D : ℝ → ℝ := fun t => hnorm 2 (A t - A t₀) with hD
  have hA2 : ∀ t ∈ Icc 0 b, Adm 2 (A t) := fun t ht => (hadm t ht).rotF _
  have hrot : Tendsto (fun t => hnorm 2 (rotF (r * t) (y t₀) - rotF (r * t₀) (y t₀)))
      (𝓝[Icc 0 b] t₀) (𝓝 0) := by
    have h := tendsto_hnorm_rotF (hadm t₀ ht₀).inH (hadm t₀ ht₀).sol (r * t₀)
    have hc : Tendsto (fun t : ℝ => r * t) (𝓝[Icc 0 b] t₀) (𝓝 (r * t₀)) :=
      ((continuous_const.mul continuous_id).tendsto t₀).mono_left nhdsWithin_le_nhds
    exact h.comp hc
  have hDle : ∀ t ∈ Icc 0 b, D t ≤ hnorm 2 (y t - y t₀) +
      hnorm 2 (rotF (r * t) (y t₀) - rotF (r * t₀) (y t₀)) := fun t ht => by
    have e : A t - A t₀ = rotF (r * t) (y t - y t₀) +
        (rotF (r * t) (y t₀) - rotF (r * t₀) (y t₀)) := by
      rw [rotF_sub]; simp only [hA]; abel
    have i1 : InH 2 (rotF (r * t) (y t - y t₀)) := by
      rw [rotF_sub]
      exact ((hadm t ht).rotF _).inH.sub ((hadm t₀ ht₀).rotF _).inH
    have i2 : InH 2 (rotF (r * t) (y t₀) - rotF (r * t₀) (y t₀)) :=
      ((hadm t₀ ht₀).rotF _).inH.sub ((hadm t₀ ht₀).rotF _).inH
    simp only [hD]
    rw [e, ← hnorm_rotF (r * t) (sol_sub' (hadm t ht).sol (hadm t₀ ht₀).sol)]
    exact hnorm_add_le i1 i2
  have hD0 : Tendsto D (𝓝[Icc 0 b] t₀) (𝓝 0) := by
    have hs := (hcont t₀ ht₀).add hrot
    rw [add_zero] at hs
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
      (.of_forall fun t => hnorm_nonneg _ _)
      (eventually_nhdsWithin_of_forall hDle)
  set c := hnorm 2 (A t₀)
  have hR : Tendsto (fun t => K * (c + D t + c) ^ 2 * D t) (𝓝[Icc 0 b] t₀) (𝓝 0) := by
    have := ((tendsto_const_nhds (x := c)).add hD0).add (tendsto_const_nhds (x := c))
    have h2 := ((tendsto_const_nhds (x := K)).mul (this.pow 2)).mul hD0
    simpa using h2
  rw [ContinuousWithinAt, ← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun t ht => ?_) hR
  rw [Real.norm_eq_abs]
  refine (hKb (hA2 t ht) (hA2 t₀ ht₀)).trans ?_
  have hn : hnorm 2 (A t) ≤ c + D t := by
    have := hnorm_add_le (hA2 t₀ ht₀).inH ((hA2 t ht).inH.sub (hA2 t₀ ht₀).inH)
    rwa [add_sub_cancel] at this
  have := hnorm_nonneg 2 (A t)
  have := hnorm_nonneg 2 (A t₀)
  have hD := hnorm_nonneg 2 (A t - A t₀)
  gcongr

end OVNS
