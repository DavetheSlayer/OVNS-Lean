import OddViscousNS.LocalTheory
import OddViscousNS.Filtered

/-! # Higher regularity (`Lemma fg:lem:lwp(e)`, `Proposition prop:smooth`)

`heat_gain`: a mode-wise heat equation with `F ∈ L²_t H^{σ-1}` and `c(a) ∈ H^σ` stays in `H^σ`,
gains `L²_t H^{σ+1}`, and is continuous in `H^σ`.  Iterating from `σ = 2` gives persistence. -/

open MeasureTheory Set
open scoped ENNReal Topology
noncomputable section
namespace OVNS

/-! ### Truncation to finitely many modes -/

/-- The energy of the modes in `S`. -/
private def trE (s : ℝ) (S : Finset Mode) (u : Field) : ℝ :=
  ∑ k ∈ S, sobWeight s k * ‖u k‖ ^ 2

/-- Restriction of a field to the modes in `S`. -/
private def trunc (S : Finset Mode) (u : Field) : Field := fun k => if k ∈ S then u k else 0

private lemma inH_trunc (s : ℝ) (S : Finset Mode) (u : Field) : InH s (trunc S u) :=
  summable_of_ne_finset_zero (s := S) fun k hk => by simp [trunc, hk]

private lemma hnorm_sq_trunc (s : ℝ) (S : Finset Mode) (u : Field) :
    hnorm s (trunc S u) ^ 2 = trE s S u := by
  rw [hnorm_sq (inH_trunc s S u), tsum_eq_sum (s := S) fun k hk => by simp [trunc, hk]]
  exact Finset.sum_congr rfl fun k hk => by simp [trunc, hk]

private lemma trE_nonneg (s : ℝ) (S : Finset Mode) (u : Field) : 0 ≤ trE s S u :=
  Finset.sum_nonneg fun k _ => mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _)

private lemma hsE_trunc_le (s : ℝ) (S : Finset Mode) (u : Field) :
    hsE s (trunc S u) ≤ hsE s u := by
  refine tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_left ?_ (sobWeight_nonneg s k)
  by_cases hk : k ∈ S <;> simp [trunc, hk]

private lemma continuousOn_trE {s a b : ℝ} {u : ℝ → Field}
    (hu : ∀ k, ContinuousOn (fun t => u t k) (Icc a b)) (S : Finset Mode) :
    ContinuousOn (fun t => trE s S (u t)) (Icc a b) :=
  continuousOn_finsetSum S fun k _ => continuousOn_const.mul ((hu k).norm.pow 2)

/-- The truncation of a mode-wise heat equation is a `HeatPair` at every level. -/
private lemma heatPair_trunc {σ a b : ℝ} {c F : ℝ → Field}
    (hmode : ∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => c s k)
      ((-(absSq k : ℝ) : ℂ) • c t k + F t k) (Icc a b) t)
    (hFc : ∀ k, ContinuousOn (fun t => F t k) (Icc a b))
    (hF : ∫⁻ t in Icc a b, hsE (σ - 1) (F t) < ∞) (S : Finset Mode) :
    HeatPair σ a b (fun t => trunc S (c t)) (fun t => trunc S (F t)) := by
  refine ⟨fun t _ => inH_trunc σ S _, fun k t ht => ?_, fun k => ?_, ?_⟩
  · by_cases hk : k ∈ S
    · simpa only [trunc, hk, ite_true] using hmode k t ht
    · simpa only [trunc, hk, ite_false, smul_zero, add_zero] using
        hasDerivWithinAt_const t (Icc a b) (0 : V3)
  · by_cases hk : k ∈ S
    · simpa only [trunc, hk, ite_true] using hFc k
    · simpa only [trunc, hk, ite_false] using continuousOn_const
  · exact (lintegral_mono fun t => hsE_trunc_le _ S _).trans_lt hF

/-- The truncated energy inequality. -/
private lemma trE_le {σ a b : ℝ} (hab : a ≤ b) {c F : ℝ → Field}
    (hmode : ∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => c s k)
      ((-(absSq k : ℝ) : ℂ) • c t k + F t k) (Icc a b) t)
    (hFc : ∀ k, ContinuousOn (fun t => F t k) (Icc a b))
    (hF : ∫⁻ t in Icc a b, hsE (σ - 1) (F t) < ∞) (S : Finset Mode) :
    trE σ S (c b) ≤ trE σ S (c a) + ∫ u in a..b, trE (σ - 1) S (F u) := by
  have h := heatPair_trunc hmode hFc hF S
  have hid := h.energy_identity le_rfl hab le_rfl
  rw [hnorm_sq_trunc, hnorm_sq_trunc] at hid
  have hD := h.intervalIntegrable_dissipation hab
  have hP := h.intervalIntegrable_pair hab
  have hQ : IntervalIntegrable (fun u => trE (σ - 1) S (F u)) volume a b :=
    (continuousOn_trE hFc S).intervalIntegrable_of_Icc hab
  have hle : ∫ u in a..b, pair σ (trunc S (c u)) (trunc S (F u)) ≤
      ∫ u in a..b, (hnorm (σ + 1) (trunc S (c u)) ^ 2 + trE (σ - 1) S (F u) / 2) := by
    refine intervalIntegral.integral_mono_on hab hP (hD.add (hQ.div_const 2)) fun u _ => ?_
    have h1 := (pair_le (inH_trunc (σ + 1) S (c u)) (inH_trunc (σ - 1) S (F u))).2
    have h2 := hnorm_sq_trunc (σ - 1) S (F u)
    have h3 := le_of_abs_le h1
    rw [← h2]
    nlinarith [sq_nonneg (hnorm (σ + 1) (trunc S (c u)) - hnorm (σ - 1) (trunc S (F u))),
      sq_nonneg (hnorm (σ + 1) (trunc S (c u)))]
  rw [intervalIntegral.integral_add hD (hQ.div_const 2), intervalIntegral.integral_div] at hle
  linarith

/-- The energy at the endpoint is controlled by the datum and the force. -/
private lemma hsE_le {σ a b : ℝ} (hab : a ≤ b) {c F : ℝ → Field}
    (hmode : ∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => c s k)
      ((-(absSq k : ℝ) : ℂ) • c t k + F t k) (Icc a b) t)
    (hFc : ∀ k, ContinuousOn (fun t => F t k) (Icc a b))
    (hF : ∫⁻ t in Icc a b, hsE (σ - 1) (F t) < ∞) :
    hsE σ (c b) ≤ hsE σ (c a) + ∫⁻ t in Icc a b, hsE (σ - 1) (F t) := by
  have hof : ∀ (s : ℝ) (S : Finset Mode) (u : Field),
      ENNReal.ofReal (trE s S u) ≤ hsE s u := fun s S u => by
    rw [trE, ENNReal.ofReal_sum_of_nonneg fun k _ =>
      mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _)]
    exact sum_le_tsum S
  rw [hsE, tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg (sobWeight_nonneg σ k) (sq_nonneg _)]
  change ENNReal.ofReal (trE σ S (c b)) ≤ _
  have hQ : ENNReal.ofReal (∫ u in a..b, trE (σ - 1) S (F u)) =
      ∫⁻ t in Icc a b, ENNReal.ofReal (trE (σ - 1) S (F t)) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal (continuousOn_trE hFc S).integrableOn_Icc
      (.of_forall fun t => trE_nonneg _ _ _)
  calc ENNReal.ofReal (trE σ S (c b))
      ≤ ENNReal.ofReal (trE σ S (c a) + ∫ u in a..b, trE (σ - 1) S (F u)) :=
        ENNReal.ofReal_le_ofReal (trE_le hab hmode hFc hF S)
    _ ≤ ENNReal.ofReal (trE σ S (c a)) + ENNReal.ofReal (∫ u in a..b, trE (σ - 1) S (F u)) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := by
        rw [hQ]
        exact add_le_add (hof _ _ _) (lintegral_mono fun t => hof _ _ _)

/-- The parabolic regularity gain, assuming only a priori `H^{σ-1}` membership (no `InH σ`). -/
theorem heat_gain {σ a b : ℝ} (_hab : a ≤ b) {c F : ℝ → Field}
    (hmode : ∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => c s k)
      ((-(absSq k : ℝ) : ℂ) • c t k + F t k) (Icc a b) t)
    (hFc : ∀ k, ContinuousOn (fun t => F t k) (Icc a b))
    (hF : ∫⁻ t in Icc a b, hsE (σ - 1) (F t) < ∞) (h0 : InH σ (c a)) :
    HeatPair σ a b c F := by
  refine ⟨fun t ht => ?_, hmode, hFc, hF⟩
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hl := (lintegral_mono_set hsub).trans_lt hF
  refine inH_iff_hsE_lt_top.2 ((hsE_le ht.1 (fun k u hu => (hmode k u (hsub hu)).mono hsub)
    (fun k => (hFc k).mono hsub) hl).trans_lt ?_)
  exact ENNReal.add_lt_top.2 ⟨inH_iff_hsE_lt_top.1 h0, hl⟩

/-- The tail bound: the distance is controlled by finitely many modes and two tails. -/
private lemma hnorm_sub_sq_le {s : ℝ} {f g : Field} (hf : InH s f) (hg : InH s g)
    (S : Finset Mode) :
    hnorm s (f - g) ^ 2 ≤ trE s S (f - g) + 2 * (hnorm s f ^ 2 - trE s S f) +
      2 * (hnorm s g ^ 2 - trE s S g) := by
  have hfg : InH s (f - g) := hf.sub hg
  rw [hnorm_sq hfg, hnorm_sq hf, hnorm_sq hg]
  have hf' : Summable fun k => sobWeight s k * ‖f k‖ ^ 2 := hf
  have hg' : Summable fun k => sobWeight s k * ‖g k‖ ^ 2 := hg
  have hfg' : Summable fun k => sobWeight s k * ‖(f - g) k‖ ^ 2 := hfg
  have hψ := (hf'.mul_left 2).add (hg'.mul_left 2)
  have hnn : ∀ k, 0 ≤ 2 * (sobWeight s k * ‖f k‖ ^ 2) + 2 * (sobWeight s k * ‖g k‖ ^ 2) -
      sobWeight s k * ‖(f - g) k‖ ^ 2 := fun k => by
    have h1 : ‖(f - g) k‖ ≤ ‖f k‖ + ‖g k‖ := norm_sub_le _ _
    have h2 : ‖(f - g) k‖ ^ 2 ≤ (‖f k‖ + ‖g k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := mul_le_mul_of_nonneg_left
      (show ‖(f - g) k‖ ^ 2 ≤ 2 * ‖f k‖ ^ 2 + 2 * ‖g k‖ ^ 2 by
        nlinarith [sq_nonneg (‖f k‖ - ‖g k‖)]) (sobWeight_nonneg s k)
    linarith
  have hsum := (hψ.sub hfg').sum_le_tsum S fun k _ => hnn k
  rw [hψ.tsum_sub hfg', (hf'.mul_left 2).tsum_add (hg'.mul_left 2), tsum_mul_left, tsum_mul_left,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  simp only [trE]
  linarith

/-- Strong `H^σ` continuity of a `HeatPair`. -/
theorem HeatPair.tendsto_hnorm {σ a b : ℝ} {c F : ℝ → Field} (h : HeatPair σ a b c F)
    (hab : a ≤ b) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) :
    Filter.Tendsto (fun t => hnorm σ (c t - c t₀)) (𝓝[Icc a b] t₀) (𝓝 0) := by
  have hcm : ∀ k, ContinuousOn (fun t => c t k) (Icc a b) := fun k t ht =>
    (h.mode k t ht).continuousWithinAt
  have hi₀ : InH σ (c t₀) := h.inH t₀ ht₀
  have hsq : Filter.Tendsto (fun t => hnorm σ (c t - c t₀) ^ 2) (𝓝[Icc a b] t₀) (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have hlim : Filter.Tendsto (fun S => trE σ S (c t₀)) Filter.atTop
        (𝓝 (hnorm σ (c t₀) ^ 2)) := by
      rw [hnorm_sq hi₀]
      exact hi₀.hasSum
    obtain ⟨S, hS⟩ := (hlim.eventually (lt_mem_nhds
      (show hnorm σ (c t₀) ^ 2 - ε / 8 < hnorm σ (c t₀) ^ 2 by linarith))).exists
    have hsubm : ∀ k, ContinuousOn (fun t => (c t - c t₀) k) (Icc a b) := fun k => by
      exact (hcm k).sub continuousOn_const
    have hB : ContinuousOn (fun t => trE σ S (c t - c t₀) +
        2 * (hnorm σ (c t) ^ 2 - trE σ S (c t)) +
        2 * (hnorm σ (c t₀) ^ 2 - trE σ S (c t₀))) (Icc a b) :=
      ((continuousOn_trE hsubm S).add (continuousOn_const.mul
        ((h.continuousOn_hnorm_sq hab).sub (continuousOn_trE hcm S)))).add continuousOn_const
    have h0 : trE σ S (c t₀ - c t₀) = 0 := by simp [trE]
    have hlt : ∀ᶠ t in 𝓝[Icc a b] t₀, trE σ S (c t - c t₀) +
        2 * (hnorm σ (c t) ^ 2 - trE σ S (c t)) +
        2 * (hnorm σ (c t₀) ^ 2 - trE σ S (c t₀)) < ε :=
      (hB t₀ ht₀).eventually (gt_mem_nhds (by beta_reduce; rw [h0]; linarith))
    filter_upwards [hlt, self_mem_nhdsWithin] with t ht hmem
    have h1 := hnorm_sub_sq_le (h.inH t hmem) hi₀ S
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)]
    linarith
  have := hsq.sqrt
  simpa [Real.sqrt_sq (hnorm_nonneg σ _)] using this

variable {N : ℝ → Field → Field → Field} {y : ℝ → Field}

/-- The force `-N(y,y)`, in the form produced by `G = 0`. -/
private def nlF (N : ℝ → Field → Field → Field) (y : ℝ → Field) : ℝ → Field :=
  fun t => (0 : Field) - N t (y t) (y t)

/-- One step of the regularity ladder. -/
private lemma step (hN : Majorized N) {σ σ' b C : ℝ} (hb : 0 ≤ b)
    (hmz : ∀ t ∈ Icc 0 b, MZ 2 (y t)) (hC : ∀ t ∈ Icc 0 b, hnorm 2 (y t) ≤ C) (hσ2 : 2 ≤ σ')
    (hσ : σ' ≤ σ + 1) (h : HeatPair σ 0 b y (nlF N y)) (h0 : InH σ' (y 0)) :
    HeatPair σ' 0 b y (nlF N y) := by
  refine heat_gain hb h.mode h.force_cont ?_ h0
  set K : ℝ := (2 ^ σ' * (2 * (c4 * C))) ^ 2 with hK
  have hC0 : 0 ≤ C := (hnorm_nonneg 2 _).trans (hC 0 ⟨le_rfl, hb⟩)
  have hbd : ∀ᵐ t ∂(volume.restrict (Icc 0 b)),
      hsE (σ' - 1) (nlF N y t) ≤ ENNReal.ofReal K * hsE (σ + 1) (y t) := by
    filter_upwards [h.ae_inH hb, ae_restrict_mem measurableSet_Icc] with t ht1 ht
    have hm2 := hmz t ht
    have hm' : MZ σ' (y t) := ⟨ht1.mono hσ, hm2.mean⟩
    obtain ⟨hi, hn⟩ := hN.hnorm_le t (σ := σ') (by linarith) hm' hm' hm2 hm2
    have e : hsE (σ' - 1) (nlF N y t) = hsE (σ' - 1) (N t (y t) (y t)) := by
      simp [hsE, nlF]
    rw [e, hsE_eq_ofReal hi, hsE_eq_ofReal ht1, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw : wiener (y t) ≤ c4 * C :=
      (wiener_le hm2).trans (mul_le_mul_of_nonneg_left (hC t ht) c4_pos.le)
    have hw0 := wiener_nonneg (y t)
    have hnm : hnorm σ' (y t) ≤ hnorm (σ + 1) (y t) := hnorm_mono hσ ht1
    have hn0 := hnorm_nonneg σ' (y t)
    have hm0 := hnorm_nonneg (σ + 1) (y t)
    have hc0 : 0 ≤ c4 * C := mul_nonneg c4_pos.le hC0
    have hle : wiener (y t) * hnorm σ' (y t) + hnorm σ' (y t) * wiener (y t) ≤
        2 * (c4 * C) * hnorm (σ + 1) (y t) := by
      have := mul_le_mul hw hnm hn0 hc0
      linarith
    have hX : hnorm (σ' - 1) (N t (y t) (y t)) ≤
        2 ^ σ' * (2 * (c4 * C)) * hnorm (σ + 1) (y t) := by
      refine hn.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    calc hnorm (σ' - 1) (N t (y t) (y t)) ^ 2
        ≤ (2 ^ σ' * (2 * (c4 * C)) * hnorm (σ + 1) (y t)) ^ 2 :=
          pow_le_pow_left₀ (hnorm_nonneg _ _) hX 2
      _ = K * hnorm (σ + 1) (y t) ^ 2 := by rw [hK]; ring
  calc ∫⁻ t in Icc 0 b, hsE (σ' - 1) (nlF N y t)
      ≤ ∫⁻ t in Icc 0 b, ENNReal.ofReal K * hsE (σ + 1) (y t) := lintegral_mono_ae hbd
    _ = ENNReal.ofReal K * ∫⁻ t in Icc 0 b, hsE (σ + 1) (y t) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((h.dissipation_lt_top hb).trans_lt
        (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, h.force_l2⟩))

/-- The regularity ladder for an unforced global solution, on every compact time interval. -/
private lemma ladder {Γ : ℝ} (hN : Majorized N) (hG : GoodForce (fun _ => 0) Γ)
    (hy : IsHeatSol N (fun _ => 0) ⊤ y) {s : ℝ} (hs : 2 ≤ s) (h0 : InH s (y 0)) {b : ℝ}
    (hb : 0 ≤ b) : HeatPair s 0 b y (nlF N y) := by
  have hbT : ENNReal.ofReal b < ⊤ := ENNReal.ofReal_lt_top
  have hb2 := hy.heatPair hN hG hb hbT
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (hb2.continuousOn_hnorm_sq hb)
  have hC : ∀ t ∈ Icc 0 b, hnorm 2 (y t) ≤ C₀ + 1 := fun t ht => by
    have h := hC₀ t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
    nlinarith [sq_nonneg (hnorm 2 (y t) - 1), sq_nonneg (hnorm 2 (y t))]
  have hmz : ∀ t ∈ Icc 0 b, MZ 2 (y t) := fun t ht =>
    (hy.adm t ht.1 ENNReal.ofReal_lt_top).mz
  have hlad : ∀ n : ℕ, HeatPair (min (2 + (n : ℝ)) s) 0 b y (nlF N y) := by
    intro n
    induction n with
    | zero =>
      have e : min (2 + ((0 : ℕ) : ℝ)) s = 2 := by simpa using hs
      rw [e]
      exact hb2
    | succ n ih =>
      refine step hN hb hmz hC (le_min (by linarith [(n + 1).cast_nonneg (α := ℝ)]) hs) ?_ ih
        (h0.mono (min_le_right _ _))
      push_cast
      rcases le_total (2 + (n : ℝ)) s with hl | hl
      · rw [min_eq_left hl]
        exact (min_le_left _ _).trans (by linarith)
      · rw [min_eq_right hl]
        exact (min_le_right _ _).trans (by linarith)
  have e : min (2 + ((⌈s⌉₊ : ℕ) : ℝ)) s = s :=
    min_eq_right (by linarith [Nat.le_ceil s])
  simpa only [e] using hlad ⌈s⌉₊

/-- A time shift of an unforced global solution is an unforced global solution. -/
private lemma shifted (hy : IsHeatSol N (fun _ => 0) ⊤ y) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    IsHeatSol (fun t => N (t + t₀)) (fun _ => 0) ⊤ (fun t => y (t + t₀)) := by
  have h := hy.shift ht₀ ENNReal.ofReal_lt_top
  rwa [ENNReal.ofReal, ENNReal.top_sub_coe] at h

/-- Instant regularization: at positive times the solution is in every `H^{n+2}`. -/
private lemma inH_pos {Γ : ℝ} (hN : Majorized N) (hG : GoodForce (fun _ => 0) Γ)
    (hy : IsHeatSol N (fun _ => 0) ⊤ y) (n : ℕ) :
    ∀ a : ℝ, 0 < a → ∀ t, a ≤ t → InH ((n : ℝ) + 2) (y t) := by
  induction n with
  | zero =>
    intro a ha t ht
    simpa using (hy.adm t (ha.le.trans ht) ENNReal.ofReal_lt_top).inH
  | succ n ih =>
    intro a ha t ht
    have hδ : 0 < a / 3 := by positivity
    have h1 : HeatPair ((n : ℝ) + 2) 0 (a / 3) (fun u => y (u + a / 3)) _ :=
      ladder (hN.shift (a / 3)) hG (shifted hy hδ.le) (by linarith [n.cast_nonneg (α := ℝ)])
        (by
          rw [zero_add]
          exact ih (a / 3) hδ (a / 3) le_rfl) hδ.le
    have hvol : volume (Icc 0 (a / 3)) ≠ 0 := by
      simpa [Real.volume_Icc] using hδ
    obtain ⟨t₁, ht₁, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol (h1.ae_inH hδ.le)
    have ht₂ : 0 ≤ t₁ + a / 3 := by linarith [ht₁.1]
    have ht₂t : 0 ≤ t - (t₁ + a / 3) := by linarith [ht₁.2]
    have h2 := ladder (s := ((n + 1 : ℕ) : ℝ) + 2) (hN.shift (t₁ + a / 3)) hG (shifted hy ht₂)
      (by linarith [(n + 1).cast_nonneg (α := ℝ)])
      (by
        have e : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 2 + 1 := by push_cast; ring
        change InH _ (y (0 + (t₁ + a / 3)))
        rw [e, zero_add]
        exact hgood) ht₂t
    have h3 : InH (((n + 1 : ℕ) : ℝ) + 2) (y (t - (t₁ + a / 3) + (t₁ + a / 3))) :=
      h2.inH _ ⟨ht₂t, le_rfl⟩
    rwa [sub_add_cancel] at h3

/-- Persistence for a global unforced filtered solution: every `H^s` regularity of the datum
persists, with `L²_loc H^{s+1}`. -/
theorem persist {G : ℝ → Field} {Γ : ℝ} (hN : Majorized N) (hG : GoodForce G Γ)
    (hG0 : G = fun _ => 0) (hy : IsHeatSol N G ⊤ y) {s : ℝ} (hs : 2 ≤ s) (h0 : InH s (y 0)) :
    (∀ t, 0 ≤ t → InH s (y t)) ∧ ContH s y ∧ L2locH (s + 1) y := by
  subst hG0
  have hL : ∀ {b : ℝ}, 0 ≤ b → HeatPair s 0 b y (nlF N y) := fun hb => ladder hN hG hy hs h0 hb
  refine ⟨fun t ht => (hL ht).inH t ⟨ht, le_rfl⟩, fun t₀ ht₀ => ?_, fun T hT => ?_⟩
  · have ht : (0 : ℝ) ≤ t₀ := ht₀
    have hb : (0 : ℝ) ≤ t₀ + 1 := by linarith
    have hm : Icc 0 (t₀ + 1) ∈ 𝓝[Ici 0] t₀ := by
      rw [← Ici_inter_Iic]
      exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
    exact ((hL hb).tendsto_hnorm hb ⟨ht, by linarith⟩).mono_left (nhdsWithin_le_of_mem hm)
  · exact ((hL hT).dissipation_lt_top hT).trans_lt
      (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, (hL hT).force_l2⟩)

/-- Instant smoothing: for positive times the unforced solution lies in every `H^m`, locally
uniformly. -/
theorem smoothing {G : ℝ → Field} {Γ : ℝ} (hN : Majorized N) (hG : GoodForce G Γ)
    (hG0 : G = fun _ => 0) (hy : IsHeatSol N G ⊤ y) (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, ∀ t ∈ Icc a b, InH m (y t) ∧ hnorm m (y t) ≤ C := by
  subst hG0
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  have hreg := inH_pos hN hG hy m a ha
  have hb : 0 ≤ b - a := by linarith
  have h1 : HeatPair ((m : ℝ) + 2) 0 (b - a) (fun u => y (u + a)) _ :=
    ladder (hN.shift a) hG (shifted hy ha.le) (by linarith)
      (by
        rw [zero_add]
        exact hreg a le_rfl) hb
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (h1.continuousOn_hnorm_sq hb)
  refine ⟨C + 1, fun t ht => ?_⟩
  have hit : InH ((m : ℝ) + 2) (y t) := hreg t ht.1
  refine ⟨hit.mono (by linarith), (hnorm_mono (by linarith) hit).trans ?_⟩
  have hc := hC (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only [sub_add_cancel, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (hnorm _ _))] at hc
  nlinarith [sq_nonneg (hnorm ((m : ℝ) + 2) (y t) - 1), sq_nonneg (hnorm ((m : ℝ) + 2) (y t))]

end OVNS
