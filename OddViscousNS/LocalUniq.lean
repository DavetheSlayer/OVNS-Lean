import OddViscousNS.LocalBasic

/-! # Uniqueness of filtered solutions (`Lemma fg:lem:lwp(b)`) -/

open scoped ENNReal Topology
open MeasureTheory Set Filter
noncomputable section
namespace OVNS

variable {N : ℝ → Field → Field → Field} {G : ℝ → Field} {Γ : ℝ}

/-- Solutions are `MZ 2` throughout their lifespan. -/
private lemma IsHeatSol.mz {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y) {t : ℝ}
    (h0 : 0 ≤ t) (ht : ENNReal.ofReal t < T) : MZ 2 (y t) :=
  ⟨(hy.adm t h0 ht).inH, (hy.adm t h0 ht).mean⟩

/-- Differences of `MZ 2` fields are `MZ 2`. -/
private lemma mz_sub {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) : MZ 2 (f - g) :=
  ⟨hf.inH.sub hg.inH, by simp [hf.mean, hg.mean]⟩

/-- Time continuity of the `H²` norm on a compact interval of the lifespan. -/
private lemma continuousOn_hnorm_two {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y) {b : ℝ}
    (hbT : ENNReal.ofReal b < T) : ContinuousOn (fun t => hnorm 2 (y t)) (Icc 0 b) := by
  intro t₀ ht₀
  have hlt : ∀ t ∈ Icc 0 b, ENNReal.ofReal t < T := fun t ht =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) hbT
  have hlim : Tendsto (fun t => hnorm 2 (y t - y t₀)) (𝓝[Icc 0 b] t₀) (𝓝 0) :=
    (hy.cont t₀ ht₀.1 (hlt t₀ ht₀)).mono_left (nhdsWithin_mono t₀ fun t ht => ht.1)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ =>
    norm_nonneg _) ?_ hlim)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have h1 := (hy.mz ht.1 (hlt t ht)).inH
  have h2 := (hy.mz ht₀.1 (hlt t₀ ht₀)).inH
  have h3 : hnorm 2 (y t) ≤ hnorm 2 (y t - y t₀) + hnorm 2 (y t₀) := by
    simpa using hnorm_add_le (h1.sub h2) h2
  have h4 : hnorm 2 (y t₀) ≤ hnorm 2 (y t₀ - y t) + hnorm 2 (y t) := by
    simpa using hnorm_add_le (h2.sub h1) h1
  rw [hnorm_sub_comm] at h4
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Uniform `H²` bound on a compact interval of the lifespan. -/
private lemma exists_hnorm_bound {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y) {b : ℝ}
    (hbT : ENNReal.ofReal b < T) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 b, hnorm 2 (y t) ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.bddAbove_image (continuousOn_hnorm_two hy hbT))
  refine ⟨max M 0, le_max_right _ _, fun t ht => (hM ⟨t, ht, rfl⟩).trans (le_max_left _ _)⟩

/-- The pairing with a field bounded by `2|k| W_k`, at level `σ = 0`. -/
private lemma pair_zero_le {c H : Field} {W : Mode → ℝ} (hc : InH 1 c) (hW0 : ∀ k, 0 ≤ W k)
    (hW : Summable fun k => W k ^ 2) (hH : ∀ k, ‖H k‖ ≤ 2 * absk k * W k) :
    |pair 0 c H| ≤ 2 * hnorm 1 c * Real.sqrt (∑' k, W k ^ 2) := by
  have ha2 : ∀ k, (absk k * ‖c k‖) ^ 2 = sobWeight 1 k * ‖c k‖ ^ 2 := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have h0 : absk 0 = 0 := absk_eq_zero.2 rfl
      simp [h0, sobWeight]
    · simp only [sobWeight, hk, ite_false, mul_one, mul_pow]
      rw [Real.rpow_two]
  have ha : Summable fun k => (absk k * ‖c k‖) ^ 2 := by
    simp only [ha2]
    exact hc
  have hcs := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg (c k))) hW0
    (by simpa only [Real.rpow_two] using ha) (by simpa only [Real.rpow_two] using hW)
  obtain ⟨hs, hle'⟩ := hcs
  have hle : ∑' k, absk k * ‖c k‖ * W k ≤
      Real.sqrt (∑' k, (absk k * ‖c k‖) ^ 2) * Real.sqrt (∑' k, W k ^ 2) := by
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using hle'
  have hterm : ∀ k, ‖sobWeight 0 k * (inner ℂ (c k) (H k)).re‖ ≤
      2 * (absk k * ‖c k‖ * W k) := by
    intro k
    have hw : sobWeight 0 k ≤ 1 := by
      unfold sobWeight
      split_ifs <;> simp
    have hi : |(inner ℂ (c k) (H k)).re| ≤ ‖c k‖ * ‖H k‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sobWeight_nonneg 0 k)]
    calc sobWeight 0 k * |(inner ℂ (c k) (H k)).re| ≤ 1 * (‖c k‖ * ‖H k‖) :=
          mul_le_mul hw hi (abs_nonneg _) zero_le_one
      _ ≤ 1 * (‖c k‖ * (2 * absk k * W k)) := by gcongr; exact hH k
      _ = 2 * (absk k * ‖c k‖ * W k) := by ring
  rw [pair, ← Real.norm_eq_abs]
  refine (tsum_of_norm_bounded (hs.mul_left 2).hasSum hterm).trans ?_
  rw [tsum_mul_left]
  have hn : hnorm 1 c = Real.sqrt (∑' k, (absk k * ‖c k‖) ^ 2) := by
    simp only [hnorm, ha2]
  rw [hn, mul_assoc]
  exact mul_le_mul_of_nonneg_left hle zero_le_two

/-- The `ℓ²` norm of an `MZ` field is its `H⁰` norm. -/
private lemma l2_of_mz {f : Field} (hf : MZ 2 f) :
    Summable (fun k => ‖f k‖ ^ 2) ∧ ∑' k, ‖f k‖ ^ 2 = hnorm 0 f ^ 2 := by
  have h0 : InH 0 f := hf.inH.mono (by norm_num)
  have e : ∀ k, sobWeight 0 k * ‖f k‖ ^ 2 = ‖f k‖ ^ 2 := by
    intro k
    by_cases hk : k = 0
    · simp [hk, sobWeight, hf.mean]
    · simp [hk, sobWeight]
  have hS : Summable fun k => ‖f k‖ ^ 2 := by simpa only [InH, e] using h0
  refine ⟨hS, ?_⟩
  rw [hnorm_sq h0]
  simp only [e]

/-- Young's inequality for the coefficient convolution of `f ∈ ℓ¹`, `g ∈ ℓ²`. -/
private lemma conv_l2 {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) :
    Summable (fun k => convR (fun p => ‖f p‖) (fun p => ‖g p‖) k ^ 2) ∧
      Real.sqrt (∑' k, convR (fun p => ‖f p‖) (fun p => ‖g p‖) k ^ 2) ≤
        wiener f * hnorm 0 g := by
  obtain ⟨hg1, hg2⟩ := l2_of_mz hg
  obtain ⟨-, h2, h3⟩ := young_l1_l2 (a := fun p => ‖f p‖) (b := fun p => ‖g p‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (summable_wiener hf.inH) hg1
  refine ⟨h2, ?_⟩
  rw [hg2, show (∑' k, ‖f k‖) = wiener f from rfl] at h3
  have h4 := Real.sqrt_le_sqrt h3
  rwa [← mul_pow, Real.sqrt_sq (mul_nonneg (wiener_nonneg f) (hnorm_nonneg 0 g))] at h4

/-- Pairing bound for `N`, with `f` in `ℓ¹` and `g` in `ℓ²`. -/
private lemma pair_N_left (hN : Majorized N) (t : ℝ) {c f g : Field} (hc : InH 1 c)
    (hf : MZ 2 f) (hg : MZ 2 g) :
    |pair 0 c (N t f g)| ≤ 2 * hnorm 1 c * (wiener f * hnorm 0 g) := by
  obtain ⟨h1, h2⟩ := conv_l2 hf hg
  refine (pair_zero_le hc (fun k => tsum_nonneg fun p => mul_nonneg (norm_nonneg _)
    (norm_nonneg _)) h1 fun k => hN.maj₂ t f g k hf hg).trans ?_
  exact mul_le_mul_of_nonneg_left h2 (mul_nonneg zero_le_two (hnorm_nonneg 1 c))

/-- Pairing bound for `N`, with `f` in `ℓ²` and `g` in `ℓ¹`. -/
private lemma pair_N_right (hN : Majorized N) (t : ℝ) {c f g : Field} (hc : InH 1 c)
    (hf : MZ 2 f) (hg : MZ 2 g) :
    |pair 0 c (N t f g)| ≤ 2 * hnorm 1 c * (wiener g * hnorm 0 f) := by
  obtain ⟨h1, h2⟩ := conv_l2 hg hf
  have e : convR (fun p => ‖g p‖) (fun p => ‖f p‖) = convR (fun p => ‖f p‖) (fun p => ‖g p‖) :=
    funext (convR_comm _ _)
  rw [e] at h1 h2
  refine (pair_zero_le hc (fun k => tsum_nonneg fun p => mul_nonneg (norm_nonneg _)
    (norm_nonneg _)) h1 fun k => hN.maj₂ t f g k hf hg).trans ?_
  exact mul_le_mul_of_nonneg_left h2 (mul_nonneg zero_le_two (hnorm_nonneg 1 c))

/-- The pairing of the difference with the difference of the nonlinearities. -/
private lemma pair_diff_le (hN : Majorized N) (t : ℝ) {u v : Field} (hu : MZ 2 u) (hv : MZ 2 v) :
    pair 0 (u - v) (N t v v - N t u u) ≤
      2 * hnorm 1 (u - v) * hnorm 0 (u - v) * (wiener u + wiener v) := by
  have hz := mz_sub hu hv
  have hc1 : InH (0 + 1) (u - v) := by simpa using hz.inH.mono (s := 1) (by norm_num)
  have hc : InH 1 (u - v) := hz.inH.mono (by norm_num)
  have hA := hN.hnorm_zero_le t hz hu
  have hB := hN.hnorm_zero_le t hv hz
  have hm : ∀ {f : Field}, InH 0 f → InH (0 - 1) f := fun hf => hf.mono (by norm_num)
  have e : N t v v - N t u u = -N t (u - v) u - N t v (u - v) := by
    rw [hN.sub_left t u v u hu hv hu, hN.sub_right t v u v hv hu hv]
    abel
  have h1 := pair_N_right hN t hc hz hu
  have h3 : pair 0 (u - v) (-N t (u - v) u) = -pair 0 (u - v) (N t (u - v) u) := by
    simp only [pair, Pi.neg_apply, inner_neg_right, Complex.neg_re, mul_neg, tsum_neg]
  have h4 := pair_N_left hN t hc hv hz
  rw [e, pair_sub hc1 (hm hA.1.neg) (hm hB.1), h3]
  have := abs_le.1 h1
  have := abs_le.1 h4
  nlinarith

/-- `H⁰` bound on the nonlinearity from an `H²` bound. -/
private lemma hnorm_N_self_le (hN : Majorized N) (t : ℝ) {u : Field} (hu : MZ 2 u) {M : ℝ}
    (hM : hnorm 2 u ≤ M) : hnorm 0 (N t u u) ≤ 2 * (M * (c4 * M)) := by
  have h1 : hnorm 1 u ≤ M := (hnorm_mono (by norm_num) hu.inH).trans hM
  have h2 : wiener u ≤ c4 * M :=
    (wiener_le hu).trans (mul_le_mul_of_nonneg_left hM c4_pos.le)
  have h3 : hnorm 1 u * wiener u ≤ M * (c4 * M) :=
    mul_le_mul h1 h2 (wiener_nonneg u) ((hnorm_nonneg 1 u).trans h1)
  have h4 := (hN.hnorm_zero_le t hu hu).2
  rw [mul_comm (wiener u)] at h4
  linarith

/-- The `H⁻¹` energy of a field is at most its `H⁰` norm square. -/
private lemma hsE_neg_one_le {f : Field} (hf : InH 0 f) {C : ℝ} (hC : hnorm 0 f ≤ C) :
    hsE (0 - 1) f ≤ ENNReal.ofReal (C ^ 2) := by
  have h1 : hsE (0 - 1) f ≤ hsE 0 f := tsum_le_tsum fun k =>
    ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (sobWeight_mono (by norm_num) k) (sq_nonneg _))
  rw [hsE_eq_ofReal hf] at h1
  exact h1.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hnorm_nonneg 0 f) hC 2))

/-- The difference of two solutions is a `HeatPair` at level `0`. -/
private lemma heatPair_diff (hN : Majorized N) (hG : GoodForce G Γ) {T : ℝ≥0∞} {y y' : ℝ → Field}
    (hy : IsHeatSol N G T y) (hy' : IsHeatSol N G T y') {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) :
    HeatPair 0 0 b (fun t => y t - y' t) (fun t => N t (y' t) (y' t) - N t (y t) (y t)) := by
  obtain ⟨M, -, hM⟩ := exists_hnorm_bound hy hbT
  obtain ⟨M', -, hM'⟩ := exists_hnorm_bound hy' hbT
  have hlt : ∀ t ∈ Icc 0 b, ENNReal.ofReal t < T := fun t ht =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) hbT
  have h1 := hy.heatPair_low hN hG (σ := 0) (Or.inl rfl) hb hbT
  have h2 := hy'.heatPair_low hN hG (σ := 0) (Or.inl rfl) hb hbT
  refine ⟨fun t ht => (h1.inH t ht).sub (h2.inH t ht), fun k t ht => ?_, fun k => ?_, ?_⟩
  · refine ((h1.mode k t ht).sub (h2.mode k t ht)).congr_deriv ?_
    simp only [Pi.sub_apply, smul_sub]
    abel
  · refine ((h1.force_cont k).sub (h2.force_cont k)).congr fun t _ => ?_
    simp only [Pi.sub_apply]
    abel
  · set C : ℝ := 2 * (M' * (c4 * M')) + 2 * (M * (c4 * M))
    have hbd : ∀ t ∈ Icc 0 b, hsE (0 - 1) (N t (y' t) (y' t) - N t (y t) (y t)) ≤
        ENNReal.ofReal (C ^ 2) := by
      intro t ht
      have hu := hy.mz ht.1 (hlt t ht)
      have hu' := hy'.mz ht.1 (hlt t ht)
      have ha := (hN.hnorm_zero_le t hu hu).1
      have ha' := (hN.hnorm_zero_le t hu' hu').1
      refine hsE_neg_one_le (ha'.sub ha) ((hnorm_sub_le ha' ha).trans ?_)
      exact add_le_add (hnorm_N_self_le hN t hu' (hM' t ht)) (hnorm_N_self_le hN t hu (hM t ht))
    calc ∫⁻ t in Icc 0 b, hsE (0 - 1) (N t (y' t) (y' t) - N t (y t) (y t))
        ≤ ∫⁻ _ in Icc 0 b, ENNReal.ofReal (C ^ 2) := setLIntegral_mono' measurableSet_Icc hbd
      _ = ENNReal.ofReal (C ^ 2) * volume (Icc 0 b) := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp [Real.volume_Icc])

/-- The Young absorption of the pairing into the dissipation. -/
private lemma pair_diff_young (hN : Majorized N) (t : ℝ) {u v : Field} (hu : MZ 2 u)
    (hv : MZ 2 v) {L : ℝ} (hL : wiener u + wiener v ≤ L) :
    pair 0 (u - v) (N t v v - N t u u) ≤ hnorm 1 (u - v) ^ 2 + L ^ 2 * hnorm 0 (u - v) ^ 2 := by
  have h := pair_diff_le hN t hu hv
  have ha := hnorm_nonneg 1 (u - v)
  have hb := hnorm_nonneg 0 (u - v)
  have hc : 2 * hnorm 1 (u - v) * hnorm 0 (u - v) * (wiener u + wiener v) ≤
      2 * hnorm 1 (u - v) * hnorm 0 (u - v) * L :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  nlinarith [sq_nonneg (hnorm 1 (u - v) - hnorm 0 (u - v) * L)]

/-- Uniqueness in the class `IsHeatSol`. -/
theorem heatSol_unique (hN : Majorized N) (hG : GoodForce G Γ) {T : ℝ≥0∞} {y y' : ℝ → Field}
    (hy : IsHeatSol N G T y) (hy' : IsHeatSol N G T y') (h0 : y 0 = y' 0) :
    ∀ t, 0 ≤ t → ENNReal.ofReal t < T → y t = y' t := by
  intro t ht0 htT
  obtain ⟨M, -, hM⟩ := exists_hnorm_bound hy htT
  obtain ⟨M', -, hM'⟩ := exists_hnorm_bound hy' htT
  have hlt : ∀ u ∈ Icc 0 t, ENNReal.ofReal u < T := fun u hu =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) htT
  have hP := heatPair_diff hN hG hy hy' ht0 htT
  set L : ℝ := c4 * M + c4 * M'
  have hL : ∀ u ∈ Icc 0 t, wiener (y u) + wiener (y' u) ≤ L := fun u hu =>
    add_le_add ((wiener_le (hy.mz hu.1 (hlt u hu))).trans
        (mul_le_mul_of_nonneg_left (hM u hu) c4_pos.le))
      ((wiener_le (hy'.mz hu.1 (hlt u hu))).trans
        (mul_le_mul_of_nonneg_left (hM' u hu) c4_pos.le))
  have hcont := hP.continuousOn_hnorm_sq ht0
  have hkey : ∀ s r, 0 ≤ s → s ≤ r → r ≤ t →
      hnorm 0 (y r - y' r) ^ 2 ≤ hnorm 0 (y s - y' s) ^ 2 +
        ∫ u in s..r, (2 * L ^ 2 * hnorm 0 (y u - y' u) ^ 2 + 0) := by
    intro s r hs hsr hr
    have hE := hP.energy_identity hs hsr hr
    have hQ := hP.mono hs hr
    simp only [zero_add] at hE
    have hi0 : IntervalIntegrable (fun u => hnorm 0 (y u - y' u) ^ 2) volume s r :=
      ContinuousOn.intervalIntegrable (by
        rw [uIcc_of_le hsr]
        exact hcont.mono (Icc_subset_Icc hs hr))
    have hi1 : IntervalIntegrable (fun u => hnorm 1 (y u - y' u) ^ 2) volume s r := by
      simpa only [zero_add] using hQ.intervalIntegrable_dissipation hsr
    have hip := hQ.intervalIntegrable_pair hsr
    have hle : ∫ u in s..r, pair 0 (y u - y' u) (N u (y' u) (y' u) - N u (y u) (y u)) ≤
        ∫ u in s..r, (hnorm 1 (y u - y' u) ^ 2 + L ^ 2 * hnorm 0 (y u - y' u) ^ 2) :=
      intervalIntegral.integral_mono_on hsr hip (hi1.add (hi0.const_mul _)) fun u hu => by
        have hu' : u ∈ Icc 0 t := ⟨hs.trans hu.1, hu.2.trans hr⟩
        exact pair_diff_young hN u (hy.mz hu'.1 (hlt u hu')) (hy'.mz hu'.1 (hlt u hu')) (hL u hu')
    rw [intervalIntegral.integral_add hi1 (hi0.const_mul _),
      intervalIntegral.integral_const_mul] at hle
    simp only [add_zero]
    rw [intervalIntegral.integral_const_mul]
    linarith
  have hg := gronwall_simple (y := fun u => hnorm 0 (y u - y' u) ^ 2) (κ := fun _ => 2 * L ^ 2)
    (β := fun _ => 0) ht0 hcont intervalIntegrable_const (fun _ => by positivity)
    intervalIntegrable_const (fun _ => le_rfl) hkey 0 t le_rfl ht0 le_rfl
  have hz0 : hnorm 0 (y 0 - y' 0) = 0 := by rw [h0, sub_self, hnorm_zero]
  have hsq : hnorm 0 (y t - y' t) ^ 2 ≤ 0 := by simpa [hz0] using hg
  have hn : hnorm 0 (y t - y' t) = 0 :=
    pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hsq (sq_nonneg _))
  have hz := mz_sub (hy.mz ht0 htT) (hy'.mz ht0 htT)
  exact sub_eq_zero.1 (eq_zero_of_hnorm_eq_zero (hz.inH.mono (by norm_num)) hz.mean hn)

end OVNS
