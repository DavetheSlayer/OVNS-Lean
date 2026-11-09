import OddViscousNS.Closed.Metric
import OddViscousNS.LocalTheory
import OddViscousNS.LocalMaximal

/-!
# From a bounded metric to a global heat solution (Lemma `moment-continuation`, normalized part)

If every heat solution started at `y₀` has `Y ≤ Ycap` and `∫_I Z ≤ J` on unit windows inside its
interval of existence, then the maximal solution is global and has uniform `H¹`, `H²` bounds and
unit-window `H³` square-integral bounds, with a constant depending only on
`(‖y₀‖₂ ≤ μ, Ycap, J, Γ)`.  The proof is the manuscript's: `.29 ‖y‖₁² ≤ Y`, `.29 ‖y‖₂² ≤ Z`, the
`H²` inequality `h2_ineq` (`B' + c² ≤ 128 c₄² B² + 2Γ²` after `wiener_le`), uniform Gronwall on
unit windows (`uniform_gronwall`), and the blow-up alternative of `exists_maximal`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

variable {N : ℝ → Field → Field → Field} {G : ℝ → Field} {Γ : ℝ}

/-- The uniform `H²` cap `(μ² + J/.29 + 2Γ²) exp(128 c₄² J/.29)`. -/
private noncomputable def capH (μ J Γ : ℝ) : ℝ :=
  (μ ^ 2 + 100 / 29 * J + 2 * Γ ^ 2) * Real.exp (128 * c4 ^ 2 * (100 / 29 * J))

/-- `x ≤ 1 + x²`. -/
private lemma le_one_add_sq (x : ℝ) : x ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (x - 1)]

/-- The `H¹` norm is controlled by the metric `Y`. -/
private lemma h1_le_Ycap {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y) {t Ycap : ℝ}
    (hYcap : 0 ≤ Ycap) (ht0 : 0 ≤ t) (htT : ENNReal.ofReal t < T)
    (hY : Ymet (y t) ≤ ENNReal.ofReal Ycap) : 29 / 100 * hnorm 1 (y t) ^ 2 ≤ Ycap := by
  have hin : InH 1 (y t) := InH.mono (by norm_num) (hy.adm t ht0 htT).inH
  have h := (hsE_one_le_Ymet (y t)).trans hY
  rw [hsE_eq_ofReal hin, ← ENNReal.ofReal_mul (by norm_num)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hYcap).1 h

/-- `t ↦ ‖y t‖₂²` is continuous on compact windows of the lifespan. -/
private lemma contOn_sq {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y) {a b : ℝ}
    (ha : 0 ≤ a) (hb : ENNReal.ofReal b < T) :
    ContinuousOn (fun u ↦ hnorm 2 (y u) ^ 2) (Icc a b) :=
  ((hy.continuousOn_hnorm2 hb).mono (Icc_subset_Icc_left ha)).pow 2

/-- The `H²` square-integral on a window is controlled by the metric `Z`. -/
private lemma window_le {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y) {a b J : ℝ}
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hab : a ≤ b) (hb : ENNReal.ofReal b < T)
    (hZ : ∫⁻ τ in Icc a b, Zmet (y τ) ≤ ENNReal.ofReal J) :
    ∫ u in a..b, hnorm 2 (y u) ^ 2 ≤ 100 / 29 * J := by
  have hint : IntegrableOn (fun u ↦ hnorm 2 (y u) ^ 2) (Icc a b) :=
    (contOn_sq hy ha hb).integrableOn_compact isCompact_Icc
  have hle : ∫⁻ τ in Icc a b, ENNReal.ofReal (29 / 100 * hnorm 2 (y τ) ^ 2) ≤
      ENNReal.ofReal J := by
    refine le_trans (setLIntegral_mono' measurableSet_Icc fun τ hτ ↦ ?_) hZ
    rw [ENNReal.ofReal_mul (by norm_num), ← hsE_eq_ofReal
      (hy.adm τ (ha.trans hτ.1) ((ENNReal.ofReal_le_ofReal hτ.2).trans_lt hb)).inH]
    exact hsE_two_le_Zmet _
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (Filter.Eventually.of_forall fun _ ↦ by positivity)] at hle
  have h := (ENNReal.ofReal_le_ofReal_iff hJ).1 hle
  rw [integral_const_mul] at h
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  linarith

/-- The `H²` inequality with the Wiener norm replaced by `c₄ ‖y‖₂`. -/
private lemma energy_le (hN : Majorized N) (hG : GoodForce G Γ) {T : ℝ≥0∞} {y : ℝ → Field}
    (hy : IsHeatSol N G T y) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < T) :
    hnorm 2 (y t) ^ 2 + ∫ u in s..t, hnorm 3 (y u) ^ 2 ≤ hnorm 2 (y s) ^ 2 +
      ∫ u in s..t, (128 * c4 ^ 2 * hnorm 2 (y u) ^ 2 * hnorm 2 (y u) ^ 2 + 2 * Γ ^ 2) := by
  refine (h2_ineq hN hG hy hs hst ht).trans (add_le_add le_rfl ?_)
  have hgi : IntegrableOn
      (fun u ↦ 128 * c4 ^ 2 * hnorm 2 (y u) ^ 2 * hnorm 2 (y u) ^ 2 + 2 * Γ ^ 2) (Ioc s t) :=
    ((((contOn_sq hy hs ht).const_mul _).mul (contOn_sq hy hs ht)).add
      continuousOn_const).integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u ↦ by positivity) hgi
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu ↦ ?_))
  have hmz : MZ 2 (y u) :=
    (hy.adm u (hs.trans hu.1.le) ((ENNReal.ofReal_le_ofReal hu.2).trans_lt ht)).mz
  have hw := wiener_le hmz
  have hw0 := wiener_nonneg (y u)
  have h2 : wiener (y u) ^ 2 ≤ c4 ^ 2 * hnorm 2 (y u) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hw0 hw 2
  have := mul_le_mul_of_nonneg_right h2 (sq_nonneg (hnorm 2 (y u)))
  simp only
  nlinarith

/-- The uniform `H²` cap on the whole lifespan. -/
private lemma cap_le (hN : Majorized N) (hG : GoodForce G Γ) {T : ℝ≥0∞} {y : ℝ → Field}
    (hy : IsHeatSol N G T y) {μ J : ℝ} (hJ : 0 ≤ J) (hy0 : hnorm 2 (y 0) ≤ μ)
    (hZ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ a + 1 → ENNReal.ofReal b < T →
      ∫⁻ τ in Icc a b, Zmet (y τ) ≤ ENNReal.ofReal J)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : ENNReal.ofReal t < T) :
    hnorm 2 (y t) ^ 2 ≤ capH μ J Γ := by
  set B : ℝ → ℝ := fun u ↦ hnorm 2 (y u) ^ 2 with hBdef
  have hB0 : ∀ u, 0 ≤ B u := fun u ↦ sq_nonneg _
  have hc4 : 0 ≤ 128 * c4 ^ 2 := by positivity
  have hW : ∀ a, 0 ≤ a → a ≤ t → t ≤ a + 1 → ∫ u in a..t, B u ≤ 100 / 29 * J :=
    fun a ha hat hta ↦ window_le hy hJ ha hat htT (hZ a t ha hat hta htT)
  have hE : ∀ a, 0 ≤ a → a ≤ t → t ≤ a + 1 →
      ∫ u in a..t, 128 * c4 ^ 2 * B u ≤ 128 * c4 ^ 2 * (100 / 29 * J) := fun a ha hat hta ↦ by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hW a ha hat hta) hc4
  have hh : ∀ a, 0 ≤ a → ∀ s t', a ≤ s → s ≤ t' → t' ≤ t →
      B t' ≤ B s + ∫ u in s..t', (128 * c4 ^ 2 * B u * B u + 2 * Γ ^ 2) :=
    fun a ha s t' has hst htt ↦ by
      have h := energy_le hN hG hy (ha.trans has) hst
        ((ENNReal.ofReal_le_ofReal htt).trans_lt htT)
      have h3 : 0 ≤ ∫ u in s..t', hnorm 3 (y u) ^ 2 :=
        intervalIntegral.integral_nonneg hst fun u _ ↦ sq_nonneg _
      simp only [hBdef]
      linarith
  have hcont : ∀ a, 0 ≤ a → ContinuousOn B (Icc a t) := fun a ha ↦ contOn_sq hy ha htT
  have hκi : ∀ a, 0 ≤ a → a ≤ t →
      IntervalIntegrable (fun u ↦ 128 * c4 ^ 2 * B u) volume a t :=
    fun a ha hat ↦ ContinuousOn.intervalIntegrable_of_Icc hat
      (continuousOn_const.mul (hcont a ha))
  have hfin : ∀ X E : ℝ, 0 ≤ X → X ≤ μ ^ 2 + 100 / 29 * J + 2 * Γ ^ 2 →
      E ≤ 128 * c4 ^ 2 * (100 / 29 * J) → X * Real.exp E ≤ capH μ J Γ := fun X E hX0 hX hE ↦
    mul_le_mul hX (Real.exp_le_exp.2 hE) (Real.exp_pos _).le (by linarith)
  have hμ2 : B 0 ≤ μ ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) hy0 2
  change B t ≤ capH μ J Γ
  clear_value B
  rcases le_total t 1 with ht1 | ht1
  · have h := gronwall_simple (y := B) (κ := fun u ↦ 128 * c4 ^ 2 * B u)
      (β := fun _ ↦ 2 * Γ ^ 2) ht0 (hcont 0 le_rfl) (hκi 0 le_rfl ht0)
      (fun u ↦ mul_nonneg hc4 (hB0 u)) intervalIntegrable_const (fun _ ↦ by positivity)
      (hh 0 le_rfl) 0 t le_rfl ht0 le_rfl
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    have h2 : t * (2 * Γ ^ 2) ≤ 2 * Γ ^ 2 := by nlinarith [sq_nonneg Γ]
    have h3 := hfin (B 0 + t * (2 * Γ ^ 2)) (∫ u in (0 : ℝ)..t, 128 * c4 ^ 2 * B u)
      (add_nonneg (hB0 0) (by positivity)) (by linarith) (hE 0 le_rfl ht0 (by linarith))
    exact h.trans h3
  · have h := uniform_gronwall (y := B) (κ := fun u ↦ 128 * c4 ^ 2 * B u)
      (β := fun _ ↦ 2 * Γ ^ 2) (t := t) (hcont _ (by linarith)) hB0
      (hκi _ (by linarith) (by linarith))
      (fun u ↦ mul_nonneg hc4 (hB0 u)) intervalIntegrable_const (fun _ ↦ by positivity)
      (hh (t - 1) (by linarith))
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_sub_cancel, one_mul] at h
    have hw := hW (t - 1) (by linarith) (by linarith) (by linarith)
    refine h.trans (hfin _ _ ?_ (by nlinarith [sq_nonneg μ])
      (hE _ (by linarith) (by linarith) (by linarith)))
    exact add_nonneg (intervalIntegral.integral_nonneg (by linarith) fun u _ ↦ hB0 u)
      (by positivity)

theorem heat_global_of_metric (μ Ycap J Γ : ℝ) (_hμ : 0 ≤ μ) (hYcap : 0 ≤ Ycap) (hJ : 0 ≤ J) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ {N : ℝ → Field → Field → Field} {G : ℝ → Field} {y₀ : Field},
      Majorized N → GoodForce G Γ → Adm 2 y₀ → hnorm 2 y₀ ≤ μ →
      (∀ (T : ℝ≥0∞) (y : ℝ → Field), IsHeatSol N G T y → y 0 = y₀ →
        (∀ t, 0 ≤ t → ENNReal.ofReal t < T → Ymet (y t) ≤ ENNReal.ofReal Ycap) ∧
        (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ a + 1 → ENNReal.ofReal b < T →
          ∫⁻ τ in Icc a b, Zmet (y τ) ≤ ENNReal.ofReal J)) →
      ∃ y : ℝ → Field, IsHeatSol N G ⊤ y ∧ y 0 = y₀ ∧
        (∀ t, 0 ≤ t → hnorm 1 (y t) ≤ Bd ∧ hnorm 2 (y t) ≤ Bd) ∧
        (∀ t, 0 ≤ t → ∫ s in t..(t + 1), hnorm 3 (y s) ^ 2 ≤ Bd) := by
  have hH : 0 ≤ capH μ J Γ := by unfold capH; positivity
  have hc4 : 0 ≤ 128 * c4 ^ 2 := by positivity
  refine ⟨2 + 4 * Ycap + 2 * capH μ J Γ + 128 * c4 ^ 2 * capH μ J Γ * (100 / 29 * J) +
    2 * Γ ^ 2, by positivity, ?_⟩
  intro N G y₀ hN hG hy₀ hμ0 hmet
  obtain ⟨T, y, -, hy, hy0, hmax⟩ := exists_maximal hN hG hy₀
  obtain ⟨hY, hZ⟩ := hmet T y hy hy0
  have hy0' : hnorm 2 (y 0) ≤ μ := hy0 ▸ hμ0
  have hcap := fun t ht0 htT ↦ cap_le hN hG hy hJ hy0' hZ (t := t) ht0 htT
  obtain rfl : T = ⊤ := by
    by_contra hne
    exact hmax hne (1 + capH μ J Γ) fun t ht0 htT ↦
      (le_one_add_sq _).trans (by linarith [hcap t ht0 htT])
  refine ⟨y, hy, hy0, fun t ht ↦ ⟨?_, ?_⟩, fun t ht ↦ ?_⟩
  · have h1 := h1_le_Ycap hy hYcap ht ENNReal.ofReal_lt_top (hY t ht ENNReal.ofReal_lt_top)
    have := le_one_add_sq (hnorm 1 (y t))
    have : 0 ≤ 128 * c4 ^ 2 * capH μ J Γ * (100 / 29 * J) := by positivity
    nlinarith
  · have := le_one_add_sq (hnorm 2 (y t))
    have := hcap t ht ENNReal.ofReal_lt_top
    have : 0 ≤ 128 * c4 ^ 2 * capH μ J Γ * (100 / 29 * J) := by positivity
    nlinarith
  · have htop : ENNReal.ofReal (t + 1) < ⊤ := ENNReal.ofReal_lt_top
    have h := energy_le hN hG hy ht (by linarith) htop
    have hw := window_le hy hJ ht (by linarith) htop (hZ t (t + 1) ht (by linarith) le_rfl htop)
    have hc := contOn_sq hy ht htop
    have hBi : IntervalIntegrable (fun u ↦ hnorm 2 (y u) ^ 2) volume t (t + 1) :=
      hc.intervalIntegrable_of_Icc (by linarith)
    have hBBi : IntervalIntegrable
        (fun u ↦ 128 * c4 ^ 2 * hnorm 2 (y u) ^ 2 * hnorm 2 (y u) ^ 2) volume t (t + 1) :=
      ((continuousOn_const.mul hc).mul hc).intervalIntegrable_of_Icc (by linarith)
    have hmono : ∫ u in t..(t + 1), 128 * c4 ^ 2 * hnorm 2 (y u) ^ 2 * hnorm 2 (y u) ^ 2 ≤
        ∫ u in t..(t + 1), 128 * c4 ^ 2 * capH μ J Γ * hnorm 2 (y u) ^ 2 :=
      intervalIntegral.integral_mono_on (by linarith) hBBi (hBi.const_mul _) fun u hu ↦
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (hcap u (ht.trans hu.1) ENNReal.ofReal_lt_top) hc4) (sq_nonneg _)
    rw [intervalIntegral.integral_const_mul] at hmono
    rw [intervalIntegral.integral_add hBBi intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at h
    have := hcap t ht ENNReal.ofReal_lt_top
    have := mul_le_mul_of_nonneg_left hw (mul_nonneg hc4 hH)
    have : 0 ≤ hnorm 2 (y (t + 1)) ^ 2 := sq_nonneg _
    have : 0 ≤ 4 * Ycap := by positivity
    nlinarith

end OVNS
