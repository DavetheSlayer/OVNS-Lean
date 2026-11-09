import OddViscousNS.Quant.Joint.Metric.LowLink

/-!
# The differentiated group: the block of `X₂` (step J5, nodes N5, N7)

Body 42, `D_S X₂[h]`, off the sector `M > D`, `M ≥ 4 F₀` (`F₀ = max(L, J)`), which is pilot 1's
`DSX2_high_le`:
* ordinary comparable exteriors: `q⁻¹/F₀`;
* ordinary separated exteriors: `q⁻² E₂`, with one `F₀` for the exterior and `|h|/F₀ ≲ |h|/P_h`;
* high intermediate, common phase, heat and separated noncommon: `q⁻² M⁴/(L²J²)`;
* high intermediate, comparable noncommon: `q⁻¹/F₀`.
`norm_X2_diff` is the sum, on one label.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open Classical in
/-- The kernel of comparable exteriors. -/
def kapC (l j : Mode) : ℝ := if absk l ≤ 2 * absk j ∧ absk j ≤ 2 * absk l then (absk j)⁻¹ else 0

lemma kapC_nonneg (l j : Mode) : 0 ≤ kapC l j := by
  have := inv_nonneg.2 (absk_nonneg j)
  unfold kapC
  split_ifs <;> positivity

private lemma term_le₃ {R : ℂ} {ρ nA nB : ℝ} {T T' : V3 →L[ℂ] V3} (c e d : Sgn) (l m j : Mode)
    (w : V3) (hR : ‖R‖ ≤ ρ) (hA : ‖T‖ ≤ nA) (hB : ‖T'‖ ≤ nB) :
    ‖R • hel c l (T (hel e m (T' (hel d j w))))‖ ≤ ρ * (nA * nB) * ‖w‖ := by
  rw [norm_smul]
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hR
  have hA0 : 0 ≤ nA := (norm_nonneg _).trans hA
  have h1 := norm_chain_le T T' c e d l m j w
  have h2 : ‖T‖ * ‖T'‖ * ‖w‖ ≤ nA * nB * ‖w‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul hA hB (norm_nonneg _) hA0) (norm_nonneg _)
  calc _ ≤ ρ * (nA * nB * ‖w‖) := mul_le_mul hR (h1.trans h2) (norm_nonneg _) hρ
    _ = _ := by ring

/-- A channel of the phase block, with any bound on the outer resolvent. -/
lemma chan_ph_gen {s : ℕ} {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) {ρ₀ H : ℝ}
    (hO : ∀ c d : Sgn, ‖resolv (-1) H (r * outerPhi c d l (l - a - b))‖ ≤ ρ₀)
    (v w : V3) (c d : Sgn) (y : V3) :
    ‖hel c l (outerInv r H l (l - a - b) (tR s r τ l a b v w - tH s r τ l a b v w)
      (hel d (l - a - b) y))‖ ≤
      2 * (16 / 9 / (|r| ^ 2 * absk (l - a) ^ 2) *
          ((16 * wt s (l - a) l * absk (l - a) * ‖v‖) *
            (16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖)) +
        ρ₀ * (4 / 3 / (|r| * absk (l - a))) *
          ((16 * wt s l (l - a) * absk l * ‖v‖) *
            (16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖)) +
        ρ₀ * (4 / 3 / (|r| * absk (l - a))) *
          ((16 * wt s (l - a) l * absk (l - a) * ‖v‖) *
            (16 * wt s (l - a - b) (l - a) * absk (l - a - b) * ‖w‖))) * ‖y‖ := by
  obtain ⟨-, hm0, hj0⟩ := fast_labels ha hb hj
  obtain ⟨hne₁, hne₂, hz₁, hz₂, -, hN⟩ := high_data hr ha hb hj hL hJ
  obtain ⟨hH1, hH2, -, -⟩ := high_heats hj0 hL hJ
  have hq : 0 < |r| := abs_pos.2 hr
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  obtain ⟨hA, hB, hC, hD⟩ := edge_sizes (s := s) τ (l := l) (a := a) (b := b) v w
  have hρ₀ : 0 ≤ ρ₀ := (norm_nonneg _).trans (hO c d)
  have hO1 := hO c d
  set R₀ := resolv (-1) H (r * outerPhi c d l (l - a - b)) with hR₀
  rw [hel_outerInv, chan_tP s r τ ha hb hj hne₁ hne₂, Finset.smul_sum]
  set nA := 16 * wt s (l - a) l * absk (l - a) * ‖v‖
  set nB := 16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖
  set nC := 16 * wt s l (l - a) * absk l * ‖v‖
  set nD := 16 * wt s (l - a - b) (l - a) * absk (l - a - b) * ‖w‖
  set ρ := 16 / 9 / (|r| ^ 2 * absk (l - a) ^ 2)
  set ρ₁ := ρ₀ * (4 / 3 / (|r| * absk (l - a)))
  refine (norm_sum_le_of_le (n := fun _ => (ρ * (nA * nB) + ρ₁ * (nC * nB) + ρ₁ * (nA * nD)) * ‖y‖)
    _ fun e _ => ?_).trans (le_of_eq ?_)
  · have hc1 : ‖chR r (triHeat a (l - a)) c e l (l - a)‖ ≤ 4 / 3 / (|r| * absk (l - a)) :=
      rho₁_le hq hN hM (hz₁ c e)
    have hc2 : ‖chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)‖ ≤
        4 / 3 / (|r| * absk (l - a)) := rho₁_le hq hN hM (hz₂ d e)
    have hR1 : ‖R₀ * chR r (triHeat a (l - a)) c e l (l - a)‖ ≤ ρ₁ := by
      rw [norm_mul]
      exact mul_le_mul hO1 hc1 (norm_nonneg _) hρ₀
    have hR2 : ‖R₀ * chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)‖ ≤ ρ₁ := by
      rw [norm_mul]
      exact mul_le_mul hO1 hc2 (norm_nonneg _) hρ₀
    have hRp : ‖R₀ * (chR r (triHeat a (l - a)) c e l (l - a) +
        chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b) - hsS r l a b c d e)‖ ≤ ρ := by
      rw [hpS_eq hH1 hH2]
      have g3 := norm_resolv_mul_le H (r * outerPhi c d l (l - a - b))
      have e1 : ‖R₀ * (((r * outerPhi c d l (l - a - b) : ℝ) : ℂ) * Complex.I *
          (chR r (triHeat a (l - a)) c e l (l - a) *
            chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)))‖ =
          (‖R₀‖ * |r * outerPhi c d l (l - a - b)|) *
            (‖chR r (triHeat a (l - a)) c e l (l - a)‖ *
              ‖chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)‖) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
          Real.norm_eq_abs]
        ring
      rw [e1]
      have h3 : ‖chR r (triHeat a (l - a)) c e l (l - a)‖ *
          ‖chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)‖ ≤
          4 / 3 / (|r| * absk (l - a)) * (4 / 3 / (|r| * absk (l - a))) :=
        mul_le_mul hc1 hc2 (norm_nonneg _) (by positivity)
      calc _ ≤ 1 * (4 / 3 / (|r| * absk (l - a)) * (4 / 3 / (|r| * absk (l - a)))) :=
            mul_le_mul g3 h3 (by positivity) zero_le_one
        _ = ρ := by
            simp only [ρ]
            field_simp
            norm_num
    have t1 := term_le₃ c e d l (l - a) (l - a - b) y hRp hA hB
    have t2 := term_le₃ c e d l (l - a) (l - a - b) y hR1 hC hB
    have t3 := term_le₃ c e d l (l - a) (l - a - b) y hR2 hA hD
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
    calc _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ρ * (nA * nB) * ‖y‖ + ρ₁ * (nC * nB) * ‖y‖ + ρ₁ * (nA * nD) * ‖y‖ :=
          add_le_add (add_le_add t1 t2) t3
      _ = _ := by ring
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    ring

/-- The arithmetic of the comparable phase block. -/
lemma ph_comp_arith {q L M K x y ρ₀ : ℝ} (hq : 0 < q) (hL : 0 < L) (hK : 0 < K) (hM : 0 < M)
    (h4L : 4 * L ≤ M) (h4K : 4 * K ≤ M) (h1 : L ≤ 2 * K) (h2 : K ≤ 2 * L) (hρ : ρ₀ = 8 / (9 * M ^ 2))
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    4 * (2 * (16 / 9 / (q ^ 2 * M ^ 2) * ((16 * (M / L) ^ 2 * M * x) * (16 * (M / K) ^ 2 * M * y)) +
      ρ₀ * (4 / 3 / (q * M)) * ((16 * (L / M) ^ 2 * L * x) * (16 * (M / K) ^ 2 * M * y)) +
      ρ₀ * (4 / 3 / (q * M)) * ((16 * (M / L) ^ 2 * M * x) * (16 * (K / M) ^ 2 * K * y)))) ≤
      (2 ^ 13 / q ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) + 2 ^ 12 / q * K⁻¹) * (x * y) := by
  subst hρ
  have hLM : 16 * (L * K) ≤ M ^ 2 := by nlinarith only [h4L, h4K, hL, hK]
  have e1 : L ^ 3 / (M ^ 2 * K ^ 2) ≤ 1 / (4 * K) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h3 : L ^ 2 ≤ 4 * K ^ 2 := by nlinarith only [h1, hL, hK]
    calc L ^ 3 * (4 * K) = L ^ 2 * (4 * (L * K)) := by ring
      _ ≤ 4 * K ^ 2 * (4 * (L * K)) := by gcongr
      _ = 16 * (L * K) * K ^ 2 := by ring
      _ ≤ _ := by gcongr
  have e2 : K ^ 3 / (M ^ 2 * L ^ 2) ≤ 1 / (2 * K) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h3 : K ^ 3 ≤ (2 * L) ^ 3 := pow_le_pow_left₀ hK.le h2 3
    calc K ^ 3 * (2 * K) ≤ (2 * L) ^ 3 * (2 * K) := by gcongr
      _ = 16 * (L * K) * L ^ 2 := by ring
      _ ≤ _ := by gcongr
  have hxy : 0 ≤ x * y / q := by positivity
  have hxy2 : 0 ≤ x * y / q ^ 2 := by positivity
  have e3 : 4 * (2 * (16 / 9 / (q ^ 2 * M ^ 2) *
      ((16 * (M / L) ^ 2 * M * x) * (16 * (M / K) ^ 2 * M * y)) +
      8 / (9 * M ^ 2) * (4 / 3 / (q * M)) *
        ((16 * (L / M) ^ 2 * L * x) * (16 * (M / K) ^ 2 * M * y)) +
      8 / (9 * M ^ 2) * (4 / 3 / (q * M)) *
        ((16 * (M / L) ^ 2 * M * x) * (16 * (K / M) ^ 2 * K * y)))) =
      (x * y / q ^ 2) * (8 * (16 / 9 * 256) * (M ^ 4 / (L ^ 2 * K ^ 2))) +
      (x * y / q) * (8 * (32 / 27 * 256) * (L ^ 3 / (M ^ 2 * K ^ 2)) +
        8 * (32 / 27 * 256) * (K ^ 3 / (M ^ 2 * L ^ 2))) := by
    field_simp
    ring
  rw [e3]
  have hE : 0 ≤ M ^ 4 / (L ^ 2 * K ^ 2) := by positivity
  have t1 : (x * y / q ^ 2) * (8 * (16 / 9 * 256) * (M ^ 4 / (L ^ 2 * K ^ 2))) ≤
      (x * y / q ^ 2) * (2 ^ 13 * (M ^ 4 / (L ^ 2 * K ^ 2))) := by
    refine mul_le_mul_of_nonneg_left ?_ hxy2
    nlinarith only [hE]
  have t2 : (x * y / q) * (8 * (32 / 27 * 256) * (L ^ 3 / (M ^ 2 * K ^ 2)) +
      8 * (32 / 27 * 256) * (K ^ 3 / (M ^ 2 * L ^ 2))) ≤ (x * y / q) * (2 ^ 12 * K⁻¹) := by
    refine mul_le_mul_of_nonneg_left ?_ hxy
    have hi : 0 < K⁻¹ := inv_pos.2 hK
    have e4 : 1 / (4 * K) = K⁻¹ / 4 := by field_simp
    have e5 : 1 / (2 * K) = K⁻¹ / 2 := by field_simp
    rw [e4] at e1
    rw [e5] at e2
    nlinarith only [e1, e2, hi]
  calc _ ≤ (x * y / q ^ 2) * (2 ^ 13 * (M ^ 4 / (L ^ 2 * K ^ 2))) + (x * y / q) * (2 ^ 12 * K⁻¹) :=
        add_le_add t1 t2
    _ = _ := by ring

/-- **The phase block at comparable exteriors.** -/
theorem norm_Xph_comp {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) (h4L : 4 * absk l ≤ absk (l - a))
    (h4K : 4 * absk (l - a - b) ≤ absk (l - a)) (h1 : absk l ≤ 2 * absk (l - a - b))
    (h2 : absk (l - a - b) ≤ 2 * absk l) (v w : V3) :
    ‖outerInv r (heat4 l (l - a - b) a b) l (l - a - b)
        (tR 2 r τ l a b v w - tH 2 r τ l a b v w)‖ ≤
      (2 ^ 13 / |r| ^ 2 * (absk (l - a) ^ 4 / (absk l ^ 2 * absk (l - a - b) ^ 2)) +
        2 ^ 12 / |r| * (absk (l - a - b))⁻¹) * (‖v‖ * ‖w‖) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hvw := norm_nonneg v
  have hww := norm_nonneg w
  obtain ⟨-, -, -, hH4⟩ := high_heats hj0 h4L h4K
  have hH0 : 0 < heat4 l (l - a - b) a b := heat4_pos hj0 a b
  have hO : ∀ c d : Sgn, ‖resolv (-1) (heat4 l (l - a - b) a b)
      (r * outerPhi c d l (l - a - b))‖ ≤ 8 / (9 * absk (l - a) ^ 2) := fun c d => by
    refine (norm_resolv_le (Or.inr rfl) hH0 _).trans ?_
    rw [div_le_div_iff₀ hH0 (by positivity)]
    linarith
  refine (norm_outerInv_from_chan (K := _) ?_ fun c e y => chan_ph_gen (s := 2) hr τ ha hb hj
    h4L h4K hO v w c e y).trans ?_
  · simp only [wt]
    positivity
  · simp only [wt]
    exact ph_comp_arith hq hL hK hM h4L h4K h1 h2 rfl hvw hww

/-- The ordinary comparable sector. -/
lemma ord_comp_arith {q L K M H : ℝ} (hq : 0 < q) (hL : 0 < L) (hK : 0 < K) (hM : 0 ≤ M)
    (h1 : L ≤ 2 * K) (h2 : K ≤ 2 * L) (h3 : M ≤ 8 * K) (hH : L ^ 2 + K ^ 2 ≤ H) :
    2816 / q * (M / H) * Br (L ^ 2) (M ^ 2) (K ^ 2) ≤ 2 ^ 30 / q * K⁻¹ := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have e1 : M / H ≤ 8 * K⁻¹ := by
    rw [div_le_iff₀ hH0]
    have h4 : M * K ≤ 8 * H := by nlinarith only [h3, hK, hH, sq_nonneg L, hM]
    calc M = M * K * K⁻¹ := by field_simp
      _ ≤ 8 * H * K⁻¹ := by gcongr
      _ = _ := by ring
  have e2 : Br (L ^ 2) (M ^ 2) (K ^ 2) ≤ 32776 := by
    have t1 : L ^ 2 / K ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [h1, hL, hK]
    have t2 : K ^ 2 / L ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [h2, hL, hK]
    have t3 : 2 * (M ^ 2) ^ 2 / (L ^ 2 * K ^ 2) ≤ 32768 := by
      rw [div_le_iff₀ (by positivity)]
      have m1 : M ^ 2 ≤ 64 * K ^ 2 := by nlinarith only [h3, hM, hK]
      have m2 : (M ^ 2) ^ 2 ≤ (64 * K ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) m1 2
      have m3 : K ^ 2 ≤ 4 * L ^ 2 := by nlinarith only [h2, hL, hK]
      have m4 : K ^ 2 * K ^ 2 ≤ K ^ 2 * (4 * L ^ 2) := mul_le_mul_of_nonneg_left m3 (by positivity)
      nlinarith only [m2, m4]
    simp only [Br]
    linarith
  have hB0 : 0 ≤ Br (L ^ 2) (M ^ 2) (K ^ 2) := by
    simp only [Br]
    positivity
  have hi : 0 < K⁻¹ := inv_pos.2 hK
  calc 2816 / q * (M / H) * Br (L ^ 2) (M ^ 2) (K ^ 2)
      ≤ 2816 / q * (8 * K⁻¹) * 32776 := by gcongr
    _ = 738377728 / q * K⁻¹ := by ring
    _ ≤ _ := by
        have : 0 ≤ K⁻¹ / q := by positivity
        have e : ∀ c : ℝ, c / q * K⁻¹ = c * (K⁻¹ / q) := fun c => by ring
        rw [e, e]
        nlinarith only [this]

/-- The larger exterior, at separated exteriors. -/
lemma sep_data {L K : ℝ} (hL : 0 < L) (hK : 0 < K) (hc : ¬ (L ≤ 2 * K ∧ K ≤ 2 * L)) :
    ∃ F : ℝ, 0 < F ∧ L ≤ F ∧ K ≤ F ∧ F ≤ L + K ∧ F / 2 ≤ |K - L| ∧ (F = L ∨ F = K) := by
  rcases not_and_or.1 hc with h | h
  · rw [not_le] at h
    refine ⟨L, hL, le_rfl, by linarith, by linarith, ?_, Or.inl rfl⟩
    rw [abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self _)
  · rw [not_le] at h
    exact ⟨K, hK, by linarith, le_rfl, by linarith, le_trans (by linarith) (le_abs_self _),
      Or.inr rfl⟩

/-- The two parts at a large intermediate. -/
lemma X2b_split (r τ : ℝ) (f g : Field) (l a b : Mode) :
    X2b 2 r τ f g l a b =
      outerInv r (heat4 l (l - a - b) a b) l (l - a - b)
          (tR 2 r τ l a b (f a) (g b) - tH 2 r τ l a b (f a) (g b)) +
        outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (tH 2 r τ l a b (f a) (g b)) := by
  rw [X2b, ← twoRoot_eq_tR, ← outerInv_add, sub_add_cancel]

/-- **The block of `X₂` off the high tail of the intermediate.** -/
theorem norm_X2_diff {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) {D Pd T : ℝ} (hPd : 0 < Pd) (hT0 : 0 ≤ T)
    (hP : Pd ≤ absk (l - a) + absk l + absk (l - a - b))
    (hT : absk (l - a) ≤ D → 4 * absk l ≤ absk (l - a) → 4 * absk (l - a - b) ≤ absk (l - a) →
      absk (l - a) ^ 4 ≤ T)
    (hmask : ¬ (D < absk (l - a) ∧ 4 * absk l ≤ absk (l - a) ∧
      4 * absk (l - a - b) ≤ absk (l - a))) :
    ‖X2b 2 r τ f g l a b‖ ≤ (2 ^ 30 / |r| * kapC l (l - a - b) +
      2 ^ 21 / |r| ^ 2 * ((absk l + absk (l - a - b)) / Pd) * E2 (l, a, b) +
      2 ^ 16 / |r| ^ 2 * (T / (absk l ^ 2 * absk (l - a - b) ^ 2))) * (‖f a‖ * ‖g b‖) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hfg : 0 ≤ ‖f a‖ * ‖g b‖ := by positivity
  have hE2 := E2_nonneg (l, a, b)
  have hk0 := kapC_nonneg l (l - a - b)
  have hH0 := heat4_pos (l := l) hj0 a b
  have hHL : absk l ^ 2 + absk (l - a - b) ^ 2 ≤ heat4 l (l - a - b) a b := by
    rw [heat4_eq]
    nlinarith only [sq_nonneg (absk a), sq_nonneg (absk b)]
  have hBrE := Br_le_E2 (a := a) (b := b) hl0 hj0
  set L := absk l with hLd
  set K := absk (l - a - b) with hKd
  set M := absk (l - a) with hMd
  set A₁ := 2 ^ 30 / |r| * kapC l (l - a - b) with hA₁
  set A₂ := 2 ^ 21 / |r| ^ 2 * ((L + K) / Pd) * E2 (l, a, b) with hA₂
  set A₃ := 2 ^ 16 / |r| ^ 2 * (T / (L ^ 2 * K ^ 2)) with hA₃
  have h1 : 0 ≤ A₁ := by positivity
  have h2 : 0 ≤ A₂ := by positivity
  have h3 : 0 ≤ A₃ := by positivity
  by_cases hhi : 4 * L ≤ M ∧ 4 * K ≤ M
  · obtain ⟨h4L, h4K⟩ := hhi
    have hMD : M ≤ D := by
      by_contra hc
      exact hmask ⟨not_le.1 hc, h4L, h4K⟩
    have hE : M ^ 4 / (L ^ 2 * K ^ 2) ≤ T / (L ^ 2 * K ^ 2) := by
      have := hT hMD h4L h4K
      gcongr
    have hH1 := norm_Xheat_le (s := 2) le_rfl hr τ ha hb hj h4L h4K (f a) (g b)
    have eE : (M / L) ^ 2 * (M / K) ^ 2 = M ^ 4 / (L ^ 2 * K ^ 2) := by
      field_simp
    rw [eE] at hH1
    have hE0 : 0 ≤ M ^ 4 / (L ^ 2 * K ^ 2) := by positivity
    have hA3' : 2 ^ 16 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) ≤ A₃ := by
      rw [hA₃]
      gcongr
    rw [X2b_split]
    refine (norm_add_le _ _).trans ?_
    by_cases hc : L ≤ 2 * K ∧ K ≤ 2 * L
    · have hP1 := norm_Xph_comp hr τ ha hb hj h4L h4K hc.1 hc.2 (f a) (g b)
      have hk : kapC l (l - a - b) = K⁻¹ := by
        simp only [kapC, hc.1, hc.2, and_self, ite_true, ← hLd, ← hKd]
      have hi : 0 ≤ K⁻¹ := (inv_pos.2 hK).le
      have hA1' : 2 ^ 12 / |r| * K⁻¹ ≤ A₁ := by
        rw [hA₁, hk]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hq.le) hi
      have hsum := add_le_add hP1 hH1
      refine hsum.trans ?_
      have e : (2 ^ 13 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) + 2 ^ 12 / |r| * K⁻¹) *
          (‖f a‖ * ‖g b‖) + 2 ^ 15 * (M ^ 4 / (L ^ 2 * K ^ 2)) * (‖f a‖ * ‖g b‖) * (1 / |r| ^ 2) =
          (2 ^ 12 / |r| * K⁻¹ + (2 ^ 13 + 2 ^ 15) * (1 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)))) *
            (‖f a‖ * ‖g b‖) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_right ?_ hfg
      have e3 : 2 ^ 16 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) =
          2 ^ 16 * (1 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2))) := by ring
      rw [e3] at hA3'
      have h0 : 0 ≤ 1 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) := by positivity
      linarith
    · obtain ⟨F, hF, hLF, hKF, -, hsep, hFc⟩ := sep_data hL hK hc
      have h4F : 4 * F ≤ M := by
        rcases hFc with e | e <;> rw [e] <;> assumption
      have hP1 := norm_Xph_sep hr τ ha hb hj hF hLF hKF h4F hsep
        (H := heat4 l (l - a - b) a b) (f a) (g b)
      refine (add_le_add hP1 hH1).trans ?_
      have e : 2 ^ 14 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) * (‖f a‖ * ‖g b‖) +
          2 ^ 15 * (M ^ 4 / (L ^ 2 * K ^ 2)) * (‖f a‖ * ‖g b‖) * (1 / |r| ^ 2) =
          (2 ^ 14 + 2 ^ 15) * (1 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2))) * (‖f a‖ * ‖g b‖) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_right ?_ hfg
      have e3 : 2 ^ 16 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) =
          2 ^ 16 * (1 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2))) := by ring
      rw [e3] at hA3'
      have h0 : 0 ≤ 1 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) := by positivity
      linarith
  · have hBr0 : 0 ≤ Br (L ^ 2) (M ^ 2) (K ^ 2) := by
      simp only [Br]
      positivity
    have hBrE' : Br (L ^ 2) (M ^ 2) (K ^ 2) ≤ 14 * E2 (l, a, b) := by
      rw [hLd, hKd, hMd, absk_sq, absk_sq, absk_sq]
      exact hBrE
    have hn := not_and_or.1 hhi
    by_cases hc : L ≤ 2 * K ∧ K ≤ 2 * L
    · have hM8 : M ≤ 8 * K := by
        rcases hn with h | h
        · rw [not_le] at h
          linarith [hc.1]
        · rw [not_le] at h
          linarith
      have hN := norm_X2b_le (Or.inr rfl) hr τ f g ha hb hj
      have hA := ord_comp_arith hq hL hK hM.le hc.1 hc.2 hM8 hHL
      have hk : kapC l (l - a - b) = K⁻¹ := by
        simp only [kapC, hc.1, hc.2, and_self, ite_true, ← hLd, ← hKd]
      have hA' : 2816 / |r| * (M / heat4 l (l - a - b) a b) * Br (L ^ 2) (M ^ 2) (K ^ 2) ≤ A₁ := by
        rw [hA₁, hk]
        exact hA
      calc _ ≤ 2816 / |r| * (M / heat4 l (l - a - b) a b) * (‖f a‖ * ‖g b‖) *
            Br (L ^ 2) (M ^ 2) (K ^ 2) := hN
        _ = 2816 / |r| * (M / heat4 l (l - a - b) a b) * Br (L ^ 2) (M ^ 2) (K ^ 2) *
            (‖f a‖ * ‖g b‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hfg
    · obtain ⟨F, hF, hLF, hKF, hFs, hsep, -⟩ := sep_data hL hK hc
      have hM4 : M ≤ 4 * F := by
        rcases hn with h | h
        · rw [not_le] at h
          linarith
        · rw [not_le] at h
          linarith
      have hN := norm_X2_sep hr τ f g ha hb hj hF hsep
      rw [← absk_sq l, ← absk_sq (l - a), ← absk_sq (l - a - b)] at hN
      have hR : 1 / 6 ≤ (L + K) / Pd := by
        rw [div_le_div_iff₀ (by norm_num) hPd]
        linarith
      have hA' : 5632 / (|r| ^ 2 * F) * M * Br (L ^ 2) (M ^ 2) (K ^ 2) ≤ A₂ := by
        have h4 : 5632 / (|r| ^ 2 * F) * M ≤ 22528 / |r| ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have : 0 ≤ |r| ^ 2 := by positivity
          nlinarith only [hM4, this]
        have h5 : 22528 / |r| ^ 2 * (14 * E2 (l, a, b)) ≤
            2 ^ 21 / |r| ^ 2 * (1 / 6) * E2 (l, a, b) := by
          have h6 : 0 ≤ 1 / |r| ^ 2 * E2 (l, a, b) := by positivity
          have e1 : 22528 / |r| ^ 2 * (14 * E2 (l, a, b)) =
              315392 * (1 / |r| ^ 2 * E2 (l, a, b)) := by ring
          have e2 : 2 ^ 21 / |r| ^ 2 * (1 / 6) * E2 (l, a, b) =
              2 ^ 21 / 6 * (1 / |r| ^ 2 * E2 (l, a, b)) := by ring
          rw [e1, e2]
          nlinarith only [h6]
        have h7 : 2 ^ 21 / |r| ^ 2 * (1 / 6) * E2 (l, a, b) ≤ A₂ := by
          rw [hA₂]
          gcongr
        calc _ ≤ 22528 / |r| ^ 2 * (14 * E2 (l, a, b)) := mul_le_mul h4 hBrE' hBr0 (by positivity)
          _ ≤ _ := h5.trans h7
      calc _ ≤ 5632 / (|r| ^ 2 * F) * M * (‖f a‖ * ‖g b‖) * Br (L ^ 2) (M ^ 2) (K ^ 2) := hN
        _ = 5632 / (|r| ^ 2 * F) * M * Br (L ^ 2) (M ^ 2) (K ^ 2) * (‖f a‖ * ‖g b‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hfg

end OVNS.Quant.Metric

end
