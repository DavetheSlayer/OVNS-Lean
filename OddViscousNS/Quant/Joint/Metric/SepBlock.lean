import OddViscousNS.Quant.Joint.Metric.Q3Link

/-!
# The primitive-separated high-last sector: the blocks (step J5, node N9)

Body 43 (LOCAL663).  On `max(L, K) > 2 min(L, K)` the outer denominator satisfies `|d₂| ≥ q F₀/2`,
`F₀ = max(L, K)`.  At a large intermediate the phase numerator meets the same `δ_lk` in the outer
denominator: `|irδ|/|d₂| ≤ 1` (`hpS_eq`, `chan_ph_sep`), so the phase block has no factor `(L + K)/M`
left and gains `q⁻²`; the heat block gains `q⁻³`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-- A block `outerInv` from its channels. -/
lemma norm_outerInv_from_chan {r H K : ℝ} (hK : 0 ≤ K) {l j : Mode} {T : Blk}
    (h : ∀ c e y, ‖hel c l (outerInv r H l j T (hel e j y))‖ ≤ K * ‖y‖) :
    ‖outerInv r H l j T‖ ≤ 4 * K := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have e : outerInv r H l j T y =
      ∑ c : Sgn, ∑ e : Sgn, hel c l (outerInv r H l j T (hel e j y)) := by
    simp only [hel_outerInv]
    simp only [outerInv, sum_apply, smul_apply, ContinuousLinearMap.comp_apply, helL_apply]
  rw [e]
  refine (norm_sum_le_of_le _ fun c _ => norm_sum_le_of_le _ fun e _ => h c e y).trans
    (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

/-- The phase numerator of the two inverses is the exterior phase. -/
lemma hpS_eq {r : ℝ} {l a b : Mode} {c d e : Sgn} (h1 : 0 < triHeat a (l - a))
    (h2 : 0 < triHeat b (l - a - b)) :
    chR r (triHeat a (l - a)) c e l (l - a) +
        chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b) - hsS r l a b c d e =
      ((r * outerPhi c d l (l - a - b) : ℝ) : ℂ) * Complex.I *
        (chR r (triHeat a (l - a)) c e l (l - a) *
          chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)) := by
  simp only [chR, hsS]
  rw [resolv_add h1.ne' h2.ne']
  have e1 : r * (lam e (l - a) - lam c l) + r * (lam d (l - a - b) - lam e (l - a)) =
      r * outerPhi c d l (l - a - b) := by
    simp only [outerPhi]
    ring
  rw [e1]
  ring

/-- A resolvent absorbs its phase. -/
lemma norm_resolv_mul_le (H z : ℝ) : ‖resolv (-1) H z‖ * |z| ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · have := norm_resolv_le_abs H hz
    have h0 : 0 < |z| := abs_pos.2 hz
    calc _ ≤ 1 / |z| * |z| := mul_le_mul_of_nonneg_right this h0.le
      _ = 1 := by field_simp

/-- The exterior phase of the outer resolvent at separated exteriors. -/
lemma norm_resolv_sep {r H d : ℝ} (hr : r ≠ 0) {l j : Mode} (h2 : l 2 = j 2) (hn : j 2 ≠ 0)
    (hd : 0 < d) (hsep : d ≤ |absk j - absk l|) (c e : Sgn) :
    ‖resolv (-1) H (r * outerPhi c e l j)‖ ≤ 1 / (|r| * d) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hphi : d ≤ |outerPhi c e l j| := hsep.trans (lam_sep h2 hn c e)
  have hz : r * outerPhi c e l j ≠ 0 := mul_ne_zero hr (abs_pos.1 (hd.trans_le hphi))
  refine (norm_resolv_le_abs H hz).trans ?_
  rw [abs_mul]
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hphi hr0.le)

private lemma term_le'' {R : ℂ} {ρ nA nB : ℝ} {T T' : V3 →L[ℂ] V3} (c e d : Sgn) (l m j : Mode)
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

/-- A channel of the phase block at separated exteriors. -/
lemma chan_ph_sep {s : ℕ} {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) {d₀ H : ℝ} (hd : 0 < d₀)
    (hsep : d₀ ≤ |absk (l - a - b) - absk l|) (v w : V3) (c d : Sgn) (y : V3) :
    ‖hel c l (outerInv r H l (l - a - b) (tR s r τ l a b v w - tH s r τ l a b v w)
      (hel d (l - a - b) y))‖ ≤
      2 * (16 / 9 / (|r| ^ 2 * absk (l - a) ^ 2) *
          ((16 * wt s (l - a) l * absk (l - a) * ‖v‖) *
            (16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖)) +
        1 / (|r| * d₀) * (4 / 3 / (|r| * absk (l - a))) *
          ((16 * wt s l (l - a) * absk l * ‖v‖) *
            (16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖)) +
        1 / (|r| * d₀) * (4 / 3 / (|r| * absk (l - a))) *
          ((16 * wt s (l - a) l * absk (l - a) * ‖v‖) *
            (16 * wt s (l - a - b) (l - a) * absk (l - a - b) * ‖w‖))) * ‖y‖ := by
  obtain ⟨-, hm0, hj0⟩ := fast_labels ha hb hj
  obtain ⟨hne₁, hne₂, hz₁, hz₂, -, hN⟩ := high_data hr ha hb hj hL hJ
  obtain ⟨hH1, hH2, -, -⟩ := high_heats hj0 hL hJ
  have hq : 0 < |r| := abs_pos.2 hr
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  obtain ⟨hA, hB, hC, hD⟩ := edge_sizes (s := s) τ (l := l) (a := a) (b := b) v w
  have hl2 : l 2 = (l - a - b) 2 := by simp [ha, hb]
  have hO := norm_resolv_sep (H := H) hr hl2 hj hd hsep c d
  set R₀ := resolv (-1) H (r * outerPhi c d l (l - a - b)) with hR₀
  rw [hel_outerInv, chan_tP s r τ ha hb hj hne₁ hne₂, Finset.smul_sum]
  set nA := 16 * wt s (l - a) l * absk (l - a) * ‖v‖
  set nB := 16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖
  set nC := 16 * wt s l (l - a) * absk l * ‖v‖
  set nD := 16 * wt s (l - a - b) (l - a) * absk (l - a - b) * ‖w‖
  set ρ := 16 / 9 / (|r| ^ 2 * absk (l - a) ^ 2)
  set ρ₁ := 1 / (|r| * d₀) * (4 / 3 / (|r| * absk (l - a)))
  refine (norm_sum_le_of_le (n := fun _ => (ρ * (nA * nB) + ρ₁ * (nC * nB) + ρ₁ * (nA * nD)) * ‖y‖)
    _ fun e _ => ?_).trans (le_of_eq ?_)
  · have hc1 : ‖chR r (triHeat a (l - a)) c e l (l - a)‖ ≤ 4 / 3 / (|r| * absk (l - a)) :=
      rho₁_le hq hN hM (hz₁ c e)
    have hc2 : ‖chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)‖ ≤
        4 / 3 / (|r| * absk (l - a)) := rho₁_le hq hN hM (hz₂ d e)
    have hR1 : ‖R₀ * chR r (triHeat a (l - a)) c e l (l - a)‖ ≤ ρ₁ := by
      rw [norm_mul]
      exact mul_le_mul hO hc1 (norm_nonneg _) (by positivity)
    have hR2 : ‖R₀ * chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)‖ ≤ ρ₁ := by
      rw [norm_mul]
      exact mul_le_mul hO hc2 (norm_nonneg _) (by positivity)
    have hRp : ‖R₀ * (chR r (triHeat a (l - a)) c e l (l - a) +
        chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b) - hsS r l a b c d e)‖ ≤ ρ := by
      rw [hpS_eq hH1 hH2]
      have g1 := resolv_gap_le (H := triHeat a (l - a)) hq hN hM (hz₁ c e)
      have g2 := resolv_gap_le (H := triHeat b (l - a - b)) hq hN hM (hz₂ d e)
      have g3 := norm_resolv_mul_le H (r * outerPhi c d l (l - a - b))
      have hNM : 0 < |r| * (|((l - a) 2 : ℝ)| * absk (l - a)) := by
        have : 0 < |((l - a) 2 : ℝ)| := by linarith
        positivity
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
    have t1 := term_le'' c e d l (l - a) (l - a - b) y hRp hA hB
    have t2 := term_le'' c e d l (l - a) (l - a - b) y hR1 hC hB
    have t3 := term_le'' c e d l (l - a) (l - a - b) y hR2 hA hD
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
    calc _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ρ * (nA * nB) * ‖y‖ + ρ₁ * (nC * nB) * ‖y‖ + ρ₁ * (nA * nD) * ‖y‖ :=
          add_le_add (add_le_add t1 t2) t3
      _ = _ := by ring
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    ring

/-- The arithmetic of the phase block. -/
lemma ph_sep_arith {q L M K F x y : ℝ} (hq : 0 < q) (hL : 0 < L) (hK : 0 < K) (hF : 0 < F)
    (hLF : L ≤ F) (hKF : K ≤ F) (h4 : 4 * F ≤ M) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    4 * (2 * (16 / 9 / (q ^ 2 * M ^ 2) * ((16 * (M / L) ^ 2 * M * x) * (16 * (M / K) ^ 2 * M * y)) +
      1 / (q * (F / 2)) * (4 / 3 / (q * M)) *
        ((16 * (L / M) ^ 2 * L * x) * (16 * (M / K) ^ 2 * M * y)) +
      1 / (q * (F / 2)) * (4 / 3 / (q * M)) *
        ((16 * (M / L) ^ 2 * M * x) * (16 * (K / M) ^ 2 * K * y)))) ≤
      2 ^ 14 / q ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) * (x * y) := by
  have hM : 0 < M := by linarith
  have hLM : L ≤ M := by linarith
  have hKM : K ≤ M := by linarith
  have e1 : L ^ 3 / (F * K ^ 2) ≤ M ^ 4 / (L ^ 2 * K ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have a1 : L ^ 4 ≤ M ^ 4 := pow_le_pow_left₀ hL.le hLM 4
    calc L ^ 3 * (L ^ 2 * K ^ 2) = L * L ^ 4 * K ^ 2 := by ring
      _ ≤ F * M ^ 4 * K ^ 2 := by gcongr
      _ = _ := by ring
  have e2 : K ^ 3 / (F * L ^ 2) ≤ M ^ 4 / (L ^ 2 * K ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have a1 : K ^ 4 ≤ M ^ 4 := pow_le_pow_left₀ hK.le hKM 4
    calc K ^ 3 * (L ^ 2 * K ^ 2) = K * K ^ 4 * L ^ 2 := by ring
      _ ≤ F * M ^ 4 * L ^ 2 := by gcongr
      _ = _ := by ring
  have hxy : 0 ≤ x * y / q ^ 2 := by positivity
  have e3 : 4 * (2 * (16 / 9 / (q ^ 2 * M ^ 2) *
      ((16 * (M / L) ^ 2 * M * x) * (16 * (M / K) ^ 2 * M * y)) +
      1 / (q * (F / 2)) * (4 / 3 / (q * M)) *
        ((16 * (L / M) ^ 2 * L * x) * (16 * (M / K) ^ 2 * M * y)) +
      1 / (q * (F / 2)) * (4 / 3 / (q * M)) *
        ((16 * (M / L) ^ 2 * M * x) * (16 * (K / M) ^ 2 * K * y)))) =
      (x * y / q ^ 2) * (8 * (16 / 9 * 256) * (M ^ 4 / (L ^ 2 * K ^ 2)) +
        8 * (8 / 3 * 256) * (L ^ 3 / (F * K ^ 2)) + 8 * (8 / 3 * 256) * (K ^ 3 / (F * L ^ 2))) := by
    field_simp
    ring
  rw [e3]
  have hE : 0 ≤ M ^ 4 / (L ^ 2 * K ^ 2) := by positivity
  calc _ ≤ (x * y / q ^ 2) * (2 ^ 14 * (M ^ 4 / (L ^ 2 * K ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hxy
        linarith
    _ = _ := by ring

/-- **The phase block at separated exteriors**: the exterior phase is paid once. -/
theorem norm_Xph_sep {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) {F H : ℝ} (hF : 0 < F) (hLF : absk l ≤ F)
    (hKF : absk (l - a - b) ≤ F) (h4 : 4 * F ≤ absk (l - a))
    (hsep : F / 2 ≤ |absk (l - a - b) - absk l|) (v w : V3) :
    ‖outerInv r H l (l - a - b) (tR 2 r τ l a b v w - tH 2 r τ l a b v w)‖ ≤
      2 ^ 14 / |r| ^ 2 * (absk (l - a) ^ 4 / (absk l ^ 2 * absk (l - a - b) ^ 2)) *
        (‖v‖ * ‖w‖) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hvw := norm_nonneg v
  have hww := norm_nonneg w
  have h4L : 4 * absk l ≤ absk (l - a) := by linarith
  have h4K : 4 * absk (l - a - b) ≤ absk (l - a) := by linarith
  refine (norm_outerInv_from_chan (K := _) ?_ fun c e y => chan_ph_sep hr τ ha hb hj h4L h4K
    (by positivity : 0 < F / 2) hsep v w c e y).trans ?_
  · simp only [wt]
    positivity
  · simp only [wt]
    exact ph_sep_arith hq hL hK hF hLF hKF h4 hvw hww

/-- **The heat block at separated exteriors**: the exterior phase and the inner phases are different
denominators. -/
theorem norm_Xheat_sep {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) {F H : ℝ} (hF : 0 < F) (hLF : absk l ≤ F)
    (hKF : absk (l - a - b) ≤ F) (h4 : 4 * F ≤ absk (l - a))
    (hsep : F / 2 ≤ |absk (l - a - b) - absk l|) (v w : V3) :
    ‖outerInv r H l (l - a - b) (tH 2 r τ l a b v w)‖ ≤
      2 ^ 16 / (|r| ^ 3 * F) * (absk (l - a) ^ 6 / (absk l ^ 2 * absk (l - a - b) ^ 2)) *
        (‖v‖ * ‖w‖) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hvw := norm_nonneg v
  have hww := norm_nonneg w
  have h4L : 4 * absk l ≤ absk (l - a) := by linarith
  have h4K : 4 * absk (l - a - b) ≤ absk (l - a) := by linarith
  have hl2 : l 2 = (l - a - b) 2 := by simp [ha, hb]
  have hb0 : 0 ≤ 2 ^ 14 / (|r| ^ 3 * F) *
      (absk (l - a) ^ 6 / (absk l ^ 2 * absk (l - a - b) ^ 2)) * (‖v‖ * ‖w‖) := by positivity
  have hch : ∀ c e y, ‖hel c l (outerInv r H l (l - a - b) (tH 2 r τ l a b v w)
      (hel e (l - a - b) y))‖ ≤ 2 ^ 14 / (|r| ^ 3 * F) *
        (absk (l - a) ^ 6 / (absk l ^ 2 * absk (l - a - b) ^ 2)) * (‖v‖ * ‖w‖) * ‖y‖ := by
    intro c e y
    rw [hel_outerInv, norm_smul]
    have h1 := norm_resolv_sep (H := H) hr hl2 hj (by positivity : 0 < F / 2) hsep c e
    have h2 := high_chan_heat (s := 2) hr τ ha hb hj h4L h4K v w c e y
    simp only [wt] at h2
    refine (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans ?_
    have hP : 0 ≤ 1 / (|r| ^ 3 * F) * (absk (l - a) ^ 6 / (absk l ^ 2 * absk (l - a - b) ^ 2)) *
        (‖v‖ * ‖w‖) * ‖y‖ := by positivity
    have e1 : 1 / (|r| * (F / 2)) * (2 * (32 / 3 / |r| ^ 2 *
        (16 * (absk (l - a) / absk l) ^ 2 * absk (l - a) * ‖v‖ *
          (16 * (absk (l - a) / absk (l - a - b)) ^ 2 * absk (l - a) * ‖w‖))) * ‖y‖) =
        32768 / 3 * (1 / (|r| ^ 3 * F) * (absk (l - a) ^ 6 / (absk l ^ 2 * absk (l - a - b) ^ 2)) *
          (‖v‖ * ‖w‖) * ‖y‖) := by
      field_simp
      ring
    have e2 : 2 ^ 14 / (|r| ^ 3 * F) * (absk (l - a) ^ 6 / (absk l ^ 2 * absk (l - a - b) ^ 2)) *
        (‖v‖ * ‖w‖) * ‖y‖ = 2 ^ 14 * (1 / (|r| ^ 3 * F) *
          (absk (l - a) ^ 6 / (absk l ^ 2 * absk (l - a - b) ^ 2)) * (‖v‖ * ‖w‖) * ‖y‖) := by
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by norm_num) hP
  refine (norm_outerInv_from_chan hb0 hch).trans (le_of_eq ?_)
  ring

/-- The edge of the third leaf at weight two. -/
lemma norm_last_edge (τ : ℝ) {x : I4} (h : Field) :
    ‖Lb 2 τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x) (h x.2.2.2)‖ ≤
      16 * (absk (x.1 - x.2.1 - x.2.2.1) / absk (inJ x)) ^ 2 * absk (x.1 - x.2.1 - x.2.2.1) *
        ‖h x.2.2.2‖ := by
  have ek : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
    simp only [inJ]
    abel
  exact norm_Lb_le 2 τ ek _

/-- `X₂` on the ordinary separated sector. -/
lemma norm_X2_sep {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) {F : ℝ} (hF : 0 < F)
    (hsep : F / 2 ≤ |absk (l - a - b) - absk l|) :
    ‖X2b 2 r τ f g l a b‖ ≤ 5632 / (|r| ^ 2 * F) * absk (l - a) * (‖f a‖ * ‖g b‖) *
      Br (absSq l) (absSq (l - a)) (absSq (l - a - b)) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hl2 : l 2 = (l - a - b) 2 := by simp [ha, hb]
  have h1 := norm_outerInv_sep (H := heat4 l (l - a - b) a b) hr hl2 hj (by positivity : 0 < F / 2)
    hsep (tR 2 r τ l a b (f a) (g b))
  have h2 := norm_tR_le (s := 2) (Or.inr rfl) hr τ ha hb hj (f a) (g b)
  have hX : X2b 2 r τ f g l a b =
      outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (tR 2 r τ l a b (f a) (g b)) := by
    rw [X2b, ← twoRoot_eq_tR]
  rw [hX]
  refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
  field_simp
  ring

/-- `Z` on the separated sector. -/
lemma norm_Z_sep {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) {F : ℝ} (hF : 0 < F)
    (hsep : F / 2 ≤ |absk (l - a - b) - absk l|) :
    ‖Zb 2 r τ f g l a b‖ ≤ 2816 / (|r| ^ 2 * F) * absk (a + b) * (‖f a‖ * ‖g b‖) *
      (absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hl2 : l 2 = (l - a - b) 2 := by simp [ha, hb]
  have h1 := norm_outerInv_sep (H := heat4 l (l - a - b) a b) hr hl2 hj (by positivity : 0 < F / 2)
    hsep (X1b 2 r τ (a + b) l (l - a - b) (slowV a b (f a) (g b)))
  have e1 : (a + b) + (l - a - b) = l := by abel
  have hab : (a + b) 2 = 0 := by simp [ha, hb]
  have h2 := norm_X1b_two_le hr τ e1 hab hj (slowV a b (f a) (g b))
  have h3 := norm_slowV_le a b (f a) (g b)
  have hP := absk_nonneg (a + b)
  have hL := absSq_nonneg l
  have hK := absSq_nonneg (l - a - b)
  have hA := norm_nonneg (f a)
  have hB := norm_nonneg (g b)
  set R := absSq l / absSq (l - a - b) + absSq (l - a - b) / absSq l with hR
  have hR0 : 0 ≤ R := by positivity
  have h4 : ‖X1b 2 r τ (a + b) l (l - a - b) (slowV a b (f a) (g b))‖ ≤
      44 / |r| * (8 * absk (a + b) * ‖f a‖ * ‖g b‖) * R := h2.trans (by gcongr)
  refine h1.trans ((mul_le_mul_of_nonneg_left h4 (by positivity)).trans (le_of_eq ?_))
  field_simp
  ring

end OVNS.Quant.Metric

end
