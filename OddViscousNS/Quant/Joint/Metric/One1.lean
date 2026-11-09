import OddViscousNS.Quant.Joint.Metric.DiffZ

/-!
# Weight one: the blocks of `X₂`, `Z` (step J5, node N10)

Unit: `TIMED_METRIC_PROOF_V2.md` §8.
* `norm_Xheat_one`, `norm_Xph_one`: the signed split at weight one: `q⁻² M²/(LK)` and
  `q⁻¹ (1/L + 1/K)`;
* `norm_X2_one`: the first-weight kernel of §8.4;
* `norm_Y_half_one`: the output half, (8.1), before the sum.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-- The arithmetic of the heat block at weight one. -/
lemma heat_one_arith {q L M K H x y : ℝ} (hq : 0 < q) (hL : 0 < L) (hK : 0 < K) (hM : 0 < M)
    (hH : 9 / 8 * M ^ 2 ≤ H) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    4 / H * (2 * (32 / 3 / q ^ 2 * ((16 * (M / L) * M * x) * (16 * (M / K) * M * y)))) ≤
      2 ^ 15 / q ^ 2 * (M ^ 2 / (L * K)) * (x * y) := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hH' : 4 / H ≤ 32 / 9 / M ^ 2 := by
    rw [div_le_div_iff₀ hH0 (by positivity)]
    linarith
  have hT : 0 ≤ M ^ 2 / (L * K) * (x * y) / q ^ 2 := by positivity
  calc _ ≤ 32 / 9 / M ^ 2 * (2 * (32 / 3 / q ^ 2 * ((16 * (M / L) * M * x) * (16 * (M / K) * M * y)))) :=
        mul_le_mul_of_nonneg_right hH' (by positivity)
    _ = (32 / 9 * (2 * (32 / 3 * 256))) * (M ^ 2 / (L * K) * (x * y) / q ^ 2) := by
        field_simp
        ring
    _ ≤ 2 ^ 15 * (M ^ 2 / (L * K) * (x * y) / q ^ 2) := by
        nlinarith only [hT]
    _ = _ := by ring

/-- **The heat block at weight one.** -/
theorem norm_Xheat_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) (v w : V3) :
    ‖outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (tH 1 r τ l a b v w)‖ ≤
      2 ^ 15 / |r| ^ 2 * (absk (l - a) ^ 2 / (absk l * absk (l - a - b))) * (‖v‖ * ‖w‖) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hL0 : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK0 : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  obtain ⟨-, -, -, hH4⟩ := high_heats hj0 hL hJ
  have hH0 : 0 < heat4 l (l - a - b) a b := heat4_pos hj0 a b
  have hvw := norm_nonneg v
  have hww := norm_nonneg w
  refine (norm_outerInv_of_chan hH0 (K := _) ?_ r l (l - a - b) _
    fun c e y => high_chan_heat (s := 1) hr τ ha hb hj hL hJ v w c e y).trans ?_
  · simp only [wt, pow_one]
    positivity
  · simp only [wt, pow_one]
    exact heat_one_arith hq hL0 hK0 hM hH4 hvw hww

/-- The arithmetic of the phase block at weight one. -/
lemma ph_one_arith {q L M K H x y : ℝ} (hq : 0 < q) (hL : 0 < L) (hK : 0 < K) (hM : 0 < M)
    (h4L : 4 * L ≤ M) (h4K : 4 * K ≤ M) (hH : 9 / 8 * M ^ 2 ≤ H) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    4 / H * (2 * (16 / 9 * (L + K) / (q * M ^ 2) * ((16 * (M / L) * M * x) * (16 * (M / K) * M * y)) +
      4 / 3 / (q * M) * ((16 * (L / M) * L * x) * (16 * (M / K) * M * y)) +
      4 / 3 / (q * M) * ((16 * (M / L) * M * x) * (16 * (K / M) * K * y)))) ≤
      2 ^ 13 / q * (L⁻¹ + K⁻¹) * (x * y) := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hH' : 4 / H ≤ 32 / 9 / M ^ 2 := by
    rw [div_le_div_iff₀ hH0 (by positivity)]
    linarith
  have e1 : L ^ 2 / (M ^ 2 * K) ≤ K⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    have : L ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hL.le (by linarith) 2
    calc L ^ 2 ≤ M ^ 2 := this
      _ = K⁻¹ * (M ^ 2 * K) := by field_simp
  have e2 : K ^ 2 / (M ^ 2 * L) ≤ L⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    have : K ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hK.le (by linarith) 2
    calc K ^ 2 ≤ M ^ 2 := this
      _ = L⁻¹ * (M ^ 2 * L) := by field_simp
  have hxy : 0 ≤ x * y / q := by positivity
  have hS0 : 0 ≤ 16 / 9 * (L + K) / (q * M ^ 2) * ((16 * (M / L) * M * x) * (16 * (M / K) * M * y)) +
      4 / 3 / (q * M) * ((16 * (L / M) * L * x) * (16 * (M / K) * M * y)) +
      4 / 3 / (q * M) * ((16 * (M / L) * M * x) * (16 * (K / M) * K * y)) := by positivity
  have e3 : 32 / 9 / M ^ 2 * (2 * (16 / 9 * (L + K) / (q * M ^ 2) *
      ((16 * (M / L) * M * x) * (16 * (M / K) * M * y)) +
      4 / 3 / (q * M) * ((16 * (L / M) * L * x) * (16 * (M / K) * M * y)) +
      4 / 3 / (q * M) * ((16 * (M / L) * M * x) * (16 * (K / M) * K * y)))) =
      (x * y / q) * (32 / 9 * (2 * (16 / 9 * 256)) * (L⁻¹ + K⁻¹) +
        32 / 9 * (2 * (4 / 3 * 256)) * (L ^ 2 / (M ^ 2 * K)) +
        32 / 9 * (2 * (4 / 3 * 256)) * (K ^ 2 / (M ^ 2 * L))) := by
    field_simp
    ring
  have hL' := inv_pos.2 hL
  have hK' := inv_pos.2 hK
  calc _ ≤ _ := mul_le_mul_of_nonneg_right hH' (by positivity)
    _ = _ := e3
    _ ≤ (x * y / q) * (2 ^ 13 * (L⁻¹ + K⁻¹)) := by
        refine mul_le_mul_of_nonneg_left ?_ hxy
        nlinarith only [e1, e2, hL', hK']
    _ = _ := by ring

/-- **The phase block at weight one.** -/
theorem norm_Xph_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) (v w : V3) :
    ‖outerInv r (heat4 l (l - a - b) a b) l (l - a - b)
      (tR 1 r τ l a b v w - tH 1 r τ l a b v w)‖ ≤
      2 ^ 13 / |r| * ((absk l)⁻¹ + (absk (l - a - b))⁻¹) * (‖v‖ * ‖w‖) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hL0 : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK0 : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  obtain ⟨-, -, -, hH4⟩ := high_heats hj0 hL hJ
  have hH0 : 0 < heat4 l (l - a - b) a b := heat4_pos hj0 a b
  have hvw := norm_nonneg v
  have hww := norm_nonneg w
  refine (norm_outerInv_of_chan hH0 (K := _) ?_ r l (l - a - b) _
    fun c e y => high_chan_ph (s := 1) hr τ ha hb hj hL hJ v w c e y).trans ?_
  · simp only [wt, pow_one]
    positivity
  · simp only [wt, pow_one]
    exact ph_one_arith hq hL0 hK0 hM hL hJ hH4 hvw hww

/-- The two parts of `X₂`, at any weight. -/
lemma X2b_split' (s : ℕ) (r τ : ℝ) (f g : Field) (l a b : Mode) :
    X2b s r τ f g l a b =
      outerInv r (heat4 l (l - a - b) a b) l (l - a - b)
          (tR s r τ l a b (f a) (g b) - tH s r τ l a b (f a) (g b)) +
        outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (tH s r τ l a b (f a) (g b)) := by
  rw [X2b, ← twoRoot_eq_tR, ← outerInv_add, sub_add_cancel]

/-- The ordinary sector at weight one. -/
lemma ord_one_arith {L M K H : ℝ} (hL : 0 < L) (hK : 0 < K) (hM0 : 0 ≤ M)
    (hM : M < 4 * L ∨ M < 4 * K) (hH : L ^ 2 + K ^ 2 ≤ H) (hM2 : M ^ 2 ≤ 2 * H) :
    M / H * Br₁ L M K ≤ 24 * (L⁻¹ + K⁻¹) := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hLi := inv_pos.2 hL
  have hKi := inv_pos.2 hK
  have hH1 : L ^ 2 ≤ H := by nlinarith only [hH, sq_nonneg K]
  have hH2 : K ^ 2 ≤ H := by nlinarith only [hH, sq_nonneg L]
  rcases hM with h | h
  · have t1 : M / H * (L / K) ≤ 4 * K⁻¹ := by
      rw [div_mul_div_comm, div_le_iff₀ (by positivity), ← div_eq_mul_inv (4 : ℝ) K,
        div_mul_eq_mul_div, le_div_iff₀ hK]
      nlinarith only [h, hL, hK, hH1, mul_pos hL hK, hH0,
        mul_le_mul_of_nonneg_right hH1 hK.le]
    have t2 : M / H * (2 * M ^ 2 / (L * K)) ≤ 16 * K⁻¹ := by
      have e : M / H * (2 * M ^ 2 / (L * K)) = (M ^ 2 / H) * (2 * (M / L)) * K⁻¹ := by
        field_simp
      rw [e]
      have h1 : M ^ 2 / H ≤ 2 := (div_le_iff₀ hH0).2 hM2
      have h2 : M / L ≤ 4 := (div_le_iff₀ hL).2 h.le
      refine mul_le_mul_of_nonneg_right ?_ hKi.le
      have h3 : 0 ≤ M / L := by positivity
      have h4 : 0 ≤ M ^ 2 / H := by positivity
      nlinarith only [h1, h2, h3, h4]
    have t3 : M / H * (K / L) ≤ 4 * K⁻¹ := by
      have e : M / H * (K / L) = (M / L) * (K ^ 2 / H) * K⁻¹ := by
        field_simp
      rw [e]
      have h2 : M / L ≤ 4 := (div_le_iff₀ hL).2 h.le
      have h5 : K ^ 2 / H ≤ 1 := (div_le_one hH0).2 hH2
      refine mul_le_mul_of_nonneg_right ?_ hKi.le
      have h3 : 0 ≤ M / L := by positivity
      have h4 : 0 ≤ K ^ 2 / H := by positivity
      nlinarith only [h5, h2, h3, h4]
    have e : M / H * Br₁ L M K = M / H * (L / K) + M / H * (2 * M ^ 2 / (L * K)) +
        M / H * (K / L) := by
      simp only [Br₁]
      ring
    rw [e]
    linarith
  · have t1 : M / H * (K / L) ≤ 4 * L⁻¹ := by
      have e : M / H * (K / L) = (M / K) * (K ^ 2 / H) * L⁻¹ := by
        field_simp
      rw [e]
      have h2 : M / K ≤ 4 := (div_le_iff₀ hK).2 h.le
      have h5 : K ^ 2 / H ≤ 1 := (div_le_one hH0).2 hH2
      refine mul_le_mul_of_nonneg_right ?_ hLi.le
      have h3 : 0 ≤ M / K := by positivity
      have h4 : 0 ≤ K ^ 2 / H := by positivity
      nlinarith only [h5, h2, h3, h4]
    have t2 : M / H * (2 * M ^ 2 / (L * K)) ≤ 16 * L⁻¹ := by
      have e : M / H * (2 * M ^ 2 / (L * K)) = (M ^ 2 / H) * (2 * (M / K)) * L⁻¹ := by
        field_simp
      rw [e]
      have h1 : M ^ 2 / H ≤ 2 := (div_le_iff₀ hH0).2 hM2
      have h2 : M / K ≤ 4 := (div_le_iff₀ hK).2 h.le
      refine mul_le_mul_of_nonneg_right ?_ hLi.le
      have h3 : 0 ≤ M / K := by positivity
      have h4 : 0 ≤ M ^ 2 / H := by positivity
      nlinarith only [h1, h2, h3, h4]
    have t3 : M / H * (L / K) ≤ 4 * L⁻¹ := by
      have e : M / H * (L / K) = (M / K) * (L ^ 2 / H) * L⁻¹ := by
        field_simp
      rw [e]
      have h2 : M / K ≤ 4 := (div_le_iff₀ hK).2 h.le
      have h5 : L ^ 2 / H ≤ 1 := (div_le_one hH0).2 hH1
      refine mul_le_mul_of_nonneg_right ?_ hLi.le
      have h3 : 0 ≤ M / K := by positivity
      have h4 : 0 ≤ L ^ 2 / H := by positivity
      nlinarith only [h5, h2, h3, h4]
    have e : M / H * Br₁ L M K = M / H * (L / K) + M / H * (2 * M ^ 2 / (L * K)) +
        M / H * (K / L) := by
      simp only [Br₁]
      ring
    rw [e]
    linarith

open Classical in
/-- The heat kernel of a large intermediate at weight one. -/
def hiK (l a b : Mode) : ℝ :=
  if 4 * absk l ≤ absk (l - a) ∧ 4 * absk (l - a - b) ≤ absk (l - a) then
    absk (l - a) ^ 2 / (absk l * absk (l - a - b)) else 0

lemma hiK_nonneg (l a b : Mode) : 0 ≤ hiK l a b := by
  have h1 := absk_nonneg l
  have h2 := absk_nonneg (l - a)
  have h3 := absk_nonneg (l - a - b)
  unfold hiK
  split_ifs <;> positivity

/-- **The block of `X₂` at weight one** (§8.4). -/
theorem norm_X2_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖X2b 1 r τ f g l a b‖ ≤ (2 ^ 15 / |r| * ((absk l)⁻¹ + (absk (l - a - b))⁻¹) +
      2 ^ 15 / |r| ^ 2 * hiK l a b) * (‖f a‖ * ‖g b‖) := by
  obtain ⟨hl0, -, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hfg : 0 ≤ ‖f a‖ * ‖g b‖ := by positivity
  have hLi := inv_pos.2 hL
  have hKi := inv_pos.2 hK
  by_cases hhi : 4 * absk l ≤ absk (l - a) ∧ 4 * absk (l - a - b) ≤ absk (l - a)
  · have e : hiK l a b = absk (l - a) ^ 2 / (absk l * absk (l - a - b)) := by
      simp only [hiK, hhi.1, hhi.2, and_self, ite_true]
    rw [X2b_split', e]
    refine (norm_add_le _ _).trans ((add_le_add (norm_Xph_one hr τ ha hb hj hhi.1 hhi.2 _ _)
      (norm_Xheat_one hr τ ha hb hj hhi.1 hhi.2 _ _)).trans ?_)
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ hfg
    have h1 : 2 ^ 13 / |r| * ((absk l)⁻¹ + (absk (l - a - b))⁻¹) ≤
        2 ^ 15 / |r| * ((absk l)⁻¹ + (absk (l - a - b))⁻¹) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact div_le_div_of_nonneg_right (by norm_num) hq.le
    linarith
  · have e : hiK l a b = 0 := by simp [hiK, hhi]
    rw [e, mul_zero, add_zero]
    have hH := heat4_pos (l := l) hj0 a b
    have hHL : absk l ^ 2 + absk (l - a - b) ^ 2 ≤ heat4 l (l - a - b) a b := by
      rw [heat4_eq]
      nlinarith only [sq_nonneg (absk a), sq_nonneg (absk b)]
    have hM2 : absk (l - a) ^ 2 ≤ 2 * heat4 l (l - a - b) a b := by
      rw [heat4_eq]
      have h1 := absk_sub_le l a
      have h2 := absk_nonneg (l - a)
      have h3 := absk_nonneg l
      have h4 := absk_nonneg a
      nlinarith only [h1, h2, h3, h4, sq_nonneg (absk l - absk a), sq_nonneg (absk b),
        sq_nonneg (absk (l - a - b))]
    have hM : absk (l - a) < 4 * absk l ∨ absk (l - a) < 4 * absk (l - a - b) := by
      rcases not_and_or.1 hhi with h | h
      · exact Or.inl (not_le.1 h)
      · exact Or.inr (not_le.1 h)
    have hA := ord_one_arith hL hK (absk_nonneg _) hM hHL hM2
    refine (norm_X2b_one_le hr τ f g ha hb hj).trans ?_
    have hI : 0 ≤ 1280 / |r| := by positivity
    calc _ = 1280 / |r| * (absk (l - a) / heat4 l (l - a - b) a b *
          Br₁ (absk l) (absk (l - a)) (absk (l - a - b))) * (‖f a‖ * ‖g b‖) := by ring
      _ ≤ 1280 / |r| * (24 * ((absk l)⁻¹ + (absk (l - a - b))⁻¹)) * (‖f a‖ * ‖g b‖) := by
          gcongr
      _ = 30720 / |r| * ((absk l)⁻¹ + (absk (l - a - b))⁻¹) * (‖f a‖ * ‖g b‖) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hfg
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact div_le_div_of_nonneg_right (by norm_num) hq.le

/-- **The block of `Z` at weight one.** -/
theorem norm_Zb_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖Zb 1 r τ f g l a b‖ ≤ 640 / |r| * (absk (a + b) / heat4 l (l - a - b) a b) *
      (absk l / absk (l - a - b) + absk (l - a - b) / absk l) * (‖f a‖ * ‖g b‖) := by
  obtain ⟨hl0, -, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hH := heat4_pos (l := l) hj0 a b
  have e1 : (a + b) + (l - a - b) = l := by abel
  have hab : (a + b) 2 = 0 := by simp [ha, hb]
  have h1 := norm_X1b_one_le hr τ e1 hab hj (slowV a b (f a) (g b))
  have h2 := norm_slowV_le a b (f a) (g b)
  have hP := absk_nonneg (a + b)
  have hA := norm_nonneg (f a)
  have hB := norm_nonneg (g b)
  have hR : 0 ≤ absk l / absk (l - a - b) + absk (l - a - b) / absk l := by
    have h3 := absk_nonneg l
    have h4 := absk_nonneg (l - a - b)
    positivity
  have h4 : ‖X1b 1 r τ (a + b) l (l - a - b) (slowV a b (f a) (g b))‖ ≤
      20 / |r| * (8 * absk (a + b) * ‖f a‖ * ‖g b‖) *
        (absk l / absk (l - a - b) + absk (l - a - b) / absk l) := h1.trans (by gcongr)
  refine (norm_outerInv_le hH r l _ _).trans
    ((mul_le_mul_of_nonneg_left h4 (by positivity)).trans (le_of_eq ?_))
  ring

/-- The heat ratio of `Z`. -/
lemma Z_ratio {L K P H : ℝ} (hL : 0 < L) (hK : 0 < K) (hP : P ≤ L + K)
    (hH : L ^ 2 + K ^ 2 ≤ H) : P / H * (L / K + K / L) ≤ 2 * (L⁻¹ + K⁻¹) := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hLi := inv_pos.2 hL
  have hKi := inv_pos.2 hK
  have h1 : L ^ 2 / H ≤ 1 := (div_le_one hH0).2 (by nlinarith only [hH, sq_nonneg K])
  have h2 : K ^ 2 / H ≤ 1 := (div_le_one hH0).2 (by nlinarith only [hH, sq_nonneg L])
  have e : (L + K) / H * (L / K + K / L) =
      L ^ 2 / H * K⁻¹ + K ^ 2 / H * K⁻¹ + L ^ 2 / H * L⁻¹ + K ^ 2 / H * L⁻¹ := by
    field_simp
    ring
  have h3 : P / H * (L / K + K / L) ≤ (L + K) / H * (L / K + K / L) := by gcongr
  refine h3.trans ?_
  rw [e]
  have t1 := mul_le_mul_of_nonneg_right h1 hKi.le
  have t2 := mul_le_mul_of_nonneg_right h2 hKi.le
  have t3 := mul_le_mul_of_nonneg_right h1 hLi.le
  have t4 := mul_le_mul_of_nonneg_right h2 hLi.le
  linarith

/-- **The block of `Z` at weight one**, first-power kernel. -/
theorem norm_Z_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖Zb 1 r τ f g l a b‖ ≤ 2 ^ 11 / |r| * ((absk l)⁻¹ + (absk (l - a - b))⁻¹) *
      (‖f a‖ * ‖g b‖) := by
  obtain ⟨hl0, -, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hfg : 0 ≤ ‖f a‖ * ‖g b‖ := by positivity
  have hHL : absk l ^ 2 + absk (l - a - b) ^ 2 ≤ heat4 l (l - a - b) a b := by
    rw [heat4_eq]
    nlinarith only [sq_nonneg (absk a), sq_nonneg (absk b)]
  have hab : a + b = l - (l - a - b) := by abel
  have hPle : absk (a + b) ≤ absk l + absk (l - a - b) := by
    rw [hab]
    exact absk_sub_le _ _
  have h1 := Z_ratio hL hK hPle hHL
  refine (norm_Zb_one hr τ f g ha hb hj).trans ?_
  have hI : 0 ≤ 640 / |r| := by positivity
  calc _ = 640 / |r| * (absk (a + b) / heat4 l (l - a - b) a b *
        (absk l / absk (l - a - b) + absk (l - a - b) / absk l)) * (‖f a‖ * ‖g b‖) := by ring
    _ ≤ 640 / |r| * (2 * ((absk l)⁻¹ + (absk (l - a - b))⁻¹)) * (‖f a‖ * ‖g b‖) := by gcongr
    _ = 1280 / |r| * ((absk l)⁻¹ + (absk (l - a - b))⁻¹) * (‖f a‖ * ‖g b‖) := by ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ hfg
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact div_le_div_of_nonneg_right (by norm_num) hq.le

/-- The first-weight kernel of the output half. -/
def E1k (x : I3) : ℝ :=
  1 + (absk x.2.1 + absk x.2.2) / absk x.1 + (absk x.2.1 + absk x.2.2) / absk (inJ₂ x) +
    absk x.2.1 * absk x.2.2 / (absk x.1 * absk (inJ₂ x))

lemma E1k_nonneg (x : I3) : 0 ≤ E1k x := by
  have h1 := absk_nonneg x.1
  have h2 := absk_nonneg (inJ₂ x)
  have h3 := absk_nonneg x.2.1
  have h4 := absk_nonneg x.2.2
  unfold E1k
  positivity

/-- The bracket of weight one in the kernel. -/
lemma Br₁_le_E {L M K A B : ℝ} (hL : 0 < L) (hK : 0 < K) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p3 : L ≤ K + A + B) (p4 : K ≤ L + A + B) (q1 : M ≤ L + A) (q2 : M ≤ K + B) :
    (L / K + K / L ≤ 2 * (1 + (A + B) / L + (A + B) / K + A * B / (L * K))) ∧
      Br₁ L M K ≤ 4 * (1 + (A + B) / L + (A + B) / K + A * B / (L * K)) := by
  have hLK : 0 < L * K := by positivity
  have e1 : L / K ≤ 1 + (A + B) / K := by
    rw [div_le_iff₀ hK]
    have : (1 + (A + B) / K) * K = K + (A + B) := by field_simp
    rw [this]
    linarith
  have e2 : K / L ≤ 1 + (A + B) / L := by
    rw [div_le_iff₀ hL]
    have : (1 + (A + B) / L) * L = L + (A + B) := by field_simp
    rw [this]
    linarith
  have e3 : 2 * M ^ 2 / (L * K) ≤ 2 * (1 + A / L + B / K + A * B / (L * K)) := by
    rw [div_le_iff₀ hLK]
    have h1 : M ^ 2 ≤ (L + A) * (K + B) := by
      rw [sq]
      exact mul_le_mul q1 q2 hM (by linarith)
    have : 2 * (1 + A / L + B / K + A * B / (L * K)) * (L * K) = 2 * ((L + A) * (K + B)) := by
      field_simp
      ring
    rw [this]
    linarith
  have a1 : A / L ≤ (A + B) / L := by gcongr; linarith
  have a2 : B / K ≤ (A + B) / K := by gcongr; linarith
  have n1 : 0 ≤ (A + B) / L := by positivity
  have n2 : 0 ≤ (A + B) / K := by positivity
  have n3 : 0 ≤ A * B / (L * K) := by positivity
  constructor
  · linarith
  · simp only [Br₁]
    linarith

/-- **The output half at weight one**, on one label. -/
theorem norm_Y_half_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    absk l * ‖X2b 1 r τ f g l a b‖ ≤ 2 ^ 14 / |r| * E1k (l, a, b) * (‖f a‖ * ‖g b‖) ∧
      absk l * ‖Zb 1 r τ f g l a b‖ ≤ 2 ^ 14 / |r| * E1k (l, a, b) * (‖f a‖ * ‖g b‖) := by
  obtain ⟨hl0, -, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hfg : 0 ≤ ‖f a‖ * ‖g b‖ := by positivity
  have hA := absk_nonneg a
  have hB := absk_nonneg b
  have hH := heat4_pos (l := l) hj0 a b
  obtain ⟨q1, q2, p3, p4⟩ := two_leaf_paths l a b
  have hE : E1k (l, a, b) = 1 + (absk a + absk b) / absk l + (absk a + absk b) / absk (l - a - b) +
      absk a * absk b / (absk l * absk (l - a - b)) := rfl
  obtain ⟨hB1, hB2⟩ := Br₁_le_E hL hK (absk_nonneg (l - a)) hA hB (by linarith) (by linarith)
    q1 q2
  rw [← hE] at hB1 hB2
  have hE0 := E1k_nonneg (l, a, b)
  constructor
  · have h1 := norm_X2b_one_le hr τ f g ha hb hj
    have h2 := half_ratio_le l a b
    have h3 : 0 ≤ absk l * (absk (l - a) / heat4 l (l - a - b) a b) := by
      have := absk_nonneg (l - a)
      positivity
    have hBr0 : 0 ≤ Br₁ (absk l) (absk (l - a)) (absk (l - a - b)) := by
      have := absk_nonneg (l - a)
      simp only [Br₁]
      positivity
    calc _ ≤ absk l * (1280 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) * (‖f a‖ * ‖g b‖) *
          Br₁ (absk l) (absk (l - a)) (absk (l - a - b))) := mul_le_mul_of_nonneg_left h1 hL.le
      _ = 1280 / |r| * ((absk l * (absk (l - a) / heat4 l (l - a - b) a b)) *
          Br₁ (absk l) (absk (l - a)) (absk (l - a - b))) * (‖f a‖ * ‖g b‖) := by ring
      _ ≤ 1280 / |r| * (2 * (4 * E1k (l, a, b))) * (‖f a‖ * ‖g b‖) := by
          gcongr
      _ = 10240 / |r| * E1k (l, a, b) * (‖f a‖ * ‖g b‖) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hfg
          refine mul_le_mul_of_nonneg_right ?_ hE0
          exact div_le_div_of_nonneg_right (by norm_num) hq.le
  · have h1 := norm_Zb_one hr τ f g ha hb hj
    have hLP : absk l * absk (a + b) ≤ heat4 l (l - a - b) a b := by
      rw [heat4_eq]
      have h2 := absk_add_le a b
      have h3 := absk_nonneg (a + b)
      nlinarith only [h2, h3, hA, hB, sq_nonneg (absk l - absk (a + b)), sq_nonneg (absk a - absk b),
        sq_nonneg (absk (l - a - b)), hL]
    have h3 : absk l * (absk (a + b) / heat4 l (l - a - b) a b) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hH]
      exact hLP
    have h4 : 0 ≤ absk l * (absk (a + b) / heat4 l (l - a - b) a b) := by
      have := absk_nonneg (a + b)
      positivity
    have hR0 : 0 ≤ absk l / absk (l - a - b) + absk (l - a - b) / absk l := by positivity
    calc _ ≤ absk l * (640 / |r| * (absk (a + b) / heat4 l (l - a - b) a b) *
          (absk l / absk (l - a - b) + absk (l - a - b) / absk l) * (‖f a‖ * ‖g b‖)) :=
          mul_le_mul_of_nonneg_left h1 hL.le
      _ = 640 / |r| * ((absk l * (absk (a + b) / heat4 l (l - a - b) a b)) *
          (absk l / absk (l - a - b) + absk (l - a - b) / absk l)) * (‖f a‖ * ‖g b‖) := by ring
      _ ≤ 640 / |r| * (1 * (2 * E1k (l, a, b))) * (‖f a‖ * ‖g b‖) := by
          gcongr
      _ = 1280 / |r| * E1k (l, a, b) * (‖f a‖ * ‖g b‖) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hfg
          refine mul_le_mul_of_nonneg_right ?_ hE0
          exact div_le_div_of_nonneg_right (by norm_num) hq.le

end OVNS.Quant.Metric

end
