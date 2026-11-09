import OddViscousNS.Quant.Joint.Metric.Path3Id

/-!
# The heat part and the phase part of `X₂` at a large intermediate (step J5, node N8)

Body 33: "Split this numerator exactly into its real heat sum and its imaginary phase sum."  At
`M ≥ 4 max(L, K)` the two rootings carry `1/d₁ + 1/d₂ = [−(Σ₁ + Σ₂) + i r δ]/(d₁ d₂)`.  `tH` is the
block of the heat sum, on the common product.  The rest `tR − tH` is the phase sum and the two
noncommon products: `Q₃` is defined on it, with the literal `tR` on the ordinary sector.

* `norm_Xheat_le`: `‖H⁻¹ tH‖ ≤ 2¹⁵ (M²/L²)(M²/K²) f g / q²`;
* `norm_Xph_le`: `‖H⁻¹ (tR − tH)‖ ≤ 2¹⁵ (M²/L²)(M²/K²) f g (L + K)/(q M²)`.

The sum of the two is `norm_X2b_signed_le`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-- The scalar of the heat sum on the channel `(c, e, d)`. -/
def hsS (r : ℝ) (l a b : Mode) (c d e : Sgn) : ℂ :=
  ((-(triHeat a (l - a) + triHeat b (l - a - b)) : ℝ) : ℂ) *
    (chR r (triHeat a (l - a)) c e l (l - a) *
      chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b))

/-- The block of the heat sum. -/
def tH (s : ℕ) (r τ : ℝ) (l a b : Mode) (v w : V3) : Blk :=
  ∑ c : Sgn, ∑ d : Sgn, ∑ e : Sgn, hsS r l a b c d e •
    (helL c l ∘L Lad s τ a l (l - a) v ∘L helL e (l - a) ∘L
      Lb s τ b (l - a) (l - a - b) w ∘L helL d (l - a - b))

variable {s : ℕ} {r τ : ℝ} {l a b : Mode}

private lemma hel_zero' (c : Sgn) (k : Mode) : hel c k (0 : V3) = 0 := by
  simpa using hel_smul c k 0 (0 : V3)

/-- A channel of the heat block. -/
lemma chan_tH (s : ℕ) (r τ : ℝ) (l a b : Mode) (v w y : V3) (c d : Sgn) :
    hel c l (tH s r τ l a b v w (hel d (l - a - b) y)) = ∑ e : Sgn, hsS r l a b c d e •
      hel c l (Lad s τ a l (l - a) v
        (hel e (l - a) (Lb s τ b (l - a) (l - a - b) w (hel d (l - a - b) y)))) := by
  simp only [tH, sum_apply, smul_apply, ContinuousLinearMap.comp_apply, helL_apply]
  rw [hel_sum_distrib, Fintype.sum_eq_single c (fun c' hc' => ?_)]
  · rw [hel_sum_distrib, Fintype.sum_eq_single d (fun d' hd' => ?_)]
    · rw [hel_sum_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [hel_smul, hel_idem, hel_idem]
    · rw [hel_sum_distrib]
      refine Finset.sum_eq_zero fun e _ => ?_
      have h0 : hel d' (l - a - b) (hel d (l - a - b) y) = 0 := hel_orth hd' _ _
      rw [h0, map_zero, hel_zero', map_zero, hel_zero', smul_zero, hel_zero']
  · rw [hel_sum_distrib]
    refine Finset.sum_eq_zero fun d' _ => ?_
    rw [hel_sum_distrib]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [hel_smul, hel_orth (Ne.symm hc'), smul_zero]

/-- The two-root channel, with the heat sum removed. -/
lemma chan_tP (s : ℕ) (r τ : ℝ) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) (h1 : ∀ e c, lam e (l - a) ≠ lam c l)
    (h2 : ∀ d e, lam d (l - a - b) ≠ lam e (l - a)) (v w y : V3) (c d : Sgn) :
    hel c l ((tR s r τ l a b v w - tH s r τ l a b v w) (hel d (l - a - b) y)) = ∑ e : Sgn,
      ((chR r (triHeat a (l - a)) c e l (l - a) +
          chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b) - hsS r l a b c d e) •
          hel c l (Lad s τ a l (l - a) v
            (hel e (l - a) (Lb s τ b (l - a) (l - a - b) w (hel d (l - a - b) y)))) +
        chR r (triHeat a (l - a)) c e l (l - a) •
          hel c l (Lb s τ a l (l - a) v
            (hel e (l - a) (Lb s τ b (l - a) (l - a - b) w (hel d (l - a - b) y)))) +
        chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b) •
          hel c l (Lad s τ a l (l - a) v
            (hel e (l - a) (Lad s τ b (l - a) (l - a - b) w (hel d (l - a - b) y))))) := by
  have e0 := twoRoot_split s r τ (fun _ => v) (fun _ => w) ha hb hj h1 h2 c d y
  have e2 : hel c l (tR s r τ l a b v w (hel d (l - a - b) y)) = _ := e0
  rw [sub_apply, hel_sub, chan_tH, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sub_smul]
  abel

/-- The sizes at a large intermediate. -/
lemma high_data {r : ℝ} (hr : r ≠ 0) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) :
    (∀ e c, lam e (l - a) ≠ lam c l) ∧ (∀ d e, lam d (l - a - b) ≠ lam e (l - a)) ∧
    (∀ c e, 3 / 4 * (|r| * (|((l - a) 2 : ℝ)| * absk (l - a))) ≤
      |r * (lam e (l - a) - lam c l)|) ∧
    (∀ d e, 3 / 4 * (|r| * (|((l - a) 2 : ℝ)| * absk (l - a))) ≤
      |r * (lam d (l - a - b) - lam e (l - a))|) ∧
    (∀ c d e, |r * (lam e (l - a) - lam c l) + r * (lam d (l - a - b) - lam e (l - a))| ≤
      |r| * (|((l - a) 2 : ℝ)| * (absk l + absk (l - a - b)))) ∧
    (1 : ℝ) ≤ |((l - a) 2 : ℝ)| := by
  obtain ⟨-, hm0, -⟩ := fast_labels ha hb hj
  have hl2 : l 2 = (l - a) 2 := by simp [ha]
  have hj2 : (l - a - b) 2 = (l - a) 2 := by simp [hb]
  have hm2 : (l - a) 2 ≠ 0 := by rwa [← hj2]
  have hq : 0 < |r| := abs_pos.2 hr
  have hM1 := one_le_absk hm0
  have hN : (1 : ℝ) ≤ |((l - a) 2 : ℝ)| := by
    have : (1 : ℤ) ≤ |(l - a) 2| := Int.one_le_abs hm2
    exact_mod_cast this
  have hg1 : ∀ c e, 0 < |lam e (l - a) - lam c l| := fun c e =>
    lt_of_lt_of_le (by positivity) (lam_gap hl2 hL c e)
  have hg2 : ∀ d e, 0 < |lam e (l - a) - lam d (l - a - b)| := fun d e =>
    lt_of_lt_of_le (by positivity) (lam_gap hj2 hJ d e)
  refine ⟨fun e c h => ?_, fun d e h => ?_, fun c e => ?_, fun d e => ?_, fun c d e => ?_, hN⟩
  · have := hg1 c e
    rw [h, sub_self, abs_zero] at this
    exact lt_irrefl _ this
  · have := hg2 d e
    rw [h, sub_self, abs_zero] at this
    exact lt_irrefl _ this
  · have := mul_le_mul_of_nonneg_left (lam_gap hl2 hL c e) hq.le
    rw [abs_mul]
    linarith
  · have := mul_le_mul_of_nonneg_left (lam_gap hj2 hJ d e) hq.le
    rw [abs_mul, abs_sub_comm (lam d (l - a - b))]
    linarith
  · have h := lam_ext (hl2.trans hj2.symm) c d
    rw [hj2] at h
    have e' : r * (lam e (l - a) - lam c l) + r * (lam d (l - a - b) - lam e (l - a)) =
        r * (lam d (l - a - b) - lam c l) := by
      ring
    rw [e', abs_mul]
    exact mul_le_mul_of_nonneg_left h hq.le

/-- The resolvent against its phase. -/
lemma resolv_gap_le {H z q N M : ℝ} (hq : 0 < q) (hN : 1 ≤ N) (hM : 0 < M)
    (hz : 3 / 4 * (q * (N * M)) ≤ |z|) : ‖resolv (-1) H z‖ ≤ 4 / 3 / (q * (N * M)) := by
  have hN0 : 0 < N := by linarith
  have hp : 0 < q * (N * M) := by positivity
  have hz0 : z ≠ 0 := fun h => by
    rw [h, abs_zero] at hz
    linarith
  refine (norm_resolv_le_abs H hz0).trans ?_
  rw [div_le_div_iff₀ (abs_pos.2 hz0) hp]
  linarith

/-- The heat scalar. -/
lemma heat_scalar_le {H₁ H₂ z₁ z₂ q N M : ℝ} (hq : 0 < q) (hN : 1 ≤ N) (hM : 0 < M)
    (h1 : 0 < H₁) (h2 : 0 < H₂) (hH : H₁ + H₂ ≤ 6 * M ^ 2) (hz₁ : 3 / 4 * (q * (N * M)) ≤ |z₁|)
    (hz₂ : 3 / 4 * (q * (N * M)) ≤ |z₂|) :
    ‖((-(H₁ + H₂) : ℝ) : ℂ) * (resolv (-1) H₁ z₁ * resolv (-1) H₂ z₂)‖ ≤ 32 / 3 / q ^ 2 := by
  have r1 := resolv_gap_le (H := H₁) hq hN hM hz₁
  have r2 := resolv_gap_le (H := H₂) hq hN hM hz₂
  have hN0 : 0 < N := by linarith
  have hp : 0 < q * (N * M) := by positivity
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos (by positivity : 0 < H₁ + H₂)]
  calc _ ≤ 6 * M ^ 2 * (4 / 3 / (q * (N * M)) * (4 / 3 / (q * (N * M)))) := by
        refine mul_le_mul hH (mul_le_mul r1 r2 (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = 32 / 3 / q ^ 2 * (1 / N ^ 2) := by
        field_simp
        norm_num
    _ ≤ _ := by
        have : 1 / N ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith only [hN]
        exact mul_le_of_le_one_right (by positivity) this

/-- The phase scalar. -/
lemma phase_scalar_le {H₁ H₂ z₁ z₂ q N M S : ℝ} (hq : 0 < q) (hN : 1 ≤ N) (hM : 0 < M)
    (hS : 0 ≤ S) (h1 : 0 < H₁) (h2 : 0 < H₂) (hz₁ : 3 / 4 * (q * (N * M)) ≤ |z₁|)
    (hz₂ : 3 / 4 * (q * (N * M)) ≤ |z₂|) (hs : |z₁ + z₂| ≤ q * (N * S)) :
    ‖resolv (-1) H₁ z₁ + resolv (-1) H₂ z₂ -
      ((-(H₁ + H₂) : ℝ) : ℂ) * (resolv (-1) H₁ z₁ * resolv (-1) H₂ z₂)‖ ≤
      16 / 9 * S / (q * M ^ 2) := by
  have r1 := resolv_gap_le (H := H₁) hq hN hM hz₁
  have r2 := resolv_gap_le (H := H₂) hq hN hM hz₂
  have hN0 : 0 < N := by linarith
  have hp : 0 < q * (N * M) := by positivity
  rw [resolv_add h1.ne' h2.ne']
  have e : (((-(H₁ + H₂) : ℝ) : ℂ) + ((z₁ + z₂ : ℝ) : ℂ) * Complex.I) *
      (resolv (-1) H₁ z₁ * resolv (-1) H₂ z₂) -
      ((-(H₁ + H₂) : ℝ) : ℂ) * (resolv (-1) H₁ z₁ * resolv (-1) H₂ z₂) =
      ((z₁ + z₂ : ℝ) : ℂ) * Complex.I * (resolv (-1) H₁ z₁ * resolv (-1) H₂ z₂) := by
    ring
  rw [e, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  calc _ ≤ q * (N * S) * (4 / 3 / (q * (N * M)) * (4 / 3 / (q * (N * M)))) := by
        refine mul_le_mul hs (mul_le_mul r1 r2 (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = 16 / 9 * S / (q * M ^ 2) * (1 / N) := by
        field_simp
        ring
    _ ≤ _ := by
        have : 1 / N ≤ 1 := by
          rw [div_le_one hN0]
          exact hN
        exact mul_le_of_le_one_right (by positivity) this

private lemma term_le' {R : ℂ} {ρ nA nB : ℝ} {T T' : V3 →L[ℂ] V3} (c e d : Sgn) (l m j : Mode)
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

/-- The two-sided sizes of the edges at a large intermediate. -/
lemma edge_sizes {s : ℕ} (τ : ℝ) {l a b : Mode} (v w : V3) :
    ‖Lad s τ a l (l - a) v‖ ≤ 16 * wt s (l - a) l * absk (l - a) * ‖v‖ ∧
      ‖Lb s τ b (l - a) (l - a - b) w‖ ≤ 16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖ ∧
      ‖Lb s τ a l (l - a) v‖ ≤ 16 * wt s l (l - a) * absk l * ‖v‖ ∧
      ‖Lad s τ b (l - a) (l - a - b) w‖ ≤
        16 * wt s (l - a - b) (l - a) * absk (l - a - b) * ‖w‖ := by
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  exact ⟨norm_Lad_le s τ e1 v, norm_Lb_le s τ e2 w, norm_Lb_le s τ e1 v, norm_Lad_le s τ e2 w⟩

/-- A channel of the heat block, at a large intermediate. -/
lemma high_chan_heat {s : ℕ} {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) (v w : V3) (c d : Sgn) (y : V3) :
    ‖hel c l (tH s r τ l a b v w (hel d (l - a - b) y))‖ ≤
      2 * (32 / 3 / |r| ^ 2 * ((16 * wt s (l - a) l * absk (l - a) * ‖v‖) *
        (16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖))) * ‖y‖ := by
  obtain ⟨-, hm0, hj0⟩ := fast_labels ha hb hj
  obtain ⟨-, -, hz₁, hz₂, -, hN⟩ := high_data hr ha hb hj hL hJ
  obtain ⟨hH1, hH2, hHs, -⟩ := high_heats hj0 hL hJ
  have hq : 0 < |r| := abs_pos.2 hr
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  obtain ⟨hA, hB, -, -⟩ := edge_sizes (s := s) τ (l := l) (a := a) (b := b) v w
  rw [chan_tH]
  refine (norm_sum_le_of_le (n := fun _ => 32 / 3 / |r| ^ 2 * ((16 * wt s (l - a) l * absk (l - a) *
    ‖v‖) * (16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖)) * ‖y‖) _ fun e _ => ?_).trans
    (le_of_eq ?_)
  · refine term_le' c e d l (l - a) (l - a - b) y ?_ hA hB
    exact heat_scalar_le hq hN hM hH1 hH2 hHs (hz₁ c e) (hz₂ d e)
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    ring

/-- A channel of the phase part, at a large intermediate. -/
lemma high_chan_ph {s : ℕ} {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) (v w : V3) (c d : Sgn) (y : V3) :
    ‖hel c l ((tR s r τ l a b v w - tH s r τ l a b v w) (hel d (l - a - b) y))‖ ≤
      2 * (16 / 9 * (absk l + absk (l - a - b)) / (|r| * absk (l - a) ^ 2) *
          ((16 * wt s (l - a) l * absk (l - a) * ‖v‖) *
            (16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖)) +
        4 / 3 / (|r| * absk (l - a)) * ((16 * wt s l (l - a) * absk l * ‖v‖) *
            (16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖)) +
        4 / 3 / (|r| * absk (l - a)) * ((16 * wt s (l - a) l * absk (l - a) * ‖v‖) *
            (16 * wt s (l - a - b) (l - a) * absk (l - a - b) * ‖w‖))) * ‖y‖ := by
  obtain ⟨-, hm0, hj0⟩ := fast_labels ha hb hj
  obtain ⟨hne₁, hne₂, hz₁, hz₂, hzs, hN⟩ := high_data hr ha hb hj hL hJ
  obtain ⟨hH1, hH2, -, -⟩ := high_heats hj0 hL hJ
  have hq : 0 < |r| := abs_pos.2 hr
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hS : 0 ≤ absk l + absk (l - a - b) := add_nonneg (absk_nonneg _) (absk_nonneg _)
  obtain ⟨hA, hB, hC, hD⟩ := edge_sizes (s := s) τ (l := l) (a := a) (b := b) v w
  rw [chan_tP s r τ ha hb hj hne₁ hne₂]
  set nA := 16 * wt s (l - a) l * absk (l - a) * ‖v‖
  set nB := 16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖w‖
  set nC := 16 * wt s l (l - a) * absk l * ‖v‖
  set nD := 16 * wt s (l - a - b) (l - a) * absk (l - a - b) * ‖w‖
  set ρ := 16 / 9 * (absk l + absk (l - a - b)) / (|r| * absk (l - a) ^ 2)
  set ρ₁ := 4 / 3 / (|r| * absk (l - a))
  refine (norm_sum_le_of_le (n := fun _ => (ρ * (nA * nB) + ρ₁ * (nC * nB) + ρ₁ * (nA * nD)) * ‖y‖)
    _ fun e _ => ?_).trans (le_of_eq ?_)
  · refine (norm_add_le _ _).trans ?_
    have hc1 : ‖chR r (triHeat a (l - a)) c e l (l - a)‖ ≤ ρ₁ :=
      rho₁_le hq hN hM (hz₁ c e)
    have hc2 : ‖chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)‖ ≤ ρ₁ :=
      rho₁_le hq hN hM (hz₂ d e)
    have t1 := term_le' c e d l (l - a) (l - a - b) y (ρ := ρ) (phase_scalar_le hq hN hM hS hH1 hH2
      (hz₁ c e) (hz₂ d e) (hzs c d e)) hA hB
    have t2 := term_le' c e d l (l - a) (l - a - b) y hc1 hC hB
    have t3 := term_le' c e d l (l - a) (l - a - b) y hc2 hA hD
    calc _ ≤ _ := add_le_add (norm_add_le _ _) t3
      _ ≤ ρ * (nA * nB) * ‖y‖ + ρ₁ * (nC * nB) * ‖y‖ + ρ₁ * (nA * nD) * ‖y‖ :=
          add_le_add (add_le_add t1 t2) le_rfl
      _ = _ := by ring
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    ring

/-- The arithmetic of the heat block. -/
lemma heat_arith {q M W Y H nAB : ℝ} (hq : 0 < q) (hM : 0 < M) (hW : 0 ≤ W) (hY : 0 ≤ Y)
    (hH : 9 / 8 * M ^ 2 ≤ H) (hn : 0 ≤ nAB) (h1 : nAB ≤ 256 * W * M ^ 2 * Y) :
    4 / H * (2 * (32 / 3 / q ^ 2 * nAB)) ≤ 2 ^ 15 * W * Y * (1 / q ^ 2) := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hH' : 4 / H ≤ 32 / 9 / M ^ 2 := by
    rw [div_le_div_iff₀ hH0 (by positivity)]
    linarith
  calc 4 / H * (2 * (32 / 3 / q ^ 2 * nAB))
      ≤ 32 / 9 / M ^ 2 * (2 * (32 / 3 / q ^ 2 * (256 * W * M ^ 2 * Y))) := by
        refine mul_le_mul hH' ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity))
          (by norm_num)
    _ = (32 / 9 * (2 * (32 / 3 * 256))) * (W * Y * (1 / q ^ 2)) := by
        field_simp
    _ ≤ _ := by
        have : 0 ≤ W * Y * (1 / q ^ 2) := by positivity
        nlinarith only [this]

/-- The arithmetic of the phase block. -/
lemma ph_arith {q M L J W Y H nAB nCB nAD : ℝ} (hq : 0 < q) (hM : 0 < M) (hL : 0 ≤ L) (hJ : 0 ≤ J)
    (hW : 0 ≤ W) (hY : 0 ≤ Y) (hH : 9 / 8 * M ^ 2 ≤ H) (hn1 : 0 ≤ nAB) (hn2 : 0 ≤ nCB)
    (hn3 : 0 ≤ nAD) (h1 : nAB ≤ 256 * W * M ^ 2 * Y) (h2 : nCB ≤ 256 * W * (L * M) * Y)
    (h3 : nAD ≤ 256 * W * (M * J) * Y) :
    4 / H * (2 * (16 / 9 * (L + J) / (q * M ^ 2) * nAB + 4 / 3 / (q * M) * nCB +
      4 / 3 / (q * M) * nAD)) ≤ 2 ^ 15 * W * Y * ((L + J) / (q * M ^ 2)) := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hH' : 4 / H ≤ 32 / 9 / M ^ 2 := by
    rw [div_le_div_iff₀ hH0 (by positivity)]
    linarith
  have hsum : 16 / 9 * (L + J) / (q * M ^ 2) * nAB + 4 / 3 / (q * M) * nCB + 4 / 3 / (q * M) * nAD ≤
      16 / 9 * (L + J) / (q * M ^ 2) * (256 * W * M ^ 2 * Y) +
        4 / 3 / (q * M) * (256 * W * (L * M) * Y) + 4 / 3 / (q * M) * (256 * W * (M * J) * Y) := by
    gcongr
  have e : 16 / 9 * (L + J) / (q * M ^ 2) * (256 * W * M ^ 2 * Y) +
      4 / 3 / (q * M) * (256 * W * (L * M) * Y) + 4 / 3 / (q * M) * (256 * W * (M * J) * Y) =
      256 * (28 / 9) * (W * Y * ((L + J) / q)) := by
    field_simp
    ring
  rw [e] at hsum
  have hT : 0 ≤ W * Y * ((L + J) / (q * M ^ 2)) := by positivity
  have hn : 0 ≤ 16 / 9 * (L + J) / (q * M ^ 2) * nAB + 4 / 3 / (q * M) * nCB +
      4 / 3 / (q * M) * nAD := by positivity
  calc _ ≤ 32 / 9 / M ^ 2 * (2 * (256 * (28 / 9) * (W * Y * ((L + J) / q)))) := by
        refine mul_le_mul hH' ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (32 / 9 * (2 * (256 * (28 / 9)))) * (W * Y * ((L + J) / (q * M ^ 2))) := by
        field_simp
    _ ≤ _ := by
        nlinarith only [hT]

/-- The norms of the edges against the weight, at a large intermediate. -/
private lemma high_weights {s : ℕ} (hs : s ≤ 2) {l a b : Mode} (hl0 : l ≠ 0) (hj0 : l - a - b ≠ 0)
    (hL : 4 * absk l ≤ absk (l - a)) (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (16 * wt s (l - a) l * absk (l - a) * x) *
        (16 * wt s (l - a) (l - a - b) * absk (l - a) * y) ≤
      256 * ((absk (l - a) / absk l) ^ 2 * (absk (l - a) / absk (l - a - b)) ^ 2) *
        absk (l - a) ^ 2 * (x * y) ∧
    (16 * wt s l (l - a) * absk l * x) * (16 * wt s (l - a) (l - a - b) * absk (l - a) * y) ≤
      256 * ((absk (l - a) / absk l) ^ 2 * (absk (l - a) / absk (l - a - b)) ^ 2) *
        (absk l * absk (l - a)) * (x * y) ∧
    (16 * wt s (l - a) l * absk (l - a) * x) *
        (16 * wt s (l - a - b) (l - a) * absk (l - a - b) * y) ≤
      256 * ((absk (l - a) / absk l) ^ 2 * (absk (l - a) / absk (l - a - b)) ^ 2) *
        (absk (l - a) * absk (l - a - b)) * (x * y) := by
  have hL1 := one_le_absk hl0
  have hJ1 := one_le_absk hj0
  obtain ⟨w1, w2, w3⟩ := wt_prod_le hs (lt_of_lt_of_le one_pos hL1) (lt_of_lt_of_le one_pos hJ1)
    (by linarith : absk l ≤ absk (l - a)) (by linarith : absk (l - a - b) ≤ absk (l - a))
  have h0 := wt_nonneg s (l - a) l
  have h1 := wt_nonneg s (l - a) (l - a - b)
  have h2 := wt_nonneg s l (l - a)
  have h3 := wt_nonneg s (l - a - b) (l - a)
  have n1 := absk_nonneg l
  have n2 := absk_nonneg (l - a)
  have n3 := absk_nonneg (l - a - b)
  refine ⟨?_, ?_, ?_⟩
  · calc _ = 256 * (wt s (l - a) l * wt s (l - a) (l - a - b)) * absk (l - a) ^ 2 * (x * y) := by
          ring
      _ ≤ _ := by gcongr
  · calc _ = 256 * (wt s l (l - a) * wt s (l - a) (l - a - b)) * (absk l * absk (l - a)) *
          (x * y) := by ring
      _ ≤ _ := by gcongr
  · calc _ = 256 * (wt s (l - a) l * wt s (l - a - b) (l - a)) *
          (absk (l - a) * absk (l - a - b)) * (x * y) := by ring
      _ ≤ _ := by gcongr

/-- **The heat block** at a large intermediate. -/
theorem norm_Xheat_le {s : ℕ} (hs : s ≤ 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode}
    (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) (v w : V3) :
    ‖outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (tH s r τ l a b v w)‖ ≤
      2 ^ 15 * ((absk (l - a) / absk l) ^ 2 * (absk (l - a) / absk (l - a - b)) ^ 2) *
        (‖v‖ * ‖w‖) * (1 / |r| ^ 2) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  obtain ⟨-, -, -, hH4⟩ := high_heats hj0 hL hJ
  have hH0 : 0 < heat4 l (l - a - b) a b := heat4_pos hj0 a b
  have h0 := wt_nonneg s (l - a) l
  have h1 := wt_nonneg s (l - a) (l - a - b)
  have hvw := norm_nonneg v
  have hww := norm_nonneg w
  obtain ⟨w1, -, -⟩ := high_weights hs hl0 hj0 hL hJ hvw hww
  refine (norm_outerInv_of_chan hH0 (by positivity) r l (l - a - b) _
    fun c e y => high_chan_heat hr τ ha hb hj hL hJ v w c e y).trans ?_
  exact heat_arith hq hM (by positivity) (by positivity) hH4 (by positivity) w1

/-- **The phase block** at a large intermediate. -/
theorem norm_Xph_le {s : ℕ} (hs : s ≤ 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {l a b : Mode}
    (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) (v w : V3) :
    ‖outerInv r (heat4 l (l - a - b) a b) l (l - a - b)
      (tR s r τ l a b v w - tH s r τ l a b v w)‖ ≤
      2 ^ 15 * ((absk (l - a) / absk l) ^ 2 * (absk (l - a) / absk (l - a - b)) ^ 2) *
        (‖v‖ * ‖w‖) * ((absk l + absk (l - a - b)) / (|r| * absk (l - a) ^ 2)) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hM : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  obtain ⟨-, -, -, hH4⟩ := high_heats hj0 hL hJ
  have hH0 : 0 < heat4 l (l - a - b) a b := heat4_pos hj0 a b
  have h0 := wt_nonneg s (l - a) l
  have h1 := wt_nonneg s (l - a) (l - a - b)
  have h2 := wt_nonneg s l (l - a)
  have h3 := wt_nonneg s (l - a - b) (l - a)
  have hvw := norm_nonneg v
  have hww := norm_nonneg w
  have hL0 := absk_nonneg l
  have hJ0 := absk_nonneg (l - a - b)
  obtain ⟨w1, w2, w3⟩ := high_weights hs hl0 hj0 hL hJ hvw hww
  refine (norm_outerInv_of_chan hH0 (by positivity) r l (l - a - b) _
    fun c e y => high_chan_ph hr τ ha hb hj hL hJ v w c e y).trans ?_
  exact ph_arith hq hM hL0 hJ0 (by positivity) (by positivity) hH4 (by positivity) (by positivity)
    (by positivity) w1 w2 w3

end OVNS.Quant.Metric

end
