import OddViscousNS.Quant.Joint.Quartic.Gap

/-!
# The fourth correction: one label (step J5, node N11)

Pointwise on the labels, with `P = ‖t‖‖w‖‖u‖‖v‖`, `k = p + q`, `K = mxL`:
* `coreQ_two_le`, `coreQ_one_le`: the coefficient at weights two and one: the cyclic sum with
  `cyc3_le`, the proper kernel with `near_ker`, the edge with `norm_edgeQ`;
* `termQ_two_le`: `‖Q₄‖ ≤ 2¹⁴ q⁻¹ kT (|s|²‖t‖) ‖w‖ (|q|²‖u‖) (|k|²‖v‖)`: Body 34, "the added divisor is
  bounded in modulus by `C/(q|s|)`.  On the high complement the derivative of the mixed vertex is
  bounded by `C|h| ≤ C'|s|` … Its `H²` weight at `h` is at most `C|s|²`";
* `srcQ_two_le`: the same with `|s|³`, no `q⁻¹`, the source;
* `termQ_one_static`: `√q ‖Q₄,₁‖ ≤ 2¹² kT (|s|^{3/2}‖t‖) ‖w‖ (|q|‖u‖) (|k|‖v‖)`: Body 35;
* `termQ_one_eps`: `q^{1−ε} ‖Q₄,₁‖ ≤ 2¹² |s|^{−ε} K |p||q||k| kT P`: Body 35, before the placements.
-/

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {r : ℝ} {x : L4} {d a b c : Sgn} {t w u v : V3} {τ : ℝ}

/-- The size of the source edge. -/
lemma norm_edgeQ (x : L4) (d : Sgn) (t w : V3) :
    ‖edgeQ x d t w‖ ≤ hiMu x.2.2 (inL x) * (8 * absk x.1 * ‖t‖) * ‖w‖ := by
  have h1 := norm_blk_hiM 0 (p_eq x) t
  have h2 := (blk (hiM 0) x.2.2 x.1 (inL x) t).le_opNorm (hel d (inL x) w)
  exact h2.trans (mul_le_mul h1 (norm_hel_le _ _ _) (norm_nonneg _)
    (mul_nonneg (hiMu_nonneg _ _) (mul_nonneg (mul_nonneg (by norm_num) (absk_nonneg _))
      (norm_nonneg _))))

lemma sum_zero_outE (x : L4) : x.1 + x.2.1 + outE x = 0 := by
  simp only [outE]
  abel

/-- The four amplitudes. -/
def amp (t w u v : V3) : ℝ := ‖t‖ * ‖w‖ * ‖u‖ * ‖v‖

lemma amp_nonneg (t w u v : V3) : 0 ≤ amp t w u v := by
  unfold amp
  positivity

/-- **The coefficient at weight two.** -/
theorem coreQ_two_le (hx : Act x) (r : ℝ) (d a b c : Sgn) (t w u v : V3) :
    ‖coreQ 2 r x d a b c t w u v‖ ≤ 416 * hiMu x.2.2 (inL x) *
      (absk x.1 ^ 3 * absk x.2.1 ^ 2 * absk (x.1 + x.2.1) ^ 2) * kT |r| (x.1, x.2.1) *
        amp t w u v := by
  have hμ := hiMu_nonneg x.2.2 (inL x)
  have hk := kT_nonneg |r| (x.1, x.2.1)
  have hA := amp_nonneg t w u v
  by_cases hN : NearT a b c x.1 x.2.1
  · obtain ⟨mn, hmn, hw2, -, hker⟩ := near_ker r hx.p hx.q hx.e
    have hK := hker 2 a b c hN
    simp only [coreQ, hN, ite_true]
    obtain ⟨m1, m2, m3⟩ := le_mxL x.1 x.2.1
    have hc := cyc3_le (j := 2) (ε := -1) (Or.inr rfl) (Or.inr rfl) (r * Phi a b c x.1 x.2.1)
      (sum_zero_outE x) hx.ne_p hx.ne_q hx.ne_e a b c (edgeQ x d t w) u v (mn := mn)
      (mx := mxL x.1 x.2.1) (by rwa [absk_outE]) ⟨m1, m2, by rwa [absk_outE]⟩
    have hE := norm_edgeQ x d t w
    have hkb : kerB 2 (r * Phi a b c x.1 x.2.1) mn (mxL x.1 x.2.1) ≤
        52 * (absk x.1 ^ 2 * absk x.2.1 ^ 2 * absk (x.1 + x.2.1) ^ 2) * kT |r| (x.1, x.2.1) := by
      refine hK.trans ?_
      have e : 13 * mn ^ 2 * mxL x.1 x.2.1 ^ (2 * 2) * kT |r| (x.1, x.2.1) =
          13 * (mn ^ 2 * mxL x.1 x.2.1 ^ 4) * kT |r| (x.1, x.2.1) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hw2 hk
      nlinarith only [this]
    refine hc.trans ?_
    have h0 : 0 ≤ kerB 2 (r * Phi a b c x.1 x.2.1) mn (mxL x.1 x.2.1) := by
      unfold kerB
      have hm : 0 ≤ mn := by
        have h1 := absk_nonneg x.1
        have h2 := absk_nonneg x.2.1
        have h3 := absk_nonneg (x.1 + x.2.1)
        rcases hmn with h | h | h <;> linarith
      have := (absk_nonneg x.1).trans (le_mxL x.1 x.2.1).1
      positivity
    have hE2 : ‖edgeQ x d t w‖ * ‖u‖ * ‖v‖ ≤
        hiMu x.2.2 (inL x) * (8 * absk x.1) * amp t w u v := by
      have := mul_le_mul_of_nonneg_right hE (norm_nonneg u)
      have := mul_le_mul_of_nonneg_right this (norm_nonneg v)
      refine this.trans (le_of_eq ?_)
      unfold amp
      ring
    calc _ ≤ kerB 2 (r * Phi a b c x.1 x.2.1) mn (mxL x.1 x.2.1) *
          (hiMu x.2.2 (inL x) * (8 * absk x.1) * amp t w u v) :=
          mul_le_mul_of_nonneg_left hE2 h0
      _ ≤ 52 * (absk x.1 ^ 2 * absk x.2.1 ^ 2 * absk (x.1 + x.2.1) ^ 2) * kT |r| (x.1, x.2.1) *
          (hiMu x.2.2 (inL x) * (8 * absk x.1) * amp t w u v) :=
          mul_le_mul_of_nonneg_right hkb (by have := absk_nonneg x.1; positivity)
      _ = _ := by ring
  · simp only [coreQ, hN, ite_false, norm_zero]
    have := absk_nonneg x.1
    have := absk_nonneg x.2.1
    positivity

/-- **The coefficient at weight one.** -/
theorem coreQ_one_le (hx : Act x) (r : ℝ) (d a b c : Sgn) (t w u v : V3) :
    ‖coreQ 1 r x d a b c t w u v‖ ≤ 104 * hiMu x.2.2 (inL x) *
      (mxL x.1 x.2.1 * absk x.1 ^ 2 * absk x.2.1 * absk (x.1 + x.2.1)) * kT |r| (x.1, x.2.1) *
        amp t w u v := by
  have hμ := hiMu_nonneg x.2.2 (inL x)
  have hk := kT_nonneg |r| (x.1, x.2.1)
  have hA := amp_nonneg t w u v
  have hmx0 : 0 ≤ mxL x.1 x.2.1 := (absk_nonneg _).trans (le_mxL _ _).1
  by_cases hN : NearT a b c x.1 x.2.1
  · obtain ⟨mn, hmn, -, hw1, hker⟩ := near_ker r hx.p hx.q hx.e
    have hK := hker 1 a b c hN
    simp only [coreQ, hN, ite_true]
    obtain ⟨m1, m2, m3⟩ := le_mxL x.1 x.2.1
    have hc := cyc3_le (j := 1) (ε := -1) (Or.inl rfl) (Or.inr rfl) (r * Phi a b c x.1 x.2.1)
      (sum_zero_outE x) hx.ne_p hx.ne_q hx.ne_e a b c (edgeQ x d t w) u v (mn := mn)
      (mx := mxL x.1 x.2.1) (by rwa [absk_outE]) ⟨m1, m2, by rwa [absk_outE]⟩
    have hE := norm_edgeQ x d t w
    have hkb : kerB 1 (r * Phi a b c x.1 x.2.1) mn (mxL x.1 x.2.1) ≤
        13 * (mxL x.1 x.2.1 * (absk x.1 * absk x.2.1 * absk (x.1 + x.2.1))) *
          kT |r| (x.1, x.2.1) := by
      refine hK.trans ?_
      have e : 13 * mn ^ 2 * mxL x.1 x.2.1 ^ (2 * 1) * kT |r| (x.1, x.2.1) =
          13 * (mn ^ 2 * mxL x.1 x.2.1 ^ 2) * kT |r| (x.1, x.2.1) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hw1 hk
      nlinarith only [this]
    refine hc.trans ?_
    have h0 : 0 ≤ kerB 1 (r * Phi a b c x.1 x.2.1) mn (mxL x.1 x.2.1) := by
      unfold kerB
      have hm : 0 ≤ mn := by
        have h1 := absk_nonneg x.1
        have h2 := absk_nonneg x.2.1
        have h3 := absk_nonneg (x.1 + x.2.1)
        rcases hmn with h | h | h <;> linarith
      positivity
    have hE2 : ‖edgeQ x d t w‖ * ‖u‖ * ‖v‖ ≤
        hiMu x.2.2 (inL x) * (8 * absk x.1) * amp t w u v := by
      have := mul_le_mul_of_nonneg_right hE (norm_nonneg u)
      have := mul_le_mul_of_nonneg_right this (norm_nonneg v)
      refine this.trans (le_of_eq ?_)
      unfold amp
      ring
    calc _ ≤ kerB 1 (r * Phi a b c x.1 x.2.1) mn (mxL x.1 x.2.1) *
          (hiMu x.2.2 (inL x) * (8 * absk x.1) * amp t w u v) :=
          mul_le_mul_of_nonneg_left hE2 h0
      _ ≤ 13 * (mxL x.1 x.2.1 * (absk x.1 * absk x.2.1 * absk (x.1 + x.2.1))) *
            kT |r| (x.1, x.2.1) *
          (hiMu x.2.2 (inL x) * (8 * absk x.1) * amp t w u v) :=
          mul_le_mul_of_nonneg_right hkb (by have := absk_nonneg x.1; positivity)
      _ = _ := by ring
  · simp only [coreQ, hN, ite_false, norm_zero]
    have := absk_nonneg x.1
    have := absk_nonneg x.2.1
    have := absk_nonneg (x.1 + x.2.1)
    positivity

/-- The sum of the sixteen channels of a term. -/
lemma termQ_le {j : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ d a b c, NearT a b c x.1 x.2.1 →
      Rq r d b c x * ‖coreQ j r x d a b c t w u v‖ ≤ B) : ‖termQ j r x τ t w u v‖ ≤ 16 * B := by
  have hch : ∀ d a b c, ‖resolv (-1) (heatQ x) (r * psiQ d b c x) *
      (chQ τ d b c x * coreQ j r x d a b c t w u v)‖ ≤ B := fun d a b c => by
    by_cases hN : NearT a b c x.1 x.2.1
    · rw [norm_mul, norm_mul, norm_chQ, one_mul]
      exact h d a b c hN
    · simp only [coreQ, hN, ite_false, mul_zero, norm_zero]
      exact hB
  have h1 : ‖termQ j r x τ t w u v‖ ≤ ∑ _d : Sgn, ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, B :=
    norm_sum_le_of_le _ fun d _ => norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
      norm_sum_le_of_le _ fun c _ => hch d a b c
  refine h1.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

/-- The sum of the sixteen channels of a source term. -/
lemma srcQ_le {j : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ d a b c, NearT a b c x.1 x.2.1 → ‖coreQ j r x d a b c t w u v‖ ≤ B) :
    ‖srcQ j r x τ t w u v‖ ≤ 16 * B := by
  have hch : ∀ d a b c, ‖chQ τ d b c x * coreQ j r x d a b c t w u v‖ ≤ B := fun d a b c => by
    by_cases hN : NearT a b c x.1 x.2.1
    · rw [norm_mul, norm_chQ, one_mul]
      exact h d a b c hN
    · simp only [coreQ, hN, ite_false, mul_zero, norm_zero]
      exact hB
  have h1 : ‖srcQ j r x τ t w u v‖ ≤ ∑ _d : Sgn, ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, B :=
    norm_sum_le_of_le _ fun d _ => norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
      norm_sum_le_of_le _ fun c _ => hch d a b c
  refine h1.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

/-! ### The quartic at weight two -/

/-- **One label of `Q₄`.** -/
theorem termQ_two_le (hr : r ≠ 0) (hx : Act x) (τ : ℝ) (t w u v : V3) :
    ‖termQ 2 r x τ t w u v‖ ≤ 2 ^ 14 / |r| * kT |r| (x.1, x.2.1) *
      ((absk x.2.2 ^ 2 * ‖t‖) * ‖w‖ * (absk x.2.1 ^ 2 * ‖u‖) *
        (absk (x.1 + x.2.1) ^ 2 * ‖v‖)) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hk := kT_nonneg |r| (x.1, x.2.1)
  have hA := amp_nonneg t w u v
  set Y := absk x.2.1 ^ 2 * absk (x.1 + x.2.1) ^ 2 * kT |r| (x.1, x.2.1) * amp t w u v with hY
  have hY0 : 0 ≤ Y := by positivity
  have hB : 0 ≤ 615 / |r| * (absk x.2.2 ^ 2 * Y) := by positivity
  have hmain := termQ_le (j := 2) (r := r) (x := x) (t := t) (w := w) (u := u) (v := v) (τ := τ)
    hB fun d a b c hN => ?_
  · refine hmain.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_right
      (by norm_num : (16 * 615 : ℝ) ≤ 2 ^ 14) (by positivity :
        0 ≤ 1 / |r| * (absk x.2.2 ^ 2 * Y)))) |>.trans (le_of_eq ?_)
    · ring
    · simp only [hY, amp]
      field_simp
  · have hc := coreQ_two_le hx r d a b c t w u v
    have hR := Rq_nonneg r d b c x
    by_cases hμ : hiMu x.2.2 (inL x) = 0
    · rw [hμ] at hc
      have h0 : ‖coreQ 2 r x d a b c t w u v‖ ≤ 0 := by simpa using hc
      exact (mul_le_mul_of_nonneg_left h0 hR).trans (by simpa using hB)
    have hS := sep_of hμ
    have hs := Sep.s_pos hS hx
    have hs0 : 0 < absk x.2.2 := by linarith
    have h1 := R_phase (d := d) hr hx hS hN
    have hp := Sep.p_le hS
    have hp0 := absk_nonneg x.1
    have hp3 : absk x.1 ^ 3 ≤ (17 / 16 * absk x.2.2) ^ 3 := pow_le_pow_left₀ hp0 hp 3
    have hμ1 := hiMu_le_one x.2.2 (inL x)
    have hμ0 := hiMu_nonneg x.2.2 (inL x)
    have h2 : ‖coreQ 2 r x d a b c t w u v‖ ≤ 416 * ((17 / 16 * absk x.2.2) ^ 3 * Y) := by
      refine hc.trans ?_
      have e : 416 * hiMu x.2.2 (inL x) *
          (absk x.1 ^ 3 * absk x.2.1 ^ 2 * absk (x.1 + x.2.1) ^ 2) * kT |r| (x.1, x.2.1) *
            amp t w u v = 416 * (hiMu x.2.2 (inL x) * (absk x.1 ^ 3 * Y)) := by
        simp only [hY]
        ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have h3 : absk x.1 ^ 3 * Y ≤ (17 / 16 * absk x.2.2) ^ 3 * Y :=
        mul_le_mul_of_nonneg_right hp3 hY0
      have h4 : 0 ≤ absk x.1 ^ 3 * Y := by positivity
      nlinarith only [h3, h4, hμ1, hμ0]
    have h3 : Rq r d b c x * ‖coreQ 2 r x d a b c t w u v‖ ≤
        Rq r d b c x * (416 * ((17 / 16 * absk x.2.2) ^ 3 * Y)) :=
      mul_le_mul_of_nonneg_left h2 hR
    refine h3.trans ?_
    have e0 : 615 / |r| * (absk x.2.2 ^ 2 * Y) = 615 * (absk x.2.2 ^ 2 * Y) / |r| := by ring
    rw [e0, le_div_iff₀ hq]
    have e : Rq r d b c x * (416 * ((17 / 16 * absk x.2.2) ^ 3 * Y)) * |r| =
        (Rq r d b c x * (|r| * absk x.2.2)) * (416 * (17 / 16) ^ 3 * (absk x.2.2 ^ 2 * Y)) := by
      ring
    rw [e]
    have h5 := mul_le_mul_of_nonneg_right h1 (by positivity :
      0 ≤ 416 * (17 / 16 : ℝ) ^ 3 * (absk x.2.2 ^ 2 * Y))
    refine h5.trans ?_
    have h6 : 0 ≤ absk x.2.2 ^ 2 * Y := by positivity
    nlinarith only [h6]

/-- **One label of the source**, weight two. -/
theorem srcQ_two_le (hx : Act x) (r τ : ℝ) (t w u v : V3) :
    ‖srcQ 2 r x τ t w u v‖ ≤ 2 ^ 14 * kT |r| (x.1, x.2.1) *
      ((absk x.2.2 ^ 3 * ‖t‖) * ‖w‖ * (absk x.2.1 ^ 2 * ‖u‖) *
        (absk (x.1 + x.2.1) ^ 2 * ‖v‖)) := by
  have hk := kT_nonneg |r| (x.1, x.2.1)
  have hA := amp_nonneg t w u v
  set Y := absk x.2.1 ^ 2 * absk (x.1 + x.2.1) ^ 2 * kT |r| (x.1, x.2.1) * amp t w u v with hY
  have hY0 : 0 ≤ Y := by positivity
  have hB : 0 ≤ 512 * (2 * (absk x.2.2 ^ 3 * Y)) := by
    have := absk_nonneg x.2.2
    positivity
  have hmain := srcQ_le (j := 2) (r := r) (x := x) (t := t) (w := w) (u := u) (v := v) (τ := τ)
    hB fun d a b c hN => ?_
  · refine hmain.trans (le_of_eq ?_)
    simp only [hY, amp]
    ring
  · have hc := coreQ_two_le hx r d a b c t w u v
    by_cases hμ : hiMu x.2.2 (inL x) = 0
    · rw [hμ] at hc
      have h0 : ‖coreQ 2 r x d a b c t w u v‖ ≤ 0 := by simpa using hc
      exact h0.trans hB
    have hS := sep_of hμ
    have hp := Sep.p_le hS
    have hp0 := absk_nonneg x.1
    have hs0 := absk_nonneg x.2.2
    have hp3 : absk x.1 ^ 3 ≤ (17 / 16 * absk x.2.2) ^ 3 := pow_le_pow_left₀ hp0 hp 3
    have hμ1 := hiMu_le_one x.2.2 (inL x)
    have hμ0 := hiMu_nonneg x.2.2 (inL x)
    refine hc.trans ?_
    have e : 416 * hiMu x.2.2 (inL x) *
        (absk x.1 ^ 3 * absk x.2.1 ^ 2 * absk (x.1 + x.2.1) ^ 2) * kT |r| (x.1, x.2.1) *
          amp t w u v = 416 * (hiMu x.2.2 (inL x) * (absk x.1 ^ 3 * Y)) := by
      simp only [hY]
      ring
    rw [e]
    have h3 : absk x.1 ^ 3 * Y ≤ (17 / 16 * absk x.2.2) ^ 3 * Y :=
      mul_le_mul_of_nonneg_right hp3 hY0
    have h4 : 0 ≤ absk x.1 ^ 3 * Y := by positivity
    have h5 : 0 ≤ absk x.2.2 ^ 3 * Y := by positivity
    have h6 : hiMu x.2.2 (inL x) * (absk x.1 ^ 3 * Y) ≤ (17 / 16 * absk x.2.2) ^ 3 * Y := by
      nlinarith only [h3, h4, hμ1, hμ0]
    have e2 : (17 / 16 * absk x.2.2) ^ 3 * Y = (17 / 16) ^ 3 * (absk x.2.2 ^ 3 * Y) := by ring
    rw [e2] at h6
    nlinarith only [h6, h5]

end OVNS.Quant.Quartic

end
