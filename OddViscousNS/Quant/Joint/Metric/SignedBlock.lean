import OddViscousNS.Quant.Joint.Metric.Channel

/-!
# The signed block at a large intermediate (step J5, node N2)

On the sector `M ≥ 4 max(L, J)`, at weights `s ≤ 2`, with `W = M⁴/(L²J²)`:
`‖X₂(f,g)_{lj}‖ ≤ 2¹⁵ W f_a g_b [1/q² + (L + J)/(q M²)]` (`norm_X2b_signed_le`).
The second term is the "phase and noncommon" relative factor `(L + J)/M`, the first is the heat
factor `M/q`, both relative to the old one-root `W/(q M)`.

The proof is `twoRoot_split` with the sizes of the four edges.  The two inner phases have modulus at
least `(3/4) q |n| M`, the exterior phase at most `q |n| (L + J)`, the two inner heats sum to at
most `6 M²`.  No outer cancellation is used: `outerInv` is paid by `1/Σ`, and `Σ ≥ (9/8) M²`,
because both ancestors are comparable to `M`.  Body 36: "No cancellation is claimed on the old outer
heat."
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### D. The sizes at a large intermediate -/

private lemma abs_sg_mul (a : Sgn) (x : ℝ) : |sg a * x| = |x| := by
  rw [abs_mul]
  cases a <;> simp [sg]

/-- **The inner phases** (Body 33: "Both inner signed differences have modulus at least `M/2` before
multiplying by `|n|`"; here `3/4`): at `|v| ≥ 4|u|`, on the same vertical. -/
lemma lam_gap {u v : Mode} (h2 : u 2 = v 2) (h : 4 * absk u ≤ absk v) (c e : Sgn) :
    3 / 4 * (|(v 2 : ℝ)| * absk v) ≤ |lam e v - lam c u| := by
  have hs : lam e v - lam c u = (v 2 : ℝ) * (sg e * absk v - sg c * absk u) := by
    simp only [lam, h2]
    ring
  have hu := absk_nonneg u
  have hv := absk_nonneg v
  have h1 : 3 / 4 * absk v ≤ |sg e * absk v - sg c * absk u| := by
    have h3 := abs_sub_abs_le_abs_sub (sg e * absk v) (sg c * absk u)
    rw [abs_sg_mul, abs_sg_mul, abs_of_nonneg hv, abs_of_nonneg hu] at h3
    linarith
  rw [hs, abs_mul]
  have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (v 2 : ℝ))
  linarith

/-- **The exterior phase** (Body 33: "`|δ_lk| ≤ |n|(L + K)`"). -/
lemma lam_ext {u v : Mode} (h2 : u 2 = v 2) (c e : Sgn) :
    |lam e v - lam c u| ≤ |(v 2 : ℝ)| * (absk u + absk v) := by
  have hs : lam e v - lam c u = (v 2 : ℝ) * (sg e * absk v - sg c * absk u) := by
    simp only [lam, h2]
    ring
  rw [hs, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (abs_sub _ _).trans ?_
  rw [abs_sg_mul, abs_sg_mul, abs_of_nonneg (absk_nonneg v), abs_of_nonneg (absk_nonneg u)]
  linarith

/-- The arithmetic of the signed gain. -/
lemma rho_le {H₁ H₂ z₁ z₂ q N M S : ℝ} (hq : 0 < q) (hN : 1 ≤ N) (hM : 0 < M) (hS : 0 ≤ S)
    (h1 : 0 < H₁) (h2 : 0 < H₂) (hH : H₁ + H₂ ≤ 6 * M ^ 2) (hz₁ : 3 / 4 * (q * (N * M)) ≤ |z₁|)
    (hz₂ : 3 / 4 * (q * (N * M)) ≤ |z₂|) (hs : |z₁ + z₂| ≤ q * (N * S)) :
    ‖resolv (-1) H₁ z₁ + resolv (-1) H₂ z₂‖ ≤ 32 / 3 / q ^ 2 + 16 / 9 * S / (q * M ^ 2) := by
  have hT : 0 < 3 / 4 * (q * (N * M)) := by positivity
  have n1 : 0 < |z₁| := hT.trans_le hz₁
  have n2 : 0 < |z₂| := hT.trans_le hz₂
  refine (norm_resolv_add_le h1 h2 (abs_pos.1 n1) (abs_pos.1 n2)).trans ?_
  have hd : (3 / 4 * (q * (N * M))) ^ 2 ≤ |z₁| * |z₂| := by
    rw [sq]
    exact mul_le_mul hz₁ hz₂ hT.le n1.le
  have hnum : H₁ + H₂ + |z₁ + z₂| ≤ 6 * M ^ 2 + q * (N * S) := by linarith
  have hnn : 0 ≤ 6 * M ^ 2 + q * (N * S) := by positivity
  calc (H₁ + H₂ + |z₁ + z₂|) / (|z₁| * |z₂|)
      ≤ (6 * M ^ 2 + q * (N * S)) / (3 / 4 * (q * (N * M))) ^ 2 :=
        div_le_div₀ hnn hnum (by positivity) hd
    _ ≤ _ := by
        rw [div_le_iff₀ (by positivity)]
        have e : (32 / 3 / q ^ 2 + 16 / 9 * S / (q * M ^ 2)) * (3 / 4 * (q * (N * M))) ^ 2 =
            6 * M ^ 2 * N ^ 2 + q * (N ^ 2 * S) := by
          field_simp
          ring
        rw [e]
        have h3 : M ^ 2 ≤ M ^ 2 * N ^ 2 := le_mul_of_one_le_right (by positivity) (by nlinarith)
        have h4 : N * S ≤ N ^ 2 * S := mul_le_mul_of_nonneg_right (by nlinarith) hS
        have h5 := mul_le_mul_of_nonneg_left h4 hq.le
        linarith

/-- One inverse denominator at a large intermediate: "the one-root inner upper `1/(q|n|M)`". -/
lemma rho₁_le {H z q N M : ℝ} (hq : 0 < q) (hN : 1 ≤ N) (hM : 0 < M)
    (hz : 3 / 4 * (q * (N * M)) ≤ |z|) : ‖resolv (-1) H z‖ ≤ 4 / 3 / (q * M) := by
  have hT : 0 < 3 / 4 * (q * (N * M)) := by positivity
  have n1 : 0 < |z| := hT.trans_le hz
  refine (norm_resolv_le_abs H (abs_pos.1 n1)).trans ?_
  have h1 : 3 / 4 * (q * M) ≤ |z| := by
    refine le_trans ?_ hz
    have : q * M ≤ q * (N * M) := mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left hM.le hN) hq.le
    linarith
  calc 1 / |z| ≤ 1 / (3 / 4 * (q * M)) := one_div_le_one_div_of_le (by positivity) h1
    _ = _ := by
        field_simp

/-- The weights of an edge, against the ratio: at `s ≤ 2`. -/
lemma wt_up {s : ℕ} (hs : s ≤ 2) {u v : Mode} (hu : 0 < absk u) (h : absk u ≤ absk v) :
    1 ≤ (absk v / absk u) ^ 2 ∧ wt s v u ≤ (absk v / absk u) ^ 2 ∧ wt s u v ≤ 1 := by
  have h1 : 1 ≤ absk v / absk u := (one_le_div hu).2 h
  refine ⟨one_le_pow₀ h1, pow_le_pow_right₀ h1 hs, pow_le_one₀ (by
    have := absk_nonneg v
    positivity) ?_⟩
  exact div_le_one_of_le₀ h (hu.le.trans h)

/-- The product of the edges against `W = M⁴/(L²J²)`, for the three products of the two rootings. -/
lemma wt_prod_le {s : ℕ} (hs : s ≤ 2) {l m j : Mode} (hL : 0 < absk l) (hJ : 0 < absk j)
    (h1 : absk l ≤ absk m) (h2 : absk j ≤ absk m) :
    wt s m l * wt s m j ≤ (absk m / absk l) ^ 2 * (absk m / absk j) ^ 2 ∧
      wt s l m * wt s m j ≤ (absk m / absk l) ^ 2 * (absk m / absk j) ^ 2 ∧
      wt s m l * wt s j m ≤ (absk m / absk l) ^ 2 * (absk m / absk j) ^ 2 := by
  obtain ⟨a1, a2, a3⟩ := wt_up hs hL h1
  obtain ⟨b1, b2, b3⟩ := wt_up hs hJ h2
  have n1 := wt_nonneg s m l
  have n2 := wt_nonneg s m j
  exact ⟨mul_le_mul a2 b2 n2 (by positivity), mul_le_mul (a3.trans a1) b2 n2 (by positivity),
    mul_le_mul a2 (b3.trans b1) (wt_nonneg s j m) (by positivity)⟩

/-! ### E. The block at a large intermediate -/

/-- Two operators between three channels. -/
lemma norm_chain_le (T T' : V3 →L[ℂ] V3) (c e d : Sgn) (l m j : Mode) (w : V3) :
    ‖hel c l (T (hel e m (T' (hel d j w))))‖ ≤ ‖T‖ * ‖T'‖ * ‖w‖ := by
  have h1 : ‖T' (hel d j w)‖ ≤ ‖T'‖ * ‖w‖ :=
    (T'.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_hel_le _ _ _) (norm_nonneg _))
  calc _ ≤ ‖T (hel e m (T' (hel d j w)))‖ := norm_hel_le _ _ _
    _ ≤ ‖T‖ * ‖hel e m (T' (hel d j w))‖ := T.le_opNorm _
    _ ≤ ‖T‖ * (‖T'‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left ((norm_hel_le _ _ _).trans h1) (norm_nonneg _)
    _ = _ := by ring

/-- A term of the split: a scalar times a chain. -/
private lemma term_le {R : ℂ} {ρ nA nB : ℝ} {T T' : V3 →L[ℂ] V3} (c e d : Sgn) (l m j : Mode)
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

/-- The channel of the two rootings, against the sizes of the four edges. -/
lemma norm_chan_le {s : ℕ} {r τ : ℝ} {f g : Field} {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0)
    (hj : (l - a - b) 2 ≠ 0) (h1 : ∀ e c, lam e (l - a) ≠ lam c l)
    (h2 : ∀ d e, lam d (l - a - b) ≠ lam e (l - a)) (c d : Sgn) (w : V3) {ρ ρ₁ nA nB nC nD : ℝ}
    (hρ : ∀ e, ‖chR r (triHeat a (l - a)) c e l (l - a) +
      chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)‖ ≤ ρ)
    (hρ₁ : ∀ e, ‖chR r (triHeat a (l - a)) c e l (l - a)‖ ≤ ρ₁)
    (hρ₂ : ∀ e, ‖chR r (triHeat b (l - a - b)) e d (l - a) (l - a - b)‖ ≤ ρ₁)
    (hA : ‖Lad s τ a l (l - a) (f a)‖ ≤ nA) (hB : ‖Lb s τ b (l - a) (l - a - b) (g b)‖ ≤ nB)
    (hC : ‖Lb s τ a l (l - a) (f a)‖ ≤ nC) (hD : ‖Lad s τ b (l - a) (l - a - b) (g b)‖ ≤ nD) :
    ‖hel c l (twoRoot s r τ f g l a b (hel d (l - a - b) w))‖ ≤
      2 * (ρ * (nA * nB) + ρ₁ * (nC * nB) + ρ₁ * (nA * nD)) * ‖w‖ := by
  rw [twoRoot_split s r τ f g ha hb hj h1 h2]
  refine (norm_sum_le_of_le (n := fun _ => (ρ * (nA * nB) + ρ₁ * (nC * nB) + ρ₁ * (nA * nD)) * ‖w‖)
    _ fun e _ => ?_).trans (le_of_eq ?_)
  · refine (norm_add_le _ _).trans ?_
    have t1 := term_le c e d l (l - a) (l - a - b) w (hρ e) hA hB
    have t2 := term_le c e d l (l - a) (l - a - b) w (hρ₁ e) hC hB
    have t3 := term_le c e d l (l - a) (l - a - b) w (hρ₂ e) hA hD
    calc _ ≤ _ := add_le_add (norm_add_le _ _) t3
      _ ≤ ρ * (nA * nB) * ‖w‖ + ρ₁ * (nC * nB) * ‖w‖ + ρ₁ * (nA * nD) * ‖w‖ :=
          add_le_add (add_le_add t1 t2) le_rfl
      _ = _ := by ring
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    ring

/-- The bound of a block from a bound on the exterior channels of its source. -/
lemma norm_outerInv_of_chan {H K : ℝ} (hH : 0 < H) (hK : 0 ≤ K) (r : ℝ) (l j : Mode)
    (T : V3 →L[ℂ] V3) (h : ∀ c e w, ‖hel c l (T (hel e j w))‖ ≤ K * ‖w‖) :
    ‖outerInv r H l j T‖ ≤ 4 / H * K := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  simp only [outerInv, sum_apply, smul_apply, ContinuousLinearMap.comp_apply, helL_apply]
  have hterm : ∀ c e, ‖resolv (-1) H (r * outerPhi c e l j) • hel c l (T (hel e j w))‖ ≤
      1 / H * (K * ‖w‖) := fun c e => by
    rw [norm_smul]
    exact mul_le_mul (Quant.norm_resolv_le (Or.inr rfl) hH _) (h c e w) (norm_nonneg _)
      (by positivity)
  refine (norm_sum_le_of_le _ fun c _ => norm_sum_le_of_le _ fun e _ => hterm c e).trans
    (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

/-- The final arithmetic of the signed block. -/
lemma signed_arith {q M L J W ff gg H nAB nCB nAD : ℝ} (hq : 0 < q) (hM : 0 < M) (hL : 0 ≤ L)
    (hJ : 0 ≤ J) (hW : 0 ≤ W) (hff : 0 ≤ ff) (hgg : 0 ≤ gg) (hH : 9 / 8 * M ^ 2 ≤ H)
    (h1 : nAB ≤ 256 * W * M ^ 2 * (ff * gg)) (h2 : nCB ≤ 256 * W * (L * M) * (ff * gg))
    (h3 : nAD ≤ 256 * W * (M * J) * (ff * gg)) :
    4 / H * (2 * ((32 / 3 / q ^ 2 + 16 / 9 * (L + J) / (q * M ^ 2)) * nAB +
        4 / 3 / (q * M) * nCB + 4 / 3 / (q * M) * nAD)) ≤
      2 ^ 15 * W * (ff * gg) * (1 / q ^ 2 + (L + J) / (q * M ^ 2)) := by
  set Y := W * (ff * gg) with hY
  have hY0 : 0 ≤ Y := by positivity
  set X₁ := 1 / q ^ 2 with hX₁
  set X₂ := (L + J) / (q * M ^ 2) with hX₂
  have hX₁0 : 0 ≤ X₁ := by positivity
  have hX₂0 : 0 ≤ X₂ := by positivity
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have e1 : 32 / 3 / q ^ 2 + 16 / 9 * (L + J) / (q * M ^ 2) = 32 / 3 * X₁ + 16 / 9 * X₂ := by
    simp only [hX₁, hX₂]
    ring
  have e2 : 4 / 3 / (q * M) * (L * M) + 4 / 3 / (q * M) * (M * J) = 4 / 3 * X₂ * M ^ 2 := by
    simp only [hX₂]
    field_simp
  have h4 : (32 / 3 * X₁ + 16 / 9 * X₂) * nAB ≤
      (32 / 3 * X₁ + 16 / 9 * X₂) * (256 * Y * M ^ 2) := by
    refine mul_le_mul_of_nonneg_left (h1.trans (le_of_eq ?_)) (by positivity)
    simp only [hY]
    ring
  have h5 : 4 / 3 / (q * M) * nCB + 4 / 3 / (q * M) * nAD ≤ 4 / 3 * X₂ * M ^ 2 * (256 * Y) := by
    rw [← e2]
    have hρ : 0 ≤ 4 / 3 / (q * M) := by positivity
    have a1 := mul_le_mul_of_nonneg_left h2 hρ
    have a2 := mul_le_mul_of_nonneg_left h3 hρ
    calc _ ≤ _ := add_le_add a1 a2
      _ = _ := by
          simp only [hY]
          ring
  rw [e1]
  have hS : (32 / 3 * X₁ + 16 / 9 * X₂) * nAB + 4 / 3 / (q * M) * nCB + 4 / 3 / (q * M) * nAD ≤
      256 * Y * M ^ 2 * (32 / 3 * X₁ + 28 / 9 * X₂) := by
    calc _ ≤ (32 / 3 * X₁ + 16 / 9 * X₂) * (256 * Y * M ^ 2) + 4 / 3 * X₂ * M ^ 2 * (256 * Y) := by
          linarith
      _ = _ := by ring
  have hH' : 4 / H ≤ 32 / 9 / M ^ 2 := by
    rw [div_le_div_iff₀ hH0 (by positivity)]
    linarith
  have hMne : M ^ 2 ≠ 0 := by positivity
  have hR : 0 ≤ 256 * Y * M ^ 2 * (32 / 3 * X₁ + 28 / 9 * X₂) := by positivity
  calc 4 / H * (2 * ((32 / 3 * X₁ + 16 / 9 * X₂) * nAB + 4 / 3 / (q * M) * nCB +
        4 / 3 / (q * M) * nAD))
      ≤ 4 / H * (2 * (256 * Y * M ^ 2 * (32 / 3 * X₁ + 28 / 9 * X₂))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ 32 / 9 / M ^ 2 * (2 * (256 * Y * M ^ 2 * (32 / 3 * X₁ + 28 / 9 * X₂))) :=
        mul_le_mul_of_nonneg_right hH' (by positivity)
    _ = 32 / 9 * (2 * (256 * Y * (32 / 3 * X₁ + 28 / 9 * X₂))) := by
        field_simp
    _ ≤ 2 ^ 15 * Y * (X₁ + X₂) := by nlinarith [mul_nonneg hY0 hX₁0, mul_nonneg hY0 hX₂0]
    _ = _ := by
        simp only [hY]
        ring

/-- The heats, in the lengths. -/
private lemma heats_real {L M J Pa Pb : ℝ} (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J) (hPa0 : 0 ≤ Pa)
    (hPb0 : 0 ≤ Pb) (hL : 4 * L ≤ M) (hJ : 4 * J ≤ M) (h1 : Pa ≤ L + M) (h2 : Pb ≤ M + J)
    (h3 : M ≤ L + Pa) (h4 : M ≤ J + Pb) :
    Pa ^ 2 + M ^ 2 + L ^ 2 + (Pb ^ 2 + J ^ 2 + M ^ 2) ≤ 6 * M ^ 2 ∧
      9 / 8 * M ^ 2 ≤ L ^ 2 + J ^ 2 + Pa ^ 2 + Pb ^ 2 := by
  have hM0 : 0 ≤ M := by linarith
  have a1 : Pa ^ 2 ≤ (5 / 4 * M) ^ 2 := pow_le_pow_left₀ hPa0 (by linarith) 2
  have a2 : Pb ^ 2 ≤ (5 / 4 * M) ^ 2 := pow_le_pow_left₀ hPb0 (by linarith) 2
  have a3 : L ^ 2 ≤ (1 / 4 * M) ^ 2 := pow_le_pow_left₀ hL0 (by linarith) 2
  have a4 : J ^ 2 ≤ (1 / 4 * M) ^ 2 := pow_le_pow_left₀ hJ0 (by linarith) 2
  have a5 : (3 / 4 * M) ^ 2 ≤ Pa ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have a6 : (3 / 4 * M) ^ 2 ≤ Pb ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  constructor <;> nlinarith [sq_nonneg L, sq_nonneg J, sq_nonneg M]

/-- The heats at a large intermediate: "the two true heat sums are `O(M²)`", `Σ ≥ c M²`. -/
lemma high_heats {l a b : Mode} (hj0 : l - a - b ≠ 0) (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) :
    0 < triHeat a (l - a) ∧ 0 < triHeat b (l - a - b) ∧
      triHeat a (l - a) + triHeat b (l - a - b) ≤ 6 * absk (l - a) ^ 2 ∧
      9 / 8 * absk (l - a) ^ 2 ≤ heat4 l (l - a - b) a b := by
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  have hPa : absk a ≤ absk l + absk (l - a) := by
    have := absk_sub_le l (l - a)
    rwa [show l - (l - a) = a by abel] at this
  have hPb : absk b ≤ absk (l - a) + absk (l - a - b) := by
    have := absk_sub_le (l - a) (l - a - b)
    rwa [show l - a - (l - a - b) = b by abel] at this
  have hPb' : absk (l - a) ≤ absk (l - a - b) + absk b := by
    have := absk_add_le (l - a - b) b
    rwa [show l - a - b + b = l - a by abel] at this
  have hT1 : triHeat a (l - a) = absk a ^ 2 + absk (l - a) ^ 2 + absk l ^ 2 := by
    simp only [triHeat, e1, absk_sq]
  have hT2 : triHeat b (l - a - b) = absk b ^ 2 + absk (l - a - b) ^ 2 + absk (l - a) ^ 2 := by
    simp only [triHeat, e2, absk_sq]
  have hT3 : heat4 l (l - a - b) a b =
      absk l ^ 2 + absk (l - a - b) ^ 2 + absk a ^ 2 + absk b ^ 2 := by
    simp only [heat4, absk_sq]
  have hJ1 := one_le_absk hj0
  have hM : 0 < absk (l - a) := by linarith
  have hr := heats_real (absk_nonneg l) (absk_nonneg (l - a - b)) (absk_nonneg a) (absk_nonneg b)
    hL hJ hPa hPb (absk_sub_le l a) hPb'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hT1]
    positivity
  · rw [hT2]
    positivity
  · rw [hT1, hT2]
    exact hr.1
  · rw [hT3]
    exact hr.2

/-- The channel of the two rootings at a large intermediate. -/
lemma high_chan {s : ℕ} {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) (c d : Sgn) (w : V3) :
    ‖hel c l (twoRoot s r τ f g l a b (hel d (l - a - b) w))‖ ≤
      2 * ((32 / 3 / |r| ^ 2 + 16 / 9 * (absk l + absk (l - a - b)) /
            (|r| * absk (l - a) ^ 2)) *
          ((16 * wt s (l - a) l * absk (l - a) * ‖f a‖) *
            (16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖g b‖)) +
        4 / 3 / (|r| * absk (l - a)) * ((16 * wt s l (l - a) * absk l * ‖f a‖) *
            (16 * wt s (l - a) (l - a - b) * absk (l - a) * ‖g b‖)) +
        4 / 3 / (|r| * absk (l - a)) * ((16 * wt s (l - a) l * absk (l - a) * ‖f a‖) *
            (16 * wt s (l - a - b) (l - a) * absk (l - a - b) * ‖g b‖))) * ‖w‖ := by
  obtain ⟨-, hm0, hj0⟩ := fast_labels ha hb hj
  have e1 : a + (l - a) = l := by abel
  have e2 : b + (l - a - b) = l - a := by abel
  have hl2 : l 2 = (l - a) 2 := by simp [ha]
  have hj2 : (l - a - b) 2 = (l - a) 2 := by simp [hb]
  have hm2 : (l - a) 2 ≠ 0 := by rwa [← hj2]
  have hq : 0 < |r| := abs_pos.2 hr
  have hM1 := one_le_absk hm0
  have hN : (1 : ℝ) ≤ |((l - a) 2 : ℝ)| := by
    have : (1 : ℤ) ≤ |(l - a) 2| := Int.one_le_abs hm2
    exact_mod_cast this
  obtain ⟨hH1, hH2, hHs, -⟩ := high_heats hj0 hL hJ
  have hg1 : ∀ c e, 0 < |lam e (l - a) - lam c l| := fun c e =>
    lt_of_lt_of_le (by positivity) (lam_gap hl2 hL c e)
  have hg2 : ∀ d e, 0 < |lam e (l - a) - lam d (l - a - b)| := fun d e =>
    lt_of_lt_of_le (by positivity) (lam_gap hj2 hJ d e)
  have hne₁ : ∀ e c, lam e (l - a) ≠ lam c l := fun e c h => by
    have := hg1 c e
    rw [h, sub_self, abs_zero] at this
    exact lt_irrefl _ this
  have hne₂ : ∀ d e, lam d (l - a - b) ≠ lam e (l - a) := fun d e h => by
    have := hg2 d e
    rw [h, sub_self, abs_zero] at this
    exact lt_irrefl _ this
  have hz₁ : ∀ c e, 3 / 4 * (|r| * (|((l - a) 2 : ℝ)| * absk (l - a))) ≤
      |r * (lam e (l - a) - lam c l)| := fun c e => by
    have := mul_le_mul_of_nonneg_left (lam_gap hl2 hL c e) hq.le
    rw [abs_mul]
    linarith
  have hz₂ : ∀ d e, 3 / 4 * (|r| * (|((l - a) 2 : ℝ)| * absk (l - a))) ≤
      |r * (lam d (l - a - b) - lam e (l - a))| := fun d e => by
    have := mul_le_mul_of_nonneg_left (lam_gap hj2 hJ d e) hq.le
    rw [abs_mul, abs_sub_comm (lam d (l - a - b))]
    linarith
  have hzs : ∀ c d e, |r * (lam e (l - a) - lam c l) + r * (lam d (l - a - b) - lam e (l - a))| ≤
      |r| * (|((l - a) 2 : ℝ)| * (absk l + absk (l - a - b))) := fun c d e => by
    have h := lam_ext (hl2.trans hj2.symm) c d
    rw [hj2] at h
    have e' : r * (lam e (l - a) - lam c l) + r * (lam d (l - a - b) - lam e (l - a)) =
        r * (lam d (l - a - b) - lam c l) := by
      ring
    rw [e', abs_mul]
    exact mul_le_mul_of_nonneg_left h hq.le
  have hS : 0 ≤ absk l + absk (l - a - b) := add_nonneg (absk_nonneg _) (absk_nonneg _)
  exact norm_chan_le ha hb hj hne₁ hne₂ c d w
    (fun e => rho_le hq hN (by linarith) hS hH1 hH2 hHs (hz₁ c e) (hz₂ d e) (hzs c d e))
    (fun e => rho₁_le hq hN (by linarith) (hz₁ c e))
    (fun e => rho₁_le hq hN (by linarith) (hz₂ d e))
    (norm_Lad_le s τ e1 (f a)) (norm_Lb_le s τ e2 (g b)) (norm_Lb_le s τ e1 (f a))
    (norm_Lad_le s τ e2 (g b))

/-- **The signed block** (Bodies 33, 36, 41; LOCAL457): at `M ≥ 4 max(L, J)`, at weights `s ≤ 2`,
both rootings with their outer heat,
`‖X₂(f,g)_{lj}‖ ≤ 2¹⁵ (M²/L²)(M²/J²) f_a g_b [1/q² + (L + J)/(q M²)]`.  The bracket is the sum of
the heat part and of the phase and noncommon parts.  This is LOCAL457's "`C q⁻¹ [M/q + (L + J)/M]
M³/(L²J²)`" at `s = 2`; at `s = 1` the same upper bound holds, with room. -/
theorem norm_X2b_signed_le {s : ℕ} (hs : s ≤ 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field)
    {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0)
    (hL : 4 * absk l ≤ absk (l - a)) (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) :
    ‖X2b s r τ f g l a b‖ ≤ 2 ^ 15 * ((absk (l - a) / absk l) ^ 2 *
      (absk (l - a) / absk (l - a - b)) ^ 2) * (‖f a‖ * ‖g b‖) *
        (1 / |r| ^ 2 + (absk l + absk (l - a - b)) / (|r| * absk (l - a) ^ 2)) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hq : 0 < |r| := abs_pos.2 hr
  have hL1 := one_le_absk hl0
  have hJ1 := one_le_absk hj0
  have hM1 := one_le_absk hm0
  obtain ⟨-, -, -, hH4⟩ := high_heats hj0 hL hJ
  obtain ⟨w1, w2, w3⟩ := wt_prod_le hs (lt_of_lt_of_le one_pos hL1) (lt_of_lt_of_le one_pos hJ1)
    (by linarith : absk l ≤ absk (l - a)) (by linarith : absk (l - a - b) ≤ absk (l - a))
  have hff := norm_nonneg (f a)
  have hgg := norm_nonneg (g b)
  have h0 := wt_nonneg s (l - a) l
  have h1 := wt_nonneg s (l - a) (l - a - b)
  have h2 := wt_nonneg s l (l - a)
  have h3 := wt_nonneg s (l - a - b) (l - a)
  have hH0 : 0 < heat4 l (l - a - b) a b := heat4_pos hj0 a b
  refine (norm_outerInv_of_chan hH0 ?_ r l (l - a - b) _
    fun c e w => high_chan hr τ f g ha hb hj hL hJ c e w).trans ?_
  · positivity
  refine signed_arith hq (by linarith) (by linarith) (by linarith) (by positivity) hff hgg hH4
    ?_ ?_ ?_
  · calc _ = 256 * (wt s (l - a) l * wt s (l - a) (l - a - b)) * absk (l - a) ^ 2 *
          (‖f a‖ * ‖g b‖) := by ring
      _ ≤ _ := by gcongr
  · calc _ = 256 * (wt s l (l - a) * wt s (l - a) (l - a - b)) * (absk l * absk (l - a)) *
          (‖f a‖ * ‖g b‖) := by ring
      _ ≤ _ := by gcongr
  · calc _ = 256 * (wt s (l - a) l * wt s (l - a - b) (l - a)) *
          (absk (l - a) * absk (l - a - b)) * (‖f a‖ * ‖g b‖) := by ring
      _ ≤ _ := by gcongr

end OVNS.Quant.Metric

end
