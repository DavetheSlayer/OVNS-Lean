import OddViscousNS.Quant.Joint.Metric.Static
import OddViscousNS.Quant.Joint.Metric.FibreSub

/-!
# The static bound of `X₂`: the form (step J5, node N3)

`X2Form_static_le`: Body 36's static bound,
`(C/q)[(1 + √(1 + ln D)) a² + a W + b²/D] + (C/q²) D a b`, bilinear in the two leaves, for every
multiplier of modulus at most one, at `s = 1, 2`.  After the pointwise kernel `norm_X2b_kernel`,
this is a sum of ten positive forms, and only the two kinds `pos2_base`, `pos2_band` of
`FibreForms.lean` are new.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {f g G F : Field}

/-! ### A. The positive forms -/

/-- A slow mean-zero field of `H²` is a slow sequence of `H¹`. -/
lemma slowH1_nrm (hf : MZ 2 f) (hf' : PiS f = f) : SlowH1 (nrm f) (hnorm 1 f) where
  nn _ := norm_nonneg _
  slow p hp := by
    simp only [nrm]
    rw [slow_zero hf' hp, norm_zero]
  mean := by
    simp only [nrm]
    rw [hf.mean, norm_zero]
  grad := l2B_gr (hf.inH.mono (by norm_num))

/-- A slow mean-zero field of `H^{1+ε}` is a slow sequence of `H^{1+ε}`: the entry of the
subcritical rules of `FibreSub.lean`. -/
lemma slowHs_nrm {ε : ℝ} (hf : MZ (1 + ε) f) (hf' : PiS f = f) :
    SlowHs ε (nrm f) (hnorm (1 + ε) f) := by
  have e : ∀ k, (absk k ^ (1 + ε) * nrm f k) ^ 2 = sobWeight (1 + ε) k * ‖f k‖ ^ 2 := fun k => by
    by_cases hk : k = 0
    · simp [hk, nrm, hf.mean, sobWeight]
    · have h : (absk k ^ (1 + ε)) ^ 2 = absk k ^ (2 * (1 + ε)) := by
        rw [mul_comm 2, Real.rpow_mul (absk_nonneg k), Real.rpow_two]
      simp only [sobWeight, hk, ite_false, mul_pow, h, nrm]
  refine ⟨fun _ => norm_nonneg _, fun p hp => ?_, ?_, ?_⟩
  · simp only [nrm]
    rw [slow_zero hf' hp, norm_zero]
  · simp only [nrm]
    rw [hf.mean, norm_zero]
  · refine ⟨fun k => mul_nonneg (Real.rpow_nonneg (absk_nonneg k) _) (norm_nonneg _), ?_, ?_⟩
    · simp only [e]
      exact hf.inH
    · simp only [e, hnorm]
      exact le_rfl

/-- The ordinary forms: `2 · 30 a a' + 2 c₄ (a W' + a' W)`. -/
lemma sb_kerO (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2) (hf : MZ 2 f)
    (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g) :
    SB (fun x : I3 => ‖G x.1‖ * ‖F (inJ₂ x)‖ * kerO f g x) (l2n G * l2n F *
      (60 * (hnorm 1 f * hnorm 1 g) + 2 * c4 * (hnorm 1 f * wiener g + hnorm 1 g * wiener f))) := by
  have hα := l2B_nrm hG
  have hβ := l2B_nrm hF
  have h1 := slowH1_nrm hf hf'
  have h2 := slowH1_nrm hg hg'
  have g1 : L2B (gr f) (hnorm 1 f) := h1.grad
  have g2 : L2B (gr g) (hnorm 1 g) := h2.grad
  have W1 := l1B_nrm hf.inH
  have W2 := l1B_nrm hg.inH
  have t1 := pos2_base hα hβ h1 h2
  have t2 := pos2_base' hα hβ h1 h2
  have t3 := pos2_II' hα hβ.in2 g1 W2
  have t4 : SB (Phi₂ (nrm G) (in2 (nrm F)) (nrm f) (gr g)) _ :=
    SB.equiv swapL (pos2_II' hα hβ.in2 g2 W1) (Phi₂_swapL _ _ _ _)
  have t5 := pos2_II hα.in2 hβ g1 W2
  have t6 : SB (Phi₂ (in2 (nrm G)) (nrm F) (nrm f) (gr g)) _ :=
    SB.equiv swapL (pos2_II hα.in2 hβ g2 W1) (Phi₂_swapL _ _ _ _)
  have h := (((((t1.add t2).add t3).add t4).add t5).add t6)
  have e : (fun x : I3 => ‖G x.1‖ * ‖F (inJ₂ x)‖ * kerO f g x) = fun x =>
      Phi₂ (nrm G) (in1 (nrm F)) (nrm f) (nrm g) x + Phi₂ (in1 (nrm G)) (nrm F) (nrm f) (nrm g) x +
        Phi₂ (nrm G) (in2 (nrm F)) (gr f) (nrm g) x + Phi₂ (nrm G) (in2 (nrm F)) (nrm f) (gr g) x +
        Phi₂ (in2 (nrm G)) (nrm F) (gr f) (nrm g) x +
        Phi₂ (in2 (nrm G)) (nrm F) (nrm f) (gr g) x := by
    funext x
    simp only [Phi₂, in1, in2, nrm, kerO, div_eq_mul_inv]
    ring
  rw [e]
  refine h.mono_bd (le_of_eq ?_)
  ring

/-- The band forms. -/
lemma sb_kerB {D : ℝ} (hD : 1 ≤ D) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hf : MZ 2 f) (hf' : PiS f = f) (hg : MZ 2 g)
    (hg' : PiS g = g) :
    SB (fun x : I3 => ‖G x.1‖ * ‖F (inJ₂ x)‖ * kerB D f g x) (l2n G * l2n F *
      (10 * Real.sqrt (9 + 8 * Real.log D) * (hnorm 1 f * hnorm 1 g))) := by
  have hα := l2B_nrm hG
  have hβ := l2B_nrm hF
  have h1 := slowH1_nrm hf hf'
  have h2 := slowH1_nrm hg hg'
  have g1 : L2B (gr f) (hnorm 1 f) := h1.grad
  have g2 : L2B (gr g) (hnorm 1 g) := h2.grad
  have s1 : ∀ p : Mode, p 2 ≠ 0 → gr f p = 0 := fun p hp => by
    simp only [gr]
    rw [slow_zero hf' hp, norm_zero, mul_zero]
  have s2 : ∀ p : Mode, p 2 ≠ 0 → gr g p = 0 := fun p hp => by
    simp only [gr]
    rw [slow_zero hg' hp, norm_zero, mul_zero]
  have t1 := pos2_band hD hα hβ g1 g2 s1 s2
  have t2 := pos2_band' hD hα hβ g1 g2 s1 s2
  have h := t1.add t2
  have e : (fun x : I3 => ‖G x.1‖ * ‖F (inJ₂ x)‖ * kerB D f g x) = fun x =>
      Phi₂ (in2 (nrm G)) (band D (nrm F)) (gr f) (gr g) x +
        Phi₂ (band D (nrm G)) (in2 (nrm F)) (gr f) (gr g) x := by
    funext x
    simp only [Phi₂, band, in2, nrm, kerB, div_eq_mul_inv]
    ring
  rw [e]
  refine h.mono_bd (le_of_eq ?_)
  ring

/-- The form with two weighted leaves and two inverse squares. -/
lemma sb_kerQ {U : ℝ} (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hf : L2B (gr f) U) (hg : InH 2 g) :
    SB (fun x : I3 => ‖G x.1‖ * ‖F (inJ₂ x)‖ * kerQ f g x)
      (c4 ^ 2 * (l2n G * l2n F) * (U * hnorm 2 g)) := by
  have h := pos2_III (l2B_nrm hG).in2 (l2B_nrm hF).in2 hf (l2B_up hg)
  have e : (fun x : I3 => ‖G x.1‖ * ‖F (inJ₂ x)‖ * kerQ f g x) =
      Phi₂ (in2 (nrm G)) (in2 (nrm F)) (gr f) (up (nrm g)) := by
    funext x
    simp only [Phi₂, in2, nrm, kerQ, div_eq_mul_inv]
    ring
  rw [e]
  exact SB.mono_bd h (le_of_eq (by ring))

/-- `‖P_{>R} f‖₁ ≤ ‖f‖₂ / R`: "One `H¹` tail is at most `C b/D`". -/
lemma l2B_gr_hiP {R : ℝ} (hR : 0 < R) (hf : InH 2 f) : L2B (gr (hiP R f)) (hnorm 2 f / R) := by
  have hR2 : 0 < R ^ 2 := by positivity
  have hpt : ∀ k, gr (hiP R f) k ^ 2 ≤ (1 / R ^ 2) * (sobWeight 2 k * ‖f k‖ ^ 2) := fun k => by
    rw [sobWeight_two, gr, mul_pow, absk_sq]
    by_cases hk : R < absk k
    · rw [hiP_of_lt f hk]
      have hsq : R ^ 2 ≤ absSq k := by
        rw [← absk_sq k]
        exact pow_le_pow_left₀ hR.le hk.le 2
      have hA : 0 ≤ absSq k := absSq_nonneg k
      have hn : 0 ≤ ‖f k‖ ^ 2 := sq_nonneg _
      have h1 : absSq k * ‖f k‖ ^ 2 * R ^ 2 ≤ absSq k * ‖f k‖ ^ 2 * absSq k :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      calc absSq k * ‖f k‖ ^ 2 = absSq k * ‖f k‖ ^ 2 * R ^ 2 * (1 / R ^ 2) := by
            field_simp
        _ ≤ absSq k * ‖f k‖ ^ 2 * absSq k * (1 / R ^ 2) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := by ring
    · rw [hiP_of_le f hk, norm_zero]
      have : 0 ≤ (1 / R ^ 2) * (absSq k ^ 2 * ‖f k‖ ^ 2) := by positivity
      simpa using this
  have hs : Summable fun k => (1 / R ^ 2) * (sobWeight 2 k * ‖f k‖ ^ 2) := hf.mul_left _
  have hs' : Summable fun k => gr (hiP R f) k ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hpt hs
  refine ⟨gr_nonneg _, hs', ?_⟩
  have h0 : 0 ≤ ∑' k, sobWeight 2 k * ‖f k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg 2 k) (sq_nonneg _)
  refine Real.sqrt_le_iff.2 ⟨by have := hnorm_nonneg 2 f; positivity, ?_⟩
  calc ∑' k, gr (hiP R f) k ^ 2 ≤ ∑' k, (1 / R ^ 2) * (sobWeight 2 k * ‖f k‖ ^ 2) :=
        hs'.tsum_le_tsum hpt hs
    _ = (1 / R ^ 2) * hnorm 2 f ^ 2 := by
        rw [tsum_mul_left, hnorm, Real.sq_sqrt h0]
    _ = _ := by
        rw [div_pow]
        ring

/-! ### B. The form -/

/-- The summand of an `X₂` form at any weight, against a block bound on the actual support. -/
lemma norm_X2s_summand_le {s : ℕ} {r τ : ℝ} (hf : PiS f = f) (hg : PiS g = g) (hF : PiF F = F)
    {B : I3 → ℝ} (hB0 : ∀ x, 0 ≤ B x)
    (hB : ∀ x : I3, x.2.1 2 = 0 → x.2.2 2 = 0 → inJ₂ x 2 ≠ 0 →
      ‖X2b s r τ f g x.1 x.2.1 x.2.2‖ ≤ B x) (c : ℂ) (x : I3) :
    ‖c * inner ℂ (G x.1) (X2b s r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))‖ ≤
      ‖c‖ * (‖G x.1‖ * ‖F (inJ₂ x)‖ * B x) := by
  have hR : 0 ≤ ‖c‖ * (‖G x.1‖ * ‖F (inJ₂ x)‖ * B x) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (by positivity) (hB0 x))
  have hzero : ∀ (hb0 : X2b s r τ f g x.1 x.2.1 x.2.2 = 0),
      ‖c * inner ℂ (G x.1) (X2b s r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))‖ ≤
        ‖c‖ * (‖G x.1‖ * ‖F (inJ₂ x)‖ * B x) := fun hb0 => by
    simpa [hb0] using hR
  by_cases ha : x.2.1 2 = 0
  swap
  · exact hzero (X2b_eq_zero (Or.inl (slow_zero hf ha)))
  by_cases hb : x.2.2 2 = 0
  swap
  · exact hzero (X2b_eq_zero (Or.inr (slow_zero hg hb)))
  by_cases hj : inJ₂ x 2 = 0
  · have : F (inJ₂ x) = 0 := fast_zero hF hj
    have h0 : F (x.1 - x.2.1 - x.2.2) = 0 := this
    simpa [h0, map_zero] using hR
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_inner_apply_le _ _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (hB x ha hb hj) (by positivity)

/-- The constant of the static bound. -/
def Cst : ℝ := 2 ^ 25 * (1 + c4) ^ 2

lemma Cst_eq : Cst = 2 ^ 25 * (1 + c4) ^ 2 := rfl

lemma sqrt_log_le {D : ℝ} (hD : 1 ≤ D) :
    Real.sqrt (9 + 8 * Real.log D) ≤ 3 * Real.sqrt (1 + Real.log D) := by
  have hl := Real.log_nonneg hD
  have e : (3 : ℝ) = Real.sqrt (3 ^ 2) := by
    rw [Real.sqrt_sq (by norm_num)]
  rw [e, ← Real.sqrt_mul (by norm_num)]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- The arithmetic of the static bound. -/
private lemma static_arith {q D a₁ a₂ W₁ W₂ b₁ b₂ S Sl GF C4 Y : ℝ} (hq : 0 < q) (hD : 1 ≤ D)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hS : 0 ≤ S) (hSl : Sl ≤ 3 * S) (hGF : 0 ≤ GF) (hc : 0 ≤ C4) (hY1 : 1 ≤ Y) (hY2 : C4 ≤ Y)
    (hY3 : C4 ^ 2 ≤ Y) :
    2 ^ 18 / q * (GF * (60 * (a₁ * a₂) + 2 * C4 * (a₁ * W₂ + a₂ * W₁))) +
      2 ^ 16 / q * (GF * (10 * Sl * (a₁ * a₂))) +
      2 ^ 15 / q * (C4 ^ 2 * GF * (b₁ / (3 / 4 * D) * b₂)) +
      2 ^ 17 * D / q ^ 2 * (C4 ^ 2 * GF * (a₁ * b₂)) ≤
    2 ^ 25 * Y / q * ((1 + S) * (a₁ * a₂) + a₁ * W₂ + a₂ * W₁ + b₁ * b₂ / D) * GF +
      2 ^ 25 * Y / q ^ 2 * D * (a₁ * b₂) * GF := by
  have hD0 : 0 < D := by linarith
  have i1 : 0 ≤ GF / q := by positivity
  have p1 : 0 ≤ a₁ * a₂ * (GF / q) := by positivity
  have p2 : 0 ≤ S * (a₁ * a₂) * (GF / q) := by positivity
  have p3 : 0 ≤ a₁ * W₂ * (GF / q) := by positivity
  have p4 : 0 ≤ a₂ * W₁ * (GF / q) := by positivity
  have p5 : 0 ≤ b₁ * b₂ / D * (GF / q) := by positivity
  have p6 : 0 ≤ D * (a₁ * b₂) * (GF / q ^ 2) := by positivity
  have e1 : 2 ^ 18 / q * (GF * (60 * (a₁ * a₂) + 2 * C4 * (a₁ * W₂ + a₂ * W₁))) =
      2 ^ 18 * 60 * (a₁ * a₂ * (GF / q)) + 2 ^ 19 * C4 * (a₁ * W₂ * (GF / q)) +
        2 ^ 19 * C4 * (a₂ * W₁ * (GF / q)) := by ring
  have e2 : 2 ^ 16 / q * (GF * (10 * Sl * (a₁ * a₂))) =
      2 ^ 16 * 10 * (Sl * ((a₁ * a₂) * (GF / q))) := by ring
  have e3 : 2 ^ 15 / q * (C4 ^ 2 * GF * (b₁ / (3 / 4 * D) * b₂)) =
      2 ^ 15 * (4 / 3) * C4 ^ 2 * (b₁ * b₂ / D * (GF / q)) := by
    field_simp
  have e4 : 2 ^ 17 * D / q ^ 2 * (C4 ^ 2 * GF * (a₁ * b₂)) =
      2 ^ 17 * C4 ^ 2 * (D * (a₁ * b₂) * (GF / q ^ 2)) := by ring
  have e5 : 2 ^ 25 * Y / q * ((1 + S) * (a₁ * a₂) + a₁ * W₂ + a₂ * W₁ + b₁ * b₂ / D) * GF +
      2 ^ 25 * Y / q ^ 2 * D * (a₁ * b₂) * GF =
      2 ^ 25 * Y * (a₁ * a₂ * (GF / q)) + 2 ^ 25 * Y * (S * (a₁ * a₂) * (GF / q)) +
        2 ^ 25 * Y * (a₁ * W₂ * (GF / q)) + 2 ^ 25 * Y * (a₂ * W₁ * (GF / q)) +
        2 ^ 25 * Y * (b₁ * b₂ / D * (GF / q)) + 2 ^ 25 * Y * (D * (a₁ * b₂) * (GF / q ^ 2)) := by
    ring
  have q1 : Sl * ((a₁ * a₂) * (GF / q)) ≤ 3 * (S * (a₁ * a₂) * (GF / q)) := by
    have := mul_le_mul_of_nonneg_right hSl p1
    linarith
  have hY0 : (2 : ℝ) ^ 25 ≤ 2 ^ 25 * Y := le_mul_of_one_le_right (by positivity) hY1
  have hC1 : (2 : ℝ) ^ 25 * C4 ≤ 2 ^ 25 * Y := mul_le_mul_of_nonneg_left hY2 (by positivity)
  have hC2 : (2 : ℝ) ^ 25 * C4 ^ 2 ≤ 2 ^ 25 * Y := mul_le_mul_of_nonneg_left hY3 (by positivity)
  have n1 : (2 : ℝ) ^ 19 * C4 ≤ 2 ^ 25 * C4 :=
    mul_le_mul_of_nonneg_right (by norm_num) hc
  have n2 : (2 : ℝ) ^ 15 * (4 / 3) * C4 ^ 2 ≤ 2 ^ 25 * C4 ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have n3 : (2 : ℝ) ^ 17 * C4 ^ 2 ≤ 2 ^ 25 * C4 ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  rw [e1, e2, e3, e4, e5]
  have k1 : (2 : ℝ) ^ 18 * 60 * (a₁ * a₂ * (GF / q)) ≤ 2 ^ 25 * Y * (a₁ * a₂ * (GF / q)) :=
    mul_le_mul_of_nonneg_right (le_trans (by norm_num) hY0) p1
  have k2 : (2 : ℝ) ^ 16 * 10 * (Sl * ((a₁ * a₂) * (GF / q))) ≤
      2 ^ 25 * Y * (S * (a₁ * a₂) * (GF / q)) := by
    have h1 := mul_le_mul_of_nonneg_left q1 (by norm_num : (0 : ℝ) ≤ 2 ^ 16 * 10)
    have h2 : (2 : ℝ) ^ 16 * 10 * 3 ≤ 2 ^ 25 * Y := le_trans (by norm_num) hY0
    have h3 := mul_le_mul_of_nonneg_right h2 p2
    linarith
  have k3 := mul_le_mul_of_nonneg_right (n1.trans hC1) p3
  have k4 := mul_le_mul_of_nonneg_right (n1.trans hC1) p4
  have k5 := mul_le_mul_of_nonneg_right (n2.trans hC2) p5
  have k6 := mul_le_mul_of_nonneg_right (n3.trans hC2) p6
  linarith

/-- **The static bound of `X₂`** (Body 36, check Body 74), at both weights, bilinear in the leaves,
for every multiplier of modulus at most one, with `D ≥ 1` free. -/
theorem X2Form_static_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ}
    (hD : 1 ≤ D) (hf : MZ 2 f) (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g)
    (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F)
    {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ 1) :
    ‖X2Form μ s r τ f g G F‖ ≤
      Cst / |r| * ((1 + Real.sqrt (1 + Real.log D)) * (hnorm 1 f * hnorm 1 g) +
          hnorm 1 f * wiener g + hnorm 1 g * wiener f + hnorm 2 f * hnorm 2 g / D) *
        (l2n G * l2n F) +
      Cst / |r| ^ 2 * D * (hnorm 1 f * hnorm 2 g) * (l2n G * l2n F) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hD0 : 0 < D := by linarith
  have hR : 0 < 3 / 4 * D := by positivity
  have hO := (sb_kerO hG hF hf hf' hg hg').const_mul (by positivity : (0 : ℝ) ≤ 2 ^ 18 / |r|)
  have hB := (sb_kerB hD hG hF hf hf' hg hg').const_mul (by positivity : (0 : ℝ) ≤ 2 ^ 16 / |r|)
  have hT := (sb_kerQ hG hF (l2B_gr_hiP hR hf.inH) hg.inH).const_mul
    (by positivity : (0 : ℝ) ≤ 2 ^ 15 / |r|)
  have hQ := (sb_kerQ hG hF (slowH1_nrm hf hf').grad hg.inH).const_mul
    (by positivity : (0 : ℝ) ≤ 2 ^ 17 * |D| / |r| ^ 2)
  have hΨ := ((hO.add hB).add hT).add hQ
  have hker0 : ∀ x : I3, 0 ≤ 2 ^ 18 / |r| * kerO f g x + 2 ^ 16 / |r| * kerB D f g x +
      2 ^ 15 / |r| * kerT (3 / 4 * D) f g x + 2 ^ 17 * |D| / |r| ^ 2 * kerQ f g x := fun x => by
    have h1 := kerO_nonneg f g x
    have h2 := kerB_nonneg D f g x
    have h3 := kerT_nonneg (3 / 4 * D) f g x
    have h4 := kerQ_nonneg f g x
    positivity
  have hle : ∀ x : I3, ‖μ x * inner ℂ (G x.1) (X2b s r τ f g x.1 x.2.1 x.2.2
      (F (x.1 - x.2.1 - x.2.2)))‖ ≤
      2 ^ 18 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * kerO f g x) +
      2 ^ 16 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * kerB D f g x) +
      2 ^ 15 / |r| * (‖G x.1‖ * ‖F (inJ₂ x)‖ * kerQ (hiP (3 / 4 * D) f) g x) +
      2 ^ 17 * |D| / |r| ^ 2 * (‖G x.1‖ * ‖F (inJ₂ x)‖ * kerQ f g x) := fun x => by
    refine (norm_X2s_summand_le hf' hg' hF' hker0 (fun x ha hb hj =>
      norm_X2b_kernel hs hr τ D f g ha hb hj) _ x).trans ?_
    have h5 := hker0 x
    have h6 := mul_le_mul_of_nonneg_right (hμ x) (mul_nonneg (mul_nonneg (norm_nonneg (G x.1))
      (norm_nonneg (F (inJ₂ x)))) h5)
    refine h6.trans (le_of_eq ?_)
    simp only [kerT]
    ring
  refine (form_le hΨ hle).2.trans ?_
  rw [abs_of_pos hD0, Cst_eq]
  have hSl := sqrt_log_le hD
  have h1 := hnorm_nonneg 1 f
  have h2 := hnorm_nonneg 1 g
  have h3 := hnorm_nonneg 2 f
  have h4 := hnorm_nonneg 2 g
  have h5 : 0 ≤ wiener f := tsum_nonneg fun _ => norm_nonneg _
  have h6 : 0 ≤ wiener g := tsum_nonneg fun _ => norm_nonneg _
  have h7 := Real.sqrt_nonneg (1 + Real.log D)
  have h8 := mul_nonneg (l2n_nonneg G) (l2n_nonneg F)
  have hc := c4_pos
  have := static_arith (a₁ := hnorm 1 f) (a₂ := hnorm 1 g) (W₁ := wiener f) (W₂ := wiener g)
    (b₁ := hnorm 2 f) (b₂ := hnorm 2 g) (Y := (1 + c4) ^ 2) hq hD h1 h2 h5 h6 h3 h4 h7 hSl h8
    hc.le (by nlinarith) (by nlinarith) (by nlinarith)
  refine le_trans (le_of_eq ?_) this
  ring

/-- **The static bound on the diagonal**: `‖X₂(S)‖ ≤ (C/q)[(1 + √(1 + ln D)) a² + 2 a W + b²/D]
+ (C/q²) D a b`, Body 36's display. -/
theorem X2Form_static_diag {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ}
    (hD : 1 ≤ D) {S : Field} (hS : MZ 2 S) (hS' : PiS S = S)
    (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) :
    ‖X2Form 1 s r τ S S G F‖ ≤
      Cst / |r| * ((1 + Real.sqrt (1 + Real.log D)) * hnorm 1 S ^ 2 +
          2 * hnorm 1 S * wiener S + hnorm 2 S ^ 2 / D) * (l2n G * l2n F) +
      Cst / |r| ^ 2 * D * (hnorm 1 S * hnorm 2 S) * (l2n G * l2n F) := by
  refine (X2Form_static_le hs hr τ hD hS hS' hS hS' hG hF hF' (μ := 1)
    fun _ => by simp).trans (le_of_eq ?_)
  ring

end OVNS.Quant.Metric

end
