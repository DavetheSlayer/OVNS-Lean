import OddViscousNS.Quant.Joint.Metric.HighAncestor
import OddViscousNS.Quant.Joint.Metric.SignedBlock
import OddViscousNS.Quant.Joint.Metric.FibreForms
import OddViscousNS.Quant.Joint.Metric.Ordinary

/-!
# The static bound of `X₂` (step J5, node N3)

Body 36 (LOCAL515, check Body 74), "Exact static X2 operator at both original weights":
`‖X₂‖ ≤ C q⁻¹ [(1 + √(1 + ln D)) a² + a W + b²/D] + C q⁻² D a b`, at `s = 1, 2`, with `a = ‖S‖₁`,
`W = ‖Ŝ‖_{ℓ¹}`, `b = ‖S‖₂`, `q = |r|`, and `D ≥ 1` free (`X2Form_static_le`).  This is the first
term of the static row tied at `Q` (`U(a² + aW + b²/D)`, role 28 at `D = R`), and the `X₂` part
of the coercivity in `H1EnergyJoint` and of the `31/32`, `33/32` of `H2Output`.

## The three sectors
`norm_X2b_kernel` is one pointwise bound on the block, by the three sectors of Body 36:
* `M < 4 max(L, J)`, ordinary: `norm_X2b_le`, `ord_bracket_le`; `kerO`.
* `M ≥ 4 max(L, J)`, `M ≤ D`: `norm_X2b_signed_le`, the phase and noncommon part `kerB`, in the band
  `L, J ≤ D`, and the heat part `kerQ`.
* `M ≥ 4 max(L, J)`, `M > D`: no cancellation; `high_bracket_le`, with a slow tail: `kerT`.

Everything after the block is positive.  In particular the bound holds **for every multiplier `μ`
of modulus at most one**: a mask needs no new argument.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. The kernels -/

/-- The ordinary kernel: `f_a g_b (1/J + 1/L) + (P₁ f_a g_b + f_a P₂ g_b)(1/J² + 1/L²)`. -/
def kerO (f g : Field) (x : I3) : ℝ :=
  ‖f x.2.1‖ * ‖g x.2.2‖ * ((absk (inJ₂ x))⁻¹ + (absk x.1)⁻¹) +
    (gr f x.2.1 * ‖g x.2.2‖ + ‖f x.2.1‖ * gr g x.2.2) * ((absSq (inJ₂ x))⁻¹ + (absSq x.1)⁻¹)

/-- The phase and noncommon kernel in the band: `P₁ f_a P₂ g_b (1/(L J²) + 1/(L² J))`,
`L, J ≤ D`. -/
def kerB (D : ℝ) (f g : Field) (x : I3) : ℝ :=
  gr f x.2.1 * gr g x.2.2 *
    (bandW D x.1 * (absSq (inJ₂ x))⁻¹ + (absSq x.1)⁻¹ * bandW D (inJ₂ x))

/-- The kernel `P₁ f_a P₂² g_b /(L²J²)`, with `f` free. -/
def kerQ (f g : Field) (x : I3) : ℝ :=
  gr f x.2.1 * up (nrm g) x.2.2 * ((absSq x.1)⁻¹ * (absSq (inJ₂ x))⁻¹)

lemma gr_nonneg (h : Field) (a : Mode) : 0 ≤ gr h a := mul_nonneg (absk_nonneg a) (norm_nonneg _)

lemma up_nrm_nonneg (h : Field) (a : Mode) : 0 ≤ up (nrm h) a :=
  mul_nonneg (absSq_nonneg a) (norm_nonneg _)

lemma kerO_nonneg (f g : Field) (x : I3) : 0 ≤ kerO f g x := by
  have h1 := gr_nonneg f x.2.1
  have h2 := gr_nonneg g x.2.2
  have h3 := absSq_nonneg x.1
  have h4 := absSq_nonneg (inJ₂ x)
  have h5 := absk_nonneg x.1
  have h6 := absk_nonneg (inJ₂ x)
  unfold kerO
  positivity

lemma kerB_nonneg (D : ℝ) (f g : Field) (x : I3) : 0 ≤ kerB D f g x := by
  have h1 := gr_nonneg f x.2.1
  have h2 := gr_nonneg g x.2.2
  have h3 := absSq_nonneg x.1
  have h4 := absSq_nonneg (inJ₂ x)
  have h5 := bandW_nonneg D x.1
  have h6 := bandW_nonneg D (inJ₂ x)
  unfold kerB
  positivity

lemma kerQ_nonneg (f g : Field) (x : I3) : 0 ≤ kerQ f g x := by
  have h1 := gr_nonneg f x.2.1
  have h2 := up_nrm_nonneg g x.2.2
  have h3 := absSq_nonneg x.1
  have h4 := absSq_nonneg (inJ₂ x)
  unfold kerQ
  positivity

/-- The paths of a two-leaf block, in the lengths. -/
lemma two_leaf_paths (l a b : Mode) :
    absk (l - a) ≤ absk l + absk a ∧ absk (l - a) ≤ absk (l - a - b) + absk b ∧
      absk l ≤ absk (l - a - b) + absk a + absk b ∧
      absk (l - a - b) ≤ absk l + absk a + absk b := by
  have h1 := absk_sub_le l a
  have h2 : absk (l - a) ≤ absk (l - a - b) + absk b := by
    have := absk_add_le (l - a - b) b
    rwa [show l - a - b + b = l - a by abel] at this
  have h3 := absk_add_le (l - a) a
  rw [show l - a + a = l by abel] at h3
  have h4 := absk_sub_le (l - a) b
  exact ⟨h1, h2, by linarith, by linarith⟩

/-- `heat4` in the lengths. -/
lemma heat4_eq (l j a b : Mode) :
    heat4 l j a b = absk l ^ 2 + absk j ^ 2 + absk a ^ 2 + absk b ^ 2 := by
  simp only [heat4, absk_sq]

/-- **The ordinary sector of the block.** -/
theorem norm_X2b_ord_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field)
    {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0)
    (hM : absk (l - a) ≤ 4 * absk l ∨ absk (l - a) ≤ 4 * absk (l - a - b)) :
    ‖X2b s r τ f g l a b‖ ≤ 2 ^ 18 / |r| * kerO f g (l, a, b) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hL : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hJ : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  obtain ⟨p1, p2, p3, p4⟩ := two_leaf_paths l a b
  have hB := ord_bracket_le hL hJ (absk_nonneg (l - a)) (absk_nonneg a) (absk_nonneg b) p1 p2 p3
    p4 hM
  rw [← heat4_eq l (l - a - b) a b] at hB
  have hff := norm_nonneg (f a)
  have hgg := norm_nonneg (g b)
  have hfg : 0 ≤ ‖f a‖ * ‖g b‖ := by positivity
  have hK : 0 ≤ 2816 / |r| * (‖f a‖ * ‖g b‖) := by positivity
  refine (norm_X2b_le hs hr τ f g ha hb hj).trans ?_
  set J := absk (l - a - b)
  set L := absk l
  set Pa := absk a
  set Pb := absk b
  have hPa0 : 0 ≤ Pa := absk_nonneg a
  have hPb0 : 0 ≤ Pb := absk_nonneg b
  have e : kerO f g (l, a, b) = (‖f a‖ * ‖g b‖) *
      (1 / J + 1 / L + (Pa + Pb) / J ^ 2 + (Pa + Pb) / L ^ 2) := by
    simp only [kerO, gr, inJ₂, ← absk_sq]
    change ‖f a‖ * ‖g b‖ * (J⁻¹ + L⁻¹) +
      (Pa * ‖f a‖ * ‖g b‖ + ‖f a‖ * (Pb * ‖g b‖)) * ((J ^ 2)⁻¹ + (L ^ 2)⁻¹) = _
    simp only [div_eq_mul_inv]
    ring
  rw [e]
  calc 2816 / |r| * (absk (l - a) / heat4 l (l - a - b) a b) * (‖f a‖ * ‖g b‖) *
        Br (L ^ 2) (absk (l - a) ^ 2) (J ^ 2)
      = 2816 / |r| * (‖f a‖ * ‖g b‖) * (absk (l - a) / heat4 l (l - a - b) a b *
          Br (L ^ 2) (absk (l - a) ^ 2) (J ^ 2)) := by ring
    _ ≤ 2816 / |r| * (‖f a‖ * ‖g b‖) *
          (68 * (1 / J + 1 / L + (Pa + Pb) / J ^ 2 + (Pa + Pb) / L ^ 2)) :=
        mul_le_mul_of_nonneg_left hB hK
    _ = 191488 * (1 / |r| * ((‖f a‖ * ‖g b‖) *
          (1 / J + 1 / L + (Pa + Pb) / J ^ 2 + (Pa + Pb) / L ^ 2))) := by ring
    _ ≤ 2 ^ 18 * (1 / |r| * ((‖f a‖ * ‖g b‖) *
          (1 / J + 1 / L + (Pa + Pb) / J ^ 2 + (Pa + Pb) / L ^ 2))) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

/-! ### B. The large intermediate -/

/-- The ancestors at a large intermediate are comparable to `M`. -/
lemma leaves_ge {l a b : Mode} (hL : 4 * absk l ≤ absk (l - a))
    (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) :
    3 / 4 * absk (l - a) ≤ absk a ∧ 3 / 4 * absk (l - a) ≤ absk b := by
  obtain ⟨p1, p2, -, -⟩ := two_leaf_paths l a b
  constructor <;> linarith

/-- The arithmetic of the band: the two parts of `norm_X2b_signed_le`. -/
private lemma band_arith {L J M Pa Pb ff gg q D : ℝ} (hL : 0 < L) (hJ : 0 < J) (hM : 0 < M)
    (hff : 0 ≤ ff) (hgg : 0 ≤ gg) (hq : 0 < q) (h1 : 3 / 4 * M ≤ Pa) (h2 : 3 / 4 * M ≤ Pb)
    (hD : M ≤ D) :
    2 ^ 15 * ((M / L) ^ 2 * (M / J) ^ 2) * (ff * gg) * (1 / q ^ 2 + (L + J) / (q * M ^ 2)) ≤
      2 ^ 16 / q * (Pa * ff * (Pb * gg) * (L⁻¹ * (J ^ 2)⁻¹ + (L ^ 2)⁻¹ * J⁻¹)) +
        2 ^ 17 * D / q ^ 2 * (Pa * ff * (Pb ^ 2 * gg) * ((L ^ 2)⁻¹ * (J ^ 2)⁻¹)) := by
  have hPa : 0 ≤ Pa := le_trans (by positivity) h1
  have hPb : 0 ≤ Pb := le_trans (by positivity) h2
  set A := (L ^ 2)⁻¹ * (J ^ 2)⁻¹ with hA
  have hA0 : 0 < A := by positivity
  have hξ : 0 ≤ ff * gg := by positivity
  have e1 : (M / L) ^ 2 * (M / J) ^ 2 * (1 / q ^ 2) = M ^ 4 * A * (1 / q ^ 2) := by
    simp only [hA]
    field_simp
  have e2 : (M / L) ^ 2 * (M / J) ^ 2 * ((L + J) / (q * M ^ 2)) = M ^ 2 * ((L + J) * A) / q := by
    simp only [hA]
    field_simp
  have e3 : L⁻¹ * (J ^ 2)⁻¹ + (L ^ 2)⁻¹ * J⁻¹ = (L + J) * A := by
    simp only [hA]
    field_simp
  have a1 : M ^ 2 ≤ 16 / 9 * (Pa * Pb) := by
    have := mul_le_mul h1 h2 (by positivity) hPa
    nlinarith
  have a2 : M ^ 3 ≤ 4 * (Pa * Pb ^ 2) := by
    have h3 := mul_le_mul h1 (pow_le_pow_left₀ (by positivity) h2 2) (by positivity) hPa
    nlinarith [pow_pos hM 3]
  have a3 : M ^ 4 ≤ D * (4 * (Pa * Pb ^ 2)) := by
    calc M ^ 4 = M * M ^ 3 := by ring
      _ ≤ D * (4 * (Pa * Pb ^ 2)) := mul_le_mul hD a2 (by positivity) (by linarith)
  have hS : 0 ≤ L + J := by positivity
  rw [e3]
  calc 2 ^ 15 * ((M / L) ^ 2 * (M / J) ^ 2) * (ff * gg) * (1 / q ^ 2 + (L + J) / (q * M ^ 2))
      = 2 ^ 15 * (ff * gg) * (M ^ 4 * A * (1 / q ^ 2)) +
        2 ^ 15 * (ff * gg) * (M ^ 2 * ((L + J) * A) / q) := by
        rw [← e1, ← e2]
        ring
    _ ≤ 2 ^ 15 * (ff * gg) * ((D * (4 * (Pa * Pb ^ 2))) * A * (1 / q ^ 2)) +
        2 ^ 15 * (ff * gg) * ((16 / 9 * (Pa * Pb)) * ((L + J) * A) / q) := by
        gcongr
    _ ≤ _ := by
        have h5 : 0 ≤ (Pa * Pb) * (ff * gg) * ((L + J) * A) / q := by positivity
        have e4 : 2 ^ 16 / q * (Pa * ff * (Pb * gg) * ((L + J) * A)) =
            2 ^ 16 * ((Pa * Pb) * (ff * gg) * ((L + J) * A) / q) := by ring
        have e5 : (2 : ℝ) ^ 15 * (ff * gg) * ((16 / 9 * (Pa * Pb)) * ((L + J) * A) / q) =
            2 ^ 15 * (16 / 9) * ((Pa * Pb) * (ff * gg) * ((L + J) * A) / q) := by ring
        have e6 : (2 : ℝ) ^ 15 * (ff * gg) * ((D * (4 * (Pa * Pb ^ 2))) * A * (1 / q ^ 2)) =
            2 ^ 17 * D / q ^ 2 * (Pa * ff * (Pb ^ 2 * gg) * A) := by ring
        rw [e4, e5, e6]
        have h6 : (2 : ℝ) ^ 15 * (16 / 9) ≤ 2 ^ 16 := by norm_num
        have := mul_le_mul_of_nonneg_right h6 h5
        linarith

/-- **The high intermediate at `M ≤ D`** (Body 36: phase and noncommon in the band, plus the heat
part). -/
theorem norm_X2b_band_le {s : ℕ} (hs : s ≤ 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field)
    {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0)
    (hL : 4 * absk l ≤ absk (l - a)) (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) {D : ℝ}
    (hD : absk (l - a) ≤ D) :
    ‖X2b s r τ f g l a b‖ ≤ 2 ^ 16 / |r| * kerB D f g (l, a, b) +
      2 ^ 17 * D / |r| ^ 2 * kerQ f g (l, a, b) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hr0 : 0 < |r| := abs_pos.2 hr
  have h0L : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have h0J : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have h0M : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  obtain ⟨hPa, hPb⟩ := leaves_ge hL hJ
  have hbL : bandW D l = (absk l)⁻¹ := by
    rw [bandW, ite_eq_left (by linarith)]
  have hbJ : bandW D (l - a - b) = (absk (l - a - b))⁻¹ := by
    rw [bandW, ite_eq_left (by linarith)]
  refine (norm_X2b_signed_le hs hr τ f g ha hb hj hL hJ).trans ?_
  refine (band_arith h0L h0J h0M (norm_nonneg (f a)) (norm_nonneg (g b)) hr0 hPa hPb hD).trans
    (le_of_eq ?_)
  have eB : kerB D f g (l, a, b) = absk a * ‖f a‖ * (absk b * ‖g b‖) *
      ((absk l)⁻¹ * (absk (l - a - b) ^ 2)⁻¹ + (absk l ^ 2)⁻¹ * (absk (l - a - b))⁻¹) := by
    simp only [kerB, gr, inJ₂, ← absk_sq]
    rw [hbL, hbJ]
  have eQ : kerQ f g (l, a, b) = absk a * ‖f a‖ * (absk b ^ 2 * ‖g b‖) *
      ((absk l ^ 2)⁻¹ * (absk (l - a - b) ^ 2)⁻¹) := by
    simp only [kerQ, gr, up, nrm, inJ₂, ← absk_sq]
  rw [eB, eQ]

/-- The tail of the first leaf at a length. -/
def kerT (R : ℝ) (f g : Field) : I3 → ℝ := kerQ (hiP R f) g

lemma kerT_nonneg (R : ℝ) (f g : Field) (x : I3) : 0 ≤ kerT R f g x := kerQ_nonneg _ _ _

/-- The arithmetic of the high sector. -/
private lemma high_arith {L J M Pa Pb ff gg q : ℝ} (hM : 0 < M) (hL : 0 < L) (hJ : 0 < J)
    (hff : 0 ≤ ff) (hgg : 0 ≤ gg) (hq : 0 < q) (h1 : 3 / 4 * M ≤ Pa) (h2 : 3 / 4 * M ≤ Pb) :
    2816 / q * (ff * gg) * (32 / 9 * (M ^ 3 / (L ^ 2 * J ^ 2))) ≤
      2 ^ 15 / q * (Pa * ff * (Pb ^ 2 * gg) * ((L ^ 2)⁻¹ * (J ^ 2)⁻¹)) := by
  have hPa : 0 ≤ Pa := le_trans (by positivity) h1
  have hPb : 0 ≤ Pb := le_trans (by positivity) h2
  have a2 : M ^ 3 ≤ 64 / 27 * (Pa * Pb ^ 2) := by
    have h3 := mul_le_mul h1 (pow_le_pow_left₀ (by positivity) h2 2) (by positivity) hPa
    nlinarith
  have hA : 0 ≤ (L ^ 2)⁻¹ * (J ^ 2)⁻¹ := by positivity
  have e : M ^ 3 / (L ^ 2 * J ^ 2) = M ^ 3 * ((L ^ 2)⁻¹ * (J ^ 2)⁻¹) := by
    rw [div_eq_mul_inv, mul_inv]
  rw [e]
  have h3 := mul_le_mul_of_nonneg_right a2 hA
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity :
    0 ≤ 2816 / q * (ff * gg) * (32 / 9))
  have h5 : 0 ≤ 1 / q * (ff * gg) * (Pa * Pb ^ 2 * ((L ^ 2)⁻¹ * (J ^ 2)⁻¹)) := by positivity
  have h6 : (2816 : ℝ) * (32 / 9) * (64 / 27) ≤ 2 ^ 15 := by norm_num
  have h7 := mul_le_mul_of_nonneg_right h6 h5
  calc _ = 2816 / q * (ff * gg) * (32 / 9) * (M ^ 3 * ((L ^ 2)⁻¹ * (J ^ 2)⁻¹)) := by ring
    _ ≤ _ := h4
    _ = 2816 * (32 / 9) * (64 / 27) *
          (1 / q * (ff * gg) * (Pa * Pb ^ 2 * ((L ^ 2)⁻¹ * (J ^ 2)⁻¹))) := by
        ring
    _ ≤ _ := h7
    _ = _ := by ring

/-- **The high intermediate at `M > D`** (Body 36: "do not require the new cancellation"): both
leaves are above `(3/4) D`, and the first one pays the tail. -/
theorem norm_X2b_tail_le {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field)
    {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0)
    (hL : 4 * absk l ≤ absk (l - a)) (hJ : 4 * absk (l - a - b) ≤ absk (l - a)) {D : ℝ}
    (hD : D < absk (l - a)) :
    ‖X2b s r τ f g l a b‖ ≤ 2 ^ 15 / |r| * kerT (3 / 4 * D) f g (l, a, b) := by
  obtain ⟨hl0, hm0, hj0⟩ := fast_labels ha hb hj
  have hr0 : 0 < |r| := abs_pos.2 hr
  have h0L : 0 < absk l := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have h0J : 0 < absk (l - a - b) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have h0M : 0 < absk (l - a) := lt_of_lt_of_le one_pos (one_le_absk hm0)
  obtain ⟨hPa, hPb⟩ := leaves_ge hL hJ
  obtain ⟨-, -, -, hH4⟩ := high_heats hj0 hL hJ
  have hB := high_bracket_le h0L h0J h0M hL hJ hH4
  have hT : hiP (3 / 4 * D) f a = f a := hiP_of_lt f (by linarith)
  have hff := norm_nonneg (f a)
  have hgg := norm_nonneg (g b)
  have hK : 0 ≤ 2816 / |r| * (‖f a‖ * ‖g b‖) := by positivity
  refine (norm_X2b_le hs hr τ f g ha hb hj).trans ?_
  have hA := high_arith h0M h0L h0J hff hgg hr0 hPa hPb
  have eQ : kerT (3 / 4 * D) f g (l, a, b) = absk a * ‖f a‖ * (absk b ^ 2 * ‖g b‖) *
      ((absk l ^ 2)⁻¹ * (absk (l - a - b) ^ 2)⁻¹) := by
    simp only [kerT, kerQ, gr, up, nrm, inJ₂, ← absk_sq, hT]
  rw [eQ]
  refine le_trans ?_ hA
  have h1 := mul_le_mul_of_nonneg_left hB hK
  calc _ = 2816 / |r| * (‖f a‖ * ‖g b‖) * (absk (l - a) / heat4 l (l - a - b) a b *
        Br (absk l ^ 2) (absk (l - a) ^ 2) (absk (l - a - b) ^ 2)) := by ring
    _ ≤ _ := h1

/-- **The block**, in the three sectors of Body 36: one pointwise bound. -/
theorem norm_X2b_kernel {s : ℕ} (hs : s = 1 ∨ s = 2) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (D : ℝ)
    (f g : Field) {l a b : Mode} (ha : a 2 = 0) (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) :
    ‖X2b s r τ f g l a b‖ ≤ 2 ^ 18 / |r| * kerO f g (l, a, b) +
      2 ^ 16 / |r| * kerB D f g (l, a, b) + 2 ^ 15 / |r| * kerT (3 / 4 * D) f g (l, a, b) +
        2 ^ 17 * |D| / |r| ^ 2 * kerQ f g (l, a, b) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have h1 := kerO_nonneg f g (l, a, b)
  have h2 := kerB_nonneg D f g (l, a, b)
  have h3 := kerT_nonneg (3 / 4 * D) f g (l, a, b)
  have h4 := kerQ_nonneg f g (l, a, b)
  have p1 : 0 ≤ 2 ^ 18 / |r| * kerO f g (l, a, b) := by positivity
  have p2 : 0 ≤ 2 ^ 16 / |r| * kerB D f g (l, a, b) := by positivity
  have p3 : 0 ≤ 2 ^ 15 / |r| * kerT (3 / 4 * D) f g (l, a, b) := by positivity
  have p4 : 0 ≤ 2 ^ 17 * |D| / |r| ^ 2 * kerQ f g (l, a, b) := by positivity
  by_cases hL : 4 * absk l ≤ absk (l - a)
  · by_cases hJ : 4 * absk (l - a - b) ≤ absk (l - a)
    · by_cases hD : absk (l - a) ≤ D
      · have := norm_X2b_band_le (show s ≤ 2 by omega) hr τ f g ha hb hj hL hJ hD
        have e : 2 ^ 17 * D / |r| ^ 2 * kerQ f g (l, a, b) ≤
            2 ^ 17 * |D| / |r| ^ 2 * kerQ f g (l, a, b) := by
          gcongr
          exact le_abs_self D
        linarith
      · have := norm_X2b_tail_le hs hr τ f g ha hb hj hL hJ (not_le.1 hD)
        linarith
    · have := norm_X2b_ord_le hs hr τ f g ha hb hj (Or.inr (not_le.1 hJ).le)
      linarith
  · have := norm_X2b_ord_le hs hr τ f g ha hb hj (Or.inl (not_le.1 hL).le)
    linarith

end OVNS.Quant.Metric

end
