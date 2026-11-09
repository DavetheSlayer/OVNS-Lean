import OddViscousNS.Quant.Joint.Metric.One1Form
import OddViscousNS.Quant.Joint.Metric.Group2

/-!
# Weight one: the high last edge (step J5, node N10)

Unit: `TIMED_METRIC_PROOF_V2.md` §8.2, §8.3.
* `norm_YLb_sep_one`: on `muS`: (8.3): `q⁻² [(P₁ + P₂) P₃² + (P₁² + P₂²) P₃ + P₁² P₂]/(LJ)`;
* `norm_HB_one`: the heat of the comparable mask: `q⁻² P₁ P₂ P₃/(LJ)`, §8.3, with `P₃ ≍ K`;
* `norm_YLb_hi`: on `K ≥ J`, weight one is below weight two, so a high ancestor is paid as there.

The mask has ancestors at most `D`, so every label is at most `4D`, and `pos3_band2` pays both
inverse-first exteriors.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {D : ℝ} {x : I4}

/-- The lengths on the masks of the high last edge. -/
lemma last_lengths (hgt : 16 * absk (inJ x) < absk x.2.2.2) :
    15 * absk (inJ x) < absk (x.1 - x.2.1 - x.2.2.1) ∧
      absk (x.1 - x.2.1 - x.2.2.1) ≤ 2 * absk x.2.2.2 := by
  have ek : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
    simp only [inJ]
    abel
  have h1 := absk_add_le x.2.2.2 (inJ x)
  rw [ek] at h1
  have h2 := absk_sub_le (x.1 - x.2.1 - x.2.2.1) (inJ x)
  have e2 : x.1 - x.2.1 - x.2.2.1 - inJ x = x.2.2.2 := by
    rw [← ek]
    abel
  rw [e2] at h2
  have h4 := absk_nonneg (inJ x)
  constructor <;> linarith

/-- The kernel of the separated sector at weight one. -/
def Es1 (x : I4) : ℝ :=
  ((absk x.2.1 + absk x.2.2.1) * absk x.2.2.2 ^ 2 +
    (absk x.2.1 ^ 2 + absk x.2.2.1 ^ 2) * absk x.2.2.2 + absk x.2.1 ^ 2 * absk x.2.2.1) *
      ((absk x.1)⁻¹ * (absk (inJ x))⁻¹)

lemma Es1_nonneg (x : I4) : 0 ≤ Es1 x := by
  have h1 := absk_nonneg x.1
  have h2 := absk_nonneg (inJ x)
  have h3 := absk_nonneg x.2.1
  have h4 := absk_nonneg x.2.2.1
  have h5 := absk_nonneg x.2.2.2
  unfold Es1
  positivity

/-- The separated bracket at `L ≪ K`. -/
lemma s1_gt {L M K P A B C : ℝ} (hL : 0 < L) (hK : 0 < K) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (h1 : 2 * L ≤ K) (hP : P ≤ L + K)
    (hKA : K ≤ 2 * (A + B)) (hKC : K ≤ 2 * C) (hMA : 4 * K ≤ M → 3 * M ≤ 4 * A ∧ 3 * M ≤ 4 * B) :
    M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) + P * (L ^ 2 + K ^ 2) ≤
      2 ^ 12 * ((A + B) * C ^ 2 + (A ^ 2 + B ^ 2) * C + A ^ 2 * B) := by
  have hT : 0 ≤ (A + B) * C ^ 2 := by positivity
  have hU : 0 ≤ (A ^ 2 + B ^ 2) * C := by positivity
  have hV : 0 ≤ A ^ 2 * B := by positivity
  have hK3 : K ^ 3 ≤ 8 * ((A + B) * C ^ 2) := by
    calc K ^ 3 = K * K ^ 2 := by ring
      _ ≤ 2 * (A + B) * (2 * C) ^ 2 := by gcongr
      _ = _ := by ring
  have hLK : L ^ 2 ≤ K ^ 2 / 4 := by nlinarith only [h1, hL, hK]
  have hK2 : 0 ≤ K ^ 2 := by positivity
  have hPt : P * (L ^ 2 + K ^ 2) ≤ 2 * K ^ 3 := by
    have h2 : P ≤ 3 / 2 * K := by linarith
    calc P * (L ^ 2 + K ^ 2) ≤ 3 / 2 * K * (K ^ 2 / 4 + K ^ 2) := by gcongr
      _ ≤ _ := by nlinarith only [pow_pos hK 3]
  by_cases hhi : 4 * K ≤ M
  · obtain ⟨h3, h4⟩ := hMA hhi
    have m1 : M ≤ 4 / 3 * A := by linarith
    have m2 : M ≤ 4 / 3 * B := by linarith
    have hM3 : M ^ 3 ≤ 64 / 27 * (A ^ 2 * B) := by
      calc M ^ 3 = M * M * M := by ring
        _ ≤ 4 / 3 * A * (4 / 3 * A) * (4 / 3 * B) := by gcongr
        _ = _ := by ring
    have hK4 : K ^ 2 ≤ M ^ 2 / 16 := by nlinarith only [hhi, hK, hM]
    have hS : M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) ≤ 3 * M ^ 3 := by
      calc M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) ≤ M * (M ^ 2 / 16 + 2 * M ^ 2 + M ^ 2 / 16) := by
            gcongr
            linarith
        _ ≤ _ := by nlinarith only [pow_nonneg hM 3]
    nlinarith only [hS, hPt, hM3, hK3, hT, hU, hV]
  · rw [not_le] at hhi
    have hM2 : M ^ 2 ≤ 16 * K ^ 2 := by nlinarith only [hhi, hK, hM]
    have hS : M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) ≤ 133 * K ^ 3 := by
      calc M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) ≤ 4 * K * (K ^ 2 / 4 + 2 * (16 * K ^ 2) + K ^ 2) := by
            gcongr
        _ = _ := by ring
    nlinarith only [hS, hPt, hK3, hT, hU, hV]

/-- The separated bracket at `K ≪ L`. -/
lemma s1_lt {L M K P A B C : ℝ} (hL : 0 < L) (hK : 0 < K) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (h1 : 2 * K ≤ L) (hP : P ≤ L + K)
    (hLA : L ≤ 2 * (A + B)) (hKC : K ≤ 2 * C) (hMA : 4 * L ≤ M → 3 * M ≤ 4 * A ∧ 3 * M ≤ 4 * B) :
    M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) * K ^ 2 + P * (L ^ 2 + K ^ 2) * K ^ 2 ≤
      2 ^ 12 * ((A + B) * C ^ 2 + (A ^ 2 + B ^ 2) * C + A ^ 2 * B) * L * K := by
  have hT : 0 ≤ (A + B) * C ^ 2 := by positivity
  have hU : 0 ≤ (A ^ 2 + B ^ 2) * C := by positivity
  have hV : 0 ≤ A ^ 2 * B := by positivity
  have hLK : 0 < L * K := by positivity
  have hKL : K ^ 2 ≤ L ^ 2 / 4 := by nlinarith only [h1, hL, hK]
  have hL2 : L ^ 2 ≤ 8 * (A ^ 2 + B ^ 2) := by
    nlinarith only [hLA, hL, hA, hB, sq_nonneg (A - B)]
  have hLU : L ^ 2 * K ≤ 16 * ((A ^ 2 + B ^ 2) * C) := by
    calc L ^ 2 * K ≤ 8 * (A ^ 2 + B ^ 2) * (2 * C) := by gcongr
      _ = _ := by ring
  have hPt : P * (L ^ 2 + K ^ 2) * K ≤ 2 * L ^ 2 * K * L := by
    have h2 : P ≤ 3 / 2 * L := by linarith
    calc P * (L ^ 2 + K ^ 2) * K ≤ 3 / 2 * L * (L ^ 2 + L ^ 2 / 4) * K := by gcongr
      _ ≤ _ := by nlinarith only [mul_pos (pow_pos hL 3) hK]
  have hgoal : M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) * K + P * (L ^ 2 + K ^ 2) * K ≤
      2 ^ 12 * ((A + B) * C ^ 2 + (A ^ 2 + B ^ 2) * C + A ^ 2 * B) * L := by
    by_cases hhi : 4 * L ≤ M
    · obtain ⟨h3, h4⟩ := hMA hhi
      have m1 : M ≤ 4 / 3 * A := by linarith
      have m2 : M ≤ 4 / 3 * B := by linarith
      have hM3 : M ^ 3 ≤ 64 / 27 * (A ^ 2 * B) := by
        calc M ^ 3 = M * M * M := by ring
          _ ≤ 4 / 3 * A * (4 / 3 * A) * (4 / 3 * B) := by gcongr
          _ = _ := by ring
      have hL4 : L ^ 2 ≤ M ^ 2 / 16 := by nlinarith only [hhi, hL, hM]
      have hS : M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) ≤ 3 * M ^ 3 := by
        have hM0 := sq_nonneg M
        calc M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) ≤ M * (M ^ 2 / 16 + 2 * M ^ 2 + M ^ 2 / 16) := by
              gcongr
              linarith
          _ ≤ _ := by nlinarith only [pow_nonneg hM 3]
      have h5 : M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) * K ≤ 8 * (A ^ 2 * B) * L := by
        have h6 : K ≤ L := by linarith
        calc _ ≤ 3 * M ^ 3 * L := by gcongr
          _ ≤ 3 * (64 / 27 * (A ^ 2 * B)) * L := by gcongr
          _ ≤ _ := by
              have : 0 ≤ A ^ 2 * B * L := by positivity
              nlinarith only [this]
      have h7 : 2 * L ^ 2 * K * L ≤ 32 * ((A ^ 2 + B ^ 2) * C) * L := by
        have := mul_le_mul_of_nonneg_right hLU hL.le
        nlinarith only [this]
      have h8 : 0 ≤ ((A + B) * C ^ 2) * L := by positivity
      have h9 : 0 ≤ ((A ^ 2 + B ^ 2) * C) * L := by positivity
      have h10 : 0 ≤ (A ^ 2 * B) * L := by positivity
      nlinarith only [h5, h7, hPt, h8, h9, h10]
    · rw [not_le] at hhi
      have hM2 : M ^ 2 ≤ 16 * L ^ 2 := by nlinarith only [hhi, hL, hM]
      have hS : M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) * K ≤ 133 * L ^ 2 * K * L := by
        calc M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) * K ≤
            4 * L * (L ^ 2 + 2 * (16 * L ^ 2) + L ^ 2 / 4) * K := by gcongr
          _ ≤ _ := by nlinarith only [mul_pos (pow_pos hL 3) hK]
      have h7 : L ^ 2 * K * L ≤ 16 * ((A ^ 2 + B ^ 2) * C) * L :=
        mul_le_mul_of_nonneg_right hLU hL.le
      have h8 : 0 ≤ ((A + B) * C ^ 2) * L := by positivity
      have h9 : 0 ≤ ((A ^ 2 + B ^ 2) * C) * L := by positivity
      have h10 : 0 ≤ (A ^ 2 * B) * L := by positivity
      nlinarith only [hS, h7, hPt, h8, h9, h10]
  have := mul_le_mul_of_nonneg_right hgoal hK.le
  calc _ = (M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) * K + P * (L ^ 2 + K ^ 2) * K) * K := by ring
    _ ≤ _ := this

/-- `X₂` at separated exteriors, weight one. -/
lemma norm_X2_sep_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) {F : ℝ} (hF : 0 < F)
    (hsep : F / 2 ≤ |absk (l - a - b) - absk l|) :
    ‖X2b 1 r τ f g l a b‖ ≤ 2560 / (|r| ^ 2 * F) * absk (l - a) * (‖f a‖ * ‖g b‖) *
      Br₁ (absk l) (absk (l - a)) (absk (l - a - b)) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hl2 : l 2 = (l - a - b) 2 := by simp [ha, hb]
  have h1 := norm_outerInv_sep (H := heat4 l (l - a - b) a b) hr hl2 hj (by positivity : 0 < F / 2)
    hsep (tR 1 r τ l a b (f a) (g b))
  have h2 := norm_tR_one_le hr τ ha hb hj (f a) (g b)
  have hX : X2b 1 r τ f g l a b =
      outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (tR 1 r τ l a b (f a) (g b)) := by
    rw [X2b, ← twoRoot_eq_tR]
  rw [hX]
  refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
  ring

/-- `Z` at separated exteriors, weight one. -/
lemma norm_Z_sep_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) {F : ℝ} (hF : 0 < F)
    (hsep : F / 2 ≤ |absk (l - a - b) - absk l|) :
    ‖Zb 1 r τ f g l a b‖ ≤ 1280 / (|r| ^ 2 * F) * absk (a + b) * (‖f a‖ * ‖g b‖) *
      (absk l / absk (l - a - b) + absk (l - a - b) / absk l) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hl2 : l 2 = (l - a - b) 2 := by simp [ha, hb]
  have h1 := norm_outerInv_sep (H := heat4 l (l - a - b) a b) hr hl2 hj (by positivity : 0 < F / 2)
    hsep (X1b 1 r τ (a + b) l (l - a - b) (slowV a b (f a) (g b)))
  have e1 : (a + b) + (l - a - b) = l := by abel
  have hab : (a + b) 2 = 0 := by simp [ha, hb]
  have h2 := norm_X1b_one_le hr τ e1 hab hj (slowV a b (f a) (g b))
  have h3 := norm_slowV_le a b (f a) (g b)
  have hP := absk_nonneg (a + b)
  have hL := absk_nonneg l
  have hK := absk_nonneg (l - a - b)
  have hA := norm_nonneg (f a)
  have hB := norm_nonneg (g b)
  set R := absk l / absk (l - a - b) + absk (l - a - b) / absk l with hR
  have hR0 : 0 ≤ R := by positivity
  have h4 : ‖X1b 1 r τ (a + b) l (l - a - b) (slowV a b (f a) (g b))‖ ≤
      20 / |r| * (8 * absk (a + b) * ‖f a‖ * ‖g b‖) * R := h2.trans (by gcongr)
  refine h1.trans ((mul_le_mul_of_nonneg_left h4 (by positivity)).trans (le_of_eq ?_))
  ring

/-- The closing arithmetic of the separated block. -/
lemma sep1_close {q L M K J P F En : ℝ} (hq : 0 < q) (hL : 0 < L) (hK : 0 < K) (hJ : 0 < J)
    (hF : 0 < F) (hE : 0 ≤ En)
    (hS : (M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) + P * (L ^ 2 + K ^ 2)) * K ≤ 2 ^ 12 * En * F)
    (hS0 : 0 ≤ P * (L / K + K / L)) :
    (2560 / (q ^ 2 * F) * (M * Br₁ L M K) + 1280 / (q ^ 2 * F) * (P * (L / K + K / L))) *
        (16 * (K / J) * K) ≤ 2 ^ 28 / q ^ 2 * (En * (L⁻¹ * J⁻¹)) := by
  have e1 : M * Br₁ L M K + P * (L / K + K / L) =
      (M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) + P * (L ^ 2 + K ^ 2)) / (L * K) := by
    simp only [Br₁]
    field_simp
  have h1 : 2560 / (q ^ 2 * F) * (M * Br₁ L M K) + 1280 / (q ^ 2 * F) * (P * (L / K + K / L)) ≤
      2560 / (q ^ 2 * F) * (M * Br₁ L M K + P * (L / K + K / L)) := by
    have : 1280 / (q ^ 2 * F) * (P * (L / K + K / L)) ≤
        2560 / (q ^ 2 * F) * (P * (L / K + K / L)) := by
      refine mul_le_mul_of_nonneg_right ?_ hS0
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    rw [mul_add]
    linarith
  have hE' : 0 ≤ 16 * (K / J) * K := by positivity
  calc _ ≤ 2560 / (q ^ 2 * F) * (M * Br₁ L M K + P * (L / K + K / L)) * (16 * (K / J) * K) :=
        mul_le_mul_of_nonneg_right h1 hE'
    _ = 40960 / q ^ 2 * (((M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) + P * (L ^ 2 + K ^ 2)) * K) *
        (F⁻¹ * (L⁻¹ * J⁻¹))) := by
        rw [e1]
        field_simp
        ring
    _ ≤ 40960 / q ^ 2 * ((2 ^ 12 * En * F) * (F⁻¹ * (L⁻¹ * J⁻¹))) := by gcongr
    _ = 40960 * 2 ^ 12 / q ^ 2 * (En * (L⁻¹ * J⁻¹)) := by
        field_simp
    _ ≤ _ := by
        have : 0 ≤ En * (L⁻¹ * J⁻¹) := by positivity
        refine mul_le_mul_of_nonneg_right ?_ this
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- **The block on the separated mask at weight one** (8.3). -/
theorem norm_YLb_sep_one {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hx : Act₃ x) (hS : OnS D x)
    (f g h : Field) :
    ‖YLb 1 r τ f g h x‖ ≤ 2 ^ 28 / |r| ^ 2 * Es1 x *
      (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) := by
  obtain ⟨ha, hb, hc, hj⟩ := hx
  have hq : 0 < |r| := abs_pos.2 hr
  have hk2 : (x.1 - x.2.1 - x.2.2.1) 2 ≠ 0 := by
    have e : (x.1 - x.2.1 - x.2.2.1) 2 = inJ x 2 := by
      simp [inJ, hc]
    rwa [e]
  obtain ⟨hl0, hm0, hk0⟩ := fast_labels ha hb hk2
  have hj0 : inJ x ≠ 0 := fun h => hj (by rw [h]; rfl)
  have hL : 0 < absk x.1 := lt_of_lt_of_le one_pos (one_le_absk hl0)
  have hK : 0 < absk (x.1 - x.2.1 - x.2.2.1) := lt_of_lt_of_le one_pos (one_le_absk hk0)
  have hJ : 0 < absk (inJ x) := lt_of_lt_of_le one_pos (one_le_absk hj0)
  have hA0 := absk_nonneg x.2.1
  have hB0 := absk_nonneg x.2.2.1
  have hC0 := absk_nonneg x.2.2.2
  have hM0 := absk_nonneg (x.1 - x.2.1)
  have hP0 := absk_nonneg (x.2.1 + x.2.2.1)
  obtain ⟨-, hKc⟩ := last_lengths hS.c_gt
  have hab : x.2.1 + x.2.2.1 = x.1 - (x.1 - x.2.1 - x.2.2.1) := by abel
  have hPle : absk (x.2.1 + x.2.2.1) ≤ absk x.1 + absk (x.1 - x.2.1 - x.2.2.1) := by
    rw [hab]
    exact absk_sub_le _ _
  obtain ⟨q1, q2, p3, p4⟩ := two_leaf_paths x.1 x.2.1 x.2.2.1
  have hN1 := norm_nonneg (f x.2.1)
  have hN2 := norm_nonneg (g x.2.2.1)
  have hN3 := norm_nonneg (h x.2.2.2)
  have hfg : 0 ≤ ‖f x.2.1‖ * ‖g x.2.2.1‖ := by positivity
  have ek : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
    simp only [inJ]
    abel
  have hLast := norm_Lb_le 1 τ ek (h x.2.2.2)
  simp only [wt, pow_one] at hLast
  have hop : ‖YLb 1 r τ f g h x‖ ≤ (‖X2b 1 r τ f g x.1 x.2.1 x.2.2.1‖ +
      ‖Zb 1 r τ f g x.1 x.2.1 x.2.2.1‖) * (16 * (absk (x.1 - x.2.1 - x.2.2.1) / absk (inJ x)) *
        absk (x.1 - x.2.1 - x.2.2.1) * ‖h x.2.2.2‖) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_add_le _ _) hLast (norm_nonneg _) (by positivity))
  refine hop.trans ?_
  set L := absk x.1 with hLd
  set K := absk (x.1 - x.2.1 - x.2.2.1) with hKd
  set J := absk (inJ x) with hJd
  set M := absk (x.1 - x.2.1) with hMd
  set A := absk x.2.1 with hAd
  set B := absk x.2.2.1 with hBd
  set C := absk x.2.2.2 with hCd
  set P := absk (x.2.1 + x.2.2.1) with hPd
  have hE : Es1 x = ((A + B) * C ^ 2 + (A ^ 2 + B ^ 2) * C + A ^ 2 * B) * (L⁻¹ * J⁻¹) := rfl
  have hEn : 0 ≤ (A + B) * C ^ 2 + (A ^ 2 + B ^ 2) * C + A ^ 2 * B := by positivity
  have hZ0 : 0 ≤ P * (L / K + K / L) := by positivity
  have hsep : ∃ F : ℝ, 0 < F ∧ F / 2 ≤ |K - L| ∧
      (M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) + P * (L ^ 2 + K ^ 2)) * K ≤
        2 ^ 12 * ((A + B) * C ^ 2 + (A ^ 2 + B ^ 2) * C + A ^ 2 * B) * F := by
    rcases not_and_or.1 hS.sep with h1 | h1
    · rw [not_le] at h1
      refine ⟨L, hL, ?_, ?_⟩
      · rw [abs_sub_comm]
        exact le_trans (by linarith) (le_abs_self _)
      · have h2 := s1_lt hL hK hM0 hA0 hB0 hC0 h1.le hPle (by linarith) hKc
          (fun h3 => ⟨by linarith, by linarith⟩)
        have h3 : (M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) + P * (L ^ 2 + K ^ 2)) * K * K ≤
            2 ^ 12 * ((A + B) * C ^ 2 + (A ^ 2 + B ^ 2) * C + A ^ 2 * B) * L * K := by
          calc _ = M * (L ^ 2 + 2 * M ^ 2 + K ^ 2) * K ^ 2 + P * (L ^ 2 + K ^ 2) * K ^ 2 := by ring
            _ ≤ _ := h2
        exact le_of_mul_le_mul_right h3 hK
    · rw [not_le] at h1
      refine ⟨K, hK, le_trans (by linarith) (le_abs_self _), ?_⟩
      have h2 := s1_gt hL hK hM0 hA0 hB0 hC0 h1.le hPle (by linarith) hKc
        (fun h3 => ⟨by linarith, by linarith⟩)
      exact mul_le_mul_of_nonneg_right h2 hK.le
  obtain ⟨F, hF, hF2, hF3⟩ := hsep
  have hXb := norm_X2_sep_one hr τ f g ha hb hk2 hF hF2
  have hZb := norm_Z_sep_one hr τ f g ha hb hk2 hF hF2
  have hcl := sep1_close (q := |r|) (M := M) hq hL hK hJ hF hEn hF3 hZ0
  have hX1 : (‖X2b 1 r τ f g x.1 x.2.1 x.2.2.1‖ + ‖Zb 1 r τ f g x.1 x.2.1 x.2.2.1‖) ≤
      (2560 / (|r| ^ 2 * F) * (M * Br₁ L M K) + 1280 / (|r| ^ 2 * F) * (P * (L / K + K / L))) *
        (‖f x.2.1‖ * ‖g x.2.2.1‖) := by
    refine (add_le_add hXb hZb).trans (le_of_eq ?_)
    ring
  have he : 0 ≤ 16 * (K / J) * K := by positivity
  rw [hE]
  calc _ = (‖X2b 1 r τ f g x.1 x.2.1 x.2.2.1‖ + ‖Zb 1 r τ f g x.1 x.2.1 x.2.2.1‖) *
        (16 * (K / J) * K) * ‖h x.2.2.2‖ := by ring
    _ ≤ (2560 / (|r| ^ 2 * F) * (M * Br₁ L M K) + 1280 / (|r| ^ 2 * F) * (P * (L / K + K / L))) *
        (‖f x.2.1‖ * ‖g x.2.2.1‖) * (16 * (K / J) * K) * ‖h x.2.2.2‖ := by gcongr
    _ = (2560 / (|r| ^ 2 * F) * (M * Br₁ L M K) + 1280 / (|r| ^ 2 * F) * (P * (L / K + K / L))) *
        (16 * (K / J) * K) * ((‖f x.2.1‖ * ‖g x.2.2.1‖) * ‖h x.2.2.2‖) := by ring
    _ ≤ 2 ^ 28 / |r| ^ 2 * (((A + B) * C ^ 2 + (A ^ 2 + B ^ 2) * C + A ^ 2 * B) * (L⁻¹ * J⁻¹)) *
        ((‖f x.2.1‖ * ‖g x.2.2.1‖) * ‖h x.2.2.2‖) := by gcongr
    _ = _ := by ring

end OVNS.Quant.Metric

end
