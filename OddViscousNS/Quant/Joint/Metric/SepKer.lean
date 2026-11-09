import OddViscousNS.Quant.Joint.Metric.SepBlock

/-!
# The primitive-separated high-last sector: the kernel (step J5, node N9)

Body 43 (LOCAL663).  `muS`: `P₃ > 16 J` up to the low pass, all ancestors at most `D`,
`max(L, K) > 2 min(L, K)`.  `norm_YLb_sep`: the block of `(X₂ + Z) 𝓛` at weight two is at most
`q⁻² (Eg + El + Em) + q⁻³ D² Eh` times the three leaves.  `Eg`, `El` are the two ordinary sectors
(`L ≪ K`, `K ≪ L`) and the whole of `Z`; `Em` the phase part of a large intermediate, `Eh` its heat
part.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open Classical in
/-- The mask of the primitive-separated high-last sector. -/
def muS (D : ℝ) (x : I4) : ℝ :=
  (1 - lowM x.2.2.2 (inJ x)) *
    if absk x.2.1 ≤ D ∧ absk x.2.2.1 ≤ D ∧ absk x.2.2.2 ≤ D ∧
      ¬ (absk x.1 ≤ 2 * absk (x.1 - x.2.1 - x.2.2.1) ∧
        absk (x.1 - x.2.1 - x.2.2.1) ≤ 2 * absk x.1)
    then 1 else 0

lemma muS_nonneg (D : ℝ) (x : I4) : 0 ≤ muS D x := by
  have h := lowM_le_one x.2.2.2 (inJ x)
  unfold muS
  split_ifs <;> linarith

lemma muS_le_one (D : ℝ) (x : I4) : muS D x ≤ 1 := by
  have h := lowM_nonneg x.2.2.2 (inJ x)
  have h1 := lowM_le_one x.2.2.2 (inJ x)
  unfold muS
  split_ifs <;> linarith

variable {D : ℝ} {x : I4}

/-- The support of the mask. -/
structure OnS (D : ℝ) (x : I4) : Prop where
  a_le : absk x.2.1 ≤ D
  b_le : absk x.2.2.1 ≤ D
  c_le : absk x.2.2.2 ≤ D
  sep : ¬ (absk x.1 ≤ 2 * absk (x.1 - x.2.1 - x.2.2.1) ∧
    absk (x.1 - x.2.1 - x.2.2.1) ≤ 2 * absk x.1)
  c_gt : 16 * absk (inJ x) < absk x.2.2.2

lemma onS_of_ne (h : muS D x ≠ 0) : OnS D x := by
  unfold muS at h
  by_cases hm : absk x.2.1 ≤ D ∧ absk x.2.2.1 ≤ D ∧ absk x.2.2.2 ≤ D ∧
      ¬ (absk x.1 ≤ 2 * absk (x.1 - x.2.1 - x.2.2.1) ∧
        absk (x.1 - x.2.1 - x.2.2.1) ≤ 2 * absk x.1)
  swap
  · simp only [hm, ↓reduceIte, mul_zero, ne_eq, not_true_eq_false] at h
  obtain ⟨h1, h2, h3, h4⟩ := hm
  refine ⟨h1, h2, h3, h4, ?_⟩
  by_contra hc
  rw [not_lt] at hc
  apply h
  have hJ := lt_two_pow_bnd (inJ x)
  have hle : absk x.2.2.2 ≤ 2 ^ (bnd (inJ x) + 5) := by
    have e : (2 : ℝ) ^ (bnd (inJ x) + 5) = 16 * 2 ^ (bnd (inJ x) + 1) := by ring
    rw [e]
    linarith
  have : lowM x.2.2.2 (inJ x) = 1 := chiM_one hle
  rw [this]
  simp

/-- The kernel of the ordinary sector at `L ≪ K`. -/
def Eg (x : I4) : ℝ :=
  (absk x.2.1 ^ 2 + absk x.2.2.1 ^ 2) * absk x.2.2.2 ^ 3 / (absk x.1 ^ 2 * absk (inJ x) ^ 2)

/-- The kernel of the ordinary sector at `K ≪ L`. -/
def El (x : I4) : ℝ :=
  (absk x.2.1 ^ 2 + absk x.2.2.1 ^ 2) * absk x.2.2.2 / absk (inJ x) ^ 2

/-- The kernel of the phase part. -/
def Em (x : I4) : ℝ :=
  absk x.2.1 ^ 2 * absk x.2.2.1 ^ 2 * absk x.2.2.2 / (absk x.1 ^ 2 * absk (inJ x) ^ 2)

/-- The kernel of the heat part. -/
def Eh (x : I4) : ℝ :=
  absk x.2.1 ^ 2 * absk x.2.2.1 ^ 2 / (absk x.1 ^ 2 * absk (inJ x) ^ 2)

lemma Eg_nonneg (x : I4) : 0 ≤ Eg x := by
  have := absk_nonneg x.2.2.2
  unfold Eg
  positivity

lemma El_nonneg (x : I4) : 0 ≤ El x := by
  have := absk_nonneg x.2.2.2
  unfold El
  positivity

lemma Em_nonneg (x : I4) : 0 ≤ Em x := by
  have := absk_nonneg x.2.2.2
  unfold Em
  positivity

lemma Eh_nonneg (x : I4) : 0 ≤ Eh x := by
  unfold Eh
  positivity

lemma Br_gt_le {L M K : ℝ} (hL : 0 < L) (hK : 0 < K) (h1 : 2 * L ≤ K) (h2 : M ≤ 4 * K)
    (hM : 0 ≤ M) : Br (L ^ 2) (M ^ 2) (K ^ 2) ≤ 514 * (K ^ 2 / L ^ 2) := by
  have e1 : L ^ 2 / K ^ 2 ≤ K ^ 2 / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : L ^ 2 ≤ K ^ 2 := by nlinarith only [h1, hL, hK]
    exact mul_le_mul this this (by positivity) (by positivity)
  have e2 : 2 * (M ^ 2) ^ 2 / (L ^ 2 * K ^ 2) ≤ 512 * (K ^ 2 / L ^ 2) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have m1 : M ^ 2 ≤ 16 * K ^ 2 := by nlinarith only [h2, hM, hK]
    have m2 : (M ^ 2) ^ 2 ≤ (16 * K ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) m1 2
    have hp : 0 ≤ L ^ 2 * L ^ 2 * K ^ 2 := by positivity
    calc 2 * (M ^ 2) ^ 2 * L ^ 2 ≤ 2 * (16 * K ^ 2) ^ 2 * L ^ 2 := by gcongr
      _ = 512 * K ^ 2 * (L ^ 2 * K ^ 2) := by ring
  simp only [Br]
  linarith

lemma Br_lt_le {L M K : ℝ} (hL : 0 < L) (hK : 0 < K) (h1 : 2 * K ≤ L) (h2 : M ≤ 4 * L)
    (hM : 0 ≤ M) : Br (L ^ 2) (M ^ 2) (K ^ 2) ≤ 514 * (L ^ 2 / K ^ 2) := by
  have e1 : K ^ 2 / L ^ 2 ≤ L ^ 2 / K ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : K ^ 2 ≤ L ^ 2 := by nlinarith only [h1, hL, hK]
    exact mul_le_mul this this (by positivity) (by positivity)
  have e2 : 2 * (M ^ 2) ^ 2 / (L ^ 2 * K ^ 2) ≤ 512 * (L ^ 2 / K ^ 2) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have m1 : M ^ 2 ≤ 16 * L ^ 2 := by nlinarith only [h2, hM, hL]
    have m2 : (M ^ 2) ^ 2 ≤ (16 * L ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) m1 2
    calc 2 * (M ^ 2) ^ 2 * K ^ 2 ≤ 2 * (16 * L ^ 2) ^ 2 * K ^ 2 := by gcongr
      _ = 512 * L ^ 2 * (L ^ 2 * K ^ 2) := by ring
  simp only [Br]
  linarith

/-- The price of the ordinary sector at `L ≪ K`. -/
lemma gt_arith {q L K J S A₂ C : ℝ} (hq : 0 < q) (hL : 0 < L) (hK : 0 < K) (hJ : 0 < J)
    (hS : S ≤ 4 * K * (514 * (K ^ 2 / L ^ 2))) (hA0 : 0 ≤ A₂)
    (hA : K ^ 2 ≤ 8 * A₂) (hC0 : 0 ≤ C) (hC : K ≤ 2 * C) :
    5632 / (q ^ 2 * K) * S * (16 * (K / J) ^ 2 * K) ≤ 2 ^ 34 / q ^ 2 * (A₂ * C ^ 3 / (L ^ 2 * J ^ 2)) := by
  have h3 : K ^ 3 ≤ 8 * C ^ 3 := by
    calc K ^ 3 ≤ (2 * C) ^ 3 := pow_le_pow_left₀ hK.le hC 3
      _ = _ := by ring
  have h5 : K ^ 5 ≤ 8 * A₂ * (8 * C ^ 3) := by
    calc K ^ 5 = K ^ 2 * K ^ 3 := by ring
      _ ≤ _ := mul_le_mul hA h3 (by positivity) (by positivity)
  have e : 5632 / (q ^ 2 * K) * (4 * K * (514 * (K ^ 2 / L ^ 2))) * (16 * (K / J) ^ 2 * K) =
      185270272 / q ^ 2 * (K ^ 5 / (L ^ 2 * J ^ 2)) := by
    field_simp
    ring
  calc _ ≤ 5632 / (q ^ 2 * K) * (4 * K * (514 * (K ^ 2 / L ^ 2))) * (16 * (K / J) ^ 2 * K) := by
        gcongr
    _ = _ := e
    _ ≤ 185270272 / q ^ 2 * (8 * A₂ * (8 * C ^ 3) / (L ^ 2 * J ^ 2)) := by gcongr
    _ = 185270272 * 64 / q ^ 2 * (A₂ * C ^ 3 / (L ^ 2 * J ^ 2)) := by ring
    _ ≤ _ := by
        have : 0 ≤ A₂ * C ^ 3 / (L ^ 2 * J ^ 2) := by positivity
        gcongr
        norm_num

/-- The price of the ordinary sector at `K ≪ L`. -/
lemma lt_arith {q L K J S A₂ C : ℝ} (hq : 0 < q) (hL : 0 < L) (hK : 0 < K) (hJ : 0 < J)
    (hS : S ≤ 4 * L * (514 * (L ^ 2 / K ^ 2))) (hA0 : 0 ≤ A₂)
    (hA : L ^ 2 ≤ 8 * A₂) (hC0 : 0 ≤ C) (hC : K ≤ 2 * C) :
    5632 / (q ^ 2 * L) * S * (16 * (K / J) ^ 2 * K) ≤ 2 ^ 32 / q ^ 2 * (A₂ * C / J ^ 2) := by
  have e : 5632 / (q ^ 2 * L) * (4 * L * (514 * (L ^ 2 / K ^ 2))) * (16 * (K / J) ^ 2 * K) =
      185270272 / q ^ 2 * (L ^ 2 * K / J ^ 2) := by
    field_simp
    ring
  calc _ ≤ 5632 / (q ^ 2 * L) * (4 * L * (514 * (L ^ 2 / K ^ 2))) * (16 * (K / J) ^ 2 * K) := by
        gcongr
    _ = _ := e
    _ ≤ 185270272 / q ^ 2 * (8 * A₂ * (2 * C) / J ^ 2) := by gcongr
    _ = 185270272 * 16 / q ^ 2 * (A₂ * C / J ^ 2) := by ring
    _ ≤ _ := by
        have : 0 ≤ A₂ * C / J ^ 2 := by positivity
        gcongr
        norm_num

/-- The merged size at `L ≪ K`. -/
lemma Zsum_gt {L K P : ℝ} (hL : 0 < L) (hK : 0 < K) (h1 : 2 * L ≤ K)
    (hP : P ≤ L + K) : P * (L ^ 2 / K ^ 2 + K ^ 2 / L ^ 2) ≤ 4 * K * (514 * (K ^ 2 / L ^ 2)) := by
  have e1 : L ^ 2 / K ^ 2 ≤ K ^ 2 / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : L ^ 2 ≤ K ^ 2 := by nlinarith only [h1, hL, hK]
    exact mul_le_mul this this (by positivity) (by positivity)
  have hE : 0 ≤ K ^ 2 / L ^ 2 := by positivity
  have hP2 : P ≤ 2 * K := by linarith
  calc P * (L ^ 2 / K ^ 2 + K ^ 2 / L ^ 2) ≤ 2 * K * (2 * (K ^ 2 / L ^ 2)) := by
        refine mul_le_mul hP2 (by linarith) (by positivity) (by positivity)
    _ ≤ _ := by
        have : 0 ≤ K * (K ^ 2 / L ^ 2) := by positivity
        nlinarith only [this]

/-- The merged size at `K ≪ L`. -/
lemma Zsum_lt {L K P : ℝ} (hL : 0 < L) (hK : 0 < K) (h1 : 2 * K ≤ L)
    (hP : P ≤ L + K) : P * (L ^ 2 / K ^ 2 + K ^ 2 / L ^ 2) ≤ 4 * L * (514 * (L ^ 2 / K ^ 2)) := by
  have e1 : K ^ 2 / L ^ 2 ≤ L ^ 2 / K ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : K ^ 2 ≤ L ^ 2 := by nlinarith only [h1, hL, hK]
    exact mul_le_mul this this (by positivity) (by positivity)
  have hE : 0 ≤ L ^ 2 / K ^ 2 := by positivity
  have hP2 : P ≤ 2 * L := by linarith
  calc P * (L ^ 2 / K ^ 2 + K ^ 2 / L ^ 2) ≤ 2 * L * (2 * (L ^ 2 / K ^ 2)) := by
        refine mul_le_mul hP2 (by linarith) (by positivity) (by positivity)
    _ ≤ _ := by
        have : 0 ≤ L * (L ^ 2 / K ^ 2) := by positivity
        nlinarith only [this]

/-- The two prices at a large intermediate. -/
lemma hi_arith {q L K J M F A B C Dd : ℝ} (hq : 0 < q) (hL : 0 < L) (hK : 0 < K) (hJ : 0 < J)
    (hM : 0 < M) (hF : 0 < F) (hKF : K ≤ F) (hA0 : 0 ≤ A)
    (hA : 3 * M ≤ 4 * A) (hB : 3 * M ≤ 4 * B) (hAD : A ≤ Dd) (hC0 : 0 ≤ C) (hC : K ≤ 2 * C) :
    (2 ^ 14 / q ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) + 2 ^ 16 / (q ^ 3 * F) * (M ^ 6 / (L ^ 2 * K ^ 2))) *
        (16 * (K / J) ^ 2 * K) ≤
      2 ^ 22 / q ^ 2 * (A ^ 2 * B ^ 2 * C / (L ^ 2 * J ^ 2)) +
        2 ^ 23 * Dd ^ 2 / q ^ 3 * (A ^ 2 * B ^ 2 / (L ^ 2 * J ^ 2)) := by
  have hD0 : 0 ≤ Dd := hA0.trans hAD
  have m1 : M ≤ 4 / 3 * A := by linarith
  have m2 : M ≤ 4 / 3 * B := by linarith
  have m3 : M ≤ 4 / 3 * Dd := by linarith
  have h4 : M ^ 4 ≤ (4 / 3 * A) ^ 2 * (4 / 3 * B) ^ 2 := by
    calc M ^ 4 = M ^ 2 * M ^ 2 := by ring
      _ ≤ _ := by gcongr
  have h6 : M ^ 6 ≤ (4 / 3 * Dd) ^ 2 * ((4 / 3 * A) ^ 2 * (4 / 3 * B) ^ 2) := by
    calc M ^ 6 = M ^ 2 * M ^ 4 := by ring
      _ ≤ _ := by gcongr
  have e : (2 ^ 14 / q ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) +
      2 ^ 16 / (q ^ 3 * F) * (M ^ 6 / (L ^ 2 * K ^ 2))) * (16 * (K / J) ^ 2 * K) =
      2 ^ 18 / q ^ 2 * (M ^ 4 * K / (L ^ 2 * J ^ 2)) +
        2 ^ 20 / q ^ 3 * (K / F) * (M ^ 6 / (L ^ 2 * J ^ 2)) := by
    field_simp
    ring
  rw [e]
  have hKF' : K / F ≤ 1 := (div_le_one hF).2 hKF
  have t1 : 2 ^ 18 / q ^ 2 * (M ^ 4 * K / (L ^ 2 * J ^ 2)) ≤
      2 ^ 22 / q ^ 2 * (A ^ 2 * B ^ 2 * C / (L ^ 2 * J ^ 2)) := by
    calc _ ≤ 2 ^ 18 / q ^ 2 * ((4 / 3 * A) ^ 2 * (4 / 3 * B) ^ 2 * (2 * C) / (L ^ 2 * J ^ 2)) := by
          gcongr
      _ = 2 ^ 18 * (512 / 81) / q ^ 2 * (A ^ 2 * B ^ 2 * C / (L ^ 2 * J ^ 2)) := by ring
      _ ≤ _ := by
          have : 0 ≤ A ^ 2 * B ^ 2 * C / (L ^ 2 * J ^ 2) := by positivity
          gcongr
          norm_num
  have t2 : 2 ^ 20 / q ^ 3 * (K / F) * (M ^ 6 / (L ^ 2 * J ^ 2)) ≤
      2 ^ 23 * Dd ^ 2 / q ^ 3 * (A ^ 2 * B ^ 2 / (L ^ 2 * J ^ 2)) := by
    calc _ ≤ 2 ^ 20 / q ^ 3 * 1 * ((4 / 3 * Dd) ^ 2 * ((4 / 3 * A) ^ 2 * (4 / 3 * B) ^ 2) /
          (L ^ 2 * J ^ 2)) := by gcongr
      _ = 2 ^ 20 * (4096 / 729) * Dd ^ 2 / q ^ 3 * (A ^ 2 * B ^ 2 / (L ^ 2 * J ^ 2)) := by ring
      _ ≤ _ := by
          have : 0 ≤ A ^ 2 * B ^ 2 / (L ^ 2 * J ^ 2) := by positivity
          gcongr
          norm_num
  linarith

/-- The block of `X₂` at a large intermediate and separated exteriors. -/
lemma norm_X2_hi_sep {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (f g : Field) {l a b : Mode} (ha : a 2 = 0)
    (hb : b 2 = 0) (hj : (l - a - b) 2 ≠ 0) {F : ℝ} (hF : 0 < F) (hLF : absk l ≤ F)
    (hKF : absk (l - a - b) ≤ F) (h4 : 4 * F ≤ absk (l - a))
    (hsep : F / 2 ≤ |absk (l - a - b) - absk l|) :
    ‖X2b 2 r τ f g l a b‖ ≤
      (2 ^ 14 / |r| ^ 2 * (absk (l - a) ^ 4 / (absk l ^ 2 * absk (l - a - b) ^ 2)) +
        2 ^ 16 / (|r| ^ 3 * F) * (absk (l - a) ^ 6 / (absk l ^ 2 * absk (l - a - b) ^ 2))) *
        (‖f a‖ * ‖g b‖) := by
  have hX : X2b 2 r τ f g l a b =
      outerInv r (heat4 l (l - a - b) a b) l (l - a - b)
          (tR 2 r τ l a b (f a) (g b) - tH 2 r τ l a b (f a) (g b)) +
        outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (tH 2 r τ l a b (f a) (g b)) := by
    rw [X2b, ← twoRoot_eq_tR, ← outerInv_add, sub_add_cancel]
  rw [hX, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_Xph_sep hr τ ha hb hj hF hLF hKF h4 hsep _ _)
    (norm_Xheat_sep hr τ ha hb hj hF hLF hKF h4 hsep _ _))

/-- **The block on the separated mask**, at weight two. -/
theorem norm_YLb_sep {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (hx : Act₃ x) (hS : OnS D x) (f g h : Field) :
    ‖YLb 2 r τ f g h x‖ ≤
      (2 ^ 36 / |r| ^ 2 * (Eg x + El x + Em x) + 2 ^ 23 * D ^ 2 / |r| ^ 3 * Eh x) *
        (‖f x.2.1‖ * ‖g x.2.2.1‖ * ‖h x.2.2.2‖) := by
  obtain ⟨ha, hb, hc, hj⟩ := hx
  have hq : 0 < |r| := abs_pos.2 hr
  have hk2 : (x.1 - x.2.1 - x.2.2.1) 2 ≠ 0 := by
    have e : (x.1 - x.2.1 - x.2.2.1) 2 = inJ x 2 := by
      simp [inJ, hc]
    rwa [e]
  obtain ⟨hl0, hm0, hk0⟩ := fast_labels ha hb hk2
  have hj0 : inJ x ≠ 0 := fun h => hj (by rw [h]; rfl)
  have hL1 := one_le_absk hl0
  have hK1 := one_le_absk hk0
  have hM1 := one_le_absk hm0
  have hJ1 := one_le_absk hj0
  have hL : 0 < absk x.1 := by linarith
  have hK : 0 < absk (x.1 - x.2.1 - x.2.2.1) := by linarith
  have hM : 0 < absk (x.1 - x.2.1) := by linarith
  have hJ : 0 < absk (inJ x) := by linarith
  have hA0 := absk_nonneg x.2.1
  have hB0 := absk_nonneg x.2.2.1
  have hC0 := absk_nonneg x.2.2.2
  have hg := Eg_nonneg x
  have hl := El_nonneg x
  have hm := Em_nonneg x
  have hh := Eh_nonneg x
  have hN1 := norm_nonneg (f x.2.1)
  have hN2 := norm_nonneg (g x.2.2.1)
  have hN3 := norm_nonneg (h x.2.2.2)
  have hKc : absk (x.1 - x.2.1 - x.2.2.1) ≤ 2 * absk x.2.2.2 := by
    have ek : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
      simp only [inJ]
      abel
    have h1 := absk_add_le x.2.2.2 (inJ x)
    rw [ek] at h1
    linarith [hS.c_gt]
  have hab : x.2.1 + x.2.2.1 = x.1 - (x.1 - x.2.1 - x.2.2.1) := by abel
  have hPle : absk (x.2.1 + x.2.2.1) ≤ absk x.1 + absk (x.1 - x.2.1 - x.2.2.1) := by
    rw [hab]
    exact absk_sub_le _ _
  obtain ⟨-, -, p3, p4⟩ := two_leaf_paths x.1 x.2.1 x.2.2.1
  obtain ⟨q1, q2, -, -⟩ := two_leaf_paths x.1 x.2.1 x.2.2.1
  set L := absk x.1 with hLd
  set K := absk (x.1 - x.2.1 - x.2.2.1) with hKd
  set J := absk (inJ x) with hJd
  set M := absk (x.1 - x.2.1) with hMd
  set A := absk x.2.1 with hAd
  set B := absk x.2.2.1 with hBd
  set C := absk x.2.2.2 with hCd
  set e := 16 * (K / J) ^ 2 * K with he
  have he0 : 0 ≤ e := by positivity
  set y₁ := ‖f x.2.1‖ * ‖g x.2.2.1‖ with hy₁
  have hy0 : 0 ≤ y₁ := by positivity
  have hLast : ‖Lb 2 τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x) (h x.2.2.2)‖ ≤
      e * ‖h x.2.2.2‖ := norm_last_edge τ h
  have hop : ‖YLb 2 r τ f g h x‖ ≤ (‖X2b 2 r τ f g x.1 x.2.1 x.2.2.1‖ +
      ‖Zb 2 r τ f g x.1 x.2.1 x.2.2.1‖) * (e * ‖h x.2.2.2‖) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_add_le _ _) hLast (norm_nonneg _) (by positivity))
  refine hop.trans ?_
  have hmain : (‖X2b 2 r τ f g x.1 x.2.1 x.2.2.1‖ + ‖Zb 2 r τ f g x.1 x.2.1 x.2.2.1‖) * e ≤
      (2 ^ 36 / |r| ^ 2 * (Eg x + El x + Em x) + 2 ^ 23 * D ^ 2 / |r| ^ 3 * Eh x) * y₁ := by
    have eg : Eg x = (A ^ 2 + B ^ 2) * C ^ 3 / (L ^ 2 * J ^ 2) := rfl
    have el : El x = (A ^ 2 + B ^ 2) * C / J ^ 2 := rfl
    have em : Em x = A ^ 2 * B ^ 2 * C / (L ^ 2 * J ^ 2) := rfl
    have eh : Eh x = A ^ 2 * B ^ 2 / (L ^ 2 * J ^ 2) := rfl
    have hAB : 0 ≤ A ^ 2 + B ^ 2 := by positivity
    have hBr0 : 0 ≤ Br (L ^ 2) (M ^ 2) (K ^ 2) := by
      simp only [Br]
      positivity
    have a1 : 0 ≤ Eg x * y₁ / |r| ^ 2 := by positivity
    have a2 : 0 ≤ El x * y₁ / |r| ^ 2 := by positivity
    have a3 : 0 ≤ Em x * y₁ / |r| ^ 2 := by positivity
    have a4 : 0 ≤ D ^ 2 * (Eh x * y₁) / |r| ^ 3 := by positivity
    have eT : (2 ^ 36 / |r| ^ 2 * (Eg x + El x + Em x) + 2 ^ 23 * D ^ 2 / |r| ^ 3 * Eh x) * y₁ =
        2 ^ 36 * (Eg x * y₁ / |r| ^ 2) + 2 ^ 36 * (El x * y₁ / |r| ^ 2) +
          2 ^ 36 * (Em x * y₁ / |r| ^ 2) + 2 ^ 23 * (D ^ 2 * (Eh x * y₁) / |r| ^ 3) := by ring
    rw [eT, add_mul]
    have hP := absk_nonneg (x.2.1 + x.2.2.1)
    rcases not_and_or.1 hS.sep with h1 | h1
    · rw [not_le] at h1
      have hsep : L / 2 ≤ |K - L| := by
        rw [abs_sub_comm]
        exact le_trans (by linarith) (le_abs_self _)
      have hXb := norm_X2_sep hr τ f g ha hb hk2 hL hsep
      have hZb := norm_Z_sep hr τ f g ha hb hk2 hL hsep
      rw [← absk_sq x.1, ← absk_sq (x.1 - x.2.1), ← absk_sq (x.1 - x.2.1 - x.2.2.1)] at hXb
      rw [← absk_sq x.1, ← absk_sq (x.1 - x.2.1 - x.2.2.1)] at hZb
      have hLA : L ^ 2 ≤ 8 * (A ^ 2 + B ^ 2) := by
        have : L ≤ 2 * (A + B) := by linarith
        nlinarith only [this, hL, hA0, hB0, sq_nonneg (A - B)]
      have t2 : ‖Zb 2 r τ f g x.1 x.2.1 x.2.2.1‖ * e ≤ 2 ^ 32 * (El x * y₁ / |r| ^ 2) := by
        have hS1 := Zsum_lt hL hK h1.le hPle
        calc _ ≤ (2816 / (|r| ^ 2 * L) * absk (x.2.1 + x.2.2.1) * y₁ *
              (L ^ 2 / K ^ 2 + K ^ 2 / L ^ 2)) * e := mul_le_mul_of_nonneg_right hZb he0
          _ ≤ (5632 / (|r| ^ 2 * L) * absk (x.2.1 + x.2.2.1) * y₁ *
              (L ^ 2 / K ^ 2 + K ^ 2 / L ^ 2)) * e := by gcongr; norm_num
          _ = 5632 / (|r| ^ 2 * L) * (absk (x.2.1 + x.2.2.1) *
              (L ^ 2 / K ^ 2 + K ^ 2 / L ^ 2)) * e * y₁ := by ring
          _ ≤ 2 ^ 32 / |r| ^ 2 * ((A ^ 2 + B ^ 2) * C / J ^ 2) * y₁ :=
              mul_le_mul_of_nonneg_right (lt_arith hq hL hK hJ hS1 hAB hLA hC0 hKc) hy0
          _ = _ := by rw [el]; ring
      by_cases hhi : 4 * L ≤ M
      · have hXs := norm_X2_hi_sep hr τ f g ha hb hk2 hL le_rfl (by linarith) hhi hsep
        have t1 : ‖X2b 2 r τ f g x.1 x.2.1 x.2.2.1‖ * e ≤
            2 ^ 22 * (Em x * y₁ / |r| ^ 2) + 2 ^ 23 * (D ^ 2 * (Eh x * y₁) / |r| ^ 3) := by
          have h2 := hi_arith hq hL hK hJ hM hL (by linarith : K ≤ L) hA0
            (by linarith : 3 * M ≤ 4 * A) (by linarith : 3 * M ≤ 4 * B) hS.a_le hC0 hKc
          calc _ ≤ _ := mul_le_mul_of_nonneg_right hXs he0
            _ = (2 ^ 14 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) +
                2 ^ 16 / (|r| ^ 3 * L) * (M ^ 6 / (L ^ 2 * K ^ 2))) * e * y₁ := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right h2 hy0
            _ = _ := by
                rw [em, eh]
                ring
        linarith
      · rw [not_le] at hhi
        have t1 : ‖X2b 2 r τ f g x.1 x.2.1 x.2.2.1‖ * e ≤ 2 ^ 32 * (El x * y₁ / |r| ^ 2) := by
          have hS1 : M * Br (L ^ 2) (M ^ 2) (K ^ 2) ≤ 4 * L * (514 * (L ^ 2 / K ^ 2)) :=
            mul_le_mul hhi.le (Br_lt_le hL hK h1.le hhi.le hM.le) hBr0 (by positivity)
          calc _ ≤ (5632 / (|r| ^ 2 * L) * M * y₁ * Br (L ^ 2) (M ^ 2) (K ^ 2)) * e :=
                mul_le_mul_of_nonneg_right hXb he0
            _ = 5632 / (|r| ^ 2 * L) * (M * Br (L ^ 2) (M ^ 2) (K ^ 2)) * e * y₁ := by ring
            _ ≤ 2 ^ 32 / |r| ^ 2 * ((A ^ 2 + B ^ 2) * C / J ^ 2) * y₁ :=
                mul_le_mul_of_nonneg_right (lt_arith hq hL hK hJ hS1 hAB hLA hC0 hKc) hy0
            _ = _ := by rw [el]; ring
        linarith
    · rw [not_le] at h1
      have hsep : K / 2 ≤ |K - L| := le_trans (by linarith) (le_abs_self _)
      have hXb := norm_X2_sep hr τ f g ha hb hk2 hK hsep
      have hZb := norm_Z_sep hr τ f g ha hb hk2 hK hsep
      rw [← absk_sq x.1, ← absk_sq (x.1 - x.2.1), ← absk_sq (x.1 - x.2.1 - x.2.2.1)] at hXb
      rw [← absk_sq x.1, ← absk_sq (x.1 - x.2.1 - x.2.2.1)] at hZb
      have hKA : K ^ 2 ≤ 8 * (A ^ 2 + B ^ 2) := by
        have : K ≤ 2 * (A + B) := by linarith
        nlinarith only [this, hK, hA0, hB0, sq_nonneg (A - B)]
      have t2 : ‖Zb 2 r τ f g x.1 x.2.1 x.2.2.1‖ * e ≤ 2 ^ 34 * (Eg x * y₁ / |r| ^ 2) := by
        have hS1 := Zsum_gt hL hK h1.le hPle
        calc _ ≤ (2816 / (|r| ^ 2 * K) * absk (x.2.1 + x.2.2.1) * y₁ *
              (L ^ 2 / K ^ 2 + K ^ 2 / L ^ 2)) * e := mul_le_mul_of_nonneg_right hZb he0
          _ ≤ (5632 / (|r| ^ 2 * K) * absk (x.2.1 + x.2.2.1) * y₁ *
              (L ^ 2 / K ^ 2 + K ^ 2 / L ^ 2)) * e := by gcongr; norm_num
          _ = 5632 / (|r| ^ 2 * K) * (absk (x.2.1 + x.2.2.1) *
              (L ^ 2 / K ^ 2 + K ^ 2 / L ^ 2)) * e * y₁ := by ring
          _ ≤ 2 ^ 34 / |r| ^ 2 * ((A ^ 2 + B ^ 2) * C ^ 3 / (L ^ 2 * J ^ 2)) * y₁ :=
              mul_le_mul_of_nonneg_right (gt_arith hq hL hK hJ hS1 hAB hKA hC0 hKc) hy0
          _ = _ := by rw [eg]; ring
      by_cases hhi : 4 * K ≤ M
      · have hXs := norm_X2_hi_sep hr τ f g ha hb hk2 hK (by linarith) le_rfl hhi hsep
        have t1 : ‖X2b 2 r τ f g x.1 x.2.1 x.2.2.1‖ * e ≤
            2 ^ 22 * (Em x * y₁ / |r| ^ 2) + 2 ^ 23 * (D ^ 2 * (Eh x * y₁) / |r| ^ 3) := by
          have h2 := hi_arith hq hL hK hJ hM hK le_rfl hA0
            (by linarith : 3 * M ≤ 4 * A) (by linarith : 3 * M ≤ 4 * B) hS.a_le hC0 hKc
          calc _ ≤ _ := mul_le_mul_of_nonneg_right hXs he0
            _ = (2 ^ 14 / |r| ^ 2 * (M ^ 4 / (L ^ 2 * K ^ 2)) +
                2 ^ 16 / (|r| ^ 3 * K) * (M ^ 6 / (L ^ 2 * K ^ 2))) * e * y₁ := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right h2 hy0
            _ = _ := by
                rw [em, eh]
                ring
        linarith
      · rw [not_le] at hhi
        have t1 : ‖X2b 2 r τ f g x.1 x.2.1 x.2.2.1‖ * e ≤ 2 ^ 34 * (Eg x * y₁ / |r| ^ 2) := by
          have hS1 : M * Br (L ^ 2) (M ^ 2) (K ^ 2) ≤ 4 * K * (514 * (K ^ 2 / L ^ 2)) :=
            mul_le_mul hhi.le (Br_gt_le hL hK h1.le hhi.le hM.le) hBr0 (by positivity)
          calc _ ≤ (5632 / (|r| ^ 2 * K) * M * y₁ * Br (L ^ 2) (M ^ 2) (K ^ 2)) * e :=
                mul_le_mul_of_nonneg_right hXb he0
            _ = 5632 / (|r| ^ 2 * K) * (M * Br (L ^ 2) (M ^ 2) (K ^ 2)) * e * y₁ := by ring
            _ ≤ 2 ^ 34 / |r| ^ 2 * ((A ^ 2 + B ^ 2) * C ^ 3 / (L ^ 2 * J ^ 2)) * y₁ :=
                mul_le_mul_of_nonneg_right (gt_arith hq hL hK hJ hS1 hAB hKA hC0 hKc) hy0
            _ = _ := by rw [eg]; ring
        linarith
  calc _ = (‖X2b 2 r τ f g x.1 x.2.1 x.2.2.1‖ + ‖Zb 2 r τ f g x.1 x.2.1 x.2.2.1‖) * e *
        ‖h x.2.2.2‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmain hN3
    _ = _ := by ring

end OVNS.Quant.Metric

end
