import OddViscousNS.Closed.Row.TailPair

/-!
# The tail lemma

With `S_m(ρ) = ∑_{|p|>ρ} |p|^{-2m}` (so `Sm 2 = S₄`, `Sm 3 = S₆`): for real `c ⊥ k`, on the set
`O` of pairs leaving the lens of radius `R`,

`3 ∑_{p ∈ O} pterm ≤ ω² (1+ε) C |c|² (4 S₄(ρ) + C S₆(ρ))`,

under `ρ² ≥ 120`, `|k| ≤ R - ρ`, `0 ≤ e ≤ 2aρ²` and `δ² ≤ ε a² ρ⁴`.  Everything is done in `[0,∞]`.
The factor is `(4/3 S₄ + C/3 S₆)`, against `9/4 S₄` for the trace tail of UF661.
-/

open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

/-- `S_{2m}(ρ) = ∑_{|p|>ρ} |p|^{-2m}`. -/
def Sm (m ρ : ℕ) : ℝ≥0∞ :=
  ∑' p : Mode, ENNReal.ofReal (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ m else 0)

/-- The off-lens indicator. -/
def Off (k : Mode) (R : ℕ) (p : Mode) : Prop := R ^ 2 < nsq p ∨ R ^ 2 < nsq (k - p)

open Classical in
/-- The part of the row form off the lens of radius `R`. -/
def offSum (k : Mode) (c : R3) (R : ℕ) : ℝ≥0∞ :=
  ∑' p, ENNReal.ofReal (if Off k R p then pterm k c p else 0)

/-- `p ↦ (U-truncated A⁻ᵐ)` is invariant. -/
private lemma sym_cut (m ρ : ℕ) :
    SymFn (fun p => if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ m else 0) := by
  intro σ ε hε p
  simp only [nsq_act hε, absSq_act hε]

private lemma cut_nonneg (m ρ : ℕ) (p : Mode) :
    0 ≤ (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ m else 0 : ℝ) := by
  have := absSq_nonneg' p
  split_ifs <;> positivity

private lemma pos_of_U {ρ : ℕ} {p : Mode} (h : ρ ^ 2 < nsq p) : 0 < absSq p := by
  rw [← nsq_cast]
  have : 0 < nsq p := by omega
  exact_mod_cast this

/-- Moments over `U`, in the form used below. -/
private lemma mom_U (m ρ : ℕ) (v : R3) :
    3 * ∑' p : Mode, ENNReal.ofReal (dR p v ^ 2 * (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ (m + 1) else 0)) =
      ENNReal.ofReal (nR v) * Sm m ρ := by
  rw [moment (cut_nonneg (m + 1) ρ) (sym_cut (m + 1) ρ) v]
  congr 1
  refine tsum_congr fun p => ?_
  congr 1
  split_ifs with h
  · have := (pos_of_U h).ne'
    rw [pow_succ]
    field_simp
  · simp

/-- Two legs above `ρ` off the lens. -/
lemma off_legs {k p : Mode} {R ρ : ℕ} (hρ : ρ ≤ R) (hk : nsq k ≤ (R - ρ) ^ 2)
    (h : Off k R p) : ρ ^ 2 < nsq p ∧ ρ ^ 2 < nsq (k - p) := by
  have hK : absk k ≤ ((R - ρ : ℕ) : ℝ) := by
    unfold absk
    rw [show absSq k = (nsq k : ℝ) from (nsq_cast k).symm]
    apply Real.sqrt_le_iff.2
    exact ⟨by positivity, by exact_mod_cast hk⟩
  have hsub : ((R - ρ : ℕ) : ℝ) = (R : ℝ) - ρ := by
    rw [Nat.cast_sub hρ]
  have hsq : ∀ (q : Mode) (t : ℕ), (t ^ 2 < nsq q ↔ (t : ℝ) < absk q) := by
    intro q t
    unfold absk
    rw [show absSq q = (nsq q : ℝ) from (nsq_cast q).symm, Real.lt_sqrt (by positivity)]
    exact_mod_cast Iff.rfl
  have h1 := absk_sub_le k p
  have h2 := absk_sub_le k (k - p)
  rw [sub_sub_self'] at h2
  rcases h with h | h
  · rw [hsq] at h
    have hρ' : (ρ : ℝ) ≤ R := by exact_mod_cast hρ
    refine ⟨(hsq _ _).2 (by linarith), (hsq _ _).2 ?_⟩
    have : absk p ≤ absk (k - p) + absk k := by
      have := absk_sub_le (k - p) (-k)
      have e : (k - p) - (-k) = 2 • k - p := by abel
      have h3 := absk_sub_le p (p - k)
      have e2 : p - (p - k) = k := by abel
      have h4 := absk_sub_le k (k - p)
      have e3 : absk (p - k) = absk (k - p) := by
        rw [← absk_neg (k - p)]; congr 1; abel
      rw [sub_sub_self'] at h4
      have h5 := absk_sub_le (k - p) (-p)
      have e4 := absk_add_le (k - p) (-k)
      have e5 : (k - p) + (-k) = -p := by abel
      rw [e5, absk_neg, absk_neg] at e4
      exact e4
    linarith
  · rw [hsq] at h
    have hρ' : (ρ : ℝ) ≤ R := by exact_mod_cast hρ
    refine ⟨(hsq _ _).2 (by linarith), (hsq _ _).2 (by linarith)⟩

/-- The first half of the tail bound: reduction to the `U` sums. -/
private lemma off_sum_le (k : Mode) (c : R3) (hc : dR k c = 0) (R ρ : ℕ) (ε : ℝ)
    (hρ : ρ ≤ R) (hk : nsq k ≤ (R - ρ) ^ 2) (h120 : 120 ≤ ρ ^ 2) (hε : 0 ≤ ε)
    (he0 : 0 ≤ hm k - 117 / 500) (he1 : hm k - 117 / 500 ≤ 2 * (29 / 100) * (ρ : ℝ) ^ 2)
    (hδ : (hm k - 29 / 100 * absSq k - 117 / 500) ^ 2 ≤ ε * (29 / 100) ^ 2 * (ρ : ℝ) ^ 4) :
    offSum k c R ≤ ENNReal.ofReal (om (nsq k) ^ 2) *
      (2 * ∑' p, ENNReal.ofReal (if ρ ^ 2 < nsq p then t1 k c p else 0)
        + ENNReal.ofReal (1 + ε) * ∑' p, ENNReal.ofReal (if ρ ^ 2 < nsq p then t2 k c p else 0)) := by
  classical
  set G₁ : Mode → ℝ≥0∞ := fun p => ENNReal.ofReal (if ρ ^ 2 < nsq p then t1 k c p else 0) with hG₁
  set G₂ : Mode → ℝ≥0∞ := fun p => ENNReal.ofReal (if ρ ^ 2 < nsq p then t2 k c p else 0) with hG₂
  have hpt : ∀ p, ENNReal.ofReal (if Off k R p then pterm k c p else 0) ≤
      ENNReal.ofReal (om (nsq k) ^ 2) * (G₁ p + G₁ (k - p)
        + ENNReal.ofReal ((1 + ε) / 2) * (G₂ p + G₂ (k - p))) := by
    intro p
    by_cases hO : Off k R p
    · obtain ⟨h1, h2⟩ := off_legs hρ hk hO
      have hAe : (nsq p : ℝ) = absSq p := nsq_cast p
      have hBe : (nsq (k - p) : ℝ) = absSq (k - p) := nsq_cast (k - p)
      have hρ2 : (ρ : ℝ) ^ 2 ≤ absSq p := by
        rw [← hAe]; exact_mod_cast h1.le
      have hρ3 : (ρ : ℝ) ^ 2 ≤ absSq (k - p) := by
        rw [← hBe]; exact_mod_cast h2.le
      have hb := pterm_off k p c hc ε (by omega) (by omega) he0
        (he1.trans (by linarith)) (he1.trans (by linarith)) hε
        (hδ.trans (by
          have h4 : (ρ : ℝ) ^ 4 ≤ absSq p * absSq (k - p) := by
            have := mul_le_mul hρ2 hρ3 (by positivity) (absSq_nonneg' _)
            calc (ρ : ℝ) ^ 4 = (ρ : ℝ) ^ 2 * (ρ : ℝ) ^ 2 := by ring
              _ ≤ _ := this
          exact mul_le_mul_of_nonneg_left h4 (by positivity)))
      have hl : ρ ^ 2 < nsq (k - p) := h2
      simp only [hO, ite_true, hG₁, hG₂, h1, hl]
      have h0 := pterm_nonneg k c p
      have ht1 := t1_nonneg k c p
      have ht1' := t1_nonneg k c (k - p)
      have ht2 := t2_nonneg k c p
      have ht2' := t2_nonneg k c (k - p)
      have hε2 : 0 ≤ (1 + ε) / 2 := by positivity
      rw [← ENNReal.ofReal_add ht2 ht2', ← ENNReal.ofReal_mul hε2,
        ← ENNReal.ofReal_add ht1 ht1',
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hb
    · simp [hO]
  refine (tsum_le_tsum hpt).trans (le_of_eq ?_)
  have hr1 : ∑' p, G₁ (k - p) = ∑' p, G₁ p := (Equiv.subLeft k).tsum_eq G₁
  have hr2 : ∑' p, G₂ (k - p) = ∑' p, G₂ p := (Equiv.subLeft k).tsum_eq G₂
  rw [ENNReal.tsum_mul_left, tsum_add, tsum_add, ENNReal.tsum_mul_left, tsum_add, hr1, hr2]
  congr 1
  have e : ENNReal.ofReal (1 + ε) = ENNReal.ofReal ((1 + ε) / 2) * 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [e]
  ring

/-- `3 ∑_U t₁ = C |c|² S₄`. -/
private lemma sum_t1 (k : Mode) (c : R3) (hc : dR k c = 0) (ρ : ℕ) :
    3 * ∑' p, ENNReal.ofReal (if ρ ^ 2 < nsq p then t1 k c p else 0) =
      ENNReal.ofReal (absSq k * nR c) * Sm 2 ρ := by
  have := mom_U 2 ρ (crR k c)
  rw [nR_crR k c hc] at this
  rw [← this]
  congr 1
  refine tsum_congr fun p => ?_
  congr 1
  simp only [t1, mul_ite, mul_zero]

/-- The real vector of a lattice vector. -/
def kv (k : Mode) : R3 := fun i => (k i : ℝ)

lemma dR_kv (p k : Mode) : dR p (kv k) = dZ p k := rfl

lemma nR_kv (k : Mode) : nR (kv k) = absSq k := rfl

/-- The sum of `t₂` over `U`. -/
private lemma sum_t2 (k : Mode) (hk : k ≠ 0) (c : R3) (hc : dR k c = 0) (ρ : ℕ) :
    3 * ∑' p, ENNReal.ofReal (if ρ ^ 2 < nsq p then t2 k c p else 0) ≤
      2 * ENNReal.ofReal (absSq k * nR c) * Sm 2 ρ
        + ENNReal.ofReal (absSq k ^ 2 * nR c) * Sm 3 ρ := by
  classical
  set G₂ : Mode → ℝ≥0∞ := fun p => ENNReal.ofReal (if ρ ^ 2 < nsq p then t2 k c p else 0) with hG₂
  have hneg : ∑' p, G₂ (-p) = ∑' p, G₂ p := (Equiv.neg Mode).tsum_eq G₂
  set H : Mode → ℝ := fun p => if ρ ^ 2 < nsq p then
      (4 * dZ p k ^ 2 * dR p c ^ 2 + absSq k ^ 2 * dR p c ^ 2) * (absSq p)⁻¹ ^ 4 else 0 with hH
  have hC0 : 0 ≤ absSq k := absSq_nonneg' k
  have hstep : ∀ p, G₂ p + G₂ (-p) = 2 * ENNReal.ofReal (H p) := by
    intro p
    have hnp : nsq (-p) = nsq p := by simp [nsq]
    by_cases h : ρ ^ 2 < nsq p
    · simp only [hG₂, hH, h, hnp, ite_true]
      have ht := t2_nonneg k c p
      have ht' := t2_nonneg k c (-p)
      rw [← ENNReal.ofReal_add ht ht', show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      have e1 : absSq (-p) = absSq p := absSq_neg p
      have e2 : dR (-p) c = - dR p c := dR_neg p c
      have e3 : absSq (k - -p) = absSq k + 2 * dZ p k + absSq p := by
        have := absSq_sub k (-p)
        have e4 : dZ (-p) k = - dZ p k := by
          simp only [dZ, Pi.neg_apply, Int.cast_neg, Fin.sum_univ_three]; ring
        rw [this, e4, e1]; ring
      have e5 := absSq_sub k p
      simp only [t2, e1, e2, e3, e5]
      ring
    · simp only [hG₂, hH, h, hnp, ite_false]
      simp
  have h2 : 2 * ∑' p, G₂ p = 2 * ∑' p, ENNReal.ofReal (H p) := by
    rw [two_mul, ← ENNReal.tsum_mul_left]
    nth_rewrite 2 [← hneg]
    rw [← tsum_add]
    exact tsum_congr hstep
  have h3 : ∑' p, G₂ p = ∑' p, ENNReal.ofReal (H p) :=
    (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).1 h2
  have hle : ∀ p, ENNReal.ofReal (H p) ≤
      ENNReal.ofReal (nR c) * ENNReal.ofReal (dZ p k ^ 2 *
        (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ 3 else 0))
      + ENNReal.ofReal (absSq k) * ENNReal.ofReal (dR p c ^ 2 *
        (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ 3 else 0))
      + ENNReal.ofReal (absSq k ^ 2) * ENNReal.ofReal (dR p c ^ 2 *
        (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ 4 else 0)) := by
    intro p
    by_cases h : ρ ^ 2 < nsq p
    · simp only [hH, h, ite_true]
      have hA := pos_of_U h
      have hn := nR_nonneg c
      rw [← ENNReal.ofReal_mul hn, ← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h4 := mul_four_le k p hk c hc
      have h5 : (absSq p)⁻¹ ^ 4 * (4 * dZ p k ^ 2 * dR p c ^ 2) ≤
          (absSq p)⁻¹ ^ 4 * (absSq p * (dZ p k ^ 2 * nR c + absSq k * dR p c ^ 2)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have e6 : (absSq p)⁻¹ ^ 4 * (absSq p * (dZ p k ^ 2 * nR c + absSq k * dR p c ^ 2)) =
          (absSq p)⁻¹ ^ 3 * (dZ p k ^ 2 * nR c + absSq k * dR p c ^ 2) := by
        have := hA.ne'
        field_simp
      nlinarith
    · simp [hH, h]
  rw [h3]
  have hm3 : 3 * ∑' p : Mode, ENNReal.ofReal (dZ p k ^ 2 *
        (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ 3 else 0)) = ENNReal.ofReal (absSq k) * Sm 2 ρ := by
    have := mom_U 2 ρ (kv k)
    rwa [nR_kv] at this
  have hm3' : 3 * ∑' p : Mode, ENNReal.ofReal (dR p c ^ 2 *
        (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ 3 else 0)) = ENNReal.ofReal (nR c) * Sm 2 ρ :=
    mom_U 2 ρ c
  have hm4 : 3 * ∑' p : Mode, ENNReal.ofReal (dR p c ^ 2 *
        (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ 4 else 0)) = ENNReal.ofReal (nR c) * Sm 3 ρ :=
    mom_U 3 ρ c
  have hn := nR_nonneg c
  calc 3 * ∑' p, ENNReal.ofReal (H p)
      ≤ 3 * ∑' p, (ENNReal.ofReal (nR c) * ENNReal.ofReal (dZ p k ^ 2 *
        (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ 3 else 0))
      + ENNReal.ofReal (absSq k) * ENNReal.ofReal (dR p c ^ 2 *
        (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ 3 else 0))
      + ENNReal.ofReal (absSq k ^ 2) * ENNReal.ofReal (dR p c ^ 2 *
        (if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ 4 else 0))) :=
        mul_le_mul_right (tsum_le_tsum hle) 3
    _ = ENNReal.ofReal (nR c) * (ENNReal.ofReal (absSq k) * Sm 2 ρ)
        + ENNReal.ofReal (absSq k) * (ENNReal.ofReal (nR c) * Sm 2 ρ)
        + ENNReal.ofReal (absSq k ^ 2) * (ENNReal.ofReal (nR c) * Sm 3 ρ) := by
          rw [tsum_add, tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
            ENNReal.tsum_mul_left, ← hm3, ← hm3', ← hm4]
          ring
    _ = _ := by
          rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_mul (sq_nonneg _)]
          ring

/-- **The tail lemma.** -/
theorem tail_le (k : Mode) (hk0 : k ≠ 0) (c : R3) (hc : dR k c = 0) (R ρ : ℕ) (ε : ℝ)
    (hρ : ρ ≤ R) (hk : nsq k ≤ (R - ρ) ^ 2) (h120 : 120 ≤ ρ ^ 2) (hε : 0 ≤ ε)
    (he0 : 0 ≤ hm k - 117 / 500) (he1 : hm k - 117 / 500 ≤ 2 * (29 / 100) * (ρ : ℝ) ^ 2)
    (hδ : (hm k - 29 / 100 * absSq k - 117 / 500) ^ 2 ≤ ε * (29 / 100) ^ 2 * (ρ : ℝ) ^ 4) :
    3 * offSum k c R ≤
      ENNReal.ofReal (om (nsq k) ^ 2 * (1 + ε) * (absSq k * nR c)) *
        (4 * Sm 2 ρ + ENNReal.ofReal (absSq k) * Sm 3 ρ) := by
  have h1 := off_sum_le k c hc R ρ ε hρ hk h120 hε he0 he1 hδ
  have h2 := sum_t1 k c hc ρ
  have h3 := sum_t2 k hk0 c hc ρ
  set X := ∑' p, ENNReal.ofReal (if ρ ^ 2 < nsq p then t1 k c p else 0)
  set Y := ∑' p, ENNReal.ofReal (if ρ ^ 2 < nsq p then t2 k c p else 0)
  set S := Sm 2 ρ
  set S' := Sm 3 ρ
  have hC0 : 0 ≤ absSq k := absSq_nonneg' k
  have hn := nR_nonneg c
  have hε1 : 1 ≤ ENNReal.ofReal (1 + ε) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  set E := ENNReal.ofReal (1 + ε)
  set Cn := ENNReal.ofReal (absSq k * nR c)
  set O := ENNReal.ofReal (om (nsq k) ^ 2)
  have hrhs : ENNReal.ofReal (om (nsq k) ^ 2 * (1 + ε) * (absSq k * nR c)) = O * E * Cn := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (sq_nonneg _)]
  rw [hrhs]
  have hCC : ENNReal.ofReal (absSq k ^ 2 * nR c) = ENNReal.ofReal (absSq k) * Cn := by
    rw [← ENNReal.ofReal_mul hC0]; congr 1; ring
  rw [hCC] at h3
  calc 3 * offSum k c R ≤ 3 * (O * (2 * X + E * Y)) := mul_le_mul_right h1 3
    _ = O * (2 * (3 * X) + E * (3 * Y)) := by ring
    _ ≤ O * (2 * (Cn * S) + E * (2 * Cn * S + ENNReal.ofReal (absSq k) * Cn * S')) := by
        rw [h2]
        exact mul_le_mul_right (add_le_add_right (mul_le_mul_right h3 E) _) O
    _ ≤ O * (E * (2 * (Cn * S)) + E * (2 * Cn * S + ENNReal.ofReal (absSq k) * Cn * S')) := by
        refine mul_le_mul_right (add_le_add_left ?_ _) O
        calc 2 * (Cn * S) = 1 * (2 * (Cn * S)) := by rw [one_mul]
          _ ≤ E * (2 * (Cn * S)) := mul_le_mul_left hε1 _
    _ = _ := by ring

/-- `S₆(ρ) ≤ S₄(ρ)/ρ²`. -/
lemma Sm3_le (ρ : ℕ) (hρ : 0 < ρ) : Sm 3 ρ ≤ ENNReal.ofReal ((ρ : ℝ)⁻¹ ^ 2) * Sm 2 ρ := by
  unfold Sm
  rw [← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun p => ?_
  by_cases h : ρ ^ 2 < nsq p
  · simp only [h, ite_true]
    have hA := pos_of_U h
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hle : (ρ : ℝ) ^ 2 ≤ absSq p := by
      rw [← nsq_cast]; exact_mod_cast h.le
    have hρ0 : (0 : ℝ) < ρ := by exact_mod_cast hρ
    have h1 : (absSq p)⁻¹ ≤ ((ρ : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hle
    calc (absSq p)⁻¹ ^ 3 = (absSq p)⁻¹ * (absSq p)⁻¹ ^ 2 := by ring
      _ ≤ ((ρ : ℝ) ^ 2)⁻¹ * (absSq p)⁻¹ ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by simp only [inv_pow]
  · simp [h]

end Row
end OVNS
