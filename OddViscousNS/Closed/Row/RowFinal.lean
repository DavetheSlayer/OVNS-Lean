import OddViscousNS.Closed.Row.Check

/-!
# The matrix band: from a passing row test to the row bound
-/

open Finset
open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

set_option maxRecDepth 20000
set_option linter.constructorNameAsVariable false

/-- The left kernel of `(1,0)`. -/
noncomputable def L10 : ℕ → ℕ := F1 17592186044416000 6084

/-- The right kernel of `(1,0)`. -/
noncomputable def R10 : ℕ → ℕ := F0 35184372088832000 6084

lemma kl10 : KerR 1 L10 17592186044416 := kerR1 _ _ (by norm_num) (by norm_num)

lemma kr10 : KerR 0 R10 35184372088832 := kerR0 _ _ (by norm_num) (by norm_num)

/-- The left kernel of `(2,0)`. -/
noncomputable def L20 : ℕ → ℕ := F2 4294967296000 6084

/-- The right kernel of `(2,0)`. -/
noncomputable def R20 : ℕ → ℕ := F0 140737488355328000 6084

lemma kl20 : KerR 2 L20 4294967296 := kerR2 _ _ (by norm_num) (by norm_num)

lemma kr20 : KerR 0 R20 140737488355328 := kerR0 _ _ (by norm_num) (by norm_num)

/-- The left kernel of `(3,0)`. -/
noncomputable def L30 : ℕ → ℕ := F3 131072000 6084

/-- The right kernel of `(3,0)`. -/
noncomputable def R30 : ℕ → ℕ := F0 1125899906842624000 6084

lemma kl30 : KerR 3 L30 131072 := kerR3 _ _ (by norm_num) (by norm_num)

lemma kr30 : KerR 0 R30 1125899906842624 := kerR0 _ _ (by norm_num) (by norm_num)

/-- The left kernel of `(1,1)`. -/
noncomputable def L11 : ℕ → ℕ := F1 1099511627776000 6084

/-- The right kernel of `(1,1)`. -/
noncomputable def R11 : ℕ → ℕ := F1 1099511627776000 6084

lemma kl11 : KerR 1 L11 1099511627776 := kerR1 _ _ (by norm_num) (by norm_num)

lemma kr11 : KerR 1 R11 1099511627776 := kerR1 _ _ (by norm_num) (by norm_num)

/-- The left kernel of `(3,1)`. -/
noncomputable def L31 : ℕ → ℕ := F3 1048576000 6084

/-- The right kernel of `(3,1)`. -/
noncomputable def R31 : ℕ → ℕ := F1 1099511627776000 6084

lemma kl31 : KerR 3 L31 1048576 := kerR3 _ _ (by norm_num) (by norm_num)

lemma kr31 : KerR 1 R31 1099511627776 := kerR1 _ _ (by norm_num) (by norm_num)

/-- The left kernel of `(2,2)`. -/
noncomputable def L22 : ℕ → ℕ := F2 1073741824000 6084

/-- The right kernel of `(2,2)`. -/
noncomputable def R22 : ℕ → ℕ := F2 8589934592000 6084

lemma kl22 : KerR 2 L22 1073741824 := kerR2 _ _ (by norm_num) (by norm_num)

lemma kr22 : KerR 2 R22 8589934592 := kerR2 _ _ (by norm_num) (by norm_num)

/-- The tables hold the convolutions of the six kernels. -/
structure TabsOK (T : Tabs) : Prop where
  k10 : KerOK L10 R10 T.a10 T.b10
  k20 : KerOK L20 R20 T.a20 T.b20
  k30 : KerOK L30 R30 T.a30 T.b30
  k11 : KerOK L11 R11 T.a11 T.b11
  k31 : KerOK L31 R31 T.a31 T.b31
  k22 : KerOK L22 R22 T.a22 T.b22

/-- The rounding constants are checked. -/
structure ErrOK : Prop where
  e10 : (errS L10 R10 : ℝ) / 618970019642690137449562112 ≤ (E10 : ℝ)
  e20 : (errS L20 R20 : ℝ) / 604462909807314587353088 ≤ (E20 : ℝ)
  e30 : (errS L30 R30 : ℝ) / 147573952589676412928 ≤ (E30 : ℝ)
  e31 : (errS L31 R31 : ℝ) / 1152921504606846976 ≤ (E31 : ℝ)

/-- The scaled kernel forms. -/
def m10 (k : Mode) (v : R3) : ℝ := MR L10 R10 k v / 618970019642690137449562112
def m20 (k : Mode) (v : R3) : ℝ := MR L20 R20 k v / 604462909807314587353088
def m30 (k : Mode) (v : R3) : ℝ := MR L30 R30 k v / 147573952589676412928
def m11 (k : Mode) (v : R3) : ℝ := MR L11 R11 k v / 1208925819614629174706176
def m31 (k : Mode) (v : R3) : ℝ := MR L31 R31 k v / 1152921504606846976
def m22 (k : Mode) (v : R3) : ℝ := MR L22 R22 k v / 9223372036854775808

/-- The high-pair bound, with `e ≥ 0`. -/
theorem hh_le (hE : ErrOK) (k : Mode) (c : R3) (hc : dR k c = 0)
    (he : 0 ≤ hm k - 117 / 500) :
    let e := hm k - 117 / 500
    let δ := hm k - 29 / 100 * absSq k - 117 / 500
    let c' := crR k c
    ∑ p ∈ hhF k, pterm k c p ≤ om (nsq k) ^ 2 *
      ((2 * e ^ 2 * m10 k c' - 4 * (29 / 100) * e * m20 k c' + 2 * (29 / 100) ^ 2 * m30 k c')
        + (2 * δ ^ 2 * (m20 k c - m11 k c) + 2 * (29 / 100) ^ 2 * (m31 k c - m22 k c)))
      + om (nsq k) ^ 2 * ((2 * e ^ 2 * (E10 : ℝ) + 2 * (29 / 100) ^ 2 * (E30 : ℝ)) * absSq k
        + 2 * δ ^ 2 * (E20 : ℝ) + 2 * (29 / 100) ^ 2 * (E31 : ℝ)) * nR c := by
  intro e δ c'
  have hc' : dR k c' = 0 := dR_crR_self k c
  have hn' : nR c' = absSq k * nR c := nR_crR k c hc
  have hn := nR_nonneg c
  have hC := absSq_nonneg' k
  have hs : ∑ p ∈ hhF k, pterm k c p =
      ∑ p ∈ hhF k, w1 k p * dR p c' ^ 2 + ∑ p ∈ hhF k, w2 k p * dR p c ^ 2 := by
    rw [← sum_add_distrib]; rfl
  rw [hs, hh_sum1 k c' hc', hh_sum2 k c hc]
  have a10 := Mh_hi kl10 kr10 k c'
  have b20 := Mh_lo kl20 kr20 k c'
  have a30 := Mh_hi kl30 kr30 k c'
  have a20 := Mh_hi kl20 kr20 k c
  have b11 := Mh_lo kl11 kr11 k c
  have a31 := Mh_hi kl31 kr31 k c
  have b22 := Mh_lo kl22 kr22 k c
  norm_num at a10 b20 a30 a20 b11 a31 b22
  have e10 := hE.e10
  have e20 := hE.e20
  have e30 := hE.e30
  have e31 := hE.e31
  have u10 : Mh 1 0 k c' ≤ m10 k c' + (E10 : ℝ) * (absSq k * nR c) := by
    rw [← hn']
    have := mul_le_mul_of_nonneg_right e10 (nR_nonneg c')
    unfold m10
    linarith
  have u30 : Mh 3 0 k c' ≤ m30 k c' + (E30 : ℝ) * (absSq k * nR c) := by
    rw [← hn']
    have := mul_le_mul_of_nonneg_right e30 (nR_nonneg c')
    unfold m30
    linarith
  have u20 : Mh 2 0 k c ≤ m20 k c + (E20 : ℝ) * nR c := by
    have := mul_le_mul_of_nonneg_right e20 hn
    unfold m20
    linarith
  have u31 : Mh 3 1 k c ≤ m31 k c + (E31 : ℝ) * nR c := by
    have := mul_le_mul_of_nonneg_right e31 hn
    unfold m31
    linarith
  have l20 : m20 k c' ≤ Mh 2 0 k c' := b20
  have l11 : m11 k c ≤ Mh 1 1 k c := b11
  have l22 : m22 k c ≤ Mh 2 2 k c := b22
  have hd2 : 0 ≤ δ ^ 2 := sq_nonneg _
  have he2 : 0 ≤ e ^ 2 := sq_nonneg _
  have heq : 0 ≤ e := he
  have hom := sq_nonneg (om (nsq k))
  have s1 := mul_le_mul_of_nonneg_left u10 (show 0 ≤ 2 * e ^ 2 by positivity)
  have s2 := mul_le_mul_of_nonneg_left l20 (show 0 ≤ 4 * (29 / 100) * e by positivity)
  have s3 := mul_le_mul_of_nonneg_left u30 (show (0 : ℝ) ≤ 2 * (29 / 100) ^ 2 by positivity)
  have s4 := mul_le_mul_of_nonneg_left u20 (show 0 ≤ 2 * δ ^ 2 by positivity)
  have s5 := mul_le_mul_of_nonneg_left l11 (show 0 ≤ 2 * δ ^ 2 by positivity)
  have s6 := mul_le_mul_of_nonneg_left u31 (show (0 : ℝ) ≤ 2 * (29 / 100) ^ 2 by positivity)
  have s7 := mul_le_mul_of_nonneg_left l22 (show (0 : ℝ) ≤ 2 * (29 / 100) ^ 2 by positivity)
  have hmain : (2 * e ^ 2 * Mh 1 0 k c' - 4 * (29 / 100) * e * Mh 2 0 k c'
      + 2 * (29 / 100) ^ 2 * Mh 3 0 k c')
      + (2 * δ ^ 2 * (Mh 2 0 k c - Mh 1 1 k c) + 2 * (29 / 100) ^ 2 * (Mh 3 1 k c - Mh 2 2 k c)) ≤
      ((2 * e ^ 2 * m10 k c' - 4 * (29 / 100) * e * m20 k c' + 2 * (29 / 100) ^ 2 * m30 k c')
        + (2 * δ ^ 2 * (m20 k c - m11 k c) + 2 * (29 / 100) ^ 2 * (m31 k c - m22 k c)))
      + ((2 * e ^ 2 * (E10 : ℝ) + 2 * (29 / 100) ^ 2 * (E30 : ℝ)) * absSq k
        + 2 * δ ^ 2 * (E20 : ℝ) + 2 * (29 / 100) ^ 2 * (E31 : ℝ)) * nR c := by
    clear a10 b20 a30 a20 b11 a31 b22 e10 e20 e30 e31 u10 u30 u20 u31 l20 l11 l22 hn hC hs hom
    linarith
  have := mul_le_mul_of_nonneg_left hmain hom
  calc _ = om (nsq k) ^ 2 * ((2 * e ^ 2 * Mh 1 0 k c' - 4 * (29 / 100) * e * Mh 2 0 k c'
      + 2 * (29 / 100) ^ 2 * Mh 3 0 k c')
      + (2 * δ ^ 2 * (Mh 2 0 k c - Mh 1 1 k c) + 2 * (29 / 100) ^ 2 * (Mh 3 1 k c - Mh 2 2 k c))) := by
        ring
    _ ≤ _ := this
    _ = _ := by ring

/-- The low forms. -/
def LX (k : Mode) (HC rC : ℕ) (v : R3) : ℝ := ∑ p ∈ boxM 10, (fa1 k HC rC p : ℝ) * dR p v ^ 2

def LY (k : Mode) (C HC rC : ℕ) (v : R3) : ℝ := ∑ p ∈ boxM 10, (fa2 k C HC rC p : ℝ) * dR p v ^ 2

/-- The low zone is below the low forms. -/
theorem lo_le (k : Mode) (hk : k ≠ 0) (c : R3) :
    ∑ p ∈ loF, wtL k p * pterm k c p ≤
      9 * (root (nsq k) : ℝ) * root (nsq k) / lowS *
        (LX k (metric (nsq k)) (root (nsq k)) (crR k c)
          + LY k (nsq k) (metric (nsq k)) (root (nsq k)) c) := by
  set K := 9 * (root (nsq k) : ℝ) * root (nsq k) / lowS with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ p ∈ loF, wtL k p * pterm k c p ≤
      K * ((fa1 k (metric (nsq k)) (root (nsq k)) p : ℝ) * dR p (crR k c) ^ 2
        + (fa2 k (nsq k) (metric (nsq k)) (root (nsq k)) p : ℝ) * dR p c ^ 2) := by
    intro p hp
    obtain ⟨h1, h2⟩ := w_le_ceil hk (mem_loF.1 hp)
    have s1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (dR p (crR k c)))
    have s2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (dR p c))
    unfold pterm
    calc wtL k p * (w1 k p * dR p (crR k c) ^ 2 + w2 k p * dR p c ^ 2)
        = wtL k p * w1 k p * dR p (crR k c) ^ 2 + wtL k p * w2 k p * dR p c ^ 2 := by ring
      _ ≤ _ := add_le_add s1 s2
      _ = _ := by ring
  refine (sum_le_sum hpt).trans ?_
  unfold LX LY
  rw [← sum_add_distrib]
  refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => ?_).trans ?_
  · positivity
  · rw [mul_sum]

/-- From `3 X ≤ Y` to `X ≤ Y/3`. -/
lemma le_third {X : ℝ≥0∞} {Y : ℝ} (h : 3 * X ≤ ENNReal.ofReal Y) :
    X ≤ ENNReal.ofReal (Y / 3) := by
  have e : X = ENNReal.ofReal (1 / 3) * (3 * X) := by
    rw [← mul_assoc, ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [e]
  calc ENNReal.ofReal (1 / 3) * (3 * X) ≤ ENNReal.ofReal (1 / 3) * ENNReal.ofReal Y :=
        mul_le_mul_right h _
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- Bounds on the metric for the tail conditions. -/
lemma hm_small {k : Mode} (hk : k ≠ 0) (hC : nsq k < 1936) :
    0 ≤ hm k - 117 / 500 ∧ hm k - 117 / 500 ≤ 2 * (29 / 100) * (34 : ℝ) ^ 2 := by
  have h1 : 1 ≤ nsq k := nsq_pos_of_ne hk
  have h2 : hmet 1 ≤ hmet (nsq k) := by
    rcases Nat.lt_or_ge 1 (nsq k) with h | h
    · exact (hmet_lt_hmet le_rfl h).le
    · rw [show nsq k = 1 by omega]
  have h3 : hmet (nsq k) ≤ hmet 1936 := (hmet_lt_hmet h1 hC).le
  rw [hmet_one] at h2
  rw [hmet_affine (j := 1936) (by norm_num)] at h3
  unfold hm
  norm_num at h3 ⊢
  constructor <;> linarith

/-- **The tail of a row of the matrix band.** -/
theorem tail_row {k : Mode} (hk : k ≠ 0) (hk1 : nsq k < 1936) {cK : ℕ} (h1 : nsq k ≤ cK * cK)
    (h2 : cK + 34 ≤ 78) (c : R3) (hc : dR k c = 0) :
    let ρ : ℝ := ((78 - cK : ℕ) : ℝ)
    let δ := hm k - 29 / 100 * absSq k - 117 / 500
    offSum k c 78 ≤ ENNReal.ofReal (om (nsq k) ^ 2 *
      (1 + δ ^ 2 / ((29 / 100) ^ 2 * ρ ^ 4)) * (absSq k * (4 * (15 * ρ⁻¹) + absSq k *
        (15 * ρ⁻¹ ^ 3))) / 3 * nR c) := by
  intro ρ δ
  set r := 78 - cK with hr
  have hr34 : 34 ≤ r := by omega
  have hρ34 : (34 : ℝ) ≤ ρ := by
    have : ((34 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr34
    simpa [ρ] using this
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨he0, he1⟩ := hm_small hk hk1
  set ε := δ ^ 2 / ((29 / 100) ^ 2 * ρ ^ 4) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hsq : (34 : ℝ) ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (by norm_num) hρ34 2
  have ht := tail_le k hk c hc 78 r ε (by omega)
    (by
      have : 78 - r = cK := by omega
      rw [this, pow_two]; exact h1)
    (by nlinarith) hε0 he0
    (by
      refine he1.trans ?_
      nlinarith)
    (by
      have : ε * (29 / 100) ^ 2 * ρ ^ 4 = δ ^ 2 := by
        rw [hε]; field_simp
      exact this.ge)
  have hS4 := S4_le r (by omega)
  have hS6 := S6_le r (by omega)
  have hC0 := absSq_nonneg' k
  have hn := nR_nonneg c
  have hsum : 4 * Sm 2 r + ENNReal.ofReal (absSq k) * Sm 3 r ≤
      ENNReal.ofReal (4 * (15 * ρ⁻¹) + absSq k * (15 * ρ⁻¹ ^ 3)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hC0,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    refine add_le_add ?_ (mul_le_mul_right hS6 _)
    rw [show ENNReal.ofReal 4 = 4 by norm_num]
    exact mul_le_mul_right hS4 _
  have h3 : 3 * offSum k c 78 ≤ ENNReal.ofReal (om (nsq k) ^ 2 * (1 + ε) * (absSq k * nR c) *
      (4 * (15 * ρ⁻¹) + absSq k * (15 * ρ⁻¹ ^ 3))) := by
    refine ht.trans ((mul_le_mul_right hsum _).trans (le_of_eq ?_))
    exact (ENNReal.ofReal_mul (by positivity)).symm
  refine (le_third h3).trans (le_of_eq ?_)
  congr 1
  ring

end Row
end OVNS
