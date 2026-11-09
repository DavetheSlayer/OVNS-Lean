import OddViscousNS.Quant.Joint.Metric.LinkSrc

/-!
# The joint energy identity, two-leaf level (step J5, node N13)

`joint_h1`, `joint_h2`: the library's energy identities (`h1Energy_identity`, `h2Energy_identity`)
with `X₂`, `Z` added to the metric.  The terms `X₁(𝓛)`, `X₁(B)` of the library's right side cancel
against the sources of `X₂`, `Z` (`src_X2_re`, `src_Z_re`), at almost every time; what is left is

`coreRHS`:  `2(⟨AˢF, X₁(h₀)F⟩ + ⟨AˢF, X₁(S)N_F⟩ + ⟨AˢN_F, X₁(S)F⟩)`,

with `h₀ = slowNL + B(S,S)`, `N_F = fastNL + 𝓛F`, plus half of the four insertions in each of
`X₂`, `Z`.  `Links.lean`, `LinkSrc.lean` hold the links; this file does the bookkeeping.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (Qm_two_le Qm_one_le ae_inH3_split h2RHS h2Energy h2Energy_identity cubicHeat2)

noncomputable section

namespace OVNS.Quant.Metric

/-! ### Additivity -/

/-- Sobolev membership from a weighted bound. -/
lemma inH_of_le {m : ℕ} {c : Field} {a : Mode → ℝ} (ha : Summable fun k => a k ^ 2)
    (h : ∀ k, absk k ^ m * ‖c k‖ ≤ a k) (hc0 : c 0 = 0) : InH m c := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg _ k) (by positivity))
    (fun k => ?_) ha
  by_cases hk : k = 0
  · subst hk
    simp only [hc0, norm_zero]
    have := sq_nonneg (a 0)
    simpa using this
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
  have hw : sobWeight (m : ℝ) k = (absk k ^ m) ^ 2 := by
    simp only [sobWeight, hk, ite_false]
    rw [show (2 : ℝ) * m = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul', ]
  rw [hw, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (h k) 2

/-- A bounded block on two `ℓ²` fields is summable. -/
lemma blk_summable {m : Mult} (hm : m.Bdd) {f g : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hg : Summable fun k => ‖g k‖ ^ 2) (k : Mode) :
    Summable fun p => blk m p k (k - p) (f p) (g (k - p)) := by
  have hg' : Summable fun p => ‖g (k - p)‖ ^ 2 := (Equiv.subLeft k).summable_iff.2 hg
  have h0 : Summable fun p => ‖f p‖ * ‖g (k - p)‖ :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun p => by nlinarith only [sq_nonneg (‖f p‖ - ‖g (k - p)‖)]) (hf.add hg')
  refine Summable.of_norm_bounded (h0.mul_left (8 * absk k)) fun p => ?_
  have hb := norm_blk_le hm (show p + (k - p) = k by abel) (f p)
  have h1 := (ContinuousLinearMap.le_opNorm (blk m p k (k - p) (f p)) (g (k - p))).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  exact h1.trans (le_of_eq (by ring))

lemma Qm_add_left_l2 {m : Mult} (hm : m.Bdd) {f f' g : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hf' : Summable fun k => ‖f' k‖ ^ 2) (hg : Summable fun k => ‖g k‖ ^ 2) :
    Qm m (f + f') g = Qm m f g + Qm m f' g := by
  funext k
  rw [Pi.add_apply, Qm_eq_tsum_blk, Qm_eq_tsum_blk, Qm_eq_tsum_blk,
    ← (blk_summable hm hf hg k).tsum_add (blk_summable hm hf' hg k)]
  refine tsum_congr fun p => ?_
  simp only [Pi.add_apply, blk_add_leaf, add_apply]

lemma Qm_add_right_l2 {m : Mult} (hm : m.Bdd) {f g g' : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hg : Summable fun k => ‖g k‖ ^ 2) (hg' : Summable fun k => ‖g' k‖ ^ 2) :
    Qm m f (g + g') = Qm m f g + Qm m f g' := by
  funext k
  rw [Pi.add_apply, Qm_eq_tsum_blk, Qm_eq_tsum_blk, Qm_eq_tsum_blk,
    ← (blk_summable hm hf hg k).tsum_add (blk_summable hm hf hg' k)]
  refine tsum_congr fun p => ?_
  simp only [Pi.add_apply, map_add]

/-- The pairing is additive in the first slot, in the dual scale. -/
lemma pair_add_left' {σ : ℝ} {c c' F : Field} (hc : InH (σ - 1) c) (hc' : InH (σ - 1) c')
    (hF : InH (σ + 1) F) : pair σ (c + c') F = pair σ c F + pair σ c' F := by
  have e : ∀ c : Field, ∀ k, sobWeight σ k * (inner ℂ (c k) (F k)).re =
      sobWeight σ k * (inner ℂ (F k) (c k)).re := fun c k => by
    have := inner_re_symm (𝕜 := ℂ) (c k) (F k)
    simp only [RCLike.re_to_complex] at this
    rw [this]
  have s1 : ∀ c : Field, InH (σ - 1) c →
      Summable fun k => sobWeight σ k * (inner ℂ (c k) (F k)).re := fun c hc => by
    simp only [e]
    exact pair_summable hF hc
  simp only [pair]
  rw [← (s1 c hc).tsum_add (s1 c' hc')]
  refine tsum_congr fun k => ?_
  rw [Pi.add_apply, inner_add_left, Complex.add_re, mul_add]

/-! ### Regularity of `X₁` -/

/-- The gain of the metric symbol: one derivative. -/
lemma mul_norm_X1op_le (r τ : ℝ) {h B : Field} {k : Mode} (hk : k ≠ 0)
    (hs : Summable fun p => ‖h p‖ * ‖B (k - p)‖) :
    absk k * ‖X1op r τ h B k‖ ≤ 8 * ∑' p, ‖h p‖ * ‖B (k - p)‖ := by
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
  have hb : ∀ p, ‖blk (metM r τ) p k (k - p) (h p) (B (k - p))‖ ≤
      8 / absk k * (‖h p‖ * ‖B (k - p)‖) := fun p => by
    have ekj : p + (k - p) = k := by abel
    have hm : ∀ a b c, ‖metM r τ a b c p (k - p)‖ ≤ 1 / absSq k := fun a b c => by
      have := norm_metM_le_absSq r τ a b c p (k - p)
      rwa [ekj] at this
    have h1 := norm_blk_le_of (m := metM r τ) (by have := absSq_nonneg k; positivity) hm ekj (h p)
    have h2 := (ContinuousLinearMap.le_opNorm (blk (metM r τ) p k (k - p) (h p)) (B (k - p))).trans
      (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    refine h2.trans (le_of_eq ?_)
    rw [← absk_sq k]
    field_simp
  have hs2 : Summable fun p => ‖blk (metM r τ) p k (k - p) (h p) (B (k - p))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hs.mul_left _)
  rw [X1op, Qm_eq_tsum_blk]
  calc absk k * ‖∑' p, blk (metM r τ) p k (k - p) (h p) (B (k - p))‖
      ≤ absk k * ∑' p, 8 / absk k * (‖h p‖ * ‖B (k - p)‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hK.le
        exact (norm_tsum_le_tsum_norm hs2).trans (hs2.tsum_le_tsum hb (hs.mul_left _))
    _ = _ := by
        rw [tsum_mul_left]
        field_simp

/-- `X₁(h) B ∈ H¹`. -/
lemma inH_one_X1op (r τ : ℝ) {h B : Field} {A W : ℝ}
    (hb : (∀ k, Summable fun p => nrm h p * nrm B (k - p)) ∧ L2B (convR (nrm h) (nrm B)) (A * W)) :
    InH 1 (X1op r τ h B) := by
  have hL := hb.2
  have ha : Summable fun k => (8 * convR (nrm h) (nrm B) k) ^ 2 := by
    simp only [mul_pow]
    exact hL.s.mul_left _
  have := inH_of_le (m := 1) (c := X1op r τ h B) ha (fun k => ?_) (OVNS.Quant.H2.Qm_zero_mode _ _ _)
  · simpa using this
  by_cases hk : k = 0
  · subst hk
    simp only [absk_eq_zero.2 rfl]
    have := hL.nn 0
    simp only [ne_eq, one_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity
  · rw [pow_one]
    exact mul_norm_X1op_le r τ hk (hb.1 k)

/-- `X₁(h) B ∈ H³` for `h, B ∈ H²`. -/
lemma inH_three_X1op (r τ : ℝ) {h B : Field} (hh : MZ 2 h) (hB : MZ 2 B) :
    InH 3 (X1op r τ h B) := by
  obtain ⟨c1, d1⟩ := (l2B_up hh.inH).conv_l1 (l1B_nrm hB.inH)
  obtain ⟨c2, d2⟩ := (l1B_nrm hh.inH).conv_l2 (l2B_up hB.inH)
  set a : Mode → ℝ := fun k => 16 * (convR (up (nrm h)) (nrm B) k + convR (nrm h) (up (nrm B)) k)
    with ha
  have hs : Summable fun k => a k ^ 2 := by
    have h1 := (d1.s.mul_left (2 * 16 ^ 2)).add (d2.s.mul_left (2 * 16 ^ 2))
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => ?_) h1
    simp only [ha]
    nlinarith only [sq_nonneg (convR (up (nrm h)) (nrm B) k - convR (nrm h) (up (nrm B)) k)]
  have := inH_of_le (m := 3) (c := X1op r τ h B) hs (fun k => ?_) (OVNS.Quant.H2.Qm_zero_mode _ _ _)
  · simpa using this
  have h0 : 0 ≤ a k := by
    have := d1.nn k
    have := d2.nn k
    simp only [ha]
    positivity
  by_cases hk : k = 0
  · subst hk
    simpa [absk_eq_zero.2 rfl] using h0
  have hl1 : L1B (nrm h) (wiener h) := l1B_nrm hh.inH
  have hl2 : L1B (nrm B) (wiener B) := l1B_nrm hB.inH
  have hle : ∀ p, ‖h p‖ * ‖B (k - p)‖ ≤ absSq p * ‖h p‖ * ‖B (k - p)‖ +
      ‖h p‖ * (absSq (k - p) * ‖B (k - p)‖) := fun p => by
    by_cases hp : p = 0
    · subst hp
      simp only [hh.mean, norm_zero, zero_mul, mul_zero, add_zero, le_refl]
    · have h1 := one_le_absSq hp
      have h2 := mul_nonneg (norm_nonneg (h p)) (norm_nonneg (B (k - p)))
      have h3 : 0 ≤ ‖h p‖ * (absSq (k - p) * ‖B (k - p)‖) :=
        mul_nonneg (norm_nonneg _) (mul_nonneg (absSq_nonneg _) (norm_nonneg _))
      nlinarith only [h1, h2, h3]
  have hsum0 : Summable fun p => ‖h p‖ * ‖B (k - p)‖ :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hle
      ((c1 k).add (c2 k))
  have hK := absk_nonneg k
  have h1 := mul_norm_X1op_le r τ hk hsum0
  have hKK : absk k ^ 2 * ∑' p, ‖h p‖ * ‖B (k - p)‖ ≤
      2 * (convR (up (nrm h)) (nrm B) k + convR (nrm h) (up (nrm B)) k) := by
    rw [← tsum_mul_left]
    have hsS := ((c1 k).add (c2 k)).mul_left 2
    have e2 : convR (up (nrm h)) (nrm B) k + convR (nrm h) (up (nrm B)) k =
        ∑' p, (up (nrm h) p * nrm B (k - p) + nrm h p * up (nrm B) (k - p)) := by
      rw [(c1 k).tsum_add (c2 k)]
      rfl
    rw [e2, ← tsum_mul_left]
    refine (hsum0.mul_left _).tsum_le_tsum (fun p => ?_) hsS
    have ekj : k = p + (k - p) := by abel
    have h2 : absk k ^ 2 ≤ 2 * (absSq p + absSq (k - p)) := by
      rw [absk_sq]
      exact absSq_le₂ ekj
    have h3 := mul_le_mul_of_nonneg_right h2
      (mul_nonneg (norm_nonneg (h p)) (norm_nonneg (B (k - p))))
    refine h3.trans (le_of_eq ?_)
    simp only [up, nrm]
    ring
  calc absk k ^ 3 * ‖X1op r τ h B k‖ = absk k ^ 2 * (absk k * ‖X1op r τ h B k‖) := by ring
    _ ≤ absk k ^ 2 * (8 * ∑' p, ‖h p‖ * ‖B (k - p)‖) := by gcongr
    _ = 8 * (absk k ^ 2 * ∑' p, ‖h p‖ * ‖B (k - p)‖) := by ring
    _ ≤ 8 * (2 * (convR (up (nrm h)) (nrm B) k + convR (nrm h) (up (nrm B)) k)) := by gcongr
    _ = a k := by simp only [ha]; ring

/-! ### The bookkeeping at one time -/

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- What is left of the slow force: `h₀ = slowNL + B(S, S)`. -/
def hp (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : Field :=
  slowNL r g y u + Bslow (Sp r g y u)

/-- What is left of the fast force: `N_F = fastNL + 𝓛F`. -/
def NFp (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : Field :=
  fastNL r g y u + Lop (r * u) (Sp r g y u) (Fp r g y u)

/-- The `X₁` terms that survive the cancellation. -/
def coreRHS (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  2 * (pair s (Fp r g y u) (X1op r (r * u) (hp r g y u) (Fp r g y u)) +
    pair s (Fp r g y u) (X1op r (r * u) (Sp r g y u) (NFp r g y u)) +
    pair s (NFp r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u)))

/-- The four insertions of a form. -/
def insJ (𝔉 : Fam) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (Nzp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (Nzp s r g y u) +
    𝔉.form r (r * u) (slowNL r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (slowNL r g y u) (zp s r g y u) (zp s r g y u)

lemma rhs_eq (𝔉 : Fam) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    𝔉.rhs s r g y u = 𝔉.src (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u) +
      insJ 𝔉 s r g y u := by
  unfold Fam.rhs insJ
  abel

/-- **The cancellation**, at a time when `S, F ∈ H³`. -/
theorem core_eq {s : ℕ} (hs : s = 1 ∨ s = 2) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ}
    (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u))
    (hS3 : InH 3 (Sp r g y u)) :
    2 * (pair s (Fp r g y u) (X1op r (r * u) (slowNL r g y u) (Fp r g y u)) +
      pair s (Fp r g y u) (X1op r (r * u) (Sp r g y u) (fastNL r g y u)) +
      pair s (fastNL r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u))) +
      1 / 2 * ((famX2 s r).rhs s r g y u).re + 1 / 2 * ((famZ s r).rhs s r g y u).re =
    coreRHS s r g y u + 1 / 2 * (insJ (famX2 s r) s r g y u).re +
      1 / 2 * (insJ (famZ s r) s r g y u).re := by
  have hx := actual_adm h hu huT
  have hS2Adm : Adm 2 (Sp r g y u) := hx.PiS
  have hF2Adm : Adm 2 (Fp r g y u) := hx.PiF
  obtain ⟨M, -, hM⟩ := Fam.path_sup h hr hu (b := u) (lt_of_eq_of_lt rfl huT)
  obtain ⟨hS2, hF2, -, -, hN1, hh1, -, -, -⟩ := hM u ⟨le_rfl, le_rfl⟩
  have hSM : MZ 3 (Sp r g y u) := ⟨hS3, hS2.mean⟩
  have hFM : MZ 3 (Fp r g y u) := ⟨hF3, hF2.mean⟩
  have hS' := Fam.PiS_Sp r g y u
  have hF' := Fam.PiF_Fp r g y u
  set τ := r * u with hτ
  set S := Sp r g y u with hS
  set F := Fp r g y u with hF
  set NL := fastNL r g y u with hNL
  set h₀ := slowNL r g y u with hh₀
  have hL := mz_Lop τ hSM hFM
  have hB := mz_Bslow hSM
  have hsl : ((s : ℕ) : ℝ) - 1 ≤ 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsu : ((s : ℕ) : ℝ) + 1 ≤ 3 := by rcases hs with rfl | rfl <;> norm_num
  have l0 : ∀ {c : Field}, InH 1 c → Summable fun k => ‖c k‖ ^ 2 := fun hc =>
    summable_norm_sq_of_inH (hc.mono (by norm_num))
  have l2 : ∀ {c : Field}, MZ 2 c → Summable fun k => ‖c k‖ ^ 2 := fun hc =>
    summable_norm_sq_of_inH (hc.inH.mono (by norm_num))
  have up1 : ∀ {c : Field}, InH 1 c → InH ((s : ℝ) - 1) c := fun hc => hc.mono hsl
  have e1 : X1op r τ (hp r g y u) F = X1op r τ h₀ F + X1op r τ (Bslow S) F :=
    Qm_add_left_l2 (metM_bdd r τ) (l0 hh1) (l2 hB) (l2 hF2)
  have e2 : X1op r τ S (NFp r g y u) = X1op r τ S NL + X1op r τ S (Lop τ S F) :=
    Qm_add_right_l2 (metM_bdd r τ) (l2 hS2) (l0 hN1) (l2 hL)
  have i1 : InH 1 (X1op r τ h₀ F) :=
    inH_one_X1op r τ ((l2B_nrm (l0 hh1)).conv_l1 (l1B_nrm hF2.inH))
  have i2 : InH 1 (X1op r τ (Bslow S) F) :=
    inH_one_X1op r τ ((l2B_nrm (l2 hB)).conv_l1 (l1B_nrm hF2.inH))
  have i3 : InH 1 (X1op r τ S NL) :=
    inH_one_X1op r τ ((l1B_nrm hS2.inH).conv_l2 (l2B_nrm (l0 hN1)))
  have i4 : InH 1 (X1op r τ S (Lop τ S F)) :=
    inH_one_X1op r τ ((l1B_nrm hS2.inH).conv_l2 (l2B_nrm (l2 hL)))
  have i5 := inH_three_X1op r τ hS2 hF2
  have p1 := pair_add (σ := s) (hF3.mono hsu) (up1 i1) (up1 i2)
  have p2 := pair_add (σ := s) (hF3.mono hsu) (up1 i3) (up1 i4)
  have p3 := pair_add_left' (σ := s) (up1 hN1) (up1 (hL.inH.mono (by norm_num)))
    (i5.mono hsu)
  have src1 := src_X2_re hs hr τ hSM hS' hS2Adm.real hFM hF' hF2Adm.sol
  have src2 := src_Z_re hs hr τ hSM hS' hS2Adm hFM hF' hF2Adm.sol
  have e3 : coreRHS s r g y u = 2 * (pair s F (X1op r τ h₀ F + X1op r τ (Bslow S) F) +
      pair s F (X1op r τ S NL + X1op r τ S (Lop τ S F)) +
      (pair s NL (X1op r τ S F) + pair s (Lop τ S F) (X1op r τ S F))) := by
    rw [← p3, ← e1, ← e2]
    rfl
  rw [e3, p1, p2, rhs_eq, rhs_eq, Complex.add_re, Complex.add_re]
  have e4 : ((famX2 s r).src τ S S (zp s r g y u) (zp s r g y u)).re =
      4 * (pair s F (X1op r τ S (Lop τ S F)) + pair s (Lop τ S F) (X1op r τ S F)) := src1
  have e5 : ((famZ s r).src τ S S (zp s r g y u) (zp s r g y u)).re =
      4 * pair s F (X1op r τ (Bslow S) F) := src2
  rw [e4, e5]
  ring

/-! ### The two identities -/

/-- `⟨z, (X₂ + Z) z⟩` along the solution. -/
def corrJ (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  ((famX2 s r).val s r g y u).re + ((famZ s r).val s r g y u).re

/-- The integrand of the sum of the two forms. -/
lemma corrJ_identity {s : ℕ} (hs : s = 1 ∨ s = 2) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (fun u => ((famX2 s r).rhs s r g y u).re) volume a b ∧
      IntervalIntegrable (fun u => ((famZ s r).rhs s r g y u).re) volume a b ∧
      corrJ s r g y b - corrJ s r g y a = (∫ u in a..b, ((famX2 s r).rhs s r g y u).re) +
        ∫ u in a..b, ((famZ s r).rhs s r g y u).re := by
  obtain ⟨hI1, hE1⟩ := X2_identity hs h hr ha hab hb
  obtain ⟨hI2, hE2⟩ := Z_identity hs h hr ha hab hb
  have i1 : ∫ u in a..b, ((famX2 s r).rhs s r g y u).re =
      (∫ u in a..b, (famX2 s r).rhs s r g y u).re := Complex.reCLM.intervalIntegral_comp_comm hI1
  have i2 : ∫ u in a..b, ((famZ s r).rhs s r g y u).re =
      (∫ u in a..b, (famZ s r).rhs s r g y u).re := Complex.reCLM.intervalIntegral_comp_comm hI2
  refine ⟨⟨hI1.1.re, hI1.2.re⟩, ⟨hI2.1.re, hI2.2.re⟩, ?_⟩
  rw [i1, i2, ← hE1, ← hE2, Complex.sub_re, Complex.sub_re]
  simp only [corrJ]
  ring

/-- The right side of the joint `H¹` identity. -/
def joint1RHS (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -pair 1 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) - pair 1 (Fp r g y u) (Hpsi r g y u) +
    coreRHS 1 r g y u - cubicHeat r (r * u) (Fp r g y u) +
    cubicD 1 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) +
    1 / 2 * (insJ (famX2 1 r) 1 r g y u).re + 1 / 2 * (insJ (famZ 1 r) 1 r g y u).re

/-- The right side of the joint `H²` identity. -/
def joint2RHS (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -pair 2 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) - pair 2 (Fp r g y u) (Hpsi r g y u) +
    coreRHS 2 r g y u - cubicHeat2 r (r * u) (Fp r g y u) +
    cubicD 2 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) +
    1 / 2 * (insJ (famX2 2 r) 2 r g y u).re + 1 / 2 * (insJ (famZ 2 r) 2 r g y u).re

/-- **The joint `H¹` identity**, two-leaf level: `E + ½⟨z₁, (X₂ + Z) z₁⟩`. -/
theorem joint_h1 (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (joint1RHS r g y) volume a b ∧
      (h1Energy r g y b + 1 / 2 * corrJ 1 r g y b) - (h1Energy r g y a + 1 / 2 * corrJ 1 r g y a) +
        (∫ u in a..b, fastNorm 2 r g y u ^ 2) = ∫ u in a..b, joint1RHS r g y u := by
  obtain ⟨hI, hE⟩ := h1Energy_identity h hr ha hab hb
  obtain ⟨hI1, hI2, hE2⟩ := corrJ_identity (s := 1) (Or.inl rfl) h hr ha hab hb
  have hae : ∀ᵐ u, u ∈ uIoc a b → h1RHS r g y u + 1 / 2 * ((famX2 1 r).rhs 1 r g y u).re +
      1 / 2 * ((famZ 1 r).rhs 1 r g y u).re = joint1RHS r g y u := by
    rw [uIoc_of_le hab]
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 (ae_inH3_split h ha hab hb)]
      with u hu hmemu
    have hm := Ioc_subset_Icc_self hmemu
    have h3 := core_eq (s := 1) (Or.inl rfl) h hr (ha.trans hm.1) (lt_lifespan hm.2 hb)
      (hu hm).1 (hu hm).2
    simp only [Nat.cast_one] at h3
    unfold h1RHS joint1RHS
    change -pair 1 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) -
      pair 1 (Fp r g y u) (Hpsi r g y u) +
      2 * (pair 1 (Fp r g y u) (X1op r (r * u) (slowNL r g y u) (Fp r g y u)) +
        pair 1 (Fp r g y u) (X1op r (r * u) (Sp r g y u) (fastNL r g y u)) +
        pair 1 (fastNL r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u))) -
      cubicHeat r (r * u) (Fp r g y u) +
      cubicD 1 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) +
      1 / 2 * ((famX2 1 r).rhs 1 r g y u).re + 1 / 2 * ((famZ 1 r).rhs 1 r g y u).re = _
    linarith
  have hS := (hI.add (hI1.const_mul (1 / 2))).add (hI2.const_mul (1 / 2))
  have hIJ : IntervalIntegrable (joint1RHS r g y) volume a b := by
    refine hS.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hae
  refine ⟨hIJ, ?_⟩
  have e : ∫ u in a..b, joint1RHS r g y u = (∫ u in a..b, h1RHS r g y u) +
      1 / 2 * (∫ u in a..b, ((famX2 1 r).rhs 1 r g y u).re) +
      1 / 2 * ∫ u in a..b, ((famZ 1 r).rhs 1 r g y u).re := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hI (hI1.const_mul _),
      ← intervalIntegral.integral_add (hI.add (hI1.const_mul _)) (hI2.const_mul _)]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with u hu hmem
    exact (hu hmem).symm
  rw [e, ← hE]
  linarith

/-- **The joint `H²` identity**, two-leaf level: `½W + ½⟨z₂, (X₂ + Z) z₂⟩`. -/
theorem joint_h2 (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (joint2RHS r g y) volume a b ∧
      1 / 2 * (h2Energy r g y b + corrJ 2 r g y b) - 1 / 2 * (h2Energy r g y a + corrJ 2 r g y a) +
        (∫ u in a..b, fastNorm 3 r g y u ^ 2) = ∫ u in a..b, joint2RHS r g y u := by
  obtain ⟨hI, hE⟩ := h2Energy_identity h hr ha hab hb
  obtain ⟨hI1, hI2, hE2⟩ := corrJ_identity (s := 2) (Or.inr rfl) h hr ha hab hb
  have hae : ∀ᵐ u, u ∈ uIoc a b → h2RHS r g y u + 1 / 2 * ((famX2 2 r).rhs 2 r g y u).re +
      1 / 2 * ((famZ 2 r).rhs 2 r g y u).re = joint2RHS r g y u := by
    rw [uIoc_of_le hab]
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 (ae_inH3_split h ha hab hb)]
      with u hu hmemu
    have hm := Ioc_subset_Icc_self hmemu
    have h3 := core_eq (s := 2) (Or.inr rfl) h hr (ha.trans hm.1) (lt_lifespan hm.2 hb)
      (hu hm).1 (hu hm).2
    simp only [Nat.cast_ofNat] at h3
    unfold h2RHS joint2RHS
    change -pair 2 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) -
      pair 2 (Fp r g y u) (Hpsi r g y u) +
      2 * (pair 2 (Fp r g y u) (X1op r (r * u) (slowNL r g y u) (Fp r g y u)) +
        pair 2 (Fp r g y u) (X1op r (r * u) (Sp r g y u) (fastNL r g y u)) +
        pair 2 (fastNL r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u))) -
      cubicHeat2 r (r * u) (Fp r g y u) +
      cubicD 2 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) +
      1 / 2 * ((famX2 2 r).rhs 2 r g y u).re + 1 / 2 * ((famZ 2 r).rhs 2 r g y u).re = _
    linarith
  have hS := (hI.add (hI1.const_mul (1 / 2))).add (hI2.const_mul (1 / 2))
  have hIJ : IntervalIntegrable (joint2RHS r g y) volume a b := by
    refine hS.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hae
  refine ⟨hIJ, ?_⟩
  have e : ∫ u in a..b, joint2RHS r g y u = (∫ u in a..b, h2RHS r g y u) +
      1 / 2 * (∫ u in a..b, ((famX2 2 r).rhs 2 r g y u).re) +
      1 / 2 * ∫ u in a..b, ((famZ 2 r).rhs 2 r g y u).re := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hI (hI1.const_mul _),
      ← intervalIntegral.integral_add (hI.add (hI1.const_mul _)) (hI2.const_mul _)]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with u hu hmem
    exact (hu hmem).symm
  rw [e, ← hE]
  linarith

end OVNS.Quant.Metric

end
