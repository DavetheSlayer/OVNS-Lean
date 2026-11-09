import OddViscousNS.Quant.Joint.Metric.PathX2

/-!
# The block forms against the library's `X₁` (step J5, node N13)

The source of `X₂` is `X₁𝓛 + 𝓛*X₁`, of `Z` is `X₁(B)`: blocks.  The library's `X₁` identities
(`metricCorr2_identity`, `h1Energy_identity`) are in `pair`, `X1op`.  This file is the bridge, at a
time when everything converges absolutely:
* `X1Form_re`: `Re⟨z_A, X₁(h) z_B⟩ = 2 pair s A (X1op h B) + 2 pair s B (X1op h A)`, the polarized
  form (`metBil2`, `X1bil`) on real fields.  One edge at a time: this is the absolute summability of
  a single edge, which §7 of the pilot report left open.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. One edge of `X₁` -/

/-- An edge against a multiplier bound at its labels. -/
lemma norm_blk_le_of {m : Mult} {B : ℝ} {p k j : Mode} (hB0 : 0 ≤ B)
    (hm : ∀ a b c, ‖m a b c p j‖ ≤ B) (hk : p + j = k) (v : V3) :
    ‖blk m p k j v‖ ≤ 8 * B * absk k * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := absk_nonneg k; positivity) fun w => ?_
  rw [blk_apply]
  set E := B * (absk k * ‖v‖ * ‖w‖) with hE
  have hterm : ∀ a b c, ‖m a b c p j • hel c k (vert p j (hel a p v) (hel b j w))‖ ≤ E := by
    intro a b c
    rw [norm_smul]
    have h1 : ‖hel c k (vert p j (hel a p v) (hel b j w))‖ ≤
        absk (p + j) * (‖hel a p v‖ * ‖hel b j w‖) :=
      (norm_hel_le _ _ _).trans (norm_vert_le₂ p j (dotM_hel a p v) (dotM_hel b j w))
    have h2 : ‖hel a p v‖ * ‖hel b j w‖ ≤ ‖v‖ * ‖w‖ :=
      mul_le_mul (norm_hel_le _ _ _) (norm_hel_le _ _ _) (norm_nonneg _) (norm_nonneg _)
    rw [hk] at h1
    have h3 : ‖hel c k (vert p j (hel a p v) (hel b j w))‖ ≤ absk k * ‖v‖ * ‖w‖ := by
      calc _ ≤ absk k * (‖v‖ * ‖w‖) := h1.trans (mul_le_mul_of_nonneg_left h2 (absk_nonneg k))
        _ = _ := by ring
    exact mul_le_mul (hm a b c) h3 (norm_nonneg _) hB0
  refine (norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
    norm_sum_le_of_le _ fun c _ => hterm a b c).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, hE]
  push_cast
  ring

/-- The forward edge of a metric form, on the energy coordinates. -/
def E1 (s : ℕ) (r τ : ℝ) (h A B : Field) (x : Mode × Mode) : ℂ :=
  inner ℂ (zOf s A x.1) (Xf s r τ x.2 x.1 (x.1 - x.2) (h x.2) (zOf s B (x.1 - x.2)))

lemma E1_eq (s : ℕ) (r τ : ℝ) (h A B : Field) (hB0 : B 0 = 0) (x : Mode × Mode) :
    E1 s r τ h A B x = ((2 * absk x.1 ^ (2 * s) : ℝ) : ℂ) *
      inner ℂ (A x.1) (blk (metM r τ) x.2 x.1 (x.1 - x.2) (h x.2) (B (x.1 - x.2))) := by
  by_cases hj : x.1 - x.2 = 0
  · simp [E1, hj, hB0, zOf]
  · have hJ : absk (x.1 - x.2) ≠ 0 := absk_eq_zero.not.2 hj
    simp only [E1, Xf, zOf, smul_apply, map_smul, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, wt, div_pow]
    push_cast
    have hJ' : ((absk (x.1 - x.2) : ℂ)) ≠ 0 := by exact_mod_cast hJ
    field_simp
    ring

/-- The positive form of an edge. -/
lemma sb_edge {α f β : Mode → ℝ} {A C : ℝ} (hα : L2B α A)
    (h1 : ∀ k, Summable fun p => f p * β (k - p)) (h2 : L2B (convR f β) C) (hf : ∀ k, 0 ≤ f k)
    (hβ : ∀ k, 0 ≤ β k) : SB (fun x : Mode × Mode => α x.1 * (f x.2 * β (x.1 - x.2))) (A * C) := by
  have hc : SB (fun k => α k * convR f β k) (A * C) := hα.pair h2
  have hin : ∀ k, SB (fun p => α k * (f p * β (k - p))) (α k * convR f β k) := fun k => by
    refine ⟨(h1 k).mul_left _, ?_⟩
    rw [tsum_mul_left]
    exact le_rfl
  exact SB.prod (H := fun x : Mode × Mode => α x.1 * (f x.2 * β (x.1 - x.2)))
    (fun x => mul_nonneg (hα.nn _) (mul_nonneg (hf _) (hβ _))) hin hc

/-- The size of the forward edge. -/
lemma norm_E1_le {s : ℕ} (hs : s = 1 ∨ s = 2) (r τ : ℝ) {h A B : Field} (hB0 : B 0 = 0)
    (x : Mode × Mode) :
    ‖E1 s r τ h A B x‖ ≤ 32 * (gr A x.1 * (nrm h x.2 * up (nrm B) (x.1 - x.2)) +
      gr A x.1 * (up (nrm h) x.2 * nrm B (x.1 - x.2))) := by
  obtain ⟨k, p⟩ := x
  simp only
  have hnn : 0 ≤ 32 * (gr A k * (nrm h p * up (nrm B) (k - p)) +
      gr A k * (up (nrm h) p * nrm B (k - p))) := by
    have h1 := gr_nonneg A k
    have h2 := up_nrm_nonneg B (k - p)
    have h3 := up_nrm_nonneg h p
    have h4 : 0 ≤ nrm h p := norm_nonneg _
    have h5 : 0 ≤ nrm B (k - p) := norm_nonneg _
    positivity
  by_cases hk : k = 0
  · subst hk
    rw [E1_eq s r τ h A B hB0]
    have h0 : absk (0 : Mode) ^ (2 * s) = 0 := by
      rw [absk_eq_zero.2 rfl]
      rcases hs with rfl | rfl <;> norm_num
    simpa [h0] using hnn
  by_cases hj : k - p = 0
  · have : zOf s B (k - p) = 0 := by simp [hj, zOf, hB0]
    simpa [E1, this, map_zero, inner_zero_right] using hnn
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
  have hJ1 : 1 ≤ absSq (k - p) := one_le_absSq hj
  have ekj : p + (k - p) = k := by abel
  have hm : ∀ a b c, ‖metM r τ a b c p (k - p)‖ ≤ 1 / absSq k := fun a b c => by
    have := norm_metM_le_absSq r τ a b c p (k - p)
    rwa [ekj] at this
  have hb := norm_blk_le_of (m := metM r τ) (by have := absSq_nonneg k; positivity) hm ekj (h p)
  have hin : ‖inner ℂ (A k) (blk (metM r τ) p k (k - p) (h p) (B (k - p)))‖ ≤
      ‖A k‖ * (8 * (1 / absSq k) * absk k * ‖h p‖ * ‖B (k - p)‖) := by
    refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  rw [E1_eq s r τ h A B hB0, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hAs : absSq k = absk k ^ 2 := (absk_sq k).symm
  set K := absk k
  set J2 := absSq (k - p)
  set P2 := absSq p
  have hP2 : 0 ≤ P2 := absSq_nonneg p
  have ha := norm_nonneg (A k)
  have hh := norm_nonneg (h p)
  have hbb := norm_nonneg (B (k - p))
  have hk2 : K ^ 2 ≤ 2 * (P2 + J2) := by
    rw [← hAs]
    exact absSq_le₂ ekj.symm
  have e0 : 2 * K ^ (2 * s) * (‖A k‖ * (8 * (1 / absSq k) * K * ‖h p‖ * ‖B (k - p)‖)) =
      16 * K ^ (2 * s) / K * (‖A k‖ * ‖h p‖ * ‖B (k - p)‖) := by
    rw [hAs]
    field_simp
    ring
  refine (mul_le_mul_of_nonneg_left hin (by positivity)).trans ?_
  rw [e0]
  have hT : 0 ≤ ‖A k‖ * ‖h p‖ * ‖B (k - p)‖ := by positivity
  simp only [gr, nrm, up]
  rcases hs with rfl | rfl
  · have e1 : 16 * K ^ (2 * 1) / K = 16 * K := by
      field_simp
    rw [e1]
    have h1 : ‖B (k - p)‖ ≤ J2 * ‖B (k - p)‖ := le_mul_of_one_le_left hbb hJ1
    have hJ0 : 0 ≤ J2 := by linarith
    have h2 : 0 ≤ K * ‖A k‖ * (P2 * ‖h p‖ * ‖B (k - p)‖) := by positivity
    have h3 : K * ‖A k‖ * (‖h p‖ * ‖B (k - p)‖) ≤ K * ‖A k‖ * (‖h p‖ * (J2 * ‖B (k - p)‖)) := by
      gcongr
    have h4 : 0 ≤ K * ‖A k‖ * (‖h p‖ * (J2 * ‖B (k - p)‖)) := by positivity
    calc 16 * K * (‖A k‖ * ‖h p‖ * ‖B (k - p)‖) = 16 * (K * ‖A k‖ * (‖h p‖ * ‖B (k - p)‖)) := by
          ring
      _ ≤ 32 * (K * ‖A k‖ * (‖h p‖ * (J2 * ‖B (k - p)‖)) +
          K * ‖A k‖ * (P2 * ‖h p‖ * ‖B (k - p)‖)) := by linarith
  · have e1 : 16 * K ^ (2 * 2) / K = 16 * K * K ^ 2 := by
      field_simp
    rw [e1]
    have h2 := mul_le_mul_of_nonneg_left hk2 (by positivity :
      0 ≤ 16 * K * (‖A k‖ * ‖h p‖ * ‖B (k - p)‖))
    calc _ = 16 * K * (‖A k‖ * ‖h p‖ * ‖B (k - p)‖) * K ^ 2 := by ring
      _ ≤ _ := h2
      _ = _ := by ring

/-- The forward edge is absolutely summable. -/
lemma E1_summable {s : ℕ} (hs : s = 1 ∨ s = 2) (r τ : ℝ) {h A B : Field} (hh : MZ 2 h)
    (hA : InH 1 A) (hB : MZ 2 B) : Summable fun x => ‖E1 s r τ h A B x‖ := by
  have hα := l2B_gr hA
  have h1 := l1B_nrm hh.inH
  have h2 := l1B_nrm hB.inH
  have u1 := l2B_up hh.inH
  have u2 := l2B_up hB.inH
  obtain ⟨c1, d1⟩ := h1.conv_l2 u2
  obtain ⟨c2, d2⟩ := u1.conv_l1 h2
  have s1 := sb_edge hα c1 d1 h1.nn u2.nn
  have s2 := sb_edge hα c2 d2 u1.nn h2.nn
  have hS := ((s1.add s2).const_mul (by norm_num : (0 : ℝ) ≤ 32)).1
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_E1_le hs r τ hB.mean) hS

/-- The sum of a forward edge. -/
lemma tsum_E1 {s : ℕ} (hs : s = 1 ∨ s = 2) (r τ : ℝ) {h A B : Field} (hh : MZ 2 h)
    (hA : InH 1 A) (hB : MZ 2 B) :
    (∑' x, E1 s r τ h A B x).re = 2 * pair s A (X1op r τ h B) := by
  have hS := (E1_summable hs r τ hh hA hB).of_norm
  rw [hS.tsum_prod]
  have hin : ∀ k, ∑' p, E1 s r τ h A B (k, p) =
      ((2 * absk k ^ (2 * s) : ℝ) : ℂ) * inner ℂ (A k) (X1op r τ h B k) := fun k => by
    have hB1 : Summable fun p => blk (metM r τ) p k (k - p) (h p) (B (k - p)) := by
      have c1 := (l1B_nrm hh.inH).conv_l2 (l2B_up hB.inH)
      refine Summable.of_norm_bounded (((c1.1 k).mul_left (8 * (1 + absk k)))) fun p => ?_
      have hb := norm_blk_le (metM_bdd r τ) (show p + (k - p) = k by abel) (h p)
      have h1 := (ContinuousLinearMap.le_opNorm (blk (metM r τ) p k (k - p) (h p)) (B (k - p))).trans
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
      refine h1.trans ?_
      have hKK := absk_nonneg k
      have hhh := norm_nonneg (h p)
      have hbb := norm_nonneg (B (k - p))
      have hup : ‖B (k - p)‖ ≤ up (nrm B) (k - p) := by
        by_cases hj : k - p = 0
        · simp [hj, hB.mean, up, nrm]
        · exact le_mul_of_one_le_left hbb (one_le_absSq hj)
      calc 8 * absk k * ‖h p‖ * ‖B (k - p)‖ ≤ 8 * (1 + absk k) * ‖h p‖ * up (nrm B) (k - p) := by
            gcongr
            linarith
        _ = _ := by simp only [nrm]; ring
    have e : X1op r τ h B k = ∑' p, blk (metM r τ) p k (k - p) (h p) (B (k - p)) :=
      Qm_eq_tsum_blk _ _ _ _
    simp only [E1_eq s r τ h A B hB.mean]
    rw [e, inner_tsum _ hB1, tsum_mul_left]
  simp only [hin]
  have hs2 : Summable fun k => ((2 * absk k ^ (2 * s) : ℝ) : ℂ) * inner ℂ (A k) (X1op r τ h B k) :=
    hS.prod.congr fun k => hin k
  rw [Complex.re_tsum hs2, pair, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [Complex.re_ofReal_mul]
  have hw : sobWeight (s : ℝ) k = absk k ^ (2 * s) := by
    rcases hs with rfl | rfl
    · simp [sobWeight_one, absk_sq]
    · simp only [Nat.cast_ofNat, sobWeight_two, ← absk_sq k]
      ring
  rw [hw]
  ring

/-- **The polarized form of `X₁`** (`metBil2`, `X1bil`): on a real slow field, at both weights. -/
theorem X1Form_re {s : ℕ} (hs : s = 1 ∨ s = 2) (r τ : ℝ) {h A B : Field} (hh : MZ 2 h)
    (hr : IsReal h) (hA : MZ 2 A) (hB : MZ 2 B) :
    (X1Form s r τ h (zOf s A) (zOf s B)).re =
      2 * pair s A (X1op r τ h B) + 2 * pair s B (X1op r τ h A) := by
  have hA1 : InH 1 A := hA.inH.mono (by norm_num)
  have hB1 : InH 1 B := hB.inH.mono (by norm_num)
  set e : Mode × Mode ≃ Mode × Mode :=
    { toFun := fun x => (x.1 - x.2, -x.2)
      invFun := fun x => (x.1 - x.2, -x.2)
      left_inv := fun ⟨k, p⟩ => Prod.ext (show k - p - -p = k by abel) (neg_neg p)
      right_inv := fun ⟨k, p⟩ => Prod.ext (show k - p - -p = k by abel) (neg_neg p) } with he
  have s1 := (E1_summable hs r τ hh hA1 hB).of_norm
  have s2 := (E1_summable hs r τ hh hB1 hA).of_norm
  have hsplit : ∀ x : Mode × Mode, inner ℂ (zOf s A x.1)
      (X1b s r τ x.2 x.1 (x.1 - x.2) (h x.2) (zOf s B (x.1 - x.2))) =
      E1 s r τ h A B x + conj (E1 s r τ h B A (e x)) := fun x => by
    rw [X1b_eq_add, add_apply, inner_add_right]
    congr 1
    have hc : conjV (h x.2) = h (-x.2) := (hr x.2).symm
    have e1 : x.1 - x.2 - -x.2 = x.1 := by abel
    simp only [E1, he, Equiv.coe_fn_mk, e1, Xr, hc, ContinuousLinearMap.adjoint_inner_right]
    rw [inner_conj_symm]
  have s3 : Summable fun x => conj (E1 s r τ h B A (e x)) :=
    (Complex.hasSum_conj'.2 ((e.summable_iff.2 s2).hasSum)).summable
  have hval : (∑' x, conj (E1 s r τ h B A (e x))).re = (∑' x, E1 s r τ h B A x).re := by
    have h1 : ∑' x, conj (E1 s r τ h B A (e x)) = conj (∑' x, E1 s r τ h B A (e x)) :=
      (Complex.hasSum_conj'.2 ((e.summable_iff.2 s2).hasSum)).tsum_eq
    rw [h1, Complex.conj_re, e.tsum_eq (E1 s r τ h B A)]
  unfold X1Form
  simp only [hsplit]
  rw [s1.tsum_add s3, Complex.add_re, hval, tsum_E1 hs r τ hh hA1 hB, tsum_E1 hs r τ hh hB1 hA]

end OVNS.Quant.Metric

end
