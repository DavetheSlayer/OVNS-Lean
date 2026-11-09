import OddViscousNS.Quant.Joint.Metric.Links

/-!
# The sources of `X₂`, `Z` are the library's `X₁` terms (step J5, node N13)

`src_X2_re`: `Re⟨z, (X₁𝓛 + 𝓛*X₁) z⟩ = 4 [pair s F (X1op S (𝓛F)) + pair s (𝓛F) (X1op S F)]`.
`src_Z_re`: `Re⟨z, X₁(B) z⟩ = 4 pair s F (X1op B F)`.

These are the exact cancellations of the energy identity (LOCAL83): the terms the library's `X₁`
leaves on the right are the sources of `X₂` and `Z`.  They are Fubini: the slow leaves of the block
are summed first, at fixed exteriors, and give `𝓛F` (`zOf_Lop`) and `B(S,S)` (`Bslow_eq_tsum`).
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (Qm_two_le)

noncomputable section

namespace OVNS.Quant.Metric

variable {S F : Field} {s : ℕ} {r τ : ℝ}

/-- The majorant of a source. -/
def srcMaj (G F S : Field) (x : I3) : ℝ :=
  Phi₂ (gr G) (nrm F) (nrm S) (nrm S) x * E2 x + Phi₂ (nrm G) (nrm F) (gr S) (nrm S) x * E2 x +
    Phi₂ (nrm G) (nrm F) (nrm S) (gr S) x * E2 x

lemma srcMaj_nonneg (G F S : Field) (x : I3) : 0 ≤ srcMaj G F S x := by
  have n0 : ∀ k, 0 ≤ nrm G k := fun k => norm_nonneg (G k)
  have n1 : ∀ k, 0 ≤ nrm F k := fun k => norm_nonneg (F k)
  have n2 : ∀ k, 0 ≤ nrm S k := fun k => norm_nonneg (S k)
  have h1 := Phi₂_E2_nonneg (gr_nonneg G) n1 n2 n2 x
  have h2 := Phi₂_E2_nonneg n0 n1 (gr_nonneg S) n2 x
  have h3 := Phi₂_E2_nonneg n0 n1 n2 (gr_nonneg S) x
  unfold srcMaj
  linarith

lemma srcMaj_summable {G F S : Field} (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : InH 1 G)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hS : MZ 3 S) : Summable (srcMaj G F S) := by
  have hS2 : MZ 2 S := hS.mono' (by norm_num)
  have α := l2B_nrm hG
  have β := l2B_nrm hF
  have α1 := l2B_gr hG1
  have W := l1B_nrm hS2.inH
  have U := l2B_up hS2.inH
  have W1 := l1B_gr hS
  have U1 := l2B_up_gr hS
  exact (((pos2_E2 α1 β W W U U).add (pos2_E2 α β W1 W U1 U)).add (pos2_E2 α β W W1 U U1)).1

/-- A block with the size of the source is bounded by the majorant. -/
lemma le_srcMaj {G F S : Field} {K : ℝ} {x : I3} {B : Blk}
    (hB : ‖B‖ ≤ K * (absk x.1 + absk x.2.1 + absk x.2.2) * (‖S x.2.1‖ * ‖S x.2.2‖) * E2 x) :
    ‖G x.1‖ * ‖B‖ * ‖F (inJ₂ x)‖ ≤ K * srcMaj G F S x := by
  have h1 := norm_nonneg (G x.1)
  have h2 := norm_nonneg (F (inJ₂ x))
  have h3 := mul_le_mul_of_nonneg_left hB (mul_nonneg h1 h2)
  calc _ = ‖G x.1‖ * ‖F (inJ₂ x)‖ * ‖B‖ := by ring
    _ ≤ _ := h3
    _ = _ := by
        simp only [srcMaj, Phi₂, nrm, gr]
        ring

/-- A real slow field is transverse, in the sense of the pairing. -/
lemma inner_leray_right' (k : Mode) (v w : V3) : inner ℂ v (leray k w) = inner ℂ (leray k v) w := by
  rw [← hel_sum k w, ← hel_sum k v, inner_sum, sum_inner]
  exact Finset.sum_congr rfl fun c _ => inner_hel_right _ _ _ _

/-- `leray` of the energy coordinates. -/
lemma leray_zOf {F : Field} (hF : IsSolenoidal F) (hF0 : F 0 = 0) (k : Mode) (s : ℕ) :
    leray k (zOf s F k) = zOf s F k := by
  by_cases hk : k = 0
  · subst hk
    have h0 : leray (0 : Mode) (0 : V3) = 0 := by simpa using leray_smul 0 0 (0 : V3)
    simp [zOf, hF0, h0]
  · simp only [zOf]
    rw [leray_smul, leray_of_perp hk (hF k)]

/-- A source term on transverse vectors. -/
lemma srcT_eq {𝔉 : Fam} {G F : Field} (hG : ∀ k, leray k (G k) = G k)
    (hF : ∀ k, leray k (F k) = F k) (x : I3) (v w : V3) (τ : ℝ) :
    𝔉.srcT x (G x.1) (F (inJ₂ x)) v w τ = inner ℂ (G x.1) (𝔉.Sr x τ v w (F (inJ₂ x))) := by
  simp only [Fam.srcT]
  rw [hF, inner_leray_right', hG]

/-- An edge on the energy coordinates. -/
lemma norm_Lb_apply_le (s : ℕ) (τ : ℝ) {p k j : Mode} (hk : p + j = k) (v : V3) {F : Field}
    (hF0 : F 0 = 0) :
    ‖Lb s τ p k j v (zOf s F j)‖ ≤ 16 * absk k ^ (s + 1) * (‖v‖ * ‖F j‖) := by
  have hK := absk_nonneg k
  have hv := norm_nonneg v
  by_cases hj : j = 0
  · subst hj
    simp only [zOf, hF0, smul_zero, map_zero, norm_zero]
    positivity
  have hJ : 0 < absk j := lt_of_lt_of_le one_pos (one_le_absk hj)
  have hn : ‖zOf s F j‖ = absk j ^ s * ‖F j‖ := by
    simp only [zOf, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hJ.le s)]
  have h1 := (ContinuousLinearMap.le_opNorm (Lb s τ p k j v) (zOf s F j)).trans
    (mul_le_mul_of_nonneg_right (norm_Lb_le s τ hk v) (norm_nonneg _))
  refine h1.trans (le_of_eq ?_)
  rw [hn, wt, div_pow]
  field_simp
  ring

/-- The leaves of an `𝓛` output. -/
lemma Lb_hasSum (s : ℕ) (τ : ℝ) {S F : Field} (hS : MZ 2 S) (hS' : PiS S = S)
    (hF : MZ 2 F) (hF' : PiF F = F) (k : Mode) :
    HasSum (fun b => Lb s τ b k (k - b) (S b) (zOf s F (k - b))) (zOf s (Lop τ S F) k) := by
  have hF0 : F 0 = 0 := hF.mean
  by_cases hk : k 2 = 0
  · have h1 : zOf s (Lop τ S F) k = 0 := by
      simp [zOf, Lop, PiF, hk]
    rw [h1]
    have h2 : (fun b => Lb s τ b k (k - b) (S b) (zOf s F (k - b))) = fun _ => 0 := by
      funext b
      by_cases hb : b 2 = 0
      · have : F (k - b) = 0 := fast_zero hF' (by simp [hk, hb])
        simp [zOf, this]
      · rw [slow_zero hS' hb, Lb_zero_leaf]
        rfl
    rw [h2]
    exact hasSum_zero
  · have hsum : Summable fun b => Lb s τ b k (k - b) (S b) (zOf s F (k - b)) := by
      have hc := ((l1B_nrm hS.inH).conv_l2 (l2B_nrm (z := F)
        (summable_norm_sq_of_inH (hF.inH.mono (by norm_num))))).1 k
      refine Summable.of_norm_bounded (hc.mul_left (16 * absk k ^ (s + 1))) fun b => ?_
      exact norm_Lb_apply_le s τ (by abel) (S b) hF0
    rw [zOf_Lop s τ hF0 hk]
    exact hsum.hasSum

/-! ### The two rootings -/

/-- The first rooting, at one label. -/
def P1 (s : ℕ) (r τ : ℝ) (S z : Field) (x : I3) : ℂ :=
  inner ℂ (z x.1) ((X1b s r τ x.2.1 x.1 (x.1 - x.2.1) (S x.2.1) ∘L
    Lb s τ x.2.2 (x.1 - x.2.1) (x.1 - x.2.1 - x.2.2) (S x.2.2)) (z (inJ₂ x)))

/-- The second rooting, at one label. -/
def P2 (s : ℕ) (r τ : ℝ) (S z : Field) (x : I3) : ℂ :=
  inner ℂ (z x.1) ((Lad s τ x.2.1 x.1 (x.1 - x.2.1) (S x.2.1) ∘L
    X1b s r τ x.2.2 (x.1 - x.2.1) (x.1 - x.2.1 - x.2.2) (S x.2.2)) (z (inJ₂ x)))

/-- A block on the active labels of the source, summed against the majorant. -/
lemma block_le {B : I3 → Blk} {G F S : Field} {K : ℝ} (hK : 0 ≤ K) (hz : PiF F = F)
    (hact : ∀ x, Act x → ‖B x‖ ≤
      K * (absk x.1 + absk x.2.1 + absk x.2.2) * (‖S x.2.1‖ * ‖S x.2.2‖) * E2 x)
    (hzero : ∀ x, inJ₂ x 2 ≠ 0 → ¬Act x → B x = 0) (x : I3) :
    ‖inner ℂ (G x.1) (B x (F (inJ₂ x)))‖ ≤ K * srcMaj G F S x := by
  have hR := mul_nonneg hK (srcMaj_nonneg G F S x)
  by_cases hj : inJ₂ x 2 = 0
  · rw [fast_zero hz hj, map_zero, inner_zero_right, norm_zero]
    exact hR
  by_cases hA : Act x
  · refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
    have h1 := (B x).le_opNorm (F (inJ₂ x))
    refine le_trans ?_ (le_srcMaj (hact x hA))
    calc _ ≤ ‖G x.1‖ * (‖B x‖ * ‖F (inJ₂ x)‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := by ring
  · rw [hzero x hj hA, zero_apply, inner_zero_right, norm_zero]
    exact hR

/-- `M ≤ L + P₁ + P₂`. -/
private lemma M_le (x : I3) : absk (x.1 - x.2.1) ≤ absk x.1 + absk x.2.1 + absk x.2.2 := by
  have h2 := absk_sub_le x.1 x.2.1
  have := absk_nonneg x.2.2
  linarith

/-- The bound of a rooting. -/
private lemma part_bound {T : Blk} {r : ℝ} (hr : r ≠ 0) {x : I3} {v w : V3} (hx : Act x)
    (h : ‖T‖ ≤ 704 / |r| * absk (x.1 - x.2.1) * (‖v‖ * ‖w‖) *
      Br (absSq x.1) (absSq (x.1 - x.2.1)) (absSq (x.1 - x.2.1 - x.2.2))) :
    ‖T‖ ≤ 9856 / |r| * (absk x.1 + absk x.2.1 + absk x.2.2) * (‖v‖ * ‖w‖) * E2 x := by
  obtain ⟨hl0, -, hj0⟩ := fast_labels hx.1 hx.2.1 hx.2.2
  have hB := Br_le_E2 (a := x.2.1) (b := x.2.2) hl0 hj0
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hv := norm_nonneg v
  have hw := norm_nonneg w
  have hE := E2_nonneg x
  have hM0 := absk_nonneg (x.1 - x.2.1)
  have hM := M_le x
  calc _ ≤ 704 / |r| * absk (x.1 - x.2.1) * (‖v‖ * ‖w‖) *
        Br (absSq x.1) (absSq (x.1 - x.2.1)) (absSq (x.1 - x.2.1 - x.2.2)) := h
    _ ≤ 704 / |r| * absk (x.1 - x.2.1) * (‖v‖ * ‖w‖) * (14 * E2 x) := by gcongr
    _ = 9856 / |r| * absk (x.1 - x.2.1) * (‖v‖ * ‖w‖) * E2 x := by ring
    _ ≤ _ := by gcongr

lemma norm_P1_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {S z : Field} (hS' : PiS S = S)
    (hz : PiF z = z) (x : I3) : ‖P1 s r τ S z x‖ ≤ 9856 / |r| * srcMaj z z S x := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  refine block_le (B := fun x => X1b s r τ x.2.1 x.1 (x.1 - x.2.1) (S x.2.1) ∘L
    Lb s τ x.2.2 (x.1 - x.2.1) (x.1 - x.2.1 - x.2.2) (S x.2.2)) (by positivity) hz
    (fun x hx => part_bound hr hx (parts_le hs hr τ hx.1 hx.2.1 hx.2.2 _ _).1)
    (fun x hj hA => ?_) x
  by_cases ha : x.2.1 2 = 0
  · have hb : x.2.2 2 ≠ 0 := fun hb => hA ⟨ha, hb, hj⟩
    simp only [slow_zero hS' hb, Lb_zero_leaf, ContinuousLinearMap.comp_zero]
  · simp only [slow_zero hS' ha, X1b_zero_leaf, ContinuousLinearMap.zero_comp]

lemma norm_P2_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {S z : Field} (hS' : PiS S = S)
    (hz : PiF z = z) (x : I3) : ‖P2 s r τ S z x‖ ≤ 9856 / |r| * srcMaj z z S x := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  refine block_le (B := fun x => Lad s τ x.2.1 x.1 (x.1 - x.2.1) (S x.2.1) ∘L
    X1b s r τ x.2.2 (x.1 - x.2.1) (x.1 - x.2.1 - x.2.2) (S x.2.2)) (by positivity) hz
    (fun x hx => part_bound hr hx (parts_le hs hr τ hx.1 hx.2.1 hx.2.2 _ _).2)
    (fun x hj hA => ?_) x
  by_cases ha : x.2.1 2 = 0
  · have hb : x.2.2 2 ≠ 0 := fun hb => hA ⟨ha, hb, hj⟩
    simp only [slow_zero hS' hb, X1b_zero_leaf, ContinuousLinearMap.comp_zero]
  · simp only [slow_zero hS' ha, Lad_zero_leaf, ContinuousLinearMap.zero_comp]

/-- **The first rooting sums to `⟨z, X₁ w⟩`.** -/
theorem tsum_P1 {S F : Field} (hS2 : MZ 2 S) (hS' : PiS S = S) (hF2 : MZ 2 F) (hF' : PiF F = F)
    (hs1 : Summable (P1 s r τ S (zOf s F))) :
    ∑' x, P1 s r τ S (zOf s F) x = X1Form s r τ S (zOf s F) (zOf s (Lop τ S F)) := by
  set z := zOf s F with hz
  set w := zOf s (Lop τ S F) with hw
  let as : (Mode × Mode) × Mode ≃ I3 := Equiv.prodAssoc Mode Mode Mode
  have h1 : Summable fun y => P1 s r τ S z (as y) := as.summable_iff.2 hs1
  rw [← as.tsum_eq (P1 s r τ S z), h1.tsum_prod]
  unfold X1Form
  refine tsum_congr fun p => ?_
  have hL := Lb_hasSum s τ hS2 hS' hF2 hF' (p.1 - p.2)
  have h2 := (X1b s r τ p.2 p.1 (p.1 - p.2) (S p.2)).hasSum hL
  have h3 := (innerSL ℂ (z p.1)).hasSum h2
  have e : ∀ b, P1 s r τ S z (as (p, b)) = (innerSL ℂ (z p.1))
      (X1b s r τ p.2 p.1 (p.1 - p.2) (S p.2)
        (Lb s τ b (p.1 - p.2) (p.1 - p.2 - b) (S b) (z (p.1 - p.2 - b)))) := fun b => by
    obtain ⟨l, a⟩ := p
    simp only [P1, as, Equiv.prodAssoc_apply, inJ₂, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]
  simp only [e]
  rw [h3.tsum_eq, innerSL_apply_apply]

/-- The relabelling of the second rooting. -/
def rootE : I3 ≃ (Mode × Mode) × Mode where
  toFun x := ((x.1 - x.2.1, x.2.2), -x.2.1)
  invFun y := (y.1.1 - y.2, -y.2, y.1.2)
  left_inv := fun ⟨l, a, b⟩ => Prod.ext (show l - a - -a = l by abel)
    (Prod.ext (neg_neg a) rfl)
  right_inv := fun ⟨⟨m, b⟩, a⟩ => Prod.ext (Prod.ext (show m - a - -a = m by abel) rfl) (neg_neg a)

/-- **The second rooting sums to `⟨w, X₁ z⟩`.** -/
theorem tsum_P2 {S F : Field} (hS2 : MZ 2 S) (hS' : PiS S = S) (hSr : IsReal S) (hF2 : MZ 2 F)
    (hF' : PiF F = F) (hs2 : Summable (P2 s r τ S (zOf s F))) :
    ∑' x, P2 s r τ S (zOf s F) x = X1Form s r τ S (zOf s (Lop τ S F)) (zOf s F) := by
  set z := zOf s F with hz
  set w := zOf s (Lop τ S F) with hw
  have h1 : Summable fun y => P2 s r τ S z (rootE.symm y) := rootE.symm.summable_iff.2 hs2
  rw [← rootE.symm.tsum_eq (P2 s r τ S z), h1.tsum_prod]
  unfold X1Form
  refine tsum_congr fun p => ?_
  have hL := Lb_hasSum s τ hS2 hS' hF2 hF' p.1
  set u := X1b s r τ p.2 p.1 (p.1 - p.2) (S p.2) (z (p.1 - p.2)) with hu
  have h3 := Complex.hasSum_conj'.2 ((innerSL ℂ u).hasSum hL)
  have e : ∀ a, P2 s r τ S z (rootE.symm (p, a)) =
      conj ((innerSL ℂ u) (Lb s τ a p.1 (p.1 - a) (S a) (z (p.1 - a)))) := fun a => by
    obtain ⟨m, b⟩ := p
    have e1 : m - a - -a = m := by abel
    have hc : conjV (S (-a)) = S a := by
      rw [← hSr (-a), neg_neg]
    simp only [P2, rootE, Equiv.coe_fn_symm_mk, inJ₂, e1, neg_neg,
      ContinuousLinearMap.comp_apply, Lad, hc, ContinuousLinearMap.adjoint_inner_right]
    simp only [innerSL_apply_apply, inner_conj_symm]
    rfl
  simp only [e]
  have e2 : conj ((innerSL ℂ u) (w p.1)) = inner ℂ (w p.1) u := by
    simp only [innerSL_apply_apply, inner_conj_symm]
  rw [h3.tsum_eq, e2]

/-- `Lop` is an `H²` field at an `H³` time. -/
lemma mz_Lop (τ : ℝ) {S F : Field} (hS : MZ 3 S) (hF : MZ 3 F) : MZ 2 (Lop τ S F) := by
  refine ⟨((Qm_two_le (phaseM_bdd τ) hS hF).1.PiF).smul 2, ?_⟩
  simp [Lop, PiF]

/-- **The source of `X₂`** is the two insertions of `𝓛` into `X₁`. -/
theorem src_X2_eq (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {S F : Field} (hS : MZ 3 S)
    (hS' : PiS S = S) (hSr : IsReal S) (hF : MZ 3 F) (hF' : PiF F = F) (hFs : IsSolenoidal F) :
    (famX2 s r).src τ S S (zOf s F) (zOf s F) =
      X1Form s r τ S (zOf s F) (zOf s (Lop τ S F)) +
        X1Form s r τ S (zOf s (Lop τ S F)) (zOf s F) := by
  have hsle : s ≤ 2 := by omega
  obtain ⟨z1, -, z3, -⟩ := Fam.z_facts hsle hF
  have hzf : PiF (zOf s F) = zOf s F := Fam.PiF_zOf hF'
  have hm := srcMaj_summable z1 z3 z1 hS
  have s1 : Summable (P1 s r τ S (zOf s F)) :=
    Summable.of_norm_bounded (hm.mul_left _) (norm_P1_le hs hr τ hS' hzf)
  have s2 : Summable (P2 s r τ S (zOf s F)) :=
    Summable.of_norm_bounded (hm.mul_left _) (norm_P2_le hs hr τ hS' hzf)
  have hS2 : MZ 2 S := hS.mono' (by norm_num)
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  have e : ∀ x : I3, (famX2 s r).srcT x (zOf s F x.1) (zOf s F (inJ₂ x)) (S x.2.1) (S x.2.2) τ =
      P1 s r τ S (zOf s F) x + P2 s r τ S (zOf s F) x := fun x => by
    rw [srcT_eq (fun k => leray_zOf hFs hF.mean k s) (fun k => leray_zOf hFs hF.mean k s)]
    simp only [famX2, tR, add_apply, inner_add_right, P1, P2]
  unfold Fam.src
  simp only [e]
  rw [s1.tsum_add s2, tsum_P1 hS2 hS' hF2 hF' s1, tsum_P2 hS2 hS' hSr hF2 hF' s2]

/-- **The source of `X₂`, in the library's terms.** -/
theorem src_X2_re (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {S F : Field} (hS : MZ 3 S)
    (hS' : PiS S = S) (hSr : IsReal S) (hF : MZ 3 F) (hF' : PiF F = F) (hFs : IsSolenoidal F) :
    ((famX2 s r).src τ S S (zOf s F) (zOf s F)).re =
      4 * (pair s F (X1op r τ S (Lop τ S F)) + pair s (Lop τ S F) (X1op r τ S F)) := by
  have hS2 : MZ 2 S := hS.mono' (by norm_num)
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  have hL := mz_Lop τ hS hF
  rw [src_X2_eq hs hr τ hS hS' hSr hF hF' hFs, Complex.add_re, X1Form_re hs r τ hS2 hSr hF2 hL,
    X1Form_re hs r τ hS2 hSr hL hF2]
  ring

/-! ### The merged leaf -/

/-- The leaves of `B(S, S)`. -/
lemma slowV_hasSum {S : Field} (hS : MZ 2 S) (hS' : PiS S = S) (p : Mode) :
    HasSum (fun a => slowV a (p - a) (S a) (S (p - a))) (Bslow S p) := by
  by_cases hp : p 2 = 0
  · have hc := ((l1B_nrm hS.inH).conv_l2 (l2B_nrm (z := S)
      (summable_norm_sq_of_inH (hS.inH.mono (by norm_num))))).1 p
    have hsum : Summable fun a => slowV a (p - a) (S a) (S (p - a)) := by
      refine Summable.of_norm_bounded (hc.mul_left (8 * absk p)) fun a => ?_
      have h1 := norm_slowV_le a (p - a) (S a) (S (p - a))
      rw [show a + (p - a) = p by abel] at h1
      refine h1.trans (le_of_eq ?_)
      simp only [nrm]
      ring
    rw [Bslow_eq_tsum S hp]
    exact hsum.hasSum
  · have h1 : Bslow S p = 0 := by simp [Bslow, PiS, hp]
    rw [h1]
    have h2 : (fun a => slowV a (p - a) (S a) (S (p - a))) = fun _ => 0 := by
      funext a
      by_cases ha : a 2 = 0
      · have : (p - a) 2 ≠ 0 := by simpa [ha] using hp
        rw [slow_zero hS' this]
        exact slowV_eq_zero (Or.inr rfl)
      · rw [slow_zero hS' ha]
        exact slowV_eq_zero (Or.inl rfl)
    rw [h2]
    exact hasSum_zero

/-- `X₁` as a continuous linear map of its leaf. -/
def X1CL (s : ℕ) (r τ : ℝ) (p k j : Mode) : V3 →L[ℂ] Blk :=
  LinearMap.toContinuousLinearMap
    { toFun := X1b s r τ p k j
      map_add' := X1b_add_leaf s r τ p k j
      map_smul' := fun c v => X1b_smul_leaf s r τ p k j c v }

@[simp] lemma X1CL_apply (s : ℕ) (r τ : ℝ) (p k j : Mode) (v : V3) :
    X1CL s r τ p k j v = X1b s r τ p k j v := rfl

/-- The merged term at one label. -/
def P3 (s : ℕ) (r τ : ℝ) (S G F : Field) (x : I3) : ℂ :=
  inner ℂ (G x.1) (zR s r τ x.1 x.2.1 x.2.2 (S x.2.1) (S x.2.2) (F (inJ₂ x)))

lemma norm_P3_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {S G F : Field} (hS' : PiS S = S)
    (hz : PiF F = F) (x : I3) : ‖P3 s r τ S G F x‖ ≤ 4928 / |r| * srcMaj G F S x := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  refine block_le (B := fun x => zR s r τ x.1 x.2.1 x.2.2 (S x.2.1) (S x.2.2)) (by positivity) hz
    (fun x hx => (famZ_bd hs hr).source x hx τ _ _) (fun x hj hA => ?_) x
  by_cases ha : x.2.1 2 = 0
  · have hb : x.2.2 2 ≠ 0 := fun hb => hA ⟨ha, hb, hj⟩
    simp only [slow_zero hS' hb]
    exact (famZ s r).zero_r x τ _
  · simp only [slow_zero hS' ha]
    exact (famZ s r).zero_l x τ _

/-- The relabelling of the merged term. -/
def mergeE : (Mode × Mode) × Mode ≃ I3 where
  toFun y := (y.1.1, y.2, y.1.2 - y.2)
  invFun x := ((x.1, x.2.1 + x.2.2), x.2.1)
  left_inv := fun ⟨⟨l, p⟩, a⟩ => Prod.ext (Prod.ext rfl (show a + (p - a) = p by abel)) rfl
  right_inv := fun ⟨l, a, b⟩ => Prod.ext rfl (Prod.ext rfl (show a + b - a = b by abel))

/-- **The merged term sums to `⟨G, X₁(B) F⟩`.** -/
theorem tsum_P3 {S G F : Field} (hS2 : MZ 2 S) (hS' : PiS S = S)
    (hs3 : Summable (P3 s r τ S G F)) :
    ∑' x, P3 s r τ S G F x = X1Form s r τ (Bslow S) G F := by
  have h1 : Summable fun y => P3 s r τ S G F (mergeE y) := mergeE.summable_iff.2 hs3
  rw [← mergeE.tsum_eq (P3 s r τ S G F), h1.tsum_prod]
  unfold X1Form
  refine tsum_congr fun p => ?_
  have hL := slowV_hasSum hS2 hS' p.2
  have h2 := (X1CL s r τ p.2 p.1 (p.1 - p.2)).hasSum hL
  have h3 := (ContinuousLinearMap.apply ℂ V3 (F (p.1 - p.2))).hasSum h2
  have h4 := (innerSL ℂ (G p.1)).hasSum h3
  have e : ∀ a, P3 s r τ S G F (mergeE (p, a)) = (innerSL ℂ (G p.1))
      ((ContinuousLinearMap.apply ℂ V3 (F (p.1 - p.2)))
        (X1CL s r τ p.2 p.1 (p.1 - p.2) (slowV a (p.2 - a) (S a) (S (p.2 - a))))) := fun a => by
    obtain ⟨l, q⟩ := p
    have e1 : a + (q - a) = q := by abel
    have e2 : l - a - (q - a) = l - q := by abel
    simp only [P3, mergeE, Equiv.coe_fn_mk, zR, inJ₂, e1, e2, innerSL_apply_apply,
      ContinuousLinearMap.apply_apply, X1CL_apply]
  simp only [e]
  rw [h4.tsum_eq]
  simp only [innerSL_apply_apply, ContinuousLinearMap.apply_apply, X1CL_apply]

/-- The source of `Z` is `X₁(B)`, on two transverse fields. -/
theorem src_Z_eq₂ (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {S G F : Field} (hS : MZ 3 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : InH 1 G)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) (hGl : ∀ k, leray k (G k) = G k)
    (hFl : ∀ k, leray k (F k) = F k) :
    (famZ s r).src τ S S G F = X1Form s r τ (Bslow S) G F := by
  have hm := srcMaj_summable hG hG1 hF hS
  have s3 : Summable (P3 s r τ S G F) :=
    Summable.of_norm_bounded (hm.mul_left _) (norm_P3_le hs hr τ hS' hF')
  have hS2 : MZ 2 S := hS.mono' (by norm_num)
  have e : ∀ x : I3, (famZ s r).srcT x (G x.1) (F (inJ₂ x)) (S x.2.1) (S x.2.2) τ =
      P3 s r τ S G F x := fun x => by
    rw [srcT_eq hGl hFl]
    rfl
  unfold Fam.src
  simp only [e]
  exact tsum_P3 hS2 hS' s3

/-- **The source of `Z`** is `X₁(B)`. -/
theorem src_Z_eq (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {S F : Field} (hS : MZ 3 S)
    (hS' : PiS S = S) (hF : MZ 3 F) (hF' : PiF F = F) (hFs : IsSolenoidal F) :
    (famZ s r).src τ S S (zOf s F) (zOf s F) = X1Form s r τ (Bslow S) (zOf s F) (zOf s F) := by
  have hsle : s ≤ 2 := by omega
  obtain ⟨z1, -, z3, -⟩ := Fam.z_facts hsle hF
  have hzf : PiF (zOf s F) = zOf s F := Fam.PiF_zOf hF'
  have hl := fun k => leray_zOf hFs hF.mean k s
  exact src_Z_eq₂ hs hr τ hS hS' z1 z3 z1 hzf hl hl

/-- `B(S, S)` at an `H³` time. -/
lemma mz_Bslow {S : Field} (hS : MZ 3 S) : MZ 2 (Bslow S) := by
  refine ⟨(Qm_two_le resM_bdd hS hS).1.PiS, ?_⟩
  simp [Bslow, PiS, Qres, Qm, hel_zero_mode]

/-- **The source of `Z`, in the library's terms.** -/
theorem src_Z_re (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {S F : Field} (hS : MZ 3 S)
    (hS' : PiS S = S) (hSa : Adm 2 S) (hF : MZ 3 F) (hF' : PiF F = F) (hFs : IsSolenoidal F) :
    ((famZ s r).src τ S S (zOf s F) (zOf s F)).re = 4 * pair s F (X1op r τ (Bslow S) F) := by
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  have hr' : IsReal (Bslow S) := (majorized_res.real 0 S S hSa hSa).PiS'
  rw [src_Z_eq hs hr τ hS hS' hF hF' hFs, X1Form_re hs r τ (mz_Bslow hS) hr' hF2 hF2]
  ring

end OVNS.Quant.Metric

end
