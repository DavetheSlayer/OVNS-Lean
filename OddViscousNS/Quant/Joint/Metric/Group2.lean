import OddViscousNS.Quant.Joint.Metric.DiffZ
import OddViscousNS.Quant.Joint.Force.Pairs

/-!
# The cubic group at the last edge: the split (step J5, nodes N7, N8, N9)

Unit: `TIMED_METRIC_PROOF_V2.md` §7, §9.  On the energy coordinates, with `Y = X₂ + Z`,
`⟨G, Y A^{s/2} 𝓛 F⟩ = ⟨G, Y A^{s/2} QLF⟩ + YLForm (1 − lowM)`, and the high complement is the
sum of the three masks `muH` (a high ancestor), `muQ` (comparable), `muS` (separated).
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {s : ℕ} {r τ : ℝ} {S F G : Field}

/-! ### Summability of the forms -/

lemma Fam.T_summable {𝔉 : Fam} {ρ : I3 → ℝ} {K₁ K₂ : ℝ} (hB : 𝔉.Bd r ρ K₁ K₂) (τ : ℝ)
    {f g G F : Field} (hf : MZ 2 f) (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g)
    (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) :
    Summable fun x : I3 => 𝔉.T r x (G x.1) (F (inJ₂ x)) (f x.2.1) (g x.2.2) τ :=
  Summable.of_norm_bounded (Fam.sb_maj₀ hB.K₁0 (l2B_nrm hG) (l2B_nrm hF) (l1B_nrm hf.inH)
    (l1B_nrm hg.inH) (l2B_up hf.inH) (l2B_up hg.inH)).1 fun x => Fam.T_le_maj₀ hB hf' hg' hF' x

/-- The terms of `X₂`. -/
lemma X2_summable (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {f g G F : Field} (hf : MZ 2 f)
    (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) :
    Summable fun x : I3 => inner ℂ (G x.1)
      (X2b s r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2))) := by
  have h := Fam.T_summable (famX2_bd hs hr) τ hf hf' hg hg' hG hF hF'
  refine h.congr fun x => ?_
  dsimp only [Fam.T, oTerm, X2b, Hx, inJ₂, famX2, twoRoot, tR]

/-- The terms of `Z`. -/
lemma Z_summable (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {f g G F : Field} (hf : MZ 2 f)
    (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) :
    Summable fun x : I3 => inner ℂ (G x.1)
      (Zb s r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2))) := by
  have h := Fam.T_summable (famZ_bd hs hr) τ hf hf' hg hg' hG hF hF'
  refine h.congr fun x => ?_
  dsimp only [Fam.T, oTerm, Zb, Hx, inJ₂, famZ, zR]

lemma X2Form_one (s : ℕ) (r τ : ℝ) (f g G F : Field) :
    X2Form 1 s r τ f g G F = ∑' x : I3, inner ℂ (G x.1)
      (X2b s r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2))) := by
  simp only [X2Form, Pi.one_apply, one_mul]

lemma ZForm_one (s : ℕ) (r τ : ℝ) (f g G F : Field) :
    ZForm 1 s r τ f g G F = ∑' x : I3, inner ℂ (G x.1)
      (Zb s r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2))) := by
  simp only [ZForm, Pi.one_apply, one_mul]

/-- `X₂` is additive on the input. -/
lemma X2Form_add (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {f g G F₁ F₂ : Field} (hf : MZ 2 f)
    (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF₁ : Summable fun k => ‖F₁ k‖ ^ 2) (hF₁' : PiF F₁ = F₁)
    (hF₂ : Summable fun k => ‖F₂ k‖ ^ 2) (hF₂' : PiF F₂ = F₂) :
    X2Form 1 s r τ f g G (F₁ + F₂) = X2Form 1 s r τ f g G F₁ + X2Form 1 s r τ f g G F₂ := by
  simp only [X2Form_one, Pi.add_apply, map_add, inner_add_right]
  exact (X2_summable hs hr τ hf hf' hg hg' hG hF₁ hF₁').tsum_add
    (X2_summable hs hr τ hf hf' hg hg' hG hF₂ hF₂')

/-- `Z` is additive on the input. -/
lemma ZForm_add (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {f g G F₁ F₂ : Field} (hf : MZ 2 f)
    (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hF₁ : Summable fun k => ‖F₁ k‖ ^ 2) (hF₁' : PiF F₁ = F₁)
    (hF₂ : Summable fun k => ‖F₂ k‖ ^ 2) (hF₂' : PiF F₂ = F₂) :
    ZForm 1 s r τ f g G (F₁ + F₂) = ZForm 1 s r τ f g G F₁ + ZForm 1 s r τ f g G F₂ := by
  simp only [ZForm_one, Pi.add_apply, map_add, inner_add_right]
  exact (Z_summable hs hr τ hf hf' hg hg' hG hF₁ hF₁').tsum_add
    (Z_summable hs hr τ hf hf' hg hg' hG hF₂ hF₂')

lemma mz_l2 {t : ℝ} (ht : 0 ≤ t) {u : Field} (hu : MZ t u) : Summable fun k => ‖u k‖ ^ 2 := by
  refine (hu.inH.mono ht).congr fun k => ?_
  by_cases hk : k = 0
  · simp [hk, hu.mean]
  · simp [sobWeight, hk]

/-! ### The high last edge is the four-label form -/

/-- The block of the four-label form. -/
lemma YLb_apply (s : ℕ) (r τ : ℝ) (f g h : Field) (x : I4) (v : V3) :
    YLb s r τ f g h x v = (X2b s r τ f g x.1 x.2.1 x.2.2.1 + Zb s r τ f g x.1 x.2.1 x.2.2.1)
      (Lb s τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x) (h x.2.2.2) v) := by
  simp only [YLb, inJ, ContinuousLinearMap.comp_apply]

/-- The abstract Fubini step: `Y`, with a multiplier on the edge. -/
lemma Y_fubini_abs {Y : I3 → Blk} {G w : Field} {μ : I4 → ℂ} {Eg : I4 → V3}
    (hE : ∀ y : I3, y.2.1 2 = 0 → y.2.2 2 = 0 → (y.1 - y.2.1 - y.2.2) 2 ≠ 0 →
      HasSum (fun c => μ (y.1, y.2.1, y.2.2, c) • Eg (y.1, y.2.1, y.2.2, c))
        (w (y.1 - y.2.1 - y.2.2)))
    (hzero : ∀ y : I3, ¬ (y.2.1 2 = 0 ∧ y.2.2 2 = 0 ∧ (y.1 - y.2.1 - y.2.2) 2 ≠ 0) →
      Y y = 0 ∨ G y.1 = 0)
    (hT : Summable fun x : I4 => μ x * inner ℂ (G x.1) (Y (x.1, x.2.1, x.2.2.1) (Eg x))) :
    ∑' y : I3, inner ℂ (G y.1) (Y y (w (y.1 - y.2.1 - y.2.2))) =
      ∑' x : I4, μ x * inner ℂ (G x.1) (Y (x.1, x.2.1, x.2.2.1) (Eg x)) := by
  have hf := form_fubini (Y := Y) (G := G) (w := w) (E := fun x => μ x • Eg x) hE
    (fun y hy => by
      rcases hzero y hy with h0 | h0
      · refine ⟨?_, fun c => ?_⟩
        · rw [h0]
          simp
        · rw [h0]
          simp
      · refine ⟨?_, fun c => ?_⟩
        · rw [h0, inner_zero_left]
        · rw [h0, inner_zero_left])
    (by
      refine hT.congr fun x => ?_
      rw [map_smul, inner_smul_right])
  rw [hf]
  refine tsum_congr fun x => ?_
  rw [map_smul, inner_smul_right]

lemma zOf_QHF' (s : ℕ) (τ : ℝ) {S F : Field} (hF0 : F 0 = 0) (hS2 : Summable fun k => ‖S k‖ ^ 2)
    (hF2 : Summable fun k => ‖F k‖ ^ 2) (y : I3) (hk : (y.1 - y.2.1 - y.2.2) 2 ≠ 0) :
    HasSum (fun c => ((1 - lowM c (inJ (y.1, y.2.1, y.2.2, c)) : ℝ) : ℂ) •
      Lb s τ c (y.1 - y.2.1 - y.2.2) (inJ (y.1, y.2.1, y.2.2, c)) (S c)
        (zOf s F (inJ (y.1, y.2.1, y.2.2, c)))) (zOf s (QHF τ S F) (y.1 - y.2.1 - y.2.2)) := by
  have e : ∀ c, inJ (y.1, y.2.1, y.2.2, c) = y.1 - y.2.1 - y.2.2 - c := fun c => rfl
  simp only [e]
  exact zOf_QHF s τ hF0 hS2 hF2 hk

/-- **The high last edge.** -/
theorem Y_high_eq (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {S F G : Field} (hS : MZ 2 S)
    (hS' : PiS S = S) (hF0 : F 0 = 0) (hF2 : Summable fun k => ‖F k‖ ^ 2)
    (hG : Summable fun k => ‖G k‖ ^ 2) (hG' : PiF G = G)
    (hw : Summable fun k => ‖zOf s (QHF τ S F) k‖ ^ 2) (hw' : PiF (zOf s (QHF τ S F)) =
      zOf s (QHF τ S F))
    (hT : Summable fun x : I4 => ((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ) * inner ℂ (G x.1)
      (YLb s r τ S S S x (zOf s F (inJ x)))) :
    X2Form 1 s r τ S S G (zOf s (QHF τ S F)) + ZForm 1 s r τ S S G (zOf s (QHF τ S F)) =
      YLForm (fun x => ((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ)) s r τ S S S G (zOf s F) := by
  have hS2 := mz_l2 (by norm_num) hS
  have hsumX := X2_summable hs hr τ hS hS' hS hS' hG hw hw'
  have hsumZ := Z_summable hs hr τ hS hS' hS hS' hG hw hw'
  rw [X2Form_one, ZForm_one, ← hsumX.tsum_add hsumZ]
  have hzero : ∀ y : I3, ¬ (y.2.1 2 = 0 ∧ y.2.2 2 = 0 ∧ (y.1 - y.2.1 - y.2.2) 2 ≠ 0) →
      (X2b s r τ S S y.1 y.2.1 y.2.2 + Zb s r τ S S y.1 y.2.1 y.2.2 = 0) ∨ G y.1 = 0 := by
    intro y hy
    by_cases ha : y.2.1 2 = 0
    · by_cases hb : y.2.2 2 = 0
      · have hk : (y.1 - y.2.1 - y.2.2) 2 = 0 := by
          by_contra hc
          exact hy ⟨ha, hb, hc⟩
        have hl : y.1 2 = 0 := by
          simpa [ha, hb] using hk
        exact Or.inr (fast_zero hG' hl)
      · left
        rw [X2b_eq_zero (Or.inr (slow_zero hS' hb)), Zb_eq_zero (Or.inr (slow_zero hS' hb)),
          add_zero]
    · left
      rw [X2b_eq_zero (Or.inl (slow_zero hS' ha)), Zb_eq_zero (Or.inl (slow_zero hS' ha)),
        add_zero]
  have e1 : (fun x : I3 => inner ℂ (G x.1) (X2b s r τ S S x.1 x.2.1 x.2.2
      (zOf s (QHF τ S F) (x.1 - x.2.1 - x.2.2))) + inner ℂ (G x.1) (Zb s r τ S S x.1 x.2.1 x.2.2
      (zOf s (QHF τ S F) (x.1 - x.2.1 - x.2.2)))) = fun y : I3 => inner ℂ (G y.1)
        ((X2b s r τ S S y.1 y.2.1 y.2.2 + Zb s r τ S S y.1 y.2.1 y.2.2)
          (zOf s (QHF τ S F) (y.1 - y.2.1 - y.2.2))) := by
    funext y
    rw [add_apply, inner_add_right]
  rw [e1]
  have hT' : Summable fun x : I4 => ((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ) * inner ℂ (G x.1)
      ((X2b s r τ S S x.1 x.2.1 x.2.2.1 + Zb s r τ S S x.1 x.2.1 x.2.2.1)
        (Lb s τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x) (S x.2.2.2) (zOf s F (inJ x)))) :=
    hT.congr fun x => by rw [YLb_apply]
  have h := Y_fubini_abs
    (Y := fun y : I3 => X2b s r τ S S y.1 y.2.1 y.2.2 + Zb s r τ S S y.1 y.2.1 y.2.2) (G := G)
    (w := zOf s (QHF τ S F)) (μ := fun x => ((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ))
    (Eg := fun x => Lb s τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (inJ x) (S x.2.2.2) (zOf s F (inJ x)))
    (fun y _ _ hk => zOf_QHF' s τ hF0 hS2 hF2 y hk) hzero (by simpa only using hT')
  simp only at h
  rw [h]
  simp only [YLForm, YLb_apply]

/-! ### The low edge as a field -/

lemma leray_hel' (c : Sgn) (k : Mode) (y : V3) : leray k (hel c k y) = hel c k y := by
  rw [← hel_sum, Fintype.sum_eq_single c fun c' hc' => hel_orth hc' k y, hel_idem]

lemma leray_blk (m : Mult) (p k j : Mode) (v w : V3) :
    leray k (blk m p k j v w) = blk m p k j v w := by
  rw [← hel_sum, blk_apply]
  have e : ∀ e : Sgn, hel e k (∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      m a b c p j • hel c k (vert p j (hel a p v) (hel b j w))) =
      ∑ a : Sgn, ∑ b : Sgn, m a b e p j • hel e k (vert p j (hel a p v) (hel b j w)) := fun e => by
    simp only [hel_sum_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Fintype.sum_eq_single e fun c hc => ?_]
    · rw [hel_smul, hel_idem]
    · rw [hel_smul, hel_orth (Ne.symm hc), smul_zero]
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma Qlo_summable (τ : ℝ) {S F : Field} (hS2 : Summable fun k => ‖S k‖ ^ 2)
    (hF2 : Summable fun k => ‖F k‖ ^ 2) (k : Mode) :
    Summable fun p => ((lowM p (k - p) : ℝ) : ℂ) • blk (phaseM τ) p k (k - p) (S p) (F (k - p)) := by
  refine Summable.of_norm_bounded (blk_norm_summable (phaseM_bdd τ) hS2 hF2 k) fun p => ?_
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (lowM_nonneg _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (lowM_le_one _ _)

lemma leray_Qlo (τ : ℝ) {S F : Field} (hS2 : Summable fun k => ‖S k‖ ^ 2)
    (hF2 : Summable fun k => ‖F k‖ ^ 2) (k : Mode) :
    leray k (Qlo τ S F k) = Qlo τ S F k := by
  have hs := (Qlo_summable τ hS2 hF2 k).hasSum
  have e : ∀ v : V3, (∑ c : Sgn, helL c k) v = leray k v := fun v => by
    rw [← hel_sum, sum_apply]
    rfl
  have h1 := (∑ c : Sgn, helL c k).hasSum hs
  have h2 : (fun p => (∑ c : Sgn, helL c k) (((lowM p (k - p) : ℝ) : ℂ) •
      blk (phaseM τ) p k (k - p) (S p) (F (k - p)))) = fun p => ((lowM p (k - p) : ℝ) : ℂ) •
      blk (phaseM τ) p k (k - p) (S p) (F (k - p)) := by
    funext p
    rw [e, leray_smul, leray_blk]
  rw [h2] at h1
  rw [← e]
  exact h1.unique hs

lemma QLF_sol (τ : ℝ) {S F : Field} (hS2 : Summable fun k => ‖S k‖ ^ 2)
    (hF2 : Summable fun k => ‖F k‖ ^ 2) : IsSolenoidal (QLF τ S F) := fun k => by
  by_cases hk : k 2 = 0
  · simp [QLF, PiF, hk, dotM]
  · have e : QLF τ S F k = (2 : ℂ) • Qlo τ S F k := by simp [QLF, PiF, hk]
    rw [e, dotM_smul, ← leray_Qlo τ hS2 hF2 k, dotM_leray, mul_zero]

lemma PiF_QLF (τ : ℝ) (S F : Field) : PiF (QLF τ S F) = QLF τ S F := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [QLF, PiF, hk]

lemma PiF_Lop (τ : ℝ) (S F : Field) : PiF (Lop τ S F) = Lop τ S F := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [Lop, PiF, hk]

lemma PiF_QHF (τ : ℝ) (S F : Field) : PiF (QHF τ S F) = QHF τ S F := by
  funext k
  by_cases hk : k 2 = 0
  · simp only [PiF, hk, ite_true]
    have h1 := congrFun (PiF_QLF τ S F) k
    have h2 := congrFun (PiF_Lop τ S F) k
    simp only [PiF, hk, ite_true] at h1 h2
    simp [QHF, ← h1, ← h2]
  · simp [PiF, hk]

lemma zOf_add' (s : ℕ) (u v : Field) : zOf s (u + v) = zOf s u + zOf s v := by
  funext k
  simp only [zOf, Pi.add_apply, smul_add]

lemma zOf_Lop_split (s : ℕ) (τ : ℝ) (S F : Field) :
    zOf s (Lop τ S F) = zOf s (QLF τ S F) + zOf s (QHF τ S F) := by
  rw [← zOf_add']
  congr 1
  simp [QHF]

/-! ### The three masks of the high last edge -/

/-- The mask of a high ancestor, on the high last edge. -/
def muH (D : ℝ) (x : I4) : ℂ := ((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ) * hiMask₃ D x

lemma norm_muH_le (D : ℝ) (x : I4) : ‖muH D x‖ ≤ ‖hiMask₃ D x‖ := by
  rw [muH, norm_mul, Complex.norm_real]
  have h1 := lowM_nonneg x.2.2.2 (inJ x)
  have h2 := lowM_le_one x.2.2.2 (inJ x)
  rw [Real.norm_of_nonneg (by linarith)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- **The partition of the high last edge.** -/
lemma mu_split (D : ℝ) (x : I4) :
    ((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ) = muH D x + ((muQ D x : ℝ) : ℂ) + ((muS D x : ℝ) : ℂ) := by
  by_cases h1 : absk x.2.1 ≤ D
  · by_cases h2 : absk x.2.2.1 ≤ D
    · by_cases h3 : absk x.2.2.2 ≤ D
      · have e : hiMask₃ D x = 0 := by
          simp [hiMask₃, not_lt.2 h1, not_lt.2 h2, not_lt.2 h3]
        by_cases h4 : absk x.1 ≤ 2 * absk (x.1 - x.2.1 - x.2.2.1) ∧
            absk (x.1 - x.2.1 - x.2.2.1) ≤ 2 * absk x.1
        · simp [muH, muQ, muS, e, h1, h2, h3, h4]
        · simp [muH, muQ, muS, e, h1, h2, h3, h4]
      · have e : hiMask₃ D x = 1 := by
          simp [hiMask₃, not_le.1 h3]
        simp [muH, muQ, muS, e, h3]
    · have e : hiMask₃ D x = 1 := by
        simp [hiMask₃, not_le.1 h2]
      simp [muH, muQ, muS, e, h2]
  · have e : hiMask₃ D x = 1 := by
      simp [hiMask₃, not_le.1 h1]
    simp [muH, muQ, muS, e, h1]

/-! ### The split -/

/-- **The cubic group at the last edge, split**, at weight two. -/
theorem Y_split₂ {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 1 ≤ D) {S F : Field} (hS : MZ 2 S)
    (hS' : PiS S = S) (hF : MZ 2 F) (hF' : PiF F = F) (hFs : IsSolenoidal F)
    (hw : Summable fun k => ‖zOf 2 (Lop τ S F) k‖ ^ 2)
    (hwl : Summable fun k => ‖zOf 2 (QLF τ S F) k‖ ^ 2) :
    X2Form 1 2 r τ S S (zOf 2 F) (zOf 2 (Lop τ S F)) +
        ZForm 1 2 r τ S S (zOf 2 F) (zOf 2 (Lop τ S F)) =
      (X2Form 1 2 r τ S S (zOf 2 F) (zOf 2 (QLF τ S F)) +
        ZForm 1 2 r τ S S (zOf 2 F) (zOf 2 (QLF τ S F))) +
      YLForm (muH D) 2 r τ S S S (zOf 2 F) (zOf 2 F) +
      YLForm (fun x => ((muS D x : ℝ) : ℂ)) 2 r τ S S S (zOf 2 F) (zOf 2 F) +
      ((famQ 2 r D).src τ S S S (zOf 2 F) (zOf 2 F) + HtQ D 2 r τ S S S (zOf 2 F) (zOf 2 F)) := by
  have hF2 : InH ((2 : ℕ) : ℝ) F := by simpa using hF.inH
  obtain ⟨hz, -⟩ := l2_zOf hF2 hF.mean
  have hz' : PiF (zOf 2 F) = zOf 2 F := Fam.PiF_zOf hF'
  have hzl : ∀ k, leray k (zOf 2 F k) = zOf 2 F k := fun k => leray_zOf hFs hF.mean k 2
  have hL' : PiF (zOf 2 (QLF τ S F)) = zOf 2 (QLF τ S F) := Fam.PiF_zOf (PiF_QLF τ S F)
  have hH' : PiF (zOf 2 (QHF τ S F)) = zOf 2 (QHF τ S F) := Fam.PiF_zOf (PiF_QHF τ S F)
  have hwh : Summable fun k => ‖zOf 2 (QHF τ S F) k‖ ^ 2 := by
    have e : ∀ k, zOf 2 (QHF τ S F) k = zOf 2 (Lop τ S F) k - zOf 2 (QLF τ S F) k := fun k => by
      simp only [zOf, QHF, Pi.sub_apply, smul_sub]
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((hw.mul_left 2).add (hwl.mul_left 2))
    rw [e]
    have h1 := norm_sub_le (zOf 2 (Lop τ S F) k) (zOf 2 (QLF τ S F) k)
    have h2 := norm_nonneg (zOf 2 (Lop τ S F) k - zOf 2 (QLF τ S F) k)
    nlinarith only [h1, h2, sq_nonneg (‖zOf 2 (Lop τ S F) k‖ - ‖zOf 2 (QLF τ S F) k‖)]
  have hsum : ∀ {μ : I4 → ℂ}, (∀ x, ‖μ x‖ ≤ 1) → Summable fun x : I4 => μ x * inner ℂ (zOf 2 F x.1)
      (YLb 2 r τ S S S x (zOf 2 F (inJ x))) := fun hμ => (YL_bound hr τ hS hS' hz hz hz' hμ).1
  have n1 : ∀ x : I4, ‖((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ)‖ ≤ 1 := fun x => by
    have h1 := lowM_nonneg x.2.2.2 (inJ x)
    have h2 := lowM_le_one x.2.2.2 (inJ x)
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  have n2 : ∀ x : I4, ‖muH D x‖ ≤ 1 := fun x => (norm_muH_le D x).trans (by
    unfold hiMask₃
    split_ifs <;> simp)
  have n3 : ∀ x : I4, ‖((muQ D x : ℝ) : ℂ)‖ ≤ 1 := fun x => by
    rw [Complex.norm_real, Real.norm_of_nonneg (muQ_nonneg D x)]
    exact muQ_le_one D x
  have n4 : ∀ x : I4, ‖((muS D x : ℝ) : ℂ)‖ ≤ 1 := fun x => by
    rw [Complex.norm_real, Real.norm_of_nonneg (muS_nonneg D x)]
    exact muS_le_one D x
  have hHigh := Y_high_eq (s := 2) (Or.inr rfl) hr τ hS hS' hF.mean (mz_l2 (by norm_num) hF) hz hz'
    hwh hH' (hsum n1)
  have hSplit : YLForm (fun x => ((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ)) 2 r τ S S S (zOf 2 F)
      (zOf 2 F) = YLForm (muH D) 2 r τ S S S (zOf 2 F) (zOf 2 F) +
        YLForm (fun x => ((muQ D x : ℝ) : ℂ)) 2 r τ S S S (zOf 2 F) (zOf 2 F) +
        YLForm (fun x => ((muS D x : ℝ) : ℂ)) 2 r τ S S S (zOf 2 F) (zOf 2 F) := by
    simp only [YLForm]
    rw [← (hsum n2).tsum_add (hsum n3), ← ((hsum n2).add (hsum n3)).tsum_add (hsum n4)]
    refine tsum_congr fun x => ?_
    rw [mu_split D x]
    ring
  have hQ := YL_eq_src_add (s := 2) (Or.inr rfl) hr τ hD hS hS' hS hS' hS hS' hz hz hz' hzl hzl
  have hX := X2Form_add (s := 2) (Or.inr rfl) hr τ hS hS' hS hS' hz hwl hL' hwh hH'
  have hZ := ZForm_add (s := 2) (Or.inr rfl) hr τ hS hS' hS hS' hz hwl hL' hwh hH'
  rw [zOf_Lop_split, hX, hZ]
  rw [hSplit, hQ] at hHigh
  calc _ = (X2Form 1 2 r τ S S (zOf 2 F) (zOf 2 (QLF τ S F)) +
        ZForm 1 2 r τ S S (zOf 2 F) (zOf 2 (QLF τ S F))) +
        (X2Form 1 2 r τ S S (zOf 2 F) (zOf 2 (QHF τ S F)) +
          ZForm 1 2 r τ S S (zOf 2 F) (zOf 2 (QHF τ S F))) := by ring
    _ = _ := by
        rw [hHigh]
        ring

/-! ### The bound of the group -/

/-- The low edge in the Sobolev norms. -/
lemma QLF_bound (τ : ℝ) {S F : Field} {M : ℝ} (hS : Adm 2 S) (hS' : PiS S = S) (hM : GN.SupBd S M)
    (hF : Adm 2 F) (σ : ℕ) (hFs : InH ((σ + 1 : ℕ) : ℝ) F) :
    InH σ (QLF τ S F) ∧ hnorm σ (QLF τ S F) ≤ 2 * CLow σ * M * hnorm ((σ + 1 : ℕ) : ℝ) F := by
  obtain ⟨h1, h2⟩ := hnorm_Qlo_le τ hS hS' hM hF σ hFs
  have h3 : InH σ (QLF τ S F) := h1.PiF.smul 2
  refine ⟨h3, ?_⟩
  simp only [QLF]
  rw [hnorm_smul]
  have h4 := hnorm_PiF_le h1
  have e : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e]
  calc 2 * hnorm σ (PiF (Qlo τ S F)) ≤ 2 * (CLow σ * M * hnorm ((σ + 1 : ℕ) : ℝ) F) := by
        gcongr
        exact h4.trans h2
    _ = _ := by ring

/-- `Lop` is in `H²` at an `H³` time. -/
lemma Lop_two {τ : ℝ} {S F : Field} (hS : MZ 3 S) (hF : MZ 3 F) : MZ 2 (Lop τ S F) := by
  have h1 := (OVNS.Quant.H2.Qm_two_le (phaseM_bdd τ) hS hF).1
  refine ⟨?_, ?_⟩
  · have h2 : InH 2 (PiF (Qphase τ S F)) := InH.PiF h1
    exact h2.smul 2
  · simp [Lop, PiF]

lemma X2Cf_nn (r : ℝ) {D : ℝ} (hD : 1 ≤ D) (S : Field) : 0 ≤ X2Cf r D S := by
  have h2 := hnorm_nonneg 1 S
  have h3 := hnorm_nonneg 2 S
  have h4 := tailB_nonneg D S
  have h5 := Cm2_pos
  have h6 := Real.log_nonneg hD
  have h7 := c4_pos
  have h8 := abs_nonneg r
  have hW := wiener_nonneg S
  have hD0 : 0 ≤ D := by linarith
  simp only [X2Cf, X2Lo, cls2]
  positivity

lemma ZCf_nn {r M : ℝ} (hr : 1 ≤ |r|) (hM : 0 ≤ M) (S : Field) : 0 ≤ ZCf r M S := by
  have h1 := CZh_pos
  have h2 := Real.log_nonneg hr
  have h3 := hnorm_nonneg 2 S
  have h4 := abs_nonneg r
  unfold ZCf
  positivity

/-- The multiplier of the cubic group at weight two. -/
def G₂ (r D M : ℝ) (S : Field) : ℝ :=
  (X2Cf r D S + ZCf r M S) * (2 * CLow 1 * M) +
  Cm3 / |r| * (tailW D S * hnorm 2 S ^ 2 + wiener S * hnorm 2 S * tailB D S) +
  sepB D |r| S S S +
  2 ^ 22 * D / |r| ^ 2 * (hnorm 2 S * Real.sqrt 17 *
    (hnorm 1 S * Real.sqrt (9 + 8 * Real.log (4 * D))) * wiener S)

/-- **The cubic group at weight two, off the source of `O`**: all of rows 1–3, the heat of row 4,
and rows 7–10. -/
theorem group₂_le (hr1 : 1 ≤ |r|) (τ : ℝ) {D M : ℝ} (hD : 1 ≤ D) {S F : Field} (hS : Adm 2 S)
    (hS3 : InH 3 S) (hS' : PiS S = S) (hM : GN.SupBd S M) (hW : wiener S ≤ |r|) (hF : Adm 2 F)
    (hF3 : InH 3 F) (hF' : PiF F = F) :
    ‖X2Form 1 2 r τ S S (zOf 2 F) (zOf 2 (Lop τ S F)) +
        ZForm 1 2 r τ S S (zOf 2 F) (zOf 2 (Lop τ S F)) -
        (famQ 2 r D).src τ S S S (zOf 2 F) (zOf 2 F)‖ ≤ G₂ r D M S * hnorm 2 F ^ 2 := by
  have hq : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hq
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hF2 : InH ((2 : ℕ) : ℝ) F := by simpa using hF.inH
  obtain ⟨hz, nz⟩ := l2_zOf hF2 hF.mean
  have nz' : l2n (zOf 2 F) = hnorm 2 F := by simpa using nz
  have hz' : PiF (zOf 2 F) = zOf 2 F := Fam.PiF_zOf hF'
  have hS3' : MZ 3 S := ⟨hS3, hS.mean⟩
  have hF3' : MZ 3 F := ⟨hF3, hF.mean⟩
  have hw : Summable fun k => ‖zOf 2 (Lop τ S F) k‖ ^ 2 := by
    have h1 := Lop_two (τ := τ) hS3' hF3'
    have h2 : InH ((2 : ℕ) : ℝ) (Lop τ S F) := by simpa using h1.inH
    exact (l2_zOf h2 h1.mean).1
  have hL2 := QLF_bound τ hS hS' hM hF 2 (by simpa using hF3)
  have hL1 := QLF_bound τ hS hS' hM hF 1 (by simpa using hF.inH)
  have h0 : QLF τ S F 0 = 0 := by simp [QLF, PiF]
  have hwl : Summable fun k => ‖zOf 2 (QLF τ S F) k‖ ^ 2 := (l2_zOf hL2.1 h0).1
  have hS2 := mz_l2 (by norm_num) hS.mz
  have hFl2 := mz_l2 (by norm_num) hF.mz
  have hsol := QLF_sol τ hS2 hFl2
  rw [Y_split₂ hr τ hD hS.mz hS' hF.mz hF' hF.sol hw hwl]
  have e : ∀ A B C P H : ℂ, A + B + C + (P + H) - P = A + B + C + H := fun A B C P H => by ring
  rw [e]
  have hQ1 : MZ 1 (QLF τ S F) := ⟨by simpa using hL1.1, h0⟩
  have hQ2 : MZ 2 (QLF τ S F) := ⟨by simpa using hL2.1, h0⟩
  have t1 := two_X2' hr τ hD hS.mz hS' hS.real hF.mz hQ1 hF'
  have t2 := two_Z' hr1 τ hS hS' hM hW hF.mz hF' hF.sol hQ2 (PiF_QLF τ S F) hsol
  have hn : hnorm 1 (QLF τ S F) ≤ 2 * CLow 1 * M * hnorm 2 F := by
    simpa using hL1.2
  have hb := hnorm_nonneg 2 F
  have hX0 : 0 ≤ X2Cf r D S := X2Cf_nn r hD S
  have hZ0 : 0 ≤ ZCf r M S := ZCf_nn hr1 hM0 S
  have t12 : ‖X2Form 1 2 r τ S S (zOf 2 F) (zOf 2 (QLF τ S F)) +
      ZForm 1 2 r τ S S (zOf 2 F) (zOf 2 (QLF τ S F))‖ ≤
      (X2Cf r D S + ZCf r M S) * (2 * CLow 1 * M) * hnorm 2 F ^ 2 := by
    refine (norm_add_le _ _).trans ((add_le_add t1 t2).trans ?_)
    have h3 : hnorm 1 (QLF τ S F) * hnorm 2 F ≤ 2 * CLow 1 * M * hnorm 2 F * hnorm 2 F :=
      mul_le_mul_of_nonneg_right hn hb
    have h4 := mul_le_mul_of_nonneg_left h3 (add_nonneg hX0 hZ0)
    calc _ = (X2Cf r D S + ZCf r M S) * (hnorm 1 (QLF τ S F) * hnorm 2 F) := by ring
      _ ≤ _ := h4
      _ = _ := by ring
  have t3 := YLForm_high_le hr τ D hS.mz hS' hz hz hz' (norm_muH_le D)
  have t4 := (YLForm_sep_le (D := D) hr τ hD hS.mz hS' hS.mz hS' hS.mz hS3 hS' hz hz hz'
    (μ := fun x => ((muS D x : ℝ) : ℂ)) fun x => by
      rw [Complex.norm_real, Real.norm_of_nonneg (muS_nonneg D x)]).2
  have t5 := (HtQ_le (s := 2) (Or.inr rfl) hr τ hD hS.mz hS' (hS.inH.mono (by norm_num)) hS' hS.inH
    hS' hz hz hz').2
  rw [nz'] at t3 t4 t5
  have hH : 2 ^ 22 * D / |r| ^ 2 * (hnorm 2 F * hnorm 2 S * Real.sqrt 17 * (hnorm 2 F *
      hnorm 1 S * Real.sqrt (9 + 8 * Real.log (4 * D))) * wiener S) =
      2 ^ 22 * D / |r| ^ 2 * (hnorm 2 S * Real.sqrt 17 *
        (hnorm 1 S * Real.sqrt (9 + 8 * Real.log (4 * D))) * wiener S) * hnorm 2 F ^ 2 := by ring
  rw [hH] at t5
  calc _ ≤ _ := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add t12 t3) t4) t5
    _ = _ := by
        simp only [G₂]
        ring

end OVNS.Quant.Metric

end
