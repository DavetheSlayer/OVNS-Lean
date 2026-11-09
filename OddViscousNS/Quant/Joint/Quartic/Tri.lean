import OddViscousNS.Quant.Joint.Quartic.FibreBd

/-!
# The fourth correction: the proper trilinear map (step J5, node N11)

Bodies 34, 35: "the fixed-largest-output positive Cauchy bound, with all sorted slots and both real
orientations.  It can be used on three different arrays and for a coefficientwise smaller kernel."

`kT q (p, q')` is the proper near kernel of a triad, summed over its three possible longest legs.
* `tri_pos`: `∑ kT α_p β_q γ_{−(p+q)} ≤ 3 √𝔐_P ‖α‖ ‖β‖ ‖γ‖`, on three different arrays;
* `near_ker`: on a fast triad, the kernel `kerB j` of the cyclic sum, at a near helicity, is at most
  `13 m² K^{2j} kT`, with the two weights: `m²K⁴ ≤ 4 |p|²|q|²|e|²` (slots `H², H², H²`, Body 34),
  `m²K² ≤ K |p||q||e|` (one `H²` on the largest leg, `H¹` on the two others, Body 35).

The regions are those of `H2/Cubic.lean`, applied to the field `0`: the amplitudes are not used.
-/

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric OVNS.Quant.H2

variable {α β γ : Mode → ℝ} {A B C : ℝ}

/-- The proper kernel on the box labels. -/
def kB (q : ℝ) (y : Mode × Mode) : ℝ := if y.2 ∈ nearBox y.1 then propKer q y.1 y.2 else 0

lemma kB_nonneg (q : ℝ) (y : Mode × Mode) : 0 ≤ kB q y := by
  unfold kB
  split_ifs
  · exact propKer_nonneg q _ _
  · exact le_rfl

/-- The proper kernel of a triad: its three possible longest legs. -/
def kT (q : ℝ) (x : Mode × Mode) : ℝ := kB q (eA x) + kB q (eB x) + kB q (eC x)

lemma kT_nonneg (q : ℝ) (x : Mode × Mode) : 0 ≤ kT q x :=
  add_nonneg (add_nonneg (kB_nonneg q _) (kB_nonneg q _)) (kB_nonneg q _)

/-- A box term is a kernel times the arrays. -/
lemma boxK_eq (q : ℝ) (U V W : Mode → ℝ) (y : Mode × Mode) :
    boxK (propKer q) U V W y = kB q y * (U y.1 * (V y.2 * W (y.1 - y.2))) := by
  unfold boxK kB
  split_ifs
  · ring
  · ring

/-- One region. -/
lemma box_sb (q : ℝ) {U V W : Mode → ℝ} {a b c : ℝ} (hU : L2B U a) (hV : L2B V b) (hW : L2B W c) :
    SB (boxK (propKer q) U V W) (Real.sqrt (MomP q) * (a * b * c)) := by
  obtain ⟨s, h⟩ := boxK_tsum_le (propKer_nonneg q) (sum_propKer_sq q) hU.nn hV.nn hW.nn hU.s hV.s hW.s
  refine ⟨s, h.trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  exact mul_le_mul (mul_le_mul hU.le hV.le (Real.sqrt_nonneg _) hU.bd_nonneg) hW.le
    (Real.sqrt_nonneg _) (mul_nonneg hU.bd_nonneg hV.bd_nonneg)

/-- **The proper trilinear map on three arrays.** -/
theorem tri_pos (q : ℝ) (hα : L2B α A) (hβ : L2B β B) (hγ : L2B γ C) :
    SB (fun x : Mode × Mode => kT q x * (α x.1 * β x.2 * γ (-(x.1 + x.2))))
      (3 * (Real.sqrt (MomP q) * (A * B * C))) := by
  have b1 := box_sb q hα.refl hβ hγ
  have b2 := box_sb q hβ.refl hα hγ
  have b3 := box_sb q hγ.refl hα hβ
  have s1 : SB (fun x => boxK (propKer q) (refl α) β γ (eA x))
      (Real.sqrt (MomP q) * (A * B * C)) := ⟨perm_summable eA b1.1, (perm_tsum eA).le.trans b1.2⟩
  have s2 : SB (fun x => boxK (propKer q) (refl β) α γ (eB x))
      (Real.sqrt (MomP q) * (B * A * C)) := ⟨perm_summable eB b2.1, (perm_tsum eB).le.trans b2.2⟩
  have s3 : SB (fun x => boxK (propKer q) (refl γ) α β (eC x))
      (Real.sqrt (MomP q) * (C * A * B)) := ⟨perm_summable eC b3.1, (perm_tsum eC).le.trans b3.2⟩
  have hs := (s1.add s2).add s3
  have e3 : Real.sqrt (MomP q) * (A * B * C) + Real.sqrt (MomP q) * (B * A * C) +
      Real.sqrt (MomP q) * (C * A * B) = 3 * (Real.sqrt (MomP q) * (A * B * C)) := by ring
  rw [e3] at hs
  have e : ∀ x : Mode × Mode, boxK (propKer q) (refl α) β γ (eA x) +
      boxK (propKer q) (refl β) α γ (eB x) + boxK (propKer q) (refl γ) α β (eC x) =
      kT q x * (α x.1 * β x.2 * γ (-(x.1 + x.2))) := fun x => by
    have e1 : (eA x).1 = -x.1 := rfl
    have e2 : (eA x).2 = x.2 := rfl
    have e3 : (eB x).1 = -x.2 := rfl
    have e4 : (eB x).2 = x.1 := rfl
    have e5 : (eC x).1 = x.1 + x.2 := rfl
    have e6 : (eC x).2 = x.1 := rfl
    have g1 : -x.1 - x.2 = -(x.1 + x.2) := by abel
    have g2 : -x.2 - x.1 = -(x.1 + x.2) := by abel
    have g3 : x.1 + x.2 - x.1 = x.2 := by abel
    simp only [boxK_eq, e1, e2, e3, e4, e5, e6, g1, g2, g3, Metric.refl, neg_neg, kT]
    ring
  simp only [e] at hs
  exact hs

/-! ### The near kernel of a fast triad -/

/-- The longest leg of a triad. -/
def mxL (p q : Mode) : ℝ := max (absk p) (max (absk q) (absk (p + q)))

lemma le_mxL (p q : Mode) : absk p ≤ mxL p q ∧ absk q ≤ mxL p q ∧ absk (p + q) ≤ mxL p q :=
  ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

/-- The longest leg against any two legs. -/
lemma mxL_tri (p q : Mode) : mxL p q ≤ absk q + absk (p + q) ∧ mxL p q ≤ absk p + absk (p + q) ∧
    mxL p q ≤ absk p + absk q := by
  have h1 : absk p ≤ absk (p + q) + absk q := by
    simpa using absk_sub_le (p + q) q
  have h2 : absk q ≤ absk (p + q) + absk p := by
    have := absk_sub_le (p + q) p
    simpa using this
  have h3 := absk_add_le p q
  have n1 := absk_nonneg p
  have n2 := absk_nonneg q
  have n3 := absk_nonneg (p + q)
  refine ⟨max_le ?_ (max_le ?_ ?_), max_le ?_ (max_le ?_ ?_), max_le ?_ (max_le ?_ ?_)⟩ <;> linarith

/-- **The near kernel of a fast triad.** -/
theorem near_ker (r : ℝ) {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0) (hr3 : (-(p + q)) 2 ≠ 0) :
    ∃ mn : ℝ, (absk p ≤ mn ∨ absk q ≤ mn ∨ absk (p + q) ≤ mn) ∧
      mn ^ 2 * mxL p q ^ 4 ≤ 4 * (absk p ^ 2 * absk q ^ 2 * absk (p + q) ^ 2) ∧
      mn ^ 2 * mxL p q ^ 2 ≤ mxL p q * (absk p * absk q * absk (p + q)) ∧
      ∀ (j : ℕ) (a b c : Sgn), NearT a b c p q →
        kerB j (r * Phi a b c p q) mn (mxL p q) ≤
          13 * mn ^ 2 * mxL p q ^ (2 * j) * kT |r| (p, q) := by
  have hR : IsReal (0 : Field) := fun k => by
    ext i
    simp [conjV]
  obtain ⟨e, L, u, he, hex, hu, hpat, -, hmx, hmn⟩ := exists_region hR hp3 hq3 hr3
  obtain ⟨hK, hy, hl, htri, hyK, hlK⟩ := box_legs hu
  have hL : absk L = mxL p q := by
    refine le_antisymm ?_ (max_le hmx.1 (max_le hmx.2.1 hmx.2.2))
    have h0 := le_mxL p q
    rcases he with rfl | rfl | rfl
    · have : L = -p := (congrArg Prod.fst hex).symm
      rw [this, absk_neg]
      exact h0.1
    · have : L = -q := (congrArg Prod.fst hex).symm
      rw [this, absk_neg]
      exact h0.2.1
    · have : L = p + q := (congrArg Prod.fst hex).symm
      rw [this]
      exact h0.2.2
  have hprod : absk L * absk u * absk (L - u) = absk p * absk q * absk (p + q) := by
    rcases he with rfl | rfl | rfl
    · have e1 : L = -p := (congrArg Prod.fst hex).symm
      have e2 : u = q := (congrArg Prod.snd hex).symm
      have e3 : L - u = -(p + q) := by rw [e1, e2]; abel
      rw [e3, e1, e2, absk_neg, absk_neg]
    · have e1 : L = -q := (congrArg Prod.fst hex).symm
      have e2 : u = p := (congrArg Prod.snd hex).symm
      have e3 : L - u = -(p + q) := by rw [e1, e2]; abel
      rw [e3, e1, e2, absk_neg, absk_neg]
      ring
    · have e1 : L = p + q := (congrArg Prod.fst hex).symm
      have e2 : u = p := (congrArg Prod.snd hex).symm
      have e3 : L - u = q := by rw [e1, e2]; abel
      rw [e3, e1, e2]
      ring
  have hm0 := minLeg_pos hu
  have hmy : minLeg u L ≤ absk u := min_le_left _ _
  have hml : minLeg u L ≤ absk (L - u) := min_le_right _ _
  have hk : kB |r| (L, u) ≤ kT |r| (p, q) := by
    have h1 := kB_nonneg |r| (eA (p, q))
    have h2 := kB_nonneg |r| (eB (p, q))
    have h3 := kB_nonneg |r| (eC (p, q))
    have e0 : kB |r| (e (p, q)) = kB |r| (L, u) := by rw [hex]
    unfold kT
    rcases he with rfl | rfl | rfl <;> linarith
  have hk' : propKer |r| L u ≤ kT |r| (p, q) := by
    have : kB |r| (L, u) = propKer |r| L u := ite_eq_left hu
    linarith
  refine ⟨minLeg u L, hmn, ?_, ?_, fun j a b c hN => ?_⟩
  · have e1 : absk p ^ 2 * absk q ^ 2 * absk (p + q) ^ 2 =
        (absk L * absk u * absk (L - u)) ^ 2 := by rw [hprod]; ring
    rw [← hL, e1]
    unfold minLeg
    set K := absk L
    set y := absk u
    set l := absk (L - u)
    rcases le_total y l with h | h
    · rw [min_eq_left h]
      have h3 : K ^ 2 ≤ 4 * l ^ 2 := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ y ^ 2 * K ^ 2)
      nlinarith
    · rw [min_eq_right h]
      have h3 : K ^ 2 ≤ 4 * y ^ 2 := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ l ^ 2 * K ^ 2)
      nlinarith
  · rw [← hL, ← hprod]
    have h2 : minLeg u L ^ 2 ≤ absk u * absk (L - u) := by
      rw [sq]
      exact mul_le_mul hmy hml hm0.le hy.le
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ absk L ^ 2)
    nlinarith only [h3]
  · obtain ⟨s₁, s₂, hs⟩ := hpat a b c
    have h1 := kerB_le_nearKerSum j r _ hu hs hN.2.1 hN.2.2
    rw [← hL]
    refine h1.trans ?_
    have e : 13 * minLeg u L ^ 2 * absk L ^ (2 * j + 1) * nearKerSum |r| L u =
        13 * minLeg u L ^ 2 * absk L ^ (2 * j) * propKer |r| L u := by
      unfold propKer
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hk' (by positivity)

end OVNS.Quant.Quartic

end
