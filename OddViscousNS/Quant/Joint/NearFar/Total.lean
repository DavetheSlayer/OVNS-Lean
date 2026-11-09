import OddViscousNS.Quant.Joint.NearFar.Main

/-!
# The cubic and the quartic together

`E_s⁰ + C_{4,s}` on a joint piece, with `nf_s = −heat + nearD(F; N_rest) + farD(F; N_F) + Rem4`:

* `total_one_joint`: `|E⁰ + C_{4,1}| ≤ 2η a²`, `|nfOne| ≤ 4η b² + (η/2) b`.
* `total_two_joint`: `|E₂⁰ + C_{4,2}| ≤ 2η b²`,
  `|nfTwo| ≤ 4η c² + (m + 2 g₁ c_y²) b² + (A c_y² + B)`, with `∫_clip (m + 2 g₁ c_y²) ≤ 3η` and
  `∫_clip (A c_y² + B) ≤ η T²`.

The thresholds are `qTot₁`, `qTot₂`: `qTot₁_below`, `qTot₂_below`.
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.NearFar

open OVNS.Quant.Metric OVNS.Quant.Quartic

variable {μ φ X R r η CS cS KN KP R₀ Tp : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps}
  {s t : ℝ} {q : Caps → ℝ} {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop}

/-- What the near and far differentials and the quartic add at weight one. -/
def nfOne (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -cubicHeat r (r * u) (Fp r g y u) + nearD 1 (-1) r (r * u) (Fp r g y u) (fastRest r g y u) +
    farD 1 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) + Rem4 1 r g y u

/-- What the near and far differentials and the quartic add at weight two. -/
def nfTwo (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -H2.cubicHeat2 r (r * u) (Fp r g y u) +
    nearD 2 (-1) r (r * u) (Fp r g y u) (fastRest r g y u) +
    farD 2 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) + Rem4 2 r g y u

/-- **The whole threshold of weight one**, with the quartic. -/
def qTot₁ (η X R : ℝ) (caps : Caps) : ℝ :=
  max (qNF₁ η X R caps) (qOneFull (2 ^ 26 * Real.exp 5 / η ^ 2) X R caps)

/-- **The whole threshold of weight two**, with the quartic. -/
def qTot₂ (η CS cS X R : ℝ) (caps : Caps) : ℝ :=
  max (qNF₂ η CS cS X R caps) (2 ^ 15 / η * thrTwo CS cS X R caps + flrTwo R caps)

theorem qTot₁_below (hη : 0 < η) : JointBelow fun X R caps ↦ qTot₁ η X R caps :=
  (qNF₁_below hη).sup (qOneFull_below (by positivity))

theorem qTot₂_below (hCS : 0 ≤ CS) (hη : 0 < η) :
    JointBelow fun X R caps ↦ qTot₂ η CS cS X R caps :=
  (qNF₂_below hCS hη).sup (qTwo_below hCS (by positivity))

/-- `1 ≤ K_P`, as the quartics ask. -/
lemma one_le_KP (hη : 0 < η) (hη1 : η ≤ 1) (hKP : kP / η ≤ KP) : 1 ≤ KP := by
  have hc := c4_pos
  have h1 : 1 ≤ kP := by
    unfold kP H2.cHeat2
    nlinarith only [hc]
  have h2 : kP ≤ kP / η := by
    rw [le_div_iff₀ hη]
    have := kP_pos
    nlinarith only [this, hη1]
  linarith

/-- The near share of the quartics, from `NearPaid`. -/
lemma nearP_zq (hdom : JDom R₀ X R) (hKP : 1 ≤ KP)
    (h : NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP caps |r|) :
    nearP |r| ≤ zq X R := by
  obtain ⟨-, -, p3⟩ := proper_shares (zero_le_one.trans hKP) hdom
    (nearP_nonneg (abs_nonneg r)) h.2
  exact nearP_le_zq hdom hKP (abs_nonneg r) p3

/-- **Weight one, total**: all that `E⁰ + C_{4,1}` adds to the `H¹` energy.  `N_f = η/2` is a
constant, so its `L²` norm on a piece of length `T_p` is `(η/2) √T_p`. -/
theorem total_one_joint (hdom : JDom R₀ X R) (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece Tp (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP) Sl r g y Ty caps s t)
    (hCS : 0 ≤ CS) (hη : 0 < η) (hη1 : η ≤ 1) (hKN : kN / η ≤ KN) (hKP : kP / η ≤ KP)
    (hq : qTot₁ η X R caps ≤ q caps) :
    ∀ u ∈ Set.Icc s t,
      |cubicCorr r g y u + C4 1 r g y u| ≤ 2 * η * fastNorm 1 r g y u ^ 2 ∧
      |nfOne r g y u| ≤ 4 * η * fastNorm 2 r g y u ^ 2 + η / 2 * fastNorm 2 r g y u := by
  have hq1 := hq.trans hp.thr
  have hA : qNF₁ η X R caps ≤ q caps := (le_max_left _ _).trans hq
  have hB : qOneFull (2 ^ 26 * Real.exp 5 / η ^ 2) X R caps ≤ |r| :=
    (le_max_right _ _).trans hq1
  have hfl0 : jointSlowFloor X R caps ≤ |r| := (le_max_left _ _).trans (hA.trans hp.thr)
  obtain ⟨hX, -, -, -, hr⟩ := floor_setup hdom hfl0
  have hP := nearP_zq hdom (one_le_KP hη hη1 hKP) hp.nearPaid
  have n := nf_one_joint hdom h hp hCS hη hKN hKP hA
  have Q4 := quartic_one_piece hdom h hr hp.hs hp.ht hp.onPrefix hη hη1 hB hP
  intro u hu
  obtain ⟨n1, n2, n3, n4⟩ := n u hu
  obtain ⟨q1, q2⟩ := Q4 u hu
  have hf := role18 h hX (Q0_of_slow hfl0) hp.hs hp.ht hp.onPrefix hu
  have hb0 : 0 ≤ fastNorm 2 r g y u := hnorm_nonneg _ _
  constructor
  · have e : cubicCorr r g y u = cubicE 1 (-1) r (r * u) (Fp r g y u) := rfl
    rw [e]
    refine (abs_add_le _ _).trans ?_
    linarith
  · have h1 : |nfOne r g y u| ≤ |cubicHeat r (r * u) (Fp r g y u)| +
        |nearD 1 (-1) r (r * u) (Fp r g y u) (fastRest r g y u)| +
        |farD 1 (-1) r (r * u) (Fp r g y u) (fastNL r g y u)| + |Rem4 1 r g y u| := by
      refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
      refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
      refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
      rw [abs_neg]
    have h2 : η * hnorm 1 (Hpsi r g y u) * fastNorm 2 r g y u ≤ η / 2 * fastNorm 2 r g y u := by
      refine mul_le_mul_of_nonneg_right ?_ hb0
      nlinarith only [hf, hη]
    linarith

/-- **Weight two, total**: all that `E₂⁰ + C_{4,2}` adds to the `H²` energy. -/
theorem total_two_joint (hdom : JDom R₀ X R) (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece Tp (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t)
    (hCS : 0 ≤ CS) (hη : 0 < η) (hη1 : η ≤ 1) (hKN : kN / η ≤ KN) (hKP : kP / η ≤ KP)
    (hq : qTot₂ η CS cS X R caps ≤ q caps) :
    ∃ m A B g₁ : ℝ, 0 ≤ m ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ g₁ ∧
      (∀ u ∈ Set.Icc s t, |H2.cubicCorr2 r g y u + C4 2 r g y u| ≤
        2 * η * fastNorm 2 r g y u ^ 2) ∧
      (∀ᵐ u ∂(volume.restrict (Set.Icc s t)), |nfTwo r g y u| ≤
        4 * η * fastNorm 3 r g y u ^ 2 +
          (m + 2 * g₁ * hnorm 3 (corrSlow r g y u) ^ 2) * fastNorm 2 r g y u ^ 2 +
          (A * hnorm 3 (corrSlow r g y u) ^ 2 + B)) ∧
      ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ lamI X R caps →
        (∫ u in u₁..u₂, (m + 2 * g₁ * hnorm 3 (corrSlow r g y u) ^ 2)) ≤ 3 * η ∧
        (∫ u in u₁..u₂, (A * hnorm 3 (corrSlow r g y u) ^ 2 + B)) ≤ η * jointT X R ^ 2 := by
  have hq1 := hq.trans hp.thr
  have hA' : qNF₂ η CS cS X R caps ≤ q caps := (le_max_left _ _).trans hq
  have hB' : 2 ^ 15 / η * thrTwo CS cS X R caps + flrTwo R caps ≤ |r| :=
    (le_max_right _ _).trans hq1
  have hfl0 : jointSlowFloor X R caps ≤ |r| := (le_max_left _ _).trans (hA'.trans hp.thr)
  obtain ⟨-, -, -, -, hr⟩ := floor_setup hdom hfl0
  have hP := nearP_zq hdom (one_le_KP hη hη1 hKP) hp.nearPaid
  obtain ⟨g₁, hg0, s1, s2, s3⟩ := nf_two_joint hdom h hp hCS hη hKN hKP hA'
  obtain ⟨m, A, B, hm, hA, hB, c1, c2, c3, c4'⟩ := quartic_two_piece hdom h hr hp.hs hp.hst hp.ht
    hp.onPrefix hp.sup hCS hp.slow hη hB' hP
  refine ⟨m, A, B, g₁, hm, hA, hB, hg0, fun u hu => ?_, ?_, fun u₁ u₂ h1 h12 h2 hlen => ?_⟩
  · have e : H2.cubicCorr2 r g y u = cubicE 2 (-1) r (r * u) (Fp r g y u) := rfl
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have := s1 u hu
    have := c1 u hu
    linarith
  · filter_upwards [s2, c2] with u b1 b2
    obtain ⟨b3, b4, b5⟩ := b1
    have h1 : |nfTwo r g y u| ≤ |H2.cubicHeat2 r (r * u) (Fp r g y u)| +
        |nearD 2 (-1) r (r * u) (Fp r g y u) (fastRest r g y u)| +
        |farD 2 (-1) r (r * u) (Fp r g y u) (fastNL r g y u)| + |Rem4 2 r g y u| := by
      refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
      refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
      refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
      rw [abs_neg]
    nlinarith only [h1, b2, b3, b4, b5]
  · have hsub : Set.uIcc u₁ u₂ ⊆ Set.uIcc s t := by
      rw [Set.uIcc_of_le h12, Set.uIcc_of_le hp.hst]
      exact Set.Icc_subset_Icc h1 h2
    have hi : IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume u₁ u₂ :=
      hp.slow.cy_int.mono_set hsub
    refine ⟨?_, c4' u₁ u₂ h1 h12 h2 hlen⟩
    have hg := s3 u₁ u₂ h1 h12 h2 hlen
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (hi.const_mul (2 * g₁)), intervalIntegral.integral_const, smul_eq_mul]
    have e : (∫ u in u₁..u₂, 2 * g₁ * hnorm 3 (corrSlow r g y u) ^ 2) =
        2 * ∫ u in u₁..u₂, g₁ * hnorm 3 (corrSlow r g y u) ^ 2 := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    rw [e]
    have t1 : (u₂ - u₁) * m ≤ lamI X R caps * m := mul_le_mul_of_nonneg_right hlen hm
    linarith

end OVNS.Quant.NearFar

end
