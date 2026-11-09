import OddViscousNS.Quant.Joint.NearFar.Degree

/-!
# The near and far differentials on a joint piece

The statements N14, N15 apply.  Take `K_N ≥ kN/η`, `K_P ≥ kP/η`, and put `qNF₁`, `qNF₂` into `q₁`,
`q₂`.  Then, on a joint piece:

* `nf_one_joint`: `|E⁰| ≤ η a²`, and the heat, `nearD₁(F; N_rest)`, `farD₁(F; N_F)` are `≤ η b²`,
  one by one.  Nothing is charged to `N_f`, `f_f`, `m`.
* `nf_two_joint`: `|E⁰₂| ≤ η b²`, the heat is `≤ η c²`, and `nearD₂(F; N_rest)`, `farD₂(F; N_F)` are
  `≤ η c² + g₁ c_y² b²`, with `∫_clip g₁ c_y² ≤ η`.  Nothing is charged to `H`.

Each monomial of `K_N`, `K_P`, `q₁`, `q₂` is a separate share; none replaces another.
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.NearFar

open OVNS.Quant.Metric OVNS.Quant.Quartic
open OVNS.Quant.H2 (ae_inH3_split)

variable {X R r η CS cS KN KP R₀ Tp : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps}
  {s t : ℝ} {q : Caps → ℝ} {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop}

/-- The clip price of a Young multiplier. -/
lemma clip_share {ν E PS : ℝ} (hη : 0 < η) (hPS : 0 ≤ PS) (h0 : 0 ≤ ν * E)
    (h : ν * E * Real.sqrt PS ≤ η / 4) : 1 / η * (ν * E) ^ 2 * (4 * PS) ≤ η / 4 := by
  have hw0 : 0 ≤ ν * E * Real.sqrt PS := mul_nonneg h0 (Real.sqrt_nonneg _)
  have h1 := pow_le_pow_left₀ hw0 h 2
  rw [mul_pow, Real.sq_sqrt hPS] at h1
  have e : 1 / η * (ν * E) ^ 2 * (4 * PS) = 4 / η * ((ν * E) ^ 2 * PS) := by ring
  rw [e]
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 4 / η)
  refine h2.trans (le_of_eq ?_)
  field_simp

/-- What both weights read off the floor. -/
lemma floor_setup (hdom : JDom R₀ X R) (hfl : jointSlowFloor X R caps ≤ |r|) :
    0 ≤ X ∧ 0 ≤ R - X ∧ Floor X (R - X) |r| caps ∧ 1 ≤ |r| ∧ r ≠ 0 := by
  have hX : 0 ≤ X := by linarith [hdom.one_lt_X]
  have hφ : 0 ≤ R - X := by linarith [hdom.X_le_R]
  have hF := Floor.of_slow hX hφ hfl
  have h1 : 1 ≤ |r| := by linarith [hF.one]
  exact ⟨hX, hφ, hF, h1, abs_pos.1 (by linarith)⟩

/-- **Weight one on a joint piece**: the static remainder, the heat, the near differential and the
FAR, each a separate share. -/
theorem nf_one_joint (hdom : JDom R₀ X R) (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece Tp (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP) Sl r g y Ty caps s t)
    (hCS : 0 ≤ CS) (hη : 0 < η) (hKN : kN / η ≤ KN) (hKP : kP / η ≤ KP)
    (hq : qNF₁ η X R caps ≤ q caps) :
    ∀ u ∈ Set.Icc s t,
      |cubicE 1 (-1) r (r * u) (Fp r g y u)| ≤ η * fastNorm 1 r g y u ^ 2 ∧
      |cubicHeat r (r * u) (Fp r g y u)| ≤ η * fastNorm 2 r g y u ^ 2 ∧
      |nearD 1 (-1) r (r * u) (Fp r g y u) (fastRest r g y u)| ≤
        η * fastNorm 2 r g y u ^ 2 ∧
      |farD 1 (-1) r (r * u) (Fp r g y u) (fastNL r g y u)| ≤
        η * fastNorm 2 r g y u ^ 2 := by
  have hq1 := hq.trans hp.thr
  have hfl0 : jointSlowFloor X R caps ≤ |r| := (le_max_left _ _).trans hq1
  have hfar : 2 ^ 14 / η * tNF₁ caps ≤ |r| := (le_max_right _ _).trans hq1
  obtain ⟨hX, -, -, hr1, hr⟩ := floor_setup hdom hfl0
  have hKN0 : 0 ≤ KN := (div_pos kN_pos hη).le.trans hKN
  have hKP0 : 0 ≤ KP := (div_pos kP_pos hη).le.trans hKP
  have hS := Shares.of_paid hdom hKN0 hKP0 hCS (abs_nonneg r) hp.nearPaid
  have hEx := Ex_pos cS R
  have hM0 : 0 ≤ CS * Ex cS R * R := mul_nonneg (mul_nonneg hCS hEx.le) hdom.R_pos.le
  intro u hu
  have hu0 := hp.hs.trans hu.1
  have huT := lt_lifespan hu.2 hp.ht
  obtain ⟨c1, c2, -, c4', c5⟩ := hp.onPrefix.1 u hu
  have hf := role18 h hX (Q0_of_slow hfl0) hp.hs hp.ht hp.onPrefix hu
  exact ⟨static_one_le h hr1 hu0 huT hη hKP c2 hS, heat_one_le h hr1 hu0 huT hη hKP c2 hS,
    near_one_le h hr hu0 huT hη hKN hM0 c1 c2 (hp.sup u hu) hf hS,
    far_one_le h hr hu0 huT hη (c5.trans (le_cp _)) (c4'.trans (le_cp _)) (c2.trans (le_cp _))
      hf hfar⟩

/-- **Weight two on a joint piece.** -/
theorem nf_two_joint (hdom : JDom R₀ X R) (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece Tp (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t)
    (hCS : 0 ≤ CS) (hη : 0 < η) (hKN : kN / η ≤ KN) (hKP : kP / η ≤ KP)
    (hq : qNF₂ η CS cS X R caps ≤ q caps) :
    ∃ g₁ : ℝ, 0 ≤ g₁ ∧
      (∀ u ∈ Set.Icc s t,
        |cubicE 2 (-1) r (r * u) (Fp r g y u)| ≤ η * fastNorm 2 r g y u ^ 2) ∧
      (∀ᵐ u ∂(volume.restrict (Set.Icc s t)),
        |H2.cubicHeat2 r (r * u) (Fp r g y u)| ≤ η * fastNorm 3 r g y u ^ 2 ∧
        |nearD 2 (-1) r (r * u) (Fp r g y u) (fastRest r g y u)| ≤ η * fastNorm 3 r g y u ^ 2 +
          g₁ * hnorm 3 (corrSlow r g y u) ^ 2 * fastNorm 2 r g y u ^ 2 ∧
        |farD 2 (-1) r (r * u) (Fp r g y u) (fastNL r g y u)| ≤ η * fastNorm 3 r g y u ^ 2 +
          g₁ * hnorm 3 (corrSlow r g y u) ^ 2 * fastNorm 2 r g y u ^ 2) ∧
      ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ lamI X R caps →
        ∫ u in u₁..u₂, g₁ * hnorm 3 (corrSlow r g y u) ^ 2 ≤ η := by
  have hq1 := hq.trans hp.thr
  have hfl0 : jointSlowFloor X R caps ≤ |r| := (le_max_left _ _).trans hq1
  have ht2 : tNF₂ η CS cS X R caps ≤ |r| := (le_max_right _ _).trans hq1
  obtain ⟨hX, hφ, hFl, hr1, hr⟩ := floor_setup hdom hfl0
  have hq0 : 0 < |r| := by linarith
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  have hKN0 : 0 ≤ KN := (div_pos kN_pos hη).le.trans hKN
  have hKP0 : 0 ≤ KP := (div_pos kP_pos hη).le.trans hKP
  have hS := Shares.of_paid hdom hKN0 hKP0 hCS (abs_nonneg r) hp.nearPaid
  have hEx := Ex_pos cS R
  have hC : 0 ≤ CS * Ex cS R := mul_nonneg hCS hEx.le
  have hM0 : 0 ≤ CS * Ex cS R * R := mul_nonneg hC hR0.le
  have hcF := cFar_pos
  set L := fibL R caps with hLd
  have hL0 : 0 ≤ L := fibL_nonneg hR0 caps
  set PS := priceS CS cS X R caps with hPSd
  have hPS : 0 ≤ PS := priceS_nonneg hCS cS X hR0.le caps
  have hrt := Real.sqrt_nonneg PS
  obtain ⟨q1, q2, q3, q4, q5⟩ := tNF₂_parts hη hCS hR0 hφ ht2
  -- the two multipliers
  set E := Eq₂ (R - X) r with hEd
  have hE0 : 0 ≤ E := Eq_nonneg (r := r) h
  have hE1 : E ≤ 1 := (hFl.Eq_le hX hφ).trans (by norm_num)
  set νN := nearC₀ * nearN |r| with hνN
  set νF := H2.cFar / |r| with hνF
  have hνN0 : 0 ≤ νN := mul_nonneg nearC₀_pos.le (nearN_nonneg _)
  have hνF0 : 0 ≤ νF := by positivity
  set gN := 1 / η * (νN * E) ^ 2 with hgN
  set gF := 1 / η * (νF * (E + 20 * L)) ^ 2 with hgF
  have hgN0 : 0 ≤ gN := by positivity
  have hgF0 : 0 ≤ gF := by positivity
  have hcN : gN * (4 * PS) ≤ η / 4 := by
    refine clip_share hη hPS (by positivity) ?_
    have h4 : 4 * nearC₀ * nearN |r| ≤ η := by
      refine share_one (c₀ := kN) hη hKN ?_ (nearN_nonneg _) hS.flr
      have hC0 := nearC₀_pos
      have hCL1 := CLow_nonneg 1
      have hCL2 := CLow_nonneg 2
      have hcQ := cQone_nonneg
      have hcI := one_le_cI
      unfold kN
      nlinarith only [hC0, hCL1, hCL2, hcQ, hcI]
    have h5 : E * Real.sqrt PS ≤ 1 := by
      have e : E * Real.sqrt PS = 64 * c4 * (R - X) * Real.sqrt PS / |r| := by
        simp only [hEd, Eq₂]
        ring
      rw [e, div_le_one hq0]
      exact q4
    have h6 := mul_le_mul_of_nonneg_left h5 hνN0
    have e : νN * E * Real.sqrt PS = νN * (E * Real.sqrt PS) := by ring
    rw [e]
    have h7 : νN ≤ η / 4 := by
      simp only [hνN]
      linarith
    linarith
  have hcF' : gF * (4 * PS) ≤ η / 4 := by
    refine clip_share hη hPS (by positivity) ?_
    have h5 : νF * ((1 + 20 * L) * Real.sqrt PS) ≤ η / 4 := by
      have e : 4 * H2.cFar / η * ((1 + 20 * L) * Real.sqrt PS) =
          4 * H2.cFar * ((1 + 20 * L) * Real.sqrt PS) / η := by ring
      rw [e, div_le_iff₀ hη] at q3
      have e2 : νF * ((1 + 20 * L) * Real.sqrt PS) =
          H2.cFar * ((1 + 20 * L) * Real.sqrt PS) / |r| := by
        simp only [hνF]
        ring
      rw [e2, div_le_iff₀ hq0]
      linarith
    have h6 : (E + 20 * L) * Real.sqrt PS ≤ (1 + 20 * L) * Real.sqrt PS :=
      mul_le_mul_of_nonneg_right (by linarith) hrt
    have h7 := mul_le_mul_of_nonneg_left h6 hνF0
    have e : νF * (E + 20 * L) * Real.sqrt PS = νF * ((E + 20 * L) * Real.sqrt PS) := by ring
    rw [e]
    linarith
  refine ⟨gN + gF, by positivity, fun u hu => ?_, ?_, fun u₁ u₂ h1 h12 h2 hlen => ?_⟩
  · have hu0 := hp.hs.trans hu.1
    have huT := lt_lifespan hu.2 hp.ht
    exact static_two_le h hr1 hu0 huT hη hKP (hp.onPrefix.1 u hu).2.1 hS q5
  · filter_upwards [ae_inH3_split h hp.hs hp.hst hp.ht, ae_inH3_corr h hr hp.hs hp.hst hp.ht,
      ae_restrict_mem measurableSet_Icc] with u hu3 hz hu
    have hu0 := hp.hs.trans hu.1
    have huT := lt_lifespan hu.2 hp.ht
    obtain ⟨c1, c2, -, -, -⟩ := hp.onPrefix.1 u hu
    have hF := Fp_adm h hu0 huT
    have hcS := slow_three_le h hr hu0 huT hu3.1 hz (c2.trans (le_cp _)) q1
    have T : T2 X (R - X) (CS * Ex cS R * R) (hnorm 3 (corrSlow r g y u)) r g y u caps :=
      ⟨hu3.1, hu3.2, c1, c2, hp.sup u hu, hM0, hnorm_nonneg _ _, hcS, hFl, hX⟩
    have hLh : LhB (nrm (Fp r g y u)) L := lhB_fibL (R := R) (caps := caps) hF.inH
      (PiF_Fp r g y u) hR1 (c1.trans (le_cp _)) (c2.trans (le_cp _))
    have b1 := T.near_le h hu0 huT hη hKN hS
    have b2 := T.far_le h hu0 huT hη hLh hL0 q2
    have b3 := heat_two_le h hr1 hu0 huT hη hKP hu3.1 c2 hS q5
    set cy := hnorm 3 (corrSlow r g y u)
    set b := fastNorm 2 r g y u
    have hw : 0 ≤ cy ^ 2 * b ^ 2 := by positivity
    have t1 := mul_le_mul_of_nonneg_right
      (by linarith : gN ≤ gN + gF) hw
    have t2 := mul_le_mul_of_nonneg_right
      (by linarith : gF ≤ gN + gF) hw
    refine ⟨b3, b1.trans ?_, b2.trans ?_⟩
    · have e : 1 / η * (νN * E) ^ 2 * cy ^ 2 * b ^ 2 = gN * (cy ^ 2 * b ^ 2) := by
        simp only [hgN]
        ring
      rw [e]
      nlinarith only [t1]
    · have e : 1 / η * (νF * (E + 20 * L)) ^ 2 * cy ^ 2 * b ^ 2 = gF * (cy ^ 2 * b ^ 2) := by
        simp only [hgF]
        ring
      rw [e]
      nlinarith only [t2]
  · have hclip := slowOut_clip_le hp.slow hC hR1 h1 h12 h2 hlen
    rw [intervalIntegral.integral_const_mul]
    have h3 := mul_le_mul_of_nonneg_left hclip (by positivity : 0 ≤ gN + gF)
    have e : (gN + gF) * (4 * slowPrice CS (Ex cS R) R (lamI X R caps)) =
        gN * (4 * PS) + gF * (4 * PS) := by
      simp only [hPSd, priceS]
      ring
    rw [e] at h3
    linarith

end OVNS.Quant.NearFar

end
