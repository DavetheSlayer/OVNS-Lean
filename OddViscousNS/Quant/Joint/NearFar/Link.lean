import OddViscousNS.Quant.Joint.NearFar.Total
import OddViscousNS.Quant.Joint.Force.Final

/-!
# The near and far differentials in the form of N12

`ae_joint_final` (`Joint/Force/Final.lean`) writes
`joint_s RHS = joint_s T + metQ s + h0Part s + forceS s`.  There the filter has left the native
slot: `joint_s T` holds `cubicD s F fastQ`, `fastQ = fastNL + Hf`, and `forceS s` holds
`−cubicD s F Hf`.  So the slot that N14, N15 have to pay is

  `nfQ₁ = −heat + cubicD 1 F fastQ − J4 1 + Rem4 1`, and likewise `nfQ₂`,

which is `nfOne`, `nfTwo` plus `cubicD s F Hf` (`nfQ₁_eq`, `nfQ₂_eq`).  The filter is paid once more
here, at the same monomials: that costs a constant only.

* `filter_one_le`, `filter_two_joint`: `cubicD s F Hf`.
* `total_one_fastQ`, `total_two_fastQ`: the bounds of `nfQ₁`, `nfQ₂`, at `qTot₁`, `qTot₂`.
* `joint1T_C4`, `joint2T_C4`: `joint_s T − J4 s + Rem4 s` is the resonant slot, the bracket and
  `nfQ_s`.
* `joint1_left`, `joint2_left`: all of N11, N12 and this node at once: `joint_s RHS − J4 s + Rem4 s`
  is at most the resonant slot and the bracket, plus paid terms.
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.NearFar

open OVNS.Quant.Metric OVNS.Quant.Quartic
open OVNS.Quant.H2 (ae_inH3_split cubicHeat2)

variable {μ φ X R r η CS cS KN KP M R₀ Tp cy : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}
  {caps : Caps} {s t u : ℝ} {q : Caps → ℝ} {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop}

/-- The slot of `joint₁T` that this node pays. -/
def nfQ₁ (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -cubicHeat r (r * u) (Fp r g y u) + cubicD 1 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) -
    J4 1 r g y u + Rem4 1 r g y u

/-- The slot of `joint₂T` that this node pays. -/
def nfQ₂ (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -cubicHeat2 r (r * u) (Fp r g y u) + cubicD 2 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) -
    J4 2 r g y u + Rem4 2 r g y u

/-- `joint₁T` with the source of `C_{4,1}`. -/
theorem joint1T_C4 (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    joint1T r g y u + (-J4 1 r g y u + Rem4 1 r g y u) =
      -pair 1 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) +
        1 / 2 * (insT (famX2 1 r) 1 r g y u).re + 1 / 2 * (insT (famZ 1 r) 1 r g y u).re +
        nfQ₁ r g y u := by
  unfold joint1T nfQ₁
  ring

/-- `joint₂T` with the source of `C_{4,2}`. -/
theorem joint2T_C4 (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    joint2T r g y u + (-J4 2 r g y u + Rem4 2 r g y u) =
      -pair 2 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) +
        1 / 2 * (insT (famX2 2 r) 2 r g y u).re + 1 / 2 * (insT (famZ 2 r) 2 r g y u).re +
        nfQ₂ r g y u := by
  unfold joint2T nfQ₂
  ring

/-- `nfQ₁` at an `H³` time. -/
theorem nfQ₁_eq (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u)) :
    nfQ₁ r g y u = nfOne r g y u + cubicD 1 (-1) r (r * u) (Fp r g y u) (Hf r g y u) := by
  obtain ⟨hN, -, hH, -, -⟩ := link_facts h hr hu huT hF3 hS3
  have hF3m : MZ 3 (Fp r g y u) := ⟨hF3, (Fp_adm h hu huT).mean⟩
  have e1 : cubicD 1 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) =
      cubicD 1 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) +
        cubicD 1 (-1) r (r * u) (Fp r g y u) (Hf r g y u) := by
    rw [fastQ_eq]
    exact cubicD_add (Or.inl rfl) (Or.inr rfl) r _ hF3m hN hH
  have e2 := cubicD_split_one h hu huT
  simp only [nfQ₁, nfOne]
  rw [e1, e2]
  ring

/-- `nfQ₂` at an `H³` time. -/
theorem nfQ₂_eq (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u)) :
    nfQ₂ r g y u = nfTwo r g y u + cubicD 2 (-1) r (r * u) (Fp r g y u) (Hf r g y u) := by
  obtain ⟨hN, -, hH, -, -⟩ := link_facts h hr hu huT hF3 hS3
  have hF3m : MZ 3 (Fp r g y u) := ⟨hF3, (Fp_adm h hu huT).mean⟩
  have e1 : cubicD 2 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) =
      cubicD 2 (-1) r (r * u) (Fp r g y u) (fastNL r g y u) +
        cubicD 2 (-1) r (r * u) (Fp r g y u) (Hf r g y u) := by
    rw [fastQ_eq]
    exact cubicD_add (Or.inr rfl) (Or.inr rfl) r _ hF3m hN hH
  have e2 := cubicD_split_two h hr hu huT hF3 hS3
  simp only [nfQ₂, nfTwo]
  rw [e1, e2]
  ring

/-- **The filter in the native slot, weight one.** -/
theorem filter_one_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hη : 0 < η) (hK : kN / η ≤ KN) (hq : 2 ^ 14 / η ≤ |r|)
    (hf : hnorm 1 (Hpsi r g y u) ≤ 1 / 2) (hS : Shares KN KP M |r| caps) :
    |cubicD 1 (-1) r (r * u) (Fp r g y u) (Hf r g y u)| ≤ η * fastNorm 2 r g y u ^ 2 := by
  have hF := Fp_adm h hu huT
  obtain ⟨hH, -⟩ := Hf_one h hr hu huT
  have hHr := (Hf_facts h hu huT).1
  have h1 := cubicD_one_le (Or.inr rfl) hr (r * u) hF.mz hF.real (PiF_Fp r g y u) hH hHr
  have hN0 := nearN_nonneg |r|
  have hq0 : 0 < |r| := abs_pos.2 hr
  have hC0 := nearC₀_pos
  have hCL1 := CLow_nonneg 1
  have hCL2 := CLow_nonneg 2
  have hcQ := cQone_nonneg
  have hcI := one_le_cI
  have hcn : nearC₀ * nearN |r| ≤ η := share_one (c₀ := kN) hη hK
    (by unfold kN; nlinarith only [hC0, hCL1, hCL2, hcQ, hcI]) hN0 hS.flr
  have hcf : 2 ^ 14 / |r| ≤ η := by
    rw [div_le_iff₀ hq0]
    rw [div_le_iff₀ hη] at hq
    linarith
  have hH1 : hnorm 1 (Hf r g y u) ≤ 1 / 2 :=
    (hnorm_PiF_le (hnorm_one_Hpsi_le h hr hu huT).1).trans hf
  have h2 : (nearC₀ * nearN |r| + 2 ^ 14 / |r|) * hnorm 1 (Hf r g y u) ≤ η := by
    have h3 : 0 ≤ nearC₀ * nearN |r| + 2 ^ 14 / |r| := by positivity
    have h4 := mul_le_mul_of_nonneg_left hH1 h3
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))

/-- `‖H_{ψ,F}‖₂` at a time of `T2`. -/
theorem T2.filter_size (T : T2 X φ M cy r g y u caps) (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    MZ 2 (Hf r g y u) ∧ hnorm 2 (Hf r g y u) ≤
      2 * Eq₂ φ r * hnorm 3 (Fp r g y u) + Eq₂ φ r * cy + Gq₂ φ r := by
  obtain ⟨i, bd⟩ := hnorm_two_Hpsi_J h T.r_ne hu huT T.hF3 T.hS3
  refine ⟨⟨i.PiF, (Hf_facts h hu huT).2.2⟩, (hnorm_PiF_le i).trans (bd.trans ?_)⟩
  have hE := Eq_nonneg (r := r) h
  have hc0 := hnorm_nonneg 3 (Fp r g y u)
  have hS := T.hc
  have e2 : fastNorm 3 r g y u = hnorm 3 (Fp r g y u) := rfl
  rw [e2] at hS ⊢
  have h1 : hnorm 3 (Fp r g y u) + slowNorm 3 r g y u ≤ 2 * hnorm 3 (Fp r g y u) + cy := by
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hE
  change Eq₂ φ r * (hnorm 3 (Fp r g y u) + slowNorm 3 r g y u) + Gq₂ φ r ≤ _
  nlinarith only [h2]

/-- **The filter in the native slot, weight two, at a time.** -/
theorem T2.filter_le (T : T2 X φ M cy r g y u caps) (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hη : 0 < η) (hν : H2.nM r ≤ η) :
    |cubicD 2 (-1) r (r * u) (Fp r g y u) (Hf r g y u)| ≤
      η * fastNorm 3 r g y u ^ 2 + 1 / η * (H2.nM r * Eq₂ φ r) ^ 2 * cy ^ 2 *
        fastNorm 2 r g y u ^ 2 := by
  have hF := Fp_adm h hu huT
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hF3m : MZ 3 (Fp r g y u) := ⟨T.hF3, hF.mean⟩
  obtain ⟨hm, bρ⟩ := T.filter_size h hu huT
  have h1 := H2.cubicD_two_le T.r_ne (r * u) hF3m hF.real (PiF_Fp r g y u) hm
    (Hf_facts h hu huT).1
  have hν0 := H2.nM_nonneg r
  have hb' : hnorm 2 (Fp r g y u) ≤ cp caps.yF := T.hb.trans (le_cp _)
  have hE := Eq_nonneg (r := r) h
  have t3 : Eq₂ φ r * hnorm 2 (Fp r g y u) ≤ 1 / 64 :=
    (mul_le_mul_of_nonneg_left hb' hE).trans (T.hfl.Eq_y_le T.hX hφ)
  have hb2 : H2.nM r * (2 * Eq₂ φ r) * hnorm 2 (Fp r g y u) ≤ η / 2 := by
    have t4 := mul_le_mul_of_nonneg_left t3 hν0
    nlinarith only [t4, hν, hη]
  have hG : H2.nM r * Gq₂ φ r ≤ η / 4 := by
    have t2 : Gq₂ φ r ≤ 1 / 64 := T.hfl.Gq_le T.hX hφ
    have t3 := mul_le_mul_of_nonneg_left t2 hν0
    nlinarith only [t3, hν, hη]
  exact h1.trans (alg_nf hη hν0 (hnorm_nonneg _ _) T.b_le_c bρ hb2 hG)

/-- The coefficients at weight two, from the shares and the threshold. -/
lemma nu_facts {L PS : ℝ} (hη : 0 < η) (hK : kN / η ≤ KN) (hS : Shares KN KP M |r| caps)
    (hq0 : 0 < |r|) (hL0 : 0 ≤ L) (hM : 0 ≤ lead₂ M caps)
    (q2 : 2 * H2.cFar / η * (lead₂ M caps + 1 + L * cp caps.yF) ≤ |r|)
    (q3 : 4 * H2.cFar / η * ((1 + 20 * L) * Real.sqrt PS) ≤ |r|) :
    nearC₀ * nearN |r| ≤ η / 4 ∧ H2.cFar / |r| ≤ η / 2 ∧
      H2.cFar / |r| * ((1 + 20 * L) * Real.sqrt PS) ≤ η / 4 := by
  have hcF := cFar_pos
  have hy := cp_nonneg caps.yF
  have hC0 := nearC₀_pos
  have hCL1 := CLow_nonneg 1
  have hCL2 := CLow_nonneg 2
  have hcQ := cQone_nonneg
  have hcI := one_le_cI
  have h4 : 4 * nearC₀ * nearN |r| ≤ η := share_one (c₀ := kN) hη hK
    (by unfold kN; nlinarith only [hC0, hCL1, hCL2, hcQ, hcI]) (nearN_nonneg _) hS.flr
  refine ⟨by linarith, ?_, ?_⟩
  · have h1 : 2 * H2.cFar / η ≤ |r| := by
      have h2 : 0 ≤ L * cp caps.yF := mul_nonneg hL0 hy
      have h3 : 2 * H2.cFar / η * 1 ≤ 2 * H2.cFar / η * (lead₂ M caps + 1 + L * cp caps.yF) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    rw [div_le_iff₀ hη] at h1
    rw [div_le_iff₀ hq0]
    linarith
  · have e : 4 * H2.cFar / η * ((1 + 20 * L) * Real.sqrt PS) =
        4 * H2.cFar * ((1 + 20 * L) * Real.sqrt PS) / η := by ring
    rw [e, div_le_iff₀ hη] at q3
    have e2 : H2.cFar / |r| * ((1 + 20 * L) * Real.sqrt PS) =
        H2.cFar * ((1 + 20 * L) * Real.sqrt PS) / |r| := by ring
    rw [e2, div_le_iff₀ hq0]
    linarith

/-- **The filter in the native slot, weight two, on a joint piece.** -/
theorem filter_two_joint (hdom : JDom R₀ X R) (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece Tp (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t)
    (hCS : 0 ≤ CS) (hη : 0 < η) (hKN : kN / η ≤ KN) (hKP : kP / η ≤ KP)
    (hq : qNF₂ η CS cS X R caps ≤ q caps) :
    ∃ g₂ : ℝ, 0 ≤ g₂ ∧
      (∀ᵐ u ∂(volume.restrict (Set.Icc s t)),
        |cubicD 2 (-1) r (r * u) (Fp r g y u) (Hf r g y u)| ≤ η * fastNorm 3 r g y u ^ 2 +
          g₂ * hnorm 3 (corrSlow r g y u) ^ 2 * fastNorm 2 r g y u ^ 2) ∧
      ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ lamI X R caps →
        ∫ u in u₁..u₂, g₂ * hnorm 3 (corrSlow r g y u) ^ 2 ≤ η := by
  have hq1 := hq.trans hp.thr
  have hfl0 : jointSlowFloor X R caps ≤ |r| := (le_max_left _ _).trans hq1
  have ht2 : tNF₂ η CS cS X R caps ≤ |r| := (le_max_right _ _).trans hq1
  obtain ⟨hX, hφ, hFl, -, hr⟩ := floor_setup hdom hfl0
  have hq0 : 0 < |r| := abs_pos.2 hr
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hR0 := hdom.R_pos
  have hKN0 : 0 ≤ KN := (div_pos kN_pos hη).le.trans hKN
  have hKP0 : 0 ≤ KP := (div_pos kP_pos hη).le.trans hKP
  have hS := Shares.of_paid hdom hKN0 hKP0 hCS (abs_nonneg r) hp.nearPaid
  have hEx := Ex_pos cS R
  have hC : 0 ≤ CS * Ex cS R := mul_nonneg hCS hEx.le
  have hM0 : 0 ≤ CS * Ex cS R * R := mul_nonneg hC hR0.le
  set L := fibL R caps with hLd
  have hL0 : 0 ≤ L := fibL_nonneg hR0 caps
  set PS := priceS CS cS X R caps with hPSd
  have hPS : 0 ≤ PS := priceS_nonneg hCS cS X hR0.le caps
  have hrt := Real.sqrt_nonneg PS
  obtain ⟨q1, q2, q3, q4, -⟩ := tNF₂_parts hη hCS hR0 hφ ht2
  obtain ⟨n1, n2, n3⟩ := nu_facts hη hKN hS hq0 hL0 (lead₂_nonneg hM0 caps) q2 q3
  set E := Eq₂ (R - X) r with hEd
  have hE0 : 0 ≤ E := Eq_nonneg (r := r) h
  have hE1 : E ≤ 1 := (hFl.Eq_le hX hφ).trans (by norm_num)
  have hE2 : E * Real.sqrt PS ≤ 1 := by
    have e : E * Real.sqrt PS = 64 * c4 * (R - X) * Real.sqrt PS / |r| := by
      simp only [hEd, Eq₂]
      ring
    rw [e, div_le_one hq0]
    exact q4
  have hν0 := H2.nM_nonneg r
  have hνe : H2.nM r = nearC₀ * nearN |r| + H2.cFar / |r| := rfl
  have hν : H2.nM r ≤ η := by
    rw [hνe]
    linarith
  have hcl : H2.nM r * E * Real.sqrt PS ≤ 2 * η / 4 := by
    have t1 := mul_le_mul_of_nonneg_left hE2 (mul_nonneg nearC₀_pos.le (nearN_nonneg |r|))
    have t2 : (H2.cFar / |r|) * (E * Real.sqrt PS) ≤
        H2.cFar / |r| * ((1 + 20 * L) * Real.sqrt PS) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hrt) ?_
      · linarith
      · have := cFar_pos
        positivity
    rw [hνe]
    nlinarith only [t1, t2, n1, n3]
  have hg4 : 1 / η * (H2.nM r * E) ^ 2 * (4 * PS) ≤ η := by
    have h3 := clip_share (η := 2 * η) (by positivity) hPS (mul_nonneg hν0 hE0) hcl
    have e : 1 / η * (H2.nM r * E) ^ 2 * (4 * PS) =
        2 * (1 / (2 * η) * (H2.nM r * E) ^ 2 * (4 * PS)) := by
      field_simp
    rw [e]
    linarith
  refine ⟨1 / η * (H2.nM r * E) ^ 2, by positivity, ?_, fun u₁ u₂ h1 h12 h2 hlen => ?_⟩
  · filter_upwards [ae_inH3_split h hp.hs hp.hst hp.ht, ae_inH3_corr h hr hp.hs hp.hst hp.ht,
      ae_restrict_mem measurableSet_Icc] with u hu3 hz hu
    have hu0 := hp.hs.trans hu.1
    have huT := lt_lifespan hu.2 hp.ht
    obtain ⟨c1, c2, -, -, -⟩ := hp.onPrefix.1 u hu
    have hcS := slow_three_le h hr hu0 huT hu3.1 hz (c2.trans (le_cp _)) q1
    have T : T2 X (R - X) (CS * Ex cS R * R) (hnorm 3 (corrSlow r g y u)) r g y u caps :=
      ⟨hu3.1, hu3.2, c1, c2, hp.sup u hu, hM0, hnorm_nonneg _ _, hcS, hFl, hX⟩
    exact T.filter_le h hu0 huT hη hν
  · have hclip := slowOut_clip_le hp.slow hC hR1 h1 h12 h2 hlen
    rw [intervalIntegral.integral_const_mul]
    have h3 := mul_le_mul_of_nonneg_left hclip (by positivity : 0 ≤ 1 / η * (H2.nM r * E) ^ 2)
    exact h3.trans hg4

/-- **Weight one, in the form of `joint₁T`.** -/
theorem total_one_fastQ (hdom : JDom R₀ X R) (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece Tp (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP) Sl r g y Ty caps s t)
    (hCS : 0 ≤ CS) (hη : 0 < η) (hη1 : η ≤ 1) (hKN : kN / η ≤ KN) (hKP : kP / η ≤ KP)
    (hq : qTot₁ η X R caps ≤ q caps) :
    ∀ᵐ u ∂(volume.restrict (Set.Icc s t)), |nfQ₁ r g y u| ≤
      5 * η * fastNorm 2 r g y u ^ 2 + η / 2 * fastNorm 2 r g y u := by
  have hA : qNF₁ η X R caps ≤ q caps := (le_max_left _ _).trans hq
  have hA1 := hA.trans hp.thr
  have hfl0 : jointSlowFloor X R caps ≤ |r| := (le_max_left _ _).trans hA1
  have hfar : 2 ^ 14 / η * tNF₁ caps ≤ |r| := (le_max_right _ _).trans hA1
  obtain ⟨hX, -, -, -, hr⟩ := floor_setup hdom hfl0
  have hKN0 : 0 ≤ KN := (div_pos kN_pos hη).le.trans hKN
  have hKP0 : 0 ≤ KP := (div_pos kP_pos hη).le.trans hKP
  have hS := Shares.of_paid hdom hKN0 hKP0 hCS (abs_nonneg r) hp.nearPaid
  have hq14 : 2 ^ 14 / η ≤ |r| := by
    have h1 : 1 ≤ tNF₁ caps := by
      have := mul_nonneg (nbF_nonneg caps) (cp_nonneg caps.yF)
      unfold tNF₁
      linarith
    have h2 : 2 ^ 14 / η * 1 ≤ 2 ^ 14 / η * tNF₁ caps :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have ht := total_one_joint hdom h hp hCS hη hη1 hKN hKP hq
  filter_upwards [ae_inH3_split h hp.hs hp.hst hp.ht, ae_restrict_mem measurableSet_Icc]
    with u hu3 hu
  have hu0 := hp.hs.trans hu.1
  have huT := lt_lifespan hu.2 hp.ht
  have hf := role18 h hX (Q0_of_slow hfl0) hp.hs hp.ht hp.onPrefix hu
  rw [nfQ₁_eq h hr hu0 huT hu3.1 hu3.2]
  refine (abs_add_le _ _).trans ?_
  have t1 := (ht u hu).2
  have t2 := filter_one_le h hr hu0 huT hη hKN hq14 hf hS
  linarith

/-- **Weight two, in the form of `joint₂T`.** -/
theorem total_two_fastQ (hdom : JDom R₀ X R) (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece Tp (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t)
    (hCS : 0 ≤ CS) (hη : 0 < η) (hη1 : η ≤ 1) (hKN : kN / η ≤ KN) (hKP : kP / η ≤ KP)
    (hq : qTot₂ η CS cS X R caps ≤ q caps) :
    ∃ m A B g₃ : ℝ, 0 ≤ m ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ g₃ ∧
      (∀ᵐ u ∂(volume.restrict (Set.Icc s t)), |nfQ₂ r g y u| ≤
        5 * η * fastNorm 3 r g y u ^ 2 +
          (m + g₃ * hnorm 3 (corrSlow r g y u) ^ 2) * fastNorm 2 r g y u ^ 2 +
          (A * hnorm 3 (corrSlow r g y u) ^ 2 + B)) ∧
      ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ lamI X R caps →
        (∫ u in u₁..u₂, (m + g₃ * hnorm 3 (corrSlow r g y u) ^ 2)) ≤ 4 * η ∧
        (∫ u in u₁..u₂, (A * hnorm 3 (corrSlow r g y u) ^ 2 + B)) ≤ η * jointT X R ^ 2 := by
  have hA' : qNF₂ η CS cS X R caps ≤ q caps := (le_max_left _ _).trans hq
  have hfl0 : jointSlowFloor X R caps ≤ |r| := (le_max_left _ _).trans (hA'.trans hp.thr)
  obtain ⟨-, -, -, -, hr⟩ := floor_setup hdom hfl0
  obtain ⟨m, A, B, g₁, hm, hA, hB, hg₁, -, s2, s3⟩ :=
    total_two_joint hdom h hp hCS hη hη1 hKN hKP hq
  obtain ⟨g₂, hg₂, f2, f3⟩ := filter_two_joint hdom h hp hCS hη hKN hKP hA'
  refine ⟨m, A, B, 2 * g₁ + g₂, hm, hA, hB, by positivity, ?_, fun u₁ u₂ h1 h12 h2 hlen => ?_⟩
  · filter_upwards [s2, f2, ae_inH3_split h hp.hs hp.hst hp.ht,
      ae_restrict_mem measurableSet_Icc] with u b1 b2 hu3 hu
    have hu0 := hp.hs.trans hu.1
    have huT := lt_lifespan hu.2 hp.ht
    rw [nfQ₂_eq h hr hu0 huT hu3.1 hu3.2]
    refine (abs_add_le _ _).trans ?_
    nlinarith only [b1, b2]
  · obtain ⟨c1, c2⟩ := s3 u₁ u₂ h1 h12 h2 hlen
    refine ⟨?_, c2⟩
    have hf3 := f3 u₁ u₂ h1 h12 h2 hlen
    have hsub : Set.uIcc u₁ u₂ ⊆ Set.uIcc s t := by
      rw [Set.uIcc_of_le h12, Set.uIcc_of_le hp.hst]
      exact Set.Icc_subset_Icc h1 h2
    have hi : IntervalIntegrable (fun u => hnorm 3 (corrSlow r g y u) ^ 2) volume u₁ u₂ :=
      hp.slow.cy_int.mono_set hsub
    have i1 : IntervalIntegrable (fun u => m + 2 * g₁ * hnorm 3 (corrSlow r g y u) ^ 2) volume
        u₁ u₂ := intervalIntegrable_const.add (hi.const_mul _)
    have e : (∫ u in u₁..u₂, (m + (2 * g₁ + g₂) * hnorm 3 (corrSlow r g y u) ^ 2)) =
        (∫ u in u₁..u₂, (m + 2 * g₁ * hnorm 3 (corrSlow r g y u) ^ 2)) +
          ∫ u in u₁..u₂, g₂ * hnorm 3 (corrSlow r g y u) ^ 2 := by
      rw [← intervalIntegral.integral_add i1 (hi.const_mul _)]
      refine intervalIntegral.integral_congr fun u _ => ?_
      ring
    rw [e]
    linarith

/-- **What is left at weight one**: the resonant slot and the bracket `−½⟨z, T₁ z⟩` of `X₂`, `Z`.
Everything else of `joint1RHS` and of the derivative of `C_{4,1}` is paid. -/
theorem joint1_left (hdom : JDom R₀ X R) (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece 4 (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t)
    (hCS : 0 ≤ CS) (hη : 0 < η) (hη1 : η ≤ 1) (hKN : kN / η ≤ KN) (hKP : kP / η ≤ KP)
    (hq : qTot₁ η X R caps ≤ q caps) {D ζ ϑ : ℝ} (hD : 1 ≤ D)
    (hF1 : force1Q (R - X) D (CS * Ex cS R * R) caps ≤ q caps) (hζ : 0 < ζ) (hϑ : 1 ≤ ϑ)
    (hst : ϑ * staticQ R (CS * Ex cS R * R) caps ≤ q caps) :
    ∀ᵐ u ∂(volume.restrict (Set.Icc s t)),
      joint1RHS r g y u + (-J4 1 r g y u + Rem4 1 r g y u) ≤
        -pair 1 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) +
          1 / 2 * (insT (famX2 1 r) 1 r g y u).re + 1 / 2 * (insT (famZ 1 r) 1 r g y u).re +
          (5 * η * fastNorm 2 r g y u ^ 2 + η / 2 * fastNorm 2 r g y u) +
          (2 * hBd (R - X) r g y u * fastNorm 2 r g y u +
            24 * c4 * cp caps.PF ^ 2 * hBd (R - X) r g y u) +
          (ζ * fastNorm 2 r g y u ^ 2 +
            (Ch0 * kapH0 caps * h0Bd (R - X) r g y u / |r|) ^ 2 / (4 * ζ) *
              fastNorm 1 r g y u ^ 2) +
          16 * c4 / ϑ * fastNorm 2 r g y u ^ 2 := by
  have hfl0 : jointSlowFloor X R caps ≤ |r| :=
    (le_max_left _ _).trans (((le_max_left _ _).trans hq).trans hp.thr)
  obtain ⟨-, -, -, -, hr⟩ := floor_setup hdom hfl0
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  filter_upwards [total_one_fastQ hdom h hp hCS hη hη1 hKN hKP hq,
    joint1_final_le (φ := R - X) h hr hp hD hF1 hζ hR1 hϑ hst] with u h1 h2
  have e := joint1T_C4 r g y u
  have t := (le_abs_self _).trans h1
  linarith

/-- **What is left at weight two**: the resonant slot and the bracket of `X₂`, `Z`. -/
theorem joint2_left (hdom : JDom R₀ X R) (h : ActualSol X (R - X) r g y Ty)
    (hp : JointPiece 4 (CS * Ex cS R * R) q
      (NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP)
      (SlowOut CS (Ex cS R) R Sl) r g y Ty caps s t)
    (hCS : 0 ≤ CS) (hη : 0 < η) (hη1 : η ≤ 1) (hKN : kN / η ≤ KN) (hKP : kP / η ≤ KP)
    (hq : qTot₂ η CS cS X R caps ≤ q caps) {D ζ ϑ : ℝ} (hD : 1 ≤ D)
    (hF2 : force2Q (R - X) D (CS * Ex cS R * R) CS (Ex cS R) R caps ≤ q caps) (hζ : 0 < ζ)
    (hϑ : 1 ≤ ϑ) (hst : ϑ * staticQ R (CS * Ex cS R * R) caps ≤ q caps) :
    ∃ m A B g₃ : ℝ, 0 ≤ m ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ g₃ ∧
      (∀ᵐ u ∂(volume.restrict (Set.Icc s t)),
        joint2RHS r g y u + (-J4 2 r g y u + Rem4 2 r g y u) ≤
          -pair 2 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) +
            1 / 2 * (insT (famX2 2 r) 2 r g y u).re + 1 / 2 * (insT (famZ 2 r) 2 r g y u).re +
            (5 * η * fastNorm 3 r g y u ^ 2 +
              (m + g₃ * hnorm 3 (corrSlow r g y u) ^ 2) * fastNorm 2 r g y u ^ 2 +
              (A * hnorm 3 (corrSlow r g y u) ^ 2 + B)) +
            (1 / 64 * fastNorm 3 r g y u ^ 2 + 16 * GF (R - X) D (CS * Ex cS R * R) r g y caps u) +
            (ζ * fastNorm 3 r g y u ^ 2 +
              (Ch0 * kapH0 caps * h0Bd (R - X) r g y u / |r|) ^ 2 / (4 * ζ) *
                fastNorm 2 r g y u ^ 2) +
            32 * c4 / ϑ * fastNorm 3 r g y u ^ 2) ∧
      ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ lamI X R caps →
        (∫ u in u₁..u₂, (m + g₃ * hnorm 3 (corrSlow r g y u) ^ 2)) ≤ 4 * η ∧
        (∫ u in u₁..u₂, (A * hnorm 3 (corrSlow r g y u) ^ 2 + B)) ≤ η * jointT X R ^ 2 := by
  have hfl0 : jointSlowFloor X R caps ≤ |r| :=
    (le_max_left _ _).trans (((le_max_left _ _).trans hq).trans hp.thr)
  obtain ⟨-, -, -, -, hr⟩ := floor_setup hdom hfl0
  have hR1 : 1 ≤ R := hdom.one_lt_R.le
  have hEx := Ex_pos cS R
  obtain ⟨m, A, B, g₃, hm, hA, hB, hg, s1, s2⟩ := total_two_fastQ hdom h hp hCS hη hη1 hKN hKP hq
  refine ⟨m, A, B, g₃, hm, hA, hB, hg, ?_, s2⟩
  filter_upwards [s1, joint2_final_le (φ := R - X) h hr hp (mul_nonneg hCS hEx.le)
    hdom.R_pos.le hD hF2 hζ hR1 hϑ hst] with u h1 h2
  have e := joint2T_C4 r g y u
  have t := (le_abs_self _).trans h1
  linarith

end OVNS.Quant.NearFar

end
