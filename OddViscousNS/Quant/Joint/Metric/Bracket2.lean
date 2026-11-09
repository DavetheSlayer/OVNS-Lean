import OddViscousNS.Quant.Joint.Metric.Bound2

/-!
# The bracket and the third correction at weight two (node N15)

`bracket_two_le`: at an `H³` time of `F`, `S`, `y_S`, the bracket of `E₂` is
`[Gm + κ_y c_y + highG/q] b_F² + c_F²/32 + ‖H_{ψ,F}‖₁ c_F`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic OVNS.Quant.NearFar
open GN (SupBd)

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ} {caps : Caps}

lemma zOf_one_two (F : Field) : zOf 1 (zOf 2 F) = zOf 3 F := by
  funext k
  simp only [zOf, smul_smul]
  congr 1
  push_cast
  ring

/-- **The bracket of `E₂`**, at an `H³` time. -/
theorem bracket_two_le (h : ActualSol μ φ r g y Ty) (hr1 : 1 ≤ |r|) {M D : ℝ} (hD : 1 ≤ D)
    (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u))
    (hy3 : InH 3 (corrSlow r g y u)) (hR2 : hnorm 2 (slowCorr r g y u) ≤ delta0)
    (hA : hnorm 1 (Sp r g y u) ≤ cp caps.AS) (hB : hnorm 2 (Sp r g y u) ≤ cp caps.BS)
    (hW : wiener (Sp r g y u) ≤ cp caps.WS) (hY : hnorm 2 (Fp r g y u) ≤ cp caps.yF)
    (hM : slowSup r g y u ≤ M) (hWq : wiener (Sp r g y u) ≤ |r|)
    (hs : hnorm 1 (slowNL r g y u) ≤ hSrc φ caps) (hsm : MZ 1 (slowNL r g y u))
    (hq : 2 ^ 11 * c4 * cp caps.yF ≤ |r|) (hKq : Kc caps / |r| ^ 2 ≤ 1 / 2) :
    ‖grp 2 D r g y u‖ + 1 / 2 * ‖hBY (famX2 2 r) 2 r g y u‖ + 1 / 2 * ‖hBY (famZ 2 r) 2 r g y u‖ +
        extQ 2 D r g y u + slotQ 2 D r g y u ≤
      (Gm φ D |r| M caps + kapY |r| caps * hnorm 3 (corrSlow r g y u) +
        highG (Chigh (2 * CLow 1)) D (cp caps.BS) (cp caps.WS) M (hnorm 3 (corrSlow r g y u)) / |r|) *
          fastNorm 2 r g y u ^ 2 +
      1 / 32 * fastNorm 3 r g y u ^ 2 + hnorm 1 (Hf r g y u) * fastNorm 3 r g y u := by
  have hq0 : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hq0
  have hD0 : 0 < D := by linarith
  have hx := actual_adm h hu huT
  have hSA : Adm 2 (Sp r g y u) := hx.PiS
  have hFA : Adm 2 (Fp r g y u) := hx.PiF
  have hS' := Fam.PiS_Sp r g y u
  have hF' := Fam.PiF_Fp r g y u
  have hSup : SupBd (Sp r g y u) M := GN.supBd_slowSup hSA.inH hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hSup 0)
  have hc := c4_pos
  have hC1 := CLow_nonneg 1
  have hBc := cp_nonneg caps.BS
  have hWc := cp_nonneg caps.WS
  have hAc := cp_nonneg caps.AS
  have hYc := cp_nonneg caps.yF
  set S := Sp r g y u with hSd
  set F := Fp r g y u with hFd
  set cy := hnorm 3 (corrSlow r g y u) with hcy
  have hcy0 : 0 ≤ cy := hnorm_nonneg _ _
  have ed : fastNorm 2 r g y u = hnorm 2 F := rfl
  have ec : fastNorm 3 r g y u = hnorm 3 F := rfl
  rw [ed, ec]
  set d := hnorm 2 F with hd
  set c := hnorm 3 F with hc'
  have hd0 : 0 ≤ d := hnorm_nonneg _ _
  have hc0 : 0 ≤ c := hnorm_nonneg _ _
  have hdc : d ≤ c := hnorm_mono (by norm_num) hF3
  have hd2 := sq_nonneg d
  -- the group
  have g1 : ‖grp 2 D r g y u‖ ≤ G₂ r D M S * d ^ 2 :=
    group₂_le hr1 (r * u) hD hSA hS3 hS' hSup hWq hFA hF3 hF'
  have hSl : SlowAt (cp caps.BS) (cp caps.WS) M S (corrSlow r g y u) (slowCorr r g y u) :=
    ⟨hSA, hS', hy3, (slowCorr_adm h hr hu huT).inH, rfl, hR2, hB, hW, hSup⟩
  have tW : tailW D S ≤ 5 / D * cp caps.BS :=
    (tailW_le hD0 hSA.mz hS').trans (mul_le_mul_of_nonneg_left hB (by positivity))
  have tB := hSl.tail_le hD0
  have g2 := tail_part_le (K := 2 * CLow 1) hq0 hD0 (by positivity) hM0 hcy0 hB hW tW tB
  have g3 := X2Lo_le hq0 hD hA hB hW
  have g4 := sepB_le hq0 hD hB hW
  have hlogq : 0 ≤ Real.log |r| := Real.log_nonneg hr1
  have g5 : ZCf r M S ≤ CZh / |r| * (1 + M * (1 + Real.log |r|)) * cp caps.BS := by
    have hZ := CZh_pos
    simp only [ZCf]
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  have g6 : 2 ^ 22 * D / |r| ^ 2 * (hnorm 2 S * Real.sqrt 17 *
      (hnorm 1 S * Real.sqrt (9 + 8 * Real.log (4 * D))) * wiener S) ≤ gHt D |r| caps := by
    have hS0 := hnorm_nonneg 2 S
    have hA0 := hnorm_nonneg 1 S
    have hW0 := wiener_nonneg S
    have hZ4 := Real.sqrt_nonneg (9 + 8 * Real.log (4 * D))
    have h17 := Real.sqrt_nonneg 17
    simp only [gHt, Z4s]
    gcongr
  have hS3' : hnorm 3 S ≤ cy + c / 128 :=
    slow_three_le h hr hu huT hF3 hy3 hY hq
  have hkY : 0 ≤ kapY |r| caps := by
    unfold kapY
    positivity
  have g7 := mul_le_mul_of_nonneg_left hS3' hkY
  -- the derivative in `B`
  have hF2 : InH ((2 : ℕ) : ℝ) F := by simpa using hFA.inH
  have hF33 : InH ((3 : ℕ) : ℝ) F := by simpa using hF3
  obtain ⟨hzs, hzn⟩ := l2_zOf hF2 hFA.mean
  obtain ⟨hz3, hzn3⟩ := l2_zOf hF33 hFA.mean
  have hzn' : l2n (zOf 2 F) = d := by
    simp only [Nat.cast_ofNat] at hzn
    exact hzn
  have hz1 : Summable fun k => ‖zOf 1 (zOf 2 F) k‖ ^ 2 := by
    rw [zOf_one_two]
    exact hz3
  have hzn1 : l2n (zOf 1 (zOf 2 F)) = c := by
    rw [zOf_one_two, hzn3]
    simp only [Nat.cast_ofNat]
    rfl
  have hz' : PiF (zOf 2 F) = zOf 2 F := Fam.PiF_zOf hF'
  obtain ⟨b1, b2⟩ := hBY_two_le hr (r * u) hD0.le hSA hS' hSup hzs hz1 hz'
  rw [hzn', hzn1] at b1 b2
  obtain ⟨hf1, hf2, hf3⟩ := Bslow_facts hSA hS' hSup
  obtain ⟨hl, hl3⟩ := Bslow_l2 hSA hS' hSup
  have hSA1 : hnorm 1 S ≤ cp caps.AS := hA
  have hBmono : hnorm 1 (Bslow S) ≤ 41 * M * cp caps.BS :=
    hf3.trans (mul_le_mul_of_nonneg_left hB (by positivity))
  have hBmono0 : l2n (Bslow S) ≤ 3 * M * cp caps.AS :=
    hl3.trans (mul_le_mul_of_nonneg_left hA (by positivity))
  have hBYc := BY_two_le (caps := caps) (D := D) (M := M) (f₀ := l2n (Bslow S))
    (f₁ := hnorm 1 (Bslow S)) (a := hnorm 1 S) (W := wiener S) (b := hnorm 2 S) (e := d) (c := c)
    hq0 hD0.le hM0 (hnorm_nonneg _ _) (hnorm_nonneg _ _) (wiener_nonneg S) (hnorm_nonneg _ _) hd0 hc0
    hBmono0 hBmono hA hW hB
  have e11 : hnorm (1 + 1) S = hnorm 2 S := by norm_num
  rw [e11] at b2
  have e1 : hBY (famX2 2 r) 2 r g y u = X2Form 1 2 r (r * u) (Bslow S) S (zOf 2 F) (zOf 2 F) +
      X2Form 1 2 r (r * u) S (Bslow S) (zOf 2 F) (zOf 2 F) := by
    simp only [hBY, famX2_form]
    rfl
  have e2 : hBY (famZ 2 r) 2 r g y u = ZForm 1 2 r (r * u) (Bslow S) S (zOf 2 F) (zOf 2 F) +
      ZForm 1 2 r (r * u) S (Bslow S) (zOf 2 F) (zOf 2 F) := by
    simp only [hBY, famZ_form]
    rfl
  have hHi := DSX2_highG_le hr (r * u) hD0 hSl hzs hz' hWc (μ := hiIntMask D) (fun x => le_rfl)
  rw [hzn'] at hHi
  -- the exterior
  obtain ⟨iN, bN⟩ := fastNL_one_Hf (caps := caps) h hr hu huT hW hB hY
  have iN' : InH ((1 : ℕ) : ℝ) (fastNL r g y u) := by simpa using iN
  have hNm : fastNL r g y u 0 = 0 := by simp [fastNL, PiF]
  obtain ⟨hN1, hNn⟩ := l2_zOf iN' hNm
  have hNn' : l2n (zOf 1 (fastNL r g y u)) = hnorm 1 (fastNL r g y u) := by
    simp only [Nat.cast_one] at hNn
    exact hNn
  have hNF : PiF (zOf 1 (fastNL r g y u)) = zOf 1 (fastNL r g y u) :=
    Fam.PiF_zOf (PiF_fastNL u)
  have hext := Q3_ext_half (s := 2) (Or.inr rfl) hr (r * u) D hSA.mz hS' hN1 hNF hzs hz'
  rw [zOf_add_one, hNn', hzn'] at hext
  set H := hnorm 1 (Hf r g y u) with hH
  have hH0 : 0 ≤ H := hnorm_nonneg _ _
  have hK0 : 0 ≤ K3 |r| (wiener S) (hnorm 2 S) := K3_nonneg (wiener_nonneg S) (hnorm_nonneg _ _)
  have hKc : K3 |r| (wiener S) (hnorm 2 S) ≤ Kc caps / |r| ^ 2 := by
    have := clsS_mono (wiener_nonneg S) (hnorm_nonneg 2 S) hW hB
    simp only [K3, Kc]
    have h2 : 0 ≤ 2 ^ 37 / |r| ^ 2 := by positivity
    refine (mul_le_mul_of_nonneg_left this h2).trans (le_of_eq ?_)
    ring
  set Q := Kc caps / |r| ^ 2 with hQ
  have hQ0 : 0 ≤ Q := hK0.trans hKc
  have hXic : 0 ≤ Xic caps := by
    unfold Xic
    positivity
  have hext2 : extQ 2 D r g y u ≤ 2 * Q * Xic caps * d ^ 2 + H * c := by
    have h1 : hnorm 1 (fastNL r g y u) * d ≤ (Xic caps * d + H) * d :=
      mul_le_mul_of_nonneg_right bN hd0
    have h2 : K3 |r| (wiener S) (hnorm 2 S) * (hnorm 1 (fastNL r g y u) * d) ≤
        Q * ((Xic caps * d + H) * d) :=
      mul_le_mul hKc h1 (mul_nonneg (hnorm_nonneg _ _) hd0) hQ0
    have h3 : 2 * Q * H * d ≤ H * c := by
      have h4 : 2 * Q ≤ 1 := by linarith only [hKq]
      have h5 : 2 * Q * d ≤ 1 * c := mul_le_mul h4 hdc hd0 zero_le_one
      have := mul_le_mul_of_nonneg_left h5 hH0
      nlinarith only [this]
    have e0 : extQ 2 D r g y u = ‖(famQ 2 r D).form r (r * u) S S S (zOf 2 (fastNL r g y u))
        (zOf 2 F)‖ + ‖(famQ 2 r D).form r (r * u) S S S (zOf 2 F) (zOf 2 (fastNL r g y u))‖ := rfl
    rw [e0]
    nlinarith only [hext, h2, h3]
  -- the slots
  have hslot : slotQ 2 D r g y u ≤ gSlot φ D |r| caps * d ^ 2 := by
    have hk := Q3_slots_le (s := 2) (D := D) (S := S) (Or.inr rfl) hr (r * u) hD hsm (PiS_slowNL u)
      hSA.mz hS' hzs hz'
    rw [hzn'] at hk
    refine hk.trans ?_
    have h1 : T3 D (hnorm 1 S) (wiener S) ≤ T0 D * (cp caps.WS ^ 2 + cp caps.AS ^ 2) := by
      refine T3_le.trans (mul_le_mul_of_nonneg_left ?_ (T0_nonneg D))
      have h2 := pow_le_pow_left₀ (wiener_nonneg S) hW 2
      have h3 := pow_le_pow_left₀ (hnorm_nonneg 1 S) hA 2
      linarith only [h2, h3]
    have hT30 : 0 ≤ T3 D (hnorm 1 S) (wiener S) := by
      have ha := hnorm_nonneg 1 S
      have hW0 := wiener_nonneg S
      have := Real.log_nonneg hD
      unfold T3
      positivity
    have h2 : hnorm 1 (slowNL r g y u) * T3 D (hnorm 1 S) (wiener S) ≤
        hSrc φ caps * (T0 D * (cp caps.WS ^ 2 + cp caps.AS ^ 2)) :=
      mul_le_mul hs h1 hT30 ((hnorm_nonneg _ _).trans hs)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 ^ 36 / |r| ^ 2 * d ^ 2)
    simp only [gSlot]
    nlinarith only [h3]
  -- Young
  have y1 : kapY |r| caps / 128 * c * d ^ 2 ≤
      1 / 64 * c ^ 2 + 16 * (kapY |r| caps / 128) ^ 2 * cp caps.yF ^ 2 * d ^ 2 := by
    have h1 : 16 * ((kapY |r| caps / 128) * d ^ 2) ^ 2 ≤
        16 * (kapY |r| caps / 128) ^ 2 * cp caps.yF ^ 2 * d ^ 2 := by
      have h2 : d ^ 2 ≤ cp caps.yF ^ 2 := pow_le_pow_left₀ hd0 hY 2
      have h3 := mul_le_mul_of_nonneg_left h2
        (by positivity : 0 ≤ 16 * (kapY |r| caps / 128) ^ 2 * d ^ 2)
      nlinarith only [h3]
    nlinarith only [h1, sq_nonneg (c / 8 - 4 * ((kapY |r| caps / 128) * d ^ 2))]
  have y2 : Om M caps / |r| ^ 2 * (c * d) ≤ 1 / 64 * c ^ 2 + 16 * (Om M caps / |r| ^ 2) ^ 2 * d ^ 2 := by
    nlinarith only [sq_nonneg (c / 8 - 4 * (Om M caps / |r| ^ 2 * d))]
  -- the sum
  rw [e1, e2]
  set X1 := ‖X2Form 1 2 r (r * u) (Bslow S) S (zOf 2 F) (zOf 2 F) +
    X2Form 1 2 r (r * u) S (Bslow S) (zOf 2 F) (zOf 2 F)‖ with hX1
  set Z1 := ‖ZForm 1 2 r (r * u) (Bslow S) S (zOf 2 F) (zOf 2 F) +
    ZForm 1 2 r (r * u) S (Bslow S) (zOf 2 F) (zOf 2 F)‖ with hZ1
  have hG : G₂ r D M S ≤ gLow D |r| M caps + highG (Cm2 * (2 * CLow 1) + 5 * Cm3) D (cp caps.BS)
      (cp caps.WS) M cy / |r| + (kapY |r| caps * (cy + c / 128) + gSep D |r| caps) + gHt D |r| caps := by
    have s1 : (X2Lo r D S S + ZCf r M S) * (2 * CLow 1 * M) ≤ gLow D |r| M caps := by
      simp only [gLow]
      exact mul_le_mul_of_nonneg_right (add_le_add g3 g5) (by positivity)
    simp only [G₂, X2Cf]
    have e3 : (X2Lo r D S S + Cm2 / |r| * (hnorm 2 S * tailB D S) + ZCf r M S) * (2 * CLow 1 * M) =
        (X2Lo r D S S + ZCf r M S) * (2 * CLow 1 * M) +
          Cm2 / |r| * (hnorm 2 S * tailB D S) * (2 * CLow 1 * M) := by ring
    rw [e3]
    linarith only [s1, g2, g4, g7, g6]
  have hG2 := mul_le_mul_of_nonneg_right hG hd2
  have hHi2 : 1 / 2 * ‖DSX2Form (hiIntMask D) 2 r (r * u) (Bslow S) S (zOf 2 F) (zOf 2 F)‖ ≤
      1 / 2 * (highG (82 * Cm2) D (cp caps.BS) (cp caps.WS) M cy / |r| * d ^ 2) :=
    mul_le_mul_of_nonneg_left hHi (by norm_num)
  have hB2 : 1 / 2 * X1 + 1 / 2 * Z1 ≤ gBY D |r| M caps * d ^ 2 + Om M caps / |r| ^ 2 * (c * d) +
      1 / 2 * ‖DSX2Form (hiIntMask D) 2 r (r * u) (Bslow S) S (zOf 2 F) (zOf 2 F)‖ := by
    linarith only [b1, b2, hBYc]
  have ehG : highG (Chigh (2 * CLow 1)) D (cp caps.BS) (cp caps.WS) M cy / |r| =
      highG (Cm2 * (2 * CLow 1) + 5 * Cm3) D (cp caps.BS) (cp caps.WS) M cy / |r| +
        highG (82 * Cm2) D (cp caps.BS) (cp caps.WS) M cy / |r| := by
    simp only [highG, Chigh]
    ring
  have hhG0 : 0 ≤ highG (82 * Cm2) D (cp caps.BS) (cp caps.WS) M cy / |r| := by
    have := Cm2_pos
    have := delta0_pos
    simp only [highG]
    positivity
  have hhG2 : 0 ≤ highG (82 * Cm2) D (cp caps.BS) (cp caps.WS) M cy / |r| * d ^ 2 :=
    mul_nonneg hhG0 hd2
  rw [ehG]
  simp only [Gm]
  set Gh := highG (Cm2 * (2 * CLow 1) + 5 * Cm3) D (cp caps.BS) (cp caps.WS) M cy / |r|
  set Gi := highG (82 * Cm2) D (cp caps.BS) (cp caps.WS) M cy / |r|
  set KY := kapY |r| caps with hKY
  have e4 : (gLow D |r| M caps + Gh + (KY * (cy + c / 128) + gSep D |r| caps) + gHt D |r| caps) * d ^ 2 =
      gLow D |r| M caps * d ^ 2 + Gh * d ^ 2 + KY * cy * d ^ 2 + KY / 128 * c * d ^ 2 +
        gSep D |r| caps * d ^ 2 + gHt D |r| caps * d ^ 2 := by ring
  rw [e4] at hG2
  have e5 : (gLow D |r| M caps + gSep D |r| caps + gHt D |r| caps + gBY D |r| M caps +
      2 * Q * Xic caps + gSlot φ D |r| caps +
      16 * (KY / 128) ^ 2 * cp caps.yF ^ 2 + 16 * (Om M caps / |r| ^ 2) ^ 2 + KY * cy + (Gh + Gi)) * d ^ 2 =
      gLow D |r| M caps * d ^ 2 + gSep D |r| caps * d ^ 2 + gHt D |r| caps * d ^ 2 +
      gBY D |r| M caps * d ^ 2 + 2 * Q * Xic caps * d ^ 2 + gSlot φ D |r| caps * d ^ 2 +
      16 * (KY / 128) ^ 2 * cp caps.yF ^ 2 * d ^ 2 + 16 * (Om M caps / |r| ^ 2) ^ 2 * d ^ 2 +
      KY * cy * d ^ 2 + Gh * d ^ 2 + Gi * d ^ 2 := by ring
  rw [e5]
  have hG3 := g1.trans hG2
  linarith only [hG3, hB2, hHi2, hext2, hslot, y1, y2, hhG2]

end OVNS.Quant.Metric

end
