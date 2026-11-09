import OddViscousNS.Quant.Joint.Metric.Mass1

/-!
# The bracket and the third correction at weight one (node N14)

`bracket_one_le`: at an `H³` time of `y_S`, the bracket of `E₁` is `[κ₁ (W² + a²) + κ₂ c_y² + κ₃] a_F²`,
a small part of `b_F²` and the genuine `2 K₃ ‖H_{ψ,F}‖₁ b_F`.  The exterior direction `N_F` of `O` is taken
in `L²` (`fastNL_l2_le`), so that no `H²` norm of `S` meets a second power of `b_F`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic
open GN (SupBd)

/-- The operator norm of `O` at the caps, without `q`. -/
def Kc (caps : Caps) : ℝ :=
  2 ^ 37 * clsS (cp caps.WS) (cp caps.WS) (cp caps.WS) (cp caps.BS) (cp caps.BS) (cp caps.BS)

lemma Kc_nonneg (caps : Caps) : 0 ≤ Kc caps := by
  have := c4_pos
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.BS
  unfold Kc clsS
  positivity

/-- The `q⁻²` coefficient of `W² + a²`. -/
def B11 (φ D : ℝ) (caps : Caps) : ℝ :=
  B11g D (cp caps.BS) + 2 ^ 40 * (cp caps.WS ^ 2 + 3 * c4 * (cp caps.BS * cp caps.WS)) +
    2 ^ 36 * (hSrc φ caps * T0 D)

/-- The coefficient of the kinetic density. -/
def kap1 (φ R M D q : ℝ) (caps : Caps) : ℝ :=
  A11 R M D (cp caps.BS) / q + B11 φ D caps / q ^ 2 + 2 ^ 10 * c4 ^ 2 * (Kc caps / q ^ 2) ^ 2

/-- The coefficient of `c_y²`. -/
def kap2 (D q : ℝ) (caps : Caps) : ℝ := A12 D (cp caps.BS) / q

/-- The constant of the multiplier. -/
def kap3 (R M D q : ℝ) (caps : Caps) : ℝ :=
  A13 R D (cp caps.BS) / q + B13 M D (cp caps.AS) (cp caps.BS) / q ^ 2 +
    2 ^ 10 * c4 ^ 2 * (Kc caps / q ^ 2) ^ 2 * cp caps.PF ^ 2

/-- The share of `b_F²`. -/
def nu1 (q D M : ℝ) (caps : Caps) : ℝ := X12 q D M (cp caps.AS) (cp caps.BS)

/-- The scalar of the exterior. -/
lemma ext_scalar {K Kq K' W a e d w h P c : ℝ} (hc : 0 ≤ c) (hK0 : 0 ≤ K) (hK : K ≤ Kq)
    (hKW : K * W ≤ K' * W ^ 2) (ha : 0 ≤ a) (he : 0 ≤ e) (hd : 0 ≤ d) (hed : e ≤ d)
    (hw0 : 0 ≤ w) (hw : w ≤ c * d) (hh : 0 ≤ h) (heP : e ≤ P) :
    2 * (K * ((4 * (W * e + a * w) + 4 * (w * e) + h) * e)) ≤
      (8 * K' * W ^ 2 + 2 ^ 10 * c ^ 2 * Kq ^ 2 * a ^ 2 + 2 ^ 10 * c ^ 2 * Kq ^ 2 * P ^ 2) * e ^ 2 +
        1 / 32 * d ^ 2 + 2 * Kq * h * d := by
  have hKq : 0 ≤ Kq := hK0.trans hK
  have hP : 0 ≤ P := he.trans heP
  have s1 : 2 * (K * (4 * (W * e) * e)) ≤ 8 * K' * W ^ 2 * e ^ 2 := by
    have := mul_le_mul_of_nonneg_right hKW (sq_nonneg e)
    nlinarith only [this]
  have s2 : 2 * (K * (4 * (a * w) * e)) ≤ (8 * c * Kq * (a * e)) * d := by
    have h1 : K * w ≤ Kq * (c * d) := mul_le_mul hK hw hw0 hKq
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ a * e)
    nlinarith only [h2]
  have s3 : 2 * (K * (4 * (w * e) * e)) ≤ (8 * c * Kq * (P * e)) * d := by
    have h1 : K * w ≤ Kq * (c * d) := mul_le_mul hK hw hw0 hKq
    have h2 : K * w * e ≤ Kq * (c * d) * P := mul_le_mul h1 heP he (by positivity)
    have h3 := mul_le_mul_of_nonneg_right h2 he
    nlinarith only [h3]
  have s4 : 2 * (K * (h * e)) ≤ 2 * Kq * h * d := by
    have h1 : K * e ≤ Kq * d := mul_le_mul hK hed he hKq
    have h2 := mul_le_mul_of_nonneg_left h1 hh
    nlinarith only [h2]
  have y1 : (8 * c * Kq * (a * e)) * d ≤ 1 / 64 * d ^ 2 + 2 ^ 10 * c ^ 2 * Kq ^ 2 * a ^ 2 * e ^ 2 := by
    nlinarith only [sq_nonneg (d / 8 - 4 * (8 * c * Kq * (a * e)))]
  have y2 : (8 * c * Kq * (P * e)) * d ≤ 1 / 64 * d ^ 2 + 2 ^ 10 * c ^ 2 * Kq ^ 2 * P ^ 2 * e ^ 2 := by
    nlinarith only [sq_nonneg (d / 8 - 4 * (8 * c * Kq * (P * e)))]
  have e0 : 2 * (K * ((4 * (W * e + a * w) + 4 * (w * e) + h) * e)) =
      2 * (K * (4 * (W * e) * e)) + 2 * (K * (4 * (a * w) * e)) + 2 * (K * (4 * (w * e) * e)) +
        2 * (K * (h * e)) := by ring
  rw [e0]
  have e1 : (8 * K' * W ^ 2 + 2 ^ 10 * c ^ 2 * Kq ^ 2 * a ^ 2 + 2 ^ 10 * c ^ 2 * Kq ^ 2 * P ^ 2) * e ^ 2 =
      8 * K' * W ^ 2 * e ^ 2 + 2 ^ 10 * c ^ 2 * Kq ^ 2 * a ^ 2 * e ^ 2 +
        2 ^ 10 * c ^ 2 * Kq ^ 2 * P ^ 2 * e ^ 2 := by ring
  rw [e1]
  linarith only [s1, s2, s3, s4, y1, y2]

/-- `clsS` is monotone. -/
lemma clsS_mono {W W' b b' : ℝ} (hW : 0 ≤ W) (hb : 0 ≤ b) (h1 : W ≤ W') (h2 : b ≤ b') :
    clsS W W W b b b ≤ clsS W' W' W' b' b' b' := by
  have := c4_pos
  have hW' : 0 ≤ W' := hW.trans h1
  have hb' : 0 ≤ b' := hb.trans h2
  unfold clsS
  gcongr

section Path

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ} {caps : Caps}

/-- The size of `K₃ W`. -/
lemma K3_mul_W {W b Wc B q : ℝ} (hW : 0 ≤ W) (hb : 0 ≤ b) (h1 : W ≤ Wc) (h2 : b ≤ B) :
    K3 q W b * W ≤ 2 ^ 37 / q ^ 2 * (Wc ^ 2 + 3 * c4 * (B * Wc)) * W ^ 2 := by
  have hc := c4_pos
  have hq2 : 0 ≤ 2 ^ 37 / q ^ 2 := by positivity
  have hWc : 0 ≤ Wc := hW.trans h1
  have hB : 0 ≤ B := hb.trans h2
  have e1 : K3 q W b * W = 2 ^ 37 / q ^ 2 * ((W ^ 2 + 3 * c4 * (b * W)) * W ^ 2) := by
    simp only [K3, clsS]
    ring
  have e2 : 2 ^ 37 / q ^ 2 * (Wc ^ 2 + 3 * c4 * (B * Wc)) * W ^ 2 =
      2 ^ 37 / q ^ 2 * ((Wc ^ 2 + 3 * c4 * (B * Wc)) * W ^ 2) := by ring
  rw [e1, e2]
  gcongr

/-- **The bracket of `E₁`**, at an `H³` time of `y_S`. -/
theorem bracket_one_le (h : ActualSol μ φ r g y Ty) (hr1 : 1 ≤ |r|) {R M D : ℝ} (hD : 1 ≤ D)
    (hR : 0 < R) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) (hA : hnorm 1 (Sp r g y u) ≤ cp caps.AS)
    (hB : hnorm 2 (Sp r g y u) ≤ cp caps.BS) (hW : wiener (Sp r g y u) ≤ cp caps.WS)
    (hP : hnorm 1 (Fp r g y u) ≤ cp caps.PF) (hM : slowSup r g y u ≤ M)
    (hy3 : InH 3 (corrSlow r g y u)) (hR2 : hnorm 2 (slowCorr r g y u) ≤ delta0)
    (hs : hnorm 1 (slowNL r g y u) ≤ hSrc φ caps) (hsm : MZ 1 (slowNL r g y u)) :
    ‖grp 1 D r g y u‖ + 1 / 2 * ‖hBY (famX2 1 r) 1 r g y u‖ + 1 / 2 * ‖hBY (famZ 1 r) 1 r g y u‖ +
        extQ 1 D r g y u + slotQ 1 D r g y u ≤
      (kap1 φ R M D |r| caps * kinD r g y u + kap2 D |r| caps * hnorm 3 (corrSlow r g y u) ^ 2 +
        kap3 R M D |r| caps) * fastNorm 1 r g y u ^ 2 +
      (nu1 |r| D M caps + 1 / 32) * fastNorm 2 r g y u ^ 2 +
      2 * (Kc caps / |r| ^ 2) * hnorm 1 (Hf r g y u) * fastNorm 2 r g y u := by
  have hq : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hq
  have hD0 : 0 < D := by linarith
  have hx := actual_adm h hu huT
  have hS : Adm 2 (Sp r g y u) := hx.PiS
  have hF : Adm 2 (Fp r g y u) := hx.PiF
  have hS' := Fam.PiS_Sp r g y u
  have hF' := Fam.PiF_Fp r g y u
  have hSup : SupBd (Sp r g y u) M := GN.supBd_slowSup hS.inH hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hSup 0)
  set S := Sp r g y u with hSd
  set F := Fp r g y u with hFd
  set a := hnorm 1 S with ha
  set W := wiener S with hWd
  set b := hnorm 2 S with hb
  set e := hnorm 1 F with he
  set d := hnorm 2 F with hd
  set cy := hnorm 3 (corrSlow r g y u) with hcy
  have ha0 : 0 ≤ a := hnorm_nonneg _ _
  have hW0 : 0 ≤ W := wiener_nonneg S
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  have he0 : 0 ≤ e := hnorm_nonneg _ _
  have hd0 : 0 ≤ d := hnorm_nonneg _ _
  have hcy0 : 0 ≤ cy := hnorm_nonneg _ _
  have hed : e ≤ d := hnorm_mono (by norm_num) hF.inH
  -- the group
  have g1 : ‖grp 1 D r g y u‖ ≤ G₁ r D M S e d := group₁_le hr1 (r * u) hD hS hS' hSup hF hF'
  have g2 : ‖X2Form 1 1 r (r * u) (Bslow S) S (zOf 1 F) (zOf 1 F) +
        X2Form 1 1 r (r * u) S (Bslow S) (zOf 1 F) (zOf 1 F)‖ +
      ‖ZForm 1 1 r (r * u) (Bslow S) S (zOf 1 F) (zOf 1 F) +
        ZForm 1 1 r (r * u) S (Bslow S) (zOf 1 F) (zOf 1 F)‖ ≤ BY1 |r| D M a W b e d :=
    hBY_one_le hr (r * u) hD hS hS' hSup hF hF'
  have e1 : hBY (famX2 1 r) 1 r g y u = X2Form 1 1 r (r * u) (Bslow S) S (zOf 1 F) (zOf 1 F) +
      X2Form 1 1 r (r * u) S (Bslow S) (zOf 1 F) (zOf 1 F) := by
    simp only [hBY, famX2_form]
    rfl
  have e2 : hBY (famZ 1 r) 1 r g y u = ZForm 1 1 r (r * u) (Bslow S) S (zOf 1 F) (zOf 1 F) +
      ZForm 1 1 r (r * u) S (Bslow S) (zOf 1 F) (zOf 1 F) := by
    simp only [hBY, famZ_form]
    rfl
  rw [e1, e2]
  have g3 := G1_BY1_le (r := r) (M := M) (S := S) hq hD hM0 he0 hd0
  -- tails
  have hSl : SlowAt (cp caps.BS) (cp caps.WS) M S (corrSlow r g y u) (slowCorr r g y u) :=
    ⟨hS, hS', hy3, (slowCorr_adm h hr hu huT).inH, rfl, hR2, hB, hW, hSup⟩
  have tW : tailW D S ≤ 5 / D * cp caps.BS :=
    (tailW_le hD0 hS.mz hS').trans (mul_le_mul_of_nonneg_left hB (by positivity))
  have tB := hSl.tail_le hD0
  have hX := X11_le (q := |r|) (D := D) (R := R) (M := M) (a := a) (W := W) (b := b)
    (A := cp caps.AS) (B := cp caps.BS) (cy := cy) hq hD hR hM0 ha0 hW0 hb0 hcy0 hA hB tW tB
    (tailB_nonneg _ _)
  -- the exterior
  have hz1 : InH ((1 : ℕ) : ℝ) F := by simpa using hF.inH.mono (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨hzs, hzn⟩ := l2_zOf hz1 hF.mean
  have hzn' : l2n (zOf 1 F) = e := by simpa using hzn
  have hz' : PiF (zOf 1 F) = zOf 1 F := Fam.PiF_zOf hF'
  obtain ⟨hN, hNb⟩ := fastNL_l2_le h hr hu huT
  have hext := Q3_ext_half (s := 1) (Or.inl rfl) hr (r * u) D hS.mz hS' hN (PiF_fastNL u) hzs hz'
  rw [hzn'] at hext
  set w := wiener F with hwd
  have hw0 : 0 ≤ w := wiener_nonneg F
  have hw : w ≤ c4 * d := wiener_le hF.mz
  set H := hnorm 1 (Hf r g y u) with hH
  have hH0 : 0 ≤ H := hnorm_nonneg _ _
  have hK0 : 0 ≤ K3 |r| W b := K3_nonneg hW0 hb0
  have hKq : K3 |r| W b ≤ Kc caps / |r| ^ 2 := by
    have := clsS_mono hW0 hb0 hW hB
    simp only [K3, Kc]
    have h2 : 0 ≤ 2 ^ 37 / |r| ^ 2 := by positivity
    calc 2 ^ 37 / |r| ^ 2 * clsS W W W b b b ≤ 2 ^ 37 / |r| ^ 2 * clsS (cp caps.WS) (cp caps.WS)
          (cp caps.WS) (cp caps.BS) (cp caps.BS) (cp caps.BS) := mul_le_mul_of_nonneg_left this h2
      _ = _ := by ring
  have hKW := K3_mul_W (q := |r|) hW0 hb0 hW hB
  have hs0 := ext_scalar c4_pos.le hK0 hKq hKW ha0 he0 hd0 hed hw0 hw hH0 hP
  have hext2 : extQ 1 D r g y u ≤ 2 * (K3 |r| W b * ((4 * (W * e + a * w) + 4 * (w * e) + H) * e)) := by
    refine hext.trans ?_
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNb he0) hK0
    linarith
  -- the slots
  have hslot : slotQ 1 D r g y u ≤ 2 ^ 36 / |r| ^ 2 * (e ^ 2 * (hSrc φ caps * T0 D * kinD r g y u)) := by
    have hk := Q3_slots_le (s := 1) (D := D) (S := S) (Or.inl rfl) hr (r * u) hD hsm (PiS_slowNL u)
      hS.mz hS' hzs hz'
    rw [hzn'] at hk
    refine hk.trans ?_
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg e)) (by positivity)
    have h1 : T3 D a W ≤ T0 D * kinD r g y u := T3_le
    have h2 := mul_le_mul hs h1 (by
      unfold T3
      have hc := c4_pos
      positivity) ((hnorm_nonneg _ _).trans hs)
    refine h2.trans (le_of_eq ?_)
    ring
  -- sum
  have hWK : W ^ 2 ≤ kinD r g y u := by
    have : kinD r g y u = W ^ 2 + a ^ 2 := rfl
    linarith only [this, sq_nonneg a]
  have haK : a ^ 2 ≤ kinD r g y u := by
    have : kinD r g y u = W ^ 2 + a ^ 2 := rfl
    linarith only [this, sq_nonneg W]
  have hK00 := kinD_nonneg r g y u
  have hν : X12 |r| D M a b ≤ nu1 |r| D M caps := by
    simp only [X12, nu1]
    have h1 : a ^ 2 ≤ cp caps.AS ^ 2 := pow_le_pow_left₀ ha0 hA 2
    have h2 : a * b ≤ cp caps.AS * cp caps.BS := mul_le_mul hA hB hb0 (cp_nonneg _)
    have hcL := cL_nonneg
    gcongr
  have hd2 := sq_nonneg d
  have he2 := sq_nonneg e
  set Q := Kc caps / |r| ^ 2 with hQ
  have e3 : kinD r g y u = W ^ 2 + a ^ 2 := rfl
  have hfin : (A11 R M D (cp caps.BS) / |r| + B11g D (cp caps.BS) / |r| ^ 2) * (W ^ 2 + a ^ 2) +
      A12 D (cp caps.BS) / |r| * cy ^ 2 +
      (A13 R D (cp caps.BS) / |r| + B13 M D (cp caps.AS) (cp caps.BS) / |r| ^ 2) +
      (8 * (2 ^ 37 / |r| ^ 2 * (cp caps.WS ^ 2 + 3 * c4 * (cp caps.BS * cp caps.WS))) * W ^ 2 +
        2 ^ 10 * c4 ^ 2 * Q ^ 2 * a ^ 2 + 2 ^ 10 * c4 ^ 2 * Q ^ 2 * cp caps.PF ^ 2) +
      2 ^ 36 / |r| ^ 2 * (hSrc φ caps * T0 D) * kinD r g y u ≤
      kap1 φ R M D |r| caps * kinD r g y u + kap2 D |r| caps * cy ^ 2 + kap3 R M D |r| caps := by
    have c1 : 8 * (2 ^ 37 / |r| ^ 2 * (cp caps.WS ^ 2 + 3 * c4 * (cp caps.BS * cp caps.WS))) * W ^ 2 ≤
        8 * (2 ^ 37 / |r| ^ 2 * (cp caps.WS ^ 2 + 3 * c4 * (cp caps.BS * cp caps.WS))) *
          kinD r g y u := by
      have := cp_nonneg caps.WS
      have := cp_nonneg caps.BS
      have := c4_pos
      exact mul_le_mul_of_nonneg_left hWK (by positivity)
    have c2 : 2 ^ 10 * c4 ^ 2 * Q ^ 2 * a ^ 2 ≤ 2 ^ 10 * c4 ^ 2 * Q ^ 2 * kinD r g y u :=
      mul_le_mul_of_nonneg_left haK (by positivity)
    simp only [kap1, kap2, kap3, B11, ← hQ]
    rw [← e3]
    have e4 : (A11 R M D (cp caps.BS) / |r| + (B11g D (cp caps.BS) +
        2 ^ 40 * (cp caps.WS ^ 2 + 3 * c4 * (cp caps.BS * cp caps.WS)) +
        2 ^ 36 * (hSrc φ caps * T0 D)) / |r| ^ 2 + 2 ^ 10 * c4 ^ 2 * Q ^ 2) * kinD r g y u =
        (A11 R M D (cp caps.BS) / |r| + B11g D (cp caps.BS) / |r| ^ 2) * kinD r g y u +
        8 * (2 ^ 37 / |r| ^ 2 * (cp caps.WS ^ 2 + 3 * c4 * (cp caps.BS * cp caps.WS))) *
          kinD r g y u + 2 ^ 36 / |r| ^ 2 * (hSrc φ caps * T0 D) * kinD r g y u +
        2 ^ 10 * c4 ^ 2 * Q ^ 2 * kinD r g y u := by
      ring
    rw [e4]
    linarith only [c1, c2]
  have hfin2 := mul_le_mul_of_nonneg_right hfin he2
  have hX2 := mul_le_mul_of_nonneg_right hX he2
  have hX3 : X11 |r| D M a W b (tailW D S) (tailB D S) * e ^ 2 ≤
      ((A11 R M D (cp caps.BS) / |r| + B11g D (cp caps.BS) / |r| ^ 2) * (W ^ 2 + a ^ 2) +
      A12 D (cp caps.BS) / |r| * cy ^ 2 +
      (A13 R D (cp caps.BS) / |r| + B13 M D (cp caps.AS) (cp caps.BS) / |r| ^ 2)) * e ^ 2 := hX2
  have hν2 := mul_le_mul_of_nonneg_right hν hd2
  have e5 : 2 ^ 36 / |r| ^ 2 * (e ^ 2 * (hSrc φ caps * T0 D * kinD r g y u)) =
      2 ^ 36 / |r| ^ 2 * (hSrc φ caps * T0 D) * kinD r g y u * e ^ 2 := by ring
  rw [e5] at hslot
  have hext3 := hext2.trans hs0
  have hZ : (nu1 |r| D M caps + 1 / 32) * d ^ 2 = nu1 |r| D M caps * d ^ 2 + 1 / 32 * d ^ 2 := by ring
  have ef1 : fastNorm 1 r g y u = e := rfl
  have ef2 : fastNorm 2 r g y u = d := rfl
  rw [ef1, ef2, hZ]
  nlinarith only [g1, g2, g3, hX3, hfin2, hν2, hext3, hslot]

end Path

end OVNS.Quant.Metric

end
