import OddViscousNS.Quant.Joint.Quartic.Path

/-!
# The identity of `Q₄`, `Q₄,₁` along the actual solution (step J5, node N11)

`Q4_identity_two`, `Q4_identity_one`: at weights two and one, the increment of `Q₄` is the integral of
the source plus the four insertions, and the integrand is in `L¹`.

Weight two (Body 34, "at actual `H³` times"): `N_F, N_S ∈ H²` at the `H³` times, linearly in `‖·‖₃`
(`NL_two`), so the integrand is dominated by `C (2 + c_F² + c_S²)`.
Weight one (Body 35, "no `H³` source or actual `c_y` integral is required"): all the terms are bounded,
on `H¹` directions, with the weighted fibre at `ε = 1/2` on the inner direction.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (slow_c3_integrable fast_h2_law ae_inH3_split)

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

lemma PiF_Fp (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : PiF (Fp r g y u) = Fp r g y u :=
  PiF_PiF_eq _

lemma slots_val (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    Slots (Sp r g y u) (Fp r g y u) (Fp r g y u) (Fp r g y u) :=
  ⟨Fam.PiS_Sp r g y u, PiF_Fp r g y u, PiF_Fp r g y u, PiF_Fp r g y u⟩

lemma slots_S (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    Slots (slowNL r g y u) (Fp r g y u) (Fp r g y u) (Fp r g y u) :=
  ⟨PiS_slowNL u, PiF_Fp r g y u, PiF_Fp r g y u, PiF_Fp r g y u⟩

lemma slots_W (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    Slots (Sp r g y u) (fastNL r g y u) (Fp r g y u) (Fp r g y u) :=
  ⟨Fam.PiS_Sp r g y u, PiF_fastNL u, PiF_Fp r g y u, PiF_Fp r g y u⟩

lemma slots_U (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    Slots (Sp r g y u) (Fp r g y u) (fastNL r g y u) (Fp r g y u) :=
  ⟨Fam.PiS_Sp r g y u, PiF_Fp r g y u, PiF_fastNL u, PiF_Fp r g y u⟩

lemma slots_V (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    Slots (Sp r g y u) (Fp r g y u) (Fp r g y u) (fastNL r g y u) :=
  ⟨Fam.PiS_Sp r g y u, PiF_Fp r g y u, PiF_Fp r g y u, PiF_fastNL u⟩

/-- The nonlinearities in `H²`, at the `H³` times, linearly in `‖·‖₃`. -/
lemma NL_two (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : ENNReal.ofReal b < Ty) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ u ∈ Icc 0 b, InH 3 (Fp r g y u) → InH 3 (Sp r g y u) →
      InH 2 (fastNL r g y u) ∧ InH 2 (slowNL r g y u) ∧
      hnorm 2 (fastNL r g y u) ≤ N * (1 + hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) ∧
      hnorm 2 (slowNL r g y u) ≤ N * (1 + hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_actual_bound h hr hb
  have hc := c4_pos
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  set Z : ℝ := 4 * φ with hZ
  have hZ0 : 0 ≤ Z := by positivity
  set A : ℝ := 16 * c4 * (M₁ + Z) * (1 + Z) with hA
  have hA0 : 0 ≤ A := by positivity
  have hg0 := hnorm_nonneg 2 g
  refine ⟨A + hnorm 2 g, by positivity, fun u hu hF3 hS3 => ?_⟩
  have hu0 := hu.1
  have huT := lt_lifespan hu.2 hb
  have hx := actual_adm h hu0 huT
  have hy := h.sol.adm u hu0 huT
  obtain ⟨hψ3, hψ3le⟩ := H2.psi_three_le h hu0
  have hψ2 : hnorm 2 (psi r 0 g u) ≤ hnorm 3 (psi r 0 g u) := hnorm_mono (by norm_num) hψ3
  have hxSF := PiS_add_PiF (actual r g y u)
  have hx3I : InH 3 (actual r g y u) := by
    rw [← hxSF]
    exact hS3.add hF3
  have ey : y u = actual r g y u + psi r 0 g u := by simp [actual]
  have hy3I : InH 3 (y u) := by
    rw [ey]
    exact hx3I.add hψ3
  have hy3 : MZ 3 (y u) := ⟨hy3I, hy.mean⟩
  obtain ⟨iQ, bQ⟩ := H2.Qm_two_le (phaseM_bdd (r * u)) hy3 hy3
  have hX0 : 0 ≤ hnorm 3 (Fp r g y u) := hnorm_nonneg _ _
  have hX1 : 0 ≤ hnorm 3 (Sp r g y u) := hnorm_nonneg _ _
  have hy2 : hnorm 2 (y u) ≤ M₁ + Z := by
    rw [ey]
    refine (hnorm_add_le hx.inH (hψ3.mono (by norm_num))).trans (add_le_add (hM₁ u hu) ?_)
    linarith
  have hy3n : hnorm 3 (y u) ≤ hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u) + Z := by
    rw [ey]
    refine (hnorm_add_le hx3I hψ3).trans (add_le_add ?_ hψ3le)
    conv_lhs => rw [← hxSF]
    refine (hnorm_add_le hS3 hF3).trans (le_of_eq ?_)
    simp only [Sp, Fp]
    ring
  have hw : wiener (y u) ≤ c4 * (M₁ + Z) :=
    (wiener_le (hy3.mono' (by norm_num))).trans (mul_le_mul_of_nonneg_left hy2 hc.le)
  have hW0 := wiener_nonneg (y u)
  have hQb : hnorm 2 (Qm (phaseM (r * u)) (y u) (y u)) ≤ A * (1 + hnorm 3 (Fp r g y u) +
      hnorm 3 (Sp r g y u)) := by
    refine bQ.trans ?_
    set X := hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u) with hX
    have hX2 : 0 ≤ X := by positivity
    have h1 : wiener (y u) * hnorm 3 (y u) ≤ c4 * (M₁ + Z) * (X + Z) :=
      mul_le_mul hw hy3n (hnorm_nonneg _ _) (by positivity)
    have h2 : X + Z ≤ (1 + Z) * (1 + X) := by nlinarith only [hZ0, hX2, mul_nonneg hZ0 hX2]
    have h3 : c4 * (M₁ + Z) * (X + Z) ≤ c4 * (M₁ + Z) * ((1 + Z) * (1 + X)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e1 : A * (1 + hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) =
        16 * (c4 * (M₁ + Z) * ((1 + Z) * (1 + X))) := by
      simp only [hA, hX]
      ring
    rw [e1]
    nlinarith only [h1, h3]
  have eF : fastNL r g y u = -PiF (Qm (phaseM (r * u)) (y u) (y u)) := rfl
  have eS : slowNL r g y u = -PiS (Qm (phaseM (r * u)) (y u) (y u)) + PiS g := rfl
  have hg2 : InH 2 (PiS g) := h.force_adm.inH.PiS
  have hI1 : InH 2 (fastNL r g y u) := by
    rw [eF]
    exact iQ.PiF.neg
  have hI2 : InH 2 (slowNL r g y u) := by
    rw [eS]
    exact iQ.PiS.neg.add hg2
  have hXn : 0 ≤ 1 + hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u) := by positivity
  refine ⟨hI1, hI2, ?_, ?_⟩
  · rw [eF, hnorm_neg]
    refine (hnorm_PiF_le iQ).trans (hQb.trans ?_)
    exact mul_le_mul_of_nonneg_right (by linarith) hXn
  · rw [eS]
    refine (hnorm_add_le iQ.PiS.neg hg2).trans ?_
    rw [hnorm_neg]
    have h1 := hnorm_PiS_le iQ
    have h2 := hnorm_PiS_le h.force_adm.inH
    have h3 : hnorm 2 g * 1 ≤ hnorm 2 g * (1 + hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) :=
      mul_le_mul_of_nonneg_left (by linarith) hg0
    calc _ ≤ A * (1 + hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) + hnorm 2 g := by linarith
      _ ≤ _ := by
          rw [add_mul]
          linarith

/-- Four numbers below `M`. -/
lemma prod4_le {a b c d M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h1 : a ≤ M)
    (h2 : b ≤ M) (h3 : c ≤ M) (h4 : d ≤ M) : a * b * c * d ≤ M ^ 4 := by
  have hM := ha.trans h1
  calc a * b * c * d ≤ M * M * M * M := by gcongr
    _ = M ^ 4 := by ring

/-- `√𝔐_P ≤ 11`. -/
lemma sqrt_MomP_le (q : ℝ) : Real.sqrt (MomP q) ≤ 11 := by
  rw [Real.sqrt_le_left (by norm_num)]
  exact (MomP_le_const q).trans (by norm_num)

/-- **The identity at weight two**: Body 34. -/
theorem Q4_identity_two (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (fun u => src4 2 r g y u + rem4 2 r g y u) volume a b ∧
      val4 2 r g y b - val4 2 r g y a = ∫ u in a..b, (src4 2 r g y u + rem4 2 r g y u) := by
  have hq : 0 < |r| := abs_pos.2 hr
  obtain ⟨M, hM0, hM⟩ := Fam.path_sup h hr ha hb
  obtain ⟨N, hN0, hN⟩ := NL_two h hr hb
  set Cn : ℝ := 3 * Real.sqrt (MomP |r|) with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  set K : ℝ := 2 ^ 14 * (1 + 1 / |r|) * Cn * Real.sqrt 17 with hK
  have hK0 : 0 ≤ K := by positivity
  set E : ℝ := (1 + M) ^ 3 * (1 + N) with hE
  have hE0 : 0 ≤ E := by positivity
  set gf : ℝ → ℝ := fun u => 8 * K * E *
    (2 + (hnorm 3 (Fp r g y u) ^ 2 + hnorm 3 (Sp r g y u) ^ 2)) with hgf
  have hgi : IntervalIntegrable gf volume a b :=
    (intervalIntegrable_const.add ((fast_h2_law h ha hab hb).1.add
      (slow_c3_integrable h ha hab hb))).const_mul (8 * K * E)
  have hgood : ∀ᵐ u ∂(volume.restrict (Icc a b)), InH 3 (Fp r g y u) ∧ InH 3 (Sp r g y u) :=
    ae_inH3_split h ha hab hb
  have hend : ∀ c ∈ Icc a b, Summable fun x : L4 => termQ 2 r x (r * c) (Sp r g y c x.2.2)
      (Fp r g y c (inL x)) (Fp r g y c x.2.1) (Fp r g y c (outE x)) := fun c hc => by
    obtain ⟨hS2, hF2, -⟩ := hM c hc
    have hL := lhB_two hF2.inH (PiF_Fp r g y c)
    exact (Q2_sb hr (slots_val r g y c) hS2.inH hL hF2.inH hF2.inH _).1.of_norm
  refine identity_of_dom h 2 ha hab hb hgi ?_ hend
  filter_upwards [hgood, ae_restrict_mem measurableSet_Icc] with u hu3 hu
  obtain ⟨hS2, hF2, -, -, -, -, -, -, -⟩ := hM u hu
  obtain ⟨hSn, hFn, -⟩ := (hM u hu).2.2
  have hu' : u ∈ Icc 0 b := ⟨ha.trans hu.1, hu.2⟩
  obtain ⟨iF, iS, bF, bS⟩ := hN u hu' hu3.1 hu3.2
  have hF3 : MZ 3 (Fp r g y u) := ⟨hu3.1, hF2.mean⟩
  have hS3 : MZ 3 (Sp r g y u) := ⟨hu3.2, hS2.mean⟩
  have hLF := lhB_two hF2.inH (PiF_Fp r g y u)
  have hLN := lhB_two iF (PiF_fastNL u)
  set X := 1 + hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u) with hX
  have hX1 : 1 ≤ X := by
    have := hnorm_nonneg 3 (Fp r g y u)
    have := hnorm_nonneg 3 (Sp r g y u)
    linarith
  have s0 := J2_sb r (slots_val r g y u) hS3 hLF hF2.inH hF2.inH (r * u)
  have s1 := Q2_sb hr (slots_S r g y u) iS hLF hF2.inH hF2.inH (r * u)
  have s2 := Q2_sb hr (slots_W r g y u) hS2.inH hLN hF2.inH hF2.inH (r * u)
  have s3 := Q2_sb hr (slots_U r g y u) hS2.inH hLF iF hF2.inH (r * u)
  have s4 := Q2_sb hr (slots_V r g y u) hS2.inH hLF hF2.inH iF (r * u)
  refine ⟨_, _, _, _, _, s0, s1, s2, s3, s4, ?_⟩
  set Sn := hnorm 2 (Sp r g y u) with hSnd
  set Fn := hnorm 2 (Fp r g y u) with hFnd
  have hS0 : 0 ≤ Sn := hnorm_nonneg _ _
  have hF0 : 0 ≤ Fn := hnorm_nonneg _ _
  set n1 := hnorm 2 (fastNL r g y u) with hn1
  set n2 := hnorm 2 (slowNL r g y u) with hn2
  have hn10 : 0 ≤ n1 := hnorm_nonneg _ _
  have hn20 : 0 ≤ n2 := hnorm_nonneg _ _
  have hc3 : hnorm 3 (Sp r g y u) ≤ X := by
    have := hnorm_nonneg 3 (Fp r g y u)
    linarith
  have hc30 := hnorm_nonneg 3 (Sp r g y u)
  set c3 := hnorm 3 (Sp r g y u) with hc3d
  set s17 := Real.sqrt 17 with hs17
  have hs170 : 0 ≤ s17 := Real.sqrt_nonneg _
  set W : ℝ := 1 + M with hW
  have hW1 : 1 ≤ W := by linarith
  have hSW : Sn ≤ W := by linarith
  have hFW : Fn ≤ W := by linarith
  have hn1' : n1 ≤ (1 + N) * X := bF.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have hn2' : n2 ≤ (1 + N) * X := bS.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have hc3' : c3 ≤ (1 + N) * X := hc3.trans (by nlinarith only [hX1, hN0])
  set Z := (1 + N) * X with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hP3 : Sn * Fn * Fn ≤ W ^ 3 := by
    calc Sn * Fn * Fn ≤ W * W * W := by gcongr
      _ = W ^ 3 := by ring
  have hP4 : Fn * Fn * Fn ≤ W ^ 3 := by
    calc Fn * Fn * Fn ≤ W * W * W := by gcongr
      _ = W ^ 3 := by ring
  have hW30 : 0 ≤ W ^ 3 := by positivity
  have t0 : 2 ^ 14 * (Cn * (c3 * (s17 * Fn) * Fn * Fn)) ≤ K * (W ^ 3 * Z) := by
    have h1 : c3 * (Fn * Fn * Fn) ≤ Z * W ^ 3 := mul_le_mul hc3' hP4 (by positivity) hZ0
    have h2 : 2 ^ 14 * Cn * s17 ≤ K := by
      simp only [hK]
      have : 0 ≤ 2 ^ 14 * Cn * s17 * (1 / |r|) := by positivity
      nlinarith only [this]
    have h3 : 2 ^ 14 * (Cn * (c3 * (s17 * Fn) * Fn * Fn)) = 2 ^ 14 * Cn * s17 * (c3 * (Fn * Fn * Fn)) := by
      ring
    rw [h3]
    calc _ ≤ K * (Z * W ^ 3) := mul_le_mul h2 h1 (by positivity) hK0
      _ = _ := by ring
  have hK1 : 2 ^ 14 / |r| * Cn * s17 ≤ K := by
    simp only [hK]
    have : 0 ≤ 2 ^ 14 * Cn * s17 := by positivity
    have e : 2 ^ 14 * (1 + 1 / |r|) * Cn * s17 = 2 ^ 14 / |r| * Cn * s17 + 2 ^ 14 * Cn * s17 := by
      ring
    rw [e]
    linarith
  have t1 : 2 ^ 14 / |r| * (3 * (Real.sqrt (MomP |r|) * (n2 * (s17 * Fn) * Fn * Fn))) ≤
      K * (W ^ 3 * Z) := by
    have h1 : n2 * (Fn * Fn * Fn) ≤ Z * W ^ 3 := mul_le_mul hn2' hP4 (by positivity) hZ0
    have h3 : 2 ^ 14 / |r| * (3 * (Real.sqrt (MomP |r|) * (n2 * (s17 * Fn) * Fn * Fn))) =
        2 ^ 14 / |r| * Cn * s17 * (n2 * (Fn * Fn * Fn)) := by
      simp only [hCn]
      ring
    rw [h3]
    calc _ ≤ K * (Z * W ^ 3) := mul_le_mul hK1 h1 (by positivity) hK0
      _ = _ := by ring
  have t2 : 2 ^ 14 / |r| * (3 * (Real.sqrt (MomP |r|) * (Sn * (s17 * n1) * Fn * Fn))) ≤
      K * (W ^ 3 * Z) := by
    have h1 : n1 * (Sn * Fn * Fn) ≤ Z * W ^ 3 := mul_le_mul hn1' hP3 (by positivity) hZ0
    have h3 : 2 ^ 14 / |r| * (3 * (Real.sqrt (MomP |r|) * (Sn * (s17 * n1) * Fn * Fn))) =
        2 ^ 14 / |r| * Cn * s17 * (n1 * (Sn * Fn * Fn)) := by
      simp only [hCn]
      ring
    rw [h3]
    calc _ ≤ K * (Z * W ^ 3) := mul_le_mul hK1 h1 (by positivity) hK0
      _ = _ := by ring
  have t3 : 2 ^ 14 / |r| * (3 * (Real.sqrt (MomP |r|) * (Sn * (s17 * Fn) * n1 * Fn))) ≤
      K * (W ^ 3 * Z) := by
    have h1 : n1 * (Sn * Fn * Fn) ≤ Z * W ^ 3 := mul_le_mul hn1' hP3 (by positivity) hZ0
    have h3 : 2 ^ 14 / |r| * (3 * (Real.sqrt (MomP |r|) * (Sn * (s17 * Fn) * n1 * Fn))) =
        2 ^ 14 / |r| * Cn * s17 * (n1 * (Sn * Fn * Fn)) := by
      simp only [hCn]
      ring
    rw [h3]
    calc _ ≤ K * (Z * W ^ 3) := mul_le_mul hK1 h1 (by positivity) hK0
      _ = _ := by ring
  have t4 : 2 ^ 14 / |r| * (3 * (Real.sqrt (MomP |r|) * (Sn * (s17 * Fn) * Fn * n1))) ≤
      K * (W ^ 3 * Z) := by
    have h1 : n1 * (Sn * Fn * Fn) ≤ Z * W ^ 3 := mul_le_mul hn1' hP3 (by positivity) hZ0
    have h3 : 2 ^ 14 / |r| * (3 * (Real.sqrt (MomP |r|) * (Sn * (s17 * Fn) * Fn * n1))) =
        2 ^ 14 / |r| * Cn * s17 * (n1 * (Sn * Fn * Fn)) := by
      simp only [hCn]
      ring
    rw [h3]
    calc _ ≤ K * (Z * W ^ 3) := mul_le_mul hK1 h1 (by positivity) hK0
      _ = _ := by ring
  have hsum : K * (W ^ 3 * Z) * 5 ≤ gf u := by
    simp only [hgf, hE, hZ, hX, hW]
    set c1 := hnorm 3 (Fp r g y u)
    have h1 : 1 + c1 + c3 ≤ 2 + (c1 ^ 2 + c3 ^ 2) := by
      nlinarith only [sq_nonneg (c1 - 1), sq_nonneg (c3 - 1)]
    have h2 : 0 ≤ K * ((1 + M) ^ 3 * (1 + N)) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    have h4 : 0 ≤ K * ((1 + M) ^ 3 * (1 + N)) * (2 + (c1 ^ 2 + c3 ^ 2)) := by positivity
    nlinarith only [h3, h4]
  linarith

/-- **The identity at weight one**: Body 35.  No `H³` time is used. -/
theorem Q4_identity_one (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (fun u => src4 1 r g y u + rem4 1 r g y u) volume a b ∧
      val4 1 r g y b - val4 1 r g y a = ∫ u in a..b, (src4 1 r g y u + rem4 1 r g y u) := by
  have hq : 0 < |r| := abs_pos.2 hr
  obtain ⟨M, hM0, hM⟩ := Fam.path_sup h hr ha hb
  set ε : ℝ := 1 / 2 with hε
  have hε0 : 0 < ε := by norm_num [hε]
  have hε1 : ε ≤ 1 := by norm_num [hε]
  set c : ℝ := |r| ^ (1 - ε) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hq _
  set Cn : ℝ := 3 * Real.sqrt (MomP |r|) with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  set A₁ : ℝ := 1 + Real.sqrt 17 + Real.sqrt (9 + 4 / ε) with hA₁
  have hA₁1 : 1 ≤ A₁ := by
    have := Real.sqrt_nonneg 17
    have := Real.sqrt_nonneg (9 + 4 / ε)
    linarith
  set Ŵ : ℝ := A₁ * (1 + M) with hŴ
  have hŴ0 : 0 ≤ Ŵ := by positivity
  have hŴ1 : 1 + M ≤ Ŵ := le_mul_of_one_le_left (by positivity) hA₁1
  set K : ℝ := 2 ^ 13 * (1 + 1 / c) * (2 * Cn) * Ŵ ^ 4 with hK
  have hK0 : 0 ≤ K := by positivity
  have hgi : IntervalIntegrable (fun _ : ℝ => 5 * K) volume a b := intervalIntegrable_const
  have hend : ∀ d ∈ Icc a b, Summable fun x : L4 => termQ 1 r x (r * d) (Sp r g y d x.2.2)
      (Fp r g y d (inL x)) (Fp r g y d x.2.1) (Fp r g y d (outE x)) := fun d hd => by
    obtain ⟨hS2, hF2, -⟩ := hM d hd
    have hL := lhB_two hF2.inH (PiF_Fp r g y d)
    exact (Q1_static_sb hr (slots_val r g y d) (hS2.inH.mono (by norm_num)) hL
      (hF2.inH.mono (by norm_num)) (hF2.inH.mono (by norm_num)) _).1.of_norm
  refine identity_of_dom h 1 ha hab hb hgi ?_ hend
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  obtain ⟨hS2, hF2, hSn, hFn, hN1, hNs1, hNn, hNsn, -⟩ := hM u hu
  have hLF := lhB_two hF2.inH (PiF_Fp r g y u)
  have hF1 : InH 1 (Fp r g y u) := hF2.inH.mono (by norm_num)
  have hS1 : InH 1 (Sp r g y u) := hS2.inH.mono (by norm_num)
  have hLe := lhB_eps hε0 hF1 (PiF_Fp r g y u)
  have hLN := lhB_eps hε0 hN1 (PiF_fastNL u)
  have s0 := J1_sb r (slots_val r g y u) hS2.inH hLF hF2.inH hF2.inH (r * u)
  have s1 := Q1_in_sb hr hε0.le hε1 (slots_S r g y u) hNs1 hLe hF2.inH hF2.inH (r * u)
  have s2 := Q1_in_sb hr hε0.le hε1 (slots_W r g y u) hS1 hLN hF2.inH hF2.inH (r * u)
  have s3 := Q1_q_sb hr hε0.le hε1 (slots_U r g y u) hS2.inH hLF hN1 hF2.inH (r * u)
  have s4 := Q1_e_sb hr hε0.le hε1 (slots_V r g y u) hS2.inH hLF hF2.inH hN1 (r * u)
  refine ⟨_, _, _, _, _, s0, s1, s2, s3, s4, ?_⟩
  have le_W : ∀ {t : ℝ}, t ≤ M → t ≤ Ŵ := fun ht => by linarith
  have h1S : hnorm 1 (Sp r g y u) ≤ Ŵ :=
    le_W ((hnorm_mono (by norm_num) hS2.inH).trans hSn)
  have h1F : hnorm 1 (Fp r g y u) ≤ Ŵ :=
    le_W ((hnorm_mono (by norm_num) hF2.inH).trans hFn)
  have h2S := le_W hSn
  have h2F := le_W hFn
  have hN1W := le_W hNn
  have hNsW := le_W hNsn
  have hs17 : Real.sqrt 17 ≤ A₁ := by
    have := Real.sqrt_nonneg (9 + 4 / ε)
    simp only [hA₁]
    linarith
  have hse : Real.sqrt (9 + 4 / ε) ≤ A₁ := by
    have := Real.sqrt_nonneg 17
    simp only [hA₁]
    linarith
  have hM1 : ∀ t B : ℝ, 0 ≤ t → t ≤ M → 0 ≤ B → B ≤ A₁ → B * t ≤ Ŵ :=
    fun t B h0 ht hB0 hB => by
      have : B * t ≤ A₁ * (1 + M) := mul_le_mul hB (by linarith) h0 (by linarith)
      exact this
  have hL0 := hM1 _ _ (hnorm_nonneg _ _) hFn (Real.sqrt_nonneg _) hs17
  have hL1 := hM1 _ _ (hnorm_nonneg 1 _) ((hnorm_mono (s := 1) (by norm_num) hF2.inH).trans hFn)
    (Real.sqrt_nonneg _) hse
  have hL2 := hM1 _ _ (hnorm_nonneg _ _) hNn (Real.sqrt_nonneg _) hse
  set L := Real.sqrt 17 * hnorm 2 (Fp r g y u)
  set L' := Real.sqrt (9 + 4 / ε) * hnorm 1 (Fp r g y u)
  set L'' := Real.sqrt (9 + 4 / ε) * hnorm 1 (fastNL r g y u)
  have hL00 : 0 ≤ L := mul_nonneg (Real.sqrt_nonneg _) (hnorm_nonneg _ _)
  have hL10 : 0 ≤ L' := mul_nonneg (Real.sqrt_nonneg _) (hnorm_nonneg _ _)
  have hL20 : 0 ≤ L'' := mul_nonneg (Real.sqrt_nonneg _) (hnorm_nonneg _ _)
  have nn : ∀ s f, 0 ≤ hnorm s f := fun s f => hnorm_nonneg s f
  have p := fun {x₁ x₂ x₃ x₄ : ℝ} (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂) (h₃ : 0 ≤ x₃) (h₄ : 0 ≤ x₄)
    (b₁ : x₁ ≤ Ŵ) (b₂ : x₂ ≤ Ŵ) (b₃ : x₃ ≤ Ŵ) (b₄ : x₄ ≤ Ŵ) => prod4_le h₁ h₂ h₃ h₄ b₁ b₂ b₃ b₄
  have scale : ∀ {x x' : ℝ}, x ≤ Ŵ ^ 4 → x' ≤ Ŵ ^ 4 → 0 ≤ x → 0 ≤ x' →
      2 ^ 13 / c * (3 * (Real.sqrt (MomP |r|) * x) + 3 * (Real.sqrt (MomP |r|) * x')) ≤ K := by
    intro x x' h h' h0 h0'
    have e : 2 ^ 13 / c * (3 * (Real.sqrt (MomP |r|) * x) + 3 * (Real.sqrt (MomP |r|) * x')) =
        2 ^ 13 / c * Cn * (x + x') := by
      simp only [hCn]
      ring
    rw [e]
    have h1 : 2 ^ 13 / c * Cn * (x + x') ≤ 2 ^ 13 / c * Cn * (2 * Ŵ ^ 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    refine h1.trans ?_
    simp only [hK]
    have h2 : 0 ≤ 2 ^ 13 * (2 * Cn) * Ŵ ^ 4 := by positivity
    have e2 : 2 ^ 13 * (1 + 1 / c) * (2 * Cn) * Ŵ ^ 4 =
        2 ^ 13 * (2 * Cn) * Ŵ ^ 4 + 2 ^ 13 / c * Cn * (2 * Ŵ ^ 4) := by ring
    rw [e2]
    linarith
  have t0 : 2 ^ 13 * (3 * (Real.sqrt (MomP |r|) * (hnorm 2 (Sp r g y u) * L *
      hnorm 2 (Fp r g y u) * hnorm 1 (Fp r g y u))) + 3 * (Real.sqrt (MomP |r|) *
      (hnorm 2 (Sp r g y u) * L * hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)))) ≤ K := by
    have h1 := p (nn _ _) hL00 (nn _ _) (nn _ _) h2S hL0 h2F h1F
    have h2 := p (nn _ _) hL00 (nn _ _) (nn _ _) h2S hL0 h1F h2F
    have e : 2 ^ 13 * (3 * (Real.sqrt (MomP |r|) * (hnorm 2 (Sp r g y u) * L *
        hnorm 2 (Fp r g y u) * hnorm 1 (Fp r g y u))) + 3 * (Real.sqrt (MomP |r|) *
        (hnorm 2 (Sp r g y u) * L * hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)))) =
        2 ^ 13 * Cn * ((hnorm 2 (Sp r g y u) * L * hnorm 2 (Fp r g y u) * hnorm 1 (Fp r g y u)) +
        (hnorm 2 (Sp r g y u) * L * hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u))) := by
      simp only [hCn]
      ring
    rw [e]
    have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : 0 ≤ 2 ^ 13 * Cn)
    refine h3.trans ?_
    simp only [hK]
    have h4 : 0 ≤ 2 ^ 13 / c * (2 * Cn) * Ŵ ^ 4 := by positivity
    have e2 : 2 ^ 13 * (1 + 1 / c) * (2 * Cn) * Ŵ ^ 4 =
        2 ^ 13 * Cn * (Ŵ ^ 4 + Ŵ ^ 4) + 2 ^ 13 / c * (2 * Cn) * Ŵ ^ 4 := by ring
    rw [e2]
    linarith
  have pp : ∀ {x₁ x₂ x₃ x₄ : ℝ}, 0 ≤ x₁ → 0 ≤ x₂ → 0 ≤ x₃ → 0 ≤ x₄ → 0 ≤ x₁ * x₂ * x₃ * x₄ :=
    fun h₁ h₂ h₃ h₄ => mul_nonneg (mul_nonneg (mul_nonneg h₁ h₂) h₃) h₄
  have t1 := scale (p (nn _ _) hL10 (nn _ _) (nn _ _) hNsW hL1 h2F h1F)
    (p (nn _ _) hL10 (nn _ _) (nn _ _) hNsW hL1 h1F h2F)
    (pp (nn _ _) hL10 (nn _ _) (nn _ _)) (pp (nn _ _) hL10 (nn _ _) (nn _ _))
  have t2 := scale (p (nn _ _) hL20 (nn _ _) (nn _ _) h1S hL2 h2F h1F)
    (p (nn _ _) hL20 (nn _ _) (nn _ _) h1S hL2 h1F h2F)
    (pp (nn _ _) hL20 (nn _ _) (nn _ _)) (pp (nn _ _) hL20 (nn _ _) (nn _ _))
  have t3 := scale (p (nn _ _) hL00 (nn _ _) (nn _ _) h2S hL0 hN1W h1F)
    (p (nn _ _) hL00 (nn _ _) (nn _ _) h1S hL0 hN1W h2F)
    (pp (nn _ _) hL00 (nn _ _) (nn _ _)) (pp (nn _ _) hL00 (nn _ _) (nn _ _))
  have t4 := scale (p (nn _ _) hL00 (nn _ _) (nn _ _) h2S hL0 h1F hN1W)
    (p (nn _ _) hL00 (nn _ _) (nn _ _) h1S hL0 h2F hN1W)
    (pp (nn _ _) hL00 (nn _ _) (nn _ _)) (pp (nn _ _) hL00 (nn _ _) (nn _ _))
  simp only [← hc]
  linarith

end OVNS.Quant.Quartic

end
