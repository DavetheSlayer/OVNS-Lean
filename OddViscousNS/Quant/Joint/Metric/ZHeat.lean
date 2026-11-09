import OddViscousNS.Quant.Joint.Metric.ZOp

/-!
# `Z` on the heat flow (step J5, nodes N4, N5)

* `h_one_le`, `h_two_le`: the merged field `h_u = B(S_u, S_u)`;
* `ZForm_le`: `‖Z‖ ≤ C q⁻¹ M b` (Body 30);
* `ZForm_half_le`: `‖A^{1/2} Z‖ ≲ W b √u₀ + q⁻¹ M b (1 + ln(1/u₀))` (Body 40).
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (Qm_two_le)

noncomputable section

namespace OVNS.Quant.Metric

variable {r : ℝ} {s : ℕ} {h G F : Field}

/-! ### The merged field along the heat flow -/

open GN (SupBd)

variable {S : Field} {M u : ℝ}

/-- `‖h_u‖₁ ≤ 41 M e^{−u} b` (Body 30). -/
lemma h_one_le (hu : 0 ≤ u) (hS : Adm 2 S) (hS' : PiS S = S) (hM : SupBd S M) :
    MZ 1 (Bslow (heatF u S)) ∧ PiS (Bslow (heatF u S)) = Bslow (heatF u S) ∧
      hnorm 1 (Bslow (heatF u S)) ≤ 41 * M * (Real.exp (-u) * hnorm 2 S) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hs := supBd_heatF (summable_wiener hS.inH) hM hu
  obtain ⟨h1, h2, h3⟩ := Bslow_facts (adm_heat hu hS) (PiS_heatF hS') hs
  refine ⟨h1, h2, h3.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (hnorm_two_heat_le hu hS.mz).2 (by positivity)

lemma sqrt_div_le (hu : 0 < u) : Real.sqrt (Real.exp (-u) / u) ≤ (Real.sqrt u)⁻¹ := by
  have h1 : Real.exp (-u) / u ≤ 1 / u :=
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by linarith)) hu.le
  refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one, one_div]

/-- `‖h_u‖₂ ≤ 16 W u^{−1/2} b`: the Wiener bound (no tame estimate). -/
lemma h_two_le (hu : 0 < u) (hS : Adm 2 S) :
    MZ 2 (Bslow (heatF u S)) ∧
      hnorm 2 (Bslow (heatF u S)) ≤ 16 * wiener S * ((Real.sqrt u)⁻¹ * hnorm 2 S) := by
  obtain ⟨h31, h32⟩ := hnorm_three_heat_le hu hS.mz
  have hS3 : MZ 3 (heatF u S) := ⟨h31, heatF_zero_mode hS.mean⟩
  have hB := mz_Bslow hS3
  refine ⟨hB, ?_⟩
  obtain ⟨hQ, hQle⟩ := Qm_two_le resM_bdd hS3 hS3
  have hw := (wiener_heat_le hu.le (summable_wiener hS.inH)).2
  have hb := hnorm_nonneg 2 S
  have h3 := h32.trans (mul_le_mul_of_nonneg_right (sqrt_div_le hu) hb)
  have hn := hnorm_nonneg 3 (heatF u S)
  have hW := wiener_nonneg (heatF u S)
  have e : hnorm 2 (Bslow (heatF u S)) ≤ hnorm 2 (Qres (heatF u S) (heatF u S)) :=
    hnorm_PiS_le hQ
  refine e.trans (hQle.trans ?_)
  have h4 : wiener (heatF u S) * hnorm 3 (heatF u S) ≤
      wiener S * ((Real.sqrt u)⁻¹ * hnorm 2 S) := mul_le_mul hw h3 hn (hW.trans hw)
  have h5 : hnorm 3 (heatF u S) * wiener (heatF u S) ≤
      wiener S * ((Real.sqrt u)⁻¹ * hnorm 2 S) := by rw [mul_comm]; exact h4
  linarith

/-- The heat form of `Z` is `X₁(h_u)`, at a positive time. -/
lemma src_heat_eq (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (hu : 0 < u) (τ : ℝ) (hS : Adm 2 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hG0 : G 0 = 0)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) (hGl : ∀ k, leray k (G k) = G k)
    (hFl : ∀ k, leray k (F k) = F k) :
    (famZ s r).src τ (heatF u S) (heatF u S) (heatF u G) (heatF u F) =
      X1Form s r τ (Bslow (heatF u S)) (heatF u G) (heatF u F) := by
  have hS3 : MZ 3 (heatF u S) := ⟨(hnorm_three_heat_le hu hS.mz).1, heatF_zero_mode hS.mean⟩
  have hG1 : InH 1 (heatF u G) := by
    have h := (l2n_half_heat_le hu hG hG0).1
    refine h.congr fun k => ?_
    rw [sobWeight_one]
    simp only [zOf, norm_smul, Complex.norm_real, pow_one, Real.norm_of_nonneg (absk_nonneg k),
      mul_pow, absk_sq]
  exact src_Z_eq₂ hs hr τ hS3 (PiS_heatF hS') (l2n_heat_le hu.le hG hG0).1 hG1
    (l2n_heat_le hu.le hF (fast_zero hF' (by rfl))).1 (PiF_heatF hF')
    (fun k => leray_heatF (hGl k)) (fun k => leray_heatF (hFl k))

/-- The energy coordinate commutes with the heat flow. -/
lemma heatF_zOf (u : ℝ) (m : ℕ) (G : Field) : heatF u (zOf m G) = zOf m (heatF u G) := by
  funext k
  simp only [heatF, zOf]
  rw [smul_comm]

lemma zOf_zOf_one (G : Field) : zOf 1 (zOf 1 G) = zOf 2 G := by
  funext k
  simp only [zOf, smul_smul, ← Complex.ofReal_mul]
  congr 2
  ring

lemma rpow_half (hu : 0 < u) : u ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt u)⁻¹ := by
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg hu.le, Real.sqrt_eq_rpow]

/-- The constant of the static bound. -/
def CZ : ℝ := 44 * (Ce * (41 * (2 * Real.sqrt Real.pi)))

/-- **The static bound of `Z`** (Body 30): `‖Z‖ ≤ C q⁻¹ M b`, on two fast fields. -/
theorem ZForm_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hS : Adm 2 S) (hS' : PiS S = S)
    (hM : SupBd S M) (hG : Summable fun k => ‖G k‖ ^ 2) (hG' : PiF G = G)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) (hGl : ∀ k, leray k (G k) = G k)
    (hFl : ∀ k, leray k (F k) = F k) :
    ‖ZForm 1 s r τ S S G F‖ ≤ CZ / |r| * M * hnorm 2 S * (l2n G * l2n F) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hb := hnorm_nonneg 2 S
  have hCe := Ce_pos
  have hG0 : G 0 = 0 := fast_zero hG' rfl
  have hF0 : F 0 = 0 := fast_zero hF' rfl
  have hl1 := l2n_nonneg G
  have hl2 := l2n_nonneg F
  set K := 44 / |r| * (Ce * (41 * M * hnorm 2 S) * (2 * (l2n G * l2n F))) with hK
  have hK0 : 0 ≤ K := by positivity
  have hbd : ∀ u ∈ Ioi (0 : ℝ), ‖(famZ s r).src (τ + r * u) (heatF u S) (heatF u S) (heatF u G)
      (heatF u F)‖ ≤ K * (Real.exp (-u) * u ^ ((1 / 2 : ℝ) - 1)) := fun u hu => by
    have hu0 : 0 < u := hu
    have he := Real.exp_pos (-u)
    have he1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hq := (Real.sqrt_pos.2 hu0)
    rw [src_heat_eq hs hr hu0 _ hS hS' hG hG0 hF hF' hGl hFl, rpow_half hu0]
    obtain ⟨h1, h2, h3⟩ := h_one_le hu0.le hS hS' hM
    obtain ⟨g1, g2⟩ := l2n_heat_le hu0.le hG hG0
    obtain ⟨f1, f2⟩ := l2n_heat_le hu0.le hF hF0
    obtain ⟨g3, g4⟩ := l2n_half_heat_le hu0 hG hG0
    obtain ⟨f3, f4⟩ := l2n_half_heat_le hu0 hF hF0
    have hm := X1Form_mixed_le hs hr (τ + r * u) h1 h2 g1 g3 (PiF_heatF hG') f1 f3 (PiF_heatF hF')
    set q := (Real.sqrt u)⁻¹ with hq'
    have hq0 : 0 ≤ q := by positivity
    have hs1 := sqrt_div_le hu0
    have g5 : l2n (zOf 1 (heatF u G)) ≤ q * l2n G :=
      g4.trans (mul_le_mul_of_nonneg_right hs1 hl1)
    have f5 : l2n (zOf 1 (heatF u F)) ≤ q * l2n F :=
      f4.trans (mul_le_mul_of_nonneg_right hs1 hl2)
    have g6 : l2n (heatF u G) ≤ l2n G := g2.trans (mul_le_of_le_one_left hl1 he1)
    have f6 : l2n (heatF u F) ≤ l2n F := f2.trans (mul_le_of_le_one_left hl2 he1)
    have n1 := l2n_nonneg (heatF u G)
    have n2 := l2n_nonneg (heatF u F)
    have n3 := l2n_nonneg (zOf 1 (heatF u G))
    have n4 := l2n_nonneg (zOf 1 (heatF u F))
    have hsum : l2n (zOf 1 (heatF u G)) * l2n (heatF u F) +
        l2n (heatF u G) * l2n (zOf 1 (heatF u F)) ≤ 2 * (l2n G * l2n F) * q := by
      have a1 := mul_le_mul g5 f6 n2 (by positivity)
      have a2 := mul_le_mul g6 f5 n4 hl1
      nlinarith only [a1, a2]
    have hsum0 : 0 ≤ l2n (zOf 1 (heatF u G)) * l2n (heatF u F) +
        l2n (heatF u G) * l2n (zOf 1 (heatF u F)) := by positivity
    have hh1 : Ce * hnorm 1 (Bslow (heatF u S)) ≤ Ce * (41 * M * hnorm 2 S) * Real.exp (-u) := by
      calc _ ≤ Ce * (41 * M * (Real.exp (-u) * hnorm 2 S)) :=
            mul_le_mul_of_nonneg_left h3 hCe.le
        _ = _ := by ring
    have hn0 := hnorm_nonneg 1 (Bslow (heatF u S))
    refine hm.trans ?_
    refine (mul_le_mul_of_nonneg_left (mul_le_mul hh1 hsum hsum0 (by positivity))
      (by positivity)).trans (le_of_eq ?_)
    simp only [hK]
    ring
  have hg : IntegrableOn (fun u : ℝ => K * (Real.exp (-u) * u ^ ((1 / 2 : ℝ) - 1))) (Ioi 0) :=
    (Real.GammaIntegral_convergent (by norm_num)).const_mul K
  have hmain := norm_integral_le_of_norm_le hg
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hbd))
  rw [← famZ_form, Fam.form_heat (famZ_bd hs hr) hS.mz hS' hS.mz hS' hG hF hF' τ, norm_neg]
  refine hmain.trans ?_
  rw [integral_const_mul, ← Real.Gamma_eq_integral (by norm_num), Real.Gamma_one_half_eq]
  apply le_of_eq
  simp only [hK, CZ]
  ring

/-! ### The output half -/

/-- The majorant of the log split. -/
def maj3 (u₀ A B : ℝ) (u : ℝ) : ℝ :=
  (Ioc 0 u₀).indicator (fun u => A * (Real.sqrt u)⁻¹) u +
    (Ioc u₀ 1).indicator (fun u => B * u⁻¹) u + (Ioi 1).indicator (fun u => B * Real.exp (-u)) u

/-- The integrals of the three pieces. -/
lemma maj3_integral {u₀ A B : ℝ} (hu₀ : 0 < u₀) (hu₁ : u₀ ≤ 1) (hB : 0 ≤ B) :
    IntegrableOn (maj3 u₀ A B) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), maj3 u₀ A B u ≤ 2 * A * Real.sqrt u₀ + B * (1 + Real.log (1 / u₀)) := by
  have i0 : IntervalIntegrable (fun u : ℝ => (u) ^ (-(1 / 2 : ℝ))) volume 0 u₀ :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have e0 : ∀ u ∈ Ioc 0 u₀, u ^ (-(1 / 2 : ℝ)) = (Real.sqrt u)⁻¹ := fun u hu => by
    rw [Real.rpow_neg hu.1.le, Real.sqrt_eq_rpow]
  have i1 : IntegrableOn (fun u : ℝ => (Real.sqrt u)⁻¹) (Ioc 0 u₀) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le hu₀.le).1 i0
    exact this.congr_fun e0 measurableSet_Ioc
  have v0 : ∫ u in Ioc 0 u₀, (Real.sqrt u)⁻¹ = 2 * Real.sqrt u₀ := by
    rw [← setIntegral_congr_fun measurableSet_Ioc e0, ← intervalIntegral.integral_of_le hu₀.le,
      integral_rpow (Or.inl (by norm_num))]
    have e : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by norm_num
    rw [e, Real.zero_rpow (by norm_num), ← Real.sqrt_eq_rpow]
    ring
  have i2 : IntegrableOn (fun u : ℝ => u⁻¹) (Ioc u₀ 1) := by
    have : IntervalIntegrable (fun u : ℝ => u⁻¹) volume u₀ 1 :=
      intervalIntegral.intervalIntegrable_inv (fun x hx => by
        have := hx.1
        rw [min_eq_left hu₁] at this
        exact (hu₀.trans_le this).ne') continuousOn_id
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hu₁).1 this
  have v2 : ∫ u in Ioc u₀ 1, u⁻¹ = Real.log (1 / u₀) := by
    rw [← intervalIntegral.integral_of_le hu₁, integral_inv_of_pos hu₀ one_pos]
  have i3 := integrableOn_exp_neg_Ioi 1
  have v3 := integral_exp_neg_Ioi 1
  have m1 : MeasurableSet (Ioc (0 : ℝ) u₀) := measurableSet_Ioc
  have m2 : MeasurableSet (Ioc u₀ (1 : ℝ)) := measurableSet_Ioc
  have m3 : MeasurableSet (Ioi (1 : ℝ)) := measurableSet_Ioi
  have I1 : IntegrableOn ((Ioc 0 u₀).indicator fun u => A * (Real.sqrt u)⁻¹) (Ioi 0) :=
    ((integrable_indicator_iff m1).2 (i1.const_mul A)).integrableOn
  have I2 : IntegrableOn ((Ioc u₀ 1).indicator fun u => B * u⁻¹) (Ioi 0) :=
    ((integrable_indicator_iff m2).2 (i2.const_mul B)).integrableOn
  have I3 : IntegrableOn ((Ioi 1).indicator fun u => B * Real.exp (-u)) (Ioi 0) :=
    ((integrable_indicator_iff m3).2 (i3.const_mul B)).integrableOn
  have I12 : IntegrableOn (fun u => (Ioc 0 u₀).indicator (fun u => A * (Real.sqrt u)⁻¹) u +
      (Ioc u₀ 1).indicator (fun u => B * u⁻¹) u) (Ioi 0) := I1.add I2
  have hI : IntegrableOn (maj3 u₀ A B) (Ioi 0) := I12.add I3
  refine ⟨hI, ?_⟩
  have e : ∫ u in Ioi (0 : ℝ), maj3 u₀ A B u =
      (∫ u in Ioi (0 : ℝ), (Ioc 0 u₀).indicator (fun u => A * (Real.sqrt u)⁻¹) u) +
      (∫ u in Ioi (0 : ℝ), (Ioc u₀ 1).indicator (fun u => B * u⁻¹) u) +
      ∫ u in Ioi (0 : ℝ), (Ioi 1).indicator (fun u => B * Real.exp (-u)) u := by
    unfold maj3
    rw [integral_add I12 I3, integral_add I1 I2]
  have sub1 : Ioc 0 u₀ ⊆ Ioi (0 : ℝ) := fun u hu => hu.1
  have sub2 : Ioc u₀ 1 ⊆ Ioi (0 : ℝ) := fun u hu => hu₀.trans hu.1
  have sub3 : Ioi 1 ⊆ Ioi (0 : ℝ) := fun u (hu : 1 < u) => show (0 : ℝ) < u from one_pos.trans hu
  rw [e, setIntegral_indicator m1, setIntegral_indicator m2, setIntegral_indicator m3,
    inter_eq_right.2 sub1, inter_eq_right.2 sub2, inter_eq_right.2 sub3, integral_const_mul,
    integral_const_mul, integral_const_mul, v0, v2, v3]
  have h1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have h2 := mul_le_mul_of_nonneg_left h1 hB
  nlinarith only [h2]

/-- The bound of the output half on the short range. -/
lemma half_short (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (hu : 0 < u) (τ : ℝ) (hS : Adm 2 S)
    (hS' : PiS S = S) (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2)
    (hG' : PiF G = G) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F)
    (hGl : ∀ k, leray k (G k) = G k) (hFl : ∀ k, leray k (F k) = F k) :
    ‖(famZ s r).src τ (heatF u S) (heatF u S) (heatF u (zOf 1 G)) (heatF u F)‖ ≤
      12800 * c4 * wiener S * hnorm 2 S * (l2n G * l2n F) * (Real.sqrt u)⁻¹ := by
  have hG0 : G 0 = 0 := fast_zero hG' rfl
  have hF0 : F 0 = 0 := fast_zero hF' rfl
  have hGz0 : zOf 1 G 0 = 0 := by simp [zOf, hG0]
  have hGzl : ∀ k, leray k (zOf 1 G k) = zOf 1 G k := fun k => by
    simp only [zOf]
    rw [leray_smul, hGl]
  rw [src_heat_eq hs hr hu τ hS hS' hG1 hGz0 hF hF' hGzl hFl, heatF_zOf]
  obtain ⟨h1, h2⟩ := h_two_le hu hS
  obtain ⟨g1, g2⟩ := l2n_heat_le hu.le hG hG0
  obtain ⟨f1, f2⟩ := l2n_heat_le hu.le hF hF0
  have hf := X1Form_free_le hs r (τ) h1 g1 (PiF_heatF hG') f1 (PiF_heatF hF')
  have hw := wiener_le h1
  have hc := c4_pos
  have hb0 := hnorm_nonneg 2 (Bslow (heatF u S))
  have he1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hl1 := l2n_nonneg G
  have hl2 := l2n_nonneg F
  have n1 := l2n_nonneg (heatF u G)
  have n2 := l2n_nonneg (heatF u F)
  have g6 : l2n (heatF u G) ≤ l2n G := g2.trans (mul_le_of_le_one_left hl1 he1)
  have f6 : l2n (heatF u F) ≤ l2n F := f2.trans (mul_le_of_le_one_left hl2 he1)
  have hp : l2n (heatF u G) * l2n (heatF u F) ≤ l2n G * l2n F := mul_le_mul g6 f6 n2 hl1
  have hW : 9 * wiener (Bslow (heatF u S)) + 16 * c4 * hnorm 2 (Bslow (heatF u S)) ≤
      25 * c4 * hnorm 2 (Bslow (heatF u S)) := by nlinarith only [hw]
  have hW2 : 25 * c4 * hnorm 2 (Bslow (heatF u S)) ≤
      25 * c4 * (16 * wiener S * ((Real.sqrt u)⁻¹ * hnorm 2 S)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hW0 := wiener_nonneg (Bslow (heatF u S))
  have hW1 := wiener_nonneg S
  have hb1 := hnorm_nonneg 2 S
  refine hf.trans ?_
  calc _ ≤ 32 * (25 * c4 * (16 * wiener S * ((Real.sqrt u)⁻¹ * hnorm 2 S)) * (l2n G * l2n F)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (hW.trans hW2) hp (by positivity)
          (by positivity)) (by norm_num)
    _ = _ := by ring

/-- The bound of the output half on the long range. -/
lemma half_long (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (hu : 0 < u) (τ : ℝ) (hS : Adm 2 S)
    (hS' : PiS S = S) (hM : SupBd S M) (hG : Summable fun k => ‖G k‖ ^ 2)
    (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2) (hG' : PiF G = G)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F)
    (hGl : ∀ k, leray k (G k) = G k) (hFl : ∀ k, leray k (F k) = F k) :
    ‖(famZ s r).src τ (heatF u S) (heatF u S) (heatF u (zOf 1 G)) (heatF u F)‖ ≤
      44 * (Ce * (41 * 3)) / |r| * M * hnorm 2 S * (l2n G * l2n F) * (Real.exp (-u) * u⁻¹) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hG0 : G 0 = 0 := fast_zero hG' rfl
  have hF0 : F 0 = 0 := fast_zero hF' rfl
  have hGz0 : zOf 1 G 0 = 0 := by simp [zOf, hG0]
  have hGzl : ∀ k, leray k (zOf 1 G k) = zOf 1 G k := fun k => by
    simp only [zOf]
    rw [leray_smul, hGl]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hb := hnorm_nonneg 2 S
  rw [src_heat_eq hs hr hu τ hS hS' hG1 hGz0 hF hF' hGzl hFl, heatF_zOf]
  obtain ⟨h1, h2, h3⟩ := h_one_le hu.le hS hS' hM
  obtain ⟨g1, g2⟩ := l2n_half_heat_le hu hG hG0
  obtain ⟨g3, g4⟩ := l2n_one_heat_le hu hG hG0
  obtain ⟨f1, f2⟩ := l2n_heat_le hu.le hF hF0
  obtain ⟨f3, f4⟩ := l2n_half_heat_le hu hF hF0
  have g3' : Summable fun k => ‖zOf 1 (zOf 1 (heatF u G)) k‖ ^ 2 := by
    rw [zOf_zOf_one]
    exact g3
  have hPF : PiF (zOf 1 (heatF u G)) = zOf 1 (heatF u G) := Fam.PiF_zOf (PiF_heatF hG')
  have hm := X1Form_mixed_le hs hr τ h1 h2 g1 g3' hPF f1 f3 (PiF_heatF hF')
  rw [zOf_zOf_one] at hm
  have hCe := Ce_pos
  have he := Real.exp_pos (-u)
  have he1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hl1 := l2n_nonneg G
  have hl2 := l2n_nonneg F
  set v := Real.exp (-u) / u with hv
  have hv0 : 0 ≤ v := by positivity
  have hq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv0
  have hsq : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  have n1 := l2n_nonneg (zOf 2 (heatF u G))
  have n2 := l2n_nonneg (heatF u F)
  have n3 := l2n_nonneg (zOf 1 (heatF u G))
  have n4 := l2n_nonneg (zOf 1 (heatF u F))
  have hs1 : Real.sqrt (Real.exp (-u)) ≤ 1 := Real.sqrt_le_one.2 he1
  have a1 : l2n (zOf 2 (heatF u G)) * l2n (heatF u F) ≤ 2 * v * (l2n G * l2n F) := by
    have g5 : l2n (zOf 2 (heatF u G)) ≤ 2 / u * l2n G := by
      refine g4.trans (mul_le_mul_of_nonneg_right ?_ hl1)
      calc _ ≤ 1 * (2 / u) := mul_le_mul_of_nonneg_right hs1 (by positivity)
        _ = _ := by ring
    have a := mul_le_mul g5 f2 n2 (by positivity)
    refine a.trans (le_of_eq ?_)
    simp only [hv]
    ring
  have a2 : l2n (zOf 1 (heatF u G)) * l2n (zOf 1 (heatF u F)) ≤ v * (l2n G * l2n F) := by
    have a := mul_le_mul g2 f4 n4 (by positivity)
    refine a.trans (le_of_eq ?_)
    calc _ = Real.sqrt v ^ 2 * (l2n G * l2n F) := by ring
      _ = _ := by rw [hq]
  have hsum : l2n (zOf 2 (heatF u G)) * l2n (heatF u F) +
      l2n (zOf 1 (heatF u G)) * l2n (zOf 1 (heatF u F)) ≤ 3 * v * (l2n G * l2n F) := by
    linarith
  have hh1 : Ce * hnorm 1 (Bslow (heatF u S)) ≤ Ce * (41 * M * hnorm 2 S) := by
    have : hnorm 1 (Bslow (heatF u S)) ≤ 41 * M * hnorm 2 S := by
      refine h3.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact mul_le_of_le_one_left hb he1
    exact mul_le_mul_of_nonneg_left this hCe.le
  have hn0 := hnorm_nonneg 1 (Bslow (heatF u S))
  have hsum0 : 0 ≤ l2n (zOf 2 (heatF u G)) * l2n (heatF u F) +
      l2n (zOf 1 (heatF u G)) * l2n (zOf 1 (heatF u F)) := by positivity
  refine hm.trans ?_
  refine (mul_le_mul_of_nonneg_left (mul_le_mul hh1 hsum hsum0 (by positivity))
    (by positivity)).trans (le_of_eq ?_)
  simp only [hv]
  field_simp

/-- **The output half of `Z`** (Body 40, LOCAL649), at a free cut `u₀`:
`‖A^{1/2} Z‖ ≲ W b √u₀ + q⁻¹ M b (1 + ln(1/u₀))`.  Body 40 cuts at `u₀ = q⁻²` and needs the tame
bound `‖h_u‖₂ ≲ M b u^{−1/2}` (the `A₆ B₃` of Body 30).  With the Wiener bound below `u₀`, the same
result follows by cutting at `u₀ ≲ (M/(qW))²`: only `ln(1/u₀)` changes, by a logarithm of the caps. -/
theorem ZForm_half_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hS : Adm 2 S) (hS' : PiS S = S)
    (hM : SupBd S M) (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2)
    (hG' : PiF G = G) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F)
    (hGl : ∀ k, leray k (G k) = G k) (hFl : ∀ k, leray k (F k) = F k) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (hu₁ : u₀ ≤ 1) :
    ‖ZForm 1 s r τ S S (zOf 1 G) F‖ ≤ (25600 * c4 * wiener S * hnorm 2 S * Real.sqrt u₀ +
      44 * (Ce * (41 * 3)) / |r| * M * hnorm 2 S * (1 + Real.log (1 / u₀))) * (l2n G * l2n F) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hb := hnorm_nonneg 2 S
  have hCe := Ce_pos
  have hc := c4_pos
  have hl1 := l2n_nonneg G
  have hl2 := l2n_nonneg F
  have hW := wiener_nonneg S
  set A := 12800 * c4 * wiener S * hnorm 2 S * (l2n G * l2n F) with hA
  set B := 44 * (Ce * (41 * 3)) / |r| * M * hnorm 2 S * (l2n G * l2n F) with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨hI, hV⟩ := maj3_integral (A := A) hu₀ hu₁ hB0
  have hbd : ∀ u ∈ Ioi (0 : ℝ), ‖(famZ s r).src (τ + r * u) (heatF u S) (heatF u S)
      (heatF u (zOf 1 G)) (heatF u F)‖ ≤ maj3 u₀ A B u := fun u hu => by
    have hu0 : 0 < u := hu
    have hs1 := half_short hs hr hu0 (τ + r * u) hS hS' hG hG1 hG' hF hF' hGl hFl
    have hs2 := half_long hs hr hu0 (τ + r * u) hS hS' hM hG hG1 hG' hF hF' hGl hFl
    have he := Real.exp_pos (-u)
    unfold maj3
    by_cases h1 : u ≤ u₀
    · have m1 : u ∈ Ioc 0 u₀ := ⟨hu0, h1⟩
      have m2 : u ∉ Ioc u₀ 1 := fun h => absurd h.1 (not_lt.2 h1)
      have m3 : u ∉ Ioi (1 : ℝ) := fun h => absurd (lt_of_le_of_lt (h1.trans hu₁) h) (lt_irrefl _)
      rw [indicator_of_mem m1, indicator_of_notMem m2, indicator_of_notMem m3, add_zero, add_zero]
      exact hs1
    · rw [not_le] at h1
      by_cases h2 : u ≤ 1
      · have m1 : u ∉ Ioc 0 u₀ := fun h => absurd h.2 (not_le.2 h1)
        have m2 : u ∈ Ioc u₀ 1 := ⟨h1, h2⟩
        have m3 : u ∉ Ioi (1 : ℝ) := fun h => absurd h (not_lt.2 h2)
        rw [indicator_of_notMem m1, indicator_of_mem m2, indicator_of_notMem m3, add_zero, zero_add]
        refine hs2.trans (mul_le_mul_of_nonneg_left ?_ hB0)
        have he1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
        exact mul_le_of_le_one_left (by positivity) he1
      · rw [not_le] at h2
        have m1 : u ∉ Ioc 0 u₀ := fun h => absurd (h.2.trans hu₁) (not_le.2 h2)
        have m2 : u ∉ Ioc u₀ 1 := fun h => absurd h.2 (not_le.2 h2)
        have m3 : u ∈ Ioi (1 : ℝ) := h2
        rw [indicator_of_notMem m1, indicator_of_notMem m2, indicator_of_mem m3, zero_add,
          zero_add]
        refine hs2.trans (mul_le_mul_of_nonneg_left ?_ hB0)
        have : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2.le
        exact mul_le_of_le_one_right he.le this
  have hmain := norm_integral_le_of_norm_le hI
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hbd))
  rw [← famZ_form, Fam.form_heat (famZ_bd hs hr) hS.mz hS' hS.mz hS' hG1 hF hF' τ, norm_neg]
  refine hmain.trans (hV.trans (le_of_eq ?_))
  simp only [hA, hB]
  ring

end OVNS.Quant.Metric

end
