import OddViscousNS.Quant.Joint.Metric.High1

/-!
# The cubic group at weight one (step J5, node N10)

Unit: `TIMED_METRIC_PROOF_V2.md` §8.  `Y_split₁` is `Y_split₂` at weight one.  `group₁_le`: off the
source of `O`, the group is the low last edge, (8.2), the high ancestors, the separated sector
(8.4) and the heat (8.5).
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic

/-- `A^{−1/2} u`. -/
def zInv (u : Field) (k : Mode) : V3 := (((absk k)⁻¹ : ℝ) : ℂ) • u k

lemma nrm_zInv (u : Field) : nrm (zInv u) = in1 (nrm u) := by
  funext k
  simp only [nrm, zInv, in1, norm_smul, Complex.norm_real, Real.norm_of_nonneg
    (inv_nonneg.2 (absk_nonneg k))]
  rw [div_eq_mul_inv, mul_comm]

lemma weight_zInv (σ : ℕ) (u : Field) (k : Mode) :
    sobWeight ((σ + 1 : ℕ) : ℝ) k * ‖zInv u k‖ ^ 2 = sobWeight (σ : ℝ) k * ‖u k‖ ^ 2 := by
  by_cases hk : k = 0
  · simp [sobWeight, hk]
  · have hK : absk k ≠ 0 := absk_eq_zero.not.2 hk
    rw [sobWeight_nat _ hk, sobWeight_nat _ hk]
    simp only [zInv, norm_smul, Complex.norm_real, Real.norm_of_nonneg
      (inv_nonneg.2 (absk_nonneg k))]
    field_simp
    ring

lemma inH_zInv {σ : ℕ} {u : Field} (hu : InH (σ : ℝ) u) : InH ((σ + 1 : ℕ) : ℝ) (zInv u) :=
  hu.congr fun k => (weight_zInv σ u k).symm

lemma hnorm_zInv (σ : ℕ) (u : Field) : hnorm ((σ + 1 : ℕ) : ℝ) (zInv u) = hnorm (σ : ℝ) u := by
  simp only [hnorm, weight_zInv]

lemma PiF_zInv {u : Field} (hu : PiF u = u) : PiF (zInv u) = zInv u := by
  funext k
  by_cases hk : k 2 = 0
  · have h0 : u k = 0 := fast_zero hu hk
    simp [PiF, hk, zInv, h0]
  · simp [PiF, hk]

/-- The fibre norm of `A^{−1/2} u`. -/
lemma lhB_zInv {D : ℝ} (hD : 1 ≤ D) {u : Field} (h1 : InH 1 u) (hu : PiF u = u) :
    LhB (in1 (nrm u)) (Real.sqrt (9 + 8 * Real.log D) * hnorm 0 u + 5 / D * hnorm 1 u) := by
  have hV : InH 2 (zInv u) := by
    have := inH_zInv (σ := 1) (by simpa using h1)
    simpa using this
  have h := lhB_log hD hV (PiF_zInv hu)
  rw [nrm_zInv] at h
  have e1 : hnorm 1 (zInv u) = hnorm 0 u := by
    simpa using hnorm_zInv 0 u
  have e2 : hnorm 2 (zInv u) = hnorm 1 u := by
    have := hnorm_zInv 1 u
    norm_num at this
    exact this
  rwa [e1, e2] at h

/-- **The cubic group at the last edge, split**, at weight one. -/
theorem Y_split₁ {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 1 ≤ D) {S F : Field} (hS : MZ 2 S)
    (hS' : PiS S = S) (hF : MZ 2 F) (hF' : PiF F = F) (hFs : IsSolenoidal F)
    (hw : Summable fun k => ‖zOf 1 (Lop τ S F) k‖ ^ 2)
    (hwl : Summable fun k => ‖zOf 1 (QLF τ S F) k‖ ^ 2) :
    X2Form 1 1 r τ S S (zOf 1 F) (zOf 1 (Lop τ S F)) +
        ZForm 1 1 r τ S S (zOf 1 F) (zOf 1 (Lop τ S F)) =
      (X2Form 1 1 r τ S S (zOf 1 F) (zOf 1 (QLF τ S F)) +
        ZForm 1 1 r τ S S (zOf 1 F) (zOf 1 (QLF τ S F))) +
      YLForm (muH D) 1 r τ S S S (zOf 1 F) (zOf 1 F) +
      YLForm (fun x => ((muS D x : ℝ) : ℂ)) 1 r τ S S S (zOf 1 F) (zOf 1 F) +
      ((famQ 1 r D).src τ S S S (zOf 1 F) (zOf 1 F) + HtQ D 1 r τ S S S (zOf 1 F) (zOf 1 F)) := by
  have hF1 : InH ((1 : ℕ) : ℝ) F := by simpa using hF.inH.mono (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨hz, -⟩ := l2_zOf hF1 hF.mean
  have hz' : PiF (zOf 1 F) = zOf 1 F := Fam.PiF_zOf hF'
  have hzl : ∀ k, leray k (zOf 1 F k) = zOf 1 F k := fun k => leray_zOf hFs hF.mean k 1
  have hL' : PiF (zOf 1 (QLF τ S F)) = zOf 1 (QLF τ S F) := Fam.PiF_zOf (PiF_QLF τ S F)
  have hH' : PiF (zOf 1 (QHF τ S F)) = zOf 1 (QHF τ S F) := Fam.PiF_zOf (PiF_QHF τ S F)
  have hwh : Summable fun k => ‖zOf 1 (QHF τ S F) k‖ ^ 2 := by
    have e : ∀ k, zOf 1 (QHF τ S F) k = zOf 1 (Lop τ S F) k - zOf 1 (QLF τ S F) k := fun k => by
      simp only [zOf, QHF, Pi.sub_apply, smul_sub]
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((hw.mul_left 2).add (hwl.mul_left 2))
    rw [e]
    have h1 := norm_sub_le (zOf 1 (Lop τ S F) k) (zOf 1 (QLF τ S F) k)
    have h2 := norm_nonneg (zOf 1 (Lop τ S F) k - zOf 1 (QLF τ S F) k)
    nlinarith only [h1, h2, sq_nonneg (‖zOf 1 (Lop τ S F) k‖ - ‖zOf 1 (QLF τ S F) k‖)]
  have n3 : ∀ x : I4, ‖((muS D x : ℝ) : ℂ)‖ ≤ muS D x := fun x => by
    rw [Complex.norm_real, Real.norm_of_nonneg (muS_nonneg D x)]
  have hsH := (YLForm_high_one hr τ D hS hS' hz hz hz' (norm_muH_le D) fun x hx => lowM_gt fun h0 => by
    apply hx
    have h1 : ((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ) = 0 := by rw [h0]; simp
    rw [muH, h1, zero_mul]).1
  have hsS := (YLForm_sep_one hr τ hD hS hS' hz hz hz' n3).1
  have hsQ : Summable fun x : I4 => ((muQ D x : ℝ) : ℂ) * inner ℂ (zOf 1 F x.1)
      (YLb 1 r τ S S S x (zOf 1 F (inJ x))) := by
    have h1 := srcQ_summable (s := 1) (Or.inl rfl) hr τ D hS hS' hS hS' hS hS' hz hz hz'
    have h2 := (HtQ_le (s := 1) (Or.inl rfl) hr τ hD hS hS' (hS.inH.mono (by norm_num)) hS' hS.inH
      hS' hz hz hz').1
    have h3 : Summable fun x : I4 => (famQ 1 r D).srcT x (zOf 1 F x.1) (zOf 1 F (inJ x)) (S x.2.1)
        (S x.2.2.1) (S x.2.2.2) τ + ((muQ D x : ℝ) : ℂ) * inner ℂ (zOf 1 F x.1)
          (HB 1 r τ S S S x (zOf 1 F (inJ x))) := h1.add h2
    refine h3.congr fun x => ?_
    exact (YL_term (G := zOf 1 F) (F := zOf 1 F) D 1 r τ S S S hzl hzl x).symm
  have hsum : Summable fun x : I4 => ((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ) *
      inner ℂ (zOf 1 F x.1) (YLb 1 r τ S S S x (zOf 1 F (inJ x))) := by
    refine ((hsH.add hsQ).add hsS).congr fun x => ?_
    rw [mu_split D x]
    ring
  have hHigh := Y_high_eq (s := 1) (Or.inl rfl) hr τ hS hS' hF.mean (mz_l2 (by norm_num) hF) hz hz'
    hwh hH' hsum
  have hSplit : YLForm (fun x => ((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ)) 1 r τ S S S (zOf 1 F)
      (zOf 1 F) = YLForm (muH D) 1 r τ S S S (zOf 1 F) (zOf 1 F) +
        YLForm (fun x => ((muQ D x : ℝ) : ℂ)) 1 r τ S S S (zOf 1 F) (zOf 1 F) +
        YLForm (fun x => ((muS D x : ℝ) : ℂ)) 1 r τ S S S (zOf 1 F) (zOf 1 F) := by
    simp only [YLForm]
    rw [← hsH.tsum_add hsQ, ← (hsH.add hsQ).tsum_add hsS]
    refine tsum_congr fun x => ?_
    rw [mu_split D x]
    ring
  have hQ := YL_eq_src_add (s := 1) (Or.inl rfl) hr τ hD hS hS' hS hS' hS hS' hz hz hz' hzl hzl
  have hX := X2Form_add (s := 1) (Or.inl rfl) hr τ hS hS' hS hS' hz hwl hL' hwh hH'
  have hZ := ZForm_add (s := 1) (Or.inl rfl) hr τ hS hS' hS hS' hz hwl hL' hwh hH'
  rw [zOf_Lop_split, hX, hZ]
  rw [hSplit, hQ] at hHigh
  calc _ = (X2Form 1 1 r τ S S (zOf 1 F) (zOf 1 (QLF τ S F)) +
        ZForm 1 1 r τ S S (zOf 1 F) (zOf 1 (QLF τ S F))) +
        (X2Form 1 1 r τ S S (zOf 1 F) (zOf 1 (QHF τ S F)) +
          ZForm 1 1 r τ S S (zOf 1 F) (zOf 1 (QHF τ S F))) := by ring
    _ = _ := by
        rw [hHigh]
        ring

/-- The bound of the cubic group at weight one, with `e = a_F`, `d = b_F`. -/
def G₁ (r D M : ℝ) (S : Field) (e d : ℝ) : ℝ :=
  2 * (2 ^ 14 / |r| * halfB (hnorm 1 S) (wiener S) (2 * CLow 0 * M * e) e
    (Real.sqrt (9 + 8 * Real.log D) * (2 * CLow 0 * M * e) + 5 / D * (2 * CLow 1 * M * d))
    (Real.sqrt (9 + 8 * Real.log D) * e + 5 / D * d)) +
  Cm3 / |r| * (tailW D S * hnorm 2 S ^ 2 + wiener S * hnorm 2 S * tailB D S) * e ^ 2 +
  2 ^ 28 / |r| ^ 2 * (e ^ 2 * sep1B D S) +
  2 ^ 21 / |r| ^ 2 * (e ^ 2 * (hnorm 1 S ^ 2 * (9 + 8 * Real.log (4 * D)) *
    (Real.sqrt (9 + 8 * Real.log D) * hnorm 2 S)))

lemma l2n_eq_hnorm0 {u : Field} (h0 : u 0 = 0) : l2n u = hnorm 0 u := by
  simp only [l2n, hnorm]
  congr 1
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [hk, h0, sobWeight]
  · simp [sobWeight, hk]

/-- `Lop` is in `H¹` on `H²`. -/
lemma Lop_one {τ : ℝ} {S F : Field} (hS : MZ 2 S) (hF : MZ 2 F) : MZ 1 (Lop τ S F) := by
  have h1 := (OVNS.Quant.H2.Qm_one_le (phaseM_bdd τ) hS hF).1
  refine ⟨?_, ?_⟩
  · have h2 : InH 1 (PiF (Qphase τ S F)) := InH.PiF h1
    exact h2.smul 2
  · simp [Lop, PiF]

/-- `halfB` is monotone. -/
lemma halfB_mono {a W e₁ e₁' e₂ L₁ L₁' L₂ : ℝ} (ha : 0 ≤ a) (hW : 0 ≤ W) (he₁ : 0 ≤ e₁)
    (he₂ : 0 ≤ e₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (h1 : e₁ ≤ e₁') (h2 : L₁ ≤ L₁') :
    halfB a W e₁ e₂ L₁ L₂ ≤ halfB a W e₁' e₂ L₁' L₂ := by
  simp only [halfB]
  have hL : 0 ≤ L₁' := hL₁.trans h2
  have he : 0 ≤ e₁' := he₁.trans h1
  gcongr

/-- **The cubic group at weight one, off the source of `O`.** -/
theorem group₁_le (hr1 : 1 ≤ |r|) (τ : ℝ) {D M : ℝ} (hD : 1 ≤ D) {S F : Field} (hS : Adm 2 S)
    (hS' : PiS S = S) (hM : GN.SupBd S M) (hF : Adm 2 F) (hF' : PiF F = F) :
    ‖X2Form 1 1 r τ S S (zOf 1 F) (zOf 1 (Lop τ S F)) +
        ZForm 1 1 r τ S S (zOf 1 F) (zOf 1 (Lop τ S F)) -
        (famQ 1 r D).src τ S S S (zOf 1 F) (zOf 1 F)‖ ≤ G₁ r D M S (hnorm 1 F) (hnorm 2 F) := by
  have hq : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hq
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hF1' : InH 1 F := hF.inH.mono (by norm_num)
  have hF1 : InH ((1 : ℕ) : ℝ) F := by simpa using hF1'
  obtain ⟨hz, nz⟩ := l2_zOf hF1 hF.mean
  have nz' : l2n (zOf 1 F) = hnorm 1 F := by simpa using nz
  have hz' : PiF (zOf 1 F) = zOf 1 F := Fam.PiF_zOf hF'
  have hw : Summable fun k => ‖zOf 1 (Lop τ S F) k‖ ^ 2 := by
    have h1 := Lop_one (τ := τ) hS.mz hF.mz
    have h2 : InH ((1 : ℕ) : ℝ) (Lop τ S F) := by simpa using h1.inH
    exact (l2_zOf h2 h1.mean).1
  have hL0 := QLF_bound τ hS hS' hM hF 0 (by simpa using hF1')
  have hL1 := QLF_bound τ hS hS' hM hF 1 (by simpa using hF.inH)
  have h0 : QLF τ S F 0 = 0 := by simp [QLF, PiF]
  have hwl : Summable fun k => ‖zOf 1 (QLF τ S F) k‖ ^ 2 := (l2_zOf hL1.1 h0).1
  rw [Y_split₁ hr τ hD hS.mz hS' hF.mz hF' hF.sol hw hwl]
  have e : ∀ A B C P H : ℂ, A + B + C + (P + H) - P = A + B + C + H := fun A B C P H => by ring
  rw [e]
  set e₀ := hnorm 1 F with he₀
  set d₀ := hnorm 2 F with hd₀
  have he0 : 0 ≤ e₀ := hnorm_nonneg _ _
  have hd0 : 0 ≤ d₀ := hnorm_nonneg _ _
  have hzB : L2B (nrm (zOf 1 F)) e₀ := by
    have := l2B_nrm hz
    rwa [nz'] at this
  have hL0' : hnorm 0 (QLF τ S F) ≤ 2 * CLow 0 * M * e₀ := by
    simpa using hL0.2
  have hL1' : hnorm 1 (QLF τ S F) ≤ 2 * CLow 1 * M * d₀ := by
    simpa using hL1.2
  have hG2 : Summable fun k => ‖QLF τ S F k‖ ^ 2 :=
    mz_l2 (t := 0) le_rfl ⟨by simpa using hL0.1, h0⟩
  have hGB : L2B (nrm (QLF τ S F)) (hnorm 0 (QLF τ S F)) := by
    have := l2B_nrm hG2
    rwa [l2n_eq_hnorm0 h0] at this
  have hLG := lhB_zInv hD (by simpa using hL1.1) (PiF_QLF τ S F)
  have hLF := lhB_log hD hF.inH hF'
  set Z := Real.sqrt (9 + 8 * Real.log D) with hZ
  have hZ0 : 0 ≤ Z := Real.sqrt_nonneg _
  have hD0 : 0 < D := by linarith
  have hS0 := hnorm_nonneg 1 S
  have hW0 := wiener_nonneg S
  have hn0 := hnorm_nonneg 0 (QLF τ S F)
  have hn1 := hnorm_nonneg 1 (QLF τ S F)
  have hC0 := CLow_nonneg 0
  have hC1 := CLow_nonneg 1
  have hL2n : 0 ≤ Z * e₀ + 5 / D * d₀ := by positivity
  have hMono := halfB_mono hS0 hW0 hn0 he0 (L₁ := Z * hnorm 0 (QLF τ S F) +
      5 / D * hnorm 1 (QLF τ S F)) (by positivity) hL2n hL0'
      (L₁' := Z * (2 * CLow 0 * M * e₀) + 5 / D * (2 * CLow 1 * M * d₀)) (by gcongr)
  have hKc : (0 : ℝ) ≤ 2 ^ 14 / |r| := by positivity
  have t1 : ‖X2Form 1 1 r τ S S (zOf 1 F) (zOf 1 (QLF τ S F))‖ ≤ 2 ^ 14 / |r| *
      halfB (hnorm 1 S) (wiener S) (2 * CLow 0 * M * e₀) e₀
        (Z * (2 * CLow 0 * M * e₀) + 5 / D * (2 * CLow 1 * M * d₀)) (Z * e₀ + 5 / D * d₀) := by
    rw [X2Form_conj 1 r τ hS.real hS.real, RCLike.norm_conj]
    exact (X2_half_one hr τ hS.mz hS' hF' hGB hzB hLG hLF).2.trans
      (mul_le_mul_of_nonneg_left hMono hKc)
  have t2 : ‖ZForm 1 1 r τ S S (zOf 1 F) (zOf 1 (QLF τ S F))‖ ≤ 2 ^ 14 / |r| *
      halfB (hnorm 1 S) (wiener S) (2 * CLow 0 * M * e₀) e₀
        (Z * (2 * CLow 0 * M * e₀) + 5 / D * (2 * CLow 1 * M * d₀)) (Z * e₀ + 5 / D * d₀) := by
    rw [ZForm_conj 1 r τ hS.real hS.real, RCLike.norm_conj]
    exact (Z_half_one hr τ hS.mz hS' hF' hGB hzB hLG hLF).2.trans
      (mul_le_mul_of_nonneg_left hMono hKc)
  have n3 : ∀ x : I4, ‖((muS D x : ℝ) : ℂ)‖ ≤ muS D x := fun x => by
    rw [Complex.norm_real, Real.norm_of_nonneg (muS_nonneg D x)]
  have t3 := (YLForm_high_one hr τ D hS.mz hS' hz hz hz' (norm_muH_le D) fun x hx =>
    lowM_gt fun h0 => by
      apply hx
      have h1 : ((1 - lowM x.2.2.2 (inJ x) : ℝ) : ℂ) = 0 := by rw [h0]; simp
      rw [muH, h1, zero_mul]).2
  have t4 := (YLForm_sep_one hr τ hD hS.mz hS' hz hz hz' n3).2
  have t5 := HtQ_one_le hr τ hD hS.mz hS' hz hz hz'
  rw [nz'] at t3 t4 t5
  have hZ4 : Real.sqrt (9 + 8 * Real.log (4 * D)) * Real.sqrt (9 + 8 * Real.log (4 * D)) =
      9 + 8 * Real.log (4 * D) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 4 * D)
    exact Real.mul_self_sqrt (by linarith)
  have hH : e₀ * hnorm 1 S * Real.sqrt (9 + 8 * Real.log (4 * D)) *
      (e₀ * hnorm 1 S * Real.sqrt (9 + 8 * Real.log (4 * D))) * (Z * hnorm 2 S) =
      e₀ ^ 2 * (hnorm 1 S ^ 2 * (9 + 8 * Real.log (4 * D)) * (Z * hnorm 2 S)) := by
    calc _ = e₀ ^ 2 * (hnorm 1 S ^ 2 * (Real.sqrt (9 + 8 * Real.log (4 * D)) *
          Real.sqrt (9 + 8 * Real.log (4 * D))) * (Z * hnorm 2 S)) := by ring
      _ = _ := by rw [hZ4]
  rw [hH] at t5
  calc _ ≤ _ := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3) t4)
        t5
    _ = _ := by
        simp only [G₁]
        ring

end OVNS.Quant.Metric

end
