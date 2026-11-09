import OddViscousNS.Quant.Joint.Quartic.Link

/-!
# The four source directions (step J5, node N11)

J3-v2 §4, §5: the exact split of `N_F = F_t + AF`, `N_S = S_t + AS`.

* `fastNL_split`: `N_F = −2 Q_hi + N_rest`, `N_rest = −2 Q_lo − Π_F Q(F, F) − Π_F H_ψ`;
* `hnorm_two_fastRest`: `‖N_rest‖₂ ≲ M c_F + √(ab) c_F + (φ/q)(c_F + c_S) + φ²/q²`;
* `lhB_fastNL`: the inner fibre of `N_F`;
* `hnorm_two_fastNL`, `hnorm_two_slowNL`: the two `H²` bounds.

**One deviation from J3-v2 §4, deliberate.**  The slow–slow product is bounded by `‖Q(S, S)‖₂ ≤ 16 W c_S`,
with the Wiener norm, not by `C M_∞ c_S`.  The latter needs the Gagliardo–Nirenberg estimates
`‖DS‖₆ ≲ M^{2/3} c^{1/3}`, `‖D²S‖₃ ≲ M^{1/3} c^{2/3}`, which are not in Lean.  The price is in one row, the
slow ancestor: `U W y` in place of `U R y`.  That row stays strictly below `Q` (`Rows.lean`).
-/

open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- The signed high source of the energy identity: `−2 Q_hi`. -/
def mixHi (τ : ℝ) (S F : Field) : Field := -(Qhi τ S F + Qhi τ S F)

/-- The rest of `N_F`. -/
def fastRest (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : Field :=
  -(Qlo (r * u) (Sp r g y u) (Fp r g y u) + Qlo (r * u) (Sp r g y u) (Fp r g y u)) -
    PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u)) - PiF (Hpsi r g y u)

lemma Sp_adm (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    Adm 2 (Sp r g y u) := (actual_adm h hu huT).PiS

lemma Fp_adm (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    Adm 2 (Fp r g y u) := (actual_adm h hu huT).PiF

lemma l2_of_adm {f : Field} (hf : Adm 2 f) : Summable fun k => ‖f k‖ ^ 2 :=
  summable_norm_sq_of_inH (hf.inH.mono (by norm_num : (0 : ℝ) ≤ 2))

/-- **The split of the fast direction.** -/
theorem fastNL_split (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    fastNL r g y u = mixHi (r * u) (Sp r g y u) (Fp r g y u) + fastRest r g y u := by
  have hx := actual_adm h hu huT
  have e1 : Qphase (r * u) (y u) (y u) = Qphase (r * u) (actual r g y u) (actual r g y u) +
      Hpsi r g y u := by
    simp only [Hpsi]
    abel
  have e2 := PiF_Qphase_eq (r * u) hx
  have e3 := Qphase_split (r * u) (l2_of_adm (Sp_adm h hu huT)) (l2_of_adm (Fp_adm h hu huT))
  have e4 : PiF (Qphase (r * u) (y u) (y u)) = PiF (Qphase (r * u) (actual r g y u)
      (actual r g y u)) + PiF (Hpsi r g y u) := by
    rw [e1, PiF_add'']
  change -PiF (Qphase (r * u) (y u) (y u)) = _
  rw [e4, e2]
  simp only [mixHi, fastRest]
  change -(Qphase (r * u) (Sp r g y u) (Fp r g y u) + Qphase (r * u) (Sp r g y u) (Fp r g y u) +
    PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u)) + PiF (Hpsi r g y u)) = _
  rw [e3]
  abel

/-- `‖Q(F, F)‖₂ ≤ 16 c_I √(ab) c`, on the whole product. -/
lemma hnorm_two_QFF (τ : ℝ) {F : Field} (hF : MZ 3 F) :
    InH 2 (Qphase τ F F) ∧ hnorm 2 (Qphase τ F F) ≤
      16 * cI * Real.sqrt (hnorm 1 F * hnorm 2 F) * hnorm 3 F := by
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  obtain ⟨i, b⟩ := H2.Qm_two_le (phaseM_bdd τ) hF hF
  refine ⟨i, b.trans ?_⟩
  have hw := wiener_le_cI hF2
  have h3 := hnorm_nonneg 3 F
  have := mul_le_mul_of_nonneg_right hw h3
  nlinarith only [this]

/-- **The rest of the fast direction in `H²`** (J3-v2 §4): the low mixed, purefast and filter pieces. -/
theorem hnorm_two_fastRest (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u M : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u))
    (hM : slowSup r g y u ≤ M) :
    InH 2 (fastRest r g y u) ∧ hnorm 2 (fastRest r g y u) ≤
      (2 * CLow 2 * M + 16 * cI * Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u))) *
          hnorm 3 (Fp r g y u) +
        64 * c4 * φ / |r| * (hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) +
        64 * c4 * φ ^ 2 / r ^ 2 := by
  have hS := Sp_adm h hu huT
  have hF := Fp_adm h hu huT
  have hF3m : MZ 3 (Fp r g y u) := ⟨hF3, hF.mean⟩
  have hSup : GN.SupBd (Sp r g y u) M := GN.supBd_slowSup hS.inH hM
  obtain ⟨iL, bL⟩ := hnorm_Qlo_le (r * u) hS (Fam.PiS_Sp r g y u) hSup hF 2
    (by simpa using hF3)
  have iL' : InH 2 (Qlo (r * u) (Sp r g y u) (Fp r g y u)) := by simpa using iL
  have bL' : hnorm 2 (Qlo (r * u) (Sp r g y u) (Fp r g y u)) ≤ CLow 2 * M *
      hnorm 3 (Fp r g y u) := by
    have e : (((2 + 1 : ℕ)) : ℝ) = 3 := by norm_num
    have e2 : (((2 : ℕ)) : ℝ) = 2 := by norm_num
    rw [e, e2] at bL
    exact bL
  obtain ⟨iQ, bQ⟩ := hnorm_two_QFF (r * u) hF3m
  obtain ⟨iH, bH⟩ := hnorm_two_Hpsi_J h hr hu huT hF3 hS3
  have e : fastRest r g y u = -(Qlo (r * u) (Sp r g y u) (Fp r g y u) +
      Qlo (r * u) (Sp r g y u) (Fp r g y u)) + (-PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u)) +
      -PiF (Hpsi r g y u)) := by
    simp only [fastRest]
    abel
  have i1 := (iL'.add iL').neg
  have i2 := iQ.PiF.neg
  have i3 := iH.PiF.neg
  refine ⟨by rw [e]; exact i1.add (i2.add i3), ?_⟩
  rw [e]
  refine (hnorm_add_le i1 (i2.add i3)).trans ?_
  have t1 := hnorm_add_le iL' iL'
  have t2 := hnorm_add_le i2 i3
  rw [hnorm_neg]
  have t3 := (hnorm_PiF_le iQ).trans bQ
  have t4 := (hnorm_PiF_le iH).trans bH
  have a2 : hnorm 2 (-PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u))) =
      hnorm 2 (PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u))) := hnorm_neg
  have a3 : hnorm 2 (-PiF (Hpsi r g y u)) = hnorm 2 (PiF (Hpsi r g y u)) := hnorm_neg
  rw [a2, a3] at t2
  have e4 : fastNorm 3 r g y u = hnorm 3 (Fp r g y u) := rfl
  have e5 : slowNorm 3 r g y u = hnorm 3 (Sp r g y u) := rfl
  rw [e4, e5] at t4
  linarith

/-- The rest of the fast direction is fast. -/
lemma fastRest_eq (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    fastRest r g y u = fastNL r g y u +
      (Qhi (r * u) (Sp r g y u) (Fp r g y u) + Qhi (r * u) (Sp r g y u) (Fp r g y u)) := by
  rw [fastNL_split h hu huT, mixHi]
  abel

lemma PiF_fastRest (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) : PiF (fastRest r g y u) = fastRest r g y u := by
  rw [fastRest_eq h hu huT, PiF_add'', PiF_add'', PiF_fastNL,
    PiF_Qhi (Fam.PiS_Sp r g y u) (PiF_Fp r g y u)]

/-- **The inner fibre of `N_F`** (Body 46, J3-v2 §4): `L_h(N_F) ≤ 20 W₁ L_h(F) + √17 ‖N_rest‖₂`.
"Do not enlarge the inner fast direction to `H²` before splitting it." -/
theorem lhB_fastNL (h : ActualSol μ φ r g y Ty) {u L W₁ : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hR : InH 2 (fastRest r g y u))
    (hW : L1B (gr (Sp r g y u)) W₁) (hL : LhB (nrm (Fp r g y u)) L) :
    LhB (nrm (fastNL r g y u)) (20 * (W₁ * L) + Real.sqrt 17 * hnorm 2 (fastRest r g y u)) := by
  have hS := Sp_adm h hu huT
  have hF := Fp_adm h hu huT
  have h1 := (lhB_Qhi (r * u) hS.mz (Fam.PiS_Sp r g y u) (l2_of_adm hF) hW hL).const_mul
    (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := lhB_two hR (PiF_fastRest h hu huT)
  have h3 := h1.add h2
  have e : 2 * (10 * (W₁ * L)) + Real.sqrt 17 * hnorm 2 (fastRest r g y u) =
      20 * (W₁ * L) + Real.sqrt 17 * hnorm 2 (fastRest r g y u) := by ring
  rw [e] at h3
  refine h3.of_le (fun _ => norm_nonneg _) fun k => ?_
  rw [fastNL_split h hu huT]
  simp only [nrm, mixHi, Pi.add_apply, Pi.neg_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  rw [norm_neg]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  ring

/-- **`N_F` in `H²`.** -/
theorem hnorm_two_fastNL (h : ActualSol μ φ r g y Ty) {u L : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hR : InH 2 (fastRest r g y u)) (hS3 : InH 3 (Sp r g y u))
    (hL : LhB (nrm (Fp r g y u)) L) :
    InH 2 (fastNL r g y u) ∧ hnorm 2 (fastNL r g y u) ≤
      20 * (hnorm 3 (Sp r g y u) * L) + hnorm 2 (fastRest r g y u) := by
  have hS := Sp_adm h hu huT
  have hF := Fp_adm h hu huT
  have hS3m : MZ 3 (Sp r g y u) := ⟨hS3, hS.mean⟩
  obtain ⟨iQ, bQ⟩ := hnorm_two_Qhi (r * u) hS3m (Fam.PiS_Sp r g y u) (l2_of_adm hF) hL
  have i1 := (iQ.add iQ).neg
  rw [fastNL_split h hu huT, mixHi]
  refine ⟨i1.add hR, (hnorm_add_le i1 hR).trans ?_⟩
  rw [hnorm_neg]
  have := hnorm_add_le iQ iQ
  linarith

/-- `Π_S Q(w, w)`: the mixed term has no slow output. -/
lemma PiS_Qphase_eq (τ : ℝ) {w : Field} (hw : Adm 2 w) :
    PiS (Qphase τ w w) = Qphase τ (PiS w) (PiS w) + PiS (Qphase τ (PiF w) (PiF w)) := by
  funext k
  rw [Qphase_sectors τ hw]
  by_cases hk : k 2 = 0
  · simp only [Pi.add_apply, PiS, hk, ite_true, Qphase_slow_fast τ (PiS_PiS_eq w) (PiF_PiF_eq w) hk]
    simp
  · simp only [Pi.add_apply, PiS, hk, ite_false, Qphase_slow_slow τ (PiS_PiS_eq w) hk]
    simp

/-- **`N_S` in `H²`**, with the Wiener norm of `S` (see the module docstring). -/
theorem hnorm_two_slowNL (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u)) :
    InH 2 (slowNL r g y u) ∧ hnorm 2 (slowNL r g y u) ≤
      16 * wiener (Sp r g y u) * hnorm 3 (Sp r g y u) +
        16 * cI * Real.sqrt (hnorm 1 (Fp r g y u) * hnorm 2 (Fp r g y u)) * hnorm 3 (Fp r g y u) +
        (64 * c4 * φ / |r| * (hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) +
          64 * c4 * φ ^ 2 / r ^ 2) + φ := by
  have hx := actual_adm h hu huT
  have hS := Sp_adm h hu huT
  have hF := Fp_adm h hu huT
  have hF3m : MZ 3 (Fp r g y u) := ⟨hF3, hF.mean⟩
  have hS3m : MZ 3 (Sp r g y u) := ⟨hS3, hS.mean⟩
  obtain ⟨iS, bS⟩ := H2.Qm_two_le (phaseM_bdd (r * u)) hS3m hS3m
  obtain ⟨iQ, bQ⟩ := hnorm_two_QFF (r * u) hF3m
  obtain ⟨iH, bH⟩ := hnorm_two_Hpsi_J h hr hu huT hF3 hS3
  have hg2 : InH 2 (PiS g) := h.force_adm.inH.PiS
  have e1 : Qphase (r * u) (y u) (y u) = Qphase (r * u) (actual r g y u) (actual r g y u) +
      Hpsi r g y u := by
    simp only [Hpsi]
    abel
  have e2 := PiS_Qphase_eq (r * u) hx
  have e : slowNL r g y u = -(Qphase (r * u) (Sp r g y u) (Sp r g y u)) +
      (-PiS (Qphase (r * u) (Fp r g y u) (Fp r g y u)) + (-PiS (Hpsi r g y u) + PiS g)) := by
    change -PiS (Qphase (r * u) (y u) (y u)) + PiS g = _
    rw [e1, PiS_add', e2]
    change -(Qphase (r * u) (Sp r g y u) (Sp r g y u) +
      PiS (Qphase (r * u) (Fp r g y u) (Fp r g y u)) + PiS (Hpsi r g y u)) + PiS g = _
    abel
  have i1 : InH 2 (-(Qphase (r * u) (Sp r g y u) (Sp r g y u))) := InH.neg iS
  have i2 := iQ.PiS.neg
  have i3 := iH.PiS.neg
  have i4 := i3.add hg2
  refine ⟨by rw [e]; exact i1.add (i2.add i4), ?_⟩
  rw [e]
  have t1 := hnorm_add_le i1 (i2.add i4)
  have t2 := hnorm_add_le i2 i4
  have t3 := hnorm_add_le i3 hg2
  have t4 := (hnorm_PiS_le iQ).trans bQ
  have t5 := (hnorm_PiS_le iH).trans bH
  have t6 := (hnorm_PiS_le h.force_adm.inH).trans h.force_le
  have a1 : hnorm 2 (-Qphase (r * u) (Sp r g y u) (Sp r g y u)) =
      hnorm 2 (Qphase (r * u) (Sp r g y u) (Sp r g y u)) := hnorm_neg
  have a2 : hnorm 2 (-PiS (Qphase (r * u) (Fp r g y u) (Fp r g y u))) =
      hnorm 2 (PiS (Qphase (r * u) (Fp r g y u) (Fp r g y u))) := hnorm_neg
  have a3 : hnorm 2 (-PiS (Hpsi r g y u)) = hnorm 2 (PiS (Hpsi r g y u)) := hnorm_neg
  rw [a1] at t1
  rw [a2] at t2
  rw [a3] at t3
  have e4 : fastNorm 3 r g y u = hnorm 3 (Fp r g y u) := rfl
  have e5 : slowNorm 3 r g y u = hnorm 3 (Sp r g y u) := rfl
  rw [e4, e5] at t5
  have bS' : hnorm 2 (Qphase (r * u) (Sp r g y u) (Sp r g y u)) ≤
      8 * (wiener (Sp r g y u) * hnorm 3 (Sp r g y u) +
        hnorm 3 (Sp r g y u) * wiener (Sp r g y u)) := bS
  linarith

/-- **`N_F` in `H¹`** (J3-v2 §5): `‖N_F‖₁ ≤ 8 Ξ(x) + h`, `h = ‖H_ψ‖₁`. -/
theorem hnorm_one_fastNL_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    hnorm 1 (fastNL r g y u) ≤ 8 * fastXi (actual r g y u) + hnorm 1 (Hpsi r g y u) := by
  have hx := actual_adm h hu huT
  obtain ⟨i1, b1⟩ := hnorm_PiF_Qphase_le (r * u) hx
  obtain ⟨i2, -⟩ := hnorm_one_Hpsi_le h hr hu huT
  have e1 : Qphase (r * u) (y u) (y u) = Qphase (r * u) (actual r g y u) (actual r g y u) +
      Hpsi r g y u := by
    simp only [Hpsi]
    abel
  have e : fastNL r g y u = -(PiF (Qphase (r * u) (actual r g y u) (actual r g y u)) +
      PiF (Hpsi r g y u)) := by
    change -PiF (Qphase (r * u) (y u) (y u)) = _
    rw [e1, PiF_add'']
  rw [e, hnorm_neg]
  exact (hnorm_add_le i1 i2.PiF).trans (add_le_add b1 (hnorm_PiF_le i2))

end OVNS.Quant.Quartic

end
