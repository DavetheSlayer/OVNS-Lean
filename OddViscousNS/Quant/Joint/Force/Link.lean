import OddViscousNS.Quant.Joint.Force.Main
import OddViscousNS.Quant.Joint.Metric.Group2

/-!
# The force slots of the joint right sides (step J5, node N12)

`joint1RHS`, `joint2RHS` (`Metric/JointId.lean`) carry the fast filter `Hf = Π_F H_ψ` through
`fastNL = −Π_F Q(y, y)`, and through the direct term `⟨AˢF, H_ψ⟩`.  Here this is made an identity
instead of a reading of the definitions.

* `fastQ_eq`: `−Π_F Q(x, x) = fastNL + Hf`.  So `fastQ` is `fastNL` without the filter.
* `NQp_pure`: `N_F` without the filter is exactly `−Π_F Q(F, F)`: `(2.5)` of `JOINT_METRIC`.
* `fastQ_pure`: `fastQ = −𝓛F − Π_F Q(F, F)`, the two directions of the remainder.
* `joint1RHS_split`, `joint2RHS_split`, at an `H³` time:
  `joint₁RHS = joint₁Q + forceS 1`, `joint₂RHS = joint₂Q + forceS 2`.
  `forceS s` is the part that carries `Hf`.  `joint₁Q`, `joint₂Q` are the same right sides with
  `fastNL`, `NFp` replaced by `fastQ`, `NQp`, and the direct term removed.
* `forceS_one_le`, `forceS_two_le`: `|forceS s| ≤ force_s`, with no hypothesis.
* `ae_joint_split`: both at almost every time.  `joint1_force_le`, `joint2_force_le`: on a piece,
  with the bounds of `force1_joint`, `force2_joint`.

**What stays in the remainder.**  Only the fast force leaves.  The slow slots are untouched:
`joint₁Q`, `joint₂Q` still contain `hp`, `slowNL`, hence the slow filter `Π_S H_ψ` and `Π_S g`.
These are the `h₀` slots (`hp_eq`), treated in `Force/H0Slot.lean`.

The sums are finite-norm at an `H³` time: every direction is in `H²` (`link_facts`).  No summability
is assumed in a statement.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (Qm_two_le ae_inH3_split cubicHeat2)

noncomputable section

namespace OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}

/-! ### The splitting of the fast nonlinearity -/

lemma PiF_add_f (u v : Field) : PiF (u + v) = PiF u + PiF v := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [PiF, hk]

/-- `−Π_F Q(x, x)`: the fast nonlinearity without the filter. -/
def fastQ (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : Field :=
  -PiF (Qphase (r * u) (actual r g y u) (actual r g y u))

/-- `N_F` without the filter: `fastQ + 𝓛F`. -/
def NQp (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : Field :=
  fastQ r g y u + Lop (r * u) (Sp r g y u) (Fp r g y u)

/-- **The splitting**: `−Π_F Q(x, x) = fastNL + Hf`. -/
theorem fastQ_eq (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    fastQ r g y u = fastNL r g y u + Hf r g y u := by
  funext k
  have e : Hpsi r g y u k = Qphase (r * u) (y u) (y u) k -
      Qphase (r * u) (actual r g y u) (actual r g y u) k := rfl
  by_cases hk : k 2 = 0
  · simp [fastQ, fastNL, Hf, PiF_apply_slow _ hk]
  · simp only [fastQ, fastNL, Hf, Pi.add_apply, Pi.neg_apply, PiF_apply_fast _ hk, e]
    abel

/-- `NQp = NFp + Hf`. -/
theorem NQp_eq (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    NQp r g y u = NFp r g y u + Hf r g y u := by
  rw [NQp, NFp, fastQ_eq, add_right_comm]

private lemma cancel_two {A : Type*} [AddCommGroup A] (a c : A) : -(a + a + c) + (a + a) = -c := by
  abel

/-- **`N_F` without the filter is `−Π_F Q(F, F)`**: the mixed term is `𝓛F`. -/
theorem NQp_pure (hx : Adm 2 (actual r g y u)) :
    NQp r g y u = -PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u)) := by
  funext k
  have e := congrFun (PiF_Qphase_eq (r * u) hx) k
  by_cases hk : k 2 = 0
  · simp [NQp, fastQ, Lop, PiF_apply_slow _ hk]
  · have e2 : Lop (r * u) (Sp r g y u) (Fp r g y u) k =
        Qphase (r * u) (PiS (actual r g y u)) (PiF (actual r g y u)) k +
          Qphase (r * u) (PiS (actual r g y u)) (PiF (actual r g y u)) k := by
      simp only [Lop, Pi.smul_apply, PiF_apply_fast _ hk, two_smul, Sp, Fp]
    simp only [Pi.add_apply, PiF_apply_fast _ hk] at e
    have e3 : NQp r g y u k = -(PiF (Qphase (r * u) (actual r g y u) (actual r g y u)) k) +
        Lop (r * u) (Sp r g y u) (Fp r g y u) k := rfl
    have e4 : (-PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u))) k =
        -Qphase (r * u) (PiF (actual r g y u)) (PiF (actual r g y u)) k := by
      rw [Pi.neg_apply, PiF_apply_fast _ hk]
      rfl
    rw [e3, e2, PiF_apply_fast _ hk, e, e4]
    exact cancel_two (A := V3) _ _

/-- **The two directions of the remainder**: `fastQ = −𝓛F − Π_F Q(F, F)`. -/
theorem fastQ_pure (hx : Adm 2 (actual r g y u)) :
    fastQ r g y u = -Lop (r * u) (Sp r g y u) (Fp r g y u) +
      -PiF (Qphase (r * u) (Fp r g y u) (Fp r g y u)) := by
  rw [← NQp_pure hx, NQp]
  abel

/-- At an `H³` time, every direction of the right sides is a fast `H²` field. -/
theorem link_facts (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u)) :
    MZ 2 (fastNL r g y u) ∧ PiF (fastNL r g y u) = fastNL r g y u ∧ MZ 2 (Hf r g y u) ∧
      MZ 2 (fastQ r g y u) ∧ PiF (fastQ r g y u) = fastQ r g y u := by
  have hx := actual_adm h hu huT
  have hx3 : MZ 3 (actual r g y u) := by
    refine ⟨?_, hx.mean⟩
    rw [← PiS_add_PiF (actual r g y u)]
    exact hS3.add hF3
  have hQ := (Qm_two_le (phaseM_bdd (r * u)) hx3 hx3).1
  have hQF : MZ 2 (fastQ r g y u) := ⟨hQ.PiF.neg, by simp [fastQ, PiF]⟩
  have hH2 : MZ 2 (Hf r g y u) :=
    ⟨(hnorm_two_Hpsi_J h hr hu huT hF3 hS3).1.PiF, (Hf_facts h hu huT).2.2⟩
  have e : fastNL r g y u = fastQ r g y u - Hf r g y u := eq_sub_of_add_eq (fastQ_eq r g y u).symm
  have hN : MZ 2 (fastNL r g y u) := by
    rw [e]
    exact ⟨hQF.inH.sub hH2.inH, by simp [hQF.mean, hH2.mean]⟩
  have hNF := PiF_fastNL (r := r) (g := g) (y := y) u
  refine ⟨hN, hNF, hH2, hQF, ?_⟩
  rw [fastQ_eq, PiF_add_f, hNF, PiF_Hf]

/-! ### Additivity at a fixed time -/

section Fixed

variable {s : ℕ} {τ : ℝ} {S F A B : Field}

private lemma l2_of_MZ {c : Field} (hc : MZ 2 c) : Summable fun k => ‖c k‖ ^ 2 :=
  summable_norm_sq_of_inH (hc.inH.mono (by norm_num))

/-- The two slots of `X₁` are additive in the direction. -/
theorem X1_slots_add (hs : s = 1 ∨ s = 2) (hS : MZ 2 S) (hF : MZ 2 F) (hF3 : InH 3 F) (hA : MZ 2 A)
    (hB : MZ 2 B) :
    pair s F (X1op r τ S (A + B)) = pair s F (X1op r τ S A) + pair s F (X1op r τ S B) ∧
      pair s (A + B) (X1op r τ S F) = pair s A (X1op r τ S F) + pair s B (X1op r τ S F) := by
  have hsl : ((s : ℕ) : ℝ) - 1 ≤ 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsu : ((s : ℕ) : ℝ) + 1 ≤ 3 := by rcases hs with rfl | rfl <;> norm_num
  have hs2 : ((s : ℕ) : ℝ) - 1 ≤ 2 := by linarith
  have e : X1op r τ S (A + B) = X1op r τ S A + X1op r τ S B :=
    Qm_add_right_l2 (metM_bdd r τ) (l2_of_MZ hS) (l2_of_MZ hA) (l2_of_MZ hB)
  have i1 : InH 1 (X1op r τ S A) :=
    inH_one_X1op r τ ((l1B_nrm hS.inH).conv_l2 (l2B_nrm (l2_of_MZ hA)))
  have i2 : InH 1 (X1op r τ S B) :=
    inH_one_X1op r τ ((l1B_nrm hS.inH).conv_l2 (l2B_nrm (l2_of_MZ hB)))
  have i3 := inH_three_X1op r τ hS hF
  refine ⟨?_, pair_add_left' (hA.inH.mono hs2) (hB.inH.mono hs2) (i3.mono hsu)⟩
  rw [e]
  exact pair_add (hF3.mono hsu) (i1.mono hsl) (i2.mono hsl)

/-- **The native differential is additive in the direction.** -/
theorem cubicD_add {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ)
    {F A B : Field} (hF : MZ 3 F) (hA : MZ 2 A) (hB : MZ 2 B) :
    cubicD j ε r τ F (A + B) = cubicD j ε r τ F A + cubicD j ε r τ F B := by
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  have hF1 : MZ 1 F := hF.mono' (by norm_num)
  have hA' : MZ 2 (PiF A) := hA.PiF'
  have hB' : MZ 2 (PiF B) := hB.PiF'
  have hA1 : MZ 1 (PiF A) := hA'.mono' (by norm_num)
  have hB1 : MZ 1 (PiF B) := hB'.mono' (by norm_num)
  have hm := corrM_gain ε r τ hε
  have hb := corrM_bdd hε r τ
  have hsl : ((j : ℕ) : ℝ) - 1 ≤ 1 := by rcases hj with rfl | rfl <;> norm_num
  have hsu : ((j : ℕ) : ℝ) + 1 ≤ 3 := by rcases hj with rfl | rfl <;> norm_num
  have e0 : PiF (A + B) = PiF A + PiF B := PiF_add_f A B
  have e1 : corr ε r τ (PiF A + PiF B) F = corr ε r τ (PiF A) F + corr ε r τ (PiF B) F :=
    Qm_add_left_l2 hb (l2_of_MZ hA') (l2_of_MZ hB') (l2_of_MZ hF2)
  have e2 : corr ε r τ F (PiF A + PiF B) = corr ε r τ F (PiF A) + corr ε r τ F (PiF B) :=
    Qm_add_right_l2 hb (l2_of_MZ hF2) (l2_of_MZ hA') (l2_of_MZ hB')
  have a1 : InH 1 (corr ε r τ (PiF A) F) := (hnorm_one_gain_le hm hA1 hF1).1
  have a2 : InH 1 (corr ε r τ (PiF B) F) := (hnorm_one_gain_le hm hB1 hF1).1
  have a3 : InH 1 (corr ε r τ F (PiF A)) := (hnorm_one_gain_le hm hF1 hA1).1
  have a4 : InH 1 (corr ε r τ F (PiF B)) := (hnorm_one_gain_le hm hF1 hB1).1
  have a5 : InH 3 (corr ε r τ F F) := (hnorm_three_gain_le hm hF2 hF2).1
  have p1 := pair_add (hF.inH.mono hsu) (a1.mono hsl) (a2.mono hsl)
  have p2 := pair_add (hF.inH.mono hsu) (a3.mono hsl) (a4.mono hsl)
  have p3 := pair_add_left' (hA1.inH.mono hsl) (hB1.inH.mono hsl) (a5.mono hsu)
  unfold cubicD
  rw [e0, e1, e2, p1, p2, p3]
  ring

variable {f : Field}

lemma zOf_add'' (s : ℕ) (A B : Field) : zOf s (A + B) = zOf s A + zOf s B := by
  funext k
  simp only [zOf, Pi.add_apply, smul_add]

/-- `X₂` is additive on the test. -/
lemma X2Form_add_left (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {f g G₁ G₂ F : Field} (hf : MZ 2 f)
    (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g) (hG₁ : Summable fun k => ‖G₁ k‖ ^ 2)
    (hG₂ : Summable fun k => ‖G₂ k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) :
    X2Form 1 s r τ f g (G₁ + G₂) F = X2Form 1 s r τ f g G₁ F + X2Form 1 s r τ f g G₂ F := by
  simp only [X2Form_one, Pi.add_apply, inner_add_left]
  exact (X2_summable hs hr τ hf hf' hg hg' hG₁ hF hF').tsum_add
    (X2_summable hs hr τ hf hf' hg hg' hG₂ hF hF')

/-- `Z` is additive on the test. -/
lemma ZForm_add_left (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {f g G₁ G₂ F : Field} (hf : MZ 2 f)
    (hf' : PiS f = f) (hg : MZ 2 g) (hg' : PiS g = g) (hG₁ : Summable fun k => ‖G₁ k‖ ^ 2)
    (hG₂ : Summable fun k => ‖G₂ k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) :
    ZForm 1 s r τ f g (G₁ + G₂) F = ZForm 1 s r τ f g G₁ F + ZForm 1 s r τ f g G₂ F := by
  simp only [ZForm_one, Pi.add_apply, inner_add_left]
  exact (Z_summable hs hr τ hf hf' hg hg' hG₁ hF hF').tsum_add
    (Z_summable hs hr τ hf hf' hg hg' hG₂ hF hF')

private lemma l2_zOf_of {s : ℕ} (hs : s = 1 ∨ s = 2) {c : Field} (hc : MZ 2 c) :
    Summable fun k => ‖zOf s c k‖ ^ 2 := by
  have h2 : ((s : ℕ) : ℝ) ≤ 2 := by rcases hs with rfl | rfl <;> norm_num
  exact (l2_zOf (hc.inH.mono h2) hc.mean).1

/-- The two slots of `X₂` are additive in the direction. -/
theorem X2_slots_add (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hS : MZ 2 S) (hS' : PiS S = S)
    (hF : MZ 2 F) (hF' : PiF F = F) (hA : MZ 2 A) (hA' : PiF A = A) (hB : MZ 2 B)
    (hB' : PiF B = B) :
    X2Form 1 s r τ S S (zOf s (A + B)) (zOf s F) =
        X2Form 1 s r τ S S (zOf s A) (zOf s F) + X2Form 1 s r τ S S (zOf s B) (zOf s F) ∧
      X2Form 1 s r τ S S (zOf s F) (zOf s (A + B)) =
        X2Form 1 s r τ S S (zOf s F) (zOf s A) + X2Form 1 s r τ S S (zOf s F) (zOf s B) := by
  rw [zOf_add'']
  exact ⟨X2Form_add_left hs hr τ hS hS' hS hS' (l2_zOf_of hs hA) (l2_zOf_of hs hB)
      (l2_zOf_of hs hF) (Fam.PiF_zOf hF'),
    X2Form_add hs hr τ hS hS' hS hS' (l2_zOf_of hs hF) (l2_zOf_of hs hA) (Fam.PiF_zOf hA')
      (l2_zOf_of hs hB) (Fam.PiF_zOf hB')⟩

/-- The two slots of `Z` are additive in the direction. -/
theorem Z_slots_add (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hS : MZ 2 S) (hS' : PiS S = S)
    (hF : MZ 2 F) (hF' : PiF F = F) (hA : MZ 2 A) (hA' : PiF A = A) (hB : MZ 2 B)
    (hB' : PiF B = B) :
    ZForm 1 s r τ S S (zOf s (A + B)) (zOf s F) =
        ZForm 1 s r τ S S (zOf s A) (zOf s F) + ZForm 1 s r τ S S (zOf s B) (zOf s F) ∧
      ZForm 1 s r τ S S (zOf s F) (zOf s (A + B)) =
        ZForm 1 s r τ S S (zOf s F) (zOf s A) + ZForm 1 s r τ S S (zOf s F) (zOf s B) := by
  rw [zOf_add'']
  exact ⟨ZForm_add_left hs hr τ hS hS' hS hS' (l2_zOf_of hs hA) (l2_zOf_of hs hB)
      (l2_zOf_of hs hF) (Fam.PiF_zOf hF'),
    ZForm_add hs hr τ hS hS' hS hS' (l2_zOf_of hs hF) (l2_zOf_of hs hA) (Fam.PiF_zOf hA')
      (l2_zOf_of hs hB) (Fam.PiF_zOf hB')⟩

end Fixed

/-! ### The right sides without the filter -/

/-- `coreRHS`, with `N_F` without the filter. -/
def coreQ (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  2 * (pair s (Fp r g y u) (X1op r (r * u) (hp r g y u) (Fp r g y u)) +
    pair s (Fp r g y u) (X1op r (r * u) (Sp r g y u) (NQp r g y u)) +
    pair s (NQp r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u)))

/-- `insJ`, with `fastNL` replaced by `fastQ` in the two fast slots.  The slow slots are kept. -/
def insQ (𝔉 : Fam) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (zOf s (fastQ r g y u)) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zOf s (fastQ r g y u)) +
    𝔉.form r (r * u) (slowNL r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (slowNL r g y u) (zp s r g y u) (zp s r g y u)

/-- **`joint1RHS` without the fast force.** -/
def joint1Q (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -pair 1 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) +
    coreQ 1 r g y u - cubicHeat r (r * u) (Fp r g y u) +
    cubicD 1 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) +
    1 / 2 * (insQ (famX2 1 r) 1 r g y u).re + 1 / 2 * (insQ (famZ 1 r) 1 r g y u).re

/-- **`joint2RHS` without the fast force.** -/
def joint2Q (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -pair 2 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) +
    coreQ 2 r g y u - cubicHeat2 r (r * u) (Fp r g y u) +
    cubicD 2 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) +
    1 / 2 * (insQ (famX2 2 r) 2 r g y u).re + 1 / 2 * (insQ (famZ 2 r) 2 r g y u).re

/-- **The part of the right sides that carries `Hf`**, with its signs. -/
def forceS (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -pair s (Fp r g y u) (Hpsi r g y u) - cubicD s (-1) r (r * u) (Fp r g y u) (Hf r g y u) -
    (2 * pair s (Fp r g y u) (X1op r (r * u) (Sp r g y u) (Hf r g y u)) +
      2 * pair s (Hf r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u))) -
    1 / 2 * (X2Form 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zOf s (Hf r g y u)) (zp s r g y u) +
      X2Form 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zOf s (Hf r g y u))).re -
    1 / 2 * (ZForm 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zOf s (Hf r g y u)) (zp s r g y u) +
      ZForm 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zOf s (Hf r g y u))).re

private lemma force_triangle {a b c : ℝ} {x₁ x₂ x₃ x₄ : ℂ} :
    |-a - b - c - 1 / 2 * (x₁ + x₂).re - 1 / 2 * (x₃ + x₄).re| ≤
      |a| + |b| + |c| + ‖x₁‖ + ‖x₂‖ + ‖x₃‖ + ‖x₄‖ := by
  have h1 := abs_le.1 (Complex.abs_re_le_norm x₁)
  have h2 := abs_le.1 (Complex.abs_re_le_norm x₂)
  have h3 := abs_le.1 (Complex.abs_re_le_norm x₃)
  have h4 := abs_le.1 (Complex.abs_re_le_norm x₄)
  have n1 := norm_nonneg x₁
  have n2 := norm_nonneg x₂
  have n3 := norm_nonneg x₃
  have n4 := norm_nonneg x₄
  rw [Complex.add_re, Complex.add_re, abs_le]
  constructor <;> linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, le_abs_self a, le_abs_self b,
    le_abs_self c, neg_abs_le a, neg_abs_le b, neg_abs_le c, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
    h4.1, h4.2]

/-- **`forceS 1` is bounded by `force1`.** -/
theorem forceS_one_le (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    |forceS 1 r g y u| ≤ force1 r g y u := by
  unfold forceS force1
  simp only [Nat.cast_one]
  exact force_triangle

/-- **`forceS 2` is bounded by `force2`.** -/
theorem forceS_two_le (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    |forceS 2 r g y u| ≤ force2 r g y u := by
  unfold forceS force2
  simp only [Nat.cast_ofNat]
  exact force_triangle

/-! ### The link -/

/-- The three groups of the right side, at an `H³` time. -/
theorem link_slots {s : ℕ} (hs : s = 1 ∨ s = 2) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u))
    (hS3 : InH 3 (Sp r g y u)) :
    coreQ s r g y u = coreRHS s r g y u +
        (2 * pair s (Fp r g y u) (X1op r (r * u) (Sp r g y u) (Hf r g y u)) +
          2 * pair s (Hf r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u))) ∧
      cubicD s (-1) r (r * u) (Fp r g y u) (fastQ r g y u) =
        cubicD s (-1) r (r * u) (Fp r g y u) (fastNL r g y u) +
          cubicD s (-1) r (r * u) (Fp r g y u) (Hf r g y u) ∧
      insQ (famX2 s r) s r g y u = insJ (famX2 s r) s r g y u +
        (X2Form 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zOf s (Hf r g y u)) (zp s r g y u) +
          X2Form 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zOf s (Hf r g y u))) ∧
      insQ (famZ s r) s r g y u = insJ (famZ s r) s r g y u +
        (ZForm 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zOf s (Hf r g y u)) (zp s r g y u) +
          ZForm 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zOf s (Hf r g y u))) := by
  have hx := actual_adm h hu huT
  have hSA : Adm 2 (Sp r g y u) := hx.PiS
  have hFA : Adm 2 (Fp r g y u) := hx.PiF
  have hS' := Fam.PiS_Sp r g y u
  have hF' := Fam.PiF_Fp r g y u
  have hSM : MZ 3 (Sp r g y u) := ⟨hS3, hSA.mean⟩
  have hFM : MZ 3 (Fp r g y u) := ⟨hF3, hFA.mean⟩
  obtain ⟨hN, hN', hH, hQ, hQ'⟩ := link_facts h hr hu huT hF3 hS3
  have hH' := PiF_Hf r g y u
  have hL := mz_Lop (r * u) hSM hFM
  have hNF : MZ 2 (NFp r g y u) := ⟨hN.inH.add hL.inH, by
    change fastNL r g y u 0 + Lop (r * u) (Sp r g y u) (Fp r g y u) 0 = 0
    rw [hN.mean, hL.mean, add_zero]⟩
  have hX := X1_slots_add (r := r) (τ := r * u) hs hSA.mz hFA.mz hF3 hNF hH
  have hc := cubicD_add (j := s) (ε := -1) hs (Or.inr rfl) r (r * u) hFM hN hH
  have hA := X2_slots_add hs hr (r * u) hSA.mz hS' hFA.mz hF' hN hN' hH hH'
  have hZ := Z_slots_add hs hr (r * u) hSA.mz hS' hFA.mz hF' hN hN' hH hH'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold coreQ coreRHS
    rw [NQp_eq, hX.1, hX.2]
    ring
  · rw [fastQ_eq]
    exact hc
  · simp only [insQ, insJ, famX2_form, Nzp, zp, fastQ_eq]
    rw [hA.1, hA.2]
    ring
  · simp only [insQ, insJ, famZ_form, Nzp, zp, fastQ_eq]
    rw [hZ.1, hZ.2]
    ring

/-- **The link at weight one**: the part of `joint1RHS` that carries `Hf` is `forceS 1`, at an
`H³` time, and the rest is `joint1Q`, with no fast force. -/
theorem joint1RHS_split (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u)) :
    joint1RHS r g y u = joint1Q r g y u + forceS 1 r g y u := by
  obtain ⟨e1, e2, e3, e4⟩ := link_slots (s := 1) (Or.inl rfl) h hr hu huT hF3 hS3
  have e1' := congrArg Complex.re e3
  have e2' := congrArg Complex.re e4
  rw [Complex.add_re] at e1' e2'
  unfold joint1RHS joint1Q forceS
  rw [e1, e2, e1', e2']
  simp only [Nat.cast_one]
  ring

/-- **The link at weight two**: the part of `joint2RHS` that carries `Hf` is `forceS 2`, at an
`H³` time, and the rest is `joint2Q`, with no fast force. -/
theorem joint2RHS_split (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u)) :
    joint2RHS r g y u = joint2Q r g y u + forceS 2 r g y u := by
  obtain ⟨e1, e2, e3, e4⟩ := link_slots (s := 2) (Or.inr rfl) h hr hu huT hF3 hS3
  have e1' := congrArg Complex.re e3
  have e2' := congrArg Complex.re e4
  rw [Complex.add_re] at e1' e2'
  unfold joint2RHS joint2Q forceS
  rw [e1, e2, e1', e2']
  simp only [Nat.cast_ofNat]
  ring

/-- **The link at almost every time.** -/
theorem ae_joint_split (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    ∀ᵐ u ∂(volume.restrict (Icc a b)),
      joint1RHS r g y u = joint1Q r g y u + forceS 1 r g y u ∧
        joint2RHS r g y u = joint2Q r g y u + forceS 2 r g y u := by
  filter_upwards [ae_inH3_split h ha hab hb, ae_restrict_mem measurableSet_Icc] with u hu hm
  have hu0 := ha.trans hm.1
  have huT := lt_lifespan hm.2 hb
  exact ⟨joint1RHS_split h hr hu0 huT hu.1 hu.2, joint2RHS_split h hr hu0 huT hu.1 hu.2⟩

/-! ### On a joint piece -/

variable {M C ex R D : ℝ} {q : Caps → ℝ} {near : Caps → ℝ → Prop}
  {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} {caps : Caps} {s t : ℝ}

/-- **`joint1RHS` on a joint piece**: the fast force is `N_f b_F + f_f` (`force1_joint`). -/
theorem joint1_force_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hp' : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (hD : 1 ≤ D)
    (hq : force1Q φ D M caps ≤ q caps) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), joint1RHS r g y u ≤ joint1Q r g y u +
      (2 * hBd φ r g y u * fastNorm 2 r g y u + 24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) := by
  obtain ⟨h1, -, -⟩ := force1_joint h hp' hD hq
  filter_upwards [ae_joint_split h hr hp'.hs hp'.hst hp'.ht, ae_restrict_mem measurableSet_Icc]
    with u hu hm
  rw [hu.1]
  have h2 := (le_abs_self _).trans ((forceS_one_le r g y u).trans (h1 u hm))
  linarith

/-- **`joint2RHS` on a joint piece**: the fast force is `c_F²/64 + 16 GF` (`force2_joint`). -/
theorem joint2_force_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hp' : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (h0 : 0 ≤ C * ex)
    (hR : 0 ≤ R) (hD : 1 ≤ D) (hq : force2Q φ D M C ex R caps ≤ q caps) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), joint2RHS r g y u ≤ joint2Q r g y u +
      (1 / 64 * fastNorm 3 r g y u ^ 2 + 16 * GF φ D M r g y caps u) := by
  obtain ⟨-, -, h1⟩ := force2_joint h hp' h0 hR hD hq
  filter_upwards [h1, ae_joint_split h hr hp'.hs hp'.hst hp'.ht] with u hb hu
  rw [hu.2]
  have h2 := (le_abs_self _).trans ((forceS_two_le r g y u).trans hb)
  linarith

end OVNS.Quant.Metric

end
