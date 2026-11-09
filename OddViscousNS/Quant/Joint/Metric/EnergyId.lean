import OddViscousNS.Quant.Joint.Metric.Q3Rhs
import OddViscousNS.Quant.Joint.Quartic.Main

/-!
# The corrected energies and their identities (nodes N14, N15)

`JOINT_ASSEMBLY_V4.md` §3: `E_s = e_s + E_s⁰ + C_{3,s} + C_{4,s}`, `W_s = 2 E_s`.  `C_{3,s}` is the real
part of the value of the directed form `O`: the Hermitian operator `Q = O + O*` of the source has
`C_{3,s} = ½ Re⟨z, Q z⟩ = Re⟨z, O z⟩`, and so the derivative of `C_{3,s}` is `Fam3.rhs` with coefficient
one in every slot.

* `En1`, `En2`: the energies; `T1`, `T2`: the right sides.
* `En1_identity`, `En2_identity`.
* `bracket_le`: the bracket of the right side, against the group of the last edge, whose source
  cancels `Re⟨z, T_sep z⟩`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open OVNS.Quant.Quartic
open OVNS.Quant.H2 (h2Energy h2Energy_identity)

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {D : ℝ}

/-- **The corrected `H¹` energy** `E₁ = e₁ + E₁⁰ + C_{3,1} + C_{4,1}`. -/
def En1 (D r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  h1Energy r g y u + 1 / 2 * corrJ 1 r g y u + ((famQ 1 r D).val 1 r g y u).re + C4 1 r g y u

/-- **The corrected `H²` energy** `W₂ = 2 E₂`. -/
def En2 (D r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  h2Energy r g y u + corrJ 2 r g y u + 2 * ((famQ 2 r D).val 2 r g y u).re + 2 * C4 2 r g y u

/-- The right side of `E₁`. -/
def T1 (D r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  joint1RHS r g y u + ((famQ 1 r D).rhs 1 r g y u).re + (-J4 1 r g y u + Rem4 1 r g y u)

/-- The right side of `E₂ = W₂/2`. -/
def T2 (D r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  joint2RHS r g y u + ((famQ 2 r D).rhs 2 r g y u).re + (-J4 2 r g y u + Rem4 2 r g y u)

/-- The third correction in the identities. -/
lemma Q3_re_identity {s : ℕ} (hs : s = 1 ∨ s = 2) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (D : ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (fun u => ((famQ s r D).rhs s r g y u).re) volume a b ∧
      ((famQ s r D).val s r g y b).re - ((famQ s r D).val s r g y a).re =
        ∫ u in a..b, ((famQ s r D).rhs s r g y u).re := by
  obtain ⟨hI, hE⟩ := Q3_identity hs h hr D ha hab hb
  have i1 : ∫ u in a..b, ((famQ s r D).rhs s r g y u).re =
      (∫ u in a..b, (famQ s r D).rhs s r g y u).re := Complex.reCLM.intervalIntegral_comp_comm hI
  refine ⟨⟨hI.1.re, hI.2.re⟩, ?_⟩
  rw [i1, ← hE, Complex.sub_re]

/-- **The identity of `E₁`.** -/
theorem En1_identity (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (D : ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (T1 D r g y) volume a b ∧
      En1 D r g y b - En1 D r g y a + (∫ u in a..b, fastNorm 2 r g y u ^ 2) =
        ∫ u in a..b, T1 D r g y u := by
  obtain ⟨i1, e1⟩ := joint_h1 h hr ha hab hb
  obtain ⟨i2, e2⟩ := Q3_re_identity (s := 1) (Or.inl rfl) h hr D ha hab hb
  obtain ⟨i3, e3⟩ := C4_identity_one h hr ha hab hb
  have hI : IntervalIntegrable (T1 D r g y) volume a b := (i1.add i2).add i3
  refine ⟨hI, ?_⟩
  have e : ∫ u in a..b, T1 D r g y u = (∫ u in a..b, joint1RHS r g y u) +
      (∫ u in a..b, ((famQ 1 r D).rhs 1 r g y u).re) +
      ∫ u in a..b, (-J4 1 r g y u + Rem4 1 r g y u) := by
    rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_add (i1.add i2) i3]
    rfl
  rw [e, ← e1, ← e2, ← e3]
  simp only [En1]
  ring

/-- **The identity of `W₂`.** -/
theorem En2_identity (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (D : ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (T2 D r g y) volume a b ∧
      1 / 2 * En2 D r g y b - 1 / 2 * En2 D r g y a + (∫ u in a..b, fastNorm 3 r g y u ^ 2) =
        ∫ u in a..b, T2 D r g y u := by
  obtain ⟨i1, e1⟩ := joint_h2 h hr ha hab hb
  obtain ⟨i2, e2⟩ := Q3_re_identity (s := 2) (Or.inr rfl) h hr D ha hab hb
  obtain ⟨i3, e3⟩ := C4_identity_two h hr ha hab hb
  have hI : IntervalIntegrable (T2 D r g y) volume a b := (i1.add i2).add i3
  refine ⟨hI, ?_⟩
  have e : ∫ u in a..b, T2 D r g y u = (∫ u in a..b, joint2RHS r g y u) +
      (∫ u in a..b, ((famQ 2 r D).rhs 2 r g y u).re) +
      ∫ u in a..b, (-J4 2 r g y u + Rem4 2 r g y u) := by
    rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_add (i1.add i2) i3]
    rfl
  rw [e, ← e1, ← e2, ← e3]
  simp only [En2]
  ring

/-! ### The bracket -/

lemma X2Form_neg_left (μ₀ : I3 → ℂ) (s : ℕ) (r τ : ℝ) (f g G F : Field) :
    X2Form μ₀ s r τ f g (-G) F = -X2Form μ₀ s r τ f g G F := by
  simp only [X2Form, Pi.neg_apply, inner_neg_left, mul_neg]
  exact tsum_neg

lemma X2Form_neg_right (μ₀ : I3 → ℂ) (s : ℕ) (r τ : ℝ) (f g G F : Field) :
    X2Form μ₀ s r τ f g G (-F) = -X2Form μ₀ s r τ f g G F := by
  simp only [X2Form, Pi.neg_apply, map_neg, inner_neg_right, mul_neg]
  exact tsum_neg

lemma ZForm_neg_left (μ₀ : I3 → ℂ) (s : ℕ) (r τ : ℝ) (f g G F : Field) :
    ZForm μ₀ s r τ f g (-G) F = -ZForm μ₀ s r τ f g G F := by
  simp only [ZForm, Pi.neg_apply, inner_neg_left, mul_neg]
  exact tsum_neg

lemma ZForm_neg_right (μ₀ : I3 → ℂ) (s : ℕ) (r τ : ℝ) (f g G F : Field) :
    ZForm μ₀ s r τ f g G (-F) = -ZForm μ₀ s r τ f g G F := by
  simp only [ZForm, Pi.neg_apply, map_neg, inner_neg_right, mul_neg]
  exact tsum_neg

lemma zOf_mLp (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    zOf s (mLp r g y u) = -zOf s (Lop (r * u) (Sp r g y u) (Fp r g y u)) := by
  funext k
  simp only [zOf, mLp, Pi.neg_apply, smul_neg]

/-- The real part of the bracket of a family. -/
lemma insT_X2_re (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ)
    (hS : IsReal (Sp r g y u)) :
    1 / 2 * (insT (famX2 s r) s r g y u).re = -(X2Form 1 s r (r * u) (Sp r g y u) (Sp r g y u)
      (zp s r g y u) (zOf s (Lop (r * u) (Sp r g y u) (Fp r g y u)))).re -
        1 / 2 * (hBY (famX2 s r) s r g y u).re := by
  simp only [insT, famX2_form, zOf_mLp, X2Form_neg_left, X2Form_neg_right]
  rw [X2Form_conj s r (r * u) hS hS (zOf s (Lop (r * u) (Sp r g y u) (Fp r g y u))) (zp s r g y u)]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.conj_re]
  ring

lemma insT_Z_re (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ)
    (hS : IsReal (Sp r g y u)) :
    1 / 2 * (insT (famZ s r) s r g y u).re = -(ZForm 1 s r (r * u) (Sp r g y u) (Sp r g y u)
      (zp s r g y u) (zOf s (Lop (r * u) (Sp r g y u) (Fp r g y u)))).re -
        1 / 2 * (hBY (famZ s r) s r g y u).re := by
  simp only [insT, famZ_form, zOf_mLp, ZForm_neg_left, ZForm_neg_right]
  rw [ZForm_conj s r (r * u) hS hS (zOf s (Lop (r * u) (Sp r g y u) (Fp r g y u))) (zp s r g y u)]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.conj_re]
  ring

/-- The form `⟨z, Y 𝓛 z⟩ − source`. -/
def grp (s : ℕ) (D r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  X2Form 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u)
      (zOf s (Lop (r * u) (Sp r g y u) (Fp r g y u))) +
    ZForm 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u)
      (zOf s (Lop (r * u) (Sp r g y u) (Fp r g y u))) -
    (famQ s r D).src (r * u) (Sp r g y u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u)

/-- The exterior slots of `O`. -/
def extQ (s : ℕ) (D r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  ‖(famQ s r D).form r (r * u) (Sp r g y u) (Sp r g y u) (Sp r g y u) (Nzp s r g y u)
      (zp s r g y u)‖ +
    ‖(famQ s r D).form r (r * u) (Sp r g y u) (Sp r g y u) (Sp r g y u) (zp s r g y u)
      (Nzp s r g y u)‖

/-- The slow slots of `O`. -/
def slotQ (s : ℕ) (D r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  ‖(famQ s r D).form r (r * u) (slowNL r g y u) (Sp r g y u) (Sp r g y u) (zp s r g y u)
      (zp s r g y u)‖ +
    ‖(famQ s r D).form r (r * u) (Sp r g y u) (slowNL r g y u) (Sp r g y u) (zp s r g y u)
      (zp s r g y u)‖ +
    ‖(famQ s r D).form r (r * u) (Sp r g y u) (Sp r g y u) (slowNL r g y u) (zp s r g y u)
      (zp s r g y u)‖

/-- **The bracket**: `½⟨z, −T_s z⟩ + (C_{3,s})' = −Re(group) − ½ D_S Y[B] + extQ + slotQ`.  The source of
`O` cancels the high last edge of the group: the coefficients are exact. -/
theorem bracket_le (s : ℕ) (D r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ)
    (hS : IsReal (Sp r g y u)) :
    1 / 2 * (insT (famX2 s r) s r g y u).re + 1 / 2 * (insT (famZ s r) s r g y u).re +
        ((famQ s r D).rhs s r g y u).re ≤
      ‖grp s D r g y u‖ + 1 / 2 * ‖hBY (famX2 s r) s r g y u‖ +
        1 / 2 * ‖hBY (famZ s r) s r g y u‖ + extQ s D r g y u + slotQ s D r g y u := by
  rw [insT_X2_re s r g y u hS, insT_Z_re s r g y u hS]
  simp only [Fam3.rhs, grp, extQ, slotQ, Complex.add_re]
  have h1 := abs_le.1 (Complex.abs_re_le_norm (grp s D r g y u))
  simp only [grp, Complex.add_re, Complex.sub_re] at h1
  have h2 := abs_le.1 (Complex.abs_re_le_norm (hBY (famX2 s r) s r g y u))
  have h3 := abs_le.1 (Complex.abs_re_le_norm (hBY (famZ s r) s r g y u))
  have t := fun x : ℂ => abs_le.1 (Complex.abs_re_le_norm x)
  have t1 := t ((famQ s r D).form r (r * u) (Sp r g y u) (Sp r g y u) (Sp r g y u) (Nzp s r g y u)
      (zp s r g y u))
  have t2 := t ((famQ s r D).form r (r * u) (Sp r g y u) (Sp r g y u) (Sp r g y u) (zp s r g y u)
      (Nzp s r g y u))
  have t3 := t ((famQ s r D).form r (r * u) (slowNL r g y u) (Sp r g y u) (Sp r g y u)
      (zp s r g y u) (zp s r g y u))
  have t4 := t ((famQ s r D).form r (r * u) (Sp r g y u) (slowNL r g y u) (Sp r g y u)
      (zp s r g y u) (zp s r g y u))
  have t5 := t ((famQ s r D).form r (r * u) (Sp r g y u) (Sp r g y u) (slowNL r g y u)
      (zp s r g y u) (zp s r g y u))
  linarith [h1.1, h2.1, h3.1, t1.2, t2.2, t3.2, t4.2, t5.2]

end OVNS.Quant.Metric

end
