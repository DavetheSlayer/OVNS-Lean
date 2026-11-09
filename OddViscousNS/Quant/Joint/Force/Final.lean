import OddViscousNS.Quant.Joint.Force.Insert

/-!
# The right sides in four parts (step J5, node N12)

* `kapQ`, `staticQ`, `Pkap_le`: the threshold of the metric–`Q` insertion: `P_F K ≤ 2/η` at
  `η staticQ ≤ q`.
* `staticQ_le_rowStatic`, `deg_staticQ`: at `D = R`, `staticQ ≤ CsQ rowStatic`, degree `(1, 3)`.
* `metQ_joint`: `(15.2)` on a joint piece: a share `16 c₄/η`, `32 c₄/η` of the dissipation.
* `joint1T`, `joint2T`, `ae_joint_final`: at almost every time
  `joint_s RHS = joint_s T + metQ s + h0Part s + forceS s`.
* `joint1_final_le`, `joint2_final_le`: everything but `joint_s T` is paid, on a joint piece.

`joint₁T`, `joint₂T` keep the resonant `⟨AˢF, Q_res(F, F)⟩`, the cubic heat, the native differential
`cubicD (fastQ)`, and `½ ⟨z, Y (−𝓛)z⟩ + … − ½ ⟨z, D_S Y[B(S, S)] z⟩`: the bracket `−½⟨z, T_s z⟩` of
`(2.5)`.  Those are for N7–N11, N13.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (ae_inH3_split cubicHeat2)

noncomputable section

namespace OVNS.Quant.Metric

open JDeg

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}

/-! ### The threshold -/

/-- The operator norm of the metric at the caps. -/
def kapQ (r D M : ℝ) (caps : Caps) : ℝ :=
  2 ^ 8 * (1 + c4) * cp caps.BS / |r| + X2StC r D caps + CZ / |r| * M * cp caps.BS

lemma Kmet_le_kapQ {D M : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M) {S : Field} {caps : Caps}
    (hW : wiener S ≤ cp caps.WS) (hA : hnorm 1 S ≤ cp caps.AS) (hB : hnorm 2 S ≤ cp caps.BS) :
    Kmet r D M S ≤ kapQ r D M caps := by
  have h1 := X2St_le (r := r) hD hW hA hB
  have hC := CZ_nonneg
  have hc := c4_pos
  unfold Kmet kapQ
  gcongr

/-- The part of `P_F K` in `q⁻¹`. -/
def stA (D M : ℝ) (caps : Caps) : ℝ :=
  cp caps.PF * (2 ^ 8 * (1 + c4) * cp caps.BS +
    Cst * ((1 + Real.sqrt (1 + Real.log D)) * cp caps.AS ^ 2 +
      2 * (cp caps.AS * cp caps.WS) + cp caps.BS ^ 2 / D) + CZ * M * cp caps.BS)

/-- The part of `P_F K` in `q⁻²`. -/
def stB (D : ℝ) (caps : Caps) : ℝ := cp caps.PF * (Cst * (D * (cp caps.AS * cp caps.BS)))

/-- **The threshold of the metric–`Q` insertion.** -/
def staticQ (D M : ℝ) (caps : Caps) : ℝ := stA D M caps + rootQ 2 (stB D caps)

lemma stA_nonneg {D M : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (caps : Caps) : 0 ≤ stA D M caps := by
  have := c4_pos
  have := cp_nonneg caps.PF
  have := cp_nonneg caps.BS
  have := cp_nonneg caps.AS
  have := cp_nonneg caps.WS
  have := Cst_nonneg
  have := CZ_nonneg
  have := Real.sqrt_nonneg (1 + Real.log D)
  unfold stA
  positivity

lemma stB_nonneg {D : ℝ} (hD : 0 ≤ D) (caps : Caps) : 0 ≤ stB D caps := by
  have := cp_nonneg caps.PF
  have := cp_nonneg caps.BS
  have := cp_nonneg caps.AS
  have := Cst_nonneg
  unfold stB
  positivity

lemma Pkap_eq (r D M : ℝ) (caps : Caps) :
    cp caps.PF * kapQ r D M caps = stA D M caps / |r| + stB D caps / |r| ^ 2 := by
  unfold kapQ X2StC stA stB
  ring

/-- **`η staticQ ≤ q` gives `P_F K ≤ 2/η`.** -/
theorem Pkap_le {D M η : ℝ} {caps : Caps} (hD : 0 ≤ D) (hM : 0 ≤ M) (hη : 1 ≤ η)
    (hq : η * staticQ D M caps ≤ |r|) (hr : 0 < |r|) :
    cp caps.PF * kapQ r D M caps ≤ 2 / η := by
  have hη0 : 0 < η := by linarith
  have hA := stA_nonneg hD hM caps
  have hB := stB_nonneg hD caps
  have hR := rootQ_nonneg 2 hB
  unfold staticQ at hq
  have h1 : η * stA D M caps ≤ |r| := by nlinarith only [hq, hR, hη0]
  have h2 : η * rootQ 2 (stB D caps) ≤ |r| := by nlinarith only [hq, hA, hη0]
  have h3 : stB D caps ≤ rootQ 2 (stB D caps) ^ 2 := by
    have := le_rpow_of_rootQ (e := 2) (by norm_num) hB le_rfl
    rwa [Real.rpow_two] at this
  have t1 : stA D M caps / |r| ≤ 1 / η := by
    rw [div_le_div_iff₀ hr hη0]
    linarith
  have t2 : stB D caps / |r| ^ 2 ≤ 1 / η := by
    have h4 : (η * rootQ 2 (stB D caps)) ^ 2 ≤ |r| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have h5 : η ^ 2 * stB D caps ≤ |r| ^ 2 := by
      have := mul_le_mul_of_nonneg_left h3 (sq_nonneg η)
      nlinarith only [this, h4]
    rw [div_le_div_iff₀ (by positivity) hη0]
    have h6 : η * stB D caps ≤ η ^ 2 * stB D caps := by
      have := mul_le_mul_of_nonneg_right (by nlinarith only [hη] : η ≤ η ^ 2) hB
      linarith
    linarith
  rw [Pkap_eq]
  have e : (2 : ℝ) / η = 1 / η + 1 / η := by ring
  rw [e]
  exact add_le_add t1 t2

/-- The constant of the absorption by `rowStatic`. -/
def CsQ : ℝ := 2 ^ 8 * (1 + c4) + CZ + 2 * Cst + Real.sqrt Cst

/-- **`rowStatic` absorbs the insertion**, term by term, at the static `D = R`. -/
theorem staticQ_le_rowStatic {CS cS R : ℝ} {caps : Caps} (hR : 1 ≤ R)
    (hM : 1 ≤ CS * Ex cS R * R) :
    staticQ R (CS * Ex cS R * R) caps ≤ CsQ * rowStatic CS cS R caps := by
  set P := cp caps.PF with hP
  set A := cp caps.AS with hA
  set W := cp caps.WS with hW
  set B := cp caps.BS with hB
  set M := CS * Ex cS R * R with hMd
  set L := 1 + Real.log R with hL
  have hP0 : 0 ≤ P := cp_nonneg _
  have hA0 : 0 ≤ A := cp_nonneg _
  have hW0 : 0 ≤ W := cp_nonneg _
  have hB0 : 0 ≤ B := cp_nonneg _
  have hR0 : 0 < R := by linarith
  have hL1 : 1 ≤ L := by
    have := Real.log_nonneg hR
    linarith
  have hc := c4_pos
  have hCs := Cst_nonneg
  have hCZ := CZ_nonneg
  have hs0 := Real.sqrt_nonneg Cst
  have hsL : Real.sqrt L ≤ L := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith only [hL1]
  have hsL0 := Real.sqrt_nonneg L
  have eR : B ^ 2 / R = B ^ 2 * R ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  set T1 := P * (L * A ^ 2 + A * W + B ^ 2 * R ^ (-1 : ℝ)) with hT1
  set T2 := P * M * B with hT2
  set T3 := Real.sqrt (P * R * A * B) with hT3
  have hRm : 0 ≤ R ^ (-1 : ℝ) := Real.rpow_nonneg hR0.le _
  have hT10 : 0 ≤ T1 := by positivity
  have hT20 : 0 ≤ T2 := by positivity
  have hT30 : 0 ≤ T3 := Real.sqrt_nonneg _
  have e0 : rowStatic CS cS R caps = T1 + T2 + T3 + B := rfl
  have e1 : rootQ 2 (stB R caps) = Real.sqrt Cst * T3 := by
    have e2 : stB R caps = Cst * (P * R * A * B) := by
      unfold stB
      ring
    rw [e2, rootQ, ← Real.sqrt_eq_rpow, Real.sqrt_mul hCs]
  have h1 : stA R M caps ≤ (2 ^ 8 * (1 + c4) + CZ) * T2 + 2 * Cst * T1 := by
    have t1 : P * B ≤ P * M * B := by
      have : 0 ≤ P * B := by positivity
      nlinarith only [this, hM]
    have t2 : (1 + Real.sqrt L) * A ^ 2 ≤ 2 * L * A ^ 2 := by
      have : 0 ≤ A ^ 2 := by positivity
      nlinarith only [this, hsL, hL1]
    have t3 : 0 ≤ B ^ 2 * R ^ (-1 : ℝ) := by positivity
    have t4 : 0 ≤ P * Cst * (L * A ^ 2 + A * W + B ^ 2 * R ^ (-1 : ℝ)) := by positivity
    have t5 := mul_le_mul_of_nonneg_left t2 (mul_nonneg hP0 hCs)
    have t6 : 0 ≤ P * Cst * (A * W) := by positivity
    have t7 : 0 ≤ P * Cst * (B ^ 2 * R ^ (-1 : ℝ)) := by positivity
    have t8 := mul_le_mul_of_nonneg_left t1 (by positivity : 0 ≤ 2 ^ 8 * (1 + c4))
    unfold stA
    rw [eR, ← hP, ← hA, ← hW, ← hB, ← hL]
    simp only [hT1, hT2]
    nlinarith only [t5, t6, t7, t8]
  have h2 : 0 ≤ (2 ^ 8 * (1 + c4) + CZ + Real.sqrt Cst) * T1 + (2 * Cst + Real.sqrt Cst) * T2 +
      (2 ^ 8 * (1 + c4) + CZ + 2 * Cst) * T3 +
        (2 ^ 8 * (1 + c4) + CZ + 2 * Cst + Real.sqrt Cst) * B := by positivity
  rw [e0]
  unfold staticQ CsQ
  rw [e1]
  nlinarith only [h1, h2]

/-- **The degree of the threshold of the insertion**: tied at `U R³`. -/
theorem deg_staticQ {C e : ℝ} (hC : 0 ≤ C) :
    JDeg 1 3 fun _ R caps ↦ staticQ R (C * Ex e R * R) caps := by
  have hL : JDeg 0 0 fun _ R _ ↦ 1 + Real.sqrt (1 + Real.log R) :=
    (const zero_le_one).add (logR.sqrt.up 0 0)
  have hB2 : JDeg 0 3 fun _ R caps ↦ cp caps.BS ^ 2 / R := by
    refine (((BS.pow 2).mul (Rpow (-1))).up 0 3).congr' fun _ X R hdom _ ↦ ?_
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hc : (0 : ℝ) ≤ 2 ^ 8 * (1 + c4) := by
    have := c4_pos
    positivity
  have h1 := (BS.const_mul hc).up 0 3
  have hS := (((hL.mul (AS.pow 2)).up 0 3).add
    (((AS.mul WS).const_mul (by norm_num : (0 : ℝ) ≤ 2)).up 0 3)).add hB2
  have h2 := (hS.const_mul Cst_nonneg).up 0 3
  have h3 := (((Minf (e := e) hC).const_mul CZ_nonneg).mul BS).up 0 3
  have h4 := (PF.mul ((h1.add h2).add h3)).up 1 3
  have h5 := ((PF.mul ((R.mul (AS.mul BS)).const_mul Cst_nonneg)).root (1 / 2)).up (1 / 2) (9 / 4)
  exact h4.add (h5.up 1 3)

theorem staticQ_below {C e : ℝ} (hC : 0 ≤ C) :
    JointBelow fun _ R caps ↦ staticQ R (C * Ex e R * R) caps := (deg_staticQ hC).toQ

/-! ### The right sides without `metQ` -/

/-- `−𝓛F`. -/
def mLp (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : Field :=
  -Lop (r * u) (Sp r g y u) (Fp r g y u)

/-- The bracket `−T_s` of `(2.5)`, for a family `Y`: `Y (−𝓛)`, its adjoint, `−D_S Y[B(S, S)]`. -/
def insT (𝔉 : Fam) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (zOf s (mLp r g y u)) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zOf s (mLp r g y u)) -
    hBY 𝔉 s r g y u

/-- **`joint1RHS` without the force, `h₀` and the metric–`Q` insertion.** -/
def joint1T (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -pair 1 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) - cubicHeat r (r * u) (Fp r g y u) +
    cubicD 1 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) +
    1 / 2 * (insT (famX2 1 r) 1 r g y u).re + 1 / 2 * (insT (famZ 1 r) 1 r g y u).re

/-- **`joint2RHS` without the force, `h₀` and the metric–`Q` insertion.** -/
def joint2T (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -pair 2 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) - cubicHeat2 r (r * u) (Fp r g y u) +
    cubicD 2 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) +
    1 / 2 * (insT (famX2 2 r) 2 r g y u).re + 1 / 2 * (insT (famZ 2 r) 2 r g y u).re

private lemma cancel_neg {A : Type*} [AddCommGroup A] (a b : A) : b = -a + (b + a) := by abel

/-- `fastQ = −𝓛F + N_Q`. -/
theorem fastQ_mL (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    fastQ r g y u = mLp r g y u + NQp r g y u := by
  rw [mLp, NQp]
  exact cancel_neg _ _

/-- The two fast slots of `insR` split into `−𝓛F` and `N_Q`. -/
theorem insR_split {s : ℕ} (hs : s = 1 ∨ s = 2) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u))
    (hS3 : InH 3 (Sp r g y u)) :
    insR (famX2 s r) s r g y u = insT (famX2 s r) s r g y u +
        (X2Form 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zOf s (NQp r g y u)) (zp s r g y u) +
          X2Form 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zOf s (NQp r g y u))) ∧
      insR (famZ s r) s r g y u = insT (famZ s r) s r g y u +
        (ZForm 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zOf s (NQp r g y u)) (zp s r g y u) +
          ZForm 1 s r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zOf s (NQp r g y u))) := by
  have hx := actual_adm h hu huT
  have hSA : Adm 2 (Sp r g y u) := hx.PiS
  have hFA : Adm 2 (Fp r g y u) := hx.PiF
  have hS' := Fam.PiS_Sp r g y u
  have hF' := Fam.PiF_Fp r g y u
  have hSM : MZ 3 (Sp r g y u) := ⟨hS3, hSA.mean⟩
  have hFM : MZ 3 (Fp r g y u) := ⟨hF3, hFA.mean⟩
  have hL := mz_Lop (r * u) hSM hFM
  have hA : MZ 2 (mLp r g y u) := ⟨hL.inH.neg, by simp [mLp, hL.mean]⟩
  have hA' : PiF (mLp r g y u) = mLp r g y u := by
    funext k
    by_cases hk : k 2 = 0 <;> simp [mLp, Lop, PiF, hk]
  have hB := (NQp_two_le h hu huT hF3).1
  have hB' := (NQp_facts h hu huT).2.2.1
  have hX := X2_slots_add hs hr (r * u) hSA.mz hS' hFA.mz hF' hA hA' hB hB'
  have hZ := Z_slots_add hs hr (r * u) hSA.mz hS' hFA.mz hF' hA hA' hB hB'
  constructor
  · simp only [insR, insT, famX2_form, zp, fastQ_mL]
    rw [hX.1, hX.2]
    ring
  · simp only [insR, insT, famZ_form, zp, fastQ_mL]
    rw [hZ.1, hZ.2]
    ring

/-- `joint₁R = joint₁T + metQ 1`. -/
theorem joint1R_split (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u)) :
    joint1R r g y u = joint1T r g y u + metQ 1 r g y u := by
  obtain ⟨e1, e2⟩ := insR_split (s := 1) (Or.inl rfl) h hr hu huT hF3 hS3
  have e1' := congrArg Complex.re e1
  have e2' := congrArg Complex.re e2
  rw [Complex.add_re] at e1' e2'
  unfold joint1R joint1T metQ metS coreR
  rw [e1', e2']
  simp only [Nat.cast_one]
  ring

/-- `joint₂R = joint₂T + metQ 2`. -/
theorem joint2R_split (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) (hS3 : InH 3 (Sp r g y u)) :
    joint2R r g y u = joint2T r g y u + metQ 2 r g y u := by
  obtain ⟨e1, e2⟩ := insR_split (s := 2) (Or.inr rfl) h hr hu huT hF3 hS3
  have e1' := congrArg Complex.re e1
  have e2' := congrArg Complex.re e2
  rw [Complex.add_re] at e1' e2'
  unfold joint2R joint2T metQ metS coreR
  rw [e1', e2']
  simp only [Nat.cast_ofNat]
  ring

/-- **The right sides in four parts, at almost every time.** -/
theorem ae_joint_final (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    ∀ᵐ u ∂(volume.restrict (Icc a b)),
      joint1RHS r g y u = joint1T r g y u + metQ 1 r g y u + h0Part 1 r g y u + forceS 1 r g y u ∧
        joint2RHS r g y u =
          joint2T r g y u + metQ 2 r g y u + h0Part 2 r g y u + forceS 2 r g y u := by
  filter_upwards [ae_joint_full h hr ha hab hb, ae_inH3_split h ha hab hb,
    ae_restrict_mem measurableSet_Icc] with u hu h3 hm
  have hu0 := ha.trans hm.1
  have huT := lt_lifespan hm.2 hb
  rw [hu.1, hu.2, joint1R_split h hr hu0 huT h3.1 h3.2, joint2R_split h hr hu0 huT h3.1 h3.2]
  exact ⟨rfl, rfl⟩

/-! ### On a joint piece -/

variable {M C ex R D : ℝ} {q : Caps → ℝ} {near : Caps → ℝ → Prop}
  {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} {caps : Caps} {s t ζ η : ℝ}

/-- The product `K a` on a prefix, at the threshold. -/
private lemma Ka_le (hr : r ≠ 0) (hP : OnPrefix caps r g y s t) (hM0 : 0 ≤ M) (hD : 1 ≤ D)
    (hη : 1 ≤ η) (hq : η * staticQ D M caps ≤ |r|) (hu : u ∈ Icc s t) :
    Kmet r D M (Sp r g y u) * fastNorm 1 r g y u ≤ 2 / η := by
  have hq0 : 0 < |r| := abs_pos.2 hr
  obtain ⟨a1, -, a3, a4, a5⟩ := hP.1 u hu
  have hK : Kmet r D M (Sp r g y u) ≤ kapQ r D M caps :=
    Kmet_le_kapQ hD hM0 (a5.trans (le_cp _)) (a3.trans (le_cp _)) (a4.trans (le_cp _))
  have hK0 := Kmet_nonneg r hD hM0 (Sp r g y u)
  have h1 := Pkap_le (by linarith) hM0 hη hq hq0
  have h2 : Kmet r D M (Sp r g y u) * fastNorm 1 r g y u ≤ kapQ r D M caps * cp caps.PF :=
    mul_le_mul hK (a1.trans (le_cp _)) (hnorm_nonneg _ _) (hK0.trans hK)
  linarith

/-- **`(15.2)` on a joint piece**: a share `16 c₄/η`, `32 c₄/η` of the dissipation. -/
theorem metQ_joint (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hp' : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (hD : 1 ≤ D) (hη : 1 ≤ η)
    (hq : η * staticQ D M caps ≤ q caps) :
    (∀ u ∈ Icc s t, |metQ 1 r g y u| ≤ 16 * c4 / η * fastNorm 2 r g y u ^ 2) ∧
      ∀ᵐ u ∂(volume.restrict (Icc s t)),
        |metQ 2 r g y u| ≤ 32 * c4 / η * fastNorm 3 r g y u ^ 2 := by
  have hM0 : 0 ≤ M := slowSup_nonneg.trans (hp'.sup s ⟨le_rfl, hp'.hst⟩)
  have hc := c4_pos
  have hka := fun u (hu : u ∈ Icc s t) =>
    Ka_le hr hp'.onPrefix hM0 hD hη (hq.trans hp'.thr) hu
  refine ⟨fun u hu => ?_, ?_⟩
  · have hu0 : 0 ≤ u := hp'.hs.trans hu.1
    have huT : ENNReal.ofReal u < Ty := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) hp'.ht
    refine (metQ_one_le h hr hu0 huT hD (hp'.sup u hu)).trans ?_
    have h1 := mul_le_mul_of_nonneg_left (hka u hu)
      (by positivity : 0 ≤ 8 * c4 * fastNorm 2 r g y u ^ 2)
    have e1 : 8 * c4 * fastNorm 2 r g y u ^ 2 * (2 / η) =
        16 * c4 / η * fastNorm 2 r g y u ^ 2 := by ring
    rw [e1] at h1
    linarith
  · filter_upwards [ae_inH3_split h hp'.hs hp'.hst hp'.ht, ae_restrict_mem measurableSet_Icc]
      with u h3 hu
    have hu0 : 0 ≤ u := hp'.hs.trans hu.1
    have huT : ENNReal.ofReal u < Ty := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) hp'.ht
    refine (metQ_two_le h hr hu0 huT h3.1 hD (hp'.sup u hu)).trans ?_
    have h1 := mul_le_mul_of_nonneg_left (hka u hu)
      (by positivity : 0 ≤ 16 * c4 * fastNorm 3 r g y u ^ 2)
    have e1 : 16 * c4 * fastNorm 3 r g y u ^ 2 * (2 / η) =
        32 * c4 / η * fastNorm 3 r g y u ^ 2 := by ring
    rw [e1] at h1
    linarith

/-- **`joint1RHS` on a joint piece**: `joint₁T` is what is left. -/
theorem joint1_final_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hp' : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (hD : 1 ≤ D)
    (hq : force1Q φ D M caps ≤ q caps) (hζ : 0 < ζ) (hD' : 1 ≤ R) (hη : 1 ≤ η)
    (hs' : η * staticQ R M caps ≤ q caps) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), joint1RHS r g y u ≤ joint1T r g y u +
      (2 * hBd φ r g y u * fastNorm 2 r g y u + 24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) +
      (ζ * fastNorm 2 r g y u ^ 2 +
        (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * ζ) * fastNorm 1 r g y u ^ 2) +
      16 * c4 / η * fastNorm 2 r g y u ^ 2 := by
  obtain ⟨hm1, -⟩ := metQ_joint h hr hp' hD' hη hs'
  obtain ⟨h1, -, -⟩ := force1_joint h hp' hD hq
  filter_upwards [ae_joint_final h hr hp'.hs hp'.hst hp'.ht, ae_restrict_mem measurableSet_Icc]
    with u hu hm
  rw [hu.1]
  have h2 := (le_abs_self _).trans ((forceS_one_le r g y u).trans (h1 u hm))
  have h3 := (le_abs_self _).trans (h0Part_young_one (φ := φ) h hr hp'.onPrefix hp'.hs hp'.ht hm hζ)
  have h4 := (le_abs_self _).trans (hm1 u hm)
  linarith

/-- **`joint2RHS` on a joint piece**: `joint₂T` is what is left. -/
theorem joint2_final_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0)
    (hp' : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (h0 : 0 ≤ C * ex)
    (hR : 0 ≤ R) (hD : 1 ≤ D) (hq : force2Q φ D M C ex R caps ≤ q caps) (hζ : 0 < ζ) (hD' : 1 ≤ R)
    (hη : 1 ≤ η) (hs' : η * staticQ R M caps ≤ q caps) :
    ∀ᵐ u ∂(volume.restrict (Icc s t)), joint2RHS r g y u ≤ joint2T r g y u +
      (1 / 64 * fastNorm 3 r g y u ^ 2 + 16 * GF φ D M r g y caps u) +
      (ζ * fastNorm 3 r g y u ^ 2 +
        (Ch0 * kapH0 caps * h0Bd φ r g y u / |r|) ^ 2 / (4 * ζ) * fastNorm 2 r g y u ^ 2) +
      32 * c4 / η * fastNorm 3 r g y u ^ 2 := by
  obtain ⟨-, hm2⟩ := metQ_joint h hr hp' hD' hη hs'
  obtain ⟨-, -, h1⟩ := force2_joint h hp' h0 hR hD hq
  filter_upwards [h1, hm2, ae_joint_final h hr hp'.hs hp'.hst hp'.ht,
    ae_restrict_mem measurableSet_Icc, ae_inH3_split h hp'.hs hp'.hst hp'.ht]
    with u hb hm hu hmem h3F
  rw [hu.2]
  have h2 := (le_abs_self _).trans ((forceS_two_le r g y u).trans hb)
  have h3 := (le_abs_self _).trans
    (h0Part_young_two (φ := φ) h hr hp'.onPrefix hp'.hs hp'.ht hmem h3F.1 hζ)
  have h4 := (le_abs_self _).trans hm
  linarith

end OVNS.Quant.Metric

end
