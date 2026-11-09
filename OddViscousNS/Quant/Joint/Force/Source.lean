import OddViscousNS.Quant.Joint.Force.One

/-!
# The companions of the force: `h₀`, role 18, the bare appearances (step J5, node N12)

`JOINT_ASSEMBLY_V4.md` §5, roles 11–12, 18; `FORCE_AND_JOINT_PAYMENTS_V2.md` §§10, 14;
`TIMED_METRIC_PROOF_V2.md` (8.10).

* `hp_eq`: `h₀ = Π_S g − Π_S Q(F, F) − Π_S H_ψ` (TeX eq. quant-actual-system): `hp` of
  `Joint/Metric/JointId.lean` has no slow–slow and no mixed term.
* `h0_sq_le`, `H0c`: `‖h₀‖_{L²H¹} ≤ H₀ ≲ φ + y √J_F`, of size `R`.  J4 §5 left it open.
* `companion_le`, `companion_paid`: the two forms in which `h₀` enters the fast energies: the source
  `P_F (1 + B_S) ‖h₀‖₁/q` (roles 11–12) and the Young mass `q⁻² (1 + B_S)² ‖h₀‖₁²` ((8.10)).  So
  `h₀` is not dropped.
* `h0_slot_one`, `h0_slot_two`: the first slot of `coreRHS`, `X₁[h₀]`, at both weights, as a form.
* `role18_direct`: the literal `‖H_ψ‖₁ ≤ 1/2`, paid by `q ≥ C Y φ` and `q² ≥ C φ²`, with no raised
  floor (§10; `role18` of J4 goes through `Q₀'`).
* `Hf_le_gF`: `‖H_{ψ,F}‖₁ ≤ gF`: the bare source of `Q_{3,s}` ("fixed tightening pays the additional
  bare genuine source appearances", §14) is a fixed multiple of LOCAL363's `g`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}

/-! ### `h₀` -/

/-- On a slow field the phased product is the slow product: every leg has phase zero. -/
lemma Qphase_slow_eq (τ : ℝ) {S : Field} (hS : PiS S = S) : Qphase τ S S = Bslow S := by
  funext k
  simp only [Bslow]
  by_cases hk : k 2 = 0
  · rw [PiS_apply_slow _ hk]
    unfold Qphase Qres Qm
    refine tsum_congr fun p => ?_
    by_cases hp : p 2 = 0
    · have hq : (k - p) 2 = 0 := by simp [hk, hp]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => ?_
      have hk' : (p + (k - p)) 2 = 0 := by simp [hk, hp]
      have hΦ : Phi a b c p (k - p) = 0 := by
        simp only [Phi]
        rw [lam_slow hp, lam_slow hq, lam_slow hk']
        ring
      simp [phaseM, resM, hΦ]
    · have h0 : S p = 0 := slow_zero hS hp
      simp [h0, hel_zero_right, vert_zero_left]
  · rw [PiS_apply_fast _ hk, Qphase_slow_slow τ hS hk]

/-- **`h₀`** (TeX eq. quant-actual-system): no slow–slow term, no mixed term. -/
theorem hp_eq (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    hp r g y u = PiS g - PiS (Qphase (r * u) (Fp r g y u) (Fp r g y u)) -
      PiS (Hpsi r g y u) := by
  have hx := actual_adm h hu huT
  funext k
  have hs := congrFun (Qphase_sectors (r * u) hx) k
  have he : Hpsi r g y u k = Qphase (r * u) (y u) (y u) k -
      Qphase (r * u) (actual r g y u) (actual r g y u) k := rfl
  by_cases hk : k 2 = 0
  · simp only [hp, slowNL, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, PiS_apply_slow _ hk]
    have e1 : Qphase (r * u) (PiS (actual r g y u)) (PiF (actual r g y u)) k = 0 :=
      Qphase_slow_fast _ (PiS_PiS_eq _) (PiF_PiF_eq _) hk
    have e2 : Qphase (r * u) (PiS (actual r g y u)) (PiS (actual r g y u)) k =
        Bslow (Sp r g y u) k := congrFun (Qphase_slow_eq (r * u) (PiS_PiS_eq (actual r g y u))) k
    simp only [Pi.add_apply, e1, add_zero] at hs
    rw [he, hs, e2]
    simp only [Fp]
    abel
  · have e0 : Bslow (Sp r g y u) k = 0 := by
      simp only [Bslow]
      exact PiS_apply_fast _ hk
    simp only [hp, slowNL, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, PiS_apply_fast _ hk, e0]
    simp

/-- The pointwise bound of `‖h₀‖₁`: `φ + 8 c₄ b_F² + hBd`. -/
def h0Bd (φ r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  φ + 8 * c4 * fastNorm 2 r g y u ^ 2 + hBd φ r g y u

/-- `‖h₀‖₁`, at every time. -/
theorem hp_one_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    InH 1 (hp r g y u) ∧ hnorm 1 (hp r g y u) ≤ h0Bd φ r g y u := by
  have hx := actual_adm h hu huT
  have hF : MZ 2 (Fp r g y u) := hx.PiF.mz
  obtain ⟨iQ, bQ⟩ := hnorm_one_Qm_le (phaseM_bdd (r * u)) hF hF
  obtain ⟨iH, bH⟩ := hnorm_one_Hpsi_le h hr hu huT
  have ig : InH 1 g := h.force_adm.inH.mono (by norm_num)
  have e := hp_eq h hu huT
  have i1 := ig.PiS
  have i2 : InH 1 (PiS (Qphase (r * u) (Fp r g y u) (Fp r g y u))) := iQ.PiS
  have i3 := iH.PiS
  have i12 : InH 1 (PiS g - PiS (Qphase (r * u) (Fp r g y u) (Fp r g y u))) := by
    rw [sub_eq_add_neg]
    exact i1.add i2.neg
  have i123 : InH 1 (PiS g - PiS (Qphase (r * u) (Fp r g y u) (Fp r g y u)) -
      PiS (Hpsi r g y u)) := by
    rw [sub_eq_add_neg]
    exact i12.add i3.neg
  rw [e]
  refine ⟨i123, (hnorm_sub_le i12 i3).trans ?_⟩
  have h1 := hnorm_sub_le i1 i2
  have g1 : hnorm 1 (PiS g) ≤ φ :=
    (hnorm_PiS_le ig).trans ((hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le)
  have q1 : hnorm 1 (PiS (Qphase (r * u) (Fp r g y u) (Fp r g y u))) ≤
      8 * c4 * fastNorm 2 r g y u ^ 2 := by
    refine (hnorm_PiS_le iQ).trans (bQ.trans ?_)
    have hw := wiener_le hF
    have hb := hnorm_nonneg 2 (Fp r g y u)
    have e2 : fastNorm 2 r g y u = hnorm 2 (Fp r g y u) := rfl
    rw [e2]
    have h3 := mul_le_mul_of_nonneg_right hw hb
    nlinarith only [h3]
  have q2 : hnorm 1 (PiS (Hpsi r g y u)) ≤ hBd φ r g y u := (hnorm_PiS_le iH).trans bH
  unfold h0Bd
  linarith

/-- The square of the `L²H¹` size of `h₀` on a piece of length `≤ 4`. -/
def H0sq (φ r : ℝ) (caps : Caps) : ℝ :=
  3 * (4 * φ ^ 2 + 64 * c4 ^ 2 * (cp caps.yF ^ 2 * cp caps.JF) +
    (3 * (hLc φ caps / |r|) ^ 2 + 3 * (hQc φ / |r| ^ 2) ^ 2))

/-- **`‖h₀‖_{L²H¹}`**, by the majorant `h0Bd`. -/
theorem h0_sq_le (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 4) (hP : OnPrefix caps r g y s t) :
    IntervalIntegrable (fun u => h0Bd φ r g y u ^ 2) volume s t ∧
      ∫ u in s..t, h0Bd φ r g y u ^ 2 ≤ H0sq φ r caps := by
  have ht0 := hs.trans hst
  obtain ⟨hI1, hV1⟩ := hBd_sq_int h hs hst ht hlen hP
  have hS := continuousOn_slow_two h hs hst ht
  have hF : ContinuousOn (fastNorm 2 r g y) (uIcc s t) := by
    rw [uIcc_of_le hst]
    exact (norms_continuous h ht0 ht).2.1.mono (Icc_subset_Icc_left hs)
  have hc := c4_pos
  have hF2 : IntervalIntegrable (fun u => fastNorm 2 r g y u ^ 2) volume s t :=
    (hF.pow 2).intervalIntegrable
  have hF4 : IntervalIntegrable (fun u => fastNorm 2 r g y u ^ 4) volume s t :=
    (hF.pow 4).intervalIntegrable
  have hI : IntervalIntegrable (fun u => h0Bd φ r g y u ^ 2) volume s t := by
    have hc1 : ContinuousOn (fun u => h0Bd φ r g y u) (uIcc s t) :=
      (continuousOn_const.add (continuousOn_const.mul (hF.pow 2))).add
        ((continuousOn_const.mul (hS.add hF)).add continuousOn_const)
    exact (hc1.pow 2).intervalIntegrable
  refine ⟨hI, ?_⟩
  set a := fun u => hBd φ r g y u ^ 2 with ha
  set b := fun u => fastNorm 2 r g y u ^ 4 with hb
  have hg : IntervalIntegrable (fun u => 3 * φ ^ 2 + (3 * (64 * c4 ^ 2) * b u + 3 * a u))
      volume s t :=
    intervalIntegrable_const.add ((hF4.const_mul _).add (hI1.const_mul 3))
  have hle : ∀ u ∈ Icc s t, h0Bd φ r g y u ^ 2 ≤
      3 * φ ^ 2 + (3 * (64 * c4 ^ 2) * b u + 3 * a u) := fun u _ => by
    set x := fastNorm 2 r g y u
    set w := hBd φ r g y u
    set v := 8 * c4 * x ^ 2 with hv
    have e1 : h0Bd φ r g y u = φ + v + w := rfl
    have e2 : 3 * φ ^ 2 + (3 * (64 * c4 ^ 2) * b u + 3 * a u) = 3 * (φ ^ 2 + v ^ 2 + w ^ 2) := by
      simp only [ha, hb, hv]
      ring
    rw [e1, e2]
    nlinarith only [sq_nonneg (φ - v), sq_nonneg (φ - w), sq_nonneg (v - w)]
  have hm := intervalIntegral.integral_mono_on hst hI hg hle
  have hval : ∫ u in s..t, (3 * φ ^ 2 + (3 * (64 * c4 ^ 2) * b u + 3 * a u)) =
      (t - s) * (3 * φ ^ 2) + (3 * (64 * c4 ^ 2) * (∫ u in s..t, b u) + 3 * ∫ u in s..t, a u) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
        ((hF4.const_mul _).add (hI1.const_mul 3)),
      intervalIntegral.integral_add (hF4.const_mul _) (hI1.const_mul 3),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [hval] at hm
  have h4 : ∫ u in s..t, b u ≤ cp caps.yF ^ 2 * cp caps.JF := by
    have hle2 : ∀ u ∈ Icc s t, b u ≤ cp caps.yF ^ 2 * fastNorm 2 r g y u ^ 2 := fun u hu => by
      have hb0 : 0 ≤ fastNorm 2 r g y u := hnorm_nonneg _ _
      have hy : fastNorm 2 r g y u ≤ cp caps.yF := (hP.1 u hu).2.1.trans (le_cp _)
      have h5 : fastNorm 2 r g y u ^ 2 ≤ cp caps.yF ^ 2 := pow_le_pow_left₀ hb0 hy 2
      simp only [hb]
      nlinarith only [mul_le_mul_of_nonneg_right h5 (sq_nonneg (fastNorm 2 r g y u))]
    have h6 := intervalIntegral.integral_mono_on hst hF4 (hF2.const_mul (cp caps.yF ^ 2)) hle2
    rw [intervalIntegral.integral_const_mul] at h6
    refine h6.trans (mul_le_mul_of_nonneg_left (hP.2.1.trans (le_cp _)) (sq_nonneg _))
  have h5 : (t - s) * (3 * φ ^ 2) ≤ 4 * (3 * φ ^ 2) :=
    mul_le_mul_of_nonneg_right hlen (by positivity)
  have h6 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 3 * (64 * c4 ^ 2))
  unfold H0sq
  linarith

/-- The cap of `‖h₀‖_{L²H¹}`: `4 φ + 16 c₄ y √J_F + 2`, of size `R`. -/
def H0c (φ : ℝ) (caps : Caps) : ℝ := 4 * φ + 16 * c4 * (cp caps.yF * Real.sqrt (cp caps.JF)) + 2

/-- The threshold of the two companions: `(1 + P_F) (1 + B_S) H₀`. -/
def force0Q (φ : ℝ) (caps : Caps) : ℝ := (1 + cp caps.PF) * (1 + cp caps.BS) * H0c φ caps

lemma H0c_nonneg (hφ : 0 ≤ φ) (caps : Caps) : 0 ≤ H0c φ caps := by
  have := c4_pos
  have := cp_nonneg caps.yF
  have := Real.sqrt_nonneg (cp caps.JF)
  unfold H0c
  positivity

/-- `H0sq ≤ H₀²`, once the source part of `force1Q` is paid. -/
lemma H0sq_le (hφ : 0 ≤ φ) {caps : Caps} (hx : hLc φ caps / |r| ≤ 1 / 8)
    (hz : hQc φ / |r| ^ 2 ≤ 1 / 8) (hx0 : 0 ≤ hLc φ caps / |r|) (hz0 : 0 ≤ hQc φ / |r| ^ 2) :
    H0sq φ r caps ≤ H0c φ caps ^ 2 := by
  set Y := cp caps.yF * Real.sqrt (cp caps.JF) with hY
  have hY0 : 0 ≤ Y := mul_nonneg (cp_nonneg _) (Real.sqrt_nonneg _)
  have hY2 : cp caps.yF ^ 2 * cp caps.JF = Y ^ 2 := by
    rw [hY, mul_pow, Real.sq_sqrt (cp_nonneg _)]
  have hc := c4_pos
  have h1 : 3 * (hLc φ caps / |r|) ^ 2 + 3 * (hQc φ / |r| ^ 2) ^ 2 ≤ 1 := by
    nlinarith only [hx, hz, hx0, hz0]
  unfold H0sq H0c
  rw [hY2]
  have h2 : 0 ≤ φ * (c4 * Y) := by positivity
  have h3 : 0 ≤ c4 * Y := by positivity
  nlinarith only [h1, h2, h3, hφ, sq_nonneg φ, sq_nonneg (c4 * Y)]

/-- **The two companions of the force** (`JOINT_ASSEMBLY_V4.md` roles 11–12; `TIMED_METRIC` (8.10)):
for `κ ≥ 0`, `∫ (κ ‖h₀‖₁/q)² ≤ (κ H₀/q)²`, with `κ = P_F (1 + B_S)` for the source and
`κ = 1 + B_S` for the Young mass. -/
theorem companion_le (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t κ : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 4) (hP : OnPrefix caps r g y s t)
    (hx : hLc φ caps / |r| ≤ 1 / 8) (hz : hQc φ / |r| ^ 2 ≤ 1 / 8) (hr : r ≠ 0) :
    (∫ u in s..t, (κ * h0Bd φ r g y u / |r|) ^ 2) ≤ (κ * H0c φ caps / |r|) ^ 2 := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hq : 0 < |r| := abs_pos.2 hr
  obtain ⟨-, hV⟩ := h0_sq_le h hs hst ht hlen hP
  have hx0 : 0 ≤ hLc φ caps / |r| := div_nonneg (hLc_nonneg hφ caps) hq.le
  have hz0 : 0 ≤ hQc φ / |r| ^ 2 := div_nonneg (hQc_nonneg φ) (by positivity)
  have h1 := hV.trans (H0sq_le hφ hx hz hx0 hz0)
  have e : ∫ u in s..t, (κ * h0Bd φ r g y u / |r|) ^ 2 =
      (κ / |r|) ^ 2 * ∫ u in s..t, h0Bd φ r g y u ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring
  have e2 : (κ * H0c φ caps / |r|) ^ 2 = (κ / |r|) ^ 2 * H0c φ caps ^ 2 := by ring
  rw [e, e2]
  exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

/-- **The companions are paid** at the threshold of the force: `κ H₀ ≤ q` gives `‖κ h₀/q‖_{L²} ≤ 1`,
for `κ = C P_F (1 + B_S)` and `κ = C (1 + B_S)`. -/
theorem companion_paid (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t κ D M : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 4) (hP : OnPrefix caps r g y s t)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hq : force1Q φ D M caps ≤ |r|) (hκ0 : 0 ≤ κ)
    (hκ : κ * H0c φ caps ≤ |r|) :
    (∫ u in s..t, (κ * h0Bd φ r g y u / |r|) ^ 2) ≤ 1 := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  obtain ⟨hq1, hx, hz⟩ := force1Q_source hφ hM hD hq
  have hq0 : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hq0
  refine (companion_le h hs hst ht hlen hP hx hz hr).trans ?_
  have h1 : κ * H0c φ caps / |r| ≤ 1 := by
    rw [div_le_iff₀ hq0]
    linarith
  have h0 : 0 ≤ κ * H0c φ caps / |r| :=
    div_nonneg (mul_nonneg hκ0 (H0c_nonneg hφ caps)) hq0.le
  exact pow_le_one₀ h0 h1

/-- `h₀` is a real slow `H¹` field of mean zero. -/
theorem hp_facts (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    MZ 1 (hp r g y u) ∧ IsReal (hp r g y u) ∧ PiS (hp r g y u) = hp r g y u := by
  have hx := actual_adm h hu huT
  have hS : Adm 2 (Sp r g y u) := hx.PiS
  have r1 := (slowNL_l2 h hu huT).1
  have r2 : IsReal (Bslow (Sp r g y u)) := (majorized_res.real 0 _ _ hS hS).PiS'
  have e1 := PiS_slowNL (r := r) (g := g) (y := y) u
  have e2 : PiS (Bslow (Sp r g y u)) = Bslow (Sp r g y u) := by
    funext k
    by_cases hk : k 2 = 0 <;> simp [Bslow, PiS, hk]
  refine ⟨⟨(hp_one_le h hr hu huT).1, ?_⟩, fun k => ?_, ?_⟩
  · have m1 : g 0 = 0 := h.force_adm.mean
    have m2 := H2.Qm_zero_mode (m := phaseM (r * u)) (y u) (y u)
    have m3 := H2.Qm_zero_mode (m := resM) (Sp r g y u) (Sp r g y u)
    simp only [hp, slowNL, Bslow, Pi.add_apply, Pi.neg_apply, PiS, Qphase, Qres]
    simp [m1, m2, m3]
  · simp only [hp, Pi.add_apply, r1 k, r2 k]
    ext i
    simp [conjV]
  · funext k
    by_cases hk : k 2 = 0
    · exact PiS_apply_slow _ hk
    · have a := congrFun e1 k
      have b := congrFun e2 k
      rw [PiS_apply_fast _ hk] at a b
      simp [PiS_apply_fast _ hk, hp, ← a, ← b]

/-- **The direction `h₀` of `X₁`, at weight one** (the first slot of `coreRHS`, (8.10); it is kept
as a form, and the Young step of (8.10) is left to the energies). -/
theorem h0_slot_one (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    |2 * pair 1 (Fp r g y u) (X1op r (r * u) (hp r g y u) (Fp r g y u))| ≤
      2 ^ 10 * h0Bd φ r g y u / |r| * (fastNorm 1 r g y u * fastNorm 2 r g y u) := by
  have hx := actual_adm h hu huT
  obtain ⟨hm, hrl, hsl⟩ := hp_facts h hr hu huT
  have hq : 0 < |r| := abs_pos.2 hr
  have h1 := X1op_slow_le hr (r * u) hm hrl hsl hx.PiF.mz (PiF_PiF_eq _)
  have h2 := (hp_one_le h hr hu huT).2
  have hab : 0 ≤ fastNorm 1 r g y u * fastNorm 2 r g y u :=
    mul_nonneg (hnorm_nonneg _ _) (hnorm_nonneg _ _)
  have e : 2 ^ 9 * hnorm 1 (hp r g y u) * hnorm 1 (PiF (actual r g y u)) *
      hnorm 2 (PiF (actual r g y u)) / |r| =
      2 ^ 9 * hnorm 1 (hp r g y u) / |r| * (fastNorm 1 r g y u * fastNorm 2 r g y u) := by
    simp only [fastNorm]
    ring
  rw [abs_mul, abs_two]
  refine (mul_le_mul_of_nonneg_left h1 (by norm_num)).trans ?_
  rw [e]
  have h3 : 2 ^ 9 * hnorm 1 (hp r g y u) / |r| ≤ 2 ^ 9 * h0Bd φ r g y u / |r| := by gcongr
  have h4 := mul_le_mul_of_nonneg_right h3 hab
  have e2 : 2 ^ 10 * h0Bd φ r g y u / |r| = 2 * (2 ^ 9 * h0Bd φ r g y u / |r|) := by ring
  rw [e2]
  linarith

/-- **The direction `h₀` of `X₁`, at weight two** (the first slot of `coreRHS`, (8.10)). -/
theorem h0_slot_two (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) :
    |2 * pair 2 (Fp r g y u) (X1op r (r * u) (hp r g y u) (Fp r g y u))| ≤
      2 * H2.cSrc * h0Bd φ r g y u / |r| * (fastNorm 2 r g y u * fastNorm 3 r g y u) := by
  have hx := actual_adm h hu huT
  obtain ⟨hm, -, hsl⟩ := hp_facts h hr hu huT
  have hq : 0 < |r| := abs_pos.2 hr
  have hc := H2.cSrc_nonneg
  have hFM : MZ 3 (Fp r g y u) := ⟨hF3, hx.PiF.mean⟩
  have h1 := H2.pair_X1op_slow_le hr (r * u) hm hsl hFM (PiF_PiF_eq _) hx.PiF.real
  have h2 := (hp_one_le h hr hu huT).2
  have hab : 0 ≤ fastNorm 2 r g y u * fastNorm 3 r g y u :=
    mul_nonneg (hnorm_nonneg _ _) (hnorm_nonneg _ _)
  have e : H2.cSrc * hnorm 1 (hp r g y u) * hnorm 2 (Fp r g y u) * hnorm 3 (Fp r g y u) / |r| =
      H2.cSrc * hnorm 1 (hp r g y u) / |r| * (fastNorm 2 r g y u * fastNorm 3 r g y u) := by
    simp only [fastNorm, Fp]
    ring
  rw [abs_mul, abs_two]
  refine (mul_le_mul_of_nonneg_left h1 (by norm_num)).trans ?_
  rw [e]
  have h3 : H2.cSrc * hnorm 1 (hp r g y u) / |r| ≤ H2.cSrc * h0Bd φ r g y u / |r| := by gcongr
  have h4 := mul_le_mul_of_nonneg_right h3 hab
  have e2 : 2 * H2.cSrc * h0Bd φ r g y u / |r| = 2 * (H2.cSrc * h0Bd φ r g y u / |r|) := by ring
  rw [e2]
  linarith

/-! ### Role 18, and the bare appearances -/

/-- **The threshold of role 18**: `q ≥ 4 j_L`, `q² ≥ 4 j_Q`, `j_L ≍ φ (B_S + y)`, `j_Q ≍ φ²`. -/
def role18J (φ : ℝ) (caps : Caps) : ℝ := 4 * jLc φ caps + rootQ 2 (4 * jQc φ)

/-- **Role 18**: the literal pointwise `‖H_ψ‖₁ ≤ 1/2`, paid directly by `q ≥ 4 j_L`, `q² ≥ 4 j_Q`
(§10: "`q ≥ C Y φ` pays it directly", "no `Y²φ` floor is used here"). -/
theorem role18_direct (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {caps : Caps} {s t : ℝ}
    (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hP : OnPrefix caps r g y s t) (hu : u ∈ Icc s t)
    (hq' : role18J φ caps ≤ |r|) :
    hnorm 1 (Hpsi r g y u) ≤ 1 / 2 := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hj := jLc_nonneg hφ caps
  have hk := jQc_nonneg φ
  have hr2 := rootQ_nonneg 2 (by positivity : 0 ≤ 4 * jQc φ)
  have h1 : 4 * jLc φ caps ≤ |r| := by
    unfold role18J at hq'
    linarith
  have h2 : 4 * jQc φ ≤ |r| ^ 2 := by
    have h3 : rootQ 2 (4 * jQc φ) ≤ |r| := by
      unfold role18J at hq'
      linarith
    have h4 := le_rpow_of_rootQ (by norm_num) (by positivity) h3
    rwa [Real.rpow_two] at h4
  refine (hnorm_one_Hpsi_sup h hr hs ht hP hu).trans ?_
  have t1 : jLc φ caps / |r| ≤ 1 / 4 := by
    rw [div_le_iff₀ hq]
    linarith
  have t2 : jQc φ / |r| ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have e : 32 * c4 * φ * (cp caps.BS + cp caps.yF) / |r| + 32 * c4 * φ ^ 2 / r ^ 2 =
      jLc φ caps / |r| + jQc φ / |r| ^ 2 := by
    simp only [jLc, jQc, sq_abs]
  rw [e]
  linarith

/-- **The bare source**: `‖H_{ψ,F}‖₁ ≤ gF`.  Since `gA ≥ 1`, every further appearance of the force
with a coefficient at most one, as `Re⟨Q_{3,s} z, A^{s/2} H⟩` under `‖A^{1/2} Q_{3,2}‖ ≤ 1`,
`‖Q_{3,1}‖ ≤ 1` (§14), is a fixed share of LOCAL363's `g`. -/
theorem Hf_le_gF (h : ActualSol μ φ r g y Ty) (hr1 : 1 ≤ |r|) {D M : ℝ} {caps : Caps} (hD : 1 ≤ D)
    (hM : 0 ≤ M) (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    hnorm 1 (Hf r g y u) ≤ gF φ D M r g y caps u := by
  have hq : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hq
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  obtain ⟨-, h1⟩ := Hf_one h hr hu huT
  have hb := hBd_nonneg hφ r g y u
  have h2 : 1 ≤ gA D M r caps := by
    have h3 := E2c_nonneg caps
    have h4 := E4c_nonneg hD caps
    have h5 := E5c_nonneg hD caps
    have h6 : 0 ≤ cp caps.PF := cp_nonneg _
    have hc := c4_pos
    have h7 : 1 ≤ E1c caps := by
      unfold E1c
      nlinarith only [h6, hc]
    have h8 := CZh_pos
    have h9 := Real.log_nonneg hr1
    have h10 := cp_nonneg caps.BS
    have h11 := Real.sqrt_nonneg |r|
    have h12 : 0 ≤ E2c caps / Real.sqrt |r| := by positivity
    have h13 : 0 ≤ E4c D caps / |r| := by positivity
    have h14 : 0 ≤ E5c D caps / |r| ^ 2 := by positivity
    have h15 : 0 ≤ 2 * (CZh / |r| * (1 + M * (1 + Real.log |r|)) * cp caps.BS) := by positivity
    unfold gA
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 hb
  have h4 := mul_nonneg (Shc_nonneg hφ r caps) (Vc_nonneg (r := r) (by linarith : 0 ≤ D) g y caps u)
  have h5 : hnorm 1 (Hf r g y u) ≤ hBd φ r g y u := h1
  unfold gF
  linarith

end OVNS.Quant.Metric

end
