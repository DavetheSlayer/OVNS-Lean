import OddViscousNS.Quant.Joint.Force.Degree

/-!
# Node N12: the force on a joint piece, for the energies

The statements of `Joint/Force/` at the shape of `JointPiece`.  The energies put into their
thresholds `q₁`, `q₂`, with `M = slowC Ex(36, R) R`, `φ = R − X`:
* `q₂ ≥ force2Q φ (jointD R) M slowC (Ex 36 R) R`, `force2Q_below`;
* `q₁ ≥ force1Q φ R M`, `force1Q_below`;
* `q₁, q₂ ≥ C force0Q φ`, `force0Q_below`, for the companions;
* `role18J φ`, `role18J_below`, if the literal `‖H_ψ‖₁ ≤ 1/2` is wanted.

Then, on a joint piece:
* `force2_joint`: `force2 ≤ c_F²/64 + 16 GF`, `∫ GF ≤ 2⁻¹²` on every subinterval;
* `force1_joint`: `force1 ≤ N_f b_F + f_f`, `∫ N_f² ≤ 1`, `∫ f_f ≤ 1`;
* `bare_two`, `bare_one`: a further bare `‖H_{ψ,F}‖₁ c_F`, `‖H_{ψ,F}‖₁ b_F`, for `Q₃,₁`, `Q₃,₂`;
* `h0_joint_one`, `h0_joint_two`, `companion_paid`: the slot `X₁[h₀]` and its masses.

`Force/Final.lean` is the end of the directory: the link to `joint1RHS`, `joint2RHS`, the whole
`h₀` derivative and the metric–`Q` insertion (`ae_joint_final`, `joint1_final_le`,
`joint2_final_le`).
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}
  {M C ex R D : ℝ} {q : Caps → ℝ} {near : Caps → ℝ → Prop}
  {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop} {caps : Caps} {s t : ℝ}

/-- **The ten pairs at weight two, on a joint piece.** -/
theorem force2_joint (h : ActualSol μ φ r g y Ty)
    (hp : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (h0 : 0 ≤ C * ex)
    (hR : 0 ≤ R) (hD : 1 ≤ D) (hq : force2Q φ D M C ex R caps ≤ q caps) :
    IntervalIntegrable (GF φ D M r g y caps) volume s t ∧
      (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
        ∫ u in u₁..u₂, GF φ D M r g y caps u ≤ 1 / 2 ^ 12) ∧
      ∀ᵐ u ∂(volume.restrict (Icc s t)),
        force2 r g y u ≤ 1 / 64 * fastNorm 3 r g y u ^ 2 + 16 * GF φ D M r g y caps u :=
  force2_final h hp.slow h0 hR hp.hs hp.hst hp.ht hp.len hp.onPrefix hp.sup hD (hq.trans hp.thr)

/-- **The pairs at weight one, on a joint piece.** -/
theorem force1_joint (h : ActualSol μ φ r g y Ty)
    (hp : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (hD : 1 ≤ D)
    (hq : force1Q φ D M caps ≤ q caps) :
    (∀ u ∈ Icc s t, force1 r g y u ≤ 2 * hBd φ r g y u * fastNorm 2 r g y u +
        24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) ∧
      (∫ u in s..t, (2 * hBd φ r g y u) ^ 2) ≤ 1 ∧
      (∫ u in s..t, 24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) ≤ 1 := by
  obtain ⟨h1, -, -, -, h5, h6⟩ :=
    force1_final h hp.onPrefix hp.hs hp.hst hp.ht hp.len hp.sup hD (hq.trans hp.thr)
  exact ⟨h1, h5, h6⟩

/-- **A bare source at weight two**: `‖H_{ψ,F}‖₁ c_F`, at LOCAL363's tolerance. -/
theorem bare_two (h : ActualSol μ φ r g y Ty) (hr1 : 1 ≤ |r|) (hD : 1 ≤ D) (hM : 0 ≤ M)
    (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    hnorm 1 (Hf r g y u) * fastNorm 3 r g y u ≤
      1 / 64 * fastNorm 3 r g y u ^ 2 + 16 * GF φ D M r g y caps u := by
  have h1 := Hf_le_gF (caps := caps) h hr1 hD hM hu huT
  have h2 := gF_sq_le φ D M r g y caps u
  have hc := hnorm_nonneg 3 (PiF (actual r g y u))
  have h3 : hnorm 1 (Hf r g y u) * fastNorm 3 r g y u ≤
      gF φ D M r g y caps u * fastNorm 3 r g y u := mul_le_mul_of_nonneg_right h1 hc
  set x := gF φ D M r g y caps u
  set c := fastNorm 3 r g y u
  nlinarith only [h3, h2, sq_nonneg (c / 8 - 4 * x)]

/-- **A bare source at weight one**: `‖H_{ψ,F}‖₁ b_F ≤ hBd b_F`, a share of `N_f b_F`. -/
theorem bare_one (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    hnorm 1 (Hf r g y u) * fastNorm 2 r g y u ≤ hBd φ r g y u * fastNorm 2 r g y u :=
  mul_le_mul_of_nonneg_right (Hf_one h hr hu huT).2 (hnorm_nonneg _ _)

/-- **`X₁[h₀]` at weight one, in the form `N b_F`** on a piece, `N = 2¹⁰ P_F ‖h₀‖₁/q`:
`∫ N² ≤ 1` as soon as `2¹⁰ P_F H₀ ≤ q`.  This is the genuine term of (2.5), "never dropped". -/
theorem h0_joint_one (h : ActualSol μ φ r g y Ty)
    (hp' : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (hD : 1 ≤ D)
    (hq : force1Q φ D M caps ≤ q caps) (hκ : 2 ^ 10 * cp caps.PF * H0c φ caps ≤ |r|) :
    (∀ u ∈ Icc s t, |2 * pair 1 (Fp r g y u) (X1op r (r * u) (hp r g y u) (Fp r g y u))| ≤
        2 ^ 10 * cp caps.PF * h0Bd φ r g y u / |r| * fastNorm 2 r g y u) ∧
      ∫ u in s..t, (2 ^ 10 * cp caps.PF * h0Bd φ r g y u / |r|) ^ 2 ≤ 1 := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hM : 0 ≤ M := slowSup_nonneg.trans (hp'.sup s ⟨le_rfl, hp'.hst⟩)
  have hq' := hq.trans hp'.thr
  have hq1 := (force1Q_source hφ hM (by linarith) hq').1
  have hr0 : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hr0
  have hP0 := cp_nonneg caps.PF
  refine ⟨fun u hu => ?_, companion_paid h hp'.hs hp'.hst hp'.ht hp'.len hp'.onPrefix
    (by linarith) hM hq' (by positivity) hκ⟩
  have hu0 : 0 ≤ u := hp'.hs.trans hu.1
  have huT : ENNReal.ofReal u < Ty := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) hp'.ht
  refine (h0_slot_one h hr hu0 huT).trans ?_
  have ha : fastNorm 1 r g y u ≤ cp caps.PF := (hp'.onPrefix.1 u hu).1.trans (le_cp _)
  have hb := hnorm_nonneg 2 (PiF (actual r g y u))
  have hh0 : 0 ≤ h0Bd φ r g y u := (hnorm_nonneg _ _).trans (hp_one_le h hr hu0 huT).2
  have hk : 0 ≤ 2 ^ 10 * h0Bd φ r g y u / |r| := by positivity
  have h3 := mul_le_mul_of_nonneg_right ha hb
  have h4 := mul_le_mul_of_nonneg_left h3 hk
  have e : 2 ^ 10 * cp caps.PF * h0Bd φ r g y u / |r| * fastNorm 2 r g y u =
      2 ^ 10 * h0Bd φ r g y u / |r| * (cp caps.PF * fastNorm 2 r g y u) := by ring
  rw [e]
  exact h4

/-- **`X₁[h₀]` at weight two, after Young** ((8.10)): a share of the dissipation, and the
multiplier `(8 C_src ‖h₀‖₁/q)²` of `b_F²`, whose integral is bounded by `companion_le`. -/
theorem h0_joint_two (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (Fp r g y u)) :
    |2 * pair 2 (Fp r g y u) (X1op r (r * u) (hp r g y u) (Fp r g y u))| ≤
      1 / 64 * fastNorm 3 r g y u ^ 2 +
        (8 * H2.cSrc * h0Bd φ r g y u / |r|) ^ 2 * fastNorm 2 r g y u ^ 2 := by
  refine (h0_slot_two h hr hu huT hF3).trans ?_
  set x := 2 * H2.cSrc * h0Bd φ r g y u / |r| * fastNorm 2 r g y u with hx
  set c := fastNorm 3 r g y u
  have e1 : 2 * H2.cSrc * h0Bd φ r g y u / |r| * (fastNorm 2 r g y u * c) = x * c := by
    rw [hx]
    ring
  have e2 : (8 * H2.cSrc * h0Bd φ r g y u / |r|) ^ 2 * fastNorm 2 r g y u ^ 2 = 16 * x ^ 2 := by
    rw [hx]
    ring
  rw [e1, e2]
  nlinarith only [sq_nonneg (c / 8 - 4 * x)]

/-- `N̄`, `π` at the package: the force takes the share `1` of `(C_N X)²`, `(C_π X)²`. -/
theorem force1_joint_tolerance {X CN Cp : ℝ} (h : ActualSol μ φ r g y Ty)
    (hp : JointPiece 4 M q near (SlowOut C ex R Sl) r g y Ty caps s t) (hD : 1 ≤ D)
    (hq : force1Q φ D M caps ≤ q caps) (hX : 1 ≤ X) (hCN : 1 ≤ CN) (hCp : 1 ≤ Cp) :
    (∫ u in s..t, (2 * hBd φ r g y u) ^ 2) ≤ (CN * X) ^ 2 ∧
      (∫ u in s..t, 24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) ≤ (Cp * X) ^ 2 :=
  force1_tolerance h hp.onPrefix hp.hs hp.hst hp.ht hp.len hp.sup hD (hq.trans hp.thr) hX hCN hCp

end OVNS.Quant.Metric

end
