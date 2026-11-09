import OddViscousNS.Quant.Joint.Force.Link

/-!
# The whole `h₀` derivative (step J5, node N12)

`JOINT_METRIC_PROOF_V2.md` (2.5), (3.7), `TIMED_METRIC_PROOF_V2.md` (8.10),
`JOINT_ASSEMBLY_V4.md` §3: "the whole `h₀` derivative is either retained as its genuine form or paid
by the explicit J2 Young mass.  It is not removed."

`S_t + AS = −h + h₀`, `h = B(S, S)`: in Lean `slowNL = h₀ − B(S, S)`, `h₀ = hp`.  So the slow slots
of `insJ` split into `h₀` and `B(S, S)`, and `joint₁Q`, `joint₂Q` (`Force/Link.lean`) into

* `h0Part σ = 2⟨AˢF, X₁[h₀]F⟩ + ½ Re⟨z, D_S X₂[h₀] z⟩ + ½ Re⟨z, D_S Z[h₀] z⟩`, the genuine term;
* `joint₁R`, `joint₂R`: no `g`, no `H_ψ`, only `Q(x, x)` and the direction `B(S, S)`.

`joint1Q_split`, `joint2Q_split`, `ae_joint_full`: this at almost every time.

**The size.**  `form_dir`: a slow `H¹` direction in a slot of `X₂`, `Z`, at both weights, costs
`(C/q) ‖v‖₁ (W + b) e_σ²`.  This is `(3.7)` with no exterior derivative: the length `V` of the
direction is paid by `V ρ ≤ 2` (`Fam.Bd.ρa`, `ρb`), that is `VM ≤ Σ` of `(3.7)`, not by the
dissipation.  `DSX2Form_le` is the same bound at weight two; here it holds for both families and
both weights, so `X2diff_le`, `Zdiff_le` and the tail `DSX2_high_le` are not needed for `h₀`.  They
gain a power of `q`, which the direction `B(S, S)` needs, since `‖B(S, S)‖₁ ≍ M_∞ b` at every time;
`h₀` has size `R` in `L²_t`, and the plain bound is enough.

`h0Part_one_le`, `h0Part_two_le`: `|h0Part σ| ≤ x e_σ d_σ + y e_σ²`, `x ≍ ‖h₀‖₁/q`,
`y ≍ (W + b) ‖h₀‖₁/q`.  The whole derivative carries `‖h₀‖₁`, with its `L²_t` history.

`h0Part_young_one`, `h0Part_young_two` are (8.10), with `κ = 1 + W + c₄ b`:
`|h0Part σ| ≤ ζ d_σ² + (Ch0 κ ‖h₀‖₁/q)²/(4ζ) e_σ²`.  With `companion_clip`, the mass on any
subinterval is at most `(Ch0 κ H₀/q)²/(4ζ)`, which is the printed `O(q⁻² R⁶ L)`: `force0Y`, degree
`(0, 3)` in `H0Degree.lean`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (ae_inH3_split cubicHeat2)

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A slow `H¹` direction in a slot -/

namespace Fam

variable {𝔉 : Fam} {r : ℝ} {ρ : I3 → ℝ} {K₁ K₂ : ℝ}

/-- A slow direction in the first slot. -/
lemma T_dir_left (hB : 𝔉.Bd r ρ K₁ K₂) (τ : ℝ) {h S z : Field} (hh' : PiS h = h) (hh0 : h 0 = 0)
    (hS' : PiS S = S) (hz' : PiF z = z) (x : I3) :
    ‖𝔉.T r x (z x.1) (z (inJ₂ x)) (h x.2.1) (S x.2.2) τ‖ ≤
      2 * K₁ * (Phi₂ (nrm z) (nrm z) (dv h) (nrm S) x * E2 x) := by
  have hK₁ := hB.K₁0
  have nz : ∀ k, 0 ≤ nrm z k := fun _ => norm_nonneg _
  have nS : ∀ k, 0 ≤ nrm S k := fun _ => norm_nonneg _
  refine T_form_le hh' hS' hz' (fun x => mul_nonneg (by positivity)
    (Phi₂_E2_nonneg nz nz (dv_nonneg h) nS x)) (fun x hx => ?_) x
  refine (norm_T_le hB hx).trans ?_
  have h1 := dv_ratio hh0 x.2.1 (hB.ρa x hx)
  have hE := E2_nonneg x
  have h2 := mul_le_mul_of_nonneg_right h1 (by positivity :
    0 ≤ ‖z x.1‖ * ‖z (inJ₂ x)‖ * ‖S x.2.2‖ * E2 x)
  have h3 := mul_le_mul_of_nonneg_left h2 hK₁
  calc _ = K₁ * (‖h x.2.1‖ * ρ x * (‖z x.1‖ * ‖z (inJ₂ x)‖ * ‖S x.2.2‖ * E2 x)) := by
        ring
    _ ≤ _ := h3
    _ = _ := by
        simp only [Phi₂, nrm]
        ring

/-- A slow direction in the second slot. -/
lemma T_dir_right (hB : 𝔉.Bd r ρ K₁ K₂) (τ : ℝ) {h S z : Field} (hh' : PiS h = h) (hh0 : h 0 = 0)
    (hS' : PiS S = S) (hz' : PiF z = z) (x : I3) :
    ‖𝔉.T r x (z x.1) (z (inJ₂ x)) (S x.2.1) (h x.2.2) τ‖ ≤
      2 * K₁ * (Phi₂ (nrm z) (nrm z) (nrm S) (dv h) x * E2 x) := by
  have hK₁ := hB.K₁0
  have nz : ∀ k, 0 ≤ nrm z k := fun _ => norm_nonneg _
  have nS : ∀ k, 0 ≤ nrm S k := fun _ => norm_nonneg _
  refine T_form_le hS' hh' hz' (fun x => mul_nonneg (by positivity)
    (Phi₂_E2_nonneg nz nz nS (dv_nonneg h) x)) (fun x hx => ?_) x
  refine (norm_T_le hB hx).trans ?_
  have h1 := dv_ratio hh0 x.2.2 (hB.ρb x hx)
  have hE := E2_nonneg x
  have h2 := mul_le_mul_of_nonneg_right h1 (by positivity :
    0 ≤ ‖z x.1‖ * ‖z (inJ₂ x)‖ * ‖S x.2.1‖ * E2 x)
  have h3 := mul_le_mul_of_nonneg_left h2 hK₁
  calc _ = K₁ * (‖h x.2.2‖ * ρ x * (‖z x.1‖ * ‖z (inJ₂ x)‖ * ‖S x.2.1‖ * E2 x)) := by
        ring
    _ ≤ _ := h3
    _ = _ := by
        simp only [Phi₂, nrm]
        ring

/-- **A slow `H¹` direction in a slot of a family**, at the weight of the family: `(3.7)` with no
exterior derivative. -/
theorem form_dir (hB : 𝔉.Bd r ρ K₁ K₂) (τ : ℝ) {h S z : Field} (hh : InH 1 h) (hh0 : h 0 = 0)
    (hh' : PiS h = h) (hS : MZ 2 S) (hS' : PiS S = S) (hz : Summable fun k => ‖z k‖ ^ 2)
    (hz' : PiF z = z) :
    (Summable fun x : I3 => 𝔉.T r x (z x.1) (z (inJ₂ x)) (h x.2.1) (S x.2.2) τ) ∧
      ‖𝔉.form r τ h S z z‖ ≤
        2 * K₁ * (l2n z * l2n z * cls2 (c4 * hnorm 1 h) (wiener S) (hnorm 1 h) (hnorm 2 S)) ∧
      (Summable fun x : I3 => 𝔉.T r x (z x.1) (z (inJ₂ x)) (S x.2.1) (h x.2.2) τ) ∧
      ‖𝔉.form r τ S h z z‖ ≤
        2 * K₁ * (l2n z * l2n z * cls2 (wiener S) (c4 * hnorm 1 h) (hnorm 2 S) (hnorm 1 h)) := by
  have α := l2B_nrm hz
  have D1 := l1B_dv hh
  have D2 := l2B_up_dv hh
  have W := l1B_nrm hS.inH
  have U := l2B_up hS.inH
  have hK : 0 ≤ 2 * K₁ := by
    have := hB.K₁0
    positivity
  have t1 := (pos2_E2 α α D1 W D2 U).const_mul hK
  have t2 := (pos2_E2 α α W D1 U D2).const_mul hK
  obtain ⟨s1, b1⟩ := form_le t1 (T_dir_left hB τ hh' hh0 hS' hz')
  obtain ⟨s2, b2⟩ := form_le t2 (T_dir_right hB τ hh' hh0 hS' hz')
  exact ⟨s1, b1, s2, b2⟩

/-- The source of a family is additive in the slow leaves. -/
structure AddS (𝔉 : Fam) : Prop where
  /-- The first leaf. -/
  add_l : ∀ x τ v v' w, 𝔉.Sr x τ (v + v') w = 𝔉.Sr x τ v w + 𝔉.Sr x τ v' w
  /-- The second leaf. -/
  add_r : ∀ x τ v w w', 𝔉.Sr x τ v (w + w') = 𝔉.Sr x τ v w + 𝔉.Sr x τ v w'

private lemma outerInv_add_f (r H : ℝ) (l j : Mode) (T T' : Blk) :
    outerInv r H l j (T + T') = outerInv r H l j T + outerInv r H l j T' := by
  simp only [outerInv, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, smul_add,
    Finset.sum_add_distrib]

/-- **The form is additive on the slow leaves**, on `H¹` directions. -/
theorem form_add_slow (hB : 𝔉.Bd r ρ K₁ K₂) (hA : 𝔉.AddS) (τ : ℝ) {h₁ h₂ S z : Field}
    (m₁ : MZ 1 h₁) (m₂ : MZ 1 h₂) (e₁ : PiS h₁ = h₁) (e₂ : PiS h₂ = h₂) (hS : MZ 2 S)
    (hS' : PiS S = S) (hz : Summable fun k => ‖z k‖ ^ 2) (hz' : PiF z = z) :
    𝔉.form r τ (h₁ + h₂) S z z = 𝔉.form r τ h₁ S z z + 𝔉.form r τ h₂ S z z ∧
      𝔉.form r τ S (h₁ + h₂) z z = 𝔉.form r τ S h₁ z z + 𝔉.form r τ S h₂ z z := by
  obtain ⟨s1, -, s1', -⟩ := form_dir hB τ m₁.inH m₁.mean e₁ hS hS' hz hz'
  obtain ⟨s2, -, s2', -⟩ := form_dir hB τ m₂.inH m₂.mean e₂ hS hS' hz hz'
  have l1 : ∀ x : I3, 𝔉.T r x (z x.1) (z (inJ₂ x)) ((h₁ + h₂) x.2.1) (S x.2.2) τ =
      𝔉.T r x (z x.1) (z (inJ₂ x)) (h₁ x.2.1) (S x.2.2) τ +
        𝔉.T r x (z x.1) (z (inJ₂ x)) (h₂ x.2.1) (S x.2.2) τ := fun x => by
    simp only [T, oTerm, Pi.add_apply, hA.add_l, outerInv_add_f, add_apply,
      inner_add_right]
  have l2 : ∀ x : I3, 𝔉.T r x (z x.1) (z (inJ₂ x)) (S x.2.1) ((h₁ + h₂) x.2.2) τ =
      𝔉.T r x (z x.1) (z (inJ₂ x)) (S x.2.1) (h₁ x.2.2) τ +
        𝔉.T r x (z x.1) (z (inJ₂ x)) (S x.2.1) (h₂ x.2.2) τ := fun x => by
    simp only [T, oTerm, Pi.add_apply, hA.add_r, outerInv_add_f, add_apply,
      inner_add_right]
  constructor
  · simp only [form, l1]
    exact s1.tsum_add s2
  · simp only [form, l2]
    exact s1'.tsum_add s2'

end Fam

lemma famX2_addS (s : ℕ) (r : ℝ) : (famX2 s r).AddS :=
  ⟨fun x τ => (tR_isBil s r τ x.1 x.2.1 x.2.2).add_l,
    fun x τ => (tR_isBil s r τ x.1 x.2.1 x.2.2).add_r⟩

lemma famZ_addS (s : ℕ) (r : ℝ) : (famZ s r).AddS :=
  ⟨fun x τ => (zR_isBil s r τ x.1 x.2.1 x.2.2).add_l,
    fun x τ => (zR_isBil s r τ x.1 x.2.1 x.2.2).add_r⟩

lemma PiS_Bslow (S : Field) : PiS (Bslow S) = Bslow S := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [Bslow, PiS, hk]

/-- `cls2` of a direction: the two orders. -/
lemma cls2_dir (f W b : ℝ) :
    cls2 (c4 * f) W f b = 3 * c4 * (f * (W + c4 * b)) ∧
      cls2 W (c4 * f) b f = 3 * c4 * (f * (W + c4 * b)) := by
  constructor <;>
  · unfold cls2
    ring

/-! ### The direction `h₀` along the solution -/

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}

/-- `⟨z, D_S Y[h₀] z⟩`, for a family `Y`. -/
def h0Y (𝔉 : Fam) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  𝔉.form r (r * u) (hp r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (hp r g y u) (zp s r g y u) (zp s r g y u)

/-- `⟨z, D_S Y[B(S, S)] z⟩`, for a family `Y`. -/
def hBY (𝔉 : Fam) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  𝔉.form r (r * u) (Bslow (Sp r g y u)) (Sp r g y u) (zp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (Bslow (Sp r g y u)) (zp s r g y u) (zp s r g y u)

/-- **The genuine term**: the whole `h₀` derivative, at the weight `σ`, as in `(2.5)`. -/
def h0Part (σ : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  2 * pair σ (Fp r g y u) (X1op r (r * u) (hp r g y u) (Fp r g y u)) +
    1 / 2 * (h0Y (famX2 σ r) σ r g y u).re + 1 / 2 * (h0Y (famZ σ r) σ r g y u).re

/-- `coreQ` without `h₀`. -/
def coreR (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  2 * (pair s (Fp r g y u) (X1op r (r * u) (Sp r g y u) (NQp r g y u)) +
    pair s (NQp r g y u) (X1op r (r * u) (Sp r g y u) (Fp r g y u)))

/-- `insQ` without `h₀`: the slow slots have the direction `−B(S, S)`. -/
def insR (𝔉 : Fam) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (zOf s (fastQ r g y u)) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zOf s (fastQ r g y u)) -
    hBY 𝔉 s r g y u

/-- **`joint1RHS` without the force and without `h₀`.** -/
def joint1R (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -pair 1 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) +
    coreR 1 r g y u - cubicHeat r (r * u) (Fp r g y u) +
    cubicD 1 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) +
    1 / 2 * (insR (famX2 1 r) 1 r g y u).re + 1 / 2 * (insR (famZ 1 r) 1 r g y u).re

/-- **`joint2RHS` without the force and without `h₀`.** -/
def joint2R (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -pair 2 (Fp r g y u) (Qres (Fp r g y u) (Fp r g y u)) +
    coreR 2 r g y u - cubicHeat2 r (r * u) (Fp r g y u) +
    cubicD 2 (-1) r (r * u) (Fp r g y u) (fastQ r g y u) +
    1 / 2 * (insR (famX2 2 r) 2 r g y u).re + 1 / 2 * (insR (famZ 2 r) 2 r g y u).re

/-- The hypotheses of `Fam.form_dir` along the solution. -/
private lemma path_data {s : ℕ} (hs : s = 1 ∨ s = 2) (h : ActualSol μ φ r g y Ty) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    MZ 2 (Sp r g y u) ∧ PiS (Sp r g y u) = Sp r g y u ∧
      (Summable fun k => ‖zp s r g y u k‖ ^ 2) ∧ PiF (zp s r g y u) = zp s r g y u ∧
      l2n (zp s r g y u) = hnorm s (Fp r g y u) := by
  have hx := actual_adm h hu huT
  have h2 : ((s : ℕ) : ℝ) ≤ 2 := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨z1, z2⟩ := l2_zOf (hx.PiF.inH.mono h2) hx.PiF.mean
  exact ⟨hx.PiS.mz, Fam.PiS_Sp r g y u, z1, Fam.PiF_zp s r g y u, z2⟩

/-- **The split of the slow slots**: `slowNL = h₀ − B(S, S)` in the two slots of a family. -/
theorem slow_slots_split {𝔉 : Fam} {ρ : I3 → ℝ} {K₁ K₂ : ℝ} {s : ℕ} (hs : s = 1 ∨ s = 2)
    (hB : 𝔉.Bd r ρ K₁ K₂) (hA : 𝔉.AddS) (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hS3 : InH 3 (Sp r g y u)) :
    𝔉.form r (r * u) (slowNL r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u) +
        𝔉.form r (r * u) (Sp r g y u) (slowNL r g y u) (zp s r g y u) (zp s r g y u) =
      h0Y 𝔉 s r g y u - hBY 𝔉 s r g y u := by
  obtain ⟨hS, hS', hz, hz', -⟩ := path_data hs h hu huT
  have hSM : MZ 3 (Sp r g y u) := ⟨hS3, hS.mean⟩
  have mB : MZ 1 (Bslow (Sp r g y u)) := (mz_Bslow hSM).mono' (by norm_num)
  obtain ⟨M, -, hM⟩ := Fam.path_sup h hr hu (b := u) huT
  obtain ⟨-, -, -, -, -, hN1, -, -, hN0⟩ := hM u ⟨le_rfl, le_rfl⟩
  have mN : MZ 1 (slowNL r g y u) := ⟨hN1, hN0⟩
  obtain ⟨e1, e2⟩ := Fam.form_add_slow (τ := r * u) hB hA mN mB (PiS_slowNL u)
    (PiS_Bslow _) hS hS' hz hz'
  have e0 : slowNL r g y u + Bslow (Sp r g y u) = hp r g y u := rfl
  rw [e0] at e1 e2
  simp only [h0Y, hBY, e1, e2]
  ring

/-- **`joint₁Q` splits**: the whole `h₀` derivative leaves. -/
theorem joint1Q_split (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hS3 : InH 3 (Sp r g y u)) :
    joint1Q r g y u = joint1R r g y u + h0Part 1 r g y u := by
  have e1 := slow_slots_split (s := 1) (Or.inl rfl) (famX2_bd (Or.inl rfl) hr) (famX2_addS 1 r) h
    hr hu huT hS3
  have e2 := slow_slots_split (s := 1) (Or.inl rfl) (famZ_bd (Or.inl rfl) hr) (famZ_addS 1 r) h
    hr hu huT hS3
  have e3 : insQ (famX2 1 r) 1 r g y u =
      insR (famX2 1 r) 1 r g y u + h0Y (famX2 1 r) 1 r g y u := by
    simp only [insQ, insR, add_assoc] at e1 ⊢
    rw [e1]
    ring
  have e4 : insQ (famZ 1 r) 1 r g y u = insR (famZ 1 r) 1 r g y u + h0Y (famZ 1 r) 1 r g y u := by
    simp only [insQ, insR, add_assoc] at e2 ⊢
    rw [e2]
    ring
  unfold joint1Q joint1R h0Part coreQ coreR
  rw [e3, e4, Complex.add_re, Complex.add_re]
  simp only [Nat.cast_one]
  ring

/-- **`joint₂Q` splits**: the whole `h₀` derivative leaves. -/
theorem joint2Q_split (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hS3 : InH 3 (Sp r g y u)) :
    joint2Q r g y u = joint2R r g y u + h0Part 2 r g y u := by
  have e1 := slow_slots_split (s := 2) (Or.inr rfl) (famX2_bd (Or.inr rfl) hr) (famX2_addS 2 r) h
    hr hu huT hS3
  have e2 := slow_slots_split (s := 2) (Or.inr rfl) (famZ_bd (Or.inr rfl) hr) (famZ_addS 2 r) h
    hr hu huT hS3
  have e3 : insQ (famX2 2 r) 2 r g y u =
      insR (famX2 2 r) 2 r g y u + h0Y (famX2 2 r) 2 r g y u := by
    simp only [insQ, insR, add_assoc] at e1 ⊢
    rw [e1]
    ring
  have e4 : insQ (famZ 2 r) 2 r g y u = insR (famZ 2 r) 2 r g y u + h0Y (famZ 2 r) 2 r g y u := by
    simp only [insQ, insR, add_assoc] at e2 ⊢
    rw [e2]
    ring
  unfold joint2Q joint2R h0Part coreQ coreR
  rw [e3, e4, Complex.add_re, Complex.add_re]
  simp only [Nat.cast_ofNat]
  ring

/-- **The full splitting of the right sides, at almost every time.** -/
theorem ae_joint_full (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    ∀ᵐ u ∂(volume.restrict (Icc a b)),
      joint1RHS r g y u = joint1R r g y u + h0Part 1 r g y u + forceS 1 r g y u ∧
        joint2RHS r g y u = joint2R r g y u + h0Part 2 r g y u + forceS 2 r g y u := by
  filter_upwards [ae_inH3_split h ha hab hb, ae_restrict_mem measurableSet_Icc] with u hu hm
  have hu0 := ha.trans hm.1
  have huT := lt_lifespan hm.2 hb
  rw [joint1RHS_split h hr hu0 huT hu.1 hu.2, joint2RHS_split h hr hu0 huT hu.1 hu.2,
    joint1Q_split h hr hu0 huT hu.2, joint2Q_split h hr hu0 huT hu.2]
  exact ⟨rfl, rfl⟩

end OVNS.Quant.Metric

end
