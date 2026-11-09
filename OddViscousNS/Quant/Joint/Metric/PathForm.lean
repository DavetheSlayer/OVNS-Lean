import OddViscousNS.Quant.Joint.Metric.PathTerm
import OddViscousNS.Quant.Joint.Metric.Slots
import OddViscousNS.Quant.Joint.Metric.StaticForm

/-!
# The two-leaf metric forms on the actual path (step J5, node N13)

The identity of a form `⟨z, O(S, S) z⟩` along the actual solution, for a family `O` of blocks with
outer heat `Σ`, from `term_hasDeriv` and the dominated FTC `integral_tsum_deriv_ae`.  `Fam` is the
abstract family: a source `Sr`, covariant on the slow labels, and its value at `τ = 0`, bilinear in
the two leaves.  `Fam.Bd` is the only analysis: the block bound `K₁ ρ f g E₂`, the source bound
`K₂ (L + P₁ + P₂) f g E₂`, and the ratio `ρ` against the lengths.  `X₂`, `Z` are instances
(`PathX2.lean`).

## What is dominated, and by what
The solution is `C_t H² ∩ L²_t H³`, so `z' ∉ ℓ²`.  The derivative family is split as the source plus
four insertions, and each is summable: the insertion `N_F = A^{s/2} fastNL` costs one more derivative
than `ℓ²`, paid by `ρ` against the length (`|l| ρ ≤ 2`, the "output half"), with `fastNL ∈ H¹`
uniformly in time; `slowNL ∈ H¹` likewise, by `|a| ρ ≤ 2` (the "genuine direction" of Body 12 §7).
Only the source needs an `H³` time: it is linear in `‖F‖₃ + ‖S‖₃`, whence `L¹` in time.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (integral_tsum_deriv_ae summable_wtd_one sobWeight_three Qm_one_le
  exists_Qphase_one_bound ae_inH3_split fast_h2_law slow_c3_integrable)

noncomputable section

namespace OVNS.Quant.Metric

/-- The labels on which a block can be nonzero. -/
def Act (x : I3) : Prop := x.2.1 2 = 0 ∧ x.2.2 2 = 0 ∧ inJ₂ x 2 ≠ 0

/-- The outer heat at `x`. -/
def Hx (x : I3) : ℝ := heat4 x.1 (inJ₂ x) x.2.1 x.2.2

/-- A family of blocks with outer heat `Σ`. -/
structure Fam where
  /-- The source. -/
  Sr : I3 → ℝ → V3 → V3 → Blk
  /-- The source at `τ = 0`, as a bilinear map of the leaves. -/
  Sr0 : I3 → V3 →L[ℂ] V3 →L[ℂ] Blk
  /-- Covariance on the slow labels. -/
  cov : ∀ x : I3, x.2.1 2 = 0 → x.2.2 2 = 0 → ∀ (τ : ℝ) (v w : V3) (c e : Sgn) (y : V3),
    hel c x.1 (Sr x τ v w (hel e (inJ₂ x) y)) =
      Complex.exp (Complex.I * (τ * outerPhi c e x.1 (inJ₂ x) : ℝ)) •
        hel c x.1 (Sr0 x v w (hel e (inJ₂ x) y))
  zero_l : ∀ x τ w, Sr x τ 0 w = 0
  zero_r : ∀ x τ v, Sr x τ v 0 = 0

namespace Fam

variable (𝔉 : Fam)

/-- A term of the form. -/
def T (r : ℝ) (x : I3) (G F v w : V3) (τ : ℝ) : ℂ :=
  oTerm r (Hx x) x.1 (inJ₂ x) (𝔉.Sr x) G F v w τ

/-- The form `⟨G, O(f, g) F⟩`. -/
def form (r τ : ℝ) (f g G F : Field) : ℂ :=
  ∑' x : I3, 𝔉.T r x (G x.1) (F (inJ₂ x)) (f x.2.1) (g x.2.2) τ

/-- A term of the source form. -/
def srcT (x : I3) (G F v w : V3) (τ : ℝ) : ℂ :=
  inner ℂ G (leray x.1 (𝔉.Sr x τ v w (leray (inJ₂ x) F)))

/-- The source form `⟨G, P T(f, g) P F⟩`. -/
def src (τ : ℝ) (f g G F : Field) : ℂ :=
  ∑' x : I3, 𝔉.srcT x (G x.1) (F (inJ₂ x)) (f x.2.1) (g x.2.2) τ

/-- The analysis of a family. -/
structure Bd (r : ℝ) (ρ : I3 → ℝ) (K₁ K₂ : ℝ) : Prop where
  K₁0 : 0 ≤ K₁
  K₂0 : 0 ≤ K₂
  ρ0 : ∀ x, 0 ≤ ρ x
  ρ2 : ∀ x, Act x → ρ x ≤ 2
  ρl : ∀ x, Act x → absk x.1 * ρ x ≤ 2
  ρj : ∀ x, Act x → absk (inJ₂ x) * ρ x ≤ 2
  ρa : ∀ x, Act x → absk x.2.1 * ρ x ≤ 2
  ρb : ∀ x, Act x → absk x.2.2 * ρ x ≤ 2
  op : ∀ x, Act x → ∀ (τ : ℝ) (v w : V3),
    ‖outerInv r (Hx x) x.1 (inJ₂ x) (𝔉.Sr x τ v w)‖ ≤ K₁ * ρ x * (‖v‖ * ‖w‖) * E2 x
  source : ∀ x, Act x → ∀ (τ : ℝ) (v w : V3),
    ‖𝔉.Sr x τ v w‖ ≤ K₂ * (absk x.1 + absk x.2.1 + absk x.2.2) * (‖v‖ * ‖w‖) * E2 x

variable {𝔉}
variable {r τ : ℝ} {x : I3} {G F v w : V3}

lemma T_zero_l (r : ℝ) (x : I3) (G F w : V3) (τ : ℝ) : 𝔉.T r x G F 0 w τ = 0 := by
  simp [T, oTerm, 𝔉.zero_l, outerInv_zero]

lemma T_zero_r (r : ℝ) (x : I3) (G F v : V3) (τ : ℝ) : 𝔉.T r x G F v 0 τ = 0 := by
  simp [T, oTerm, 𝔉.zero_r, outerInv_zero]

lemma outerInv_zero_input (r H : ℝ) (l j : Mode) (T : Blk) : outerInv r H l j T 0 = 0 := map_zero _

lemma T_zero_F (r : ℝ) (x : I3) (G v w : V3) (τ : ℝ) : 𝔉.T r x G 0 v w τ = 0 := by
  simp [T, oTerm]

lemma srcT_zero_l (x : I3) (G F w : V3) (τ : ℝ) : 𝔉.srcT x G F 0 w τ = 0 := by
  have h : leray x.1 (0 : V3) = 0 := by simpa using leray_smul x.1 0 (0 : V3)
  simp [srcT, 𝔉.zero_l, h]

lemma srcT_zero_r (x : I3) (G F v : V3) (τ : ℝ) : 𝔉.srcT x G F v 0 τ = 0 := by
  have h : leray x.1 (0 : V3) = 0 := by simpa using leray_smul x.1 0 (0 : V3)
  simp [srcT, 𝔉.zero_r, h]

lemma srcT_zero_F (x : I3) (G v w : V3) (τ : ℝ) : 𝔉.srcT x G 0 v w τ = 0 := by
  have h : ∀ k : Mode, leray k (0 : V3) = 0 := fun k => by simpa using leray_smul k 0 (0 : V3)
  simp [srcT, h]

/-- The norm of a term on the active labels. -/
lemma norm_T_le {K₁ K₂ : ℝ} {ρ : I3 → ℝ} (hB : 𝔉.Bd r ρ K₁ K₂) (hx : Act x) :
    ‖𝔉.T r x G F v w τ‖ ≤ K₁ * (‖G‖ * ‖F‖ * (‖v‖ * ‖w‖) * ρ x * E2 x) := by
  refine (norm_inner_apply_le _ _ _).trans ?_
  have h1 := hB.op x hx τ v w
  calc _ ≤ ‖G‖ * ‖F‖ * (K₁ * ρ x * (‖v‖ * ‖w‖) * E2 x) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- The norm of a source term on the active labels. -/
lemma norm_srcT_le {K₁ K₂ : ℝ} {ρ : I3 → ℝ} (hB : 𝔉.Bd r ρ K₁ K₂) (hx : Act x) :
    ‖𝔉.srcT x G F v w τ‖ ≤ K₂ * (‖G‖ * ‖F‖ * (‖v‖ * ‖w‖) *
      (absk x.1 + absk x.2.1 + absk x.2.2) * E2 x) := by
  refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
  have h1 := hB.source x hx τ v w
  have h2 := (norm_leray_le x.1 (𝔉.Sr x τ v w (leray (inJ₂ x) F)))
  have h3 : ‖𝔉.Sr x τ v w (leray (inJ₂ x) F)‖ ≤ ‖𝔉.Sr x τ v w‖ * ‖F‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (norm_leray_le _ _)
      (norm_nonneg _))
  calc _ ≤ ‖G‖ * (‖𝔉.Sr x τ v w‖ * ‖F‖) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (norm_nonneg _)
    _ ≤ ‖G‖ * ((K₂ * (absk x.1 + absk x.2.1 + absk x.2.2) * (‖v‖ * ‖w‖) * E2 x) * ‖F‖) := by
        gcongr
    _ = _ := by ring

end Fam

/-! ### The positive forms of the five terms -/

variable {f₀ g₀ G₀ F₀ : Field}

/-- `E₂ ≥ 0`, on `Phi₂`. -/
lemma Phi₂_E2_nonneg {α β f₁ f₂ : Mode → ℝ} (hα : ∀ k, 0 ≤ α k) (hβ : ∀ k, 0 ≤ β k)
    (h1 : ∀ k, 0 ≤ f₁ k) (h2 : ∀ k, 0 ≤ f₂ k) (x : I3) : 0 ≤ Phi₂ α β f₁ f₂ x * E2 x :=
  mul_nonneg (Phi₂_nonneg hα hβ h1 h2 x) (E2_nonneg x)

/-- `L1B` of the gradient of an `H³` field. -/
lemma l1B_gr {S : Field} (hS : MZ 3 S) : L1B (gr S) (c4 * hnorm 3 S) := by
  obtain ⟨h1, h2⟩ := summable_wtd_one hS
  have e : gr S = wtd 1 S := by
    funext k
    simp [gr, wtd]
  rw [e]
  exact ⟨wtd_nonneg 1 S, h1, h2⟩

/-- `L2B` of `|p|³ S`. -/
lemma l2B_up_gr {S : Field} (hS : MZ 3 S) : L2B (up (gr S)) (hnorm 3 S) := by
  have e : ∀ k, up (gr S) k ^ 2 = sobWeight 3 k * ‖S k‖ ^ 2 := fun k => by
    rw [sobWeight_three, up, gr, ← absk_sq k]
    ring
  refine ⟨fun k => mul_nonneg (absSq_nonneg k) (gr_nonneg S k), ?_, ?_⟩
  · simp only [e]
    exact hS.inH
  · simp only [e, hnorm]
    exact le_rfl

/-- `L1B` of the genuine direction. -/
lemma l1B_dv {h : Field} (hh : InH 1 h) : L1B (dv h) (c4 * hnorm 1 h) := (l2B_gr hh).in2

/-- `L2B` of the genuine direction. -/
lemma l2B_up_dv {h : Field} (hh : InH 1 h) : L2B (up (dv h)) (hnorm 1 h) := by
  rw [up_dv]
  exact l2B_gr hh

/-- The ratio at an inserted fast leaf, at both weights. -/
lemma zOf_ratio {s : ℕ} (hs : s = 1 ∨ s = 2) (N : Field) (k : Mode) {ρ : ℝ} (hρ2 : ρ ≤ 2)
    (hρl : absk k * ρ ≤ 2) : ‖zOf s N k‖ * ρ ≤ 2 * gr N k := by
  have hK := absk_nonneg k
  have hN := norm_nonneg (N k)
  have hn : ‖zOf s N k‖ = absk k ^ s * ‖N k‖ := by
    simp only [zOf, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hK s)]
  rw [hn, gr]
  rcases hs with rfl | rfl
  · calc absk k ^ 1 * ‖N k‖ * ρ = (absk k * ‖N k‖) * ρ := by ring
      _ ≤ (absk k * ‖N k‖) * 2 := mul_le_mul_of_nonneg_left hρ2 (by positivity)
      _ = _ := by ring
  · calc absk k ^ 2 * ‖N k‖ * ρ = (absk k * ρ) * (absk k * ‖N k‖) := by ring
      _ ≤ 2 * (absk k * ‖N k‖) := mul_le_mul_of_nonneg_right hρl (by positivity)

/-- The ratio at an inserted slow leaf. -/
lemma dv_ratio {h : Field} (hh0 : h 0 = 0) (a : Mode) {ρ : ℝ} (hρa : absk a * ρ ≤ 2) :
    ‖h a‖ * ρ ≤ 2 * dv h a := by
  by_cases ha : a = 0
  · subst ha
    rw [hh0, norm_zero, zero_mul, dv_apply]
    simp [hh0]
  · have hP : 0 < absk a := lt_of_lt_of_le one_pos (one_le_absk ha)
    rw [dv_apply, div_eq_mul_inv]
    have h1 : ‖h a‖ * ρ = (absk a * ρ) * (‖h a‖ * (absk a)⁻¹) := by
      field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_right hρa (by positivity)

namespace Fam

variable {𝔉 : Fam} {r τ : ℝ} {ρ : I3 → ℝ} {K₁ K₂ : ℝ}

/-- A term vanishes off the active labels. -/
lemma T_form_le (hf : PiS f₀ = f₀) (hg : PiS g₀ = g₀) (hF : PiF F₀ = F₀) {B : I3 → ℝ}
    (hB0 : ∀ x, 0 ≤ B x)
    (h : ∀ x, Act x → ‖𝔉.T r x (G₀ x.1) (F₀ (inJ₂ x)) (f₀ x.2.1) (g₀ x.2.2) τ‖ ≤ B x) (x : I3) :
    ‖𝔉.T r x (G₀ x.1) (F₀ (inJ₂ x)) (f₀ x.2.1) (g₀ x.2.2) τ‖ ≤ B x := by
  by_cases ha : x.2.1 2 = 0
  · by_cases hb : x.2.2 2 = 0
    · by_cases hj : inJ₂ x 2 = 0
      · rw [fast_zero hF hj, T_zero_F, norm_zero]
        exact hB0 x
      · exact h x ⟨ha, hb, hj⟩
    · rw [slow_zero hg hb, T_zero_r, norm_zero]
      exact hB0 x
  · rw [slow_zero hf ha, T_zero_l, norm_zero]
    exact hB0 x

/-- A source term vanishes off the active labels. -/
lemma srcT_form_le (hf : PiS f₀ = f₀) (hg : PiS g₀ = g₀) (hF : PiF F₀ = F₀) {B : I3 → ℝ}
    (hB0 : ∀ x, 0 ≤ B x)
    (h : ∀ x, Act x → ‖𝔉.srcT x (G₀ x.1) (F₀ (inJ₂ x)) (f₀ x.2.1) (g₀ x.2.2) τ‖ ≤ B x) (x : I3) :
    ‖𝔉.srcT x (G₀ x.1) (F₀ (inJ₂ x)) (f₀ x.2.1) (g₀ x.2.2) τ‖ ≤ B x := by
  by_cases ha : x.2.1 2 = 0
  · by_cases hb : x.2.2 2 = 0
    · by_cases hj : inJ₂ x 2 = 0
      · rw [fast_zero hF hj, srcT_zero_F, norm_zero]
        exact hB0 x
      · exact h x ⟨ha, hb, hj⟩
    · rw [slow_zero hg hb, srcT_zero_r, norm_zero]
      exact hB0 x
  · rw [slow_zero hf ha, srcT_zero_l, norm_zero]
    exact hB0 x

/-- The majorant of the plain form. -/
def maj₀ (K₁ : ℝ) (G F f g : Field) (x : I3) : ℝ :=
  2 * K₁ * (Phi₂ (nrm G) (nrm F) (nrm f) (nrm g) x * E2 x)

lemma maj₀_nonneg (hK : 0 ≤ K₁) (G F f g : Field) (x : I3) : 0 ≤ maj₀ K₁ G F f g x :=
  mul_nonneg (by positivity) (Phi₂_E2_nonneg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) x)

/-- The plain form at a time. -/
lemma T_le_maj₀ (hB : 𝔉.Bd r ρ K₁ K₂) (hf : PiS f₀ = f₀) (hg : PiS g₀ = g₀) (hF : PiF F₀ = F₀)
    (x : I3) : ‖𝔉.T r x (G₀ x.1) (F₀ (inJ₂ x)) (f₀ x.2.1) (g₀ x.2.2) τ‖ ≤
      maj₀ K₁ G₀ F₀ f₀ g₀ x := by
  refine T_form_le hf hg hF (maj₀_nonneg hB.K₁0 _ _ _ _) (fun x hx => ?_) x
  refine (norm_T_le hB hx).trans ?_
  have hE := E2_nonneg x
  have h1 := hB.ρ2 x hx
  have hK := hB.K₁0
  have h2 : ‖G₀ x.1‖ * ‖F₀ (inJ₂ x)‖ * (‖f₀ x.2.1‖ * ‖g₀ x.2.2‖) * ρ x * E2 x ≤
      ‖G₀ x.1‖ * ‖F₀ (inJ₂ x)‖ * (‖f₀ x.2.1‖ * ‖g₀ x.2.2‖) * 2 * E2 x := by gcongr
  have h3 := mul_le_mul_of_nonneg_left h2 hK
  refine h3.trans (le_of_eq ?_)
  simp only [maj₀, Phi₂, nrm]
  ring

/-- `SB` of the plain majorant. -/
lemma sb_maj₀ {A B W₁ W₂ U₁ U₂ : ℝ} (hK : 0 ≤ K₁) (hG : L2B (nrm G₀) A) (hF : L2B (nrm F₀) B)
    (h1 : L1B (nrm f₀) W₁) (h2 : L1B (nrm g₀) W₂) (u1 : L2B (up (nrm f₀)) U₁)
    (u2 : L2B (up (nrm g₀)) U₂) :
    SB (maj₀ K₁ G₀ F₀ f₀ g₀) (2 * K₁ * (A * B * cls2 W₁ W₂ U₁ U₂)) :=
  (pos2_E2 hG hF h1 h2 u1 u2).const_mul (by positivity)

end Fam

/-! ### The actual path -/

/-- The slow field along the actual solution. -/
def Sp (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : Field := PiS (actual r g y u)

/-- The fast field along the actual solution. -/
def Fp (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : Field := PiF (actual r g y u)

/-- The energy coordinates along the actual solution. -/
def zp (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : Field := zOf s (Fp r g y u)

/-- The non-heat part of `z'`. -/
def Nzp (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : Field := zOf s (fastNL r g y u)

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

lemma zp_hasDeriv (h : ActualSol μ φ r g y Ty) (s : ℕ) (k : Mode) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    HasDerivWithinAt (fun v => zp s r g y v k)
      (((-absSq k : ℝ) : ℂ) • zp s r g y u k + Nzp s r g y u k) (Ici 0) u := by
  have h1 := (fast_mode h k hu huT).const_smul ((absk k ^ s : ℝ) : ℂ)
  refine h1.congr_deriv ?_
  rw [fastRHS_eq_lap]
  simp only [zp, Nzp, zOf, Fp, Pi.add_apply, Pi.neg_apply, lapF, Complex.ofReal_neg]
  module

lemma Sp_hasDeriv (h : ActualSol μ φ r g y Ty) (k : Mode) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    HasDerivWithinAt (fun v => Sp r g y v k)
      (((-absSq k : ℝ) : ℂ) • Sp r g y u k + slowNL r g y u k) (Ici 0) u := by
  refine (slow_mode h k hu huT).congr_deriv ?_
  rw [slowRHS_eq_lap]
  simp only [Sp, Pi.add_apply, Pi.neg_apply, lapF, Complex.ofReal_neg, neg_smul]

lemma fastNL_mode_continuousOn (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => fastNL r g y u k) (Icc 0 b) :=
  (continuousOn_PiF_Qphase_mode h hb hbT k).neg

lemma slowNL_mode_continuousOn (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => slowNL r g y u k) (Icc 0 b) :=
  (continuousOn_PiS_Qphase_mode h hb hbT k).neg.add continuousOn_const

/-! ### The five terms at a time -/

namespace Fam

variable {𝔉 : Fam} {τ : ℝ} {ρ : I3 → ℝ} {K₁ K₂ : ℝ}

/-- The derivative family. -/
def rhsT (𝔉 : Fam) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) (x : I3) : ℂ :=
  𝔉.srcT x (zp s r g y u x.1) (zp s r g y u (inJ₂ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2) (r * u) +
    𝔉.T r x (Nzp s r g y u x.1) (zp s r g y u (inJ₂ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2)
      (r * u) +
    𝔉.T r x (zp s r g y u x.1) (Nzp s r g y u (inJ₂ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2)
      (r * u) +
    𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ₂ x)) (slowNL r g y u x.2.1) (Sp r g y u x.2.2)
      (r * u) +
    𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ₂ x)) (Sp r g y u x.2.1) (slowNL r g y u x.2.2)
      (r * u)

/-- The integrand of the identity: the source and the four insertions. -/
def rhs (𝔉 : Fam) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  𝔉.src (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (Nzp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (Nzp s r g y u) +
    𝔉.form r (r * u) (slowNL r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u) +
    𝔉.form r (r * u) (Sp r g y u) (slowNL r g y u) (zp s r g y u) (zp s r g y u)

/-- The value of the form along the solution. -/
def val (𝔉 : Fam) (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℂ :=
  𝔉.form r (r * u) (Sp r g y u) (Sp r g y u) (zp s r g y u) (zp s r g y u)

/-- `PiS` and `PiF` of the path. -/
lemma PiS_Sp (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : PiS (Sp r g y u) = Sp r g y u := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [Sp, PiS, hk]

lemma PiF_Fp (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : PiF (Fp r g y u) = Fp r g y u := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [Fp, PiF, hk]

lemma PiF_zOf {s : ℕ} {F : Field} (hF : PiF F = F) : PiF (zOf s F) = zOf s F := by
  funext k
  by_cases hk : k 2 = 0
  · have : F k = 0 := fast_zero hF hk
    simp [PiF, hk, zOf, this]
  · simp [PiF, hk]

lemma PiF_zp (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    PiF (zp s r g y u) = zp s r g y u := PiF_zOf (PiF_Fp r g y u)

lemma PiF_Nzp (s : ℕ) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    PiF (Nzp s r g y u) = Nzp s r g y u := PiF_zOf (PiF_fastNL u)

/-- The five majorants at a time, with their sum. -/
def maj (K₁ K₂ : ℝ) (z N Ns S : Field) (x : I3) : ℝ :=
  K₂ * (Phi₂ (gr z) (nrm z) (nrm S) (nrm S) x * E2 x + Phi₂ (nrm z) (nrm z) (gr S) (nrm S) x * E2 x +
      Phi₂ (nrm z) (nrm z) (nrm S) (gr S) x * E2 x) +
    2 * K₁ * (Phi₂ (gr N) (nrm z) (nrm S) (nrm S) x * E2 x +
      Phi₂ (nrm z) (gr N) (nrm S) (nrm S) x * E2 x +
      Phi₂ (nrm z) (nrm z) (dv Ns) (nrm S) x * E2 x +
      Phi₂ (nrm z) (nrm z) (nrm S) (dv Ns) x * E2 x)

/-- `SB` of the sum of the majorants. -/
lemma sb_maj {z N Ns S : Field} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hz : Summable fun k => ‖z k‖ ^ 2) (hz1 : InH 1 z) (hN : InH 1 N) (hNs : InH 1 Ns)
    (hS : MZ 3 S) :
    SB (maj K₁ K₂ z N Ns S) (K₂ *
        (hnorm 1 z * l2n z * cls2 (wiener S) (wiener S) (hnorm 2 S) (hnorm 2 S) +
          l2n z * l2n z * cls2 (c4 * hnorm 3 S) (wiener S) (hnorm 3 S) (hnorm 2 S) +
          l2n z * l2n z * cls2 (wiener S) (c4 * hnorm 3 S) (hnorm 2 S) (hnorm 3 S)) +
      2 * K₁ * (hnorm 1 N * l2n z * cls2 (wiener S) (wiener S) (hnorm 2 S) (hnorm 2 S) +
        l2n z * hnorm 1 N * cls2 (wiener S) (wiener S) (hnorm 2 S) (hnorm 2 S) +
        l2n z * l2n z * cls2 (c4 * hnorm 1 Ns) (wiener S) (hnorm 1 Ns) (hnorm 2 S) +
        l2n z * l2n z * cls2 (wiener S) (c4 * hnorm 1 Ns) (hnorm 2 S) (hnorm 1 Ns))) := by
  have hS2 : MZ 2 S := hS.mono' (by norm_num)
  have α := l2B_nrm hz
  have α1 := l2B_gr hz1
  have N1 := l2B_gr hN
  have W := l1B_nrm hS2.inH
  have U := l2B_up hS2.inH
  have W1 := l1B_gr hS
  have U1 := l2B_up_gr hS
  have D1 := l1B_dv hNs
  have D2 := l2B_up_dv hNs
  have t1 := pos2_E2 α1 α W W U U
  have t2 := pos2_E2 α α W1 W U1 U
  have t3 := pos2_E2 α α W W1 U U1
  have t4 := pos2_E2 N1 α W W U U
  have t5 := pos2_E2 α N1 W W U U
  have t6 := pos2_E2 α α D1 W D2 U
  have t7 := pos2_E2 α α W D1 U D2
  exact (((t1.add t2).add t3).const_mul hK₂).add
    ((((t4.add t5).add t6).add t7).const_mul (by positivity))

/-- **The five terms of the derivative family are dominated** at a time. -/
lemma terms_le (hB : 𝔉.Bd r ρ K₁ K₂) {s : ℕ} (hs : s = 1 ∨ s = 2) (u : ℝ)
    (hNs0 : slowNL r g y u 0 = 0) (x : I3) :
    ‖𝔉.srcT x (zp s r g y u x.1) (zp s r g y u (inJ₂ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2)
        (r * u)‖ ≤ maj K₁ K₂ (zp s r g y u) (fastNL r g y u) (slowNL r g y u) (Sp r g y u) x ∧
    ‖𝔉.T r x (Nzp s r g y u x.1) (zp s r g y u (inJ₂ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2)
        (r * u)‖ ≤ maj K₁ K₂ (zp s r g y u) (fastNL r g y u) (slowNL r g y u) (Sp r g y u) x ∧
    ‖𝔉.T r x (zp s r g y u x.1) (Nzp s r g y u (inJ₂ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2)
        (r * u)‖ ≤ maj K₁ K₂ (zp s r g y u) (fastNL r g y u) (slowNL r g y u) (Sp r g y u) x ∧
    ‖𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ₂ x)) (slowNL r g y u x.2.1) (Sp r g y u x.2.2)
        (r * u)‖ ≤ maj K₁ K₂ (zp s r g y u) (fastNL r g y u) (slowNL r g y u) (Sp r g y u) x ∧
    ‖𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ₂ x)) (Sp r g y u x.2.1) (slowNL r g y u x.2.2)
        (r * u)‖ ≤ maj K₁ K₂ (zp s r g y u) (fastNL r g y u) (slowNL r g y u) (Sp r g y u) x := by
  set z := zp s r g y u with hz
  set N := fastNL r g y u with hN
  set Ns := slowNL r g y u with hNs
  set S := Sp r g y u with hS
  have hSs : PiS S = S := PiS_Sp r g y u
  have hNss : PiS Ns = Ns := PiS_slowNL u
  have hzf : PiF z = z := PiF_zp s r g y u
  have hNz : PiF (Nzp s r g y u) = Nzp s r g y u := PiF_Nzp s r g y u
  have hK₁ := hB.K₁0
  have hK₂ := hB.K₂0
  have nn : ∀ {A B C D : Mode → ℝ}, (∀ k, 0 ≤ A k) → (∀ k, 0 ≤ B k) → (∀ k, 0 ≤ C k) →
      (∀ k, 0 ≤ D k) → ∀ x, 0 ≤ Phi₂ A B C D x * E2 x := fun a b c d x => Phi₂_E2_nonneg a b c d x
  have nz : ∀ k, 0 ≤ nrm z k := fun _ => norm_nonneg _
  have nS : ∀ k, 0 ≤ nrm S k := fun _ => norm_nonneg _
  have gz := gr_nonneg z
  have gS := gr_nonneg S
  have gN := gr_nonneg N
  have dN := dv_nonneg Ns
  have t1 : ‖𝔉.srcT x (z x.1) (z (inJ₂ x)) (S x.2.1) (S x.2.2) (r * u)‖ ≤
      K₂ * (Phi₂ (gr z) (nrm z) (nrm S) (nrm S) x * E2 x +
        Phi₂ (nrm z) (nrm z) (gr S) (nrm S) x * E2 x +
        Phi₂ (nrm z) (nrm z) (nrm S) (gr S) x * E2 x) := by
    refine srcT_form_le hSs hSs hzf (fun x => mul_nonneg hK₂ (add_nonneg (add_nonneg
      (nn gz nz nS nS x) (nn nz nz gS nS x)) (nn nz nz nS gS x))) (fun x hx => ?_) x
    refine (norm_srcT_le hB hx).trans (le_of_eq ?_)
    simp only [Phi₂, nrm, gr]
    ring
  have t2 : ‖𝔉.T r x (Nzp s r g y u x.1) (z (inJ₂ x)) (S x.2.1) (S x.2.2) (r * u)‖ ≤
      2 * K₁ * (Phi₂ (gr N) (nrm z) (nrm S) (nrm S) x * E2 x) := by
    refine T_form_le hSs hSs hzf (fun x => mul_nonneg (by positivity) (nn gN nz nS nS x))
      (fun x hx => ?_) x
    refine (norm_T_le hB hx).trans ?_
    have h1 := zOf_ratio hs N x.1 (hB.ρ2 x hx) (hB.ρl x hx)
    have hE := E2_nonneg x
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity :
      0 ≤ ‖z (inJ₂ x)‖ * (‖S x.2.1‖ * ‖S x.2.2‖) * E2 x)
    have h3 := mul_le_mul_of_nonneg_left h2 hK₁
    calc _ = K₁ * (‖Nzp s r g y u x.1‖ * ρ x * (‖z (inJ₂ x)‖ * (‖S x.2.1‖ * ‖S x.2.2‖) * E2 x)) := by
          ring
      _ ≤ _ := h3
      _ = _ := by
          simp only [Phi₂, nrm]
          ring
  have t3 : ‖𝔉.T r x (z x.1) (Nzp s r g y u (inJ₂ x)) (S x.2.1) (S x.2.2) (r * u)‖ ≤
      2 * K₁ * (Phi₂ (nrm z) (gr N) (nrm S) (nrm S) x * E2 x) := by
    refine T_form_le hSs hSs hNz (fun x => mul_nonneg (by positivity) (nn nz gN nS nS x))
      (fun x hx => ?_) x
    refine (norm_T_le hB hx).trans ?_
    have h1 := zOf_ratio hs N (inJ₂ x) (hB.ρ2 x hx) (hB.ρj x hx)
    have hE := E2_nonneg x
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity :
      0 ≤ ‖z x.1‖ * (‖S x.2.1‖ * ‖S x.2.2‖) * E2 x)
    have h3 := mul_le_mul_of_nonneg_left h2 hK₁
    calc _ = K₁ * (‖Nzp s r g y u (inJ₂ x)‖ * ρ x * (‖z x.1‖ * (‖S x.2.1‖ * ‖S x.2.2‖) * E2 x)) := by
          ring
      _ ≤ _ := h3
      _ = _ := by
          simp only [Phi₂, nrm]
          ring
  have t4 : ‖𝔉.T r x (z x.1) (z (inJ₂ x)) (Ns x.2.1) (S x.2.2) (r * u)‖ ≤
      2 * K₁ * (Phi₂ (nrm z) (nrm z) (dv Ns) (nrm S) x * E2 x) := by
    refine T_form_le hNss hSs hzf (fun x => mul_nonneg (by positivity) (nn nz nz dN nS x))
      (fun x hx => ?_) x
    refine (norm_T_le hB hx).trans ?_
    have h1 := dv_ratio hNs0 x.2.1 (hB.ρa x hx)
    have hE := E2_nonneg x
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity :
      0 ≤ ‖z x.1‖ * ‖z (inJ₂ x)‖ * ‖S x.2.2‖ * E2 x)
    have h3 := mul_le_mul_of_nonneg_left h2 hK₁
    calc _ = K₁ * (‖Ns x.2.1‖ * ρ x * (‖z x.1‖ * ‖z (inJ₂ x)‖ * ‖S x.2.2‖ * E2 x)) := by
          ring
      _ ≤ _ := h3
      _ = _ := by
          simp only [Phi₂, nrm]
          ring
  have t5 : ‖𝔉.T r x (z x.1) (z (inJ₂ x)) (S x.2.1) (Ns x.2.2) (r * u)‖ ≤
      2 * K₁ * (Phi₂ (nrm z) (nrm z) (nrm S) (dv Ns) x * E2 x) := by
    refine T_form_le hSs hNss hzf (fun x => mul_nonneg (by positivity) (nn nz nz nS dN x))
      (fun x hx => ?_) x
    refine (norm_T_le hB hx).trans ?_
    have h1 := dv_ratio hNs0 x.2.2 (hB.ρb x hx)
    have hE := E2_nonneg x
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity :
      0 ≤ ‖z x.1‖ * ‖z (inJ₂ x)‖ * ‖S x.2.1‖ * E2 x)
    have h3 := mul_le_mul_of_nonneg_left h2 hK₁
    calc _ = K₁ * (‖Ns x.2.2‖ * ρ x * (‖z x.1‖ * ‖z (inJ₂ x)‖ * ‖S x.2.1‖ * E2 x)) := by
          ring
      _ ≤ _ := h3
      _ = _ := by
          simp only [Phi₂, nrm]
          ring
  have p1 := nn gz nz nS nS x
  have p2 := nn nz nz gS nS x
  have p3 := nn nz nz nS gS x
  have p4 := nn gN nz nS nS x
  have p5 := nn nz gN nS nS x
  have p6 := nn nz nz dN nS x
  have p7 := nn nz nz nS dN x
  have q1 := mul_nonneg hK₂ (add_nonneg (add_nonneg p1 p2) p3)
  have q2 := mul_nonneg hK₁ p4
  have q3 := mul_nonneg hK₁ p5
  have q4 := mul_nonneg hK₁ p6
  have q5 := mul_nonneg hK₁ p7
  simp only [maj]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine t1.trans ?_
    nlinarith only [q2, q3, q4, q5]
  · refine t2.trans ?_
    nlinarith only [q1, q3, q4, q5]
  · refine t3.trans ?_
    nlinarith only [q1, q2, q4, q5]
  · refine t4.trans ?_
    nlinarith only [q1, q2, q3, q5]
  · refine t5.trans ?_
    nlinarith only [q1, q2, q3, q4]

end Fam

end OVNS.Quant.Metric

end
