import OddViscousNS.Quant.Joint.Quartic.Main
import OddViscousNS.Quant.Joint.Assembly.Package

/-!
# The near and far differentials on a joint piece: the shares and the floor

What `JointPiece` hands to the differentials of `Joint/NearFar/`:
* `Floor`: `jointSlowFloor ≤ q` read as the three inequalities used here, and the filter sizes.
* `Shares`: `NearPaid (jointLN …) (jointLP …)` read summand by summand, without `Ex(1, R)`.
* `kN`, `kP`: the normalizations: `kN/η ≤ K_N`, `kP/η ≤ K_P`.

The direction `N_rest = fastRest` is `−2 Q_lo − Π_F Q(F,F) − Π_F H_ψ`.  `J4` removes the high mixed
near part (`cubicD_split_one`, `cubicD_split_two`).
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.NearFar

open OVNS.Quant.Metric OVNS.Quant.Quartic

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- The constant of the `H¹` product leaf (`hnorm_one_Qphase_le`). -/
def cQone : ℝ := 16 * Real.sqrt 5488

lemma cQone_nonneg : 0 ≤ cQone := by
  unfold cQone
  positivity

/-- **The normalization of `K_N`**, at both weights: `kN/η ≤ K_N`. -/
def kN : ℝ := 2 * nearC₀ * (2 * CLow 1 + 2 * CLow 2 + cQone + 16 * cI + 1)

/-- **The normalization of `K_P`**, at both weights: `kP/η ≤ K_P`. -/
def kP : ℝ := 2 * H2.cHeat2

lemma kN_pos : 0 < kN := by
  have h1 := CLow_nonneg 1
  have h2 := CLow_nonneg 2
  have h3 := cQone_nonneg
  have h4 := cI_pos
  have h5 := nearC₀_pos
  unfold kN
  positivity

lemma kP_pos : 0 < kP := by
  have h := H2.cHeat2_pos
  unfold kP
  positivity

/-! ### The floor -/

/-- The part of `jointSlowFloor ≤ q` read by the differentials. -/
structure Floor (X φ q : ℝ) (caps : Caps) : Prop where
  /-- `q` is large. -/
  one : 128 ≤ q
  /-- `φ/q` is small. -/
  phi : 2 ^ 15 * φ ≤ q
  /-- Role 18: `2¹¹ c₄ Y φ ≤ q`, `Y = totalY`. -/
  filt : 2 ^ 11 * c4 * totalY X caps * φ ≤ q

theorem Q0_of_slow {X R r : ℝ} {caps : Caps} (h : jointSlowFloor X R caps ≤ |r|) :
    64 * Q0Prime X (R - X) (kinJ0 Slow.slowC 36 X R caps) caps ≤ |r| :=
  (le_max_right _ _).trans h

theorem Floor.of_slow {X R r : ℝ} {caps : Caps} (hX : 0 ≤ X) (hφ : 0 ≤ R - X)
    (h : jointSlowFloor X R caps ≤ |r|) : Floor X (R - X) |r| caps := by
  have h1 := Q0_of_slow h
  have h2 : rootFloor X (R - X) caps ≤ |r| / 64 := by
    have : rootFloor X (R - X) caps ≤ Q0Prime X (R - X) (kinJ0 Slow.slowC 36 X R caps) caps :=
      le_max_left _ _
    linarith
  set φ := R - X
  set Y := totalY X caps with hY
  have hc := c4_pos
  have hy := cp_nonneg caps.yF
  have hB := cp_nonneg caps.BS
  have hY0 : 0 ≤ Y := by
    have : Y = 2 * (1 + X + cp caps.yF + cp caps.BS) := rfl
    linarith
  have hYφ : 0 ≤ 2 ^ 5 * c4 * Y * φ := by positivity
  have hyy : 0 ≤ 2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 := by positivity
  unfold rootFloor at h2
  refine ⟨by linarith only [h2, hφ, hYφ, hyy, hY0], by linarith only [h2, hφ, hYφ, hyy, hY0], ?_⟩
  linarith only [h2, hφ, hYφ, hyy, hY0]

section Sizes

variable {X q : ℝ} {caps : Caps}

lemma Floor.q_pos (h : Floor X φ q caps) : 0 < q := by linarith [h.one]

/-- `64 c₄ φ/q ≤ 1/64`. -/
lemma Floor.Eq_le (h : Floor X φ q caps) (hX : 0 ≤ X) (hφ : 0 ≤ φ) :
    64 * c4 * φ / q ≤ 1 / 64 := by
  have hq := h.q_pos
  have hc := c4_pos
  have hY : 2 ≤ totalY X caps := by
    have : totalY X caps = 2 * (1 + X + cp caps.yF + cp caps.BS) := rfl
    have := cp_nonneg caps.yF
    have := cp_nonneg caps.BS
    linarith
  have h1 := mul_le_mul_of_nonneg_right hY (by positivity : 0 ≤ 2 ^ 11 * c4 * φ)
  have h2 := h.filt
  rw [div_le_iff₀ hq]
  nlinarith only [h1, h2]

/-- `(64 c₄ φ/q) y ≤ 1/64`. -/
lemma Floor.Eq_y_le (h : Floor X φ q caps) (hX : 0 ≤ X) (hφ : 0 ≤ φ) :
    64 * c4 * φ / q * cp caps.yF ≤ 1 / 64 := by
  have hq := h.q_pos
  have hc := c4_pos
  have hY : 2 * cp caps.yF ≤ totalY X caps := by
    have : totalY X caps = 2 * (1 + X + cp caps.yF + cp caps.BS) := rfl
    have := cp_nonneg caps.yF
    have := cp_nonneg caps.BS
    linarith
  have h1 := mul_le_mul_of_nonneg_right hY (by positivity : 0 ≤ 2 ^ 11 * c4 * φ)
  have h2 := h.filt
  have e : 64 * c4 * φ / q * cp caps.yF = 64 * c4 * φ * cp caps.yF / q := by ring
  rw [e, div_le_iff₀ hq]
  nlinarith only [h1, h2]

/-- `64 c₄ φ²/q² ≤ 1/64`. -/
lemma Floor.Gq_le {r : ℝ} (h : Floor X φ |r| caps) (hX : 0 ≤ X) (hφ : 0 ≤ φ) :
    64 * c4 * φ ^ 2 / r ^ 2 ≤ 1 / 64 := by
  have hq := h.q_pos
  have h1 := h.Eq_le hX hφ
  have h2 : φ / |r| ≤ 1 := by
    rw [div_le_one hq]
    have := h.phi
    nlinarith only [this, hφ]
  have hc := c4_pos
  have h0 : 0 ≤ 64 * c4 * φ / |r| := by positivity
  have e : 64 * c4 * φ ^ 2 / r ^ 2 = 64 * c4 * φ / |r| * (φ / |r|) := by
    rw [← sq_abs r]
    field_simp
  rw [e]
  nlinarith only [h0, h1, h2]

end Sizes

/-! ### The shares -/

section Shares

variable {KN KP CS cS R₀ X R M q : ℝ} {caps : Caps}

/-- `NearPaid`, read summand by summand, with `Ex(1, R) ≥ 1` dropped. -/
structure Shares (KN KP M q : ℝ) (caps : Caps) : Prop where
  /-- The low mixed direction: `K_N N M y ≤ 1`. -/
  low : KN * (nearN q * (M * cp caps.yF)) ≤ 1
  /-- The purefast direction: `K_N N √P y^{3/2} ≤ 1`. -/
  pure : KN * (nearN q * (Real.sqrt (cp caps.PF) * cp caps.yF ^ ((3 : ℝ) / 2))) ≤ 1
  /-- The floor: `K_N N ≤ 1`. -/
  flr : KN * nearN q ≤ 1
  /-- The proper static and heats: `K_P P y ≤ 1`. -/
  stat : KP * (nearP q * cp caps.yF) ≤ 1

private lemma drop_ex {K E x n : ℝ} (hK : 0 ≤ K) (hE : 1 ≤ E) (hx : 0 ≤ x) (hn : 0 ≤ n)
    (h : K * E * x * n ≤ 1) : K * (n * x) ≤ 1 := by
  have h0 : 0 ≤ K * (n * x) := by positivity
  have h1 := mul_le_mul_of_nonneg_right hE h0
  nlinarith only [h, h1]

theorem Shares.of_paid (hdom : JDom R₀ X R) (hKN : 0 ≤ KN) (hKP : 0 ≤ KP) (hCS : 0 ≤ CS)
    (hq : 0 ≤ q)
    (h : NearPaid (jointLN KN CS cS X R) (jointLP KP X R) nearN nearP caps q) :
    Shares KN KP (CS * Ex cS R * R) q caps := by
  have hN := nearN_nonneg q
  have hP : 0 ≤ nearP q := nearP_nonneg hq
  obtain ⟨n1, n2, n3⟩ := native_shares hKN hCS hdom hN h.1
  obtain ⟨-, p2, -⟩ := proper_shares hKP hdom hP h.2
  have hE : 1 ≤ Ex 1 R := hdom.one_le_Ex zero_le_one
  have hEx := Ex_pos cS R
  have hR := hdom.R_pos
  have hy := cp_nonneg caps.yF
  have hPc := cp_nonneg caps.PF
  have hQ1 : 1 ≤ jointQ X R ^ ((1 : ℝ) / 2) := by
    have h1 : 1 ≤ jointQ X R := by linarith [hdom.R_le_Q, hdom.one_lt_R]
    exact Real.one_le_rpow h1 (by norm_num)
  refine ⟨drop_ex hKN hE (by positivity) hN n1, drop_ex hKN hE (by positivity) hN n2, ?_,
    drop_ex hKP hE hy hP p2⟩
  have h3 := drop_ex hKN hE (by positivity) hN n3
  have h4 : 0 ≤ KN * nearN q := by positivity
  have h5 := mul_le_mul_of_nonneg_left hQ1 h4
  nlinarith only [h3, h5]

end Shares

/-- `a₁ x₁ + a₂ x₂ + a₃ x₃ ≤ η` from the three shares `K xᵢ ≤ 1`. -/
lemma share_sum {K x₁ x₂ x₃ a₁ a₂ a₃ c η : ℝ} (hK : 0 < K) (hη : 0 < η) (h₁ : K * x₁ ≤ 1)
    (h₂ : K * x₂ ≤ 1) (h₃ : K * x₃ ≤ 1) (a₁0 : 0 ≤ a₁) (a₂0 : 0 ≤ a₂) (a₃0 : 0 ≤ a₃)
    (hc : a₁ + a₂ + a₃ ≤ c) (hKc : c / η ≤ K) : a₁ * x₁ + a₂ * x₂ + a₃ * x₃ ≤ η := by
  have h1 : c ≤ K * η := by
    rw [div_le_iff₀ hη] at hKc
    exact hKc
  have h2 : K * (a₁ * x₁ + a₂ * x₂ + a₃ * x₃) ≤ K * η := by
    have t1 := mul_le_mul_of_nonneg_left h₁ a₁0
    have t2 := mul_le_mul_of_nonneg_left h₂ a₂0
    have t3 := mul_le_mul_of_nonneg_left h₃ a₃0
    nlinarith only [t1, t2, t3, hc, h1]
  exact le_of_mul_le_mul_left h2 hK

/-- A single share. -/
lemma share_one {c₀ c K x η : ℝ} (hη : 0 < η) (hK : c₀ / η ≤ K) (hc : c ≤ c₀) (hx : 0 ≤ x)
    (h : K * x ≤ 1) : c * x ≤ η := by
  have h1 : c₀ ≤ K * η := by
    rw [div_le_iff₀ hη] at hK
    exact hK
  have h2 := mul_le_mul_of_nonneg_right hc hx
  have h3 := mul_le_mul_of_nonneg_right h1 hx
  have h4 := mul_le_mul_of_nonneg_right h hη.le
  nlinarith only [h2, h3, h4]

/-! ### The direction `N_rest` -/

lemma fastRest_zero (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) : fastRest r g y u 0 = 0 := by
  rw [← PiF_fastRest h hu huT]
  simp [PiF]

lemma isReal_fastRest (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) : IsReal (fastRest r g y u) := by
  have hR := isReal_Qhi (r * u) (Sp_adm h hu huT) (Fp_adm h hu huT)
  rw [fastRest_eq h hu huT]
  exact IsReal.add'' (isReal_fastNL h hu huT) (IsReal.add'' hR hR)

end OVNS.Quant.NearFar

end
