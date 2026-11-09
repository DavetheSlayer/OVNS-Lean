import OddViscousNS.Quant.Joint.Kinetic.GN
import OddViscousNS.Quant.Joint.Arith
import OddViscousNS.Quant.Energy.Kinetic.Main

/-!
# E4-J: the kinetic correction at the joint scale (step J3)

`kineticJoint : KineticJoint μ φ M (kinJThreshold φ M)` (`Joint/Interfaces.lean`, TeX eq.
quant-kinetic, eq. quant-kinetic-floor), and `kinJ0_le`, `kinJ0_below`: the threshold is `≲ R³` up
to the subpower on the joint caps, uniformly in `φ`.  No `sorry`; all constants absolute.

The functional is the fixed-force `W₀`, the identity is `W0_identity`; only the budget changes.
`W₀' = −2a_F² − 2⟨F,H_ψ⟩ − 2⟨S',N(F,F)⟩ − 4⟨S,N(F',F)⟩`, with
`S' = −AS − Π_S Q(y,y) + Π_S g` and `F' = −AF − Π_F Q(y,y)`.  Three changes against `Kinetic/Main`:
* sectors (`hnorm_PiS_Qyy`, `hnorm_PiF_Qyy`): `‖Π_S Q(y,y)‖₀ ≤ ‖Q(S,S)‖₀ + ‖Q(F,F)‖₀ + ‖H_ψ‖₀`,
  `‖Π_F Q(y,y)‖₀ ≤ 2‖Q(S,F)‖₀ + ‖Q(F,F)‖₀ + ‖H_ψ‖₀`.  The old budget kept `‖Q(y,y)‖₀`, and so paid
  `W_S ‖Q(S,S)‖₀` in a pairing where `Q(S,S)` does not occur (it costs `R^{9/2}` at the joint caps);
* physical products (`GN.lean`): `‖Q(S,S)‖₀ ≤ 3 M_∞ a_S`, `‖Q(S,F)‖₀ ≲ (M_∞ + √(M_∞ b_S)) a_F`;
* N15 (`hnorm_kinN_sob`): `‖N(F,F)‖₀ ≲ a_F²/q`, one derivative less than `hnorm_kinN_le`, so the
  sources `S'` are paid without the factor `y`.  The term `Q(F,F)` keeps `hnorm_kinN_le` (`y²`).
The filter is paid once: `h₀ ≤ 1/16` (`filter_alg`), so no `φ`-monomial meets `W_S` or `y` twice.

## The threshold against `Q = U R³`, at `(W, A, y, P, m, B, φ) ≍ (R^{3/2}, R^{3/2}, T, U, R, R², R)`
Paid through `M_∞`, and the only monomial that must be: `W_S √(M_∞ B_S)`, degree `R³`.  With the
caps alone it is `W_S √(A_S B_S) ≍ R^{13/4}`, or `W_S A_S y ≍ U^{1/2} R^{7/2}` by Young.  The others
through `M_∞` are sharpenings: `M_∞ A_S`, `W_S M_∞` are `R^{5/2}`, and would be `R³` with `W_S`.
All the others are below: `φ W, φ A ≍ R^{5/2}`, `W y ≍ U^{1/2} R²`, `B ≍ R²`, `y², φ P ≍ U R`,
`φ y ≍ U^{1/2} R^{3/2}`, `W ≍ R^{3/2}`, `φ ≍ R`.  So `q₀ ≲ R³ Ex`, no factor `U`: tied with `Q` only
at `U ≍ 1`, as in the survey §1.2.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ENNReal

noncomputable section

namespace OVNS.Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### The threshold -/

/-- `M_∞ + D₄`, with `D₄² = M_∞ b_S` (`GN.hnorm_Qphase_mixed`). -/
def kinD (M B : ℝ) : ℝ := M + Real.sqrt (M * B)

/-- The size of the force filter: `‖H_ψ‖₀ ≤ (4φ/q) kinJG`. -/
def kinJG (caps : Caps) : ℝ :=
  cp caps.WS + c4 * cp caps.yF + c4 * (cp caps.AS + cp caps.PF + 1)

/-- The raised floor `W_S(M_∞ + D₄ + y) + M_∞ A_S + y²` (TeX eq. quant-kinetic-floor), plus the
linear monomials `B_S`, `φ`, `1`; every constant is absolute. -/
def kinJFloor (φ M : ℝ) (caps : Caps) : ℝ :=
  8 * c4 * (cp caps.BS + 3 * cp M * cp caps.AS + 1 + φ) + 16 * c4 ^ 2 * cp caps.yF ^ 2 +
    16 * cp caps.WS * (8 * (1 + c4) * kinD (cp M) (cp caps.BS) + 2 * c4 * cp caps.yF)

/-- **The joint kinetic threshold** `q₀(φ, M, caps)`. -/
def kinJThreshold (φ M : ℝ) (caps : Caps) : ℝ :=
  1 + 16 * cp caps.WS + 4 * φ + 64 * φ * kinJG caps + 32 * cp caps.WS * (cp caps.yF + 1) +
    kinJFloor φ M caps

lemma kinJG_nonneg (caps : Caps) : 0 ≤ kinJG caps := by
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.AS
  have := cp_nonneg caps.PF
  have := c4_pos
  unfold kinJG
  positivity

lemma kinD_nonneg {M B : ℝ} (hM : 0 ≤ M) : 0 ≤ kinD M B :=
  add_nonneg hM (Real.sqrt_nonneg _)

lemma kinJFloor_nonneg (hφ : 0 ≤ φ) (M : ℝ) (caps : Caps) : 0 ≤ kinJFloor φ M caps := by
  have h1 := cp_nonneg caps.WS
  have h2 := cp_nonneg caps.yF
  have h3 := cp_nonneg caps.AS
  have h4 := cp_nonneg caps.BS
  have h5 := cp_nonneg M
  have h6 := c4_pos
  have h7 := kinD_nonneg (B := cp caps.BS) h5
  unfold kinJFloor
  positivity

lemma one_le_kinJ (hφ : 0 ≤ φ) (M : ℝ) (caps : Caps) : 1 ≤ kinJThreshold φ M caps := by
  have h1 := cp_nonneg caps.WS
  have h2 := cp_nonneg caps.yF
  have h3 := kinJG_nonneg caps
  have h4 := kinJFloor_nonneg hφ M caps
  have h5 : 0 ≤ 64 * φ * kinJG caps := by positivity
  have h6 : 0 ≤ 32 * cp caps.WS * (cp caps.yF + 1) := by positivity
  unfold kinJThreshold
  linarith

lemma thr_parts (hφ : 0 ≤ φ) (M : ℝ) (caps : Caps) :
    16 * cp caps.WS ≤ kinJThreshold φ M caps ∧ 4 * φ ≤ kinJThreshold φ M caps ∧
      64 * φ * kinJG caps ≤ kinJThreshold φ M caps ∧
      32 * cp caps.WS * (cp caps.yF + 1) ≤ kinJThreshold φ M caps ∧
      kinJFloor φ M caps ≤ kinJThreshold φ M caps := by
  have h1 := cp_nonneg caps.WS
  have h2 := cp_nonneg caps.yF
  have h3 := kinJG_nonneg caps
  have h4 := kinJFloor_nonneg hφ M caps
  have h5 : 0 ≤ 64 * φ * kinJG caps := by positivity
  have h6 : 0 ≤ 32 * cp caps.WS * (cp caps.yF + 1) := by positivity
  unfold kinJThreshold
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### Coercivity and the true-zero bound -/

/-- `|r| ≥ 1`, `φ ≥ 0` once the threshold is paid. -/
lemma phi_nonneg_of_sol (h : ActualSol μ φ r g y Ty) : 0 ≤ φ :=
  (hnorm_nonneg _ _).trans h.force_le

theorem W0_coercive_J (h : ActualSol μ φ r g y Ty) {M : ℝ} {caps : Caps}
    {s t : ℝ} (hP : PrefixHyp (kinJThreshold φ M) r g y Ty caps s t) {u : ℝ} (hu : u ∈ Icc s t) :
    3 / 4 * fastNorm 0 r g y u ^ 2 ≤ W0 r g y u ∧ W0 r g y u ≤ 5 / 4 * fastNorm 0 r g y u ^ 2 := by
  have hφ := phi_nonneg_of_sol h
  have hr1 := (one_le_kinJ hφ M caps).trans hP.thr
  have hr : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr1; linarith
  have hu0 : 0 ≤ u := hP.hs.trans hu.1
  have huT := lt_lifespan hu.2 hP.ht
  have hK := abs_kinCorr_le h hr hu0 huT
  have hW : slowWiener r g y u ≤ cp caps.WS := (hP.onPrefix.1 u hu).2.2.2.2.trans (le_cp _)
  have hW0 : 0 ≤ slowWiener r g y u := wiener_nonneg _
  have h16 : 16 * slowWiener r g y u ≤ |r| := by
    have := (thr_parts hφ M caps).1
    linarith [hP.thr]
  have hA := sq_nonneg (fastNorm 0 r g y u)
  have hbound : 2 / |r| * (slowWiener r g y u * fastNorm 0 r g y u ^ 2) ≤
      1 / 8 * fastNorm 0 r g y u ^ 2 := by
    have hrpos : 0 < |r| := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hrpos]
    nlinarith [mul_le_mul_of_nonneg_left h16 hA]
  have := abs_le.1 (hK.trans hbound)
  unfold W0
  constructor <;> linarith

theorem W0_zero_le_J (h : ActualSol μ φ r g y Ty) {M : ℝ} {caps : Caps} {t : ℝ}
    (hP : PrefixHyp (kinJThreshold φ M) r g y Ty caps 0 t) :
    W0 r g y 0 ≤ 5 / 4 * (μ + 1 / 4) ^ 2 := by
  have hc := (W0_coercive_J h hP (u := 0) ⟨le_rfl, hP.hst⟩).2
  have hy0 := h.sol.adm 0 le_rfl h.pos
  have hμ : 0 ≤ μ := (hnorm_nonneg _ _).trans h.init_le
  have e : actual r g y 0 = y 0 := by simp [actual, psi_zero]
  have h1 : fastNorm 0 r g y 0 ≤ μ := by
    unfold fastNorm
    rw [e]
    calc hnorm 0 (PiF (y 0)) ≤ hnorm 0 (y 0) := hnorm_PiF_le (hy0.inH.mono (by norm_num))
      _ ≤ hnorm 2 (y 0) := hnorm_mono (by norm_num) hy0.inH
      _ ≤ μ := h.init_le
  have h0 := hnorm_nonneg 0 (PiF (actual r g y 0))
  have h2 : fastNorm 0 r g y 0 ^ 2 ≤ (μ + 1 / 4) ^ 2 := by
    unfold fastNorm at h1 ⊢
    nlinarith
  linarith

/-! ### The source norms -/

/-- **N15**: `‖N(F,F)‖₀ ≤ (2 c₄/q) ‖F‖₁²`, with one derivative less than `hnorm_kinN_le`. -/
lemma hnorm_kinN_sob (hr : r ≠ 0) (τ : ℝ) {F : Field} (hF : InH 1 F) (hF0 : F 0 = 0) :
    hnorm 0 (kinN r τ F F) ≤ 2 / |r| * (c4 * hnorm 1 F ^ 2) := by
  have hs : Summable fun k => absSq k * ‖F k‖ ^ 2 :=
    hF.congr fun k => by rw [sobWeight_one]
  obtain ⟨h1, h2⟩ := GN.sob_conv (a := fun k => ‖F k‖) (fun _ => norm_nonneg _) (by simp [hF0]) hs
  have hF2 : Summable fun k => ‖F k‖ ^ 2 := summable_norm_sq_of_inH (hF.mono (by norm_num))
  have hS0 : 0 ≤ ∑' k, sobWeight 1 k * ‖F k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg 1 k) (sq_nonneg _)
  have hS : ∑' k, absSq k * ‖F k‖ ^ 2 = hnorm 1 F ^ 2 := by
    rw [hnorm, Real.sq_sqrt hS0]
    exact tsum_congr fun k => by rw [sobWeight_one]
  have hq : 0 ≤ 2 / |r| := by positivity
  have hpt : ∀ k, ‖kinN r τ F F k‖ ^ 2 ≤
      (2 / |r|) ^ 2 * convR (fun k => ‖F k‖) (fun k => ‖F k‖) k ^ 2 := fun k => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_kinN_le hr hF2 hF2 k) 2
  have hsum := h1.mul_left ((2 / |r|) ^ 2)
  have hs2 : Summable fun k => ‖kinN r τ F F k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hpt hsum
  rw [hnorm_zero_eq (kinN_zero_mode F F)]
  have hc := c4_pos.le
  calc Real.sqrt (∑' k, ‖kinN r τ F F k‖ ^ 2)
      ≤ Real.sqrt ((2 / |r| * (c4 * hnorm 1 F ^ 2)) ^ 2) := by
        refine Real.sqrt_le_sqrt ((hs2.tsum_le_tsum hpt hsum).trans ?_)
        rw [tsum_mul_left, mul_pow, mul_pow]
        rw [hS] at h2
        rw [← mul_pow c4] at h2 ⊢
        exact mul_le_mul_of_nonneg_left (by simpa only [mul_pow] using h2) (by positivity)
    _ = 2 / |r| * (c4 * hnorm 1 F ^ 2) := Real.sqrt_sq (by positivity)

/-- `ℓ²` Cauchy–Schwarz for the `σ = 0` pairing. -/
private lemma abs_pair_zero_le_l2' {c F : Field} (hc : Summable fun k => ‖c k‖ ^ 2)
    (hF : Summable fun k => ‖F k‖ ^ 2) :
    |pair 0 c F| ≤ Real.sqrt (∑' k, ‖c k‖ ^ 2) * Real.sqrt (∑' k, ‖F k‖ ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hc' : Summable fun k => ‖c k‖ ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hc
  have hF' : Summable fun k => ‖F k‖ ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hF
  have key : Summable (fun k => ‖c k‖ * ‖F k‖) ∧ ∑' k, ‖c k‖ * ‖F k‖ ≤
      Real.sqrt (∑' k, ‖c k‖ ^ 2) * Real.sqrt (∑' k, ‖F k‖ ^ 2) := by
    have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq
      (fun k => norm_nonneg (c k)) (fun k => norm_nonneg (F k)) hc' hF'
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using h
  rw [pair, ← Real.norm_eq_abs]
  refine (tsum_of_norm_bounded key.1.hasSum fun k => ?_).trans key.2
  have h1 : sobWeight 0 k ≤ 1 := by
    unfold sobWeight
    split_ifs <;> simp
  refine (norm_pair_term_le' 0 c F k).trans ?_
  rw [mul_assoc]
  exact mul_le_of_le_one_left (by positivity) h1

/-- The filter force splits as `H_ψ = Q(ψ, y) + Q(x, ψ)`. -/
private lemma Hpsi_eq' (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    Hpsi r g y u = Qphase (r * u) (psi r 0 g u) (y u) +
      Qphase (r * u) (actual r g y u) (psi r 0 g u) := by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  have e1 := (majorized_Qphase (r * u)).sub_left 0 (y u) (actual r g y u) (y u) hy.mz hx.mz hy.mz
  have e2 := (majorized_Qphase (r * u)).sub_right 0 (actual r g y u) (y u) (actual r g y u)
    hx.mz hy.mz hx.mz
  have hyx : y u - actual r g y u = psi r 0 g u := by simp [actual]
  simp only [hyx] at e1 e2
  rw [Hpsi, e1, e2]
  abel

/-- `Q(x,x) = Q(S,S) + 2Q(S,F) + Q(F,F)`. -/
private lemma Qphase_split (τ : ℝ) {x : Field} (hx : Adm 2 x) :
    Qphase τ x x = Qphase τ (PiS x) (PiS x) + Qphase τ (PiS x) (PiF x) +
      Qphase τ (PiS x) (PiF x) + Qphase τ (PiF x) (PiF x) := by
  have hS : Adm 2 (PiS x) := hx.PiS
  have hF : Adm 2 (PiF x) := hx.PiF
  have hM := majorized_Qphase τ
  have hx' : x = PiS x + PiF x := (PiS_add_PiF x).symm
  have hsum : MZ 2 (PiS x + PiF x) := by rw [← hx']; exact hx.mz
  have hcomm : Qphase τ (PiF x) (PiS x) = Qphase τ (PiS x) (PiF x) :=
    Qm_comm_of_symm (phaseM_symm τ) hF.mz hS.mz
  conv_lhs => rw [hx']
  rw [hM.add_left 0 _ _ _ hS.mz hF.mz hsum, hM.add_right 0 _ _ _ hS.mz hS.mz hF.mz,
    hM.add_right 0 _ _ _ hF.mz hS.mz hF.mz, hcomm]
  abel

lemma PiS_PiS' (x : Field) : PiS (PiS x) = PiS x := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [PiS, hk]

lemma PiF_PiF' (x : Field) : PiF (PiF x) = PiF x := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [PiF, hk]

/-- **The slow output of the actual nonlinearity**: no mixed term (`Qphase_slow_fast`). -/
lemma hnorm_PiS_Qyy {τ : ℝ} {x H W : Field} (hx : Adm 2 x) (hW : W = Qphase τ x x + H)
    (hH : InH 0 H) :
    hnorm 0 (PiS W) ≤ hnorm 0 (Qphase τ (PiS x) (PiS x)) +
      hnorm 0 (Qphase τ (PiF x) (PiF x)) + hnorm 0 H := by
  have hS : Adm 2 (PiS x) := hx.PiS
  have hF : Adm 2 (PiF x) := hx.PiF
  have hQ1 : InH 0 (Qphase τ (PiS x) (PiS x)) := (hnorm_Qm_zero_le (phaseM_bdd τ) hS.mz hS.mz).1
  have hQ2 : InH 0 (Qphase τ (PiF x) (PiF x)) := (hnorm_Qm_zero_le (phaseM_bdd τ) hF.mz hF.mz).1
  have e : PiS W = Qphase τ (PiS x) (PiS x) + PiS (Qphase τ (PiF x) (PiF x)) + PiS H := by
    funext k
    rw [hW, Qphase_split τ hx]
    by_cases hk : k 2 = 0
    · simp only [Pi.add_apply, PiS_apply_slow _ hk]
      rw [Qphase_slow_fast τ (PiS_PiS' x) (PiF_PiF' x) hk]
      abel
    · simp only [Pi.add_apply, PiS_apply_fast _ hk, Qphase_slow_slow τ (PiS_PiS' x) hk]
      simp
  rw [e]
  refine (hnorm_add_le (hQ1.add hQ2.PiS) hH.PiS).trans (add_le_add ?_ (hnorm_PiS_le hH))
  exact (hnorm_add_le hQ1 hQ2.PiS).trans (add_le_add le_rfl (hnorm_PiS_le hQ2))

/-- **The fast output of the actual nonlinearity**: no slow-slow term (`Qphase_slow_slow`). -/
lemma hnorm_PiF_Qyy {τ : ℝ} {x H W : Field} (hx : Adm 2 x) (hW : W = Qphase τ x x + H)
    (hH : InH 0 H) :
    hnorm 0 (PiF W) ≤ 2 * hnorm 0 (Qphase τ (PiS x) (PiF x)) +
      hnorm 0 (Qphase τ (PiF x) (PiF x)) + hnorm 0 H := by
  have hS : Adm 2 (PiS x) := hx.PiS
  have hF : Adm 2 (PiF x) := hx.PiF
  have hQ1 : InH 0 (Qphase τ (PiS x) (PiF x)) := (hnorm_Qm_zero_le (phaseM_bdd τ) hS.mz hF.mz).1
  have hQ2 : InH 0 (Qphase τ (PiF x) (PiF x)) := (hnorm_Qm_zero_le (phaseM_bdd τ) hF.mz hF.mz).1
  have e : PiF W = Qphase τ (PiS x) (PiF x) + Qphase τ (PiS x) (PiF x) +
      PiF (Qphase τ (PiF x) (PiF x)) + PiF H := by
    funext k
    rw [hW, Qphase_split τ hx]
    by_cases hk : k 2 = 0
    · simp only [Pi.add_apply, PiF_apply_slow _ hk,
        Qphase_slow_fast τ (PiS_PiS' x) (PiF_PiF' x) hk]
      simp
    · simp only [Pi.add_apply, PiF_apply_fast _ hk]
      rw [Qphase_slow_slow τ (PiS_PiS' x) hk]
      abel
  rw [e]
  refine (hnorm_add_le ((hQ1.add hQ1).add hQ2.PiF) hH.PiF).trans
    (add_le_add ?_ (hnorm_PiF_le hH))
  refine (hnorm_add_le (hQ1.add hQ1) hQ2.PiF).trans (add_le_add ?_ (hnorm_PiF_le hQ2))
  refine (hnorm_add_le hQ1 hQ1).trans (le_of_eq ?_)
  ring

/-- `‖F'‖_{ℓ²} ≤ ‖F‖₂ + ‖Π_F Q(y,y)‖₀`: `fastRHS_l2` before discarding `Π_F`. -/
lemma fastRHS_l2J (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    Real.sqrt (∑' k, ‖fastRHS r g y u k‖ ^ 2) ≤
      hnorm 2 (PiF (actual r g y u)) + hnorm 0 (PiF (Qphase (r * u) (y u) (y u))) := by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  have hF := hx.PiF
  have hQ : InH 0 (Qphase (r * u) (y u) (y u)) := (hnorm_Qm_zero_le (phaseM_bdd _) hy.mz hy.mz).1
  obtain ⟨hA2, hAn⟩ := tsum_norm_sq_absSq_smul hF.inH
  have h0 : fastRHS r g y u 0 = 0 := by simp [fastRHS, PiF]
  have hA0 : (fun k => (-(absSq k : ℝ) : ℂ) • PiF (actual r g y u) k) 0 = 0 := by
    simp [hF.mean]
  rw [← hnorm_zero_eq h0]
  have e : fastRHS r g y u = (fun k => (-(absSq k : ℝ) : ℂ) • PiF (actual r g y u) k) +
      (-PiF (Qphase (r * u) (y u) (y u))) := by
    funext k; simp [fastRHS, sub_eq_add_neg]
  rw [e]
  refine (hnorm_add_le (inH_zero_of_summable hA2) hQ.PiF.neg).trans ?_
  rw [hnorm_zero_eq hA0, hAn, hnorm_neg]

/-- `‖S'‖_{ℓ²} ≤ ‖S‖₂ + ‖Π_S Q(y,y)‖₀ + ‖g‖₂`: `slowRHS_l2` before discarding `Π_S`. -/
lemma slowRHS_l2J (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    Real.sqrt (∑' k, ‖slowRHS r g y u k‖ ^ 2) ≤
      hnorm 2 (PiS (actual r g y u)) + hnorm 0 (PiS (Qphase (r * u) (y u) (y u))) + hnorm 2 g := by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  have hS := hx.PiS
  have hQ : InH 0 (Qphase (r * u) (y u) (y u)) := (hnorm_Qm_zero_le (phaseM_bdd _) hy.mz hy.mz).1
  obtain ⟨hA2, hAn⟩ := tsum_norm_sq_absSq_smul hS.inH
  have hg0 : InH 0 g := h.force_adm.inH.mono (by norm_num)
  have hQ0 : Qphase (r * u) (y u) (y u) 0 = 0 := by simp [Qphase, Qm, hel_zero_mode]
  have ha0 : absSq (0 : Mode) = 0 := by simp [absSq]
  have h0 : slowRHS r g y u 0 = 0 := by
    simp [slowRHS, PiS, h.force_adm.mean, hx.mean, hQ0, ha0]
  have hA0 : (fun k => (-(absSq k : ℝ) : ℂ) • PiS (actual r g y u) k) 0 = 0 := by
    simp [hS.mean]
  rw [← hnorm_zero_eq h0]
  have e : slowRHS r g y u = (fun k => (-(absSq k : ℝ) : ℂ) • PiS (actual r g y u) k) +
      (-PiS (Qphase (r * u) (y u) (y u)) + PiS g) := by
    funext k; simp [slowRHS, sub_eq_add_neg, add_assoc]
  rw [e]
  refine (hnorm_add_le (inH_zero_of_summable hA2) (hQ.PiS.neg.add hg0.PiS)).trans ?_
  rw [hnorm_zero_eq hA0, hAn, add_assoc]
  refine add_le_add le_rfl ((hnorm_add_le hQ.PiS.neg hg0.PiS).trans ?_)
  rw [hnorm_neg]
  exact add_le_add le_rfl ((hnorm_PiS_le hg0).trans (hnorm_mono (by norm_num) h.force_adm.inH))

/-! ### The budget -/

/-- `Q ≤ 4(1 + c)(m + √(mB)) a` from `Q² ≤ (9/2 m² + 27/2 c m b) a²`. -/
private lemma mixed_alg {c m B b a Q : ℝ} (hc : 0 ≤ c) (hm : 0 ≤ m) (hb : b ≤ B) (ha : 0 ≤ a)
    (hb0 : 0 ≤ b) (h : Q ^ 2 ≤ (9 / 2 * m ^ 2 + 27 / 2 * c * m * b) * a ^ 2) :
    Q ≤ 4 * (1 + c) * kinD m B * a := by
  have hB : 0 ≤ B := hb0.trans hb
  set s := Real.sqrt (m * B) with hs
  have hs2 : s ^ 2 = m * B := Real.sq_sqrt (mul_nonneg hm hB)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hD : 0 ≤ kinD m B := kinD_nonneg hm
  have h1 : 9 / 2 * m ^ 2 + 27 / 2 * c * m * b ≤ (4 * (1 + c) * kinD m B) ^ 2 := by
    have e : kinD m B = m + s := rfl
    rw [e]
    have h2 : m * b ≤ s ^ 2 := by
      rw [hs2]
      exact mul_le_mul_of_nonneg_left hb hm
    have h3 : c * (m * b) ≤ c * s ^ 2 := mul_le_mul_of_nonneg_left h2 hc
    have h4 : 0 ≤ m * s := mul_nonneg hm hs0
    have h5 : (1 : ℝ) + 2 * c ≤ (1 + c) ^ 2 := by nlinarith [sq_nonneg c]
    have h6 : (m + s) ^ 2 ≥ m ^ 2 + s ^ 2 := by nlinarith
    have h7 : (4 * (1 + c) * (m + s)) ^ 2 = 16 * (1 + c) ^ 2 * (m + s) ^ 2 := by ring
    rw [h7]
    have h8 : 16 * (1 + 2 * c) * (m ^ 2 + s ^ 2) ≤ 16 * (1 + c) ^ 2 * (m + s) ^ 2 :=
      mul_le_mul (by linarith) h6 (by positivity) (by positivity)
    nlinarith [mul_nonneg hc (sq_nonneg s), mul_nonneg hc (sq_nonneg m), sq_nonneg m, sq_nonneg s]
  have h2 : Q ^ 2 ≤ (4 * (1 + c) * kinD m B * a) ^ 2 := by
    refine h.trans ?_
    rw [mul_pow (4 * (1 + c) * kinD m B)]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg a)
  exact (abs_le_of_sq_le_sq' h2 (by positivity)).2

/-- **Body 56, the fast source**: `‖Q_F‖₀ ≲ (M_∞ + D₄ + b_F) a_F`, `D₄² = M_∞ b_S`. -/
theorem hnorm_QF_le (τ : ℝ) {x : Field} (hx : Adm 2 x) {M : ℝ} (hM : GN.SupBd (PiS x) M) :
    hnorm 0 (PiF (Qphase τ x x)) ≤
      (8 * (1 + c4) * kinD M (hnorm 2 (PiS x)) + 2 * c4 * hnorm 2 (PiF x)) * hnorm 1 (PiF x) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hF := hx.PiF
  have hS := hx.PiS
  have h1 := mixed_alg c4_pos.le hM0 le_rfl (hnorm_nonneg 1 _) (hnorm_nonneg 2 _)
    (GN.hnorm_Qphase_mixed τ hS (PiS_PiS' x) hF hM)
  have h2 := (hnorm_Qm_zero_le (phaseM_bdd τ) hF.mz hF.mz).2
  have hw := mul_le_mul_of_nonneg_left (wiener_le hF.mz) (hnorm_nonneg 1 (PiF x))
  have h3 := hnorm_PiF_Qyy (τ := τ) (W := Qphase τ x x) (H := 0) hx (by simp)
    (by simp [InH, summable_zero])
  have h4 : hnorm 0 (0 : Field) = 0 := by simp [hnorm]
  rw [h4] at h3
  have h2' : hnorm 0 (Qphase τ (PiF x) (PiF x)) ≤
      2 * c4 * hnorm 2 (PiF x) * hnorm 1 (PiF x) := by
    calc _ ≤ _ := h2
      _ ≤ _ := by nlinarith only [hw]
  calc hnorm 0 (PiF (Qphase τ x x))
      ≤ 2 * (4 * (1 + c4) * kinD M (hnorm 2 (PiS x)) * hnorm 1 (PiF x)) +
        2 * c4 * hnorm 2 (PiF x) * hnorm 1 (PiF x) := by linarith only [h1, h2', h3]
    _ = _ := by ring

/-- **Body 56, the slow source**: `‖Q_S‖₀ ≲ M_∞ a_S + b_F a_F`. -/
theorem hnorm_QS_le (τ : ℝ) {x : Field} (hx : Adm 2 x) {M : ℝ} (hM : GN.SupBd (PiS x) M) :
    hnorm 0 (PiS (Qphase τ x x)) ≤
      3 * M * hnorm 1 (PiS x) + 2 * c4 * hnorm 2 (PiF x) * hnorm 1 (PiF x) := by
  have hF := hx.PiF
  have hS := hx.PiS
  have h1 := GN.hnorm_Qphase_slow τ hS (PiS_PiS' x) hM
  have h2 := (hnorm_Qm_zero_le (phaseM_bdd τ) hF.mz hF.mz).2
  have hw := mul_le_mul_of_nonneg_left (wiener_le hF.mz) (hnorm_nonneg 1 (PiF x))
  have h3 := hnorm_PiS_Qyy (τ := τ) (W := Qphase τ x x) (H := 0) hx (by simp)
    (by simp [InH, summable_zero])
  have h4 : hnorm 0 (0 : Field) = 0 := by simp [hnorm]
  rw [h4] at h3
  have h2' : hnorm 0 (Qphase τ (PiF x) (PiF x)) ≤
      2 * c4 * hnorm 2 (PiF x) * hnorm 1 (PiF x) := by
    calc _ ≤ _ := h2
      _ ≤ _ := by nlinarith only [hw]
  linarith only [h1, h2', h3]

/-- The filter: `h₀ ≤ 1/16` once `64 φ G ≤ q`. -/
private lemma filter_alg {c q φ ε ψ1 wψ a aS bF wS wF ax wx ay wy h0 Y A P W : ℝ}
    (hc : 0 ≤ c) (hq : 0 < q) (hε : 0 ≤ ε) (hqε : q * ε ≤ 2 * φ) (h4 : 4 * φ ≤ q)
    (hG : 64 * φ * (W + c * Y + c * (A + P + 1)) ≤ q)
    (hψ1 : ψ1 ≤ ε) (hwψ : wψ ≤ c * ε) (ha : a ≤ P) (haS : aS ≤ A) (hbF : bF ≤ Y)
    (hwS : wS ≤ W) (hwF : wF ≤ c * bF) (hax0 : 0 ≤ ax) (hax : ax ≤ aS + a) (hwx0 : 0 ≤ wx)
    (hwx : wx ≤ wS + wF) (hay0 : 0 ≤ ay) (hay : ay ≤ ax + ψ1) (hwy0 : 0 ≤ wy)
    (hwy : wy ≤ wx + wψ) (hh0 : h0 ≤ ψ1 * wy + wψ * ay + ax * wψ + wx * ψ1) :
    h0 ≤ 1 / 16 := by
  have hε1 : ε ≤ 1 := by nlinarith
  have hG0 : 0 ≤ W + c * Y + c * (A + P + 1) := by
    have h1 : 0 ≤ wx := hwx0
    have h2 : wx ≤ W + c * Y := by nlinarith [mul_le_mul_of_nonneg_left hbF hc]
    have h3 : 0 ≤ A + P := hax0.trans (by linarith)
    nlinarith [mul_nonneg hc h3]
  have h1 : h0 ≤ ε * (2 * (W + c * Y + c * (A + P + 1))) := by
    have e1 : ψ1 * wy ≤ ε * wy := mul_le_mul_of_nonneg_right hψ1 hwy0
    have e2 : wψ * ay ≤ c * ε * ay := mul_le_mul_of_nonneg_right hwψ hay0
    have e3 : ax * wψ ≤ ax * (c * ε) := mul_le_mul_of_nonneg_left hwψ hax0
    have e4 : wx * ψ1 ≤ wx * ε := mul_le_mul_of_nonneg_left hψ1 hwx0
    have hwx' : wx ≤ W + c * Y := by nlinarith [mul_le_mul_of_nonneg_left hbF hc]
    have hax' : ax ≤ A + P := by linarith
    have e5 : wy ≤ W + c * Y + c * ε := by linarith
    have e6 : ay ≤ A + P + ε := by linarith
    have h5 : ε * wy + c * ε * ay + ax * (c * ε) + wx * ε ≤
        ε * (2 * (W + c * Y + c * (A + P + 1))) := by
      have e7 : c * ay ≤ c * (A + P + ε) := mul_le_mul_of_nonneg_left e6 hc
      have e8 : c * ax ≤ c * (A + P) := mul_le_mul_of_nonneg_left hax' hc
      have e9 : c * ε ≤ c * 1 := mul_le_mul_of_nonneg_left hε1 hc
      have e10 : wy + c * ay + c * ax + wx ≤ 2 * (W + c * Y + c * (A + P + 1)) := by
        nlinarith
      have := mul_le_mul_of_nonneg_left e10 hε
      nlinarith
    linarith
  have h2 : q * h0 ≤ q * (1 / 16) := by
    have h3 := mul_le_mul_of_nonneg_left h1 hq.le
    have h4' : q * (ε * (2 * (W + c * Y + c * (A + P + 1)))) ≤
        2 * φ * (2 * (W + c * Y + c * (A + P + 1))) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hqε (by positivity)
    nlinarith
  exact le_of_mul_le_mul_left h2 hq

/-- The slow-output term of the budget. -/
private lemma budget_X2 {c q a Y s1 s' n0 X2 : ℝ} (hc : 0 ≤ c) (hq : 0 < q) (ha : 0 ≤ a)
    (hY : 0 ≤ Y) (hs1 : 0 ≤ s1) (hs' : s' ≤ s1 + 2 * a * c * Y) (hn0 : 0 ≤ n0)
    (hn1 : n0 ≤ 2 / q * (c * a ^ 2)) (hn2 : n0 ≤ 2 / q * (c * Y * a)) (hX2 : |X2| ≤ s' * n0) :
    q * |X2| ≤ (2 * c * s1 + 4 * c ^ 2 * Y ^ 2) * a ^ 2 := by
  have hqi : q * (2 / q) = 2 := by field_simp
  have h1 : |X2| ≤ s1 * n0 + 2 * a * c * Y * n0 := by
    refine hX2.trans ?_
    have := mul_le_mul_of_nonneg_right hs' hn0
    linarith only [this]
  have h2 : q * (s1 * n0) ≤ 2 * c * s1 * a ^ 2 := by
    have h3 := mul_le_mul_of_nonneg_left hn1 (mul_nonneg hq.le hs1)
    calc q * (s1 * n0) = q * s1 * n0 := by ring
      _ ≤ q * s1 * (2 / q * (c * a ^ 2)) := h3
      _ = q * (2 / q) * (s1 * (c * a ^ 2)) := by ring
      _ = 2 * c * s1 * a ^ 2 := by rw [hqi]; ring
  have h4 : q * (2 * a * c * Y * n0) ≤ 4 * c ^ 2 * Y ^ 2 * a ^ 2 := by
    have h3 := mul_le_mul_of_nonneg_left hn2 (by positivity : 0 ≤ q * (2 * a * c * Y))
    calc q * (2 * a * c * Y * n0) = q * (2 * a * c * Y) * n0 := by ring
      _ ≤ q * (2 * a * c * Y) * (2 / q * (c * Y * a)) := h3
      _ = q * (2 / q) * (2 * a * c * Y * (c * Y * a)) := by ring
      _ = 4 * c ^ 2 * Y ^ 2 * a ^ 2 := by rw [hqi]; ring
  have h5 := mul_le_mul_of_nonneg_left h1 hq.le
  rw [mul_add] at h5
  calc q * |X2| ≤ 2 * c * s1 * a ^ 2 + 4 * c ^ 2 * Y ^ 2 * a ^ 2 := by linarith only [h5, h2, h4]
    _ = _ := by ring

/-- The fast-input term of the budget. -/
private lemma budget_X3 {c q a f0 Y W E fd w X3 : ℝ} (hq : 0 < q) (hf0 : 0 ≤ f0)
    (hfa : f0 ≤ a) (hW : 0 ≤ W) (hfd0 : 0 ≤ fd) (hfd : fd ≤ Y + (E + 2 * c * Y) * a + 1 / 16)
    (hw : w ≤ W) (hX3 : |X3| ≤ 2 / q * (w * (fd * f0))) :
    q * |X3| ≤ 2 * W * (Y + 1 / 16) * a + 2 * W * (E + 2 * c * Y) * a ^ 2 := by
  have hqi : q * (2 / q) = 2 := by field_simp
  have h1 : q * |X3| ≤ 2 * (w * (fd * f0)) := by
    have := mul_le_mul_of_nonneg_left hX3 hq.le
    calc q * |X3| ≤ q * (2 / q * (w * (fd * f0))) := this
      _ = q * (2 / q) * (w * (fd * f0)) := by ring
      _ = _ := by rw [hqi]
  have h0 : 0 ≤ Y + (E + 2 * c * Y) * a + 1 / 16 := hfd0.trans hfd
  have h2 : w * (fd * f0) ≤ W * ((Y + (E + 2 * c * Y) * a + 1 / 16) * a) :=
    mul_le_mul hw (mul_le_mul hfd hfa hf0 h0) (mul_nonneg hfd0 hf0) hW
  calc q * |X3| ≤ 2 * (W * ((Y + (E + 2 * c * Y) * a + 1 / 16) * a)) := by
        linarith only [h1, h2]
    _ = _ := by ring

/-- The real-number bookkeeping of the joint budget. -/
private lemma budget_core {c q a f0 Y W s1 E h0 s' n0 fd w X1 X2 X3 : ℝ}
    (hc : 0 ≤ c) (hq : 0 < q) (ha : 0 ≤ a) (hf0 : 0 ≤ f0) (hfa : f0 ≤ a) (hY : 0 ≤ Y)
    (hW : 0 ≤ W) (hs1 : 0 ≤ s1)
    (hX1 : |X1| ≤ a * h0) (hh0 : h0 ≤ 1 / 16)
    (hs' : s' ≤ s1 + 2 * a * c * Y) (hn0 : 0 ≤ n0)
    (hn1 : n0 ≤ 2 / q * (c * a ^ 2)) (hn2 : n0 ≤ 2 / q * (c * Y * a)) (hX2 : |X2| ≤ s' * n0)
    (hfd0 : 0 ≤ fd) (hfd : fd ≤ Y + (E + 2 * c * Y) * a + 1 / 16) (hw : w ≤ W)
    (hX3 : |X3| ≤ 2 / q * (w * (fd * f0)))
    (hthr1 : 32 * W * (Y + 1) ≤ q)
    (hthr2 : 8 * c * s1 + 16 * c ^ 2 * Y ^ 2 + 16 * W * (E + 2 * c * Y) ≤ q) :
    -2 * a ^ 2 - 2 * X1 - 2 * X2 - 4 * X3 + a ^ 2 ≤ 1 / 8 := by
  have hA := budget_X2 hc hq ha hY hs1 hs' hn0 hn1 hn2 hX2
  have hB := budget_X3 hq hf0 hfa hW hfd0 hfd hw hX3
  have h1 : 8 * W * (Y + 1 / 16) ≤ q / 4 := by
    have : W * (1 / 16) ≤ W * 1 := mul_le_mul_of_nonneg_left (by norm_num) hW
    linarith only [hthr1, this, mul_add W Y 1, mul_add W Y (1 / 16), mul_assoc 32 W (Y + 1),
      mul_assoc 8 W (Y + 1 / 16)]
  have h2 : 4 * c * s1 + 8 * c ^ 2 * Y ^ 2 + 8 * W * (E + 2 * c * Y) ≤ q / 2 := by
    linarith only [hthr2]
  have h3 := mul_le_mul_of_nonneg_right h1 ha
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg a)
  have hC : q * (2 * |X2| + 4 * |X3|) ≤ q * (a / 4 + a ^ 2 / 2) := by
    calc q * (2 * |X2| + 4 * |X3|) = 2 * (q * |X2|) + 4 * (q * |X3|) := by ring
      _ ≤ 2 * ((2 * c * s1 + 4 * c ^ 2 * Y ^ 2) * a ^ 2) +
          4 * (2 * W * (Y + 1 / 16) * a + 2 * W * (E + 2 * c * Y) * a ^ 2) := by
          linarith only [hA, hB]
      _ = 8 * W * (Y + 1 / 16) * a +
          (4 * c * s1 + 8 * c ^ 2 * Y ^ 2 + 8 * W * (E + 2 * c * Y)) * a ^ 2 := by ring
      _ ≤ q / 4 * a + q / 2 * a ^ 2 := add_le_add h3 h4
      _ = _ := by ring
  have hD : 2 * |X2| + 4 * |X3| ≤ a / 4 + a ^ 2 / 2 := le_of_mul_le_mul_left hC hq
  have hF : 2 * |X1| ≤ a / 8 := by
    have := hX1.trans (mul_le_mul_of_nonneg_left hh0 ha)
    linarith only [this]
  have h5 := neg_abs_le X1
  have h6 := neg_abs_le X2
  have h7 := neg_abs_le X3
  nlinarith only [hD, hF, h5, h6, h7, sq_nonneg (a - 3 / 8)]

/-! ### E4-J: the pointwise budget and the kinetic law -/

/-- **The pointwise budget** `W₀' + a_F² ≤ 1/8`: on a prefix where the caps hold, `M_∞ ≤ M` and
`kinJThreshold φ M caps ≤ q`. -/
private lemma W0RHS_budgetJ (h : ActualSol μ φ r g y Ty) {M : ℝ} {caps : Caps} {s t : ℝ}
    (hP : PrefixHyp (kinJThreshold φ M) r g y Ty caps s t)
    (hsup : ∀ u ∈ Icc s t, slowSup r g y u ≤ M) {u : ℝ} (hu : u ∈ Icc s t) :
    W0RHS r g y u + fastNorm 1 r g y u ^ 2 ≤ 1 / 8 := by
  have hφ := phi_nonneg_of_sol h
  have hr1 := (one_le_kinJ hφ M caps).trans hP.thr
  have hr : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr1; linarith
  have hq : 0 < |r| := by linarith
  obtain ⟨-, t2, t3, t4, t5⟩ := thr_parts hφ M caps
  have hthr := hP.thr
  have hu0 : 0 ≤ u := hP.hs.trans hu.1
  have huT := lt_lifespan hu.2 hP.ht
  have hx := actual_adm h hu0 huT
  have hy := h.sol.adm u hu0 huT
  have hF := hx.PiF
  have hS := hx.PiS
  have hψ : Adm 2 (psi r 0 g u) := psi_adm h.force_adm u hu0
  have hψb := (psi_bound (t₀ := 0) hr h.force_adm u hu0).2
  obtain ⟨cF1, cF2, cS1, cS2, cW⟩ := hP.onPrefix.1 u hu
  have hc := c4_pos.le
  have hm := cp_nonneg M
  have hF2 : Summable fun k => ‖PiF (actual r g y u) k‖ ^ 2 :=
    summable_norm_sq_of_inH (hF.inH.mono (by norm_num))
  -- the filter
  have hQ1 := hnorm_Qm_zero_le (phaseM_bdd (r * u)) hψ.mz hy.mz
  have hQ2 := hnorm_Qm_zero_le (phaseM_bdd (r * u)) hx.mz hψ.mz
  have hH0 : InH 0 (Hpsi r g y u) := by
    rw [Hpsi_eq' h hu0 huT]; exact hQ1.1.add hQ2.1
  have hh0 : hnorm 0 (Hpsi r g y u) ≤ hnorm 1 (psi r 0 g u) * wiener (y u) +
      wiener (psi r 0 g u) * hnorm 1 (y u) + hnorm 1 (actual r g y u) * wiener (psi r 0 g u) +
      wiener (actual r g y u) * hnorm 1 (psi r 0 g u) := by
    rw [Hpsi_eq' h hu0 huT]
    refine (hnorm_add_le hQ1.1 hQ2.1).trans ?_
    linarith [hQ1.2, hQ2.2]
  have hyx : y u = actual r g y u + psi r 0 g u := by simp [actual]
  have hay : hnorm 1 (y u) ≤ hnorm 1 (actual r g y u) + hnorm 1 (psi r 0 g u) := by
    rw [hyx]; exact hnorm_add_le (hx.inH.mono (by norm_num)) (hψ.inH.mono (by norm_num))
  have hwy : wiener (y u) ≤ wiener (actual r g y u) + wiener (psi r 0 g u) := by
    rw [hyx]; exact wiener_add_le (summable_wiener hx.inH) (summable_wiener hψ.inH)
  have hxSF := PiS_add_PiF (actual r g y u)
  have hax : hnorm 1 (actual r g y u) ≤
      hnorm 1 (PiS (actual r g y u)) + hnorm 1 (PiF (actual r g y u)) := by
    conv_lhs => rw [← hxSF]
    exact hnorm_add_le (hS.inH.mono (by norm_num)) (hF.inH.mono (by norm_num))
  have hwx : wiener (actual r g y u) ≤
      wiener (PiS (actual r g y u)) + wiener (PiF (actual r g y u)) := by
    conv_lhs => rw [← hxSF]
    exact wiener_add_le (summable_wiener hS.inH) (summable_wiener hF.inH)
  have hqε : |r| * hnorm 2 (psi r 0 g u) ≤ 2 * φ := by
    have hg12 : hnorm 1 g ≤ hnorm 2 g := hnorm_mono (by norm_num) h.force_adm.inH
    have := (le_div_iff₀ hq).1 hψb
    nlinarith [h.force_le]
  have hh1 : hnorm 0 (Hpsi r g y u) ≤ 1 / 16 :=
    filter_alg hc hq (hnorm_nonneg _ _) hqε (t2.trans hthr) (t3.trans hthr)
      (hnorm_mono (by norm_num) hψ.inH) (wiener_le hψ.mz) (cF1.trans (le_cp _))
      (cS1.trans (le_cp _)) (cF2.trans (le_cp _)) (cW.trans (le_cp _)) (wiener_le hF.mz)
      (hnorm_nonneg _ _) hax (wiener_nonneg _) hwx (hnorm_nonneg _ _) hay (wiener_nonneg _) hwy hh0
  -- the three pairings
  have hX1 : |pair 0 (PiF (actual r g y u)) (Hpsi r g y u)| ≤
      hnorm 1 (PiF (actual r g y u)) * hnorm 0 (Hpsi r g y u) := by
    have := (pair_le (σ := 0) (hF.inH.mono (by norm_num)) (hH0.mono (by norm_num))).2
    rw [zero_add] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (hnorm_nonneg _ _))
    exact hnorm_mono (by norm_num) hH0
  obtain ⟨hNs, hNle⟩ := hnorm_kinN_le (τ := r * u) hr (summable_wiener hF.inH) hF2
  have hN2 := hnorm_kinN_sob hr (r * u) (hF.inH.mono (by norm_num)) hF.mean
  have hSd := (slowRHS_l2 h hu0 huT).1
  have hFd := (fastRHS_l2 h hu0 huT).1
  have hX2 := abs_pair_zero_le_l2' hSd (summable_norm_sq_of_inH hNs)
  rw [← hnorm_zero_eq (kinN_zero_mode _ _)] at hX2
  have hX3 := abs_pair_kinN_le (τ := r * u) hr (summable_wiener hS.inH) hFd hF2
  have hf0 : Real.sqrt (∑' k, ‖PiF (actual r g y u) k‖ ^ 2) ≤ hnorm 1 (PiF (actual r g y u)) := by
    rw [← hnorm_zero_eq hF.mean]; exact hnorm_mono (by norm_num) (hF.inH.mono (by norm_num))
  -- the physical products
  have hSup : GN.SupBd (PiS (actual r g y u)) (cp M) :=
    GN.supBd_slowSup hS.inH ((hsup u hu).trans (le_cp _))
  have hQSS := GN.hnorm_Qphase_slow (r * u) hS (PiS_PiS' _) hSup
  have hQSF := mixed_alg hc hm (cS2.trans (le_cp _)) (hnorm_nonneg 1 _) (hnorm_nonneg 2 _)
    (GN.hnorm_Qphase_mixed (r * u) hS (PiS_PiS' _) hF hSup)
  have hQFF := (hnorm_Qm_zero_le (phaseM_bdd (r * u)) hF.mz hF.mz).2
  have hW1 : wiener (PiF (actual r g y u)) ≤ c4 * cp caps.yF :=
    (wiener_le hF.mz).trans (mul_le_mul_of_nonneg_left (cF2.trans (le_cp _)) hc)
  have ha0 : 0 ≤ hnorm 1 (PiF (actual r g y u)) := hnorm_nonneg _ _
  have hQFF' : hnorm 0 (Qphase (r * u) (PiF (actual r g y u)) (PiF (actual r g y u))) ≤
      2 * hnorm 1 (PiF (actual r g y u)) * c4 * cp caps.yF := by
    have := mul_le_mul_of_nonneg_left hW1 ha0
    calc _ ≤ _ := hQFF
      _ ≤ _ := by nlinarith only [this]
  have e : Qphase (r * u) (y u) (y u) =
      Qphase (r * u) (actual r g y u) (actual r g y u) + Hpsi r g y u := by
    simp [Hpsi]
  have hPS := hnorm_PiS_Qyy hx e hH0
  have hPF := hnorm_PiF_Qyy hx e hH0
  have hs' := slowRHS_l2J h hu0 huT
  have hfd := fastRHS_l2J h hu0 huT
  have hbound1 : Real.sqrt (∑' k, ‖slowRHS r g y u k‖ ^ 2) ≤
      (cp caps.BS + 3 * cp M * cp caps.AS + 1 + φ) +
        2 * hnorm 1 (PiF (actual r g y u)) * c4 * cp caps.yF := by
    have h3 : 3 * cp M * hnorm 1 (PiS (actual r g y u)) ≤ 3 * cp M * cp caps.AS :=
      mul_le_mul_of_nonneg_left (cS1.trans (le_cp _)) (by positivity)
    have h4 : hnorm 2 (PiS (actual r g y u)) ≤ cp caps.BS := cS2.trans (le_cp _)
    have h5 := h.force_le
    linarith only [hs', hPS, hQSS, hQFF', hh1, h3, h4, h5]
  have hbound2 : Real.sqrt (∑' k, ‖fastRHS r g y u k‖ ^ 2) ≤
      cp caps.yF + (8 * (1 + c4) * kinD (cp M) (cp caps.BS) + 2 * c4 * cp caps.yF) *
        hnorm 1 (PiF (actual r g y u)) + 1 / 16 := by
    have h4 : hnorm 2 (PiF (actual r g y u)) ≤ cp caps.yF := cF2.trans (le_cp _)
    linarith only [hfd, hPF, hQSF, hQFF', hh1, h4,
      mul_add (8 * (1 + c4) * kinD (cp M) (cp caps.BS)) (2 * c4 * cp caps.yF)
        (hnorm 1 (PiF (actual r g y u))),
      add_mul (8 * (1 + c4) * kinD (cp M) (cp caps.BS)) (2 * c4 * cp caps.yF)
        (hnorm 1 (PiF (actual r g y u))),
      mul_assoc (2 : ℝ) c4 (cp caps.yF), mul_comm (hnorm 1 (PiF (actual r g y u))) c4,
      mul_assoc (2 : ℝ) (hnorm 1 (PiF (actual r g y u))) c4,
      mul_assoc (4 : ℝ) (1 + c4) (kinD (cp M) (cp caps.BS)),
      mul_assoc (8 : ℝ) (1 + c4) (kinD (cp M) (cp caps.BS))]
  have hs10 : 0 ≤ cp caps.BS + 3 * cp M * cp caps.AS + 1 + φ := by
    have := cp_nonneg caps.BS
    have := cp_nonneg caps.AS
    positivity
  have hn2 : hnorm 0 (kinN r (r * u) (PiF (actual r g y u)) (PiF (actual r g y u))) ≤
      2 / |r| * (c4 * cp caps.yF * hnorm 1 (PiF (actual r g y u))) := by
    refine hNle.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact mul_le_mul hW1 hf0 (Real.sqrt_nonneg _) (mul_nonneg hc (cp_nonneg _))
  simp only [W0RHS, fastNorm]
  exact budget_core hc hq ha0 (Real.sqrt_nonneg _) hf0 (cp_nonneg _) (cp_nonneg _) hs10 hX1 hh1
    hbound1 (hnorm_nonneg _ _) hN2 hn2 hX2 (Real.sqrt_nonneg _) hbound2 (cW.trans (le_cp _)) hX3
    (t4.trans hthr) (t5.trans hthr)

/-- **E4.5 at the joint scale**: the integrated `W₀' + a_F² ≤ 1/8`. -/
theorem W0_diff_ineq_J (h : ActualSol μ φ r g y Ty) {M : ℝ} {caps : Caps} {s t : ℝ}
    (hP : PrefixHyp (kinJThreshold φ M) r g y Ty caps s t)
    (hsup : ∀ u ∈ Icc s t, slowSup r g y u ≤ M) :
    ∀ s' t' : ℝ, s ≤ s' → s' ≤ t' → t' ≤ t →
      W0 r g y t' - W0 r g y s' + (∫ u in s'..t', fastNorm 1 r g y u ^ 2) ≤ (t' - s') / 8 := by
  intro s' t' hs' hst' ht'
  have hφ := phi_nonneg_of_sol h
  have hr1 := (one_le_kinJ hφ M caps).trans hP.thr
  have hr : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr1; linarith
  have hs0 : 0 ≤ s' := hP.hs.trans hs'
  have ht'T := lt_lifespan ht' hP.ht
  obtain ⟨hI1, hI2⟩ := intervalIntegrable_fast h hs0 hst' ht'T
  have hI3 := (kinCorr_identity h hr hs0 hst' ht'T).1
  have hI : IntervalIntegrable (W0RHS r g y) volume s' t' := by
    refine (((hI1.const_mul (-2)).add (hI2.const_mul 2)).sub (hI3.const_mul 2)).congr
      fun u hu => ?_
    rw [uIoc_of_le hst'] at hu
    have hu0 : 0 ≤ u := hs0.trans hu.1.le
    have huT := lt_lifespan hu.2 ht'T
    simp only [W0RHS, kinCorrRHS]
    rw [pair_fast_force_eq h hu0 huT]
    ring
  rw [W0_identity h hr hs0 hst' ht'T]
  have hmono : ∫ u in s'..t', W0RHS r g y u ≤ ∫ u in s'..t', (1 / 8 - fastNorm 1 r g y u ^ 2) := by
    refine intervalIntegral.integral_mono_on hst' hI (intervalIntegrable_const.sub hI1)
      fun u hu => ?_
    have := W0RHS_budgetJ h hP hsup ⟨hs'.trans hu.1, hu.2.trans ht'⟩
    linarith
  rw [intervalIntegral.integral_sub intervalIntegrable_const hI1, intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  linarith

/-- **E4-J** (`KineticJoint`, TeX eq. quant-kinetic, eq. quant-kinetic-floor, survey block J3):
for all `μ, φ, M`, with the explicit threshold `kinJThreshold φ M`; all constants are absolute and
no `(1 + φ)` prefactor occurs.  From the coercivity, the true-zero bound, the budget and
`gronwall_decay_max` (`λ = 4/5`, `β = 1/8`). -/
theorem kineticJoint (μ φ M : ℝ) : KineticJoint μ φ M (kinJThreshold φ M) := by
  intro r g y Ty h
  refine ⟨W0 r g y, fun caps s t hP hsup => ?_⟩
  have hφ := phi_nonneg_of_sol h
  have hr1 := (one_le_kinJ hφ M caps).trans hP.thr
  have hr : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr1; linarith
  have hcoer : ∀ u ∈ Icc s t, 3 / 4 * fastNorm 0 r g y u ^ 2 ≤ W0 r g y u ∧
      W0 r g y u ≤ 5 / 4 * fastNorm 0 r g y u ^ 2 := fun u hu => W0_coercive_J h hP hu
  have hdiff := W0_diff_ineq_J h hP hsup
  refine ⟨hcoer, fun hs0 => ?_, hdiff s t le_rfl hP.hst le_rfl, ?_⟩
  · subst hs0
    exact W0_zero_le_J h hP
  · have ht0 : 0 ≤ t := hP.hs.trans hP.hst
    have hW := (continuousOn_W0 h hr ht0 hP.ht).mono (Icc_subset_Icc_left hP.hs)
    have ha := (continuousOn_fastNorm_sq h (σ := 1) (Or.inr rfl) ht0 hP.ht).mono
      (Icc_subset_Icc_left hP.hs)
    have key : ∀ s' t', s ≤ s' → s' ≤ t' → t' ≤ t →
        W0 r g y t' + 4 / 5 * ∫ u in s'..t', W0 r g y u ≤ W0 r g y s' + 1 / 8 * (t' - s') := by
      intro s' t' hs' hst' ht'
      have hsub : Icc s' t' ⊆ Icc s t := Icc_subset_Icc hs' ht'
      have hWI : IntervalIntegrable (W0 r g y) volume s' t' :=
        (hW.mono hsub).intervalIntegrable_of_Icc hst'
      have haI : IntervalIntegrable (fun u => fastNorm 1 r g y u ^ 2) volume s' t' :=
        (ha.mono hsub).intervalIntegrable_of_Icc hst'
      have hmono : ∫ u in s'..t', 4 / 5 * W0 r g y u ≤ ∫ u in s'..t', fastNorm 1 r g y u ^ 2 := by
        refine intervalIntegral.integral_mono_on hst' (hWI.const_mul _) haI fun u hu => ?_
        have hu' := hsub hu
        have h1 := (hcoer u hu').2
        have hx := actual_adm h (hP.hs.trans hu'.1) (lt_lifespan hu'.2 hP.ht)
        have h2 : fastNorm 0 r g y u ≤ fastNorm 1 r g y u :=
          hnorm_mono (by norm_num) (hx.PiF.inH.mono (by norm_num))
        have h3 := hnorm_nonneg 0 (PiF (actual r g y u))
        have h4 : fastNorm 0 r g y u ^ 2 ≤ fastNorm 1 r g y u ^ 2 := by
          unfold fastNorm at h2 h3 ⊢
          nlinarith
        linarith
      rw [intervalIntegral.integral_const_mul] at hmono
      have := hdiff s' t' hs' hst' ht'
      linarith
    have := gronwall_decay_max hP.hst (by norm_num : (0 : ℝ) < 4 / 5)
      (by norm_num : (0 : ℝ) ≤ 1 / 8) hW key
    have e : (1 : ℝ) / 8 / (4 / 5) = 5 / 32 := by norm_num
    rw [e] at this
    exact this

/-! ### R1 at the joint scale: the threshold against `Q = U R³` -/

/-- The kinetic threshold of the joint package: `M = C_S Ex(c_S, R) R`, `φ = R − X`. -/
def kinJ0 (CS cS X R : ℝ) (caps : Caps) : ℝ :=
  kinJThreshold (R - X) (CS * Ex cS R * R) caps

/-- **The field `kinetic` of `JointInterfaces`**, with `q₀ = kinJ0 C_S c_S`. -/
theorem kineticJoint_data (CS cS X R : ℝ) :
    KineticJoint X (R - X) (CS * Ex cS R * R) (kinJ0 CS cS X R) :=
  kineticJoint X (R - X) _

/-- Every atom of the threshold below one `a ≥ 1`, except `B_S ≤ a²`. -/
private lemma kinJ_alg {c a φ m W Y A B P d : ℝ} (hc : 0 ≤ c) (ha : 1 ≤ a) (hm0 : 0 ≤ m)
    (hW0 : 0 ≤ W) (hY0 : 0 ≤ Y) (hA0 : 0 ≤ A) (hP0 : 0 ≤ P) (hd0 : 0 ≤ d)
    (hφ : φ ≤ a) (hm : m ≤ a) (hW : W ≤ a) (hY : Y ≤ a) (hA : A ≤ a) (hP : P ≤ a) (hd : d ≤ a)
    (hB : B ≤ a ^ 2) :
    1 + 16 * W + 4 * φ + 64 * φ * (W + c * Y + c * (A + P + 1)) + 32 * W * (Y + 1) +
      (8 * c * (B + 3 * m * A + 1 + φ) + 16 * c ^ 2 * Y ^ 2 +
        16 * W * (8 * (1 + c) * (m + d) + 2 * c * Y)) ≤ (405 + 592 * c + 16 * c ^ 2) * a ^ 2 := by
  have ha0 : 0 ≤ a := by linarith
  have h1 : 1 ≤ a ^ 2 := one_le_pow₀ ha
  have haa : a ≤ a ^ 2 := by nlinarith
  have hG : W + c * Y + c * (A + P + 1) ≤ (1 + 4 * c) * a := by
    have h2 : c * Y ≤ c * a := mul_le_mul_of_nonneg_left hY hc
    have h3 : c * (A + P + 1) ≤ c * (3 * a) := mul_le_mul_of_nonneg_left (by linarith) hc
    linarith only [h2, h3, hW]
  have hG0 : 0 ≤ W + c * Y + c * (A + P + 1) := by positivity
  have t1 : 64 * φ * (W + c * Y + c * (A + P + 1)) ≤ 64 * (1 + 4 * c) * a ^ 2 := by
    have := mul_le_mul hφ hG hG0 ha0
    nlinarith only [this]
  have t2 : 32 * W * (Y + 1) ≤ 64 * a ^ 2 := by
    have := mul_le_mul hW (by linarith : Y + 1 ≤ 2 * a) (by linarith) ha0
    nlinarith only [this]
  have t3 : 8 * c * (B + 3 * m * A + 1 + φ) ≤ 48 * c * a ^ 2 := by
    have h2 : m * A ≤ a * a := mul_le_mul hm hA hA0 ha0
    have h3 : B + 3 * m * A + 1 + φ ≤ 6 * a ^ 2 := by nlinarith only [h2, hB, h1, hφ, haa]
    have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 8 * c)
    nlinarith only [this]
  have t4 : 16 * c ^ 2 * Y ^ 2 ≤ 16 * c ^ 2 * a ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hY0 hY 2) (by positivity)
  have t5 : 16 * W * (8 * (1 + c) * (m + d) + 2 * c * Y) ≤ (256 + 288 * c) * a ^ 2 := by
    have h2 : 8 * (1 + c) * (m + d) ≤ 8 * (1 + c) * (2 * a) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : 2 * c * Y ≤ 2 * c * a := mul_le_mul_of_nonneg_left hY (by positivity)
    have h4 : 8 * (1 + c) * (m + d) + 2 * c * Y ≤ (16 + 18 * c) * a := by nlinarith only [h2, h3]
    have := mul_le_mul hW h4 (by positivity) ha0
    nlinarith only [this]
  nlinarith only [t1, t2, t3, t4, t5, h1, haa, hW, hφ]

/-- **The joint kinetic threshold is `≲ R³` up to the subpower, uniformly in `φ`**: no factor `U`.
The leading monomial is `W_S √(M_∞ B_S)`. -/
theorem kinJ0_le {CS cS K c : ℝ} (hCS : 0 ≤ CS) (hcS : 0 ≤ cS) (hK : 1 ≤ K) (hc : 0 ≤ c)
    {R₀ X R : ℝ} (hdom : JDom R₀ X R) {caps : Caps} (hcaps : CapsScaledJ K c X R caps) :
    kinJ0 CS cS X R caps ≤ (405 + 592 * c4 + 16 * c4 ^ 2) * (1 + K + CS) ^ 2 * R ^ 3 *
      Ex (2 * (c + cS)) R := by
  obtain ⟨⟨-, hP⟩, ⟨-, hY⟩, -, hA, hB, -, hW, -, -, -⟩ := hcaps
  have hR1 := hdom.one_lt_R
  have hR0 := hdom.R_pos
  have hEc : 1 ≤ Ex c R := hdom.one_le_Ex hc
  have hEs : 1 ≤ Ex cS R := hdom.one_le_Ex hcS
  have hEt : 1 ≤ Ex (c + cS) R := hdom.one_le_Ex (by linarith)
  have hEc' : Ex c R ≤ Ex (c + cS) R := hdom.Ex_le_Ex (by linarith)
  have hEs' : Ex cS R ≤ Ex (c + cS) R := hdom.Ex_le_Ex (by linarith)
  set e := 1 + K * Ex c R + CS * Ex cS R with he
  have he1 : 1 ≤ e := by
    have : 0 ≤ K * Ex c R := by positivity
    have : 0 ≤ CS * Ex cS R := by positivity
    linarith
  have heK : K * Ex c R ≤ e := by
    have : 0 ≤ CS * Ex cS R := by positivity
    linarith
  have heS : CS * Ex cS R ≤ e := by
    have : 0 ≤ K * Ex c R := by positivity
    linarith
  set ρ := R ^ ((3 : ℝ) / 2) with hρ
  have hρ2 : ρ ^ 2 = R ^ 3 := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le, ← Real.rpow_natCast]
    norm_num
  have hRρ : R ≤ ρ := by
    calc R = R ^ (1 : ℝ) := (Real.rpow_one R).symm
      _ ≤ ρ := Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num)
  have h1ρ : 1 ≤ ρ := hR1.le.trans hRρ
  set a := e * ρ with ha
  have ha1 : 1 ≤ a := one_le_mul_of_one_le_of_one_le he1 h1ρ
  have ha0 : 0 ≤ a := by linarith
  have hEρ : ∀ {x E : ℝ}, x ≤ E * ρ → E ≤ e → x ≤ a := fun hx hE =>
    hx.trans (mul_le_mul_of_nonneg_right hE (by linarith))
  have hU0 : 0 ≤ jointU X := by linarith [hdom.one_lt_U]
  have hU : jointU X ≤ R := by
    refine hdom.U_le.trans ?_
    calc R ^ ((1 : ℝ) / 8) ≤ R ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num)
      _ = R := Real.rpow_one R
  have hT : jointT X R ≤ R := by
    have h1 : jointT X R ≤ Real.sqrt (R * R) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hU hR0.le)
    rwa [Real.sqrt_mul_self hR0.le] at h1
  have hKE0 : 0 ≤ K * Ex c R := by positivity
  have hW' : cp caps.WS ≤ a := cp_le ha0 (hEρ (by simpa [slowExpHA] using hW) heK)
  have hA' : cp caps.AS ≤ a := cp_le ha0 (hEρ (by simpa [slowExpHA] using hA) heK)
  have hY' : cp caps.yF ≤ a := cp_le ha0 (hEρ (hY.trans (mul_le_mul_of_nonneg_left
    (hT.trans hRρ) hKE0)) heK)
  have hP' : cp caps.PF ≤ a := cp_le ha0 (hEρ (hP.trans (mul_le_mul_of_nonneg_left
    (hU.trans hRρ) hKE0)) heK)
  have hMR : CS * Ex cS R * R ≤ e * R := mul_le_mul_of_nonneg_right heS hR0.le
  have hm' : cp (CS * Ex cS R * R) ≤ e * R :=
    cp_le (by positivity) hMR
  have hm'' : cp (CS * Ex cS R * R) ≤ a := hm'.trans (mul_le_mul_of_nonneg_left hRρ (by linarith))
  have hB1 : cp caps.BS ≤ e * R ^ 2 := by
    refine cp_le (by positivity) (hB.trans ?_)
    have e2 : R ^ slowExpHA.eB = R ^ 2 := by
      simp only [slowExpHA]
      exact_mod_cast Real.rpow_natCast R 2
    rw [e2]
    exact mul_le_mul_of_nonneg_right heK (by positivity)
  have ha2 : a ^ 2 = e ^ 2 * R ^ 3 := by rw [ha, mul_pow, hρ2]
  have hB' : cp caps.BS ≤ a ^ 2 := by
    rw [ha2]
    refine hB1.trans ?_
    have h1 : e ≤ e ^ 2 := by nlinarith
    have h2 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR1.le (by norm_num)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hd' : Real.sqrt (cp (CS * Ex cS R * R) * cp caps.BS) ≤ a := by
    rw [← Real.sqrt_sq ha0]
    refine Real.sqrt_le_sqrt ?_
    rw [ha2]
    calc cp (CS * Ex cS R * R) * cp caps.BS ≤ (e * R) * (e * R ^ 2) :=
          mul_le_mul hm' hB1 (cp_nonneg _) (by positivity)
      _ = e ^ 2 * R ^ 3 := by ring
  have hX0 : 0 ≤ X := by linarith [hdom.one_lt_X]
  have hφ : R - X ≤ a := by
    have : R ≤ a := hRρ.trans (le_mul_of_one_le_left (by linarith) he1)
    linarith
  have hmain := kinJ_alg (c := c4) (a := a) (φ := R - X) (m := cp (CS * Ex cS R * R))
    (W := cp caps.WS) (Y := cp caps.yF) (A := cp caps.AS) (B := cp caps.BS) (P := cp caps.PF)
    (d := Real.sqrt (cp (CS * Ex cS R * R) * cp caps.BS)) c4_pos.le ha1 (cp_nonneg _)
    (cp_nonneg _) (cp_nonneg _) (cp_nonneg _) (cp_nonneg _) (Real.sqrt_nonneg _) hφ hm'' hW' hY'
    hA' hP' hd' hB'
  have hE2 : e ^ 2 ≤ (1 + K + CS) ^ 2 * Ex (2 * (c + cS)) R := by
    have h1 : e ≤ (1 + K + CS) * Ex (c + cS) R := by
      have h2 : K * Ex c R ≤ K * Ex (c + cS) R :=
        mul_le_mul_of_nonneg_left hEc' (by linarith)
      have h3 : CS * Ex cS R ≤ CS * Ex (c + cS) R := mul_le_mul_of_nonneg_left hEs' hCS
      rw [he]
      nlinarith only [h2, h3, hEt]
    have h4 := pow_le_pow_left₀ (by linarith) h1 2
    have e5 : Ex (2 * (c + cS)) R = Ex (c + cS) R ^ 2 := by
      rw [two_mul, Ex_add]
      ring
    rw [e5, ← mul_pow]
    exact h4
  have hC0 : 0 ≤ 405 + 592 * c4 + 16 * c4 ^ 2 := by
    have := c4_pos
    positivity
  have hR3 : 0 ≤ R ^ 3 := by positivity
  calc kinJ0 CS cS X R caps ≤ (405 + 592 * c4 + 16 * c4 ^ 2) * a ^ 2 := hmain
    _ = (405 + 592 * c4 + 16 * c4 ^ 2) * (e ^ 2 * R ^ 3) := by rw [ha2]
    _ ≤ (405 + 592 * c4 + 16 * c4 ^ 2) *
        (((1 + K + CS) ^ 2 * Ex (2 * (c + cS)) R) * R ^ 3) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE2 hR3) hC0
    _ = _ := by ring

/-- **The field `below₀` of `JointInterfaces`**: `q₀ ≤ C Q Ex(C₀, R)` on all scaled caps (in fact
`≤ C R³ Ex(C₀, R)`, `kinJ0_le`), for every `C_S, c_S ≥ 0`. -/
theorem kinJ0_below {CS cS : ℝ} (hCS : 0 ≤ CS) (hcS : 0 ≤ cS) : JointBelow (kinJ0 CS cS) := by
  intro K c hK hc
  refine ⟨(405 + 592 * c4 + 16 * c4 ^ 2) * (1 + K + CS) ^ 2, 2 * (c + cS), 0, fun X R hdom caps
    hcaps => (kinJ0_le hCS hcS hK hc hdom hcaps).trans ?_⟩
  have hU := hdom.one_lt_U
  have hR := hdom.R_pos
  have hC : 0 ≤ (405 + 592 * c4 + 16 * c4 ^ 2) * (1 + K + CS) ^ 2 := by
    have := c4_pos
    positivity
  have hQ : R ^ 3 ≤ jointQ X R := by
    unfold jointQ
    exact le_mul_of_one_le_left (by positivity) hU.le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hC) (Ex_pos _ _).le

end OVNS.Quant

end
