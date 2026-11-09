import OddViscousNS.Quant.Energy.Interfaces
import OddViscousNS.Quant.Energy.Slow.Equation

/-!
# Theorem 1.2, joint large force: the analytic interfaces (step J0, revised on the sources)

Named `Prop`s for the outputs of the analytic layers of the joint bound
`quantitative_joint_force` (`OddViscousNS/Quant.lean`), mirroring
`OddViscousNS/Quant/Energy/Interfaces.lean`; the plan is
`OddViscousNS_data/reports/t12_joint_route.md` (cited below as "the survey"), the source is TeX
`quantitative_regimes.tex` §Joint.  The regimes layer (`Joint/Regimes.lean`) proves the joint
theorem from these `Prop`s.

## The regime
`X = e^e + μ`, `R = X + φ`, `U = X^{1719/719}` on `R ≥ max(R₀, X²⁴)` (`JDom`), so `U ≤ R^{1/8}`:
the force dominates.  The clocks are `T = √(UR)` (`jointT`, a norm scale, not a time), `Q = UR³`
(`jointQ`) and the virtual coefficient `B_* = T/P_F` (`jointBs`).  Prospective sizes:
`P_F, √J_F ≍ U`, `y ≍ T`, `λ_* ≍ R/U`, `(M_∞, A_S, W_S, B_S, J_S) ≍ (R, R^{3/2}, R^{3/2}, R², R³)`,
up to the subpower factors tracked by `CapsScaledJ`.
All interfaces are at the radii `(μ, φ) = (X, R − X)`: every constant below is absolute, and all
dependence on the force is through `R`.

## What is reused verbatim
`Caps`, `OnPrefix`, `PrefixHyp`, `PieceHyp`, `ActualSol`, `SlowLevel`, `slowExpHA`, and the
corrected slow field `corrSlow = y_S`, `slowCorr = R_S` of `Energy/Slow/Equation.lean`.

## Corrections to the survey's draft `t12_evidence/t12joint/lean/JointIface.lean`
The draft type-checks, but its clauses cannot be discharged as written.
1. **Piece starts (E7-P).**  The draft's `SlowCapsJoint` bounds the slow norms from `PieceHyp`
   alone.  This is exactly the defect of the first fixed-force `SlowCapsInterface`: nothing bounds
   the values at the piece start.  Worse here, the sup norm `M_∞` is not controlled by any cap
   (`W_S ≍ R^{3/2}`), and a vertical spike of height `R^{3/2}` and width `R^{−1/2}` is compatible
   with all the caps at the start.  Fix: `SlowCapsJoint` starts from the start levels `L` and the
   backward-unit history `SlowHistory`, the device of the sources; the decision and its reasons are
   in the docstring of `SlowCapsJoint`.
2. **Feeding the slow output forward (E5-J, E8-J).**  The draft reuses `H1EnergyInterface` and has
   `H2EnergyInterfaceB`, both from `PieceHyp` alone.  The tied low mixed role needs `M_∞ ≲ R`, not
   the cap `W_S`: paid with `W_S` it costs `R³T²`, above `Q`.  So those clauses are unprovable at
   the joint caps.  Fix: `JointPiece` hands them the E7-P output on the same piece, namely the
   bound on `slowSup` and `SlowOut`.  Chronology: E7-P uses only `PieceHyp` and the start
   history, so this is not circular, and `Caps` need not grow.
3. **The kinetic floor (E4-J).**  The survey reuses `KineticInterface` as is.  But the floor of
   TeX eq. quant-kinetic-floor has `D₄ ∋ √(R B_S)`, where `R` is `M_∞`: `‖∇S‖₄² ≲ M_∞ b` (Body 36
   LOCAL515: "these use only the earlier physical maximum"; Body 74: the slow maximum is
   "available before N16").  From `PrefixHyp` alone the estimate is `‖∇w‖₄² ≲ a_S b_S`, which
   costs `W_S √(a_S b_S) ≍ R^{13/4}`, above `Q` at `U ≍ 1`.  Fix: `KineticJoint` takes the bound
   on `slowSup` on the prefix.  It is implied by `KineticInterface`, so it is a weakening.
4. **The kinetic scale (E8-J).**  `B ≍ U/X` needs `‖F‖₀ ≲ X` along the piece, but `PieceHyp` gives
   only `‖F‖₀ ≤ a_F ≤ P_F` (the kinetic bound needs the piece-start value), and the draft's free
   number `Bs` is tied to one cap set while the interface quantifies over all of them.  Fix:
   `Bs : Caps → ℝ`, with the explicit guard `C_G ‖F‖_θ ≤ B_*` as a hypothesis.  In the joint
   regime the guard is free: `C_G P_F ≤ T/P_F` since `T/U² ≥ R^{5/16}`.  So `ρ_F` and the precise
   `v_* = XT/U²` of the TeX are not needed: `T/P_F` is `v_* B` up to an absolute factor.
5. **Quantifiers (`JointBelow`).**  The draft's `JointBelow` is at one abstract family `caps X R`,
   with no link to the closure of the bootstrap; the actual caps depend on the constants of
   E5/E7.  Fix, as for `DegreeBelow`: every `K, c`, every scaled cap set (`CapsScaledJ`).  Also all
   thresholds may depend on the resonant constants (`JointData`), which the draft's `q₂` may not.
6. **The fitted monomials.**  The survey's `m3 = (a + W + M) b D⁻¹ √(P_S/λ_*)` has the right
   exponent and the wrong shape.  The true rows are `rowM2`, `rowM3`: the term `a b` is in no
   source, and the `δ₀` companion is real.  They are Lean monomials now, and are paid by theorem.
7. **One subpower on all the levels and outputs cannot close at bounded `Tp`** (J0's own draft).
   Free decay of a shear mode, `|k|² ≍ R`, amplitude `ex R`, `F = 0`, `B(S,S) = 0`, starts at the
   levels `‖S‖₀ ≍ ex R`, `a_S ≍ ex R^{3/2}`, `b_S ≍ ex R²` and has `∫ b_S² ≍ ex² R³`, above the
   claimed `ex R³`; and an `L²` level `ex R` is regained only as `ex R`, so the strain stays `≍ p ex
   R`.  Fix: `levelsJ`: `L₀, L₁` carry no subpower (the sources' `R₀ ≍ R`), the other levels carry
   `Ex (c/3) R`, all outputs carry `Ex c R`.

Two further changes: the near conditions stay explicit (`NearPaid`), so that the regimes layer
pays them and the origin of `Ex` is proved there; and `Tp` is left free up to a subpower (`Tp_le`),
though the decision at `SlowCapsJoint` is that it stays bounded.  The chronology is slow (E7-P),
kinetic (E4-J), `H¹` (E5-J), `H²` (E8-J), as in the TeX and Body 47.

## Status and provenance
Discharged elsewhere: `ResH1`, `ResH2` (`Arith/`), E4-J (`kineticJoint`, `Joint/Kinetic/Main.lean`),
E9-J (`jointProfiles`, `Energy/NearJ/Main.lean`).  Proved here or in `Joint/Arith.lean`: the payment
of the rows 2, 3 of Table quant-metric and of the raised root floor.  Open: E5-J, E7-P, E8-J and the
rest of the role table.

Sources.  "Body n" refers to the proof volume `upstream/proofs/THEOREM_1_2_PROOF_VOLUME.md`.
A path `checkpoints/…` or `validation_…/…` is relative to `upstream/bodies_v7/joint/`: the recovered
documents, whose status is in `reports/t12_joint_documents.md` §4.  Every document cited below was
found; all checks are "candidate-exposed, same-family" AI reconstructions, not reviewed, and
`R³` is tied in 8+ independent roles (survey §1.2, §5).  **[design]** marks a clause of this layer
which is not read off a source; its justification is then stated in place.

**Not needed at the joint scale** (7 of the 19 ids of the survey's flat list; report §4).  No clause
below rests on them:
* NEW413, `checkpoints/COMPLETE_UF_WEIGHTED_RESIDUE_413_CANDIDATE.md`: a same-slot rebind that only
  quotes the proper profile, whose owner is LOCAL368 (Body 57);
* LOCAL428, `checkpoints/FULL_CENTERED_HEIGHT_PRODUCT_428_LOCAL_CANDIDATE.md`: a height-product gain
  in `H`, and `H` is fixed here (Body 34);
* LOCAL670, `checkpoints/LOCAL670_PHYSICAL_SFF_KINETIC_AND_X1_FORCE_CANDIDATE.md`: "optional … not a
  premise" (Body 45);
* F650, `checkpoints/COMPLETE_FORCED_LOG_Z_BALANCE_650_CANDIDATE.md`, and F660,
  `checkpoints/COMPLETE_FORCED_SIGNED_COMPARABLE_BALANCE_660_CANDIDATE.md`: whole rebinds,
  superseded by F664, F675, F686.  Their local content is in Bodies 40–42, 78.  (The check of F650,
  `checkpoints/F650_LOG_Z_HIGH_FORCE_WHOLE_CHECKED_RECONSTRUCTION.md`, stays the only check of
  LOCAL649.)
* LOCAL404, `checkpoints/UNFORCED_ACTUAL_SLOW_H1_H2_CAPS_404_LOCAL_CANDIDATE.md`: unforced graph;
* LOCAL362, `checkpoints/SINGLE_ANCESTRAL_TIMING_362_LOCAL_CANDIDATE.md`: **must not be used**, see
  the trap in `H1EnergyJoint`.
-/

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace OVNS.Quant

/-! ### The subpower and the clocks -/

/-- The subpower `exp(c log t / log log t)` of the joint theorem. -/
def Ex (c t : ℝ) : ℝ := Real.exp (c * Real.log t / Real.log (Real.log t))

/-- `U = X^β`, `β = 1719/719`: the fast `H¹` clock. -/
def jointU (X : ℝ) : ℝ := X ^ ((1719 : ℝ) / 719)

/-- `T_* = √(UR)`: the fast `H²` clock, a norm scale (TeX, joint proof). -/
def jointT (X R : ℝ) : ℝ := Real.sqrt (jointU X * R)

/-- `Q_* = U R³`: the joint trial, up to the subpower. -/
def jointQ (X R : ℝ) : ℝ := jointU X * R ^ 3

/-- The joint domain: `X ≥ e^e` and `R ≥ max(R₀, X²⁴)`. -/
def JDom (R₀ X R : ℝ) : Prop := Real.exp (Real.exp 1) ≤ X ∧ max R₀ (X ^ (24 : ℝ)) ≤ R

/-- The virtual coefficient `B_* = T/P_F`.  The TeX has `B_* = v_* B`, `v_* = XT/U²`; since only
`B ≤ B_*` matters (see `H2EnergyInterfaceB`), we normalize `A B_* = T`, whence
`W_* = (297/128) T²` and `λ_* = (16/11) T²/P_F²` (`lamStar_jointBs`, `WStar_jointBs`). -/
def jointBs (X R : ℝ) (caps : Caps) : ℝ := jointT X R / caps.PF

/-- `lamStar v A B = lamStar 1 A (v B)`: the fixed-force barrier covers every `v_*`. -/
theorem lamStar_eq (v A B : ℝ) : lamStar v A B = lamStar 1 A (v * B) := by
  unfold lamStar bStar
  ring

/-- `WStar v A B = WStar 1 A (v B)`. -/
theorem WStar_eq (v A B : ℝ) : WStar v A B = WStar 1 A (v * B) := by
  unfold WStar bStar
  ring

/-- `W_* = (297/128) T²` at `B_* = T/A`. -/
theorem WStar_jointBs {A T : ℝ} (hA : A ≠ 0) : WStar 1 A (T / A) = 297 / 128 * T ^ 2 := by
  unfold WStar bStar dZero
  field_simp
  ring

/-- `λ_* = (16/11) T²/A²` at `B_* = T/A`. -/
theorem lamStar_jointBs {A T : ℝ} (hA : A ≠ 0) :
    lamStar 1 A (T / A) = 16 / 11 * T ^ 2 / A ^ 2 := by
  unfold lamStar bStar dZero
  field_simp
  ring

/-! ### The physical sup norm of the slow part -/

/-- The physical slow field of a summable slow `Field`, on the horizontal torus. -/
def physS (u : Field) (x : UnitAddTorus (Fin 2)) : V3 :=
  ∑' k : Fin 2 → ℤ, UnitAddTorus.mFourier k x • u ![k 0, k 1, 0]

/-- The sup norm `M_∞ = ‖S‖_∞` of the slow part. -/
def slowSup (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  ⨆ x : UnitAddTorus (Fin 2), ‖physS (PiS (actual r g y t)) x‖

/-- The modes of `physS` are distinct modes of `u`. -/
theorem slowMode_injective :
    Function.Injective fun k : Fin 2 → ℤ ↦ (![k 0, k 1, 0] : Mode) := by
  intro a b hab
  funext i
  fin_cases i
  · exact congrFun hab 0
  · exact congrFun hab 1

theorem norm_physS_term_le (u : Field) (x : UnitAddTorus (Fin 2)) (k : Fin 2 → ℤ) :
    ‖UnitAddTorus.mFourier k x • u ![k 0, k 1, 0]‖ ≤ ‖u ![k 0, k 1, 0]‖ := by
  rw [norm_smul]
  have h1 : ‖UnitAddTorus.mFourier k x‖ ≤ 1 :=
    (ContinuousMap.norm_coe_le_norm _ x).trans_eq UnitAddTorus.mFourier_norm
  exact mul_le_of_le_one_left (norm_nonneg _) h1

/-- The series of `physS` converges absolutely on `H²`. -/
theorem summable_physS {u : Field} (hu : InH 2 u) (x : UnitAddTorus (Fin 2)) :
    Summable fun k : Fin 2 → ℤ ↦ ‖UnitAddTorus.mFourier k x • u ![k 0, k 1, 0]‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_physS_term_le u x)
    ((summable_wiener hu).comp_injective slowMode_injective)

/-- The Wiener norm dominates the physical slow field. -/
theorem norm_physS_le_wiener {u : Field} (hu : InH 2 u) (x : UnitAddTorus (Fin 2)) :
    ‖physS u x‖ ≤ wiener u := by
  have hs : Summable fun k : Mode ↦ ‖u k‖ := summable_wiener hu
  have hsι : Summable fun k : Fin 2 → ℤ ↦ ‖u ![k 0, k 1, 0]‖ :=
    hs.comp_injective slowMode_injective
  have hsm := summable_physS hu x
  calc ‖physS u x‖ ≤ ∑' k : Fin 2 → ℤ, ‖UnitAddTorus.mFourier k x • u ![k 0, k 1, 0]‖ :=
        norm_tsum_le_tsum_norm hsm
    _ ≤ ∑' k : Fin 2 → ℤ, ‖u ![k 0, k 1, 0]‖ := hsm.tsum_le_tsum (norm_physS_term_le u x) hsι
    _ ≤ ∑' k, ‖u k‖ :=
        tsum_comp_le_tsum_of_inj hs (fun _ ↦ norm_nonneg _) slowMode_injective

/-- `physS` is additive on `H²`. -/
theorem physS_add {u v : Field} (hu : InH 2 u) (hv : InH 2 v) (x : UnitAddTorus (Fin 2)) :
    physS (u + v) x = physS u x + physS v x := by
  unfold physS
  rw [← (summable_physS hu x).of_norm.tsum_add (summable_physS hv x).of_norm]
  exact tsum_congr fun k ↦ by simp only [Pi.add_apply, smul_add]

/-- `M_∞ ≤ W_S` (TeX; `‖S‖_∞ ≤ ‖Ŝ‖_{ℓ¹}`): the sup norm is a true sup, below the Wiener cap. -/
theorem slowSup_le_slowWiener {r : ℝ} {g : Field} {y : ℝ → Field} {t : ℝ}
    (h : InH 2 (PiS (actual r g y t))) : slowSup r g y t ≤ slowWiener r g y t :=
  ciSup_le fun x ↦ norm_physS_le_wiener h x

/-- **`M_∞` of `S` from the corrected field**: `S = y_S − R_S`, so a sup bound on `y_S` bounds
`slowSup` after adding the Wiener norm of `R_S`, which is `≤ c₄ ‖R_S‖₂ ≤ c₄ δ₀` by the trace clause.
This is the last step of the sup bound of E7-P, which is a bound on `S` itself (Body 27). -/
theorem slowSup_le_corrected {r : ℝ} {g : Field} {y : ℝ → Field} {t M : ℝ}
    (hS : InH 2 (PiS (actual r g y t))) (hR : InH 2 (slowCorr r g y t))
    (hM : ∀ x, ‖physS (corrSlow r g y t) x‖ ≤ M) :
    slowSup r g y t ≤ M + wiener (slowCorr r g y t) := by
  refine ciSup_le fun x ↦ ?_
  have e : physS (corrSlow r g y t) x =
      physS (PiS (actual r g y t)) x + physS (slowCorr r g y t) x := physS_add hS hR x
  have h1 : ‖physS (PiS (actual r g y t)) x‖ ≤
      ‖physS (corrSlow r g y t) x‖ + ‖physS (slowCorr r g y t) x‖ := by
    rw [e]
    simpa using norm_sub_le (physS (PiS (actual r g y t)) x + physS (slowCorr r g y t) x)
      (physS (slowCorr r g y t) x)
  have h2 := norm_physS_le_wiener hR x
  linarith [hM x]

/-- `slowSup` dominates the pointwise values of the physical slow field. -/
theorem norm_physS_le_slowSup {r : ℝ} {g : Field} {y : ℝ → Field} {t : ℝ}
    (h : InH 2 (PiS (actual r g y t))) (x : UnitAddTorus (Fin 2)) :
    ‖physS (PiS (actual r g y t)) x‖ ≤ slowSup r g y t :=
  le_ciSup (f := fun x ↦ ‖physS (PiS (actual r g y t)) x‖)
    ⟨_, by rintro _ ⟨x, rfl⟩; exact norm_physS_le_wiener h x⟩ x

/-! ### E9-J: the near profiles with explicit subpower -/

/-- **E9-J output** (TeX eq. quant-profiles; survey §1.3, block J1): `N(q) ≤ C q^{−1/2} Ex(c, q)`
and `P(q) ≤ C q^{−1/3} Ex(c, q)` for large `q`.  This is where `Ex` comes from: at the tied low
mixed role a fixed-`δ` profile would only give `R^{3+ε}`.  For `P` the exponent `−1/3` is needed
(`−3/10` gives `R^{40/13}`).  Proved: `jointProfiles` (`Energy/NearJ/Main.lean`), for the moments
`nearN`, `nearP`. -/
def JointProfiles (N P : ℝ → ℝ) : Prop :=
  ∃ c C q₀ : ℝ, 0 ≤ c ∧ 0 ≤ C ∧ ∀ q : ℝ, q₀ ≤ q →
    N q ≤ C * q ^ (-(1 : ℝ) / 2) * Ex c q ∧ P q ≤ C * q ^ (-(1 : ℝ) / 3) * Ex c q

/-- The near payment at the threshold `q`: the near moments `N`, `P` are paid by the leading
coefficients `LN`, `LP` (a sum of the near roles of E5-J and E8-J).  Survey §1.2, §1.3:
`LN ≳ M_∞ y` (roles 15, 31 at the tie, Body 27, with `M_∞ ≤ Minf`) and `√P_F y^{3/2}` (the purefast
term, with a polynomial gap); `LP ≳ U^{1/4} √B_S` (the `H¹` quartic). -/
def NearPaid (LN LP : Caps → ℝ) (N P : ℝ → ℝ) (caps : Caps) (q : ℝ) : Prop :=
  LN caps * N q ≤ 1 ∧ LP caps * P q ≤ 1

/-! ### E7-P: the slow caps in the strict-improvement form -/

/-- `δ₀ = 2⁻¹⁴`: the budget of the `H²` trace of the slow corrector, at every actual time (`delta0`
of F301, `checkpoints/COMPLETE_FORCED_SMALL_SLOW_301_CANDIDATE.md`). -/
def delta0 : ℝ := 1 / 2 ^ 14

/-- The slow `H³` price `P_S` of a clip of length `ℓ`: `C ex (R⁴ + ℓ R⁵)`.  At `ℓ = 1/λ_*` this is
`P_S ≲ R⁴ + R⁵/λ_* ≲ U R⁴` (Body 47), at `ℓ = 1` the unit extension `λ_* P_S ≲ R⁵`.  TeX eq.
quant-short-slow has `[(B_S + δ₀)² + R⁵/λ_* + F_src²]`; Bodies 26, 45 have `p² R⁵/λ_*`.
**[design]** all clip lengths at once, with no `λ_*`: this keeps the slow outputs caps-free (J0
doubt 3).  The proof is the integration of eq. quant-slow-hessian over the clip, which is the same
for every length (Body 24: "by the identical estimate over length at most one"). -/
def slowPrice (C ex R ℓ : ℝ) : ℝ := C * ex * (R ^ 4 + ℓ * R ^ 5)

/-- **The slow outputs fed forward to E5-J and E8-J** on a piece `[s, t]`, besides the sup bound
(which is a field of `JointPiece`).  This is the list of report `t12_joint_documents.md` §3:
* `trace`: `‖R_S‖₂ ≤ δ₀` at every time.  It gives the tail `b_> ≤ D⁻¹ c_y + δ₀` of row 3, from
  `S = y_S − R_S` (LOCAL440 step 1).  Paid by the raised floor (`hnorm_slowCorr_le`, `slowCorr_le`);
* `cy_int`, `clip`: `∫_clip c_y² ≤ P_S`, for `c_y = ‖y_S‖₃` (TeX Lemma quant-short-metric, eq.
  quant-short-slow): whence `∫_clip c_y ≤ √(ℓ P_S)`, which is the weighted high-ancestor row;
* `kin`: `∫ a_S², ∫ W_S² ≲ R²` up to the subpower on every unit (Body 38, "the true actual early
  slow kinetic integral"; the unit histories of NEW392,
  `checkpoints/COMPLETE_FORCED_POLYNOMIAL_BELOW_FOUR_392_CANDIDATE.md`): the timed `E1` mass;
* `rest`: any further slot found by block J5.  None is known today.
The physical product `‖DS‖₄² ≲ M_∞ b` is not a slot: it holds at each time (`GN.gn_tensor`). -/
structure SlowOut (C ex R : ℝ) (Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop) (r : ℝ) (g : Field)
    (y : ℝ → Field) (s t : ℝ) : Prop where
  /-- `‖R_S‖₂ ≤ δ₀` on the piece. -/
  trace : ∀ u ∈ Icc s t, hnorm 2 (slowCorr r g y u) ≤ delta0
  /-- `c_y = ‖y_S‖₃` is square integrable on the piece. -/
  cy_int : IntervalIntegrable (fun u ↦ hnorm 3 (corrSlow r g y u) ^ 2) volume s t
  /-- `∫_clip c_y² ≤ P_S`, on every clip of length at most one. -/
  clip : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ 1 →
    (∫ u in u₁..u₂, hnorm 3 (corrSlow r g y u) ^ 2) ≤ slowPrice C ex R (u₂ - u₁)
  /-- The slow kinetic integrals on every unit. -/
  kin : ∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ 1 →
    (∫ u in u₁..u₂, slowNorm 1 r g y u ^ 2) ≤ C * ex * R ^ 2 ∧
      (∫ u in u₁..u₂, slowWiener r g y u ^ 2) ≤ C * ex * R ^ 2
  /-- The remaining slots. -/
  rest : Sl r g y s t

/-- **The `R_S` trace is paid by the raised floor**: `‖R_S‖₂ ≤ δ₀` once `2²⁰ (1 + c₄) Y² ≤ q`, from
`hnorm_slowCorr_le` (TeX: role 25 "pays every actual `R_S` `H²` trace before feedback"). -/
theorem slowCorr_le {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {t Y : ℝ}
    (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) (ht : 0 ≤ t) (htT : ENNReal.ofReal t < Ty)
    (hb : fastNorm 2 r g y t ≤ Y) (hq : 2 ^ 20 * (1 + c4) * Y ^ 2 ≤ |r|) :
    hnorm 2 (slowCorr r g y t) ≤ delta0 := by
  have hq0 : 0 < |r| := abs_pos.2 hr
  have hc := c4_pos
  have hb2 : fastNorm 2 r g y t ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) hb 2
  refine (hnorm_slowCorr_le h hr ht htT).2.trans ?_
  have e : 8 * c4 / |r| * fastNorm 2 r g y t ^ 2 = 8 * c4 * fastNorm 2 r g y t ^ 2 / |r| := by ring
  rw [e, div_le_iff₀ hq0]
  have h1 : 8 * c4 * fastNorm 2 r g y t ^ 2 ≤ 8 * c4 * Y ^ 2 :=
    mul_le_mul_of_nonneg_left hb2 (by positivity)
  have h2 : delta0 * (2 ^ 20 * (1 + c4) * Y ^ 2) ≤ delta0 * |r| :=
    mul_le_mul_of_nonneg_left hq (by norm_num [delta0])
  have h3 : 8 * c4 * Y ^ 2 ≤ delta0 * (2 ^ 20 * (1 + c4) * Y ^ 2) := by
    norm_num [delta0]
    nlinarith [sq_nonneg Y]
  linarith

/-- The start levels from their constants: `‖S‖₀ ≤ L₀ R`, `a_h ≤ L₁ R` with no subpower (the
sources' `R₀ ≍ R`, F301, NEW354), and `L_i e` on the other three.  See `SlowCapsJoint`. -/
def levelsJ (L : Fin 5 → ℝ) (e : ℝ) : Fin 5 → ℝ := fun i ↦ if i.val < 2 then L i else L i * e

/-- **The backward-unit history at a piece start `s`**, the start predicate of E7-P (`Lev` of
`StrictOn`): on the clipped backward unit `[max 0 (s − 1), s]`, the caps hold, and so do the start
levels `L`.  The clip at `0` is the true zero of the sources.  **[design]** The sources read only
the `L²` traces `‖y_S‖₀, ‖u‖₁` on that unit; the other three levels are carried because they come
free.  See `SlowCapsJoint`. -/
structure SlowHistory (caps : Caps) (L : Fin 5 → ℝ) (R : ℝ) (r : ℝ) (g : Field) (y : ℝ → Field)
    (s : ℝ) : Prop where
  /-- The caps on the clipped backward unit: with the threshold of the piece, they pay the source
  of the corrected slow equation there. -/
  onUnit : OnPrefix caps r g y (max 0 (s - 1)) s
  /-- The levels on the clipped backward unit: they give the left `L²` trace at each `u ≤ s`. -/
  level : ∀ u ∈ Icc (max 0 (s - 1)) s, SlowLevel L R slowExpHA r g y u

/-- **E7-P output** (TeX eq. quant-slow-caps; survey §3.4, block J2; replaces E7-HA), in the
strict-improvement form (amendment D4 of the fixed-force layer, with correction 1 of the module
docstring).  All constants are absolute.  Write `ex = Ex c R`, `e = Ex (c/3) R`.  For every solution
at the radii `(X, R − X)`, on every piece where the caps hold and the slow roles are paid, starting
from the backward-unit history at the levels `levelsJ L e`:
* pointwise on the piece `‖S‖₀, a_h ≤ C ex R`, `b_h, b_S ≤ C ex R²`, `a_S, W_S ≤ C ex R^{3/2}`, and
  `M_∞ ≤ C ex R` (`slowSup`);
* `∫ b_S² ≤ C ex R³` on the piece;
* the outputs `SlowOut`, consumed by E5-J and E8-J;
* on `[s + 1, t]` the levels hold again, as in the fixed-force `SlowCapsInterface`.

**`M_∞` is that of `S`, not of `y_S`.**  `slowSup` is the sup of `Π_S x`.  The proof bounds the
corrected field `y_S`, and must then subtract `R_S` (TeX: "the actual trace of `R_S` is subtracted
separately"; Body 27: `‖R_S‖_∞ ≲ δ₀`), so the trace floor of `Q0Prime` is used here, and
`slowSup_le_corrected` is the step.  Consumers: Body 56 has `M_inf = ‖S‖_∞`, and `kineticJoint`
takes exactly this object.

**Decision on the start predicate (J0 doubt 6): the backward-unit history, not `L^p` levels.**
Survey §3.4 proposes `L^p` and sup levels at `s`, propagated by an Alikakos iteration.  The sources
instead read the previous unit: Duhamel on the clipped backward unit `[max 0 (t − 1), t]` for the
drift-independent scalar propagator, with the homogeneous term at `t ≥ 1` paid by `L² → L^p`
smoothing of the true left `L²` trace at `t − 1`, at `t ≤ 1` by the true-zero `H¹` vorticity, and
the source on the same unit (Body 55 for `v`; Bodies 24, 26 for `ω` at `p = 2⌈8 + ln R⌉`; Body 27 at
`p = 4`; checks Bodies 81, 82, 83; TeX: "actual preceding kinetic unit intervals", and "the slow
source estimates are restricted and square-summed across at most two already established pieces").
We take the sources' reading.  Reasons:
1. The Alikakos law `M_p' + (c/p) M_p ≤ ‖F‖_p` needs the source in `L¹_t L^p_x`, and the source is
   not there: `f = g_S + r_S` with `‖r_S‖_{L²(I;H¹)} ≤ 1/16` only (Body 26), so `curl r_S` is only
   `L²_t L²_x` (Body 83: "its separate true residual curl is L2-in-time L2"; Lean:
   `corrRes_budget`).  No role pays an `L^p_x` bound of it.  The sources pay it by the kernel
   `τ^{−1/2+1/p}`, whose square integrates to `p/2`: a smoothing estimate, which the survey's law
   does not contain.
2. It keeps `Tp` bounded, see below; the rate `c/p` of Alikakos would force `Tp ≍ p ≍ log R`.
3. It costs nothing at the seam: `SlowHistory` is regained on the last unit of a piece with no
   analysis, the caps by restriction and the levels by the last clause of this statement, and it
   holds at `0`.  Both facts are theorems of `Joint/Regimes.lean` (`slowHistory_regained`,
   `slowHistory_zero`), so `Lev` is no longer an existential of this interface.

The price of this choice: the drift-uniform `L² → L^p` smoothing with an `L²_t L²_x` source is a new
analytic input.  The sources prove it with the propagator and its adjoint (Nash, duality; Body 55),
neither of which exists in Lean.  **[design]** A Moser iteration with a time cut-off on the solution
itself would avoid both; that is my remark for J2, in no source, untested.

**Decision on `Tp` (J0 doubt 5): bounded.**  The sources' `T_μ = max(4, 1 + ln(1 + μ² + 12))` (Body
13) is, on my reading, the time for the full kinetic energy to return from `μ²` to the budget `1 +
3φ²` of their restart.  `global_of_strictOn` does not use that return: it restarts at `a_F ≤ 2X`,
`W₀ ≤ 2X²` (proved), and E6 only needs `E₀, I_a = O(X²)`.  The slow side needs one unit to regain
the levels and one more for the seam: for `v` in the last unit `[v − 1, v] ⊂ [s + 1, t]`, hence `3 ≤
Tp` (`Tp_ge`; the TeX has `T ≥ 4`).  So J2 takes `Tp` constant, and `K_P` is absolute.  `Tp_le`
keeps its subpower form only as a hedge: if J2 fails to close at bounded `Tp`, the regimes layer
absorbs growth through `Z`, inside `Ex`, at the price of `A ≍ U` up to `Ex` (`capsJoint_scaled`).

**The levels (correction 7).**  `L₀, L₁` carry no subpower: `‖S‖₀, a_h ≲ R` closes on its own, since
the `L²` energy and the horizontal enstrophy have no nonlinear term (F301: `(‖y_S‖₀²)' + ‖y_S‖₁² ≤
‖f‖₁²`, `(‖u‖₁²)' + ‖u‖₂² ≤ ‖f‖₁²`), and Poincaré gives the contraction in one unit.  The order of
constants is triangular: `L₀, L₁`; then `L₂, L₃, L₄`; then `C`.  **[design]** Levels at `e`, outputs
at `ex = e³`: `∫ b_S²` and `P_S` contain the squares of the start levels of `a_S`, `b_S`, and the
factors `p`, `p²`, and `e ≥ p²` for large `R`.

Proof sources: Bodies 24, 26, 27, 30, 55 (NEW370, NEW377, NEW382, LOCAL390, NEW369; checks Bodies
81, 82, 83, 63); the early source and the slow caps of
`checkpoints/COMPLETE_FORCED_SMALL_SLOW_301_CANDIDATE.md` (F301, verdict
`ORIGINAL301_COMPLETE_FORCED_RECONSTRUCTION_AND_VERDICT.md` in
`validation_small_slow301_fresh/fresh_20261104/`) and the integral of
`checkpoints/COMPLETE_FORCED_SLOW_INTEGRAL_354_CANDIDATE.md` (NEW354, check
`checkpoints/FORCED_SLOW_INTEGRAL_354_CHECKED_RECONSTRUCTION.md`).  NEW378 and LOCAL319 are not slow
inputs: Body 27 binds them for the metric graph and for the high mixed Minkowski step, see
`H2EnergyInterfaceB`.  In the TeX, E7-HA (Nash, circle Hilbert and density step (A3), Riesz) is
asserted, not proved; Body 26 has a Calderón–Zygmund route to `‖T_ij‖_p ≲ p`.  The irrational
binomial route of survey §3.4 is in no source.  Body 14's early `A_S = K ρ^{3/2}` is a supplied
leaf: not to be built on; its unforced proof LOCAL404 does not apply.  Necessity: survey §3.1 (`R³`
iff the caps are exactly these). -/
def SlowCapsJoint (R₀ : ℝ) (Tp : ℝ → ℝ → ℝ) (qS : ℝ → ℝ → Caps → ℝ) (L : Fin 5 → ℝ) (C c : ℝ)
    (Sl : ℝ → ℝ → ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop) : Prop :=
  ∀ X R : ℝ, JDom R₀ X R → ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞),
    ActualSol X (R - X) r g y Ty → ∀ (caps : Caps) (s t : ℝ),
      PieceHyp (Tp X R) (qS X R) r g y Ty caps s t →
      SlowHistory caps (levelsJ L (Ex (c / 3) R)) R r g y s →
      (∀ u ∈ Icc s t, SlowLevel (fun _ ↦ C * Ex c R) R slowExpHA r g y u ∧
        slowWiener r g y u ≤ C * Ex c R * R ^ slowExpHA.eW ∧
        slowSup r g y u ≤ C * Ex c R * R) ∧
      (∫ u in s..t, slowNorm 2 r g y u ^ 2) ≤ C * Ex c R * R ^ slowExpHA.eJ ∧
      SlowOut C (Ex c R) R (Sl X R) r g y s t ∧
      ∀ v ∈ Icc (s + 1) t, SlowLevel (levelsJ L (Ex (c / 3) R)) R slowExpHA r g y v

/-! ### E4-J: the kinetic correction -/

/-- **E4-J output** (TeX eq. quant-kinetic, eq. quant-kinetic-floor; survey block J3): the clauses
of `KineticInterface`, on the prefixes where moreover `M_∞ ≤ Minf` (correction 3 of the module
docstring).  The functional `W₀` is global, as in E4; the sup bound is an E7-P output, so the
regimes layer supplies it on pieces and their sub-intervals.  The threshold `q₀` is the raised floor
`W_S (M_∞ + D₄ + y) + M_∞ A_S + y²`, `≲ R³` polylog (Bodies 36, 74, LOCAL515, on the N16 primitive
of Body 48, with Bodies 29, 56, 84 for the raised domain).  Proved: `kineticJoint`.  The Lean proof
re-derives the budget, and does not rest on the `W₀` inequality of F283,
`checkpoints/COMPLETE_FORCED_KINETIC_DISSIPATION_283_CANDIDATE.md` (verdict
`ORIGINAL283_COMPLETE_FORCED_RECONSTRUCTION_AND_VERDICT.md` in
`validation_kinetic283_fresh/fresh_20261104/`,
"full conditional pass"); F290 is recovered in `bodies_v7/checkpoints`. The monomials of `Q₀'` that
E4-J does not need go to the slow threshold: see `Q0Prime`. -/
def KineticJoint (μ φ Minf : ℝ) (q₀ : Caps → ℝ) : Prop :=
  ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞), ActualSol μ φ r g y Ty →
    ∃ W0 : ℝ → ℝ, ∀ (caps : Caps) (s t : ℝ), PrefixHyp q₀ r g y Ty caps s t →
      (∀ u ∈ Icc s t, slowSup r g y u ≤ Minf) →
      (∀ u ∈ Icc s t, 3 / 4 * fastNorm 0 r g y u ^ 2 ≤ W0 u ∧
        W0 u ≤ 5 / 4 * fastNorm 0 r g y u ^ 2) ∧
      (s = 0 → W0 0 ≤ 5 / 4 * (μ + 1 / 4) ^ 2) ∧
      W0 t - W0 s + (∫ u in s..t, fastNorm 1 r g y u ^ 2) ≤ (t - s) / 8 ∧
      W0 t ≤ max (W0 s) (5 / 32)

/-- `KineticJoint` is a weakening of `KineticInterface`. -/
theorem KineticInterface.toJoint {μ φ : ℝ} {q₀ : Caps → ℝ} (h : KineticInterface μ φ q₀)
    (Minf : ℝ) : KineticJoint μ φ Minf q₀ := fun r g y Ty hsol ↦
  (h r g y Ty hsol).imp fun _ hW caps s t hP _ ↦ hW caps s t hP

/-! ### E5-J and E8-J: the fast energies -/

/-- The hypotheses of the joint fast energies on a piece: `PieceHyp` with the energy's own
threshold, the output of E7-P on the same piece (fed forward: the sup bound, and `Sl`, which is
`SlowOut` in `JointInterfaces`), and the near payment at `q = |r|`. -/
structure JointPiece (Tp Minf : ℝ) (q : Caps → ℝ) (near : Caps → ℝ → Prop)
    (Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop) (r : ℝ) (g : Field) (y : ℝ → Field)
    (Ty : ℝ≥0∞) (caps : Caps) (s t : ℝ) : Prop extends PieceHyp Tp q r g y Ty caps s t where
  /-- `M_∞ ≤ Minf` on the piece. -/
  sup : ∀ u ∈ Icc s t, slowSup r g y u ≤ Minf
  /-- The other slow outputs on the piece. -/
  slow : Sl r g y s t
  /-- The near roles are paid. -/
  nearPaid : near caps |r|

/-- The conclusion of the `H¹` energy on `[s, t]`: literally the output of `H1EnergyInterface`. -/
def H1Output (σ Cs Nbar piTol : ℝ) (r : ℝ) (g : Field) (y : ℝ → Field) (s t : ℝ) : Prop :=
  ∃ E Nf ff m : ℝ → ℝ,
    (∀ u ∈ Icc s t, ell1 * fastNorm 1 r g y u ^ 2 ≤ 2 * E u ∧
      2 * E u ≤ u1 * fastNorm 1 r g y u ^ 2) ∧
    (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      E u₂ - E u₁ + 3 / 4 * (∫ u in u₁..u₂, fastNorm 2 r g y u ^ 2) ≤
        ∫ u in u₁..u₂, (Cs * fastNorm 1 r g y u ^ (3 - σ) * fastNorm 2 r g y u ^ σ +
          Nf u * fastNorm 2 r g y u + ff u + m u * fastNorm 1 r g y u ^ 2)) ∧
    (∀ u ∈ Icc s t, 0 ≤ ff u ∧ 0 ≤ m u) ∧
    IntervalIntegrable (fun u => Nf u ^ 2) volume s t ∧ IntervalIntegrable ff volume s t ∧
    IntervalIntegrable m volume s t ∧
    (∫ u in s..t, Nf u ^ 2) ≤ Nbar ^ 2 ∧ (∫ u in s..t, ff u) ≤ piTol ^ 2 ∧
    2 / ell1 * (∫ u in s..t, m u) ≤ 1

/-- **E5-J output** (TeX eq. quant-h1-energy, Lemma quant-static, Lemma quant-quartic at weight
one; survey block J5).  On a joint piece, the output of `H1EnergyInterface` holds, with `E` the
corrected energy with the **full** signed metric `M₁ = X₁ + X₂ + Z`, plus the cubic correction
`Q₃,₁` of Body 38.  Today's Lean E5 has `M₁ = X₁` only (`H1/Defs.lean`), which stops at `U²R⁶`
(survey §3.3): this interface is new work.

**Trap: the timed quota.**  The clause `(2/ℓ₁) ∫ m ≤ 1` is the integrating factor of LOCAL516 (Body
37, check Body 75) applied to the mass of LOCAL518 (Body 38, check Body 76), with its `Q₃,₁`.  The
additive timed quota of LOCAL362 (`checkpoints/SINGLE_ANCESTRAL_TIMING_362_LOCAL_CANDIDATE.md`),
kept by NEW378 (`checkpoints/COMPLETE_FORCED_UNWEIGHTED_CUBIC_HISTORY_378_CANDIDATE.md`), must
**not** be used at the joint scale: it pays `∫ m a_F²` against `π²` at the quota `δ₁ ≍ π²/P_F²`, so
the mass `q⁻¹R³` costs `X^{2β−2} R³`, above `U R³ = X^β R³` by `X^{β−2} = X^{281/719}`.  LOCAL516
plus LOCAL518 replace it, and this is why `m` stays a multiplier of `a_F²` here (`peak_bound_core`).

Clause by clause:
* coercivity: the static bounds of `X₂`, `Z` (`U(a²+aW+b²/D)`, `U M_∞ b`, own `D = R`): Body 36
  (LOCAL515, check Body 74), on the datum kinetic scale `A, P_F, √J_F ≍ U`, uniform in `φ`, of
  `checkpoints/COMPLETE_FORCED_DATUM_KINETIC_BALANCE_458_CANDIDATE.md` (NEW458, check
  `checkpoints/NEW458_DATUM_KINETIC_BALANCE_CHECKED_RECONSTRUCTION.md`);
* the energy inequality: the near part through `near`, whose normalization has no derivation
  (caveat (A1) of the fixed-force layer); the high quartic `Q₄,₁`: Bodies 35, 43 (LOCAL496,
  LOCAL663, checks Bodies 73, 79), with the exact helical vertex of
  `checkpoints/EXACT_VERTEX_PROPER_NATIVE_312_LOCAL_CANDIDATE.md` (LOCAL312, check
  `checkpoints/EXACT_VERTEX_312_CHECK_AND_E1_STATIC_EXTENSION.md`) and the proper profile of Body 57
  (LOCAL368), not NEW413;
* `∫ N_f² ≤ N̄²`, `∫ f_f ≤ π²` with `N̄, π ≲ X` **uniformly in `φ`**: the ten paired force roles 29,
  30, 32 (TeX Table joint): Bodies 40, 41 (LOCAL649, LOCAL655, Body 41 checked in Body 78), the
  first three roots of `checkpoints/FAST_SLOW_METRIC_FORCE_PAIRING_363_LOCAL_CANDIDATE.md`
  (LOCAL363, check `checkpoints/LOCAL363_METRIC_FORCE_CHECKED_RECONSTRUCTION.md`), the seven-class
  prices of `checkpoints/LOCAL577_X2_FIXED_VERTICAL_FIBRE_REPRICE_CHECKED_RECONSTRUCTION.md`
  (LOCAL577, no author file) and the filter bound of
  `checkpoints/ACTUAL_H3_Z_FORCE_PAIR_479_LOCAL_CANDIDATE.md` (LOCAL479, check
  `checkpoints/LOCAL479_ACTUAL_H3_Z_FORCE_PAIR_CHECKED_RECONSTRUCTION.md`);
* the timed quota: Bodies 37, 38, with mass `q⁻¹R³ + q⁻²R⁶` on units.  Inputs: only the unit
  histories `∫ a², ∫ W²` of `checkpoints/COMPLETE_FORCED_POLYNOMIAL_BELOW_FOUR_392_CANDIDATE.md`
  (NEW392, check `checkpoints/NEW392_BELOW_FOUR_CHECKED_RECONSTRUCTION.md`; its timed group is
  replaced), which are the slot `kin` of `SlowOut`; NEW458; the kernels of LOCAL83
  (`validation_forced85_full88/fresh_gate85_signed88_20261103A/INDEPENDENT_LOCAL83_GATE_001.md`,
  `forced_evolving_metric_v85/fresh_gate83_author85_20261103A/LOCAL83_FULL_RECONSTRUCTION_001.md`)
  and LOCAL95 (`checkpoints/FULL_GROUP_PREFACTOR_95_CANDIDATE.md`,
  `forced_group_reprice_v96/fresh_gate95_author96_20261103A/INDEPENDENT_LOCAL95_FULL_PROOF_001.md`).

`Cs` is a fixed resonant constant of the energy, possibly larger than that of `ResH1` (TeX: "the
enlarged fixed `C_s` does not change `U`"). -/
def H1EnergyJoint (σ Cs μ φ Tp Nbar piTol Minf : ℝ) (q₁ : Caps → ℝ) (near : Caps → ℝ → Prop)
    (Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop) : Prop :=
  ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞) (caps : Caps) (s t : ℝ),
    ActualSol μ φ r g y Ty → JointPiece Tp Minf q₁ near Sl r g y Ty caps s t →
    H1Output σ Cs Nbar piTol r g y s t

/-- `H1EnergyJoint` is a weakening of `H1EnergyInterface` (near conditions in the threshold). -/
theorem H1EnergyInterface.toJoint {σ Cs μ φ Tp Nbar piTol Minf : ℝ} {q₁ : Caps → ℝ}
    {near : Caps → ℝ → Prop} {Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop}
    (h : H1EnergyInterface σ Cs μ φ Tp Nbar piTol 0 q₁ fun _ ↦ 0) :
    H1EnergyJoint σ Cs μ φ Tp Nbar piTol Minf q₁ near Sl :=
  fun r g y Ty caps s t hsol hP ↦ h r g y Ty caps s t hsol hP.toPieceHyp (by simp)

/-- The conclusion of the `H²` energy on `[s, t]`: the output of `H2EnergyInterface` with `A` and
the coefficient `B` free. -/
def H2Output (A B m₀ : ℝ) (r : ℝ) (g : Field) (y : ℝ → Field) (s t : ℝ) : Prop :=
  ∃ W G H : ℝ → ℝ,
    (∀ u ∈ Icc s t, 31 / 32 * fastNorm 2 r g y u ^ 2 ≤ W u ∧
      W u ≤ 33 / 32 * fastNorm 2 r g y u ^ 2) ∧
    IntervalIntegrable (fun u => fastNorm 3 r g y u ^ 2) volume s t ∧
    (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
      W u₂ - W u₁ ≤ ∫ u in u₁..u₂, (-2 * dZero * fastNorm 3 r g y u ^ 2 +
        2 * B * fastNorm 2 r g y u * fastNorm 3 r g y u + G u * W u + H u)) ∧
    (∀ u ∈ Icc s t, 0 ≤ G u ∧ 0 ≤ H u) ∧
    IntervalIntegrable G volume s t ∧ IntervalIntegrable H volume s t ∧
    (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ 1 / lamStar 1 A B →
      (∫ u in u₁..u₂, G u) ≤ m₀ ∧ (∫ u in u₁..u₂, H u) ≤ WStar 1 A B / 32)

/-- **E8-J output, E10 input** (TeX eq. quant-metric at `s = 2`, Lemma quant-short-metric, Table
quant-metric, Lemma quant-quartic; survey block J5).  On a joint piece on which the guard
`C_G ‖F‖_θ ≤ B_*` holds, the output of `H2EnergyInterface` holds with the coefficient `B_* = Bs
caps`.  `C_G` is the resonant constant (`ResH2`, up to the metric factor).  The guard is what makes
the resonant term `≤ 2 B_* b_F c_F`, with no kinetic scale (correction 4); then `barrier_cap`
applies at `B := B_*`, since `lamStar v A B = lamStar 1 A (v B)` (`lamStar_eq`, `WStar_eq`).

The clip masses on `1/λ_*` are Table quant-metric, budget `2⁻³⁵` per clip (Body 47), with
`P_S ≲ U R⁴`, `λ_* ≍ R/U`.  The ten rows, their true forms and owners are report
`t12_joint_documents.md` §3.  Clause by clause:
* the signed two-root `X₂`, the high intermediate sector and the third correction `Q₃, Q₃,₁`
  (coercivity, rows 4–6): Body 33 (LOCAL474, check Body 71), on the kernels of LOCAL83, LOCAL95
  (paths at `H1EnergyJoint`); the outer-length split of
  `checkpoints/OUTER_LENGTH_SPLIT_AND_INDEPENDENT_FLOORS_449_LOCAL_CANDIDATE.md` and
  `checkpoints/COMPLETE_FORCED_OUTER_LENGTH_450_CANDIDATE.md` (LOCAL449, NEW450, check
  `checkpoints/LOCAL449_NEW450_OUTER_LENGTH_CHECKED_RECONSTRUCTION.md`; live for FAR and row 28, the
  split is redone in Body 43); the `Q₃` orientations of
  `checkpoints/THIRD_METRIC_TOTAL_PHASE_REMAINDER_466_LOCAL_CANDIDATE.md` and
  `checkpoints/COMPLETE_FORCED_THIRD_METRIC_467_CANDIDATE.md` (LOCAL466, NEW467, check
  `checkpoints/LOCAL466_NEW467_THIRD_METRIC_CHECKED_RECONSTRUCTION.md`); the two-root identity and
  convolution of `checkpoints/PAIRED_INNER_PHASE_DERIVATIVE_METRIC_457_LOCAL_CANDIDATE.md`
  (LOCAL457, author file only, re-derived in the checks of LOCAL466 and LOCAL474); NEW458;
* row 1, the comparable row `q⁻¹R⁴/λ_*`, tied at `Q`, and the last-edge split: Bodies 39, 42
  (LOCAL525, LOCAL659, checks Bodies 77, 78), with the seven classes of LOCAL577; its low part is
  the slot of `M_∞`;
* rows 2, 3, the two high-ancestor rows, tied at `Q`: `rowM2`, `rowM3`, part of the threshold
  through `JointData.q₂Full`, and paid by theorem (`highAnc_below`).  True forms: the `E₂^z` classes
  of `checkpoints/NEW378_UNWEIGHTED_CUBIC_HISTORY_CHECKED_RECONSTRUCTION.md` (NEW378, live for these
  rows only) with one ancestor at `|p| > D` give `q⁻¹(W_> b² + W b b_>)`
  (`checkpoints/PHASE_AND_ACTUAL_TAIL_SHORT_METRIC_440_LOCAL_CANDIDATE.md` step 1, LOCAL440, and
  `checkpoints/OPTIMIZED_CUTOFF_SHORT_METRIC_441_LOCAL_CANDIDATE.md`, LOCAL441, check
  `checkpoints/LOCAL440_441_NEW442_OUTER_PHASE_METRIC_CHECKED_RECONSTRUCTION.md`), with
  `W_> ≲ D⁻¹ b` and `b_> ≤ D⁻¹ c_y + δ₀` (the slots `trace`, `clip` of `SlowOut`).  The companions
  `q⁻¹ M_∞ b b_>` (the high ancestor of the low-last `X₂`, Body 42, printed with its `δ₀`) and
  `q⁻¹ f₁ b_{>cD}`, `f₁ ≲ M_∞ b` (differentiated, Bodies 33, 42) give the `M_∞`;
* rows 7–10, the primitive-separated high-last sector: Body 43 (LOCAL663, check Body 79);
* the quartic `Q₄`: Bodies 34, 46 (LOCAL488, LOCAL680, checks Bodies 72, 62), on the low/high split
  only of `checkpoints/ALL_LENGTH_LOW_VERTICAL_MIXED_391_LOCAL_CANDIDATE.md` (LOCAL391, check
  `checkpoints/LOCAL391_ALL_LENGTH_LOW_VERTICAL_CHECKED_RECONSTRUCTION.md`), the filter bound
  `‖H_{ψ,F}‖₂ ≲ (φ/q)(c_F + c_S) + φ²/q²` of LOCAL479 (path at `H1EnergyJoint`) and the proper
  profile of Body 57.  Body 34 also binds
  `checkpoints/RATIO_RESOLVED_LOW_MIXED_422_LOCAL_CANDIDATE.md` (LOCAL422, check
  `checkpoints/LOCAL422_NEW423_RATIO_RESOLVED_CHECKED_RECONSTRUCTION.md`) together with LOCAL428; at
  a fixed ratio `H₀` no ratio resolution should be used, but this was read at head and grep level
  only: J5 must confirm it. -/
def H2EnergyInterfaceB (θ CG μ φ Tp m₀ Minf : ℝ) (Bs q₂ : Caps → ℝ) (near : Caps → ℝ → Prop)
    (Sl : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop) : Prop :=
  ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞) (caps : Caps) (s t : ℝ),
    ActualSol μ φ r g y Ty → JointPiece Tp Minf q₂ near Sl r g y Ty caps s t →
    (∀ u ∈ Icc s t, CG * fastNorm θ r g y u ≤ Bs caps) →
    H2Output caps.PF (Bs caps) m₀ r g y s t

/-! ### The role table: thresholds at the joint scale -/

/-- The joint scaling of prospective caps, with constant `K` and subpower exponent `c`: `P_F ≍ U`,
`y ≍ T`, `J_F ≍ U²` two-sided up to `K Ex(c, R)` (polylogs of `Tp` are inside `Ex`), and the slow
caps at the exponents `slowExpHA`.  Mirrors `CapsScaled`. -/
def CapsScaledJ (K c X R : ℝ) (caps : Caps) : Prop :=
  (jointU X / K ≤ caps.PF ∧ caps.PF ≤ K * Ex c R * jointU X) ∧
    (jointT X R / K ≤ caps.yF ∧ caps.yF ≤ K * Ex c R * jointT X R) ∧
    (jointU X ^ 2 / K ≤ caps.JF ∧ caps.JF ≤ K * Ex c R * jointU X ^ 2) ∧
    caps.AS ≤ K * Ex c R * R ^ slowExpHA.eA ∧ caps.BS ≤ K * Ex c R * R ^ slowExpHA.eB ∧
    caps.JS ≤ K * Ex c R * R ^ slowExpHA.eJ ∧ caps.WS ≤ K * Ex c R * R ^ slowExpHA.eW ∧
    caps.ES ≤ K * Ex c R * R ∧ caps.AH ≤ K * Ex c R * R ∧ caps.BH ≤ K * Ex c R * R ^ 2

/-- **R1 at the joint scale**, in place of `DegreeBelow`: the threshold `q(X, R, caps)` is
`≤ C Q Ex(C₀, R)` on all scaled caps, for every scaling constant.  This is the duty of the whole
role table of survey §1.2, block J6.  The monomials are those of report `t12_joint_documents.md` §3,
which reproduce every inverse power of the TeX.  The rows 2, 3 of Table quant-metric are the Lean
monomials `rowM2`, `rowM3`, with no fitted term, and `highAnc_below`, `rootFloor_below`
(`Joint/Arith.lean`) prove this bound for them and for the raised floor. -/
def JointBelow (q : ℝ → ℝ → Caps → ℝ) : Prop :=
  ∀ K c : ℝ, 1 ≤ K → 0 ≤ c → ∃ C C₀ R₀ : ℝ, ∀ X R : ℝ, JDom R₀ X R → ∀ caps : Caps,
    CapsScaledJ K c X R caps → q X R caps ≤ C * jointQ X R * Ex C₀ R

/-- The leading near coefficient `L(X, R, caps)` is `≤ C Q^a Ex(c', R)` on all scaled caps
(`a = 1/2` for the native moment, `a = 1/3` for the proper one). -/
def LeadBelow (a : ℝ) (L : ℝ → ℝ → Caps → ℝ) : Prop :=
  ∀ K c : ℝ, 1 ≤ K → 0 ≤ c → ∃ C c' R₀ : ℝ, ∀ X R : ℝ, JDom R₀ X R → ∀ caps : Caps,
    CapsScaledJ K c X R caps → 0 ≤ L X R caps ∧ L X R caps ≤ C * jointQ X R ^ a * Ex c' R

/-! ### The two tied high-ancestor rows and the raised root floor -/

/-- `D = R²`: the timed horizontal cutoff of the joint proof (TeX; Body 47).  The static metric has
its own `D = R`. -/
def jointD (R : ℝ) : ℝ := R ^ 2

/-- `λ_*`, at the virtual coefficient `B_* = T/P_F`. -/
def jointLam (X R : ℝ) (caps : Caps) : ℝ := lamStar 1 caps.PF (jointBs X R caps)

/-- **Row 2 of Table quant-metric** as an inverse price: the clip cost is `q⁻¹ rowM2`, namely
`m2 = q⁻¹ D⁻¹ b³/λ_*`.  It is `∫_clip q⁻¹ W_> b²` with `W_> ≲ D⁻¹ b` (the inverse-fourth tail of the
slow lattice).  Owner: LOCAL440 step 1 and LOCAL441 (paths at `H2EnergyInterfaceB`). -/
def rowM2 (D lam b : ℝ) : ℝ := b ^ 3 / (D * lam)

/-- **Row 3 of Table quant-metric** as an inverse price, with its `δ₀` companion: the clip cost is
`q⁻¹ rowM3`, namely `m3 = q⁻¹ (W + M_∞) b [D⁻¹ √(P_S/λ_*) + δ₀/λ_*]`.  It is the integral on the
clip of `q⁻¹ (W + M_∞) b b_>`, with `b_> ≤ D⁻¹ c_y + δ₀` and `∫_clip c_y ≤ √(P_S/λ_*)`.  The Table
drops the `δ₀` term, which has inverse `U R^{5/2}`.  The survey's fitted `a b` occurs in no source
(report §3). -/
def rowM3 (D lam PS W Minf b : ℝ) : ℝ :=
  (W + Minf) * b * (Real.sqrt (PS / lam) / D + delta0 / lam)

/-- The two high-ancestor inverse prices at the caps, with `M_∞ = C ex R` and `P_S` the clip price
of `SlowOut` at `ℓ = 1/λ_*`.  Caps enter through `cp`, as in `kinThreshold`. -/
def highAnc (C ex X R : ℝ) (caps : Caps) : ℝ :=
  rowM2 (jointD R) (jointLam X R caps) (cp caps.BS) +
    rowM3 (jointD R) (jointLam X R caps) (slowPrice C ex R (1 / jointLam X R caps)) (cp caps.WS)
      (C * ex * R) (cp caps.BS)

/-- The total `H²` cap `Y = 2(1 + μ + y + B_S)` of the raised floor (TeX), at `μ = X`. -/
def totalY (X : ℝ) (caps : Caps) : ℝ := 2 * (1 + X + cp caps.yF + cp caps.BS)

/-- The six linear and force monomials of the raised floor `Q₀'`, as a sum:
`2, 4φ, 2¹²Y, 2⁹φ, 2⁵ C_A Y φ, 2²⁰ y²` (Bodies 29, 56, 84), with `C_A ↦ c₄` as in `role27`.
**[design]** the last one has the extra factor `1 + c₄`, because the Lean trace bound is
`‖R_S‖₂ ≤ 8 c₄ b_F²/q` (`hnorm_slowCorr_le`), where the TeX has `20 y²/q`; `c₄` is a `tsum` with no
numerical bound in Lean. -/
def rootFloor (X φ : ℝ) (caps : Caps) : ℝ :=
  2 + 4 * φ + 2 ^ 12 * totalY X caps + 2 ^ 9 * φ + 2 ^ 5 * c4 * totalY X caps * φ +
    2 ^ 20 * (1 + c4) * cp caps.yF ^ 2

/-- **The raised floor `Q₀'`** `= max(2, 4φ, 2¹²Y, 2⁹φ, 2⁵C_A Yφ, 2²⁰y², 16 K_N)` of Bodies 29, 56,
84, with `K_N ≤ q₀`.  E4-J does not need the monomials of `rootFloor`: `kinJThreshold` has none of
them (report `t12_joint_kinetic.md`, doubt 1), so `below₀` does not pay them.  But rows 7, 20, 33
and the trace of `R_S` use them: Body 84 substitutes `64 Q₀'` in rows 7, 20, in both independent row
33 roots and in row 36, and row 25 is `2²⁰ y²`.  They therefore belong to the slow threshold, see
`JointData.qSFull`.  Sizes: `≤ R³` up to the subpower (`rootFloor_below`), so no risk to `Q`. -/
def Q0Prime (X φ q₀ : ℝ) (caps : Caps) : ℝ := max (rootFloor X φ caps) (16 * q₀)

/-! ### The whole package -/

/-- The parameters of the joint interfaces.  They are all chosen before the solution, and may
depend on the resonant constants (`quantitative_joint_of_interfaces`). -/
structure JointData where
  /-- The start of the domain of the interfaces. -/
  R₀ : ℝ
  /-- The piece length: bounded, see `SlowCapsJoint`. -/
  Tp : ℝ → ℝ → ℝ
  /-- The kinetic threshold (E4-J; the raised floor of row 36.  The other monomials of roles 22–27
  are in `Q0Prime`). -/
  q₀ : ℝ → ℝ → Caps → ℝ
  /-- The `H¹` threshold (E5-J; roles 8–15, 28–30). -/
  q₁ : ℝ → ℝ → Caps → ℝ
  /-- The `H²` threshold (E8-J; roles 16, 17, 28, 31, 32), apart from the rows 2, 3 of Table
  quant-metric: see `JointData.q₂Full`. -/
  q₂ : ℝ → ℝ → Caps → ℝ
  /-- The slow threshold (E7-P; roles 5–7, 18–21, 33–35), apart from the raised floor: see
  `JointData.qSFull`. -/
  qS : ℝ → ℝ → Caps → ℝ
  /-- The `L²` source tolerance `N̄`. -/
  Nbar : ℝ → ℝ → ℝ
  /-- The tested force tolerance `π`. -/
  piTol : ℝ → ℝ → ℝ
  /-- The leading coefficient of the native moment. -/
  LN : ℝ → ℝ → Caps → ℝ
  /-- The leading coefficient of the proper moment. -/
  LP : ℝ → ℝ → Caps → ℝ
  /-- The native near moment. -/
  N : ℝ → ℝ
  /-- The proper near moment. -/
  P : ℝ → ℝ
  /-- The remaining slow outputs fed forward, the slot `rest` of `SlowOut`. -/
  Sl : ℝ → ℝ → ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop
  /-- The (enlarged) resonant constant of the `H¹` energy. -/
  Cs : ℝ
  /-- The (enlarged) resonant constant of the `H²` energy. -/
  CG : ℝ
  /-- The clip multiplier mass. -/
  m₀ : ℝ
  /-- The kernel constant of the rows 2, 3 of Table quant-metric, budget `2⁻³⁵` included. -/
  Cm : ℝ
  /-- The constants of the slow start levels, see `levelsJ`. -/
  L : Fin 5 → ℝ
  /-- The constant of the slow caps. -/
  CS : ℝ
  /-- The subpower exponent of the slow caps. -/
  cS : ℝ

/-- The sup bound `M_∞ ≤ C_S Ex(c_S, R) R` of E7-P. -/
def JointData.Minf (D : JointData) (R : ℝ) : ℝ := D.CS * Ex D.cS R * R

/-- The near payment of the package at `(X, R)`. -/
def JointData.near (D : JointData) (X R : ℝ) : Caps → ℝ → Prop :=
  NearPaid (D.LN X R) (D.LP X R) D.N D.P

/-- The raised floor is visible in the slow threshold: `2²⁰ (1 + c₄) y² ≤ qSFull`, which pays the
`R_S` trace (`slowCorr_le`). -/
theorem le_qS_of_floor {qS q₀ X φ : ℝ} (hX : 0 ≤ X) (hφ : 0 ≤ φ) (caps : Caps) :
    2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 ≤ max qS (64 * Q0Prime X φ q₀ caps) := by
  have hc := c4_pos
  have hy := cp_nonneg caps.yF
  have hB := cp_nonneg caps.BS
  have hY : 0 ≤ totalY X caps := by unfold totalY; positivity
  have h1 : 2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 ≤ rootFloor X φ caps := by
    have h2 : 0 ≤ 2 ^ 5 * c4 * totalY X caps * φ := by positivity
    have h3 : 0 ≤ 2 ^ 12 * totalY X caps := by positivity
    unfold rootFloor
    linarith
  have h4 : rootFloor X φ caps ≤ Q0Prime X φ q₀ caps := le_max_left _ _
  have h5 : 0 ≤ 2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 := by positivity
  exact le_max_of_le_right (by linarith)

/-- The slow outputs of the package at `(X, R)`, as seen by E5-J and E8-J. -/
def JointData.slowOut (D : JointData) (X R : ℝ) : ℝ → Field → (ℝ → Field) → ℝ → ℝ → Prop :=
  SlowOut D.CS (Ex D.cS R) R (D.Sl X R)

/-- **The slot `trace` of `SlowOut` is discharged by the threshold**: on a piece where `qSFull` is
paid, `‖R_S‖₂ ≤ δ₀` at every time, by `slowCorr_le`. -/
theorem JointData.slowOut_trace (D : JointData) {X R Tp r : ℝ} {g : Field} {y : ℝ → Field}
    {Ty : ℝ≥0∞} {caps : Caps} {s t : ℝ} (hsol : ActualSol X (R - X) r g y Ty) (hX : 0 ≤ X)
    (hXR : X ≤ R) (hp : PieceHyp Tp (fun caps ↦ max (D.qS X R caps)
      (64 * Q0Prime X (R - X) (D.q₀ X R caps) caps)) r g y Ty caps s t) :
    ∀ u ∈ Icc s t, hnorm 2 (slowCorr r g y u) ≤ delta0 := by
  have hφ : 0 ≤ R - X := by linarith
  have hq := hp.thr
  have hc := c4_pos
  have hy := cp_nonneg caps.yF
  have hB := cp_nonneg caps.BS
  have hY : 0 ≤ totalY X caps := by unfold totalY; positivity
  have h2 : 2 ≤ rootFloor X (R - X) caps := by
    have h3 : 0 ≤ 2 ^ 5 * c4 * totalY X caps * (R - X) := by positivity
    have h4 : 0 ≤ 2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 := by positivity
    unfold rootFloor
    nlinarith only [h3, h4, hY, hφ]
  have h5 : 2 ≤ Q0Prime X (R - X) (D.q₀ X R caps) caps := h2.trans (le_max_left _ _)
  have h6 : (64 : ℝ) * 2 ≤ |r| := by
    refine le_trans ?_ hq
    exact le_max_of_le_right (by linarith)
  have hr : r ≠ 0 := fun h0 ↦ by
    rw [h0, abs_zero] at h6
    norm_num at h6
  intro u hu
  exact slowCorr_le hsol hr (hp.hs.trans hu.1) (lt_lifespan hu.2 hp.ht)
    ((hp.onPrefix.1 u hu).2.1.trans (le_cp _)) ((le_qS_of_floor hX hφ caps).trans hq)

/-- **The `H²` threshold**: the other roles and the two tied high-ancestor rows, whose payment is a
theorem (`JointInterfaces.below₂Full`). -/
def JointData.q₂Full (D : JointData) (X R : ℝ) (caps : Caps) : ℝ :=
  max (D.q₂ X R caps) (D.Cm * highAnc D.CS (Ex D.cS R) X R caps)

/-- **The slow threshold**: the other roles and the raised domain `64 Q₀'`, which rows 7, 20, 33 and
the `R_S` trace use (`Q0Prime`).  It reads `q₀`, which reads `C_S, c_S`; there is no circularity,
since the constants of E7-P are chosen first and `q₀` only enters as a hypothesis of E7-P.  Its
payment is a theorem from `below₀`, `belowS` (`JointInterfaces.belowSFull`). -/
def JointData.qSFull (D : JointData) (X R : ℝ) (caps : Caps) : ℝ :=
  max (D.qS X R caps) (64 * Q0Prime X (R - X) (D.q₀ X R caps) caps)

/-- **All the joint interfaces.**  The conditional joint theorem has exactly these hypotheses
(`quantitative_joint_of_interfaces`).  The constants are absolute: nothing below depends on `φ`
except through `R`. -/
structure JointInterfaces (D : JointData) : Prop where
  /-- `C_s ≥ 0`. -/
  Cs_nonneg : 0 ≤ D.Cs
  /-- `C_G ≥ 0`. -/
  CG_nonneg : 0 ≤ D.CG
  /-- The clip mass (the post-clip level must survive the next first clip). -/
  m₀_mem : 0 ≤ D.m₀ ∧ D.m₀ ≤ 1 / 4
  /-- The level constants are `≥ 1`. -/
  L_ge : ∀ i, 1 ≤ D.L i
  /-- `C_S ≥ 1`. -/
  CS_ge : 1 ≤ D.CS
  /-- `c_S ≥ 0`. -/
  cS_nonneg : 0 ≤ D.cS
  /-- `C_m ≥ 0`. -/
  Cm_nonneg : 0 ≤ D.Cm
  /-- Pieces have length at least three: the last unit of a piece and the unit before it must lie
  past the first unit, for the backward history (see `SlowCapsJoint`). -/
  Tp_ge : ∀ X R : ℝ, JDom D.R₀ X R → 3 ≤ D.Tp X R
  /-- The piece length is at most a subpower of `R` (bounded in fact, see `SlowCapsJoint`: then
  `cT = 0`). -/
  Tp_le : ∃ CT cT : ℝ, 0 ≤ cT ∧ ∀ X R : ℝ, JDom D.R₀ X R → D.Tp X R ≤ CT * Ex cT R
  /-- **E4-J**, see `KineticJoint`. -/
  kinetic : ∀ X R : ℝ, JDom D.R₀ X R → KineticJoint X (R - X) (D.Minf R) (D.q₀ X R)
  /-- **E5-J**, see `H1EnergyJoint`. -/
  h1 : ∀ X R : ℝ, JDom D.R₀ X R →
    H1EnergyJoint ((281 : ℝ) / 1000) D.Cs X (R - X) (D.Tp X R) (D.Nbar X R) (D.piTol X R)
      (D.Minf R) (D.q₁ X R) (D.near X R) (D.slowOut X R)
  /-- **E8-J**, see `H2EnergyInterfaceB`, at the virtual coefficient `B_* = T/P_F`. -/
  h2 : ∀ X R : ℝ, JDom D.R₀ X R →
    H2EnergyInterfaceB ((281 : ℝ) / 1000) D.CG X (R - X) (D.Tp X R) D.m₀ (D.Minf R)
      (jointBs X R) (D.q₂Full X R) (D.near X R) (D.slowOut X R)
  /-- **E7-P**, see `SlowCapsJoint`. -/
  slow : SlowCapsJoint D.R₀ D.Tp D.qSFull D.L D.CS D.cS D.Sl
  /-- **E9-J**, see `JointProfiles`. -/
  profiles : JointProfiles D.N D.P
  /-- The kinetic floor (TeX: `≲ R³` polylog; tied at `U ≍ 1`). -/
  below₀ : JointBelow D.q₀
  /-- The `H¹` roles, see `JointBelow`. -/
  below₁ : JointBelow D.q₁
  /-- The `H²` roles but the rows 2, 3 of Table quant-metric, including the comparable row, tied at
  `Q`. -/
  below₂ : JointBelow D.q₂
  /-- The slow roles but the raised floor (`B_S y² = R²T²`, tied at `Q`; `q ≥ Y φ`, tied at
  `U ≍ 1`). -/
  belowS : JointBelow D.qS
  /-- The native leading coefficient: `(M_∞ y)² ≲ Q`, the tie that produces `Ex` (survey §1.3). -/
  leadN : LeadBelow (1 / 2) D.LN
  /-- The proper leading coefficient (the `H¹` quartic, `U^{3/4} R³ ≤ Q`). -/
  leadP : LeadBelow (1 / 3) D.LP
  /-- `N̄ ≥ 0`. -/
  Nbar_nonneg : ∀ X R : ℝ, JDom D.R₀ X R → 0 ≤ D.Nbar X R
  /-- `π ≥ 0`. -/
  piTol_nonneg : ∀ X R : ℝ, JDom D.R₀ X R → 0 ≤ D.piTol X R
  /-- `N̄ ≲ X`, uniformly in `φ` (TeX Lemma quant-scalar). -/
  Nbar_le : ∃ C : ℝ, ∀ X R : ℝ, JDom D.R₀ X R → D.Nbar X R ≤ C * X
  /-- `π ≲ X`, uniformly in `φ` (TeX Lemma quant-scalar). -/
  piTol_le : ∃ C : ℝ, ∀ X R : ℝ, JDom D.R₀ X R → D.piTol X R ≤ C * X

end OVNS.Quant

end
