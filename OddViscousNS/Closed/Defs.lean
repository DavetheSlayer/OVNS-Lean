import OddViscousNS.Basic

/-!
# Theorem 1.3 — statement-level definitions

The weighted metric `h`, the normalized energies `X, Y, Z` of the scaled field `w`, the
normalization `w(τ) = u(τ/ν)/(ν s)`, and the seven forced rectangles.  Everything here is part of
the *statement* of Theorem 1.3 (`closed_regions_unforced`, `closed_regions_forced`); the proof
machinery lives in `OddViscousNS/Closed/*`.
-/

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace OVNS

/-- `1000·h(j)` for `1 ≤ j ≤ 32`. -/
def hmetTable : List ℕ :=
  [1000, 1569, 2042, 2462, 2847, 3205, 3543, 3864, 4171, 4467, 4752, 5029, 5297, 5559, 5814, 6063,
   6307, 6545, 6779, 7009, 7235, 7457, 7676, 7891, 8103, 8313, 8519, 8723, 8924, 9123, 9319, 9514]

/-- The metric `h(j)`: the table for `1 ≤ j ≤ 32`, and `29j/100 + 117/500` for `j ≥ 33`
(`h(0) = 0` is a convention; the zero mode never enters). -/
def hmet (j : ℕ) : ℝ :=
  if j = 0 then 0 else if j ≤ 32 then (hmetTable.getD (j - 1) 0 : ℝ) / 1000
  else 29 * (j : ℝ) / 100 + 117 / 500

/-- `|k|²` as a natural number. -/
def nsq (k : Mode) : ℕ := ∑ i, (k i).natAbs ^ 2

/-- `X = ‖w‖₀² ∈ [0,∞]`. -/
def Xmet (w : Field) : ℝ≥0∞ := ∑' k, ENNReal.ofReal (if k = 0 then 0 else ‖w k‖ ^ 2)

/-- `Y = ⟨h(A)w, w⟩ ∈ [0,∞]`. -/
def Ymet (w : Field) : ℝ≥0∞ := ∑' k, ENNReal.ofReal (hmet (nsq k) * ‖w k‖ ^ 2)

/-- `Z = ⟨A h(A)w, w⟩ ∈ [0,∞]`. -/
def Zmet (w : Field) : ℝ≥0∞ := ∑' k, ENNReal.ofReal ((nsq k : ℝ) * hmet (nsq k) * ‖w k‖ ^ 2)

/-- The scaled field `w(τ) = v(τ)/s = u(τ/ν)/(ν s)` in normalized time `τ = ν t`. -/
def scaled (ν s : ℝ) (u : ℝ → Field) (τ : ℝ) : Field :=
  fun k => ((1 / (ν * s) : ℝ) : ℂ) • u (τ / ν) k

/-- The seven forced rectangles `(208013·μ_max, 208013·φ_max, J)` of Theorem 1.3. -/
def forcedRows : List (ℕ × ℕ × ℕ) :=
  [(419650, 419650, 850), (425500, 382950, 294), (434000, 347200, 468), (442000, 309400, 320),
   (458500, 229250, 808), (478500, 119625, 355), (489500, 48950, 124)]

/-- The global strong conclusion shared by Theorems 1.1–1.3: a unique global strong solution in
`C H² ∩ L²_loc H³`, uniform `H¹, H²` bounds `ν·Bd`, every-time sliding `H³` square-integral bounds
with the physical window factor `ν⌈νh⌉`, and for zero force the persistence of every `H^s`,
`s ≥ 2`, together with smoothness at positive times. -/
def GlobalConclusion (ν α : ℝ) (f u₀ : Field) (Bd : ℝ) : Prop :=
  ∃ u : ℝ → Field, IsStrongSolution ν α f u₀ u ∧
    (∀ u', IsStrongSolution ν α f u₀ u' → ∀ t, 0 ≤ t → u' t = u t) ∧ L2locH 3 u ∧
    (∀ t, 0 ≤ t → hnorm 1 (u t) ≤ ν * Bd ∧ hnorm 2 (u t) ≤ ν * Bd) ∧
    (∀ t h : ℝ, 0 ≤ t → 0 ≤ h →
      ∫⁻ s in Icc t (t + h), hsE 3 (u s) ≤ ENNReal.ofReal (ν * ⌈ν * h⌉ * Bd)) ∧
    (f = 0 → (∀ s, 2 ≤ s → InH s u₀ → ContH s u ∧ L2locH (s + 1) u) ∧ SmoothAtPositiveTimes u)

end OVNS
