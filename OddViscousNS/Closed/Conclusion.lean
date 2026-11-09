import OddViscousNS.Closed.Defs

/-!
# The global strong conclusion with the explicit `u t ∈ H^s` clause

`GlobalConclusion'` strengthens `GlobalConclusion` (OddViscousNS/Closed/Defs.lean) in the zero-force
persistence clause by stating `u t ∈ H^s` for all `t ≥ 0` explicitly (as in Theorem 1.1's
statement): `ContH s u` alone is vacuous for non-`H^s` values.  This is the conclusion used by the
Theorem 1.3 anchors.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

/-- The global strong conclusion of Theorems 1.1–1.3 with the explicit persistence clause. -/
def GlobalConclusion' (ν α : ℝ) (f u₀ : Field) (Bd : ℝ) : Prop :=
  ∃ u : ℝ → Field, IsStrongSolution ν α f u₀ u ∧
    (∀ u', IsStrongSolution ν α f u₀ u' → ∀ t, 0 ≤ t → u' t = u t) ∧ L2locH 3 u ∧
    (∀ t, 0 ≤ t → hnorm 1 (u t) ≤ ν * Bd ∧ hnorm 2 (u t) ≤ ν * Bd) ∧
    (∀ t h : ℝ, 0 ≤ t → 0 ≤ h →
      ∫⁻ s in Icc t (t + h), hsE 3 (u s) ≤ ENNReal.ofReal (ν * ⌈ν * h⌉ * Bd)) ∧
    (f = 0 → (∀ s, 2 ≤ s → InH s u₀ → (∀ t, 0 ≤ t → InH s (u t)) ∧ ContH s u ∧
        L2locH (s + 1) u) ∧ SmoothAtPositiveTimes u)

theorem GlobalConclusion'.toGlobalConclusion {ν α : ℝ} {f u₀ : Field} {Bd : ℝ}
    (h : GlobalConclusion' ν α f u₀ Bd) : GlobalConclusion ν α f u₀ Bd := by
  obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨u, h1, h2, h3, h4, h5, fun hf => ⟨fun s hs hi => ((h6 hf).1 s hs hi).2, (h6 hf).2⟩⟩

end OVNS
