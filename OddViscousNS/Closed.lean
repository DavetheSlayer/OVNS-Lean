import OddViscousNS.Closed.Defs
import OddViscousNS.Closed.Unforced
import OddViscousNS.Closed.Forced.Assembly
import OddViscousNS.Closed.GTable
import OddViscousNS.Closed.Conclusion
import OddViscousNS.Closed.Row.Main

/-!
# Theorem 1.3 (closed zero-threshold regions) — statement

For every fixed real `α`, including `0` and both signs, the original equation has a unique global
strong solution with uniform `H¹, H²` bounds and every-time sliding `H³` square-integral bounds,
(i) unforced, on `0 ≤ μ = M/ν ≤ 97/40`, where the scaled solution `w = u(τ/ν)/(ν·97/40)` satisfies
`Y ≤ 1` and `∫₀^∞ Z ≤ 100000`; (ii) forced, on each of the seven closed rectangles
`208013 μ ≤ μ_max, 208013 φ ≤ φ_max`, where with `s = μ_max/208013` the scaled solution satisfies
`∫_I Z ≤ J` on every normalized interval `|I| ≤ 1`.  For zero force every initial `H^s`, `s ≥ 2`,
persists and the solution is smooth at positive times.  All endpoint equalities are included.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

/-- Theorem 1.3, unforced branch (`φ = 0`, `0 ≤ μ ≤ 97/40`). The bound `Bd` is uniform in `α`.
The UF661 Gram row bound `λ_max(G_k) ≤ M₀ = .185955292` for every output `k` is the
kernel-checked `rowBound_M₀`. -/
theorem closed_regions_unforced : ∃ Bd : ℝ, 0 ≤ Bd ∧
    ∀ (ν α M : ℝ) (u₀ : Field), 0 < ν → 0 ≤ M → Adm 2 u₀ → hnorm 2 u₀ ≤ M → M / ν ≤ 97 / 40 →
      GlobalConclusion' ν α 0 u₀ Bd ∧
      ∀ u : ℝ → Field, IsStrongSolution ν α 0 u₀ u →
        (∀ τ, 0 ≤ τ → Ymet (scaled ν (97 / 40) u τ) ≤ 1) ∧
        ∫⁻ τ in Ici 0, Zmet (scaled ν (97 / 40) u τ) ≤ 100000 :=
  closed_regions_unforced_aux rowBound_M₀

/-- Theorem 1.3, forced branch: each row `(208013 μ_max, 208013 φ_max, J)` of `forcedRows` is an
independent closed rectangle; `s = μ_max` and `w = u(τ/ν)/(ν s)`. The bound `Bd` is uniform in
`α` and in the row.  The UF661 per-output Gram prices `g_C` are the kernel-checked
`rowBound_gOVNS`.  Proved through `Forced.closed_regions_forced_of_rows`:
the six off-axis rows by the kernel-checked F662 face certificates, the common row by a re-planned
graph (`Forced/Common`) using only kinetic, whole-`κ₀` and moment-regime faces, with the
moment-regime cubic bounds (`Forced/Moment`) kernel-checked from exact pair tables. -/
theorem closed_regions_forced : ∃ Bd : ℝ, 0 ≤ Bd ∧
    ∀ r ∈ forcedRows, ∀ (ν α M F : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F →
      Adm 2 u₀ → Adm 2 f → hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F →
      208013 * (M / ν) ≤ r.1 → 208013 * (F / ν ^ 2) ≤ r.2.1 →
      GlobalConclusion' ν α f u₀ Bd ∧
      ∀ u : ℝ → Field, IsStrongSolution ν α f u₀ u →
        ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ a + 1 →
          ∫⁻ τ in Icc a b, Zmet (scaled ν ((r.1 : ℝ) / 208013) u τ) ≤ r.2.2 := by
  exact Forced.closed_regions_forced_of_rows rowBound_gOVNS

end OVNS
