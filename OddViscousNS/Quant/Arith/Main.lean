import OddViscousNS.Quant.Arith.Weighted.Main
import OddViscousNS.Quant.Arith.Surface.QuantWeighted
import OddViscousNS.Quant.Arith.NormCount
import OddViscousNS.Quant.Arith.Algebra.FewPoints
import OddViscousNS.Quant.Arith.Resonant.Main

/-!
# The arithmetic layer of Theorem 1.2, assembled

Lemma quant-weighted holds with no hypotheses (`quant_weighted'`, `Quant/Arith/Surface/`): the
plane-curve count, the quadratic norm count and the few-points lemma are theorems, and the one use
of a surface covering is replaced by a specialized determinant argument for the explicit conic
bundle.  So `WeightedCount` and Proposition quant-resonant (`resonant_H1_of_counts`,
`resonant_H2_of_counts`) are unconditional.
-/

namespace OVNS.Quant

/-- Lemma quant-weighted, with no hypotheses. -/
theorem weightedCount_of_counts : WeightedCount := weightedCount'

/-- Proposition quant-resonant, `H¹` form, with no hypotheses. -/
theorem resonant_H1_of_counts :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ F : Field, Adm 2 F → PiF F = F →
      |pair 1 F (Qres F F)| ≤ Cs * hnorm 1 F ^ (3 - (281 : ℝ) / 1000) * hnorm 2 F ^ ((281 : ℝ) / 1000) :=
  resonant_H1 weightedCount_of_counts

/-- Proposition quant-resonant, `H²` form, with no hypotheses. -/
theorem resonant_H2_of_counts :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∀ F : Field, Adm 3 F → PiF F = F →
      |pair 2 F (Qres F F)| ≤ CH * hnorm ((281 : ℝ) / 1000) F * hnorm 2 F * hnorm 3 F :=
  resonant_H2 weightedCount_of_counts

end OVNS.Quant
