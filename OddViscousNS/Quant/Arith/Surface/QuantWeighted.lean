import OddViscousNS.Quant.Arith.Surface.ShellBound
import OddViscousNS.Quant.Arith.Weighted.Main

/-!
# `quant_weighted'`: Lemma quant-weighted with no hypotheses

`quant_weighted` of `Weighted/Main.lean` applied to its three proved inputs: `planeCurveCount`,
`shell_surface_bound'` and `quadraticNormCount`.
-/

namespace OVNS.Quant

/-- **Lemma quant-weighted, with no hypotheses.** -/
theorem quant_weighted' : QuantWeighted :=
  quant_weighted PlaneCount.planeCurveCount shell_surface_bound' quadraticNormCount

/-- The weighted count of the resonant layer, with no hypotheses. -/
theorem weightedCount' : WeightedCount := weightedCount_of_quantWeighted quant_weighted'

end OVNS.Quant
