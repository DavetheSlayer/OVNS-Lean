import OddViscousNS.Quant.Defs
import OddViscousNS.Quant.Regimes.Assembly
import OddViscousNS.Quant.Joint.Assembly.Package
import OddViscousNS.Quant.Joint.Metric.Close
import OddViscousNS.Closed.Conclusion

/-!
# Theorem 1.2 (general quantitative consequences)

Both bounds are stated with no hypotheses, and both are proved.  `μ = M/ν`, `φ = F/ν²`, `q = |α|/ν`.
The conclusion is `GlobalConclusion'` (with the explicit `u t ∈ H^s` persistence clause), as in
Theorems 1.1 and 1.3.  The fixed-force bound is `quantitative_fixed_force_proved`
(`Quant/Regimes/Assembly.lean`).  The joint bound is `quantitative_joint_of_energies`
(`Quant/Joint/Assembly/Package.lean`) applied to `energies_close` (`Quant/Joint/Metric/Close.lean`).
The two published counting theorems the manuscript cites are not hypotheses: `PlaneCurveCount` is
proved (`Quant/Arith/Plane/PlaneCount.lean`) and the use of the surface covering is replaced by a
specialized determinant argument (`Quant/Arith/Surface/`).
-/

namespace OVNS

/-- Theorem 1.2, fixed-force bound: for each `φ ≥ 0` and `ε > 0` there is `C` such that
`q ≥ C (1+μ)^{9876/719+ε}` suffices for the global strong conclusion of Theorem 1.1 on the
force ball `φ`. -/
theorem quantitative_fixed_force :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ C : ℝ, ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F → F / ν ^ 2 ≤ φ →
        C * (1 + M / ν) ^ ((9876 : ℝ) / 719 + ε) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  exact Quant.quantitative_fixed_force_proved

/-- Theorem 1.2, joint large-force bound: with `X = e^e + μ`, `R = X + φ`, `U = X^{1719/719}`,
there are absolute `C, C₀, R₀ > 0` such that on `R ≥ max(R₀, X²⁴)`,
`q ≥ C U R³ exp(C₀ log R / log log R)` suffices for the same conclusion. -/
theorem quantitative_joint_force :
    ∃ C C₀ R₀ : ℝ, 0 < C ∧ 0 < C₀ ∧ 0 < R₀ ∧ ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F →
        let X := Real.exp (Real.exp 1) + M / ν
        let R := X + F / ν ^ 2
        let U := X ^ ((1719 : ℝ) / 719)
        max R₀ (X ^ (24 : ℝ)) ≤ R →
        C * U * R ^ 3 * Real.exp (C₀ * Real.log R / Real.log (Real.log R)) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  exact Quant.quantitative_joint_of_energies Quant.Metric.energies_close

/-- Theorem 1.2, joint bound, with the side condition removed.  `quantitative_joint_force` asks
`R ≥ max(R₀, X²⁴)`.  That condition restricts the radii, not the data: a smaller force also lies in
a larger ball.  So every pair of radii has a threshold, with `R` replaced by `max(R, R₀, X²⁴)`.  On
the manuscript's domain the two thresholds are the same. -/
theorem quantitative_joint_force_all_radii :
    ∃ C C₀ R₀ : ℝ, 0 < C ∧ 0 < C₀ ∧ 0 < R₀ ∧ ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F →
        let X := Real.exp (Real.exp 1) + M / ν
        let R := max (X + F / ν ^ 2) (max R₀ (X ^ (24 : ℝ)))
        let U := X ^ ((1719 : ℝ) / 719)
        C * U * R ^ 3 * Real.exp (C₀ * Real.log R / Real.log (Real.log R)) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  obtain ⟨C, C₀, R₀, hC, hC₀, hR₀, Bd, h⟩ := quantitative_joint_force
  refine ⟨C, C₀, R₀, hC, hC₀, hR₀, fun μ φ ↦
    Bd μ (max (Real.exp (Real.exp 1) + μ + φ)
      (max R₀ ((Real.exp (Real.exp 1) + μ) ^ (24 : ℝ))) - (Real.exp (Real.exp 1) + μ)),
    fun ν M F α u₀ f hν hM hF hu₀ hf hu₀M hfF ↦ ?_⟩
  intro X R U hα
  have hν2 : 0 < ν ^ 2 := by positivity
  have hRX : X + F / ν ^ 2 ≤ R := le_max_left _ _
  have hdom : max R₀ (X ^ (24 : ℝ)) ≤ R := le_max_right _ _
  have hF' : F ≤ ν ^ 2 * (R - X) := by
    have : F / ν ^ 2 ≤ R - X := by linarith
    rw [div_le_iff₀ hν2] at this
    linarith [mul_comm (R - X) (ν ^ 2)]
  have hF'0 : 0 ≤ ν ^ 2 * (R - X) := hF.trans hF'
  have hratio : ν ^ 2 * (R - X) / ν ^ 2 = R - X := by field_simp
  have key := h ν M (ν ^ 2 * (R - X)) α u₀ f hν hM hF'0 hu₀ hf hu₀M (hfF.trans hF')
  simp only [hratio] at key
  simp only [show Real.exp (Real.exp 1) + M / ν + (R - X) = R by
    show X + (R - X) = R; ring] at key
  exact key hdom hα

end OVNS
