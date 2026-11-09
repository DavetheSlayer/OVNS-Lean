import OddViscousNS.Quant.Regimes.FixedForce
import OddViscousNS.Quant.Arith.Main
import OddViscousNS.Quant.Energy.Near.Profiles
import OddViscousNS.Quant.Energy.Kinetic.Main
import OddViscousNS.Quant.Energy.Slow.Main
import OddViscousNS.Quant.Energy.H1.Main
import OddViscousNS.Quant.Energy.H2.Main

/-!
# Theorem 1.2, fixed force: assembly with the arithmetic layer and the near profiles discharged

`quantitative_fixed_force_of_energy` is the conclusion of `quantitative_fixed_force`
(`OddViscousNS/Quant.lean`), verbatim, from the remaining analytic energy interfaces.  The interfaces E5/E8 use `ResH1`/`ResH2` as black boxes, so they
are assumed for every valid resonant constant.

| layer | status here |
|---|---|
| arithmetic `ResH1`, `ResH2` at `281/1000` | discharged (`resonant_H1/H2_of_counts`) |
| E9 near profile `N(q) ≤ C q^{−1/2+δ}` | discharged: `nearProfilesEl`, concrete `nearN` |
| E4 `KineticInterface` | hypothesis `hK` |
| E5 `H1EnergyInterface` (every valid `Cs ≥ 0`) | hypothesis `hE1` |
| E7 `SlowCapsInterface` | hypothesis `hS7` |
| E8 `H2EnergyInterface` (every valid `CH ≥ 1`) | hypothesis `hE2` |
| R1 bookkeeping | `hq₀ hq₁ hq₂ hqS` (`DegreeBelow`), `hNbar hpi hNbar0 hpi0` |
| regimes layer (R1, R3, E6, E10) | proved (`quantitative_fixed_force_of_interfaces`) |

The arithmetic layer rests on no hypothesis: `PlaneCurveCount` is proved and the surface covering is
avoided.  Every interface is discharged below, so `quantitative_fixed_force_proved` has none.
-/

namespace OVNS.Quant

/-- `ResH2 θ` is monotone in the constant (the right-hand side is a product of norms). -/
theorem ResH2.mono {θ CH CH' : ℝ} (h : ResH2 θ CH) (hle : CH ≤ CH') : ResH2 θ CH' :=
  fun F hF hP ↦ (h F hF hP).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hle (hnorm_nonneg _ _)) (hnorm_nonneg _ _)) (hnorm_nonneg _ _))

/-- The elementary-route profiles give the native profile clause. -/
theorem nativeProfile_nearN : NativeProfile nearN :=
  fun δ hδ ↦ (nearProfilesEl δ hδ).imp fun _ hC q hq ↦ (hC q hq).1

/-- **Theorem 1.2, fixed force, from the energy interfaces**: the conclusion of
`quantitative_fixed_force` under the two published counting inputs, the energy interfaces
E4, E5, E7, E8 (E5/E8 for every valid resonant constant), the R1 degree bookkeeping and the
nonnegative `O(μ)` tolerances; E9 (`nearN`) and the arithmetic layer are discharged. -/
theorem quantitative_fixed_force_of_energy
    {K₁ K₂ m₀ Tp : ℝ} {e : SlowExp} {q₀ q₁ q₂ qS : ℝ → ℝ → Caps → ℝ}
    {Nbar piTol : ℝ → ℝ → ℝ} (hTp : 2 ≤ Tp) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4) (he : 1 ≤ e.eA ∧ 1 ≤ e.eB ∧ 1 ≤ e.eW)
    (hK : ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ → KineticInterface μ φ (q₀ μ φ))
    (hE1 : ∀ Cs : ℝ, 0 ≤ Cs → ResH1 ((281 : ℝ) / 1000) Cs → ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H1EnergyInterface ((281 : ℝ) / 1000) Cs μ φ Tp (Nbar μ φ) (piTol μ φ) K₁ (q₁ μ φ) nearN)
    (hE2 : ∀ CH : ℝ, 1 ≤ CH → ResH2 ((281 : ℝ) / 1000) CH → ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H2EnergyInterface ((281 : ℝ) / 1000) CH μ φ Tp K₂ m₀ (q₂ μ φ) nearN)
    (hS7 : SlowCapsInterface Tp e qS)
    (hq₀ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e q₀)
    (hq₁ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e q₁)
    (hq₂ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e q₂)
    (hqS : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e qS)
    (hNbar : AtMostLinear Nbar) (hpi : AtMostLinear piTol)
    (hNbar0 : ∀ μ φ : ℝ, 0 ≤ Nbar μ φ) (hpi0 : ∀ μ φ : ℝ, 0 ≤ piTol μ φ) :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ C : ℝ, ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F → F / ν ^ 2 ≤ φ →
        C * (1 + M / ν) ^ ((9876 : ℝ) / 719 + ε) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  obtain ⟨Cs, hCs, h1⟩ := resonant_H1_of_counts
  obtain ⟨CH, -, h2⟩ := resonant_H2_of_counts
  have h2' : ResH2 ((281 : ℝ) / 1000) (max CH 1) := ResH2.mono h2 (le_max_left _ _)
  have hCH1 : (1 : ℝ) ≤ max CH 1 := le_max_right _ _
  have hCH : 0 < max CH 1 := lt_of_lt_of_le one_pos hCH1
  exact quantitative_fixed_force_of_interfaces hTp hK₁ hK₂ hm₀ hCs hCH he h1 h2' hK
    (hE1 Cs hCs h1) (hE2 _ hCH1 h2') hS7 nativeProfile_nearN hq₀ hq₁ hq₂ hqS hNbar hpi hNbar0
    hpi0


/-- **Theorem 1.2, fixed force, with the kinetic interface discharged.**  Same as
`quantitative_fixed_force_of_energy`, but E4 is supplied by `kineticInterface`
(`Quant/Energy/Kinetic/`): the remaining analytic hypotheses are E5 (`hE1`), E8 (`hE2`) and
E7 (`hS7`) with the degree bookkeeping of their thresholds and tolerances.  The slow exponents
must satisfy `e.eA ≤ 2`, `e.eB ≤ 4`, `e.eW ≤ 5/2` (the kinetic degree lemma), which covers
`slowExpHA`, `slowExpEl` and the Fourier-side `⟨2, 3, 4, 5/2⟩`. -/
theorem quantitative_fixed_force_of_energy'
    {K₁ K₂ m₀ Tp : ℝ} {e : SlowExp} {q₁ q₂ qS : ℝ → ℝ → Caps → ℝ}
    {Nbar piTol : ℝ → ℝ → ℝ} (hTp : 2 ≤ Tp) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4) (he : 1 ≤ e.eA ∧ 1 ≤ e.eB ∧ 1 ≤ e.eW)
    (heA : e.eA ≤ 2) (heB : e.eB ≤ 4) (heW : e.eW ≤ 5 / 2)
    (hE1 : ∀ Cs : ℝ, 0 ≤ Cs → ResH1 ((281 : ℝ) / 1000) Cs → ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H1EnergyInterface ((281 : ℝ) / 1000) Cs μ φ Tp (Nbar μ φ) (piTol μ φ) K₁ (q₁ μ φ) nearN)
    (hE2 : ∀ CH : ℝ, 1 ≤ CH → ResH2 ((281 : ℝ) / 1000) CH → ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H2EnergyInterface ((281 : ℝ) / 1000) CH μ φ Tp K₂ m₀ (q₂ μ φ) nearN)
    (hS7 : SlowCapsInterface Tp e qS)
    (hq₁ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e q₁)
    (hq₂ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e q₂)
    (hqS : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e qS)
    (hNbar : AtMostLinear Nbar) (hpi : AtMostLinear piTol)
    (hNbar0 : ∀ μ φ : ℝ, 0 ≤ Nbar μ φ) (hpi0 : ∀ μ φ : ℝ, 0 ≤ piTol μ φ) :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ C : ℝ, ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F → F / ν ^ 2 ≤ φ →
        C * (1 + M / ν) ^ ((9876 : ℝ) / 719 + ε) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  obtain ⟨q₀, hK, hdeg⟩ := kineticInterface e heA heB heW
  have hq₀ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e q₀ :=
    (hdeg _ (by norm_num) (by norm_num)).mono (by rw [dOf_281])
  exact quantitative_fixed_force_of_energy hTp hK₁ hK₂ hm₀ he hK hE1 hE2 hS7 hq₀ hq₁ hq₂
    hqS hNbar hpi hNbar0 hpi0


/-- **Theorem 1.2, fixed force, with the kinetic and slow-cap interfaces discharged.**  Same as
`quantitative_fixed_force_of_energy'`, with E7 supplied by `slowCapsInterface`
(`Quant/Energy/Slow/`) at the piece length `Tp = 2` and the exponents `slowExpF = ⟨2, 3, 4, 5/2⟩`.
The remaining analytic hypotheses are E5 (`hE1`) and E8 (`hE2`) with the degree bookkeeping of
their thresholds and tolerances. -/
theorem quantitative_fixed_force_of_H1H2
    {K₁ K₂ m₀ : ℝ} {q₁ q₂ : ℝ → ℝ → Caps → ℝ} {Nbar piTol : ℝ → ℝ → ℝ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4)
    (hE1 : ∀ Cs : ℝ, 0 ≤ Cs → ResH1 ((281 : ℝ) / 1000) Cs → ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H1EnergyInterface ((281 : ℝ) / 1000) Cs μ φ 2 (Nbar μ φ) (piTol μ φ) K₁ (q₁ μ φ) nearN)
    (hE2 : ∀ CH : ℝ, 1 ≤ CH → ResH2 ((281 : ℝ) / 1000) CH → ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H2EnergyInterface ((281 : ℝ) / 1000) CH μ φ 2 K₂ m₀ (q₂ μ φ) nearN)
    (hq₁ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) slowExpF q₁)
    (hq₂ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) slowExpF q₂)
    (hNbar : AtMostLinear Nbar) (hpi : AtMostLinear piTol)
    (hNbar0 : ∀ μ φ : ℝ, 0 ≤ Nbar μ φ) (hpi0 : ∀ μ φ : ℝ, 0 ≤ piTol μ φ) :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ C : ℝ, ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F → F / ν ^ 2 ≤ φ →
        C * (1 + M / ν) ^ ((9876 : ℝ) / 719 + ε) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  exact quantitative_fixed_force_of_energy' (by norm_num) hK₁ hK₂ hm₀
    (by norm_num [slowExpF]) (by norm_num [slowExpF]) (by norm_num [slowExpF])
    (by norm_num [slowExpF]) hE1 hE2 slowCapsInterface_of_threshold hq₁ hq₂ slow_degree hNbar hpi
    hNbar0 hpi0


/-- **Theorem 1.2, fixed force, with everything but the `H²` energy discharged.**  Same as
`quantitative_fixed_force_of_H1H2`, with E5 supplied by `h1Energy_of_threshold` and `h1_degree`
(`Quant/Energy/H1/`).  The only analytic hypothesis left is E8 (`hE2`) with the degree of its
threshold; the only other inputs are the two published counting theorems. -/
theorem quantitative_fixed_force_of_H2
    {K₂ m₀ : ℝ} {q₂ : ℝ → ℝ → Caps → ℝ} (hK₂ : 0 ≤ K₂) (hm₀ : 0 ≤ m₀ ∧ m₀ ≤ 1 / 4)
    (hE2 : ∀ CH : ℝ, 1 ≤ CH → ResH2 ((281 : ℝ) / 1000) CH → ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H2EnergyInterface ((281 : ℝ) / 1000) CH μ φ 2 K₂ m₀ (q₂ μ φ) nearN)
    (hq₂ : DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) slowExpF q₂) :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ C : ℝ, ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F → F / ν ^ 2 ≤ φ →
        C * (1 + M / ν) ^ ((9876 : ℝ) / 719 + ε) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  have hK₁ : 0 ≤ h1K₁ := by
    unfold h1K₁
    exact mul_nonneg (mul_nonneg (by norm_num) nearC₀_pos.le) cQ1_pos.le
  exact quantitative_fixed_force_of_H1H2 hK₁ hK₂ hm₀ h1Energy_of_threshold hE2
    (h1_degree slowExpF (by norm_num [slowExpF]) (by norm_num [slowExpF])
      (by norm_num [slowExpF]) (by norm_num [slowExpF]))
    hq₂ h1Nbar_atMostLinear h1Pi_atMostLinear h1Nbar_nonneg h1Pi_nonneg


/-- **Theorem 1.2, fixed force, proved** from the two published counting theorems: E8 is supplied
by `H2.h2EnergyInterface_uniform`.  This is the proof of `OVNS.quantitative_fixed_force`
(`OddViscousNS/Quant.lean`). -/
theorem quantitative_fixed_force_proved :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ C : ℝ, ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F → F / ν ^ 2 ≤ φ →
        C * (1 + M / ν) ^ ((9876 : ℝ) / 719 + ε) ≤ |α| / ν →
        GlobalConclusion' ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  obtain ⟨K₂, m₀, q₂, hK₂, hm0, hm1, hE2, hq₂⟩ := H2.h2EnergyInterface_uniform
  exact quantitative_fixed_force_of_H2 hK₂ ⟨hm0, hm1⟩ hE2 hq₂

end OVNS.Quant
