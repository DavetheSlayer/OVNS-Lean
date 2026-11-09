import OddViscousNS.Closed.Forced.Common.Conclusion
import OddViscousNS.Closed.Forced.Common.Rows
import OddViscousNS.Closed.Forced.Moment.Rows
import OddViscousNS.Closed.Forced.Moment.RowsCf

/-!
# The common row `(419650, 419650, 850)`: `k = .8393`, `f₀ = 1`, `s = 419650/208013`

The kernel data: the 436-cell certificate (`Common/Rows.lean`), the moment pair tables
(`Moment/Rows.lean`: `coverAl`, `coverSm`, the six `bigJ*` checks; `Moment/RowsCf.lean`: `coverCf`).
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

namespace Forced

open Chk Mom Com

theorem common_row_conclusion (hRB : RowBound gOVNS) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ RowConcl (419650, 419650, 850) Bd := by
  have hO : MomentOracle := momentOracle_of hRB coverAl coverSm
    ⟨bigJLo90r0, bigJLo90rh, bigJM0r91, bigJM0rh, bigJHir0, bigJHirh⟩ coverCf
  have hR : CRowOK kC f0C sC JC cellsC termC winC := ⟨chainC_ok, cellsC_ok, termC_ok, winC_ok⟩
  have hs : (0 : ℚ) < sC := by norm_num [sC]
  have hk : ((kC : ℚ) : ℝ) = (sC : ℝ) * κ₀ := by norm_num [kC, sC, κ₀]
  have hf0 : f0C ≤ 1 := by norm_num [f0C]
  obtain ⟨Bd, hBd, h⟩ := common_row_conclusion_of hO hs hk hf0 hR (hRB.mono gOVNS_le_M₀)
  refine ⟨Bd, hBd, fun ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMν hFν => ?_⟩
  have hsR : ((sC : ℚ) : ℝ) = 419650 / 208013 := by norm_num [sC]
  have hMs : M / ν ≤ sC := by
    rw [hsR, le_div_iff₀ (by norm_num)]
    simp only at hMν
    linarith
  have hFs : F / ν ^ 2 ≤ f0C * sC := by
    rw [hsR, show ((f0C : ℚ) : ℝ) = 1 by norm_num [f0C], one_mul, le_div_iff₀ (by norm_num)]
    simp only at hFν
    linarith
  obtain ⟨hg, hw⟩ := h ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMs hFs
  refine ⟨hg, fun u hu a b ha hab hb => ?_⟩
  have := hw u hu a b ha hab hb
  simp only [JC] at this
  convert this using 3
  rw [hsR]
  norm_num

end Forced

end OVNS
