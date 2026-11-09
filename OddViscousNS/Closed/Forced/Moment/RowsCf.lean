import OddViscousNS.Closed.Forced.Moment.ParamsCf
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_0
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_1
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_2
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_3
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_4
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_5
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_6
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_7
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_8
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_9
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_10
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_11
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_12
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_13
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_14
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_15
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_16
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_17
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_18
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_19
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_20
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_21
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_22
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_23
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_24
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_25
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_26
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_27
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_28
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_29
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_30
import OddViscousNS.Closed.Forced.Moment.DataCf.Cf_31

namespace OVNS.Forced.Mom

/-- Coverage of `C_l ∈ [1, 800)` by the checked ranges of the `c_f` row. -/
theorem coverCf (Cl : ℕ) (h1 : 1 ≤ Cl) (h2 : Cl < 800) :
    ∃ lo hi, lo ≤ Cl ∧ Cl < hi ∧ rangeOk PCf lo hi = true := by
  rcases (show (1 ≤ Cl ∧ Cl < 7) ∨ (7 ≤ Cl ∧ Cl < 14) ∨ (14 ≤ Cl ∧ Cl < 21) ∨ (21 ≤ Cl ∧ Cl < 27) ∨ (27 ≤ Cl ∧ Cl < 35) ∨ (35 ≤ Cl ∧ Cl < 42) ∨ (42 ≤ Cl ∧ Cl < 49) ∨ (49 ≤ Cl ∧ Cl < 55) ∨ (55 ≤ Cl ∧ Cl < 63) ∨ (63 ≤ Cl ∧ Cl < 71) ∨ (71 ≤ Cl ∧ Cl < 79) ∨ (79 ≤ Cl ∧ Cl < 87) ∨ (87 ≤ Cl ∧ Cl < 97) ∨ (97 ≤ Cl ∧ Cl < 105) ∨ (105 ≤ Cl ∧ Cl < 114) ∨ (114 ≤ Cl ∧ Cl < 123) ∨ (123 ≤ Cl ∧ Cl < 133) ∨ (133 ≤ Cl ∧ Cl < 142) ∨ (142 ≤ Cl ∧ Cl < 151) ∨ (151 ≤ Cl ∧ Cl < 163) ∨ (163 ≤ Cl ∧ Cl < 174) ∨ (174 ≤ Cl ∧ Cl < 186) ∨ (186 ≤ Cl ∧ Cl < 198) ∨ (198 ≤ Cl ∧ Cl < 211) ∨ (211 ≤ Cl ∧ Cl < 226) ∨ (226 ≤ Cl ∧ Cl < 242) ∨ (242 ≤ Cl ∧ Cl < 259) ∨ (259 ≤ Cl ∧ Cl < 277) ∨ (277 ≤ Cl ∧ Cl < 299) ∨ (299 ≤ Cl ∧ Cl < 327) ∨ (327 ≤ Cl ∧ Cl < 378) ∨ (378 ≤ Cl ∧ Cl < 800) by omega) with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨1, 7, h.1, h.2, rangeCf_0⟩
  · exact ⟨7, 14, h.1, h.2, rangeCf_1⟩
  · exact ⟨14, 21, h.1, h.2, rangeCf_2⟩
  · exact ⟨21, 27, h.1, h.2, rangeCf_3⟩
  · exact ⟨27, 35, h.1, h.2, rangeCf_4⟩
  · exact ⟨35, 42, h.1, h.2, rangeCf_5⟩
  · exact ⟨42, 49, h.1, h.2, rangeCf_6⟩
  · exact ⟨49, 55, h.1, h.2, rangeCf_7⟩
  · exact ⟨55, 63, h.1, h.2, rangeCf_8⟩
  · exact ⟨63, 71, h.1, h.2, rangeCf_9⟩
  · exact ⟨71, 79, h.1, h.2, rangeCf_10⟩
  · exact ⟨79, 87, h.1, h.2, rangeCf_11⟩
  · exact ⟨87, 97, h.1, h.2, rangeCf_12⟩
  · exact ⟨97, 105, h.1, h.2, rangeCf_13⟩
  · exact ⟨105, 114, h.1, h.2, rangeCf_14⟩
  · exact ⟨114, 123, h.1, h.2, rangeCf_15⟩
  · exact ⟨123, 133, h.1, h.2, rangeCf_16⟩
  · exact ⟨133, 142, h.1, h.2, rangeCf_17⟩
  · exact ⟨142, 151, h.1, h.2, rangeCf_18⟩
  · exact ⟨151, 163, h.1, h.2, rangeCf_19⟩
  · exact ⟨163, 174, h.1, h.2, rangeCf_20⟩
  · exact ⟨174, 186, h.1, h.2, rangeCf_21⟩
  · exact ⟨186, 198, h.1, h.2, rangeCf_22⟩
  · exact ⟨198, 211, h.1, h.2, rangeCf_23⟩
  · exact ⟨211, 226, h.1, h.2, rangeCf_24⟩
  · exact ⟨226, 242, h.1, h.2, rangeCf_25⟩
  · exact ⟨242, 259, h.1, h.2, rangeCf_26⟩
  · exact ⟨259, 277, h.1, h.2, rangeCf_27⟩
  · exact ⟨277, 299, h.1, h.2, rangeCf_28⟩
  · exact ⟨299, 327, h.1, h.2, rangeCf_29⟩
  · exact ⟨327, 378, h.1, h.2, rangeCf_30⟩
  · exact ⟨378, 800, h.1, h.2, rangeCf_31⟩

end OVNS.Forced.Mom
