import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_20 : rangeOk PCf 163 174 = true := by
  decide +kernel

end OVNS.Forced.Mom
