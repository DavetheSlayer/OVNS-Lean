import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_0 : rangeOk PCf 1 7 = true := by
  decide +kernel

end OVNS.Forced.Mom
