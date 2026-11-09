import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_10 : rangeOk PCf 71 79 = true := by
  decide +kernel

end OVNS.Forced.Mom
