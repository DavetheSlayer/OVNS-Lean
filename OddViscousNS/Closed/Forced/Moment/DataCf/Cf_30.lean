import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_30 : rangeOk PCf 327 378 = true := by
  decide +kernel

end OVNS.Forced.Mom
