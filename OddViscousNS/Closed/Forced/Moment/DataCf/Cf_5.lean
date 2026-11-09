import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_5 : rangeOk PCf 35 42 = true := by
  decide +kernel

end OVNS.Forced.Mom
