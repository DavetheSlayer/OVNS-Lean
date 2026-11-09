import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_8 : rangeOk PCf 55 63 = true := by
  decide +kernel

end OVNS.Forced.Mom
