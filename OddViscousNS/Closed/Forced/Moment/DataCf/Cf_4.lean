import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_4 : rangeOk PCf 27 35 = true := by
  decide +kernel

end OVNS.Forced.Mom
