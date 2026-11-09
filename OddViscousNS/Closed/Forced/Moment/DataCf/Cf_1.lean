import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_1 : rangeOk PCf 7 14 = true := by
  decide +kernel

end OVNS.Forced.Mom
