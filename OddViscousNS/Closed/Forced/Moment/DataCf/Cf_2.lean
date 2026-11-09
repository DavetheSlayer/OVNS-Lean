import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_2 : rangeOk PCf 14 21 = true := by
  decide +kernel

end OVNS.Forced.Mom
