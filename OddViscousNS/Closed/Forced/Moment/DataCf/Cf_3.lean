import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_3 : rangeOk PCf 21 27 = true := by
  decide +kernel

end OVNS.Forced.Mom
