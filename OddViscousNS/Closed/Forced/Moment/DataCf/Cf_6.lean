import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_6 : rangeOk PCf 42 49 = true := by
  decide +kernel

end OVNS.Forced.Mom
