import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_16 : rangeOk PCf 123 133 = true := by
  decide +kernel

end OVNS.Forced.Mom
