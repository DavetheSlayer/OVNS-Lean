import OddViscousNS.Closed.Forced.Moment.ParamsCf

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeCf_25 : rangeOk PCf 226 242 = true := by
  decide +kernel

end OVNS.Forced.Mom
