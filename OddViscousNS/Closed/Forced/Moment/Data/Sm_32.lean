import OddViscousNS.Closed.Forced.Moment.Params

set_option maxRecDepth 100000

namespace OVNS.Forced.Mom

theorem rangeSm_32 : rangeOk PSm 212 220 = true := by
  decide +kernel

end OVNS.Forced.Mom
