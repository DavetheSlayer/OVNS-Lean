import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e22_37_0 : check (edgeOf 22) 40 ⟨(3 / 4 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (by decide +kernel) (by decide)

end OVNS.Cert
