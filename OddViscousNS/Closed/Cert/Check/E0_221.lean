import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_221_0 : check (edgeOf 0) 37 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_221_1 : check (edgeOf 0) 37 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_221_2 : check (edgeOf 0) 37 ⟨(7 / 8 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_221_3 : check (edgeOf 0) 37 ⟨(7 / 8 : ℚ), (1 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
