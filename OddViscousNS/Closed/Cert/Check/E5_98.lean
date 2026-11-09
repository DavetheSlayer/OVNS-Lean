import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e5_98_0 : check (edgeOf 5) 37 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_98_1 : check (edgeOf 5) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_98_2 : check (edgeOf 5) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_98_3 : check (edgeOf 5) 36 ⟨(7 / 8 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_98_4 : check (edgeOf 5) 37 ⟨(7 / 8 : ℚ), (1 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_98_5 : check (edgeOf 5) 39 ⟨(3 / 4 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
