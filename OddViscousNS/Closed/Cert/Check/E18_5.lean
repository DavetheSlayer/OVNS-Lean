import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e18_5_0 : check (edgeOf 18) 37 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e18_5_1 : check (edgeOf 18) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e18_5_2 : check (edgeOf 18) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e18_5_3 : check (edgeOf 18) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e18_5_4 : check (edgeOf 18) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e18_5_5 : check (edgeOf 18) 33 ⟨(0 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e18_5_6 : check (edgeOf 18) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e18_5_7 : check (edgeOf 18) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
