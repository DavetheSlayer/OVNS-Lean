import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_204_0 : check (edgeOf 0) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_204_1 : check (edgeOf 0) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_204_2 : check (edgeOf 0) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_204_3 : check (edgeOf 0) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_204_4 : check (edgeOf 0) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_204_5 : check (edgeOf 0) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_204_6 : check (edgeOf 0) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_204_7 : check (edgeOf 0) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
