import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_201_0 : check (edgeOf 0) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_201_1 : check (edgeOf 0) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_201_2 : check (edgeOf 0) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_201_3 : check (edgeOf 0) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_201_4 : check (edgeOf 0) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_201_5 : check (edgeOf 0) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_201_6 : check (edgeOf 0) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_201_7 : check (edgeOf 0) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
