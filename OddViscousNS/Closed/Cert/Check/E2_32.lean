import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e2_32_0 : check (edgeOf 2) 35 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_32_1 : check (edgeOf 2) 36 ⟨(0 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_32_2 : check (edgeOf 2) 37 ⟨(0 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_32_3 : check (edgeOf 2) 35 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_32_4 : check (edgeOf 2) 35 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_32_5 : check (edgeOf 2) 36 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_32_6 : check (edgeOf 2) 37 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_32_7 : check (edgeOf 2) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
