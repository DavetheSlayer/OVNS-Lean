import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e2_118_0 : check (edgeOf 2) 32 ⟨(27 / 32 : ℚ), (7 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_118_1 : check (edgeOf 2) 32 ⟨(3 / 4 : ℚ), (25 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_118_2 : check (edgeOf 2) 32 ⟨(25 / 32 : ℚ), (13 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_118_3 : check (edgeOf 2) 33 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_118_4 : check (edgeOf 2) 33 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_118_5 : check (edgeOf 2) 33 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_118_6 : check (edgeOf 2) 32 ⟨(13 / 16 : ℚ), (27 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_118_7 : check (edgeOf 2) 32 ⟨(27 / 32 : ℚ), (7 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
