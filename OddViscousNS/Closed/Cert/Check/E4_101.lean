import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e4_101_0 : check (edgeOf 4) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_101_1 : check (edgeOf 4) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_101_2 : check (edgeOf 4) 37 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_101_3 : check (edgeOf 4) 36 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_101_4 : check (edgeOf 4) 35 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_101_5 : check (edgeOf 4) 35 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_101_6 : check (edgeOf 4) 37 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_101_7 : check (edgeOf 4) 39 ⟨(3 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
