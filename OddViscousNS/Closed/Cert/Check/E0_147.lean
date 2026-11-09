import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_147_0 : check (edgeOf 0) 33 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_147_1 : check (edgeOf 0) 33 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_147_2 : check (edgeOf 0) 33 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_147_3 : check (edgeOf 0) 33 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_147_4 : check (edgeOf 0) 33 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_147_5 : check (edgeOf 0) 33 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_147_6 : check (edgeOf 0) 39 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_147_7 : check (edgeOf 0) 36 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
