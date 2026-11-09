import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e5_58_0 : check (edgeOf 5) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_58_1 : check (edgeOf 5) 36 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_58_2 : check (edgeOf 5) 33 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_58_3 : check (edgeOf 5) 33 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_58_4 : check (edgeOf 5) 34 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_58_5 : check (edgeOf 5) 33 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_58_6 : check (edgeOf 5) 33 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_58_7 : check (edgeOf 5) 34 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
