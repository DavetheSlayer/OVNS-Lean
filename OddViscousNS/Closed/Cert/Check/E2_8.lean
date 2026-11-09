import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e2_8_0 : check (edgeOf 2) 34 ⟨(0 : ℚ), (1 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_8_1 : check (edgeOf 2) 35 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_8_2 : check (edgeOf 2) 36 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_8_3 : check (edgeOf 2) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_8_4 : check (edgeOf 2) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_8_5 : check (edgeOf 2) 34 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_8_6 : check (edgeOf 2) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_8_7 : check (edgeOf 2) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
