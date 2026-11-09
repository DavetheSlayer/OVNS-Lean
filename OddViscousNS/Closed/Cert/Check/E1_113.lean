import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_113_0 : check (edgeOf 1) 33 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_113_1 : check (edgeOf 1) 36 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_113_2 : check (edgeOf 1) 33 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_113_3 : check (edgeOf 1) 33 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_113_4 : check (edgeOf 1) 34 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_113_5 : check (edgeOf 1) 35 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_113_6 : check (edgeOf 1) 36 ⟨(7 / 8 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_113_7 : check (edgeOf 1) 33 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
