import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_156_0 : check (edgeOf 1) 33 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_156_1 : check (edgeOf 1) 33 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_156_2 : check (edgeOf 1) 33 ⟨(15 / 16 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_156_3 : check (edgeOf 1) 33 ⟨(15 / 16 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_156_4 : check (edgeOf 1) 34 ⟨(15 / 16 : ℚ), (1 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_156_5 : check (edgeOf 1) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_156_6 : check (edgeOf 1) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_156_7 : check (edgeOf 1) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
