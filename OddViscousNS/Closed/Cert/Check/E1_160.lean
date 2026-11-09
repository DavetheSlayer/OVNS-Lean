import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_160_0 : check (edgeOf 1) 36 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_160_1 : check (edgeOf 1) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_160_2 : check (edgeOf 1) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_160_3 : check (edgeOf 1) 36 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_160_4 : check (edgeOf 1) 35 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_160_5 : check (edgeOf 1) 35 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_160_6 : check (edgeOf 1) 36 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_160_7 : check (edgeOf 1) 35 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
