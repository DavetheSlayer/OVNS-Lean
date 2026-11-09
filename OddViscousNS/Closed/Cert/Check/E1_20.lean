import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_20_0 : check (edgeOf 1) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_20_1 : check (edgeOf 1) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_20_2 : check (edgeOf 1) 34 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_20_3 : check (edgeOf 1) 36 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_20_4 : check (edgeOf 1) 33 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_20_5 : check (edgeOf 1) 33 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_20_6 : check (edgeOf 1) 33 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_20_7 : check (edgeOf 1) 33 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
