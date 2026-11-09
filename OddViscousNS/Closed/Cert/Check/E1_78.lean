import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_78_0 : check (edgeOf 1) 33 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_78_1 : check (edgeOf 1) 33 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_78_2 : check (edgeOf 1) 34 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_78_3 : check (edgeOf 1) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_78_4 : check (edgeOf 1) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_78_5 : check (edgeOf 1) 34 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_78_6 : check (edgeOf 1) 37 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_78_7 : check (edgeOf 1) 37 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
