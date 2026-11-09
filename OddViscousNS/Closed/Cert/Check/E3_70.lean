import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e3_70_0 : check (edgeOf 3) 35 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_70_1 : check (edgeOf 3) 35 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_70_2 : check (edgeOf 3) 35 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_70_3 : check (edgeOf 3) 35 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_70_4 : check (edgeOf 3) 35 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_70_5 : check (edgeOf 3) 35 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_70_6 : check (edgeOf 3) 35 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_70_7 : check (edgeOf 3) 35 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
