import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e8_71_0 : check (edgeOf 8) 35 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_71_1 : check (edgeOf 8) 36 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_71_2 : check (edgeOf 8) 37 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_71_3 : check (edgeOf 8) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_71_4 : check (edgeOf 8) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_71_5 : check (edgeOf 8) 36 ⟨(7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_71_6 : check (edgeOf 8) 37 ⟨(7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_71_7 : check (edgeOf 8) 39 ⟨(3 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
