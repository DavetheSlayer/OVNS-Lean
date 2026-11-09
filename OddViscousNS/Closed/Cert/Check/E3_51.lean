import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e3_51_0 : check (edgeOf 3) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_51_1 : check (edgeOf 3) 32 ⟨(3 / 8 : ℚ), (13 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_51_2 : check (edgeOf 3) 32 ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_51_3 : check (edgeOf 3) 33 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_51_4 : check (edgeOf 3) 32 ⟨(3 / 8 : ℚ), (13 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_51_5 : check (edgeOf 3) 32 ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_51_6 : check (edgeOf 3) 33 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_51_7 : check (edgeOf 3) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
