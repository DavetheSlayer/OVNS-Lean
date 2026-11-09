import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e7_50_0 : check (edgeOf 7) 34 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_50_1 : check (edgeOf 7) 35 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_50_2 : check (edgeOf 7) 36 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_50_3 : check (edgeOf 7) 35 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_50_4 : check (edgeOf 7) 35 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_50_5 : check (edgeOf 7) 36 ⟨(7 / 8 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_50_6 : check (edgeOf 7) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_50_7 : check (edgeOf 7) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
