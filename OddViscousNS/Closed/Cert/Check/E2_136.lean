import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e2_136_0 : check (edgeOf 2) 36 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_136_1 : check (edgeOf 2) 35 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_136_2 : check (edgeOf 2) 35 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_136_3 : check (edgeOf 2) 36 ⟨(7 / 8 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_136_4 : check (edgeOf 2) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_136_5 : check (edgeOf 2) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_136_6 : check (edgeOf 2) 36 ⟨(7 / 8 : ℚ), (1 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_136_7 : check (edgeOf 2) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
