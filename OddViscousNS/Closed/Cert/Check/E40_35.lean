import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e40_35_0 : check (edgeOf 40) 31 ⟨(25 / 32 : ℚ), (13 / 16 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_35_1 : check (edgeOf 40) 31 ⟨(25 / 32 : ℚ), (13 / 16 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_35_2 : check (edgeOf 40) 34 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_35_3 : check (edgeOf 40) 32 ⟨(13 / 16 : ℚ), (27 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_35_4 : check (edgeOf 40) 32 ⟨(27 / 32 : ℚ), (7 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_35_5 : check (edgeOf 40) 31 ⟨(13 / 16 : ℚ), (27 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_35_6 : check (edgeOf 40) 31 ⟨(13 / 16 : ℚ), (27 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_35_7 : check (edgeOf 40) 32 ⟨(27 / 32 : ℚ), (7 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
