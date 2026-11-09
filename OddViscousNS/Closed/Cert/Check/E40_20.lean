import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e40_20_0 : check (edgeOf 40) 30 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_20_1 : check (edgeOf 40) 31 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_20_2 : check (edgeOf 40) 30 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (19 / 32 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_20_3 : check (edgeOf 40) 30 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_20_4 : check (edgeOf 40) 31 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_20_5 : check (edgeOf 40) 34 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_20_6 : check (edgeOf 40) 31 ⟨(3 / 8 : ℚ), (13 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_20_7 : check (edgeOf 40) 31 ⟨(3 / 8 : ℚ), (13 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
