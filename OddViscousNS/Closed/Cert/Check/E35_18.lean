import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e35_18_0 : check (edgeOf 35) 31 ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_18_1 : check (edgeOf 35) 31 ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_18_2 : check (edgeOf 35) 34 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_18_3 : check (edgeOf 35) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_18_4 : check (edgeOf 35) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_18_5 : check (edgeOf 35) 31 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_18_6 : check (edgeOf 35) 31 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_18_7 : check (edgeOf 35) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
