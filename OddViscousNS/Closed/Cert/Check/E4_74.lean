import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e4_74_0 : check (edgeOf 4) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_74_1 : check (edgeOf 4) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_74_2 : check (edgeOf 4) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_74_3 : check (edgeOf 4) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_74_4 : check (edgeOf 4) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_74_5 : check (edgeOf 4) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_74_6 : check (edgeOf 4) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_74_7 : check (edgeOf 4) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
