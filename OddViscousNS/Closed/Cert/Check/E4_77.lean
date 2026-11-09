import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e4_77_0 : check (edgeOf 4) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_77_1 : check (edgeOf 4) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_77_2 : check (edgeOf 4) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_77_3 : check (edgeOf 4) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_77_4 : check (edgeOf 4) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_77_5 : check (edgeOf 4) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_77_6 : check (edgeOf 4) 33 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_77_7 : check (edgeOf 4) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
