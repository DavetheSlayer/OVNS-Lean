import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_77_0 : check (edgeOf 1) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_77_1 : check (edgeOf 1) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_77_2 : check (edgeOf 1) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_77_3 : check (edgeOf 1) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_77_4 : check (edgeOf 1) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_77_5 : check (edgeOf 1) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_77_6 : check (edgeOf 1) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_77_7 : check (edgeOf 1) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
