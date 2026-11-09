import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e6_62_0 : check (edgeOf 6) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e6_62_1 : check (edgeOf 6) 34 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e6_62_2 : check (edgeOf 6) 34 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e6_62_3 : check (edgeOf 6) 34 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e6_62_4 : check (edgeOf 6) 34 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e6_62_5 : check (edgeOf 6) 34 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e6_62_6 : check (edgeOf 6) 32 ⟨(5 / 8 : ℚ), (21 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e6_62_7 : check (edgeOf 6) 32 ⟨(21 / 32 : ℚ), (11 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
