import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e40_4_0 : check (edgeOf 40) 32 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_4_1 : check (edgeOf 40) 32 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_4_2 : check (edgeOf 40) 30 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (19 / 32 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_4_3 : check (edgeOf 40) 29 ⟨(1 / 16 : ℚ), (5 / 64 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_4_4 : check (edgeOf 40) 29 ⟨(5 / 64 : ℚ), (3 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_4_5 : check (edgeOf 40) 31 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_4_6 : check (edgeOf 40) 30 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (19 / 32 : ℚ)⟩ = true := by
  decide +kernel

theorem e40_4_7 : check (edgeOf 40) 29 ⟨(3 / 32 : ℚ), (7 / 64 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
