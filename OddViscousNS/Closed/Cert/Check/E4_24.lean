import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e4_24_0 : check (edgeOf 4) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_24_1 : check (edgeOf 4) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_24_2 : check (edgeOf 4) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_24_3 : check (edgeOf 4) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_24_4 : check (edgeOf 4) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_24_5 : check (edgeOf 4) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_24_6 : check (edgeOf 4) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_24_7 : check (edgeOf 4) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
