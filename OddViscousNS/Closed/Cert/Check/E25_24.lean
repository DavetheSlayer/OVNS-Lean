import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e25_24_0 : check (edgeOf 25) 32 ⟨(21 / 32 : ℚ), (11 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e25_24_1 : check (edgeOf 25) 32 ⟨(5 / 8 : ℚ), (21 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e25_24_2 : check (edgeOf 25) 32 ⟨(21 / 32 : ℚ), (11 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e25_24_3 : check (edgeOf 25) 34 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e25_24_4 : check (edgeOf 25) 32 ⟨(11 / 16 : ℚ), (23 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e25_24_5 : check (edgeOf 25) 32 ⟨(23 / 32 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e25_24_6 : check (edgeOf 25) 32 ⟨(11 / 16 : ℚ), (23 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e25_24_7 : check (edgeOf 25) 32 ⟨(23 / 32 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
