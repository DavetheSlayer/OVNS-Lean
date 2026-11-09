import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e39_20_0 : check (edgeOf 39) 30 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (19 / 32 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_20_1 : check (edgeOf 39) 29 ⟨(11 / 32 : ℚ), (23 / 64 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_20_2 : check (edgeOf 39) 29 ⟨(23 / 64 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_20_3 : check (edgeOf 39) 31 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_20_4 : check (edgeOf 39) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_20_5 : check (edgeOf 39) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_20_6 : check (edgeOf 39) 30 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (21 / 32 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_20_7 : check (edgeOf 39) 30 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
