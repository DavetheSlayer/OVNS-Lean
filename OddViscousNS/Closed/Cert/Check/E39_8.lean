import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e39_8_0 : check (edgeOf 39) 30 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_8_1 : check (edgeOf 39) 31 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_8_2 : check (edgeOf 39) 29 ⟨(3 / 32 : ℚ), (7 / 64 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (21 / 32 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_8_3 : check (edgeOf 39) 29 ⟨(7 / 64 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (21 / 32 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_8_4 : check (edgeOf 39) 30 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_8_5 : check (edgeOf 39) 31 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_8_6 : check (edgeOf 39) 32 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_8_7 : check (edgeOf 39) 32 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
