import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e10_16_0 : check (edgeOf 10) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_16_1 : check (edgeOf 10) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_16_2 : check (edgeOf 10) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_16_3 : check (edgeOf 10) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_16_4 : check (edgeOf 10) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_16_5 : check (edgeOf 10) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_16_6 : check (edgeOf 10) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_16_7 : check (edgeOf 10) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
