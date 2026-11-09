import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_102_0 : check (edgeOf 0) 32 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_102_1 : check (edgeOf 0) 32 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_102_2 : check (edgeOf 0) 33 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_102_3 : check (edgeOf 0) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_102_4 : check (edgeOf 0) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_102_5 : check (edgeOf 0) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_102_6 : check (edgeOf 0) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_102_7 : check (edgeOf 0) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
