import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e5_30_0 : check (edgeOf 5) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_30_1 : check (edgeOf 5) 32 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_30_2 : check (edgeOf 5) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_30_3 : check (edgeOf 5) 32 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_30_4 : check (edgeOf 5) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_30_5 : check (edgeOf 5) 32 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_30_6 : check (edgeOf 5) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_30_7 : check (edgeOf 5) 32 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
