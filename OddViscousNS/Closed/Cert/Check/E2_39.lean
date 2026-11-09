import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e2_39_0 : check (edgeOf 2) 34 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_39_1 : check (edgeOf 2) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_39_2 : check (edgeOf 2) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_39_3 : check (edgeOf 2) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_39_4 : check (edgeOf 2) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_39_5 : check (edgeOf 2) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_39_6 : check (edgeOf 2) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_39_7 : check (edgeOf 2) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
