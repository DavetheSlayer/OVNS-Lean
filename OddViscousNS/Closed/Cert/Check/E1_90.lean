import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_90_0 : check (edgeOf 1) 35 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_90_1 : check (edgeOf 1) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_90_2 : check (edgeOf 1) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_90_3 : check (edgeOf 1) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_90_4 : check (edgeOf 1) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_90_5 : check (edgeOf 1) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_90_6 : check (edgeOf 1) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_90_7 : check (edgeOf 1) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
