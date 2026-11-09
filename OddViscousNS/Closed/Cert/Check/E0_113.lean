import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_113_0 : check (edgeOf 0) 37 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_113_1 : check (edgeOf 0) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_113_2 : check (edgeOf 0) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_113_3 : check (edgeOf 0) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_113_4 : check (edgeOf 0) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_113_5 : check (edgeOf 0) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_113_6 : check (edgeOf 0) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_113_7 : check (edgeOf 0) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
