import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_51_0 : check (edgeOf 0) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_51_1 : check (edgeOf 0) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_51_2 : check (edgeOf 0) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_51_3 : check (edgeOf 0) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_51_4 : check (edgeOf 0) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_51_5 : check (edgeOf 0) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_51_6 : check (edgeOf 0) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_51_7 : check (edgeOf 0) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
