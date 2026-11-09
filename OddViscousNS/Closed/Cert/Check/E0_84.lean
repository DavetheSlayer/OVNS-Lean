import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_84_0 : check (edgeOf 0) 33 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_84_1 : check (edgeOf 0) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_84_2 : check (edgeOf 0) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_84_3 : check (edgeOf 0) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_84_4 : check (edgeOf 0) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_84_5 : check (edgeOf 0) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_84_6 : check (edgeOf 0) 37 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_84_7 : check (edgeOf 0) 37 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
