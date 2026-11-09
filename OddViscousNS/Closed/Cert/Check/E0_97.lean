import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_97_0 : check (edgeOf 0) 34 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_97_1 : check (edgeOf 0) 34 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_97_2 : check (edgeOf 0) 39 ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_97_3 : check (edgeOf 0) 36 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_97_4 : check (edgeOf 0) 35 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_97_5 : check (edgeOf 0) 35 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_97_6 : check (edgeOf 0) 36 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_97_7 : check (edgeOf 0) 35 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
