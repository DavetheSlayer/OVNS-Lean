import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_145_0 : check (edgeOf 0) 33 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_145_1 : check (edgeOf 0) 33 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_145_2 : check (edgeOf 0) 33 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_145_3 : check (edgeOf 0) 33 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_145_4 : check (edgeOf 0) 36 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_145_5 : check (edgeOf 0) 33 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_145_6 : check (edgeOf 0) 33 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_145_7 : check (edgeOf 0) 33 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
