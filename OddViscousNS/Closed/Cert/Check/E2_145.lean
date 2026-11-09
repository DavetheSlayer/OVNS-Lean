import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e2_145_0 : check (edgeOf 2) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_145_1 : check (edgeOf 2) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_145_2 : check (edgeOf 2) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_145_3 : check (edgeOf 2) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_145_4 : check (edgeOf 2) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_145_5 : check (edgeOf 2) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_145_6 : check (edgeOf 2) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_145_7 : check (edgeOf 2) 39 ⟨(3 / 4 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
