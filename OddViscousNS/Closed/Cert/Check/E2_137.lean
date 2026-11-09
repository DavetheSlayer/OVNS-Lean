import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e2_137_0 : check (edgeOf 2) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_137_1 : check (edgeOf 2) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_137_2 : check (edgeOf 2) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_137_3 : check (edgeOf 2) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_137_4 : check (edgeOf 2) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_137_5 : check (edgeOf 2) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_137_6 : check (edgeOf 2) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_137_7 : check (edgeOf 2) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
