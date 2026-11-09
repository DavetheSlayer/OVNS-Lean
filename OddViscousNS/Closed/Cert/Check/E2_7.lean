import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e2_7_0 : check (edgeOf 2) 33 ⟨(0 : ℚ), (1 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_7_1 : check (edgeOf 2) 33 ⟨(0 : ℚ), (1 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_7_2 : check (edgeOf 2) 33 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_7_3 : check (edgeOf 2) 33 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_7_4 : check (edgeOf 2) 33 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_7_5 : check (edgeOf 2) 33 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_7_6 : check (edgeOf 2) 36 ⟨(0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_7_7 : check (edgeOf 2) 34 ⟨(0 : ℚ), (1 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
