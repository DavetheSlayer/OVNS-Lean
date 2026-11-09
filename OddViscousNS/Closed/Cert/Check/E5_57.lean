import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e5_57_0 : check (edgeOf 5) 33 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_57_1 : check (edgeOf 5) 33 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_57_2 : check (edgeOf 5) 34 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_57_3 : check (edgeOf 5) 33 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_57_4 : check (edgeOf 5) 33 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_57_5 : check (edgeOf 5) 34 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_57_6 : check (edgeOf 5) 36 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_57_7 : check (edgeOf 5) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
