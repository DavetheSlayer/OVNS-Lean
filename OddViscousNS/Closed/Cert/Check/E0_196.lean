import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_196_0 : check (edgeOf 0) 35 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_196_1 : check (edgeOf 0) 39 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_196_2 : check (edgeOf 0) 36 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_196_3 : check (edgeOf 0) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_196_4 : check (edgeOf 0) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_196_5 : check (edgeOf 0) 36 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_196_6 : check (edgeOf 0) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_196_7 : check (edgeOf 0) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
