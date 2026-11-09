import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_158_0 : check (edgeOf 1) 36 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_158_1 : check (edgeOf 1) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_158_2 : check (edgeOf 1) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_158_3 : check (edgeOf 1) 36 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_158_4 : check (edgeOf 1) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_158_5 : check (edgeOf 1) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_158_6 : check (edgeOf 1) 36 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_158_7 : check (edgeOf 1) 35 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
