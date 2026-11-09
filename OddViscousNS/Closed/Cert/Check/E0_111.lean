import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_111_0 : check (edgeOf 0) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_111_1 : check (edgeOf 0) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_111_2 : check (edgeOf 0) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_111_3 : check (edgeOf 0) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_111_4 : check (edgeOf 0) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_111_5 : check (edgeOf 0) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_111_6 : check (edgeOf 0) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_111_7 : check (edgeOf 0) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
