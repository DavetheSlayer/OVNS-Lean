import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_47_0 : check (edgeOf 1) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_47_1 : check (edgeOf 1) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_47_2 : check (edgeOf 1) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_47_3 : check (edgeOf 1) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_47_4 : check (edgeOf 1) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_47_5 : check (edgeOf 1) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_47_6 : check (edgeOf 1) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_47_7 : check (edgeOf 1) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
