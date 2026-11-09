import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_63_0 : check (edgeOf 1) 32 ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_63_1 : check (edgeOf 1) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_63_2 : check (edgeOf 1) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_63_3 : check (edgeOf 1) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_63_4 : check (edgeOf 1) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_63_5 : check (edgeOf 1) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_63_6 : check (edgeOf 1) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_63_7 : check (edgeOf 1) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
