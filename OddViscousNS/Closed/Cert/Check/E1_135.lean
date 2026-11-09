import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_135_0 : check (edgeOf 1) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_135_1 : check (edgeOf 1) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_135_2 : check (edgeOf 1) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_135_3 : check (edgeOf 1) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_135_4 : check (edgeOf 1) 34 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_135_5 : check (edgeOf 1) 34 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_135_6 : check (edgeOf 1) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_135_7 : check (edgeOf 1) 32 ⟨(5 / 8 : ℚ), (21 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
