import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_135_0 : check (edgeOf 0) 37 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_135_1 : check (edgeOf 0) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_135_2 : check (edgeOf 0) 32 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_135_3 : check (edgeOf 0) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_135_4 : check (edgeOf 0) 32 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_135_5 : check (edgeOf 0) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_135_6 : check (edgeOf 0) 32 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_135_7 : check (edgeOf 0) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
