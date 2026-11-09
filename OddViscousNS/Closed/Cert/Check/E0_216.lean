import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_216_0 : check (edgeOf 0) 33 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_216_1 : check (edgeOf 0) 33 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_216_2 : check (edgeOf 0) 33 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_216_3 : check (edgeOf 0) 34 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_216_4 : check (edgeOf 0) 35 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_216_5 : check (edgeOf 0) 35 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_216_6 : check (edgeOf 0) 33 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_216_7 : check (edgeOf 0) 33 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
