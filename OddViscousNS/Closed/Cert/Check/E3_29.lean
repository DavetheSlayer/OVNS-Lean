import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e3_29_0 : check (edgeOf 3) 35 ⟨(0 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_29_1 : check (edgeOf 3) 35 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_29_2 : check (edgeOf 3) 36 ⟨(0 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_29_3 : check (edgeOf 3) 37 ⟨(0 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_29_4 : check (edgeOf 3) 35 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_29_5 : check (edgeOf 3) 35 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_29_6 : check (edgeOf 3) 36 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_29_7 : check (edgeOf 3) 37 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
