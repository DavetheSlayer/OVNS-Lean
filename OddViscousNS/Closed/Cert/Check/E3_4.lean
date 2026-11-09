import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e3_4_0 : check (edgeOf 3) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_4_1 : check (edgeOf 3) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_4_2 : check (edgeOf 3) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_4_3 : check (edgeOf 3) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_4_4 : check (edgeOf 3) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_4_5 : check (edgeOf 3) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_4_6 : check (edgeOf 3) 36 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_4_7 : check (edgeOf 3) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
