import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e3_31_0 : check (edgeOf 3) 32 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_31_1 : check (edgeOf 3) 32 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_31_2 : check (edgeOf 3) 32 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_31_3 : check (edgeOf 3) 32 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_31_4 : check (edgeOf 3) 32 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_31_5 : check (edgeOf 3) 32 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_31_6 : check (edgeOf 3) 32 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_31_7 : check (edgeOf 3) 32 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
