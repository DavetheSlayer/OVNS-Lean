import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e3_54_0 : check (edgeOf 3) 32 ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_54_1 : check (edgeOf 3) 32 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_54_2 : check (edgeOf 3) 32 ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_54_3 : check (edgeOf 3) 32 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_54_4 : check (edgeOf 3) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_54_5 : check (edgeOf 3) 32 ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_54_6 : check (edgeOf 3) 32 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_54_7 : check (edgeOf 3) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
