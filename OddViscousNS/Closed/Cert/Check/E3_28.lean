import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e3_28_0 : check (edgeOf 3) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_28_1 : check (edgeOf 3) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_28_2 : check (edgeOf 3) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_28_3 : check (edgeOf 3) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_28_4 : check (edgeOf 3) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_28_5 : check (edgeOf 3) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_28_6 : check (edgeOf 3) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_28_7 : check (edgeOf 3) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
