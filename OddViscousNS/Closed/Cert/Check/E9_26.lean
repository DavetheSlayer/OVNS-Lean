import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e9_26_0 : check (edgeOf 9) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e9_26_1 : check (edgeOf 9) 32 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e9_26_2 : check (edgeOf 9) 34 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e9_26_3 : check (edgeOf 9) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e9_26_4 : check (edgeOf 9) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e9_26_5 : check (edgeOf 9) 34 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e9_26_6 : check (edgeOf 9) 34 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e9_26_7 : check (edgeOf 9) 34 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
