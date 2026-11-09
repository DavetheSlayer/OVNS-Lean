import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e23_26_0 : check (edgeOf 23) 32 ⟨(23 / 32 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_26_1 : check (edgeOf 23) 32 ⟨(11 / 16 : ℚ), (23 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_26_2 : check (edgeOf 23) 32 ⟨(23 / 32 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_26_3 : check (edgeOf 23) 34 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_26_4 : check (edgeOf 23) 32 ⟨(5 / 8 : ℚ), (21 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_26_5 : check (edgeOf 23) 32 ⟨(21 / 32 : ℚ), (11 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_26_6 : check (edgeOf 23) 33 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_26_7 : check (edgeOf 23) 34 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
