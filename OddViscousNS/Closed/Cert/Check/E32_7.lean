import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e32_7_0 : check (edgeOf 32) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e32_7_1 : check (edgeOf 32) 31 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e32_7_2 : check (edgeOf 32) 31 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e32_7_3 : check (edgeOf 32) 31 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e32_7_4 : check (edgeOf 32) 31 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e32_7_5 : check (edgeOf 32) 34 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e32_7_6 : check (edgeOf 32) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e32_7_7 : check (edgeOf 32) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
