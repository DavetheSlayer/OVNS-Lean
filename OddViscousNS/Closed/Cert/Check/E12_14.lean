import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e12_14_0 : check (edgeOf 12) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e12_14_1 : check (edgeOf 12) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e12_14_2 : check (edgeOf 12) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e12_14_3 : check (edgeOf 12) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e12_14_4 : check (edgeOf 12) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e12_14_5 : check (edgeOf 12) 33 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e12_14_6 : check (edgeOf 12) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e12_14_7 : check (edgeOf 12) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
