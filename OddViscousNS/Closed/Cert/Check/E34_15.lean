import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e34_15_0 : check (edgeOf 34) 31 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e34_15_1 : check (edgeOf 34) 31 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e34_15_2 : check (edgeOf 34) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e34_15_3 : check (edgeOf 34) 34 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e34_15_4 : check (edgeOf 34) 31 ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e34_15_5 : check (edgeOf 34) 31 ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e34_15_6 : check (edgeOf 34) 32 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e34_15_7 : check (edgeOf 34) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
