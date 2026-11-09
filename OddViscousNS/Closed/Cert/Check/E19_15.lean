import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e19_15_0 : check (edgeOf 19) 32 ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_15_1 : check (edgeOf 19) 32 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_15_2 : check (edgeOf 19) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_15_3 : check (edgeOf 19) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_15_4 : check (edgeOf 19) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_15_5 : check (edgeOf 19) 32 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_15_6 : check (edgeOf 19) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_15_7 : check (edgeOf 19) 34 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
