import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e19_40_0 : check (edgeOf 19) 40 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_40_1 : check (edgeOf 19) 40 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_40_2 : check (edgeOf 19) 40 ⟨(3 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_40_3 : check (edgeOf 19) 40 ⟨(3 / 4 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_40_4 : check (edgeOf 19) 38 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_40_5 : check (edgeOf 19) 38 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_40_6 : check (edgeOf 19) 39 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e19_40_7 : check (edgeOf 19) 40 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
