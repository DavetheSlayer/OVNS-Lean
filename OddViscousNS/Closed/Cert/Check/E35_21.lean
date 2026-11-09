import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e35_21_0 : check (edgeOf 35) 37 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_21_1 : check (edgeOf 35) 38 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_21_2 : check (edgeOf 35) 38 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_21_3 : check (edgeOf 35) 39 ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_21_4 : check (edgeOf 35) 42 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_21_5 : check (edgeOf 35) 41 ⟨(0 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_21_6 : check (edgeOf 35) 41 ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e35_21_7 : check (edgeOf 35) 39 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
