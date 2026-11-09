import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e2_69_0 : check (edgeOf 2) 35 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_69_1 : check (edgeOf 2) 37 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_69_2 : check (edgeOf 2) 37 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_69_3 : check (edgeOf 2) 37 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_69_4 : check (edgeOf 2) 37 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_69_5 : check (edgeOf 2) 39 ⟨(0 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_69_6 : check (edgeOf 2) 36 ⟨(0 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_69_7 : check (edgeOf 2) 35 ⟨(0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
