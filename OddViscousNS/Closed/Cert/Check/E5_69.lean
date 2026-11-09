import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e5_69_0 : check (edgeOf 5) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_69_1 : check (edgeOf 5) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_69_2 : check (edgeOf 5) 33 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_69_3 : check (edgeOf 5) 33 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_69_4 : check (edgeOf 5) 34 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_69_5 : check (edgeOf 5) 34 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_69_6 : check (edgeOf 5) 34 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_69_7 : check (edgeOf 5) 34 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
