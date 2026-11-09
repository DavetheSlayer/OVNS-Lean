import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_69_0 : check (edgeOf 1) 32 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_69_1 : check (edgeOf 1) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_69_2 : check (edgeOf 1) 32 ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_69_3 : check (edgeOf 1) 32 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_69_4 : check (edgeOf 1) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_69_5 : check (edgeOf 1) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_69_6 : check (edgeOf 1) 32 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_69_7 : check (edgeOf 1) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
