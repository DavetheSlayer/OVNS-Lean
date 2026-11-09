import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e4_107_0 : check (edgeOf 4) 36 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_107_1 : check (edgeOf 4) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_107_2 : check (edgeOf 4) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_107_3 : check (edgeOf 4) 36 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_107_4 : check (edgeOf 4) 35 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_107_5 : check (edgeOf 4) 35 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_107_6 : check (edgeOf 4) 36 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_107_7 : check (edgeOf 4) 35 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
