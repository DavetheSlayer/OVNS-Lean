import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e4_60_0 : check (edgeOf 4) 35 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_60_1 : check (edgeOf 4) 36 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_60_2 : check (edgeOf 4) 35 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_60_3 : check (edgeOf 4) 35 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_60_4 : check (edgeOf 4) 36 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_60_5 : check (edgeOf 4) 39 ⟨(0 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_60_6 : check (edgeOf 4) 35 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e4_60_7 : check (edgeOf 4) 35 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
