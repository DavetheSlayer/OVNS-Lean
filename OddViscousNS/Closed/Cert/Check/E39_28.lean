import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e39_28_0 : check (edgeOf 39) 34 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_28_1 : check (edgeOf 39) 35 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_28_2 : check (edgeOf 39) 35 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_28_3 : check (edgeOf 39) 35 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_28_4 : check (edgeOf 39) 35 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_28_5 : check (edgeOf 39) 36 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_28_6 : check (edgeOf 39) 36 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e39_28_7 : check (edgeOf 39) 37 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
