import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e10_39_0 : check (edgeOf 10) 35 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_39_1 : check (edgeOf 10) 35 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_39_2 : check (edgeOf 10) 36 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_39_3 : check (edgeOf 10) 36 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_39_4 : check (edgeOf 10) 39 ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_39_5 : check (edgeOf 10) 36 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_39_6 : check (edgeOf 10) 35 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e10_39_7 : check (edgeOf 10) 35 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
