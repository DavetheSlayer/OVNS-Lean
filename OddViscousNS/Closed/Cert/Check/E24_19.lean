import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e24_19_0 : check (edgeOf 24) 36 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e24_19_1 : check (edgeOf 24) 35 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e24_19_2 : check (edgeOf 24) 35 ⟨(9 / 16 : ℚ), (5 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e24_19_3 : check (edgeOf 24) 37 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e24_19_4 : check (edgeOf 24) 36 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e24_19_5 : check (edgeOf 24) 35 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e24_19_6 : check (edgeOf 24) 35 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e24_19_7 : check (edgeOf 24) 37 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
