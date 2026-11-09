import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e26_30_0 : check (edgeOf 26) 32 ⟨(7 / 8 : ℚ), (29 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e26_30_1 : check (edgeOf 26) 32 ⟨(29 / 32 : ℚ), (15 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e26_30_2 : check (edgeOf 26) 33 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e26_30_3 : check (edgeOf 26) 34 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e26_30_4 : check (edgeOf 26) 32 ⟨(15 / 16 : ℚ), (31 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e26_30_5 : check (edgeOf 26) 32 ⟨(31 / 32 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e26_30_6 : check (edgeOf 26) 33 ⟨(15 / 16 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e26_30_7 : check (edgeOf 26) 34 ⟨(15 / 16 : ℚ), (1 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
