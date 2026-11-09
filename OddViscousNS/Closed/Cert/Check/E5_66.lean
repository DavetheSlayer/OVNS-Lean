import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e5_66_0 : check (edgeOf 5) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_66_1 : check (edgeOf 5) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_66_2 : check (edgeOf 5) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_66_3 : check (edgeOf 5) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_66_4 : check (edgeOf 5) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_66_5 : check (edgeOf 5) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_66_6 : check (edgeOf 5) 33 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_66_7 : check (edgeOf 5) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
