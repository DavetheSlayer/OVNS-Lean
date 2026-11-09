import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e5_68_0 : check (edgeOf 5) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_68_1 : check (edgeOf 5) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_68_2 : check (edgeOf 5) 32 ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_68_3 : check (edgeOf 5) 32 ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_68_4 : check (edgeOf 5) 33 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_68_5 : check (edgeOf 5) 33 ⟨(1 / 2 : ℚ), (9 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_68_6 : check (edgeOf 5) 32 ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_68_7 : check (edgeOf 5) 32 ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
