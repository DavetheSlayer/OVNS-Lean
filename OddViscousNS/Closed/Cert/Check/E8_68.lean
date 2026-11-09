import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e8_68_0 : check (edgeOf 8) 39 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_68_1 : check (edgeOf 8) 38 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_68_2 : check (edgeOf 8) 38 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_68_3 : check (edgeOf 8) 39 ⟨(3 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_68_4 : check (edgeOf 8) 37 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_68_5 : check (edgeOf 8) 37 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_68_6 : check (edgeOf 8) 37 ⟨(7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_68_7 : check (edgeOf 8) 37 ⟨(7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
