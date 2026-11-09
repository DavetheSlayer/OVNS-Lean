import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_128_0 : check (edgeOf 0) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_128_1 : check (edgeOf 0) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_128_2 : check (edgeOf 0) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_128_3 : check (edgeOf 0) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_128_4 : check (edgeOf 0) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_128_5 : check (edgeOf 0) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_128_6 : check (edgeOf 0) 32 ⟨(3 / 8 : ℚ), (13 / 32 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_128_7 : check (edgeOf 0) 32 ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
