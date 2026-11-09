import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e11_24_0 : check (edgeOf 11) 32 ⟨(3 / 8 : ℚ), (13 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e11_24_1 : check (edgeOf 11) 32 ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e11_24_2 : check (edgeOf 11) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e11_24_3 : check (edgeOf 11) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e11_24_4 : check (edgeOf 11) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e11_24_5 : check (edgeOf 11) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e11_24_6 : check (edgeOf 11) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e11_24_7 : check (edgeOf 11) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
