import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e8_62_0 : check (edgeOf 8) 32 ⟨(29 / 32 : ℚ), (15 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_62_1 : check (edgeOf 8) 32 ⟨(7 / 8 : ℚ), (29 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_62_2 : check (edgeOf 8) 32 ⟨(29 / 32 : ℚ), (15 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_62_3 : check (edgeOf 8) 33 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_62_4 : check (edgeOf 8) 33 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_62_5 : check (edgeOf 8) 32 ⟨(15 / 16 : ℚ), (31 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_62_6 : check (edgeOf 8) 32 ⟨(31 / 32 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e8_62_7 : check (edgeOf 8) 32 ⟨(15 / 16 : ℚ), (31 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
