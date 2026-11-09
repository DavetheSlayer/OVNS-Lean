import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e2_62_0 : check (edgeOf 2) 32 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_62_1 : check (edgeOf 2) 32 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_62_2 : check (edgeOf 2) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_62_3 : check (edgeOf 2) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_62_4 : check (edgeOf 2) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 16 : ℚ), (3 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_62_5 : check (edgeOf 2) 32 ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_62_6 : check (edgeOf 2) 32 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e2_62_7 : check (edgeOf 2) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (5 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
