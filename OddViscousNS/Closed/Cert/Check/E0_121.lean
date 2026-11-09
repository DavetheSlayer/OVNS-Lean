import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_121_0 : check (edgeOf 0) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (7 / 8 : ℚ), (15 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_121_1 : check (edgeOf 0) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (7 / 8 : ℚ), (15 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_121_2 : check (edgeOf 0) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (7 / 8 : ℚ), (15 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_121_3 : check (edgeOf 0) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (7 / 8 : ℚ), (15 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_121_4 : check (edgeOf 0) 34 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (15 / 16 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_121_5 : check (edgeOf 0) 35 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_121_6 : check (edgeOf 0) 35 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_121_7 : check (edgeOf 0) 37 ⟨(0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
