import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e38_9_0 : check (edgeOf 38) 34 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_9_1 : check (edgeOf 38) 35 ⟨(0 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_9_2 : check (edgeOf 38) 35 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_9_3 : check (edgeOf 38) 35 ⟨(0 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_9_4 : check (edgeOf 38) 35 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_9_5 : check (edgeOf 38) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_9_6 : check (edgeOf 38) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_9_7 : check (edgeOf 38) 30 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (19 / 32 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
