import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e38_23_0 : check (edgeOf 38) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_23_1 : check (edgeOf 38) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_23_2 : check (edgeOf 38) 30 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (19 / 32 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_23_3 : check (edgeOf 38) 30 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_23_4 : check (edgeOf 38) 31 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_23_5 : check (edgeOf 38) 30 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (19 / 32 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_23_6 : check (edgeOf 38) 30 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_23_7 : check (edgeOf 38) 31 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
