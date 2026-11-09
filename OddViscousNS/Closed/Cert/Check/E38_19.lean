import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e38_19_0 : check (edgeOf 38) 30 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_19_1 : check (edgeOf 38) 31 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_19_2 : check (edgeOf 38) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_19_3 : check (edgeOf 38) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_19_4 : check (edgeOf 38) 30 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (21 / 32 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_19_5 : check (edgeOf 38) 30 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_19_6 : check (edgeOf 38) 31 ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e38_19_7 : check (edgeOf 38) 31 ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
