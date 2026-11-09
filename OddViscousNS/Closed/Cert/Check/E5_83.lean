import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e5_83_0 : check (edgeOf 5) 32 ⟨(15 / 16 : ℚ), (31 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_83_1 : check (edgeOf 5) 32 ⟨(31 / 32 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_83_2 : check (edgeOf 5) 32 ⟨(15 / 16 : ℚ), (31 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_83_3 : check (edgeOf 5) 32 ⟨(31 / 32 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_83_4 : check (edgeOf 5) 32 ⟨(15 / 16 : ℚ), (31 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_83_5 : check (edgeOf 5) 32 ⟨(31 / 32 : ℚ), (1 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_83_6 : check (edgeOf 5) 32 ⟨(15 / 16 : ℚ), (31 / 32 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e5_83_7 : check (edgeOf 5) 32 ⟨(31 / 32 : ℚ), (1 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
