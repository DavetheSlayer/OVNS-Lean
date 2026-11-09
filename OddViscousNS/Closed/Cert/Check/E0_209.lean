import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_209_0 : check (edgeOf 0) 32 ⟨(5 / 8 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_209_1 : check (edgeOf 0) 32 ⟨(21 / 32 : ℚ), (11 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_209_2 : check (edgeOf 0) 32 ⟨(5 / 8 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_209_3 : check (edgeOf 0) 32 ⟨(21 / 32 : ℚ), (11 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_209_4 : check (edgeOf 0) 32 ⟨(11 / 16 : ℚ), (23 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_209_5 : check (edgeOf 0) 32 ⟨(23 / 32 : ℚ), (3 / 4 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_209_6 : check (edgeOf 0) 32 ⟨(11 / 16 : ℚ), (23 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_209_7 : check (edgeOf 0) 32 ⟨(23 / 32 : ℚ), (3 / 4 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
