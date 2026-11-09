import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_86_0 : check (edgeOf 1) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_86_1 : check (edgeOf 1) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_86_2 : check (edgeOf 1) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_86_3 : check (edgeOf 1) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_86_4 : check (edgeOf 1) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_86_5 : check (edgeOf 1) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_86_6 : check (edgeOf 1) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_86_7 : check (edgeOf 1) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
