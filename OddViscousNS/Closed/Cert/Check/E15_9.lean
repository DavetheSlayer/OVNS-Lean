import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e15_9_0 : check (edgeOf 15) 32 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e15_9_1 : check (edgeOf 15) 33 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e15_9_2 : check (edgeOf 15) 35 ⟨(0 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e15_9_3 : check (edgeOf 15) 35 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e15_9_4 : check (edgeOf 15) 35 ⟨(0 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e15_9_5 : check (edgeOf 15) 35 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e15_9_6 : check (edgeOf 15) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e15_9_7 : check (edgeOf 15) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
