import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_117_0 : check (edgeOf 0) 32 ⟨(1 / 16 : ℚ), (3 / 32 : ℚ), (7 / 8 : ℚ), (15 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_117_1 : check (edgeOf 0) 32 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (7 / 8 : ℚ), (15 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_117_2 : check (edgeOf 0) 34 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (15 / 16 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_117_3 : check (edgeOf 0) 35 ⟨(0 : ℚ), (1 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_117_4 : check (edgeOf 0) 35 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_117_5 : check (edgeOf 0) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_117_6 : check (edgeOf 0) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_117_7 : check (edgeOf 0) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
