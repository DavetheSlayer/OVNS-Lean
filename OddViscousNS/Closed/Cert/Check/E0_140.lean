import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_140_0 : check (edgeOf 0) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_140_1 : check (edgeOf 0) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_140_2 : check (edgeOf 0) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_140_3 : check (edgeOf 0) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_140_4 : check (edgeOf 0) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_140_5 : check (edgeOf 0) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_140_6 : check (edgeOf 0) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_140_7 : check (edgeOf 0) 35 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
