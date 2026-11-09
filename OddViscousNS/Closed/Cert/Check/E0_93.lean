import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_93_0 : check (edgeOf 0) 35 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_93_1 : check (edgeOf 0) 39 ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_93_2 : check (edgeOf 0) 36 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_93_3 : check (edgeOf 0) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_93_4 : check (edgeOf 0) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_93_5 : check (edgeOf 0) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_93_6 : check (edgeOf 0) 33 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_93_7 : check (edgeOf 0) 33 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
