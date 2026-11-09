import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_92_0 : check (edgeOf 0) 36 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_92_1 : check (edgeOf 0) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_92_2 : check (edgeOf 0) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_92_3 : check (edgeOf 0) 34 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_92_4 : check (edgeOf 0) 34 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_92_5 : check (edgeOf 0) 34 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_92_6 : check (edgeOf 0) 36 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_92_7 : check (edgeOf 0) 35 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
