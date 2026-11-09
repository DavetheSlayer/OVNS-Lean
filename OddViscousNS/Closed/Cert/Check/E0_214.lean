import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_214_0 : check (edgeOf 0) 34 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_214_1 : check (edgeOf 0) 35 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_214_2 : check (edgeOf 0) 35 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_214_3 : check (edgeOf 0) 35 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_214_4 : check (edgeOf 0) 35 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_214_5 : check (edgeOf 0) 35 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_214_6 : check (edgeOf 0) 35 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_214_7 : check (edgeOf 0) 37 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
