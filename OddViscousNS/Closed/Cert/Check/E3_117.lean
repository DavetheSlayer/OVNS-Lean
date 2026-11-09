import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e3_117_0 : check (edgeOf 3) 36 ⟨(7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_117_1 : check (edgeOf 3) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_117_2 : check (edgeOf 3) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_117_3 : check (edgeOf 3) 36 ⟨(7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_117_4 : check (edgeOf 3) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_117_5 : check (edgeOf 3) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_117_6 : check (edgeOf 3) 39 ⟨(3 / 4 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e3_117_7 : check (edgeOf 3) 36 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
