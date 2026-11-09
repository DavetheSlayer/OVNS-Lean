import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e1_139_0 : check (edgeOf 1) 33 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_139_1 : check (edgeOf 1) 32 ⟨(5 / 8 : ℚ), (21 / 32 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_139_2 : check (edgeOf 1) 32 ⟨(21 / 32 : ℚ), (11 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_139_3 : check (edgeOf 1) 32 ⟨(11 / 16 : ℚ), (23 / 32 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_139_4 : check (edgeOf 1) 32 ⟨(23 / 32 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_139_5 : check (edgeOf 1) 32 ⟨(11 / 16 : ℚ), (23 / 32 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_139_6 : check (edgeOf 1) 32 ⟨(23 / 32 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e1_139_7 : check (edgeOf 1) 33 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
