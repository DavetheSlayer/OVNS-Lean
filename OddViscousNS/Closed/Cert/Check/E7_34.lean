import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e7_34_0 : check (edgeOf 7) 32 ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_34_1 : check (edgeOf 7) 32 ⟨(3 / 8 : ℚ), (13 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_34_2 : check (edgeOf 7) 32 ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_34_3 : check (edgeOf 7) 34 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_34_4 : check (edgeOf 7) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_34_5 : check (edgeOf 7) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_34_6 : check (edgeOf 7) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

theorem e7_34_7 : check (edgeOf 7) 34 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
