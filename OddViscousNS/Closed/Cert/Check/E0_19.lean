import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e0_19_0 : check (edgeOf 0) 32 ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_19_1 : check (edgeOf 0) 33 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_19_2 : check (edgeOf 0) 32 ⟨(3 / 8 : ℚ), (13 / 32 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_19_3 : check (edgeOf 0) 32 ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_19_4 : check (edgeOf 0) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_19_5 : check (edgeOf 0) 32 ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_19_6 : check (edgeOf 0) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e0_19_7 : check (edgeOf 0) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
