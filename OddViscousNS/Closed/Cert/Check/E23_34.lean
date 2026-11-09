import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e23_34_0 : check (edgeOf 23) 38 ⟨(7 / 8 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_34_1 : check (edgeOf 23) 38 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_34_2 : check (edgeOf 23) 38 ⟨(7 / 8 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_34_3 : check (edgeOf 23) 39 ⟨(3 / 4 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_34_4 : check (edgeOf 23) 41 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_34_5 : check (edgeOf 23) 41 ⟨(3 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_34_6 : check (edgeOf 23) 40 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e23_34_7 : check (edgeOf 23) 40 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
