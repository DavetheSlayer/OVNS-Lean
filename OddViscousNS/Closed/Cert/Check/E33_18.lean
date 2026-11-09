import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e33_18_0 : check (edgeOf 33) 37 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e33_18_1 : check (edgeOf 33) 38 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e33_18_2 : check (edgeOf 33) 38 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e33_18_3 : check (edgeOf 33) 38 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e33_18_4 : check (edgeOf 33) 39 ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e33_18_5 : check (edgeOf 33) 42 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ = true := by
  decide +kernel

theorem e33_18_6 : check (edgeOf 33) 41 ⟨(0 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

theorem e33_18_7 : check (edgeOf 33) 41 ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
