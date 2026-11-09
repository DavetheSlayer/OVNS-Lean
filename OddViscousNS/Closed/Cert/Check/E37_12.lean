import OddViscousNS.Closed.Cert.Bounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e37_12_0 : check (edgeOf 37) 30 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (21 / 32 : ℚ)⟩ = true := by
  decide +kernel

theorem e37_12_1 : check (edgeOf 37) 30 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e37_12_2 : check (edgeOf 37) 31 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e37_12_3 : check (edgeOf 37) 32 ⟨(1 / 8 : ℚ), (5 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e37_12_4 : check (edgeOf 37) 32 ⟨(5 / 32 : ℚ), (3 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e37_12_5 : check (edgeOf 37) 34 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true := by
  decide +kernel

theorem e37_12_6 : check (edgeOf 37) 31 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

theorem e37_12_7 : check (edgeOf 37) 31 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true := by
  decide +kernel

end OVNS.Cert
