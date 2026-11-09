import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e40_5_0 : check (edgeOf 40) 29 ⟨(7 / 64 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) .leaf)) (by decide +kernel) (by decide)

theorem e40_5_1 : check (edgeOf 40) 31 ⟨(3 / 32 : ℚ), (1 / 8 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e40_5_2 : check (edgeOf 40) 34 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e40_5_3 : check (edgeOf 40) 30 ⟨(0 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (21 / 32 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e40_5_4 : check (edgeOf 40) 30 ⟨(0 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) .leaf) (.node .leaf .leaf)) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e40_5_5 : check (edgeOf 40) 31 ⟨(0 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e40_5_6 : check (edgeOf 40) 30 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (21 / 32 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e40_5_7 : check (edgeOf 40) 30 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) .leaf) (.node .leaf .leaf)) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

end OVNS.Cert
