import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e16_27_0 : check (edgeOf 16) 37 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf)) (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e16_27_1 : check (edgeOf 16) 37 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e16_27_2 : check (edgeOf 16) 37 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf)) (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e16_27_3 : check (edgeOf 16) 37 ⟨(5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e16_27_4 : check (edgeOf 16) 39 ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e16_27_5 : check (edgeOf 16) 36 ⟨(3 / 4 : ℚ), (7 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e16_27_6 : check (edgeOf 16) 35 ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e16_27_7 : check (edgeOf 16) 35 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

end OVNS.Cert
