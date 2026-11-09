import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e20_12_0 : check (edgeOf 20) 35 ⟨(3 / 16 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e20_12_1 : check (edgeOf 20) 37 ⟨(0 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf))) .leaf) (by decide +kernel) (by decide)

theorem e20_12_2 : check (edgeOf 20) 37 ⟨(0 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) .leaf) (.node .leaf .leaf)) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) .leaf) (.node .leaf .leaf))) .leaf) (by decide +kernel) (by decide)

theorem e20_12_3 : check (edgeOf 20) 37 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf))) .leaf) (by decide +kernel) (by decide)

theorem e20_12_4 : check (edgeOf 20) 37 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) .leaf) .leaf) (.node .leaf .leaf)) (.node (.node (.node .leaf .leaf) .leaf) (.node .leaf .leaf))) .leaf) (by decide +kernel) (by decide)

theorem e20_12_5 : check (edgeOf 20) 35 ⟨(0 : ℚ), (1 / 16 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)))) (by decide +kernel) (by decide)

theorem e20_12_6 : check (edgeOf 20) 35 ⟨(1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)))) (by decide +kernel) (by decide)

theorem e20_12_7 : check (edgeOf 20) 36 ⟨(0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node .leaf .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node .leaf .leaf))) (by decide +kernel) (by decide)

end OVNS.Cert
