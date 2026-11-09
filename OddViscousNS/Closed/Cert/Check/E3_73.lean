import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e3_73_0 : check (edgeOf 3) 35 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)))) (by decide +kernel) (by decide)

theorem e3_73_1 : check (edgeOf 3) 35 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e3_73_2 : check (edgeOf 3) 35 ⟨(3 / 8 : ℚ), (7 / 16 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e3_73_3 : check (edgeOf 3) 35 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e3_73_4 : check (edgeOf 3) 36 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (7 / 8 : ℚ), (1 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) .leaf))) (by decide +kernel) (by decide)

theorem e3_73_5 : check (edgeOf 3) 39 ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf))) (by decide +kernel) (by decide)

theorem e3_73_6 : check (edgeOf 3) 39 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))))) (by decide +kernel) (by decide)

theorem e3_73_7 : check (edgeOf 3) 36 ⟨(1 / 2 : ℚ), (5 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))))) (by decide +kernel) (by decide)

end OVNS.Cert
