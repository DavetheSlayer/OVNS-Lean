import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e3_52_0 : check (edgeOf 3) 32 ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e3_52_1 : check (edgeOf 3) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e3_52_2 : check (edgeOf 3) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf))) (by decide +kernel) (by decide)

theorem e3_52_3 : check (edgeOf 3) 33 ⟨(7 / 16 : ℚ), (1 / 2 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e3_52_4 : check (edgeOf 3) 37 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf))) .leaf) (by decide +kernel) (by decide)

theorem e3_52_5 : check (edgeOf 3) 37 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf))) .leaf) (by decide +kernel) (by decide)

theorem e3_52_6 : check (edgeOf 3) 37 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf))) .leaf) (by decide +kernel) (by decide)

theorem e3_52_7 : check (edgeOf 3) 37 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf))) .leaf) (by decide +kernel) (by decide)

end OVNS.Cert
