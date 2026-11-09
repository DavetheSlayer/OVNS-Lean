import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e39_1_0 : check (edgeOf 39) 37 ⟨(1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)) (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e39_1_1 : check (edgeOf 39) 40 ⟨(0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node .leaf (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node .leaf .leaf))) (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e39_1_2 : check (edgeOf 39) 39 ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e39_1_3 : check (edgeOf 39) 36 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e39_1_4 : check (edgeOf 39) 35 ⟨(1 / 4 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)) (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e39_1_5 : check (edgeOf 39) 35 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)) (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e39_1_6 : check (edgeOf 39) 37 ⟨(1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)) (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e39_1_7 : check (edgeOf 39) 36 ⟨(3 / 8 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

end OVNS.Cert
