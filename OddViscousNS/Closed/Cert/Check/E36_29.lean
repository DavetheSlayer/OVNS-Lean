import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e36_29_0 : check (edgeOf 36) 34 ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)) (.node (.node (.node .leaf .leaf) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e36_29_1 : check (edgeOf 36) 32 ⟨(11 / 16 : ℚ), (23 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)))) (by decide +kernel) (by decide)

theorem e36_29_2 : check (edgeOf 36) 32 ⟨(23 / 32 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)))) (by decide +kernel) (by decide)

theorem e36_29_3 : check (edgeOf 36) 32 ⟨(11 / 16 : ℚ), (23 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e36_29_4 : check (edgeOf 36) 32 ⟨(23 / 32 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e36_29_5 : check (edgeOf 36) 34 ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node .leaf .leaf))) (.node .leaf .leaf)) (.node (.node .leaf (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e36_29_6 : check (edgeOf 36) 32 ⟨(5 / 8 : ℚ), (21 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)))) (by decide +kernel) (by decide)

theorem e36_29_7 : check (edgeOf 36) 32 ⟨(21 / 32 : ℚ), (11 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)))) (by decide +kernel) (by decide)

end OVNS.Cert
