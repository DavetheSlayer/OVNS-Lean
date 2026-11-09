import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e30_3_0 : check (edgeOf 30) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e30_3_1 : check (edgeOf 30) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e30_3_2 : check (edgeOf 30) 31 ⟨(0 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node .leaf .leaf)) (.node (.node .leaf (.node .leaf .leaf)) (.node .leaf .leaf))) (.node (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e30_3_3 : check (edgeOf 30) 31 ⟨(0 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e30_3_4 : check (edgeOf 30) 31 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node .leaf .leaf)) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e30_3_5 : check (edgeOf 30) 31 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e30_3_6 : check (edgeOf 30) 33 ⟨(0 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node .leaf .leaf))) (.node .leaf .leaf)) (.node (.node .leaf (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e30_3_7 : check (edgeOf 30) 33 ⟨(0 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf))) (by decide +kernel) (by decide)

end OVNS.Cert
