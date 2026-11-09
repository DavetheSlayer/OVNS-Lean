import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e38_11_0 : check (edgeOf 38) 33 ⟨(1 / 8 : ℚ), (3 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e38_11_1 : check (edgeOf 38) 32 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e38_11_2 : check (edgeOf 38) 32 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (9 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e38_11_3 : check (edgeOf 38) 30 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (19 / 32 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node .leaf .leaf) .leaf))) (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e38_11_4 : check (edgeOf 38) 29 ⟨(3 / 16 : ℚ), (13 / 64 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)))) (by decide +kernel) (by decide)

theorem e38_11_5 : check (edgeOf 38) 29 ⟨(13 / 64 : ℚ), (7 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (19 / 32 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)))) (by decide +kernel) (by decide)

theorem e38_11_6 : check (edgeOf 38) 31 ⟨(3 / 16 : ℚ), (7 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (9 / 16 : ℚ), (5 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e38_11_7 : check (edgeOf 38) 30 ⟨(7 / 32 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (9 / 16 : ℚ), (19 / 32 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf .leaf))) (by decide +kernel) (by decide)

end OVNS.Cert
