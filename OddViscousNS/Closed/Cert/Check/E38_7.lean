import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e38_7_0 : check (edgeOf 38) 30 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node .leaf .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node .leaf .leaf) .leaf)) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e38_7_1 : check (edgeOf 38) 31 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e38_7_2 : check (edgeOf 38) 32 ⟨(0 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) .leaf)) (by decide +kernel) (by decide)

theorem e38_7_3 : check (edgeOf 38) 32 ⟨(1 / 32 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf)) .leaf)) (by decide +kernel) (by decide)

theorem e38_7_4 : check (edgeOf 38) 33 ⟨(0 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node (.node .leaf .leaf) .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e38_7_5 : check (edgeOf 38) 33 ⟨(0 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e38_7_6 : check (edgeOf 38) 29 ⟨(1 / 16 : ℚ), (5 / 64 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (21 / 32 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node .leaf .leaf) .leaf))) (by decide +kernel) (by decide)

theorem e38_7_7 : check (edgeOf 38) 29 ⟨(5 / 64 : ℚ), (3 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (21 / 32 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node .leaf .leaf))) (by decide +kernel) (by decide)

end OVNS.Cert
