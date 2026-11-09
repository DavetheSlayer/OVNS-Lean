import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e39_22_0 : check (edgeOf 39) 30 ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) .leaf) (.node .leaf .leaf)) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e39_22_1 : check (edgeOf 39) 31 ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e39_22_2 : check (edgeOf 39) 30 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (5 / 8 : ℚ), (21 / 32 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e39_22_3 : check (edgeOf 39) 30 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (21 / 32 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) .leaf) (.node .leaf .leaf)) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) .leaf) (.node .leaf .leaf))) (by decide +kernel) (by decide)

theorem e39_22_4 : check (edgeOf 39) 31 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

theorem e39_22_5 : check (edgeOf 39) 32 ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) .leaf)) (by decide +kernel) (by decide)

theorem e39_22_6 : check (edgeOf 39) 32 ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (11 / 16 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) .leaf)) (by decide +kernel) (by decide)

theorem e39_22_7 : check (edgeOf 39) 34 ⟨(5 / 16 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node .leaf .leaf)) (.node (.node (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (by decide +kernel) (by decide)

end OVNS.Cert
