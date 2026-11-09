import OddViscousNS.Closed.Cert.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OVNS.Cert

theorem e5_62_0 : check (edgeOf 5) 35 ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e5_62_1 : check (edgeOf 5) 36 ⟨(7 / 8 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))))) (by decide +kernel) (by decide)

theorem e5_62_2 : check (edgeOf 5) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) (.node (.node .leaf .leaf) .leaf))) (.node .leaf .leaf)) (.node (.node .leaf (.node (.node (.node .leaf .leaf) .leaf) .leaf)) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e5_62_3 : check (edgeOf 5) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e5_62_4 : check (edgeOf 5) 36 ⟨(7 / 8 : ℚ), (1 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))))) (by decide +kernel) (by decide)

theorem e5_62_5 : check (edgeOf 5) 35 ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e5_62_6 : check (edgeOf 5) 35 ⟨(15 / 16 : ℚ), (1 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))) (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (by decide +kernel) (by decide)

theorem e5_62_7 : check (edgeOf 5) 39 ⟨(3 / 4 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩ = true :=
  Fast.check_of_trN (by decide) (.node (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf))))) (.node (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))) (.node .leaf (.node (.node (.node .leaf .leaf) (.node .leaf .leaf)) (.node (.node .leaf .leaf) (.node .leaf .leaf)))))) (by decide +kernel) (by decide)

end OVNS.Cert
