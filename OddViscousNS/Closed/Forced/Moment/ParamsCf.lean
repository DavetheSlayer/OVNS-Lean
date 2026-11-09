import OddViscousNS.Closed.Forced.Moment.PairCheck

namespace OVNS.Forced.Mom

/-- Parameters of the `c_f` row (`a = .18`, `bL = .022·8`, `λ = .031`, `K = .41085²/1.202`,
`W ∈ [1/4, 2]`, `.020 < t ≤ .042`, `J < 800`). -/
def PCf : Params := ⟨(9 / 50 : ℚ), (22 / 125 : ℚ), (31 / 1000 : ℚ), (67519089 / 480800000 : ℚ), (1 / 4 : ℚ), (2 : ℚ), (1 / 50 : ℚ), (21 / 500 : ℚ), 800, 16⟩

end OVNS.Forced.Mom
