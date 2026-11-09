import OddViscousNS.Closed.Forced.Defs

/-!
# Exact rational checker for the forced face certificates (F662 rows and kind-0 faces)

A **support witness** `Supp` `(r, m, H, ε, c, M, J₀)` certifies hypothesis (S) of the support lemma,
`G(j) := ε((r + m h(j))/j)² − r j − mH j h(j) + c h(j) ≤ M` for every `j ≥ 1`: directly for
`1 ≤ j ≤ J₀` and by the affine-tail monotonicity (`support_of_finite`) beyond `J₀ ≥ 33`.

A **slope face** `SFace` is the cell `B ≤ Y ≤ B + Δ`, `X = E − m(Y − B)` (`Δ = 1/1000`) with the
whole-cubic heat `H = 1 − k q`, `q ≥ √(B+Δ)`, and the margin
`−max(−cB + ME, −c(B+Δ) + M(E − mΔ)) − f₀²/(4ε) > 0`.  A **kinetic face** `KFace` is a zero-slope
cell with `B − f₀ q_E > 0`, `q_E ≥ √E`.  The **terminal** is the face `Y = Y*`, `0 ≤ X ≤ E*` with the
pure-`Y` support (`r = 0`, `m = 1`) and margin `cY* − max(0,M)E* − f₀²/(4ε) > 0`.

All quantities are exact rationals; the checks are `Bool`s evaluated by `decide +kernel`.
-/

namespace OVNS

namespace Forced

namespace Chk

/-- `h(j)` as a rational. -/
def hq (j : ℕ) : ℚ :=
  if j = 0 then 0 else if j ≤ 32 then (hmetTable.getD (j - 1) 0 : ℚ) / 1000
  else 29 * (j : ℚ) / 100 + 117 / 500

/-- The shell function with the `c h(j)` term: `G(j) = F(j) + c h(j)`. -/
def Gq (r m H ε c : ℚ) (j : ℕ) : ℚ :=
  ε * ((r + m * hq j) / j) ^ 2 - r * j - m * H * j * hq j + c * hq j

/-- A support witness. -/
structure Supp where
  (r m H ε c M : ℚ)
  (J0 : ℕ)

/-- The support check: signs, tail condition, and the direct shell inequalities `1 ≤ j ≤ J₀`. -/
def Supp.ok (w : Supp) : Bool :=
  decide (0 ≤ w.r) && decide (0 ≤ w.m) && decide (0 < w.ε) && decide (0 < w.m * w.H) &&
  decide (33 ≤ w.J0) &&
  decide (w.c * (29 / 100) - w.m * w.H * (117 / 500) - w.r
    - w.m * w.H * (29 / 100) * (2 * (w.J0 : ℚ) + 1) ≤ 0) &&
  (List.range w.J0).all fun j => decide (Gq w.r w.m w.H w.ε w.c (j + 1) ≤ w.M)

/-- A slope face: cell data `(B, E, m)`, the root bound `q ≥ √(B+Δ)`, the heat `H = 1 − k q`,
and its support witness. -/
structure SFace where
  (B E m q H : ℚ)
  (sp : Supp)

/-- The slope-face check for the row `(k, f₀)`. -/
def SFace.ok (k f0 : ℚ) (F : SFace) : Bool :=
  decide (0 ≤ F.q) && decide (F.B + 1 / 1000 ≤ F.q ^ 2) && decide (F.H = 1 - k * F.q) &&
  decide (0 ≤ F.m) && decide (F.sp.r = 1) && decide (F.sp.m = F.m) && decide (F.sp.H = F.H) &&
  F.sp.ok &&
  decide (0 < -(max (-F.sp.c * F.B + F.sp.M * F.E)
    (-F.sp.c * (F.B + 1 / 1000) + F.sp.M * (F.E - F.m * (1 / 1000)))) - f0 ^ 2 / (4 * F.sp.ε))

/-- A kinetic (zero-slope) face: `X = E`, `Y ≥ B`, root bound `qE ≥ √E`. -/
structure KFace where
  (B E qE : ℚ)

def KFace.ok (f0 : ℚ) (F : KFace) : Bool :=
  decide (0 ≤ F.qE) && decide (F.E ≤ F.qE ^ 2) && decide (0 < F.B - f0 * F.qE)

/-- The terminal face `Y = Y*`, `0 ≤ X ≤ E*`, heat `H = 1 − k q` with `q ≥ √Y*`. -/
structure Term where
  (Y E q H : ℚ)
  (sp : Supp)

def Term.ok (k f0 : ℚ) (t : Term) : Bool :=
  decide (0 ≤ t.q) && decide (t.Y ≤ t.q ^ 2) && decide (t.H = 1 - k * t.q) && decide (0 < t.H) &&
  decide (t.sp.r = 0) && decide (t.sp.m = 1) && decide (t.sp.H = t.H) && t.sp.ok &&
  decide (0 < t.sp.c * t.Y - max 0 t.sp.M * t.E - f0 ^ 2 / (4 * t.sp.ε))

/-- A cell of a row: a slope face or a kinetic face. -/
inductive Cell where
  | slope (F : SFace)
  | kin (F : KFace)

def Cell.B : Cell → ℚ
  | .slope F => F.B
  | .kin F => F.B

def Cell.E : Cell → ℚ
  | .slope F => F.E
  | .kin F => F.E

def Cell.m : Cell → ℚ
  | .slope F => F.m
  | .kin _ => 0

def Cell.ok (k f0 : ℚ) : Cell → Bool
  | .slope F => F.ok k f0
  | .kin F => F.ok f0

/-- The chain `B_i = 1 + i/1000`, `E₀ = 1`, `E_{i+1} = E_i − m_i/1000 > 0`, ending at the terminal. -/
def chainOk : ℚ → ℚ → List Cell → Term → Bool
  | B, E, [], t => decide (t.Y = B) && decide (t.E = E) && decide (0 < E)
  | B, E, C :: rest, t =>
    decide (C.B = B) && decide (C.E = E) && decide (0 < E) &&
      chainOk (B + 1 / 1000) (E - C.m / 1000) rest t

/-- The window check `(Y*/2 + f₀)/H* ≤ J` with the terminal heat `H*`. -/
def windowOk (f0 : ℚ) (J : ℕ) (t : Term) : Bool :=
  decide (0 < t.H) && decide ((t.Y / 2 + f0) / t.H ≤ (J : ℚ))

end Chk

end Forced

end OVNS
