import OddViscousNS.Closed.Forced.Check.Defs

/-!
# Exact rational checker for the common forced row (`k = .8393`, `f₀ = 1`)

Cells are kind-0 slope faces (`SFace`), strict kinetic faces (`KFace`), plateau kinetic faces
`kin1` (`E = 1`, covered by the a-priori bound `X ≤ s²`), and **moment faces** `MFace`: the cell
`(B, E, m)` with `U ≥ √(B+Δ)` and a list of `t`-regimes `(t_lo, t_hi]` covering `(0, ∞)`; in a
regime with coefficient `c ∈ {.41034 (t ≤ .020), .4137 (.020 < t ≤ .030), κ₀}` the heat is
`H_act = 1 − s c U`, a trial heat `H > 0` is used with the debit `δ = m (H − H_act)₊/t_lo`
(`δ = 0`, `H = H_act` when `t_lo = 0`), and the support test runs with the shifted coefficient
`c' = c − δ`.  The terminal `MTerm` has regimes covering `(0, τ]` with the late exclusion
`1/τ ≤ ℓ − c_ℓ E*/Y*`; a regime is tested either by the scalar test (`H Y*/t_hi − f₀ q_E > 0`) or by a
pure-`Y` support.  The window data `Win` carries the three heats and the debit slope `D_q` with
`(Y*/2 + f₀ + D_q Y*)/H_s ≤ J`.
-/

namespace OVNS

namespace Forced

namespace Com

open Chk

/-- The moment coefficients of the face regimes. -/
inductive Coef where
  | small
  | aligned
  | kappa

/-- Their values `.41034`, `.4137`, `κ₀`. -/
def Coef.val : Coef → ℚ
  | .small => 20517 / 50000
  | .aligned => 4137 / 10000
  | .kappa => 208013 / 500000

/-- A face regime `(t_lo, t_hi]` (`t_hi = none`: unbounded). -/
structure MRegime where
  (tlo : ℚ)
  (thi : Option ℚ)
  (coef : Coef)
  (H δ : ℚ)
  (sp : Supp)

/-- The coefficient is valid on the regime. -/
def MRegime.domOk (R : MRegime) : Bool :=
  match R.coef, R.thi with
  | .small, some h => decide (h ≤ 1 / 50)
  | .small, none => false
  | .aligned, some h => decide (1 / 50 ≤ R.tlo) && decide (h ≤ 3 / 100)
  | .aligned, none => false
  | .kappa, _ => true

/-- The regime check on the face `(B, E, m)` with root bound `U`, scale `s`, force cap `f₀`. -/
def MRegime.ok (s f0 B E m U : ℚ) (R : MRegime) : Bool :=
  R.domOk && decide (0 ≤ R.tlo) && decide (0 < R.H) && decide (R.sp.r = 1) &&
  decide (R.sp.m = m) && decide (R.sp.H = R.H) && R.sp.ok &&
  (if R.tlo = 0 then decide (R.H = 1 - s * R.coef.val * U) && decide (R.δ = 0)
    else decide (R.δ = m * max 0 (R.H - (1 - s * R.coef.val * U)) / R.tlo)) &&
  decide (0 < -(max (-(R.sp.c - R.δ) * B + R.sp.M * E)
    (-(R.sp.c - R.δ) * (B + 1 / 1000) + R.sp.M * (E - m / 1000))) - f0 ^ 2 / (4 * R.sp.ε))

/-- Consecutive coverage of `(t, ∞)` by the regimes. -/
def coverOk : ℚ → List MRegime → Bool
  | _, [] => false
  | t, R :: rest => decide (R.tlo = t) &&
      (match R.thi with
       | none => rest.isEmpty
       | some h => decide (t < h) && coverOk h rest)

/-- A moment face. -/
structure MFace where
  (B E m U : ℚ)
  (regs : List MRegime)

def MFace.ok (s f0 : ℚ) (F : MFace) : Bool :=
  decide (0 ≤ F.U) && decide (F.B + 1 / 1000 ≤ F.U ^ 2) && decide (0 < F.m) && coverOk 0 F.regs &&
  F.regs.all (MRegime.ok s f0 F.B F.E F.m F.U)

/-- Terminal coefficients: `.41034`, or a rational upper bound `c` of `c_f(E*/Y*)`. -/
inductive TCoef where
  | small
  | cf (c : ℚ)

def TCoef.val : TCoef → ℚ
  | .small => 20517 / 50000
  | .cf c => c

/-- Terminal tests: the scalar test with `q_E ≥ √E*`, or a pure-`Y` support. -/
inductive TTest where
  | scalar (qE : ℚ)
  | supp (sp : Supp)

/-- A terminal regime `(t_lo, t_hi]`. -/
structure TRegime where
  (tlo thi : ℚ)
  (coef : TCoef)
  (H : ℚ)
  (test : TTest)

def TRegime.ok (s f0 Y E U : ℚ) (R : TRegime) : Bool :=
  decide (R.H = 1 - s * R.coef.val * U) && decide (0 < R.H) && decide (0 ≤ R.tlo) &&
  (match R.coef with
   | .small => decide (R.thi ≤ 1 / 50)
   | .cf c => decide (1 / 50 ≤ R.tlo) && decide (R.thi ≤ 21 / 500) && decide (0 ≤ c) &&
       decide ((118 / 100 + 176 / 1000 * (E / Y)) * ((41085 / 100000) ^ 2 / (1202 / 1000)) ≤ c ^ 2)) &&
  (match R.test with
   | .scalar qE => decide (R.tlo = 0) && decide (0 ≤ qE) && decide (E ≤ qE ^ 2) &&
       decide (0 < R.H * Y / R.thi - f0 * qE)
   | .supp sp => decide (sp.r = 0) && decide (sp.m = 1) && decide (sp.H = R.H) && sp.ok &&
       decide (0 < sp.c * Y - max 0 sp.M * E - f0 ^ 2 / (4 * sp.ε)))

/-- Consecutive coverage of `(t, τ]`. -/
def tcoverOk : ℚ → ℚ → List TRegime → Bool
  | t, τ, [] => decide (t = τ)
  | t, τ, R :: rest => decide (R.tlo = t) && decide (t < R.thi) && tcoverOk R.thi τ rest

/-- The terminal face `Y = Y*`, `0 ≤ X ≤ E*`, root bound `U ≥ √Y*`, late bound `τ`. -/
structure MTerm where
  (Y E U τ : ℚ)
  (regs : List TRegime)

def MTerm.ok (s f0 : ℚ) (T : MTerm) : Bool :=
  decide (0 ≤ T.U) && decide (T.Y ≤ T.U ^ 2) && decide (0 < T.Y) && decide (0 ≤ T.E) &&
  decide (0 < T.τ) && decide (1 / T.τ ≤ 13191 / 212 - 63940773 / 212000 * (T.E / T.Y)) &&
  tcoverOk 0 T.τ T.regs && T.regs.all (TRegime.ok s f0 T.Y T.E T.U)

/-- Window data: the three regime heats and the debit slope `D_q` (`D* = D_q Y*`). -/
structure Win where
  (Hs Hm Hg Dq : ℚ)

def Win.ok (s f0 : ℚ) (J : ℕ) (T : MTerm) (W : Win) : Bool :=
  decide (W.Hs = 1 - s * (20517 / 50000) * T.U) && decide (W.Hm = 1 - s * (4137 / 10000) * T.U) &&
  decide (W.Hg = 1 - s * (208013 / 500000) * T.U) && decide (0 < W.Hs) && decide (0 ≤ W.Dq) &&
  decide ((W.Hs - W.Hm) / (1 / 50) ≤ W.Dq) && decide ((W.Hs - W.Hg) / (3 / 100) ≤ W.Dq) &&
  decide ((T.Y / 2 + f0 + W.Dq * T.Y) / W.Hs ≤ (J : ℚ))

/-- A cell of the common row. -/
inductive CCell where
  | slope (F : SFace)
  | kin (F : KFace)
  | kin1 (B : ℚ)
  | mom (F : MFace)

def CCell.B : CCell → ℚ
  | .slope F => F.B
  | .kin F => F.B
  | .kin1 B => B
  | .mom F => F.B

def CCell.E : CCell → ℚ
  | .slope F => F.E
  | .kin F => F.E
  | .kin1 _ => 1
  | .mom F => F.E

def CCell.m : CCell → ℚ
  | .slope F => F.m
  | .kin _ => 0
  | .kin1 _ => 0
  | .mom F => F.m

def CCell.ok (k f0 s : ℚ) : CCell → Bool
  | .slope F => F.ok k f0
  | .kin F => F.ok f0
  | .kin1 _ => true
  | .mom F => F.ok s f0

/-- The chain `B_i = 1 + i/1000`, `E₀ = 1`, `E_{i+1} = E_i − m_i/1000 > 0`, ending at the terminal. -/
def cchainOk : ℚ → ℚ → List CCell → MTerm → Bool
  | B, E, [], T => decide (T.Y = B) && decide (T.E = E) && decide (0 < E)
  | B, E, C :: rest, T =>
    decide (C.B = B) && decide (C.E = E) && decide (0 < E) &&
      cchainOk (B + 1 / 1000) (E - C.m / 1000) rest T

end Com

end Forced

end OVNS
