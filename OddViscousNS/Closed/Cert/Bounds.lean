import OddViscousNS.Closed.Plan
import OddViscousNS.Closed.Cond.Defs

/-!
# The directed cube certificate (U785): exact rational bounds and the bisection checker

An exact transcription of `U785_separate_piecewise_barrier_replay.py` (§5 of the reconstruction).
For an edge `(x_h, y_h, m, width)` and a closed box `[u₋,u₊]×[p₋,p₊]×[v₋,v₊] ⊆ [0,1]³`, `gap`
computes the directed heat lower bound `1 − m K₊ − s √↑Y₊ C₊`; a box is accepted when
`gap > 10⁻⁵`, otherwise it is bisected along the first longest side.  `check e fuel b = true`
means that the whole tree below `b` is accepted within `fuel` levels.
-/

namespace OVNS

namespace Cert

def h2q : ℚ := 1569 / 1000
def h3q : ℚ := 1021 / 500
def Dq : ℚ := h2q * h3q / (h3q - h2q)
def Cq : ℚ := 2 + Dq / h2q
def Lq : ℚ := 1 - Cq + Dq
def βq : ℚ := 2 * (1 - h2q / h3q)
def a0q : ℚ := 29 / 100
def aq : ℚ := 11 / 60
def sq : ℚ := 97 / 40
def κq : ℚ := 208013 / 500000
def εq : ℚ := 1 / 100000
def gramq : ℚ := 185955292 / 1000000000

/-- The upward square root on the `10⁻¹²` grid: the least `N/10¹²` with `(N/10¹²)² ≥ v`
(`0` for `v ≤ 0`). -/
def usqrt (v : ℚ) : ℚ :=
  if v ≤ 0 then 0 else
    ((Nat.sqrt ((v.num.toNat * 10 ^ 24 - 1) / v.den) + 1 : ℕ) : ℚ) / 10 ^ 12

/-- `c₁⁺ = (h₂ − 1) √↑(1/(3h₂))`. -/
def c1q : ℚ := (h2q - 1) * usqrt (1 / (3 * h2q))

/-- An edge of the plan: right knot `(x_h, y_h)`, slope `m`, width. -/
structure Edge where
  (xh yh m width : ℚ)

def Edge.xl (e : Edge) : ℚ := e.xh - e.width
def Edge.yl (e : Edge) : ℚ := e.yh - e.m * e.width

/-- `X(u)`, `Y(u)` along the edge (`u = 0` at the left knot). -/
def Edge.X (e : Edge) (u : ℚ) : ℚ := e.xl + (e.xh - e.xl) * u
def Edge.Y (e : Edge) (u : ℚ) : ℚ := e.yl + (e.yh - e.yl) * u
def Edge.z (e : Edge) (u : ℚ) : ℚ := e.X u / e.Y u

/-- `ρ_min(z) = [(h₂z − 1)/(h₂ − 1)]₊`. -/
def lowerQ (z : ℚ) : ℚ := max 0 ((h2q * z - 1) / (h2q - 1))

/-- `ρ(u,p) = (1−p) ρ_min(z(u)) + p z(u)`. -/
def Edge.ρ (e : Edge) (u p : ℚ) : ℚ := (1 - p) * lowerQ (e.z u) + p * e.z u

/-- A closed box in the parameters `(u, p, v)`. -/
structure Box where
  (ul uh pl ph vl vh : ℚ)
  deriving DecidableEq

def Box.root : Box := ⟨0, 1, 0, 1, 0, 1⟩

/-- `G(m, w)` with the certificate's zero conventions. -/
def Gq (m w : ℚ) : ℚ :=
  m / 2 + (if m ≠ 0 ∧ w ≠ 0 then m * w / (2 * (w + 4 * aq * m)) else 0)

/-- The directed heat lower bound on a box. -/
def gap (e : Edge) (b : Box) : ℚ :=
  let zl := e.z b.ul
  let rl := e.ρ b.ul b.pl
  let zh := e.z b.uh
  let rh := e.ρ b.uh b.ph
  let dl := max 1 (Cq - Dq * zh + Lq * rl)
  let dh := Cq - Dq * zl + Lq * rh
  let tl := b.vl * min zl (min (1 / (2 - rl)) (1 / dh))
  let th := b.vh * min zh (min (1 / (2 - rh)) (1 / dl))
  let Rl := rl * tl
  let Rh := rh * th
  let prob := 1 - Rl ^ 2
  let den := max (1 + (1 - 2 * rl) * tl) (1 + (1 - 2 * rl) * th)
  let deficit := if den ≠ 0 then rl * (1 - th) ^ 2 / den else 0
  let harmonic := max 0 (1 - Rl * rl - deficit)
  let residual := Gq prob harmonic
  let high := zh - rl
  let llh := c1q * Rh * usqrt (min (1 - rl) (h2q * high))
  let cubic := min κq (llh + usqrt (gramq * (1 + aq) * residual))
  let kinetic := min (th / a0q) (min (Rh + (1 - Rh) / h2q)
    (min (th * (rl + (1 - rl) / a0q)) (Rh + (1 - Rh) / h3q + βq * th * high)))
  1 - e.m * kinetic - sq * usqrt (e.Y b.uh) * cubic

def accept (e : Edge) (b : Box) : Bool := decide (εq < gap e b)

/-- Bisection along the first longest side (order `u, p, v`). -/
def split (b : Box) : Box × Box :=
  let du := b.uh - b.ul
  let dp := b.ph - b.pl
  let dv := b.vh - b.vl
  if dp ≤ du ∧ dv ≤ du then
    let mid := (b.ul + b.uh) / 2
    (⟨b.ul, mid, b.pl, b.ph, b.vl, b.vh⟩, ⟨mid, b.uh, b.pl, b.ph, b.vl, b.vh⟩)
  else if dv ≤ dp then
    let mid := (b.pl + b.ph) / 2
    (⟨b.ul, b.uh, b.pl, mid, b.vl, b.vh⟩, ⟨b.ul, b.uh, mid, b.ph, b.vl, b.vh⟩)
  else
    let mid := (b.vl + b.vh) / 2
    (⟨b.ul, b.uh, b.pl, b.ph, b.vl, mid⟩, ⟨b.ul, b.uh, b.pl, b.ph, mid, b.vh⟩)

/-- The recursive checker. -/
def check (e : Edge) : ℕ → Box → Bool
  | 0, b => accept e b
  | n + 1, b => accept e b || (check e n (split b).1 && check e n (split b).2)

/-- The edge `i` of the plan. -/
def edgeOf (i : ℕ) : Edge := ⟨kX i, kY i, slope i, kX i - kX (i + 1)⟩

/-- Propositional combination: a box whose two halves are accepted trees is an accepted tree. -/
theorem check_of_split {e : Edge} {n : ℕ} {b b1 b2 : Box} (hs : split b = (b1, b2))
    (h1 : check e n b1 = true) (h2 : check e n b2 = true) : check e (n + 1) b = true := by
  simp [check, hs, h1, h2]

end Cert

end OVNS
