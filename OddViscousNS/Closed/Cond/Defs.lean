import OddViscousNS.Closed.Cubic
import OddViscousNS.Closed.Moments

/-!
# The conditional cubic `C_cond` (unforced graph): definitions

`C_cond(ρ,t,q) = min{κ₀, c₁ r √q + √(M₀(1+a) G(m₀, max(0,w₀)))}` with `r = ρt`, `a = 11/60`,
`c₁ = (h₂−1)/√(3h₂)`, `m₀ = 1 − r²`, `w₀ = 1 − rρ − D_LH(ρ,t)`,
`D_LH(ρ,t) = ρ(1−t)²/(1+(1−2ρ)t)` (zero when the denominator vanishes),
`G(m,w) = (m/2)(1 + w/(w+4am))` (`G(0,·) = 0`).  The *LLH class* of a triad sum consists of the
ordered triples with at least two legs on the first shell; `R'_k` deletes the pairs with both
inputs on the first shell (and collinear pairs).
-/

open scoped ENNReal

noncomputable section

namespace OVNS

def aC : ℝ := 11 / 60

/-- `c₁ = (h₂ − 1)/√(3h₂)`. -/
def c1 : ℝ := (hmet 2 - 1) / Real.sqrt (3 * hmet 2)

/-- `D_LH(ρ,t) = ρ(1−t)²/(1+(1−2ρ)t)`, `0` if the denominator vanishes. -/
def DLH (ρ t : ℝ) : ℝ :=
  if 1 + (1 - 2 * ρ) * t = 0 then 0 else ρ * (1 - t) ^ 2 / (1 + (1 - 2 * ρ) * t)

/-- `G(m,w) = (m/2)(1 + w/(w+4am))`, with `G(0,w) = 0`. -/
def Gfun (m w : ℝ) : ℝ := if m = 0 then 0 else m / 2 * (1 + w / (w + 4 * aC * m))

/-- The conditional cubic coefficient. -/
def Ccond (ρ t q : ℝ) : ℝ :=
  min κ₀ (c1 * (ρ * t) * Real.sqrt q +
    Real.sqrt (M₀ * (1 + aC) * Gfun (1 - (ρ * t) ^ 2) (max 0 (1 - ρ * t * ρ - DLH ρ t))))

/-- The ratios of a field: `ρ = x/Y`, `q = Y₂/Y` (and `t = Y/Z`, `tYZ`). -/
def ρw (w : Field) : ℝ := x1 w / Yr w
def qw (w : Field) : ℝ := Y2r w / Yr w

/-- The shell projection `P_j w`. -/
def shell (j : ℕ) (w : Field) : Field := fun k => if nsq k = j then w k else 0

/-- The LLH class: at least two legs of the ordered triple on the first shell. -/
def isLLH (p l q : Mode) : Prop :=
  (nsq p = 1 ∧ nsq l = 1) ∨ (nsq p = 1 ∧ nsq q = 1) ∨ (nsq l = 1 ∧ nsq q = 1)

instance (p l q : Mode) : Decidable (isLLH p l q) := by unfold isLLH; infer_instance

/-- The LLH part of the weighted triad sum (fixed-output form `(k,p) ↦ (p, k−p, −k)`). -/
def triadLLH (u : Field) : ℝ :=
  (1 / 6) * ∑' kp : Mode × Mode,
    if isLLH kp.2 (kp.1 - kp.2) (-kp.1) then
      Wk lamW kp.1 kp.2 * (triT kp.2 (kp.1 - kp.2) (-kp.1) (u kp.2) (u (kp.1 - kp.2))
        (conjV (u kp.1))).re
    else 0

/-- The complementary part. -/
def triadRest (u : Field) : ℝ :=
  (1 / 6) * ∑' kp : Mode × Mode,
    if isLLH kp.2 (kp.1 - kp.2) (-kp.1) then 0 else
      Wk lamW kp.1 kp.2 * (triT kp.2 (kp.1 - kp.2) (-kp.1) (u kp.2) (u (kp.1 - kp.2))
        (conjV (u kp.1))).re

/-- `R'_k`: the pair sum with the first-shell pairs (and collinear pairs) deleted. -/
def Rk' (u : Field) (k : Mode) : ℝ :=
  ∑' p : Mode, if (nsq p = 1 ∧ nsq (k - p) = 1) ∨ cross (modeVec p) (modeVec (k - p)) = 0 then 0
    else Pk u p * Pk u (k - p)

end OVNS
