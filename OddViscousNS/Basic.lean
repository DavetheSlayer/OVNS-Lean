import Mathlib

/-!
# Navier–Stokes with odd viscosity on the cubic torus: the Fourier-side model

All objects are Fourier coefficients on `𝕋³ = (ℝ/2πℤ)³`, exactly as in the manuscript, where a
solution is *defined* by its mode equations (`\eqref{eq:mode}`).

* `Mode` — the lattice `ℤ³`.
* `V3` — `ℂ³` with its Hilbert norm.  A vector field is `Field = Mode → V3`.
* `leray k` — the Leray symbol `P_k = I - k kᵀ/|k|²` (and `0` at `k = 0`).
* `oddSym k` — the symbol of `L = ℙ(e₃ × Δ)`.
* `convec u k` — the `k`-th coefficient of `ℙ((u·∇)u)`.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter

noncomputable section

namespace OVNS

/-- The Fourier lattice `ℤ³`. -/
abbrev Mode := Fin 3 → ℤ

/-- Complex 3-vectors with the Hilbert norm. -/
abbrev V3 := EuclideanSpace ℂ (Fin 3)

/-- Vector fields, as families of Fourier coefficients. -/
abbrev Field := Mode → V3

/-- `|k|²`. -/
def absSq (k : Mode) : ℝ := ∑ i, (k i : ℝ) ^ 2

/-- `|k|`. -/
def absk (k : Mode) : ℝ := Real.sqrt (absSq k)

/-- A wave vector, as a complex vector. -/
def modeVec (k : Mode) : V3 := WithLp.toLp 2 (fun i => (k i : ℂ))

/-- The bilinear (conjugation-free) pairing `v · k`. -/
def dotM (v : V3) (k : Mode) : ℂ := ∑ i, v i * (k i : ℂ)

/-- The bilinear cross product on `ℂ³`. -/
def cross (a b : V3) : V3 :=
  WithLp.toLp 2 ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- The vertical unit vector `e₃`. -/
def e3 : V3 := WithLp.toLp 2 ![0, 0, 1]

/-- The Leray symbol `P_k v = v - (v·k) k / |k|²`, extended by `0` at `k = 0`. -/
def leray (k : Mode) (v : V3) : V3 :=
  if k = 0 then 0 else v - (dotM v k / (absSq k : ℂ)) • modeVec k

/-- The symbol of `L = ℙ(e₃ × Δ)`: first `Δ` (multiplication by `-|k|²`), then `e₃ ×`, then `ℙ`. -/
def oddSym (k : Mode) (v : V3) : V3 :=
  leray k (cross e3 ((-(absSq k : ℂ)) • v))

/-- Coefficients of `(a·∇)b`: `∑_{p+q=k} (â_p · i q) b̂_q`. -/
def advect (a b : Field) (k : Mode) : V3 :=
  ∑' p : Mode, (Complex.I * dotM (a p) (k - p)) • b (k - p)

/-- Coefficients of `ℙ((u·∇)u)`. -/
def convec (u : Field) (k : Mode) : V3 := leray k (advect u u k)

/-- The Sobolev weight `|k|^{2s}`, zero at `k = 0`. -/
def sobWeight (s : ℝ) (k : Mode) : ℝ := if k = 0 then 0 else absk k ^ (2 * s)

/-- `‖u‖_s² ∈ [0,∞]`, the extended homogeneous coefficient Sobolev norm. -/
def hsE (s : ℝ) (u : Field) : ℝ≥0∞ := ∑' k, ENNReal.ofReal (sobWeight s k * ‖u k‖ ^ 2)

/-- `u ∈ H^s` (homogeneous coefficient norm finite). -/
def InH (s : ℝ) (u : Field) : Prop := Summable fun k => sobWeight s k * ‖u k‖ ^ 2

/-- `‖u‖_s`. -/
def hnorm (s : ℝ) (u : Field) : ℝ := Real.sqrt (∑' k, sobWeight s k * ‖u k‖ ^ 2)

/-- Componentwise complex conjugation on `ℂ³`. -/
def conjV (v : V3) : V3 := WithLp.toLp 2 (fun i => conj (v i))

/-- Reality of the physical field: `û(-k) = conj û(k)`. -/
def IsReal (u : Field) : Prop := ∀ k, u (-k) = conjV (u k)

/-- `k · û(k) = 0`. -/
def IsSolenoidal (u : Field) : Prop := ∀ k, dotM (u k) k = 0

/-- The real, mean-zero, divergence-free `H^s` fields. -/
structure Adm (s : ℝ) (u : Field) : Prop where
  inH : InH s u
  real : IsReal u
  sol : IsSolenoidal u
  mean : u 0 = 0

/-- `t ↦ u t` is continuous on `[0,∞)` with values in `H^s` (in the `H^s` metric). -/
def ContH (s : ℝ) (u : ℝ → Field) : Prop :=
  ∀ t₀ ∈ Ici (0 : ℝ), Tendsto (fun t => hnorm s (u t - u t₀)) (𝓝[Ici 0] t₀) (𝓝 0)

/-- `u ∈ L²_loc([0,∞); H^s)`. -/
def L2locH (s : ℝ) (u : ℝ → Field) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∫⁻ t in Icc 0 T, hsE s (u t) < ∞

/-- A global strong solution in `C([0,∞); H²_sol)` of
`∂ₜu + ℙ((u·∇)u) = νΔu + αLu + f`, `u(0) = u₀`, in the sense of the manuscript's mode equations:
every Fourier coefficient is differentiable on `[0,∞)` (one-sided at `0`) and solves its ODE. -/
structure IsStrongSolution (ν α : ℝ) (f u₀ : Field) (u : ℝ → Field) : Prop where
  init : u 0 = u₀
  adm : ∀ t, 0 ≤ t → Adm 2 (u t)
  cont : ContH 2 u
  mode : ∀ k t, 0 ≤ t → HasDerivWithinAt (fun s => u s k)
    ((-(ν * absSq k : ℝ) : ℂ) • u t k + (α : ℂ) • oddSym k (u t k) - convec (u t) k + f k)
    (Ici 0) t

/-- Smoothness at positive times, in the form equivalent to `u ∈ C^∞((0,∞) × 𝕋³)`:
each mode is smooth in time, and every time derivative lies in every `H^r`, locally uniformly
on `(0,∞)`. -/
def SmoothAtPositiveTimes (u : ℝ → Field) : Prop :=
  (∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => u t k) (Ioi 0)) ∧
  ∀ (j : ℕ) (r a b : ℝ), 0 < a → a ≤ b → ∃ C : ℝ, ∀ t ∈ Icc a b,
    hsE r (fun k => iteratedDerivWithin j (fun s => u s k) (Ioi 0) t) ≤ ENNReal.ofReal C

end OVNS
