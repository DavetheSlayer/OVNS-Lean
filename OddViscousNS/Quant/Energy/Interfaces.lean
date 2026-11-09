import OddViscousNS.Corrector

/-!
# Theorem 1.2, fixed force: the analytic interfaces (interface-first staging)

Named `Prop`s, with explicit quantifiers, for the outputs of the analytic energy layers of the
fixed-force proof of Theorem 1.2, following
`OddViscousNS_data/reports/t12_energy_spec.md` §2.1 ("Interface-first staging").  The regimes
layer (`OddViscousNS/Quant/Regimes/FixedForce.lean`: R1 role table, R3 continuation, E6 scalar
lemma, E10 virtual barrier) is formalized *against* these `Prop`s, which are then discharged one
by one.

## Objects (spec §1.1, TeX ↔ Lean)
* the actual solution `y` with `IsHeatSol (filtN r 0) (filtG r 0 g) Ty y`, `q = |r|`
  (`ActualSol`); the force filter `ψ = psi r 0 g`; the split `x = y − ψ = S + F`
  (`actual`; `slowNorm`, `fastNorm` give `a_S, b_S` and `a_F, b_F, c_F`; `slowWiener` is `W_S`);
* the prospective caps `(P_F, y, A_S, B_S, J_F, J_S)` (`Caps`) with the first-exit prefix
  hypotheses of Source 3 §2 (`OnPrefix`, `PrefixHyp`), and the piece length `Tp` (`PieceHyp`,
  amendment D1): the energy interfaces E5, E7, E8 are stated on pieces `[s, t]` of length
  `≤ Tp` only, because their integral clauses (`∫ f_f ≤ π²`, `(2/ℓ₁)∫ m ≤ 1`, …) bound force
  terms that are constant in time; the regimes layer runs the lookahead bootstrap on pieces of
  length in `[Tp − 1, Tp]`.  The kinetic interface E4 keeps unbounded prefixes: its clauses are
  per unit time (`(t − s)/8`);
* the slow-cap exponents `SlowExp` (amendment D3): the slow caps E7 are stated with abstract
  exponents `e = (eA, eB, eJ, eW)` for `a_S, b_S, ∫ b_S², W_S`, constants depending on `φ`,
  polylogs absorbed in the exponents.  E7-HA (TeX eq. quant-slow-caps, Nash/Riesz/Biot–Savart)
  is `e = (3/2, 2, 3, 3/2) (+δ)` (`slowExpHA`); the elementary route E7-el, the only one the
  sources derive, is `e = (2, 4, 4, 2)` (`slowExpEl`; survey `t12_near_slow_route.md` §III,
  every slow-dependent role then still has degree `< d`).  `Caps` carries a `W_S` cap `WS` so
  that role thresholds can see `W_S` at degree `eW` rather than through `c₄ B_S`;
* the exact resonance `⟨Q_res(F,F), A^s F⟩ = pair s F (Qres F F)` (`ResH1`, `ResH2`).

## Status of the interfaces
* Discharged (conditionally): `ResH1 (281/1000) Cs` and `ResH2 (281/1000) CH` are literally the
  conclusions of `resonant_H1`/`resonant_H2` (`OddViscousNS/Quant/Arith/Resonant/Main.lean`),
  conditional on `WeightedCount`; `flux_le` is the `σ = 1` instance of `ResH1` (`β = ∞`, outside
  the scalar domain).  Nothing else is discharged yet.
* Open: `KineticInterface` (E4), `H1EnergyInterface` (E5), `SlowCapsInterface` (E7),
  `H2EnergyInterface` (E8), `NearProfiles` (E9).  Per spec §1.3/§4.2 these rest on MISSING
  bodies: E8 (role 31: F290, N_411; ambiguity (A1)), E5 (role 15's margin through N_411,
  Body 32; the timed metric quota NEW378/LOCAL362, (A4)), E4 (row 36: F283), E9 (N_411; the
  moments `N`, `P` are not defined in the TeX and are abstract parameters here).  E7's
  harmonic-analysis steps are asserted, not proved ((A3)).
* The Mathlib-gap `Prop`s of spec §2.3 (`DriftHeatNash`, `CircleHilbertLp`, `RieszLp`,
  `BiotSavartLp`) are needed only by the E7-HA route and the joint bound (§2.3 heading, §6); the
  fixed-force chain can take E7-el, so they are not stated here.

## Degree bookkeeping (spec §3.1; `θ = σ`)
`β = (2 − σ)/(1 − σ)`, `v = 2β − 1`, `d = β + 3v = 7β − 3` (`betaOf`, `vOf`, `dOf`);
`B = C_H ρ^{1−θ} A^θ` has degree `β − 1` and `λ_* ≍ μ^{2β−2}`.  The exponent is set by roles 31
and 15, whose smallness condition `C √P_F y^{3/2} N(q) ≤ c` with `N(q) ≤ C_δ q^{−1/2+δ}` gives
`q ≳ μ^{β+3v}`; every other role has a threshold of degree `< d` (`DegreeBelow`, Table
quant-fixed).  At `σ = 281/1000`: `β = 1719/719`, `v = 2719/719`, `d = 9876/719`.
**Caveat (A1).** The leading role-15/31 coefficient `√P_F y^{3/2} N(q)` has no derivation in
the sources (its normalization refers to the MISSING N_411/F290; survey
`t12_energy_derivation.md` §E5): `H1EnergyInterface`/`H2EnergyInterface` state it exactly as the
TeX asserts it.
-/

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace OVNS.Quant

/-! ### Arithmetic-layer interfaces (Proposition quant-resonant; spec §2.1) -/

/-- **`ResH1 σ Cs`**: the `H¹` resonant energy inequality
`|⟨Q_res(F,F), AF⟩| ≤ C_s ‖F‖₁^{3−σ} ‖F‖₂^σ` for real fast `F ∈ H²` (spec §2.1).  At
`σ = 281/1000` this is the conclusion of `resonant_H1`; `flux_le` is `σ = 1` with `Cs = CF`. -/
def ResH1 (σ Cs : ℝ) : Prop :=
  ∀ F : Field, Adm 2 F → PiF F = F →
    |pair 1 F (Qres F F)| ≤ Cs * hnorm 1 F ^ (3 - σ) * hnorm 2 F ^ σ

/-- **`ResH2 θ CH`**: the `H²` resonant energy inequality
`|⟨Q_res(F,F), A²F⟩| ≤ C_H ‖F‖_θ ‖F‖₂ ‖F‖₃` for real fast `F ∈ H³` (spec §2.1).  At
`θ = 281/1000` this is the conclusion of `resonant_H2`. -/
def ResH2 (θ CH : ℝ) : Prop :=
  ∀ F : Field, Adm 3 F → PiF F = F →
    |pair 2 F (Qres F F)| ≤ CH * hnorm θ F * hnorm 2 F * hnorm 3 F

/-! ### Degree bookkeeping (spec §3.1) -/

/-- `β(σ) = (2 − σ)/(1 − σ)`: the fast `H¹` peak degree, `A, P_F, √J_F ≍ μ^β` (spec §3.1, E6). -/
def betaOf (σ : ℝ) : ℝ := (2 - σ) / (1 - σ)

/-- `v(σ) = 2β − 1`: the degree of the virtual-barrier fast `H²` cap `y ≍ μ^v` (spec §3.1). -/
def vOf (σ : ℝ) : ℝ := 2 * betaOf σ - 1

/-- `d(σ) = β + 3v = 7β − 3`: the fixed-force exponent (spec §0.1, §3.1). -/
def dOf (σ : ℝ) : ℝ := 7 * betaOf σ - 3

/-- `ρ = μ + 5 + 4φ`: the kinetic (`H⁰`) scale of the normalized data, `‖x‖₀ < ρ` (TeX
quantitative_energies, "explicit independent preliminary bounds"; Source 3 §2). -/
def rhoOf (μ φ : ℝ) : ℝ := μ + 5 + 4 * φ

/-! ### The actual split solution and the prospective caps (spec §1.1, §2 conventions) -/

/-- The actual split field `x(t) = y(t) − ψ(t)` (TeX `x = z − ψ = S + F`), with the force filter
`ψ = psi r 0 g` started at `0`. -/
def actual (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : Field := y t - psi r 0 g t

/-- `‖Π_F x(t)‖_j`: the fast norms `a_F, b_F, c_F` are `j = 1, 2, 3`; `j = 0` is the kinetic
norm `‖F‖₀`. -/
def fastNorm (j r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  hnorm j (PiF (actual r g y t))

/-- `‖Π_S x(t)‖_j`: the slow norms `a_S, b_S` are `j = 1, 2`. -/
def slowNorm (j r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  hnorm j (PiS (actual r g y t))

/-- `‖Π_H x(t)‖_j`: the horizontal slow norms `a_h, b_h` are `j = 1, 2` (`h = PiH`, the
horizontal part of the 2D–3C slow field; D4). -/
def horizNorm (j r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  hnorm j (PiH (actual r g y t))

/-- `W_S(t) = ‖Ŝ(t)‖_{ℓ¹}`, the Wiener norm of the slow part (TeX eq. quant-kinetic-floor).  It
dominates the physical sup norm `M_∞ = ‖S‖_∞` (spec §2.2, E7-el: `M_∞ ≤ W_S`), which has no
Fourier-side object in this library; `M_∞` is therefore represented by `W_S` throughout. -/
def slowWiener (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  wiener (PiS (actual r g y t))

/-- `ActualSol μ φ r g y Ty`: `y` is a filtered heat solution on `[0, Ty)` of the normalized
problem with coefficient `r` (`q = |r|`), a steady force `g` in the force ball `‖g‖₂ ≤ φ`, and a
datum `y 0` in the datum ball `‖y 0‖₂ ≤ μ` — the hypotheses of `normalized_main`, on a lifespan
(as produced by `exists_maximal`). -/
structure ActualSol (μ φ r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞) : Prop where
  /-- The force is real, mean-zero, divergence-free and in `H²`. -/
  force_adm : Adm 2 g
  /-- The force ball `‖g‖₂ ≤ φ`. -/
  force_le : hnorm 2 g ≤ φ
  /-- The lifespan is nonempty. -/
  pos : 0 < Ty
  /-- The filtered equation on `[0, Ty)`. -/
  sol : IsHeatSol (filtN r 0) (filtG r 0 g) Ty y
  /-- The datum ball `‖y 0‖₂ ≤ μ`. -/
  init_le : hnorm 2 (y 0) ≤ μ

/-- The prospective caps of the bootstrap (spec §2, "Caps"; Source 3 §2): the fast `H¹` cap
`P_F`, the fast `H²` cap `y` (the virtual barrier), the slow `H¹` cap `A_S`, the slow `H²` cap
`B_S`, the slow Wiener cap `W_S` (D3), and the fast/slow `H²` square-integral budgets `J_F`,
`J_S` over the current piece. -/
structure Caps where
  /-- `P_F ≥ a_F`. -/
  PF : ℝ
  /-- `y ≥ b_F`. -/
  yF : ℝ
  /-- `A_S ≥ a_S`. -/
  AS : ℝ
  /-- `B_S ≥ b_S`. -/
  BS : ℝ
  /-- `W_S ≥ ‖Ŝ‖_{ℓ¹}` (D3; `M_∞ ≤ W_S`). -/
  WS : ℝ
  /-- `J_F ≥ ∫ b_F²`. -/
  JF : ℝ
  /-- `J_S ≥ ∫ b_S²`. -/
  JS : ℝ
  /-- `E_S ≥ ‖S‖₀`, the slow `L²` sub-cap (D4). -/
  ES : ℝ
  /-- `A_H ≥ a_h`, the horizontal slow `H¹` sub-cap (D4). -/
  AH : ℝ
  /-- `B_H ≥ b_h`, the horizontal slow `H²` sub-cap (D4). -/
  BH : ℝ

/-- `OnPrefix caps r g y s t`: the first-exit hypotheses of Source 3 §2 on the existing prefix
`[s, t]`, in closed form (the bootstrap has them strictly and improves them strictly):
`a_F ≤ P_F`, `b_F ≤ y`, `a_S ≤ A_S`, `b_S ≤ B_S`, `W_S ≤ WS` pointwise and `∫_s^t b_F² ≤ J_F`,
`∫_s^t b_S² ≤ J_S`, and the slow sub-caps `‖S‖₀ ≤ E_S`, `a_h ≤ A_H`, `b_h ≤ B_H` pointwise (D4,
appended last).  The total caps `a_x, b_x, ∫ b_x²` of the source follow from `x = S + F`. -/
def OnPrefix (caps : Caps) (r : ℝ) (g : Field) (y : ℝ → Field) (s t : ℝ) : Prop :=
  (∀ u ∈ Icc s t, fastNorm 1 r g y u ≤ caps.PF ∧ fastNorm 2 r g y u ≤ caps.yF ∧
      slowNorm 1 r g y u ≤ caps.AS ∧ slowNorm 2 r g y u ≤ caps.BS ∧
      slowWiener r g y u ≤ caps.WS) ∧
    (∫ u in s..t, fastNorm 2 r g y u ^ 2) ≤ caps.JF ∧
    (∫ u in s..t, slowNorm 2 r g y u ^ 2) ≤ caps.JS ∧
    (∀ u ∈ Icc s t, slowNorm 0 r g y u ≤ caps.ES ∧ horizNorm 1 r g y u ≤ caps.AH ∧
      horizNorm 2 r g y u ≤ caps.BH)

/-- The standing hypotheses of an energy interface on a prefix: `[s, t]` lies in the lifespan,
the interface's own role threshold `q(caps) ≤ |r|` is paid (spec §2.1 caveat: every interface
exposes its `q(caps)` function), and the caps hold on `[s, t]`. -/
structure PrefixHyp (q : Caps → ℝ) (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞)
    (caps : Caps) (s t : ℝ) : Prop where
  /-- `0 ≤ s`. -/
  hs : 0 ≤ s
  /-- `s ≤ t`. -/
  hst : s ≤ t
  /-- `t` is inside the lifespan. -/
  ht : ENNReal.ofReal t < Ty
  /-- The role threshold is paid. -/
  thr : q caps ≤ |r|
  /-- The caps hold on `[s, t]`. -/
  onPrefix : OnPrefix caps r g y s t

/-- `PrefixHyp` on a *piece*: additionally `t − s ≤ Tp` (amendment D1).  The energy interfaces
E5, E7, E8 are stated on pieces only; the bootstrap uses pieces of length in `[Tp − 1, Tp]`. -/
structure PieceHyp (Tp : ℝ) (q : Caps → ℝ) (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞)
    (caps : Caps) (s t : ℝ) : Prop extends PrefixHyp q r g y Ty caps s t where
  /-- The piece has length at most `Tp`. -/
  len : t - s ≤ Tp

/-! ### E4: the kinetic correction and independent fast peak -/

/-- **E4 output** (spec §2.1 `KineticInterface`; TeX eq. quant-kinetic; Source 3 §3).  Along every
actual solution there is one global AC kinetic functional `W₀ = ‖F‖₀² − 2Re⟨N(F,F),S⟩` (chosen
before any prefix: it is never restarted) which, on every prefix where the caps hold and the six
proper kinetic floors (roles 22–27) and the raised floor (row 36, eq. quant-kinetic-floor) are
paid, `q₀(caps) ≤ q`, satisfies `¾‖F‖₀² ≤ W₀ ≤ ⁵⁄₄‖F‖₀²`, the true-zero bound
`W₀(0) ≤ ⁵⁄₄(μ + ¼)²`, and the integrated forms of `W₀' + a_F² ≤ 1/8` and
`W₀' + 4W₀/5 ≤ 1/8`.  (The spec writes `q₀` as a number along a global solution; row 36 depends
on the slow traces, so the threshold is exposed as `q₀ : Caps → ℝ`.) -/
def KineticInterface (μ φ : ℝ) (q₀ : Caps → ℝ) : Prop :=
  ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞), ActualSol μ φ r g y Ty →
    ∃ W0 : ℝ → ℝ, ∀ (caps : Caps) (s t : ℝ), PrefixHyp q₀ r g y Ty caps s t →
      (∀ u ∈ Icc s t, 3 / 4 * fastNorm 0 r g y u ^ 2 ≤ W0 u ∧
        W0 u ≤ 5 / 4 * fastNorm 0 r g y u ^ 2) ∧
      (s = 0 → W0 0 ≤ 5 / 4 * (μ + 1 / 4) ^ 2) ∧
      W0 t - W0 s + (∫ u in s..t, fastNorm 1 r g y u ^ 2) ≤ (t - s) / 8 ∧
      W0 t ≤ max (W0 s) (5 / 32)

/-! ### E5: the `H¹` energy with signed metric and purefast cubic -/

/-- `ℓ₁ = 1 − 2⁻²⁰ − 1/128`: the lower coercivity constant of the corrected `H¹` energy (TeX,
after eq. quant-kinetic-floor). -/
def ell1 : ℝ := 1 - 1 / 2 ^ 20 - 1 / 128

/-- `u₁ = 1 + 2⁻²⁰ + 1/128`: the upper coercivity constant of the corrected `H¹` energy (TeX). -/
def u1 : ℝ := 1 + 1 / 2 ^ 20 + 1 / 128

/-- **E5 output** (spec §2.1 `H1EnergyInterface`; TeX eq. quant-h1-energy with `n = 3/4`).  On a
prefix where the caps hold, the roles 8, 9, 11–14, 28–30 are paid (`q₁(caps) ≤ q`) and the
leading role 15 (the entire native `E1` nonlinear differential) is paid through the native near
profile, `K₁ √P_F y^{3/2} N(q) ≤ 1`, there are an energy `E = e₁(M₁) + E⁰` with
`ℓ₁ a_F² ≤ 2E ≤ u₁ a_F²`, a genuine `L²` source `N_f`, a separately tested force term `f_f ≥ 0`
and a timed metric multiplier `m ≥ 0` with
`E' + ¾ b_F² ≤ C_s a_F^{3−σ} b_F^σ + N_f b_F + f_f + m a_F²` (integrated), `∫ N_f² ≤ N̄²`,
`∫ f_f ≤ π²` and `(2/ℓ₁)∫ m ≤ 1`, on pieces of length `≤ Tp` (D1).  Abstract parameters:
`N̄ = Nbar` and `π = piTol` (the spec's `Nbar(caps)`, `π(μ)`; only their growth `O(μ)` at fixed
`φ` is used, spec §1.4, §3.1), the role-15 normalization `K₁` (Body 32 through the MISSING
N_411/F290) and the native moment `N` (E9).  The leading coefficient `√P_F y^{3/2} N(q)` has no
derivation in the sources ((A1)); it is stated as the TeX asserts it.  Uses `ResH1 σ Cs`. -/
def H1EnergyInterface (σ Cs μ φ Tp Nbar piTol K₁ : ℝ) (q₁ : Caps → ℝ) (N : ℝ → ℝ) : Prop :=
  ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞) (caps : Caps) (s t : ℝ),
    ActualSol μ φ r g y Ty → PieceHyp Tp q₁ r g y Ty caps s t →
    K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * N |r| ≤ 1 →
    ∃ E Nf ff m : ℝ → ℝ,
      (∀ u ∈ Icc s t, ell1 * fastNorm 1 r g y u ^ 2 ≤ 2 * E u ∧
        2 * E u ≤ u1 * fastNorm 1 r g y u ^ 2) ∧
      (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
        E u₂ - E u₁ + 3 / 4 * (∫ u in u₁..u₂, fastNorm 2 r g y u ^ 2) ≤
          ∫ u in u₁..u₂, (Cs * fastNorm 1 r g y u ^ (3 - σ) * fastNorm 2 r g y u ^ σ +
            Nf u * fastNorm 2 r g y u + ff u + m u * fastNorm 1 r g y u ^ 2)) ∧
      (∀ u ∈ Icc s t, 0 ≤ ff u ∧ 0 ≤ m u) ∧
      IntervalIntegrable (fun u => Nf u ^ 2) volume s t ∧ IntervalIntegrable ff volume s t ∧
      IntervalIntegrable m volume s t ∧
      (∫ u in s..t, Nf u ^ 2) ≤ Nbar ^ 2 ∧ (∫ u in s..t, ff u) ≤ piTol ^ 2 ∧
      2 / ell1 * (∫ u in s..t, m u) ≤ 1

/-! ### E8 + E10: the `H²` energy and the virtual-barrier constants -/

/-- `d₀ = 2/3`: the retained share of the `H³` dissipation in the `H²` energy (TeX, virtual
barrier). -/
def dZero : ℝ := 2 / 3

/-- `b_* = v_* A B / d₀`: the barrier level of `b_F` (TeX, virtual barrier; `v_* = 1` for fixed
force). -/
def bStar (vStar A B : ℝ) : ℝ := vStar * A * B / dZero

/-- `W_* = u b_*²`, `u = 33/32`: the barrier level of the `H²` energy (TeX, virtual barrier). -/
def WStar (vStar A B : ℝ) : ℝ := 33 / 32 * bStar vStar A B ^ 2

/-- `λ_* = d₀ b_*² / (u A²)`: the virtual damping rate (TeX, virtual barrier); clips have length
`≤ 1/λ_*`. -/
def lamStar (vStar A B : ℝ) : ℝ := dZero * bStar vStar A B ^ 2 / (33 / 32 * A ^ 2)

/-- The resonant `H²` coefficient `B = C_H ρ^{1−θ} A^θ` after the `H¹` proof (TeX, virtual
barrier; spec §1.2 E8), with `A = P_F` the fast `H¹` cap on the prefix and `ρ = rhoOf μ φ` the
kinetic scale (`‖F‖_θ ≤ ‖F‖₀^{1−θ}‖F‖₁^θ`, from `ResH2 θ CH`). -/
def resCoeff (θ CH μ φ : ℝ) (caps : Caps) : ℝ := CH * rhoOf μ φ ^ (1 - θ) * caps.PF ^ θ

/-- **E8 output, E10 input** (spec §2.1 `H2EnergyInterface`; TeX eq. quant-metric at `s = 2`,
the weight-two cubic, and the virtual barrier paragraph).  On a prefix where the caps hold, the
roles 16, 17, 28, 32 are paid (`q₂(caps) ≤ q`) and the leading role 31 (the entire native `E2`
nonlinear differential, coefficient `C √P_F y^{3/2} N(q)`) is paid through the native near
profile, `K₂ √P_F y^{3/2} N(q) ≤ 1`, there are a corrected `H²` energy `W = 2(e₂(M₂) + E⁰₂)`
with `³¹⁄₃₂ b_F² ≤ W ≤ ³³⁄₃₂ b_F²`, a multiplier `G ≥ 0` and a short residual `H ≥ 0` with
`W' ≤ −2d₀ c_F² + 2B b_F c_F + G W + H` (integrated), `B = resCoeff`, such that on every clip of
length `≤ 1/λ_*` the multiplier has mass `≤ m₀` ("small", TeX) and the residual has integral
`≤ W_*/32`; all on pieces of length `≤ Tp` (D1).  Abstract parameters: the role-31
normalization `K₂` (MISSING F290/N_411), the clip mass `m₀`, the native moment `N` (E9).  The
leading coefficient `√P_F y^{3/2} N(q)` has no derivation in the sources ((A1)); it is stated as
the TeX asserts it.  The short slow `H³` price (eq. quant-short-slow) and the `L_h(F)` mixed split
are consumed inside `H` and are not separate interfaces. -/
def H2EnergyInterface (θ CH μ φ Tp K₂ m₀ : ℝ) (q₂ : Caps → ℝ) (N : ℝ → ℝ) : Prop :=
  ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞) (caps : Caps) (s t : ℝ),
    ActualSol μ φ r g y Ty → PieceHyp Tp q₂ r g y Ty caps s t →
    K₂ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * N |r| ≤ 1 →
    let A := caps.PF
    let B := resCoeff θ CH μ φ caps
    ∃ W G H : ℝ → ℝ,
      (∀ u ∈ Icc s t, 31 / 32 * fastNorm 2 r g y u ^ 2 ≤ W u ∧
        W u ≤ 33 / 32 * fastNorm 2 r g y u ^ 2) ∧
      IntervalIntegrable (fun u => fastNorm 3 r g y u ^ 2) volume s t ∧
      (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t →
        W u₂ - W u₁ ≤ ∫ u in u₁..u₂, (-2 * dZero * fastNorm 3 r g y u ^ 2 +
          2 * B * fastNorm 2 r g y u * fastNorm 3 r g y u + G u * W u + H u)) ∧
      (∀ u ∈ Icc s t, 0 ≤ G u ∧ 0 ≤ H u) ∧
      IntervalIntegrable G volume s t ∧ IntervalIntegrable H volume s t ∧
      (∀ u₁ u₂ : ℝ, s ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ t → u₂ - u₁ ≤ 1 / lamStar 1 A B →
        (∫ u in u₁..u₂, G u) ≤ m₀ ∧ (∫ u in u₁..u₂, H u) ≤ WStar 1 A B / 32)

/-! ### E7: the slow caps on the existing prefix -/

/-- The slow-cap exponents (D3): `a_S ≲ μ^{eA}`, `b_S ≲ μ^{eB}`, `∫ b_S² ≲ μ^{eJ}`,
`W_S ≲ μ^{eW}` at fixed `φ`.  E7-HA (TeX eq. quant-slow-caps): `(3/2, 2, 3, 3/2)` up to
polylogs; E7-el (the elementary route, the only one the sources derive): `(2, 4, 4, 2)`. -/
structure SlowExp where
  /-- Exponent of the slow `H¹` cap `A_S`. -/
  eA : ℝ
  /-- Exponent of the slow `H²` cap `B_S`. -/
  eB : ℝ
  /-- Exponent of the slow `H²` square-integral budget `J_S`. -/
  eJ : ℝ
  /-- Exponent of the slow Wiener cap `W_S` (`M_∞ ≤ W_S`). -/
  eW : ℝ

/-- The harmonic-analysis exponents of TeX eq. quant-slow-caps (polylogs to be absorbed by a
`+δ`): `A_S ≲ R^{3/2}`, `B_S ≲ R²`, `J_S ≲ R³`, `W_S ≲ R^{3/2}`.  Route E7-HA (grade X). -/
def slowExpHA : SlowExp := ⟨3 / 2, 2, 3, 3 / 2⟩

/-- The elementary exponents of route E7-el (survey `t12_near_slow_route.md` §III):
`A_S ≲ μ²`, `B_S ≲ μ⁴`, `J_S ≲ μ⁴`, `W_S ≲ μ^{2(+δ)}`. -/
def slowExpEl : SlowExp := ⟨2, 4, 4, 2⟩

/-- The slow start levels at radius `μ` (D4): `‖S‖₀ ≤ L₀ μ`, `a_h ≤ L₁ μ`, `b_h ≤ L₂ μ²`,
`a_S ≤ L₃ μ^{eA}`, `b_S ≤ L₄ μ^{eB}` at time `u`. -/
def SlowLevel (L : Fin 5 → ℝ) (μ : ℝ) (e : SlowExp) (r : ℝ) (g : Field) (y : ℝ → Field)
    (u : ℝ) : Prop :=
  slowNorm 0 r g y u ≤ L 0 * μ ∧ horizNorm 1 r g y u ≤ L 1 * μ ∧
    horizNorm 2 r g y u ≤ L 2 * μ ^ 2 ∧ slowNorm 1 r g y u ≤ L 3 * μ ^ e.eA ∧
    slowNorm 2 r g y u ≤ L 4 * μ ^ e.eB

/-- **E7 output** (spec §2.1 `SlowCapsInterface`; TeX eq. quant-slow-caps; D3; restated in the
strict-improvement form, D4).  At fixed `φ` there are start levels `L` (all `≥ 1`) and a constant
`C` such that for all `μ ≥ 1`, on every piece `[s, t]` where the caps hold and the slow-correction
roles 5–7, 18–21 are paid (`qS(μ,φ,caps) ≤ q`) and whose START is at the slow levels `L`
(`SlowLevel L μ e … s`): pointwise on the piece `‖S‖₀, a_h ≤ C μ`, `b_h ≤ C μ²`,
`a_S ≤ C μ^{eA}`, `b_S ≤ C μ^{eB}`, `W_S ≤ C μ^{eW}`; `∫_s^t b_S² ≤ C μ^{eJ}`; and after the first
unit (`u ∈ [s + 1, t]`) the slow quantities are back at the start levels `L` (so the next good
point, chosen in the last unit of the piece, is again at the levels).  Why this form: the
previous statement (bounds from `PieceHyp` alone) is not dischargeable by any route, since
nothing bounded the piece-start values (`t12_slow_fourier_route.md` §4).  Route E7-F (Fourier
side) proves it with `e = ⟨2, 3, 4, 5/2⟩`: slow `L²` energy and horizontal enstrophy contract
`‖S‖₀, a_h` to levels `≍ μ`, window averaging gives `a_S ≲ μ²`, `∫ b_S² ≲ μ⁴`, the `h`-barrier
`b_h ≲ a_h²`, the `ζ`-barrier `b_ζ ≲ μ³`, and `W_S ≤ c √(A_S B_S)`; the levels `L` are chosen
triangularly (`L₀, L₁`, then `L₂`, then `L₃, L₄`).  `M_∞ ≤ W_S` represents the physical sup norm.
Stated on pieces of length `≤ Tp` (D1). -/
def SlowCapsInterface (Tp : ℝ) (e : SlowExp) (qS : ℝ → ℝ → Caps → ℝ) : Prop :=
  ∀ φ : ℝ, 0 ≤ φ → ∃ (L : Fin 5 → ℝ) (C : ℝ), (∀ i, 1 ≤ L i) ∧ ∀ μ : ℝ, 1 ≤ μ →
    ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞) (caps : Caps) (s t : ℝ),
      ActualSol μ φ r g y Ty → PieceHyp Tp (qS μ φ) r g y Ty caps s t →
      SlowLevel L μ e r g y s →
      (∀ u ∈ Icc s t, SlowLevel (fun _ ↦ C) μ e r g y u ∧ slowWiener r g y u ≤ C * μ ^ e.eW) ∧
      (∫ u in s..t, slowNorm 2 r g y u ^ 2) ≤ C * μ ^ e.eJ ∧
      ∀ u ∈ Icc (s + 1) t, SlowLevel L μ e r g y u

/-! ### E9: the complete near profiles -/

/-- **E9 output** (spec §2.1 `NearProfiles`; TeX eq. quant-profiles in the fixed-`δ` form that
suffices for fixed force, spec §0.3): the complete native near moment `N(q)` and proper near
moment `P(q)` satisfy `N(q) ≤ C_δ q^{−1/2+δ}` and `P(q) ≤ C_δ q^{−1/3+δ}` for `q ≥ 1`.  The
moments are abstract parameters: the TeX does not define them ("the exact moment being bounded
is not defined", spec §4.2 R3) — their kernel weights are in Bodies 19–21, 89, 90.  `N` enters the
leading roles 15/31 (`H1EnergyInterface`, `H2EnergyInterface`); `P` enters the proper roles
13, 14, 16, 17 (degree `3v < d`), which are folded into the thresholds `q₁`, `q₂`. -/
def NearProfiles (N P : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ q : ℝ, 1 ≤ q →
    N q ≤ C * q ^ (-1 / 2 + δ) ∧ P q ≤ C * q ^ (-1 / 3 + δ)

/-- **The native profile clause** (D5): `N(q) ≤ C_δ q^{−1/2+δ}` for `q ≥ 1`.  This is the only
part of the near profiles used by the regimes layer (the leading pair, roles 15/31,
`NearProfiles.leading_paid'`); the proper profile `P` enters only the abstract thresholds
`q₁, q₂` (`DegreeBelow`).  Both `NearProfiles N P` and the elementary-route `NearProfilesEl N P`
(`Near/Defs.lean`, proper exponent `−3/10 + δ`) imply it: the projection is
`fun δ hδ ↦ (h δ hδ).imp fun C hC q hq ↦ (hC q hq).1`. -/
def NativeProfile (N : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ q : ℝ, 1 ≤ q → N q ≤ C * q ^ (-1 / 2 + δ)

/-- `NearProfiles` gives the native profile clause. -/
theorem NearProfiles.nativeProfile {N P : ℝ → ℝ} (h : NearProfiles N P) : NativeProfile N :=
  fun δ hδ ↦ (h δ hδ).imp fun _ hC q hq ↦ (hC q hq).1

/-- The native profile clause alone gives `NearProfiles` with the zero proper profile. -/
theorem NativeProfile.nearProfiles_zero {N : ℝ → ℝ} (h : NativeProfile N) :
    NearProfiles N (fun _ ↦ 0) := by
  intro δ hδ
  obtain ⟨C, hC⟩ := h δ hδ
  refine ⟨max C 0, fun q hq ↦ ⟨(hC q hq).trans ?_, ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
  · exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)

/-! ### Fixed-force degrees of the role thresholds (spec §1.4, §3.2; Table quant-fixed) -/

/-- The fixed-force scaling of the prospective caps at datum radius `μ ≥ 1` and fixed `φ` (spec
§1.2, §3.1, Fixed finite force proof): `P_F ≍ μ^β`, `y ≍ μ^v`, `J_F ≍ μ^{2β}` two-sided (E6, E10),
and `A_S ≲ μ^{eA+δ}`, `B_S ≲ μ^{eB+δ}`, `J_S ≲ μ^{eJ+δ}`, `W_S ≲ μ^{eW+δ}` (E7 with the slow
exponents `e`, D3; polylogs absorbed in `μ^δ`), all with constant `K`. -/
def CapsScaled (σ δ K μ : ℝ) (e : SlowExp) (caps : Caps) : Prop :=
  (μ ^ betaOf σ / K ≤ caps.PF ∧ caps.PF ≤ K * μ ^ betaOf σ) ∧
    (μ ^ vOf σ / K ≤ caps.yF ∧ caps.yF ≤ K * μ ^ vOf σ) ∧
    (μ ^ (2 * betaOf σ) / K ≤ caps.JF ∧ caps.JF ≤ K * μ ^ (2 * betaOf σ)) ∧
    caps.AS ≤ K * μ ^ (e.eA + δ) ∧ caps.BS ≤ K * μ ^ (e.eB + δ) ∧
    caps.JS ≤ K * μ ^ (e.eJ + δ) ∧ caps.WS ≤ K * μ ^ (e.eW + δ) ∧
    caps.ES ≤ K * μ ^ (1 + δ) ∧ caps.AH ≤ K * μ ^ (1 + δ) ∧ caps.BH ≤ K * μ ^ (2 + δ)

/-- A role threshold `q(μ, φ, caps)` has fixed-force degree `< d` (spec §2.1 caveat:
"`∃ C κ, κ < 7β−3 ∧ q₁ ≤ C μ^κ`"; Table quant-fixed): at fixed `φ`, for all sufficiently small
polylog exponents `δ` and every cap-scaling constant `K`, it is `≤ C μ^κ` with `κ < d` on all
`δ`-scaled caps (slow exponents `e`, D3).  This is the R1 duty of each non-leading role; the
leading pair (15, 31) is instead tied to `NearProfiles`. -/
def DegreeBelow (σ d : ℝ) (e : SlowExp) (q : ℝ → ℝ → Caps → ℝ) : Prop :=
  ∀ φ : ℝ, 0 ≤ φ → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ K : ℝ, 0 < δ → δ ≤ δ₀ → 1 ≤ K →
    ∃ C κ : ℝ, κ < d ∧ ∀ μ : ℝ, 1 ≤ μ → ∀ caps : Caps,
      CapsScaled σ δ K μ e caps → q μ φ caps ≤ C * μ ^ κ

/-- Linear growth at fixed `φ`: `f(μ, φ) ≤ C μ` for `μ ≥ 1` (spec §1.4: `ρ, π ≍ μ`; TeX Lemma
quant-scalar: `E₀, I_a, π² = O(X²)`, `N̄ = O(X)`). -/
def AtMostLinear (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ φ : ℝ, 0 ≤ φ → ∃ C : ℝ, ∀ μ : ℝ, 1 ≤ μ → f μ φ ≤ C * μ

end OVNS.Quant

end
