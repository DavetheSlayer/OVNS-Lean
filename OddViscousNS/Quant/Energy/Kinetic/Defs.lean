import OddViscousNS.Quant.Energy.Interfaces
import OddViscousNS.Trilinear

/-!
# E4, the kinetic correction: definitions

The objects of the kinetic layer of the fixed-force proof of Theorem 1.2 (TeX
`quantitative_energies.tex`, "The kinetic correction and independent fast peak"; survey
`OddViscousNS_data/reports/t12_energy_derivation.md` §2.1; spec `t12_energy_spec.md` §2.2 E4).

## The kinetic primitive (TeX: "the proper kinetic primitive, which is different from `R_S`")
* `kinM r τ` — the multiplier `𝟏_{k₃ = 0, p₃ ≠ 0} e^{iτΦ}/(i r Φ)`: slow output `k = p + q`, fast
  inputs, denominator "the actual nonzero outer phase".  Lean's `x / 0 = 0` makes it vanish on
  the resonant slow-output triads `Φ = 0`, exactly as the TeX restricts the denominator to the
  nonzero phases; there the vertex itself vanishes (`vert_hel_zero`, `res_null`).
* `kinSym r τ` — the same symbol written as Body 48 (N2) does, `e^{iτΦ}/(2 i r p₃)`: on a slow
  output the vertex is `Φ/(2p₃)·ℙ(A×B)` (`vert_hel_slow_out`, `Symbol.lean`), so
  `kinM • vert = kinSym • ℙ(A×B)` (`kinM_smul_vert`), a bounded symbol `≤ 1/(2q)` with no small
  divisor.
* `kinN r τ f g = Q^♯_{kinM r τ}(f, g)` — the primitive `N(f,g)`; `W₀ = ‖F‖₀² − 2Re⟨N(F,F),S⟩`
  is `W0`, with `kinCorr = Re⟨N(F,F), S⟩ = pair 0 S (N(F,F))` (`pair` is the real pairing, so the
  order of the slots is immaterial).  The phase is evaluated at `τ = r t` along the actual
  filtered solution (`filtN r 0 t = Qphase (r t)`), so that the frozen-amplitude derivative of
  `N(F,F)` is `Π_S Q_{rt}(F,F)` (TeX (N4); `Derivative.lean`).

## The right-hand sides of the split system (TeX eq. quant-actual-system)
`x = y − ψ = S + F` with `ψ = psi r 0 g` (`actual`), `x' = −Ax − Q_{rt}(y,y) + Π_S g`
(`actual_mode`, `Derivative.lean`); `fastRHS`/`slowRHS` are `F'` and `S'`, and
`Hpsi = Q(y,y) − Q(x,x) = 2Q(x,ψ) + Q(ψ,ψ)` is the force filter `H_ψ`.

## The role thresholds (TeX Table quant-roles, rows 22–27 and 36; eq. quant-kinetic-floor)
`kinThreshold μ φ caps` is the sum of the six proper kinetic floors, the raised floor and the
Fourier-side error budget of the Lean proof (`Main.lean`), all multiplied by the loose constant
`kinC φ`.  A sum dominates the TeX's maximum, so paying it pays every role.  Caps enter through
their nonnegative parts `cp` (the caps dominate norms, so are nonnegative on every nonempty
prefix; clipping keeps the threshold monotone, which `DegreeBelow` needs).  Row ↔ Lean:

| TeX row (Body 17 §4, F225 literal function) | Lean |
|---|---|
| 22, coefficient floor `1` | `role22` |
| 23, filter `H⁰–H³`: `4φ` | `role23` |
| 24, `2¹² Y` (`Y` the total `H²` cap, here `y + B_S`) | `role24` |
| 25, `2²⁰ y²` (NEW385; also every `R_S` `H²` trace) | `role25` |
| 26, `2⁹ φ` | `role26` |
| 27, `2⁵ C_A Y φ` (`C_A ↦ c₄`) | `role27` |
| 36, raised kinetic domain `64 Q₀'`, `Q₀' ≲ T² + Tφ + T + S₀(R + R^{3/2} + T) + R A_S` | `role36` |
| eq. quant-kinetic-floor `C q⁻¹{W_S(M_∞ + D₄ + y) + M_∞ A_S + y²}`, with `M_∞ ↦ W_S` and
  `D₄ ↦ ρ + √(ρ(B_S+1)) + 1` | `kineticFloor` |
| the Lean error budget (fixed-slow-output Cauchy, Young; `Main.lean`) | `fourierFloor` |

Here `ρ = rhoOf μ φ = μ + 5 + 4φ` is the kinetic scale (TeX "explicit independent preliminary
bounds"), `T = y`, `S₀ = B_S`, `R = ρ`.  Constants are loose throughout ("constants can be
enlarged by fixed factors", TeX §quant-energies).
-/

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace OVNS

/-! ### The kinetic primitive -/

open Classical in
/-- The kinetic multiplier `𝟏_{(p+q)₃ = 0, p₃ ≠ 0} e^{iτΦ}/(i r Φ)` (TeX: "its denominator is the
actual nonzero outer phase"; spec §1.1 `N(F,F)`, "`V/(irΦ)` on `Φ ≠ 0`").  It vanishes on the
resonant slow-output triads (`x / 0 = 0`). -/
def kinM (r τ : ℝ) : Mult := fun a b c p q =>
  if (p + q) 2 = 0 ∧ p 2 ≠ 0 then
    phaseM τ a b c p q / (Complex.I * (r * Phi a b c p q : ℝ)) else 0

open Classical in
/-- The kinetic symbol in Body 48 (N2) form, `e^{iτΦ}/(2 i r p₃)` on the nonresonant slow-output
triads with fast inputs; `kinM • vert = kinSym • ℙ(A×B)` (`kinM_smul_vert`). -/
def kinSym (r τ : ℝ) (a b c : Sgn) (p q : Mode) : ℂ :=
  if (p + q) 2 = 0 ∧ p 2 ≠ 0 ∧ Phi a b c p q ≠ 0 then
    phaseM τ a b c p q / (2 * Complex.I * (r * (p 2 : ℝ) : ℝ)) else 0

/-- The kinetic primitive `N(f, g) = Q^♯_{kinM}(f, g)` (TeX, "the proper kinetic primitive"):
slow-valued, bilinear, with the bounded symbol `kinSym` (`Symbol.lean`). -/
def kinN (r τ : ℝ) : Field → Field → Field := Qm (kinM r τ)

/-! ### Elementary algebra used by the kinetic layer -/

lemma bd_smul_right (c : ℂ) (A B : V3) : bd A (c • B) = c * bd A B := by
  simp only [bd, PiLp.smul_apply, smul_eq_mul]
  ring

lemma vert_comm (p q : Mode) (A B : V3) : vert p q A B = vert q p B A := by
  rw [vert, vert, add_comm p q, add_comm ((Complex.I * dotM A q) • B)]

lemma Phi_symm' (a b c : Sgn) (p q : Mode) : Phi a b c p q = Phi b a c q p := by
  simp only [Phi, add_comm q p]
  ring

lemma Phi_neg' (a b c : Sgn) (p q : Mode) : Phi a b c (-p) (-q) = -Phi a b c p q := by
  have h : -p + -q = -(p + q) := by abel
  simp only [Phi, lam_neg, h]
  ring

/-! ### `ℓ²` bookkeeping for mean-zero fields -/

lemma summable_norm_sq_of_inH {f : Field} (hf : InH 0 f) : Summable fun k => ‖f k‖ ^ 2 := by
  have h1 : Summable fun k => sobWeight 0 k * ‖f k‖ ^ 2 := hf
  have h2 : Summable fun k : Mode => if k = 0 then ‖f 0‖ ^ 2 else 0 :=
    (hasSum_ite_eq (0 : Mode) _).summable
  refine (h1.add h2).congr fun k => ?_
  by_cases hk : k = 0 <;> simp [sobWeight, hk]

lemma inH_zero_of_summable {f : Field} (hf : Summable fun k => ‖f k‖ ^ 2) : InH 0 f :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg 0 k) (sq_nonneg _))
    (fun k => by
      have : sobWeight 0 k ≤ 1 := by unfold sobWeight; split_ifs <;> simp
      nlinarith [sq_nonneg ‖f k‖]) hf

/-- For a mean-zero field, `‖f‖₀` is the `ℓ²` norm of the coefficients. -/
lemma hnorm_zero_eq {f : Field} (hf : f 0 = 0) :
    hnorm 0 f = Real.sqrt (∑' k, ‖f k‖ ^ 2) := by
  unfold hnorm
  congr 1
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk; simp [hf]
  · simp [sobWeight, hk]

lemma summable_sq_of_summable {f : Field} (hf : Summable fun k => ‖f k‖) :
    Summable fun k => ‖f k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    (hf.mul_left (∑' k, ‖f k‖))
  have := hf.le_tsum k fun j _ => norm_nonneg _
  nlinarith [norm_nonneg (f k)]

namespace Quant

/-! ### The corrected kinetic functional along the actual solution -/

/-- The kinetic correction `Re⟨N(F,F), S⟩ = pair 0 S (N(F,F))` along the split solution
`x = y − ψ = S + F`, with the phase at `τ = r t`. -/
def kinCorr (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  pair 0 (PiS (actual r g y t))
    (kinN r (r * t) (PiF (actual r g y t)) (PiF (actual r g y t)))

/-- **The corrected kinetic energy** `W₀ = ‖F‖₀² − 2Re⟨N(F,F), S⟩` (TeX, eq. before
quant-kinetic): one global functional along the actual solution, never restarted. -/
def W0 (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  fastNorm 0 r g y t ^ 2 - 2 * kinCorr r g y t

/-- The force filter `H_ψ = 2Q_τ(x,ψ) + Q_τ(ψ,ψ) = Q_τ(y,y) − Q_τ(x,x)` (TeX
eq. quant-actual-system), with `τ = r t`. -/
def Hpsi (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : Field :=
  Qphase (r * t) (y t) (y t) - Qphase (r * t) (actual r g y t) (actual r g y t)

/-- The right-hand side `F' = −AF − Π_F Q_{rt}(y,y)` of the fast equation (TeX
eq. quant-actual-system, first line, before isolating `𝓛_τ(S)F` and `H_{ψ,F}`). -/
def fastRHS (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : Field := fun k =>
  (-(absSq k : ℝ) : ℂ) • PiF (actual r g y t) k - PiF (Qphase (r * t) (y t) (y t)) k

/-- The right-hand side `S' = −AS − Π_S Q_{rt}(y,y) + Π_S g` of the slow equation (TeX
eq. quant-actual-system, second line: `−B(S,S) + h₀`). -/
def slowRHS (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : Field := fun k =>
  (-(absSq k : ℝ) : ℂ) • PiS (actual r g y t) k - PiS (Qphase (r * t) (y t) (y t)) k + PiS g k

/-! ### The role thresholds -/

/-- The nonnegative part of a cap. -/
def cp (x : ℝ) : ℝ := max x 0

lemma cp_nonneg (x : ℝ) : 0 ≤ cp x := le_max_right _ _

lemma le_cp (x : ℝ) : x ≤ cp x := le_max_left _ _

lemma cp_le {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y) : cp x ≤ y := max_le h hy

/-- The loose absolute constant of the kinetic floors: `2²⁰ (1 + c₄)⁴ (1 + φ)⁴`, absorbing the
Wiener-algebra constant `c₄` (`wiener_le`), the force radius and all numerical factors of the
error budget (`Main.lean`). -/
def kinC (φ : ℝ) : ℝ := 2 ^ 20 * (1 + c4) ^ 4 * (1 + φ) ^ 4

/-- Role 22: the coefficient floor `1` (`q ≥ 1`). -/
def role22 : ℝ := 1

/-- Role 23: the force filter through `H³`, `4φ` (`‖ψ‖_j ≤ φ/q ≤ 1/4`). -/
def role23 (φ : ℝ) : ℝ := 4 * φ

/-- Role 24: `2¹² Y`, with the total `H²` cap `Y ↦ y + B_S`. -/
def role24 (caps : Caps) : ℝ := 2 ^ 12 * (cp caps.yF + cp caps.BS)

/-- Role 25: `2²⁰ y²` (NEW385; it also pays every actual `R_S` `H²` trace before feedback). -/
def role25 (caps : Caps) : ℝ := 2 ^ 20 * cp caps.yF ^ 2

/-- Role 26: `2⁹ φ`. -/
def role26 (φ : ℝ) : ℝ := 2 ^ 9 * φ

/-- Role 27: `2⁵ C_A Y φ`, `C_A ↦ c₄`, `Y ↦ y + B_S`. -/
def role27 (φ : ℝ) (caps : Caps) : ℝ := 2 ^ 5 * c4 * (cp caps.yF + cp caps.BS) * φ

/-- Row 36, the raised kinetic domain `64 Q₀'` with
`Q₀' = T² + Tφ + T + S₀(R + R^{3/2} + T) + R A_S` (`T = y`, `S₀ = B_S`, `R = ρ`). -/
def role36 (μ φ : ℝ) (caps : Caps) : ℝ :=
  let ρ := rhoOf μ φ
  let Y := cp caps.yF
  64 * (Y ^ 2 + Y * φ + Y + cp caps.BS * (ρ + ρ * Real.sqrt ρ + Y) + ρ * cp caps.AS)

/-- The raised kinetic floor of eq. quant-kinetic-floor,
`W_S(M_∞ + D₄ + y) + M_∞ A_S + y²` with `M_∞ ↦ W_S` and `D₄ ↦ ρ + √(ρ(B_S + 1)) + 1`
(`D₄ = C[R + √(R(B_S + δ₀)) + δ₀]`, `δ₀ ↦ 1`). -/
def kineticFloor (μ φ : ℝ) (caps : Caps) : ℝ :=
  let ρ := rhoOf μ φ
  let W := cp caps.WS
  W * (W + (ρ + Real.sqrt (ρ * (cp caps.BS + 1)) + 1) + cp caps.yF) + W * cp caps.AS +
    cp caps.yF ^ 2

/-- The Fourier-side error budget of the Lean proof (`Main.lean`, terms (a)–(h) of the
derivative of `W₀`): coercivity `q ≳ W_S`; `⟨AS, N(F,F)⟩ ≲ B_S y`; the two
`Q(y,y)`-terms `≲ y(A_S + P_F + 1)(W_S + y + 1)` and `W_S(A_S + P_F + 1)(W_S + y + 1)`
(fixed-slow-output Cauchy, `‖Q(y,y)‖₀ ≤ 2‖y‖₁𝒜(y)`); `⟨S, N(AF,F)⟩ ≲ W_S y`; the force
terms `≲ (A_S + P_F + W_S + y) + 1`.  `W_F ≤ c₄ y` is used for the fast Wiener norm. -/
def fourierFloor (caps : Caps) : ℝ :=
  let P := cp caps.PF
  let Y := cp caps.yF
  let A := cp caps.AS
  let B := cp caps.BS
  let W := cp caps.WS
  W + B * Y + Y * (A + P + 1) * (W + Y + 1) + W * (A + P + 1) * (W + Y + 1) + W * Y +
    (A + P + W + Y) + 1

/-- **The kinetic role threshold** `q₀(μ, φ, caps)`: the six proper kinetic floors (roles 22–27),
the raised floor (row 36 and eq. quant-kinetic-floor) and the Lean error budget, times the loose
constant `kinC φ`.  Degree `5β − 3/2 < d = 7β − 3` (`kinetic_degree`, `Main.lean`). -/
def kinThreshold (μ φ : ℝ) (caps : Caps) : ℝ :=
  kinC φ * (role22 + role23 φ + role24 caps + role25 caps + role26 φ + role27 φ caps +
    role36 μ φ caps + kineticFloor μ φ caps + fourierFloor caps)

lemma one_le_kinC (φ : ℝ) (hφ : 0 ≤ φ) : 1 ≤ kinC φ := by
  have h4 := c4_pos
  have h1 : (1 : ℝ) ≤ (1 + c4) ^ 4 := one_le_pow₀ (by linarith)
  have h2 : (1 : ℝ) ≤ (1 + φ) ^ 4 := one_le_pow₀ (by linarith)
  unfold kinC
  nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity)]

lemma rhoOf_nonneg {μ φ : ℝ} (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) : 0 ≤ rhoOf μ φ := by
  unfold rhoOf; linarith

lemma role36_nonneg {μ φ : ℝ} (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) (caps : Caps) : 0 ≤ role36 μ φ caps := by
  have := rhoOf_nonneg hμ hφ
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.BS
  have := cp_nonneg caps.AS
  have := Real.sqrt_nonneg (rhoOf μ φ)
  unfold role36
  positivity

lemma kineticFloor_nonneg {μ φ : ℝ} (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) (caps : Caps) :
    0 ≤ kineticFloor μ φ caps := by
  have := rhoOf_nonneg hμ hφ
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.BS
  have := cp_nonneg caps.AS
  have := cp_nonneg caps.WS
  have := Real.sqrt_nonneg (rhoOf μ φ * (cp caps.BS + 1))
  unfold kineticFloor
  positivity

lemma fourierFloor_nonneg (caps : Caps) : 0 ≤ fourierFloor caps := by
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.BS
  have := cp_nonneg caps.AS
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.PF
  unfold fourierFloor
  positivity

/-- Role 22 is paid: `1 ≤ q₀`. -/
lemma one_le_kinThreshold {μ φ : ℝ} (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) (caps : Caps) :
    1 ≤ kinThreshold μ φ caps := by
  have h1 := one_le_kinC φ hφ
  have h2 := role36_nonneg hμ hφ caps
  have h3 := kineticFloor_nonneg hμ hφ caps
  have h4 := fourierFloor_nonneg caps
  have h5 : 0 ≤ role23 φ + role24 caps + role25 caps + role26 φ + role27 φ caps := by
    have := cp_nonneg caps.yF
    have := cp_nonneg caps.BS
    have := c4_pos
    unfold role23 role24 role25 role26 role27
    positivity
  unfold kinThreshold role22
  nlinarith

/-- Coercivity payment: `16 W_S ≤ q₀` (used for `|2⟨N(F,F),S⟩| ≤ ¼‖F‖₀²`, `Main.lean`). -/
lemma wiener_cap_le_kinThreshold {μ φ : ℝ} (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) (caps : Caps) :
    16 * cp caps.WS ≤ kinThreshold μ φ caps := by
  have h1 := one_le_kinC φ hφ
  have h2 := role36_nonneg hμ hφ caps
  have h3 := kineticFloor_nonneg hμ hφ caps
  have h5 : 0 ≤ role22 + role23 φ + role24 caps + role25 caps + role26 φ + role27 φ caps := by
    have := cp_nonneg caps.yF
    have := cp_nonneg caps.BS
    have := c4_pos
    unfold role22 role23 role24 role25 role26 role27
    positivity
  have h6 : cp caps.WS ≤ fourierFloor caps := by
    have := cp_nonneg caps.yF
    have := cp_nonneg caps.BS
    have := cp_nonneg caps.AS
    have := cp_nonneg caps.WS
    have := cp_nonneg caps.PF
    unfold fourierFloor
    nlinarith [mul_nonneg (cp_nonneg caps.BS) (cp_nonneg caps.yF),
      mul_nonneg (mul_nonneg (cp_nonneg caps.yF) (by positivity : 0 ≤ cp caps.AS + cp caps.PF + 1))
        (by positivity : 0 ≤ cp caps.WS + cp caps.yF + 1),
      mul_nonneg (mul_nonneg (cp_nonneg caps.WS) (by positivity : 0 ≤ cp caps.AS + cp caps.PF + 1))
        (by positivity : 0 ≤ cp caps.WS + cp caps.yF + 1),
      mul_nonneg (cp_nonneg caps.WS) (cp_nonneg caps.yF)]
  have hW := cp_nonneg caps.WS
  have h7 : 16 * cp caps.WS ≤ kinC φ * fourierFloor caps := by
    have h8 : (16 : ℝ) ≤ kinC φ := by
      unfold kinC
      have := c4_pos
      have h1 : (1 : ℝ) ≤ (1 + c4) ^ 4 := one_le_pow₀ (by linarith)
      have h2 : (1 : ℝ) ≤ (1 + φ) ^ 4 := one_le_pow₀ (by linarith)
      nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity)]
    calc 16 * cp caps.WS ≤ kinC φ * cp caps.WS := mul_le_mul_of_nonneg_right h8 hW
      _ ≤ kinC φ * fourierFloor caps := mul_le_mul_of_nonneg_left h6 (by linarith)
  unfold kinThreshold
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ kinC φ) (add_nonneg (add_nonneg h5 h2) h3)]

end Quant

end OVNS

end
