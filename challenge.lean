import Mathlib

/-!
# Challenge file: Theorems 1.1, 1.2 and 1.3 of the OVNS manuscript
# 3D Navier–Stokes with large odd viscosity on the cubic torus

This file is the complete **trusted base** of the formal theorems of the OVNS manuscript, in a
single self-contained file that imports only Mathlib. Beyond Mathlib it introduces exactly
**eight definitions**: `hsE`, `Adm`, `ContH`, `L2locH`, `IsStrongSolution`,
`SmoothAtPositiveTimes`, `GlobalConclusion` (the conclusion of Theorem 1.1 for one datum, one force
and one bound) and the metric `hm`.
Everything else is expressed with Mathlib's own notions: `EuclideanSpace ℂ (Fin 3)` for `ℂ³`,
its norm and inner product, `Submodule.starProjection` for the orthogonal projection onto `k^⊥`
(the Leray symbol), `crossProduct` for `e₃ × ·`, `tsum` over `ℤ³`, `HasDerivWithinAt`,
`ContDiffOn`, `iteratedDerivWithin`, and the lower Lebesgue integral. Three `local notation`s
(`Field`, `κ`, `P`) are macros for readability; they add no constants to the statements.

It states five theorems, each with its proof replaced by `sorry`:

* `global_regularity`: Theorem 1.1, norm-uniform global regularity;
* `quantitative_fixed_force`, `quantitative_joint_force`: Theorem 1.2, explicit sufficient
  thresholds `𝓡_gen(μ, φ)`;
* `closed_regions_unforced`, `closed_regions_forced`: Theorem 1.3, Theorem 1.1 with threshold `0`
  on explicit bounded regions.

Anyone who replaces those `sorry`s by proofs using no additional axioms has proved the theorems.

## Status

All five are proved. `solution.lean` repeats the definitions and statements below word for word
and replaces each `sorry` by a proof, with no axioms beyond `propext`, `Classical.choice`,
`Quot.sound`. Its proofs come from the `OddViscousNS` library of this repository. The many
definitions used inside the library (helical basis, filtered equation, normal forms, correctors,
energies, certificates, …) do not appear here, and a `def` cannot affect soundness, so none of them
has to be trusted in order to trust the theorems.

The namespace is `Challenge`, not `OVNS`, because `solution.lean` imports the library, which uses
`OVNS`.

## Reading guide: statement ↔ manuscript

### The model, for all three theorems

* The model is the manuscript's own Fourier-side model. A vector field on `𝕋³ = (ℝ/2πℤ)³` *is*
  its family of Fourier coefficients `Field = (ℤ³ → ℂ³)`, and a solution is *defined* by the
  mode equations (eq:mode). Nothing in this file refers to functions on the torus.
* `κ k ∈ ℂ³` is the wave vector `k ∈ ℤ³`, so `‖κ k‖ = |k|` and `⟪κ k, v⟫_ℂ = k · v` (bilinear,
  since `κ k` is real). `P k = ` orthogonal projection onto `k^⊥` is the Leray symbol `P_k`.
* `hsE s u = ‖u‖_s² = ∑_{k≠0} |k|^{2s} |û_k|² ∈ [0, ∞]` is the squared coefficient `H^s` norm of
  Section 1 (homogeneous: the mean mode `k = 0` is excluded, as all fields are mean-zero).
  Being `[0,∞]`-valued it needs no summability side condition: `hsE s u < ∞` *is* `u ∈ H^s`.
* `Adm s u`: real (`û_{-k} = conj û_k`), mean-zero, divergence-free (`k · û_k = 0`), in `H^s`.
* `IsStrongSolution ν α f u₀ u`: `u ∈ C([0,∞); H²_sol)`, `u(0) = u₀`, and every mode solves
  `d/dt û_k = -ν|k|² û_k + α P_k(e₃ × (-|k|² û_k)) - P_k ∑_{p+q=k} (i q·û_p) û_q + f̂_k`,
  i.e. `∂ₜu + ℙ((u·∇)u) = νΔu + αLu + f` with `L = ℙ(e₃ × Δ)` (eq:original-forced), with the
  derivative one-sided at `t = 0`.
* Time integrals are Lebesgue lower integrals `∫⁻` of `ℝ≥0∞`-valued integrands, so the statement
  needs no measurability hypotheses.

### Theorem 1.1

* In the theorem, `R` is `𝓡_gen(M/ν, F/ν²)`; `‖u₀‖₂ ≤ M` is written `hsE 2 u₀ ≤ ofReal M ^ 2`;
  `ν · Bd (M/ν) (F/ν²)` is the uniform `H¹`/`H²` bound and `ν ⌈νh⌉ · Bd (M/ν) (F/ν²)` bounds
  `∫_t^{t+h} ‖u‖₃²` on every sliding window. For `f = 0`, initial `H^s` regularity (`s ≥ 2`)
  persists: `u t ∈ H^s` for all `t ≥ 0`, continuously, with `u ∈ L²_loc H^{s+1}`.

### Theorem 1.2

* `GlobalConclusion ν α f u₀ Bd` is the conclusion of Theorem 1.1 for the datum `u₀`, the force
  `f`, the coefficient `α`, with bound `Bd`. "`𝓡_gen(μ, φ) ≤ ρ` is a sufficient choice" is
  formalized as: every real mean-zero divergence-free `H²` datum and steady force with
  `‖u₀‖₂ ≤ M`, `‖f‖₂ ≤ F`, `μ = M/ν`, `φ = F/ν²`, and every real `α` with `|α|/ν ≥ ρ`, has
  `GlobalConclusion` with a bound `Bd(μ, φ)`. (`‖u₀‖₂ ≤ M` is written `hsE 2 u₀ ≤ ofReal M ^ 2`.)
* `quantitative_fixed_force` (eq:fixed-force-power): for each `φ ≥ 0` and `ε > 0` there is
  `C = C_{φ,ε}` such that `𝓡_gen(μ, φ') ≤ C (1+μ)^{9876/719+ε}` for all `μ ≥ 0`, `φ' ≤ φ`.
* `quantitative_joint_force` (eq:joint-force): with `X = e^e + μ`, `R = X + φ`,
  `U = X^{1719/719}`, there are absolute `C, C₀, R₀ > 0` such that on `R ≥ max(R₀, X²⁴)`,
  `𝓡_gen(μ, φ) ≤ C U R³ exp(C₀ log R / log log R)`.

### Theorem 1.3

* The metric `h` (Section "Weighted energy"): `1000·h(j)` is tabulated for `1 ≤ j ≤ 32` and
  `h(j) = 29j/100 + 117/500` for `j ≥ 33`; `hm k = h(|k|²)` (`hm 0 = 0` is a convention; the zero
  mode never enters). With `A = −Δ`, for a scaled field `w`,
  `Y(w) = ⟨h(A)w, w⟩ = ∑_k h(|k|²)|ŵ_k|²` and `Z(w) = ⟨A h(A)w, w⟩ = ∑_k |k|² h(|k|²)|ŵ_k|²`, both
  in `[0,∞]`. They are written out in the theorems for the scaled solution
  `w(τ) = u(τ/ν)/(νs)`, i.e. `u(t) = ν s w(νt)`, as `((1/(νs) : ℝ) : ℂ) • u (τ/ν)`.
* Forced table: each row is `(208013 μ_max, 208013 φ_max, J)`; the closed rectangle is
  `208013 M/ν ≤ 208013 μ_max`, `208013 F/ν² ≤ 208013 φ_max`; the scaling is `s = μ_max`; and
  `∫_I Z(w) dτ ≤ J` on every normalized interval `I = [a, b] ⊆ [0,∞)` with `b − a ≤ 1`. In the
  unforced branch `s = 97/40`, `Y(w(τ)) ≤ 1` for all `τ ≥ 0` and `∫₀^∞ Z(w) dτ ≤ 100000`.
* The theorems hold for every fixed real `α`, including `0` and both signs; the bound `Bd` is
  uniform in `α` (and, in the forced branch, in the row). All endpoint equalities are included.
-/

open scoped ComplexConjugate ENNReal Topology InnerProductSpace Matrix
open MeasureTheory Set Filter

noncomputable section

namespace Challenge

/- Notation. These are macros: they introduce no new constants. -/

-- A vector field on `𝕋³ = (ℝ/2πℤ)³`, given by its Fourier coefficients `û_k ∈ ℂ³`, `k ∈ ℤ³`.
local notation "Field" => (Fin 3 → ℤ) → EuclideanSpace ℂ (Fin 3)

-- The wave vector `k ∈ ℤ³` as an element of `ℂ³`; in particular `‖κ k‖ = |k|`.
local notation:max "κ" k:max =>
  (WithLp.toLp 2 fun i => ((k : Fin 3 → ℤ) i : ℂ) : EuclideanSpace ℂ (Fin 3))

-- The Leray symbol `P_k`: the orthogonal projection of `ℂ³` onto `k^⊥`.
local notation:max "P" k:max => Submodule.starProjection (ℂ ∙ κ k)ᗮ

/-- `‖u‖_s² = ∑_{k ≠ 0} |k|^{2s} |û_k|² ∈ [0, ∞]`, the squared homogeneous `H^s` coefficient norm. -/
def hsE (s : ℝ) (u : Field) : ℝ≥0∞ :=
  ∑' k, if k = 0 then 0 else ENNReal.ofReal (‖κ k‖ ^ (2 * s) * ‖u k‖ ^ 2)

/-- Real, mean-zero, divergence-free fields in `H^s`. -/
structure Adm (s : ℝ) (u : Field) : Prop where
  finite : hsE s u < ∞
  real : ∀ k i, u (-k) i = conj (u k i)
  sol : ∀ k, ⟪κ k, u k⟫_ℂ = 0
  mean : u 0 = 0

/-- `t ↦ u t` is continuous on `[0,∞)` with values in `H^s`. -/
def ContH (s : ℝ) (u : ℝ → Field) : Prop :=
  ∀ t₀ ∈ Ici (0 : ℝ), Tendsto (fun t => hsE s (u t - u t₀)) (𝓝[Ici 0] t₀) (𝓝 0)

/-- `u ∈ L²_loc([0,∞); H^s)`. -/
def L2locH (s : ℝ) (u : ℝ → Field) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∫⁻ t in Icc 0 T, hsE s (u t) < ∞

/-- A global strong solution in `C([0,∞); H²_sol)` of
`∂ₜu + ℙ((u·∇)u) = νΔu + αLu + f`, `u(0) = u₀`, where `L = ℙ(e₃ × Δ)`: every Fourier coefficient
is differentiable on `[0,∞)` (one-sided at `0`) and satisfies its mode equation
`d/dt û_k = -ν|k|² û_k + α P_k(e₃ × (-|k|² û_k)) - P_k ∑_{p+q=k} (i q·û_p) û_q + f̂_k`. -/
structure IsStrongSolution (ν α : ℝ) (f u₀ : Field) (u : ℝ → Field) : Prop where
  init : u 0 = u₀
  adm : ∀ t, 0 ≤ t → Adm 2 (u t)
  cont : ContH 2 u
  mode : ∀ k t, 0 ≤ t → HasDerivWithinAt (fun s => u s k)
    ((-(ν * ‖κ k‖ ^ 2 : ℝ) : ℂ) • u t k
      + (α : ℂ) • P k (WithLp.toLp 2
          (![0, 0, 1] ⨯₃ WithLp.ofLp ((-((‖κ k‖ ^ 2 : ℝ) : ℂ)) • u t k)))
      - P k (∑' p, (Complex.I * ⟪κ (k - p), u t p⟫_ℂ) • u t (k - p))
      + f k) (Ici 0) t

/-- Smoothness at positive times, in the form equivalent to `u ∈ C^∞((0,∞) × 𝕋³)`:
each mode is smooth in time, and every time derivative lies in every `H^r`, locally uniformly
on `(0,∞)`. -/
def SmoothAtPositiveTimes (u : ℝ → Field) : Prop :=
  (∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => u t k) (Ioi 0)) ∧
  ∀ (j : ℕ) (r a b : ℝ), 0 < a → a ≤ b → ∃ C : ℝ, ∀ t ∈ Icc a b,
    hsE r (fun k => iteratedDerivWithin j (fun s => u s k) (Ioi 0) t) ≤ ENNReal.ofReal C

/-- The conclusion of Theorem 1.1 for the datum `u₀`, the steady force `f`, the coefficient `α`
and the bound `Bd`: a unique global strong solution in `C([0,∞);H²) ∩ L²_loc H³`, uniform
`H¹, H²` bounds `‖u(t)‖₁, ‖u(t)‖₂ ≤ ν·Bd`, sliding `H³` square integrals
`∫_t^{t+h} ‖u‖₃² ≤ ν⌈νh⌉·Bd`, and for `f = 0` persistence of every `H^s`, `s ≥ 2` (continuously,
with `u ∈ L²_loc H^{s+1}`), together with smoothness at positive times. -/
def GlobalConclusion (ν α : ℝ) (f u₀ : Field) (Bd : ℝ) : Prop :=
  ∃ u : ℝ → Field, IsStrongSolution ν α f u₀ u ∧
    (∀ u', IsStrongSolution ν α f u₀ u' → ∀ t, 0 ≤ t → u' t = u t) ∧ L2locH 3 u ∧
    (∀ t, 0 ≤ t → hsE 1 (u t) ≤ ENNReal.ofReal (ν * Bd) ^ 2 ∧
      hsE 2 (u t) ≤ ENNReal.ofReal (ν * Bd) ^ 2) ∧
    (∀ t h : ℝ, 0 ≤ t → 0 ≤ h →
      ∫⁻ s in Icc t (t + h), hsE 3 (u s) ≤ ENNReal.ofReal (ν * ⌈ν * h⌉ * Bd)) ∧
    (f = 0 → (∀ s, 2 ≤ s → hsE s u₀ < ∞ →
        (∀ t, 0 ≤ t → hsE s (u t) < ∞) ∧ ContH s u ∧ L2locH (s + 1) u) ∧
      SmoothAtPositiveTimes u)

/-- The metric `h(|k|²)` of Section "Weighted energy": `1000·h(j)` is tabulated for `1 ≤ j ≤ 32`
and `h(j) = 29j/100 + 117/500` for `j ≥ 33`; `h(0) = 0` is a convention (the zero mode never
enters). -/
def hm (k : Fin 3 → ℤ) : ℝ :=
  let j := ∑ i, (k i).natAbs ^ 2
  if j = 0 then 0
  else if j ≤ 32 then
    (([1000, 1569, 2042, 2462, 2847, 3205, 3543, 3864, 4171, 4467, 4752, 5029, 5297, 5559, 5814,
      6063, 6307, 6545, 6779, 7009, 7235, 7457, 7676, 7891, 8103, 8313, 8519, 8723, 8924, 9123,
      9319, 9514] : List ℕ).getD (j - 1) 0 : ℝ) / 1000
  else 29 * (j : ℝ) / 100 + 117 / 500

/-- **Theorem 1.1 (Norm-uniform global regularity).** -/
theorem global_regularity :
    ∃ R Bd : ℝ → ℝ → ℝ, (∀ μ φ, 0 ≤ R μ φ) ∧
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F →
        Adm 2 u₀ → Adm 2 f →
        hsE 2 u₀ ≤ ENNReal.ofReal M ^ 2 → hsE 2 f ≤ ENNReal.ofReal F ^ 2 →
        R (M / ν) (F / ν ^ 2) ≤ |α| / ν →
        ∃ u : ℝ → Field,
          IsStrongSolution ν α f u₀ u ∧
          (∀ u', IsStrongSolution ν α f u₀ u' → ∀ t, 0 ≤ t → u' t = u t) ∧
          L2locH 3 u ∧
          (∀ t, 0 ≤ t → hsE 1 (u t) ≤ ENNReal.ofReal (ν * Bd (M / ν) (F / ν ^ 2)) ^ 2 ∧
            hsE 2 (u t) ≤ ENNReal.ofReal (ν * Bd (M / ν) (F / ν ^ 2)) ^ 2) ∧
          (∀ t h : ℝ, 0 ≤ t → 0 ≤ h →
            ∫⁻ s in Icc t (t + h), hsE 3 (u s) ≤
              ENNReal.ofReal (ν * ⌈ν * h⌉ * Bd (M / ν) (F / ν ^ 2))) ∧
          (f = 0 → (∀ s, 2 ≤ s → hsE s u₀ < ∞ →
              (∀ t, 0 ≤ t → hsE s (u t) < ∞) ∧ ContH s u ∧ L2locH (s + 1) u) ∧
            SmoothAtPositiveTimes u) := by
  sorry


/-- **Theorem 1.2, fixed-force bound** (eq:fixed-force-power). For each normalized force radius
`φ ≥ 0` and each `ε > 0` there is `C = C_{φ,ε} < ∞` such that `|α|/ν ≥ C (1 + M/ν)^{9876/719+ε}`
is a sufficient choice in Theorem 1.1 for all data `‖u₀‖₂ ≤ M` and forces `‖f‖₂ ≤ F` with
`F/ν² ≤ φ`. -/
theorem quantitative_fixed_force :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ C : ℝ, ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hsE 2 u₀ ≤ ENNReal.ofReal M ^ 2 → hsE 2 f ≤ ENNReal.ofReal F ^ 2 → F / ν ^ 2 ≤ φ →
        C * (1 + M / ν) ^ ((9876 : ℝ) / 719 + ε) ≤ |α| / ν →
        GlobalConclusion ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  sorry

/-- **Theorem 1.2, joint large-force bound** (eq:joint-force). With `X = e^e + M/ν`,
`R = X + F/ν²`, `U = X^{1719/719}`, there are absolute constants `C, C₀, R₀ > 0` such that, when
`R ≥ max(R₀, X²⁴)`, `|α|/ν ≥ C U R³ exp(C₀ log R / log log R)` is a sufficient choice in
Theorem 1.1. -/
theorem quantitative_joint_force :
    ∃ C C₀ R₀ : ℝ, 0 < C ∧ 0 < C₀ ∧ 0 < R₀ ∧ ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hsE 2 u₀ ≤ ENNReal.ofReal M ^ 2 → hsE 2 f ≤ ENNReal.ofReal F ^ 2 →
        let X := Real.exp (Real.exp 1) + M / ν
        let R := X + F / ν ^ 2
        let U := X ^ ((1719 : ℝ) / 719)
        max R₀ (X ^ (24 : ℝ)) ≤ R →
        C * U * R ^ 3 * Real.exp (C₀ * Real.log R / Real.log (Real.log R)) ≤ |α| / ν →
        GlobalConclusion ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  sorry


/-- **Theorem 1.3, unforced branch.** For every fixed real `α` (including `0`, either sign) and
all real mean-zero divergence-free `H²` data with `‖u₀‖₂ ≤ M`, `0 ≤ M/ν ≤ 97/40`, the conclusion
of Theorem 1.1 holds with zero force and a bound `Bd` uniform in `α`; moreover, for every strong
solution `u`, the scaled solution `w(τ) = u(τ/ν)/(ν·97/40)` satisfies `Y(w(τ)) ≤ 1` for all
`τ ≥ 0` and `∫₀^∞ Z(w(τ)) dτ ≤ 100000`. -/
theorem closed_regions_unforced :
    ∃ Bd : ℝ, 0 ≤ Bd ∧
      ∀ (ν α M : ℝ) (u₀ : Field), 0 < ν → 0 ≤ M → Adm 2 u₀ → hsE 2 u₀ ≤ ENNReal.ofReal M ^ 2 →
        M / ν ≤ 97 / 40 →
        GlobalConclusion ν α 0 u₀ Bd ∧
        ∀ u : ℝ → Field, IsStrongSolution ν α 0 u₀ u →
          (∀ τ, 0 ≤ τ → ∑' k, ENNReal.ofReal
            (hm k * ‖((1 / (ν * (97 / 40)) : ℝ) : ℂ) • u (τ / ν) k‖ ^ 2) ≤ 1) ∧
          ∫⁻ τ in Ici 0, ∑' k, ENNReal.ofReal
            (‖κ k‖ ^ 2 * hm k * ‖((1 / (ν * (97 / 40)) : ℝ) : ℂ) • u (τ / ν) k‖ ^ 2) ≤ 100000 := by
  sorry

/-- **Theorem 1.3, forced branch.** Each row `(208013·μ_max, 208013·φ_max, J)` of the table is a
closed rectangle `M/ν ≤ μ_max`, `F/ν² ≤ φ_max` on which, for every fixed real `α`, the conclusion
of Theorem 1.1 holds with a bound `Bd` uniform in `α` and in the row; moreover, with `s = μ_max`,
the scaled solution `w(τ) = u(τ/ν)/(νs)` of every strong solution satisfies `∫_a^b Z(w(τ)) dτ ≤ J`
on every interval `0 ≤ a ≤ b ≤ a + 1`. -/
theorem closed_regions_forced : ∃ Bd : ℝ, 0 ≤ Bd ∧
    ∀ r ∈ ([(419650, 419650, 850), (425500, 382950, 294), (434000, 347200, 468),
        (442000, 309400, 320), (458500, 229250, 808), (478500, 119625, 355),
        (489500, 48950, 124)] : List (ℕ × ℕ × ℕ)),
      ∀ (ν α M F : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F →
        Adm 2 u₀ → Adm 2 f → hsE 2 u₀ ≤ ENNReal.ofReal M ^ 2 → hsE 2 f ≤ ENNReal.ofReal F ^ 2 →
        208013 * (M / ν) ≤ r.1 → 208013 * (F / ν ^ 2) ≤ r.2.1 →
        GlobalConclusion ν α f u₀ Bd ∧
        ∀ u : ℝ → Field, IsStrongSolution ν α f u₀ u →
          ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ a + 1 →
            ∫⁻ τ in Icc a b, ∑' k, ENNReal.ofReal (‖κ k‖ ^ 2 * hm k *
              ‖((1 / (ν * ((r.1 : ℝ) / 208013)) : ℝ) : ℂ) • u (τ / ν) k‖ ^ 2) ≤ r.2.2 := by
  sorry


end Challenge
