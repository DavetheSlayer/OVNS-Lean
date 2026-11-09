import OddViscousNS.Trilinear
import OddViscousNS.Quant.Arith.Squarefree

/-!
# The resonant coefficient `γ`, the sorted fibre and the weighted count `W(n)`

For a zero-sum triad `ℓ = (ℓ₀, ℓ₁, ℓ₂)` with helicity pattern `s`, the signed helical lengths are
`x_j = s_j |ℓ_j|`, `D = |ℓ₀ × ℓ₁|`, and the physical coefficient (manuscript eq. quant-gamma) is
`γ = D |(x₀+x₁+x₂)(x₀−x₁)(x₁−x₂)(x₂−x₀)| / (12√2 (|ℓ₀||ℓ₁||ℓ₂|)²)`.  `h₂ = e₁² − e₂` is the
complete symmetric polynomial of degree two.  A pattern is resonant when `∑ λ_{s_j}(ℓ_j) = 0`
(all-incoming convention); `gammaR ℓ` is `γ` of the resonant pattern (`0` off resonance, and
`½ ∑` over patterns since the two resonant patterns of a fast triad are opposite with equal `γ`).
`orbitSum σ ℓ A` is the six-ordering sum of the `|output|^{2σ}`-weighted triad form `tau`.
`SFib n k` is the sorted fast fibre of the largest output `n` indexed by the middle leg `k`
(`m = −k − n`), `Wfib n = ∑_{fibre} γ²`, and `WeightedCount` is Lemma quant-weighted
`W(n) ≤ C_η |n|^{p* + η}` as a hypothesis.
-/

noncomputable section

namespace OVNS.Quant

/-- The legs of the triad indexed by `(p, q)`: `(p, q, −(p+q))`. -/
def legs (x : Mode × Mode) : Fin 3 → Mode := ![x.1, x.2, -(x.1 + x.2)]

/-- The integer cross product. -/
def crossZ (p q : Mode) : Mode :=
  ![p 1 * q 2 - p 2 * q 1, p 2 * q 0 - p 0 * q 2, p 0 * q 1 - p 1 * q 0]

/-- `D = |p × q|`. -/
def areaM (p q : Mode) : ℝ := absk (crossZ p q)

/-- Signed helical lengths `x_j = s_j |ℓ_j|`. -/
def sl (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) (j : Fin 3) : ℝ := sg (s j) * absk (ℓ j)

/-- The physical coefficient `γ` (eq. quant-gamma). -/
def gammaC (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) : ℝ :=
  areaM (ℓ 0) (ℓ 1) * |(sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2) * (sl ℓ s 0 - sl ℓ s 1) *
      (sl ℓ s 1 - sl ℓ s 2) * (sl ℓ s 2 - sl ℓ s 0)| /
    (12 * Real.sqrt 2 * (absk (ℓ 0) * absk (ℓ 1) * absk (ℓ 2)) ^ 2)

/-- `h₂ = e₁² − e₂ = x₀² + x₁² + x₂² + x₀x₁ + x₁x₂ + x₂x₀`. -/
def h2C (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) : ℝ :=
  sl ℓ s 0 ^ 2 + sl ℓ s 1 ^ 2 + sl ℓ s 2 ^ 2 +
    sl ℓ s 0 * sl ℓ s 1 + sl ℓ s 1 * sl ℓ s 2 + sl ℓ s 2 * sl ℓ s 0

/-- The resonance condition of a helicity pattern. -/
def ResPat (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) : Prop := ∑ j, lam (s j) (ℓ j) = 0

instance (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) : Decidable (ResPat ℓ s) := by
  unfold ResPat; infer_instance

/-- The per-triad coefficient (half the sum over resonant patterns). -/
def gammaR (ℓ : Fin 3 → Mode) : ℝ :=
  (1 / 2) * ∑ s : Fin 3 → Sgn, if ResPat ℓ s then gammaC ℓ s else 0

/-- The `H²` coefficient `γ |h₂|` (half the sum over resonant patterns). -/
def gammaR2 (ℓ : Fin 3 → Mode) : ℝ :=
  (1 / 2) * ∑ s : Fin 3 → Sgn, if ResPat ℓ s then gammaC ℓ s * |h2C ℓ s| else 0

/-- The six-ordering orbit sum of the `|output|^{2σ}`-weighted triad form. -/
def orbitSum (σ : ℝ) (ℓ : Fin 3 → Mode) (A : Fin 3 → V3) : ℂ :=
  ∑ π : Equiv.Perm (Fin 3),
    ((sobWeight σ (ℓ (π 2)) : ℝ) : ℂ) * tau (ℓ (π 0)) (ℓ (π 1)) (A (π 0)) (A (π 1)) (A (π 2))

/-- The sorted fast fibre of the largest output `n`, indexed by the middle leg `k` (`m = −k−n`). -/
def SFib (n k : Mode) : Prop :=
  absk (-k - n) ≤ absk k ∧ absk k ≤ absk n ∧ n 2 ≠ 0 ∧ k 2 ≠ 0 ∧ (-k - n) 2 ≠ 0

instance (n k : Mode) : Decidable (SFib n k) := by unfold SFib; infer_instance

/-- `W(n) = ∑_{sorted fibre} γ²`. -/
def Wfib (n : Mode) : ℝ := ∑' k : Mode, if SFib n k then gammaR ![-k - n, k, n] ^ 2 else 0

/-- **Lemma quant-weighted** as a hypothesis: `W(n) ≤ C_η |n|^{p* + η}`. -/
def WeightedCount : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Mode, n ≠ 0 → Wfib n ≤ C * absk n ^ (pStar + η)

/-- The derivative-weighted amplitude `u_k = |k| ‖F_k‖`. -/
def uAmp (F : Field) (k : Mode) : ℝ := absk k * ‖F k‖

end OVNS.Quant

end
