import OddViscousNS.Closed.Forced.Defs
import OddViscousNS.Closed.RowChain

/-!
# Moment-regime cubic bounds — definitions

For a probability `P` on the nonzero modes (even, `P 0 = 0`) with `t = ∑ P_j/|j|²`, the weighted
Cauchy–Schwarz with weight `ξ_k = 1 + a t |k|² + bL/h_k` turns the row chain
`∑_k √(Q_k g_k R_k)` into `(1 + a + bL·X/Y) · S₂`, where `S₂ = E_{P⊗P}[1_{p×ℓ≠0} g(u)/ξ(u)]`
(`u = p + ℓ`).  Averaging over the reflection `ℓ ↦ −ℓ` gives the pair value
`T(p,ℓ) = ½[g(|p+ℓ|²)/ξ(p+ℓ) + g(|p−ℓ|²)/ξ(p−ℓ)]`, and the expectation argument with
`V(p,ℓ) = (|p|⁻² + |ℓ|⁻²)/(2t)` (`E V = 1`) bounds `S₂ ≤ K` whenever `T − λ(V − 1) ≤ K` on
non-collinear pairs and `0 ≤ λ ≤ K`.  `W(p,ℓ) = 2/(t(|p|² + |ℓ|²)) ≤ V(p,ℓ)`.
-/

noncomputable section

namespace OVNS

namespace Forced

/-- The weight `ξ_k = 1 + a t |k|² + bL/h_k` (`bL` is the product `b·L`). -/
def xiM (a bL t : ℝ) (k : Mode) : ℝ := 1 + a * t * absSq k + bL / hm k

/-- The pair value `T(p,ℓ) = ½[g(|p+ℓ|²)/ξ(p+ℓ) + g(|p−ℓ|²)/ξ(p−ℓ)]`. -/
def Tpair (g : ℕ → ℝ) (a bL t : ℝ) (p l : Mode) : ℝ :=
  (g (nsq (p + l)) / xiM a bL t (p + l) + g (nsq (p - l)) / xiM a bL t (p - l)) / 2

/-- `V(p,ℓ) = (|p|⁻² + |ℓ|⁻²)/(2t)`. -/
def Vpair (t : ℝ) (p l : Mode) : ℝ := (1 / absSq p + 1 / absSq l) / (2 * t)

/-- `W(p,ℓ) = 2/(t(|p|² + |ℓ|²))`. -/
def Wpair (t : ℝ) (p l : Mode) : ℝ := 2 / (t * (absSq p + absSq l))

/-- Non-collinearity of a pair of modes. -/
def NonColl (p l : Mode) : Prop := cross (modeVec p) (modeVec l) ≠ 0

/-- The pointwise moment hypothesis: `T − λ(W − 1) ≤ K` on all non-collinear pairs of
nonzero modes (with `W` in place of `V`, which is stronger since `W ≤ V`). -/
def PointwiseW (g : ℕ → ℝ) (a bL t lam K : ℝ) : Prop :=
  ∀ p l : Mode, p ≠ 0 → l ≠ 0 → NonColl p l → Tpair g a bL t p l - lam * (Wpair t p l - 1) ≤ K

end Forced

end OVNS
