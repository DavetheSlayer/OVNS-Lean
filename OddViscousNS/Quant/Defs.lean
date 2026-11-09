import OddViscousNS.Closed.Defs

/-!
# Theorem 1.2 — the plane-curve count, as a statement

The manuscript's proof of Theorem 1.2 cites two published counting theorems
(`handoff/EXTERNAL_ANALYTIC_INPUTS.md`).

* `PlaneCurveCount` is stated here as eq. (3) of Browning–Heath-Brown, *Plane curves in boxes and
  equal sums of two powers*, in its affine specialization (manuscript Lemma `quant-plane`).  That
  paper does not prove it (its Section 2 assumes `P₁ > 1`): the source is Heath-Brown, LNM 1891,
  Theorem 15, which as quoted carries a factor `(log‖F‖)^{2n−3}`.  It is proved in Lean
  (`Arith/Plane/PlaneCount.lean`).
* The surface covering of Browning–Verzobio, *Counting integer points on affine surfaces with a
  side condition*, Theorem 1.1 at modulus one (manuscript Lemma `quant-surface`), is not used: a
  specialized determinant argument replaces its one use (`Arith/Surface/`).

Neither is a hypothesis of Theorem 1.2 (`OddViscousNS/Quant.lean`).  No axiom is declared.
-/

open MvPolynomial

noncomputable section

namespace OVNS

/-- Absolute irreducibility of an integer polynomial: irreducible over `\bar ℚ`. -/
def AbsIrred {n : ℕ} (F : MvPolynomial (Fin n) ℤ) : Prop :=
  Irreducible (MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ)) F)

/-- The box size `𝔗 = max {∏ Bᵢ^{eᵢ} : X^e occurs in F}` (as a real number; `sSup ∅ = 0` for
`F = 0`). -/
def boxSize {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (B : Fin n → ℝ) : ℝ :=
  sSup ((fun e : Fin n →₀ ℕ => ∏ i, B i ^ (e i)) '' (F.support : Set (Fin n →₀ ℕ)))

/-- The integer points of the box `|xᵢ| ≤ Bᵢ`. -/
def boxPts (n : ℕ) (B : Fin n → ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (-⌊B i⌋) ⌊B i⌋

/-- The integer zeros of `F` in the box. -/
def boxZeros {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (B : Fin n → ℝ) : Finset (Fin n → ℤ) := by
  classical
  exact (boxPts n B).filter fun x => MvPolynomial.eval x F = 0

/-- **Lemma `quant-plane`** (Heath-Brown, LNM 1891, Theorem 15, in the form of Browning–Heath-Brown
eq. (3), affine; see the module docstring). For every degree `d ≥ 1`
and `η > 0` there is `C` such that every absolutely irreducible `F ∈ ℤ[X,Y]` of degree `d` has at
most `C B₂^η exp(log B₁ log B₂ / log 𝔗)` integer zeros in the box `|X| ≤ B₁`, `|Y| ≤ B₂`,
`2 ≤ B₁ ≤ B₂`. -/
def PlaneCurveCount : Prop :=
  ∀ (d : ℕ) (η : ℝ), 1 ≤ d → 0 < η → ∃ C : ℝ, ∀ F : MvPolynomial (Fin 2) ℤ,
    F.totalDegree = d → AbsIrred F → ∀ B : Fin 2 → ℝ, 2 ≤ B 0 → B 0 ≤ B 1 →
      ((boxZeros F B).card : ℝ) ≤
        C * B 1 ^ η * Real.exp (Real.log (B 0) * Real.log (B 1) / Real.log (boxSize F B))

end OVNS
