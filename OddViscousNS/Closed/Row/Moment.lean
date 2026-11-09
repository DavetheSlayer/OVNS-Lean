import OddViscousNS.Closed.Row.Sym

/-!
# The second-moment identity over symmetric lattice sets

For `φ ≥ 0` invariant under the signed permutations,
`3 ∑ (p·v)² φ(p) = |v|² ∑ |p|² φ(p)` in `[0,∞]`.  Sign flips kill the cross terms and cyclic
permutations equalize the three squares.  There is no subtraction, so no summability is needed.
-/

open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

lemma tsum_act {σ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ℤ} (hε : ∀ i, ε i * ε i = 1)
    (F : Mode → ℝ≥0∞) : ∑' p, F (act σ ε p) = ∑' p, F p :=
  (actEquiv σ ε hε).tsum_eq F

/-- Invariance under all signed permutations. -/
def SymFn (φ : Mode → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℤ), (∀ i, ε i * ε i = 1) → ∀ p, φ (act σ ε p) = φ p

/-- The three sign flips, as `act 1 ε`. -/
private def flip1 : Fin 3 → ℤ := ![1, 1, -1]
private def flip2 : Fin 3 → ℤ := ![1, -1, 1]
private def flip3 : Fin 3 → ℤ := ![1, -1, -1]

private lemma flip1_sq : ∀ i, flip1 i * flip1 i = 1 := by decide
private lemma flip2_sq : ∀ i, flip2 i * flip2 i = 1 := by decide
private lemma flip3_sq : ∀ i, flip3 i * flip3 i = 1 := by decide
private lemma one_sq : ∀ i : Fin 3, (fun _ => (1 : ℤ)) i * (fun _ => (1 : ℤ)) i = 1 := by
  intro i; norm_num

private lemma flip_identity (p : Mode) (v : R3) :
    dR p v ^ 2 + dR (act 1 flip1 p) v ^ 2 + dR (act 1 flip2 p) v ^ 2 + dR (act 1 flip3 p) v ^ 2 =
      4 * (v 0 ^ 2 * (p 0 : ℝ) ^ 2 + v 1 ^ 2 * (p 1 : ℝ) ^ 2 + v 2 ^ 2 * (p 2 : ℝ) ^ 2) := by
  simp [dR, act, flip1, flip2, flip3, Fin.sum_univ_three]
  ring

/-- The coordinate moments. -/
def mom (φ : Mode → ℝ) (i : Fin 3) : ℝ≥0∞ := ∑' p, ENNReal.ofReal ((p i : ℝ) ^ 2 * φ p)

private lemma mom_swap {φ : Mode → ℝ} (hφ : SymFn φ) (i j : Fin 3) : mom φ i = mom φ j := by
  unfold mom
  rw [← tsum_act (σ := Equiv.swap i j) (ε := fun _ => 1) one_sq]
  refine tsum_congr fun p => ?_
  rw [hφ _ _ one_sq]
  simp [act]

private lemma three_mom {φ : Mode → ℝ} (hφ0 : ∀ p, 0 ≤ φ p) (i : Fin 3) (hφ : SymFn φ) :
    3 * mom φ i = ∑' p, ENNReal.ofReal (absSq p * φ p) := by
  have h0 := mom_swap hφ i 0
  have h1 := mom_swap hφ i 1
  have h2 := mom_swap hφ i 2
  have e : (3 : ℝ≥0∞) * mom φ i = mom φ 0 + mom φ 1 + mom φ 2 := by
    rw [← h0, ← h1, ← h2]; ring
  rw [e]
  unfold mom
  rw [← tsum_add, ← tsum_add]
  refine tsum_congr fun p => ?_
  have := hφ0 p
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  simp only [absSq, Fin.sum_univ_three]
  ring

/-- `∑ (p·v)² φ = ∑ᵢ vᵢ² mᵢ`. -/
private lemma quad_mom {φ : Mode → ℝ} (hφ0 : ∀ p, 0 ≤ φ p) (hφ : SymFn φ) (v : R3) :
    ∑' p, ENNReal.ofReal (dR p v ^ 2 * φ p) =
      ENNReal.ofReal (v 0 ^ 2) * mom φ 0 + ENNReal.ofReal (v 1 ^ 2) * mom φ 1
        + ENNReal.ofReal (v 2 ^ 2) * mom φ 2 := by
  set S := ∑' p, ENNReal.ofReal (dR p v ^ 2 * φ p) with hS
  have h1 : S = ∑' p, ENNReal.ofReal (dR (act 1 flip1 p) v ^ 2 * φ p) := by
    rw [hS, ← tsum_act (σ := 1) flip1_sq]
    exact tsum_congr fun p => by rw [hφ _ _ flip1_sq]
  have h2 : S = ∑' p, ENNReal.ofReal (dR (act 1 flip2 p) v ^ 2 * φ p) := by
    rw [hS, ← tsum_act (σ := 1) flip2_sq]
    exact tsum_congr fun p => by rw [hφ _ _ flip2_sq]
  have h3 : S = ∑' p, ENNReal.ofReal (dR (act 1 flip3 p) v ^ 2 * φ p) := by
    rw [hS, ← tsum_act (σ := 1) flip3_sq]
    exact tsum_congr fun p => by rw [hφ _ _ flip3_sq]
  have h4 : (4 : ℝ≥0∞) * S = S + S + S + S := by ring
  have h5 : S + S + S + S = ∑' p, ENNReal.ofReal
      (4 * (v 0 ^ 2 * (p 0 : ℝ) ^ 2 + v 1 ^ 2 * (p 1 : ℝ) ^ 2 + v 2 ^ 2 * (p 2 : ℝ) ^ 2) * φ p) := by
    calc S + S + S + S = S + (∑' p, ENNReal.ofReal (dR (act 1 flip1 p) v ^ 2 * φ p))
          + (∑' p, ENNReal.ofReal (dR (act 1 flip2 p) v ^ 2 * φ p))
          + (∑' p, ENNReal.ofReal (dR (act 1 flip3 p) v ^ 2 * φ p)) := by
            rw [← h1, ← h2, ← h3]
      _ = _ := ?_
    rw [hS, ← tsum_add, ← tsum_add, ← tsum_add]
    refine tsum_congr fun p => ?_
    have := hφ0 p
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← flip_identity p v]
    congr 1
    ring
  have h6 : (∑' p : Mode, ENNReal.ofReal
      (4 * (v 0 ^ 2 * (p 0 : ℝ) ^ 2 + v 1 ^ 2 * (p 1 : ℝ) ^ 2 + v 2 ^ 2 * (p 2 : ℝ) ^ 2) * φ p)) =
      4 * (ENNReal.ofReal (v 0 ^ 2) * mom φ 0 + ENNReal.ofReal (v 1 ^ 2) * mom φ 1
        + ENNReal.ofReal (v 2 ^ 2) * mom φ 2) := by
    unfold mom
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← tsum_add,
      ← tsum_add, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun p => ?_
    have := hφ0 p
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [h5, h6] at h4
  exact (ENNReal.mul_right_inj (a := 4) (by norm_num) (by norm_num)).1 h4

/-- **The moment identity.** -/
theorem moment {φ : Mode → ℝ} (hφ0 : ∀ p, 0 ≤ φ p) (hφ : SymFn φ) (v : R3) :
    3 * ∑' p, ENNReal.ofReal (dR p v ^ 2 * φ p) =
      ENNReal.ofReal (nR v) * ∑' p, ENNReal.ofReal (absSq p * φ p) := by
  rw [quad_mom hφ0 hφ]
  have h0 := three_mom hφ0 (0 : Fin 3) hφ
  have h1 := three_mom hφ0 (1 : Fin 3) hφ
  have h2 := three_mom hφ0 (2 : Fin 3) hφ
  have e : ENNReal.ofReal (nR v) = ENNReal.ofReal (v 0 ^ 2) + ENNReal.ofReal (v 1 ^ 2)
      + ENNReal.ofReal (v 2 ^ 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [nR, Fin.sum_univ_three]
  rw [e]
  calc 3 * (ENNReal.ofReal (v 0 ^ 2) * mom φ 0 + ENNReal.ofReal (v 1 ^ 2) * mom φ 1
        + ENNReal.ofReal (v 2 ^ 2) * mom φ 2)
      = ENNReal.ofReal (v 0 ^ 2) * (3 * mom φ 0) + ENNReal.ofReal (v 1 ^ 2) * (3 * mom φ 1)
        + ENNReal.ofReal (v 2 ^ 2) * (3 * mom φ 2) := by ring
    _ = _ := by rw [h0, h1, h2]; ring

/-- A function of `nsq` is invariant. -/
lemma symFn_nsq (f : ℕ → ℝ) : SymFn (fun p => f (nsq p)) := by
  intro σ ε hε p
  simp only [nsq_act hε]

end Row
end OVNS
