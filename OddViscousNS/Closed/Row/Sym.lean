import OddViscousNS.Closed.Row.Form

/-!
# Signed-permutation invariance of the row form; reduction to sorted representatives

`rowR (σ k) (σ c) = rowR k c` for every signed permutation `σ`; the proof goes through Parseval, so
the triple product `p·(k × c)` (which picks up `det σ`) is never transformed directly.  Hence
`RealRow g` follows from the sorted case `k 0 ≥ k 1 ≥ k 2 ≥ 0`.
-/

open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

/-- Signed permutation of the lattice. -/
def act (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℤ) (p : Mode) : Mode := fun i => ε i * p (σ i)

/-- Signed permutation of real vectors. -/
def actR (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℤ) (v : R3) : R3 := fun i => (ε i : ℝ) * v (σ i)

section
variable {σ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ℤ}

/-- The inverse action. -/
def actInv (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℤ) (q : Mode) : Mode :=
  fun i => ε (σ⁻¹ i) * q (σ⁻¹ i)

lemma act_actInv (hε : ∀ i, ε i * ε i = 1) (q : Mode) : act σ ε (actInv σ ε q) = q := by
  funext i
  have h : σ⁻¹ (σ i) = i := by simp
  simp only [act, actInv, h]
  rw [← mul_assoc, hε, one_mul]

lemma actInv_act (hε : ∀ i, ε i * ε i = 1) (q : Mode) : actInv σ ε (act σ ε q) = q := by
  funext i
  have h : σ (σ⁻¹ i) = i := by simp
  simp only [act, actInv, h]
  rw [← mul_assoc, hε, one_mul]

/-- `act` as an equivalence of the lattice. -/
def actEquiv (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℤ) (hε : ∀ i, ε i * ε i = 1) : Mode ≃ Mode where
  toFun := act σ ε
  invFun := actInv σ ε
  left_inv := actInv_act hε
  right_inv := act_actInv hε

lemma act_sub (p q : Mode) : act σ ε (p - q) = act σ ε p - act σ ε q := by
  funext i; simp [act, mul_sub]

lemma act_zero : act σ ε 0 = 0 := by
  funext i; simp [act]

lemma eps_cast (hε : ∀ i, ε i * ε i = 1) (i : Fin 3) : (ε i : ℝ) * (ε i : ℝ) = 1 := by
  exact_mod_cast hε i

lemma dZ_act (hε : ∀ i, ε i * ε i = 1) (p q : Mode) :
    dZ (act σ ε p) (act σ ε q) = dZ p q := by
  unfold dZ
  rw [← Equiv.sum_comp σ (fun i => (p i : ℝ) * (q i : ℝ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [act, Int.cast_mul]
  linear_combination ((p (σ i) : ℝ) * q (σ i)) * eps_cast hε i

lemma dR_act (hε : ∀ i, ε i * ε i = 1) (p : Mode) (v : R3) :
    dR (act σ ε p) (actR σ ε v) = dR p v := by
  unfold dR
  rw [← Equiv.sum_comp σ (fun i => (p i : ℝ) * v i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [act, actR, Int.cast_mul]
  linear_combination ((p (σ i) : ℝ) * v (σ i)) * eps_cast hε i

lemma nR_act (hε : ∀ i, ε i * ε i = 1) (v : R3) : nR (actR σ ε v) = nR v := by
  unfold nR
  rw [← Equiv.sum_comp σ (fun i => v i ^ 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [actR]
  linear_combination (v (σ i) ^ 2) * eps_cast hε i

lemma absSq_eq_dZ (p : Mode) : absSq p = dZ p p := by
  simp only [absSq, dZ, sq]

lemma absSq_act (hε : ∀ i, ε i * ε i = 1) (p : Mode) : absSq (act σ ε p) = absSq p := by
  rw [absSq_eq_dZ, absSq_eq_dZ, dZ_act hε]

lemma nsq_act (hε : ∀ i, ε i * ε i = 1) (p : Mode) : nsq (act σ ε p) = nsq p := by
  have : ((nsq (act σ ε p) : ℕ) : ℝ) = (nsq p : ℝ) := by
    rw [nsq_cast, nsq_cast, absSq_act hε]
  exact_mod_cast this

lemma hm_act (hε : ∀ i, ε i * ε i = 1) (p : Mode) : hm (act σ ε p) = hm p := by
  simp only [hm, nsq_act hε]

lemma Wk_act (hε : ∀ i, ε i * ε i = 1) (k p : Mode) :
    Wk lamW (act σ ε k) (act σ ε p) = Wk lamW k p := by
  simp only [Wk, ← act_sub, nsq_act hε]

lemma w1_act (hε : ∀ i, ε i * ε i = 1) (k p : Mode) :
    w1 (act σ ε k) (act σ ε p) = w1 k p := by
  simp only [w1, Wk_act hε, ← act_sub, absSq_act hε, hm_act hε]

lemma Lst_act (hε : ∀ i, ε i * ε i = 1) (k p : Mode) :
    Lst (act σ ε k) (act σ ε p) = Lst k p := by
  simp only [Lst, ← act_sub, absSq_act hε, hm_act hε]

lemma w2_act (hε : ∀ i, ε i * ε i = 1) (k p : Mode) :
    w2 (act σ ε k) (act σ ε p) = w2 k p := by
  simp only [w2, Wk_act hε, ← act_sub, absSq_act hε, hm_act hε, Lst_act hε]

lemma dR_cross_act (hε : ∀ i, ε i * ε i = 1) (p k : Mode) (c : R3) (hc : dR k c = 0) :
    dR (act σ ε p) (crR (act σ ε k) (actR σ ε c)) ^ 2 = dR p (crR k c) ^ 2 := by
  have h1 := parseval p k c hc
  have h2 := parseval (act σ ε p) (act σ ε k) (actR σ ε c) (by rw [dR_act hε]; exact hc)
  rw [dR_act hε, dZ_act hε, nR_act hε, absSq_act hε, absSq_act hε] at h2
  linarith

lemma pterm_act (hε : ∀ i, ε i * ε i = 1) (k p : Mode) (c : R3) (hc : dR k c = 0) :
    pterm (act σ ε k) (actR σ ε c) (act σ ε p) = pterm k c p := by
  unfold pterm
  rw [w1_act hε, w2_act hε, dR_cross_act hε p k c hc, dR_act hε]

/-- Invariance of the row form. -/
theorem rowR_act (hε : ∀ i, ε i * ε i = 1) (k : Mode) (c : R3) (hc : dR k c = 0) :
    rowR (act σ ε k) (actR σ ε c) = rowR k c := by
  unfold rowR
  rw [← (actEquiv σ ε hε).tsum_eq]
  refine tsum_congr fun p => ?_
  show ENNReal.ofReal (pterm (act σ ε k) (actR σ ε c) (act σ ε p)) = _
  rw [pterm_act hε k p c hc]

end

/-- Sorted nonnegative representatives. -/
def Sorted (k : Mode) : Prop := 0 ≤ k 2 ∧ k 2 ≤ k 1 ∧ k 1 ≤ k 0

/-- Every lattice vector has a sorted image. -/
lemma exists_sorted (k : Mode) : ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℤ),
    (∀ i, ε i * ε i = 1) ∧ Sorted (act σ ε k) := by
  let f : Fin 3 → ℕ := fun i => (k i).natAbs
  let σ : Equiv.Perm (Fin 3) := Fin.revPerm.trans (Tuple.sort f)
  let s : Fin 3 → ℤ := fun j => if 0 ≤ k j then 1 else -1
  have hs : ∀ j, s j * k j = ((k j).natAbs : ℤ) := by
    intro j
    by_cases h : 0 ≤ k j
    · simp only [s, h, ↓reduceIte, one_mul]; omega
    · simp only [s, h, ↓reduceIte]; omega
  have hm := Tuple.monotone_sort f
  have hval : ∀ i, act σ (fun i => s (σ i)) k i = (f (σ i) : ℤ) := fun i => by
    simp only [act, hs, f]
  refine ⟨σ, fun i => s (σ i), fun i => ?_, ?_⟩
  · show s (σ i) * s (σ i) = 1
    by_cases h : 0 ≤ k (σ i) <;> simp [s, h]
  · have h01 : f (σ 1) ≤ f (σ 0) := by
      have := hm (show Fin.rev (0 : Fin 3) ≥ Fin.rev (1 : Fin 3) by decide)
      simpa [σ, Function.comp] using this
    have h12 : f (σ 2) ≤ f (σ 1) := by
      have := hm (show Fin.rev (1 : Fin 3) ≥ Fin.rev (2 : Fin 3) by decide)
      simpa [σ, Function.comp] using this
    refine ⟨?_, ?_, ?_⟩
    · rw [hval]; positivity
    · rw [hval, hval]; exact_mod_cast h12
    · rw [hval, hval]; exact_mod_cast h01

/-- Reduction of `RealRow` to sorted representatives. -/
theorem realRow_of_sorted {g : ℕ → ℝ}
    (h : ∀ k : Mode, k ≠ 0 → Sorted k → ∀ c : R3, dR k c = 0 →
      rowR k c ≤ ENNReal.ofReal (36 * g (nsq k) * hm k * nR c)) : RealRow g := by
  intro k hk c hc
  obtain ⟨σ, ε, hε, hs⟩ := exists_sorted k
  have hk' : act σ ε k ≠ 0 := by
    intro h0
    apply hk
    rw [← actInv_act (σ := σ) hε k, h0]
    funext i; simp [actInv]
  have := h (act σ ε k) hk' hs (actR σ ε c) (by rw [dR_act hε]; exact hc)
  rwa [rowR_act hε k c hc, nsq_act hε, hm_act hε, nR_act hε] at this

end Row
end OVNS
