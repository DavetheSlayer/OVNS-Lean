import OddViscousNS.Quant.Arith.Resonant.Defs

/-!
# The orbit identity and the pattern structure (elementary algebra)

* `orbit_vertex_H1`: for a zero-sum triad of nonzero modes and helical amplitudes
  `A j = hel (s j) (ℓ j) (v j)`, `‖orbitSum 1 ℓ A‖ = 6 γ (∏ |ℓ_j|) ∏ ‖A j‖`;
  `orbit_vertex_H2`: `‖orbitSum 2 ℓ A‖ = 6 γ |h₂| (∏ |ℓ_j|) ∏ ‖A j‖`.
* `resPat_unique`: a fast triad has at most the two opposite resonant patterns; `gammaC_neg`,
  `h2C_neg`, `resPat_neg`: invariance under global helicity reversal.
* `hel_contraction`: `∑_{t ∈ {s, !s}} ∏ ‖hel (t j) (ℓ j) (F (ℓ j))‖ ≤ ∏ ‖F (ℓ j)‖` for solenoidal
  `F`.
* `h2C_le`: sorted `0 < M ≤ K ≤ N ≤ M + K` gives `|h₂| ≤ 6 K N`.

Proof of the orbit identity: with `n = ℓ₀ × ℓ₁` (orthogonal to every leg), each helical
amplitude is a multiple of the explicit eigenvector `wv ℓ_j n x_j = |ℓ_j|² n + i x_j ℓ_j × n`
(`eig_decomp`); all the bilinear pairings of these frame vectors are explicit
(`dot_pq`, …, `bd_wv`), which reduces the orbit sum to a polynomial identity in the signed
lengths `x_j`.  Collinear triads (`n = 0`) give `0` on both sides.
-/

open Finset

namespace OVNS.Quant

/-! ### Elementary sign facts -/

private lemma sg_not (a : Sgn) : sg (!a) = -sg a := by cases a <;> simp [sg]

private lemma sg_sq' (a : Sgn) : sg a ^ 2 = 1 := by cases a <;> simp [sg]

private lemma abs_sg (a : Sgn) : |sg a| = 1 := by cases a <;> simp [sg]

private lemma sl_not (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) (j : Fin 3) :
    sl ℓ (fun j => !s j) j = -sl ℓ s j := by
  simp only [sl, sg_not]; ring

private lemma sl_sq (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) (j : Fin 3) :
    sl ℓ s j ^ 2 = absSq (ℓ j) := by
  rw [sl, mul_pow, sg_sq', one_mul, absk_sq]

private lemma abs_sl (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) (j : Fin 3) :
    |sl ℓ s j| = absk (ℓ j) := by
  rw [sl, abs_mul, abs_sg, one_mul, abs_of_nonneg (absk_nonneg _)]

/-! ### The six orderings -/

private lemma perm3_sum {M : Type*} [AddCommMonoid M] (g : Fin 3 → Fin 3 → Fin 3 → M) :
    ∑ π : Equiv.Perm (Fin 3), g (π 0) (π 1) (π 2) =
      g 0 1 2 + g 0 2 1 + g 1 0 2 + g 1 2 0 + g 2 0 1 + g 2 1 0 := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 1 2, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 1 2,
        Equiv.swap 1 2 * Equiv.swap 0 1, Equiv.swap 0 2} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have e1 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
  have e2 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
  have e3 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
  have f1 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have f2 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
  have f3 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have g1 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
  have g2 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  have g3 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, e1, e2, e3, f1, f2, f3, g1, g2, g3]
  abel

/-! ### The helical frame -/

/-- Unnormalised helical frame vector `|k|² n + i x (k × n)`. -/
private def wv (k n : Mode) (x : ℝ) : V3 :=
  (absSq k : ℂ) • modeVec n + (Complex.I * x) • cross (modeVec k) (modeVec n)

private lemma wv_apply (k n : Mode) (x : ℝ) (i : Fin 3) :
    wv k n x i =
      (absSq k : ℂ) * (n i : ℂ) + Complex.I * x * cross (modeVec k) (modeVec n) i := by
  simp [wv, modeVec_apply]

private lemma crossZ_zero (p q : Mode) : crossZ p q 0 = p 1 * q 2 - p 2 * q 1 := by
  simp [crossZ]

private lemma crossZ_one (p q : Mode) : crossZ p q 1 = p 2 * q 0 - p 0 * q 2 := by
  simp [crossZ]

private lemma crossZ_two (p q : Mode) : crossZ p q 2 = p 0 * q 1 - p 1 * q 0 := by
  simp [crossZ]

/-- A helical eigenvector orthogonal to `k` is a multiple of the frame vector. -/
private lemma eig_decomp {k n : Mode} {x : ℝ} {A : V3}
    (hkn : (k 0 : ℂ) * n 0 + (k 1 : ℂ) * n 1 + (k 2 : ℂ) * n 2 = 0)
    (hA : dotM A k = 0) (he : Complex.I • cross (modeVec k) A = (x : ℂ) • A) :
    ((absSq k : ℂ) * absSq n) • A = dotM A n • wv k n x := by
  have e0 := congrArg (fun v : V3 => v 0) he
  have e1 := congrArg (fun v : V3 => v 1) he
  have e2 := congrArg (fun v : V3 => v 2) he
  simp only [PiLp.smul_apply, smul_eq_mul, cross_apply_zero, cross_apply_one, cross_apply_two,
    modeVec_apply] at e0 e1 e2
  rw [dotM_eq] at hA
  have hc : Complex.I * ((n 0 : ℂ) * (Complex.I * ((k 1 : ℂ) * A 2 - (k 2 : ℂ) * A 1)) +
      (n 1 : ℂ) * (Complex.I * ((k 2 : ℂ) * A 0 - (k 0 : ℂ) * A 2)) +
      (n 2 : ℂ) * (Complex.I * ((k 0 : ℂ) * A 1 - (k 1 : ℂ) * A 0))) =
      Complex.I * ((n 0 : ℂ) * (x * A 0) + (n 1 : ℂ) * (x * A 1) + (n 2 : ℂ) * (x * A 2)) := by
    rw [e0, e1, e2]
  rw [dotM_eq]
  apply v3_ext <;>
  simp only [PiLp.smul_apply, smul_eq_mul, wv_apply, absSq_cast, cross_apply_zero,
    cross_apply_one, cross_apply_two, modeVec_apply]
  · linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
      (((k 0 : ℂ) * (n 0 : ℂ) + (k 1 : ℂ) * (n 1 : ℂ) + (k 2 : ℂ) * (n 2 : ℂ)) * A 0 -
      (A 0 * (n 0 : ℂ) + A 1 * (n 1 : ℂ) + A 2 * (n 2 : ℂ)) * (k 0 : ℂ)) * hkn -
      (((k 2 : ℂ) * (n 0 : ℂ) - (k 0 : ℂ) * (n 2 : ℂ)) * (n 2 : ℂ) -
      ((k 0 : ℂ) * (n 1 : ℂ) - (k 1 : ℂ) * (n 0 : ℂ)) * (n 1 : ℂ)) * hA +
      ((k 1 : ℂ) * (n 2 : ℂ) - (k 2 : ℂ) * (n 1 : ℂ)) * hc
  · linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
      (((k 0 : ℂ) * (n 0 : ℂ) + (k 1 : ℂ) * (n 1 : ℂ) + (k 2 : ℂ) * (n 2 : ℂ)) * A 1 -
      (A 0 * (n 0 : ℂ) + A 1 * (n 1 : ℂ) + A 2 * (n 2 : ℂ)) * (k 1 : ℂ)) * hkn -
      (((k 0 : ℂ) * (n 1 : ℂ) - (k 1 : ℂ) * (n 0 : ℂ)) * (n 0 : ℂ) -
      ((k 1 : ℂ) * (n 2 : ℂ) - (k 2 : ℂ) * (n 1 : ℂ)) * (n 2 : ℂ)) * hA +
      ((k 2 : ℂ) * (n 0 : ℂ) - (k 0 : ℂ) * (n 2 : ℂ)) * hc
  · linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
      (((k 0 : ℂ) * (n 0 : ℂ) + (k 1 : ℂ) * (n 1 : ℂ) + (k 2 : ℂ) * (n 2 : ℂ)) * A 2 -
      (A 0 * (n 0 : ℂ) + A 1 * (n 1 : ℂ) + A 2 * (n 2 : ℂ)) * (k 2 : ℂ)) * hkn -
      (((k 1 : ℂ) * (n 2 : ℂ) - (k 2 : ℂ) * (n 1 : ℂ)) * (n 1 : ℂ) -
      ((k 2 : ℂ) * (n 0 : ℂ) - (k 0 : ℂ) * (n 2 : ℂ)) * (n 0 : ℂ)) * hA +
      ((k 0 : ℂ) * (n 1 : ℂ) - (k 1 : ℂ) * (n 0 : ℂ)) * hc

private lemma norm_wv_sq {k n : Mode} (x : ℝ)
    (hkn : (k 0 : ℝ) * n 0 + (k 1 : ℝ) * n 1 + (k 2 : ℝ) * n 2 = 0) :
    ‖wv k n x‖ ^ 2 = absSq k ^ 2 * absSq n + x ^ 2 * (absSq k * absSq n) := by
  have hi : ∀ i, wv k n x i = ((absSq k * n i : ℝ) : ℂ) +
      ((x * ((crossZ k n i : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I := by
    intro i
    rw [wv_apply]
    fin_cases i <;>
    simp [cross_apply_zero, cross_apply_one, cross_apply_two, modeVec_apply, crossZ] <;> ring
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, hi, hi, hi]
  simp only [Complex.sq_norm, Complex.normSq_add_mul_I]
  simp only [absSq, Fin.sum_univ_three, crossZ]
  simp
  linear_combination (-(x ^ 2) * ((k 0 : ℝ) * n 0 + (k 1 : ℝ) * n 1 + (k 2 : ℝ) * n 2)) * hkn

private lemma bd_wv {k n : Mode} (l : Mode) (x y : ℝ)
    (hkn : (k 0 : ℂ) * n 0 + (k 1 : ℂ) * n 1 + (k 2 : ℂ) * n 2 = 0) :
    bd (wv k n x) (wv l n y) = absSq n * (absSq k * absSq l -
      x * y * ((k 0 : ℂ) * l 0 + (k 1 : ℂ) * l 1 + (k 2 : ℂ) * l 2)) := by
  simp only [wv_apply, bd, absSq_cast, cross_apply_zero, cross_apply_one, cross_apply_two,
    modeVec_apply]
  linear_combination (norm := ring_nf) (x * y * (((k 1 : ℂ) * n 2 - (k 2 : ℂ) * n 1) *
      ((l 1 : ℂ) * n 2 - (l 2 : ℂ) * n 1) + ((k 2 : ℂ) * n 0 - (k 0 : ℂ) * n 2) *
      ((l 2 : ℂ) * n 0 - (l 0 : ℂ) * n 2) + ((k 0 : ℂ) * n 1 - (k 1 : ℂ) * n 0) *
      ((l 0 : ℂ) * n 1 - (l 1 : ℂ) * n 0))) * Complex.I_sq +
    x * y * ((l 0 : ℂ) * n 0 + (l 1 : ℂ) * n 1 + (l 2 : ℂ) * n 2) * hkn

/-! ### The triad `(p, q, -(p+q))` with normal `n = p × q` -/

private lemma kn_p (p q : Mode) :
    p 0 * crossZ p q 0 + p 1 * crossZ p q 1 + p 2 * crossZ p q 2 = 0 := by
  simp only [crossZ_zero, crossZ_one, crossZ_two]; ring

private lemma kn_q (p q : Mode) :
    q 0 * crossZ p q 0 + q 1 * crossZ p q 1 + q 2 * crossZ p q 2 = 0 := by
  simp only [crossZ_zero, crossZ_one, crossZ_two]; ring

private lemma kn_r (p q : Mode) :
    (-(p + q)) 0 * crossZ p q 0 + (-(p + q)) 1 * crossZ p q 1 +
      (-(p + q)) 2 * crossZ p q 2 = 0 := by
  simp only [crossZ_zero, crossZ_one, crossZ_two, Pi.neg_apply, Pi.add_apply]; ring

private lemma dot_pq (p q : Mode) (x : ℝ) :
    dotM (wv p (crossZ p q) x) q = -Complex.I * x * absSq (crossZ p q) := by
  simp [wv_apply, dotM_eq, absSq_cast, cross_apply_zero, cross_apply_one, cross_apply_two,
    modeVec_apply, crossZ]
  ring

private lemma dot_rp (p q : Mode) (x : ℝ) :
    dotM (wv (-(p + q)) (crossZ p q) x) p = -Complex.I * x * absSq (crossZ p q) := by
  simp [wv_apply, dotM_eq, absSq_cast, cross_apply_zero, cross_apply_one, cross_apply_two,
    modeVec_apply, crossZ]
  ring

private lemma dot_qr (p q : Mode) (x : ℝ) :
    dotM (wv q (crossZ p q) x) (-(p + q)) = -Complex.I * x * absSq (crossZ p q) := by
  simp [wv_apply, dotM_eq, absSq_cast, cross_apply_zero, cross_apply_one, cross_apply_two,
    modeVec_apply, crossZ]
  ring

private lemma dot_qp (p q : Mode) (x : ℝ) :
    dotM (wv q (crossZ p q) x) p = Complex.I * x * absSq (crossZ p q) := by
  simp [wv_apply, dotM_eq, absSq_cast, cross_apply_zero, cross_apply_one, cross_apply_two,
    modeVec_apply, crossZ]
  ring

private lemma dot_rq (p q : Mode) (x : ℝ) :
    dotM (wv (-(p + q)) (crossZ p q) x) q = Complex.I * x * absSq (crossZ p q) := by
  simp [wv_apply, dotM_eq, absSq_cast, cross_apply_zero, cross_apply_one, cross_apply_two,
    modeVec_apply, crossZ]
  ring

private lemma dot_pr (p q : Mode) (x : ℝ) :
    dotM (wv p (crossZ p q) x) (-(p + q)) = Complex.I * x * absSq (crossZ p q) := by
  simp [wv_apply, dotM_eq, absSq_cast, cross_apply_zero, cross_apply_one, cross_apply_two,
    modeVec_apply, crossZ]
  ring

private lemma bd_pq (p q : Mode) (x y : ℝ) :
    bd (wv p (crossZ p q) x) (wv q (crossZ p q) y) = absSq (crossZ p q) *
      (absSq p * absSq q - x * y * (absSq (-(p + q)) - absSq p - absSq q) / 2) := by
  rw [bd_wv _ _ _ (by exact_mod_cast kn_p p q)]
  simp only [absSq_cast, Pi.neg_apply, Pi.add_apply, Int.cast_neg, Int.cast_add]
  ring

private lemma bd_qr (p q : Mode) (x y : ℝ) :
    bd (wv q (crossZ p q) x) (wv (-(p + q)) (crossZ p q) y) = absSq (crossZ p q) *
      (absSq q * absSq (-(p + q)) - x * y * (absSq p - absSq q - absSq (-(p + q))) / 2) := by
  rw [bd_wv _ _ _ (by exact_mod_cast kn_q p q)]
  simp only [absSq_cast, Pi.neg_apply, Pi.add_apply, Int.cast_neg, Int.cast_add]
  ring

private lemma bd_rp (p q : Mode) (x y : ℝ) :
    bd (wv (-(p + q)) (crossZ p q) x) (wv p (crossZ p q) y) = absSq (crossZ p q) *
      (absSq (-(p + q)) * absSq p - x * y * (absSq q - absSq (-(p + q)) - absSq p) / 2) := by
  rw [bd_wv _ _ _ (by exact_mod_cast kn_r p q)]
  simp only [absSq_cast, Pi.neg_apply, Pi.add_apply, Int.cast_neg, Int.cast_add]
  ring

private lemma bd_smul (a b : ℂ) (A B : V3) : bd (a • A) (b • B) = a * b * bd A B := by
  simp only [bd, PiLp.smul_apply, smul_eq_mul]; ring

private lemma tau_smul (p q : Mode) (a b c : ℂ) (A B C : V3) :
    tau p q (a • A) (b • B) (c • C) = a * b * c * tau p q A B C := by
  simp only [tau, dotM_smul, bd_smul]; ring

/-- The orbit sum of frame vectors, for an arbitrary weight. -/
private lemma orbit_core (σ : ℝ) (ℓ : Fin 3 → Mode) (hr : ℓ 2 = -(ℓ 0 + ℓ 1)) (x : Fin 3 → ℝ)
    (hx : ∀ j, x j ^ 2 = absSq (ℓ j)) (α : Fin 3 → ℂ) :
    orbitSum σ ℓ (fun j => α j • wv (ℓ j) (crossZ (ℓ 0) (ℓ 1)) (x j)) =
      α 0 * α 1 * α 2 * ((absSq (crossZ (ℓ 0) (ℓ 1)) ^ 2 * (x 0 * x 1 * x 2) *
        (x 0 + x 1 + x 2) * (sobWeight σ (ℓ 2) * (x 1 - x 0) +
          sobWeight σ (ℓ 0) * (x 2 - x 1) + sobWeight σ (ℓ 1) * (x 0 - x 2)) : ℝ) : ℂ) := by
  have h := perm3_sum (fun a b c => ((sobWeight σ (ℓ c) : ℝ) : ℂ) *
    tau (ℓ a) (ℓ b) (α a • wv (ℓ a) (crossZ (ℓ 0) (ℓ 1)) (x a))
      (α b • wv (ℓ b) (crossZ (ℓ 0) (ℓ 1)) (x b)) (α c • wv (ℓ c) (crossZ (ℓ 0) (ℓ 1)) (x c)))
  rw [orbitSum, h]
  simp only [tau_smul]
  have h0 : (absSq (ℓ 0) : ℂ) = (x 0 : ℂ) ^ 2 := by exact_mod_cast (hx 0).symm
  have h1 : (absSq (ℓ 1) : ℂ) = (x 1 : ℂ) ^ 2 := by exact_mod_cast (hx 1).symm
  have h2 : (absSq (-(ℓ 0 + ℓ 1)) : ℂ) = (x 2 : ℂ) ^ 2 := by
    rw [← hr]; exact_mod_cast (hx 2).symm
  rw [hr]
  simp only [tau, dot_pq, dot_qr, dot_rp, dot_qp, dot_rq, dot_pr, bd_pq, bd_qr, bd_rp,
    bd_comm (wv (ℓ 1) _ _) (wv (ℓ 0) _ _), bd_comm (wv (-(ℓ 0 + ℓ 1)) _ _) (wv (ℓ 1) _ _),
    bd_comm (wv (ℓ 0) _ _) (wv (-(ℓ 0 + ℓ 1)) _ _), h0, h1, h2]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-! ### Assembling the orbit identity -/

private lemma kn_leg (ℓ : Fin 3 → Mode) (hr : ℓ 2 = -(ℓ 0 + ℓ 1)) (j : Fin 3) :
    ℓ j 0 * crossZ (ℓ 0) (ℓ 1) 0 + ℓ j 1 * crossZ (ℓ 0) (ℓ 1) 1 +
      ℓ j 2 * crossZ (ℓ 0) (ℓ 1) 2 = 0 := by
  fin_cases j
  · exact kn_p _ _
  · exact kn_q _ _
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [hr]; exact kn_r _ _

private lemma hel_decomp (ℓ : Fin 3 → Mode) (hr : ℓ 2 = -(ℓ 0 + ℓ 1)) (hne : ∀ j, ℓ j ≠ 0)
    (s : Fin 3 → Sgn) (v : Fin 3 → V3) (hG : absSq (crossZ (ℓ 0) (ℓ 1)) ≠ 0) (j : Fin 3) :
    hel (s j) (ℓ j) (v j) = (dotM (hel (s j) (ℓ j) (v j)) (crossZ (ℓ 0) (ℓ 1)) /
      ((absSq (ℓ j) : ℂ) * absSq (crossZ (ℓ 0) (ℓ 1)))) •
        wv (ℓ j) (crossZ (ℓ 0) (ℓ 1)) (sl ℓ s j) := by
  have h := eig_decomp (x := sl ℓ s j) (by exact_mod_cast kn_leg ℓ hr j)
    (dotM_hel (s j) (ℓ j) (v j)) (cross_hel (s j) (ℓ j) (v j))
  have hc : ((absSq (ℓ j) : ℂ) * absSq (crossZ (ℓ 0) (ℓ 1))) ≠ 0 :=
    mul_ne_zero (absSq_cast_ne (hne j)) (by exact_mod_cast hG)
  rw [div_eq_inv_mul, ← smul_smul, ← h, smul_smul, inv_mul_cancel₀ hc, one_smul]

private lemma norm_wv_leg (ℓ : Fin 3 → Mode) (hr : ℓ 2 = -(ℓ 0 + ℓ 1)) (s : Fin 3 → Sgn)
    (j : Fin 3) :
    ‖wv (ℓ j) (crossZ (ℓ 0) (ℓ 1)) (sl ℓ s j)‖ =
      Real.sqrt 2 * absSq (ℓ j) * Real.sqrt (absSq (crossZ (ℓ 0) (ℓ 1))) := by
  have h := norm_wv_sq (sl ℓ s j) (by exact_mod_cast kn_leg ℓ hr j)
  rw [sl_sq] at h
  have hG := absSq_nonneg (crossZ (ℓ 0) (ℓ 1))
  have hP := absSq_nonneg (ℓ j)
  rw [← pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero, h, mul_pow, mul_pow,
    Real.sq_sqrt (by norm_num), Real.sq_sqrt hG]
  ring

private lemma crossZ_leg_zero (ℓ : Fin 3 → Mode) (hr : ℓ 2 = -(ℓ 0 + ℓ 1))
    (h : crossZ (ℓ 0) (ℓ 1) = 0) (a b : Fin 3) : crossZ (ℓ a) (ℓ b) = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [crossZ_zero, crossZ_one, crossZ_two, Pi.zero_apply] at h0 h1 h2
  funext i
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp only [Fin.reduceFinMk, Fin.isValue, hr, crossZ_zero, crossZ_one, crossZ_two,
      Pi.zero_apply, Pi.neg_apply, Pi.add_apply] <;>
    first
    | ring1
    | linear_combination h0
    | linear_combination -h0
    | linear_combination h1
    | linear_combination -h1
    | linear_combination h2
    | linear_combination -h2

private lemma dot_collinear {k l : Mode} {A : V3} (hk : k ≠ 0) (hc : crossZ k l = 0)
    (hA : dotM A k = 0) : dotM A l = 0 := by
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp only [crossZ_zero, crossZ_one, crossZ_two, Pi.zero_apply] at h0 h1 h2
  have c0 : (k 1 : ℂ) * l 2 - (k 2 : ℂ) * l 1 = 0 := by exact_mod_cast h0
  have c1 : (k 2 : ℂ) * l 0 - (k 0 : ℂ) * l 2 = 0 := by exact_mod_cast h1
  have c2 : (k 0 : ℂ) * l 1 - (k 1 : ℂ) * l 0 = 0 := by exact_mod_cast h2
  rw [dotM_eq] at hA ⊢
  have key : (absSq k : ℂ) * (A 0 * l 0 + A 1 * l 1 + A 2 * l 2) = 0 := by
    rw [absSq_cast]
    linear_combination ((k 0 : ℂ) * l 0 + (k 1 : ℂ) * l 1 + (k 2 : ℂ) * l 2) * hA -
      (A 0 * ((k 1 : ℂ) * c2 - (k 2 : ℂ) * c1) + A 1 * ((k 2 : ℂ) * c0 - (k 0 : ℂ) * c2) +
        A 2 * ((k 0 : ℂ) * c1 - (k 1 : ℂ) * c0))
  exact (mul_eq_zero.mp key).resolve_left (absSq_cast_ne hk)

/-- The orbit sum for an arbitrary weight, in normalised form. -/
private lemma orbit_norm (σ : ℝ) (ℓ : Fin 3 → Mode) (hsum : ∑ j, ℓ j = 0) (hne : ∀ j, ℓ j ≠ 0)
    (s : Fin 3 → Sgn) (v : Fin 3 → V3) :
    ‖orbitSum σ ℓ (fun j => hel (s j) (ℓ j) (v j))‖ *
        (2 * Real.sqrt 2 * (absk (ℓ 0) * absk (ℓ 1) * absk (ℓ 2))) =
      areaM (ℓ 0) (ℓ 1) * |(sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2) *
        (sobWeight σ (ℓ 2) * (sl ℓ s 1 - sl ℓ s 0) + sobWeight σ (ℓ 0) * (sl ℓ s 2 - sl ℓ s 1) +
          sobWeight σ (ℓ 1) * (sl ℓ s 0 - sl ℓ s 2))| * ∏ j, ‖hel (s j) (ℓ j) (v j)‖ := by
  have hr : ℓ 2 = -(ℓ 0 + ℓ 1) := by
    rw [Fin.sum_univ_three] at hsum
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hsum
  set n := crossZ (ℓ 0) (ℓ 1) with hn
  by_cases hG : absSq n = 0
  · have hn0 : n = 0 := absk_eq_zero.mp (by rw [absk, hG, Real.sqrt_zero])
    have hd : ∀ a b, dotM (hel (s a) (ℓ a) (v a)) (ℓ b) = 0 := fun a b =>
      dot_collinear (hne a) (crossZ_leg_zero ℓ hr hn0 a b) (dotM_hel _ _ _)
    have h0 : orbitSum σ ℓ (fun j => hel (s j) (ℓ j) (v j)) = 0 := by
      simp [orbitSum, tau, hd]
    have hA : areaM (ℓ 0) (ℓ 1) = 0 := by
      rw [areaM, ← hn, absk, hG, Real.sqrt_zero]
    rw [h0, hA]; simp
  · set α : Fin 3 → ℂ := fun j => dotM (hel (s j) (ℓ j) (v j)) n /
      ((absSq (ℓ j) : ℂ) * absSq n) with hα
    have hdec : (fun j => hel (s j) (ℓ j) (v j)) = fun j => α j • wv (ℓ j) n (sl ℓ s j) :=
      funext fun j => hel_decomp ℓ hr hne s v hG j
    have hnorm : ∀ j, ‖hel (s j) (ℓ j) (v j)‖ =
        ‖α j‖ * (Real.sqrt 2 * absSq (ℓ j) * Real.sqrt (absSq n)) := by
      intro j
      rw [congrFun hdec j, norm_smul, norm_wv_leg ℓ hr s j]
    rw [hdec, orbit_core σ ℓ hr (sl ℓ s) (sl_sq ℓ s) α, Fin.prod_univ_three, hnorm, hnorm,
      hnorm, areaM, ← hn]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hg : absk n = Real.sqrt (absSq n) := rfl
    have hG2 : absSq n ^ 2 = Real.sqrt (absSq n) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (absSq_nonneg n)]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [abs_sl, abs_sl, abs_sl, abs_mul, abs_of_nonneg (by positivity), hg, ← absk_sq (ℓ 0),
      ← absk_sq (ℓ 1), ← absk_sq (ℓ 2)]
    rw [hG2]
    set g := Real.sqrt (absSq n)
    set T := |sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2|
    set U := |sobWeight σ (ℓ 2) * (sl ℓ s 1 - sl ℓ s 0) + sobWeight σ (ℓ 0) *
      (sl ℓ s 2 - sl ℓ s 1) + sobWeight σ (ℓ 1) * (sl ℓ s 0 - sl ℓ s 2)|
    linear_combination (-(‖α 0‖ * ‖α 1‖ * ‖α 2‖ * g ^ 4 *
      (absk (ℓ 0) * absk (ℓ 1) * absk (ℓ 2)) ^ 2 * T * U * Real.sqrt 2)) * h2

private lemma prod_absk_pos (ℓ : Fin 3 → Mode) (hne : ∀ j, ℓ j ≠ 0) :
    0 < absk (ℓ 0) * absk (ℓ 1) * absk (ℓ 2) := by
  have h : ∀ j, 0 < absk (ℓ j) := fun j => lt_of_lt_of_le one_pos (one_le_absk (hne j))
  have := h 0; have := h 1; have := h 2
  positivity

/-- The orbit identity with the `H¹` weight. -/
theorem orbit_vertex_H1 (ℓ : Fin 3 → Mode) (hsum : ∑ j, ℓ j = 0) (hne : ∀ j, ℓ j ≠ 0)
    (s : Fin 3 → Sgn) (v : Fin 3 → V3) :
    ‖orbitSum 1 ℓ (fun j => hel (s j) (ℓ j) (v j))‖ =
      6 * gammaC ℓ s * (∏ j, absk (ℓ j)) * ∏ j, ‖hel (s j) (ℓ j) (v j)‖ := by
  have h := orbit_norm 1 ℓ hsum hne s v
  rw [sobWeight_one, sobWeight_one, sobWeight_one, ← sl_sq, ← sl_sq, ← sl_sq] at h
  have hB : (sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2) * (sl ℓ s 2 ^ 2 * (sl ℓ s 1 - sl ℓ s 0) +
      sl ℓ s 0 ^ 2 * (sl ℓ s 2 - sl ℓ s 1) + sl ℓ s 1 ^ 2 * (sl ℓ s 0 - sl ℓ s 2)) =
      (sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2) * (sl ℓ s 0 - sl ℓ s 1) * (sl ℓ s 1 - sl ℓ s 2) *
        (sl ℓ s 2 - sl ℓ s 0) := by ring
  rw [hB] at h
  have ha := prod_absk_pos ℓ hne
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hk : ∀ j, absk (ℓ j) ≠ 0 := fun j => (lt_of_lt_of_le one_pos (one_le_absk (hne j))).ne'
  have hk0 := hk 0
  have hk1 := hk 1
  have hk2 := hk 2
  apply mul_right_cancel₀ (show 2 * Real.sqrt 2 * (absk (ℓ 0) * absk (ℓ 1) * absk (ℓ 2)) ≠ 0
    by positivity)
  rw [h, gammaC]
  simp only [Fin.prod_univ_three]
  field_simp
  ring

/-- The orbit identity with the `H²` weight. -/
theorem orbit_vertex_H2 (ℓ : Fin 3 → Mode) (hsum : ∑ j, ℓ j = 0) (hne : ∀ j, ℓ j ≠ 0)
    (s : Fin 3 → Sgn) (v : Fin 3 → V3) :
    ‖orbitSum 2 ℓ (fun j => hel (s j) (ℓ j) (v j))‖ =
      6 * gammaC ℓ s * |h2C ℓ s| * (∏ j, absk (ℓ j)) * ∏ j, ‖hel (s j) (ℓ j) (v j)‖ := by
  have h := orbit_norm 2 ℓ hsum hne s v
  rw [sobWeight_two, sobWeight_two, sobWeight_two, ← sl_sq, ← sl_sq, ← sl_sq] at h
  have hB : (sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2) * ((sl ℓ s 2 ^ 2) ^ 2 * (sl ℓ s 1 - sl ℓ s 0) +
      (sl ℓ s 0 ^ 2) ^ 2 * (sl ℓ s 2 - sl ℓ s 1) + (sl ℓ s 1 ^ 2) ^ 2 * (sl ℓ s 0 - sl ℓ s 2)) =
      (sl ℓ s 0 + sl ℓ s 1 + sl ℓ s 2) * (sl ℓ s 0 - sl ℓ s 1) * (sl ℓ s 1 - sl ℓ s 2) *
        (sl ℓ s 2 - sl ℓ s 0) * h2C ℓ s := by
    unfold h2C; ring
  rw [hB, abs_mul] at h
  have ha := prod_absk_pos ℓ hne
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hk : ∀ j, absk (ℓ j) ≠ 0 := fun j => (lt_of_lt_of_le one_pos (one_le_absk (hne j))).ne'
  have hk0 := hk 0
  have hk1 := hk 1
  have hk2 := hk 2
  apply mul_right_cancel₀ (show 2 * Real.sqrt 2 * (absk (ℓ 0) * absk (ℓ 1) * absk (ℓ 2)) ≠ 0
    by positivity)
  rw [h, gammaC]
  simp only [Fin.prod_univ_three]
  field_simp
  ring

/-! ### Helicity reversal, pattern structure, contraction, bounds -/

/-- Global helicity reversal preserves resonance, `γ` and `h₂`. -/
theorem resPat_neg (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) :
    ResPat ℓ (fun j => !s j) ↔ ResPat ℓ s := by
  have h : ∑ j, lam (!s j) (ℓ j) = -∑ j, lam (s j) (ℓ j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [lam, sg_not]; ring
  unfold ResPat
  rw [h, neg_eq_zero]

theorem gammaC_neg (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) :
    gammaC ℓ (fun j => !s j) = gammaC ℓ s := by
  simp only [gammaC, sl_not]
  congr 3
  ring

theorem h2C_neg (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) : h2C ℓ (fun j => !s j) = h2C ℓ s := by
  simp only [h2C, sl_not]
  ring

/-- The sign bookkeeping behind `resPat_unique`. -/
private lemma pat_aux (t0 t1 t2 : ℝ) (h0 : t0 ≠ 0) (h1 : t1 ≠ 0) (h2 : t2 ≠ 0)
    (a0 a1 a2 b0 b1 b2 : Bool)
    (ha : sg a0 * t0 + sg a1 * t1 + sg a2 * t2 = 0)
    (hb : sg b0 * t0 + sg b1 * t1 + sg b2 * t2 = 0) :
    (b0 = a0 ∧ b1 = a1 ∧ b2 = a2) ∨ (b0 = !a0 ∧ b1 = !a1 ∧ b2 = !a2) := by
  cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;>
    simp only [sg, ↓reduceIte, Bool.false_eq_true] at ha hb <;> simp <;>
    first
    | exact h0 (by linarith)
    | exact h1 (by linarith)
    | exact h2 (by linarith)

/-- A fast triad has at most two resonant patterns, and they are opposite. -/
theorem resPat_unique (ℓ : Fin 3 → Mode) (hfast : ∀ j, ℓ j 2 ≠ 0) {s s' : Fin 3 → Sgn}
    (hs : ResPat ℓ s) (hs' : ResPat ℓ s') : s' = s ∨ s' = fun j => !s j := by
  have ht : ∀ j, (ℓ j 2 : ℝ) * absk (ℓ j) ≠ 0 := by
    intro j
    have hj : ℓ j ≠ 0 := fun h => hfast j (by simp [h])
    have : 0 < absk (ℓ j) := lt_of_lt_of_le one_pos (one_le_absk hj)
    exact mul_ne_zero (by exact_mod_cast hfast j) this.ne'
  unfold ResPat lam at hs hs'
  simp only [Fin.sum_univ_three, mul_assoc] at hs hs'
  rcases pat_aux _ _ _ (ht 0) (ht 1) (ht 2) _ _ _ _ _ _ hs hs' with h | h
  · left
    funext j
    fin_cases j
    exacts [h.1, h.2.1, h.2.2]
  · right
    funext j
    fin_cases j
    exacts [h.1, h.2.1, h.2.2]

/-- Helicity contraction: the two opposite patterns together are bounded by the modal
magnitudes. -/
theorem hel_contraction (ℓ : Fin 3 → Mode) (hne : ∀ j, ℓ j ≠ 0) (s : Fin 3 → Sgn) {F : Field}
    (hF : IsSolenoidal F) :
    (∏ j, ‖hel (s j) (ℓ j) (F (ℓ j))‖) + ∏ j, ‖hel (!s j) (ℓ j) (F (ℓ j))‖ ≤
      ∏ j, ‖F (ℓ j)‖ := by
  have hsq : ∀ j, ‖hel (s j) (ℓ j) (F (ℓ j))‖ ^ 2 + ‖hel (!s j) (ℓ j) (F (ℓ j))‖ ^ 2 =
      ‖F (ℓ j)‖ ^ 2 := by
    intro j
    have h := norm_sq_hel_sum (ℓ j) (F (ℓ j))
    rw [Fintype.sum_bool, leray_of_perp (hne j) (hF (ℓ j))] at h
    cases s j
    · simpa [add_comm] using h
    · simpa using h
  simp only [Fin.prod_univ_three]
  have h0 := hsq 0
  have h1 := hsq 1
  have h2 := hsq 2
  set a0 := ‖hel (s 0) (ℓ 0) (F (ℓ 0))‖
  set a1 := ‖hel (s 1) (ℓ 1) (F (ℓ 1))‖
  set a2 := ‖hel (s 2) (ℓ 2) (F (ℓ 2))‖
  set b0 := ‖hel (!s 0) (ℓ 0) (F (ℓ 0))‖
  set b1 := ‖hel (!s 1) (ℓ 1) (F (ℓ 1))‖
  set b2 := ‖hel (!s 2) (ℓ 2) (F (ℓ 2))‖
  set c0 := ‖F (ℓ 0)‖
  set c1 := ‖F (ℓ 1)‖
  set c2 := ‖F (ℓ 2)‖
  have key : (a0 * a1 * a2 + b0 * b1 * b2) ^ 2 ≤ (c0 * c1 * c2) ^ 2 := by
    have e : (c0 * c1 * c2) ^ 2 - (a0 * a1 * a2 + b0 * b1 * b2) ^ 2 =
        (a0 * b1 * b2 - b0 * a1 * a2) ^ 2 +
          (a0 ^ 2 + b0 ^ 2) * (a1 ^ 2 * b2 ^ 2 + b1 ^ 2 * a2 ^ 2) := by
      rw [mul_pow, mul_pow, ← h0, ← h1, ← h2]; ring
    nlinarith [sq_nonneg (a0 * b1 * b2 - b0 * a1 * a2), sq_nonneg (a1 * b2), sq_nonneg (b1 * a2),
      sq_nonneg a0, sq_nonneg b0, mul_nonneg (add_nonneg (sq_nonneg a0) (sq_nonneg b0))
        (add_nonneg (sq_nonneg (a1 * b2)) (sq_nonneg (b1 * a2)))]
  have hc : 0 ≤ c0 * c1 * c2 := by positivity
  have ha : 0 ≤ a0 * a1 * a2 + b0 * b1 * b2 := by positivity
  exact (pow_le_pow_iff_left₀ ha hc two_ne_zero).mp key

/-- `|h₂| ≤ 6 K N` on sorted triads `0 < M ≤ K ≤ N ≤ M + K`, for any signs. -/
theorem h2C_le (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) (hM : 0 < absk (ℓ 0))
    (hMK : absk (ℓ 0) ≤ absk (ℓ 1)) (hKN : absk (ℓ 1) ≤ absk (ℓ 2))
    (hN : absk (ℓ 2) ≤ absk (ℓ 0) + absk (ℓ 1)) :
    |h2C ℓ s| ≤ 6 * absk (ℓ 1) * absk (ℓ 2) := by
  have hnn : 0 ≤ h2C ℓ s := by
    unfold h2C
    nlinarith [sq_nonneg (sl ℓ s 0 + sl ℓ s 1), sq_nonneg (sl ℓ s 1 + sl ℓ s 2),
      sq_nonneg (sl ℓ s 2 + sl ℓ s 0)]
  rw [abs_of_nonneg hnn]
  unfold h2C sl
  set M := absk (ℓ 0)
  set K := absk (ℓ 1)
  set N := absk (ℓ 2)
  have hK : 0 < K := by linarith
  have hNp : 0 < N := by linarith
  have hb : 3 * K ^ 2 + N ^ 2 + 2 * K * N ≤ 6 * K * N := by nlinarith
  cases s 0 <;> cases s 1 <;> cases s 2 <;> simp only [sg, ↓reduceIte,
    Bool.false_eq_true] <;> nlinarith [mul_pos hM hK, mul_pos hK hNp, mul_pos hM hNp]

/-- `γ` is nonnegative. -/
theorem gammaC_nonneg (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) : 0 ≤ gammaC ℓ s := by
  unfold gammaC areaM
  exact div_nonneg (mul_nonneg (absk_nonneg _) (abs_nonneg _)) (by positivity)

theorem gammaR_nonneg (ℓ : Fin 3 → Mode) : 0 ≤ gammaR ℓ := by
  unfold gammaR
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ => ?_)
  split_ifs
  · exact gammaC_nonneg ℓ s
  · exact le_rfl

theorem gammaR2_nonneg (ℓ : Fin 3 → Mode) : 0 ≤ gammaR2 ℓ := by
  unfold gammaR2
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ => ?_)
  split_ifs
  · exact mul_nonneg (gammaC_nonneg ℓ s) (abs_nonneg _)
  · exact le_rfl
end OVNS.Quant
