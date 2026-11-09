import OddViscousNS.Closed.Gram

/-!
# The pair Gram inequality

Item 2 of `OddViscousNS_data/reports/uf661_row_operator.md` (Lemma `pair Gram`).  For a
non-collinear triad `p + l = k` (all nonzero), the bilinear map `V(f,g) = T(p,l,-k)(f,g,·)/6`
on `p^⊥ × l^⊥` has Hilbert–Schmidt Gram `c* V V* c = gramQ p l k c / 36`, whence
`|T(p,l,-k)(f,g,c)|² ≤ ‖f‖² ‖g‖² · gramQ p l k c` for `f ⊥ p`, `g ⊥ l`, `c ⊥ k`.
Collinear triads (`p × k = 0`) give `T = 0` and `gramQ = 0`.

Suggested route (report item G9): expand `f` in the real orthogonal basis `{E, p × E}` of `p^⊥`
(`E = p × k`, `|E|² = D²`, `|p × E|² = A_p D²`), similarly `g` in `{E, l × E}` of `l^⊥`, so that
`T(f,g,c)` is bilinear in the four complex coordinates with coefficients polynomial in the integer
coordinates of `p, k` and in `E·c`, `N·c` (`N = k × E`); then the Cauchy–Schwarz inequality in
`ℂ⁴` and the closed form of the coefficient sum of squares.  All constants are explicit; check
them numerically first (e.g. in Python) before proving.
-/

open scoped ENNReal ComplexConjugate

namespace OVNS

/-- Integer cross product of two modes. -/
private def icross (a b : Mode) : Mode :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- `modeVec` intertwines the integer and complex cross products. -/
private theorem cross_modeVec (a b : Mode) :
    cross (modeVec a) (modeVec b) = modeVec (icross a b) := by
  ext i; fin_cases i <;> simp [cross, modeVec, icross]

/-- Orthogonal decomposition of `v` in the basis `{a × b, a × (a × b), a}`. -/
private theorem decomp (a b : Mode) (v : V3) :
    ((absSq a * absSq (icross a b) : ℝ) : ℂ) • v =
      ((absSq a : ℂ) * dotV (modeVec (icross a b)) v) • modeVec (icross a b)
      + dotV (modeVec (icross a (icross a b))) v • modeVec (icross a (icross a b))
      + ((absSq (icross a b) : ℂ) * dotM v a) • modeVec a := by
  ext i; fin_cases i <;> simp [absSq, dotV, dotM, modeVec, icross, Fin.sum_univ_three] <;> ring

/-- `triT p l (-(p + l))` with free complex metric coefficients. -/
private def T0 (p l : Mode) (hp hl hk : ℂ) (a b c : V3) : ℂ :=
  (hk - hl) * det3 (curlS p a) b c + (hp - hk) * det3 a (curlS l b) c
    + (hl - hp) * det3 a b (curlS (-(p + l)) c)

/-- Homogeneity of `T0` in all three slots. -/
private theorem T0_smul (p l : Mode) (hp hl hk x y z : ℂ) (a b c : V3) :
    T0 p l hp hl hk (x • a) (y • b) (z • c) = x * y * z * T0 p l hp hl hk a b c := by
  simp [T0, det3, dotV, curlS, cross, Fin.sum_univ_three]; ring

/-- Additivity of `T0` in the first slot. -/
private theorem T0_add1 (p l : Mode) (hp hl hk : ℂ) (a a' b c : V3) :
    T0 p l hp hl hk (a + a') b c = T0 p l hp hl hk a b c + T0 p l hp hl hk a' b c := by
  simp [T0, det3, dotV, curlS, cross, Fin.sum_univ_three]; ring

/-- Additivity of `T0` in the second slot. -/
private theorem T0_add2 (p l : Mode) (hp hl hk : ℂ) (a b b' c : V3) :
    T0 p l hp hl hk a (b + b') c = T0 p l hp hl hk a b c + T0 p l hp hl hk a b' c := by
  simp [T0, det3, dotV, curlS, cross, Fin.sum_univ_three]; ring

/-- Additivity of `T0` in the third slot. -/
private theorem T0_add3 (p l : Mode) (hp hl hk : ℂ) (a b c c' : V3) :
    T0 p l hp hl hk a b (c + c') = T0 p l hp hl hk a b c + T0 p l hp hl hk a b c' := by
  simp [T0, det3, dotV, curlS, cross, Fin.sum_univ_three]; ring

/-- Homogeneity of `T0` in the first slot. -/
private theorem T0_smul1 (p l : Mode) (hp hl hk x : ℂ) (a b c : V3) :
    T0 p l hp hl hk (x • a) b c = x * T0 p l hp hl hk a b c := by
  simp [T0, det3, dotV, curlS, cross, Fin.sum_univ_three]; ring

/-- Homogeneity of `T0` in the second slot. -/
private theorem T0_smul2 (p l : Mode) (hp hl hk x : ℂ) (a b c : V3) :
    T0 p l hp hl hk a (x • b) c = x * T0 p l hp hl hk a b c := by
  simp [T0, det3, dotV, curlS, cross, Fin.sum_univ_three]; ring

/-- Homogeneity of `T0` in the third slot. -/
private theorem T0_smul3 (p l : Mode) (hp hl hk x : ℂ) (a b c : V3) :
    T0 p l hp hl hk a b (x • c) = x * T0 p l hp hl hk a b c := by
  simp [T0, det3, dotV, curlS, cross, Fin.sum_univ_three]; ring

/-- The eight values of `T0` on the bases `{E,P}`, `{E,Q}`, `{E,N}`. -/
private theorem T0_basis (p l : Mode) (hp hl hk : ℂ) :
    let E := modeVec (icross p l)
    let P := modeVec (icross p (icross p l))
    let Q := modeVec (icross l (icross p l))
    let N := modeVec (icross (p + l) (icross p l))
    let D := (absSq (icross p l) : ℂ)
    T0 p l hp hl hk E E E = 0 ∧ T0 p l hp hl hk E E N = Complex.I * (hl - hp) * D ^ 2 ∧
    T0 p l hp hl hk E Q E = - Complex.I * (hp - hk) * D ^ 2 ∧ T0 p l hp hl hk E Q N = 0 ∧
    T0 p l hp hl hk P E E = - Complex.I * (hk - hl) * D ^ 2 ∧ T0 p l hp hl hk P E N = 0 ∧
    T0 p l hp hl hk P Q E = 0 ∧
    T0 p l hp hl hk P Q N = Complex.I * ((absSq p : ℂ) * (hk - hl) + (absSq l : ℂ) * (hp - hk)
        + (absSq (p + l) : ℂ) * (hl - hp)) * D ^ 2 := by
  intro E P Q N D
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [E, P, Q, N, D, T0, det3, dotV, curlS, cross, modeVec, icross, absSq,
    Fin.sum_univ_three] <;> ring

/-- Trilinear expansion of `T0` in the bases `{E,P}`, `{E,Q}`, `{E,N}`. -/
private theorem T0_expand (p l : Mode) (hp hl hk x1 x2 y1 y2 z1 z2 : ℂ) :
    let E := modeVec (icross p l)
    let P := modeVec (icross p (icross p l))
    let Q := modeVec (icross l (icross p l))
    let N := modeVec (icross (p + l) (icross p l))
    let D := (absSq (icross p l) : ℂ)
    T0 p l hp hl hk (x1 • E + x2 • P) (y1 • E + y2 • Q) (z1 • E + z2 • N) =
      Complex.I * D ^ 2 * (x1 * y1 * z2 * (hl - hp) - x1 * y2 * z1 * (hp - hk)
        - x2 * y1 * z1 * (hk - hl) + x2 * y2 * z2 * ((absSq p : ℂ) * (hk - hl)
        + (absSq l : ℂ) * (hp - hk) + (absSq (p + l) : ℂ) * (hl - hp))) := by
  intro E P Q N D
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := T0_basis p l hp hl hk
  simp only [T0_add1, T0_add2, T0_add3, T0_smul1, T0_smul2, T0_smul3]
  rw [h1, h2, h3, h4, h5, h6, h7, h8]; ring

/-- Squared norm of a combination of the orthogonal real vectors `a × b`, `a × (a × b)`. -/
private theorem normsq (a b : Mode) (x y : ℂ) :
    ‖x • modeVec (icross a b) + y • modeVec (icross a (icross a b))‖ ^ 2 =
      (‖x‖ ^ 2 + ‖y‖ ^ 2 * absSq a) * absSq (icross a b) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Complex.sq_norm, Complex.normSq_apply, modeVec, icross, absSq, Fin.sum_univ_three]
  ring

/-- Three vectors orthogonal to a nonzero `n` have zero determinant. -/
private theorem det_zero (n a b c : V3) (hn : n ≠ 0) (h1 : dotV n a = 0) (h2 : dotV n b = 0)
    (h3 : dotV n c = 0) : det3 a b c = 0 := by
  have key : ∀ i, det3 a b c * n i = dotV n a * cross b c i + dotV n b * cross c a i
      + dotV n c * cross a b i := by
    intro i; fin_cases i <;> simp [det3, dotV, cross, Fin.sum_univ_three] <;> ring
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h; push Not at h; exact hn (by ext i; simp [h i])
  have := key i
  rw [h1, h2, h3] at this
  simpa [hi] using this

/-- If `p × m = 0`, `m ≠ 0` and `v ⊥ m`, then `v ⊥ p`. -/
private theorem perp_transfer (p m : Mode) (v : V3) (hpm : icross p m = 0) (hm0 : m ≠ 0)
    (hv : dotM v m = 0) : dotV (modeVec p) v = 0 := by
  have key : ∀ i, (m i : ℂ) * dotV (modeVec p) v = (p i : ℂ) * dotM v m
      + cross (modeVec (icross p m)) v i := by
    intro i; fin_cases i <;> simp [dotV, dotM, cross, modeVec, icross, Fin.sum_univ_three] <;> ring
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h; push Not at h; exact hm0 (by ext i; simp [h i])
  have := key i
  rw [hv, hpm] at this
  have hi' : (m i : ℂ) ≠ 0 := by exact_mod_cast hi
  have h0 : cross (modeVec 0) v i = 0 := by fin_cases i <;> simp [cross, modeVec]
  rw [h0] at this
  simpa [hi'] using this

/-- Weighted Cauchy–Schwarz inequality with four terms. -/
private theorem cs4 (w1 w2 w3 w4 a1 a2 a3 a4 b1 b2 b3 b4 : ℝ) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2)
    (h3 : 0 ≤ w3) (h4 : 0 ≤ w4) :
    (w1 * a1 * b1 + w2 * a2 * b2 + w3 * a3 * b3 + w4 * a4 * b4) ^ 2 ≤
      (w1 * a1 ^ 2 + w2 * a2 ^ 2 + w3 * a3 ^ 2 + w4 * a4 ^ 2) *
      (w1 * b1 ^ 2 + w2 * b2 ^ 2 + w3 * b3 ^ 2 + w4 * b4 ^ 2) := by
  nlinarith [mul_nonneg (mul_nonneg h1 h2) (sq_nonneg (a1 * b2 - a2 * b1)),
    mul_nonneg (mul_nonneg h1 h3) (sq_nonneg (a1 * b3 - a3 * b1)),
    mul_nonneg (mul_nonneg h1 h4) (sq_nonneg (a1 * b4 - a4 * b1)),
    mul_nonneg (mul_nonneg h2 h3) (sq_nonneg (a2 * b3 - a3 * b2)),
    mul_nonneg (mul_nonneg h2 h4) (sq_nonneg (a2 * b4 - a4 * b2)),
    mul_nonneg (mul_nonneg h3 h4) (sq_nonneg (a3 * b4 - a4 * b3))]

/-- The real-variable core of the pair Gram inequality. -/
private theorem final_real (Ap Al Ak D t F Gg a1 a2 b1 b2 g1 g2 e1 e2 e3 eL G : ℝ)
    (hAp : 0 < Ap) (hAl : 0 < Al) (hAk : 0 < Ak) (hD : 0 < D) (ht : 0 ≤ t)
    (hF : (Ap * D) ^ 2 * F = (Ap ^ 2 * a1 ^ 2 + Ap * a2 ^ 2) * D)
    (hGg : (Al * D) ^ 2 * Gg = (Al ^ 2 * b1 ^ 2 + Al * b2 ^ 2) * D)
    (hT : t * (Ap * Al * Ak * D) ≤ Ap * Al * a1 * b1 * (g2 * e3) + Ap * a1 * b2 * (Ak * g1 * e2)
      + Al * a2 * b1 * (Ak * g1 * e1) + a2 * b2 * (g2 * eL))
    (hG : G = ((Al * Ak * e1 ^ 2 + Ap * Ak * e2 ^ 2) * g1 ^ 2
      + (eL ^ 2 + Ap * Al * e3 ^ 2) * g2 ^ 2 / Ak) / (Ap * Al * Ak)) :
    t ^ 2 ≤ F * Gg * G := by
  have hcs := cs4 (Ap * Al) Ap Al 1 (a1 * b1) (a1 * b2) (a2 * b1) (a2 * b2) (g2 * e3)
    (Ak * g1 * e2) (Ak * g1 * e1) (g2 * eL) (by positivity) hAp.le hAl.le zero_le_one
  have hF' : Ap * a1 ^ 2 + a2 ^ 2 = Ap * D * F := by
    have : (Ap * D) * (Ap * a1 ^ 2 + a2 ^ 2) = (Ap * D) * (Ap * D * F) := by
      linear_combination -hF
    exact mul_left_cancel₀ (by positivity) this
  have hGg' : Al * b1 ^ 2 + b2 ^ 2 = Al * D * Gg := by
    have : (Al * D) * (Al * b1 ^ 2 + b2 ^ 2) = (Al * D) * (Al * D * Gg) := by
      linear_combination -hGg
    exact mul_left_cancel₀ (by positivity) this
  have hX : Ap * Al * (a1 * b1) ^ 2 + Ap * (a1 * b2) ^ 2 + Al * (a2 * b1) ^ 2 + 1 * (a2 * b2) ^ 2
      = (Ap * Al * D ^ 2) * (F * Gg) := by
    linear_combination (Al * b1 ^ 2 + b2 ^ 2) * hF' + (Ap * D * F) * hGg'
  have hY : Ap * Al * (g2 * e3) ^ 2 + Ap * (Ak * g1 * e2) ^ 2 + Al * (Ak * g1 * e1) ^ 2
      + 1 * (g2 * eL) ^ 2 = (Ap * Al * Ak ^ 2) * G := by
    rw [hG]; field_simp; ring
  rw [hX, hY] at hcs
  have hR : 0 < Ap * Al * Ak * D := by positivity
  have h5 : (t * (Ap * Al * Ak * D)) ^ 2 ≤
      (Ap * Al * D ^ 2) * (F * Gg) * ((Ap * Al * Ak ^ 2) * G) :=
    le_trans (pow_le_pow_left₀ (by positivity) hT 2) (by linarith [hcs])
  have h6 : t ^ 2 * (Ap * Al * Ak * D) ^ 2 ≤ (F * Gg * G) * (Ap * Al * Ak * D) ^ 2 := by
    linear_combination h5
  exact le_of_mul_le_mul_right h6 (by positivity)

/-- Triangle inequality for `a - b - c + d`. -/
private theorem norm4 (a b c d : ℂ) : ‖a - b - c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have e4 := norm_add_le (a - b - c) d
  have e3 := norm_sub_le (a - b) c
  have e2 := norm_sub_le a b
  linarith

/-- `|a|² > 0` for a nonzero mode. -/
private theorem absSq_pos' {a : Mode} (h : a ≠ 0) : 0 < absSq a := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h'; push Not at h'; exact h (by ext i; simp [h' i])
  have hi' : (0 : ℝ) < (a i : ℝ) ^ 2 := by positivity
  exact lt_of_lt_of_le hi' (Finset.single_le_sum (f := fun j ↦ (a j : ℝ) ^ 2)
    (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i))

/-- `h(|-k|²) = h(|k|²)`. -/
private theorem hm_neg (k : Mode) : hm (-k) = hm k := by
  simp [hm, nsq]

/-- `p × (p + l) = p × l`. -/
private theorem icross_p_pl (p l : Mode) : icross p (p + l) = icross p l := by
  ext i; fin_cases i <;> simp [icross] <;> ring

/-- `l × (-p) = p × l`. -/
private theorem icross_l_np (p l : Mode) : icross l (-p) = icross p l := by
  ext i; fin_cases i <;> simp [icross] <;> ring

/-- `(p + l) × (-p) = p × l`. -/
private theorem icross_pl_np (p l : Mode) : icross (p + l) (-p) = icross p l := by
  ext i; fin_cases i <;> simp [icross] <;> ring

/-- For collinear triads `T0` vanishes on the orthogonal complements. -/
private theorem T0_collinear (p l : Mode) (hp : p ≠ 0) (hl : l ≠ 0) (hk0 : p + l ≠ 0)
    (hE : icross p l = 0) (hp' hl' hk' : ℂ) {f g c : V3} (hf : dotM f p = 0)
    (hg : dotM g l = 0) (hc : dotM c (p + l) = 0) : T0 p l hp' hl' hk' f g c = 0 := by
  have hn : modeVec p ≠ 0 := by
    intro h; apply hp; ext i
    have := congrArg (fun v : V3 ↦ v i) h
    simpa [modeVec] using this
  have h0 : ∀ v : V3, dotV (modeVec 0) v = 0 := fun v ↦ by simp [dotV, modeVec]
  have hfp : dotV (modeVec p) f = 0 := by
    rw [← hf]; simp [dotV, dotM, modeVec, mul_comm]
  have hgp : dotV (modeVec p) g = 0 := perp_transfer p l g hE hl hg
  have hcp : dotV (modeVec p) c = 0 :=
    perp_transfer p (p + l) c (by rw [icross_p_pl, hE]) hk0 hc
  have h1 : dotV (modeVec p) (curlS p f) = 0 := by
    simp [dotV, curlS, cross, modeVec, Fin.sum_univ_three]; ring
  have h2 : dotV (modeVec p) (curlS l g) = Complex.I * dotV (modeVec (icross p l)) g := by
    simp [dotV, curlS, cross, modeVec, icross, Fin.sum_univ_three]; ring
  have h3 : dotV (modeVec p) (curlS (-(p + l)) c) =
      -Complex.I * dotV (modeVec (icross p l)) c := by
    simp [dotV, curlS, cross, modeVec, icross, Fin.sum_univ_three]; ring
  rw [hE, h0, mul_zero] at h2 h3
  simp only [T0]
  rw [det_zero _ _ _ _ hn h1 hgp hcp, det_zero _ _ _ _ hn hfp h2 hcp,
    det_zero _ _ _ _ hn hfp hgp h3]
  ring

theorem triT_sq_le {p l k : Mode} (hk : p + l = k) (hp : p ≠ 0) (hl : l ≠ 0) (hk0 : k ≠ 0)
    {f g c : V3} (hf : dotM f p = 0) (hg : dotM g l = 0) (hc : dotM c k = 0) :
    ‖triT p l (-k) f g c‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 * gramQ p l k c := by
  subst hk
  have hT : triT p l (-(p + l)) f g c = T0 p l (hm p) (hm l) (hm (p + l)) f g c := by
    simp only [triT, T0, hm_neg]; push_cast; ring
  have hcr : cross (modeVec p) (modeVec (p + l)) = modeVec (icross p l) := by
    rw [cross_modeVec, icross_p_pl]
  have hnz : ¬ (p = 0 ∨ l = 0 ∨ p + l = 0) := by simp [hp, hl, hk0]
  rw [hT]
  by_cases hE : icross p l = 0
  · have hG : gramQ p l (p + l) c = 0 := by
      simp only [gramQ, hnz, ↓reduceIte]
      rw [hcr, cross_modeVec, hE]
      have h0 : ∀ v : V3, dotV (modeVec 0) v = 0 := fun v ↦ by simp [dotV, modeVec]
      have h1 : icross (p + l) 0 = 0 := by ext i; fin_cases i <;> simp [icross]
      simp [h0, h1]
    rw [T0_collinear p l hp hl hk0 hE _ _ _ hf hg hc, hG]; simp
  · set e := icross p l with he
    have hD : 0 < absSq e := absSq_pos' hE
    have hAp : 0 < absSq p := absSq_pos' hp
    have hAl : 0 < absSq l := absSq_pos' hl
    have hAk : 0 < absSq (p + l) := absSq_pos' hk0
    have hf' := decomp p l f
    rw [← he, hf, mul_zero, zero_smul, add_zero] at hf'
    have hg' := decomp l (-p) g
    rw [icross_l_np, ← he, hg, mul_zero, zero_smul, add_zero] at hg'
    have hc' := decomp (p + l) (-p) c
    rw [icross_pl_np, ← he, hc, mul_zero, zero_smul, add_zero] at hc'
    set α := dotV (modeVec e) f
    set α' := dotV (modeVec (icross p e)) f
    set β := dotV (modeVec e) g
    set β' := dotV (modeVec (icross l e)) g
    set γ := dotV (modeVec e) c
    set γ' := dotV (modeVec (icross (p + l) e)) c
    set Ap := absSq p
    set Al := absSq l
    set Ak := absSq (p + l)
    set D := absSq e
    set d₁ := hm (p + l) - hm l
    set d₂ := hm p - hm (p + l)
    set d₃ := hm l - hm p
    set Ls := Ap * d₁ + Al * d₂ + Ak * d₃
    have key : ((Ap * D : ℝ) : ℂ) * ((Al * D : ℝ) : ℂ) * ((Ak * D : ℝ) : ℂ) *
        T0 p l (hm p) (hm l) (hm (p + l)) f g c = Complex.I * (D : ℂ) ^ 2 *
        ((Ap : ℂ) * α * ((Al : ℂ) * β) * γ' * (d₃ : ℂ)
        - (Ap : ℂ) * α * β' * ((Ak : ℂ) * γ) * (d₂ : ℂ)
        - α' * ((Al : ℂ) * β) * ((Ak : ℂ) * γ) * (d₁ : ℂ) + α' * β' * γ' * (Ls : ℂ)) := by
      rw [← T0_smul, hf', hg', hc', he, T0_expand]
      simp only [Ls, d₁, d₂, d₃, Ap, Al, Ak, D]; push_cast; ring
    have nr : ∀ r : ℝ, 0 ≤ r → ‖(r : ℂ)‖ = r := fun r hr ↦ by
      rw [Complex.norm_real, Real.norm_of_nonneg hr]
    have hF : (Ap * D) ^ 2 * ‖f‖ ^ 2 = (Ap ^ 2 * ‖α‖ ^ 2 + Ap * ‖α'‖ ^ 2) * D := by
      have h1 := congrArg (fun v : V3 ↦ ‖v‖ ^ 2) hf'
      have h2 := normsq p l ((Ap : ℂ) * α) α'
      rw [← he] at h2
      rw [h2, norm_smul, nr _ (by positivity), norm_mul, nr _ hAp.le] at h1
      linear_combination h1
    have hGg : (Al * D) ^ 2 * ‖g‖ ^ 2 = (Al ^ 2 * ‖β‖ ^ 2 + Al * ‖β'‖ ^ 2) * D := by
      have h1 := congrArg (fun v : V3 ↦ ‖v‖ ^ 2) hg'
      have h2 := normsq l (-p) ((Al : ℂ) * β) β'
      rw [icross_l_np, ← he] at h2
      rw [h2, norm_smul, nr _ (by positivity), norm_mul, nr _ hAl.le] at h1
      linear_combination h1
    have hTn : ‖T0 p l (hm p) (hm l) (hm (p + l)) f g c‖ * (Ap * Al * Ak * D) ≤
        Ap * Al * ‖α‖ * ‖β‖ * (‖γ'‖ * |d₃|) + Ap * ‖α‖ * ‖β'‖ * (Ak * ‖γ‖ * |d₂|)
        + Al * ‖α'‖ * ‖β‖ * (Ak * ‖γ‖ * |d₁|) + ‖α'‖ * ‖β'‖ * (‖γ'‖ * |Ls|) := by
      have h1 := congrArg norm key
      simp only [norm_mul, norm_pow, Complex.norm_I, nr _ hD.le, nr _ (mul_pos hAp hD).le,
        nr _ (mul_pos hAl hD).le, nr _ (mul_pos hAk hD).le, one_mul] at h1
      have hB := norm4 ((Ap : ℂ) * α * ((Al : ℂ) * β) * γ' * (d₃ : ℂ))
        ((Ap : ℂ) * α * β' * ((Ak : ℂ) * γ) * (d₂ : ℂ))
        (α' * ((Al : ℂ) * β) * ((Ak : ℂ) * γ) * (d₁ : ℂ)) (α' * β' * γ' * (Ls : ℂ))
      simp only [norm_mul, nr _ hAp.le, nr _ hAl.le, nr _ hAk.le, Complex.norm_real,
        Real.norm_eq_abs] at hB
      have hD2 : 0 < D ^ 2 := by positivity
      refine le_of_mul_le_mul_left ?_ hD2
      have : D ^ 2 * (‖T0 p l (hm p) (hm l) (hm (p + l)) f g c‖ * (Ap * Al * Ak * D)) =
          Ap * D * (Al * D) * (Ak * D) * ‖T0 p l (hm p) (hm l) (hm (p + l)) f g c‖ := by ring
      rw [this, h1]
      refine mul_le_mul_of_nonneg_left (hB.trans (le_of_eq ?_)) hD2.le
      ring
    have hG : gramQ p l (p + l) c = ((Al * Ak * |d₁| ^ 2 + Ap * Ak * |d₂| ^ 2) * ‖γ‖ ^ 2
        + (|Ls| ^ 2 + Ap * Al * |d₃| ^ 2) * ‖γ'‖ ^ 2 / Ak) / (Ap * Al * Ak) := by
      simp only [sq_abs, gramQ, hnz, ↓reduceIte]
      rw [hcr, cross_modeVec]
    exact final_real Ap Al Ak D _ _ _ ‖α‖ ‖α'‖ ‖β‖ ‖β'‖ ‖γ‖ ‖γ'‖ |d₁| |d₂| |d₃| |Ls| _ hAp hAl hAk
      hD (norm_nonneg _) hF hGg hTn hG


theorem gramQ_nonneg (p l k : Mode) (c : V3) : 0 ≤ gramQ p l k c := by
  simp only [gramQ, absSq]
  split_ifs
  · exact le_rfl
  · positivity

end OVNS
