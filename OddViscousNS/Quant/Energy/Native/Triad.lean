import OddViscousNS.Quant.Energy.Native.Bound

/-!
# Theorem 1.2, fixed force — E5/E8 native layer: the triad expansion of `D_j^N`

For real fields, each slot pairing of the near differential `nearD` is a triad sum
(`inner_Qm`, `pair_eq_tsum` of `Trilinear.lean`); relabelling the second and third pairings by the
cyclic permutation `rho` puts the direction `Π_F h` on the first leg of every triad, so that
`D_j^N(F; h) = Re Σ_{(p,q)} T(p, q)` with `T` the sum of the three rootings of the triad
`(p, q, −(p+q))` carrying `Π_F h` at `p` (`nearTriadTerm`, `nearD_eq_tsum_triad`).

Reality (`IsReal F`, `IsReal h`) is what turns the conjugated test amplitude of each pairing into
a field amplitude on the reflected leg (`inner_hel_real`); without it the three rootings do not
carry the same amplitudes and the cyclic cancellation of `Kernel.lean` is unavailable.
-/

noncomputable section

namespace OVNS.Quant

/-! ### `ℓ²`/`ℓ¹` facts and three-leg products -/

private lemma l2_grad_of_one {X : Field} (hX : MZ 1 X) :
    Summable fun k => (absk k * ‖X k‖) ^ 2 :=
  hX.inH.congr fun k => by rw [sobWeight_one, mul_pow, absk_sq]

private lemma l2_of_one {X : Field} (hX : MZ 1 X) : Summable fun k => ‖X k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (l2_grad_of_one hX)
  by_cases hk : k = 0
  · subst hk
    simp [hX.mean]
  · have h1 : 1 ≤ absk k ^ 2 := one_le_pow₀ (one_le_absk hk)
    rw [mul_pow]
    nlinarith [sq_nonneg ‖X k‖]

private lemma l2_hess_of_two {X : Field} (hX : MZ 2 X) :
    Summable fun k => (absk k ^ 2 * ‖X k‖) ^ 2 :=
  hX.inH.congr fun k => by rw [sobWeight_two, mul_pow, absk_sq]

/-- The three-leg product `α(p) β(q) γ(−(p+q))`. -/
def leg3 (α β γ : Mode → ℝ) (x : Mode × Mode) : ℝ := α x.1 * β x.2 * γ (-(x.1 + x.2))

private lemma leg3_rho (α β γ : Mode → ℝ) (x : Mode × Mode) :
    leg3 β γ α (rho x) = leg3 α β γ x := by
  have e : -(x.2 + -(x.1 + x.2)) = x.1 := by abel
  change β x.2 * γ (-(x.1 + x.2)) * α (-(x.2 + -(x.1 + x.2))) = _
  rw [e, leg3]
  ring

private lemma summable_leg3_one {α β γ : Mode → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hγ0 : ∀ k, 0 ≤ γ k) (hα : Summable α) (hβ : Summable fun k => β k ^ 2)
    (hγ : Summable fun k => γ k ^ 2) : Summable (leg3 α β γ) := by
  have hγ' : Summable fun k => γ (-k) ^ 2 :=
    (Equiv.neg Mode).summable_iff.mpr hγ
  exact (triple_bound hα0 hβ0 (fun k => hγ0 (-k)) hα hβ hγ').1

/-- A three-leg product with one `ℓ¹` factor and two `ℓ²` factors is summable. -/
theorem summable_leg3 {α β γ : Mode → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hγ0 : ∀ k, 0 ≤ γ k)
    (h : (Summable α ∧ Summable (fun k => β k ^ 2) ∧ Summable (fun k => γ k ^ 2)) ∨
      (Summable β ∧ Summable (fun k => γ k ^ 2) ∧ Summable (fun k => α k ^ 2)) ∨
      (Summable γ ∧ Summable (fun k => α k ^ 2) ∧ Summable (fun k => β k ^ 2))) :
    Summable (leg3 α β γ) := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact summable_leg3_one hα0 hβ0 hγ0 h1 h2 h3
  · have := summable_leg3_one hβ0 hγ0 hα0 h1 h2 h3
    exact (rho.summable_iff.mpr this).congr (leg3_rho α β γ)
  · have := summable_leg3_one hγ0 hα0 hβ0 h1 h2 h3
    have h' := rho.summable_iff.mpr (rho.summable_iff.mpr this)
    refine h'.congr fun x => ?_
    simp only [Function.comp]
    rw [leg3_rho, leg3_rho]

/-! ### One rooting: the weighted triad summand and its majorant -/

/-- One rooting of the near differential: the weighted triad summand
`|p+q|^{2j} · tripT_{nearCorrM}(X, Y, Z)(p, q)` of `pair j Z (nearCorr X Y)`. -/
def nearTri (j : ℕ) (ε r τ : ℝ) (X Y Z : Field) (x : Mode × Mode) : ℂ :=
  (sobWeight j (x.1 + x.2) : ℂ) * tripT (nearCorrM ε r τ) X Y Z x.1 x.2

/-- The absolute majorant `|p+q|^{2j−2} (|p| + |q|) ‖X_p‖ ‖Y_q‖ ‖Z_{−(p+q)}‖`. -/
def nearMaj (j : ℕ) (X Y Z : Field) (x : Mode × Mode) : ℝ :=
  absk (x.1 + x.2) ^ (2 * j - 2) *
    ((absk x.1 + absk x.2) * ‖X x.1‖ * ‖Y x.2‖ * ‖Z (-(x.1 + x.2))‖)

private lemma sobWeight_nat_eq {j : ℕ} (hj : 1 ≤ j) {k : Mode} (hk : k ≠ 0) :
    sobWeight j k = absk k ^ (2 * j - 2) * absSq k := by
  have e : (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) := by push_cast; ring
  have hw : sobWeight j k = absk k ^ (2 * (j : ℝ)) := by simp [sobWeight, hk]
  rw [hw, e, Real.rpow_natCast, ← absk_sq, ← pow_add]
  congr 1
  omega

theorem norm_nearTri_le {j : ℕ} (hj : 1 ≤ j) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ)
    (X Y Z : Field) (x : Mode × Mode) :
    ‖nearTri j ε r τ X Y Z x‖ ≤ 8 * nearMaj j X Y Z x := by
  obtain ⟨p, q⟩ := x
  simp only [nearTri, nearMaj]
  set E := (absk p + absk q) * ‖X p‖ * ‖Y q‖ * ‖Z (-(p + q))‖ with hE
  have hE0 : 0 ≤ E := by
    have := absk_nonneg p
    have := absk_nonneg q
    positivity
  by_cases hk : p + q = 0
  · have h0 : tripT (nearCorrM ε r τ) X Y Z p q = 0 := by
      simp [tripT, nearCorrM, NearT, hk]
    rw [h0, mul_zero, norm_zero]
    exact mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg (absk_nonneg _) _) hE0)
  have hS : 0 < absSq (p + q) := lt_of_lt_of_le one_pos (one_le_absSq hk)
  have hterm : ∀ a b c, ‖nearCorrM ε r τ a b c p q *
      tau p q (hel a p (X p)) (hel b q (Y q)) (hel c (-(p + q)) (Z (-(p + q))))‖ ≤
        1 / absSq (p + q) * E := by
    intro a b c
    rw [norm_mul]
    have hm : ‖nearCorrM ε r τ a b c p q‖ ≤ 1 / absSq (p + q) := by
      unfold nearCorrM
      split_ifs
      · exact norm_corrSym_le hε r τ a b c hk
      · simp only [norm_zero]
        positivity
    have ht : ‖tau p q (hel a p (X p)) (hel b q (Y q)) (hel c (-(p + q)) (Z (-(p + q))))‖ ≤
        E := by
      refine (norm_tau_le _ _ _ _ _).trans ?_
      have h1 := norm_hel_le a p (X p)
      have h2 := norm_hel_le b q (Y q)
      have h3 := norm_hel_le c (-(p + q)) (Z (-(p + q)))
      have := absk_nonneg p
      have := absk_nonneg q
      rw [hE]
      gcongr
    exact mul_le_mul hm ht (norm_nonneg _) (by positivity)
  have hbd : ‖tripT (nearCorrM ε r τ) X Y Z p q‖ ≤
      ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, 1 / absSq (p + q) * E :=
    norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
      norm_sum_le_of_le _ fun c _ => hterm a b c
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul] at hbd
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sobWeight_nonneg _ _),
    sobWeight_nat_eq hj hk]
  have hA := pow_nonneg (absk_nonneg (p + q)) (2 * j - 2)
  calc absk (p + q) ^ (2 * j - 2) * absSq (p + q) * ‖tripT (nearCorrM ε r τ) X Y Z p q‖
      ≤ absk (p + q) ^ (2 * j - 2) * absSq (p + q) * (2 * (2 * (2 * (1 / absSq (p + q) * E)))) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hbd) (by positivity)
    _ = 8 * (absk (p + q) ^ (2 * j - 2) * E) := by
        field_simp
        ring

private lemma nearMaj_one (X Y Z : Field) (x : Mode × Mode) :
    nearMaj 1 X Y Z x = leg3 (fun k => absk k * ‖X k‖) (fun k => ‖Y k‖) (fun k => ‖Z k‖) x +
      leg3 (fun k => ‖X k‖) (fun k => absk k * ‖Y k‖) (fun k => ‖Z k‖) x := by
  simp only [nearMaj, leg3]
  norm_num
  ring

private lemma nearMaj_two (X Y Z : Field) (x : Mode × Mode) :
    nearMaj 2 X Y Z x =
      leg3 (fun k => absk k * ‖X k‖) (fun k => ‖Y k‖) (fun k => absk k ^ 2 * ‖Z k‖) x +
        leg3 (fun k => ‖X k‖) (fun k => absk k * ‖Y k‖) (fun k => absk k ^ 2 * ‖Z k‖) x := by
  simp only [nearMaj, leg3, absk_neg]
  norm_num
  ring

/-- Summability of the `j = 1` majorant: `H¹` fields, with an `ℓ¹` factor available for each of
the two derivative placements. -/
theorem summable_nearMaj_one {X Y Z : Field} (hX : MZ 1 X) (hY : MZ 1 Y) (hZ : MZ 1 Z)
    (h1 : Summable (fun k => ‖Y k‖) ∨ Summable (fun k => ‖Z k‖))
    (h2 : Summable (fun k => ‖X k‖) ∨ Summable (fun k => ‖Z k‖)) :
    Summable (nearMaj 1 X Y Z) := by
  have g0 : ∀ (W : Field) k, 0 ≤ absk k * ‖W k‖ := fun W k =>
    mul_nonneg (absk_nonneg k) (norm_nonneg _)
  have n0 : ∀ (W : Field) k, 0 ≤ ‖W k‖ := fun W k => norm_nonneg _
  have s1 : Summable (leg3 (fun k => absk k * ‖X k‖) (fun k => ‖Y k‖) (fun k => ‖Z k‖)) := by
    refine summable_leg3 (g0 X) (n0 Y) (n0 Z) ?_
    rcases h1 with h | h
    · exact Or.inr (Or.inl ⟨h, l2_of_one hZ, l2_grad_of_one hX⟩)
    · exact Or.inr (Or.inr ⟨h, l2_grad_of_one hX, l2_of_one hY⟩)
  have s2 : Summable (leg3 (fun k => ‖X k‖) (fun k => absk k * ‖Y k‖) (fun k => ‖Z k‖)) := by
    refine summable_leg3 (n0 X) (g0 Y) (n0 Z) ?_
    rcases h2 with h | h
    · exact Or.inl ⟨h, l2_grad_of_one hY, l2_of_one hZ⟩
    · exact Or.inr (Or.inr ⟨h, l2_of_one hX, l2_grad_of_one hY⟩)
  exact (s1.add s2).congr fun x => (nearMaj_one X Y Z x).symm

/-- Summability of the `j = 2` majorant for `H²` fields. -/
theorem summable_nearMaj_two {X Y Z : Field} (hX : MZ 2 X) (hY : MZ 2 Y) (hZ : MZ 2 Z) :
    Summable (nearMaj 2 X Y Z) := by
  have g0 : ∀ (W : Field) k, 0 ≤ absk k * ‖W k‖ := fun W k =>
    mul_nonneg (absk_nonneg k) (norm_nonneg _)
  have h0 : ∀ (W : Field) k, 0 ≤ absk k ^ 2 * ‖W k‖ := fun W k =>
    mul_nonneg (pow_nonneg (absk_nonneg k) 2) (norm_nonneg _)
  have n0 : ∀ (W : Field) k, 0 ≤ ‖W k‖ := fun W k => norm_nonneg _
  have hX1 : MZ 1 X := ⟨hX.inH.mono (by norm_num), hX.mean⟩
  have hY1 : MZ 1 Y := ⟨hY.inH.mono (by norm_num), hY.mean⟩
  have s1 := summable_leg3 (g0 X) (n0 Y) (h0 Z)
    (Or.inr (Or.inl ⟨summable_wiener hY.inH, l2_hess_of_two hZ, l2_grad_of_one hX1⟩))
  have s2 := summable_leg3 (n0 X) (g0 Y) (h0 Z)
    (Or.inl ⟨summable_wiener hX.inH, l2_grad_of_one hY1, l2_hess_of_two hZ⟩)
  exact (s1.add s2).congr fun x => (nearMaj_two X Y Z x).symm

/-! ### The pairing as a triad sum -/

private lemma summable_Qm_term_one {m : Mult} (hm : m.Bdd) {X Y : Field} (hX : MZ 1 X)
    (hY : MZ 1 Y) (k : Mode) :
    Summable fun p => ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      m a b c p (k - p) • hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p)))) := by
  have hs1 := (cs_equiv (fun p => norm_nonneg (X p))
    (fun p => mul_nonneg (absk_nonneg p) (norm_nonneg (Y p))) (l2_of_one hX)
    (l2_grad_of_one hY) (Equiv.subLeft k)).1
  have hs2 := (cs_equiv (fun p => mul_nonneg (absk_nonneg p) (norm_nonneg (X p)))
    (fun p => norm_nonneg (Y p)) (l2_grad_of_one hX) (l2_of_one hY) (Equiv.subLeft k)).1
  refine Summable.of_norm_bounded ((hs1.add hs2).mul_left 4) fun p => ?_
  simp only [Equiv.subLeft_apply]
  have hterm : ∀ a b c, ‖m a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))))‖ ≤
        (1 / 2) * (absk (k - p) + absk p) * (‖X p‖ * ‖Y (k - p)‖) := by
    intro a b c
    rw [norm_smul]
    refine (mul_le_mul (hm a b c p (k - p)) (norm_hel_le _ _ _) (norm_nonneg _)
      zero_le_one).trans ?_
    rw [one_mul]
    refine (norm_vert_le₁ _ _ _ _).trans ?_
    have := absk_nonneg (k - p)
    have := absk_nonneg p
    gcongr
    · exact norm_hel_le _ _ _
    · exact norm_hel_le _ _ _
  refine (norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
    norm_sum_le_of_le _ fun c _ => hterm a b c).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

private lemma inner_Qm_one {m : Mult} (hm : m.Bdd) {X Y Z : Field} (hZ : IsReal Z)
    (hX : MZ 1 X) (hY : MZ 1 Y) (k : Mode) :
    inner ℂ (Z k) (Qm m X Y k) = ∑' p, tripT m X Y Z p (k - p) := by
  rw [Qm, inner_tsum _ (summable_Qm_term_one hm hX hY k)]
  refine tsum_congr fun p => ?_
  have hk : p + (k - p) = k := by abel
  simp only [inner_sum, inner_smul_right, tripT, hk, inner_hel_real hZ]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  have := bd_hel_vert c p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))) (Z (-k))
  rw [hk] at this
  rw [this]

/-- A slot pairing of the near differential as a triad sum (real test field `Z`). -/
theorem pair_nearCorr_eq {j : ℕ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) {X Y Z : Field}
    (hZ : IsReal Z) (hX : MZ 1 X) (hY : MZ 1 Y) (hs : Summable (nearTri j ε r τ X Y Z)) :
    pair j Z (nearCorr ε r τ X Y) = (∑' x, nearTri j ε r τ X Y Z x).re :=
  pair_eq_tsum (tripT (nearCorrM ε r τ) X Y Z)
    (inner_Qm_one (nearCorrM_bdd hε r τ) hZ hX hY) hs

theorem isReal_PiF {h : Field} (hh : IsReal h) : IsReal (PiF h) := by
  intro k
  simp only [PiF, Pi.neg_apply, neg_eq_zero]
  split_ifs
  · ext i
    simp [conjV]
  · exact hh k

/-! ### The triad term -/

/-- **The triad term**: the three rootings of the triad `(p, q, −(p+q))` with the direction `G`
on the leg `p` (`G` at the first input / at the second input / at the output). -/
def nearTriadTerm (j : ℕ) (ε r τ : ℝ) (F G : Field) (x : Mode × Mode) : ℂ :=
  nearTri j ε r τ G F F x + nearTri j ε r τ F G F (rho (rho x)) + nearTri j ε r τ F F G (rho x)

private lemma summable_nearTri {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (r τ : ℝ) {F G : Field} (hF : MZ ((j : ℝ) + 1) F) (hG : MZ j G) :
    Summable (nearTri j ε r τ G F F) ∧ Summable (nearTri j ε r τ F G F) ∧
      Summable (nearTri j ε r τ F F G) := by
  have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> norm_num
  have key : ∀ {X Y Z : Field}, Summable (nearMaj j X Y Z) →
      Summable (nearTri j ε r τ X Y Z) := fun h =>
    Summable.of_norm_bounded (h.mul_left 8) (norm_nearTri_le hj1 hε r τ _ _ _)
  rcases hj with rfl | rfl
  · have hF2 : MZ 2 F := by convert hF using 2; norm_num
    have hF1 : MZ 1 F := ⟨hF2.inH.mono (by norm_num), hF2.mean⟩
    have hG1 : MZ 1 G := by simpa using hG
    have hw := summable_wiener hF2.inH
    exact ⟨key (summable_nearMaj_one hG1 hF1 hF1 (Or.inl hw) (Or.inr hw)),
      key (summable_nearMaj_one hF1 hG1 hF1 (Or.inr hw) (Or.inl hw)),
      key (summable_nearMaj_one hF1 hF1 hG1 (Or.inl hw) (Or.inl hw))⟩
  · have hF3 : MZ 3 F := by convert hF using 2; norm_num
    have hF2 : MZ 2 F := ⟨hF3.inH.mono (by norm_num), hF3.mean⟩
    have hG2 : MZ 2 G := by simpa using hG
    exact ⟨key (summable_nearMaj_two hG2 hF2 hF2), key (summable_nearMaj_two hF2 hG2 hF2),
      key (summable_nearMaj_two hF2 hF2 hG2)⟩

/-- **The triad expansion of the near differential**: for real `F ∈ H^{j+1}`, `h ∈ H^j`,
`D_j^N(F; h) = Re Σ_{(p,q)} T(p, q)` with `T = nearTriadTerm` (all three slots collected on the
triads carrying `Π_F h` at the first leg), the series being summable. -/
theorem nearD_eq_tsum_triad {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (r τ : ℝ) {F h : Field} (hF : MZ ((j : ℝ) + 1) F) (hFr : IsReal F) (hh : MZ j h)
    (hhr : IsReal h) :
    Summable (nearTriadTerm j ε r τ F (PiF h)) ∧
      nearD j ε r τ F h = (∑' x, nearTriadTerm j ε r τ F (PiF h) x).re := by
  have hG : MZ j (PiF h) := hh.PiF'
  have hGr := isReal_PiF hhr
  have hj1 : (1 : ℝ) ≤ j := by rcases hj with rfl | rfl <;> norm_num
  have hF1 : MZ 1 F := ⟨hF.inH.mono (by linarith), hF.mean⟩
  have hG1 : MZ 1 (PiF h) := ⟨hG.inH.mono hj1, hG.mean⟩
  obtain ⟨s1, s2, s3⟩ := summable_nearTri hj hε r τ hF hG
  have s2' : Summable fun x => nearTri j ε r τ F (PiF h) F (rho (rho x)) :=
    rho.summable_iff.mpr (rho.summable_iff.mpr s2)
  have s3' : Summable fun x => nearTri j ε r τ F F (PiF h) (rho x) := rho.summable_iff.mpr s3
  refine ⟨(s1.add s2').add s3', ?_⟩
  have e2 : ∑' x, nearTri j ε r τ F (PiF h) F (rho (rho x)) =
      ∑' x, nearTri j ε r τ F (PiF h) F x := by
    rw [rho.tsum_eq (fun y => nearTri j ε r τ F (PiF h) F (rho y)), rho.tsum_eq]
  have e3 : ∑' x, nearTri j ε r τ F F (PiF h) (rho x) = ∑' x, nearTri j ε r τ F F (PiF h) x :=
    rho.tsum_eq _
  unfold nearD
  rw [pair_nearCorr_eq hε r τ hFr hG1 hF1 s1, pair_nearCorr_eq hε r τ hFr hF1 hG1 s2,
    pair_nearCorr_eq hε r τ hGr hF1 hF1 s3]
  unfold nearTriadTerm
  rw [(s1.add s2').tsum_add s3', s1.tsum_add s2', e2, e3, Complex.add_re, Complex.add_re]

end OVNS.Quant

end
