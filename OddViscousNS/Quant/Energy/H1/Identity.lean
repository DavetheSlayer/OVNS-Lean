import OddViscousNS.Quant.Energy.H1.Defs

/-!
# E5 — the AC identity of the corrected `H¹` energy along the actual solution

The E4.4-type identity for `E = ½ a_F² + ½⟨z₁, X₁ z₁⟩ + E⁰` (`h1Energy`, `Defs.lean`), obtained
from the general multilinear correction lemma `trilinear_integral_identity`
(`Kinetic/Derivative.lean`) with the paths `S, F` of `Kinetic/Actual.lean` and the test path
`A F` (`lapF`): the `H¹` pairing is the `L²` pairing against `AF` (`pair_one_eq_pair_zero_lap`).

* **A. Algebra of the triad summand** `tripT`: linearity in each slot and in the multiplier, the
  mode-dependent scalars `(c k) • X k` (`tripT_smul_*`), in particular `A` (`tripT_lapF_*`).
* **B. Majorants with the output-heat gain.**  The corrector and metric multipliers are bounded by
  `1/|k|²` (`norm_corrSym_le`, `norm_metM_le_absSq`), so against the test `AF` the weight `|k|²`
  cancels: `‖tripT m X Y (AW) p q‖ ≤ 8(|p|+|q|)‖X_p‖‖Y_q‖‖W_{−(p+q)}‖` (`norm_tripT_gain_lap`).
* **C. The `ℓ¹ℓ²ℓ²` triple sums with the vertex weight** `|p|+|q|` (`gradTri_*`), including the
  versions with an `ℓ²`-only (derivative) slot, through `|p| ≤ |p+q| + |q|`.
* **D. The bridge** `pair 1 W (Q^♯_m(X,Y)) = Re ∑_{(p,q)} tripT m X Y (AW)`
  (`pair_one_eq_re_tsum`), with the fixed-output summability from the gain.
* **E. The multiplier paths.**  `∂_t corrM(−1, r, rt) = corrDM`, `∂_t metM(r, rt) = metDM'`
  (`hasDerivAt_corrM`, `hasDerivAt_metM`), and the exact heat algebra: for the cubic the
  multiplier derivative and the test heat combine to the nonresonant phase,
  `(irΦ − |k|²) e^{irtΦ}/(−|k|² + irΦ) = e^{irtΦ}` (`tripT_corr_heat_combine`: TeX "the output heat
  cancels the test derivative"); for `X₁` all three heats combine,
  `(irΦ − |p|² − |q|² − |k|²) metSym = e^{irtΦ}` (`tripT_met_heat_combine`).
* **F. Along the actual solution** (TeX, "Its exact derivative is …" and eq. quant-metric):
  `cubicCorr_identity`: `E⁰(t) − E⁰(s) = ∫ (⟨AF, Q_nr(F,F)⟩ − E_heat + DE⁰[fastNL])`;
  `metricCorr_identity`: `⟨z₁,X₁z₁⟩(t) − ⟨z₁,X₁z₁⟩(s) = ∫ 4(⟨AF, Q^♯_{metDM}(S,F)⟩ + ⟨AF, X₁(slowNL)F⟩
  + ⟨AF, X₁(S) fastNL⟩ + ⟨A fastNL, X₁(S)F⟩)`.
* **G. The energy identity** `h1Energy_identity`: with the `H¹` law (`heatPair_fast` at `σ = 1`),
  the split `⟨AF, Q(y,y)⟩ = 2⟨AF, Q(S,F)⟩ + ⟨AF, Q(F,F)⟩ + ⟨AF, H_ψ⟩`, catalytic neutrality
  (`cat_neutral`, `σ = 1`: the resonant slow–fast term vanishes) and `Q_τ = Q_res + Q_nr`:
  `E(t) − E(s) + ∫ b_F² = ∫ h1RHS`, where `h1RHS` keeps exactly the resonant term
  `−⟨AF, Q_res(F,F)⟩` (the `ResH1` slot), the force `−⟨AF, H_ψ⟩`, the three uncancelled `X₁`
  insertions, `−E_heat` and the native differential `DE⁰[fastNL]` (roles 15/9).  The slow–fast term
  and the nonresonant fast–fast term have cancelled exactly.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS

/-! ### A. Algebra of the triad summand -/

lemma tau_add_left (p q : Mode) (A A' B C : V3) :
    tau p q (A + A') B C = tau p q A B C + tau p q A' B C := by
  simp only [tau, dotM_eq, bd, PiLp.add_apply]
  ring

lemma tau_add_mid (p q : Mode) (A B B' C : V3) :
    tau p q A (B + B') C = tau p q A B C + tau p q A B' C := by
  simp only [tau, dotM_eq, bd, PiLp.add_apply]
  ring

lemma tau_add_right (p q : Mode) (A B C C' : V3) :
    tau p q A B (C + C') = tau p q A B C + tau p q A B C' := by
  simp only [tau, dotM_eq, bd, PiLp.add_apply]
  ring

lemma tau_smul_left (p q : Mode) (c : ℂ) (A B C : V3) :
    tau p q (c • A) B C = c * tau p q A B C := by
  simp only [tau, dotM_eq, bd, PiLp.smul_apply, smul_eq_mul]
  ring

lemma tau_smul_mid (p q : Mode) (c : ℂ) (A B C : V3) :
    tau p q A (c • B) C = c * tau p q A B C := by
  simp only [tau, dotM_eq, bd, PiLp.smul_apply, smul_eq_mul]
  ring

lemma tau_smul_right (p q : Mode) (c : ℂ) (A B C : V3) :
    tau p q A B (c • C) = c * tau p q A B C := by
  simp only [tau, dotM_eq, bd, PiLp.smul_apply, smul_eq_mul]
  ring

lemma tripT_add_left (m : Mult) (X X' Y Z : Field) (p q : Mode) :
    tripT m (X + X') Y Z p q = tripT m X Y Z p q + tripT m X' Y Z p q := by
  simp only [tripT, Pi.add_apply, hel_add, tau_add_left, mul_add, Finset.sum_add_distrib]

lemma tripT_add_mid (m : Mult) (X Y Y' Z : Field) (p q : Mode) :
    tripT m X (Y + Y') Z p q = tripT m X Y Z p q + tripT m X Y' Z p q := by
  simp only [tripT, Pi.add_apply, hel_add, tau_add_mid, mul_add, Finset.sum_add_distrib]

lemma tripT_add_right (m : Mult) (X Y Z Z' : Field) (p q : Mode) :
    tripT m X Y (Z + Z') p q = tripT m X Y Z p q + tripT m X Y Z' p q := by
  simp only [tripT, Pi.add_apply, hel_add, tau_add_right, mul_add, Finset.sum_add_distrib]

/-- A mode-dependent scalar in the first slot. -/
lemma tripT_smul_left (m : Mult) (c : Mode → ℂ) (X Y Z : Field) (p q : Mode) :
    tripT m (fun k => c k • X k) Y Z p q = c p * tripT m X Y Z p q := by
  simp only [tripT, hel_smul, tau_smul_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun d _ => ?_
  ring

lemma tripT_smul_mid (m : Mult) (c : Mode → ℂ) (X Y Z : Field) (p q : Mode) :
    tripT m X (fun k => c k • Y k) Z p q = c q * tripT m X Y Z p q := by
  simp only [tripT, hel_smul, tau_smul_mid, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun d _ => ?_
  ring

lemma tripT_smul_right (m : Mult) (c : Mode → ℂ) (X Y Z : Field) (p q : Mode) :
    tripT m X Y (fun k => c k • Z k) p q = c (-(p + q)) * tripT m X Y Z p q := by
  simp only [tripT, hel_smul, tau_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun d _ => ?_
  ring

lemma tripT_neg_left (m : Mult) (X Y Z : Field) (p q : Mode) :
    tripT m (-X) Y Z p q = -tripT m X Y Z p q := by
  have e : (-X : Field) = fun k => ((-1 : ℂ)) • X k := funext fun k => by simp
  rw [e, tripT_smul_left]
  ring

lemma tripT_neg_mid (m : Mult) (X Y Z : Field) (p q : Mode) :
    tripT m X (-Y) Z p q = -tripT m X Y Z p q := by
  have e : (-Y : Field) = fun k => ((-1 : ℂ)) • Y k := funext fun k => by simp
  rw [e, tripT_smul_mid]
  ring

lemma tripT_neg_right (m : Mult) (X Y Z : Field) (p q : Mode) :
    tripT m X Y (-Z) p q = -tripT m X Y Z p q := by
  have e : (-Z : Field) = fun k => ((-1 : ℂ)) • Z k := funext fun k => by simp
  rw [e, tripT_smul_right]
  ring

/-- `A` in the first slot: the factor `|p|²`. -/
lemma tripT_lapF_left (m : Mult) (X Y Z : Field) (p q : Mode) :
    tripT m (lapF X) Y Z p q = (absSq p : ℂ) * tripT m X Y Z p q :=
  tripT_smul_left m (fun k => (absSq k : ℂ)) X Y Z p q

lemma tripT_lapF_mid (m : Mult) (X Y Z : Field) (p q : Mode) :
    tripT m X (lapF Y) Z p q = (absSq q : ℂ) * tripT m X Y Z p q :=
  tripT_smul_mid m (fun k => (absSq k : ℂ)) X Y Z p q

/-- `A` in the test slot: the factor `|p+q|²` (`absSq (−(p+q)) = absSq (p+q)`). -/
lemma tripT_lapF_right (m : Mult) (X Y Z : Field) (p q : Mode) :
    tripT m X Y (lapF Z) p q = (absSq (p + q) : ℂ) * tripT m X Y Z p q := by
  rw [show lapF Z = fun k => (absSq k : ℂ) • Z k from rfl, tripT_smul_right, absSq_neg]

/-- Linearity in the multiplier. -/
lemma tripT_sub_mult (m₁ m₂ : Mult) (X Y Z : Field) (p q : Mode) :
    tripT (fun a b c p q => m₁ a b c p q - m₂ a b c p q) X Y Z p q =
      tripT m₁ X Y Z p q - tripT m₂ X Y Z p q := by
  simp only [tripT, sub_mul, Finset.sum_sub_distrib]

/-- A factor depending on the triad only (not on the helicities) factors out. -/
lemma tripT_mul_mult_fun (f : Mode → Mode → ℂ) (m : Mult) (X Y Z : Field) (p q : Mode) :
    tripT (fun a b c p q => f p q * m a b c p q) X Y Z p q = f p q * tripT m X Y Z p q := by
  simp only [tripT, mul_assoc, Finset.mul_sum]

/-- Two multipliers that agree on the triad give the same summand. -/
lemma tripT_congr {m₁ m₂ : Mult} (X Y Z : Field) {p q : Mode}
    (h : ∀ a b c, m₁ a b c p q = m₂ a b c p q) : tripT m₁ X Y Z p q = tripT m₂ X Y Z p q := by
  simp only [tripT, h]

/-! ### B. Majorants with the output-heat gain -/

/-- `‖tripT m X Y Z p q‖ ≤ 8 κ (|p|+|q|) ‖X_p‖ ‖Y_q‖ ‖Z_{−(p+q)}‖` when `‖m‖ ≤ κ` on the triad
(`norm_tripT_le` with a general bound). -/
lemma norm_tripT_le_of_le {m : Mult} {κ : ℝ} (hκ : 0 ≤ κ) {p q : Mode}
    (hm : ∀ a b c, ‖m a b c p q‖ ≤ κ) (X Y Z : Field) :
    ‖tripT m X Y Z p q‖ ≤ 8 * (κ * ((absk p + absk q) * ‖X p‖ * ‖Y q‖ * ‖Z (-(p + q))‖)) := by
  set E := κ * ((absk p + absk q) * ‖X p‖ * ‖Y q‖ * ‖Z (-(p + q))‖) with hE
  have hterm : ∀ a b c, ‖m a b c p q *
      tau p q (hel a p (X p)) (hel b q (Y q)) (hel c (-(p + q)) (Z (-(p + q))))‖ ≤ E := by
    intro a b c
    have hp := absk_nonneg p
    have hq := absk_nonneg q
    rw [norm_mul]
    refine mul_le_mul (hm a b c) ?_ (norm_nonneg _) hκ
    refine (norm_tau_le _ _ _ _ _).trans ?_
    have h1 := norm_hel_le a p (X p)
    have h2 := norm_hel_le b q (Y q)
    have h3 := norm_hel_le c (-(p + q)) (Z (-(p + q)))
    gcongr
  have hbd : ‖tripT m X Y Z p q‖ ≤ ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, E :=
    norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
      norm_sum_le_of_le _ fun c _ => hterm a b c
  refine hbd.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

/-- The gain against the test `A W`: for `‖m‖ ≤ 1/|p+q|²`,
`‖tripT m X Y (AW) p q‖ ≤ 8 (|p|+|q|) ‖X_p‖ ‖Y_q‖ ‖W_{−(p+q)}‖`. -/
lemma norm_tripT_gain_lap {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    (X Y W : Field) (p q : Mode) :
    ‖tripT m X Y (lapF W) p q‖ ≤ 8 * ((absk p + absk q) * ‖X p‖ * ‖Y q‖ * ‖W (-(p + q))‖) := by
  by_cases hk : p + q = 0
  · rw [tripT_zero_of_add_eq_zero _ _ _ _ hk, norm_zero]
    have := absk_nonneg p
    have := absk_nonneg q
    positivity
  · have hpos : 0 < absSq (p + q) := lt_of_lt_of_le one_pos (one_le_absSq hk)
    have h := norm_tripT_le_of_le (κ := 1 / absSq (p + q)) (by positivity) (fun a b c => hm a b c p q)
      X Y (lapF W)
    have e : ‖lapF W (-(p + q))‖ = absSq (p + q) * ‖W (-(p + q))‖ := by
      simp only [lapF, norm_smul, absSq_neg, Complex.norm_real,
        Real.norm_of_nonneg (absSq_nonneg (p + q))]
    rw [e] at h
    refine h.trans (le_of_eq ?_)
    field_simp

/-- The bounded-multiplier majorant against the test `A W`: `8 (|p|+|q|) ‖X_p‖ ‖Y_q‖ |p+q|² ‖W_{−(p+q)}‖`. -/
lemma norm_tripT_bdd_lap {m : Mult} (hm : m.Bdd) (X Y W : Field) (p q : Mode) :
    ‖tripT m X Y (lapF W) p q‖ ≤
      8 * ((absk p + absk q) * ‖X p‖ * ‖Y q‖ * (absSq (p + q) * ‖W (-(p + q))‖)) := by
  have h := norm_tripT_le hm X Y (lapF W) p q
  have e : ‖lapF W (-(p + q))‖ = absSq (p + q) * ‖W (-(p + q))‖ := by
    simp only [lapF, norm_smul, absSq_neg, Complex.norm_real,
      Real.norm_of_nonneg (absSq_nonneg (p + q))]
  rw [e] at h
  exact h

/-! ### C. Triple sums with the vertex weight -/

/-- `(|p|+|q|) α_p β_q γ_{−(p+q)}`. -/
def gradTri (α β γ : Mode → ℝ) (x : Mode × Mode) : ℝ :=
  (absk x.1 + absk x.2) * α x.1 * β x.2 * γ (-(x.1 + x.2))

lemma gradTri_nonneg {α β γ : Mode → ℝ} (hα : ∀ k, 0 ≤ α k) (hβ : ∀ k, 0 ≤ β k)
    (hγ : ∀ k, 0 ≤ γ k) (x : Mode × Mode) : 0 ≤ gradTri α β γ x := by
  unfold gradTri
  have := absk_nonneg x.1
  have := absk_nonneg x.2
  have := hα x.1
  have := hβ x.2
  have := hγ (-(x.1 + x.2))
  positivity

/-- Both inputs in `ℓ¹ ∩ H¹`, the output in `ℓ²`:
`∑ gradTri ≤ ‖∇α‖₂ ‖β‖₁ ‖γ‖₂ + ‖α‖₁ ‖∇β‖₂ ‖γ‖₂`. -/
lemma gradTri_bound {α β γ : Mode → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hγ0 : ∀ k, 0 ≤ γ k) (hα1 : Summable α) (hαg : Summable fun k => (absk k * α k) ^ 2)
    (hβ1 : Summable β) (hβg : Summable fun k => (absk k * β k) ^ 2)
    (hγ2 : Summable fun k => γ k ^ 2) :
    Summable (gradTri α β γ) ∧ ∑' x, gradTri α β γ x ≤
      Real.sqrt (∑' k, (absk k * α k) ^ 2) * (∑' k, β k) * Real.sqrt (∑' k, γ k ^ 2) +
        (∑' k, α k) * Real.sqrt (∑' k, (absk k * β k) ^ 2) * Real.sqrt (∑' k, γ k ^ 2) := by
  have hαg0 : ∀ k, 0 ≤ absk k * α k := fun k => mul_nonneg (absk_nonneg k) (hα0 k)
  have hβg0 : ∀ k, 0 ≤ absk k * β k := fun k => mul_nonneg (absk_nonneg k) (hβ0 k)
  obtain ⟨s1, b1⟩ := summable_tri_second (a := fun k => absk k * α k) (b := β) (c := γ) hαg0 hβ0
    hγ0 hαg hγ2 hβ1
  obtain ⟨s2, b2⟩ := summable_tri_first (b := α) (a := fun k => absk k * β k) (c := γ) hα0 hβg0
    hγ0 hα1 hβg hγ2
  have e : ∀ x : Mode × Mode, gradTri α β γ x =
      absk x.1 * α x.1 * β x.2 * γ (-(x.1 + x.2)) +
        α x.1 * (absk x.2 * β x.2) * γ (-(x.1 + x.2)) := fun x => by
    unfold gradTri
    ring
  refine ⟨(s1.add s2).congr fun x => (e x).symm, ?_⟩
  rw [tsum_congr e, s1.tsum_add s2]
  have h := add_le_add b1 b2
  calc _ ≤ _ := h
    _ = _ := by ring

/-- The first input only in `ℓ²` (a derivative slot), the second in `ℓ¹ ∩ H¹`, the output in
`ℓ¹ ∩ H¹`: through `|p| ≤ |p+q| + |q|`,
`∑ gradTri ≤ 2 ‖α'‖₂ ‖∇β‖₂ ‖γ‖₁ + ‖α'‖₂ ‖β‖₁ ‖∇γ‖₂`. -/
lemma gradTri_bound_first {α β γ : Mode → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hγ0 : ∀ k, 0 ≤ γ k) (hα2 : Summable fun k => α k ^ 2)
    (hβ1 : Summable β) (hβg : Summable fun k => (absk k * β k) ^ 2)
    (hγ1 : Summable γ) (hγg : Summable fun k => (absk k * γ k) ^ 2) :
    Summable (gradTri α β γ) ∧ ∑' x, gradTri α β γ x ≤
      2 * Real.sqrt (∑' k, α k ^ 2) * Real.sqrt (∑' k, (absk k * β k) ^ 2) * (∑' k, γ k) +
        Real.sqrt (∑' k, α k ^ 2) * (∑' k, β k) * Real.sqrt (∑' k, (absk k * γ k) ^ 2) := by
  have hβg0 : ∀ k, 0 ≤ absk k * β k := fun k => mul_nonneg (absk_nonneg k) (hβ0 k)
  have hγg0 : ∀ k, 0 ≤ absk k * γ k := fun k => mul_nonneg (absk_nonneg k) (hγ0 k)
  obtain ⟨s1, b1⟩ := summable_tri_third (a := α) (c := fun k => absk k * β k) (b := γ) hα0 hγ0
    hβg0 hα2 hβg hγ1
  obtain ⟨s2, b2⟩ := summable_tri_second (a := α) (b := β) (c := fun k => absk k * γ k) hα0 hβ0
    hγg0 hα2 hγg hβ1
  set G : Mode × Mode → ℝ := fun x =>
    2 * (α x.1 * (absk x.2 * β x.2) * γ (-(x.1 + x.2))) +
      α x.1 * β x.2 * (absk (-(x.1 + x.2)) * γ (-(x.1 + x.2))) with hG
  have hGs : Summable G := (s1.mul_left 2).add s2
  have hle : ∀ x, gradTri α β γ x ≤ G x := fun x => by
    have h1 : absk x.1 ≤ absk (-(x.1 + x.2)) + absk x.2 := by
      rw [absk_neg]
      have := absk_sub_le (x.1 + x.2) x.2
      rwa [add_sub_cancel_right] at this
    have := hα0 x.1
    have := hβ0 x.2
    have := hγ0 (-(x.1 + x.2))
    have := absk_nonneg x.2
    have := absk_nonneg (-(x.1 + x.2))
    have hP : 0 ≤ α x.1 * β x.2 * γ (-(x.1 + x.2)) := by positivity
    rw [hG]
    unfold gradTri
    nlinarith [mul_le_mul_of_nonneg_right h1 hP]
  have hs := Summable.of_nonneg_of_le (gradTri_nonneg hα0 hβ0 hγ0) hle hGs
  refine ⟨hs, (hs.tsum_le_tsum hle hGs).trans ?_⟩
  rw [hG, (s1.mul_left 2).tsum_add s2, tsum_mul_left]
  calc 2 * ∑' x : Mode × Mode, α x.1 * (absk x.2 * β x.2) * γ (-(x.1 + x.2)) +
        ∑' x : Mode × Mode, α x.1 * β x.2 * (absk (-(x.1 + x.2)) * γ (-(x.1 + x.2)))
      ≤ 2 * ((∑' k, γ k) * (Real.sqrt (∑' k, α k ^ 2) * Real.sqrt (∑' k, (absk k * β k) ^ 2))) +
        (∑' k, β k) * (Real.sqrt (∑' k, α k ^ 2) * Real.sqrt (∑' k, (absk k * γ k) ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- The second input only in `ℓ²`, the first in `ℓ¹ ∩ H¹`, the output in `ℓ¹ ∩ H¹`:
`∑ gradTri ≤ 2 ‖∇α‖₂ ‖β'‖₂ ‖γ‖₁ + ‖α‖₁ ‖β'‖₂ ‖∇γ‖₂`. -/
lemma gradTri_bound_mid {α β γ : Mode → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hγ0 : ∀ k, 0 ≤ γ k) (hα1 : Summable α) (hαg : Summable fun k => (absk k * α k) ^ 2)
    (hβ2 : Summable fun k => β k ^ 2)
    (hγ1 : Summable γ) (hγg : Summable fun k => (absk k * γ k) ^ 2) :
    Summable (gradTri α β γ) ∧ ∑' x, gradTri α β γ x ≤
      2 * Real.sqrt (∑' k, (absk k * α k) ^ 2) * Real.sqrt (∑' k, β k ^ 2) * (∑' k, γ k) +
        (∑' k, α k) * Real.sqrt (∑' k, β k ^ 2) * Real.sqrt (∑' k, (absk k * γ k) ^ 2) := by
  have hαg0 : ∀ k, 0 ≤ absk k * α k := fun k => mul_nonneg (absk_nonneg k) (hα0 k)
  have hγg0 : ∀ k, 0 ≤ absk k * γ k := fun k => mul_nonneg (absk_nonneg k) (hγ0 k)
  obtain ⟨s1, b1⟩ := summable_tri_third (a := fun k => absk k * α k) (c := β) (b := γ) hαg0 hγ0
    hβ0 hαg hβ2 hγ1
  obtain ⟨s2, b2⟩ := summable_tri_first (b := α) (a := β) (c := fun k => absk k * γ k) hα0 hβ0
    hγg0 hα1 hβ2 hγg
  set G : Mode × Mode → ℝ := fun x =>
    2 * ((absk x.1 * α x.1) * β x.2 * γ (-(x.1 + x.2))) +
      α x.1 * β x.2 * (absk (-(x.1 + x.2)) * γ (-(x.1 + x.2))) with hG
  have hGs : Summable G := (s1.mul_left 2).add s2
  have hle : ∀ x, gradTri α β γ x ≤ G x := fun x => by
    have h1 : absk x.2 ≤ absk (-(x.1 + x.2)) + absk x.1 := by
      rw [absk_neg]
      have := absk_sub_le (x.1 + x.2) x.1
      rwa [add_sub_cancel_left] at this
    have := hα0 x.1
    have := hβ0 x.2
    have := hγ0 (-(x.1 + x.2))
    have := absk_nonneg x.1
    have := absk_nonneg (-(x.1 + x.2))
    have hP : 0 ≤ α x.1 * β x.2 * γ (-(x.1 + x.2)) := by positivity
    rw [hG]
    unfold gradTri
    nlinarith [mul_le_mul_of_nonneg_right h1 hP]
  have hs := Summable.of_nonneg_of_le (gradTri_nonneg hα0 hβ0 hγ0) hle hGs
  refine ⟨hs, (hs.tsum_le_tsum hle hGs).trans ?_⟩
  rw [hG, (s1.mul_left 2).tsum_add s2, tsum_mul_left]
  calc 2 * ∑' x : Mode × Mode, absk x.1 * α x.1 * β x.2 * γ (-(x.1 + x.2)) +
        ∑' x : Mode × Mode, α x.1 * β x.2 * (absk (-(x.1 + x.2)) * γ (-(x.1 + x.2)))
      ≤ 2 * ((∑' k, γ k) * (Real.sqrt (∑' k, (absk k * α k) ^ 2) * Real.sqrt (∑' k, β k ^ 2))) +
        (∑' k, α k) * (Real.sqrt (∑' k, β k ^ 2) * Real.sqrt (∑' k, (absk k * γ k) ^ 2)) := by
        gcongr
    _ = _ := by ring

/-! ### D. The bridge `pair 1 W (Q^♯_m(X,Y)) = Re ∑ tripT m X Y (AW)` -/

/-- Fixed-output summability of the vertex-weighted product `(|p|+|k−p|)‖X_p‖‖Y_{k−p}‖` when both
factors are `ℓ²` and one of them has an `ℓ²` gradient (`|p| ≤ |k| + |k−p|`). -/
lemma summable_vertex_fixed {X Y : Field} (k : Mode) (hX2 : Summable fun p => ‖X p‖ ^ 2)
    (hY2 : Summable fun p => ‖Y p‖ ^ 2)
    (hg : (Summable fun p => (absk p * ‖X p‖) ^ 2) ∨ Summable fun p => (absk p * ‖Y p‖) ^ 2) :
    Summable fun p => (absk p + absk (k - p)) * ‖X p‖ * ‖Y (k - p)‖ := by
  have hY2' : Summable fun p => ‖Y (k - p)‖ ^ 2 := (Equiv.subLeft k).summable_iff.mpr hY2
  have hXY : Summable fun p => ‖X p‖ * ‖Y (k - p)‖ :=
    Summable.of_nonneg_of_le (fun p => by positivity)
      (fun p => by nlinarith [sq_nonneg (‖X p‖ - ‖Y (k - p)‖)]) ((hX2.add hY2').mul_left (1 / 2))
  rcases hg with hXg | hYg
  · -- `|k−p| ≤ |k| + |p|`: bound by `(|k| + 2|p|)‖X_p‖‖Y_{k−p}‖`
    have hgY : Summable fun p => absk p * ‖X p‖ * ‖Y (k - p)‖ :=
      Summable.of_nonneg_of_le
        (fun p => mul_nonneg (mul_nonneg (absk_nonneg p) (norm_nonneg _)) (norm_nonneg _))
        (fun p => by nlinarith [sq_nonneg (absk p * ‖X p‖ - ‖Y (k - p)‖)])
        ((hXg.add hY2').mul_left (1 / 2))
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg (mul_nonneg
      (add_nonneg (absk_nonneg p) (absk_nonneg (k - p))) (norm_nonneg _)) (norm_nonneg _))
      (fun p => ?_) ((hXY.mul_left (absk k)).add (hgY.mul_left 2))
    have h1 : absk (k - p) ≤ absk k + absk p := absk_sub_le k p
    have := absk_nonneg p
    have := norm_nonneg (X p)
    have := norm_nonneg (Y (k - p))
    nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg (norm_nonneg (X p)) (norm_nonneg (Y (k - p))))]
  · -- `|p| ≤ |k| + |k−p|`
    have hYg' : Summable fun p => (absk (k - p) * ‖Y (k - p)‖) ^ 2 :=
      (Equiv.subLeft k).summable_iff.mpr hYg
    have hgY : Summable fun p => ‖X p‖ * (absk (k - p) * ‖Y (k - p)‖) :=
      Summable.of_nonneg_of_le
        (fun p => mul_nonneg (norm_nonneg _) (mul_nonneg (absk_nonneg _) (norm_nonneg _)))
        (fun p => by nlinarith [sq_nonneg (‖X p‖ - absk (k - p) * ‖Y (k - p)‖)])
        ((hX2.add hYg').mul_left (1 / 2))
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg (mul_nonneg
      (add_nonneg (absk_nonneg p) (absk_nonneg (k - p))) (norm_nonneg _)) (norm_nonneg _))
      (fun p => ?_) ((hXY.mul_left (absk k)).add (hgY.mul_left 2))
    have h1 : absk p ≤ absk k + absk (k - p) := by
      have := absk_sub_le k (k - p)
      rwa [sub_sub_cancel] at this
    have := absk_nonneg (k - p)
    have := norm_nonneg (X p)
    have := norm_nonneg (Y (k - p))
    nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg (norm_nonneg (X p)) (norm_nonneg (Y (k - p))))]

/-- The summand of `Q^♯_m(X,Y)_k` at `p` is bounded by `4 κ (|p|+|k−p|) ‖X_p‖ ‖Y_{k−p}‖` when
`‖m‖ ≤ κ` on the triad. -/
lemma norm_Qm_summand_le {m : Mult} {κ : ℝ} (hκ : 0 ≤ κ) {X Y : Field} {k p : Mode}
    (hm : ∀ a b c, ‖m a b c p (k - p)‖ ≤ κ) :
    ‖∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p (k - p) •
        hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))))‖ ≤
      8 * (κ * ((absk p + absk (k - p)) * ‖X p‖ * ‖Y (k - p)‖)) := by
  set E := κ * ((absk p + absk (k - p)) * ‖X p‖ * ‖Y (k - p)‖) with hE
  have hterm : ∀ a b c, ‖m a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))))‖ ≤ E := by
    intro a b c
    rw [norm_smul]
    refine mul_le_mul (hm a b c) ?_ (norm_nonneg _) hκ
    refine (norm_hel_le _ _ _).trans ((norm_vert_le₁ _ _ _ _).trans ?_)
    have h1 := norm_hel_le a p (X p)
    have h2 := norm_hel_le b (k - p) (Y (k - p))
    have hA : 0 ≤ absk (k - p) + absk p := add_nonneg (absk_nonneg _) (absk_nonneg _)
    have h3 : ‖hel a p (X p)‖ * ‖hel b (k - p) (Y (k - p))‖ ≤ ‖X p‖ * ‖Y (k - p)‖ :=
      mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
    have h5 : 0 ≤ (absk (k - p) + absk p) * (‖X p‖ * ‖Y (k - p)‖) :=
      mul_nonneg hA (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    calc 1 / 2 * (absk (k - p) + absk p) * (‖hel a p (X p)‖ * ‖hel b (k - p) (Y (k - p))‖)
        ≤ 1 / 2 * (absk (k - p) + absk p) * (‖X p‖ * ‖Y (k - p)‖) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ ≤ (absk (k - p) + absk p) * (‖X p‖ * ‖Y (k - p)‖) := by linarith
      _ = (absk p + absk (k - p)) * ‖X p‖ * ‖Y (k - p)‖ := by ring
  have hbd : ‖∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))))‖ ≤
      ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, E :=
    norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
      norm_sum_le_of_le _ fun c _ => hterm a b c
  refine hbd.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

/-- The `p`-sum of `Q^♯_m(X,Y)_k` converges for a multiplier with the gain `‖m‖ ≤ 1/|k|²`, given
the fixed-output summability of the vertex-weighted product. -/
lemma summable_Qm_term_gain {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    {X Y : Field} (k : Mode)
    (hXY : Summable fun p => (absk p + absk (k - p)) * ‖X p‖ * ‖Y (k - p)‖) :
    Summable fun p => ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p)))) := by
  refine Summable.of_norm_bounded (hXY.mul_left (8 * (1 / absSq k))) fun p => ?_
  have hk : p + (k - p) = k := by abel
  have h := norm_Qm_summand_le (κ := 1 / absSq k) (div_nonneg zero_le_one (absSq_nonneg k))
    (X := X) (Y := Y) (k := k) (p := p) (fun a b c => by
      have := hm a b c p (k - p)
      rwa [hk] at this)
  refine h.trans (le_of_eq ?_)
  ring

/-- `⟨Z_k, Q^♯_m(X,Y)_k⟩ = ∑_p tripT m X Y Z p (k−p)` for a real test field, given the
convergence of the `p`-sum (`inner_Qm` without the `H²` hypotheses on the inputs). -/
lemma inner_Qm_of_summable {m : Mult} {X Y Z : Field} (hZ : IsReal Z) (k : Mode)
    (hs : Summable fun p => ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))))) :
    inner ℂ (Z k) (Qm m X Y k) = ∑' p, tripT m X Y Z p (k - p) := by
  rw [Qm, inner_tsum _ hs]
  refine tsum_congr fun p => ?_
  have hk : p + (k - p) = k := by abel
  simp only [inner_sum, inner_smul_right, tripT, hk, inner_hel_real hZ]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  have := bd_hel_vert c p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))) (Z (-k))
  rw [hk] at this
  rw [this]

/-- **The bridge**: `pair 1 W (Q^♯_m(X,Y)) = Re ∑_{(p,q)} tripT m X Y (AW) p q` for a real `W`,
from the fixed-output identity and the summability of the triad family. -/
lemma pair_one_eq_re_tsum {m : Mult} {X Y W : Field} (hW : IsReal W)
    (hin : ∀ k, inner ℂ (lapF W k) (Qm m X Y k) = ∑' p, tripT m X Y (lapF W) p (k - p))
    (hs : Summable fun x : Mode × Mode => tripT m X Y (lapF W) x.1 x.2) :
    pair 1 W (Qm m X Y) = (∑' x : Mode × Mode, tripT m X Y (lapF W) x.1 x.2).re := by
  have _ := hW
  rw [pair_one_eq_pair_zero_lap]
  have hT : Summable fun x : Mode × Mode =>
      (sobWeight 0 (x.1 + x.2) : ℂ) * tripT m X Y (lapF W) x.1 x.2 :=
    hs.congr fun x => (weight_zero_mul (tripT_zero_of_add_eq_zero _ _ _ _)).symm
  have e := pair_eq_tsum (tripT m X Y (lapF W)) hin hT
  rw [tsum_weight_tripT] at e
  exact e

/-- The bridge for a gain multiplier, inputs `X ∈ ℓ²`, `Y ∈ ℓ² ∩ H¹` (or the symmetric case) and
a real `W ∈ H²`, with the summability of the triad family as the only remaining hypothesis. -/
lemma pair_one_eq_re_tsum_gain {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    {X Y W : Field} (hW : IsReal W) (hX2 : Summable fun p => ‖X p‖ ^ 2)
    (hY2 : Summable fun p => ‖Y p‖ ^ 2)
    (hg : (Summable fun p => (absk p * ‖X p‖) ^ 2) ∨ Summable fun p => (absk p * ‖Y p‖) ^ 2)
    (hs : Summable fun x : Mode × Mode => tripT m X Y (lapF W) x.1 x.2) :
    pair 1 W (Qm m X Y) = (∑' x : Mode × Mode, tripT m X Y (lapF W) x.1 x.2).re :=
  pair_one_eq_re_tsum hW (fun k => inner_Qm_of_summable hW.lapF k
    (summable_Qm_term_gain hm k (summable_vertex_fixed k hX2 hY2 hg))) hs

/-! ### E. The multiplier paths and the heat algebra -/

/-- `∂_t [e^{irtΦ} C] = irΦ e^{irtΦ} C`. -/
lemma hasDerivAt_phaseM_mul (r Φ : ℝ) (C : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * ((r * u) * Φ : ℝ)) * C)
      (Complex.I * (r * Φ : ℝ) * (Complex.exp (Complex.I * ((r * t) * Φ : ℝ)) * C)) t := by
  have h1 : HasDerivAt (fun u : ℝ => Complex.I * (((r * u) * Φ : ℝ) : ℂ))
      (Complex.I * (r * Φ : ℝ)) t := by
    have h0 := (((hasDerivAt_id t).const_mul r).mul_const Φ).ofReal_comp
    simpa [mul_comm, mul_assoc, mul_left_comm] using h0.const_mul Complex.I
  have h2 := (h1.cexp).mul_const C
  refine h2.congr_deriv ?_
  ring

open Classical in
/-- The derivative multiplier of the corrector path: `𝟏_{NonRes} irΦ e^{iτΦ}/(ε|k|² + irΦ)`. -/
def corrDM (ε r τ : ℝ) : Mult := fun a b c p q =>
  if Quant.NonRes a b c p q then
    (Complex.I * (r * Phi a b c p q : ℝ)) * Quant.corrSym ε r τ a b c p q else 0

open Classical in
/-- The derivative multiplier of the `X₁` path: `𝟏_{SlowFast} irΦ metSym`. -/
def metDM' (r τ : ℝ) : Mult := fun a b c p q =>
  if SlowFast a b c p q then (Complex.I * (r * Phi a b c p q : ℝ)) * metSym r τ a b c p q else 0

theorem hasDerivAt_corrM (ε r : ℝ) (a b c : Sgn) (p q : Mode) (t : ℝ) :
    HasDerivAt (fun u => Quant.corrM ε r (r * u) a b c p q) (corrDM ε r (r * t) a b c p q) t := by
  by_cases h : Quant.NonRes a b c p q
  · have e : (fun u => Quant.corrM ε r (r * u) a b c p q) = fun u =>
        Complex.exp (Complex.I * ((r * u) * Phi a b c p q : ℝ)) *
          Quant.resolv ε (absSq (p + q)) (r * Phi a b c p q) :=
      funext fun u => by simp only [Quant.corrM, ite_eq_left h, Quant.corrSym, phaseM]
    have e2 : corrDM ε r (r * t) a b c p q = Complex.I * (r * Phi a b c p q : ℝ) *
        (Complex.exp (Complex.I * ((r * t) * Phi a b c p q : ℝ)) *
          Quant.resolv ε (absSq (p + q)) (r * Phi a b c p q)) := by
      simp only [corrDM, ite_eq_left h, Quant.corrSym, phaseM]
    rw [e, e2]
    exact hasDerivAt_phaseM_mul r _ _ t
  · have e : (fun u => Quant.corrM ε r (r * u) a b c p q) = fun _ => 0 :=
      funext fun u => by simp only [Quant.corrM, ite_eq_right h]
    have e2 : corrDM ε r (r * t) a b c p q = 0 := by simp only [corrDM, ite_eq_right h]
    rw [e, e2]
    exact hasDerivAt_const _ _

theorem hasDerivAt_metM (r : ℝ) (a b c : Sgn) (p q : Mode) (t : ℝ) :
    HasDerivAt (fun u => metM r (r * u) a b c p q) (metDM' r (r * t) a b c p q) t := by
  by_cases h : SlowFast a b c p q
  · have e : (fun u => metM r (r * u) a b c p q) = fun u =>
        Complex.exp (Complex.I * ((r * u) * Phi a b c p q : ℝ)) *
          Quant.resolv (-1) (triHeat p q) (r * Phi a b c p q) :=
      funext fun u => by simp only [metM, ite_eq_left h, metSym, phaseM]
    have e2 : metDM' r (r * t) a b c p q = Complex.I * (r * Phi a b c p q : ℝ) *
        (Complex.exp (Complex.I * ((r * t) * Phi a b c p q : ℝ)) *
          Quant.resolv (-1) (triHeat p q) (r * Phi a b c p q)) := by
      simp only [metDM', ite_eq_left h, metSym, phaseM]
    rw [e, e2]
    exact hasDerivAt_phaseM_mul r _ _ t
  · have e : (fun u => metM r (r * u) a b c p q) = fun _ => 0 :=
      funext fun u => by simp only [metM, ite_eq_right h]
    have e2 : metDM' r (r * t) a b c p q = 0 := by simp only [metDM', ite_eq_right h]
    rw [e, e2]
    exact hasDerivAt_const _ _

lemma continuous_corrDM (ε r : ℝ) (a b c : Sgn) (p q : Mode) :
    Continuous fun t : ℝ => corrDM ε r (r * t) a b c p q := by
  by_cases h : Quant.NonRes a b c p q
  · simp only [corrDM, ite_eq_left h, Quant.corrSym, phaseM]
    refine continuous_const.mul (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).mul continuous_const)))
  · simp only [corrDM, ite_eq_right h]
    exact continuous_const

lemma continuous_metDM' (r : ℝ) (a b c : Sgn) (p q : Mode) :
    Continuous fun t : ℝ => metDM' r (r * t) a b c p q := by
  by_cases h : SlowFast a b c p q
  · simp only [metDM', ite_eq_left h, metSym, phaseM]
    refine continuous_const.mul (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).mul continuous_const)))
  · simp only [metDM', ite_eq_right h]
    exact continuous_const

/-- `|z| ≤ √(s² + z²)`. -/
private lemma abs_le_sqrt_sq_add (s z : ℝ) : |z| ≤ Real.sqrt (s ^ 2 + z ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])

/-- `|irΦ e^{iτΦ}/(ε|k|² + irΦ)| = |rΦ|/√(|k|⁴ + r²Φ²) ≤ 1`. -/
lemma corrDM_bdd {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) : (corrDM ε r τ).Bdd := by
  intro a b c p q
  unfold corrDM
  split_ifs with h
  · rw [norm_mul, Quant.norm_corrSym hε, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have hpos : 0 < Real.sqrt (absSq (p + q) ^ 2 + (r * Phi a b c p q) ^ 2) := by
      have := one_le_absSq h.1
      positivity
    rw [mul_one_div, div_le_one hpos]
    exact abs_le_sqrt_sq_add _ _
  · simp

/-- `|irΦ metSym| = |rΦ|/√(Σ² + r²Φ²) ≤ 1`. -/
lemma metDM'_bdd (r τ : ℝ) : (metDM' r τ).Bdd := by
  intro a b c p q
  unfold metDM'
  split_ifs with h
  · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      metSym, norm_mul]
    have h1 : ‖phaseM τ a b c p q‖ = 1 := by
      rw [phaseM, mul_comm, Complex.norm_exp_ofReal_mul_I]
    rw [h1, one_mul, Quant.norm_resolv_sgn (Or.inr rfl)]
    have hpos : 0 < Real.sqrt (triHeat p q ^ 2 + (r * Phi a b c p q) ^ 2) := by
      have := one_le_triHeat h.ne_zero
      positivity
    rw [mul_one_div, div_le_one hpos]
    exact abs_le_sqrt_sq_add _ _
  · simp

/-- The exact heat algebra of the corrector: `(irΦ − |k|²) e^{iτΦ}/(−|k|² + irΦ) = e^{iτΦ}` on
the nonresonant triads with `k ≠ 0`, and `0 = 0` on the resonant ones. -/
lemma corrDM_sub_heat (r τ : ℝ) (a b c : Sgn) {p q : Mode} (hk : p + q ≠ 0) :
    corrDM (-1) r τ a b c p q - (absSq (p + q) : ℂ) * Quant.corrM (-1) r τ a b c p q =
      nonresM τ a b c p q := by
  unfold corrDM Quant.corrM nonresM
  by_cases hΦ : Phi a b c p q = 0
  · have h : ¬ Quant.NonRes a b c p q := fun h' => h'.2 hΦ
    simp only [ite_eq_right h, ite_eq_left hΦ, mul_zero, sub_zero]
  · have h : Quant.NonRes a b c p q := ⟨hk, hΦ⟩
    simp only [ite_eq_left h, ite_eq_right hΦ, Quant.corrSym, Quant.resolv]
    have hD := Quant.resolv_den_ne_zero (Or.inr rfl) (K2 := absSq (p + q))
      (by linarith [one_le_absSq hk]) (r * Phi a b c p q)
    have eD : Complex.I * ((r * Phi a b c p q : ℝ) : ℂ) - (absSq (p + q) : ℂ) =
        ((-1 * absSq (p + q) : ℝ) : ℂ) + ((r * Phi a b c p q : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    calc _ = phaseM τ a b c p q * ((Complex.I * ((r * Phi a b c p q : ℝ) : ℂ) -
          (absSq (p + q) : ℂ)) * (1 / (((-1 * absSq (p + q) : ℝ) : ℂ) +
          ((r * Phi a b c p q : ℝ) : ℂ) * Complex.I))) := by ring
      _ = phaseM τ a b c p q := by rw [eD, mul_one_div_cancel hD, mul_one]

/-- The exact heat algebra of `X₁`: `(irΦ − |p|² − |q|² − |p+q|²) metSym = e^{iτΦ}` on the
slow–fast triads. -/
lemma metDM'_sub_heat (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    metDM' r τ a b c p q - (triHeat p q : ℂ) * metM r τ a b c p q = metDM τ a b c p q := by
  unfold metDM' metM metDM
  by_cases h : SlowFast a b c p q
  · simp only [ite_eq_left h, metSym, Quant.resolv]
    have hD := Quant.resolv_den_ne_zero (Or.inr rfl) (K2 := triHeat p q)
      (by linarith [one_le_triHeat h.ne_zero]) (r * Phi a b c p q)
    have eD : Complex.I * ((r * Phi a b c p q : ℝ) : ℂ) - (triHeat p q : ℂ) =
        ((-1 * triHeat p q : ℝ) : ℂ) + ((r * Phi a b c p q : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    calc _ = phaseM τ a b c p q * ((Complex.I * ((r * Phi a b c p q : ℝ) : ℂ) -
          (triHeat p q : ℂ)) * (1 / (((-1 * triHeat p q : ℝ) : ℂ) +
          ((r * Phi a b c p q : ℝ) : ℂ) * Complex.I))) := by ring
      _ = phaseM τ a b c p q := by rw [eD, mul_one_div_cancel hD, mul_one]
  · simp only [ite_eq_right h, mul_zero, sub_zero]

/-- **The cubic heat combination** (TeX: "the output heat cancels the test derivative"): the
multiplier-derivative slot and the test-heat slot combine to the nonresonant phase. -/
lemma tripT_corr_heat_combine (r τ : ℝ) (X Y W : Field) (p q : Mode) :
    tripT (corrDM (-1) r τ) X Y (lapF W) p q +
        tripT (Quant.corrM (-1) r τ) X Y (-lapF (lapF W)) p q =
      tripT (nonresM τ) X Y (lapF W) p q := by
  by_cases hk : p + q = 0
  · simp only [tripT_zero_of_add_eq_zero _ _ _ _ hk, add_zero]
  · have hc := tripT_congr (m₁ := fun a b c p q => corrDM (-1) r τ a b c p q -
      (absSq (p + q) : ℂ) * Quant.corrM (-1) r τ a b c p q) (m₂ := nonresM τ) X Y (lapF W)
      (fun a b c => corrDM_sub_heat r τ a b c hk)
    rw [tripT_neg_right, tripT_lapF_right _ _ _ (lapF W), ← hc, tripT_sub_mult,
      tripT_mul_mult_fun (f := fun p q => (absSq (p + q) : ℂ))]
    ring

/-- **The metric heat combination**: the multiplier derivative and the three heats combine to the
slow–fast nonresonant phase `metDM`. -/
lemma tripT_met_heat_combine (r τ : ℝ) (X Y W : Field) (p q : Mode) :
    tripT (metDM' r τ) X Y (lapF W) p q + tripT (metM r τ) (-lapF X) Y (lapF W) p q +
        tripT (metM r τ) X (-lapF Y) (lapF W) p q +
        tripT (metM r τ) X Y (-lapF (lapF W)) p q =
      tripT (metDM τ) X Y (lapF W) p q := by
  have hc := tripT_congr (m₁ := fun a b c p q => metDM' r τ a b c p q -
    (triHeat p q : ℂ) * metM r τ a b c p q) (m₂ := metDM τ) X Y (lapF W)
    (fun a b c => metDM'_sub_heat r τ a b c p q)
  rw [tripT_neg_left, tripT_lapF_left, tripT_neg_mid, tripT_lapF_mid, tripT_neg_right,
    tripT_lapF_right _ _ _ (lapF W), ← hc, tripT_sub_mult,
    tripT_mul_mult_fun (f := fun p q => (triHeat p q : ℂ))]
  push_cast [triHeat]
  ring

/-! ### F. Along the actual solution -/

/-- `(|k|² ‖Z_k‖)` is `ℓ²` for `Z ∈ H²`. -/
lemma summable_hess {Z : Field} (hZ : InH 2 Z) : Summable fun k => (absSq k * ‖Z k‖) ^ 2 :=
  (lapF_l2 hZ).1.congr fun k => by
    simp only [lapF, norm_smul, Complex.norm_real, Real.norm_of_nonneg (absSq_nonneg k)]

/-- `√∑ (|k|² ‖Z_k‖)² = ‖Z‖₂`. -/
lemma sqrt_tsum_hess_sq {Z : Field} (hZ : InH 2 Z) :
    Real.sqrt (∑' k, (absSq k * ‖Z k‖) ^ 2) = hnorm 2 Z := by
  rw [← (lapF_l2 hZ).2]
  congr 1
  exact tsum_congr fun k => by
    simp only [lapF, norm_smul, Complex.norm_real, Real.norm_of_nonneg (absSq_nonneg k)]

private lemma conjV_neg' (v : V3) : conjV (-v) = -conjV v := by
  ext i
  simp [conjV]

lemma IsReal.neg' {W : Field} (h : IsReal W) : IsReal (-W) := fun k => by
  simp only [Pi.neg_apply, h k, conjV_neg']

/-- The derivative family of `pair 1 W (Q^♯_m(X,Y))` is dominated by four vertex-weighted triple
products (the `m'` slot with the full weight `|k|²`, the three others with the gain). -/
lemma norm_tripD_gain_le {m m' : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    (hm' : m'.Bdd) (X X' Y Y' W W' : Field) (x : Mode × Mode) :
    ‖tripD m m' X X' Y Y' (lapF W) (lapF W') x.1 x.2‖ ≤
      8 * (gradTri (fun k => ‖X k‖) (fun k => ‖Y k‖) (fun k => absSq k * ‖W k‖) x +
        gradTri (fun k => ‖X' k‖) (fun k => ‖Y k‖) (fun k => ‖W k‖) x +
        gradTri (fun k => ‖X k‖) (fun k => ‖Y' k‖) (fun k => ‖W k‖) x +
        gradTri (fun k => ‖X k‖) (fun k => ‖Y k‖) (fun k => ‖W' k‖) x) := by
  have h1 := norm_tripT_bdd_lap hm' X Y W x.1 x.2
  have h2 := norm_tripT_gain_lap hm X' Y W x.1 x.2
  have h3 := norm_tripT_gain_lap hm X Y' W x.1 x.2
  have h4 := norm_tripT_gain_lap hm X Y W' x.1 x.2
  have h5 : ‖tripD m m' X X' Y Y' (lapF W) (lapF W') x.1 x.2‖ ≤
      ‖tripT m' X Y (lapF W) x.1 x.2‖ + ‖tripT m X' Y (lapF W) x.1 x.2‖ +
        ‖tripT m X Y' (lapF W) x.1 x.2‖ + ‖tripT m X Y (lapF W') x.1 x.2‖ :=
    (norm_add_le _ _).trans (add_le_add norm_add₃_le le_rfl)
  simp only [gradTri, absSq_neg]
  linarith

/-- **The summability control** for the derivative family of `pair 1 W (Q^♯_m(X,Y))` at a fixed
time: `X, Y, W ∈ ℓ¹ ∩ H¹` (`W ∈ H²`), the derivative slots `X', Y', W' ∈ ℓ²`. -/
lemma tripD_gain_summable {m m' : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    (hm' : m'.Bdd) {X X' Y Y' W W' : Field}
    (hX1 : Summable fun k => ‖X k‖) (hXg : Summable fun k => (absk k * ‖X k‖) ^ 2)
    (hY1 : Summable fun k => ‖Y k‖) (hYg : Summable fun k => (absk k * ‖Y k‖) ^ 2)
    (hW1 : Summable fun k => ‖W k‖) (hWg : Summable fun k => (absk k * ‖W k‖) ^ 2)
    (hWh : Summable fun k => (absSq k * ‖W k‖) ^ 2)
    (hX'2 : Summable fun k => ‖X' k‖ ^ 2) (hY'2 : Summable fun k => ‖Y' k‖ ^ 2)
    (hW'2 : Summable fun k => ‖W' k‖ ^ 2) :
    (Summable fun x : Mode × Mode => ‖tripD m m' X X' Y Y' (lapF W) (lapF W') x.1 x.2‖) ∧
      ∑' x : Mode × Mode, ‖tripD m m' X X' Y Y' (lapF W) (lapF W') x.1 x.2‖ ≤
        8 * ((Real.sqrt (∑' k, (absk k * ‖X k‖) ^ 2) * (∑' k, ‖Y k‖) *
            Real.sqrt (∑' k, (absSq k * ‖W k‖) ^ 2) +
          (∑' k, ‖X k‖) * Real.sqrt (∑' k, (absk k * ‖Y k‖) ^ 2) *
            Real.sqrt (∑' k, (absSq k * ‖W k‖) ^ 2)) +
        (2 * Real.sqrt (∑' k, ‖X' k‖ ^ 2) * Real.sqrt (∑' k, (absk k * ‖Y k‖) ^ 2) *
            (∑' k, ‖W k‖) +
          Real.sqrt (∑' k, ‖X' k‖ ^ 2) * (∑' k, ‖Y k‖) * Real.sqrt (∑' k, (absk k * ‖W k‖) ^ 2)) +
        (2 * Real.sqrt (∑' k, (absk k * ‖X k‖) ^ 2) * Real.sqrt (∑' k, ‖Y' k‖ ^ 2) *
            (∑' k, ‖W k‖) +
          (∑' k, ‖X k‖) * Real.sqrt (∑' k, ‖Y' k‖ ^ 2) * Real.sqrt (∑' k, (absk k * ‖W k‖) ^ 2)) +
        (Real.sqrt (∑' k, (absk k * ‖X k‖) ^ 2) * (∑' k, ‖Y k‖) * Real.sqrt (∑' k, ‖W' k‖ ^ 2) +
          (∑' k, ‖X k‖) * Real.sqrt (∑' k, (absk k * ‖Y k‖) ^ 2) *
            Real.sqrt (∑' k, ‖W' k‖ ^ 2))) := by
  have hn : ∀ (V : Field) (k : Mode), 0 ≤ ‖V k‖ := fun V k => norm_nonneg _
  have hh : ∀ k, 0 ≤ absSq k * ‖W k‖ := fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _)
  obtain ⟨s1, b1⟩ := gradTri_bound (hn X) (hn Y) hh hX1 hXg hY1 hYg hWh
  obtain ⟨s2, b2⟩ := gradTri_bound_first (hn X') (hn Y) (hn W) hX'2 hY1 hYg hW1 hWg
  obtain ⟨s3, b3⟩ := gradTri_bound_mid (hn X) (hn Y') (hn W) hX1 hXg hY'2 hW1 hWg
  obtain ⟨s4, b4⟩ := gradTri_bound (hn X) (hn Y) (hn W') hX1 hXg hY1 hYg hW'2
  have hG : Summable fun x : Mode × Mode =>
      8 * (gradTri (fun k => ‖X k‖) (fun k => ‖Y k‖) (fun k => absSq k * ‖W k‖) x +
        gradTri (fun k => ‖X' k‖) (fun k => ‖Y k‖) (fun k => ‖W k‖) x +
        gradTri (fun k => ‖X k‖) (fun k => ‖Y' k‖) (fun k => ‖W k‖) x +
        gradTri (fun k => ‖X k‖) (fun k => ‖Y k‖) (fun k => ‖W' k‖) x) :=
    (((s1.add s2).add s3).add s4).mul_left 8
  have hpt := norm_tripD_gain_le hm hm' X X' Y Y' W W'
  have hS := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hG
  refine ⟨hS, (hS.tsum_le_tsum hpt hG).trans ?_⟩
  rw [tsum_mul_left, ((s1.add s2).add s3).tsum_add s4, (s1.add s2).tsum_add s3, s1.tsum_add s2]
  have := add_le_add (add_le_add (add_le_add b1 b2) b3) b4
  linarith

namespace Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- The summability data of an `H²` field. -/
lemma adm_summables {Z : Field} (hZ : Adm 2 Z) :
    (Summable fun k => ‖Z k‖) ∧ (Summable fun k => ‖Z k‖ ^ 2) ∧
      (Summable fun k => (absk k * ‖Z k‖) ^ 2) ∧ Summable fun k => (absSq k * ‖Z k‖) ^ 2 :=
  ⟨summable_wiener hZ.inH, summable_norm_sq_of_inH (hZ.inH.mono (by norm_num)),
    summable_grad_sq hZ.mz, summable_hess hZ.inH⟩

/-- `fastNL` is a real `ℓ²` field with `‖fastNL‖_{ℓ²} ≤ ‖Q(y,y)‖₀`. -/
lemma fastNL_l2 (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    IsReal (fastNL r g y u) ∧ (Summable fun k => ‖fastNL r g y u k‖ ^ 2) ∧
      Real.sqrt (∑' k, ‖fastNL r g y u k‖ ^ 2) ≤ hnorm 0 (Qphase (r * u) (y u) (y u)) := by
  have hy := h.sol.adm u hu huT
  have hQ : InH 0 (Qphase (r * u) (y u) (y u)) := (hnorm_Qm_zero_le (phaseM_bdd _) hy.mz hy.mz).1
  have hQr : IsReal (Qphase (r * u) (y u) (y u)) :=
    (majorized_Qphase (r * u)).real 0 (y u) (y u) hy hy
  refine ⟨hQr.PiF'.neg', summable_norm_sq_of_inH hQ.PiF.neg, ?_⟩
  have h0 : fastNL r g y u 0 = 0 := by simp [fastNL, PiF]
  rw [← hnorm_zero_eq h0]
  unfold fastNL
  rw [hnorm_neg]
  exact hnorm_PiF_le hQ

/-- `slowNL` is a real `ℓ²` field with `‖slowNL‖_{ℓ²} ≤ ‖Q(y,y)‖₀ + ‖g‖₂`. -/
lemma slowNL_l2 (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    IsReal (slowNL r g y u) ∧ (Summable fun k => ‖slowNL r g y u k‖ ^ 2) ∧
      Real.sqrt (∑' k, ‖slowNL r g y u k‖ ^ 2) ≤
        hnorm 0 (Qphase (r * u) (y u) (y u)) + hnorm 2 g := by
  have hy := h.sol.adm u hu huT
  have hQ : InH 0 (Qphase (r * u) (y u) (y u)) := (hnorm_Qm_zero_le (phaseM_bdd _) hy.mz hy.mz).1
  have hQr : IsReal (Qphase (r * u) (y u) (y u)) :=
    (majorized_Qphase (r * u)).real 0 (y u) (y u) hy hy
  have hg0 : InH 0 g := h.force_adm.inH.mono (by norm_num)
  have hI : InH 0 (slowNL r g y u) := hQ.PiS.neg.add hg0.PiS
  refine ⟨fun k => ?_, summable_norm_sq_of_inH hI, ?_⟩
  · simp only [slowNL, Pi.add_apply, Pi.neg_apply, hQr.PiS' k, h.force_adm.PiS.real k, conjV_neg']
    ext i
    simp [conjV]
  · have hQ0 : Qphase (r * u) (y u) (y u) 0 = 0 := by simp [Qphase, Qm, hel_zero_mode]
    have h0 : slowNL r g y u 0 = 0 := by simp [slowNL, PiS, h.force_adm.mean, hQ0]
    rw [← hnorm_zero_eq h0]
    unfold slowNL
    refine (hnorm_add_le hQ.PiS.neg hg0.PiS).trans ?_
    rw [hnorm_neg]
    exact add_le_add (hnorm_PiS_le hQ)
      ((hnorm_PiS_le hg0).trans (hnorm_mono (by norm_num) h.force_adm.inH))

/-- The integrand of the derivative of `E⁰` along the actual solution (TeX: "`(E⁰)' =
Re⟨Q_nr(F,F),AF⟩ − E_heat − DE⁰[Π_F Q_τ(S+F,S+F)] − DE⁰[H_{ψ,F}]`"; here the last two are
`DE⁰[fastNL]` with `fastNL = −Π_F Q(y,y)`). -/
def cubicRHS (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  pair 1 (PiF (actual r g y u)) (Qnr (r * u) (PiF (actual r g y u)) (PiF (actual r g y u))) -
    cubicHeat r (r * u) (PiF (actual r g y u)) +
    cubicD 1 (-1) r (r * u) (PiF (actual r g y u)) (fastNL r g y u)

/-- The integrand of the derivative of `⟨z₁, X₁ z₁⟩` along the actual solution: the frozen part
`4⟨AF, Q^♯_{metDM}(S,F)⟩` and the three insertions of the non-heat right-hand sides. -/
def metricRHS (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  4 * (pair 1 (PiF (actual r g y u))
      (Qm (metDM (r * u)) (PiS (actual r g y u)) (PiF (actual r g y u))) +
    pair 1 (PiF (actual r g y u)) (X1op r (r * u) (slowNL r g y u) (PiF (actual r g y u))) +
    pair 1 (PiF (actual r g y u)) (X1op r (r * u) (PiS (actual r g y u)) (fastNL r g y u)) +
    pair 1 (fastNL r g y u) (X1op r (r * u) (PiS (actual r g y u)) (PiF (actual r g y u))))

/-- The gain bound of the corrector multiplier along the path. -/
lemma corrM_gain (ε r τ : ℝ) (hε : ε = 1 ∨ ε = -1) (a b c : Sgn) (p q : Mode) :
    ‖corrM ε r τ a b c p q‖ ≤ 1 / absSq (p + q) := by
  unfold corrM
  split_ifs with h0
  · exact norm_corrSym_le hε r τ a b c h0.1
  · rw [norm_zero]
    exact div_nonneg zero_le_one (absSq_nonneg _)

/-- **E⁰ is absolutely continuous along the actual solution** with derivative `cubicRHS`
(TeX "Its exact derivative is …"): `E⁰(t) − E⁰(s) = ∫ₛᵗ (⟨AF, Q_nr(F,F)⟩ − E_heat + DE⁰[fastNL])`.
Proof: `trilinear_integral_identity` with the paths `F, F, AF`, the multiplier
`corrM(−1, r, ru)` (`hasDerivAt_corrM`), the summability control `tripD_gain_summable` with the
sup bounds of `exists_actual_bound`/`exists_Qphase_bound`, the heat combination
`tripT_corr_heat_combine` and the bridge `pair_one_eq_re_tsum_gain`. -/
theorem cubicCorr_identity (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (cubicRHS r g y) volume s t ∧
      cubicCorr r g y t - cubicCorr r g y s = ∫ u in s..t, cubicRHS r g y u := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hmem : ∀ u ∈ Icc s t, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hs.trans hu.1, lt_lifespan hu.2 ht⟩
  set X : ℝ → Field := fun u => PiF (actual r g y u) with hXdef
  set Z : ℝ → Field := fun u => lapF (PiF (actual r g y u)) with hZdef
  set X' : ℝ → Field := fastRHS r g y with hX'def
  set Z' : ℝ → Field := fun u => lapF (fastRHS r g y u) with hZ'def
  set m : ℝ → Mult := fun u => corrM (-1) r (r * u) with hmdef
  set m' : ℝ → Mult := fun u => corrDM (-1) r (r * u) with hm'def
  have hgain : ∀ u a b c p q, ‖m u a b c p q‖ ≤ 1 / absSq (p + q) := fun u a b c p q =>
    corrM_gain (-1) r (r * u) (Or.inr rfl) a b c p q
  have hm'B : ∀ u, (m' u).Bdd := fun u => corrDM_bdd (Or.inr rfl) r (r * u)
  have hadm : ∀ u ∈ Icc s t, Adm 2 (X u) := fun u hu =>
    (actual_adm h (hmem u hu).1 (hmem u hu).2).PiF
  -- derivatives and continuity of the paths
  have hXd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => X v k) (X' u k) (Icc s t) u :=
    fun k u hu => (fast_mode h k (hmem u hu).1 (hmem u hu).2).mono fun v hv =>
      show v ∈ Ici 0 from hs.trans hv.1
  have hZd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => Z v k) (Z' u k) (Icc s t) u :=
    fun k u hu => (hXd k u hu).const_smul (absSq k : ℂ)
  have hX'c : ∀ k, ContinuousOn (fun u => X' u k) (Icc s t) := fun k =>
    (continuousOn_fastRHS_mode h ht0 ht k).mono (Icc_subset_Icc_left hs)
  have hZ'c : ∀ k, ContinuousOn (fun u => Z' u k) (Icc s t) := fun k =>
    (hX'c k).const_smul (absSq k : ℂ)
  have hmd : ∀ a b c p q, ∀ u ∈ Icc s t,
      HasDerivWithinAt (fun v => m v a b c p q) (m' u a b c p q) (Icc s t) u :=
    fun a b c p q u _ => (hasDerivAt_corrM (-1) r a b c p q u).hasDerivWithinAt
  have hm'c : ∀ a b c p q, ContinuousOn (fun u => m' u a b c p q) (Icc s t) :=
    fun a b c p q => (continuous_corrDM (-1) r a b c p q).continuousOn
  -- summability data at each time
  have hdat : ∀ u ∈ Icc s t, (Summable fun k => ‖X u k‖) ∧ (Summable fun k => ‖X u k‖ ^ 2) ∧
      (Summable fun k => (absk k * ‖X u k‖) ^ 2) ∧
      (Summable fun k => (absSq k * ‖X u k‖) ^ 2) := fun u hu => adm_summables (hadm u hu)
  have hX'2 : ∀ u ∈ Icc s t, Summable fun k => ‖X' u k‖ ^ 2 := fun u hu =>
    (fastRHS_l2 h (hmem u hu).1 (hmem u hu).2).1
  -- summability at the endpoints
  have hsum : ∀ u ∈ Icc s t, Summable (tripPath m X X Z u) := fun u hu => by
    obtain ⟨h1, h2, h3, h4⟩ := hdat u hu
    have hb := (gradTri_bound (fun k => norm_nonneg (X u k)) (fun k => norm_nonneg (X u k))
      (fun k => norm_nonneg (X u k)) h1 h3 h1 h3 h2).1
    refine Summable.of_norm_bounded (hb.mul_left 8) fun x => ?_
    exact norm_tripT_gain_lap (hgain u) (X u) (X u) (X u) x.1 x.2
  -- the uniform bound
  obtain ⟨Mx, hMx0, hMx⟩ := exists_actual_bound h hr ht
  obtain ⟨D, hD0, hD⟩ := exists_Qphase_bound h ht
  have hc4 := c4_pos
  set C := 8 * ((Mx * (c4 * Mx) * Mx + c4 * Mx * Mx * Mx) +
    (2 * (Mx + D) * Mx * (c4 * Mx) + (Mx + D) * (c4 * Mx) * Mx) +
    (2 * Mx * (Mx + D) * (c4 * Mx) + c4 * Mx * (Mx + D) * Mx) +
    (Mx * (c4 * Mx) * (Mx + D) + c4 * Mx * Mx * (Mx + D))) with hCdef
  have hB : ∀ u ∈ Icc s t, Summable (fun x => ‖tripDPath m m' X X' X X' Z Z' u x‖) ∧
      ∑' x, ‖tripDPath m m' X X' X X' Z Z' u x‖ ≤ C := by
    intro u hu
    obtain ⟨h1, h2, h3, h4⟩ := hdat u hu
    have hu' : u ∈ Icc 0 t := ⟨(hmem u hu).1, hu.2⟩
    obtain ⟨hS0, hle⟩ := tripD_gain_summable (hgain u) (hm'B u) h1 h3 h1 h3 h1 h3 h4
      (hX'2 u hu) (hX'2 u hu) (hX'2 u hu)
    refine ⟨hS0, hle.trans ?_⟩
    have hx2 : hnorm 2 (actual r g y u) ≤ Mx := hMx u hu'
    have hF2 : hnorm 2 (X u) ≤ Mx :=
      (hnorm_PiF_le (actual_adm h (hmem u hu).1 (hmem u hu).2).inH).trans hx2
    have e1 : ∑' k, ‖X u k‖ = wiener (X u) := rfl
    have hW : ∑' k, ‖X u k‖ ≤ c4 * Mx := by
      rw [e1]; exact (wiener_le (hadm u hu).mz).trans (mul_le_mul_of_nonneg_left hF2 hc4.le)
    have hG1 : Real.sqrt (∑' k, (absk k * ‖X u k‖) ^ 2) ≤ Mx := by
      rw [sqrt_tsum_grad_sq]
      exact (hnorm_mono (by norm_num) (hadm u hu).inH).trans hF2
    have hG2 : Real.sqrt (∑' k, (absSq k * ‖X u k‖) ^ 2) ≤ Mx := by
      rw [sqrt_tsum_hess_sq (hadm u hu).inH]; exact hF2
    have hN' : Real.sqrt (∑' k, ‖X' u k‖ ^ 2) ≤ Mx + D :=
      (fastRHS_l2 h (hmem u hu).1 (hmem u hu).2).2.trans (add_le_add hF2 (hD u hu').2)
    have n1 : 0 ≤ ∑' k, ‖X u k‖ := tsum_nonneg fun _ => norm_nonneg _
    have n2 := Real.sqrt_nonneg (∑' k, (absk k * ‖X u k‖) ^ 2)
    have n3 := Real.sqrt_nonneg (∑' k, (absSq k * ‖X u k‖) ^ 2)
    have n4 := Real.sqrt_nonneg (∑' k, ‖X' u k‖ ^ 2)
    have hcM : 0 ≤ c4 * Mx := mul_nonneg hc4.le hMx0
    have hMD : 0 ≤ Mx + D := add_nonneg hMx0 hD0
    rw [hCdef]
    gcongr
  -- the complex identity
  have key := trilinear_integral_identity (m := m) (m' := m') (X := X) (X' := X') (Y := X)
    (Y' := X') (Z := Z) (Z' := Z') hst hmd hm'c hXd hX'c hXd hX'c hZd hZ'c (hsum s ⟨le_rfl, hst⟩)
    (hsum t ⟨hst, le_rfl⟩) hB
  -- continuity of the derivative family and integrability
  have hmc : ∀ a b c p q, ContinuousOn (fun u => m u a b c p q) (Icc s t) :=
    fun a b c p q u hu => (hmd a b c p q u hu).continuousWithinAt
  have hXc : ∀ k, ContinuousOn (fun u => X u k) (Icc s t) := fun k u hu =>
    (hXd k u hu).continuousWithinAt
  have hZc : ∀ k, ContinuousOn (fun u => Z u k) (Icc s t) := fun k u hu =>
    (hZd k u hu).continuousWithinAt
  have hc : ∀ x : Mode × Mode,
      ContinuousOn (fun u => tripDPath m m' X X' X X' Z Z' u x) (Icc s t) := fun x =>
    continuousOn_tripDPath x (fun a b c => hmc a b c _ _) (fun a b c => hm'c a b c _ _)
      (hXc _) (hX'c _) (hXc _) (hX'c _) (hZc _) (hZ'c _)
  have hG := intervalIntegrable_tsum_of_bound hst hc hB
  -- the left side
  have hL : ∀ u ∈ Icc s t, (∑' x, tripPath m X X Z u x).re = cubicCorr r g y u := fun u hu => by
    obtain ⟨h1, h2, h3, h4⟩ := hdat u hu
    have hb := (gradTri_bound (fun k => norm_nonneg (X u k)) (fun k => norm_nonneg (X u k))
      (fun k => norm_nonneg (X u k)) h1 h3 h1 h3 h2).1
    have hs' : Summable fun x : Mode × Mode => tripT (m u) (X u) (X u) (lapF (X u)) x.1 x.2 :=
      Summable.of_norm_bounded (hb.mul_left 8) fun x =>
        norm_tripT_gain_lap (hgain u) (X u) (X u) (X u) x.1 x.2
    have e := pair_one_eq_re_tsum_gain (hgain u) (hadm u hu).real h2 h2 (Or.inl h3) hs'
    unfold cubicCorr cubicE corr
    rw [Nat.cast_one]
    exact e.symm
  -- the integrand
  have hre : ∀ u ∈ Icc s t, (∑' x, tripDPath m m' X X' X X' Z Z' u x).re = cubicRHS r g y u := by
    intro u hu
    obtain ⟨h1, h2, h3, h4⟩ := hdat u hu
    have hu0 := (hmem u hu).1
    have huT := (hmem u hu).2
    obtain ⟨hNr, hN2, -⟩ := fastNL_l2 h hu0 huT
    have hreal : IsReal (X u) := (hadm u hu).real
    have hlap2 : Summable fun k => ‖lapF (X u) k‖ ^ 2 := (lapF_l2 (hadm u hu).inH).1
    have hX'eq : X' u = -lapF (X u) + fastNL r g y u := fastRHS_eq_lap u
    have hZ'eq : Z' u = -lapF (lapF (X u)) + lapF (fastNL r g y u) := by
      show lapF (fastRHS r g y u) = _
      rw [fastRHS_eq_lap, lapF_add, lapF_neg]
    -- the six families
    have g0 := fun k => norm_nonneg (X u k)
    have gN := fun k => norm_nonneg (fastNL r g y u k)
    have gL := fun k => norm_nonneg (lapF (X u) k)
    have sA1 : Summable fun x : Mode × Mode =>
        tripT (nonresM (r * u)) (X u) (X u) (lapF (X u)) x.1 x.2 := by
      have hb := (gradTri_bound g0 g0 (fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _))
        h1 h3 h1 h3 h4).1
      refine Summable.of_norm_bounded (hb.mul_left 8) fun x => ?_
      have := norm_tripT_bdd_lap (nonresM_bdd (r * u)) (X u) (X u) (X u) x.1 x.2
      simpa only [gradTri, absSq_neg] using this
    have sA2 : Summable fun x : Mode × Mode =>
        tripT (m u) (lapF (X u)) (X u) (lapF (X u)) x.1 x.2 := by
      have hb := (gradTri_bound_first gL g0 g0 hlap2 h1 h3 h1 h3).1
      exact Summable.of_norm_bounded (hb.mul_left 8) fun x =>
        norm_tripT_gain_lap (hgain u) _ _ _ x.1 x.2
    have sA3 : Summable fun x : Mode × Mode =>
        tripT (m u) (fastNL r g y u) (X u) (lapF (X u)) x.1 x.2 := by
      have hb := (gradTri_bound_first gN g0 g0 hN2 h1 h3 h1 h3).1
      exact Summable.of_norm_bounded (hb.mul_left 8) fun x =>
        norm_tripT_gain_lap (hgain u) _ _ _ x.1 x.2
    have sA4 : Summable fun x : Mode × Mode =>
        tripT (m u) (X u) (lapF (X u)) (lapF (X u)) x.1 x.2 := by
      have hb := (gradTri_bound_mid g0 gL g0 h1 h3 hlap2 h1 h3).1
      exact Summable.of_norm_bounded (hb.mul_left 8) fun x =>
        norm_tripT_gain_lap (hgain u) _ _ _ x.1 x.2
    have sA5 : Summable fun x : Mode × Mode =>
        tripT (m u) (X u) (fastNL r g y u) (lapF (X u)) x.1 x.2 := by
      have hb := (gradTri_bound_mid g0 gN g0 h1 h3 hN2 h1 h3).1
      exact Summable.of_norm_bounded (hb.mul_left 8) fun x =>
        norm_tripT_gain_lap (hgain u) _ _ _ x.1 x.2
    have sA6 : Summable fun x : Mode × Mode =>
        tripT (m u) (X u) (X u) (lapF (fastNL r g y u)) x.1 x.2 := by
      have hb := (gradTri_bound g0 g0 gN h1 h3 h1 h3 hN2).1
      exact Summable.of_norm_bounded (hb.mul_left 8) fun x =>
        norm_tripT_gain_lap (hgain u) _ _ _ x.1 x.2
    -- the pointwise decomposition of the derivative family
    have hpt : ∀ x : Mode × Mode, tripDPath m m' X X' X X' Z Z' u x =
        tripT (nonresM (r * u)) (X u) (X u) (lapF (X u)) x.1 x.2 +
        (-tripT (m u) (lapF (X u)) (X u) (lapF (X u)) x.1 x.2) +
        tripT (m u) (fastNL r g y u) (X u) (lapF (X u)) x.1 x.2 +
        (-tripT (m u) (X u) (lapF (X u)) (lapF (X u)) x.1 x.2) +
        tripT (m u) (X u) (fastNL r g y u) (lapF (X u)) x.1 x.2 +
        tripT (m u) (X u) (X u) (lapF (fastNL r g y u)) x.1 x.2 := by
      intro x
      simp only [tripDPath, tripD]
      have hZu : Z u = lapF (X u) := rfl
      rw [hZu, hX'eq, hZ'eq, tripT_add_left, tripT_add_mid, tripT_add_right, tripT_neg_left,
        tripT_neg_mid]
      have hc := tripT_corr_heat_combine r (r * u) (X u) (X u) (X u) x.1 x.2
      simp only [hmdef, hm'def] at hc ⊢
      linear_combination hc
    have hsplit : (∑' x, tripDPath m m' X X' X X' Z Z' u x) =
        (∑' x : Mode × Mode, tripT (nonresM (r * u)) (X u) (X u) (lapF (X u)) x.1 x.2) +
        (-∑' x : Mode × Mode, tripT (m u) (lapF (X u)) (X u) (lapF (X u)) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (fastNL r g y u) (X u) (lapF (X u)) x.1 x.2) +
        (-∑' x : Mode × Mode, tripT (m u) (X u) (lapF (X u)) (lapF (X u)) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (X u) (fastNL r g y u) (lapF (X u)) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (X u) (X u) (lapF (fastNL r g y u)) x.1 x.2) := by
      rw [← tsum_neg, ← tsum_neg, ← sA1.tsum_add sA2.neg, ← (sA1.add sA2.neg).tsum_add sA3,
        ← ((sA1.add sA2.neg).add sA3).tsum_add sA4.neg,
        ← (((sA1.add sA2.neg).add sA3).add sA4.neg).tsum_add sA5,
        ← ((((sA1.add sA2.neg).add sA3).add sA4.neg).add sA5).tsum_add sA6]
      exact tsum_congr hpt
    rw [hsplit]
    simp only [Complex.add_re, Complex.neg_re]
    -- the six pairings
    have r1 : (∑' x : Mode × Mode, tripT (nonresM (r * u)) (X u) (X u) (lapF (X u)) x.1 x.2).re =
        pair 1 (X u) (Qnr (r * u) (X u) (X u)) :=
      (pair_one_eq_re_tsum hreal (fun k => inner_Qm (nonresM_bdd (r * u)) hreal.lapF
        (hadm u hu).mz (hadm u hu).mz k) sA1).symm
    have r2 : (∑' x : Mode × Mode, tripT (m u) (lapF (X u)) (X u) (lapF (X u)) x.1 x.2).re =
        pair 1 (X u) (corr (-1) r (r * u) (lapF (X u)) (X u)) :=
      (pair_one_eq_re_tsum_gain (hgain u) hreal hlap2 h2 (Or.inr h3) sA2).symm
    have r3 : (∑' x : Mode × Mode, tripT (m u) (fastNL r g y u) (X u) (lapF (X u)) x.1 x.2).re =
        pair 1 (X u) (corr (-1) r (r * u) (fastNL r g y u) (X u)) :=
      (pair_one_eq_re_tsum_gain (hgain u) hreal hN2 h2 (Or.inr h3) sA3).symm
    have r4 : (∑' x : Mode × Mode, tripT (m u) (X u) (lapF (X u)) (lapF (X u)) x.1 x.2).re =
        pair 1 (X u) (corr (-1) r (r * u) (X u) (lapF (X u))) :=
      (pair_one_eq_re_tsum_gain (hgain u) hreal h2 hlap2 (Or.inl h3) sA4).symm
    have r5 : (∑' x : Mode × Mode, tripT (m u) (X u) (fastNL r g y u) (lapF (X u)) x.1 x.2).re =
        pair 1 (X u) (corr (-1) r (r * u) (X u) (fastNL r g y u)) :=
      (pair_one_eq_re_tsum_gain (hgain u) hreal h2 hN2 (Or.inl h3) sA5).symm
    have r6 : (∑' x : Mode × Mode, tripT (m u) (X u) (X u) (lapF (fastNL r g y u)) x.1 x.2).re =
        pair 1 (fastNL r g y u) (corr (-1) r (r * u) (X u) (X u)) :=
      (pair_one_eq_re_tsum hNr (fun k => inner_Qm (corrM_bdd (Or.inr rfl) r (r * u)) hNr.lapF
        (hadm u hu).mz (hadm u hu).mz k) sA6).symm
    rw [r1, r2, r3, r4, r5, r6]
    unfold cubicRHS cubicHeat cubicD
    rw [Nat.cast_one, PiF_fastNL]
    ring
  -- integrability of the real part
  have hGre : IntervalIntegrable (fun u => (∑' x, tripDPath m m' X X' X X' Z Z' u x).re)
      volume s t := by
    refine hG.mono_fun ?_ ?_
    · exact Complex.continuous_re.comp_aestronglyMeasurable
        ((intervalIntegrable_iff.1 hG).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall fun u => by
        simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm _
  have hI : IntervalIntegrable (cubicRHS r g y) volume s t := by
    refine hGre.congr fun u hu => hre u ?_
    rw [uIoc_of_le hst] at hu
    exact Ioc_subset_Icc_self hu
  refine ⟨hI, ?_⟩
  have hR := congrArg Complex.re key
  rw [Complex.sub_re, hL t ⟨hst, le_rfl⟩, hL s ⟨le_rfl, hst⟩] at hR
  rw [hR, ← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hG]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hst] at hu
  simp only [Complex.reCLM_apply]
  exact hre u hu

/-- **`⟨z₁, X₁ z₁⟩` is absolutely continuous along the actual solution** with derivative
`metricRHS` (TeX eq. quant-metric, the `X₁` part of "the literal polynomial differentiation").
Same route as `cubicCorr_identity` with the paths `S, F, AF`, the multiplier `metM(r, ru)`
(`hasDerivAt_metM`) and the heat combination `tripT_met_heat_combine`. -/
theorem metricCorr_identity (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (metricRHS r g y) volume s t ∧
      metricCorr r g y t - metricCorr r g y s = ∫ u in s..t, metricRHS r g y u := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hmem : ∀ u ∈ Icc s t, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hs.trans hu.1, lt_lifespan hu.2 ht⟩
  set X : ℝ → Field := fun u => PiS (actual r g y u) with hXdef
  set Y : ℝ → Field := fun u => PiF (actual r g y u) with hYdef
  set Z : ℝ → Field := fun u => lapF (PiF (actual r g y u)) with hZdef
  set X' : ℝ → Field := slowRHS r g y with hX'def
  set Y' : ℝ → Field := fastRHS r g y with hY'def
  set Z' : ℝ → Field := fun u => lapF (fastRHS r g y u) with hZ'def
  set m : ℝ → Mult := fun u => metM r (r * u) with hmdef
  set m' : ℝ → Mult := fun u => metDM' r (r * u) with hm'def
  have hgain : ∀ u a b c p q, ‖m u a b c p q‖ ≤ 1 / absSq (p + q) := fun u a b c p q =>
    norm_metM_le_absSq r (r * u) a b c p q
  have hm'B : ∀ u, (m' u).Bdd := fun u => metDM'_bdd r (r * u)
  have hadmX : ∀ u ∈ Icc s t, Adm 2 (X u) := fun u hu =>
    (actual_adm h (hmem u hu).1 (hmem u hu).2).PiS
  have hadmY : ∀ u ∈ Icc s t, Adm 2 (Y u) := fun u hu =>
    (actual_adm h (hmem u hu).1 (hmem u hu).2).PiF
  -- derivatives and continuity of the paths
  have hXd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => X v k) (X' u k) (Icc s t) u :=
    fun k u hu => (slow_mode h k (hmem u hu).1 (hmem u hu).2).mono fun v hv =>
      show v ∈ Ici 0 from hs.trans hv.1
  have hYd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => Y v k) (Y' u k) (Icc s t) u :=
    fun k u hu => (fast_mode h k (hmem u hu).1 (hmem u hu).2).mono fun v hv =>
      show v ∈ Ici 0 from hs.trans hv.1
  have hZd : ∀ k, ∀ u ∈ Icc s t, HasDerivWithinAt (fun v => Z v k) (Z' u k) (Icc s t) u :=
    fun k u hu => (hYd k u hu).const_smul (absSq k : ℂ)
  have hX'c : ∀ k, ContinuousOn (fun u => X' u k) (Icc s t) := fun k =>
    (continuousOn_slowRHS_mode h ht0 ht k).mono (Icc_subset_Icc_left hs)
  have hY'c : ∀ k, ContinuousOn (fun u => Y' u k) (Icc s t) := fun k =>
    (continuousOn_fastRHS_mode h ht0 ht k).mono (Icc_subset_Icc_left hs)
  have hZ'c : ∀ k, ContinuousOn (fun u => Z' u k) (Icc s t) := fun k =>
    (hY'c k).const_smul (absSq k : ℂ)
  have hmd : ∀ a b c p q, ∀ u ∈ Icc s t,
      HasDerivWithinAt (fun v => m v a b c p q) (m' u a b c p q) (Icc s t) u :=
    fun a b c p q u _ => (hasDerivAt_metM r a b c p q u).hasDerivWithinAt
  have hm'c : ∀ a b c p q, ContinuousOn (fun u => m' u a b c p q) (Icc s t) :=
    fun a b c p q => (continuous_metDM' r a b c p q).continuousOn
  -- summability data at each time
  have hdatX : ∀ u ∈ Icc s t, (Summable fun k => ‖X u k‖) ∧ (Summable fun k => ‖X u k‖ ^ 2) ∧
      (Summable fun k => (absk k * ‖X u k‖) ^ 2) ∧
      (Summable fun k => (absSq k * ‖X u k‖) ^ 2) := fun u hu => adm_summables (hadmX u hu)
  have hdatY : ∀ u ∈ Icc s t, (Summable fun k => ‖Y u k‖) ∧ (Summable fun k => ‖Y u k‖ ^ 2) ∧
      (Summable fun k => (absk k * ‖Y u k‖) ^ 2) ∧
      (Summable fun k => (absSq k * ‖Y u k‖) ^ 2) := fun u hu => adm_summables (hadmY u hu)
  have hX'2 : ∀ u ∈ Icc s t, Summable fun k => ‖X' u k‖ ^ 2 := fun u hu =>
    (slowRHS_l2 h (hmem u hu).1 (hmem u hu).2).1
  have hY'2 : ∀ u ∈ Icc s t, Summable fun k => ‖Y' u k‖ ^ 2 := fun u hu =>
    (fastRHS_l2 h (hmem u hu).1 (hmem u hu).2).1
  have hsum : ∀ u ∈ Icc s t, Summable (tripPath m X Y Z u) := fun u hu => by
    obtain ⟨x1, x2, x3, x4⟩ := hdatX u hu
    obtain ⟨y1, y2, y3, y4⟩ := hdatY u hu
    have hb := (gradTri_bound (fun k => norm_nonneg (X u k)) (fun k => norm_nonneg (Y u k))
      (fun k => norm_nonneg (Y u k)) x1 x3 y1 y3 y2).1
    refine Summable.of_norm_bounded (hb.mul_left 8) fun x => ?_
    exact norm_tripT_gain_lap (hgain u) (X u) (Y u) (Y u) x.1 x.2
  -- the uniform bound
  obtain ⟨Mx, hMx0, hMx⟩ := exists_actual_bound h hr ht
  obtain ⟨D, hD0, hD⟩ := exists_Qphase_bound h ht
  have hc4 := c4_pos
  have hg2 := hnorm_nonneg 2 g
  set C := 8 * ((Mx * (c4 * Mx) * Mx + c4 * Mx * Mx * Mx) +
    (2 * (Mx + D + hnorm 2 g) * Mx * (c4 * Mx) + (Mx + D + hnorm 2 g) * (c4 * Mx) * Mx) +
    (2 * Mx * (Mx + D) * (c4 * Mx) + c4 * Mx * (Mx + D) * Mx) +
    (Mx * (c4 * Mx) * (Mx + D) + c4 * Mx * Mx * (Mx + D))) with hCdef
  have hB : ∀ u ∈ Icc s t, Summable (fun x => ‖tripDPath m m' X X' Y Y' Z Z' u x‖) ∧
      ∑' x, ‖tripDPath m m' X X' Y Y' Z Z' u x‖ ≤ C := by
    intro u hu
    obtain ⟨x1, x2, x3, x4⟩ := hdatX u hu
    obtain ⟨y1, y2, y3, y4⟩ := hdatY u hu
    have hu' : u ∈ Icc 0 t := ⟨(hmem u hu).1, hu.2⟩
    obtain ⟨hS0, hle⟩ := tripD_gain_summable (hgain u) (hm'B u) x1 x3 y1 y3 y1 y3 y4
      (hX'2 u hu) (hY'2 u hu) (hY'2 u hu)
    refine ⟨hS0, hle.trans ?_⟩
    have hx2 : hnorm 2 (actual r g y u) ≤ Mx := hMx u hu'
    have hadm := actual_adm h (hmem u hu).1 (hmem u hu).2
    have hF2 : hnorm 2 (Y u) ≤ Mx := (hnorm_PiF_le hadm.inH).trans hx2
    have hS2 : hnorm 2 (X u) ≤ Mx := (hnorm_PiS_le hadm.inH).trans hx2
    have hWX : ∑' k, ‖X u k‖ ≤ c4 * Mx :=
      (wiener_le (hadmX u hu).mz).trans (mul_le_mul_of_nonneg_left hS2 hc4.le)
    have hWY : ∑' k, ‖Y u k‖ ≤ c4 * Mx :=
      (wiener_le (hadmY u hu).mz).trans (mul_le_mul_of_nonneg_left hF2 hc4.le)
    have hG1 : Real.sqrt (∑' k, (absk k * ‖X u k‖) ^ 2) ≤ Mx := by
      rw [sqrt_tsum_grad_sq]
      exact (hnorm_mono (by norm_num) (hadmX u hu).inH).trans hS2
    have hG2 : Real.sqrt (∑' k, (absk k * ‖Y u k‖) ^ 2) ≤ Mx := by
      rw [sqrt_tsum_grad_sq]
      exact (hnorm_mono (by norm_num) (hadmY u hu).inH).trans hF2
    have hG3 : Real.sqrt (∑' k, (absSq k * ‖Y u k‖) ^ 2) ≤ Mx := by
      rw [sqrt_tsum_hess_sq (hadmY u hu).inH]; exact hF2
    have hNX : Real.sqrt (∑' k, ‖X' u k‖ ^ 2) ≤ Mx + D + hnorm 2 g :=
      (slowRHS_l2 h (hmem u hu).1 (hmem u hu).2).2.trans
        (add_le_add (add_le_add hS2 (hD u hu').2) le_rfl)
    have hNY : Real.sqrt (∑' k, ‖Y' u k‖ ^ 2) ≤ Mx + D :=
      (fastRHS_l2 h (hmem u hu).1 (hmem u hu).2).2.trans (add_le_add hF2 (hD u hu').2)
    have n1 : 0 ≤ ∑' k, ‖X u k‖ := tsum_nonneg fun _ => norm_nonneg _
    have n1' : 0 ≤ ∑' k, ‖Y u k‖ := tsum_nonneg fun _ => norm_nonneg _
    have n2 := Real.sqrt_nonneg (∑' k, (absk k * ‖X u k‖) ^ 2)
    have n2' := Real.sqrt_nonneg (∑' k, (absk k * ‖Y u k‖) ^ 2)
    have n3 := Real.sqrt_nonneg (∑' k, (absSq k * ‖Y u k‖) ^ 2)
    have n4 := Real.sqrt_nonneg (∑' k, ‖X' u k‖ ^ 2)
    have n4' := Real.sqrt_nonneg (∑' k, ‖Y' u k‖ ^ 2)
    have hcM : 0 ≤ c4 * Mx := mul_nonneg hc4.le hMx0
    have hMD : 0 ≤ Mx + D := add_nonneg hMx0 hD0
    have hMDg : 0 ≤ Mx + D + hnorm 2 g := add_nonneg hMD hg2
    rw [hCdef]
    gcongr
  -- the complex identity
  have key := trilinear_integral_identity (m := m) (m' := m') (X := X) (X' := X') (Y := Y)
    (Y' := Y') (Z := Z) (Z' := Z') hst hmd hm'c hXd hX'c hYd hY'c hZd hZ'c (hsum s ⟨le_rfl, hst⟩)
    (hsum t ⟨hst, le_rfl⟩) hB
  have hmc : ∀ a b c p q, ContinuousOn (fun u => m u a b c p q) (Icc s t) :=
    fun a b c p q u hu => (hmd a b c p q u hu).continuousWithinAt
  have hXc : ∀ k, ContinuousOn (fun u => X u k) (Icc s t) := fun k u hu =>
    (hXd k u hu).continuousWithinAt
  have hYc : ∀ k, ContinuousOn (fun u => Y u k) (Icc s t) := fun k u hu =>
    (hYd k u hu).continuousWithinAt
  have hZc : ∀ k, ContinuousOn (fun u => Z u k) (Icc s t) := fun k u hu =>
    (hZd k u hu).continuousWithinAt
  have hc : ∀ x : Mode × Mode,
      ContinuousOn (fun u => tripDPath m m' X X' Y Y' Z Z' u x) (Icc s t) := fun x =>
    continuousOn_tripDPath x (fun a b c => hmc a b c _ _) (fun a b c => hm'c a b c _ _)
      (hXc _) (hX'c _) (hYc _) (hY'c _) (hZc _) (hZ'c _)
  have hG := intervalIntegrable_tsum_of_bound hst hc hB
  -- the left side: `X1form = 4 Re ∑ tripT metM S F (AF)`
  have hL : ∀ u ∈ Icc s t, 4 * (∑' x, tripPath m X Y Z u x).re = metricCorr r g y u := by
    intro u hu
    obtain ⟨x1, x2, x3, x4⟩ := hdatX u hu
    obtain ⟨y1, y2, y3, y4⟩ := hdatY u hu
    have hb := (gradTri_bound (fun k => norm_nonneg (X u k)) (fun k => norm_nonneg (Y u k))
      (fun k => norm_nonneg (Y u k)) x1 x3 y1 y3 y2).1
    have hs' : Summable fun x : Mode × Mode => tripT (m u) (X u) (Y u) (lapF (Y u)) x.1 x.2 :=
      Summable.of_norm_bounded (hb.mul_left 8) fun x =>
        norm_tripT_gain_lap (hgain u) (X u) (Y u) (Y u) x.1 x.2
    have e := pair_one_eq_re_tsum_gain (hgain u) (hadmY u hu).real x2 y2 (Or.inl x3) hs'
    show 4 * (∑' x, tripPath m X Y Z u x).re = 4 * pair 1 (Y u) (Qm (m u) (X u) (Y u))
    rw [e]
    rfl
  -- the integrand
  have hre : ∀ u ∈ Icc s t, 4 * (∑' x, tripDPath m m' X X' Y Y' Z Z' u x).re =
      metricRHS r g y u := by
    intro u hu
    obtain ⟨x1, x2, x3, x4⟩ := hdatX u hu
    obtain ⟨y1, y2, y3, y4⟩ := hdatY u hu
    have hu0 := (hmem u hu).1
    have huT := (hmem u hu).2
    obtain ⟨hNr, hN2, -⟩ := fastNL_l2 h hu0 huT
    obtain ⟨-, hS2, -⟩ := slowNL_l2 h hu0 huT
    have hrealY : IsReal (Y u) := (hadmY u hu).real
    have hX'eq : X' u = -lapF (X u) + slowNL r g y u := slowRHS_eq_lap u
    have hY'eq : Y' u = -lapF (Y u) + fastNL r g y u := fastRHS_eq_lap u
    have hZ'eq : Z' u = -lapF (lapF (Y u)) + lapF (fastNL r g y u) := by
      show lapF (fastRHS r g y u) = _
      rw [fastRHS_eq_lap, lapF_add, lapF_neg]
    have gX := fun k => norm_nonneg (X u k)
    have gY := fun k => norm_nonneg (Y u k)
    have gN := fun k => norm_nonneg (fastNL r g y u k)
    have gS := fun k => norm_nonneg (slowNL r g y u k)
    have sA1 : Summable fun x : Mode × Mode =>
        tripT (metDM (r * u)) (X u) (Y u) (lapF (Y u)) x.1 x.2 := by
      have hb := (gradTri_bound gX gY (fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _))
        x1 x3 y1 y3 y4).1
      refine Summable.of_norm_bounded (hb.mul_left 8) fun x => ?_
      have := norm_tripT_bdd_lap (metDM_bdd (r * u)) (X u) (Y u) (Y u) x.1 x.2
      simpa only [gradTri, absSq_neg] using this
    have sA2 : Summable fun x : Mode × Mode =>
        tripT (m u) (slowNL r g y u) (Y u) (lapF (Y u)) x.1 x.2 := by
      have hb := (gradTri_bound_first gS gY gY hS2 y1 y3 y1 y3).1
      exact Summable.of_norm_bounded (hb.mul_left 8) fun x =>
        norm_tripT_gain_lap (hgain u) _ _ _ x.1 x.2
    have sA3 : Summable fun x : Mode × Mode =>
        tripT (m u) (X u) (fastNL r g y u) (lapF (Y u)) x.1 x.2 := by
      have hb := (gradTri_bound_mid gX gN gY x1 x3 hN2 y1 y3).1
      exact Summable.of_norm_bounded (hb.mul_left 8) fun x =>
        norm_tripT_gain_lap (hgain u) _ _ _ x.1 x.2
    have sA4 : Summable fun x : Mode × Mode =>
        tripT (m u) (X u) (Y u) (lapF (fastNL r g y u)) x.1 x.2 := by
      have hb := (gradTri_bound gX gY gN x1 x3 y1 y3 hN2).1
      exact Summable.of_norm_bounded (hb.mul_left 8) fun x =>
        norm_tripT_gain_lap (hgain u) _ _ _ x.1 x.2
    have hpt : ∀ x : Mode × Mode, tripDPath m m' X X' Y Y' Z Z' u x =
        tripT (metDM (r * u)) (X u) (Y u) (lapF (Y u)) x.1 x.2 +
        tripT (m u) (slowNL r g y u) (Y u) (lapF (Y u)) x.1 x.2 +
        tripT (m u) (X u) (fastNL r g y u) (lapF (Y u)) x.1 x.2 +
        tripT (m u) (X u) (Y u) (lapF (fastNL r g y u)) x.1 x.2 := by
      intro x
      simp only [tripDPath, tripD]
      have hZu : Z u = lapF (Y u) := rfl
      rw [hZu, hX'eq, hY'eq, hZ'eq, tripT_add_left, tripT_add_mid, tripT_add_right]
      have hc := tripT_met_heat_combine r (r * u) (X u) (Y u) (Y u) x.1 x.2
      simp only [hmdef, hm'def] at hc ⊢
      linear_combination hc
    have hsplit : (∑' x, tripDPath m m' X X' Y Y' Z Z' u x) =
        (∑' x : Mode × Mode, tripT (metDM (r * u)) (X u) (Y u) (lapF (Y u)) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (slowNL r g y u) (Y u) (lapF (Y u)) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (X u) (fastNL r g y u) (lapF (Y u)) x.1 x.2) +
        (∑' x : Mode × Mode, tripT (m u) (X u) (Y u) (lapF (fastNL r g y u)) x.1 x.2) := by
      rw [← sA1.tsum_add sA2, ← (sA1.add sA2).tsum_add sA3, ← ((sA1.add sA2).add sA3).tsum_add sA4]
      exact tsum_congr hpt
    rw [hsplit]
    simp only [Complex.add_re]
    have r1 : (∑' x : Mode × Mode, tripT (metDM (r * u)) (X u) (Y u) (lapF (Y u)) x.1 x.2).re =
        pair 1 (Y u) (Qm (metDM (r * u)) (X u) (Y u)) :=
      (pair_one_eq_re_tsum hrealY (fun k => inner_Qm (metDM_bdd (r * u)) hrealY.lapF
        (hadmX u hu).mz (hadmY u hu).mz k) sA1).symm
    have r2 : (∑' x : Mode × Mode, tripT (m u) (slowNL r g y u) (Y u) (lapF (Y u)) x.1 x.2).re =
        pair 1 (Y u) (X1op r (r * u) (slowNL r g y u) (Y u)) :=
      (pair_one_eq_re_tsum_gain (hgain u) hrealY hS2 y2 (Or.inr y3) sA2).symm
    have r3 : (∑' x : Mode × Mode, tripT (m u) (X u) (fastNL r g y u) (lapF (Y u)) x.1 x.2).re =
        pair 1 (Y u) (X1op r (r * u) (X u) (fastNL r g y u)) :=
      (pair_one_eq_re_tsum_gain (hgain u) hrealY x2 hN2 (Or.inl x3) sA3).symm
    have r4 : (∑' x : Mode × Mode, tripT (m u) (X u) (Y u) (lapF (fastNL r g y u)) x.1 x.2).re =
        pair 1 (fastNL r g y u) (X1op r (r * u) (X u) (Y u)) :=
      (pair_one_eq_re_tsum hNr (fun k => inner_Qm (metM_bdd r (r * u)) hNr.lapF
        (hadmX u hu).mz (hadmY u hu).mz k) sA4).symm
    rw [r1, r2, r3, r4]
    rfl
  -- integrability of the real part
  have hGre : IntervalIntegrable (fun u => (∑' x, tripDPath m m' X X' Y Y' Z Z' u x).re)
      volume s t := by
    refine hG.mono_fun ?_ ?_
    · exact Complex.continuous_re.comp_aestronglyMeasurable
        ((intervalIntegrable_iff.1 hG).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall fun u => by
        simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm _
  have hI : IntervalIntegrable (metricRHS r g y) volume s t := by
    refine (hGre.const_mul 4).congr fun u hu => hre u ?_
    rw [uIoc_of_le hst] at hu
    exact Ioc_subset_Icc_self hu
  refine ⟨hI, ?_⟩
  have hR := congrArg Complex.re key
  rw [Complex.sub_re] at hR
  have hR4 : metricCorr r g y t - metricCorr r g y s =
      4 * (∫ u in s..t, ∑' x, tripDPath m m' X X' Y Y' Z Z' u x).re := by
    rw [← hL t ⟨hst, le_rfl⟩, ← hL s ⟨le_rfl, hst⟩, ← hR]
    ring
  rw [hR4, ← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hG,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hst] at hu
  simp only [Complex.reCLM_apply]
  exact hre u hu

/-! ### G. The energy identity -/

/-- Two multipliers agreeing wherever both inputs are nonzero give the same `Q^♯`. -/
lemma Qm_congr_support {m₁ m₂ : Mult} {X Y : Field}
    (h : ∀ a b c p q, X p ≠ 0 → Y q ≠ 0 → m₁ a b c p q = m₂ a b c p q) :
    Qm m₁ X Y = Qm m₂ X Y := by
  funext k
  unfold Qm
  refine tsum_congr fun p => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  by_cases hX : X p = 0
  · simp [hX, hel_zero_right, vert_zero_left]
  · by_cases hY : Y (k - p) = 0
    · simp [hY, hel_zero_right, vert_zero_right]
    · rw [h a b c p (k - p) hX hY]

/-- The frozen `X₁` derivative is the slow–fast nonresonant convection: for slow `S` and fast `F`,
`Q^♯_{metDM}(S,F) = Q_nr(S,F)`. -/
lemma Qm_metDM_eq_Qnr (τ : ℝ) {S F : Field} (hS : PiS S = S) (hF : PiF F = F) :
    Qm (metDM τ) S F = Qnr τ S F := by
  refine Qm_congr_support fun a b c p q hSp hFq => ?_
  have hp : p 2 = 0 := by
    by_contra hp
    exact hSp (slow_zero hS hp)
  have hq : q 2 ≠ 0 := by
    intro hq
    exact hFq (fast_zero hF hq)
  unfold metDM nonresM SlowFast
  by_cases hΦ : Phi a b c p q = 0
  · simp [hp, hq, hΦ]
  · simp [hp, hq, hΦ]

/-- **The slow–fast frozen term is the full slow–fast convection**: by catalytic neutrality the
resonant slow–fast part pairs to zero at `σ = 1` (`cat_neutral`), so
`⟨AF, Q^♯_{metDM}(S,F)⟩ = ⟨AF, Q_τ(S,F)⟩`. -/
theorem pair_metDM_eq (τ : ℝ) {S F : Field} (hS : Adm 2 S) (hF : Adm 2 F) (hS' : PiS S = S)
    (hF' : PiF F = F) : pair 1 F (Qm (metDM τ) S F) = pair 1 F (Qphase τ S F) := by
  rw [Qm_metDM_eq_Qnr τ hS' hF', Qphase_eq_Qres_add_Qnr τ hS.mz hF.mz]
  have hF1 : InH (1 + 1) F := hF.inH.mono (by norm_num)
  have hQr : InH (1 - 1) (Qres S F) :=
    ((hnorm_Qm_zero_le resM_bdd hS.mz hF.mz).1).mono (by norm_num)
  have hQn : InH (1 - 1) (Qnr τ S F) :=
    ((hnorm_Qm_zero_le (nonresM_bdd τ) hS.mz hF.mz).1).mono (by norm_num)
  rw [pair_add hF1 hQr hQn, cat_neutral hS hF hS' hF' (Or.inr rfl), zero_add]

/-- The `H¹` split of the convection tested on the fast part (the `σ = 1` version of
`pair_fast_Qphase`'s `hsplit`): `⟨AF, Q_τ(x,x)⟩ = 2⟨AF, Q_τ(S,F)⟩ + ⟨AF, Q_τ(F,F)⟩`
(`⟨AF, Q(S,S)⟩ = 0`: a slow output against a fast test). -/
theorem pair_one_Qphase_split (τ : ℝ) {x : Field} (hx : Adm 2 x) :
    pair 1 (PiF x) (Qphase τ x x) =
      2 * pair 1 (PiF x) (Qphase τ (PiS x) (PiF x)) +
        pair 1 (PiF x) (Qphase τ (PiF x) (PiF x)) := by
  set S := PiS x with hSdef
  set F := PiF x with hFdef
  have hS : Adm 2 S := hx.PiS
  have hF : Adm 2 F := hx.PiF
  have hS' : PiS S = S := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hSdef, PiS, hk]
  have hF' : PiF F = F := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hFdef, PiF, hk]
  have hM := majorized_Qphase τ
  have hx' : x = S + F := (PiS_add_PiF x).symm
  have hsum : MZ 2 (S + F) := by rw [← hx']; exact hx.mz
  have hcomm : Qphase τ F S = Qphase τ S F := Qm_comm_of_symm (phaseM_symm τ) hF.mz hS.mz
  have hsplit : Qphase τ x x = Qphase τ S S + Qphase τ S F + Qphase τ S F + Qphase τ F F := by
    conv_lhs => rw [hx']
    rw [hM.add_left 0 _ _ _ hS.mz hF.mz hsum, hM.add_right 0 _ _ _ hS.mz hS.mz hF.mz,
      hM.add_right 0 _ _ _ hF.mz hS.mz hF.mz, hcomm]
    abel
  have hQ : ∀ {u v : Field}, Adm 2 u → Adm 2 v → InH (1 - 1) (Qphase τ u v) := fun hu hv =>
    ((hnorm_Qm_zero_le (phaseM_bdd τ) hu.mz hv.mz).1).mono (by norm_num)
  have hF1 : InH (1 + 1) F := hF.inH.mono (by norm_num)
  rw [hsplit, pair_add hF1 ((hQ hS hS).add (hQ hS hF) |>.add (hQ hS hF)) (hQ hF hF),
    pair_add hF1 ((hQ hS hS).add (hQ hS hF)) (hQ hS hF), pair_add hF1 (hQ hS hS) (hQ hS hF),
    pair_eq_zero_of_disjoint 1 (fun k => by
      by_cases hk : k 2 = 0
      · exact Or.inl (fast_zero hF' hk)
      · exact Or.inr (Qphase_slow_slow τ hS' hk))]
  ring

/-- **The right-hand side of the energy identity** (the integrand of `E' + b_F²`): the resonant
slot `−⟨AF, Q_res(F,F)⟩` (paid by `ResH1`), the force `−⟨AF, H_ψ⟩`, the three uncancelled `X₁`
insertions (slow source, fast source, output), minus the cubic heat `E_heat`, plus the native
differential `DE⁰[fastNL]`. -/
def h1RHS (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -pair 1 (PiF (actual r g y u)) (Qres (PiF (actual r g y u)) (PiF (actual r g y u))) -
    pair 1 (PiF (actual r g y u)) (Hpsi r g y u) +
    2 * (pair 1 (PiF (actual r g y u)) (X1op r (r * u) (slowNL r g y u) (PiF (actual r g y u))) +
      pair 1 (PiF (actual r g y u)) (X1op r (r * u) (PiS (actual r g y u)) (fastNL r g y u)) +
      pair 1 (fastNL r g y u) (X1op r (r * u) (PiS (actual r g y u)) (PiF (actual r g y u)))) -
    cubicHeat r (r * u) (PiF (actual r g y u)) +
    cubicD 1 (-1) r (r * u) (PiF (actual r g y u)) (fastNL r g y u)

/-- The `H¹` law of the fast part (TeX: `½(a_F²)' + b_F² = −⟨AF, Π_F Q_τ(y,y)⟩`, integrated):
`½a_F(t)² − ½a_F(s)² + ∫ b_F² = ∫ ⟨AF, fastNL⟩`. -/
theorem fast_h1_law (h : ActualSol μ φ r g y Ty) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (fun u => pair 1 (PiF (actual r g y u)) (fastNL r g y u)) volume s t ∧
      1 / 2 * fastNorm 1 r g y t ^ 2 - 1 / 2 * fastNorm 1 r g y s ^ 2 +
        (∫ u in s..t, fastNorm 2 r g y u ^ 2) =
        ∫ u in s..t, pair 1 (PiF (actual r g y u)) (fastNL r g y u) := by
  have hP := heatPair_fast h (σ := 1) (Or.inr rfl) (hs.trans hst) ht
  have hid := hP.energy_identity hs hst le_rfl
  rw [show (1 : ℝ) + 1 = 2 by norm_num] at hid
  refine ⟨(hP.mono hs le_rfl).intervalIntegrable_pair hst, ?_⟩
  unfold fastNorm fastNL
  linarith

/-- The pointwise bookkeeping of the integrand: `⟨AF, fastNL⟩ + ½ metricRHS + cubicRHS = h1RHS`,
through the split `pair_one_Qphase_split`, the frozen-term identity `pair_metDM_eq` and the
resonant split `Q_τ = Q_res + Q_nr` (the slow–fast and the nonresonant fast–fast terms cancel). -/
theorem h1RHS_eq (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    pair 1 (PiF (actual r g y u)) (fastNL r g y u) + 1 / 2 * metricRHS r g y u +
      cubicRHS r g y u = h1RHS r g y u := by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  set F := PiF (actual r g y u) with hFdef
  set S := PiS (actual r g y u) with hSdef
  have hF : Adm 2 F := hx.PiF
  have hS : Adm 2 S := hx.PiS
  have hF' : PiF F = F := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hFdef, PiF, hk]
  have hS' : PiS S = S := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hSdef, PiS, hk]
  have hF1 : InH (1 + 1) F := hF.inH.mono (by norm_num)
  have hQ : ∀ {v w : Field}, Adm 2 v → Adm 2 w → InH (1 - 1) (Qphase (r * u) v w) := fun hv hw =>
    ((hnorm_Qm_zero_le (phaseM_bdd _) hv.mz hw.mz).1).mono (by norm_num)
  have hH : InH (1 - 1) (Hpsi r g y u) :=
    ((hQ hy hy).sub (hQ hx hx))
  -- `⟨AF, fastNL⟩ = −⟨AF, Q(x,x)⟩ − ⟨AF, H_ψ⟩`
  have e1 : pair 1 F (fastNL r g y u) = -(pair 1 F (Qphase (r * u) (actual r g y u) (actual r g y u))
      + pair 1 F (Hpsi r g y u)) := by
    have e : Qphase (r * u) (y u) (y u) =
        Qphase (r * u) (actual r g y u) (actual r g y u) + Hpsi r g y u := by
      simp [Hpsi]
    unfold fastNL
    rw [pair_neg_right, pair_PiF_right 1 hF', e, pair_add hF1 (hQ hx hx) hH]
  -- the split of `⟨AF, Q(x,x)⟩`
  have e2 := pair_one_Qphase_split (r * u) hx
  -- the frozen metric term
  have e3 := pair_metDM_eq (r * u) hS hF hS' hF'
  -- the resonant split of `⟨AF, Q(F,F)⟩`
  have hQr : InH (1 - 1) (Qres F F) := ((hnorm_Qm_zero_le resM_bdd hF.mz hF.mz).1).mono (by norm_num)
  have hQn : InH (1 - 1) (Qnr (r * u) F F) :=
    ((hnorm_Qm_zero_le (nonresM_bdd _) hF.mz hF.mz).1).mono (by norm_num)
  have e4 : pair 1 F (Qphase (r * u) F F) = pair 1 F (Qres F F) + pair 1 F (Qnr (r * u) F F) := by
    rw [Qphase_eq_Qres_add_Qnr _ hF.mz hF.mz, pair_add hF1 hQr hQn]
  unfold metricRHS cubicRHS h1RHS
  rw [← hFdef, ← hSdef] at *
  rw [e1, e3] at *
  linarith [e2, e4]

/-- **E5, the energy identity** (the E4.4-type identity for the corrected `H¹` energy): along the
actual solution, on `[s,t]` inside the lifespan,
`E(t) − E(s) + ∫ₛᵗ b_F² = ∫ₛᵗ h1RHS`, with `h1RHS` integrable.  The slow–fast term of the `H¹` law
is cancelled by the frozen derivative of `X₁` (`pair_metDM_eq`: exactly, the resonant slow–fast
part being zero by catalytic neutrality) and the nonresonant fast–fast term by the frozen
derivative of `E⁰` (`tripT_corr_heat_combine`); what remains is `h1RHS`. -/
theorem h1Energy_identity (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (h1RHS r g y) volume s t ∧
      h1Energy r g y t - h1Energy r g y s + (∫ u in s..t, fastNorm 2 r g y u ^ 2) =
        ∫ u in s..t, h1RHS r g y u := by
  obtain ⟨hI1, hE1⟩ := fast_h1_law h hs hst ht
  obtain ⟨hI2, hE2⟩ := metricCorr_identity h hr hs hst ht
  obtain ⟨hI3, hE3⟩ := cubicCorr_identity h hr hs hst ht
  have hmem : ∀ u ∈ Icc s t, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hs.trans hu.1, lt_lifespan hu.2 ht⟩
  have hI : IntervalIntegrable (h1RHS r g y) volume s t := by
    refine ((hI1.add (hI2.const_mul (1 / 2))).add hI3).congr fun u hu => ?_
    rw [uIoc_of_le hst] at hu
    have hu' := hmem u (Ioc_subset_Icc_self hu)
    exact h1RHS_eq h hu'.1 hu'.2
  refine ⟨hI, ?_⟩
  have e : ∫ u in s..t, h1RHS r g y u = (∫ u in s..t, pair 1 (PiF (actual r g y u)) (fastNL r g y u))
      + 1 / 2 * (∫ u in s..t, metricRHS r g y u) + ∫ u in s..t, cubicRHS r g y u := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hI1
      (hI2.const_mul _), ← intervalIntegral.integral_add (hI1.add (hI2.const_mul _)) hI3]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hst] at hu
    exact (h1RHS_eq h (hmem u hu).1 (hmem u hu).2).symm
  rw [e]
  unfold h1Energy
  linarith

end Quant

end OVNS

end
