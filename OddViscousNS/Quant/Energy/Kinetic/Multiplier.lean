import OddViscousNS.Quant.Energy.Kinetic.Derivative

/-!
# E4.4: the kinetic multiplier along the solution and the triple sums

* B'. `summable_tri_first/second/third`: `∑_{(p,q)} a_p b_q c_{−(p+q)} ≤ ‖·‖_{ℓ¹}‖·‖_{ℓ²}‖·‖_{ℓ²}`
  with the `ℓ¹` factor in any of the three slots (`triple_bound` of `Trilinear.lean`
  reindexed) — the summability controls of the multilinear correction lemma.
* E. The kinetic multiplier along the solution: `hasDerivAt_kinM`,
  `∂_t [e^{irtΦ}/(irΦ)] = e^{irtΦ}` on the nonresonant slow-output triads (TeX (N4): the
  frozen-amplitude derivative of `N(F,F)` is `Π_S Q_τ(F,F)`; the resonant slow-output triads carry
  a vanishing vertex, `tripT_kinDM_eq`), the summability of the kinetic triad family
  (`summable_tripT_kinM`) and the identification of its real part with the pairings
  (`pair_kinN_eq_re_tsum`, `pair_Qphase_eq_re_tsum`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS

/-! ### B'. Triple sums with one `ℓ¹` factor -/

/-- `∑_{(p,q)} a_p c_q b_{−(p+q)} ≤ ‖b‖_{ℓ¹} ‖a‖_{ℓ²} ‖c‖_{ℓ²}` (the `ℓ¹` factor in the output
slot; `triple_bound` reindexed by `rho.symm`). -/
lemma summable_tri_third {a c b : Mode → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hc : ∀ k, 0 ≤ c k) (ha2 : Summable fun k => a k ^ 2) (hc2 : Summable fun k => c k ^ 2)
    (hb1 : Summable b) :
    Summable (fun x : Mode × Mode => a x.1 * c x.2 * b (-(x.1 + x.2))) ∧
      ∑' x : Mode × Mode, a x.1 * c x.2 * b (-(x.1 + x.2)) ≤
        (∑' k, b k) * (Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, c k ^ 2)) := by
  have hcn : Summable fun k => c (-k) ^ 2 := (Equiv.neg Mode).summable_iff.mpr hc2
  have hT := triple_bound (b := b) (a := a) (c := fun k => c (-k)) hb ha (fun k => hc _) hb1 ha2
    hcn
  have e : ∀ x : Mode × Mode, a x.1 * c x.2 * b (-(x.1 + x.2)) =
      (fun x : Mode × Mode => b x.1 * a x.2 * c (-(x.1 + x.2))) (rho.symm x) := by
    intro x
    simp only [rho, Equiv.coe_fn_symm_mk]
    have : -(-(x.1 + x.2) + x.1) = x.2 := by abel
    rw [this]
    ring
  have hs : Summable (fun x : Mode × Mode => a x.1 * c x.2 * b (-(x.1 + x.2))) :=
    (summable_congr e).mpr (rho.symm.summable_iff.mpr hT.1)
  refine ⟨hs, ?_⟩
  rw [tsum_congr e, rho.symm.tsum_eq (fun x : Mode × Mode => b x.1 * a x.2 * c (-(x.1 + x.2)))]
  have hcc : ∑' k, c (-k) ^ 2 = ∑' k, c k ^ 2 := (Equiv.neg Mode).tsum_eq fun k => c k ^ 2
  rw [hcc] at hT
  exact hT.2

/-- The `ℓ¹` factor in the second slot (`triple_bound` reindexed by `prodComm`). -/
lemma summable_tri_second {a c b : Mode → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hc : ∀ k, 0 ≤ c k) (ha2 : Summable fun k => a k ^ 2) (hc2 : Summable fun k => c k ^ 2)
    (hb1 : Summable b) :
    Summable (fun x : Mode × Mode => a x.1 * b x.2 * c (-(x.1 + x.2))) ∧
      ∑' x : Mode × Mode, a x.1 * b x.2 * c (-(x.1 + x.2)) ≤
        (∑' k, b k) * (Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, c k ^ 2)) := by
  have hcn : Summable fun k => c (-k) ^ 2 := (Equiv.neg Mode).summable_iff.mpr hc2
  have hT := triple_bound (b := b) (a := a) (c := fun k => c (-k)) hb ha (fun k => hc _) hb1 ha2
    hcn
  have e : ∀ x : Mode × Mode, a x.1 * b x.2 * c (-(x.1 + x.2)) =
      (fun x : Mode × Mode => b x.1 * a x.2 * c (-(x.1 + x.2))) (Equiv.prodComm Mode Mode x) := by
    intro x
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm x.2 x.1]
    ring
  have hs : Summable (fun x : Mode × Mode => a x.1 * b x.2 * c (-(x.1 + x.2))) :=
    (summable_congr e).mpr ((Equiv.prodComm Mode Mode).summable_iff.mpr hT.1)
  refine ⟨hs, ?_⟩
  rw [tsum_congr e,
    (Equiv.prodComm Mode Mode).tsum_eq (fun x : Mode × Mode => b x.1 * a x.2 * c (-(x.1 + x.2)))]
  have hcc : ∑' k, c (-k) ^ 2 = ∑' k, c k ^ 2 := (Equiv.neg Mode).tsum_eq fun k => c k ^ 2
  rw [hcc] at hT
  exact hT.2

/-- The `ℓ¹` factor in the first slot (`triple_bound` with `c ↦ c(−·)`). -/
lemma summable_tri_first {b a c : Mode → ℝ} (hb : ∀ k, 0 ≤ b k) (ha : ∀ k, 0 ≤ a k)
    (hc : ∀ k, 0 ≤ c k) (hb1 : Summable b) (ha2 : Summable fun k => a k ^ 2)
    (hc2 : Summable fun k => c k ^ 2) :
    Summable (fun x : Mode × Mode => b x.1 * a x.2 * c (-(x.1 + x.2))) ∧
      ∑' x : Mode × Mode, b x.1 * a x.2 * c (-(x.1 + x.2)) ≤
        (∑' k, b k) * (Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, c k ^ 2)) := by
  have hcn : Summable fun k => c (-k) ^ 2 := (Equiv.neg Mode).summable_iff.mpr hc2
  have hT := triple_bound (b := b) (a := a) (c := fun k => c (-k)) hb ha (fun k => hc _) hb1 ha2
    hcn
  have hcc : ∑' k, c (-k) ^ 2 = ∑' k, c k ^ 2 := (Equiv.neg Mode).tsum_eq fun k => c k ^ 2
  rw [hcc] at hT
  exact hT

/-! ### E. The kinetic identities -/

open Classical in
/-- The derivative multiplier `∂_t [kinM r (r t)] = 𝟏_{(p+q)₃ = 0, p₃ ≠ 0, Φ ≠ 0} e^{irtΦ}`: the
nonresonant slow-output phase (TeX (N4)). -/
def kinDM (τ : ℝ) : Mult := fun a b c p q =>
  if (p + q) 2 = 0 ∧ p 2 ≠ 0 ∧ Phi a b c p q ≠ 0 then phaseM τ a b c p q else 0

lemma hasDerivAt_phase_div (r Φ : ℝ) (hΦ : Φ ≠ 0) (hr : r ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * ((r * t) * Φ : ℝ)) /
      (Complex.I * (r * Φ : ℝ))) (Complex.exp (Complex.I * ((r * t) * Φ : ℝ))) t := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.I * (((r * t) * Φ : ℝ) : ℂ))
      (Complex.I * (r * Φ : ℝ)) t := by
    have h0 := (((hasDerivAt_id t).const_mul r).mul_const Φ).ofReal_comp
    simpa [mul_comm, mul_assoc, mul_left_comm] using h0.const_mul Complex.I
  have h2 := (h1.cexp).div_const (Complex.I * (r * Φ : ℝ))
  refine h2.congr_deriv ?_
  have hne : ((r * Φ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero hr hΦ
  field_simp

variable {r : ℝ}

/-- **TeX (N4) at the level of multipliers**: `∂_t [e^{irtΦ}/(irΦ)] = e^{irtΦ}` on the nonresonant
slow-output triads with fast inputs (and `0 = 0` elsewhere, including the resonant ones). -/
theorem hasDerivAt_kinM (hr : r ≠ 0) (a b c : Sgn) (p q : Mode) (t : ℝ) :
    HasDerivAt (fun t => kinM r (r * t) a b c p q) (kinDM (r * t) a b c p q) t := by
  by_cases h : (p + q) 2 = 0 ∧ p 2 ≠ 0
  · by_cases hΦ : Phi a b c p q = 0
    · have e : (fun t => kinM r (r * t) a b c p q) = fun _ => 0 := funext fun t => by
        simp [kinM, h, hΦ]
      have e2 : kinDM (r * t) a b c p q = 0 := by simp [kinDM, hΦ]
      rw [e, e2]
      exact hasDerivAt_const _ _
    · have h' : (p + q) 2 = 0 ∧ p 2 ≠ 0 ∧ Phi a b c p q ≠ 0 := ⟨h.1, h.2, hΦ⟩
      have e : (fun t => kinM r (r * t) a b c p q) = fun t =>
          Complex.exp (Complex.I * ((r * t) * Phi a b c p q : ℝ)) /
            (Complex.I * (r * Phi a b c p q : ℝ)) :=
        funext fun t => by simp only [kinM, ite_eq_left h, phaseM]
      have e2 : kinDM (r * t) a b c p q =
          Complex.exp (Complex.I * ((r * t) * Phi a b c p q : ℝ)) := by
        simp only [kinDM, ite_eq_left h', phaseM]
      rw [e, e2]
      exact hasDerivAt_phase_div r _ hΦ hr t
  · have h' : ¬ ((p + q) 2 = 0 ∧ p 2 ≠ 0 ∧ Phi a b c p q ≠ 0) := fun h'' => h ⟨h''.1, h''.2.1⟩
    have e : (fun t => kinM r (r * t) a b c p q) = fun _ => 0 := funext fun t => by
      simp only [kinM, ite_eq_right h]
    have e2 : kinDM (r * t) a b c p q = 0 := by simp only [kinDM, ite_eq_right h']
    rw [e, e2]
    exact hasDerivAt_const _ _

lemma continuous_kinDM (a b c : Sgn) (p q : Mode) :
    Continuous fun t : ℝ => kinDM (r * t) a b c p q := by
  by_cases h : (p + q) 2 = 0 ∧ p 2 ≠ 0 ∧ Phi a b c p q ≠ 0
  · simp only [kinDM, ite_eq_left h, phaseM]
    fun_prop
  · simp only [kinDM, ite_eq_right h]
    exact continuous_const

/-- The slow-output resonant null (TeX: "use the slow-output resonant null"): tested on a slow
`S` with fast inputs `F`, the derivative multiplier acts as the full phase `e^{iτΦ}` — the
excluded triads carry a vanishing summand (`vert_hel_zero`, `res_null`; sector vanishing). -/
lemma tripT_kinDM_eq (τ : ℝ) {F S : Field} (hF : PiF F = F) (hS : PiS S = S) (p q : Mode) :
    tripT (kinDM τ) F F S p q = tripT (phaseM τ) F F S p q := by
  unfold tripT
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  by_cases h : (p + q) 2 = 0 ∧ p 2 ≠ 0 ∧ Phi a b c p q ≠ 0
  · simp only [kinDM, ite_eq_left h]
  · simp only [kinDM, ite_eq_right h, zero_mul]
    symm
    by_cases h1 : (p + q) 2 = 0
    · by_cases h2 : p 2 = 0
      · rw [fast_zero hF h2, hel_zero_right, tau_zero_left, mul_zero]
      · have hΦ : Phi a b c p q = 0 := by
          by_contra h3
          exact h ⟨h1, h2, h3⟩
        rw [← bd_hel_vert, vert_hel_zero _ _ (res_null h1 h2 hΦ), bd_zero_right, mul_zero]
    · have h1' : (-(p + q)) 2 ≠ 0 := by rw [Pi.neg_apply, neg_ne_zero]; exact h1
      rw [slow_zero hS h1', hel_zero_right, tau_zero_right, mul_zero]

lemma tripT_zero_of_add_eq_zero (m : Mult) (X Y Z : Field) {p q : Mode} (h : p + q = 0) :
    tripT m X Y Z p q = 0 := by
  simp [tripT, h, hel_zero_mode, tau_zero_right]

/-- The weighted triad family of `⟨Z, N(X,Y)⟩` is summable when `X ∈ ℓ¹` and `Y, Z ∈ ℓ²`. -/
lemma summable_tripT_kinM (hr : r ≠ 0) (τ : ℝ) {X Y Z : Field} (hX1 : Summable fun k => ‖X k‖)
    (hY2 : Summable fun k => ‖Y k‖ ^ 2) (hZ2 : Summable fun k => ‖Z k‖ ^ 2) :
    Summable fun x : Mode × Mode =>
      (sobWeight 0 (x.1 + x.2) : ℂ) * tripT (kinM r τ) X Y Z x.1 x.2 := by
  have hb := (summable_tri_first (b := fun k => ‖X k‖) (a := fun k => ‖Y k‖)
    (c := fun k => ‖Z k‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hX1 hY2 hZ2).1
  refine Summable.of_norm_bounded (hb.mul_left (2 / |r|)) fun x => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sobWeight_nonneg _ _)]
  have h1 : sobWeight 0 (x.1 + x.2) ≤ 1 := by
    unfold sobWeight
    split_ifs <;> simp
  calc sobWeight 0 (x.1 + x.2) * ‖tripT (kinM r τ) X Y Z x.1 x.2‖
      ≤ 1 * ‖tripT (kinM r τ) X Y Z x.1 x.2‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ 2 / |r| * (‖X x.1‖ * ‖Y x.2‖ * ‖Z (-(x.1 + x.2))‖) := by
        rw [one_mul]
        exact norm_tripT_kinM_le hr X Y Z x.1 x.2

/-- Same with the `ℓ¹` factor in the second slot (`X ∈ ℓ²`, `Y ∈ ℓ¹`). -/
lemma summable_tripT_kinM' (hr : r ≠ 0) (τ : ℝ) {X Y Z : Field}
    (hX2 : Summable fun k => ‖X k‖ ^ 2) (hY1 : Summable fun k => ‖Y k‖)
    (hZ2 : Summable fun k => ‖Z k‖ ^ 2) :
    Summable fun x : Mode × Mode =>
      (sobWeight 0 (x.1 + x.2) : ℂ) * tripT (kinM r τ) X Y Z x.1 x.2 := by
  have hb := (summable_tri_second (a := fun k => ‖X k‖) (b := fun k => ‖Y k‖)
    (c := fun k => ‖Z k‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hX2 hZ2 hY1).1
  refine Summable.of_norm_bounded (hb.mul_left (2 / |r|)) fun x => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sobWeight_nonneg _ _)]
  have h1 : sobWeight 0 (x.1 + x.2) ≤ 1 := by
    unfold sobWeight
    split_ifs <;> simp
  calc sobWeight 0 (x.1 + x.2) * ‖tripT (kinM r τ) X Y Z x.1 x.2‖
      ≤ 1 * ‖tripT (kinM r τ) X Y Z x.1 x.2‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ 2 / |r| * (‖X x.1‖ * ‖Y x.2‖ * ‖Z (-(x.1 + x.2))‖) := by
        rw [one_mul]
        exact norm_tripT_kinM_le hr X Y Z x.1 x.2

/-- Dropping the trivial `|k|⁰` weight from a triad sum. -/
lemma tsum_weight_tripT (m : Mult) (X Y Z : Field) :
    ∑' x : Mode × Mode, (sobWeight 0 (x.1 + x.2) : ℂ) * tripT m X Y Z x.1 x.2 =
      ∑' x : Mode × Mode, tripT m X Y Z x.1 x.2 :=
  tsum_congr fun _ => weight_zero_mul (tripT_zero_of_add_eq_zero m X Y Z)

/-- `⟨Z, N(X,Y)⟩ = Re ∑_{(p,q)} tripT (kinM) X Y Z` for real `Z`. -/
lemma pair_kinN_eq_re_tsum (hr : r ≠ 0) (τ : ℝ) {X Y Z : Field} (hZ : IsReal Z)
    (hX2 : Summable fun k => ‖X k‖ ^ 2) (hY2 : Summable fun k => ‖Y k‖ ^ 2)
    (hsum : Summable fun x : Mode × Mode =>
      (sobWeight 0 (x.1 + x.2) : ℂ) * tripT (kinM r τ) X Y Z x.1 x.2) :
    pair 0 Z (kinN r τ X Y) = (∑' x : Mode × Mode, tripT (kinM r τ) X Y Z x.1 x.2).re := by
  have hW := inner_kinN (τ := τ) hr hZ hX2 hY2
  have e := @pair_eq_tsum 0 Z (kinN r τ X Y) (tripT (kinM r τ) X Y Z) hW hsum
  rw [tsum_weight_tripT] at e
  exact e

/-- `⟨Z, Q_τ(X,Y)⟩ = Re ∑_{(p,q)} tripT (phaseM τ) X Y Z` for real `Z` and `H²` inputs. -/
lemma pair_Qphase_eq_re_tsum (τ : ℝ) {X Y Z : Field} (hZ : IsReal Z) (hX : MZ 2 X)
    (hY : MZ 2 Y) (hZ2 : MZ 2 Z) :
    pair 0 Z (Qphase τ X Y) = (∑' x : Mode × Mode, tripT (phaseM τ) X Y Z x.1 x.2).re := by
  have e := pair_eq_tsum (tripT (phaseM τ) X Y Z) (inner_Qm (phaseM_bdd τ) hZ hX hY)
    (summable_tripT (phaseM_bdd τ) (σ := 0) (by norm_num) hX hY hZ2)
  rw [tsum_weight_tripT] at e
  exact e

end OVNS

end
