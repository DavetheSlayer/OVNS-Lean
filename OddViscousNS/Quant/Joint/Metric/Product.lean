import OddViscousNS.Quant.Joint.Kinetic.GN
import OddViscousNS.Quant.Energy.H1.Defs

/-!
# The physical slow product in `H¹` (step J5, pilot)

Body 30 (LOCAL390): `‖B_slow(U, U)‖₁ ≤ C M b`, `M = ‖U‖_∞`, `b = ‖U‖₂`: the source `f₁ = ‖h‖₁` of
the differentiated groups, whence the `M_∞` of row 3.  The proof is Body 30's: Leibniz puts one
derivative on each factor of `(U·∇)U`; `(∂U·∇)U` is `L⁴ × L⁴`, `‖∂U‖₄² ≲ M b` by
Gagliardo–Nirenberg, and `(U·∇)∂U` is `L^∞ × L²`.  It is built on `Joint/Kinetic/GN.lean`: the only
new analytic step is `cv_gn_gn`, Gagliardo–Nirenberg on both factors.  It holds at fixed time on
`H²`, and needs no heat regularization (Body 30 approximates by heat; Fatou in the truncation is
simpler).
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.GN

private lemma sqrt_le_of_sq' {X b : ℝ} (hb : 0 ≤ b) (h : X ≤ b ^ 2) : Real.sqrt X ≤ b := by
  rw [← Real.sqrt_sq hb]
  exact Real.sqrt_le_sqrt h

/-- **Gagliardo–Nirenberg on both factors**: `‖∂_i u ∂_j v‖₂² ≤ ‖∂_i u‖₄² ‖∂_j v‖₄²`, in the Fourier
form, with `‖∂_i u‖₄² ≤ 3 M ‖∂_i² u‖₂`. -/
theorem cv_gn_gn (i j : Fin 3) {u v : Mode → ℂ} (hu : Summable fun k => ‖u k‖)
    (hv : Summable fun k => ‖v k‖) (hu1 : Summable fun k => ‖dC i u k‖ ^ 2)
    (hv1 : Summable fun k => ‖dC j v k‖ ^ 2) (hu2 : Summable fun k => ‖dC i (dC i u) k‖ ^ 2)
    (hv2 : Summable fun k => ‖dC j (dC j v) k‖ ^ 2) {M : ℝ}
    (hMu : ∀ x, ‖∑' k, u k * mFourier k x‖ ≤ M) (hMv : ∀ x, ‖∑' k, v k * mFourier k x‖ ≤ M) :
    Summable (fun m => ‖cv (dC i u) (dC j v) m‖ ^ 2) ∧
      ∑' m, ‖cv (dC i u) (dC j v) m‖ ^ 2 ≤
        (3 * M * Real.sqrt (∑' k, ‖dC i (dC i u) k‖ ^ 2)) *
          (3 * M * Real.sqrt (∑' k, ‖dC j (dC j v) k‖ ^ 2)) := by
  set Wu := ∑' k, ‖dC i (dC i u) k‖ ^ 2 with hWu
  set Wv := ∑' k, ‖dC j (dC j v) k‖ ^ 2 with hWv
  have hWu0 : 0 ≤ Wu := tsum_nonneg fun _ => by positivity
  have hWv0 : 0 ≤ Wv := tsum_nonneg fun _ => by positivity
  have hB : Tendsto (fun A => (3 * (M + tailN u A) * Real.sqrt Wu) *
      (3 * (M + tailN v A) * Real.sqrt Wv)) atTop
      (𝓝 ((3 * M * Real.sqrt Wu) * (3 * M * Real.sqrt Wv))) := by
    have h1 := tendsto_tailN hu
    have h2 := tendsto_tailN hv
    have : Tendsto (fun A => (3 * (M + tailN u A) * Real.sqrt Wu) *
        (3 * (M + tailN v A) * Real.sqrt Wv)) atTop
        (𝓝 ((3 * (M + 0) * Real.sqrt Wu) * (3 * (M + 0) * Real.sqrt Wv))) :=
      (((tendsto_const_nhds.add h1).const_mul 3).mul_const _).mul
        (((tendsto_const_nhds.add h2).const_mul 3).mul_const _)
    simpa using this
  refine cv_fatou (summable_mul_of_l2 hu1 hv1) (fun A => ?_) hB
  have hbu := norm_tp_le hu hMu A
  have hbv := norm_tp_le hv hMv A
  have hMu0 : 0 ≤ M + tailN u A := (norm_nonneg _).trans (hbu 0)
  have hMv0 : 0 ≤ M + tailN v A := (norm_nonneg _).trans (hbv 0)
  have h1 := integral_mul_le_sqrt (f := fun x => ‖tp A (dC i u) x‖ ^ 2)
    (g := fun x => ‖tp A (dC j v) x‖ ^ 2) ((tp A (dC i u)).continuous.norm.pow 2)
    ((tp A (dC j v)).continuous.norm.pow 2) (fun _ => by positivity) (fun _ => by positivity)
  have e4 : ∀ c : C(T3, ℂ), ∫ x, (‖c x‖ ^ 2) ^ 2 ∂μT = ∫ x, ‖c x‖ ^ 4 ∂μT := fun c =>
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  simp only [e4] at h1
  refine h1.trans ?_
  have key : ∀ (w : Mode → ℂ) (l : Fin 3) (K W : ℝ), 0 ≤ K → 0 ≤ W →
      (∀ x, ‖tp A w x‖ ≤ K) → (Summable fun k => ‖dC l (dC l w) k‖ ^ 2) →
      ∑' k, ‖dC l (dC l w) k‖ ^ 2 = W →
      Real.sqrt (∫ x, ‖tp A (dC l w) x‖ ^ 4 ∂μT) ≤ 3 * K * Real.sqrt W := by
    intro w l K W hK hW hbd hs he
    refine sqrt_le_of_sq' (by positivity) ?_
    have h4 := gn_tp A w l hbd
    rw [integral_norm_sq_tp] at h4
    refine h4.trans ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt hW]
    have := sum_le_tsum_sq hs A
    rw [he] at this
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 9 * K ^ 2)]
  exact mul_le_mul (key u i _ _ hMu0 hWu0 hbu hu2 rfl) (key v j _ _ hMv0 hWv0 hbv hv2 rfl)
    (Real.sqrt_nonneg _) (by positivity)

/-- **Leibniz on coefficients**: `∂_i (a ∗ b) = ∂_i a ∗ b + a ∗ ∂_i b`. -/
lemma dC_cv (i : Fin 3) {a b : Mode → ℂ} {k : Mode}
    (h1 : Summable fun p => ‖dC i a p‖ * ‖b (k - p)‖)
    (h2 : Summable fun p => ‖a p‖ * ‖dC i b (k - p)‖) :
    dC i (cv a b) k = cv (dC i a) b k + cv a (dC i b) k := by
  have s1 : Summable fun p => dC i a p * b (k - p) :=
    Summable.of_norm_bounded h1 fun p => by rw [norm_mul]
  have s2 : Summable fun p => a p * dC i b (k - p) :=
    Summable.of_norm_bounded h2 fun p => by rw [norm_mul]
  have e : dC i (cv a b) k = ∑' p, Complex.I * (k i : ℂ) * (a p * b (k - p)) := by
    rw [tsum_mul_left]
    rfl
  rw [e]
  simp only [cv]
  rw [← s1.tsum_add s2]
  refine tsum_congr fun p => ?_
  simp only [dC, Pi.sub_apply, Int.cast_sub]
  ring

/-- The mixed second derivative is `≤ |k|² |û_k|`. -/
lemma normSq_dC_dC_mixed_le (u : Field) (i j a : Fin 3) (k : Mode) :
    ‖dC i (dC j (cmp u a)) k‖ ^ 2 ≤ sobWeight 2 k * ‖u k‖ ^ 2 := by
  rw [normSq_dC, normSq_dC, sobWeight_two]
  have h1 := sq_le_absSq i k
  have h1' := sq_le_absSq j k
  have h2 : ‖cmp u a k‖ ^ 2 ≤ ‖u k‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_cmp_le u a k) 2
  have h3 : (k i : ℝ) ^ 2 * (k j : ℝ) ^ 2 ≤ absSq k ^ 2 := by
    nlinarith [sq_nonneg (k i : ℝ), sq_nonneg (k j : ℝ), absSq_nonneg k]
  calc (k i : ℝ) ^ 2 * ((k j : ℝ) ^ 2 * ‖cmp u a k‖ ^ 2)
      = (k i : ℝ) ^ 2 * (k j : ℝ) ^ 2 * ‖cmp u a k‖ ^ 2 := by ring
    _ ≤ absSq k ^ 2 * ‖u k‖ ^ 2 := mul_le_mul h3 h2 (by positivity) (by positivity)

lemma summable_dC_dC_mixed {u : Field} (hu : InH 2 u) (i j a : Fin 3) :
    Summable fun k => ‖dC i (dC j (cmp u a)) k‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => by positivity) (normSq_dC_dC_mixed_le u i j a) hu

lemma tsum_dC_dC_mixed_le {u : Field} (hu : InH 2 u) (i j a : Fin 3) :
    ∑' k, ‖dC i (dC j (cmp u a)) k‖ ^ 2 ≤ hnorm 2 u ^ 2 := by
  have h0 : 0 ≤ ∑' k, sobWeight 2 k * ‖u k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg 2 k) (sq_nonneg _)
  rw [hnorm, Real.sq_sqrt h0]
  exact (summable_dC_dC_mixed hu i j a).tsum_le_tsum (normSq_dC_dC_mixed_le u i j a) hu

/-- The summands of `∂_i (U·∇U)_a`. -/
private def trA (S : Field) (i j a : Fin 3) (k : Mode) : ℂ :=
  cv (dC i (cmp S j)) (dC j (cmp S a)) k

private def trB (S : Field) (i j a : Fin 3) (k : Mode) : ℂ :=
  cv (cmp S j) (dC i (dC j (cmp S a))) k

/-- **The two factors of `∂_i(U·∇U)`**. -/
private lemma trA_le {S : Field} (hS : InH 2 S) {M : ℝ} (hM : SupBd S M) (i j a : Fin 3) :
    Summable (fun k => ‖trA S i j a k‖ ^ 2) ∧
      ∑' k, ‖trA S i j a k‖ ^ 2 ≤ 9 * M ^ 2 * hnorm 2 S ^ 2 := by
  have hu1 := summable_wiener hS
  have hS1 : InH 1 S := hS.mono (by norm_num)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hb := hnorm_nonneg 2 S
  obtain ⟨h1, h2⟩ := cv_gn_gn i j (summable_cmp hu1 j) (summable_cmp hu1 a)
    (summable_dC_sq hS1 i j) (summable_dC_sq hS1 j a) (summable_dC_dC_sq hS i j)
    (summable_dC_dC_sq hS j a) (hM.cmp hu1 j) (hM.cmp hu1 a)
  refine ⟨h1, h2.trans ?_⟩
  have e1 : Real.sqrt (∑' k, ‖dC i (dC i (cmp S j)) k‖ ^ 2) ≤ hnorm 2 S :=
    sqrt_le_of_sq' hb (tsum_dC_dC_sq_le hS i j)
  have e2 : Real.sqrt (∑' k, ‖dC j (dC j (cmp S a)) k‖ ^ 2) ≤ hnorm 2 S :=
    sqrt_le_of_sq' hb (tsum_dC_dC_sq_le hS j a)
  have h3 := mul_le_mul e1 e2 (Real.sqrt_nonneg _) hb
  calc _ = 9 * M ^ 2 * (Real.sqrt (∑' k, ‖dC i (dC i (cmp S j)) k‖ ^ 2) *
        Real.sqrt (∑' k, ‖dC j (dC j (cmp S a)) k‖ ^ 2)) := by ring
    _ ≤ 9 * M ^ 2 * (hnorm 2 S * hnorm 2 S) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

private lemma trB_le {S : Field} (hS : InH 2 S) {M : ℝ} (hM : SupBd S M) (i j a : Fin 3) :
    Summable (fun k => ‖trB S i j a k‖ ^ 2) ∧
      ∑' k, ‖trB S i j a k‖ ^ 2 ≤ M ^ 2 * hnorm 2 S ^ 2 := by
  have hu1 := summable_wiener hS
  obtain ⟨h1, h2⟩ := sup_product (summable_cmp hu1 j) (summable_dC_dC_mixed hS i j a)
    (hM.cmp hu1 j)
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (tsum_dC_dC_mixed_le hS i j a) (by positivity))⟩

/-- `k_i (U·∇U)_a` is the sum of the two factors. -/
private lemma dC_advect {S : Field} (hS : InH 2 S) (i a : Fin 3) (k : Mode) :
    ((k i : ℝ) : ℂ) * Complex.I * advect S S k a = ∑ j, (trA S i j a k + trB S i j a k) := by
  have hu1 := summable_wiener hS
  have hS1 : InH 1 S := hS.mono (by norm_num)
  have hS2 : Summable fun k => ‖S k‖ ^ 2 := summable_sq_of_summable hu1
  have hc2 : ∀ j, Summable fun k => ‖cmp S j k‖ ^ 2 := fun j =>
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun k => pow_le_pow_left₀ (norm_nonneg _) (norm_cmp_le S j k) 2) hS2
  rw [advect_apply (summable_adv hS2 hS1 k) a, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := dC_cv i (a := cmp S j) (b := dC j (cmp S a)) (k := k)
    (summable_mul_of_l2 (summable_dC_sq hS1 i j) (summable_dC_sq hS1 j a) k)
    (summable_mul_of_l2 (hc2 j) (summable_dC_dC_mixed hS i j a) k)
  simp only [dC] at h
  simp only [trA, trB]
  rw [← h]
  push_cast
  ring

/-- **`‖U·∇U‖₁ ≲ M b`**, on the coefficients. -/
private lemma tsum_absSq_advect_le {S : Field} (hS : InH 2 S) {M : ℝ} (hM : SupBd S M) :
    Summable (fun k => absSq k * ‖advect S S k‖ ^ 2) ∧
      ∑' k, absSq k * ‖advect S S k‖ ^ 2 ≤ 1620 * M ^ 2 * hnorm 2 S ^ 2 := by
  set E : Mode → ℝ := fun k => 6 * ∑ i, ∑ a, ∑ j,
    (‖trA S i j a k‖ ^ 2 + ‖trB S i j a k‖ ^ 2) with hE
  have hpt : ∀ k, absSq k * ‖advect S S k‖ ^ 2 ≤ E k := fun k => by
    have h1 : absSq k * ‖advect S S k‖ ^ 2 =
        ∑ i : Fin 3, ∑ a : Fin 3, ‖((k i : ℝ) : ℂ) * Complex.I * advect S S k a‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [absSq, Finset.sum_mul, Finset.mul_sum, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      exact Finset.sum_comm
    rw [h1, hE]
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => ?_
    rw [dC_advect hS i a k, ← Finset.mul_sum]
    set x : Fin 3 → ℝ := fun j => ‖trA S i j a k + trB S i j a k‖ with hx
    have h2 : ‖∑ j, (trA S i j a k + trB S i j a k)‖ ≤ ∑ j, x j := norm_sum_le _ _
    have h3 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3))) (f := x)
    have h4 : ∀ j, x j ^ 2 ≤
        2 * (‖trA S i j a k‖ ^ 2 + ‖trB S i j a k‖ ^ 2) := fun j => by
      have := norm_add_le (trA S i j a k) (trB S i j a k)
      have h5 : x j ≤ ‖trA S i j a k‖ + ‖trB S i j a k‖ := this
      have h6 : 0 ≤ x j := norm_nonneg _
      nlinarith [sq_nonneg (‖trA S i j a k‖ - ‖trB S i j a k‖)]
    calc ‖∑ j, (trA S i j a k + trB S i j a k)‖ ^ 2
        ≤ (∑ j, x j) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ ≤ 3 * ∑ j, x j ^ 2 := by simpa using h3
      _ ≤ 3 * ∑ j, 2 * (‖trA S i j a k‖ ^ 2 + ‖trB S i j a k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => h4 j) (by norm_num)
      _ = 6 * ∑ j, (‖trA S i j a k‖ ^ 2 + ‖trB S i j a k‖ ^ 2) := by
          rw [← Finset.mul_sum]
          ring
  have hsum : ∀ i a j, Summable fun k =>
      ‖trA S i j a k‖ ^ 2 + ‖trB S i j a k‖ ^ 2 := fun i a j =>
    (trA_le hS hM i j a).1.add (trB_le hS hM i j a).1
  have hEs : Summable E :=
    (summable_sum fun i _ => summable_sum fun a _ => summable_sum fun j _ =>
      hsum i a j).mul_left 6
  have hS3 : Summable fun k => absSq k * ‖advect S S k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (absSq_nonneg k) (by positivity)) hpt hEs
  refine ⟨hS3, (hS3.tsum_le_tsum hpt hEs).trans ?_⟩
  have hterm : ∀ i a j, ∑' k, (‖trA S i j a k‖ ^ 2 + ‖trB S i j a k‖ ^ 2) ≤
      10 * M ^ 2 * hnorm 2 S ^ 2 := fun i a j => by
    rw [(trA_le hS hM i j a).1.tsum_add (trB_le hS hM i j a).1]
    nlinarith [(trA_le hS hM i j a).2, (trB_le hS hM i j a).2]
  simp only [hE]
  rw [tsum_mul_left, Summable.tsum_finsetSum fun i _ => summable_sum fun a _ =>
    summable_sum fun j _ => hsum i a j]
  have h3 : ∑ i : Fin 3, ∑' k, ∑ a, ∑ j,
      (‖trA S i j a k‖ ^ 2 + ‖trB S i j a k‖ ^ 2) ≤
      ∑ _i : Fin 3, ∑ _a : Fin 3, ∑ _j : Fin 3, 10 * M ^ 2 * hnorm 2 S ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Summable.tsum_finsetSum fun a _ => summable_sum fun j _ => hsum i a j]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Summable.tsum_finsetSum fun j _ => hsum i a j]
    exact Finset.sum_le_sum fun j _ => hterm i a j
  have h4 : ∑ _i : Fin 3, ∑ _a : Fin 3, ∑ _j : Fin 3, 10 * M ^ 2 * hnorm 2 S ^ 2 =
      270 * M ^ 2 * hnorm 2 S ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [h4] at h3
  linarith

/-- **Body 30**: `‖B(S, S)‖₁ ≤ 41 M ‖S‖₂`, for `S ∈ H²` with sup bound `M`. -/
theorem hnorm_one_Bsym_le {S : Field} (hS : InH 2 S) {M : ℝ} (hM : SupBd S M) :
    InH 1 (Bsym S S) ∧ hnorm 1 (Bsym S S) ≤ 41 * M * hnorm 2 S := by
  have hu1 := summable_wiener hS
  have hS1 : InH 1 S := hS.mono (by norm_num)
  have hS2 : Summable fun k => ‖S k‖ ^ 2 := summable_sq_of_summable hu1
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hb := hnorm_nonneg 2 S
  obtain ⟨h1, h2⟩ := tsum_absSq_advect_le hS hM
  have hpt : ∀ k, sobWeight 1 k * ‖Bsym S S k‖ ^ 2 ≤ absSq k * ‖advect S S k‖ ^ 2 := fun k => by
    rw [sobWeight_one]
    have h3 := norm_Bsym_le (summable_adv hS2 hS1 k) (summable_adv hS2 hS1 k)
    have h4 : ‖Bsym S S k‖ ≤ ‖advect S S k‖ := h3.trans (le_of_eq (by ring))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h4 2) (absSq_nonneg k)
  have hs : InH 1 (Bsym S S) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg 1 k) (sq_nonneg _)) hpt h1
  refine ⟨hs, ?_⟩
  refine sqrt_le_of_sq' (by positivity) ?_
  refine (Summable.tsum_le_tsum hpt hs h1).trans (h2.trans ?_)
  have : 0 ≤ M ^ 2 * hnorm 2 S ^ 2 := by positivity
  nlinarith only [this]

end OVNS.Quant.GN

end
