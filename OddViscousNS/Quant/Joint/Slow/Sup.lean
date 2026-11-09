import OddViscousNS.Quant.Joint.Slow.Bernstein
import OddViscousNS.Quant.Joint.Slow.Strain

/-!
# E7-P: the physical maximum of a slow field

Steps 9, 10 of `Joint/Slow/Plan.lean`: `‖physS z x‖ ≤ ‖v‖_∞ + 𝒜(h)`, and the sup of `v` from
`L^{2q}` of a box truncation, by Nikolskii at even exponent (`norm_ev_pow_le`) and the `H²` tail
(`tsum_tail_le`).
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter UnitAddTorus

noncomputable section

namespace OVNS.Quant.Slow

open GN

/-! ### The horizontal torus inside `T3` -/

/-- The horizontal modes. -/
private def iotaM (k : Fin 2 → ℤ) : Mode := ![k 0, k 1, 0]

/-- The horizontal torus in `T3`. -/
private def iota (x : UnitAddTorus (Fin 2)) : T3 := ![x 0, x 1, 0]

private lemma mFourier_iota (k : Fin 2 → ℤ) (x : UnitAddTorus (Fin 2)) :
    mFourier (iotaM k) (iota x) = mFourier k x := by
  simp [mFourier, Fin.prod_univ_three, Fin.prod_univ_two, iotaM, iota]

private lemma norm_mFourier_two_le (k : Fin 2 → ℤ) (x : UnitAddTorus (Fin 2)) :
    ‖mFourier k x‖ ≤ 1 :=
  (ContinuousMap.norm_coe_le_norm _ x).trans_eq mFourier_norm

private lemma norm_e3 : ‖e3‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [e3, Fin.sum_univ_three]

private lemma PiV_iotaM (z : Field) (k : Fin 2 → ℤ) :
    PiV z (iotaM k) = GN.cmp z 2 (iotaM k) • e3 := by
  ext i
  fin_cases i <;> simp [PiV, e3, iotaM, GN.cmp]

/-- The vertical series on the horizontal torus. -/
private lemma summable_vert {z : Field} (hz : InH 2 z) (x : UnitAddTorus (Fin 2)) :
    Summable fun k : Fin 2 → ℤ => mFourier k x * GN.cmp z 2 (iotaM k) := by
  refine Summable.of_norm_bounded
    ((summable_wiener hz).comp_injective slowMode_injective) fun k => ?_
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_mFourier_two_le k x)).trans
    (norm_cmp_le z 2 _)

/-- `physS` of a vertical field is its scalar series. -/
private lemma norm_physS_PiV {z : Field} (hz : InH 2 z) (x : UnitAddTorus (Fin 2)) :
    ‖physS (PiV z) x‖ = ‖∑' k : Fin 2 → ℤ, mFourier k x * GN.cmp z 2 (iotaM k)‖ := by
  have e : physS (PiV z) x =
      (∑' k : Fin 2 → ℤ, mFourier k x * GN.cmp z 2 (iotaM k)) • e3 := by
    rw [← (summable_vert hz x).tsum_smul_const, physS]
    refine tsum_congr fun k => ?_
    change mFourier k x • PiV z (iotaM k) = _
    rw [PiV_iotaM, smul_smul]
  rw [e, norm_smul, norm_e3, mul_one]

/-- The series on the horizontal torus is a series on all the modes, at a point of `T3`. -/
private lemma tsum_vert_eq {c : Mode → ℂ} (hc : ∀ k, k 2 ≠ 0 → c k = 0)
    (x : UnitAddTorus (Fin 2)) :
    ∑' k : Fin 2 → ℤ, mFourier k x * c (iotaM k) = ∑' k : Mode, c k * mFourier k (iota x) := by
  have hsupp : Function.support (fun k => c k * mFourier k (iota x)) ⊆ Set.range iotaM :=
    fun k hk => by
      have h2 : k 2 = 0 := by
        by_contra h2
        exact hk (by simp [hc k h2])
      refine ⟨![k 0, k 1], ?_⟩
      funext i
      fin_cases i
      · rfl
      · rfl
      · exact h2.symm
  have hinj : Function.Injective iotaM := slowMode_injective
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun k => ?_
  rw [mFourier_iota, mul_comm]

private lemma summable_tail {f : Mode → ℝ} (hf : ∀ k, 0 ≤ f k) (hs : Summable f)
    (A : Finset Mode) : Summable fun k => if k ∈ A then (0 : ℝ) else f k :=
  Summable.of_nonneg_of_le (fun k => by split_ifs; exacts [le_rfl, hf k])
    (fun k => by split_ifs; exacts [hf k, le_rfl]) hs

private lemma norm_cmp_two_le {z : Field} (hz' : PiS z = z) (k : Mode) :
    ‖GN.cmp z 2 k‖ ≤ ‖PiV z k‖ := by
  by_cases hk : k 2 = 0
  · have h := PiLp.norm_apply_le (PiV z k) 2
    simpa [PiV, hk, GN.cmp] using h
  · simp [GN.cmp, slow_zero' hz' hk]

/-- The series is its truncation plus a tail. -/
private lemma norm_tsum_sub_ev_le {c : Mode → ℂ} (hc : Summable fun k => ‖c k‖) (A : Finset Mode)
    (p : T3) :
    ‖∑' k, c k * mFourier k p‖ ≤
      ‖ev (polyOf A c) p‖ + ∑' k, (if k ∈ A then 0 else ‖c k‖) := by
  have hle : ∀ k, ‖c k * mFourier k p‖ ≤ ‖c k‖ := fun k => by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_mFourier_le k p)
  have ht := summable_tail (fun _ => norm_nonneg _) hc A
  have hb : ∀ k, ‖if k ∈ A then 0 else c k * mFourier k p‖ ≤ if k ∈ A then 0 else ‖c k‖ :=
    fun k => by
      split_ifs
      · simp
      · exact hle k
  have hg : Summable fun k => if k ∈ A then c k * mFourier k p else 0 :=
    summable_of_ne_finset_zero (s := A) fun k hk => by simp [hk]
  have e : ∑' k, c k * mFourier k p = ev (polyOf A c) p +
      ∑' k, (if k ∈ A then 0 else c k * mFourier k p) := by
    have h1 : ∑ k ∈ A, c k * mFourier k p = ∑' k, if k ∈ A then c k * mFourier k p else 0 := by
      rw [tsum_eq_sum (s := A) (fun k hk => by simp [hk])]
      exact Finset.sum_congr rfl fun k hk => by simp [hk]
    rw [ev_polyOf, tp_apply, h1, ← hg.tsum_add (Summable.of_norm_bounded ht hb)]
    refine tsum_congr fun k => ?_
    split_ifs <;> simp
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add_right (tsum_of_norm_bounded ht.hasSum hb) _)

/-- Nikolskii on the box, under the root. -/
private lemma norm_ev_le_of_mP {P : Pol} {q N : ℕ} (hq : 1 ≤ q) {Y Λ : ℝ} (hY : 0 ≤ Y)
    (hΛ : 0 ≤ Λ) (hP : ∀ k, P.coeff k ≠ 0 → k ∈ slowBox (2 * N)) (hm : mP q P ≤ Y ^ q)
    (hΛq : 4 * (q : ℝ) * N + 1 ≤ Λ ^ q) (p : T3) :
    ‖ev P p‖ ≤ Λ * Real.sqrt Y := by
  have h := norm_ev_pow_le hP hq p
  have e1 : (2 * (q : ℝ) * ((2 * N : ℕ) : ℝ) + 1) = 4 * (q : ℝ) * N + 1 := by
    push_cast
    ring
  rw [e1] at h
  have h0 : (0 : ℝ) ≤ 4 * (q : ℝ) * N + 1 := by positivity
  have h1 : (4 * (q : ℝ) * N + 1) ^ 2 ≤ (Λ ^ q) ^ 2 := pow_le_pow_left₀ h0 hΛq 2
  have hYq : 0 ≤ Y ^ q := pow_nonneg hY q
  have h2 : (‖ev P p‖ ^ 2) ^ q ≤ (Λ ^ 2 * Y) ^ q := by
    calc (‖ev P p‖ ^ 2) ^ q = ‖ev P p‖ ^ (2 * q) := (pow_mul _ _ _).symm
      _ ≤ (4 * (q : ℝ) * N + 1) ^ 2 * mP q P := h
      _ ≤ (4 * (q : ℝ) * N + 1) ^ 2 * Y ^ q := mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      _ ≤ (Λ ^ q) ^ 2 * Y ^ q := mul_le_mul_of_nonneg_right h1 hYq
      _ = (Λ ^ 2 * Y) ^ q := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm q 2]
  have h3 : ‖ev P p‖ ^ 2 ≤ Λ ^ 2 * Y :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).1 h2
  have h4 : (Λ * Real.sqrt Y) ^ 2 = Λ ^ 2 * Y := by rw [mul_pow, Real.sq_sqrt hY]
  rw [← h4] at h3
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

/-- **The physical slow field from the truncated `L^{2q}` of its vertical part.** -/
theorem norm_physS_le_of_poly {z : Field} (hz : Adm 2 z) (hz' : PiS z = z) {q N : ℕ} (hq : 1 ≤ q)
    (hN : 1 ≤ N) {Y Λ : ℝ} (hY : 0 ≤ Y) (hΛ : 0 ≤ Λ)
    (hm : mP q (polyOf (slowBox (2 * N)) (GN.cmp z 2)) ≤ Y ^ q)
    (hΛq : 4 * (q : ℝ) * N + 1 ≤ Λ ^ q) (x : UnitAddTorus (Fin 2)) :
    ‖physS z x‖ ≤ Λ * Real.sqrt Y + 2 * hnorm 2 z / N + wiener (PiH z) := by
  have hH : InH 2 (PiH z) := hz.inH.PiH
  have hV : InH 2 (PiV z) := hz.inH.PiV
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : physS z x = physS (PiH z) x + physS (PiV z) x := by
    rw [← physS_add hH hV, ← PiS_eq_PiH_add_PiV, hz']
  have hcs : ∀ k, k 2 ≠ 0 → GN.cmp z 2 k = 0 := fun k hk => by
    simp [GN.cmp, slow_zero' hz' hk]
  have hc : Summable fun k => ‖GN.cmp z 2 k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_cmp_le z 2) (summable_wiener hz.inH)
  have h2 := norm_tsum_sub_ev_le hc (slowBox (2 * N)) (iota x)
  rw [← tsum_vert_eq hcs x, ← norm_physS_PiV hz.inH x] at h2
  have h3 := norm_ev_le_of_mP (N := N) hq hY hΛ (fun k hk => ?_) hm hΛq (iota x)
  · have h4 := tsum_tail_le hV (fun k hk => by simp [PiV, hk]) (by simp [PiV, hz.mean])
      (N := 2 * N) (by omega)
    have h5 : ∑' k, (if k ∈ slowBox (2 * N) then 0 else ‖GN.cmp z 2 k‖) ≤
        ∑' k, (if k ∈ slowBox (2 * N) then 0 else ‖PiV z k‖) := by
      refine Summable.tsum_le_tsum (fun k => ?_) (summable_tail (fun _ => norm_nonneg _) hc _)
        (summable_tail (fun _ => norm_nonneg _) (summable_wiener hV) _)
      split_ifs
      · exact le_rfl
      · exact norm_cmp_two_le hz' k
    have h6 : 4 * hnorm 2 (PiV z) / ((2 * N : ℕ) : ℝ) ≤ 2 * hnorm 2 z / N := by
      have e2 : 4 * hnorm 2 (PiV z) / ((2 * N : ℕ) : ℝ) = 2 * hnorm 2 (PiV z) / N := by
        push_cast
        field_simp
        ring
      rw [e2]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hnorm_PiV_le' hz.inH) (by norm_num)) hN0.le
    have h7 := norm_physS_le_wiener hH x
    have h8 := norm_add_le (physS (PiH z) x) (physS (PiV z) x)
    rw [e]
    linarith
  · by_contra hA
    apply hk
    rw [coeff_polyOf]
    simp [tr, hA]

end OVNS.Quant.Slow
