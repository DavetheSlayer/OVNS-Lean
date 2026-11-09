import OddViscousNS.Closed.Cond.Defs
import OddViscousNS.Closed.Triad
import OddViscousNS.Closed.PairGram
import OddViscousNS.Closed.RowChain

/-!
# The row chain on the complement of the LLH class

Same Cauchy–Schwarz chain as `cubic_le_rowchain` (OddViscousNS/Closed/RowChain.lean), applied to
the complementary triad sum `triadRest`: per output `k`, the pairs `(p, k−p)` occurring in the
complement are never both on the first shell, so after restoring the other nonnegative pair
masses, `|triadRest w| ≤ √Y Z ∑_k √(M₀ Q_k R'_k)` under `RowBound (fun _ => M₀)`.
-/

open scoped ENNReal ComplexConjugate

namespace OVNS

private lemma absSq_pos' {k : Mode} (hk : k ≠ 0) : 0 < absSq k :=
  lt_of_lt_of_le one_pos (one_le_absSq hk)

private lemma hm_pos {k : Mode} (hk : k ≠ 0) : 0 < hm k :=
  hmet_pos (Nat.one_le_iff_ne_zero.2 fun h ↦ hk ((nsq_eq_zero_iff k).1 h))

private lemma hm_zero : hm 0 = 0 := by
  simp [hm, hmet, nsq]

private lemma hm_nonneg (k : Mode) : 0 ≤ hm k := by
  by_cases hk : k = 0
  · rw [hk, hm_zero]
  · exact (hm_pos hk).le

private lemma absSq_zero : absSq 0 = 0 := by
  simp [absSq]

/-- The unnormalized dissipation weights `A_k h_k ‖u_k‖²`. -/
private lemma aw_nonneg (u : Field) (k : Mode) : 0 ≤ absSq k * hm k * ‖u k‖ ^ 2 :=
  mul_nonneg (mul_nonneg (absSq_nonneg k) (hm_nonneg k)) (sq_nonneg _)

private lemma summable_aw {u : Field} (hu : Adm 2 u) :
    Summable fun k ↦ absSq k * hm k * ‖u k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (aw_nonneg u) (fun k ↦ ?_) hu.inH
  by_cases hk : k = 0
  · simp [hk, absSq_zero, sobWeight]
  · have h0 := absSq_nonneg k
    have hw : sobWeight 2 k = absSq k ^ 2 := by
      simp only [sobWeight, hk, ↓reduceIte]
      rw [absk, show (2 : ℝ) * 2 = (4 : ℕ) by norm_num, Real.rpow_natCast,
        show 4 = 2 * 2 by rfl, pow_mul, Real.sq_sqrt h0]
    have hh : hm k ≤ absSq k := by
      rw [← nsq_cast]; exact hmet_upper _
    rw [hw, sq (absSq k)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh h0) (sq_nonneg _)

private lemma summable_hy {u : Field} (hu : Adm 2 u) :
    Summable fun k ↦ hm k * ‖u k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (hm_nonneg k) (sq_nonneg _))
    (fun k ↦ ?_) (summable_aw hu)
  by_cases hk : k = 0
  · simp [hk, hm_zero]
  · rw [mul_assoc]
    exact le_mul_of_one_le_left (mul_nonneg (hm_nonneg k) (sq_nonneg _)) (one_le_absSq hk)

private lemma eq_zero_of_Zr {u : Field} (hu : Adm 2 u) (hZ : Zr u = 0) : u = 0 := by
  have h0 : HasSum (fun k ↦ absSq k * hm k * ‖u k‖ ^ 2) (Zr u) := (summable_aw hu).hasSum
  rw [hZ] at h0
  have h := (hasSum_zero_iff_of_nonneg (aw_nonneg u)).1 h0
  funext k
  by_cases hk : k = 0
  · rw [hk, hu.mean]; rfl
  · have hk' := congrFun h k
    simp only [Pi.zero_apply, mul_eq_zero, (absSq_pos' hk).ne', (hm_pos hk).ne', false_or,
      pow_eq_zero_iff two_ne_zero, norm_eq_zero] at hk'
    exact hk'

private lemma eq_zero_of_Yr {u : Field} (hu : Adm 2 u) (hY : Yr u = 0) : u = 0 := by
  have h0 : HasSum (fun k ↦ hm k * ‖u k‖ ^ 2) (Yr u) := (summable_hy hu).hasSum
  rw [hY] at h0
  have h := (hasSum_zero_iff_of_nonneg (fun k ↦ mul_nonneg (hm_nonneg k) (sq_nonneg _))).1 h0
  funext k
  by_cases hk : k = 0
  · rw [hk, hu.mean]; rfl
  · have hk' := congrFun h k
    simp only [Pi.zero_apply, mul_eq_zero, (hm_pos hk).ne', false_or,
      pow_eq_zero_iff two_ne_zero, norm_eq_zero] at hk'
    exact hk'

private lemma Zr_nonneg (u : Field) : 0 ≤ Zr u := tsum_nonneg (aw_nonneg u)

private lemma Yr_nonneg (u : Field) : 0 ≤ Yr u :=
  tsum_nonneg fun k ↦ mul_nonneg (hm_nonneg k) (sq_nonneg _)

private lemma Pk_nonneg (u : Field) (k : Mode) : 0 ≤ Pk u k :=
  div_nonneg (aw_nonneg u k) (Zr_nonneg u)

private lemma Qk_nonneg (u : Field) (k : Mode) : 0 ≤ Qk u k := by
  unfold Qk
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Pk_nonneg u k)
      (mul_nonneg (div_nonneg (Yr_nonneg u) (Zr_nonneg u)) (absSq_nonneg k))

private lemma Qk_eq {u : Field} (hZ : Zr u ≠ 0) (hY : Yr u ≠ 0) (k : Mode) :
    Qk u k = hm k * ‖u k‖ ^ 2 / Yr u := by
  unfold Qk Pk tYZ
  split_ifs with hk
  · simp [hk, hm_zero]
  · have := (absSq_pos' hk).ne'
    field_simp

private lemma Yr_ne_zero {u : Field} (hu : Adm 2 u) (hZ : Zr u ≠ 0) : Yr u ≠ 0 := fun hY ↦
  hZ (by rw [eq_zero_of_Yr hu hY]; simp [Zr])

private lemma Qk_of_Zr {u : Field} (hu : Adm 2 u) (hZ : Zr u = 0) (k : Mode) : Qk u k = 0 := by
  have h0 := eq_zero_of_Zr hu hZ
  unfold Qk Pk
  split_ifs
  · rfl
  · simp [h0]

private lemma summable_Qk {u : Field} (hu : Adm 2 u) (hZ : Zr u ≠ 0) :
    Summable (Qk u) ∧ ∑' k, Qk u k = 1 := by
  have hY := Yr_ne_zero hu hZ
  have h : Qk u = fun k ↦ hm k * ‖u k‖ ^ 2 / Yr u := funext (Qk_eq hZ hY)
  rw [h]
  exact ⟨(summable_hy hu).div_const _, by rw [tsum_div_const]; exact div_self hY⟩

private lemma summable_Pk {u : Field} (hu : Adm 2 u) (hZ : Zr u ≠ 0) :
    Summable (Pk u) ∧ ∑' k, Pk u k = 1 :=
  ⟨(summable_aw hu).div_const _, by unfold Pk; rw [tsum_div_const]; exact div_self hZ⟩

/-- The `(k, p)`-indexed summand of `R_k`. -/
private noncomputable def Fr (u : Field) (kp : Mode × Mode) : ℝ :=
  if cross (modeVec kp.2) (modeVec (kp.1 - kp.2)) = 0 then 0 else Pk u kp.2 * Pk u (kp.1 - kp.2)

/-- `(k, p) ↦ (p, k - p)`. -/
private def eKP : Mode × Mode ≃ Mode × Mode where
  toFun kp := (kp.2, kp.1 - kp.2)
  invFun pl := (pl.1 + pl.2, pl.1)
  left_inv kp := by simp
  right_inv pl := by simp

private lemma Fr_nonneg (u : Field) (kp : Mode × Mode) : 0 ≤ Fr u kp := by
  unfold Fr
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Pk_nonneg u _) (Pk_nonneg u _)

private lemma Fr_le (u : Field) (kp : Mode × Mode) :
    Fr u kp ≤ Pk u kp.2 * Pk u (kp.1 - kp.2) := by
  unfold Fr
  split_ifs
  · exact mul_nonneg (Pk_nonneg u _) (Pk_nonneg u _)
  · exact le_rfl

private lemma summable_Pk_norm {u : Field} (hu : Adm 2 u) (hZ : Zr u ≠ 0) :
    Summable fun k ↦ ‖Pk u k‖ := by
  simpa [Real.norm_eq_abs, abs_of_nonneg (Pk_nonneg u _)] using (summable_Pk hu hZ).1

private lemma summable_PP {u : Field} (hu : Adm 2 u) (hZ : Zr u ≠ 0) :
    Summable fun kp : Mode × Mode ↦ Pk u kp.2 * Pk u (kp.1 - kp.2) := by
  have hPn := summable_Pk_norm hu hZ
  have hG : Summable fun x : Mode × Mode ↦ Pk u x.1 * Pk u x.2 :=
    summable_mul_of_summable_norm hPn hPn
  have h := (eKP.summable_iff (f := fun x : Mode × Mode ↦ Pk u x.1 * Pk u x.2)).2 hG
  exact h

private lemma summable_Fr {u : Field} (hu : Adm 2 u) (hZ : Zr u ≠ 0) : Summable (Fr u) :=
  (summable_PP hu hZ).of_nonneg_of_le (Fr_nonneg u) (Fr_le u)

/-! ### Pointwise algebra for the triad terms -/

private lemma abs_tsum_le {ι : Type*} {f b : ι → ℝ} (hb : Summable b)
    (h : ∀ i, |f i| ≤ b i) :
    |∑' i, f i| ≤ ∑' i, b i := by
  have hf : Summable f := Summable.of_norm_bounded hb fun i ↦ by simpa using h i
  rw [abs_le]
  constructor
  · rw [← tsum_neg]
    exact hb.neg.tsum_le_tsum (fun i ↦ neg_le_of_abs_le (h i)) hf
  · exact hf.tsum_le_tsum (fun i ↦ le_of_abs_le (h i)) hb

private lemma conjV_zero : conjV 0 = 0 := by
  ext i
  simp [conjV]

private lemma dotM_conjV (v : V3) (k : Mode) : dotM (conjV v) k = conj (dotM v k) := by
  simp [dotM, conjV, map_sum]

private lemma triT_zero_left (p l q : Mode) (b c : V3) : triT p l q 0 b c = 0 := by
  simp [triT, det3, dotV, curlS, cross, Fin.sum_univ_three]

private lemma triT_zero_mid (p l q : Mode) (a c : V3) : triT p l q a 0 c = 0 := by
  simp [triT, det3, dotV, curlS, cross, Fin.sum_univ_three]

private lemma triT_zero_right (p l q : Mode) (a b : V3) : triT p l q a b 0 = 0 := by
  simp [triT, det3, dotV, curlS, cross, Fin.sum_univ_three]

private lemma gramQ_of_cross {p k : Mode} {c : V3}
    (h : cross (modeVec p) (modeVec (k - p)) = 0) : gramQ p (k - p) k c = 0 := by
  have hE : cross (modeVec p) (modeVec k) = cross (modeVec p) (modeVec (k - p)) := by
    ext i
    fin_cases i <;> simp [cross, modeVec] <;> ring
  unfold gramQ
  split_ifs
  · rfl
  · simp only [hE, h]
    simp [dotV, cross, Fin.sum_univ_three]

/-- The bound of the `(k, p)` triad term given by the pair Gram inequality. -/
private noncomputable def tk (u : Field) (k p : Mode) : ℝ :=
  |Wk lamW k p| * (‖u p‖ * ‖u (k - p)‖ * Real.sqrt (gramQ p (k - p) k (conjV (u k))))

/-- The first Cauchy–Schwarz factor `[p×l≠0] √(A_p h_p ‖u_p‖² A_l h_l ‖u_l‖²)`. -/
private noncomputable def xk (u : Field) (k p : Mode) : ℝ :=
  if cross (modeVec p) (modeVec (k - p)) = 0 then 0 else
    Real.sqrt (absSq p * hm p * ‖u p‖ ^ 2 * (absSq (k - p) * hm (k - p) * ‖u (k - p)‖ ^ 2))

/-- The summand of `rowQ k (conj u_k)`, before `ofReal`. -/
private noncomputable def rk (u : Field) (k p : Mode) : ℝ :=
  Wk lamW k p ^ 2 * gramQ p (k - p) k (conjV (u k)) /
    (absSq p * hm p * absSq (k - p) * hm (k - p))

private lemma rk_nonneg (u : Field) (k p : Mode) : 0 ≤ rk u k p :=
  div_nonneg (mul_nonneg (sq_nonneg _) (gramQ_nonneg _ _ _ _))
    (mul_nonneg (mul_nonneg (mul_nonneg (absSq_nonneg p) (hm_nonneg p)) (absSq_nonneg _))
      (hm_nonneg _))

private lemma tk_nonneg (u : Field) (k p : Mode) : 0 ≤ tk u k p := by
  unfold tk; positivity

private lemma xk_nonneg (u : Field) (k p : Mode) : 0 ≤ xk u k p := by
  unfold xk; split_ifs
  · exact le_rfl
  · exact Real.sqrt_nonneg _

private lemma term_le {u : Field} (hu : Adm 2 u) (k p : Mode) :
    |Wk lamW k p * (triT p (k - p) (-k) (u p) (u (k - p)) (conjV (u k))).re| ≤ tk u k p := by
  rw [tk, abs_mul]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (abs_nonneg _)
  by_cases hp : p = 0
  · simp [hp, hu.mean, triT_zero_left]
  by_cases hl : k - p = 0
  · rw [hl, hu.mean, triT_zero_mid, norm_zero]; positivity
  by_cases hk : k = 0
  · rw [hk, hu.mean, conjV_zero, triT_zero_right, norm_zero]; positivity
  have h := triT_sq_le (show p + (k - p) = k by abel) hp hl hk (hu.sol p) (hu.sol (k - p))
    (show dotM (conjV (u k)) k = 0 by rw [dotM_conjV, hu.sol k, map_zero])
  calc ‖triT p (k - p) (-k) (u p) (u (k - p)) (conjV (u k))‖
      ≤ Real.sqrt ((‖u p‖ * ‖u (k - p)‖) ^ 2 * gramQ p (k - p) k (conjV (u k))) :=
        Real.le_sqrt_of_sq_le (by rw [mul_pow]; exact h)
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

private lemma tk_le {u : Field} (hu : Adm 2 u) (k p : Mode) :
    tk u k p ≤ xk u k p * Real.sqrt (rk u k p) := by
  have h0 : 0 ≤ xk u k p * Real.sqrt (rk u k p) :=
    mul_nonneg (xk_nonneg u k p) (Real.sqrt_nonneg _)
  unfold xk
  split_ifs with hc
  · simp [tk, gramQ_of_cross hc]
  by_cases hp : p = 0
  · rw [show tk u k p = 0 by simp [tk, hp, hu.mean]]
    exact (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  by_cases hl : k - p = 0
  · rw [show tk u k p = 0 by simp [tk, hl, hu.mean]]
    exact (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have h1 := (absSq_pos' hp).ne'
  have h2 := (hm_pos hp).ne'
  have h3 := (absSq_pos' hl).ne'
  have h4 := (hm_pos hl).ne'
  rw [← Real.sqrt_mul (mul_nonneg (aw_nonneg u p) (aw_nonneg u (k - p)))]
  have e : tk u k p = Real.sqrt ((Wk lamW k p * ‖u p‖ * ‖u (k - p)‖) ^ 2 *
      gramQ p (k - p) k (conjV (u k))) := by
    rw [tk, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_mul, abs_mul, abs_norm,
      abs_norm]
    ring
  rw [e]
  apply le_of_eq
  congr 1
  unfold rk
  field_simp

private lemma xk_sq {u : Field} (hZ : Zr u ≠ 0) (k p : Mode) :
    xk u k p ^ 2 = Zr u ^ 2 * Fr u (k, p) := by
  unfold xk Fr Pk
  split_ifs
  · simp
  · rw [Real.sq_sqrt (mul_nonneg (aw_nonneg u p) (aw_nonneg u (k - p)))]
    field_simp


/-! ### The restricted pair sums -/

/-- The `(k, p)`-indexed summand of `R'_k`. -/
private noncomputable def Fr' (u : Field) (kp : Mode × Mode) : ℝ :=
  if (nsq kp.2 = 1 ∧ nsq (kp.1 - kp.2) = 1) ∨ cross (modeVec kp.2) (modeVec (kp.1 - kp.2)) = 0
  then 0 else Pk u kp.2 * Pk u (kp.1 - kp.2)

private lemma Rk'_eq (u : Field) (k : Mode) : Rk' u k = ∑' p, Fr' u (k, p) := rfl

private lemma Fr'_nonneg (u : Field) (kp : Mode × Mode) : 0 ≤ Fr' u kp := by
  unfold Fr'
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Pk_nonneg u _) (Pk_nonneg u _)

private lemma Fr'_le (u : Field) (kp : Mode × Mode) : Fr' u kp ≤ Fr u kp := by
  unfold Fr' Fr
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact mul_nonneg (Pk_nonneg u _) (Pk_nonneg u _)
  · exact absurd (Or.inr h2) h1
  · exact le_rfl

private lemma summable_Fr' {u : Field} (hu : Adm 2 u) (hZ : Zr u ≠ 0) : Summable (Fr' u) :=
  (summable_Fr hu hZ).of_nonneg_of_le (Fr'_nonneg u) (Fr'_le u)

private lemma Rk'_nonneg (u : Field) (k : Mode) : 0 ≤ Rk' u k :=
  tsum_nonneg fun p ↦ Fr'_nonneg u (k, p)

private lemma summable_Rk' {u : Field} (hu : Adm 2 u) (hZ : Zr u ≠ 0) : Summable (Rk' u) := by
  have h := (summable_Fr' hu hZ).prod
  exact h

private lemma sqrt_QR'_le (u : Field) (k : Mode) :
    Real.sqrt (Qk u k * Rk' u k) ≤ (Qk u k + Rk' u k) / 2 := by
  have hQ := Qk_nonneg u k
  have hR := Rk'_nonneg u k
  calc Real.sqrt (Qk u k * Rk' u k) ≤ Real.sqrt (((Qk u k + Rk' u k) / 2) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Qk u k - Rk' u k)])
    _ = (Qk u k + Rk' u k) / 2 := Real.sqrt_sq (by positivity)

/-- The restricted pair sums are summable in `k` and the chain series converges. -/
theorem summable_sqrt_QR' {w : Field} (hw : Adm 2 w) :
    Summable fun k => Real.sqrt (Qk w k * Rk' w k) := by
  by_cases hZ : Zr w = 0
  · simp [Qk_of_Zr hw hZ]
  exact (((summable_Qk hw hZ).1.add (summable_Rk' hw hZ)).div_const 2).of_nonneg_of_le
    (fun k ↦ Real.sqrt_nonneg _) (sqrt_QR'_le w)

/-! ### The chain on the complement of the LLH class -/

/-- The first Cauchy–Schwarz factor restricted to the complement of the LLH class. -/
private noncomputable def xk' (u : Field) (k p : Mode) : ℝ :=
  if isLLH p (k - p) (-k) then 0 else xk u k p

private lemma xk'_nonneg (u : Field) (k p : Mode) : 0 ≤ xk' u k p := by
  unfold xk'; split_ifs
  · exact le_rfl
  · exact xk_nonneg u k p

private lemma xk'_sq_le {u : Field} (hZ : Zr u ≠ 0) (k p : Mode) :
    xk' u k p ^ 2 ≤ Zr u ^ 2 * Fr' u (k, p) := by
  unfold xk'
  split_ifs with h
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (sq_nonneg _) (Fr'_nonneg u _)
  · rw [xk_sq hZ]
    apply le_of_eq
    congr 1
    have hLL : ¬ (nsq p = 1 ∧ nsq (k - p) = 1) := fun h' ↦ h (Or.inl h')
    unfold Fr Fr'
    simp only [hLL, false_or]

private lemma M₀_nonneg : 0 ≤ M₀ := by norm_num [M₀]

/-- The row sums of `rk` under `RowBound (fun _ => M₀)`. -/
private lemma rk_row (hRB : RowBound fun _ => M₀) {u : Field} (hu : Adm 2 u) (k : Mode) :
    Summable (fun p ↦ Real.sqrt (rk u k p) ^ 2) ∧
      ∑' p, Real.sqrt (rk u k p) ^ 2 ≤ 36 * M₀ * hm k * ‖u k‖ ^ 2 := by
  by_cases hk : k = 0
  · have h0 : ∀ p, rk u k p = 0 := fun p ↦ by simp [rk, hk, gramQ]
    simp only [h0, Real.sqrt_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      tsum_zero]
    exact ⟨summable_zero,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) M₀_nonneg) (hm_nonneg k)) (sq_nonneg _)⟩
  have hc : dotM (conjV (u k)) k = 0 := by rw [dotM_conjV, hu.sol k, map_zero]
  have hrow := hRB k hk _ hc
  have hfin : rowQ k (conjV (u k)) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrow
  have hy2 : ∀ p, Real.sqrt (rk u k p) ^ 2 = (ENNReal.ofReal (rk u k p)).toReal := fun p ↦ by
    rw [Real.sq_sqrt (rk_nonneg u k p), ENNReal.toReal_ofReal (rk_nonneg u k p)]
  refine ⟨by simp_rw [hy2]; exact ENNReal.summable_toReal hfin, ?_⟩
  simp_rw [hy2]
  rw [← ENNReal.tsum_toReal_eq fun _ ↦ ENNReal.ofReal_ne_top, ← norm_conjV (u k)]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) M₀_nonneg) (hm_nonneg k)) (sq_nonneg _)) hrow

private lemma summable_rk (hRB : RowBound fun _ => M₀) {u : Field} (hu : Adm 2 u) :
    Summable fun kp : Mode × Mode ↦ rk u kp.1 kp.2 := by
  have e : ∀ k, (fun p ↦ rk u k p) = fun p ↦ Real.sqrt (rk u k p) ^ 2 := fun k ↦
    funext fun p ↦ (Real.sq_sqrt (rk_nonneg u k p)).symm
  refine (summable_prod_of_nonneg (fun kp ↦ rk_nonneg u kp.1 kp.2)).2 ⟨fun k ↦ ?_, ?_⟩
  · rw [e k]; exact (rk_row hRB hu k).1
  · refine (((summable_hy hu).mul_left (36 * M₀))).of_nonneg_of_le
      (fun k ↦ tsum_nonneg fun p ↦ rk_nonneg u k p) fun k ↦ ?_
    rw [e k, ← mul_assoc]
    exact (rk_row hRB hu k).2

/-- The pair-level majorant of the complementary triad terms. -/
private noncomputable def Bk (u : Field) (kp : Mode × Mode) : ℝ :=
  xk' u kp.1 kp.2 * Real.sqrt (rk u kp.1 kp.2)

private lemma Bk_nonneg (u : Field) (kp : Mode × Mode) : 0 ≤ Bk u kp :=
  mul_nonneg (xk'_nonneg u _ _) (Real.sqrt_nonneg _)

private lemma summable_Bk (hRB : RowBound fun _ => M₀) {u : Field} (hu : Adm 2 u)
    (hZ : Zr u ≠ 0) : Summable (Bk u) := by
  refine ((((summable_Fr' hu hZ).mul_left (Zr u ^ 2)).add (summable_rk hRB hu)).div_const
    2).of_nonneg_of_le (Bk_nonneg u) fun kp ↦ ?_
  have h1 := xk'_sq_le hZ kp.1 kp.2
  have h2 := Real.sq_sqrt (rk_nonneg u kp.1 kp.2)
  have h3 := sq_nonneg (xk' u kp.1 kp.2 - Real.sqrt (rk u kp.1 kp.2))
  simp only [Bk]
  nlinarith

/-- The summand of `triadRest`. -/
private noncomputable def fR (u : Field) (kp : Mode × Mode) : ℝ :=
  if isLLH kp.2 (kp.1 - kp.2) (-kp.1) then 0 else
    Wk lamW kp.1 kp.2 * (triT kp.2 (kp.1 - kp.2) (-kp.1) (u kp.2) (u (kp.1 - kp.2))
      (conjV (u kp.1))).re

private lemma fR_le {u : Field} (hu : Adm 2 u) (kp : Mode × Mode) : |fR u kp| ≤ Bk u kp := by
  unfold fR Bk xk'
  split_ifs
  · simp
  · exact (term_le hu kp.1 kp.2).trans (tk_le hu kp.1 kp.2)

/-- The Cauchy–Schwarz step at a fixed output `k`. -/
private lemma row_le' (hRB : RowBound fun _ => M₀) {u : Field} (hu : Adm 2 u) (hZ : Zr u ≠ 0)
    (k : Mode) :
    ∑' p, Bk u (k, p) ≤ 6 * (Real.sqrt (Yr u) * Zr u * Real.sqrt (M₀ * Qk u k * Rk' u k)) := by
  have hY := Yr_ne_zero hu hZ
  obtain ⟨hys, hysum⟩ := rk_row hRB hu k
  have hxs : Summable fun p ↦ xk' u k p ^ 2 :=
    (((summable_Fr' hu hZ).prod_factor k).mul_left (Zr u ^ 2)).of_nonneg_of_le
      (fun p ↦ sq_nonneg _) (xk'_sq_le hZ k)
  have hxsum : ∑' p, xk' u k p ^ 2 ≤ Zr u ^ 2 * Rk' u k := by
    rw [Rk'_eq, ← tsum_mul_left]
    exact hxs.tsum_le_tsum (xk'_sq_le hZ k)
      (((summable_Fr' hu hZ).prod_factor k).mul_left _)
  obtain ⟨_, hCS⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two (xk'_nonneg u k) (fun p ↦ Real.sqrt_nonneg (rk u k p))
    (by simpa only [Real.rpow_two] using hxs) (by simpa only [Real.rpow_two] using hys)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  have e1 : Real.sqrt (Zr u ^ 2 * Rk' u k) = Zr u * Real.sqrt (Rk' u k) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Zr_nonneg u)]
  have e2 : Real.sqrt (36 * M₀ * hm k * ‖u k‖ ^ 2) =
      6 * (Real.sqrt (Yr u) * Real.sqrt (M₀ * Qk u k)) := by
    have h36 : (6 : ℝ) = Real.sqrt 36 := by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h36, ← Real.sqrt_mul (Yr_nonneg u), ← Real.sqrt_mul (by norm_num), Qk_eq hZ hY]
    congr 1
    field_simp
  have e3 : Real.sqrt (M₀ * Qk u k * Rk' u k) =
      Real.sqrt (M₀ * Qk u k) * Real.sqrt (Rk' u k) :=
    Real.sqrt_mul (mul_nonneg M₀_nonneg (Qk_nonneg u k)) _
  calc ∑' p, Bk u (k, p) = ∑' p, xk' u k p * Real.sqrt (rk u k p) := rfl
    _ ≤ Real.sqrt (∑' p, xk' u k p ^ 2) * Real.sqrt (∑' p, Real.sqrt (rk u k p) ^ 2) := hCS
    _ ≤ Real.sqrt (Zr u ^ 2 * Rk' u k) * Real.sqrt (36 * M₀ * hm k * ‖u k‖ ^ 2) :=
      mul_le_mul (Real.sqrt_le_sqrt hxsum) (Real.sqrt_le_sqrt hysum) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    _ = _ := by rw [e1, e2, e3]; ring

/-- The row chain on the complement of the LLH class. -/
theorem triadRest_le (hRB : RowBound fun _ => M₀) {w : Field} (hw : Adm 2 w) :
    |triadRest w| ≤ Real.sqrt (Yr w) * Zr w * ∑' k, Real.sqrt (M₀ * Qk w k * Rk' w k) := by
  have hR : 0 ≤ Real.sqrt (Yr w) * Zr w * ∑' k, Real.sqrt (M₀ * Qk w k * Rk' w k) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Zr_nonneg w))
      (tsum_nonneg fun _ ↦ Real.sqrt_nonneg _)
  by_cases hZ : Zr w = 0
  · have h0 := eq_zero_of_Zr hw hZ
    have : triadRest w = 0 := by simp [triadRest, h0, triT_zero_left]
    rw [this, abs_zero]
    exact hR
  have hB := summable_Bk hRB hw hZ
  have hs : Summable fun k ↦ Real.sqrt (Yr w) * Zr w * Real.sqrt (M₀ * Qk w k * Rk' w k) := by
    refine ((summable_sqrt_QR' hw).mul_left (Real.sqrt (Yr w) * Zr w * Real.sqrt M₀)).congr
      fun k ↦ ?_
    rw [mul_assoc M₀, Real.sqrt_mul M₀_nonneg]
    ring
  have h1 : |∑' kp, fR w kp| ≤ ∑' kp, Bk w kp := abs_tsum_le hB (fR_le hw)
  have h2 : ∑' kp, Bk w kp ≤ 6 * ∑' k, Real.sqrt (Yr w) * Zr w *
      Real.sqrt (M₀ * Qk w k * Rk' w k) := by
    rw [hB.tsum_prod' hB.prod_factor, ← tsum_mul_left]
    exact hB.prod.tsum_le_tsum (row_le' hRB hw hZ) (hs.mul_left 6)
  have hBn : 0 ≤ ∑' kp, Bk w kp := tsum_nonneg (Bk_nonneg w)
  have e : triadRest w = (1 / 6) * ∑' kp, fR w kp := rfl
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6), ← tsum_mul_left]
  linarith

end OVNS
