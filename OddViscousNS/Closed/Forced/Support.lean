import OddViscousNS.Closed.Forced.Defs

/-!
# The spectral support lemma and its infinite tail (§2 of the forced reconstruction)

Shell form: if `F(j) + c h(j) ≤ M` for every `j ≥ 1`, where
`F(j) = ε((r + m h(j))/j)² − r j − mH j h(j)`, then for every admissible `w`
`−r J₁ − mH Z + ε N² ≤ M X − c Y` (sum the shell inequality against the shell masses).
Tail: for `j ≥ 33`, `h` is affine and the force part is non-increasing in `j` (`r, m ≥ 0`), while
the remaining quadratic has forward difference `c a_h − d b_h − r − d a_h(2j+1)` (`d = mH`),
strictly decreasing; so `G(j) = F(j) + c h(j)` is non-increasing beyond any `J₀ ≥ 33` with
`c a_h − d b_h − r − d a_h (2J₀+1) ≤ 0`, and a finite maximum over `j ≤ J₀` bounds all `j`.
-/

namespace OVNS

namespace Forced

/-- Indicator of `j ≥ 1`. -/
private def fX (j : ℕ) : ℝ := if j = 0 then 0 else 1

/-- `j h(j)`. -/
private noncomputable def fZ (j : ℕ) : ℝ := (j : ℝ) * hmet j

/-- The support weight on shells. -/
private noncomputable def fN (r m : ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else ((r + m * hmet j) / j) ^ 2

private lemma oneLeNsq {k : Mode} (hk : k ≠ 0) : 1 ≤ nsq k :=
  Nat.one_le_iff_ne_zero.2 fun h ↦ hk ((nsq_eq_zero_iff k).1 h)

private lemma sobW2 {k : Mode} (hk : k ≠ 0) : sobWeight 2 k = (nsq k : ℝ) ^ 2 := by
  have h0 : 0 ≤ absSq k := absSq_nonneg k
  simp only [sobWeight, hk, ↓reduceIte]
  rw [nsq_cast, absk, show (2 : ℝ) * 2 = (4 : ℕ) by norm_num, Real.rpow_natCast,
    show 4 = 2 * 2 by rfl, pow_mul, Real.sq_sqrt h0]

private lemma summGen {w : Field} (hw : Adm 2 w) (F : ℕ → ℝ) (C : ℝ)
    (hF : ∀ j, 1 ≤ j → |F j| ≤ C * (j : ℝ) ^ 2) :
    Summable fun k ↦ F (nsq k) * ‖w k‖ ^ 2 := by
  refine Summable.of_norm_bounded (hw.inH.mul_left C) fun k ↦ ?_
  by_cases hk : k = 0
  · subst hk; simp [hw.mean, sobWeight]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖w k‖), sobW2 hk, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hF _ (oneLeNsq hk)) (sq_nonneg _)

private lemma absLeSq {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (h0 : 0 ≤ x) (h : x ≤ j) :
    |x| ≤ 1 * (j : ℝ) ^ 2 := by
  have : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [abs_of_nonneg h0]; nlinarith

private lemma hasSumX {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ fX (nsq k) * ‖w k‖ ^ 2) (Xr w) := by
  have h := (summGen hw fX 1 fun j hj ↦ absLeSq hj
    (by simp [fX, show j ≠ 0 by omega])
    (by simp [fX, show j ≠ 0 by omega]; exact_mod_cast hj)).hasSum
  convert h using 1
  exact tsum_congr fun k ↦ by by_cases hk : k = 0 <;> simp [fX, hk, nsq_eq_zero_iff]

private lemma hasSumY {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ hmet (nsq k) * ‖w k‖ ^ 2) (Yr w) :=
  (summGen hw hmet 1 fun j hj ↦ absLeSq hj (hmet_pos hj).le (hmet_upper j)).hasSum

private lemma hasSumJ {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ (fun j : ℕ ↦ (j : ℝ)) (nsq k) * ‖w k‖ ^ 2) (J1r w) := by
  have h := (summGen hw (fun j : ℕ ↦ (j : ℝ)) 1 fun j hj ↦
    absLeSq hj (Nat.cast_nonneg j) le_rfl).hasSum
  convert h using 1
  exact tsum_congr fun k ↦ by simp [nsq_cast]

private lemma hasSumZ {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ fZ (nsq k) * ‖w k‖ ^ 2) (Zr w) := by
  have h := (summGen hw fZ 1 fun j hj ↦ by
    have h1 := hmet_upper j
    have h2 := (hmet_pos hj).le
    have h3 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [fZ, abs_of_nonneg (mul_nonneg h3 h2)]; nlinarith).hasSum
  convert h using 1
  exact tsum_congr fun k ↦ by simp [fZ, nsq_cast, hm]

private lemma fN_le {r m : ℝ} (hr : 0 ≤ r) (hm : 0 ≤ m) {j : ℕ} (hj : 1 ≤ j) :
    |fN r m j| ≤ (r + m) ^ 2 * (j : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hu := hmet_upper j
  have hp := (hmet_pos hj).le
  rw [fN]
  simp only [show j ≠ 0 by omega, ↓reduceIte]
  rw [abs_of_nonneg (sq_nonneg _)]
  have hb0 : 0 ≤ (r + m * hmet j) / j := div_nonneg (by positivity) (by positivity)
  have hb : (r + m * hmet j) / j ≤ r + m := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have : ((r + m * hmet j) / j) ^ 2 ≤ (r + m) ^ 2 := pow_le_pow_left₀ hb0 hb 2
  have h2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ h1
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg (r + m))]

private lemma hasSumN {r m : ℝ} (hr : 0 ≤ r) (hm : 0 ≤ m) {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ fN r m (nsq k) * ‖w k‖ ^ 2) (Nsq r m w) := by
  have h := (summGen hw (fN r m) _ fun j hj ↦ fN_le hr hm hj).hasSum
  convert h using 1
  refine tsum_congr fun k ↦ ?_
  by_cases hk : k = 0
  · simp [fN, hk, nsq_eq_zero_iff]
  · have hk' : nsq k ≠ 0 := fun h ↦ hk ((nsq_eq_zero_iff k).1 h)
    simp [fN, hk, hk', nsq_cast, OVNS.hm]

/-- Shell form of the support lemma. -/
theorem support_shells {r m H ε c M : ℝ} (hr : 0 ≤ r) (hm : 0 ≤ m)
    (hS : ∀ j : ℕ, 1 ≤ j → Fsh r m H ε j + c * hmet j ≤ M) {w : Field} (hw : Adm 2 w) :
    -r * J1r w - m * H * Zr w + ε * Nsq r m w ≤ M * Xr w - c * Yr w := by
  have hL := (((hasSumJ hw).mul_left (-r)).sub ((hasSumZ hw).mul_left (m * H))).add
    ((hasSumN hr hm hw).mul_left ε)
  have hR := ((hasSumX hw).mul_left M).sub ((hasSumY hw).mul_left c)
  refine hasSum_le (fun k ↦ ?_) hL hR
  by_cases hk : k = 0
  · subst hk; simp [hw.mean]
  · have hj := oneLeNsq hk
    have ha : 0 ≤ ‖w k‖ ^ 2 := sq_nonneg _
    generalize nsq k = j at hj ⊢
    generalize ‖w k‖ ^ 2 = a at ha ⊢
    have h := mul_le_mul_of_nonneg_right (hS j hj) ha
    simp only [Fsh, fN, fX, fZ, show j ≠ 0 by omega, ↓reduceIte] at h ⊢
    linarith

/-- Young once: `f₀ N ≤ f₀²/(4ε) + ε N²` for `ε > 0`, `N ≥ 0`. -/
theorem young_force {f N ε : ℝ} (hε : 0 < ε) (_hN : 0 ≤ N) : f * N ≤ f ^ 2 / (4 * ε) + ε * N ^ 2 := by
  have h : f * N * (4 * ε) ≤ f ^ 2 + ε * N ^ 2 * (4 * ε) := by
    nlinarith [sq_nonneg (f - 2 * ε * N)]
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  linarith

/-- The tail lemma under the (necessary) sign condition `0 ≤ ε`. -/
theorem support_tail {r m H ε c : ℝ} (hr : 0 ≤ r) (hm : 0 ≤ m) (hε : 0 ≤ ε)
    (hd : 0 < m * H) {J₀ : ℕ} (hJ : 33 ≤ J₀)
    (hΔ : c * (29 / 100) - m * H * (117 / 500) - r - m * H * (29 / 100) * (2 * J₀ + 1) ≤ 0) :
    ∀ j : ℕ, J₀ ≤ j → Fsh r m H ε (j + 1) + c * hmet (j + 1) ≤ Fsh r m H ε j + c * hmet j := by
  intro j hj
  have hJr : (J₀ : ℝ) ≤ j := by exact_mod_cast hj
  have hx : (33 : ℝ) ≤ j := by exact_mod_cast hJ.trans hj
  rw [hmet_affine (show 33 ≤ j + 1 by omega), hmet_affine (show 33 ≤ j by omega)]
  simp only [Fsh, Nat.cast_add, Nat.cast_one]
  rw [hmet_affine (show 33 ≤ j + 1 by omega), hmet_affine (show 33 ≤ j by omega)]
  simp only [Nat.cast_add, Nat.cast_one]
  generalize (j : ℝ) = x at hJr hx ⊢
  have hb0 : 0 ≤ (r + m * (29 * (x + 1) / 100 + 117 / 500)) / (x + 1) :=
    div_nonneg (by positivity) (by linarith)
  have hb : (r + m * (29 * (x + 1) / 100 + 117 / 500)) / (x + 1) ≤
      (r + m * (29 * x / 100 + 117 / 500)) / x := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hf := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb 2) hε
  nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.2 hJr) hd.le]

/-- `(S)` from a finite maximum, under the (necessary) sign condition `0 ≤ ε`. -/
theorem support_of_finite {r m H ε c M : ℝ} (hr : 0 ≤ r) (hm : 0 ≤ m) (hε : 0 ≤ ε)
    (hd : 0 < m * H) {J₀ : ℕ} (hJ : 33 ≤ J₀)
    (hΔ : c * (29 / 100) - m * H * (117 / 500) - r - m * H * (29 / 100) * (2 * J₀ + 1) ≤ 0)
    (hfin : ∀ j : ℕ, 1 ≤ j → j ≤ J₀ → Fsh r m H ε j + c * hmet j ≤ M) :
    ∀ j : ℕ, 1 ≤ j → Fsh r m H ε j + c * hmet j ≤ M := by
  have key : ∀ n : ℕ, J₀ ≤ n → Fsh r m H ε n + c * hmet n ≤ M := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hfin J₀ (by omega) le_rfl
    | succ n hn ih => exact (support_tail hr hm hε hd hJ hΔ n hn).trans ih
  intro j hj
  rcases le_or_gt j J₀ with h | h
  · exact hfin j hj h
  · exact key j h.le

end Forced

end OVNS
