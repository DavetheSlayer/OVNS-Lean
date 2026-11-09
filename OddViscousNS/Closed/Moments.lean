import OddViscousNS.Closed.Gram

/-!
# Shell constraints and kinetic bounds (unforced graph, §4 of the U785 reconstruction)

For a mean-zero `H²` field `w` with first-shell mass `x`, second-shell mass `m₂`,
`X = ‖w‖₀²`, `Y = ⟨h(A)w,w⟩`, `Z = ⟨Ah(A)w,w⟩`, `J₁ = ⟨Aw,w⟩`, `Y₂ = h₂ m₂`:
`Y ≥ x + h₂(X − x)`, `Y₂ ≤ Y − x`, `Y₂ ≤ h₂(X − x)`, `Y² ≤ X Z`, `Z ≥ 2Y − x`,
`Z ≥ C Y − D X + L x` (`C = 2988/473`, `D = 1601949/236500`, `L = 344449/236500`), and the four
kinetic bounds `J₁ ≤ Y/.29`, `J₁ ≤ x + (Z − x)/h₂`, `J₁ ≤ x + (Y − x)/.29`,
`J₁ ≤ x + (Z − x)/h₃ + β(X − x)` (`h₂ = 1569/1000`, `h₃ = 1021/500`, `β = 473/1021`).
All are shell inequalities (exact on shells 2 and 3) summed against the shell masses.
-/

open scoped ENNReal

noncomputable section

namespace OVNS

/-- `J₁ = ∑ |k|² ‖w_k‖²`. -/
def J1r (w : Field) : ℝ := ∑' k, absSq k * ‖w k‖ ^ 2

/-- The first-shell mass `x = ∑_{|k|²=1} ‖w_k‖²`. -/
def x1 (w : Field) : ℝ := ∑' k, if nsq k = 1 then ‖w k‖ ^ 2 else 0

/-- The second-shell mass `m₂ = ∑_{|k|²=2} ‖w_k‖²`. -/
def m2 (w : Field) : ℝ := ∑' k, if nsq k = 2 then ‖w k‖ ^ 2 else 0

/-- `Y₂ = h₂ m₂`. -/
def Y2r (w : Field) : ℝ := hmet 2 * m2 w

theorem hmet_two : hmet 2 = 1569 / 1000 := by
  norm_num [hmet, hmetTable]

theorem hmet_three : hmet 3 = 1021 / 500 := by
  norm_num [hmet, hmetTable]

/-- Indicator of `j ≥ 1`. -/
private def fX (j : ℕ) : ℝ := if j = 0 then 0 else 1

/-- Indicator of `j = 1`. -/
private def f1 (j : ℕ) : ℝ := if j = 1 then 1 else 0

/-- Indicator of `j = 2`. -/
private def f2 (j : ℕ) : ℝ := if j = 2 then 1 else 0

/-- `j h(j)`. -/
private def fZ (j : ℕ) : ℝ := (j : ℝ) * hmet j

private lemma fX_of {j : ℕ} (hj : 1 ≤ j) : fX j = 1 := by
  simp [fX, show j ≠ 0 by omega]

private lemma f1_of {j : ℕ} (hj : 2 ≤ j) : f1 j = 0 := by
  simp [f1, show j ≠ 1 by omega]

private lemma one_le_nsq' {k : Mode} (hk : k ≠ 0) : 1 ≤ nsq k :=
  Nat.one_le_iff_ne_zero.2 fun h ↦ hk ((nsq_eq_zero_iff k).1 h)

private lemma sobWeight_two'' {k : Mode} (hk : k ≠ 0) : sobWeight 2 k = (nsq k : ℝ) ^ 2 := by
  have h0 : 0 ≤ absSq k := absSq_nonneg k
  simp only [sobWeight, hk, ↓reduceIte]
  rw [nsq_cast, absk, show (2 : ℝ) * 2 = (4 : ℕ) by norm_num, Real.rpow_natCast,
    show 4 = 2 * 2 by rfl, pow_mul, Real.sq_sqrt h0]

private lemma hmet_ge_two {j : ℕ} (hj : 2 ≤ j) : hmet 2 ≤ hmet j := by
  rcases hj.lt_or_eq with h | h
  · exact (hmet_lt_hmet (by norm_num) h).le
  · rw [h]

private lemma hmet_ge_three {j : ℕ} (hj : 3 ≤ j) : hmet 3 ≤ hmet j := by
  rcases hj.lt_or_eq with h | h
  · exact (hmet_lt_hmet (by norm_num) h).le
  · rw [h]

private lemma abs_le_sq {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (h0 : 0 ≤ x) (h : x ≤ j) :
    |x| ≤ 1 * (j : ℝ) ^ 2 := by
  have : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [abs_of_nonneg h0]; nlinarith

private lemma summ_gen {w : Field} (hw : Adm 2 w) (F : ℕ → ℝ) (C : ℝ)
    (hF : ∀ j, 1 ≤ j → |F j| ≤ C * (j : ℝ) ^ 2) :
    Summable fun k ↦ F (nsq k) * ‖w k‖ ^ 2 := by
  refine Summable.of_norm_bounded (hw.inH.mul_left C) fun k ↦ ?_
  by_cases hk : k = 0
  · subst hk; simp [hw.mean, sobWeight]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖w k‖), sobWeight_two'' hk, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hF _ (one_le_nsq' hk)) (sq_nonneg _)

private lemma term_nonneg {w : Field} (hw : Adm 2 w) (P : ℕ → ℝ)
    (hP : ∀ j, 1 ≤ j → 0 ≤ P j) (k : Mode) : 0 ≤ P (nsq k) * ‖w k‖ ^ 2 := by
  by_cases hk : k = 0
  · subst hk; simp [hw.mean]
  · exact mul_nonneg (hP _ (one_le_nsq' hk)) (sq_nonneg _)

private lemma hasSum_X {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ fX (nsq k) * ‖w k‖ ^ 2) (Xr w) := by
  have h := (summ_gen hw fX 1 fun j hj ↦ abs_le_sq hj (by simp [fX_of hj])
    (by simp [fX_of hj]; exact_mod_cast hj)).hasSum
  convert h using 1
  exact tsum_congr fun k ↦ by by_cases hk : k = 0 <;> simp [fX, hk, nsq_eq_zero_iff]

private lemma hasSum_x1 {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ f1 (nsq k) * ‖w k‖ ^ 2) (x1 w) := by
  have h := (summ_gen hw f1 1 fun j hj ↦ abs_le_sq hj (by unfold f1; split_ifs <;> norm_num)
    (by unfold f1; split_ifs <;> simp; exact_mod_cast hj)).hasSum
  convert h using 1
  exact tsum_congr fun k ↦ by by_cases hk : nsq k = 1 <;> simp [f1, hk]

private lemma hasSum_m2 {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ f2 (nsq k) * ‖w k‖ ^ 2) (m2 w) := by
  have h := (summ_gen hw f2 1 fun j hj ↦ abs_le_sq hj (by unfold f2; split_ifs <;> norm_num)
    (by unfold f2; split_ifs <;> simp; exact_mod_cast hj)).hasSum
  convert h using 1
  exact tsum_congr fun k ↦ by by_cases hk : nsq k = 2 <;> simp [f2, hk]

private lemma hasSum_Y {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ hmet (nsq k) * ‖w k‖ ^ 2) (Yr w) :=
  (summ_gen hw hmet 1 fun j hj ↦ abs_le_sq hj (hmet_pos hj).le (hmet_upper j)).hasSum

private lemma hasSum_J {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ (fun j : ℕ ↦ (j : ℝ)) (nsq k) * ‖w k‖ ^ 2) (J1r w) := by
  have h := (summ_gen hw (fun j : ℕ ↦ (j : ℝ)) 1 fun j hj ↦
    abs_le_sq hj (Nat.cast_nonneg j) le_rfl).hasSum
  convert h using 1
  exact tsum_congr fun k ↦ by simp [nsq_cast]

private lemma hasSum_Z {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ fZ (nsq k) * ‖w k‖ ^ 2) (Zr w) := by
  have h := (summ_gen hw fZ 1 fun j hj ↦ by
    have h1 := hmet_upper j
    have h2 := (hmet_pos hj).le
    have h3 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [fZ, abs_of_nonneg (mul_nonneg h3 h2)]; nlinarith).hasSum
  convert h using 1
  exact tsum_congr fun k ↦ by simp [fZ, nsq_cast, hm]

private lemma hasSum_S {w : Field} (hw : Adm 2 w) :
    HasSum (fun k ↦ (fun j : ℕ ↦ (j : ℝ) ^ 2) (nsq k) * ‖w k‖ ^ 2) (hnorm 2 w ^ 2) := by
  have h := (summ_gen hw (fun j : ℕ ↦ (j : ℝ) ^ 2) 1 fun j _ ↦ by
    rw [abs_of_nonneg (sq_nonneg _), one_mul]).hasSum
  have e : (∑' k, sobWeight 2 k * ‖w k‖ ^ 2) = ∑' k, (fun j : ℕ ↦ (j : ℝ) ^ 2) (nsq k) *
      ‖w k‖ ^ 2 := tsum_congr fun k ↦ by
    by_cases hk : k = 0
    · subst hk; simp [hw.mean]
    · rw [sobWeight_two'' hk]
  rw [hnorm, Real.sq_sqrt, e]
  · exact h
  · rw [e]; exact h.nonneg fun k ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)

private lemma f2_of {j : ℕ} (hj : 3 ≤ j) : f2 j = 0 := by
  simp [f2, show j ≠ 2 by omega]

private lemma cases_j {j : ℕ} (hj : 1 ≤ j) : j = 1 ∨ j = 2 ∨ 3 ≤ j := by omega

private lemma pw_X_le_Y : ∀ j, 1 ≤ j → 0 ≤ hmet j - fX j := fun j hj ↦ by
  rw [fX_of hj]
  rcases hj.lt_or_eq with h | h
  · have := hmet_lt_hmet le_rfl h; rw [hmet_one] at this; linarith
  · subst h; rw [hmet_one]; norm_num

private lemma pw_Y_le_Z : ∀ j, 1 ≤ j → 0 ≤ fZ j - hmet j := fun j hj ↦ by
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h2 := (hmet_pos hj).le
  rw [fZ]; nlinarith

private lemma pw_x1_le_X : ∀ j, 1 ≤ j → 0 ≤ fX j - f1 j := fun j hj ↦ by
  rw [fX_of hj]; unfold f1; split_ifs <;> norm_num

private lemma pw_X_le_S : ∀ j : ℕ, 1 ≤ j → 0 ≤ (j : ℝ) ^ 2 - fX j := fun j hj ↦ by
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [fX_of hj]; nlinarith

private lemma pw_three : ∀ j, 1 ≤ j → 0 ≤ 2 * fX j + (j : ℝ) ^ 2 - 3 * hmet j := fun j hj ↦ by
  have := hmet_le_quad j
  rw [fX_of hj]; linarith

private lemma pw_shell : ∀ j, 1 ≤ j → 0 ≤ hmet j - (f1 j + hmet 2 * (fX j - f1 j)) :=
  fun j hj ↦ by
  rcases cases_j hj with rfl | rfl | h3
  · simp [f1, fX, hmet_one]
  · simp [f1, fX]
  · rw [fX_of hj, f1_of (by omega)]; have := hmet_ge_two (j := j) (by omega); linarith

private lemma pw_Y2a : ∀ j, 1 ≤ j → 0 ≤ hmet j - f1 j - hmet 2 * f2 j := fun j hj ↦ by
  rcases cases_j hj with rfl | rfl | h3
  · simp [f1, f2, hmet_one]
  · simp [f1, f2]
  · rw [f1_of (by omega), f2_of h3]; have := hmet_pos hj; linarith

private lemma pw_Y2b : ∀ j, 1 ≤ j → 0 ≤ hmet 2 * (fX j - f1 j) - hmet 2 * f2 j :=
  fun j hj ↦ by
  rcases cases_j hj with rfl | rfl | h3
  · simp [f1, f2, fX]
  · simp [f1, f2, fX]
  · rw [fX_of hj, f1_of (by omega), f2_of h3]; have := hmet_pos (j := 2) (by norm_num)
    linarith

private lemma pw_quad (t : ℝ) : ∀ j, 1 ≤ j → 0 ≤ t ^ 2 * fX j + fZ j - 2 * t * hmet j :=
  fun j hj ↦ by
  have h1 := hmet_upper j
  have h2 := (hmet_pos hj).le
  rw [fX_of hj, fZ]
  nlinarith [sq_nonneg (t - hmet j), mul_le_mul_of_nonneg_right h1 h2]

private lemma pw_two_Y : ∀ j, 1 ≤ j → 0 ≤ fZ j - (2 * hmet j - f1 j) := fun j hj ↦ by
  rcases cases_j hj with rfl | rfl | h3
  · norm_num [f1, fZ, hmet_one]
  · rw [f1_of le_rfl, fZ]; norm_num
  · have h1 : (3 : ℝ) ≤ j := by exact_mod_cast h3
    have h2 := (hmet_pos hj).le
    rw [f1_of (by omega), fZ]; nlinarith

private lemma pw_line : ∀ j, 1 ≤ j →
    0 ≤ fZ j - (2988 / 473 * hmet j - 1601949 / 236500 * fX j + 344449 / 236500 * f1 j) :=
  fun j hj ↦ by
  rcases le_or_gt j 32 with h | h
  · interval_cases j <;> norm_num [fZ, fX, f1, hmet, hmetTable]
  · have h1 : (33 : ℝ) ≤ j := by exact_mod_cast h
    rw [fX_of hj, f1_of (by omega), fZ, hmet_affine (by omega)]
    nlinarith

private lemma pw_k1 : ∀ j, 1 ≤ j → 0 ≤ hmet j / (29 / 100) - j := fun j hj ↦ by
  have := hmet_lower hj; linarith

private lemma pw_k2 : ∀ j, 1 ≤ j → 0 ≤ f1 j + (fZ j - f1 j) / (1569 / 1000) - j :=
  fun j hj ↦ by
  rcases cases_j hj with rfl | h2 | h3
  · simp [f1, fZ, hmet_one]
  all_goals
    have hj2 : 2 ≤ j := by omega
    have h1 : (2 : ℝ) ≤ j := by exact_mod_cast hj2
    have := hmet_ge_two hj2
    rw [hmet_two] at this
    rw [f1_of hj2, fZ]; nlinarith

private lemma pw_k3 : ∀ j, 1 ≤ j → 0 ≤ f1 j + (hmet j - f1 j) / (29 / 100) - j :=
  fun j hj ↦ by
  rcases cases_j hj with rfl | h2 | h3
  · simp [f1, hmet_one]
  all_goals
    have hj2 : 2 ≤ j := by omega
    have := hmet_lower hj
    rw [f1_of hj2]; linarith

private lemma pw_k4 : ∀ j, 1 ≤ j →
    0 ≤ f1 j + (fZ j - f1 j) / (1021 / 500) + 473 / 1021 * (fX j - f1 j) - j := fun j hj ↦ by
  rcases cases_j hj with rfl | rfl | h3
  · simp [f1, fZ, fX, hmet_one]
  · rw [f1_of le_rfl, fX_of (by norm_num), fZ, hmet_two]; norm_num
  · have h1 : (3 : ℝ) ≤ j := by exact_mod_cast h3
    have := hmet_ge_three h3
    rw [hmet_three] at this
    rw [f1_of (by omega), fX_of hj, fZ]; nlinarith

private lemma pos_term {w : Field} (hw : Adm 2 w) (hne : w ≠ 0) (P : ℕ → ℝ)
    (hP : ∀ j, 1 ≤ j → 0 < P j) {a : ℝ}
    (ha : HasSum (fun k ↦ P (nsq k) * ‖w k‖ ^ 2) a) : 0 < a := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
  have hk0 : k ≠ 0 := by rintro rfl; exact hk hw.mean
  refine lt_of_lt_of_le ?_ (le_hasSum ha k fun j _ ↦ term_nonneg hw P (fun j hj ↦ (hP j hj).le) j)
  exact mul_pos (hP _ (one_le_nsq' hk0)) (pow_pos (norm_pos_iff.2 hk) 2)

section
variable {w : Field} (hw : Adm 2 w)
include hw

theorem summable_X : Summable fun k => (if k = 0 then (0 : ℝ) else ‖w k‖ ^ 2) := by
  exact (hasSum_X hw).summable.congr fun k ↦ by
    by_cases hk : k = 0 <;> simp [fX, hk, nsq_eq_zero_iff]

theorem summable_Y : Summable fun k => hm k * ‖w k‖ ^ 2 := by
  exact (hasSum_Y hw).summable

theorem summable_Z : Summable fun k => absSq k * hm k * ‖w k‖ ^ 2 := by
  exact (hasSum_Z hw).summable.congr fun k ↦ by simp [fZ, nsq_cast, hm]

theorem summable_J1 : Summable fun k => absSq k * ‖w k‖ ^ 2 := by
  exact (hasSum_J hw).summable.congr fun k ↦ by simp [nsq_cast]

theorem Xr_nonneg : 0 ≤ Xr w := by
  exact (hasSum_X hw).nonneg fun k ↦ term_nonneg hw fX
    (fun j hj ↦ by rw [fX_of hj]; norm_num) k

theorem x1_nonneg : 0 ≤ x1 w := by
  exact (hasSum_x1 hw).nonneg fun k ↦ term_nonneg hw f1
    (fun j _ ↦ by unfold f1; split_ifs <;> norm_num) k

theorem m2_nonneg : 0 ≤ m2 w := by
  exact (hasSum_m2 hw).nonneg fun k ↦ term_nonneg hw f2
    (fun j _ ↦ by unfold f2; split_ifs <;> norm_num) k

theorem x1_le_Xr : x1 w ≤ Xr w := by
  have h := ((hasSum_X hw).sub (hasSum_x1 hw)).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_x1_le_X k
    linarith
  linarith

theorem Xr_le_Yr : Xr w ≤ Yr w := by
  have h := ((hasSum_Y hw).sub (hasSum_X hw)).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_X_le_Y k
    linarith
  linarith

theorem Yr_le_Zr : Yr w ≤ Zr w := by
  have h := ((hasSum_Z hw).sub (hasSum_Y hw)).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_Y_le_Z k
    linarith
  linarith

/-- `X ≤ ‖w‖₂²`. -/
theorem Xr_le_hnorm_sq : Xr w ≤ hnorm 2 w ^ 2 := by
  have h := ((hasSum_S hw).sub (hasSum_X hw)).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_X_le_S k
    linarith
  linarith

/-- `3Y ≤ 2X + ‖w‖₂²`. -/
theorem three_Yr_le : 3 * Yr w ≤ 2 * Xr w + hnorm 2 w ^ 2 := by
  have h := ((((hasSum_X hw).mul_left 2).add (hasSum_S hw)).sub ((hasSum_Y hw).mul_left 3)).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_three k
    linarith
  linarith

/-- 4.1: `Y ≥ x + h₂(X − x)`. -/
theorem Yr_ge_shell : x1 w + hmet 2 * (Xr w - x1 w) ≤ Yr w := by
  have h := ((hasSum_Y hw).sub ((hasSum_x1 hw).add (((hasSum_X hw).sub (hasSum_x1 hw)).mul_left (hmet 2)))).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_shell k
    linarith
  linarith

/-- 4.2: `Y₂ ≤ Y − x` and `Y₂ ≤ h₂(X − x)`. -/
theorem Y2r_le_Yr_sub : Y2r w ≤ Yr w - x1 w := by
  unfold Y2r
  have h := (((hasSum_Y hw).sub (hasSum_x1 hw)).sub ((hasSum_m2 hw).mul_left (hmet 2))).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_Y2a k
    linarith
  linarith

theorem Y2r_le_h2_X : Y2r w ≤ hmet 2 * (Xr w - x1 w) := by
  unfold Y2r
  have h := ((((hasSum_X hw).sub (hasSum_x1 hw)).mul_left (hmet 2)).sub ((hasSum_m2 hw).mul_left (hmet 2))).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_Y2b k
    linarith
  linarith

/-- 4.3: `Y² ≤ X Z`. -/
theorem Yr_sq_le : Yr w ^ 2 ≤ Xr w * Zr w := by
  have key : ∀ t : ℝ, 2 * t * Yr w ≤ t ^ 2 * Xr w + Zr w := fun t ↦ by
    have h := ((((hasSum_X hw).mul_left (t ^ 2)).add (hasSum_Z hw)).sub
      ((hasSum_Y hw).mul_left (2 * t))).nonneg fun k ↦ by
      have := term_nonneg hw _ (pw_quad t) k
      linarith
    linarith
  have hX := Xr_nonneg hw
  have hY : 0 ≤ Yr w := le_trans hX (Xr_le_Yr hw)
  rcases hX.lt_or_eq with hX | hX
  · have := key (Yr w / Xr w)
    have e : 2 * (Yr w / Xr w) * Yr w = (Yr w / Xr w) ^ 2 * Xr w + Yr w ^ 2 / Xr w := by
      field_simp; ring
    rw [e] at this
    have h3 : Yr w ^ 2 / Xr w ≤ Zr w := by linarith
    rwa [div_le_iff₀ hX, mul_comm] at h3
  · rw [← hX]
    rcases hY.lt_or_eq with hY | hY
    · have := key ((Zr w + 1) / (2 * Yr w))
      rw [← hX] at this
      have e : 2 * ((Zr w + 1) / (2 * Yr w)) * Yr w = Zr w + 1 := by field_simp
      linarith
    · rw [← hY]; norm_num

/-- 4.4: `Z ≥ 2Y − x`. -/
theorem Zr_ge_two_Y : 2 * Yr w - x1 w ≤ Zr w := by
  have h := ((hasSum_Z hw).sub (((hasSum_Y hw).mul_left 2).sub (hasSum_x1 hw))).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_two_Y k
    linarith
  linarith

/-- 4.5: `Z ≥ C Y − D X + L x`. -/
theorem Zr_ge_line :
    2988 / 473 * Yr w - 1601949 / 236500 * Xr w + 344449 / 236500 * x1 w ≤ Zr w := by
  have h := ((hasSum_Z hw).sub ((((hasSum_Y hw).mul_left (2988 / 473)).sub ((hasSum_X hw).mul_left (1601949 / 236500))).add ((hasSum_x1 hw).mul_left (344449 / 236500)))).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_line k
    linarith
  linarith

/-- 4.6 (k₁): `J₁ ≤ Y/.29`. -/
theorem J1r_le_k1 : J1r w ≤ Yr w / (29 / 100) := by
  have h := (((hasSum_Y hw).div_const (29 / 100)).sub (hasSum_J hw)).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_k1 k
    linarith
  linarith

/-- 4.6 (k₂): `J₁ ≤ x + (Z − x)/h₂`. -/
theorem J1r_le_k2 : J1r w ≤ x1 w + (Zr w - x1 w) / hmet 2 := by
  rw [hmet_two]
  have h := (((hasSum_x1 hw).add (((hasSum_Z hw).sub (hasSum_x1 hw)).div_const (1569 / 1000))).sub (hasSum_J hw)).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_k2 k
    linarith
  linarith

/-- 4.6 (k₃): `J₁ ≤ x + (Y − x)/.29`. -/
theorem J1r_le_k3 : J1r w ≤ x1 w + (Yr w - x1 w) / (29 / 100) := by
  have h := (((hasSum_x1 hw).add (((hasSum_Y hw).sub (hasSum_x1 hw)).div_const (29 / 100))).sub (hasSum_J hw)).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_k3 k
    linarith
  linarith

/-- 4.6 (k₄): `J₁ ≤ x + (Z − x)/h₃ + β(X − x)`. -/
theorem J1r_le_k4 :
    J1r w ≤ x1 w + (Zr w - x1 w) / hmet 3 + 473 / 1021 * (Xr w - x1 w) := by
  rw [hmet_three]
  have h := ((((hasSum_x1 hw).add (((hasSum_Z hw).sub (hasSum_x1 hw)).div_const (1021 / 500))).add (((hasSum_X hw).sub (hasSum_x1 hw)).mul_left (473 / 1021))).sub (hasSum_J hw)).nonneg fun k ↦ by
    have := term_nonneg hw _ pw_k4 k
    linarith
  linarith

/-- `Y = 0` only for the zero field (so `Y, Z > 0` for nonzero admissible fields). -/
theorem Yr_pos_of_ne (hne : w ≠ 0) : 0 < Yr w := by
  exact pos_term hw hne hmet (fun j hj ↦ hmet_pos hj) (hasSum_Y hw)

theorem Zr_pos_of_ne (hne : w ≠ 0) : 0 < Zr w := by
  exact pos_term hw hne fZ (fun j hj ↦ mul_pos (by exact_mod_cast hj) (hmet_pos hj))
    (hasSum_Z hw)

end

end OVNS
