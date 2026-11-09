import OddViscousNS.Closed.Row.RowMatrix
import OddViscousNS.Closed.Row.Data.Tabs
import OddViscousNS.Closed.Row.Data.Scal
import OddViscousNS.Closed.Row.Data.Norm

/-!
# Assembling `RowBound` from the kernel data
-/

open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

set_option maxRecDepth 20000
set_option linter.constructorNameAsVariable false

lemma ball_of {i F s} (h : KerR i F s) : Ball 6084 F := h.ball

/-- The six kernels of the tables. -/
theorem tabsOK : TabsOK TT where
  k10 := kerOK_of HH10a_ok HH10b_ok norm10 (ball_of kl10) (ball_of kr10)
  k20 := kerOK_of HH20a_ok HH20b_ok norm20 (ball_of kl20) (ball_of kr20)
  k30 := kerOK_of HH30a_ok HH30b_ok norm30 (ball_of kl30) (ball_of kr30)
  k11 := kerOK_of HH11a_ok HH11b_ok norm11 (ball_of kl11) (ball_of kr11)
  k31 := kerOK_of HH31a_ok HH31b_ok norm31 (ball_of kl31) (ball_of kr31)
  k22 := kerOK_of HH22a_ok HH22b_ok norm22 (ball_of kl22) (ball_of kr22)

/-- The real form of an error check. -/
lemma err_real {F G : ℕ → ℕ} {fg Eb : ℕ} (h : errChk F G fg Eb = true) {s : ℝ} {E : ℚ}
    (hs : s = 2 ^ fg) (hE : E = (Eb : ℚ) / 100000000000000000000) : (errS F G : ℝ) / s ≤ (E : ℝ) := by
  have h1 : Nat.mul (errS F G) 100000000000000000000 ≤ Nat.mul Eb (Nat.shiftLeft 1 fg) :=
    Nat.le_of_ble_eq_true h
  simp only [Nat.mul_eq, shl_eq, one_mul] at h1
  have h2 : ((errS F G * 100000000000000000000 : ℕ) : ℝ) ≤ ((Eb * 2 ^ fg : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  rw [hs, hE]
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- The rounding constants. -/
theorem errOK : ErrOK where
  e10 := err_real err10 (by norm_num) (by unfold E10; norm_num)
  e20 := err_real err20 (by norm_num) (by unfold E20; norm_num)
  e30 := err_real err30 (by norm_num) (by unfold E30; norm_num)
  e31 := err_real err31 (by norm_num) (by unfold E31; norm_num)

/-- A sorted lattice vector, as natural coordinates. -/
lemma sorted_kN {k : Mode} (h : Sorted k) :
    ∃ a b c : ℕ, k = kN a b c ∧ c ≤ b ∧ b ≤ a := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(k 0).toNat, (k 1).toNat, (k 2).toNat, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [kN] <;> omega
  · omega
  · omega

/-- **The row bound for all outputs**, given the rows of the matrix band. -/
theorem realRow_of_rows
    (H : ∀ a b c : ℕ, c ≤ b → b ≤ a → 0 < a → a * a + (b * b + c * c) < 1936 →
      ∃ cK, rowTest TT a b c cK = true) : RealRow gOVNS := by
  refine realRow_of_sorted fun k hk hs w hw => ?_
  obtain ⟨a, b, c, rfl, hcb, hba⟩ := sorted_kN hs
  have hn := nsq_kN a b c
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      have hb0 : b = 0 := by omega
      have hc0 : c = 0 := by omega
      apply hk
      subst h hb0 hc0
      funext i
      fin_cases i <;> simp [kN]
    · exact h
  rcases lt_or_ge (a * a + (b * b + c * c)) 1936 with h1 | h1
  · obtain ⟨cK, hcK⟩ := H a b c hcb hba ha0 h1
    exact row_matrix tabsOK errOK hba hcb ha0 h1 hcK w hw
  · rcases lt_or_ge (a * a + (b * b + c * c)) 10000 with h2 | h2
    · exact row_scal scal_ok normS_ok hcb hba h1 h2 w hw
    · exact rowR_high _ (by rw [hn]; exact h2) w hw

end Row

/-- `RowBound` is monotone. -/
theorem rowBound_mono {g g' : ℕ → ℝ} (h : RowBound g) (hle : ∀ j, g j ≤ g' j) : RowBound g' := by
  intro k hk c hc
  refine (h k hk c hc).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 := Row.hm_nonneg k
  have h2 : 0 ≤ ‖c‖ ^ 2 := by positivity
  have h3 := hle (nsq k)
  have h4 : 36 * g (nsq k) ≤ 36 * g' (nsq k) := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 h1) h2

end OVNS
