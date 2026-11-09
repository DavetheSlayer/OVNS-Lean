import OddViscousNS.Closed.Row.Radial
import OddViscousNS.Closed.Row.Pair
import OddViscousNS.Closed.Row.ScalK

/-!
# The kernel tables against the definitions: `metric`, `root`, `gN`, `FA`
-/

open Finset

noncomputable section

namespace OVNS
namespace Row

lemma le_cdiv (n d : ℕ) (hd : 0 < d) : n ≤ cdiv n d * d := by
  unfold cdiv
  show n ≤ (n + (d - 1)) / d * d
  have h1 := Nat.div_add_mod (n + (d - 1)) d
  have h2 := Nat.mod_lt (n + (d - 1)) hd
  rw [mul_comm]
  omega

/-- A real quotient below the ceiling. -/
lemma div_le_cdiv (n d : ℕ) (hd : 0 < d) : (n : ℝ) / d ≤ cdiv n d := by
  have h := le_cdiv n d hd
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast h

/-- `metric` is the table of `h`. -/
lemma metric_low : ∀ j, 1 ≤ j → j ≤ 32 → (metric j : ℕ) = hmetTable.getD (j - 1) 0 := by
  intro j h1 h2
  interval_cases j <;> decide +kernel

lemma metric_high {j : ℕ} (h : 33 ≤ j) : metric j = 290 * j + 234 := by
  unfold metric
  have e : Nat.ble j 32 = false := by
    rw [← Bool.not_eq_true]; intro h'; have := Nat.le_of_ble_eq_true h'; omega
  rw [e]
  rfl

/-- `hmet j = metric j / 1000` for `j ≥ 1`. -/
theorem metric_spec {j : ℕ} (h : 1 ≤ j) : hmet j = (metric j : ℝ) / 1000 := by
  rcases le_or_gt j 32 with h2 | h2
  · unfold hmet
    rw [metric_low j h h2]
    simp [show j ≠ 0 by omega, h2]
  · rw [hmet_affine (by omega), metric_high (by omega)]
    push_cast
    ring

/-- `lamW` as a natural number. -/
def lamN (j : ℕ) : ℕ :=
  match lamEdges.findIdx? (fun e => decide (j ≤ e)) with
  | some i => lamVals.getD i 100000
  | none => 100000

lemma lamW_eq (j : ℕ) : lamW j = (lamN j : ℝ) / 100000 := by
  unfold lamW lamN
  cases h : List.findIdx? (fun e => decide (j ≤ e)) lamEdges with
  | none => norm_num
  | some i => rfl

lemma root_low : ∀ j, j < 121 → root j = lamN j := by decide +kernel

lemma root_high {j : ℕ} (h : 120 < j) : root j = 100000 := by
  unfold root
  have e : Nat.ble j 120 = false := by
    rw [← Bool.not_eq_true]; intro h'; have := Nat.le_of_ble_eq_true h'; omega
  rw [e]

/-- `lamW j = root j / 10⁵`. -/
theorem root_spec (j : ℕ) : lamW j = (root j : ℝ) / 100000 := by
  rcases le_or_gt j 120 with h | h
  · rw [root_low j (by omega), lamW_eq]
  · rw [root_high h, lamW_gt h]
    norm_num

/-- `root` is positive. -/
lemma root_pos_all : ∀ j, j < 121 → 0 < root j := by decide +kernel

lemma root_pos (j : ℕ) : 0 < root j := by
  rcases le_or_gt j 120 with h | h
  · exact root_pos_all j (by omega)
  · rw [root_high h]; norm_num

lemma metric_pos {j : ℕ} (h : 1 ≤ j) : 0 < metric j := by
  have h1 := hmet_pos h
  rw [metric_spec h] at h1
  have : (0 : ℝ) < metric j := by linarith
  exact_mod_cast this

/-- The check of `gN` against `gTableN`. -/
def gChk (C : ℕ) : Bool :=
  match gTableN.find? (fun e => e.1 == C) with
  | some e => e.2 == gN C
  | none => gN C == 0

set_option maxRecDepth 100000 in
theorem gChk_all : ∀ C, C < 1024 → gChk C = true := by decide +kernel

lemma gN_low {C : ℕ} (h : C < 1024) : (gN C : ℝ) / 1000000000 ≤ gOVNS C := by
  unfold gOVNS
  simp only [h, ↓reduceIte]
  have hc := gChk_all C h
  unfold gChk at hc
  unfold gTable
  split at hc
  · rename_i e he
    have := Nat.eq_of_beq_eq_true hc
    rw [he]
    show (gN C : ℝ) / 1000000000 ≤ (e.2 : ℝ) / 1000000000
    rw [this]
  · rename_i he
    have h0 : gN C = 0 := Nat.eq_of_beq_eq_true hc
    rw [he, h0]
    norm_num [M₀]

lemma gN_mid {C : ℕ} (h1 : 1024 ≤ C) (h2 : C < 3600) : gN C = 172754764 := by
  unfold gN
  have e1 : Nat.ble C 1023 = false := by
    rw [← Bool.not_eq_true]; intro h'; have := Nat.le_of_ble_eq_true h'; omega
  have e2 : Nat.ble 3600 C = false := by
    rw [← Bool.not_eq_true]; intro h'; have := Nat.le_of_ble_eq_true h'; omega
  rw [e1, e2]

lemma gN_high {C : ℕ} (h2 : 3600 ≤ C) : gN C = 163043000 := by
  unfold gN
  have e1 : Nat.ble C 1023 = false := by
    rw [← Bool.not_eq_true]; intro h'; have := Nat.le_of_ble_eq_true h'; omega
  have e2 : Nat.ble 3600 C = true := Nat.ble_eq_true_of_le h2
  rw [e1, e2]

/-- `gN` is below the price. -/
theorem gN_le (C : ℕ) : (gN C : ℝ) / 1000000000 ≤ gOVNS C := by
  rcases lt_or_ge C 1024 with h | h
  · exact gN_low h
  · rcases lt_or_ge C 3600 with h2 | h2
    · rw [gN_mid h h2]
      unfold gOVNS
      simp only [show ¬ C < 1024 by omega, h2, ↓reduceIte]
      norm_num
    · rw [gN_high h2]
      unfold gOVNS
      simp only [show ¬ C < 1024 by omega, show ¬ C < 3600 by omega, ↓reduceIte]
      norm_num

/-- `a(n) ≤ FA(n)/2²¹`. -/
theorem aa_le_FA {n : ℕ} (h0 : 0 < n) (h1 : n ≤ 16384) : aa n ≤ (FA n : ℝ) / 2097152 := by
  unfold aa vv
  have hr := root_spec n
  have hr0 : (0 : ℝ) < root n := by exact_mod_cast root_pos n
  have hn : (0 : ℝ) < n := by exact_mod_cast h0
  unfold FA
  rw [cut_eq]
  simp only [h0, h1, and_self, ↓reduceIte, lit_eq, hr, Nat.mul_eq, Nat.add_eq]
  set u := 200000 + root n with hu
  have hu0 : 0 < u := by omega
  have hd : 0 < u * u * n := by positivity
  have h2 := div_le_cdiv 188743680000000000 (u * u * n) hd
  have hu1 : (2 + (root n : ℝ) / 100000) = (u : ℝ) / 100000 := by
    rw [hu]; push_cast; ring
  have hu2 : (0 : ℝ) < u := by exact_mod_cast hu0
  have e : 9 / (2 + (root n : ℝ) / 100000) ^ 2 / (n : ℝ) =
      ((188743680000000000 : ℕ) : ℝ) / ((u * u * n : ℕ) : ℝ) / 2097152 := by
    rw [hu1]
    push_cast
    field_simp
    norm_num
  rw [e]
  exact div_le_div_of_nonneg_right h2 (by norm_num)

end Row
end OVNS
