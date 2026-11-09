import OddViscousNS.Closed.Row.Split
import OddViscousNS.Closed.Row.Tables
import OddViscousNS.Closed.Row.Scal

/-!
# Specification of the direct low zone

`lowSum` is the packed sum, over the low points, of the two ceilings `f₁, f₂` times the three squares
`(p·r)²`, `(p·s)²`, `(p·(r+s))²`, with `r = (-b,a,0)`, `s = k × r`, `k = (a,b,c)`.  Each slot is
below the base, and the ceilings dominate the true weights `w1`, `w2`.
-/

open Finset

noncomputable section

namespace OVNS
namespace Row

set_option maxRecDepth 20000
set_option linter.constructorNameAsVariable false

lemma sqd_cast (a b : ℕ) : (sqd a b : ℤ) = ((a : ℤ) - b) ^ 2 := by
  unfold sqd
  rw [lit_eq]
  show (((a - b + (b - a)) * (a - b + (b - a)) : ℕ) : ℤ) = _
  rcases le_total a b with h | h
  · have e1 : a - b = 0 := by omega
    rw [e1]; push_cast [Nat.cast_sub h]; ring
  · have e1 : b - a = 0 := by omega
    rw [e1]; push_cast [Nat.cast_sub h]; ring

lemma sqd_ten (i : ℕ) : sqd i 10 = sq 10 i := by
  zify
  rw [sqd_cast, sq_cast]

/-- `n₁`. -/
def nOne (A B HA HB HC : ℕ) : ℕ := B * sqd HC HB + A * sqd HA HC

/-- `n₂`. -/
def nTwo (A B C HA HB HC : ℕ) : ℕ :=
  sqd (A * HC + (B * HA + C * HB)) (A * HB + (B * HC + C * HA)) + A * B * sqd HA HB

/-- The denominator. -/
def denL (A B HA HB rr : ℕ) : ℕ := rr * rr * (A * A * (B * B) * (HA * HB))

/-- The integer weight of a low point. -/
def wtN (B : ℕ) : ℕ := if B ≤ 120 then 1 else 2

/-- The two ceilings at the low point with squared lengths `A`, `B`. -/
def fOne (A B HC rC : ℕ) : ℕ :=
  wtN B * cdiv (lowS * nOne A B (metric A) (metric B) HC)
    (denL A B (metric A) (metric B) (root A + root B + rC))

/-- The second ceiling. -/
def fTwo (A B C HC rC : ℕ) : ℕ :=
  wtN B * cdiv (lowS * nTwo A B C (metric A) (metric B) HC)
    (denL A B (metric A) (metric B) (root A + root B + rC))

/-- The slot base. -/
def Yb : ℕ := 2 ^ 128

lemma ltPack_eq (f1 f2 wr ws wt : ℕ) :
    ltPack f1 f2 wr ws wt =
      f1 * ws + (f1 * wr) * Yb ^ 1 + (f1 * wt) * Yb ^ 2 + (f2 * ws) * Yb ^ 3
        + (f2 * wr) * Yb ^ 4 + (f2 * wt) * Yb ^ 5
        + (f1 * ws + f1 * wr + f1 * wt + f2 * ws + f2 * wr + f2 * wt) * Yb ^ 6 := by
  unfold ltPack
  simp only [Nat.add_eq, Nat.mul_eq, shl_eq]
  have e2 : (2 : ℕ) ^ 256 = Yb ^ 2 := by rw [Yb, ← pow_mul]
  have e3 : (2 : ℕ) ^ 384 = Yb ^ 3 := by rw [Yb, ← pow_mul]
  have e6 : (2 : ℕ) ^ 768 = Yb ^ 6 := by rw [Yb, ← pow_mul]
  have e1 : (2 : ℕ) ^ 128 = Yb := rfl
  rw [e2, e3, e6, e1]
  generalize Yb = Y
  ring

lemma ble_rec_eq {α : Type} (B : ℕ) (x y : α) :
    (Bool.rec (motive := fun _ => α) x y (Nat.ble B 120) : α) = if B ≤ 120 then y else x := by
  by_cases h : B ≤ 120
  · rw [Nat.ble_eq_true_of_le h]; simp [h]
  · have e : Nat.ble B 120 = false := by
      rw [← Bool.not_eq_true]; intro h'; exact h (Nat.le_of_ble_eq_true h')
    rw [e]; simp [h]

lemma ble_zero_rec {α : Type} (B : ℕ) (x y : α) :
    (Bool.rec (motive := fun _ => α) x y (Nat.ble B 0) : α) = if B = 0 then y else x := by
  by_cases h : B = 0
  · subst h
    rw [show Nat.ble 0 0 = true from rfl]
    simp
  · have e : Nat.ble B 0 = false := by
      rw [← Bool.not_eq_true]; intro h'; exact h (by have := Nat.le_of_ble_eq_true h'; omega)
    rw [e]; simp [h]

/-- The unfolded low term. -/
lemma lowTerm_eq (a b c C HC rC Q ac bc ix iy iz A : ℕ) :
    lowTerm a b c C HC rC Q ac bc ix iy iz A =
      if sqd (a + 10) ix + (sqd (b + 10) iy + sqd (c + 10) iz) = 0 then 0 else
      ltPack (fOne A (sqd (a + 10) ix + (sqd (b + 10) iy + sqd (c + 10) iz)) HC rC)
        (fTwo A (sqd (a + 10) ix + (sqd (b + 10) iy + sqd (c + 10) iz)) C HC rC)
        (sqd (a * iy + 10 * b) (b * ix + 10 * a))
        (sqd (Q * iz + 10 * (ac + bc)) (ac * ix + bc * iy + 10 * Q))
        (sqd (a * iy + 10 * b + (Q * iz + 10 * (ac + bc)))
          (b * ix + 10 * a + (ac * ix + bc * iy + 10 * Q))) := by
  unfold lowTerm
  simp only [lit_eq, Nat.add_eq, ble_zero_rec]
  split_ifs with h
  · rfl
  · set B := sqd (a + 10) ix + (sqd (b + 10) iy + sqd (c + 10) iz)
    unfold ltM ltF ltL ltW
    simp only [lit_eq, Nat.add_eq, Nat.mul_eq, ble_rec_eq]
    rfl

/-- The integer inner product. -/
def iprod (p u : Mode) : ℤ := p 0 * u 0 + p 1 * u 1 + p 2 * u 2

/-- `(p·u)²` as a natural number. -/
def wS (u p : Mode) : ℕ := (iprod p u).natAbs ^ 2

lemma wS_int (u p : Mode) : (wS u p : ℤ) = iprod p u ^ 2 := by
  simp [wS, sq_abs]

/-- The vector `r = (-b,a,0)`. -/
def rV (a b : ℕ) : Mode := ![-(b : ℤ), a, 0]

/-- The vector `s = k × r = (-ac,-bc,a²+b²)`. -/
def sV (ac bc Q : ℕ) : Mode := ![-(ac : ℤ), -(bc : ℤ), Q]

/-- The packed contribution of a low point. -/
def lowP (a b c C HC rC Q ac bc : ℕ) (p : Mode) : ℕ :=
  if nsq p ≤ 120 ∧ nsq p ≠ 0 ∧ nsq (kN a b c - p) ≠ 0 then
    ltPack (fOne (nsq p) (nsq (kN a b c - p)) HC rC) (fTwo (nsq p) (nsq (kN a b c - p)) C HC rC)
      (wS (rV a b) p) (wS (sV ac bc Q) p) (wS (rV a b + sV ac bc Q) p)
  else 0

lemma pt10_sq (q : ℕ × ℕ × ℕ) : nsq (pt 10 q) = sq 10 q.2.2 + sq 10 q.2.1 + sq 10 q.1 := by
  rw [nsq_pt]; ring

lemma nsq_sub_pt (a b c : ℕ) (q : ℕ × ℕ × ℕ) :
    nsq (kN a b c - pt 10 q) =
      sqd (a + 10) q.2.2 + (sqd (b + 10) q.2.1 + sqd (c + 10) q.1) := by
  zify
  rw [sqd_cast, sqd_cast, sqd_cast]
  simp [nsq, kN, pt, Fin.sum_univ_three, sq_abs]
  ring

/-- The three squares at an index. -/
lemma wS_r (a b : ℕ) (q : ℕ × ℕ × ℕ) :
    wS (rV a b) (pt 10 q) = sqd (a * q.2.1 + 10 * b) (b * q.2.2 + 10 * a) := by
  zify
  rw [wS_int, sqd_cast]
  simp [iprod, rV, pt]
  ring

lemma wS_s (ac bc Q : ℕ) (q : ℕ × ℕ × ℕ) :
    wS (sV ac bc Q) (pt 10 q) = sqd (Q * q.1 + 10 * (ac + bc)) (ac * q.2.2 + bc * q.2.1 + 10 * Q) := by
  zify
  rw [wS_int, sqd_cast]
  simp [iprod, sV, pt]
  ring

lemma wS_t (a b ac bc Q : ℕ) (q : ℕ × ℕ × ℕ) :
    wS (rV a b + sV ac bc Q) (pt 10 q) =
      sqd (a * q.2.1 + 10 * b + (Q * q.1 + 10 * (ac + bc)))
        (b * q.2.2 + 10 * a + (ac * q.2.2 + bc * q.2.1 + 10 * Q)) := by
  zify
  rw [wS_int, sqd_cast]
  simp [iprod, rV, sV, pt]
  ring

/-- One index of the `z` loop. -/
lemma lowZ_eq (a b c C HC rC Q ac bc : ℕ) (q : ℕ × ℕ × ℕ) :
    lowZ a b c C HC rC Q ac bc q.2.2 q.2.1 (sq 10 q.2.2 + sq 10 q.2.1) q.1 =
      lowP a b c C HC rC Q ac bc (pt 10 q) := by
  unfold lowZ lowP
  simp only [lit_eq, Nat.add_eq, ble_rec_eq, ble_zero_rec, sqd_ten]
  rw [lowTerm_eq, pt10_sq, nsq_sub_pt, wS_r, wS_s, wS_t]
  generalize sq 10 q.2.2 + sq 10 q.2.1 + sq 10 q.1 = A
  generalize sqd (a + 10) q.2.2 + (sqd (b + 10) q.2.1 + sqd (c + 10) q.1) = B
  generalize ltPack _ _ _ _ _ = X
  split_ifs <;> omega

/-- The triple loop as a sum over the box of radius `10`. -/
theorem lowSum_spec (a b c C HC rC Q ac bc : ℕ) :
    lowSum a b c C HC rC Q ac bc = ∑ p ∈ boxM 10, lowP a b c C HC rC Q ac bc p := by
  have e21 : (21 : ℕ) % 2 ^ 5 = 21 := by norm_num
  rw [← sum_box 10 (lowP a b c C HC rC Q ac bc)]
  have hinner : ∀ ix iy, (Bool.rec (motive := fun _ => ℕ) 0
      (pkB 0 (lowZ a b c C HC rC Q ac bc ix iy (Nat.add (sq 10 ix) (sq 10 iy))) 21 5 0)
      (Nat.ble (Nat.add (sq 10 ix) (sq 10 iy)) 120) : ℕ) =
      ∑ iz ∈ range 21, lowZ a b c C HC rC Q ac bc ix iy (sq 10 ix + sq 10 iy) iz := by
    intro ix iy
    rw [ble_rec_eq, pkB_spec, e21]
    simp only [Nat.add_eq, zero_add, pow_zero, one_pow, mul_one]
    split_ifs with h
    · rfl
    · refine (sum_eq_zero fun iz _ => ?_).symm
      unfold lowZ
      simp only [lit_eq, Nat.add_eq, ble_rec_eq]
      simp only [show ¬ (sq 10 ix + sq 10 iy + sqd iz 10 ≤ 120) by omega, ↓reduceIte]
  unfold lowSum
  rw [pkB_spec, e21]
  simp only [zero_add, pow_zero, one_pow, mul_one, lit_eq, sqd_ten]
  have h2 : ∀ ix, pkB 0 (fun iy => Bool.rec (motive := fun _ => ℕ) 0
      (pkB 0 (lowZ a b c C HC rC Q ac bc ix iy (Nat.add (sq 10 ix) (sq 10 iy))) 21 5 0)
      (Nat.ble (Nat.add (sq 10 ix) (sq 10 iy)) 120)) 21 5 0 =
      ∑ iy ∈ range 21, ∑ iz ∈ range 21, lowZ a b c C HC rC Q ac bc ix iy (sq 10 ix + sq 10 iy) iz := by
    intro ix
    rw [pkB_spec, e21]
    simp only [zero_add, pow_zero, one_pow, mul_one]
    exact sum_congr rfl fun iy _ => hinner ix iy
  have h3 : ∑ ix ∈ range 21, pkB 0 (fun iy => Bool.rec (motive := fun _ => ℕ) 0
      (pkB 0 (lowZ a b c C HC rC Q ac bc ix iy (Nat.add (sq 10 ix) (sq 10 iy))) 21 5 0)
      (Nat.ble (Nat.add (sq 10 ix) (sq 10 iy)) 120)) 21 5 0 =
      ∑ ix ∈ range 21, ∑ iy ∈ range 21, ∑ iz ∈ range 21,
        lowZ a b c C HC rC Q ac bc ix iy (sq 10 ix + sq 10 iy) iz :=
    sum_congr rfl fun ix _ => h2 ix
  refine h3.trans ?_
  rw [Bx, sum_product]
  simp only [sum_product]
  rw [sum_comm]
  rw [sum_congr rfl fun iy _ => sum_comm]
  rw [sum_comm]
  refine sum_congr rfl fun iz _ => sum_congr rfl fun iy _ => sum_congr rfl fun ix _ => ?_
  exact lowZ_eq a b c C HC rC Q ac bc (iz, iy, ix)

/-- Seven slots, the last one the sum of the others. -/
lemma digits_seven {Y S E0 E1 E2 E3 E4 E5 : ℕ} (hY : 0 < Y)
    (hS : S = E0 + E1 * Y ^ 1 + E2 * Y ^ 2 + E3 * Y ^ 3 + E4 * Y ^ 4 + E5 * Y ^ 5
      + (E0 + E1 + E2 + E3 + E4 + E5) * Y ^ 6) (hlim : S + 1 ≤ Y ^ 7) :
    Dig Y S 0 = E0 ∧ Dig Y S 1 = E1 ∧ Dig Y S 2 = E2 ∧ Dig Y S 3 = E3 ∧ Dig Y S 4 = E4 ∧
      Dig Y S 5 = E5 := by
  set T := E0 + E1 + E2 + E3 + E4 + E5 with hT
  have h1 : T * Y ^ 6 ≤ S := by rw [hS]; exact Nat.le_add_left _ _
  have h2 : T < Y := by
    by_contra h
    have h3 : Y * Y ^ 6 ≤ T * Y ^ 6 := Nat.mul_le_mul_right _ (by omega)
    have h4 : Y ^ 7 = Y * Y ^ 6 := by ring
    omega
  have hd : ∀ i < 7, (![E0, E1, E2, E3, E4, E5, T] : Fin 7 → ℕ) ⟨i % 7, Nat.mod_lt _ (by norm_num)⟩ < Y := by
    intro i hi
    interval_cases i <;> simp <;> omega
  have hdig := fun j hj => dig_sum_range hY 7
    (fun i => (![E0, E1, E2, E3, E4, E5, T] : Fin 7 → ℕ) ⟨i % 7, Nat.mod_lt _ (by norm_num)⟩) hd j hj
  have hsum : ∑ i ∈ range 7, (![E0, E1, E2, E3, E4, E5, T] : Fin 7 → ℕ) ⟨i % 7, Nat.mod_lt _ (by norm_num)⟩ * Y ^ i = S := by
    rw [hS]
    simp [sum_range_succ]
  simp only [hsum] at hdig
  exact ⟨by simpa using hdig 0 (by norm_num), by simpa using hdig 1 (by norm_num),
    by simpa using hdig 2 (by norm_num), by simpa using hdig 3 (by norm_num),
    by simpa using hdig 4 (by norm_num), by simpa using hdig 5 (by norm_num)⟩

/-- The condition of a live low point. -/
def liveL (k p : Mode) : Prop := nsq p ≤ 120 ∧ nsq p ≠ 0 ∧ nsq (k - p) ≠ 0

instance (k p : Mode) : Decidable (liveL k p) := by unfold liveL; infer_instance

/-- The first ceiling at a lattice point. -/
def fa1 (k : Mode) (HC rC : ℕ) (p : Mode) : ℕ :=
  if liveL k p then fOne (nsq p) (nsq (k - p)) HC rC else 0

/-- The second ceiling at a lattice point. -/
def fa2 (k : Mode) (C HC rC : ℕ) (p : Mode) : ℕ :=
  if liveL k p then fTwo (nsq p) (nsq (k - p)) C HC rC else 0

lemma ite_f {α : Type*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-- A low point, slot by slot. -/
lemma lowP_eq (a b c C HC rC Q ac bc : ℕ) (p : Mode) :
    lowP a b c C HC rC Q ac bc p =
      ltPack (fa1 (kN a b c) HC rC p) (fa2 (kN a b c) C HC rC p)
        (wS (rV a b) p) (wS (sV ac bc Q) p) (wS (rV a b + sV ac bc Q) p) := by
  unfold lowP fa1 fa2
  by_cases h : liveL (kN a b c) p
  · have h' : nsq p ≤ 120 ∧ nsq p ≠ 0 ∧ nsq (kN a b c - p) ≠ 0 := h
    rw [ite_t h', ite_t h, ite_t h]
  · have h' : ¬ (nsq p ≤ 120 ∧ nsq p ≠ 0 ∧ nsq (kN a b c - p) ≠ 0) := h
    rw [ite_f h', ite_f h, ite_f h, ltPack_eq]
    simp

/-- The six slots of the low sum. -/
theorem lowSum_slots (a b c C HC rC Q ac bc : ℕ)
    (hlim : Nat.add (lowSum a b c C HC rC Q ac bc) 1 ≤ Yb ^ 7) :
    let f1 := fa1 (kN a b c) HC rC
    let f2 := fa2 (kN a b c) C HC rC
    let wr := wS (rV a b)
    let ws := wS (sV ac bc Q)
    let wt := wS (rV a b + sV ac bc Q)
    let S := lowSum a b c C HC rC Q ac bc
    rd 128 0 S = ∑ p ∈ boxM 10, f1 p * ws p ∧ rd 128 1 S = ∑ p ∈ boxM 10, f1 p * wr p ∧
    rd 128 2 S = ∑ p ∈ boxM 10, f1 p * wt p ∧ rd 128 3 S = ∑ p ∈ boxM 10, f2 p * ws p ∧
    rd 128 4 S = ∑ p ∈ boxM 10, f2 p * wr p ∧ rd 128 5 S = ∑ p ∈ boxM 10, f2 p * wt p := by
  intro f1 f2 wr ws wt S
  have hS : S = ∑ p ∈ boxM 10, f1 p * ws p + (∑ p ∈ boxM 10, f1 p * wr p) * Yb ^ 1
      + (∑ p ∈ boxM 10, f1 p * wt p) * Yb ^ 2 + (∑ p ∈ boxM 10, f2 p * ws p) * Yb ^ 3
      + (∑ p ∈ boxM 10, f2 p * wr p) * Yb ^ 4 + (∑ p ∈ boxM 10, f2 p * wt p) * Yb ^ 5
      + (∑ p ∈ boxM 10, f1 p * ws p + ∑ p ∈ boxM 10, f1 p * wr p + ∑ p ∈ boxM 10, f1 p * wt p
        + ∑ p ∈ boxM 10, f2 p * ws p + ∑ p ∈ boxM 10, f2 p * wr p + ∑ p ∈ boxM 10, f2 p * wt p)
        * Yb ^ 6 := by
    show lowSum a b c C HC rC Q ac bc = _
    rw [lowSum_spec]
    simp only [lowP_eq, ltPack_eq, sum_mul, ← sum_add_distrib]
    rfl
  have hY : 0 < Yb := by unfold Yb; positivity
  have hlim' : S + 1 ≤ Yb ^ 7 := hlim
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := digits_seven hY hS hlim'
  have e : ∀ i, rd 128 i S = Dig Yb S i := fun i => rd_eq 128 i S
  rw [e, e, e, e, e, e]
  exact ⟨h0, h1, h2, h3, h4, h5⟩

/-- The ceiling of a scaled quotient. -/
lemma ceil_le_real (w S n d : ℕ) (K : ℝ) (hK : 0 ≤ K) (hS : 0 < S) (hd : 0 < d) :
    (w : ℝ) * (K * n / d) ≤ K / S * ((w * cdiv (S * n) d : ℕ) : ℝ) := by
  have h := div_le_cdiv (S * n) d hd
  have hS0 : (0 : ℝ) < S := by exact_mod_cast hS
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  push_cast at h ⊢
  have h2 : (n : ℝ) / d ≤ cdiv (S * n) d / S := by
    rw [le_div_iff₀ hS0]
    calc (n : ℝ) / d * S = (S : ℝ) * n / d := by ring
      _ ≤ _ := h
  calc (w : ℝ) * (K * n / d) = w * K * ((n : ℝ) / d) := by ring
    _ ≤ w * K * ((cdiv (S * n) d : ℝ) / S) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

lemma sqd_real (a b : ℕ) : (sqd a b : ℝ) = ((a : ℝ) - b) ^ 2 := by
  have := sqd_cast a b
  have h2 : ((sqd a b : ℤ) : ℝ) = (((a : ℤ) - b) ^ 2 : ℤ) := by rw [this]
  push_cast at h2
  exact h2

/-- `w1` in integers. -/
lemma w1_exact {k p : Mode} (hA : nsq p ≠ 0) (hB : nsq (k - p) ≠ 0) (hC : nsq k ≠ 0) :
    w1 k p = 9 * (root (nsq k) : ℝ) * root (nsq k) *
        (nOne (nsq p) (nsq (k - p)) (metric (nsq p)) (metric (nsq (k - p))) (metric (nsq k)) : ℝ) /
      (denL (nsq p) (nsq (k - p)) (metric (nsq p)) (metric (nsq (k - p)))
        (root (nsq p) + root (nsq (k - p)) + root (nsq k)) : ℝ) := by
  have h1 : 1 ≤ nsq p := by omega
  have h2 : 1 ≤ nsq (k - p) := by omega
  have h3 : 1 ≤ nsq k := by omega
  have hA0 : (nsq p : ℝ) ≠ 0 := by exact_mod_cast hA
  have hB0 : (nsq (k - p) : ℝ) ≠ 0 := by exact_mod_cast hB
  have hHA : (metric (nsq p) : ℝ) ≠ 0 := by exact_mod_cast (metric_pos h1).ne'
  have hHB : (metric (nsq (k - p)) : ℝ) ≠ 0 := by exact_mod_cast (metric_pos h2).ne'
  have hr : ((root (nsq p) : ℝ) + root (nsq (k - p)) + root (nsq k)) ≠ 0 := by
    have := root_pos (nsq p)
    have : (0 : ℝ) < root (nsq p) := by exact_mod_cast this
    positivity
  unfold w1 Wk
  simp only [hm, ← nsq_cast, metric_spec h1, metric_spec h2, metric_spec h3, root_spec, nOne, denL]
  push_cast
  simp only [sqd_real]
  field_simp
  ring

/-- `Lst` in integers. -/
lemma Lst_exact {k p : Mode} (h1 : 1 ≤ nsq p) (h2 : 1 ≤ nsq (k - p)) (h3 : 1 ≤ nsq k) :
    Lst k p ^ 2 = (sqd (nsq p * metric (nsq k) + (nsq (k - p) * metric (nsq p)
        + nsq k * metric (nsq (k - p))))
      (nsq p * metric (nsq (k - p)) + (nsq (k - p) * metric (nsq k)
        + nsq k * metric (nsq p))) : ℝ) / 1000000 := by
  unfold Lst
  simp only [hm, ← nsq_cast, metric_spec h1, metric_spec h2, metric_spec h3, sqd_real]
  push_cast
  ring

/-- `w2` in integers. -/
lemma w2_exact {k p : Mode} (hA : nsq p ≠ 0) (hB : nsq (k - p) ≠ 0) (hC : nsq k ≠ 0) :
    w2 k p = 9 * (root (nsq k) : ℝ) * root (nsq k) *
        (nTwo (nsq p) (nsq (k - p)) (nsq k) (metric (nsq p)) (metric (nsq (k - p)))
          (metric (nsq k)) : ℝ) /
      (denL (nsq p) (nsq (k - p)) (metric (nsq p)) (metric (nsq (k - p)))
        (root (nsq p) + root (nsq (k - p)) + root (nsq k)) : ℝ) := by
  have h1 : 1 ≤ nsq p := by omega
  have h2 : 1 ≤ nsq (k - p) := by omega
  have h3 : 1 ≤ nsq k := by omega
  have hA0 : (nsq p : ℝ) ≠ 0 := by exact_mod_cast hA
  have hB0 : (nsq (k - p) : ℝ) ≠ 0 := by exact_mod_cast hB
  have hHA : (metric (nsq p) : ℝ) ≠ 0 := by exact_mod_cast (metric_pos h1).ne'
  have hHB : (metric (nsq (k - p)) : ℝ) ≠ 0 := by exact_mod_cast (metric_pos h2).ne'
  have hr : ((root (nsq p) : ℝ) + root (nsq (k - p)) + root (nsq k)) ≠ 0 := by
    have := root_pos (nsq p)
    have : (0 : ℝ) < root (nsq p) := by exact_mod_cast this
    positivity
  have hL := Lst_exact h1 h2 h3
  unfold w2 Wk
  rw [hL]
  simp only [hm, ← nsq_cast, metric_spec h1, metric_spec h2, root_spec, nTwo, denL]
  push_cast
  simp only [sqd_real]
  field_simp
  ring

/-- The true weights are below the ceilings, on a low point. -/
theorem w_le_ceil {k p : Mode} (hk : k ≠ 0) (hp : nsq p ≤ 120) :
    wtL k p * w1 k p ≤ 9 * (root (nsq k) : ℝ) * root (nsq k) / lowS *
        fa1 k (metric (nsq k)) (root (nsq k)) p ∧
      wtL k p * w2 k p ≤ 9 * (root (nsq k) : ℝ) * root (nsq k) / lowS *
        fa2 k (nsq k) (metric (nsq k)) (root (nsq k)) p := by
  have hK : (0 : ℝ) ≤ 9 * (root (nsq k) : ℝ) * root (nsq k) / lowS := by positivity
  by_cases hl : liveL k p
  · obtain ⟨h1, h2, h3⟩ := id hl
    have hC : nsq k ≠ 0 := fun h => hk ((nsq_eq_zero_iff k).1 h)
    have hS : 0 < lowS := by unfold lowS; norm_num
    have hd : 0 < denL (nsq p) (nsq (k - p)) (metric (nsq p)) (metric (nsq (k - p)))
        (root (nsq p) + root (nsq (k - p)) + root (nsq k)) := by
      have a1 := metric_pos (j := nsq p) (by omega)
      have a2 := metric_pos (j := nsq (k - p)) (by omega)
      have a3 := root_pos (nsq p)
      have a4 : 0 < nsq p := by omega
      have a5 : 0 < nsq (k - p) := by omega
      unfold denL
      positivity
    have hwt : wtL k p = (wtN (nsq (k - p)) : ℝ) := by
      unfold wtL wtN
      split_ifs <;> simp
    constructor
    · rw [w1_exact h2 h3 hC, hwt]
      unfold fa1 fOne
      rw [ite_t hl]
      exact ceil_le_real _ _ _ _ _ (by positivity) hS hd
    · rw [w2_exact h2 h3 hC, hwt]
      unfold fa2 fTwo
      rw [ite_t hl]
      exact ceil_le_real _ _ _ _ _ (by positivity) hS hd
  · have h0 : nsq p = 0 ∨ nsq (k - p) = 0 := by
      unfold liveL at hl
      omega
    have hw : w1 k p = 0 ∧ w2 k p = 0 := by
      rcases h0 with h0 | h0
      · have : absSq p = 0 := by rw [← nsq_cast, h0]; simp
        simp [w1, w2, this]
      · have : absSq (k - p) = 0 := by rw [← nsq_cast, h0]; simp
        simp [w1, w2, this]
    rw [hw.1, hw.2, mul_zero]
    exact ⟨by positivity, by positivity⟩

end Row
end OVNS
