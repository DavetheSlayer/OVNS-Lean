import OddViscousNS.Closed.Row.Kron
import OddViscousNS.Closed.Row.Core

/-!
# Specification of the kernel-side array builders of `Row/Core.lean`

Each builder has a specification as a finite sum of `digit * X ^ position`.
-/

open Finset

namespace OVNS
namespace Row

lemma lit_eq (e : Nat) (k : Nat → Nat) : lit e k = k e := by
  cases e <;> rfl

lemma shl_eq (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

lemma pk_zero (w : Nat) (g : Nat → Nat) (lo : Nat) : pk w g 0 lo = g lo := rfl

lemma pk_succ (w : Nat) (g : Nat → Nat) (n lo : Nat) :
    pk w g (n + 1) lo = pk w g n lo + (pk w g n (lo + 2 ^ n)) * (2 ^ w) ^ (2 ^ n) := by
  show Nat.add (pk w g n lo) (Nat.shiftLeft (pk w g n (Nat.add lo (Nat.shiftLeft 1 n)))
    (Nat.mul w (Nat.shiftLeft 1 n))) = _
  simp only [Nat.add_eq, Nat.mul_eq, shl_eq, one_mul, pow_mul]

/-- Specification of `pk`. -/
lemma pk_spec (w : Nat) (g : Nat → Nat) (n lo : Nat) :
    pk w g n lo = ∑ i ∈ range (2 ^ n), g (lo + i) * (2 ^ w) ^ i := by
  induction n generalizing lo with
  | zero => simp [pk_zero]
  | succ n ih =>
    rw [pk_succ, ih, ih, pow_succ, mul_two, sum_range_add, sum_mul]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [add_assoc, pow_add]
    ring

lemma pkB_zero (w : Nat) (g : Nat → Nat) (n lo : Nat) : pkB w g n 0 lo = 0 := rfl

lemma bit_split (n b : Nat) : n % 2 ^ (b + 1) =
    n % 2 ^ b + (if Nat.ble 1 (Nat.land 1 (Nat.shiftRight n b)) = true then 2 ^ b else 0) := by
  have h1 : Nat.land 1 (Nat.shiftRight n b) = (n / 2 ^ b) % 2 := by
    show 1 &&& (n >>> b) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
  rw [h1, Nat.mod_pow_succ]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ b) with h | h <;> simp [h]

lemma pkB_succ (w : Nat) (g : Nat → Nat) (n b lo : Nat) :
    pkB w g n (b + 1) lo =
      if Nat.ble 1 (Nat.land 1 (Nat.shiftRight n b)) = true then
        pk w g b lo + pkB w g n b (lo + 2 ^ b) * (2 ^ w) ^ (2 ^ b)
      else pkB w g n b lo := by
  show Bool.rec (motive := fun _ => Nat) (pkB w g n b lo)
      (Nat.add (pk w g b lo) (Nat.shiftLeft (pkB w g n b (Nat.add lo (Nat.shiftLeft 1 b)))
        (Nat.mul w (Nat.shiftLeft 1 b)))) (Nat.ble 1 (Nat.land 1 (Nat.shiftRight n b))) = _
  cases h : Nat.ble 1 (Nat.land 1 (Nat.shiftRight n b)) with
  | false => simp
  | true =>
    simp only [Nat.add_eq, Nat.mul_eq, shl_eq, one_mul, pow_mul, ite_true]

/-- Specification of `pkB`. -/
lemma pkB_spec (w : Nat) (g : Nat → Nat) (n b lo : Nat) :
    pkB w g n b lo = ∑ i ∈ range (n % 2 ^ b), g (lo + i) * (2 ^ w) ^ i := by
  induction b generalizing lo with
  | zero => simp [pkB_zero, Nat.mod_one]
  | succ b ih =>
    rw [pkB_succ, bit_split]
    split_ifs with h
    · rw [ih, pk_spec, add_comm (n % 2 ^ b), sum_range_add, sum_mul]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [add_assoc, pow_add]
      ring
    · rw [ih]; rfl

lemma sq_cast (R i : Nat) : (sq R i : ℤ) = ((i : ℤ) - R) ^ 2 := by
  show (((i - R) * (i - R) + (R - i) * (R - i) : ℕ) : ℤ) = _
  rcases le_total i R with h | h
  · have e1 : i - R = 0 := by omega
    rw [e1]; push_cast [Nat.cast_sub h]; ring
  · have e1 : R - i = 0 := by omega
    rw [e1]; push_cast [Nat.cast_sub h]; ring

section spec
variable {w R R2 n b : Nat} {F : Nat → Nat}

/-- Vanishing outside the ball. -/
def Ball (R2 : Nat) (F : Nat → Nat) : Prop := ∀ a, R2 < a → F a = 0

lemma ball_guard (s z : Nat) (hz : R2 < s → z = 0) :
    (Bool.rec (motive := fun _ => Nat) 0 z (Nat.ble s R2) : Nat) = z := by
  cases h : Nat.ble s R2 with
  | true => rfl
  | false =>
    have : R2 < s := by
      by_contra h'
      have := Nat.ble_eq_true_of_le (Nat.le_of_not_lt h')
      simp_all
    simp [hz this]

/-- Specification of the rows, as sums over `i < n`, where `n < 2^b`. -/
lemma row_gen (hF : Ball R2 F) (hb : n < 2 ^ b) (s : Nat) (G : Nat → Nat → Nat)
    (hG : ∀ i, G i 0 = 0) :
    (Bool.rec (motive := fun _ => Nat) 0 (pkB w (fun i => G i (F (Nat.add s (sq R i)))) n b 0)
        (Nat.ble s R2) : Nat) =
      ∑ i ∈ range n, G i (F (s + sq R i)) * (2 ^ w) ^ i := by
  rw [ball_guard, pkB_spec, Nat.mod_eq_of_lt hb]
  · simp only [zero_add]; rfl
  · intro hs
    rw [pkB_spec]
    refine sum_eq_zero fun i _ => ?_
    have : F (s + sq R (0 + i)) = 0 := hF _ (by omega)
    simp only [Nat.add_eq]
    rw [this, hG, zero_mul]

lemma row0_spec (hF : Ball R2 F) (hb : n < 2 ^ b) (s : Nat) :
    row0 w R R2 n b F s = ∑ i ∈ range n, F (s + sq R i) * (2 ^ w) ^ i :=
  row_gen (G := fun _ x => x) hF hb s (fun _ => rfl)

lemma row1_spec (hF : Ball R2 F) (hb : n < 2 ^ b) (s : Nat) :
    row1 w R R2 n b F s = ∑ i ∈ range n, (F (s + sq R i) * i) * (2 ^ w) ^ i :=
  row_gen (G := fun i x => Nat.mul x i) hF hb s (fun i => Nat.zero_mul i)

lemma row2_spec (hF : Ball R2 F) (hb : n < 2 ^ b) (s : Nat) :
    row2 w R R2 n b F s = ∑ i ∈ range n, (F (s + sq R i) * sq R i) * (2 ^ w) ^ i :=
  row_gen (G := fun i x => Nat.mul x (sq R i)) hF hb s (fun _ => Nat.zero_mul _)

/-- The pointwise identity behind `rowXY`. -/
lemma xy_identity (R i iy : Nat) :
    sq R i + 2 * (iy - R) * i + ((iy - R) * (iy - R) + ((R - iy) * (R - iy) + 2 * R * (R - iy))) =
      sq (2 * R) (i + iy) + (2 * (R - iy) * i + 2 * R * (iy - R)) := by
  zify
  rw [sq_cast, sq_cast]
  rcases le_total iy R with h | h
  · have e1 : iy - R = 0 := by omega
    rw [e1]; push_cast [Nat.cast_sub h]; ring
  · have e1 : R - iy = 0 := by omega
    rw [e1]; push_cast [Nat.cast_sub h]; ring

/-- Specification of `rowXY`: the weight is `sq (2R) (i+iy) = (x+y)²`. -/
lemma rowXY_spec (hF : Ball R2 F) (hb : n < 2 ^ b) (iy s : Nat) :
    rowXY w R R2 n b F iy s =
      ∑ i ∈ range n, (F (s + sq R i) * sq (2 * R) (i + iy)) * (2 ^ w) ^ i := by
  unfold rowXY
  simp only [lit_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  rw [row0_spec hF hb, row1_spec hF hb, row2_spec hF hb]
  set X := (2 ^ w : ℕ)
  set y0 := iy - R
  set y1 := R - iy
  set Q := y0 * y0 + (y1 * y1 + 2 * R * y1)
  have e1 : (∑ i ∈ range n, F (s + sq R i) * sq R i * X ^ i)
      + (2 * y0 * ∑ i ∈ range n, F (s + sq R i) * i * X ^ i
        + Q * ∑ i ∈ range n, F (s + sq R i) * X ^ i) =
      (∑ i ∈ range n, F (s + sq R i) * sq (2 * R) (i + iy) * X ^ i)
        + (2 * y1 * ∑ i ∈ range n, F (s + sq R i) * i * X ^ i
          + 2 * R * y0 * ∑ i ∈ range n, F (s + sq R i) * X ^ i) := by
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    have := xy_identity R i iy
    have h2 : (sq R i + 2 * y0 * i + Q) * (F (s + sq R i) * X ^ i) =
        (sq (2 * R) (i + iy) + (2 * y1 * i + 2 * R * y0)) * (F (s + sq R i) * X ^ i) := by
      rw [show sq R i + 2 * y0 * i + Q = _ from this]
    calc _ = (sq R i + 2 * y0 * i + Q) * (F (s + sq R i) * X ^ i) := by ring
      _ = _ := h2
      _ = _ := by ring
  rw [e1, Nat.add_sub_cancel]

/-- Specification of a slice and an array of rows: the sum over the index box `(iz, iy, ix)`. -/
lemma arr_spec {w P wP wPP : Nat} {nz z0 bz : Nat} (hwP : wP = w * P) (hwPP : wPP = w * P * P)
    (hb : n < 2 ^ b) (hbz : nz < 2 ^ bz)
    (rw : Nat → Nat → Nat) (H : Nat → Nat → Nat → Nat)
    (hrw : ∀ iy s, rw iy s = ∑ i ∈ range n, H iy s i * (2 ^ w) ^ i) :
    arr wPP R bz nz z0 (slice wP R n b rw) =
      ∑ q ∈ range nz ×ˢ range n ×ˢ range n,
        H q.2.1 (sq R q.2.1 + sq R (z0 + q.1)) q.2.2 *
          (2 ^ w) ^ (q.2.2 + P * q.2.1 + P * P * q.1) := by
  subst hwP hwPP
  have e1 : ∀ y, (2 ^ (w * P) : ℕ) ^ y = (2 ^ w) ^ (P * y) := fun y => by
    rw [← pow_mul, ← pow_mul, mul_assoc]
  have e2 : ∀ y, (2 ^ (w * P * P) : ℕ) ^ y = (2 ^ w) ^ (P * P * y) := fun y => by
    rw [← pow_mul, ← pow_mul]; ring_nf
  unfold arr
  rw [pkB_spec, Nat.mod_eq_of_lt hbz, sum_product]
  refine sum_congr rfl fun iz _ => ?_
  rw [sum_product, lit_eq]
  unfold slice
  rw [pkB_spec, Nat.mod_eq_of_lt hb, sum_mul]
  refine sum_congr rfl fun iy _ => ?_
  rw [lit_eq, hrw, zero_add]
  simp only [Nat.add_eq]
  rw [sum_mul, sum_mul]
  refine sum_congr rfl fun ix _ => ?_
  rw [e1, e2, pow_add, pow_add]
  ring

end spec

/-! ### Radial kernels -/

lemma shell_eq (R2 A x : Nat) : shell R2 A x = if 120 < A ∧ A ≤ R2 then x else 0 := by
  unfold shell
  by_cases h1 : A ≤ R2
  · by_cases h2 : A ≤ 120
    · have e1 := Nat.ble_eq_true_of_le h1
      have e2 := Nat.ble_eq_true_of_le h2
      rw [e1, e2]; simp [show ¬ (120 < A) by omega]
    · have e1 := Nat.ble_eq_true_of_le h1
      have e2 : Nat.ble A 120 = false := by
        rw [← Bool.not_eq_true]; intro h; exact h2 (Nat.le_of_ble_eq_true h)
      rw [e1, e2]; simp [show 120 < A by omega, h1]
  · have e1 : Nat.ble A R2 = false := by
      rw [← Bool.not_eq_true]; intro h; exact h1 (Nat.le_of_ble_eq_true h)
    rw [e1]; simp [h1]

lemma shell_ball (R2 x : Nat) (A : Nat) (h : R2 < A) : shell R2 A x = 0 := by
  rw [shell_eq]; simp [show ¬ A ≤ R2 by omega]

/-! ### Windows and the table check -/

lemma win_eq (w s n N : Nat) : win w s n N = N / (2 ^ w) ^ s % (2 ^ w) ^ n := by
  show (N >>> (w * s)) % (1 <<< (w * n)) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, one_mul, pow_mul, pow_mul]

lemma rd_eq (w i N : Nat) : rd w i N = Dig (2 ^ w) N i := by
  show (N >>> (w * i)) % (1 <<< w) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, one_mul, pow_mul]
  rfl

lemma litB_eq (e : Nat) (k : Nat → Bool) : litB e k = k e := by
  cases e <;> rfl

lemma allN_spec (g : Nat → Bool) (n : Nat) (h : allN g n = true) : ∀ i < n, g i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have h' : Bool.and (g n) (allN g n) = true := h
    rw [Bool.and_eq_true_iff] at h'
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h1 | h1
    · exact ih h'.2 i h1
    · rw [h1]; exact h'.1

/-- Soundness of `cubeChk`: the table holds the digits of the product. -/
theorem cubeChk_spec {w P wPP off Z T N : Nat} (hPP : wPP = w * P * P) (hZP : Z ≤ P)
    (hb : off + P * (Z + off) ≤ P * P)
    (h : cubeChk w P wPP off Z T N = true) {x y z : Nat} (hx : x < Z) (hy : y < Z) (hz : z < Z) :
    Dig (2 ^ w) T (x + Z * (y + Z * z)) =
      Dig (2 ^ w) N (off + x + P * (y + off) + P * P * (z + off)) := by
  have hX : ∀ m, (2 ^ wPP : ℕ) ^ m = (2 ^ w) ^ (P * P * m) := fun m => by
    rw [hPP, ← pow_mul, ← pow_mul]; ring_nf
  unfold cubeChk at h
  simp only [litB_eq] at h
  have h1 := allN_spec _ _ h z hz
  have h2 := allN_spec _ _ h1 y hy
  have h3 := Nat.eq_of_beq_eq_true h2
  rw [win_eq, win_eq, win_eq, win_eq] at h3
  simp only [hX] at h3
  set X : ℕ := 2 ^ w
  set Rg := N / X ^ (P * P * off) % X ^ (P * P * Z) with hRg
  set sl := Rg / X ^ (P * P * z) % X ^ (P * P * 1) with hsl
  have hR := congrArg (fun M => Dig X M x) h3
  rw [dig_window _ _ _ _ hx, dig_window _ _ _ _ hx] at hR
  simp only [Nat.add_eq, Nat.mul_eq] at hR
  have hxP : x < P := by omega
  have e1 : off + P * (y + off) + x < P * P := by
    have : P * (y + 1 + off) ≤ P * (Z + off) := Nat.mul_le_mul_left _ (by omega)
    have e : P * (y + 1 + off) = P * (y + off) + P := by ring
    omega
  have e2 : P * P * z + (off + P * (y + off) + x) < P * P * Z := by
    have : P * P * (z + 1) ≤ P * P * Z := Nat.mul_le_mul_left _ (by omega)
    have e : P * P * (z + 1) = P * P * z + P * P := by ring
    omega
  rw [hsl, dig_window _ _ _ _ (by simpa using e1), hRg, dig_window _ _ _ _ e2] at hR
  rw [show x + Z * (y + Z * z) = Z * (y + Z * z) + x by ring, ← hR]
  congr 1
  ring

end Row
end OVNS
