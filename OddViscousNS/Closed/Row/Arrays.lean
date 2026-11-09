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

/-- Specification of a slice and an array of rows: the sum over the index box `(iz, iy, ix)`. -/
lemma arr_spec {w P wP wPP : Nat} {nz z0 bz : Nat} (hwP : wP = w * P) (hwPP : wPP = w * P * P)
    (hb : n < 2 ^ b) (hbz : nz < 2 ^ bz)
    (rw : Nat → Nat → Nat) (H : Nat → Nat → Nat → Nat)
    (hrw : ∀ iy < n, ∀ s, rw iy s = ∑ i ∈ range n, H iy s i * (2 ^ w) ^ i) :
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
  refine sum_congr rfl fun iy hiy => ?_
  rw [lit_eq, zero_add]
  simp only [Nat.add_eq]
  rw [hrw iy (mem_range.1 hiy), sum_mul, sum_mul]
  refine sum_congr rfl fun ix _ => ?_
  rw [e1, e2, pow_add, pow_add]
  ring

/-- A slice of keyed rows, with the keys removed, is the slice of the plain rows. -/
lemma sliceT_eq {w wP R n b : Nat} (hb : n < 2 ^ b)
    (rw : Nat → Nat → Nat) (H : Nat → Nat → Nat → Nat)
    (hrw : ∀ iy < n, ∀ s, rw iy s = ∑ i ∈ range n, H iy s i * (2 ^ w) ^ i + s) (zz : Nat) :
    sliceT wP R n b rw zz =
      slice wP R n b (fun iy s => ∑ i ∈ range n, H iy s i * (2 ^ w) ^ i) zz := by
  unfold sliceT slice
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  rw [pkB_spec, pkB_spec, pkB_spec, pkB_spec, Nat.mod_eq_of_lt hb]
  have e : ∑ i ∈ range n, lit (sq R (0 + i) + zz) (rw (0 + i)) * (2 ^ wP) ^ i =
      ∑ i ∈ range n, lit (sq R (0 + i) + zz)
          ((fun iy s => ∑ j ∈ range n, H iy s j * (2 ^ w) ^ j) (0 + i)) * (2 ^ wP) ^ i +
        (∑ i ∈ range n, sq R (0 + i) * (2 ^ wP) ^ i + zz * ∑ i ∈ range n, 1 * (2 ^ wP) ^ i) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [lit_eq, lit_eq, zero_add, hrw i (mem_range.1 hi)]
    ring
  rw [e, Nat.add_sub_cancel]

/-- `arr_spec` for slices of keyed rows. -/
lemma arr_specT {w P wP wPP R n b nz z0 bz : Nat} (hwP : wP = w * P) (hwPP : wPP = w * P * P)
    (hb : n < 2 ^ b) (hbz : nz < 2 ^ bz)
    (rw : Nat → Nat → Nat) (H : Nat → Nat → Nat → Nat)
    (hrw : ∀ iy < n, ∀ s, rw iy s = ∑ i ∈ range n, H iy s i * (2 ^ w) ^ i + s) :
    arr wPP R bz nz z0 (sliceT wP R n b rw) =
      ∑ q ∈ range nz ×ˢ range n ×ˢ range n,
        H q.2.1 (sq R q.2.1 + sq R (z0 + q.1)) q.2.2 *
          (2 ^ w) ^ (q.2.2 + P * q.2.1 + P * P * q.1) := by
  have e : sliceT wP R n b rw = slice wP R n b (fun iy s => ∑ i ∈ range n, H iy s i * (2 ^ w) ^ i) :=
    funext (sliceT_eq hb rw H hrw)
  rw [e]
  exact arr_spec hwP hwPP hb hbz _ H (fun _ _ _ => rfl)

end spec

/-! ### Rows gathered from one product

Digit `t + n k` of `ftR · qW` collects the pairs `(j, t')` with `t' + n (j + (t'-R)²) = t + n k`; as
`t, t' < n` there is at most one, `t' = t` and `j = k - (t-R)²`.  So when every term is below
`X = 2^w` the digits are the terms, and row `k = R2 - s` holds `F (s + (t-R)²) wt t`. -/

lemma winA_eq (w s n N : Nat) : winA w s n N = N / (2 ^ w) ^ s % (2 ^ w) ^ n := by
  show (N >>> (w * s)) &&& (1 <<< (w * n) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, ← pow_mul,
    ← pow_mul]

section gather

variable {w n R R2 b bA : Nat} {F wt : Nat → Nat}

lemma ftR_spec (hbA : R2 + 1 < 2 ^ bA) :
    ftR w n R2 bA F = ∑ j ∈ range (R2 + 1), F (R2 - j) * (2 ^ w) ^ (n * j) := by
  unfold ftR
  rw [pkB_spec, Nat.add_eq, Nat.mod_eq_of_lt hbA]
  refine sum_congr rfl fun j _ => ?_
  rw [zero_add, Nat.mul_eq, ← pow_mul, ← pow_mul, mul_assoc]
  rfl

lemma qW_spec (hb : n < 2 ^ b) :
    qW w n R b wt = ∑ t ∈ range n, wt t * (2 ^ w) ^ (t + n * sq R t) := by
  unfold qW
  rw [pkB_spec, Nat.mod_eq_of_lt hb]
  refine sum_congr rfl fun t _ => ?_
  rw [zero_add, pow_zero, one_pow, mul_one, shl_eq, ← pow_mul]
  rfl

/-- The product, as a packed sum over pairs `(j, t)`. -/
lemma prod_spec (hb : n < 2 ^ b) (hbA : R2 + 1 < 2 ^ bA) :
    ftR w n R2 bA F * qW w n R b wt =
      ∑ q ∈ range (R2 + 1) ×ˢ range n,
        (F (R2 - q.1) * wt q.2) * (2 ^ w) ^ (n * q.1 + (q.2 + n * sq R q.2)) := by
  rw [ftR_spec hbA, qW_spec hb, pack_mul]

lemma prL_eq (w n R R2 b bA : Nat) (F wt : Nat → Nat) :
    prL w n R R2 b bA F wt = ftR w n R2 bA F * qW w n R b wt % (2 ^ w) ^ (n * (R2 + 1)) := by
  show (ftR w n R2 bA F * qW w n R b wt) &&& (1 <<< (w * (n * (R2 + 1))) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, ← pow_mul]

/-- A pair in the fiber of position `p`: `t = p % n` and `j + (t-R)² = p / n`. -/
lemma gather_fiber (hn : 0 < n) {p : ℕ} {q : ℕ × ℕ} (hq : q.2 < n)
    (h : n * q.1 + (q.2 + n * sq R q.2) = p) : q.2 = p % n ∧ q.1 + sq R q.2 = p / n := by
  have e : p = q.2 + n * (q.1 + sq R q.2) := by rw [← h]; ring
  subst e
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]
  · rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hq, zero_add]

/-- Every position of the product holds at most one term, so its digits are the terms. -/
lemma gather_slot (hn : 0 < n) (hX : ∀ A ≤ R2, ∀ t < n, F A * wt t < 2 ^ w) (p : ℕ) :
    ∑ q ∈ (range (R2 + 1) ×ˢ range n).filter (fun q => n * q.1 + (q.2 + n * sq R q.2) = p),
      F (R2 - q.1) * wt q.2 < 2 ^ w := by
  set S := (range (R2 + 1) ×ˢ range n).filter (fun q => n * q.1 + (q.2 + n * sq R q.2) = p)
  have hS : S ⊆ {(p / n - sq R (p % n), p % n)} := by
    intro q hq
    simp only [S, mem_filter, mem_product, mem_range] at hq
    obtain ⟨⟨_, h2⟩, h3⟩ := hq
    obtain ⟨e1, e2⟩ := gather_fiber hn h2 h3
    rw [mem_singleton, Prod.ext_iff]
    exact ⟨by simp only; rw [← e1]; omega, e1⟩
  rcases subset_singleton_iff.1 hS with h | h
  · rw [h, sum_empty]; positivity
  · rw [h, sum_singleton]
    have hm : (p / n - sq R (p % n), p % n) ∈ S := by rw [h]; exact mem_singleton_self _
    simp only [S, mem_filter, mem_product, mem_range] at hm
    exact hX _ (Nat.sub_le _ _) _ hm.1.2

/-- **The digits of the product**: position `n (R2 - s) + i` holds `F (s + (i-R)²) wt i`. -/
lemma dig_gather (hn : 0 < n) (hb : n < 2 ^ b) (hbA : R2 + 1 < 2 ^ bA) (hF : Ball R2 F)
    (hX : ∀ A ≤ R2, ∀ t < n, F A * wt t < 2 ^ w) {s i : ℕ} (hs : s ≤ R2) (hi : i < n) :
    Dig (2 ^ w) (ftR w n R2 bA F * qW w n R b wt) (n * (R2 - s) + i) = F (s + sq R i) * wt i := by
  classical
  set I := range (R2 + 1) ×ˢ range n
  set idx : ℕ × ℕ → ℕ := fun q => n * q.1 + (q.2 + n * sq R q.2)
  set p := n * (R2 - s) + i
  have hp1 : p % n = i := by
    simp only [p]; rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have hp2 : p / n = R2 - s := by
    simp only [p]; rw [add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hi, zero_add]
  rw [prod_spec hb hbA]
  rw [dig_fiber (by positivity) I (fun q => F (R2 - q.1) * wt q.2) idx (M := p + 1 + ∑ q ∈ I, idx q)
    (fun q hq => by have := single_le_sum (f := idx) (fun _ _ => Nat.zero_le _) hq; omega)
    (fun t _ => gather_slot hn hX t) p (by omega)]
  by_cases hk : sq R i ≤ R2 - s
  · have e : I.filter (fun q => idx q = p) = {(R2 - s - sq R i, i)} := by
      ext q
      simp only [I, idx, mem_filter, mem_product, mem_range, mem_singleton]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        obtain ⟨e1, e2⟩ := gather_fiber hn h2 h3
        rw [hp1] at e1; rw [hp2, e1] at e2
        exact Prod.ext (by simp only; omega) e1
      · rintro rfl
        refine ⟨⟨by omega, hi⟩, ?_⟩
        simp only [p]
        obtain ⟨m, hm⟩ : ∃ m, R2 - s = sq R i + m := ⟨R2 - s - sq R i, by omega⟩
        rw [hm, Nat.add_sub_cancel_left]; ring
    rw [e, sum_singleton]
    congr 2
    omega
  · have e : I.filter (fun q => idx q = p) = ∅ := by
      rw [filter_eq_empty_iff]
      intro q hq h3
      simp only [I, mem_product, mem_range] at hq
      obtain ⟨e1, e2⟩ := gather_fiber hn hq.2 h3
      rw [hp1] at e1; rw [hp2, e1] at e2
      omega
    rw [e, sum_empty, hF _ (by omega), zero_mul]

/-- **Specification of a gathered row.** -/
lemma rowW_spec (hn : 0 < n) (hb : n < 2 ^ b) (hbA : R2 + 1 < 2 ^ bA) (hF : Ball R2 F)
    (hX : ∀ A ≤ R2, ∀ t < n, F A * wt t < 2 ^ w) (s : ℕ) :
    rowW w n R2 (prL w n R R2 b bA F wt) s =
      ∑ i ∈ range n, (F (s + sq R i) * wt i) * (2 ^ w) ^ i := by
  have hd : ∀ i < n, F (s + sq R i) * wt i < 2 ^ w := fun i hi => by
    by_cases h : s + sq R i ≤ R2
    · exact hX _ h _ hi
    · rw [hF _ (by omega), zero_mul]; positivity
  unfold rowW
  by_cases hs : s ≤ R2
  · rw [Nat.ble_eq_true_of_le hs]
    simp only [lit_eq]
    show winA w (n * ((R2 - s) % 64)) n (blk w n _ ((R2 - s) / 1024) ((R2 - s) / 64 % 16)) = _
    unfold blk sblk
    rw [winA_eq, winA_eq, winA_eq]
    simp only [Nat.mul_eq]
    refine eq_of_dig (by positivity) (Nat.mod_lt _ (by positivity)) (sum_lt_pow n _ hd)
      fun i hi => ?_
    set k := R2 - s with hk
    have h64 : k % 64 < 64 := Nat.mod_lt _ (by norm_num)
    have h16 : k / 64 % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have hw1 : n * (k % 64) + i < 64 * n := by nlinarith
    have hw2 : 64 * n * (k / 64 % 16) + (n * (k % 64) + i) < 1024 * n := by nlinarith
    have e : 1024 * n * (k / 1024) + (64 * n * (k / 64 % 16) + (n * (k % 64) + i)) = n * k + i := by
      have h1 := Nat.div_add_mod k 64
      have h2 := Nat.div_add_mod (k / 64) 16
      have h3 : k / 64 / 16 = k / 1024 := by rw [Nat.div_div_eq_div_mul]
      calc _ = n * (64 * (16 * (k / 1024) + k / 64 % 16) + k % 64) + i := by ring
        _ = n * (64 * (16 * (k / 64 / 16) + k / 64 % 16) + k % 64) + i := by rw [h3]
        _ = n * (64 * (k / 64) + k % 64) + i := by rw [h2]
        _ = _ := by rw [h1]
    have hlt : n * k + i < n * (R2 + 1) := by
      have := Nat.mul_le_mul_left n (Nat.sub_le R2 s)
      nlinarith
    rw [dig_window _ _ _ _ hi, dig_window _ _ _ _ hw1, dig_window _ _ _ _ hw2, e, prL_eq, dig_mod _ _ _ hlt, dig_sum_range (by positivity) n _ hd i hi,
      dig_gather hn hb hbA hF hX hs hi]
  · have : Nat.ble s R2 = false := by
      cases h : Nat.ble s R2 with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true h) hs
    rw [this]
    symm
    refine sum_eq_zero fun i _ => ?_
    rw [hF _ (by omega), zero_mul, zero_mul]

end gather

/-! ### The `(x+y)²` row, by the sign of `y` -/

/-- `y ≥ 0`: `x² + 2 y i = (x+y)² + y (2R - y)`, where `x = i - R`. -/
lemma xy_pos (R i iy : Nat) (h : R ≤ iy) (h' : iy ≤ 3 * R) :
    sq R i + 2 * (iy - R) * i = sq (2 * R) (i + iy) + (iy - R) * (2 * R - (iy - R)) := by
  zify [h, show iy - R ≤ 2 * R by omega]
  rw [sq_cast, sq_cast]
  push_cast
  ring

/-- `y < 0`: `x² + |y| (2R + |y|) = (x+y)² + 2 |y| i`. -/
lemma xy_neg (R i iy : Nat) (h : iy ≤ R) :
    sq R i + (R - iy) * (2 * R + (R - iy)) = sq (2 * R) (i + iy) + 2 * (R - iy) * i := by
  zify [h]
  rw [sq_cast, sq_cast]
  push_cast
  ring

/-- Specification of `rowXYg`: the weight is `sq (2R) (i+iy) = (x+y)²`, plus the key `s`. -/
lemma rowXYg_spec {w n R R2 P0 P1 P2 iy s : Nat} {f : Nat → Nat} (hiy : iy ≤ 3 * R)
    (h0 : rowW w n R2 P0 s = ∑ i ∈ range n, (f i * 1) * (2 ^ w) ^ i)
    (h1 : rowW w n R2 P1 s = ∑ i ∈ range n, (f i * i) * (2 ^ w) ^ i)
    (h2 : rowW w n R2 P2 s = ∑ i ∈ range n, (f i * sq R i) * (2 ^ w) ^ i) :
    rowXYg w n R R2 P0 P1 P2 iy s = ∑ i ∈ range n, (f i * sq (2 * R) (i + iy)) * (2 ^ w) ^ i + s := by
  unfold rowXYg rowWS
  set X := (2 ^ w : ℕ)
  by_cases hR : R ≤ iy
  · rw [Nat.ble_eq_true_of_le hR]
    show rowW w n R2 P2 s + s + 2 * (iy - R) * rowW w n R2 P1 s -
      (iy - R) * (2 * R - (iy - R)) * rowW w n R2 P0 s = _
    rw [h0, h1, h2]
    have e : ∑ i ∈ range n, f i * sq R i * X ^ i + s + 2 * (iy - R) * ∑ i ∈ range n, f i * i * X ^ i =
        (∑ i ∈ range n, f i * sq (2 * R) (i + iy) * X ^ i + s) +
          (iy - R) * (2 * R - (iy - R)) * ∑ i ∈ range n, f i * 1 * X ^ i := by
      have e0 : ∑ i ∈ range n, f i * sq R i * X ^ i + 2 * (iy - R) * ∑ i ∈ range n, f i * i * X ^ i =
          ∑ i ∈ range n, f i * sq (2 * R) (i + iy) * X ^ i +
            (iy - R) * (2 * R - (iy - R)) * ∑ i ∈ range n, f i * 1 * X ^ i := by
        simp only [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        have := xy_pos R i iy hR hiy
        calc _ = (sq R i + 2 * (iy - R) * i) * (f i * X ^ i) := by ring
          _ = (sq (2 * R) (i + iy) + (iy - R) * (2 * R - (iy - R))) * (f i * X ^ i) := by rw [this]
          _ = _ := by ring
      omega
    rw [e, Nat.add_sub_cancel]
  · have hb : Nat.ble R iy = false := by
      cases h : Nat.ble R iy with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true h) hR
    rw [hb]
    show rowW w n R2 P2 s + s + (R - iy) * (2 * R + (R - iy)) * rowW w n R2 P0 s -
      2 * (R - iy) * rowW w n R2 P1 s = _
    rw [h0, h1, h2]
    have e : ∑ i ∈ range n, f i * sq R i * X ^ i + s +
          (R - iy) * (2 * R + (R - iy)) * ∑ i ∈ range n, f i * 1 * X ^ i =
        (∑ i ∈ range n, f i * sq (2 * R) (i + iy) * X ^ i + s) +
          2 * (R - iy) * ∑ i ∈ range n, f i * i * X ^ i := by
      have e0 : ∑ i ∈ range n, f i * sq R i * X ^ i +
            (R - iy) * (2 * R + (R - iy)) * ∑ i ∈ range n, f i * 1 * X ^ i =
          ∑ i ∈ range n, f i * sq (2 * R) (i + iy) * X ^ i +
            2 * (R - iy) * ∑ i ∈ range n, f i * i * X ^ i := by
        simp only [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        have := xy_neg R i iy (by omega)
        calc _ = (sq R i + (R - iy) * (2 * R + (R - iy))) * (f i * X ^ i) := by ring
          _ = (sq (2 * R) (i + iy) + 2 * (R - iy) * i) * (f i * X ^ i) := by rw [this]
          _ = _ := by ring
      omega
    rw [e, Nat.add_sub_cancel]

lemma sq_le (R i : ℕ) (hi : i ≤ 2 * R) : sq R i ≤ R * R := by
  unfold sq
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  rcases le_total i R with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_mul, zero_add]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  · rw [Nat.sub_eq_zero_of_le h, zero_mul, add_zero]
    exact Nat.mul_le_mul (by omega) (by omega)

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

lemma shell_le (R2 A x : Nat) : shell R2 A x ≤ x := by
  rw [shell_eq]; split_ifs <;> omega

lemma F0_le (N R2 A : Nat) : F0 N R2 A ≤ N :=
  (shell_le _ _ _).trans (Nat.div_le_self _ _)

lemma F1_le (N R2 A : Nat) : F1 N R2 A ≤ N :=
  (shell_le _ _ _).trans (Nat.div_le_self _ _)

lemma F2_le (N R2 A : Nat) : F2 N R2 A ≤ N :=
  (shell_le _ _ _).trans (Nat.div_le_self _ _)

lemma F3_le (N R2 A : Nat) : F3 N R2 A ≤ N := by
  refine (shell_le _ _ _).trans ?_
  show N * A / (290 * A + 234) ≤ N
  rcases Nat.eq_zero_or_pos A with h | h
  · simp [h]
  · exact Nat.div_le_of_le_mul (by nlinarith)

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
  rw [winA_eq, winA_eq, winA_eq, winA_eq, winA_eq] at h3
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
  have e3 : Z * y + x < Z * Z := by
    have : Z * (y + 1) ≤ Z * Z := Nat.mul_le_mul_left _ (by omega)
    have e : Z * (y + 1) = Z * y + Z := by ring
    omega
  rw [hsl, dig_window _ _ _ _ (by simpa using e1), hRg, dig_window _ _ _ _ e2,
    dig_window _ _ _ _ e3] at hR
  rw [show x + Z * (y + Z * z) = Z * Z * z + (Z * y + x) by ring, ← hR]
  congr 1
  ring

end Row
end OVNS
