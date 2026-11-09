import OddViscousNS.Closed.Cert.Bounds

/-!
# Fast checking of the U785 certificate: the bound in scaled natural numbers

A certificate leaf needs `εq < gap e b` (`accept e b = true`). `gap` is computed in exact rationals, and
Lean's `Rat` normalises by `gcd` after every operation; in the kernel that costs about 20 ms per box.

Here the same quantity is bounded in raw `Nat` arithmetic at scale `S = 2⁸⁰`. Every intermediate value of
`gap` gets only the one-sided bound its use needs (`Lo n x : n ≤ x S`, `Hi n x : x S ≤ n`): truncated
subtraction is either exactly the `max 0 (…)` of `gap` or errs on the safe side, the sign split of
`1 - 2 ρ` in the denominator is written branch-free, and the test is
`ε + m K⁺ + s U⁺ C⁺ < 1` in nonnegative integers. `ok_sound` proves that a passing test gives
`εq < gap e b`, so `acceptN_sound` reduces to the exact `accept` and `Sound.lean` is untouched.

`check_of_trN` is what the generated theorems in `Cert/Check/E*_*.lean` use: the statement stays
`check (edgeOf i) n box = true`. The box corners are dyadic, so they are encoded exactly (`boxOK`);
the edge data get floor/ceiling bounds; the six sign facts of the 41 edges are one kernel computation
(`edgeChk_all`). Python mirror: `OddViscousNS_data/pilot_check/accn.py` (all 530,690 leaves pass).
-/

namespace OVNS.Cert.Fast

/-- The scale `2⁸⁰`. -/
def S : ℕ := 1208925819614629174706176

theorem S_eq : S = 2 ^ 80 := by norm_num [S]

theorem S_pos : 0 < S := by norm_num [S]

theorem S_posQ : (0 : ℚ) < S := by exact_mod_cast S_pos

/-- `⌊a b / S⌋`. -/
def mD (a b : ℕ) : ℕ := Nat.div (Nat.mul a b) 1208925819614629174706176

/-- `⌈a b / S⌉`. -/
def mU (a b : ℕ) : ℕ := Nat.div (Nat.add (Nat.mul a b) 1208925819614629174706175) 1208925819614629174706176

/-- `⌊a S / b⌋`. -/
def dD (a b : ℕ) : ℕ := Nat.div (Nat.mul a 1208925819614629174706176) b

/-- `⌈a S / b⌉` (for `b > 0`). -/
def dU (a b : ℕ) : ℕ := Nat.div (Nat.add (Nat.mul a 1208925819614629174706176) (Nat.sub b 1)) b

/-- `min`. -/
def mn (a b : ℕ) : ℕ := Bool.rec b a (Nat.ble a b)

/-- `max`. -/
def mx (a b : ℕ) : ℕ := Bool.rec a b (Nat.ble a b)

theorem mD_eq (a b : ℕ) : mD a b = a * b / S := rfl

theorem mU_eq (a b : ℕ) : mU a b = (a * b + (S - 1)) / S := rfl

theorem dD_eq (a b : ℕ) : dD a b = a * S / b := rfl

theorem dU_eq (a b : ℕ) : dU a b = (a * S + (b - 1)) / b := rfl

theorem mn_eq (a b : ℕ) : mn a b = min a b := by
  unfold mn
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hab => by rw [Nat.ble_eq_true_of_le hab] at h; exact absurd h (by decide)
    simp [this]; omega
  · have : a ≤ b := Nat.le_of_ble_eq_true h
    simp [this]

theorem mx_eq (a b : ℕ) : mx a b = max a b := by
  unfold mx
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hab => by rw [Nat.ble_eq_true_of_le hab] at h; exact absurd h (by decide)
    simp [this]; omega
  · have : a ≤ b := Nat.le_of_ble_eq_true h
    simp [this]

/-- `n ≤ x·S`. -/
def Lo (n : ℕ) (x : ℚ) : Prop := (n : ℚ) ≤ x * S

/-- `x·S ≤ n`. -/
def Hi (n : ℕ) (x : ℚ) : Prop := x * S ≤ n

theorem Lo.nonneg {n : ℕ} {x : ℚ} (h : Lo n x) : 0 ≤ x := by
  have h0 : (0 : ℚ) ≤ n := by positivity
  have := h0.trans h
  exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using this) S_posQ

theorem Lo.pos {n : ℕ} {x : ℚ} (h : Lo n x) (hn : 0 < n) : 0 < x := by
  have h0 : (0 : ℚ) < n := by exact_mod_cast hn
  have := h0.trans_le h
  exact pos_of_mul_pos_left (by simpa [mul_comm] using this) S_posQ.le

theorem lo_exact {n : ℕ} {x : ℚ} (h : (n : ℚ) = x * S) : Lo n x := le_of_eq h
theorem hi_exact {n : ℕ} {x : ℚ} (h : (n : ℚ) = x * S) : Hi n x := ge_of_eq h

theorem lo_zero (x : ℚ) (hx : 0 ≤ x) : Lo 0 x := by
  unfold Lo; push_cast; exact mul_nonneg hx S_posQ.le

theorem lo_add {a b : ℕ} {x y : ℚ} (ha : Lo a x) (hb : Lo b y) : Lo (a + b) (x + y) := by
  unfold Lo at *; push_cast; nlinarith

theorem hi_add {a b : ℕ} {x y : ℚ} (ha : Hi a x) (hb : Hi b y) : Hi (a + b) (x + y) := by
  unfold Hi at *; push_cast; nlinarith

/-- Truncated subtraction gives a lower bound of `max 0 (x - y)`. -/
theorem lo_sub {a b : ℕ} {x y : ℚ} (ha : Lo a x) (hb : Hi b y) : Lo (a - b) (max 0 (x - y)) := by
  unfold Lo Hi at *
  rcases le_total b a with hab | hab
  · rw [Nat.cast_sub hab]
    calc (a : ℚ) - b ≤ (x - y) * S := by nlinarith
      _ ≤ max 0 (x - y) * S := mul_le_mul_of_nonneg_right (le_max_right _ _) S_posQ.le
  · rw [Nat.sub_eq_zero_of_le hab]; push_cast
    exact mul_nonneg (le_max_left _ _) S_posQ.le

theorem lo_sub' {a b : ℕ} {x y : ℚ} (ha : Lo a x) (hb : Hi b y) (hxy : y ≤ x) : Lo (a - b) (x - y) := by
  have := lo_sub ha hb
  rwa [max_eq_right (by linarith)] at this

theorem hi_sub {a b : ℕ} {x y : ℚ} (ha : Hi a x) (hb : Lo b y) : Hi (a - b) (x - y) := by
  unfold Lo Hi at *
  rcases le_total b a with hab | hab
  · rw [Nat.cast_sub hab]; nlinarith
  · rw [Nat.sub_eq_zero_of_le hab]; push_cast
    have : (a : ℚ) ≤ b := by exact_mod_cast hab
    nlinarith

theorem hi_sub_max {a b : ℕ} {x y : ℚ} (ha : Hi a x) (hb : Lo b y) : Hi (a - b) (max 0 (x - y)) := by
  have h1 := hi_sub ha hb
  unfold Hi at *
  rcases le_total 0 (x - y) with h | h
  · rwa [max_eq_right h]
  · rw [max_eq_left h]; push_cast; simp only [zero_mul]; positivity

theorem lo_mul {a b : ℕ} {x y : ℚ} (ha : Lo a x) (hb : Lo b y) : Lo (mD a b) (x * y) := by
  have hx := ha.nonneg; have hy := hb.nonneg
  unfold Lo at *
  rw [mD_eq]
  have h1 : ((a * b / S : ℕ) : ℚ) * S ≤ (a * b : ℕ) := by
    exact_mod_cast Nat.div_mul_le_self (a * b) S
  have h2 : ((a * b : ℕ) : ℚ) ≤ (x * S) * (y * S) := by
    push_cast; exact mul_le_mul ha hb (by positivity) (by positivity)
  have h3 : ((a * b / S : ℕ) : ℚ) * S ≤ (x * y * S) * S := by nlinarith
  exact le_of_mul_le_mul_right h3 S_posQ

theorem hi_mul {a b : ℕ} {x y : ℚ} (hx : 0 ≤ x) (ha : Hi a x) (hb : Hi b y) : Hi (mU a b) (x * y) := by
  unfold Hi at *
  rw [mU_eq]
  have h1 : ((a * b : ℕ) : ℚ) ≤ (((a * b + (S - 1)) / S : ℕ) : ℚ) * S := by
    have := Nat.lt_div_mul_add (a := a * b + (S - 1)) S_pos
    have h' : a * b ≤ (a * b + (S - 1)) / S * S := by
      have := Nat.div_add_mod' (a * b + (S - 1)) S
      have hm := Nat.mod_lt (a * b + (S - 1)) S_pos
      have hS := S_pos
      omega
    exact_mod_cast h'
  rcases le_total 0 y with hy | hy
  · have h2 : (x * S) * (y * S) ≤ ((a * b : ℕ) : ℚ) := by
      push_cast; exact mul_le_mul ha hb (by positivity) (by positivity)
    have h3 : (x * y * S) * S ≤ (((a * b + (S - 1)) / S : ℕ) : ℚ) * S := by nlinarith
    exact le_of_mul_le_mul_right h3 S_posQ
  · have : x * y * S ≤ 0 := by
      have : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy
      nlinarith [S_posQ]
    exact this.trans (by positivity)

theorem lo_div {a b : ℕ} {x y : ℚ} (ha : Lo a x) (hb : Hi b y) (hy : 0 < y) : Lo (dD a b) (x / y) := by
  have hx := ha.nonneg
  unfold Lo Hi at *
  rw [dD_eq]
  have hbpos : (0 : ℚ) < b := lt_of_lt_of_le (mul_pos hy S_posQ) hb
  have hb' : 0 < b := by exact_mod_cast hbpos
  have h1 : ((a * S / b : ℕ) : ℚ) * b ≤ (a * S : ℕ) := by exact_mod_cast Nat.div_mul_le_self (a * S) b
  have h2 : ((a * S / b : ℕ) : ℚ) ≤ (a : ℚ) * S / b := by
    rw [le_div_iff₀ hbpos]; push_cast at h1 ⊢; linarith
  have h3 : (a : ℚ) * S / b ≤ x * S * S / (y * S) := by
    rw [div_le_div_iff₀ hbpos (mul_pos hy S_posQ)]
    have : (a : ℚ) * (y * S) ≤ x * S * b := by
      have := mul_le_mul ha hb (by positivity) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hb (show (0 : ℚ) ≤ x * S by positivity)]
    nlinarith [S_posQ]
  have h4 : x * S * S / (y * S) = x / y * S := by field_simp
  linarith [h4 ▸ h3]

theorem hi_div {a b : ℕ} {x y : ℚ} (hx : 0 ≤ x) (ha : Hi a x) (hb : Lo b y) (hb0 : 0 < b) :
    Hi (dU a b) (x / y) := by
  have hy := hb.pos hb0
  unfold Lo Hi at *
  rw [dU_eq]
  have hbpos : (0 : ℚ) < b := by exact_mod_cast hb0
  have h1 : a * S ≤ (a * S + (b - 1)) / b * b := by
    have := Nat.div_add_mod' (a * S + (b - 1)) b
    have hm := Nat.mod_lt (a * S + (b - 1)) hb0
    omega
  have h1' : (a : ℚ) * S ≤ (((a * S + (b - 1)) / b : ℕ) : ℚ) * b := by exact_mod_cast h1
  have h2 : x / y * S ≤ (a : ℚ) * S / b := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hy hbpos]
    have : x * S * b ≤ a * (y * S) := by
      have := mul_le_mul ha hb (by positivity) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hb (show (0 : ℚ) ≤ (a : ℚ) by positivity)]
    nlinarith [S_posQ]
  have h3 : (a : ℚ) * S / b ≤ (((a * S + (b - 1)) / b : ℕ) : ℚ) := by
    rw [div_le_iff₀ hbpos]; exact h1'
  linarith

theorem lo_min {a b : ℕ} {x y : ℚ} (ha : Lo a x) (hb : Lo b y) : Lo (mn a b) (min x y) := by
  unfold Lo at *; rw [mn_eq]; push_cast
  rcases le_total x y with h | h
  · rw [min_eq_left h]; exact (min_le_left _ _).trans ha
  · rw [min_eq_right h]; exact (min_le_right _ _).trans hb

theorem hi_min {a b : ℕ} {x y : ℚ} (ha : Hi a x) (hb : Hi b y) : Hi (mn a b) (min x y) := by
  unfold Hi at *; rw [mn_eq]; push_cast
  rcases le_total a b with h | h
  · rw [min_eq_left (by exact_mod_cast h : (a : ℚ) ≤ b)]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) S_posQ.le).trans ha
  · rw [min_eq_right (by exact_mod_cast h : (b : ℚ) ≤ a)]
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) S_posQ.le).trans hb

theorem lo_max {a b : ℕ} {x y : ℚ} (ha : Lo a x) (hb : Lo b y) : Lo (mx a b) (max x y) := by
  unfold Lo at *; rw [mx_eq]; push_cast
  rcases le_total a b with h | h
  · rw [max_eq_right (by exact_mod_cast h : (a : ℚ) ≤ b)]
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) S_posQ.le)
  · rw [max_eq_left (by exact_mod_cast h : (b : ℚ) ≤ a)]
    exact ha.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) S_posQ.le)

theorem hi_max {a b : ℕ} {x y : ℚ} (ha : Hi a x) (hb : Hi b y) : Hi (mx a b) (max x y) := by
  unfold Hi at *; rw [mx_eq]; push_cast
  rcases le_total x y with h | h
  · rw [max_eq_right h]; exact hb.trans (le_max_right _ _)
  · rw [max_eq_left h]; exact ha.trans (le_max_left _ _)

/-! ### Encodings of rationals, the square root, and `G` -/

/-- `⌊q S⌋` for `q ≥ 0`. -/
def flQ (q : ℚ) : ℕ := Nat.div (Nat.mul q.num.toNat 1208925819614629174706176) q.den

/-- `⌈q S⌉` for `q ≥ 0`. -/
def ceQ (q : ℚ) : ℕ :=
  Nat.div (Nat.add (Nat.mul q.num.toNat 1208925819614629174706176) (Nat.sub q.den 1)) q.den

theorem num_toNat_cast {q : ℚ} (hq : 0 ≤ q) : ((q.num.toNat : ℕ) : ℚ) = q.num := by
  have : 0 ≤ q.num := Rat.num_nonneg.2 hq
  exact_mod_cast Int.toNat_of_nonneg this

theorem q_eq_num_div {q : ℚ} (hq : 0 ≤ q) : q = (q.num.toNat : ℚ) / q.den := by
  rw [num_toNat_cast hq]; exact (Rat.num_div_den q).symm

theorem lo_flQ {q : ℚ} (hq : 0 ≤ q) : Lo (flQ q) q := by
  unfold Lo flQ
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have h1 : (q.num.toNat * S / q.den : ℕ) * q.den ≤ q.num.toNat * S := Nat.div_mul_le_self _ _
  have h1' : ((q.num.toNat * S / q.den : ℕ) : ℚ) * q.den ≤ (q.num.toNat : ℚ) * S := by exact_mod_cast h1
  show ((q.num.toNat * S / q.den : ℕ) : ℚ) ≤ q * S
  have hq' : q * S = (q.num.toNat : ℚ) * S / q.den := by
    conv_lhs => rw [q_eq_num_div hq]
    ring
  rw [hq', le_div_iff₀ hd]
  linarith

theorem hi_ceQ {q : ℚ} (hq : 0 ≤ q) : Hi (ceQ q) q := by
  unfold Hi ceQ
  have hd0 := q.den_pos
  have hd : (0 : ℚ) < q.den := by exact_mod_cast hd0
  have h1 : q.num.toNat * S ≤ (q.num.toNat * S + (q.den - 1)) / q.den * q.den := by
    have := Nat.div_add_mod' (q.num.toNat * S + (q.den - 1)) q.den
    have hm := Nat.mod_lt (q.num.toNat * S + (q.den - 1)) hd0
    omega
  have h1' : (q.num.toNat : ℚ) * S ≤ (((q.num.toNat * S + (q.den - 1)) / q.den : ℕ) : ℚ) * q.den := by
    exact_mod_cast h1
  show q * S ≤ (((q.num.toNat * S + (q.den - 1)) / q.den : ℕ) : ℚ)
  have hq' : q * S = (q.num.toNat : ℚ) * S / q.den := by
    conv_lhs => rw [q_eq_num_div hq]
    ring
  rw [hq', div_le_iff₀ hd]
  linarith

/-- A rational whose denominator divides `S` is encoded exactly. -/
theorem flQ_exact {q : ℚ} (hq : 0 ≤ q) (hd : S % q.den = 0) : (flQ q : ℚ) = q * S := by
  unfold flQ
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hd
  have hd0 := q.den_pos
  show ((q.num.toNat * S / q.den : ℕ) : ℚ) = q * S
  have : q.num.toNat * S / q.den = q.num.toNat * k := by
    rw [hk, ← mul_assoc, mul_comm (q.num.toNat) q.den, mul_assoc, Nat.mul_div_cancel_left _ hd0]
  rw [this]
  have hd' : (q.den : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hS : (S : ℚ) = q.den * k := by exact_mod_cast hk
  conv_rhs => rw [q_eq_num_div hq, hS]
  push_cast
  field_simp

/-- `usqrt` is monotone. -/
theorem usqrt_mono {v w : ℚ} (hvw : v ≤ w) : usqrt v ≤ usqrt w := by
  unfold usqrt
  by_cases hv : v ≤ 0
  · rw [if_pos hv]; split_ifs <;> positivity
  · have hw : ¬ w ≤ 0 := fun h => hv (hvw.trans h)
    rw [if_neg hv, if_neg hw]
    have hv0 : 0 < v := not_le.mp hv
    have hw0 : 0 < w := not_le.mp hw
    apply div_le_div_of_nonneg_right _ (by positivity)
    have key : (v.num.toNat * 10 ^ 24 - 1) / v.den ≤ (w.num.toNat * 10 ^ 24 - 1) / w.den := by
      set A := (v.num.toNat * 10 ^ 24 - 1) / v.den
      have hnv : 1 ≤ v.num.toNat := by
        have := Rat.num_pos.2 hv0; omega
      have hnw : 1 ≤ w.num.toNat := by
        have := Rat.num_pos.2 hw0; omega
      have hA : A * v.den ≤ v.num.toNat * 10 ^ 24 - 1 := Nat.div_mul_le_self _ _
      have hA' : A * v.den < v.num.toNat * 10 ^ 24 := by
        have : 1 ≤ v.num.toNat * 10 ^ 24 := by nlinarith
        omega
      -- A < v · 10²⁴ ≤ w · 10²⁴
      have hvq : (A : ℚ) < v * 10 ^ 24 := by
        have h1 : ((A * v.den : ℕ) : ℚ) < ((v.num.toNat * 10 ^ 24 : ℕ) : ℚ) := by exact_mod_cast hA'
        have hd : (0 : ℚ) < v.den := by exact_mod_cast v.den_pos
        rw [q_eq_num_div hv0.le]
        push_cast at h1
        rw [div_mul_eq_mul_div, lt_div_iff₀ hd]
        linarith
      have hwq : (A : ℚ) * w.den < w.num.toNat * 10 ^ 24 := by
        have hd : (0 : ℚ) < w.den := by exact_mod_cast w.den_pos
        have : (A : ℚ) < w * 10 ^ 24 := lt_of_lt_of_le hvq (by nlinarith)
        rw [q_eq_num_div hw0.le, div_mul_eq_mul_div, lt_div_iff₀ hd] at this
        linarith
      have hwn : A * w.den < w.num.toNat * 10 ^ 24 := by exact_mod_cast hwq
      rw [Nat.le_div_iff_mul_le w.den_pos]
      omega
    have := Nat.sqrt_le_sqrt key
    exact_mod_cast Nat.add_le_add_right this 1

/-- Upper bound of `usqrt (n/S)`, times `S`. -/
def uq (n : ℕ) : ℕ :=
  Bool.rec (Nat.div (Nat.add (Nat.mul (Nat.add (Nat.sqrt (Nat.div (Nat.sub (Nat.mul n
    1000000000000000000000000) 1) 1208925819614629174706176)) 1) 1208925819614629174706176)
    999999999999) 1000000000000) 0 (Nat.beq n 0)

theorem hi_usqrt {n : ℕ} {v : ℚ} (h : Hi n v) : Hi (uq n) (usqrt v) := by
  unfold Hi at *
  by_cases hv : v ≤ 0
  · rw [show usqrt v = 0 by simp [usqrt, hv]]; simp
  have hv0 : 0 < v := not_le.mp hv
  have hn : 0 < n := by
    have : (0 : ℚ) < n := lt_of_lt_of_le (mul_pos hv0 S_posQ) h
    exact_mod_cast this
  -- usqrt v ≤ usqrt (n / S), which the formula computes
  have hle : v ≤ (n : ℚ) / S := by rw [le_div_iff₀ S_posQ]; exact h
  have hmono := usqrt_mono hle
  have hnS : (0 : ℚ) < (n : ℚ) / S := div_pos (by exact_mod_cast hn) S_posQ
  set N := Nat.sqrt ((n * 10 ^ 24 - 1) / S) with hN
  -- the formula at n / S
  have hform : usqrt ((n : ℚ) / S) ≤ ((N + 1 : ℕ) : ℚ) / 10 ^ 12 := by
    unfold usqrt
    rw [if_neg (not_le.2 hnS)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    set q : ℚ := (n : ℚ) / S
    have key : (q.num.toNat * 10 ^ 24 - 1) / q.den ≤ (n * 10 ^ 24 - 1) / S := by
      set A := (q.num.toNat * 10 ^ 24 - 1) / q.den
      have hq0 : 0 < q := hnS
      have hnq : 1 ≤ q.num.toNat := by have := Rat.num_pos.2 hq0; omega
      have hA : A * q.den ≤ q.num.toNat * 10 ^ 24 - 1 := Nat.div_mul_le_self _ _
      have hA' : A * q.den < q.num.toNat * 10 ^ 24 := by
        have : 1 ≤ q.num.toNat * 10 ^ 24 := by nlinarith
        omega
      have hqq : (A : ℚ) < q * 10 ^ 24 := by
        have h1 : ((A * q.den : ℕ) : ℚ) < ((q.num.toNat * 10 ^ 24 : ℕ) : ℚ) := by exact_mod_cast hA'
        have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
        rw [q_eq_num_div hq0.le]
        push_cast at h1
        rw [div_mul_eq_mul_div, lt_div_iff₀ hd]
        linarith
      have hS : (A : ℚ) * S < n * 10 ^ 24 := by
        have : (A : ℚ) < (n : ℚ) / S * 10 ^ 24 := hqq
        rw [div_mul_eq_mul_div, lt_div_iff₀ S_posQ] at this
        linarith
      have hSn : A * S < n * 10 ^ 24 := by exact_mod_cast hS
      rw [Nat.le_div_iff_mul_le S_pos]
      omega
    have := Nat.sqrt_le_sqrt key
    exact_mod_cast Nat.add_le_add_right this 1
  -- the rounding up to `uq n`
  have huq : ((N + 1 : ℕ) : ℚ) / 10 ^ 12 * S ≤ (uq n : ℚ) := by
    have hbeq : Nat.beq n 0 = false := by
      cases h : Nat.beq n 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hn.ne'
    have : uq n = ((N + 1) * S + 999999999999) / 1000000000000 := by
      simp only [uq, hbeq, hN]; rfl
    rw [this]
    have h1 : (N + 1) * S ≤ ((N + 1) * S + 999999999999) / 1000000000000 * 1000000000000 := by
      have := Nat.div_add_mod' ((N + 1) * S + 999999999999) 1000000000000
      have hm := Nat.mod_lt ((N + 1) * S + 999999999999) (show 0 < 1000000000000 by norm_num)
      omega
    have h1' : ((N + 1 : ℕ) : ℚ) * S ≤ ((((N + 1) * S + 999999999999) / 1000000000000 : ℕ) : ℚ) * 10 ^ 12 := by
      have := (show (((N + 1) * S : ℕ) : ℚ) ≤ ((((N + 1) * S + 999999999999) / 1000000000000 * 1000000000000 : ℕ) : ℚ) by exact_mod_cast h1)
      push_cast at this ⊢; linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    exact h1'
  calc usqrt v * S ≤ usqrt ((n : ℚ) / S) * S := mul_le_mul_of_nonneg_right hmono S_posQ.le
    _ ≤ ((N + 1 : ℕ) : ℚ) / 10 ^ 12 * S := mul_le_mul_of_nonneg_right hform S_posQ.le
    _ ≤ uq n := huq

/-- `G` is monotone in both arguments on the nonnegative quadrant. -/
theorem Gq_le {m w M W : ℚ} (hm : 0 ≤ m) (hw : 0 ≤ w) (hmM : m ≤ M) (hwW : w ≤ W) :
    Gq m w ≤ M / 2 + (if M = 0 ∨ W = 0 then 0 else M * W / (2 * (W + 4 * aq * M))) := by
  have ha : (0 : ℚ) < aq := by norm_num [aq]
  unfold Gq
  split_ifs with h1 h2 h2
  · -- m, w ≠ 0 but M = 0 or W = 0: impossible
    rcases h2 with h2 | h2
    · exact absurd (le_antisymm (h2 ▸ hmM) hm) h1.1
    · exact absurd (le_antisymm (h2 ▸ hwW) hw) h1.2
  · have hm0 : 0 < m := lt_of_le_of_ne hm (Ne.symm h1.1)
    have hw0 : 0 < w := lt_of_le_of_ne hw (Ne.symm h1.2)
    have hM0 : 0 < M := lt_of_lt_of_le hm0 hmM
    have hW0 : 0 < W := lt_of_lt_of_le hw0 hwW
    have hd1 : 0 < 2 * (w + 4 * aq * m) := by positivity
    have hd2 : 0 < 2 * (W + 4 * aq * M) := by positivity
    have : m * w / (2 * (w + 4 * aq * m)) ≤ M * W / (2 * (W + 4 * aq * M)) := by
      rw [div_le_div_iff₀ hd1 hd2]
      nlinarith [mul_nonneg (mul_nonneg hw0.le hW0.le) (sub_nonneg.2 hmM),
        mul_nonneg (mul_nonneg ha.le (mul_nonneg hm0.le hM0.le)) (sub_nonneg.2 hwW)]
    linarith
  · simp; linarith
  · have hM : 0 ≤ M := hm.trans hmM
    have hW : 0 ≤ W := hw.trans hwW
    have : 0 ≤ M * W / (2 * (W + 4 * aq * M)) := by positivity
    linarith

/-! ### The exact pieces of `gap` -/

def zL (e : Edge) (b : Box) : ℚ := e.z b.ul
def zH (e : Edge) (b : Box) : ℚ := e.z b.uh
def rL (e : Edge) (b : Box) : ℚ := e.ρ b.ul b.pl
def rH (e : Edge) (b : Box) : ℚ := e.ρ b.uh b.ph
def dLq (e : Edge) (b : Box) : ℚ := max 1 (Cq - Dq * zH e b + Lq * rL e b)
def dHq (e : Edge) (b : Box) : ℚ := Cq - Dq * zL e b + Lq * rH e b
def tL (e : Edge) (b : Box) : ℚ := b.vl * min (zL e b) (min (1 / (2 - rL e b)) (1 / dHq e b))
def tH (e : Edge) (b : Box) : ℚ := b.vh * min (zH e b) (min (1 / (2 - rH e b)) (1 / dLq e b))
def RL (e : Edge) (b : Box) : ℚ := rL e b * tL e b
def RH (e : Edge) (b : Box) : ℚ := rH e b * tH e b
def denQ (e : Edge) (b : Box) : ℚ :=
  max (1 + (1 - 2 * rL e b) * tL e b) (1 + (1 - 2 * rL e b) * tH e b)
def defQ (e : Edge) (b : Box) : ℚ :=
  if denQ e b ≠ 0 then rL e b * (1 - tH e b) ^ 2 / denQ e b else 0
def harmQ (e : Edge) (b : Box) : ℚ := max 0 (1 - RL e b * rL e b - defQ e b)
def resQ (e : Edge) (b : Box) : ℚ := Gq (1 - RL e b ^ 2) (harmQ e b)
def highQ (e : Edge) (b : Box) : ℚ := zH e b - rL e b
def llhQ (e : Edge) (b : Box) : ℚ := c1q * RH e b * usqrt (min (1 - rL e b) (h2q * highQ e b))
def cubQ (e : Edge) (b : Box) : ℚ := min κq (llhQ e b + usqrt (gramq * (1 + aq) * resQ e b))
def kinQ (e : Edge) (b : Box) : ℚ :=
  min (tH e b / a0q) (min (RH e b + (1 - RH e b) / h2q)
    (min (tH e b * (rL e b + (1 - rL e b) / a0q))
      (RH e b + (1 - RH e b) / h3q + βq * tH e b * highQ e b)))

theorem gap_eq' (e : Edge) (b : Box) :
    gap e b = 1 - e.m * kinQ e b - sq * usqrt (e.Y b.uh) * cubQ e b := rfl

theorem X_eq (e : Edge) (u : ℚ) : e.X u = e.xh - e.width * (1 - u) := by
  simp only [Edge.X, Edge.xl]; ring

theorem Y_eq (e : Edge) (u : ℚ) : e.Y u = e.yh - e.m * e.width * (1 - u) := by
  simp only [Edge.Y, Edge.yl]; ring

/-! ### The bound in scaled natural numbers -/

@[irreducible] def h2D : ℕ := flQ h2q
@[irreducible] def h2U : ℕ := ceQ h2q
@[irreducible] def h3D : ℕ := flQ h3q
@[irreducible] def h2mD : ℕ := flQ (h2q - 1)
@[irreducible] def h2mU : ℕ := ceQ (h2q - 1)
@[irreducible] def DD : ℕ := flQ Dq
@[irreducible] def DU : ℕ := ceQ Dq
@[irreducible] def CD : ℕ := flQ Cq
@[irreducible] def CU : ℕ := ceQ Cq
@[irreducible] def LD : ℕ := flQ Lq
@[irreducible] def LU : ℕ := ceQ Lq
@[irreducible] def bU : ℕ := ceQ βq
@[irreducible] def a0D : ℕ := flQ a0q
@[irreducible] def aD : ℕ := flQ aq
@[irreducible] def aU : ℕ := ceQ aq
@[irreducible] def sU : ℕ := ceQ sq
@[irreducible] def kU : ℕ := ceQ κq
@[irreducible] def gU : ℕ := ceQ gramq
@[irreducible] def c1U : ℕ := ceQ c1q
@[irreducible] def eU : ℕ := ceQ εq

/-- The scaled inputs: bounds of the edge data, the exact box corners. -/
structure In where
  xhD : ℕ
  xhU : ℕ
  yhD : ℕ
  yhU : ℕ
  mL : ℕ
  mH : ℕ
  wdD : ℕ
  wdU : ℕ
  ul : ℕ
  uh : ℕ
  pl : ℕ
  ph : ℕ
  vl : ℕ
  vh : ℕ

namespace In

def XD (I : In) (u : ℕ) : ℕ := (I.xhD - (mU I.wdU ((S - u))))
def XU (I : In) (u : ℕ) : ℕ := (I.xhU - (mD I.wdD ((S - u))))
def YD (I : In) (u : ℕ) : ℕ := (I.yhD - (mU (mU I.mH I.wdU) ((S - u))))
def YU (I : In) (u : ℕ) : ℕ := (I.yhU - (mD (mD I.mL I.wdD) ((S - u))))
def zD (I : In) (u : ℕ) : ℕ := dD (I.XD u) (I.YU u)
def zU (I : In) (u : ℕ) : ℕ := dU (I.XU u) (I.YD u)
def loD (z : ℕ) : ℕ := dD (((mD h2D z) - S)) h2mU
def loU (z : ℕ) : ℕ := dU (((mU h2U z) - S)) h2mD
def rD (I : In) (u p : ℕ) : ℕ := ((mD ((S - p)) (loD (I.zD u))) + (mD p (I.zD u)))
def rU (I : In) (u p : ℕ) : ℕ := ((mU ((S - p)) (loU (I.zU u))) + (mU p (I.zU u)))
def rlD (I : In) : ℕ := I.rD I.ul I.pl
def rlU (I : In) : ℕ := I.rU I.ul I.pl
def rhD (I : In) : ℕ := I.rD I.uh I.ph
def rhU (I : In) : ℕ := I.rU I.uh I.ph
def dlD (I : In) : ℕ := mx S ((((CD + (mD LD I.rlD))) - (mU DU (I.zU I.uh))))
def dlU (I : In) : ℕ := mx S ((((CU + (mU LU I.rlU))) - (mD DD (I.zD I.uh))))
def dhD (I : In) : ℕ := (((CD + (mD LD I.rhD))) - (mU DU (I.zU I.ul)))
def dhU (I : In) : ℕ := (((CU + (mU LU I.rhU))) - (mD DD (I.zD I.ul)))
def tlD (I : In) : ℕ := mD I.vl (mn (I.zD I.ul) (mn (dD S ((((2 * S)) - I.rlD))) (dD S I.dhU)))
def tlU (I : In) : ℕ := mU I.vl (mn (I.zU I.ul) (mn (dU S ((((2 * S)) - I.rlU))) (dU S I.dhD)))
def thD (I : In) : ℕ := mD I.vh (mn (I.zD I.uh) (mn (dD S ((((2 * S)) - I.rhD))) (dD S I.dlU)))
def thU (I : In) : ℕ := mU I.vh (mn (I.zU I.uh) (mn (dU S ((((2 * S)) - I.rhU))) (dU S I.dlD)))
def RlD (I : In) : ℕ := mD I.rlD I.tlD
def RlU (I : In) : ℕ := mU I.rlU I.tlU
def RhU (I : In) : ℕ := mU I.rhU I.thU
def prU (I : In) : ℕ := (S - (mD I.RlD I.RlD))
def denD (I : In) : ℕ :=
  (S + mD (S - 2 * I.rlU) (mx I.tlD I.thD)) - mU (2 * I.rlU - S) (mn I.tlU I.thU)
def denU (I : In) : ℕ :=
  (S + mU (S - 2 * I.rlD) (mx I.tlU I.thU)) - mD (2 * I.rlD - S) (mn I.tlD I.thD)
def d1 (I : In) : ℕ := (((S - I.thU)) + ((I.thD - S)))
def defD (I : In) : ℕ := dD (mD I.rlD (mD I.d1 I.d1)) I.denU
def hmU (I : In) : ℕ := (S - (((mD I.RlD I.rlD) + I.defD)))
def resU (I : In) : ℕ :=
  dU I.prU (2 * S) + dU (mU I.prU I.hmU) (mx 1 (2 * (I.hmU + mD (4 * aD) I.prU)))
def hiU (I : In) : ℕ := ((I.zU I.uh) - I.rlD)
def llhU (I : In) : ℕ := mU (mU c1U I.RhU) (uq (mn ((S - I.rlD)) (mU h2U I.hiU)))
def cubU (I : In) : ℕ := mn kU ((I.llhU + (uq (mU (mU gU ((S + aU))) I.resU))))
def kinU (I : In) : ℕ :=
  mn (dU I.thU a0D) (mn ((I.RhU + (dU ((S - I.RhU)) h2D)))
    (mn (mU I.thU ((I.rlD + (dU ((S - I.rlD)) a0D))))
      ((((I.RhU + (dU ((S - I.RhU)) h3D))) + (mU (mU bU I.thU) I.hiU)))))
def UU (I : In) : ℕ := uq (I.YU I.uh)

/-- The fast test. -/
def ok (I : In) : Bool :=
  Bool.and (Bool.and (Bool.and (Nat.blt 0 (I.YD I.ul)) (Nat.blt 0 (I.YD I.uh)))
      (Bool.and (Nat.blt I.rlU ((2 * S))) (Bool.and (Nat.blt I.rhU ((2 * S))) (Nat.blt 0 I.dhD))))
    (Bool.and (Bool.and (Nat.blt 0 I.denD) (Nat.ble (mU I.RlU I.RlU) S))
      (Nat.blt ((eU + (((mU I.mH I.kinU) + (mU (mU sU I.UU) I.cubU))))) S))

end In

/-! ### Soundness -/

theorem Lo.mono {n : ℕ} {x y : ℚ} (h : Lo n x) (hxy : x ≤ y) : Lo n y :=
  h.trans (mul_le_mul_of_nonneg_right hxy S_posQ.le)

theorem Hi.mono {n : ℕ} {x y : ℚ} (h : Hi n x) (hyx : y ≤ x) : Hi n y :=
  (mul_le_mul_of_nonneg_right hyx S_posQ.le).trans h

theorem Hi.le_div {n : ℕ} {x : ℚ} (h : Hi n x) : x ≤ (n : ℚ) / S := by
  rw [le_div_iff₀ S_posQ]; exact h

theorem lo_one : Lo S 1 := by unfold Lo; simp
theorem hi_one : Hi S 1 := by unfold Hi; simp
theorem lo_two : Lo (2 * S) 2 := by unfold Lo; push_cast; rw [mul_comm]
theorem hi_two : Hi (2 * S) 2 := by unfold Hi; push_cast; rw [mul_comm]

theorem lo_nat_mul {a : ℕ} {x : ℚ} (k : ℕ) (h : Lo a x) : Lo ((k * a)) (k * x) := by
  unfold Lo at *; push_cast [Nat.mul_eq]; nlinarith [show (0 : ℚ) ≤ k by positivity]

theorem hi_nat_mul {a : ℕ} {x : ℚ} (k : ℕ) (h : Hi a x) : Hi ((k * a)) (k * x) := by
  unfold Hi at *; push_cast [Nat.mul_eq]; nlinarith [show (0 : ℚ) ≤ k by positivity]

theorem sub_exact {u : ℕ} {x : ℚ} (hu : (u : ℚ) = x * S) (hx : x ≤ 1) :
    (((S - u) : ℕ) : ℚ) = (1 - x) * S := by
  have hle : u ≤ S := by
    have : (u : ℚ) ≤ S := by rw [hu]; nlinarith [S_posQ]
    exact_mod_cast this
  rw [Nat.cast_sub hle, hu]; ring

theorem usqrt_nonneg' (v : ℚ) : 0 ≤ usqrt v := by
  unfold usqrt; split_ifs <;> positivity

theorem h2q_gt : 1 < h2q := by norm_num [h2q]
theorem h3q_gt : 1 < h3q := by norm_num [h3q]
theorem a0q_pos : 0 < a0q := by norm_num [a0q]
theorem a0q_lt : a0q < 1 := by norm_num [a0q]
theorem Dq_pos : 0 < Dq := by norm_num [Dq, h2q, h3q]
theorem Cq_pos : 0 < Cq := by norm_num [Cq, Dq, h2q, h3q]
theorem Lq_pos : 0 < Lq := by norm_num [Lq, Cq, Dq, h2q, h3q]
theorem βq_nonneg : 0 ≤ βq := by norm_num [βq, h2q, h3q]
theorem aq_pos : 0 < aq := by norm_num [aq]
theorem sq_nonneg' : 0 ≤ sq := by norm_num [sq]
theorem κq_nonneg : 0 ≤ κq := by norm_num [κq]
theorem gramq_nonneg : 0 ≤ gramq := by norm_num [gramq]
theorem εq_nonneg : 0 ≤ εq := by norm_num [εq]
theorem c1q_nonneg : 0 ≤ c1q := by
  unfold c1q; exact mul_nonneg (by norm_num [h2q]) (usqrt_nonneg' _)

theorem h2mD_pos : 0 < h2mD := by decide +kernel
theorem a0D_pos : 0 < a0D := by decide +kernel
theorem h2D_pos : 0 < h2D := by decide +kernel
theorem h3D_pos : 0 < h3D := by decide +kernel

theorem lo_h2D : Lo h2D h2q := by unfold h2D; exact lo_flQ (by linarith [h2q_gt])
theorem hi_h2U : Hi h2U h2q := by unfold h2U; exact hi_ceQ (by linarith [h2q_gt])
theorem lo_h3D : Lo h3D h3q := by unfold h3D; exact lo_flQ (by linarith [h3q_gt])
theorem lo_h2mD : Lo h2mD (h2q - 1) := by unfold h2mD; exact lo_flQ (by linarith [h2q_gt])
theorem hi_h2mU : Hi h2mU (h2q - 1) := by unfold h2mU; exact hi_ceQ (by linarith [h2q_gt])
theorem lo_DD : Lo DD Dq := by unfold DD; exact lo_flQ Dq_pos.le
theorem hi_DU : Hi DU Dq := by unfold DU; exact hi_ceQ Dq_pos.le
theorem lo_CD : Lo CD Cq := by unfold CD; exact lo_flQ Cq_pos.le
theorem hi_CU : Hi CU Cq := by unfold CU; exact hi_ceQ Cq_pos.le
theorem lo_LD : Lo LD Lq := by unfold LD; exact lo_flQ Lq_pos.le
theorem hi_LU : Hi LU Lq := by unfold LU; exact hi_ceQ Lq_pos.le
theorem hi_bU : Hi bU βq := by unfold bU; exact hi_ceQ βq_nonneg
theorem lo_a0D : Lo a0D a0q := by unfold a0D; exact lo_flQ a0q_pos.le
theorem lo_aD : Lo aD aq := by unfold aD; exact lo_flQ aq_pos.le
theorem hi_aU : Hi aU aq := by unfold aU; exact hi_ceQ aq_pos.le
theorem hi_sU : Hi sU sq := by unfold sU; exact hi_ceQ sq_nonneg'
theorem hi_kU : Hi kU κq := by unfold kU; exact hi_ceQ κq_nonneg
theorem hi_gU : Hi gU gramq := by unfold gU; exact hi_ceQ gramq_nonneg
theorem hi_c1U : Hi c1U c1q := by unfold c1U; exact hi_ceQ c1q_nonneg
theorem hi_eU : Hi eU εq := by unfold eU; exact hi_ceQ εq_nonneg

/-- What the fast test needs about its inputs. -/
structure Good (e : Edge) (b : Box) (I : In) : Prop where
  xhL : Lo I.xhD e.xh
  xhH : Hi I.xhU e.xh
  yhL : Lo I.yhD e.yh
  yhH : Hi I.yhU e.yh
  mLo : Lo I.mL e.m
  mHi : Hi I.mH e.m
  wdL : Lo I.wdD e.width
  wdH : Hi I.wdU e.width
  m0 : 0 ≤ e.m
  w0 : 0 ≤ e.width
  xl0 : 0 ≤ e.xl
  yl0 : 0 ≤ e.yl
  ulE : (I.ul : ℚ) = b.ul * S
  uhE : (I.uh : ℚ) = b.uh * S
  plE : (I.pl : ℚ) = b.pl * S
  phE : (I.ph : ℚ) = b.ph * S
  vlE : (I.vl : ℚ) = b.vl * S
  vhE : (I.vh : ℚ) = b.vh * S
  ul0 : 0 ≤ b.ul
  ul1 : b.ul ≤ 1
  uh0 : 0 ≤ b.uh
  uh1 : b.uh ≤ 1
  pl0 : 0 ≤ b.pl
  pl1 : b.pl ≤ 1
  ph0 : 0 ≤ b.ph
  ph1 : b.ph ≤ 1
  vl0 : 0 ≤ b.vl
  vh0 : 0 ≤ b.vh

namespace Good

variable {e : Edge} {b : Box} {I : In} (G : Good e b I)
include G

theorem X_nonneg {x : ℚ} (hx0 : 0 ≤ x) : 0 ≤ e.X x := by
  rw [X_eq]; have := G.xl0; have := G.w0; simp only [Edge.xl] at *; nlinarith

theorem Y_nonneg {x : ℚ} (hx0 : 0 ≤ x) : 0 ≤ e.Y x := by
  rw [Y_eq]; have := G.yl0; have := G.w0; have := G.m0; simp only [Edge.yl] at *
  nlinarith [mul_nonneg G.m0 G.w0]

theorem X_lo {u : ℕ} {x : ℚ} (hu : (u : ℚ) = x * S) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Lo (I.XD u) (e.X x) := by
  have h1 : Hi ((S - u)) (1 - x) := hi_exact (sub_exact hu hx1)
  have h2 : Hi (mU I.wdU ((S - u))) (e.width * (1 - x)) := hi_mul G.w0 G.wdH h1
  have hpos : e.width * (1 - x) ≤ e.xh := by
    have := G.X_nonneg hx0; rw [X_eq] at this; linarith
  rw [X_eq]; exact lo_sub' G.xhL h2 hpos

theorem X_hi {u : ℕ} {x : ℚ} (hu : (u : ℚ) = x * S) (hx1 : x ≤ 1) : Hi (I.XU u) (e.X x) := by
  rw [X_eq]; exact hi_sub G.xhH (lo_mul G.wdL (lo_exact (sub_exact hu hx1)))

theorem Y_lo {u : ℕ} {x : ℚ} (hu : (u : ℚ) = x * S) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Lo (I.YD u) (e.Y x) := by
  have h1 : Hi ((S - u)) (1 - x) := hi_exact (sub_exact hu hx1)
  have h2 : Hi (mU (mU I.mH I.wdU) ((S - u))) (e.m * e.width * (1 - x)) :=
    hi_mul (mul_nonneg G.m0 G.w0) (hi_mul G.m0 G.mHi G.wdH) h1
  have hpos : e.m * e.width * (1 - x) ≤ e.yh := by
    have := G.Y_nonneg hx0; rw [Y_eq] at this; linarith
  rw [Y_eq]; exact lo_sub' G.yhL h2 hpos

theorem Y_hi {u : ℕ} {x : ℚ} (hu : (u : ℚ) = x * S) (hx1 : x ≤ 1) : Hi (I.YU u) (e.Y x) := by
  rw [Y_eq]; exact hi_sub G.yhH (lo_mul (lo_mul G.mLo G.wdL) (lo_exact (sub_exact hu hx1)))

theorem z_lo {u : ℕ} {x : ℚ} (hu : (u : ℚ) = x * S) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hY : 0 < I.YD u) : Lo (I.zD u) (e.z x) :=
  lo_div (G.X_lo hu hx0 hx1) (G.Y_hi hu hx1) ((G.Y_lo hu hx0 hx1).pos hY)

theorem z_hi {u : ℕ} {x : ℚ} (hu : (u : ℚ) = x * S) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hY : 0 < I.YD u) : Hi (I.zU u) (e.z x) :=
  hi_div (G.X_nonneg hx0) (G.X_hi hu hx1) (G.Y_lo hu hx0 hx1) hY

end Good

theorem lowerQ_eq (z : ℚ) : lowerQ z = max 0 (h2q * z - 1) / (h2q - 1) := by
  have hp : 0 < h2q - 1 := by linarith [h2q_gt]
  unfold lowerQ
  rcases le_total 0 (h2q * z - 1) with h | h
  · rw [max_eq_right h, max_eq_right (div_nonneg h hp.le)]
  · rw [max_eq_left h, max_eq_left (div_nonpos_of_nonpos_of_nonneg h hp.le), zero_div]

theorem lo_lower {n : ℕ} {z : ℚ} (h : Lo n z) : Lo (In.loD n) (lowerQ z) := by
  have a : Lo (mD h2D n) (h2q * z) := lo_mul lo_h2D h
  have b := lo_sub a hi_one
  have c := lo_div b hi_h2mU (by linarith [h2q_gt])
  rw [lowerQ_eq]; exact c

theorem hi_lower {n : ℕ} {z : ℚ} (h : Hi n z) : Hi (In.loU n) (lowerQ z) := by
  have a : Hi (mU h2U n) (h2q * z) := hi_mul (by linarith [h2q_gt]) hi_h2U h
  have b := hi_sub_max a lo_one
  have c := hi_div (le_max_left _ _) b lo_h2mD h2mD_pos
  rw [lowerQ_eq]; exact c

theorem lowerQ_nonneg (z : ℚ) : 0 ≤ lowerQ z := le_max_left _ _

/-! ### Exact facts used by the bounds -/

theorem max_one_max_zero (t : ℚ) : max 1 (max 0 t) = max 1 t := by
  rcases le_total 0 t with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, max_eq_left (by norm_num : (0 : ℚ) ≤ 1), max_eq_left (by linarith)]

theorem mx_lin {c a b : ℚ} (hc : 0 ≤ c) : max (1 + c * a) (1 + c * b) = 1 + c * max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith)]
  · rw [max_eq_left h, max_eq_left (by nlinarith)]

theorem mn_lin {c a b : ℚ} (hc : c ≤ 0) : max (1 + c * a) (1 + c * b) = 1 + c * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (by nlinarith)]
  · rw [min_eq_right h, max_eq_right (by nlinarith)]

theorem mx_ge (c a b : ℚ) : 1 + c * min a b ≤ max (1 + c * a) (1 + c * b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]; exact le_max_left _ _
  · rw [min_eq_right h]; exact le_max_right _ _

theorem mx_le {c a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (1 + c * a) (1 + c * b) ≤ 1 + max 0 c * max a b := by
  have h1 : c * a ≤ max 0 c * max a b :=
    (mul_le_mul_of_nonneg_right (le_max_right 0 c) ha).trans
      (mul_le_mul_of_nonneg_left (le_max_left a b) (le_max_left 0 c))
  have h2 : c * b ≤ max 0 c * max a b :=
    (mul_le_mul_of_nonneg_right (le_max_right 0 c) hb).trans
      (mul_le_mul_of_nonneg_left (le_max_right a b) (le_max_left 0 c))
  exact max_le (by linarith) (by linarith)

theorem pos_part_sum (t : ℚ) : max 0 (1 - t) + max 0 (t - 1) = |1 - t| := by
  rcases le_total t 1 with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonneg (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonpos (by linarith)]; ring

theorem lem_t2 {h R R' : ℚ} (hh : 1 < h) (hR : R ≤ R') :
    R + (1 - R) / h ≤ R' + max 0 (1 - R') / h := by
  have hp : 0 < h := by linarith
  have key : (R' - R) / h ≤ R' - R := div_le_self (sub_nonneg.2 hR) hh.le
  have e1 : R + (1 - R) / h ≤ R' + (1 - R') / h := by
    have : (1 - R) / h = (1 - R') / h + (R' - R) / h := by ring
    rw [this]; linarith
  have e2 : (1 - R') / h ≤ max 0 (1 - R') / h := div_le_div_of_nonneg_right (le_max_right _ _) hp.le
  linarith

theorem lem_t3 {a r r' : ℚ} (ha : 0 < a) (ha1 : a < 1) (hr : r' ≤ r) :
    r + (1 - r) / a ≤ r' + max 0 (1 - r') / a := by
  have e1 : r + (1 - r) / a ≤ r' + (1 - r') / a := by
    rw [add_div' _ _ _ ha.ne', add_div' _ _ _ ha.ne', div_le_div_iff_of_pos_right ha]
    nlinarith
  have e2 : (1 - r') / a ≤ max 0 (1 - r') / a := div_le_div_of_nonneg_right (le_max_right _ _) ha.le
  linarith

/-- The side conditions checked by `In.ok`. -/
structure Conds (I : In) : Prop where
  Yl : 0 < I.YD I.ul
  Yh : 0 < I.YD I.uh
  rl2 : I.rlU < (2 * S)
  rh2 : I.rhU < (2 * S)
  dh : 0 < I.dhD
  den : 0 < I.denD
  Rl1 : mU I.RlU I.RlU ≤ S

namespace Good

variable {e : Edge} {b : Box} {I : In} (G : Good e b I) (C : Conds I)
include G

theorem r_lo {u p : ℕ} {x y : ℚ} (hu : (u : ℚ) = x * S) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hp : (p : ℚ) = y * S) (hy1 : y ≤ 1) (hY : 0 < I.YD u) : Lo (I.rD u p) (e.ρ x y) := by
  unfold In.rD Edge.ρ
  exact lo_add (lo_mul (lo_exact (sub_exact hp hy1)) (lo_lower (G.z_lo hu hx0 hx1 hY)))
    (lo_mul (lo_exact hp) (G.z_lo hu hx0 hx1 hY))

theorem r_hi {u p : ℕ} {x y : ℚ} (hu : (u : ℚ) = x * S) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hp : (p : ℚ) = y * S) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hY : 0 < I.YD u) :
    Hi (I.rU u p) (e.ρ x y) := by
  unfold In.rU Edge.ρ
  have hz := G.z_hi hu hx0 hx1 hY
  have hz0 : 0 ≤ e.z x := (G.z_lo hu hx0 hx1 hY).nonneg
  exact hi_add (hi_mul (by linarith) (hi_exact (sub_exact hp hy1)) (hi_lower hz))
    (hi_mul hy0 (hi_exact hp) hz)

include C

theorem zl_lo : Lo (I.zD I.ul) (zL e b) := G.z_lo G.ulE G.ul0 G.ul1 C.Yl
theorem zl_hi : Hi (I.zU I.ul) (zL e b) := G.z_hi G.ulE G.ul0 G.ul1 C.Yl
theorem zh_lo : Lo (I.zD I.uh) (zH e b) := G.z_lo G.uhE G.uh0 G.uh1 C.Yh
theorem zh_hi : Hi (I.zU I.uh) (zH e b) := G.z_hi G.uhE G.uh0 G.uh1 C.Yh
theorem rl_lo : Lo I.rlD (rL e b) := G.r_lo G.ulE G.ul0 G.ul1 G.plE G.pl1 C.Yl
theorem rl_hi : Hi I.rlU (rL e b) := G.r_hi G.ulE G.ul0 G.ul1 G.plE G.pl0 G.pl1 C.Yl
theorem rh_lo : Lo I.rhD (rH e b) := G.r_lo G.uhE G.uh0 G.uh1 G.phE G.ph1 C.Yh
theorem rh_hi : Hi I.rhU (rH e b) := G.r_hi G.uhE G.uh0 G.uh1 G.phE G.ph0 G.ph1 C.Yh

theorem dl_lo : Lo I.dlD (dLq e b) := by
  have a : Lo ((CD + (mD LD I.rlD))) (Cq + Lq * rL e b) := lo_add lo_CD (lo_mul lo_LD (G.rl_lo C))
  have bb : Hi (mU DU (I.zU I.uh)) (Dq * zH e b) := hi_mul Dq_pos.le hi_DU (G.zh_hi C)
  have d := lo_max lo_one (lo_sub a bb)
  unfold dLq
  rw [← max_one_max_zero, show Cq - Dq * zH e b + Lq * rL e b = Cq + Lq * rL e b - Dq * zH e b by ring]
  exact d

theorem dl_hi : Hi I.dlU (dLq e b) := by
  have a : Hi ((CU + (mU LU I.rlU))) (Cq + Lq * rL e b) :=
    hi_add hi_CU (hi_mul Lq_pos.le hi_LU (G.rl_hi C))
  have bb : Lo (mD DD (I.zD I.uh)) (Dq * zH e b) := lo_mul lo_DD (G.zh_lo C)
  have d := hi_max hi_one (hi_sub a bb)
  unfold dLq
  rw [show Cq - Dq * zH e b + Lq * rL e b = Cq + Lq * rL e b - Dq * zH e b by ring]
  exact d

omit G C in
theorem dl_pos' : 0 < dLq e b := by
  unfold dLq; exact lt_of_lt_of_le one_pos (le_max_left _ _)

theorem dlD_pos : 0 < I.dlD := by
  unfold In.dlD; rw [mx_eq]; exact lt_of_lt_of_le S_pos (le_max_left _ _)

theorem dh_lo : Lo I.dhD (dHq e b) := by
  have a : Lo ((CD + (mD LD I.rhD))) (Cq + Lq * rH e b) := lo_add lo_CD (lo_mul lo_LD (G.rh_lo C))
  have bb : Hi (mU DU (I.zU I.ul)) (Dq * zL e b) := hi_mul Dq_pos.le hi_DU (G.zl_hi C)
  have c : Lo I.dhD (max 0 (Cq + Lq * rH e b - Dq * zL e b)) := lo_sub a bb
  have hc := c.pos C.dh
  have ht : 0 ≤ Cq + Lq * rH e b - Dq * zL e b := by
    by_contra hneg
    rw [max_eq_left (le_of_lt (not_le.mp hneg))] at hc
    exact lt_irrefl 0 hc
  rw [max_eq_right ht] at c
  unfold dHq
  rw [show Cq - Dq * zL e b + Lq * rH e b = Cq + Lq * rH e b - Dq * zL e b by ring]
  exact c

theorem dh_hi : Hi I.dhU (dHq e b) := by
  have := hi_sub (hi_add hi_CU (hi_mul Lq_pos.le hi_LU (G.rh_hi C))) (lo_mul lo_DD (G.zl_lo C))
  unfold dHq
  rw [show Cq - Dq * zL e b + Lq * rH e b = Cq + Lq * rH e b - Dq * zL e b by ring]
  exact this

theorem rl_lt2 : rL e b < 2 := by
  have h := G.rl_hi C
  have h2 : ((I.rlU : ℕ) : ℚ) < (((2 * S) : ℕ) : ℚ) := by exact_mod_cast C.rl2
  unfold Hi at h; push_cast at h2
  nlinarith [S_posQ]

theorem rh_lt2 : rH e b < 2 := by
  have h := G.rh_hi C
  have h2 : ((I.rhU : ℕ) : ℚ) < (((2 * S) : ℕ) : ℚ) := by exact_mod_cast C.rh2
  unfold Hi at h; push_cast at h2
  nlinarith [S_posQ]

theorem tl_lo : Lo I.tlD (tL e b) := by
  have inv1 : Lo (dD S ((((2 * S)) - I.rlD))) (1 / (2 - rL e b)) :=
    lo_div lo_one (hi_sub hi_two (G.rl_lo C)) (by linarith [G.rl_lt2 C])
  have inv2 : Lo (dD S I.dhU) (1 / dHq e b) := lo_div lo_one (G.dh_hi C) ((G.dh_lo C).pos C.dh)
  unfold In.tlD tL
  exact lo_mul (lo_exact G.vlE) (lo_min (G.zl_lo C) (lo_min inv1 inv2))

theorem tl_hi : Hi I.tlU (tL e b) := by
  have hpos2 : 0 < (((2 * S)) - I.rlU) := by have := C.rl2; omega
  have inv1 : Hi (dU S ((((2 * S)) - I.rlU))) (1 / (2 - rL e b)) :=
    hi_div zero_le_one hi_one (lo_sub' lo_two (G.rl_hi C) (G.rl_lt2 C).le) hpos2
  have inv2 : Hi (dU S I.dhD) (1 / dHq e b) := hi_div zero_le_one hi_one (G.dh_lo C) C.dh
  unfold In.tlU tL
  exact hi_mul G.vl0 (hi_exact G.vlE) (hi_min (G.zl_hi C) (hi_min inv1 inv2))

theorem th_lo : Lo I.thD (tH e b) := by
  have inv1 : Lo (dD S ((((2 * S)) - I.rhD))) (1 / (2 - rH e b)) :=
    lo_div lo_one (hi_sub hi_two (G.rh_lo C)) (by linarith [G.rh_lt2 C])
  have inv2 : Lo (dD S I.dlU) (1 / dLq e b) := lo_div lo_one (G.dl_hi C) dl_pos'
  unfold In.thD tH
  exact lo_mul (lo_exact G.vhE) (lo_min (G.zh_lo C) (lo_min inv1 inv2))

theorem th_hi : Hi I.thU (tH e b) := by
  have hpos2 : 0 < (((2 * S)) - I.rhU) := by have := C.rh2; omega
  have inv1 : Hi (dU S ((((2 * S)) - I.rhU))) (1 / (2 - rH e b)) :=
    hi_div zero_le_one hi_one (lo_sub' lo_two (G.rh_hi C) (G.rh_lt2 C).le) hpos2
  have inv2 : Hi (dU S I.dlD) (1 / dLq e b) := hi_div zero_le_one hi_one (G.dl_lo C) (G.dlD_pos C)
  unfold In.thU tH
  exact hi_mul G.vh0 (hi_exact G.vhE) (hi_min (G.zh_hi C) (hi_min inv1 inv2))

theorem RL_lo : Lo I.RlD (RL e b) := lo_mul (G.rl_lo C) (G.tl_lo C)
theorem RL_hi : Hi I.RlU (RL e b) := hi_mul (G.rl_lo C).nonneg (G.rl_hi C) (G.tl_hi C)
theorem RH_hi : Hi I.RhU (RH e b) := hi_mul (G.rh_lo C).nonneg (G.rh_hi C) (G.th_hi C)

end Good


theorem bool_rec_false {a b : ℕ} {c : Bool} (h : c = false) :
    Bool.rec (motive := fun _ => ℕ) a b c = a := by subst h; rfl

theorem bool_rec_true {a b : ℕ} {c : Bool} (h : c = true) :
    Bool.rec (motive := fun _ => ℕ) a b c = b := by subst h; rfl

theorem lo_two_mul {a : ℕ} {x : ℚ} (h : Lo a x) : Lo ((2 * a)) (2 * x) := by
  have := lo_nat_mul 2 h; simpa using this

theorem hi_two_mul {a : ℕ} {x : ℚ} (h : Hi a x) : Hi ((2 * a)) (2 * x) := by
  have := hi_nat_mul 2 h; simpa using this

theorem lo_le_S (x : ℕ) : Lo ((S - x)) 1 := by
  unfold Lo; simp only [one_mul]; exact_mod_cast Nat.sub_le S x

theorem two_S_pos : 0 < 2 * S := Nat.mul_pos (by norm_num) S_pos

theorem div_S_mul (n : ℕ) : (n : ℚ) = (n : ℚ) / S * S := by rw [div_mul_cancel₀ _ S_posQ.ne']

namespace Good

variable {e : Edge} {b : Box} {I : In} (G : Good e b I) (C : Conds I)
include G C

theorem tL_nonneg : 0 ≤ tL e b := (G.tl_lo C).nonneg
theorem tH_nonneg : 0 ≤ tH e b := (G.th_lo C).nonneg

omit G C in
theorem den_split (c a b : ℚ) :
    max (1 + c * a) (1 + c * b) = 1 + max 0 c * max a b - max 0 (-c) * min a b := by
  rcases le_total 0 c with hc | hc
  · rw [max_eq_right hc, max_eq_left (by linarith : -c ≤ 0), mx_lin hc]; ring
  · rw [max_eq_left hc, max_eq_right (by linarith : 0 ≤ -c), mn_lin hc]; ring

omit G C in
theorem denQ_eq (e : Edge) (b : Box) : denQ e b = 1 + max 0 (1 - 2 * rL e b) * max (tL e b) (tH e b)
    - max 0 (2 * rL e b - 1) * min (tL e b) (tH e b) := by
  unfold denQ; rw [den_split, neg_sub]

theorem denD_lo : Lo I.denD (denQ e b) := by
  have x : Lo (S + mD (S - 2 * I.rlU) (mx I.tlD I.thD))
      (1 + max 0 (1 - 2 * rL e b) * max (tL e b) (tH e b)) :=
    lo_add lo_one (lo_mul (lo_sub lo_one (hi_two_mul (G.rl_hi C))) (lo_max (G.tl_lo C) (G.th_lo C)))
  have y : Hi (mU (2 * I.rlU - S) (mn I.tlU I.thU)) (max 0 (2 * rL e b - 1) * min (tL e b) (tH e b)) :=
    hi_mul (le_max_left _ _) (hi_sub_max (hi_two_mul (G.rl_hi C)) lo_one) (hi_min (G.tl_hi C) (G.th_hi C))
  have h : Lo I.denD (max 0 (denQ e b)) := by rw [denQ_eq]; exact lo_sub x y
  have hpos := h.pos C.den
  have hd : 0 ≤ denQ e b := by
    by_contra hn
    rw [max_eq_left (le_of_lt (not_le.mp hn))] at hpos
    exact lt_irrefl 0 hpos
  rwa [max_eq_right hd] at h

theorem denU_hi : Hi I.denU (denQ e b) := by
  have x : Hi (S + mU (S - 2 * I.rlD) (mx I.tlU I.thU))
      (1 + max 0 (1 - 2 * rL e b) * max (tL e b) (tH e b)) :=
    hi_add hi_one (hi_mul (le_max_left _ _) (hi_sub_max hi_one (lo_two_mul (G.rl_lo C)))
      (hi_max (G.tl_hi C) (G.th_hi C)))
  have y : Lo (mD (2 * I.rlD - S) (mn I.tlD I.thD)) (max 0 (2 * rL e b - 1) * min (tL e b) (tH e b)) :=
    lo_mul (lo_sub (lo_two_mul (G.rl_lo C)) hi_one) (lo_min (G.tl_lo C) (G.th_lo C))
  rw [denQ_eq]; exact hi_sub x y

theorem den_pos : 0 < denQ e b := (G.denD_lo C).pos C.den

theorem d1_lo : Lo I.d1 |1 - tH e b| := by
  unfold In.d1
  have := lo_add (lo_sub lo_one (G.th_hi C)) (lo_sub (G.th_lo C) hi_one)
  rw [pos_part_sum] at this
  exact this

theorem defD_lo : Lo I.defD (defQ e b) := by
  have hden := G.den_pos C
  unfold defQ In.defD
  rw [if_pos hden.ne']
  have h1 : Lo (mD I.d1 I.d1) ((1 - tH e b) ^ 2) := by
    have := lo_mul (G.d1_lo C) (G.d1_lo C)
    rwa [abs_mul_abs_self, ← pow_two] at this
  exact lo_div (lo_mul (G.rl_lo C) h1) (G.denU_hi C) hden

theorem hm_hi : Hi I.hmU (harmQ e b) := by
  unfold In.hmU harmQ
  have := hi_sub_max hi_one (lo_add (lo_mul (G.RL_lo C) (G.rl_lo C)) (G.defD_lo C))
  rw [show 1 - RL e b * rL e b - defQ e b = 1 - (RL e b * rL e b + defQ e b) by ring]
  exact this

theorem prob_nonneg : 0 ≤ 1 - RL e b ^ 2 := by
  have h := hi_mul (G.RL_lo C).nonneg (G.RL_hi C) (G.RL_hi C)
  have h1 : ((mU I.RlU I.RlU : ℕ) : ℚ) ≤ S := by exact_mod_cast C.Rl1
  unfold Hi at h
  have : RL e b * RL e b * S ≤ 1 * S := by linarith
  have := le_of_mul_le_mul_right this S_posQ
  rw [pow_two]; linarith

theorem prU_hi : Hi I.prU (1 - RL e b ^ 2) := by
  unfold In.prU
  have := hi_sub hi_one (lo_mul (G.RL_lo C) (G.RL_lo C))
  rw [pow_two]; exact this

theorem res_hi : Hi I.resU (resQ e b) := by
  set M : ℚ := (I.prU : ℚ) / S with hMdef
  set W : ℚ := (I.hmU : ℚ) / S with hWdef
  have hM : (I.prU : ℚ) = M * S := div_S_mul _
  have hW : (I.hmU : ℚ) = W * S := div_S_mul _
  have hM0 : 0 ≤ M := by positivity
  have hW0 : 0 ≤ W := by positivity
  have hG := Gq_le (G.prob_nonneg C) (le_max_left _ _) (Hi.le_div (G.prU_hi C)) (Hi.le_div (G.hm_hi C))
  unfold resQ
  refine Hi.mono ?_ hG
  unfold In.resU
  apply hi_add
  · exact hi_div hM0 (hi_exact hM) lo_two two_S_pos
  · by_cases hz : M = 0 ∨ W = 0
    · rw [if_pos hz]; unfold Hi; simp
    · rw [if_neg hz]
      push_neg at hz
      have hh0 : I.hmU ≠ 0 := by
        intro h; apply hz.2; rw [hWdef, h]; simp
      have hnum : Hi (mU I.prU I.hmU) (M * W) := hi_mul hM0 (hi_exact hM) (hi_exact hW)
      have h4 : Lo (4 * aD) (4 * aq) := by have := lo_nat_mul 4 lo_aD; simpa using this
      have hden : Lo (2 * (I.hmU + mD (4 * aD) I.prU)) (2 * (W + 4 * aq * M)) := by
        have := lo_two_mul (lo_add (lo_exact hW) (lo_mul h4 (lo_exact hM)))
        rwa [mul_assoc 4 aq M] at this ⊢
      have hge : 1 ≤ 2 * (I.hmU + mD (4 * aD) I.prU) := by have := Nat.pos_of_ne_zero hh0; omega
      rw [mx_eq, max_eq_right hge]
      exact hi_div (mul_nonneg hM0 hW0) hnum hden (by omega)

theorem high_hi : Hi I.hiU (max 0 (highQ e b)) := by
  unfold In.hiU highQ; exact hi_sub_max (G.zh_hi C) (G.rl_lo C)

theorem RH_nonneg : 0 ≤ RH e b := mul_nonneg (G.rh_lo C).nonneg (G.tH_nonneg C)

theorem llh_hi : Hi I.llhU (llhQ e b) := by
  have h2 : (0 : ℚ) ≤ h2q := by linarith [h2q_gt]
  have harg : Hi (mn ((S - I.rlD)) (mU h2U I.hiU))
      (min (max 0 (1 - rL e b)) (h2q * max 0 (highQ e b))) :=
    hi_min (hi_sub_max hi_one (G.rl_lo C)) (hi_mul h2 hi_h2U (G.high_hi C))
  have hle : min (1 - rL e b) (h2q * highQ e b) ≤ min (max 0 (1 - rL e b)) (h2q * max 0 (highQ e b)) :=
    min_le_min (le_max_right _ _) (mul_le_mul_of_nonneg_left (le_max_right _ _) h2)
  have hu := Hi.mono (hi_usqrt harg) (usqrt_mono hle)
  unfold In.llhU llhQ
  exact hi_mul (mul_nonneg c1q_nonneg (G.RH_nonneg C)) (hi_mul c1q_nonneg hi_c1U (G.RH_hi C)) hu

theorem cub_hi : Hi I.cubU (cubQ e b) := by
  have ha : (0 : ℚ) ≤ 1 + aq := by linarith [aq_pos]
  unfold In.cubU cubQ
  exact hi_min hi_kU (hi_add (G.llh_hi C) (hi_usqrt (hi_mul (mul_nonneg gramq_nonneg ha)
    (hi_mul gramq_nonneg hi_gU (hi_add hi_one hi_aU)) (G.res_hi C))))

theorem kin_hi : Hi I.kinU (kinQ e b) := by
  have hth0 := G.tH_nonneg C
  set Rp : ℚ := (I.RhU : ℚ) / S with hRpdef
  have hRp : (I.RhU : ℚ) = Rp * S := div_S_mul _
  set rp : ℚ := (I.rlD : ℚ) / S with hrpdef
  have hrp : (I.rlD : ℚ) = rp * S := div_S_mul _
  have hRle : RH e b ≤ Rp := Hi.le_div (G.RH_hi C)
  have hrle : rp ≤ rL e b := by
    have h := G.rl_lo C; unfold Lo at h; rw [hrpdef, div_le_iff₀ S_posQ]; exact h
  have t1 : Hi (dU I.thU a0D) (tH e b / a0q) := hi_div hth0 (G.th_hi C) lo_a0D a0D_pos
  have t2 : Hi ((I.RhU + (dU ((S - I.RhU)) h2D))) (RH e b + (1 - RH e b) / h2q) :=
    Hi.mono (hi_add (hi_exact hRp) (hi_div (le_max_left _ _) (hi_sub_max hi_one (lo_exact hRp)) lo_h2D h2D_pos))
      (lem_t2 h2q_gt hRle)
  have hG' : Hi ((I.rlD + (dU ((S - I.rlD)) a0D))) (rp + max 0 (1 - rp) / a0q) :=
    hi_add (hi_exact hrp) (hi_div (le_max_left _ _) (hi_sub_max hi_one (lo_exact hrp)) lo_a0D a0D_pos)
  have t3 : Hi (mU I.thU ((I.rlD + (dU ((S - I.rlD)) a0D)))) (tH e b * (rL e b + (1 - rL e b) / a0q)) :=
    Hi.mono (hi_mul hth0 (G.th_hi C) hG') (mul_le_mul_of_nonneg_left (lem_t3 a0q_pos a0q_lt hrle) hth0)
  have tA : Hi ((I.RhU + (dU ((S - I.RhU)) h3D))) (Rp + max 0 (1 - Rp) / h3q) :=
    hi_add (hi_exact hRp) (hi_div (le_max_left _ _) (hi_sub_max hi_one (lo_exact hRp)) lo_h3D h3D_pos)
  have tB : Hi (mU (mU bU I.thU) I.hiU) (βq * tH e b * max 0 (highQ e b)) :=
    hi_mul (mul_nonneg βq_nonneg hth0) (hi_mul βq_nonneg hi_bU (G.th_hi C)) (G.high_hi C)
  have t4 : Hi ((((I.RhU + (dU ((S - I.RhU)) h3D))) + (mU (mU bU I.thU) I.hiU)))
      (RH e b + (1 - RH e b) / h3q + βq * tH e b * highQ e b) :=
    Hi.mono (hi_add tA tB) (add_le_add (lem_t2 h3q_gt hRle)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg βq_nonneg hth0)))
  unfold In.kinU kinQ
  exact hi_min t1 (hi_min t2 (hi_min t3 t4))

theorem U_hi : Hi I.UU (usqrt (e.Y b.uh)) := hi_usqrt (G.Y_hi G.uhE G.uh1)

/-- **Soundness of the fast test.** -/
theorem sound (hfin : (eU + (((mU I.mH I.kinU) + (mU (mU sU I.UU) I.cubU)))) < S) :
    εq < gap e b := by
  have hA : Hi (mU I.mH I.kinU) (e.m * kinQ e b) := hi_mul G.m0 G.mHi (G.kin_hi C)
  have hB : Hi (mU (mU sU I.UU) I.cubU) (sq * usqrt (e.Y b.uh) * cubQ e b) :=
    hi_mul (mul_nonneg sq_nonneg' (usqrt_nonneg' _)) (hi_mul sq_nonneg' hi_sU (G.U_hi C)) (G.cub_hi C)
  have hsum := hi_add hi_eU (hi_add hA hB)
  have hlt : (((eU + (((mU I.mH I.kinU) + (mU (mU sU I.UU) I.cubU)))) : ℕ) : ℚ) < S := by
    exact_mod_cast hfin
  unfold Hi at hsum
  have h2 : (εq + (e.m * kinQ e b + sq * usqrt (e.Y b.uh) * cubQ e b)) * S < 1 * S := by
    rw [one_mul]; exact lt_of_le_of_lt hsum hlt
  have h1 := lt_of_mul_lt_mul_right h2 S_posQ.le
  rw [gap_eq']; linarith

end Good

theorem ok_parts {I : In} (h : I.ok = true) :
    Conds I ∧ (eU + (((mU I.mH I.kinU) + (mU (mU sU I.UU) I.cubU)))) < S := by
  unfold In.ok at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3, h4, h5⟩, ⟨h6, h7⟩, h8⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩

theorem ok_sound {e : Edge} {b : Box} {I : In} (G : Good e b I) (h : I.ok = true) : εq < gap e b := by
  obtain ⟨C, hfin⟩ := ok_parts h
  exact G.sound C hfin

/-! ### The fast leaf test and the tree checker -/

/-- A box corner: nonnegative, with a denominator dividing `S` (so it is encoded exactly). -/
def corOK (q : ℚ) : Bool := Bool.and (decide (0 ≤ q.num)) (Nat.beq (S % q.den) 0)

/-- The box checks: exact corners, `u, p ≤ 1`. -/
def boxOK (b : Box) : Bool :=
  Bool.and (Bool.and (Bool.and (corOK b.ul) (corOK b.uh)) (Bool.and (corOK b.pl) (corOK b.ph)))
    (Bool.and (Bool.and (corOK b.vl) (corOK b.vh))
      (Bool.and (Bool.and (Nat.ble (flQ b.ul) S) (Nat.ble (flQ b.uh) S))
        (Bool.and (Nat.ble (flQ b.pl) S) (Nat.ble (flQ b.ph) S))))

/-- The scaled inputs of an edge and a box. -/
def mkIn (e : Edge) (b : Box) : In :=
  ⟨flQ e.xh, ceQ e.xh, flQ e.yh, ceQ e.yh, flQ e.m, ceQ e.m, flQ e.width, ceQ e.width,
   flQ b.ul, flQ b.uh, flQ b.pl, flQ b.ph, flQ b.vl, flQ b.vh⟩

/-- The fast leaf test. -/
def acceptN (e : Edge) (b : Box) : Bool := Bool.and (boxOK b) (mkIn e b).ok

/-- What the soundness proof needs from an edge. -/
structure EdgeOK (e : Edge) : Prop where
  xh0 : 0 ≤ e.xh
  yh0 : 0 ≤ e.yh
  m0 : 0 ≤ e.m
  w0 : 0 ≤ e.width
  xl0 : 0 ≤ e.xl
  yl0 : 0 ≤ e.yl

theorem cor_of {q : ℚ} (h : corOK q = true) : 0 ≤ q ∧ (flQ q : ℚ) = q * S := by
  unfold corOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hq : 0 ≤ q := Rat.num_nonneg.1 h.1
  exact ⟨hq, flQ_exact hq (Nat.eq_of_beq_eq_true h.2)⟩

theorem le_one_of {q : ℚ} (hq : (flQ q : ℚ) = q * S) (h : Nat.ble (flQ q) S = true) : q ≤ 1 := by
  have h1 : ((flQ q : ℕ) : ℚ) ≤ S := by exact_mod_cast Nat.le_of_ble_eq_true h
  rw [hq] at h1
  have : q * S ≤ 1 * S := by rw [one_mul]; exact h1
  exact le_of_mul_le_mul_right this S_posQ

theorem good_of {e : Edge} {b : Box} (he : EdgeOK e) (hb : boxOK b = true) : Good e b (mkIn e b) := by
  unfold boxOK at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨hul, huh⟩, hpl, hph⟩, ⟨hvl, hvh⟩, ⟨hul1, huh1⟩, hpl1, hph1⟩ := hb
  obtain ⟨ul0, ulE⟩ := cor_of hul
  obtain ⟨uh0, uhE⟩ := cor_of huh
  obtain ⟨pl0, plE⟩ := cor_of hpl
  obtain ⟨ph0, phE⟩ := cor_of hph
  obtain ⟨vl0, vlE⟩ := cor_of hvl
  obtain ⟨vh0, vhE⟩ := cor_of hvh
  exact { xhL := lo_flQ he.xh0, xhH := hi_ceQ he.xh0, yhL := lo_flQ he.yh0, yhH := hi_ceQ he.yh0,
          mLo := lo_flQ he.m0, mHi := hi_ceQ he.m0, wdL := lo_flQ he.w0, wdH := hi_ceQ he.w0,
          m0 := he.m0, w0 := he.w0, xl0 := he.xl0, yl0 := he.yl0,
          ulE := ulE, uhE := uhE, plE := plE, phE := phE, vlE := vlE, vhE := vhE,
          ul0 := ul0, ul1 := le_one_of ulE hul1, uh0 := uh0, uh1 := le_one_of uhE huh1,
          pl0 := pl0, pl1 := le_one_of plE hpl1, ph0 := ph0, ph1 := le_one_of phE hph1,
          vl0 := vl0, vh0 := vh0 }

/-- **The fast leaf test implies the exact one.** -/
theorem acceptN_sound {e : Edge} {b : Box} (he : EdgeOK e) (h : acceptN e b = true) :
    accept e b = true := by
  unfold acceptN at h
  rw [Bool.and_eq_true] at h
  unfold accept
  exact decide_eq_true (ok_sound (good_of he h.1) h.2)

/-- The tree-guided checker with the fast leaf test. -/
def checkTrN (e : Edge) : Tr → Box → Bool
  | .leaf, b => acceptN e b
  | .node l r, b => checkTrN e l (split b).1 && checkTrN e r (split b).2

theorem checkTrN_sound {e : Edge} (he : EdgeOK e) :
    ∀ t b, checkTrN e t b = true → checkTr e t b = true
  | .leaf, b, h => acceptN_sound he h
  | .node l r, b, h => by
    simp only [checkTrN, checkTr, Bool.and_eq_true] at h ⊢
    exact ⟨checkTrN_sound he l _ h.1, checkTrN_sound he r _ h.2⟩

/-- The six sign facts of the plan's edges, by one kernel computation. -/
def edgeChk (e : Edge) : Bool :=
  decide (0 ≤ e.xh) && decide (0 ≤ e.yh) && decide (0 ≤ e.m) && decide (0 ≤ e.width) &&
    decide (0 ≤ e.xl) && decide (0 ≤ e.yl)

theorem edgeChk_all : ∀ i < 41, edgeChk (edgeOf i) = true := by decide +kernel

theorem edgeOK_edgeOf {i : ℕ} (hi : i < 41) : EdgeOK (edgeOf i) := by
  have h := edgeChk_all i hi
  unfold edgeChk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- What a generated certificate theorem uses: the old statement, from the fast tree check. -/
theorem check_of_trN {i n : ℕ} {b : Box} (hi : i < 41) (t : Tr) (h : checkTrN (edgeOf i) t b = true)
    (hn : t.depth ≤ n) : check (edgeOf i) n b = true :=
  check_of_tr t (checkTrN_sound (edgeOK_edgeOf hi) t b h) hn

end OVNS.Cert.Fast
