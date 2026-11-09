import OddViscousNS.Quant.Joint.Slow.Chain
import OddViscousNS.Quant.Joint.Regimes

/-!
# E7-P: the moving exponent

`q = 2ⁿ`, `n = ⌈log log R⌉`.  All the constants of Moser and Riesz are functions of `n` of size
`exp(O(n²))`, which is far below the subpower `Ex`; the loss `R^{1/q}` is a subpower.  Everything of
the moving `p` of `Joint/Slow/Plan.lean` is in this file.
-/

open scoped ENNReal Topology
open MeasureTheory Set Filter

noncomputable section

namespace OVNS.Quant.Slow

/-- The constant of the `L^{2q}` level of the vorticity and of `v`, in units of `R²`. -/
def Pstar (n : ℕ) : ℝ :=
  piM 6 n * 400 + Real.exp 6 * (2 * (piM 1 n * 8) + 201 * 2 ^ n * 400)

/-- The strain constant at level `n`. -/
def Kn (n : ℕ) : ℝ := rK (2 ^ n) * Real.sqrt (Pstar n)

/-- The strain constant at the levels `n`, `n + 1`. -/
def KK (n : ℕ) : ℝ := Kn n + Kn (n + 1)

lemma two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

lemma two_pow_le_exp (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp m := by
  have h : Real.exp m = Real.exp 1 ^ m := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [h]
  exact pow_le_pow_left₀ (by norm_num) two_le_exp_one m

lemma piM_le {T : ℝ} (hT0 : 0 ≤ T) (hT : T ≤ 6) (n : ℕ) :
    piM T n ≤ Real.exp ((n : ℝ) * (24 + 3 * n)) := by
  induction n with
  | zero => simp [piM]
  | succ n ih =>
    simp only [piM]
    have h1 : Real.exp T ≤ Real.exp 6 := Real.exp_le_exp.2 hT
    have h2 : (2 : ℝ) ^ 18 ≤ Real.exp 18 := by
      simpa using two_pow_le_exp 18
    have h3 : (8 : ℝ) ^ n ≤ Real.exp (3 * n) := by
      have e : (8 : ℝ) ^ n = 2 ^ (3 * n) := by rw [pow_mul]; norm_num
      rw [e]
      simpa using two_pow_le_exp (3 * n)
    have hP := one_le_piM hT0 n
    have h4 : Real.exp T * 2 ^ 18 * 8 ^ n * piM T n ≤
        Real.exp 6 * Real.exp 18 * Real.exp (3 * n) * Real.exp ((n : ℝ) * (24 + 3 * n)) := by
      gcongr
    refine h4.trans ?_
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma rK_le (n : ℕ) : rK (2 ^ n) ≤ Real.exp (10 + 2 * n) := by
  have h1 : (4 * (4 * ((2 ^ n : ℕ) : ℝ) + 1)) ≤ 2 ^ (n + 5) := by
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    push_cast
    rw [pow_add]
    nlinarith
  have h2 : (4 * (4 * ((2 ^ n : ℕ) : ℝ) + 1)) ^ 2 ≤ (2 ^ (n + 5)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  refine h2.trans ?_
  rw [← pow_mul]
  have e : ((10 : ℝ) + 2 * n) = (((n + 5) * 2 : ℕ) : ℝ) := by push_cast; ring
  rw [e]
  exact two_pow_le_exp _

lemma Pstar_le (n : ℕ) : Pstar n ≤ Real.exp (24 + (n : ℝ) * (24 + 3 * n)) := by
  set X := Real.exp ((n : ℝ) * (24 + 3 * n)) with hX
  have hX1 : 1 ≤ X := Real.one_le_exp (by positivity)
  have h6 := piM_le (T := 6) (by norm_num) le_rfl n
  have h1 := piM_le (T := 1) (by norm_num) (by norm_num) n
  have h2 : (2 : ℝ) ^ n ≤ X := by
    refine (two_pow_le_exp n).trans (Real.exp_le_exp.2 ?_)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have e9 : (400 : ℝ) ≤ Real.exp 9 := by
    have := two_pow_le_exp 9
    norm_num at this
    linarith
  have e17 : (80416 : ℝ) ≤ Real.exp 17 := by
    have := two_pow_le_exp 17
    norm_num at this
    linarith
  have e26 : Real.exp 23 = Real.exp 6 * Real.exp 17 := by rw [← Real.exp_add]; norm_num
  have e23 : Real.exp 9 ≤ Real.exp 23 := Real.exp_le_exp.2 (by norm_num)
  have e24 : 2 * Real.exp 23 ≤ Real.exp 24 := by
    have h3 : Real.exp 24 = Real.exp 1 * Real.exp 23 := by rw [← Real.exp_add]; norm_num
    rw [h3]
    exact mul_le_mul_of_nonneg_right two_le_exp_one (Real.exp_pos _).le
  have h7 : Pstar n ≤ X * 400 + Real.exp 6 * (2 * (X * 8) + 201 * X * 400) := by
    unfold Pstar
    gcongr
  have h8 : X * 400 + Real.exp 6 * (2 * (X * 8) + 201 * X * 400) =
      (400 + Real.exp 6 * 80416) * X := by ring
  have h9 : 400 + Real.exp 6 * 80416 ≤ 2 * Real.exp 23 := by
    have : Real.exp 6 * 80416 ≤ Real.exp 6 * Real.exp 17 :=
      mul_le_mul_of_nonneg_left e17 (Real.exp_pos _).le
    linarith
  rw [Real.exp_add, ← hX]
  calc Pstar n ≤ (400 + Real.exp 6 * 80416) * X := h7.trans_eq h8
    _ ≤ Real.exp 24 * X := mul_le_mul_of_nonneg_right (h9.trans e24) (by linarith)

lemma one_le_Pstar (n : ℕ) : 1 ≤ Pstar n := by
  have h6 := one_le_piM (T := 6) (by norm_num) n
  have h1 := one_le_piM (T := 1) (by norm_num) n
  have h2 : 0 ≤ Real.exp 6 * (2 * (piM 1 n * 8) + 201 * 2 ^ n * 400) := by positivity
  unfold Pstar
  nlinarith

lemma one_le_Kn (n : ℕ) : 1 ≤ Kn n := by
  have h1 := one_le_rK (2 ^ n)
  have h2 : 1 ≤ Real.sqrt (Pstar n) := Real.one_le_sqrt.2 (one_le_Pstar n)
  unfold Kn
  nlinarith

lemma one_le_KK (n : ℕ) : 1 ≤ KK n := by
  have h1 := one_le_Kn n
  have h2 := one_le_Kn (n + 1)
  unfold KK
  linarith

lemma Kn_le (n : ℕ) : Kn n ≤ Real.exp (22 + 2 * n + (n : ℝ) * (12 + 2 * n)) := by
  have h1 := rK_le n
  have h2 : Real.sqrt (Pstar n) ≤ Real.exp ((24 + (n : ℝ) * (24 + 3 * n)) / 2) := by
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt (Pstar_le n)
  have h3 : Kn n ≤ Real.exp (10 + 2 * n) * Real.exp ((24 + (n : ℝ) * (24 + 3 * n)) / 2) := by
    unfold Kn
    exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.exp_pos _).le
  refine h3.trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]

lemma KK_le (n : ℕ) : KK n ≤ Real.exp (40 * ((n : ℝ) + 2) ^ 2) := by
  have h1 := Kn_le n
  have h2 := Kn_le (n + 1)
  have hn := Nat.cast_nonneg (α := ℝ) n
  set g : ℝ := 38 + 18 * n + 2 * n ^ 2 with hg
  have h3 : Real.exp (22 + 2 * n + (n : ℝ) * (12 + 2 * n)) ≤ Real.exp g :=
    Real.exp_le_exp.2 (by simp only [hg]; nlinarith)
  have h4 : Real.exp (22 + 2 * ((n + 1 : ℕ) : ℝ) +
      ((n + 1 : ℕ) : ℝ) * (12 + 2 * ((n + 1 : ℕ) : ℝ))) ≤ Real.exp g :=
    Real.exp_le_exp.2 (by simp only [hg]; push_cast; nlinarith)
  have h5 : 2 * Real.exp g ≤ Real.exp (40 * ((n : ℝ) + 2) ^ 2) := by
    have h6 : Real.exp (1 + g) = Real.exp 1 * Real.exp g := Real.exp_add _ _
    have h7 : Real.exp (1 + g) ≤ Real.exp (40 * ((n : ℝ) + 2) ^ 2) :=
      Real.exp_le_exp.2 (by simp only [hg]; nlinarith)
    have h8 := mul_le_mul_of_nonneg_right two_le_exp_one (Real.exp_pos g).le
    linarith
  unfold KK
  linarith

/-! ### The moving level -/

/-- The moving level: `q = 2^{nR R}`, `nR R = ⌈log log R⌉`. -/
def nR (R : ℝ) : ℕ := ⌈Real.log (Real.log R)⌉₊

/-- The size of the explicit box of the sup bound. -/
def cN : ℝ := 10 ^ 8 * (1 + errK)

/-- The facts on the moving level, for large `R`. -/
structure LargeR (R : ℝ) : Prop where
  loglog : 16000 ≤ Real.log (Real.log R)
  kk : KK (nR R) ≤ Ex 1 R
  kkR : KK (nR R) * R ≤ Ex 4 R ^ (2 ^ nR R - 1)
  pow6 : R ^ 6 ≤ Ex 6 R ^ (2 ^ nR R)
  two : (2 : ℝ) ^ nR R ≤ R
  cn : cN * Ex 6 R ^ 6 ≤ R
  lg : 1 + Real.log (⌈R ^ 2⌉₊ : ℝ) ≤ Ex 6 R ^ 2

lemma Ex_pow (c R : ℝ) (m : ℕ) :
    Ex c R ^ m = Real.exp (m * (c * Real.log R / Real.log (Real.log R))) := by
  rw [Ex, Real.exp_nat_mul]

/-- The scales `L = log R`, `ℓ = log L`, `n = ⌈ℓ⌉` for large `R`. -/
private structure Scales (R L ℓ : ℝ) (n : ℕ) : Prop where
  hℓ : 16000 ≤ ℓ
  hR1 : 1 < R
  hL0 : 0 < L
  hLe : L = Real.exp ℓ
  hRe : R = Real.exp L
  hL3 : 640 * ℓ ^ 3 ≤ L
  hn1 : ℓ ≤ n
  hn2 : (n : ℝ) < ℓ + 1
  hEx : ∀ (c : ℝ) (m : ℕ), Ex c R ^ m = Real.exp (m * (c * L / ℓ))

private lemma scales {R : ℝ} (h1 : Real.exp (Real.exp 16000) ≤ R) :
    Scales R (Real.log R) (Real.log (Real.log R)) (nR R) := by
  have hℓ : 16000 ≤ Real.log (Real.log R) := le_loglog h1
  have hR1 : 1 < R := by
    have : 1 < Real.exp (Real.exp 16000) := Real.one_lt_exp_iff.2 (Real.exp_pos _)
    linarith
  have hR0 : 0 < R := by linarith
  have hL0 : 0 < Real.log R := Real.log_pos hR1
  have hLe : Real.log R = Real.exp (Real.log (Real.log R)) := (Real.exp_log hL0).symm
  have hℓ0 : 0 < Real.log (Real.log R) := by linarith
  have hL3 : 640 * Real.log (Real.log R) ^ 3 ≤ Real.log R := by
    have hL4 : Real.log (Real.log R) ^ 4 / 24 ≤ Real.log R := by
      conv_rhs => rw [hLe]
      have := Real.pow_div_factorial_le_exp (Real.log (Real.log R)) hℓ0.le 4
      simpa [Nat.factorial] using this
    have h3 : 0 < Real.log (Real.log R) ^ 3 := by positivity
    have h4 : Real.log (Real.log R) ^ 4 =
      Real.log (Real.log R) * Real.log (Real.log R) ^ 3 := by ring
    rw [h4] at hL4
    nlinarith
  exact ⟨hℓ, hR1, hL0, hLe, (Real.exp_log hR0).symm, hL3, Nat.le_ceil _,
    Nat.ceil_lt_add_one hℓ0.le, fun c m => Ex_pow c R m⟩

section Scales

variable {R L ℓ : ℝ} {n : ℕ}

private lemma Scales.hℓ0 (h : Scales R L ℓ n) : 0 < ℓ := by linarith [h.hℓ]

private lemma Scales.hR0 (h : Scales R L ℓ n) : 0 < R := by linarith [h.hR1]

private lemma Scales.kk (h : Scales R L ℓ n) : KK n ≤ Real.exp (L / ℓ) := by
  have hℓ := h.hℓ
  have hn2 := h.hn2
  have hℓ0 := h.hℓ0
  have hdiv : 640 * ℓ ^ 2 ≤ L / ℓ := by
    rw [le_div_iff₀ hℓ0]
    calc _ = 640 * ℓ ^ 3 := by ring
      _ ≤ L := h.hL3
  refine (KK_le n).trans (Real.exp_le_exp.2 ?_)
  have h3 : (n : ℝ) + 2 ≤ 4 * ℓ := by linarith
  have h4 : ((n : ℝ) + 2) ^ 2 ≤ (4 * ℓ) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
  nlinarith

private lemma Scales.ex_one (h : Scales R L ℓ n) : Ex 1 R = Real.exp (L / ℓ) := by
  have h1 := h.hEx 1 1
  simpa using h1

private lemma Scales.kkR (h : Scales R L ℓ n) : KK n * R ≤ Ex 4 R ^ (2 ^ n - 1) := by
  have hL0 := h.hL0
  have hℓ0 := h.hℓ0
  have hn3 : n < 2 ^ n := Nat.lt_two_pow_self
  have h3 : KK n * R ≤ Real.exp (L / ℓ) * Real.exp L := by
    rw [← h.hRe]
    exact mul_le_mul_of_nonneg_right h.kk h.hR0.le
  rw [← Real.exp_add] at h3
  refine h3.trans ?_
  rw [h.hEx]
  refine Real.exp_le_exp.2 ?_
  have h4 : ℓ ≤ ((2 ^ n - 1 : ℕ) : ℝ) := by
    have h5 : n ≤ 2 ^ n - 1 := by omega
    have h6 : (n : ℝ) ≤ ((2 ^ n - 1 : ℕ) : ℝ) := by exact_mod_cast h5
    linarith [h.hn1]
  have h5 : 4 * L = ℓ * (4 * L / ℓ) := by field_simp
  have h6 : ℓ * (4 * L / ℓ) ≤ ((2 ^ n - 1 : ℕ) : ℝ) * (4 * L / ℓ) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  have hll : L / ℓ ≤ L := div_le_self hL0.le (by linarith [h.hℓ])
  linarith

private lemma Scales.pow6 (h : Scales R L ℓ n) : R ^ 6 ≤ Ex 6 R ^ (2 ^ n) := by
  have hL0 := h.hL0
  have hℓ0 := h.hℓ0
  have hn3 : n < 2 ^ n := Nat.lt_two_pow_self
  have hn4 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast hn3.le
  have h3 : R ^ 6 = Real.exp (6 * L) := by
    conv_lhs => rw [h.hRe]
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h3, h.hEx]
  refine Real.exp_le_exp.2 ?_
  have h4 : ℓ ≤ ((2 ^ n : ℕ) : ℝ) := by
    push_cast
    linarith [h.hn1]
  have h5 : 6 * L = ℓ * (6 * L / ℓ) := by field_simp
  have h6 : ℓ * (6 * L / ℓ) ≤ ((2 ^ n : ℕ) : ℝ) * (6 * L / ℓ) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  linarith

private lemma Scales.one_le (h : Scales R L ℓ n) : 8 ≤ L := by
  have : (16000 : ℝ) ^ 3 ≤ ℓ ^ 3 := pow_le_pow_left₀ (by norm_num) h.hℓ 3
  nlinarith [h.hL3]

private lemma Scales.two (h : Scales R L ℓ n) : (2 : ℝ) ^ n ≤ R := by
  have hL0 := h.hL0
  have h3 : (2 : ℝ) ^ n ≤ Real.exp n := two_pow_le_exp n
  have h4 : Real.exp n ≤ Real.exp (ℓ + 1) := Real.exp_le_exp.2 h.hn2.le
  have h5 : Real.exp (ℓ + 1) = L * Real.exp 1 := by rw [Real.exp_add, ← h.hLe]
  have h6 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h7 := Real.quadratic_le_exp_of_nonneg hL0.le
  rw [← h.hRe] at h7
  have hL8 := h.one_le
  nlinarith

private lemma Scales.cn (hs : Scales R (Real.log R) (Real.log (Real.log R)) n)
    (h2 : cN ^ 2 ≤ R) : cN * Ex 6 R ^ 6 ≤ R := by
  have hR0 := hs.hR0
  have hℓ := hs.hℓ
  have h3 : Ex 6 R ^ 6 = Ex 36 R := by
    rw [Ex_pow]
    simp only [Ex]
    congr 1
    push_cast
    ring
  have h4 : Ex 36 R ≤ R ^ ((1 : ℝ) / 2) := Ex_le_rpow hs.hR1 hs.hℓ0 (by linarith)
  rw [h3]
  have h5 : cN ≤ R ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.le_sqrt_of_sq_le h2
  have h6 : R ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) = R := by
    rw [← Real.rpow_add hR0]
    norm_num
  have h7 : 0 ≤ cN := by
    have := errK_nonneg
    unfold cN
    positivity
  calc cN * Ex 36 R ≤ R ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) :=
        mul_le_mul h5 h4 (Ex_pos _ _).le (Real.rpow_nonneg hR0.le _)
    _ = R := h6

private lemma Scales.log_ceil (hs : Scales R (Real.log R) ℓ n) (hR36 : 2 ≤ R) :
    Real.log (⌈R ^ 2⌉₊ : ℝ) ≤ 3 * Real.log R := by
  have hR0 := hs.hR0
  set N := ⌈R ^ 2⌉₊ with hN
  have hN1 : (N : ℝ) < R ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hN2 : R ^ 2 ≤ N := Nat.le_ceil _
  have hN0 : (0 : ℝ) < N := by
    have : 0 < R ^ 2 := by positivity
    linarith
  have hN3 : (N : ℝ) ≤ R ^ 3 := by nlinarith [sq_nonneg R]
  have h3 := Real.log_le_log hN0 hN3
  have e : Real.log (R ^ 3) = 3 * Real.log R := by
    rw [Real.log_pow]
    norm_num
  rw [e] at h3
  exact h3

private lemma Scales.lg (hs : Scales R (Real.log R) ℓ n)
    (h1 : Real.exp (Real.exp 16000) ≤ R) : 1 + Real.log (⌈R ^ 2⌉₊ : ℝ) ≤ Ex 6 R ^ 2 := by
  have hℓ := hs.hℓ
  have hℓ0 := hs.hℓ0
  have hL0 := hs.hL0
  have hL3 := hs.hL3
  have hR36 : 2 ≤ R := by
    have h3 : (1 : ℝ) + 16000 ≤ Real.exp 16000 := by
      have := Real.add_one_le_exp (16000 : ℝ)
      linarith
    have h4 : (1 : ℝ) + Real.exp 16000 ≤ Real.exp (Real.exp 16000) := by
      have := Real.add_one_le_exp (Real.exp 16000)
      linarith
    linarith
  have hlog := hs.log_ceil hR36
  have hL1 := hs.one_le
  rw [hs.hEx]
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have h5 : 4 * Real.log R ≤ Real.exp 2 * Real.exp ℓ := by
    rw [← hs.hLe]
    exact mul_le_mul_of_nonneg_right h4 hL0.le
  rw [← Real.exp_add] at h5
  have h6 : Real.exp (2 + ℓ) ≤ Real.exp (((2 : ℕ) : ℝ) * (6 * Real.log R / ℓ)) := by
    refine Real.exp_le_exp.2 ?_
    have h7 : 2 + ℓ ≤ 12 * Real.log R / ℓ := by
      rw [le_div_iff₀ hℓ0]
      have h8 : ℓ ^ 2 ≤ ℓ ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have h9 : 0 ≤ ℓ ^ 2 := by positivity
      nlinarith
    have e : ((2 : ℕ) : ℝ) * (6 * Real.log R / ℓ) = 12 * Real.log R / ℓ := by
      push_cast
      ring
    rw [e]
    exact h7
  linarith

end Scales

theorem largeR {R : ℝ} (h1 : Real.exp (Real.exp 16000) ≤ R) (h2 : cN ^ 2 ≤ R) : LargeR R := by
  have hs := scales h1
  exact ⟨hs.hℓ, hs.kk.trans_eq hs.ex_one.symm, hs.kkR, hs.pow6, hs.two, hs.cn h2, hs.lg h1⟩

end OVNS.Quant.Slow
