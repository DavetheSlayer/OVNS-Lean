import OddViscousNS.Quant.Energy.Near.Count
import OddViscousNS.Quant.Joint.Arith

/-!
# J1, part 1: the near count with the divisor bound as an explicit parameter

The fixed-`δ` chain of `Near/Count.lean` hides its constants behind `∃ C` (`divisor_bound`).  The
joint theorem needs them as explicit functions, because the subpower `Ex c q` of
`JointProfiles` comes from taking `δ ≈ 1/log log q`.

* `divisor_bound_explicit`: `τ(n) ≤ K(δ)^{N(δ)} n^δ` with `K(δ) = 1 + 1/(2^δ − 1)` and
  `N(δ) = ⌈2^{1/δ}⌉` (the proof of `divisor_bound`, with `K^N` kept visible).
* `tau_le_Ex`: **`τ(n) ≤ Ex cTau Q` for `1 ≤ n ≤ Q`, `log Q ≥ 3`**, `cTau = 2 log 2 + 16/log²2`
  (`δ = 2 log 2/log log Q`; the crude count of the small primes suffices, no Chebyshev).  Stated
  at the uniform level `Q`, so no monotonicity of `log n/log log n` is needed.
* The chain with a real parameter `τm`, a bound for `τ(n)`, `1 ≤ n ≤ Nm`:
  `card_circle_explicit` (`r₂(n) ≤ (8 + 12 log Nm) τm³`; here `sol_card_bound` already has the
  divisor function displayed), `card_fibre_explicit` (`#fibre ≤ fibB τm Nm`),
  `near_count_explicit` (`#countSet ≤ 7 τm³ (fibB τm Nm) (K/|k₃|) T`).

The proofs are those of `Near/Count.lean`; the private lemmas used there are restated here.
-/

noncomputable section

namespace OVNS.Quant.NearJ

open Finset

/-! ### The explicit divisor bound -/

/-- Bernoulli. -/
private lemma bernoulli_nat (x : ℝ) (hx : 1 ≤ x) (a : ℕ) :
    1 + (a : ℝ) * (x - 1) ≤ x ^ a := by
  have := one_add_mul_le_pow (a := x - 1) (by linarith) a
  simpa using this

/-- The base of the explicit constant. -/
def tauK (δ : ℝ) : ℝ := 1 + 1 / ((2 : ℝ) ^ δ - 1)

/-- The exponent of the explicit constant: the primes below `2^{1/δ}` are the bad ones. -/
def tauN (δ : ℝ) : ℕ := ⌈(2 : ℝ) ^ (1 / δ)⌉₊

/-- `divisor_bound` with the constant displayed: `τ(n) ≤ K(δ)^{N(δ)} n^δ`. -/
theorem divisor_bound_explicit {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card : ℝ) ≤ tauK δ ^ tauN δ * (n : ℝ) ^ δ := by
  set q : ℝ := (2 : ℝ) ^ δ with hq
  have hq1 : 1 < q := Real.one_lt_rpow (by norm_num) hδ
  set K : ℝ := tauK δ with hK
  have hK' : K = 1 + 1 / (q - 1) := rfl
  have hK1 : 1 ≤ K := by
    have : 0 < 1 / (q - 1) := by apply div_pos one_pos; linarith
    rw [hK']; linarith
  set N : ℕ := tauN δ with hNdef
  have hN : ∀ p : ℕ, N ≤ p → (2 : ℝ) ≤ (p : ℝ) ^ δ := by
    intro p hp
    have h1 : (2 : ℝ) ^ (1 / δ) ≤ p :=
      (Nat.le_ceil _).trans (by exact_mod_cast hp)
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / δ)) ^ δ := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one]
      _ ≤ (p : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) h1 hδ.le
  let c : ℕ → ℝ := fun p ↦ if p < N then K else 1
  have hloc : ∀ p : ℕ, p.Prime → ∀ a : ℕ,
      ((a : ℝ) + 1) ≤ c p * ((p : ℝ) ^ δ) ^ a := by
    intro p hp a
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpq : q ≤ (p : ℝ) ^ δ := Real.rpow_le_rpow (by norm_num) hp2 hδ.le
    by_cases h : p < N
    · have hcp : c p = K := by simp [c, h]
      rw [hcp]
      have hb := bernoulli_nat ((p : ℝ) ^ δ) (by linarith) a
      have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have hq0 : 0 < q - 1 := by linarith
      have hmul : (a : ℝ) * (q - 1) ≤ (a : ℝ) * ((p : ℝ) ^ δ - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) ha
      have : (a : ℝ) + 1 ≤ K * (1 + a * (q - 1)) := by
        rw [hK']
        have e : (1 + 1 / (q - 1)) * (1 + a * (q - 1)) =
            1 + 1 / (q - 1) + a * (q - 1) + a := by
          field_simp; ring
        rw [e]
        have : 0 < 1 / (q - 1) := by apply div_pos one_pos; linarith
        nlinarith
      calc (a : ℝ) + 1 ≤ K * (1 + a * (q - 1)) := this
        _ ≤ K * ((p : ℝ) ^ δ) ^ a := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith
    · have hcp : c p = 1 := by simp [c, h]
      rw [hcp, one_mul]
      have h2 := hN p (by omega)
      have hb := bernoulli_nat ((p : ℝ) ^ δ) (by linarith) a
      have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have : (a : ℝ) ≤ a * ((p : ℝ) ^ δ - 1) := by nlinarith
      linarith
  have hn0 : n ≠ 0 := by omega
  have hnδ : (n : ℝ) ^ δ =
      ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) := by
    have hnp := Nat.prod_primeFactors_pow_factorization hn0
    have hcast : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by
      have := congrArg (Nat.cast : ℕ → ℝ) hnp
      push_cast at this
      exact this
    rw [hcast, ← Real.finsetProd_rpow _ _ (fun p _ ↦ by positivity)]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity), mul_comm]
  have hc : ∏ p ∈ n.primeFactors, c p ≤ K ^ N := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    refine pow_le_pow_right₀ hK1 ?_
    calc #{p ∈ n.primeFactors | p < N} ≤ #(Finset.range N) := by
          refine Finset.card_le_card fun p hp ↦ ?_
          simp only [Finset.mem_filter] at hp
          exact Finset.mem_range.2 hp.2
      _ = N := Finset.card_range N
  rw [Nat.card_divisors hn0, Nat.cast_prod, hnδ]
  calc ∏ p ∈ n.primeFactors, (((n.factorization p + 1 : ℕ)) : ℝ)
      ≤ ∏ p ∈ n.primeFactors, (c p * ((p : ℝ) ^ δ) ^ (n.factorization p)) := by
        refine Finset.prod_le_prod₀ (fun p _ ↦ by positivity) (fun p hp ↦ ?_)
        push_cast
        exact hloc p (Nat.prime_of_mem_primeFactors hp) _
    _ = (∏ p ∈ n.primeFactors, c p) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) :=
        Finset.prod_mul_distrib
    _ ≤ K ^ N * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) :=
        mul_le_mul_of_nonneg_right hc (Finset.prod_nonneg fun p _ ↦ by positivity)

/-- The exponent of the divisor subpower. -/
def cTau : ℝ := 2 * Real.log 2 + 16 / Real.log 2 ^ 2

/-- **The subpower divisor bound**, uniformly up to `Q`: `τ(n) ≤ exp(cTau log Q/log log Q)` for
`1 ≤ n ≤ Q`, `log Q ≥ 3` (`δ = 2 log 2/log log Q`, so that `2^{1/δ} = √(log Q)`). -/
theorem tau_le_Ex {Q : ℝ} (hQ : 3 ≤ Real.log Q) {n : ℕ} (hn : 1 ≤ n) (hnQ : (n : ℝ) ≤ Q) :
    (n.divisors.card : ℝ) ≤ Ex cTau Q := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ0 : 0 < Q := by linarith
  set L := Real.log Q with hL
  have hL0 : 0 < L := by linarith
  set h := Real.log L with hh
  have hh0 : 0 < h := Real.log_pos (by linarith)
  set δ : ℝ := 2 * Real.log 2 / h with hδ
  have hδ0 : 0 < δ := by positivity
  -- 2^(1/δ) = √L
  have hexpL : Real.exp h = L := Real.exp_log hL0
  set s := Real.exp (h / 2) with hs
  have hs0 : 0 < s := Real.exp_pos _
  have hss : s * s = L := by
    rw [hs, ← Real.exp_add, ← hexpL]; congr 1; ring
  have h2s : (2 : ℝ) ^ (1 / δ) = s := by
    rw [Real.rpow_def_of_pos (by norm_num), hs]
    congr 1
    rw [hδ]; field_simp
  -- N ≤ s + 1
  have hN : (tauN δ : ℝ) ≤ s + 1 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (2 : ℝ) ^ (1 / δ) by positivity)
    rw [tauN]
    rw [h2s] at this ⊢
    exact this.le
  -- K ≤ exp(h/(2 log²2))
  have hq : δ * Real.log 2 + 1 ≤ (2 : ℝ) ^ δ := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm (Real.log 2) δ]
    exact Real.add_one_le_exp _
  have hq0 : 0 < (2 : ℝ) ^ δ - 1 := by
    have : 0 < δ * Real.log 2 := by positivity
    linarith
  set x : ℝ := h / (2 * Real.log 2 ^ 2) with hx
  have hx0 : 0 < x := by positivity
  have hK : tauK δ ≤ Real.exp x := by
    have h1 : 1 / ((2 : ℝ) ^ δ - 1) ≤ x := by
      rw [div_le_iff₀ hq0]
      have e : x * (δ * Real.log 2) = 1 := by
        rw [hx, hδ]; field_simp
      have : x * (δ * Real.log 2) ≤ x * ((2 : ℝ) ^ δ - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hx0.le
      linarith
    have := Real.add_one_le_exp x
    rw [tauK]; linarith
  have hK0 : 0 ≤ tauK δ := by
    rw [tauK]; have : 0 ≤ 1 / ((2 : ℝ) ^ δ - 1) := by positivity
    linarith
  have hKN : tauK δ ^ tauN δ ≤ Real.exp ((s + 1) * x) := by
    calc tauK δ ^ tauN δ ≤ Real.exp x ^ tauN δ := pow_le_pow_left₀ hK0 hK _
      _ = Real.exp ((tauN δ : ℝ) * x) := (Real.exp_nat_mul x _).symm
      _ ≤ Real.exp ((s + 1) * x) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hN hx0.le)
  have hnδ : (n : ℝ) ^ δ ≤ Real.exp (δ * L) := by
    calc (n : ℝ) ^ δ ≤ Q ^ δ := Real.rpow_le_rpow (by positivity) hnQ hδ0.le
      _ = Real.exp (δ * L) := by rw [Real.rpow_def_of_pos hQ0, mul_comm]
  -- log L ≤ 4 L^{1/4}, so h² ≤ 16 √L = 16 s
  have hlog : h ≤ 4 * Real.sqrt s := by
    have h1 : h = 4 * Real.log (Real.sqrt s) := by
      have e : L = (Real.sqrt s) ^ 4 := by
        rw [← hss]
        have := Real.sq_sqrt hs0.le
        calc s * s = (Real.sqrt s ^ 2) * (Real.sqrt s ^ 2) := by rw [this]
          _ = _ := by ring
      rw [hh, e, Real.log_pow]; norm_num
    have h2 : Real.log (Real.sqrt s) ≤ Real.sqrt s - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hs0)
    rw [h1]; nlinarith [Real.sqrt_nonneg s]
  have hh2 : h ^ 2 ≤ 16 * s := by
    have := pow_le_pow_left₀ hh0.le hlog 2
    have e : (4 * Real.sqrt s) ^ 2 = 16 * s := by
      rw [mul_pow, Real.sq_sqrt hs0.le]; norm_num
    linarith
  have hfinal : (s + 1) * x + δ * L ≤ cTau * L / h := by
    have e : cTau * L / h = δ * L + 16 / Real.log 2 ^ 2 * L / h := by
      rw [hδ, cTau]; field_simp
    rw [e]
    have h3 : (s + 1) * x ≤ 16 / Real.log 2 ^ 2 * L / h := by
      rw [hx, ← hss, le_div_iff₀ hh0]
      have hl : 0 < Real.log 2 ^ 2 := by positivity
      have e2 : (s + 1) * (h / (2 * Real.log 2 ^ 2)) * h =
          (s + 1) * h ^ 2 / (2 * Real.log 2 ^ 2) := by ring
      rw [e2, div_le_iff₀ (by positivity)]
      have e3 : 16 / Real.log 2 ^ 2 * (s * s) * (2 * Real.log 2 ^ 2) = 32 * (s * s) := by
        field_simp; ring
      rw [e3]
      have hs1 : 1 ≤ s := by
        have : (0 : ℝ) ≤ h / 2 := by positivity
        exact Real.one_le_exp this
      nlinarith [mul_le_mul_of_nonneg_left hh2 (by positivity : (0 : ℝ) ≤ s + 1)]
    linarith
  calc (n.divisors.card : ℝ) ≤ tauK δ ^ tauN δ * (n : ℝ) ^ δ := divisor_bound_explicit hδ0 n hn
    _ ≤ Real.exp ((s + 1) * x) * Real.exp (δ * L) :=
        mul_le_mul hKN hnδ (by positivity) (by positivity)
    _ = Real.exp ((s + 1) * x + δ * L) := (Real.exp_add _ _).symm
    _ ≤ Ex cTau Q := Real.exp_le_exp.2 hfinal

/-! ### Lattice points on a circle -/

/-- **`r₂` with explicit constant**: `r₂(n) ≤ (8 + 12 log Nm) τm³` for `1 ≤ n ≤ Nm`, from
`sol_card_bound` at `a = −1`, which already displays `τ(n)³` and `Nat.log 2 (2n²)`. -/
theorem card_circle_explicit {τm Nm : ℝ}
    (hτ : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ Nm → (n.divisors.card : ℝ) ≤ τm)
    {n : ℕ} (hn : 1 ≤ n) (hnm : (n : ℝ) ≤ Nm) :
    ((solSet (-1) n n).card : ℝ) ≤ (8 + 12 * Real.log Nm) * τm ^ 3 := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨d, hd, hcount⟩ := sol_card_bound (a := -1) (M := (n : ℤ)) (N := n) (by norm_num) hn0
  have hd1 : d.natAbs ≤ 1 := by simpa using hd
  set X := (1 + d.natAbs) * (n * (-1 : ℤ).natAbs) ^ 2 with hX
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNm1 : 1 ≤ Nm := hn1.trans hnm
  have hlogNm : 0 ≤ Real.log Nm := Real.log_nonneg hNm1
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hl20 : 0 < Real.log 2 := by linarith
  have hX1 : (1 : ℝ) ≤ X := by
    have hpos : 0 < n * (-1 : ℤ).natAbs := by simpa using (show 0 < n by omega)
    have : 1 ≤ X := by
      rw [hX]
      exact Nat.mul_pos (by omega) (pow_pos hpos 2)
    exact_mod_cast this
  have hXle : (X : ℝ) ≤ 2 * Nm ^ 2 := by
    rw [hX]
    simp only [Int.natAbs_neg, Int.natAbs_one, mul_one]
    push_cast
    have hd' : ((d.natAbs : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hd1
    have h0 : (0 : ℝ) ≤ n := by positivity
    have h1 : (1 + ((d.natAbs : ℕ) : ℝ)) * (n : ℝ) ^ 2 ≤ 2 * Nm ^ 2 := by
      gcongr
      linarith
    exact h1
  have hlogX : Real.log X ≤ Real.log 2 + 2 * Real.log Nm := by
    calc Real.log X ≤ Real.log (2 * Nm ^ 2) := Real.log_le_log (by linarith) hXle
      _ = Real.log 2 + 2 * Real.log Nm := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring
  have hlog : (Nat.log 2 X : ℝ) ≤ 1 + 3 * Real.log Nm := by
    have h1 := Real.natLog_le_logb X 2
    have h2 : Real.logb ((2 : ℕ) : ℝ) X ≤ 1 + 3 * Real.log Nm := by
      rw [Real.logb, div_le_iff₀ (by exact_mod_cast hl20)]
      push_cast
      nlinarith
    linarith
  have htau : ((n : ℤ).natAbs.divisors.card : ℝ) ≤ τm := by
    rw [Int.natAbs_natCast]
    exact hτ n hn hnm
  have htau0 : (0 : ℝ) ≤ ((n : ℤ).natAbs.divisors.card : ℝ) := Nat.cast_nonneg _
  calc ((solSet (-1) n n).card : ℝ)
      ≤ (((4 * Nat.log 2 X + 4) * (n : ℤ).natAbs.divisors.card ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast hcount
    _ = (4 * (Nat.log 2 X : ℝ) + 4) * ((n : ℤ).natAbs.divisors.card : ℝ) ^ 3 := by
        push_cast
        ring
    _ ≤ (8 + 12 * Real.log Nm) * τm ^ 3 := by
        have h3 := pow_le_pow_left₀ htau0 htau 3
        have h4 : 4 * (Nat.log 2 X : ℝ) + 4 ≤ 8 + 12 * Real.log Nm := by linarith
        exact mul_le_mul h4 h3 (by positivity) (by positivity)

/-! ### The fibres of `(A, B)` -/

/-- Off-axis outputs: over a fixed vertical component `u`, the fibre legs are lattice points of
two circles with centres `0` and `k_h ≠ 0`, hence at most two. -/
private theorem card_fibre_filter_le_two {k : Mode} (hk : (k 0, k 1) ≠ (0, 0)) (A B u : ℤ) :
    ((fibre k A B).filter fun p => p 2 = u).card ≤ 2 := by
  classical
  set S := (fibre k A B).filter fun p => p 2 = u with hS
  have hinj : Set.InjOn (fun p : Mode => (p 0, p 1)) S := by
    intro p hp p' hp' h
    simp only [Prod.mk.injEq] at h
    rw [Finset.mem_coe, hS, Finset.mem_filter] at hp hp'
    have h2 : p 2 = p' 2 := hp.2.trans hp'.2.symm
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
    · exact h2
  rw [← Finset.card_image_of_injOn hinj]
  by_cases hu : u = 0
  · have hempty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      rw [hS, Finset.mem_filter, fibre, Finset.mem_filter] at hp
      exact (mem_nearBox.1 hp.1.1).2.1 (hp.2.trans hu)
    simp [hempty]
  apply card_two_circles_le (c := (k 0, k 1)) hk (A / u ^ 2 - u ^ 2)
    (B / (k 2 - u) ^ 2 - (k 2 - u) ^ 2)
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [hS, Finset.mem_filter, fibre, Finset.mem_filter] at hp
  obtain ⟨⟨hbox, hA, hB⟩, hpu⟩ := hp
  obtain ⟨-, -, hj3, -, -⟩ := mem_nearBox.1 hbox
  have hju : (k - p) 2 = k 2 - u := by simp [hpu]
  have e1 : A / u ^ 2 = p 0 ^ 2 + p 1 ^ 2 + u ^ 2 := by
    rw [← hA, legA, nsqZ_eq, hpu]
    exact Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hu)
  have e2 : B / (k 2 - u) ^ 2 = (k 0 - p 0) ^ 2 + (k 1 - p 1) ^ 2 + (k 2 - u) ^ 2 := by
    rw [← hB, legA, nsqZ_eq]
    simp only [Pi.sub_apply]
    rw [hpu]
    exact Int.mul_ediv_cancel_left _ (pow_ne_zero 2 (by rwa [hju] at hj3))
  constructor
  · simp only
    rw [e1]
    ring
  · simp only
    rw [e2]
    ring

/-- Over a fixed vertical component `u`, the fibre legs inject into the lattice points of the
circle `x² + y² = A/u² − u²`. -/
private theorem card_fibre_filter_le_circle {k : Mode} (A B u : ℤ) (hu : u ≠ 0) :
    ((fibre k A B).filter fun p => p 2 = u).card ≤
      (solSet (-1) (((A / u ^ 2 - u ^ 2).toNat : ℕ) : ℤ) (A / u ^ 2 - u ^ 2).toNat).card := by
  classical
  set n : ℤ := A / u ^ 2 - u ^ 2 with hn
  apply Finset.card_le_card_of_injOn (fun p : Mode => (p 0, p 1))
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, fibre, Finset.mem_filter] at hp
    obtain ⟨⟨-, hA, -⟩, hpu⟩ := hp
    have hn' : n = p 0 ^ 2 + p 1 ^ 2 := by
      rw [hn, ← hA, legA, nsqZ_eq, hpu, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hu)]
      ring
    have hn0 : 0 ≤ n := by
      rw [hn']
      positivity
    rw [Finset.mem_coe, mem_solSet, Int.toNat_of_nonneg hn0]
    refine ⟨?_, ?_, ?_⟩
    · rw [hn', Int.abs_eq_natAbs]
      nlinarith [Int.natAbs_le_self_sq (p 0), sq_nonneg (p 1)]
    · rw [hn', Int.abs_eq_natAbs]
      nlinarith [Int.natAbs_le_self_sq (p 1), sq_nonneg (p 0)]
    · simp only
      rw [hn']
      ring
  · intro p hp p' hp' h
    simp only [Prod.mk.injEq] at h
    rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
    · exact hp.2.trans hp'.2.symm

/-- Off-axis: the vertical components occurring in the fibre divide `A`, so there are at most
`2τ(|A|)` of them. -/
private theorem card_image_vertical_le {k : Mode} (A B : ℤ) (hA : A ≠ 0) :
    ((fibre k A B).image fun p => p 2).card ≤ 2 * A.natAbs.divisors.card := by
  classical
  have hsub : (fibre k A B).image (fun p => p 2) ⊆
      A.natAbs.divisors.image (fun d : ℕ => (d : ℤ)) ∪
        A.natAbs.divisors.image (fun d : ℕ => -(d : ℤ)) := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨p, hp, rfl⟩ := hu
    rw [fibre, Finset.mem_filter] at hp
    obtain ⟨-, hA', -⟩ := hp
    have hdvd : (p 2).natAbs ∣ A.natAbs := by
      rw [Int.natAbs_dvd_natAbs, ← hA', legA]
      exact Dvd.intro (p 2 * nsqZ p) (by ring)
    have hmem : (p 2).natAbs ∈ A.natAbs.divisors :=
      Nat.mem_divisors.2 ⟨hdvd, Int.natAbs_ne_zero.2 hA⟩
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases Int.natAbs_eq (p 2) with h | h
    · exact Or.inl ⟨_, hmem, h.symm⟩
    · exact Or.inr ⟨_, hmem, h.symm⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ A.natAbs.divisors.card + A.natAbs.divisors.card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * A.natAbs.divisors.card := by ring

/-- On-axis: at most five vertical components occur in the fibre (`card_axis_vertical_le`). -/
private theorem card_image_vertical_le_five {k : Mode} (hk : k 2 ≠ 0) (h0 : k 0 = 0)
    (h1 : k 1 = 0) (A B : ℤ) : ((fibre k A B).image fun p => p 2).card ≤ 5 := by
  classical
  apply card_axis_vertical_le hk A B
  intro u hu
  rw [Finset.mem_image] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  rw [fibre, Finset.mem_filter] at hp
  obtain ⟨hbox, hA, hB⟩ := hp
  obtain ⟨-, hp3, hj3, -, -⟩ := mem_nearBox.1 hbox
  refine ⟨hp3, by simpa using hj3, p 0 ^ 2 + p 1 ^ 2, ?_, ?_⟩
  · rw [← hA, legA, nsqZ_eq]
  · rw [← hB, legA, nsqZ_eq]
    simp only [Pi.sub_apply, h0, h1]
    ring

/-- The explicit fibre bound. -/
def fibB (τm Nm : ℝ) : ℝ := 4 * τm + 5 * (1 + (8 + 12 * Real.log Nm) * τm ^ 3)

/-- **The fibre bound with explicit constant**: `#{p ∈ box : A(p) = A, A(k − p) = B} ≤ fibB τm Nm`
for fast outputs, if `τ ≤ τm` up to `Nm ≥ K⁴`. -/
theorem card_fibre_explicit {τm Nm : ℝ}
    (hτ : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ Nm → (n.divisors.card : ℝ) ≤ τm) (hτ0 : 0 ≤ τm)
    {k : Mode} (hk : k 2 ≠ 0) (hN : absk k ^ 4 ≤ Nm) (A B : ℤ) :
    ((fibre k A B).card : ℝ) ≤ fibB τm Nm := by
  classical
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hK4 : 1 ≤ absk k ^ 4 := one_le_pow₀ hK1
  have hNm1 : 1 ≤ Nm := hK4.trans hN
  have hlogNm : 0 ≤ Real.log Nm := Real.log_nonneg hNm1
  have hG0 : 0 ≤ (8 + 12 * Real.log Nm) * τm ^ 3 := by positivity
  have hF0 : 0 ≤ fibB τm Nm := by
    unfold fibB
    positivity
  rcases (fibre k A B).eq_empty_or_nonempty with he | ⟨p₀, hp₀⟩
  · rw [he, Finset.card_empty, Nat.cast_zero]
    exact hF0
  have hp₀' := hp₀
  rw [fibre, Finset.mem_filter] at hp₀'
  obtain ⟨hbox₀, hA₀, -⟩ := hp₀'
  have hApos : 0 < A := hA₀ ▸ legA_pos (mem_nearBox.1 hbox₀).2.1
  have hAle : (A : ℝ) ≤ absk k ^ 4 := by
    rw [← hA₀]
    exact (legA_le p₀).trans
      (pow_le_pow_left₀ (absk_nonneg _) (mem_nearBox.1 hbox₀).2.2.2.1 4)
  have hfw : ∀ x ∈ fibre k A B, (fun p : Mode => p 2) x ∈ (fibre k A B).image fun p => p 2 :=
    fun x hx => Finset.mem_image_of_mem _ hx
  by_cases hax : (k 0, k 1) = (0, 0)
  · -- on-axis output: at most five vertical components, each fibre on one circle
    simp only [Prod.mk.injEq] at hax
    obtain ⟨h0, h1⟩ := hax
    have himg := card_image_vertical_le_five hk h0 h1 A B
    have hfib : ∀ u ∈ (fibre k A B).image (fun p => p 2),
        (((fibre k A B).filter fun p => p 2 = u).card : ℝ) ≤
          1 + (8 + 12 * Real.log Nm) * τm ^ 3 := by
      intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨p, hp, rfl⟩ := hu
      rw [fibre, Finset.mem_filter] at hp
      obtain ⟨hbox, hA, -⟩ := hp
      obtain ⟨-, hp3, -, hpk, -⟩ := mem_nearBox.1 hbox
      set n : ℤ := A / p 2 ^ 2 - p 2 ^ 2 with hn
      have hn' : n = p 0 ^ 2 + p 1 ^ 2 := by
        rw [hn, ← hA, legA, nsqZ_eq, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp3)]
        ring
      have hn0 : 0 ≤ n := by
        rw [hn']
        positivity
      have hnK : (n : ℝ) ≤ absk k ^ 2 := by
        rw [absk_sq_eq_nsqZ]
        have h2 := (absk_le_absk_iff p k).1 hpk
        rw [nsqZ_eq] at h2
        have : n ≤ nsqZ k := by
          rw [hn']
          nlinarith [sq_nonneg (p 2)]
        exact_mod_cast this
      have hcard := card_fibre_filter_le_circle (k := k) A B (p 2) hp3
      rcases Nat.eq_zero_or_pos n.toNat with hz | hpos
      · have h1' : (solSet (-1) ((0 : ℕ) : ℤ) 0).card ≤ 1 := by
          calc (solSet (-1) ((0 : ℕ) : ℤ) 0).card
              ≤ (Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) ×ˢ
                  Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).card := Finset.card_filter_le _ _
            _ = 1 := by simp
        rw [hz] at hcard
        have : (((fibre k A B).filter fun p' => p' 2 = p 2).card : ℝ) ≤ 1 := by
          exact_mod_cast hcard.trans h1'
        linarith
      · have hnR : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hn0]
        have hnNm : ((n.toNat : ℕ) : ℝ) ≤ Nm := by
          rw [hnR]
          have h2 : absk k ^ 2 ≤ absk k ^ 4 :=
            pow_le_pow_right₀ hK1 (by norm_num)
          linarith
        calc (((fibre k A B).filter fun p' => p' 2 = p 2).card : ℝ)
            ≤ (solSet (-1) (n.toNat : ℤ) n.toNat).card := by exact_mod_cast hcard
          _ ≤ (8 + 12 * Real.log Nm) * τm ^ 3 := card_circle_explicit hτ hpos hnNm
          _ ≤ 1 + (8 + 12 * Real.log Nm) * τm ^ 3 := by linarith
    calc ((fibre k A B).card : ℝ)
        = ∑ u ∈ (fibre k A B).image (fun p => p 2),
            (((fibre k A B).filter fun p => p 2 = u).card : ℝ) := by
          rw [Finset.card_eq_sum_card_fiberwise hfw]
          push_cast
          rfl
      _ ≤ ∑ _u ∈ (fibre k A B).image (fun p => p 2), (1 + (8 + 12 * Real.log Nm) * τm ^ 3) :=
          Finset.sum_le_sum hfib
      _ = (((fibre k A B).image fun p => p 2).card : ℝ) *
            (1 + (8 + 12 * Real.log Nm) * τm ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 5 * (1 + (8 + 12 * Real.log Nm) * τm ^ 3) := by
          gcongr
          exact_mod_cast himg
      _ ≤ fibB τm Nm := by
          unfold fibB
          linarith
  · -- off-axis output: `u² ∣ A`, then two circles with distinct centres
    have h2 : ∀ u ∈ (fibre k A B).image (fun p => p 2),
        ((fibre k A B).filter fun p => p 2 = u).card ≤ 2 :=
      fun u _ => card_fibre_filter_le_two hax A B u
    have hmul := Finset.card_le_mul_card_image (fibre k A B) 2 h2
    have himg := card_image_vertical_le (k := k) A B hApos.ne'
    have hAn : ((A.natAbs : ℕ) : ℝ) ≤ Nm := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hApos)]
      linarith
    have hτA : (A.natAbs.divisors.card : ℝ) ≤ τm := hτ A.natAbs (Int.natAbs_pos.2 hApos.ne') hAn
    calc ((fibre k A B).card : ℝ) ≤ ((2 * (2 * A.natAbs.divisors.card) : ℕ) : ℝ) := by
          exact_mod_cast hmul.trans (Nat.mul_le_mul_left 2 himg)
      _ = 4 * (A.natAbs.divisors.card : ℝ) := by push_cast; ring
      _ ≤ 4 * τm := by gcongr
      _ ≤ fibB τm Nm := by
          unfold fibB
          linarith

/-! ### The centred count -/

/-- **The centred count with the fibre and divisor bounds as parameters**: the proof of
`near_count`, without its numerics.  With `n = 4C = 4k₃²K²`,
`#{p near : |D(p)| ≤ T} ≤ 7 τ(n)³ F (K/|k₃|) T`. -/
theorem near_count_of_fibre {F τn : ℝ} (hF0 : 0 ≤ F) {k : Mode} (hk : k 2 ≠ 0)
    (hfib : ∀ A B : ℤ, ((fibre k A B).card : ℝ) ≤ F)
    (hτn : (((4 * legA k).natAbs.divisors.card : ℕ) : ℝ) ≤ τn)
    (s₁ s₂ : Sgn) {T : ℝ} (hT : 0 ≤ T) :
    ((countSet s₁ s₂ k T).card : ℝ) ≤ 7 * τn ^ 3 * F * (absk k / |(k 2 : ℝ)|) * T := by
  classical
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hK0 : 0 < absk k := by linarith
  have hw : 0 < |(k 2 : ℝ)| := abs_pos.2 (by exact_mod_cast hk)
  have hwK : |(k 2 : ℝ)| ≤ absk k := abs_coord_le_absk k 2
  have hw1 : 1 ≤ |(k 2 : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hKw : 1 ≤ absk k / |(k 2 : ℝ)| := by
    rw [le_div_iff₀ hw]
    linarith
  -- the modulus `n = 4C`
  set n : ℕ := (4 * legA k).natAbs with hn
  have hC : 0 < legA k := legA_pos hk
  have hn0 : 0 < n := by
    rw [hn]
    exact Int.natAbs_pos.2 (by omega)
  have : NeZero n := ⟨hn0.ne'⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR : (n : ℝ) = 4 * |(k 2 : ℝ)| ^ 2 * absk k ^ 2 := by
    have h1 : ((n : ℤ) : ℝ) = (n : ℝ) := Int.cast_natCast n
    have h2 : (n : ℤ) = 4 * legA k := by
      rw [hn]
      exact Int.natAbs_of_nonneg (by omega)
    rw [← h1, h2, sq_abs, absk_sq_eq_nsqZ, legA]
    push_cast
    ring
  -- the window half-width `W`
  set W : ℤ := ⌈4 * |(k 2 : ℝ)| * absk k ^ 3⌉ with hW
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact Int.ceil_nonneg (by positivity)
  have hWR : (0 : ℝ) ≤ W := by exact_mod_cast hW0
  have hWle : (W : ℝ) ≤ 5 * |(k 2 : ℝ)| * absk k ^ 3 := by
    have h1 := Int.ceil_lt_add_one (4 * |(k 2 : ℝ)| * absk k ^ 3)
    have h2 : 1 ≤ |(k 2 : ℝ)| * absk k ^ 3 := by
      have := one_le_pow₀ hK1 (n := 3)
      nlinarith
    rw [hW]
    linarith
  -- the `d`-range and the window
  set Tn : ℕ := ⌊T⌋₊ with hTn
  have hTnT : (Tn : ℝ) ≤ T := Nat.floor_le hT
  set D : Finset ℤ := (Finset.Icc (-(Tn : ℤ)) Tn).erase 0 with hD
  set win : Finset ℤ := Finset.Icc (legA k - W) (legA k + W) with hwin
  set S := countSet s₁ s₂ k T with hS
  set f : Mode → ℤ × ℤ := fun p => dyMap p k with hf
  -- Step A: the fibres of `(d, y)` are fibres of `(A, B)`.
  have hfw : ∀ p ∈ S, f p ∈ S.image f := fun p hp => Finset.mem_image_of_mem f hp
  have hA : (S.card : ℝ) ≤ (S.image f).card * F := by
    rw [Finset.card_eq_sum_card_fiberwise hfw]
    push_cast
    calc ∑ dy ∈ S.image f, ((S.filter fun p => f p = dy).card : ℝ)
        ≤ ∑ _dy ∈ S.image f, F := by
          refine Finset.sum_le_sum ?_
          rintro ⟨d, y⟩ _
          calc ((S.filter fun p => f p = (d, y)).card : ℝ)
              ≤ ((fibre k ((y ^ 2 - d) / (4 * legA k))
                  ((y ^ 2 - d) / (4 * legA k) + legA k - y)).card : ℝ) := by
                exact_mod_cast Finset.card_le_card (fibre_dyMap_subset s₁ s₂ hk T d y)
            _ ≤ F := hfib _ _
      _ = (S.image f).card * F := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Step B: the image lies in the pairs `(d, y)`, `d ∈ D`, `y ∈ win`, `y² ≡ d (mod n)`.
  have hB : S.image f ⊆ D.biUnion fun d =>
      (win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).image fun y => (d, y) := by
    intro dy hdy
    rw [Finset.mem_image] at hdy
    obtain ⟨p, hp, rfl⟩ := hdy
    obtain ⟨⟨hd0, hdT⟩, hwin', hcong⟩ := dyMap_mem hp
    rw [Finset.mem_biUnion]
    refine ⟨normD p k, ?_, ?_⟩
    · rw [hD, Finset.mem_erase, Finset.mem_Icc]
      have h1 : (normD p k).natAbs ≤ Tn := by
        rw [hTn]
        apply Nat.le_floor
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact hdT
      refine ⟨hd0, ?_, ?_⟩ <;> omega
    · rw [Finset.mem_image]
      refine ⟨legA p - legA (k - p) + legA k, ?_, rfl⟩
      rw [Finset.mem_filter, hwin, Finset.mem_Icc]
      refine ⟨?_, hcong⟩
      have h1 : |((legA p - legA (k - p) + legA k - legA k : ℤ) : ℝ)| ≤ (W : ℝ) :=
        hwin'.trans (by rw [hW]; exact Int.le_ceil _)
      have h2 : |legA p - legA (k - p) + legA k - legA k| ≤ W := by exact_mod_cast h1
      rw [abs_le] at h2
      constructor <;> linarith [h2.1, h2.2]
  -- Step C: for each `d`, the window carries at most `#roots · (2W/n + 1)` values of `y`.
  have hroots : ∀ d : ℤ,
      ((win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).card : ℝ) ≤
        (Nat.card {t : ZMod n // t ^ 2 = d} : ℝ) * (2 * W / n + 1) := by
    intro d
    set R : Finset (ZMod n) := Finset.univ.filter fun r => r ^ 2 = (d : ZMod n) with hR
    have hsub : (win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)) ⊆
        R.biUnion fun r => win.filter fun y : ℤ => ((y : ℤ) : ZMod n) = r := by
      intro y hy
      rw [Finset.mem_filter] at hy
      rw [Finset.mem_biUnion]
      refine ⟨(y : ZMod n), ?_, ?_⟩
      · rw [hR, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hy.2⟩
      · rw [Finset.mem_filter]
        exact ⟨hy.1, rfl⟩
    have hcardR : (R.card : ℝ) = Nat.card {t : ZMod n // t ^ 2 = d} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    calc ((win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).card : ℝ)
        ≤ ((R.biUnion fun r => win.filter fun y : ℤ => ((y : ℤ) : ZMod n) = r).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ r ∈ R, ((win.filter fun y : ℤ => ((y : ℤ) : ZMod n) = r).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ R, (2 * (W : ℝ) / n + 1) :=
          Finset.sum_le_sum fun r _ => card_residue_window_le hn0 (legA k) hW0 r
      _ = (R.card : ℝ) * (2 * W / n + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = _ := by rw [hcardR]
  have hsumroots : ∑ d ∈ D, (Nat.card {t : ZMod n // t ^ 2 = d} : ℝ) ≤
      2 * T * (n.divisors.card : ℝ) ^ 3 := by
    refine (sum_card_sqrt_le n Tn hn0).trans ?_
    gcongr
  have hlift0 : (0 : ℝ) ≤ 2 * W / n + 1 := by positivity
  have himg : ((S.image f).card : ℝ) ≤
      2 * T * (n.divisors.card : ℝ) ^ 3 * (2 * W / n + 1) := by
    calc ((S.image f).card : ℝ)
        ≤ ((D.biUnion fun d => (win.filter fun y : ℤ =>
            ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).image fun y => (d, y)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hB
      _ ≤ ∑ d ∈ D, (((win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).image
            fun y => (d, y)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ d ∈ D, ((win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).card : ℝ) :=
          Finset.sum_le_sum fun d _ => by exact_mod_cast Finset.card_image_le
      _ ≤ ∑ d ∈ D, (Nat.card {t : ZMod n // t ^ 2 = d} : ℝ) * (2 * W / n + 1) :=
          Finset.sum_le_sum fun d _ => hroots d
      _ = (∑ d ∈ D, (Nat.card {t : ZMod n // t ^ 2 = d} : ℝ)) * (2 * W / n + 1) := by
          rw [Finset.sum_mul]
      _ ≤ 2 * T * (n.divisors.card : ℝ) ^ 3 * (2 * W / n + 1) := by gcongr
  -- Step D: numerics of the lifts.
  have hlift : 2 * (W : ℝ) / n + 1 ≤ 7 / 2 * (absk k / |(k 2 : ℝ)|) := by
    have h1 : 2 * (W : ℝ) / n ≤ 5 / 2 * (absk k / |(k 2 : ℝ)|) := by
      rw [div_le_iff₀ hnpos, hnR]
      calc 2 * (W : ℝ) ≤ 2 * (5 * |(k 2 : ℝ)| * absk k ^ 3) := by gcongr
        _ = 5 / 2 * (absk k / |(k 2 : ℝ)|) * (4 * |(k 2 : ℝ)| ^ 2 * absk k ^ 2) := by
            field_simp
            ring
    linarith
  have hτ3 : (n.divisors.card : ℝ) ^ 3 ≤ τn ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hτn 3
  have hτn0 : 0 ≤ τn := le_trans (Nat.cast_nonneg _) hτn
  calc (S.card : ℝ) ≤ (S.image f).card * F := hA
    _ ≤ (2 * T * (n.divisors.card : ℝ) ^ 3 * (2 * W / n + 1)) * F := by
        gcongr
    _ ≤ (2 * T * τn ^ 3 * (7 / 2 * (absk k / |(k 2 : ℝ)|))) * F := by
        gcongr
    _ = 7 * τn ^ 3 * F * (absk k / |(k 2 : ℝ)|) * T := by ring

/-- The modulus `4C = 4 k₃² K²` of the centred count is at most `4K⁴`. -/
theorem natAbs_four_legA_le {k : Mode} (hk : k 2 ≠ 0) :
    (((4 * legA k).natAbs : ℕ) : ℝ) ≤ 4 * absk k ^ 4 := by
  have hC : 0 < legA k := legA_pos hk
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast (by omega : 0 < 4 * legA k))]
  push_cast
  linarith [legA_le k]

/-- **The explicit centred count** (`near_count` with the constant displayed): if `τ ≤ τm` up to
`Nm ≥ 4K⁴`, then `#{p near : |D(p)| ≤ T} ≤ 7 τm³ (fibB τm Nm) (K/|k₃|) T`. -/
theorem near_count_explicit {τm Nm : ℝ}
    (hτ : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ Nm → (n.divisors.card : ℝ) ≤ τm) (hτ0 : 0 ≤ τm)
    {k : Mode} (hk : k 2 ≠ 0) (hN : 4 * absk k ^ 4 ≤ Nm) (s₁ s₂ : Sgn) {T : ℝ} (hT : 0 ≤ T) :
    ((countSet s₁ s₂ k T).card : ℝ) ≤
      7 * τm ^ 3 * fibB τm Nm * (absk k / |(k 2 : ℝ)|) * T := by
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hK4 : 0 ≤ absk k ^ 4 := by positivity
  have hN' : absk k ^ 4 ≤ Nm := by linarith
  have hNm1 : 1 ≤ Nm := (one_le_pow₀ hK1).trans hN'
  have hF0 : 0 ≤ fibB τm Nm := by
    have := Real.log_nonneg hNm1
    unfold fibB
    positivity
  have hmod : 1 ≤ (4 * legA k).natAbs := by
    have := legA_pos hk
    exact Int.natAbs_pos.2 (by omega)
  exact near_count_of_fibre hF0 hk (card_fibre_explicit hτ hτ0 hk hN')
    (hτ _ hmod ((natAbs_four_legA_le hk).trans hN)) s₁ s₂ hT

/-- The count in the form used by the layer-cake summation (`near_count_nat`, explicit). -/
theorem near_count_nat_explicit {τm Nm : ℝ}
    (hτ : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ Nm → (n.divisors.card : ℝ) ≤ τm) (hτ0 : 0 ≤ τm)
    {k : Mode} (hk : k 2 ≠ 0) (hN : 4 * absk k ^ 4 ≤ Nm) (s₁ s₂ : Sgn) (t : ℕ) :
    ((((nearBox k).filter fun p => IsNear s₁ s₂ p k).filter
      fun p => (normD p k).natAbs ≤ t).card : ℝ) ≤
        7 * τm ^ 3 * fibB τm Nm * (absk k / |(k 2 : ℝ)|) * t := by
  refine le_trans ?_ (near_count_explicit hτ hτ0 hk hN s₁ s₂ (T := t) (by positivity))
  gcongr
  intro p hp
  simp only [Finset.mem_filter] at hp
  refine mem_countSet.2 ⟨hp.1.1, hp.1.2, ?_⟩
  have h1 : ((normD p k).natAbs : ℝ) ≤ t := by exact_mod_cast hp.2
  rwa [Nat.cast_natAbs, Int.cast_abs] at h1

end OVNS.Quant.NearJ

end
