import OddViscousNS.Quant.Energy.NearJ.Explicit
import OddViscousNS.Quant.Energy.Near.Sums

/-!
# J1, part 2: the small-output moments with the explicit subpower

`momN_le_explicit`: the Lorentzian-layer summation of `Near/Profiles.lean` with the constant
displayed, `momN q k ≤ 54 · 7 τm³ (fibB τm Nm) (1 + log⌈27K⁶⌉) / q` (kernel through the norm form,
`κ_N² ≤ 27|k₃|/(2qK|D|)`, then the layer cake against the centred count; the factors `K/|k₃|`
cancel, so nothing depends on `k₃`).

`momN_low`: at `τm = Ex cTau q`, `Nm = q`, for the outputs `K⁶ ≤ q` and `log q ≥ 5`,
`momN q k ≤ 52920 Ex(6 cTau + 8, q)/q`.  The polynomial `log q` factors are absorbed by
`sq_log_le_Ex` (`(log q)² ≤ Ex(8, q)`).

The lemmas `nearW_le_of_near`, `momN_eq_sum_patterns`, `sum_nearW_le_sum_inv` are restated from
`Near/Profiles.lean` (namespace `NearJ`), so that this directory does not import that file: thus
`Near/Profiles.lean` may later import `NearJ/Main.lean` to discharge `nearProfiles`.
-/

noncomputable section

namespace OVNS.Quant.NearJ

open Finset

/-! ### The kernel through the norm form (restated from `Near/Profiles.lean`) -/

/-- `κ_N² ≤ 27 |k₃| / (2 q K |D|)` on near triads. -/
theorem nearW_le_of_near {q : ℝ} (hq : 0 < q) {s₁ s₂ : Sgn} {p k : Mode} (hp : p ∈ nearBox k)
    (h : IsNear s₁ s₂ p k) :
    nearW q s₁ s₂ p k ≤ 27 * |(k 2 : ℝ)| / (2 * q * absk k * |(normD p k : ℝ)|) := by
  have hk : (k 2 : ℝ) ≠ 0 := by exact_mod_cast (mem_nearBox.1 hp).1
  have hw : 0 < |(k 2 : ℝ)| := abs_pos.2 hk
  have hm := minLeg_pos hp
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk_of_mem_nearBox hp).1
  have hD : 0 < |(normD p k : ℝ)| := lt_of_lt_of_le one_pos (one_le_abs_normD_of_near hp h)
  have hDle := abs_normD_le_of_near hp h
  set Φ := nearPhi s₁ s₂ p k
  have hAM : 2 * absk k ^ 2 * q * |Φ| ≤ absk k ^ 4 + q ^ 2 * Φ ^ 2 := by
    nlinarith [sq_nonneg (absk k ^ 2 - q * |Φ|), sq_abs Φ]
  have hX : 0 < minLeg p k ^ 2 * absk k ^ 2 * (absk k ^ 4 + q ^ 2 * Φ ^ 2) := by positivity
  have e : nearW q s₁ s₂ p k = nearKer q s₁ s₂ p k := by simp [nearW, h]
  rw [e, nearKer, div_le_div_iff₀ hX (by positivity), one_mul]
  calc 2 * q * absk k * |(normD p k : ℝ)|
      ≤ 2 * q * absk k * (27 * |Φ| * minLeg p k ^ 2 * absk k ^ 3 * |(k 2 : ℝ)|) := by gcongr
    _ = 27 * |(k 2 : ℝ)| * (minLeg p k ^ 2 * absk k ^ 2 * (2 * absk k ^ 2 * q * |Φ|)) := by ring
    _ ≤ 27 * |(k 2 : ℝ)| * (minLeg p k ^ 2 * absk k ^ 2 * (absk k ^ 4 + q ^ 2 * Φ ^ 2)) := by
        gcongr

/-- `momN` as the sum over the four patterns of the sums over their near sets. -/
theorem momN_eq_sum_patterns (q : ℝ) (k : Mode) :
    momN q k = ∑ s : Sgn × Sgn,
      ∑ p ∈ (nearBox k).filter (fun p => IsNear s.1 s.2 p k), nearW q s.1 s.2 p k := by
  unfold momN
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_filter_of_ne]
  intro p _ hne
  by_contra h
  exact hne (by simp [nearW, h])

/-- The near sum of one pattern through `Σ 1/|D|`. -/
theorem sum_nearW_le_sum_inv {q : ℝ} (hq : 0 < q) (s₁ s₂ : Sgn) {k : Mode} :
    ∑ p ∈ (nearBox k).filter (fun p => IsNear s₁ s₂ p k), nearW q s₁ s₂ p k ≤
      27 * |(k 2 : ℝ)| / (2 * q * absk k) *
        ∑ p ∈ (nearBox k).filter (fun p => IsNear s₁ s₂ p k), (((normD p k).natAbs : ℕ) : ℝ)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [Nat.cast_natAbs, Int.cast_abs]
  refine (nearW_le_of_near hq hp.1 hp.2).trans (le_of_eq ?_)
  ring

/-! ### The layer sum with explicit constant -/

theorem fibB_nonneg {τm Nm : ℝ} (hτ0 : 0 ≤ τm) (hNm : 1 ≤ Nm) : 0 ≤ fibB τm Nm := by
  have := Real.log_nonneg hNm
  unfold fibB
  positivity

/-- The layer cake for one pattern, explicitly:
`Σ_{p near} 1/|D(p)| ≤ 7 τm³ (fibB τm Nm) (K/|k₃|) (1 + log⌈27K⁶⌉)`. -/
theorem sum_inv_normD_explicit {τm Nm : ℝ}
    (hτ : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ Nm → (n.divisors.card : ℝ) ≤ τm) (hτ0 : 0 ≤ τm)
    {k : Mode} (hk : k 2 ≠ 0) (hN : 4 * absk k ^ 4 ≤ Nm) (s₁ s₂ : Sgn) :
    ∑ p ∈ (nearBox k).filter (fun p => IsNear s₁ s₂ p k), (((normD p k).natAbs : ℕ) : ℝ)⁻¹ ≤
      7 * τm ^ 3 * fibB τm Nm * (absk k / |(k 2 : ℝ)|) *
        (1 + Real.log (⌈27 * absk k ^ 6⌉₊ : ℕ)) := by
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hNm : 1 ≤ Nm := by
    have := one_le_pow₀ hK1 (n := 4)
    linarith
  have hF := fibB_nonneg hτ0 hNm
  have key := sum_inv_le_of_card_le ((nearBox k).filter fun p => IsNear s₁ s₂ p k)
    (fun p => (normD p k).natAbs) ⌈27 * absk k ^ 6⌉₊
    (7 * τm ^ 3 * fibB τm Nm * (absk k / |(k 2 : ℝ)|))
    ?_ (fun t _ => near_count_nat_explicit hτ hτ0 hk hN s₁ s₂ t)
  · refine key.trans (mul_le_mul_of_nonneg_left (sum_Icc_inv_le_log _) ?_)
    exact mul_nonneg (by positivity) (div_nonneg (absk_nonneg k) (abs_nonneg _))
  · intro p hp
    rw [Finset.mem_filter] at hp
    refine ⟨Int.natAbs_pos.2 (normD_ne_zero_of_near hp.1 hp.2), ?_⟩
    have h1 := abs_normD_le_pow_of_near hp.1 hp.2
    have h2 : (((normD p k).natAbs : ℕ) : ℝ) ≤ 27 * absk k ^ 6 := by
      rwa [Nat.cast_natAbs, Int.cast_abs]
    exact_mod_cast h2.trans (Nat.le_ceil _)

/-- **Lorentzian-layer summation with explicit constant**:
`momN q k ≤ 54 · 7 τm³ (fibB τm Nm) (1 + log⌈27K⁶⌉) / q` for fast outputs. -/
theorem momN_le_explicit {q τm Nm : ℝ} (hq : 0 < q)
    (hτ : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ Nm → (n.divisors.card : ℝ) ≤ τm) (hτ0 : 0 ≤ τm)
    {k : Mode} (hk : k 2 ≠ 0) (hN : 4 * absk k ^ 4 ≤ Nm) :
    momN q k ≤ 54 * (7 * τm ^ 3 * fibB τm Nm) * (1 + Real.log (⌈27 * absk k ^ 6⌉₊ : ℕ)) / q := by
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hK : 0 < absk k := by linarith
  have hw : 0 < |(k 2 : ℝ)| := abs_pos.2 (by exact_mod_cast hk)
  set X := 7 * τm ^ 3 * fibB τm Nm with hX
  set Lg := 1 + Real.log (⌈27 * absk k ^ 6⌉₊ : ℕ) with hLg
  have hpat : ∀ s : Sgn × Sgn,
      ∑ p ∈ (nearBox k).filter (fun p => IsNear s.1 s.2 p k), nearW q s.1 s.2 p k ≤
        27 / 2 * X * Lg / q := by
    intro s
    calc ∑ p ∈ (nearBox k).filter (fun p => IsNear s.1 s.2 p k), nearW q s.1 s.2 p k
        ≤ 27 * |(k 2 : ℝ)| / (2 * q * absk k) *
            ∑ p ∈ (nearBox k).filter (fun p => IsNear s.1 s.2 p k),
              (((normD p k).natAbs : ℕ) : ℝ)⁻¹ := sum_nearW_le_sum_inv hq s.1 s.2
      _ ≤ 27 * |(k 2 : ℝ)| / (2 * q * absk k) * (X * (absk k / |(k 2 : ℝ)|) * Lg) := by
          gcongr
          exact sum_inv_normD_explicit hτ hτ0 hk hN s.1 s.2
      _ = 27 / 2 * X * Lg / q := by
          field_simp
  rw [momN_eq_sum_patterns]
  calc ∑ s : Sgn × Sgn,
        ∑ p ∈ (nearBox k).filter (fun p => IsNear s.1 s.2 p k), nearW q s.1 s.2 p k
      ≤ ∑ _s : Sgn × Sgn, 27 / 2 * X * Lg / q := Finset.sum_le_sum fun s _ => hpat s
    _ = 54 * X * Lg / q := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
          nsmul_eq_mul]
        push_cast
        ring

/-! ### The polynomial logarithms against the subpower -/

/-- `log 28 ≤ 4`. -/
theorem log_28_le : Real.log 28 ≤ 4 := by
  have h1 : Real.log 28 ≤ Real.log (2 ^ 5) := Real.log_le_log (by norm_num) (by norm_num)
  have h2 := Real.log_two_lt_d9
  rw [Real.log_pow] at h1
  push_cast at h1
  linarith

/-- `1 + log⌈27K⁶⌉ ≤ 5 + 6 log K`. -/
theorem one_add_log_ceil_le' {K : ℝ} (hK : 1 ≤ K) :
    1 + Real.log (⌈27 * K ^ 6⌉₊ : ℕ) ≤ 5 + 6 * Real.log K := by
  have hK0 : 0 < K := by linarith
  have hK6 : (1 : ℝ) ≤ K ^ 6 := one_le_pow₀ hK
  have h1 : ((⌈27 * K ^ 6⌉₊ : ℕ) : ℝ) ≤ 28 * K ^ 6 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 27 * K ^ 6)
    linarith
  have hpos : (0 : ℝ) < (⌈27 * K ^ 6⌉₊ : ℕ) := by
    have := Nat.le_ceil (27 * K ^ 6)
    have : (0 : ℝ) < 27 * K ^ 6 := by positivity
    linarith
  have h2 : Real.log (⌈27 * K ^ 6⌉₊ : ℕ) ≤ Real.log 28 + 6 * Real.log K := by
    calc Real.log (⌈27 * K ^ 6⌉₊ : ℕ) ≤ Real.log (28 * K ^ 6) := Real.log_le_log hpos h1
      _ = Real.log 28 + 6 * Real.log K := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring
  linarith [log_28_le]

/-- `(log L)² ≤ 4 L` for `L ≥ 1`. -/
theorem sq_log_le {L : ℝ} (hL : 1 ≤ L) : Real.log L ^ 2 ≤ 4 * L := by
  have hL0 : 0 < L := by linarith
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hss : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have h1 : Real.log L = 2 * Real.log (Real.sqrt L) := by
    rw [Real.log_sqrt hL0.le]
    ring
  have h2 : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := Real.log_le_sub_one_of_pos hs
  have h3 : 0 ≤ Real.log L := Real.log_nonneg hL
  have h4 : Real.log L ≤ 2 * Real.sqrt L := by linarith
  calc Real.log L ^ 2 ≤ (2 * Real.sqrt L) ^ 2 := pow_le_pow_left₀ h3 h4 2
    _ = 4 * L := by rw [mul_pow, hss]; norm_num

/-- **The polynomial logarithms against the subpower**: `(log q)² ≤ Ex(8, q)`. -/
theorem sq_log_le_Ex {q : ℝ} (hq : 3 ≤ Real.log q) : Real.log q ^ 2 ≤ Ex 8 q := by
  set L := Real.log q with hL
  have hL0 : 0 < L := by linarith
  have hlL : 0 < Real.log L := Real.log_pos (by linarith)
  have h1 := sq_log_le (L := L) (by linarith)
  have h2 : 2 * Real.log L ≤ 8 * L / Real.log L := by
    rw [le_div_iff₀ hlL]
    nlinarith
  calc L ^ 2 = Real.exp (2 * Real.log L) := by
        rw [show (2 : ℝ) * Real.log L = (2 : ℕ) * Real.log L by norm_num, Real.exp_nat_mul,
          Real.exp_log hL0]
    _ ≤ Ex 8 q := Real.exp_le_exp.2 h2

theorem cTau_nonneg : 0 ≤ cTau := by
  have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  unfold cTau
  positivity

theorem Ex_pow (c t : ℝ) (n : ℕ) : Ex c t ^ n = Ex (n * c) t := by
  rw [← Real.rpow_natCast, Ex_rpow, mul_comm]

/-- `4K⁴ ≤ q` on the small outputs. -/
theorem four_pow_le_of_pow_six_le {K q : ℝ} (hK : 1 ≤ K) (hq : 64 ≤ q) (h : K ^ 6 ≤ q) :
    4 * K ^ 4 ≤ q := by
  rcases le_total K 2 with h2 | h2
  · have : K ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by linarith) h2 4
    linarith
  · have h4 : 0 ≤ K ^ 4 := by positivity
    have : K ^ 6 = K ^ 4 * K ^ 2 := by ring
    nlinarith

/-- `q ≥ 64` once `log q ≥ 5`. -/
theorem sixty_four_le {q : ℝ} (hq : 5 ≤ Real.log q) (h0 : 0 < q) : 64 ≤ q := by
  by_contra hc
  push Not at hc
  have h1 : Real.log q < Real.log 64 := Real.log_lt_log h0 hc
  have h2 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have h3 := Real.log_two_lt_d9
  linarith

/-- **The small outputs, explicit subpower**: for `K⁶ ≤ q`, `log q ≥ 5`,
`momN q k ≤ 52920 Ex(6 cTau + 8, q)/q`. -/
theorem momN_low {q : ℝ} (hq : 5 ≤ Real.log q) (hq0 : 0 < q) {k : Mode} (hk : k 2 ≠ 0)
    (hK : absk k ^ 6 ≤ q) : momN q k ≤ 52920 * Ex (6 * cTau + 8) q / q := by
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hK0 : 0 < absk k := by linarith
  set L := Real.log q with hL
  have hL5 : 5 ≤ L := hq
  have hlL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  set τm := Ex cTau q with hτmdef
  have hτ : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ q → (n.divisors.card : ℝ) ≤ τm :=
    fun n hn hnq => tau_le_Ex (by linarith) hn hnq
  have hτ1 : 1 ≤ τm := one_le_Ex cTau_nonneg (by linarith) hlL
  have hτ0 : 0 ≤ τm := by linarith
  have hN : 4 * absk k ^ 4 ≤ q :=
    four_pow_le_of_pow_six_le hK1 (sixty_four_le hq hq0) hK
  have h := momN_le_explicit hq0 hτ hτ0 hk hN
  -- the fibre bound
  have hτ3 : 1 ≤ τm ^ 3 := one_le_pow₀ hτ1
  have hτle : τm ≤ τm ^ 3 := le_self_pow₀ hτ1 (by norm_num)
  have hF : fibB τm q ≤ 70 * L * τm ^ 3 := by
    unfold fibB
    rw [← hL]
    nlinarith
  have hF0 : 0 ≤ fibB τm q := fibB_nonneg hτ0 (by linarith [sixty_four_le hq hq0])
  -- the logarithm
  have hlogK : 6 * Real.log (absk k) ≤ L := by
    have := Real.log_le_log (by positivity) hK
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hLg : 1 + Real.log (⌈27 * absk k ^ 6⌉₊ : ℕ) ≤ 2 * L := by
    have := one_add_log_ceil_le' hK1
    linarith
  have hLg0 : 0 ≤ 1 + Real.log (⌈27 * absk k ^ 6⌉₊ : ℕ) := by
    have h1 : (1 : ℝ) ≤ (⌈27 * absk k ^ 6⌉₊ : ℕ) := by
      have h2 := Nat.le_ceil (27 * absk k ^ 6)
      have h3 := one_le_pow₀ hK1 (n := 6)
      linarith
    have := Real.log_nonneg h1
    linarith
  have hsq : L ^ 2 ≤ Ex 8 q := sq_log_le_Ex (by linarith)
  have hτ6 : τm ^ 6 = Ex (6 * cTau) q := by
    rw [hτmdef, Ex_pow]
    norm_num
  calc momN q k
      ≤ 54 * (7 * τm ^ 3 * fibB τm q) * (1 + Real.log (⌈27 * absk k ^ 6⌉₊ : ℕ)) / q := h
    _ ≤ 54 * (7 * τm ^ 3 * (70 * L * τm ^ 3)) * (2 * L) / q := by
        gcongr
    _ = 52920 * L ^ 2 * τm ^ 6 / q := by ring
    _ ≤ 52920 * Ex 8 q * τm ^ 6 / q := by gcongr
    _ = 52920 * Ex (6 * cTau + 8) q / q := by
        rw [hτ6, Ex_add]
        ring

end OVNS.Quant.NearJ

end
