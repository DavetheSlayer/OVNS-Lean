import OddViscousNS.Quant.Energy.NearJ.Main
import OddViscousNS.Quant.Energy.Near.Count
import OddViscousNS.Quant.Energy.Near.Sums
import OddViscousNS.Quant.Energy.Interfaces

/-!
# E9: the near profiles `N(q) ≲ q^{−1/2+δ}`, `P(q) ≲ q^{−3/10+δ}`

Assembly of the elementary route (`OddViscousNS_data/reports/t12_near_slow_route.md` §2.2):

1. **Kernel through the norm form** (`nearW_le_of_near`): on a near triad
   `κ_N² ≤ 27|k₃| / (2 q K |D|)`, from `K⁴ + q²Φ² ≥ 2K²q|Φ|` and `|Φ| ≥ |D|/(27 m² K³ |k₃|)`
   (`abs_normD_le_of_near`).  The `m²` of the kernel cancels against the `m²` of the `D`-bound, so
   no `m`-shells are needed.
2. **Lorentzian-layer summation** (`momN_le`): `Σ_{p near} 1/|D(p)| ≤ L (1 + log(27K⁶))` with
   `L = C_δ (K/|k₃|) K^δ` from the centred count (`near_count`, `Count.lean`) and the layer cake
   (`sum_inv_le_of_card_le`, `Sums.lean`); hence `momN q k ≤ C_δ K^{δ}/q` for `q ≥ 1`
   (the report's `C_δ K^{3δ}/q`, step 3; the exponent of `K` is immaterial).
3. **Trivial bound** (`momN_le_trivial`): `momN q k ≤ 208 K^{−5}` from `κ_N² ≤ 1/(m²K⁶)` and
   `Σ_{0<|p|≤K} |p|^{−2} ≤ 26K` (`lattice_sum_le`; Body 18), used for the large outputs.
4. **Split at `K = q^{1/5}`** (`MomN_le_rpow`, `MomP_le_rpow`): `𝔐_N(q) ≤ C_δ q^{δ−1}` and
   `𝔐_P(q) ≤ C_δ q^{−3/5+δ}`; then `N = 96√𝔐_N ≤ C q^{−1/2+δ}` and
   `P = 18√𝔐_P + 2⁷q^{−3/4} ≤ C q^{−3/10+δ}` (`nearProfilesEl`).

`nearProfiles : NearProfiles nearN nearP` (the TeX's `P ≲ q^{−1/3+δ}`) is stated and left
`sorry`: it needs the MISSING LOCAL210 "full direct 238 count" for the outputs `K > q^{1/6}`
(route report §2.1 step 4).  The regimes layer only needs `NearProfilesEl` (degree
`10v/3 ≈ 12.61 < d ≈ 13.74`), and `nearProfilesEl_of_nearProfiles` shows the two are ordered.
Numerics (route report §1.5): `q·𝔐_N ≤ 0.71`, `q^{2/3}𝔐_P ≤ 0.23` for `|k| ≤ 32`, `q ≤ 10⁷`.
-/

noncomputable section

namespace OVNS.Quant

/-! ### Step 1: the kernel through the norm form -/

/-- `κ_N² ≤ 27 |k₃| / (2 q K |D|)` on near triads (AM–GM `K⁴ + q²Φ² ≥ 2K²q|Φ|` and the
lower bound `|Φ| ≥ |D|/(27 m² K³ |k₃|)`). -/
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

/-! ### Step 2: the Lorentzian-layer summation -/

/-- The layer cake for one pattern: `Σ_{p near} 1/|D(p)| ≤ C_δ (K/|k₃|) K^δ (1 + log ⌈27K⁶⌉)`
(route report §2.1 step 3, with the harmonic sum in place of the continuous majorant). -/
theorem sum_inv_normD_le {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (s₁ s₂ : Sgn) (k : Mode), k 2 ≠ 0 →
      ∑ p ∈ (nearBox k).filter (fun p => IsNear s₁ s₂ p k), (((normD p k).natAbs : ℕ) : ℝ)⁻¹ ≤
        C * (absk k / |(k 2 : ℝ)|) * absk k ^ δ * (1 + Real.log (⌈27 * absk k ^ 6⌉₊ : ℕ)) := by
  obtain ⟨C, hC, h⟩ := near_count_nat hδ
  refine ⟨C, hC, fun s₁ s₂ k hk => ?_⟩
  have key := sum_inv_le_of_card_le ((nearBox k).filter fun p => IsNear s₁ s₂ p k)
    (fun p => (normD p k).natAbs) ⌈27 * absk k ^ 6⌉₊ (C * (absk k / |(k 2 : ℝ)|) * absk k ^ δ)
    ?_ (fun t ht => h s₁ s₂ k hk t ht)
  · refine key.trans (mul_le_mul_of_nonneg_left (sum_Icc_inv_le_log _) ?_)
    exact mul_nonneg (mul_nonneg hC (div_nonneg (absk_nonneg k) (abs_nonneg _)))
      (Real.rpow_nonneg (absk_nonneg k) δ)
  · intro p hp
    rw [Finset.mem_filter] at hp
    refine ⟨Int.natAbs_pos.2 (normD_ne_zero_of_near hp.1 hp.2), ?_⟩
    have h1 := abs_normD_le_pow_of_near hp.1 hp.2
    have h2 : (((normD p k).natAbs : ℕ) : ℝ) ≤ 27 * absk k ^ 6 := by
      rwa [Nat.cast_natAbs, Int.cast_abs]
    exact_mod_cast h2.trans (Nat.le_ceil _)

/-- `1 + log ⌈27K⁶⌉ ≤ (1 + log 28 + 12/δ) K^{δ/2}` for `K ≥ 1` (`log K ≤ K^{δ/2}/(δ/2)`). -/
theorem one_add_log_ceil_le {δ : ℝ} (hδ : 0 < δ) {K : ℝ} (hK : 1 ≤ K) :
    1 + Real.log (⌈27 * K ^ 6⌉₊ : ℕ) ≤ (1 + Real.log 28 + 12 / δ) * K ^ (δ / 2) := by
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
  have h3 : Real.log K ≤ K ^ (δ / 2) / (δ / 2) := Real.log_le_rpow_div hK0.le (by positivity)
  have h4 : 1 ≤ K ^ (δ / 2) := Real.one_le_rpow hK (by positivity)
  have h5 : 0 ≤ Real.log 28 := Real.log_nonneg (by norm_num)
  calc 1 + Real.log (⌈27 * K ^ 6⌉₊ : ℕ) ≤ 1 + Real.log 28 + 6 * (K ^ (δ / 2) / (δ / 2)) := by
        linarith
    _ = (1 + Real.log 28) * 1 + 12 / δ * K ^ (δ / 2) := by
        field_simp
        ring
    _ ≤ (1 + Real.log 28) * K ^ (δ / 2) + 12 / δ * K ^ (δ / 2) := by gcongr
    _ = (1 + Real.log 28 + 12 / δ) * K ^ (δ / 2) := by ring

/-- **Lorentzian-layer summation** (route report §2.1 step 3 and §2.2, fixed-`δ` form): for every
`δ > 0` there is `C_δ` with `momN q k ≤ C_δ K^δ / q` for all `q ≥ 1` and all outputs `k`.
(Report: `Σ_p κ_N² ≤ 36·(459/32)·(π/2 + 1/(2δ))·2^ω Σ_∞ D_δ K^{2δ}/q`, giving `C_δ K^{3δ}/q`.) -/
theorem momN_le {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℝ) (k : Mode), 1 ≤ q → momN q k ≤ C * absk k ^ δ / q := by
  obtain ⟨C₁, hC₁, h₁⟩ := sum_inv_normD_le (half_pos hδ)
  have hL : 0 ≤ 1 + Real.log 28 + 12 / δ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 28 by norm_num)
    positivity
  have hC : 0 ≤ 54 * C₁ * (1 + Real.log 28 + 12 / δ) :=
    mul_nonneg (mul_nonneg (by norm_num) hC₁) hL
  refine ⟨54 * C₁ * (1 + Real.log 28 + 12 / δ), hC, fun q k hq => ?_⟩
  have hq0 : 0 < q := by linarith
  by_cases hk : k 2 = 0
  · rw [momN_eq_zero_of_slow hk]
    exact div_nonneg (mul_nonneg hC (Real.rpow_nonneg (absk_nonneg k) δ)) hq0.le
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hK : 0 < absk k := by linarith
  have hw : 0 < |(k 2 : ℝ)| := abs_pos.2 (by exact_mod_cast hk)
  have hpat : ∀ s : Sgn × Sgn,
      ∑ p ∈ (nearBox k).filter (fun p => IsNear s.1 s.2 p k), nearW q s.1 s.2 p k ≤
        27 / 2 * C₁ * (1 + Real.log 28 + 12 / δ) * absk k ^ δ / q := by
    intro s
    have hhalf : absk k ^ (δ / 2) * absk k ^ (δ / 2) = absk k ^ δ := by
      rw [← Real.rpow_add hK, add_halves]
    calc ∑ p ∈ (nearBox k).filter (fun p => IsNear s.1 s.2 p k), nearW q s.1 s.2 p k
        ≤ 27 * |(k 2 : ℝ)| / (2 * q * absk k) *
            ∑ p ∈ (nearBox k).filter (fun p => IsNear s.1 s.2 p k),
              (((normD p k).natAbs : ℕ) : ℝ)⁻¹ := sum_nearW_le_sum_inv hq0 s.1 s.2
      _ ≤ 27 * |(k 2 : ℝ)| / (2 * q * absk k) *
            (C₁ * (absk k / |(k 2 : ℝ)|) * absk k ^ (δ / 2) *
              (1 + Real.log (⌈27 * absk k ^ 6⌉₊ : ℕ))) := by
          gcongr
          exact h₁ s.1 s.2 k hk
      _ ≤ 27 * |(k 2 : ℝ)| / (2 * q * absk k) *
            (C₁ * (absk k / |(k 2 : ℝ)|) * absk k ^ (δ / 2) *
              ((1 + Real.log 28 + 12 / δ) * absk k ^ (δ / 2))) := by
          gcongr
          exact one_add_log_ceil_le hδ hK1
      _ = 27 / 2 * C₁ * (1 + Real.log 28 + 12 / δ) * (absk k ^ (δ / 2) * absk k ^ (δ / 2)) / q := by
          field_simp
      _ = 27 / 2 * C₁ * (1 + Real.log 28 + 12 / δ) * absk k ^ δ / q := by rw [hhalf]
  rw [momN_eq_sum_patterns]
  calc ∑ s : Sgn × Sgn,
        ∑ p ∈ (nearBox k).filter (fun p => IsNear s.1 s.2 p k), nearW q s.1 s.2 p k
      ≤ ∑ _s : Sgn × Sgn, 27 / 2 * C₁ * (1 + Real.log 28 + 12 / δ) * absk k ^ δ / q :=
        Finset.sum_le_sum fun s _ => hpat s
    _ = 54 * C₁ * (1 + Real.log 28 + 12 / δ) * absk k ^ δ / q := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
          nsmul_eq_mul]
        push_cast
        ring

/-- The proper version: `momP q k ≤ C_δ K^{2+δ} / q` for `q ≥ 1`. -/
theorem momP_le {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℝ) (k : Mode), 1 ≤ q → momP q k ≤ C * absk k ^ (2 + δ) / q := by
  obtain ⟨C, hC, h⟩ := momN_le hδ
  refine ⟨C, hC, fun q k hq => ?_⟩
  have hq0 : 0 < q := by linarith
  unfold momP
  rcases eq_or_ne k 0 with rfl | hk
  · have : absk (0 : Mode) = 0 := absk_eq_zero.2 rfl
    rw [this, Real.zero_rpow (by linarith)]
    simp
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
  calc absk k ^ 2 * momN q k ≤ absk k ^ 2 * (C * absk k ^ δ / q) := by
        gcongr
        exact h q k hq
    _ = C * absk k ^ (2 + δ) / q := by
        rw [Real.rpow_add hK, Real.rpow_two]
        ring

/-! ### Step 3: the trivial bound for large outputs -/

/-- `1/min(x,y)² ≤ 1/x² + 1/y²`. -/
theorem inv_min_sq_le (x y : ℝ) : (min x y ^ 2)⁻¹ ≤ (x ^ 2)⁻¹ + (y ^ 2)⁻¹ := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    linarith [inv_nonneg.2 (sq_nonneg y)]
  · rw [min_eq_right h]
    linarith [inv_nonneg.2 (sq_nonneg x)]

/-- The near box is symmetric under `p ↦ k − p`. -/
theorem sub_mem_nearBox {p k : Mode} (hp : p ∈ nearBox k) : k - p ∈ nearBox k := by
  rw [mem_nearBox] at hp ⊢
  obtain ⟨hk, hp3, hj3, hpk, hjk⟩ := hp
  refine ⟨hk, hj3, ?_, hjk, ?_⟩
  · simpa using hp3
  · simpa using hpk

theorem sum_reflect_nearBox (k : Mode) (f : Mode → ℝ) :
    ∑ p ∈ nearBox k, f (k - p) = ∑ p ∈ nearBox k, f p :=
  Finset.sum_nbij' (fun p => k - p) (fun p => k - p) (fun _ hp => sub_mem_nearBox hp)
    (fun _ hp => sub_mem_nearBox hp) (fun p _ => sub_sub_cancel k p)
    (fun p _ => sub_sub_cancel k p) (fun _ _ => rfl)

/-- `Σ_{p ∈ box} |p|^{−2} ≤ 26 K` (Body 18). -/
theorem sum_inv_absk_sq_nearBox_le (k : Mode) :
    ∑ p ∈ nearBox k, (absk p ^ 2)⁻¹ ≤ 26 * absk k := by
  have hsub : nearBox k ⊆ (modeBox (Nat.sqrt (nsqZ k).toNat)).erase 0 := by
    intro p hp
    have hp' := hp
    rw [nearBox, Finset.mem_filter] at hp'
    rw [Finset.mem_erase]
    refine ⟨?_, hp'.1⟩
    rintro rfl
    exact (mem_nearBox.1 hp).2.1 rfl
  calc ∑ p ∈ nearBox k, (absk p ^ 2)⁻¹ = ∑ p ∈ nearBox k, (absSq p)⁻¹ := by simp [absk_sq]
    _ ≤ ∑ p ∈ (modeBox (Nat.sqrt (nsqZ k).toNat)).erase 0, (absSq p)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => inv_nonneg.2 (absSq_nonneg p)
    _ ≤ 26 * (Nat.sqrt (nsqZ k).toNat : ℝ) := lattice_sum_le _
    _ ≤ 26 * absk k := by
        gcongr
        exact sqrt_toNat_le_absk k

/-- `Σ_{p ∈ box} m(p)^{−2} ≤ 52 K` (`m^{−2} ≤ |p|^{−2} + |j|^{−2}`, both sums `≤ 26K`). -/
theorem sum_inv_minLeg_sq_le (k : Mode) : ∑ p ∈ nearBox k, (minLeg p k ^ 2)⁻¹ ≤ 52 * absk k := by
  calc ∑ p ∈ nearBox k, (minLeg p k ^ 2)⁻¹
      ≤ ∑ p ∈ nearBox k, ((absk p ^ 2)⁻¹ + (absk (k - p) ^ 2)⁻¹) := by
        exact Finset.sum_le_sum fun p _ => inv_min_sq_le _ _
    _ = ∑ p ∈ nearBox k, (absk p ^ 2)⁻¹ + ∑ p ∈ nearBox k, (absk (k - p) ^ 2)⁻¹ :=
        Finset.sum_add_distrib
    _ = ∑ p ∈ nearBox k, (absk p ^ 2)⁻¹ + ∑ p ∈ nearBox k, (absk p ^ 2)⁻¹ := by
        rw [sum_reflect_nearBox k (fun p => (absk p ^ 2)⁻¹)]
    _ ≤ 26 * absk k + 26 * absk k := by
        gcongr <;> exact sum_inv_absk_sq_nearBox_le k
    _ = 52 * absk k := by ring

/-- **The trivial bound** (route report §2.2): `momN q k ≤ 208 K^{−5}` for every `q` and `k`
(`κ_N² ≤ 1/(m²K⁶)`, four patterns, `Σ m^{−2} ≤ 52K`). -/
theorem momN_le_trivial (q : ℝ) (k : Mode) : momN q k ≤ 208 / absk k ^ 5 := by
  by_cases hk : k 2 = 0
  · rw [momN_eq_zero_of_slow hk]
    exact div_nonneg (by norm_num) (pow_nonneg (absk_nonneg k) 5)
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hK : 0 < absk k := by linarith
  unfold momN
  calc ∑ p ∈ nearBox k, ∑ s : Sgn × Sgn, nearW q s.1 s.2 p k
      ≤ ∑ p ∈ nearBox k, ∑ _s : Sgn × Sgn, 1 / (minLeg p k ^ 2 * absk k ^ 6) :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun s _ =>
          nearW_le_inv_minLeg_sq q s.1 s.2 hp
    _ = 4 / absk k ^ 6 * ∑ p ∈ nearBox k, (minLeg p k ^ 2)⁻¹ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
          nsmul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        push_cast
        ring
    _ ≤ 4 / absk k ^ 6 * (52 * absk k) := by
        gcongr
        exact sum_inv_minLeg_sq_le k
    _ = 208 / absk k ^ 5 := by
        field_simp
        ring

/-! ### Step 4: the split at `K = q^{1/5}` -/

/-- `(q^{1/5})^n = q^{n/5}`. -/
theorem rpow_fifth_pow {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    (q ^ ((1 : ℝ) / 5)) ^ n = q ^ ((n : ℝ) / 5) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  congr 1
  ring

/-- **The native split** (route report §2.2, "Native"): `𝔐_N(q) ≤ C_δ q^{δ−1}` for `q ≥ 1`
(`K ≤ q^{1/5}`: `C_δ K^δ/q ≤ C_δ q^δ/q`; `K > q^{1/5}`: `208 K^{−5} ≤ 208/q`). -/
theorem MomN_le_rpow {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ q : ℝ, 1 ≤ q → MomN q ≤ C * q ^ (δ - 1) := by
  obtain ⟨C₁, hC₁, h₁⟩ := momN_le hδ
  refine ⟨C₁ + 208, by positivity, fun q hq => MomN_le fun k => ?_⟩
  have hq0 : 0 < q := by linarith
  set r := q ^ ((1 : ℝ) / 5) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr5 : r ^ 5 = q := by
    rw [hr, rpow_fifth_pow hq0.le 5]
    norm_num
  have hrq : r ≤ q := by
    rw [hr]
    calc q ^ ((1 : ℝ) / 5) ≤ q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq (by norm_num)
      _ = q := Real.rpow_one q
  have hqδ : q ^ (δ - 1) = q ^ δ / q := Real.rpow_sub_one hq0.ne' δ
  have hpos : 0 ≤ q ^ (δ - 1) := by positivity
  rcases le_or_gt (absk k) r with hK | hK
  · have h2 : absk k ^ δ ≤ q ^ δ := Real.rpow_le_rpow (absk_nonneg k) (hK.trans hrq) hδ.le
    calc momN q k ≤ C₁ * absk k ^ δ / q := h₁ q k hq
      _ ≤ C₁ * q ^ δ / q := by gcongr
      _ = C₁ * q ^ (δ - 1) := by rw [hqδ]; ring
      _ ≤ (C₁ + 208) * q ^ (δ - 1) := by gcongr; linarith
  · have h5 : q ≤ absk k ^ 5 := by
      rw [← hr5]
      exact pow_le_pow_left₀ hr0 hK.le 5
    calc momN q k ≤ 208 / absk k ^ 5 := momN_le_trivial q k
      _ ≤ 208 / q := by gcongr
      _ = 208 * q ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; ring
      _ ≤ 208 * q ^ (δ - 1) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq (by linarith))
            (by norm_num)
      _ ≤ (C₁ + 208) * q ^ (δ - 1) := by gcongr; linarith

/-- **The proper split** (route report §2.2, "Proper"): `𝔐_P(q) ≤ C_δ q^{−3/5+δ}` for `q ≥ 1`
(`K ≤ q^{1/5}`: `K² C_δ K^δ/q ≤ C_δ q^{2/5+δ−1}`; `K > q^{1/5}`: `208 K^{−3} ≤ 208 q^{−3/5}`). -/
theorem MomP_le_rpow {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ q : ℝ, 1 ≤ q → MomP q ≤ C * q ^ (-3 / 5 + δ) := by
  obtain ⟨C₁, hC₁, h₁⟩ := momN_le hδ
  refine ⟨C₁ + 208, by positivity, fun q hq => MomP_le fun k => ?_⟩
  have hq0 : 0 < q := by linarith
  set r := q ^ ((1 : ℝ) / 5) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = q ^ ((2 : ℝ) / 5) := by
    rw [hr, rpow_fifth_pow hq0.le 2]
    norm_num
  have hr3 : r ^ 3 = q ^ ((3 : ℝ) / 5) := by
    rw [hr, rpow_fifth_pow hq0.le 3]
    norm_num
  have hrq : r ≤ q := by
    rw [hr]
    calc q ^ ((1 : ℝ) / 5) ≤ q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq (by norm_num)
      _ = q := Real.rpow_one q
  have hpos : 0 ≤ q ^ (-3 / 5 + δ) := by positivity
  have hexp : q ^ (-3 / 5 + δ) = q ^ ((2 : ℝ) / 5) * q ^ δ / q := by
    rw [show (-3 / 5 + δ : ℝ) = 2 / 5 + δ + (-1) by ring, Real.rpow_add hq0, Real.rpow_add hq0,
      Real.rpow_neg_one]
    ring
  unfold momP
  rcases le_or_gt (absk k) r with hK | hK
  · have h2 : absk k ^ δ ≤ q ^ δ := Real.rpow_le_rpow (absk_nonneg k) (hK.trans hrq) hδ.le
    have h3 : absk k ^ 2 ≤ q ^ ((2 : ℝ) / 5) := by
      rw [← hr2]
      exact pow_le_pow_left₀ (absk_nonneg k) hK 2
    calc absk k ^ 2 * momN q k ≤ absk k ^ 2 * (C₁ * absk k ^ δ / q) := by
          gcongr
          exact h₁ q k hq
      _ ≤ q ^ ((2 : ℝ) / 5) * (C₁ * q ^ δ / q) := by
          gcongr
          exact div_nonneg (mul_nonneg hC₁ (Real.rpow_nonneg (absk_nonneg k) δ)) hq0.le
      _ = C₁ * q ^ (-3 / 5 + δ) := by rw [hexp]; ring
      _ ≤ (C₁ + 208) * q ^ (-3 / 5 + δ) := by gcongr; linarith
  · have hK0 : 0 < absk k := lt_of_le_of_lt hr0 hK
    have h3 : q ^ ((3 : ℝ) / 5) ≤ absk k ^ 3 := by
      rw [← hr3]
      exact pow_le_pow_left₀ hr0 hK.le 3
    have h35 : 0 < q ^ ((3 : ℝ) / 5) := by positivity
    calc absk k ^ 2 * momN q k ≤ absk k ^ 2 * (208 / absk k ^ 5) := by
          gcongr
          exact momN_le_trivial q k
      _ = 208 / absk k ^ 3 := by field_simp
      _ ≤ 208 / q ^ ((3 : ℝ) / 5) := by gcongr
      _ = 208 * q ^ (-3 / 5 : ℝ) := by
          rw [show (-3 / 5 : ℝ) = -(3 / 5) by norm_num, Real.rpow_neg hq0.le]
          ring
      _ ≤ 208 * q ^ (-3 / 5 + δ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq (by linarith))
            (by norm_num)
      _ ≤ (C₁ + 208) * q ^ (-3 / 5 + δ) := by gcongr; linarith

/-! ### The profiles -/

/-- `N(q) = 96√𝔐_N(q) ≤ C_δ q^{−1/2+δ}` for `q ≥ 1`. -/
theorem nearN_le {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ q : ℝ, 1 ≤ q → nearN q ≤ C * q ^ (-1 / 2 + δ) := by
  obtain ⟨C, hC, h⟩ := MomN_le_rpow hδ
  refine ⟨96 * Real.sqrt C, by positivity, fun q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  unfold nearN
  calc 96 * Real.sqrt (MomN q) ≤ 96 * Real.sqrt (C * q ^ (δ - 1)) := by
        gcongr
        exact h q hq
    _ = 96 * Real.sqrt C * q ^ ((δ - 1) * (1 / 2)) := by
        rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow (q ^ (δ - 1)), ← Real.rpow_mul hq0.le]
        ring
    _ ≤ 96 * Real.sqrt C * q ^ (-1 / 2 + δ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq (by linarith))
          (by positivity)

/-- `P(q) = 18√𝔐_P(q) + 2⁷q^{−3/4} ≤ C_δ q^{−3/10+δ}` for `q ≥ 1`. -/
theorem nearP_le {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ q : ℝ, 1 ≤ q → nearP q ≤ C * q ^ (-3 / 10 + δ) := by
  obtain ⟨C, hC, h⟩ := MomP_le_rpow hδ
  refine ⟨18 * Real.sqrt C + 2 ^ 7, by positivity, fun q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  have h1 : 18 * Real.sqrt (MomP q) ≤ 18 * Real.sqrt C * q ^ (-3 / 10 + δ) := by
    calc 18 * Real.sqrt (MomP q) ≤ 18 * Real.sqrt (C * q ^ (-3 / 5 + δ)) := by
          gcongr
          exact h q hq
      _ = 18 * Real.sqrt C * q ^ ((-3 / 5 + δ) * (1 / 2)) := by
          rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow (q ^ (-3 / 5 + δ)), ← Real.rpow_mul hq0.le]
          ring
      _ ≤ 18 * Real.sqrt C * q ^ (-3 / 10 + δ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq (by linarith))
            (by positivity)
  have h2 : (2 : ℝ) ^ 7 * q ^ (-(3 : ℝ) / 4) ≤ 2 ^ 7 * q ^ (-3 / 10 + δ) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq (by linarith)) (by norm_num)
  unfold nearP
  linarith

/-- **E9, elementary route** (route report §2.2): the concrete near profiles satisfy
`N(q) ≤ C_δ q^{−1/2+δ}` and `P(q) ≤ C_δ q^{−3/10+δ}` for `q ≥ 1`.  This is the statement the
fixed-force regimes layer should consume (degree `10v/3 ≈ 12.61 < d`). -/
theorem nearProfilesEl : NearProfilesEl nearN nearP := by
  intro δ hδ
  obtain ⟨C₁, hC₁, h₁⟩ := nearN_le hδ
  obtain ⟨C₂, hC₂, h₂⟩ := nearP_le hδ
  refine ⟨C₁ + C₂, fun q hq => ⟨?_, ?_⟩⟩
  · have hx : 0 ≤ q ^ (-1 / 2 + δ) := Real.rpow_nonneg (by linarith) _
    calc nearN q ≤ C₁ * q ^ (-1 / 2 + δ) := h₁ q hq
      _ ≤ (C₁ + C₂) * q ^ (-1 / 2 + δ) := by gcongr; linarith
  · have hx : 0 ≤ q ^ (-3 / 10 + δ) := Real.rpow_nonneg (by linarith) _
    calc nearP q ≤ C₂ * q ^ (-3 / 10 + δ) := h₂ q hq
      _ ≤ (C₁ + C₂) * q ^ (-3 / 10 + δ) := by gcongr; linarith

/-- **E9 as stated in `Interfaces.lean`** (TeX eq. quant-profiles, proper exponent `−1/3`): the
concrete profiles satisfy `NearProfiles`.  The native half is `nearN_le`; the proper half
`P(q) ≤ C_δ q^{−1/3+δ}` requires, for the outputs `K > q^{1/6}`, the MISSING LOCAL210 "full direct
238 count" (atom `2^{17}K^{−6}`, `T^{1/4}` and `T^{1/2}` layer terms; route report §2.1 step 4,
§2.2) — the trivial bound `208K^{−5}` only gives `q^{−3/10+δ}` (`nearP_le`).  Numerically
`q^{2/3} 𝔐_P ≤ 0.23` for `|k| ≤ 32`, `q ≤ 10⁷`.  Left as `sorry`; the regimes layer should
switch to `NearProfilesEl` (`nearProfilesEl`), which is proved from the centred count. -/
theorem nearProfiles : NearProfiles nearN nearP :=
  nearProfiles_of_joint jointProfiles

/-- `NearProfiles` implies `NearProfilesEl` (`q^{−1/3+δ} ≤ q^{−3/10+δ}` for `q ≥ 1`). -/
theorem nearProfilesEl_of_nearProfiles {N P : ℝ → ℝ} (h : NearProfiles N P) :
    NearProfilesEl N P := by
  intro δ hδ
  obtain ⟨C, hC⟩ := h δ hδ
  refine ⟨|C|, fun q hq => ?_⟩
  obtain ⟨h1, h2⟩ := hC q hq
  have hq0 : 0 < q := by linarith
  constructor
  · exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  · calc P q ≤ C * q ^ (-1 / 3 + δ) := h2
      _ ≤ |C| * q ^ (-1 / 3 + δ) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * q ^ (-3 / 10 + δ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq (by linarith))
            (abs_nonneg C)

end OVNS.Quant

end
