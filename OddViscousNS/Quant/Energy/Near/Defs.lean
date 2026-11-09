import OddViscousNS.Quant.Arith.Weighted.Defs

/-!
# Theorem 1.2, fixed force — E9: the near moments (definitions)

Concrete Fourier-side definitions of the native and proper **near moments** whose square roots
are the near profiles `N(q)`, `P(q)` of `NearProfiles`
(`OddViscousNS/Quant/Energy/Interfaces.lean`), following
`OddViscousNS_data/reports/t12_near_slow_route.md` §1 (provenance: proof volume Bodies 18 §1–2,
20, 90 §2–3; TeX quantitative_energies l.300–352).

* A fast triad with **largest leg** (output) `k`, legs `p` and `j = k − p`, all third
  coordinates nonzero; `K = |k|`, `m = min(|p|, |j|)`, `w = k₃`.
* The triad phase `Φ_{s₁s₂} = λ_{s₁}(p) + λ_{s₂}(j) − λ₊(k) = s₁p₃|p| + s₂j₃|j| − k₃|k|`
  (`nearPhi`).  The global sign of a pattern is irrelevant, so the four patterns `(s₁, s₂)` with
  `s₃ = +` produce all values of `|Φ|`.
* The **near set** is `0 < |Φ| < 1` (`IsNear`; Body 18 §1 "split into N: 0 < |Φ| < 1 and
  B: |Φ| ≥ 1").  It is *not* `|Φ| ≤ 1/q`: `q` enters only through the Lorentzian `K⁴ + q²Φ²`.
* The **unit native kernel** `κ_N² = 1/(m²K²(K⁴ + q²Φ²))` (`nearKer`; this is `(Z1/32)²` with
  `Z1 = 32/(mK√(K⁴ + q²Φ²))`, Body 18 §2) and the **proper kernel** `K²κ_N²` (Body 90 §2).
* The moments at a fixed output `k` (`momN`, `momP`: finite sums over the near box
  `|p|, |j| ≤ K`, `p₃ j₃ ≠ 0`, and over the four patterns), their suprema over the outputs
  (`MomN`, `MomP`; "no further sum over largest outputs", TeX l.330–352), and the profiles
  `N(q) = 96 √𝔐_N(q)`, `P(q) = 18 √𝔐_P(q) + 2⁷ q^{−3/4}` (allowances 96 and 18: Body 20 `Nraw`,
  `Graw`, Body 90 §3; the far part `|Φ| ≥ 1` is the elementary `2⁷ q^{−3/4}`).
* `NearProfilesEl`: the target of the elementary route (route report §2.2), `N ≲ q^{−1/2+δ}`
  and `P ≲ q^{−3/10+δ}`.

## Reading choices
* "Near" is `0 < |Φ| < 1` with `Φ` the phase of the triad whose longest leg is the output
  (route report §1.1, §1.4 (c)); exactly resonant triads (`Φ = 0`) are excluded.
* The moment is the per-largest-leg Hilbert–Schmidt (`ℓ²`) moment, then `sup` over the largest
  leg, then the square root (§1.4 (a), forced by the operator-bound use in E5/E8).
* The box is `|p| ≤ |k|` and `|k − p| ≤ |k|` (non-strict), so that `k` is a longest leg.
* Outputs with `k₃ = 0` have an empty near box, so `MomN` is the supremum over fast outputs.
-/

noncomputable section

namespace OVNS.Quant

/-! ### The triad phase and the near set -/

/-- The triad phase of the output `k` with legs `p`, `j = k − p` and helicity pattern `(s₁, s₂)`
(the output carries `s₃ = +`): `Φ_{s₁s₂}(p, k) = λ_{s₁}(p) + λ_{s₂}(k − p) − λ₊(k)`, i.e.
`s₁ p₃ |p| + s₂ j₃ |j| − k₃ |k|` (route report §1.1, §1.3; Body 18 §1). -/
def nearPhi (s₁ s₂ : Sgn) (p k : Mode) : ℝ := lam s₁ p + lam s₂ (k - p) - lam true k

/-- `nearPhi` is the library's oscillation phase `Φ^{s₁ s₂ +}_{p, k−p}` (`Phi`, `Defs.lean`). -/
theorem nearPhi_eq_Phi (s₁ s₂ : Sgn) (p k : Mode) :
    nearPhi s₁ s₂ p k = Phi s₁ s₂ true p (k - p) := by
  simp [nearPhi, Phi]

/-- `nearPhi` is the all-incoming phase `phase3` of the zero-sum triad `(p, k − p, −k)`
(`Weighted/Defs.lean`). -/
theorem nearPhi_eq_phase3 (s₁ s₂ : Sgn) (p k : Mode) :
    nearPhi s₁ s₂ p k = phase3 s₁ s₂ true p (k - p) (-k) := by
  simp only [nearPhi, phase3, lam_neg]
  ring

/-- Identification with the resonance predicate `ResPat` of `Resonant/Defs.lean`: the pattern
`(s₁, s₂, +)` on the legs `(p, k − p, −k)` is resonant iff the triad phase vanishes. -/
theorem resPat_iff_nearPhi_eq_zero (s₁ s₂ : Sgn) (p k : Mode) :
    ResPat ![p, k - p, -k] ![s₁, s₂, true] ↔ nearPhi s₁ s₂ p k = 0 := by
  simp [ResPat, Fin.sum_univ_three, nearPhi, lam_neg, sub_eq_add_neg]

/-- `λ_{¬s} = −λ_s`. -/
theorem lam_not (s : Sgn) (p : Mode) : lam (!s) p = -lam s p := by
  cases s <;> simp [lam, sg]

/-- `|λ_s(p)| = |p₃| |p|`. -/
theorem abs_lam (s : Sgn) (p : Mode) : |lam s p| = |(p 2 : ℝ)| * absk p := by
  cases s <;> simp [lam, sg, abs_mul, abs_of_nonneg (absk_nonneg p)]

/-- Flipping the second sign. -/
theorem nearPhi_not_right (s₁ s₂ : Sgn) (p k : Mode) :
    nearPhi s₁ (!s₂) p k = nearPhi s₁ s₂ p k - 2 * lam s₂ (k - p) := by
  simp only [nearPhi, lam_not]
  ring

/-- Flipping the first sign. -/
theorem nearPhi_not_left (s₁ s₂ : Sgn) (p k : Mode) :
    nearPhi (!s₁) s₂ p k = nearPhi s₁ s₂ p k - 2 * lam s₁ p := by
  simp only [nearPhi, lam_not]
  ring

/-- The near set `0 < |Φ| < 1` of the pattern `(s₁, s₂)` (Body 18 §1; route report §1.1).
Exactly resonant triads are excluded; `|Φ| ≥ 1` is the (far) complement. -/
def IsNear (s₁ s₂ : Sgn) (p k : Mode) : Prop :=
  0 < |nearPhi s₁ s₂ p k| ∧ |nearPhi s₁ s₂ p k| < 1

instance (s₁ s₂ : Sgn) (p k : Mode) : Decidable (IsNear s₁ s₂ p k) := by
  unfold IsNear
  infer_instance

/-! ### Kernels -/

/-- `m = min(|p|, |k − p|)`, the shorter of the two non-output legs. -/
def minLeg (p k : Mode) : ℝ := min (absk p) (absk (k - p))

/-- The unit native near kernel `κ_N² = 1/(m² K² (K⁴ + q² Φ²))` of the pattern `(s₁, s₂)`
(Body 18 §2: `Z1 = 32/(mK√(K⁴ + q²Φ²))`, unit kernel `Z1/32`; route report §1.2).  The proper
kernel is `K² κ_N²` (Body 90 §2) and is accounted for in `momP`. -/
def nearKer (q : ℝ) (s₁ s₂ : Sgn) (p k : Mode) : ℝ :=
  1 / (minLeg p k ^ 2 * absk k ^ 2 * (absk k ^ 4 + q ^ 2 * nearPhi s₁ s₂ p k ^ 2))

/-- The near kernel restricted to the near set (`0` off `0 < |Φ| < 1`). -/
def nearW (q : ℝ) (s₁ s₂ : Sgn) (p k : Mode) : ℝ :=
  if IsNear s₁ s₂ p k then nearKer q s₁ s₂ p k else 0

/-! ### The near box and the moments -/

/-- The near box of the output `k`: the legs `p` with `|p| ≤ |k|`, `|k − p| ≤ |k|` and all three
third coordinates `k₃, p₃, (k − p)₃` nonzero (route report §1.3: `|p|, |j| ≤ |k|`,
`p₃ j₃ ≠ 0`, `k₃ ≠ 0`).  Realized as a filter of the cube `modeBox ⌊|k|⌋`. -/
def nearBox (k : Mode) : Finset Mode :=
  (modeBox (Nat.sqrt (nsqZ k).toNat)).filter fun p =>
    k 2 ≠ 0 ∧ p 2 ≠ 0 ∧ (k - p) 2 ≠ 0 ∧ nsqZ p ≤ nsqZ k ∧ nsqZ (k - p) ≤ nsqZ k

/-- The native near moment at the fixed largest output `k`:
`Σ_{p : |p|,|j| ≤ K, p₃ j₃ ≠ 0} Σ_{(s₁,s₂), 0 < |Φ| < 1} κ_N²` (route report §1.3). -/
def momN (q : ℝ) (k : Mode) : ℝ := ∑ p ∈ nearBox k, ∑ s : Sgn × Sgn, nearW q s.1 s.2 p k

/-- The proper near moment at the fixed output `k`: `K² ·` the native one (Body 90 §2). -/
def momP (q : ℝ) (k : Mode) : ℝ := absk k ^ 2 * momN q k

/-- `𝔐_N(q) = sup_k momN q k`, the complete native near moment (sup over fast outputs; outputs
with `k₃ = 0` contribute `0`).  Bounded: `bddAbove_momN`. -/
def MomN (q : ℝ) : ℝ := ⨆ k : Mode, momN q k

/-- `𝔐_P(q) = sup_k momP q k`, the complete proper near moment.  Bounded: `bddAbove_momP`. -/
def MomP (q : ℝ) : ℝ := ⨆ k : Mode, momP q k

/-- The native near profile `N(q) = 96 √𝔐_N(q)` (allowance 96: Body 20 `Nraw`, Body 90 §3). -/
def nearN (q : ℝ) : ℝ := 96 * Real.sqrt (MomN q)

/-- The proper near profile `P(q) = 18 √𝔐_P(q) + 2⁷ q^{−3/4}` (allowance 18: Body 20 `Graw`,
Body 90 §3; the second term is the elementary proper FAR part `|Φ| ≥ 1`). -/
def nearP (q : ℝ) : ℝ := 18 * Real.sqrt (MomP q) + 2 ^ 7 * q ^ (-(3 : ℝ) / 4)

/-- **The elementary-route profiles** (route report §2.2): `N(q) ≤ C_δ q^{−1/2+δ}` and
`P(q) ≤ C_δ q^{−3/10+δ}` for `q ≥ 1`.  This is `NearProfiles` with the proper exponent `−1/3`
weakened to `−3/10`.  It suffices for the fixed-force regimes layer: the proper duties
`P(q) y ≤ c` (roles 13, 14, 16, 17) have degree `v/p` for `P ~ q^{−p}`, and at `p = 3/10` this is
`10v/3 = 27190/2157 ≈ 12.61 < d = 9876/719 ≈ 13.74` (gap `≈ 1.13`); the regimes layer should
therefore be switched from `NearProfiles` to this `Prop` (the exact `−1/3` needs the MISSING
LOCAL210 direct count). -/
def NearProfilesEl (N P : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ q : ℝ, 1 ≤ q →
    N q ≤ C * q ^ (-1 / 2 + δ) ∧ P q ≤ C * q ^ (-3 / 10 + δ)

/-! ### Elementary facts: lengths -/

theorem nsqZ_nonneg (k : Mode) : 0 ≤ nsqZ k := Finset.sum_nonneg fun i _ => sq_nonneg (k i)

theorem absSq_eq_nsqZ (k : Mode) : absSq k = (nsqZ k : ℝ) := by
  simp [absSq, nsqZ]

theorem absk_sq_eq_nsqZ (k : Mode) : absk k ^ 2 = (nsqZ k : ℝ) := by
  rw [absk_sq, absSq_eq_nsqZ]

theorem absk_le_absk_iff (p k : Mode) : absk p ≤ absk k ↔ nsqZ p ≤ nsqZ k := by
  rw [absk_eq_sqrt_nsqZ, absk_eq_sqrt_nsqZ,
    Real.sqrt_le_sqrt_iff (by exact_mod_cast nsqZ_nonneg k)]
  exact Int.cast_le

/-- `(p i)² ≤ |p|²`. -/
theorem sq_coord_le_nsqZ (p : Mode) (i : Fin 3) : p i ^ 2 ≤ nsqZ p :=
  Finset.single_le_sum (f := fun j => p j ^ 2) (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)

theorem mem_modeBox {R : ℕ} {p : Mode} : p ∈ modeBox R ↔ ∀ i, |p i| ≤ R := by
  simp [modeBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem card_modeBox (R : ℕ) : (modeBox R).card = (2 * R + 1) ^ 3 := by
  simp only [modeBox, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  omega

/-- `⌊|k|⌋ ≤ |k|`. -/
theorem sqrt_toNat_le_absk (k : Mode) : (Nat.sqrt (nsqZ k).toNat : ℝ) ≤ absk k := by
  have h0 := nsqZ_nonneg k
  have h1 : ((Nat.sqrt (nsqZ k).toNat : ℤ)) ^ 2 ≤ nsqZ k := by
    have := Nat.sqrt_le' (nsqZ k).toNat
    have h2 : ((nsqZ k).toNat : ℤ) = nsqZ k := Int.toNat_of_nonneg h0
    rw [← h2]
    exact_mod_cast this
  rw [absk_eq_sqrt_nsqZ, Real.le_sqrt (by positivity) (by exact_mod_cast h0)]
  exact_mod_cast h1

/-- Membership in the near box in terms of the real lengths. -/
theorem mem_nearBox {p k : Mode} : p ∈ nearBox k ↔
    k 2 ≠ 0 ∧ p 2 ≠ 0 ∧ (k - p) 2 ≠ 0 ∧ absk p ≤ absk k ∧ absk (k - p) ≤ absk k := by
  rw [nearBox, Finset.mem_filter, absk_le_absk_iff, absk_le_absk_iff]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨hk, hp, hj, hpk, hjk⟩
    refine ⟨?_, hk, hp, hj, hpk, hjk⟩
    rw [mem_modeBox]
    intro i
    have h0 := nsqZ_nonneg k
    have h1 : (p i).natAbs ^ 2 ≤ (nsqZ k).toNat := by
      have h3 := (sq_coord_le_nsqZ p i).trans hpk
      zify
      rw [Int.toNat_of_nonneg h0, sq_abs]
      exact h3
    have h2 : (p i).natAbs ≤ Nat.sqrt (nsqZ k).toNat := Nat.le_sqrt'.mpr h1
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h2

theorem nearBox_eq_empty {k : Mode} (hk : k 2 = 0) : nearBox k = ∅ := by
  ext p
  simp [mem_nearBox, hk]

theorem momN_eq_zero_of_slow {q : ℝ} {k : Mode} (hk : k 2 = 0) : momN q k = 0 := by
  simp [momN, nearBox_eq_empty hk]

/-- All three legs of a box triad have length `≥ 1`. -/
theorem one_le_absk_of_mem_nearBox {p k : Mode} (hp : p ∈ nearBox k) :
    1 ≤ absk k ∧ 1 ≤ absk p ∧ 1 ≤ absk (k - p) := by
  obtain ⟨hk, hp3, hj, -, -⟩ := mem_nearBox.1 hp
  refine ⟨one_le_absk ?_, one_le_absk ?_, one_le_absk ?_⟩
  · rintro rfl
    simp at hk
  · rintro rfl
    simp at hp3
  · intro h
    rw [h] at hj
    simp at hj

theorem one_le_minLeg {p k : Mode} (hp : p ∈ nearBox k) : 1 ≤ minLeg p k :=
  le_min (one_le_absk_of_mem_nearBox hp).2.1 (one_le_absk_of_mem_nearBox hp).2.2

theorem minLeg_le_absk {p k : Mode} (hp : p ∈ nearBox k) : minLeg p k ≤ absk k :=
  min_le_of_left_le (mem_nearBox.1 hp).2.2.2.1

theorem minLeg_pos {p k : Mode} (hp : p ∈ nearBox k) : 0 < minLeg p k :=
  lt_of_lt_of_le one_pos (one_le_minLeg hp)

/-! ### Elementary facts: kernels and moments -/

theorem nearKer_nonneg (q : ℝ) (s₁ s₂ : Sgn) (p k : Mode) : 0 ≤ nearKer q s₁ s₂ p k := by
  unfold nearKer
  positivity

theorem nearW_nonneg (q : ℝ) (s₁ s₂ : Sgn) (p k : Mode) : 0 ≤ nearW q s₁ s₂ p k := by
  unfold nearW
  split_ifs
  · exact nearKer_nonneg q s₁ s₂ p k
  · exact le_rfl

theorem momN_nonneg (q : ℝ) (k : Mode) : 0 ≤ momN q k :=
  Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun s _ => nearW_nonneg q s.1 s.2 p k

theorem momP_nonneg (q : ℝ) (k : Mode) : 0 ≤ momP q k :=
  mul_nonneg (by positivity) (momN_nonneg q k)

/-- The `q`-free bound `κ_N² ≤ 1/(m² K⁶)` (drop `q²Φ² ≥ 0`). -/
theorem nearW_le_inv_minLeg_sq (q : ℝ) (s₁ s₂ : Sgn) {p k : Mode} (hp : p ∈ nearBox k) :
    nearW q s₁ s₂ p k ≤ 1 / (minLeg p k ^ 2 * absk k ^ 6) := by
  have hm := minLeg_pos hp
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk_of_mem_nearBox hp).1
  unfold nearW
  split_ifs with h
  · unfold nearKer
    apply one_div_le_one_div_of_le (by positivity)
    have e : minLeg p k ^ 2 * absk k ^ 6 = minLeg p k ^ 2 * absk k ^ 2 * absk k ^ 4 := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [sq_nonneg (q * nearPhi s₁ s₂ p k)]
  · positivity

/-- The cruder `κ_N² ≤ K^{−6}` (also `m ≥ 1`). -/
theorem nearW_le_inv_pow (q : ℝ) (s₁ s₂ : Sgn) {p k : Mode} (hp : p ∈ nearBox k) :
    nearW q s₁ s₂ p k ≤ 1 / absk k ^ 6 := by
  refine (nearW_le_inv_minLeg_sq q s₁ s₂ hp).trans ?_
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk_of_mem_nearBox hp).1
  apply one_div_le_one_div_of_le (by positivity)
  exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (one_le_minLeg hp))

/-- The near box has at most `(2⌊K⌋ + 1)³ ≤ 27 K³` points. -/
theorem card_nearBox_le {k : Mode} (hk : 1 ≤ absk k) :
    ((nearBox k).card : ℝ) ≤ 27 * absk k ^ 3 := by
  have h1 : (nearBox k).card ≤ (modeBox (Nat.sqrt (nsqZ k).toNat)).card :=
    Finset.card_filter_le _ _
  rw [card_modeBox] at h1
  have h2 := sqrt_toNat_le_absk k
  calc ((nearBox k).card : ℝ) ≤ ((2 * Nat.sqrt (nsqZ k).toNat + 1 : ℕ) : ℝ) ^ 3 := by
        exact_mod_cast h1
    _ ≤ (3 * absk k) ^ 3 := by
        gcongr
        push_cast
        linarith
    _ = 27 * absk k ^ 3 := by ring

/-- The crude per-output bound `momN q k ≤ 4 · #box · K^{−6}`. -/
theorem momN_le_card (q : ℝ) (k : Mode) :
    momN q k ≤ 4 * (nearBox k).card / absk k ^ 6 := by
  unfold momN
  calc ∑ p ∈ nearBox k, ∑ s : Sgn × Sgn, nearW q s.1 s.2 p k
      ≤ ∑ p ∈ nearBox k, ∑ _s : Sgn × Sgn, 1 / absk k ^ 6 :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun s _ => nearW_le_inv_pow q s.1 s.2 hp
    _ = 4 * (nearBox k).card / absk k ^ 6 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
          nsmul_eq_mul]
        push_cast
        ring

/-- The crude per-output bound `momN q k ≤ 108 K^{−3}` (`K ≥ 1`). -/
theorem momN_le_crude (q : ℝ) {k : Mode} (hk : 1 ≤ absk k) : momN q k ≤ 108 / absk k ^ 3 := by
  have hK : 0 < absk k := lt_of_lt_of_le one_pos hk
  calc momN q k ≤ 4 * (nearBox k).card / absk k ^ 6 := momN_le_card q k
    _ ≤ 4 * (27 * absk k ^ 3) / absk k ^ 6 := by gcongr; exact card_nearBox_le hk
    _ = 108 / absk k ^ 3 := by field_simp; ring

/-- Uniform boundedness of the per-output native moments. -/
theorem momN_le_const (q : ℝ) (k : Mode) : momN q k ≤ 108 := by
  by_cases hk : k 2 = 0
  · rw [momN_eq_zero_of_slow hk]
    norm_num
  · have hk1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
    refine (momN_le_crude q hk1).trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [one_le_pow₀ hk1 (n := 3)]

/-- Uniform boundedness of the per-output proper moments. -/
theorem momP_le_const (q : ℝ) (k : Mode) : momP q k ≤ 108 := by
  by_cases hk : k 2 = 0
  · simp [momP, momN_eq_zero_of_slow hk]
  · have hk1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
    have hK : 0 < absk k := lt_of_lt_of_le one_pos hk1
    unfold momP
    calc absk k ^ 2 * momN q k ≤ absk k ^ 2 * (108 / absk k ^ 3) := by
          gcongr
          exact momN_le_crude q hk1
      _ = 108 / absk k := by field_simp
      _ ≤ 108 := by
          rw [div_le_iff₀ hK]
          nlinarith

theorem bddAbove_momN (q : ℝ) : BddAbove (Set.range (momN q)) :=
  ⟨108, by rintro _ ⟨k, rfl⟩; exact momN_le_const q k⟩

theorem bddAbove_momP (q : ℝ) : BddAbove (Set.range (momP q)) :=
  ⟨108, by rintro _ ⟨k, rfl⟩; exact momP_le_const q k⟩

/-- The workable form of the supremum: every output is below `𝔐_N`. -/
theorem momN_le_MomN (q : ℝ) (k : Mode) : momN q k ≤ MomN q := le_ciSup (bddAbove_momN q) k

theorem momP_le_MomP (q : ℝ) (k : Mode) : momP q k ≤ MomP q := le_ciSup (bddAbove_momP q) k

/-- The workable form of the supremum: a uniform per-output bound bounds `𝔐_N`. -/
theorem MomN_le {q c : ℝ} (h : ∀ k, momN q k ≤ c) : MomN q ≤ c := ciSup_le h

theorem MomP_le {q c : ℝ} (h : ∀ k, momP q k ≤ c) : MomP q ≤ c := ciSup_le h

theorem MomN_nonneg (q : ℝ) : 0 ≤ MomN q := (momN_nonneg q 0).trans (momN_le_MomN q 0)

theorem MomP_nonneg (q : ℝ) : 0 ≤ MomP q := (momP_nonneg q 0).trans (momP_le_MomP q 0)

theorem MomN_le_const (q : ℝ) : MomN q ≤ 108 := MomN_le (momN_le_const q)

theorem MomP_le_const (q : ℝ) : MomP q ≤ 108 := MomP_le (momP_le_const q)

theorem nearN_nonneg (q : ℝ) : 0 ≤ nearN q := by
  unfold nearN
  positivity

end OVNS.Quant

end
